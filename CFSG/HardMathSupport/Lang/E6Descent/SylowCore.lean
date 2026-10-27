module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG.Open (IsElemAbelian)

@[expose] def RankBoundTStar : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsPGroup 3 Q → ∀ x : Q, x ^ 3 = 1 →
    Nat.card (Subgroup.centralizer ({x} : Set Q)) = 9 →
    ∀ (M : Subgroup Q) [M.Normal], M.index = 3 → x ∉ M → 81 ≤ Nat.card M →
      ∀ E : Subgroup Q, E ≤ M → IsElemAbelian 3 E → Nat.card E < 27

theorem card_modEq_card_fixedPoints_iterate' {X : Type*} [Finite X] (g : X → X) {r m : ℕ}
    [Fact r.Prime] (hg : ∀ x, g^[r ^ m] x = x) :
    Nat.card X ≡ Nat.card {x // g x = x} [MOD r] := by
  classical
  have := Fintype.ofFinite X
  let g' : Function.End X := g
  have hpow : ∀ (n : ℕ) (x : X), (g' ^ n) x = g^[n] x := by
    intro n
    induction n with
    | zero => intro x; rw [pow_zero]; rfl
    | succ n ih =>
      intro x
      rw [pow_succ]
      show (g' ^ n) (g x) = _
      rw [ih, Function.iterate_succ_apply]
  have hg' : g' ^ r ^ m = 1 := by
    funext x
    rw [hpow]
    exact hg x
  have h1 := Equiv.Perm.card_fixedPoints_modEq hg'
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card] at h1
  exact h1

theorem exists_ne_one_commute {Q : Type*} [Group Q] [Finite Q] (T : Subgroup Q) {v : Q}
    (hv3 : v ^ 3 = 1) (hvT : v ∈ Subgroup.normalizer (T : Set Q))
    (h3 : 3 ∣ Nat.card T) : ∃ t ∈ T, t ≠ 1 ∧ v * t = t * v := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmem : ∀ t : T, v * (t : Q) * v⁻¹ ∈ T := fun t => (Subgroup.mem_normalizer_iff.mp hvT t).1 t.2
  let g : T → T := fun t => ⟨v * (t : Q) * v⁻¹, hmem t⟩
  have hg : ∀ t : T, g^[3 ^ 1] t = t := by
    intro t
    apply Subtype.ext
    have h : ∀ n : ℕ, ((g^[n] t : T) : Q) = v ^ n * (t : Q) * (v ^ n)⁻¹ := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Function.iterate_succ_apply', show ((g (g^[n] t) : T) : Q) =
          v * ((g^[n] t : T) : Q) * v⁻¹ from rfl, ih]
        simp only [pow_succ', mul_inv_rev, mul_assoc]
    rw [h, pow_one, hv3]
    simp
  have hmod := card_modEq_card_fixedPoints_iterate' g hg
  have hfix : 3 ∣ Nat.card {t : T // g t = t} :=
    (Nat.modEq_zero_iff_dvd.1 ((hmod.symm.trans (Nat.modEq_zero_iff_dvd.2 h3))))
  have hpos : 0 < Nat.card {t : T // g t = t} := by
    have : Finite {t : T // g t = t} := inferInstance
    refine Nat.card_pos_iff.2 ⟨⟨⟨1, ?_⟩⟩, inferInstance⟩
    exact Subtype.ext (by simp [g])
  have h2 : 1 < Nat.card {t : T // g t = t} := by
    have := Nat.le_of_dvd hpos hfix
    omega
  obtain ⟨a, b, hab⟩ := Finite.one_lt_card_iff_nontrivial.mp (by simpa using h2) |>.exists_pair_ne
  by_cases ha : (a : T) = 1
  · refine ⟨((b : T) : Q), (b : T).2, ?_, ?_⟩
    · intro hb
      apply hab
      apply Subtype.ext
      rw [ha]
      exact (Subtype.ext hb).symm
    · have := congrArg (fun t : T => (t : Q)) b.2
      simp only [g] at this
      calc v * ((b : T) : Q) = (v * ((b : T) : Q) * v⁻¹) * v := by group
        _ = ((b : T) : Q) * v := by rw [this]
  · refine ⟨((a : T) : Q), (a : T).2, ?_, ?_⟩
    · intro h
      exact ha (Subtype.ext h)
    · have := congrArg (fun t : T => (t : Q)) a.2
      simp only [g] at this
      calc v * ((a : T) : Q) = (v * ((a : T) : Q) * v⁻¹) * v := by group
        _ = ((a : T) : Q) * v := by rw [this]

theorem card_centralizer_le_index_mul {P : Type*} [Group P] [Finite P] (S : Subgroup P)
    [S.Normal] (Z : Subgroup P) (u : P) (hC : ∀ y ∈ S, y * u = u * y → y ∈ Z) :
    Nat.card (Subgroup.centralizer ({u} : Set P)) ≤ S.index * Nat.card Z := by
  set C := Subgroup.centralizer ({u} : Set P) with hCdef
  let f : C →* P ⧸ S := (QuotientGroup.mk' S).comp C.subtype
  have h1 := Subgroup.card_ker_mul_card_range f
  have hrange : Nat.card f.range ≤ S.index := by
    have := Subgroup.card_le_card_group f.range
    rwa [Subgroup.index_eq_card]
  have hker : Nat.card f.ker ≤ Nat.card Z := by
    refine Nat.card_le_card_of_injective
      (fun x => (⟨((x : C) : P), ?_⟩ : Z)) ?_
    · have hx := x.2
      rw [MonoidHom.mem_ker] at hx
      have hS : ((x : C) : P) ∈ S := by
        have : (QuotientGroup.mk ((x : C) : P) : P ⧸ S) = 1 := hx
        exact QuotientGroup.eq_one_iff _ |>.mp this
      have hc' : ((x : C) : P) ∈ Subgroup.centralizer ({u} : Set P) := (x : C).2
      have hc := Subgroup.mem_centralizer_singleton_iff.mp hc'
      exact hC _ hS hc
    · intro a b hab
      have := congrArg (fun z : Z => (z : P)) hab
      exact Subtype.ext (Subtype.ext this)
  rw [← h1]
  exact Nat.mul_le_mul hker hrange |>.trans_eq (by ring)

theorem card_centralizer_quotient_le {P : Type*} [Group P] [Finite P] (Z : Subgroup P)
    [Z.Normal] (hZ : ∀ z ∈ Z, ∀ g : P, z * g = g * z) (u : P) :
    Nat.card (Subgroup.centralizer ({(u : P ⧸ Z)} : Set (P ⧸ Z))) ≤
      Nat.card (Subgroup.centralizer ({u} : Set P)) := by
  set C := Subgroup.centralizer ({u} : Set P) with hCdef
  set Cb := Subgroup.centralizer ({(u : P ⧸ Z)} : Set (P ⧸ Z)) with hCbdef
  set π := QuotientGroup.mk' Z with hπ
  set D : Subgroup P := Cb.comap π with hD
  have hDmem : ∀ g : P, g ∈ D ↔ g⁻¹ * u⁻¹ * g * u ∈ Z := by
    intro g
    rw [hD, Subgroup.mem_comap, hCbdef, Subgroup.mem_centralizer_singleton_iff]
    simp only [hπ, QuotientGroup.mk'_apply]
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have e : g⁻¹ * u⁻¹ * g * u = (u⁻¹ * (g⁻¹ * (u * g)))⁻¹ := by group
    rw [e, Z.inv_mem_iff]; simp only [mul_inv_rev, mul_assoc]
  let ψ : D →* Z :=
    { toFun := fun g => ⟨(g : P)⁻¹ * u⁻¹ * (g : P) * u, (hDmem g).1 g.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => by
        apply Subtype.ext
        have hca := hZ _ ((hDmem a).1 a.2) (b : P)
        show ((a : P) * b)⁻¹ * u⁻¹ * ((a : P) * b) * u =
          ((a : P)⁻¹ * u⁻¹ * (a : P) * u) * ((b : P)⁻¹ * u⁻¹ * (b : P) * u)
        calc ((a : P) * b)⁻¹ * u⁻¹ * ((a : P) * b) * u
            = ((b : P)⁻¹ * ((a : P)⁻¹ * u⁻¹ * (a : P) * u) * (b : P)) *
                ((b : P)⁻¹ * u⁻¹ * (b : P) * u) := by group
          _ = ((a : P)⁻¹ * u⁻¹ * (a : P) * u) * ((b : P)⁻¹ * u⁻¹ * (b : P) * u) := by
              have hb' : (b : P)⁻¹ * ((a : P)⁻¹ * u⁻¹ * (a : P) * u) * (b : P) =
                  (a : P)⁻¹ * u⁻¹ * (a : P) * u := by
                rw [mul_assoc, hca, inv_mul_cancel_left]
              rw [hb'] }
  have h1 := Subgroup.card_ker_mul_card_range ψ
  have hker : Nat.card ψ.ker ≤ Nat.card C := by
    refine Nat.card_le_card_of_injective (fun x => (⟨((x : D) : P), ?_⟩ : C)) ?_
    · have hx := x.2
      rw [MonoidHom.mem_ker] at hx
      have hx' : ((x : D) : P)⁻¹ * u⁻¹ * ((x : D) : P) * u = 1 := congrArg Subtype.val hx
      rw [hCdef, Subgroup.mem_centralizer_singleton_iff]
      have h : u * ((x : D) : P) = ((x : D) : P) * u := by
        calc u * ((x : D) : P)
            = u * ((x : D) : P) * (((x : D) : P)⁻¹ * u⁻¹ * ((x : D) : P) * u) := by
              rw [hx', mul_one]
          _ = ((x : D) : P) * u := by group
      first | exact h | exact h.symm
    · intro a b hab
      have := congrArg (fun z : C => (z : P)) hab
      exact Subtype.ext (Subtype.ext this)
  have hrange : Nat.card ψ.range ≤ Nat.card Z := Subgroup.card_le_card_group _
  have hDcard : Nat.card D = Nat.card Cb * Nat.card Z := by
    have hidx : D.index = Cb.index := Subgroup.index_comap_of_surjective Cb
      (QuotientGroup.mk'_surjective Z)
    have h2 := Subgroup.card_mul_index D
    have h3 := Subgroup.card_mul_index Cb
    have h4 := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
    have hpos : 0 < Cb.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
    rw [hidx] at h2
    have : Nat.card D * Cb.index = (Nat.card Cb * Nat.card Z) * Cb.index := by
      calc Nat.card D * Cb.index = Nat.card P := h2
        _ = Nat.card Z * Nat.card (P ⧸ Z) := by rw [mul_comm]; exact h4.trans (by ring)
        _ = (Nat.card Cb * Nat.card Z) * Cb.index := by
            rw [← h3]; ring
    exact Nat.eq_of_mul_eq_mul_right hpos this
  have : Nat.card Cb * Nat.card Z ≤ Nat.card C * Nat.card Z := by
    rw [← hDcard, ← h1]; exact Nat.mul_le_mul hker hrange
  exact Nat.le_of_mul_le_mul_right this Nat.card_pos

theorem card_eq_mul_card_map_mk {P : Type*} [Group P] [Finite P] (Z T : Subgroup P) [Z.Normal]
    (hZT : Z ≤ T) :
    Nat.card T = Nat.card Z * Nat.card (T.map (QuotientGroup.mk' Z)) := by
  have hker : (QuotientGroup.mk' Z).ker = Z := QuotientGroup.ker_mk' Z
  have hidx : (T.map (QuotientGroup.mk' Z)).index = T.index :=
    Subgroup.index_map_eq T (QuotientGroup.mk'_surjective Z) (by rw [hker]; exact hZT)
  have h1 := Subgroup.card_mul_index T
  have h2 := Subgroup.card_mul_index (T.map (QuotientGroup.mk' Z))
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
  have hpos : 0 < T.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  rw [hidx] at h2
  have : Nat.card T * T.index = (Nat.card Z * Nat.card (T.map (QuotientGroup.mk' Z))) * T.index := by
    calc Nat.card T * T.index = Nat.card P := h1
      _ = Nat.card (P ⧸ Z) * Nat.card Z := h3
      _ = (Nat.card Z * Nat.card (T.map (QuotientGroup.mk' Z))) * T.index := by
          rw [← h2]; ring
  exact Nat.eq_of_mul_eq_mul_right hpos this

theorem eq_one_of_mem_zpowers_of_mem {Q : Type*} [Group Q] (T : Subgroup Q) {v : Q}
    (hv3 : v ^ 3 = 1) (hvT : v ∉ T) {x : Q} (hxT : x ∈ T) (hx : x ∈ Subgroup.zpowers v) :
    x = 1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h3z : v ^ (3 : ℤ) = 1 := by exact_mod_cast hv3
  have hk : v ^ k = v ^ (k % 3) := by
    have hk3 : k = 3 * (k / 3) + k % 3 := by omega
    conv_lhs => rw [hk3, zpow_add, zpow_mul, h3z, one_zpow, one_mul]
  have hcases : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hcases with h | h | h
  · rw [hk, h]; simp
  · exfalso; apply hvT
    rw [hk, h] at hxT; simpa using hxT
  · exfalso; apply hvT
    rw [hk, h] at hxT
    have h2 : v ^ (2 : ℤ) = v * v := by rw [zpow_two]
    rw [h2] at hxT
    have : (v * v) * (v * v) = v := by
      calc (v * v) * (v * v) = v ^ 3 * v := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = v := by rw [hv3, one_mul]
    rw [← this]
    exact T.mul_mem hxT hxT

theorem exists_noncentral_fixed_of_maxClassRank (hB : RankBoundTStar)
    {P : Type} [Group P] [Finite P] (hP : IsPGroup 3 P)
    {Z S F : Subgroup P} [S.Normal]
    (hZc : ∀ z ∈ Z, ∀ g : P, z * g = g * z) (hZ3 : Nat.card Z ≤ 3)
    (hSi : S.index ≤ 3) (hZS : Z ≤ S) {u : P} (hu3 : u ^ 3 = 1) (huS : u ∉ S)
    (hZF : Z ≤ F) (hFS : F ≤ S)
    (hFc : ∀ a ∈ F, ∀ b ∈ F, a * b * a⁻¹ * b⁻¹ ∈ Z) (hFe : ∀ a ∈ F, a ^ 3 ∈ Z)
    (hFo : 27 * Nat.card Z ≤ Nat.card F) (hSo : 81 * Nat.card Z ≤ Nat.card S) :
    ∃ y ∈ S, y * u = u * y ∧ y ∉ Z := by
  by_contra hcon
  push Not at hcon
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZn : Z.Normal := ⟨fun z hz g => by
    have e : g * z * g⁻¹ = z := by rw [← hZc z hz g, mul_inv_cancel_right]
    rw [e]; exact hz⟩
  set π := QuotientGroup.mk' Z with hπ
  have hQ3 : IsPGroup 3 (P ⧸ Z) := hP.to_quotient Z
  set Sb : Subgroup (P ⧸ Z) := S.map π with hSb
  have hSbn : Sb.Normal := Subgroup.Normal.map ‹S.Normal› π (QuotientGroup.mk'_surjective Z)
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  have hSbcard : Nat.card S = Nat.card Z * Nat.card Sb := card_eq_mul_card_map_mk Z S hZS
  have hFbcard : Nat.card F = Nat.card Z * Nat.card (F.map π) := card_eq_mul_card_map_mk Z F hZF
  have hSb81 : 81 ≤ Nat.card Sb := by
    by_contra h
    push Not at h
    have : Nat.card Z * Nat.card Sb < Nat.card Z * 81 := Nat.mul_lt_mul_of_pos_left h hZpos
    nlinarith
  have hFb27 : 27 ≤ Nat.card (F.map π) := by
    by_contra h
    push Not at h
    have : Nat.card Z * Nat.card (F.map π) < Nat.card Z * 27 := Nat.mul_lt_mul_of_pos_left h hZpos
    nlinarith
  set ub : P ⧸ Z := (u : P ⧸ Z) with hub
  have hub3 : ub ^ 3 = 1 := by
    rw [hub, ← QuotientGroup.mk_pow, hu3, QuotientGroup.mk_one]
  have hubS : ub ∉ Sb := by
    intro h
    obtain ⟨s, hs, hsu⟩ := Subgroup.mem_map.mp h
    have : (s : P ⧸ Z) = (u : P ⧸ Z) := hsu
    rw [QuotientGroup.eq] at this
    exact huS (by simpa using S.mul_mem hs (hZS this) )
  have hub1 : ub ≠ 1 := fun h => hubS (h ▸ Sb.one_mem)
  have hord : orderOf ub = 3 := orderOf_eq_prime hub3 hub1
  have hSbp : IsPGroup 3 Sb := hQ3.of_injective Sb.subtype Subtype.coe_injective
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hSbp
  have h3 : 3 ∣ Nat.card Sb := by
    rw [hn]
    refine dvd_pow_self 3 ?_
    rintro rfl
    rw [pow_zero] at hn
    omega
  obtain ⟨sb, hsb, hsb1, hsbc⟩ :=
    exists_ne_one_commute Sb hub3 (by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top _) h3
  set Cb := Subgroup.centralizer ({ub} : Set (P ⧸ Z)) with hCb
  have hCb9 : Nat.card Cb = 3 ^ 2 := by
    have hup : Nat.card Cb ≤ 9 := by
      have h1 := card_centralizer_quotient_le Z hZc u
      have h2 := card_centralizer_le_index_mul S Z u hcon
      have : Nat.card Cb ≤ Nat.card (Subgroup.centralizer ({u} : Set P)) := h1
      have h4 : S.index * Nat.card Z ≤ 3 * Nat.card Z := Nat.mul_le_mul_right _ hSi
      omega
    have hlow : 9 ≤ Nat.card Cb := by
      have hCbp : IsPGroup 3 Cb := hQ3.of_injective Cb.subtype Subtype.coe_injective
      obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hCbp
      have hzp : Subgroup.zpowers ub ≤ Cb := by
        rw [Subgroup.zpowers_le, hCb, Subgroup.mem_centralizer_singleton_iff]
      have hzcard : Nat.card (Subgroup.zpowers ub) = 3 := by
        rw [Nat.card_zpowers, hord]
      have hsbC : sb ∈ Cb := by
        rw [hCb, Subgroup.mem_centralizer_singleton_iff]
        exact hsbc.symm
      have hsbz : sb ∉ Subgroup.zpowers ub := fun h =>
        hsb1 (eq_one_of_mem_zpowers_of_mem Sb hub3 hubS hsb h)
      by_contra hlt
      push Not at hlt
      have hdvd : 3 ∣ Nat.card Cb := hzcard ▸ Subgroup.card_dvd_of_le hzp
      have : Nat.card Cb = 3 := by
        rw [hm] at hlt hdvd ⊢
        have hm1 : m ≤ 1 := by
          by_contra h2
          push Not at h2
          have : 3 ^ 2 ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) h2
          omega
        interval_cases m
        · simp at hdvd
        · simp
      have heq : Subgroup.zpowers ub = Cb :=
        Subgroup.eq_of_le_of_card_ge hzp (by rw [this, hzcard])
      exact hsbz (heq ▸ hsbC)
    omega
  have hFel : IsElemAbelian 3 (F.map π) := by
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨a, ha⟩ ⟨b, hb⟩
      obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
      obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
      apply Subtype.ext
      show π a' * π b' = π b' * π a'
      have hc := hFc a' ha' b' hb'
      have h1 : π (a' * b' * a'⁻¹ * b'⁻¹) = 1 := (QuotientGroup.eq_one_iff _).2 hc
      simp only [map_mul, map_inv] at h1
      calc π a' * π b' = (π a' * π b' * (π a')⁻¹ * (π b')⁻¹) * (π b' * π a') := by group
        _ = π b' * π a' := by rw [h1, one_mul]
    · rintro x hx
      obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp hx
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).2 (hFe a' ha')
  have hidx : Sb.index = S.index := by
    rw [hSb, Subgroup.index_map_eq S (QuotientGroup.mk'_surjective Z)
      (by rw [QuotientGroup.ker_mk']; exact hZS)]
  have hS2 : 2 ≤ S.index := by
    have h1 : S.index ≠ 1 := fun h => huS ((Subgroup.index_eq_one.mp h) ▸ Subgroup.mem_top u)
    have h0 : S.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  have hS3 : S.index = 3 := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hP
    have hd : S.index ∣ 3 ^ k := hk ▸ Subgroup.index_dvd_card S
    obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd
    rcases a with _ | _ | a
    · omega
    · simpa using ha
    · have h1 : 3 ^ 2 ≤ 3 ^ (a + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [ha] at hSi
      omega
  have hFbS : F.map π ≤ Sb := Subgroup.map_mono hFS
  have hlt := hB (P ⧸ Z) hQ3 ub hub3 (by rw [← hCb, hCb9]; norm_num) Sb (hidx.trans hS3) hubS
    hSb81 (F.map π) hFbS hFel
  omega

end CFSG.HardMathSupport.Lang.E6Descent
