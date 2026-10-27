module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Bal3Lemma2_1Defs
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.GL83PartI.I_20_1
public import CFSG.LocalAnalysis.GLTheoremB.PCompLift
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

theorem exists_commutator_of_isPlaneDiagonal {X : Type*} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] (hp5 : 5 ≤ p) {D : Subgroup X} (hD : IsElemAbelian p D)
    (hcard : Nat.card D = p ^ 2) {z g : X} (hz : z ∈ D) (hz1 : z ≠ 1)
    (hg : IsPlaneDiagonal p D z g) :
    ∀ d ∈ D, ∃ d' ∈ D, d = d'⁻¹ * g * d' * g⁻¹ := by
  obtain ⟨hgN, -, a, b, hab, hord, hga, hgd⟩ := hg
  have hconj : ∀ x ∈ D, g * x * g⁻¹ ∈ D := fun x hx => (mem_normalizer_iff.1 hgN x).1 hx
  have hp : p.Prime := Fact.out
  have hzp : z ^ p = 1 := hD.2 z hz
  have hzord : orderOf z = p := orderOf_eq_prime hzp hz1
  have hab' : (a : ZMod p) * (b : ZMod p) = 1 := by
    have := congrArg (Nat.cast : ℕ → ZMod p) hab
    rwa [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_one] at this
  have ha1 : (a : ZMod p) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    omega
  have hb1 : (b : ZMod p) ≠ 1 := by
    intro h
    apply ha1
    rw [h, mul_one] at hab'
    exact hab'
  have hfix : ∀ w ∈ D, g * w * g⁻¹ = w → w = 1 := by
    intro w hw hgw
    by_contra hw1
    have hwp : w ^ p = 1 := hD.2 w hw
    have hwo : orderOf w = p := orderOf_eq_prime hwp hw1
    by_cases hwz : w ∈ Subgroup.zpowers z
    ·
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hwz
      rw [← conj_zpow, hga, ← zpow_natCast, ← zpow_mul] at hgw
      have hmod : (a : ℤ) * k ≡ k [ZMOD (orderOf z : ℤ)] := zpow_eq_zpow_iff_modEq.1 hgw
      rw [hzord] at hmod
      have hZ : (((k : ℤ) - (a : ℤ) * k : ℤ) : ZMod p) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hmod.dvd
      push_cast at hZ
      have hmul : (1 - (a : ZMod p)) * (k : ZMod p) = 0 := by linear_combination hZ
      rcases mul_eq_zero.1 hmul with h | h
      · exact ha1 (sub_eq_zero.1 h).symm
      · have hpk : ((orderOf z : ℕ) : ℤ) ∣ k := by
          rw [hzord]
          exact (ZMod.intCast_zmod_eq_zero_iff_dvd k p).1 h
        exact hw1 (orderOf_dvd_iff_zpow_eq_one.1 hpk)
    ·
      obtain ⟨c, hc⟩ := hgd w hw hwz
      have hwc : w = w ^ b * z ^ c := hgw.symm.trans hc
      have hu_w : z ^ c ∈ Subgroup.zpowers w := by
        have hzc : z ^ c = (w ^ b)⁻¹ * w := by
          calc z ^ c = (w ^ b)⁻¹ * (w ^ b * z ^ c) := by group
            _ = (w ^ b)⁻¹ * w := by rw [← hwc]
        rw [hzc]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _
          (Subgroup.mem_zpowers w) b)) (Subgroup.mem_zpowers w)
      have hu_z : z ^ c ∈ Subgroup.zpowers z := Subgroup.pow_mem _ (Subgroup.mem_zpowers z) c
      have hu1 : z ^ c = 1 := by
        by_contra hne
        have hup : (z ^ c) ^ p = 1 := by
          rw [← pow_mul, mul_comm, pow_mul, hzp, one_pow]
        have hou : orderOf (z ^ c) = p := orderOf_eq_prime hup hne
        have h1 : Subgroup.zpowers (z ^ c) = Subgroup.zpowers z :=
          Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hu_z) (by
            rw [Nat.card_zpowers, Nat.card_zpowers, hzord, hou])
        have h2 : Subgroup.zpowers (z ^ c) = Subgroup.zpowers w :=
          Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hu_w) (by
            rw [Nat.card_zpowers, Nat.card_zpowers, hwo, hou])
        apply hwz
        have hww : w ∈ Subgroup.zpowers w := Subgroup.mem_zpowers w
        rw [← h2, h1] at hww
        exact hww
      rw [hu1, mul_one] at hwc
      have hwb : w ^ b = w ^ 1 := by rw [pow_one]; exact hwc.symm
      have hmodb : b ≡ 1 [MOD orderOf w] := pow_eq_pow_iff_modEq.1 hwb
      rw [hwo] at hmodb
      have hb : (b : ZMod p) = ((1 : ℕ) : ZMod p) := (ZMod.natCast_eq_natCast_iff _ _ _).2 hmodb
      exact hb1 (by simpa using hb)
  let ψ : D → D := fun x =>
    ⟨(x : X)⁻¹ * (g * (x : X) * g⁻¹), D.mul_mem (D.inv_mem x.2) (hconj _ x.2)⟩
  have hψ : Function.Injective ψ := by
    intro x y hxy
    have h1 : (x : X)⁻¹ * (g * (x : X) * g⁻¹) = (y : X)⁻¹ * (g * (y : X) * g⁻¹) :=
      congrArg Subtype.val hxy
    have h2 : g * (y : X) * g⁻¹ = (y : X) * (x : X)⁻¹ * (g * (x : X) * g⁻¹) := by
      calc g * (y : X) * g⁻¹ = (y : X) * ((y : X)⁻¹ * (g * (y : X) * g⁻¹)) := by group
        _ = (y : X) * ((x : X)⁻¹ * (g * (x : X) * g⁻¹)) := by rw [h1]
        _ = (y : X) * (x : X)⁻¹ * (g * (x : X) * g⁻¹) := by group
    have hw : g * ((y : X) * (x : X)⁻¹) * g⁻¹ = (y : X) * (x : X)⁻¹ := by
      calc g * ((y : X) * (x : X)⁻¹) * g⁻¹
          = (g * (y : X) * g⁻¹) * (g * (x : X) * g⁻¹)⁻¹ := by group
        _ = (y : X) * (x : X)⁻¹ * (g * (x : X) * g⁻¹) * (g * (x : X) * g⁻¹)⁻¹ := by rw [h2]
        _ = (y : X) * (x : X)⁻¹ := by group
    have hyx : (y : X) * (x : X)⁻¹ = 1 :=
      hfix _ (D.mul_mem y.2 (D.inv_mem x.2)) hw
    exact Subtype.ext (mul_inv_eq_one.1 hyx).symm
  intro d hd
  obtain ⟨⟨d', hd'⟩, hdd⟩ := Finite.surjective_of_injective hψ ⟨d, hd⟩
  have h3 : (d' : X)⁻¹ * (g * d' * g⁻¹) = d := congrArg Subtype.val hdd
  refine ⟨d', hd', ?_⟩
  calc d = (d' : X)⁻¹ * (g * d' * g⁻¹) := h3.symm
    _ = d'⁻¹ * g * d' * g⁻¹ := by group

theorem glaPLayer_top_eq_bot_of_subgroup {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (H : Subgroup X) (h : GLAPLayer p H = ⊥) : GLAPLayer p (⊤ : Subgroup H) = ⊥ := by
  have hle : GLAPLayer p (⊤ : Subgroup H) ≤ (GLAPLayer p H).comap H.subtype := by
    unfold GLAPLayer
    refine sSup_le fun J hJ => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    have hker : Nat.Coprime p (Nat.card ↥((⊤ : Subgroup H) ⊓ H.subtype.ker)) := by
      have : (⊤ : Subgroup H) ⊓ H.subtype.ker = ⊥ := by simp
      rw [this, Subgroup.card_bot]
      exact Nat.coprime_one_right p
    have h1 := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_map hp H.subtype hker hJ
    have htop : (⊤ : Subgroup H).map H.subtype = H :=
      le_antisymm (by rintro _ ⟨y, -, rfl⟩; exact y.2)
        fun y hy => ⟨⟨y, hy⟩, Subgroup.mem_top _, rfl⟩
    rw [htop] at h1
    exact le_sSup h1
  rw [h, MonoidHom.comap_bot, Subgroup.ker_subtype] at hle
  exact le_bot_iff.1 hle

theorem glaPPrimeCoreOf_top_eq_bot_of_subgroup {X : Type} [Group X] {p : ℕ} (H : Subgroup X)
    (h : GLAPPrimeCoreOf p H = ⊥) : GLAPPrimeCoreOf p (⊤ : Subgroup H) = ⊥ := by
  have hcore : GLAPPrimeCore p H = ⊥ := by
    have h' : (GLAPPrimeCore p H).map H.subtype = ⊥ := h
    exact Subgroup.map_injective H.subtype_injective (h'.trans (Subgroup.map_bot _).symm)
  have h1 := CFSG.LocalAnalysis.GLTheoremB.glaPPrimeCore_map_iso p
    (Subgroup.topEquiv (G := H))
  rw [hcore] at h1
  have hcore' : GLAPPrimeCore p (⊤ : Subgroup H) = ⊥ :=
    Subgroup.map_injective (f := (Subgroup.topEquiv (G := H)).toMonoidHom)
      (Subgroup.topEquiv (G := H)).injective (h1.trans (Subgroup.map_bot _).symm)
  unfold GLAPPrimeCoreOf
  rw [hcore', Subgroup.map_bot]

theorem le_of_isSylowOf_central {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {K D : Subgroup X} (hsyl : CFSG.ABGLocalTools.IsSylowOf p D K)
    (hcomm : ∀ k ∈ K, ∀ d ∈ D, k * d = d * k)
    {E : Subgroup X} (hEp : ∀ x ∈ E, x ^ p = 1) (hEK : E ≤ K) (hDE : D ≤ E) : E ≤ D := by
  obtain ⟨Q, hQ⟩ := hsyl
  have hmemQ : ∀ x : K, x ∈ (Q : Subgroup K) ↔ (x : X) ∈ D := by
    intro x
    constructor
    · intro hx
      rw [← hQ]
      exact Subgroup.mem_map_of_mem K.subtype hx
    · intro hx
      rw [← hQ] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have : y = x := Subtype.ext hyx
      exact this ▸ hy
  have hQn : (Q : Subgroup K).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hmemQ] at hn ⊢
    have hgn : ((g * n * g⁻¹ : K) : X) = (n : X) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hcomm (g : X) g.2 (n : X) hn, mul_assoc, mul_inv_cancel, mul_one]
    rw [hgn]
    exact hn
  haveI : Unique (Sylow p K) := Sylow.unique_of_normal Q hQn
  have hEp' : IsPGroup p (E.subgroupOf K) := fun e =>
    ⟨1, Subtype.ext (Subtype.ext (by simpa using hEp e.1 (Subgroup.mem_subgroupOf.1 e.2)))⟩
  obtain ⟨Q', hQ'⟩ := hEp'.exists_le_sylow
  have hQQ : Q' = Q := Subsingleton.elim _ _
  intro e he
  have heK : (⟨e, hEK he⟩ : K) ∈ E.subgroupOf K := Subgroup.mem_subgroupOf.2 he
  have hmem := hQ' heK
  rw [hQQ] at hmem
  exact (hmemQ _).1 hmem

theorem signalizer_eq_bot_of_constrained {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {D : Subgroup X} (hD : IsElemAbelian p D)
    (hcard : Nat.card D = p ^ 2) (hsyl : CFSG.ABGLocalTools.IsSylowOf p D (centralizer D))
    (hC : ∀ d ∈ D, d ≠ 1 →
      GLAPLayer p (centralizer ({d} : Set X)) = ⊥ ∧
      GLAPPrimeCoreOf p (centralizer ({d} : Set X)) = ⊥) :
    ∀ T : Subgroup X, p.Coprime (Nat.card T) → D ≤ normalizer (T : Set X) → T = ⊥ := by
  intro T hT hDT
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsMulCommutative D := hD.1
  have hDc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb => setLike_mul_comm ha hb
  have hcent : ∀ d ∈ D, d ≠ 1 → T ⊓ centralizer ({d} : Set X) = ⊥ := by
    intro d hd hd1
    obtain ⟨hlay, hcore⟩ := hC d hd hd1
    have hDH : D ≤ centralizer ({d} : Set X) := fun w hw =>
      Subgroup.mem_centralizer_singleton_iff.2 (hDc w hw d hd)
    have hB : IsElemAbelian p (D.subgroupOf (centralizer ({d} : Set X))) := by
      refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
      · apply Subtype.ext
        apply Subtype.ext
        simpa using hDc _ (Subgroup.mem_subgroupOf.1 a.2) _ (Subgroup.mem_subgroupOf.1 b.2)
      · apply Subtype.ext
        simpa using hD.2 _ (Subgroup.mem_subgroupOf.1 hy)
    have hmax : ∀ E' : Subgroup (centralizer ({d} : Set X)), IsElemAbelian p E' →
        D.subgroupOf (centralizer ({d} : Set X)) ≤ E' →
        E' = D.subgroupOf (centralizer ({d} : Set X)) := by
      intro E' hE' hBE'
      haveI : IsMulCommutative E' := hE'.1
      have hE''p : ∀ x ∈ E'.map (centralizer ({d} : Set X)).subtype, x ^ p = 1 := by
        rintro _ ⟨y, hy, rfl⟩
        simpa using congrArg (centralizer ({d} : Set X)).subtype (hE'.2 y hy)
      have hE''K : E'.map (centralizer ({d} : Set X)).subtype ≤ centralizer (D : Set X) := by
        rintro _ ⟨y, hy, rfl⟩
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        have hwE' : (⟨w, hDH hw⟩ : centralizer ({d} : Set X)) ∈ E' :=
          hBE' (Subgroup.mem_subgroupOf.2 hw)
        have hc := congrArg Subtype.val (setLike_mul_comm hy hwE')
        simp only [Subgroup.coe_mul] at hc
        exact hc.symm
      have hDE'' : D ≤ E'.map (centralizer ({d} : Set X)).subtype := fun w hw =>
        ⟨⟨w, hDH hw⟩, hBE' (Subgroup.mem_subgroupOf.2 hw), rfl⟩
      have hle := le_of_isSylowOf_central hsyl
        (fun k hk w hw => ((Subgroup.mem_centralizer_iff.1 hk) w hw).symm) hE''p hE''K hDE''
      apply le_antisymm
      · intro y hy
        exact Subgroup.mem_subgroupOf.2 (hle ⟨y, hy, rfl⟩)
      · exact hBE'
    have key := GL83.I_20_1_proved (centralizer ({d} : Set X)) p hp hp2
      (glaPLayer_top_eq_bot_of_subgroup hp (centralizer ({d} : Set X)) hlay)
      (D.subgroupOf (centralizer ({d} : Set X))) hB hmax
    have hcoreH := glaPPrimeCoreOf_top_eq_bot_of_subgroup (centralizer ({d} : Set X)) hcore
    have hYcop : Nat.Coprime p (Nat.card ↥((T ⊓ centralizer ({d} : Set X)).subgroupOf
        (centralizer ({d} : Set X)))) := by
      have h1 : Nat.card ↥((T ⊓ centralizer ({d} : Set X)).subgroupOf
          (centralizer ({d} : Set X))) = Nat.card ↥(T ⊓ centralizer ({d} : Set X)) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe
          (inf_le_right : T ⊓ centralizer ({d} : Set X) ≤ centralizer ({d} : Set X))).toEquiv
      rw [h1]
      exact Nat.Coprime.coprime_dvd_right
        (Subgroup.card_dvd_of_le (inf_le_left : T ⊓ centralizer ({d} : Set X) ≤ T)) hT
    have hYnorm : D.subgroupOf (centralizer ({d} : Set X)) ≤
        normalizer ((((T ⊓ centralizer ({d} : Set X)).subgroupOf
          (centralizer ({d} : Set X)) : Subgroup (centralizer ({d} : Set X))) :
          Set (centralizer ({d} : Set X)))) := by
      intro b hb
      have hβ : (b : X) ∈ D := Subgroup.mem_subgroupOf.1 hb
      have hβd : (b : X) * d = d * (b : X) := hDc _ hβ d hd
      have hH' : ∀ z : X, z ∈ centralizer ({d} : Set X) ↔
          (b : X) * z * (b : X)⁻¹ ∈ centralizer ({d} : Set X) := by
        intro z
        rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
        have hinv : (b : X)⁻¹ * d = d * (b : X)⁻¹ := by
          calc (b : X)⁻¹ * d = (b : X)⁻¹ * (d * (b : X)) * (b : X)⁻¹ := by group
            _ = (b : X)⁻¹ * ((b : X) * d) * (b : X)⁻¹ := by rw [← hβd]
            _ = d * (b : X)⁻¹ := by group
        have e1 : (b : X) * z * (b : X)⁻¹ * d = (b : X) * (z * d) * (b : X)⁻¹ := by
          calc (b : X) * z * (b : X)⁻¹ * d = (b : X) * z * ((b : X)⁻¹ * d) := by group
            _ = (b : X) * z * (d * (b : X)⁻¹) := by rw [hinv]
            _ = (b : X) * (z * d) * (b : X)⁻¹ := by group
        have e2 : d * ((b : X) * z * (b : X)⁻¹) = (b : X) * (d * z) * (b : X)⁻¹ := by
          calc d * ((b : X) * z * (b : X)⁻¹) = (d * (b : X)) * z * (b : X)⁻¹ := by group
            _ = ((b : X) * d) * z * (b : X)⁻¹ := by rw [← hβd]
            _ = (b : X) * (d * z) * (b : X)⁻¹ := by group
        rw [e1, e2]
        constructor
        · intro h
          rw [h]
        · intro h
          simp only [mul_left_inj, mul_right_inj] at h
          exact h
      intro y
      have hT' : (y : X) ∈ T ↔ (b : X) * (y : X) * (b : X)⁻¹ ∈ T :=
        Subgroup.mem_normalizer_iff.1 (hDT hβ) (y : X)
      simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv,
        Subgroup.mem_inf]
      exact and_congr hT' (hH' (y : X))
    have hY : (T ⊓ centralizer ({d} : Set X)).subgroupOf (centralizer ({d} : Set X)) ≤
        GLAPPrimeCoreOf p (⊤ : Subgroup (centralizer ({d} : Set X))) := by
      rw [← key]
      exact le_iSup_of_le _ (le_iSup_of_le hYcop (le_iSup_of_le hYnorm le_rfl))
    rw [hcoreH] at hY
    refine eq_bot_iff.2 fun t ht => Subgroup.mem_bot.2 ?_
    have ht' : (⟨t, ht.2⟩ : centralizer ({d} : Set X)) ∈
        (T ⊓ centralizer ({d} : Set X)).subgroupOf (centralizer ({d} : Set X)) :=
      Subgroup.mem_subgroupOf.2 ht
    have h1 := hY ht'
    rw [Subgroup.mem_bot] at h1
    exact congrArg Subtype.val h1
  have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity hp hD
    hcard.ge hDT hT
  exact hgen.symm.trans (iSup_eq_bot.2 fun a => iSup_eq_bot.2 fun ha =>
    iSup_eq_bot.2 fun ha1 => hcent a ha ha1)

theorem card_le_card_ker_pow_pow {V : Type*} [AddCommGroup V] [Finite V] (f : AddMonoid.End V) :
    ∀ (n : ℕ) (S : AddSubgroup V), (∀ s ∈ S, f s ∈ S) → (∀ s ∈ S, (f ^ n) s = 0) →
      Nat.card S ≤ (Nat.card (f : V →+ V).ker) ^ n := by
  intro n
  induction n with
  | zero =>
    intro S _ hS0
    have h0 : ∀ s ∈ S, s = 0 := fun s hs => by simpa using hS0 s hs
    have hsub : Subsingleton S := ⟨fun a b => Subtype.ext ((h0 a a.2).trans (h0 b b.2).symm)⟩
    rw [pow_zero]
    exact Finite.card_le_one_iff_subsingleton.2 hsub
  | succ n ih =>
    intro S hS hSn
    let φ : S →+ V := (f : V →+ V).comp S.subtype
    have hcard := AddSubgroup.card_ker_mul_card_range φ
    have hT : ∀ t ∈ φ.range, f t ∈ φ.range := by
      rintro t ⟨s, rfl⟩
      exact ⟨⟨f s, hS s s.2⟩, rfl⟩
    have hTn : ∀ t ∈ φ.range, (f ^ n) t = 0 := by
      rintro t ⟨s, rfl⟩
      have h := hSn s s.2
      rw [pow_succ] at h
      exact h
    have hIH := ih φ.range hT hTn
    have hker : Nat.card φ.ker ≤ Nat.card (f : V →+ V).ker := by
      refine Nat.card_le_card_of_injective (fun u : φ.ker =>
        (⟨(u : S), u.2⟩ : (f : V →+ V).ker)) ?_
      intro u v huv
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun w : (f : V →+ V).ker => (w : V)) huv
    calc Nat.card S = Nat.card φ.ker * Nat.card φ.range := hcard.symm
      _ ≤ Nat.card (f : V →+ V).ker * (Nat.card (f : V →+ V).ker) ^ n :=
          Nat.mul_le_mul hker hIH
      _ = (Nat.card (f : V →+ V).ker) ^ (n + 1) := (pow_succ' _ _).symm

theorem le_pRank_of_isElemAbelian_le {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]
    {C F : Subgroup P} (hFC : F ≤ C) (hF : IsElemAbelian p F) {k : ℕ}
    (hk : Nat.card F = p ^ k) : k ≤ CFSG.Open.pRank p C := by
  unfold CFSG.Open.pRank
  refine le_csSup ⟨Nat.card P, ?_⟩ ⟨F, hFC, hF, hk⟩
  rintro m ⟨E, -, -, hEm⟩
  have h1 : p ^ m ≤ Nat.card P := by
    rw [← hEm]
    exact Subgroup.card_le_card_group E
  exact le_trans (Nat.lt_pow_self (Fact.out : p.Prime).one_lt : m < p ^ m).le h1

theorem three_le_pRank_centralizer_of_normal {P : Type*} [Group P] [Finite P] {p : ℕ}
    [Fact p.Prime] (hp5 : 5 ≤ p) (hP : IsPGroup p P) {x : P} (hx : orderOf x = p)
    {E : Subgroup P} [E.Normal] (hE : IsElemAbelian p E) (he : p ^ (p + 1) ≤ Nat.card E) :
    3 ≤ CFSG.Open.pRank p (centralizer ({x} : Set P)) := by
  have hp : p.Prime := Fact.out
  have hxp : x ^ p = 1 := hx ▸ pow_orderOf_eq_one x
  haveI : IsMulCommutative E := hE.1
  have hEp : IsPGroup p E := fun e => ⟨1, Subtype.ext (by simpa using hE.2 e e.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hEp
  have hk3 : p + 1 ≤ k := by
    rw [hk] at he
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 he
  by_cases hxE : x ∈ E
  ·
    have hEC : E ≤ centralizer ({x} : Set P) := by
      intro e he'
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact setLike_mul_comm he' hxE
    exact le_trans (by omega) (le_pRank_of_isElemAbelian_le hEC hE hk)
  · set C : Subgroup P := centralizer ({x} : Set P)
    have hxC : x ∈ C := Subgroup.mem_centralizer_singleton_iff.2 rfl
    letI : CommGroup E := IsMulCommutative.instCommGroup
    let φ : E →* E := ((MulAut.conj x).toMonoidHom.comp E.subtype).codRestrict E
      (fun e => Subgroup.Normal.conj_mem inferInstance (e : P) e.2 x)
    let σ : AddMonoid.End (Additive E) := MonoidHom.toAdditive φ
    have hσ : ∀ v : Additive E, (((σ v).toMul : E) : P) = x * ((v.toMul : E) : P) * x⁻¹ :=
      fun v => rfl
    have hσk : ∀ (k : ℕ) (v : Additive E),
        (((σ ^ k) v).toMul : P) = x ^ k * ((v.toMul : E) : P) * (x ^ k)⁻¹ := by
      intro k
      induction k with
      | zero => intro v; simp
      | succ k ih =>
        intro v
        rw [pow_succ]
        change (((σ ^ k) (σ v)).toMul : P) = _
        rw [ih (σ v), hσ v]
        group
    have hσp : σ ^ p = 1 := by
      refine DFunLike.ext _ _ fun v => ?_
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [hσk, hxp]
      simp
    have hpv : ∀ v : Additive E, p • v = 0 := by
      intro v
      apply Additive.toMul.injective
      rw [toMul_nsmul, toMul_zero]
      apply Subtype.ext
      simpa using hE.2 ((v.toMul : E) : P) (v.toMul).2
    have hcardV : Nat.card (Additive E) = Nat.card E := (Nat.card_congr Additive.ofMul).symm
    have hntV : Nontrivial (Additive E) := by
      rw [← Finite.one_lt_card_iff_nontrivial, hcardV]
      exact lt_of_lt_of_le (Nat.one_lt_pow (by omega) hp.one_lt) he
    haveI hchar : CharP (AddMonoid.End (Additive E)) p := by
      refine ⟨fun n => ⟨fun hn => ?_, fun hdvd => ?_⟩⟩
      · obtain ⟨v, hv⟩ := exists_ne (0 : Additive E)
        have hnv : n • v = 0 := by
          have h := DFunLike.congr_fun hn v
          simpa [AddMonoid.End.natCast_apply] using h
        rw [← addOrderOf_eq_prime (hpv v) hv]
        exact addOrderOf_dvd_of_nsmul_eq_zero hnv
      · obtain ⟨c, rfl⟩ := hdvd
        refine DFunLike.ext _ _ fun v => ?_
        show (p * c) • v = 0
        rw [mul_nsmul, hpv v, nsmul_zero]
    set δ : AddMonoid.End (Additive E) := σ - 1 with hδ
    have hδp : δ ^ p = 0 := by
      rw [hδ, sub_pow_char_of_commute p (Commute.one_right σ), hσp, one_pow, sub_self]
    set K0 : AddSubgroup (Additive E) := (δ : Additive E →+ Additive E).ker
    have hchain := card_le_card_ker_pow_pow δ p ⊤ (fun s _ => AddSubgroup.mem_top _)
      (fun s _ => by rw [hδp]; rfl)
    have hTop : Nat.card (⊤ : AddSubgroup (Additive E)) = Nat.card E :=
      AddSubgroup.card_top.trans hcardV
    have hEV : Nat.card E ≤ (Nat.card K0) ^ p := by
      rw [← hTop]
      exact hchain
    have hmemK : ∀ u : Additive E, u ∈ K0 → ((u.toMul : E) : P) ∈ E ⊓ C := by
      intro u hu
      refine Subgroup.mem_inf.2 ⟨(u.toMul).2, ?_⟩
      have hσu : σ u = u := by
        have h0 : δ u = 0 := AddMonoidHom.mem_ker.1 hu
        have h1 : σ u - u = 0 := h0
        exact sub_eq_zero.1 h1
      have h1 := hσ u
      rw [hσu] at h1
      have hcomm : ((u.toMul : E) : P) * x = x * ((u.toMul : E) : P) := by
        calc ((u.toMul : E) : P) * x = (x * ((u.toMul : E) : P) * x⁻¹) * x := by rw [← h1]
          _ = x * ((u.toMul : E) : P) := by group
      exact Subgroup.mem_centralizer_singleton_iff.2 hcomm
    have hKC : Nat.card K0 ≤ Nat.card ↥(E ⊓ C) := by
      refine Nat.card_le_card_of_injective (fun u : K0 =>
        (⟨((u : Additive E).toMul : P), hmemK _ u.2⟩ : ↥(E ⊓ C))) ?_
      intro u v huv
      apply Subtype.ext
      apply Additive.toMul.injective
      apply Subtype.ext
      exact congrArg (fun w : ↥(E ⊓ C) => (w : P)) huv
    have hdvd : Nat.card ↥(E ⊓ C) ∣ p ^ k := by
      rw [← hk]
      exact Subgroup.card_dvd_of_le (inf_le_left : E ⊓ C ≤ E)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    have hj2 : 2 ≤ j := by
      have h1 : p ^ (p + 1) ≤ p ^ (j * p) := by
        calc p ^ (p + 1) ≤ Nat.card E := he
          _ ≤ (Nat.card K0) ^ p := hEV
          _ ≤ (p ^ j) ^ p := Nat.pow_le_pow_left (hKC.trans_eq hj) p
          _ = p ^ (j * p) := (pow_mul p j p).symm
      have h2 : p + 1 ≤ j * p := (Nat.pow_le_pow_iff_right hp.one_lt).1 h1
      by_contra hlt
      have h3 : j * p ≤ 1 * p := Nat.mul_le_mul_right p (by omega)
      omega
    have hH'el : IsElemAbelian p (E ⊓ C) := hE.mono inf_le_left
    have hKel : IsElemAbelian p (Subgroup.zpowers x) := CFSG.Open.isElemAbelian_zpowers hxp
    have hcomm : ∀ a ∈ E ⊓ C, ∀ b ∈ Subgroup.zpowers x, a * b = b * a := by
      intro a ha b hb
      have hax : a * x = x * a := Subgroup.mem_centralizer_singleton_iff.1 ha.2
      have hbC : b ∈ centralizer ({a} : Set P) :=
        Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 hax.symm) hb
      exact (Subgroup.mem_centralizer_singleton_iff.1 hbC).symm
    have hF : IsElemAbelian p (E ⊓ C ⊔ Subgroup.zpowers x) :=
      IsElemAbelian.sup_of_commute hH'el hKel hcomm
    have hFC : E ⊓ C ⊔ Subgroup.zpowers x ≤ C := sup_le inf_le_right (Subgroup.zpowers_le.2 hxC)
    have hinter : (E ⊓ C) ⊓ Subgroup.zpowers x = ⊥ := by
      rw [eq_bot_iff]
      rintro y ⟨⟨hyE, -⟩, hyK⟩
      rw [Subgroup.mem_bot]
      by_contra hy1
      have hyo : orderOf y = p := orderOf_eq_prime (hE.2 y hyE) hy1
      have hzz : Subgroup.zpowers y = Subgroup.zpowers x :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hyK) (by
          rw [Nat.card_zpowers, Nat.card_zpowers, hyo, hx])
      have hxE' : x ∈ E := by
        have hxy : x ∈ Subgroup.zpowers y := by
          rw [hzz]
          exact Subgroup.mem_zpowers x
        exact (Subgroup.zpowers_le.2 hyE) hxy
      exact hxE hxE'
    have hcardF : p ^ (j + 1) ≤ Nat.card ↥(E ⊓ C ⊔ Subgroup.zpowers x) := by
      have hinj : Function.Injective (fun q : ↥(E ⊓ C) × ↥(Subgroup.zpowers x) =>
          (⟨(q.1 : P) * (q.2 : P), mul_mem (Subgroup.mem_sup_left q.1.2)
            (Subgroup.mem_sup_right q.2.2)⟩ :
            ↥(E ⊓ C ⊔ Subgroup.zpowers x))) := by
        rintro ⟨h1, k1⟩ ⟨h2, k2⟩ heq
        have heq' : (h1 : P) * (k1 : P) = (h2 : P) * (k2 : P) := congrArg Subtype.val heq
        have hw : ((h2 : P))⁻¹ * (h1 : P) = (k2 : P) * ((k1 : P))⁻¹ := by
          calc ((h2 : P))⁻¹ * (h1 : P)
              = ((h2 : P))⁻¹ * ((h1 : P) * (k1 : P)) * ((k1 : P))⁻¹ := by group
            _ = ((h2 : P))⁻¹ * ((h2 : P) * (k2 : P)) * ((k1 : P))⁻¹ := by rw [heq']
            _ = (k2 : P) * ((k1 : P))⁻¹ := by group
        have hmem : ((h2 : P))⁻¹ * (h1 : P) ∈ (E ⊓ C) ⊓ Subgroup.zpowers x :=
          ⟨(E ⊓ C).mul_mem ((E ⊓ C).inv_mem h2.2) h1.2, by
            rw [hw]
            exact (Subgroup.zpowers x).mul_mem k2.2 ((Subgroup.zpowers x).inv_mem k1.2)⟩
        rw [hinter, Subgroup.mem_bot, inv_mul_eq_one] at hmem
        have hk12 : (k2 : P) * ((k1 : P))⁻¹ = 1 := by rw [← hw, hmem, inv_mul_cancel]
        have e1 : h1 = h2 := Subtype.ext (hmem.symm)
        have e2 : k1 = k2 := Subtype.ext (mul_inv_eq_one.1 hk12).symm
        rw [e1, e2]
      have hle := Nat.card_le_card_of_injective _ hinj
      rw [Nat.card_prod, hj, Nat.card_zpowers, hx, ← pow_succ] at hle
      exact hle
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 (fun q : ↥(E ⊓ C ⊔ Subgroup.zpowers x) =>
      ⟨1, Subtype.ext (by simpa using hF.2 q.1 q.2)⟩)
    rw [hm] at hcardF
    have hm3 : 3 ≤ m := by
      have h1 : j + 1 ≤ m := (Nat.pow_le_pow_iff_right hp.one_lt).1 hcardF
      omega
    exact le_trans hm3 (le_pRank_of_isElemAbelian_le hFC hF hm)

end CFSG.LocalAnalysis.RankFourTheoremC
