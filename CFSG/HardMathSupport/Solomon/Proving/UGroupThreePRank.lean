module

public import CFSG.HardMathSupport.Solomon.Proving.UGroupCaseBKlein
public import CFSG.HardMathSupport.Solomon.Proving.UGroupCentral
public import CFSG.HardMathSupport.Solomon.Proving.UGroupCaseB

public section

namespace CFSG.HardMathSupport.Solomon.Proving

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.UniquenessMaximal

variable {G : Type} [Group G]

theorem exists_elemAbelian_card_ge_eight [Finite G] {T : Subgroup G} (h3 : 3 ≤ pRank 2 T) :
    ∃ E : Subgroup G, E ≤ T ∧ IsElemAbelian 2 E ∧ 8 ≤ Nat.card E := by
  have hbdd : BddAbove {k : ℕ | ∃ E : Subgroup G, E ≤ T ∧ IsElemAbelian 2 E ∧
      Nat.card E = 2 ^ k} := by
    refine ⟨Nat.card G, ?_⟩
    rintro k ⟨E, -, -, hk⟩
    have h1 : 2 ^ k ≤ Nat.card G := hk ▸ Subgroup.card_le_card_group E
    exact le_trans (Nat.lt_two_pow_self).le h1
  have hne : {k : ℕ | ∃ E : Subgroup G, E ≤ T ∧ IsElemAbelian 2 E ∧
      Nat.card E = 2 ^ k}.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have h0 : pRank 2 T = 0 := by
      unfold pRank
      rw [hne]
      simp
    omega
  obtain ⟨E, hET, hE, hEcard⟩ := Nat.sSup_mem hne hbdd
  have h3' : 3 ≤ sSup {k : ℕ | ∃ E : Subgroup G, E ≤ T ∧ IsElemAbelian 2 E ∧
      Nat.card E = 2 ^ k} := h3
  refine ⟨E, hET, hE, ?_⟩
  rw [hEcard]
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ sSup {k : ℕ | ∃ E : Subgroup G, E ≤ T ∧ IsElemAbelian 2 E ∧
        Nat.card E = 2 ^ k} := Nat.pow_le_pow_right (by norm_num) h3'

theorem exists_central_involution [Finite G] {T : Subgroup G} (hT : IsPGroup 2 T)
    (hT1 : 1 < Nat.card T) :
    ∃ z : G, z ∈ T ∧ z ^ 2 = 1 ∧ z ≠ 1 ∧ ∀ t ∈ T, t * z = z * t := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial T := (Finite.one_lt_card_iff_nontrivial).1 hT1
  have hZp : IsPGroup 2 (Subgroup.center T) := hT.to_subgroup _
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hZp
  have : Nontrivial (Subgroup.center T) := hT.center_nontrivial
  have hZ1 : 1 < Nat.card (Subgroup.center T) := Finite.one_lt_card
  have h2dvd : 2 ∣ Nat.card (Subgroup.center T) := by
    rw [hn] at hZ1 ⊢
    rcases n with _ | n
    · simp at hZ1
    · exact dvd_pow_self 2 (Nat.succ_ne_zero n)
  let : Fintype (Subgroup.center T) := Fintype.ofFinite _
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card (G := Subgroup.center T) 2
    (by rwa [Nat.card_eq_fintype_card] at h2dvd)
  have hy2 : y ^ 2 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hy
    norm_num at hy
  refine ⟨((y : T) : G), (y : T).2, ?_, ?_, ?_⟩
  · have h1 : ((y : T)) ^ 2 = (1 : T) := by
      have := congrArg (fun w : Subgroup.center T => ((w : T))) hy2
      simpa using this
    have h2 := congrArg (fun w : T => (w : G)) h1
    simpa using h2
  · intro h
    apply hy1
    apply Subtype.ext
    apply Subtype.ext
    simpa using h
  · intro t ht
    have hc := Subgroup.mem_center_iff.1 y.2 ⟨t, ht⟩
    have := congrArg Subtype.val hc
    simpa using this

theorem odd_of_involution_conj {f a : G} {N : ℕ} {k : ℤ} (ha1 : a ≠ 1) (haN : a ^ (2 ^ N) = 1)
    (hf2 : f ^ 2 = 1) (hfa : f * a * f⁻¹ = a ^ k) : k % 2 = 1 := by
  have hff : f * f = 1 := by rw [← pow_two]; exact hf2
  have hfinv : f⁻¹ = f := inv_eq_of_mul_eq_one_right hff
  have hF : (a ^ k) ^ k = a := by
    calc (a ^ k) ^ k = (f * a * f⁻¹) ^ k := by rw [hfa]
      _ = f * a ^ k * f⁻¹ := conj_zpow
      _ = f * (f * a * f⁻¹) * f⁻¹ := by rw [← hfa]
      _ = (f * f) * a * (f⁻¹ * f⁻¹) := by group
      _ = a := by rw [hfinv, hff, one_mul, mul_one]
  have hpow : a ^ (k * k) = a := by rw [zpow_mul]; exact hF
  have hord : orderOf a ∣ 2 ^ N := orderOf_dvd_of_pow_eq_one haN
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
  have hi1 : i ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hi
    exact ha1 (orderOf_eq_one_iff.1 hi)
  have h2ord : (2 : ℤ) ∣ (orderOf a : ℤ) := by
    rw [hi]
    exact_mod_cast dvd_pow_self 2 hi1
  have hdiv : (orderOf a : ℤ) ∣ k * k - 1 := by
    apply orderOf_dvd_iff_zpow_eq_one.2
    rw [zpow_sub_one, hpow, mul_inv_cancel]
  have h2 : (2 : ℤ) ∣ k * k - 1 := dvd_trans h2ord hdiv
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · exfalso
    obtain ⟨m, rfl⟩ := Int.dvd_of_emod_eq_zero h
    have e : (2 * m) * (2 * m) - 1 = 2 * (2 * m * m - 1) + 1 := by ring
    rw [e] at h2
    have h3 : (2 : ℤ) ∣ 1 := (dvd_add_right (dvd_mul_right 2 _)).1 h2
    norm_num at h3
  · exact h

@[expose] def omegaOne (A : Subgroup G) (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    Subgroup G where
  carrier := {x | x ∈ A ∧ x ^ 2 = 1}
  mul_mem' := fun {a b} ha hb => ⟨A.mul_mem ha.1 hb.1, by
    rw [Commute.mul_pow (hAab a ha.1 b hb.1 : Commute a b) 2, ha.2, hb.2, one_mul]⟩
  one_mem' := ⟨A.one_mem, by simp⟩
  inv_mem' := fun {x} hx => ⟨A.inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩

theorem mem_omegaOne {A : Subgroup G} {hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a} {y : G} :
    y ∈ omegaOne A hAab ↔ y ∈ A ∧ y ^ 2 = 1 := Iff.rfl

theorem mem_normalizer_of_conj {M : Subgroup G} {t : G}
    (h1 : ∀ x ∈ M, t * x * t⁻¹ ∈ M) (h2 : ∀ x ∈ M, t⁻¹ * x * t⁻¹⁻¹ ∈ M) :
    t ∈ Subgroup.normalizer (M : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact fun hx => h1 x hx
  · intro hx
    have h := h2 _ hx
    have e : t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x := by group
    rwa [e] at h

theorem klein_of_nonunique_involution [Finite G] {T A : Subgroup G} {z x : G} (hT : IsPGroup 2 T)
    (hAT : A ≤ T) (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hAn : ∀ t ∈ T, ∀ a ∈ A, t * a * t⁻¹ ∈ A)
    (hz : z ∈ A) (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) (hzc : ∀ t ∈ T, t * z = z * t)
    (hx : x ∈ A) (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1) (hxz : x ≠ z) :
    ∃ U : Subgroup G, IsPPlane 2 U ∧ U ≤ T ∧ T ≤ Subgroup.normalizer (U : Set G) := by
  obtain ⟨M, hM_eq⟩ : ∃ M : Subgroup G, M = omegaOne A hAab := ⟨_, rfl⟩
  have hmem : ∀ y : G, y ∈ M ↔ y ∈ A ∧ y ^ 2 = 1 := by
    intro y
    rw [hM_eq]
    exact mem_omegaOne
  have hMA : ∀ y ∈ M, y ∈ A := fun y hy => ((hmem y).1 hy).1
  have hMT : M ≤ T := fun y hy => hAT (hMA y hy)
  have hzM : z ∈ M := (hmem z).2 ⟨hz, hz2⟩
  have hxM : x ∈ M := (hmem x).2 ⟨hx, hx2⟩
  have hM : IsElemAbelian 2 M :=
    ⟨⟨⟨fun p q => Subtype.ext (hAab p.1 (hMA p p.2) q.1 (hMA q q.2))⟩⟩,
      fun y hy => ((hmem y).1 hy).2⟩
  have hMnorm : ∀ t ∈ T, ∀ y ∈ M, t * y * t⁻¹ ∈ M := fun t ht y hy =>
    (hmem _).2 ⟨hAn t ht y (hMA y hy), by
      rw [conj_pow, ((hmem y).1 hy).2, mul_one, mul_inv_cancel]⟩
  have hMn : T ≤ Subgroup.normalizer (M : Set G) := fun t ht =>
    mem_normalizer_of_conj (fun y hy => hMnorm t ht y hy)
      (fun y hy => hMnorm t⁻¹ (T.inv_mem ht) y hy)
  have hMcard : 4 ≤ Nat.card M := by
    have hK := isPPlane_kleinOf (ha := hx2) (hb := hz2) (hab := hAab x hx z hz) hx1 hz1 hxz
    have hle : kleinOf hx2 hz2 (hAab x hx z hz) ≤ M := by
      intro y hy
      rw [mem_kleinOf] at hy
      rcases hy with h | h | h | h
      · rw [h]; exact M.one_mem
      · rw [h]; exact hxM
      · rw [h]; exact hzM
      · rw [h]; exact M.mul_mem hxM hzM
    have h1 := Subgroup.card_le_of_le hle
    have h4 : Nat.card (kleinOf hx2 hz2 (hAab x hx z hz)) = 4 := by
      rw [hK.2]
      norm_num
    omega
  exact normal_klein_of_normal_elemAbelian hT hMT hMn hM hMcard hzM hz1 hzc

theorem exists_mod_four_involution [Finite G] {T A : Subgroup G} {a z : G} (hT : IsPGroup 2 T)
    (hAT : A ≤ T) (hAn : ∀ t ∈ T, ∀ x ∈ A, t * x * t⁻¹ ∈ A)
    (hAgen : ∀ x ∈ A, ∃ j : ℤ, x = a ^ j) (ha : a ∈ A) (ha1 : a ≠ 1)
    (hz : z ∈ A) (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) (hzc : ∀ t ∈ T, t * z = z * t)
    (hu : ∀ x ∈ A, x ^ 2 = 1 → x = 1 ∨ x = z)
    {E : Subgroup G} (hET : E ≤ T) (hE : IsElemAbelian 2 E) (h8 : 8 ≤ Nat.card E) :
    ∃ f : G, f ∈ T ∧ f ^ 2 = 1 ∧ f ∉ A ∧ ∃ k : ℤ, k % 4 = 1 ∧ f * a * f⁻¹ = a ^ k := by
  obtain ⟨N, hN⟩ := hT ⟨a, hAT ha⟩
  have haN : a ^ (2 ^ N) = 1 := by
    have := congrArg Subtype.val hN
    simpa using this
  have hEA : ¬ E ≤ A := by
    intro hEA
    have hsub : E ≤ Subgroup.zpowers z := by
      intro x hx
      rcases hu x (hEA hx) (hE.2 x hx) with h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [h]; exact Subgroup.mem_zpowers z
    have h1 := Subgroup.card_le_of_le hsub
    have hzc2 : Nat.card (Subgroup.zpowers z) = 2 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hz2 hz1]
    omega
  obtain ⟨f1, hf1E, hf1A⟩ : ∃ f1 ∈ E, f1 ∉ A := by
    by_contra h
    apply hEA
    intro x hx
    by_contra hxA
    exact h ⟨x, hx, hxA⟩
  have hf1T : f1 ∈ T := hET hf1E
  have hf12 : f1 ^ 2 = 1 := hE.2 f1 hf1E
  have hf1one : f1 ≠ 1 := fun h => hf1A (by rw [h]; exact A.one_mem)
  have hf1z : f1 ≠ z := fun h => hf1A (by rw [h]; exact hz)
  obtain ⟨k1, hk1⟩ := hAgen _ (hAn f1 hf1T a ha)
  have hk1odd : k1 % 2 = 1 := odd_of_involution_conj ha1 haN hf12 hk1
  by_cases hk1m : k1 % 4 = 1
  · exact ⟨f1, hf1T, hf12, hf1A, k1, hk1m, hk1⟩
  have hk1m3 : k1 % 4 = 3 := by omega
  obtain ⟨H0, hH0⟩ : ∃ H : Subgroup G, H = kleinOf hf12 hz2 (hzc f1 hf1T) := ⟨_, rfl⟩
  have hH0m : ∀ y : G, y ∈ H0 ↔ y = 1 ∨ y = f1 ∨ y = z ∨ y = f1 * z := by
    intro y
    rw [hH0]
    exact mem_kleinOf
  have hH0c : Nat.card H0 = 4 := by
    rw [hH0, (isPPlane_kleinOf (ha := hf12) (hb := hz2) (hab := hzc f1 hf1T) hf1one hz1 hf1z).2]
    norm_num
  obtain ⟨g, hgE, hgH0⟩ : ∃ g ∈ E, g ∉ H0 := by
    by_contra h
    have hle : E ≤ H0 := fun x hx => by
      by_contra hx'
      exact h ⟨x, hx, hx'⟩
    have h1 := Subgroup.card_le_of_le hle
    omega
  have hgT : g ∈ T := hET hgE
  have hg2 : g ^ 2 = 1 := hE.2 g hgE
  have hgA : g ∉ A := by
    intro h
    apply hgH0
    rcases hu g h hg2 with e | e
    · rw [hH0m]; exact Or.inl e
    · rw [hH0m]; exact Or.inr (Or.inr (Or.inl e))
  obtain ⟨kg, hkg⟩ := hAgen _ (hAn g hgT a ha)
  have hkgodd : kg % 2 = 1 := odd_of_involution_conj ha1 haN hg2 hkg
  by_cases hkgm : kg % 4 = 1
  · exact ⟨g, hgT, hg2, hgA, kg, hkgm, hkg⟩
  have hkgm3 : kg % 4 = 3 := by omega
  have hcomm : Commute f1 g := by
    have := congrArg Subtype.val (hE.1.is_comm.comm (⟨f1, hf1E⟩ : E) ⟨g, hgE⟩)
    exact this
  have hfg2 : (f1 * g) ^ 2 = 1 := by
    rw [hcomm.mul_pow, hf12, hg2, one_mul]
  have hfgT : f1 * g ∈ T := T.mul_mem hf1T hgT
  have hfgA : f1 * g ∉ A := by
    intro h
    have hg' : g = f1 * (f1 * g) := by
      rw [← mul_assoc, ← pow_two, hf12, one_mul]
    rcases hu _ h hfg2 with e | e
    · apply hgH0
      rw [hH0m]
      rw [e, mul_one] at hg'
      exact Or.inr (Or.inl hg')
    · apply hgH0
      rw [hH0m]
      rw [e] at hg'
      exact Or.inr (Or.inr (Or.inr hg'))
  have hconj : (f1 * g) * a * (f1 * g)⁻¹ = a ^ (k1 * kg) := by
    calc (f1 * g) * a * (f1 * g)⁻¹ = f1 * (g * a * g⁻¹) * f1⁻¹ := by group
      _ = f1 * a ^ kg * f1⁻¹ := by rw [hkg]
      _ = (f1 * a * f1⁻¹) ^ kg := by rw [conj_zpow]
      _ = (a ^ k1) ^ kg := by rw [hk1]
      _ = a ^ (k1 * kg) := by rw [← zpow_mul]
  have hmod : (k1 * kg) % 4 = 1 := by
    have := Int.mul_emod k1 kg 4
    rw [hk1m3, hkgm3] at this
    exact this.trans (by norm_num)
  exact ⟨f1 * g, hfgT, hfg2, hfgA, k1 * kg, hmod, hconj⟩

theorem klein_of_maxNormalAbelian [Finite G] {T A : Subgroup G} {z : G} (hT : IsPGroup 2 T)
    (hAT : A ≤ T) (hAn : ∀ t ∈ T, ∀ a ∈ A, t * a * t⁻¹ ∈ A)
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hmax : ∀ B : Subgroup G, B ≤ T → (∀ t ∈ T, ∀ b ∈ B, t * b * t⁻¹ ∈ B) →
      (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) → A ≤ B → B ≤ A)
    (hz : z ∈ A) (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) (hzc : ∀ t ∈ T, t * z = z * t)
    {E : Subgroup G} (hET : E ≤ T) (hE : IsElemAbelian 2 E) (h8 : 8 ≤ Nat.card E) :
    ∃ U : Subgroup G, IsPPlane 2 U ∧ U ≤ T ∧ T ≤ Subgroup.normalizer (U : Set G) := by
  classical
  by_cases hinv : ∃ x ∈ A, x ^ 2 = 1 ∧ x ≠ 1 ∧ x ≠ z
  · obtain ⟨x, hxA, hx2, hx1, hxz⟩ := hinv
    exact klein_of_nonunique_involution hT hAT hAab hAn hz hz2 hz1 hzc hxA hx2 hx1 hxz
  have hu : ∀ x ∈ A, x ^ 2 = 1 → x = 1 ∨ x = z := by
    intro x hxA hx2
    by_contra hcon
    push Not at hcon
    exact hinv ⟨x, hxA, hx2, hcon.1, hcon.2⟩
  let : CommGroup A :=
    { (inferInstance : Group A) with mul_comm := fun x y => Subtype.ext (hAab x x.2 y y.2) }
  have hAp : IsPGroup 2 A := fun x => by
    obtain ⟨N, hN⟩ := hT ⟨(x : G), hAT x.2⟩
    refine ⟨N, Subtype.ext ?_⟩
    have := congrArg Subtype.val hN
    simpa using this
  have hcyc : IsCyclic A := isCyclic_of_unique_involution (z := (⟨z, hz⟩ : A)) hAp
    (fun x hx => by
      have hx' : (x : G) ^ 2 = 1 := by
        have := congrArg Subtype.val hx
        simpa using this
      rcases hu x x.2 hx' with h | h
      · left; exact Subtype.ext (by simpa using h)
      · right; exact Subtype.ext h)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := A)
  have hAgen0 : ∀ x ∈ A, ∃ j : ℤ, x = (g : G) ^ j := by
    intro x hxA
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨x, hxA⟩)
    refine ⟨j, ?_⟩
    have := congrArg Subtype.val hj
    simpa using this.symm
  obtain ⟨a, haA, hAgen⟩ : ∃ a : G, a ∈ A ∧ ∀ x ∈ A, ∃ j : ℤ, x = a ^ j :=
    ⟨g, g.2, hAgen0⟩
  have ha1 : a ≠ 1 := by
    intro h
    apply hz1
    obtain ⟨j, hj⟩ := hAgen z hz
    rw [hj, h, one_zpow]
  obtain ⟨f, hfT, hf2, hfA, k, hk, hfa⟩ :=
    exists_mod_four_involution hT hAT hAn hAgen haA ha1 hz hz2 hz1 hzc hu hET hE h8
  exact normal_klein_of_involution_coset hT hAT hAn hAgen haA
    (fun c hc hcomm => mem_of_centralizes_maxNormalAbelian hT hAT hAn hAab hmax hc hcomm)
    hz hz2 hz1 hzc hu hfT hf2 hfA hk hfa

theorem exists_normal_klein_of_three_le_pRank [Finite G] {T : Subgroup G} (hT : IsPGroup 2 T)
    (h3 : 3 ≤ pRank 2 T) :
    ∃ U : Subgroup G, IsPPlane 2 U ∧ U ≤ T ∧ T ≤ Subgroup.normalizer (U : Set G) := by
  obtain ⟨E, hET, hE, h8⟩ := exists_elemAbelian_card_ge_eight h3
  have hT1 : 1 < Nat.card T := by
    have := Subgroup.card_le_of_le hET
    omega
  obtain ⟨z, hzT, hz2, hz1, hzc⟩ := exists_central_involution hT hT1
  obtain ⟨A, hAT, hzA, hAn, hAab, hmax⟩ := exists_maximal_normal_abelian hzT hzc
  exact klein_of_maxNormalAbelian hT hAT hAn hAab hmax hzA hz2 hz1 hzc hET hE h8

theorem exists_isUGroup_of_three_le_pRank [Finite G] {T : Subgroup G} (hT : IsPGroup 2 T)
    (h3 : 3 ≤ pRank 2 T) : ∃ U : Subgroup G, IsUGroup 2 T U := by
  by_cases h2 : 2 ≤ pRank 2 (centerOf T)
  · exact exists_isUGroup_of_two_le_pRank_centerOf h2
  · obtain ⟨U, hUp, hUT, hTN⟩ := exists_normal_klein_of_three_le_pRank hT h3
    refine ⟨U, hUT, hTN, hUp, fun h => ?_⟩
    exact absurd h (by omega)

end CFSG.HardMathSupport.Solomon.Proving

end
