module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3L221Diag
public import CFSG.ClassicalInvolution.SubnormalCommutator
public import CFSG.Quasithin.Background.A4Coprime
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Critical
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3L221Cases

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.F3L226S

open CFSG Subgroup
open scoped MatrixGroups commutatorElement

theorem sl23_pow_twelve : ∀ x : SL(2, ZMod 3), x ^ 12 = 1 := by
  decide +kernel

theorem sl23_two_cases : ∀ x : SL(2, ZMod 3), x ^ 4 = 1 → x = 1 ∨ x = -1 ∨ x ^ 2 = -1 := by
  decide +kernel

theorem sl23_conj : ∀ x y : SL(2, ZMod 3), x ^ 2 = -1 → y ^ 2 = -1 →
    ∃ g : SL(2, ZMod 3), g * x = y * g := by
  decide +kernel

theorem sl23_anticomm : ∃ a b : SL(2, ZMod 3), a ^ 2 = -1 ∧ b ^ 2 = -1 ∧ a * b = -1 * (b * a) := by
  decide +kernel

theorem sl23_neg_one_ne_one : (-1 : SL(2, ZMod 3)) ≠ 1 := by
  decide +kernel

theorem sl23_pow_four {x : SL(2, ZMod 3)} {n : ℕ} (hx : x ^ 2 ^ n = 1) : x ^ 4 = 1 := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hx)
  have h12 : 2 ^ j ∣ 12 := hj ▸ orderOf_dvd_of_pow_eq_one (sl23_pow_twelve x)
  have hj2 : j ≤ 2 := by
    by_contra hlt
    have h8 : 2 ^ 3 ∣ 12 := (Nat.pow_dvd_pow 2 (by omega)).trans h12
    norm_num at h8
  exact orderOf_dvd_iff_pow_eq_one.mp (hj ▸ Nat.pow_dvd_pow 2 hj2)

theorem sl23_eq_of_sq_eq_one {x : SL(2, ZMod 3)} (hx : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  rcases sl23_two_cases x (by rw [show 4 = 2 * 2 from rfl, pow_mul, hx, one_pow]) with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd (h.symm.trans hx) sl23_neg_one_ne_one

theorem exists_two_element_map {H Q : Type*} [Group H] [Finite H] [Group Q] (φ : H →* Q) (x : H)
    {k : ℕ} (hk : φ x ^ 2 ^ k = 1) :
    ∃ y ∈ zpowers x, (∃ m : ℕ, y ^ 2 ^ m = 1) ∧ φ y = φ x := by
  set n := orderOf x with hn
  set a := n.factorization 2 with ha
  set o := n / 2 ^ a with ho
  have hn0 : n ≠ 0 := (orderOf_pos x).ne'
  have hno : 2 ^ a * o = n := Nat.ordProj_mul_ordCompl_eq_self n 2
  have hc2o : Nat.Coprime 2 o := Nat.coprime_ordCompl Nat.prime_two hn0
  have h1 : (x ^ o) ^ 2 ^ a = 1 := by
    rw [← pow_mul, mul_comm, hno, hn, pow_orderOf_eq_one]
  have hcop : Nat.Coprime o (orderOf (φ x)) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
    rw [hj]
    exact Nat.Coprime.pow_right j hc2o.symm
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  refine ⟨(x ^ o) ^ m, pow_mem (pow_mem (mem_zpowers x) _) _, ⟨a, ?_⟩, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, h1, one_pow]
  · rw [map_pow, map_pow, hm]

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem mem_oPrimeResidualOf_of_pow {L : Subgroup X} {x : ↥L} {m : ℕ} (hx : x ^ 2 ^ m = 1) :
    (x : X) ∈ GH74.GLS.oPrimeResidualOf 2 L :=
  ⟨x, subset_closure ⟨m, hx⟩, rfl⟩

omit [Finite X] in
theorem exists_pow_eq_one_of_isPGroup {U : Subgroup X} (hU : IsPGroup 2 U) {u : X} (hu : u ∈ U) :
    ∃ n : ℕ, u ^ 2 ^ n = 1 := by
  obtain ⟨n, hn⟩ := hU ⟨u, hu⟩
  exact ⟨n, by simpa using congrArg Subtype.val hn⟩

omit [Finite X] in
theorem mem_normalizer_of_normal {N : Subgroup X} (hN : N.Normal) (g : X) :
    g ∈ normalizer (N : Set X) := by
  rw [normalizer_eq_top_iff.mpr hN]
  exact mem_top g

omit [Finite X] in
theorem mem_normalizer_inf {A B : Subgroup X} {g : X} (hA : g ∈ normalizer (A : Set X))
    (hB : g ∈ normalizer (B : Set X)) : g ∈ normalizer ((A ⊓ B : Subgroup X) : Set X) := by
  rw [mem_normalizer_iff] at hA hB ⊢
  intro h
  simp only [mem_inf] at hA hB ⊢
  exact and_congr (hA h) (hB h)

omit [Finite X] in
theorem isSubnormal_subgroupOf_of_le {A D C : Subgroup X} (hDC : D ≤ C)
    (h : (A.subgroupOf C).IsSubnormal) : (A.subgroupOf D).IsSubnormal := by
  have h1 := h.subgroupOf (K := D.subgroupOf C)
  have heq : A.subgroupOf D = ((A.subgroupOf C).subgroupOf (D.subgroupOf C)).comap
      (subgroupOfEquivOfLe hDC).symm.toMonoidHom := by
    ext x
    exact Iff.rfl
  rw [heq]
  exact h1.comap _

theorem eq_one_of_mem_pPrimeCore {K : Subgroup X} {x : ↥K} (hx : x ∈ pPrimeCore 2 ↥K) {n : ℕ}
    (hxn : x ^ 2 ^ n = 1) : x = 1 := by
  have hodd := odd_card_pPrimeCore_two ↥K
  have h1 : orderOf (⟨x, hx⟩ : ↥(pPrimeCore 2 ↥K)) ∣ 2 ^ n :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hxn))
  have h2 : orderOf (⟨x, hx⟩ : ↥(pPrimeCore 2 ↥K)) ∣ Nat.card ↥(pPrimeCore 2 ↥K) :=
    orderOf_dvd_natCard _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  rcases j with _ | j
  · rw [pow_zero, orderOf_eq_one_iff] at hj
    exact congrArg Subtype.val hj
  · exfalso
    rw [hj, pow_succ] at h2
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (dvd_trans (dvd_mul_left 2 _) h2))

theorem mem_of_mk_eq {K T : Subgroup X} (hTn : ∀ k ∈ K, ∀ t ∈ T, k * t * k⁻¹ ∈ T) {x y : ↥K}
    (hyT : (y : X) ∈ T) (hxy : (QuotientGroup.mk x : ↥K ⧸ pPrimeCore 2 ↥K) = QuotientGroup.mk y)
    {n : ℕ} (hxn : (x : X) ^ 2 ^ n = 1) : (x : X) ∈ T := by
  set N := (pPrimeCore 2 ↥K).map K.subtype with hN
  have hNT : N ≤ normalizer (T : Set X) := by
    rintro _ ⟨w, -, rfl⟩
    rw [mem_normalizer_iff]
    intro t
    constructor
    · exact hTn w w.2 t
    · intro ht
      have h1 := hTn w⁻¹ (inv_mem w.2) _ ht
      simpa [mul_assoc] using h1
  have hodd : Odd (Nat.card N) := by
    rw [hN, Subgroup.card_map_of_injective K.subtype_injective]
    exact odd_card_pPrimeCore_two ↥K
  have hmem : (y⁻¹ * x : ↥K) ∈ pPrimeCore 2 ↥K := by
    have h1 := QuotientGroup.eq.mp hxy.symm
    exact h1
  have hx : (x : X) ∈ T ⊔ N := by
    have h1 : (x : X) = (y : X) * ((y⁻¹ * x : ↥K) : X) := by simp
    rw [h1]
    exact mul_mem (mem_sup_left hyT) (mem_sup_right ⟨_, hmem, rfl⟩)
  exact F3L221.mem_of_mem_sup_of_odd hNT hodd hx hxn

theorem psl23_lift_pow_four {α : SL(2, ZMod 3)} {n : ℕ}
    (h : (QuotientGroup.mk α : PSL(2, ZMod 3)) ^ 2 ^ n = 1) : α ^ 4 = 1 := by
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff,
    CFSG.ClassicalInvolution.mem_center_sl2_iff] at h
  refine sl23_pow_four (n := n + 1) ?_
  rcases h with h | h
  · rw [pow_succ, pow_mul, h, one_pow]
  · rw [pow_succ, pow_mul, h]
    decide +kernel

theorem mem_center_of_mulEquiv {Q R : Type*} [Group Q] [Group R] (e : Q ≃* R) {a : Q}
    (h : e a ∈ center R) : a ∈ center Q := by
  rw [mem_center_iff] at h ⊢
  intro g
  apply e.injective
  rw [map_mul, map_mul, h (e g)]

theorem sl23_quot_cases {Q : Type*} [Group Q] (e : Q ≃* SL(2, ZMod 3)) {a b : Q}
    (ha : a ∉ center Q) {na nb : ℕ} (han : a ^ 2 ^ na = 1) (hbn : b ^ 2 ^ nb = 1) :
    b = 1 ∨ b = a * a ∨ ∃ g : Q, b = g * a * g⁻¹ := by
  have ha4 : e a ^ 4 = 1 := sl23_pow_four (n := na) (by rw [← map_pow, han, map_one])
  have hb4 : e b ^ 4 = 1 := sl23_pow_four (n := nb) (by rw [← map_pow, hbn, map_one])
  have hasq : e a ^ 2 = -1 := by
    rcases sl23_two_cases _ ha4 with h | h | h
    · exact absurd (mem_center_of_mulEquiv e (by rw [h]; exact one_mem _)) ha
    · refine absurd (mem_center_of_mulEquiv e ?_) ha
      rw [h]
      exact (CFSG.ClassicalInvolution.mem_center_sl2_iff _).mpr (Or.inr rfl)
    · exact h
  rcases sl23_two_cases _ hb4 with h | h | h
  · exact Or.inl (e.injective (by rw [h, map_one]))
  · exact Or.inr (Or.inl (e.injective (by rw [h, map_mul, ← sq, hasq])))
  · obtain ⟨g, hg⟩ := sl23_conj _ _ hasq h
    refine Or.inr (Or.inr ⟨e.symm g, e.injective ?_⟩)
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hg]
    group

theorem psl23_quot_cases {Q : Type*} [Group Q] (e : Q ≃* PSL(2, ZMod 3)) {a b : Q}
    (ha : a ∉ center Q) {na nb : ℕ} (han : a ^ 2 ^ na = 1) (hbn : b ^ 2 ^ nb = 1) :
    b = 1 ∨ ∃ g : Q, b = g * a * g⁻¹ := by
  obtain ⟨α, hα⟩ := QuotientGroup.mk_surjective (e a)
  obtain ⟨β, hβ⟩ := QuotientGroup.mk_surjective (e b)
  have ha4 : α ^ 4 = 1 := psl23_lift_pow_four (n := na) (by rw [hα, ← map_pow, han, map_one])
  have hb4 : β ^ 4 = 1 := psl23_lift_pow_four (n := nb) (by rw [hβ, ← map_pow, hbn, map_one])
  have hone : ∀ {c : Q} {γ : SL(2, ZMod 3)}, (QuotientGroup.mk γ : PSL(2, ZMod 3)) = e c →
      (γ = 1 ∨ γ = -1) → c = 1 := fun {c γ} hγ h => by
    apply e.injective
    rw [← hγ, map_one]
    exact (QuotientGroup.eq_one_iff _).mpr ((CFSG.ClassicalInvolution.mem_center_sl2_iff _).mpr h)
  have hasq : α ^ 2 = -1 := by
    rcases sl23_two_cases _ ha4 with h | h | h
    · exact absurd (by rw [hone hα (Or.inl h)]; exact one_mem _) ha
    · exact absurd (by rw [hone hα (Or.inr h)]; exact one_mem _) ha
    · exact h
  rcases sl23_two_cases _ hb4 with h | h | h
  · exact Or.inl (hone hβ (Or.inl h))
  · exact Or.inl (hone hβ (Or.inr h))
  · obtain ⟨g, hg⟩ := sl23_conj _ _ hasq h
    refine Or.inr ⟨e.symm (QuotientGroup.mk g), e.injective ?_⟩
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, ← hα, ← hβ,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, hg]
    congr 1
    group

theorem central_or_le_of_normal_two {K A T : Subgroup X} (hK : IsSolvableTwoComponentIn K A)
    (hTK : T ≤ K) (hTn : ∀ k ∈ K, ∀ t ∈ T, k * t * k⁻¹ ∈ T)
    (hT2 : ∀ t ∈ T, ∃ n : ℕ, t ^ 2 ^ n = 1) :
    (∀ t ∈ T, ∀ k ∈ K, t * k = k * t) ∨ GH74.GLS.oPrimeResidualOf 2 K ≤ T := by
  by_cases hc : ∀ t ∈ T, ∀ k ∈ K, t * k = k * t
  · exact Or.inl hc
  right
  push Not at hc
  obtain ⟨t, htT, k₀, hk₀, htk⟩ := hc
  have htK := hTK htT
  obtain ⟨nt, hnt⟩ := hT2 t htT
  set R := pPrimeCore 2 ↥K with hR
  have htnc : (QuotientGroup.mk ⟨t, htK⟩ : ↥K ⧸ R) ∉ center (↥K ⧸ R) := by
    intro hcen
    apply htk
    have hc' := mem_center_iff.mp hcen (QuotientGroup.mk ⟨k₀, hk₀⟩)
    have h1 : (QuotientGroup.mk (⟨t, htK⟩ * ⟨k₀, hk₀⟩ * ⟨t, htK⟩⁻¹ * ⟨k₀, hk₀⟩⁻¹) :
        ↥K ⧸ R) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_inv, ← hc']
      group
    rw [QuotientGroup.eq_one_iff] at h1
    have h2 : t * k₀ * t⁻¹ * k₀⁻¹ ∈ T := by
      have h3 := hTn k₀ hk₀ t⁻¹ (inv_mem htT)
      rw [show t * k₀ * t⁻¹ * k₀⁻¹ = t * (k₀ * t⁻¹ * k₀⁻¹) by group]
      exact mul_mem htT h3
    obtain ⟨m, hm⟩ := hT2 _ h2
    have h5 := eq_one_of_mem_pPrimeCore h1 (n := m) (Subtype.ext (by simpa using hm))
    have h6 : t * k₀ * t⁻¹ * k₀⁻¹ = 1 := by simpa using congrArg Subtype.val h5
    calc t * k₀ = (t * k₀ * t⁻¹ * k₀⁻¹) * (k₀ * t) := by group
      _ = k₀ * t := by rw [h6, one_mul]
  have hta : (QuotientGroup.mk ⟨t, htK⟩ : ↥K ⧸ R) ^ 2 ^ nt = 1 := by
    rw [← QuotientGroup.mk_pow, show (⟨t, htK⟩ : ↥K) ^ 2 ^ nt = 1 from
      Subtype.ext (by simpa using hnt), QuotientGroup.mk_one]
  suffices hx : ∀ x : ↥K, (∃ n : ℕ, x ^ 2 ^ n = 1) → (x : X) ∈ T by
    rintro _ ⟨y, hy, rfl⟩
    have hle : GH74.GLS.oPrimeResidual 2 ↥K ≤ T.comap K.subtype :=
      (closure_le _).mpr fun w hw => hx w hw
    exact hle hy
  intro x ⟨n, hxn⟩
  have hxn' : (x : X) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hxn
  have hxa : (QuotientGroup.mk x : ↥K ⧸ R) ^ 2 ^ n = 1 := by
    rw [← QuotientGroup.mk_pow, hxn, QuotientGroup.mk_one]
  have hone : (QuotientGroup.mk x : ↥K ⧸ R) = 1 → (x : X) ∈ T := fun h => by
    rw [QuotientGroup.eq_one_iff] at h
    rw [eq_one_of_mem_pPrimeCore h hxn]
    exact one_mem _
  have hconj : ∀ g : ↥K ⧸ R, (QuotientGroup.mk x : ↥K ⧸ R) =
      g * QuotientGroup.mk ⟨t, htK⟩ * g⁻¹ → (x : X) ∈ T := fun g hg => by
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective g
    refine mem_of_mk_eq hTn (y := k * ⟨t, htK⟩ * k⁻¹) ?_ ?_ hxn'
    · simpa using hTn k k.2 t htT
    · rw [hg, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rcases hK.2.2.2 with he | he
  · obtain ⟨e⟩ := he
    rcases psl23_quot_cases e htnc hta hxa with h | ⟨g, hg⟩
    · exact hone h
    · exact hconj g hg
  · obtain ⟨e⟩ := he
    rcases sl23_quot_cases e htnc hta hxa with h | h | ⟨g, hg⟩
    · exact hone h
    · refine mem_of_mk_eq hTn (y := ⟨t, htK⟩ * ⟨t, htK⟩) (by simpa using mul_mem htT htT) ?_ hxn'
      rw [h, QuotientGroup.mk_mul]
    · exact hconj g hg

theorem exists_commutator_eq {L A U : Subgroup X} (hL : IsSolvableTwoComponentIn L A) {z : X}
    (hzL : z ∈ L) (hz : orderOf z = 2) (hzc : ∀ l ∈ L, l * z = z * l)
    (hLU : GH74.GLS.oPrimeResidualOf 2 L ≤ U) (hU : ∀ u ∈ U, ∃ n : ℕ, u ^ 2 ^ n = 1) :
    ∃ a ∈ GH74.GLS.oPrimeResidualOf 2 L, ∃ b ∈ GH74.GLS.oPrimeResidualOf 2 L,
      a * b * a⁻¹ * b⁻¹ = z := by
  obtain ⟨e⟩ := F3L221.nonempty_sl23_of_central hL hzL hz hzc
  set φ : ↥L →* SL(2, ZMod 3) := e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥L))
    with hφ
  have hφs : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ∀ x : ↥L, φ x = 1 → x ∈ pPrimeCore 2 ↥L := fun x hx =>
    (QuotientGroup.eq_one_iff x).mp (e.injective (by rw [map_one]; exact hx))
  have hz2 : z ^ 2 = 1 := by rw [← hz, pow_orderOf_eq_one]
  have hz2' : (⟨z, hzL⟩ : ↥L) ^ 2 = 1 := Subtype.ext (by simpa using hz2)
  have hφz : φ ⟨z, hzL⟩ = -1 := by
    rcases sl23_eq_of_sq_eq_one (by rw [← map_pow, hz2', map_one] : φ ⟨z, hzL⟩ ^ 2 = 1) with
      h | h
    · exact absurd (hker _ h) (F3L221.not_mem_pPrimeCore_of_orderOf hzL hz)
    · exact h
  obtain ⟨α, β, hα, hβ, hαβ⟩ := sl23_anticomm
  have h4 : ∀ γ : SL(2, ZMod 3), γ ^ 2 = -1 → γ ^ 2 ^ 2 = 1 := fun γ h => by
    rw [show 2 ^ 2 = 2 * 2 from rfl, pow_mul, h]
    decide +kernel
  obtain ⟨x₀, hx₀⟩ := hφs α
  obtain ⟨y₀, hy₀⟩ := hφs β
  obtain ⟨a, -, ⟨ma, hma⟩, ha⟩ :=
    exists_two_element_map φ x₀ (k := 2) (by rw [hx₀]; exact h4 α hα)
  obtain ⟨b, -, ⟨mb, hmb⟩, hb⟩ :=
    exists_two_element_map φ y₀ (k := 2) (by rw [hy₀]; exact h4 β hβ)
  have haO := mem_oPrimeResidualOf_of_pow hma
  have hbO := mem_oPrimeResidualOf_of_pow hmb
  have hzO : z ∈ GH74.GLS.oPrimeResidualOf 2 L :=
    mem_oPrimeResidualOf_of_pow (x := ⟨z, hzL⟩) (m := 1) (by rw [pow_one]; exact hz2')
  have hφc : φ (a * b * a⁻¹ * b⁻¹) = φ ⟨z, hzL⟩ := by
    rw [hφz, map_mul, map_mul, map_mul, map_inv, map_inv, ha, hb, hx₀, hy₀, hαβ]
    simp only [mul_assoc, mul_inv_cancel, mul_one]
  have hcz : a * b * a⁻¹ * b⁻¹ = ⟨z, hzL⟩ := by
    have h1 : (a * b * a⁻¹ * b⁻¹)⁻¹ * ⟨z, hzL⟩ ∈ pPrimeCore 2 ↥L :=
      hker _ (by rw [map_mul, map_inv, hφc, inv_mul_cancel])
    have hcU : ((a * b * a⁻¹ * b⁻¹ : ↥L) : X) ∈ U := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact mul_mem (mul_mem (mul_mem (hLU haO) (hLU hbO)) (inv_mem (hLU haO)))
        (inv_mem (hLU hbO))
    have h2 : (((a * b * a⁻¹ * b⁻¹)⁻¹ * ⟨z, hzL⟩ : ↥L) : X) ∈ U := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      exact mul_mem (inv_mem hcU) (hLU hzO)
    obtain ⟨n, hn⟩ := hU _ h2
    exact inv_mul_eq_one.mp (eq_one_of_mem_pPrimeCore h1 (n := n) (Subtype.ext (by simpa using hn)))
  refine ⟨a, haO, b, hbO, ?_⟩
  have h5 := congrArg Subtype.val hcz
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h5
  exact h5

theorem commutator_le_of_isSubnormal {C H U : Subgroup X} (hHC : H ≤ C)
    (hH : (H.subgroupOf C).IsSubnormal) (hUC : U ≤ C) (hCU : C ≤ normalizer (U : Set X))
    (hU : IsPGroup 2 U) {ν : X} (hνH : ν ∈ H) (hν : Odd (orderOf ν)) :
    ⁅U, zpowers ν⁆ ≤ H ⊓ U := by
  have h1 := Components.chain_map C.subtype (Components.chain_of_mathlib_subnormal hH)
  rw [map_subgroupOf_eq_of_le hHC, ← MonoidHom.range_eq_map, range_subtype] at h1
  exact CFSG.ClassicalInvolution.commutator_zpowers_le_of_isSubnormal h1 hUC hCU hU hνH hν

theorem centralizes_of_centralizes_commutator {U : Subgroup X} (hU : IsPGroup 2 U) {ν : X}
    (hν : Odd (orderOf ν)) (hνU : ν ∈ normalizer (U : Set X))
    (h : ∀ w ∈ ⁅U, zpowers ν⁆, w * ν = ν * w) : ∀ u ∈ U, ν * u = u * ν := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRW : zpowers ν ≤ normalizer (U : Set X) := zpowers_le.mpr hνU
  have hcop : Nat.Coprime (Nat.card (zpowers ν)) (Nat.card U) := by
    obtain ⟨k, hk⟩ := hU.exists_card_eq
    rw [Nat.card_zpowers, hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hν)
  have h1 := CFSG.ClassicalInvolution.commutator_le_commutator_commutator_of_coprime U
    (zpowers ν) hRW hcop
  have h2 : ⁅⁅U, zpowers ν⁆, zpowers ν⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer]
    intro w hw
    rw [mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    exact ((show Commute w ν from h w hw).zpow_right k).symm.eq
  have h3 : ⁅U, zpowers ν⁆ = ⊥ := le_bot_iff.mp (h2 ▸ h1)
  rw [commutator_eq_bot_iff_le_centralizer] at h3
  intro u hu
  exact mem_centralizer_iff.mp (h3 hu) ν (mem_zpowers ν)

theorem centralizes_of_axb {V B : Subgroup X} (hV : IsPGroup 2 V) {ν : X} (hν : Odd (orderOf ν))
    (hνV : ν ∈ normalizer (V : Set X)) (hBV : B ≤ normalizer (V : Set X))
    (hB : ∀ b ∈ B, ∃ k : ℕ, b ^ 2 ^ k ∈ centralizer (V : Set X))
    (hνB : ∀ b ∈ B, ν * b = b * ν)
    (hfix : ∀ v ∈ V, (∀ b ∈ B, v * b = b * v) → ν * v = v * ν) :
    ∀ v ∈ V, ν * v = v * ν := by
  have hA : zpowers ν = CFSG.Quasithin.oTwoUpper (zpowers ν) :=
    le_antisymm (zpowers_le.mpr (CFSG.Quasithin.mem_oTwoUpper_of_odd (mem_zpowers ν) hν))
      (CFSG.Quasithin.oTwoUpper_le _)
  have hAB : ⁅zpowers ν, B⁆ ≤ centralizer (V : Set X) := by
    have h1 : ⁅zpowers ν, B⁆ = ⊥ := by
      rw [commutator_eq_bot_iff_le_centralizer, zpowers_le, mem_centralizer_iff]
      intro b hb
      exact (hνB b hb).symm
    rw [h1]
    exact bot_le
  have hfix' : zpowers ν ≤ centralizer ((V ⊓ centralizer (B : Set X) : Subgroup X) : Set X) := by
    rw [zpowers_le, mem_centralizer_iff]
    intro v hv
    obtain ⟨hvV, hvB⟩ := mem_inf.mp hv
    exact (hfix v hvV fun b hb => (mem_centralizer_iff.mp hvB b hb).symm).symm
  have h := CFSG.Quasithin.A4.thompson_axb hV hA (zpowers_le.mpr hνV) hBV hB hAB hfix'
  intro v hv
  exact (mem_centralizer_iff.mp (h (mem_zpowers ν)) v hv).symm

theorem exists_critical (X : Type) [Group X] [Finite X] :
    ∃ P : Subgroup X, P ≤ pCore 2 X ∧ P.Normal ∧ ⁅P, P⁆ ≤ centralizer (P : Set X) ∧
      pCore 2 X ⊓ centralizer (P : Set X) ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨C₀, hchar, -, hcomm, hcen⟩, -⟩ :=
    SectionRank.Ccomm.thompson_critical_subgroup (P := ↥(pCore 2 X)) (p := 2) pCore_isPGroup
  refine ⟨C₀.map (pCore 2 X).subtype, map_subtype_le _, ⟨fun n hn g => ?_⟩, ?_, ?_⟩
  · obtain ⟨c, hc, rfl⟩ := hn
    have h1 := (characteristic_iff_map_eq.mp hchar) (MulAut.conjNormal g)
    have h2 : MulAut.conjNormal g c ∈ C₀ := by
      rw [← h1]
      exact ⟨c, hc, rfl⟩
    exact ⟨_, h2, by simp [MulAut.conjNormal_apply]⟩
  · rw [commutator_le]
    rintro _ ⟨a, -, rfl⟩ _ ⟨b, hb, rfl⟩
    have h1 : ⁅a, b⁆ ∈ C₀ ⊓ centralizer (C₀ : Set ↥(pCore 2 X)) :=
      hcomm (commutator_mem_commutator (mem_top a) hb)
    rw [mem_centralizer_iff]
    rintro _ ⟨c, hc, rfl⟩
    have h2 := congrArg Subtype.val (mem_centralizer_iff.mp (mem_inf.mp h1).2 c hc)
    simpa [commutatorElement_def] using h2
  · rintro x ⟨hxQ, hxc⟩
    have h1 : (⟨x, hxQ⟩ : ↥(pCore 2 X)) ∈ centralizer (C₀ : Set ↥(pCore 2 X)) := by
      rw [mem_centralizer_iff]
      intro c hc
      exact Subtype.ext (mem_centralizer_iff.mp hxc c ⟨c, hc, rfl⟩)
    rw [hcen] at h1
    exact ⟨⟨x, hxQ⟩, (mem_inf.mp h1).1, rfl⟩

theorem centralizes_pCore_of_centralizes_fixed {P : Subgroup X} (hPQ : P ≤ pCore 2 X)
    (hPn : P.Normal) (hPcen : pCore 2 X ⊓ centralizer (P : Set X) ≤ P) {z ν : X}
    (hz : z ^ 2 = 1) (hν : Odd (orderOf ν)) (hνz : ν * z = z * ν)
    (hfix : ∀ u ∈ P, u * z = z * u → ν * u = u * ν) : ∀ u ∈ pCore 2 X, ν * u = u * ν := by
  have hQ2 : IsPGroup 2 (pCore 2 X) := pCore_isPGroup
  have hP2 : IsPGroup 2 P := hQ2.to_le hPQ
  have hQn : (pCore 2 X).Normal := pCore_normal
  have h1 : ∀ u ∈ P, ν * u = u * ν := by
    refine centralizes_of_axb (B := zpowers z) hP2 hν (mem_normalizer_of_normal hPn ν)
      (fun b _ => mem_normalizer_of_normal hPn b) ?_ ?_ ?_
    · intro b hb
      have hb2 : b ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp
        ((orderOf_dvd_of_mem_zpowers hb).trans (orderOf_dvd_of_pow_eq_one hz))
      exact ⟨1, by rw [pow_one, hb2]; exact one_mem _⟩
    · intro b hb
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hb
      exact ((show Commute ν z from hνz).zpow_right k).eq
    · intro v hv hvz
      exact hfix v hv (hvz z (mem_zpowers z))
  refine centralizes_of_axb (B := P) hQ2 hν (mem_normalizer_of_normal hQn ν)
    (fun b _ => mem_normalizer_of_normal hQn b) ?_ h1 ?_
  · intro b hb
    obtain ⟨k, hk⟩ := exists_pow_eq_one_of_isPGroup hP2 hb
    exact ⟨k, by rw [hk]; exact one_mem _⟩
  · intro v hv hvP
    exact h1 v (hPcen (mem_inf.mpr ⟨hv, mem_centralizer_iff.mpr fun b hb => (hvP b hb).symm⟩))

theorem oPrimeResidualOf_le_of_critical {P : Subgroup X} (hPQ : P ≤ pCore 2 X) (hPn : P.Normal)
    (hPcen : pCore 2 X ⊓ centralizer (P : Set X) ≤ P) {z : X} (hz : orderOf z = 2)
    {L : Subgroup X} (hL : IsSolvableTwoComponentIn L (centralizer {z})) (hzL : z ∈ L)
    (hL2 : GH74.GLS.oPrimeResidualOf 2 L ≤ pCore 2 X) : GH74.GLS.oPrimeResidualOf 2 L ≤ P := by
  have hQ2 : IsPGroup 2 (pCore 2 X) := pCore_isPGroup
  have hP2 : IsPGroup 2 P := hQ2.to_le hPQ
  have hzc : ∀ l ∈ L, l * z = z * l := fun l hl => mem_centralizer_singleton_iff.mp (hL.1 hl)
  have hz2 : z ^ 2 = 1 := by rw [← hz, pow_orderOf_eq_one]
  have hTn : ∀ k ∈ L, ∀ t ∈ L ⊓ P, k * t * k⁻¹ ∈ L ⊓ P := fun k hk t ht =>
    mem_inf.mpr ⟨mul_mem (mul_mem hk (mem_inf.mp ht).1) (inv_mem hk),
      hPn.conj_mem t (mem_inf.mp ht).2 k⟩
  rcases central_or_le_of_normal_two hL inf_le_left hTn
      (fun t ht => exists_pow_eq_one_of_isPGroup hP2 (mem_inf.mp ht).2) with hc | hc
  · exfalso
    have hodd : ∀ ν ∈ L, Odd (orderOf ν) →
        ν ∈ centralizer (GH74.GLS.oPrimeResidualOf 2 L : Set X) := by
      intro ν hνL hν
      have hνC : ν ∈ centralizer ({z} : Set X) := hL.1 hνL
      have hU2 : IsPGroup 2 ↥(P ⊓ centralizer ({z} : Set X)) := hP2.to_le inf_le_left
      have hCU : centralizer ({z} : Set X) ≤
          normalizer ((P ⊓ centralizer ({z} : Set X) : Subgroup X) : Set X) := fun c hc' =>
        mem_normalizer_inf (mem_normalizer_of_normal hPn c) (le_normalizer hc')
      have hab := commutator_le_of_isSubnormal hL.1 hL.2.1 inf_le_right hCU hU2 hνL hν
      have h1 : ∀ u ∈ P ⊓ centralizer ({z} : Set X), ν * u = u * ν :=
        centralizes_of_centralizes_commutator hU2 hν (hCU hνC) fun w hw =>
          hc w (mem_inf.mpr ⟨(mem_inf.mp (hab hw)).1, (mem_inf.mp (mem_inf.mp (hab hw)).2).1⟩)
            ν hνL
      have h3 := centralizes_pCore_of_centralizes_fixed hPQ hPn hPcen hz2 hν (hzc ν hνL)
        fun u hu huz => h1 u (mem_inf.mpr ⟨hu, mem_centralizer_singleton_iff.mpr huz⟩)
      rw [mem_centralizer_iff]
      intro y hy
      exact (h3 y (hL2 hy)).symm
    have hLc := F3L221.le_of_forall_odd hL hodd
    obtain ⟨a, ha, b, hb, hab⟩ := exists_commutator_eq hL hzL hz hzc hL2
      fun u hu => exists_pow_eq_one_of_isPGroup hQ2 hu
    have h1 : b * a = a * b := mem_centralizer_iff.mp (hLc (map_subtype_le _ ha)) b hb
    have h2 : z = 1 := by
      rw [← hab, ← h1]
      group
    rw [h2, orderOf_one] at hz
    exact absurd hz (by norm_num)
  · exact hc.trans inf_le_right

theorem mem_commutator_of_le {P : Subgroup X} (hP2 : IsPGroup 2 P) {z : X} (hz : orderOf z = 2)
    {L : Subgroup X} (hL : IsSolvableTwoComponentIn L (centralizer {z})) (hzL : z ∈ L)
    (hLP : GH74.GLS.oPrimeResidualOf 2 L ≤ P) : z ∈ ⁅P, P⁆ := by
  obtain ⟨a, ha, b, hb, hab⟩ := exists_commutator_eq hL hzL hz
    (fun l hl => mem_centralizer_singleton_iff.mp (hL.1 hl)) hLP
    fun u hu => exists_pow_eq_one_of_isPGroup hP2 hu
  rw [← hab]
  exact commutator_mem_commutator (hLP ha) (hLP hb)

theorem centralizes_of_inf_central {z : X} {M Z : Subgroup X}
    (hM : IsSolvableTwoComponentIn M (centralizer {z})) (hZn : Z.Normal) (hZ2 : IsPGroup 2 Z)
    (hZC : Z ≤ centralizer {z}) (hc : ∀ t ∈ M ⊓ Z, ∀ k ∈ M, t * k = k * t) {ν : X}
    (hνM : ν ∈ M) (hν : Odd (orderOf ν)) : ∀ u ∈ Z, ν * u = u * ν := by
  have hab := commutator_le_of_isSubnormal hM.1 hM.2.1 hZC
    (fun c _ => mem_normalizer_of_normal hZn c) hZ2 hνM hν
  exact centralizes_of_centralizes_commutator hZ2 hν (mem_normalizer_of_normal hZn ν)
    fun w hw => hc w (hab hw) ν hνM

theorem mem_centralizer_commutator_of_le {z : X} {M P : Subgroup X}
    (hM : IsSolvableTwoComponentIn M (centralizer {z})) (hPn : P.Normal) (hP2 : IsPGroup 2 P)
    (hPC : P ≤ centralizer {z}) (hc : GH74.GLS.oPrimeResidualOf 2 M ≤ centralizer (P : Set X))
    {ν : X} (hνM : ν ∈ M) (hν : Odd (orderOf ν)) :
    ν ∈ centralizer ((⁅P, P⁆ : Subgroup X) : Set X) := by
  have hab := commutator_le_of_isSubnormal hM.1 hM.2.1 hPC
    (fun c _ => mem_normalizer_of_normal hPn c) hP2 hνM hν
  have h1 : ⁅P, zpowers ν⁆ ≤ centralizer (P : Set X) := by
    intro w hw
    obtain ⟨hwM, hwP⟩ := mem_inf.mp (hab hw)
    obtain ⟨n, hn⟩ := exists_pow_eq_one_of_isPGroup hP2 hwP
    exact hc (mem_oPrimeResidualOf_of_pow (x := ⟨w, hwM⟩) (m := n)
      (Subtype.ext (by simpa using hn)))
  have h2 : ⁅⁅P, P⁆, zpowers ν⁆ = ⊥ := by
    refine commutator_commutator_eq_bot_of_rotate ?_ ?_
    · rw [commutator_eq_bot_iff_le_centralizer]
      exact h1
    · rw [commutator_comm (zpowers ν) P, commutator_eq_bot_iff_le_centralizer]
      exact h1
  rw [commutator_eq_bot_iff_le_centralizer] at h2
  rw [mem_centralizer_iff]
  intro y hy
  exact (mem_centralizer_iff.mp (h2 hy) ν (mem_zpowers ν)).symm

theorem isSubnormal_of_oPrimeResidualOf_le_pCore {z : X} (hz : orderOf z = 2) {L M : Subgroup X}
    (hL : IsSolvableTwoComponentIn L (centralizer {z})) (hzL : z ∈ L)
    (hM : IsSolvableTwoComponentIn M (centralizer {z}))
    (hL2 : GH74.GLS.oPrimeResidualOf 2 L ≤ pCore 2 X) : M.IsSubnormal := by
  obtain ⟨P, hPQ, hPn, hPc, hPcen⟩ := exists_critical X
  have hP2 : IsPGroup 2 P := (pCore_isPGroup : IsPGroup 2 (pCore 2 X)).to_le hPQ
  have hLP := oPrimeResidualOf_le_of_critical hPQ hPn hPcen hz hL hzL hL2
  have hzPP := mem_commutator_of_le hP2 hz hL hzL hLP
  have hPC : P ≤ centralizer ({z} : Set X) := fun u hu =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hPc hzPP) u hu)
  have := hPn
  have hZn : (P ⊓ centralizer (P : Set X)).Normal := inferInstance
  have hZ2 : IsPGroup 2 ↥(P ⊓ centralizer (P : Set X)) := hP2.to_le inf_le_left
  have hodd : ∀ ν ∈ M, Odd (orderOf ν) → ν ∈ centralizer ((⁅P, P⁆ : Subgroup X) : Set X) := by
    intro ν hνM hν
    have hMn : ∀ k ∈ M, ∀ t ∈ M ⊓ (P ⊓ centralizer (P : Set X)),
        k * t * k⁻¹ ∈ M ⊓ (P ⊓ centralizer (P : Set X)) := fun k hk t ht =>
      mem_inf.mpr ⟨mul_mem (mul_mem hk (mem_inf.mp ht).1) (inv_mem hk),
        hZn.conj_mem t (mem_inf.mp ht).2 k⟩
    rcases central_or_le_of_normal_two hM inf_le_left hMn
        (fun t ht => exists_pow_eq_one_of_isPGroup hZ2 (mem_inf.mp ht).2) with hc | hc
    · have h1 := centralizes_of_inf_central hM hZn hZ2 (inf_le_left.trans hPC) hc hνM hν
      rw [mem_centralizer_iff]
      intro y hy
      exact (h1 y (le_inf (commutator_le_left P P) hPc hy)).symm
    · exact mem_centralizer_commutator_of_le hM hPn hP2 hPC
        (hc.trans (inf_le_right.trans inf_le_right)) hνM hν
  have hMN := F3L221.le_of_forall_odd hM hodd
  have hNC : centralizer ((⁅P, P⁆ : Subgroup X) : Set X) ≤ centralizer ({z} : Set X) := fun g hg =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hg z hzPP).symm
  have hNn : (centralizer ((⁅P, P⁆ : Subgroup X) : Set X)).Normal := inferInstance
  exact Subgroup.IsSubnormal.trans hMN (isSubnormal_subgroupOf_of_le hNC hM.2.1)
    hNn.isSubnormal

end CFSG.ComponentClassification.HarrisLit.T1.F3L226S
