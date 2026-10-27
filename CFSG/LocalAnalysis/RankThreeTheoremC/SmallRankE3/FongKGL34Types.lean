module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherGraphFieldInvolution

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

theorem kgl34_card_filter_pow_two_pow_le {B : Type*} [Group B] [Fintype B] [DecidableEq B]
    (hcomm : ∀ a b : B, a * b = b * a)
    (h1 : (Finset.univ.filter fun x : B => x ^ 2 = 1).card ≤ 2) (j : ℕ) :
    (Finset.univ.filter fun x : B => x ^ 2 ^ j = 1).card ≤ 2 ^ j := by
  induction j with
  | zero =>
    rw [pow_zero]
    refine le_of_eq ?_
    rw [Finset.card_eq_one]
    exact ⟨1, by ext x; simp⟩
  | succ j ih =>
    set T := Finset.univ.filter fun x : B => x ^ 2 ^ (j + 1) = 1
    have himg : T.image (fun x => x ^ 2) ⊆ Finset.univ.filter fun x : B => x ^ 2 ^ j = 1 := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [← pow_mul, ← pow_succ']
      exact hx
    have hfib : ∀ y ∈ T.image (fun x => x ^ 2), (T.filter fun x => x ^ 2 = y).card ≤ 2 := by
      intro y hy
      obtain ⟨x₀, -, rfl⟩ := Finset.mem_image.mp hy
      refine le_trans ?_ h1
      refine Finset.card_le_card_of_injOn (fun x => x * x₀⁻¹) ?_ ?_
      · intro x hx
        simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ, true_and] at hx ⊢
        rw [Commute.mul_pow (hcomm x x₀⁻¹), hx.2, inv_pow, mul_inv_cancel]
      · intro x _ y _ hxy
        simpa using hxy
    calc T.card ≤ 2 * (T.image fun x => x ^ 2).card := Finset.card_le_mul_card_image T 2 hfib
      _ ≤ 2 * 2 ^ j := Nat.mul_le_mul_left 2 ((Finset.card_le_card himg).trans ih)
      _ = 2 ^ (j + 1) := by rw [pow_succ, mul_comm]

theorem kgl34_isCyclic_of_card_sq_eq_one_le {B : Type*} [Group B] [Finite B] (hB : IsPGroup 2 B)
    (hcomm : ∀ a b : B, a * b = b * a) (h1 : Nat.card {x : B // x ^ 2 = 1} ≤ 2) :
    IsCyclic B := by
  classical
  have : Fintype B := Fintype.ofFinite B
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h1
  refine isCyclic_of_card_pow_eq_one_le fun n hn => ?_
  have hsub : (Finset.univ.filter fun x : B => x ^ n = 1) ⊆
      Finset.univ.filter fun x : B => x ^ 2 ^ n.factorization 2 = 1 := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨k, hk⟩ := hB x
    have hord : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
    have hn' : 2 ^ i ∣ n := hi ▸ orderOf_dvd_of_pow_eq_one hx
    have hle : i ≤ n.factorization 2 :=
      (Nat.prime_two.pow_dvd_iff_le_factorization hn.ne').mp hn'
    rw [← orderOf_dvd_iff_pow_eq_one, hi]
    exact Nat.pow_dvd_pow 2 hle
  calc (Finset.univ.filter fun x : B => x ^ n = 1).card
      ≤ (Finset.univ.filter fun x : B => x ^ 2 ^ n.factorization 2 = 1).card :=
        Finset.card_le_card hsub
    _ ≤ 2 ^ n.factorization 2 := kgl34_card_filter_pow_two_pow_le hcomm h1 _
    _ ≤ n := Nat.le_of_dvd hn (Nat.ordProj_dvd n 2)

theorem exists_two_involutions_of_noncyclic {G : Type*} [Group G] [Finite G] {S : Subgroup G}
    (hS : IsPGroup 2 ↥S) (hcomm : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s) (hnc : ¬ IsCyclic ↥S) :
    ∃ a ∈ S, ∃ b ∈ S, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a * a = 1 ∧ b * b = 1 := by
  classical
  by_contra hno
  have hno' : ∀ x y : S, x * x = 1 → y * y = 1 → x ≠ 1 → y ≠ 1 → x = y := by
    intro x y hxx hyy hx1 hy1
    by_contra hxy
    exact hno ⟨(x : G), x.2, (y : G), y.2, fun h => hx1 (Subtype.ext h),
      fun h => hy1 (Subtype.ext h), fun h => hxy (Subtype.ext h),
      congrArg Subtype.val hxx, congrArg Subtype.val hyy⟩
  apply hnc
  refine kgl34_isCyclic_of_card_sq_eq_one_le hS (fun x y => Subtype.ext (hcomm _ x.2 _ y.2)) ?_
  calc Nat.card {x : S // x ^ 2 = 1} ≤ Nat.card Bool := by
        refine Nat.card_le_card_of_injective (fun x => decide ((x : S) = 1)) ?_
        intro x y hxy
        by_cases hx : (x : S) = 1
        · have hy : (y : S) = 1 := by
            by_contra hy
            simp [hx, hy] at hxy
          exact Subtype.ext (hx.trans hy.symm)
        · have hy : (y : S) ≠ 1 := by
            intro hy
            simp [hx, hy] at hxy
          have hx2 := x.2
          have hy2 := y.2
          rw [pow_two] at hx2 hy2
          exact Subtype.ext (hno' _ _ hx2 hy2 hx hy)
    _ = 2 := by simp

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem pigeon3 {α : Type*} (P Q R : α → Prop) (x y z : α) (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) (hP : ∀ u v, P u → P v → u = v) (hQ : ∀ u v, Q u → Q v → u = v)
    (hR : ∀ u v, R u → R v → u = v)
    (hx : P x ∨ Q x ∨ R x) (hy : P y ∨ Q y ∨ R y) (hz : P z ∨ Q z ∨ R z) :
    (∃ u, P u) ∧ (∃ u, Q u) := by
  constructor
  · by_contra h
    push Not at h
    have hx' : Q x ∨ R x := hx.resolve_left (h x)
    have hy' : Q y ∨ R y := hy.resolve_left (h y)
    have hz' : Q z ∨ R z := hz.resolve_left (h z)
    rcases hx' with hx' | hx' <;> rcases hy' with hy' | hy' <;> rcases hz' with hz' | hz'
    · exact hxy (hQ x y hx' hy')
    · exact hxy (hQ x y hx' hy')
    · exact hxz (hQ x z hx' hz')
    · exact hyz (hR y z hy' hz')
    · exact hyz (hQ y z hy' hz')
    · exact hxz (hR x z hx' hz')
    · exact hxy (hR x y hx' hy')
    · exact hxy (hR x y hx' hy')
  · by_contra h
    push Not at h
    have hx' : P x ∨ R x := by
      rcases hx with hx | hx | hx
      · exact Or.inl hx
      · exact absurd hx (h x)
      · exact Or.inr hx
    have hy' : P y ∨ R y := by
      rcases hy with hy | hy | hy
      · exact Or.inl hy
      · exact absurd hy (h y)
      · exact Or.inr hy
    have hz' : P z ∨ R z := by
      rcases hz with hz | hz | hz
      · exact Or.inl hz
      · exact absurd hz (h z)
      · exact Or.inr hz
    rcases hx' with hx' | hx' <;> rcases hy' with hy' | hy' <;> rcases hz' with hz' | hz'
    · exact hxy (hP x y hx' hy')
    · exact hxy (hP x y hx' hy')
    · exact hxz (hP x z hx' hz')
    · exact hyz (hR y z hy' hz')
    · exact hyz (hP y z hy' hz')
    · exact hxz (hR x z hx' hz')
    · exact hxy (hR x y hx' hy')
    · exact hxy (hR x y hx' hy')

section Types

variable {n f : ℕ} {F : Type*} [Field F] [Finite F]

@[expose] def IsFieldType (ι : MulAut (projectiveSL n F)) : Prop :=
  ∃ (A : GL (Fin n) F) (σ : F ≃+* F), σ ≠ 1 ∧ ι = conjAut n F A * fieldAut n F σ

@[expose] def IsGraphType (ι : MulAut (projectiveSL n F)) : Prop :=
  ∃ A : GL (Fin n) F, ι = conjAut n F A * dualAut n F

@[expose] def IsGraphFieldType (ι : MulAut (projectiveSL n F)) : Prop :=
  ∃ (A : GL (Fin n) F) (σ : F ≃+* F), σ ≠ 1 ∧ ι = conjAut n F A * fieldAut n F σ * dualAut n F

theorem sigma_sq_of_field (hn : 3 ≤ n) {A : GL (Fin n) F} {σ : F ≃+* F}
    (h : (conjAut n F A * fieldAut n F σ) * (conjAut n F A * fieldAut n F σ) = 1) :
    σ * σ = 1 := by
  rw [conjAut_mul_fieldAut_mul] at h
  exact (eq_one_of_conjAut_mul_fieldAut_eq_one hn _ _ h).1

theorem sigma_sq_of_graphField (hn : 3 ≤ n) {A : GL (Fin n) F} {σ : F ≃+* F}
    (h : (conjAut n F A * fieldAut n F σ * dualAut n F) *
      (conjAut n F A * fieldAut n F σ * dualAut n F) = 1) : σ * σ = 1 := by
  rw [← pow_two, sq_conjAut_fieldAut_dualAut] at h
  exact (eq_one_of_conjAut_mul_fieldAut_eq_one hn _ _ h).1

theorem sigma_eq_of_sq_eq_one (hF : Nat.card F = 2 ^ f) (hf : 1 ≤ f) {σ τ : F ≃+* F}
    (hσ : σ ≠ 1) (hτ : τ ≠ 1) (hσσ : σ * σ = 1) (hττ : τ * τ = 1) : σ = τ := by
  obtain ⟨-, h1⟩ := even_and_eq_pow_of_involution hf hF hσ hσσ
  obtain ⟨-, h2⟩ := even_and_eq_pow_of_involution hf hF hτ hττ
  ext x
  rw [h1, h2]

theorem eq_of_mul_inv_mem {G : Type*} [Group G] {S D : Subgroup G} (hSD : S ⊓ D = ⊥) {a b : G}
    (ha : a ∈ S) (hb : b ∈ S) (h : a * b⁻¹ ∈ D) : a = b := by
  have h1 : a * b⁻¹ ∈ S ⊓ D := ⟨S.mul_mem ha (S.inv_mem hb), h⟩
  rw [hSD, Subgroup.mem_bot, mul_inv_eq_one] at h1
  exact h1

theorem eq_of_isFieldType (hn : 3 ≤ n) (hF : Nat.card F = 2 ^ f) (hf : 1 ≤ f)
    {S : Subgroup (MulAut (projectiveSL n F))} (hSD : S ⊓ linearAutGroup n F = ⊥)
    {ι ι' : MulAut (projectiveSL n F)} (hι : ι ∈ S) (hι' : ι' ∈ S) (h1 : ι * ι = 1)
    (h1' : ι' * ι' = 1) (hT : IsFieldType ι) (hT' : IsFieldType ι') : ι = ι' := by
  obtain ⟨A, σ, hσ, rfl⟩ := hT
  obtain ⟨B, τ, hτ, rfl⟩ := hT'
  have hστ : σ = τ :=
    sigma_eq_of_sq_eq_one hF hf hσ hτ (sigma_sq_of_field hn h1) (sigma_sq_of_field hn h1')
  subst hστ
  refine eq_of_mul_inv_mem hSD hι hι' ?_
  have : conjAut n F A * fieldAut n F σ * (conjAut n F B * fieldAut n F σ)⁻¹ =
      conjAut n F (A * B⁻¹) := by
    rw [map_mul, map_inv]; group
  rw [this]
  exact conjAut_mem_linearAutGroup _

theorem eq_of_isGraphType {S : Subgroup (MulAut (projectiveSL n F))}
    (hSD : S ⊓ linearAutGroup n F = ⊥) {ι ι' : MulAut (projectiveSL n F)} (hι : ι ∈ S)
    (hι' : ι' ∈ S) (hT : IsGraphType ι) (hT' : IsGraphType ι') : ι = ι' := by
  obtain ⟨A, rfl⟩ := hT
  obtain ⟨B, rfl⟩ := hT'
  refine eq_of_mul_inv_mem hSD hι hι' ?_
  have : conjAut n F A * dualAut n F * (conjAut n F B * dualAut n F)⁻¹ = conjAut n F (A * B⁻¹) := by
    rw [map_mul, map_inv]; group
  rw [this]
  exact conjAut_mem_linearAutGroup _

theorem eq_of_isGraphFieldType (hn : 3 ≤ n) (hF : Nat.card F = 2 ^ f) (hf : 1 ≤ f)
    {S : Subgroup (MulAut (projectiveSL n F))} (hSD : S ⊓ linearAutGroup n F = ⊥)
    {ι ι' : MulAut (projectiveSL n F)} (hι : ι ∈ S) (hι' : ι' ∈ S) (h1 : ι * ι = 1)
    (h1' : ι' * ι' = 1) (hT : IsGraphFieldType ι) (hT' : IsGraphFieldType ι') : ι = ι' := by
  obtain ⟨A, σ, hσ, rfl⟩ := hT
  obtain ⟨B, τ, hτ, rfl⟩ := hT'
  have hστ : σ = τ :=
    sigma_eq_of_sq_eq_one hF hf hσ hτ (sigma_sq_of_graphField hn h1) (sigma_sq_of_graphField hn h1')
  subst hστ
  refine eq_of_mul_inv_mem hSD hι hι' ?_
  have : conjAut n F A * fieldAut n F σ * dualAut n F *
      (conjAut n F B * fieldAut n F σ * dualAut n F)⁻¹ = conjAut n F (A * B⁻¹) := by
    rw [map_mul, map_inv]; group
  rw [this]
  exact conjAut_mem_linearAutGroup _

theorem involution_type (hn : 3 ≤ n) {S : Subgroup (MulAut (projectiveSL n F))}
    (hSD : S ⊓ linearAutGroup n F = ⊥) {ι : MulAut (projectiveSL n F)} (hι : ι ∈ S)
    (h1 : ι ≠ 1) : IsFieldType ι ∨ IsGraphType ι ∨ IsGraphFieldType ι := by
  obtain ⟨A, σ, ε, hε, rfl⟩ := (automorphism_generation (K := F) hn).2 ι
  interval_cases ε
  · by_cases hσ : σ = 1
    · exfalso
      subst hσ
      apply h1
      have hD : conjAut n F A * fieldAut n F 1 * dualAut n F ^ 0 ∈ linearAutGroup n F := by
        simp only [map_one, mul_one, pow_zero]
        exact conjAut_mem_linearAutGroup A
      have hmem : conjAut n F A * fieldAut n F 1 * dualAut n F ^ 0 ∈ S ⊓ linearAutGroup n F :=
        ⟨hι, hD⟩
      rw [hSD, Subgroup.mem_bot] at hmem
      exact hmem
    · left
      exact ⟨A, σ, hσ, by simp⟩
  · by_cases hσ : σ = 1
    · right; left
      subst hσ
      exact ⟨A, by simp⟩
    · right; right
      exact ⟨A, σ, hσ, by simp⟩

theorem exists_field_and_graph_involution (hn : 3 ≤ n) (hF : Nat.card F = 2 ^ f) (hf : 1 ≤ f)
    {S : Subgroup (MulAut (projectiveSL n F))} (hSD : S ⊓ linearAutGroup n F = ⊥)
    (hcomm : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s)
    {a b : MulAut (projectiveSL n F)} (ha : a ∈ S) (hb : b ∈ S) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hab : a ≠ b) (haa : a * a = 1) (hbb : b * b = 1) :
    (∃ ι ∈ S, ι ≠ 1 ∧ ι * ι = 1 ∧ IsFieldType ι) ∧
      (∃ ι ∈ S, ι ≠ 1 ∧ ι * ι = 1 ∧ IsGraphType ι) := by
  have hcS : a * b ∈ S := S.mul_mem ha hb
  have hba : a * b = b * a := hcomm a ha b hb
  have hcc : (a * b) * (a * b) = 1 := by
    calc (a * b) * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← hba]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [haa, hbb, one_mul]
  have hc1 : a * b ≠ 1 := by
    intro h
    apply hab
    have : a = b⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this, inv_eq_of_mul_eq_one_left hbb]
  have hac : a ≠ a * b := by
    intro h
    apply hb1
    have := mul_left_cancel (a := a) (h.symm.trans (mul_one a).symm)
    exact this
  have hbc : b ≠ a * b := by
    intro h
    apply ha1
    have h' : 1 * b = a * b := by rw [one_mul]; exact h
    exact (mul_right_cancel h').symm
  let P : MulAut (projectiveSL n F) → Prop :=
    fun ι => ι ∈ S ∧ ι ≠ 1 ∧ ι * ι = 1 ∧ IsFieldType ι
  let Q : MulAut (projectiveSL n F) → Prop :=
    fun ι => ι ∈ S ∧ ι ≠ 1 ∧ ι * ι = 1 ∧ IsGraphType ι
  let R : MulAut (projectiveSL n F) → Prop :=
    fun ι => ι ∈ S ∧ ι ≠ 1 ∧ ι * ι = 1 ∧ IsGraphFieldType ι
  have hP : ∀ u v, P u → P v → u = v := fun u v hu hv =>
    eq_of_isFieldType hn hF hf hSD hu.1 hv.1 hu.2.2.1 hv.2.2.1 hu.2.2.2 hv.2.2.2
  have hQ : ∀ u v, Q u → Q v → u = v := fun u v hu hv =>
    eq_of_isGraphType hSD hu.1 hv.1 hu.2.2.2 hv.2.2.2
  have hR : ∀ u v, R u → R v → u = v := fun u v hu hv =>
    eq_of_isGraphFieldType hn hF hf hSD hu.1 hv.1 hu.2.2.1 hv.2.2.1 hu.2.2.2 hv.2.2.2
  have hcls : ∀ ι, ι ∈ S → ι ≠ 1 → ι * ι = 1 → P ι ∨ Q ι ∨ R ι := by
    intro ι hι h1 h2
    rcases involution_type hn hSD hι h1 with h | h | h
    · exact Or.inl ⟨hι, h1, h2, h⟩
    · exact Or.inr (Or.inl ⟨hι, h1, h2, h⟩)
    · exact Or.inr (Or.inr ⟨hι, h1, h2, h⟩)
  obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := pigeon3 P Q R a b (a * b) hab hac hbc hP hQ hR
    (hcls a ha ha1 haa) (hcls b hb hb1 hbb) (hcls _ hcS hc1 hcc)
  exact ⟨⟨u, hu.1, hu.2.1, hu.2.2.1, hu.2.2.2⟩, ⟨v, hv.1, hv.2.1, hv.2.2.1, hv.2.2.2⟩⟩

end Types

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
