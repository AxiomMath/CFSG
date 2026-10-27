module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7
public import CFSG.ClassicalInvolution.Asc77.AscT7CHyp
public import CFSG.ClassicalInvolution.Asc77.AscT7TStar2
public import CFSG.ClassicalInvolution.Q3.Q3CLBasic

public section

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected

section Standing

structure Hyp25A7 {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K K' W : Subgroup G)
    (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G) : Prop
    extends Hyp25Data Ω K K' W S R R' z t u₁ u₂ where
  std : Hyp23A7 Ω K K' z

@[expose] def A7C25_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25A7 Ω K K' W S R R' z t u₁ u₂ → ∀ A : Subgroup G, z ∈ A → A ≤ (S : Subgroup G) →
      (∀ s ∈ (S : Subgroup G), conjSub s A = A) →
      (∀ a ∈ A, a ≠ 1 → z ∈ zStarOf (Subgroup.centralizer ({a} : Set G))) → A = Subgroup.zpowers z

@[expose] def A7C25_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25A7 Ω K K' W S R R' z t u₁ u₂ → ∀ a : G, a * a = 1 → a ≠ 1 →
      a ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) →
        z ∈ zStarOf (Subgroup.centralizer ({a} : Set G))

@[expose] def A7C25_11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25A7 Ω K K' W S R R' z t u₁ u₂ →
      (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) =
        Subgroup.zpowers z

@[expose] def A7C25_16 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25A7 Ω K K' W S R R' z t u₁ u₂ → ∀ a ∈ (S : Subgroup G), ¬ IsFAut R' a

end Standing

section Conj

variable {G : Type} [Group G]

theorem conjSub_le_of_mem {S X : Subgroup G} {s : G} (hs : s ∈ S) (hX : X ≤ S) :
    conjSub s X ≤ S := by
  intro x hx
  have h1 : s⁻¹ * x * s ∈ X := mem_conjSub_iff.mp hx
  have h2 := S.mul_mem (S.mul_mem hs (hX h1)) (S.inv_mem hs)
  have e : s * (s⁻¹ * x * s) * s⁻¹ = x := by group
  rwa [e] at h2

end Conj

section Elementary

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}

theorem Hyp25A7.hΩ (h : Hyp25A7 Ω K K' W S R R' z t u₁ u₂) : AschTight.HypOmegaGen Ω :=
  h.std.1.stand.hyp

theorem Hyp25A7.hK (h : Hyp25A7 Ω K K' W S R R' z t u₁ u₂) : K ∈ Ω :=
  h.std.1.stand.mem

theorem Hyp25A7.hK' (h : Hyp25A7 Ω K K' W S R R' z t u₁ u₂) : K' ∈ Ω :=
  h.std.1.hK'.1

theorem Hyp25A7.hRsyl (h : Hyp25A7 Ω K K' W S R R' z t u₁ u₂) : IsSylow2In R K :=
  AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le h.hΩ h.hK h.hR.1 h.hR.2.1

theorem Hyp25A7.hzR (h : Hyp25A7 Ω K K' W S R R' z t u₁ u₂) : z ∈ R :=
  AschTight.Sec6Gen.mem_of_isSylow2In h.std.1.hz h.hRsyl

theorem Hyp25A7.ne (h : Hyp25A7 Ω K K' W S R R' z t u₁ u₂) : R ≠ R' := by
  intro e
  have h1 := AschTight.Sec6Gen.card_le_two_of_le_inf h.hΩ h.hK h.hK' h.std.1.hne.symm
    h.hRsyl.2.1 h.hRsyl.1 (e ▸ h.hR'.2.1)
  have h2 := (AschTight.Sec6Gen.isQuatSub_of_mem_RSet h.hΩ h.hR.1).eight_le
  omega

theorem Hyp25A7.conj_R (h : Hyp25A7 Ω K K' W S R R' z t u₁ u₂) {s : G}
    (hs : s ∈ (S : Subgroup G)) :
    (conjSub s R = R ∧ conjSub s R' = R') ∨ (conjSub s R = R' ∧ conjSub s R' = R) := by
  have hR := Q3.Q3CL.Thompson.conjSub_mem_RSet h.hΩ h.hR.1 s
  have hR' := Q3.Q3CL.Thompson.conjSub_mem_RSet h.hΩ h.hR'.1 s
  have hRle : conjSub s R ≤ (S : Subgroup G) := conjSub_le_of_mem hs h.hR.2.2
  have hR'le : conjSub s R' ≤ (S : Subgroup G) := conjSub_le_of_mem hs h.hR'.2.2
  have hne : conjSub s R ≠ conjSub s R' := fun e => h.ne (conjSub_injective s e)
  rcases h.hRS _ hR hRle with h1 | h1 <;> rcases h.hRS _ hR' hR'le with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (h1.trans h2.symm) hne

theorem Hyp25A7.conj_sup (h : Hyp25A7 Ω K K' W S R R' z t u₁ u₂) {s : G}
    (hs : s ∈ (S : Subgroup G)) : conjSub s (R ⊔ R') = R ⊔ R' := by
  have e : conjSub s (R ⊔ R') = conjSub s R ⊔ conjSub s R' := Subgroup.map_sup _ _ _
  rw [e]
  rcases h.conj_R hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, sup_comm]

end Elementary

section Eleven

theorem a7C25_11_of_5_6 (h5 : A7C25_5) (h6 : A7C25_6) : A7C25_11 := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp
  set A : Subgroup G := (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G)
    with hAdef
  have hzS : z ∈ (S : Subgroup G) := hyp.hR.2.2 hyp.hzR
  have hzA : z ∈ A := by
    refine Subgroup.mem_inf.mpr ⟨hzS, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyS : y ∈ (S : Subgroup G) := by
      have : R ⊔ R' ≤ (S : Subgroup G) := sup_le hyp.hR.2.2 hyp.hR'.2.2
      exact this hy
    exact hyp.hzS y hyS
  have hnorm : ∀ s ∈ (S : Subgroup G), conjSub s A = A := by
    have key : ∀ s ∈ (S : Subgroup G), ∀ x ∈ A, s * x * s⁻¹ ∈ A := by
      intro s hs x hx
      have hx1 := Subgroup.mem_inf.mp hx
      refine Subgroup.mem_inf.mpr ⟨(S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem hs hx1.1)
        ((S : Subgroup G).inv_mem hs), ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy' : s⁻¹ * y * s ∈ R ⊔ R' := by
        have h1 := conj_mem_conjSub (n := s⁻¹) hy
        rw [hyp.conj_sup ((S : Subgroup G).inv_mem hs), inv_inv] at h1
        exact h1
      have hxc := (Subgroup.mem_centralizer_iff.mp hx1.2) _ hy'
      calc y * (s * x * s⁻¹) = s * ((s⁻¹ * y * s) * x) * s⁻¹ := by group
        _ = s * (x * (s⁻¹ * y * s)) * s⁻¹ := by rw [hxc]
        _ = (s * x * s⁻¹) * y := by group
    intro s hs
    apply le_antisymm
    · intro x hx
      have h1 : s⁻¹ * x * s ∈ A := mem_conjSub_iff.mp hx
      have h2 := key s hs _ h1
      have e : s * (s⁻¹ * x * s) * s⁻¹ = x := by group
      rwa [e] at h2
    · intro x hx
      have h1 := key s⁻¹ ((S : Subgroup G).inv_mem hs) x hx
      rw [inv_inv] at h1
      exact mem_conjSub_iff.mpr h1
  have hZ : ∀ a ∈ A, a ≠ 1 → z ∈ zStarOf (Subgroup.centralizer ({a} : Set G)) := by
    intro a ha ha1
    have haS : a ∈ (S : Subgroup G) := ha.1
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp S.isPGroup') ⟨a, haS⟩
    have hk' : orderOf a = 2 ^ k := by rw [← hk]; simp [← Subgroup.orderOf_coe]
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact ha1 (orderOf_eq_one_iff.mp (by simpa using hk'))
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    set i : G := a ^ (2 ^ j) with hi
    have hiA : i ∈ A := A.pow_mem ha _
    have hdvd : 2 ^ j ∣ orderOf a := by rw [hk']; exact pow_dvd_pow 2 (Nat.le_succ j)
    have hio : orderOf i = 2 := by
      rw [hi, orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) hdvd, hk', pow_succ,
        Nat.mul_div_cancel_left _ (pow_pos two_pos j)]
    have hi2 : i * i = 1 := by
      have := pow_orderOf_eq_one i
      rwa [hio, pow_two] at this
    have hi1 : i ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hio
      omega
    have h := h6 G Ω K K' W S R R' z t u₁ u₂ hyp i hi2 hi1 hiA
    refine T7T.mem_zStarOf_of_le ?_ h ?_
    · intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
      exact ((Commute.pow_right (show Commute y a from hy) (2 ^ j)).eq)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hyp.hzS a haS).symm
  exact h5 G Ω K K' W S R R' z t u₁ u₂ hyp A hzA inf_le_left hnorm hZ

end Eleven

end CFSG.ClassicalInvolution.Hat2A7S
