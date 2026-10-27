module

public import CFSG.ClassicalInvolution.Asc77.AscSPN10

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Asc77 CFSG.LieType.Universal
open SemidirectProduct

abbrev Holo (X : Type) [Group X] : Type := X ⋊[MonoidHom.id (MulAut X)] MulAut X

section Holo

variable {X : Type} [Group X]

theorem holo_inr_mul_inl (g : MulAut X) (q : X) :
    (inr g : Holo X) * inl q = inl (g q) * inr g := by
  have h := SemidirectProduct.inl_aut (φ := MonoidHom.id (MulAut X)) g q
  simp only [MonoidHom.id_apply, map_inv] at h
  exact (eq_mul_inv_iff_mul_eq.mp h).symm

theorem holo_inr_mul_inl_mul_inv (g : MulAut X) (q : X) :
    (inr g : Holo X) * inl q * (inr g)⁻¹ = inl (g q) :=
  mul_inv_eq_iff_eq_mul.mpr (holo_inr_mul_inl g q)

instance holo_finite [Finite X] : Finite (Holo X) := by
  have : Finite (MulAut X) :=
    Finite.of_injective (fun f : MulAut X => (f : X → X)) fun f g h => MulEquiv.ext (congrFun h)
  exact Finite.of_injective (fun a : Holo X => (a.left, a.right)) fun a b h =>
    SemidirectProduct.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

theorem sq_trichotomy_of_spinGenOn {t : StatedLieTag} {M : LieUniversal}
    (hSG : SPN.SpinGenOn t M) [Finite X] (ψ : M.K →* X) (hψ : Function.Surjective ψ)
    {R R' : Subgroup M.K} {x x' : M.K} (hP : TwinPairOn t M ψ R R' x x') (α : MulAut X)
    (hα4 : α * α * (α * α) = 1) (hαR : ∀ r ∈ R, α (ψ r) = ψ r)
    (hαR' : ∀ r ∈ R', α (ψ r) = ψ r) :
    α * α = 1 ∨ α * α = MulAut.conj (ψ x) ∨
      Subgroup.closure ({q | (α * α) q = q} ∪ {q | ψ x * q = q * ψ x}) = ⊤ := by
  classical
  set β : MulAut X := α * α with hβ
  have hι : Function.Injective (inl : X →* Holo X) := SemidirectProduct.inl_injective
  have hrange : ((inl : X →* Holo X).comp ψ).range = (inl : X →* Holo X).range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hψ, ← MonoidHom.range_eq_map]
  have hnormal : (inl : X →* Holo X).range.Normal := by
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    infer_instance
  have hs : (inr β : Holo X) ∈
      Subgroup.normalizer (((inl : X →* Holo X).comp ψ).range : Set (Holo X)) := by
    rw [hrange]
    have := hnormal
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top _
  have hss : (inr β : Holo X) * inr β = 1 := by
    rw [← map_mul, hα4, map_one]
  have hβR : ∀ q : X, α q = q → β q = q := fun q hq => by
    show α (α q) = q
    rw [hq, hq]
  have hcR : ∀ r ∈ R, (inr β : Holo X) * ((inl : X →* Holo X).comp ψ) r =
      ((inl : X →* Holo X).comp ψ) r * inr β := fun r hr => by
    show (inr β : Holo X) * inl (ψ r) = inl (ψ r) * inr β
    rw [holo_inr_mul_inl, hβR _ (hαR r hr)]
  have hcR' : ∀ r ∈ R', (inr β : Holo X) * ((inl : X →* Holo X).comp ψ) r =
      ((inl : X →* Holo X).comp ψ) r * inr β := fun r hr => by
    show (inr β : Holo X) * inl (ψ r) = inl (ψ r) * inr β
    rw [holo_inr_mul_inl, hβR _ (hαR' r hr)]
  have hP' : TwinPairOn t M ((inl : X →* Holo X).comp ψ) R R' x x' :=
    { ker := fun a ha => hP.ker (MonoidHom.mem_ker.mpr
        (hι ((MonoidHom.mem_ker.mp ha).trans (map_one (inl : X →* Holo X)).symm)))
      mem := hP.mem
      mem' := hP.mem'
      ne := hP.ne
      comm := hP.comm
      hx := hP.hx
      hx2 := hP.hx2
      hx1 := hP.hx1
      hx' := hP.hx'
      hx'2 := hP.hx'2
      hx'1 := hP.hx'1
      same := congrArg (inl : X →* Holo X) hP.same }
  have hfix : ∀ q : X, (inr β : Holo X) * inl q = inl q * inr β → β q = q := fun q h => by
    rw [holo_inr_mul_inl] at h
    exact hι (mul_right_cancel h)
  have hcen : ∀ q : X, (inl (ψ x) : Holo X) * inl q = inl q * inl (ψ x) →
      ψ x * q = q * ψ x := fun q h => by
    rw [← map_mul, ← map_mul] at h
    exact hι h
  rcases hSG (Holo X) ((inl : X →* Holo X).comp ψ) R R' x x' hP' (inr β) hs hss hcR hcR' with
    h1 | h2 | h3
  · left
    ext q
    obtain ⟨a, rfl⟩ := hψ q
    exact hfix _ (h1 (inl (ψ a)) ⟨a, rfl⟩)
  · right
    left
    ext q
    obtain ⟨a, rfl⟩ := hψ q
    have h := h2 (inl (ψ a)) ⟨a, rfl⟩
    rw [holo_inr_mul_inl_mul_inv] at h
    have h' : (inl (β (ψ a)) : Holo X) = inl (ψ x * ψ a * (ψ x)⁻¹) := by
      rw [h]
      simp
    rw [MulAut.conj_apply]
    exact hι h'
  · right
    right
    rw [Subgroup.eq_top_iff']
    have hsub : Subgroup.closure ({w | w ∈ ((inl : X →* Holo X).comp ψ).range ∧
        (inr β : Holo X) * w = w * inr β} ∪
        {w | w ∈ ((inl : X →* Holo X).comp ψ).range ∧
          ((inl : X →* Holo X).comp ψ) x * w = w * ((inl : X →* Holo X).comp ψ) x}) ≤
        (Subgroup.closure ({q | β q = q} ∪ {q | ψ x * q = q * ψ x})).map
          (inl : X →* Holo X) := by
      rw [Subgroup.closure_le]
      rintro w (⟨hw, hc⟩ | ⟨hw, hc⟩)
      · rw [hrange] at hw
        obtain ⟨q, rfl⟩ := hw
        exact Subgroup.mem_map_of_mem _ (Subgroup.subset_closure (Or.inl (hfix q hc)))
      · rw [hrange] at hw
        obtain ⟨q, rfl⟩ := hw
        exact Subgroup.mem_map_of_mem _ (Subgroup.subset_closure (Or.inr (hcen q hc)))
    intro q
    obtain ⟨a, rfl⟩ := hψ q
    obtain ⟨q₀, hq₀, hq₀e⟩ := hsub (h3 (inl (ψ a)) ⟨a, rfl⟩)
    rwa [← hι hq₀e]

theorem le_of_closure_aut {G : Type} [Group G] [Finite G] (Y : Subgroup G) {X : Type} [Group X]
    (π : ↥Y →* X) (hπ : Function.Surjective π) (hodd : Odd (Nat.card π.ker)) {c₁ c₂ : G}
    (hc₁ : c₁ ∈ Subgroup.normalizer (Y : Set G)) (hc₂ : c₂ ∈ Subgroup.normalizer (Y : Set G))
    (hc₁2 : c₁ * c₁ = 1) (hc₂2 : c₂ * c₂ = 1) (α₁ α₂ : MulAut X)
    (hα₁ : ∀ y : ↥Y, π (SPN.conjOn Y c₁ hc₁ y) = α₁ (π y))
    (hα₂ : ∀ y : ↥Y, π (SPN.conjOn Y c₂ hc₂ y) = α₂ (π y)) (S : Subgroup G)
    (hS₁ : ∀ y : ↥Y, c₁ * (y : G) = (y : G) * c₁ → (y : G) ∈ S)
    (hS₂ : ∀ y : ↥Y, c₂ * (y : G) = (y : G) * c₂ → (y : G) ∈ S)
    (hker : ∀ n : ↥Y, n ∈ π.ker → (n : G) ∈ S)
    (hgen : Subgroup.closure ({q | α₁ q = q} ∪ {q | α₂ q = q}) = (⊤ : Subgroup X)) : Y ≤ S := by
  classical
  have hι : Function.Injective (inl : X →* Holo X) := SemidirectProduct.inl_injective
  have hker' : ((inl : X →* Holo X).comp π).ker = π.ker := by
    ext n
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    exact ⟨fun h => hι (h.trans (map_one (inl : X →* Holo X)).symm), fun h => by
      show (inl : X →* Holo X) (π n) = 1
      rw [h, map_one]⟩
  have hodd' : Odd (Nat.card ((inl : X →* Holo X).comp π).ker) := by
    rw [hker']
    exact hodd
  have hfix : ∀ (α : MulAut X) (q : X), (inr α : Holo X) * inl q = inl q * inr α → α q = q :=
    fun α q h => by
      rw [holo_inr_mul_inl] at h
      exact hι (mul_right_cancel h)
  have hlift : ∀ (c : G) (hc : c ∈ Subgroup.normalizer (Y : Set G)) (hc2 : c * c = 1)
      (α : MulAut X), (∀ y : ↥Y, π (SPN.conjOn Y c hc y) = α (π y)) →
      ∀ q ∈ ((inl : X →* Holo X).comp π).range, (inr α : Holo X) * q = q * inr α →
        ∃ y : ↥Y, ((inl : X →* Holo X).comp π) y = q ∧ c * (y : G) = (y : G) * c :=
    fun c hc hc2 α hα q hqr hq => by
      obtain ⟨y₀, rfl⟩ := hqr
      refine SPN.exists_fixed_lift Y ((inl : X →* Holo X).comp π) hodd' c hc hc2 (inr α)
        (fun y => ?_) ⟨y₀, rfl⟩ (mul_inv_eq_iff_eq_mul.mpr hq)
      show (inl (π (SPN.conjOn Y c hc y)) : Holo X) = inr α * inl (π y) * (inr α)⁻¹
      rw [hα, holo_inr_mul_inl_mul_inv]
  refine SPN.le_of_closure Y ((inl : X →* Holo X).comp π) S (inr α₁) (inr α₂) ?_ ?_ ?_ ?_
  · intro q hqr hq
    obtain ⟨y, hy, hyc⟩ := hlift c₁ hc₁ hc₁2 α₁ hα₁ q hqr hq
    exact ⟨y, hy, hS₁ y hyc⟩
  · intro q hqr hq
    obtain ⟨y, hy, hyc⟩ := hlift c₂ hc₂ hc₂2 α₂ hα₂ q hqr hq
    exact ⟨y, hy, hS₂ y hyc⟩
  · intro n hn
    exact hker n (hker' ▸ hn)
  · intro q hq
    obtain ⟨y₀, rfl⟩ := hq
    have hmem : ∀ q' : X, q' ∈ Subgroup.closure ({q | α₁ q = q} ∪ {q | α₂ q = q}) →
        (inl q' : Holo X) ∈ Subgroup.closure
          ({w | w ∈ ((inl : X →* Holo X).comp π).range ∧ (inr α₁ : Holo X) * w = w * inr α₁} ∪
            {w | w ∈ ((inl : X →* Holo X).comp π).range ∧
              (inr α₂ : Holo X) * w = w * inr α₂}) := by
      intro q' hq'
      have hle : Subgroup.closure ({q | α₁ q = q} ∪ {q | α₂ q = q}) ≤
          (Subgroup.closure
            ({w | w ∈ ((inl : X →* Holo X).comp π).range ∧
                (inr α₁ : Holo X) * w = w * inr α₁} ∪
              {w | w ∈ ((inl : X →* Holo X).comp π).range ∧
                (inr α₂ : Holo X) * w = w * inr α₂})).comap (inl : X →* Holo X) := by
        rw [Subgroup.closure_le]
        rintro q'' (hq'' | hq'')
        · obtain ⟨y, rfl⟩ := hπ q''
          exact Subgroup.subset_closure (Or.inl ⟨⟨y, rfl⟩, by
            rw [holo_inr_mul_inl, hq'']⟩)
        · obtain ⟨y, rfl⟩ := hπ q''
          exact Subgroup.subset_closure (Or.inr ⟨⟨y, rfl⟩, by
            rw [holo_inr_mul_inl, hq'']⟩)
      exact hle hq'
    exact hmem (π y₀) (by rw [hgen]; exact Subgroup.mem_top _)

end Holo

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
