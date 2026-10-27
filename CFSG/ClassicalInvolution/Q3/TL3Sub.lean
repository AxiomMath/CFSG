module

public import CFSG.ClassicalInvolution.Q3.TL3Act

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution
open scoped commutatorElement Pointwise

theorem isSubnormal_threeElement_join {G : Type*} [Group G] [Finite G] {R C : Subgroup G}
    (hRC : R ≤ C) (hCR : C ≤ Subgroup.normalizer (R : Set G))
    (eQ : (R ⧸ oddCore R) ≃* QuaternionGroup 2)
    {x : G} (hxC : x ∈ C) {k : ℕ} (hx3 : x ^ 3 ^ k = 1)
    (hxR : ∃ r ∈ R, ⁅x, r⁆ ∉ oddCoreImg R)
    (hxD : ∀ y ∈ C, (∀ r ∈ R, ⁅y, r⁆ ∈ oddCoreImg R) → ⁅x, y⁆ ∈ oddCoreImg C) :
    IsSubnormal (R ⊔ Subgroup.zpowers x ⊔ oddCoreImg C) C := by
  classical
  set O : Subgroup G := oddCoreImg C with hO
  set J : Subgroup G := R ⊔ Subgroup.zpowers x ⊔ O with hJ
  have hOC : O ≤ C := oddCoreImg_le C
  have hRJ : R ≤ J := le_sup_left.trans le_sup_left
  have hXJ : Subgroup.zpowers x ≤ J := le_sup_right.trans le_sup_left
  have hOJ : O ≤ J := le_sup_right
  have hxJ : x ∈ J := hXJ (Subgroup.mem_zpowers x)
  have hJC : J ≤ C := sup_le (sup_le hRC (Subgroup.zpowers_le.mpr hxC)) hOC
  have hconjO : ∀ g ∈ C, ∀ o ∈ O, g * o * g⁻¹ ∈ O := fun g hg o ho =>
    conj_mem_oddCoreImg (Subgroup.le_normalizer hg) ho
  have hconjR : ∀ g ∈ C, ∀ r ∈ R, g * r * g⁻¹ ∈ R := fun g hg r hr =>
    (Subgroup.mem_normalizer_iff.mp (hCR hg) r).mp hr
  let ρ : C →* MulAut (R ⧸ oddCore R) := (tl3Act R).comp (Subgroup.inclusion hCR)
  have hρ1 : ∀ (y : G) (hy : y ∈ C),
      ρ ⟨y, hy⟩ = 1 ↔ ∀ r ∈ R, ⁅y, r⁆ ∈ oddCoreImg R := fun y hy =>
    tl3Act_eq_one_iff R ⟨y, hCR hy⟩
  have hρR : ∀ r : R, ρ ⟨(r : G), hRC r.2⟩ = MulAut.conj (r : R ⧸ oddCore R) := fun r =>
    tl3Act_of_mem R r
  set D : Subgroup G := (ρ.ker).map C.subtype with hD
  have hDmem : ∀ y : G, y ∈ D ↔ ∃ hy : y ∈ C, ∀ r ∈ R, ⁅y, r⁆ ∈ oddCoreImg R := by
    intro y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.2, (hρ1 z z.2).mp (MonoidHom.mem_ker.mp hz)⟩
    · rintro ⟨hy, h⟩
      exact ⟨⟨y, hy⟩, MonoidHom.mem_ker.mpr ((hρ1 y hy).mpr h), rfl⟩
  have hDC : D ≤ C := by
    rintro y hy
    exact ((hDmem y).mp hy).1
  set P : MulAut (R ⧸ oddCore R) := ρ ⟨x, hxC⟩ with hP
  have hPk : P ^ 3 ^ k = 1 := by
    rw [hP, ← map_pow]
    have : (⟨x, hxC⟩ : C) ^ 3 ^ k = 1 := Subtype.ext (by simpa using hx3)
    rw [this, map_one]
  have hP1 : P ≠ 1 := by
    intro h
    obtain ⟨r, hr, hnr⟩ := hxR
    exact hnr ((hρ1 x hxC).mp h r hr)
  have hBn := tl3_inn_sup_zpowers_normal eQ hPk hP1
  have hInnN := tl3_inn_normal (M := R ⧸ oddCore R)
  set Inn := (MulAut.conj : (R ⧸ oddCore R) →* MulAut (R ⧸ oddCore R)).range with hInn
  set Z := Subgroup.zpowers P with hZ
  have hconjx : ∀ c ∈ C, c * x * c⁻¹ ∈ J ⊔ D := by
    intro c hc
    have hcxC : c * x * c⁻¹ ∈ C := C.mul_mem (C.mul_mem hc hxC) (C.inv_mem hc)
    have hρcx : ρ ⟨c * x * c⁻¹, hcxC⟩ = ρ ⟨c, hc⟩ * P * (ρ ⟨c, hc⟩)⁻¹ := by
      rw [hP, ← map_inv, ← map_mul, ← map_mul]
      rfl
    have hPB : P ∈ Inn ⊔ Z := Subgroup.mem_sup_right (Subgroup.mem_zpowers P)
    have hmem := hBn.conj_mem P hPB (ρ ⟨c, hc⟩)
    have hmem' : ρ ⟨c * x * c⁻¹, hcxC⟩ ∈ (Inn : Set (MulAut (R ⧸ oddCore R))) *
        (Z : Set (MulAut (R ⧸ oddCore R))) := by
      rw [← Subgroup.normal_mul, hρcx]
      exact hmem
    obtain ⟨ι, hι, p, hp, hιp⟩ := hmem'
    obtain ⟨m, rfl⟩ := hι
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective m
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
    set y : G := ((r : G) * x ^ i)⁻¹ * (c * x * c⁻¹) with hy
    have hyC : y ∈ C := C.mul_mem (C.inv_mem (C.mul_mem (hRC r.2) (C.zpow_mem hxC i)))
      hcxC
    have hρy : ρ ⟨y, hyC⟩ = 1 := by
      have e1 : (⟨y, hyC⟩ : C) =
          (⟨(r : G), hRC r.2⟩ * ⟨x, hxC⟩ ^ i)⁻¹ * ⟨c * x * c⁻¹, hcxC⟩ :=
        Subtype.ext (by simp [hy])
      rw [e1, map_mul, map_inv, map_mul, map_zpow, hρR r, ← hιp]
      exact inv_mul_cancel _
    have hyD : y ∈ D := (hDmem y).mpr ⟨hyC, (hρ1 y hyC).mp hρy⟩
    have : c * x * c⁻¹ = ((r : G) * x ^ i) * y := by rw [hy]; group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left (hRJ r.2))
      (Subgroup.mem_sup_left (hXJ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) i))))
      (Subgroup.mem_sup_right hyD)
  have hdJ : ∀ d ∈ D, ∀ h ∈ J, d * h * d⁻¹ ∈ J := by
    intro d hd
    obtain ⟨hdC, hdc⟩ := (hDmem d).mp hd
    have hle : J ≤ J.comap (MulAut.conj d).toMonoidHom := by
      refine sup_le (sup_le ?_ ?_) ?_
      · intro r hr
        show d * r * d⁻¹ ∈ J
        have h1 : d * r * d⁻¹ = ⁅d, r⁆ * r := by rw [commutatorElement_def]; group
        rw [h1]
        exact J.mul_mem (hRJ (oddCoreImg_le R (hdc r hr))) (hRJ hr)
      · refine Subgroup.zpowers_le.mpr ?_
        show d * x * d⁻¹ ∈ J
        have h1 : d * x * d⁻¹ = (⁅x, d⁆)⁻¹ * x := by
          rw [commutatorElement_inv, commutatorElement_def]; group
        rw [h1]
        exact J.mul_mem (J.inv_mem (hOJ (hxD d hdC hdc))) hxJ
      · intro o ho
        exact hOJ (hconjO d hdC o ho)
    exact fun h hh => hle hh
  have hJnorm : J ⊔ D ≤ Subgroup.normalizer (J : Set G) := by
    refine sup_le Subgroup.le_normalizer ?_
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hdJ d hd h hh, fun hh => ?_⟩
    have := hdJ d⁻¹ (D.inv_mem hd) _ hh
    simpa [mul_assoc] using this
  have hconjN : ∀ c ∈ C, ∀ n ∈ J ⊔ D, c * n * c⁻¹ ∈ J ⊔ D := by
    intro c hc
    have hle : J ⊔ D ≤ (J ⊔ D).comap (MulAut.conj c).toMonoidHom := by
      refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
      · intro r hr
        exact Subgroup.mem_sup_left (hRJ (hconjR c hc r hr))
      · refine Subgroup.zpowers_le.mpr ?_
        exact hconjx c hc
      · intro o ho
        exact Subgroup.mem_sup_left (hOJ (hconjO c hc o ho))
      · intro d hd
        obtain ⟨hdC, hdc⟩ := (hDmem d).mp hd
        have hcdC : c * d * c⁻¹ ∈ C := C.mul_mem (C.mul_mem hc hdC) (C.inv_mem hc)
        refine Subgroup.mem_sup_right ((hDmem _).mpr ⟨hcdC, ?_⟩)
        have h1 : ρ ⟨d, hdC⟩ = 1 := (hρ1 d hdC).mpr hdc
        have h2 : ρ ⟨c * d * c⁻¹, C.mul_mem (C.mul_mem hc hdC) (C.inv_mem hc)⟩ = 1 := by
          have : (⟨c * d * c⁻¹, C.mul_mem (C.mul_mem hc hdC) (C.inv_mem hc)⟩ : C) =
              ⟨c, hc⟩ * ⟨d, hdC⟩ * ⟨c, hc⟩⁻¹ := rfl
          rw [this, map_mul, map_mul, h1, mul_one, map_inv, mul_inv_cancel]
        exact (hρ1 _ _).mp h2
    exact fun n hn => hle hn
  have hCnorm : C ≤ Subgroup.normalizer ((J ⊔ D : Subgroup G) : Set G) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨fun hn => hconjN c hc n hn, fun hn => ?_⟩
    have := hconjN c⁻¹ (C.inv_mem hc) _ hn
    simpa [mul_assoc] using this
  have hNC : J ⊔ D ≤ C := sup_le hJC hDC
  exact IsSubnormal.step le_sup_left
    ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hJnorm)
    (IsSubnormal.step hNC ((Subgroup.normal_subgroupOf_iff_le_normalizer hNC).mpr hCnorm)
      (IsSubnormal.refl C))

end CFSG.ClassicalInvolution.Q3
