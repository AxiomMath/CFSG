module

public import CFSG.CGT.PushingUpLit.CGT6.Embedding
public import CFSG.CGT.PushingUpLit.CGT6.SixTwoType
public import CFSG.Quasithin.Background.D2Fitting

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.Quasithin
open scoped commutatorElement

section HolFacts

variable {V : Type} [CommGroup V]

theorem yuHol_mono {A B : Subgroup (MulAut V)} (h : A ≤ B) : yuHol A ≤ yuHol B :=
  fun _ hx => ⟨commV_mono h hx.1, h hx.2⟩

theorem yuHol_inj {A B : Subgroup (MulAut V)} (h : yuHol A = yuHol B) : A = B := by
  refine le_antisymm (fun a ha => ?_) (fun a ha => ?_)
  · have : (⟨1, a⟩ : Hol V) ∈ yuHol A := ⟨one_mem _, ha⟩
    rw [h] at this
    exact this.2
  · have : (⟨1, a⟩ : Hol V) ∈ yuHol B := ⟨one_mem _, ha⟩
    rw [← h] at this
    exact this.2

theorem yuHol_normal {A B : Subgroup (MulAut V)} (hAB : A ≤ B) (hn : (A.subgroupOf B).Normal) :
    ((yuHol A).subgroupOf (yuHol B)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (yuHol_mono hAB)]
  rintro ⟨u, a⟩ ⟨w, b⟩ ⟨hu, ha⟩ ⟨_, hb⟩
  have ha' : b * a * b⁻¹ ∈ A := (Subgroup.normal_subgroupOf_iff hAB).mp hn a b ha hb
  have hbn : ∀ x ∈ A, b * x * b⁻¹ ∈ A := fun x hx =>
    (Subgroup.normal_subgroupOf_iff hAB).mp hn x b hx hb
  refine ⟨?_, ?_⟩
  · have h1 : b u ∈ commV A := G6.apply_mem_commV hbn hu
    have h2 : (b * a * b⁻¹) w * w⁻¹ ∈ commV A := G6.mem_commV_of_mem ha' w
    have e : (⟨w, b⟩ * ⟨u, a⟩ * ⟨w, b⟩⁻¹ : Hol V).left =
        b u * ((b * a * b⁻¹) w * w⁻¹)⁻¹ := by
      simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
        SemidirectProduct.inv_left, MonoidHom.id_apply,
        MulAut.mul_apply, map_inv, map_mul, MulAut.inv_apply, inv_inv, mul_inv_rev]
      rw [mul_comm w (b u), mul_assoc]
    rw [e]
    exact mul_mem h1 (inv_mem h2)
  · have : (⟨w, b⟩ * ⟨u, a⟩ * ⟨w, b⟩⁻¹ : Hol V).right = b * a * b⁻¹ := by
      simp [SemidirectProduct.mul_right, SemidirectProduct.inv_right]
    show (⟨w, b⟩ * ⟨u, a⟩ * ⟨w, b⟩⁻¹ : Hol V).right ∈ A
    rw [this]
    exact ha'

theorem isPGroup_of_yuHol_le_oTwoIn [Finite V] {A B : Subgroup (MulAut V)}
    (h : yuHol A ≤ oTwoIn (yuHol B)) : IsPGroup 2 ↥A := by
  have h2 : IsPGroup 2 ↥(yuHol A) :=
    (IsPGroup.map (pCore_isPGroup (p := 2) (G := ↥(yuHol B))) (yuHol B).subtype).to_le h
  intro a
  obtain ⟨k, hk⟩ := h2 ⟨⟨1, (a : MulAut V)⟩, ⟨one_mem _, a.2⟩⟩
  refine ⟨k, Subtype.ext ?_⟩
  have h3 : SemidirectProduct.rightHom
      ((⟨⟨1, (a : MulAut V)⟩, ⟨one_mem _, a.2⟩⟩ : ↥(yuHol A)) ^ 2 ^ k : ↥(yuHol A)).1 = 1 := by
    rw [hk]
    rfl
  rw [Subgroup.coe_pow, map_pow] at h3
  exact h3

theorem not_le_oTwoIn_yuHol [Finite V] {A B : Subgroup (MulAut V)} (hA : ¬ IsPGroup 2 ↥A) :
    ¬ yuHol A ≤ oTwoIn (yuHol B) := fun h => hA (isPGroup_of_yuHol_le_oTwoIn h)

theorem eq_of_inClassX_yuHol [Finite V] {A B : Subgroup (MulAut V)} (hAB : A ≤ B)
    (hn : (A.subgroupOf B).Normal) (hB : InClassX ↥(yuHol B)) (hA : ¬ IsPGroup 2 ↥A) : A = B :=
  yuHol_inj (inClassX_eq_of_normal_not_le hB (yuHol_mono hAB) (yuHol_normal hAB hn)
    (not_le_oTwoIn_yuHol hA))

end HolFacts

end CFSG.CGT.PushingUpLit.CGT6
