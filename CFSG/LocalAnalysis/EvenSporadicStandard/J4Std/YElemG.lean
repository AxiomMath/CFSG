module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.YLift
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.Interface

public section

namespace CFSG.EvenSporadicStandard.J4Std.YElem

open Subgroup

variable {G : Type} [Group G]

class IsAbelianSub (Y : Subgroup G) : Prop where
  comm : ∀ y ∈ Y, ∀ y' ∈ Y, y * y' = y' * y

instance commGroupOfAbelian (Y : Subgroup G) [h : IsAbelianSub Y] : CommGroup Y :=
  { (inferInstance : Group Y) with mul_comm := fun a b => Subtype.ext (h.comm _ a.2 _ b.2) }

theorem ebasis_eq_coe_prod (Y : Subgroup G) [IsAbelianSub Y] (e : Fin 11 → G) (he : ∀ i, e i ∈ Y)
    (c : Fin 11 → ZMod 2) :
    ebasis e c = ((∏ i, (⟨e i, he i⟩ : Y) ^ (c i).val : Y) : G) := by
  rw [← List.prod_ofFn]
  have h2 := map_list_prod Y.subtype (List.ofFn fun i => (⟨e i, he i⟩ : Y) ^ (c i).val)
  rw [List.map_ofFn] at h2
  exact h2.symm

theorem false_of_abelian_subgroup [Finite G] (Y U : Subgroup G) [IsAbelianSub Y] (hUY : U ≤ Y)
    (φ : G → G) (hφmul : ∀ y ∈ Y, ∀ y' ∈ Y, φ (y * y') = φ y * φ y')
    (hφU : ∀ y ∈ Y, φ y ∈ U) (hφone : ∀ u ∈ U, φ u = 1)
    (hφker : ∀ y ∈ Y, φ y = 1 → y ∈ U) (hφsurj : ∀ u ∈ U, ∃ y ∈ Y, φ y = u)
    (hU2 : ∀ u ∈ U, u * u = 1) (hsq : ∀ y ∈ Y, y * y ∈ U)
    (hΩ : ∀ y ∈ Y, y * y = 1 → y ∈ U) (hcard : Nat.card U = 2 ^ 11)
    (e : Fin 11 → G) (heU : ∀ i, e i ∈ U)
    (hinj : ∀ c d : Fin 11 → ZMod 2, ebasis e c = ebasis e d → c = d)
    (s t : G) (hsY : ∀ y ∈ Y, s * y * s⁻¹ ∈ Y) (htY : ∀ y ∈ Y, t * y * t⁻¹ ∈ Y)
    (hss : s * s = 1) (htt : t * t = 1) (hst : (s * t) * (s * t) = 1)
    (hφs : ∀ y ∈ Y, φ (s * y * s⁻¹) = s * φ y * s⁻¹)
    (hφt : ∀ y ∈ Y, φ (t * y * t⁻¹) = t * φ y * t⁻¹)
    (hse : ∀ i, s * e i * s⁻¹ = ebasis e (fun j => Smat i j))
    (hte : ∀ i, t * e i * t⁻¹ = ebasis e (fun j => Tmat i j)) : False := by
  let φ' : Y →* Y :=
    { toFun := fun y => ⟨φ y, hUY (hφU y y.2)⟩
      map_one' := Subtype.ext (hφone 1 U.one_mem)
      map_mul' := fun a b => Subtype.ext (hφmul a a.2 b b.2) }
  let σ : Y →* Y :=
    { toFun := fun y => ⟨s * y * s⁻¹, hsY y y.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  let τ : Y →* Y :=
    { toFun := fun y => ⟨t * y * t⁻¹, htY y y.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  let eY : Fin 11 → Y := fun i => ⟨e i, hUY (heU i)⟩
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hLS : LiftSetting (U.subgroupOf Y) φ' eY :=
    { φ_mem := fun y => mem_subgroupOf.2 (hφU y y.2)
      φ_one := fun u hu => Subtype.ext (hφone u (mem_subgroupOf.1 hu))
      ker_le := fun y hy => mem_subgroupOf.2 (hφker y y.2 (congrArg Subtype.val hy))
      surj := fun u hu => by
        obtain ⟨y, hyY, hy⟩ := hφsurj u (mem_subgroupOf.1 hu)
        exact ⟨⟨y, hyY⟩, Subtype.ext hy⟩
      U_sq := fun u hu => Subtype.ext (hU2 u (mem_subgroupOf.1 hu))
      sq_mem := fun y => mem_subgroupOf.2 (hsq y y.2)
      sq_eq_one := fun y hy => mem_subgroupOf.2 (hΩ y y.2 (congrArg Subtype.val hy))
      card_U := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUY).toEquiv, hcard]
      e_mem := fun i => mem_subgroupOf.2 (heU i)
      e_inj := fun c d hcd => hinj c d (by
        rw [ebasis_eq_coe_prod Y e (fun i => hUY (heU i)) c,
          ebasis_eq_coe_prod Y e (fun i => hUY (heU i)) d]
        exact congrArg Subtype.val hcd) }
  refine hLS.false_of_involutions σ τ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro y
    refine Subtype.ext ?_
    show s * (s * y * s⁻¹) * s⁻¹ = y
    rw [hsi]
    calc s * (s * y * s) * s = (s * s) * y * (s * s) := by simp only [mul_assoc]
      _ = y := by rw [hss, one_mul, mul_one]
  · intro y
    refine Subtype.ext ?_
    show t * (t * y * t⁻¹) * t⁻¹ = y
    rw [hti]
    calc t * (t * y * t) * t = (t * t) * y * (t * t) := by simp only [mul_assoc]
      _ = y := by rw [htt, one_mul, mul_one]
  · intro y
    refine Subtype.ext ?_
    show s * (t * (s * (t * y * t⁻¹) * s⁻¹) * t⁻¹) * s⁻¹ = y
    have h4 : s * t * s * t = 1 := by simpa only [mul_assoc] using hst
    calc s * (t * (s * (t * y * t⁻¹) * s⁻¹) * t⁻¹) * s⁻¹
        = (s * t * s * t) * y * (t⁻¹ * s⁻¹ * t⁻¹ * s⁻¹) := by simp only [mul_assoc]
      _ = y := by
        have : t⁻¹ * s⁻¹ * t⁻¹ * s⁻¹ = (s * t * s * t)⁻¹ := by
          simp only [mul_inv_rev, mul_assoc]
        rw [this, h4, inv_one, one_mul, mul_one]
  · intro y
    exact Subtype.ext (hφs y y.2)
  · intro y
    exact Subtype.ext (hφt y y.2)
  · intro i
    refine Subtype.ext ?_
    show s * e i * s⁻¹ = _
    rw [hse i, ebasis_eq_coe_prod Y e (fun i => hUY (heU i))]
  · intro i
    refine Subtype.ext ?_
    show t * e i * t⁻¹ = _
    rw [hte i, ebasis_eq_coe_prod Y e (fun i => hUY (heU i))]

end CFSG.EvenSporadicStandard.J4Std.YElem
