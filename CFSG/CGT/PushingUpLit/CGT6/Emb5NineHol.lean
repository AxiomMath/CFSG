module

public import CFSG.CGT.PushingUpLit.CGT6.EmbEight
public import CFSG.CGT.PushingUpLit.CGT6.Emb5Basic
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.YuBasic
public import CFSG.CGT.PushingUpLit.CGT6E.Emb55Conj

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit CFSG.CGT.PushingUp
open scoped commutatorElement

section Char

variable {V : Type} [CommGroup V]

theorem isCharacteristicP_yuHol (hV : ∀ v : V, v ^ 2 = 1) (H : Subgroup (MulAut V)) :
    IsCharacteristicP 2 ↥(yuHol H) := by
  intro c hc
  rw [pCore_yuHol H hV]
  show yuProj H c ∈ pCore 2 ↥H
  have hcentr : ∀ u : ↥(commV H), (c : Hol V).right (u : V) = (u : V) := by
    intro u
    have h1 : yuInc H u ∈ pCore 2 ↥(yuHol H) := yuInc_range_le_pCore H hV ⟨u, rfl⟩
    have h2 : yuInc H u * c = c * yuInc H u := Subgroup.mem_centralizer_iff.mp hc _ h1
    have h3 := conj_yuInc H c u
    have h4 : c * yuInc H u * c⁻¹ = yuInc H u := by rw [← h2]; group
    rw [h4] at h3
    exact (congrArg Subtype.val (yuInc_injective H h3)).symm
  set U := commV H with hU
  have hq : yuProj H c ∈ (centW U).subgroupOf H := by
    rw [Subgroup.mem_subgroupOf]
    intro w hw
    exact hcentr ⟨w, hw⟩
  have hnorm : ((centW U).subgroupOf H).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    intro w hw
    have hg : ((g⁻¹ : ↥H) : MulAut V) w ∈ U := apply_mem_commV_self H (g⁻¹).2 hw
    have h1 := hn _ hg
    show ((g : MulAut V) * (n : MulAut V) * ((g : MulAut V))⁻¹) w = w
    simp only [MulAut.mul_apply]
    have : ((g : MulAut V))⁻¹ w = ((g⁻¹ : ↥H) : MulAut V) w := rfl
    rw [this, h1]
    exact MulAut.apply_inv_self _ _ _
  have hmem : ∀ q : ↥((centW U).subgroupOf H), (q : MulAut V) ∈ stabGrp U := by
    intro q
    have hq1 : ((q : ↥H) : MulAut V) ∈ centW U := Subgroup.mem_subgroupOf.mp q.2
    exact ⟨hq1, le_trV_commV H (q : ↥H).2⟩
  let f : ↥((centW U).subgroupOf H) →* ↥(stabGrp U) :=
    { toFun := fun q => ⟨((q : ↥H) : MulAut V), hmem q⟩
      map_one' := rfl
      map_mul' := fun a b => rfl }
  have hf : Function.Injective f := fun a b h => by
    have := congrArg (fun z : ↥(stabGrp U) => (z : MulAut V)) h
    exact Subtype.ext (Subtype.ext this)
  have hp2 : IsPGroup 2 ↥((centW U).subgroupOf H) :=
    IsPGroup.of_injective (isPGroup_two_stabGrp hV U) f hf
  have hle : (centW U).subgroupOf H ≤ pCore 2 ↥H := le_sSup ⟨hnorm, hp2⟩
  exact hle hq

end Char

section Sub

variable {V : Type} [CommGroup V]

theorem mul_mul_inv_mem_yuHol {A : Subgroup (MulAut V)} {u : V} {a b : MulAut V} (w : V)
    (hu : u ∈ commV A) (ha : a ∈ A) (hb : b ∈ A) :
    (⟨w, b⟩ * ⟨u, a⟩ * ⟨w, b⟩⁻¹ : Hol V) ∈ yuHol A := by
  have ha' : b * a * b⁻¹ ∈ A := A.mul_mem (A.mul_mem hb ha) (A.inv_mem hb)
  have hbn : ∀ x ∈ A, b * x * b⁻¹ ∈ A := fun x hx =>
    A.mul_mem (A.mul_mem hb hx) (A.inv_mem hb)
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

theorem isSubnormal_yuHol {H B₀ : Subgroup (MulAut V)} (hs : (B₀.subgroupOf H).IsSubnormal) :
    ((yuHol B₀).subgroupOf (yuHol H)).IsSubnormal := by
  have hC : ((B₀.subgroupOf H).comap (yuProj H)).IsSubnormal := hs.comap (yuProj H)
  have hle : (yuHol B₀).subgroupOf (yuHol H) ≤ (B₀.subgroupOf H).comap (yuProj H) := by
    intro a ha
    rw [Subgroup.mem_subgroupOf] at ha
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact ha.2
  refine Subgroup.IsSubnormal.step _ _ hle hC ?_
  rw [Subgroup.normal_subgroupOf_iff hle]
  rintro ⟨⟨u, a⟩, hmem⟩ ⟨⟨w, b⟩, hmem'⟩ ha hc
  rw [Subgroup.mem_subgroupOf] at ha ⊢
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf] at hc
  exact mul_mul_inv_mem_yuHol w ha.1 ha.2 hc

end Sub


section Conj

variable {V : Type} [CommGroup V]

theorem hol_conj_one (x : MulAut V) (u : V) (b : MulAut V) :
    (⟨1, x⟩ * ⟨u, b⟩ * ⟨1, x⟩⁻¹ : Hol V) = ⟨x u, x * b * x⁻¹⟩ := by
  apply SemidirectProduct.ext
  · simp [SemidirectProduct.mul_left, SemidirectProduct.inv_left]
  · simp [SemidirectProduct.mul_right, SemidirectProduct.inv_right]

theorem yuHol_conjSub (x : MulAut V) (B : Subgroup (MulAut V)) :
    yuHol (CGT6E.conjSub x B) =
      (yuHol B).map (MulAut.conj (⟨1, x⟩ : Hol V)).toMonoidHom := by
  ext ⟨u', b'⟩
  constructor
  · rintro ⟨hu, hb⟩
    obtain ⟨b, hbB, rfl⟩ := CGT6E.mem_conjSub.mp hb
    have hu' : x⁻¹ u' ∈ commV B := CGT6E.mem_commV_conjSub.mp hu
    refine ⟨⟨x⁻¹ u', b⟩, ⟨hu', hbB⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hol_conj_one]
    simp
  · rintro ⟨⟨u, b⟩, ⟨hu, hb⟩, he⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at he
    rw [hol_conj_one] at he
    have h1 : x u = u' := congrArg SemidirectProduct.left he
    have h2 : x * b * x⁻¹ = b' := congrArg SemidirectProduct.right he
    refine ⟨?_, ?_⟩
    · rw [CGT6E.mem_commV_conjSub, ← h1]
      simpa using hu
    · rw [← h2]
      exact CGT6E.conj_mem_conjSub hb

variable [Finite V]

theorem inClassX_yuHol_conjSub {B : Subgroup (MulAut V)} (x : MulAut V)
    (h : InClassX ↥(yuHol B)) : InClassX ↥(yuHol (CGT6E.conjSub x B)) := by
  let φ : Hol V →* Hol V := (MulAut.conj (⟨1, x⟩ : Hol V)).toMonoidHom
  have e : ↥(yuHol B) ≃* ↥(yuHol (CGT6E.conjSub x B)) :=
    (Subgroup.equivMapOfInjective _ φ (MulAut.conj _).injective).trans
      (MulEquiv.subgroupCongr (yuHol_conjSub x B).symm)
  exact InClassX.of_mulEquiv e h

omit [Finite V] in
theorem map_conj_eq_self_of_mem' {H : Subgroup (MulAut V)} {x : MulAut V} (hx : x ∈ H) :
    H.map (MulAut.conj x).toMonoidHom = H := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)
  · intro hz
    refine ⟨x⁻¹ * z * x, H.mul_mem (H.mul_mem (H.inv_mem hx) hz) hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem trivial_of_conj_ne (hV : ∀ v : V, v ^ 2 = 1) {H B : Subgroup (MulAut V)} (hBH : B ≤ H)
    (hs : (B.subgroupOf H).IsSubnormal) (hc : InClassX ↥(yuHol B)) {x : MulAut V} (hx : x ∈ H)
    (hne : CGT6E.conjSub x B ≠ B) :
    (∀ b' ∈ CGT6E.conjSub x B, ∀ e ∈ commV B, b' e = e) ∧
      (∀ b ∈ B, ∀ e ∈ commV (CGT6E.conjSub x B), b e = e) := by
  have hB'H : CGT6E.conjSub x B ≤ H := by
    rintro _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact H.mul_mem (H.mul_mem hx (hBH hb)) (H.inv_mem hx)
  have hs' : ((CGT6E.conjSub x B).subgroupOf H).IsSubnormal := by
    have h1 := isSubnormal_map_conj x hs
    rw [map_conj_eq_self_of_mem' hx] at h1
    exact h1
  have hK : IsCharacteristicP 2 ↥(yuHol H) := isCharacteristicP_yuHol hV H
  have hX₁ : IsBlockOfInX (yuHol H) (yuHol B) := ⟨yuHol_mono hBH, isSubnormal_yuHol hs, hc⟩
  have hX₂ : IsBlockOfInX (yuHol H) (yuHol (CGT6E.conjSub x B)) :=
    ⟨yuHol_mono hB'H, isSubnormal_yuHol hs', inClassX_yuHol_conjSub x hc⟩
  have hne' : yuHol B ≠ yuHol (CGT6E.conjSub x B) := fun h => hne (yuHol_inj h).symm
  have hcomm := distinct_blocks_commute_of_isBlockOfInX hK hX₁ hX₂ hne'
  have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  refine ⟨fun b' hb' e he => ?_, fun b hb e he => ?_⟩
  · have h1 : (⟨e, 1⟩ : Hol V) ∈ yuHol B := ⟨he, one_mem _⟩
    have h2 : (⟨1, b'⟩ : Hol V) ∈ yuHol (CGT6E.conjSub x B) := ⟨one_mem _, hb'⟩
    have h3 := Subgroup.mem_centralizer_iff.mp (hle h1) _ h2
    have h4 := congrArg SemidirectProduct.left h3
    simpa [SemidirectProduct.mul_left] using h4
  · have h1 : (⟨1, b⟩ : Hol V) ∈ yuHol B := ⟨one_mem _, hb⟩
    have h2 : (⟨e, 1⟩ : Hol V) ∈ yuHol (CGT6E.conjSub x B) := ⟨he, one_mem _⟩
    have h3 := Subgroup.mem_centralizer_iff.mp (hle h1) _ h2
    have h4 := congrArg SemidirectProduct.left h3
    simpa [SemidirectProduct.mul_left] using h4.symm

end Conj

end CFSG.CGT.PushingUpLit.CGT6
