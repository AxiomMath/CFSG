module

public import CFSG.LieType.Chevalley.C2E6FieldExtensionStar
public import CFSG.LieType.Chevalley.C2E6FourthResidueOrder

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std.FieldExtension

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

open CFSG.LieType.Chevalley.CosetBuilding
open scoped Pointwise

theorem apply_apply_of_mem_betaGroup
    (b : betaGroup) (x : stdGroup) :
    (b : MulAut stdGroup) ((b : MulAut stdGroup) x) = x := by
  rcases mem_betaGroup_iff.mp b.2 with h | h <;> rw [h]
  · rfl
  · exact betaG_betaG x

theorem apply_mem_nativeParabolic_iff
    (b : betaGroup) (J : Set (Fin 4)) (x : stdGroup) :
    (((b : MulAut stdGroup) x : stdGroup) : ModGL Tag.E6 K) ∈ nativeParabolic J ↔
      (x : ModGL Tag.E6 K) ∈ nativeParabolic J := by
  rcases mem_betaGroup_iff.mp b.2 with h | h <;> rw [h]
  · rfl
  · exact ⟨fun hx => betaGL_betaGL (x : ModGL Tag.E6 K) ▸ betaGL_mem_nativeParabolic hx,
      betaGL_mem_nativeParabolic⟩

abbrev baseResidue
    (J : Set (Fin 4)) : Set stdChamber :=
  residue nativeCoxeterSystem stdDistance J ((1 : stdGroup) : stdChamber)

theorem mem_baseResidue_iff
    (J : Set (Fin 4)) (g : stdGroup) :
    (g : stdChamber) ∈ baseResidue J ↔ (g : ModGL Tag.E6 K) ∈ nativeParabolic J := by
  change (g : stdChamber) ∈ residue nativeCoxeterSystem stdDistance J ((1 : stdGroup) :
    stdChamber) ↔ _
  rw [residue_stdDistance, one_smul]
  constructor
  · rintro ⟨x, hx, e⟩
    have hxg : x⁻¹ * g ∈ stdBorelG := QuotientGroup.eq.mp e
    have hg : (g : ModGL Tag.E6 K) = x * ((x⁻¹ * g : stdGroup) : ModGL Tag.E6 K) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
    rw [hg]
    exact mul_mem hx (stdBorel_le_nativeParabolic J hxg)
  · intro hg
    exact ⟨g, hg, rfl⟩

theorem image_smul_baseResidue_iff
    (γ : GStar) (J : Set (Fin 4)) :
    (γ • ·) '' baseResidue J = baseResidue J ↔ (γ.left : ModGL Tag.E6 K) ∈ nativeParabolic J := by
  constructor
  · intro h
    have h1 : γ • ((1 : stdGroup) : stdChamber) ∈ baseResidue J := by
      rw [← h]
      exact ⟨_, (mem_baseResidue_iff J 1).2 (one_mem _), rfl⟩
    rwa [smul_mk, map_one, mul_one, mem_baseResidue_iff] at h1
  · intro hγ
    ext q
    induction q using QuotientGroup.induction_on with | H y => ?_
    constructor
    · rintro ⟨q', hq', e⟩
      induction q' using QuotientGroup.induction_on with | H x => ?_
      dsimp only at e
      rw [← e, smul_mk, mem_baseResidue_iff, Subgroup.coe_mul]
      exact mul_mem hγ ((apply_mem_nativeParabolic_iff _ J _).2
        ((mem_baseResidue_iff J x).1 hq'))
    · intro hy
      refine ⟨(((γ.right : MulAut stdGroup) (γ.left⁻¹ * y) : stdGroup) : stdChamber), ?_, ?_⟩
      · rw [mem_baseResidue_iff, apply_mem_nativeParabolic_iff, Subgroup.coe_mul,
          Subgroup.coe_inv]
        exact mul_mem (inv_mem hγ) ((mem_baseResidue_iff J y).1 hy)
      · dsimp only
        rw [smul_mk, apply_apply_of_mem_betaGroup, mul_inv_cancel_left]

@[expose] def parStar
    (J : Set (Fin 4)) : Subgroup GStar where
  carrier := {γ | (γ.left : ModGL Tag.E6 K) ∈ nativeParabolic J}
  mul_mem' {γ γ'} hγ hγ' := by
    change (((γ * γ').left : stdGroup) : ModGL Tag.E6 K) ∈ nativeParabolic J
    rw [SemidirectProduct.mul_left, Subgroup.coe_mul]
    exact mul_mem hγ ((apply_mem_nativeParabolic_iff γ.right J _).2 hγ')
  one_mem' := one_mem (nativeParabolic J)
  inv_mem' {γ} hγ := by
    change ((γ⁻¹.left : stdGroup) : ModGL Tag.E6 K) ∈ nativeParabolic J
    rw [SemidirectProduct.inv_left]
    exact (apply_mem_nativeParabolic_iff γ.right⁻¹ J _).2 (by
      rw [Subgroup.coe_inv]
      exact inv_mem hγ)

theorem mem_parStar
    {J : Set (Fin 4)} {γ : GStar} :
    γ ∈ parStar J ↔ (γ.left : ModGL Tag.E6 K) ∈ nativeParabolic J :=
  Iff.rfl

abbrev parLeft
    {J : Set (Fin 4)} (γ : parStar J) : nativeParabolic J :=
  ⟨γ.1.left, mem_parStar.mp γ.2⟩

@[expose] def parMap
    {J : Set (Fin 4)} (γ : parStar J) (p : nativeParabolic J) :
    nativeParabolic J :=
  ⟨((γ.1.left * (γ.1.right : MulAut stdGroup) ⟨p, nativeParabolic_le_stdGroup J p.2⟩ :
      stdGroup) : ModGL Tag.E6 K),
    mul_mem γ.2 ((apply_mem_nativeParabolic_iff _ J _).2 p.2)⟩

theorem coe_parMap
    {J : Set (Fin 4)} (γ : parStar J) (p : nativeParabolic J) :
    (parMap γ p : ModGL Tag.E6 K) = ((γ.1.left * (γ.1.right : MulAut stdGroup)
      ⟨p, nativeParabolic_le_stdGroup J p.2⟩ : stdGroup) : ModGL Tag.E6 K) :=
  rfl

@[expose] def parSmul
    {J : Set (Fin 4)} (γ : parStar J) :
    ParabolicCosets J → ParabolicCosets J :=
  Quotient.map' (parMap γ) fun p q hpq => by
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at hpq ⊢
    have e : (((parMap γ p)⁻¹ * parMap γ q : nativeParabolic J) : ModGL Tag.E6 K) =
        (((γ.1.right : MulAut stdGroup) (⟨p, nativeParabolic_le_stdGroup J p.2⟩⁻¹ *
          ⟨q, nativeParabolic_le_stdGroup J q.2⟩) : stdGroup) : ModGL Tag.E6 K) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, coe_parMap, coe_parMap, map_mul, map_inv]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
    rw [e]
    have h1 := (apply_mem_stdBorelG_iff γ.1.right (⟨p, nativeParabolic_le_stdGroup J p.2⟩⁻¹ *
      ⟨q, nativeParabolic_le_stdGroup J q.2⟩)).2 (by
        rw [Subgroup.mem_subgroupOf]
        exact hpq)
    exact h1

theorem parSmul_mk
    {J : Set (Fin 4)} (γ : parStar J) (p : nativeParabolic J) :
    parSmul γ (QuotientGroup.mk p) = QuotientGroup.mk (parMap γ p) :=
  rfl

theorem chamberOf_parSmul
    {J : Set (Fin 4)} (γ : parStar J) (y : ParabolicCosets J) :
    FourthResidue.chamberOf J (parSmul γ y) = γ.1 • FourthResidue.chamberOf J y := by
  induction y using QuotientGroup.induction_on with | H p => ?_
  rfl

theorem range_chamberOf
    (J : Set (Fin 4)) :
    Set.range (FourthResidue.chamberOf J) = baseResidue J :=
  FourthResidue.range_chamberOf J

theorem forall_smul_eq_iff
    {J : Set (Fin 4)} (γ : parStar J) :
    (∀ x ∈ baseResidue J, γ.1 • x = x) ↔ ∀ y : ParabolicCosets J, parSmul γ y = y := by
  constructor
  · intro h y
    apply FourthResidue.chamberOf_injective J
    rw [chamberOf_parSmul]
    exact h _ (range_chamberOf J ▸ ⟨y, rfl⟩)
  · intro h x hx
    rw [← range_chamberOf J] at hx
    obtain ⟨y, rfl⟩ := hx
    rw [← chamberOf_parSmul, h]

open _root_.Classical in
@[expose] noncomputable def betaGroupHom
    {M : Type*} [Group M] (t : M) (ht : t * t = 1) :
    betaGroup →* M where
  toFun b := if (b : MulAut stdGroup) = 1 then 1 else t
  map_one' := by simp
  map_mul' b b' := by
    rcases mem_betaGroup_iff.mp b.2 with h | h <;>
      rcases mem_betaGroup_iff.mp b'.2 with h' | h' <;>
      simp [h, h', betaG_mul_self, betaG_ne_one, ht]

theorem betaGroupHom_of_eq_one
    {M : Type*} [Group M] {t : M} (ht : t * t = 1) {b : betaGroup}
    (hb : (b : MulAut stdGroup) = 1) : betaGroupHom t ht b = 1 := by
  simp [betaGroupHom, hb]

theorem betaGroupHom_of_eq_betaG
    {M : Type*} [Group M] {t : M} (ht : t * t = 1) {b : betaGroup}
    (hb : (b : MulAut stdGroup) = betaG) : betaGroupHom t ht b = t := by
  simp [betaGroupHom, hb, betaG_ne_one]


abbrev betaPar
    {J : Set (Fin 4)} (b : betaGroup) (p : nativeParabolic J) : nativeParabolic J :=
  ⟨(((b : MulAut stdGroup) ⟨p, nativeParabolic_le_stdGroup J p.2⟩ : stdGroup) : ModGL Tag.E6 K),
    (apply_mem_nativeParabolic_iff b J _).2 p.2⟩

theorem parStar_left_mul
    {J : Set (Fin 4)} (γ γ' : parStar J) :
    parLeft (γ * γ') = parLeft γ * betaPar γ.1.right (parLeft γ') :=
  Subtype.ext rfl

theorem parMap_eq_mul
    {J : Set (Fin 4)} (γ : parStar J) (p : nativeParabolic J) :
    parMap γ p = parLeft γ * betaPar γ.1.right p :=
  Subtype.ext rfl

abbrev betaElt
    : betaGroup := ⟨betaG, Subgroup.mem_zpowers betaG⟩

abbrev leviStar
    {J : Set (Fin 4)} (hJ : (2 : Fin 4) ∈ J) (l : stdLevi J) (b : betaGroup) :
    parStar J :=
  ⟨⟨⟨l, nativeParabolic_le_stdGroup J (stdLevi_le_nativeParabolic hJ l.2)⟩, b⟩,
    stdLevi_le_nativeParabolic hJ l.2⟩

end CFSG.LieType.Chevalley.C2E6Std.FieldExtension
