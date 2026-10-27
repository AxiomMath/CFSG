module

public import CFSG.LieType.Chevalley.C2E6FieldExtensionBeta
public import CFSG.LieType.Chevalley.C2E6NativeF4Building

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std.FieldExtension

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

abbrev betaGroup
    : Subgroup (MulAut stdGroup) := Subgroup.zpowers betaG

theorem mem_betaGroup_iff
    {b : MulAut stdGroup} : b ∈ betaGroup ↔ b = 1 ∨ b = betaG := by
  constructor
  · intro hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    rw [← zpow_mod_orderOf, orderOf_betaG]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      rw [Nat.cast_ofNat, h, zpow_zero]
    · right
      rw [Nat.cast_ofNat, h, zpow_one]
  · rintro (rfl | rfl)
    exacts [one_mem _, Subgroup.mem_zpowers _]

theorem card_betaGroup :
    Nat.card betaGroup = 2 := by
  rw [Nat.card_zpowers, orderOf_betaG]

abbrev GStar :
    Type := stdGroup ⋊[betaGroup.subtype] betaGroup

theorem card_GStar
    : Nat.card GStar = 153064959367549707878400 := by
  rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod, card_stdGroup, card_betaGroup]

theorem betaGL_mem_stdBorel_iff
    {g : ModGL Tag.E6 K} : betaGL g ∈ stdBorel ↔ g ∈ stdBorel :=
  ⟨fun h => betaGL_betaGL g ▸ betaGL_mem_stdBorel h, betaGL_mem_stdBorel⟩

theorem apply_mem_stdBorelG_iff
    (b : betaGroup) (x : stdGroup) :
    (b : MulAut stdGroup) x ∈ stdBorelG ↔ x ∈ stdBorelG := by
  rcases mem_betaGroup_iff.mp b.2 with h | h <;> rw [h]
  · rfl
  · exact betaGL_mem_stdBorel_iff

@[expose] def chamberMap
    (b : betaGroup) : stdChamber → stdChamber :=
  Quotient.map' (b : MulAut stdGroup) fun x y hxy => by
    rw [QuotientGroup.leftRel_apply] at hxy ⊢
    rw [← map_inv, ← map_mul]
    exact (apply_mem_stdBorelG_iff b _).2 hxy

theorem chamberMap_mk
    (b : betaGroup) (x : stdGroup) :
    chamberMap b (x : stdChamber) = ((b : MulAut stdGroup) x : stdChamber) :=
  rfl

instance :
    MulAction GStar stdChamber where
  smul γ q := γ.left • chamberMap γ.right q
  one_smul q := by
    induction q using QuotientGroup.induction_on with | H x => ?_
    change (1 : stdGroup) • chamberMap 1 (x : stdChamber) = x
    rw [one_smul]
    rfl
  mul_smul γ γ' q := by
    induction q using QuotientGroup.induction_on with | H x => ?_
    change (γ * γ').left • chamberMap (γ * γ').right (x : stdChamber) =
      γ.left • chamberMap γ.right (γ'.left • chamberMap γ'.right (x : stdChamber))
    simp only [chamberMap_mk, MulAction.Quotient.smul_mk, SemidirectProduct.mul_left,
      SemidirectProduct.mul_right]
    congr 1
    simp only [smul_eq_mul, Subgroup.coe_mul, MulAut.mul_apply, map_mul, Subgroup.subtype_apply,
      mul_assoc]

theorem smul_mk
    (γ : GStar) (x : stdGroup) :
    γ • (x : stdChamber) = ((γ.left * (γ.right : MulAut stdGroup) x : stdGroup) : stdChamber) :=
  rfl

theorem eq_one_of_forall_smul_eq
    {n : stdGroup} (h : ∀ q : stdChamber, n • q = q) : n = 1 := by
  have hker : n ∈ (MulAction.toPermHom stdGroup stdChamber).ker := Equiv.Perm.ext h
  have hcore := (fixed_Borel_core_center TwistTag.E6 K barEquiv).2
  have hcen := exceptional_fixed_center_trivial TwistTag.E6 K barEquiv
  rw [barEquiv_toRingHom] at hcore hcen
  exact Subgroup.mem_bot.mp (hcen.le (hcore.le hker))

theorem eq_one_of_forall_smul_eq_star
    {γ : GStar} (h : ∀ q : stdChamber, γ • q = q) : γ = 1 := by
  rcases mem_betaGroup_iff.mp γ.right.2 with hb | hb
  · have hr : γ.right = 1 := Subtype.ext hb
    have hl : γ.left = 1 := eq_one_of_forall_smul_eq fun q => by
      induction q using QuotientGroup.induction_on with | H x => ?_
      have := h (x : stdChamber)
      rwa [smul_mk, hb, MulAut.one_apply] at this
    exact SemidirectProduct.ext hl hr
  · exfalso
    set n := γ.left
    have key : ∀ x : stdGroup, ((n * betaG x : stdGroup) : stdChamber) = x := fun x => by
      have := h (x : stdChamber)
      rwa [smul_mk, hb] at this
    have hinv : ∀ y : stdGroup, n⁻¹ • (y : stdChamber) = (betaG y : stdChamber) := fun y => by
      rw [← key y, MulAction.Quotient.smul_mk, smul_eq_mul, inv_mul_cancel_left]
    have hconj : ∀ x : stdGroup, betaG x = n⁻¹ * x * n := by
      intro x
      have h1 : ∀ q : stdChamber, (x⁻¹ * n * betaG x * n⁻¹) • q = q := by
        intro q
        induction q using QuotientGroup.induction_on with | H y => ?_
        rw [mul_smul, hinv, MulAction.Quotient.smul_mk, smul_eq_mul, mul_assoc, mul_assoc,
          ← map_mul, ← smul_eq_mul, ← MulAction.Quotient.smul_mk, key, MulAction.Quotient.smul_mk,
          smul_eq_mul, inv_mul_cancel_left]
      have h2 := eq_one_of_forall_smul_eq h1
      rw [mul_inv_eq_one, mul_assoc, inv_mul_eq_iff_eq_mul] at h2
      rw [mul_assoc, ← h2, inv_mul_cancel_left]
    exact betaG_ne_conj n⁻¹ (MulEquiv.ext fun x => by
      rw [hconj x, MulAut.conj_apply, inv_inv])

theorem betaGL_mem_stdBruhatCell
    {w : relWeylTwist TwistTag.E6} {g : ModGL Tag.E6 K}
    (hg : g ∈ stdBruhatCell w) : betaGL g ∈ stdBruhatCell w := by
  rw [stdBruhatCell_eq] at hg ⊢
  obtain ⟨y, ⟨b, hb, r, hr, rfl⟩, b', hb', rfl⟩ := hg
  rw [Set.mem_singleton_iff] at hr
  subst hr
  have hn : betaGL (stdRepM w) = stdRepM w := betaGL_canonicalRep _
  refine ⟨betaGL b * stdRepM w, ⟨betaGL b, betaGL_mem_stdBorel hb, stdRepM w, rfl, rfl⟩,
    betaGL b', betaGL_mem_stdBorel hb', ?_⟩
  rw [map_mul, map_mul, hn]

theorem apply_mem_stdBruhatCell_iff
    (b : betaGroup) (w : relWeylTwist TwistTag.E6)
    (x : stdGroup) :
    (((b : MulAut stdGroup) x : stdGroup) : ModGL Tag.E6 K) ∈ stdBruhatCell w ↔
      (x : ModGL Tag.E6 K) ∈ stdBruhatCell w := by
  rcases mem_betaGroup_iff.mp b.2 with h | h <;> rw [h]
  · rfl
  · exact ⟨fun hx => betaGL_betaGL (x : ModGL Tag.E6 K) ▸ betaGL_mem_stdBruhatCell hx,
      betaGL_mem_stdBruhatCell⟩

theorem stdDistance_smul
    (γ : GStar) (x y : stdChamber) :
    stdDistance (γ • x) (γ • y) = stdDistance x y := by
  induction x using QuotientGroup.induction_on with | H g => ?_
  induction y using QuotientGroup.induction_on with | H h => ?_
  rw [smul_mk, smul_mk, stdDistance_mk_eq_iff]
  have e : (((γ.left * (γ.right : MulAut stdGroup) g : stdGroup) : ModGL Tag.E6 K))⁻¹ *
      ((γ.left * (γ.right : MulAut stdGroup) h : stdGroup) : ModGL Tag.E6 K) =
      (((γ.right : MulAut stdGroup) (g⁻¹ * h) : stdGroup) : ModGL Tag.E6 K) := by
    rw [map_mul, map_inv]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  rw [e, apply_mem_stdBruhatCell_iff, Subgroup.coe_mul, Subgroup.coe_inv]
  exact (stdDistance_mk_eq_iff g h _).1 rfl


open CFSG.LieType.Chevalley.CosetBuilding in
theorem image_smul_residue
    (γ : GStar) (J : Set (Fin 4)) (x : stdChamber) :
    (γ • ·) '' residue nativeCoxeterSystem stdDistance J x =
      residue nativeCoxeterSystem stdDistance J (γ • x) := by
  have hmap : ∀ (γ : GStar) (a b : stdChamber),
      Relation.ReflTransGen (fun a b => ∃ i ∈ J, stdDistance a b = nativeCoxeterSystem.simple i)
        a b →
      Relation.ReflTransGen (fun a b => ∃ i ∈ J, stdDistance a b = nativeCoxeterSystem.simple i)
        (γ • a) (γ • b) := fun γ a b hab =>
    Relation.ReflTransGen.lift (p := fun a b => ∃ i ∈ J,
      stdDistance a b = nativeCoxeterSystem.simple i) (γ • ·)
      (fun a b ⟨i, hi, h⟩ => ⟨i, hi, by rw [stdDistance_smul, h]⟩) a b hab
  ext y
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hmap γ x y hy
  · intro hy
    refine ⟨γ⁻¹ • y, ?_, smul_inv_smul γ y⟩
    have h := hmap γ⁻¹ _ _ hy
    rwa [inv_smul_smul] at h

end CFSG.LieType.Chevalley.C2E6Std.FieldExtension
