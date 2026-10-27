module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3318D
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3319D

public section
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.L3319

open CFSG.Open (pCoreOf quasithinOmegaOneCenter)
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.JonesParshall (wedgeRep)
open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem exists_data_F4 (h14 : Stmt3_3_14_F4) (hGA : CFSG.Open.GriessAllModelsStatement)
    {T M L D : Subgroup G} (h : Hyp331 G T M L D) [IsMulCommutative ↥(vPlus L T)]
    (e : ↥(autOn L (vPlus L T)) ≃* SpecialLinearGroup (Fin 5) (ZMod 2))
    (hext : SLExteriorTwo (autOn L (vPlus L T)) (commV (autOn L (vPlus L T))) ⊥ 5) :
    ∃ (α : ↥L →* SpecialLinearGroup (Fin 5) (ZMod 2))
      (Φ : Multiplicative (Fin 10 → ZMod 2) →* ↥(vPlus L T)), Data G T M L D α Φ := by
  have hTL := L3318.le_normalizer_of_h14_F4 h14 h
  set V := vPlus L T with hVdef
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hred.2.2.2.1
  set Lb := autOn L V with hLb
  obtain ⟨π₀, hr⟩ := hext
  let π : ↥(StatedSL 5 (ZMod 2)) →* ↥Lb := π₀
  have hcardL : Nat.card ↥Lb = 9999360 := by
    rw [Nat.card_congr e.toEquiv, Ln2.card_specialLinear 5 (Or.inr rfl)]
    rfl
  have hπb : Function.Bijective π := Function.Surjective.bijective_of_nat_card_le hr.1 (by
    rw [CFSG.Quasithin.card_statedSL_five_zmod1527d, hcardL])
  set πe := MulEquiv.ofBijective π hπb with hπe
  obtain ⟨β₀, hβs, hβk, hβe⟩ := FFModel.RealizesVia.coord rfl rfl hr
  let β : ↥(commV Lb) →* Multiplicative (⋀[ZMod 2]^2 (Fin 5 → ZMod 2)) := β₀
  have hβi : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have := (hβk x).1 hx
    rw [Subgroup.mem_bot] at this
    exact Subtype.ext this
  let wE : ⋀[ZMod 2]^2 (Fin 5 → ZMod 2) ≃ₗ[ZMod 2] (Fin 10 → ZMod 2) :=
    LinearEquiv.ofBijective JonesParshall.wedgeCoord JonesParshall.wedgeCoord_bijective
  let κ : ↥(commV Lb) ≃* Multiplicative (Fin 10 → ZMod 2) :=
    (MulEquiv.ofBijective β ⟨hβi, hβs⟩).trans (AddEquiv.toMultiplicative wE.toAddEquiv)
  have hκ : ∀ u, Multiplicative.toAdd (κ u) =
      JonesParshall.wedgeCoord (Multiplicative.toAdd (β u)) := fun u => rfl
  let Φ₀ : Multiplicative (Fin 10 → ZMod 2) →* ↥V := (commV Lb).subtype.comp κ.symm.toMonoidHom
  have hconj : ∀ l : ↥L, conjOf V L hLV l ∈ Lb := fun l => by
    rw [hLb, ← range_conjOf hLV]
    exact ⟨l, rfl⟩
  let conjL : ↥L →* ↥Lb := (conjOf V L hLV).codRestrict Lb hconj
  let E := specialLinearGroupEquivStatedSL 5 (ZMod 2)
  let α₀ : ↥L →* SpecialLinearGroup (Fin 5) (ZMod 2) :=
    E.symm.toMonoidHom.comp (πe.symm.toMonoidHom.comp conjL)
  have hα₀π : ∀ l : ↥L, π (E (α₀ l)) = conjL l := fun l => by
    show π (E (E.symm (πe.symm (conjL l)))) = conjL l
    rw [MulEquiv.apply_symm_apply]
    exact πe.apply_symm_apply (conjL l)
  have hconjs : Function.Surjective conjL := by
    rintro ⟨a, ha⟩
    rw [hLb, ← range_conjOf hLV] at ha
    obtain ⟨l, rfl⟩ := ha
    exact ⟨l, rfl⟩
  have hα₀s : Function.Surjective α₀ :=
    E.symm.surjective.comp (πe.symm.surjective.comp hconjs)
  have hα₀c : ∀ l : ↥L, α₀ l = 1 ↔ (l : G) ∈ Subgroup.centralizer (V : Set G) := by
    intro l
    rw [← conjOf_eq_one_iff hLV]
    constructor
    · intro h1
      have := hα₀π l
      rw [h1, map_one, map_one] at this
      exact congrArg Subtype.val this.symm
    · intro h1
      have h2 : conjL l = 1 := Subtype.ext h1
      show E.symm (πe.symm (conjL l)) = 1
      rw [h2, map_one, map_one]
  have hΦ₀ : ∀ (l : ↥L) (x : Multiplicative (Fin 10 → ZMod 2)),
      (l : G) * (Φ₀ x : G) * (l : G)⁻¹ =
        (Φ₀ (Multiplicative.ofAdd (wedgeRep (α₀ l) (Multiplicative.toAdd x))) : G) := by
    intro l x
    set u := κ.symm x with hu
    have hmem : ((π (E (α₀ l)) : ↥Lb) : MulAut ↥V) (u : ↥V) ∈ commV Lb :=
      hr.2.2.2.1 (π (E (α₀ l))) u u.2
    have h1 : β ⟨_, hmem⟩ = extSqAct (ZMod 2) 5 (E (α₀ l)) (β u) := hβe (E (α₀ l)) u hmem
    have hxu : Multiplicative.toAdd x = JonesParshall.wedgeCoord (Multiplicative.toAdd (β u)) := by
      rw [← hκ, hu, MulEquiv.apply_symm_apply]
    have h2 : κ ⟨_, hmem⟩ = Multiplicative.ofAdd (wedgeRep (α₀ l) (Multiplicative.toAdd x)) := by
      apply Multiplicative.toAdd.injective
      rw [hκ, toAdd_ofAdd, h1, JonesParshall.Curtis.wedgeRep_apply', hxu,
        ← JonesParshall.wedgeCoord_map]
      rfl
    have h3 : (Φ₀ (Multiplicative.ofAdd (wedgeRep (α₀ l) (Multiplicative.toAdd x))) : G) =
        ((((π (E (α₀ l)) : ↥Lb) : MulAut ↥V) (u : ↥V) : ↥V) : G) := by
      rw [← h2]
      show (((κ.symm (κ ⟨_, hmem⟩) : ↥(commV Lb)) : ↥V) : G) = _
      rw [MulEquiv.symm_apply_apply]
    rw [h3, hα₀π]
    exact (conjOf_coe hLV l u).symm
  obtain ⟨α', -, hα'k, hα'c⟩ :=
    Ln2.exists_modO2Surj h hGA hTL (Nat.card_zmod 2) (by norm_num) le_rfl e
  have hker₀ : α₀.ker = CFSG.pCore 2 ↥L := by
    rw [← hα'k]
    ext l
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hα₀c, hα'c]
  have hS₀ : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal h.toSetup331.isSylowTwoOf le_sup_left
      (sup_le Subgroup.le_normalizer hTL)
  obtain ⟨g, hg⟩ := L3318.exists_conj_unitriangular hS₀ (K := ZMod 2) (by norm_num) hα₀s
  have hwg : ∀ (a b : SpecialLinearGroup (Fin 5) (ZMod 2)) (y : Multiplicative (Fin 10 → ZMod 2)),
      wedgeHom a (wedgeHom b y) = wedgeHom (a * b) y := fun a b y => by
    show Multiplicative.ofAdd (wedgeRep a (wedgeRep b (Multiplicative.toAdd y))) =
      Multiplicative.ofAdd (wedgeRep (a * b) (Multiplicative.toAdd y))
    rw [wedgeRep_mul_apply]
  have hw1 : ∀ y : Multiplicative (Fin 10 → ZMod 2), wedgeHom 1 y = y := fun y => by
    show Multiplicative.ofAdd (wedgeRep 1 (Multiplicative.toAdd y)) = y
    rw [wedgeRep_one_apply]
    rfl
  have hwb : Function.Bijective (wedgeHom g⁻¹) := by
    refine ⟨fun a b hab => ?_, fun a => ⟨wedgeHom g a, by rw [hwg, inv_mul_cancel, hw1]⟩⟩
    have := congrArg (wedgeHom g) hab
    rwa [hwg, hwg, mul_inv_cancel, hw1, hw1] at this
  refine ⟨(MulAut.conj g).toMonoidHom.comp α₀, Φ₀.comp (wedgeHom g⁻¹),
    ⟨h, hTL, ?_, ?_, fun l => ?_, hg, ?_, ?_, fun l x => ?_⟩⟩
  · rw [MonoidHom.coe_comp]
    exact (MulEquiv.surjective _).comp hα₀s
  · rw [MonoidHom.ker_comp_of_injective _ _ (MulEquiv.injective _), hker₀]
  · rw [← hα₀c]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
  · exact ((commV Lb).subtype_injective.comp κ.symm.injective).comp hwb.1
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hwb.2, ← MonoidHom.range_eq_map,
      MonoidHom.range_comp, MonoidHom.range_eq_top.mpr κ.symm.surjective,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype, hLb, Ln2.commV_autOn_eq h]
  · rw [MonoidHom.comp_apply, hΦ₀]
    refine congrArg (fun y => (Φ₀ y : G)) ?_
    show Multiplicative.ofAdd (wedgeRep (α₀ l) (wedgeRep g⁻¹ (Multiplicative.toAdd x))) =
      Multiplicative.ofAdd (wedgeRep g⁻¹ (wedgeRep (g * α₀ l * g⁻¹) (Multiplicative.toAdd x)))
    rw [← wedgeRep_mul_apply, ← wedgeRep_mul_apply,
      show g⁻¹ * (g * α₀ l * g⁻¹) = α₀ l * g⁻¹ by group]

end CFSG.Quasithin.H13.L3319
