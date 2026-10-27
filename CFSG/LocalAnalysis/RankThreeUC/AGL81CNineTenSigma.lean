module


import CFSG.RankThree.PartTwo.KFacts.KP14MonomialStructure
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CanonicalPerfectLifts
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNBridgeB
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.Asc83Table.Automizer
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15 Subgroup
open CFSG.RankThree.Asc83Table CFSG.RankThree.PartTwo.KFacts.KP14
open scoped Matrix

private lemma exists_zpowers_of_card_three {V : Type*} [Group V] [Finite V]
    (H : Subgroup V) (hH : Nat.card H = 3) :
    ∃ d : V, d ∈ H ∧ H = Subgroup.zpowers d ∧ orderOf d = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : 3 ∣ Nat.card H := by rw [hH]
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  refine ⟨(x : V), x.2, ?_, ?_⟩
  · exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr x.2)
      (by rw [hH, Nat.card_zpowers, Subgroup.orderOf_coe, hx])).symm
  · rw [Subgroup.orderOf_coe, hx]

private lemma zpowers_ofAdd_single_injective {n : ℕ} {i j : Fin n}
    (h : Subgroup.zpowers (Multiplicative.ofAdd
        (Pi.single i (1 : ZMod 3) : Fin n → ZMod 3)) =
      Subgroup.zpowers (Multiplicative.ofAdd
        (Pi.single j (1 : ZMod 3) : Fin n → ZMod 3))) : i = j := by
  by_contra hne
  have hmem : Multiplicative.ofAdd (Pi.single i (1 : ZMod 3) : Fin n → ZMod 3) ∈
      Subgroup.zpowers (Multiplicative.ofAdd
        (Pi.single j (1 : ZMod 3) : Fin n → ZMod 3)) := by
    rw [← h]
    exact Subgroup.mem_zpowers _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have h1 : k • (Pi.single j (1 : ZMod 3) : Fin n → ZMod 3) =
      (Pi.single i (1 : ZMod 3) : Fin n → ZMod 3) := by
    have := congrArg Multiplicative.toAdd hk
    simpa using this
  have h2 := congrFun h1 i
  rw [Pi.smul_apply, Pi.single_eq_of_ne hne, smul_zero, Pi.single_eq_same] at h2
  exact one_ne_zero h2.symm

private lemma mulVec_ne_zero_of_unit {n : ℕ} (A : GL (Fin n) (ZMod 3))
    {v : Fin n → ZMod 3} (hv : v ≠ 0) :
    ((A : Matrix (Fin n) (Fin n) (ZMod 3)) *ᵥ v) ≠ 0 := by
  intro h
  apply hv
  have h1 : (((A⁻¹ : GL (Fin n) (ZMod 3)) : Matrix (Fin n) (Fin n) (ZMod 3)) *
      (A : Matrix (Fin n) (Fin n) (ZMod 3))) *ᵥ v = v := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have h2 : (((A⁻¹ : GL (Fin n) (ZMod 3)) : Matrix (Fin n) (Fin n) (ZMod 3)) *
      (A : Matrix (Fin n) (Fin n) (ZMod 3))) *ᵥ v = 0 := by
    rw [← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]
  rw [h2] at h1
  exact h1.symm

theorem exists_hom_perm_four_of_lines {V : Type} [Group V] [Finite V]
    (hVc : ∀ a b : V, a * b = b * a) (hV3 : ∀ v : V, v ^ 3 = 1) (hV : Nat.card V = 27)
    (D : Fin 3 → Subgroup V) (hD : ∀ i, Nat.card (D i) = 3) (hDV : (⨆ i, D i) = ⊤)
    {X : Type} [Group X] (ρ : X →* MulAut V)
    (hρ : ∀ x i, ∃ j, (D i).map (ρ x).toMonoidHom = D j) :
    ∃ σ : X →* Equiv.Perm (Fin 4), ∀ x, σ x = 1 → ρ x = 1 ∨ ∀ v, ρ x v = v⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  choose d hdD hdDz hdord using fun i => exists_zpowers_of_card_three (D i) (hD i)
  have hd3 : ∀ i, d i ^ 3 = 1 := fun i => by
    rw [← hdord i]; exact pow_orderOf_eq_one _
  have hcomm : ∀ i j, Commute (d i) (d j) := fun i j => hVc _ _
  have hcl : closure (Set.range d) = ⊤ := by
    rw [show Set.range d = ⋃ i, ({d i} : Set V) by
      ext v
      simp only [Set.mem_range, Set.mem_iUnion, Set.mem_singleton_iff]
      exact ⟨fun ⟨i, hi⟩ => ⟨i, hi.symm⟩, fun ⟨i, hi⟩ => ⟨i, hi.symm⟩⟩]
    rw [Subgroup.closure_iUnion]
    simp_rw [← Subgroup.zpowers_eq_closure]
    have hsup : (⨆ i, Subgroup.zpowers (d i)) = ⨆ i, D i :=
      iSup_congr fun i => (hdDz i).symm
    rw [hsup]
    exact hDV
  have hcard : Nat.card (Multiplicative (Fin 3 → ZMod 3)) = 27 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]
  have hsurj : Function.Surjective (basisHom (x := d) hd3 hcomm) :=
    basisHom_surjective (x := d) hd3 hcomm
  have hbij : Function.Bijective (basisHom (x := d) hd3 hcomm) :=
    hsurj.bijective_of_nat_card_le (by rw [hcard, hcl, Subgroup.card_top, hV])
  have hinj : Function.Injective (basisProd d) := by
    intro a b hab
    have key : basisHom (x := d) hd3 hcomm (Multiplicative.ofAdd a) =
        basisHom (x := d) hd3 hcomm (Multiplicative.ofAdd b) := by
      apply Subtype.ext
      rw [coe_basisHom, coe_basisHom]
      simpa using hab
    exact Multiplicative.ofAdd.injective (hbij.1 key)
  let c : Multiplicative (Fin 3 → ZMod 3) ≃* closure (Set.range d) :=
    basisEquiv (x := d) hd3 hcomm hinj
  let c' : Multiplicative (Fin 3 → ZMod 3) →* V :=
    (Subgroup.subtype (closure (Set.range d))).comp c.toMonoidHom
  have hc'inj : Function.Injective c' := fun a b hab => c.injective (Subtype.ext hab)
  have hc'surj : Function.Surjective c' := by
    intro v
    obtain ⟨a, ha⟩ := c.surjective ⟨v, hcl ▸ Subgroup.mem_top v⟩
    refine ⟨a, ?_⟩
    change ((c a : closure (Set.range d)) : V) = v
    simpa using congrArg (fun x : closure (Set.range d) => (x : V)) ha
  have hf : Function.Bijective c' := ⟨hc'inj, hc'surj⟩
  let e : V ≃* Multiplicative (Fin 3 → ZMod 3) := (MulEquiv.ofBijective c' hf).symm
  have hc'single : ∀ i, c' (Multiplicative.ofAdd
      (Pi.single i (1 : ZMod 3) : Fin 3 → ZMod 3)) = d i :=
    fun i => basisEquiv_single (x := d) hd3 hcomm hinj i
  have he : ∀ i, e (d i) = Multiplicative.ofAdd
      (Pi.single i (1 : ZMod 3) : Fin 3 → ZMod 3) := by
    intro i
    rw [← hc'single i]
    exact (MulEquiv.ofBijective c' hf).symm_apply_apply _
  let G : X →* GL (Fin 3) (ZMod 3) :=
    (CFSG.SectionRank.Ccomm.elemAutEquivGL e).toMonoidHom.comp ρ
  have hmono : ∀ x, G x ∈ monomial := by
    intro x
    let A : GL (Fin 3) (ZMod 3) := CFSG.SectionRank.Ccomm.elemAutEquivGL e (ρ x)
    change A ∈ monomial
    let π : Fin 3 → Fin 3 := fun i => Classical.choose (hρ x i)
    have hπx : ∀ i, (D i).map (ρ x).toMonoidHom = D (π i) :=
      fun i => Classical.choose_spec (hρ x i)
    have hπinj : Function.Injective π := by
      intro i j hij
      have hmap : (D i).map (ρ x).toMonoidHom = (D j).map (ρ x).toMonoidHom := by
        rw [hπx i, hπx j, hij]
      have hDij : D i = D j := Subgroup.map_injective (ρ x).injective hmap
      have hz : Subgroup.zpowers (Multiplicative.ofAdd
            (Pi.single i (1 : ZMod 3) : Fin 3 → ZMod 3)) =
          Subgroup.zpowers (Multiplicative.ofAdd
            (Pi.single j (1 : ZMod 3) : Fin 3 → ZMod 3)) := by
        have hmap_e : (D i).map e.toMonoidHom = (D j).map e.toMonoidHom := by rw [hDij]
        have h1 : (D i).map e.toMonoidHom = Subgroup.zpowers (Multiplicative.ofAdd
            (Pi.single i (1 : ZMod 3) : Fin 3 → ZMod 3)) := by
          rw [hdDz i, MonoidHom.map_zpowers]
          exact congrArg Subgroup.zpowers (he i)
        have h2 : (D j).map e.toMonoidHom = Subgroup.zpowers (Multiplicative.ofAdd
            (Pi.single j (1 : ZMod 3) : Fin 3 → ZMod 3)) := by
          rw [hdDz j, MonoidHom.map_zpowers]
          exact congrArg Subgroup.zpowers (he j)
        rw [h1, h2] at hmap_e
        exact hmap_e
      exact zpowers_ofAdd_single_injective hz
    have hπbij : Function.Bijective π := Finite.injective_iff_bijective.mp hπinj
    have hex : ∀ j : Fin 3, ∃ k : ℤ, (d (π j)) ^ k = ρ x (d j) := by
      intro j
      have hmem : ρ x (d j) ∈ D (π j) := by
        rw [← hπx j]
        exact Subgroup.mem_map_of_mem (ρ x).toMonoidHom (hdD j)
      rw [hdDz (π j)] at hmem
      exact Subgroup.mem_zpowers_iff.mp hmem
    let s : Fin 3 → ZMod 3 := fun j => ((Classical.choose (hex j) : ℤ) : ZMod 3)
    have hs : ∀ j, (d (π j)) ^ (Classical.choose (hex j)) = ρ x (d j) :=
      fun j => Classical.choose_spec (hex j)
    have hcol : ∀ j, (A : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ
        (Pi.single j (1 : ZMod 3) : Fin 3 → ZMod 3) =
        s j • (Pi.single (π j) (1 : ZMod 3) : Fin 3 → ZMod 3) := by
      intro j
      have hmv := CFSG.SectionRank.Ccomm.elemAutEquivGL_mulVec e (ρ x) (d j)
      rw [he j, toAdd_ofAdd] at hmv
      have hA : (A : Matrix (Fin 3) (Fin 3) (ZMod 3)) =
          (CFSG.SectionRank.Ccomm.elemAutEquivGL e (ρ x) :
            Matrix (Fin 3) (Fin 3) (ZMod 3)) := rfl
      have h1 : e (ρ x (d j)) = e ((d (π j)) ^ (Classical.choose (hex j))) :=
        (congrArg e (hs j)).symm
      have hz : e (ρ x (d j)) = (Multiplicative.ofAdd
          (Pi.single (π j) (1 : ZMod 3) : Fin 3 → ZMod 3)) ^
          (Classical.choose (hex j)) := by
        rw [h1, map_zpow]
        exact congrArg (fun x => x ^ (Classical.choose (hex j))) (he (π j))
      have hkv : Multiplicative.toAdd (e (ρ x (d j))) =
          (Classical.choose (hex j)) •
            (Pi.single (π j) (1 : ZMod 3) : Fin 3 → ZMod 3) := by
        rw [hz, toAdd_zpow, toAdd_ofAdd]
      rw [hkv] at hmv
      rw [hA, hmv]
      funext i
      rw [Pi.smul_apply, Pi.smul_apply]
      by_cases hi : i = π j
      · subst hi
        rw [Pi.single_eq_same]
        simp only [s, Int.smul_one_eq_cast, smul_eq_mul, mul_one]
      · rw [Pi.single_eq_of_ne hi]
        simp
    have hs0 : ∀ j, s j ≠ 0 := by
      intro j hsj
      have hsingle : (Pi.single j (1 : ZMod 3) : Fin 3 → ZMod 3) ≠ 0 := by
        intro h
        have := congrFun h j
        simp at this
      have hne := mulVec_ne_zero_of_unit A hsingle
      rw [hcol j, hsj, zero_smul] at hne
      exact hne rfl
    have hmat : (A : Matrix (Fin 3) (Fin 3) (ZMod 3)) = signedMat π s := by
      refine Matrix.ext_of_mulVec_single fun j => ?_
      rw [hcol j, Matrix.mulVec_single_one]
      ext i
      by_cases h : i = π j
      · simp [signedMat, h]
      · simp [signedMat, h, Pi.single_eq_of_ne h]
    exact mem_monomial_of π s hπbij hs0 hmat
  let F : X →* monomial := G.codRestrict monomial hmono
  let σ : X →* Equiv.Perm (Fin 4) := diagPerm.comp F
  refine ⟨σ, fun x hx => ?_⟩
  have hx' : diagPerm (F x) = 1 := by simpa [σ] using hx
  rcases eq_one_or_eq_negOne hx' with h1 | hneg
  · left
    have hA : CFSG.SectionRank.Ccomm.elemAutEquivGL e (ρ x) = 1 := by
      have := congrArg Subtype.val h1
      simpa [F, G] using this
    exact (CFSG.SectionRank.Ccomm.elemAutEquivGL e).injective (by rw [hA, map_one])
  · right
    have hA : CFSG.SectionRank.Ccomm.elemAutEquivGL e (ρ x) = -1 := by
      have := congrArg Subtype.val hneg
      simpa [F, G, negOne] using this
    exact (CFSG.SectionRank.Ccomm.elemAutEquivGL_eq_neg_one_iff e (ρ x)).mp hA

theorem mem_center_mulAut_of_forall_eq_inv {V : Type} [Group V] {α : MulAut V}
    (hα : ∀ v, α v = v⁻¹) : α ∈ Subgroup.center (MulAut V) := by
  refine Subgroup.mem_center_iff.mpr fun β => MulEquiv.ext fun v => ?_
  change β (α v) = α (β v)
  rw [hα, hα, map_inv]

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
