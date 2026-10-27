module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTFac
public import CFSG.LieType.SemisimpleCentralizers.HeldCompTrivSU
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HSubT

open CFSG.Open CFSG.Open.StatedAPI CFSG.Yardstones.Md0ec50421ce4 Matrix
open CFSG.LieType.SemisimpleCentralizers.Held
open scoped commutatorElement

theorem scalar_eq_one_of_det_four {E : Type} [Field E] [Fintype E] (hE : Fintype.card E = 4)
    {z : GL (Fin 4) E} (hz : z ∈ StatedScalars (Fin 4) E)
    (hdet : (z : Matrix (Fin 4) (Fin 4) E).det = 1) : z = 1 := by
  obtain ⟨c, rfl⟩ := hz
  have h4 : ((Matrix.GeneralLinearGroup.scalar (Fin 4) c : GL (Fin 4) E) :
      Matrix (Fin 4) (Fin 4) E).det = ((c : Eˣ) : E) ^ 4 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.det_scalar,
      Fintype.card_fin, Units.val_pow_eq_pow_val]
  have hc1 : ((c : Eˣ) : E) ^ 4 = 1 := by rw [← h4]; exact hdet
  have hcc : ((c : Eˣ) : E) ^ 4 = ((c : Eˣ) : E) := by
    have h := FiniteField.pow_card ((c : Eˣ) : E)
    rwa [hE] at h
  have hc : ((c : Eˣ) : E) = 1 := hcc.symm.trans hc1
  rw [show c = 1 from Units.ext hc, map_one]

theorem scalars_subgroupOf_statedSU_four {E : Type} [Field E] [Fintype E] (hE : Fintype.card E = 4) :
    (StatedScalars (Fin 4) E).subgroupOf (StatedSU 4 2 E) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx
  have hdet : ((x : GL (Fin 4) E) : Matrix (Fin 4) (Fin 4) E).det = 1 :=
    mem_statedSL_iff.mp (statedSU_le_statedSL 4 2 E x.2)
  exact Subtype.ext (scalar_eq_one_of_det_four hE hx hdet)

theorem statedProj_equiv_statedSU_four {E : Type} [Field E] [Fintype E] (hE : Fintype.card E = 4) :
    Nonempty (StatedProj (StatedSU 4 2 E) ≃* ↥(StatedSU 4 2 E)) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq (scalars_subgroupOf_statedSU_four hE)).trans
    QuotientGroup.quotientBot⟩

theorem natCard_statedProj_statedSU_four {E : Type} [Field E] [Finite E] (hE : Nat.card E = 4) :
    Nat.card (StatedProj (StatedSU 4 2 E)) = 25920 := by
  have hK' : Nat.card E = (2 ^ 1) ^ 2 := hE.trans (by norm_num)
  have h := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU (K := E) (p := 2) (f := 1)
    (n := 4) Nat.prime_two le_rfl hK' (by norm_num)
  norm_num at h
  exact h

theorem isSimpleGroup_statedProj_statedSU_four {E : Type} [Field E] [Finite E] (hE : Nat.card E = 4) :
    IsSimpleGroup (StatedProj (StatedSU 4 2 E)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU E 2 1 (hE.trans (by norm_num)) 4
    (by norm_num) (by norm_num)

theorem gu4_center_eq_bot_of_simple {X : Type} [Group X] [IsSimpleGroup X]
    (hq : CFSG.Open.IsQuasisimple X) : Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    haveI := hq.2
    have hsub : Subsingleton (X ⧸ Subgroup.center X) := by
      rw [h]
      exact QuotientGroup.subsingleton_quotient_top
    exact not_subsingleton (X ⧸ Subgroup.center X) hsub

theorem resGU_comp_four {E : Type} [Field E] [Finite E] (hE : Nat.card E = 4)
    {τ : E ≃+* E} (hτQ : ∀ x, τ x = x ^ 2) (hτ : ∀ x, τ (τ x) = x)
    {n : ℕ} (hn : n = 4) {G : Type} [Group G]
    (e : G ≃* CFSG.LieType.SemisimpleCentralizers.Held.heldGU n E τ hτ)
    (K : Subgroup G) (hK : CFSG.Open.IsComponentOf K ⊤) :
    catalogIs (↥K ⧸ Subgroup.center ↥K) CFSG.LocalAnalysis.GLTheoremA.S9.isU4two ∧
      Nat.card ↥K = 25920 ∧ Subgroup.center ↥K = ⊥ := by
  subst hn
  haveI : Fintype E := Fintype.ofFinite E
  have hE' : Fintype.card E = 4 := by rw [← Nat.card_eq_fintype_card]; exact hE
  obtain ⟨φ, hφ⟩ : ∃ φ : G →* GL (Fin 4) E,
      ∀ x : G, φ x = ((e x : heldGU 4 E τ hτ) : GL (Fin 4) E) :=
    ⟨(heldGU 4 E τ hτ).subtype.comp e.toMonoidHom, fun x => rfl⟩
  have hφinj : Function.Injective φ := by
    intro a b hab
    apply e.injective
    apply Subtype.ext
    rw [← hφ a, ← hφ b]
    exact hab
  have hφle : heldSU 4 E τ hτ ≤ φ.range := by
    intro g hg
    have hgH : g ∈ heldGU 4 E τ hτ := (Subgroup.mem_inf.mp hg).1
    refine MonoidHom.mem_range.mpr ⟨e.symm ⟨g, hgH⟩, ?_⟩
    rw [hφ, MulEquiv.apply_symm_apply]
  have hcomm : ∀ x y : G, ⁅x, y⁆ ∈ Subgroup.comap φ (heldSU 4 E τ hτ) := by
    intro x y
    rw [Subgroup.mem_comap, map_commutatorElement, hφ, hφ]
    exact commutatorElement_mem_heldSU (e x).2 (e y).2
  have hKT : K ≤ Subgroup.comap φ (heldSU 4 E τ hτ) := by
    have hle : commutator ↥K ≤ (Subgroup.comap φ (heldSU 4 E τ hτ)).subgroupOf K := by
      rw [commutator_def, Subgroup.commutator_le]
      intro x _ y _
      rw [Subgroup.mem_subgroupOf]
      have hc : ((⁅x, y⁆ : ↥K) : G) = ⁅(x : G), (y : G)⁆ := map_commutatorElement K.subtype x y
      rw [hc]
      exact hcomm _ _
    intro k hk
    have h1 : (⟨k, hk⟩ : ↥K) ∈ commutator ↥K := by
      rw [hK.2.2.1]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp (hle h1)
  have hsub : CFSG.Open.IsSubnormal K (Subgroup.comap φ (heldSU 4 E τ hτ)) := by
    have h := hK.2.1.inf_of_le (le_top : Subgroup.comap φ (heldSU 4 E τ hτ) ≤ ⊤)
    rwa [inf_eq_left.mpr hKT] at h
  have hcomp : CFSG.Open.IsComponentOf K (Subgroup.comap φ (heldSU 4 E τ hτ)) :=
    ⟨hKT, hsub, hK.2.2⟩
  have hall := triv_comap φ hφinj (heldSU 4 E τ hτ) hφle
    (fun X hX => SUComponentsTrivial_holds 4 2 E τ hτ (hE.trans (by norm_num)) hτQ X hX)
  have hKtop : K.subgroupOf (Subgroup.comap φ (heldSU 4 E τ hτ)) = ⊤ :=
    hall _ (isComponentOf_top_subgroupOf hcomp)
  have hTK : Subgroup.comap φ (heldSU 4 E τ hτ) ≤ K := by
    intro t ht
    have h1 : (⟨t, ht⟩ : ↥(Subgroup.comap φ (heldSU 4 E τ hτ))) ∈
        K.subgroupOf (Subgroup.comap φ (heldSU 4 E τ hτ)) := by
      rw [hKtop]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp h1
  have hKeq : K = Subgroup.comap φ (heldSU 4 E τ hτ) := le_antisymm hKT hTK
  obtain ⟨eT⟩ := comap_equiv_of_injective_le_range φ hφinj (heldSU 4 E τ hτ) hφle
  have hSUeq : heldSU 4 E τ hτ = StatedSU 4 2 E := hct_heldSU_eq_statedSU (a := 4) hτQ
  obtain ⟨eKS⟩ : Nonempty (↥K ≃* ↥(StatedSU 4 2 E)) :=
    ⟨(MulEquiv.subgroupCongr hKeq).trans (eT.trans (MulEquiv.subgroupCongr hSUeq))⟩
  obtain ⟨eP⟩ := statedProj_equiv_statedSU_four hE'
  haveI : IsSimpleGroup (StatedProj (StatedSU 4 2 E)) := isSimpleGroup_statedProj_statedSU_four hE
  haveI : IsSimpleGroup ↥(StatedSU 4 2 E) := eP.symm.isSimpleGroup
  haveI : IsSimpleGroup ↥K := eKS.isSimpleGroup
  have hcen : Subgroup.center ↥K = ⊥ := gu4_center_eq_bot_of_simple hK.2.2
  have hcard : Nat.card ↥K = 25920 := by
    rw [Nat.card_congr eKS.toEquiv, ← Nat.card_congr eP.toEquiv]
    exact natCard_statedProj_statedSU_four hE
  have eQ : (↥K ⧸ Subgroup.center ↥K) ≃* StatedProj (StatedSU 4 (2 ^ 1) E) :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans
      (QuotientGroup.quotientBot.trans (eKS.trans eP.symm))
  exact ⟨CFSG.LocalAnalysis.GLTheoremA.CatB.catalogIs_u4two_of_statedProj hE eQ, hcard, hcen⟩

end CFSG.LocalAnalysis.GLTheoremA.HSubT

end
