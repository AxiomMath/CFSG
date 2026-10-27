module

public import CFSG.GH74.GLS.IVK.Prod.Lemma31
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.Assembly.GL83LieDefs
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.GrpA
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx4
public import CFSG.GH74.GLS.Stage1.Thm6.Prod.Transport
public import CFSG.GH74.GLS.Stage2.Final.ModelGroupTheory
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6 CFSG.GH74.GLS.Stage1.Thm3.Sec7
  CFSG.GH74.GLS.Stage1.Thm3.Sec8 CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm6.Prod
  CFSG.GH74.GLS.Stage2.Final CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

section LayerProd

variable {X A B : Type*} [Group X] [Group A] [Group B]

theorem layer_equiv_of_prod [IsSimpleGroup A] (hA : ∃ a b : A, a * b ≠ b * a)
    (hB : ∀ a b : B, a * b = b * a) (e : X ≃* A × B) : Nonempty (↥(layer X) ≃* A) := by
  classical
  let f : X →* B := (MonoidHom.snd A B).comp e.toMonoidHom
  let P : Subgroup X := f.ker
  have hPn : P.Normal := f.normal_ker
  let g : ↥P →* A := ((MonoidHom.fst A B).comp e.toMonoidHom).comp P.subtype
  have hginj : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    apply e.injective
    refine Prod.ext hxy ?_
    have hx : (e (x : X)).2 = 1 := x.2
    have hy : (e (y : X)).2 = 1 := y.2
    exact hx.trans hy.symm
  have hgsurj : Function.Surjective g := by
    intro a
    refine ⟨⟨e.symm (a, 1), ?_⟩, ?_⟩
    · show (e (e.symm (a, 1))).2 = 1
      simp
    · show (e (e.symm (a, 1))).1 = a
      simp
  let eP : ↥P ≃* A := MulEquiv.ofBijective g ⟨hginj, hgsurj⟩
  have hPcomp : IsComponent P :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv eP.symm
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hA).1, hPn.isSubnormal⟩
  have hlayer : layer X = P := by
    apply le_antisymm
    · apply sSup_le
      intro K hK
      have hperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hK.1.1
      rw [← hperf]
      rw [Subgroup.commutator_le]
      intro g₁ _ g₂ _
      show (e ⁅g₁, g₂⁆).2 = 1
      rw [map_commutatorElement]
      show ⁅(e g₁).2, (e g₂).2⁆ = 1
      exact commutatorElement_eq_one_iff_mul_comm.2 (hB _ _)
    · exact CFSG.LocalCores.component_le_layer hPcomp
  exact ⟨(MulEquiv.subgroupCongr hlayer).trans eP⟩

end LayerProd

section L2Facts

variable {F : Type} [Field F] [Finite F]

theorem l2_simple_nonab (h4 : 4 ≤ Nat.card F) :
    IsSimpleGroup (IVK.L2 F) ∧ ∃ a b : IVK.L2 F, a * b ≠ b * a := by
  have hs : ∃ s : Finset F, s.card = 4 := by
    have : Fintype F := Fintype.ofFinite F
    have hc : 4 ≤ (Finset.univ : Finset F).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
      exact h4
    obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq hc
    exact ⟨t, ht⟩
  have hsimple : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    (CFSG.LinearGroups.linear_projective_simple (K := F) (n := 2) le_rfl (Or.inr hs)).2.1
  have e : IVK.L2 F ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F := IVK.L2.equivPSL F
  have hperf : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    CFSG.LinearGroups.linear_projective_perfect (K := F) (n := 2) le_rfl (Or.inr hs)
  have hperf' : Group.IsPerfect (IVK.L2 F) :=
    Group.IsPerfect.ofSurjective (G := Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
      (G' := IVK.L2 F) (f := e.symm.toMonoidHom) e.symm.surjective
  have hs' : IsSimpleGroup (IVK.L2 F) := e.isSimpleGroup
  have : Nontrivial (IVK.L2 F) := hs'.toNontrivial
  refine ⟨hs', ?_⟩
  by_contra h
  push Not at h
  have hc : commutator (IVK.L2 F) = ⊥ := by
    rw [eq_bot_iff, commutator_def]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨a, -, b, -, rfl⟩
    show ⁅a, b⁆ = 1
    exact commutatorElement_eq_one_iff_mul_comm.2 (h a b)
  have h2 : commutator (IVK.L2 F) = ⊤ := hperf'.commutator_eq_top
  rw [hc] at h2
  obtain ⟨x, hx⟩ := exists_ne (1 : IVK.L2 F)
  have hxt : x ∈ (⊤ : Subgroup (IVK.L2 F)) := trivial
  rw [← h2] at hxt
  exact hx (Subgroup.mem_bot.1 hxt)

end L2Facts

section SwapB

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {q : ℕ}
  {L₁ L₂ : Subgroup (CentralizerBar z)}

omit [Finite G] in
theorem CL_eq_centralizer {t : G} (ht : t ∈ Cen z) (hprod : L₁ ⊔ L₂ = LBar z) :
    CL z t = centralizer ({toBar z ⟨t, ht⟩} : Set (CentralizerBar z)) ⊓ (L₁ ⊔ L₂) := by
  have hc : centralizer ((barOf z (zpowers t) : Subgroup (CentralizerBar z)) :
      Set (CentralizerBar z)) = centralizer ({toBar z ⟨t, ht⟩} : Set (CentralizerBar z)) := by
    ext x
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro h h' hh'
      rw [Set.mem_singleton_iff] at hh'
      rw [hh']
      exact h _ ⟨⟨t, ht⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers t), rfl⟩
    · intro h y hy
      obtain ⟨w, hw, rfl⟩ := hy
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_subgroupOf.1 hw)
      have hwk : w = (⟨t, ht⟩ : ↥(Cen z)) ^ k := Subtype.ext (by simpa using hk.symm)
      have hcomm : Commute (toBar z ⟨t, ht⟩) x := h _ rfl
      rw [hwk, map_zpow]
      exact (hcomm.zpow_left k).eq
  show LBar z ⊓ centralizer ((barOf z (zpowers t) : Subgroup (CentralizerBar z)) :
      Set (CentralizerBar z)) = _
  rw [hc, ← hprod, inf_comm]

theorem exists_CL_iso (hpair : Stage1Pair G z S q L₁ L₂) {t : G} (hsw : Swaps z t L₁ L₂)
    (ht2 : t * t = 1) : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ∧
      Nonempty (↥(CL z t) ≃* IVK.L2 F × Multiplicative (ZMod 2)) := by
  obtain ⟨ht, h1, h2⟩ := hsw
  set tb : CentralizerBar z := toBar z ⟨t, ht⟩ with htb
  have htb2 : tb * tb = 1 := by
    rw [htb, ← map_mul]
    have : (⟨t, ht⟩ : ↥(Cen z)) * ⟨t, ht⟩ = 1 := Subtype.ext ht2
    rw [this, map_one]
  have htbinv : tb⁻¹ = tb := inv_eq_of_mul_eq_one_right htb2
  have htb1 : tb ≠ 1 := by
    intro h
    apply hpair.ne
    rw [← h1]
    ext x
    rw [mem_conjugate_iff, h]
    simp
  have htord : orderOf tb = 2 := orderOf_eq_prime (by rwa [pow_two]) htb1
  have hP : IsPGroup 2 (zpowers tb) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, htord]; norm_num)
  obtain ⟨T, hT⟩ := hP.exists_le_sylow
  have htT : tb ∈ (T : Subgroup (CentralizerBar z)) := hT (Subgroup.mem_zpowers tb)
  obtain ⟨F₁, iF₁, fF₁, hF₁q, ⟨e₁⟩⟩ := hpair.sl₁
  obtain ⟨F₂, iF₂, fF₂, hF₂q, ⟨e₂⟩⟩ := hpair.sl₂
  have hnormal : (L₁ ⊔ L₂).Normal := by
    rw [hpair.prod.1]
    exact LBar_isNormal z
  have hcent : centralizer ((L₁ ⊔ L₂ : Subgroup (CentralizerBar z)) : Set (CentralizerBar z)) ≤
      L₁ ⊔ L₂ := by
    rw [hpair.prod.1, ← hpair.fitting]
    exact CFSG.centralizer_generalizedFitting_le _
  have hprodSL : IVK.ProdSL2 (CentralizerBar z) L₁ L₂ F₁ F₂ :=
    ⟨hpair.prod.2.1, ⟨e₁⟩, ⟨e₂⟩, hpair.prod.2.2, hnormal, hcent⟩
  obtain ⟨z₀, hz₀, hz₀1⟩ : ∃ z₀ ∈ L₁ ⊓ L₂, z₀ ≠ 1 := by
    have h2c := hpair.prod.2.2
    have hne : L₁ ⊓ L₂ ≠ ⊥ := by
      intro hbot
      rw [hbot] at h2c
      simp at h2c
    obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
    exact ⟨a, a.2, fun h => ha (Subtype.ext h)⟩
  have hK : L₁.map (MulAut.conj tb).toMonoidHom = L₂ := by
    have : conjugate L₁ tb = L₂ := h1
    rw [← this]
    show _ = L₁.map (MulAut.conj tb⁻¹).toMonoidHom
    rw [htbinv]
  obtain ⟨-, ⟨φ⟩⟩ :=
    IVK.ivk_3_1b F₁ F₂ (CentralizerBar z) L₁ L₂ hprodSL z₀ hz₀ hz₀1 T tb htT htord hK
  have hcl : CL z t = centralizer ({tb} : Set (CentralizerBar z)) ⊓ (L₁ ⊔ L₂) :=
    CL_eq_centralizer ht hpair.prod.1
  let e : ↥(CL z t) ≃* IVK.L2 F₁ × Multiplicative (ZMod 2) :=
    (MulEquiv.subgroupCongr hcl).trans φ
  exact ⟨F₁, iF₁, fF₁, hF₁q, ⟨e⟩⟩

theorem swap_b_of_pair (hpair : Stage1Pair G z S q L₁ L₂) {t : G} (hsw : Swaps z t L₁ L₂)
    (ht2 : t * t = 1) : IVK.IsL2 ↥(layer ↥(CL z t)) (fun r => r = q) := by
  obtain ⟨F, iF, fF, hFq, ⟨e⟩⟩ := exists_CL_iso hpair hsw ht2
  have h4 : 4 ≤ Nat.card F := by
    have := hpair.gt3
    omega
  obtain ⟨hs, hnc⟩ := l2_simple_nonab h4
  have := hs
  obtain ⟨eL⟩ := layer_equiv_of_prod (A := IVK.L2 F) (B := Multiplicative (ZMod 2)) hnc
    (fun a b => mul_comm a b) e
  exact ⟨F, iF, fF, hFq, ⟨eL⟩⟩

end SwapB

end CFSG.GH74.GLS.Stage1.Main
