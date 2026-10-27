module

public import CFSG.CGT.PushingUpLit.BHS7.QuotModuleU
public import CFSG.CGT.PushingUpLit.BHS7.OffenderModule
public import CFSG.CGT.PushingUpLit.BHS7.ModuleW

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

omit [Group Γ] in
theorem le_normalizer_inf_centralizer_opResidual [Group Γ] {P V : Subgroup Γ}
    (hPV : P ≤ Subgroup.normalizer (V : Set Γ)) :
    P ≤ Subgroup.normalizer
      ((V ⊓ Subgroup.centralizer (opResidual 2 P : Set Γ) : Subgroup Γ) : Set Γ) := fun _ hg =>
  Subgroup.inf_normalizer_le_normalizer_inf ⟨hPV hg,
    B6.le_normalizer_centralizer (le_normalizer_opResidual' P) hg⟩

section Finite

variable [Finite Γ] {P T M V W : Subgroup Γ}

theorem stabTrivSub_le_of_isModuleW (hmin : MinPar P T M) (hW : IsModuleW P T V W)
    (hPV : P ≤ Subgroup.normalizer (V : Set Γ)) :
    stabTrivSub P W (V ⊓ Subgroup.centralizer (opResidual 2 P : Set Γ))
      (le_normalizer_inf_centralizer_opResidual hPV) ≤ M := by
  set W₀ : Subgroup Γ := V ⊓ Subgroup.centralizer (opResidual 2 P : Set Γ) with hW₀def
  have hW₀ := le_normalizer_inf_centralizer_opResidual hPV
  set N : Subgroup Γ := stabTrivSub P W W₀ hW₀ with hN
  by_contra hNM
  have hNP : N ≤ P := fun x hx => hx.1
  have hNn := le_normalizer_stabTrivSub hW.normalized hW₀
  have h33 : opResidual 2 P ≤ N := three_three_b hmin.syl hmin.max hNP hNn hNM
  apply hW.ne_bot
  have hWW₀ : W ≤ W₀ := by
    rw [← hW.comm_eq, Subgroup.commutator_le]
    intro w hw k hk
    have h1 := (h33 hk).2 w hw
    have h2 : ⁅w, k⁆ = (k * w * k⁻¹ * w⁻¹)⁻¹ := by simp only [commutatorElement_def]; group
    rw [h2]
    exact W₀.inv_mem h1
  have : ⁅W, opResidual 2 P⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro w hw k hk
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.mp (hWW₀ hw).2 k hk).symm
  rw [← hW.comm_eq, this]


omit [Finite Γ] in
theorem coe_mem_pCoreOf_of_mem_pCoreOf_top {P : Subgroup Γ} [Finite Γ] {q : ↥P}
    (hq : q ∈ pCoreOf 2 (⊤ : Subgroup ↥P)) : (q : Γ) ∈ pCoreOf 2 P := by
  have hn : (pCoreOf 2 (⊤ : Subgroup ↥P)).Normal :=
    ⟨fun x hx g => (Subgroup.mem_normalizer_iff.1
      (le_normalizer_pCoreOf_self (⊤ : Subgroup ↥P) (Subgroup.mem_top g)) x).1 hx⟩
  have hN : (pCoreOf 2 (⊤ : Subgroup ↥P)).map P.subtype ≤ pCoreOf 2 P := by
    refine CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 _ _
      (Subgroup.map_subtype_le _) ?_
      ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _).map _)
    have h1 : ((pCoreOf 2 (⊤ : Subgroup ↥P)).map P.subtype).subgroupOf P =
        pCoreOf 2 (⊤ : Subgroup ↥P) :=
      Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
    rw [h1]
    exact hn
  exact hN ⟨q, hq, rfl⟩

theorem relIndex_pCoreOf_le_secFix (hV : IsElemAbelian 2 V)
    (hPV : P ≤ Subgroup.normalizer (V : Set Γ)) (hmin : MinPar P T M) (hW : IsModuleW P T V W)
    {B : Subgroup Γ} (hBT : B ≤ T)
    (hBe : @IsElemAbelian2 ↥V (commGroupOfElemAbelian hV) (autOn B V)) :
    (B ⊓ pCoreOf 2 P).relIndex B ≤
      (@secFix ↥V (commGroupOfElemAbelian hV) (autOn B V) (W.subgroupOf V)
        ((V ⊓ Subgroup.centralizer (opResidual 2 P : Set Γ)).subgroupOf V)).relIndex
        (W.subgroupOf V) := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hV
  have hV2 : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (by simpa [sq] using hV.2 v v.2)
  set W₀ : Subgroup Γ := V ⊓ Subgroup.centralizer (opResidual 2 P : Set Γ) with hW₀def
  have hW₀ := le_normalizer_inf_centralizer_opResidual hPV
  have hWV : W ≤ V := hW.le_V
  have hBP : B ≤ P := hBT.trans hmin.T_le
  set ψ : ↥P →* MulAut ↥V := actOn V P hPV with hψdef
  have hψ : ∀ g : ↥P, ψ g ∈ stabSub (W.subgroupOf V) ⊓ stabSub (W₀.subgroupOf V) := by
    intro g
    refine ⟨fun v => ?_, fun v => ?_⟩
    · show ((ψ g v : ↥V) : Γ) ∈ W ↔ (v : Γ) ∈ W
      rw [hψdef, actOn_apply_coe]
      exact (Subgroup.mem_normalizer_iff.mp (hW.normalized g.2) (v : Γ)).symm
    · show ((ψ g v : ↥V) : Γ) ∈ W₀ ↔ (v : Γ) ∈ W₀
      rw [hψdef, actOn_apply_coe]
      exact (Subgroup.mem_normalizer_iff.mp (hW₀ g.2) (v : Γ)).symm
  have hkerchar : ∀ g : ↥P, g ∈ (secActOf ψ hψ).ker ↔ (g : Γ) ∈ stabTrivSub P W W₀ hW₀ := by
    intro g
    rw [mem_ker_secActOf]
    constructor
    · intro h
      refine ⟨g.2, fun w hw => ?_⟩
      have h1 := h ⟨w, hWV hw⟩ (Subgroup.mem_subgroupOf.mpr hw)
      have h2 := Subgroup.mem_subgroupOf.mp h1
      rw [Subgroup.coe_mul, hψdef, actOn_apply_coe, Subgroup.coe_inv] at h2
      exact h2
    · intro h u hu
      refine Subgroup.mem_subgroupOf.mpr ?_
      rw [Subgroup.coe_mul, hψdef, actOn_apply_coe, Subgroup.coe_inv]
      exact h.2 u (Subgroup.mem_subgroupOf.mp hu)
  have hker : (secActOf ψ hψ).ker ⊓ ⊤ ≤ M.subgroupOf P := by
    intro g hg
    exact Subgroup.mem_subgroupOf.mpr
      (stabTrivSub_le_of_isModuleW hmin hW hPV ((hkerchar g).mp hg.1))
  have hpc : ∀ g : ↥P, (g : Γ) ∈ pCoreOf 2 P → g ∈ (secActOf ψ hψ).ker := by
    intro g hg
    rw [hkerchar]
    refine ⟨g.2, fun w hw => ?_⟩
    have h1 : ⁅w, (g : Γ)⁆ ∈ (⁅W, pCoreOf 2 P⁆ : Subgroup Γ) :=
      Subgroup.commutator_mem_commutator hw hg
    have h2 : (g : Γ) * w * (g : Γ)⁻¹ * w⁻¹ = ⁅w, (g : Γ)⁆⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [h2]
    exact W₀.inv_mem (hW.pCore_comm_le h1)
  have hO2 : pCoreOf 2 (⊤ : Subgroup ↥P) ≤ (secActOf ψ hψ).ker := fun q hq =>
    hpc q (coe_mem_pCoreOf_of_mem_pCoreOf_top hq)
  have hBe' : IsElemAbelian2 ((B.subgroupOf P).map ψ) := by
    rw [hψdef, ← autOn_eq_map_actOn hPV hBP]
    exact hBe
  have hmain := relIndex_ker_le_secFix hV2 ψ hψ hmin.subgroupOf_top hker hO2
    (fun g hg => hBT hg : B.subgroupOf P ≤ T.subgroupOf P) hBe'
  have hker' : (secActOf ψ hψ).ker ⊓ B.subgroupOf P = (B ⊓ pCoreOf 2 P).subgroupOf P := by
    ext g
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨hg, hgB⟩
      exact ⟨hgB, hW.cen_le g (hBT hgB) fun w hw => ((hkerchar g).mp hg).2 w hw⟩
    · rintro ⟨hgB, hgp⟩
      exact ⟨hpc g hgp, hgB⟩
  have h3 : Subgroup.map ψ (B.subgroupOf P) = autOn B V := by
    rw [hψdef]
    exact (autOn_eq_map_actOn hPV hBP).symm
  rw [hker', h3, Subgroup.relIndex_subgroupOf hBP] at hmain
  exact hmain

omit [Finite Γ] in
theorem centralizer_inf_le_pCoreOf_of_isModuleW (hW : IsModuleW P T V W) {t : Γ} (ht : t ∈ T)
    (htV : t ∈ Subgroup.centralizer (V : Set Γ)) : t ∈ pCoreOf 2 P := by
  refine hW.cen_le t ht fun w hw => ?_
  have h1 : t * w = w * t := (Subgroup.mem_centralizer_iff.mp htV w (hW.le_V hw)).symm
  have h2 : t * w * t⁻¹ * w⁻¹ = 1 := by rw [h1]; group
  rw [h2]
  exact Subgroup.one_mem _

omit [Finite Γ] in
theorem relIndex_autOn_pCoreOf (hPV : P ≤ Subgroup.normalizer (V : Set Γ)) (hmin : MinPar P T M)
    (hW : IsModuleW P T V W) {B : Subgroup Γ} (hBT : B ≤ T) :
    (autOn B V ⊓ autOn (pCoreOf 2 P) V).relIndex (autOn B V) =
      (B ⊓ pCoreOf 2 P).relIndex B := by
  have hBP : B ≤ P := hBT.trans hmin.T_le
  have hOP : pCoreOf 2 P ≤ P := CFSG.LieType.BorelTits.pCoreOf_le 2 P
  have hOT : pCoreOf 2 P ≤ T := (isSylowTwoOf_of_isSylowOf hmin.syl).pCoreOf_le
  set f : ↥P →* MulAut ↥V := actOn V P hPV with hf
  have h1 : autOn B V = (B.subgroupOf P).map f := autOn_eq_map_actOn hPV hBP
  have h2 : autOn (pCoreOf 2 P) V = ((pCoreOf 2 P).subgroupOf P).map f :=
    autOn_eq_map_actOn hPV hOP
  have h3 : (((pCoreOf 2 P).subgroupOf P).map f).comap f ⊓ B.subgroupOf P =
      (B ⊓ pCoreOf 2 P).subgroupOf P := by
    ext g
    simp only [Subgroup.mem_inf, Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨⟨x, hx, hxg⟩, hgB⟩
      refine ⟨hgB, ?_⟩
      have hker : g * x⁻¹ ∈ f.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, ← hxg, mul_inv_cancel]
      have hker' : g * x⁻¹ ∈ (P ⊓ Subgroup.centralizer (V : Set Γ)).subgroupOf P := by
        rw [← ker_actOn V P hPV]
        exact hker
      have hxT : (x : Γ) ∈ T := hOT hx
      have hgx : ((g * x⁻¹ : ↥P) : Γ) ∈ pCoreOf 2 P := by
        refine centralizer_inf_le_pCoreOf_of_isModuleW hW ?_ (Subgroup.mem_subgroupOf.mp hker').2
        exact T.mul_mem (hBT hgB) (T.inv_mem hxT)
      have := (pCoreOf 2 P).mul_mem hgx hx
      simpa using this
    · rintro ⟨hgB, hgp⟩
      exact ⟨⟨g, hgp, rfl⟩, hgB⟩
  rw [h1, h2, inf_comm, Subgroup.inf_relIndex_right, ← Subgroup.relIndex_comap,
    ← Subgroup.inf_relIndex_right, h3, Subgroup.relIndex_subgroupOf hBP]

end Finite

end CFSG.CGT.PushingUpLit.BHS7
