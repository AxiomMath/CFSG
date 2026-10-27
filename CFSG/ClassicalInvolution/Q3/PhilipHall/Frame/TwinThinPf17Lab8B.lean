module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf17Lab8Pair
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf9Conj

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

set_option linter.unusedSectionVars false

namespace TwinThin

variable {G : Type} [Group G] [Finite G] {K₀ K K' : Subgroup G} {z : G} {π : Set (Subgroup G)}
  {g : G}

theorem lab8_map_conjX {P : Set (Subgroup G)} {n : ℕ} (I : AEIdent P n) (s : G) (L : Subgroup G) :
    ((conjSub s L).subgroupOf (pSpan (conjSub s '' P))).map (I.conjX s).φ =
      (L.subgroupOf (pSpan P)).map I.φ := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(pSpanConj s P).symm y, ?_, (I.conjXHom_apply s y).symm⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, pSpanConj_symm_apply]
    exact mem_conjSub_iff.mp (Subgroup.mem_subgroupOf.mp hy)
  · rintro ⟨w, hw, rfl⟩
    refine ⟨pSpanConj s P w, ?_, I.conjXHom_apply_conj s w⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, pSpanConj_apply]
    exact conj_mem_conjSub (Subgroup.mem_subgroupOf.mp hw)

namespace Setting

variable (S : Setting K₀ K K' z π g)
include S

theorem lab8_false_of_caseB (J : AEIdent (fam K (conjSub g (piGen π))) 8)
    {α : Finset (Fin 8)} {h : α.card = 4} {b : Bool}
    (hlab : (K.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ = AE.memBar α h b)
    {M : Subgroup G} (hMF : M ∈ fam K (conjSub g (piGen π))) (hMπ : M ∈ π)
    (hlabM : (M.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ = AE.memBar α h (!b))
    {γ : Finset (Fin 8)} (hγ : γ.card = 4) (hγα : Disjoint γ α) {c : Bool}
    (hlab' : (K'.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ =
      AE.memBar γ hγ c) : False := by
  classical
  have hn : 5 ≤ 8 := by norm_num
  have hΩ : HypOmegaGen (CoreAssembly.conjClass K₀) := S.hs.hyp
  obtain ⟨y, hyφ, ⟨a3, hya3⟩, hyz, hyN0⟩ := S.exists_y hn J hlab
  have hyX' : (y : G) ∈ conjSub g (piGen π) := (SetLike.ext_iff.mp S.fam_gen (y : G)).mp y.2
  have hyC : (y : G) ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hyz
  have hyKg : ∀ l ∈ conjSub g K, (y : G) * l = l * (y : G) := by
    intro l hl
    have := (S.hos.conj_le_inf_centralizer S.hπ S.hg hl).2
    exact (Subgroup.mem_centralizer_iff.mp this) (y : G) hyX'
  have hmax1 : MaxAdj (nbrAdj (CoreAssembly.conjClass K₀)) K (conjSub g K) :=
    maxAdj_of_mem_maxOrb S.hos.graph S.hπ S.hg
  have hmax2 : MaxAdj (nbrAdj (CoreAssembly.conjClass K₀)) (conjSub g K) K :=
    maxAdj_of_mem_maxOrb S.hos.graph (isMaxOrb_conj S.hos.graph S.hπ g)
      (S.hos.mem_conj_image_of_mem S.hπ S.hg)
  obtain ⟨s, hs1, hs2⟩ := exists_conj_maxAdj S.hos.graph hmax1 hmax2
  have hPs : conjSub s '' fam K (conjSub g (piGen π)) = π := by
    rw [S.lab8_fam_eq]
    have h1 : conjSub s '' (conjSub g '' π) ∈ maxOrbs (nbrAdj (CoreAssembly.conjClass K₀)) K := by
      rw [← hs2]
      exact isMaxOrb_conj S.hos.graph (isMaxOrb_conj S.hos.graph S.hπ g) s
    exact maxOrb_unique S.hos.graph S.hK h1 S.hπ
  set P : Set (Subgroup G) := conjSub s '' fam K (conjSub g (piGen π))
  set Js : AEIdent P 8 := J.conjX s
  have hpSpanP : pSpan P = piGen π := by rw [hPs]; rfl
  have hyN : (y : G) ∈ Subgroup.normalizer ((pSpan P : Subgroup G) : Set G) := by
    rw [hpSpanP]; exact hyN0
  have hOX : classicalInvolutionOddCore ↥(pSpan P) = ⊥ :=
    classicalInvolutionOddCore_eq_bot_of_mulEquiv (pSpanConj s _) S.hOdd
  have hk2 : IsPGroup 2 Js.φ.ker := Js.isPGroup_ker hOX
  have hPΩ : P ⊆ CoreAssembly.conjClass K₀ := by
    rw [hPs]; exact fun L hL => S.mem_of_mem_pi hL
  have haP : ∀ L ∈ P, conjSub (y : G) L ∈ P := by
    rw [hPs]; exact fun L hL => S.conj_pi_of_cent hyC hL
  have hlabKs : ((conjSub s K).subgroupOf (pSpan P)).map Js.φ = AE.memBar α h b :=
    (lab8_map_conjX J s K).trans hlab
  have hlabK's : ((conjSub s K').subgroupOf (pSpan P)).map Js.φ = AE.memBar γ hγ c :=
    (lab8_map_conjX J s K').trans hlab'
  have hyKs : ∀ l ∈ conjSub s K, (y : G) * l = l * (y : G) := by
    rw [hs1]; exact hyKg
  have htw : conjSub s K' ∈ twinSet (CoreAssembly.conjClass K₀) (conjSub g K) := by
    obtain ⟨-, z', hz'K, hz'K'⟩ := S.hK'
    refine ⟨S.hos.graph.conjMem K' S.hK'.1 s, s * z' * s⁻¹, ?_, hz'K'.conj s⟩
    have := hz'K.conj s
    rwa [hs1] at this
  have hyK's : ∀ l ∈ conjSub s K', (y : G) * l = l * (y : G) := by
    intro l hl
    have hβ := S.hos.twinSet_subset_beta (isMaxOrb_conj S.hos.graph S.hπ g) (S.hH1.conj g) htw
    have hcen := S.hos.beta_le_centralizer hβ
    rw [piGen_conj] at hcen
    exact (Subgroup.mem_centralizer_iff.mp (hcen hl)) (y : G) hyX'
  set θ := Js.inducedAut hn hyN
  have hya3' : (y : G) ^ 3 ^ a3 = 1 := by
    have := congrArg Subtype.val hya3
    simpa using this
  have hθ3 : θ ^ 3 ^ a3 = 1 := Js.inducedAut_pow_eq_one hn hyN hya3'
  have hγc : γ = αᶜ := TwinThinPf17Lab8.eq_compl_of_disjoint h hγ hγα
  have hθ1 : θ = 1 := by
    refine aut_eq_one_of_cent hn (by norm_num) θ ⟨a3, hθ3⟩ h (b₀ := b) ?_ ?_
    · intro x hx
      exact Js.inducedAut_fix_of_comm hn hyN hyKs x (by rw [hlabKs]; exact hx) _
    · intro β hβ hd
      have hβc : β = αᶜ := TwinThinPf17Lab8.eq_compl_of_disjoint h hβ hd
      have hβγ : β = γ := hβc.trans hγc.symm
      subst hβγ
      refine ⟨c, fun x hx => ?_⟩
      exact Js.inducedAut_fix_of_comm hn hyN hyK's x (by rw [hlabK's]; exact hx) _
  have hcentP : ∀ x ∈ pSpan P, (y : G) * x = x * (y : G) :=
    Js.comm_of_inducedAut_eq_one hΩ S.hs.two S.card8 hPΩ hn hk2 hyN haP hθ1
  have hyM : ∀ k ∈ M, k * (y : G) = (y : G) * k := fun k hk' =>
    (hcentP k (by rw [hpSpanP]; exact le_piGen hMπ hk')).symm
  obtain ⟨x, hx, hxne⟩ := AE.yBar_not_comm_memBar hn α h (!b)
  rw [← hlabM] at hx
  have hxy := lab8_map_comm J hMF y.2 hyM hx
  exact hxne (by rw [← hyφ]; exact hxy.symm)

end Setting

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
