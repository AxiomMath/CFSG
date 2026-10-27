module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPfCent
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf3Cent

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3.AE

set_option linter.unusedSectionVars false

namespace TwinThin

variable {G : Type} [Group G] [Finite G] {K₀ K K' : Subgroup G} {z : G} {π : Set (Subgroup G)}
  {g : G}

namespace Setting

variable (S : Setting K₀ K K' z π g)
include S

theorem pi_maxOrb_twin : π ∈ maxOrbs (nbrAdj (CoreAssembly.conjClass K₀)) K' :=
  (mem_betaOf_iff S.hos.graph S.hK S.hπ).mp (S.hos.twinSet_subset_beta S.hπ S.hH1 S.hK')

theorem twin_conj_mem_pi : conjSub g K' ∈ π := by
  obtain ⟨a, ha, haK⟩ := TwinSecXg.twin_conj S.hos S.hK S.hπ S.hH1 S.conj_inv_mem S.hK'
  have hx : g * a * g⁻¹ ∈ piGen π := by
    have := mem_conjSub_iff.mp ha
    simpa using this
  have h : conjSub g K' = conjSub (g * a * g⁻¹) (conjSub g K) := by
    rw [← haK, ← conjSub_mul, ← conjSub_mul]
    congr 1
    group
  rw [h]
  exact stable_of_maxOrb S.hos.graph S.hπ _ hx _ S.hg

theorem mem_Q_of_mem_pi {J : Subgroup G} (hJ : J ∈ π) :
    J ∈ conjSub g⁻¹ '' fam K (conjSub g (piGen π)) := by
  obtain ⟨a, ha, hKa⟩ := transitive_of_maxOrb S.hos.graph S.hπ _ S.conj_inv_mem _ hJ
  refine ⟨conjSub (g * a * g⁻¹) K, mem_fam ?_, ?_⟩
  · have ha' : a ∈ piGen π := ha
    rw [mem_conjSub_iff]
    simpa [mul_assoc] using ha'
  · rw [← conjSub_mul, show g⁻¹ * (g * a * g⁻¹) = a * g⁻¹ by group, conjSub_mul]
    exact hKa

theorem twin_le_cent : conjSub g K' ≤ piGen π ⊓ Subgroup.centralizer (conjSub g (piGen π) : Set G) :=
  S.hos.conj_le_inf_centralizer S.pi_maxOrb_twin S.twin_conj_mem_pi

theorem twin_inv : IsUniqueInvolution (conjSub g K') (g * z * g⁻¹) := by
  obtain ⟨-, z', hz'K, hz'K'⟩ := S.hK'
  have : z' = z := (S.hz.eq hz'K).symm
  rw [this] at hz'K'
  exact hz'K'.conj g

theorem twin_conj_ne : conjSub g K ≠ conjSub g K' := by
  intro h
  have h2 := congrArg (conjSub g⁻¹) h
  rw [conjSub_inv_conjSub, conjSub_inv_conjSub] at h2
  exact S.hne h2.symm


theorem twin_images_ne {m : ℕ} {𝒜 : Set (Finset (Fin m))} {H : Subgroup (AEQ m)}
    (hS : IsSimpleGroup ↥(genFittingFStar G)) (hnab : ∃ a b : ↥(genFittingFStar G), a * b ≠ b * a)
    (J : AEIdentOn (conjSub g⁻¹ '' fam K (conjSub g (piGen π))) m 𝒜 H) :
    ((conjSub g K).subgroupOf (pSpan (conjSub g⁻¹ '' fam K (conjSub g (piGen π))))).map J.φ ≠
      ((conjSub g K').subgroupOf (pSpan (conjSub g⁻¹ '' fam K (conjSub g (piGen π))))).map J.φ := by
  have hZ : Subgroup.center G = ⊥ := InductionBridge.center_eq_bot_of_fstar_simple hS hnab
  have hgen : (⨆ M ∈ π ∪ conjSub g '' π, M) = ⊤ :=
    (graph_17_10 S.hos.graph S.hK S.hπ).generate (iSup_conjClass_eq_top S.hs.gen) g S.hg
  have hPQ : pSpan (conjSub g⁻¹ '' fam K (conjSub g (piGen π))) = piGen π := S.pSpan_conj_fam
  have hKl := S.hos.conj_le_inf_centralizer S.hπ S.hg
  have hKl' := S.twin_le_cent
  have key : ∀ A B : Subgroup G,
      A ≤ piGen π ⊓ Subgroup.centralizer (conjSub g (piGen π) : Set G) →
      B ≤ piGen π ⊓ Subgroup.centralizer (conjSub g (piGen π) : Set G) →
      (A.subgroupOf (pSpan (conjSub g⁻¹ '' fam K (conjSub g (piGen π))))).map J.φ ≤
        (B.subgroupOf (pSpan (conjSub g⁻¹ '' fam K (conjSub g (piGen π))))).map J.φ → A ≤ B := by
    intro A B hA hB hAB l hl
    have hlX : l ∈ pSpan (conjSub g⁻¹ '' fam K (conjSub g (piGen π))) := by
      rw [hPQ]; exact (hA hl).1
    have hmem : J.φ ⟨l, hlX⟩ ∈
        (B.subgroupOf (pSpan (conjSub g⁻¹ '' fam K (conjSub g (piGen π))))).map J.φ :=
      hAB ⟨⟨l, hlX⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
    obtain ⟨b, hb, hbe⟩ := hmem
    have hbB : (b : G) ∈ B := Subgroup.mem_subgroupOf.mp hb
    have hker : (⟨l, hlX⟩ : ↥(pSpan (conjSub g⁻¹ '' fam K (conjSub g (piGen π)))))⁻¹ * b ∈
        J.φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hbe, inv_mul_cancel]
    have hcen := J.ker_le hker
    have hcX : ∀ x ∈ piGen π, x * (l⁻¹ * (b : G)) = (l⁻¹ * (b : G)) * x := by
      intro x hx
      have hxQ : x ∈ pSpan (conjSub g⁻¹ '' fam K (conjSub g (piGen π))) := by rw [hPQ]; exact hx
      have := Subgroup.mem_center_iff.mp hcen ⟨x, hxQ⟩
      have h2 := congrArg Subtype.val this
      simpa using h2
    have hcXg : ∀ x ∈ conjSub g (piGen π), x * (l⁻¹ * (b : G)) = (l⁻¹ * (b : G)) * x := by
      intro x hx
      have h1 : x * l = l * x := Subgroup.mem_centralizer_iff.mp (hA hl).2 x hx
      have h2 : x * (b : G) = (b : G) * x := Subgroup.mem_centralizer_iff.mp (hB hbB).2 x hx
      have h3 : x * l⁻¹ = l⁻¹ * x := by
        calc x * l⁻¹ = l⁻¹ * (l * x) * l⁻¹ := by group
          _ = l⁻¹ * (x * l) * l⁻¹ := by rw [h1]
          _ = l⁻¹ * x := by group
      calc x * (l⁻¹ * (b : G)) = (x * l⁻¹) * b := by group
        _ = l⁻¹ * (x * b) := by rw [h3]; group
        _ = l⁻¹ * (b * x) := by rw [h2]
        _ = (l⁻¹ * (b : G)) * x := by group
    have hle : (⨆ M ∈ π ∪ conjSub g '' π, M) ≤
        Subgroup.centralizer ({l⁻¹ * (b : G)} : Set G) := by
      refine iSup₂_le fun M hM => ?_
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      rcases hM with hM | ⟨M₀, hM₀, rfl⟩
      · exact (hcX x (le_piGen hM hx)).symm
      · have hM' : conjSub g M₀ ≤ conjSub g (piGen π) := by
          rw [← piGen_conj]
          exact le_piGen ⟨M₀, hM₀, rfl⟩
        exact (hcXg x (hM' hx)).symm
    have hcG : l⁻¹ * (b : G) ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro x
      have hx : x ∈ (⨆ M ∈ π ∪ conjSub g '' π, M) := by rw [hgen]; exact Subgroup.mem_top x
      have := Subgroup.mem_centralizer_iff.mp (hle hx) (l⁻¹ * (b : G)) (Set.mem_singleton _)
      exact this.symm
    rw [hZ, Subgroup.mem_bot] at hcG
    have : l = (b : G) := inv_mul_eq_one.mp hcG
    rw [this]
    exact hbB
  intro heq
  have h1 := key _ _ hKl hKl' heq.le
  have h2 := key _ _ hKl' hKl heq.ge
  exact S.twin_conj_ne (le_antisymm h1 h2)

theorem centralizes_of_three_e29 (hS : IsSimpleGroup ↥(genFittingFStar G))
    (hnab : ∃ a b : ↥(genFittingFStar G), a * b ≠ b * a)
    (I : AEIdentOn (fam K (conjSub g (piGen π))) 8 AE.e29Sets AE.e29Sub) {y : G}
    (hyX' : y ∈ conjSub g (piGen π)) (hyz : y * z = z * y) (hy3 : ∃ a : ℕ, y ^ 3 ^ a = 1) :
    ∀ x ∈ piGen π, y * x = x * y := by
  have hyN : y ∈ Subgroup.normalizer (pSpan (conjSub g⁻¹ '' fam K (conjSub g (piGen π))) :
      Set G) := by
    rw [S.pSpan_conj_fam]
    exact S.hos.centralizer_le_normalizer_piGen S.hK S.hπ S.hH1 S.hz
      (Subgroup.mem_centralizer_singleton_iff.mpr hyz)
  have hyL : ∀ l ∈ conjSub g K, y * l = l * y := by
    intro l hl
    have := (S.hos.conj_le_inf_centralizer S.hπ S.hg hl).2
    exact (Subgroup.mem_centralizer_iff.mp this) y hyX'
  have hyL' : ∀ l ∈ conjSub g K', y * l = l * y := by
    intro l hl
    have := (S.twin_le_cent hl).2
    exact (Subgroup.mem_centralizer_iff.mp this) y hyX'
  have J := I.conj g⁻¹
  have := TwinThinPf.centralizes_of_e29_pair J hyN hy3 S.conj_mem_image
    (S.mem_Q_of_mem_pi S.twin_conj_mem_pi) (S.card8 _ (S.hos.graph.conjMem K S.hK g))
    (S.card8 _ (S.hos.graph.conjMem K' S.hK'.1 g)) (S.hz.conj g) S.twin_inv
    (S.twin_images_ne hS hnab J) hyL hyL' (S.trans_conj_fam _ S.conj_mem_image)
  rw [S.pSpan_conj_fam] at this
  exact this

end Setting

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
