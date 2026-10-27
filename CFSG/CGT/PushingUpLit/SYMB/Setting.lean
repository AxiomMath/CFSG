module

public import CFSG.CGT.PushingUpLit.BHS6.SymAssemblyBlock
public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalSymplecticSix
public import CFSG.CGT.PushingUpLit.BHS6.SymAssembly

public section

namespace CFSG.CGT.PushingUpLit.SYMB

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.G6 CFSG.QuasithinUnique
  CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS
  CFSG.CGT.PushingUpLit.BHS6 CFSG.CGT.PushingUpLit.BHS7
open scoped commutatorElement

variable {Γ : Type} [Group Γ] {G T V : Subgroup Γ} {n : ℕ} {φ : ↥G →* Equiv.Perm (Fin n)}
  {ψ : ↥V →* ↥(coreMod n)} {T' : Set (Equiv.Perm (Fin n))}

theorem sym_ker_le_cStarIn (S : SymSetting G T V n φ ψ T') : kerG G φ ≤ cStarIn G T := by
  intro g hg
  obtain ⟨hgG, hg1⟩ := mem_kerG.1 hg
  have h2 : (⟨g, hgG⟩ : ↥G) ∈ φ.ker := hg1
  rw [S.data.φ_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at h2
  exact centralizer_le_cStarIn G T ⟨hgG, Subgroup.centralizer_le S.vT h2.2⟩

theorem sym_baum_ne_bot (S : SymSetting G T V n φ ψ T') : baum T ≠ ⊥ := by
  intro h0
  obtain ⟨t, ht⟩ := S.nonempty
  have h1 : t ∈ imgG G φ (baum T) := by
    rw [S.baum]
    exact Subgroup.subset_closure ht
  obtain ⟨g, hg, hgB, hgt⟩ := mem_imgG.1 h1
  rw [h0, Subgroup.mem_bot] at hgB
  subst hgB
  have h1' : (⟨(1 : Γ), hg⟩ : ↥G) = 1 := rfl
  rw [h1', map_one] at hgt
  obtain ⟨a, b, hab, rfl⟩ := S.swaps _ ht
  have := congrArg (fun f : Equiv.Perm (Fin n) => f a) hgt
  simp only [Equiv.swap_apply_left, Equiv.Perm.one_apply] at this
  exact hab this

theorem sym_T_le_cStarIn (S : SymSetting G T V n φ ψ T') : T ≤ cStarIn G T := fun _ ht =>
  inf_normalizer_baum_le_cStarIn (sym_baum_ne_bot S)
    ⟨S.sylow.1 ht, normalizer_le_normalizer_baum T (Subgroup.le_normalizer ht)⟩

theorem sym_not_alt_le_imgG (S : SymSetting G T V n φ ψ T') {X : Subgroup Γ}
    (hX : X ≤ cStarIn G T) : ¬ alternatingGroup (Fin n) ≤ imgG G φ X := by
  classical
  intro hA
  obtain ⟨t, ht⟩ := S.nonempty
  have htB : t ∈ imgG G φ (baum T) := by
    rw [S.baum]
    exact Subgroup.subset_closure ht
  obtain ⟨b, hbG, hbB, hbt⟩ := mem_imgG.1 htB
  have hbC : b ∈ cStarIn G T := sym_T_le_cStarIn S ((inf_le_left : baum T ≤ T) hbB)
  have hodd : Equiv.Perm.sign t = -1 := by
    obtain ⟨a, a', haa, rfl⟩ := S.swaps t ht
    exact Equiv.Perm.sign_swap haa
  have hCtop : imgG G φ (cStarIn G T) = ⊤ :=
    eq_top_of_alt_le_of_odd (hA.trans (imgG_mono G φ hX)) (mem_imgG.2 ⟨b, hbG, hbC, hbt⟩) hodd
  apply S.ne
  refine le_antisymm (cStarIn_le G T) fun g hg => ?_
  have hmem : φ ⟨g, hg⟩ ∈ imgG G φ (cStarIn G T) := by
    rw [hCtop]
    trivial
  obtain ⟨c, hcG, hcC, hcφ⟩ := mem_imgG.1 hmem
  have hker : c⁻¹ * g ∈ kerG G φ := by
    refine mem_kerG.2 ⟨G.mul_mem (G.inv_mem hcG) hg, ?_⟩
    have e : (⟨c⁻¹ * g, G.mul_mem (G.inv_mem hcG) hg⟩ : ↥G) = ⟨c, hcG⟩⁻¹ * ⟨g, hg⟩ := rfl
    rw [e, map_mul, map_inv, hcφ]
    simp
  have := (cStarIn G T).mul_mem hcC (sym_ker_le_cStarIn S hker)
  simpa using this

variable [Finite Γ]

theorem sym_omegaOneCenter_baum_le_ker (S : SymSetting G T V n φ ψ T') (h4 : 4 ≤ n) :
    omegaOneCenterOf (baum T) ≤ kerG G φ := by
  classical
  obtain ⟨𝓔, h𝓔⟩ := exists_symCover S
  have hcomm := h𝓔.comm_le S.data.normal
  have hAn := h𝓔.img_eq_alt S.odd S.swaps S.comm S.nonempty
  intro z hz
  have hzB : z ∈ baum T := C1GN.omegaOneCenterOf_le_self _ hz
  have hzG : z ∈ G := S.sylow.1 ((inf_le_left : baum T ≤ T) hzB)
  refine mem_kerG.2 ⟨hzG, ?_⟩
  have hVG : V ≤ G := (S.vQ.trans (C1GN.omegaOneCenterOf_le_self _)).trans
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 G)
  have hker : ∀ v : Γ, v ∈ V → ∀ hv : v ∈ G, φ ⟨v, hv⟩ = 1 := by
    intro v hv hvG
    have h1 : (⟨v, hvG⟩ : ↥G) ∈ φ.ker := by
      rw [S.data.φ_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨hvG, mem_centralizer_of_mem S.data.elemAbelian hv⟩
    exact h1
  have hcent : φ ⟨z, hzG⟩ ∈
      Subgroup.centralizer (alternatingGroup (Fin n) : Set (Equiv.Perm (Fin n))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rw [← hAn] at ha
    obtain ⟨e, heG, heE, rfl⟩ := mem_imgG.1 ha
    have hc : ⁅e, z⁆ ∈ V := hcomm (Subgroup.commutator_mem_commutator heE hz)
    have hcG : ⁅e, z⁆ ∈ G := hVG hc
    have h1 : φ ⟨⁅e, z⁆, hcG⟩ = 1 := hker _ hc hcG
    have e1 : (⟨⁅e, z⁆, hcG⟩ : ↥G) = ⟨e, heG⟩ * ⟨z, hzG⟩ * ⟨e, heG⟩⁻¹ * ⟨z, hzG⟩⁻¹ := rfl
    rw [e1, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h1)
  rw [CFSG.ComponentClassification.PresentationLocal.centralizer_alternatingGroup_eq_bot
    (by simpa using h4)] at hcent
  exact Subgroup.mem_bot.1 hcent

end CFSG.CGT.PushingUpLit.SYMB
