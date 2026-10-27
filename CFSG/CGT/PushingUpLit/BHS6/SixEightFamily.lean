module

public import CFSG.CGT.PushingUpLit.BHS6.SixEightType
public import CFSG.CGT.PushingUpLit.BHS6.SixEightPerm

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.G6 CFSG.QuasithinUnique
  CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

namespace AltSetup

variable {E : Subgroup Γ} {n : ℕ} {M : AltSetup E n} {p : Fin 3 → Fin n}

theorem isBTBlock_blockSub {G T : Subgroup Γ} (hEG : E ≤ G)
    (hBE : baum T ≤ Subgroup.normalizer (E : Set Γ))
    (hBW : baum T ≤ Subgroup.normalizer (M.W : Set Γ)) (S : ↥(baum T) →* Equiv.Perm (Fin n))
    (hS : ∀ (y : ↥(baum T)) (w : ↥M.W) (hw : (y : Γ) * w * (y : Γ)⁻¹ ∈ M.W),
      M.βe ⟨(y : Γ) * w * (y : Γ)⁻¹, hw⟩ = coreAct n (S y) (M.βe w))
    (hSd : ∀ y : ↥(baum T), S y ∈ Subgroup.normalizer
      (Subgroup.zpowers (triCyc p) : Set (Equiv.Perm (Fin n))))
    (hp : Function.Injective p) {g : ↥E} (hg3 : g ^ 3 = 1) (hgd : M.Ψ g = triCyc p)
    (hy₀ : ∃ y₀ : ↥(baum T), S y₀ = Equiv.swap (p 0) (p 2))
    (hnot : ¬ M.blockSub p g ≤ cStarIn G T) : IsBTBlock G T (M.blockSub p g) where
  le := (blockSub_le_E hp hgd).trans hEG
  residual := oResidualTwo_eq_top_of_opResidual (opResidual_blockSub hp hg3 hgd)
  commutator := commutator_blockSub_eq hBE hBW S hS hSd hp hg3 hgd hy₀
  perfect := by
    rw [pCoreOf_blockSub hp hg3 hgd]
    exact commutator_wSub_blockSub hp hgd
  elemAbelian := by
    rw [pCoreOf_blockSub hp hg3 hgd]
    exact ⟨fun x hx y hy => M.hWab x (M.wSub_le_W hx) y (M.wSub_le_W hy),
      fun x hx => sq_eq_one_of_mem_W (M.wSub_le_W hx)⟩
  nonCentral := by
    intro h
    apply hnot
    intro f hf
    refine centralizer_le_cStarIn G T (Subgroup.mem_inf.2 ⟨hEG (blockSub_le_E hp hgd hf), ?_⟩)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have h1 : ⁅f, z⁆ ∈ ⁅M.blockSub p g, omegaOneCenterOf T⁆ :=
      Subgroup.commutator_mem_commutator hf hz
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  type := Or.inr ⟨1, le_rfl, isNaturalAltModule_blockSub hp hg3 hgd⟩

theorem exists_block_or_mem_cStar {G T : Subgroup Γ} (hEG : E ≤ G)
    (hBE : baum T ≤ Subgroup.normalizer (E : Set Γ))
    (hBW : baum T ≤ Subgroup.normalizer (M.W : Set Γ)) (S : ↥(baum T) →* Equiv.Perm (Fin n))
    (hS : ∀ (y : ↥(baum T)) (w : ↥M.W) (hw : (y : Γ) * w * (y : Γ)⁻¹ ∈ M.W),
      M.βe ⟨(y : Γ) * w * (y : Γ)⁻¹, hw⟩ = coreAct n (S y) (M.βe w))
    {T' : Set (Equiv.Perm (Fin n))} (hs : ∀ t ∈ T', t.IsSwap)
    (hc : ∀ t ∈ T', ∀ t' ∈ T', t * t' = t' * t)
    (hSY : ∀ y : ↥(baum T), S y ∈ Subgroup.closure T')
    (hy₀ : ∀ t ∈ T', ∃ y₀ : ↥(baum T), S y₀ = t)
    (hsurj : ∀ π ∈ alternatingGroup (Fin n), ∃ e : ↥E, M.Ψ e = π)
    {t : Equiv.Perm (Fin n)} (ht : t ∈ T') {x : Fin n} (hx : t x ≠ x) {c : Fin n}
    (hcfix : ∀ t ∈ T', t c = c) :
    (∃ F : Subgroup Γ, IsBTBlock G T F ∧ F ≤ E ∧ ¬ F ≤ cStarIn G T ∧
        IsNaturalAltModule ↥F 1) ∨
      ∃ g : ↥E, (g : Γ) ∈ cStarIn G T ∧ M.Ψ g = cyc x (t x) c := by
  have e1 : t = Equiv.swap x (t x) := eq_swap_of_isSwap_apply_ne (hs t ht) hx
  have hy : t (t x) = x := by
    have := congrArg (fun σ : Equiv.Perm (Fin n) => σ (t x)) e1
    simpa using this
  have hxy : x ≠ t x := hx.symm
  have hxc : x ≠ c := fun h => hx (h ▸ hcfix t ht)
  have hyc : t x ≠ c := fun h => hxc (by
    have h1 := hcfix t ht
    rw [← h, hy] at h1
    exact h1.trans h)
  obtain ⟨p, hp, hp0, hp1, hp2⟩ := exists_tri hxc hxy hyc.symm
  have hd : triCyc p = cyc x (t x) c := by
    rw [triCyc, hp0, hp1, hp2]
  obtain ⟨e₀, he₀⟩ := hsurj (cyc x (t x) c) (cyc_mem_alternatingGroup hxy hxc hyc)
  obtain ⟨g, hg3, hgd⟩ := M.exists_lift_cube_one (triCyc_isThreeCycle hp) (by
    rw [hd]
    exact he₀)
  by_cases hF : M.blockSub p g ≤ cStarIn G T
  · right
    exact ⟨g, hF g_mem_blockSub, hgd.trans hd⟩
  · left
    have hSd : ∀ y : ↥(baum T), S y ∈ Subgroup.normalizer
        (Subgroup.zpowers (triCyc p) : Set (Equiv.Perm (Fin n))) := fun y => by
      rw [hd]
      exact closure_le_normalizer_zpowers_cyc hs hc ht hx hcfix (hSY y)
    have hy₀' : ∃ y₀ : ↥(baum T), S y₀ = Equiv.swap (p 0) (p 2) := by
      obtain ⟨y₀, hy₀t⟩ := hy₀ t ht
      refine ⟨y₀, ?_⟩
      rw [hp0, hp2, hy₀t]
      exact e1
    exact ⟨M.blockSub p g, isBTBlock_blockSub hEG hBE hBW S hS hSd hp hg3 hgd hy₀' hF,
      blockSub_le_E hp hgd, hF, isNaturalAltModule_blockSub hp hg3 hgd⟩

end AltSetup

end CFSG.CGT.PushingUpLit.BHS6
