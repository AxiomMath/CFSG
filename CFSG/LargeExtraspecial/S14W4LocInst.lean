module

public import CFSG.LargeExtraspecial.S14W4SetInst
public import CFSG.LargeExtraspecial.S14W4LocB3
public import CFSG.LargeExtraspecial.O62Rank

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial.S4 CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] [Finite G]

namespace W4Hyp

variable {S : Setting G} {g : G} {t : S.O} {c : Config} (h : W4Hyp S g t c)
include h

theorem act : W4Loc.Act h.S₀ h.R₀ h.π where
  R_le_M := h.R₀_le_M
  conj_mem := fun k _ hr => h.conj_mem_R₀ k.2 hr
  Q_le_ker := h.Q_le_ker_π
  ker_R := fun r hr h1 => (show ι S r ∈ Nbar S g t from ⟨hr, (h.π_eq_one_iff r).mp h1⟩)

theorem lat [IsSimpleGroup G] (hNQ : NQIrredStmt) (hNQ6 : NQPlus6Stmt) :
    W4Loc.Lat h.S₀ h.R₀ := by
  rcases h.hc with hm | hp
  · exact Or.inl (h.irr hNQ hm)
  · exact Or.inr (h.lattice hNQ6 hp)

theorem card_Qt : Nat.card h.S₀.Qt = 2 ^ 8 := by
  rw [h.S₀.card_Qt, h.S₀.finrank_Qt_eq_two_mul_width, h.width_S₀]

theorem rnOmega : RNOmega S g t 6 := by
  rcases h.hc with hm | hp
  · exact (hm ▸ h.occ : Config.omegaMinus6.Occurs S g t).1.1
  · exact (hp ▸ h.occ : Config.omegaPlus6.Occurs S g t).1.1

theorem exists_form : ∃ (q : QuadraticForm (ZMod 2) (Vt S g t))
    (hq : q.polarBilin.Nondegenerate), RmodN S g t = omegaGroup q hq ∧
      finrank (ZMod 2) (Vt S g t) = 6 ∧ (c = .omegaMinus6 → ¬ O62.IsPlus q) := by
  obtain ⟨H, C, ht, ht1, hVQ, hO, hfin⟩ := h.rnOmega
  obtain ⟨q, hq, -, hR, -, horb⟩ := hO.exists_form
  refine ⟨q, hq, hR, hfin, fun hm hplus => ?_⟩
  have hnp : ¬ RNPlus S g t := (hm ▸ h.occ : Config.omegaMinus6.Occurs S g t).1.2
  obtain ⟨W, hW, hW0⟩ := hplus
  exact hnp ⟨ht, W, hfin ▸ hW, fun w hw hw0 => (horb w hw0).mp (hW0 w hw)⟩

omit h in
noncomputable def qf (h : W4Hyp S g t c) : QuadraticForm (ZMod 2) (Vt S g t) :=
  h.exists_form.choose

theorem qf_nondeg : h.qf.polarBilin.Nondegenerate := h.exists_form.choose_spec.choose

theorem RmodN_eq : RmodN S g t = omegaGroup h.qf h.qf_nondeg :=
  h.exists_form.choose_spec.choose_spec.1

theorem finrank_Vt : finrank (ZMod 2) (Vt S g t) = 6 := h.exists_form.choose_spec.choose_spec.2.1

theorem not_isPlus (hm : c = .omegaMinus6) : ¬ O62.IsPlus h.qf :=
  h.exists_form.choose_spec.choose_spec.2.2 hm

theorem πR_eq : (h.R₀.subgroupOf h.S₀.M).map h.π = omegaGroup h.qf h.qf_nondeg :=
  h.π_R₀.trans h.RmodN_eq

theorem π_mem_O (k : ↥(h.S₀.M)) : h.π k ∈ TauCeti.QuadraticMap.orthogonalGroup h.qf :=
  W4Loc.mem_orthogonalGroup h.act h.finrank_Vt h.qf_nondeg h.πR_eq k

theorem card_le_of_isPGroup [IsSimpleGroup G] (hNQ : NQIrredStmt) (hNQ6 : NQPlus6Stmt)
    (P : Subgroup h.S₀.Mbar) (hP : IsPGroup 2 P) : Nat.card P ≤ 2 ^ 7 :=
  W4Loc.card_le_of_isPGroup h.act h.card_Qt (h.lat hNQ hNQ6) h.π_mem_O
    (fun _ hP' h2 => O62.card_le_of_isPGroup h.finrank_Vt h.qf_nondeg hP' h2) P hP

theorem card_le_of_elemAbelian
    [IsSimpleGroup G] (hNQ : NQIrredStmt) (hNQ6 : NQPlus6Stmt)
    (P : Subgroup h.S₀.Mbar) (hab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    (h2 : ∀ x ∈ P, x ^ 2 = 1) : Nat.card P ≤ 2 ^ 4 :=
  W4Loc.card_le_of_elemAbelian h.act h.card_Qt (h.lat hNQ hNQ6) h.π_mem_O
    (fun _ hP' hab' h2' => O62.card_le_of_elemAbelian h.finrank_Vt h.qf_nondeg hP' hab' h2')
    P hab h2

end W4Hyp

end CFSG.LargeExtraspecial.S14
