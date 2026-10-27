module

public import CFSG.CGT.PushingUpLit.BHS6.SixSix
public import CFSG.CGT.PushingUpLit.BHS6.SymLocalBlock
public import CFSG.CGT.PushingUpLit.BHS7.BlockV

public section

namespace CFSG.CGT.PushingUpLit.SYMB

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
  CFSG.CGT.PushingUpLit.BHS7
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {G T V : Subgroup Γ} {n : ℕ}
  {φ : ↥G →* Equiv.Perm (Fin n)} {ψ : ↥V →* ↥(G6.coreMod n)} {T' : Set (Equiv.Perm (Fin n))}

omit [Finite Γ] in
theorem sym_V_le_pCore (S : SymSetting G T V n φ ψ T') : V ≤ pCoreOf 2 G :=
  S.vQ.trans (C1GN.omegaOneCenterOf_le_self _)

omit [Finite Γ] in
theorem sym_ne_comm_block (S : SymSetting G T V n φ ψ T') {F : Subgroup Γ} (hF : IsBTBlock G T F)
    (hFn : ¬ F ≤ cStarIn G T) : ⁅F, V⁆ ≠ ⊥ := by
  have hC : G ⊓ Subgroup.centralizer (V : Set Γ) ≤ cStarIn G T :=
    (inf_le_inf_left G (Subgroup.centralizer_le fun x hx => S.vT hx)).trans
      (centralizer_le_cStarIn G T)
  exact fun h0 => hFn ((le_inf hF.le (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h0)).trans hC)

omit [Finite Γ] in
theorem sym_block_le_normalizer (S : SymSetting G T V n φ ψ T') {F : Subgroup Γ}
    (hF : IsBTBlock G T F) : F ≤ Subgroup.normalizer (V : Set Γ) :=
  hF.le.trans S.data.normal

theorem sym_inf_centralizer_block (S : SymSetting G T V n φ ψ T') {F : Subgroup Γ}
    (hF : IsBTBlock G T F) (hFn : ¬ F ≤ cStarIn G T) :
    F ⊓ Subgroup.centralizer (V : Set Γ) = pCoreOf 2 F :=
  inf_centralizer_eq_pCoreOf S.charTwo S.sylow hF (sym_V_le_pCore S)
    (sym_block_le_normalizer S hF) (sym_ne_comm_block S hF hFn)

theorem sym_pCore_block_le (S : SymSetting G T V n φ ψ T') {F : Subgroup Γ}
    (hF : IsBTBlock G T F) (hFn : ¬ F ≤ cStarIn G T) : pCoreOf 2 F ≤ V := by
  have hEV := sym_block_le_normalizer S hF
  have h1 := commutator_eq_blockW S.charTwo S.sylow hF (sym_V_le_pCore S) hEV
    (sym_ne_comm_block S hF hFn)
  rw [blockW_eq_pCoreOf hF] at h1
  rw [← h1, Subgroup.commutator_le]
  intro f hf v hv
  have e : ⁅f, v⁆ = (f * v * f⁻¹) * v⁻¹ := by simp [commutatorElement_def, mul_assoc]
  rw [e]
  exact V.mul_mem ((Subgroup.mem_normalizer_iff.mp (hEV hf) v).mp hv) (V.inv_mem hv)

theorem sym_block_normalized_by_kernel (S : SymSetting G T V n φ ψ T') {F : Subgroup Γ}
    (hF : IsBTBlock G T F) (hFn : ¬ F ≤ cStarIn G T) :
    kerG G φ ≤ Subgroup.normalizer (F : Set Γ) := by
  intro g hg
  obtain ⟨hgG, hg1⟩ := mem_kerG.1 hg
  have h2 : (⟨g, hgG⟩ : ↥G) ∈ φ.ker := hg1
  rw [S.data.φ_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at h2
  have hW : (blockW F : Set Γ) ⊆ (V : Set Γ) := by
    rw [blockW_eq_pCoreOf hF]
    exact sym_pCore_block_le S hF hFn
  have hgc : g ∈ G ⊓ Subgroup.centralizer (blockW F : Set Γ) :=
    ⟨hgG, Subgroup.centralizer_le hW h2.2⟩
  exact six_six S.charTwo S.sylow hF hgc

theorem sym_block_comm_pCore_le (S : SymSetting G T V n φ ψ T') {F : Subgroup Γ}
    (hF : IsBTBlock G T F) (hFn : ¬ F ≤ cStarIn G T) :
    ∀ f ∈ F, ∀ q ∈ pCoreOf 2 G, ⁅f, q⁆ ∈ V := by
  intro f hf q hq
  have hqG : q ∈ G := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 G hq
  have hqK : q ∈ kerG G φ := mem_kerG.2 ⟨hqG, map_eq_one_of_mem_pCoreOf S.data S.vQ hq hqG⟩
  have hqN : q ∈ Subgroup.normalizer (F : Set Γ) := sym_block_normalized_by_kernel S hF hFn hqK
  have hfG : f ∈ G := hF.le hf
  have h1 : ⁅f, q⁆ ∈ F := by
    have h2 : q * f⁻¹ * q⁻¹ ∈ F := (Subgroup.mem_normalizer_iff.mp hqN f⁻¹).mp (F.inv_mem hf)
    have e : ⁅f, q⁆ = f * (q * f⁻¹ * q⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [e]
    exact F.mul_mem hf h2
  have h3 : ⁅f, q⁆ ∈ pCoreOf 2 G := by
    have hn : f ∈ Subgroup.normalizer (pCoreOf 2 G : Set Γ) := le_normalizer_pCoreOf_self' G hfG
    have h4 : f * q * f⁻¹ ∈ pCoreOf 2 G := (Subgroup.mem_normalizer_iff.mp hn q).mp hq
    have e : ⁅f, q⁆ = (f * q * f⁻¹) * q⁻¹ := by simp [commutatorElement_def, mul_assoc]
    rw [e]
    exact (pCoreOf 2 G).mul_mem h4 ((pCoreOf 2 G).inv_mem hq)
  have h5 : ⁅f, q⁆ ∈ Subgroup.centralizer (V : Set Γ) := by
    have hVc : V ≤ Subgroup.centralizer (pCoreOf 2 G : Set Γ) :=
      S.vQ.trans ((Subgroup.closure_le _).mpr fun x hx => hx.1.2)
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (Subgroup.mem_centralizer_iff.1 (hVc hv) _ h3).symm
  have h6 : ⁅f, q⁆ ∈ F ⊓ Subgroup.centralizer (V : Set Γ) := ⟨h1, h5⟩
  rw [sym_inf_centralizer_block S hF hFn] at h6
  exact sym_pCore_block_le S hF hFn h6

theorem sym_block_ker_psi (S : SymSetting G T V n φ ψ T') {F : Subgroup Γ}
    (hF : IsBTBlock G T F) (hFn : ¬ F ≤ cStarIn G T) :
    ∃ k : ↥V, (k : Γ) ∈ F ⊓ Subgroup.centralizer (V : Set Γ) ∧ ψ k ≠ 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have hPV := sym_pCore_block_le S hF hFn
  have hPK := sym_inf_centralizer_block S hF hFn
  have hle : pCoreOf 2 F ≤ Subgroup.centralizer (F : Set Γ) := by
    intro p hp
    have hpV : p ∈ V := hPV hp
    have hpK : p ∈ F ⊓ Subgroup.centralizer (V : Set Γ) := by
      rw [hPK]
      exact hp
    have h1 : ψ ⟨p, hpV⟩ = 1 := hcon ⟨p, hpV⟩ hpK
    have h2 : (⟨p, hpV⟩ : ↥V) ∈ ψ.ker := h1
    rw [S.data.ψ_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at h2
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact Subgroup.mem_centralizer_iff.mp h2.2 f (hF.le hf)
  have h3 : ⁅pCoreOf 2 F, F⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hle
  rw [hF.perfect] at h3
  have hne := sym_ne_comm_block S hF hFn
  have h1 := commutator_eq_blockW S.charTwo S.sylow hF (sym_V_le_pCore S)
    (sym_block_le_normalizer S hF) hne
  rw [blockW_eq_pCoreOf hF, h3] at h1
  exact hne h1

end CFSG.CGT.PushingUpLit.SYMB
