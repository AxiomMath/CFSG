module

public import CFSG.CGT.PushingUpLit.BHS6.BlockThree

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

theorem mem_sup_centralizer_of_mem_autOn {W E : Subgroup Γ} {g : Γ}
    (hg : g ∈ Subgroup.normalizer (W : Set Γ))
    (h : conjAct W ⟨g, hg⟩ ∈ autOn E W) : g ∈ E ⊔ Subgroup.centralizer (W : Set Γ) := by
  obtain ⟨a, haE, hag⟩ := mem_autOn_iff.mp h
  have h1 : conjAct W (a⁻¹ * ⟨g, hg⟩) = 1 := by rw [map_mul, map_inv, hag, inv_mul_cancel]
  have h2 := (conjAct_eq_one_iff W (a⁻¹ * ⟨g, hg⟩)).mp h1
  have h3 : ((a⁻¹ * ⟨g, hg⟩ : ↥(Subgroup.normalizer (W : Set Γ))) : Γ) = (a : Γ)⁻¹ * g := rfl
  rw [h3] at h2
  have : g = (a : Γ) * ((a : Γ)⁻¹ * g) := by group
  rw [this]
  exact mul_mem (le_sup_left (a := E) haE) (le_sup_right (b := Subgroup.centralizer (W : Set Γ)) h2)

variable [Finite Γ] {G T E : Subgroup Γ}

theorem baum_le_sup_centralizer_of_sl (hG : CharTwo G) (hT : IsSylowOf 2 T G)
    (hE : IsBTBlock G T E) {n : ℕ} (hn2 : 2 ≤ n) (hn : IsNaturalSLTwoModule ↥E n) :
    baum T ≤ E ⊔ Subgroup.centralizer (blockW E : Set Γ) := by
  have hBN : baum T ≤ Subgroup.normalizer (E : Set Γ) := baum_le_normalizer_of_isBTBlock hE
  have hW : blockW E = pCoreOf 2 E := blockW_eq_pCoreOf hE
  have hBW : baum T ≤ Subgroup.normalizer ((pCoreOf 2 E : Subgroup Γ) : Set Γ) :=
    hBN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 E)
  have h1 := (block_structure_sl hG hT hE hn2 hn).1
  rw [hW] at h1 ⊢
  intro b hb
  refine mem_sup_centralizer_of_mem_autOn (hBW hb) ?_
  exact h1 (mem_autOn_iff.mpr ⟨⟨b, hBW hb⟩, hb, rfl⟩)

theorem block_alt_commutator (hG : CharTwo G) (hT : IsSylowOf 2 T G) (hE : IsBTBlock G T E)
    {m : ℕ} (hm : 1 ≤ m) (hn : IsNaturalAltModule ↥E m) {x y : Γ}
    (hxE : x ∈ Subgroup.normalizer (E : Set Γ)) (hyE : y ∈ Subgroup.normalizer (E : Set Γ)) :
    x * y * x⁻¹ * y⁻¹ ∈ E ⊔ Subgroup.centralizer (blockW E : Set Γ) := by
  classical
  have hWb : blockW E = pCoreOf 2 E := blockW_eq_pCoreOf hE
  rw [hWb]
  set W : Subgroup Γ := pCoreOf 2 E with hWdef
  have hWe : IsElemAbelian 2 W := isElemAbelian_of_forall' hE.elemAbelian.1 hE.elemAbelian.2
  let _ : CommGroup ↥W := commGroupOfElemAbelian hWe
  obtain ⟨D, ψ, hψβ, -, hψbij, -⟩ := block_structure_symm hG hT hE hm hn hWdef hWe
  have hXV : Subgroup.normalizer (E : Set Γ) ≤ Subgroup.normalizer (W : Set Γ) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 E
  have hxN : x ∈ Subgroup.normalizer (W : Set Γ) := hXV hxE
  have hyN : y ∈ Subgroup.normalizer (W : Set Γ) := hXV hyE
  have hNE : autOn (Subgroup.normalizer (E : Set Γ)) W ≤
      Subgroup.normalizer (autOn E W : Set (MulAut ↥W)) :=
    autOn_le_normalizer_autOn hXV le_rfl
  have hxbar : conjAct W ⟨x, hxN⟩ ∈ Subgroup.normalizer (autOn E W : Set (MulAut ↥W)) :=
    hNE (mem_autOn_iff.mpr ⟨⟨x, hxN⟩, hxE, rfl⟩)
  have hybar : conjAct W ⟨y, hyN⟩ ∈ Subgroup.normalizer (autOn E W : Set (MulAut ↥W)) :=
    hNE (mem_autOn_iff.mpr ⟨⟨y, hyN⟩, hyE, rfl⟩)
  have hθ : ∀ e : ↥(autOn E W),
      ψ ⟨(e : MulAut ↥W), Subgroup.le_normalizer e.2⟩ =
        ((D.θ e : alternatingGroup (Fin (2 * m + 1))) : Equiv.Perm (Fin (2 * m + 1))) := by
    intro e
    refine coreAct_injective (by omega) ?_
    ext v
    obtain ⟨w, rfl⟩ := D.surj v
    rw [← hψβ ⟨(e : MulAut ↥W), Subgroup.le_normalizer e.2⟩ w, D.equivar e w]
  set c : ↥(Subgroup.normalizer (autOn E W : Set (MulAut ↥W))) :=
    ⟨conjAct W ⟨x, hxN⟩, hxbar⟩ * ⟨conjAct W ⟨y, hyN⟩, hybar⟩ * ⟨conjAct W ⟨x, hxN⟩, hxbar⟩⁻¹ *
      ⟨conjAct W ⟨y, hyN⟩, hybar⟩⁻¹ with hcdef
  have hsign : (ψ c).sign = 1 := by
    simp only [hcdef, map_mul, map_inv]
    rw [mul_comm (Equiv.Perm.sign (ψ ⟨conjAct W ⟨x, hxN⟩, hxbar⟩))
      (Equiv.Perm.sign (ψ ⟨conjAct W ⟨y, hyN⟩, hybar⟩)), mul_inv_cancel_right, mul_inv_cancel]
  have hcA : ψ c ∈ alternatingGroup (Fin (2 * m + 1)) := Equiv.Perm.mem_alternatingGroup.mpr hsign
  set a : ↥(autOn E W) := D.θ.symm ⟨ψ c, hcA⟩ with hadef
  have hψa : ψ ⟨(a : MulAut ↥W), Subgroup.le_normalizer a.2⟩ = ψ c := by
    rw [hθ a, hadef, D.θ.apply_symm_apply]
  have hac : (⟨(a : MulAut ↥W), Subgroup.le_normalizer a.2⟩ :
      ↥(Subgroup.normalizer (autOn E W : Set (MulAut ↥W)))) = c := hψbij.1 hψa
  have hcA' : (c : MulAut ↥W) ∈ autOn E W := by
    have := congrArg (fun z : ↥(Subgroup.normalizer (autOn E W : Set (MulAut ↥W))) =>
      (z : MulAut ↥W)) hac
    simp only at this
    rw [← this]
    exact a.2
  have hcomm : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.normalizer (W : Set Γ) :=
    mul_mem (mul_mem (mul_mem hxN hyN) (inv_mem hxN)) (inv_mem hyN)
  refine mem_sup_centralizer_of_mem_autOn hcomm ?_
  have : conjAct W ⟨x * y * x⁻¹ * y⁻¹, hcomm⟩ = (c : MulAut ↥W) := by
    have e1 : (⟨x * y * x⁻¹ * y⁻¹, hcomm⟩ : ↥(Subgroup.normalizer (W : Set Γ))) =
        ⟨x, hxN⟩ * ⟨y, hyN⟩ * ⟨x, hxN⟩⁻¹ * ⟨y, hyN⟩⁻¹ := rfl
    rw [e1]
    simp only [map_mul, map_inv, hcdef]
    rfl
  rw [this]
  exact hcA'

end CFSG.CGT.PushingUpLit.BHS7
