module

public import CFSG.CGT.PushingUpLit.SolK.Basics
public import CFSG.CGT.PushingUpLit.SolK.ModData

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.Assembly CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin
  CFSG.Quasithin.G6 Equiv Equiv.Perm
open scoped commutatorElement

variable {G : Type} [Group G] {M X : Subgroup G} {n : ℕ} (D : ModData G X n)

theorem ModData.W_le_Y : D.W ≤ pCoreOf 2 X := by
  rw [D.W_eq, Subgroup.commutator_le]
  intro y hy x hx
  have h1 : x * y⁻¹ * x⁻¹ ∈ pCoreOf 2 X := pCoreOf_normalized X hx ((pCoreOf 2 X).inv_mem hy)
  have : ⁅y, x⁆ = y * (x * y⁻¹ * x⁻¹) := by simp only [commutatorElement_def]; group
  rw [this]
  exact Subgroup.mul_mem _ hy h1

theorem ModData.W_le_X : D.W ≤ X := (ModData.W_le_Y D).trans (pCoreOf_le_self X)

structure XNorm (M X : Subgroup G) : Prop where
  le : X ≤ M
  normal : ∀ m ∈ M, ∀ x ∈ X, m * x * m⁻¹ ∈ X

namespace XNorm

variable {D} (h : XNorm M X)
include h

theorem Y_normalized {m : G} (hm : m ∈ M) {y : G} (hy : y ∈ pCoreOf 2 X) :
    m * y * m⁻¹ ∈ pCoreOf 2 X := by
  let N : Subgroup G := (pCoreOf 2 X).map (MulAut.conj m).toMonoidHom
  have hNX : N ≤ X := by
    rintro _ ⟨z, hz, rfl⟩
    exact h.normal m hm z (pCoreOf_le_self X hz)
  have hN2 : IsPGroup 2 N := (isPGroup_pCoreOf' X).map (MulAut.conj m).toMonoidHom
  have hNnorm : ∀ x ∈ X, ∀ z ∈ N, x * z * x⁻¹ ∈ N := by
    rintro x hx _ ⟨z, hz, rfl⟩
    have h1 : m⁻¹ * x * m ∈ X := by
      have := h.normal m⁻¹ (M.inv_mem hm) x hx
      simpa using this
    refine ⟨(m⁻¹ * x * m) * z * (m⁻¹ * x * m)⁻¹, pCoreOf_normalized X h1 hz, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  have hle : N ≤ pCoreOf 2 X := le_pCoreOf_of_normalized hNX hNnorm hN2
  exact hle ⟨y, hy, rfl⟩

theorem W_normalized {m : G} (hm : m ∈ M) {w : G} (hw : w ∈ D.W) : m * w * m⁻¹ ∈ D.W := by
  rw [D.W_eq] at hw ⊢
  revert w
  have key : ⁅pCoreOf 2 X, X⁆ ≤ (⁅pCoreOf 2 X, X⁆).comap (MulAut.conj m).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro y hy x hx
    show m * ⁅y, x⁆ * m⁻¹ ∈ ⁅pCoreOf 2 X, X⁆
    rw [conj_commutator]
    exact Subgroup.commutator_mem_commutator (Y_normalized h hm hy) (h.normal m hm x hx)
  intro w hw
  exact key hw

theorem commutator_Q_X_le_Y {q x : G} (hq : q ∈ pCoreOf 2 M) (hx : x ∈ X) :
    ⁅q, x⁆ ∈ pCoreOf 2 X := by
  have hqM : q ∈ M := pCoreOf_le_self M hq
  have hxM : x ∈ M := h.le hx
  have hN2 : IsPGroup 2 ↥(X ⊓ pCoreOf 2 M) :=
    isPGroup_of_le (isPGroup_pCoreOf' M) inf_le_right
  have hle : X ⊓ pCoreOf 2 M ≤ pCoreOf 2 X := by
    refine le_pCoreOf_of_normalized inf_le_left (fun x' hx' z hz => ?_) hN2
    exact Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hx' hz.1)
      (X.inv_mem hx'), pCoreOf_normalized M (h.le hx') hz.2⟩
  apply hle
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · have h1 : q * x * q⁻¹ ∈ X := h.normal q hqM x hx
    have : ⁅q, x⁆ = (q * x * q⁻¹) * x⁻¹ := by simp only [commutatorElement_def]
    rw [this]
    exact Subgroup.mul_mem _ h1 (X.inv_mem hx)
  · have h1 : x * q⁻¹ * x⁻¹ ∈ pCoreOf 2 M := pCoreOf_normalized M hxM ((pCoreOf 2 M).inv_mem hq)
    have : ⁅q, x⁆ = q * (x * q⁻¹ * x⁻¹) := by simp only [commutatorElement_def]; group
    rw [this]
    exact Subgroup.mul_mem _ hq h1

end XNorm

theorem ModData.fix (hn : 2 ≤ n) {w : G} (hw : w ∈ D.W) (hfix : ∀ x ∈ X, x * w * x⁻¹ = w) :
    w = 1 := by
  have hd : Odd (2 * n + 1) := odd_two_mul_add_one n
  have hmem : D.β ⟨w, hw⟩ ∈ fixV ((alternatingGroup (Fin (2 * n + 1))).map
      (coreAct (2 * n + 1))) := by
    rw [mem_fixV_map_iff]
    intro σ hσ i
    obtain ⟨x, hx⟩ := D.ρ_surj σ hσ
    have h1 := D.equivar x ⟨w, hw⟩ (by rw [hfix x x.2]; exact hw)
    have h2 : D.β ⟨(x : G) * w * (x : G)⁻¹, by rw [hfix x x.2]; exact hw⟩ = D.β ⟨w, hw⟩ := by
      congr 1
      exact Subtype.ext (hfix x x.2)
    rw [h2, hx] at h1
    have := congrArg (fun v => vcoord v i) h1
    simp only [vcoord_coreAct] at this
    have h4 := congrArg (fun v => vcoord v (σ i)) h1
    have e : σ⁻¹ (σ i) = i := by simp
    simp only [vcoord_coreAct, e] at h4
    exact h4
  rw [fixV_alt_map hd (by omega)] at hmem
  have : D.β ⟨w, hw⟩ = 1 := hmem
  have h5 := D.β.injective (this.trans (map_one D.β).symm)
  exact congrArg Subtype.val h5

theorem ModData.comm_mem_W (hres : oResidualTwo ↥X = ⊤) {m : G}
    (hmY : ∀ x ∈ X, ⁅m, x⁆ ∈ pCoreOf 2 X) {x : G} (hx : x ∈ X) : ⁅m, x⁆ ∈ D.W := by
  classical
  have hWY : D.W ≤ pCoreOf 2 X := ModData.W_le_Y D
  have : (D.W.subgroupOf (pCoreOf 2 X)).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h1 : (g : G) * (n : G) * (g : G)⁻¹ = (n : G) := by
      rw [← D.W_comm_Y _ hn _ g.2]
      group
    show (g : G) * (n : G) * (g : G)⁻¹ ∈ D.W
    rw [h1]
    exact hn⟩
  have hq2 : IsPGroup 2 (↥(pCoreOf 2 X) ⧸ D.W.subgroupOf (pCoreOf 2 X)) :=
    (isPGroup_pCoreOf' X).to_quotient _
  have hY : ∀ x' : ↥X, ⁅m, (x' : G)⁆ ∈ pCoreOf 2 X := fun x' => hmY x' x'.2
  let f : ↥X →* (↥(pCoreOf 2 X) ⧸ D.W.subgroupOf (pCoreOf 2 X)) :=
    { toFun := fun x' => QuotientGroup.mk ⟨⁅m, (x' : G)⁆, hY x'⟩
      map_one' := by
        have : (⟨⁅m, ((1 : ↥X) : G)⁆, hY 1⟩ : ↥(pCoreOf 2 X)) = 1 := Subtype.ext (by simp)
        rw [this]
        exact QuotientGroup.mk_one _
      map_mul' := fun a b => by
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
        set y : G := ⁅m, (b : G)⁆ with hy
        have hyY : y ∈ pCoreOf 2 X := hY b
        have hxy : ⁅(a : G), y⁆ ∈ D.W := by
          rw [← commutator_inv']
          refine D.W.inv_mem ?_
          rw [D.W_eq]
          exact Subgroup.commutator_mem_commutator hyY a.2
        have hcalc : (⁅m, (a : G)⁆ * ⁅m, (b : G)⁆)⁻¹ * ⁅m, ((a * b : ↥X) : G)⁆ = ⁅(a : G), y⁆ := by
          have e1 : ⁅m, ((a * b : ↥X) : G)⁆ = ⁅m, (a : G)⁆ * ((a : G) * y * (a : G)⁻¹) := by
            rw [Subgroup.coe_mul, commutator_mul_right]
          have e2 : (a : G) * y * (a : G)⁻¹ = ⁅(a : G), y⁆ * y := conj_eq_commutator_mul _ _
          rw [e1, e2]
          have hc := D.W_comm_Y _ hxy _ hyY
          calc (⁅m, (a : G)⁆ * y)⁻¹ * (⁅m, (a : G)⁆ * (⁅(a : G), y⁆ * y))
              = y⁻¹ * (⁅(a : G), y⁆ * y) := by group
            _ = ⁅(a : G), y⁆ := by rw [hc]; group
        have hmem : (⁅m, (a : G)⁆ * ⁅m, (b : G)⁆)⁻¹ * ⁅m, ((a * b : ↥X) : G)⁆ ∈ D.W := by
          rw [hcalc]
          exact hxy
        have hmem' := D.W.inv_mem hmem
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv] at hmem' ⊢
        exact hmem' }
  have h1 := hom_eq_one_of_oResidual hres hq2 f
  have h2 : f ⟨x, hx⟩ = 1 := DFunLike.congr_fun h1 ⟨x, hx⟩
  have h3 : (⟨⁅m, x⁆, hY ⟨x, hx⟩⟩ : ↥(pCoreOf 2 X)) ∈ D.W.subgroupOf (pCoreOf 2 X) :=
    (QuotientGroup.eq_one_iff _).1 h2
  exact h3

namespace XNorm

variable {D} (h : XNorm M X)
include h

theorem q_centralizes_W (hn : 2 ≤ n) {q : G} (hq : q ∈ pCoreOf 2 M) :
    ∀ w ∈ D.W, q * w * q⁻¹ = w := by
  classical
  have hd : Odd (2 * n + 1) := odd_two_mul_add_one n
  have hd5 : 5 ≤ 2 * n + 1 := by omega
  have hqM : q ∈ M := pCoreOf_le_self M hq
  have hqW : ∀ w ∈ D.W, q * w * q⁻¹ ∈ D.W := fun w hw => W_normalized h hqM hw
  have hqW' : ∀ w ∈ D.W, q⁻¹ * w * q ∈ D.W := fun w hw => by
    have := W_normalized h (M.inv_mem hqM) hw
    simpa using this
  let α : MulAut ↥D.W :=
    { toFun := fun w => ⟨q * w * q⁻¹, hqW w w.2⟩
      invFun := fun w => ⟨q⁻¹ * w * q, hqW' w w.2⟩
      left_inv := fun w => Subtype.ext (by simp [mul_assoc])
      right_inv := fun w => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  let γ : MulAut ↥(coreMod (2 * n + 1)) := (D.β.symm.trans α).trans D.β
  have hγ : ∀ w : ↥D.W, γ (D.β w) = D.β (α w) := fun w => by simp [γ]
  have hcomm : ∀ (x : ↥X) (v : ↥(coreMod (2 * n + 1))),
      γ (coreAct (2 * n + 1) (D.ρ x) v) = coreAct (2 * n + 1) (D.ρ x) (γ v) := by
    intro x v
    obtain ⟨w, rfl⟩ := D.β.surjective v
    have hxW : (x : G) * (w : G) * (x : G)⁻¹ ∈ D.W := W_normalized h (h.le x.2) w.2
    have hqwW : q * (w : G) * q⁻¹ ∈ D.W := hqW w w.2
    have hxqwW : (x : G) * (q * (w : G) * q⁻¹) * (x : G)⁻¹ ∈ D.W :=
      W_normalized h (h.le x.2) hqwW
    rw [← D.equivar x w hxW, hγ, hγ]
    show D.β (α ⟨(x : G) * (w : G) * (x : G)⁻¹, hxW⟩) =
      coreAct (2 * n + 1) (D.ρ x) (D.β ⟨q * (w : G) * q⁻¹, hqwW⟩)
    rw [← D.equivar x ⟨q * (w : G) * q⁻¹, hqwW⟩ hxqwW]
    congr 1
    refine Subtype.ext ?_
    show q * ((x : G) * (w : G) * (x : G)⁻¹) * q⁻¹ = (x : G) * (q * (w : G) * q⁻¹) * (x : G)⁻¹
    have hy : ⁅q, (x : G)⁆ ∈ pCoreOf 2 X := commutator_Q_X_le_Y h hq x.2
    have h1 : q * (x : G) * q⁻¹ = ⁅q, (x : G)⁆ * (x : G) := conj_eq_commutator_mul q x
    have h2 : q * ((x : G) * (w : G) * (x : G)⁻¹) * q⁻¹ =
        (q * (x : G) * q⁻¹) * (q * (w : G) * q⁻¹) * (q * (x : G) * q⁻¹)⁻¹ := by group
    rw [h2, h1]
    have h3 := D.W_comm_Y _ hxqwW _ hy
    calc ⁅q, (x : G)⁆ * (x : G) * (q * (w : G) * q⁻¹) * (⁅q, (x : G)⁆ * (x : G))⁻¹
        = ⁅q, (x : G)⁆ * ((x : G) * (q * (w : G) * q⁻¹) * (x : G)⁻¹) * ⁅q, (x : G)⁆⁻¹ := by group
      _ = (x : G) * (q * (w : G) * q⁻¹) * (x : G)⁻¹ := by
        rw [← h3]
        group
  have hcommA : ∀ σ ∈ alternatingGroup (Fin (2 * n + 1)), ∀ v,
      γ (coreAct (2 * n + 1) σ v) = coreAct (2 * n + 1) σ (γ v) := by
    intro σ hσ v
    obtain ⟨x, hx⟩ := D.ρ_surj σ hσ
    rw [← hx]
    exact hcomm x v
  have hnorm : ∀ σ ∈ alternatingGroup (Fin (2 * n + 1)), ∃ σ' ∈ alternatingGroup (Fin (2 * n + 1)),
      ∀ v, γ (coreAct (2 * n + 1) σ v) = coreAct (2 * n + 1) σ' (γ v) :=
    fun σ hσ => ⟨σ, hσ, hcommA σ hσ⟩
  have hnorm' : ∀ σ' ∈ alternatingGroup (Fin (2 * n + 1)),
      ∃ σ ∈ alternatingGroup (Fin (2 * n + 1)),
      ∀ v, γ (coreAct (2 * n + 1) σ v) = coreAct (2 * n + 1) σ' (γ v) :=
    fun σ' hσ' => ⟨σ', hσ', hcommA σ' hσ'⟩
  obtain ⟨π, hπ⟩ := exists_perm_of_normalizes_alt hd hd5 γ hnorm hnorm'
  have hπc : ∀ σ ∈ alternatingGroup (Fin (2 * n + 1)), π * σ = σ * π := by
    intro σ hσ
    refine coreAct_injective (n := 2 * n + 1) (by omega) (MulEquiv.ext fun v => ?_)
    have h1 : coreAct (2 * n + 1) (π * σ) v = coreAct (2 * n + 1) π (coreAct (2 * n + 1) σ v) := by
      rw [map_mul]; rfl
    have h2 : coreAct (2 * n + 1) (σ * π) v = coreAct (2 * n + 1) σ (coreAct (2 * n + 1) π v) := by
      rw [map_mul]; rfl
    rw [h1, h2, ← hπ, ← hπ]
    exact hcommA σ hσ v
  have hπ1 : π = 1 := eq_one_of_commute_alt (by omega) hπc
  have hid : ∀ v, γ v = v := fun v => by rw [hπ v, hπ1, map_one]; rfl
  intro w hw
  have h1 := hid (D.β ⟨w, hw⟩)
  rw [hγ] at h1
  exact congrArg Subtype.val (D.β.injective h1)

theorem Y_le_Q : pCoreOf 2 X ≤ pCoreOf 2 M :=
  le_pCoreOf_of_normalized ((pCoreOf_le_self X).trans h.le)
    (fun _ hm _ hy => Y_normalized h hm hy) (isPGroup_pCoreOf' X)

section WithD

variable (D)

include D

theorem W_le_Q : D.W ≤ pCoreOf 2 M := (ModData.W_le_Y D).trans (Y_le_Q h)

theorem comm_Y_eq_one (hn : 2 ≤ n) (hres : oResidualTwo ↥X = ⊤) {m : G} (hmM : m ∈ M)
    (hmW : ∀ w ∈ D.W, m * w * m⁻¹ = w) (hmY : ∀ x ∈ X, ⁅m, x⁆ ∈ pCoreOf 2 X) {y : G}
    (hy : y ∈ pCoreOf 2 X) : ⁅m, y⁆ = 1 := by
  have hyX : y ∈ X := pCoreOf_le_self X hy
  have hz : ⁅m, y⁆ ∈ D.W := D.comm_mem_W hres hmY hyX
  refine ModData.fix D hn hz (fun x hx => ?_)
  have hm' : m⁻¹ ∈ M := M.inv_mem hmM
  have hmY' : ∀ x ∈ X, ⁅m⁻¹, x⁆ ∈ pCoreOf 2 X := by
    intro x hx
    have h1 : ⁅m⁻¹, x⁆ = m⁻¹ * ⁅x, m⁆ * (m⁻¹)⁻¹ := by simp only [commutatorElement_def]; group
    rw [h1, ← commutator_inv' m x]
    exact Y_normalized h hm' ((pCoreOf 2 X).inv_mem (hmY x hx))
  have hc' : ⁅m⁻¹, x⁆ ∈ D.W := D.comm_mem_W hres hmY' hx
  have hy' : x * y * x⁻¹ ∈ pCoreOf 2 X := pCoreOf_normalized X hx hy
  have hw : ⁅x, y⁆ ∈ D.W := by
    rw [← commutator_inv']
    refine D.W.inv_mem ?_
    rw [D.W_eq]
    exact Subgroup.commutator_mem_commutator hy hx
  have e1 : x * ⁅m, y⁆ * x⁻¹ = ⁅x * m * x⁻¹, x * y * x⁻¹⁆ := conj_commutator x m y
  have e2 : x * m * x⁻¹ = m * ⁅m⁻¹, x⁆ := by simp only [commutatorElement_def]; group
  have e3 : ⁅m * ⁅m⁻¹, x⁆, x * y * x⁻¹⁆ = ⁅m, x * y * x⁻¹⁆ := by
    rw [commutator_mul_left']
    have : ⁅⁅m⁻¹, x⁆, x * y * x⁻¹⁆ = 1 := commutator_eq_one_of_comm (D.W_comm_Y _ hc' _ hy')
    rw [this]
    simp
  have e4 : ⁅m, x * y * x⁻¹⁆ = ⁅m, y⁆ := by
    rw [conj_eq_commutator_mul, commutator_mul_right]
    have h1 : ⁅m, ⁅x, y⁆⁆ = 1 := commutator_eq_one_of_comm (comm_of_conj_eq (hmW _ hw))
    rw [h1, one_mul]
    rw [D.comm hw hz, mul_inv_cancel_right]
  rw [e1, e2, e3, e4]

theorem exists_mul_mem_centralizer (hn : 2 ≤ n) (hres : oResidualTwo ↥X = ⊤) {m : G}
    (hmM : m ∈ M) (hmW : ∀ w ∈ D.W, m * w * m⁻¹ = w) (hmY : ∀ x ∈ X, ⁅m, x⁆ ∈ pCoreOf 2 X) :
    ∃ w ∈ D.W, w * m ∈ Subgroup.centralizer (X : Set G) := by
  classical
  have hd : Odd (2 * n + 1) := odd_two_mul_add_one n
  have hd5 : 5 ≤ 2 * n + 1 := by omega
  have hmem : ∀ x : ↥X, ⁅m, (x : G)⁆ ∈ D.W := fun x => D.comm_mem_W hres hmY x.2
  let c : ↥X → ↥(coreMod (2 * n + 1)) := fun x => D.β ⟨⁅m, (x : G)⁆, hmem x⟩
  have hc : ∀ x y, c (x * y) = c x * coreAct (2 * n + 1) (D.ρ x) (c y) := by
    intro x y
    have h1 : ⁅m, ((x * y : ↥X) : G)⁆ = ⁅m, (x : G)⁆ * ((x : G) * ⁅m, (y : G)⁆ * (x : G)⁻¹) := by
      rw [Subgroup.coe_mul, commutator_mul_right]
    have hxW : (x : G) * ⁅m, (y : G)⁆ * (x : G)⁻¹ ∈ D.W :=
      W_normalized h (h.le x.2) (hmem y)
    have h2 : (⟨⁅m, ((x * y : ↥X) : G)⁆, hmem (x * y)⟩ : ↥D.W) =
        ⟨⁅m, (x : G)⁆, hmem x⟩ * ⟨(x : G) * ⁅m, (y : G)⁆ * (x : G)⁻¹, hxW⟩ := Subtype.ext h1
    show D.β _ = _
    rw [h2, map_mul, D.equivar x ⟨⁅m, (y : G)⁆, hmem y⟩ hxW]
  have hker : ∀ x, D.ρ x = 1 → c x = 1 := by
    intro x hx
    have hxY : (x : G) ∈ pCoreOf 2 X := (D.ker x).1 hx
    have h1 : (⟨⁅m, (x : G)⁆, hmem x⟩ : ↥D.W) = 1 :=
      Subtype.ext (comm_Y_eq_one D h hn hres hmM hmW hmY hxY)
    show D.β _ = 1
    rw [h1, map_one]
  obtain ⟨u, hu⟩ := cocycle_coboundary_of_surj hd hd5 D.ρ D.ρ_alt D.ρ_surj c hc hker
  let w0 : ↥D.W := D.β.symm u
  have hw0u : D.β w0 = u := D.β.apply_symm_apply u
  have hw0sq : (w0 : G) * (w0 : G) = 1 := by
    have := D.sq w0.2
    rwa [pow_two] at this
  have hk : ∀ x ∈ X, ⁅m, x⁆ = (w0 : G) * (x * (w0 : G) * x⁻¹) := by
    intro x hx
    have hxW : x * (w0 : G) * x⁻¹ ∈ D.W := W_normalized h (h.le hx) w0.2
    have h1 := hu ⟨x, hx⟩
    have h2 : c ⟨x, hx⟩ = D.β (w0 * ⟨x * (w0 : G) * x⁻¹, hxW⟩) := by
      rw [map_mul, hw0u, D.equivar ⟨x, hx⟩ w0 hxW, hw0u]
      exact h1
    exact congrArg Subtype.val (D.β.injective h2)
  refine ⟨(w0 : G), w0.2, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hk' := hk x hx
  have key : m * x * m⁻¹ = (w0 : G) * x * (w0 : G) := by
    have e : m * x * m⁻¹ * x⁻¹ = (w0 : G) * (x * (w0 : G) * x⁻¹) := hk'
    calc m * x * m⁻¹ = (m * x * m⁻¹ * x⁻¹) * x := by group
      _ = (w0 : G) * (x * (w0 : G) * x⁻¹) * x := by rw [e]
      _ = (w0 : G) * x * (w0 : G) := by group
  have key' : m * x = (w0 : G) * x * (w0 : G) * m := by
    calc m * x = (m * x * m⁻¹) * m := by group
      _ = (w0 : G) * x * (w0 : G) * m := by rw [key]
  calc x * ((w0 : G) * m) = ((w0 : G) * (w0 : G)) * x * ((w0 : G) * m) := by rw [hw0sq]; group
    _ = (w0 : G) * ((w0 : G) * x * (w0 : G) * m) := by group
    _ = (w0 : G) * (m * x) := by rw [key']
    _ = (w0 : G) * m * x := by group

theorem q_eq_W_mul_R (hn : 2 ≤ n) (hres : oResidualTwo ↥X = ⊤) {q : G} (hq : q ∈ pCoreOf 2 M) :
    ∃ w ∈ D.W, ∃ r ∈ pCoreOf 2 M ⊓ Subgroup.centralizer (X : Set G), q = w * r := by
  obtain ⟨w, hw, hwq⟩ := exists_mul_mem_centralizer D h hn hres (pCoreOf_le_self M hq)
    (q_centralizes_W h hn hq) (fun _ hx => commutator_Q_X_le_Y h hq hx)
  have hsq : w * w = 1 := by
    have := D.sq hw
    rwa [pow_two] at this
  refine ⟨w, hw, w * q, Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ (W_le_Q D h hw) hq, hwq⟩, ?_⟩
  calc q = (w * w) * q := by rw [hsq]; group
    _ = w * (w * q) := by group

end WithD

end XNorm

end CFSG.CGT.PushingUpLit.SolK
