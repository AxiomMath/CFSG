
module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCentSoundBase1

public import CFSG.Sporadic.Th.Simple
public import CFSG.Perm.CentralizerOrbit
public import CFSG.Sporadic.Ly.ThreeBCount

@[expose] public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open scoped Matrix Pointwise

section Facts

variable {c' : ℕ} (hC : CertFacts c')
include hC

theorem card_L : Nat.card L = 54 := by
  have hT := treeData_q1 hC
  have horb := hT.card_orbit
  have hstab : MulAction.stabilizer L (⟨2, hT.r_lt⟩ : Fin nX) = ⊥ := by
    rw [eq_bot_iff]
    intro l hl
    rw [MulAction.mem_stabilizer_iff] at hl
    have h2 : idx nX (l : J) 2 = 2 := by
      have := idx_val (l : J) (⟨2, hT.r_lt⟩ : Fin nX)
      rw [show (l : J) • (⟨2, hT.r_lt⟩ : Fin nX) = l • (⟨2, hT.r_lt⟩ : Fin nX) from rfl, hl]
        at this
      exact this
    have := L_fix_two_eq_one hC l l.2 h2
    exact (Subgroup.mem_bot).2 (Subtype.ext this)
  have h := Subgroup.card_mul_index (MulAction.stabilizer L (⟨2, hT.r_lt⟩ : Fin nX))
  rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq, hstab, Subgroup.card_bot, one_mul] at h
  rw [← h]
  exact horb

theorem eq_one_of_fix_of_card_orbit {w : Fin nX}
    (hw : Nat.card (MulAction.orbit L w) = 54) {l : J} (hl : l ∈ L) (hfix : l • w = w) :
    l = 1 := by
  have h := Subgroup.card_mul_index (MulAction.stabilizer L w)
  rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq, hw, card_L hC] at h
  have h1 : Nat.card (MulAction.stabilizer L w) = 1 := by omega
  have hmem : (⟨l, hl⟩ : L) ∈ MulAction.stabilizer L w := by
    rw [MulAction.mem_stabilizer_iff]
    exact hfix
  rw [Subgroup.card_eq_one] at h1
  rw [h1] at hmem
  exact congrArg Subtype.val ((Subgroup.mem_bot).1 hmem)

theorem card_centralizer_le_of_centChecks {z : J} {p0 bound c : ℕ} {Z X Y Z0 Z1 : Array V4}
    {zT xT yT yiT z0T z1T : Table} {q0 : Table × Table × Table} {qw : Table × Table}
    (hZ : rowsMatrix Z = matJ z) (hX : rowsMatrix X = matJ xJ) (hY : rowsMatrix Y = matJ yJ)
    (hZ0 : rowsMatrix Z0 = matJ z0J) (hZ1 : rowsMatrix Z1 = matJ z1J)
    (h : centChecks thSt nX p0 bound c Z X Y Z0 Z1 zT xT yT yiT z0T z1T alphaT betaInvT gplT q0
      qw = true) :
    Nat.card (Subgroup.centralizer ({z} : Set J)) ≤ bound := by
  unfold centChecks at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hmz, hmx⟩, hmy⟩, hmz0⟩, hmz1⟩, hinv⟩, ht0⟩, hp0⟩, hk0⟩, hr0⟩, hr1⟩, htw⟩,
    hcnt⟩ := h
  have hzT : Rep nX zT z := rep_of_matTableOK hC hZ hmz
  have hxT : Rep nX xT xJ := rep_of_matTableOK hC hX hmx
  have hyT : Rep nX yT yJ := rep_of_matTableOK hC hY hmy
  have hz0T : Rep nX z0T z0J := rep_of_matTableOK hC hZ0 hmz0
  have hz1T : Rep nX z1T z1J := rep_of_matTableOK hC hZ1 hmz1
  have hyiT : Rep nX yiT yJ⁻¹ := hyT.inv_of_invOK hinv
  have hxinv : xJ⁻¹ = xJ := by rw [inv_eq_iff_mul_eq_one, ← pow_two, x_sq hC]
  have hxiT : Rep nX xT xJ⁻¹ := by rw [hxinv]; exact hxT
  have T0 : TreeData nX xJ yJ q0Size 1 (ap q0.1) (ap q0.2.2) q0.2.1 :=
    TreeData.of_treeOK hxT hyT ht0
  set w := (stripZ zT gplT alphaT betaInvT q0.2.1 q0.2.2 xT yiT p0).2[2]! with hw
  have TW : TreeData nX z0J z1J q1Size w (ap qw.1) (findPt qw.1) qw.2 :=
    TreeData.of_treeOK hz0T hz1T htw
  have TJ := treeData_J hC
  have hwn : w < nX := TW.r_lt
  have hLw : Nat.card (MulAction.orbit L (⟨w, hwn⟩ : Fin nX)) = 54 := TW.card_orbit
  obtain ⟨-, hs⟩ := stripZ_spec hC hzT hxiT hyiT (pl0 := q0.2.1) (pos0 := q0.2.2) hp0
  set σ : J := (treeElt q0.2.1 (lettersG xJ yJ)
    (stripZ zT gplT alphaT betaInvT q0.2.1 q0.2.2 xT yiT p0).1)⁻¹ *
    (treeElt gplT (lettersG a b) p0)⁻¹ with hσ
  have hσ0 : idx nX σ p0 = 0 := by
    have := hs 0 (by norm_num)
    rw [pow_zero, idx_one] at this
    rw [← this, hr0]
  have hσ1 : idx nX σ (idx nX z p0) = 1 := by
    have := hs 1 (by norm_num)
    rw [pow_one] at this
    rw [← this, hr1]
  have hz2 : ∀ q : ℕ, idx nX (z ^ 2) q = idx nX z (idx nX z q) := fun q => by
    rw [pow_two, idx_mul]
  have hσ2 : idx nX σ (idx nX z (idx nX z p0)) = w := by
    have := hs 2 (by norm_num)
    rw [← hz2]
    exact this.symm
  have hσi0 : idx nX σ⁻¹ 0 = p0 := by rw [← hσ0, idx_inv_idx]
  have hσi1 : idx nX σ⁻¹ 1 = idx nX z p0 := by rw [← hσ1, idx_inv_idx]
  have hσi2 : idx nX σ⁻¹ w = idx nX z (idx nX z p0) := by rw [← hσ2, idx_inv_idx]
  set ω₀ : Fin nX := ⟨p0, hp0⟩ with hω₀
  have hreg : ∀ g : J, g • ω₀ = ω₀ → g • (z • ω₀) = z • ω₀ → g • (z • z • ω₀) = z • z • ω₀ →
      g = 1 := by
    intro g h1 h2 h3
    have e1 : idx nX g p0 = p0 := by
      have := congrArg Fin.val h1
      simp only [smul_val] at this
      exact this
    have e2 : idx nX g (idx nX z p0) = idx nX z p0 := by
      have := congrArg Fin.val h2
      simp only [smul_val] at this
      exact this
    have e3 : idx nX g (idx nX z (idx nX z p0)) = idx nX z (idx nX z p0) := by
      have := congrArg Fin.val h3
      simp only [smul_val] at this
      exact this
    set γ := σ * g * σ⁻¹ with hγ
    have hγ0 : idx nX γ 0 = 0 := by
      rw [hγ]; simp only [idx_mul]; rw [hσi0, e1, hσ0]
    have hγ1 : idx nX γ 1 = 1 := by
      rw [hγ]; simp only [idx_mul]; rw [hσi1, e2, hσ1]
    have hγw : idx nX γ w = w := by
      rw [hγ]; simp only [idx_mul]; rw [hσi2, e3, hσ2]
    have hγH : γ ∈ H := fix_zero_mem_H hC γ hγ0
    have hγL : γ ∈ L := H_fix_one_mem_L hC γ hγH hγ1
    have hγ1' : γ = 1 :=
      eq_one_of_fix_of_card_orbit hC hLw hγL (smul_eq_of_idx γ _ _ hγw)
    have : g = σ⁻¹ * γ * σ := by rw [hγ]; group
    rw [this, hγ1', mul_one, inv_mul_cancel]
  set f := acceptAt zT gplT alphaT betaInvT q0.2.1 q0.2.2 xT yiT qw.1 q1Size with hf
  have hS : ∀ ω : Fin nX, (∃ g : J, g • ω₀ = ω ∧ g • (z • ω₀) = z • ω ∧
      g • (z • z • ω₀) = z • z • ω) → ω ∈ {p : Fin nX | f p.val = true} := by
    rintro ω ⟨g, h1, h2, h3⟩
    have e1 : idx nX g p0 = ω.val := by
      have := congrArg Fin.val h1
      simp only [smul_val] at this
      exact this
    have e2 : idx nX g (idx nX z p0) = idx nX z ω.val := by
      have := congrArg Fin.val h2
      simp only [smul_val] at this
      exact this
    have e3 : idx nX g (idx nX z (idx nX z p0)) = idx nX z (idx nX z ω.val) := by
      have := congrArg Fin.val h3
      simp only [smul_val] at this
      exact this
    set t := treeElt gplT (lettersG a b) ω.val with ht
    have ht0 : idx nX t 0 = ω.val := TJ.elt ω.val ω.isLt
    have hti : idx nX t⁻¹ ω.val = 0 := by rw [← ht0, idx_inv_idx]
    obtain ⟨hs1, hs2⟩ := stripZ_spec hC hzT hxiT hyiT (pl0 := q0.2.1) (pos0 := q0.2.2) ω.isLt
    set γ := t⁻¹ * g * σ⁻¹ with hγ
    have hγ0 : idx nX γ 0 = 0 := by
      rw [hγ]; simp only [idx_mul]; rw [hσi0, e1, hti]
    have hγH : γ ∈ H := fix_zero_mem_H hC γ hγ0
    set v₁ := idx nX t⁻¹ (idx nX z ω.val) with hv₁
    have hγ1 : idx nX γ 1 = v₁ := by
      rw [hγ]; simp only [idx_mul]; rw [hσi1, e2]
    have hv₁n : v₁ < nX := idx_lt _ (idx_lt _ ω.isLt)
    have hmem : (⟨v₁, hv₁n⟩ : Fin nX) ∈
        MulAction.orbit (Subgroup.closure ({xJ, yJ} : Set J)) (⟨1, T0.r_lt⟩ : Fin nX) := by
      refine ⟨⟨γ, hγH⟩, ?_⟩
      apply smul_eq_of_idx
      exact hγ1
    have hpos := T0.pos_spec hmem
    have hk : (stripZ zT gplT alphaT betaInvT q0.2.1 q0.2.2 xT yiT ω.val).1 < q0Size := by
      rw [hs1]; exact hpos.1
    have hpk : ap q0.1 (stripZ zT gplT alphaT betaInvT q0.2.1 q0.2.2 xT yiT ω.val).1 = v₁ := by
      rw [hs1]; exact hpos.2
    set k := (stripZ zT gplT alphaT betaInvT q0.2.1 q0.2.2 xT yiT ω.val).1 with hkdef
    set h' := treeElt q0.2.1 (lettersG xJ yJ) k with hh'
    have hh'1 : idx nX h' 1 = v₁ := by rw [hh', T0.elt k hk]; exact hpk
    have hh'H : h' ∈ H := treeElt_mem H _ xy_mem_H k
    set δ := h'⁻¹ * γ with hδ
    have hδH : δ ∈ H := H.mul_mem (H.inv_mem hh'H) hγH
    have hδ1 : idx nX δ 1 = 1 := by rw [hδ, idx_mul, hγ1, ← hh'1, idx_inv_idx]
    have hδL : δ ∈ L := H_fix_one_mem_L hC δ hδH hδ1
    have hr2 : (stripZ zT gplT alphaT betaInvT q0.2.1 q0.2.2 xT yiT ω.val).2[2]! = idx nX δ w := by
      rw [hs2 2 (by norm_num)]
      have e4 : idx nX (z ^ 2) ω.val = idx nX g (idx nX σ⁻¹ w) := by
        rw [hz2, ← e3, hσi2]
      rw [e4, hδ, hγ]
      simp only [idx_mul]
      rfl
    have hmemw : (⟨idx nX δ w, idx_lt δ hwn⟩ : Fin nX) ∈
        MulAction.orbit (Subgroup.closure ({z0J, z1J} : Set J)) (⟨w, TW.r_lt⟩ : Fin nX) := by
      refine ⟨⟨δ, hδL⟩, ?_⟩
      apply smul_eq_of_idx
      rfl
    obtain ⟨hkw, -⟩ := TW.pos_spec hmemw
    show f ω.val = true
    rw [hf]
    unfold acceptAt
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hk, by rw [hr2]; exact hkw⟩
  have hcard := CFSG.Perm.card_centralizer_le_of_triple z ω₀ hreg _ (Set.toFinite _) hS
  have hcount : {p : Fin nX | f p.val = true}.ncard ≤
      countAccept zT gplT alphaT betaInvT q0.2.1 q0.2.2 xT yiT qw.1 q1Size nX 1048576 :=
    CFSG.Sporadic.Ly.ncard_le_countBlocks (by norm_num) f
  exact hcard.trans (hcount.trans hcnt)

end Facts

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent
