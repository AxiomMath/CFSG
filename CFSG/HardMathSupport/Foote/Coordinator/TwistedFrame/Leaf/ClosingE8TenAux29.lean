module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenAux28
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenAux23

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8
open scoped commutatorElement
open E8TenTwo

set_option linter.unusedSectionVars false


section Group

theorem comm_conj_comm {G : Type*} [Group G] {a a' g x : G} (ha : a * g = g * a)
    (ha' : a' * g = g * a') : ⁅a, ⁅a', g * x * g⁻¹⁆⁆ = g * ⁅a, ⁅a', x⁆⁆ * g⁻¹ := by
  have e1 : g⁻¹ * a * g = a := by
    calc g⁻¹ * a * g = g⁻¹ * (a * g) := by group
      _ = g⁻¹ * (g * a) := by rw [ha]
      _ = a := by group
  have e2 : g⁻¹ * a' * g = a' := by
    calc g⁻¹ * a' * g = g⁻¹ * (a' * g) := by group
      _ = g⁻¹ * (g * a') := by rw [ha']
      _ = a' := by group
  calc ⁅a, ⁅a', g * x * g⁻¹⁆⁆ = g * ⁅g⁻¹ * a * g, ⁅g⁻¹ * a' * g, x⁆⁆ * g⁻¹ := by
        simp only [commutatorElement_def]
        group
    _ = g * ⁅a, ⁅a', x⁆⁆ * g⁻¹ := by rw [e1, e2]

theorem E_identity {G : Type*} [Group G] (v a' u : G) :
    v * ⁅a', u⁆ * v⁻¹ = (v * a' * v⁻¹) * ((v * u * v⁻¹ * u⁻¹) * (u * (v * a' * v⁻¹)⁻¹ * u⁻¹) *
      (v * u * v⁻¹ * u⁻¹)⁻¹) := by
  simp only [commutatorElement_def]
  group

theorem conj_comm_central {G : Type*} [Group G] {a v X : G} (ha : a * v = v * a) :
    ⁅a, v * X * v⁻¹⁆ = v * ⁅a, X⁆ * v⁻¹ := by
  have e : v⁻¹ * a * v = a := by
    calc v⁻¹ * a * v = v⁻¹ * (a * v) := by group
      _ = v⁻¹ * (v * a) := by rw [ha]
      _ = a := by group
  calc ⁅a, v * X * v⁻¹⁆ = v * ⁅v⁻¹ * a * v, X⁆ * v⁻¹ := by
        simp only [commutatorElement_def]
        group
    _ = v * ⁅a, X⁆ * v⁻¹ := by rw [e]

end Group

section Main

variable {K : Type} [Field K] [Finite K] (D : LangLevi TwClass.e8Ten.tag K TwClass.e8Ten.w)

theorem comm_mem_Uθ (D : LangLevi TwClass.e8Ten.tag K TwClass.e8Ten.w) {x y : ModGL Tag.E8 K}
    (hx : x ∈ Qθ Tag.E8 K) (hy : y ∈ Qθ Tag.E8 K) :
    x * y * x⁻¹ * y⁻¹ ∈ Uθ Tag.E8 K := by
  have hxy : x * y * x⁻¹ ∈ Qθ Tag.E8 K := mul_mem (mul_mem hx hy) (inv_mem hx)
  have hz : x * y * x⁻¹ * y⁻¹ ∈ Qθ Tag.E8 K := mul_mem hxy (inv_mem hy)
  refine (CoordsAux.κ_eq_zero_iff D hz).1 ?_
  have h1 : CoordsAux.κ D (x * y * x⁻¹ * y⁻¹) =
      CoordsAux.κ D (x * y * x⁻¹) + CoordsAux.κ D y⁻¹ := CoordsAux.κ_mul D hxy (inv_mem hy)
  have h2 : CoordsAux.κ D (x * y * x⁻¹) = CoordsAux.κ D (x * y) + CoordsAux.κ D x⁻¹ :=
    CoordsAux.κ_mul D (mul_mem hx hy) (inv_mem hx)
  have h3 : CoordsAux.κ D (x * y) = CoordsAux.κ D x + CoordsAux.κ D y := CoordsAux.κ_mul D hx hy
  rw [h1, h2, h3, TwCoordsAux.κ_inv TwClass.e8Ten D hx, TwCoordsAux.κ_inv TwClass.e8Ten D hy]
  funext β
  simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply]
  ring

theorem case2_main (hchk : e8TenTwoCheck () = true) (hK : Nat.card K = 2)
    {H : Subgroup (ModGL Tag.E8 K)}
    (hb : TwBasic (TwClass.e8Ten.X₁ D) (TwClass.e8Ten.X₂ D))
    (hXH : TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D ≤ H)
    {v : ModGL Tag.E8 K} (hvQ : v ∈ Qθ Tag.E8 K)
    (hvB : conjSub v (Heis.Uneg Tag.E8 K) ≤ H)
    (hvM : ∀ β, κF D v β ≠ 0 → β ∈ mRoots ∧ (cls β = 1 ∨ cls β = 4))
    (hne : ∃ β, κF D v β ≠ 0) :
    ∃ m ∈ H, m ∈ Qθ Tag.E8 K ∧
      heisCoord Tag.E8 K m ∉ VS (TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D) := by
  haveI hcL : CharP D.L 2 := charP_L D hK
  simp only [e8TenTwoCheck, Bool.and_eq_true] at hchk
  obtain ⟨⟨⟨⟨hrat, hcols⟩, hwords⟩, hbfs⟩, hall⟩ := hchk
  obtain ⟨ω, hω⟩ := exists_omega D hK
  obtain ⟨b, hb20, hκb⟩ := decode D hK hω hvQ hvM
  have hb0 : b ≠ 0 := by
    rintro rfl
    obtain ⟨β, hβ⟩ := hne
    apply hβ
    rw [hκb, decv_zero hω]
    rfl
  have hT := allBelow_spec _ _ hall b (Nat.one_le_iff_ne_zero.2 hb0) (by omega)
  unfold hasTrans at hT
  rw [List.any_eq_true] at hT
  obtain ⟨c, hcT, hcO⟩ := hT
  rw [List.mem_map] at hcT
  obtain ⟨w, hwT, rfl⟩ := hcT
  have hwlt := wordsOk_spec hwords w hwT
  obtain ⟨e, he, hed⟩ := oSet_spec hcO
  obtain ⟨idx, hidx, hidxe⟩ := List.mem_iff_getElem.1 he
  have hgetD : bfsTab.getD idx (0, 0, 0) = e := by
    rw [getD_of_lt _ _ hidx]
    exact hidxe
  obtain ⟨f₁, hf₁, s, hs, hfs⟩ := Rz_bfs D hK hω hrat hcols hbfs idx hidx
  obtain ⟨k₁, hk₁, hdig⟩ := (bfsOk_spec hbfs idx hidx).1
  rw [hgetD, hed] at hfs hdig
  set d : ℕ := applyCols (compCols (gmats ()) w) b ^^^ b with hd
  have hRw := Rz_word D hK hω hrat hcols w hwlt
  unfold Rz at hRw
  obtain ⟨y, hy, -, Ty, hTy, hyb⟩ := hRw
  obtain ⟨hyb20, hTyb⟩ := hyb b hb20
  have hyw : applyCols (compCols (gmats ()) w) b = applyWord (gmats ()) w b :=
    applyCols_compCols _ w b hb20
  rw [hyw] at hd
  obtain ⟨k, hk, a, ha, rfl⟩ := stdVecs_form s hs
  unfold Rz at hf₁
  obtain ⟨h', hh', -, T', hT', hh'b⟩ := hf₁
  obtain ⟨-, hT's⟩ := hh'b _ (stdVecs_lt _ hs)
  rw [hfs] at hT's
  obtain ⟨u₀, hu₀Q, hu₀Ψ, hu₀κ⟩ := exists_u0 D hK hω hk ha
  obtain ⟨t₁, ht₁, ha₁⟩ := exists_apos D
  obtain ⟨t₂, ht₂, ha₂⟩ := exists_aneg D
  have hX₁H : TwClass.e8Ten.X₁ D ≤ H := le_sup_left.trans hXH
  have hX₂H : TwClass.e8Ten.X₂ D ≤ H := le_sup_right.trans hXH
  have ha₁U : pinnedX Tag.E8 K (highRoot Tag.E8) 1 ∈ Uθ Tag.E8 K := mem_rootSubgroup.2 ⟨1, rfl⟩
  have ha₂U : pinnedX Tag.E8 K (-highRoot Tag.E8) 1 ∈ Heis.Uneg Tag.E8 K :=
    mem_rootSubgroup.2 ⟨1, rfl⟩
  set a₁ := pinnedX Tag.E8 K (highRoot Tag.E8) 1 with ha₁def
  set a₂ := pinnedX Tag.E8 K (-highRoot Tag.E8) 1 with ha₂def
  have ha₁H : a₁ ∈ H := hX₁H (hb.Uθ_le ha₁U)
  have ha₂H : a₂ ∈ H := hX₁H (hb.Uneg_le ha₂U)
  obtain ⟨huQ, hκu⟩ := conj_Q D hK hh' hT' hu₀Q
  rw [hu₀κ, hT's] at hκu
  set u := h' * u₀ * h'⁻¹ with hu
  obtain ⟨hvyQ, hκvy⟩ := conj_Q D hK hy hTy hvQ
  rw [hκb, hTyb] at hκvy
  set vy := y * v * y⁻¹ with hvy
  have hvyB := conj_B D hb hXH hy hvB
  have huvQ : u * v ∈ Qθ Tag.E8 K := mul_mem huQ hvQ
  have hκuv : κF D (u * v) = κF D vy := by
    have h1 : κF D (u * v) = κF D u + κF D v := CoordsAux.κ_mul D huQ hvQ
    rw [h1, hκu, hκb, hκvy, ← decv_xor hω, hd, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  set z := (u * v) * vy⁻¹ with hz
  have hzQ : z ∈ Qθ Tag.E8 K := mul_mem huvQ (inv_mem hvyQ)
  have hzU : z ∈ Uθ Tag.E8 K := by
    refine (CoordsAux.κ_eq_zero_iff D hzQ).1 ?_
    have h1 : CoordsAux.κ D z = CoordsAux.κ D (u * v) + CoordsAux.κ D vy⁻¹ :=
      CoordsAux.κ_mul D huvQ (inv_mem hvyQ)
    rw [h1, TwCoordsAux.κ_inv TwClass.e8Ten D hvyQ]
    have h2 : CoordsAux.κ D (u * v) = CoordsAux.κ D vy := hκuv
    rw [h2]
    funext β
    simp
  have hzH : z ∈ H := hX₁H (hb.Uθ_le hzU)
  have huv : u * v = z * vy := by
    rw [hz]
    group
  have hb₀H : v * a₂ * v⁻¹ ∈ H := hvB (mem_conjSub_iff.2 (by
    have e : v⁻¹ * (v * a₂ * v⁻¹) * v = a₂ := by group
    rw [e]
    exact ha₂U))
  have hvya : vy * a₂ * vy⁻¹ ∈ H := hvyB (mem_conjSub_iff.2 (by
    have e : vy⁻¹ * (vy * a₂ * vy⁻¹) * vy = a₂ := by group
    rw [e]
    exact ha₂U))
  have hub : u * (v * a₂ * v⁻¹) * u⁻¹ ∈ H := by
    have e : u * (v * a₂ * v⁻¹) * u⁻¹ = z * (vy * a₂ * vy⁻¹) * z⁻¹ := by
      calc u * (v * a₂ * v⁻¹) * u⁻¹ = (u * v) * a₂ * (u * v)⁻¹ := by group
        _ = (z * vy) * a₂ * (z * vy)⁻¹ := by rw [huv]
        _ = z * (vy * a₂ * vy⁻¹) * z⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem hzH hvya) (inv_mem hzH)
  have hub' : u * (v * a₂ * v⁻¹)⁻¹ * u⁻¹ ∈ H := by
    have e : u * (v * a₂ * v⁻¹)⁻¹ * u⁻¹ = (u * (v * a₂ * v⁻¹) * u⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem hub
  have hc₀H : v * u * v⁻¹ * u⁻¹ ∈ H := hX₁H (hb.Uθ_le (comm_mem_Uθ D hvQ huQ))
  have hEH : v * ⁅a₂, u⁆ * v⁻¹ ∈ H := by
    rw [E_identity]
    exact mul_mem hb₀H (mul_mem (mul_mem hc₀H hub') (inv_mem hc₀H))
  have hMH : ⁅a₁, v * ⁅a₂, u⁆ * v⁻¹⁆ ∈ H := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha₁H hEH) (inv_mem ha₁H)) (inv_mem hEH)
  have hcomm1 : a₁ * v = v * a₁ := Uθ_comm_Qθ' ha₁U hvQ
  have hM : ⁅a₁, v * ⁅a₂, u⁆ * v⁻¹⁆ = v * ⁅a₁, ⁅a₂, u⁆⁆ * v⁻¹ := conj_comm_central hcomm1
  have hc₁ : a₁ * h' = h' * a₁ := hb.comm a₁ (hb.Uθ_le ha₁U) h' hh'
  have hc₂ : a₂ * h' = h' * a₂ := hb.comm a₂ (hb.Uneg_le ha₂U) h' hh'
  have hN' : ⁅a₁, ⁅a₂, u⁆⁆ = h' * ⁅a₁, ⁅a₂, u₀⁆⁆ * h'⁻¹ := comm_conj_comm hc₁ hc₂
  obtain ⟨hN₀Q, hκN₀⟩ := N_rat D hK hω hk ha hu₀Q hu₀Ψ ha₁ ha₂
  obtain ⟨hN'Q, hκN'⟩ := conj_Q D hK hh' hT' hN₀Q
  rw [hκN₀, map_smul, hT's, ← hN'] at hκN'
  rw [← hN'] at hN'Q
  have hMQ : v * ⁅a₁, ⁅a₂, u⁆⁆ * v⁻¹ ∈ Qθ Tag.E8 K := mul_mem (mul_mem hvQ hN'Q) (inv_mem hvQ)
  have hκM : κF D (v * ⁅a₁, ⁅a₂, u⁆⁆ * v⁻¹) = κF D ⁅a₁, ⁅a₂, u⁆⁆ := by
    have h1 : κF D (v * ⁅a₁, ⁅a₂, u⁆⁆ * v⁻¹) = κF D (v * ⁅a₁, ⁅a₂, u⁆⁆) + κF D v⁻¹ :=
      CoordsAux.κ_mul D (mul_mem hvQ hN'Q) (inv_mem hvQ)
    have h2 : κF D (v * ⁅a₁, ⁅a₂, u⁆⁆) = κF D v + κF D ⁅a₁, ⁅a₂, u⁆⁆ :=
      CoordsAux.κ_mul D hvQ hN'Q
    have h3 : κF D v⁻¹ = -κF D v := TwCoordsAux.κ_inv TwClass.e8Ten D hvQ
    rw [h1, h2, h3]
    funext β
    simp only [Pi.add_apply, Pi.neg_apply]
    ring
  have hi : 2 * k₁ < 20 := by omega
  have hdig4 : ((expandV d).getD (2 * k₁) 0) = (d >>> (2 * k₁)) &&& 3 := by
    rw [expandV_getD hi]
    have h2 : 2 * k₁ % 2 = 0 := by omega
    have h3 : 2 * k₁ / 2 = k₁ := by omega
    rw [if_pos h2, h3]
  have hemb : emb ω ((expandV d).getD (2 * k₁) 0) ≠ 0 := by
    intro h0
    exact hdig (by rw [← hdig4]; exact emb_eq_zero hω (expandV_lt d _) h0)
  have hcoord : κF D (v * ⁅a₁, ⁅a₂, u⁆⁆ * v⁻¹) (nuW (2 * k₁)) ≠ 0 := by
    rw [hκM, hκN', decv]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [decvX_apply_nuW ω _ hi]
    exact mul_ne_zero (mul_ne_zero ht₁ ht₂) hemb
  have hMH' : v * ⁅a₁, ⁅a₂, u⁆⁆ * v⁻¹ ∈ H := by
    rw [← hM]
    exact hMH
  exact ⟨_, hMH', hMQ,
    notVS_of_support D hK hMQ (mRoots_not_Bset (nuW_data _ (List.mem_range.2 hi)).1) hcoord⟩

end Main

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux
