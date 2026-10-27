module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TwelveTwoAux2
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenAux11
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.Coords

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8
open scoped commutatorElement

set_option linter.unusedSectionVars false



section Char2

variable {K : Type} [Field K] [Finite K] (D : LangLevi TwClass.e8Ten.tag K TwClass.e8Ten.w)

theorem charP_L (hK : Nat.card K = 2) : CharP D.L 2 := by
  haveI : CharP K 2 := E8Two.charP_two_of_card_two hK
  exact charP_of_injective_algebraMap (algebraMap K D.L).injective 2

theorem Fr_sq (hK : Nat.card K = 2) (c : D.L) : D.Fr c = c ^ 2 := by
  rw [D.hFr, hK]

theorem sign_eq_one {R : Type} [Field R] [CharP R 2] {ε : R} (h : ε = 1 ∨ ε = -1) : ε = 1 := by
  rcases h with h | h
  · exact h
  · rw [h, CharTwo.neg_eq]

theorem mem_Qθ_of_bc (hK : Nat.card K = 2) {z : ModGL Tag.E8 K} (hz : z ∈ adjointGroup Tag.E8 K)
    (hQ : baseChangeGL (algebraMap K D.L) z ∈ Qθ Tag.E8 D.L) : z ∈ Qθ Tag.E8 K := by
  haveI hcL : CharP D.L 2 := charP_L D hK
  haveI hAC : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  have hFr2 : ∀ c : D.L, D.Fr c = c ^ 2 := Fr_sq D hK
  have hbij : Function.Bijective D.Fr := by
    refine ⟨D.Fr.injective, fun a => ?_⟩
    obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq a (by norm_num : 0 < 2)
    exact ⟨b, by rw [hFr2, hb]⟩
  let σ : D.L ≃+* D.L := RingEquiv.ofBijective D.Fr hbij
  have hσ : ∀ c : D.L, σ c = c → c = 0 ∨ c = 1 := by
    intro c hc
    have h2 : c ^ 2 = c := by rw [← hFr2]; exact hc
    have h3 : c * (c - 1) = 0 := by linear_combination h2
    rcases mul_eq_zero.1 h3 with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.1 h)
  exact E8TwoD.mem_Qθ_of_baseChange_mem σ hσ (E8Two.eq_zero_or_one_of_card_two hK) hz hQ

end Char2

section Core

variable {K : Type} [Field K] [Finite K] (D : LangLevi TwClass.e8Ten.tag K TwClass.e8Ten.w)

@[expose] def ΨE (q : ModGL Tag.E8 K) : ModGL Tag.E8 D.L :=
  (gE D)⁻¹ * baseChangeGL (algebraMap K D.L) q * gE D

theorem ΨE_eq (q : ModGL Tag.E8 K) : ΨE D q = CoordsAux.Ψ D q := rfl

@[expose] def κF (q : ModGL Tag.E8 K) : Fn D.L := CoordsAux.κ D q

theorem κF_eq (q : ModGL Tag.E8 K) : κF D q = heisCoord Tag.E8 D.L (ΨE D q) := rfl

theorem ΨE_mul (q q' : ModGL Tag.E8 K) : ΨE D (q * q') = ΨE D q * ΨE D q' := by
  unfold ΨE
  rw [map_mul]
  group

theorem ΨE_one : ΨE D (1 : ModGL Tag.E8 K) = 1 := by
  unfold ΨE
  rw [map_one]
  group

theorem ΨE_inv (q : ModGL Tag.E8 K) : ΨE D q⁻¹ = (ΨE D q)⁻¹ := by
  unfold ΨE
  rw [map_inv]
  group

theorem ΨE_injective : Function.Injective (ΨE D (K := K)) := by
  intro x y h
  unfold ΨE at h
  apply baseChangeGL_injective (algebraMap K D.L)
  exact mul_left_cancel (mul_right_cancel h)

theorem bc_eq_conj (q : ModGL Tag.E8 K) :
    baseChangeGL (algebraMap K D.L) q = gE D * ΨE D q * (gE D)⁻¹ := by
  unfold ΨE
  group

theorem gE_mem_Lθ : gE D ∈ Lθ Tag.E8 D.L := D.g_mem

theorem ΨE_Qθ {q : ModGL Tag.E8 K} (hq : q ∈ Qθ Tag.E8 K) : ΨE D q ∈ Qθ Tag.E8 D.L :=
  CoordsAux.Ψ_Qθ D hq

@[expose] def Agp : Subgroup (ModGL Tag.E8 K) :=
  Subgroup.closure (((Rθ (TwClass.e8Ten.X₁ D) : Subgroup (ModGL Tag.E8 K)) :
      Set (ModGL Tag.E8 K)) ∪
    ((Heis.Uneg Tag.E8 K : Subgroup (ModGL Tag.E8 K)) : Set (ModGL Tag.E8 K)))

theorem Agp_le_X₁ (hb : TwBasic (TwClass.e8Ten.X₁ D) (TwClass.e8Ten.X₂ D)) :
    Agp D ≤ TwClass.e8Ten.X₁ D := by
  refine (Subgroup.closure_le _).2 ?_
  rintro x (hx | hx)
  · exact hx.1
  · exact hb.Uneg_le hx

theorem v_comm_R {v : ModGL Tag.E8 K} (hvQ : v ∈ Qθ Tag.E8 K)
    (hvs : ∀ β, κF D v β ≠ 0 → β ∉ CoordsAux.Bset TwClass.e8Ten)
    {r : ModGL Tag.E8 K} (hr : r ∈ Rθ (TwClass.e8Ten.X₁ D)) : r * v = v * r := by
  have hrX : r ∈ TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D := Subgroup.mem_sup_left hr.1
  exact CoordsAux.commute_of_disjoint_support TwClass.e8Ten D hr.2 hvQ
    (fun β hβ => CoordsAux.support_of_mem_X TwClass.e8Ten D hr.2 hrX β hβ) hvs

theorem conj_Agp_mem {H : Subgroup (ModGL Tag.E8 K)}
    (hXH : TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D ≤ H)
    {v : ModGL Tag.E8 K} (hvQ : v ∈ Qθ Tag.E8 K)
    (hvB : conjSub v (Heis.Uneg Tag.E8 K) ≤ H)
    (hvR : ∀ r : ModGL Tag.E8 K, r ∈ Rθ (TwClass.e8Ten.X₁ D) → r * v = v * r)
    {x : ModGL Tag.E8 K} (hx : x ∈ Agp D) : v * x * v⁻¹ ∈ H := by
  have hX₁H : TwClass.e8Ten.X₁ D ≤ H := le_sup_left.trans hXH
  refine Subgroup.closure_induction (p := fun x _ => v * x * v⁻¹ ∈ H) ?_ ?_ ?_ ?_ hx
  · rintro x (hx | hx)
    · have hc := hvR x hx
      have e : v * x * v⁻¹ = x := by
        rw [← hc]
        group
      rw [e]
      exact hX₁H hx.1
    · exact hvB (mem_conjSub_iff.2 (by
        have e : v⁻¹ * (v * x * v⁻¹) * v = x := by group
        rw [e]
        exact hx))
  · have e : v * (1 : ModGL Tag.E8 K) * v⁻¹ = 1 := by group
    rw [e]
    exact one_mem _
  · intro x y _ _ hx hy
    have e : v * (x * y) * v⁻¹ = (v * x * v⁻¹) * (v * y * v⁻¹) := by group
    rw [e]
    exact mul_mem hx hy
  · intro x _ hx
    have e : v * x⁻¹ * v⁻¹ = (v * x * v⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem hx

theorem notVS_of_support (hK : Nat.card K = 2) {m : ModGL Tag.E8 K}
    (hmQ : m ∈ Qθ Tag.E8 K) {μ : Fin Tag.E8.rank → ℤ}
    (hμ : μ ∉ CoordsAux.Bset TwClass.e8Ten) (hne : κF D m μ ≠ 0) :
    heisCoord Tag.E8 K m ∉ VS (TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D) := by
  have h2 : TwClass.e8Ten.minQ ≤ Nat.card K := by
    have : TwClass.e8Ten.minQ = 2 := rfl
    omega
  intro hVS
  have hco := twCoords TwClass.e8Ten K h2 D
  have hmX : m ∈ TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D := hco.inj m hmQ hVS
  exact hμ (CoordsAux.support_of_mem_X TwClass.e8Ten D hmQ hmX μ hne)

theorem RB_step (hK : Nat.card K = 2) {H : Subgroup (ModGL Tag.E8 K)}
    (hHG : H ≤ adjointGroup Tag.E8 K)
    (hb : TwBasic (TwClass.e8Ten.X₁ D) (TwClass.e8Ten.X₂ D))
    (hXH : TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D ≤ H)
    {v : ModGL Tag.E8 K} (hvQ : v ∈ Qθ Tag.E8 K)
    (hvB : conjSub v (Heis.Uneg Tag.E8 K) ≤ H)
    (hvR : ∀ r : ModGL Tag.E8 K, r ∈ Rθ (TwClass.e8Ten.X₁ D) → r * v = v * r)
    {x : ModGL Tag.E8 K} (hx : x ∈ Agp D) {M : Fn D.L →ₗ[D.L] Fn D.L}
    (hM : ActsBy (ΨE D x) M) {μ : Fin Tag.E8.rank → ℤ}
    (hμ : μ ∉ CoordsAux.Bset TwClass.e8Ten)
    (hne : κF D v μ - M (κF D v) μ ≠ 0) :
    ∃ m ∈ H, m ∈ Qθ Tag.E8 K ∧
      heisCoord Tag.E8 K m ∉ VS (TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D) := by
  have hX₁H : TwClass.e8Ten.X₁ D ≤ H := le_sup_left.trans hXH
  have hxX : x ∈ TwClass.e8Ten.X₁ D := Agp_le_X₁ D hb hx
  set m : ModGL Tag.E8 K := v * x * v⁻¹ * x⁻¹ with hm
  have hmH : m ∈ H := mul_mem (conj_Agp_mem D hXH hvQ hvB hvR hx) (inv_mem (hX₁H hxX))
  have hΨv : ΨE D v ∈ Qθ Tag.E8 D.L := ΨE_Qθ D hvQ
  obtain ⟨hcQ, hcc⟩ := hM _ (inv_mem hΨv)
  have hΨm : ΨE D m = ΨE D v * (ΨE D x * (ΨE D v)⁻¹ * (ΨE D x)⁻¹) := by
    rw [hm]
    simp only [ΨE_mul, ΨE_inv]
    group
  have hΨmQ : ΨE D m ∈ Qθ Tag.E8 D.L := by
    rw [hΨm]
    exact mul_mem hΨv hcQ
  have hκm : κF D m = κF D v - M (κF D v) := by
    rw [κF_eq, κF_eq, hΨm, (heisCoord_spec Tag.E8 D.L).mul _ hΨv _ hcQ, hcc,
      heisCoord_inv hΨv, map_neg]
    abel
  have hmQ' : m ∈ Qθ Tag.E8 K := by
    refine mem_Qθ_of_bc D hK (hHG hmH) ?_
    rw [bc_eq_conj D m]
    exact Lθ_conj_mem_Qθ (gE_mem_Lθ D) hΨmQ
  refine ⟨m, hmH, hmQ', notVS_of_support D hK hmQ' hμ ?_⟩
  have h1 : κF D m μ ≠ 0 := by
    rw [hκm]
    exact hne
  exact h1

end Core

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux
