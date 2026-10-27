module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB44Elem
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB44Basic

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.OddStandard.Seitz77.CaseB45
  CFSG.LocalAnalysis.ComponentInitial.FieldFourCover CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

section Gen

variable {G : Type} [Group G]

theorem perfect_sup {H K : Subgroup G} (hH : ⁅H, H⁆ = H) (hK : ⁅K, K⁆ = K) :
    ⁅H ⊔ K, H ⊔ K⁆ = H ⊔ K := by
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact (H ⊔ K).mul_mem ((H ⊔ K).mul_mem ((H ⊔ K).mul_mem ha hb) ((H ⊔ K).inv_mem ha))
      ((H ⊔ K).inv_mem hb)
  · calc H = ⁅H, H⁆ := hH.symm
      _ ≤ ⁅H ⊔ K, H ⊔ K⁆ := Subgroup.commutator_mono le_sup_left le_sup_left
  · calc K = ⁅K, K⁆ := hK.symm
      _ ≤ ⁅H ⊔ K, H ⊔ K⁆ := Subgroup.commutator_mono le_sup_right le_sup_right

theorem le_normalizer_sup_of_cent_norm [Finite G] {K X Y : Subgroup G}
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) (hKY : ∀ k ∈ K, ∀ y ∈ Y, k * y = y * k)
    (hKX : ∀ k ∈ K, ∀ x ∈ X, k * x * k⁻¹ ∈ X) : K ≤ normalizer ((X ⊔ Y : Subgroup G) : Set G) := by
  intro k hk
  refine Subgroup.mem_normalizer_fintype fun w hw => ?_
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_sup_of_forall_comm (O := X) (E := Y) hXY hw
  have hky : k * y * k⁻¹ = y := by rw [hKY k hk y hy]; group
  have e : k * (x * y) * k⁻¹ = (k * x * k⁻¹) * y := by
    calc k * (x * y) * k⁻¹ = (k * x * k⁻¹) * (k * y * k⁻¹) := by group
      _ = (k * x * k⁻¹) * y := by rw [hky]
  show k * (x * y) * k⁻¹ ∈ X ⊔ Y
  rw [e]
  exact mul_mem (mem_sup_left (hKX k hk x hx)) (mem_sup_right hy)

theorem inf_eq_of_W_eq {A B X W M₁ M₂ S : Subgroup G} {t : G} (P : SwapPair A B t)
    (hX : X ≤ A) (hW : W = X ⊔ cs t X) (hS₁ : S ⊓ M₁ = A) (hS₂ : S ⊓ M₂ = B) (hWS : W ≤ S) :
    W ⊓ M₁ = X ∧ W ⊓ M₂ = cs t X := by
  have hXW : X ≤ W := hW ▸ le_sup_left
  have hcsW : cs t X ≤ W := hW ▸ le_sup_right
  have hA : A ≤ M₁ := hS₁ ▸ inf_le_right
  have hB : B ≤ M₂ := hS₂ ▸ inf_le_right
  have hcsB : cs t X ≤ B := P.cs_le hX
  constructor
  · refine le_antisymm (fun y hy => ?_) (le_inf hXW (hX.trans hA))
    have hyA : y ∈ A := hS₁ ▸ (⟨hWS hy.1, hy.2⟩ : y ∈ S ⊓ M₁)
    have hyW : y ∈ X ⊔ cs t X := hW ▸ hy.1
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_forall_comm (O := X) (E := cs t X)
      (fun x hx z hz => P.comm_X_cs hX hx hz) hyW
    have hb1 : b ∈ A ⊓ B := ⟨by
      have := A.mul_mem (A.inv_mem (hX ha)) hyA
      simpa using this, hcsB hb⟩
    rw [P.inf_eq, Subgroup.mem_bot] at hb1
    rw [hb1, mul_one]
    exact ha
  · refine le_antisymm (fun y hy => ?_) (le_inf hcsW (hcsB.trans hB))
    have hyB : y ∈ B := hS₂ ▸ (⟨hWS hy.1, hy.2⟩ : y ∈ S ⊓ M₂)
    have hyW : y ∈ X ⊔ cs t X := hW ▸ hy.1
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_forall_comm (O := X) (E := cs t X)
      (fun x hx z hz => P.comm_X_cs hX hx hz) hyW
    have ha1 : a ∈ A ⊓ B := ⟨hX ha, by
      have := B.mul_mem hyB (B.inv_mem (hcsB hb))
      simpa using this⟩
    rw [P.inf_eq, Subgroup.mem_bot] at ha1
    rw [ha1, one_mul]
    exact hb

end Gen

section CS

variable {G : Type} [Group G] [Finite G] {A V₁ V₂ : Subgroup G} {d : Datum A}
  {c₁ : CaseB A V₁ d.t} {c₂ : CaseB A V₂ d.t} {M₁ M₂ N₁ N₂ S A₁ B₁ : Subgroup G} {k : Type}
  [Field k] {e : ↥A₁ ≃* ↥(unipAll k)} (CS : CommonSylow c₁ c₂ M₁ M₂ N₁ N₂ S A₁ B₁ e)

include CS

theorem CommonSylow.loc (hZ₁ : c₁.OddCoreCentral) (hZ₂ : c₂.OddCoreCentral) :
    ∀ W : Subgroup G, W ≤ S → IsElemAbelian 2 W → Nat.card W = 2 ^ 8 →
      S ≤ perfectResidualOf (normalizer (W : Set G) ⊓ (M₁ ⊔ N₁ ⊔ (M₂ ⊔ N₂))) := by
  intro W hWS hW hcard
  have hk := CS.syl.card_k
  have P := CS.swapPair
  obtain ⟨E₁, E₂, hE₁, hE₂, hWeq⟩ := P.elem_classify (e := e) hk (hWS.trans CS.S_eq.le) hW hcard
  have aux : ∀ H : Subgroup G, ⁅H, H⁆ = H → H ≤ M₁ ⊔ N₁ ⊔ (M₂ ⊔ N₂) → S ≤ H →
      H ≤ normalizer (W : Set G) →
      S ≤ perfectResidualOf (normalizer (W : Set G) ⊓ (M₁ ⊔ N₁ ⊔ (M₂ ⊔ N₂))) :=
    fun H hperf hG hSH hN => hSH.trans (le_prOf hperf (le_inf hN hG))
  have hM₁G : M₁ ≤ M₁ ⊔ N₁ ⊔ (M₂ ⊔ N₂) := le_sup_left.trans le_sup_left
  have hN₁G : N₁ ≤ M₁ ⊔ N₁ ⊔ (M₂ ⊔ N₂) := le_sup_right.trans le_sup_left
  have hM₂G : M₂ ≤ M₁ ⊔ N₁ ⊔ (M₂ ⊔ N₂) := le_sup_left.trans le_sup_right
  have hN₂G : N₂ ≤ M₁ ⊔ N₁ ⊔ (M₂ ⊔ N₂) := le_sup_right.trans le_sup_right
  have hI₁ := inf_eq_of_W_eq P (radIn_le (E₀ := radOne k)) CS.W₁_eq CS.syl.A₁_eq.symm
    CS.syl.B₁_eq.symm CS.W₁_le_S
  have hI₂ := inf_eq_of_W_eq P (radIn_le (E₀ := radTwo k)) CS.W₂_eq CS.A_eq CS.B_eq CS.W₂_le_S
  have hM₁X₁ : ∀ m ∈ M₁, ∀ x ∈ radIn A₁ e (radOne k), m * x * m⁻¹ ∈ radIn A₁ e (radOne k) := by
    intro m hm x hx
    rw [← hI₁.1] at hx ⊢
    exact ⟨(mem_normalizer_iff.mp (prOf_le c₁.N (CS.F₁.M₁_le hm)) x).mp hx.1,
      M₁.mul_mem (M₁.mul_mem hm hx.2) (M₁.inv_mem hm)⟩
  have hM₂X₁ : ∀ m ∈ M₂, ∀ x ∈ cs d.t (radIn A₁ e (radOne k)),
      m * x * m⁻¹ ∈ cs d.t (radIn A₁ e (radOne k)) := by
    intro m hm x hx
    rw [← hI₁.2] at hx ⊢
    exact ⟨(mem_normalizer_iff.mp (prOf_le c₁.N (CS.F₁.M₂_le hm)) x).mp hx.1,
      M₂.mul_mem (M₂.mul_mem hm hx.2) (M₂.inv_mem hm)⟩
  have hN₁X₂ : ∀ m ∈ N₁, ∀ x ∈ radIn A₁ e (radTwo k), m * x * m⁻¹ ∈ radIn A₁ e (radTwo k) := by
    intro m hm x hx
    rw [← hI₂.1] at hx ⊢
    exact ⟨(mem_normalizer_iff.mp (prOf_le c₂.N (CS.F₂.M₁_le hm)) x).mp hx.1,
      N₁.mul_mem (N₁.mul_mem hm hx.2) (N₁.inv_mem hm)⟩
  have hN₂X₂ : ∀ m ∈ N₂, ∀ x ∈ cs d.t (radIn A₁ e (radTwo k)),
      m * x * m⁻¹ ∈ cs d.t (radIn A₁ e (radTwo k)) := by
    intro m hm x hx
    rw [← hI₂.2] at hx ⊢
    exact ⟨(mem_normalizer_iff.mp (prOf_le c₂.N (CS.F₂.M₂_le hm)) x).mp hx.1,
      N₂.mul_mem (N₂.mul_mem hm hx.2) (N₂.inv_mem hm)⟩
  have hXY : ∀ X Y : Subgroup G, X ≤ A₁ → Y ≤ A₁ → ∀ x ∈ X, ∀ y ∈ cs d.t Y, x * y = y * x :=
    fun X Y hX hY x hx y hy => P.comm x (hX hx) y (P.cs_le hY hy)
  have hM₁c : ∀ Y : Subgroup G, Y ≤ A₁ → ∀ m ∈ M₁, ∀ y ∈ cs d.t Y, m * y = y * m :=
    fun Y hY m hm y hy => CS.F₁.comm_elem hZ₁ hm (CS.B₁_le_M₂ (P.cs_le hY hy))
  have hN₁c : ∀ Y : Subgroup G, Y ≤ A₁ → ∀ m ∈ N₁, ∀ y ∈ cs d.t Y, m * y = y * m :=
    fun Y hY m hm y hy => CS.F₂.comm_elem hZ₂ hm (CS.B₁_le_N₂ (P.cs_le hY hy))
  have hM₂c : ∀ X : Subgroup G, X ≤ A₁ → ∀ m ∈ M₂, ∀ x ∈ X, m * x = x * m :=
    fun X hX m hm x hx => (CS.F₁.comm_elem hZ₁ (CS.A₁_le_M₁ (hX hx)) hm).symm
  have hN₂c : ∀ X : Subgroup G, X ≤ A₁ → ∀ m ∈ N₂, ∀ x ∈ X, m * x = x * m :=
    fun X hX m hm x hx => (CS.F₂.comm_elem hZ₂ (CS.A₁_le_N₁ (hX hx)) hm).symm
  rcases hE₁ with rfl | rfl <;> rcases hE₂ with rfl | rfl
  ·
    have hW₁ : W = c₁.W := hWeq.trans CS.W₁_eq.symm
    exact aux c₁.Ninf c₁.Ninf_perfect (CS.ninf₁ ▸ sup_le hM₁G hM₂G)
      CS.syl.S₀_sylow.le (by rw [hW₁]; exact prOf_le c₁.N)
  ·
    have hNM : M₁ ≤ normalizer (W : Set G) := by
      rw [hWeq]
      exact le_normalizer_sup_of_cent_norm (hXY _ _ radIn_le radIn_le) (hM₁c _ radIn_le) hM₁X₁
    have hNN : N₂ ≤ normalizer (W : Set G) := by
      rw [hWeq, sup_comm]
      refine le_normalizer_sup_of_cent_norm
        (fun x hx y hy => (hXY _ _ radIn_le radIn_le y hy x hx).symm) (hN₂c _ radIn_le) hN₂X₂
    exact aux (M₁ ⊔ N₂) (perfect_sup CS.F₁.perfect₁ CS.F₂.perfect₂) (sup_le hM₁G hN₂G)
      (CS.S_eq ▸ sup_le (CS.A₁_le_M₁.trans le_sup_left) (CS.B₁_le_N₂.trans le_sup_right))
      (sup_le hNM hNN)
  ·
    have hNN : N₁ ≤ normalizer (W : Set G) := by
      rw [hWeq]
      exact le_normalizer_sup_of_cent_norm (hXY _ _ radIn_le radIn_le) (hN₁c _ radIn_le) hN₁X₂
    have hNM : M₂ ≤ normalizer (W : Set G) := by
      rw [hWeq, sup_comm]
      refine le_normalizer_sup_of_cent_norm
        (fun x hx y hy => (hXY _ _ radIn_le radIn_le y hy x hx).symm) (hM₂c _ radIn_le) hM₂X₁
    exact aux (N₁ ⊔ M₂) (perfect_sup CS.F₂.perfect₁ CS.F₁.perfect₂) (sup_le hN₁G hM₂G)
      (CS.S_eq ▸ sup_le (CS.A₁_le_N₁.trans le_sup_left) (CS.B₁_le_M₂.trans le_sup_right))
      (sup_le hNN hNM)
  ·
    have hW₂ : W = c₂.W := hWeq.trans CS.W₂_eq.symm
    exact aux c₂.Ninf c₂.Ninf_perfect (CS.ninf₂ ▸ sup_le hN₁G hN₂G)
      CS.S_sylow₂.le (by rw [hW₂]; exact prOf_le c₂.N)

end CS

end CFSG.OddStandard.Seitz77
