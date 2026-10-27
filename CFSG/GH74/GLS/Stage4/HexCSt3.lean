module

public import CFSG.GH74.GLS.Stage4.HexCAsm1
public import CFSG.GH74.GLS.Stage4.HexCW3
public import CFSG.GH74.GLS.Stage4.HexCSolve3
public import CFSG.GH74.GLS.Stage4.HexCSolve2
public import CFSG.GH74.GLS.Stage4.HexCSt1
public import CFSG.GH74.GLS.Stage4.HexCWeylSlot

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

variable {G : Type} [Group G] {H : Subgroup G} {r₁ r₂ : G} {U : Subgroup G}
  {root : ℤ → Subgroup G} {F : Type} [Field F]

theorem exists_u_ne [Finite F] (h5 : 5 ≤ Nat.card F) : ∃ u : F, u ≠ 0 ∧ u ^ 2 ≠ 1 := by
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  have := Fintype.ofFinite F
  classical
  have hsub : (Finset.univ : Finset F) ⊆ {0, 1, -1} := by
    intro x _
    by_cases hx : x = 0
    · simp [hx]
    · have h := hcon x hx
      have h1 : (x - 1) * (x + 1) = 0 := by linear_combination h
      rcases mul_eq_zero.1 h1 with h | h
      · simp [show x = 1 by linear_combination h]
      · simp [show x = -1 by linear_combination h]
  have h3 : Fintype.card F ≤ 3 :=
    calc Fintype.card F = (Finset.univ : Finset F).card := Finset.card_univ.symm
      _ ≤ ({0, 1, -1} : Finset F).card := Finset.card_le_card hsub
      _ ≤ 3 := Finset.card_le_three
  rw [Nat.card_eq_fintype_card] at h5
  omega

theorem stage2_lin (R : RGD2 6 H r₁ r₂ U root) (hC : Hex6Comm root) (D : HexData root F)
    (h2 : (2 : F) ≠ 0) {u : F} (hu : u ≠ 0) (hu2 : u ^ 2 ≠ 1) {μ : G → F} (hμ : MuData D μ)
    {a2 a4 : F → F → F} {L : F → F → G} (hcd : CommData D a2 a4 L) {A2 A4 : F → F → F}
    {g3 : F → F → G} (had : ActData D A2 A4 g3) {n : G} (hnφ : n = D.φ (sl2W F))
    (hnact : ActsPos 6 root n (fun q => 4 - q)) :
    ∃ e : F, (∀ s t, a2 s t = 3 * e * s ^ 2 * t) ∧ (∀ s t, μ (L s t) = 6 * e * (s * t)) ∧
      (∀ s t, a4 s t = 3 * e * s * t ^ 2) ∧ (∀ c s, A2 c s = e * c * s ^ 3) ∧
      (∀ c s, μ (g3 c s) = 3 * e * c * s ^ 2) ∧ (∀ c s, A4 c s = 2 * e * c ^ 2 * s ^ 3) := by
  obtain ⟨e, hκ, ha2, hA2, hMg⟩ := stage1 R hC D h2 hμ hcd had
  have hmuL : ∀ s t, μ (L s t) = 6 * e * (s * t) := by
    intro s t
    rw [L_eq_mul R D hcd s t, mu_L R hC D hμ hcd, hκ]
  have ha4 : ∀ s t, a4 s t = 3 * e * s * t ^ 2 := by
    refine solve_a4 h2 e a4 (fun s s' t => (comm15_add_s R hC D hμ hcd s s' t).2.2)
      (fun s t t' => ?_) (fun τ s t => (comm15_torus R D hcd τ s t).2.2)
    have := (comm15_add_t R hC D hμ hcd s t t').2.2
    rwa [hmuL] at this
  obtain ⟨-, -, ⟨f₂, hf2⟩, -⟩ := weyl_coords D hnact
  obtain ⟨-, ⟨f₅, hf5⟩, -, -⟩ := weyl_coords D hnact
  obtain ⟨⟨f₁, hf1⟩, -, -, -⟩ := weyl_coords D hnact
  obtain ⟨-, -, -, ⟨f₄, hf4⟩⟩ := weyl_coords D hnact
  have hlin : ∀ x, f₂ x = x * f₂ 1 := weyl_lin D hnφ hf2
  have hA4 : ∀ c s, A4 c s = 2 * e * c ^ 2 * s ^ 3 := by
    refine solve_A4_lin h2 u hu hu2 e (f₂ 1) a4 A4 ha4 (fun c c' s => ?_) (fun c s s' => ?_)
      (fun τ c s => (act_torus R D had τ c s).2.2) (fun s => ?_)
    · have := (act_add_c R hC D hμ had c c' s).2.2
      rwa [hA2 c' s, hMg c s] at this
    · have := (act_add_s R hC D hμ hcd had c s s').2.2
      rwa [hμ.add _ (had.g3_mem c s') _ (hcd.L_mem s (c * s')), hMg c s', hmuL] at this
    · have := weyl_slot R hC D hcd had hnφ hnact hf1 hf5 hf2 hf4 s
      rw [hA2 1 s, hlin] at this
      linear_combination this
  exact ⟨e, ha2, hmuL, ha4, hA2, hMg, hA4⟩

theorem exists_Lam3 [Finite G] (D : HexData root F) {a2 a4 : F → F → F} {L : F → F → G}
    (hcd : CommData D a2 a4 L) (hLadd : ∀ u v, L 1 (u + v) = L 1 u * L 1 v)
    (hLinj : ∀ u, L 1 u = 1 → u = 0) (hcard : Nat.card (root 3) = Nat.card F) :
    Function.Injective (L 1) ∧ ∀ x ∈ root 3, ∃ u, L 1 u = x := by
  have hinj : Function.Injective (L 1) := by
    intro u v h
    have h1 : L 1 (u + -v) = 1 := by
      rw [hLadd, ← inv_eq_of_add (fun a b => hLadd a b) v, h, mul_inv_cancel]
    have := hLinj _ h1
    linear_combination this
  refine ⟨hinj, fun x hx => ?_⟩
  have hb : Function.Bijective (fun u : F => (⟨L 1 u, hcd.L_mem 1 u⟩ : root 3)) := by
    refine (Nat.bijective_iff_injective_and_card _).2 ⟨fun u v h => hinj (congrArg Subtype.val h),
      hcard.symm⟩
  obtain ⟨u, hu⟩ := hb.2 ⟨x, hx⟩
  exact ⟨u, congrArg Subtype.val hu⟩

theorem g3_eq_char3 (R : RGD2 6 H r₁ r₂ U root) (hC : Hex6Comm root) (D : HexData root F)
    (h2 : (2 : F) ≠ 0) (h3z : (3 : F) = 0) {μ : G → F} (hμ : MuData D μ) {a2 a4 : F → F → F}
    {L : F → F → G} (hcd : CommData D a2 a4 L) {A2 A4 : F → F → F} {g3 : F → F → G}
    (had : ActData D A2 A4 g3) (hLinj : Function.Injective (L 1))
    (hLsurj : ∀ x ∈ root 3, ∃ u, L 1 u = x) : ∀ c s, g3 c s = L 1 (-(c * s ^ 2)) := by
  choose γ hγ using fun c s => hLsurj (g3 c s) (had.g3_mem c s)
  have hLadd : ∀ u v, L 1 (u + v) = L 1 u * L 1 v := fun u v =>
    (comm15_add_t R hC D hμ hcd 1 u v).2.1
  have hLmul : ∀ s t, L s t = L 1 (s * t) := fun s t => L_eq_mul R D hcd s t
  have G1 : ∀ c c' s, γ (c + c') s = γ c' s + γ c s := by
    intro c c' s
    apply hLinj
    rw [hLadd, hγ, hγ, hγ]
    exact (act_add_c R hC D hμ had c c' s).2.1
  have G2 : ∀ c s s', γ c (s + s') = γ c s + γ c s' + s * (c * s') := by
    intro c s s'
    apply hLinj
    rw [hLadd, hLadd, hγ, hγ, hγ, ← hLmul]
    rw [(act_add_s R hC D hμ hcd had c s s').2.1, mul_assoc]
  have G3 : ∀ τ : Fˣ, ∀ c s, γ ((τ : F) ^ 2 * c) ((τ : F)⁻¹ * s) = γ c s := by
    intro τ c s
    apply hLinj
    rw [hγ, hγ]
    exact (act_torus R D had τ c s).2.1
  have hg := solve_gamma h2 γ G1 G2 G3
  intro c s
  rw [← hγ, hg]
  congr 1
  field_simp
  linear_combination (c * s ^ 2) * h3z

end CFSG.GH74.GLS.Stage4.Hex
