module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3PField
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04I117Rank

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.DFour
local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner


@[expose] def D3CaseTwoOneFour : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 3 →
    ∀ b x y : MulAut (D4Model K), b ^ 3 = 1 → b ∉ D4Img K → x ^ 2 = 1 → y ^ 2 = 1 →
      x * y = y * x → x ≠ 1 → y ≠ 1 → x ≠ y → b * x = x * b → b * y = y * b →
      ∀ A : Subgroup (D4Model K), IsElemAbelian 3 A → 9 ≤ Nat.card A →
        (∀ a ∈ A, b a = a) → (∀ a ∈ A, x a = a) → (∀ a ∈ A, y a = a) → False

theorem d3CaseTwoOne_of_four (hN : D3CaseTwoOneFour) : D3CaseTwoOne := by
  intro K _ _ hK E hE hEQ hcard T hT hT2 hnorm hfix ⟨b₀, hb₀E, hb₀Q, hb₀c⟩
  classical
  have hK' : Nat.card K = 3 ^ 1 := by simpa using hK
  have hf : 1 ≤ 1 := le_rfl
  obtain ⟨-, -, hcen⟩ := d4Facts2 Nat.prime_three (by norm_num) hf hK'
  have hcommE : ∀ x ∈ E, ∀ z ∈ E, x * z = z * x := fun x hx z hz => D3P.comm_of_elemAbelian hE hx hz
  have hcard' : 3 ^ (4 * 1) ≤ Nat.card E := by simpa using hcard
  have hnf := d3_nonfield d3FieldPair_holds hK' hE hEQ hcard'
  have hQE : (D4Img K ⊓ E : Subgroup (MulAut (D4Model K))) = E ⊓ Inn (D4Model K) := by
    ext y
    constructor
    · rintro ⟨hyQ, hyE⟩
      exact ⟨hyE, hnf y hyE hyQ⟩
    · rintro ⟨hyE, hyI⟩
      exact ⟨inner_le_D4Img hyI, hyE⟩
  obtain ⟨H, hHT, hHbot, hHnorm, hex, ⟨b₁, hb₁E, hb₁c⟩, hfpf, hdata⟩ :=
    D3P.exists_fourgroup E T hE hT2 hT hnorm hfix
  obtain ⟨x₀', hx₀'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hHbot
  set x₀ : MulAut (D4Model K) := (x₀' : MulAut (D4Model K)) with hx₀def
  have hx₀H : x₀ ∈ H := x₀'.2
  have hx₀1 : x₀ ≠ 1 := fun h => hx₀' (Subtype.ext h)
  obtain ⟨hcardE0, h1, h2, h3, h4, hHall⟩ := hdata b₁ hb₁E hb₁c x₀ hx₀H hx₀1
  set y₀ : MulAut (D4Model K) := b₁ * x₀ * b₁⁻¹ with hy₀def
  have hy₀H : y₀ ∈ H := D3P.conj_mem_of_normalizer (hHnorm hb₁E) hx₀H
  have hx₀2 : x₀ ^ 2 = 1 := by rw [pow_two]; exact (hex x₀ hx₀H).1
  have hy₀2 : y₀ ^ 2 = 1 := by rw [pow_two]; exact (hex y₀ hy₀H).1
  have hxy : x₀ * y₀ = y₀ * x₀ := (hex x₀ hx₀H).2 y₀ hy₀H
  set E₀ : Subgroup (MulAut (D4Model K)) :=
    E ⊓ Subgroup.centralizer (H : Set (MulAut (D4Model K))) with hE₀
  have hb₀E₀ : b₀ ∈ E₀ := ⟨hb₀E, Subgroup.mem_centralizer_iff.2 fun x hx => (hb₀c x (hHT hx)).symm⟩
  have hE₀el : IsElemAbelian 3 E₀ := ⟨⟨⟨fun a b => Subtype.ext (hcommE _ a.2.1 _ b.2.1)⟩⟩,
    fun x hx => hE.2 x hx.1⟩
  have hE₀Q : ¬ E₀ ≤ D4Img K := fun h => hb₀Q (h hb₀E₀)
  have hE₀card := d3_card_E_Q hK' hE₀el hE₀Q
  have hQE₀ : (D4Img K ⊓ E₀ : Subgroup (MulAut (D4Model K))) = E₀ ⊓ Inn (D4Model K) := by
    ext y
    constructor
    · rintro ⟨hyQ, hyE₀⟩
      have : y ∈ E ⊓ Inn (D4Model K) := by
        rw [← hQE]
        exact ⟨hyQ, hyE₀.1⟩
      exact ⟨hyE₀, this.2⟩
    · rintro ⟨hyE₀, hyI⟩
      exact ⟨inner_le_D4Img hyI, hyE₀⟩
  rw [hQE₀] at hE₀card
  set A : Subgroup (D4Model K) := innerPartAut E₀ with hA
  have hAel : IsElemAbelian 3 A := innerPart_elemAbelian hcen hE₀el
  have hAcard : Nat.card A = Nat.card (E₀ ⊓ Inn (D4Model K) : Subgroup (MulAut (D4Model K))) :=
    card_innerPart hcen E₀
  have h9 : Nat.card E = 9 * Nat.card A := by
    rw [hAcard, hcardE0]
    have : Nat.card ↥(E ⊓ Subgroup.centralizer (H : Set (MulAut (D4Model K)))) = Nat.card E₀ := rfl
    rw [this, hE₀card]
    ring
  have hA9 : 9 ≤ Nat.card A := by omega
  have hfixb : ∀ a ∈ A, b₀ a = a := fun a ha =>
    fixed_of_mem_innerPart (X := E₀) hcen (fun x hx => hcommE b₀ hb₀E x hx.1) ha
  have hfixH : ∀ t ∈ H, ∀ a ∈ A, t a = a := fun t ht a ha =>
    fixed_of_mem_innerPart (X := E₀) hcen (fun x hx => Subgroup.mem_centralizer_iff.1 hx.2 t ht) ha
  have hb₀3 : b₀ ^ 3 = 1 := hE.2 b₀ hb₀E
  have hb₀x : b₀ * x₀ = x₀ * b₀ := (hb₀c x₀ (hHT hx₀H))
  have hb₀y : b₀ * y₀ = y₀ * b₀ := (hb₀c y₀ (hHT hy₀H))
  have hy₀1 : y₀ ≠ 1 := h2
  have hxy₀ : x₀ ≠ y₀ := fun h => h1 h.symm
  exact hN K hK b₀ x₀ y₀ hb₀3 hb₀Q hx₀2 hy₀2 hxy hx₀1 hy₀1 hxy₀ hb₀x hb₀y A hAel hA9 hfixb
    (hfixH x₀ hx₀H) (hfixH y₀ hy₀H)

end CFSG.LocalAnalysis.GLTheoremA
