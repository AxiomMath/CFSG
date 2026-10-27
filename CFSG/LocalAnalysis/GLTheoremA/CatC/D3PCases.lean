module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3PFour
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3FAlg
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04D3Split

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.DFour
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

section InnerPart

variable {P : Type} [Group P]

def innerPartAut (X : Subgroup (MulAut P)) : Subgroup P := X.comap (MulAut.conj : P →* MulAut P)

theorem card_innerPart (hcen : Subgroup.center P = ⊥) [Finite P] (X : Subgroup (MulAut P)) :
    Nat.card (innerPartAut X) = Nat.card (X ⊓ Inn P : Subgroup (MulAut P)) := by
  have hinj := CFSG.HardMathSupport.Timmesfeld.ComponentBalance.conj_injective_of_center_eq_bot hcen
  have hmap : (innerPartAut X).map (MulAut.conj : P →* MulAut P) = X ⊓ Inn P := by
    rw [innerPartAut, Subgroup.map_comap_eq, inf_comm]
    rfl
  rw [← hmap, Subgroup.card_map_of_injective hinj]

theorem innerPart_elemAbelian (hcen : Subgroup.center P = ⊥) {p : ℕ} {X : Subgroup (MulAut P)}
    (hX : IsElemAbelian p X) : IsElemAbelian p (innerPartAut X) := by
  have hinj := CFSG.HardMathSupport.Timmesfeld.ComponentBalance.conj_injective_of_center_eq_bot hcen
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
  · apply Subtype.ext
    apply hinj
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact D3P.comm_of_elemAbelian hX a.2 b.2
  · apply hinj
    rw [map_pow, map_one]
    exact hX.2 _ ha

theorem fixed_of_mem_innerPart (hcen : Subgroup.center P = ⊥) {X : Subgroup (MulAut P)}
    {e : MulAut P} (he : ∀ x ∈ X, e * x = x * e) {a : P} (ha : a ∈ innerPartAut X) : e a = a :=
  CFSG.HardMathSupport.Timmesfeld.DFour.fixed_of_commute_conj hcen (he _ ha)

end InnerPart

section Defs

@[expose] def D3FieldPair : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), Nat.card K = 3 ^ n →
    ∀ y b : MulAut (D4Model K), y ^ 3 = 1 → b ^ 3 = 1 → y * b = b * y → y ∈ D4Img K →
      y ∉ Inn (D4Model K) → b ∉ D4Img K →
      ∀ A : Subgroup (D4Model K), IsElemAbelian 3 A → (∀ a ∈ A, y a = a) → (∀ a ∈ A, b a = a) →
        Nat.card A ≤ 3 ^ (2 * n)

@[expose] def D3A4Fixed : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), Nat.card K = 3 ^ n →
    ∀ b t₁ t₂ : MulAut (D4Model K), b ^ 3 = 1 → b ∉ D4Img K → t₁ ^ 2 = 1 → t₂ ^ 2 = 1 →
      t₁ * t₂ = t₂ * t₁ → t₁ ≠ 1 → t₂ ≠ 1 → t₁ ≠ t₂ → b * t₁ = t₂ * b → b * t₂ = t₁ * t₂ * b →
      ∀ A : Subgroup (D4Model K), IsElemAbelian 3 A → 3 ^ (4 * n) ≤ 3 * Nat.card A →
        (∀ a ∈ A, b a = a) → (∀ a ∈ A, t₁ a = a) → (∀ a ∈ A, t₂ a = a) → False

@[expose] def D3A4Borel : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), Nat.card K = 3 ^ n →
    ∀ b t₁ t₂ : MulAut (D4Model K), b ^ 3 = 1 → b ∉ D4Img K → t₁ ^ 2 = 1 → t₂ ^ 2 = 1 →
      t₁ * t₂ = t₂ * t₁ → t₁ ≠ 1 → t₂ ≠ 1 → t₁ ≠ t₂ → b * t₁ = t₂ * b → b * t₂ = t₁ * t₂ * b →
      ∀ A : Subgroup (D4Model K), IsElemAbelian 3 A → 3 ^ (4 * n) ≤ 3 * Nat.card A →
        (∀ a ∈ A, b a = a) → (∀ a ∈ A, t₁ a = a) → (∀ a ∈ A, t₂ a = a) →
        ∀ S : Sylow 3 (D4Model K), A ≤ (S : Subgroup (D4Model K)) →
          (S : Subgroup (D4Model K)).map b.toMonoidHom = S →
          (S : Subgroup (D4Model K)).map t₁.toMonoidHom = S → False

@[expose] def D3A4Regular : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), Nat.card K = 3 ^ n →
    ∀ b t₁ t₂ : MulAut (D4Model K), b ^ 3 = 1 → b ∉ D4Img K → t₁ ^ 2 = 1 → t₂ ^ 2 = 1 →
      t₁ * t₂ = t₂ * t₁ → t₁ ≠ 1 → t₂ ≠ 1 → t₁ ≠ t₂ → b * t₁ = t₂ * b → b * t₂ = t₁ * t₂ * b →
      ∀ A : Subgroup (D4Model K), IsElemAbelian 3 A → 3 ^ (4 * n) ≤ 3 * Nat.card A →
        (∀ a ∈ A, b a = a) → (∀ a ∈ A, t₁ a = a) → (∀ a ∈ A, t₂ a = a) →
        ∀ S : Sylow 3 (D4Model K), A ≤ (S : Subgroup (D4Model K)) →
          (S : Subgroup (D4Model K)).map b.toMonoidHom = S →
          (S : Subgroup (D4Model K)).map t₁.toMonoidHom ≠ S → False

@[expose] def D3CaseTwoOne : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 3 →
    ∀ E : Subgroup (MulAut (D4Model K)), IsElemAbelian 3 E → ¬ E ≤ D4Img K → 81 ≤ Nat.card E →
      ∀ T : Subgroup (MulAut (D4Model K)), T ≠ ⊥ → IsPGroup 2 T →
        E ≤ Subgroup.normalizer (T : Set (MulAut (D4Model K))) →
        (∀ x ∈ T, (∀ e ∈ E, e * x = x * e) → x = 1) →
        (∃ b ∈ E, b ∉ D4Img K ∧ ∀ x ∈ T, b * x = x * b) → False

theorem d3A4Fixed_of_borel_regular (hB : D3A4Borel) (hR : D3A4Regular) : D3A4Fixed := by
  intro K _ _ n hK b t₁ t₂ hb3 hbQ ht₁2 ht₂2 hcomm h1 h2 h12 hbt₁ hbt₂ A hA hAbig hfb hf₁ hf₂
  classical
  haveI : Finite (D4Model K) := inferInstance
  obtain ⟨S, hAS, hSb⟩ := exists_stable_sylow_fixing b hb3 A hA hfb
  by_cases hS : (S : Subgroup (D4Model K)).map t₁.toMonoidHom = S
  · exact hB K n hK b t₁ t₂ hb3 hbQ ht₁2 ht₂2 hcomm h1 h2 h12 hbt₁ hbt₂ A hA hAbig hfb hf₁ hf₂ S
      hAS hSb hS
  · exact hR K n hK b t₁ t₂ hb3 hbQ ht₁2 ht₂2 hcomm h1 h2 h12 hbt₁ hbt₂ A hA hAbig hfb hf₁ hf₂ S
      hAS hSb hS

end Defs

section Reduction

variable {K : Type} [Field K] [Finite K]

theorem d3_card_E_Q {n : ℕ} (hK : Nat.card K = 3 ^ n) {E : Subgroup (MulAut (D4Model K))}
    (hE : IsElemAbelian 3 E) (hEQ : ¬ E ≤ D4Img K) :
    Nat.card E = 3 * Nat.card (D4Img K ⊓ E : Subgroup (MulAut (D4Model K))) := by
  have hf : 1 ≤ n := one_le_of_card_field hK
  obtain ⟨-, -, -, -, hidx⟩ := d4Facts Nat.prime_three (by norm_num) hf hK
  have hrel : (D4Img K).relIndex E * Nat.card (D4Img K ⊓ E : Subgroup (MulAut (D4Model K)))
      = Nat.card E := Subgroup.relIndex_mul_card _ _
  have hle3 := relIndex_le_three hidx E
  have hne1 : (D4Img K).relIndex E ≠ 1 := fun h => hEQ (Subgroup.relIndex_eq_one.1 h)
  obtain ⟨k, hk⟩ := exists_card_eq_pow_of_isElemAbelian Nat.prime_three hE
  have hdvd : (D4Img K).relIndex E ∣ 3 ^ k := ⟨_, by rw [← hk, ← hrel]⟩
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have hi1 : i = 1 := by
    rcases i with _ | _ | i
    · exact absurd (by simpa using hi) hne1
    · rfl
    · exfalso
      have : 3 ^ (i + 2) ≤ 3 := hi ▸ hle3
      have h9 : 9 ≤ 3 ^ (i + 2) := by
        calc 9 = 3 ^ 2 := by norm_num
          _ ≤ 3 ^ (i + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  rw [hi, hi1, pow_one] at hrel
  exact hrel.symm

theorem inner_le_D4Img : Inn (D4Model K) ≤ D4Img K :=
  (inner_le_linearRange (coordinateQuadPlus 4 K)).trans (linearRange_le_image _)

theorem d3_nonfield (hFR : D3FieldPair) {n : ℕ} (hK : Nat.card K = 3 ^ n)
    {E : Subgroup (MulAut (D4Model K))} (hE : IsElemAbelian 3 E) (hEQ : ¬ E ≤ D4Img K)
    (hcard : 3 ^ (4 * n) ≤ Nat.card E) :
    ∀ y ∈ E, y ∈ D4Img K → y ∈ Inn (D4Model K) := by
  intro y hyE hyQ
  by_contra hyI
  have hf : 1 ≤ n := one_le_of_card_field hK
  obtain ⟨-, -, hcen⟩ := d4Facts2 Nat.prime_three (by norm_num) hf hK
  obtain ⟨b, hbE, hbQ⟩ := Set.not_subset.mp hEQ
  obtain ⟨h9, h3⟩ := d3_card_le_nine_inner hK E hE
  have hcommE : ∀ x ∈ E, ∀ z ∈ E, x * z = z * x := fun x hx z hz => D3P.comm_of_elemAbelian hE hx hz
  set A' : Subgroup (MulAut (D4Model K)) := E ⊓ Inn (D4Model K) with hA'
  have hAQ : A' ≤ D4Img K ⊓ E := fun x hx => ⟨inner_le_D4Img hx.2, hx.1⟩
  have hyQE : y ∈ D4Img K ⊓ E := ⟨hyQ, hyE⟩
  have hyA' : y ∉ A' := fun h => hyI h.2
  have hEQcard := d3_card_E_Q hK hE hEQ
  have hQE : IsElemAbelian 3 (D4Img K ⊓ E : Subgroup (MulAut (D4Model K))) :=
    ⟨⟨⟨fun a b => Subtype.ext (hcommE _ a.2.2 _ b.2.2)⟩⟩, fun x hx => hE.2 x hx.2⟩
  obtain ⟨j, hj⟩ := exists_card_eq_pow_of_isElemAbelian Nat.prime_three hQE
  have hrel : A'.relIndex (D4Img K ⊓ E : Subgroup (MulAut (D4Model K))) *
      Nat.card (A' ⊓ (D4Img K ⊓ E) : Subgroup (MulAut (D4Model K))) =
      Nat.card (D4Img K ⊓ E : Subgroup (MulAut (D4Model K))) := Subgroup.relIndex_mul_card _ _
  rw [inf_eq_left.2 hAQ] at hrel
  have hrne1 : A'.relIndex (D4Img K ⊓ E : Subgroup (MulAut (D4Model K))) ≠ 1 := fun h =>
    hyA' (Subgroup.relIndex_eq_one.1 h hyQE)
  have hrdvd : A'.relIndex (D4Img K ⊓ E : Subgroup (MulAut (D4Model K))) ∣ 3 ^ j :=
    ⟨_, by rw [← hj, ← hrel]⟩
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hrdvd
  have h3le : 3 ≤ A'.relIndex (D4Img K ⊓ E : Subgroup (MulAut (D4Model K))) := by
    rcases i with _ | i
    · exact absurd (by simpa using hi) hrne1
    · rw [hi]
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ (i + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hApos : 0 < Nat.card A' := Nat.card_pos
  have hE9 : 9 * Nat.card A' ≤ Nat.card E := by
    rw [hEQcard, ← hrel]
    calc 9 * Nat.card A' = 3 * (3 * Nat.card A') := by ring
      _ ≤ 3 * (A'.relIndex (D4Img K ⊓ E : Subgroup (MulAut (D4Model K))) * Nat.card A') :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h3le)
  by_cases h3n : 3 ∣ n
  · have hn3 : 3 ≤ n := Nat.le_of_dvd (by omega) h3n
    obtain ⟨hAel, hfixy, hfixb, hAcard⟩ : IsElemAbelian 3 (innerPartAut E) ∧
        (∀ a ∈ innerPartAut E, y a = a) ∧ (∀ a ∈ innerPartAut E, b a = a) ∧
        Nat.card (innerPartAut E) = Nat.card A' :=
      ⟨innerPart_elemAbelian hcen hE, fun a ha => fixed_of_mem_innerPart hcen
        (fun x hx => hcommE y hyE x hx) ha, fun a ha => fixed_of_mem_innerPart hcen
        (fun x hx => hcommE b hbE x hx) ha, card_innerPart hcen E⟩
    have hfield := hFR K n hK y b (hE.2 y hyE) (hE.2 b hbE) (hcommE y hyE b hbE) hyQ hyI hbQ
      (innerPartAut E) hAel hfixy hfixb
    rw [hAcard] at hfield
    have h1 : 3 ^ (4 * n) ≤ 3 ^ (2 * n + 2) := hcard.trans (h9.trans (by
      calc 9 * Nat.card A' ≤ 9 * 3 ^ (2 * n) := Nat.mul_le_mul_left _ hfield
        _ = 3 ^ (2 * n + 2) := by rw [pow_add]; ring))
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 h1
    omega
  · have := h3 h3n
    omega

theorem d3FixedPointFree_of_cases (hI : D3InnerInvolution) (hF : D3FieldInvolution)
    (hFR : D3FieldPair) (hA4 : D3A4Fixed) (hN : D3CaseTwoOne) : D3FixedPointFree := by
  intro K _ _ n hK E hE hEQ hcard T hT hT2 hnorm hfix
  classical
  have hf : 1 ≤ n := one_le_of_card_field hK
  obtain ⟨-, -, hcen⟩ := d4Facts2 Nat.prime_three (by norm_num) hf hK
  have hcommE : ∀ x ∈ E, ∀ z ∈ E, x * z = z * x := fun x hx z hz => D3P.comm_of_elemAbelian hE hx hz
  have hnf := d3_nonfield hFR hK hE hEQ hcard
  have hEQcard := d3_card_E_Q hK hE hEQ
  have hQE : (D4Img K ⊓ E : Subgroup (MulAut (D4Model K))) = E ⊓ Inn (D4Model K) := by
    ext y
    constructor
    · rintro ⟨hyQ, hyE⟩
      exact ⟨hyE, hnf y hyE hyQ⟩
    · rintro ⟨hyE, hyI⟩
      exact ⟨inner_le_D4Img hyI, hyE⟩
  have hEA : Nat.card E = 3 * Nat.card (E ⊓ Inn (D4Model K) : Subgroup (MulAut (D4Model K))) := by
    rw [hEQcard, hQE]
  obtain ⟨H, hHT, hHbot, hHnorm, hex, ⟨b₀, hb₀E, hb₀c⟩, hfpf, hdata⟩ :=
    D3P.exists_fourgroup E T hE hT2 hT hnorm hfix
  obtain ⟨x₀', hx₀'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hHbot
  set x₀ : MulAut (D4Model K) := (x₀' : MulAut (D4Model K)) with hx₀def
  have hx₀H : x₀ ∈ H := x₀'.2
  have hx₀1 : x₀ ≠ 1 := fun h => hx₀' (Subtype.ext h)
  obtain ⟨hcardE0, h1, h2, h3, h4, hHall⟩ := hdata b₀ hb₀E hb₀c x₀ hx₀H hx₀1
  have hH2 : IsPGroup 2 H := hT2.of_injective (Subgroup.inclusion hHT) (Subgroup.inclusion_injective hHT)
  have hHfix : ∀ x ∈ H, (∀ e ∈ E, e * x = x * e) → x = 1 := fun x hx hc => hfix x (hHT hx) hc
  by_cases hcaseI : ∀ a ∈ E ⊓ Inn (D4Model K), a ∈ Subgroup.centralizer (H : Set (MulAut (D4Model K)))
  ·
    have hb₀Q : b₀ ∉ D4Img K := fun hQ => hb₀c (hcaseI b₀ (hQE ▸ ⟨hQ, hb₀E⟩))
    have hb₀3 : b₀ ^ 3 = 1 := hE.2 b₀ hb₀E
    set t₂ : MulAut (D4Model K) := b₀ * x₀ * b₀⁻¹ with ht₂def
    have ht₂H : t₂ ∈ H := D3P.conj_mem_of_normalizer (hHnorm hb₀E) hx₀H
    have hx₀2 : x₀ ^ 2 = 1 := by rw [pow_two]; exact (hex x₀ hx₀H).1
    have ht₂2 : t₂ ^ 2 = 1 := by rw [pow_two]; exact (hex t₂ ht₂H).1
    have hcomm : x₀ * t₂ = t₂ * x₀ := (hex x₀ hx₀H).2 t₂ ht₂H
    have hbt₁ : b₀ * x₀ = t₂ * b₀ := by rw [ht₂def]; group
    have hbt₂ : b₀ * t₂ = x₀ * t₂ * b₀ := by
      calc b₀ * t₂ = (b₀ * t₂ * b₀⁻¹) * b₀ := by group
        _ = (x₀ * t₂) * b₀ := by rw [ht₂def, h3]
    set A : Subgroup (D4Model K) := innerPartAut E with hA
    have hAel : IsElemAbelian 3 A := innerPart_elemAbelian hcen hE
    have hAcard : Nat.card A = Nat.card (E ⊓ Inn (D4Model K) : Subgroup (MulAut (D4Model K))) :=
      card_innerPart hcen E
    have hAbig : 3 ^ (4 * n) ≤ 3 * Nat.card A := by rw [hAcard, ← hEA]; exact hcard
    have hfixb : ∀ a ∈ A, b₀ a = a := fun a ha =>
      fixed_of_mem_innerPart hcen (fun x hx => hcommE b₀ hb₀E x hx) ha
    have hfixH : ∀ t ∈ H, ∀ a ∈ A, t a = a := by
      intro t ht a ha
      have hcc := hcaseI (MulAut.conj a) ⟨ha, ⟨a, rfl⟩⟩
      exact CFSG.HardMathSupport.Timmesfeld.DFour.fixed_of_commute_conj hcen
        (Subgroup.mem_centralizer_iff.1 hcc t ht)
    exact hA4 K n hK b₀ x₀ t₂ hb₀3 hb₀Q hx₀2 ht₂2 hcomm hx₀1 h2 (fun h => h1 h.symm) hbt₁ hbt₂ A
      hAel hAbig hfixb (hfixH x₀ hx₀H) (hfixH t₂ ht₂H)
  ·
    push Not at hcaseI
    obtain ⟨a₁, ha₁, ha₁c⟩ := hcaseI
    set E₀ : Subgroup (MulAut (D4Model K)) :=
      E ⊓ Subgroup.centralizer (H : Set (MulAut (D4Model K))) with hE₀
    have hE₀E : E₀ ≤ E := inf_le_left
    have hE₀el : IsElemAbelian 3 E₀ := ⟨⟨⟨fun a b => Subtype.ext (hcommE _ a.2.1 _ b.2.1)⟩⟩,
      fun x hx => hE.2 x hx.1⟩
    obtain ⟨b', hb'E₀, hb'Q⟩ : ∃ b' ∈ E₀, b' ∉ D4Img K := by
      by_contra hcon
      push Not at hcon
      have hle : E₀ ≤ E ⊓ Inn (D4Model K) := by
        intro y hy
        rw [← hQE]
        exact ⟨hcon y hy, hy.1⟩
      have hcA : Nat.card (E ⊓ Inn (D4Model K) : Subgroup (MulAut (D4Model K))) ≤ Nat.card E₀ := by
        omega
      have heq := Subgroup.eq_of_le_of_card_ge hle hcA
      apply ha₁c
      rw [← heq] at ha₁
      exact ha₁.2
    have hb'E : b' ∈ E := hb'E₀.1
    have hb'3 : b' ^ 3 = 1 := hE.2 b' hb'E
    have hx₀2 : x₀ ^ 2 = 1 := by rw [pow_two]; exact (hex x₀ hx₀H).1
    have hzb' : x₀ * b' = b' * x₀ := Subgroup.mem_centralizer_iff.1 hb'E₀.2 x₀ hx₀H
    have hA₀el : IsElemAbelian 3 (innerPartAut E₀) := innerPart_elemAbelian hcen hE₀el
    have hA₀card : Nat.card (innerPartAut E₀) =
        Nat.card (E₀ ⊓ Inn (D4Model K) : Subgroup (MulAut (D4Model K))) := card_innerPart hcen E₀
    have hfixb' : ∀ a ∈ innerPartAut E₀, b' a = a := fun a ha =>
      fixed_of_mem_innerPart (X := E₀) hcen (fun x hx => hcommE b' hb'E x hx.1) ha
    have hfixz : ∀ a ∈ innerPartAut E₀, x₀ a = a := fun a ha =>
      fixed_of_mem_innerPart (X := E₀) hcen (fun x hx => Subgroup.mem_centralizer_iff.1 hx.2 x₀ hx₀H) ha
    have hE₀Q : ¬ E₀ ≤ D4Img K := fun h => hb'Q (h hb'E₀)
    have hE₀card := d3_card_E_Q hK hE₀el hE₀Q
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
    have h9 : Nat.card E = 9 * Nat.card (innerPartAut E₀) := by
      rw [hA₀card, hcardE0]
      have : Nat.card ↥(E ⊓ Subgroup.centralizer (H : Set (MulAut (D4Model K)))) =
          Nat.card E₀ := rfl
      rw [this, hE₀card]
      ring
    have hbound : Nat.card (innerPartAut E₀) ≤ 3 ^ (2 * n) := by
      by_cases hzI : x₀ ∈ Inn (D4Model K)
      · exact hI K n hK b' hb'3 hb'Q x₀ hx₀2 hx₀1 hzI hzb' (innerPartAut E₀) hA₀el hfixb' hfixz
      · exact hF K n hK b' hb'3 hb'Q x₀ hx₀2 hzI hzb' (innerPartAut E₀) hA₀el hfixb' hfixz
    have hn1 : n = 1 := by
      have h1 : 3 ^ (4 * n) ≤ 3 ^ (2 * n + 2) := by
        calc 3 ^ (4 * n) ≤ Nat.card E := hcard
          _ = 9 * Nat.card (innerPartAut E₀) := h9
          _ ≤ 9 * 3 ^ (2 * n) := Nat.mul_le_mul_left _ hbound
          _ = 3 ^ (2 * n + 2) := by rw [pow_add]; ring
      have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 h1
      omega
    subst hn1
    refine hN K (by simpa using hK) E hE hEQ (by simpa using hcard) H hHbot hH2 hHnorm hHfix
      ⟨b', hb'E, hb'Q, fun x hx => ?_⟩
    exact (Subgroup.mem_centralizer_iff.1 hb'E₀.2 x hx).symm

end Reduction

end CFSG.LocalAnalysis.GLTheoremA
