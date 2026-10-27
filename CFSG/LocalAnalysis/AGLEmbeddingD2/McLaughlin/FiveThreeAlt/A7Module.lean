module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.FiveThreeAlt.A7Section
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.FiveThreeAlt.A6Module

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt

open Module CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF CFSG.RankThree.FFModules
  CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
open scoped commutatorElement IsMulCommutative

variable {G : Type*} [Group G] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

theorem center_alt7 : Subgroup.center (alternatingGroup (Fin 7)) = ⊥ :=
  alternatingGroup.center_eq_bot (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)

theorem isSimpleGroup_alt7 : IsSimpleGroup (alternatingGroup (Fin 7)) :=
  alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)

theorem exists_ne_comm_alt7 : ∃ a b : alternatingGroup (Fin 7), a * b ≠ b * a :=
  ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
    ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
    by decide⟩

theorem exists_secRep_ne_one {ρ : Representation (ZMod 2) G W} {L : Subgroup G}
    {Y₀ Y₁ : Submodule (ZMod 2) W} (h₀ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L Y₀) (h₁ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L Y₁)
    (hnt : ¬ SecTrivial ρ L Y₀ Y₁) : ∃ k : ↥L, secRep ρ L h₀ h₁ k ≠ 1 := by
  by_contra hcon
  push Not at hcon
  apply hnt
  rw [secTrivial_iff h₀ h₁ le_rfl]
  intro k hk q
  have h1 := hcon k
  have h3 := congrArg (fun u : Module.End (ZMod 2) (SecQ Y₀ Y₁) => u q) h1
  simpa using h3

theorem a7_commOn_quot [Finite G] [Finite W] (ρ : Representation (ZMod 2) G W)
    (hρ : Function.Injective ρ) {L : Subgroup G} (eL : ↥L ≃* alternatingGroup (Fin 7))
    {A : Subgroup G} (hA2 : CFSG.IsElementaryAbelian 2 ↥A)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hLA : ⁅L, A⁆ = L)
    (hb : IsBestOffenderOn ρ A ⊤) :
    (∀ Z : Submodule (ZMod 2) W, CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L Z → fixOn ρ L (commOn ρ L ⊤) ≤ Z →
      Z ≤ commOn ρ L ⊤ → Z = fixOn ρ L (commOn ρ L ⊤) ∨ Z = commOn ρ L ⊤) ∧
    fixOn ρ L (commOn ρ L ⊤) < commOn ρ L ⊤ := by
  classical
  have : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  have := isSimpleGroup_alt7
  have hsimpL : IsSimpleGroup ↥L := eL.isSimpleGroup
  obtain ⟨hq, hLL, -, hLnab⟩ := isQuasisimple_of_mulEquiv center_alt7 exists_ne_comm_alt7 eL
  have hKnt : ¬ L ≤ cenOn ρ L ⊤ := by
    intro h
    obtain ⟨a, b, hab⟩ := hLnab
    apply hab
    have h1 : ∀ k : ↥L, k = 1 := fun k => by
      apply Subtype.ext
      apply hρ
      ext v
      rw [Subgroup.coe_one, map_one, Module.End.one_apply]
      exact (h k.2).2 v Submodule.mem_top
    rw [h1 a, h1 b]
  obtain ⟨B, hBA, hUinv, hLU, hBU, hbest, hquad, hmove, -⟩ :=
    exists_strictMin_moving (ρ := ρ) L A hA2 hAN hLA hKnt hb
  set U := commOn ρ L ⊤ with hU
  have hAc : ∀ a ∈ A, ∀ c ∈ A, a * c = c * a := fun a ha c hc =>
    congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥A) ⟨c, hc⟩)
  have hBc : ∀ a ∈ B, ∀ c ∈ B, a * c = c * a := fun a ha c hc => hAc a (hBA ha) c (hBA hc)
  have hB2 : ∀ b ∈ B, b ^ 2 = 1 := fun b hb =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian (A := A) b (hBA hb)
  have hBN : B ≤ Subgroup.normalizer (L : Set G) := hBA.trans hAN
  have hLB : ⁅L, B⁆ = L := by
    refine commutator_eq_of_ne_bot hq hBN fun hbot => ?_
    obtain ⟨b, hb, hbc⟩ := Set.not_subset.mp hBU
    obtain ⟨k, hk, u, -, hne⟩ := hmove b hb hbc
    apply hne
    have h1 : ⁅k, b⁆ ∈ ⁅L, B⁆ := Subgroup.commutator_mem_commutator hk hb
    rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    rw [← Module.End.mul_apply, ← map_mul, ← h1, map_mul, Module.End.mul_apply]
  have hUU : commOn ρ L (commOn ρ L ⊤) = commOn ρ L ⊤ := commOn_commOn_eq hA2 hAN hLA
  have hcen := ms24_comm ρ hBN hLB hUU hquad
  have hbudU := two_pow_secCod_le hbest hcen
  have h₀ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) ⊥ := fun _ _ u hu => by
    rw [Submodule.mem_bot] at hu ⊢
    rw [hu, map_zero]
  have hntU : ¬ SecTrivial ρ L ⊥ U := by
    intro ht
    apply hLU
    intro k hk
    refine ⟨hk, fun u hu => ?_⟩
    have h1 := ht k hk u hu
    rw [Submodule.mem_bot, sub_eq_zero] at h1
    exact h1
  have hsec : ∀ Z₀ Z₁ : Submodule (ZMod 2) W, Z₁ ≤ U → IsMinSec ρ (L ⊔ B) Z₀ Z₁ →
      (∀ b ∈ B, (∀ k ∈ L, b * k = k * b) → ∀ v ∈ Z₁, ρ b v = v) ∧
      2 ^ secCod ρ B Z₀ Z₁ * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) ≤ Nat.card B := by
    intro Z₀ Z₁ hZ₁ hmin
    refine ⟨fun b hb hbL v hv => hcen b hb hbL v (hZ₁ hv), ?_⟩
    have hmono : secCod ρ B Z₀ Z₁ ≤ secCod ρ B ⊥ U :=
      secCod_mono_sub bot_le hmin.2.2.1.le hZ₁ (isInvariant_mono le_sup_right hmin.1)
        (isInvariant_mono le_sup_right hmin.2.1)
    calc 2 ^ secCod ρ B Z₀ Z₁ * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G))
        ≤ 2 ^ secCod ρ B ⊥ U * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hmono)
      _ ≤ Nat.card B := hbudU
  obtain ⟨Z₀, Z₁, -, hZ₁, hmin₀, hnt₀⟩ :=
    exists_isMinSec_not_secTrivial hLL h₀ hUinv bot_le hntU
  obtain ⟨-, hbud₀⟩ := hsec Z₀ Z₁ hZ₁ hmin₀
  obtain ⟨r, hrcard, -, -, -, -⟩ := a7_section ρ eL hBN hLB hBc hB2 hmin₀ hnt₀ hbud₀
  have hcpos : 0 < Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) := Nat.card_pos
  have hsU : secCod ρ B ⊥ U ≤ r := by
    have h1 : 2 ^ secCod ρ B ⊥ U * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) ≤
        2 ^ r * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) := by
      rw [hrcard]
      exact hbudU
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp (Nat.le_of_mul_le_mul_right h1 hcpos)
  have hcost : ∀ Y₀ Y₁ : Submodule (ZMod 2) W, CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) Y₀ →
      CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) Y₁ → Y₀ ≤ Y₁ → Y₁ ≤ U → ¬ SecTrivial ρ L Y₀ Y₁ →
      r < 2 * secCod ρ B Y₀ Y₁ := by
    intro Y₀ Y₁ hY₀ hY₁ hle hY₁U hnt
    obtain ⟨X₀, X₁, hX₀, hX₁, hmin, hntX⟩ := exists_isMinSec_not_secTrivial hLL hY₀ hY₁ hle hnt
    obtain ⟨-, hbudX⟩ := hsec X₀ X₁ (hX₁.trans hY₁U) hmin
    obtain ⟨r', hr'card, h2r, -, -, -⟩ := a7_section ρ eL hBN hLB hBc hB2 hmin hntX hbudX
    have hrr : r' = r := by
      have h1 : 2 ^ r' * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) =
          2 ^ r * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) := by rw [hr'card, hrcard]
      exact Nat.pow_right_injective le_rfl (Nat.eq_of_mul_eq_mul_right hcpos h1)
    subst hrr
    have hmono : secCod ρ B X₀ X₁ ≤ secCod ρ B Y₀ Y₁ :=
      secCod_mono_sub hX₀ hmin.2.2.1.le hX₁ (isInvariant_mono le_sup_right hmin.1)
        (isInvariant_mono le_sup_right hmin.2.1)
    omega
  set C := fixOn ρ L U with hC
  have hLBN : L ⊔ B ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hBN
  have hCinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) C := isInvariant_fixOn hLBN hUinv
  have hCU : C ≤ U := fun v hv => (mem_fixOn.mp hv).1
  have htop : ∀ Z : Submodule (ZMod 2) W, Z ≤ U → SecTrivial ρ L Z U → Z = U := by
    intro Z hZU ht
    apply le_antisymm hZU
    have h1 : commOn ρ L U ≤ Z := by
      rw [commOn, Submodule.span_le]
      rintro _ ⟨k, hk, u, hu, rfl⟩
      exact ht k hk u hu
    rw [hU] at h1 ⊢
    rwa [hUU] at h1
  have hbot : ∀ Z : Submodule (ZMod 2) W, Z ≤ U → SecTrivial ρ L ⊥ Z → Z ≤ C := by
    intro Z hZU ht v hv
    refine mem_fixOn.mpr ⟨hZU hv, fun k hk => ?_⟩
    have h1 := ht k hk v hv
    rwa [Submodule.mem_bot, sub_eq_zero] at h1
  have hCltU : C < U := by
    refine lt_of_le_of_ne hCU fun h => hntU ?_
    intro k hk v hv
    rw [Submodule.mem_bot, sub_eq_zero]
    have hv' : v ∈ C := h ▸ hv
    exact (mem_fixOn.mp hv').2 k hk
  have hminCU : IsMinSec ρ (L ⊔ B) C U := by
    refine ⟨hCinv, hUinv, hCltU, fun Z hZ hCZ hZU => ?_⟩
    by_cases h1 : SecTrivial ρ L Z U
    · exact Or.inr (htop Z hZU h1)
    · by_cases h2 : SecTrivial ρ L ⊥ Z
      · exact Or.inl (le_antisymm (hbot Z hZU h2) hCZ)
      · exfalso
        have c1 := hcost ⊥ Z h₀ hZ bot_le hZU h2
        have c2 := hcost Z U hZ hUinv hZU le_rfl h1
        have c3 := secCod_add_le (ρ := ρ) (B := B) (bot_le : (⊥ : Submodule (ZMod 2) W) ≤ Z) hZU
          (isInvariant_mono le_sup_right hZ)
        omega

  have hntCU : ¬ SecTrivial ρ L C U := fun ht => hCltU.ne (htop C hCU ht)
  have hbudCU := (hsec C U le_rfl hminCU).2
  obtain ⟨r₂, -, -, -, h6Q, hfixQ⟩ := a7_section ρ eL hBN hLB hBc hB2 hminCU hntCU hbudCU
  refine ⟨fun Z hZ hCZ hZU => ?_, hCltU⟩
  by_contra hne
  push Not at hne
  have hCZlt : C < Z := lt_of_le_of_ne hCZ (Ne.symm hne.1)
  have hZUlt : Z < U := lt_of_le_of_ne hZU hne.2
  have nt1 : ¬ SecTrivial ρ L C Z := fun ht =>
    hne.1 (le_antisymm (fun v hv => hfixQ v (hZU hv) (fun l hl => ht l hl v hv)) hCZ)
  have nt2 : ¬ SecTrivial ρ L Z U := fun ht => hne.2 (htop Z hZU ht)
  have hC' : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L C := isInvariant_mono le_sup_left hCinv
  have hU' : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L U := isInvariant_mono le_sup_left hUinv
  obtain ⟨k₁, hk₁⟩ := exists_secRep_ne_one hC' hZ nt1
  obtain ⟨k₂, hk₂⟩ := exists_secRep_ne_one hZ hU' nt2
  have : Finite (SecQ C Z) := Module.finite_of_finite (ZMod 2)
  have : Finite (SecQ Z U) := Module.finite_of_finite (ZMod 2)
  have d₁ := four_le_finrank_of_alt7 eL (secRep ρ L hC' hZ) ⟨k₁, hk₁⟩
  have d₂ := four_le_finrank_of_alt7 eL (secRep ρ L hZ hU') ⟨k₂, hk₂⟩
  have e1 := finrank_secQ hCZ
  have e2 := finrank_secQ hZU
  have e3 := finrank_secQ hCU
  omega

end CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt
