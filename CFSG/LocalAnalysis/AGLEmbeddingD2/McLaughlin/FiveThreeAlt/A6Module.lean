module

public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.A6Core

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt

open Module CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF CFSG.RankThree.FFModules
  CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
open scoped commutatorElement IsMulCommutative

variable {G : Type*} [Group G] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

theorem isInvariant_fixOn {ρ : Representation (ZMod 2) G W} {L H : Subgroup G}
    {U : Submodule (ZMod 2) W} (hHN : H ≤ Subgroup.normalizer (L : Set G))
    (hU : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H U) : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H (fixOn ρ L U) := by
  intro g hg v hv
  refine mem_fixOn.mpr ⟨hU g hg v (mem_fixOn.mp hv).1, fun l hl => ?_⟩
  have hl' : g⁻¹ * l * g ∈ L := by
    have := (Subgroup.mem_normalizer_iff.mp (hHN (H.inv_mem hg)) l).mp hl
    simpa using this
  have h1 := (mem_fixOn.mp hv).2 _ hl'
  have e : ρ l (ρ g v) = ρ g (ρ (g⁻¹ * l * g) v) := by
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul,
      show g * (g⁻¹ * l * g) = l * g by group]
  rw [e, h1]

theorem a6_commOn_quot [Finite G] [Finite W] (ρ : Representation (ZMod 2) G W)
    (hρ : Function.Injective ρ) {L : Subgroup G} (eL : ↥L ≃* alternatingGroup (Fin 6))
    {A : Subgroup G} (hA2 : CFSG.IsElementaryAbelian 2 ↥A)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hLA : ⁅L, A⁆ = L)
    (hb : IsBestOffenderOn ρ A ⊤) :
    (∀ Z : Submodule (ZMod 2) W, CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L Z → fixOn ρ L (commOn ρ L ⊤) ≤ Z →
      Z ≤ commOn ρ L ⊤ → Z = fixOn ρ L (commOn ρ L ⊤) ∨ Z = commOn ρ L ⊤) ∧
    finrank (ZMod 2) ↥(commOn ρ L ⊤) = finrank (ZMod 2) ↥(fixOn ρ L (commOn ρ L ⊤)) + 4 := by
  classical
  have : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  have := isSimpleGroup_alt6
  have hsimpL : IsSimpleGroup ↥L := eL.isSimpleGroup
  obtain ⟨hq, hLL, -, hLnab⟩ := isQuasisimple_of_mulEquiv center_alt6 exists_ne_comm_alt6 eL
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
  obtain ⟨hcen₀, hbud₀⟩ := hsec Z₀ Z₁ hZ₁ hmin₀
  obtain ⟨r, hr3, hrcard, -, -⟩ := a6_section ρ eL hBN hLB hBc hB2 hmin₀ hnt₀ hcen₀ hbud₀
  have hcpos : 0 < Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) := Nat.card_pos
  have hsU : secCod ρ B ⊥ U ≤ r := by
    have h1 : 2 ^ secCod ρ B ⊥ U * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) ≤
        2 ^ r * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) := by
      rw [hrcard]
      exact hbudU
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp (Nat.le_of_mul_le_mul_right h1 hcpos)
  have hr1 : 1 ≤ r := by
    by_contra h
    have hr0 : r = 0 := by omega
    rw [hr0, pow_zero, one_mul] at hrcard
    have h1 : B ⊓ Subgroup.centralizer (L : Set G) = B :=
      Subgroup.eq_of_le_of_card_ge inf_le_left hrcard.ge
    have h2 : ⁅L, B⁆ = ⊥ := by
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer, ← h1]
      exact inf_le_right
    rw [hLB] at h2
    obtain ⟨a, b, hab⟩ := hLnab
    apply hab
    have ha : a = 1 := Subtype.ext (Subgroup.mem_bot.mp (h2 ▸ a.2))
    have hb' : b = 1 := Subtype.ext (Subgroup.mem_bot.mp (h2 ▸ b.2))
    rw [ha, hb']
  have hcost : ∀ Y₀ Y₁ : Submodule (ZMod 2) W, CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) Y₀ →
      CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) Y₁ → Y₀ ≤ Y₁ → Y₁ ≤ U → ¬ SecTrivial ρ L Y₀ Y₁ →
      2 * r ≤ 3 * secCod ρ B Y₀ Y₁ := by
    intro Y₀ Y₁ hY₀ hY₁ hle hY₁U hnt
    obtain ⟨X₀, X₁, hX₀, hX₁, hmin, hntX⟩ := exists_isMinSec_not_secTrivial hLL hY₀ hY₁ hle hnt
    obtain ⟨hcenX, hbudX⟩ := hsec X₀ X₁ (hX₁.trans hY₁U) hmin
    obtain ⟨r', -, hr'card, h2r, -⟩ := a6_section ρ eL hBN hLB hBc hB2 hmin hntX hcenX hbudX
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
  set H := L ⊔ B with hH
  have hLH : L ≤ H := le_sup_left
  have hBH : B ≤ H := le_sup_right
  set Q := SecQ C U with hQ
  set σ := secRep ρ H hCinv hUinv with hσ
  set σu := σ.asGroupHom with hσu
  have hσu_apply : ∀ h : ↥H, ((σu h : (Module.End (ZMod 2) Q)ˣ) : Module.End (ZMod 2) Q) = σ h :=
    fun h => Representation.asGroupHom_apply σ h
  obtain ⟨hQnt, hirrQ⟩ := secRep_irreducible hminCU
  have : Finite Q := Module.finite_of_finite (ZMod 2)
  set σL : ↥L →* (Module.End (ZMod 2) Q)ˣ := σu.comp (Subgroup.inclusion hLH) with hσL
  set σB : ↥B →* (Module.End (ZMod 2) Q)ˣ := σu.comp (Subgroup.inclusion hBH) with hσB
  have hσLnt : ∃ k : ↥L, σL k ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply (show ¬ SecTrivial ρ L C U from fun ht => hCltU.ne (htop C hCU ht))
    rw [secTrivial_iff hCinv hUinv hLH]
    intro k hk q
    have h1 := hcon ⟨k, Subgroup.mem_subgroupOf.mp hk⟩
    have h2 : Subgroup.inclusion hLH ⟨k, Subgroup.mem_subgroupOf.mp hk⟩ = k := Subtype.ext rfl
    have h3 := congrArg (fun u : (Module.End (ZMod 2) Q)ˣ => (u : Module.End (ZMod 2) Q) q) h1
    simp only [hσL, MonoidHom.comp_apply, h2, Units.val_one, Module.End.one_apply] at h3
    rw [hσu_apply] at h3
    exact h3
  have hσLinj : Function.Injective σL := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal σL.ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff σL).mp h
    · exfalso
      obtain ⟨k, hk⟩ := hσLnt
      exact hk (σL.mem_ker.mp (h ▸ Subgroup.mem_top k))
  set Y := σL.range with hY
  set A' := σB.range with hA'
  set eY : ↥Y ≃* alternatingGroup (Fin 6) := (MonoidHom.ofInjective hσLinj).symm.trans eL with heY
  have hconjB : ∀ (b : ↥B) (k : ↥L), σB b * σL k * (σB b)⁻¹ =
      σL ⟨(b : G) * k * (b : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hBN b.2) k).mp k.2⟩ := by
    intro b k
    simp only [hσL, hσB, MonoidHom.comp_apply, ← map_inv, ← map_mul]
    rfl
  have hA'N : A' ≤ Subgroup.normalizer (Y : Set (Module.End (ZMod 2) Q)ˣ) := by
    rintro _ ⟨b, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨_, (hconjB b k).symm⟩
    · rintro ⟨k, hk⟩
      have hb' : (b : G)⁻¹ ∈ B := B.inv_mem b.2
      have h1 := hconjB ⟨(b : G)⁻¹, hb'⟩ k
      have h2 : σB ⟨(b : G)⁻¹, hb'⟩ = (σB b)⁻¹ := by
        rw [← map_inv]
        rfl
      rw [h2, inv_inv, hk] at h1
      refine ⟨⟨(b : G)⁻¹ * (k : G) * ((b : G)⁻¹)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hBN hb') k).mp k.2⟩, ?_⟩
      rw [← h1]
      group
  have hHle : ∀ h : ↥H, σu h ∈ Y ⊔ A' := by
    intro h
    have hmem : (h : G) ∈ ((L ⊔ B : Subgroup G) : Set G) := h.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left L B hBN] at hmem
    obtain ⟨l, hl, b, hb, hlb⟩ := hmem
    have e : h = Subgroup.inclusion hLH ⟨l, hl⟩ * Subgroup.inclusion hBH ⟨b, hb⟩ :=
      Subtype.ext hlb.symm
    rw [e, map_mul]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨⟨l, hl⟩, rfl⟩)
      (Subgroup.mem_sup_right ⟨⟨b, hb⟩, rfl⟩)
  have hirr : ∀ N : Submodule (ZMod 2) Q,
      (∀ d ∈ Y ⊔ A', ∀ v ∈ N, (d : Module.End (ZMod 2) Q) v ∈ N) → N = ⊥ ∨ N = ⊤ := by
    intro N hN
    refine hirrQ N fun h q hq => ?_
    have h1 := hN _ (hHle h) q hq
    rwa [hσu_apply] at h1
  have hA1 : A' ≠ ⊥ := by
    intro hbot
    obtain ⟨k, hk⟩ := hσLnt
    apply hk
    have hBtriv : ∀ b : ↥B, σB b = 1 := fun b => by
      have h1 : σB b ∈ A' := ⟨b, rfl⟩
      rw [hbot] at h1
      exact Subgroup.mem_bot.mp h1
    have hle' : ⁅L, B⁆ ≤ (σL.ker).map L.subtype := by
      rw [Subgroup.commutator_le]
      intro l hl b hb
      have hmem : ⁅l, b⁆ ∈ L := by
        rw [commutatorElement_def]
        have h1 : b * l⁻¹ * b⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hBN hb) l⁻¹).mp
          (L.inv_mem hl)
        have e : l * b * l⁻¹ * b⁻¹ = l * (b * l⁻¹ * b⁻¹) := by group
        rw [e]
        exact L.mul_mem hl h1
      refine ⟨⟨⁅l, b⁆, hmem⟩, ?_, rfl⟩
      show σL ⟨⁅l, b⁆, hmem⟩ = 1
      have e : Subgroup.inclusion hLH ⟨⁅l, b⁆, hmem⟩ =
          ⁅Subgroup.inclusion hLH ⟨l, hl⟩, Subgroup.inclusion hBH ⟨b, hb⟩⁆ := Subtype.ext rfl
      have hb1 : σu (Subgroup.inclusion hBH ⟨b, hb⟩) = 1 := hBtriv ⟨b, hb⟩
      rw [hσL, MonoidHom.comp_apply, e]
      simp only [commutatorElement_def, map_mul, map_inv, hb1]
      group
    rw [hLB] at hle'
    obtain ⟨k', hk', hkk'⟩ := hle' k.2
    have e : k' = k := Subtype.ext hkk'
    rw [← e]
    exact hk'
  have hAc' : ∀ a ∈ A', ∀ c ∈ A', a * c = c * a := by
    rintro _ ⟨a, rfl⟩ _ ⟨c, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hBc _ a.2 _ c.2)
  have hA2' : ∀ a ∈ A', a ^ 2 = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_pow]
    have h1 : a ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hB2 _ a.2)
    rw [h1, map_one]
  have hkerB : ∀ b : ↥B, σB b = 1 ↔ (b : G) ∈ Subgroup.centralizer (L : Set G) := by
    intro b
    constructor
    · intro h1
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h2 := hconjB b ⟨k, hk⟩
      rw [h1, one_mul, inv_one, mul_one] at h2
      have h3 : k = (b : G) * k * (b : G)⁻¹ := congrArg Subtype.val (hσLinj h2)
      calc k * (b : G) = (b : G) * k * (b : G)⁻¹ * (b : G) := by rw [← h3]
        _ = (b : G) * k := by group
    · intro h1
      apply Units.ext
      refine LinearMap.ext fun q => ?_
      induction q using Submodule.Quotient.induction_on with
      | H z =>
        rw [Units.val_one, Module.End.one_apply, hσB, MonoidHom.comp_apply, hσu_apply, hσ,
          secRep_mk]
        congr 1
        apply Subtype.ext
        exact hcen b b.2 (fun k hk => (Subgroup.mem_centralizer_iff.mp h1 k hk).symm) z z.2
  have hcardA : Nat.card A' * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) = Nat.card B := by
    have h1 := Subgroup.index_mul_card σB.ker
    rw [Subgroup.index_ker] at h1
    have h2 : Nat.card σB.ker = Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) :=
      Nat.card_congr
        { toFun := fun b => ⟨b.1.1, b.1.2, (hkerB b.1).mp b.2⟩
          invFun := fun c => ⟨⟨c.1, c.2.1⟩, (hkerB _).mpr c.2.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    rw [← h2]
    exact h1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAfin : Finite ↥A' := Finite.of_surjective _ σB.rangeRestrict_surjective
  have hAp : IsPGroup 2 ↥A' := fun a => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hA2' a a.2)⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hAp
  have hfixeq : fixSub σ (B.subgroupOf H) = CFSG.LocalAnalysis.CommutingFactor.fixedSub A' := by
    ext q
    rw [mem_fixSub, CFSG.LocalAnalysis.CommutingFactor.mem_fixedSub]
    constructor
    · rintro h _ ⟨b, rfl⟩
      rw [hσB, MonoidHom.comp_apply, hσu_apply]
      exact h _ (Subgroup.mem_subgroupOf.mpr b.2)
    · intro h b hb
      have h1 := h (σB ⟨b, Subgroup.mem_subgroupOf.mp hb⟩) ⟨_, rfl⟩
      rw [hσB, MonoidHom.comp_apply, hσu_apply] at h1
      exact h1
  have hsc0 := secCod_eq hCinv hUinv hCU hBH
  rw [← hσ, hfixeq] at hsc0
  have hsc : secCod ρ B C U = finrank (ZMod 2) Q -
      finrank (ZMod 2) ↥(CFSG.LocalAnalysis.CommutingFactor.fixedSub A') := hsc0
  have hbudCU := (hsec C U le_rfl hminCU).2
  have hs : secCod ρ B C U ≤ m := by
    have h1 : 2 ^ secCod ρ B C U * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) ≤
        2 ^ m * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) := by
      rw [← hm, hcardA]
      exact hbudCU
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp (Nat.le_of_mul_le_mul_right h1 hcpos)
  have := hQnt
  obtain ⟨r', m', hr'card, -, -, hmr, hdimle⟩ := a6_short_gen hirr hA'N eY hA1 hAc' hA2'
  have hrm : r' = m := Nat.pow_right_injective le_rfl (hr'card.symm.trans hm)
  subst hrm
  have hdimle' : finrank (ZMod 2) Q ≤ m' * secCod ρ B C U := by
    rw [hsc]
    exact hdimle
  have hdim6 : finrank (ZMod 2) Q ≤ 6 := by
    calc finrank (ZMod 2) Q ≤ m' * secCod ρ B C U := hdimle'
      _ ≤ m' * r' := Nat.mul_le_mul_left _ hs
      _ ≤ 6 := hmr
  obtain ⟨hdim4, -⟩ := a6_natural _ _ hirr hA'N eY hdim6
  have hYirr := a6_irreducible hirr hA'N eY hdim6
  refine ⟨fun Z hZ hCZ hZU => ?_, ?_⟩
  ·
    set N : Submodule (ZMod 2) Q :=
      (Z.comap U.subtype).map (C.comap U.subtype).mkQ with hN
    have hNinv : ∀ y ∈ Y, ∀ v ∈ N, (y : Module.End (ZMod 2) Q) v ∈ N := by
      rintro _ ⟨k, rfl⟩ _ ⟨z, hz, rfl⟩
      refine ⟨⟨ρ k z, hUinv k (hLH k.2) z z.2⟩, hZ k k.2 z hz, ?_⟩
      rw [hσL, MonoidHom.comp_apply, hσu_apply, Submodule.mkQ_apply, Submodule.mkQ_apply, hσ,
        secRep_mk]
      rfl
    rcases hYirr N hNinv with hb | ht
    · left
      refine le_antisymm (fun z hz => ?_) hCZ
      have h1 : (C.comap U.subtype).mkQ ⟨z, hZU hz⟩ ∈ N := ⟨⟨z, hZU hz⟩, hz, rfl⟩
      rw [hb, Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1
      exact h1
    · right
      refine le_antisymm hZU (fun u hu => ?_)
      have h1 : (C.comap U.subtype).mkQ ⟨u, hu⟩ ∈ N := by rw [ht]; exact Submodule.mem_top
      obtain ⟨z, hz, hzu⟩ := h1
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hzu
      have h2 : ((z - ⟨u, hu⟩ : ↥U) : W) ∈ C := hzu
      have h3 : (u : W) = (z : W) - ((z - ⟨u, hu⟩ : ↥U) : W) := by simp
      rw [h3]
      exact Z.sub_mem hz (hCZ h2)
  · have h1 := finrank_secQ (Z₀ := C) (Z₁ := U) hCU
    have h2 : finrank (ZMod 2) (SecQ C U) = 4 := hdim4
    omega

end CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt
