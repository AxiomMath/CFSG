module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K55Frob
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K55Sec
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K55Split
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.L32Core

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K55Proof

open Module CFSG.QuasithinUnique.Setup.Family CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
  CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
open scoped commutatorElement IsMulCommutative

section Setup

variable {G : Type*} [Group G] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

theorem exists_k55_setup [Finite G] [Finite W] (ρ : Representation (ZMod 2) G W)
    (hρ : Function.Injective ρ) {L : Subgroup G} (eL : ↥L ≃* GL32)
    {A : Subgroup G} (hA2 : CFSG.IsElementaryAbelian 2 ↥A)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hLA : ⁅L, A⁆ = L)
    (hb : IsBestOffenderOn ρ A ⊤) :
    ∃ B : Subgroup G, B ≤ Subgroup.normalizer (L : Set G) ∧ (∀ b ∈ B, b ^ 2 = 1) ∧
      (∀ a ∈ B, ∀ c ∈ B, a * c = c * a) ∧ ⁅L, B⁆ = L ∧
      CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) (commOn ρ L ⊤) ∧
      (∀ b ∈ B, (∀ k ∈ L, b * k = k * b) → ∀ u ∈ commOn ρ L ⊤, ρ b u = u) ∧
      2 ^ secCod ρ B ⊥ (commOn ρ L ⊤) * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) ≤
        Nat.card B ∧
      commOn ρ L (commOn ρ L ⊤) = commOn ρ L ⊤ ∧ commOn ρ L ⊤ ≠ ⊥ := by
  classical
  have : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  have hsimpL : IsSimpleGroup ↥L := by
    have := isSimpleGroup_gl32
    exact eL.isSimpleGroup
  have hperf : Group.IsPerfect ↥L := by
    have := GL32_isPerfect
    exact Group.IsPerfect.ofSurjective (f := eL.symm.toMonoidHom) eL.symm.surjective
  have hZL : ∀ z : ↥L, (∀ k : ↥L, z * k = k * z) → z = 1 := by
    intro z hz
    exact eq_of_forall_conj_eq eL (x := z) (y := 1) fun k hk => by
      have h2 := congrArg Subtype.val (hz ⟨k, hk⟩)
      simp only [Subgroup.coe_mul] at h2
      simp only [Subgroup.coe_one, one_mul, inv_one, mul_one]
      rw [h2]
      group
  have hcenL : Subgroup.center ↥L = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    exact hZL z fun k => (Subgroup.mem_center_iff.mp hz k).symm
  have hLnab : ∃ a b : ↥L, a * b ≠ b * a := by
    by_contra h
    push Not at h
    obtain ⟨z, hz⟩ := exists_ne (1 : ↥L)
    exact hz (hZL z fun k => h z k)
  let eQ : ↥L ⧸ Subgroup.center ↥L ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hcenL).trans QuotientGroup.quotientBot
  have hq : CFSG.IsQuasisimple ↥L := by
    refine ⟨hperf, eQ.isSimpleGroup, ?_⟩
    obtain ⟨a, b, hab⟩ := hLnab
    exact ⟨eQ.symm a, eQ.symm b, fun h => hab (by simpa using congrArg eQ h)⟩
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
  refine ⟨B, hBN, hB2, hBc, hLB, hUinv, hcen, hbudU, hUU, ?_⟩
  intro hbot
  apply hLU
  intro k hk
  refine ⟨hk, fun u hu => ?_⟩
  rw [hbot, Submodule.mem_bot] at hu
  rw [hu, map_zero]

end Setup

section Chain

variable {G : Type*} [Group G] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

theorem sec_budget [Finite W] {ρ : Representation (ZMod 2) G W} {L B : Subgroup G}
    {U Z₀ Z₁ : Submodule (ZMod 2) W}
    (hbudU : 2 ^ secCod ρ B ⊥ U * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) ≤ Nat.card B)
    (hZ₀ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ B Z₀) (hZ₁ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ B Z₁) (hle : Z₀ ≤ Z₁) (hZ₁U : Z₁ ≤ U) :
    2 ^ secCod ρ B Z₀ Z₁ * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) ≤ Nat.card B :=
  (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num)
    (secCod_mono_sub bot_le hle hZ₁U hZ₀ hZ₁))).trans hbudU

theorem k55_chain [Finite G] [Finite W] (ρ : Representation (ZMod 2) G W) {L : Subgroup G}
    (eL : ↥L ≃* GL32) {B : Subgroup G} (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (hB2 : ∀ b ∈ B, b ^ 2 = 1) (hBc : ∀ a ∈ B, ∀ c ∈ B, a * c = c * a) (hLB : ⁅L, B⁆ = L)
    (hUinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) (commOn ρ L ⊤))
    (hcen : ∀ b ∈ B, (∀ k ∈ L, b * k = k * b) → ∀ u ∈ commOn ρ L ⊤, ρ b u = u)
    (hbudU : 2 ^ secCod ρ B ⊥ (commOn ρ L ⊤) *
      Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) ≤ Nat.card B)
    {F : Subgroup G} (hFL : F ≤ L) (hF : Odd (Nat.card F))
    (hFix : ∀ u ∈ commOn ρ L ⊤, (∀ f ∈ F, ρ f u = u) → u = 0) (hUne : commOn ρ L ⊤ ≠ ⊥) :
    ∃ τ : GL32 →* (Vec3 ≃ₗ[ZMod 2] Vec3), (τ = repV ∨ τ = repDual) ∧
      ∃ (M : Submodule (ZMod 2) W) (hM : IsMinSec ρ (L ⊔ B) ⊥ M), M ≤ commOn ρ L ⊤ ∧
        SecIso ρ eL hM.1 hM.2.1 τ ∧
        (M = commOn ρ L ⊤ ∨ ∃ hM2 : IsMinSec ρ (L ⊔ B) M (commOn ρ L ⊤),
          SecIso ρ eL hM2.1 hM2.2.1 τ) := by
  classical
  set U := commOn ρ L ⊤ with hU
  have hLH : L ≤ L ⊔ B := le_sup_left
  have hBH : B ≤ L ⊔ B := le_sup_right
  have h₀ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) ⊥ := fun _ _ u hu => by
    rw [Submodule.mem_bot] at hu ⊢
    rw [hu, map_zero]
  have key : ∀ Z₀ Z₁ : Submodule (ZMod 2) W, Z₀ < Z₁ → Z₁ ≤ U → IsMinSec ρ (L ⊔ B) Z₀ Z₁ →
      ∃ hmin : IsMinSec ρ (L ⊔ B) Z₀ Z₁, 1 ≤ secCod ρ B Z₀ Z₁ ∧
        Nat.card (innImg L B eL) * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) = Nat.card B ∧
        FixedCodimData (innImg L B eL) ∧
        ((SecIso ρ eL hmin.1 hmin.2.1 repV ∧
            2 ^ (3 - secCod ρ B Z₀ Z₁) = Nat.card (fixVec3 (innImg L B eL))) ∨
          (SecIso ρ eL hmin.1 hmin.2.1 repDual ∧
            2 ^ (3 - secCod ρ B Z₀ Z₁) = Nat.card (fixDual3 (innImg L B eL)))) := by
    intro Z₀ Z₁ hlt hZ₁U hmin
    have hnt : ¬ SecTrivial ρ L Z₀ Z₁ :=
      not_secTrivial_of_fixed_zero ρ hFL hF hFix hZ₁U hlt (isInvariant_mono hLH hmin.2.1)
    have hc1 := one_le_secCod_of_not_secTrivial ρ hLB hmin.1 hmin.2.1 hnt
    obtain ⟨hcard, hfix, -, hty⟩ := l32_section_iso ρ eL hBN hLB hBc hB2 hmin hnt
      (fun b hb hbL v hv => hcen b hb hbL v (hZ₁U hv))
      (sec_budget hbudU (isInvariant_mono hBH hmin.1) (isInvariant_mono hBH hmin.2.1) hlt.le hZ₁U)
    exact ⟨hmin, hc1, hcard, hfix, hty⟩
  have hbotU : (⊥ : Submodule (ZMod 2) W) < U := bot_lt_iff_ne_bot.2 hUne
  obtain ⟨M₁, hbM₁, hM₁U, hmin₁⟩ := exists_isMinSec_above ρ (L ⊔ B) hbotU h₀ hUinv
  obtain ⟨hmin₁', hc₁, hcard, hfix, hty₁⟩ := key ⊥ M₁ hbM₁ hM₁U hmin₁
  have hcpos : 0 < Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) := Nat.card_pos
  have hsU : 2 ^ secCod ρ B ⊥ U ≤ Nat.card (innImg L B eL) := by
    have h1 : 2 ^ secCod ρ B ⊥ U * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) ≤
        Nat.card (innImg L B eL) * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) := by
      rw [hcard]; exact hbudU
    exact Nat.le_of_mul_le_mul_right h1 hcpos
  have hB4 : Nat.card (innImg L B eL) ≤ 4 := by
    unfold FixedCodimData at hfix
    rcases hfix with ⟨h2, -⟩ | ⟨h4, -⟩ <;> omega
  have hsU2 : secCod ρ B ⊥ U ≤ 2 := by
    by_contra hcon
    have : 2 ^ 3 ≤ 2 ^ secCod ρ B ⊥ U := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  by_cases hM₁eq : M₁ = U
  ·
    rcases hty₁ with ⟨hiso, -⟩ | ⟨hiso, -⟩
    · exact ⟨repV, Or.inl rfl, M₁, hmin₁', hM₁U, hiso, Or.inl hM₁eq⟩
    · exact ⟨repDual, Or.inr rfl, M₁, hmin₁', hM₁U, hiso, Or.inl hM₁eq⟩
  · have hM₁lt : M₁ < U := lt_of_le_of_ne hM₁U hM₁eq
    obtain ⟨M₂, hM₁M₂, hM₂U, hmin₂⟩ := exists_isMinSec_above ρ (L ⊔ B) hM₁lt hmin₁.2.1 hUinv
    obtain ⟨hmin₂', hc₂, -, -, hty₂⟩ := key M₁ M₂ hM₁M₂ hM₂U hmin₂
    have hinvB : ∀ {Z : Submodule (ZMod 2) W}, CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) Z → CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ B Z :=
      fun h => isInvariant_mono hBH h
    have hsum : secCod ρ B ⊥ M₁ + secCod ρ B M₁ M₂ ≤ secCod ρ B ⊥ U := by
      have h1 := secCod_add_le (ρ := ρ) (B := B) (bot_le : (⊥ : Submodule (ZMod 2) W) ≤ M₁)
        hM₁M₂.le (hinvB hmin₂.1)
      have h2 : secCod ρ B ⊥ M₂ ≤ secCod ρ B ⊥ U :=
        secCod_mono_sub (le_refl ⊥) bot_le hM₂U (hinvB h₀) (hinvB hmin₂.2.1)
      omega
    have hsame := same_type hfix hc₁ hc₂ (s := secCod ρ B ⊥ U) hsum hsU hty₁ hty₂
    have hM₂eq : M₂ = U := by
      by_contra hne
      have hlt : M₂ < U := lt_of_le_of_ne hM₂U hne
      obtain ⟨M₃, hM₂M₃, hM₃U, hmin₃⟩ := exists_isMinSec_above ρ (L ⊔ B) hlt hmin₂.2.1 hUinv
      obtain ⟨-, hc₃, -, -, -⟩ := key M₂ M₃ hM₂M₃ hM₃U hmin₃
      have h1 := secCod_add_le (ρ := ρ) (B := B) (bot_le : (⊥ : Submodule (ZMod 2) W) ≤ M₂)
        hM₂M₃.le (hinvB hmin₃.1)
      have h2 : secCod ρ B ⊥ M₃ ≤ secCod ρ B ⊥ U :=
        secCod_mono_sub (le_refl ⊥) bot_le hM₃U (hinvB h₀) (hinvB hmin₃.2.1)
      have h3 := secCod_add_le (ρ := ρ) (B := B) (bot_le : (⊥ : Submodule (ZMod 2) W) ≤ M₁)
        hM₁M₂.le (hinvB hmin₂.1)
      omega
    subst hM₂eq
    rcases hsame with ⟨hP₁, hP₂⟩ | ⟨hQ₁, hQ₂⟩
    · exact ⟨repV, Or.inl rfl, M₁, hmin₁', hM₁U, hP₁, Or.inr ⟨hmin₂', hP₂⟩⟩
    · exact ⟨repDual, Or.inr rfl, M₁, hmin₁', hM₁U, hQ₁, Or.inr ⟨hmin₂', hQ₂⟩⟩

end Chain

section Models

variable {G : Type*} [Group G] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] def ModEmb (ρ : Representation (ZMod 2) G W) {L : Subgroup G} (eL : ↥L ≃* GL32)
    (τ : GL32 →* (Vec3 ≃ₗ[ZMod 2] Vec3)) (ι : Vec3 →ₗ[ZMod 2] W) : Prop :=
  Function.Injective ι ∧ ∀ g v, ι (τ g v) = ρ ((eL.symm g : ↥L) : G) (ι v)

@[expose] noncomputable def restrictRep (ρ : Representation (ZMod 2) G W) {L : Subgroup G}
    (eL : ↥L ≃* GL32) (U : Submodule (ZMod 2) W) (hU : ∀ l ∈ L, ∀ u ∈ U, ρ l u ∈ U) :
    GL32 →* Module.End (ZMod 2) ↥U where
  toFun g := (ρ ((eL.symm g : ↥L) : G)).restrict (fun u hu => hU _ (eL.symm g).2 u hu)
  map_one' := by
    refine LinearMap.ext fun u => Subtype.ext ?_
    simp
  map_mul' g h := by
    refine LinearMap.ext fun u => Subtype.ext ?_
    simp [Module.End.mul_apply]

theorem modEmb_of_secIso_bot [Finite W] (ρ : Representation (ZMod 2) G W) {L B : Subgroup G}
    (eL : ↥L ≃* GL32) {M : Submodule (ZMod 2) W} (h₀ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) ⊥)
    (hM : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) M) (τ : GL32 →* (Vec3 ≃ₗ[ZMod 2] Vec3))
    (hs : SecIso ρ eL h₀ hM τ) :
    ∃ ι : Vec3 →ₗ[ZMod 2] W, ModEmb ρ eL τ ι ∧ LinearMap.range ι = M := by
  obtain ⟨e, he⟩ := hs
  have hbot : (⊥ : Submodule (ZMod 2) W).comap M.subtype = ⊥ := by
    rw [Submodule.comap_bot, Submodule.ker_subtype]
  let qe : SecQ (⊥ : Submodule (ZMod 2) W) M ≃ₗ[ZMod 2] ↥M := Submodule.quotEquivOfEqBot _ hbot
  have hqe : ∀ (h : ↥(L ⊔ B)) (q : SecQ (⊥ : Submodule (ZMod 2) W) M),
      ((qe (secRep ρ (L ⊔ B) h₀ hM h q) : ↥M) : W) = ρ (h : G) ((qe q : ↥M) : W) := by
    intro h q
    have hq : ∀ x : ↥M, qe (Submodule.Quotient.mk x) = x :=
      fun x => Submodule.quotEquivOfEqBot_apply_mk _ hbot x
    induction q using Submodule.Quotient.induction_on with
    | H z =>
      rw [secRep_mk, hq, hq]
  refine ⟨M.subtype ∘ₗ qe.toLinearMap ∘ₗ e.toLinearMap, ⟨?_, fun g v => ?_⟩, ?_⟩
  · exact M.injective_subtype.comp (qe.injective.comp e.injective)
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply]
    rw [he g v]
    exact hqe _ _
  · rw [LinearMap.range_comp, LinearMap.range_comp]
    have h1 : LinearMap.range e.toLinearMap = ⊤ := LinearEquiv.range e
    have h2 : Submodule.map qe.toLinearMap ⊤ = ⊤ := by
      rw [Submodule.map_top, LinearEquiv.range]
    rw [h1, h2, Submodule.map_top, Submodule.range_subtype]

@[expose] def SplitsFor (τ : GL32 →* (Vec3 ≃ₗ[ZMod 2] Vec3)) : Prop :=
  ∀ {E : Type} [AddCommGroup E] [Module (ZMod 2) E] [Finite E]
    (ρ : GL32 →* Module.End (ZMod 2) E) (ι : Vec3 →ₗ[ZMod 2] E), Function.Injective ι →
    (∀ g v, ι (τ g v) = ρ g (ι v)) → ∀ (π : E →ₗ[ZMod 2] Vec3), Function.Surjective π →
    (∀ g x, π (ρ g x) = τ g (π x)) → LinearMap.ker π = LinearMap.range ι →
    ∃ s : Vec3 →ₗ[ZMod 2] E, (∀ v, π (s v) = v) ∧ ∀ g v, s (τ g v) = ρ g (s v)

theorem splitsFor_repV : SplitsFor repV :=
  fun ρ ι hι hιρ π hπ hπρ hex => exists_equivariant_section ρ ι hι hιρ π hπ hπρ hex

theorem splitsFor_repDual : SplitsFor repDual :=
  fun ρ ι hι hιρ π hπ hπρ hex => exists_equivariant_section_dual ρ ι hι hιρ π hπ hπρ hex

theorem exists_split_embeddings [Finite W] (ρ : Representation (ZMod 2) G W) {L B : Subgroup G}
    (eL : ↥L ≃* GL32) {M U : Submodule (ZMod 2) W} (hMU : M ≤ U)
    (h₀ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) ⊥) (hM : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) M)
    (hU : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) U) (τ : GL32 →* (Vec3 ≃ₗ[ZMod 2] Vec3)) (hsplit : SplitsFor τ)
    (s₁ : SecIso ρ eL h₀ hM τ) (s₂ : SecIso ρ eL hM hU τ) :
    ∃ ι₁ ι₂ : Vec3 →ₗ[ZMod 2] W, ModEmb ρ eL τ ι₁ ∧ ModEmb ρ eL τ ι₂ ∧
      LinearMap.range ι₁ = M ∧ LinearMap.range ι₁ ⊔ LinearMap.range ι₂ = U ∧
      LinearMap.range ι₁ ⊓ LinearMap.range ι₂ = ⊥ := by
  classical
  obtain ⟨ι₁, hι₁, hr₁⟩ := modEmb_of_secIso_bot ρ eL h₀ hM τ s₁
  obtain ⟨e₂, he₂⟩ := s₂
  have hUL : ∀ l ∈ L, ∀ u ∈ U, ρ l u ∈ U := fun l hl u hu => hU l (Subgroup.mem_sup_left hl) u hu
  have : Finite ↥U := inferInstance
  let ρ' := restrictRep ρ eL U hUL
  have hι₁U : ∀ v, ι₁ v ∈ U := fun v => hMU (hr₁ ▸ LinearMap.mem_range_self ι₁ v)
  let ι' : Vec3 →ₗ[ZMod 2] ↥U := LinearMap.codRestrict U ι₁ hι₁U
  let π : ↥U →ₗ[ZMod 2] Vec3 := e₂.symm.toLinearMap ∘ₗ (M.comap U.subtype).mkQ
  have hι' : Function.Injective ι' := fun a b h => hι₁.1 (congrArg Subtype.val h)
  have hιρ' : ∀ g v, ι' (τ g v) = ρ' g (ι' v) := fun g v =>
    Subtype.ext (hι₁.2 g v)
  have hπ : Function.Surjective π :=
    e₂.symm.surjective.comp (Submodule.mkQ_surjective _)
  have hπρ' : ∀ g x, π (ρ' g x) = τ g (π x) := by
    intro g x
    have h1 := he₂ g (π x)
    have h2 : e₂ (π x) = (M.comap U.subtype).mkQ x := by
      simp [π]
    rw [h2] at h1
    have h3 : secRep ρ (L ⊔ B) hM hU
        ⟨((eL.symm g : ↥L) : G), Subgroup.mem_sup_left (eL.symm g).2⟩ ((M.comap U.subtype).mkQ x) =
        (M.comap U.subtype).mkQ (ρ' g x) := rfl
    rw [h3] at h1
    have h4 := congrArg e₂.symm h1
    rw [LinearEquiv.symm_apply_apply] at h4
    exact h4.symm
  have hex : LinearMap.ker π = LinearMap.range ι' := by
    ext x
    constructor
    · intro hx
      have hx' : (M.comap U.subtype).mkQ x = 0 := by
        have : e₂.symm ((M.comap U.subtype).mkQ x) = 0 := hx
        simpa using this
      have hxM : (x : W) ∈ M := by
        have := (Submodule.Quotient.mk_eq_zero _).1 hx'
        exact this
      rw [← hr₁] at hxM
      obtain ⟨v, hv⟩ := hxM
      exact ⟨v, Subtype.ext hv⟩
    · rintro ⟨v, rfl⟩
      have hvM : ι₁ v ∈ M := hr₁ ▸ LinearMap.mem_range_self ι₁ v
      have : (M.comap U.subtype).mkQ (ι' v) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).2 hvM
      show e₂.symm ((M.comap U.subtype).mkQ (ι' v)) = 0
      rw [this, map_zero]
  obtain ⟨s, hs1, hs2⟩ := hsplit ρ' ι' hι' hιρ' π hπ hπρ' hex
  have hsinj : Function.Injective s := fun a b h => by
    have := congrArg π h
    rwa [hs1, hs1] at this
  refine ⟨ι₁, U.subtype ∘ₗ s, hι₁, ⟨U.injective_subtype.comp hsinj, fun g v => ?_⟩, hr₁, ?_, ?_⟩
  · simp only [LinearMap.comp_apply, Submodule.subtype_apply]
    rw [hs2 g v]
    rfl
  · apply le_antisymm
    · refine sup_le (hr₁ ▸ hMU) ?_
      rintro _ ⟨v, rfl⟩
      exact (s v).2
    · intro y hy
      have hy' : (⟨y, hy⟩ : ↥U) - s (π ⟨y, hy⟩) ∈ LinearMap.ker π := by
        rw [LinearMap.mem_ker, map_sub, hs1]
        exact sub_self _
      rw [hex] at hy'
      obtain ⟨w, hw⟩ := hy'
      have hyw : y = ι₁ w + (s (π ⟨y, hy⟩) : W) := by
        have := congrArg Subtype.val hw
        simp only [Submodule.coe_sub] at this
        have h5 : (ι' w : W) = ι₁ w := rfl
        rw [h5] at this
        rw [this]
        abel
      rw [hyw]
      exact Submodule.add_mem_sup ⟨w, rfl⟩ ⟨π ⟨y, hy⟩, rfl⟩
  · rw [eq_bot_iff]
    rintro x ⟨⟨w, rfl⟩, ⟨v, hv⟩⟩
    have hmem : (⟨ι₁ w, hι₁U w⟩ : ↥U) ∈ LinearMap.range ι' := ⟨w, rfl⟩
    rw [← hex, LinearMap.mem_ker] at hmem
    have hsv : s v = ⟨ι₁ w, hι₁U w⟩ := Subtype.ext hv
    rw [← hsv, hs1] at hmem
    rw [hmem] at hv
    simpa using hv.symm

end Models

section Main

variable {G : Type*} [Group G] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

theorem k55_module [Finite G] [Finite W] (ρ : Representation (ZMod 2) G W)
    (hρ : Function.Injective ρ) {L : Subgroup G} (eL : ↥L ≃* GL32)
    {A : Subgroup G} (hA2 : CFSG.IsElementaryAbelian 2 ↥A)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hLA : ⁅L, A⁆ = L)
    (hb : IsBestOffenderOn ρ A ⊤) {F : Subgroup G} (hFL : F ≤ L) (hF : Odd (Nat.card F))
    (hFix : ∀ u ∈ commOn ρ L ⊤, (∀ f ∈ F, ρ f u = u) → u = 0) :
    ∃ τ : GL32 →* (Vec3 ≃ₗ[ZMod 2] Vec3), (τ = repV ∨ τ = repDual) ∧
      ∃ ι₁ ι₂ : Vec3 →ₗ[ZMod 2] W, ModEmb ρ eL τ ι₁ ∧
        ((LinearMap.range ι₁ = commOn ρ L ⊤ ∧ ι₂ = 0) ∨
          (ModEmb ρ eL τ ι₂ ∧ LinearMap.range ι₁ ⊔ LinearMap.range ι₂ = commOn ρ L ⊤ ∧
            LinearMap.range ι₁ ⊓ LinearMap.range ι₂ = ⊥)) := by
  obtain ⟨B, hBN, hB2, hBc, hLB, hUinv, hcen, hbudU, hUU, hUne⟩ :=
    exists_k55_setup ρ hρ eL hA2 hAN hLA hb
  obtain ⟨τ, hτ, M, hM, hMU, hs₁, hcase⟩ :=
    k55_chain ρ eL hBN hB2 hBc hLB hUinv hcen hbudU hFL hF hFix hUne
  refine ⟨τ, hτ, ?_⟩
  obtain ⟨ι₁, hι₁, hr₁⟩ := modEmb_of_secIso_bot ρ eL hM.1 hM.2.1 τ hs₁
  rcases hcase with hMeq | ⟨hM2, hs₂⟩
  · exact ⟨ι₁, 0, hι₁, Or.inl ⟨hr₁.trans hMeq, rfl⟩⟩
  · have hsplit : SplitsFor τ := by
      rcases hτ with rfl | rfl
      · exact splitsFor_repV
      · exact splitsFor_repDual
    obtain ⟨ι₁', ι₂, h1, h2, -, hsup, hinf⟩ :=
      exists_split_embeddings ρ eL hMU hM.1 hM.2.1 hM2.2.1 τ hsplit hs₁ hs₂
    exact ⟨ι₁', ι₂, h1, Or.inr ⟨h2, hsup, hinf⟩⟩

end Main

end CFSG.LocalAnalysis.RankThreeUC.S15.K55Proof
