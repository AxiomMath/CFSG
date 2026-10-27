module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K534Module
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.L32Tools

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K55Proof

open Module Polynomial CFSG.QuasithinUnique.Setup.Family CFSG.Quasithin.H13.NQTerm
  CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF CFSG.RankThree.FFModules
  CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
open scoped commutatorElement

variable {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] def SecIso (ρ : Representation (ZMod 2) G W) {L B : Subgroup G} (eL : ↥L ≃* GL32)
    {Z₀ Z₁ : Submodule (ZMod 2) W} (h₀ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) Z₀)
    (h₁ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) Z₁) (τ : GL32 →* (Vec3 ≃ₗ[ZMod 2] Vec3)) : Prop :=
  ∃ e : Vec3 ≃ₗ[ZMod 2] SecQ Z₀ Z₁, ∀ g v, e (τ g v) =
    secRep ρ (L ⊔ B) h₀ h₁ ⟨((eL.symm g : ↥L) : G), Subgroup.mem_sup_left (eL.symm g).2⟩ (e v)

theorem l32_section_iso [Finite G] [Finite W] (ρ : Representation (ZMod 2) G W) {L B : Subgroup G}
    (eL : ↥L ≃* GL32) (hBN : B ≤ Subgroup.normalizer (L : Set G)) (hLB : ⁅L, B⁆ = L)
    (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hB2 : ∀ b ∈ B, b ^ 2 = 1)
    {Z₀ Z₁ : Submodule (ZMod 2) W} (hmin : IsMinSec ρ (L ⊔ B) Z₀ Z₁)
    (hnt : ¬ SecTrivial ρ L Z₀ Z₁)
    (hcen : ∀ b ∈ B, (∀ k ∈ L, b * k = k * b) → ∀ v ∈ Z₁, ρ b v = v)
    (hbud : 2 ^ secCod ρ B Z₀ Z₁ * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) ≤
      Nat.card B) :
    Nat.card (innImg L B eL) * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) = Nat.card B ∧
      FixedCodimData (innImg L B eL) ∧ secCod ρ B Z₀ Z₁ ≤ 3 ∧
      ((SecIso ρ eL hmin.1 hmin.2.1 repV ∧
          2 ^ (3 - secCod ρ B Z₀ Z₁) = Nat.card (fixVec3 (innImg L B eL))) ∨
        (SecIso ρ eL hmin.1 hmin.2.1 repDual ∧
          2 ^ (3 - secCod ρ B Z₀ Z₁) = Nat.card (fixDual3 (innImg L B eL)))) := by
  classical
  have : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  set H := L ⊔ B with hH
  have hLH : L ≤ H := le_sup_left
  have hBH : B ≤ H := le_sup_right
  obtain ⟨h₀, h₁, hlt, hbet⟩ := hmin
  have hle : Z₀ ≤ Z₁ := hlt.le
  set Q := SecQ Z₀ Z₁ with hQ
  set σ := secRep ρ H h₀ h₁ with hσ
  set σu := σ.asGroupHom with hσu
  have hσu_apply : ∀ h : ↥H, ((σu h : (Module.End (ZMod 2) Q)ˣ) : Module.End (ZMod 2) Q) = σ h :=
    fun h => Representation.asGroupHom_apply σ h
  obtain ⟨hQnt, hirrQ⟩ := secRep_irreducible ⟨h₀, h₁, hlt, hbet⟩
  have : Finite Q := Module.finite_of_finite (ZMod 2)
  set σL : ↥L →* (Module.End (ZMod 2) Q)ˣ := σu.comp (Subgroup.inclusion hLH) with hσL
  set σB : ↥B →* (Module.End (ZMod 2) Q)ˣ := σu.comp (Subgroup.inclusion hBH) with hσB
  have hsimpL : IsSimpleGroup ↥L := by
    have := isSimpleGroup_gl32
    exact eL.isSimpleGroup
  have hσLnt : ∃ k : ↥L, σL k ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hnt
    rw [secTrivial_iff h₀ h₁ hLH]
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
  set A := σB.range with hA
  set eY : ↥Y ≃* GL32 := (MonoidHom.ofInjective hσLinj).symm.trans eL with heY
  have heY_symm : ∀ g : GL32,
      ((eY.symm g : ↥Y) : (Module.End (ZMod 2) Q)ˣ) = σL (eL.symm g) := fun g => rfl
  have hconjB : ∀ (b : ↥B) (k : ↥L), σB b * σL k * (σB b)⁻¹ =
      σL ⟨(b : G) * k * (b : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hBN b.2) k).mp k.2⟩ := by
    intro b k
    simp only [hσL, hσB, MonoidHom.comp_apply, ← map_inv, ← map_mul]
    rfl
  have hAN : A ≤ Subgroup.normalizer (Y : Set (Module.End (ZMod 2) Q)ˣ) := by
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
  have hHle : ∀ h : ↥H, σu h ∈ Y ⊔ A := by
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
      (∀ d ∈ Y ⊔ A, ∀ v ∈ N, (d : Module.End (ZMod 2) Q) v ∈ N) → N = ⊥ ∨ N = ⊤ := by
    intro N hN
    refine hirrQ N fun h q hq => ?_
    have h1 := hN _ (hHle h) q hq
    rwa [hσu_apply] at h1
  have hA1 : A ≠ ⊥ := by
    intro hbot
    obtain ⟨k, hk⟩ := hσLnt
    apply hk
    have hBtriv : ∀ b : ↥B, σB b = 1 := fun b => by
      have h1 : σB b ∈ A := ⟨b, rfl⟩
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
  have hAc : ∀ a ∈ A, ∀ c ∈ A, a * c = c * a := by
    rintro _ ⟨a, rfl⟩ _ ⟨c, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hBc _ a.2 _ c.2)
  have hA2 : ∀ a ∈ A, a ^ 2 = 1 := by
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
  have hcardA : Nat.card A * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) = Nat.card B := by
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
  have hAfin : Finite ↥A := Finite.of_surjective _ σB.rangeRestrict_surjective
  have hAp : IsPGroup 2 ↥A := fun a => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hA2 a a.2)⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hAp
  have hfixeq : fixSub σ (B.subgroupOf H) = LocalAnalysis.CommutingFactor.fixedSub A := by
    ext q
    rw [mem_fixSub, LocalAnalysis.CommutingFactor.mem_fixedSub]
    constructor
    · rintro h _ ⟨b, rfl⟩
      rw [hσB, MonoidHom.comp_apply, hσu_apply]
      exact h _ (Subgroup.mem_subgroupOf.mpr b.2)
    · intro h b hb
      have h1 := h (σB ⟨b, Subgroup.mem_subgroupOf.mp hb⟩) ⟨_, rfl⟩
      rw [hσB, MonoidHom.comp_apply, hσu_apply] at h1
      exact h1
  have hsc0 := secCod_eq h₀ h₁ hle hBH
  rw [← hσ, hfixeq] at hsc0
  have hsc : secCod ρ B Z₀ Z₁ = finrank (ZMod 2) Q -
      finrank (ZMod 2) ↥(LocalAnalysis.CommutingFactor.fixedSub A) := hsc0
  have hcpos : 0 < Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) := Nat.card_pos
  have hs : secCod ρ B Z₀ Z₁ ≤ m := by
    have h1 : 2 ^ secCod ρ B Z₀ Z₁ * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) ≤
        2 ^ m * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) := by
      rw [← hm, hcardA]
      exact hbud
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp (Nat.le_of_mul_le_mul_right h1 hcpos)
  have hfle : finrank (ZMod 2) ↥(LocalAnalysis.CommutingFactor.fixedSub A) ≤ finrank (ZMod 2) Q :=
    Submodule.finrank_le _
  have hcost : finrank (ZMod 2) Q ≤
      m + finrank (ZMod 2) ↥(LocalAnalysis.CommutingFactor.fixedSub A) := by
    omega
  have := hQnt
  obtain ⟨hAY, hmod⟩ := l32_factor hirr hAN eY hA1 hAc hA2 hm hcost
  have hinner : ∀ b ∈ B, ∃ l ∈ L, ∀ k ∈ L, b * k * b⁻¹ = l * k * l⁻¹ := by
    intro b hb
    obtain ⟨l, hl⟩ := hAY ⟨⟨b, hb⟩, rfl⟩
    refine ⟨l, l.2, fun k hk => ?_⟩
    have h1 := hconjB ⟨b, hb⟩ ⟨k, hk⟩
    rw [← hl, ← map_inv, ← map_mul, ← map_mul] at h1
    exact (congrArg Subtype.val (hσLinj h1)).symm
  have hyImg : yImg Y eY A = innImg L B eL := by
    ext g
    rw [mem_yImg, heY_symm, mem_innImg_iff]
    constructor
    · rintro ⟨b, hb⟩
      refine ⟨b, b.2, fun k hk => ?_⟩
      have h1 := hconjB b ⟨k, hk⟩
      rw [hb, ← map_inv, ← map_mul, ← map_mul] at h1
      exact (congrArg Subtype.val (hσLinj h1)).symm
    · rintro ⟨b, hb, hbk⟩
      refine ⟨⟨b, hb⟩, ?_⟩
      set l : ↥L := eL.symm g with hl
      have hc : σB ⟨b, hb⟩ * (σL l)⁻¹ = 1 := by
        refine eq_one_of_commute_of_irreducible hirr hAN eY hA2 _
          (Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨_, rfl⟩)
            (Subgroup.inv_mem _ (Subgroup.mem_sup_left ⟨_, rfl⟩))) ?_
        rintro _ ⟨k, rfl⟩
        set k'' : ↥L := l⁻¹ * k * l with hk''
        have key : σB ⟨b, hb⟩ * σL k'' * (σB ⟨b, hb⟩)⁻¹ = σL k := by
          rw [hconjB]
          congr 1
          apply Subtype.ext
          show b * (k'' : G) * b⁻¹ = (k : G)
          rw [hbk _ k''.2, hk'']
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
        have hk2 : σL k'' = (σL l)⁻¹ * σL k * σL l := by
          rw [hk'', map_mul, map_mul, map_inv]
        rw [hk2] at key
        calc σB ⟨b, hb⟩ * (σL l)⁻¹ * σL k
            = (σB ⟨b, hb⟩ * ((σL l)⁻¹ * σL k * σL l) * (σB ⟨b, hb⟩)⁻¹) *
                (σB ⟨b, hb⟩ * (σL l)⁻¹) := by group
          _ = σL k * (σB ⟨b, hb⟩ * (σL l)⁻¹) := by rw [key]
      exact mul_inv_eq_one.mp hc
  have hcardI : Nat.card (innImg L B eL) * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) =
      Nat.card B := by
    rw [← hyImg, natCard_yImg eY hAY]
    exact hcardA
  have hFix : FixedCodimData (innImg L B eL) := by
    rw [← hyImg]
    set Bh := yImg Y eY A with hBh
    have hB0 : Bh ≠ ⊥ := by
      intro h
      have h1 : Nat.card Bh = 1 := by rw [h]; exact Subgroup.card_bot
      rw [natCard_yImg eY hAY] at h1
      exact hA1 (Subgroup.card_eq_one.mp h1)
    have hBc' : ∀ g ∈ Bh, ∀ h ∈ Bh, g * h = h * g := by
      intro g hg h hh
      apply eY.symm.injective
      apply Subtype.ext
      rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul]
      exact hAc _ (mem_yImg.mp hg) _ (mem_yImg.mp hh)
    have hBsq : ∀ g ∈ Bh, g ^ 2 = 1 := by
      intro g hg
      apply eY.symm.injective
      apply Subtype.ext
      rw [map_pow, map_one, Subgroup.coe_pow, Subgroup.coe_one]
      exact hA2 _ (mem_yImg.mp hg)
    exact GL3_elementary_abelian_fixed_codimensions hB0 hBc' hBsq
  refine ⟨hcardI, hFix, ?_⟩
  have hσg : ∀ g : GL32, σ ⟨((eL.symm g : ↥L) : G), hLH (eL.symm g).2⟩ =
      ((yRep Y eY g : Q ≃ₗ[ZMod 2] Q) : Module.End (ZMod 2) Q) := by
    intro g
    have h1 : ((yRep Y eY g : Q ≃ₗ[ZMod 2] Q) : Module.End (ZMod 2) Q) =
        ((eY.symm g : ↥Y) : (Module.End (ZMod 2) Q)ˣ) := LinearMap.ext fun _ => rfl
    rw [h1, heY_symm, hσL, MonoidHom.comp_apply, hσu_apply]
    rfl
  rcases hmod with hV | hD
  · have h3 : finrank (ZMod 2) Q = 3 := by
      have h1 := card_eq_of_modIso hV
      rw [natCard_Vec3, CFSG.Quasithin.H13.NQTerm.card_eq_two_pow_finrank] at h1
      have h2 : 2 ^ finrank (ZMod 2) Q = 2 ^ 3 := by rw [← h1]; norm_num
      exact Nat.pow_right_injective le_rfl h2
    obtain ⟨e, he⟩ := hV
    have hfV : Nat.card (fixVec3 (innImg L B eL)) =
        2 ^ finrank (ZMod 2) ↥(LocalAnalysis.CommutingFactor.fixedSub A) := by
      rw [← hyImg, ← natCard_fixedSub_of_modIso_repV ⟨e, he⟩, natCard_fixedSub_yRep_yImg eY hAY,
        CFSG.Quasithin.H13.NQTerm.card_eq_two_pow_finrank]
    refine ⟨by omega, .inl ⟨⟨e, fun g v => ?_⟩, ?_⟩⟩
    · rw [he g v]
      exact (congrArg (fun f : Module.End (ZMod 2) Q => f (e v)) (hσg g)).symm
    · rw [hfV]
      congr 1
      omega
  · have h3 : finrank (ZMod 2) Q = 3 := by
      have h1 := card_eq_of_modIso hD
      rw [natCard_Vec3, CFSG.Quasithin.H13.NQTerm.card_eq_two_pow_finrank] at h1
      have h2 : 2 ^ finrank (ZMod 2) Q = 2 ^ 3 := by rw [← h1]; norm_num
      exact Nat.pow_right_injective le_rfl h2
    obtain ⟨e, he⟩ := hD
    have hfD : Nat.card (fixDual3 (innImg L B eL)) =
        2 ^ finrank (ZMod 2) ↥(LocalAnalysis.CommutingFactor.fixedSub A) := by
      rw [← hyImg, ← natCard_fixedSub_of_modIso_repDual ⟨e, he⟩, natCard_fixedSub_yRep_yImg eY hAY,
        CFSG.Quasithin.H13.NQTerm.card_eq_two_pow_finrank]
    refine ⟨by omega, .inr ⟨⟨e, fun g v => ?_⟩, ?_⟩⟩
    · rw [he g v]
      exact (congrArg (fun f : Module.End (ZMod 2) Q => f (e v)) (hσg g)).symm
    · rw [hfD]
      congr 1
      omega

section Chain

theorem exists_isMinSec_above [Finite W] (ρ : Representation (ZMod 2) G W) (H : Subgroup G)
    {M U : Submodule (ZMod 2) W} (hMU : M < U) (hM : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H M)
    (hU : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H U) :
    ∃ M₂ : Submodule (ZMod 2) W, M < M₂ ∧ M₂ ≤ U ∧ IsMinSec ρ H M M₂ := by
  classical
  let S : Set (Submodule (ZMod 2) W) := {Y | M < Y ∧ Y ≤ U ∧ CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H Y}
  have hex : ∃ n, ∃ Y ∈ S, Module.finrank (ZMod 2) Y = n := ⟨_, U, ⟨hMU, le_rfl, hU⟩, rfl⟩
  obtain ⟨Y, hYS, hYn⟩ := Nat.find_spec hex
  have hmin : ∀ Z ∈ S, Nat.find hex ≤ Module.finrank (ZMod 2) Z := fun Z hZ =>
    Nat.find_min' hex ⟨Z, hZ, rfl⟩
  refine ⟨Y, hYS.1, hYS.2.1, hM, hYS.2.2, hYS.1, fun Z hZ hMZ hZY => ?_⟩
  by_cases hZM : Z = M
  · exact Or.inl hZM
  · right
    have hZS : Z ∈ S := ⟨lt_of_le_of_ne hMZ (Ne.symm hZM), hZY.trans hYS.2.1, hZ⟩
    exact Submodule.eq_of_le_of_finrank_le hZY (by rw [hYn]; exact hmin Z hZS)

theorem one_le_secCod_of_not_secTrivial [Finite W] (ρ : Representation (ZMod 2) G W)
    {L B : Subgroup G} (hLB : ⁅L, B⁆ = L) {Z₀ Z₁ : Submodule (ZMod 2) W}
    (h₀ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) Z₀) (h₁ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) Z₁)
    (hnt : ¬ SecTrivial ρ L Z₀ Z₁) : 1 ≤ secCod ρ B Z₀ Z₁ := by
  by_contra h
  apply hnt
  have hsc : secCod ρ B Z₀ Z₁ = 0 := by omega
  have hBtriv : ∀ b ∈ B, ∀ y ∈ Z₁, ρ b y - y ∈ Z₀ := by
    intro b hb y hy
    have hle : Module.finrank (ZMod 2) ↥(relFix ρ B Z₀ Z₁) ≤ Module.finrank (ZMod 2) ↥Z₁ :=
      Submodule.finrank_mono relFix_le
    have h1 : Module.finrank (ZMod 2) ↥Z₁ ≤ Module.finrank (ZMod 2) ↥(relFix ρ B Z₀ Z₁) := by
      unfold secCod at hsc
      omega
    have h2 : relFix ρ B Z₀ Z₁ = Z₁ := Submodule.eq_of_le_of_finrank_le relFix_le h1
    have : y ∈ relFix ρ B Z₀ Z₁ := by rw [h2]; exact hy
    exact this.2 b hb
  exact K534Proof.secTrivial_of_commutator hLB h₀ h₁ hBtriv

theorem same_type {B : Subgroup GL32} (hB : FixedCodimData B) {c₁ c₂ s : ℕ} (hc₁ : 1 ≤ c₁)
    (hc₂ : 1 ≤ c₂) (hs : c₁ + c₂ ≤ s) (hs2 : 2 ^ s ≤ Nat.card B) {P₁ Q₁ P₂ Q₂ : Prop}
    (h₁ : (P₁ ∧ 2 ^ (3 - c₁) = Nat.card (fixVec3 B)) ∨ (Q₁ ∧ 2 ^ (3 - c₁) = Nat.card (fixDual3 B)))
    (h₂ : (P₂ ∧ 2 ^ (3 - c₂) = Nat.card (fixVec3 B)) ∨ (Q₂ ∧ 2 ^ (3 - c₂) = Nat.card (fixDual3 B))) :
    (P₁ ∧ P₂) ∨ (Q₁ ∧ Q₂) := by
  unfold FixedCodimData at hB
  rcases hB with ⟨hB2, -⟩ | ⟨hB4, hfix, -⟩
  · exfalso
    rw [hB2] at hs2
    have : s ≤ 1 := by
      by_contra hcon
      have : 2 ^ 2 ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    omega
  · have hs' : s ≤ 2 := by
      by_contra hcon
      rw [hB4] at hs2
      have : 2 ^ 3 ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have e1 : c₁ = 1 := by omega
    have e2 : c₂ = 1 := by omega
    subst e1 e2
    rcases hfix with ⟨hv, hd⟩ | ⟨hv, hd⟩
    · rcases h₁ with ⟨hp, hq⟩ | ⟨hq, -⟩
      · exfalso; rw [hv] at hq; norm_num at hq
      · rcases h₂ with ⟨hp, hq'⟩ | ⟨hq2, -⟩
        · exfalso; rw [hv] at hq'; norm_num at hq'
        · exact Or.inr ⟨hq, hq2⟩
    · rcases h₁ with ⟨hp, -⟩ | ⟨hq, hq'⟩
      · rcases h₂ with ⟨hp2, -⟩ | ⟨hq2, hq''⟩
        · exact Or.inl ⟨hp, hp2⟩
        · exfalso; rw [hd] at hq''; norm_num at hq''
      · exfalso; rw [hd] at hq'; norm_num at hq'

end Chain

end CFSG.LocalAnalysis.RankThreeUC.S15.K55Proof
