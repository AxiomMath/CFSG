module

public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.SecModel
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.A6Gen
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.A6Nat

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542

open Module Polynomial CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF CFSG.RankThree.FFModules
open scoped commutatorElement

@[expose] noncomputable def fA : (ZMod 2)[X] := X + 1

@[expose] noncomputable def gA : (ZMod 2)[X] := X ^ 2 + X + 1

theorem isCoprime_fA_gA : IsCoprime fA gA := ⟨-X, 1, by unfold fA gA; ring⟩

theorem fA_mul_gA : fA * gA = X ^ 3 + 1 := by
  have h2 : (2 : (ZMod 2)[X]) = 0 := CharTwo.two_eq_zero
  unfold fA gA
  linear_combination (X ^ 2 + X) * h2

theorem aeval_fA_mul_gA_eq_zero {M : Type*} [AddCommMonoid M] [Module (ZMod 2) M]
    {T : Module.End (ZMod 2) M} (hT : T ^ 3 = 1) : aeval T (fA * gA) = 0 := by
  rw [fA_mul_gA]
  simp only [map_add, map_pow, aeval_X, map_one, hT]
  ext v
  simp only [LinearMap.add_apply, Module.End.one_apply, LinearMap.zero_apply]
  rw [← two_smul (ZMod 2) v, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem ker_aeval_fA {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (T : Module.End (ZMod 2) M) :
    LinearMap.ker (aeval T fA) = LinearMap.ker (T - 1) := by
  have h : aeval T fA = T - 1 := by
    unfold fA
    simp only [map_add, aeval_X, map_one]
    ext v
    simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.one_apply]
    have hv : v + v = 0 := by
      rw [← two_smul (ZMod 2) v, show (2 : ZMod 2) = 0 from rfl, zero_smul]
    rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_left hv]
  rw [h]

theorem c3A6_pow_three : c3A6 ^ 3 = 1 := by decide

theorem c33A6_pow_three : c33A6 ^ 3 = 1 := by decide

variable {G : Type*} [Group G] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

theorem secChi_fA_eq_zero_of_secTrivial [Finite W] (ρ : Representation (ZMod 2) G W)
    {H L : Subgroup G} (hLH : L ≤ H) {Z₀ Z₁ : Submodule (ZMod 2) W} (h₀ : GeneralFF.IsInvariant ρ H Z₀)
    (h₁ : GeneralFF.IsInvariant ρ H Z₁) (hle : Z₀ ≤ Z₁) (ht : SecTrivial ρ L Z₀ Z₁) {x y : G} (hx : x ∈ L)
    (hy : y ∈ L) (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) : secChi ρ fA x y Z₀ Z₁ = 0 := by
  have htriv := (secTrivial_iff h₀ h₁ hLH).mp ht
  have key : ∀ z : G, z ∈ L → z ^ 3 = 1 →
      (kerDim ρ fA z Z₁ : ℤ) - kerDim ρ fA z Z₀ = Module.finrank (ZMod 2) (SecQ Z₀ Z₁) := by
    intro z hz hz3
    have hT : (ρ z) ^ 3 = 1 := by rw [← map_pow, hz3, map_one]
    rw [kerDim_sub_eq h₀ h₁ hle isCoprime_fA_gA (hLH hz) (aeval_fA_mul_gA_eq_zero hT)]
    have hone : ∀ q, secRep ρ H h₀ h₁ ⟨z, hLH hz⟩ q = q :=
      htriv ⟨z, hLH hz⟩ (Subgroup.mem_subgroupOf.mpr hz)
    have hker : LinearMap.ker (aeval (secRep ρ H h₀ h₁ ⟨z, hLH hz⟩) fA) = ⊤ := by
      rw [ker_aeval_fA, eq_top_iff]
      intro q _
      rw [LinearMap.mem_ker, LinearMap.sub_apply, hone, Module.End.one_apply, sub_self]
    rw [hker, finrank_top]
  unfold secChi
  rw [key x hx hx3, key y hy hy3]
  ring

theorem a6_section [Finite G] [Finite W] (ρ : Representation (ZMod 2) G W) {L B : Subgroup G}
    (eL : ↥L ≃* alternatingGroup (Fin 6)) (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (hLB : ⁅L, B⁆ = L) (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hB2 : ∀ b ∈ B, b ^ 2 = 1)
    {Z₀ Z₁ : Submodule (ZMod 2) W} (hmin : IsMinSec ρ (L ⊔ B) Z₀ Z₁)
    (hnt : ¬ SecTrivial ρ L Z₀ Z₁)
    (hcen : ∀ b ∈ B, (∀ k ∈ L, b * k = k * b) → ∀ v ∈ Z₁, ρ b v = v)
    (hbud : 2 ^ secCod ρ B Z₀ Z₁ * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) ≤
      Nat.card B) :
    ∃ r : ℕ, r ≤ 3 ∧ 2 ^ r * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) = Nat.card B ∧
      2 * r ≤ 3 * secCod ρ B Z₀ Z₁ ∧
      (secChi ρ fA ((eL.symm c3A6 : ↥L) : G) ((eL.symm c33A6 : ↥L) : G) Z₀ Z₁ = 2 ∨
        secChi ρ fA ((eL.symm c3A6 : ↥L) : G) ((eL.symm c33A6 : ↥L) : G) Z₀ Z₁ = -2) := by
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
    have : IsSimpleGroup (alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
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
  set eY : ↥Y ≃* alternatingGroup (Fin 6) := (MonoidHom.ofInjective hσLinj).symm.trans eL with heY
  have heY_symm : ∀ g : alternatingGroup (Fin 6),
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
  obtain ⟨r', m', hr'card, -, hr3, hmr, hdimle⟩ := a6_short_gen hirr hAN eY hA1 hAc hA2
  have hrm : r' = m := Nat.pow_right_injective le_rfl (hr'card.symm.trans hm)
  subst hrm
  have hdimle' : finrank (ZMod 2) Q ≤ m' * secCod ρ B Z₀ Z₁ := by
    rw [hsc]
    exact hdimle
  have hdim6 : finrank (ZMod 2) Q ≤ 6 := by
    calc finrank (ZMod 2) Q ≤ m' * secCod ρ B Z₀ Z₁ := hdimle'
      _ ≤ m' * r' := Nat.mul_le_mul_left _ hs
      _ ≤ 6 := hmr
  obtain ⟨hdim4, hfixes⟩ := a6_natural _ _ hirr hAN eY hdim6
  refine ⟨r', hr3, by rw [← hm]; exact hcardA, ?_, ?_⟩
  · have h1 : 4 ≤ m' * secCod ρ B Z₀ Z₁ := by
      have h4 : finrank (ZMod 2) Q = 4 := hdim4
      rw [← h4]
      exact hdimle'
    have h2 : 4 * r' ≤ m' * secCod ρ B Z₀ Z₁ * r' := Nat.mul_le_mul_right r' h1
    have h3 : m' * secCod ρ B Z₀ Z₁ * r' = m' * r' * secCod ρ B Z₀ Z₁ := by ring
    have h4 : m' * r' * secCod ρ B Z₀ Z₁ ≤ 6 * secCod ρ B Z₀ Z₁ := Nat.mul_le_mul_right _ hmr
    omega
  · set x : G := ((eL.symm c3A6 : ↥L) : G) with hx
    set y : G := ((eL.symm c33A6 : ↥L) : G) with hy
    have hxH : x ∈ H := hLH (eL.symm c3A6).2
    have hyH : y ∈ H := hLH (eL.symm c33A6).2
    have hσx : σ ⟨x, hxH⟩ = (((eY.symm c3A6 : ↥Y) : (Module.End (ZMod 2) Q)ˣ) :
        Module.End (ZMod 2) Q) := by
      rw [heY_symm, hσL, MonoidHom.comp_apply, hσu_apply]
      rfl
    have hσy : σ ⟨y, hyH⟩ = (((eY.symm c33A6 : ↥Y) : (Module.End (ZMod 2) Q)ˣ) :
        Module.End (ZMod 2) Q) := by
      rw [heY_symm, hσL, MonoidHom.comp_apply, hσu_apply]
      rfl
    have hx3 : (ρ x) ^ 3 = 1 := by
      rw [← map_pow, hx, ← Subgroup.coe_pow, ← map_pow, c3A6_pow_three, map_one, Subgroup.coe_one,
        map_one]
    have hy3 : (ρ y) ^ 3 = 1 := by
      rw [← map_pow, hy, ← Subgroup.coe_pow, ← map_pow, c33A6_pow_three, map_one, Subgroup.coe_one,
        map_one]
    have hkx := kerDim_sub_eq h₀ h₁ hle isCoprime_fA_gA hxH (aeval_fA_mul_gA_eq_zero hx3)
    have hky := kerDim_sub_eq h₀ h₁ hle isCoprime_fA_gA hyH (aeval_fA_mul_gA_eq_zero hy3)
    rw [← hσ, hσx, ker_aeval_fA] at hkx
    rw [← hσ, hσy, ker_aeval_fA] at hky
    unfold secChi
    rw [hkx, hky]
    rcases hfixes with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      rw [h1, h2]
      norm_num
    · right
      rw [h1, h2]
      norm_num

end CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
