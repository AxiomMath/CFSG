module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.FiveThreeAlt.Unique

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt

open Module CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF CFSG.RankThree.FFModules
  CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
open CFSG.Quasithin (fixV IsElemAbelian2 IsQuadratic)
open scoped commutatorElement IsMulCommutative

@[expose] def SecCrit (K : Type) [Group K] (P : ℕ → Prop) : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G L B : Subgroup (MulAut V), Nonempty (↥L ≃* K) → L ≤ G →
    G ≤ Subgroup.normalizer (L : Set (MulAut V)) → B ≤ G → G = L ⊔ B → (∀ y ∈ G, y ^ 2 ∈ L) →
    B ≠ ⊥ → IsElemAbelian2 B → IsQuadratic B →
    (∀ J : Subgroup V, (∀ g ∈ G, ∀ v ∈ J, g v ∈ J) → J = ⊥ ∨ J = ⊤) →
    Nat.card V ≤ Nat.card B * Nat.card (fixV B) →
    (∀ J : Subgroup V, (∀ l ∈ L, ∀ v ∈ J, l v ∈ J) → J = ⊥ ∨ J = ⊤) ∧
      Nat.card B * Nat.card (fixV B) ≤ Nat.card V ∧ P (Nat.card V)

theorem zmodTwo_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide

section Bin

variable {Q : Type} [AddCommGroup Q] [Module (ZMod 2) Q]

@[expose] def topSub (J : Subgroup (Multiplicative ↥(⊤ : Submodule (ZMod 2) Q))) :
    Submodule (ZMod 2) Q where
  carrier := {q | Multiplicative.ofAdd (⟨q, Submodule.mem_top⟩ : ↥(⊤ : Submodule (ZMod 2) Q)) ∈ J}
  add_mem' ha hb := J.mul_mem ha hb
  zero_mem' := J.one_mem
  smul_mem' c q hq := by
    rcases zmodTwo_cases c with rfl | rfl
    · simp only [zero_smul, Set.mem_ofPred_eq]
      exact J.one_mem
    · simpa only [one_smul] using hq

theorem mem_topSub {J : Subgroup (Multiplicative ↥(⊤ : Submodule (ZMod 2) Q))} {q : Q} :
    q ∈ topSub J ↔
      Multiplicative.ofAdd (⟨q, Submodule.mem_top⟩ : ↥(⊤ : Submodule (ZMod 2) Q)) ∈ J :=
  Iff.rfl

@[expose] def binSub (N : Submodule (ZMod 2) Q) :
    Subgroup (Multiplicative ↥(⊤ : Submodule (ZMod 2) Q)) where
  carrier := {v | ((Multiplicative.toAdd v : ↥(⊤ : Submodule (ZMod 2) Q)) : Q) ∈ N}
  mul_mem' ha hb := N.add_mem ha hb
  one_mem' := N.zero_mem
  inv_mem' ha := N.neg_mem ha

theorem mem_binSub {N : Submodule (ZMod 2) Q} {v : Multiplicative ↥(⊤ : Submodule (ZMod 2) Q)} :
    v ∈ binSub N ↔ ((Multiplicative.toAdd v : ↥(⊤ : Submodule (ZMod 2) Q)) : Q) ∈ N :=
  Iff.rfl

theorem topSub_eq_bot_iff (J : Subgroup (Multiplicative ↥(⊤ : Submodule (ZMod 2) Q))) :
    topSub J = ⊥ ↔ J = ⊥ := by
  constructor
  · intro h
    rw [eq_bot_iff]
    intro v hv
    have hq : ((Multiplicative.toAdd v : ↥(⊤ : Submodule (ZMod 2) Q)) : Q) ∈ topSub J := hv
    rw [h, Submodule.mem_bot] at hq
    rw [Subgroup.mem_bot]
    exact Multiplicative.toAdd.injective (Subtype.ext hq)
  · intro h
    rw [eq_bot_iff]
    intro q hq
    rw [mem_topSub, h, Subgroup.mem_bot] at hq
    rw [Submodule.mem_bot]
    exact congrArg Subtype.val (Multiplicative.ofAdd.injective hq)

theorem topSub_eq_top_iff (J : Subgroup (Multiplicative ↥(⊤ : Submodule (ZMod 2) Q))) :
    topSub J = ⊤ ↔ J = ⊤ := by
  constructor
  · intro h
    rw [eq_top_iff]
    intro v _
    have hq : ((Multiplicative.toAdd v : ↥(⊤ : Submodule (ZMod 2) Q)) : Q) ∈ topSub J := by
      rw [h]
      exact Submodule.mem_top
    exact hq
  · intro h
    rw [eq_top_iff]
    intro q _
    rw [mem_topSub, h]
    exact Subgroup.mem_top _

theorem binSub_eq_bot_iff (N : Submodule (ZMod 2) Q) : binSub N = ⊥ ↔ N = ⊥ := by
  constructor
  · intro h
    rw [eq_bot_iff]
    intro q hq
    have hv : Multiplicative.ofAdd (⟨q, Submodule.mem_top⟩ : ↥(⊤ : Submodule (ZMod 2) Q)) ∈
        binSub N := hq
    rw [h, Subgroup.mem_bot] at hv
    rw [Submodule.mem_bot]
    exact congrArg Subtype.val (Multiplicative.ofAdd.injective hv)
  · intro h
    rw [eq_bot_iff]
    intro v hv
    rw [mem_binSub, h, Submodule.mem_bot] at hv
    rw [Subgroup.mem_bot]
    exact Multiplicative.toAdd.injective (Subtype.ext hv)

theorem binSub_eq_top_iff (N : Submodule (ZMod 2) Q) : binSub N = ⊤ ↔ N = ⊤ := by
  constructor
  · intro h
    rw [eq_top_iff]
    intro q _
    have hv : Multiplicative.ofAdd (⟨q, Submodule.mem_top⟩ : ↥(⊤ : Submodule (ZMod 2) Q)) ∈
        binSub N := by
      rw [h]
      exact Subgroup.mem_top _
    exact hv
  · intro h
    rw [eq_top_iff]
    intro v _
    rw [mem_binSub, h]
    exact Submodule.mem_top

theorem card_binTop [Finite Q] :
    Nat.card (Multiplicative ↥(⊤ : Submodule (ZMod 2) Q)) = 2 ^ finrank (ZMod 2) Q := by
  have : Module.Finite (ZMod 2) Q := Module.Finite.of_finite
  change Nat.card ↥(⊤ : Submodule (ZMod 2) Q) = _
  rw [Nat.card_congr (Submodule.topEquiv (R := ZMod 2) (M := Q)).toEquiv,
    Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

end Bin

theorem natCard_submodule_eq {W' : Type} [AddCommGroup W'] [Module (ZMod 2) W'] [Finite W']
    (S : Submodule (ZMod 2) W') : Nat.card ↥S = 2 ^ finrank (ZMod 2) ↥S := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

section Section

variable {G : Type} [Group G] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

theorem secCrit_section [Finite G] [Finite W] (ρ : Representation (ZMod 2) G W) {K : Type} [Group K]
    {P : ℕ → Prop} (hcrit : SecCrit K P) {L B : Subgroup G} [IsSimpleGroup ↥L] (eL : ↥L ≃* K)
    (hBN : B ≤ Subgroup.normalizer (L : Set G)) (hLB : ⁅L, B⁆ = L)
    (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hB2 : ∀ b ∈ B, b ^ 2 = 1)
    {Z₀ Z₁ : Submodule (ZMod 2) W} (hmin : IsMinSec ρ (L ⊔ B) Z₀ Z₁)
    (hnt : ¬ SecTrivial ρ L Z₀ Z₁)
    (hquad : ∀ a ∈ B, ∀ b ∈ B, ∀ z ∈ Z₁, ρ b (ρ a z - z) = ρ a z - z)
    (hcen : ∀ b ∈ B, (∀ k ∈ L, b * k = k * b) → ∀ v ∈ Z₁, ρ b v = v)
    (hbud : 2 ^ secCod ρ B Z₀ Z₁ * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) ≤
      Nat.card B) :
    (∀ Z : Submodule (ZMod 2) W, CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L Z → Z₀ ≤ Z → Z ≤ Z₁ → Z = Z₀ ∨ Z = Z₁) ∧
      Nat.card B ≤ 2 ^ secCod ρ B Z₀ Z₁ * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) ∧
      P (2 ^ finrank (ZMod 2) (SecQ Z₀ Z₁)) := by
  classical
  set H := L ⊔ B with hH
  have hLH : L ≤ H := le_sup_left
  have hBH : B ≤ H := le_sup_right
  have hHN : H ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hBN
  set Q := SecQ Z₀ Z₁ with hQ
  set σ := secRep ρ H hmin.1 hmin.2.1 with hσ
  obtain ⟨hQnt, hirrQ⟩ := secRep_irreducible hmin
  have : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  have : Finite Q := Module.finite_of_finite (ZMod 2)
  have hU : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant σ (⊤ : Subgroup ↥H) (⊤ : Submodule (ZMod 2) Q) :=
    fun _ _ _ _ => Submodule.mem_top
  set φ := resBin σ ⊤ ⊤ hU with hφ
  set L₀ : Subgroup ↥H := L.subgroupOf H with hL₀
  set B₀ : Subgroup ↥H := B.subgroupOf H with hB₀
  set G' := imgBin σ ⊤ ⊤ hU ⊤ with hG'
  set L' := imgBin σ ⊤ ⊤ hU L₀ with hL'
  set B' := imgBin σ ⊤ ⊤ hU B₀ with hB'
  let ι : ↥H → ↥(⊤ : Subgroup ↥H) := fun h => ⟨h, Subgroup.mem_top h⟩
  have hφ1 : ∀ h : ↥H, φ (ι h) = 1 ↔ ∀ q : Q, σ h q = q := fun h => by
    rw [resBin_eq_one_iff]
    exact ⟨fun h1 q => h1 q Submodule.mem_top, fun h1 q _ => h1 q⟩
  let ψL : ↥L →* MulAut (Multiplicative ↥(⊤ : Submodule (ZMod 2) Q)) :=
    φ.comp (Subgroup.topEquiv.symm.toMonoidHom.comp (Subgroup.inclusion hLH))
  have hψL : ∀ l : ↥L, ψL l = φ (ι (Subgroup.inclusion hLH l)) := fun _ => rfl
  have hψLinj : Function.Injective ψL := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψL.ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff ψL).mp h
    · exfalso
      apply hnt
      rw [secTrivial_iff hmin.1 hmin.2.1 hLH]
      intro k hk q
      have h1 : ψL ⟨(k : G), Subgroup.mem_subgroupOf.mp hk⟩ = 1 :=
        ψL.mem_ker.mp (h ▸ Subgroup.mem_top _)
      rw [hψL] at h1
      exact (hφ1 _).mp h1 q
  have hrangeL : ψL.range = L' := by
    ext x
    rw [MonoidHom.mem_range, mem_imgBin]
    constructor
    · rintro ⟨l, rfl⟩
      exact ⟨ι (Subgroup.inclusion hLH l), Subgroup.mem_subgroupOf.mpr l.2, rfl⟩
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨((h : ↥H) : G), Subgroup.mem_subgroupOf.mp hh⟩, rfl⟩
  have hLiso : Nonempty (↥L' ≃* K) :=
    ⟨((MonoidHom.ofInjective hψLinj).trans (MulEquiv.subgroupCongr hrangeL)).symm.trans eL⟩
  have hker : ∀ h : ↥H, (h : G) ∈ B →
      ((∀ q : Q, σ h q = q) ↔ (h : G) ∈ Subgroup.centralizer (L : Set G)) := by
    intro h hhB
    constructor
    · intro h1
      have hφh : φ (ι h) = 1 := (hφ1 h).mpr h1
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have hk' : (h : G) * k * (h : G)⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp (hHN h.2) k).mp hk
      have e1 : ψL ⟨(h : G) * k * (h : G)⁻¹, hk'⟩ = φ (ι h) * ψL ⟨k, hk⟩ * (φ (ι h))⁻¹ := by
        rw [hψL, hψL, ← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [hφh, one_mul, inv_one, mul_one] at e1
      have e2 : (h : G) * k * (h : G)⁻¹ = k := congrArg Subtype.val (hψLinj e1)
      calc k * (h : G) = (h : G) * k * (h : G)⁻¹ * (h : G) := by rw [e2]
        _ = (h : G) * k := by group
    · intro h1 q
      induction q using Submodule.Quotient.induction_on with
      | H z =>
        rw [hσ, secRep_mk]
        congr 1
        apply Subtype.ext
        exact hcen _ hhB (fun k hk => (Subgroup.mem_centralizer_iff.mp h1 k hk).symm) z z.2
  have hcardB₀ : Nat.card ↥B₀ = Nat.card ↥B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBH).toEquiv
  have hcen₀ : Nat.card ↥(cenOn σ B₀ ⊤) = Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨((x : ↥H) : G), Subgroup.mem_subgroupOf.mp x.2.1,
          (hker x (Subgroup.mem_subgroupOf.mp x.2.1)).mp fun q => x.2.2 q Submodule.mem_top⟩
        invFun := fun y => ⟨⟨(y : G), hBH y.2.1⟩, Subgroup.mem_subgroupOf.mpr y.2.1,
          fun q _ => (hker ⟨(y : G), hBH y.2.1⟩ y.2.1).mpr y.2.2 q⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hcardB' : Nat.card ↥B' * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) =
      Nat.card ↥B := by
    rw [← hcen₀, ← hcardB₀]
    exact card_imgBin_mul_card_cenOn le_top
  have hfix : Nat.card ↥(fixV B') = 2 ^ finrank (ZMod 2) ↥(fixSub σ B₀) := by
    rw [card_fixV_imgBin le_top]
    have e : fixOn σ B₀ ⊤ = fixSub σ B₀ := top_inf_eq _
    rw [e, natCard_submodule_eq]
  have hsc := secCod_eq hmin.1 hmin.2.1 hmin.2.2.1.le hBH
  rw [← hσ] at hsc
  have hfle : finrank (ZMod 2) ↥(fixSub σ B₀) ≤ finrank (ZMod 2) Q := Submodule.finrank_le _
  have hcpos : 0 < Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) := Nat.card_pos
  have hirrG : ∀ J : Subgroup (Multiplicative ↥(⊤ : Submodule (ZMod 2) Q)),
      (∀ g ∈ G', ∀ v ∈ J, g v ∈ J) → J = ⊥ ∨ J = ⊤ := by
    intro J hJ
    have hinv : ∀ h : ↥H, ∀ q ∈ topSub J, σ h q ∈ topSub J := by
      intro h q hq
      have h1 := hJ (φ (ι h)) (resBin_mem_imgBin (Subgroup.mem_top h) (Subgroup.mem_top h)) _ hq
      exact h1
    rcases hirrQ (topSub J) hinv with h | h
    · exact Or.inl ((topSub_eq_bot_iff J).mp h)
    · exact Or.inr ((topSub_eq_top_iff J).mp h)
  have hLG' : L' ≤ G' := imgBin_mono le_top
  have hBG' : B' ≤ G' := imgBin_mono le_top
  have hL₀n : ∀ h ∈ (⊤ : Subgroup ↥H), ∀ k ∈ L₀, h * k * h⁻¹ ∈ L₀ := by
    intro h _ k hk
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hHN h.2) k).mp hk
  have hG'N : G' ≤ Subgroup.normalizer (L' : Set (MulAut _)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      exact imgBin_normal hL₀n x hx n hn
    · intro hn
      have h1 := imgBin_normal hL₀n x⁻¹ (G'.inv_mem hx) _ hn
      simpa [mul_assoc] using h1
  have hsupH : L₀ ⊔ B₀ = ⊤ := by
    rw [hL₀, hB₀, ← Subgroup.subgroupOf_sup hLH hBH, ← hH, Subgroup.subgroupOf_self]
  have hG'eq : G' = L' ⊔ B' := by
    have e : imgBin σ ⊤ ⊤ hU (L₀ ⊔ B₀) = L' ⊔ B' := imgBin_sup le_top le_top
    rw [hsupH] at e
    exact e
  have hsq : ∀ y ∈ G', y ^ 2 ∈ L' := by
    intro y hy
    obtain ⟨x, -, rfl⟩ := mem_imgBin.mp hy
    have hmem : ((x : ↥H) : G) ∈ ((L ⊔ B : Subgroup G) : Set G) := (x : ↥H).2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left L B hBN] at hmem
    obtain ⟨l, hl, b, hb, hlb⟩ := hmem
    have hlb' : l * b = ((x : ↥H) : G) := hlb
    have hx2 : ((x : ↥H) : G) ^ 2 ∈ L := by
      have hbl : b * l * b⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hBN hb) l).mp hl
      have e : ((x : ↥H) : G) ^ 2 = l * (b * l * b⁻¹) * b ^ 2 := by
        rw [← hlb', pow_two, pow_two]
        group
      rw [e, hB2 b hb, mul_one]
      exact L.mul_mem hl hbl
    rw [← map_pow]
    refine mem_imgBin.mpr ⟨x ^ 2, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    exact hx2
  have hB'ne : B' ≠ ⊥ := by
    intro hbot
    rw [hB', imgBin_eq_bot_iff le_top] at hbot
    have hBC : B ≤ Subgroup.centralizer (L : Set G) := by
      intro b hb
      have h1 := hbot (Subgroup.mem_subgroupOf.mpr hb : (⟨b, hBH hb⟩ : ↥H) ∈ B₀)
      exact (hker ⟨b, hBH hb⟩ hb).mp fun q => h1.2 q Submodule.mem_top
    have h2 : ⁅L, B⁆ = ⊥ := by
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hBC
    rw [hLB] at h2
    obtain ⟨a, b, hab⟩ := exists_pair_ne ↥L
    apply hab
    have ha : a = 1 := Subtype.ext (Subgroup.mem_bot.mp (h2 ▸ a.2))
    have hb' : b = 1 := Subtype.ext (Subgroup.mem_bot.mp (h2 ▸ b.2))
    rw [ha, hb']
  have hB'e : IsElemAbelian2 B' := by
    refine isElemAbelian2_imgBin le_top fun a ha b hb => ⟨fun u _ => ?_, fun u _ => ?_⟩
    · have e : a * b * a⁻¹ * b⁻¹ = 1 := by
        apply Subtype.ext
        have hab := hBc _ (Subgroup.mem_subgroupOf.mp ha) _ (Subgroup.mem_subgroupOf.mp hb)
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
        rw [hab]
        group
      rw [e, map_one]
      rfl
    · have e : a * a = 1 := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_one]
        rw [← pow_two]
        exact hB2 _ (Subgroup.mem_subgroupOf.mp ha)
      rw [e, map_one]
      rfl
  have hB'q : IsQuadratic B' := by
    refine isQuadratic_imgBin le_top ?_
    show commOn σ B₀ ⊤ ≤ fixSub σ B₀
    rw [commOn, Submodule.span_le]
    rintro _ ⟨a, ha, u, -, rfl⟩
    rw [SetLike.mem_coe, mem_fixSub]
    intro b hb
    induction u using Submodule.Quotient.induction_on with
    | H z =>
      rw [hσ, secRep_mk, ← Submodule.Quotient.mk_sub, secRep_mk]
      congr 1
      apply Subtype.ext
      exact hquad _ (Subgroup.mem_subgroupOf.mp ha) _ (Subgroup.mem_subgroupOf.mp hb) z z.2
  have hoff : Nat.card (Multiplicative ↥(⊤ : Submodule (ZMod 2) Q)) ≤
      Nat.card ↥B' * Nat.card ↥(fixV B') := by
    rw [card_binTop, hfix]
    have h1 : 2 ^ secCod ρ B Z₀ Z₁ ≤ Nat.card ↥B' := by
      have h2 : 2 ^ secCod ρ B Z₀ Z₁ * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) ≤
          Nat.card ↥B' * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) := by
        rw [hcardB']
        exact hbud
      exact Nat.le_of_mul_le_mul_right h2 hcpos
    rw [hsc] at h1
    calc 2 ^ finrank (ZMod 2) Q
        = 2 ^ (finrank (ZMod 2) Q - finrank (ZMod 2) ↥(fixSub σ B₀)) *
            2 ^ finrank (ZMod 2) ↥(fixSub σ B₀) := by
          rw [← pow_add, Nat.sub_add_cancel hfle]
      _ ≤ Nat.card ↥B' * 2 ^ finrank (ZMod 2) ↥(fixSub σ B₀) := Nat.mul_le_mul_right _ h1
  have hV' : ∀ v : Multiplicative ↥(⊤ : Submodule (ZMod 2) Q), v ^ 2 = 1 := fun v => by
    rw [pow_two]
    exact binU_sq ⊤ v
  obtain ⟨hirrL, hover, hP⟩ := hcrit _ hV' G' L' B' hLiso hLG' hG'N hBG' hG'eq hsq hB'ne hB'e
    hB'q hirrG hoff
  refine ⟨fun Z hZ hZ0 hZ1 => ?_, ?_, ?_⟩
  ·
    set N : Submodule (ZMod 2) Q := (Z.comap Z₁.subtype).map (Z₀.comap Z₁.subtype).mkQ with hN
    have hNinv : ∀ g ∈ L', ∀ v ∈ binSub N, g v ∈ binSub N := by
      intro g hg v hv
      obtain ⟨x, hx, rfl⟩ := mem_imgBin.mp hg
      rw [mem_binSub, resBin_apply_val]
      obtain ⟨z, hz, hzv⟩ := hv
      rw [← hzv]
      refine ⟨⟨ρ (x : ↥H) z, hmin.2.1 _ (x : ↥H).2 z z.2⟩,
        hZ _ (Subgroup.mem_subgroupOf.mp hx) z hz, ?_⟩
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, hσ, secRep_mk]
    rcases hirrL (binSub N) hNinv with hb | ht
    · left
      have hb' := (binSub_eq_bot_iff N).mp hb
      refine le_antisymm (fun z hz => ?_) hZ0
      have h1 : (Z₀.comap Z₁.subtype).mkQ ⟨z, hZ1 hz⟩ ∈ N := ⟨⟨z, hZ1 hz⟩, hz, rfl⟩
      rw [hb', Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1
      exact h1
    · right
      have ht' := (binSub_eq_top_iff N).mp ht
      refine le_antisymm hZ1 (fun u hu => ?_)
      have h1 : (Z₀.comap Z₁.subtype).mkQ ⟨u, hu⟩ ∈ N := by rw [ht']; exact Submodule.mem_top
      obtain ⟨z, hz, hzu⟩ := h1
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hzu
      have h2 : ((z - ⟨u, hu⟩ : ↥Z₁) : W) ∈ Z₀ := hzu
      have h3 : (u : W) = (z : W) - ((z - ⟨u, hu⟩ : ↥Z₁) : W) := by simp
      rw [h3]
      exact Z.sub_mem hz (hZ0 h2)
  ·
    rw [card_binTop, hfix] at hover
    have h1 : Nat.card ↥B' ≤ 2 ^ secCod ρ B Z₀ Z₁ := by
      rw [hsc]
      have h2 : Nat.card ↥B' * 2 ^ finrank (ZMod 2) ↥(fixSub σ B₀) ≤
          2 ^ (finrank (ZMod 2) Q - finrank (ZMod 2) ↥(fixSub σ B₀)) *
            2 ^ finrank (ZMod 2) ↥(fixSub σ B₀) := by
        rw [← pow_add, Nat.sub_add_cancel hfle]
        exact hover
      exact Nat.le_of_mul_le_mul_right h2 (pow_pos (by norm_num) _)
    rw [← hcardB']
    exact Nat.mul_le_mul_right _ h1
  · rw [← card_binTop]
    exact hP

theorem commOn_quot_of_secCrit [Finite G] [Finite W] (ρ : Representation (ZMod 2) G W)
    (hρ : Function.Injective ρ) {K : Type} [Group K] [IsSimpleGroup K]
    (hKZ : Subgroup.center K = ⊥) (hKnab : ∃ a b : K, a * b ≠ b * a) {P : ℕ → Prop}
    (hcrit : SecCrit K P) {L : Subgroup G} (eL : ↥L ≃* K) {A : Subgroup G}
    (hA2 : CFSG.IsElementaryAbelian 2 ↥A) (hAN : A ≤ Subgroup.normalizer (L : Set G))
    (hLA : ⁅L, A⁆ = L) (hb : IsBestOffenderOn ρ A ⊤) :
    (∀ Z : Submodule (ZMod 2) W, CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L Z → fixOn ρ L (commOn ρ L ⊤) ≤ Z →
      Z ≤ commOn ρ L ⊤ → Z = fixOn ρ L (commOn ρ L ⊤) ∨ Z = commOn ρ L ⊤) ∧
    ∃ k, finrank (ZMod 2) ↥(commOn ρ L ⊤) = finrank (ZMod 2) ↥(fixOn ρ L (commOn ρ L ⊤)) + k ∧
      P (2 ^ k) := by
  classical
  have : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  have hsimpL : IsSimpleGroup ↥L := eL.isSimpleGroup
  obtain ⟨hq, hLL, -, hLnab⟩ := isQuasisimple_of_mulEquiv hKZ hKnab eL
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
  have hcpos : 0 < Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) := Nat.card_pos
  have hsec : ∀ Z₀ Z₁ : Submodule (ZMod 2) W, Z₁ ≤ U → IsMinSec ρ (L ⊔ B) Z₀ Z₁ →
      ¬ SecTrivial ρ L Z₀ Z₁ →
      (∀ Z : Submodule (ZMod 2) W, CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L Z → Z₀ ≤ Z → Z ≤ Z₁ → Z = Z₀ ∨ Z = Z₁) ∧
      2 ^ secCod ρ B Z₀ Z₁ * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) =
        Nat.card B ∧
      P (2 ^ finrank (ZMod 2) (SecQ Z₀ Z₁)) := by
    intro Z₀ Z₁ hZ₁ hmin hnt
    have hmono : secCod ρ B Z₀ Z₁ ≤ secCod ρ B ⊥ U :=
      secCod_mono_sub bot_le hmin.2.2.1.le hZ₁ (isInvariant_mono le_sup_right hmin.1)
        (isInvariant_mono le_sup_right hmin.2.1)
    have hbud : 2 ^ secCod ρ B Z₀ Z₁ * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) ≤
        Nat.card B :=
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hmono)).trans hbudU
    have hquad₁ : ∀ a ∈ B, ∀ b ∈ B, ∀ z ∈ Z₁, ρ b (ρ a z - z) = ρ a z - z := by
      intro a ha b hb z hz
      have h1 : ρ a z - z ∈ commOn ρ B U :=
        Submodule.subset_span ⟨a, ha, z, hZ₁ hz, rfl⟩
      exact mem_fixSub.mp (hquad h1) b hb
    obtain ⟨hirr, hge, hP⟩ := secCrit_section ρ hcrit eL hBN hLB hBc hB2 hmin hnt hquad₁
      (fun b hb hbL v hv => hcen b hb hbL v (hZ₁ hv)) hbud
    exact ⟨hirr, le_antisymm hbud hge, hP⟩
  obtain ⟨Y₀, Y₁, -, hY₁, hminY, hntY⟩ :=
    exists_isMinSec_not_secTrivial hLL h₀ hUinv bot_le hntU
  set r := secCod ρ B Y₀ Y₁ with hr
  have hrcard : 2 ^ r * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) = Nat.card B :=
    (hsec Y₀ Y₁ hY₁ hminY hntY).2.1
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
  have hcostQ : ∀ Z₀ Z₁ : Submodule (ZMod 2) W, Z₁ ≤ U → IsMinSec ρ (L ⊔ B) Z₀ Z₁ →
      ¬ SecTrivial ρ L Z₀ Z₁ → r ≤ secCod ρ B Z₀ Z₁ := by
    intro Z₀ Z₁ hZ₁ hmin hnt
    have h1 := (hsec Z₀ Z₁ hZ₁ hmin hnt).2.1
    have h2 : 2 ^ secCod ρ B Z₀ Z₁ * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) =
        2 ^ r * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) := by rw [h1, hrcard]
    exact (Nat.pow_right_injective le_rfl (Nat.eq_of_mul_eq_mul_right hcpos h2)).ge
  have hminCU := isMinSec_of_cost ρ hLL hBN hUinv hUU hntU hr1 hsU hcostQ
  set C := fixOn ρ L U with hC
  have hntCU : ¬ SecTrivial ρ L C U := by
    intro ht
    apply hminCU.2.2.1.ne
    apply le_antisymm hminCU.2.2.1.le
    have h1 : commOn ρ L U ≤ C := by
      rw [commOn, Submodule.span_le]
      rintro _ ⟨k, hk, u, hu, rfl⟩
      exact ht k hk u hu
    have h2 : commOn ρ L U = U := hUU
    exact (h2 ▸ h1 : U ≤ C)
  obtain ⟨hirr, -, hP⟩ := hsec C U le_rfl hminCU hntCU
  refine ⟨hirr, finrank (ZMod 2) (SecQ C U), ?_, hP⟩
  have h1 := finrank_secQ (Z₀ := C) (Z₁ := U) hminCU.2.2.1.le
  omega

end Section

end CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt
