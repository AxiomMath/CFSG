module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZQ14
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZQ4C

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.D4Three
  CFSG.RankThree.PartTwo.Census.Carrier.D4Even


section Three

variable {L : Type*} [AddCommGroup L] [Module (ZMod 3) L] [Finite L]

theorem trivial_of_card_three (hL : Nat.card L = 3) (t₁ t₂ : L →ₗ[ZMod 3] L)
    (h₁ : ∀ x, t₁ (t₁ x) = x) (h₂ : ∀ x, t₂ (t₂ x) = x) (B : L ≃ₗ[ZMod 3] L)
    (hB₁ : ∀ x, B (t₁ x) = t₂ (B x)) (hB₂ : ∀ x, B (t₂ x) = t₁ (t₂ (B x))) :
    (∀ x, t₁ x = x) ∧ ∀ x, t₂ x = x := by
  haveI : Module.Finite (ZMod 3) L := Module.Finite.of_finite
  have hrank : Module.finrank (ZMod 3) L = 1 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := L)
    rw [hL, Nat.card_zmod] at h
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3)
      (by simpa using h.symm : 3 ^ Module.finrank (ZMod 3) L = 3 ^ 1)
  obtain ⟨v, hv, hspan⟩ := finrank_eq_one_iff'.1 hrank
  have hsc : ∀ t : L →ₗ[ZMod 3] L, ∃ c : ZMod 3, ∀ x, t x = c • x := by
    intro t
    obtain ⟨c, hc⟩ := hspan (t v)
    refine ⟨c, fun x => ?_⟩
    obtain ⟨d, rfl⟩ := hspan x
    rw [map_smul, ← hc, smul_comm]
  obtain ⟨c₁, hc₁⟩ := hsc t₁
  obtain ⟨c₂, hc₂⟩ := hsc t₂
  have hsq : ∀ (c : ZMod 3) (t : L →ₗ[ZMod 3] L) (_ : ∀ x, t (t x) = x) (_ : ∀ x, t x = c • x),
      c * c = 1 := by
    intro c t ht hct
    have h := ht v
    rw [hct, hct, smul_smul] at h
    have : (c * c - 1) • v = 0 := by rw [sub_smul, h, one_smul, sub_self]
    rcases smul_eq_zero.1 this with h0 | h0
    · exact sub_eq_zero.1 h0
    · exact absurd h0 hv
  have e1 := hsq c₁ t₁ h₁ hc₁
  have e2 := hsq c₂ t₂ h₂ hc₂
  obtain ⟨w, hw⟩ := B.surjective v
  have e3 : c₁ = c₂ := by
    have h := hB₁ w
    rw [hc₁, hc₂, map_smul, hw] at h
    have : (c₁ - c₂) • v = 0 := by rw [sub_smul, h, sub_self]
    rcases smul_eq_zero.1 this with h0 | h0
    · exact sub_eq_zero.1 h0
    · exact absurd h0 hv
  have e4 : c₂ = c₁ * c₂ := by
    have h := hB₂ w
    rw [hc₂, map_smul, hw, hc₂, hc₁, smul_smul] at h
    have : (c₂ - c₁ * c₂) • v = 0 := by rw [sub_smul, h, sub_self]
    rcases smul_eq_zero.1 this with h0 | h0
    · exact sub_eq_zero.1 h0
    · exact absurd h0 hv
  have key : ∀ a b : ZMod 3, a * a = 1 → b * b = 1 → a = b → b = a * b → a = 1 ∧ b = 1 := by decide
  obtain ⟨k1, k2⟩ := key c₁ c₂ e1 e2 e3 e4
  exact ⟨fun x => by rw [hc₁, k1, one_smul], fun x => by rw [hc₂, k2, one_smul]⟩

end Three

section Image

variable {G : Type*} [Group G] [Finite G] {H N : Subgroup G}

theorem Lyr.relIndex_inf_eq (h : IsLayer H N) (A : Subgroup G) :
    (A ⊓ N).relIndex (A ⊓ H) =
      Nat.card {z : Lyr h | ∃ a, ∃ ha : a ∈ A, ∃ haH : a ∈ H, Lyr.mk h ⟨a, haH⟩ = z} := by
  letI := h.normal
  let f : ↥(A ⊓ H) →* H ⧸ N.subgroupOf H :=
    (QuotientGroup.mk' (N.subgroupOf H)).comp (Subgroup.inclusion inf_le_right)
  have hker : f.ker = (A ⊓ N).subgroupOf (A ⊓ H) := by
    ext ⟨a, ha⟩
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    change (QuotientGroup.mk (⟨a, ha.2⟩ : H) : H ⧸ N.subgroupOf H) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact ⟨fun hn => ⟨ha.1, hn⟩, fun hn => hn.2⟩
  have hidx : (A ⊓ N).relIndex (A ⊓ H) = Nat.card f.range := by
    rw [← Subgroup.index_ker, hker]; rfl
  rw [hidx]
  refine Nat.card_congr (Equiv.ofBijective
    (fun q : f.range => (⟨Additive.ofMul q.1, ?_⟩ :
      {z : Lyr h | ∃ a, ∃ ha : a ∈ A, ∃ haH : a ∈ H, Lyr.mk h ⟨a, haH⟩ = z})) ⟨?_, ?_⟩)
  · obtain ⟨⟨a, ha⟩, hq⟩ := q.2
    exact ⟨a, ha.1, ha.2, by rw [← hq]; rfl⟩
  · intro q q' hqq
    have h1 : Additive.ofMul q.1 = Additive.ofMul q'.1 :=
      congrArg (fun z : {z : Lyr h | ∃ a, ∃ ha : a ∈ A, ∃ haH : a ∈ H, Lyr.mk h ⟨a, haH⟩ = z} =>
        (z : Lyr h)) hqq
    exact Subtype.ext (Additive.ofMul.injective h1)
  · rintro ⟨z, a, haA, haH, rfl⟩
    exact ⟨⟨f ⟨a, haA, haH⟩, ⟨a, haA, haH⟩, rfl⟩, Subtype.ext rfl⟩

end Image

section N1

variable {K : Type} [Field K] [Finite K] [CharP K 3]

local notation "Jout" => ({0, 1, 3} : Set (Fin Tag.D4.rank))

theorem kappa_mul {M : Type*} [Group M] (x w₁ w₂ : M)
    (hc : w₁ * (x * w₂ * x⁻¹ * w₂⁻¹) = (x * w₂ * x⁻¹ * w₂⁻¹) * w₁) :
    x * (w₁ * w₂) * x⁻¹ * (w₁ * w₂)⁻¹ =
      (x * w₁ * x⁻¹ * w₁⁻¹) * (x * w₂ * x⁻¹ * w₂⁻¹) := by
  have e : x * (w₁ * w₂) * x⁻¹ * (w₁ * w₂)⁻¹ =
      (x * w₁ * x⁻¹ * w₁⁻¹) * (w₁ * (x * w₂ * x⁻¹ * w₂⁻¹) * w₁⁻¹) := by group
  rw [e, hc]; group

theorem J013_trivial_H2 (hK : Nat.card K = 3) {φ : ModGL Tag.D4 K →* ModGL Tag.D4 K}
    {Γ₁ Γ₂ : ModGL Tag.D4 K} (G : A4Grp Jout φ Γ₁ Γ₂) {c : ModGL Tag.D4 K}
    (hc : c ∈ degSeries Tag.D4 K Jout 2) : Γ₁ * c * Γ₁⁻¹ = c ∧ Γ₂ * c * Γ₂⁻¹ = c := by
  haveI := finite_modGL (τ := Tag.D4) (K := K)
  have hd2 : (1 : ℤ) ≤ 2 := by norm_num
  have hL2 := isLayer_degSeries (K := K) (J := Jout) hd2
  have hcard : Nat.card (Lyr hL2) = 3 := by
    rw [card_layer hd2]
    have h1 : (degLayerRoots Tag.D4 Jout 2).ncard = 1 := ncard_layer_J013_two
    rw [h1, pow_one, hK]
  obtain ⟨hT1, hT2⟩ := trivial_of_card_three hcard (lconj G.n₁ hd2) (lconj G.n₂ hd2)
    (G.layer_inv₁ hd2) (G.layer_inv₂ hd2) (G.layerB hd2) (G.layer_B₁ hd2) (G.layer_B₂ hd2)
  have h3 : degSeries Tag.D4 K Jout (2 + 1) = ⊥ := degSeries_J013_three (by norm_num)
  have key : ∀ (g : ModGL Tag.D4 K) (hg : NormAll Jout g),
      (∀ z, lconj hg hd2 z = z) → g * c * g⁻¹ = c := by
    intro g hg hT
    have h := hT (Lyr.mk hL2 ⟨c, hc⟩)
    rw [lconj_mk, Lyr.mk_eq_mk] at h
    have h' : ((g * c * g⁻¹)⁻¹ * c) ∈ degSeries Tag.D4 K Jout (2 + 1) := h
    rw [h3, Subgroup.mem_bot, inv_mul_eq_one] at h'
    exact h'
  exact ⟨key Γ₁ G.n₁ hT1, key Γ₂ G.n₂ hT2⟩

theorem J013_n1 (hK : Nat.card K = 3) (hK2 : ringChar K ≠ 2)
    {φ : ModGL Tag.D4 K →* ModGL Tag.D4 K}
    {Γ₁ Γ₂ c₁ : ModGL Tag.D4 K} {a₁ : Fin Tag.D4.rank → Kˣ} (G : A4Grp Jout φ Γ₁ Γ₂)
    (hc₁ : c₁ ∈ parabolicSubgroup Tag.D4 K Jout) (hΓ₁ : Γ₁ = c₁ * rootDiagUnit Tag.D4 a₁)
    (hne₁ : ∃ x ∈ adjointGroup Tag.D4 K, Γ₁ * x * Γ₁⁻¹ ≠ x)
    {A : Subgroup (ModGL Tag.D4 K)} (hA : A ≤ parabolicRadical Tag.D4 K Jout)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hA₁ : ∀ a ∈ A, Γ₁ * a * Γ₁⁻¹ = a) (hA₂ : ∀ a ∈ A, Γ₂ * a * Γ₂⁻¹ = a)
    (h27 : 27 ≤ Nat.card A) : False := by
  classical
  haveI := finite_modGL (τ := Tag.D4) (K := K)
  have hd1 : (1 : ℤ) ≤ 1 := le_refl 1
  have hd2 : (1 : ℤ) ≤ 2 := by norm_num
  have hL1 := isLayer_degSeries (K := K) (J := Jout) hd1
  have hL2 := isLayer_degSeries (K := K) (J := Jout) hd2
  have hL1card : Nat.card (Lyr hL1) = 3 ^ 8 := by
    rw [card_layer hd1]
    have h8 : (degLayerRoots Tag.D4 Jout 1).ncard = 8 := ncard_layer_J013_one
    rw [h8, hK]
  have hL2card : Nat.card (Lyr hL2) = 3 := by
    rw [card_layer hd2]
    have h1 : (degLayerRoots Tag.D4 Jout 2).ncard = 1 := ncard_layer_J013_two
    rw [h1, pow_one, hK]
  have hS1 : Nat.card (fixSp (lconj G.n₁ hd1) ⊓ fixSp (lconj G.n₂ hd1) :
      Submodule (ZMod 3) (Lyr hL1)) ≤ 9 := by
    have hfix := J013_card_fix hK2 G hc₁ hΓ₁ hne₁
    have h4 : Nat.card (fixSp (lconj G.n₁ hd1) ⊓ fixSp (lconj G.n₂ hd1) :
        Submodule (ZMod 3) (Lyr hL1)) ^ 4 ≤ 9 ^ 4 := by
      calc _ ≤ Nat.card (Lyr hL1) := hfix
        _ = 9 ^ 4 := by rw [hL1card]; norm_num
    exact (Nat.pow_le_pow_iff_left (by norm_num : (4 : ℕ) ≠ 0)).1 h4
  have hAH : A ⊓ degSeries Tag.D4 K Jout 1 = A := inf_eq_left.2 (by rwa [degSeries_one])
  have hmem1 : ∀ a (ha : a ∈ A) (haH : a ∈ degSeries Tag.D4 K Jout 1),
      Lyr.mk hL1 ⟨a, haH⟩ ∈ ((fixSp (lconj G.n₁ hd1) ⊓ fixSp (lconj G.n₂ hd1) :
        Submodule (ZMod 3) (Lyr hL1)) : Set (Lyr hL1)) := by
    intro a ha haH
    refine ⟨mem_fixSp.2 ?_, mem_fixSp.2 ?_⟩
    · rw [lconj_mk]; congr 1; exact Subtype.ext (hA₁ a ha)
    · rw [lconj_mk]; congr 1; exact Subtype.ext (hA₂ a ha)
  set I₁ : Set (Lyr hL1) := {z | ∃ a, ∃ ha : a ∈ A, ∃ haH : a ∈ degSeries Tag.D4 K Jout 1,
    Lyr.mk hL1 ⟨a, haH⟩ = z} with hI₁
  set S₁ : Set (Lyr hL1) := ((fixSp (lconj G.n₁ hd1) ⊓ fixSp (lconj G.n₂ hd1) :
    Submodule (ZMod 3) (Lyr hL1)) : Set (Lyr hL1)) with hS₁
  have hIS : I₁ ⊆ S₁ := by
    rintro _ ⟨a, ha, haH, rfl⟩
    exact hmem1 a ha haH
  have hrel := Lyr.relIndex_inf_eq hL1 A
  have h1 := Subgroup.relIndex_mul_card (H := A ⊓ degSeries Tag.D4 K Jout (1 + 1))
    (K := A ⊓ degSeries Tag.D4 K Jout 1)
  have e : (A ⊓ degSeries Tag.D4 K Jout (1 + 1)) ⊓ (A ⊓ degSeries Tag.D4 K Jout 1) =
      A ⊓ degSeries Tag.D4 K Jout (1 + 1) := inf_eq_left.2 (inf_le_inf_left A hL1.le)
  rw [e, hrel, hAH] at h1
  have h2 := card_inf_le_mul hL2 A (Set.univ : Set (Lyr hL2)) (fun _ _ _ => Set.mem_univ _)
  have h3 : degSeries Tag.D4 K Jout (2 + 1) = ⊥ := degSeries_J013_three (by norm_num)
  have hbot : Nat.card ↥(A ⊓ degSeries Tag.D4 K Jout (2 + 1)) = 1 := by
    rw [h3, inf_bot_eq]; exact Subgroup.card_bot
  rw [hbot, mul_one, Nat.card_univ, hL2card] at h2
  have hS1' : Nat.card S₁ ≤ 9 := hS1
  have hI : Nat.card I₁ ≤ 9 := le_trans (Nat.card_mono (Set.toFinite S₁) hIS) hS1'
  have hAb : Nat.card ↥(A ⊓ degSeries Tag.D4 K Jout 2) = 3 ∧ Nat.card I₁ = 9 := by
    have h2' : Nat.card ↥(A ⊓ degSeries Tag.D4 K Jout 2) ≤ 3 := h2
    have h1' : Nat.card I₁ * Nat.card ↥(A ⊓ degSeries Tag.D4 K Jout 2) = Nat.card A := h1
    constructor <;> nlinarith
  obtain ⟨hAb2, hAbI⟩ := hAb
  have hIeq : I₁ = S₁ := by
    refine Set.eq_of_subset_of_ncard_le hIS ?_ (Set.toFinite S₁)
    have : S₁.ncard ≤ 9 := by rw [← Nat.card_coe_set_eq]; exact hS1'
    have h9 : I₁.ncard = 9 := by rw [← Nat.card_coe_set_eq]; exact hAbI
    omega
  have hH2card : Nat.card (degSeries Tag.D4 K Jout 2) = 3 := by
    rw [card_degSeries (by norm_num : (1 : ℤ) ≤ 2)]
    have : (degSet Tag.D4 Jout 2).ncard = 1 := ncard_degSet_J013_two
    rw [this, pow_one, hK]
  have hH2A : degSeries Tag.D4 K Jout 2 ≤ A := by
    have hle : A ⊓ degSeries Tag.D4 K Jout 2 ≤ degSeries Tag.D4 K Jout 2 := inf_le_right
    have := Subgroup.eq_of_le_of_card_ge hle (by rw [hH2card, hAb2])
    exact this ▸ inf_le_left
  obtain ⟨x, hxA, hx2⟩ : ∃ x ∈ A, x ∉ degSeries Tag.D4 K Jout 2 := by
    by_contra hcon
    push Not at hcon
    have hle : A ≤ degSeries Tag.D4 K Jout 2 := hcon
    have := Subgroup.card_le_of_le hle
    omega
  have hxQ : x ∈ parabolicRadical Tag.D4 K Jout := hA hxA
  obtain ⟨y, hyQ, hxy⟩ : ∃ y ∈ parabolicRadical Tag.D4 K Jout, x * y ≠ y * x := by
    by_contra hcon
    push Not at hcon
    exact hx2 (d3Q013Center_holds K x hxQ hcon)
  have hxH : x ∈ degSeries Tag.D4 K Jout 1 := by rw [degSeries_one]; exact hxQ
  have hyH : y ∈ degSeries Tag.D4 K Jout 1 := by rw [degSeries_one]; exact hyQ
  have hxf₃ : (Γ₁ * Γ₂) * x * (Γ₁ * Γ₂)⁻¹ = x := by
    calc (Γ₁ * Γ₂) * x * (Γ₁ * Γ₂)⁻¹ = Γ₁ * (Γ₂ * x * Γ₂⁻¹) * Γ₁⁻¹ := by group
      _ = x := by rw [hA₂ x hxA, hA₁ x hxA]
  have hcf₃ : ∀ c ∈ degSeries Tag.D4 K Jout 2, (Γ₁ * Γ₂) * c * (Γ₁ * Γ₂)⁻¹ = c := by
    intro c hc
    obtain ⟨h1, h2⟩ := J013_trivial_H2 hK G hc
    calc (Γ₁ * Γ₂) * c * (Γ₁ * Γ₂)⁻¹ = Γ₁ * (Γ₂ * c * Γ₂⁻¹) * Γ₁⁻¹ := by group
      _ = c := by rw [h2, h1]
  have h3' : degSeries Tag.D4 K Jout (2 + 1) = ⊥ := degSeries_J013_three (by norm_num)
  have hκH2 : ∀ w ∈ degSeries Tag.D4 K Jout 1, x * w * x⁻¹ * w⁻¹ ∈ degSeries Tag.D4 K Jout 2 := by
    intro w hw
    have := commutator_degSeries_le (K := K) (J := Jout) (le_refl (1 : ℤ)) (le_refl (1 : ℤ))
      (Subgroup.commutator_mem_commutator hxH hw)
    simpa [commutatorElement_def] using this
  have hcent : ∀ c ∈ degSeries Tag.D4 K Jout 2, ∀ w ∈ degSeries Tag.D4 K Jout 1, w * c = c * w := by
    intro c hc w hw
    have := commutator_degSeries_le (K := K) (J := Jout) (by norm_num : (1 : ℤ) ≤ 2)
      (le_refl (1 : ℤ)) (Subgroup.commutator_mem_commutator hc hw)
    rw [h3', Subgroup.mem_bot] at this
    have h1 : c * w * c⁻¹ * w⁻¹ = 1 := this
    have h2 : c * w = w * c := by
      calc c * w = (c * w * c⁻¹ * w⁻¹) * (w * c) := by group
        _ = w * c := by rw [h1, one_mul]
    exact h2.symm
  have hκconj : ∀ g : ModGL Tag.D4 K, g * x * g⁻¹ = x →
      (∀ c ∈ degSeries Tag.D4 K Jout 2, g * c * g⁻¹ = c) → ∀ w ∈ degSeries Tag.D4 K Jout 1,
      x * (g * w * g⁻¹) * x⁻¹ * (g * w * g⁻¹)⁻¹ = x * w * x⁻¹ * w⁻¹ := by
    intro g hg hgc w hw
    have e : g * (x * w * x⁻¹ * w⁻¹) * g⁻¹ =
        (g * x * g⁻¹) * (g * w * g⁻¹) * (g * x * g⁻¹)⁻¹ * (g * w * g⁻¹)⁻¹ := by group
    rw [hg] at e
    rw [← e]
    exact hgc _ (hκH2 w hw)
  have hy₁H : Γ₁ * y * Γ₁⁻¹ ∈ degSeries Tag.D4 K Jout 1 := G.n₁.conj_mem hyH
  have hy₂H : Γ₂ * y * Γ₂⁻¹ ∈ degSeries Tag.D4 K Jout 1 := G.n₂.conj_mem hyH
  have hy₃H : (Γ₁ * Γ₂) * y * (Γ₁ * Γ₂)⁻¹ ∈ degSeries Tag.D4 K Jout 1 :=
    (G.n₁.mul G.n₂).conj_mem hyH
  have hc₀H2 : x * y * x⁻¹ * y⁻¹ ∈ degSeries Tag.D4 K Jout 2 := hκH2 y hyH
  have hκ₁ := hκconj Γ₁ (hA₁ x hxA) (fun c hc => (J013_trivial_H2 hK G hc).1) y hyH
  have hκ₂ := hκconj Γ₂ (hA₂ x hxA) (fun c hc => (J013_trivial_H2 hK G hc).2) y hyH
  have hκ₃ := hκconj (Γ₁ * Γ₂) hxf₃ hcf₃ y hyH
  have hc03 : (x * y * x⁻¹ * y⁻¹) ^ 3 = 1 := by
    have := hL2.cube_mem _ hc₀H2
    rw [h3', Subgroup.mem_bot] at this
    exact this
  have hYH : y * ((Γ₁ * y * Γ₁⁻¹) * ((Γ₂ * y * Γ₂⁻¹) * ((Γ₁ * Γ₂) * y * (Γ₁ * Γ₂)⁻¹))) ∈
      degSeries Tag.D4 K Jout 1 := mul_mem hyH (mul_mem hy₁H (mul_mem hy₂H hy₃H))
  have hκY : x * (y * ((Γ₁ * y * Γ₁⁻¹) * ((Γ₂ * y * Γ₂⁻¹) * ((Γ₁ * Γ₂) * y * (Γ₁ * Γ₂)⁻¹)))) * x⁻¹ *
      (y * ((Γ₁ * y * Γ₁⁻¹) * ((Γ₂ * y * Γ₂⁻¹) * ((Γ₁ * Γ₂) * y * (Γ₁ * Γ₂)⁻¹))))⁻¹ =
        x * y * x⁻¹ * y⁻¹ := by
    have hR₂ : x * ((Γ₂ * y * Γ₂⁻¹) * ((Γ₁ * Γ₂) * y * (Γ₁ * Γ₂)⁻¹)) * x⁻¹ *
        ((Γ₂ * y * Γ₂⁻¹) * ((Γ₁ * Γ₂) * y * (Γ₁ * Γ₂)⁻¹))⁻¹ =
          (x * y * x⁻¹ * y⁻¹) * (x * y * x⁻¹ * y⁻¹) := by
      rw [kappa_mul x _ _ (hcent _ (hκH2 _ hy₃H) _ hy₂H), hκ₂, hκ₃]
    have hR₁ : x * ((Γ₁ * y * Γ₁⁻¹) * ((Γ₂ * y * Γ₂⁻¹) * ((Γ₁ * Γ₂) * y * (Γ₁ * Γ₂)⁻¹))) * x⁻¹ *
        ((Γ₁ * y * Γ₁⁻¹) * ((Γ₂ * y * Γ₂⁻¹) * ((Γ₁ * Γ₂) * y * (Γ₁ * Γ₂)⁻¹)))⁻¹ =
          (x * y * x⁻¹ * y⁻¹) * ((x * y * x⁻¹ * y⁻¹) * (x * y * x⁻¹ * y⁻¹)) := by
      rw [kappa_mul x _ _ (hcent _ (hκH2 _ (mul_mem hy₂H hy₃H)) _ hy₁H), hκ₁, hR₂]
    rw [kappa_mul x _ _ (hcent _ (hκH2 _ (mul_mem hy₁H (mul_mem hy₂H hy₃H))) _ hyH), hR₁]
    have key : ∀ c : ModGL Tag.D4 K, c ^ 3 = 1 → c * (c * (c * c)) = c := fun c h => by
      calc c * (c * (c * c)) = c ^ 3 * c := by simp [pow_succ, mul_assoc]
        _ = c := by rw [h, one_mul]
    exact key _ hc03
  have hYA : y * ((Γ₁ * y * Γ₁⁻¹) * ((Γ₂ * y * Γ₂⁻¹) * ((Γ₁ * Γ₂) * y * (Γ₁ * Γ₂)⁻¹))) ∈ A := by
    set z : Lyr hL1 := Lyr.mk hL1 ⟨y, hyH⟩ with hz
    have hz₁ : Lyr.mk hL1 ⟨Γ₁ * y * Γ₁⁻¹, hy₁H⟩ = lconj G.n₁ hd1 z :=
      (lconj_mk G.n₁ hd1 ⟨y, hyH⟩).symm
    have hz₂ : Lyr.mk hL1 ⟨Γ₂ * y * Γ₂⁻¹, hy₂H⟩ = lconj G.n₂ hd1 z :=
      (lconj_mk G.n₂ hd1 ⟨y, hyH⟩).symm
    have hz₃ : Lyr.mk hL1 ⟨(Γ₁ * Γ₂) * y * (Γ₁ * Γ₂)⁻¹, hy₃H⟩ =
        lconj G.n₁ hd1 (lconj G.n₂ hd1 z) := by
      rw [← lconj_mul G.n₁ G.n₂ hd1 z]
      exact (lconj_mk (G.n₁.mul G.n₂) hd1 ⟨y, hyH⟩).symm
    have hmk : Lyr.mk hL1 ⟨y * ((Γ₁ * y * Γ₁⁻¹) * ((Γ₂ * y * Γ₂⁻¹) *
        ((Γ₁ * Γ₂) * y * (Γ₁ * Γ₂)⁻¹))), hYH⟩ =
        z + (lconj G.n₁ hd1 z + (lconj G.n₂ hd1 z + lconj G.n₁ hd1 (lconj G.n₂ hd1 z))) := by
      have e : (⟨y * ((Γ₁ * y * Γ₁⁻¹) * ((Γ₂ * y * Γ₂⁻¹) * ((Γ₁ * Γ₂) * y * (Γ₁ * Γ₂)⁻¹))), hYH⟩ :
          degSeries Tag.D4 K Jout 1) =
          ⟨y, hyH⟩ * (⟨Γ₁ * y * Γ₁⁻¹, hy₁H⟩ * (⟨Γ₂ * y * Γ₂⁻¹, hy₂H⟩ *
            ⟨(Γ₁ * Γ₂) * y * (Γ₁ * Γ₂)⁻¹, hy₃H⟩)) := rfl
      rw [e, Lyr.mk_add, Lyr.mk_add, Lyr.mk_add, hz₁, hz₂, hz₃]
    have hT₁ : lconj G.n₁ hd1 (Lyr.mk hL1 ⟨y * ((Γ₁ * y * Γ₁⁻¹) * ((Γ₂ * y * Γ₂⁻¹) *
        ((Γ₁ * Γ₂) * y * (Γ₁ * Γ₂)⁻¹))), hYH⟩) = Lyr.mk hL1 ⟨y * ((Γ₁ * y * Γ₁⁻¹) *
        ((Γ₂ * y * Γ₂⁻¹) * ((Γ₁ * Γ₂) * y * (Γ₁ * Γ₂)⁻¹))), hYH⟩ := by
      rw [hmk, map_add, map_add, map_add, G.layer_inv₁ hd1 z,
        G.layer_inv₁ hd1 (lconj G.n₂ hd1 z)]
      abel
    have hT₂ : lconj G.n₂ hd1 (Lyr.mk hL1 ⟨y * ((Γ₁ * y * Γ₁⁻¹) * ((Γ₂ * y * Γ₂⁻¹) *
        ((Γ₁ * Γ₂) * y * (Γ₁ * Γ₂)⁻¹))), hYH⟩) = Lyr.mk hL1 ⟨y * ((Γ₁ * y * Γ₁⁻¹) *
        ((Γ₂ * y * Γ₂⁻¹) * ((Γ₁ * Γ₂) * y * (Γ₁ * Γ₂)⁻¹))), hYH⟩ := by
      have c1 : lconj G.n₂ hd1 (lconj G.n₁ hd1 z) = lconj G.n₁ hd1 (lconj G.n₂ hd1 z) :=
        (G.layer_comm hd1 z).symm
      have c2 : lconj G.n₂ hd1 (lconj G.n₁ hd1 (lconj G.n₂ hd1 z)) = lconj G.n₁ hd1 z := by
        rw [← G.layer_comm hd1 (lconj G.n₂ hd1 z), G.layer_inv₂ hd1 z]
      rw [hmk, map_add, map_add, map_add, c1, G.layer_inv₂ hd1 z, c2]
      abel
    have hmS : Lyr.mk hL1 ⟨y * ((Γ₁ * y * Γ₁⁻¹) * ((Γ₂ * y * Γ₂⁻¹) *
        ((Γ₁ * Γ₂) * y * (Γ₁ * Γ₂)⁻¹))), hYH⟩ ∈ S₁ :=
      ⟨mem_fixSp.2 hT₁, mem_fixSp.2 hT₂⟩
    rw [← hIeq] at hmS
    obtain ⟨a, haA, haH, hae⟩ := hmS
    have h5 : a⁻¹ * (y * ((Γ₁ * y * Γ₁⁻¹) * ((Γ₂ * y * Γ₂⁻¹) *
        ((Γ₁ * Γ₂) * y * (Γ₁ * Γ₂)⁻¹)))) ∈ degSeries Tag.D4 K Jout 2 :=
      (Lyr.mk_eq_mk hL1).1 hae
    have h6 := hH2A h5
    have e : y * ((Γ₁ * y * Γ₁⁻¹) * ((Γ₂ * y * Γ₂⁻¹) * ((Γ₁ * Γ₂) * y * (Γ₁ * Γ₂)⁻¹))) =
        a * (a⁻¹ * (y * ((Γ₁ * y * Γ₁⁻¹) * ((Γ₂ * y * Γ₂⁻¹) *
          ((Γ₁ * Γ₂) * y * (Γ₁ * Γ₂)⁻¹))))) := by group
    rw [e]
    exact mul_mem haA h6
  have hxY := hAc x hxA _ hYA
  have h1' : x * y * x⁻¹ * y⁻¹ = 1 := by
    rw [← hκY]
    calc _ = (x * _) * x⁻¹ * _⁻¹ := rfl
      _ = 1 := by rw [hxY]; group
  exact hxy (by
    calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
      _ = y * x := by rw [h1', one_mul])

end N1

end CFSG.LocalAnalysis.GLTheoremA
