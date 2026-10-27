module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Layer
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Triple

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isQuasisimple_quotient_of_isHSet {B K : Subgroup G} (hK : IsHSet B K) :
    CFSG.Open.IsQuasisimple (↥K ⧸ GLAPPrimeCore 3 ↥K) := by
  obtain ⟨⟨x, hx1, hx2, hxK⟩, -, -⟩ := hK
  have h1 := glaPComponent_of_le Nat.prime_three hxK le_rfl hxK.1
  have h2 := h1.2.2.1.2.2
  change CFSG.Open.IsQuasisimple ↥(barX 3 K K) at h2
  rw [barX_self] at h2
  exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv Subgroup.topEquiv h2

theorem layerSetup_of_lemma75 {B N K : Subgroup G} (h68 : Prop68Out B) (h75 : Lemma75Stmt B)
    (hK : IsHSet B K) (hN : N ≠ ⊤) (hBN : B ≤ N) (hcov : Covers3 N K) : LayerSetup B N K :=
  ⟨hBN, (h68 K hK).normalizes, hcov, isQuasisimple_quotient_of_isHSet hK,
    h75 K hK N hN hBN hcov⟩

omit [Finite G] in
theorem commMod_of_barX_le {N J J' : Subgroup G} (hJN : J ≤ N) (hJ'N : J' ≤ N)
    (hle : barX 3 N J ≤ barX 3 N J') {b : G} (hb : b ∈ N)
    (h' : ∀ j ∈ J', b * j * b⁻¹ * j⁻¹ ∈ GLAPPrimeCoreOf 3 N) :
    ∀ j ∈ J, b * j * b⁻¹ * j⁻¹ ∈ GLAPPrimeCoreOf 3 N := by
  intro j hj
  obtain ⟨j', hj', hn⟩ := exists_of_barX_le hle hj (hJN hj)
  have hjn : j = j' * (j'⁻¹ * j) := by group
  set n := j'⁻¹ * j with hnn
  have e : b * j * b⁻¹ * j⁻¹ =
      (b * j' * b⁻¹ * j'⁻¹) * (j' * ((b * n * b⁻¹) * n⁻¹) * j'⁻¹) := by
    rw [hjn]; group
  rw [e]
  refine mul_mem (h' j' hj') ?_
  have hbn : b * n * b⁻¹ ∈ GLAPPrimeCoreOf 3 N :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf 3 N hb) n).1 hn
  have h2 : (b * n * b⁻¹) * n⁻¹ ∈ GLAPPrimeCoreOf 3 N := mul_mem hbn (inv_mem hn)
  exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf 3 N (hJ'N hj')) _).1 h2

theorem commMod_of_ne {N J₁ J₂ : Subgroup G} (hJ₁N : J₁ ≤ N) (hJ₂N : J₂ ≤ N)
    (h₁ : IsComponentOf (barX 3 N J₁) ⊤) (h₂ : IsComponentOf (barX 3 N J₂) ⊤)
    (hne : barX 3 N J₁ ≠ barX 3 N J₂) :
    ∀ j₁ ∈ J₁, ∀ j₂ ∈ J₂, j₁ * j₂ * j₁⁻¹ * j₂⁻¹ ∈ GLAPPrimeCoreOf 3 N := by
  intro j₁ hj₁ j₂ hj₂
  have h := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ h₁ h₂ hne
  have hm := Subgroup.commutator_mem_commutator
    (show QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) ⟨j₁, hJ₁N hj₁⟩ ∈ barX 3 N J₁ from
      ⟨⟨j₁, hJ₁N hj₁⟩, (Subgroup.mem_subgroupOf).2 hj₁, rfl⟩)
    (show QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) ⟨j₂, hJ₂N hj₂⟩ ∈ barX 3 N J₂ from
      ⟨⟨j₂, hJ₂N hj₂⟩, (Subgroup.mem_subgroupOf).2 hj₂, rfl⟩)
  rw [h, Subgroup.mem_bot] at hm
  have h2 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥N)
      (⟨j₁, hJ₁N hj₁⟩ * ⟨j₂, hJ₂N hj₂⟩ * ⟨j₁, hJ₁N hj₁⟩⁻¹ * ⟨j₂, hJ₂N hj₂⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    exact hm
  refine ⟨_, (QuotientGroup.eq_one_iff _).1 h2, ?_⟩
  simp

variable {B : Subgroup G}

theorem lemma711 (hS : GLStanding G 4 3) (hB : IsBOneMax 3 B) (h68 : Prop68Out B)
    (h75 : Lemma75Stmt B) (h710 : Lemma710Stmt B) {K₁ K₂ : Subgroup G} (hK₁ : IsHSet B K₁)
    (hK₂ : IsHSet B K₂) :
    centralizerQuot B K₂ = centralizerQuot B K₁ ∨ centralizerQuot B K₂ = B ⊓ K₁ := by
  obtain ⟨N, hN, hBN, hc₁, hc₂⟩ := exists_common_cover hS hB h710 hK₁ hK₂
  have L₁ := layerSetup_of_lemma75 h68 h75 hK₁ hN hBN hc₁
  have L₂ := layerSetup_of_lemma75 h68 h75 hK₂ hN hBN hc₂
  have hf₁ := h68 K₁ hK₁
  have hf₂ := h68 K₂ hK₂
  set J₁ := GLAPLayer 3 (K₁ ⊓ N) with hJ₁
  set J₂ := GLAPLayer 3 (K₂ ⊓ N) with hJ₂
  have hJ₁N : J₁ ≤ N := (glaPLayer_le 3 _).trans inf_le_right
  have hJ₂N : J₂ ≤ N := (glaPLayer_le 3 _).trans inf_le_right
  have hmem₁ : ∀ b, b ∈ centralizerQuot B K₁ ↔
      b ∈ B ∧ ∀ j ∈ J₁, b * j * b⁻¹ * j⁻¹ ∈ GLAPPrimeCoreOf 3 N := fun b =>
    ⟨L₁.comm_of_mem_centralizerQuot, fun h => L₁.mem_centralizerQuot_of_comm h.1 h.2⟩
  have hmem₂ : ∀ b, b ∈ centralizerQuot B K₂ ↔
      b ∈ B ∧ ∀ j ∈ J₂, b * j * b⁻¹ * j⁻¹ ∈ GLAPPrimeCoreOf 3 N := fun b =>
    ⟨L₂.comm_of_mem_centralizerQuot, fun h => L₂.mem_centralizerQuot_of_comm h.1 h.2⟩
  by_cases hJ : barX 3 N J₁ = barX 3 N J₂
  · left
    ext b
    rw [hmem₁, hmem₂]
    constructor
    · rintro ⟨hb, h⟩
      exact ⟨hb, commMod_of_barX_le hJ₁N hJ₂N hJ.le (hBN hb) h⟩
    · rintro ⟨hb, h⟩
      exact ⟨hb, commMod_of_barX_le hJ₂N hJ₁N hJ.ge (hBN hb) h⟩
  · right
    have hcomm := commMod_of_ne hJ₁N hJ₂N L₁.comp L₂.comp hJ
    have hFA : B ⊓ K₁ ≤ centralizerQuot B K₂ := by
      intro f hf
      rw [hmem₂]
      refine ⟨hf.1, fun j hj => ?_⟩
      have hfJ : f ∈ J₁ := L₁.inf_le_layer hf₁.fK.2.1 hf
      exact hcomm f hfJ j hj
    refine (Subgroup.eq_of_le_of_card_ge hFA ?_).symm
    rw [hf₂.aK.2.2, hf₁.fK.2.2]


theorem exists_swap {N J₁ J₂ : Subgroup G} (hJ₁N : J₁ ≤ N) (hJ₂N : J₂ ≤ N)
    (h₁ : IsComponentOf (barX 3 N J₁) ⊤) (h₂ : IsComponentOf (barX 3 N J₂) ⊤) :
    ∀ j₂ ∈ J₂, ∀ j₁ ∈ J₁, ∃ j₁' ∈ J₁, ∃ j₂' ∈ J₂, ∃ n ∈ GLAPPrimeCoreOf 3 N,
      j₂ * j₁ = j₁' * j₂' * n := by
  intro j₂ hj₂ j₁ hj₁
  by_cases hJ : barX 3 N J₁ = barX 3 N J₂
  · obtain ⟨j, hj, hn⟩ := exists_of_barX_le hJ.ge hj₂ (hJ₂N hj₂)
    refine ⟨j * j₁, J₁.mul_mem hj hj₁, 1, J₂.one_mem, j₁⁻¹ * (j⁻¹ * j₂) * j₁, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.1
        (le_normalizer_glaPPrimeCoreOf 3 N (hJ₁N (J₁.inv_mem hj₁))) _).1 hn
      simpa [mul_assoc] using this
    · group
  · have hcomm := commMod_of_ne hJ₁N hJ₂N h₁ h₂ hJ
    have h := hcomm j₁⁻¹ (J₁.inv_mem hj₁) j₂ hj₂
    refine ⟨j₁, hj₁, j₂, hj₂, j₂⁻¹ * (j₁⁻¹ * j₂ * (j₁⁻¹)⁻¹ * j₂⁻¹) * j₂, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.1
        (le_normalizer_glaPPrimeCoreOf 3 N (hJ₂N (J₂.inv_mem hj₂))) _).1 h
      simpa [mul_assoc] using this
    · group

theorem LayerSetup.exists_mul {B N K : Subgroup G} (h : LayerSetup B N K) :
    ∀ k ∈ K, ∃ j ∈ GLAPLayer 3 (K ⊓ N), ∃ o ∈ GLAPPrimeCoreOf 3 K, k = j * o := by
  intro k hk
  have hk' : k ∈ ((GLAPLayer 3 (K ⊓ N) ⊔ GLAPPrimeCoreOf 3 K : Subgroup G) : Set G) :=
    h.le_layer_sup hk
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (layer_le_normalizerO K N)] at hk'
  obtain ⟨j, hj, o, ho, e⟩ := hk'
  exact ⟨j, hj, o, ho, e.symm⟩

theorem lemma712 (hS : GLStanding G 4 3) (hB : IsBOneMax 3 B) {M₀ : Subgroup G}
    (h63 : Prop63Out B M₀) (h68 : Prop68Out B) (hU : UniqComp B) (h75 : Lemma75Stmt B)
    (h710 : Lemma710Stmt B) {K₁ K₂ : Subgroup G} (hK₁ : IsHSet B K₁) (hK₂ : IsHSet B K₂) :
    Permutable K₂ (K₁ ⊔ gammaOneThree B) ∧
      ((K₂ : Set G) * ((K₁ : Set G) * (gammaOneThree B : Set G)) =
        (K₁ : Set G) * ((K₂ : Set G) * (gammaOneThree B : Set G))) ∧
      K₂ ⊔ (K₁ ⊔ gammaOneThree B) ≠ ⊤ := by
  have := hS.simple
  obtain ⟨N, hN, hBN, hc₁, hc₂⟩ := exists_common_cover hS hB h710 hK₁ hK₂
  have L₁ := layerSetup_of_lemma75 h68 h75 hK₁ hN hBN hc₁
  have L₂ := layerSetup_of_lemma75 h68 h75 hK₂ hN hBN hc₂
  have hf₁ := h68 K₁ hK₁
  have hf₂ := h68 K₂ hK₂
  have h74₁ := permutable_gammaOneThree hS hB h63 h68 hU hK₁
  have h74₂ := permutable_gammaOneThree hS hB h63 h68 hU hK₂
  set M₂ := gammaOneThree B with hM₂
  set J₁ := GLAPLayer 3 (K₁ ⊓ N) with hJ₁
  set J₂ := GLAPLayer 3 (K₂ ⊓ N) with hJ₂
  have hJ₁N : J₁ ≤ N := (glaPLayer_le 3 _).trans inf_le_right
  have hJ₂N : J₂ ≤ N := (glaPLayer_le 3 _).trans inf_le_right
  have hJ₁K : J₁ ≤ K₁ := (glaPLayer_le 3 _).trans inf_le_left
  have hJ₂K : J₂ ≤ K₂ := (glaPLayer_le 3 _).trans inf_le_left
  have hO₁ : GLAPPrimeCoreOf 3 K₁ ≤ M₂ := glaPPrimeCoreOf_le_gammaOneThree hS hB hf₁.normalizes
  have hO₂ : GLAPPrimeCoreOf 3 K₂ ≤ M₂ := glaPPrimeCoreOf_le_gammaOneThree hS hB hf₂.normalizes
  have hON : GLAPPrimeCoreOf 3 N ≤ M₂ :=
    le_gammaOneThree_of_normalized hS hB (hBN.trans (le_normalizer_glaPPrimeCoreOf 3 N))
      (not_dvd_card_glaPPrimeCoreOf Nat.prime_three N)
  have hperm : Permutable K₂ (K₁ ⊔ M₂) := by
    refine permutable_of_mul_subset ?_
    rintro _ ⟨k₂, hk₂, x, hx, rfl⟩
    obtain ⟨j₂, hj₂, o₂, ho₂, rfl⟩ := L₂.exists_mul k₂ hk₂
    have hy : o₂ * x ∈ ((K₁ ⊔ M₂ : Subgroup G) : Set G) :=
      (K₁ ⊔ M₂).mul_mem (Subgroup.mem_sup_right (hO₂ ho₂)) hx
    rw [h74₁.1.coe_sup] at hy
    obtain ⟨k₁, hk₁, m, hm, hkm⟩ := hy
    have hkm : k₁ * m = o₂ * x := hkm
    obtain ⟨j₁, hj₁, o₁, ho₁, rfl⟩ := L₁.exists_mul k₁ hk₁
    obtain ⟨j₁', hj₁', j₂', hj₂', n, hn, hsw⟩ := exists_swap hJ₁N hJ₂N L₁.comp L₂.comp j₂ hj₂ j₁ hj₁
    have e1 : j₂ * o₂ * x = j₂ * (j₁ * o₁ * m) := by
      rw [mul_assoc, ← hkm]
    have hm'' : n * (o₁ * m) ∈ M₂ :=
      M₂.mul_mem (hON hn) (M₂.mul_mem (hO₁ ho₁) hm)
    have hjm : j₂' * (n * (o₁ * m)) ∈ (K₂ : Set G) * (M₂ : Set G) :=
      Set.mul_mem_mul (hJ₂K hj₂') hm''
    rw [h74₂.1] at hjm
    obtain ⟨m3, hm3, k₂', hk₂', hmk⟩ := hjm
    have hmk : m3 * k₂' = j₂' * (n * (o₁ * m)) := hmk
    refine ⟨j₁' * m3, ?_, k₂', hk₂', ?_⟩
    · exact (K₁ ⊔ M₂).mul_mem (Subgroup.mem_sup_left (hJ₁K hj₁')) (Subgroup.mem_sup_right hm3)
    · calc j₁' * m3 * k₂' = j₁' * (m3 * k₂') := by rw [mul_assoc]
        _ = j₁' * (j₂' * (n * (o₁ * m))) := by rw [hmk]
        _ = (j₁' * j₂' * n) * (o₁ * m) := by simp only [mul_assoc]
        _ = (j₂ * j₁) * (o₁ * m) := by rw [hsw]
        _ = j₂ * (j₁ * o₁ * m) := by simp only [mul_assoc]
        _ = j₂ * o₂ * x := e1.symm
  refine ⟨hperm, ?_, ?_⟩
  · have e1 : (K₂ : Set G) * ((K₁ : Set G) * (M₂ : Set G)) = ((K₁ ⊔ M₂ : Subgroup G) : Set G) * K₂ := by
      rw [← h74₁.1.coe_sup]; exact hperm
    have e2 : (K₁ : Set G) * ((K₂ : Set G) * (M₂ : Set G)) =
        ((K₁ ⊔ M₂ : Subgroup G) : Set G) * K₂ := by
      rw [h74₂.1, h74₁.1.coe_sup, mul_assoc]
    rw [e1, e2]
  · obtain ⟨⟨x, hxB, hx1, hxK⟩, -, -⟩ := id hK₂
    exact sup_ne_top_of_permutable hperm h74₁.2
      (Subgroup.mem_sup_right (le_gammaOneThree_self hS hB hxB)) hx1 hxK.1


theorem lemma713 (hS : GLStanding G 4 3) (hB : IsBOneMax 3 B) (h68 : Prop68Out B)
    (h75 : Lemma75Stmt B) (h710 : Lemma710Stmt B) {K₁ K₂ : Subgroup G} (hK₁ : IsHSet B K₁)
    (hK₂ : IsHSet B K₂) (hne : centralizerQuot B K₁ ≠ centralizerQuot B K₂) {K : Subgroup G}
    (hK : IsHSet B K) :
    centralizerQuot B K = centralizerQuot B K₁ ∨ centralizerQuot B K = centralizerQuot B K₂ := by
  have hA₂ : centralizerQuot B K₂ = B ⊓ K₁ :=
    (lemma711 hS hB h68 h75 h710 hK₁ hK₂).resolve_left fun h => hne h.symm
  rcases lemma711 hS hB h68 h75 h710 hK₁ hK with h | h
  · exact Or.inl h
  · exact Or.inr (h.trans hA₂.symm)

theorem le_sup_gammaOneThree_of_mem_centralizerQuot (hS : GLStanding G 4 3) (hB : IsBOneMax 3 B)
    (h68 : Prop68Out B) (hU : UniqComp B) {K K' : Subgroup G} (hK : IsHSet B K)
    (hK' : IsHSet B K') {x : G} (hxB : x ∈ B) (hx1 : x ≠ 1)
    (hxK' : GLAPComponent 3 (Subgroup.centralizer ({x} : Set G)) K')
    (hxA : x ∈ centralizerQuot B K) : K' ≤ K ⊔ gammaOneThree B := by
  have hf := h68 K hK
  have hf₁ := h68 K' hK'
  have hI := hf.ia x hxA hx1
  have hIK : bClosureIa K x = K' :=
    hU x hxB hx1 _ K' hI.component hxK'
      ((le_centralizer_of_mem hB.1.1 hxB).trans hI.normal) hf₁.normalizes
      hI.lThreeFour hf₁.lThreeFour hf₁.fK
  have h1 : K' ≤ kZeroOf B K ⊔ GLAPPrimeCoreOf 3 K' := by
    have := hI.le_kZero_sup
    rwa [hIK] at this
  exact h1.trans (sup_le_sup (kZeroOf_le B K)
    (glaPPrimeCoreOf_le_gammaOneThree hS hB hf₁.normalizes))

theorem lemma714 (hS : GLStanding G 4 3) (hB : IsBOneMax 3 B) (h68 : Prop68Out B)
    (hU : UniqComp B) (h75 : Lemma75Stmt B) (h710 : Lemma710Stmt B) {K₁ K₂ : Subgroup G}
    (hK₁ : IsHSet B K₁) (hK₂ : IsHSet B K₂)
    (hne : centralizerQuot B K₁ ≠ centralizerQuot B K₂) {K : Subgroup G} (hK : IsHSet B K) :
    K ≤ K₁ ⊔ gammaOneThree B ∨ K ≤ K₂ ⊔ gammaOneThree B := by
  obtain ⟨⟨x, hxB, hx1, hxK⟩, -, -⟩ := id hK
  have hxA : x ∈ centralizerQuot B K := mem_centralizerQuot_of_le_centralizer hxB hxK.1
  rcases lemma713 hS hB h68 h75 h710 hK₁ hK₂ hne hK with h | h
  · exact Or.inl (le_sup_gammaOneThree_of_mem_centralizerQuot hS hB h68 hU hK₁ hK hxB hx1 hxK
      (h ▸ hxA))
  · exact Or.inr (le_sup_gammaOneThree_of_mem_centralizerQuot hS hB h68 hU hK₂ hK hxB hx1 hxK
      (h ▸ hxA))


def mulClosedSubgroup (P : G → Prop) (h1 : P 1) (hmul : ∀ a b, P a → P b → P (a * b)) :
    Subgroup G where
  carrier := {x | P x}
  mul_mem' := fun {a b} ha hb => hmul a b ha hb
  one_mem' := h1
  inv_mem' := by
    intro x hx
    have hpow : ∀ n : ℕ, P (x ^ n) := by
      intro n
      induction n with
      | zero => simpa using h1
      | succ n ih => rw [pow_succ]; exact hmul _ _ ih hx
    have e : x ⁻¹ = x ^ (orderOf x - 1) := by
      refine eq_inv_of_mul_eq_one_right ?_ |>.symm
      rw [← pow_succ', Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]
    change P x⁻¹
    rw [e]
    exact hpow _

theorem mem_mulClosedSubgroup {P : G → Prop} {h1 : P 1} {hmul : ∀ a b, P a → P b → P (a * b)}
    {x : G} : x ∈ mulClosedSubgroup P h1 hmul ↔ P x := Iff.rfl

omit [Finite G] in
theorem exists_mul_of_mem_sup_gammaOneThree {K : Subgroup G}
    (hp : Permutable K (gammaOneThree B)) {z : G} (hz : z ∈ K ⊔ gammaOneThree B) :
    ∃ m ∈ gammaOneThree B, ∃ k ∈ K, z = m * k := by
  have hz' : z ∈ ((gammaOneThree B ⊔ K : Subgroup G) : Set G) := by rw [sup_comm]; exact hz
  rw [hp.symm.coe_sup] at hz'
  obtain ⟨m, hm, k, hk, e⟩ := hz'
  exact ⟨m, hm, k, hk, e.symm⟩

theorem exists_mul_normalizer_of_lemma714 (hS : GLStanding G 4 3) (hB : IsBOneMax 3 B)
    {M₀ : Subgroup G} (h63 : Prop63Out B M₀) (h68 : Prop68Out B) (hU : UniqComp B)
    {K₁ K₂ : Subgroup G} (hK₁ : IsHSet B K₁) (hK₂ : IsHSet B K₂)
    (hall : ∀ K' : Subgroup G, IsHSet B K' →
      K' ≤ K₁ ⊔ gammaOneThree B ∨ K' ≤ K₂ ⊔ gammaOneThree B)
    {K : Subgroup G} (hK : IsHSet B K) {Q : Subgroup G} (hQB : Q ≤ B)
    (hQ3 : 3 ≤ CFSG.Open.pRank 3 Q) {y : G} (hy : y ∈ Subgroup.normalizer (Q : Set G)) :
    ∀ k ∈ K, ∃ m ∈ GLBCore 3 3 B, ∃ k', (k' ∈ K₁ ∨ k' ∈ K₂) ∧ k * y = m * k' := by
  have := hS.simple
  have hf := h68 K hK
  have hB81 := card_eq_81 hS hB
  have h74₁ := permutable_gammaOneThree hS hB h63 h68 hU hK₁
  have h74₂ := permutable_gammaOneThree hS hB h63 h68 hU hK₂
  have hKle := le_kZeroOf_sup_of_isHSet hB.1.1 h68 hU hK
  have hM2M1 := gammaOneThree_le_glbCore B
  have hnM : ¬ K ≤ GLBCore 3 3 B := hK.2.2
  have hOK : GLAPPrimeCoreOf 3 K ≤ GLBCore 3 3 B :=
    (glaPPrimeCoreOf_le_gammaOneThree hS hB hf.normalizes).trans hM2M1
  intro k hk
  have hyM1 : y ∈ GLBCore 3 3 B :=
    (le_sSup ⟨Q, hQB, hQ3, rfl⟩ : Subgroup.normalizer (Q : Set G) ≤ GLBCore 3 3 B) hy
  obtain ⟨E, hEQ, hEel, j, hj, hEc⟩ := exists_elemAbelian_ge_of_le_pRank (by norm_num) hQ3
  obtain ⟨a, haEA, ha1⟩ := exists_ne_one_mem_inf hB81 (hEQ.trans hQB) hf.aK.1
    (by
      rw [hEc]
      calc 27 = 3 ^ 3 := by norm_num
        _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj)
    (by rw [hf.aK.2.2]; norm_num)
  have haA : a ∈ centralizerQuot B K := (Subgroup.mem_inf.1 haEA).2
  have haQ : a ∈ Q := hEQ (Subgroup.mem_inf.1 haEA).1
  have hIa := hf.ia a haA ha1
  have hIaM : ¬ bClosureIa K a ≤ GLBCore 3 3 B := fun hle =>
    hnM (hKle.trans (sup_le ((hIa.kZero_le).trans hle) hOK))
  have hIay : IsHSet B (GLBConj y (bClosureIa K a)) := by
    have ha'Q : y⁻¹ * a * y ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hy) a).1 haQ
      simpa using this
    have ha'1 : y⁻¹ * a * y ≠ 1 := by
      intro h
      apply ha1
      calc a = y * (y⁻¹ * a * y) * y⁻¹ := by group
        _ = 1 := by rw [h]; group
    have hcomp := glaPComponent_gLBConj hIa.component y
    rw [gLBConj_centralizer_singleton] at hcomp
    refine ⟨⟨_, hQB ha'Q, ha'1, hcomp⟩,
      Or.inl (IsLThreeFour.of_mulEquiv (conjQuotEquiv 3 y (bClosureIa K a)) hIa.lThreeFour), ?_⟩
    intro hle
    apply hIaM
    have h1 := gLBConj_mono y⁻¹ hle
    rw [gLBConj_inv_gLBConj, gLBConj_eq_of_mem_normalizer
      (Subgroup.inv_mem _ (Subgroup.le_normalizer hyM1))] at h1
    exact h1
  have hk1 : k ∈ ((GLAPPrimeCoreOf 3 K ⊔ (bClosureIa K a ⊓ K) : Subgroup G) : Set G) := by
    have : K ≤ GLAPPrimeCoreOf 3 K ⊔ (bClosureIa K a ⊓ K) :=
      hKle.trans (sup_le (le_sup_of_le_right (le_inf hIa.kZero_le (kZeroOf_le B K)))
        le_sup_left)
    exact this hk
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _
    (inf_le_right.trans (le_normalizer_glaPPrimeCoreOf 3 K))] at hk1
  obtain ⟨o, ho, i, hi, hoi⟩ := hk1
  have hoi : o * i = k := hoi
  subst hoi
  have hyi : y⁻¹ * i * y ∈ GLBConj y (bClosureIa K a) := by
    rw [mem_gLBConj]
    have h3 : y * (y⁻¹ * i * y) * y⁻¹ = i := by group
    rw [h3]
    exact (Subgroup.mem_inf.1 hi).1
  obtain ⟨m₂, hm₂, k'', e, hk''K⟩ : ∃ m₂ ∈ gammaOneThree B, ∃ k'',
      y⁻¹ * i * y = m₂ * k'' ∧ (k'' ∈ K₁ ∨ k'' ∈ K₂) := by
    rcases hall _ hIay with h | h
    · obtain ⟨m, hm, k', hk', e⟩ := exists_mul_of_mem_sup_gammaOneThree h74₁.1 (h hyi)
      exact ⟨m, hm, k', e, Or.inl hk'⟩
    · obtain ⟨m, hm, k', hk', e⟩ := exists_mul_of_mem_sup_gammaOneThree h74₂.1 (h hyi)
      exact ⟨m, hm, k', e, Or.inr hk'⟩
  refine ⟨o * y * m₂, mul_mem (mul_mem (hOK ho) hyM1) (hM2M1 hm₂), k'', hk''K, ?_⟩
  calc o * i * y = o * y * (y⁻¹ * i * y) := by group
    _ = o * y * (m₂ * k'') := by rw [e]
    _ = o * y * m₂ * k'' := by group

theorem even_card_glaPPrimeCoreOf_of_le (h75 : Lemma75Stmt B) (h76 : Lemma76Stmt B)
    {K N : Subgroup G} (hK : IsHSet B K) (hne : N ≠ ⊤) (hBN : B ≤ N)
    (hKN : K ⊔ gammaOneThree B ≤ N) : Even (Nat.card (GLAPPrimeCoreOf 3 N)) := by
  obtain ⟨⟨x, -, -, hxK⟩, -, -⟩ := id hK
  have hKN' : K ≤ N := le_sup_left.trans hKN
  have hcov : Covers3 N K := le_sup_of_le_left (le_inf hKN' le_rfl)
  have h5 := h75 K hK N hne hBN hcov
  have hKl : GLAPLayer 3 (K ⊓ N) = K := by
    rw [inf_eq_left.2 hKN']
    exact le_antisymm (glaPLayer_le 3 K) (le_glaPLayer_self hxK)
  rw [hKl] at h5
  obtain ⟨I, hI, hIbar⟩ := exists_glaPComponent_barX_eq (p := 3) N h5
  have h6 := h76 K hK N hne hKN I hI hIbar
  have hcomm : ⁅I, GLAPPrimeCoreOf 3 N⁆ ≤ GLAPPrimeCoreOf 3 N := by
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    have h1 := (Subgroup.mem_normalizer_iff.1
      (le_normalizer_glaPPrimeCoreOf 3 N (hI.1 ha)) b).1 hb
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hb)
  exact even_iff_two_dvd.2 ((even_iff_two_dvd.1 h6).trans (Subgroup.card_dvd_of_le hcomm))

omit [Finite G] in
theorem sup_ne_top_of_normalizes [IsSimpleGroup G] {K M Y : Subgroup G}
    (hperm : Permutable K M) (hM : M ≠ ⊤) (hY : Y ≠ ⊥) (hYM : Y ≤ M)
    (hKY : K ≤ Subgroup.normalizer (Y : Set G)) : K ⊔ M ≠ ⊤ := by
  intro htop
  refine hM (eq_top_of_mul_eq_top (A := M) (C := K) (Y := Y) hY hYM hKY ?_)
  intro g
  have hg : g ∈ ((M ⊔ K : Subgroup G) : Set G) := by
    rw [sup_comm, htop]; exact Subgroup.mem_top g
  rw [hperm.symm.coe_sup] at hg
  obtain ⟨a, ha, c, hc, e⟩ := hg
  exact ⟨a, ha, c, hc, e.symm⟩

theorem lemma715 (hS : GLStanding G 4 3) (hB : IsBOneMax 3 B) {M₀ : Subgroup G}
    (h63 : Prop63Out B M₀) (h68 : Prop68Out B) (hU : UniqComp B) (h75 : Lemma75Stmt B)
    (h76 : Lemma76Stmt B) (h710 : Lemma710Stmt B) {K₁ K₂ : Subgroup G} (hK₁ : IsHSet B K₁)
    (hK₂ : IsHSet B K₂) (hne : centralizerQuot B K₁ ≠ centralizerQuot B K₂) :
    K₂ ⊔ K₁ ⊔ GLBCore 3 3 B ≠ ⊤ := by
  have := hS.simple
  have hall : ∀ K' : Subgroup G, IsHSet B K' →
      K' ≤ K₁ ⊔ gammaOneThree B ∨ K' ≤ K₂ ⊔ gammaOneThree B := fun K' hK' =>
    lemma714 hS hB h68 hU h75 h710 hK₁ hK₂ hne hK'
  have h712 := lemma712 hS hB h63 h68 hU h75 h710 hK₁ hK₂
  have hM2M1 : gammaOneThree B ≤ GLBCore 3 3 B := gammaOneThree_le_glbCore B
  have hN₀ne : K₂ ⊔ K₁ ⊔ gammaOneThree B ≠ ⊤ := by
    have := h712.2.2
    rwa [← sup_assoc] at this
  have hBN₀ : B ≤ K₂ ⊔ K₁ ⊔ gammaOneThree B :=
    (le_gammaOneThree_self hS hB).trans le_sup_right
  have hK₁N : K₁ ≤ K₂ ⊔ K₁ ⊔ gammaOneThree B := le_sup_right.trans le_sup_left
  have hK₂N : K₂ ≤ K₂ ⊔ K₁ ⊔ gammaOneThree B := le_sup_left.trans le_sup_left
  have hM₂N : gammaOneThree B ≤ K₂ ⊔ K₁ ⊔ gammaOneThree B := le_sup_right
  have hgen : ∀ m ∈ GLBCore 3 3 B, ∀ k, (k ∈ K₁ ∨ k ∈ K₂) →
      ∃ m' ∈ GLBCore 3 3 B, ∃ k', (k' ∈ K₁ ∨ k' ∈ K₂) ∧ k * m = m' * k' := by
    let D := mulClosedSubgroup
      (fun m : G => ∀ k, (k ∈ K₁ ∨ k ∈ K₂) →
        ∃ m' ∈ GLBCore 3 3 B, ∃ k', (k' ∈ K₁ ∨ k' ∈ K₂) ∧ k * m = m' * k')
      (fun k hk => ⟨1, Subgroup.one_mem _, k, hk, by simp⟩)
      (fun a b ha hb k hk => by
        obtain ⟨m₁, hm₁, k₁, hk₁, e₁⟩ := ha k hk
        obtain ⟨m₂, hm₂, k₂, hk₂, e₂⟩ := hb k₁ hk₁
        refine ⟨m₁ * m₂, Subgroup.mul_mem _ hm₁ hm₂, k₂, hk₂, ?_⟩
        calc k * (a * b) = (k * a) * b := by rw [mul_assoc]
          _ = (m₁ * k₁) * b := by rw [e₁]
          _ = m₁ * (k₁ * b) := by rw [mul_assoc]
          _ = m₁ * (m₂ * k₂) := by rw [e₂]
          _ = m₁ * m₂ * k₂ := by rw [mul_assoc])
    have hle : GLBCore 3 3 B ≤ D := by
      refine sSup_le ?_
      rintro _ ⟨Q, hQB, hQ3, rfl⟩ y hy k hk
      rcases hk with hk | hk
      · exact exists_mul_normalizer_of_lemma714 hS hB h63 h68 hU hK₁ hK₂ hall hK₁ hQB hQ3 hy k hk
      · exact exists_mul_normalizer_of_lemma714 hS hB h63 h68 hU hK₁ hK₂ hall hK₂ hQB hQ3 hy k hk
    exact fun m hm => hle hm
  have hA : ∀ n ∈ K₂ ⊔ K₁ ⊔ gammaOneThree B, ∀ m ∈ GLBCore 3 3 B,
      ∃ m' ∈ GLBCore 3 3 B, ∃ n' ∈ K₂ ⊔ K₁ ⊔ gammaOneThree B, n * m = m' * n' := by
    let D := mulClosedSubgroup
      (fun n : G => ∀ m ∈ GLBCore 3 3 B,
        ∃ m' ∈ GLBCore 3 3 B, ∃ n' ∈ K₂ ⊔ K₁ ⊔ gammaOneThree B, n * m = m' * n')
      (fun m hm => ⟨m, hm, 1, Subgroup.one_mem _, by simp⟩)
      (fun a b ha hb m hm => by
        obtain ⟨m₁, hm₁, n₁, hn₁, e₁⟩ := hb m hm
        obtain ⟨m₂, hm₂, n₂, hn₂, e₂⟩ := ha m₁ hm₁
        refine ⟨m₂, hm₂, n₂ * n₁, Subgroup.mul_mem _ hn₂ hn₁, ?_⟩
        calc a * b * m = a * (b * m) := by rw [mul_assoc]
          _ = a * (m₁ * n₁) := by rw [e₁]
          _ = (a * m₁) * n₁ := by rw [mul_assoc]
          _ = (m₂ * n₂) * n₁ := by rw [e₂]
          _ = m₂ * (n₂ * n₁) := by rw [mul_assoc])
    have hle : K₂ ⊔ K₁ ⊔ gammaOneThree B ≤ D := by
      refine sup_le (sup_le ?_ ?_) ?_
      · intro k hk m hm
        obtain ⟨m', hm', k', hk', e⟩ := hgen m hm k (Or.inr hk)
        exact ⟨m', hm', k', by rcases hk' with h | h; exacts [hK₁N h, hK₂N h], e⟩
      · intro k hk m hm
        obtain ⟨m', hm', k', hk', e⟩ := hgen m hm k (Or.inl hk)
        exact ⟨m', hm', k', by rcases hk' with h | h; exacts [hK₁N h, hK₂N h], e⟩
      · intro g hg m hm
        exact ⟨g * m, Subgroup.mul_mem _ (hM2M1 hg) hm, 1, Subgroup.one_mem _, by simp⟩
    exact fun n hn => hle hn
  have hperm : Permutable (K₂ ⊔ K₁ ⊔ gammaOneThree B) (GLBCore 3 3 B) := by
    refine permutable_of_mul_subset ?_
    rintro _ ⟨n, hn, m, hm, rfl⟩
    obtain ⟨m', hm', n', hn', e⟩ := hA n hn m hm
    exact ⟨m', hm', n', hn', e.symm⟩
  have heven := even_card_glaPPrimeCoreOf_of_le h75 h76 hK₁ hN₀ne hBN₀ (sup_le hK₁N hM₂N)
  have hY : GLAPPrimeCoreOf 3 (K₂ ⊔ K₁ ⊔ gammaOneThree B) ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at heven
    exact Nat.not_even_one heven
  have hYM : GLAPPrimeCoreOf 3 (K₂ ⊔ K₁ ⊔ gammaOneThree B) ≤ GLBCore 3 3 B :=
    (le_gammaOneThree_of_normalized hS hB
      (hBN₀.trans (le_normalizer_glaPPrimeCoreOf 3 _))
      (not_dvd_card_glaPPrimeCoreOf Nat.prime_three _)).trans hM2M1
  have hM1ne : GLBCore 3 3 B ≠ ⊤ := fun htop =>
    Proving.ne_top_of_even_card_glaPPrimeCoreOf (G := G) Nat.prime_three hS.beta.2.2.1 h63.2
      (top_le_iff.1 (htop ▸ h63.1))
  have hfin := sup_ne_top_of_normalizes hperm hM1ne hY hYM (le_normalizer_glaPPrimeCoreOf 3 _)
  have heq : K₂ ⊔ K₁ ⊔ gammaOneThree B ⊔ GLBCore 3 3 B = K₂ ⊔ K₁ ⊔ GLBCore 3 3 B := by
    rw [sup_assoc, sup_eq_right.2 hM2M1]
  rwa [heq] at hfin

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7
