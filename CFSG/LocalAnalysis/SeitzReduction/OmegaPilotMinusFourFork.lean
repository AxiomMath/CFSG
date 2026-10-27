module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusFourMain

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup

section Abstract

variable {G : Type*} [Group G]

theorem exists_mul_eq_of_mem_sup_centralProd {A B : Subgroup G}
    (hAB : A ≤ centralizer (B : Set G)) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  have hcomm : ∀ (a : A) (b : B), Commute (A.subtype a) (B.subtype b) := fun a b =>
    (mem_centralizer_iff.1 (hAB a.2) b b.2).symm
  have hrange : (MonoidHom.noncommCoprod A.subtype B.subtype hcomm).range = A ⊔ B := by
    rw [MonoidHom.noncommCoprod_range, range_subtype, range_subtype]
  rw [← hrange] at hx
  obtain ⟨⟨a, b⟩, rfl⟩ := hx
  exact ⟨a, a.2, b, b.2, rfl⟩

theorem mul_eq_mul_cancel_of_inf_eq_bot {A B : Subgroup G} (hAB1 : A ⊓ B = ⊥)
    {a a' b b' : G} (ha : a ∈ A) (ha' : a' ∈ A) (hb : b ∈ B) (hb' : b' ∈ B)
    (h : a * b = a' * b') : a = a' ∧ b = b' := by
  have h1 : a'⁻¹ * a = b' * b⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
      _ = b' * b⁻¹ := by group
  have h2 : a'⁻¹ * a ∈ A ⊓ B :=
    Subgroup.mem_inf.2 ⟨mul_mem (inv_mem ha') ha, h1 ▸ mul_mem hb' (inv_mem hb)⟩
  rw [hAB1, mem_bot] at h2
  have haa : a = a' := by
    calc a = a' * (a'⁻¹ * a) := by group
      _ = a' := by rw [h2, mul_one]
  refine ⟨haa, ?_⟩
  rw [haa] at h
  exact mul_left_cancel h

theorem conj_mem_of_mem_sup_of_le_centralizer {A B : Subgroup G}
    (hAB : A ≤ centralizer (B : Set G)) {m : G} (hm : m ∈ A ⊔ B) {a : G} (ha : a ∈ A) :
    m * a * m⁻¹ ∈ A := by
  obtain ⟨x, hx, y, hy, rfl⟩ := exists_mul_eq_of_mem_sup_centralProd hAB hm
  have hya : y * a = a * y := mem_centralizer_iff.1 (hAB ha) y hy
  have h1 : x * y * a * (x * y)⁻¹ = x * a * x⁻¹ := by
    calc x * y * a * (x * y)⁻¹ = x * (y * a) * y⁻¹ * x⁻¹ := by group
      _ = x * (a * y) * y⁻¹ * x⁻¹ := by rw [hya]
      _ = x * a * x⁻¹ := by group
  rw [h1]
  exact mul_mem (mul_mem hx ha) (inv_mem hx)

theorem map_conj_eq_or_eq_of_mem_normalizer_sup [Finite G] {A B : Subgroup G}
    (hAB : A ≤ centralizer (B : Set G)) [IsSimpleGroup A] [IsSimpleGroup B]
    (hAnab : ∃ x ∈ A, ∃ y ∈ A, x * y ≠ y * x) (hcard : Nat.card A = Nat.card B) {t : G}
    (ht : t ∈ normalizer ((A ⊔ B : Subgroup G) : Set G)) :
    A.map (MulAut.conj t).toMonoidHom = A ∨ A.map (MulAut.conj t).toMonoidHom = B := by
  have hBA : B ≤ centralizer (A : Set G) := le_centralizer_iff.1 hAB
  set V := A.map (MulAut.conj t).toMonoidHom with hV
  have hcardV : Nat.card V = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.conj t).injective
  have hmemV : ∀ v, v ∈ V ↔ t⁻¹ * v * t ∈ A := by
    intro v
    constructor
    · rintro ⟨a, ha, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using ha
    · intro hv
      exact ⟨t⁻¹ * v * t, hv, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hVn : ∀ m ∈ A ⊔ B, ∀ v ∈ V, m * v * m⁻¹ ∈ V := by
    intro m hm v hv
    rw [hmemV] at hv ⊢
    have hm' : t⁻¹ * m * t ∈ A ⊔ B := by
      have h1 := (mem_normalizer_iff.1 (inv_mem ht) m).1 hm
      simpa using h1
    have h2 := conj_mem_of_mem_sup_of_le_centralizer hAB hm' hv
    have h3 : t⁻¹ * (m * v * m⁻¹) * t = t⁻¹ * m * t * (t⁻¹ * v * t) * (t⁻¹ * m * t)⁻¹ := by group
    rw [h3]
    exact h2
  have hVle : V ≤ A ⊔ B := by
    intro v hv
    rw [hmemV] at hv
    have h1 := (mem_normalizer_iff.1 ht _).1 (mem_sup_left hv)
    simpa [mul_assoc] using h1
  have hAn : ∀ m ∈ A ⊔ B, ∀ a ∈ A, m * a * m⁻¹ ∈ A := fun m hm a ha =>
    conj_mem_of_mem_sup_of_le_centralizer hAB hm ha
  have hBn : ∀ m ∈ A ⊔ B, ∀ b ∈ B, m * b * m⁻¹ ∈ B := fun m hm b hb =>
    conj_mem_of_mem_sup_of_le_centralizer hBA (by rwa [sup_comm]) hb
  have hint : ∀ C : Subgroup G, (∀ m ∈ A ⊔ B, ∀ c ∈ C, m * c * m⁻¹ ∈ C) → C ≤ A ⊔ B →
      ∀ [IsSimpleGroup C], V ⊓ C = ⊥ ∨ C ≤ V := by
    intro C hCn hCle _
    let N : Subgroup C := (V ⊓ C).subgroupOf C
    have hN : N.Normal := ⟨fun n hn g => by
      rw [mem_subgroupOf] at hn ⊢
      exact ⟨hVn _ (hCle g.2) _ hn.1, hCn _ (hCle g.2) _ hn.2⟩⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · left
      rw [eq_bot_iff]
      intro x hx
      have hxN : (⟨x, hx.2⟩ : C) ∈ N := hx
      rw [h, mem_bot] at hxN
      rw [mem_bot]
      exact congrArg Subtype.val hxN
    · right
      intro x hx
      have hxN : (⟨x, hx⟩ : C) ∈ N := h ▸ mem_top _
      exact (mem_subgroupOf.1 hxN).1
  have hcomm_of_bot : ∀ C : Subgroup G, (∀ m ∈ A ⊔ B, ∀ c ∈ C, m * c * m⁻¹ ∈ C) → C ≤ A ⊔ B →
      V ⊓ C = ⊥ → ∀ v ∈ V, ∀ c ∈ C, v * c = c * v := by
    intro C hCn hCle hbot v hv c hc
    have h1 : v * c * v⁻¹ * c⁻¹ ∈ V ⊓ C := by
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · have h2 := hVn c (hCle hc) v⁻¹ (inv_mem hv)
        have h3 : v * c * v⁻¹ * c⁻¹ = v * (c * v⁻¹ * c⁻¹) := by group
        rw [h3]
        exact mul_mem hv h2
      · exact mul_mem (hCn v (hVle hv) c hc) (inv_mem hc)
    rw [hbot, mem_bot] at h1
    calc v * c = v * c * v⁻¹ * c⁻¹ * (c * v) := by group
      _ = c * v := by rw [h1, one_mul]
  rcases hint A hAn le_sup_left with hA | hA
  · rcases hint B hBn le_sup_right with hB | hB
    ·
      exfalso
      obtain ⟨x, hx, y, hy, hxy⟩ := hAnab
      have hvA := hcomm_of_bot A hAn le_sup_left hA
      have hvB := hcomm_of_bot B hBn le_sup_right hB
      have hcentral : ∀ v ∈ V, ∀ m ∈ A ⊔ B, v * m = m * v := by
        intro v hv m hm
        obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_eq_of_mem_sup_centralProd hAB hm
        rw [← mul_assoc, hvA v hv a ha, mul_assoc, hvB v hv b hb, mul_assoc]
      have hx' : t * x * t⁻¹ ∈ V := ⟨x, hx, rfl⟩
      have hy' : t * y * t⁻¹ ∈ V := ⟨y, hy, rfl⟩
      have h1 := hcentral _ hx' _ (hVle hy')
      apply hxy
      have h2 : t * (x * y) * t⁻¹ = t * (y * x) * t⁻¹ := by
        calc t * (x * y) * t⁻¹ = (t * x * t⁻¹) * (t * y * t⁻¹) := by group
          _ = (t * y * t⁻¹) * (t * x * t⁻¹) := h1
          _ = t * (y * x) * t⁻¹ := by group
      simpa using h2
    · right
      exact (Subgroup.eq_of_le_of_card_ge hB (by rw [hcardV, hcard])).symm
  · left
    exact (Subgroup.eq_of_le_of_card_ge hA (by rw [hcardV])).symm

theorem le_centralizer_of_diag [Finite G] {A B R : Subgroup G}
    (hAB : A ≤ centralizer (B : Set G)) (hAB1 : A ⊓ B = ⊥) {t : G}
    (htA : A.map (MulAut.conj t).toMonoidHom = A) (htB : B.map (MulAut.conj t).toMonoidHom = B)
    (hRM : R ≤ A ⊔ B) (hRt : R ≤ centralizer ({t} : Set G)) (hRB : R ⊓ B = ⊥)
    (hcard : Nat.card A ≤ Nat.card R) :
    A ≤ centralizer ({t} : Set G) := by
  have hdec : ∀ r : R, ∃ a ∈ A, ∃ b ∈ B, a * b = (r : G) := fun r =>
    exists_mul_eq_of_mem_sup_centralProd hAB (hRM r.2)
  choose p hpA q hqB hpq using hdec
  set φ : R → A := fun r => ⟨p r, hpA r⟩ with hφ
  have hinj : Function.Injective φ := by
    intro r r' h
    have hp : p r = p r' := congrArg Subtype.val h
    have h1 : (r' : G)⁻¹ * r = (q r')⁻¹ * q r := by
      rw [← hpq r, ← hpq r', hp]
      group
    have h2 : (r' : G)⁻¹ * r ∈ R ⊓ B :=
      Subgroup.mem_inf.2 ⟨mul_mem (inv_mem r'.2) r.2, h1 ▸ mul_mem (inv_mem (hqB r')) (hqB r)⟩
    rw [hRB, mem_bot] at h2
    apply Subtype.ext
    calc (r : G) = r' * ((r' : G)⁻¹ * r) := by group
      _ = r' := by rw [h2, mul_one]
  have hsurj : Function.Surjective φ := (hinj.bijective_of_nat_card_le hcard).2
  have hconjA : ∀ a ∈ A, t * a * t⁻¹ ∈ A := fun a ha => htA ▸ ⟨a, ha, rfl⟩
  have hconjB : ∀ b ∈ B, t * b * t⁻¹ ∈ B := fun b hb => htB ▸ ⟨b, hb, rfl⟩
  intro a ha
  obtain ⟨r, hr⟩ := hsurj ⟨a, ha⟩
  have hra : p r = a := congrArg Subtype.val hr
  have htr : t * (r : G) * t⁻¹ = r := by
    have h := mem_centralizer_singleton_iff.1 (hRt r.2)
    rw [← h, mul_inv_cancel_right]
  have hdecomp : t * p r * t⁻¹ * (t * q r * t⁻¹) = p r * q r := by
    calc t * p r * t⁻¹ * (t * q r * t⁻¹) = t * (p r * q r) * t⁻¹ := by group
      _ = t * r * t⁻¹ := by rw [hpq r]
      _ = r := htr
      _ = p r * q r := (hpq r).symm
  obtain ⟨h1, -⟩ := mul_eq_mul_cancel_of_inf_eq_bot hAB1 (hconjA _ (hpA r)) (hpA r)
    (hconjB _ (hqB r)) (hqB r) hdecomp
  rw [mem_centralizer_singleton_iff, ← hra]
  exact (calc t * p r = t * p r * t⁻¹ * t := by group
    _ = p r * t := by rw [h1]).symm

theorem card_sup_centralProd [Finite G] {A B : Subgroup G}
    (hAB : A ≤ centralizer (B : Set G)) (hAB1 : A ⊓ B = ⊥) :
    Nat.card (A ⊔ B : Subgroup G) = Nat.card A * Nat.card B := by
  have hcomm : ∀ (a : A) (b : B), Commute (A.subtype a) (B.subtype b) := fun a b =>
    (mem_centralizer_iff.1 (hAB a.2) b b.2).symm
  have hinj : Function.Injective (MonoidHom.noncommCoprod A.subtype B.subtype hcomm) :=
    (MonoidHom.noncommCoprod_injective _ _ _).2 ⟨A.subtype_injective, B.subtype_injective,
      by rw [range_subtype, range_subtype, disjoint_iff]; exact hAB1⟩
  have hrange : (MonoidHom.noncommCoprod A.subtype B.subtype hcomm).range = A ⊔ B := by
    rw [MonoidHom.noncommCoprod_range, range_subtype, range_subtype]
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod]

end Abstract

section Fork

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadMinus
  minusIndexEquiv)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore_le_centralizer
  centralizerPerfectCore_anti commutator_centralizerPerfectCore)
open scoped MatrixGroups

variable
  {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {F : Type} [Field F] [Finite F] [CharP F 2]

theorem forkSwap_of_diag (hset : SeitzSetting G L) {f : ℕ} (hKc : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus 4 K (by norm_num) b c)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {ι : K →+* F}
    (hFK : Nat.card F = Nat.card K ^ 2) (C₀ : MinusFieldCover (r := 2) e ι 0)
    (h2 : modelToG e (stabPairsBar (coordinateQuadMinus 4 K (by norm_num) b c)
        (minusIndexEquiv 4 (by norm_num) (.inl 0)) (minusIndexEquiv 4 (by norm_num) (.inr (.inl 0)))
        (minusIndexEquiv 4 (by norm_num) (.inl 1))
        (minusIndexEquiv 4 (by norm_num) (.inr (.inl 1)))) ⊓ minusNode C₀ 2 = ⊥)
    (h3 : modelToG e (stabPairsBar (coordinateQuadMinus 4 K (by norm_num) b c)
        (minusIndexEquiv 4 (by norm_num) (.inl 0)) (minusIndexEquiv 4 (by norm_num) (.inr (.inl 0)))
        (minusIndexEquiv 4 (by norm_num) (.inl 1))
        (minusIndexEquiv 4 (by norm_num) (.inr (.inl 1)))) ⊓ minusNode C₀ 3 = ⊥) :
    (minusNode C₀ 2).map (MulAut.conj t).toMonoidHom = minusNode C₀ 3 := by
  have hf : 1 ≤ f := LinearPilot.one_le_of_card_eq_two_pow hKc
  have hF16 : 16 ≤ Nat.card F := by rw [hFK]; nlinarith
  have hF4 : 4 ≤ Nat.card F := by omega
  have hF9 : Nat.card F ≠ 9 := by
    intro h9
    rw [hFK] at h9
    nlinarith
  set U₂ := minusNode C₀ 2 with hU₂
  set U₃ := minusNode C₀ 3 with hU₃
  set R := modelToG e (stabPairsBar (coordinateQuadMinus 4 K (by norm_num) b c)
    (minusIndexEquiv 4 (by norm_num) (.inl 0)) (minusIndexEquiv 4 (by norm_num) (.inr (.inl 0)))
    (minusIndexEquiv 4 (by norm_num) (.inl 1))
    (minusIndexEquiv 4 (by norm_num) (.inr (.inl 1)))) with hRdef
  have h2eq : U₂ = C₀.lift (forkBlock F 2 ∅) := minusNode_of_eq C₀ (j := 2) rfl
  have h3eq : U₃ = C₀.lift (forkBlock F 2 {Fin.last 2}) := minusNode_of_eq_succ C₀ (j := 3) rfl
  obtain ⟨ψ₂⟩ := nonempty_mulEquiv_lift_forkBlock C₀ (by omega) hF9 (by omega : 1 ≤ 2) ∅
  obtain ⟨ψ₃⟩ := nonempty_mulEquiv_lift_forkBlock C₀ (by omega) hF9 (by omega : 1 ≤ 2)
    {Fin.last 2}
  rw [← h2eq] at ψ₂
  rw [← h3eq] at ψ₃
  have := LinearPilot.isSimpleGroup_specialLinearGroup_two (K := F) hF4
  have : IsSimpleGroup U₂ := ψ₂.symm.isSimpleGroup
  have : IsSimpleGroup U₃ := ψ₃.symm.isSimpleGroup
  have hcardSL : Nat.card (SL(2, F)) = Nat.card R := by
    rw [CFSG.UnitaryInvolutionIndex.card_specialLinearGroup_fin_two, hFK, hRdef,
      UnitaryPilot.card_modelToG,
      (minusStabPairsBar_four (K := K) hirr (i := 0) (j := 1) (by decide)).2.2, ← pow_mul]
  have hc2 : Nat.card U₂ = Nat.card R := (Nat.card_congr ψ₂.toEquiv).symm.trans hcardSL
  have hc3 : Nat.card U₃ = Nat.card R := (Nat.card_congr ψ₃.toEquiv).symm.trans hcardSL
  have hnab : ∀ U : Subgroup G, ⁅U, U⁆ = U → 1 < Nat.card U →
      ∃ x ∈ U, ∃ y ∈ U, x * y ≠ y * x := by
    intro U hU h1
    by_contra hcon
    push Not at hcon
    have hbot : ⁅U, U⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro x hx y hy
      rw [commutatorElement_def, hcon x hx y hy, mul_inv_cancel_right, mul_inv_cancel,
        Subgroup.mem_bot]
    rw [hU] at hbot
    rw [hbot, Subgroup.card_bot] at h1
    exact lt_irrefl _ h1
  have hR1 : 1 < Nat.card R := by
    rw [← hcardSL, CFSG.UnitaryInvolutionIndex.card_specialLinearGroup_fin_two]
    have : 2 ≤ Nat.card F ^ 2 - 1 := by
      have : 16 ≤ Nat.card F ^ 2 := by nlinarith
      omega
    nlinarith
  have hn2 := hnab U₂ (commutator_minusNode C₀ 2) (hc2 ▸ hR1)
  have hn3 := hnab U₃ (commutator_minusNode C₀ 3) (hc3 ▸ hR1)
  have h23 : U₂ ≤ centralizer (U₃ : Set G) := by
    rw [h2eq, h3eq]
    exact lift_forkBlock_le_centralizer C₀ (by omega) hF4
  have h32 : U₃ ≤ centralizer (U₂ : Set G) := le_centralizer_iff.1 h23
  have hZ2 : center U₂ = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center U₂) with h | h
    · exact h
    · exfalso
      obtain ⟨x, hx, y, hy, hxy⟩ := hn2
      apply hxy
      have hc := mem_center_iff.1 (h ▸ Subgroup.mem_top (G := U₂) ⟨y, hy⟩) ⟨x, hx⟩
      have hc' := congrArg Subtype.val hc
      simp only [Subgroup.coe_mul] at hc'
      exact hc'
  have h23bot : U₂ ⊓ U₃ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxZ : (⟨x, hx.1⟩ : U₂) ∈ center U₂ := by
      rw [mem_center_iff]
      intro y
      exact Subtype.ext (mem_centralizer_iff.1 (h32 hx.2) y y.2)
    rw [hZ2, mem_bot] at hxZ
    rw [mem_bot]
    exact congrArg Subtype.val hxZ
  have h32bot : U₃ ⊓ U₂ = ⊥ := by rwa [inf_comm]
  have hM : minusPieceCore e {Fin.last 2} = U₂ ⊔ U₃ := by
    refine le_antisymm (minusPieceCore_le_sup_minusNode_four C₀ hq hF4) (sup_le ?_ ?_)
    · rw [h2eq]
      exact lift_forkBlock_le_minusPieceCore C₀ hF4 (by omega) (Finset.empty_subset _)
    · rw [h3eq]
      exact lift_forkBlock_le_minusPieceCore C₀ hF4 (by omega) le_rfl
  have htM : t ∈ normalizer ((U₂ ⊔ U₃ : Subgroup G) : Set G) :=
    hM ▸ mem_normalizer_minusPieceCore e htC _
  have htM' : t ∈ normalizer ((U₃ ⊔ U₂ : Subgroup G) : Set G) := by rwa [sup_comm]
  have hRq := (minusStabPairsBar_four (K := K) hirr (i := 0) (j := 1) (by decide)).1
  have hRM : R ≤ U₂ ⊔ U₃ := by
    rw [← hM]
    have h01c : (({0, 1} : Finset (Fin (4 - 1)))ᶜ) = {Fin.last 2} := by decide
    have hc := modelToG_stabPairsBar_le_minusPieceCore (by norm_num) e (i := 0) (j := 1)
      (by decide) (Subgroup.isPerfect_iff.mp hRq.1)
    rwa [h01c] at hc
  have hRL : R ≤ L := fun x hx => by
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2
  have hRt : R ≤ centralizer ({t} : Set G) := fun x hx =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC x (hRL hx))
  rcases map_conj_eq_or_eq_of_mem_normalizer_sup h23 hn2 (hc2.trans hc3.symm) htM with h | h
  · exfalso
    have hU3 : U₃.map (MulAut.conj t).toMonoidHom = U₃ := by
      rcases map_conj_eq_or_eq_of_mem_normalizer_sup h32 hn3 (hc3.trans hc2.symm) htM' with
        h' | h'
      · exact h'
      · exfalso
        have hEq : U₃ = U₂ := Subgroup.map_injective (MulAut.conj t).injective (h'.trans h.symm)
        have h1 : U₂ ⊓ U₃ = U₂ := by rw [hEq, inf_idem]
        rw [h23bot] at h1
        have h2' := congrArg (fun H : Subgroup G => Nat.card H) h1
        simp only [Subgroup.card_bot] at h2'
        rw [hc2] at h2'
        omega
    have hU2t := le_centralizer_of_diag h23 h23bot h hU3 hRM hRt h3 hc2.le
    have hU3t := le_centralizer_of_diag h32 h32bot hU3 h (by rwa [sup_comm]) hRt h2 hc3.le
    have hMt : minusPieceCore e {Fin.last 2} ≤ centralizer ({t} : Set G) :=
      hM ▸ sup_le hU2t hU3t
    have hMp : ⁅minusPieceCore e {Fin.last 2}, minusPieceCore e {Fin.last 2}⁆ =
        minusPieceCore e {Fin.last 2} := commutator_centralizerPerfectCore _
    have hOut : Group.IsSolvable (Outer L) :=
      isSolvable_outer_of_mulEquiv_minus le_rfl hf hKc hirr e
    have hML : minusPieceCore e {Fin.last 2} ≤ L :=
      std_perfect_le hset.standardSetting hOut htC ht hMp hMt
    have hX : ∀ k : Fin (4 - 1), k ≠ Fin.last 2 → minusPieceCore e {Fin.last 2} ≤
        centralizer (modelToG e (minusPairTorus (K := K) (by norm_num) b c k) : Set G) := by
      intro k hk
      refine (centralizerPerfectCore_anti (UnitaryPilot.modelToG_mono e
        (minusPairTorus_le_minusPlaneTorus ?_))).trans (centralizerPerfectCore_le_centralizer _)
      simpa using hk
    have hMR : minusPieceCore e {Fin.last 2} ≤ R :=
      perfect_le_modelToG_stabPairsBar hq
        (isHypCoord_coordinateQuadMinus (by norm_num) b c _)
        (isHypCoord_coordinateQuadMinus (by norm_num) b c _) e
        (Subgroup.isPerfect_iff.mp hRq.1) hMp hML (hX 0 (by decide)) (hX 1 (by decide))
    have hcardM : Nat.card (minusPieceCore e {Fin.last 2}) = Nat.card R * Nat.card R := by
      rw [hM, card_sup_centralProd h23 h23bot, hc2, hc3]
    have hle := Subgroup.card_le_of_le hMR
    rw [hcardM] at hle
    nlinarith
  · exact h

end Fork

section Input

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadMinus
  minusIndexEquiv)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

@[expose] def OmegaMinusFourForkDiagInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K),
      (∀ s : K, s ^ 2 + b * s + c ≠ 0) → Nat.card K = 2 ^ f → 2 ≤ f →
      ∀ (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus 4 K (by norm_num) b c)) (t : G),
        orderOf t = 2 → centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
        (∀ k : Fin (4 - 1), OmegaRowAt t (modelToG e (minusPairTorus (K := K) (by norm_num) b c k))
          (modelToG e (minusPairPerp (K := K) (by norm_num) b c k)) .field) →
      ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (ι : K →+* F) (σ : F ≃+* F),
        orderOf σ = 2 → (∀ x : F, σ x = x ↔ x ∈ Set.range ι) →
      ∀ C₀ : MinusFieldCover (r := 2) e ι 0,
        modelToG e (stabPairsBar (coordinateQuadMinus 4 K (by norm_num) b c)
            (minusIndexEquiv 4 (by norm_num) (.inl 0))
            (minusIndexEquiv 4 (by norm_num) (.inr (.inl 0)))
            (minusIndexEquiv 4 (by norm_num) (.inl 1))
            (minusIndexEquiv 4 (by norm_num) (.inr (.inl 1)))) ⊓ minusNode C₀ 2 = ⊥ ∧
          modelToG e (stabPairsBar (coordinateQuadMinus 4 K (by norm_num) b c)
            (minusIndexEquiv 4 (by norm_num) (.inl 0))
            (minusIndexEquiv 4 (by norm_num) (.inr (.inl 0)))
            (minusIndexEquiv 4 (by norm_num) (.inl 1))
            (minusIndexEquiv 4 (by norm_num) (.inr (.inl 1)))) ⊓ minusNode C₀ 3 = ⊥

theorem omegaMinusFourForkSwapInput_of_diag (hdiag : OmegaMinusFourForkDiagInput) :
    OmegaMinusFourForkSwapInput := by
  intro G _ _ L hset f K _ _ _ b c hirr hKc hf2 e t ht hKt hrow F _ _ _ ι σ hσ hfix C₀
  have hq : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf2
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hFK : Nat.card F = Nat.card K ^ 2 := by
    rw [SymplecticPilot.natCard_eq_two_pow_two_mul_of_fix ι hKc hσ hfix, hKc, ← pow_mul,
      mul_comm]
  obtain ⟨h2, h3⟩ := hdiag G L hset f K b c hirr hKc hf2 e t ht hKt hrow F ι σ hσ hfix C₀
  exact forkSwap_of_diag hset hKc hq hirr e htC ht hFK C₀ h2 h3

end Input

end CFSG.SeitzReduction.OmegaPilot
