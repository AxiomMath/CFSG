module

public import CFSG.GH74.GLS.C3.Layer1.Th2Leaves
public import CFSG.GH74.GLS.C3.Layer1.BackConj
public import CFSG.LieType.SteinbergBRTwoRankBound
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Order
public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.GH74.GLS.Th2Tstar

open Subgroup CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank CFSG.Blueprint

section Orders

theorem card_psl_three_four {F : Type} [Field F] [Finite F] (h : Nat.card F = 4) :
    Nat.card (StatedProj (StatedSL 3 F)) = 20160 := by
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num), h]
  decide

theorem two_mul_card_of_hasL2Model {H : Type} [Group H] {P : ℕ → Prop} (hP : ∀ q, P q → Odd q)
    (h : HasL2Model H P) : ∃ q, P q ∧ Nat.card H * 2 = q * (q ^ 2 - 1) := by
  obtain ⟨p, f, hp, hf, hPq, hL⟩ := h
  obtain ⟨-, -, F, _, _, hF, ⟨e⟩⟩ := CFSG.GH74.Generic.lieModel_psl_data hL
  have hodd : Odd (p ^ f) := hP _ hPq
  have hoddF : Odd (Nat.card F) := hF ▸ hodd
  refine ⟨p ^ f, hPq, ?_⟩
  have h2 : 2 ∣ Nat.card F * (Nat.card F ^ 2 - 1) := by
    have h3 : Even (Nat.card F ^ 2 - 1) := Nat.Odd.sub_odd (hoddF.pow) odd_one
    exact even_iff_two_dvd.1 (h3.mul_left _)
  rw [Nat.card_congr e.toEquiv,
    CFSG.ComponentClassification.CatFactsSp4.card_statedProj_statedSL_two_odd hoddF, hF]
  rw [hF] at h2
  exact Nat.div_mul_cancel h2

theorem eq_five_of_mul {q : ℕ} (h : 120 = q * (q ^ 2 - 1)) : q = 5 := by
  have hq1 : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · simp at h
    · exact hq
  have hq6 : q < 6 := by
    by_contra hge
    push Not at hge
    have h1 : 6 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hge 2
    have h2 : 35 ≤ q ^ 2 - 1 := by omega
    have := Nat.mul_le_mul hge h2
    omega
  interval_cases q <;> simp_all

theorem false_of_mul_a7 {q : ℕ} (h : 5040 = q * (q ^ 2 - 1)) : False := by
  have hq1 : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · simp at h
    · exact hq
  have hq18 : q < 18 := by
    by_contra hge
    push Not at hge
    have h1 : 18 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hge 2
    have h2 : 323 ≤ q ^ 2 - 1 := by omega
    have := Nat.mul_le_mul hge h2
    omega
  interval_cases q <;> simp_all

theorem isFM9_five : IsFM9 5 :=
  Or.inr ⟨by norm_num, Or.inl ⟨1, by norm_num⟩⟩

theorem hasL2Model_alt5 {H : Type} [Group H] {P : ℕ → Prop} (hP : ∀ q, P q → Odd q)
    (e : H ≃* alternatingGroup (Fin 5)) (h : HasL2Model H P) : P 5 := by
  obtain ⟨q, hq, hcard⟩ := two_mul_card_of_hasL2Model hP h
  have h60 : Nat.card H = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    simp [Nat.factorial]
  rw [h60] at hcard
  have := eq_five_of_mul (by omega : 120 = q * (q ^ 2 - 1))
  exact this ▸ hq

theorem not_hasL2Model_alt7 {H : Type} [Group H] {P : ℕ → Prop} (hP : ∀ q, P q → Odd q)
    (e : H ≃* alternatingGroup (Fin 7)) (h : HasL2Model H P) : False := by
  obtain ⟨q, hq, hcard⟩ := two_mul_card_of_hasL2Model hP h
  have h2520 : Nat.card H = 2520 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.card_eq_fintype_card, Nat.factorial]
  rw [h2520] at hcard
  exact false_of_mul_a7 (by omega)

theorem not_isL34Quotient_of_card_lt {H : Type} [Group H] [Finite H] (hH : Nat.card H < 20160) :
    ¬ IsL34Quotient H := by
  intro h
  obtain ⟨-, -, F, _, _, hF, ⟨e⟩⟩ := CFSG.GH74.Generic.lieModel_psl_data h
  have hF4 : Nat.card F = 4 := by rw [hF]; norm_num
  have h1 : Nat.card (H ⧸ center H) = 20160 := by
    rw [Nat.card_congr e.toEquiv, card_psl_three_four hF4]
  have h2 : Nat.card (H ⧸ center H) ∣ Nat.card H := Subgroup.index_dvd_card (center H)
  have := Nat.le_of_dvd Nat.card_pos h2
  omega

end Orders

theorem pRank_le_two_of_card_four {X : Type} [Group X] [Finite X] (h : Nat.card X = 4) :
    pRank 2 X ≤ 2 :=
  CFSG.LieType.SteinbergBR.pRank_le_of_card_le one_lt_two fun A _ => by
    calc Nat.card A ≤ Nat.card X := Subgroup.card_le_card_group A
      _ = 2 ^ 2 := by rw [h]; norm_num

section Sup

variable {G : Type} [Group G]

theorem mem_normalizer_of_conj_mem {H : Subgroup G} {c : G}
    (h₁ : ∀ x ∈ H, c * x * c⁻¹ ∈ H) (h₂ : ∀ x ∈ H, c⁻¹ * x * c⁻¹⁻¹ ∈ H) :
    c ∈ normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h₁ x, fun hx => ?_⟩
  simpa [mul_assoc] using h₂ _ hx

theorem conj_mem_of_iSup {ι : Sort*} {S : ι → Subgroup G} {W : Subgroup G} (c : G)
    (h : ∀ i, ∀ x ∈ S i, c * x * c⁻¹ ∈ W) : ∀ x ∈ ⨆ i, S i, c * x * c⁻¹ ∈ W := by
  intro x hx
  refine Subgroup.iSup_induction S (C := fun y => c * y * c⁻¹ ∈ W) hx h (by simp) ?_
  intro y z hy hz
  have : c * (y * z) * c⁻¹ = (c * y * c⁻¹) * (c * z * c⁻¹) := by group
  rw [this]
  exact W.mul_mem hy hz

theorem conj_mem_biSup {ι : Type*} {p : ι → Prop} {F : ι → Subgroup G} (c : G)
    (h : ∀ i, p i → ∃ j, p j ∧ ∀ x ∈ F i, c * x * c⁻¹ ∈ F j) :
    ∀ x ∈ ⨆ i, ⨆ (_ : p i), F i, c * x * c⁻¹ ∈ ⨆ i, ⨆ (_ : p i), F i :=
  conj_mem_of_iSup c fun i => conj_mem_of_iSup c fun hi x hx => by
    obtain ⟨j, hj, hjx⟩ := h i hi
    exact Subgroup.mem_iSup_of_mem j (Subgroup.mem_iSup_of_mem hj (hjx x hx))

end Sup

section Transport

variable {G : Type} [Group G]

theorem omega1_map (φ : G ≃* G) (H : Subgroup G) :
    omega1 (H.map φ.toMonoidHom) = (omega1 H).map φ.toMonoidHom := by
  unfold omega1
  rw [MonoidHom.map_closure]
  congr 1
  ext u
  constructor
  · rintro ⟨⟨h, hh, rfl⟩, hu2⟩
    refine ⟨h, ⟨hh, ?_⟩, rfl⟩
    apply φ.injective
    simpa using hu2
  · rintro ⟨h, ⟨hh, hh2⟩, rfl⟩
    exact ⟨⟨h, hh, rfl⟩, by simp [← map_mul, hh2]⟩

theorem inf_centralizer_map (φ : G ≃* G) (T B : Subgroup G) :
    T.map φ.toMonoidHom ⊓ centralizer ((B.map φ.toMonoidHom : Subgroup G) : Set G) =
      (T ⊓ centralizer (B : Set G)).map φ.toMonoidHom := by
  ext y
  simp only [Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, hy⟩
    refine ⟨t, ⟨ht, fun b hb => ?_⟩, rfl⟩
    have := hy (φ.toMonoidHom b) ⟨b, hb, rfl⟩
    apply φ.injective
    simpa using this
  · rintro ⟨t, ⟨ht, hc⟩, rfl⟩
    refine ⟨⟨t, ht, rfl⟩, ?_⟩
    rintro _ ⟨b, hb, rfl⟩
    have := hc b hb
    simpa [← map_mul] using congrArg φ this

theorem isSn_map [Finite G] (φ : G ≃* G) {T B : Subgroup G} {n : ℕ} (h : IsSn n T B) :
    IsSn n (T.map φ.toMonoidHom) (B.map φ.toMonoidHom) := by
  obtain ⟨⟨hBT, hel, hB⟩, hn⟩ := h
  refine ⟨⟨Subgroup.map_mono hBT, ?_, ?_⟩, ?_⟩
  · have := hel
    exact CFSG.IsElementaryAbelian.map φ.toMonoidHom
  · rw [inf_centralizer_map, omega1_map, ← hB]
  · have := CFSG.RankThree.PartOne.Quotient36.pRank_congr_mulEquiv one_lt_two
      (B.equivMapOfInjective φ.toMonoidHom φ.injective)
    rwa [← this]

theorem map_conj_eq_of_mem_normalizer {T : Subgroup G} {c : G} (hc : c ∈ normalizer (T : Set G)) :
    T.map (MulAut.conj c).toMonoidHom = T := by
  have h1 : ∀ t ∈ T, c * t * c⁻¹ ∈ T := fun t ht => (Subgroup.mem_normalizer_iff.1 hc t).1 ht
  have h2 : ∀ t ∈ T, c⁻¹ * t * c ∈ T := fun t ht =>
    (Subgroup.mem_normalizer_iff.1 hc (c⁻¹ * t * c)).2 (by simpa [mul_assoc] using ht)
  apply le_antisymm
  · rintro _ ⟨t, ht, rfl⟩
    simpa using h1 t ht
  · intro t ht
    refine ⟨c⁻¹ * t * c, h2 t ht, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

theorem isSn_conj [Finite G] {T B : Subgroup G} {n : ℕ} {c : G} (hc : c ∈ normalizer (T : Set G))
    (h : IsSn n T B) : IsSn n T (B.map (MulAut.conj c).toMonoidHom) := by
  have := isSn_map (MulAut.conj c) h
  rwa [map_conj_eq_of_mem_normalizer hc] at this

theorem mem_normalizer_biSup_isSn [Finite G] {T : Subgroup G} {n : ℕ} {a : G}
    (ha : a ∈ normalizer (T : Set G)) :
    a ∈ normalizer ((⨆ B ∈ {B : Subgroup G | IsSn n T B}, B : Subgroup G) : Set G) := by
  have key : ∀ c ∈ normalizer (T : Set G), ∀ x ∈ (⨆ B ∈ {B : Subgroup G | IsSn n T B}, B : Subgroup G),
      c * x * c⁻¹ ∈ (⨆ B ∈ {B : Subgroup G | IsSn n T B}, B : Subgroup G) := by
    intro c hc
    refine conj_mem_biSup (p := fun B => B ∈ {B : Subgroup G | IsSn n T B}) (F := fun B => B) c
      fun B hB => ?_
    exact ⟨B.map (MulAut.conj c).toMonoidHom, isSn_conj hc hB, fun x hx => ⟨x, hx, by simp [MulAut.conj_apply]⟩⟩
  exact mem_normalizer_of_conj_mem (key a ha) (key a⁻¹ (inv_mem ha))

end Transport

section Row3b

variable {G : Type} [Group G]

theorem mem_normalizer_Tstar_r3b {x : G} {K T S : Subgroup G} {a : G} (ha : a ∈ S) :
    a ∈ normalizer ((Th2Row.r3b.Tstar x K T S : Subgroup G) : Set G) := by
  have key : ∀ c ∈ S, ∀ y ∈ Th2Row.r3b.Tstar x K T S, c * y * c⁻¹ ∈ Th2Row.r3b.Tstar x K T S := by
    intro c hc
    refine conj_mem_biSup (p := fun B => B ∈ Th2Row.r3b.BT x K T S) (F := fun B => B) c fun B hB => ⟨B, hB, ?_⟩
    obtain ⟨D, hD, rfl⟩ := hB
    refine conj_mem_biSup (p := fun s => s ∈ S) (F := fun s => D.map (MulAut.conj s).toMonoidHom) c
      fun s hs => ⟨c * s, S.mul_mem hc hs, fun y hy => ?_⟩
    obtain ⟨d, hd, rfl⟩ := hy
    exact ⟨d, hd, by simp [MulAut.conj_apply, mul_assoc]⟩
  exact mem_normalizer_of_conj_mem (key a ha) (key a⁻¹ (S.inv_mem ha))

end Row3b

section Rank

variable {G : Type} [Group G] [Finite G]

theorem le_pRank_Tstar {ρ : Th2Row} {x : G} {K T S B : Subgroup G} (hB : B ∈ ρ.BT x K T S) {k : ℕ}
    (hk : k ≤ pRank 2 ↥B) : k ≤ pRank 2 ↥(ρ.Tstar x K T S) :=
  hk.trans (CFSG.GH74.GLS.C3.Layer1.Back.pRank_mono'
    (le_iSup₂ (f := fun (B : Subgroup G) (_ : B ∈ ρ.BT x K T S) => B) B hB))

end Rank

end CFSG.GH74.GLS.Th2Tstar

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools

theorem tstar_of_facts : B_thm2_tstar := by
  intro G _ _ _ x y K T S M ρ B h hQ4 hK hTS
  have hrow := h.row
  have hmem := h.mem
  have hE := h.isE
  have hL2 : ∀ P : ℕ → Prop, (∀ q, P q → Odd q) → HasL2Model (kBar K) P → P 5 := by
    intro P hP hh
    rcases hK with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact Th2Tstar.hasL2Model_alt5 hP e hh
    · exact (Th2Tstar.not_hasL2Model_alt7 hP e hh).elim
  have hcard : Nat.card (kBar K) < 20160 := by
    rcases hK with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      norm_num [Nat.card_eq_fintype_card, Nat.factorial]
    · rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      norm_num [Nat.card_eq_fintype_card, Nat.factorial]
  have hrk : pRank 2 ↥(T ⊓ CxK x K) ≤ 2 := Th2Tstar.pRank_le_two_of_card_four hQ4
  cases ρ with
  | r1a =>
    obtain ⟨h1, -, -⟩ := hrow
    exact absurd Th2Tstar.isFM9_five (hL2 (fun q => Odd q ∧ ¬ IsFM9 q) (fun q hq => hq.1) h1).2
  | r1b =>
    obtain ⟨h1, -⟩ := hrow
    exact absurd Th2Tstar.isFM9_five (hL2 (fun q => Odd q ∧ ¬ IsFM9 q) (fun q hq => hq.1) h1).2
  | r2 =>
    exact absurd rfl (hL2 (fun q => Odd q ∧ IsFM9 q ∧ q ≠ 5) (fun q hq => hq.1) hrow).2.2
  | r3a =>
    obtain ⟨-, -, h3⟩ := hrow
    omega
  | r3b =>
    have h4 : 4 ≤ pRank 2 ↥B := hE.2.2
    exact ⟨Th2Tstar.le_pRank_Tstar hmem h4, fun a haS _ => Th2Tstar.mem_normalizer_Tstar_r3b haS⟩
  | r3c =>
    obtain ⟨-, -, h3⟩ := hrow
    rcases h3 with h3 | h3
    · omega
    · exact absurd h3 hTS.ne
  | r4a =>
    obtain ⟨-, h3⟩ := hrow
    omega
  | r4b =>
    have hmem' : IsSn 4 T B := hmem
    exact ⟨Th2Tstar.le_pRank_Tstar hmem hmem'.2, fun a _ ha =>
      Th2Tstar.mem_normalizer_biSup_isSn (n := 4) (T := T) ha⟩
  | r4c =>
    have hmem' : IsSn 4 T B := hmem
    exact ⟨Th2Tstar.le_pRank_Tstar hmem hmem'.2, fun a _ ha =>
      Th2Tstar.mem_normalizer_biSup_isSn (n := 4) (T := T) ha⟩
  | r5 =>
    obtain ⟨h1, -, -⟩ := hrow
    exact absurd h1 (Th2Tstar.not_isL34Quotient_of_card_lt hcard)

end CFSG.GH74.GLS
