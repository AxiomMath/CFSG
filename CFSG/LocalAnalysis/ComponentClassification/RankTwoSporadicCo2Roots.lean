module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCheck

public section

namespace CFSG.ComponentClassification.RankTwoSporadic

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.RankTwoSporadic.Cert

variable {W : Type*} [Group W]

theorem monoW_map_conj_iff {X : Subgroup W} (hX : X.Normal) (pw : Bool) (E : Subgroup W)
    (w : W) : MonoW X pw (E.map (MulAut.conj w).toMonoidHom) ↔ MonoW X pw E := by
  set σ := (MulAut.conj w).toMonoidHom
  have hσ : Function.Injective σ := (MulAut.conj w).injective
  have hXσ : X.map σ = X := map_conj_eq_of_normal hX w
  unfold MonoW
  constructor
  · rintro (⟨v, hv, h4⟩ | ⟨hpw, hP⟩)
    · left
      rw [← hXσ, ← map_nE σ hσ] at hv
      obtain ⟨u, hu, rfl⟩ := hv
      exact ⟨u, hu, by rwa [orderOf_injective σ hσ] at h4⟩
    · right
      rw [← hXσ] at hP
      exact ⟨hpw, (pWitness_map_iff σ hσ X E).mp hP⟩
  · rintro (⟨v, hv, h4⟩ | ⟨hpw, hP⟩)
    · left
      refine ⟨σ v, ?_, by rwa [orderOf_injective σ hσ]⟩
      rw [← hXσ, ← map_nE σ hσ]
      exact ⟨v, hv, rfl⟩
    · right
      rw [← hXσ]
      exact ⟨hpw, (pWitness_map_iff σ hσ X E).mpr hP⟩

theorem monoW_mono {X E₀ E : Subgroup W} {pw : Bool} (h : E₀ ≤ E) (hE : MonoW X pw E₀) :
    MonoW X pw E := by
  rcases hE with ⟨w, hw, h4⟩ | ⟨hpw, hP⟩
  · exact Or.inl ⟨w, nE_mono X h hw, h4⟩
  · exact Or.inr ⟨hpw, pWitness_of_le h hP⟩

theorem exists_ne_of_four_le {E : Subgroup W} (hE4 : 4 ≤ Nat.card E) (a : W) :
    ∃ y ∈ E, y ≠ 1 ∧ y ≠ a := by
  by_contra hcon
  push Not at hcon
  have hsub : (E : Set W) ⊆ {1, a} := fun y hy => by
    by_cases h1 : y = 1
    · exact Or.inl h1
    · exact Or.inr (hcon y hy h1)
  have hle : Nat.card E ≤ 2 := by
    have hE : Nat.card E = (E : Set W).ncard := (Nat.card_coe_set_eq _).symm
    rw [hE]
    calc (E : Set W).ncard ≤ ({1, a} : Set W).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ ({a} : Set W).ncard + 1 := Set.ncard_insert_le 1 {a}
      _ = 2 := by rw [Set.ncard_singleton]
  omega

variable [Finite W]

theorem exists_conj_pair {x : W} {T : Subgroup W} (hT : IsSylowOf 2 T (centralizer {x}))
    {E : Subgroup W} (hE : IsElemAbelian 2 E) {a y : W} (haE : a ∈ E) (hyE : y ∈ E)
    (hai : IsConj a x) : ∃ h : W, h * a * h⁻¹ = x ∧ h * y * h⁻¹ ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := isConj_iff.mp hai
  set V := closure ({a, y} : Set W) with hV
  have hVE : V ≤ E := by
    rw [hV, closure_le]
    rintro z (rfl | rfl)
    · exact haE
    · exact hyE
  set σ := (MulAut.conj g).toMonoidHom
  have hV'C : V.map σ ≤ centralizer {x} := by
    rintro _ ⟨v, hv, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hva : v * a = a * v := congrArg Subtype.val (hE.1.is_comm.comm ⟨v, hVE hv⟩ ⟨a, haE⟩)
    simp only [σ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hg]
    calc g * v * g⁻¹ * (g * a * g⁻¹) = g * (v * a) * g⁻¹ := by group
      _ = g * (a * v) * g⁻¹ := by rw [hva]
      _ = g * a * g⁻¹ * (g * v * g⁻¹) := by group
  have hV'2 : IsPGroup 2 (V.map σ) := ((isPGroup_of_isElemAbelian hE).to_le hVE).map σ
  obtain ⟨m, hmC, hm⟩ := exists_conj_le_of_isSylowOf hT hV'2 hV'C
  have hmx : m * x = x * m := mem_centralizer_singleton_iff.mp hmC
  refine ⟨m⁻¹ * g, ?_, ?_⟩
  · calc m⁻¹ * g * a * (m⁻¹ * g)⁻¹ = m⁻¹ * (g * a * g⁻¹) * m := by group
      _ = m⁻¹ * (x * m) := by rw [hg, mul_assoc]
      _ = x := by rw [← hmx]; group
  · have := hm (g * y * g⁻¹) ⟨y, subset_closure (Or.inr rfl), rfl⟩
    convert this using 1
    group

omit [Finite W] in
theorem conj_ne_of_ne {a y h x : W} (hxa : h * a * h⁻¹ = x) (hy1 : y ≠ 1) (hya : y ≠ a) :
    h * y * h⁻¹ ≠ 1 ∧ h * y * h⁻¹ ≠ x := by
  refine ⟨fun h1 => hy1 ?_, fun h1 => hya ?_⟩
  · have := congrArg (fun z => h⁻¹ * z * h) h1
    simpa [mul_assoc] using this
  · rw [← hxa] at h1
    have := congrArg (fun z => h⁻¹ * z * h) h1
    simpa [mul_assoc] using this

theorem monoW_of_roots {X : Subgroup W} (hX : X.Normal) {pw : Bool} {Y : Subgroup W}
    (hY : Y.Normal) {k : ℕ} (x : ℕ → W)
    (T : ℕ → Subgroup W) (hT : ∀ i < k, IsSylowOf 2 (T i) (centralizer {x i}))
    (hw : ∀ i < k, ∀ b ∈ T i, b ^ 2 = 1 → b ≠ 1 → b ≠ x i → b ∈ Y →
      MonoW X pw (closure {x i, b}) ∨ ∃ j < i, IsConj b (x j) ∨ IsConj (x i * b) (x j)) :
    ∀ i < k, ∀ {E : Subgroup W}, IsElemAbelian 2 E → E ≤ Y → 4 ≤ Nat.card E → ∀ {a : W},
      a ∈ E → IsConj a (x i) → MonoW X pw E := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro hik E hE hEY hE4 a haE hai
  obtain ⟨y, hyE, hy1, hya⟩ := exists_ne_of_four_le hE4 a
  obtain ⟨h, hxa, hbT⟩ := exists_conj_pair (hT i hik) hE haE hyE hai
  obtain ⟨hb1, hbx⟩ := conj_ne_of_ne hxa hy1 hya
  have hb2 : (h * y * h⁻¹) ^ 2 = 1 := by rw [conj_pow, hE.2 y hyE, mul_one, mul_inv_cancel]
  rcases hw i hik _ hbT hb2 hb1 hbx (hY.conj_mem y (hEY hyE) h) with hM | ⟨j, hji, hj | hj⟩
  · have hmap : closure ({x i, h * y * h⁻¹} : Set W) =
        (closure ({a, y} : Set W)).map (MulAut.conj h).toMonoidHom := by
      rw [MonoidHom.map_closure, Set.image_pair]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hxa]
    rw [hmap, monoW_map_conj_iff hX] at hM
    refine monoW_mono ?_ hM
    rw [closure_le]
    rintro z (rfl | rfl)
    · exact haE
    · exact hyE
  ·
    exact ih j hji (hji.trans hik) hE hEY hE4 hyE ((isConj_iff.mpr ⟨h, rfl⟩).trans hj)
  ·
    refine ih j hji (hji.trans hik) hE hEY hE4 (E.mul_mem haE hyE) ?_
    refine (isConj_iff.mpr ⟨h, ?_⟩).trans hj
    rw [← hxa]
    group

theorem exists_mem_of_index_le_two {X E : Subgroup W} (hXi : X.index ≤ 2)
    (hE4 : 4 ≤ Nat.card E) : ∃ a ∈ E, a ≠ 1 ∧ a ∈ X := by
  have hidx : (X.subgroupOf E).index ≤ 2 := by
    have h := Subgroup.relIndex_le_of_le_right (H := X) (le_top : E ≤ ⊤)
      (by rw [relIndex_top_right]; exact index_ne_zero_of_finite)
    rw [relIndex_top_right] at h
    exact h.trans hXi
  have hmul := (X.subgroupOf E).card_mul_index
  have hcard : 2 ≤ Nat.card (X.subgroupOf E) := by
    by_contra hlt
    push Not at hlt
    have : Nat.card E ≤ 2 := by
      rw [← hmul]
      calc Nat.card (X.subgroupOf E) * (X.subgroupOf E).index ≤ 1 * 2 :=
            Nat.mul_le_mul (by omega) hidx
        _ = 2 := by norm_num
    omega
  have hne : X.subgroupOf E ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot _).mp (by omega)
  obtain ⟨⟨⟨a, haE⟩, haX⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  refine ⟨a, haE, fun h1 => ha1 (Subtype.ext (Subtype.ext h1)), ?_⟩
  rwa [mem_subgroupOf] at haX

theorem yCensus17_of_roots {X : Subgroup W} (hX : X.Normal) (hXi : X.index ≤ 2) {k : ℕ}
    (x : ℕ → W) (T : ℕ → Subgroup W) (hT : ∀ i < k, IsSylowOf 2 (T i) (centralizer {x i}))
    (hcls : ∀ a ∈ X, a ^ 2 = 1 → a ≠ 1 → ∃ i < k, IsConj a (x i))
    (hw : ∀ i < k, ∀ b ∈ T i, b ^ 2 = 1 → b ≠ 1 → b ≠ x i →
      MonoW X true (closure {x i, b}) ∨ ∃ j < i, IsConj b (x j) ∨ IsConj (x i * b) (x j)) :
    YCensus17 X (fun _ => False) := by
  intro E hE hE4 _
  obtain ⟨a, haE, ha1, haX⟩ := exists_mem_of_index_le_two hXi hE4
  obtain ⟨i, hik, hai⟩ := hcls a haX (hE.2 a haE) ha1
  rcases monoW_of_roots hX (normal_top (G := W)) x T hT
      (fun i hi b hb hb2 hb1 hbx _ => hw i hi b hb hb2 hb1 hbx) i hik hE le_top hE4 haE hai
    with h | ⟨-, h⟩
  · exact Or.inl (Or.inl h)
  · exact Or.inr h

theorem yCensusII_of_innerRoots {X : Subgroup W} (hX : X.Normal) (hXi : X.index ≤ 2) {k : ℕ}
    (x : ℕ → W) (T : ℕ → Subgroup W) (hT : ∀ i < k, IsSylowOf 2 (T i) (centralizer {x i}))
    (hcls : ∀ a ∈ X, a ^ 2 = 1 → a ≠ 1 → ∃ i < k, IsConj a (x i))
    (hw : ∀ i < k, ∀ b ∈ T i, b ^ 2 = 1 → b ∉ X → MonoW X false (closure {x i, b})) :
    YCensus X (· ≤ X) := by
  intro E hE hE4 hEX
  obtain ⟨y, hyE, hyX⟩ : ∃ y ∈ E, y ∉ X := by
    by_contra hcon
    push Not at hcon
    exact hEX hcon
  obtain ⟨a, haE, ha1, haX⟩ := exists_mem_of_index_le_two hXi hE4
  obtain ⟨i, hik, hai⟩ := hcls a haX (hE.2 a haE) ha1
  obtain ⟨h, hxa, hbT⟩ := exists_conj_pair (hT i hik) hE haE hyE hai
  have hb2 : (h * y * h⁻¹) ^ 2 = 1 := by rw [conj_pow, hE.2 y hyE, mul_one, mul_inv_cancel]
  have hbX : h * y * h⁻¹ ∉ X := fun hb => hyX (by
    have := hX.conj_mem _ hb h⁻¹
    simpa [mul_assoc] using this)
  have hM := hw i hik _ hbT hb2 hbX
  have hmap : closure ({x i, h * y * h⁻¹} : Set W) =
      (closure ({a, y} : Set W)).map (MulAut.conj h).toMonoidHom := by
    rw [MonoidHom.map_closure, Set.image_pair]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hxa]
  rw [hmap, monoW_map_conj_iff hX] at hM
  have hle : closure ({a, y} : Set W) ≤ E := by
    rw [closure_le]
    rintro z (rfl | rfl)
    · exact haE
    · exact hyE
  rcases monoW_mono hle hM with h | ⟨h, -⟩
  · exact Or.inl h
  · exact absurd h (by decide)

theorem yCensus17_of_innerRoots {X : Subgroup W} (hX : X.Normal) (hXi : X.index ≤ 2) {k : ℕ}
    (x : ℕ → W) (T : ℕ → Subgroup W) (hT : ∀ i < k, IsSylowOf 2 (T i) (centralizer {x i}))
    (hII : YCensus X (· ≤ X))
    (hcls : ∀ a ∈ X, a ^ 2 = 1 → a ≠ 1 → ∃ i < k, IsConj a (x i))
    (hw : ∀ i < k, ∀ b ∈ T i, b ^ 2 = 1 → b ≠ 1 → b ≠ x i → b ∈ X →
      MonoW X true (closure {x i, b}) ∨ ∃ j < i, IsConj b (x j) ∨ IsConj (x i * b) (x j)) :
    YCensus17 X (fun _ => False) := by
  intro E hE hE4 _
  by_cases hEX : E ≤ X
  · obtain ⟨a, haE, ha1, -⟩ := exists_mem_of_index_le_two hXi hE4
    obtain ⟨i, hik, hai⟩ := hcls a (hEX haE) (hE.2 a haE) ha1
    rcases monoW_of_roots hX hX x T hT hw i hik hE hEX hE4 haE hai with h | ⟨-, h⟩
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
  · exact Or.inl (hII E hE hE4 hEX)

end CFSG.ComponentClassification.RankTwoSporadic
