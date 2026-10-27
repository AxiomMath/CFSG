module

public import CFSG.LocalAnalysis.OddStandard.ThmCO2A8Fix

public section

namespace CFSG.OddStandard.ThmC.O2.A8

open CFSG Subgroup

section Counting

variable {K : Type} [Group K] [Finite K] {A : Type} [Group A] [Finite A]
  {ρ : K →* MulAut A} {V : Sylow 2 K} {Z : Subgroup A}

section CardSylow

theorem cs_card_dvd_card_sub_one {B M : Type*} [Group B] [Finite B] [MulAction B M] [Finite M]
    (m₀ : M) (hm₀ : ∀ b : B, b • m₀ = m₀)
    (hfix : ∀ b : B, b ≠ 1 → ∀ y : M, b • y = y → y = m₀) :
    Nat.card B ∣ Nat.card M - 1 := by
  classical
  let := Fintype.ofFinite B
  let := Fintype.ofFinite M
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group B M
  have h1 : Fintype.card (MulAction.fixedBy M (1 : B)) = Fintype.card M :=
    Fintype.card_congr (Equiv.subtypeUnivEquiv fun y => one_smul B y)
  have h2 : ∀ b ∈ Finset.univ.erase (1 : B), Fintype.card (MulAction.fixedBy M b) = 1 := by
    intro b hb
    have hb1 : b ≠ 1 := Finset.ne_of_mem_erase hb
    rw [Fintype.card_eq_one_iff]
    exact ⟨⟨m₀, hm₀ b⟩, fun ⟨y, hy⟩ => Subtype.ext (hfix b hb1 y hy)⟩
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 1), h1, Finset.sum_congr rfl h2,
    Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    smul_eq_mul, mul_one] at hB
  have hM : 0 < Fintype.card M := Fintype.card_pos_iff.mpr ⟨m₀⟩
  have hBpos : 0 < Fintype.card B := Fintype.card_pos
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have h3 : Fintype.card B ∣ (Fintype.card M - 1) + Fintype.card B := by
    rw [show Fintype.card M - 1 + Fintype.card B = Fintype.card M + (Fintype.card B - 1) by
      omega, hB]
    exact Dvd.intro_left _ rfl
  exact (Nat.dvd_add_left (dvd_refl _)).mp h3

omit [Finite A] in
theorem cs_exists_ne {W : Sylow 2 K} {Z' : Subgroup A} (h : Hyp ρ W Z') :
    ∃ w ∈ (W : Subgroup K), w ≠ 1 := by
  have h1 : 1 < Nat.card (W : Subgroup K) := by rw [h.cardV]; norm_num
  have := Finite.one_lt_card_iff_nontrivial.1 h1
  obtain ⟨⟨w, hw⟩, hw1⟩ := exists_ne (1 : (W : Subgroup K))
  exact ⟨w, hw, fun h' => hw1 (Subtype.ext h')⟩

omit [Finite A] in
theorem cs_fixed_iff {W : Sylow 2 K} {Z' : Subgroup A} (h : Hyp ρ W Z') (a : A) :
    (∀ w ∈ (W : Subgroup K), ρ w a = a) ↔ a ∈ Z' := by
  obtain ⟨w, hw, hw1⟩ := cs_exists_ne h
  refine ⟨fun hall => (h.fix w hw hw1 a).1 (hall w hw), fun ha w' hw' => ?_⟩
  by_cases h1 : w' = 1
  · simp [h1]
  · exact (h.fix w' hw' h1 a).2 ha

theorem cs_eq_of_fixed (h : Hyp ρ V Z) {b : K} (hb : b ∈ (V : Subgroup K)) (hb1 : b ≠ 1)
    {W : Sylow 2 K} (hbW : b • W = W) : W = V := by
  by_contra hne
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K V W
  have hgn : g ∉ normalizer ((V : Subgroup K) : Set K) := fun hgn =>
    hne (hg ▸ Sylow.smul_eq_iff_mem_normalizer.2 hgn)
  have hbN : b ∈ normalizer (W : Set K) := Sylow.smul_eq_iff_mem_normalizer.1 hbW
  have hmem : b ∈ (V : Subgroup K) ⊓ normalizer (W : Set K) := ⟨hb, hbN⟩
  rw [V.isPGroup'.inf_normalizer_sylow W] at hmem
  exact hb1 (h.ti hgn b hb (hg ▸ hmem.2))

theorem cs_dvd (h : Hyp ρ V Z) : 4 ∣ Nat.card (Sylow 2 K) - 1 := by
  have := cs_card_dvd_card_sub_one (B := (V : Subgroup K)) (M := Sylow 2 K) V
    (fun b => Sylow.smul_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer b.2))
    (fun b hb W hW => cs_eq_of_fixed h b.2 (fun h1 => hb (Subtype.ext h1)) hW)
  rwa [h.cardV] at this

open Classical in
noncomputable def csF {K : Type} [Group K] {A : Type} [Group A] [Fintype A]
    (ρ : K →* MulAut A) (W : Subgroup K) : Finset A :=
  Finset.univ.filter fun a => a ≠ 1 ∧ ∀ w ∈ W, ρ w a = a

omit [Finite A] in
theorem cs_card_F [Fintype A] (h : Hyp ρ V Z) (W : Sylow 2 K) :
    (csF ρ (W : Subgroup K)).card = 3 := by
  classical
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq K V W
  have h' := h.conj g
  set Z' := Z.map (ρ g).toMonoidHom with hZ'
  have hF : csF ρ ((g • V : Sylow 2 K) : Subgroup K) =
      (Finset.univ.filter (· ∈ Z')).erase 1 := by
    ext a
    simp only [csF, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
      cs_fixed_iff h']
  have h4 : (Finset.univ.filter (· ∈ Z')).card = 4 := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]; exact h'.cardZ
  rw [hF, Finset.card_erase_of_mem (by simp), h4]

theorem cs_disjoint [Fintype A] (h : Hyp ρ V Z) {W W' : Sylow 2 K} (hne : W ≠ W') :
    Disjoint (csF ρ (W : Subgroup K)) (csF ρ (W' : Subgroup K)) := by
  classical
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq K V W
  obtain ⟨g', rfl⟩ := MulAction.exists_smul_eq K V W'
  rw [Finset.disjoint_left]
  intro a ha ha'
  simp only [csF, Finset.mem_filter, Finset.mem_univ, true_and, cs_fixed_iff (h.conj g),
    cs_fixed_iff (h.conj g')] at ha ha'
  obtain ⟨ha1, z, hz, rfl⟩ := ha
  obtain ⟨-, z', hz', hzz⟩ := ha'
  have hk : g⁻¹ * g' ∉ normalizer ((V : Subgroup K) : Set K) := by
    intro hk
    apply hne
    have h1 : (g⁻¹ * g') • V = V := Sylow.smul_eq_iff_mem_normalizer.2 hk
    calc g • V = g • ((g⁻¹ * g') • V) := by rw [h1]
      _ = g' • V := by rw [smul_smul, mul_inv_cancel_left]
  have h2 : ρ (g⁻¹ * g') z' = z := by
    have : ρ g' z' = ρ g z := hzz
    rw [map_mul, MulAut.mul_apply, this, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel,
      map_one]
    rfl
  have h3 := h.fixer_unique hk hz ⟨z', hz', h2⟩
  apply ha1
  simp [h3]

theorem cs_le_five (h : Hyp ρ V Z) : Nat.card (Sylow 2 K) ≤ 5 := by
  classical
  have := Fintype.ofFinite A
  have := Fintype.ofFinite (Sylow 2 K)
  have hsub : (Finset.univ.biUnion fun W : Sylow 2 K => csF ρ (W : Subgroup K)) ⊆
      Finset.univ.erase (1 : A) := by
    intro a ha
    obtain ⟨W, -, hW⟩ := Finset.mem_biUnion.1 ha
    simp only [csF, Finset.mem_filter, Finset.mem_univ, true_and] at hW
    simpa using hW.1
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_biUnion (fun W _ W' _ hne => cs_disjoint h hne),
    Finset.sum_const_nat (fun W _ => cs_card_F h W), Finset.card_univ,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, h.cardA] at h1
  omega

end CardSylow

theorem Hyp.card_sylow (h : Hyp ρ V Z) : Nat.card (Sylow 2 K) = 5 := by
  have hpos : 0 < Nat.card (Sylow 2 K) := Nat.card_pos
  have hne : Nat.card (Sylow 2 K) ≠ 1 := by
    intro h1
    have := (Nat.card_eq_one_iff_unique.1 h1).1
    exact h.not_normal (Sylow.normal_of_subsingleton V)
  have hdvd := cs_dvd h
  have hle := cs_le_five h
  omega

end Counting

end CFSG.OddStandard.ThmC.O2.A8
