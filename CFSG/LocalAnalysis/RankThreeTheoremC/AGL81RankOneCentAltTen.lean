module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentCited
import all CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupA10Perm
import TauCeti.GroupTheory.Perm.Jordan

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent

namespace AltTen

open Equiv Equiv.Perm Subgroup MulAction Pointwise
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Perm

private def B₀ : Finset (Fin 10) := {0, 1, 2, 3, 4}

private abbrev p₁ : Perm (Fin 10) := (a₁ : Perm (Fin 10))

private abbrev p₂ : Perm (Fin 10) := (a₂ : Perm (Fin 10))

private abbrev pν : Perm (Fin 10) := (ν₂ : Perm (Fin 10))

private theorem card_B₀ : B₀.card = 5 := by decide

private theorem stab_check : ∀ i j : Fin 5, ∀ x : Fin 10, x ∈ B₀ →
    ((a₁ ^ (i : ℕ) * a₂ ^ (j : ℕ) : A10) : Perm (Fin 10)) x ∈ B₀ := by
  decide

private theorem pν_swap : ∀ x : Fin 10, x ∈ B₀ → pν x ∉ B₀ := by
  decide

private theorem pν_surj : ∀ b : Fin 10, b ∈ B₀ → ∃ w : Fin 10, w ∉ B₀ ∧ pν w = b := by
  decide

private theorem p₂_zero : p₂ 0 = 0 := by decide

private theorem p₂_trans : ∀ z w : Fin 10, z ∉ B₀ → w ∉ B₀ → ∃ k : Fin 5, (p₂ ^ (k : ℕ)) z = w := by
  decide

private theorem p₁_reach : ∀ b : Fin 10, b ∈ B₀ → ∃ k : Fin 5, (p₁ ^ (k : ℕ)) 0 = b := by
  decide

private theorem p₁_pow_zero : ∀ j : Fin 10, j ∈ B₀ → (p₁ ^ (j : ℕ)) 0 = j := by
  decide

private theorem p₁_pow_five : p₁ ^ 5 = 1 := by decide

private theorem mem_B₀ (i : Fin 10) : i ∈ B₀ ↔ i.val < 5 := by
  revert i; decide

private theorem p₁_gen {j : Fin 10} (hj : j ∈ B₀) (hj0 : j ≠ 0) :
    ∃ k : ℕ, (p₁ ^ (j : ℕ)) ^ k = p₁ := by
  have h5 : (j : ℕ) < 5 := (mem_B₀ j).1 hj
  have h0 : 0 < (j : ℕ) := Nat.pos_of_ne_zero fun h => hj0 (Fin.ext h)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (j : ℕ) * k % 5 = 1 := by
    generalize (j : ℕ) = m at h5 h0
    interval_cases m
    exacts [⟨1, rfl⟩, ⟨3, rfl⟩, ⟨2, rfl⟩, ⟨4, rfl⟩]
  exact ⟨k, by rw [← pow_mul, pow_eq_pow_mod _ p₁_pow_five, hk, pow_one]⟩

private theorem reach_check : ∀ y : Fin 10, ∃ k : Fin 5,
    (y ∈ B₀ ∧ (p₁ ^ (k : ℕ)) 0 = y) ∨ (y ∉ B₀ ∧ (p₂ ^ (k : ℕ) * pν) 0 = y) := by
  decide

private theorem p₁_isCycle : p₁.IsCycle :=
  List.isCycle_formPerm (l := [0, 1, 2, 3, 4]) (by decide) (by decide)

private theorem p₁_support : p₁.support.card = 5 := by decide

private theorem ν₂_mem' : ν₂ ∈ normalizer (S₀ : Set A10) :=
  mem_normalizer_of_mem_list (by simp)

private theorem stab_S₀ {s : A10} (hs : s ∈ S₀) : ∀ i ∈ B₀, (s : Perm (Fin 10)) i ∈ B₀ := by
  obtain ⟨i, j, rfl⟩ := hs
  intro x hx
  rw [pow_eq_pow_mod i a₁_pow, pow_eq_pow_mod j a₂_pow]
  exact stab_check ⟨i % 5, Nat.mod_lt _ (by norm_num)⟩ ⟨j % 5, Nat.mod_lt _ (by norm_num)⟩ x hx

private theorem block_map {Y' : Subgroup (Perm (Fin 10))} {Δ : Set (Fin 10)}
    (hΔ : IsBlock Y' Δ) {g : Perm (Fin 10)} (hg : g ∈ Y') {a : Fin 10} (ha : a ∈ Δ)
    (hga : g a ∈ Δ) : ∀ z ∈ Δ, g z ∈ Δ := by
  have h : (⟨g, hg⟩ : Y') • Δ = Δ := hΔ.smul_eq_of_mem ha hga
  intro z hz
  rw [← h]
  exact Set.smul_mem_smul_set hz

private theorem pow_map {Δ : Set (Fin 10)} {g : Perm (Fin 10)} (h : ∀ z ∈ Δ, g z ∈ Δ)
    (n : ℕ) : ∀ z ∈ Δ, (g ^ n) z ∈ Δ := by
  induction n with
  | zero => intro z hz; simpa using hz
  | succ n ih => intro z hz; rw [pow_succ, Perm.mul_apply]; exact ih _ (h z hz)

private theorem block_eq_B₀ {Y' : Subgroup (Perm (Fin 10))} (h1 : p₁ ∈ Y') (h2 : p₂ ∈ Y')
    (h3 : pν ∈ Y') {Δ : Set (Fin 10)} (hΔ : IsBlock Y' Δ) (h0 : (0 : Fin 10) ∈ Δ)
    (hnt : ¬ IsTrivialBlock Δ) : Δ = (B₀ : Set (Fin 10)) := by
  have hc₂ : ∀ z ∈ Δ, p₂ z ∈ Δ := block_map hΔ h2 h0 (by rwa [p₂_zero])
  have hne : Δ ≠ Set.univ := fun h => hnt (Or.inr h)
  have hnsub : ¬ Δ.Subsingleton := fun h => hnt (Or.inl h)
  have hsub : ∀ z ∈ Δ, z ∈ B₀ := by
    intro z hz
    by_contra hzB
    have hcompl : ∀ w, w ∉ B₀ → w ∈ Δ := by
      intro w hw
      obtain ⟨k, hk⟩ := p₂_trans z w hzB hw
      rw [← hk]
      exact pow_map hc₂ k z hz
    have hg₀ : ∀ z ∈ Δ, pν z ∈ Δ :=
      block_map hΔ h3 h0 (hcompl _ (pν_swap 0 (by decide)))
    apply hne
    ext y
    simp only [Set.mem_univ, iff_true]
    by_cases hy : y ∈ B₀
    · obtain ⟨w, hw, rfl⟩ := pν_surj y hy
      exact hg₀ w (hcompl w hw)
    · exact hcompl y hy
  obtain ⟨j, hjΔ, hj0⟩ := (Set.not_subsingleton_iff.mp hnsub).exists_ne (0 : Fin 10)
  have hjB : j ∈ B₀ := hsub j hjΔ
  have hcj : ∀ z ∈ Δ, (p₁ ^ (j : ℕ)) z ∈ Δ :=
    block_map hΔ (Y'.pow_mem h1 _) h0 (by rw [p₁_pow_zero j hjB]; exact hjΔ)
  obtain ⟨k, hk⟩ := p₁_gen hjB hj0
  have hc₁ : ∀ z ∈ Δ, p₁ z ∈ Δ := by
    have := pow_map hcj k
    rwa [hk] at this
  ext b
  constructor
  · intro hb
    exact Finset.mem_coe.2 (hsub b hb)
  · intro hb
    obtain ⟨m, hm⟩ := p₁_reach b (Finset.mem_coe.1 hb)
    rw [← hm]
    exact pow_map hc₁ m 0 h0

private theorem isBlock_B₀ (Y : Subgroup A10) (hN : normalizer (S₀ : Set A10) ≤ Y)
    (hY : Y ≠ ⊤) :
    IsBlock (Y.map (alternatingGroup (Fin 10)).subtype) (B₀ : Set (Fin 10)) := by
  set Y' : Subgroup (Perm (Fin 10)) := Y.map (alternatingGroup (Fin 10)).subtype
  have hmem : ∀ y ∈ Y, ((y : A10) : Perm (Fin 10)) ∈ Y' := fun y hy => ⟨y, hy, rfl⟩
  have h1 : p₁ ∈ Y' := hmem a₁ (hN (Subgroup.le_normalizer a₁_mem))
  have h2 : p₂ ∈ Y' := hmem a₂ (hN (Subgroup.le_normalizer a₂_mem))
  have h3 : pν ∈ Y' := hmem ν₂ (hN ν₂_mem')
  have hreach : ∀ y : Fin 10, ∃ g ∈ Y', g 0 = y := by
    intro y
    obtain ⟨k, hk⟩ := reach_check y
    rcases hk with ⟨-, hk⟩ | ⟨-, hk⟩
    · exact ⟨_, Y'.pow_mem h1 k, hk⟩
    · exact ⟨_, Y'.mul_mem (Y'.pow_mem h2 k) h3, hk⟩
  haveI hpt : IsPretransitive Y' (Fin 10) := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨gx, hgx, hx⟩ := hreach x
    obtain ⟨gy, hgy, hy⟩ := hreach y
    refine ⟨⟨gy * gx⁻¹, Y'.mul_mem hgy (Y'.inv_mem hgx)⟩, ?_⟩
    show (gy * gx⁻¹) x = y
    rw [← hx]
    simp [hy]
  by_cases hprim : IsPreprimitive Y' (Fin 10)
  · exfalso
    have halt := TauCeti.alternatingGroup_le_of_isPreprimitive_of_isCycle_mem hprim
      Nat.prime_five (by simp) p₁_isCycle p₁_support h1
    apply hY
    rw [eq_top_iff]
    intro z _
    obtain ⟨y, hy, hyz⟩ := halt z.2
    obtain rfl : y = z := Subtype.ext hyz
    exact hy
  · have hex : ∃ Δ : Set (Fin 10), IsBlock Y' Δ ∧ ¬ IsTrivialBlock Δ := by
      by_contra hcon
      exact hprim { toIsPretransitive := hpt
                    isTrivialBlock_of_isBlock := fun {B} hB =>
                      by_contra fun hB' => hcon ⟨B, hB, hB'⟩ }
    obtain ⟨Δ, hΔ, hnt⟩ := hex
    obtain ⟨x, hx⟩ : Δ.Nonempty := by
      by_contra hemp
      refine hnt (Or.inl ?_)
      rw [Set.not_nonempty_iff_eq_empty.1 hemp]
      exact Set.subsingleton_empty
    obtain ⟨g, hg⟩ := exists_smul_eq Y' x (0 : Fin 10)
    have hΔ' : IsBlock Y' (g • Δ) := hΔ.translate g
    have h0 : (0 : Fin 10) ∈ g • Δ := ⟨x, hx, hg⟩
    have hnt' : ¬ IsTrivialBlock (g • Δ) := fun h => hnt ((IsTrivialBlock.smul_iff g).1 h)
    rw [← block_eq_B₀ h1 h2 h3 hΔ' h0 hnt']
    exact hΔ'

private theorem overgroup_S₀ (Y₀ : Subgroup A10) (hN : normalizer (S₀ : Set A10) ≤ Y₀)
    (hY : Y₀ ≠ ⊤) {y : A10} (hy : y ∈ Y₀) :
    (∀ i ∈ B₀, (y : Perm (Fin 10)) i ∈ B₀) ∨ ∀ i ∈ B₀, (y : Perm (Fin 10)) i ∉ B₀ := by
  have hblock := isBlock_B₀ Y₀ hN hY
  let g : ↥(Y₀.map (alternatingGroup (Fin 10)).subtype) := ⟨(y : Perm (Fin 10)), y, hy, rfl⟩
  rcases isBlock_iff_smul_eq_or_disjoint.1 hblock g with h | h
  · left
    intro i hi
    have hmem : (y : Perm (Fin 10)) i ∈ g • (B₀ : Set (Fin 10)) :=
      Set.smul_mem_smul_set (Finset.mem_coe.2 hi)
    rw [h] at hmem
    exact Finset.mem_coe.1 hmem
  · right
    intro i hi hmem
    have hmem' : (y : Perm (Fin 10)) i ∈ g • (B₀ : Set (Fin 10)) :=
      Set.smul_mem_smul_set (Finset.mem_coe.2 hi)
    exact Set.disjoint_left.1 h hmem' (Finset.mem_coe.2 hmem)

private theorem exists_conj (S : Sylow 5 A10) :
    ∃ x : A10, ∀ s : A10, s ∈ (S : Subgroup A10) ↔ x⁻¹ * s * x ∈ S₀ := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let Q : Sylow 5 A10 := Sylow.ofCard S₀ (by rw [card_S₀, factorization_A10]; norm_num)
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq A10 Q S
  refine ⟨x, fun s => ?_⟩
  have h2 : (S : Subgroup A10) = MulAut.conj x • (Q : Subgroup A10) := by rw [← hx]; rfl
  rw [h2, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp [Q]

private theorem conj_mem_normalizer {S : Subgroup A10} {x : A10}
    (hx : ∀ s : A10, s ∈ S ↔ x⁻¹ * s * x ∈ S₀) {n : A10}
    (hn : n ∈ normalizer (S₀ : Set A10)) : x * n * x⁻¹ ∈ normalizer (S : Set A10) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [hx h, hx, show x⁻¹ * (x * n * x⁻¹ * h * (x * n * x⁻¹)⁻¹) * x = n * (x⁻¹ * h * x) * n⁻¹ by
    group]
  exact Subgroup.mem_normalizer_iff.1 hn (x⁻¹ * h * x)

private theorem holds : KFactAltTenOvergroup := by
  intro S
  obtain ⟨x, hx⟩ := exists_conj S
  refine ⟨B₀.map (x : Perm (Fin 10)).toEmbedding, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_map]
    exact card_B₀
  · intro s hs i hi
    rw [Finset.mem_map_equiv] at hi ⊢
    have h := stab_S₀ ((hx s).1 hs) _ hi
    simpa [Perm.mul_apply] using h
  · refine ⟨x * ν₂ * x⁻¹, conj_mem_normalizer hx ν₂_mem', ?_⟩
    intro i hi
    rw [Finset.mem_map_equiv] at hi ⊢
    have h := pν_swap _ hi
    simpa [Perm.mul_apply] using h
  · intro Y hNY hY y hy
    let Y₀ : Subgroup A10 := Y.comap (MulAut.conj x).toMonoidHom
    have hN₀ : normalizer (S₀ : Set A10) ≤ Y₀ := fun n hn =>
      hNY (conj_mem_normalizer hx hn)
    have hY₀ : Y₀ ≠ ⊤ := by
      intro h
      apply hY
      rw [eq_top_iff]
      intro z _
      have h' : x⁻¹ * z * x ∈ Y₀ := h ▸ Subgroup.mem_top _
      have h'' : x * (x⁻¹ * z * x) * x⁻¹ ∈ Y := h'
      rwa [show x * (x⁻¹ * z * x) * x⁻¹ = z by group] at h''
    have hy₀ : x⁻¹ * y * x ∈ Y₀ := by
      show x * (x⁻¹ * y * x) * x⁻¹ ∈ Y
      rwa [show x * (x⁻¹ * y * x) * x⁻¹ = y by group]
    rcases overgroup_S₀ Y₀ hN₀ hY₀ hy₀ with h | h
    · left
      intro i hi
      rw [Finset.mem_map_equiv] at hi ⊢
      simpa [Perm.mul_apply] using h _ hi
    · right
      intro i hi
      rw [Finset.mem_map_equiv] at hi ⊢
      simpa [Perm.mul_apply] using h _ hi

end AltTen

theorem kFactAltTenOvergroup_holds : KFactAltTenOvergroup := AltTen.holds

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent
