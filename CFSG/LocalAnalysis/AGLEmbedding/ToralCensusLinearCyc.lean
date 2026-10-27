module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinearCycPair
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinearBlocks

public section

namespace CFSG.AGLEmbedding

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.RankThree.CALinearPlane
open CFSG.AGLEmbedding.ParabPrime (perfectJoin le_perfectJoin)

namespace ToralCensus

variable {K : Type*} [Field K] {n : ℕ}

@[expose] def intervalCoords (n a b : ℕ) (hb : b ≤ n) : Finset (Fin n) :=
  (Finset.Ico a b).attachFin fun m hm => by rw [Finset.mem_Ico] at hm; omega

theorem mem_intervalCoords {a b : ℕ} {hb : b ≤ n} {i : Fin n} :
    i ∈ intervalCoords n a b hb ↔ a ≤ (i : ℕ) ∧ (i : ℕ) < b := by
  rw [intervalCoords, Finset.mem_attachFin, Finset.mem_Ico]

theorem card_intervalCoords {a b : ℕ} {hb : b ≤ n} : (intervalCoords n a b hb).card = b - a := by
  rw [intervalCoords, Finset.card_attachFin, Nat.card_Ico]

theorem coordBlockSL_le_flagStabilizer {I : Set ℕ} {a b : ℕ} (h : IsConsecutiveCut n I a b) :
    coordBlockSL K (intervalCoords n a b h.2.1) ≤ flagStabilizer n K I := by
  intro g hg
  rw [mem_coordBlockSL_iff] at hg
  rw [mem_flagStabilizer]
  intro d hd
  refine mem_stabilizer_of_map_le ?_
  rintro _ ⟨v, hv, rfl⟩
  rw [mulVecLin_apply, mem_flagSpace]
  intro k hk
  have hv := mem_flagSpace.mp hv
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hkJ : k ∈ intervalCoords n a b h.2.1
  · have hk' := mem_intervalCoords.mp hkJ
    have hda : d ≤ a := by have := h.2.2.2.2 d hd; omega
    by_cases hjJ : j ∈ intervalCoords n a b h.2.1
    · rw [hv j (by have := mem_intervalCoords.mp hjJ; omega), mul_zero]
    · have hkj : k ≠ j := fun e => hjJ (e ▸ hkJ)
      rw [hg k j (Or.inr hjJ)]
      simp [hkj]
  · rw [hg k j (Or.inl hkJ)]
    split_ifs with e
    · rw [← e, hv k hk, mul_zero]
    · rw [zero_mul]

theorem coordBlockSL_mono {J₁ J : Finset (Fin n)} (h : J₁ ⊆ J) :
    coordBlockSL K J₁ ≤ coordBlockSL K J := fun _ hg =>
  mem_coordBlockSL_iff.mpr fun i j hij =>
    mem_coordBlockSL_iff.mp hg i j (hij.imp (fun hi h' => hi (h h')) fun hj h' => hj (h h'))

theorem coordBlockSL_commutator_eq [Finite K] {J : Finset (Fin n)}
    (h : 3 ≤ J.card ∨ (J.card = 2 ∧ 4 ≤ Nat.card K)) :
    ⁅coordBlockSL K J, coordBlockSL K J⁆ = coordBlockSL K J := by
  have : Group.IsPerfect (SpecialLinearGroup (Fin J.card) K) := by
    refine CFSG.LinearGroups.special_linear_isPerfect (by omega) ?_
    rcases h with h | ⟨-, h4⟩
    · exact Or.inl h
    · have : Fintype K := Fintype.ofFinite K
      obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
        (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4)
      exact Or.inr ⟨s, hs⟩
  rw [← range_blockSLOn, MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
    Group.IsPerfect.commutator_eq_top]

theorem coordBlockSL_le_perfectJoin [Finite K] {I : Set ℕ} {a b : ℕ}
    (h : IsConsecutiveCut n I a b) (hs : 3 ≤ b - a ∨ (b - a = 2 ∧ 4 ≤ Nat.card K)) :
    coordBlockSL K (intervalCoords n a b h.2.1) ≤ perfectJoin (flagStabilizer n K I) :=
  le_perfectJoin (coordBlockSL_le_flagStabilizer h)
    (coordBlockSL_commutator_eq (by rw [card_intervalCoords]; exact hs))

theorem not_isCyclic_map_of_inf_center_eq_bot {G H : Type*} [Group G] [Group H] (ρ : G →* H)
    (hker : ρ.ker ≤ Subgroup.center G) {Q : Subgroup G} (hQ : Q ⊓ Subgroup.center G = ⊥)
    (hc : ¬ IsCyclic Q) : ¬ IsCyclic (Q.map ρ) := by
  intro hcyc
  have hinj : Function.Injective (ρ.comp Q.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hx1 : (x : G) ∈ Q ⊓ Subgroup.center G := ⟨x.2, hker hx⟩
    rw [hQ, Subgroup.mem_bot] at hx1
    exact Subtype.ext hx1
  have hrange : (ρ.comp Q.subtype).range = Q.map ρ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have e : Q ≃* Q.map ρ := (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  exact hc (isCyclic_of_surjective e.symm e.symm.surjective)

end ToralCensus

open ToralCensus CFSG.LocalAnalysis.ComponentInitial.LinearCover in
open ToralCensus in
theorem cycBlocksSL_holds :
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ) (I : Set ℕ) (p : ℕ), p.Prime →
      ((∃ a b a' b' : ℕ, IsConsecutiveCut n I a b ∧ IsConsecutiveCut n I a' b' ∧ b ≤ a' ∧
          (3 ≤ b - a ∨ (b - a = 2 ∧ 4 ≤ Nat.card K)) ∧
          (3 ≤ b' - a' ∨ (b' - a' = 2 ∧ 4 ≤ Nat.card K)) ∧
          p ∣ Nat.card (Matrix.SpecialLinearGroup (Fin (b - a)) K) ∧
          p ∣ Nat.card (Matrix.SpecialLinearGroup (Fin (b' - a')) K)) ∨
        (∃ a b : ℕ, IsConsecutiveCut n I a b ∧ 3 ≤ b - a ∧ b - a < n ∧ p ∣ Nat.card K - 1) ∨
        (∃ a b d : ℕ, IsConsecutiveCut n I a b ∧ 1 ≤ d ∧ 2 * d ≤ b - a ∧
          p ∣ Nat.card K ^ d - 1 ∧ ¬ p ∣ Nat.card K - 1)) →
      ∃ Q : Subgroup (Matrix.SpecialLinearGroup (Fin n) K),
        Q ≤ perfectJoin (LinearFlag.flagStabilizer n K I) ∧ IsPGroup p Q ∧
          Q ⊓ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) = ⊥ ∧ ¬ IsCyclic Q := by
  intro K _ _ _ n I p hp hcase
  rcases hcase with ⟨a, b, a', b', h, h', hbb, hs, hs', hd, hd'⟩ | ⟨a, b, h, h3, hlt, hdvd⟩ |
      ⟨a, b, d, h, hd1, h2d, hdvd, hndvd⟩
  ·
    have hc₁ : (intervalCoords n a b h.2.1).card = b - a := card_intervalCoords
    have hc₂ : (intervalCoords n a' b' h'.2.1).card = b' - a' := card_intervalCoords
    have hdisj : Disjoint (intervalCoords n a b h.2.1) (intervalCoords n a' b' h'.2.1) :=
      Finset.disjoint_left.mpr fun i hi₁ hi₂ => by
        rw [mem_intervalCoords] at hi₁ hi₂
        omega
    obtain ⟨s₁, hs₁p, hs₁z⟩ := exists_noncentral_of_dvd_card
      (m := (intervalCoords n a b h.2.1).card) (by rw [hc₁]; omega) hp (by rw [hc₁]; exact hd)
    obtain ⟨s₂, hs₂p, hs₂z⟩ := exists_noncentral_of_dvd_card
      (m := (intervalCoords n a' b' h'.2.1).card) (by rw [hc₂]; omega) hp
      (by rw [hc₂]; exact hd')
    obtain ⟨hpg, hinf, hcyc⟩ := exists_noncyclic_of_blocks hp hdisj hs₁p hs₂p hs₁z hs₂z
    refine ⟨_, ?_, hpg, hinf, hcyc⟩
    rw [Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact coordBlockSL_le_perfectJoin h hs ((range_blockSLOn _).le ⟨s₁, rfl⟩)
    · exact coordBlockSL_le_perfectJoin h' hs' ((range_blockSLOn _).le ⟨s₂, rfl⟩)
  ·
    have hbn := h.2.1
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p
      (by rw [Nat.card_units]; exact hdvd)
    have hωp : (u : K) ^ p = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one, Units.val_one]
    have hω1 : (u : K) ≠ 1 := fun h1 => by
      rw [Units.val_eq_one.mp h1, orderOf_one] at hu
      exact hp.one_lt.ne hu
    obtain ⟨c, hc⟩ : ∃ c : Fin n, (c : ℕ) < a ∨ b ≤ (c : ℕ) := by
      by_cases ha : 1 ≤ a
      · exact ⟨⟨0, by omega⟩, Or.inl (by simp only; omega)⟩
      · exact ⟨⟨n - 1, by omega⟩, Or.inr (by simp only; omega)⟩
    have hne : ∀ {i j : Fin n}, (i : ℕ) ≠ (j : ℕ) → i ≠ j := fun h e => h (congrArg _ e)
    obtain ⟨x, y, hx, hy, hpg, hinf, hcyc⟩ := exists_noncyclic_of_diag
      (a₀ := ⟨a, by omega⟩) (a₁ := ⟨a + 1, by omega⟩) (a₂ := ⟨a + 2, by omega⟩) (c := c)
      hp hω1 hωp (hne (by simp)) (hne (by simp)) (hne (by simp)) (hne (by simp; omega))
      (hne (by simp; omega)) (hne (by simp; omega))
    refine ⟨_, ?_, hpg, hinf, hcyc⟩
    rw [Subgroup.closure_le]
    have hmem : ∀ (g : SpecialLinearGroup (Fin n) K) (i₀ i₁ : Fin n),
        (g : Matrix (Fin n) (Fin n) K) = diagonal (corootVec i₀ i₁ (u : K)) →
        i₀ ∈ intervalCoords n a b hbn → i₁ ∈ intervalCoords n a b hbn →
        g ∈ perfectJoin (flagStabilizer n K I) := by
      intro g i₀ i₁ hg h₀ h₁
      refine coordBlockSL_le_perfectJoin h (Or.inl h3) (mem_coordBlockSL_iff.mpr ?_)
      intro i j hij
      rw [hg, diagonal_apply]
      split_ifs with e
      · subst e
        have hi : i ∉ intervalCoords n a b hbn := hij.elim id id
        have hi₀ : i ≠ i₀ := fun e => hi (e ▸ h₀)
        have hi₁ : i ≠ i₁ := fun e => hi (e ▸ h₁)
        exact corootVec_apply_of_ne hi₀ hi₁ _
      · rfl
    rintro g (rfl | rfl)
    · exact hmem _ _ _ hx (mem_intervalCoords.mpr ⟨le_rfl, by simp; omega⟩)
        (mem_intervalCoords.mpr ⟨by simp, by simp; omega⟩)
    · exact hmem _ _ _ hy (mem_intervalCoords.mpr ⟨by simp, by simp; omega⟩)
        (mem_intervalCoords.mpr ⟨by simp, by simp; omega⟩)
  ·
    have hbn := h.2.1
    have hd2 : 2 ≤ d := by
      by_contra hd2
      obtain rfl : d = 1 := by omega
      exact hndvd (by simpa using hdvd)
    have hc₁ : (intervalCoords n a (a + d) (by omega)).card = d := by
      rw [card_intervalCoords]
      omega
    have hc₂ : (intervalCoords n (a + d) (a + 2 * d) (by omega)).card = d := by
      rw [card_intervalCoords]
      omega
    have hdisj : Disjoint (intervalCoords n a (a + d) (by omega))
        (intervalCoords n (a + d) (a + 2 * d) (by omega)) :=
      Finset.disjoint_left.mpr fun i hi₁ hi₂ => by
        rw [mem_intervalCoords] at hi₁ hi₂
        omega
    have hsub : ∀ {c e : ℕ} (hce : a ≤ c) (he : e ≤ b) (hen : e ≤ n),
        intervalCoords n c e hen ⊆ intervalCoords n a b hbn := fun hce he _ i hi => by
      rw [mem_intervalCoords] at hi ⊢
      omega
    obtain ⟨s₁, hs₁p, hs₁z⟩ := exists_noncentral_of_dvd_pow_sub_one
      (d := (intervalCoords n a (a + d) (by omega)).card) (by rw [hc₁]; omega) hp
      (by rw [hc₁]; exact hdvd) hndvd
    obtain ⟨s₂, hs₂p, hs₂z⟩ := exists_noncentral_of_dvd_pow_sub_one
      (d := (intervalCoords n (a + d) (a + 2 * d) (by omega)).card) (by rw [hc₂]; omega) hp
      (by rw [hc₂]; exact hdvd) hndvd
    obtain ⟨hpg, hinf, hcyc⟩ := exists_noncyclic_of_blocks hp hdisj hs₁p hs₂p hs₁z hs₂z
    refine ⟨_, ?_, hpg, hinf, hcyc⟩
    rw [Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact coordBlockSL_le_perfectJoin h (Or.inl (by omega))
        (coordBlockSL_mono (hsub le_rfl (by omega) (by omega))
          ((range_blockSLOn _).le ⟨s₁, rfl⟩))
    · exact coordBlockSL_le_perfectJoin h (Or.inl (by omega))
        (coordBlockSL_mono (hsub (by omega) (by omega) (by omega))
          ((range_blockSLOn _).le ⟨s₂, rfl⟩))

end CFSG.AGLEmbedding
