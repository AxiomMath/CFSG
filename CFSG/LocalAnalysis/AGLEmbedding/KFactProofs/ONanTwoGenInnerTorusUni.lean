module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanTwoGenInnerSylowTransfer
public import CFSG.ClassicalGroups.UnitaryFlag.OrderSylow

public section

namespace CFSG.AGLEmbedding.TwoGenInner

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

theorem exists_unit_orderOf_eq {K : Type} [Field K] [Finite K] {f p : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) (hp : p.Prime) (hpq : p ∣ 2 ^ f + 1) :
    ∃ ω : Kˣ, orderOf ω = p := by
  have : Fact p.Prime := ⟨hp⟩
  have hunits : Nat.card Kˣ = Nat.card K - 1 := by
    classical
    have := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_units]
  have hdvd : p ∣ Nat.card Kˣ := by
    rw [hunits, hK]
    have h1 : (2 ^ f) ^ 2 - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
      have := Nat.sq_sub_sq (2 ^ f) 1
      simpa using this
    exact h1 ▸ Dvd.dvd.mul_right hpq _
  exact exists_prime_orderOf_dvd_card' p hdvd

section Torus

variable {K : Type} [Field K] {f p r ε : ℕ}

theorem exists_torus_pElement (h : UnitaryFieldData 2 f K) {ω : Kˣ} (hω : orderOf ω = p)
    (hp : p.Prime) (hp2 : p ≠ 2) (hr : 2 ≤ r) :
    ∃ g ∈ hypTorus h r ε, g ^ p = 1 ∧ g ∉ hypScalars h r ε := by
  classical
  let a : Fin r → Kˣ := fun i => if (i : ℕ) = 0 then ω else if (i : ℕ) = 1 then ω⁻¹ else 1
  let d : Fin ε → Kˣ := fun _ => 1
  have hdn : ∀ k, h.norm ((d k : Kˣ) : K) = 1 := fun k => by simp [d, UnitaryFieldData.norm]
  have hωp : ω ^ p = 1 := hω ▸ pow_orderOf_eq_one ω
  have hap : ∀ i, a i ^ p = 1 := by
    intro i
    simp only [a]
    split_ifs <;> simp [inv_pow, hωp]
  have hωne : (ω : K) ≠ 0 := ω.ne_zero
  have hbne : h.bar (ω : K) ≠ 0 := (map_ne_zero h.bar).2 hωne
  have hratio : torusRatio h a d = 1 := by
    have h0 : (⟨0, by omega⟩ : Fin r) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
    have hprod : ∏ i, ((a i : Kˣ) : K) / h.bar ((a i : Kˣ) : K) = 1 := by
      rw [Finset.prod_eq_mul (⟨0, by omega⟩ : Fin r) ⟨1, by omega⟩ h0]
      · simp [a]
        field_simp
      · intro c _ hc
        have h0' : (c : ℕ) ≠ 0 := fun hh => hc.1 (Fin.ext hh)
        have h1' : (c : ℕ) ≠ 1 := fun hh => hc.2 (Fin.ext hh)
        simp [a, h0', h1']
      · intro hh; exact absurd (Finset.mem_univ _) hh
      · intro hh; exact absurd (Finset.mem_univ _) hh
    simp [torusRatio, hprod, d]
  obtain ⟨g, hgT, hgM⟩ := torusMat_mem_hypSU h a hdn hratio
  refine ⟨g, hgT, ?_, ?_⟩
  · refine Subtype.ext (Units.ext ?_)
    have hpow : torusEntries h a d ^ p = 1 := by
      funext x
      rcases x with i | k | i
      · simp only [torusEntries, Pi.pow_apply, Pi.one_apply]
        rw [← Units.val_pow_eq_pow_val, hap i, Units.val_one]
      · simp [torusEntries, d]
      · simp only [torusEntries, Pi.pow_apply, Pi.one_apply]
        rw [inv_pow, ← map_pow, ← Units.val_pow_eq_pow_val, hap i, Units.val_one, map_one,
          inv_one]
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hgM, Matrix.diagonal_pow, hpow]
    ext i j
    simp [Matrix.diagonal_apply, Matrix.one_apply]
  · intro hZ
    obtain ⟨c, -, -, hc⟩ := mem_normOneScalars.1 hZ
    have hmat : (Matrix.diagonal (torusEntries h a d) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
        Matrix.scalar (HypIndex r ε) (c : K) := by
      rw [← hgM, hc, Matrix.GeneralLinearGroup.coe_scalar]
    have e0 := congrFun (congrFun hmat (Sum.inl ⟨0, by omega⟩)) (Sum.inl ⟨0, by omega⟩)
    have e1 := congrFun (congrFun hmat (Sum.inl ⟨1, by omega⟩)) (Sum.inl ⟨1, by omega⟩)
    simp [torusEntries, a, Matrix.scalar_apply] at e0 e1
    have h3 : (ω : K)⁻¹ = ω := e1.trans e0.symm
    have h2 : (ω : K) ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 2 [← h3]
      exact mul_inv_cancel₀ hωne
    have hsq : ω ^ 2 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, h2, Units.val_one])
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
      (hω ▸ orderOf_dvd_of_pow_eq_one hsq))

end Torus

theorem exists_normalizer_element {K : Type} [Field K] {f p r ε : ℕ} (h : UnitaryFieldData 2 f K)
    (hε : ε ≤ 1) {ω : Kˣ} (hω : orderOf ω = p) (hp : p.Prime) (hp2 : p ≠ 2) (hr : 2 ≤ r) :
    ∃ a : hypPSU h r ε, orderOf a = p ∧
      a ∈ Subgroup.normalizer ((hypProjUnitriangular h r ε : Subgroup (hypPSU h r ε)) :
        Set (hypPSU h r ε)) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hgT, hgp, hgZ⟩ := exists_torus_pElement (ε := ε) h hω hp hp2 hr
  have hgB : g ∈ hypBorel h r ε := hypTorus_le_hypBorel h hgT
  have hBN : hypBorel h r ε ≤ Subgroup.normalizer ((hypUnitriangular h r ε : Subgroup _) : Set _) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hypUnitriangular_le_hypBorel h)).1
      (normal_hypUnitriangular hε)
  refine ⟨hypProj h r ε g, orderOf_eq_prime ?_ ?_, ?_⟩
  · rw [← map_pow, hgp, map_one]
  · intro h1
    exact hgZ (by rw [← ker_hypProj h r ε]; exact h1)
  · exact Subgroup.le_normalizer_map (hypProj h r ε) (Subgroup.mem_map_of_mem _ (hBN hgB))

abbrev UniModel (n f : ℕ) (K : Type) [Field K] : Type := StatedProj (StatedSU n (2 ^ f) K)

theorem torusUni_model {K : Type} [Field K] [Finite K] {f n p : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ 2 ^ f + 1) (hn : 5 ≤ n) (Q : Sylow 2 (UniModel n f K)) :
    p ∣ Nat.card ↥(Subgroup.normalizer (Q : Set (UniModel n f K))) := by
  have hp2 : p ≠ 2 := by omega
  have h : UnitaryFieldData 2 f K := ⟨Nat.prime_two, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨ω, hω⟩ := exists_unit_orderOf_eq hK hp hpq
  obtain ⟨r, ε, hε, rfl⟩ : ∃ r ε, ε ≤ 1 ∧ n = 2 * r + ε := ⟨n / 2, n % 2, by omega, by omega⟩
  have hr : 2 ≤ r := by omega
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := r) (ε := ε) h
  let Φ : hypPSU h r ε ≃* UniModel (2 * r + ε) f K :=
    hypPSUEquivStatedProj h hR (by omega : 1 ≤ 2 * r + ε)
  obtain ⟨a, hao, haN⟩ := exists_normalizer_element h hε hω hp hp2 hr
  obtain ⟨PU, hPU⟩ := (unitary_order_and_Sylow h (by omega : 1 ≤ r) hε).2.2.2.2.1
  let Q₀ : Sylow 2 (UniModel (2 * r + ε) f K) :=
    Sylow.mapSurjective (f := Φ.toMonoidHom) Φ.surjective PU
  have hQ₀ : p ∣ Nat.card ↥(Subgroup.normalizer (Q₀ : Set (UniModel (2 * r + ε) f K))) := by
    have hQ : (Q₀ : Subgroup (UniModel (2 * r + ε) f K)) =
        (hypProjUnitriangular h r ε).map Φ.toMonoidHom := by
      show (PU : Subgroup (hypPSU h r ε)).map Φ.toMonoidHom = _
      rw [hPU]
    have hmem : Φ a ∈ Subgroup.normalizer
        ((Q₀ : Subgroup (UniModel (2 * r + ε) f K)) : Set (UniModel (2 * r + ε) f K)) := by
      rw [hQ]
      exact Subgroup.le_normalizer_map Φ.toMonoidHom (Subgroup.mem_map_of_mem _ haN)
    have := Subgroup.orderOf_dvd_natCard _ hmem
    rwa [MulEquiv.orderOf_eq, hao] at this
  have : Finite (UniModel (2 * r + ε) f K) := Finite.of_equiv _ Φ.toEquiv
  exact forall_dvd_card_normalizer Q₀ hQ₀ Q

theorem torusUni :
    ∀ (Y : Type) [Group Y] [Finite Y] (L T : Subgroup Y) (n f p : ℕ), p.Prime → 5 ≤ p →
      CFSG.Open.IsQuasisimple ↥L → StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSU n 2 f →
      p ∣ Nat.gcd n (2 ^ f + 1) → IsSylowTwoOf T L →
      p ∣ Nat.card ↥(L ⊓ Subgroup.normalizer (T : Set Y)) := by
  intro Y _ _ L T n f p hp hp5 _ hmodel hdvd hT
  obtain ⟨⟨_, hf, hn3, _⟩, K, hF, hfin, hK, ⟨e⟩⟩ := hmodel
  have hpn : p ∣ n := hdvd.trans (Nat.gcd_dvd_left _ _)
  have hpq : p ∣ 2 ^ f + 1 := hdvd.trans (Nat.gcd_dvd_right _ _)
  have hn5 : 5 ≤ n := hp5.trans (Nat.le_of_dvd (by omega) hpn)
  exact dvd_card_inf_normalizer_of_equiv hT e fun Q => torusUni_model hK hf hp hp5 hpq hn5 Q

end CFSG.AGLEmbedding.TwoGenInner
