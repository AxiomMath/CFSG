module

public import CFSG.LocalAnalysis.Mason73.Fusion38
public import CFSG.LocalAnalysis.Mason73.Fusion41
public import CFSG.LocalAnalysis.Mason73.Model42
public import CFSG.LocalAnalysis.Mason73.Theta

public section

namespace CFSG.LocalAnalysis.Mason73

open CFSG.CGT.Stroth77.L4Sylow CFSG.GH74.GLS.Stage1.Thm3.Sec8 CFSG.ABGLocalTools
  CFSG.ComponentClassification Equiv Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {n : ℕ}

theorem exists_normalized_embedding [IsSimpleGroup G] (hn : 3 ≤ n) {ι : L4Model n →* G}
    (hι : Function.Injective ι) (S : Sylow 2 G) (hS : ι.range = S) :
    ∃ ι' : L4Model n →* G, Function.Injective ι' ∧ ι'.range = ι.range ∧
      (∀ a ∈ A n, ι' a = ι a) ∧ ι' (tT (by omega)) = ι (tT (by omega)) ∧
      (∃ g : G, g * ι' (uT (by omega)) * g⁻¹ = ι' (zT (by omega))) ∧
      ∃ g : G, g * ι' (uw1T hn) * g⁻¹ = ι' (w1T hn) := by
  obtain ⟨-, h36i, -⟩ := fusionPattern hn hι S hS
  rcases h36i with ⟨hu, huw⟩ | ⟨huw, hu⟩
  · exact ⟨ι, hι, rfl, fun _ _ => rfl, rfl, hu, huw⟩
  · refine ⟨ι.comp (thetaAut hn).toMonoidHom, hι.comp (thetaAut hn).injective, ?_,
      fun a ha => ?_, ?_, ?_, ?_⟩
    · rw [MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective (thetaAut hn).toMonoidHom
        (thetaAut hn).surjective, ← MonoidHom.range_eq_map]
    · change ι (thetaAut hn a) = _
      rw [thetaAut_of_mem_A hn ha]
    · change ι (thetaAut hn (tT (by omega))) = _
      rw [thetaAut_tT]
    · change ∃ g : G, g * ι (thetaAut hn (uT (by omega))) * g⁻¹ =
        ι (thetaAut hn (zT (by omega)))
      rw [thetaAut_uT, thetaAut_of_mem_A hn (zT_mem_A _)]
      exact huw
    · change ∃ g : G, g * ι (thetaAut hn (uw1T hn)) * g⁻¹ = ι (thetaAut hn (w1T hn))
      rw [thetaAut_uw1T, thetaAut_of_mem_A hn (w1T_mem_A hn)]
      exact hu

theorem conj_mem_commutator_self {C : Subgroup G} {c k : G} (hc : c ∈ C) (hk : k ∈ ⁅C, C⁆) :
    c * k * c⁻¹ ∈ ⁅C, C⁆ := by
  rw [← map_subtype_commutator] at hk ⊢
  obtain ⟨k', hk', rfl⟩ := hk
  exact ⟨⟨c, hc⟩ * k' * ⟨c, hc⟩⁻¹, (inferInstance : (commutator C).Normal).conj_mem _ hk' _, rfl⟩

theorem map_mem_commutator {ι : L4Model n →* G} {C : Subgroup G} (hC : ι.range ≤ C)
    {k : L4Model n} (hk : k ∈ commutator (L4Model n)) : ι k ∈ ⁅C, C⁆ := by
  have h : (commutator (L4Model n)).map ι ≤ ⁅C, C⁆ := by
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map]
    exact Subgroup.commutator_mono hC hC
  exact h ⟨k, hk, rfl⟩

theorem range_le_centralizer_zT (hn : 2 ≤ n) (ι : L4Model n →* G) :
    ι.range ≤ centralizer {ι (zT (n := n) (by omega))} := by
  rintro _ ⟨y, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
    (Subgroup.mem_center_iff.1 (zT_mem_center (n := n) hn) y)]

theorem xParity_w1T (hn : 3 ≤ n) : xParity (by omega) (w1T (n := n) hn) = 1 := by
  rw [w1T, xParity_el]
  simp only [wv, hv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Nat.cast_one,
    Nat.cast_zero, mul_one, mul_zero, add_zero]
  rw [show ss n + hh n + ss n = 2 * ss n + hh n by ring, map_add, map_mul, red2_two, zero_mul,
    zero_add, red2_hh (by omega), ofAdd_zero]

theorem uT_mem_commutator_centralizer [IsSimpleGroup G] (hn : 3 ≤ n) {ι : L4Model n →* G}
    (hι : Function.Injective ι) (S : Sylow 2 G) (hS : ι.range = S) :
    ι (uT (by omega)) ∈
      ⁅centralizer {ι (zT (n := n) (by omega))}, centralizer {ι (zT (n := n) (by omega))}⁆ := by
  have hS' : IsSylowOf 2 ι.range ⊤ := by
    rw [hS]
    exact GHarris.isSylowOf_top S
  obtain ⟨hzx, h36i, -⟩ := fusionPattern hn hι S hS
  have hC := range_le_centralizer_zT (by omega) ι
  have hx1 : ι (x1T (n := n) (by omega)) ∈
      ⁅centralizer {ι (zT (n := n) (by omega))}, centralizer {ι (zT (n := n) (by omega))}⁆ :=
    map_mem_commutator hC (mem_commutator_of_xParity hn (by
      rw [x1T, xParity_hv]) (Or.inl rfl))
  have key : ∀ l : L4Model n, piT l = s23 → (∃ g : G, g * ι l * g⁻¹ = ι (zT (by omega))) →
      ι l ∈ ⁅centralizer {ι (zT (n := n) (by omega))},
        centralizer {ι (zT (n := n) (by omega))}⁆ := by
    rintro l hl ⟨g, hg⟩
    obtain ⟨c, hc, hc4⟩ := exists_pow_four_eq_zT_of_piT_s23 hn (Or.inl hl)
    have hlz : l ≠ zT (by omega) := by
      rintro rfl
      rw [mem_A_iff.1 (zT_mem_A _)] at hl
      exact absurd hl (by decide)
    obtain ⟨h, hh, hlx⟩ := lemma41 hn hι hS' hzx hlz hc hc4 hg
    have : ι l = h⁻¹ * ι (x1T (by omega)) * h⁻¹⁻¹ := by rw [← hlx]; group
    rw [this]
    exact conj_mem_commutator_self (inv_mem hh) hx1
  rcases h36i with ⟨hu, -⟩ | ⟨huw, -⟩
  · exact key _ rfl hu
  · have h1 := key _ rfl huw
    have hw : ι (w1T (n := n) hn) ∈ ⁅centralizer {ι (zT (n := n) (by omega))},
        centralizer {ι (zT (n := n) (by omega))}⁆ :=
      map_mem_commutator hC (mem_commutator_of_xParity hn (xParity_w1T hn)
        (Or.inl (mem_A_iff.1 (w1T_mem_A hn))))
    have := mul_mem h1 (inv_mem hw)
    rwa [← uT_mul_w1T hn, map_mul, mul_inv_cancel_right] at this

theorem xT_pow_two_pow (hn : 2 ≤ n) : xT n ^ 2 ^ n = 1 := by
  have h := x1T_eq_pow (n := n) hn
  have h2 : x1T (n := n) (by omega) * x1T (by omega) = 1 := by
    rw [← pow_two, ← orderOf_dvd_iff_pow_eq_one, orderOf_x1T hn]
  have hpow : 2 ^ n = 2 ^ (n - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  calc xT n ^ 2 ^ n = xT n ^ (2 ^ (n - 1) * 2) := congrArg (xT n ^ ·) hpow
    _ = 1 := by rw [pow_mul, ← h, pow_two, h2]

theorem x1T_zpow_eq_one_iff (hn : 2 ≤ n) (m : ℤ) :
    x1T (n := n) (by omega) ^ m = 1 ↔ (m : ZMod 2) = 0 := by
  rw [← orderOf_dvd_iff_zpow_eq_one, orderOf_x1T hn, ZMod.intCast_zmod_eq_zero_iff_dvd]

theorem x1T_zpow_ne_zT (hn : 2 ≤ n) (m : ℤ) :
    x1T (n := n) (by omega) ^ m ≠ zT (by omega) := by
  have h2 : x1T (n := n) (by omega) ^ 2 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, orderOf_x1T hn]
  rw [zpow_eq_zpow_emod' m h2]
  have hm : m % (2 : ℕ) = 0 ∨ m % (2 : ℕ) = 1 := by omega
  rcases hm with hm | hm <;> rw [hm]
  · intro h
    have := orderOf_zT (n := n) hn
    rw [← h, zpow_zero, orderOf_one] at this
    exact absurd this (by norm_num)
  · rw [zpow_one]
    exact x1T_ne_zT hn

theorem piT_txT_inv_mul_mem_V1 {g : L4Model n} (hg : piT g ∉ V1) :
    piT ((txT n)⁻¹ * g) ∈ V1 := by
  have key : ∀ π : Fin81.R0, π ∉ V1 → tP⁻¹ * π ∈ V1 := by
    decide
  rw [map_mul, map_inv]
  exact key _ hg

theorem lemma42 [IsSimpleGroup G] (hn : 3 ≤ n) {ι : L4Model n →* G}
    (hι : Function.Injective ι) (S : Sylow 2 G) (hS : ι.range = S) :
    ι (xT n) ∉
      ⁅centralizer {ι (zT (n := n) (by omega))}, centralizer {ι (zT (n := n) (by omega))}⁆ := by
  have hS' : IsSylowOf 2 ι.range ⊤ := by
    rw [hS]
    exact GHarris.isSylowOf_top S
  set C := centralizer {ι (zT (n := n) (by omega))} with hCdef
  have hC : ι.range ≤ C := range_le_centralizer_zT (by omega) ι
  have hu := uT_mem_commutator_centralizer hn hι S hS
  have htx := lemma34_txT hn hι hS'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K : Subgroup G := ((xParity (n := n) (by omega)).ker).map ι with hKdef
  have hindex : Nat.Coprime 2 (ι.range.relIndex C) := by
    have h := (isSylowOf_iff.1 (isSylowOf_zT hn hS')).2.2
    rw [inf_of_le_left hC] at h
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 h
  refine CFSG.Quasithin.generalized_thompson_transfer_one_subgroup (p := 2) hC hindex
    (K := K) ?_ ?_ ?_ ⟨xT n, rfl⟩ ?_ ⟨n, by rw [← map_pow, xT_pow_two_pow (by omega), map_one]⟩
    ?_
  · rintro _ ⟨b, -, rfl⟩
    exact ⟨b, rfl⟩
  · rintro _ ⟨a, rfl⟩ _ ⟨b, hb, rfl⟩
    exact ⟨a * b * a⁻¹, (xParity (n := n) (by omega)).normal_ker.conj_mem b hb a,
      by rw [map_mul, map_mul, map_inv]⟩
  · rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← _root_.commutator_def]
    exact Subgroup.map_mono (Abelianization.commutator_subset_ker _)
  · rintro ⟨b, hb, hbx⟩
    rw [hι hbx, SetLike.mem_coe, MonoidHom.mem_ker, xParity_xT] at hb
    exact ofAdd_one_ne_one_zmod2 hb
  · intro m a ha hb
    obtain ⟨b, hbm⟩ := hb
    have hxm : (ι (xT n)) ^ m = ι (xT n ^ m) := (map_zpow ι _ m).symm
    rw [hxm] at hbm ⊢
    have hbpow : ι (b ^ 2 ^ (n - 1)) = a⁻¹ * ι (x1T (by omega) ^ m) * a := by
      rw [map_pow, hbm, GHarris.conj_pow_inv, ← map_pow, ← zpow_natCast, ← zpow_mul,
        mul_comm, zpow_mul, zpow_natCast, ← x1T_eq_pow (by omega)]
    have hza : a⁻¹ * ι (zT (n := n) (by omega)) * a = ι (zT (by omega)) := by
      have := Subgroup.mem_centralizer_singleton_iff.1 ha
      calc a⁻¹ * ι (zT (n := n) (by omega)) * a = a⁻¹ * (a * ι (zT (by omega))) := by
            rw [mul_assoc, ← this]
        _ = _ := by group
    have h1 : b ^ 2 ^ (n - 1) = 1 ↔ ((m : ℤ) : ZMod 2) = 0 := by
      rw [← x1T_zpow_eq_one_iff (n := n) (by omega)]
      constructor
      · intro h
        rw [h, map_one] at hbpow
        apply hι
        rw [map_one]
        calc ι (x1T (n := n) (by omega) ^ m) = a * (a⁻¹ * ι (x1T (by omega) ^ m) * a) * a⁻¹ := by
              group
          _ = 1 := by rw [← hbpow]; group
      · intro h
        apply hι
        rw [hbpow, h, map_one]
        group
    have hz : b ^ 2 ^ (n - 1) ≠ zT (by omega) := by
      intro h
      apply x1T_zpow_ne_zT (n := n) (by omega) m
      apply hι
      calc ι (x1T (n := n) (by omega) ^ m) = a * (a⁻¹ * ι (x1T (by omega) ^ m) * a) * a⁻¹ := by
            group
        _ = a * ι (zT (by omega)) * a⁻¹ := by rw [← hbpow, h]
        _ = a * (a⁻¹ * ι (zT (by omega)) * a) * a⁻¹ := by rw [hza]
        _ = ι (zT (by omega)) := by group
    refine ⟨(xT n ^ m)⁻¹ * b, ?_, by rw [map_mul, map_inv, hbm]⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    by_cases hbV : piT b ∈ V1
    · rw [map_mul, map_inv, xParity_xT_zpow, xParity_eq_of_piT_mem_V1 hn hbV _ h1 hz]
      exact inv_mul_cancel _
    ·
      by_contra hpar
      set g := (xT n ^ m)⁻¹ * b with hgdef
      have hgC : ι g ∈ ⁅C, C⁆ := by
        rw [hgdef, map_mul, map_inv, hbm]
        have hxC : ι (xT n ^ m) ∈ C := hC ⟨_, rfl⟩
        have : (ι (xT n ^ m))⁻¹ * (a⁻¹ * ι (xT n ^ m) * a) =
            ⁅(ι (xT n ^ m))⁻¹, a⁻¹⁆ := by
          rw [commutatorElement_def, inv_inv, inv_inv]
          group
        rw [this]
        exact Subgroup.commutator_mem_commutator (inv_mem hxC) (inv_mem ha)
      have hgpar : xParity (n := n) (by omega) g = Multiplicative.ofAdd 1 :=
        eq_ofAdd_one_of_ne_one _ hpar
      have hgV : piT g ∉ V1 := by
        rw [hgdef, map_mul, map_inv, map_zpow, mem_A_iff.1 xT_mem_A, one_zpow, inv_one,
          one_mul]
        exact hbV
      have h2 : ((txT n)⁻¹ * g) ∈ Q1T n := piT_txT_inv_mul_mem_V1 hgV
      have hpar2 : xParity (n := n) (by omega) ((txT n)⁻¹ * g) = 1 := by
        rw [map_mul, map_inv, xParity_txT, hgpar]
        exact inv_mul_cancel _
      have hfin1 : ((txT n)⁻¹ * g) ∈ commutator (L4Model n) → False := by
        intro hc
        apply htx
        have := mul_mem hgC (inv_mem (map_mem_commutator hC hc))
        convert this using 1
        rw [← map_inv, ← map_mul]
        congr 1
        group
      have hfin2 : ((uT (n := n) (by omega))⁻¹ * ((txT n)⁻¹ * g)) ∈ commutator (L4Model n) →
          False := by
        intro hc
        apply htx
        have := mul_mem (mul_mem hgC (inv_mem (map_mem_commutator hC hc))) (inv_mem hu)
        convert this using 1
        rw [← map_inv, ← map_inv, ← map_mul, ← map_mul]
        congr 1
        group
      have hpar3 : xParity (n := n) (by omega) ((uT (by omega))⁻¹ * ((txT n)⁻¹ * g)) = 1 := by
        rw [map_mul, map_inv, xParity_uT, hpar2]
        exact (mul_one _).trans inv_one
      rcases piT_cases_of_mem_Q1T h2 with h | h | h | h
      · exact hfin1 (mem_commutator_of_xParity hn hpar2 (Or.inl h))
      · refine hfin2 (mem_commutator_of_xParity hn hpar3 (Or.inr ?_))
        rw [map_mul, map_inv, h, piT_uT]
        decide
      · refine hfin2 (mem_commutator_of_xParity hn hpar3 (Or.inl ?_))
        rw [map_mul, map_inv, h, piT_uT]
        decide
      · exact hfin1 (mem_commutator_of_xParity hn hpar2 (Or.inr h))

end CFSG.LocalAnalysis.Mason73
