module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.Point.LayerPt
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2ProjectiveLine

public section

open Subgroup
open scoped MatrixGroups

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

open CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem movesLines_map {H G' : Type*} [Group H] [Group G'] {p : ℕ} (f : H →* G')
    (hf : Function.Injective f) {V : Subgroup H} {σ : H} (hσ : σ ∈ normalizer (V : Set H))
    (hmove : ∀ D : Subgroup H, D ≤ V → Nat.card D = p → ∃ d ∈ D, σ * d * σ⁻¹ ∉ D) :
    f σ ∈ normalizer ((V.map f : Subgroup G') : Set G') ∧
      ∀ D : Subgroup G', D ≤ V.map f → Nat.card D = p → ∃ d ∈ D, f σ * d * (f σ)⁻¹ ∉ D := by
  refine ⟨le_normalizer_map f ⟨σ, hσ, rfl⟩, fun D hD hDc => ?_⟩
  have hDr : D ≤ f.range := hD.trans (map_le_range f V)
  obtain ⟨d, hd, hdσ⟩ := hmove (D.comap f)
    (fun v hv => by
      obtain ⟨w, hw, hwv⟩ := hD hv
      exact hf hwv ▸ hw)
    (by rw [← card_map_of_injective hf, map_comap_eq_self hDr, hDc])
  refine ⟨f d, hd, fun h => hdσ ?_⟩
  rw [mem_comap, map_mul, map_mul, map_inv]
  exact h

section TorusLinesAux

open Matrix CFSG.GorensteinWalter

variable {K : Type*} [Field K]

private def tlDiag (a : Kˣ) : SL(2, K) :=
  ⟨!![(a : K), 0; 0, ((a⁻¹ : Kˣ) : K)], by simp [Matrix.det_fin_two_of]⟩

private theorem tlDiag_mem_borel (a : Kˣ) : tlDiag a ∈ sl2Borel K := by
  rw [sl2Borel, sl2_mem_stabilizer_infinity_iff]
  simp [tlDiag]

private theorem tlDiag_conj (a : Kˣ) (x : K) :
    tlDiag a * sl2UpperUnipotent x * (tlDiag a)⁻¹ =
      sl2UpperUnipotent ((a : K) ^ 2 * x) := by
  rw [sl2Borel_conj_upperUnipotent (tlDiag_mem_borel a)]
  simp [tlDiag]

private theorem tlDiag_conj_psl2 (a : Kˣ) (x : K) :
    psl2QuotientMap K (tlDiag a) * psl2QuotientMap K (sl2UpperUnipotent x) *
      (psl2QuotientMap K (tlDiag a))⁻¹ =
      psl2QuotientMap K (sl2UpperUnipotent ((a : K) ^ 2 * x)) := by
  rw [← map_inv, ← map_mul, ← map_mul, tlDiag_conj]

private theorem tlConjMemUnip {A : SL(2, K)} (hA : A ∈ sl2Borel K) {h : PSL2 K}
    (hh : h ∈ psl2UpperUnipotentSubgroup K) :
    psl2QuotientMap K A * h * (psl2QuotientMap K A)⁻¹ ∈ psl2UpperUnipotentSubgroup K := by
  obtain ⟨x, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff h).1 hh
  rw [← map_inv, ← map_mul, ← map_mul, sl2Borel_conj_upperUnipotent hA]
  exact (mem_psl2UpperUnipotentSubgroup_iff _).2 ⟨_, rfl⟩

private theorem tlMemNormalizer {A : SL(2, K)} (hA : A ∈ sl2Borel K) :
    psl2QuotientMap K A ∈
      Subgroup.normalizer (psl2UpperUnipotentSubgroup K : Set (PSL2 K)) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro h
  refine ⟨fun hh => tlConjMemUnip hA hh, fun hh => ?_⟩
  have := tlConjMemUnip (inv_mem hA) hh
  simpa [mul_assoc] using this

private theorem tlUnipPow (x : K) (n : ℕ) :
    psl2QuotientMap K (sl2UpperUnipotent x) ^ n =
      psl2QuotientMap K (sl2UpperUnipotent ((n : K) * x)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, ← map_mul, sl2UpperUnipotent_mul, Nat.cast_succ, add_mul, one_mul]

private theorem tlUnipInj {x y : K}
    (h : psl2QuotientMap K (sl2UpperUnipotent x) = psl2QuotientMap K (sl2UpperUnipotent y)) :
    x = y := by
  have hcenter : sl2UpperUnipotent (x - y) ∈ Subgroup.center (SL(2, K)) := by
    have hq : psl2QuotientMap K (sl2UpperUnipotent (x - y)) = 1 := by
      rw [sub_eq_add_neg, ← sl2UpperUnipotent_mul, map_mul, ← sl2UpperUnipotent_inv, map_inv, h,
        mul_inv_cancel]
    exact (QuotientGroup.eq_one_iff _).mp hq
  have hscalar :=
    Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center hcenter (0 : Fin 2)
  have h01 := congrFun (congrFun hscalar (0 : Fin 2)) (1 : Fin 2)
  apply sub_eq_zero.mp
  simpa [sl2UpperUnipotent] using h01.symm

private theorem tl_intCast_pow_prime (p : ℕ) [Fact p.Prime] [CharP K p] (b : ℤ) :
    (b : K) ^ p = b := by
  have h := congrArg (ZMod.castHom (dvd_refl p) K) (ZMod.pow_card (b : ZMod p))
  rwa [map_pow, map_intCast] at h

private theorem tlUnitSqNotInt (p : ℕ) [Fact p.Prime] [CharP K p] [Finite K] (n : ℕ)
    (hn : 2 ≤ n) (hp5 : 5 ≤ p) (hcard : Nat.card K = p ^ n) {g : Kˣ}
    (hg : ∀ x : Kˣ, x ∈ Subgroup.zpowers g) (b : ℤ) :
    (g : K) ^ 2 ≠ (b : K) := by
  intro hb
  have hg0 : (g : K) ≠ 0 := g.ne_zero
  have hpow : (g : K) ^ (2 * p) = (g : K) ^ 2 := by
    rw [pow_mul, hb]
    exact tl_intCast_pow_prime p b
  have e : 2 * p = 2 * (p - 1) + 2 := by omega
  have h1 : (g : K) ^ (2 * (p - 1)) = 1 := by
    have h2 : (g : K) ^ (2 * (p - 1)) * (g : K) ^ 2 = 1 * (g : K) ^ 2 := by
      rw [one_mul, ← pow_add, ← e]
      exact hpow
    exact mul_right_cancel₀ (pow_ne_zero 2 hg0) h2
  have h3 : g ^ (2 * (p - 1)) = 1 := Units.ext (by simpa using h1)
  have h4 : orderOf g = p ^ n - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hcard]
  have h5 : 0 < 2 * (p - 1) := by omega
  have h6 := Nat.le_of_dvd h5 (orderOf_dvd_of_pow_eq_one h3)
  rw [h4] at h6
  have h7 : 5 * p ≤ p ^ 2 := by nlinarith
  have h8 : p ^ 2 ≤ p ^ n := Nat.pow_le_pow_right (by omega) hn
  omega

private theorem tlExistsNotMemConj (p : ℕ) [Fact p.Prime]
    (σ : PSL2 K) (s : K) (hs : ∀ k : ℕ, s ≠ k)
    (hσ : ∀ x : K, σ * psl2QuotientMap K (sl2UpperUnipotent x) * σ⁻¹ =
      psl2QuotientMap K (sl2UpperUnipotent (s * x)))
    (H : Subgroup (PSL2 K)) (hHU : H ≤ psl2UpperUnipotentSubgroup K)
    (hH : Nat.card H = p) :
    ∃ h ∈ H, σ * h * σ⁻¹ ∉ H := by
  by_contra hcon
  push Not at hcon
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hfin : Finite H := Nat.finite_of_card_ne_zero (by rw [hH]; exact hp)
  have hnt : Nontrivial H :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hH]; exact (Fact.out : p.Prime).one_lt)
  obtain ⟨⟨h, hh⟩, hne⟩ := exists_ne (1 : H)
  obtain ⟨x0, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff h).1 (hHU hh)
  have hx0 : x0 ≠ 0 := by
    rintro rfl
    exact hne (Subtype.ext (by simp))
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).1
    (mem_powers_of_prime_card hH hne (g' := ⟨σ * _ * σ⁻¹, hcon _ hh⟩))
  have hk' := congrArg Subtype.val hk
  simp only [Subgroup.coe_pow] at hk'
  rw [tlUnipPow, hσ] at hk'
  exact hs k (mul_right_cancel₀ hx0 (tlUnipInj hk')).symm

end TorusLinesAux

open CFSG.GorensteinWalter

theorem psl2_torus_data_lines (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (n : ℕ) (hn : 2 ≤ n) :
    ∃ (U : Subgroup PSL(2, GaloisField p n)) (σ : PSL(2, GaloisField p n)),
      Nat.card U = p ^ n ∧ (∀ u ∈ U, u ^ p = 1) ∧ (∀ u ∈ U, ∀ v ∈ U, u * v = v * u) ∧
      σ ∈ normalizer (U : Set PSL(2, GaloisField p n)) ∧
      ∀ D : Subgroup PSL(2, GaloisField p n), D ≤ U → Nat.card D = p →
        ∃ d ∈ D, σ * d * σ⁻¹ ∉ D := by
  have hcard : Nat.card (GaloisField p n) = p ^ n := GaloisField.card p n (by omega)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (GaloisField p n)ˣ)
  refine ⟨psl2UpperUnipotentSubgroup (GaloisField p n),
    psl2QuotientMap (GaloisField p n) (tlDiag g), ?_, ?_, ?_, ?_, ?_⟩
  · rw [psl2UpperUnipotentSubgroup_card, hcard]
  · intro u hu
    obtain ⟨x, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff u).1 hu
    rw [tlUnipPow, CharP.cast_eq_zero, zero_mul, sl2UpperUnipotent_zero, map_one]
  · intro u hu v hv
    obtain ⟨x, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff u).1 hu
    obtain ⟨y, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff v).1 hv
    rw [← map_mul, ← map_mul, sl2UpperUnipotent_mul, sl2UpperUnipotent_mul, add_comm]
  · exact tlMemNormalizer (tlDiag_mem_borel g)
  · intro D hDU hDc
    have hs : ∀ k : ℕ, (g : GaloisField p n) ^ 2 ≠ (k : GaloisField p n) := by
      intro k
      have h := tlUnitSqNotInt p n hn hp5 hcard hg (k : ℤ)
      rwa [Int.cast_natCast] at h
    exact tlExistsNotMemConj p (psl2QuotientMap (GaloisField p n) (tlDiag g))
      ((g : GaloisField p n) ^ 2) hs (tlDiag_conj_psl2 g) D hDU hDc

theorem pt_exists_torus_lines [Fact p.Prime] (hG : FrobGlobal G) (hl : LayerLocal p P M x) :
    ∃ t ∈ layerOf x, t ∈ normalizer ((frU P x : Subgroup G) : Set G) ∧
      ∀ D : Subgroup G, D ≤ frU P x → Nat.card D = p → ∃ d ∈ D, t * d * t⁻¹ ∉ D := by
  obtain ⟨n, hn2, ⟨e⟩, hU, hUe, hUc⟩ := lp_layer_sylow hG hl
  obtain ⟨U₀, σ₀, hU₀c, -, -, hσ₀N, hσ₀⟩ := psl2_torus_data_lines p hl.p5 n hn2
  set L := layerOf x
  set f₀ : PSL(2, GaloisField p n) →* G := L.subtype.comp e.symm.toMonoidHom
  have hf₀inj : Function.Injective f₀ := L.subtype_injective.comp e.symm.injective
  have hU₁ : IsSylowOf p (U₀.map f₀) L := by
    refine isSylowOf_of_card ?_ ?_
    · rintro _ ⟨u, -, rfl⟩
      exact (e.symm u).2
    · rw [card_map_of_injective hf₀inj, hU₀c, ← hU.card_eq, hUc]
  obtain ⟨k, hkL, hk⟩ := hU₁.exists_mem_conj hU
  set f : PSL(2, GaloisField p n) →* G := (MulAut.conj k).toMonoidHom.comp f₀ with hf
  have hfinj : Function.Injective f := (MulAut.conj k).injective.comp hf₀inj
  have hfU : U₀.map f = frU P x := by
    ext y
    rw [hk y, hf, ← map_map]
    constructor
    · rintro ⟨z, hz, rfl⟩
      change k⁻¹ * (k * z * k⁻¹) * k ∈ _
      rwa [show k⁻¹ * (k * z * k⁻¹) * k = z by group]
    · intro hy
      exact ⟨k⁻¹ * y * k, hy, by simp [mul_assoc]⟩
  obtain ⟨hN, hmove⟩ := movesLines_map f hfinj hσ₀N hσ₀
  rw [hfU] at hN hmove
  refine ⟨f σ₀, ?_, hN, hmove⟩
  have h0 : f₀ σ₀ ∈ L := (e.symm σ₀).2
  change k * f₀ σ₀ * k⁻¹ ∈ L
  exact L.mul_mem (L.mul_mem hkL h0) (L.inv_mem hkL)

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
