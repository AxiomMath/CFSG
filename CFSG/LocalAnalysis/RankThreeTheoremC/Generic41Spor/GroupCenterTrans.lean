module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.HeisAction

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open Subgroup CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
open scoped commutatorElement

private theorem zin_eq_inf_centralizer' {K : Type} [Group K] (S : Subgroup K) :
    Zin S = S ⊓ centralizer (S : Set K) := by
  ext x
  constructor
  · rintro ⟨⟨y, hy⟩, hyc, rfl⟩
    refine Subgroup.mem_inf.2 ⟨hy, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro h hh
    have := Subgroup.mem_center_iff.mp hyc ⟨h, hh⟩
    exact congrArg Subtype.val this
  · intro hx
    obtain ⟨hxS, hxc⟩ := Subgroup.mem_inf.1 hx
    refine Subgroup.mem_map.2 ⟨⟨x, hxS⟩, ?_, rfl⟩
    refine Subgroup.mem_center_iff.2 fun g => ?_
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hxc g g.2)

@[expose] def CenterTransAt {K : Type} [Group K] (S : Subgroup K) : Prop :=
  ∀ z ∈ Zin S, z ≠ 1 → ∀ w ∈ Zin S, w ≠ 1 → ∃ n ∈ normalizer (S : Set K), n * z * n⁻¹ = w

theorem zin_map_equiv {K K' : Type} [Group K] [Group K'] (e : K ≃* K') (S : Subgroup K) :
    Zin (S.map e.toMonoidHom) = (Zin S).map e.toMonoidHom := by
  ext w
  rw [Subgroup.mem_map_equiv, zin_eq_inf_centralizer', zin_eq_inf_centralizer',
    Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_map_equiv, Subgroup.mem_centralizer_iff,
    Subgroup.mem_centralizer_iff]
  refine and_congr Iff.rfl ?_
  constructor
  · intro h g hg
    have := h (e g) (by rw [SetLike.mem_coe, Subgroup.mem_map_equiv]; simpa using hg)
    apply e.injective
    simpa using this
  · intro h g hg
    have hg' : e.symm g ∈ S := by
      rw [SetLike.mem_coe, Subgroup.mem_map_equiv] at hg
      exact hg
    have := h (e.symm g) hg'
    apply e.symm.injective
    simpa using this

theorem CenterTransAt.of_equiv {K K' : Type} [Group K] [Group K'] (e : K ≃* K')
    {S : Subgroup K} {S' : Subgroup K'} (hS : S.map e.toMonoidHom = S')
    (h : CenterTransAt S') : CenterTransAt S := by
  subst hS
  intro z hz hz1 w hw hw1
  have hzZ : e z ∈ Zin (S.map e.toMonoidHom) := by
    rw [zin_map_equiv]
    exact Subgroup.mem_map_of_mem _ hz
  have hwZ : e w ∈ Zin (S.map e.toMonoidHom) := by
    rw [zin_map_equiv]
    exact Subgroup.mem_map_of_mem _ hw
  obtain ⟨n', hn', hn'e⟩ := h (e z) hzZ (fun h1 => hz1 (e.injective (by simpa using h1)))
    (e w) hwZ (fun h1 => hw1 (e.injective (by simpa using h1)))
  have hN : e.symm n' ∈ normalizer (S : Set K) := by
    have : n' ∈ (normalizer (S : Set K)).map e.toMonoidHom := by
      rw [Subgroup.map_equiv_normalizer_eq]
      exact hn'
    rw [Subgroup.mem_map_equiv] at this
    exact this
  refine ⟨e.symm n', hN, e.injective ?_⟩
  simpa using hn'e

theorem coe_smul_sylow_map_conj {K : Type} [Group K] {p : ℕ} (T : Sylow p K) (g : K) :
    ((g • T : Sylow p K) : Subgroup K) = (T : Subgroup K).map (MulAut.conj g).toMonoidHom := by
  rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
  rfl

theorem CenterTransAt.of_sylow {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    {T₀ : Sylow p K} (h : CenterTransAt (T₀ : Subgroup K)) (T : Sylow p K) :
    CenterTransAt (T : Subgroup K) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K T₀ T
  refine CenterTransAt.of_equiv (MulAut.conj g⁻¹) (S' := (T₀ : Subgroup K)) ?_ h
  have h1 : (T : Subgroup K) = (T₀ : Subgroup K).map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    exact coe_smul_sylow_map_conj T₀ g
  rw [h1, Subgroup.map_map]
  conv_rhs => rw [← Subgroup.map_id (T₀ : Subgroup K)]
  congr 1
  ext x
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.coe_comp, Function.comp_apply,
    MonoidHom.id_apply]
  group

theorem normalizerTransitiveCenter_of_equiv {K K' : Type} [Group K] [Group K'] [Finite K]
    [Finite K'] {p : ℕ} (hp : p.Prime) (e : K ≃* K') (T₀ : Sylow p K')
    (h : CenterTransAt (T₀ : Subgroup K')) : NormalizerTransitiveCenter p K := by
  have : Fact p.Prime := ⟨hp⟩
  intro T
  have hf : Function.Surjective e.toMonoidHom := e.surjective
  have D' := CenterTransAt.of_sylow hp h (Sylow.mapSurjective hf T)
  exact CenterTransAt.of_equiv e (S' := ((Sylow.mapSurjective hf T : Sylow p K') : Subgroup K'))
    rfl D'

theorem commutator_zpow_mul_zpow {G : Type*} [Group G] (x y : G)
    (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y) (a b c d : ℤ) :
    ⁅x ^ a * y ^ c, x ^ b * y ^ d⁆ = ⁅x, y⁆ ^ (a * d - b * c) := by
  have e1 : ∀ k : ℤ, y ^ k * x * (y ^ k)⁻¹ = ⁅x, y⁆ ^ (-k) * x := yzpow_mul_x x y hzy
  generalize ⁅x, y⁆ = z at *
  have key : ∀ b c : ℤ, y ^ c * x ^ b = z ^ (-(c * b)) * (x ^ b * y ^ c) := by
    intro b c
    have h2 : y ^ c * x ^ b * (y ^ c)⁻¹ = z ^ (-(c * b)) * x ^ b := by
      rw [← conj_zpow, e1 c, (((hzx.zpow_left (-c))).mul_zpow b), ← zpow_mul, neg_mul]
    calc y ^ c * x ^ b = (y ^ c * x ^ b * (y ^ c)⁻¹) * y ^ c := by group
      _ = z ^ (-(c * b)) * (x ^ b * y ^ c) := by rw [h2]; group
  have mulform : ∀ a b c d : ℤ, (x ^ a * y ^ c) * (x ^ b * y ^ d) =
      z ^ (-(c * b)) * (x ^ (a + b) * y ^ (c + d)) := by
    intro a b c d
    have hc : Commute (z ^ (-(c * b))) (x ^ a) := (hzx.zpow_left _).zpow_right a
    calc (x ^ a * y ^ c) * (x ^ b * y ^ d) = x ^ a * (y ^ c * x ^ b) * y ^ d := by group
      _ = x ^ a * (z ^ (-(c * b)) * (x ^ b * y ^ c)) * y ^ d := by rw [key]
      _ = (x ^ a * z ^ (-(c * b))) * (x ^ b * y ^ c) * y ^ d := by group
      _ = (z ^ (-(c * b)) * x ^ a) * (x ^ b * y ^ c) * y ^ d := by rw [← hc.eq]
      _ = z ^ (-(c * b)) * (x ^ (a + b) * y ^ (c + d)) := by group
  have h1 := mulform a b c d
  have h2 := mulform b a d c
  rw [add_comm b a, add_comm d c] at h2
  have e : ⁅x ^ a * y ^ c, x ^ b * y ^ d⁆ =
      ((x ^ a * y ^ c) * (x ^ b * y ^ d)) * ((x ^ b * y ^ d) * (x ^ a * y ^ c))⁻¹ := by
    rw [commutatorElement_def]; group
  rw [e, h1, h2]
  group

theorem heis_exists_eq_pow_mul_center {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    {Q : Subgroup G} (D : HeisCoordData p Q) (q : Q) :
    ∃ w ∈ Subgroup.center Q, q = D.x ^ (Multiplicative.toAdd (D.π q) 0).val *
      D.y ^ (Multiplicative.toAdd (D.π q) 1).val * w := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  set v := Multiplicative.toAdd (D.π q) with hv
  set u : Q := D.x ^ (v 0).val * D.y ^ (v 1).val with hu
  have hπu : D.π u = D.π q := by
    apply Multiplicative.toAdd.injective
    rw [hu, map_mul, map_pow, map_pow, D.π_x, D.π_y]
    ext i
    fin_cases i <;> simp [hv]
  refine ⟨u⁻¹ * q, ?_, by simp⟩
  rw [← D.ker_eq, MonoidHom.mem_ker, map_mul, map_inv, hπu]
  exact inv_mul_cancel _

theorem zpow_eq_zpow_of_intCast_eq {G : Type*} [Group G] {p : ℕ} {z : G} (hz : orderOf z = p)
    {i j : ℤ} (h : (i : ZMod p) = (j : ZMod p)) : z ^ i = z ^ j := by
  rw [zpow_eq_zpow_iff_modEq, hz]
  exact (ZMod.intCast_eq_intCast_iff i j p).1 h

theorem intCast_ne_zero_of_zpow_ne_one {G : Type*} [Group G] {p : ℕ} {z : G}
    (hz : orderOf z = p) {i : ℤ} (h : z ^ i ≠ 1) : (i : ZMod p) ≠ 0 := by
  intro h0
  apply h
  rw [← orderOf_dvd_iff_zpow_eq_one, hz]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd i p).1 h0

theorem commutator_mul_mem_center {Q : Type*} [Group Q] {w₁ w₂ : Q} (a b : Q)
    (hw₁ : w₁ ∈ Subgroup.center Q) (hw₂ : w₂ ∈ Subgroup.center Q) :
    ⁅a * w₁, b * w₂⁆ = ⁅a, b⁆ := by
  have h1 : ∀ c : Q, ⁅w₁, c⁆ = 1 := fun c =>
    Commute.commutator_eq (Subgroup.mem_center_iff.1 hw₁ c).symm
  have h2 : ∀ c : Q, ⁅c, w₂⁆ = 1 := fun c =>
    Commute.commutator_eq (Subgroup.mem_center_iff.1 hw₂ c)
  rw [commutatorElement_mul_left_eq_conj_mul, h1, commutatorElement_mul_right_eq_mul_conj, h2]
  group

theorem heis_conj_comm_eq {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] {Q : Subgroup G}
    (D : HeisCoordData p Q) (hZ : Subgroup.center Q = Subgroup.zpowers ⁅D.x, D.y⁆)
    (hz : orderOf (⁅(D.x : G), (D.y : G)⁆) = p) (n : normalizer (Q : Set G)) :
    (n : G) * ⁅(D.x : G), (D.y : G)⁆ * (n : G)⁻¹ =
      ⁅(D.x : G), (D.y : G)⁆ ^ (Matrix.det (D.actMat n)).val := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hzc : ⁅D.x, D.y⁆ ∈ Subgroup.center Q := by
    rw [hZ]
    exact Subgroup.mem_zpowers _
  have hzx : Commute ⁅D.x, D.y⁆ D.x := (Subgroup.mem_center_iff.1 hzc D.x).symm
  have hzy : Commute ⁅D.x, D.y⁆ D.y := (Subgroup.mem_center_iff.1 hzc D.y).symm
  set M := D.actMat n with hM
  have hcol : ∀ j : Fin 2, ∃ w ∈ Subgroup.center Q,
      Q.normalizerMonoidHom n (D.gen2 j) = D.x ^ (M 0 j).val * D.y ^ (M 1 j).val * w := by
    intro j
    obtain ⟨w, hw, h⟩ := heis_exists_eq_pow_mul_center D (Q.normalizerMonoidHom n (D.gen2 j))
    exact ⟨w, hw, h⟩
  obtain ⟨w₁, hw₁, h₁⟩ := hcol 0
  obtain ⟨w₂, hw₂, h₂⟩ := hcol 1
  have hgen0 : D.gen2 0 = D.x := rfl
  have hgen1 : D.gen2 1 = D.y := rfl
  rw [hgen0] at h₁
  rw [hgen1] at h₂
  have hA := commutator_zpow_mul_zpow D.x D.y hzx hzy ((M 0 0).val : ℤ) ((M 0 1).val : ℤ)
    ((M 1 0).val : ℤ) ((M 1 1).val : ℤ)
  simp only [zpow_natCast] at hA
  have e1 : Q.normalizerMonoidHom n ⁅D.x, D.y⁆ = ⁅D.x, D.y⁆ ^
      (((M 0 0).val : ℤ) * ((M 1 1).val : ℤ) - ((M 0 1).val : ℤ) * ((M 1 0).val : ℤ)) := by
    rw [map_commutatorElement, h₁, h₂, commutator_mul_mem_center _ _ hw₁ hw₂, hA]
  have e3 : (n : G) * ⁅(D.x : G), (D.y : G)⁆ * (n : G)⁻¹ =
      ((Q.normalizerMonoidHom n ⁅D.x, D.y⁆ : Q) : G) := rfl
  rw [e3, e1, Subgroup.coe_zpow, ← zpow_natCast]
  apply zpow_eq_zpow_of_intCast_eq hz
  rw [Matrix.det_fin_two]
  push_cast
  simp [ZMod.natCast_val]

theorem centerTransAt_of_generator {K : Type} [Group K] {p : ℕ} [Fact p.Prime] (S : Subgroup K)
    {z n : K} {δ : ℤ} (hZ : Zin S = Subgroup.zpowers z) (hz : orderOf z = p)
    (hn : n ∈ normalizer (S : Set K)) (hconj : n * z * n⁻¹ = z ^ δ)
    (hgen : ∀ t : ZMod p, t ≠ 0 → ∃ m : ℕ, (δ : ZMod p) ^ m = t) : CenterTransAt S := by
  intro u hu hu1 w hw hw1
  rw [hZ] at hu hw
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
  have hi : (i : ZMod p) ≠ 0 := intCast_ne_zero_of_zpow_ne_one hz hu1
  have hj : (j : ZMod p) ≠ 0 := intCast_ne_zero_of_zpow_ne_one hz hw1
  obtain ⟨m, hm⟩ := hgen ((j : ZMod p) * (i : ZMod p)⁻¹) (mul_ne_zero hj (inv_ne_zero hi))
  have hpow : ∀ m : ℕ, n ^ m * z * (n ^ m)⁻¹ = z ^ (δ ^ m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc n ^ (m + 1) * z * (n ^ (m + 1))⁻¹ = n * (n ^ m * z * (n ^ m)⁻¹) * n⁻¹ := by
            rw [pow_succ']; group
        _ = n * z ^ (δ ^ m) * n⁻¹ := by rw [ih]
        _ = (n * z * n⁻¹) ^ (δ ^ m) := by rw [conj_zpow]
        _ = (z ^ δ) ^ (δ ^ m) := by rw [hconj]
        _ = z ^ (δ ^ (m + 1)) := by rw [← zpow_mul, pow_succ']
  refine ⟨n ^ m, Subgroup.pow_mem _ hn m, ?_⟩
  rw [← conj_zpow, hpow m, ← zpow_mul]
  apply zpow_eq_zpow_of_intCast_eq hz
  push_cast
  rw [hm, mul_assoc, inv_mul_cancel₀ hi, mul_one]

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
