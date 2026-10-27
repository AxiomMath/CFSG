module

public import CFSG.GH74.E2.FrattiniRank
import CFSG.LocalAnalysis.SectionRank.Ccomm.PGroupBasics
import CFSG.LocalAnalysis.PreuniquenessRankFour.CoprimeAction

public section

namespace CFSG.GH74.E2

open Subgroup

theorem mem_of_normalizing_involution {G : Type*} [Group G] [Finite G] (hG : Gen4 G)
    {Q B : Subgroup G} (hQ : IsPGroup 2 Q) (hBnorm : ∀ b ∈ B, ∀ q ∈ Q, b * q * b⁻¹ ∈ Q)
    (hB : ElemAb 3 B) (hBcard : Nat.card B = 9)
    (hfaith : ∀ b ∈ B, (∀ q ∈ Q, b * q * b⁻¹ = q) → b = 1)
    {x : G} (hx2 : x ^ 2 = 1) (hxnorm : ∀ q ∈ Q, x * q * x⁻¹ ∈ Q)
    (hxB : ∀ b ∈ B, b * x = x * b) : x ∈ Q := by
  have hxx : x * x = 1 := by rw [← pow_two]; exact hx2
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hxN : x ∈ normalizer (Q : Set G) := by
    rw [mem_normalizer_iff]
    intro q
    refine ⟨fun hq => hxnorm q hq, fun h => ?_⟩
    have h2 := hxnorm _ h
    have h3 : x * (x * q * x⁻¹) * x⁻¹ = q := by
      rw [hxinv]
      calc x * (x * q * x) * x = (x * x) * q * (x * x) := by group
        _ = q := by rw [hxx]; group
    rwa [h3] at h2
  have hZ : IsPGroup 2 ↥(zpowers x) := by
    have h1 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h]; rfl)
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h]; rfl)
  have hZN : zpowers x ≤ normalizer (Q : Set G) := zpowers_le.mpr hxN
  have hP : IsPGroup 2 ↥(Q ⊔ zpowers x) := IsPGroup.to_sup_of_normal_left' hQ hZ hZN
  have hxP : x ∈ Q ⊔ zpowers x := mem_sup_right (mem_zpowers x)
  have hQP : Q ≤ Q ⊔ zpowers x := le_sup_left
  have hBP : ∀ b ∈ B, ∀ y ∈ Q ⊔ zpowers x, b * y * b⁻¹ ∈ Q ⊔ zpowers x := by
    intro b hb y hy
    have hle : Q ⊔ zpowers x ≤ (Q ⊔ zpowers x).comap (MulAut.conj b).toMonoidHom := by
      refine sup_le (fun q hq => ?_) (fun z hz => ?_)
      · exact hQP (hBnorm b hb q hq)
      · obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
        have hbx : b * x * b⁻¹ = x := by rw [hxB b hb]; group
        show b * x ^ k * b⁻¹ ∈ Q ⊔ zpowers x
        rw [← conj_zpow, hbx]
        exact mem_sup_right (zpow_mem_zpowers x k)
    exact hle hy
  have hBnormP : B ≤ normalizer ((Q ⊔ zpowers x : Subgroup G) : Set G) := by
    intro b hb
    rw [mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hBP b hb y hy, fun h => ?_⟩
    have h2 := hBP b⁻¹ (B.inv_mem hb) _ h
    have h3 : b⁻¹ * (b * y * b⁻¹) * b⁻¹⁻¹ = y := by group
    rwa [h3] at h2
  have hφ : Function.Injective (conjAction B (Q ⊔ zpowers x) hBnormP) := by
    rw [injective_iff_map_eq_one]
    intro b hb
    apply Subtype.ext
    rw [Subgroup.coe_one]
    apply hfaith b b.2
    intro q hq
    have h2 := congrArg (fun f : MulAut ↥(Q ⊔ zpowers x) =>
      ((f ⟨q, hQP hq⟩ : ↥(Q ⊔ zpowers x)) : G)) hb
    have h3 : ((conjAction B (Q ⊔ zpowers x) hBnormP b ⟨q, hQP hq⟩ : ↥(Q ⊔ zpowers x)) : G) =
        (b : G) * q * (b : G)⁻¹ := rfl
    simp only [h3] at h2
    simpa using h2
  have hcommB : ∀ a b : B, a * b = b * a := fun a b => Subtype.ext (hB.1 a a.2 b b.2)
  have hpowB : ∀ a : B, a ^ 3 = 1 := fun a => Subtype.ext (hB.2 a a.2)
  obtain ⟨-, hfrat⟩ := threeSquared_faithful hP (Gen4.rank_le_four hG hP)
    (conjAction B (Q ⊔ zpowers x) hBnormP) hφ hcommB hpowB hBcard
  have hx_frat : (⟨x, hxP⟩ : ↥(Q ⊔ zpowers x)) ∈ frattini ↥(Q ⊔ zpowers x) := by
    apply hfrat
    intro b
    have h1 : (conjAction B (Q ⊔ zpowers x) hBnormP b ⟨x, hxP⟩ : ↥(Q ⊔ zpowers x)) =
        ⟨x, hxP⟩ := by
      apply Subtype.ext
      show (b : G) * x * (b : G)⁻¹ = x
      rw [hxB b b.2]
      group
    rw [h1, mul_inv_cancel]
    exact one_mem _
  have hdec : ∀ y ∈ Q ⊔ zpowers x, y ∈ Q ∨ ∃ q ∈ Q, y = q * x := by
    intro y hy
    have hy' : y ∈ ((Q ⊔ zpowers x : Subgroup G) : Set G) := hy
    rw [coe_mul_of_right_le_normalizer_left Q (zpowers x) hZN] at hy'
    obtain ⟨q, hq, z, hz, rfl⟩ := hy'
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
    rcases Int.even_or_odd' k with ⟨n, rfl | rfl⟩
    · left
      have h1 : x ^ (2 * n) = 1 := by rw [zpow_mul, zpow_two, hxx, one_zpow]
      show q * x ^ (2 * n) ∈ Q
      rw [h1, mul_one]
      exact hq
    · right
      refine ⟨q, hq, ?_⟩
      have h1 : x ^ (2 * n + 1) = x := by
        rw [zpow_add, zpow_mul, zpow_two, hxx, one_zpow, one_mul, zpow_one]
      show q * x ^ (2 * n + 1) = q * x
      rw [h1]
  have hnormal : (Q.subgroupOf (Q ⊔ zpowers x)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).mpr (sup_le Subgroup.le_normalizer hZN)
  have hquot : ∀ a : ↥(Q ⊔ zpowers x) ⧸ Q.subgroupOf (Q ⊔ zpowers x),
      a = 1 ∨ a = QuotientGroup.mk ⟨x, hxP⟩ := by
    intro a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective a
    rcases hdec y y.2 with h | ⟨q, hq, hyq⟩
    · left
      exact (QuotientGroup.eq_one_iff y).mpr h
    · right
      rw [QuotientGroup.eq]
      show ((y : G))⁻¹ * x ∈ Q
      rw [hyq]
      have h1 : (q * x)⁻¹ * x = x * q⁻¹ * x⁻¹ := by
        calc (q * x)⁻¹ * x = x⁻¹ * q⁻¹ * x := by group
          _ = x * q⁻¹ * x⁻¹ := by rw [hxinv]
      rw [h1]
      exact hxnorm _ (Q.inv_mem hq)
  have hFle : frattini ↥(Q ⊔ zpowers x) ≤ Q.subgroupOf (Q ⊔ zpowers x) := by
    refine CFSG.SectionRank.Ccomm.frattini_le_of_quotient_elementary (p := 2)
      (Q.subgroupOf (Q ⊔ zpowers x)) (fun a b => ?_) (fun a => ?_)
    · rcases hquot a with rfl | rfl <;> rcases hquot b with rfl | rfl <;> simp
    · rcases hquot a with rfl | rfl
      · simp
      · rw [← QuotientGroup.mk_pow]
        have h1 : (⟨x, hxP⟩ : ↥(Q ⊔ zpowers x)) ^ 2 = 1 := Subtype.ext (by simpa using hx2)
        rw [h1]
        exact QuotientGroup.mk_one _
  exact hFle hx_frat

theorem fixed_mem_commutator {X B : Type*} [Group X] [Finite X] [Group B] [Finite B]
    (hX : IsPGroup 2 X) (φ : B →* MulAut X) (hcard : Nat.card B = 9)
    (hfix0 : ∀ x : X, (∀ b : B, (φ b x) * x⁻¹ ∈ frattini X) → x ∈ frattini X)
    {c : X} (hc : ∀ b : B, φ b c = c) : c ∈ commutator X := by
  classical
  have : Fintype B := Fintype.ofFinite B
  have : Fact (IsPGroup 2 X) := ⟨hX⟩
  have hcomm : IsMulCommutative (X ⧸ commutator X) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr le_rfl
  let : CommGroup (X ⧸ commutator X) := IsMulCommutative.instCommGroup
  let : MulDistribMulAction B X := MulDistribMulAction.compHom X φ
  let := CFSG.PreuniquenessRankFour.Helpers.characteristic_quotient_mulDistribMulAction
    (acting := B) (commutator X)
  have hsm : ∀ (b : B) (x : X), b • (QuotientGroup.mk x : X ⧸ commutator X) =
      QuotientGroup.mk (φ b x) := fun b x => rfl
  have hM : IsPGroup 2 (X ⧸ commutator X) := hX.to_quotient (commutator X)
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2)).mp hM
  have hA : ∀ m : X ⧸ commutator X, (∀ b : B, b • m = m) → ∃ y : X ⧸ commutator X, y ^ 2 = m := by
    intro m hm
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective m
    have h1 : ∀ b : B, φ b x * x⁻¹ ∈ frattini X := fun b => by
      have h2 := hm b
      rw [hsm, QuotientGroup.eq_iff_div_mem, div_eq_mul_inv] at h2
      exact CFSG.commutator_le_frattini_of_isPGroup (R := X) (p := 2) h2
    have h3 := hfix0 x h1
    rw [CFSG.frattini_eq_closure_commutator_union_powers (p := 2)] at h3
    have h4 : Subgroup.closure (((commutator X : Subgroup X) : Set X) ∪
        Set.range (fun x : X => x ^ 2)) ≤
        (powMonoidHom 2 : (X ⧸ commutator X) →* (X ⧸ commutator X)).range.comap
          (QuotientGroup.mk' (commutator X)) := by
      rw [Subgroup.closure_le]
      rintro w (hw | ⟨z, rfl⟩)
      · refine ⟨1, ?_⟩
        rw [map_one]
        exact ((QuotientGroup.eq_one_iff w).mpr hw).symm
      · exact ⟨QuotientGroup.mk z, by simp [powMonoidHom_apply]⟩
    obtain ⟨y, hy⟩ := h4 h3
    exact ⟨y, by simpa [powMonoidHom_apply] using hy⟩
  have hcop : Nat.Coprime (Nat.card (X ⧸ commutator X)) 9 := by
    rw [ha]
    exact Nat.Coprime.pow_left a (by norm_num)
  have hbij := Nat.Coprime.pow_left_bijective (G := X ⧸ commutator X) hcop
  have hB' : ∀ m : X ⧸ commutator X, (∀ b : B, b • m = m) →
      (∃ y : X ⧸ commutator X, y ^ 2 = m) →
      ∃ z : X ⧸ commutator X, z ^ 2 = m ∧ ∀ b : B, b • z = z := by
    intro m hm hsq
    obtain ⟨y, hy⟩ := hsq
    obtain ⟨n, hn⟩ : ∃ n : X ⧸ commutator X, n = ∏ b : B, b • y := ⟨_, rfl⟩
    have hnfix : ∀ b' : B, b' • n = n := by
      intro b'
      rw [hn, Finset.smul_prod']
      simp only [smul_smul]
      exact Fintype.prod_equiv (Equiv.mulLeft b') _ _ (fun b => rfl)
    have hn2 : n ^ 2 = m ^ 9 := by
      rw [hn, ← Finset.prod_pow]
      calc ∏ b : B, (b • y) ^ 2 = ∏ b : B, b • y ^ 2 := by simp only [smul_pow']
        _ = ∏ b : B, m := by simp only [hy, hm]
        _ = m ^ 9 := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_eq_nat_card, hcard]
    obtain ⟨z, hz⟩ := hbij.surjective n
    have hz' : z ^ 9 = n := hz
    refine ⟨z, hbij.injective ?_, fun b => hbij.injective ?_⟩
    · show (z ^ 2) ^ 9 = m ^ 9
      calc (z ^ 2) ^ 9 = (z ^ 9) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
        _ = n ^ 2 := by rw [hz']
        _ = m ^ 9 := hn2
    · show (b • z) ^ 9 = z ^ 9
      calc (b • z) ^ 9 = b • z ^ 9 := (smul_pow' b z 9).symm
        _ = b • n := by rw [hz']
        _ = n := hnfix b
        _ = z ^ 9 := hz'.symm
  have hstep : ∀ m : X ⧸ commutator X, (∀ b : B, b • m = m) →
      ∃ z : X ⧸ commutator X, z ^ 2 = m ∧ ∀ b : B, b • z = z := fun m hm =>
    hB' m hm (hA m hm)
  have hdescent : ∀ j : ℕ, ∀ m : X ⧸ commutator X, (∀ b : B, b • m = m) →
      ∃ z : X ⧸ commutator X, z ^ (2 ^ j) = m ∧ ∀ b : B, b • z = z := by
    intro j
    induction j with
    | zero => exact fun m hm => ⟨m, by simp, hm⟩
    | succ j ih =>
      intro m hm
      obtain ⟨z₁, hz₁, hz₁fix⟩ := hstep m hm
      obtain ⟨z, hz, hzfix⟩ := ih z₁ hz₁fix
      refine ⟨z, ?_, hzfix⟩
      rw [pow_succ, pow_mul, hz, hz₁]
  obtain ⟨z, hz, -⟩ := hdescent a (QuotientGroup.mk c) (fun b => by rw [hsm, hc b])
  have h1 : (QuotientGroup.mk c : X ⧸ commutator X) = 1 := by
    rw [← hz, ← ha]
    exact pow_card_eq_one'
  exact (QuotientGroup.eq_one_iff c).mp h1

end CFSG.GH74.E2
