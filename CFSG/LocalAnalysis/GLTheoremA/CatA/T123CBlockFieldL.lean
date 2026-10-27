module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CBlockAbs
import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CBlockLinA
import CFSG.RankThree.SteinbergR3ELinearFieldDescent
import CFSG.RankThree.PartOne.KC.LinearSubfieldFixedPoints

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T123CB

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCLinearSubfield
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open scoped commutatorElement

private theorem isQuasisimple_of_simple_nonabelian {X : Type*} [Group X] [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a) : CFSG.Open.IsQuasisimple X := by
  have hZ : Subgroup.center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hnab
      exact absurd ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a) hab
  refine ⟨?_, ((QuotientGroup.quotientMulEquivOfEq hZ).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with h | h
  · obtain ⟨a, b, hab⟩ := hnab
    have h1 : ⁅a, b⁆ = 1 := by
      rw [← Subgroup.mem_bot, ← h]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    exact absurd (commutatorElement_eq_one_iff_mul_comm.mp h1) hab
  · exact h

private theorem exists_char_card_of_finite (K : Type) [Field K] [Finite K] :
    ∃ ℓ f : ℕ, ℓ.Prime ∧ CharP K ℓ ∧ 1 ≤ f ∧ Nat.card K = ℓ ^ f := by
  have := Fintype.ofFinite K
  obtain ⟨ℓ, hcharK⟩ := CharP.exists K
  have hℓ : ℓ.Prime := CharP.char_is_prime K ℓ
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨n, -, hn⟩ := FiniteField.card K ℓ
  exact ⟨ℓ, n, hℓ, hcharK, n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩

theorem not_dvd_sub_one_of_dvd_add_one {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : 1 ≤ q)
    (hdvd : p ∣ q + 1) : ¬ p ∣ q - 1 := by
  intro h
  have h2 : p ∣ q + 1 - (q - 1) := Nat.dvd_sub hdvd h
  rw [show q + 1 - (q - 1) = 2 by omega] at h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)

theorem dvd_card_projectiveSL_of_dvd_succ {m : ℕ} {k : Type} [Field k] [Finite k] (hm : 2 ≤ m)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ Nat.card k + 1) :
    p ∣ Nat.card (projectiveSL m k) := by
  classical
  letI : Fintype k := Fintype.ofFinite k
  haveI := Fact.mk hp
  have hk1 : 1 < Nat.card k := Finite.one_lt_card
  have hq1 := not_dvd_sub_one_of_dvd_add_one hp hp2 hk1.le hdvd
  have hq2 : p ∣ Nat.card k ^ 2 - 1 := by
    obtain ⟨r, hr⟩ : ∃ r, Nat.card k = r + 1 := ⟨Nat.card k - 1, by omega⟩
    have h1 : (r + 1) ^ 2 = (r + 1 + 1) * r + 1 := by ring
    rw [hr, h1, Nat.add_sub_cancel]
    rw [hr] at hdvd
    exact Dvd.dvd.mul_right hdvd r
  obtain ⟨s, hs, hsc⟩ := exists_pow_not_mem_center_of_dvd (E := k) (m := m) hp hm
    (by rwa [← Nat.card_eq_fintype_card]) (by rwa [← Nat.card_eq_fintype_card])
  have hs1 : proj m k s ≠ 1 := fun h => hsc (scalars_le_center m k (proj_eq_one_iff.mp h))
  have hord : orderOf (proj m k s) = p := orderOf_eq_prime (by rw [← map_pow, hs, map_one]) hs1
  rw [← hord]
  exact orderOf_dvd_natCard _

theorem fieldBlockAt_projectiveSL_of_dvd_succ {n : ℕ} {K : Type} [Field K] [Finite K]
    (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ Nat.card K + 1) :
    FieldBlockAt p (projectiveSL n K) := by
  classical
  haveI := Fact.mk hp
  intro α hαp hαo
  obtain ⟨ℓ, f, hℓ, hchar, hf1, hK⟩ := exists_char_card_of_finite K
  haveI := hchar
  have hα1 : α ≠ 1 := fun h => hαo 1 (by rw [h, map_one])
  have hord : orderOf α = p := orderOf_eq_prime hαp hα1
  have hK1 : 1 < Nat.card K := Finite.one_lt_card
  have hq1 := not_dvd_sub_one_of_dvd_add_one hp hp2 hK1.le hdvd
  have hpℓ : p ≠ ℓ := by
    rintro rfl
    have h1 : p ∣ Nat.card K := by rw [hK]; exact dvd_pow_self p (by omega)
    have h2 : p ∣ Nat.card K + 1 - Nat.card K := Nat.dvd_sub hdvd h1
    rw [Nat.add_sub_cancel_left] at h2
    exact hp.one_lt.ne' (Nat.dvd_one.mp h2)
  have hαE : α ∈ semilinearAutGroup n K :=
    CFSG.ComponentClassification.UnbalancedCatalog.EvenLinearSL.mem_semilinearAutGroup_of_odd hn
      (by rw [hord]; exact hp.odd_of_ne_two hp2)
  have hαD : α ∉ linearAutGroup n K := by
    intro hD
    haveI := inner_normal (projectiveSL n K)
    have hm : (inner (projectiveSL n K)).relIndex (linearAutGroup n K) ∣ Nat.card K - 1 :=
      (UnitaryHigher.relIndex_inner_linearAutGroup_dvd (k := K) (by omega)).trans
        (Nat.gcd_dvd_right _ _)
    have hpow := Subgroup.pow_index_mem ((inner (projectiveSL n K)).subgroupOf
      (linearAutGroup n K)) (⟨α, hD⟩ : linearAutGroup n K)
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow] at hpow
    have hcop : Nat.Coprime ((inner (projectiveSL n K)).relIndex (linearAutGroup n K))
        (orderOf α) := by
      rw [hord]
      exact ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => hq1 (h.trans hm)).symm
    obtain ⟨j, hj⟩ := exists_pow_eq_self_of_coprime hcop
    have hαI : α ∈ inner (projectiveSL n K) := by
      rw [← hj]
      exact Subgroup.pow_mem _ hpow j
    obtain ⟨t, ht⟩ := hαI
    exact hαo t ht
  obtain ⟨-, -, -, -, -, -, -, hdesc⟩ :=
    CFSG.RankThree.LinearDescent.higher_linear_prime_semilinear_field_descent hℓ hf1 hn hK
  obtain ⟨hpf, σ, hσ, ⟨h, -, hαh⟩, hkcard⟩ := hdesc p hp hpℓ α hαE hαD hord
  set k := semilinearFixedSubfield σ with hkdef
  have hk : ∀ x, x ∈ k ↔ σ x = x := fun x => RingHom.mem_eqLocusField
  have hσp : σ ^ p = 1 := hσ ▸ pow_orderOf_eq_one σ
  have hpKu : ¬ p ∣ Nat.card Kˣ := by
    rw [Nat.card_units]
    exact hq1
  have hset := fixed_points_eq_range (n := n) hk (by omega) (root_descent_of_not_dvd hp hk hσp hpKu)
  have hfix := fixingSubgroup_range_linearSubfieldInclusion (n := n) hk hn
  obtain ⟨hsH, hnH⟩ := simple_nonabelian_range_linearSubfieldInclusion hn k
  have hinj := linearSubfieldInclusion_injective (by omega : 0 < n) k
  set H := (linearSubfieldInclusion n k).range with hHdef
  set M := H.map (h : MulAut (projectiveSL n K)).toMonoidHom with hMdef
  have hMeq : fixSub α = M := by
    ext t
    rw [mem_fixSub, hαh, Subgroup.mem_map]
    constructor
    · intro ht
      refine ⟨h⁻¹ t, ?_, by simp⟩
      have h1 : fieldAut n K σ (h⁻¹ t) = h⁻¹ t := by
        have := congrArg (h⁻¹ : MulAut (projectiveSL n K)) ht
        simpa [MulAut.mul_apply] using this
      exact (Set.ext_iff.mp hset (h⁻¹ t)).mp h1
    · rintro ⟨y, hy, rfl⟩
      have hy' : fieldAut n K σ y = y := (Set.ext_iff.mp hset y).mpr hy
      simp [MulAut.mul_apply, hy']
  let eM : ↥M ≃* ↥H := (Subgroup.equivMapOfInjective H _ h.injective).symm
  haveI := hsH
  haveI hsM : IsSimpleGroup ↥M := eM.isSimpleGroup
  have hnM : ∃ a b : ↥M, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    apply hnH
    intro x y
    apply eM.symm.injective
    rw [map_mul, map_mul]
    exact hc _ _
  have hZM : Subgroup.center ↥M = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥M) with hc | hc
    · exact hc
    · obtain ⟨a, b, hab⟩ := hnM
      exact absurd ((Subgroup.mem_center_iff.mp (hc ▸ Subgroup.mem_top b)) a) hab
  have hcardM : Nat.card (↥M ⧸ Subgroup.center ↥M) = Nat.card (projectiveSL n k) := by
    rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZM).trans
      QuotientGroup.quotientBot).toEquiv, Nat.card_congr eM.toEquiv,
      Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm]
  have hk0 : p ∣ Nat.card k + 1 := by
    have h1 : Nat.card K = Nat.card k ^ p := by
      rw [hkcard, hK, ← pow_mul, Nat.div_mul_cancel hpf]
    rw [h1] at hdvd
    rw [← ZMod.natCast_eq_zero_iff] at hdvd ⊢
    push_cast at hdvd ⊢
    rwa [ZMod.pow_card] at hdvd
  refine ⟨M, ?_, ?_, fun P hP _ => hMeq ▸ hP, fun β hβ => ?_⟩
  · rw [hMeq]
    exact ⟨le_rfl, IsSubnormal.refl M, isQuasisimple_of_simple_nonabelian hnM⟩
  · rw [hcardM]
    exact dvd_card_projectiveSL_of_dvd_succ (by omega) hp hp2 hk0
  ·
    have hβ' : h⁻¹ * β * h ∈ fixingSubgroup (MulAut (projectiveSL n K))
        (H : Set (projectiveSL n K)) := by
      rw [mem_fixingSubgroup_iff]
      intro y hy
      have h1 : β (h y) = h y := hβ (h y) ⟨y, hy, rfl⟩
      change (h⁻¹ * β * h) y = y
      simp [MulAut.mul_apply, h1]
    rw [hfix] at hβ'
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hβ'
    refine Subgroup.mem_zpowers_iff.mpr ⟨j, ?_⟩
    rw [hαh, conj_zpow, hj]
    group

end CFSG.LocalAnalysis.GLTheoremA.T123CB

end
