module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54F3Sp
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54SU
public import CFSG.LieType.Steinberg.CentralExt.UnitaryHigher
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54F3Odd
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54F3SL
public import CFSG.Sporadic.Suz.Setup
public import CFSG.Sporadic.Suz.W64Spec

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P54.F3

open CFSG Subgroup Assembly.LowTwoRank Blueprint.Multiplier CFSG.ClassicalInvolution.Models
open CFSG.ClassicalInvolution.Phan (Su blockEmb blockEmb_injective blockMat blockMat_apply)
open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open Matrix
open scoped MatrixGroups

namespace SU

variable {K : Type} [Field K] [Finite K] [Fact (Nat.Prime 3)] [CharP K 3]

theorem rawF3_su (hK : Nat.card K = (3 ^ 1) ^ 2) {n : ℕ} (hn4 : 4 ≤ n) {a : Su K 3 1 n}
    (ha : suMat a = -1) : RawF3 (Su K 3 1 n) a := by
  have hoddK : Odd (Nat.card K) := by
    rw [hK]
    decide
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hoddK
  have hn : 2 ≤ n := by omega
  have hF3 : Nat.card (LieType.Steinberg.fixedSubfield K 3 1) = 3 := by
    rw [LieType.Steinberg.card_fixedSubfield hK, pow_one]
  have hodd : Odd (Nat.card (LieType.Steinberg.fixedSubfield K 3 1)) := by
    rw [hF3]
    decide
  obtain ⟨-, hZU⟩ := SU.su_facts hK (by norm_num : 3 ≠ 2) (n := n) (by omega)
  have haZ : a ∈ center (Su K 3 1 n) := by
    rw [mem_center_iff]
    intro g
    apply suMat_injective
    rw [suMat_mul, suMat_mul, ha, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, Matrix.one_mul]
  set u := rootInvSU K 3 1 hn with hu
  have hcl := isClassicalSL2_rootSU2 hK (by norm_num : 3 ≠ 2) hn
  have huZ : u ∉ center (Su K 3 1 n) := by
    intro h
    obtain ⟨s, hs⟩ := hZU u h
    have hum : suMat u = Matrix.scalar (Fin n) (s : K) := by
      rw [suMat, ← hs, Matrix.GeneralLinearGroup.coe_scalar]
    rw [hu, suMat_rootInvSU, negBlock_eq_diagonal] at hum
    have e0 := congrFun (congrFun hum ⟨0, by omega⟩) ⟨0, by omega⟩
    have e2 := congrFun (congrFun hum ⟨2, by omega⟩) ⟨2, by omega⟩
    simp only [Matrix.diagonal_apply_eq, Matrix.scalar_apply] at e0 e2
    rw [ite_eq_left (by simp)] at e0
    rw [ite_eq_right (by simp)] at e2
    exact h2 (by linear_combination e2 - e0)
  obtain ⟨eK⟩ := nonempty_sl2_equiv_zmod_three hF3
  obtain ⟨eL⟩ := hcl.nonempty_mulEquiv
  have hJ₁Z := inf_center_eq_bot_of_equiv_sl2 hodd eL hcl.mem hcl.orderOf_eq_two huZ
  have hJ₁n := (isLongRootSU2_standard hn).normal_subgroupOf_centralizer hK
    (by norm_num : 3 ≠ 2)
  have hj : 2 + (n - 2) ≤ n := by omega
  set J₂ := (blockEmb K 3 1 n (n - 2) 2 hj).range with hJ₂
  have hJ₂' : J₂ = longRootGroupSU K 3 1 (-negBlock K n 0) := by
    rw [hJ₂, SU.range_blockEmb_eq_longRootGroupSUK h2 hj, SL.negBlockK_two_eq_neg n hn]
  let eJ : Su K 3 1 (n - 2) ≃* J₂ := MonoidHom.ofInjective (blockEmb_injective hj)
  have hcomm : ∀ {c : Su K 3 1 n}, c ∈ centralizer {u} →
      suMat c * -negBlock K n 0 = -negBlock K n 0 * suMat c := by
    intro c hc
    have h1 := congrArg suMat (mem_centralizer_singleton_iff.mp hc)
    simp only [suMat_mul, hu, suMat_rootInvSU] at h1
    rw [Matrix.mul_neg, Matrix.neg_mul, h1]
  have hJle : J₂ ≤ centralizer {u} := by
    intro x hx
    rw [hJ₂'] at hx
    rw [mem_centralizer_singleton_iff]
    apply suMat_injective
    have h1 := (mem_longRootGroupSU.mp hx).1
    rw [Matrix.mul_neg, Matrix.neg_mul, neg_inj] at h1
    simp only [suMat_mul, hu, suMat_rootInvSU]
    exact h1
  have hJn : (J₂.subgroupOf (centralizer {u})).Normal := by
    rw [normal_subgroupOf_iff_le_normalizer hJle]
    intro c hc
    rw [mem_normalizer_iff]
    intro x
    rw [hJ₂']
    constructor
    · exact fun hx => conj_mem_longRootGroupSU_of_commute (hcomm hc) hx
    · intro hx
      have := conj_mem_longRootGroupSU_of_commute (hcomm (inv_mem hc)) hx
      rwa [show c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x by group] at this
  have hauJ : a * u ∈ J₂ := by
    rw [hJ₂', mem_longRootGroupSU, suMat_mul, ha, hu, suMat_rootInvSU, neg_one_mul]
    refine ⟨rfl, ?_⟩
    rw [Matrix.neg_mul, Matrix.mul_add, Matrix.mul_one, Matrix.mul_neg, negBlock_mul_self]
    abel
  have hau2 : orderOf (a * u) = 2 := by
    have hcomm' : a * u = u * a := (mem_center_iff.mp haZ u).symm
    have ha1 : a ≠ 1 := fun h => by
      have h1 := congrArg suMat h
      rw [ha, suMat_one] at h1
      have h3 := congrFun (congrFun h1 ⟨0, by omega⟩) ⟨0, by omega⟩
      simp only [Matrix.neg_apply, Matrix.one_apply_eq] at h3
      exact h2 (by linear_combination -h3)
    have ha2 : orderOf a = 2 :=
      orderOf_eq_prime (suMat_injective (by rw [sq, suMat_mul, ha, suMat_one]; simp)) ha1
    exact T1.F3.orderOf_mul_of_commute ha2 hcl.orderOf_eq_two hcomm' (fun h => huZ (h ▸ haZ))
  have hauZ : a * u ∉ center (Su K 3 1 n) := fun h => huZ (by
    have h1 : u = a⁻¹ * (a * u) := by group
    rw [h1]
    exact mul_mem (inv_mem haZ) h)
  have h2J : 2 ∣ Nat.card J₂ := by
    have h1 := orderOf_dvd_natCard (⟨a * u, hauJ⟩ : J₂)
    rwa [Subgroup.orderOf_mk, hau2] at h1
  refine ⟨u, hcl.orderOf_eq_two, huZ, rootSU2 K 3 1 hn, J₂, hcl.le_centralizer,
    hJ₁n.isSubnormal, hcl.mem, hJ₁Z, ⟨eL.trans eK⟩, ?_, .inr hauJ⟩
  rcases Nat.lt_or_ge n 5 with hn5 | hn5
  ·
    obtain rfl : n = 4 := by omega
    obtain ⟨e2⟩ := nonempty_sl2_mulEquiv_su_two (K := K) (p := 3) (f := 1) hK
    let eJ₂ : ↥J₂ ≃* SL(2, LieType.Steinberg.fixedSubfield K 3 1) := eJ.symm.trans e2.symm
    exact .inr ⟨hJle, hJn.isSubnormal, inf_center_eq_bot_of_equiv_sl2 hodd eJ₂ hauJ hau2 hauZ,
      ⟨eJ₂.trans eK⟩⟩
  ·
    obtain ⟨hqm, -⟩ := SU.su_facts hK (by norm_num : 3 ≠ 2) (n := n - 2) (by omega)
    have hqJ : IsQuasisimple J₂ := LocalCores.isQuasisimple_of_mulEquiv eJ hqm
    have hnq : (n - 2, 3 ^ 1) ≠ (3, 2) := fun h => by
      simp only [Prod.mk.injEq] at h
      omega
    let eJ' : StatedSU (n - 2) (3 ^ 1) K ≃* J₂ := (SU.equivStated hK (n - 2)).symm.trans eJ
    have hZJ : ((StatedScalars (Fin (n - 2)) K).subgroupOf (StatedSU (n - 2) (3 ^ 1) K)).map
        eJ'.toMonoidHom = center ↥J₂ := by
      rw [← (isQuasisimple_statedSU_of_card hK (by omega) hnq).2]
      exact Subgroup.map_center_eq eJ'
    have hlie : Blueprint.LieModel (↥J₂ ⧸ center ↥J₂) .PSU (n - 2) 3 1 := by
      refine Or.inl ⟨by decide, ⟨Nat.prime_three, le_rfl, by omega, hnq⟩, K, inferInstance,
        inferInstance, hK, ⟨(QuotientGroup.congr _ _ eJ' hZJ).symm⟩⟩
    exact .inl ⟨⟨hJle, hJn.isSubnormal, SL.isTwoQuasisimple_of_isQuasisimple hqJ h2J⟩, hqJ,
      ⟨.PSU, n - 2, hlie⟩⟩

end SU

theorem statedSU_exists_section_of_two {K : Type} [Field K] [Finite K] {p f : ℕ}
    [Fact p.Prime] [CharP K p] (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) {n : ℕ}
    (hn : 2 ≤ n) {E : Type} [Group E] [Finite E] {π : E →* StatedSU n (p ^ f) K}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ center E) (h2 : IsPGroup 2 π.ker) :
    ∃ s : StatedSU n (p ^ f) K →* E, ∀ g, π (s g) = g := by
  set ψ := equivStatedSU hK n
  have hker : (ψ.symm.toMonoidHom.comp π).ker = π.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ ψ.symm.injective]
  obtain ⟨s, hs, -⟩ := LieType.Steinberg.su_central_two_extension_splitting hK hp2 hn
    (π := ψ.symm.toMonoidHom.comp π) (ψ.symm.surjective.comp hπ) (hker ▸ hcen) (hker ▸ h2)
  refine ⟨s.comp ψ.symm.toMonoidHom, fun g => ψ.symm.injective ?_⟩
  exact hs (ψ.symm g)

theorem rowSUThree (hG : GriessNativeTable) : RowSUThree := by
  intro Y _ _ hq hZ τ n ⟨hτ, hn2⟩ hlie hc t ht htZ
  subst hτ
  have hlie' := hlie
  rcases hlie' with ⟨-, ⟨-, -, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
  rotate_left
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  have hn4 : 4 ≤ n := by
    obtain ⟨k, hk⟩ := hn2
    omega
  have hcZ := hc (n / 2) 1 (by omega) (by omega)
    (.inr (by rw [Nat.two_mul_div_two_of_even hn2]; exact hlie))
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP K 3 := LieType.BorelTits.charP_of_natCard_eq (f := 2 * 1)
    (by rw [hK, ← pow_mul, mul_comm])
  set U := StatedSU n (3 ^ 1) K
  set Z := (StatedScalars (Fin n) K).subgroupOf U
  obtain ⟨α, hαs, hαZ, hαk⟩ := exists_surjective_of_cover (β := QuotientGroup.mk' Z)
    (QuotientGroup.mk'_surjective _)
    (fun E _ _ π hπ hcen h2 => statedSU_exists_section_of_two hK (by norm_num) (by omega) hπ
      hcen h2) hq hZ e
  rw [QuotientGroup.ker_mk'] at hαZ hαk
  have hg0 : Nat.gcd n (3 ^ 1 + 1) ≠ 0 := (Nat.gcd_pos_of_pos_left _ (by omega)).ne'
  have hZY : Nat.card (center Y) = ordProj[2] (Nat.gcd n (3 ^ 1 + 1)) := by
    rw [hcZ]
    obtain ⟨-, ⟨eM⟩⟩ := hG _ .PSU n 3 1 hlie
    rw [Nat.card_congr eM.toEquiv, card_generic_prod_exceptional]
    simp only [genericOrders, mul_one]
    have hex : ¬ 2 ∣ (exceptionalOrders .PSU n 3 1).1 * (exceptionalOrders .PSU n 3 1).2 := by
      unfold exceptionalOrders
      split <;> simp_all
    have hpos : (exceptionalOrders .PSU n 3 1).1 * (exceptionalOrders .PSU n 3 1).2 ≠ 0 := by
      unfold exceptionalOrders
      split <;> simp_all
    rw [Nat.factorization_mul hg0 hpos, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hex, add_zero]
  have hψmem : ∀ x : Z, (α.comp Z.subtype) x ∈ center Y := fun x => hαZ ▸ mem_map_of_mem α x.2
  let ψ := (α.comp Z.subtype).codRestrict (center Y) hψmem
  have hψs : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    rw [← hαZ] at hy
    obtain ⟨c, hc, rfl⟩ := hy
    exact ⟨⟨c, hc⟩, rfl⟩
  have hψk : Nat.card ψ.ker = Nat.card α.ker := by
    have hmap : ψ.ker.map Z.subtype = α.ker := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact congrArg Subtype.val hy
      · intro hx
        exact ⟨⟨x, hαk hx⟩, Subtype.ext hx, rfl⟩
    rw [← hmap, Subgroup.card_map_of_injective Z.subtype_injective]
  have hcardZ : Nat.card Z = Nat.gcd n (3 ^ 1 + 1) :=
    (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_three hK (by omega)).2.2
  have hmul := Subgroup.card_ker_mul_card_of_surjective hψs
  rw [hψk, hZY, hcardZ] at hmul
  have hk : ¬ 2 ∣ Nat.card α.ker := by
    have h1 : Nat.card α.ker = ordCompl[2] (Nat.gcd n (3 ^ 1 + 1)) :=
      Nat.eq_of_mul_eq_mul_right (Nat.ordProj_pos _ 2) (by
        rw [hmul, mul_comm]
        exact (Nat.ordProj_mul_ordCompl_eq_self _ 2).symm)
    rw [h1]
    exact Nat.not_dvd_ordCompl Nat.prime_two hg0
  obtain ⟨a, ha2, hat⟩ := Frame.exists_involution_lift α hk ht (MonoidHom.mem_range.mpr (hαs t))
  have haZ : a ∈ Z := by
    have htU : t ∈ Z.map α := hαZ ▸ htZ
    obtain ⟨c, hc, hct⟩ := htU
    have h1 : a⁻¹ * c ∈ α.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hat, hct, inv_mul_cancel]
    have : a = c * (a⁻¹ * c)⁻¹ := by group
    rw [this]
    exact mul_mem hc (inv_mem (hαk h1))
  have ha1 : a ≠ 1 := fun h => by rw [h, orderOf_one] at ha2; exact absurd ha2 (by norm_num)
  have haa : a * a = 1 := by rw [← sq, ← ha2, pow_orderOf_eq_one]
  obtain ⟨c, hc⟩ := haZ
  have hc' : Matrix.GeneralLinearGroup.scalar (Fin n) c = (a : GL (Fin n) K) := hc
  have hamat : ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Matrix.scalar (Fin n) (c : K) := by
    rw [← hc', Matrix.GeneralLinearGroup.coe_scalar]
  have hc2 : (c : K) * c = 1 := by
    have h1 := congrArg (fun g : U => ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) haa
    simp only [Subgroup.coe_mul, Units.val_mul, OneMemClass.coe_one, Units.val_one, hamat] at h1
    have h3 := congrFun (congrFun h1 ⟨0, by omega⟩) ⟨0, by omega⟩
    simpa [Matrix.scalar_apply] using h3
  have hc1 : (c : K) ≠ 1 := fun h => ha1 (Subtype.ext (Units.ext (by
    rw [hamat, h, map_one, OneMemClass.coe_one, Units.val_one])))
  have hcm : (c : K) = -1 := (mul_self_eq_one_iff.mp hc2).resolve_left hc1
  set a' := (SU.equivStated hK n).symm a with ha'
  have ha'm : suMat a' = -1 := by
    have : ((a' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := rfl
    rw [suMat, this, hamat, hcm, map_neg, map_one]
  obtain ⟨hqSU, -⟩ := SU.su_facts hK (by norm_num : 3 ≠ 2) (n := n) (by omega)
  set α' := α.comp (SU.equivStated hK n).toMonoidHom with hα'
  have hα's : Function.Surjective α' := hαs.comp (SU.equivStated hK n).surjective
  have hnq' : (n, 3 ^ 1) ≠ (3, 2) := fun h => by
    simp only [Prod.mk.injEq] at h
    omega
  have hZcen : Z = center U := (isQuasisimple_statedSU_of_card hK (by omega) hnq').2.symm
  have hα'k : α'.ker ≤ center (Su K 3 1 n) := by
    intro x hx
    have h0 : (SU.equivStated hK n) x ∈ α.ker := hx
    have h1 : (SU.equivStated hK n) x ∈ center U := hZcen ▸ hαk h0
    rw [← Subgroup.map_center_eq (SU.equivStated hK n)] at h1
    obtain ⟨y, hy, hyx⟩ := h1
    rw [(SU.equivStated hK n).injective hyx] at hy
    exact hy
  have ha'Z : a' ∈ center (Su K 3 1 n) := by
    rw [mem_center_iff]
    intro g
    apply suMat_injective
    rw [suMat_mul, suMat_mul, ha'm, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul,
      Matrix.one_mul]
  have hα'a : α' a' = t := by
    rw [hα', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ha', MulEquiv.apply_symm_apply, hat]
  rw [← hα'a]
  exact (SU.rawF3_su hK hn4 ha'm).concl3 hqSU hα's hα'k (by rw [hα'a]; exact ht) ha'Z

end CFSG.ComponentClassification.HarrisLit.T1.P54.F3
