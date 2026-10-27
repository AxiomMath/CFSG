module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54SL
public import CFSG.LieType.Steinberg.CentralExt.PSUMultiplier

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P54

open CFSG Subgroup Assembly.LowTwoRank CFSG.ClassicalInvolution.Models
open CFSG.ClassicalInvolution.Phan (Su blockEmb blockEmb_injective blockMat blockMat_apply
  blockMat_mul blockMat_one blockMat_injective det_blockMat conjTr_blockMat)
open CFSG.ClassicalInvolution.WeakCT (blockSL coe_blockSL)
open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open Matrix
open scoped MatrixGroups

namespace SU

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem blockEmb_mem_longRootGroupSUK {n j k : ℕ} (hj : j + k ≤ n) (A : Su K p f k) :
    blockEmb K p f n k j hj A ∈ longRootGroupSU K p f (SL.negBlockK K n j k) :=
  SL.blockSL_mem_longRootGroupK (K := K) hj (suToSL (unitaryInvolution K p f) k A)

theorem exists_blockEmb_of_mem_longRootGroupSUK (h2 : (2 : K) ≠ 0) {n j k : ℕ} (hj : j + k ≤ n)
    {x : Su K p f n} (hx : x ∈ longRootGroupSU K p f (SL.negBlockK K n j k)) :
    ∃ A : Su K p f k, blockEmb K p f n k j hj A = x := by
  obtain ⟨A, hA⟩ := SL.exists_blockSL_of_mem_longRootGroupK h2 hj hx
  have hAm : blockMat n j (A : Matrix (Fin k) (Fin k) K) = suMat x :=
    congrArg (fun z : SL(n, K) => (z : Matrix (Fin n) (Fin n) K)) hA
  have hAu : conjTr (unitaryInvolution K p f) (A : Matrix (Fin k) (Fin k) K) *
      (A : Matrix (Fin k) (Fin k) K) = 1 := by
    have hx1 : conjTr (unitaryInvolution K p f) (suMat x) * suMat x = 1 := x.2.2
    rw [← hAm, conjTr_blockMat, ← blockMat_mul hj] at hx1
    exact blockMat_injective hj (by rw [hx1, blockMat_one])
  refine ⟨⟨Matrix.SpecialLinearGroup.toGL A, ⟨by simp, by simpa using hAu⟩⟩, ?_⟩
  exact suMat_injective (by rw [suMat_blockEmb]; simpa [suMat] using hAm)

theorem range_blockEmb_eq_longRootGroupSUK (h2 : (2 : K) ≠ 0) {n j k : ℕ} (hj : j + k ≤ n) :
    (blockEmb K p f n k j hj).range = longRootGroupSU K p f (SL.negBlockK K n j k) := by
  ext x
  constructor
  · rintro ⟨A, rfl⟩
    exact blockEmb_mem_longRootGroupSUK hj A
  · intro hx
    obtain ⟨A, hA⟩ := exists_blockEmb_of_mem_longRootGroupSUK h2 hj hx
    exact ⟨A, hA⟩

@[expose] def equivStated (hK : Nat.card K = (p ^ f) ^ 2) (n : ℕ) :
    Su K p f n ≃* StatedSU n (p ^ f) K :=
  MulEquiv.subgroupCongr (SUid_eq_statedSU hK n)

theorem su_facts (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) {n : ℕ} (hn : 3 ≤ n) :
    IsQuasisimple (Su K p f n) ∧ ∀ x ∈ center (Su K p f n),
      ∃ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin n) c = (x : GL (Fin n) K) := by
  have hnq : (n, p ^ f) ≠ (3, 2) := fun h => by
    simp only [Prod.mk.injEq] at h
    exact prime_pow_ne_two_of_ne_two hp2 f h.2
  obtain ⟨hq, hZ⟩ := isQuasisimple_statedSU_of_card hK hn hnq
  refine ⟨LocalCores.isQuasisimple_of_mulEquiv (equivStated hK n).symm hq, fun x hx => ?_⟩
  have h1 : equivStated hK n x ∈ center (StatedSU n (p ^ f) K) := by
    rw [← Subgroup.map_center_eq (equivStated hK n)]
    exact mem_map_of_mem _ hx
  rw [hZ] at h1
  obtain ⟨c, hc⟩ := h1
  exact ⟨c, hc⟩

theorem concl_su (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) {n : ℕ} (hn4 : 4 ≤ n)
    (h5 : 5 ≤ p ^ f) {a : Su K p f n} (ha : suMat a = -1) :
    Concl p f (Su K p f n) a := by
  have hp : p.Prime := Fact.out
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two hp2
  have hf : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr fun h => by rw [h, pow_zero] at h5; omega
  have hn : 2 ≤ n := by omega
  obtain ⟨hqU, hZU⟩ := su_facts hK hp2 (n := n) (by omega)
  have haZ : a ∈ center (Su K p f n) := by
    rw [mem_center_iff]
    intro g
    apply suMat_injective
    rw [suMat_mul, suMat_mul, ha, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, Matrix.one_mul]
  have ha1 : a ≠ 1 := fun h => by
    have h1 := congrArg suMat h
    rw [ha, suMat_one] at h1
    have h3 := congrFun (congrFun h1 ⟨0, by omega⟩) ⟨0, by omega⟩
    simp only [Matrix.neg_apply, Matrix.one_apply_eq] at h3
    exact h2 (by linear_combination -h3)
  have ha2 : a * a = 1 := suMat_injective (by rw [suMat_mul, ha, suMat_one]; simp)
  set u := rootInvSU K p f hn with hu
  have hcl := isClassicalSL2_rootSU2 hK hp2 hn
  have huZ : u ∉ center (Su K p f n) := by
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
  obtain ⟨eL⟩ := hcl.nonempty_mulEquiv
  have hsL : IsSLTwoOver (p ^ f) (rootSU2 K p f hn) := by
    have := Fintype.ofFinite (LieType.Steinberg.fixedSubfield K p f)
    exact ⟨LieType.Steinberg.fixedSubfield K p f, inferInstance, inferInstance,
      by rw [← Nat.card_eq_fintype_card, LieType.Steinberg.card_fixedSubfield hK], ⟨eL⟩⟩
  obtain ⟨hqL, hOL⟩ := isQuasisimple_of_isSLTwoOver hp hp2 h5 hsL
  have hj : 2 + (n - 2) ≤ n := by omega
  set J₂ := (blockEmb K p f n (n - 2) 2 hj).range with hJ₂
  have hJ₂' : J₂ = longRootGroupSU K p f (-negBlock K n 0) := by
    rw [hJ₂, range_blockEmb_eq_longRootGroupSUK h2 hj, SL.negBlockK_two_eq_neg n hn]
  let eJ : Su K p f (n - 2) ≃* J₂ := MonoidHom.ofInjective (blockEmb_injective hj)
  have hcomm : ∀ {c : Su K p f n}, c ∈ centralizer {u} →
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
    have huu : u * u = 1 := by rw [← sq, ← hcl.orderOf_eq_two, pow_orderOf_eq_one]
    refine orderOf_eq_prime ?_ fun h => huZ ?_
    · rw [sq]
      calc a * u * (a * u) = a * (u * a) * u := by group
        _ = a * (a * u) * u := by rw [← hcomm']
        _ = a * a * (u * u) := by group
        _ = 1 := by rw [ha2, huu, one_mul]
    · have : u = a⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [this]
      exact inv_mem haZ
  have h2J : 2 ∣ Nat.card J₂ := by
    have h1 := orderOf_dvd_natCard (⟨a * u, hauJ⟩ : J₂)
    rwa [Subgroup.orderOf_mk, hau2] at h1
  have hJ₂facts : IsQuasisimple J₂ ∧ ∃ (τ' : StatedLieTag) (n' : ℕ),
      Blueprint.LieModel (↥J₂ ⧸ Open.fusionZStar ↥J₂) τ' n' p f := by
    rcases Nat.lt_or_ge n 5 with hn5 | hn5
    ·
      obtain rfl : n = 4 := by omega
      obtain ⟨e2⟩ := nonempty_sl2_mulEquiv_su_two (K := K) (p := p) (f := f) hK
      have hsJ : IsSLTwoOver (p ^ f) J₂ := by
        have := Fintype.ofFinite (LieType.Steinberg.fixedSubfield K p f)
        exact ⟨LieType.Steinberg.fixedSubfield K p f, inferInstance, inferInstance,
          by rw [← Nat.card_eq_fintype_card, LieType.Steinberg.card_fixedSubfield hK],
          ⟨eJ.symm.trans e2.symm⟩⟩
      exact ⟨(isQuasisimple_of_isSLTwoOver hp hp2 h5 hsJ).1,
        .PSL, 2, lieModel_psl_of_isSLTwoOver hp hp2 h5 hsJ⟩
    ·
      obtain ⟨hqm, -⟩ := su_facts hK hp2 (n := n - 2) (by omega)
      have hqJ : IsQuasisimple J₂ := LocalCores.isQuasisimple_of_mulEquiv eJ hqm
      refine ⟨hqJ, .PSU, n - 2, ?_⟩
      have hnq : (n - 2, p ^ f) ≠ (3, 2) := fun h => by
        simp only [Prod.mk.injEq] at h
        omega
      let eJ' : StatedSU (n - 2) (p ^ f) K ≃* J₂ := (equivStated hK (n - 2)).symm.trans eJ
      have hZJ : ((StatedScalars (Fin (n - 2)) K).subgroupOf (StatedSU (n - 2) (p ^ f) K)).map
          eJ'.toMonoidHom = Open.fusionZStar ↥J₂ := by
        rw [fusionZStar_eq_center_of_isQuasisimple hqJ h2J,
          ← (isQuasisimple_statedSU_of_card hK (by omega) hnq).2]
        exact Subgroup.map_center_eq eJ'
      refine Or.inl ⟨by decide, ⟨hp, hf, by omega, ?_⟩, K, inferInstance, inferInstance, hK,
        ⟨(QuotientGroup.congr _ _ eJ' hZJ).symm⟩⟩
      intro h
      simp only [Prod.mk.injEq] at h
      omega
  obtain ⟨hqJ, hlie⟩ := hJ₂facts
  refine ⟨u, hcl.orderOf_eq_two, not_mem_fusionZStar hqU (orderOf_eq_prime (by rw [sq, ha2]) ha1)
    huZ, rootSU2 K p f hn, J₂,
    isTwoComponentIn_of_normal hcl.le_centralizer
      ((isLongRootSU2_standard hn).normal_subgroupOf_centralizer hK hp2) hqL hOL,
    ⟨hJle, Subgroup.Normal.isSubnormal hJn, SL.isTwoQuasisimple_of_isQuasisimple hqJ h2J⟩,
    fun h => ?_, hcl.mem, isSLTwoOver_quot hp hp2 h5 hsL, hlie, .inr hauJ⟩
  have huJ : u ∈ J₂ := h ▸ hcl.mem
  obtain ⟨A, hA⟩ := huJ
  have h1 := congrFun (congrFun (congrArg suMat hA) ⟨0, by omega⟩) ⟨0, by omega⟩
  rw [suMat_blockEmb, hu, suMat_rootInvSU, negBlock_eq_diagonal, Matrix.diagonal_apply_eq,
    blockMat_apply, dite_eq_right (by simp), ite_eq_left (by simp), Matrix.one_apply_eq] at h1
  exact h2 (by linear_combination h1)

end SU

theorem rowSU :
    RowSU := by
  intro Y _ _ hq hZ p hp hp2 τ n f ⟨hτ, hn2⟩ hlie h5 hpsl hc t ht htZ
  subst hτ
  have hlie' := hlie
  rcases hlie' with ⟨-, ⟨-, hf, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
  rotate_left
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  have hn4 : 4 ≤ n := by
    obtain ⟨k, hk⟩ := hn2
    omega
  have hcZ := hc (n / 2) f (by omega) (by omega)
    (.inr (by rw [Nat.two_mul_div_two_of_even hn2]; exact hlie))
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := LieType.BorelTits.charP_of_natCard_eq (f := 2 * f)
    (by rw [hK, ← pow_mul, mul_comm])
  have h5' : 4 ≤ p ^ f := by omega
  set U := StatedSU n (p ^ f) K
  set Z := (StatedScalars (Fin n) K).subgroupOf U
  obtain ⟨α, hαs, hαZ, hαk⟩ := exists_surjective_of_cover (β := QuotientGroup.mk' Z)
    (QuotientGroup.mk'_surjective _)
    (fun E _ _ π hπ hcen _ =>
      LieType.Steinberg.CentralExt.SUClosed.statedSU_exists_section_of_central hK hn2 hn4 h5' hπ
        hcen) hq hZ e
  rw [QuotientGroup.ker_mk'] at hαZ hαk
  have hg0 : Nat.gcd n (p ^ f + 1) ≠ 0 := (Nat.gcd_pos_of_pos_left _ (by omega)).ne'
  have hZY : Nat.card (center Y) = ordProj[2] (Nat.gcd n (p ^ f + 1)) := by
    rw [hcZ, Nat.card_congr (LieType.Steinberg.CentralExt.griessHopfMultiplierCongr e).toEquiv]
    obtain ⟨-, ⟨eM⟩⟩ := LieType.Steinberg.CentralExt.SUClosed.psu_hopfMultiplier hK hn2 hn4 h5'
    rw [Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
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
  have hcardZ : Nat.card Z = Nat.gcd n (p ^ f + 1) :=
    (CFSG.LinearGroups.unitary_scalar_kernel hp hK (by omega)).2.2
  have hmul := Subgroup.card_ker_mul_card_of_surjective hψs
  rw [hψk, hZY, hcardZ] at hmul
  have hk : ¬ 2 ∣ Nat.card α.ker := by
    have h1 : Nat.card α.ker = ordCompl[2] (Nat.gcd n (p ^ f + 1)) :=
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
  have hamat : ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.scalar (Fin n) (c : K) := by
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
  have hκ : ¬ 2 ∣ Nat.card (SU.equivStated hK n).toMonoidHom.ker := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr (SU.equivStated hK n).injective, Subgroup.card_bot]
    norm_num
  have hU := Concl.map (φ := (SU.equivStated hK n).toMonoidHom) (SU.equivStated hK n).surjective hκ
    (SU.concl_su hK hp2 hn4 h5 ha'm)
  have ha'a : (SU.equivStated hK n).toMonoidHom a' = a := by
    rw [ha']
    exact MulEquiv.apply_symm_apply _ a
  rw [ha'a] at hU
  rw [← hat]
  exact Concl.map (φ := α) hαs hk hU

end CFSG.ComponentClassification.HarrisLit.T1.P54
