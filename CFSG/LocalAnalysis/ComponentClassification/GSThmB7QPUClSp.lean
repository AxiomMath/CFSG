module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClLinCore
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClBarOf
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10SpInner
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10Sp4In
import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClBarIso

public section

namespace CFSG.ComponentClassification.GSThmB.QPUCl

open CFSG Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (gsp conjAut conjSp statedSp_le_gsp
  conjAut_proj coe_conjSp)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.ComponentClassification.CatFactsSp4 (fixOf mem_fixOf)
open scoped MatrixGroups

theorem card_mul_two_of_lieModel_psp_two {X : Type} [Group X] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hX : LieModel X .PSp 2 p f) :
    Nat.card X * 2 = (p ^ f) ^ 4 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1)) := by
  obtain ⟨hc, -⟩ := CatLeafProof.X10Lin.lieOrder_of_lieModel_classical
    (Or.inr (Or.inr (Or.inl rfl))) hp2 (by norm_num) hX
  have hc' : Nat.card X * Nat.gcd 2 (p ^ f - 1) =
      (p ^ f) ^ (2 ^ 2) * ∏ i ∈ Finset.Icc 1 2, ((p ^ f) ^ (2 * i) - 1) := hc
  rw [show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num)] at hc'
  have hodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hg : Nat.gcd 2 (p ^ f - 1) = 2 := by
    obtain ⟨k, hk⟩ := hodd
    exact Nat.gcd_eq_left ⟨k, by omega⟩
  rw [hg] at hc'
  exact hc'

theorem card_mul_two_of_lieModel_psl_two {X : Type} [Group X] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hX : LieModel X .PSL 2 p f) :
    Nat.card X * 2 = p ^ f * ((p ^ f) ^ 2 - 1) :=
  CFSG.Open.StatedAPI.card_mul_two_of_statedClassicalModel_psl_two_odd hp hp2 (hX.statedClassicalModel (by decide))

theorem eq_of_mul_sq_sub_one_eq {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : a * (a ^ 2 - 1) = b * (b ^ 2 - 1)) : a = b := by
  have key : ∀ {x y : ℕ}, 1 ≤ x → x < y → x * (x ^ 2 - 1) < y * (y ^ 2 - 1) := by
    intro x y hx hxy
    have h1 : x ^ 2 - 1 < y ^ 2 - 1 := by
      have h2 : x ^ 2 < y ^ 2 := Nat.pow_lt_pow_left hxy (by norm_num)
      have h3 : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ hx
      omega
    exact mul_lt_mul'' hxy h1 (Nat.zero_le _) (Nat.zero_le _)
  rcases lt_trichotomy a b with hab | hab | hab
  · exact absurd h (key ha hab).ne
  · exact hab
  · exact absurd h (key hb hab).ne'

theorem psp4_order_le {a b : ℕ} (h : a ≤ b) :
    a ^ 4 * ((a ^ 2 - 1) * (a ^ 4 - 1)) ≤ b ^ 4 * ((b ^ 2 - 1) * (b ^ 4 - 1)) :=
  Nat.mul_le_mul (Nat.pow_le_pow_left h 4)
    (Nat.mul_le_mul (Nat.sub_le_sub_right (Nat.pow_le_pow_left h 2) 1)
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left h 4) 1))

theorem conjAut_statedSp_apply {r : ℕ} {K : Type} [Field K] (g : StatedSp r K)
    (x : StatedProj (StatedSp r K)) :
    conjAut r K ⟨(g : GL (Fin r ⊕ Fin r) K), statedSp_le_gsp g.2⟩ x =
      (g : StatedProj (StatedSp r K)) * x * (g : StatedProj (StatedSp r K))⁻¹ := by
  obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective x
  have hconj : conjSp r K ⟨(g : GL (Fin r ⊕ Fin r) K), statedSp_le_gsp g.2⟩ g' = g * g' * g⁻¹ :=
    Subtype.ext ((coe_conjSp _ g').trans rfl)
  change conjAut r K _ (proj r K g') = _
  rw [conjAut_proj, hconj]
  show ((g * g' * g⁻¹ : StatedSp r K) : StatedProj (StatedSp r K)) = _
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]

theorem exists_mul_self_eq_smul_one {r : ℕ} {K : Type} [Field K] (g : StatedSp r K)
    (hg : (g : StatedProj (StatedSp r K)) * g = 1) :
    ∃ d : Kˣ, ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = (d : K) • 1 := by
  have hgg : g * g ∈ (StatedScalars (Fin r ⊕ Fin r) K).subgroupOf (StatedSp r K) :=
    (QuotientGroup.eq_one_iff (g * g)).1 (by rw [QuotientGroup.mk_mul]; exact hg)
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hgg
  obtain ⟨d, hd⟩ := hgg
  refine ⟨d, ?_⟩
  have h1 := congrArg (fun M : GL (Fin r ⊕ Fin r) K =>
    (M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) hd
  simp only [GeneralLinearGroup.coe_scalar, Subgroup.coe_mul, Units.val_mul] at h1
  rw [← h1, Matrix.smul_one_eq_diagonal]
  rfl

theorem false_of_barConfig_statedSp_two {K : Type} [Field K] [Finite K] {p f f₀ : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) (hf₀ : 1 ≤ f₀) (hK : Nat.card K = p ^ f₀)
    (hZ : center (StatedProj (StatedSp 2 K)) = ⊥)
    (hcard : Nat.card (StatedProj (StatedSp 2 K)) * 2 =
      (p ^ f₀) ^ 4 * (((p ^ f₀) ^ 2 - 1) * ((p ^ f₀) ^ 4 - 1)))
    (h : BarConfig (StatedProj (StatedSp 2 K)) p f p f) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, L, t, J, J₀, -, -, -, hLtop, hLm, -, ht2, ht1, hJt, hJc, hJm, -⟩ := h
  have hL2 := card_mul_two_of_lieModel_psp_two hp hp2 hLm
  have hLlt : Nat.card (↥L ⧸ pPrimeCore 2 ↥L) < Nat.card (StatedProj (StatedSp 2 K)) :=
    lt_of_le_of_lt (Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _))
      (lt_of_le_of_ne (Subgroup.card_le_card_group L)
        fun h1 => hLtop ((Subgroup.card_eq_iff_eq_top L).1 h1))
  have hqq : p ^ f < p ^ f₀ := by
    by_contra hge
    have := psp4_order_le (not_lt.mp hge)
    omega
  have hq₀ : 5 ≤ p ^ f₀ := by omega
  have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective t
  set A : gsp 2 K := ⟨(g : GL (Fin 2 ⊕ Fin 2) K), statedSp_le_gsp g.2⟩ with hAdef
  have hα : ∀ x, conjAut 2 K A x = (g : StatedProj (StatedSp 2 K)) * x *
      (g : StatedProj (StatedSp 2 K))⁻¹ := conjAut_statedSp_apply g
  have hcent : centralizer ({(g : StatedProj (StatedSp 2 K))} : Set _) =
      fixOf (conjAut 2 K A) := by
    ext x
    rw [mem_centralizer_singleton_iff, mem_fixOf, hα]
    constructor
    · intro hx
      rw [← hx, mul_inv_cancel_right]
    · intro hx
      calc x * (g : StatedProj (StatedSp 2 K)) =
          (g : StatedProj (StatedSp 2 K)) * x * (g : StatedProj (StatedSp 2 K))⁻¹ * g := by
            rw [hx]
        _ = (g : StatedProj (StatedSp 2 K)) * x := by group
  have hα1 : conjAut 2 K A ≠ 1 := fun h1 => ht1 (by
    have hgZ : (g : StatedProj (StatedSp 2 K)) ∈ center (StatedProj (StatedSp 2 K)) :=
      mem_center_iff.mpr fun x => by
        have hx := congrArg (fun φ : MulAut (StatedProj (StatedSp 2 K)) => φ x) h1
        simp only [MulAut.one_apply, hα] at hx
        calc x * (g : StatedProj (StatedSp 2 K)) =
            (g : StatedProj (StatedSp 2 K)) * x * (g : StatedProj (StatedSp 2 K))⁻¹ * g := by
              rw [hx]
          _ = (g : StatedProj (StatedSp 2 K)) * x := by group
    rw [hZ] at hgZ
    exact mem_bot.mp hgZ)
  obtain ⟨d, hAA⟩ := exists_mul_self_eq_smul_one g ht2
  have hJX : J ≤ fixOf (conjAut 2 K A) := hJt.trans hcent.le
  have hJc' : IsPComponent 2 (J.subgroupOf (fixOf (conjAut 2 K A))) := by
    rw [← hcent]
    exact hJc
  have hJs : IsSimpleGroup (↥J ⧸ pPrimeCore 2 ↥J) := lieModel_psl_two_isSimpleGroup hJm
  have : Group.IsPerfect ↥J := isPerfect_of_isPComponent hJX hJc'
  have : Group.IsPerfect (↥J ⧸ pPrimeCore 2 ↥J) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (pPrimeCore 2 ↥J))
      (QuotientGroup.mk'_surjective _)
  have hZJ : center (↥J ⧸ pPrimeCore 2 ↥J) = ⊥ := center_eq_bot_of_simple_perfect'
  have hJ2 := card_mul_two_of_lieModel_psl_two hp hp2 hJm
  have hsimple : IsSimpleGroup ↥J →
      Nat.card ↥J * 2 = p ^ f * ((p ^ f) ^ 2 - 1) := fun hs => by
    have hO : pPrimeCore 2 ↥J = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pPrimeCore 2 ↥J) with hO | hO
      · exact hO
      · exfalso
        have : Subsingleton (↥J ⧸ pPrimeCore 2 ↥J) := by
          rw [hO]
          exact QuotientGroup.subsingleton_quotient_top
        exact hJs.toNontrivial.exists_pair_ne.elim
          fun x hx => hx.elim fun y hxy => hxy (Subsingleton.elim x y)
    rw [← hJ2, Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hO).trans
      QuotientGroup.quotientBot).toEquiv]
  rcases X10Sp4.inner_cases hp hp2 hf₀ hK hq₀ A d hAA hα1 hJX hJc' with
    hS1 | ⟨-, hs, hJcard⟩ | ⟨hs, hJcard⟩
  ·
    obtain ⟨eS⟩ := hS1
    have hchar : ringChar K ≠ 2 := by
      have : CharP K p :=
        LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf₀ hK
      rw [ringChar.eq K p]
      exact hp2
    set z : ↥J := eS.symm (-1) with hzdef
    have hzc : ∀ w : ↥J, w * z = z * w := fun w => by
      apply eS.injective
      simp only [hzdef, map_mul, MulEquiv.apply_symm_apply, mul_neg_one, neg_one_mul]
    have hne : (-1 : SL(2, K)) ≠ 1 := fun h1 => by
      have h00 := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 0) h1
      have hm1 : ((-1 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0 = -1 := by
        rw [SpecialLinearGroup.coe_neg]
        rfl
      have hp1 : ((1 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := rfl
      exact Ring.neg_one_ne_one_of_char_ne_two hchar (hm1.symm.trans (h00.trans hp1))
    have hzo : orderOf z = 2 := by
      rw [hzdef, MulEquiv.orderOf_eq]
      exact orderOf_eq_prime (by rw [neg_one_sq]) hne
    have hzO : z ∈ pPrimeCore 2 ↥J := by
      have hc : QuotientGroup.mk' (pPrimeCore 2 ↥J) z ∈ center (↥J ⧸ pPrimeCore 2 ↥J) :=
        mem_center_iff.mpr fun w => by
          obtain ⟨w', rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥J) w
          rw [← map_mul, ← map_mul, hzc w']
      rw [hZJ, mem_bot] at hc
      exact (QuotientGroup.eq_one_iff z).1 hc
    have hcop := LocalAnalysis.ComponentInitial.coprime_orderOf_of_mem_pPrimeCore (p := 2) hzO
    rw [hzo] at hcop
    exact absurd hcop (by decide)
  ·
    rw [GorensteinWalter.sl2_card_formula K, hK, hsimple hs] at hJcard
    have := eq_of_mul_sq_sub_one_eq hq1 (by omega) hJcard
    omega
  ·
    rw [hsimple hs] at hJcard
    have := eq_of_mul_sq_sub_one_eq hq1 (Nat.one_le_pow _ _ (by omega)) hJcard
    have hle : p ^ f₀ ≤ (p ^ f₀) ^ 2 := Nat.le_self_pow (by norm_num) _
    omega

theorem false_of_barConfig_psp {P : Type} [Group P] [Finite P] {n p f f₀ : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (h5 : 5 ≤ p ^ f)
    (hP : StatedClassicalModel P .PSp n p f₀) (h : BarConfig P p f p f) : False := by
  have hadm : StatedLieAdmissible .PSp n p f₀ := hP.1
  have hn : 2 ≤ n := hadm.2.2.1
  have hf₀ : 1 ≤ f₀ := hadm.2.1
  have hLM : LieModel P .PSp n p f₀ := Or.inl ⟨by decide, hP⟩
  have : IsSimpleGroup P :=
    ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp P n p f₀ hP
  have hFT : FixedTwoComponentsQuasisimple P := fixedTwoComponentsQuasisimple_psp hp2 hP
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hP
  have : Finite (StatedProj (StatedSp n K)) := Finite.of_equiv _ e.toEquiv
  have : IsSimpleGroup (StatedProj (StatedSp n K)) := e.symm.isSimpleGroup
  have h' := BarConfig.of_mulEquiv e h
  have hZ := center_eq_bot_of_barConfig h'
  rcases (by omega : n = 2 ∨ 3 ≤ n) with rfl | hn3
  ·
    have hcard : Nat.card (StatedProj (StatedSp 2 K)) * 2 =
        (p ^ f₀) ^ 4 * (((p ^ f₀) ^ 2 - 1) * ((p ^ f₀) ^ 4 - 1)) := by
      rw [← Nat.card_congr e.toEquiv]
      exact card_mul_two_of_lieModel_psp_two hp hp2 hLM
    exact false_of_barConfig_statedSp_two hp hp2 h5 hf₀ hK hZ hcard h'
  ·
    have hQ : FixedTwoComponentsQuasisimple (StatedProj (StatedSp n K)) :=
      FixedTwoComponentsQuasisimple.of_mulEquiv e.symm hFT
    obtain ⟨t, -, -, hJ⟩ := exists_component_of_barConfig hQ hZ h'
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective t
    obtain ⟨hA, J', hJ'c, hJ'z, hJ'm⟩ := hJ _ (conjAut_statedSp_apply g)
    rcases CatLeafProof.X10Sp.inner_psp_component_cases hp hp2 hK hadm hn3 _ hA hJ'c with
      ⟨z, hz, hzc, hzz, hz1⟩ | hcm | ⟨-, hcm⟩ | hcm
    · exact hz1 (hJ'z z hz hzc hzz)
    · obtain ⟨-, hk2, -⟩ := eq_of_centralModel_of_lieModel hp hp2 hf hJ'm (Or.inl rfl) hcm
      omega
    · obtain ⟨ht, -, -⟩ :=
        eq_of_centralModel_of_lieModel hp hp2 hf hJ'm (Or.inr (Or.inr (Or.inl rfl))) hcm
      exact absurd ht (by decide)
    · obtain ⟨ht, -, -⟩ :=
        eq_of_centralModel_of_lieModel hp hp2 hf hJ'm (Or.inr (Or.inl rfl)) hcm
      exact absurd ht (by decide)

end CFSG.ComponentClassification.GSThmB.QPUCl
