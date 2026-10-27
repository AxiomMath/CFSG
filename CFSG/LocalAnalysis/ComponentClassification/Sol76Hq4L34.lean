module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76Hq4Row
public import CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanksL34
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aInvol
public import CFSG.LieType.Steinberg.CentralExt.GriessNativeModels

public section

namespace CFSG.ComponentClassification.Sol76T13.Hq4

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Multiplier
open CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanksTwo (toProjSL toProjSL_surjective
  toProjSL_eq_one_iff)
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.LieType.Steinberg.CentralExt

theorem card_centralizer_mulEquiv {S T : Type*} [Group S] [Group T] (e : S ≃* T) (x : S) :
    Nat.card (centralizer ({x} : Set S)) = Nat.card (centralizer ({e x} : Set T)) := by
  refine Nat.card_congr (e.toEquiv.subtypeEquiv fun y => ?_)
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    change e y * e x = e x * e y
    rw [← map_mul, ← map_mul, h]
  · intro h
    exact e.injective (by rw [map_mul, map_mul]; exact h)

section PSL3

variable {K : Type} [Field K]

@[expose] noncomputable def psl3E : Multiplicative (K × K) →* projSL 3 K where
  toFun w := toProjSL K (QuasithinUnique.Setup.X7a.up3 0 (Multiplicative.toAdd w).1
    (Multiplicative.toAdd w).2)
  map_one' := by
    simp only [toAdd_one, Prod.fst_zero, Prod.snd_zero, QuasithinUnique.Setup.X7a.up3_zero,
      map_one]
  map_mul' w w' := by
    rw [← map_mul, QuasithinUnique.Setup.X7a.up3_mul]
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, add_zero, mul_zero]

theorem psl3E_injective : Function.Injective (psl3E (K := K)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro w hw
  rw [MonoidHom.mem_ker] at hw
  change toProjSL K _ = 1 at hw
  rw [toProjSL_eq_one_iff, Matrix.SpecialLinearGroup.mem_center_iff] at hw
  obtain ⟨r, -, hr⟩ := hw
  have h02 := congrFun (congrFun hr 0) 2
  have h01 := congrFun (congrFun hr 0) 1
  simp [QuasithinUnique.Setup.X7a.up3_coe, QuasithinUnique.Setup.X7a.upMat] at h02 h01
  rw [Subgroup.mem_bot]
  exact Multiplicative.toAdd.injective (Prod.ext h02.symm h01.symm)

variable [CharP K 2]

theorem card_sq_dvd_card_centralizer_psl3 [Finite K] {x : projSL 3 K} (hx2 : x * x = 1)
    (hx1 : x ≠ 1) : Nat.card K * Nat.card K ∣ Nat.card (centralizer ({x} : Set (projSL 3 K))) := by
  obtain ⟨s, rfl⟩ := toProjSL_surjective x
  have hs2 : s ^ 2 ∈ center (Matrix.SpecialLinearGroup (Fin 3) K) := by
    rw [← toProjSL_eq_one_iff, map_pow, pow_two, hx2]
  obtain ⟨r, hr3, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hs2
  rw [Fintype.card_fin] at hr3
  set t := s ^ 3 with ht
  have ht2 : t * t = 1 := by
    have h6 : t * t = (s ^ 2) ^ 3 := by rw [ht, ← pow_add, ← pow_mul]
    rw [h6]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, ← hr, ← map_pow, hr3, map_one,
      Matrix.SpecialLinearGroup.coe_one]
  have htx : toProjSL K t = toProjSL K s := by
    rw [ht, map_pow, pow_succ, pow_two, hx2, one_mul]
  have ht1 : t ≠ 1 := by
    intro h
    apply hx1
    rw [← htx, h, map_one]
  obtain ⟨g, hg⟩ := QuasithinUnique.Setup.X7a.exists_conj_transvection t ht1 ht2
  set φ : Multiplicative (K × K) →* projSL 3 K :=
    (MulAut.conj (toProjSL K g)).toMonoidHom.comp psl3E with hφ
  have hφinj : Function.Injective φ := (MulAut.conj _).injective.comp psl3E_injective
  have hxφ : toProjSL K s = φ (Multiplicative.ofAdd (0, 1)) := by
    change toProjSL K s = toProjSL K g * psl3E (Multiplicative.ofAdd ((0 : K), (1 : K))) *
      (toProjSL K g)⁻¹
    have h01 : psl3E (Multiplicative.ofAdd ((0 : K), (1 : K))) =
        toProjSL K (QuasithinUnique.Setup.X7a.up3 0 0 1) := rfl
    rw [h01, ← hg, map_mul, map_mul, map_inv, htx]
    group
  have hle : φ.range ≤ centralizer {toProjSL K s} := by
    rintro _ ⟨w, rfl⟩
    rw [mem_centralizer_singleton_iff, hxφ, ← map_mul, ← map_mul, mul_comm]
  have hcard : Nat.card φ.range = Nat.card K * Nat.card K := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (K × K) ≃ K × K), Nat.card_prod]
  rw [← hcard]
  exact Subgroup.card_dvd_of_le hle

end PSL3

theorem four_le_factorization_centralizer_of_L34 {S : Type} [Group S] [Finite S]
    (hL : LieModel S .PSL 3 2 2) {x : S} (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    4 ≤ (Nat.card (centralizer ({x} : Set S))).factorization 2 := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := (GriessNative.classical_of_lieModel hL (by decide)).2
  have : CharP K 2 := GriessNative.charP_two_of_card (by norm_num) hK rfl
  let e' : S ≃* projSL 3 K := e.trans (RankThree.PartTwo.KFacts.KS44.projSLEquivStatedProj K).symm
  have hdvd := card_sq_dvd_card_centralizer_psl3 (x := e' x)
    (by rw [← map_mul, hx2, map_one]) (fun h => hx1 (e'.injective (by rw [h, map_one])))
  rw [hK, ← card_centralizer_mulEquiv e'] at hdvd
  exact (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp
    (by norm_num at hdvd ⊢; exact hdvd)

theorem centralFour_L34
    {Q : Type} [Group Q] [Finite Q] (hQ : IsQuasisimple Q) (hL : LieModel (Q ⧸ center Q) .PSL 3 2 2)
    {u v : Q} (hu : orderOf u = 2) (hv : orderOf v = 2) (huv : u ≠ v) (huZ : u ∈ center Q)
    (hvZ : v ∈ center Q) :
    (∃ x : Q, orderOf x = 2 ∧ x ∉ center Q) ∧
      ∀ x : Q, orderOf x = 2 → x ∉ center Q →
        (Nat.card ↥(center Q)).factorization 2 + 2 ≤
          (Nat.card ↥(centralizer ({x} : Set Q))).factorization 2 := by
  have hu2 : u * u = 1 := by rw [← pow_two, ← hu, pow_orderOf_eq_one]
  have hv2 : v * v = 1 := by rw [← pow_two, ← hv, pow_orderOf_eq_one]
  have hu1 : u ≠ 1 := by rintro rfl; rw [orderOf_one] at hu; omega
  have hv1 : v ≠ 1 := by rintro rfl; rw [orderOf_one] at hv; omega
  have hrow : GriessAll.GriessRow (Q ⧸ center Q) .PSL 3 2 2 :=
    GriessClassical.psl_row (GriessNative.classical_of_lieModel hL (by decide))
  have hodd : (¬ 2 ∣ (genericOrders .PSL 3 2 2).1 ∧ ¬ 2 ∣ (genericOrders .PSL 3 2 2).2) ∨
      (¬ 2 ∣ (exceptionalOrders .PSL 3 2 2).1 ∧ ¬ 2 ∣ (exceptionalOrders .PSL 3 2 2).2) :=
    Or.inl (by decide)
  have h4 := card_omegaCenter_le_four_of_griessRow hQ hrow hodd
  refine ⟨?_, fun x hx hxZ => ?_⟩
  ·
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := (GriessNative.classical_of_lieModel hL (by decide)).2
    have : CharP K 2 := GriessNative.charP_two_of_card (by norm_num) hK rfl
    let e' : Q ⧸ center Q ≃* projSL 3 K :=
      e.trans (RankThree.PartTwo.KFacts.KS44.projSLEquivStatedProj K).symm
    let φ : Q →* projSL 3 K := e'.toMonoidHom.comp (QuotientGroup.mk' (center Q))
    have hφ : Function.Surjective φ := e'.surjective.comp (QuotientGroup.mk'_surjective _)
    have hker : φ.ker = center Q := by
      ext y
      rw [MonoidHom.mem_ker]
      change e' (QuotientGroup.mk y) = 1 ↔ _
      rw [map_eq_one_iff e' e'.injective, QuotientGroup.eq_one_iff]
    have h4r := RankThree.PartTwo.Sec4.Census.DoubleCoverRanksTwo.four_le_pRank_of_involutions
      hφ hker hK huZ hvZ (by rw [pow_two]; exact hu2) (by rw [pow_two]; exact hv2) hu1 hv1 huv
    exact exists_noncentral_involution_of_pRank h4 (by omega)
  ·
    have hx2 : x * x = 1 := by rw [← pow_two, ← hx, pow_orderOf_eq_one]
    refine clause_two_of_griessRow hQ hrow hodd huZ hvZ hu2 hv2 hu1 hv1 huv hx2 ?_
    refine four_le_factorization_centralizer_of_L34 hL ?_ ?_
    · rw [← QuotientGroup.mk_mul, hx2]; rfl
    · intro h
      exact hxZ ((QuotientGroup.eq_one_iff x).mp h)

end CFSG.ComponentClassification.Sol76T13.Hq4
