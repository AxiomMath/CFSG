module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsGF2
import CFSG.Quasithin.Background.SmithD39TwoWit
import CFSG.Quasithin.Background.B69Cent
import CFSG.CGT.PushingUpLit.BHS.TwoSixteenSL
import CFSG.CGT.PushingUpLit.BHS7.FiveFamily
public import CFSG.Quasithin.Background.B1Restrict

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin
open CFSG.Assembly.LowTwoRank
open CFSG.CGT.PushingUpLit.BHS (two_sixteen_sl_gen normalizer_commV_le_stabSub
  card_autSub_eq_relIndex offender_iff isQuasisimple_of_mulEquiv'
  isQuasisimple_special_linear_two)
open CFSG.CGT.PushingUpLit.BHS7 (autSub_iSup_le)
open CFSG.Quasithin.B5 (natural_invariant_eq natQuotEquiv natQuotEquiv_mk)
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

private theorem charP_two_of_card_pow {K : Type} [Field K] [Finite K] {m : ℕ}
    (hK : Nat.card K = 2 ^ m) : CharP K 2 := by
  refine (letI : Fintype K := Fintype.ofFinite K; ?_)
  have h : Fintype.card K = 2 ^ m := by rwa [← Nat.card_eq_fintype_card]
  exact charP_of_card_eq_prime_pow (p := 2) (f := m) h

private theorem exists_finset_card_four_of_card {K : Type} [Field K] [Finite K] {m : ℕ}
    (hm : 2 ≤ m) (hK : Nat.card K = 2 ^ m) : ∃ s : Finset K, s.card = 4 := by
  refine (letI : Fintype K := Fintype.ofFinite K; ?_)
  have hcard : Fintype.card K = 2 ^ m := by rwa [← Nat.card_eq_fintype_card]
  have h4 : 4 ≤ (Finset.univ : Finset K).card := by
    rw [Finset.card_univ, hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq h4
  exact ⟨s, hs⟩

omit [Finite W] in
theorem isQuasisimple_of_binaryNaturalSL {L : Subgroup (MulAut W)} {U Z : Subgroup W} {m : ℕ}
    (hm : 2 ≤ m) (hnat : BinaryNaturalSL L U Z 2 m) : CFSG.IsQuasisimple ↥L := by
  obtain ⟨K, hKfield, hKfin, hK, e, -⟩ :=
    CFSG.Quasithin.SmithD39Two.exists_equiv_of_binaryNaturalSL hnat
  refine (letI : Field K := hKfield; letI : Finite K := hKfin; ?_)
  have h4 : ∃ s : Finset K, s.card = 4 := exists_finset_card_four_of_card hm hK
  have hqs : CFSG.Open.IsQuasisimple ↥(StatedSL 2 K) :=
    isQuasisimple_of_mulEquiv' (specialLinearGroupEquivStatedSL 2 K)
      (isQuasisimple_special_linear_two h4)
  exact CFSG.Quasithin.B1Red.isQuasisimple_of_open (isQuasisimple_of_mulEquiv' e hqs)

omit [Finite W] in
private theorem exists_nat_beta {K : Type} [Field K] {L : Subgroup (MulAut W)}
    {U Z : Subgroup W} {π : ↥(StatedSL 2 K) →* ↥L}
    (hD : (FFModel.nat (StatedSL 2 K)).RealizesVia L U Z π) :
    ∃ β : ↥U →* Multiplicative (Fin 2 → K),
      Function.Surjective β ∧ (∀ u : ↥U, β u = 1 ↔ (u : W) ∈ Z) ∧
        ∀ (γ : ↥(StatedSL 2 K)) (u : ↥U)
          (hu : ((π γ : ↥L) : MulAut W) u ∈ U),
          β ⟨((π γ : ↥L) : MulAut W) u, hu⟩ = natAct (StatedSL 2 K) γ (β u) := by
  simp only [FFModel.nat] at hD
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := hD
  let e := natQuotEquiv (Multiplicative (Fin 2 → K))
  refine ⟨e.toMonoidHom.comp β, e.surjective.comp hβs, ?_, ?_⟩
  · intro u
    rw [MonoidHom.comp_apply]
    constructor
    · intro h
      exact (hβk u).mp (e.injective (h.trans (map_one e).symm))
    · intro h
      rw [show β u = 1 from (hβk u).mpr h, map_one]
  · intro γ u hu
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
    have h1 := hβe γ u m hu trivial hm.symm
    have h2 : e (β ⟨((π γ : ↥L) : MulAut W) u, hu⟩) =
        natAct (StatedSL 2 K) γ (e (β u)) := by
      rw [h1]
      have hm' : e (β u) = (m : Multiplicative (Fin 2 → K)) := by
        rw [← hm]
        exact natQuotEquiv_mk _ (m : Multiplicative (Fin 2 → K))
      rw [hm', natQuotEquiv_mk]
    change e (β ⟨_, hu⟩) = natAct (StatedSL 2 K) γ (e (β u))
    exact h2

private theorem statedSL_symm_coe {K : Type} [Field K] {γ : ↥(StatedSL 2 K)} :
    (((specialLinearGroupEquivStatedSL 2 K).symm γ :
        Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (((γ : ↥(StatedSL 2 K)) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
  have h : (specialLinearGroupEquivStatedSL 2 K)
      ((specialLinearGroupEquivStatedSL 2 K).symm γ) = γ := MulEquiv.apply_symm_apply _ _
  have h' := congrArg (fun z : ↥(StatedSL 2 K) =>
    ((z : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) h
  rw [specialLinearGroupEquivStatedSL_coe] at h'
  exact h'

omit [Finite W] in
private theorem isIrrSec_gomiWX_lt {K : Type} [Field K] {L : Subgroup (MulAut W)}
    {π : ↥(StatedSL 2 K) →* ↥L}
    (hD : (FFModel.nat (StatedSL 2 K)).RealizesVia L (commV L)
      (commV L ⊓ fixV L) π)
    (hcomm : commSub (commV L) L = commV L) :
    commV L ⊓ fixV L < commV L := by
  obtain ⟨β, hβs, hβk, hβe⟩ := exists_nat_beta hD
  have hne : commV L ≠ ⊥ := by
    intro hbot
    have hsub : Subsingleton ↥(commV L) := by rw [hbot]; infer_instance
    have hnt : Nontrivial (Multiplicative (Fin 2 → K)) := by
      refine (letI : Nonempty (Fin 2) := ⟨0⟩; ?_)
      infer_instance
    exact (not_subsingleton _) (@Function.Surjective.subsingleton _ _ _ hsub hβs)
  refine lt_of_le_of_ne inf_le_left fun hEq => ?_
  have hle : commV L ≤ fixV L := inf_eq_left.mp hEq
  have hbot : commSub (commV L) L = ⊥ := commSub_eq_bot_iff.mpr hle
  rw [hcomm] at hbot
  exact hne hbot

omit [Finite W] in
private theorem isIrrSec_gomiWX_dichotomy {K : Type} [Field K] {L : Subgroup (MulAut W)}
    {π : ↥(StatedSL 2 K) →* ↥L}
    (hD : (FFModel.nat (StatedSL 2 K)).RealizesVia L (commV L)
      (commV L ⊓ fixV L) π) :
    ∀ J : Subgroup W, (∀ x ∈ L, ∀ w ∈ J, x w ∈ J) →
      commV L ⊓ fixV L ≤ J → J ≤ commV L →
        J = commV L ⊓ fixV L ∨ J = commV L := by
  obtain ⟨β, hβs, hβk, hβe⟩ := exists_nat_beta hD
  intro J hJinv hRJ hJle
  let J' : Subgroup (Multiplicative (Fin 2 → K)) := (J.subgroupOf (commV L)).map β
  have hJ'inv : ∀ (γ : ↥(StatedSL 2 K)) (x : Multiplicative (Fin 2 → K)), x ∈ J' →
      natAct (StatedSL 2 K) γ x ∈ J' := by
    intro γ x hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hx
    have huJ : (u : W) ∈ J := Subgroup.mem_subgroupOf.1 hu
    have huW : ((π γ : ↥L) : MulAut W) (u : W) ∈ commV L :=
      CFSG.Quasithin.FFC.commV_invariant_self L (π γ) (π γ).2 (u : W) u.2
    exact Subgroup.mem_map.2 ⟨⟨_, huW⟩,
      Subgroup.mem_subgroupOf.2 (hJinv (π γ) (π γ).2 (u : W) huJ), hβe γ u huW⟩
  rcases natural_invariant_eq (n := 2) (K := K) (by norm_num) J' hJ'inv with h | h
  · left
    refine le_antisymm ?_ hRJ
    intro w hwJ
    have hwW : w ∈ commV L := hJle hwJ
    have h1 : β ⟨w, hwW⟩ = 1 := by
      have h2 : β ⟨w, hwW⟩ ∈ J' :=
        Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hwJ)
      rw [h, Subgroup.mem_bot] at h2
      exact h2
    exact (hβk ⟨w, hwW⟩).mp h1
  · right
    refine le_antisymm hJle ?_
    intro w hwW
    have h1 : β ⟨w, hwW⟩ ∈ J' := by rw [h]; trivial
    obtain ⟨u, hu, hue⟩ := Subgroup.mem_map.1 h1
    have huJ : (u : W) ∈ J := Subgroup.mem_subgroupOf.1 hu
    have hkerβ : β (u⁻¹ * ⟨w, hwW⟩) = 1 := by
      rw [map_mul, map_inv, hue]
      group
    have hRmem : ((u⁻¹ * ⟨w, hwW⟩ : ↥(commV L)) : W) ∈ commV L ⊓ fixV L :=
      (hβk (u⁻¹ * ⟨w, hwW⟩)).mp hkerβ
    have hJmem : ((u⁻¹ * ⟨w, hwW⟩ : ↥(commV L)) : W) ∈ J := hRJ hRmem
    have hsum : (u : W) * ((u⁻¹ * ⟨w, hwW⟩ : ↥(commV L)) : W) = w := by
      simp
    rw [← hsum]
    exact J.mul_mem huJ hJmem

omit [Finite W] in
private theorem isIrrSec_gomiWX {K : Type} [Field K] {L : Subgroup (MulAut W)}
    {π : ↥(StatedSL 2 K) →* ↥L}
    (hD : (FFModel.nat (StatedSL 2 K)).RealizesVia L (commV L)
      (commV L ⊓ fixV L) π)
    (hcomm : commSub (commV L) L = commV L) :
    commV L ⊓ fixV L < commV L ∧
      ∀ J : Subgroup W, (∀ x ∈ L, ∀ w ∈ J, x w ∈ J) →
        commV L ⊓ fixV L ≤ J → J ≤ commV L →
          J = commV L ⊓ fixV L ∨ J = commV L :=
  ⟨isIrrSec_gomiWX_lt hD hcomm, isIrrSec_gomiWX_dichotomy hD⟩

omit [Finite W] in
theorem commV_mem_irrPlus_of_binaryNaturalSL {L : Subgroup (MulAut W)} {m : ℕ} (hm : 2 ≤ m)
    (hnat : BinaryNaturalSL L (commV L) (gomiWXKer L) 2 m) : commV L ∈ IrrPlus L ⊤ := by
  have hq : CFSG.IsQuasisimple ↥L := isQuasisimple_of_binaryNaturalSL hm hnat
  obtain ⟨K, hKfield, hKfin, hK, π, hD⟩ := hnat
  refine (letI : Field K := hKfield; letI : Finite K := hKfin; ?_)
  have hcomm : commSub (commV L) L = commV L :=
    CFSG.Quasithin.B15P4.commSub_commV_of_perfect (Subgroup.isPerfect_iff.mp hq.1)
  have hD' : (FFModel.nat (StatedSL 2 K)).RealizesVia L (commV L)
      (commV L ⊓ fixV L) π := by simpa [gomiWXKer] using hD
  obtain ⟨hlt, hirr⟩ := isIrrSec_gomiWX hD' hcomm
  exact mem_irrPlus_top_iff.mpr ⟨CFSG.Quasithin.FFC.commV_invariant_self L, hcomm, hlt, hirr⟩

omit [Finite W] in
private theorem inf_centSub_commV_eq_bot {K : Type} [Field K] {L : Subgroup (MulAut W)}
    {π : ↥(StatedSL 2 K) →* ↥L} (hπ : Function.Surjective π)
    {β : ↥(commV L) →* Multiplicative (Fin 2 → K)}
    (hβs : Function.Surjective β)
    (hβe : ∀ (γ : ↥(StatedSL 2 K)) (u : ↥(commV L))
      (hu : ((π γ : ↥L) : MulAut W) u ∈ commV L),
      β ⟨((π γ : ↥L) : MulAut W) u, hu⟩ = natAct (StatedSL 2 K) γ (β u)) :
    L ⊓ centSub (commV L) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun l hl => ?_
  obtain ⟨hlL, hlcen⟩ := hl
  obtain ⟨γ, hγ⟩ := hπ ⟨l, hlL⟩
  have hγcoe : ((π γ : ↥L) : MulAut W) = l := congrArg Subtype.val hγ
  let A : Matrix.SpecialLinearGroup (Fin 2) K := (specialLinearGroupEquivStatedSL 2 K).symm γ
  have hA1 : A = 1 := by
    apply CFSG.QuasithinUnique.Setup.Campbell.eq_one_of_forall_smul_vec
    intro v
    obtain ⟨p, hp⟩ := hβs (Multiplicative.ofAdd v)
    have hpU : ((π γ : ↥L) : MulAut W) p ∈ commV L := by
      rw [show ((π γ : ↥L) : MulAut W) = l from hγcoe]
      rw [hlcen p p.2]
      exact p.2
    have hp' : (⟨((π γ : ↥L) : MulAut W) p, hpU⟩ : ↥(commV L)) = p := by
      apply Subtype.ext
      show ((π γ : ↥L) : MulAut W) p = p
      rw [show ((π γ : ↥L) : MulAut W) = l from hγcoe]
      exact hlcen p p.2
    have h1 := hβe γ p hpU
    rw [hp', hp] at h1
    rw [Matrix.SpecialLinearGroup.smul_def, statedSL_symm_coe]
    simpa [natAct] using (congrArg Multiplicative.toAdd h1).symm
  have hγ1 : γ = 1 := by
    have h : (specialLinearGroupEquivStatedSL 2 K) A = γ := by
      dsimp [A]; rw [MulEquiv.apply_symm_apply]
    rw [← h, hA1, map_one]
  have h1 : (⟨l, hlL⟩ : ↥L) = 1 := by rw [← hγ, hγ1, map_one]
  exact congrArg Subtype.val h1

omit [Finite W] in
private theorem card_autSub_commV {K : Type} [Field K] [Finite K]
    {L : Subgroup (MulAut W)} {e : ↥(StatedSL 2 K) ≃* ↥L}
    (hLst : L ≤ stabSub (commV L)) (hfaith : L ⊓ centSub (commV L) = ⊥) :
    Nat.card (autSub L (commV L)) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  have h1 := card_autSub_mul hLst
  rw [hfaith, Subgroup.card_bot, mul_one] at h1
  rw [h1, ← Nat.card_congr e.toEquiv, CFSG.Open.StatedAPI.card_statedSL_two]

omit [Finite W] in
private theorem relIndex_gomiWXKer {K : Type} [Field K] {L : Subgroup (MulAut W)}
    {β : ↥(commV L) →* Multiplicative (Fin 2 → K)}
    (hβs : Function.Surjective β)
    (hβk : ∀ u : ↥(commV L), β u = 1 ↔ (u : W) ∈ commV L ⊓ fixV L) :
    (commV L ⊓ fixV L).relIndex (commV L) = Nat.card K ^ 2 := by
  have hker : β.ker = (commV L ⊓ fixV L).subgroupOf (commV L) := by
    ext u
    rw [MonoidHom.mem_ker, hβk u, Subgroup.mem_subgroupOf]
  have h1 : Nat.card (↥(commV L) ⧸ (commV L ⊓ fixV L).subgroupOf (commV L)) =
      Nat.card (Multiplicative (Fin 2 → K)) :=
    Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective β hβs)).toEquiv
  change Nat.card (↥(commV L) ⧸ (commV L ⊓ fixV L).subgroupOf (commV L)) = Nat.card K ^ 2
  have hq2 : Nat.card (Multiplicative (Fin 2 → K)) = Nat.card K ^ 2 := by
    rw [Nat.card_congr (Multiplicative.toAdd (α := Fin 2 → K)), Nat.card_fun, Nat.card_fin]
  rw [h1, hq2]

private theorem autSub_offender_le {K : Type} [Field K] [Finite K] [CharP K 2]
    (hW : ∀ w : W, w ^ 2 = 1) {S L : Subgroup (MulAut W)}
    {θ : ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) K}
    {β : ↥(commV L) →* Multiplicative (Fin 2 → K)}
    (hβs : Function.Surjective β)
    (hβk : β.ker = (commV L ⊓ fixV L).subgroupOf (commV L))
    (hβe : ∀ (x : ↥L) (p : ↥(commV L)) (hp : (x : MulAut W) p ∈ commV L),
      β ⟨(x : MulAut W) p, hp⟩ =
        Multiplicative.ofAdd ((θ x : Matrix (Fin 2) (Fin 2) K).mulVec
          (Multiplicative.toAdd (β p))))
    (h4 : ∃ s : Finset K, s.card = 4)
    (hirr : commV L ∈ IrrPlus L (⊤ : Subgroup W))
    (hN : ffJ S ≤ Subgroup.normalizer (L : Set (MulAut W)))
    {B : Subgroup (MulAut W)} (hB : IsFFStarOffender S B) :
    autSub B (commV L) ≤ autSub L (commV L) := by
  have hBoff : CFSG.CGT.PushingUpLit.BHS.IsOff B := (offender_iff.mp hB).2
  have hBffJ : B ≤ ffJ S := by
    rw [ffJ]
    exact le_iSup₂ (f := fun C (_ : IsFFStarOffender S C) => C) B hB
  have hBN : B ≤ Subgroup.normalizer (L : Set (MulAut W)) := hBffJ.trans hN
  by_cases hLB : ⁅L, B⁆ = ⊥
  · have hcomm : ∀ b ∈ B, ∀ l ∈ L, b * l = l * b :=
      fun b hb l hl => (CFSG.Quasithin.B69.mul_comm_of_commutator_eq_bot hLB l hl b hb).symm
    have hfix := CFSG.Quasithin.B69.comm_trivial_on_commV_of_elem hW hBoff.2.2.1 hcomm hirr
    have hbot : autSub B (commV L) = ⊥ := by
      refine (Subgroup.eq_bot_iff_forall _).2 fun φ hφ => ?_
      obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
      apply MulEquiv.ext
      intro u
      apply Subtype.ext
      rw [resHom_apply]
      show (g : MulAut W) (u : W) = (u : W)
      exact hfix g hg u u.2
    rw [hbot]
    exact bot_le
  · exact (two_sixteen_sl_gen (F := K) (A := B) (E := L) (W := commV L) h4 rfl θ β hβs
      hβk hβe hBN hBoff hLB).1

omit [Finite W] in
private theorem autSub_ffJ_le {S L : Subgroup (MulAut W)}
    (hN : ffJ S ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (h : ∀ B : Subgroup (MulAut W), IsFFStarOffender S B →
      autSub B (commV L) ≤ autSub L (commV L)) :
    autSub (ffJ S) (commV L) ≤ autSub L (commV L) := by
  have h' := autSub_iSup_le (V := W) (S := {B | IsFFStarOffender S B})
    (W := commV L) (U₀ := autSub L (commV L)) fun B hB =>
      ⟨((show B ≤ ffJ S from by
          rw [ffJ]
          exact le_iSup₂ (f := fun C (_ : IsFFStarOffender S C) => C) B hB).trans hN).trans
        (normalizer_commV_le_stabSub L), h B hB⟩
  simpa [ffJ] using h'

omit [Finite W] in
private theorem theta_equivariance {K : Type} [Field K] {L : Subgroup (MulAut W)}
    (e : ↥(StatedSL 2 K) ≃* ↥L) {β : ↥(commV L) →* Multiplicative (Fin 2 → K)}
    (hβe₀ : ∀ (γ : ↥(StatedSL 2 K)) (u : ↥(commV L))
      (hu : ((e.toMonoidHom γ : ↥L) : MulAut W) u ∈ commV L),
      β ⟨((e.toMonoidHom γ : ↥L) : MulAut W) u, hu⟩ = natAct (StatedSL 2 K) γ (β u)) :
    ∀ (x : ↥L) (p : ↥(commV L)) (hp : (x : MulAut W) p ∈ commV L),
      β ⟨(x : MulAut W) p, hp⟩ =
        Multiplicative.ofAdd ((((e.symm.trans (specialLinearGroupEquivStatedSL 2 K).symm) x :
          Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec
            (Multiplicative.toAdd (β p))) := by
  intro x p hp
  have h1 : β ⟨(x : MulAut W) p, hp⟩ = natAct (StatedSL 2 K) (e.symm x) (β p) := by
    simpa [e.apply_symm_apply] using hβe₀ (e.symm x) p (by simpa using hp)
  have hθ : ((((e.symm.trans (specialLinearGroupEquivStatedSL 2 K).symm) x :
      Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) =
      (((e.symm x : ↥(StatedSL 2 K)) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    change (((specialLinearGroupEquivStatedSL 2 K).symm (e.symm x) :
        Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = _
    exact statedSL_symm_coe
  rw [h1, hθ]
  rfl

private theorem autSub_ffJ_card_eq {K : Type} [Field K] [Finite K] {m : ℕ}
    (hK : Nat.card K = 2 ^ m)
    {S L : Subgroup (MulAut W)} (hS : IsPGroup 2 ↥S) {A : Subgroup (MulAut W)}
    (hJ_le : autSub (ffJ S) (commV L) ≤ autSub L (commV L))
    (hAutL_card : Nat.card (autSub L (commV L)) = Nat.card K * (Nat.card K ^ 2 - 1))
    (hAutA_le : autSub A (commV L) ≤ autSub (ffJ S) (commV L))
    (hAutA_card : Nat.card (autSub A (commV L)) = Nat.card K) :
    autSub (ffJ S) (commV L) = autSub A (commV L) := by
  have hffJ_le_S : ffJ S ≤ S := by
    rw [ffJ]
    exact iSup₂_le fun B hB => hB.1
  have hffJ2 : IsPGroup 2 ↥(ffJ S) := hS.to_le hffJ_le_S
  have hAut2 : IsPGroup 2 ↥(autSub (ffJ S) (commV L)) := by
    change IsPGroup 2 ↥(((ffJ S).subgroupOf (stabSub (commV L))).map (resHom (commV L)))
    exact (hffJ2.comap_subtype).map (resHom (commV L))
  have hAutJ_dvd : Nat.card (autSub (ffJ S) (commV L)) ∣ Nat.card K := by
    have hdvd : Nat.card (autSub (ffJ S) (commV L)) ∣
        Nat.card (autSub L (commV L)) := Subgroup.card_dvd_of_le hJ_le
    rw [hAutL_card] at hdvd
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hAut2
    rw [hk] at hdvd ⊢
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hK
      refine (letI : Fintype K := Fintype.ofFinite K; ?_)
      have h2 : 1 < Nat.card K := by
        rw [Nat.card_eq_fintype_card]
        exact Fintype.one_lt_card
      omega
    have hodd : Odd (Nat.card K ^ 2 - 1) := by
      rw [hK, ← pow_mul]
      have h1 : 1 ≤ 2 ^ (m * 2) := Nat.one_le_pow _ _ (by norm_num)
      have h2 : 2 ∣ 2 ^ (m * 2) := dvd_pow_self 2 (by omega)
      exact Nat.odd_iff.2 (by omega)
    exact (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)).dvd_of_dvd_mul_right hdvd
  have hAutJ_card : Nat.card (autSub (ffJ S) (commV L)) = Nat.card K := by
    refine Nat.dvd_antisymm hAutJ_dvd ?_
    rw [← hAutA_card]
    exact Subgroup.card_dvd_of_le hAutA_le
  exact (Subgroup.eq_of_le_of_card_ge hAutA_le (by rw [hAutJ_card, hAutA_card])).symm

private theorem autSub_ffJ_eq_offender {K : Type} [Field K] [Finite K] [CharP K 2]
    {S L : Subgroup (MulAut W)} (hW : ∀ w : W, w ^ 2 = 1)
    (hS : IsPGroup 2 ↥S) {m : ℕ} (hK : Nat.card K = 2 ^ m)
    {θ : ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) K}
    {β : ↥(commV L) →* Multiplicative (Fin 2 → K)}
    (hβs : Function.Surjective β)
    (hβk : β.ker = (commV L ⊓ fixV L).subgroupOf (commV L))
    (hβe : ∀ (x : ↥L) (p : ↥(commV L)) (hp : (x : MulAut W) p ∈ commV L),
      β ⟨(x : MulAut W) p, hp⟩ =
        Multiplicative.ofAdd ((θ x : Matrix (Fin 2) (Fin 2) K).mulVec
          (Multiplicative.toAdd (β p))))
    (h4 : ∃ s : Finset K, s.card = 4)
    (hirr : commV L ∈ IrrPlus L (⊤ : Subgroup W))
    {e : ↥(StatedSL 2 K) ≃* ↥L}
    (hLst : L ≤ stabSub (commV L)) (hfaith : L ⊓ centSub (commV L) = ⊥)
    (hN : ffJ S ≤ Subgroup.normalizer (L : Set (MulAut W)))
    {A : Subgroup (MulAut W)} (hA : IsFFStarOffender S A) (hLA : ⁅L, A⁆ ≠ ⊥) :
    autSub (ffJ S) (commV L) = autSub A (commV L) ∧
      Nat.card (autSub A (commV L)) = Nat.card K ∧
      Nat.card (autSub L (commV L)) = Nat.card K * (Nat.card K ^ 2 - 1) ∧
      (fixV A).relIndex (commV L) = Nat.card K ∧ A ≤ stabSub (commV L) := by
  have hB_le : ∀ B : Subgroup (MulAut W), IsFFStarOffender S B →
      autSub B (commV L) ≤ autSub L (commV L) :=
    fun B hB => autSub_offender_le hW hβs hβk hβe h4 hirr hN hB
  have hJ_le : autSub (ffJ S) (commV L) ≤ autSub L (commV L) := autSub_ffJ_le hN hB_le
  have hAutL_card : Nat.card (autSub L (commV L)) =
      Nat.card K * (Nat.card K ^ 2 - 1) := card_autSub_commV (e := e) hLst hfaith
  have hAffJ : A ≤ ffJ S := by
    rw [ffJ]
    exact le_iSup₂ (f := fun B (_ : IsFFStarOffender S B) => B) A hA
  have hAst : A ≤ stabSub (commV L) :=
    (hAffJ.trans hN).trans (normalizer_commV_le_stabSub L)
  have hAgen := two_sixteen_sl_gen (F := K) (A := A) (E := L) (W := commV L)
    h4 rfl θ β hβs hβk hβe (hAffJ.trans hN) (offender_iff.mp hA).2 hLA
  have hAutA_card : Nat.card (autSub A (commV L)) = Nat.card K := hAgen.2.1
  have hrelA : (fixV A).relIndex (commV L) = Nat.card K := by
    rw [hAgen.2.2.2, ← card_autSub_eq_relIndex hAst, hAutA_card]
  have hAutA_le : autSub A (commV L) ≤ autSub (ffJ S) (commV L) :=
    autSub_mono hAffJ (commV L)
  have hAutJ_eq := autSub_ffJ_card_eq hK hS hJ_le hAutL_card hAutA_le hAutA_card
  exact ⟨hAutJ_eq, hAutA_card, hAutL_card, hrelA, hAst⟩

omit [Finite W] in
private theorem false_of_relIndex_le {K : Type} [Field K] [Finite K]
    {L : Subgroup (MulAut W)}
    {A : Subgroup (MulAut W)}
    (hsub : commV L ⊓ fixV A ≤ commV L ⊓ fixV L)
    (hR_index : (commV L ⊓ fixV L).relIndex (commV L) = Nat.card K ^ 2)
    (hrelA : (fixV A).relIndex (commV L) = Nat.card K)
    (hq4 : 4 ≤ Nat.card K) : False := by
  have hq2_le : Nat.card K ^ 2 ≤ Nat.card K := by
    calc Nat.card K ^ 2 = (commV L ⊓ fixV L).relIndex (commV L) := hR_index.symm
      _ ≤ (commV L ⊓ fixV A).relIndex (commV L) := by
        refine Subgroup.relIndex_le_of_le_left hsub ?_
        rw [Subgroup.inf_relIndex_left (commV L) (fixV A), hrelA]
        exact Nat.card_pos.ne'
      _ = (fixV A).relIndex (commV L) := Subgroup.inf_relIndex_left (commV L) (fixV A)
      _ = Nat.card K := hrelA
  have hqpos : 0 < Nat.card K := Nat.card_pos
  have h1 : Nat.card K * Nat.card K ≤ Nat.card K * 1 := by
    simpa [pow_two, mul_one] using hq2_le
  have h2 : Nat.card K ≤ 1 := Nat.le_of_mul_le_mul_left h1 hqpos
  omega

theorem not_inf_fixV_ffJ_le_of_binaryNaturalSL (hW : ∀ w : W, w ^ 2 = 1)
    {S L : Subgroup (MulAut W)} (hS : IsPGroup 2 ↥S) {m : ℕ} (hm : 2 ≤ m)
    (hnat : BinaryNaturalSL L (commV L) (gomiWXKer L) 2 m)
    (hN : ffJ S ≤ Subgroup.normalizer (L : Set (MulAut W)))
    {A : Subgroup (MulAut W)} (hA : IsFFStarOffender S A) (hLA : ⁅L, A⁆ ≠ ⊥) :
    ¬ commV L ⊓ fixV (ffJ S) ≤ gomiWXKer L := by
  intro hle
  have hirr : commV L ∈ IrrPlus L ⊤ := commV_mem_irrPlus_of_binaryNaturalSL hm hnat
  obtain ⟨K, hKfield, hKfin, hK, e, hD⟩ :=
    CFSG.Quasithin.SmithD39Two.exists_equiv_of_binaryNaturalSL hnat
  refine (letI : Field K := hKfield; letI : Finite K := hKfin;
    letI : CharP K 2 := charP_two_of_card_pow hK; ?_)
  have h4 : ∃ s : Finset K, s.card = 4 := exists_finset_card_four_of_card hm hK
  obtain ⟨β, hβs, hβk, hβe₀⟩ := exists_nat_beta hD
  have hβe := theta_equivariance e hβe₀
  have hβkeq : β.ker = (commV L ⊓ fixV L).subgroupOf (commV L) := by
    ext u
    rw [MonoidHom.mem_ker, hβk u, Subgroup.mem_subgroupOf]
    rfl
  have hLst : L ≤ stabSub (commV L) :=
    CFSG.Quasithin.B1.le_stabSub_of_invariant (CFSG.Quasithin.FFC.commV_invariant_self L)
  have hfaith : L ⊓ centSub (commV L) = ⊥ :=
    inf_centSub_commV_eq_bot e.surjective hβs hβe₀
  obtain ⟨hAutJ_eq, -, -, hrelA, hAst⟩ :=
    autSub_ffJ_eq_offender (e := e) hW hS hK hβs hβkeq hβe h4 hirr hLst hfaith hN hA hLA
  have hJst : ffJ S ≤ stabSub (commV L) := hN.trans (normalizer_commV_le_stabSub L)
  have hfix_eq : commV L ⊓ fixV (ffJ S) = commV L ⊓ fixV A := by
    rw [← map_subtype_fixV_autSub hJst, ← map_subtype_fixV_autSub hAst, hAutJ_eq]
  have hR_index : (commV L ⊓ fixV L).relIndex (commV L) = Nat.card K ^ 2 :=
    relIndex_gomiWXKer hβs hβk
  have hsub : commV L ⊓ fixV A ≤ commV L ⊓ fixV L := by
    rw [← hfix_eq]
    simpa [gomiWXKer] using hle
  have hq4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  exact false_of_relIndex_le hsub hR_index hrelA hq4

end CFSG.GroupTheory
