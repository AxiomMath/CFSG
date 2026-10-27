module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgCore
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxLinear
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslBadKey
public import CFSG.Adapters.StatedSmallProjOrders

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.HardMathSupport.Dickson.Sec6.I1431
open Matrix

theorem multiplicity_eq_two_of_card_centerQuotient_eq_504 {E : Type} [Field E] [Finite E]
    {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (hE : Nat.card E = 2 ^ (3 * j)) {K : Type*} [Group K]
    (f : SpecialLinearGroup (Fin m) E →* K) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center (SpecialLinearGroup (Fin m) E))
    (hQ : CFSG.IsQuasisimple (SpecialLinearGroup (Fin m) E))
    (hN : Nat.card (K ⧸ Subgroup.center K) = 504) :
    m = 2 := by
  have hdvdK := pow_dvd_card_centerQuotient_of_surjective_specialLinear (e := 3 * j)
    (by omega) (by omega) hE f hf hker (Group.isPerfect_def.mp hQ.1)
  rw [hN, show (504 : ℕ) = 8 * 63 by norm_num] at hdvdK
  have hcop63 : Nat.Coprime (2 ^ (3 * j * (m * (m - 1) / 2))) 63 :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr (by norm_num : Odd 63))
  have hdvd8 : 2 ^ (3 * j * (m * (m - 1) / 2)) ∣ 8 :=
    Nat.Coprime.dvd_of_dvd_mul_right hcop63 hdvdK
  have hle : 3 * j * (m * (m - 1) / 2) ≤ 3 :=
    (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp (by simpa using hdvd8)
  by_contra hne
  have hm3 : 3 ≤ m := by omega
  have hN3 : 3 ≤ m * (m - 1) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    calc 3 * 2 = 3 * 2 := rfl
      _ ≤ m * (m - 1) := Nat.mul_le_mul hm3 (by omega)
  have : 9 ≤ 3 * j * (m * (m - 1) / 2) := by
    have hjN : 3 ≤ j * (m * (m - 1) / 2) := by
      calc 3 = 1 * 3 := by norm_num
        _ ≤ j * (m * (m - 1) / 2) := Nat.mul_le_mul hj hN3
    calc 9 = 3 * 3 := by norm_num
      _ ≤ 3 * (j * (m * (m - 1) / 2)) := Nat.mul_le_mul_left 3 hjN
      _ = 3 * j * (m * (m - 1) / 2) := by ring
  omega

theorem multiplicity_eq_two_of_card_centerQuotient_eq_5515776 {E : Type} [Field E] [Finite E]
    {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) (hE : Nat.card E = 2 ^ (3 * j)) {K : Type*} [Group K]
    (f : SpecialLinearGroup (Fin m) E →* K) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center (SpecialLinearGroup (Fin m) E))
    (hQ : CFSG.IsQuasisimple (SpecialLinearGroup (Fin m) E))
    (hN : Nat.card (K ⧸ Subgroup.center K) = 5515776) :
    m = 2 := by
  have hdvdK := pow_dvd_card_centerQuotient_of_surjective_specialLinear (e := 3 * j)
    (by omega) (by omega) hE f hf hker (Group.isPerfect_def.mp hQ.1)
  rw [hN, show (5515776 : ℕ) = 512 * 10773 by norm_num] at hdvdK
  have hcop10773 : Nat.Coprime (2 ^ (3 * j * (m * (m - 1) / 2))) 10773 :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr (by norm_num : Odd 10773))
  have hdvd512 : 2 ^ (3 * j * (m * (m - 1) / 2)) ∣ 512 :=
    Nat.Coprime.dvd_of_dvd_mul_right hcop10773 hdvdK
  have hle : 3 * j * (m * (m - 1) / 2) ≤ 9 :=
    (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp (by simpa using hdvd512)
  rcases Nat.lt_or_ge m 3 with hm2 | hm3
  · omega
  rcases Nat.lt_or_ge m 4 with hm3' | hm4
  ·
    have hm3e : m = 3 := by omega
    have hj1 : j = 1 := by
      subst hm3e
      norm_num at hle
      omega
    subst hm3e
    subst hj1
    have hE8 : Nat.card E = 8 := by rw [hE]; norm_num
    have hsplit : Nat.card (SpecialLinearGroup (Fin 3) E) =
        Nat.card (K ⧸ Subgroup.center K) * Nat.card (scalars 3 E) := by
      rw [card_eq_card_centerQuotient_mul_card_center_of_surjective
        (Group.isPerfect_def.mp hQ.1) f hf hker, scalars_eq_center]
    have h73SL : 73 ∣ Nat.card (SpecialLinearGroup (Fin 3) E) := by
      rw [card_SL_eq (by norm_num : 1 ≤ 3), hE8,
        Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 2 + 1), Finset.Icc_self,
        Finset.prod_singleton]
      norm_num
    have hZ7 : Nat.card (scalars 3 E) ∣ 7 := by
      have h := card_scalars_dvd (K := E) (n := 3) (by norm_num)
      rwa [hE8] at h
    have h73Z : ¬ 73 ∣ Nat.card (scalars 3 E) :=
      fun h => absurd (h.trans hZ7) (by norm_num)
    have hprod : Nat.card (SpecialLinearGroup (Fin 3) E) = 5515776 * Nat.card (scalars 3 E) := by
      rw [hsplit, hN]
    have h73 : 73 ∣ 5515776 * Nat.card (scalars 3 E) := hprod ▸ h73SL
    rcases (show Nat.Prime 73 by norm_num).dvd_mul.mp h73 with h | h
    · exact absurd h (by norm_num)
    · exact absurd h h73Z
  ·
    have hN6 : 6 ≤ m * (m - 1) / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
      calc 6 * 2 = 12 := by norm_num
        _ ≤ m * (m - 1) := Nat.mul_le_mul hm4 (by omega : 3 ≤ m - 1)
    have hjN : 6 ≤ j * (m * (m - 1) / 2) := by
      calc 6 = 1 * 6 := by norm_num
        _ ≤ j * (m * (m - 1) / 2) := Nat.mul_le_mul hj hN6
    have : 18 ≤ 3 * j * (m * (m - 1) / 2) := by
      have h18 := Nat.mul_le_mul_left 3 hjN
      calc 18 = 3 * 6 := by norm_num
        _ ≤ 3 * (j * (m * (m - 1) / 2)) := h18
        _ = 3 * j * (m * (m - 1) / 2) := by ring
    omega

theorem multiplicity_eq_two_of_compAlgEight {E : Type} [Field E] [Finite E] {m j : ℕ}
    (hm : 2 ≤ m) (hj : 1 ≤ j) (hE : Nat.card E = 2 ^ (3 * j)) {K : Type*} [Group K]
    (f : SpecialLinearGroup (Fin m) E →* K) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center (SpecialLinearGroup (Fin m) E))
    (hQ : CFSG.IsQuasisimple (SpecialLinearGroup (Fin m) E))
    (hN : Nat.card (K ⧸ Subgroup.center K) = 504 ∨
      Nat.card (K ⧸ Subgroup.center K) = 5515776) :
    m = 2 := by
  rcases hN with hN | hN
  · exact multiplicity_eq_two_of_card_centerQuotient_eq_504 hm hj hE f hf hker hQ hN
  · exact multiplicity_eq_two_of_card_centerQuotient_eq_5515776 hm hj hE f hf hker hQ hN

theorem card_catGroup_A_one_eight {k : Type} [Field k] [Finite k] (hk : Nat.card k = 8)
    {q : TauCeti.PrimePower} (hq : q.card = 8)
    {hv : (TauCeti.LieTypeIndex.A 1 q).Valid} :
    Nat.card (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.A 1 q, hv⟩).Group = 504 := by
  obtain ⟨e⟩ := CFSG.Adapters.CatalogueFieldBridges.nonempty_projectiveSL_mulEquiv_lie
    (n := 1) (k := k) q hv (by rw [hk, hq])
  rw [← Nat.card_congr e.toEquiv, card_projectiveSL, card_SL_eq (by norm_num : 1 ≤ 2), hk,
    CFSG.RankThree.PartOne.card_scalars (by norm_num : 0 < 2), hk, Finset.Icc_self,
    Finset.prod_singleton]
  norm_num

theorem card_catGroup_twistedA_two_eight {q : TauCeti.PrimePower} (hq : q.card = 8)
    {hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid} :
    Nat.card (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedA 2 q, hv⟩).Group = 5515776 := by
  let G := (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedA 2 q, hv⟩).Group
  have hmodel : CFSG.Open.StatedClassicalModel G .PSU 3 q.p q.exponent := by
    simpa using CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv (MulEquiv.refl G)
  have h := CFSG.Open.StatedAPI.card_mul_gcd_of_statedClassicalModel_psu_three hmodel
  have hq' : q.p ^ q.exponent = 8 := by
    rw [← TauCeti.PrimePower.card_def q]
    exact hq
  dsimp only [G] at h ⊢
  rw [hq'] at h
  norm_num at h ⊢
  omega

theorem subgroupStabRestrict_conjAut_eq_conj {n : ℕ} {k : Type*} [Field k]
    {A : GL (Fin n) k} {h : Polynomial k} {X : GL (Fin n) k}
    {s : SpecialLinearGroup (Fin n) k}
    (hs : s ∈ specialFactor A h)
    (hconj : ∀ m ∈ specialFactor A h,
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n k X m =
        s * m * s⁻¹)
    (hx : conjAut n k X ∈ CFSG.GroupActions.subgroupStabAut
      ((specialFactor A h).map (proj n k))) :
    CFSG.GroupActions.subgroupStabRestrict ((specialFactor A h).map (proj n k))
        ⟨conjAut n k X, hx⟩ =
      MulAut.conj (⟨proj n k s, Subgroup.mem_map_of_mem (proj n k) hs⟩ :
        Subgroup.map (proj n k) (specialFactor A h)) := by
  ext y
  obtain ⟨m, hm, hmv⟩ := y.2
  have hy : y = ⟨proj n k m, Subgroup.mem_map_of_mem (proj n k) hm⟩ :=
    Subtype.ext hmv.symm
  subst hy
  rw [CFSG.GroupActions.subgroupStabRestrict_apply, MulAut.conj_apply, conjAut_proj]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [← map_mul, ← map_inv, ← map_mul, hconj m hm]

theorem linearCompAlgEight_holds : LinearCompAlgEight := by
  intro n hn k _ _ hk β hβmem hβ3 hβ1 K hK e hidx hKiso x hxmem hx3 hβx hxstab
  obtain ⟨A, rfl⟩ := mem_linearAutGroup_iff.1
    (innAutDerived_projectiveSL_le_linearAutGroup hn hβmem)
  obtain ⟨X, rfl⟩ := mem_linearAutGroup_iff.1
    (innAutDerived_projectiveSL_le_linearAutGroup hn hxmem)
  have hA3 : conjAut n k (A ^ 3) = 1 := by rw [map_pow, hβ3]
  obtain ⟨c, hc⟩ := exists_eq_scalar_of_conjAut_eq_one hn hA3
  have hX3 : conjAut n k (X ^ 3) = 1 := by rw [map_pow, hx3]
  obtain ⟨ν, hν⟩ := exists_eq_scalar_of_conjAut_eq_one hn hX3
  have hAX : A * X = X * A := mul_comm_of_commute_conjAut_pow_three hn hk hx3 hβx
  letI : Fintype k := Fintype.ofFinite k
  haveI : CharP k 2 := charP_of_card_eq_prime_pow (p := 2) (f := 3)
    (by rw [← Nat.card_eq_fintype_card]; rw [hk]; norm_num)
  have hpk : (3 : k) ≠ 0 := by
    intro h0
    have hd : (2 : ℕ) ∣ 3 := (CharP.cast_eq_zero_iff k 2 3).1 h0
    norm_num at hd
  have hsq := squarefree_minpoly_glA hpk hc
  obtain ⟨h, rfl⟩ := linear_inner_components hpk hc K hK
  haveI : Fact (Irreducible h.1.1) := ⟨irreducible_of_mem_primaryFactors h.1.2⟩
  haveI : Finite (AdjoinRoot h.1.1) := Module.finite_of_finite k
  obtain ⟨eF⟩ := nonempty_mulEquiv_specialFactor (A := A) hsq h.1.2
  obtain ⟨f, hf, hker⟩ := exists_surjective_ker_le_center_map_proj
    (n := n) (k := k) (S := specialFactor A h.1.1)
    (G := ↥(specialFactor A h.1.1)) (MulEquiv.refl _)
  let m := primaryMultiplicity (glA A : Module.End k (Fin n → k)) h.1.1
  let E := AdjoinRoot h.1.1
  let K' : Subgroup (projectiveSL n k) := (specialFactor A h.1.1).map (proj n k)
  have hcardE : Nat.card E = Nat.card k ^ h.1.1.natDegree :=
    CFSG.RankThree.PartOne.KCLinPlane.natCard_adjoinRoot h.1.1
  have hE8 : Nat.card E = 2 ^ (3 * h.1.1.natDegree) := by
    dsimp only [E]
    rw [hcardE, hk, show (8 : ℕ) = 2 ^ 3 by norm_num, pow_mul]
  have hm : 2 ≤ m := by
    dsimp only [m]
    rcases h.2 with h3 | ⟨h2, -⟩
    · omega
    · exact h2
  have hj : 1 ≤ h.1.1.natDegree := (Fact.out : Irreducible h.1.1).natDegree_pos
  have hQ : CFSG.IsQuasisimple (SpecialLinearGroup (Fin m) E) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eF.symm
      (isQuasisimple_specialFactor hsq h.1.2 h.2)
  have hf' : Function.Surjective (f.comp eF.toMonoidHom) := hf.comp eF.surjective
  have hker' : (f.comp eF.toMonoidHom).ker ≤ Subgroup.center (SpecialLinearGroup (Fin m) E) := by
    intro z hz
    have hc' : eF z ∈ Subgroup.center ↥(specialFactor A h.1.1) :=
      hker (show eF z ∈ f.ker from hz)
    refine Subgroup.mem_center_iff.2 ?_
    intro y
    apply eF.injective
    rw [map_mul, map_mul, Subgroup.mem_center_iff.1 hc' (eF y)]
  obtain ⟨ei, hv⟩ := e
  obtain ⟨eK⟩ := hKiso
  have hN : Nat.card (K' ⧸ Subgroup.center K') = 504 ∨
      Nat.card (K' ⧸ Subgroup.center K') = 5515776 := by
    obtain ⟨q, hq, hqcard⟩ := hidx
    rcases hq with hA | htw
    · subst hA
      left
      exact (Nat.card_congr eK.toEquiv).trans (card_catGroup_A_one_eight hk hqcard)
    · subst htw
      right
      exact (Nat.card_congr eK.toEquiv).trans (card_catGroup_twistedA_two_eight hqcard)
  have hm2 : m = 2 :=
    multiplicity_eq_two_of_compAlgEight (E := E) (m := m) (j := h.1.1.natDegree)
      (K := K') hm hj hE8 (f.comp eF.toMonoidHom) hf' hker' hQ hN
  obtain ⟨s, hs, hconj⟩ := key_specialFactor hsq h.1.2 hm2 hAX.symm hν
  have hres := subgroupStabRestrict_conjAut_eq_conj (A := A) (h := h.1.1) (X := X)
    (s := s) hs hconj hxstab
  rw [hres]
  rw [CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_conj]
  exact inner_le_innAutDerived _ ⟨_, rfl⟩

theorem lieCompAlg_linear : LieCompAlg isLinearIdx :=
  lieCompAlg_linear_of_eight linearCompAlgEight_holds

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
