module

public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieLT0Basic
public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieDatum
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5InvolutionRankOne
import CFSG.RankThree.GF2n.Tim78Normal
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.CGT.PushingUpLit.SolKAb (STSetting sylowImg)
open CFSG.ComponentClassification.AschbacherTheorem3 (IsQuaternionTwoGroup)
open CFSG.Assembly (pCoreOf)
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Generic
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.RankThree.GF2n.Tim78 (exists_odd_orderOf_pow)
open CFSG.ComponentClassification.AschbacherTheorem5.SectionSix
  (cyclic_or_quaternion_of_pRank_le_one)
open scoped MatrixGroups

section Datum

variable {G : Type} [Group G] [Finite G] {K : Subgroup G}

omit [Finite G] in
private theorem le_sylow_of_normal_pGroup {P K A : Subgroup G} (hP : IsSylowOf 2 P K)
    (hAK : A ≤ K) (hKA : K ≤ Subgroup.normalizer (A : Set G)) (hA : IsPGroup 2 A) : A ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hP.exists_sylow_eq_subgroupOf
  have : (Subgroup.comap K.subtype A).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAK).mpr hKA
  have hle : A.subgroupOf K ≤ (Q : Subgroup K) := (hA.comap_subtype (K := K)).le_sylow_of_normal Q
  rw [hQ] at hle
  intro x hx
  exact hle (show (⟨x, hAK hx⟩ : K) ∈ A.subgroupOf K from hx)

theorem lt3_datum (S : STSetting G K) (R : Sylow 2 K) (hq : IsQuaternionTwoGroup (sylowImg R)) :
    ∃ t : G, orderOf t = 2 ∧ t ∈ pCoreOf 2 K ∧ IsQuaternionTwoGroup (pCoreOf 2 K) ∧
      (∀ u ∈ pCoreOf 2 K, orderOf u = 2 → u = t) ∧
      pCoreOf 2 K ≤ Subgroup.centralizer ({t} : Set G) ∧
      ((pCoreOf 2 K).subgroupOf (Subgroup.centralizer ({t} : Set G))).Normal ∧
      Subgroup.centralizer ({t} : Set G) = Subgroup.normalizer (K : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht2, htR, hKt, hU⟩ := exists_central_involution_of_quaternion S R hq
  have htK : t ∈ K := (Subgroup.map_subtype_le _) htR
  have hCN := centralizer_eq_normalizer_of_quaternion S R hq htK ht2
  have hP2 : IsPGroup 2 (pCoreOf 2 K) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
  have hPK : pCoreOf 2 K ≤ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K
  have hKP : K ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have hsyl : IsSylowOf 2 (sylowImg R) K := ⟨R, rfl⟩
  have hPR : pCoreOf 2 K ≤ sylowImg R := le_sylow_of_normal_pGroup hsyl hPK hKP hP2
  have hPnc : ¬ IsCyclic ↥(pCoreOf 2 K) := by
    intro hcyc
    have hodd : ∀ a ∈ K, Odd (orderOf a) → a = 1 := fun a ha hao =>
      eq_one_of_odd_of_cyclic hP2 hcyc hKP S.inf_centralizer_pCoreOf_le ha hao
    have hK2 : IsPGroup 2 K := by
      intro c
      obtain ⟨n, hn, hn'⟩ := exists_odd_orderOf_pow (c : G)
      have hcn : (c : G) ^ 2 ^ n ∈ K := K.pow_mem c.2 _
      have := hodd _ hcn hn
      obtain ⟨k, hk⟩ := hn' this
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    have hKR : K = sylowImg R := hsyl.eq_of_le (Subgroup.map_subtype_le _) le_rfl hK2
    have hKP' : K ≤ pCoreOf 2 K := by
      refine CFSG.LieType.BorelTits.le_pCoreOf 2 le_rfl ?_ hK2
      rw [Subgroup.subgroupOf_self]
      exact Subgroup.normal_top
    have hPS : pCoreOf 2 K = sylowImg R := le_antisymm hPR (le_trans (le_of_eq hKR.symm) hKP')
    exact not_isCyclic_of_isQuaternionTwoGroup (P := pCoreOf 2 K) (by rw [hPS]; exact hq) hcyc
  have hPq : IsQuaternionTwoGroup (pCoreOf 2 K) := by
    have hr : CFSG.Open.pRank 2 (pCoreOf 2 K) ≤ 1 :=
      (CFSG.SectionRank.pRank_mono Nat.one_lt_two hPR).trans
        (CFSG.ComponentClassification.AschbacherTheorem5.Involution.pRank_le_one_of_quaternion hq)
    rcases cyclic_or_quaternion_of_pRank_le_one hP2 hr with hc | hq'
    · exact absurd hc hPnc
    · exact hq'
  obtain ⟨n, hn, ⟨e⟩⟩ := hPq
  obtain ⟨u, hu2, -, -⟩ :=
    CFSG.ClassicalInvolution.exists_unique_involution_of_mulEquiv_quaternionGroup e
  have hu2' : orderOf (u : G) = 2 := by rwa [Subgroup.orderOf_coe]
  have htP : t ∈ pCoreOf 2 K := by
    have h1 : (u : G) = t := hU _ (hPK u.2) hu2'
    rw [← h1]
    exact u.2
  have hPC : pCoreOf 2 K ≤ Subgroup.centralizer ({t} : Set G) := hPK.trans hKt
  refine ⟨t, ht2, htP, ⟨n, hn, ⟨e⟩⟩, fun v hv hv2 => hU v (hPK hv) hv2, hPC, ?_, hCN⟩
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hPC).mpr ?_
  rw [hCN]
  exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K

end Datum

theorem exists_noncomm_of_isQuaternionTwoGroup {G : Type} [Group G] {P : Subgroup G}
    (hP : IsQuaternionTwoGroup P) : ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a := by
  obtain ⟨n, hn, ⟨e⟩⟩ := hP
  have hne : NeZero (2 ^ (n - 2)) := ⟨by positivity⟩
  have h2 : 2 ≤ 2 ^ (n - 2) :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine ⟨((e.symm (QuaternionGroup.xa 0) : ↥P) : G), (e.symm (QuaternionGroup.xa 0)).2,
    ((e.symm (QuaternionGroup.a 1) : ↥P) : G), (e.symm (QuaternionGroup.a 1)).2, fun h => ?_⟩
  have h' : e.symm (QuaternionGroup.xa 0) * e.symm (QuaternionGroup.a 1) =
      e.symm (QuaternionGroup.a 1) * e.symm (QuaternionGroup.xa 0) := Subtype.ext h
  rw [← map_mul, ← map_mul] at h'
  have h'' := e.symm.injective h'
  rw [QuaternionGroup.xa_mul_a, QuaternionGroup.a_mul_xa] at h''
  have h3 : (1 : ZMod (2 * 2 ^ (n - 2))) = - 1 := by
    have := QuaternionGroup.xa.inj h''
    simpa using this
  have h4 : ((2 : ℕ) : ZMod (2 * 2 ^ (n - 2))) = 0 := by
    have : (1 : ZMod (2 * 2 ^ (n - 2))) + 1 = 0 := by
      rw [add_eq_zero_iff_eq_neg]
      exact h3
    simpa [one_add_one_eq_two] using this
  rw [ZMod.natCast_eq_zero_iff] at h4
  have := Nat.le_of_dvd (by norm_num) h4
  omega

theorem sl2_center_of_sq_eq_one {F : Type} [Field F] (h2 : (2 : F) ≠ 0) {y : SL(2, F)}
    (hy : y ^ 2 = 1) : y ∈ Subgroup.center SL(2, F) := by
  have hm : (y : Matrix (Fin 2) (Fin 2) F) * y = 1 := by
    have := congrArg (fun z : SL(2, F) => (z : Matrix (Fin 2) (Fin 2) F)) hy
    simpa [pow_two] using this
  have hdet : (y : Matrix (Fin 2) (Fin 2) F).det = 1 := y.2
  rw [Matrix.det_fin_two] at hdet
  have e00 := congrFun (congrFun hm 0) 0
  have e01 := congrFun (congrFun hm 0) 1
  have e10 := congrFun (congrFun hm 1) 0
  have e11 := congrFun (congrFun hm 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  set a := (y : Matrix (Fin 2) (Fin 2) F) 0 0
  set b := (y : Matrix (Fin 2) (Fin 2) F) 0 1
  set c := (y : Matrix (Fin 2) (Fin 2) F) 1 0
  set d := (y : Matrix (Fin 2) (Fin 2) F) 1 1
  by_cases had : a + d = 0
  · exfalso
    have hd : d = -a := by linear_combination had
    apply h2
    rw [hd] at hdet
    linear_combination -e00 - hdet
  · have hb : b = 0 := by
      have : b * (a + d) = 0 := by linear_combination e01
      exact (mul_eq_zero.mp this).resolve_right had
    have hc : c = 0 := by
      have : c * (a + d) = 0 := by linear_combination e10
      exact (mul_eq_zero.mp this).resolve_right had
    have ha1 : a * a = 1 := by rw [hb] at e00; linear_combination e00
    have hda : d = a := by
      have : a * (d - a) = 0 := by rw [hb, hc] at hdet; linear_combination hdet - ha1
      have ha0 : a ≠ 0 := fun h => by rw [h] at ha1; simp at ha1
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left ha0)
    rw [Matrix.SpecialLinearGroup.mem_center_iff]
    refine ⟨a, ?_, ?_⟩
    · rw [Fintype.card_fin, pow_two]; exact ha1
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, a, b, c, d, hb, hc, hda]

section Bridge


theorem lt3_central_of_involution {τ : StatedLieTag} {n : ℕ} (hf : IsFundTag τ)
    (ha : StatedLieAdmissible τ n 3 1) (hG2 : τ ≠ .G2) (hD4 : τ ≠ .trialityD4)
    {X : Type} [Group X] (ψ : (modelUniv τ n 3 1 Nat.prime_three).K →* X)
    (hker : ψ.ker ≤ Subgroup.center _)
    {R : Subgroup (modelUniv τ n 3 1 Nat.prime_three).K}
    (hR : R ∈ fundamentalSubgroups τ (modelUniv τ n 3 1 Nat.prime_three).D)
    {t : X} (ht : t ∈ R.map ψ) (ht2 : orderOf t = 2) : ∀ j ∈ R.map ψ, j * t = t * j := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := CFSG.ClassicalInvolution.ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups
    (p := 3) (e := 1) (by norm_num) hf ha hG2 hD4 hR
  have hne : ¬ (τ = .PSL ∧ n = 2) := by
    rintro ⟨rfl, rfl⟩
    have := ha.2.2.2.2
    simp at this
  have hinj : ∀ x ∈ R, ψ x = 1 → x = 1 := by
    intro x hx hψx
    refine CFSG.ClassicalInvolution.ModelFacts.fundNoncentral_generic 3 τ n 1 hf ha hne R hR x hx
      fun y => ?_
    have hxc : x ∈ Subgroup.center (modelUniv τ n 3 1 Nat.prime_three).K :=
      hker (MonoidHom.mem_ker.mpr hψx)
    have hxy : x * y = y * x := (Subgroup.mem_center_iff.mp hxc y).symm
    have : x * y * x⁻¹ * y⁻¹ = 1 := by rw [hxy]; group
    rw [this]
    exact one_mem _
  obtain ⟨r, hrR, rfl⟩ := Subgroup.mem_map.mp ht
  have hr2 : r ^ 2 = 1 := by
    refine hinj (r ^ 2) (R.pow_mem hrR 2) ?_
    rw [map_pow]
    simpa [ht2] using pow_orderOf_eq_one (ψ r)
  have hy2 : (e ⟨r, hrR⟩) ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨r, hrR⟩ : R) ^ 2 = 1 := Subtype.ext hr2
    rw [this, map_one]
  have hcen := sl2_center_of_sq_eq_one
    (CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField 1 (by norm_num)) hy2
  intro j hj
  obtain ⟨s, hsR, rfl⟩ := Subgroup.mem_map.mp hj
  have hcomm : (⟨s, hsR⟩ : R) * ⟨r, hrR⟩ = ⟨r, hrR⟩ * ⟨s, hsR⟩ := by
    apply e.injective
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.mp hcen (e ⟨s, hsR⟩)
  have h' := congrArg Subtype.val hcomm
  rw [← map_mul, ← map_mul]
  exact congrArg ψ h'

theorem lie3At_of_kill {τ : StatedLieTag} {n : ℕ} (hG2 : τ ≠ .G2) (hD4 : τ ≠ .trialityD4)
    (hk : Kill3At τ n) : Lie3At τ n := by
  intro hf ha X _ _ ψ hψ hker R hR K hK R₀ hq hP
  have : IsSimpleGroup X := hK.simple
  have hker' := ker_eq_center_of_simple hK.nonab ψ hψ hker
  obtain ⟨t, ht2, htP, hPq, -, hPC, hPn, hCN⟩ := lt3_datum hK R₀ hq
  have htJ : t ∈ R.map ψ := hP htP
  have hcen := lt3_central_of_involution hf ha hG2 hD4 ψ hker hR htJ ht2
  rcases hk X ψ hψ hker' R hR t htJ ht2 hcen with ⟨w, hw, hcomm⟩ | ⟨E, hE, hqE⟩
  · exact (false_of_commuting_conj hw hP hcomm hPC hPn
      (exists_noncomm_of_isQuaternionTwoGroup hPq)).elim
  · refine (false_of_component (C := Subgroup.centralizer ({t} : Set X)) ?_ hE hqE).elim
    rw [hCN]
    exact hK.fstar

end Bridge

end CFSG.CGT.PushingUpLit.SolKNA
