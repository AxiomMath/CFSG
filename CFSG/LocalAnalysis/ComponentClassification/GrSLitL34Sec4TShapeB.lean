module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4RealStd
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsReal
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InvClsZ4
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4EndT
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCenterBase
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsStandard
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsUnitaryFix
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Center46
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEnd46F
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEnd46Z
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEndT
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Lemma53
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrOddOrbitWitness
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.StrongEmbedding
public import CFSG.Walter.J1

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.GrSLit.L34Facts
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem zStarIn_le_coreActionKernel (J : Subgroup G) : zStarIn J ≤ coreActionKernel J := by
  rw [show zStarIn J = J ⊓ coreActionKernel J from GSThmB.map_fusionZStar_eq J]
  exact inf_le_right

theorem exists_mul_of_mem_sup_zStar {S J B : Subgroup G} (hS2 : IsPGroup 2 S)
    (hBSJ : B ≤ S ⊓ J) {y : G} (hy : y ∈ B ⊔ S ⊓ zStarIn J) :
    ∃ b ∈ B, ∃ z ∈ S ⊓ zStarIn J, b * z = y := by
  have hcomm : ∀ b ∈ B, ∀ z ∈ S ⊓ zStarIn J, z * b = b * z := fun b hb z hz =>
    mul_comm_of_mem_coreActionKernel hS2 (mem_inf.mp hz).1
      (zStarIn_le_coreActionKernel J (mem_inf.mp hz).2) (mem_inf.mp (hBSJ hb)).1
      (mem_inf.mp (hBSJ hb)).2
  have hBN : B ≤ normalizer ((S ⊓ zStarIn J : Subgroup G) : Set G) := fun b hb =>
    mem_normalizer_iff.mpr fun h => ⟨fun hh => by
      rw [← hcomm b hb h hh, mul_inv_cancel_right]
      exact hh, fun hh => by
      have e : h = b * h * b⁻¹ := by
        calc h = b⁻¹ * ((b * h * b⁻¹) * b) := by group
          _ = b⁻¹ * (b * (b * h * b⁻¹)) := by rw [hcomm b hb _ hh]
          _ = b * h * b⁻¹ := by group
      rw [e]
      exact hh⟩
  have hy' : y ∈ (B : Set G) * ((S ⊓ zStarIn J : Subgroup G) : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right B _ hBN]
    exact hy
  obtain ⟨b, hb, z, hz, rfl⟩ := hy'
  exact ⟨b, hb, z, hz, rfl⟩

omit [Finite G] in
theorem mul_comm_of_commutator_eq_one {x y : G} (h : x⁻¹ * y⁻¹ * x * y = 1) : x * y = y * x := by
  calc x * y = y * x * (x⁻¹ * y⁻¹ * x * y) := by group
    _ = y * x := by rw [h, mul_one]

section Std

variable {S J B : Subgroup G} {q : Jhat J →* Equiv.Perm (Fin 42)}
  (hqker : q.ker = center (Jhat J))
  (hT : ∀ e, q e ∈ T0 ↔ ∃ p ∈ S ⊓ J, ∃ hp : p ∈ J, jq J ⟨p, hp⟩ = e)
  (hqT0 : ∀ t ∈ T0, ∃ p ∈ S ⊓ J, ∃ hp : p ∈ J, q (jq J ⟨p, hp⟩) = t)
  (hBSJ : B ≤ S ⊓ J)
  (hBc : ∀ y ∈ S ⊓ J, (∀ w ∈ S ⊓ J, y⁻¹ * w⁻¹ * y * w ∈ zStarIn J) ↔ y ∈ B ⊔ (S ⊓ zStarIn J))
include hqker hT

omit [Finite G] in
theorem commutator_mem_zStarIn_of_central {p : G} (hpJ : p ∈ J)
    (hc : ∀ t ∈ T0, q (jq J ⟨p, hpJ⟩) * t = t * q (jq J ⟨p, hpJ⟩)) :
    ∀ w ∈ S ⊓ J, p⁻¹ * w⁻¹ * p * w ∈ zStarIn J := by
  intro w hw
  have hwJ : w ∈ J := (mem_inf.mp hw).2
  have hcJ : p⁻¹ * w⁻¹ * p * w ∈ J :=
    mul_mem (mul_mem (mul_mem (inv_mem hpJ) (inv_mem hwJ)) hpJ) hwJ
  rw [mem_zStarIn_iff hcJ, ← hqker, MonoidHom.mem_ker]
  have hw' : q (jq J ⟨w, hwJ⟩) ∈ T0 := (hT _).2 ⟨w, hw, hwJ, rfl⟩
  have e1 : (⟨p⁻¹ * w⁻¹ * p * w, hcJ⟩ : ↥J) =
      (⟨p, hpJ⟩ : ↥J)⁻¹ * (⟨w, hwJ⟩ : ↥J)⁻¹ * ⟨p, hpJ⟩ * ⟨w, hwJ⟩ := rfl
  rw [e1]
  simp only [map_mul, map_inv]
  have h := hc _ hw'
  calc (q (jq J ⟨p, hpJ⟩))⁻¹ * (q (jq J ⟨w, hwJ⟩))⁻¹ * q (jq J ⟨p, hpJ⟩) * q (jq J ⟨w, hwJ⟩) =
      (q (jq J ⟨p, hpJ⟩))⁻¹ * (q (jq J ⟨w, hwJ⟩))⁻¹ *
        (q (jq J ⟨p, hpJ⟩) * q (jq J ⟨w, hwJ⟩)) := by group
    _ = 1 := by rw [h]; group

include hqT0 hBSJ hBc in
omit [Finite G] in
theorem jq_mem_l34BHat (hB : IsElemTwo B) {b : G} (hb : b ∈ B) :
    jq J ⟨b, (mem_inf.mp (hBSJ hb)).2⟩ ∈ l34BHat q := by
  have hbJ : b ∈ J := (mem_inf.mp (hBSJ hb)).2
  refine ⟨(hT _).2 ⟨b, hBSJ hb, hbJ, rfl⟩, fun t ht => ?_, ?_⟩
  · obtain ⟨w, hwP, hwJ, rfl⟩ := hqT0 t ht
    have hc := (hBc b (hBSJ hb)).2 (mem_sup_left hb) w hwP
    have hcJ : b⁻¹ * w⁻¹ * b * w ∈ J :=
      mul_mem (mul_mem (mul_mem (inv_mem hbJ) (inv_mem hwJ)) hbJ) hwJ
    have hk : jq J ⟨b⁻¹ * w⁻¹ * b * w, hcJ⟩ ∈ q.ker := by
      rw [hqker]
      exact (mem_zStarIn_iff hcJ).1 hc
    have e1 : (⟨b⁻¹ * w⁻¹ * b * w, hcJ⟩ : ↥J) =
        (⟨b, hbJ⟩ : ↥J)⁻¹ * (⟨w, hwJ⟩ : ↥J)⁻¹ * ⟨b, hbJ⟩ * ⟨w, hwJ⟩ := rfl
    rw [MonoidHom.mem_ker, e1] at hk
    simp only [map_mul, map_inv] at hk
    exact mul_comm_of_commutator_eq_one hk
  · rw [← map_mul]
    exact (congrArg (jq J) (Subtype.ext (hB.2 b hb) :
      (⟨b, hbJ⟩ * ⟨b, hbJ⟩ : ↥J) = 1)).trans (map_one _)

include hBSJ hBc in
theorem exists_of_mem_l34BHat (hS2 : IsPGroup 2 S) (hB : IsElemTwo B)
    (hZc : IsCyclic ↥(S ⊓ zStarIn J)) {a : G} (haZ : a ∈ S ⊓ zStarIn J) (haa : a * a = 1)
    (ha1 : a ≠ 1) (haB : a ∈ B) {e : Jhat J} (he : e ∈ l34BHat q) :
    ∃ b ∈ B, ∃ hb : b ∈ J, jq J ⟨b, hb⟩ = e := by
  have hP2 : IsPGroup 2 (S ⊓ J : Subgroup G) := hS2.to_le inf_le_left
  obtain ⟨heT, hec, hee⟩ := he
  obtain ⟨p, hpP, hpJ, rfl⟩ := (hT _).1 heT
  have hpp : p * p = 1 :=
    eq_one_of_jq_eq_one inf_le_right hP2 (mul_mem hpP hpP)
      ((map_mul (jq J) ⟨p, hpJ⟩ ⟨p, hpJ⟩).trans hee)
  obtain ⟨b, hb, z, hz, rfl⟩ := exists_mul_of_mem_sup_zStar hS2 hBSJ
    ((hBc p hpP).1 (commutator_mem_zStarIn_of_central hqker hT hpJ hec))
  have hzb : z * b = b * z :=
    mul_comm_of_mem_coreActionKernel hS2 (mem_inf.mp hz).1
      (zStarIn_le_coreActionKernel J (mem_inf.mp hz).2) (mem_inf.mp (hBSJ hb)).1
      (mem_inf.mp (hBSJ hb)).2
  have hzz : z * z = 1 := by
    calc z * z = b * b * (z * z) := by rw [hB.2 b hb, one_mul]
      _ = b * (z * b) * z := by rw [hzb]; group
      _ = 1 := by rw [← hpp]; group
  have hzB : z ∈ B := by
    rcases eq_one_or_eq_of_isCyclic hZc haZ hz haa ha1 hzz with rfl | rfl
    exacts [one_mem _, haB]
  exact ⟨b * z, mul_mem hb hzB, hpJ, rfl⟩

include hBSJ hBc in
theorem jq_mem_l34AHat (hS2 : IsPGroup 2 S) (hB : IsElemTwo B)
    (hZc : IsCyclic ↥(S ⊓ zStarIn J)) {a : G} (haZ : a ∈ S ⊓ zStarIn J) (haa : a * a = 1)
    (ha1 : a ≠ 1) (haB : a ∈ B) {x : G} (hxP : x ∈ S ⊓ J)
    (hxC : x ∈ centralizer (B : Set G)) : jq J ⟨x, (mem_inf.mp hxP).2⟩ ∈ l34AHat q := by
  refine ⟨(hT _).2 ⟨x, hxP, _, rfl⟩, fun e he => ?_⟩
  obtain ⟨b, hb, hbJ, rfl⟩ :=
    exists_of_mem_l34BHat hqker hT hBSJ hBc hS2 hB hZc haZ haa ha1 haB he
  rw [← map_mul, ← map_mul]
  exact congrArg (jq J) (Subtype.ext (mem_centralizer_iff.mp hxC b hb).symm)

include hqT0 hBSJ hBc in
theorem exists_of_mem_l34AHat (hS2 : IsPGroup 2 S) (hB : IsElemTwo B) {e : Jhat J}
    (he : e ∈ l34AHat q) : ∃ x ∈ S ⊓ J, x ∈ centralizer (B : Set G) ∧
      ∃ hx : x ∈ J, jq J ⟨x, hx⟩ = e := by
  have hP2 : IsPGroup 2 (S ⊓ J : Subgroup G) := hS2.to_le inf_le_left
  obtain ⟨heT, hec⟩ := he
  obtain ⟨x, hxP, hxJ, rfl⟩ := (hT _).1 heT
  refine ⟨x, hxP, mem_centralizer_iff.mpr fun b hb => ?_, hxJ, rfl⟩
  have h := hec _ (jq_mem_l34BHat hqker hT hqT0 hBSJ hBc hB hb)
  rw [← map_mul, ← map_mul] at h
  exact (eq_of_jq_eq inf_le_right hP2 (mul_mem hxP (hBSJ hb)) (mul_mem (hBSJ hb) hxP) h).symm

include hqT0 hBSJ hBc in
theorem exists_of_mem_center_T0 (hS2 : IsPGroup 2 S) {z : Equiv.Perm (Fin 42)} (hz : z ∈ T0)
    (hzc : ∀ t ∈ T0, z * t = t * z) : ∃ b ∈ B, ∃ hb : b ∈ J, q (jq J ⟨b, hb⟩) = z := by
  obtain ⟨p, hpP, hpJ, rfl⟩ := hqT0 z hz
  obtain ⟨b, hb, z', hz', rfl⟩ := exists_mul_of_mem_sup_zStar hS2 hBSJ
    ((hBc p hpP).1 (commutator_mem_zStarIn_of_central hqker hT hpJ hzc))
  have hbJ : b ∈ J := (mem_inf.mp (hBSJ hb)).2
  have hz'J : z' ∈ J := (map_subtype_le _ : zStarIn J ≤ J) (mem_inf.mp hz').2
  have hz'K : q (jq J ⟨z', hz'J⟩) = 1 := by
    rw [← MonoidHom.mem_ker, hqker]
    exact (mem_zStarIn_iff hz'J).1 (mem_inf.mp hz').2
  refine ⟨b, hb, hbJ, ?_⟩
  rw [show (⟨b * z', hpJ⟩ : ↥J) = ⟨b, hbJ⟩ * ⟨z', hz'J⟩ from rfl, map_mul, map_mul, hz'K,
    mul_one]

end Std

theorem exists_mem_not_mem_zpowers {B : Subgroup G} (hB8 : Nat.card ↥B = 8) {a : G}
    (haa : a * a = 1) (ha1 : a ≠ 1) : ∃ b ∈ B, b ∉ zpowers a := by
  by_contra hno
  push Not at hno
  have hcard2 : Nat.card ↥(zpowers a) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact haa) ha1
  have h1 := card_le_of_le (show B ≤ zpowers a from hno)
  rw [hB8, hcard2] at h1
  omega

theorem pow_pow_ne_of_four {J B T : Subgroup G} {a : G} (hB : IsElemTwo B)
    (hB8 : Nat.card ↥B = 8) (hBJ : B ≤ J) (hBZ : B ⊓ zStarIn J = zpowers a) (haB : a ∈ B)
    (ha1 : a ≠ 1) (haa : a * a = 1) (hTs : IsSylowTwoIn T (centralizer (B : Set G)))
    (hAut : ∀ σ : ↥B ≃* ↥B, ∃ n ∈ normalizer (B : Set G), ∀ b : ↥B,
      n⁻¹ * (b : G) * n = (σ b : G))
    (h4 : ∀ t ∈ T, t ^ 4 ∈ coreActionKernel J) : ∀ t ∈ T, ∀ k : ℕ, (t ^ 4) ^ k ≠ a := by
  intro t ht k htk
  obtain ⟨b', hb'B, hb'a⟩ := exists_mem_not_mem_zpowers hB8 haa ha1
  have hb'1 : b' ≠ 1 := fun h => hb'a (h ▸ one_mem _)
  obtain ⟨ν, hν, hνa⟩ := exists_mem_normalizer_conj_eq hB hTs hAut haB hb'B ha1 hb'1
  have hνt : ν⁻¹ * t * ν ∈ T := conj_mem_of_mem_normalizer hν ht
  have hconj : ∀ n : ℕ, (ν⁻¹ * t * ν) ^ n = ν⁻¹ * t ^ n * ν := fun n => by
    have h := conj_pow (a := ν⁻¹) (b := t) (i := n)
    rwa [inv_inv] at h
  have h1 : b' = ((ν⁻¹ * t * ν) ^ 4) ^ k := by
    rw [← pow_mul, hconj, pow_mul, htk, hνa]
  have h2 : b' ∈ coreActionKernel J := by
    rw [h1]
    exact pow_mem (h4 _ hνt) k
  have h3 : b' ∈ zStarIn J := by
    rw [show zStarIn J = J ⊓ coreActionKernel J from GSThmB.map_fusionZStar_eq J]
    exact mem_inf.mpr ⟨hBJ hb'B, h2⟩
  exact hb'a (hBZ ▸ mem_inf.mpr ⟨hb'B, h3⟩)

omit [Finite G] in
theorem false_of_sq_eq {T T₁ : Subgroup G} {c₀ : G} (hc₀ : c₀ ∈ T) (hc₀1 : c₀ ∉ T₁)
    {a b' ν : G} (hν : ν ∈ normalizer (T : Set G)) (hνa : ν⁻¹ * a * ν = b') (hb' : b' ≠ a)
    (hsq : ∀ t ∈ T, t ∉ T₁ → t * t = a) : False := by
  have hout : ∀ t ∈ T, t ∉ T₁ → ν⁻¹ * t * ν ∈ T₁ := by
    intro t ht ht1
    by_contra h
    have h1 := hsq _ (conj_mem_of_mem_normalizer hν ht) h
    rw [show ν⁻¹ * t * ν * (ν⁻¹ * t * ν) = ν⁻¹ * (t * t) * ν by group, hsq t ht ht1, hνa] at h1
    exact hb' h1
  have hall : ∀ t ∈ T, ν⁻¹ * t * ν ∈ T₁ := by
    intro t ht
    by_cases ht1 : t ∈ T₁
    · have htc : t * c₀ ∉ T₁ := fun h => hc₀1 (by
        have := mul_mem (inv_mem ht1) h
        rwa [inv_mul_cancel_left] at this)
      rw [show ν⁻¹ * t * ν = (ν⁻¹ * (t * c₀) * ν) * (ν⁻¹ * c₀ * ν)⁻¹ by group]
      exact mul_mem (hout _ (mul_mem ht hc₀) htc) (inv_mem (hout _ hc₀ hc₀1))
    · exact hout t ht ht1
  have h := hall (ν * c₀ * ν⁻¹) ((mem_normalizer_iff.mp hν c₀).mp hc₀)
  rw [show ν⁻¹ * (ν * c₀ * ν⁻¹) * ν = c₀ by group] at h
  exact hc₀1 h

theorem le_of_forall_pow_four_ne {K Z : Subgroup G} (hKc : IsCyclic ↥K) (hK2 : IsPGroup 2 ↥K)
    (hZK : Z ≤ K) (hZ4 : Nat.card ↥Z = 4) {a : G} (haK : a ∈ K) (haa : a * a = 1)
    (ha1 : a ≠ 1) (h : ∀ t ∈ K, t ^ 4 ≠ a) : K ≤ Z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hK2
  by_cases hle : Nat.card ↥K ≤ 4
  · exact (eq_of_le_of_card_ge hZK (by rw [hZ4]; exact hle)).symm.le
  exfalso
  have hm3 : 3 ≤ m := by
    by_contra hm3
    push Not at hm3
    interval_cases m <;> simp_all
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥K)
  have hdvd : 2 ^ (m - 3) ∣ orderOf g := by
    rw [hg, hm]
    exact pow_dvd_pow 2 (Nat.sub_le m 3)
  have ht8 : orderOf (g ^ 2 ^ (m - 3)) = 8 := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) hdvd, hg, hm,
      Nat.pow_div (Nat.sub_le m 3) two_pos, show m - (m - 3) = 3 by omega]
    norm_num
  set t : ↥K := g ^ 2 ^ (m - 3) with htdef
  have hu2 : orderOf (t ^ 4) = 2 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [ht8]; norm_num), ht8]
  have huu : ((t ^ 4 : ↥K) : G) * ((t ^ 4 : ↥K) : G) = 1 := by
    have h1 := pow_orderOf_eq_one (t ^ 4)
    rw [hu2, pow_two] at h1
    exact congrArg Subtype.val h1
  have hu1 : ((t ^ 4 : ↥K) : G) ≠ 1 := fun h1 => by
    have : t ^ 4 = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hu2
    exact absurd hu2 (by norm_num)
  rcases eq_one_or_eq_of_isCyclic hKc haK (t ^ 4).2 haa ha1 huu with h1 | h1
  · exact hu1 h1
  · exact h (t : G) t.2 (by rw [← Subgroup.coe_pow]; exact h1)

end CFSG.ComponentClassification.GrSLit.GrS4
