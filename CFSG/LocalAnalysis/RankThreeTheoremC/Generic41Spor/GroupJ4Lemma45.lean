module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupWitnessSylow
public import CFSG.Sporadic.Schreier.J4SEleven
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupJ4Trans
import CFSG.Sporadic.Bridge.J4Surj
import CFSG.Sporadic.J4.QT2AMain
import CFSG.Sporadic.J4.QT2LocMain
import CFSG.Sporadic.J4.QTRankInvProof
import CFSG.Sporadic.Schreier.J4SOutOdd
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupBridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open Subgroup CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier

private theorem twoWitness_of_constrained {G : Type} [Group G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {t u : G} (hu : orderOf u = p) (hut : u * t = t * u)
    (hcon : ∃ N : Subgroup G, N ≤ centralizer ({t} : Set G) ∧
      (∀ q ∈ centralizer ({t} : Set G), ∀ e ∈ N, q * e * q⁻¹ ∈ N) ∧ IsPGroup 2 ↥N ∧
      ∀ q ∈ centralizer ({t} : Set G), (∀ e ∈ N, q * e = e * q) → q ∈ N) :
    TwoWitness u := by
  obtain ⟨N, -, hNn, hN2, hNs⟩ := hcon
  have huC : u ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact hut.symm
  have huC' : u⁻¹ ∈ centralizer ({t} : Set G) := inv_mem huC
  refine ⟨N, hN2, ?_, ?_⟩
  · rw [mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hNn u huC h hh
    · intro hh
      have := hNn u⁻¹ huC' _ hh
      simpa [mul_assoc] using this
  · by_contra hcon
    have hcon' : ∀ e ∈ N, u * e = e * u := by
      intro e he
      by_contra hne
      exact hcon ⟨e, he, hne⟩
    have huN : u ∈ N := hNs u huC hcon'
    obtain ⟨k, hk⟩ := hN2 ⟨u, huN⟩
    have h1 : u ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have h2 : orderOf u ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
    rw [hu] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2))

private theorem conj_pow_eq_pow_pow_aux {G : Type*} [Group G] {a z : G} {m : ℕ}
    (h : a * z * a⁻¹ = z ^ m) (n : ℕ) : a ^ n * z * (a ^ n)⁻¹ = z ^ (m ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : a ^ (n + 1) * z * (a ^ (n + 1))⁻¹ = a ^ n * (a * z * a⁻¹) * (a ^ n)⁻¹ := by
      rw [pow_succ']
      group
    rw [h1, h, ← conj_pow, ih, ← pow_mul, pow_succ]

private theorem zin_le_aux {K : Type} [Group K] (S : Subgroup K) : Zin S ≤ S := by
  rintro _ ⟨⟨y, hy⟩, -, rfl⟩
  exact hy

private theorem twoWitness_of_centerTrans {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (htrans : NormalizerTransitiveCenter p K) {S₀ : Sylow p K} {u₀ : K}
    (hu₀ : u₀ ∈ Zin (S₀ : Subgroup K)) (hu₀1 : u₀ ≠ 1) (h₀ : TwoWitness u₀) :
    ∀ S : Sylow p K, ∀ u ∈ Zin (S : Subgroup K), u ≠ 1 → TwoWitness u := by
  intro S u hu hu1
  refine TwoWitness.of_sylow_pred hp (fun S x => x ∈ Zin S) ?_ hu₀ h₀ ?_ S (zin_le_aux _ hu) hu1 hu
  · intro S x g hx
    rw [zin_map_equiv (MulAut.conj g) S]
    exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
  · intro x _ hx1 hxZ
    exact htrans S₀ u₀ hu₀ hu₀1 x hxZ hx1

private theorem twoWitness_of_equiv_centerTrans {K K' : Type} [Group K] [Group K'] [Finite K]
    [Finite K'] {p : ℕ} (hp : p.Prime) (htrans : NormalizerTransitiveCenter p K) (e : K ≃* K')
    (T₀ : Sylow p K') {u₀ : K'} (hu₀ : u₀ ∈ Zin (T₀ : Subgroup K')) (hu₀1 : u₀ ≠ 1)
    (h₀ : TwoWitness u₀) :
    ∀ S : Sylow p K, ∀ u ∈ Zin (S : Subgroup K), u ≠ 1 → TwoWitness u := by
  haveI : Fact p.Prime := ⟨hp⟩
  let S₀ : Sylow p K := Sylow.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective T₀
  have hS₀ : (S₀ : Subgroup K) = (T₀ : Subgroup K').map e.symm.toMonoidHom := rfl
  have hu₀' : e.symm u₀ ∈ Zin (S₀ : Subgroup K) := by
    rw [hS₀, zin_map_equiv]
    exact Subgroup.mem_map.2 ⟨u₀, hu₀, rfl⟩
  have hu₀1' : e.symm u₀ ≠ 1 := by
    intro h
    apply hu₀1
    simpa using h
  exact twoWitness_of_centerTrans hp htrans hu₀' hu₀1' (h₀.of_mulEquiv e.symm)

section Step1b


theorem j4_exists_involution_commuting_qz :
    ∃ t : J, t * t = 1 ∧ t ≠ 1 ∧ t * qz = qz * t := by
  refine ⟨qu ^ 4, ?_, ?_, ?_⟩
  · rw [← pow_add]
    exact qu_pow_eight
  · intro h
    have h' := @sixteen_inj ((4 : Fin 8), (0 : Fin 2)) ((0 : Fin 8), (0 : Fin 2))
      (by simpa using h)
    simp at h'
  · have h1 : nrm₂ ^ 20 * qz * (nrm₂ ^ 20)⁻¹ = qz ^ (2 ^ 20) :=
      @conj_pow_eq_pow_pow_aux J (Subgroup.toGroup J) nrm₂ qz 2 nrm₂_qz 20
    have h2 : qz ^ (2 ^ 20) = qz := by
      rw [← pow_mod_orderOf, orderOf_qz]
      norm_num
    have h3 : qu ^ 4 = nrm₂ ^ 20 := by
      rw [qu, ← pow_mul]
    rw [h2] at h1
    rw [h3]
    calc nrm₂ ^ 20 * qz = nrm₂ ^ 20 * qz * (nrm₂ ^ 20)⁻¹ * nrm₂ ^ 20 := by group
      _ = qz * nrm₂ ^ 20 := by rw [h1]

end Step1b

section Step1a


theorem j4_involution_centralizer_constrained {t : J} (hsq : t * t = 1) (hne : t ≠ 1) :
    ∃ N : Subgroup J, N ≤ centralizer ({t} : Set J) ∧
      (∀ q ∈ centralizer ({t} : Set J), ∀ e ∈ N, q * e * q⁻¹ ∈ N) ∧ IsPGroup 2 ↥N ∧
      ∀ q ∈ centralizer ({t} : Set J), (∀ e ∈ N, q * e = e * q) → q ∈ N := by
  rcases CFSG.Sporadic.J4.QT.inv_conj_root j4Facts hsq hne with hc | hc
  · obtain ⟨g, hg⟩ := isConj_iff.1 hc
    refine CFSG.Sporadic.J4.QT2A.constrained_of_conj g⁻¹ t ?_
    have h : g⁻¹ * t * g⁻¹⁻¹ = CFSG.Sporadic.J4.QT.eta CFSG.Sporadic.J4.QT.uJ 11 1 := by
      rw [← hg]
      group
    rw [h]
    exact CFSG.Sporadic.J4.QT2.constrained_centralizer_eta_one
  · obtain ⟨g, hg⟩ := isConj_iff.1 hc
    refine CFSG.Sporadic.J4.QT2A.constrained_of_conj g⁻¹ t ?_
    have h : g⁻¹ * t * g⁻¹⁻¹ = CFSG.Sporadic.J4.QT.eta CFSG.Sporadic.J4.QT.uJ 11 3 := by
      rw [← hg]
      group
    rw [h]
    exact CFSG.Sporadic.J4.QT2A.constrained_centralizer_eta_three

end Step1a

section Step1c


theorem j4_witness_qz : TwoWitness (qz : J) := by
  obtain ⟨t, hsq, hne, hcomm⟩ := j4_exists_involution_commuting_qz
  exact @twoWitness_of_constrained J (Subgroup.toGroup J) 11 (by norm_num) (by norm_num) t qz
    orderOf_qz hcomm.symm (j4_involution_centralizer_constrained hsq hne)

end Step1c

section Step2


theorem j4_witness : ∀ (K : Type) [Group K] [Finite K], IsJ4Type 11 K →
    ∀ S : Sylow 11 K, ∀ u ∈ Zin (S : Subgroup K), u ≠ 1 → TwoWitness u := by
  intro K _ _ hK
  have htrans := j4_transCenter K hK
  obtain ⟨-, ⟨e⟩⟩ := hK
  have eKJ : K ≃* J :=
    e.trans ((CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv.some).symm.trans
      (seedEquiv j4Facts.mat))
  haveI : Finite J := Finite.of_equiv K eKJ.toEquiv
  have hZ : Zin (Q11Sylow : Subgroup J) = Subgroup.zpowers qz := by
    rw [Q11Sylow_coe]
    exact center_Q11
  have hu₀ : qz ∈ Zin (Q11Sylow : Subgroup J) := by
    rw [hZ]
    exact Subgroup.mem_zpowers qz
  exact @twoWitness_of_equiv_centerTrans K J _ (Subgroup.toGroup J) _ _ 11 (by norm_num) htrans
    eKJ Q11Sylow qz hu₀ qz_ne_one j4_witness_qz

end Step2

section Step3


theorem j4_lemma45 : Lemma45Facts IsJ4Type 11 J4Shape := by
  refine lemma45Facts_of_inner (by norm_num) (by norm_num) ?_
  intro X _ _ K hK R U₀ hUR hUe hUc hshape
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  haveI : K.Normal := hK.1
  obtain ⟨hne, hcomm⟩ := hshape
  obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  have hU₀ : U₀ = Subgroup.zpowers u := eq_zpowers_of_card_prime (by norm_num) hUc hu.1 hu1'
  have huK : u ∈ K := hu.2
  obtain ⟨P, hP⟩ := exists_sylow_inf_normal K R
  have huP : (⟨u, huK⟩ : K) ∈ Zin (P : Subgroup K) := by
    have huRK : u ∈ (R : Subgroup X) ⊓ K := ⟨hUR hu.1, huK⟩
    rw [← hP] at huRK
    obtain ⟨y, hyP, hyu⟩ := huRK
    have hy : y = ⟨u, huK⟩ := Subtype.ext hyu
    subst hy
    refine Subgroup.mem_map.2 ⟨⟨⟨u, huK⟩, hyP⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    apply Subtype.ext
    have hgRK : ((g : K) : X) ∈ (R : Subgroup X) ⊓ K := by
      rw [← hP]
      exact ⟨g, g.2, rfl⟩
    exact hcomm u hu _ hgRK
  have hW := j4_witness K hK.2.2 P ⟨u, huK⟩ huP
    (fun h => hu1' (congrArg Subtype.val h))
  exact ⟨hU₀ ▸ (Subgroup.zpowers_le.2 huK), kwitness_to_x K huK hW hU₀⟩

end Step3

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
