module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5TWGen
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Single

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5S

open CFSG Subgroup CFSG.ComponentClassification CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem isSylowTwoIn_inf_of_isPComponent {P M K : Subgroup G} (hP : IsSylowTwoIn P M)
    (hKM : K ≤ M) (hK : IsPComponent 2 (K.subgroupOf M)) : IsSylowTwoIn (P ⊓ K) K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hsub, -⟩ := hK
  obtain ⟨hPM, P₀, hP₀⟩ := hP
  obtain ⟨P₁, hP₁⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal P₀ hsub
  let e : (K.subgroupOf M) ≃* K := subgroupOfEquivOfLe hKM
  have he : Function.Surjective e.toMonoidHom := fun y => ⟨e.symm y, e.apply_symm_apply y⟩
  refine ⟨inf_le_right, P₁.mapSurjective he, ?_⟩
  apply map_injective K.subtype_injective
  rw [Sylow.coe_mapSurjective, map_map]
  have hcomp : K.subtype.comp e.toMonoidHom = M.subtype.comp (K.subgroupOf M).subtype := by
    ext x
    rfl
  rw [hcomp, ← map_map, hP₁, map_inf_eq _ _ M.subtype M.subtype_injective, hP₀,
    subgroupOf_map_subtype, subgroupOf_map_subtype, subgroupOf_map_subtype, inf_eq_left.mpr hPM,
    inf_eq_left.mpr hKM, inf_assoc, inf_idem]

theorem conjugate_le_coreActionKernel {M K : Subgroup G} (hKM : K ≤ M)
    (hK : IsPComponent 2 (K.subgroupOf M)) {g : G} (hg : g ∈ M) (hne : conjugate K g ≠ K) :
    conjugate K g ≤ coreActionKernel K := by
  have hKgM := UnbalancedCorr.conjugate_le_of_mem hKM hg
  have hKg := UnbalancedCorr.isPComponent_conjugate_subgroupOf hg hK
  have hne' : K ≠ conjugate K g := fun h => hne h.symm
  have hN := (GrS5.commutator_le_of_ne hKM hKgM hK hKg hne').2
  have hc := GrS5.commutator_le_inf_oddIn hKM hKgM hK hKg hne'
  intro y hy
  refine mem_coreActionKernel.mpr ⟨hN hy, fun j hj => ?_⟩
  have h1 : ⁅j⁻¹, y⁻¹⁆ ∈ ⁅K, conjugate K g⁆ :=
    commutator_mem_commutator (inv_mem hj) (inv_mem hy)
  have h2 := (hc h1)
  rw [commutatorElement_def, inv_inv, inv_inv] at h2
  exact (mem_inf.mp h2).1

theorem oddIn_le_coreActionKernel {M K : Subgroup G} (hKM : K ≤ M)
    (hK : IsPComponent 2 (K.subgroupOf M)) : oddIn M ≤ coreActionKernel K := by
  have hON := GrS4.oddIn_le_normalizer_of_isPComponent hKM hK
  intro o ho
  refine mem_coreActionKernel.mpr ⟨hON ho, fun j hj => ?_⟩
  have hjK : j⁻¹ * o⁻¹ * j * o ∈ K := by
    have h1 : o⁻¹ * j * o ∈ K := by
      have := (mem_normalizer_iff.mp (inv_mem (hON ho)) j).mp hj
      rwa [inv_inv] at this
    have := mul_mem (inv_mem hj) h1
    rwa [show j⁻¹ * (o⁻¹ * j * o) = j⁻¹ * o⁻¹ * j * o by group] at this
  have hjO : j⁻¹ * o⁻¹ * j * o ∈ oddIn M := by
    have h1 := GrS4.conj_mem_oddIn (inv_mem (hKM hj)) (inv_mem ho)
    rw [inv_inv] at h1
    exact mul_mem h1 ho
  exact GrS5.inf_oddIn_le_oddIn hKM (mem_inf.mpr ⟨hjO, hjK⟩)

theorem le_withKernel_of_le_sup {M K J : Subgroup G} (hKM : K ≤ M)
    (hK : IsPComponent 2 (K.subgroupOf M)) {g : G} (hg : g ∈ M) (hne : conjugate K g ≠ K)
    (hJ : J ≤ K ⊔ conjugate K g ⊔ oddIn M) : J ≤ withKernel K :=
  hJ.trans (sup_le (sup_le le_sup_left
    ((conjugate_le_coreActionKernel hKM hK hg hne).trans le_sup_right))
    ((oddIn_le_coreActionKernel hKM hK).trans le_sup_right))

theorem conjugate_eq_of_le {M K J : Subgroup G} (hKM : K ≤ M)
    (hK : IsPComponent 2 (K.subgroupOf M)) (hJK : J ≤ K) (hJ : ⁅J, J⁆ = J)
    (hJo : ¬ Odd (Nat.card J)) {g : G} (hgM : g ∈ M) (hgJ : g ∈ normalizer (J : Set G)) :
    conjugate K g = K := by
  by_contra hne
  have hKgM := UnbalancedCorr.conjugate_le_of_mem hKM hgM
  have hc := GrS5.commutator_le_inf_oddIn hKM hKgM hK
    (UnbalancedCorr.isPComponent_conjugate_subgroupOf hgM hK) fun h => hne h.symm
  have hJKg : J ≤ conjugate K g := fun y hy => by
    rw [UnbalancedLayer.mem_conjugate_iff]
    exact hJK ((mem_normalizer_iff.mp hgJ y).mp hy)
  have hJO : J ≤ oddIn K := by
    rw [← hJ]
    exact (commutator_mono hJK hJKg).trans (hc.trans inf_le_left)
  exact hJo (Odd.of_dvd_nat (odd_card_map_pPrimeCore K) (card_dvd_of_le hJO))

theorem mem_coreActionKernel_of_sup_eq {M K J : Subgroup G} (hKM : K ≤ M)
    (hK : IsPComponent 2 (K.subgroupOf M)) (hJM : J ≤ M) (hJ : ⁅J, J⁆ = J)
    (hJo : ¬ Odd (Nat.card J)) (hsup : J ⊔ oddIn M = K ⊔ oddIn M) {a : G} (haM : a ∈ M)
    (hJa : J ≤ centralizer ({a} : Set G)) : a ∈ coreActionKernel K := by
  have hJK := GrS4.le_of_sup_oddIn_eq hJM hKM hK hJ hsup
  have haJ : a ∈ normalizer (J : Set G) := L34Facts.mem_normalizer_of_commute fun x hx =>
    (mem_centralizer_singleton_iff.mp (hJa hx)).symm
  have hKa := conjugate_eq_of_le hKM hK hJK hJ hJo haM haJ
  have haN : a ∈ normalizer (K : Set G) := UnbalancedLayer.mem_normalizer_of_conjugate_eq hKa
  refine mem_coreActionKernel.mpr ⟨haN, fun k hk => ?_⟩
  have hset : ((K : Subgroup G) : Set G) = (J : Set G) * (oddIn K : Set G) := by
    conv_lhs => rw [GrS4.eq_sup_oddIn_of_sup_eq hJK hKM hsup]
    exact coe_mul_of_left_le_normalizer_right _ _ (hJK.trans (GrS4.self_le_normalizer_oddIn K))
  have hk' : k ∈ (J : Set G) * (oddIn K : Set G) := hset ▸ hk
  obtain ⟨j, hj, o, ho, rfl⟩ := hk'
  beta_reduce
  have hc : Commute j a⁻¹ :=
    Commute.inv_right (mem_centralizer_singleton_iff.mp (hJa hj))
  have e : (j * o)⁻¹ * a⁻¹ * (j * o) * a = o⁻¹ * (a⁻¹ * o * a⁻¹⁻¹) := by
    calc (j * o)⁻¹ * a⁻¹ * (j * o) * a = o⁻¹ * j⁻¹ * (a⁻¹ * j) * o * a := by group
      _ = o⁻¹ * j⁻¹ * (j * a⁻¹) * o * a := by rw [← hc.eq]
      _ = o⁻¹ * (a⁻¹ * o * a⁻¹⁻¹) := by group
  rw [e]
  exact mul_mem (inv_mem ho) (GrS4.conj_mem_oddIn_of_mem_normalizer (inv_mem haN) ho)


theorem exists_involution_inf_centralizer {P E S : Subgroup G} (hS2 : IsPGroup 2 S)
    (hPS : P ≤ S) (hES : E ≤ S) (hEN : E ≤ normalizer (P : Set G)) (hP : P ≠ ⊥) :
    ∃ c ∈ P, c * c = 1 ∧ c ≠ 1 ∧ ∀ e ∈ E, c * e = e * c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P' := P ⊔ E with hP'
  have hP'2 : IsPGroup 2 P' := hS2.to_le (sup_le hPS hES)
  have : Group.IsNilpotent P' := hP'2.isNilpotent
  have hPn : (P.subgroupOf P').Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr (sup_le le_normalizer hEN)
  have hPne' : P.subgroupOf P' ≠ ⊥ := by
    intro h
    apply hP
    rw [eq_bot_iff]
    intro y hy
    have h1 : (⟨y, mem_sup_left hy⟩ : P') ∈ P.subgroupOf P' := hy
    rw [h, mem_bot] at h1
    rw [mem_bot]
    exact congrArg Subtype.val h1
  have hmeet := Group.IsNilpotent.inf_center_ne_bot_of_normal hPne'
  obtain ⟨w, hw, hw1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hmeet
  obtain ⟨hwP, hwZ⟩ := mem_inf.mp hw
  set C := P ⊓ centralizer (E : Set G) with hC
  have hwC : ((w : P') : G) ∈ C := by
    refine mem_inf.mpr ⟨hwP, mem_centralizer_iff.mpr fun e he => ?_⟩
    have := mem_center_iff.mp hwZ ⟨e, mem_sup_right he⟩
    exact congrArg Subtype.val this
  have hC2 : IsPGroup 2 C := hS2.to_le (inf_le_left.trans hPS)
  have hCnt : Nontrivial C := by
    refine ⟨⟨⟨((w : P') : G), hwC⟩, 1, fun h => hw1 ?_⟩⟩
    have h1 := congrArg Subtype.val h
    exact Subtype.ext h1
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := ↥C)).mp hC2
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    have := Finite.one_lt_card_iff_nontrivial.mpr hCnt
    omega
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) 2 (by
    rw [hn]; exact dvd_pow_self 2 hn0)
  have hz' : orderOf (z : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hz
  have hz2 : (z : G) * (z : G) = 1 := by rw [← pow_two, ← hz', pow_orderOf_eq_one]
  obtain ⟨hzP, hzC⟩ := mem_inf.mp z.2
  refine ⟨z, hzP, hz2, fun h => ?_, fun e he => (mem_centralizer_iff.mp hzC e he).symm⟩
  rw [h, orderOf_one] at hz'
  omega

theorem eq_one_of_commute_of_conjugate_ne {M K T : Subgroup G} (hKM : K ≤ M)
    (hK : IsPComponent 2 (K.subgroupOf M)) (hZ : T ⊓ zStarIn K = ⊥) {f : G} (hfM : f ∈ M)
    (hne : conjugate K f ≠ K) {e : G} (heT : e ∈ T) (heK : e ∈ K) (hef : e * f = f * e) :
    e = 1 := by
  have heKf : e ∈ conjugate K f := by
    rw [UnbalancedLayer.mem_conjugate_iff, ← hef, mul_inv_cancel_right]
    exact heK
  have heC := conjugate_le_coreActionKernel hKM hK hfM hne heKf
  have := mem_inf.mpr ⟨heT, mem_zStarIn_of_mem_coreActionKernel heK heC⟩
  rwa [hZ, mem_bot] at this

theorem isSylowTwoIn_of_le_sup_oddIn {S N M : Subgroup G} (hS : IsSylowTwoIn S N) (hNM : N ≤ M)
    (hMO : M ≤ oddIn M ⊔ N) : IsSylowTwoIn S M := by
  have hSN : S ≤ N := hS.1
  refine GrS4.isSylowTwoIn_of_not_dvd (hSN.trans hNM) (GrS4.isPGroup_of_isSylowTwoIn hS) ?_
  rw [← relIndex_mul_relIndex S N M hSN hNM]
  have h1 := GrS4.not_two_dvd_relIndex_of_isSylowTwoIn hS
  have hO : Odd (Nat.card (oddIn M)) := odd_card_map_pPrimeCore M
  have hMeq : M = N ⊔ oddIn M :=
    le_antisymm (hMO.trans (by rw [sup_comm])) (sup_le hNM (map_subtype_le _))
  have e1 := relIndex_mul_card (H := N) (K := M)
  rw [inf_eq_left.mpr hNM] at e1
  have e2 := GrS4.card_sup_mul_inf_eq_mul_of_normalizes
    (hNM.trans (GrS4.self_le_normalizer_oddIn M))
  rw [← hMeq, ← e1] at e2
  have hNpos : 0 < Nat.card N := Nat.card_pos
  have e3 : N.relIndex M * Nat.card ↥(N ⊓ oddIn M) = Nat.card (oddIn M) := by
    apply Nat.eq_of_mul_eq_mul_left hNpos
    calc Nat.card N * (N.relIndex M * Nat.card ↥(N ⊓ oddIn M))
        = N.relIndex M * Nat.card N * Nat.card ↥(N ⊓ oddIn M) := by ring
      _ = Nat.card N * Nat.card (oddIn M) := e2
  have h2 : ¬ 2 ∣ N.relIndex M := fun h =>
    (Nat.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr (h.trans (Dvd.intro _ e3)))
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h' | h'
  · exact h1 h'
  · exact h2 h'

theorem inf_zStarIn_eq_bot_of_le {J K S T : Subgroup G} (hJK : J ≤ K) (hKJ : K = J ⊔ oddIn K)
    (hSJ : IsSylowTwoIn (S ⊓ J) J) (hST : S ≤ T) (hTK : IsSylowTwoIn (T ⊓ K) K)
    (hZ : S ⊓ zStarIn J = ⊥) : T ⊓ zStarIn K = ⊥ := by
  have hSK : IsSylowTwoIn (S ⊓ J) K := isSylowTwoIn_of_le_sup_oddIn hSJ hJK (by
    conv_lhs => rw [hKJ]
    rw [sup_comm])
  have heq : T ⊓ K = S ⊓ J :=
    hSK.eq_of_le (inf_le_inf hST hJK) inf_le_right (GrS4.isPGroup_of_isSylowTwoIn hTK)
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hzT, hzZ⟩ := mem_inf.mp hz
  have hzK : z ∈ K := (map_subtype_le _ : zStarIn K ≤ K) hzZ
  have hzSJ : z ∈ S ⊓ J := heq ▸ mem_inf.mpr ⟨hzT, hzK⟩
  have := mem_inf.mpr ⟨(mem_inf.mp hzSJ).1,
    GrS4.mem_zStarIn_of_le hJK (mem_inf.mp hzSJ).2 hzZ⟩
  rwa [hZ, mem_bot] at this

end CFSG.ComponentClassification.GrSLit.GrS5S
