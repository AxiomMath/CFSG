module

public import CFSG.FeitThompson.Local.MetacyclicOddGroupUniqueTorsionPlane
import CFSG.FeitThompson.Local.CyclicIndexPGroupTorsionPlane
import CFSG.FeitThompson.Local.TorsionTwoDimensionalBoundQuotient
import CFSG.FeitThompson.Local.NormalSubgroupCentralPrimeTorsion
import CFSG.FeitThompson.Local.FixedLineCharacteristicChainPrimeFactors
import CFSG.FeitThompson.Local.PGroupCyclicAbelianizationCyclic
import CFSG.FeitThompson.Foundations.QuotientOrderByNormal

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup
open scoped commutatorElement

variable {p : ℕ} {R : Type*} [Group R]

theorem isCyclic_of_forall_natCard_eq_prime_eq [Finite R] (hp : p.Prime) (hodd : Odd p)
    (hR : IsPGroup p R)
    (huniq : ∀ H K : Subgroup R, Nat.card H = p → Nat.card K = p → H = K) : IsCyclic R := by
  have := Fact.mk hp
  by_contra hnc
  obtain ⟨E, hEcard, hEexp⟩ := exists_natCard_eq_prime_sq_forall_pow_eq_one hp hodd hR hnc
  have hEfin : Finite ↥E :=
    Nat.finite_of_card_ne_zero (by rw [hEcard]; exact pow_ne_zero _ hp.ne_zero)
  have hEnt : Nontrivial ↥E := by
    refine Finite.one_lt_card_iff_nontrivial.mp ?_
    rw [hEcard]
    calc 1 < p := hp.one_lt
      _ ≤ p ^ 2 := Nat.le_self_pow (by norm_num) p
  obtain ⟨y, hy⟩ := exists_ne (1 : ↥E)
  have hyR : (y : R) ≠ 1 := fun h => hy (Subtype.ext h)
  have hyord : orderOf (y : R) = p := orderOf_eq_prime (hEexp _ y.2) hyR
  have hEle : E ≤ zpowers (y : R) := by
    intro z hz
    rcases eq_or_ne z 1 with rfl | hz1
    · exact one_mem _
    · have hzord : orderOf z = p := orderOf_eq_prime (hEexp z hz) hz1
      have h : zpowers z = zpowers (y : R) :=
        huniq _ _ (by rw [Nat.card_zpowers, hzord]) (by rw [Nat.card_zpowers, hyord])
      exact h ▸ mem_zpowers z
  have hdvd := Subgroup.card_dvd_of_le hEle
  rw [hEcard, Nat.card_zpowers, hyord] at hdvd
  have := Nat.le_of_dvd hp.pos hdvd
  nlinarith [hp.two_le]

theorem exists_maximal_isCyclic [Finite R] {D : Subgroup R} (hD : IsCyclic D) :
    ∃ S : Subgroup R, D ≤ S ∧ IsCyclic S ∧ ∀ C : Subgroup R, S ≤ C → IsCyclic C → C = S := by
  have hne : {n : ℕ | ∃ C : Subgroup R, D ≤ C ∧ IsCyclic C ∧ Nat.card C = n}.Nonempty :=
    ⟨Nat.card D, D, le_rfl, hD, rfl⟩
  have hbdd : BddAbove {n : ℕ | ∃ C : Subgroup R, D ≤ C ∧ IsCyclic C ∧ Nat.card C = n} := by
    refine ⟨Nat.card R, ?_⟩
    rintro n ⟨C, -, -, rfl⟩
    exact Subgroup.card_le_card_group C
  obtain ⟨S, hDS, hScyc, hScard⟩ := Nat.sSup_mem hne hbdd
  refine ⟨S, hDS, hScyc, fun C hSC hCcyc => ?_⟩
  have h1 : Nat.card C ≤ sSup {n : ℕ | ∃ C : Subgroup R, D ≤ C ∧ IsCyclic C ∧ Nat.card C = n} :=
    le_csSup hbdd ⟨C, hDS.trans hSC, hCcyc, rfl⟩
  exact (Subgroup.eq_of_le_of_card_ge hSC (by rw [hScard]; exact h1)).symm

def commutatorRightHom (J : Subgroup R) [J.Normal] [IsMulCommutative ↥J] (b : R) : ↥J →* ↥J where
  toFun x := ⟨⁅(x : R), b⁆, Subgroup.commutator_le_left J ⊤
    (Subgroup.commutator_mem_commutator x.2 (mem_top b))⟩
  map_one' := by ext; simp [commutatorElement_def]
  map_mul' x y := by
    have hcomm : ∀ u v : R, u ∈ J → v ∈ J → u * v = v * u := fun u v hu hv =>
      congrArg Subtype.val (‹IsMulCommutative ↥J›.is_comm.comm (⟨u, hu⟩ : ↥J) ⟨v, hv⟩)
    have hX' : b * (x : R)⁻¹ * b⁻¹ ∈ J := ‹J.Normal›.conj_mem _ (J.inv_mem x.2) b
    have hY' : b * (y : R)⁻¹ * b⁻¹ ∈ J := ‹J.Normal›.conj_mem _ (J.inv_mem y.2) b
    ext
    push_cast
    simp only [commutatorElement_def]
    calc (x : R) * y * b * ((x : R) * y)⁻¹ * b⁻¹
        = (x : R) * ((y : R) * (b * (y : R)⁻¹ * b⁻¹) * (b * (x : R)⁻¹ * b⁻¹)) := by group
      _ = (x : R) * ((b * (x : R)⁻¹ * b⁻¹) * ((y : R) * (b * (y : R)⁻¹ * b⁻¹))) := by
          rw [hcomm _ _ (J.mul_mem y.2 hY') hX']
      _ = (x : R) * b * (x : R)⁻¹ * b⁻¹ * ((y : R) * b * (y : R)⁻¹ * b⁻¹) := by group

@[simp]
theorem commutatorRightHom_coe (J : Subgroup R) [J.Normal] [IsMulCommutative ↥J] (b : R)
    (x : ↥J) : ((commutatorRightHom J b x : ↥J) : R) = ⁅(x : R), b⁆ := (rfl)

theorem isMulCommutative_closurePair {a z : R} (hz : z ∈ center R) :
    IsMulCommutative ↥(closure ({a, z} : Set R)) := by
  refine isMulCommutative_closure ?_
  rintro x (rfl | rfl) y (rfl | rfl) -
  · rfl
  · exact (hz.comm x).symm
  · exact hz.comm y
  · rfl

theorem commutatorElement_mem_zpowers_of_closurePair {J : Subgroup R} [J.Normal]
    [IsMulCommutative ↥J] {a z : R} (b : R) (hJ : J = closure {a, z}) (hz : z ∈ center R) :
    ∀ x ∈ J, ⁅x, b⁆ ∈ zpowers ⁅a, b⁆ := by
  have haJ : a ∈ J := hJ ▸ subset_closure (by simp)
  have hzJ : z ∈ J := hJ ▸ subset_closure (by simp)
  set g : ↥J →* R := J.subtype.comp (commutatorRightHom J b) with hg
  have hgapp : ∀ x : ↥J, g x = ⁅(x : R), b⁆ := fun _ => rfl
  set H := (zpowers ⁅a, b⁆).comap g with hH
  have haH : (⟨a, haJ⟩ : ↥J) ∈ H := by
    simp only [hH, mem_comap, hgapp]; exact mem_zpowers _
  have hzH : (⟨z, hzJ⟩ : ↥J) ∈ H := by
    simp only [hH, mem_comap, hgapp]
    rw [commutatorElement_eq_one_iff_commute.2 (hz.comm b)]; exact one_mem _
  have htop : (⊤ : Subgroup ↥J) = closure {(⟨a, haJ⟩ : ↥J), ⟨z, hzJ⟩} := by
    apply Subgroup.map_injective J.subtype_injective
    rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, range_subtype,
      show (J.subtype '' {(⟨a, haJ⟩ : ↥J), ⟨z, hzJ⟩}) = ({a, z} : Set R) by simp [Set.image_pair]]
    exact hJ
  intro x hx
  have hmem : (⟨x, hx⟩ : ↥J) ∈ H := by
    have hle : closure {(⟨a, haJ⟩ : ↥J), ⟨z, hzJ⟩} ≤ H := by
      rw [closure_le]; rintro y (rfl | rfl) <;> assumption
    exact hle (htop ▸ mem_top _)
  simpa [hH, hgapp] using hmem

theorem mem_normalizer_of_forall_conj_mem {C : Subgroup R} [Finite C] {g : R}
    (h : ∀ x ∈ C, g * x * g⁻¹ ∈ C) : g ∈ normalizer (C : Set R) := by
  have hmap : C.map (MulAut.conj g).toMonoidHom ≤ C := by
    rintro _ ⟨x, hx, rfl⟩; exact h x hx
  have hcard : Nat.card ↥(C.map (MulAut.conj g).toMonoidHom) = Nat.card ↥C :=
    Nat.card_congr (C.equivMapOfInjective _ (MulAut.conj g).injective).symm.toEquiv
  have heq : C.map (MulAut.conj g).toMonoidHom = C := Subgroup.eq_of_le_of_card_ge hmap hcard.ge
  rw [mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h x hx, fun hx => ?_⟩
  obtain ⟨y, hy, hxy⟩ : g * x * g⁻¹ ∈ C.map (MulAut.conj g).toMonoidHom := by rw [heq]; exact hx
  have hyx : y = x := by
    refine mul_left_cancel (a := g) ?_
    have h2 := congrArg (fun t => t * g) (show g * y * g⁻¹ = g * x * g⁻¹ from hxy)
    simp only [mul_assoc, inv_mul_cancel, mul_one] at h2
    exact h2
  rw [← hyx]; exact hy

theorem normal_of_forall_conj_mem_of_closure_eq_top {C : Subgroup R} [Finite C] {s : Set R}
    (hs : closure s = ⊤) (h : ∀ g ∈ s, ∀ x ∈ C, g * x * g⁻¹ ∈ C) : C.Normal := by
  rw [← normalizer_eq_top_iff, eq_top_iff, ← hs, closure_le]
  exact fun g hg => mem_normalizer_of_forall_conj_mem (h g hg)

theorem conj_mem_zpowers_of_conj_mem {g c : R} (h : g * c * g⁻¹ ∈ zpowers c) :
    ∀ x ∈ zpowers c, g * x * g⁻¹ ∈ zpowers c := fun x hx =>
  (zpowers_le.2 h) ((MonoidHom.map_zpowers (MulAut.conj g).toMonoidHom c) ▸ ⟨x, hx, rfl⟩)

theorem forall_mul_comm_of_closure_eq_top {s : Set R} (hs : closure s = ⊤)
    (h : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x) : ∀ x y : R, x * y = y * x := by
  have hc := isMulCommutative_closure fun x hx y hy _ => h x hx y hy
  intro x y
  exact congrArg Subtype.val
    (hc.is_comm.comm (⟨x, hs ▸ mem_top x⟩ : ↥(closure s)) ⟨y, hs ▸ mem_top y⟩)

theorem commutator_le_of_forall_mul_comm_quotient (N : Subgroup R) [N.Normal]
    (h : ∀ x y : R ⧸ N, x * y = y * x) : commutator R ≤ N := by
  rw [commutator_def, Subgroup.commutator_le]
  intro x _ y _
  have hq : (QuotientGroup.mk' N) ⁅x, y⁆ = 1 := by
    rw [map_commutatorElement]; simp [commutatorElement_def, h]
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hq
  exact hq

theorem commutator_eq_zpowers_commutatorElement [Finite R] {J : Subgroup R} [J.Normal]
    [IsMulCommutative ↥J] {a z b : R} (hJ : J = closure {a, z}) (hz : z ∈ center R)
    (hb : zpowers b ⊔ J = ⊤) : commutator R = zpowers ⁅a, b⁆ := by
  set c := ⁅a, b⁆ with hcdef
  have hkey := commutatorElement_mem_zpowers_of_closurePair (J := J) b hJ hz
  have haJ : a ∈ J := hJ ▸ subset_closure (by simp)
  have hcJ : c ∈ J := Subgroup.commutator_le_left J ⊤
    (Subgroup.commutator_mem_commutator haJ (mem_top b))
  have hJcomm : ∀ u v : R, u ∈ J → v ∈ J → u * v = v * u := fun u v hu hv =>
    congrArg Subtype.val (‹IsMulCommutative ↥J›.is_comm.comm (⟨u, hu⟩ : ↥J) ⟨v, hv⟩)
  have hsclos : closure (({b} : Set R) ∪ (J : Set R)) = ⊤ := by
    rw [Subgroup.closure_union, ← zpowers_eq_closure, closure_eq, hb]
  have hnormal : (zpowers c).Normal := by
    refine normal_of_forall_conj_mem_of_closure_eq_top hsclos ?_
    rintro g (rfl | hgJ) x hx
    · refine conj_mem_zpowers_of_conj_mem ?_ x hx
      have h1 : g * c * g⁻¹ = c * ⁅c⁻¹, g⁆ := by simp only [commutatorElement_def]; group
      rw [h1]; exact mul_mem (mem_zpowers c) (hkey _ (J.inv_mem hcJ))
    · obtain ⟨m, rfl⟩ := hx
      have heq : g * c ^ m * g⁻¹ = c ^ m := by
        rw [hJcomm _ _ hgJ (zpow_mem hcJ m)]; group
      rw [heq]; exact ⟨m, rfl⟩
  have := hnormal
  refine le_antisymm (commutator_le_of_forall_mul_comm_quotient _ ?_) (by
    rw [zpowers_le]; exact Subgroup.commutator_mem_commutator (mem_top a) (mem_top b))
  set π := QuotientGroup.mk' (zpowers c) with hπ
  refine forall_mul_comm_of_closure_eq_top (s := π '' (({b} : Set R) ∪ (J : Set R))) ?_ ?_
  · rw [← MonoidHom.map_closure, hsclos,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    have hcomm : ⁅u, v⁆ ∈ zpowers c := by
      rcases hu with (rfl | huJ) <;> rcases hv with (rfl | hvJ)
      · simp
      · rw [← commutatorElement_inv]; exact (zpowers c).inv_mem (hkey v hvJ)
      · exact hkey u huJ
      · rw [commutatorElement_eq_one_iff_commute.2 ((commute_iff_eq u v).2 (hJcomm _ _ huJ hvJ))]
        exact one_mem _
    have hπc : π ⁅u, v⁆ = 1 := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact hcomm
    rw [map_commutatorElement] at hπc
    exact (commutatorElement_eq_one_iff_commute.1 hπc).eq

theorem exists_closurePair_of_isMetacyclic_quotient {T : Subgroup R} [T.Normal] {z : R}
    (hT : T = zpowers z) (hmc : IsMetacyclic (R ⧸ T)) :
    ∃ a b : R, (closure ({a, z} : Set R)).Normal ∧
      zpowers b ⊔ closure ({a, z} : Set R) = ⊤ := by
  obtain ⟨S, hSn, hS, hQ⟩ := isMetacyclic_iff.1 hmc
  have := hSn
  set π := QuotientGroup.mk' T with hπ
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective T
  have hker : π.ker = T := QuotientGroup.ker_mk' T
  set J := S.comap π with hJ
  have hTJ : T ≤ J := hker ▸ MonoidHom.ker_le_comap π S
  have := hS
  obtain ⟨w, hw⟩ := IsCyclic.exists_generator (α := ↥S)
  obtain ⟨a, ha⟩ := hsurj (w : R ⧸ T)
  have haJ : a ∈ J := by rw [hJ, mem_comap, ha]; exact w.2
  have hzJ : z ∈ J := hTJ (hT ▸ mem_zpowers z)
  have hJeq : closure ({a, z} : Set R) = J := by
    refine le_antisymm ?_ ?_
    · rw [closure_le]; rintro x (rfl | rfl); exacts [haJ, hzJ]
    · intro x hx
      obtain ⟨m, hm'⟩ := hw ⟨π x, (hx : π x ∈ S)⟩
      have hm2 : (w : R ⧸ T) ^ m = π x := congrArg Subtype.val hm'
      have hmem : (a ^ m)⁻¹ * x ∈ T := by
        rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, map_zpow, ha, ← hm2]; group
      rw [show x = a ^ m * ((a ^ m)⁻¹ * x) by group]
      refine mul_mem (zpow_mem (subset_closure (by simp)) m) ?_
      rw [hT] at hmem
      obtain ⟨k, hk⟩ := hmem
      rw [← hk]; exact zpow_mem (subset_closure (by simp)) k
  have := hQ
  obtain ⟨q, hq⟩ := exists_zpowers_sup_eq_top_of_isCyclic_quotient (N := S)
  obtain ⟨b, rfl⟩ := hsurj q
  refine ⟨a, b, hJeq ▸ (hJ ▸ (‹S.Normal›.comap π)), ?_⟩
  rw [hJeq]
  have hmapb : (zpowers b ⊔ J).map π = ⊤ := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, hJ,
      Subgroup.map_comap_eq_self_of_surjective hsurj, hq]
  have hkle : π.ker ≤ zpowers b ⊔ J := by rw [hker]; exact hTJ.trans le_sup_right
  have hcm : comap π ((zpowers b ⊔ J).map π) = zpowers b ⊔ J := Subgroup.comap_map_eq_self hkle
  rw [hmapb, comap_top] at hcm
  exact hcm.symm

theorem not_le_of_isCyclic_of_natCard_eq_prime_sq (hp : p.Prime) {E S : Subgroup R}
    (hE : Nat.card E = p ^ 2) (hEexp : ∀ x ∈ E, x ^ p = 1) (hS : IsCyclic S) : ¬ E ≤ S := by
  intro hES
  exact not_isCyclic_of_natCard_eq_prime_sq_of_pow_eq_one hp hE hEexp hES hS

theorem isMetacyclic_of_isCyclic_commutator_of_natCard_omega1_le_sq [Finite R] (hp : p.Prime)
    (hp3 : 3 < p) (hR : IsPGroup p R) (hΩ : Nat.card (omega1 p R) ≤ p ^ 2)
    (hcomm : IsCyclic (commutator R)) : IsMetacyclic R := by
  have := Fact.mk hp
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  obtain ⟨S, hRS, hScyc, hSmax⟩ := exists_maximal_isCyclic (R := R) hcomm
  have hSnormal : S.Normal := Subgroup.Normal.of_commutator_le R hRS
  have := hSnormal
  have := hScyc
  refine isMetacyclic_of_normal S hScyc ?_
  refine isCyclic_of_forall_natCard_eq_prime_eq hp hodd (hR.to_quotient S) ?_
  have key : ∀ K : Subgroup (R ⧸ S), Nat.card K = p → K.comap (QuotientGroup.mk' S)
      = S ⊔ omega1 p R := by
    intro K hKcard
    set H := K.comap (QuotientGroup.mk' S) with hH
    have hSH : S ≤ H := fun x hx => Subgroup.mem_comap.mpr (by
      change (x : R ⧸ S) ∈ K
      rw [(QuotientGroup.eq_one_iff x).mpr hx]
      exact K.one_mem)
    have hidx : (S.subgroupOf H).index = p := index_subgroupOf_comap_mk' S K hKcard
    have hSHne : S ≠ H := by
      intro h
      have h1 : (S.subgroupOf H).index = 1 := by
        rw [Subgroup.index_eq_one]
        refine le_antisymm le_top fun x _ => Subgroup.mem_subgroupOf.mpr ?_
        rw [h]; exact x.2
      rw [hidx] at h1
      exact hp.one_lt.ne' h1
    have hHnc : ¬ IsCyclic ↥H := fun hc => hSHne (hSmax H hSH hc).symm
    have hAcyc : IsCyclic ↥(S.subgroupOf H) :=
      isCyclic_of_injective (Subgroup.subgroupOfEquivOfLe hSH).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hSH).injective
    have := hAcyc
    have hΩH : Nat.card (omega1 p ↥H) = p ^ 2 :=
      natCard_omega1_of_isCyclic_of_index_eq_prime (S.subgroupOf H) hp hodd (hR.to_subgroup H)
        hHnc hidx
    have hΩHcoe : (omega1 p ↥H : Set ↥H) = {x : ↥H | x ^ p = 1} :=
      coe_omega1_of_isCyclic_of_index_eq_prime (S.subgroupOf H) hp hodd (hR.to_subgroup H)
        hHnc hidx
    set E : Subgroup R := (omega1 p ↥H).map H.subtype with hE
    have hEcard : Nat.card ↥E = p ^ 2 := by
      rw [hE, ← Nat.card_congr
        ((omega1 p ↥H).equivMapOfInjective H.subtype H.subtype_injective).toEquiv, hΩH]
    have hEexp : ∀ x ∈ E, x ^ p = 1 := by
      rintro x ⟨y, hy, rfl⟩
      have : y ^ p = 1 := (Set.ext_iff.1 hΩHcoe y).1 hy
      simpa using congrArg H.subtype this
    have hEle : E ≤ omega1 p R := fun x hx => mem_omega1_of_pow_eq_one (hEexp x hx)
    have hΩfin : Finite ↥(omega1 p R) := Subtype.finite
    have hEeq : E = omega1 p R :=
      Subgroup.eq_of_le_of_card_ge hEle (by rw [hEcard] at *; omega)
    have hΩle : omega1 p R ≤ H := by
      rw [← hEeq, hE]
      exact Subgroup.map_subtype_le _
    have hΩcard : Nat.card ↥(omega1 p R) = p ^ 2 := hEeq ▸ hEcard
    have hΩexp : ∀ x ∈ omega1 p R, x ^ p = 1 := hEeq ▸ hEexp
    have hnotle : ¬ omega1 p R ≤ S :=
      not_le_of_isCyclic_of_natCard_eq_prime_sq hp hΩcard hΩexp hScyc
    have hsupH : S ⊔ omega1 p R ≤ H := sup_le hSH hΩle
    refine le_antisymm ?_ hsupH
    set A := S.subgroupOf H with hA
    set B := (S ⊔ omega1 p R).subgroupOf H with hB
    have hAB : A ≤ B := Subgroup.comap_mono le_sup_left
    have hABne : A ≠ B := by
      intro heq
      refine hnotle fun x hx => ?_
      have hxH : x ∈ H := hΩle hx
      have hmem : (⟨x, hxH⟩ : ↥H) ∈ B := Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right hx)
      rw [← heq] at hmem
      exact Subgroup.mem_subgroupOf.mp hmem
    have h1 : A.relIndex B * B.index = p := by rw [Subgroup.relIndex_mul_index hAB, hidx]
    have hBtop : B = ⊤ := by
      rcases (Nat.dvd_prime hp).mp (Dvd.intro_left _ h1) with h | h
      · exact Subgroup.index_eq_one.mp h
      · rw [h] at h1
        have hone : A.relIndex B = 1 := by
          nlinarith [Nat.pos_of_ne_zero
            (show A.relIndex B ≠ 0 by intro h0; simp [h0] at h1; omega), hp.pos]
        exact absurd (le_antisymm hAB (Subgroup.relIndex_eq_one.mp hone)) hABne
    intro x hxH
    have hmem : (⟨x, hxH⟩ : ↥H) ∈ B := hBtop ▸ mem_top _
    exact Subgroup.mem_subgroupOf.mp hmem
  intro K₁ K₂ h₁ h₂
  exact Subgroup.comap_injective (QuotientGroup.mk'_surjective S)
    ((key K₁ h₁).trans (key K₂ h₂).symm)

private theorem isCyclic_commutator_aux (hp : p.Prime) (hp3 : 3 < p) (n : ℕ) :
    ∀ {R : Type u} [Group R] [Finite R], Nat.card R < n → IsPGroup p R →
      Nat.card (omega1 p R) ≤ p ^ 2 → IsCyclic (commutator R) := by
  induction n with
  | zero => intro R _ _ hcard; exact absurd hcard (Nat.not_lt_zero _)
  | succ n ih =>
    intro R _ _ hcard hR hΩ
    have := Fact.mk hp
    by_cases habel : ∀ x y : R, x * y = y * x
    · rw [(commutator_eq_bot_iff R).mpr ⟨⟨habel⟩⟩]; infer_instance
    have hRnt : commutator R ≠ ⊥ := fun h => habel (fun x y =>
      ((commutator_eq_bot_iff R).1 h).is_comm.comm x y)
    obtain ⟨a', ha'⟩ := hR.exists_card_eq
    obtain ⟨T, hTle, hTcard⟩ := exists_le_inf_center_natCard_eq (commutator R) hp ha' hRnt
    obtain ⟨z, -, hz⟩ := exists_zpowers_eq_of_natCard_eq_prime hp hTcard
    have hTcen : T ≤ center R := hTle.trans inf_le_right
    have hzc : z ∈ center R := hTcen (by rw [← hz]; exact mem_zpowers z)
    have hTnormal : T.Normal := normal_of_le_center hTcen
    have := hTnormal
    have hTbot : T ≠ ⊥ := by
      intro h; rw [h, Subgroup.card_bot] at hTcard; exact hp.one_lt.ne hTcard
    have hlt : Nat.card (R ⧸ T) < n := by
      have h1 := natCard_quotient_lt_natCard_of_bot_lt (N := T) (bot_lt_iff_ne_bot.2 hTbot)
      omega
    have hΩq : Nat.card (omega1 p (R ⧸ T)) ≤ p ^ 2 := natCard_omega1_quotient_le_sq hp hp3 hR hΩ T
    have hmq : IsMetacyclic (R ⧸ T) :=
      isMetacyclic_of_isCyclic_commutator_of_natCard_omega1_le_sq hp hp3 (hR.to_quotient T) hΩq
        (ih hlt (hR.to_quotient T) hΩq)
    obtain ⟨a, b, hJn, hb⟩ := exists_closurePair_of_isMetacyclic_quotient hz.symm hmq
    have := hJn
    have := isMulCommutative_closurePair (a := a) hzc
    rw [commutator_eq_zpowers_commutatorElement rfl hzc hb]
    infer_instance

theorem isCyclic_commutator_of_natCard_omega1_le_sq [Finite R] (hp : p.Prime) (hp3 : 3 < p)
    (hR : IsPGroup p R) (hΩ : Nat.card (omega1 p R) ≤ p ^ 2) : IsCyclic (commutator R) :=
  isCyclic_commutator_aux hp hp3 (Nat.card R + 1) (Nat.lt_succ_self _) hR hΩ

theorem isMetacyclic_of_natCard_omega1_le_sq [Finite R] (hp : p.Prime) (hp3 : 3 < p)
    (hR : IsPGroup p R) (hΩ : Nat.card (omega1 p R) ≤ p ^ 2) : IsMetacyclic R :=
  isMetacyclic_of_isCyclic_commutator_of_natCard_omega1_le_sq hp hp3 hR hΩ
    (isCyclic_commutator_of_natCard_omega1_le_sq hp hp3 hR hΩ)

theorem isMetacyclic_of_natCard_omega1_le_sq_of_card_eq_pow {a : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hR : Nat.card R = p ^ a) (hΩ : Nat.card (omega1 p R) ≤ p ^ 2) : IsMetacyclic R :=
  have : Finite R := Nat.finite_of_card_ne_zero (by rw [hR]; exact pow_ne_zero _ hp.pos.ne')
  isMetacyclic_of_natCard_omega1_le_sq hp hp3 (IsPGroup.of_card hR) hΩ

end

end CFSG.FeitThompson
