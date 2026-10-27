module

public import Mathlib.GroupTheory.Nilpotent
public import CFSG.FeitThompson.Local.ElementaryAbelianCubeInvariantPlane
import CFSG.FeitThompson.Foundations.SolvableSubgroupSolvable
import CFSG.FeitThompson.OddOrder.SemidirectReassociation
import CFSG.FeitThompson.OddOrder.PConfigAlignDerivedComplement
import CFSG.FeitThompson.OddOrder.FrobeniusKernelContainsRoots
import CFSG.FeitThompson.OddOrder.FrobeniusKernelContainsCentralizers
import CFSG.FeitThompson.OddOrder.SharedSylowNormalizedByIntersection
import CFSG.FeitThompson.OddOrder.WielandtComplementFixedPoints
import CFSG.FeitThompson.OddOrder.FullExponentFreeRegularElement
import CFSG.FeitThompson.Local.PrimeFreeFactorizationFixedSubgroupTransport

open Subgroup Pointwise

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {G : Type*} [Group G]

theorem inf_subgroupOf_eq (X Y L : Subgroup G) :
    (X ⊓ Y).subgroupOf L = X.subgroupOf L ⊓ Y.subgroupOf L := comap_inf _ _ _

theorem centralizer_singleton_subgroupOf {L : Subgroup G} (y : ↥L) :
    centralizer ({y} : Set ↥L) = (centralizer ({(y : G)} : Set G)).subgroupOf L := by
  ext c
  rw [mem_centralizer_singleton_iff, mem_subgroupOf, mem_centralizer_singleton_iff]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem inf_centralizer_singleton_subgroupOf_eq_bot_iff {X L : Subgroup G} (hXL : X ≤ L)
    (y : ↥L) :
    X.subgroupOf L ⊓ centralizer ({y} : Set ↥L) = ⊥ ↔
      X ⊓ centralizer ({(y : G)} : Set G) = ⊥ := by
  rw [centralizer_singleton_subgroupOf, ← inf_subgroupOf_eq, subgroupOf_eq_bot, disjoint_iff,
    inf_eq_left.mpr (le_trans inf_le_left hXL)]

theorem le_of_subgroupOf_le {X Y L : Subgroup G} (hXL : X ≤ L)
    (h : X.subgroupOf L ≤ Y.subgroupOf L) : X ≤ Y := by
  have h' : X ⊓ L ≤ Y ⊓ L := by
    simpa [subgroupOf_map_subtype] using Subgroup.map_mono (f := L.subtype) h
  exact le_trans (le_trans (le_inf le_rfl hXL) h') inf_le_left

theorem forall_mem_subgroupOf_conjOnNormalized_apply_eq_self_iff {J K X : Subgroup G}
    (hJK : J ≤ normalizer (K : Set G)) (hXJ : X ≤ J) (v : ↥K) :
    (∀ b ∈ X.subgroupOf J, conjOnNormalized K hJK b v = v) ↔
      (v : G) ∈ centralizer (X : Set G) := by
  have key : ∀ b : ↥J, conjOnNormalized K hJK b v = v ↔ (b : G) * (v : G) = (v : G) * (b : G) := by
    intro b
    rw [← Subtype.coe_inj, conjOnNormalized_apply_coe, mul_inv_eq_iff_eq_mul]
  refine ⟨fun hb => mem_centralizer_iff.mpr fun u hu => ?_, fun hv b hb => ?_⟩
  · have h := (key ⟨u, hXJ hu⟩).1 (hb ⟨u, hXJ hu⟩ hu)
    simpa using h
  · have h := mem_centralizer_iff.1 hv (b : G) hb
    simpa using (key b).2 (by simpa using h)

variable {L H E : Subgroup G}

theorem inf_centralizer_singleton_eq_bot_of_mem_of_notMem [Finite H] [(H.subgroupOf L).Normal]
    (hmul : (H : Set G) * (E : Set G) = (L : Set G)) (hdisj : H ⊓ E = ⊥)
    (hCH : ∀ e ∈ E, e ≠ 1 → H ⊓ centralizer ({e} : Set G) = ⊥)
    {y : G} (hyL : y ∈ L) (hyH : y ∉ H) : H ⊓ centralizer ({y} : Set G) = ⊥ := by
  have hHL : H ≤ L := left_le_of_coe_mul_coe_eq hmul
  have : Finite (H.subgroupOf L) := Finite.of_equiv _ (subgroupOfEquivOfLe hHL).symm.toEquiv
  have h := inf_centralizer_singleton_eq_bot_of_notMem
    (isComplement'_subgroupOf_of_coe_mul_coe_eq hmul hdisj)
    (fun e he he1 => inf_centralizer_singleton_subgroupOf_eq_bot hCH he he1)
    (y := (⟨y, hyL⟩ : ↥L)) (by simpa [mem_subgroupOf] using hyH)
  exact (inf_centralizer_singleton_subgroupOf_eq_bot_iff hHL _).1 h

theorem inf_centralizer_singleton_le_of_mem_of_ne_one [Finite H] [(H.subgroupOf L).Normal]
    (hmul : (H : Set G) * (E : Set G) = (L : Set G)) (hdisj : H ⊓ E = ⊥)
    (hCH : ∀ e ∈ E, e ≠ 1 → H ⊓ centralizer ({e} : Set G) = ⊥)
    {h : G} (hh : h ∈ H) (hh1 : h ≠ 1) : L ⊓ centralizer ({h} : Set G) ≤ H := by
  have hHL : H ≤ L := left_le_of_coe_mul_coe_eq hmul
  have : Finite (H.subgroupOf L) := Finite.of_equiv _ (subgroupOfEquivOfLe hHL).symm.toEquiv
  have hh' : (⟨h, hHL hh⟩ : ↥L) ≠ 1 := fun he => hh1 (by simpa using Subtype.ext_iff.1 he)
  have key := centralizer_singleton_le_of_mem_of_ne_one
    (isComplement'_subgroupOf_of_coe_mul_coe_eq hmul hdisj)
    (fun e he he1 => inf_centralizer_singleton_subgroupOf_eq_bot hCH he he1)
    (h := (⟨h, hHL hh⟩ : ↥L)) hh hh'
  intro y hy
  exact key (mem_centralizer_singleton_iff.mpr
    (Subtype.ext (mem_centralizer_singleton_iff.1 hy.2)) : (⟨y, hy.1⟩ : ↥L) ∈ _)

variable [Finite G] {M K D D0 D1 P : Subgroup G} {p : ℕ}

theorem le_of_inf_centralizer_ne_bot_of_mem_sylow [Group.IsSolvable ↥M]
    [(K.subgroupOf M).Normal] [(H.subgroupOf L).Normal] (hDdef : D = M ⊓ L)
    (hKM : K ≤ M) (hK : K ≠ ⊥) (hKHall : (Nat.card K).Coprime (K.relIndex M))
    (hMKD : (K : Set G) * (D : Set G) = (M : Set G)) (hKD : K ⊓ D = ⊥)
    (hHL : H ≤ L) (hHnil : Group.IsNilpotent ↥H)
    (hHHall : (Nat.card H).Coprime (H.relIndex L))
    (hLHE : (H : Set G) * (E : Set G) = (L : Set G)) (hHE : H ⊓ E = ⊥)
    (hCH : ∀ e ∈ E, e ≠ 1 → H ⊓ centralizer ({e} : Set G) = ⊥)
    (hD0D : D0 ≤ D) (hexp : Monoid.exponent ↥D0 = Monoid.exponent ↥D)
    (hCD0 : ∀ d ∈ D0, d ≠ 1 → K ⊓ centralizer ({d} : Set G) = ⊥)
    (hD1 : IsMulCommutative ↥D1)
    (hCD1 : ∀ k ∈ K, k ≠ 1 → D ⊓ centralizer ({k} : Set G) ≤ D1)
    (hp : p.Prime) (hpK : ¬ p ∣ Nat.card K) (hPM : P ≤ M)
    (hPcard : Nat.card P = p ^ (Nat.card M).factorization p) (hPbot : P ≠ ⊥) (hPH : P ≤ H)
    {x : G} (hxP : x ∈ P) (hx1 : x ≠ 1) (hCKx : K ⊓ centralizer ({x} : Set G) ≠ ⊥) :
    D ≤ H := by
  have : Fact p.Prime := ⟨hp⟩
  subst hDdef
  have hDM : M ⊓ L ≤ M := inf_le_left
  have hDL : M ⊓ L ≤ L := inf_le_right
  have hcompM : (K.subgroupOf M).IsComplement' ((M ⊓ L).subgroupOf M) :=
    isComplement'_subgroupOf_of_coe_mul_coe_eq hMKD hKD
  have hindex : K.relIndex M = Nat.card (M ⊓ L : Subgroup G) := by
    rw [Subgroup.relIndex, hcompM.symm.index_eq_card,
      Nat.card_congr (subgroupOfEquivOfLe hDM).toEquiv]
  have hcopKD : (Nat.card K).Coprime (Nat.card (M ⊓ L : Subgroup G)) := by rwa [hindex] at hKHall
  by_contra hDH
  have hHallPi : IsHallPiSubgroup ((Nat.card H).primeFactors : Set ℕ) (H.subgroupOf L) :=
    (isHallSubgroup_subgroupOf_primeFactors hHL hHHall).isHallPiSubgroup
  have hnotPi : ¬ IsPiSubgroup ((Nat.card H).primeFactors : Set ℕ) ((M ⊓ L).subgroupOf L) :=
    fun hpi => hDH (le_of_subgroupOf_le hDL (hHallPi.le_of_isPiSubgroup hpi))
  rw [isPiSubgroup_iff, Nat.card_congr (subgroupOfEquivOfLe hDL).toEquiv] at hnotPi
  push Not at hnotPi
  obtain ⟨q, hqD, hqH⟩ := hnotPi
  have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hqD
  have : Fact q.Prime := ⟨hqprime⟩
  have hqdvdD : q ∣ Nat.card (M ⊓ L : Subgroup G) := (Nat.mem_primeFactors.1 hqD).2.1
  have hqnotH : ¬ q ∣ Nat.card H := fun hdvd =>
    hqH (Nat.mem_primeFactors.2 ⟨hqprime, hdvd, Nat.card_pos.ne'⟩)
  obtain ⟨z', hz'⟩ := exists_prime_orderOf_dvd_card' (G := ↥(M ⊓ L : Subgroup G)) q hqdvdD
  set z : G := (z' : G) with hz
  have hzD : z ∈ M ⊓ L := z'.2
  have hzord : orderOf z = q := by rw [hz, Subgroup.orderOf_coe]; exact hz'
  have hZD : zpowers z ≤ M ⊓ L := zpowers_le.2 hzD
  have hZcard : Nat.card (zpowers z) = q := by rw [Nat.card_zpowers, hzord]
  have hZnotH : ∀ a ∈ zpowers z, a ≠ 1 → a ∉ H := by
    intro a ha ha1 haH
    have h1 : orderOf a ∣ q := by
      rw [← hZcard]; exact Subgroup.orderOf_dvd_natCard _ ha
    have h2 : orderOf a = q :=
      (Nat.Prime.eq_one_or_self_of_dvd hqprime _ h1).resolve_left
        (fun h => ha1 (orderOf_eq_one_iff.1 h))
    exact hqnotH (h2 ▸ Subgroup.orderOf_dvd_natCard _ haH)
  have hCHZ : ∀ a ∈ zpowers z, a ≠ 1 → H ⊓ centralizer ({a} : Set G) = ⊥ := fun a ha ha1 =>
    inf_centralizer_singleton_eq_bot_of_mem_of_notMem hLHE hHE hCH (hDL (hZD ha))
      (hZnotH a ha ha1)
  have hCPZ : ∀ a ∈ zpowers z, a ≠ 1 → P ⊓ centralizer ({a} : Set G) = ⊥ := fun a ha ha1 =>
    le_bot_iff.1 ((inf_le_inf_right _ hPH).trans_eq (hCHZ a ha ha1))
  obtain ⟨Q, ⟨hQH, hQcard⟩, -⟩ := existsUnique_le_natCard_eq_pow_factorization (p := p) hHnil
  have hDnorm : M ⊓ L ≤ normalizer (P : Set G) :=
    inf_le_normalizer_of_le_nilpotent hHnil hHL ‹(H.subgroupOf L).Normal› hPM hPcard hPH hQH hQcard
  have hZnorm : zpowers z ≤ normalizer (P : Set G) := le_trans hZD hDnorm
  have hPZdisj : Disjoint P (zpowers z) := by
    rw [disjoint_iff, eq_bot_iff]
    intro a ha
    by_contra hne
    exact hZnotH a ha.2 (fun h => hne (Subgroup.mem_bot.2 h)) (hPH ha.1)
  have hPJ : P ≤ P ⊔ zpowers z := le_sup_left
  have hZJ : zpowers z ≤ P ⊔ zpowers z := le_sup_right
  have hPD : P ≤ M ⊓ L := le_inf hPM (le_trans hPH hHL)
  have hJD : P ⊔ zpowers z ≤ M ⊓ L := sup_le hPD hZD
  have hJM : P ⊔ zpowers z ≤ M := le_trans hJD hDM
  have hPJnormal : (P.subgroupOf (P ⊔ zpowers z)).Normal := normal_subgroupOf_sup hZnorm
  have hPJcomp : (P.subgroupOf (P ⊔ zpowers z)).IsComplement'
      ((zpowers z).subgroupOf (P ⊔ zpowers z)) :=
    isComplement'_subgroupOf_sup hZnorm hPZdisj
  have hJK : P ⊔ zpowers z ≤ normalizer (K : Set G) :=
    le_trans hJM (Subgroup.le_normalizer_of_normal_subgroupOf hKM)
  have hcop : (Nat.card ↥(P ⊔ zpowers z)).Coprime (Nat.card ↥K) :=
    Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le hJD) hcopKD.symm
  have : Group.IsSolvable ↥(P ⊔ zpowers z) := isSolvable_of_le hJM
  have : Group.IsSolvable ↥K := isSolvable_of_le hKM
  obtain ⟨S, hS⟩ := (natCard_eq_pow_factorization_iff_exists_sylow (p := p) hPM).1 hPcard
  have hSbot : (S : Subgroup ↥M) ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.map_bot] at hS
    exact hPbot hS.symm
  have hD0M : D0 ≤ M := le_trans hD0D hDM
  have hexpM : Monoid.exponent ↥(D0.subgroupOf M) = Monoid.exponent ↥((M ⊓ L).subgroupOf M) := by
    rw [Monoid.exponent_eq_of_mulEquiv (subgroupOfEquivOfLe hD0M),
      Monoid.exponent_eq_of_mulEquiv (subgroupOfEquivOfLe hDM)]
    exact hexp
  have hCD0M : ∀ d ∈ D0.subgroupOf M, d ≠ 1 →
      K.subgroupOf M ⊓ centralizer ({d} : Set ↥M) = ⊥ := fun d hd hd1 =>
    (inf_centralizer_singleton_subgroupOf_eq_bot_iff hKM d).2
      (hCD0 _ (mem_subgroupOf.1 hd) (fun h => hd1 (Subtype.ext h)))
  have hpKM : ¬ p ∣ Nat.card ↥(K.subgroupOf M) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hKM).toEquiv]
  obtain ⟨a, haS, -, hCKa⟩ := exists_mem_sylow_orderOf_eq_and_inf_centralizer_eq_bot
    (K := K.subgroupOf M) (D := (M ⊓ L).subgroupOf M) (D0 := D0.subgroupOf M) hcompM hexpM
    hCD0M hp hpKM S hSbot
  have haP : (a : G) ∈ P := by rw [← hS]; exact ⟨a, haS, rfl⟩
  have hCKa : K ⊓ centralizer ({(a : G)} : Set G) = ⊥ :=
    (inf_centralizer_singleton_subgroupOf_eq_bot_iff hKM a).1 hCKa
  have hnontriv : ∃ v : ↥K, ¬ ∀ b ∈ P.subgroupOf (P ⊔ zpowers z),
      conjOnNormalized K hJK b v = v := by
    obtain ⟨w, hw, hw1⟩ := (Subgroup.nontrivial_iff_exists_ne_one _).1
      ((Subgroup.nontrivial_iff_ne_bot _).2 hK)
    refine ⟨⟨w, hw⟩, fun hfix => hw1 ?_⟩
    have hcent : w ∈ centralizer (P : Set G) :=
      (forall_mem_subgroupOf_conjOnNormalized_apply_eq_self_iff hJK hPJ ⟨w, hw⟩).1 hfix
    have hmem : w ∈ K ⊓ centralizer ({(a : G)} : Set G) :=
      ⟨hw, mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.1 hcent _ haP).symm⟩
    rwa [hCKa, Subgroup.mem_bot] at hmem
  obtain ⟨v, hv1, hv⟩ := exists_ne_one_fixed_of_exists_not_fixed
    (U := P.subgroupOf (P ⊔ zpowers z)) (W := (zpowers z).subgroupOf (P ⊔ zpowers z))
    (conjOnNormalized K hJK) hcop hPJnormal hPJcomp
    (fun w hw hw1 => (inf_centralizer_singleton_subgroupOf_eq_bot_iff hPJ w).2
      (hCPZ (w : G) hw (fun h => hw1 (Subtype.ext h)))) hnontriv
  have hkK : (v : G) ∈ K := v.2
  have hk1 : (v : G) ≠ 1 := fun h => hv1 (Subtype.ext h)
  have hZcent : (v : G) ∈ centralizer ((zpowers z : Subgroup G) : Set G) :=
    (forall_mem_subgroupOf_conjOnNormalized_apply_eq_self_iff hJK hZJ v).1 hv
  have hZD1 : zpowers z ≤ D1 := fun u hu =>
    hCD1 _ hkK hk1 ⟨hZD hu, mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.1 hZcent u hu)⟩
  obtain ⟨t, ht, ht1⟩ := (Subgroup.nontrivial_iff_exists_ne_one _).1
    ((Subgroup.nontrivial_iff_ne_bot _).2 hCKx)
  have hxD1 : x ∈ D1 :=
    hCD1 t ht.1 ht1 ⟨hPD hxP, mem_centralizer_singleton_iff.mpr
      (mem_centralizer_singleton_iff.1 ht.2).symm⟩
  have hzx : z * x = x * z := by
    have h := hD1.is_comm.comm (⟨z, hZD1 (mem_zpowers z)⟩ : ↥D1) ⟨x, hxD1⟩
    simpa using congrArg Subtype.val h
  have hzH : z ∈ H :=
    inf_centralizer_singleton_le_of_mem_of_ne_one hLHE hHE hCH (hPH hxP) hx1
      ⟨hDL hzD, mem_centralizer_singleton_iff.mpr hzx⟩
  exact hZnotH z (mem_zpowers z)
    (fun h => hqprime.one_lt.ne' (by rw [← hzord, h, orderOf_one])) hzH

end

end CFSG.FeitThompson
