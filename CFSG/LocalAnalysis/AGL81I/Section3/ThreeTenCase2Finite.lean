module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenCase234
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenSmallCards
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenA7CertificateFacts
public import CFSG.RankThree.PartTwo.KFacts.KS14MathieuAutCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7_Struct
public import TauCeti.GroupTheory.QuotientGroup.MulAut

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open Equiv
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

theorem natCard_of_threeTenCase2SmallType {X : Type} [Group X] [Finite X]
    (hX : ThreeTenCase2SmallType X) : Nat.card X = 5040 :=
  natCard_of_isExtNotation_alternating_seven_two hX

theorem characteristic_of_normal_card_two_of_iso {X : Type} [Group X] [Finite X]
    {N : Subgroup X} [hN : N.Normal] (hNcard : Nat.card N = 2)
    (e : X ⧸ N ≃* alternatingGroup (Fin 7)) : N.Characteristic := by
  classical
  haveI hA7simple : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
  haveI hsimple : IsSimpleGroup (X ⧸ N) := e.isSimpleGroup
  refine Subgroup.characteristic_iff_map_eq.mpr fun α => ?_
  let M : Subgroup X := N.map α.toMonoidHom
  have hMnormal : M.Normal := hN.map α.toMonoidHom α.surjective
  have hMcard : Nat.card M = 2 := by
    rw [show M = N.map α.toMonoidHom from rfl, Subgroup.card_map_of_injective α.injective,
      hNcard]
  have hM2 : IsPGroup 2 M := IsPGroup.of_card (n := 1) (by rw [hMcard]; norm_num)
  letI : M.Normal := hMnormal
  let Mq : Subgroup (X ⧸ N) := M.map (QuotientGroup.mk' N)
  have hMqnormal : Mq.Normal :=
    hMnormal.map (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  letI : Mq.Normal := hMqnormal
  have hMq2 : IsPGroup 2 Mq := hM2.map (QuotientGroup.mk' N)
  have hMqbot : Mq = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Mq with h | h
    · exact h
    · exfalso
      rw [h] at hMq2
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hMq2
      have hquot : Nat.card (X ⧸ N) = 2520 := by
        rw [Nat.card_congr e.toEquiv, natCard_alternatingGroup_fin_seven]
      have h3 : 3 ∣ 2 ^ k := by
        rw [← hk, Subgroup.card_top, hquot]
        norm_num
      exact absurd (Nat.prime_three.dvd_of_dvd_pow h3) (by norm_num)
  have hle : M ≤ N := by
    intro m hm
    have : QuotientGroup.mk' N m ∈ Mq := Subgroup.mem_map_of_mem _ hm
    rw [hMqbot] at this
    exact (QuotientGroup.eq_one_iff m).mp (Subgroup.mem_bot.mp this)
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hMcard, hNcard])

theorem subsingleton_mulAut_of_card_two {N : Type} [Group N] [Finite N]
    (hNcard : Nat.card N = 2) : Subsingleton (MulAut N) := by
  haveI hNcyc : IsCyclic N := isCyclic_of_prime_card (p := 2) (by rw [hNcard])
  have hAutN : Nat.card (MulAut N) = 1 := by
    rw [IsCyclic.card_mulAut, hNcard]
    norm_num
  obtain ⟨u⟩ := Nat.card_eq_one_iff_unique.mp hAutN
  letI := u
  infer_instance

theorem le_center_of_normal_card_two {X : Type} [Group X] [Finite X] {N : Subgroup X}
    [N.Normal] (hNcard : Nat.card N = 2) : N ≤ Subgroup.center X := by
  haveI : Subsingleton (MulAut N) := subsingleton_mulAut_of_card_two hNcard
  intro n hn
  rw [Subgroup.mem_center_iff]
  intro x
  have hconj : MulAut.conjNormal (H := N) x ⟨n, hn⟩ = ⟨n, hn⟩ := by
    have h : MulAut.conjNormal (H := N) x = 1 := Subsingleton.elim _ _
    rw [h]
    rfl
  have hval : x * n * x⁻¹ = n := by
    have := congrArg Subtype.val hconj
    simpa [MulAut.conjNormal_apply] using this
  calc x * n = (x * n * x⁻¹) * x := by group
    _ = n * x := by rw [hval]

theorem mulAut_eq_one_of_odd_order_of_fixes_normal {X : Type} [Group X] [Finite X]
    {N : Subgroup X} [N.Normal] (hNcard : Nat.card N = 2) {α : MulAut X} {d : ℕ}
    (hαd : orderOf α = d) (hdodd : Odd d)
    (hfixN : ∀ n : N, α n = n)
    (hquot : ∀ x : X, α x * x⁻¹ ∈ N) : α = 1 := by
  have hfixN_pow : ∀ (n : N) (k : ℕ), α ((n : X) ^ k) = (n : X) ^ k := by
    intro n k
    have h := hfixN (n ^ k)
    simpa using h
  ext x
  let n : N := ⟨α x * x⁻¹, hquot x⟩
  have hαx : α x = (n : X) * x := by
    have h : (α x * x⁻¹) * x = α x := by group
    exact h.symm
  have hpow : ∀ k : ℕ, (α ^ k) x = (n : X) ^ k * x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        calc (α ^ (k + 1)) x = α ((α ^ k) x) := by rw [pow_succ']; rfl
          _ = α ((n : X) ^ k * x) := by rw [ih]
          _ = α ((n : X) ^ k) * α x := map_mul α _ _
          _ = (n : X) ^ k * ((n : X) * x) := by rw [hfixN_pow, hαx]
          _ = (n : X) ^ (k + 1) * x := by group
  have hd : α ^ d = 1 := by
    rw [← hαd]
    exact pow_orderOf_eq_one α
  have hxd : x = (n : X) ^ d * x := by
    have h := congrArg (fun f : MulAut X => f x) hd
    simpa [hpow d] using h.symm
  have hnd : (n : X) ^ d = 1 := by
    have h := congrArg (fun y : X => y * x⁻¹) hxd
    simpa [mul_assoc] using h.symm
  have hndN : n ^ d = 1 := by
    apply Subtype.ext
    simpa using hnd
  have hdvd : orderOf n ∣ d := orderOf_dvd_iff_pow_eq_one.mpr hndN
  have h2dvd : orderOf n ∣ 2 := by
    simpa [hNcard] using orderOf_dvd_natCard n
  have hone : orderOf n = 1 :=
    Nat.eq_one_of_dvd_coprimes hdodd.coprime_two_right hdvd h2dvd
  have hn1 : n = 1 := orderOf_eq_one_iff.mp hone
  rw [hαx, hn1]
  simp


theorem dvd_card_of_threeTenCase2SmallType {X : Type} [Group X] [Finite X]
    (hX : ThreeTenCase2SmallType X) {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2) (hd7 : d ≠ 7)
    (hdvd : d ∣ Nat.card (MulAut X)) : d ∣ Nat.card X := by
  classical
  have hXcard : Nat.card X = 5040 := natCard_of_threeTenCase2SmallType hX
  obtain ⟨N, hNnorm, hBN, hAN, hns⟩ := hX
  letI : N.Normal := hNnorm
  obtain ⟨e⟩ := hAN
  have hNcard : Nat.card N = 2 := hBN
  have hNchar : N.Characteristic :=
    characteristic_of_normal_card_two_of_iso hNcard e
  letI : N.Characteristic := hNchar
  have hNcenter : N ≤ Subgroup.center X := le_center_of_normal_card_two hNcard
  haveI : Fact d.Prime := ⟨hd⟩
  have hdodd : Odd d := hd.odd_of_ne_two hd2
  have hAutA7 : Nat.card (MulAut (alternatingGroup (Fin 7))) = 5040 :=
    CFSG.RankThree.PartTwo.KFacts.KS14.card_mulAut_alternatingGroup_seven
  have hdvdA7 : d ∣ Nat.card (MulAut (alternatingGroup (Fin 7))) := by
    by_contra hnot
    obtain ⟨α, hαd⟩ := exists_prime_orderOf_dvd_card' d hdvd
    haveI : Subsingleton (MulAut N) := subsingleton_mulAut_of_card_two hNcard
    have hfixN : ∀ n : N, α n = n := by
      intro n
      let αN : MulAut N :=
        (MulEquiv.subgroupMap α N).trans
          (MulEquiv.subgroupCongr (Subgroup.characteristic_iff_map_eq.mp hNchar α))
      have hαN : αN = 1 := Subsingleton.elim _ _
      have hval : (αN n : N) = n := by
        have h := congrArg (fun f : MulAut N => f n) hαN
        simpa using h
      have hcoe : (αN n : X) = α n := rfl
      have := congrArg Subtype.val hval
      simpa [hcoe] using this
    let αbar : MulAut (X ⧸ N) := MulAut.mapQuotient N α
    have hαbar_dvd_d : orderOf αbar ∣ d := by
      have h := orderOf_map_dvd (MulAut.mapQuotient N) α
      rw [hαd] at h
      exact h
    have hcardAutQuot : Nat.card (MulAut (X ⧸ N)) = 5040 := by
      rw [Nat.card_congr (MulAut.congr e).toEquiv, hAutA7]
    have hαbar_dvd_card : orderOf αbar ∣ 5040 := by
      rw [← hcardAutQuot]
      exact orderOf_dvd_natCard αbar
    have hnot5040 : ¬ d ∣ 5040 := by
      intro hd5040
      exact hnot (by rwa [hAutA7])
    have hcop : Nat.Coprime d 5040 := hd.coprime_iff_not_dvd.mpr hnot5040
    have hone : orderOf αbar = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop hαbar_dvd_d hαbar_dvd_card
    have hαbar1 : αbar = 1 := orderOf_eq_one_iff.mp hone
    have hquot : ∀ x : X, α x * x⁻¹ ∈ N := by
      intro x
      have h := congrArg (fun f : MulAut (X ⧸ N) => f (QuotientGroup.mk x)) hαbar1
      change (MulAut.mapQuotient N α) (QuotientGroup.mk x) =
        (1 : MulAut (X ⧸ N)) (QuotientGroup.mk x) at h
      rw [MulAut.mapQuotient_mk] at h
      have h' : α x / x ∈ N := QuotientGroup.eq_iff_div_mem.mp h
      simpa [div_eq_mul_inv] using h' 
    have hα1 : α = 1 :=
      mulAut_eq_one_of_odd_order_of_fixes_normal hNcard hαd hdodd hfixN hquot
    have hαord : orderOf α = 1 := by rw [hα1]; exact orderOf_one
    exact hd.ne_one (hαd.symm.trans hαord)
  rw [hAutA7] at hdvdA7
  simpa [hXcard] using hdvdA7


open CFSG.RankThree.PartTwo.KFacts.KP2 in
abbrev eNineA : Subgroup (alternatingGroup (Fin 7)) :=
  eNine.subgroupOf (alternatingGroup (Fin 7))

def rFourA : alternatingGroup (Fin 7) :=
  ⟨CFSG.RankThree.PartTwo.KFacts.KP2.rFour,
    Equiv.Perm.mem_alternatingGroup.mpr
      CFSG.RankThree.PartTwo.KFacts.KP2.rFour_spec.1⟩

theorem card_eNineA : Nat.card eNineA = 9 :=
  CFSG.RankThree.PartTwo.KFacts.KS14.card_eNine_subgroupOf

theorem orderOf_rFourA : orderOf rFourA = 4 := by
  have h4 : rFourA ^ 4 = 1 := by
    apply Subtype.ext
    have h := CFSG.RankThree.PartTwo.KFacts.KP2.rFour_spec
    simpa [rFourA] using h.2.2.2.2
  have h2 : rFourA ^ 2 ≠ 1 := by
    intro h
    have h' : (CFSG.RankThree.PartTwo.KFacts.KP2.rFour : Perm (Fin 7)) ^ 2 = 1 := by
      have := congrArg Subtype.val h
      simpa [rFourA] using this
    have ht : CFSG.RankThree.PartTwo.KFacts.KP2.tInv = 1 := by
      rw [← CFSG.RankThree.PartTwo.KFacts.KP2.rFour_spec.2.2.2.1]
      exact h'
    exact (by decide +kernel : CFSG.RankThree.PartTwo.KFacts.KP2.tInv ≠ 1) ht
  have hnot : ¬ rFourA ^ 2 ^ 1 = 1 := by simpa using h2
  have hfin : rFourA ^ 2 ^ (1 + 1) = 1 := by simpa using h4
  exact orderOf_eq_prime_pow hnot hfin

theorem rFourA_mem_normalizer_eNineA :
    rFourA ∈ Subgroup.normalizer (eNineA : Set (alternatingGroup (Fin 7))) := by
  have hnorm : Subgroup.normalizer (eNineA : Set (alternatingGroup (Fin 7))) =
      (Subgroup.normalizer
        (CFSG.RankThree.PartTwo.KFacts.KP2.eNine : Set (Perm (Fin 7)))).subgroupOf
        (alternatingGroup (Fin 7)) := by
    rw [show eNineA =
      CFSG.RankThree.PartTwo.KFacts.KP2.eNine.subgroupOf
        (alternatingGroup (Fin 7)) from rfl,
      ← Subgroup.subgroupOf_normalizer_eq
        CFSG.RankThree.PartTwo.KFacts.KP2.eNine_le_alternatingGroup]
  rw [hnorm]
  exact Subgroup.mem_subgroupOf.mpr
    (by simpa [rFourA] using CFSG.LocalAnalysis.RankThreeTheoremC.rFour_mem_normalizer_eNine)

theorem dvd_card_normalizer_eNineA :
    36 ∣ Nat.card (Subgroup.normalizer (eNineA : Set (alternatingGroup (Fin 7)))) := by
  let R : Subgroup (alternatingGroup (Fin 7)) := Subgroup.zpowers rFourA
  have hRcard : Nat.card R = 4 := by
    rw [show R = Subgroup.zpowers rFourA from rfl, Nat.card_zpowers, orderOf_rFourA]
  have hRnorm : R ≤ Subgroup.normalizer (eNineA : Set (alternatingGroup (Fin 7))) := by
    rw [show R = Subgroup.zpowers rFourA from rfl, Subgroup.zpowers_le]
    exact rFourA_mem_normalizer_eNineA
  have hdisj : Disjoint eNineA R := by
    apply Subgroup.disjoint_of_coprime_natCard
    rw [card_eNineA, hRcard]
    norm_num
  have hEnorm : eNineA ≤ Subgroup.normalizer (eNineA : Set (alternatingGroup (Fin 7))) :=
    Subgroup.le_normalizer
  have hsup_le : eNineA ⊔ R ≤
      Subgroup.normalizer (eNineA : Set (alternatingGroup (Fin 7))) :=
    sup_le hEnorm hRnorm
  have hcard : Nat.card (eNineA ⊔ R : Subgroup (alternatingGroup (Fin 7))) = 36 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer eNineA R hRnorm hdisj,
      card_eNineA, hRcard]
  have := Subgroup.card_dvd_of_le hsup_le
  rwa [hcard] at this


namespace Case2E5

def c5 : Equiv.Perm (Fin 7) := List.formPerm [0, 1, 2, 3, 4]

def r5 : Equiv.Perm (Fin 7) := List.formPerm [0, 1, 3, 2] * Equiv.swap 5 6

theorem c5_sign : Equiv.Perm.sign c5 = 1 := by decide +kernel
theorem r5_sign : Equiv.Perm.sign r5 = 1 := by decide +kernel
theorem c5_pow : c5 ^ 5 = 1 := by decide +kernel
theorem c5_ne_one : c5 ≠ 1 := by decide +kernel
theorem r5_pow : r5 ^ 4 = 1 := by decide +kernel
theorem r5_sq_ne_one : r5 ^ 2 ≠ 1 := by decide +kernel
theorem r5_conj : r5 * c5 * r5⁻¹ = c5 ^ 2 := by decide +kernel

def c5A : alternatingGroup (Fin 7) := ⟨c5, Equiv.Perm.mem_alternatingGroup.mpr c5_sign⟩

def r5A : alternatingGroup (Fin 7) := ⟨r5, Equiv.Perm.mem_alternatingGroup.mpr r5_sign⟩

theorem orderOf_c5 : orderOf c5 = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime c5_pow c5_ne_one

theorem orderOf_c5A : orderOf c5A = 5 := by
  rw [show c5A = (⟨c5, Equiv.Perm.mem_alternatingGroup.mpr c5_sign⟩ :
      alternatingGroup (Fin 7)) from rfl, Subgroup.orderOf_mk, orderOf_c5]

theorem orderOf_r5 : orderOf r5 = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnot : ¬ r5 ^ 2 ^ 1 = 1 := by
    rw [pow_one]
    exact r5_sq_ne_one
  have hfin : r5 ^ 2 ^ (1 + 1) = 1 := by
    rw [show 2 ^ (1 + 1) = 4 by norm_num]
    exact r5_pow
  exact orderOf_eq_prime_pow hnot hfin

theorem orderOf_r5A : orderOf r5A = 4 := by
  rw [show r5A = (⟨r5, Equiv.Perm.mem_alternatingGroup.mpr r5_sign⟩ :
      alternatingGroup (Fin 7)) from rfl, Subgroup.orderOf_mk, orderOf_r5]

theorem r5A_conj : r5A * c5A * r5A⁻¹ = c5A ^ 2 := by
  apply Subtype.ext
  change r5 * c5 * r5⁻¹ = c5 ^ 2
  exact r5_conj

theorem r5A_mem_normalizer_c5A :
    r5A ∈ Subgroup.normalizer (Subgroup.zpowers c5A : Set (alternatingGroup (Fin 7))) := by
  apply Subgroup.mem_normalizer_fintype
  intro x hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← conj_zpow, r5A_conj]
  exact Subgroup.zpow_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers c5A) 2) k

theorem dvd_card_normalizer_zpowers_c5A :
    20 ∣ Nat.card (Subgroup.normalizer
      (Subgroup.zpowers c5A : Set (alternatingGroup (Fin 7)))) := by
  let E : Subgroup (alternatingGroup (Fin 7)) := Subgroup.zpowers c5A
  let R : Subgroup (alternatingGroup (Fin 7)) := Subgroup.zpowers r5A
  have hEcard : Nat.card E = 5 := by
    rw [show E = Subgroup.zpowers c5A from rfl, Nat.card_zpowers, orderOf_c5A]
  have hRcard : Nat.card R = 4 := by
    rw [show R = Subgroup.zpowers r5A from rfl, Nat.card_zpowers, orderOf_r5A]
  have hRnorm : R ≤ Subgroup.normalizer (E : Set (alternatingGroup (Fin 7))) := by
    rw [show R = Subgroup.zpowers r5A from rfl, show E = Subgroup.zpowers c5A from rfl,
      Subgroup.zpowers_le]
    exact r5A_mem_normalizer_c5A
  have hdisj : Disjoint E R := by
    apply Subgroup.disjoint_of_coprime_natCard
    rw [hEcard, hRcard]
    norm_num
  have hEnorm : E ≤ Subgroup.normalizer (E : Set (alternatingGroup (Fin 7))) :=
    Subgroup.le_normalizer
  have hsup_le : E ⊔ R ≤ Subgroup.normalizer (E : Set (alternatingGroup (Fin 7))) :=
    sup_le hEnorm hRnorm
  have hcard : Nat.card (E ⊔ R : Subgroup (alternatingGroup (Fin 7))) = 20 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer E R hRnorm hdisj,
      hEcard, hRcard]
  have := Subgroup.card_dvd_of_le hsup_le
  rwa [hcard] at this

end Case2E5


theorem card_normalizer_eq_two_mul_normalizer_image {X : Type} [Group X] [Finite X]
    {N : Subgroup X} [hN : N.Normal] (hNcard : Nat.card N = 2)
    (hNcenter : N ≤ Subgroup.center X)
    (e : X ⧸ N ≃* alternatingGroup (Fin 7))
    {p : ℕ} [Fact p.Prime] (T : Subgroup X) [Fact (IsPGroup p T)]
    (hcop : Nat.Coprime p (Nat.card N)) :
    Nat.card (Subgroup.normalizer (T : Set X)) =
      2 * Nat.card (Subgroup.normalizer
        (T.map (e.toMonoidHom.comp (QuotientGroup.mk' N)) :
          Set (alternatingGroup (Fin 7)))) := by
  classical
  let π : X →* X ⧸ N := QuotientGroup.mk' N
  have hN_le_cent : N ≤ Subgroup.centralizer (T : Set X) :=
    hNcenter.trans (Subgroup.center_le_centralizer (T : Set X))
  have hN_le_norm : N ≤ Subgroup.normalizer (T : Set X) :=
    hN_le_cent.trans (Subgroup.centralizer_le_normalizer (T : Set X))
  have hnorm_quot : Subgroup.normalizer (T.map π : Set (X ⧸ N)) =
      (Subgroup.normalizer T).map π := by
    simpa [π] using
      CFSG.normalizer_map_quotient_eq_map_normalizer p T N hN hcop
  have hnorm_image : Subgroup.map e (Subgroup.normalizer (T.map π : Set (X ⧸ N))) =
      Subgroup.normalizer (T.map (e.toMonoidHom.comp π) : Set (alternatingGroup (Fin 7))) := by
    rw [Subgroup.map_normalizer_eq_of_bijective (T.map π) e.bijective,
      Subgroup.map_map]
    rfl
  have hmap_comp : Subgroup.map (e.toMonoidHom.comp π) (Subgroup.normalizer T) =
      Subgroup.normalizer (T.map (e.toMonoidHom.comp π) : Set (alternatingGroup (Fin 7))) := by
    rw [← Subgroup.map_map (g := e.toMonoidHom) (f := π), ← hnorm_quot]
    exact hnorm_image
  let φ : Subgroup.normalizer (T : Set X) →* alternatingGroup (Fin 7) :=
    (e.toMonoidHom.comp π).comp (Subgroup.normalizer (T : Set X)).subtype
  have hker : φ.ker = N.subgroupOf (Subgroup.normalizer (T : Set X)) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change e (QuotientGroup.mk' N (x : X)) = 1 ↔ (x : X) ∈ N
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff (x : X)
  have hker_card : Nat.card φ.ker = 2 := by
    rw [hker]
    exact (Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe hN_le_norm).toEquiv).trans hNcard
  have hrange : φ.range = Subgroup.normalizer
      (T.map (e.toMonoidHom.comp π)) := by
    have h := MonoidHom.map_range (g := e.toMonoidHom.comp π)
      (f := (Subgroup.normalizer (T : Set X)).subtype)
    rw [Subgroup.range_subtype] at h
    exact h.symm.trans hmap_comp
  have hcard := Subgroup.card_ker_mul_card_range φ
  rw [hker_card, hrange] at hcard
  exact hcard.symm


theorem card_map_of_injOn {X Y : Type} [Group X] [Group Y] {T : Subgroup X} (f : X →* Y)
    (hinj : ∀ x ∈ T, ∀ y ∈ T, f x = f y → x = y) :
    Nat.card (T.map f) = Nat.card T := by
  classical
  let g : T → T.map f := fun x => ⟨f x, Subgroup.mem_map_of_mem f x.2⟩
  have hg : Function.Bijective g := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      exact hinj x x.2 y y.2 (Subtype.ext_iff.mp hxy)
    · rintro ⟨y, hy⟩
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨x, hx⟩, rfl⟩
  exact Nat.card_congr (Equiv.ofBijective g hg).symm

theorem card_map_quotient_of_coprime {X : Type} [Group X] [Finite X]
    {N T : Subgroup X} [N.Normal] (hcop : Nat.Coprime (Nat.card T) (Nat.card N))
    (e : X ⧸ N ≃* alternatingGroup (Fin 7)) :
    Nat.card (T.map (e.toMonoidHom.comp (QuotientGroup.mk' N))) = Nat.card T := by
  classical
  apply card_map_of_injOn
  intro x hx y hy hxy
  have hπ : QuotientGroup.mk' N x = QuotientGroup.mk' N y := e.injective hxy
  have hmemN : x⁻¹ * y ∈ N := QuotientGroup.eq.mp hπ
  have hmemT : x⁻¹ * y ∈ T := T.mul_mem (T.inv_mem hx) hy
  have hbot : x⁻¹ * y = 1 := by
    have hmem : x⁻¹ * y ∈ T ⊓ N := ⟨hmemT, hmemN⟩
    rw [disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop)] at hmem
    simpa using hmem
  calc x = x * 1 := by group
    _ = x * (x⁻¹ * y) := by rw [hbot]
    _ = y := by group

theorem card_normalizer_sylow_seven {X : Type} [Group X] [Finite X]
    (hX : ThreeTenCase2SmallType X) (P : Subgroup X)
    (hP : CFSG.ABGLocalTools.IsSylowOf 7 P ⊤) :
    Nat.card (Subgroup.normalizer (P : Set X)) = 42 := by
  classical
  have hXcard : Nat.card X = 5040 := natCard_of_threeTenCase2SmallType hX
  obtain ⟨N, hNnorm, hBN, hAN, hns⟩ := hX
  letI : N.Normal := hNnorm
  obtain ⟨e⟩ := hAN
  have hNcard : Nat.card N = 2 := hBN
  have hNcenter : N ≤ Subgroup.center X := le_center_of_normal_card_two hNcard
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  haveI : Fact (IsPGroup 7 P) := ⟨hP.isPGroup⟩
  have hPcard : Nat.card P = 7 := by
    have h := hP.card_eq
    rw [Subgroup.card_top, hXcard] at h
    have hfac : (5040 : ℕ).factorization 7 = 1 :=
      CFSG.QuasithinUnique.L246.C123.factorization_eq_one Nat.prime_seven
        (show 5040 = 7 * 720 by norm_num) (by norm_num) (by norm_num)
    rw [hfac, pow_one] at h
    exact h
  have hcop : Nat.Coprime 7 (Nat.card N) := by
    rw [hNcard]
    norm_num
  have hcopPN : Nat.Coprime (Nat.card P) (Nat.card N) := by
    rw [hPcard, hNcard]
    norm_num
  have hmapcard : Nat.card
      (P.map (e.toMonoidHom.comp (QuotientGroup.mk' N))) = 7 := by
    rw [card_map_quotient_of_coprime hcopPN e, hPcard]
  rw [card_normalizer_eq_two_mul_normalizer_image hNcard hNcenter e P hcop,
    a7_normalizer_card_seven _ hmapcard]


theorem dvd_card_normalizer_of_card_nine (Q : Subgroup (alternatingGroup (Fin 7)))
    (hQ : Nat.card Q = 9) :
    36 ∣ Nat.card (Subgroup.normalizer (Q : Set (alternatingGroup (Fin 7)))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfac3 : (Nat.card (alternatingGroup (Fin 7))).factorization 3 = 2 := by
    rw [CFSG.QuasithinUnique.L246.C123.card_A7,
      show (2520 : ℕ) = 3 ^ 2 * 280 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num),
      Nat.Prime.factorization_pow Nat.prime_three, Finsupp.add_apply,
      Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]
  have hPcard : Nat.card eNineA =
      3 ^ (Nat.card (alternatingGroup (Fin 7))).factorization 3 := by
    rw [hfac3, card_eNineA]
    norm_num
  have hQcard : Nat.card Q =
      3 ^ (Nat.card (alternatingGroup (Fin 7))).factorization 3 := by
    rw [hfac3, hQ]
    norm_num
  obtain ⟨g, hg⟩ := CFSG.QuasithinUnique.L246.C123.exists_conj_of_card_sylow_p
    (p := 3) hPcard hQcard
  have hQeq : Q = CFSG.QuasithinUnique.L246.C123.conjSub g eNineA :=
    Subgroup.ext fun x => by
      rw [CFSG.QuasithinUnique.L246.C123.mem_conjSub]
      exact hg x
  rw [hQeq, CFSG.QuasithinUnique.L246.C123.card_normalizer_conjSub]
  exact dvd_card_normalizer_eNineA

theorem dvd_card_normalizer_of_card_five (Q : Subgroup (alternatingGroup (Fin 7)))
    (hQ : Nat.card Q = 5) :
    20 ∣ Nat.card (Subgroup.normalizer (Q : Set (alternatingGroup (Fin 7)))) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hfac5 : (Nat.card (alternatingGroup (Fin 7))).factorization 5 = 1 := by
    rw [CFSG.QuasithinUnique.L246.C123.card_A7]
    exact CFSG.QuasithinUnique.L246.C123.factorization_eq_one Nat.prime_five
      (show 2520 = 5 * 504 by norm_num) (by norm_num) (by norm_num)
  have hPcard : Nat.card (Subgroup.zpowers Case2E5.c5A) =
      5 ^ (Nat.card (alternatingGroup (Fin 7))).factorization 5 := by
    rw [hfac5, Nat.card_zpowers, Case2E5.orderOf_c5A]
    norm_num
  have hQcard : Nat.card Q =
      5 ^ (Nat.card (alternatingGroup (Fin 7))).factorization 5 := by
    rw [hfac5, hQ]
    norm_num
  obtain ⟨g, hg⟩ := CFSG.QuasithinUnique.L246.C123.exists_conj_of_card_sylow_p
    (p := 5) hPcard hQcard
  have hQeq : Q = CFSG.QuasithinUnique.L246.C123.conjSub g
      (Subgroup.zpowers Case2E5.c5A) :=
    Subgroup.ext fun x => by
      rw [CFSG.QuasithinUnique.L246.C123.mem_conjSub]
      exact hg x
  rw [hQeq, CFSG.QuasithinUnique.L246.C123.card_normalizer_conjSub]
  exact Case2E5.dvd_card_normalizer_zpowers_c5A

theorem dvd_card_normalizer_sylow_three {X : Type} [Group X] [Finite X]
    (hX : ThreeTenCase2SmallType X) (E : Subgroup X)
    (hE : CFSG.ABGLocalTools.IsSylowOf 3 E ⊤) :
    72 ∣ Nat.card (Subgroup.normalizer (E : Set X)) := by
  classical
  have hXcard : Nat.card X = 5040 := natCard_of_threeTenCase2SmallType hX
  obtain ⟨N, hNnorm, hBN, hAN, hns⟩ := hX
  letI : N.Normal := hNnorm
  obtain ⟨e⟩ := hAN
  have hNcard : Nat.card N = 2 := hBN
  have hNcenter : N ≤ Subgroup.center X := le_center_of_normal_card_two hNcard
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (IsPGroup 3 E) := ⟨hE.isPGroup⟩
  have hfac3 : (5040 : ℕ).factorization 3 = 2 := by
    rw [show (5040 : ℕ) = 3 ^ 2 * 560 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num),
      Nat.Prime.factorization_pow Nat.prime_three, Finsupp.add_apply,
      Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]
  have hEcard : Nat.card E = 9 := by
    have h := hE.card_eq
    rw [Subgroup.card_top, hXcard, hfac3] at h
    norm_num at h ⊢
    exact h
  have hcop : Nat.Coprime 3 (Nat.card N) := by
    rw [hNcard]
    norm_num
  have hcopEN : Nat.Coprime (Nat.card E) (Nat.card N) := by
    rw [hEcard, hNcard]
    norm_num
  have hmapcard : Nat.card
      (E.map (e.toMonoidHom.comp (QuotientGroup.mk' N))) = 9 := by
    rw [card_map_quotient_of_coprime hcopEN e, hEcard]
  have hdiv : 36 ∣ Nat.card (Subgroup.normalizer
      (E.map (e.toMonoidHom.comp (QuotientGroup.mk' N)) :
        Set (alternatingGroup (Fin 7)))) :=
    dvd_card_normalizer_of_card_nine _ hmapcard
  rw [card_normalizer_eq_two_mul_normalizer_image hNcard hNcenter e E hcop]
  have := Nat.mul_dvd_mul_left 2 hdiv
  norm_num at this ⊢
  exact this

theorem dvd_card_normalizer_sylow_five {X : Type} [Group X] [Finite X]
    (hX : ThreeTenCase2SmallType X) (E : Subgroup X)
    (hE : CFSG.ABGLocalTools.IsSylowOf 5 E ⊤) :
    40 ∣ Nat.card (Subgroup.normalizer (E : Set X)) := by
  classical
  have hXcard : Nat.card X = 5040 := natCard_of_threeTenCase2SmallType hX
  obtain ⟨N, hNnorm, hBN, hAN, hns⟩ := hX
  letI : N.Normal := hNnorm
  obtain ⟨e⟩ := hAN
  have hNcard : Nat.card N = 2 := hBN
  have hNcenter : N ≤ Subgroup.center X := le_center_of_normal_card_two hNcard
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Fact (IsPGroup 5 E) := ⟨hE.isPGroup⟩
  have hfac5 : (5040 : ℕ).factorization 5 = 1 :=
    CFSG.QuasithinUnique.L246.C123.factorization_eq_one Nat.prime_five
      (show 5040 = 5 * 1008 by norm_num) (by norm_num) (by norm_num)
  have hEcard : Nat.card E = 5 := by
    have h := hE.card_eq
    rw [Subgroup.card_top, hXcard, hfac5, pow_one] at h
    exact h
  have hcop : Nat.Coprime 5 (Nat.card N) := by
    rw [hNcard]
    norm_num
  have hcopEN : Nat.Coprime (Nat.card E) (Nat.card N) := by
    rw [hEcard, hNcard]
    norm_num
  have hmapcard : Nat.card
      (E.map (e.toMonoidHom.comp (QuotientGroup.mk' N))) = 5 := by
    rw [card_map_quotient_of_coprime hcopEN e, hEcard]
  have hdiv : 20 ∣ Nat.card (Subgroup.normalizer
      (E.map (e.toMonoidHom.comp (QuotientGroup.mk' N)) :
        Set (alternatingGroup (Fin 7)))) :=
    dvd_card_normalizer_of_card_five _ hmapcard
  rw [card_normalizer_eq_two_mul_normalizer_image hNcard hNcenter e E hcop]
  have := Nat.mul_dvd_mul_left 2 hdiv
  norm_num at this ⊢
  exact this


theorem false_of_sylow_seven_card_normalizer {W : Type} [Group W] [Finite W]
    (S : Sylow 7 W)
    (hNP : Nat.card (Subgroup.normalizer (S : Set W)) = 42)
    (hWdiv : Nat.card W ∣ 5040) (hWlt : Nat.card W < 5040)
    {L : ℕ} (hL : L ∣ Nat.card W) (hLval : L = 504 ∨ L = 840) : False := by
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hmod := card_sylow_modEq_one 7 W
  have hcount := S.card_eq_index_normalizer
  rw [hcount, Subgroup.index_eq_card_div, hNP] at hmod
  rcases hLval with rfl | rfl
  · obtain ⟨m, hm⟩ := hL
    have hm_dvd : m ∣ 10 := by
      have h5040 : (504 : ℕ) * 10 = 5040 := by norm_num
      have hdiv : 504 * m ∣ 504 * 10 := by
        rw [h5040, ← hm]
        exact hWdiv
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < (504 : ℕ)) hdiv
    have hm_lt : m < 10 := by
      rw [hm] at hWlt
      omega
    have hm_pos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · rw [h0, mul_zero] at hm
        exact (Nat.card_pos.ne' hm).elim
      · exact hpos
    have hmod' : Nat.ModEq 7 (12 * m) 1 := by
      have hdiv : Nat.card W / 42 = 12 * m := by
        rw [hm, show (504 : ℕ) = 42 * 12 by norm_num, Nat.mul_assoc,
          Nat.mul_div_cancel_left _ (by norm_num : 0 < (42 : ℕ))]
      simpa [hdiv] using hmod
    interval_cases m
    · norm_num at hmod'
    · norm_num at hmod'
    · norm_num at hm_dvd
    · norm_num at hm_dvd
    · norm_num at hmod'
    · norm_num at hm_dvd
    · norm_num at hm_dvd
    · norm_num at hm_dvd
    · norm_num at hm_dvd
  · obtain ⟨m, hm⟩ := hL
    have hm_dvd : m ∣ 6 := by
      have h5040 : (840 : ℕ) * 6 = 5040 := by norm_num
      have hdiv : 840 * m ∣ 840 * 6 := by
        rw [h5040, ← hm]
        exact hWdiv
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < (840 : ℕ)) hdiv
    have hm_lt : m < 6 := by
      rw [hm] at hWlt
      omega
    have hm_pos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · rw [h0, mul_zero] at hm
        exact (Nat.card_pos.ne' hm).elim
      · exact hpos
    have hmod' : Nat.ModEq 7 (20 * m) 1 := by
      have hdiv : Nat.card W / 42 = 20 * m := by
        rw [hm, show (840 : ℕ) = 42 * 20 by norm_num, Nat.mul_assoc,
          Nat.mul_div_cancel_left _ (by norm_num : 0 < (42 : ℕ))]
      simpa [hdiv] using hmod
    interval_cases m
    · norm_num at hmod'
    · norm_num at hmod'
    · norm_num at hmod'
    · norm_num at hm_dvd
    · norm_num at hm_dvd


theorem normalizer_sup_eq_top_of_lcm {X : Type} [Group X] [Finite X]
    (hXcard : Nat.card X = 5040) {P E : Subgroup X}
    (hP : CFSG.ABGLocalTools.IsSylowOf 7 P ⊤)
    (hNP : Nat.card (Subgroup.normalizer (P : Set X)) = 42)
    {M : ℕ} (hNE : M ∣ Nat.card (Subgroup.normalizer (E : Set X)))
    {L : ℕ} (hLdef : Nat.lcm 42 M = L) (hLval : L = 504 ∨ L = 840) :
    Subgroup.normalizer (P : Set X) ⊔ Subgroup.normalizer (E : Set X) = ⊤ := by
  classical
  let W : Subgroup X :=
    Subgroup.normalizer (P : Set X) ⊔ Subgroup.normalizer (E : Set X)
  by_contra hWne
  have hPcard : Nat.card P = 7 := by
    have h := hP.card_eq
    rw [Subgroup.card_top, hXcard] at h
    have hfac : (5040 : ℕ).factorization 7 = 1 :=
      CFSG.QuasithinUnique.L246.C123.factorization_eq_one Nat.prime_seven
        (show 5040 = 7 * 720 by norm_num) (by norm_num) (by norm_num)
    rw [hfac, pow_one] at h
    exact h
  have hP_le_W : P ≤ W := Subgroup.le_normalizer.trans le_sup_left
  have hPWcard : Nat.card (P.subgroupOf W) = 7 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP_le_W).toEquiv, hPcard]
  have hPWindex : (P.subgroupOf W).index * Nat.card (P.subgroupOf W) = Nat.card W :=
    Subgroup.index_mul_card _
  have hnotdvd : ¬ 7 ∣ (P.subgroupOf W).index := by
    intro h7
    have h49W : 7 ^ 2 ∣ Nat.card W := by
      rw [← hPWindex, hPWcard]
      have h : 7 * 7 ∣ (P.subgroupOf W).index * 7 :=
        mul_dvd_mul h7 (dvd_refl 7)
      simpa [pow_two] using h
    have hWdiv0 : Nat.card W ∣ 5040 := by
      have := Subgroup.card_subgroup_dvd_card W
      rwa [hXcard] at this
    have h49_5040 : 7 ^ 2 ∣ 5040 := h49W.trans hWdiv0
    norm_num at h49_5040
  let S : Sylow 7 W := hP.isPGroup.comap_subtype.toSylow hnotdvd
  have hScoe : (S : Subgroup W) = P.subgroupOf W :=
    IsPGroup.toSylow_coe hP.isPGroup.comap_subtype hnotdvd
  have hNPW : Nat.card (Subgroup.normalizer (S : Set W)) = 42 := by
    change Nat.card (Subgroup.normalizer ((S : Subgroup W) : Set W)) = 42
    rw [hScoe]
    have hnorm : Subgroup.normalizer ((P.subgroupOf W : Subgroup W) : Set W) =
        (Subgroup.normalizer (P : Set X)).subgroupOf W := by
      rw [← Subgroup.subgroupOf_normalizer_eq hP_le_W]
    rw [hnorm,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (show Subgroup.normalizer (P : Set X) ≤ W from le_sup_left)).toEquiv,
      hNP]
  have h42 : 42 ∣ Nat.card W := by
    have := Subgroup.card_dvd_of_le (H := Subgroup.normalizer (P : Set X)) (K := W) le_sup_left
    rwa [hNP] at this
  have hM : M ∣ Nat.card W := by
    have := Subgroup.card_dvd_of_le (H := Subgroup.normalizer (E : Set X)) (K := W) le_sup_right
    exact hNE.trans this
  have hL : L ∣ Nat.card W := by
    rw [← hLdef]
    exact Nat.lcm_dvd h42 hM
  have hWdiv : Nat.card W ∣ 5040 := by
    have := Subgroup.card_subgroup_dvd_card W
    rwa [hXcard] at this
  have hWlt : Nat.card W < 5040 := by
    have h := Subgroup.card_lt_of_lt (H := W) (K := ⊤)
      (lt_of_le_of_ne le_top hWne)
    simpa [hXcard] using h
  exact false_of_sylow_seven_card_normalizer S hNPW hWdiv hWlt hL hLval

theorem threeTenCase2FiniteInput : ThreeTenCase2FiniteInput := by
  constructor
  · intro X _ _ hX d hd hd2 hd7 hdvd
    exact dvd_card_of_threeTenCase2SmallType hX hd hd2 hd7 hdvd
  · intro X _ _ P E d hX hd hd2 hd7 hP hE
    classical
    have hXcard : Nat.card X = 5040 := natCard_of_threeTenCase2SmallType hX
    by_cases hd3 : d = 3
    · subst d
      exact normalizer_sup_eq_top_of_lcm hXcard hP
        (card_normalizer_sylow_seven hX P hP)
        (dvd_card_normalizer_sylow_three hX E hE)
        (show Nat.lcm 42 72 = 504 by norm_num) (Or.inl rfl)
    by_cases hd5 : d = 5
    · subst d
      exact normalizer_sup_eq_top_of_lcm hXcard hP
        (card_normalizer_sylow_seven hX P hP)
        (dvd_card_normalizer_sylow_five hX E hE)
        (show Nat.lcm 42 40 = 840 by norm_num) (Or.inr rfl)
    ·
      have hdvdX : ¬ d ∣ Nat.card X := by
        rw [hXcard]
        intro h
        have h' : d ∣ 2 ^ 4 * 3 ^ 2 * 5 * 7 := by
          rwa [show 2 ^ 4 * 3 ^ 2 * 5 * 7 = 5040 by norm_num]
        rcases hd.dvd_mul.mp h' with h235 | h7
        · rcases hd.dvd_mul.mp h235 with h23 | h5
          · rcases hd.dvd_mul.mp h23 with h2 | h3
            · have h2' : d ∣ 2 := hd.dvd_of_dvd_pow h2
              exact hd2 ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_two).mp h2')
            · have h3' : d ∣ 3 := hd.dvd_of_dvd_pow h3
              exact hd3 ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_three).mp h3')
          · exact hd5 ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_five).mp h5)
        · exact hd7 ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_seven).mp h7)
      haveI : Fact d.Prime := ⟨hd⟩
      have hEcard : Nat.card E = 1 := by
        have h := hE.card_eq
        rw [Subgroup.card_top, hXcard,
          Nat.factorization_eq_zero_of_not_dvd (by rwa [hXcard] at hdvdX),
          pow_zero] at h
        exact h
      have hEbot : E = ⊥ := Subgroup.eq_bot_of_card_eq E hEcard
      rw [hEbot]
      have htop : Subgroup.normalizer ((⊥ : Subgroup X) : Set X) = ⊤ :=
        Subgroup.normalizer_eq_top (⊥ : Subgroup X)
      rw [htop, sup_top_eq]

end CFSG.LocalAnalysis.AGL81I.Section3
