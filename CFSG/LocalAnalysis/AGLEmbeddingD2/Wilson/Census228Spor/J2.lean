module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census228Spor.CoverA6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census228Spor.M12
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census424Rest.J2
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census228Spor

open Subgroup CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2
open CFSG.Blueprint
open CFSG.AGLEmbeddingD2.Wilson.Census424Rest

theorem threeFiveData228_of_equiv_J2
    {X : Type} [Group X] [Finite X] (e : X ≃* CFSG.Blueprint.NativeSporadic.J2) :
    ThreeFiveData228 X := by
  intro x k hx hk hxk
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    omega
  have hzx : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨P, hxP⟩ := hzx.exists_le_sylow
  have hxmem : x ∈ (P : Subgroup (X)) := hxP (Subgroup.mem_zpowers x)
  have hkC : k ∈ centralizer ({x} : Set (X)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hxk.symm
  obtain ⟨-, -, -, h4, -⟩ := Sporadic.rank3II_4_15 (X) ⟨e⟩ P _ rfl _ rfl
  by_cases hxZ : x ∈ (P : Subgroup (X)) ⊓
      centralizer (((P : Subgroup (X)) : Set _))
  ·
    have hcentral : IsCentral218 (⊤ : Subgroup (X)) x := by
      refine ⟨(P : Subgroup (X)), ?_, ?_⟩
      · have hcard : Nat.card ((P : Subgroup (X)).subgroupOf ⊤) =
            3 ^ (Nat.card ↥(⊤ : Subgroup (X))).factorization 3 := by
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_top).toEquiv,
            Sylow.card_eq_multiplicity,
            Nat.card_congr (Subgroup.topEquiv (G := X)).toEquiv]
        refine ⟨Sylow.ofCard _ hcard, ?_⟩
        change ((P : Subgroup (X)).subgroupOf ⊤).map
          (⊤ : Subgroup (X)).subtype = (P : Subgroup _)
        exact Subgroup.map_subgroupOf_eq_of_le le_top
      · refine ⟨⟨x, (Subgroup.mem_inf.mp hxZ).1⟩, ?_, rfl⟩
        rw [SetLike.mem_coe, Subgroup.mem_center_iff]
        intro t
        exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hxZ).2) t t.2)
    obtain ⟨φ⟩ := nonempty_centralizer_equiv_of_isCentral218 e hx1 hcentral
    let Φ0 : centralizer ({x} : Set (X)) →* Equiv.Perm (Fin 6) :=
      act6.comp φ.toMonoidHom
    have hmem : ∀ c, Φ0 c ∈ alternatingGroup (Fin 6) := fun c => by
      rw [← range_act6]
      exact ⟨φ c, rfl⟩
    let Φ : centralizer ({x} : Set (X)) →* alternatingGroup (Fin 6) :=
      Φ0.codRestrict _ hmem
    have hkerΦ : ∀ c, Φ c = 1 → φ c ∈ act6.ker := by
      intro c hc
      have : Φ0 c = 1 := congrArg Subtype.val hc
      exact this
    have hker : Nat.card Φ.ker ≤ 3 := by
      rw [← card_ker_act6]
      refine Nat.card_le_card_of_injective
        (fun c : Φ.ker => (⟨φ c.1, hkerΦ c.1 c.2⟩ : act6.ker)) ?_
      intro a b h
      have : φ a.1 = φ b.1 :=
        congrArg (fun z : act6.ker => (z.1 : centralizer ({zJ} : Set GJ))) h
      exact Subtype.ext (φ.injective this)
    have hΦk : orderOf (Φ ⟨k, hkC⟩) = 5 := by
      have h5 : (5 : ℕ).Prime := by norm_num
      have hk5 : k ^ 5 = 1 := by rw [← hk]; exact pow_orderOf_eq_one k
      have hdvd : orderOf (Φ ⟨k, hkC⟩) ∣ 5 := by
        refine orderOf_dvd_of_pow_eq_one ?_
        rw [← map_pow]
        have : (⟨k, hkC⟩ : centralizer ({x} : Set X)) ^ 5 = 1 :=
          Subtype.ext (by simpa using hk5)
        rw [this, map_one]
      rcases (Nat.dvd_prime h5).mp hdvd with h1 | h1
      · exfalso
        have hone : Φ ⟨k, hkC⟩ = 1 := orderOf_eq_one_iff.mp h1
        have hker0 := hkerΦ _ hone
        have h3 : orderOf (φ ⟨k, hkC⟩) ∣ Nat.card act6.ker :=
          Subgroup.orderOf_dvd_natCard _ hker0
        rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hk, card_ker_act6] at h3
        omega
      · exact h1
    have h30 := card_inf_normalizer_le_thirty Φ hker hkC hΦk
    have hC : Nat.card (centralizer ({x} : Set (X))) = 1080 := by
      rw [Nat.card_congr φ.toEquiv]
      exact card_centralizer_z
    rw [hC]
    omega
  ·
    exfalso
    obtain ⟨hZ3, -, -⟩ := Sec14.j2_sylow_facts (Sporadic.rank3II_4_15) ⟨e⟩ P
    set Z := (P : Subgroup (X)) ⊓
      centralizer (((P : Subgroup (X)) : Set _)) with hZdef
    obtain ⟨zz, hzz⟩ := exists_prime_orderOf_dvd_card' (G := ↥Z) 3 (by rw [hZ3])
    set z : X := (zz : X) with hzdef
    have hzo : orderOf z = 3 := by rw [hzdef, Subgroup.orderOf_coe]; exact hzz
    have hzZ : z ∈ Z := zz.2
    have hz1 : z ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hzo
      omega
    have hz3 : z ^ 3 = 1 := by rw [← hzo]; exact pow_orderOf_eq_one z
    have hzP : z ∈ (P : Subgroup (X)) := (Subgroup.mem_inf.mp hzZ).1
    have hzcomm : ∀ t ∈ (P : Subgroup (X)), t * z = z * t := fun t ht =>
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hzZ).2) t ht
    have hbot : CFSG.Assembly.IsElemAbelian 3 (⊥ : Subgroup (X)) :=
      ⟨⟨⟨fun a b => by
          rw [show a = 1 from Subtype.ext (Subgroup.mem_bot.mp a.2),
            show b = 1 from Subtype.ext (Subgroup.mem_bot.mp b.2)]⟩⟩, fun a ha => by
          rw [Subgroup.mem_bot.mp ha, one_pow]⟩
    obtain ⟨hA1, hA1c⟩ := Sec5.isElemAbelian_sup_zpowers hbot
      (show z ∉ (⊥ : Subgroup (X)) from fun h => hz1 (Subgroup.mem_bot.mp h))
      hz3 (fun a ha => by rw [Subgroup.mem_bot.mp ha, one_mul, mul_one])
    rw [bot_sup_eq] at hA1 hA1c
    have hxnot : x ∉ Subgroup.zpowers z := by
      intro h
      apply hxZ
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h
      rw [← hn]
      exact Subgroup.zpow_mem _ hzZ n
    obtain ⟨hA2, hA2c⟩ := Sec5.isElemAbelian_sup_zpowers hA1 hxnot hx3 (fun a ha => by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      exact (Commute.zpow_left (show Commute z x from (hzcomm x hxmem).symm) n).eq)
    have hA9 : Nat.card (Subgroup.zpowers z ⊔ Subgroup.zpowers x :
        Subgroup (X)) = 9 := by
      rw [hA2c, hA1c, Subgroup.card_bot]
    have hAP : (Subgroup.zpowers z ⊔ Subgroup.zpowers x : Subgroup (X)) ≤
        (P : Subgroup (X)) :=
      sup_le ((Subgroup.zpowers_le).mpr hzP) ((Subgroup.zpowers_le).mpr hxmem)
    obtain ⟨-, ⟨eN⟩, -⟩ := h4 _ ⟨hAP, hA9⟩ x (Subgroup.mem_sup_right (Subgroup.mem_zpowers x)) hxZ
    have h5 : 5 ∣ Nat.card (normalizer ((Subgroup.zpowers x : Subgroup X) : Set X)) := by
      have := orderOf_dvd_natCard (⟨k, centralizer_le_normalizer_zpowers x hkC⟩ :
        normalizer ((Subgroup.zpowers x : Subgroup X) : Set X))
      rwa [Subgroup.orderOf_mk, hk] at this
    exact not_five_dvd_card_of_equiv eN h5

theorem threeFiveData228_J2 :
    ThreeFiveData228 (NativeSporadic.Carrier .J2) := by
  have : Finite (NativeSporadic.Carrier .J2) := CFSG.Sporadic.J2.fam_j2_simplicity.1
  exact threeFiveData228_of_equiv_J2 (MulEquiv.refl _)

end CFSG.AGLEmbeddingD2.Wilson.Census228Spor
