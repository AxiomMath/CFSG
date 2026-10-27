module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521Defs
import CFSG.Adapters.LinearCatalogStated
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.Adapters.StatedClassicalUnitaryOrders
import CFSG.LieType.Simplicity.Classical
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair
open KFactsSmall

theorem small1522_simple_center_aux1 {S : Type} [Group S] [IsSimpleGroup S]
    (hS : ¬ (Nat.card S).Prime) : Subgroup.center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · exact h
  · exfalso
    haveI : IsMulCommutative S := Subgroup.center_eq_top_iff.mp h
    exact hS (Group.is_simple_iff_prime_card.mp ‹IsSimpleGroup S›)

theorem small1522_simple_center_aux2 {q : TauCeti.PrimePower} {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hq : q.card = ℓ) : q.p = ℓ ∧ q.exponent = 1 := by
  have hpow : q.p ^ q.exponent = ℓ := by
    rw [← TauCeti.PrimePower.card_def]
    exact hq
  exact hℓ.pow_eq_iff.mp hpow

theorem small1522_simple_center_aux3 {S : Type} [Group S] (h : IsLThreeTwo S) :
    IsSimpleGroup S ∧ Nat.card S = 168 := by
  obtain ⟨⟨i, hv⟩, ⟨q, hq, hd⟩, ⟨e⟩⟩ := h
  have hd' : i = .A 1 q := hd
  subst hd'
  obtain ⟨hp, hn⟩ := small1522_simple_center_aux2 (by norm_num) hq
  have hmod := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
  rw [hp, hn] at hmod
  exact ⟨(CFSG.LieType.Simplicity.fam_PSL_simplicity S _ _ _ hmod).2,
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_seven hmod⟩

theorem small1522_simple_center_aux4 {S : Type} [Group S] (h : IsL5Two S) :
    IsSimpleGroup S ∧ Nat.card S = 9999360 := by
  obtain ⟨⟨i, hv⟩, ⟨q, hq, hd⟩, ⟨e⟩⟩ := h
  have hd' : i = .A 4 q := hd
  subst hd'
  obtain ⟨hp, hn⟩ := small1522_simple_center_aux2 Nat.prime_two hq
  have hmod := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
  rw [hp, hn] at hmod
  exact ⟨(CFSG.LieType.Simplicity.fam_PSL_simplicity S _ _ _ hmod).2,
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_five_two hmod⟩

theorem small1522_simple_center_aux5 {S : Type} [Group S] (h : IsUThreeThree S) :
    IsSimpleGroup S ∧ Nat.card S = 6048 := by
  obtain ⟨⟨i, hv⟩, ⟨q, hq, hd⟩, ⟨e⟩⟩ := h
  have hd' : i = .twistedA 2 q := hd
  subst hd'
  obtain ⟨hp, hn⟩ := small1522_simple_center_aux2 Nat.prime_three hq
  have hmod := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
  rw [hp, hn] at hmod
  exact ⟨(CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity S _ _ _ hmod).2,
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_three hmod⟩

theorem small1522_simple_center {S : Type} [Group S] (h : Small1522 S) :
    IsSimpleGroup S ∧ Subgroup.center S = ⊥ := by
  rcases h with h | h | h | h | h
  · obtain ⟨hs, hc⟩ := small1522_simple_center_aux3 (isLThreeTwo_iff_isLThreeOfExp_one.2 h)
    haveI := hs
    exact ⟨hs, small1522_simple_center_aux1 (by rw [hc]; norm_num)⟩
  · obtain ⟨e⟩ := h
    haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    exact ⟨MulEquiv.isSimpleGroup e, center_eq_bot_of_alt (by norm_num) e⟩
  · obtain ⟨e⟩ := h
    haveI : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
    exact ⟨MulEquiv.isSimpleGroup e, center_eq_bot_of_alt (by norm_num) e⟩
  · obtain ⟨hs, hc⟩ := small1522_simple_center_aux4 (isL5Two_iff_isLinTwo_five.2 h)
    haveI := hs
    exact ⟨hs, small1522_simple_center_aux1 (by rw [hc]; norm_num)⟩
  · obtain ⟨hs, hc⟩ := small1522_simple_center_aux5 h
    haveI := hs
    exact ⟨hs, small1522_simple_center_aux1 (by rw [hc]; norm_num)⟩

theorem primes_of_isLThreeOfExp_one {S : Type} [Group S] [Finite S] (h : IsLThreeOfExp 1 S)
    {p : ℕ} (hp : p.Prime) (hpS : p ∣ Nat.card S) : p = 2 ∨ p = 3 ∨ p = 7 := by
  rw [(small1522_simple_center_aux3 (isLThreeTwo_iff_isLThreeOfExp_one.2 h)).2] at hpS
  have h2 : (168 : ℕ) = 2 ^ 3 * 3 * 7 := by norm_num
  rw [h2] at hpS
  rcases (Nat.Prime.dvd_mul hp).1 hpS with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · left
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
    · right; left
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h
  · right; right
    exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h

theorem false_of_isAltSixCoverThree_le_aux1 {Y : Type} [Group Y] {Ls Js : Subgroup Y}
    (hsub : CFSG.Open.IsSubnormal Ls ⊤) (hle : Ls ≤ Js) {P : Type} [Group P] [IsSimpleGroup P]
    (hP : Subgroup.center P = ⊥) (ρ : ↥Js →* P) (hρ : Function.Surjective ρ)
    {z : ↥Ls} (hz : z ∈ Subgroup.center ↥Ls) : ρ (Subgroup.inclusion hle z) = 1 := by
  have hJ : CFSG.Open.IsSubnormal Ls Js := by
    have h := hsub.inf_of_le (le_top : Js ≤ ⊤)
    rwa [inf_eq_left.2 hle] at h
  have hK : CFSG.Open.IsSubnormal (Ls.subgroupOf Js) ⊤ :=
    CFSG.Open.IsSubnormal.of_mathlib hJ.subgroupOf
  have hKρ := hK.map ρ
  rw [Subgroup.map_top_of_surjective ρ hρ] at hKρ
  have hzK : Subgroup.inclusion hle z ∈ Ls.subgroupOf Js := by
    rw [Subgroup.mem_subgroupOf]
    exact z.2
  rcases CFSG.Open.IsSubnormal.eq_bot_or_top hKρ with h | h
  · have hmem : ρ (Subgroup.inclusion hle z) ∈ (Ls.subgroupOf Js).map ρ := ⟨_, hzK, rfl⟩
    rw [h] at hmem
    exact Subgroup.mem_bot.1 hmem
  · have hc : ρ (Subgroup.inclusion hle z) ∈ Subgroup.center P := by
      rw [Subgroup.mem_center_iff]
      intro y
      have hy : y ∈ (Ls.subgroupOf Js).map ρ := by
        rw [h]
        exact Subgroup.mem_top y
      obtain ⟨k, hk, rfl⟩ := hy
      rw [← map_mul, ← map_mul]
      congr 1
      have hk' : (k : Y) ∈ Ls := hk
      have hcomm := Subgroup.mem_center_iff.1 hz ⟨k, hk'⟩
      apply Subtype.ext
      simpa using congrArg Subtype.val hcomm
    rw [hP] at hc
    exact Subgroup.mem_bot.1 hc

theorem false_of_isAltSixCoverThree_le {Y : Type} [Group Y] [Finite Y] {Ls Js : Subgroup Y}
    (hLs : IsComponentOf Ls ⊤) (hle : Ls ≤ Js) (h3 : IsAltSixCoverThree ↥Ls)
    (hJ : Small1522 ↥Js ∨ IsLThreeTwoSq ↥Js ∨ IsLThreeTwoCube ↥Js) : False := by
  obtain ⟨-, hsub, -⟩ := hLs
  obtain ⟨-, hcard, -⟩ := h3
  have hne : Subgroup.center ↥Ls ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    omega
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hinc : Subgroup.inclusion hle z ≠ 1 := fun h =>
    hz1' ((Subgroup.inclusion_injective hle) (by rw [map_one]; exact h))
  rcases hJ with hJ | hJ | hJ
  · obtain ⟨hs, hc⟩ := small1522_simple_center hJ
    haveI := hs
    exact hinc (false_of_isAltSixCoverThree_le_aux1 hsub hle hc (MonoidHom.id _)
      Function.surjective_id hz)
  · obtain ⟨P, _, hP, ⟨φ⟩⟩ := hJ
    obtain ⟨hs, hc⟩ := small1522_simple_center (Or.inl hP)
    haveI := hs
    have h1 := false_of_isAltSixCoverThree_le_aux1 hsub hle hc
      ((MonoidHom.fst P P).comp φ.toMonoidHom) (Prod.fst_surjective.comp φ.surjective) hz
    have h2 := false_of_isAltSixCoverThree_le_aux1 hsub hle hc
      ((MonoidHom.snd P P).comp φ.toMonoidHom) (Prod.snd_surjective.comp φ.surjective) hz
    apply hinc
    apply φ.injective
    rw [map_one]
    exact Prod.ext h1 h2
  · obtain ⟨P, _, hP, ⟨φ⟩⟩ := hJ
    obtain ⟨hs, hc⟩ := small1522_simple_center (Or.inl hP)
    haveI := hs
    have h1 := false_of_isAltSixCoverThree_le_aux1 hsub hle hc
      ((MonoidHom.fst P (P × P)).comp φ.toMonoidHom) (Prod.fst_surjective.comp φ.surjective) hz
    have h2 := false_of_isAltSixCoverThree_le_aux1 hsub hle hc
      ((MonoidHom.fst P P).comp ((MonoidHom.snd P (P × P)).comp φ.toMonoidHom))
      (Prod.fst_surjective.comp (Prod.snd_surjective.comp φ.surjective)) hz
    have h3 := false_of_isAltSixCoverThree_le_aux1 hsub hle hc
      ((MonoidHom.snd P P).comp ((MonoidHom.snd P (P × P)).comp φ.toMonoidHom))
      (Prod.snd_surjective.comp (Prod.snd_surjective.comp φ.surjective)) hz
    apply hinc
    apply φ.injective
    rw [map_one]
    exact Prod.ext h1 (Prod.ext h2 h3)

end CFSG.LocalAnalysis.RankThreeUC.S15
