module

public import CFSG.LocalAnalysis.ZStar
public import CFSG.CGT.Timmesfeld75.Defs

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

theorem zStarCase_of_comm_mem {K : Type*} [Group K] (N : Subgroup K) [N.Normal]
    (hodd : Odd (Nat.card N)) (hcomm : ∀ a b : K, ⁅a, b⁆ ∈ N) : ZStarCase K := by
  have hle : N ≤ fusionOddCore K := le_sSup ⟨inferInstance, hodd⟩
  unfold ZStarCase fusionZStar
  rw [eq_top_iff]
  intro a _
  rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
  intro b
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  have hab : ⁅b, a⁆ ∈ fusionOddCore K := hle (hcomm b a)
  have h1 : ⁅QuotientGroup.mk' (fusionOddCore K) b, QuotientGroup.mk' (fusionOddCore K) a⁆ = 1 := by
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).2 hab
  rw [commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

theorem zStarCase_normalClosure_of_card_two {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hT : IsWC T) (h2 : Nat.card T = 2) :
    ZStarCase ↥(Subgroup.normalClosure (T : Set G)) := by
  have hTbot : T ≠ ⊥ := by
    intro h; rw [h] at h2; simp at h2
  obtain ⟨⟨t, htT⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hTbot
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  have hsq : t * t = 1 := by
    have := hT.1.2 t htT
    simpa [pow_two] using this
  have hord : orderOf t = 2 := orderOf_eq_prime (by simpa [pow_two] using hsq) ht1'
  have hTeq : T = Subgroup.zpowers t := by
    symm
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.zpowers_le]; exact htT
    · rw [Nat.card_zpowers, hord, h2]
  have hiso : ∀ g : G, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) → g * t * g⁻¹ = t := by
    intro g hg
    have hs1 : g * t * g⁻¹ ≠ 1 := by
      intro h; apply ht1'
      have e : t = g⁻¹ * (g * t * g⁻¹) * g := by group
      rw [e, h]; group
    have hle : conjSubgroup g T ≤ Subgroup.centralizer ({t} : Set G) := by
      intro x hx
      rw [mem_conjSubgroup, hTeq] at hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hx
      have hxk : x = (g * t * g⁻¹) ^ k := by
        rw [conj_zpow, hk]; group
      refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
      rw [Set.mem_singleton_iff] at hh
      rw [hh, hxk]
      exact Commute.zpow_right (show Commute t (g * t * g⁻¹) from hg.symm) k
    have hconj := (hT.2 t htT ht1').2 g hle
    have hmem : g * t * g⁻¹ ∈ conjSubgroup g T := by
      rw [mem_conjSubgroup]
      have e : g⁻¹ * (g * t * g⁻¹) * g = t := by group
      rw [e]; exact htT
    rw [hconj, hTeq] at hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have hpow : t ^ k = t ^ (k % 2) :=
      zpow_eq_zpow_emod k (by simpa [hord] using pow_orderOf_eq_one t)
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · rw [hpow, h] at hk; simp at hk; exact absurd hk.symm hs1
    · rw [hpow, h] at hk; simpa using hk.symm
  have : Fintype G := Fintype.ofFinite G
  obtain ⟨N, hNn, hNodd, hNc⟩ := CFSG.ZStar.glauberman_zStar G t ht1' hsq hiso
  have hcentral : ∀ g : G, QuotientGroup.mk' N t * QuotientGroup.mk' N g =
      QuotientGroup.mk' N g * QuotientGroup.mk' N t := by
    intro g
    have h1 : QuotientGroup.mk' N (g * t * g⁻¹ * t⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (hNc g)
    simp only [map_mul, map_inv] at h1
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  have hnormal : (Subgroup.zpowers (QuotientGroup.mk' N t)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    have hc : QuotientGroup.mk' N g * QuotientGroup.mk' N t * (QuotientGroup.mk' N g)⁻¹ =
        QuotientGroup.mk' N t := by
      rw [← hcentral g]; group
    have e : (QuotientGroup.mk g : G ⧸ N) = QuotientGroup.mk' N g := rfl
    rw [e, ← conj_zpow, hc]
    exact Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩
  have : (Subgroup.comap (QuotientGroup.mk' N) (Subgroup.zpowers (QuotientGroup.mk' N t))).Normal :=
    Subgroup.Normal.comap hnormal _
  have hK : Subgroup.normalClosure (T : Set G) ≤
      Subgroup.comap (QuotientGroup.mk' N) (Subgroup.zpowers (QuotientGroup.mk' N t)) := by
    apply Subgroup.normalClosure_le_normal
    intro x hx
    rw [SetLike.mem_coe, hTeq] at hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [SetLike.mem_coe, Subgroup.mem_comap, map_zpow]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k
  have hcomm : ∀ a b : ↥(Subgroup.normalClosure (T : Set G)), ⁅a, b⁆ ∈
      N.subgroupOf (Subgroup.normalClosure (T : Set G)) := by
    intro a b
    rw [Subgroup.mem_subgroupOf]
    have ha := hK a.2
    rw [Subgroup.mem_comap] at ha
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 ha
    have hab : QuotientGroup.mk' N (a : G) * QuotientGroup.mk' N (b : G) =
        QuotientGroup.mk' N (b : G) * QuotientGroup.mk' N (a : G) := by
      rw [← hk]
      exact (Commute.zpow_left (show Commute (QuotientGroup.mk' N t)
        (QuotientGroup.mk' N (b : G)) from hcentral b) k)
    have h1 : QuotientGroup.mk' N ⁅(a : G), (b : G)⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hab
    exact (QuotientGroup.eq_one_iff _).1 h1
  have hodd : Odd (Nat.card (N.subgroupOf (Subgroup.normalClosure (T : Set G)))) := by
    let f : ↥(N.subgroupOf (Subgroup.normalClosure (T : Set G))) →* ↥N :=
      MonoidHom.codRestrict
        ((Subgroup.normalClosure (T : Set G)).subtype.comp
          (N.subgroupOf (Subgroup.normalClosure (T : Set G))).subtype) N (fun x => x.2)
    have hf : Function.Injective f := fun x y hxy => by
      apply Subtype.ext; apply Subtype.ext
      exact congrArg (fun z : ↥N => (z : G)) hxy
    exact Odd.of_dvd_nat hNodd (Subgroup.card_dvd_of_injective f hf)
  exact zStarCase_of_comm_mem _ hodd hcomm

end CFSG.CGT.Timmesfeld75
