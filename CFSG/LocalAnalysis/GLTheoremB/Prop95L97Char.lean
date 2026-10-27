module

import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.GLTheoremB.CentralizerLift
public import CFSG.LocalAnalysis.GLTheoremB.UniqDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Quasithin.Background.B2Thompson
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.L97

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LocalAnalysis.GLTheoremB

variable {G : Type*} [Group G] [Finite G]

private theorem isCharIn_of_le_map {T T₀ : Subgroup G} (hle : T₀ ≤ T)
    (h : ∀ ψ : ↥T ≃* ↥T,
      T₀ ≤ (((T₀.subgroupOf T).comap ψ.toMonoidHom).map T.subtype)) :
    IsCharIn T₀ T := by
  refine ⟨hle, fun ψ x hx => ?_⟩
  obtain ⟨w, hw, hwx⟩ := h ψ hx
  obtain rfl : w = x := Subtype.ext hwx
  exact hw

private theorem le_thompsonJ_aux {H A : Subgroup G} (hA : IsMaxElemAbelian H A) :
    A ≤ thompsonJ H :=
  le_iSup₂ (f := fun (A : Subgroup G) (_ : IsMaxElemAbelian H A) => A) A hA

private theorem isMaxElemAbelian_map_aut {T A : Subgroup G} (ψ : ↥T ≃* ↥T)
    (hA : IsMaxElemAbelian T A) :
    IsMaxElemAbelian T (((A.subgroupOf T).map ψ.toMonoidHom).map T.subtype) := by
  have hcard : Nat.card (((A.subgroupOf T).map ψ.toMonoidHom).map T.subtype) = Nat.card A := by
    rw [Subgroup.card_map_of_injective T.subtype_injective,
      Subgroup.card_map_of_injective ψ.injective, ← Subgroup.card_subtype T (A.subgroupOf T),
      Subgroup.map_subgroupOf_eq_of_le hA.1]
  have hAe : IsElemAbelian 2 A := hA.2.1
  refine ⟨Subgroup.map_subtype_le _,
    ((hAe.subgroupOf T).map ψ.toMonoidHom).map T.subtype, fun B hBT hB => ?_⟩
  rw [hcard]
  exact hA.2.2 B hBT hB

theorem isCharIn_thompsonJ (T : Subgroup G) : IsCharIn (thompsonJ T) T := by
  refine isCharIn_of_le_map (iSup₂_le fun A hA => hA.1) fun ψ => ?_
  refine iSup₂_le fun A hA a ha => ?_
  refine ⟨⟨a, hA.1 ha⟩, ?_, rfl⟩
  exact le_thompsonJ_aux (isMaxElemAbelian_map_aut ψ hA)
    ⟨ψ ⟨a, hA.1 ha⟩, ⟨⟨a, hA.1 ha⟩, ha, rfl⟩, rfl⟩

theorem isCharIn_omegaOneCenter (T : Subgroup G) : IsCharIn (quasithinOmegaOneCenter T) T := by
  refine isCharIn_of_le_map ((Subgroup.closure_le _).2 fun z hz => hz.1.1) fun ψ => ?_
  refine (Subgroup.closure_le _).2 fun z hz => ?_
  obtain ⟨hzI, hz2⟩ := hz
  have hzT : z ∈ T := (Subgroup.mem_inf.1 hzI).1
  have hzC : z ∈ Subgroup.centralizer (T : Set G) := (Subgroup.mem_inf.1 hzI).2
  refine ⟨⟨z, hzT⟩, ?_, rfl⟩
  refine Subgroup.subset_closure ⟨Subgroup.mem_inf.2 ⟨(ψ ⟨z, hzT⟩).2, ?_⟩, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨s, hs⟩ := ψ.surjective ⟨h, hh⟩
    have hcomm : s * (⟨z, hzT⟩ : ↥T) = ⟨z, hzT⟩ * s :=
      Subtype.ext (Subgroup.mem_centralizer_iff.1 hzC s s.2)
    have h1 := congrArg (fun y : ↥T => ((ψ y : ↥T) : G)) hcomm
    simp only [map_mul, hs, Subgroup.coe_mul] at h1
    exact h1
  · have h1 : (⟨z, hzT⟩ : ↥T) ^ 2 = 1 := Subtype.ext (by simpa using hz2)
    have h2 : (ψ ⟨z, hzT⟩) ^ 2 = 1 := by rw [← map_pow, h1, map_one]
    simpa using congrArg Subtype.val h2

theorem thompsonJ_ne_bot {T : Subgroup G} (hT2 : IsPGroup 2 T) (hT : T ≠ ⊥) :
    thompsonJ T ≠ ⊥ := by
  have hdvd : 2 ∣ Nat.card T :=
    (hT2.card_eq_or_dvd).resolve_left fun h => hT (Subgroup.card_eq_one.1 h)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥T) 2 hdvd
  have hx2 : (x : G) ^ 2 = 1 := by
    have := pow_orderOf_eq_one (x : G)
    rwa [Subgroup.orderOf_coe, hx] at this
  obtain ⟨A, hA⟩ := CFSG.Quasithin.exists_isMaxElemAbelian T
  have hcard : 2 ≤ Nat.card A := by
    have h := hA.2.2 (Subgroup.zpowers (x : G)) ((Subgroup.zpowers_le).2 x.2)
      (CFSG.Open.isElemAbelian_zpowers hx2)
    rwa [Nat.card_zpowers, Subgroup.orderOf_coe, hx] at h
  intro hJ
  have hA0 : A = ⊥ := le_bot_iff.1 (hJ ▸ le_thompsonJ_aux hA)
  rw [hA0, Subgroup.card_bot] at hcard
  omega

theorem omegaOneCenter_ne_bot {T : Subgroup G} (hT2 : IsPGroup 2 T) (hT : T ≠ ⊥) :
    quasithinOmegaOneCenter T ≠ ⊥ := by
  haveI : Nontrivial ↥T := (Subgroup.nontrivial_iff_ne_bot T).2 hT
  have hZ : Nontrivial (Subgroup.center ↥T) := hT2.center_nontrivial
  have hZ2 : IsPGroup 2 (Subgroup.center ↥T) := hT2.to_subgroup _
  obtain ⟨n, hn0, hn⟩ := hZ2.nontrivial_iff_card.1 hZ
  have hdvd : 2 ∣ Nat.card (Subgroup.center ↥T) := hn ▸ dvd_pow_self 2 (ne_of_gt hn0)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center ↥T) 2 hdvd
  have hzc : ∀ g : ↥T, g * (z : ↥T) = (z : ↥T) * g := Subgroup.mem_center_iff.1 z.2
  have hord : orderOf ((z : ↥T) : G) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  have hz2 : ((z : ↥T) : G) ^ 2 = 1 := by
    have := pow_orderOf_eq_one (((z : ↥T)) : G)
    rwa [hord] at this
  have hz1 : ((z : ↥T) : G) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    omega
  have hmem : ((z : ↥T) : G) ∈ quasithinOmegaOneCenter T := by
    refine Subgroup.subset_closure ⟨Subgroup.mem_inf.2 ⟨(z : ↥T).2, ?_⟩, hz2⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact congrArg Subtype.val (hzc ⟨h, hh⟩)
  intro hbot
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hz1 hmem

theorem inf_normalizer_le_normalizer_of_isSylowTwoOf {Y Γ T₀ : Subgroup G}
    (hΓ : IsSylowTwoOf Γ Y) (hle : Γ ≤ pCoreOf 2 (Subgroup.normalizer (T₀ : Set G))) :
    Y ⊓ Subgroup.normalizer (T₀ : Set G) ≤ Subgroup.normalizer (Γ : Set G) := by
  set P := pCoreOf 2 (Subgroup.normalizer (T₀ : Set G))
  have hPΓ : P ⊓ Y = Γ := by
    refine le_antisymm ?_ (le_inf hle hΓ.1)
    have hQ2 : IsPGroup 2 (P ⊓ Y : Subgroup G) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left
    obtain ⟨m, hm⟩ := hQ2.exists_card_eq
    have hmul := Subgroup.relIndex_mul_relIndex Γ (P ⊓ Y) Y (le_inf hle hΓ.1) inf_le_right
    have hdvd : Γ.relIndex (P ⊓ Y) ∣ Γ.relIndex Y := ⟨_, hmul.symm⟩
    have hdvd2 : Γ.relIndex (P ⊓ Y) ∣ 2 ^ m := by
      rw [← hm]
      exact Subgroup.relIndex_dvd_card Γ (P ⊓ Y)
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd2
    have hk0 : k = 0 := by
      by_contra hk0
      exact hΓ.2.2 ((dvd_pow_self 2 hk0).trans (hk ▸ hdvd))
    rw [hk0, pow_zero] at hk
    exact Subgroup.relIndex_eq_one.1 hk
  intro n hn
  have hnP : n ∈ Subgroup.normalizer (P : Set G) := le_normalizer_pCoreOf 2 _ hn.2
  have hnY : n ∈ Subgroup.normalizer (Y : Set G) := Subgroup.le_normalizer hn.1
  have := mem_normalizer_inf hnP hnY
  rwa [hPΓ] at this

theorem le_normalizer_of_factorization {Y Γ T₀ T₁ : Subgroup G} (hΓ : IsSylowTwoOf Γ Y)
    (h₀ : Γ ≤ pCoreOf 2 (Subgroup.normalizer (T₀ : Set G)))
    (h₁ : Γ ≤ pCoreOf 2 (Subgroup.normalizer (T₁ : Set G)))
    (hfac : ∀ h ∈ Y, ∃ n ∈ Y ⊓ Subgroup.normalizer (T₀ : Set G),
      ∃ c ∈ Y ⊓ Subgroup.centralizer (T₁ : Set G), h = n * c) :
    Y ≤ Subgroup.normalizer (Γ : Set G) := by
  intro h hh
  obtain ⟨n, hn, c, hc, rfl⟩ := hfac h hh
  have hc' : c ∈ Y ⊓ Subgroup.normalizer (T₁ : Set G) :=
    ⟨hc.1, Subgroup.centralizer_le_normalizer _ hc.2⟩
  exact (Subgroup.normalizer (Γ : Set G)).mul_mem
    (inf_normalizer_le_normalizer_of_isSylowTwoOf hΓ h₀ hn)
    (inf_normalizer_le_normalizer_of_isSylowTwoOf hΓ h₁ hc')

end CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.L97
