module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76Props315b
public import CFSG.LocalAnalysis.ComponentClassification.Sol76LStruct
public import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit

variable {G : Type} [Group G]

@[expose] def theta (U : Subgroup G) (b : G) : Subgroup G :=
  ⁅oddCoreIn (centralizer ({b} : Set G)), U⁆ ⊔
    (oddCoreIn (centralizer ({b} : Set G)) ⊓ oddCoreIn (centralizer (U : Set G)))

@[expose] def wGroup (E U : Subgroup G) : Subgroup G :=
  ⨆ (e : G) (_ : e ∈ E) (_ : e ≠ 1), theta U e

theorem theta_eq_bot_iff {U : Subgroup G} {b : G} :
    theta U b = ⊥ ↔ ⁅oddCoreIn (centralizer ({b} : Set G)), U⁆ = ⊥ ∧
      oddCoreIn (centralizer ({b} : Set G)) ⊓ oddCoreIn (centralizer (U : Set G)) = ⊥ :=
  sup_eq_bot_iff

theorem theta_le_wGroup {E U : Subgroup G} {e : G} (he : e ∈ E) (he1 : e ≠ 1) :
    theta U e ≤ wGroup E U :=
  le_iSup₂_of_le e he (le_iSup_of_le he1 le_rfl)

theorem wGroup_eq_bot_iff {E U : Subgroup G} :
    wGroup E U = ⊥ ↔ ∀ e ∈ E, e ≠ 1 → theta U e = ⊥ := by
  refine ⟨fun h e he he1 => eq_bot_iff.mpr (h ▸ theta_le_wGroup he he1), fun h => ?_⟩
  refine eq_bot_iff.mpr (iSup₂_le fun e he => iSup_le fun he1 => ?_)
  rw [h e he he1]

theorem theta_le_oddCoreIn {U : Subgroup G} {b : G} (hU : U ≤ centralizer ({b} : Set G)) :
    theta U b ≤ oddCoreIn (centralizer ({b} : Set G)) :=
  sup_le (CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing _ _
      (hU.trans (le_normalizer_oddCoreIn _))) inf_le_left

theorem lemma315bInputFor_of_theta {𝒜 : Thm13Ambient}
    (h : ∀ (G : Type) [Group G] [Finite G], 𝒜 G → ∀ N : Subgroup G, IsSolomonChoice N →
      ∀ K ∈ kStarComponents N, ∀ K' ∈ kStarComponents N, K ≠ K' →
      ∀ B : Subgroup G, B ≤ K → CFSG.Open.IsElemAbelian 2 B → 4 ≤ Nat.card B →
      ∀ V : Subgroup G, V ≤ twoLayerIn (K' ⊓ centralizer (B : Set G)) →
        CFSG.Open.IsElemAbelian 2 V → V ≠ ⊥ →
      ∀ e ∈ B, e ≠ 1 → theta V e = ⊥) : Lemma315bInputFor 𝒜 :=
  fun G _ _ hG N hN K hK K' hK' hne B hBK hB hB4 V hV hVe hV1 e he he1 =>
    theta_eq_bot_iff.mp (h G hG N hN K hK K' hK' hne B hBK hB hB4 V hV hVe hV1 e he he1)

variable [Finite G]

theorem odd_card_theta {U : Subgroup G} {b : G} (hU : U ≤ centralizer ({b} : Set G)) :
    Odd (Nat.card (theta U b)) := by
  have h := coprime_card_oddCoreIn (centralizer ({b} : Set G))
  have hdvd := Subgroup.card_dvd_of_le (theta_le_oddCoreIn hU)
  exact Nat.coprime_two_left.mp (Nat.Coprime.coprime_dvd_right hdvd h)

omit [Finite G] in
theorem le_centralizer_of_le_of_comm {U₁ V₁ : Subgroup G} (hUV : U₁ ≤ V₁)
    (hV : ∀ x ∈ V₁, ∀ y ∈ V₁, x * y = y * x) : V₁ ≤ centralizer (U₁ : Set G) :=
  fun v hv => mem_centralizer_iff.mpr fun u hu => (hV v hv u (hUV hu)).symm

theorem oddCoreIn_inf_centralizer_le {U₁ V₁ : Subgroup G} (hUV : U₁ ≤ V₁) :
    oddCoreIn (centralizer (U₁ : Set G)) ⊓ centralizer (V₁ : Set G) ≤
      oddCoreIn (centralizer (V₁ : Set G)) :=
  inf_le_oddCoreIn (coprime_card_oddCoreIn _)
    ((centralizer_le (by exact_mod_cast hUV)).trans (le_normalizer_oddCoreIn _))

theorem theta_mono {U₁ V₁ : Subgroup G} {b : G} (hUV : U₁ ≤ V₁) (hV2 : IsPGroup 2 V₁)
    (hVc : ∀ x ∈ V₁, ∀ y ∈ V₁, x * y = y * x) (hVb : V₁ ≤ centralizer ({b} : Set G)) :
    theta U₁ b ≤ theta V₁ b := by
  set Ob := oddCoreIn (centralizer ({b} : Set G)) with hOb
  set Y := Ob ⊓ oddCoreIn (centralizer (U₁ : Set G)) with hY
  have hVOb : V₁ ≤ normalizer (Ob : Set G) := hVb.trans (le_normalizer_oddCoreIn _)
  have hVOU : V₁ ≤ normalizer (oddCoreIn (centralizer (U₁ : Set G)) : Set G) :=
    (le_centralizer_of_le_of_comm hUV hVc).trans (le_normalizer_oddCoreIn _)
  have hVY : V₁ ≤ normalizer (Y : Set G) := fun v hv => by
    rw [mem_normalizer_iff]
    intro y
    rw [hY, mem_inf, mem_inf, mem_normalizer_iff.mp (hVOb hv), mem_normalizer_iff.mp (hVOU hv)]
  have hYodd : Odd (Nat.card Y) := by
    have hdvd := Subgroup.card_dvd_of_le (inf_le_left : Y ≤ Ob)
    exact Nat.coprime_two_left.mp
      (Nat.Coprime.coprime_dvd_right hdvd (coprime_card_oddCoreIn _))
  have hfac := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization 2
    Nat.prime_two V₁ Y hV2 hVY (Nat.coprime_two_left.mpr hYodd)
  refine sup_le (le_sup_of_le_left (Subgroup.commutator_mono le_rfl hUV)) ?_
  show Y ≤ theta V₁ b
  rw [← hfac]
  refine sup_le (le_sup_of_le_left (Subgroup.commutator_mono inf_le_left le_rfl)) ?_
  refine le_sup_of_le_right (le_inf (inf_le_left.trans inf_le_left) ?_)
  exact (le_inf (inf_le_left.trans inf_le_right) inf_le_right).trans
    (oddCoreIn_inf_centralizer_le hUV)

end CFSG.ComponentClassification.Sol76.Sig
