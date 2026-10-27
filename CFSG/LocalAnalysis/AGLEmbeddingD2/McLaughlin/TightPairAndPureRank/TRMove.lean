module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRBridge

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open scoped commutatorElement Pointwise
open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

variable {G : Type} [Group G] [Finite G]

theorem false_of_both_le_gnC {M X₀ T L₁ L₂ : Subgroup G} (hTX : T ≤ X₀)
    (hT2 : IsPGroup 2 T) (hT0 : T ≠ ⊥) (hD : GNBound (T.subgroupOf X₀))
    (hL₁X : L₁ ≤ X₀) (hL₁M : L₁ ≤ M) (hL₂M : L₂ ≤ M)
    (hp₁ : ⁅L₁, L₁⁆ = L₁)
    (hc : ⁅barM M L₁, barM M L₂⁆ = ⊥)
    (hZ₁ : ¬ 3 ∣ Nat.card (Subgroup.center ↥(barM M L₁)))
    (h3₁ : 3 ∣ Nat.card (barM M L₁)) (h3₂ : 3 ∣ Nat.card (barM M L₂))
    (hL₂X : L₂ ≤ X₀)
    (hle₁ : L₁.subgroupOf X₀ ≤ gnC (T.subgroupOf X₀))
    (hle₂ : L₂.subgroupOf X₀ ≤ gnC (T.subgroupOf X₀)) : False := by
  have hTh2 : IsPGroup 2 ↥(T.subgroupOf X₀) :=
    hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTX).symm
  have hTh0 : T.subgroupOf X₀ ≠ ⊥ := by
    intro h
    apply hT0
    have := Subgroup.map_subgroupOf_eq_of_le hTX
    rw [h, Subgroup.map_bot] at this
    exact this.symm
  set Z : Subgroup ↥X₀ := Quasithin.omegaOneCenterOf (T.subgroupOf X₀) with hZ
  have hZb : Z ≠ ⊥ := QuasithinUnique.Setup.omegaOneCenterOf_ne_bot hTh2 hTh0
  have hZT : Z ≤ T.subgroupOf X₀ := QuasithinUnique.Setup.omegaOneCenterOf_le _
  have hZc : (Z.subgroupOf (T.subgroupOf X₀)).Characteristic :=
    QuasithinUnique.Setup.characteristic_omegaOneCenterOf _
  obtain ⟨hr, hp⟩ := hD Z hZb hZT hZc
  have hnorm : ∀ l ∈ gnC (T.subgroupOf X₀), l ∈ Subgroup.normalizer (Z : Set ↥X₀) := by
    intro l hl
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzV : z ∈ gnV (T.subgroupOf X₀) := Subgroup.subset_normalClosure hz
    exact Subgroup.mem_centralizer_iff.mp hl z hzV
  have hsup : L₁.subgroupOf X₀ ⊔ L₂.subgroupOf X₀ ≤ Subgroup.normalizer (Z : Set ↥X₀) :=
    sup_le (fun l hl => hnorm l (hle₁ hl)) (fun l hl => hnorm l (hle₂ hl))
  have hc' : ∀ a ∈ barM M L₁, ∀ b ∈ barM M L₂, a * b = b * a := by
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp
      ((Subgroup.commutator_eq_bot_iff_le_centralizer).mp hc ha) b hb).symm
  have hi : Nat.Coprime 3 (Nat.card (barM M L₁ ⊓ barM M L₂ : Subgroup _)) := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro hdvd
    apply hZ₁
    rw [← card_inf_centralizer_eq_card_center]
    refine hdvd.trans (Subgroup.card_dvd_of_le fun u hu => ⟨hu.1, ?_⟩)
    exact Subgroup.mem_centralizer_iff.mpr fun g hg => hc' g hg u hu.2
  have hrk : 2 ≤ Open.pRank 3 (Subgroup.normalizer (Z : Set ↥X₀)) := by
    have h1 := pRank_add_le_pRank_sup_of_coprime Nat.prime_three hc' hi
    have h2 := CFSG.AGLEmbeddingD2.one_le_pRank_of_dvd Nat.prime_three h3₁
    have h3 := CFSG.AGLEmbeddingD2.one_le_pRank_of_dvd Nat.prime_three h3₂
    have h4 : Open.pRank 3 (barM M L₁ ⊔ barM M L₂) =
        Open.pRank 3 (L₁.subgroupOf X₀ ⊔ L₂.subgroupOf X₀) := by
      rw [← barM_sup_eq hL₁M hL₂M, pRank_barM_eq Nat.prime_three (by norm_num) M _ (sup_le hL₁M hL₂M),
        ← CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective 3 Nat.prime_three X₀.subtype
          X₀.subtype_injective, Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hL₁X,
        Subgroup.map_subgroupOf_eq_of_le hL₂X]
    have h5 := CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 Nat.prime_three hsup
    have h6 : Open.pRank 3 (barM M L₁) = Open.pRank 3 L₁ :=
      pRank_barM_eq Nat.prime_three (by norm_num) M L₁ hL₁M
    omega
  have h3L₁ : 3 ∣ Nat.card L₁ := by
    refine h3₁.trans ?_
    unfold barM
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL₁M).toEquiv]
    exact Subgroup.card_map_dvd _ _
  have h3L₁' : 3 ∣ Nat.card (L₁.subgroupOf X₀) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL₁X).toEquiv]
    exact h3L₁
  exact hp hrk _ (fun l hl => hsup (Subgroup.mem_sup_left hl)) (perfect_subgroupOf hL₁X hp₁) h3L₁'

omit [Finite G] in
theorem le_gnC_of_conj {M X₀ T L₁ L₂ : Subgroup G} (hXM : X₀ ≤ M) (hTX : T ≤ X₀)
    (hQT : pCoreOf 2 M ≤ T) (hL₂M : L₂ ≤ M) (hL₁X : L₁ ≤ X₀) {t : G} (ht : t ∈ T)
    (hbar : barM M (L₁.map (MulAut.conj t).toMonoidHom) = barM M L₂)
    (hle : L₁.subgroupOf X₀ ≤ gnC (T.subgroupOf X₀)) :
    L₂.subgroupOf X₀ ≤ gnC (T.subgroupOf X₀) := by
  set C := gnC (T.subgroupOf X₀) with hC
  set L₁t := L₁.map (MulAut.conj t).toMonoidHom with hL₁t
  have htX : t ∈ X₀ := hTX ht
  have hL₁tX : L₁t ≤ X₀ := by
    rintro _ ⟨l, hl, rfl⟩
    exact X₀.mul_mem (X₀.mul_mem htX (hL₁X hl)) (X₀.inv_mem htX)
  have h1 : L₁t.subgroupOf X₀ ≤ C := by
    intro x hx
    obtain ⟨l, hl, hlx⟩ := Subgroup.mem_subgroupOf.mp hx
    have hlx' : t * l * t⁻¹ = (x : G) := by simpa using hlx
    have hlC : (⟨l, hL₁X hl⟩ : ↥X₀) ∈ C := hle (Subgroup.mem_subgroupOf.mpr hl)
    have := (inferInstance : C.Normal).conj_mem _ hlC (⟨t, htX⟩ : ↥X₀)
    have hxe : x = (⟨t, htX⟩ : ↥X₀) * ⟨l, hL₁X hl⟩ * (⟨t, htX⟩ : ↥X₀)⁻¹ :=
      Subtype.ext (by simpa using hlx'.symm)
    rw [hxe]; exact this
  have hker : (pCoreOf 2 M).subgroupOf X₀ ≤ C := pCoreOf_subgroupOf_le_gnC hXM hTX hQT
  have hL₁tM : L₁t ≤ M := hL₁tX.trans hXM
  have hsup : L₂ ≤ L₁t ⊔ pCoreOf 2 M := le_sup_pCoreOf_of_barM_le hL₂M hbar.symm.le
  have hle' : L₁t ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
    hL₁tM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right L₁t (pCoreOf 2 M) hle'
  intro x hx
  have hxm : (x : G) ∈ (L₁t : Set G) * (pCoreOf 2 M : Set G) := by
    rw [← hset]; exact hsup (Subgroup.mem_subgroupOf.mp hx)
  obtain ⟨a, ha, q, hq, hxe⟩ := hxm
  have haX : a ∈ X₀ := hL₁tX ha
  have hqX : q ∈ X₀ := by
    have : q = a⁻¹ * (x : G) := by rw [← hxe]; group
    rw [this]; exact X₀.mul_mem (X₀.inv_mem haX) x.2
  have hxe' : x = (⟨a, haX⟩ : ↥X₀) * ⟨q, hqX⟩ := Subtype.ext hxe.symm
  rw [hxe']
  exact C.mul_mem (h1 (Subgroup.mem_subgroupOf.mpr ha)) (hker (Subgroup.mem_subgroupOf.mpr hq))

omit [Finite G] in
theorem barM_conj_inv {M L₁ L₂ : Subgroup G} {t : G} (htM : t ∈ M)
    (hbar : barM M (L₁.map (MulAut.conj t).toMonoidHom) = barM M L₂) :
    barM M (L₂.map (MulAut.conj t⁻¹).toMonoidHom) = barM M L₁ := by
  rw [barM_map_conj (M.inv_mem htM), ← hbar, barM_map_conj htM, Subgroup.map_map]
  have : (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥M) (⟨t⁻¹, M.inv_mem htM⟩ : ↥M))).toMonoidHom.comp
      (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨t, htM⟩)).toMonoidHom = MonoidHom.id _ := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.id_apply]
    have e : (⟨t⁻¹, M.inv_mem htM⟩ : ↥M) = ⟨t, htM⟩⁻¹ := rfl
    rw [e, map_inv]
    group
  rw [this, Subgroup.map_id]

theorem trBlocksMove_of_swap {P : Sylow 3 G} {M A H R : Subgroup G}
    (hctx : PairStrongCtx P M A H R) (hK : KFactStrongThreeSolv)
    {L₁ L₂ T : Subgroup G} (h₁ : IsWeakSBlock M (pCoreOf 2 H) L₁)
    (h₂ : IsWeakSBlock M (pCoreOf 2 H) L₂) (hne : barM M L₁ ≠ barM M L₂)
    (hT2 : IsPGroup 2 T) (hT0 : T ≠ ⊥) (hTM : T ≤ M) (hNT : ¬ Subgroup.normalizer (T : Set G) ≤ M)
    (hQT : pCoreOf 2 M ≤ T)
    (hZ₁ : ¬ 3 ∣ Nat.card (Subgroup.center ↥(barM M L₁)))
    (h3₁ : 3 ∣ Nat.card (barM M L₁)) (h3₂ : 3 ∣ Nat.card (barM M L₂))
    {t : G} (ht : t ∈ T) (hbar : barM M (L₁.map (MulAut.conj t).toMonoidHom) = barM M L₂) :
    ¬ L₁.subgroupOf (trX M L₁ L₂ T) ≤ gnC (T.subgroupOf (trX M L₁ L₂ T)) ∧
      ¬ L₂.subgroupOf (trX M L₁ L₂ T) ≤ gnC (T.subgroupOf (trX M L₁ L₂ T)) := by
  have hXM : trX M L₁ L₂ T ≤ M := trX_le h₁.le h₂.le hTM
  have hTX : T ≤ trX M L₁ L₂ T := le_trX_right
  have hL₁X : L₁ ≤ trX M L₁ L₂ T := le_trJ_left.trans le_trX_left
  have hL₂X : L₂ ≤ trX M L₁ L₂ T := le_trJ_right.trans le_trX_left
  have hD := gnBound_of_pair hctx hK hT2 hTX hXM hNT
  have hc : ⁅barM M L₁, barM M L₂⁆ = ⊥ :=
    CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ h₁.component h₂.component hne
  have htM : t ∈ M := hTM ht
  have hbar' := barM_conj_inv htM hbar
  have ht' : t⁻¹ ∈ T := T.inv_mem ht
  constructor
  · intro hle₁
    have hle₂ := le_gnC_of_conj hXM hTX hQT h₂.le hL₁X ht hbar hle₁
    exact false_of_both_le_gnC hTX hT2 hT0 hD hL₁X h₁.le h₂.le h₁.perfect hc hZ₁ h3₁ h3₂ hL₂X hle₁ hle₂
  · intro hle₂
    have hle₁ := le_gnC_of_conj hXM hTX hQT h₁.le hL₂X ht' hbar' hle₂
    exact false_of_both_le_gnC hTX hT2 hT0 hD hL₁X h₁.le h₂.le h₁.perfect hc hZ₁ h3₁ h3₂ hL₂X hle₁ hle₂

end CFSG.AGLEmbeddingD2.McLaughlin
