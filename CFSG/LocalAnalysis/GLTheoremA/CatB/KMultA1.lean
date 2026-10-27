module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.MultA3Core

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.KMultA1

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.MI
open CFSG.LocalAnalysis.GLTheoremA.CatB.MultA1 CFSG.LocalAnalysis.GLTheoremA.CatB.MultA2
open CFSG.LocalAnalysis.GLTheoremA.CatB.MultA3

@[expose] def TD4OddNoG2Layer : Prop :=
  ∀ (S : Type) [Group S], catalogIs S (onLie fun | .trialityD4 q => q.p ≠ 2 | _ => False) →
    ∀ β : MulAut S, β ^ 3 = 1 →
      β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner S →
    ∀ J : Subgroup S, CFSG.Open.IsSubnormal J (FP.fixSub β) →
      ∀ (n : ℕ) (T : Type) [Group T], catalogIs T (S10.isG2n n) →
        ∀ φ : ↥J →* T, Function.Surjective φ → False

@[expose] def G2FieldLayerAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X L I : Subgroup G) (b : G), GLAPComponent 3 X L → CFSG.Open.IsQuasisimple ↥L → b ^ 3 = 1 →
    FieldOn 3 b L → GLAPComponent 3 (L ⊓ cx b) I →
    catalogIs (PSimple 3 I) (S10.isG2n 2) → catalogIs (PSimple 3 L) (S10.isG2n 6)

variable {G : Type} [Group G] [Finite G]

theorem ker_chevQuotHom_le_center {X L : Subgroup G} (hL : GLAPComponent 3 X L)
    (hLq : CFSG.Open.IsQuasisimple ↥L) :
    (chevQuotHom 3 L).ker ≤ Subgroup.center ↥L := by
  refine le_center_of_normal_of_isQuasisimple hLq inferInstance ?_
  intro htop
  have hsimple := (isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hL).2
  haveI := hsimple.toNontrivial
  obtain ⟨x, hx⟩ := exists_ne (1 : PSimple 3 L)
  obtain ⟨y, rfl⟩ := chevQuotHom_surjective 3 L x
  have hy : y ∈ (chevQuotHom 3 L).ker := htop ▸ Subgroup.mem_top y
  exact hx (MonoidHom.mem_ker.1 hy)

theorem center_le_ker_chevQuotHom (L : Subgroup G) :
    Subgroup.center ↥L ≤ (chevQuotHom 3 L).ker := by
  intro z hz
  rw [MonoidHom.mem_ker]
  have hc : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) z : PQuot 3 L) ∈ Subgroup.center (PQuot 3 L) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥L) y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz l]
  show QuotientGroup.mk' (Subgroup.center (PQuot 3 L)) (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) z) = 1
  exact (QuotientGroup.eq_one_iff _).2 hc

theorem ker_chevQuotHom_eq_center {X L : Subgroup G} (hL : GLAPComponent 3 X L)
    (hLq : CFSG.Open.IsQuasisimple ↥L) :
    (chevQuotHom 3 L).ker = Subgroup.center ↥L :=
  le_antisymm (ker_chevQuotHom_le_center hL hLq) (center_le_ker_chevQuotHom L)

noncomputable def chevIso {X L : Subgroup G} (hL : GLAPComponent 3 X L)
    (hLq : CFSG.Open.IsQuasisimple ↥L) : ↥L ⧸ Subgroup.center ↥L ≃* PSimple 3 L :=
  centralIso (chevQuotHom 3 L) (chevQuotHom_surjective 3 L) (ker_chevQuotHom_eq_center hL hLq)

theorem chevQuotHom_injective_of_center {X L : Subgroup G} (hL : GLAPComponent 3 X L)
    (hLq : CFSG.Open.IsQuasisimple ↥L) (hc : Subgroup.center ↥L = ⊥) :
    Function.Injective (chevQuotHom 3 L) := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_chevQuotHom_eq_center hL hLq, hc]

theorem glaPrimeCoreOf_eq_bot_of_injective {L : Subgroup G}
    (hinj : Function.Injective (chevQuotHom 3 L)) : GLAPPrimeCoreOf 3 L = ⊥ := by
  have hO : GLAPPrimeCore 3 ↥L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    apply hinj
    rw [map_one]
    have h1 : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) x : PQuot 3 L) = 1 :=
      (QuotientGroup.eq_one_iff x).2 hx
    show QuotientGroup.mk' (Subgroup.center (PQuot 3 L)) (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) x) = 1
    rw [h1, map_one]
  show (GLAPPrimeCore 3 ↥L).map L.subtype = ⊥
  rw [hO, Subgroup.map_bot]

theorem td4_index {S : Type} [Group S]
    (h : catalogIs S (onLie fun | .trialityD4 _ => True | _ => False)) :
    ∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
      Nonempty (S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie j =>
    obtain ⟨d, hv⟩ := j
    cases d with
    | trialityD4 q => exact ⟨q, hv, ⟨e⟩⟩
    | _ => exact hi.elim

theorem center_eq_bot_of_td4 (hGA : CFSG.Open.GriessAllModelsStatement) {X L : Subgroup G}
    (hL : GLAPComponent 3 X L) (hLq : CFSG.Open.IsQuasisimple ↥L) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid)
    (e : PSimple 3 L ≃* TauCeti.ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩) :
    Subgroup.center ↥L = ⊥ := by
  have hm : CFSG.Models.LieModel (↥L ⧸ Subgroup.center ↥L) .trialityD4 0 q.p q.exponent :=
    CFSG.Models.lieModel_of_namesTag (t := .trialityD4) (p := q.p) (f := q.exponent)
      ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨_, hv⟩ ⟨rfl, rfl⟩ ((chevIso hL hLq).trans e)
  have hd := card_center_dvd_of_table hGA hLq hm (a := 1) (b := 1) (c := 1) (d := 1)
    rfl rfl (by norm_num)
  have hd' : Nat.card (Subgroup.center ↥L) ∣ 1 := by simpa using hd
  exact Subgroup.eq_bot_of_card_eq _ (Nat.dvd_one.1 hd')

theorem center_eq_bot_of_G2_six (hGA : CFSG.Open.GriessAllModelsStatement) {X L : Subgroup G}
    (hL : GLAPComponent 3 X L) (hLq : CFSG.Open.IsQuasisimple ↥L)
    (hcat : catalogIs (PSimple 3 L) (S10.isG2n 6)) :
    Subgroup.center ↥L = ⊥ := by
  obtain ⟨q, hv, hq2, hq6, ⟨e⟩⟩ := lieIndex_isG2n hcat
  have hd := (card_center_dvd_G2 hGA hLq hq2 hq6 ((chevIso hL hLq).trans e)).2 (by norm_num)
  exact Subgroup.eq_bot_of_card_eq _ (Nat.dvd_one.1 hd)

theorem indAut_chevQuotHom {L : Subgroup G} {b : G} (hb : b ∈ Subgroup.normalizer (L : Set G)) (k : ↥L) :
    indAut 3 L b hb (chevQuotHom 3 L k) =
      chevQuotHom 3 L (L.normalizerMonoidHom ⟨b⁻¹, Subgroup.inv_mem _ hb⟩ k) :=
  chevAut_chevQuotHom 3 L ⟨b⁻¹, Subgroup.inv_mem _ hb⟩ k

theorem fixSub_indAut_eq {L : Subgroup G} {b : G} (hb : b ∈ Subgroup.normalizer (L : Set G))
    (hinj : Function.Injective (chevQuotHom 3 L)) :
    FP.fixSub (indAut 3 L b hb) = ((L ⊓ cx b).subgroupOf L).map (chevQuotHom 3 L) := by
  ext x
  obtain ⟨k, rfl⟩ := chevQuotHom_surjective 3 L x
  have key : ∀ k : ↥L, chevQuotHom 3 L (L.normalizerMonoidHom ⟨b⁻¹, Subgroup.inv_mem _ hb⟩ k) =
      chevQuotHom 3 L k ↔ k ∈ (L ⊓ cx b).subgroupOf L := by
    intro k
    have hN : ((L.normalizerMonoidHom ⟨b⁻¹, Subgroup.inv_mem _ hb⟩ k : ↥L) : G) = b⁻¹ * (k : G) * b := by
      simp
    have hmem : k ∈ (L ⊓ cx b).subgroupOf L ↔ b * (k : G) = (k : G) * b := by
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, cx, Subgroup.mem_centralizer_iff]
      constructor
      · rintro ⟨-, h⟩
        exact h b (Set.mem_singleton b)
      · intro h
        exact ⟨k.2, fun g hg => by obtain rfl := Set.mem_singleton_iff.1 hg; exact h⟩
    rw [hinj.eq_iff, hmem, Subtype.ext_iff, hN]
    constructor
    · intro h
      have h2 : (k : G) * b = b * (k : G) := by
        calc (k : G) * b = b * (b⁻¹ * (k : G) * b) := by group
          _ = b * (k : G) := by rw [h]
      exact h2.symm
    · intro h
      calc b⁻¹ * (k : G) * b = b⁻¹ * ((k : G) * b) := by group
        _ = b⁻¹ * (b * (k : G)) := by rw [h]
        _ = (k : G) := by group
  rw [FP.mem_fixSub, indAut_chevQuotHom hb k, Subgroup.mem_map]
  constructor
  · intro h
    exact ⟨k, (key k).1 h, rfl⟩
  · rintro ⟨k', hk', hkk⟩
    have : k' = k := hinj hkk
    subst this
    exact (key k').2 hk'

theorem clauseA_of (hGA : CFSG.Open.GriessAllModelsStatement) (hOdd : TD4OddNoG2Layer)
    {X L I : Subgroup G} {b : G} {n : ℕ}
    (hL : GLAPComponent 3 X L) (hLq : CFSG.Open.IsQuasisimple ↥L) (hbp : b ^ 3 = 1)
    (hT : IsTD4 3 L) (hNI : NonInner 3 b L) (hI : GLAPComponent 3 (L ⊓ cx b) I)
    (hcat : catalogIs (PSimple 3 I) (S10.isG2n n)) : IsChevSimple 2 (PSimple 3 L) := by
  by_contra hnc
  obtain ⟨q, hv, ⟨eS⟩⟩ := td4_index hT
  have hq2 : q.p ≠ 2 := by
    intro h2
    exact hnc (Or.inl ⟨.lie ⟨.trialityD4 q, hv⟩, by simp [onLie, h2], ⟨eS⟩⟩)
  have hb : b ∈ Subgroup.normalizer (L : Set G) := hNI.1
  have hc : Subgroup.center ↥L = ⊥ := center_eq_bot_of_td4 hGA hL hLq q hv eS
  have hinj := chevQuotHom_injective_of_center hL hLq hc
  have hβ3 : indAut 3 L b hb ^ 3 = 1 := by
    show chevAut 3 L ⟨b⁻¹, Subgroup.inv_mem _ hb⟩ ^ 3 = 1
    exact chevAut_pow_eq_one 3 L (Subgroup.inv_mem _ hb) (by rw [inv_pow, hbp, inv_one])
  have hβout : indAut 3 L b hb ∉
      CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple 3 L) := by
    intro h
    exact hNI.2 ((indAut_mem_inner_iff Nat.prime_three hL hb).1 h)
  have hS : catalogIs (PSimple 3 L) (onLie fun | .trialityD4 q => q.p ≠ 2 | _ => False) :=
    ⟨.lie ⟨.trialityD4 q, hv⟩, hq2, ⟨eS⟩⟩
  have hIL : I ≤ L := hI.1.trans inf_le_left
  have hsub : CFSG.Open.IsSubnormal ((I.subgroupOf L).map (chevQuotHom 3 L))
      (FP.fixSub (indAut 3 L b hb)) := by
    rw [fixSub_indAut_eq hb hinj]
    exact CFSG.Open.IsSubnormal.map _ (hI.2.1.comap L.subtype)
  let e : ↥L ≃* PSimple 3 L :=
    MulEquiv.ofBijective (chevQuotHom 3 L) ⟨hinj, chevQuotHom_surjective 3 L⟩
  let ψ : ((I.subgroupOf L).map (chevQuotHom 3 L)) →* PSimple 3 I :=
    (chevQuotHom 3 I).comp ((Subgroup.subgroupOfEquivOfLe hIL).toMonoidHom.comp
      (MulEquiv.subgroupMap e (I.subgroupOf L)).symm.toMonoidHom)
  have hψ : Function.Surjective ψ := by
    refine (chevQuotHom_surjective 3 I).comp ?_
    refine (Subgroup.subgroupOfEquivOfLe hIL).surjective.comp ?_
    exact (MulEquiv.subgroupMap e (I.subgroupOf L)).symm.surjective
  exact hOdd (PSimple 3 L) hS (indAut 3 L b hb) hβ3 hβout ((I.subgroupOf L).map (chevQuotHom 3 L))
    hsub n (PSimple 3 I) hcat ψ hψ

theorem clauseB_of (hGA : CFSG.Open.GriessAllModelsStatement) (hField : G2FieldLayerAt G)
    {X L I : Subgroup G} {b : G} {n : ℕ}
    (hL : GLAPComponent 3 X L) (hLq : CFSG.Open.IsQuasisimple ↥L) (hbp : b ^ 3 = 1)
    (hR : R2Prop 3 b L) (hI : GLAPComponent 3 (L ⊓ cx b) I)
    (hcat : catalogIs (PSimple 3 I) (S10.isG2n n)) (hn2 : n = 2) :
    I ⊓ GLAPPrimeCoreOf 3 L = ⊥ := by
  subst hn2
  have hc : Subgroup.center ↥L = ⊥ := by
    rcases hR with hF | ⟨-, hT, hNI⟩
    · exact center_eq_bot_of_G2_six hGA hL hLq (hField X L I b hL hLq hbp hF hI hcat)
    · obtain ⟨q, hv, ⟨e⟩⟩ := td4_index hT
      exact center_eq_bot_of_td4 hGA hL hLq q hv e
  rw [glaPrimeCoreOf_eq_bot_of_injective (chevQuotHom_injective_of_center hL hLq hc), inf_bot_eq]

theorem multaRes_of_facts (hGA : CFSG.Open.GriessAllModelsStatement) (hOdd : TD4OddNoG2Layer)
    (hField : G2FieldLayerAt G) : MultAG2Residual G := by
  refine ⟨?_, ?_⟩
  · intro X L b n hL hLq hbp hT hNI hI hcat
    exact clauseA_of hGA hOdd hL hLq hbp hT hNI hI hcat
  · intro X L b n hL hLq hbp hR hI hcat hn2
    exact clauseB_of hGA hField hL hLq hbp hR hI hcat hn2

end CFSG.LocalAnalysis.GLTheoremA.CatB.KMultA1

end
