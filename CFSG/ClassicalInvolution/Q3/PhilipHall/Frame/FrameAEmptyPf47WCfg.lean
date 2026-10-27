module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf47WStruct
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf43Sigma
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf45M12Lift
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm3QuotRows

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Asc77.T3Core
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

section Upper

variable {T : Type} [Group T]

private theorem mem_normalizer_closure_of {S : Set T} {g : T} (h : ∀ x, x ∈ S ↔ g * x * g⁻¹ ∈ S) :
    g ∈ Subgroup.normalizer ((Subgroup.closure S : Subgroup T) : Set T) := by
  rw [mem_normalizer_iff_conjSub_eq]
  show (Subgroup.closure S).map (MulAut.conj g).toMonoidHom = Subgroup.closure S
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (h x).mp hx
  · intro hy
    refine ⟨g⁻¹ * y * g, (h _).mpr ?_, ?_⟩
    · rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y by group]
    · show g * (g⁻¹ * y * g) * g⁻¹ = y
      group

theorem oUpperTwo_le (X : Subgroup T) : oUpperTwo X ≤ X :=
  (Subgroup.closure_le X).mpr fun _ hx => hx.1

theorem oUpperTwoPrime_le (X : Subgroup T) : oUpperTwoPrime X ≤ X :=
  (Subgroup.closure_le X).mpr fun _ hx => hx.1

theorem normalizer_le_normalizer_oUpperTwo (X : Subgroup T) :
    Subgroup.normalizer (X : Set T) ≤ Subgroup.normalizer (oUpperTwo X : Set T) := by
  intro g hg
  refine mem_normalizer_closure_of fun x => ?_
  have hX := Subgroup.mem_normalizer_iff.mp hg x
  have ho : orderOf (g * x * g⁻¹) = orderOf x := by
    rw [show g * x * g⁻¹ = MulAut.conj g x from rfl, MulEquiv.orderOf_eq]
  exact ⟨fun ⟨hx, h⟩ => ⟨hX.mp hx, ho ▸ h⟩, fun ⟨hx, h⟩ => ⟨hX.mpr hx, ho ▸ h⟩⟩

theorem normalizer_le_normalizer_oUpperTwoPrime (X : Subgroup T) :
    Subgroup.normalizer (X : Set T) ≤ Subgroup.normalizer (oUpperTwoPrime X : Set T) := by
  intro g hg
  refine mem_normalizer_closure_of fun x => ?_
  have hX := Subgroup.mem_normalizer_iff.mp hg x
  have hp : ∀ k : ℕ, x ^ (2 ^ k) = 1 ↔ (g * x * g⁻¹) ^ (2 ^ k) = 1 := fun k => by
    rw [conj_pow, conj_eq_one_iff]
  exact ⟨fun ⟨hx, k, hk⟩ => ⟨hX.mp hx, k, (hp k).mp hk⟩,
    fun ⟨hx, k, hk⟩ => ⟨hX.mpr hx, k, (hp k).mpr hk⟩⟩

theorem oUpperTwoPrime_idem (X : Subgroup T) : oUpperTwoPrime (oUpperTwoPrime X) = oUpperTwoPrime X :=
  le_antisymm (Subgroup.closure_mono fun _ hx => ⟨oUpperTwoPrime_le X hx.1, hx.2⟩)
    ((Subgroup.closure_le _).mpr fun _ hx => Subgroup.subset_closure ⟨Subgroup.subset_closure hx, hx.2⟩)

theorem map_oUpperTwo {A B : Type} [Group A] [Group B] [Finite A] (f : A →* B) (X : Subgroup A) :
    (oUpperTwo X).map f = oUpperTwo (X.map f) := by
  rw [oUpperTwo, oUpperTwo, MonoidHom.map_closure]
  apply le_antisymm
  · refine Subgroup.closure_mono ?_
    rintro _ ⟨x, ⟨hx, ho⟩, rfl⟩
    exact ⟨Subgroup.mem_map_of_mem f hx, ho.of_dvd_nat (orderOf_map_dvd f x)⟩
  · refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨⟨x, hx, rfl⟩, ho⟩
    obtain ⟨a, m, hm, hxm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    have hcop : (2 ^ a).Coprime (orderOf (f x)) :=
      Nat.Coprime.pow_left a (Odd.coprime_two_right ho).symm
    obtain ⟨c, hc⟩ := exists_pow_eq_self_of_coprime hcop
    have h1 : orderOf (x ^ 2 ^ a) = m := by
      rw [orderOf_pow_of_dvd (by positivity) (hxm ▸ dvd_mul_right _ _), hxm,
        Nat.mul_div_cancel_left m (by positivity)]
    refine Subgroup.subset_closure ⟨(x ^ 2 ^ a) ^ c, ⟨X.pow_mem (X.pow_mem hx _) _, ?_⟩, ?_⟩
    · exact (h1 ▸ hm).of_dvd_nat (orderOf_pow_dvd c)
    · rw [map_pow, map_pow, hc]

theorem map_oUpperTwoPrime {A B : Type} [Group A] [Group B] [Finite A] (f : A →* B)
    (X : Subgroup A) : (oUpperTwoPrime X).map f = oUpperTwoPrime (X.map f) := by
  rw [oUpperTwoPrime, oUpperTwoPrime, MonoidHom.map_closure]
  apply le_antisymm
  · refine Subgroup.closure_mono ?_
    rintro _ ⟨x, ⟨hx, k, hk⟩, rfl⟩
    exact ⟨Subgroup.mem_map_of_mem f hx, k, by rw [← map_pow, hk, map_one]⟩
  · refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨⟨x, hx, rfl⟩, k, hk⟩
    obtain ⟨a, m, hm, hxm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    have hcop : m.Coprime (orderOf (f x)) :=
      Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hk)
        (Nat.Coprime.pow_right k (Odd.coprime_two_right hm))
    obtain ⟨c, hc⟩ := exists_pow_eq_self_of_coprime hcop
    refine Subgroup.subset_closure ⟨(x ^ m) ^ c, ⟨X.pow_mem (X.pow_mem hx _) _, a, ?_⟩, ?_⟩
    · rw [← pow_mul, ← pow_mul, show m * (c * 2 ^ a) = 2 ^ a * m * c by ring, pow_mul, ← hxm,
        pow_orderOf_eq_one, one_pow]
    · rw [map_pow, map_pow, hc]

end Upper

section Defs

variable {T : Type} [Group T]

@[expose] def wQ (K : Subgroup T) : Subgroup T := oUpperTwoPrime (oUpperTwo (firstFactor K))

theorem wQ_le (K : Subgroup T) : wQ K ≤ firstFactor K :=
  (oUpperTwoPrime_le _).trans (oUpperTwo_le _)

theorem normalizer_le_normalizer_wQ (K : Subgroup T) :
    Subgroup.normalizer (firstFactor K : Set T) ≤ Subgroup.normalizer (wQ K : Set T) :=
  fun _ hg => normalizer_le_normalizer_oUpperTwoPrime _ (normalizer_le_normalizer_oUpperTwo _ hg)

theorem oUpperTwoPrime_wQ (K : Subgroup T) : oUpperTwoPrime (wQ K) = wQ K :=
  oUpperTwoPrime_idem _

end Defs

section Cfg

structure WStd {T : Type} [Group T] (K : Subgroup T) (z : T) (J : Subgroup T) (zJ : T)
    (H : Subgroup T) : Prop extends FrameStd K z J zJ where
  hH : omegaGen (aStar (CoreAssembly.conjClass K) K) = H
  row : Thm3RowW (restrictFamily (CoreAssembly.conjClass K) H) (⊤ : Subgroup ↥H)

structure WCfg {T : Type} [Group T] [Finite T] (K : Subgroup T) (z : T) (J : Subgroup T)
    (zJ : T) (H S : Subgroup T) : Prop extends FrameCfg K z J zJ S where
  hH : omegaGen (aStar (CoreAssembly.conjClass K) K) = H
  row : Thm3RowW (restrictFamily (CoreAssembly.conjClass K) H) (⊤ : Subgroup ↥H)
  ht : Nonempty (SecQuot (firstFactor K) ≃* G192)

end Cfg

section SecAux

private theorem w_le_oddCore_of_odd {X : Type} [Group X] {N : Subgroup X} [N.Normal]
    (h : Odd (Nat.card N)) : N ≤ classicalInvolutionOddCore X :=
  le_sSup ⟨‹N.Normal›, h⟩

private theorem w_odd_card_oddCore (X : Type) [Group X] [Finite X] :
    Odd (Nat.card (classicalInvolutionOddCore X)) :=
  CFSG.ComponentClassification.OddCore.odd_card X

private theorem w_secQuot_equiv_of_sup {A X : Type} [Group A] [Group X] [Finite X]
    (ι : A →* X) (hι : Function.Injective ι) (N : Subgroup X) [N.Normal]
    (hN : Odd (Nat.card N)) (hsup : ι.range ⊔ N = ⊤) :
    Nonempty ((A ⧸ classicalInvolutionOddCore A) ≃* (X ⧸ classicalInvolutionOddCore X)) := by
  haveI : Finite A := Finite.of_injective ι hι
  have hNO : N ≤ classicalInvolutionOddCore X := w_le_oddCore_of_odd hN
  let ψ : A →* X ⧸ classicalInvolutionOddCore X :=
    (QuotientGroup.mk' (classicalInvolutionOddCore X)).comp ι
  have hsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have hx : x ∈ ι.range ⊔ N := by
      rw [hsup]
      exact Subgroup.mem_top x
    obtain ⟨g, hg, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
    obtain ⟨a, rfl⟩ := hg
    refine ⟨a, ?_⟩
    show (QuotientGroup.mk' (classicalInvolutionOddCore X)) (ι a) =
      (QuotientGroup.mk' (classicalInvolutionOddCore X)) (ι a * n)
    have h1 : (QuotientGroup.mk' (classicalInvolutionOddCore X)) n = 1 :=
      (QuotientGroup.eq_one_iff n).mpr (hNO hn)
    rw [map_mul, h1, mul_one]
  have hker : ψ.ker = classicalInvolutionOddCore A := by
    ext a
    rw [MonoidHom.mem_ker]
    constructor
    · intro ha
      have h1 : ι a ∈ classicalInvolutionOddCore X := (QuotientGroup.eq_one_iff _).mp ha
      have hPodd : Odd (Nat.card ((classicalInvolutionOddCore X).comap ι)) := by
        have e1 : Nat.card (((classicalInvolutionOddCore X).comap ι).map ι) =
            Nat.card ((classicalInvolutionOddCore X).comap ι) :=
          Subgroup.card_map_of_injective hι
        have e2 : Nat.card (((classicalInvolutionOddCore X).comap ι).map ι) ∣
            Nat.card (classicalInvolutionOddCore X) :=
          Subgroup.card_dvd_of_le (Subgroup.map_comap_le ι _)
        rw [← e1]
        exact (w_odd_card_oddCore X).of_dvd_nat e2
      exact w_le_oddCore_of_odd hPodd h1
    · intro ha
      set B : Subgroup X := (classicalInvolutionOddCore A).map ι with hB
      have hBodd : Odd (Nat.card B) := by
        rw [hB, Subgroup.card_map_of_injective hι]
        exact w_odd_card_oddCore A
      have hDodd : Odd (Nat.card (N ⊔ B : Subgroup X)) :=
        CFSG.ComponentClassification.OddCore.odd_card_sup N B hN hBodd
      have hconj : ∀ g ∈ ι.range, ∀ d ∈ N ⊔ B, g * d * g⁻¹ ∈ N ⊔ B := by
        intro g hg d hd
        obtain ⟨n', hn', b, hb, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hd
        obtain ⟨a₀, rfl⟩ := hg
        obtain ⟨b', hb', rfl⟩ := hb
        have e : ι a₀ * (n' * ι b') * (ι a₀)⁻¹ =
            (ι a₀ * n' * (ι a₀)⁻¹) * ι (a₀ * b' * a₀⁻¹) := by
          rw [map_mul, map_mul, map_inv]
          group
        rw [e]
        exact (N ⊔ B).mul_mem (Subgroup.mem_sup_left (‹N.Normal›.conj_mem n' hn' _))
          (Subgroup.mem_sup_right ⟨a₀ * b' * a₀⁻¹,
            (inferInstance : (classicalInvolutionOddCore A).Normal).conj_mem b' hb' a₀, rfl⟩)
      have hDnormal : (N ⊔ B).Normal := by
        refine ⟨fun d hd x => ?_⟩
        have hx : x ∈ ι.range ⊔ N := by
          rw [hsup]
          exact Subgroup.mem_top x
        obtain ⟨g, hg, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
        have h1 : n * d * n⁻¹ ∈ N ⊔ B :=
          (N ⊔ B).mul_mem ((N ⊔ B).mul_mem (Subgroup.mem_sup_left hn) hd)
            ((N ⊔ B).inv_mem (Subgroup.mem_sup_left hn))
        have h2 := hconj g hg _ h1
        have e : g * n * d * (g * n)⁻¹ = g * (n * d * n⁻¹) * g⁻¹ := by group
        rw [e]
        exact h2
      have hDle : N ⊔ B ≤ classicalInvolutionOddCore X := w_le_oddCore_of_odd hDodd
      exact (QuotientGroup.eq_one_iff _).mpr (hDle (Subgroup.mem_sup_right ⟨a, ha, rfl⟩))
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj)⟩

private theorem w_omegaGen_aStar_restrict {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    (hΩ : HypOmegaGen Ω) {K H : Subgroup G} (hH : omegaGen (aStar Ω K) = H) :
    omegaGen (aStar (restrictFamily Ω H) (K.subgroupOf H)) = ⊤ := by
  have hMH : ∀ M ∈ aStar Ω K, M ≤ H := fun M hM => hH ▸ le_omegaGen hM
  have key : ∀ M ∈ aStar Ω K, M.subgroupOf H ∈ aStar (restrictFamily Ω H) (K.subgroupOf H) := by
    intro M hM
    induction hM with
    | refl => exact Relation.ReflTransGen.refl
    | tail hab hbc ih =>
      rename_i b c
      have hbH : b ≤ H := hMH b hab
      have hcH : c ≤ H := hMH c (hab.tail hbc)
      refine ih.tail ?_
      obtain ⟨hcΩ, hA | hA | ⟨htw, hne⟩⟩ := hbc
      · obtain ⟨zb, zc, hv⟩ := hA
        exact ⟨subgroupOf_mem_restrictFamily hcΩ hcH,
          Or.inl ⟨_, _, aViol_restrict_gen hΩ hbH hcH hv⟩⟩
      · obtain ⟨zc, zb, hv⟩ := hA
        exact ⟨subgroupOf_mem_restrictFamily hcΩ hcH,
          Or.inr (Or.inl ⟨_, _, aViol_restrict_gen hΩ hcH hbH hv⟩)⟩
      · exact ⟨subgroupOf_mem_restrictFamily hcΩ hcH,
          Or.inr (Or.inr ⟨twinSet_subgroupOf hbH hcH htw,
            subgroupOf_ne_of_ne hbH hcH hne⟩)⟩
  have hle : H ≤ (omegaGen (aStar (restrictFamily Ω H) (K.subgroupOf H))).map H.subtype := by
    refine hH.symm.le.trans (iSup₂_le fun M hM => ?_)
    have h1 : M.subgroupOf H ≤ omegaGen (aStar (restrictFamily Ω H) (K.subgroupOf H)) :=
      le_omegaGen (key M hM)
    have h2 := Subgroup.map_mono (f := H.subtype) h1
    rwa [Subgroup.map_subgroupOf_eq_of_le (hMH M hM)] at h2
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.map_top, Subgroup.range_subtype]
  exact le_antisymm (Subgroup.map_subtype_le _) hle

theorem w_secQuot_iso_of_quot {Y : Type} [Group Y] [Finite Y] (hQ : Thm3A.Thm3RGroupQuotG Y)
    {Δ : Set (Subgroup Y)} (hΔ : TypeRHyp Δ) {K : Subgroup Y} (hK : K ∈ Δ) (hA : ¬ AEmpty Δ K)
    (hgen : omegaGen (aStar Δ K) = ⊤) (hrow : Thm3RowW Δ (⊤ : Subgroup Y)) :
    Nonempty (SecQuot (⊤ : Subgroup Y) ≃* G192) := by
  have hN : Odd (Nat.card (classicalInvolutionOddCore Y)) :=
    CFSG.ComponentClassification.OddCore.odd_card Y
  have hmap : (⊤ : Subgroup Y).map (QuotientGroup.mk' (classicalInvolutionOddCore Y)) = ⊤ :=
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  have hgen' : omegaGen (aStar (oddQuotientFamily Δ)
      (K.map (QuotientGroup.mk' (classicalInvolutionOddCore Y)))) = ⊤ := by
    have h := Thm3Quot.omegaGen_aStar_map hΔ.hyp hN hK
    rw [hgen, hmap] at h
    exact h.symm
  have hrow' : Thm3RowW (oddQuotientFamily Δ)
      (⊤ : Subgroup (Y ⧸ classicalInvolutionOddCore Y)) := by
    have h := (Thm3Quot.thm3RowW_map_iff hN Δ le_top).mpr hrow
    rw [hmap] at h
    exact h
  obtain ⟨f⟩ := w_secQuot_iso (typeRHyp_oddQuot hΔ hN) (map_mem_quotFamily hK)
    (Thm3Quot.not_aEmpty_map hΔ.hyp hN hK hA) hgen' (hQ Δ hΔ K hK hA).1 hrow'
  obtain ⟨e⟩ : Nonempty (SecQuot (⊤ : Subgroup Y) ≃*
      SecQuot (⊤ : Subgroup (Y ⧸ classicalInvolutionOddCore Y))) := by
    rw [← hmap]
    exact ⟨Thm3Quot.secQuotMapEquiv hN ⊤⟩
  exact ⟨e.trans f⟩

theorem w_mk_inclusion_injective {G : Type} [Group G] [Finite G] {Ht R : Subgroup G} (hRHt : R ≤ Ht)
    (hR : IsPGroup 2 R) :
    Function.Injective ((QuotientGroup.mk' (classicalInvolutionOddCore ↥Ht)).comp
      (Subgroup.inclusion hRHt)) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have h1 : Subgroup.inclusion hRHt a ∈ classicalInvolutionOddCore ↥Ht :=
    (QuotientGroup.eq_one_iff _).mp ha
  obtain ⟨k, hk⟩ := hR a
  have hodd : Odd (orderOf (Subgroup.inclusion hRHt a)) :=
    (CFSG.ComponentClassification.OddCore.odd_card ↥Ht).of_dvd_nat
      (Subgroup.orderOf_dvd_natCard _ h1)
  have hk' : (Subgroup.inclusion hRHt a) ^ 2 ^ k = 1 := by rw [← map_pow, hk, map_one]
  have h3 : Subgroup.inclusion hRHt a = 1 :=
    orderOf_eq_one_iff.mp (eq_one_of_odd_of_dvd_two_pow hodd (orderOf_dvd_of_pow_eq_one hk'))
  exact Subgroup.inclusion_injective hRHt (by rw [h3, map_one])

end SecAux

section Exists

variable {T : Type} [Group T] [Finite T] {K : Subgroup T} {z : T} {J : Subgroup T} {zJ : T}
  {H : Subgroup T}

theorem w_secQuot_top_iso (hs : WStd K z J zJ H) :
    Nonempty (SecQuot (⊤ : Subgroup ↥H) ≃* G192) := by
  have hΩg : HypOmegaGen (CoreAssembly.conjClass K) := hs.datum.hyp
  have hK : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have htrans : ∀ M ∈ CoreAssembly.conjClass K, ∃ g : T, conjSub g K = M := by
    intro M hM
    obtain ⟨g, rfl⟩ := hM
    exact ⟨g, rfl⟩
  have hKS : K ∈ aStar (CoreAssembly.conjClass K) K := Relation.ReflTransGen.refl
  have hJS : J ∈ aStar (CoreAssembly.conjClass K) K :=
    Relation.ReflTransGen.single ⟨hs.viol.mem, Or.inl ⟨z, zJ, hs.viol⟩⟩
  have hKH : K ≤ H := hs.hH ▸ le_omegaGen hKS
  have hJH : J ≤ H := hs.hH ▸ le_omegaGen hJS
  have hHtop : H ≠ ⊤ := fun h =>
    hs.ne (aStar_eq_of_omegaGen_eq_top hΩg.conjInvariant hK htrans (hs.hH.trans h))
  have hlt : Nat.card ↥H < Nat.card T :=
    lt_of_le_of_ne (Subgroup.card_le_card_group H)
      (fun h => hHtop ((Subgroup.card_eq_iff_eq_top H).mp h))
  have hΔ : TypeRHyp (restrictFamily (CoreAssembly.conjClass K) H) :=
    (typeRHyp_of_datum hs.datum).restrict H
  have hKΔ : K.subgroupOf H ∈ restrictFamily (CoreAssembly.conjClass K) H :=
    subgroupOf_mem_restrictFamily hK hKH
  have hnA : ¬ AEmpty (restrictFamily (CoreAssembly.conjClass K) H) (K.subgroupOf H) :=
    not_aEmpty_iff.mpr ⟨J.subgroupOf H, _, _, aViol_restrict_gen hΩg hKH hJH hs.viol⟩
  exact w_secQuot_iso_of_quot (Thm3A.thm3RGroupQuotG_of_belowG hs.below hlt) hΔ hKΔ hnA
    (w_omegaGen_aStar_restrict hΩg hs.hH) hs.row

theorem w_ht_iso (hs : WStd K z J zJ H) :
    Nonempty (SecQuot (firstFactor K) ≃* G192) := by
  have hΩ : HypOmegaGen (CoreAssembly.conjClass K) := hs.datum.hyp
  have hHle : H ≤ firstFactor K := by
    rw [← hs.hH]
    exact le_sup_left
  have hNle : oddCoreOf (sigmaGen K) ≤ firstFactor K := le_sup_right
  have hHtsup : H ⊔ oddCoreOf (sigmaGen K) = firstFactor K := by
    rw [← hs.hH]
    rfl
  have hHs : firstFactor K ≤ sigmaGen K := firstFactor_le_sigmaGen hΩ
  have hnorm : firstFactor K ≤ Subgroup.normalizer (oddCoreOf (sigmaGen K) : Set T) := fun x hx =>
    mem_normalizer_oddCoreOf_of_mem_normalizer (Subgroup.le_normalizer (hHs hx))
  haveI : ((oddCoreOf (sigmaGen K)).subgroupOf (firstFactor K)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNle).mpr hnorm
  have hodd : Odd (Nat.card ((oddCoreOf (sigmaGen K)).subgroupOf (firstFactor K))) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNle).toEquiv]
    exact oddCoreOf_odd_natCard _
  let ι : ↥(⊤ : Subgroup ↥H) →* ↥(firstFactor K) :=
    (Subgroup.inclusion hHle).comp (⊤ : Subgroup ↥H).subtype
  have hι : Function.Injective ι :=
    (Subgroup.inclusion_injective hHle).comp (⊤ : Subgroup ↥H).subtype_injective
  have hrange : ι.range = H.subgroupOf (firstFactor K) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, Subgroup.map_top, Subgroup.inclusion_range]
  have hsup : ι.range ⊔ (oddCoreOf (sigmaGen K)).subgroupOf (firstFactor K) = ⊤ := by
    rw [hrange, ← Subgroup.subgroupOf_sup hHle hNle, hHtsup, Subgroup.subgroupOf_self]
  obtain ⟨e⟩ := w_secQuot_equiv_of_sup ι hι _ hodd hsup
  obtain ⟨f⟩ := w_secQuot_top_iso hs
  exact ⟨e.symm.trans f⟩

theorem w_cfg_exists (hs : WStd K z J zJ H) : ∃ S : Subgroup T, WCfg K z J zJ H S := by
  obtain ⟨S, cfg⟩ := frameCfg_exists hs.toFrameStd
  exact ⟨S, { toFrameCfg := cfg, hH := hs.hH, row := hs.row, ht := w_ht_iso hs }⟩

end Exists

namespace WCfg

variable {T : Type} [Group T] [Finite T] {K : Subgroup T} {z : T} {J : Subgroup T} {zJ : T}
  {H S : Subgroup T}

theorem K_le_ht (_cfg : WCfg K z J zJ H S) : K ≤ firstFactor K :=
  (le_omegaGen (Relation.ReflTransGen.refl : K ∈ aStar (CoreAssembly.conjClass K) K)).trans
    le_sup_left

theorem z_mem_ht (cfg : WCfg K z J zJ H S) : z ∈ firstFactor K :=
  cfg.K_le_ht cfg.datum.unique.mem

theorem center_eq_bot (cfg : WCfg K z J zJ H S) : Subgroup.center (SecQuot (firstFactor K)) = ⊥ := by
  obtain ⟨e⟩ := cfg.ht
  have h := center_map_equiv e
  rw [W192.w192_center_eq_bot] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h

theorem mul_mem_inner (cfg : WCfg K z J zJ H S) {φ ψ : MulAut (SecQuot (firstFactor K))}
    (hφ : φ ∉ inner (SecQuot (firstFactor K))) (hψ : ψ ∉ inner (SecQuot (firstFactor K))) :
    φ * ψ ∈ inner (SecQuot (firstFactor K)) := by
  obtain ⟨e⟩ := cfg.ht
  set c := MulAut.congr e with hc
  have hmap := inner_map_congr e
  have key : ∀ α : MulAut (SecQuot (firstFactor K)),
      α ∈ inner (SecQuot (firstFactor K)) ↔ c α ∈ inner G192 := by
    intro α
    rw [← hmap]
    constructor
    · intro h
      exact Subgroup.mem_map_of_mem _ h
    · rintro ⟨β, hβ, hβα⟩
      have : β = α := c.injective hβα
      exact this ▸ hβ
  rw [key] at hφ hψ ⊢
  rw [map_mul]
  exact W192.w192_mul_mem_inner hφ hψ

theorem involution_cent_order_four (cfg : WCfg K z J zJ H S) {P : Subgroup (SecQuot (firstFactor K))}
    (hP : Nonempty (↥P ≃* QuaternionGroup 2)) {y : SecQuot (firstFactor K)} (hy : y * y = 1) :
    ∃ x k : SecQuot (firstFactor K), k ∈ P ∧ orderOf k = 4 ∧ y * (x * k * x⁻¹) = x * k * x⁻¹ * y := by
  obtain ⟨e⟩ := cfg.ht
  obtain ⟨f⟩ := hP
  have hP' : Nonempty (↥(P.map e.toMonoidHom) ≃* QuaternionGroup 2) :=
    ⟨(P.equivMapOfInjective e.toMonoidHom e.injective).symm.trans f⟩
  obtain ⟨x, k, hk, hk4, hc⟩ :=
    W192.w192_involution_cent_order_four hP' (y := e y) (by rw [← map_mul, hy, map_one])
  obtain ⟨k₀, hk₀, rfl⟩ := hk
  refine ⟨e.symm x, k₀, hk₀, ?_, ?_⟩
  · rw [← MulEquiv.orderOf_eq e]
    exact hk4
  · apply e.injective
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hc

theorem map_Q (cfg : WCfg K z J zJ H S) (e : SecQuot (firstFactor K) ≃* G192) :
    (((wQ K).subgroupOf (firstFactor K)).map
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(firstFactor K)))).map e.toMonoidHom =
      W192.w192W := by
  have hsub : (wQ K).subgroupOf (firstFactor K) =
      oUpperTwoPrime (oUpperTwo (⊤ : Subgroup ↥(firstFactor K))) := by
    apply Subgroup.map_injective (firstFactor K).subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le (wQ_le K), map_oUpperTwoPrime, map_oUpperTwo,
      Subgroup.map_top, Subgroup.range_subtype]
    rfl
  rw [hsub, map_oUpperTwoPrime, map_oUpperTwo, map_oUpperTwoPrime, map_oUpperTwo,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _),
    Subgroup.map_top_of_surjective _ e.surjective]
  exact W192.w192_oUpperTwoPrime_oUpperTwo

theorem mk_mem_W_of_mem_Q (cfg : WCfg K z J zJ H S) (e : SecQuot (firstFactor K) ≃* G192) {x : T}
    (hx : x ∈ wQ K) :
    e ((⟨x, wQ_le K hx⟩ : ↥(firstFactor K)) : SecQuot (firstFactor K)) ∈ W192.w192W := by
  rw [← cfg.map_Q e]
  exact Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx))

theorem z_mem_Q (cfg : WCfg K z J zJ H S) : z ∈ wQ K := by
  obtain ⟨e⟩ := cfg.ht
  have hz := cfg.datum.unique
  have hzHt := cfg.z_mem_ht
  obtain ⟨R₀, hR₀, k, hk, -, hkk⟩ := exists_orderOf_four_of_datum cfg.datum
  have hzR₀ : z ∈ R₀ := hkk ▸ R₀.mul_mem hk hk
  have hR₀Ht : R₀ ≤ firstFactor K := hR₀.1.trans cfg.K_le_ht
  set φ : ↥R₀ →* G192 := e.toMonoidHom.comp
    ((QuotientGroup.mk' (classicalInvolutionOddCore ↥(firstFactor K))).comp
      (Subgroup.inclusion hR₀Ht)) with hφ
  have hφinj : Function.Injective φ := e.injective.comp (w_mk_inclusion_injective hR₀Ht hR₀.2.1)
  obtain ⟨e8⟩ := cfg.datum.quat R₀ hR₀
  have hP : Nonempty (↥φ.range ≃* QuaternionGroup 2) :=
    ⟨(MonoidHom.ofInjective hφinj).symm.trans e8⟩
  have hzz : φ ⟨z, hzR₀⟩ * φ ⟨z, hzR₀⟩ = 1 := by
    rw [← map_mul, show (⟨z, hzR₀⟩ : ↥R₀) * ⟨z, hzR₀⟩ = 1 from Subtype.ext hz.sq, map_one]
  have hzW : φ ⟨z, hzR₀⟩ ∈ W192.w192W := W192.w192_q8_inv_mem hP ⟨_, rfl⟩ hzz
  rw [← cfg.map_Q e] at hzW
  obtain ⟨b, ⟨a, ha, rfl⟩, hb⟩ := hzW
  have hab : (QuotientGroup.mk' (classicalInvolutionOddCore ↥(firstFactor K))) a =
      ((⟨z, hzHt⟩ : ↥(firstFactor K)) : SecQuot (firstFactor K)) := e.injective hb
  have haQ : (a : T) ∈ wQ K := Subgroup.mem_subgroupOf.mp ha
  have hO : (a : T)⁻¹ * z ∈ oddCoreOf (firstFactor K) := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq] at hab
    exact mem_oddCoreOf_iff.mpr ⟨(a⁻¹ * ⟨z, hzHt⟩ : ↥(firstFactor K)).2, hab⟩
  have hOle : oddCoreOf (firstFactor K) ≤ oUpperTwo (firstFactor K) := fun y hy =>
    Subgroup.subset_closure ⟨oddCoreOf_le_self _ hy,
      (oddCoreOf_odd_natCard _).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hy)⟩
  have hzO2 : z ∈ oUpperTwo (firstFactor K) := by
    have := (oUpperTwo (firstFactor K)).mul_mem (oUpperTwoPrime_le _ haQ) (hOle hO)
    rwa [mul_inv_cancel_left] at this
  exact Subgroup.subset_closure ⟨hzO2, 1, by rw [pow_one, pow_two]; exact hz.sq⟩

theorem Q_conj (cfg : WCfg K z J zJ H S) {x : T} (hx : x ∈ wQ K) (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    ∃ l ∈ firstFactor K, l⁻¹ * z * l = x := by
  obtain ⟨e⟩ := cfg.ht
  have hz := cfg.datum.unique
  have hzQ := cfg.z_mem_Q
  have hxHt : x ∈ firstFactor K := wQ_le K hx
  have hzHt : z ∈ firstFactor K := wQ_le K hzQ
  have hxW := cfg.mk_mem_W_of_mem_Q e hx
  have hzW := cfg.mk_mem_W_of_mem_Q e hzQ
  have hinv : ∀ (y : T) (hy : y ∈ firstFactor K), y * y = 1 → y ≠ 1 →
      e ((⟨y, hy⟩ : ↥(firstFactor K)) : SecQuot (firstFactor K)) *
        e ((⟨y, hy⟩ : ↥(firstFactor K)) : SecQuot (firstFactor K)) = 1 ∧
      e ((⟨y, hy⟩ : ↥(firstFactor K)) : SecQuot (firstFactor K)) ≠ 1 := by
    intro y hy hy2 hy1
    refine ⟨?_, ?_⟩
    · rw [← map_mul, ← QuotientGroup.mk_mul,
        show (⟨y, hy⟩ : ↥(firstFactor K)) * ⟨y, hy⟩ = 1 from Subtype.ext hy2, QuotientGroup.mk_one,
        map_one]
    · rw [Ne, map_eq_one_iff _ e.injective]
      exact mk_ne_one_of_mul_self hy hy2 hy1
  obtain ⟨hx2', hx1'⟩ := hinv x hxHt hx2 hx1
  obtain ⟨hz2', hz1'⟩ := hinv z hzHt hz.sq hz.ne_one
  obtain ⟨g, hg⟩ := W192.w192_W_inv_conj hzW hxW hz2' hx2' hz1' hx1'
  obtain ⟨l, hl, hlz⟩ := exists_conj_of_mk_conj hzHt hxHt hz.sq hx2 ⟨e.symm g, by
    apply e.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hg.symm⟩
  exact ⟨l⁻¹, (firstFactor K).inv_mem hl, by rw [inv_inv]; exact hlz⟩

theorem sylow_Q (cfg : WCfg K z J zJ H S) {R : Subgroup T}
    (hR : CFSG.ABGLocalTools.IsSylowOf 2 R (wQ K)) :
    Nonempty (↥R ≃* Multiplicative (ZMod 4 × ZMod 4)) := by
  obtain ⟨e⟩ := cfg.ht
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRQ : R ≤ wQ K := hR.le
  have hRHt : R ≤ firstFactor K := hRQ.trans (wQ_le K)
  set ψ : ↥R →* G192 := e.toMonoidHom.comp
    ((QuotientGroup.mk' (classicalInvolutionOddCore ↥(firstFactor K))).comp
      (Subgroup.inclusion hRHt)) with hψ
  have hψinj : Function.Injective ψ := e.injective.comp (w_mk_inclusion_injective hRHt hR.isPGroup)
  have hψW : ψ.range ≤ W192.w192W := by
    rintro _ ⟨r, rfl⟩
    exact cfg.mk_mem_W_of_mem_Q e (hRQ r.2)
  have hcardW : Nat.card W192.w192W = 16 := by
    rw [Nat.card_congr W192.w192WEquiv.toEquiv, Nat.card_eq_fintype_card]
    rfl
  set χ : ↥(wQ K) →* G192 := e.toMonoidHom.comp
    ((QuotientGroup.mk' (classicalInvolutionOddCore ↥(firstFactor K))).comp
      (Subgroup.inclusion (wQ_le K))) with hχ
  have hχr : χ.range = W192.w192W := by
    rw [hχ, MonoidHom.range_comp, MonoidHom.range_comp, Subgroup.inclusion_range]
    exact cfg.map_Q e
  have h16 : 2 ^ 4 ∣ Nat.card (wQ K) := by
    have := Subgroup.card_range_dvd χ
    rwa [hχr, hcardW] at this
  have hQ0 : Nat.card (wQ K) ≠ 0 := Nat.card_pos.ne'
  have h4 : 4 ≤ (Nat.card (wQ K)).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hQ0).mp h16
  have hRle : Nat.card R ≤ 16 := by
    rw [← hcardW, Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv]
    exact Subgroup.card_le_of_le hψW
  have hRge : 16 ≤ Nat.card R := by
    rw [hR.card_eq]
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (Nat.card (wQ K)).factorization 2 := Nat.pow_le_pow_right (by norm_num) h4
  have hrange : ψ.range = W192.w192W := by
    refine Subgroup.eq_of_le_of_card_ge hψW ?_
    rw [hcardW, ← Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv]
    omega
  exact ⟨(MonoidHom.ofInjective hψinj).trans ((MulEquiv.subgroupCongr hrange).trans W192.w192WEquiv)⟩

theorem normalizer_ht_le (_cfg : WCfg K z J zJ H S) :
    Subgroup.normalizer (firstFactor K : Set T) ≤ Subgroup.normalizer (wQ K : Set T) :=
  normalizer_le_normalizer_wQ K

theorem normalizer_Q_le (cfg : WCfg K z J zJ H S) :
    Subgroup.normalizer (wQ K : Set T) ≤
      sigmaNorm K ⊓ Subgroup.normalizer (firstFactor K : Set T) := by
  have hz := cfg.datum.unique
  have hzQ : z ∈ wQ K := cfg.z_mem_Q
  intro y hy
  have hyz : y * z * y⁻¹ ∈ wQ K := (Subgroup.mem_normalizer_iff.mp hy z).mp hzQ
  have h2 : (y * z * y⁻¹) * (y * z * y⁻¹) = 1 := by
    calc (y * z * y⁻¹) * (y * z * y⁻¹) = y * (z * z) * y⁻¹ := by group
      _ = 1 := by rw [hz.sq]; group
  have h1 : y * z * y⁻¹ ≠ 1 := fun h => hz.ne_one (by
    have := congrArg (fun w => y⁻¹ * w * y) h
    simpa [mul_assoc] using this)
  obtain ⟨l, hl, hly⟩ := cfg.Q_conj hyz h2 h1
  have hcz : l * y ∈ Subgroup.centralizer ({z} : Set T) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc l * y * z = l * (y * z * y⁻¹) * y := by group
      _ = l * (l⁻¹ * z * l) * y := by rw [hly]
      _ = z * (l * y) := by group
  have e : y = l⁻¹ * (l * y) := by group
  rw [e]
  refine Subgroup.mem_inf.mpr ⟨(sigmaNorm K).mul_mem ((sigmaNorm K).inv_mem (cfg.ht_le_sigmaNorm hl))
    (cfg.cz_le hcz), ?_⟩
  exact (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).inv_mem (Subgroup.le_normalizer hl))
    (cfg.cz_le_normalizer_ht hcz)

theorem tight (cfg : WCfg K z J zJ H S) : TightlyEmbedded (wQ K) := by
  have hΩ := cfg.datum.hyp
  refine tightlyEmbedded_of_conj hΩ.conjInvariant (CoreAssembly.mem_conjClass_self K)
    cfg.datum.unique cfg.z_mem_Q (fun g hg => ?_) fun x hx hx2 hx1 => ?_
  · exact normalizer_le_normalizer_wQ K
      (mem_normalizer_firstFactor hg (conjStab_aStar_le_sigmaNorm hΩ hg))
  · obtain ⟨l, hl, hlx⟩ := cfg.Q_conj hx hx2 hx1
    exact ⟨l⁻¹, (conjStab (aStar (CoreAssembly.conjClass K) K)).inv_mem
      (cfg.hs_stab (cfg.ht_le hl)), by simpa using hlx⟩

theorem inv_Qconj (cfg : WCfg K z J zJ H S) {x : T} (hx : x ∉ sigmaNorm K) {f : T}
    (hf : f ∈ rightConjugate (wQ K) x) (hf2 : f * f = 1) (hf1 : f ≠ 1) :
    ∃ w : T, w ∉ sigmaNorm K ∧ f = w⁻¹ * z * w := by
  have hf' : x * f * x⁻¹ ∈ wQ K := (mem_rightConjugate_iff (wQ K) x f).mp hf
  have h2 : (x * f * x⁻¹) * (x * f * x⁻¹) = 1 := by
    calc (x * f * x⁻¹) * (x * f * x⁻¹) = x * (f * f) * x⁻¹ := by group
      _ = 1 := by rw [hf2]; group
  have h1 : x * f * x⁻¹ ≠ 1 := fun h => hf1 (by
    have := congrArg (fun w => x⁻¹ * w * x) h
    simpa [mul_assoc] using this)
  obtain ⟨l, hl, hlf⟩ := cfg.Q_conj hf' h2 h1
  refine ⟨l * x, fun hw => hx ?_, ?_⟩
  · have := (sigmaNorm K).mul_mem ((sigmaNorm K).inv_mem (cfg.ht_le_sigmaNorm hl)) hw
    simpa using this
  · calc f = x⁻¹ * (x * f * x⁻¹) * x := by group
      _ = x⁻¹ * (l⁻¹ * z * l) * x := by rw [hlf]
      _ = (l * x)⁻¹ * z * (l * x) := by group

end WCfg

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
