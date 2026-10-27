module

public import CFSG.ClassicalInvolution.Q3.TL4SepSub

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph

section Family

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem commutes_of_mem_omegaNbr (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ omegaNbr Ω K) : Commutes K J := by
  obtain ⟨hJΩ, hne, hJN⟩ := (mem_omegaNbr_iff hΩ h2).mp hJ
  have hP : IsPGroup 2 ↥(J ⊔ K : Subgroup G) := (h2 J hJΩ).to_sup_of_normal_right' (h2 K hK) hJN
  obtain ⟨P, hPS⟩ := hP.exists_le_sylow
  exact Q3CP.l67Gen G Ω hΩ P K (mem_RSet_of_isPGroup hK (h2 K hK)) J
    (mem_RSet_of_isPGroup hJΩ (h2 J hJΩ)) (le_sup_right.trans hPS) (le_sup_left.trans hPS)
    (Ne.symm hne)

theorem nbrGen_le_centralizer (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J) {K : Subgroup G}
    (hK : K ∈ Ω) : nbrGen (nbrAdj Ω) K ≤ Subgroup.centralizer (K : Set G) :=
  nbrGen_le fun _ hJ y hy => Subgroup.mem_centralizer_iff.mpr fun x hx =>
    commutes_of_mem_omegaNbr hΩ h2 hK hJ.2 x hx y hy

omit [Finite G] in
theorem conj_mem_nbrGen (hΩ : HypOmegaGen Ω) {K : Subgroup G} {c : G}
    (hc : c ∈ Subgroup.normalizer (K : Set G)) {x : G} (hx : x ∈ nbrGen (nbrAdj Ω) K) :
    c * x * c⁻¹ ∈ nbrGen (nbrAdj Ω) K := by
  have hcK : conjSub c K = K := conjSub_eq_of_mem_normalizer hc
  have hle : nbrGen (nbrAdj Ω) K ≤ conjSub c⁻¹ (nbrGen (nbrAdj Ω) K) := by
    refine nbrGen_le fun J hJ => ?_
    have h1 : nbrAdj Ω K (conjSub c J) := by
      refine ⟨hJ.1, ?_⟩
      have := Asc77.omegaNbr_conj hΩ.conjInvariant hJ.2 c
      rwa [hcK] at this
    have h2 := conjSub_mono (n := c⁻¹) (le_nbrGen h1)
    rwa [conjSub_inv_conjSub] at h2
  have h3 := hle hx
  rwa [mem_conjSub_iff, inv_inv] at h3

theorem oddCore_eq_bot_of_le_centralizer {H : Subgroup G} {z : G}
    (hHz : H ≤ Subgroup.centralizer ({z} : Set G))
    (hn : ∀ c ∈ Subgroup.centralizer ({z} : Set G), c ∈ Subgroup.normalizer (H : Set G))
    (hO : TightOddCent z) : classicalInvolutionOddCore ↥H = ⊥ := by
  have hle : oddCoreImg H ≤ oddCoreImg (Subgroup.centralizer ({z} : Set G)) :=
    TC.le_oddCoreImg_of_normalizes ((oddCoreImg_le H).trans hHz)
      (fun e he _ ho => conj_mem_oddCoreImg (hn e he) ho) (odd_natCard_oddCoreImg H)
  rw [eq_bot_iff]
  intro x hx
  have h1 : (x : G) ∈ oddCoreImg H := ⟨x, hx, rfl⟩
  have h2 := hle h1
  rw [show oddCoreImg (Subgroup.centralizer ({z} : Set G)) = ⊥ from hO, Subgroup.mem_bot] at h2
  exact Subgroup.mem_bot.mpr (Subtype.ext h2)

end Family

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem tightOddCent_conj (hO : TightOddCent t) (g : Y) : TightOddCent (g * t * g⁻¹) := by
  set C := Subgroup.centralizer ({g * t * g⁻¹} : Set Y)
  set N := oddCoreImg C
  have hmem : ∀ x ∈ C, g⁻¹ * x * g ∈ Subgroup.centralizer ({t} : Set Y) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    calc g⁻¹ * x * g * t = g⁻¹ * (x * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * x) * g := by rw [hx]
      _ = t * (g⁻¹ * x * g) := by group
  have hle : conjSub g⁻¹ N ≤ oddCoreImg (Subgroup.centralizer ({t} : Set Y)) := by
    refine TC.le_oddCoreImg_of_normalizes ?_ ?_ ?_
    · intro y hy
      rw [mem_conjSub_iff, inv_inv] at hy
      have := hmem _ ((oddCoreImg_le C) hy)
      simpa [mul_assoc] using this
    · intro e he y hy
      rw [mem_conjSub_iff, inv_inv] at hy ⊢
      have he' : g * e * g⁻¹ ∈ C := by
        rw [Subgroup.mem_centralizer_singleton_iff] at he ⊢
        calc g * e * g⁻¹ * (g * t * g⁻¹) = g * (e * t) * g⁻¹ := by group
          _ = g * (t * e) * g⁻¹ := by rw [he]
          _ = g * t * g⁻¹ * (g * e * g⁻¹) := by group
      have h1 := conj_mem_oddCoreImg (Subgroup.le_normalizer he') hy
      convert h1 using 1
      group
    · rw [show Nat.card ↥(conjSub g⁻¹ N) = Nat.card ↥N from
        Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
      exact odd_natCard_oddCoreImg C
  rw [show oddCoreImg (Subgroup.centralizer ({t} : Set Y)) = ⊥ from hO, le_bot_iff] at hle
  show N = ⊥
  have := congrArg (conjSub g) hle
  rw [conjSub_conjSub_inv] at this
  rw [this]
  exact Subgroup.map_bot _

section Cit3


theorem quat_member {r n : ℕ} (hL : TightLargeHypR r n Y R S t) (h2 : IsPGroup 2 R)
    {J : Subgroup Y} (hJ : J ∈ CoreAssembly.conjClass (tightCore R)) :
    Nonempty (↥J ≃* QuaternionGroup (2 ^ (r - 2))) := by
  obtain ⟨g, rfl⟩ := hJ
  obtain ⟨eS⟩ := hL.cls.1
  have hS : (S : Subgroup R) = ⊤ := (S.is_maximal' (h2.to_subgroup ⊤) le_top).symm
  let e₁ : ↥(conjSub g (tightCore R)) ≃* ↥(tightCore R) :=
    ((tightCore R).equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm
  let e₂ : ↥(tightCore R) ≃* ↥R := MulEquiv.subgroupCongr (tightCore_eq_self_of_isPGroup h2)
  let e₃ : ↥R ≃* ↥(S : Subgroup R) :=
    Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hS.symm)
  exact ⟨((e₁.trans e₂).trans e₃).trans eS⟩

theorem T4Hyp.of_large {r n : ℕ} (hL : TightLargeHypR r n Y R S t) (hO : TightOddCent t) :
    T4Hyp r Y (CoreAssembly.conjClass (tightCore R)) := by
  have hd := hL.datum
  refine T4Hyp.of_isPGroup hd.hypOmegaGen (hd.isPGroup_member hO) ?_ ?_ ?_ hL.cls.2.2
  · intro J hJ P hP
    have hJP : J = P := hP.2.2 J le_rfl (hd.isPGroup_member hO J hJ) hP.1
    obtain ⟨e⟩ := quat_member hL (hd.isPGroup_of_oddCent hO) hJ
    exact ⟨(MulEquiv.subgroupCongr hJP.symm).trans e⟩
  · intro J hJ u hu
    exact (hd.normalizer_eq_centralizer_member hJ hu).ge
  · intro J hJ J' hJ' u hu hu'
    exact hd.eq_of_isUniqueInvolution_member hJ hJ' hu hu'

theorem sepHyp_of_thm4R {r n : ℕ} (hL : TightLargeHypR r n Y R S t) (hO : TightOddCent t)
    (h4 : Thm4RBelow r n) : TC.SepHyp (CoreAssembly.conjClass (tightCore R)) := by
  have hT := T4Hyp.of_large hL hO
  have h2 := hL.datum.isPGroup_member hO
  intro K J J' hKJ hKJ' hnot
  obtain ⟨g, hgK⟩ := hKJ.1
  have hz : IsUniqueInvolution K (g * t * g⁻¹) := hgK ▸ hL.datum.isUniqueInvolution_core.conj g
  set H := nbrGen (nbrAdj (CoreAssembly.conjClass (tightCore R))) K with hHdef
  have hHK := nbrGen_le_centralizer hT.hyp h2 hKJ.1
  have hHz : H ≤ Subgroup.centralizer ({g * t * g⁻¹} : Set Y) :=
    hHK.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hz.mem))
  have hcent := hT.tight K hKJ.1 _ hz
  have hOH : classicalInvolutionOddCore ↥H = ⊥ := by
    refine oddCore_eq_bot_of_le_centralizer hHz (fun c hc => ?_) (tightOddCent_conj hO g)
    refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
    · exact conj_mem_nbrGen hT.hyp (hcent hc) hx
    · have := conj_mem_nbrGen hT.hyp (hcent (Subgroup.inv_mem _ hc)) hx
      simpa [mul_assoc] using this
  have hlt : Nat.card H < n := by
    rw [← hL.card]
    have hCz : Subgroup.centralizer ({g * t * g⁻¹} : Set Y) ≠ ⊤ := by
      intro htop
      have hmem : g * t * g⁻¹ ∈ Subgroup.center Y := Subgroup.mem_center_iff.mpr fun y => by
        have hy : y ∈ Subgroup.centralizer ({g * t * g⁻¹} : Set Y) := htop ▸ Subgroup.mem_top y
        exact Subgroup.mem_centralizer_singleton_iff.mp hy
      rw [hL.center, Subgroup.mem_bot] at hmem
      exact hz.ne_one hmem
    calc Nat.card H ≤ Nat.card ↥(Subgroup.centralizer ({g * t * g⁻¹} : Set Y)) :=
          Subgroup.card_le_of_le hHz
      _ < Nat.card Y := lt_of_le_of_ne (Subgroup.card_le_card_group _)
          (fun h => hCz ((Subgroup.card_eq_iff_eq_top _).mp h))
  have hJH : J ≤ H := le_nbrGen hKJ
  have hJ'H : J' ≤ H := le_nbrGen hKJ'
  have hc := h4 ↥H hlt _ (hT.restrict H hOH) (J.subgroupOf H) ⟨J, hKJ.2.1, hJH, rfl⟩
    (J'.subgroupOf H) ⟨J', hKJ'.2.1, hJ'H, rfl⟩ fun hex => by
      obtain ⟨x, hxH, hx⟩ := exists_conjSub_of_restrict hJH hJ'H hex
      exact hnot ⟨x, hxH, hx⟩
  have hcomm := commutes_of_restrict hJH hJ'H hc
  refine ⟨hKJ.2.1, (mem_omegaNbr_iff hT.hyp h2).mpr ⟨hKJ'.2.1, fun h => ?_, fun y hy => ?_⟩⟩
  · exact hnot (by rw [h]; exact mem_orbOf_self K J)
  · refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
    · have h1 : y * x * y⁻¹ = x := by
        rw [← hcomm x hx y hy, mul_inv_cancel_right]
      rw [h1]
      exact hx
    · have h1 := hcomm _ hx y hy
      have h2 : x = y * x * y⁻¹ := by
        calc x = y⁻¹ * (y * x * y⁻¹ * y) := by group
          _ = y⁻¹ * (y * (y * x * y⁻¹)) := by rw [h1]
          _ = y * x * y⁻¹ := by group
      rw [h2]
      exact hx

theorem tightSepLeafR_of_thm4R {r n : ℕ} (h4 : Thm4RBelow r n) : TightSepLeafR r n :=
  fun _ _ _ _ _ _ hL hO => sepHyp_of_thm4R hL hO h4

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
