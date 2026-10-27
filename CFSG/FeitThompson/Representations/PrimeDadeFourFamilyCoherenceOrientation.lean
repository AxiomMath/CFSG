module

public import CFSG.FeitThompson.Representations.PrimeDadeFourFamilyAntirealBlocks
public import CFSG.FeitThompson.Representations.CoherentRowImageSelectsSignedColumn
import CFSG.FeitThompson.Representations.CoherentReferenceImageOddNonzeroOffCore

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace PrimeDadeFourFamilyOrientation

section Aux

variable {G : Type*} [Group G] [Fintype G] {L : Subgroup G} [Fintype ↥L]

theorem sum_filter_notMem_eq_sub {M : Type*} [AddCommGroup M] [DecidableEq M]
    {s t : Finset M} (hts : t ⊆ s) :
    ∑ x ∈ s.filter (· ∉ t), x = ∑ x ∈ s, x - ∑ x ∈ t, x := by
  rw [← Finset.sdiff_eq_filter, Finset.sum_sdiff_eq_sub hts]

noncomputable def toSpanIrr {S : Set (↥L → ℂ)} (τ : charSpanZero S →+ virtualChars G) :
    charSpanZero S →+ Submodule.span ℤ (Irr G) :=
  ((Submodule.inclusion virtualChars_le_span_Irr).toAddMonoidHom).comp τ

omit [Fintype G] [Fintype ↥L] in
theorem coe_toSpanIrr {S : Set (↥L → ℂ)} (τ : charSpanZero S →+ virtualChars G)
    (f : charSpanZero S) : ((toSpanIrr τ f : Submodule.span ℤ (Irr G)) : G → ℂ)
      = ((τ f : virtualChars G) : G → ℂ) := (rfl)

theorem isCoherentWith_of_toSpanIrr {S : Set (↥L → ℂ)} {τ : charSpanZero S →+ virtualChars G}
    {ν : Submodule.span ℤ S →+ virtualChars G}
    (hν : IsCoherentWith S ((spanIrrToVirtualChars G).comp (toSpanIrr τ)) ν) :
    IsCoherentWith S τ ν :=
  ⟨hν.inner_eq, fun f => (hν.eq_on_zero f).trans (Subtype.ext (by
    rw [AddMonoidHom.comp_apply, coe_spanIrrToVirtualChars, coe_toSpanIrr]))⟩

theorem coe_nu_sub_eq {S : Set (↥L → ℂ)} {A₀ : Set G} {T : G → Subgroup G}
    (hD : IsDadeData L A₀ T) {τ : charSpanZero S →+ virtualChars G}
    (hτ : ∀ (f : charSpanZero S) (F : dadeDomain L A₀), (f : ↥L → ℂ) = (F : ↥L → ℂ) →
      ((τ f : virtualChars G) : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
    {ν : Submodule.span ℤ S →+ virtualChars G}
    (hν : IsCoherentWith S ((spanIrrToVirtualChars G).comp (toSpanIrr τ)) ν)
    {f g : ↥L → ℂ} (hf : f ∈ Submodule.span ℤ S) (hg : g ∈ Submodule.span ℤ S)
    (hfg : f 1 = g 1) (hdomfg : f - g ∈ dadeDomain L A₀) :
    ((ν ⟨f, hf⟩ : virtualChars G) : G → ℂ) - ((ν ⟨g, hg⟩ : virtualChars G) : G → ℂ)
      = ((dadeMap hD ⟨f - g, hdomfg⟩ : classFun G) : G → ℂ) := by
  have hz : f - g ∈ charSpanZero S :=
    mem_charSpanZero.2 ⟨sub_mem hf hg, by rw [Pi.sub_apply, hfg, sub_self]⟩
  have hsplit : Submodule.inclusion (charSpanZero_le S) (⟨f - g, hz⟩ : charSpanZero S)
      = (⟨f, hf⟩ : Submodule.span ℤ S) - ⟨g, hg⟩ := Subtype.ext rfl
  have h1 := hν.eq_on_zero ⟨f - g, hz⟩
  rw [hsplit, map_sub] at h1
  have h2 := congrArg (fun z : virtualChars G => (z : G → ℂ)) h1
  simp only [Submodule.coe_sub] at h2
  rw [h2, AddMonoidHom.comp_apply, coe_spanIrrToVirtualChars, coe_toSpanIrr]
  exact hτ ⟨f - g, hz⟩ ⟨f - g, hdomfg⟩ rfl

theorem nu_apply_eq_zero_of_mem_cyclicTIDiff {S : Set (↥L → ℂ)} {A₀ : Set G} {T : G → Subgroup G}
    {W₁ W₂ : Subgroup ↥L} {A : Set ↥L} {K : Subgroup ↥L}
    (h : IsPrimeCyclicTIHyp K W₁ W₂) (hAK : A ⊆ (K : Set ↥L) \ {1})
    (hA₀ : (fun x : ↥L => (x : G)) '' bridgeSupport A W₁ W₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T) {τ : charSpanZero S →+ virtualChars G}
    (hτ : ∀ (f : charSpanZero S) (F : dadeDomain L A₀), (f : ↥L → ℂ) = (F : ↥L → ℂ) →
      ((τ f : virtualChars G) : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
    {ν : Submodule.span ℤ S →+ virtualChars G}
    (hν : IsCoherentWith S ((spanIrrToVirtualChars G).comp (toSpanIrr τ)) ν)
    {f g : ↥L → ℂ} (hf : f ∈ Submodule.span ℤ S) (hg : g ∈ Submodule.span ℤ S)
    (hfg : f 1 = g 1) (hdomfg : f - g ∈ dadeDomain L A₀)
    (hzero : ∀ x : ↥L, x ∉ A ∪ {1} → f x = 0 ∧ g x = 0)
    (hgV : ∀ v ∈ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype),
      ((ν ⟨g, hg⟩ : virtualChars G) : G → ℂ) v = 0)
    {v : G}
    (hv : v ∈ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)) :
    ((ν ⟨f, hf⟩ : virtualChars G) : G → ℂ) v = 0 := by
  have hsub := coe_nu_sub_eq hD hτ hν hf hg hfg hdomfg
  rw [← image_cyclicTIset_eq] at hv
  obtain ⟨x, hx, rfl⟩ := hv
  have hxA : (x : G) ∈ A₀ := hA₀ ⟨x,
    cyclicTIsetConj_subset_bridgeSupport (cyclicTIset_subset_cyclicTIsetConj _ _ hx), rfl⟩
  have hxnot : x ∉ A ∪ {1} := by
    rintro (hc | hc)
    · exact h.notMem_of_mem_cyclicTIset hx (hAK hc).1
    · exact one_notMem_cyclicTIset (hc ▸ hx)
  obtain ⟨hfx, hgx⟩ := hzero x hxnot
  have hval : ((dadeMap hD ⟨f - g, hdomfg⟩ : classFun G) : G → ℂ) (x : G) = 0 := by
    rw [dadeMap_apply_mem hD ⟨f - g, hdomfg⟩ hxA]
    have hx' : (⟨(x : G), hD.mem_of_mem hxA⟩ : ↥L) = x := Subtype.ext rfl
    change (f - g) (⟨(x : G), hD.mem_of_mem hxA⟩ : ↥L) = 0
    rw [hx', Pi.sub_apply, hfx, hgx, sub_self]
  have hgv := hgV (x : G) (image_cyclicTIset_eq L W₁ W₂ ▸ ⟨x, hx, rfl⟩)
  have hfin := congrFun hsub (x : G)
  rw [Pi.sub_apply, hval, hgv, sub_zero] at hfin
  exact hfin

omit [Fintype ↥L] in
theorem sum_prodCharEta_irrMapSubtype {W₁ W₂ : Subgroup ↥L} [Fintype ↑(Irr ↥W₁)]
    {ω : classFun ↥((W₁ ⊔ W₂).map L.subtype) →ₗ[ℂ] classFun G}
    (hW : IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    (b : Irr ↥(W₂.map L.subtype)) :
    ∑ i : Irr ↥W₁, hW.prodCharEta ω (irrMapSubtype L W₁ i) b = hW.prodCharEtaColSum ω b := by
  have : Fintype ↑(Irr ↥(W₁.map L.subtype)) := Fintype.ofFinite _
  rw [hW.prodCharEtaColSum_eq_sum]
  exact Fintype.sum_bijective (irrMapSubtype L W₁) (irrMapSubtype_bijective L W₁) _ _ fun _ => rfl

end Aux

section Blocks

variable {G : Type*} [Fintype G] [DecidableEq (G → ℂ)] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {a b : G → ℂ} {u : ι → G → ℂ}

omit [Fintype G] [DecidableEq ι] in
theorem mem_pair_union_image_iff {x : G → ℂ} :
    x ∈ ({a, b} : Finset (G → ℂ)) ∪ Finset.image u Finset.univ ↔
      x = a ∨ x = b ∨ ∃ p, u p = x := by
  simp [Finset.mem_insert, Finset.mem_image, eq_comm]

omit [DecidableEq ι] in
theorem notMem_image_of_cfInner_eq_zero (hu : ∀ p, cfInner (u p) (u p) = 1)
    (ha : ∀ p, cfInner a (u p) = 0) : a ∉ Finset.image u Finset.univ := by
  intro hc
  obtain ⟨p, -, hp⟩ := Finset.mem_image.1 hc
  have h1 := hu p
  have h2 := ha p
  rw [hp] at h1 h2
  rw [h2] at h1
  exact zero_ne_one h1

omit [DecidableEq ι] in
theorem disjoint_pair_image (hu : ∀ p, cfInner (u p) (u p) = 1)
    (ha : ∀ p, cfInner a (u p) = 0) (hb : ∀ p, cfInner b (u p) = 0) :
    Disjoint ({a, b} : Finset (G → ℂ)) (Finset.image u Finset.univ) := by
  rw [Finset.disjoint_left]
  intro x hx
  rcases Finset.mem_insert.1 hx with rfl | hx'
  · exact notMem_image_of_cfInner_eq_zero hu ha
  · rw [Finset.mem_singleton] at hx'
    subst hx'
    exact notMem_image_of_cfInner_eq_zero hu hb

theorem isOrthonormalFamily_pair_union_image
    (haa : cfInner a a = 1) (hbb : cfInner b b = 1)
    (hab : cfInner a b = 0) (hba : cfInner b a = 0)
    (hu : ∀ p q, cfInner (u p) (u q) = if p = q then 1 else 0)
    (hau : ∀ p, cfInner a (u p) = 0) (hua : ∀ p, cfInner (u p) a = 0)
    (hbu : ∀ p, cfInner b (u p) = 0) (hub : ∀ p, cfInner (u p) b = 0) :
    IsOrthonormalFamily fun w : {x // x ∈ ({a, b} : Finset (G → ℂ)) ∪
      Finset.image u Finset.univ} => (w : G → ℂ) := by
  refine IsOrthonormalFamily.of_cfInner_self_of_isOrthogonal ?_ ?_
  · rintro ⟨x, hx⟩
    rcases mem_pair_union_image_iff.1 hx with rfl | rfl | ⟨p, rfl⟩
    · exact haa
    · exact hbb
    · simpa using hu p p
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    have hne : x ≠ y := fun hc => hxy (Subtype.ext hc)
    rw [isOrthogonal_iff]
    rcases mem_pair_union_image_iff.1 hx with rfl | rfl | ⟨p, rfl⟩ <;>
      rcases mem_pair_union_image_iff.1 hy with rfl | rfl | ⟨q, rfl⟩
    · exact absurd rfl hne
    · exact hab
    · exact hau q
    · exact hba
    · exact absurd rfl hne
    · exact hbu q
    · exact hua p
    · exact hub p
    · rw [hu p q, if_neg (fun hc : p = q => hne (by rw [hc]))]

end Blocks

theorem primeDade_four_family_coherence_orientation {G : Type*} [Group G] [Fintype G]
    {L : Subgroup G} [Fintype ↥L] {K W₁ W₂ : Subgroup ↥L} [Fintype ↥(W₁ ⊔ W₂)]
    [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] [Fintype ↑(Irr ↥W₁)]
    {σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun ↥L}
    {ω : classFun ↥((W₁ ⊔ W₂).map L.subtype) →ₗ[ℂ] classFun G}
    {A₀ : Set G} {T : G → Subgroup G}
    (h : IsPrimeCyclicTIHyp K W₁ W₂) (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ)
    {H : Subgroup ↥L} [H.Normal] (hWH : W₂ ≤ H)
    {A : Set ↥L} (hAK : A ⊆ (K : Set ↥L) \ {1})
    (hAconj : ∀ t : ↥L, (fun a => t⁻¹ * a * t) '' A = A)
    (hA : ∀ y ∈ H, y ≠ 1 → ((K ⊓ Subgroup.centralizer {y} : Subgroup ↥L) : Set ↥L) \ {1} ⊆ A)
    (hA₀ : (fun x : ↥L => (x : G)) '' bridgeSupport A W₁ W₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T)
    (hstab : {g : G | (fun x => g⁻¹ * x * g) ''
        cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
      = cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)}
      = (((W₁ ⊔ W₂).map L.subtype : Subgroup G) : Set G))
    (hdisj : ∀ g ∉ (W₁ ⊔ W₂).map L.subtype,
      (fun x => g⁻¹ * x * g) ''
          cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
        ∩ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) = ∅)
    (hω : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) ω)
    (hodd : Odd (Nat.card G))
    {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂)
    {θ : ↥K → ℂ} (hθ : θ ∈ Irr ↥K)
    (hHθ : ∃ y : ↥K, (y : ↥L) ∈ H ∧ y ∉ charValueKernel θ)
    (hξ : indClassFun K θ ∈ Irr ↥L)
    (hdeg : indClassFun K θ 1 = h.primeTIrow σ j 1)
    {S : Set (↥L → ℂ)}
    (hS : S = {indClassFun K θ, star (indClassFun K θ), h.primeTIrow σ j,
      h.primeTIrow σ (starIrr j)})
    {τ : charSpanZero S →+ virtualChars G}
    (hτ : ∀ (f : charSpanZero S) (F : dadeDomain L A₀), (f : ↥L → ℂ) = (F : ↥L → ℂ) →
      ((τ f : virtualChars G) : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ)) :
    ∃ ν : Submodule.span ℤ S →+ virtualChars G, IsCoherentWith S τ ν ∧
      (∀ w : Submodule.span ℤ S, (w : ↥L → ℂ) = indClassFun K θ →
        ((ν w : virtualChars G) : G → ℂ) ∈ signedIrr G ∧
        star ((ν w : virtualChars G) : G → ℂ) ≠ ((ν w : virtualChars G) : G → ℂ) ∧
        ∀ (a : Irr ↥(W₁.map L.subtype)) (b : Irr ↥(W₂.map L.subtype)),
          cfInner ((ν w : virtualChars G) : G → ℂ)
            ((h.isCyclicTIPair_map_subtype hstab hdisj).prodCharEta ω a b) = 0) ∧
      (∀ w w' : Submodule.span ℤ S, (w : ↥L → ℂ) = indClassFun K θ →
        (w' : ↥L → ℂ) = star (indClassFun K θ) →
        ((ν w' : virtualChars G) : G → ℂ) = star ((ν w : virtualChars G) : G → ℂ)) ∧
      (∀ wj wk : Submodule.span ℤ S, (wj : ↥L → ℂ) = h.primeTIrow σ j →
        (wk : ↥L → ℂ) = h.primeTIrow σ (starIrr j) →
        (((ν wj : virtualChars G) : G → ℂ) = h.primeTISign σ j •
              (h.isCyclicTIPair_map_subtype hstab hdisj).prodCharEtaColSum ω
                (irrMapSubtype L W₂ j) ∧
            ((ν wk : virtualChars G) : G → ℂ) = h.primeTISign σ j •
              (h.isCyclicTIPair_map_subtype hstab hdisj).prodCharEtaColSum ω
                (irrMapSubtype L W₂ (starIrr j))) ∨
          (((ν wj : virtualChars G) : G → ℂ) = (-h.primeTISign σ j) •
              (h.isCyclicTIPair_map_subtype hstab hdisj).prodCharEtaColSum ω
                (irrMapSubtype L W₂ (starIrr j)) ∧
            ((ν wk : virtualChars G) : G → ℂ) = (-h.primeTISign σ j) •
              (h.isCyclicTIPair_map_subtype hstab hdisj).prodCharEtaColSum ω
                (irrMapSubtype L W₂ j))) := by
  classical
  obtain ⟨hsign, hrow, ⟨hd01, hd02, hd03, hd12, hd13, hd23⟩,
    ⟨ho01, ho02, ho03, ho12, ho13, ho23⟩,
    ⟨dn, hdn0, hdξ, hdsξ, hdj, hdk⟩, ⟨hn1, hn2, hn3, hn4⟩, hsupp, hdomain,
    ⟨ρ, hρIrr, hρnr, hρeq, horthρ, hρV⟩, htransfer⟩ :=
    primeDade_four_family_antireal_blocks h hσ hWH hAconj hA hA₀ hD hstab hdisj hω hodd hj hθ
      hHθ hξ hdeg
  set hW := h.isCyclicTIPair_map_subtype hstab hdisj with hWdef
  have hfinI : Fintype ↑(Irr ↥(W₁.map L.subtype)) := Fintype.ofFinite _
  set ξ : ↥L → ℂ := indClassFun K θ with hξdef
  set ψ : ↥L → ℂ := h.primeTIrow σ j with hψdef
  rw [hrow] at hS hsupp hdomain hd03 hd13 hd23 ho03 ho13 ho23 hdk hn4 htransfer ⊢
  set δ : ℂ := h.primeTISign σ j with hδdef
  set jj := irrMapSubtype L W₂ j with hjjdef
  set kk := irrMapSubtype L W₂ (starIrr j) with hkkdef
  have hδ : δ = 1 ∨ δ = -1 := h.primeTISign_eq_one_or_eq_neg_one j
  have hδ0 : δ ≠ 0 := by rcases hδ with hh | hh <;> simp [hh]
  have hjsne : starIrr j ≠ j := h.starIrr_ne_self_right hj
  have hjk : jj ≠ kk := fun hc => hjsne (irrMapSubtype_injective L W₂ hc.symm)
  have hdomS : ∀ f ∈ Submodule.span ℤ S, f 1 = 0 → f ∈ dadeDomain L A₀ :=
    fun f hf => hdomain f (hS ▸ hf)
  have hdom : ∀ f : charSpanZero S, (f : ↥L → ℂ) ∈ dadeDomain L A₀ := by
    intro f
    obtain ⟨hf1, hf2⟩ := mem_charSpanZero.1 f.2
    exact hdomS _ hf1 hf2
  have hτiso : ∀ w w' : charSpanZero S,
      cfInner ((toSpanIrr τ w : Submodule.span ℤ (Irr G)) : G → ℂ)
        ((toSpanIrr τ w' : Submodule.span ℤ (Irr G)) : G → ℂ)
      = cfInner ((w : ↥L → ℂ)) ((w' : ↥L → ℂ)) := by
    intro w w'
    rw [coe_toSpanIrr, coe_toSpanIrr, hτ w ⟨_, hdom w⟩ rfl, hτ w' ⟨_, hdom w'⟩ rfl]
    exact cfInner_dadeMap hD _ _
  set sTC := hW.signedTwoColumn ω δ jj kk with hsTCdef
  set Rblk : Finset (G → ℂ) := {ρ, -star ρ} with hRblkdef
  set Tblk : Finset (G → ℂ) := Finset.image sTC Finset.univ with hTblkdef
  have hinjT : Function.Injective sTC := hW.signedTwoColumn_injective hω hδ0 hjk
  have hρne : ρ ≠ -star ρ := ne_neg_of_mem_Irr hρIrr (star_mem_Irr hρIrr)
  have hsumRblk : ∑ r ∈ Rblk, r = ρ - star ρ := by
    rw [hRblkdef, Finset.sum_pair hρne]; abel
  have hτR : ∀ w : charSpanZero S, (w : ↥L → ℂ) = ξ - star ξ →
      ((toSpanIrr τ w : Submodule.span ℤ (Irr G)) : G → ℂ) = ∑ r ∈ Rblk, r := by
    intro w hw
    rw [coe_toSpanIrr, hτ w ⟨_, hdom w⟩ rfl, coe_dadeMap hD, hw, hρeq, hsumRblk]
  have hsumTblk : ∑ t ∈ Tblk, t
      = δ • hW.prodCharEtaColSum ω jj - δ • hW.prodCharEtaColSum ω kk := by
    rw [hTblkdef, Finset.sum_image (fun a _ b _ hh => hinjT hh), ← hW.sum_signedTwoColumn δ jj kk]
  have hτT : ∀ w : charSpanZero S, (w : ↥L → ℂ) = ψ - star ψ →
      ((toSpanIrr τ w : Submodule.span ℤ (Irr G)) : G → ℂ) = ∑ t ∈ Tblk, t := by
    intro w hw
    rw [coe_toSpanIrr, hτ w ⟨_, hdom w⟩ rfl, coe_dadeMap hD, hw, htransfer,
      Finset.sum_sub_distrib, sum_prodCharEta_irrMapSubtype hW,
      sum_prodCharEta_irrMapSubtype hW, smul_sub, hsumTblk]
  have hGramT : ∀ p q, cfInner (sTC p) (sTC q) = if p = q then 1 else 0 :=
    hW.cfInner_signedTwoColumn_signedTwoColumn hω hδ hjk
  have hρT : ∀ p, cfInner ρ (sTC p) = 0 ∧ cfInner (star ρ) (sTC p) = 0 := by
    rintro ⟨i, bb⟩
    cases bb
    · rw [hsTCdef]
      simp only [IsCyclicTIPair.signedTwoColumn_apply_false, cfInner_smul_right]
      exact ⟨by rw [(horthρ i kk).1]; ring, by rw [(horthρ i kk).2]; ring⟩
    · rw [hsTCdef]
      simp only [IsCyclicTIPair.signedTwoColumn_apply_true, cfInner_smul_right]
      exact ⟨by rw [(horthρ i jj).1]; ring, by rw [(horthρ i jj).2]; ring⟩
  have hρρ : cfInner ρ ρ = 1 := cfInner_self_of_mem_Irr hρIrr
  have hρsρ : cfInner ρ (star ρ) = 0 :=
    cfInner_eq_zero_of_mem_Irr hρIrr (star_mem_Irr hρIrr) (fun hc => hρnr hc.symm)
  have hsρρ : cfInner (star ρ) ρ = 0 := by rw [← conj_cfInner, hρsρ, map_zero]
  have hsρsρ : cfInner (star ρ) (star ρ) = 1 := cfInner_self_of_mem_Irr (star_mem_Irr hρIrr)
  have hON : IsOrthonormalFamily fun w : {x // x ∈ Rblk ∪ Tblk} => (w : G → ℂ) := by
    rw [hRblkdef, hTblkdef]
    refine isOrthonormalFamily_pair_union_image hρρ (by
        rw [cfInner_neg_left, cfInner_neg_right, hsρsρ]; ring)
      (by rw [cfInner_neg_right, hρsρ]; ring) (by rw [cfInner_neg_left, hsρρ]; ring)
      hGramT (fun p => (hρT p).1) (fun p => by rw [← conj_cfInner, (hρT p).1, map_zero])
      (fun p => by rw [cfInner_neg_left, (hρT p).2]; ring)
      (fun p => by rw [cfInner_neg_right, ← conj_cfInner, (hρT p).2, map_zero]; ring)
  have hRT : Disjoint Rblk Tblk := by
    rw [hRblkdef, hTblkdef]
    exact disjoint_pair_image (fun p => by simpa using hGramT p p) (fun p => (hρT p).1)
      (fun p => by rw [cfInner_neg_left, (hρT p).2]; ring)
  have hRmem : ∀ r ∈ Rblk, r ∈ Submodule.span ℤ (Irr G) := by
    intro r hr
    rw [hRblkdef] at hr
    rcases Finset.mem_insert.1 hr with rfl | hr'
    · exact Submodule.subset_span hρIrr
    · rw [Finset.mem_singleton] at hr'
      subst hr'
      exact neg_mem (Submodule.subset_span (star_mem_Irr hρIrr))
  have hTmem : ∀ t ∈ Tblk, t ∈ Submodule.span ℤ (Irr G) := by
    intro t ht
    rw [hTblkdef] at ht
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 ht
    exact hW.signedTwoColumn_mem_span_Irr hω hδ jj kk p
  have hinj : Function.Injective ![ξ, star ξ, ψ, star ψ] := by
    rw [← List.nodup_ofFn]
    simp only [List.ofFn_succ, List.ofFn_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
      List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, or_false, not_or,
      and_true, not_false_eq_true]
    exact ⟨⟨hd01, hd02, hd03⟩, ⟨hd12, hd13⟩, hd23⟩
  have horth : ∀ f ∈ S, ∀ g ∈ S, f ≠ g → IsOrthogonal f g := by
    have key : ∀ (f g : ↥L → ℂ), cfInner f g = 0 → cfInner g f = 0 := by
      intro f g hfg
      rw [← conj_cfInner, hfg, map_zero]
    intro f hf g hg hfg
    rw [hS] at hf hg
    rw [isOrthogonal_iff]
    rcases hf with rfl | rfl | rfl | rfl <;> rcases hg with rfl | rfl | rfl | rfl <;>
      first
        | exact absurd rfl hfg
        | assumption
        | exact key _ _ ‹_›
  have hdegS : ∀ f ∈ S, f 1 = ((dn : ℝ) : ℂ) := by
    intro f hf
    rw [hS] at hf
    rcases hf with rfl | rfl | rfl | rfl <;> push_cast <;> assumption
  have hξL : ξ ∈ Submodule.span ℤ (Irr ↥L) := Submodule.subset_span hξ
  have hψL : ψ ∈ Submodule.span ℤ (Irr ↥L) :=
    virtualChars_le_span_Irr (primeTIrow_mem_virtualChars h hσ j)
  obtain ⟨hRcard, hTcard, R₀, hR₀, T₀, hT₀, hR₀card, hT₀card, ν, hνc, hνξ, hνsξ, hνψ, hνsψ⟩ :=
    exists_isCoherentWith_of_four_member_mixed_norm hξL hψL hS hinj horth
      (by exact_mod_cast hdn0) hdegS (le_refl 1) (Nat.card_pos (α := ↥W₁)) (by exact_mod_cast hn1)
      hn3 hτiso hRT hRmem hTmem hON hτR hτT
  have hmξ : ξ ∈ Submodule.span ℤ S := Submodule.subset_span (by rw [hS]; simp)
  have hmψ : ψ ∈ Submodule.span ℤ S := Submodule.subset_span (by rw [hS]; simp)
  obtain ⟨r0, hr0R₀⟩ := Finset.card_eq_one.1 hR₀card
  have hr0mem : r0 ∈ Rblk := hR₀ (hr0R₀ ▸ Finset.mem_singleton_self r0)
  have hsumR₀ : ∑ r ∈ R₀, r = r0 := by rw [hr0R₀, Finset.sum_singleton]
  have hsumR₁ : ∑ r ∈ Rblk.filter (· ∉ R₀), r = (ρ - star ρ) - r0 := by
    rw [sum_filter_notMem_eq_sub hR₀, hsumRblk, hsumR₀]
  have hstarρV : ∀ v ∈ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype)
      (W₂.map L.subtype), (star ρ) v = 0 := by
    intro v hv
    rw [Pi.star_apply, hρV v hv]
    simp
  have hr0 : r0 ∈ signedIrr G ∧ star r0 ≠ r0 ∧
      (∀ (a : Irr ↥(W₁.map L.subtype)) (b : Irr ↥(W₂.map L.subtype)),
        cfInner r0 (hW.prodCharEta ω a b) = 0) ∧
      (∀ v ∈ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype),
        r0 v = 0) ∧ -((ρ - star ρ) - r0) = star r0 := by
    rw [hRblkdef] at hr0mem
    rcases Finset.mem_insert.1 hr0mem with rfl | hr0'
    · exact ⟨Irr_subset_signedIrr hρIrr, hρnr, fun a b => (horthρ a b).1, hρV, by abel⟩
    · rw [Finset.mem_singleton] at hr0'
      subst hr0'
      have hsi : (-star ρ) ∈ signedIrr G := by
        rw [← neg_mem_signedIrr_iff, neg_neg]
        exact Irr_subset_signedIrr (star_mem_Irr hρIrr)
      refine ⟨hsi, ?_, ?_, ?_, ?_⟩
      · rw [star_neg, star_star]
        intro hc
        exact hρnr (neg_injective hc).symm
      · intro a b
        rw [cfInner_neg_left, (horthρ a b).2]; ring
      · intro v hv
        rw [Pi.neg_apply, hstarρV v hv, neg_zero]
      · rw [star_neg, star_star]; abel
  obtain ⟨hr0si, hr0nr, hr0orth, hr0V, hr0conj⟩ := hr0
  have hνξr0 : ∀ w : Submodule.span ℤ S, (w : ↥L → ℂ) = ξ →
      ((ν w : virtualChars G) : G → ℂ) = r0 := fun w hw => by rw [hνξ w hw, hsumR₀]
  have hνsξr0 : ∀ w : Submodule.span ℤ S, (w : ↥L → ℂ) = star ξ →
      ((ν w : virtualChars G) : G → ℂ) = star r0 := fun w hw => by
    rw [hνsξ w hw, hsumR₁, hr0conj]
  have hνψV : ∀ v ∈ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype),
      ((ν ⟨ψ, hmψ⟩ : virtualChars G) : G → ℂ) v = 0 := by
    intro v hv
    refine nu_apply_eq_zero_of_mem_cyclicTIDiff h hAK hA₀ hD hτ hνc hmψ hmξ hdeg.symm ?_ ?_ ?_ hv
    · refine hdomS _ (sub_mem hmψ hmξ) ?_
      rw [Pi.sub_apply, hdeg, sub_self]
    · intro x hx
      exact ⟨(hsupp x hx).2.2.1, (hsupp x hx).1⟩
    · intro v hv
      rw [hνξr0 ⟨ξ, hmξ⟩ rfl]
      exact hr0V v hv
  have hsumT₀V : ∀ v ∈ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype)
      (W₂.map L.subtype), (∑ t ∈ T₀, t) v = 0 := by
    intro v hv
    rw [← hνψ ⟨ψ, hmψ⟩ rfl]
    exact hνψV v hv
  have hT₀range : (T₀ : Set (G → ℂ)) ⊆ Set.range sTC := by
    intro t ht
    rw [hTblkdef] at hT₀
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 (hT₀ ht)
    exact ⟨p, rfl⟩
  have hT₀card' : T₀.card = Nat.card ↑(Irr ↥(W₁.map L.subtype)) := by
    rw [hT₀card, hW.card_Irr_left, Subgroup.card_subtype]
  obtain hcol | hcol :=
    hW.eq_col_sum_of_card_eq_of_vanishing_on_cyclicTIDiff hω hδ hjk hT₀range hT₀card' hsumT₀V
  · refine ⟨ν, isCoherentWith_of_toSpanIrr hνc, ?_, ?_, ?_⟩
    · intro w hw
      rw [hνξr0 w hw]
      exact ⟨hr0si, hr0nr, hr0orth⟩
    · intro w w' hw hw'
      rw [hνsξr0 w' hw', hνξr0 w hw]
    · intro wj wk hwj hwk
      refine Or.inl ⟨by rw [hνψ wj hwj, hcol], ?_⟩
      rw [hνsψ wk hwk, sum_filter_notMem_eq_sub hT₀, hsumTblk, hcol]
      abel
  · refine ⟨ν, isCoherentWith_of_toSpanIrr hνc, ?_, ?_, ?_⟩
    · intro w hw
      rw [hνξr0 w hw]
      exact ⟨hr0si, hr0nr, hr0orth⟩
    · intro w w' hw hw'
      rw [hνsξr0 w' hw', hνξr0 w hw]
    · intro wj wk hwj hwk
      refine Or.inr ⟨by rw [hνψ wj hwj, hcol], ?_⟩
      rw [hνsψ wk hwk, sum_filter_notMem_eq_sub hT₀, hsumTblk, hcol]
      module

end PrimeDadeFourFamilyOrientation

end CFSG.FeitThompson

end
