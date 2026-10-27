module

public import CFSG.GH74.Generic.BProg.B2.PuL4Gen4Uni
public import CFSG.GH74.Generic.BProg.B2.PuL4GraphUniForm
public import CFSG.GH74.Generic.BProg.B2.PuL4GraphUniAlt
public import CFSG.GH74.Generic.BProg.B2.PuL4GraphUniSplit
public import CFSG.GH74.Generic.BProg.B2.PuL4GraphUniNonsplit
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OIUb
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OIUa

public section

namespace CFSG.GH74.Generic.BProg.B2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatFactsL4U4

namespace PuL4GraphUni

variable {p f : ℕ} {K : Type} [Field K]

theorem exists_stated_equiv (h : UnitaryFieldData p f K) :
    ∃ Φ : primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) ≃*
        StatedProj (StatedSU 4 (p ^ f) K),
      ∀ (g : GL (Fin 4) K) (hg : g ∈ unitarySU p f K 4)
        (hg' : g ∈ gramSU h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)),
        Φ (QuotientGroup.mk ⟨g, hg'⟩) = QuotientGroup.mk ⟨g, hg⟩ := by
  classical
  let e0 : unitarySU p f K 4 ≃*
      gramSU h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) :=
    MulEquiv.subgroupCongr (unitarySU_eq_gramSU h 4)
  have hmap : (unitaryScalars h 4).map e0.toMonoidHom =
      normOneScalars h (gramSU h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) 4 := by
    ext z
    constructor
    · rintro ⟨y, ⟨c, hcN, hcn, hy⟩, rfl⟩
      exact ⟨c, hcN, hcn, hy⟩
    · rintro ⟨c, hcN, hcn, hz⟩
      exact ⟨e0.symm z, ⟨c, hcN, hcn, hz⟩, MulEquiv.apply_symm_apply _ _⟩
  let e1 : unitaryPSU h 4 ≃* primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) :=
    QuotientGroup.congr _ _ e0 hmap
  refine ⟨e1.symm.trans (unitaryPSUEquiv h (by norm_num)), fun g hg hg' => ?_⟩
  have h1 : e1 (QuotientGroup.mk ⟨g, hg⟩) = QuotientGroup.mk ⟨g, hg'⟩ :=
    QuotientGroup.congr_mk _ _ _ _ _
  rw [MulEquiv.trans_apply, ← h1, MulEquiv.symm_apply_apply]
  exact unitaryPSUEquiv_unitaryProj h (by norm_num) ⟨g, hg⟩

theorem congr_not_mem_InnU (h : UnitaryFieldData p f K)
    {Φ : primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) ≃*
      StatedProj (StatedSU 4 (p ^ f) K)}
    (hΦ : ∀ (g : GL (Fin 4) K) (hg : g ∈ unitarySU p f K 4)
      (hg' : g ∈ gramSU h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)),
      Φ (QuotientGroup.mk ⟨g, hg'⟩) = QuotientGroup.mk ⟨g, hg⟩)
    (τ : MulAut (primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)))
    (hnd : ∀ A : primeFormUnitary h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K),
      τ ≠ primeFormConjHom h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) A) :
    MulAut.congr Φ τ ∉ DiagU.InnU p f K h := by
  rintro ⟨A, hAU, hA⟩
  have hAm : A ∈ primeFormUnitary h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    rw [mem_primeFormUnitary, Units.val_one, Matrix.mul_one]
    exact (UnitaryOut.mem_uMat h).1 hAU
  apply hnd ⟨A, hAm⟩
  apply MulEquiv.ext
  intro x
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective x
  apply Φ.injective
  rw [primeFormConjHom_mk]
  have hs : (s : GL (Fin 4) K) ∈ unitarySU p f K 4 := by
    rw [unitarySU_eq_gramSU h 4]; exact s.2
  have hA' := DiagU.conj_mem_SU h hAU ⟨s, hs⟩
  have h1 := hΦ (A * (s : GL (Fin 4) K) * A⁻¹) hA' (conj_mem_gramSU h _ hAm s.2)
  have h2 : Φ (τ (QuotientGroup.mk s)) = MulAut.congr Φ τ (Φ (QuotientGroup.mk s)) := by
    simp [MulAut.congr_apply]
  have h3 := hΦ (s : GL (Fin 4) K) hs s.2
  rw [h1, h2, h3]
  exact hA ⟨s, hs⟩ ⟨_, hA'⟩ rfl

theorem component_transport {N : Type} [Group N] [Finite N] {H : Subgroup N} [H.Normal] {t : N}
    {L : Subgroup N} (hs : ShapeInCent H t L) {P : Type} [Group P] (e : ↥H ≃* P) :
    (L.subgroupOf H).map e.toMonoidHom ≤
        OutInv.fixSub (MulAut.congr e (MulAut.conjNormal t : MulAut ↥H)) ∧
      CFSG.IsComponent (((L.subgroupOf H).map e.toMonoidHom).subgroupOf
        (OutInv.fixSub (MulAut.congr e (MulAut.conjNormal t : MulAut ↥H)))) := by
  set φ := MulAut.congr e (MulAut.conjNormal t : MulAut ↥H) with hφ
  have hLC : L ≤ H ⊓ centralizer ({t} : Set N) := hs.comp.1
  have hfix : ∀ x : ↥H, (x : N) ∈ centralizer ({t} : Set N) ↔ e x ∈ OutInv.fixSub φ := by
    intro x
    rw [OutInv.mem_fixSub, hφ, MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [EmbeddingLike.apply_eq_iff_eq, Subtype.ext_iff, MulAut.conjNormal_apply,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hx
      rw [← hx]; group
    · intro hx
      change t * (x : N) * t⁻¹ = x at hx
      calc (x : N) * t = (t * (x : N) * t⁻¹) * t := by rw [hx]
        _ = t * x := by group
  let E : ↥(H ⊓ centralizer ({t} : Set N)) ≃* ↥(OutInv.fixSub φ) :=
    { toFun := fun x => ⟨e ⟨x.1, x.2.1⟩, (hfix ⟨x.1, x.2.1⟩).1 x.2.2⟩
      invFun := fun y => ⟨((e.symm y : ↥H) : N), (e.symm y).2, (hfix (e.symm y)).2 (by
        rw [MulEquiv.apply_symm_apply]; exact y.2)⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun y => Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        change e ⟨(x : N) * y, _⟩ = e ⟨(x : N), _⟩ * e ⟨(y : N), _⟩
        rw [← map_mul]
        rfl) }
  have hJ : ((L.subgroupOf H).map e.toMonoidHom).subgroupOf (OutInv.fixSub φ) =
      (L.subgroupOf (H ⊓ centralizer ({t} : Set N))).map E.toMonoidHom := by
    ext y
    constructor
    · intro hy
      obtain ⟨l, hl, hly⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hy)
      refine Subgroup.mem_map.2 ⟨⟨(l : N), l.2, (hfix l).2 (by
        have h2 : (y : P) ∈ OutInv.fixSub φ := y.2
        rw [← hly] at h2
        exact h2)⟩, ?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 hl)
      · apply Subtype.ext
        exact hly
    · rintro ⟨x, hx, rfl⟩
      refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨⟨x.1, x.2.1⟩, ?_, rfl⟩)
      exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 hx)
  refine ⟨?_, ?_⟩
  · rintro _ ⟨l, hl, rfl⟩
    exact (hfix l).1 (hLC (Subgroup.mem_subgroupOf.1 hl)).2
  · rw [hJ]
    exact isComponent_map_of_isComponent E hs.comp.2

theorem exists_equiv_image {N : Type} [Group N] {H L : Subgroup N} (hLH : L ≤ H) {P D : Type}
    [Group P] [Group D] (e : ↥H ≃* P) (ι : P →* D) (hι : Function.Injective ι) :
    Nonempty (↥L ≃* ↥(((L.subgroupOf H).map e.toMonoidHom).map ι)) :=
  ⟨(Subgroup.subgroupOfEquivOfLe hLH).symm.trans
    (((L.subgroupOf H).equivMapOfInjective e.toMonoidHom e.injective).trans
      (((L.subgroupOf H).map e.toMonoidHom).equivMapOfInjective ι hι))⟩

end PuL4GraphUni

section Certified


theorem outGraphUni_proved : OutGraphUni := by
  intro N _ _ H _ t L p f K _ h hs hq3 hq8 e hnd h4
  have hp2 : p ≠ 2 := GenLocL4Refl.ne_two_of_pow_mod_eight hq8 rfl h.one_le
  have : Finite K := h.finite
  obtain ⟨Φ, hΦ⟩ := PuL4GraphUni.exists_stated_equiv h
  set τ := MulAut.congr e (MulAut.conjNormal t : MulAut ↥H) with hτ
  have ht2 : t ^ 2 = 1 := by
    have := pow_orderOf_eq_one t
    rwa [hs.inv] at this
  have hτ2 : τ ^ 2 = 1 := by rw [hτ, ← map_pow, ← map_pow, ht2, map_one, map_one]
  have htH : t ∉ H := by
    intro ht
    obtain ⟨s, hs'⟩ := QuotientGroup.mk_surjective (e ⟨t, ht⟩)
    apply hnd ⟨s, s.2.1⟩
    rw [primeFormConjHom_eq_conj, hs']
    ext x
    apply e.symm.injective
    apply Subtype.ext
    simp [hτ, MulAut.congr_apply, MulAut.conj_apply, MulAut.conjNormal_apply]
  set φ := MulAut.congr Φ τ with hφdef
  have hφ2 : φ ^ 2 = 1 := by rw [hφdef, ← map_pow, hτ2, map_one]
  have hφ : φ ∉ DiagU.InnU p f K h := PuL4GraphUni.congr_not_mem_InnU h hΦ τ hnd
  obtain ⟨A, ψ, hAu, hψ, hψA, c, hAA⟩ := OIU.exists_anti_form h hp2 hφ2 hφ
  have he' : MulAut.congr (e.trans Φ) (MulAut.conjNormal t : MulAut ↥H) = φ := by
    ext x
    simp [hφdef, hτ, MulAut.congr_apply]
  obtain ⟨hJφ, hJ⟩ := PuL4GraphUni.component_transport hs (e.trans Φ)
  rw [he'] at hJφ hJ
  obtain ⟨Y, hY, σ, hσs, hσk, -⟩ := OIU.exists_lift_component h hAu hψ hψA hAA hJφ hJ
  obtain ⟨eLX⟩ := PuL4GraphUni.exists_equiv_image (hs.comp.1.trans inf_le_left) (e.trans Φ)
    (CFSG.ComponentClassification.GSThmB.Catalog7L4EU.ιU h)
    (CFSG.ComponentClassification.GSThmB.Catalog7L4EU.ιU_injective h)
  rcases PuL4GraphUniForm.uni_anti_cases h hp2 hAu hAA hY σ hσs hσk with
    ⟨-, ⟨eY⟩⟩ | ⟨E', _, _, hE', ⟨e2⟩⟩ | ⟨ρ, hρk⟩
  · exact PuL4GraphUniSplit.false_of_uni_split hs h.prime hp2 h.one_le h.card_fixedField hq3 eY σ
      hσs hσk eLX
  · exact PuL4GraphUniNonsplit.false_of_uni_nonsplit hs h.prime hp2 h.one_le hq3
      (by rw [hE', h.card_fixedField]) e2 eLX
  · have h2 : (2 : h.fixedField) ≠ 0 := fun h0 => by
      have h1 := congrArg h.fixedField.subtype h0
      rw [map_ofNat, map_zero] at h1
      exact two_ne_zero_of_odd h hp2 h1
    exact PuL4GraphUniAlt.false_of_sp_cover hs htH h2 (eLX.symm.toMonoidHom.comp ρ)
      (fun x hx => hρk (MonoidHom.mem_ker.mpr
        ((MulEquiv.map_eq_one_iff eLX.symm).mp
          (show eLX.symm (ρ x) = 1 from MonoidHom.mem_ker.mp hx)))) h4

end Certified

end CFSG.GH74.Generic.BProg.B2
