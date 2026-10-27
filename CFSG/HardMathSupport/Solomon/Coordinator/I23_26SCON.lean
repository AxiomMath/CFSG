module

public import CFSG.HardMathSupport.Solomon.Coordinator.I23_26SCL3
public import CFSG.HardMathSupport.Solomon.Coordinator.ONAut
public import CFSG.Sporadic.Schreier.SteinbergBIONOuterTwo

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def ONOuterTwo : Prop :=
  ∀ (X : Type) [Group X] [Finite X], commutator X = ⊤ →
    Nonempty ((X ⧸ Subgroup.center X) ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group) →
    (MulAut.conj : X →* MulAut X).range.index ∣ 2

theorem onOuterTwo_holds :
    ONOuterTwo := by
  intro X _ _ hperf ⟨e⟩
  obtain ⟨b0⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  have b : CFSG.Blueprint.NativeSporadic.ON ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group := b0
  have hout : Nat.card (Outer (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group) ∣ 2 :=
    CFSG.Sporadic.SteinbergBI.cti_on_outer_order_divides_two ⟨b.symm⟩
  let f : MulAut X →* MulAut (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group :=
    (MulAut.congr e).toMonoidHom.comp (mulAutQuotCenter X)
  have hf : Function.Injective f :=
    (MulAut.congr e).injective.comp (mulAutQuotCenter_injective hperf)
  have hconj : ∀ x : X, f (MulAut.conj x) = MulAut.conj (e (QuotientGroup.mk x)) := by
    intro x
    have h1 : mulAutQuotCenter X (MulAut.conj x) = MulAut.conj (QuotientGroup.mk x) := by
      apply MulEquiv.ext
      intro q
      induction q using QuotientGroup.induction_on with
      | H y => rfl
    show MulAut.congr e (mulAutQuotCenter X (MulAut.conj x)) = _
    rw [h1, congr_conj]
  have hEq : (MulAut.conj : X →* MulAut X).range =
      (inner (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group).comap f := by
    ext α
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨e (QuotientGroup.mk x), (hconj x).symm⟩
    · rintro ⟨t, ht⟩
      obtain ⟨q, rfl⟩ := e.surjective t
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨x, hf (by rw [hconj x]; exact ht)⟩
  rw [hEq, Subgroup.index_comap]
  exact (Subgroup.relIndex_dvd_index_of_normal _ _).trans hout

section Inner

variable {Y : Type*} [Group Y]

theorem i2326o_conj_eq_one_iff {g : Y} : MulAut.conj g = 1 ↔ g ∈ Subgroup.center Y := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h x
    have := congrArg (fun φ : MulAut Y => φ x) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  · intro h
    ext x
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [mul_inv_eq_iff_eq_mul]
    exact (h x).symm

theorem i2326o_normal_inner : (MulAut.conj : Y →* MulAut Y).range.Normal where
  conj_mem := by
    rintro _ ⟨y, rfl⟩ φ
    refine ⟨φ y, ?_⟩
    ext z
    simp [MulAut.conj_apply]

theorem i2326o_mem_inner {α : MulAut Y}
    (h : (MulAut.conj : Y →* MulAut Y).range.index ∣ 2) (h3 : α ^ 3 = 1) :
    α ∈ (MulAut.conj : Y →* MulAut Y).range := by
  have := i2326o_normal_inner (Y := Y)
  have h1 := Subgroup.pow_index_mem (MulAut.conj : Y →* MulAut Y).range α
  obtain ⟨c, hc⟩ := h
  have h2 : α ^ 2 ∈ (MulAut.conj : Y →* MulAut Y).range := by
    rw [hc, pow_mul]
    exact Subgroup.pow_mem _ h1 c
  have h4 : α ^ 2 = α⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ]
    exact h3
  rw [h4] at h2
  simpa using inv_mem h2

end Inner

section Main

variable {X : Type} [Group X] [Finite X]

theorem i2326o_sc_ON (hB : ONGeneration) (hOut : ONOuterTwo) {K E : Subgroup X}
    (hK : IsComponentOf K ⊤)
    (hT : Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group))
    (hE : IsElemAbelian 3 E) (h27 : Nat.card E = 27) (hN : E ≤ Subgroup.normalizer (K : Set X))
    (hfaith : ∀ e ∈ E, (∀ k ∈ K, e * k = k * e) → e = 1) :
    K ≤ ⨆ (e : X) (_ : e ∈ E) (_ : e ≠ 1), GLAPLayer 3 (K ⊓ Subgroup.centralizer ({e} : Set X)) := by
  have hq : CFSG.Open.IsQuasisimple ↥K := hK.2.2
  set ρ := i2326sRho K E hN with hρdef
  have hinj : Function.Injective ρ := i2326sRho_injective hN hfaith
  have hEbar := i2326sRho_isElemAbelian hN hE
  have hcard : Nat.card ρ.range = 27 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact h27
  have hInn : (MulAut.conj : ↥K →* MulAut ↥K).range.index ∣ 2 := hOut ↥K hq.1 hT
  have hmemInn : ∀ α ∈ ρ.range, α ∈ (MulAut.conj : ↥K →* MulAut ↥K).range := fun α hα =>
    i2326o_mem_inner hInn (hEbar.2 α hα)
  set ψ : (↥K ⧸ Subgroup.center ↥K) →* MulAut ↥K :=
    QuotientGroup.lift (Subgroup.center ↥K) (MulAut.conj : ↥K →* MulAut ↥K) (fun z hz =>
      i2326o_conj_eq_one_iff.2 hz) with hψ
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro q hq1
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    have : (MulAut.conj k : MulAut ↥K) = 1 := hq1
    exact (QuotientGroup.eq_one_iff k).2 (i2326o_conj_eq_one_iff.1 this)
  have hψmk : ∀ k : ↥K, ψ (QuotientGroup.mk k) = MulAut.conj k := fun k => rfl
  set B : Subgroup ↥K := ρ.range.comap (MulAut.conj : ↥K →* MulAut ↥K) with hBdef
  have hBmap : (B.map (QuotientGroup.mk' (Subgroup.center ↥K))).map ψ = ρ.range := by
    ext α
    constructor
    · rintro ⟨q, ⟨k, hk, rfl⟩, rfl⟩
      exact hk
    · intro hα
      obtain ⟨k, hk⟩ := hmemInn α hα
      refine ⟨QuotientGroup.mk k, ⟨k, ?_, rfl⟩, ?_⟩
      · show (MulAut.conj : ↥K →* MulAut ↥K) k ∈ ρ.range
        rw [hk]
        exact hα
      · exact hk.symm ▸ hψmk k
  have hBcard : Nat.card (B.map (QuotientGroup.mk' (Subgroup.center ↥K))) = 27 := by
    rw [← hcard, ← hBmap, Subgroup.card_map_of_injective hψinj]
  have hBea : IsElemAbelian 3 (B.map (QuotientGroup.mk' (Subgroup.center ↥K))) := by
    refine ⟨⟨⟨fun u v => ?_⟩⟩, fun u hu => ?_⟩
    · apply Subtype.ext
      apply hψinj
      have hu' : ψ (u : ↥K ⧸ Subgroup.center ↥K) ∈ ρ.range := by
        rw [← hBmap]; exact ⟨u, u.2, rfl⟩
      have hv' : ψ (v : ↥K ⧸ Subgroup.center ↥K) ∈ ρ.range := by
        rw [← hBmap]; exact ⟨v, v.2, rfl⟩
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact elemAbelian_comm hEbar hu' hv'
    · apply hψinj
      have hu' : ψ u ∈ ρ.range := by
        rw [← hBmap]; exact ⟨u, hu, rfl⟩
      rw [map_pow, hEbar.2 _ hu', map_one]
  have hONG := hB ↥K hq hT B hBea hBcard
  have hK' : K = (⊤ : Subgroup ↥K).map K.subtype := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  have h1 := Subgroup.map_mono (f := K.subtype) hONG
  rw [← hK'] at h1
  refine h1.trans ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun b => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hbB => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hbZ => ?_
  obtain ⟨e, he⟩ := (show (MulAut.conj : ↥K →* MulAut ↥K) b ∈ ρ.range from hbB)
  have hbne : (MulAut.conj : ↥K →* MulAut ↥K) b ≠ 1 := fun h => hbZ (i2326o_conj_eq_one_iff.1 h)
  have hene : (e : X) ≠ 1 := by
    intro h
    apply hbne
    rw [← he]
    have : e = 1 := Subtype.ext h
    rw [this, map_one]
  have hcent : Subgroup.centralizer ({b} : Set ↥K) = Lemma512Ns.fixedSub (ρ e) := by
    ext k
    rw [Subgroup.mem_centralizer_singleton_iff]
    show _ ↔ ρ e k = k
    rw [he]
    simp only [MulAut.conj_apply]
    rw [mul_inv_eq_iff_eq_mul]
    exact eq_comm
  have hmap : (Lemma512Ns.fixedSub (ρ e)).map K.subtype =
      K ⊓ Subgroup.centralizer ({(e : X)} : Set X) :=
    i2326sAct_fixedSub K (Subgroup.inclusion hN e)
  rw [hcent, ← i2326s_layer_map, hmap]
  exact le_iSup_of_le (e : X) (le_iSup_of_le e.2 (le_iSup_of_le hene le_rfl))

end Main

end CFSG.HardMathSupport.Solomon.Coordinator
