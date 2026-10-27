module

public import CFSG.HardMathSupport.Dickson.KD.CharPAux.ClassA
public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreTwistedA

public section

namespace CFSG.HardMathSupport.Dickson.KD

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.HardMathSupport.Timmesfeld.DefChar.TwA CFSG.HardMathSupport.Timmesfeld.DefChar.Orth

section TwA

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ} {h : UnitaryFieldData p f K}

@[expose] def suRep (h : UnitaryFieldData p f K) (n : ℕ) :
    gramSU h (Cm n K) →* Module.End K (Fin n → K) :=
  (glRep (Fin n) K).comp (gramSU h (Cm n K)).subtype

theorem suRep_injective : Function.Injective (suRep h n) :=
  glRep_injective.comp Subtype.val_injective

theorem mem_flagSub_of_flag {N : Matrix (Fin n) (Fin n) K} {s : gramSU h (Cm n K)}
    (hf : Flag N (smat s - 1)) (hc : N * smat s = smat s * N) :
    s ∈ flagSub (suRep h n) (Matrix.toLin' N) := by
  show InFlag (Matrix.toLin' N) (Matrix.toLin' (smat s))
  have hsub : ∀ x, Matrix.toLin' (smat s) x - x = (smat s - 1) *ᵥ x := fun x => by
    rw [Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec]
  refine ⟨fun x => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.toLin'_apply,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hc]
  · have hx' : N *ᵥ x = 0 := by rwa [LinearMap.mem_ker, Matrix.toLin'_apply] at hx
    rw [hsub]
    exact mem_Wsp_iff.1 (hf.2.1 x hx')
  · have hw : x ∈ Wsp N := mem_Wsp_iff.2 hx
    have := hf.2.2 x hw
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at this
    rw [Matrix.toLin'_apply]
    exact this

theorem su_mem_flagSub {N : Matrix (Fin n) (Fin n) K} {u : gramSU h (Cm n K)}
    (hu : smat u = 1 + N) : u ∈ flagSub (suRep h n) (Matrix.toLin' N) := by
  show InFlag (Matrix.toLin' N) (Matrix.toLin' (smat u))
  rw [hu, map_add, Matrix.toLin'_one]
  refine inFlag_one_add rfl ?_ ?_
  · intro x hx
    rw [LinearMap.mem_ker.1 hx]
    exact Submodule.zero_mem _
  · intro x hx
    exact LinearMap.mem_ker.1 hx.1

theorem comm_of_conj_fix {G : Type*} [Group G] {s q : G} (h : (MulAut.conj s : MulAut G) q = q) :
    s * q = q * s := by
  have := h
  rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at this
  exact this

theorem frame_primeFormP [NeZero n] (hn : 3 ≤ n) (hp2 : p ≠ 2) (y : primeFormP h (Cm n K))
    (hy : orderOf y = p) : Frame p y := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  haveI : CharP K p := h.charP
  obtain ⟨u, N, hu1, hN, hN0, hUN, hu⟩ := exists_unipotent_lift (h := h) y hy
  refine ⟨GenSet h N, {y}, ?_, ?_, ?_, ?_, ?_⟩
  · rintro q (hq | hq)
    · rw [← hu1]
      exact GenSet_comm hu hq
    · rw [Set.mem_singleton_iff.1 hq]
  · intro s q hs hq
    rw [Set.mem_singleton_iff.1 hq]
    exact hs
  · intro s q hs hq
    obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective s
    have hs' : (σ : primeFormP h (Cm n K)) * (u : primeFormP h (Cm n K)) =
        (u : primeFormP h (Cm n K)) * (σ : primeFormP h (Cm n K)) := by
      rw [hσ, hu1]; exact hs
    have hσN := commute_lift hN hu hs'
    have := GenSet_conj hσN hq
    rw [← hσ]
    exact this
  · intro s hs hfix
    obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective s
    have hs' : (σ : primeFormP h (Cm n K)) * (u : primeFormP h (Cm n K)) =
        (u : primeFormP h (Cm n K)) * (σ : primeFormP h (Cm n K)) := by
      rw [hσ, hu1]
      exact comm_of_conj_fix (hfix y (Or.inr rfl))
    have hcop' : (orderOf (σ : primeFormP h (Cm n K))).Coprime p := by rw [hσ]; exact hs
    have h1 := uniq_inner hn hp2 hN hN0 hUN hu σ hs' hcop' (by
      intro q hq
      rw [hσ]
      exact comm_of_conj_fix (hfix q (Or.inl hq)))
    rw [hσ] at h1
    rw [h1, map_one]
  · refine isPGroup_closure_of_subset_map suRep_injective (isNilpotent_toLin' hN)
      (QuotientGroup.mk' (normOneScalars h (gramSU h (Cm n K)) n)) ?_
    rintro q (⟨s, rfl, hf, hc⟩ | hq)
    · exact ⟨s, mem_flagSub_of_flag hf hc, rfl⟩
    · rw [Set.mem_singleton_iff.1 hq, ← hu1]
      exact ⟨u, su_mem_flagSub hu, rfl⟩

end TwA

theorem kdCharPAt_twistedA (q : TauCeti.PrimePower) (r : ℕ)
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid) {p : ℕ} (hp2 : p ≠ 2) (hpq : p = q.p) :
    KDCharPAt p (TauCeti.CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv
    (MulEquiv.refl (TauCeti.ValidLieTypeIndex.Group ⟨.twistedA r q, hv⟩))
  have hS := (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ (r + 1) q.p q.exponent hm).2
  obtain ⟨⟨hℓ, hf, hn, hq⟩, K, _, _, hK, ⟨eT⟩⟩ := hm
  have h : UnitaryFieldData q.p q.exponent K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq' : ¬(r + 1 = 3 ∧ q.p ^ q.exponent = 2) := fun ⟨h1, h2⟩ => hq (by rw [h1, h2])
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_one (n := r + 1) (K := K))
  let e : (TauCeti.CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group ≃* primeFormP h (Cm (r + 1) K) :=
    (eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm
  subst hpq
  have hn3 : 3 ≤ r + 1 := by omega
  haveI : NeZero (r + 1) := ⟨by omega⟩
  haveI : IsSimpleGroup (TauCeti.ValidLieTypeIndex.Group ⟨.twistedA r q, hv⟩) := hS
  exact kdCharPAt_of_frame_simple e e.symm.isSimpleGroup fun y hy => frame_primeFormP hn3 hp2 y hy

end CFSG.HardMathSupport.Dickson.KD
