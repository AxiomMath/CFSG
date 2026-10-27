module

public import CFSG.HardMathSupport.Solomon.Coordinator.T112TF9Std
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

variable {F : Type} [Field F]

theorem nineFix_conj {S : Subgroup (GL (Fin 3) F)} {Ψ : GL (Fin 3) F →* GL (Fin 3) F}
    (h : NineFix S Ψ) (M : GL (Fin 3) F) (hM : ∀ x ∈ S, M * x * M⁻¹ ∈ S) :
    NineFix S ((MulAut.conj M).toMonoidHom.comp (Ψ.comp (MulAut.conj M⁻¹).toMonoidHom)) := by
  obtain ⟨T, P, Q, hTS, hQS, hPQ, hT, hT2, hPT, ⟨eP⟩, ⟨eQ⟩, hΨT, k, hk⟩ := h
  let c : GL (Fin 3) F ≃* GL (Fin 3) F := MulAut.conj M
  have hinj : Function.Injective c.toMonoidHom := c.injective
  have hc : ∀ x, c x = M * x * M⁻¹ := fun x => rfl
  have hcc : ∀ x, c (MulAut.conj M⁻¹ x) = x := fun x => by
    simp only [c, MulAut.conj_apply]; group
  have hcc' : ∀ x, MulAut.conj M⁻¹ (c x) = x := fun x => by
    simp only [c, MulAut.conj_apply]; group
  refine ⟨T.map c.toMonoidHom, P.map c.toMonoidHom, Q.map c.toMonoidHom, ?_, ?_, ?_, ?_, ?_, ?_,
    ⟨(P.equivMapOfInjective _ hinj).symm.trans eP⟩,
    ⟨(Q.equivMapOfInjective _ hinj).symm.trans eQ⟩, ?_, k, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hM x (hTS hx)
  · rintro _ ⟨x, hx, rfl⟩
    exact hM x (hQS hx)
  · exact Subgroup.map_mono hPQ
  · intro h0
    exact hT ((Subgroup.map_eq_bot_iff_of_injective T hinj).1 h0)
  · exact hT2.of_equiv (T.equivMapOfInjective _ hinj)
  · rintro _ ⟨x0, hx0, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv, map_mul, map_mul, map_inv]
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    exact Subgroup.mem_normalizer_iff.1 (hPT hx0) _
  · rw [Subgroup.map_map]
    have : ((MulAut.conj M).toMonoidHom.comp (Ψ.comp (MulAut.conj M⁻¹).toMonoidHom)).comp
        c.toMonoidHom = c.toMonoidHom.comp Ψ := by
      refine MonoidHom.ext fun x => ?_
      exact congrArg c (congrArg Ψ (hcc' x))
    rw [this, ← Subgroup.map_map, hΨT]
  · rintro _ ⟨q, hq, rfl⟩
    change c (Ψ (MulAut.conj M⁻¹ (c q))) = (c q) ^ k
    rw [hcc', hk q hq, map_pow]

theorem nine_of_nineFix {K : Type} [Group K] {S : Subgroup (GL (Fin 3) F)} (e : K ≃* ↥S)
    (ψ : MulAut K) {Ψ : GL (Fin 3) F →* GL (Fin 3) F}
    (hψ : ∀ x : K, ((e (ψ x) : ↥S) : GL (Fin 3) F) = Ψ ((e x : ↥S) : GL (Fin 3) F))
    (h : NineFix S Ψ) :
    ∃ T P Q : Subgroup K, T ≠ ⊥ ∧ IsPGroup 2 T ∧ P ≤ Subgroup.normalizer (T : Set K) ∧
      Nonempty (P ≃* Multiplicative (ZMod 9)) ∧
      Nonempty (Q ≃* Multiplicative (ZMod 9 × ZMod 9)) ∧ P ≤ Q ∧
      T.map ψ.toMonoidHom = T ∧ ∃ k : ℕ, ∀ x ∈ Q, ψ x = x ^ k := by
  obtain ⟨T, P, Q, hTS, hQS, hPQ, hT, hT2, hPT, ⟨eP⟩, ⟨eQ⟩, hΨT, k, hk⟩ := h
  have hPS : P ≤ S := hPQ.trans hQS
  let pb : Subgroup (GL (Fin 3) F) → Subgroup K := fun A =>
    (A.subgroupOf S).map e.symm.toMonoidHom
  have hmem : ∀ A x, x ∈ pb A ↔ ((e x : ↥S) : GL (Fin 3) F) ∈ A := fun A x => by
    change x ∈ (A.subgroupOf S).map e.symm.toMonoidHom ↔ _
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm, Subgroup.mem_subgroupOf]
  have hequiv : ∀ A : Subgroup (GL (Fin 3) F), A ≤ S → Nonempty (pb A ≃* A) := fun A hA =>
    ⟨((A.subgroupOf S).equivMapOfInjective _ e.symm.injective).symm.trans
      (Subgroup.subgroupOfEquivOfLe hA)⟩
  have hbot : ∀ A : Subgroup (GL (Fin 3) F), A ≤ S → A ≠ ⊥ → pb A ≠ ⊥ := by
    intro A hA hne h0
    apply hne
    rw [eq_bot_iff]
    intro a ha
    have hx : e.symm ⟨a, hA ha⟩ ∈ pb A := by
      rw [hmem]
      simpa using ha
    rw [h0, Subgroup.mem_bot] at hx
    have : (⟨a, hA ha⟩ : ↥S) = 1 := by
      rw [← e.symm.map_eq_one_iff (x := (⟨a, hA ha⟩ : ↥S))]
      exact hx
    simpa using congrArg Subtype.val this
  refine ⟨pb T, pb P, pb Q, hbot T hTS hT, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨eT⟩ := hequiv T hTS
    exact hT2.of_equiv eT.symm
  · intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [hmem, hmem, map_mul, map_mul, map_inv]
    exact Subgroup.mem_normalizer_iff.1 (hPT ((hmem P x).1 hx)) _
  · obtain ⟨eP'⟩ := hequiv P hPS
    exact ⟨eP'.trans eP⟩
  · obtain ⟨eQ'⟩ := hequiv Q hQS
    exact ⟨eQ'.trans eQ⟩
  · intro x hx
    exact (hmem Q x).2 (hPQ ((hmem P x).1 hx))
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine (hmem T _).2 ?_
      change ((e (ψ x) : ↥S) : GL (Fin 3) F) ∈ T
      rw [hψ]
      have := (hmem T x).1 hx
      rw [← hΨT]
      exact ⟨_, this, rfl⟩
    · intro hy
      have hy' := (hmem T y).1 hy
      rw [← hΨT] at hy'
      obtain ⟨t, ht, hty⟩ := hy'
      refine ⟨e.symm ⟨t, hTS ht⟩, ?_, ?_⟩
      · rw [SetLike.mem_coe, hmem]
        simpa using ht
      · apply e.injective
        apply Subtype.ext
        change ((e (ψ (e.symm ⟨t, hTS ht⟩)) : ↥S) : GL (Fin 3) F) = _
        rw [hψ]
        simpa using hty
  · refine ⟨k, fun x hx => ?_⟩
    apply e.injective
    apply Subtype.ext
    rw [hψ, hk _ ((hmem Q x).1 hx), map_pow]
    rfl

end CFSG.HardMathSupport.Solomon.Coordinator
