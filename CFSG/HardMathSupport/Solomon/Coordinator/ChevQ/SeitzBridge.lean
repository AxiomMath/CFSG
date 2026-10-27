module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Gen
import CFSG.LieType.SeitzGeneration.UnitaryHyperDiag
import CFSG.Adapters.TauCetiLieModels
public import CFSG.LieType.SeitzGeneration.HyperLeaf

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration CFSG.Open CFSG.AGLEmbedding
  CFSG.LocalAnalysis.GLTheoremB

@[expose] def SeitzHyperGood : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (Y : Type) [Group Y] [Finite Y] (K E : Subgroup Y), K.Normal →
    CFSG.Open.IsQuasisimple K → ∀ d : TauCeti.ValidLieTypeIndex,
    Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
    p ≠ d.1.characteristic → ¬ P1ThreeLieList p d →
    ¬ (p = 3 ∧ ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 2 ∧ d.1 = .A 2 q) →
    IsElemAbelian p E → Nat.card E = p ^ 3 →
    (∀ c ∈ E ⊓ Subgroup.centralizer (K : Set Y), orderOf c = p →
      c ∈ (Subgroup.center K).map K.subtype) →
    (¬ ExcIndex p d.1 ∨ (IsSixIndex d.1 ∧ E ≤ K ⊔ Subgroup.centralizer (K : Set Y))) →
    HyperGen p K E

@[expose] def Seitz2310CubeSimple : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S →
    (∃ a b : S, a * b ≠ b * a) → ∀ (d : TauCeti.ValidLieTypeIndex),
    Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) → p ≠ d.1.characteristic →
    ¬ (p = 3 ∧ IsLThreeFour S) →
    ∀ E : Subgroup (MulAut S), IsElemAbelian p E → Nat.card E = p ^ 3 →
      (¬ ExcIndex p d.1 ∨ (IsSixIndex d.1 ∧ E ≤ (MulAut.conj : S →* MulAut S).range)) →
        seitzHyperGamma p E = ⊤

@[expose] def Seitz3D48Cube : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower), IsTwoPow q 3 →
      d.1 = .trialityD4 q → Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ E : Subgroup (MulAut S), IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
        seitzHyperGamma 3 E = ⊤

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzBridgeAux

open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration CFSG.Open CFSG.AGLEmbedding
  CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

section Holomorph

variable (S : Type) [Group S] (E : Subgroup (MulAut S))

abbrev Hol : Type := S ⋊[E.subtype] E

def holK : Subgroup (Hol S E) := (SemidirectProduct.inl : S →* Hol S E).range

def holE : Subgroup (Hol S E) := (SemidirectProduct.inr : ↥E →* Hol S E).range

instance holK_normal : (holK S E).Normal := by
  unfold holK
  rw [SemidirectProduct.range_inl_eq_ker_rightHom]
  infer_instance

instance [Finite S] [Finite E] : Finite (Hol S E) :=
  Finite.of_equiv (S × E) SemidirectProduct.equivProd.symm

variable {S E}

theorem mem_holK {x : Hol S E} : x ∈ holK S E ↔ ∃ s : S, SemidirectProduct.inl s = x := Iff.rfl

theorem mem_holE {x : Hol S E} : x ∈ holE S E ↔ ∃ f : E, SemidirectProduct.inr f = x := Iff.rfl

theorem inr_mul_inl_mul_inr_inv (f : E) (s : S) :
    (SemidirectProduct.inr f : Hol S E) * SemidirectProduct.inl s *
      (SemidirectProduct.inr f)⁻¹ = SemidirectProduct.inl ((f : MulAut S) s) := by
  rw [← map_inv, ← SemidirectProduct.inl_aut]
  rfl

end Holomorph

section Converse

variable {S : Type} [Group S] {E : Subgroup (MulAut S)}

theorem seitzHyperGamma_eq_top_of_hyperGen (p : ℕ)
    (h : HyperGen p (holK S E) (holE S E)) : seitzHyperGamma p E = ⊤ := by
  classical
  rw [← closure_eq_seitzHyperGamma]
  set G : Set S := {s : S | ∃ F ≤ E, F.relIndex E = p ∧ ∀ f ∈ F, f s = s} with hG
  have hinj : Function.Injective (SemidirectProduct.inl : S →* Hol S E) :=
    SemidirectProduct.inl_injective
  have hrinj : Function.Injective (SemidirectProduct.inr : ↥E →* Hol S E) :=
    SemidirectProduct.inr_injective
  have hle : Subgroup.closure {k : Hol S E | k ∈ holK S E ∧ ∃ F : Subgroup (Hol S E),
      F ≤ holE S E ∧ F.relIndex (holE S E) = p ∧ ∀ f ∈ F, f * k = k * f} ≤
      (Subgroup.closure G).map (SemidirectProduct.inl : S →* Hol S E) := by
    rw [Subgroup.closure_le]
    rintro k ⟨⟨s, rfl⟩, F, hFE, hrel, hcomm⟩
    refine ⟨s, Subgroup.subset_closure ?_, rfl⟩
    refine ⟨(F.comap (SemidirectProduct.inr : ↥E →* Hol S E)).map E.subtype, ?_, ?_, ?_⟩
    · exact Subgroup.map_subtype_le _
    · have hF1 : (F.comap (SemidirectProduct.inr : ↥E →* Hol S E)).map
          (SemidirectProduct.inr : ↥E →* Hol S E) = F :=
        Subgroup.map_comap_eq_self hFE
      have hE1 : (⊤ : Subgroup ↥E).map (SemidirectProduct.inr : ↥E →* Hol S E) = holE S E := by
        rw [Subgroup.map_top]
        rfl
      have h2 : (F.comap (SemidirectProduct.inr : ↥E →* Hol S E)).relIndex ⊤ = p :=
        calc (F.comap (SemidirectProduct.inr : ↥E →* Hol S E)).relIndex ⊤
            = ((F.comap (SemidirectProduct.inr : ↥E →* Hol S E)).map
                (SemidirectProduct.inr : ↥E →* Hol S E)).relIndex
                ((⊤ : Subgroup ↥E).map (SemidirectProduct.inr : ↥E →* Hol S E)) :=
              (Subgroup.relIndex_map_map_of_injective _ _ hrinj).symm
          _ = F.relIndex (holE S E) := by rw [hF1, hE1]
          _ = p := hrel
      have h3 : (⊤ : Subgroup ↥E).map E.subtype = E := by
        rw [Subgroup.map_top, Subgroup.range_subtype]
      calc ((F.comap (SemidirectProduct.inr : ↥E →* Hol S E)).map E.subtype).relIndex E
          = ((F.comap (SemidirectProduct.inr : ↥E →* Hol S E)).map E.subtype).relIndex
              ((⊤ : Subgroup ↥E).map E.subtype) := by rw [h3]
        _ = (F.comap (SemidirectProduct.inr : ↥E →* Hol S E)).relIndex ⊤ :=
            Subgroup.relIndex_map_map_of_injective _ _ E.subtype_injective
        _ = p := h2
    · rintro _ ⟨f, hf, rfl⟩
      have hfF : (SemidirectProduct.inr f : Hol S E) ∈ F := hf
      have h1 := hcomm _ hfF
      have h2 := inr_mul_inl_mul_inr_inv f s
      rw [mul_inv_eq_iff_eq_mul, h1] at h2
      exact (hinj (mul_right_cancel h2)).symm
  rw [eq_top_iff]
  intro x _
  have hx : (SemidirectProduct.inl x : Hol S E) ∈ holK S E := ⟨x, rfl⟩
  obtain ⟨y, hy, hyx⟩ := hle (h hx)
  exact hinj hyx ▸ hy

end Converse

section Simple

variable {S : Type} [Group S]

theorem center_eq_bot_of_simple (hs : IsSimpleGroup S) (hnab : ∃ a b : S, a * b ≠ b * a) :
    Subgroup.center S = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have ha : a ∈ Subgroup.center S := h ▸ Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.1 ha b).symm

theorem isQuasisimple_of_simple (hs : IsSimpleGroup S) (hnab : ∃ a b : S, a * b ≠ b * a) :
    CFSG.Open.IsQuasisimple S := by
  have hZ := center_eq_bot_of_simple hs hnab
  refine ⟨?_, ?_⟩
  · rcases hs.eq_bot_or_eq_top_of_normal (commutator S) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have h1 : ⁅a, b⁆ ∈ commutator S :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot] at h1
      exact hab (commutatorElement_eq_one_iff_mul_comm.1 h1)
    · exact h
  · have e : S ≃* (S ⧸ Subgroup.center S) :=
      (QuotientGroup.quotientBot.symm).trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
    haveI := hs
    exact MulEquiv.isSimpleGroup e.symm

end Simple

section HolData

variable {S : Type} [Group S] {E : Subgroup (MulAut S)}

noncomputable def holKEquiv (S : Type) [Group S] (E : Subgroup (MulAut S)) :
    S ≃* ↥(holK S E) :=
  MonoidHom.ofInjective SemidirectProduct.inl_injective

noncomputable def holEEquiv (S : Type) [Group S] (E : Subgroup (MulAut S)) :
    ↥E ≃* ↥(holE S E) :=
  MonoidHom.ofInjective SemidirectProduct.inr_injective

theorem holK_isQuasisimple (hs : IsSimpleGroup S) (hnab : ∃ a b : S, a * b ≠ b * a) :
    CFSG.Open.IsQuasisimple ↥(holK S E) :=
  CFSG.Open.IsQuasisimple.of_mulEquiv (holKEquiv S E).symm (isQuasisimple_of_simple hs hnab)

theorem holK_center_eq_bot (hs : IsSimpleGroup S) (hnab : ∃ a b : S, a * b ≠ b * a) :
    Subgroup.center ↥(holK S E) = ⊥ := by
  have h := Subgroup.map_center_eq (holKEquiv S E)
  rw [center_eq_bot_of_simple hs hnab, Subgroup.map_bot] at h
  exact h.symm

theorem holK_quot_equiv (hs : IsSimpleGroup S) (hnab : ∃ a b : S, a * b ≠ b * a)
    {C : Type} [Group C] (e : S ≃* C) :
    Nonempty (↥(holK S E) ⧸ Subgroup.center ↥(holK S E) ≃* C) :=
  ⟨((QuotientGroup.quotientMulEquivOfEq (holK_center_eq_bot hs hnab (E := E))).trans
    QuotientGroup.quotientBot).trans ((holKEquiv S E).symm.trans e)⟩

theorem card_holE : Nat.card ↥(holE S E) = Nat.card ↥E :=
  (Nat.card_congr (holEEquiv S E).toEquiv).symm

theorem isElemAbelian_holE {p : ℕ} (hE : IsElemAbelian p E) : IsElemAbelian p (holE S E) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
  · obtain ⟨f, hf⟩ := mem_holE.1 a.2
    obtain ⟨g, hg⟩ := mem_holE.1 b.2
    apply Subtype.ext
    change (a : Hol S E) * b = b * a
    rw [← hf, ← hg, ← map_mul, ← map_mul, hE.1.is_comm.comm f g]
  · obtain ⟨f, rfl⟩ := mem_holE.1 hy
    rw [← map_pow]
    have : f ^ p = 1 := Subtype.ext (hE.2 f f.2)
    rw [this, map_one]

theorem holE_inf_centralizer_eq_bot :
    holE S E ⊓ Subgroup.centralizer (holK S E : Set (Hol S E)) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxE, hxC⟩
  obtain ⟨f, rfl⟩ := mem_holE.1 hxE
  rw [Subgroup.mem_bot]
  have hfix : ∀ s : S, (f : MulAut S) s = s := fun s => by
    have h1 := Subgroup.mem_centralizer_iff.1 hxC (SemidirectProduct.inl s) ⟨s, rfl⟩
    have h2 := inr_mul_inl_mul_inr_inv f s
    rw [mul_inv_eq_iff_eq_mul, ← h1] at h2
    exact (SemidirectProduct.inl_injective (mul_right_cancel h2)).symm
  have : f = 1 := Subtype.ext (MulEquiv.ext hfix)
  rw [this, map_one]

theorem holE_le_sup_of_inner (hinn : E ≤ (MulAut.conj : S →* MulAut S).range) :
    holE S E ≤ holK S E ⊔ Subgroup.centralizer (holK S E : Set (Hol S E)) := by
  rintro _ ⟨f, rfl⟩
  obtain ⟨s, hs⟩ := hinn f.2
  have hfs : ∀ t : S, (f : MulAut S) t = s * t * s⁻¹ := fun t => by
    rw [← hs]
    rfl
  have hK : (SemidirectProduct.inl s : Hol S E) ∈ holK S E := ⟨s, rfl⟩
  have hC : (SemidirectProduct.inl s⁻¹ : Hol S E) * SemidirectProduct.inr f ∈
      Subgroup.centralizer (holK S E : Set (Hol S E)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨t, rfl⟩
    have h1 : (SemidirectProduct.inr f : Hol S E) * SemidirectProduct.inl t =
        SemidirectProduct.inl (s * t * s⁻¹) * SemidirectProduct.inr f := by
      have := inr_mul_inl_mul_inr_inv f t
      rw [hfs t, mul_inv_eq_iff_eq_mul] at this
      exact this
    have h2 : (SemidirectProduct.inl s⁻¹ : Hol S E) * SemidirectProduct.inl (s * t * s⁻¹) =
        SemidirectProduct.inl t * SemidirectProduct.inl s⁻¹ := by
      rw [← map_mul, ← map_mul]
      congr 1
      group
    calc (SemidirectProduct.inl t : Hol S E) *
          (SemidirectProduct.inl s⁻¹ * SemidirectProduct.inr f)
        = (SemidirectProduct.inl t * SemidirectProduct.inl s⁻¹) * SemidirectProduct.inr f :=
          (mul_assoc _ _ _).symm
      _ = (SemidirectProduct.inl s⁻¹ * SemidirectProduct.inl (s * t * s⁻¹)) *
            SemidirectProduct.inr f := by rw [h2]
      _ = SemidirectProduct.inl s⁻¹ * (SemidirectProduct.inl (s * t * s⁻¹) *
            SemidirectProduct.inr f) := mul_assoc _ _ _
      _ = SemidirectProduct.inl s⁻¹ * (SemidirectProduct.inr f * SemidirectProduct.inl t) := by
            rw [h1]
      _ = (SemidirectProduct.inl s⁻¹ * SemidirectProduct.inr f) * SemidirectProduct.inl t :=
          (mul_assoc _ _ _).symm
  have h3 := Subgroup.mul_mem_sup hK hC
  have e1 : (SemidirectProduct.inl s : Hol S E) *
      (SemidirectProduct.inl s⁻¹ * SemidirectProduct.inr f) = SemidirectProduct.inr f := by
    rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  rwa [e1] at h3

end HolData

section Aut

variable {Fam : TauCeti.ValidLieTypeIndex → Prop} {p : ℕ} {S : Type} [Group S] [Finite S]
  {E : Subgroup (MulAut S)}

theorem seitzHyperGamma_eq_top_of_inner (hF : SeitzHyperInnerFor Fam) (hp : p.Prime) (hp2 : p ≠ 2)
    (hs : IsSimpleGroup S) (hnab : ∃ a b : S, a * b ≠ b * a) (d : TauCeti.ValidLieTypeIndex)
    (hd : Fam d) (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) (hpd : p ≠ d.1.characteristic)
    (hP : ¬ P1ThreeLieList p d) (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3)
    (hinn : E ≤ (MulAut.conj : S →* MulAut S).range) : seitzHyperGamma p E = ⊤ := by
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.ne_zero)
  refine seitzHyperGamma_eq_top_of_hyperGen p ?_
  refine hF p hp hp2 (Hol S E) (holK S E) (holE S E) inferInstance (holK_isQuasisimple hs hnab) d
    hd (holK_quot_equiv hs hnab e) hpd hP (isElemAbelian_holE hE) (by rw [card_holE, hcard]) ?_
    (holE_le_sup_of_inner hinn)
  intro c hc hco
  rw [holE_inf_centralizer_eq_bot, Subgroup.mem_bot] at hc
  rw [hc, orderOf_one] at hco
  exact absurd hco hp.one_lt.ne

end Aut

section Index

theorem p1_cases {p : ℕ} {d : TauCeti.ValidLieTypeIndex} (hpd : p ≠ d.1.characteristic)
    (hP : P1ThreeLieList p d) (hE : ¬ ExcIndex p d.1 ∨ IsSixIndex d.1) :
    p = 3 ∧ ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧
      (d.1 = .trialityD4 q ∨ d.1 = .twistedA 2 q) := by
  rcases hP with ⟨n, q, hd, hqp, -⟩ | ⟨q, hqp, hd⟩ | ⟨hp3, m, hd⟩ | ⟨q, h1 | h2⟩ | h
  · exact absurd (by rw [hd]; simpa using hqp.symm) hpd
  · exact absurd (by rw [hd]; simpa using hqp.symm) hpd
  · exact absurd (by rw [hd]; simpa using hp3) hpd
  · obtain ⟨hqp, -, hd⟩ := h1
    exact absurd (by rw [hd]; simpa using hqp.symm) hpd
  · obtain ⟨hp3, hq2, hq1, hd⟩ := h2
    subst hp3
    rcases hE with hE | hE
    · exact absurd (by rw [hd]; simp [ExcIndex, Bal207Index, IsTwoPow, hq2, hq1]) hE
    · rw [hd] at hE
      simp [IsSixIndex, IsF4EightIndex, IsD4FourIndex, FourIndex] at hE
  · rcases h with ⟨hp3, q, hq2, hq1, hd⟩ | ⟨hp3, q, hq2, hq3, hd⟩ | ⟨hp5, hd⟩
    · subst hp3
      exfalso
      rcases hE with hE | hE
      · refine hE ?_
        rcases hd with hd | hd | hd | hd | hd | hd | hd | hd <;> rw [hd] <;>
          simp [ExcIndex, Bal207Index, Gen2318Index, IsTwoPow, hq2, hq1]
      · rcases hd with hd | hd | hd | hd | hd | hd | hd | hd <;> rw [hd] at hE <;>
          simp [IsSixIndex, IsF4EightIndex, IsD4FourIndex, FourIndex, IsTwoPow, hq2, hq1] at hE
    · subst hp3
      rcases hd with hd | hd | hd | hd
      · exfalso
        rcases hE with hE | hE
        · exact hE (by rw [hd]; simp [ExcIndex, Bal207Index, IsTwoPow, hq2, hq3])
        · rw [hd] at hE
          simp [IsSixIndex, IsF4EightIndex, IsD4FourIndex, FourIndex] at hE
      · exfalso
        rcases hE with hE | hE
        · exact hE (by rw [hd]; simp [ExcIndex, Bal207Index, IsTwoPow, hq2, hq3])
        · rw [hd] at hE
          simp [IsSixIndex, IsF4EightIndex, IsD4FourIndex, FourIndex] at hE
      · exact ⟨rfl, q, hq2, hq3, Or.inl hd⟩
      · exact ⟨rfl, q, hq2, hq3, Or.inr hd⟩
    · subst hp5
      exfalso
      rcases hE with hE | hE
      · exact hE (by rw [hd]; simp [ExcIndex, Bal207Index])
      · rw [hd] at hE
        simp [IsSixIndex, IsF4EightIndex, IsD4FourIndex, FourIndex] at hE

end Index

section Residual

variable {S : Type} [Group S]

theorem conj_injective_of_simple' (hs : IsSimpleGroup S) (hnab : ∃ a b : S, a * b ≠ b * a) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  have hZ := center_eq_bot_of_simple hs hnab
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have hxz : x ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h := congrArg (fun φ : MulAut S => φ g) hx
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    exact (mul_inv_eq_iff_eq_mul.1 h).symm
  rwa [hZ] at hxz

theorem no_cube_in_inner_u38 [Finite S] (hs : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower)
    (hq : IsTwoPow q 3) (hd : d.1 = .twistedA 2 q) (e : S ≃* (TauCeti.CFSGIndex.lie d).Group)
    {E : Subgroup (MulAut S)} (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 3)
    (hinn : E ≤ (MulAut.conj : S →* MulAut S).range) : False := by
  obtain ⟨d₀, hv⟩ := d
  simp only at hd
  subst hd
  have hmod := CFSG.Models.lieModel_twistedA 2 q hv e
  have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩ = q.p :=
    TauCeti.LieTypeIndex.characteristic_twistedA 2 q
  have hf : TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩ = q.exponent :=
    TauCeti.LieTypeIndex.fieldExponent_twistedA 2 q
  rw [hc, hf, hq.1, hq.2] at hmod
  obtain ⟨-, hcl | ⟨h0, -⟩⟩ := hmod
  swap
  · omega
  obtain ⟨-, K, _, _, hK, ⟨eS⟩⟩ := hcl
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 3 K :=
    ⟨Nat.prime_two, by norm_num, by rw [hK]; norm_num⟩
  have hrank := pRank_three_projSU_three_le hU (by norm_num : 3 ∣ 2 ^ 3 + 1)
  have hS3 : CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ 2 :=
    (CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) eS).trans_le hrank
  have hinj := conj_injective_of_simple' hs hnab
  have hE0 : IsElemAbelian 3 (E.comap (MulAut.conj : S →* MulAut S)) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply hinj
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact congrArg Subtype.val (hE.1.is_comm.comm ⟨_, a.2⟩ ⟨_, b.2⟩)
    · apply hinj
      rw [map_pow, map_one]
      exact hE.2 _ hx
  have hcard0 : Nat.card (E.comap (MulAut.conj : S →* MulAut S)) = 3 ^ 3 := by
    have h1 : Nat.card ((E.comap (MulAut.conj : S →* MulAut S)).map
        (MulAut.conj : S →* MulAut S)) = Nat.card (E.comap (MulAut.conj : S →* MulAut S)) :=
      Subgroup.card_map_of_injective hinj
    rw [Subgroup.map_comap_eq_self hinn] at h1
    rw [← h1, hcard]
  have h3 : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) :=
    CFSG.SectionRank.le_pRank (by norm_num) le_top hE0 hcard0
  omega

end Residual

section Good

theorem exists_noncomm_quot {K : Type} [Group K] (hq : CFSG.Open.IsQuasisimple K) :
    ∃ a b : K ⧸ Subgroup.center K, a * b ≠ b * a := by
  by_contra hall
  push Not at hall
  have h1 : commutator K ≤ Subgroup.center K := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [← QuotientGroup.eq_one_iff]
    have := map_commutatorElement (QuotientGroup.mk' (Subgroup.center K)) g₁ g₂
    change (QuotientGroup.mk ⁅g₁, g₂⁆ : K ⧸ Subgroup.center K) = _ at this
    rw [this]
    exact commutatorElement_eq_one_iff_mul_comm.2 (hall _ _)
  have hctop : Subgroup.center K = ⊤ := top_le_iff.1 (hq.1 ▸ h1)
  haveI := hq.2.toNontrivial
  obtain ⟨x, hx⟩ := exists_ne (1 : K ⧸ Subgroup.center K)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  exact hx ((QuotientGroup.eq_one_iff g).2 (hctop ▸ Subgroup.mem_top g))

variable {S : Type} [Group S] [Finite S]

end Good

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzBridgeAux

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration CFSG.Open CFSG.AGLEmbedding
  CFSG.LocalAnalysis.GLTheoremB SeitzBridgeAux

theorem seitz2310_of_quasisimple (h : Seitz2310CubeSimple) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {K : Type} [Group K] [Finite K] (hq : CFSG.Open.IsQuasisimple K) (d : TauCeti.ValidLieTypeIndex)
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hdp : p ≠ d.1.characteristic) (hL34 : ¬ (p = 3 ∧ IsLThreeFour (K ⧸ Subgroup.center K)))
    (E : Subgroup (MulAut (K ⧸ Subgroup.center K))) (hE : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ 3)
    (hex : ¬ ExcIndex p d.1 ∨ (IsSixIndex d.1 ∧ E ≤ (MulAut.conj : (K ⧸ Subgroup.center K) →*
      MulAut (K ⧸ Subgroup.center K)).range)) :
    seitzHyperGamma p E = ⊤ :=
  h p hp hp2 (K ⧸ Subgroup.center K) hq.2 (exists_noncomm_quot hq) d ⟨e⟩ hdp hL34 E hE hcard hex

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
