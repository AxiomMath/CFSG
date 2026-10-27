module

public import CFSG.GroupTheory.ExtraspecialCentralizerInnerAut
public import CFSG.LinearAlgebra.BinarySymplecticCentralizerOrderThree

public noncomputable section

namespace CFSG.ComponentClassification.BMCase

open Subgroup CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.ExtraspecialFixed

section Conj

variable {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]

@[expose] def glConj (e : V ≃ₗ[ZMod 2] W) :
    LinearMap.GeneralLinearGroup (ZMod 2) V ≃* LinearMap.GeneralLinearGroup (ZMod 2) W :=
  Units.mapEquiv (e.conjRingEquiv).toMulEquiv

theorem glConj_apply (e : V ≃ₗ[ZMod 2] W) (a : LinearMap.GeneralLinearGroup (ZMod 2) V)
    (w : W) :
    ((glConj e a : LinearMap.GeneralLinearGroup (ZMod 2) W) : W →ₗ[ZMod 2] W) w =
      e ((a : V →ₗ[ZMod 2] V) (e.symm w)) := rfl

end Conj

section Model

variable {Q : Type*} [Group Q] [Module (ZMod 2) (Additive (Abelianization Q))]
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] def abelianizationEquiv (ψ : Q →* Multiplicative W) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = commutator Q) : Additive (Abelianization Q) ≃ₗ[ZMod 2] W :=
  (MulEquiv.toAdditiveLeft (MulEquiv.ofBijective (Abelianization.lift ψ) ⟨by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro v hv
      obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective v
      have hq : q ∈ ψ.ker := hv
      rw [hker, ← Abelianization.ker_of] at hq
      exact hq, fun w => by
        obtain ⟨q, hq⟩ := hψ w
        exact ⟨Abelianization.of q, by rw [Abelianization.lift_apply_of, hq]⟩⟩)).toLinearEquiv
    fun c x => ZMod.map_smul _ c x

theorem abelianizationEquiv_apply (ψ : Q →* Multiplicative W) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = commutator Q) (q : Q) :
    abelianizationEquiv ψ hψ hker (Additive.ofMul (Abelianization.of q)) =
      Multiplicative.toAdd (ψ q) := rfl

end Model

section Main

variable {H : Type*} [Group H] {Q : Subgroup H} [Q.Normal]

omit [Q.Normal] in
theorem natCard_abelianization_mul_two (hQ : IsExtraspecialPGroup 2 Q) :
    Nat.card (Abelianization Q) * 2 = Nat.card Q := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (commutator Q)
  rw [show Nat.card (commutator Q) = 2 by rw [hQ.2.1]; exact hQ.2.2.2] at h
  exact h.symm

theorem conjGL_eq_one_iff (hQ : IsExtraspecialPGroup 2 Q)
    [Module (ZMod 2) (Additive (Abelianization Q))] (h : H) :
    conjGL (Q := Q) h = 1 ↔
      ∀ q ∈ Q, h * q * h⁻¹ * q⁻¹ ∈ (center Q).map Q.subtype := by
  have key : ∀ q : Q, Abelianization.of (MulAut.conjNormal h q) = Abelianization.of q ↔
      h * (q : H) * h⁻¹ * (q : H)⁻¹ ∈ (center Q).map Q.subtype := by
    intro q
    rw [← hQ.2.1]
    constructor
    · intro h2
      have h3 : (MulAut.conjNormal h q)⁻¹ * q ∈ commutator Q := QuotientGroup.eq.1 h2
      have h4 : q * (MulAut.conjNormal h q)⁻¹ ∈ commutator Q :=
        (Subgroup.Normal.mem_comm_iff inferInstance).1 h3
      refine ⟨(q * (MulAut.conjNormal h q)⁻¹)⁻¹, (commutator Q).inv_mem h4, ?_⟩
      rw [Subgroup.coe_subtype, mul_inv_rev, inv_inv, Subgroup.coe_mul, Subgroup.coe_inv,
        MulAut.conjNormal_apply]
    · rintro ⟨c, hc, hce⟩
      apply QuotientGroup.eq.2
      have hce' : (c : H) = (MulAut.conjNormal h q : H) * (q : H)⁻¹ := by
        rw [MulAut.conjNormal_apply, ← hce]; rfl
      have hc' : c = MulAut.conjNormal h q * q⁻¹ := Subtype.ext (by rw [hce']; rfl)
      rw [hc'] at hc
      have := (commutator Q).inv_mem hc
      rw [mul_inv_rev, inv_inv] at this
      exact (Subgroup.Normal.mem_comm_iff inferInstance).1 this
  constructor
  · intro h1 q hq
    have h2 := congrArg (fun f : LinearMap.GeneralLinearGroup (ZMod 2)
      (Additive (Abelianization Q)) => (f : Additive (Abelianization Q) →ₗ[ZMod 2]
        Additive (Abelianization Q)) (Additive.ofMul (Abelianization.of ⟨q, hq⟩))) h1
    simp only [conjGL_apply, Units.val_one, Module.End.one_apply] at h2
    exact (key ⟨q, hq⟩).1 (Additive.ofMul.injective h2)
  · intro h1
    refine Units.ext (LinearMap.ext fun v => ?_)
    obtain ⟨q, rfl⟩ := exists_ofMul_of v
    simp only [conjGL_apply, Units.val_one, Module.End.one_apply]
    exact congrArg Additive.ofMul ((key q).2 (h1 q q.2))

theorem perfect_and_inner_of_model [Finite H] (hQ : IsExtraspecialPGroup 2 Q)
    (hcard : Nat.card Q = 2 ^ 23 ∨ Nat.card Q = 2 ^ 25)
    (hCQ : centralizer (Q : Set H) = (center Q).map Q.subtype)
    (hker : ∀ h : H, (∀ q ∈ Q, h * q * h⁻¹ * q⁻¹ ∈ (center Q).map Q.subtype) → h ∈ Q)
    (hsimple : IsSimpleGroup (H ⧸ Q)) (hnab : ∃ a b : H ⧸ Q, a * b ≠ b * a)
    (hinn : ∀ φ : MulAut (H ⧸ Q), ∃ g : H ⧸ Q, φ = MulAut.conj g)
    (h23 : 23 ∣ Nat.card (H ⧸ Q))
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ψ : Q →* Multiplicative W) (hψ : Function.Surjective ψ) (hψker : ψ.ker = center Q)
    (K : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) W))
    (hKH : ∀ k ∈ K, ∃ h : H, ∀ q : Q,
      ψ (MulAut.conjNormal h q) =
        Multiplicative.ofAdd ((k : W →ₗ[ZMod 2] W) (Multiplicative.toAdd (ψ q))))
    (hirr : ∀ U : Submodule (ZMod 2) W,
      (∀ k ∈ K, ∀ w ∈ U, (k : W →ₗ[ZMod 2] W) w ∈ U) → U = ⊥ ∨ U = ⊤)
    (h3 : ∀ a ∈ centralizer (K : Set (LinearMap.GeneralLinearGroup (ZMod 2) W)), a ^ 3 = 1) :
    Group.IsPerfect H ∧ ∀ α : MulAut H, ∃ g : H, α = MulAut.conj g := by
  classical
  let _ := CFSG.GroupTheory.extraspecialQuotientModule hQ
  have hc : commutator Q ≤ center Q := hQ.2.1.le
  set V := Additive (Abelianization Q) with hVdef
  set e : V ≃ₗ[ZMod 2] W := abelianizationEquiv ψ hψ (hψker.trans hQ.2.1.symm) with he
  have he_of : ∀ q : Q, e (Additive.ofMul (Abelianization.of q)) = Multiplicative.toAdd (ψ q) :=
    fun q => rfl
  have hKconj : ∀ k ∈ K, ∃ h : H, glConj e (conjGL h) = k := by
    intro k hk
    obtain ⟨h, hh⟩ := hKH k hk
    refine ⟨h, Units.ext (LinearMap.ext fun w => ?_)⟩
    obtain ⟨v, rfl⟩ := e.surjective w
    obtain ⟨q, rfl⟩ := exists_ofMul_of v
    rw [glConj_apply, LinearEquiv.symm_apply_apply, conjGL_apply, he_of, he_of, hh]
    rfl
  have hfin : Module.finrank (ZMod 2) V = 22 ∨ Module.finrank (ZMod 2) V = 24 := by
    have h1 := FiniteField.pow_finrank_eq_natCard 2 V
    have h2 : Nat.card V = Nat.card (Abelianization Q) := Nat.card_congr Additive.toMul
    have h3 := natCard_abelianization_mul_two hQ
    rcases hcard with h | h
    · left
      have h4 : 2 ^ Module.finrank (ZMod 2) V = 2 ^ 22 := by omega
      exact Nat.pow_right_injective le_rfl h4
    · right
      have h4 : 2 ^ Module.finrank (ZMod 2) V = 2 ^ 24 := by omega
      exact Nat.pow_right_injective le_rfl h4
  have hkerQ : (conjGL (Q := Q)).ker = Q := by
    ext h
    rw [MonoidHom.mem_ker, conjGL_eq_one_iff hQ]
    refine ⟨hker h, fun hh q hq => ?_⟩
    refine ⟨⟨h, hh⟩ * ⟨q, hq⟩ * (⟨h, hh⟩ : Q)⁻¹ * (⟨q, hq⟩ : Q)⁻¹, hc ?_, rfl⟩
    have := commutator_mem_commutator (G := Q) (mem_top (⟨h, hh⟩ : Q)) (mem_top ⟨q, hq⟩)
    rwa [commutatorElement_def] at this
  set K' := (conjGL (Q := Q)).range with hK'
  have hcardK' : Nat.card K' = Nat.card (H ⧸ Q) :=
    Nat.card_congr ((QuotientGroup.quotientKerEquivRange (conjGL (Q := Q))).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hkerQ)).toEquiv
  have hirrV : ∀ U : Submodule (ZMod 2) V,
      (∀ h : H, ∀ v ∈ U, ((conjGL (Q := Q) h : LinearMap.GeneralLinearGroup (ZMod 2) V) :
        V →ₗ[ZMod 2] V) v ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    have hU' : ∀ k ∈ K, ∀ w ∈ U.map e.toLinearMap,
        (k : W →ₗ[ZMod 2] W) w ∈ U.map e.toLinearMap := by
      intro k hk w hw
      obtain ⟨h, rfl⟩ := hKconj k hk
      obtain ⟨v, hv, rfl⟩ := hw
      refine ⟨_, hU h v hv, ?_⟩
      rw [glConj_apply]
      simp
    rcases hirr _ hU' with h | h
    · left
      rw [eq_bot_iff] at h ⊢
      intro v hv
      have h1 : e v = 0 := (Submodule.mem_bot _).1 (h ⟨v, hv, rfl⟩)
      exact (Submodule.mem_bot _).2 (by rwa [map_eq_zero_iff e e.injective] at h1)
    · right
      rw [eq_top_iff] at h ⊢
      intro v _
      obtain ⟨u, hu, hue⟩ := h (Submodule.mem_top (x := e v))
      rw [← e.injective hue]
      exact hu
  have h3V : ∀ a ∈ centralizer (K' : Set (LinearMap.GeneralLinearGroup (ZMod 2) V)),
      a ^ 3 = 1 := by
    intro a ha
    have ha' : glConj e a ∈ centralizer (K : Set (LinearMap.GeneralLinearGroup (ZMod 2) W)) := by
      rw [mem_centralizer_iff]
      intro k hk
      obtain ⟨h, rfl⟩ := hKconj k hk
      rw [← map_mul, ← map_mul, (mem_centralizer_iff.1 ha) (conjGL h) ⟨h, rfl⟩]
    have := h3 _ ha'
    rw [← map_pow, MulEquiv.map_eq_one_iff] at this
    exact this
  let χ : center Q ≃* Multiplicative (ZMod 2) :=
    mulEquivOfPrimeCardEq hQ.2.2.2 (Nat.card_zmod 2)
  set b := commForm hc χ.toMonoidHom with hb
  have hbnd : b.Nondegenerate := commForm_nondegenerate hc hQ.2.1.ge χ.injective
  have hbalt : b.IsAlt := by
    intro v
    obtain ⟨x, rfl⟩ := exists_ofMul_of v
    rw [hb, commForm_apply]
    have h : commRight hc x x = 1 := Subtype.ext (commutatorElement_self x)
    rw [h, map_one, toAdd_one]
  have hZ : ∀ z ∈ center Q, ∀ g : H, g * (z : H) * g⁻¹ = z :=
    fun z hz g => conj_eq_of_mem_center inferInstance hQ.2.2.2 hz g
  have hK'b : K' ≤ bilinIsometryGroup b := by
    rintro _ ⟨g, rfl⟩
    exact conjGL_mem_bilinIsometryGroup hc hZ χ.toMonoidHom g
  have hsp := CFSG.LinearAlgebra.binary_symplectic_centralizer_order_three_exclusion hfin b hbnd
    hbalt K' hK'b (fun U hU => hirrV U fun h v hv => hU _ ⟨h, rfl⟩ v hv) (hcardK' ▸ h23) h3V
  refine CFSG.GroupTheory.extraspecial_centralizer_inner_automorphisms hQ hCQ χ.toMonoidHom
    χ.injective hsimple (fun hcomm => ?_) hinn hirrV (fun φ hφ hcomm => ?_)
  · obtain ⟨a, b', hab⟩ := hnab
    exact hab (hcomm.is_comm.comm a b')
  · have hmem : φ ∈ centralizer (K' : Set (LinearMap.GeneralLinearGroup (ZMod 2) V)) ⊓
        CFSG.Certificates.bilinIsometryGroup b := by
      refine ⟨mem_centralizer_iff.2 ?_, hφ⟩
      rintro _ ⟨h, rfl⟩
      exact (hcomm h).symm
    rw [hsp] at hmem
    exact hmem

end Main

end CFSG.ComponentClassification.BMCase
