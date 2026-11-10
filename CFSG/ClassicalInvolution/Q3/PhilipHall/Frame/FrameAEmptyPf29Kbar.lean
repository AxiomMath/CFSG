module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf28Aut
public import CFSG.ClassicalInvolution.Asc77.HypOmegaDefs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Out

open CFSG.Open CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G]

abbrev Kbar (K : Subgroup G) : Type := ↥K ⧸ classicalInvolutionOddCore ↥K

@[expose] def conjK (K : Subgroup G) (x : G) (hx : x ∈ Subgroup.normalizer (K : Set G)) : MulAut ↥K where
  toFun k := ⟨x * k * x⁻¹, (Subgroup.mem_normalizer_iff.mp hx k.1).mp k.2⟩
  invFun k := ⟨x⁻¹ * k * x, by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (K : Set G)).inv_mem hx) k.1).mp
      k.2
    simpa using this⟩
  left_inv k := by apply Subtype.ext; simp [mul_assoc]
  right_inv k := by apply Subtype.ext; simp [mul_assoc]
  map_mul' a b := by apply Subtype.ext; simp [mul_assoc]

theorem conjK_apply (K : Subgroup G) (x : G) (hx : x ∈ Subgroup.normalizer (K : Set G)) (k : ↥K) :
    ((conjK K x hx k : ↥K) : G) = x * k * x⁻¹ := rfl

theorem conjK_oddCore (K : Subgroup G) (x : G) (hx : x ∈ Subgroup.normalizer (K : Set G)) :
    (classicalInvolutionOddCore ↥K).map (conjK K x hx).toMonoidHom =
      classicalInvolutionOddCore ↥K :=
  CFSG.ComponentClassification.OddCore.equiv_invariant (conjK K x hx)

@[expose] def rhoK (K : Subgroup G) : ↥(Subgroup.normalizer (K : Set G)) →* MulAut (Kbar K) where
  toFun x := QuotientGroup.congr _ _ (conjK K x.1 x.2) (conjK_oddCore K x.1 x.2)
  map_one' := by
    apply MulEquiv.ext
    intro q
    induction q using QuotientGroup.induction_on with
    | H k =>
      show ((QuotientGroup.mk (conjK K (1 : G) _ k) : Kbar K)) = QuotientGroup.mk k
      congr 1
      apply Subtype.ext
      simp [conjK_apply]
  map_mul' x y := by
    apply MulEquiv.ext
    intro q
    induction q using QuotientGroup.induction_on with
    | H k =>
      show ((QuotientGroup.mk (conjK K ((x * y : ↥(Subgroup.normalizer (K : Set G))) : G)
        (x * y).2 k) : Kbar K)) =
        QuotientGroup.mk (conjK K x.1 x.2 (conjK K y.1 y.2 k))
      congr 1
      apply Subtype.ext
      simp [conjK_apply, mul_assoc]

theorem rhoK_mk (K : Subgroup G) (x : ↥(Subgroup.normalizer (K : Set G))) (k : ↥K) :
    rhoK K x (QuotientGroup.mk k) = QuotientGroup.mk (conjK K x.1 x.2 k) := rfl

theorem mem_oddCoreOf_iff (K : Subgroup G) (k : ↥K) :
    (k : G) ∈ oddCoreOf K ↔ k ∈ classicalInvolutionOddCore ↥K := by
  unfold oddCoreOf
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨n, hn, hnk⟩
    have : n = k := Subtype.ext hnk
    exact this ▸ hn
  · intro h
    exact ⟨k, h, rfl⟩

@[expose] def InnerOn (K : Subgroup G) (x : G) : Prop :=
  ∃ k ∈ K, ∀ y ∈ K, (x * y * x⁻¹) * (k * y * k⁻¹)⁻¹ ∈ oddCoreOf K

theorem rhoK_eq_conj_iff (K : Subgroup G) (x : ↥(Subgroup.normalizer (K : Set G))) (k : ↥K) :
    rhoK K x = MulAut.conj (QuotientGroup.mk k : Kbar K) ↔
      ∀ y : ↥K, ((x : G) * y * (x : G)⁻¹) * ((k : G) * y * (k : G)⁻¹)⁻¹ ∈ oddCoreOf K := by
  constructor
  · intro h y
    have h1 := congrArg (fun φ : MulAut (Kbar K) => φ (QuotientGroup.mk y)) h
    simp only [rhoK_mk, MulAut.conj_apply] at h1
    have h2 : (conjK K x.1 x.2 y)⁻¹ * 1 = (conjK K x.1 x.2 y)⁻¹ := mul_one _
    have h3 := (QuotientGroup.eq_iff_div_mem).mp h1
    have h4 := (mem_oddCoreOf_iff K _).mpr h3
    simpa [conjK_apply, div_eq_mul_inv, mul_assoc] using h4
  · intro h
    apply MulEquiv.ext
    intro q
    induction q using QuotientGroup.induction_on with
    | H y =>
      simp only [rhoK_mk, MulAut.conj_apply]
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
        QuotientGroup.eq_iff_div_mem]
      refine (mem_oddCoreOf_iff K _).mp ?_
      simpa [conjK_apply, div_eq_mul_inv, mul_assoc] using h y

@[expose] def psiK (K : Subgroup G) : ↥(Subgroup.normalizer (K : Set G)) →* Equiv.Perm (Idx2 (Kbar K)) :=
  Idx2.act.comp (rhoK K)

theorem psiK_apply (K : Subgroup G) (x : ↥(Subgroup.normalizer (K : Set G))) :
    psiK K x = Idx2.act (rhoK K x) := rfl

variable [Finite G]

theorem psiK_eq_one_of_conj (K : Subgroup G) (x : ↥(Subgroup.normalizer (K : Set G))) (k : ↥K)
    (h : rhoK K x = MulAut.conj (QuotientGroup.mk k : Kbar K)) : psiK K x = 1 := by
  have : Finite (Kbar K) := inferInstance
  show Idx2.act (rhoK K x) = 1
  rw [h]
  exact Idx2.act_inner _

theorem psiK_eq_one_iff (K : Subgroup G) (e : Kbar K ≃* Q8)
    (x : ↥(Subgroup.normalizer (K : Set G))) :
    psiK K x = 1 ↔ InnerOn K x := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := exists_inner_of_act_eq_one_of_equiv e (rhoK K x) h
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective g
    have h1 : rhoK K x = MulAut.conj (QuotientGroup.mk k : Kbar K) := by
      apply MulEquiv.ext
      intro q
      rw [hg q]
      rfl
    refine ⟨(k : G), k.2, fun y hy => ?_⟩
    exact (rhoK_eq_conj_iff K x k).mp h1 ⟨y, hy⟩
  · rintro ⟨k, hk, h⟩
    exact psiK_eq_one_of_conj K x ⟨k, hk⟩ ((rhoK_eq_conj_iff K x ⟨k, hk⟩).mpr fun y => h y y.2)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Out
