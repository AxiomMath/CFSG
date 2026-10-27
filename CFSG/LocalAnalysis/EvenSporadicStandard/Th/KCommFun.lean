module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.KCommBp
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.GL4Rep
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.GL4Gen

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup Matrix

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa : Subgroup G}
  {z b : G}

@[expose] def Fnl (A Aa : Subgroup G) (t : G) : AddSubgroup (G → ZMod 2) where
  carrier := {f | (∀ x ∈ Csub A Aa t, ∀ y ∈ Csub A Aa t, f (x * y) = f x + f y) ∧
    (∀ x, x ∉ Csub A Aa t → f x = 0) ∧ ∀ x ∈ Aa, f x = 0}
  zero_mem' := ⟨fun x _ y _ => by simp, fun x _ => rfl, fun x _ => rfl⟩
  add_mem' := by
    rintro f g ⟨hf1, hf2, hf3⟩ ⟨hg1, hg2, hg3⟩
    refine ⟨fun x hx y hy => ?_, fun x hx => ?_, fun x hx => ?_⟩
    · simp only [Pi.add_apply, hf1 x hx y hy, hg1 x hx y hy]
      ring
    · simp [hf2 x hx, hg2 x hx]
    · simp [hf3 x hx, hg3 x hx]
  neg_mem' := by
    rintro f ⟨hf1, hf2, hf3⟩
    refine ⟨fun x hx y hy => ?_, fun x hx => ?_, fun x hx => ?_⟩
    · simp only [Pi.neg_apply, hf1 x hx y hy]
      ring
    · simp [hf2 x hx]
    · simp [hf3 x hx]

instance Fnl.instAddCommGroup (A Aa : Subgroup G) (t : G) :
    AddCommGroup ↥(Fnl A Aa t) :=
  AddSubgroup.toAddCommGroup (Fnl A Aa t)

@[expose] def conjFn (q : G) (f : G → ZMod 2) : G → ZMod 2 := fun y => f (q⁻¹ * y * q)

section

variable (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)

include H W W2

theorem ThCyc.conjFn_mem {q : G} (hq : q ∈ normalizer ((W5 A t : Subgroup G) : Set G))
    {f : G → ZMod 2} (hf : f ∈ Fnl A Aa t) : conjFn q f ∈ Fnl A Aa t := by
  obtain ⟨hf1, hf2, hf3⟩ := hf
  have hq' : q⁻¹ ∈ normalizer ((W5 A t : Subgroup G) : Set G) := (normalizer _).inv_mem hq
  have hC : ∀ x ∈ Csub A Aa t, q⁻¹ * x * q ∈ Csub A Aa t := fun x hx => by
    simpa using H.conj_mem_inf_centralizer_Aa W W2 hq' hx
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · have e : q⁻¹ * (x * y) * q = (q⁻¹ * x * q) * (q⁻¹ * y * q) := by group
    show f (q⁻¹ * (x * y) * q) = f (q⁻¹ * x * q) + f (q⁻¹ * y * q)
    rw [e]
    exact hf1 _ (hC x hx) _ (hC y hy)
  · apply hf2
    intro hxC
    apply hx
    have := H.conj_mem_inf_centralizer_Aa W W2 hq hxC
    have e : q * (q⁻¹ * x * q) * q⁻¹ = x := by group
    rwa [e] at this
  · apply hf3
    simpa using H.Aa_normal W W2 hq' x hx

@[expose] def actFn (q : ↥(normalizer ((W5 A t : Subgroup G) : Set G))) (f : ↥(Fnl A Aa t)) :
    ↥(Fnl A Aa t) :=
  ⟨conjFn (q : G) f.1, H.conjFn_mem W W2 q.2 f.2⟩

theorem actFn_apply (q : ↥(normalizer ((W5 A t : Subgroup G) : Set G))) (f : ↥(Fnl A Aa t))
    (y : G) : (actFn H W W2 q f).1 y = f.1 ((q : G)⁻¹ * y * q) := rfl

theorem actFn_one (f : ↥(Fnl A Aa t)) : actFn H W W2 1 f = f :=
  Subtype.ext (funext fun y => by simp [actFn_apply])

theorem actFn_mul (q q' : ↥(normalizer ((W5 A t : Subgroup G) : Set G))) (f : ↥(Fnl A Aa t)) :
    actFn H W W2 (q * q') f = actFn H W W2 q (actFn H W W2 q' f) :=
  Subtype.ext (funext fun y => by
    simp only [actFn_apply, Subgroup.coe_mul]
    group)

theorem actFn_add (q : ↥(normalizer ((W5 A t : Subgroup G) : Set G))) (f g : ↥(Fnl A Aa t)) :
    actFn H W W2 q (f + g) = actFn H W W2 q f + actFn H W W2 q g := rfl

theorem ThCyc.fn_conj_Bp {r : G} (hr : r ∈ Bp A t) {f : G → ZMod 2} (hf : f ∈ Fnl A Aa t)
    (y : G) : f (r⁻¹ * y * r) = f y := by
  obtain ⟨hf1, hf2, hf3⟩ := hf
  by_cases hy : y ∈ Csub A Aa t
  · have hu := H.Bp_comm_mem_Aa W W2 ((Bp A t).inv_mem hr) hy
    have hAaC : ∀ x ∈ Aa, x ∈ Csub A Aa t := fun x hx => H.Aa_le_inf_centralizer_Aa W W2 hx
    have e : r⁻¹ * y * r = (r⁻¹ * y * r⁻¹⁻¹ * y⁻¹) * y := by group
    rw [e, hf1 _ (hAaC _ hu) _ hy, hf3 _ hu, zero_add]
  · rw [hf2 y hy, hf2]
    intro hC
    apply hy
    have := H.conj_mem_inf_centralizer_Aa W W2 hr.2 hC
    have e : r * (r⁻¹ * y * r) * r⁻¹ = y := by group
    rwa [e] at this

theorem ThCyc.exists_conj_t {r : G} (hr : r ∈ normalizer ((W5 A t : Subgroup G) : Set G)) :
    ∃ a ∈ A, r * t * r⁻¹ = a * t := by
  have hA : A ≤ L := le_trans (fun x hx => (W.mem_A_iff x).1 hx |>.1) W.S_le
  have hrt : r * t * r⁻¹ ∈ W5 A t :=
    (mem_normalizer_iff.1 hr t).1 (mem_sup_right (mem_zpowers t))
  rcases (H.mem_W5_iff hA).1 hrt with h | ⟨a', ha', h⟩
  · exfalso
    apply H.not_conj_mem r⁻¹
    simpa using hA h
  · exact ⟨a', ha', h⟩

theorem ThCyc.fn_conj_t {q : G} (hq : q ∈ normalizer ((W5 A t : Subgroup G) : Set G))
    {f : G → ZMod 2} (hf : f ∈ Fnl A Aa t) : f (q⁻¹ * t * q) = f t := by
  obtain ⟨hf1, hf2, hf3⟩ := hf
  obtain ⟨a, ha, hat⟩ := H.exists_conj_t W W2 ((normalizer _).inv_mem hq)
  have e : q⁻¹ * t * q = a * t := by simpa using hat
  rw [e, hf1 a (H.Aa_le_inf_centralizer_Aa W W2 (W2.A_le ha)) t (H.t_mem_inf_centralizer_Aa W W2),
    hf3 a (W2.A_le ha), zero_add]

theorem ThCyc.fn_eq_zero_of_theta {f : G → ZMod 2} (hf : f ∈ Fnl A Aa t) (hft : f t = 0)
    {y : G} (hy : y ∈ Csub A Aa t) (h1 : theta t y = 1) : f y = 0 := by
  obtain ⟨hf1, hf2, hf3⟩ := hf
  rcases H.mem_Aa_or_mul_t W W2 hy h1 with h | ⟨x, hx, rfl⟩
  · exact hf3 y h
  · rw [hf1 x (H.Aa_le_inf_centralizer_Aa W W2 hx) t (H.t_mem_inf_centralizer_Aa W W2), hf3 x hx,
      hft, add_zero]

variable {c : G → (Fin 4 → ZMod 2)}

theorem ThCyc.fn_eq_zero_of_invariant (hc : IsCoord A c) {k₅ : G} (hk₅L : k₅ ∈ L)
    (hk₅A : ∀ x ∈ A, k₅ * x * k₅⁻¹ ∈ A) (hrep : IsRep A c k₅ (singerMat ^ 5))
    {f : G → ZMod 2} (hf : f ∈ Fnl A Aa t) (hft : f t = 0)
    (hinv : ∀ y, f (k₅ * y * k₅⁻¹) = f y) : f = 0 := by
  funext y
  by_cases hy : y ∈ Csub A Aa t
  · have hf' := hf
    obtain ⟨hf1, hf2, hf3⟩ := hf
    have hk₅N := H.mem_normalizer_W5_of_L W hk₅L hk₅A
    obtain ⟨u, hu⟩ := exists_pow_five_sub (c (theta t y))
    obtain ⟨au, hauA, hauc⟩ := hc.onto u
    obtain ⟨x, hxC, hθx⟩ := H.exists_theta_eq_of_mem_inf_centralizer_Aa W W2 hauA
    have hkxC : k₅ * x * k₅⁻¹ ∈ Csub A Aa t := H.conj_mem_inf_centralizer_Aa W W2 hk₅N hxC
    have hy'C : k₅ * x * k₅⁻¹ * x ∈ Csub A Aa t := (Csub A Aa t).mul_mem hkxC hxC
    have hθy' : theta t (k₅ * x * k₅⁻¹ * x) = theta t y := by
      have hθkx : theta t (k₅ * x * k₅⁻¹) = k₅ * au * k₅⁻¹ := by
        rw [H.theta_conj hk₅L, hθx]
      have hθA : theta t (k₅ * x * k₅⁻¹ * x) ∈ A := H.theta_mem_A W hy'C.1
      refine hc.inj _ hθA _ (H.theta_mem_A W hy.1) ?_
      rw [H.theta_mul W hkxC.1 hxC.1, hθkx, hθx, hc.mul _ (hk₅A _ hauA) _ hauA,
        hrep au hauA, hauc, hu]
    have hker : theta t (y⁻¹ * (k₅ * x * k₅⁻¹ * x)) = 1 := by
      rw [H.theta_mul W ((Csub A Aa t).inv_mem hy).1 hy'C.1, H.theta_inv W W2 hy.1, hθy',
        inv_mul_cancel]
    have hf0 := H.fn_eq_zero_of_theta W W2 hf' hft ((Csub A Aa t).mul_mem
      ((Csub A Aa t).inv_mem hy) hy'C) hker
    have hfy' : f (k₅ * x * k₅⁻¹ * x) = f y := by
      have e : k₅ * x * k₅⁻¹ * x = y * (y⁻¹ * (k₅ * x * k₅⁻¹ * x)) := by group
      rw [e, hf1 y hy _ ((Csub A Aa t).mul_mem ((Csub A Aa t).inv_mem hy) hy'C), hf0, add_zero]
    have h2 : f (k₅ * x * k₅⁻¹ * x) = 0 := by
      rw [hf1 _ hkxC x hxC, hinv x]
      exact (by decide : ∀ a : ZMod 2, a + a = 0) _
    exact hfy'.symm.trans h2
  · exact hf.2.1 y hy

end

end CFSG.EvenSporadicStandard.ThStd
