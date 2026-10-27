module

public import CFSG.HardMathSupport.Curtis.Coordinator.SPLTorusAut
public import CFSG.HardMathSupport.Curtis.Coordinator.SPLTorusPerm
public import CFSG.HardMathSupport.Curtis.Coordinator.SPLTorusInner
import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsII
import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicProof

public section

open scoped commutatorElement


namespace CFSG.HardMathSupport.Curtis.Coordinator

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem isPerfect_of_simple_nonabelian {S : Type*} [Group S] [IsSimpleGroup S]
    (hnab : ∃ a b : S, a * b ≠ b * a) : Group.IsPerfect S := by
  refine ⟨?_⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator S) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have : ⁅a, b⁆ ∈ commutator S := Subgroup.commutator_mem_commutator trivial trivial
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  · exact h

theorem false_of_alternating {p r : ℕ} {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) {n : ℕ} (e : S ≃* alternatingGroup (Fin n))
    {E : Subgroup (MulAut S)} {ζ γ : MulAut S} (h : SPLAutData p r S E ζ γ) : False := by
  have hp := h.prime_p
  have hr := h.prime_r
  have hperf : Group.IsPerfect S := isPerfect_of_simple_nonabelian hnab
  have : Nontrivial S := hs.toNontrivial
  have hn5 : 5 ≤ n := CFSG.AGLEmbedding.five_le_of_isPerfect_mulEquiv_alternatingGroup e
  have hZ : Subgroup.center S = ⊥ := CFSG.LocalAnalysis.RankThreeTheoremC.center_eq_bot_of_simple hnab
  have hr5 := five_le_of_dvd_sq_add_one hp h.ne_two hr h.dvd h.ndvd
  have hrp := ne_of_dvd_sq_add_one hp h.dvd
  have hOutS : ∀ q : ℕ, q.Prime → q ≠ 2 → ¬ q ∣ Nat.card (Outer S) := by
    intro q hq hq2 hd
    apply CFSG.AGLEmbedding.not_dvd_card_outer_alternatingGroup n hn5 q hq hq2
    rw [← Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
    exact hd
  obtain ⟨s, hsζ⟩ : ζ ∈ inner S :=
    mem_inner_of_pow_eq_one h.prime_p (hOutS p hp h.ne_two) (k := 1) (by simpa using h.zeta_pow)
  obtain ⟨k, hk⟩ := h.gamma_pow
  obtain ⟨a, haγ⟩ : γ ∈ inner S :=
    mem_inner_of_pow_eq_one hr (hOutS r hr (by omega)) hk
  have hinj := conj_injective_of_center_eq_bot' hZ
  have hs1 : s ^ p = 1 := by
    apply hinj
    rw [map_pow, hsζ, map_one]
    exact h.zeta_pow
  have ha1 : a ^ r ^ k = 1 := by
    apply hinj
    rw [map_pow, haγ, map_one]
    exact hk
  have hsa : a * s = s * a := by
    apply hinj
    rw [map_mul, map_mul, hsζ, haγ]
    exact h.gamma_zeta
  have ha0 : a ≠ 1 := by
    rintro rfl
    obtain ⟨e', -, he'⟩ := h.gamma_act
    apply he'
    rw [← haγ]
    simp
  have hfix : autFix ζ = Subgroup.centralizer {s} := by
    ext x
    rw [mem_autFix, ← hsζ, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hx
      rw [MulAut.conj_apply] at hx
      calc x * s = (s * x * s⁻¹) * s := by rw [hx]
        _ = s * x := by group
    · intro hx
      rw [MulAut.conj_apply]
      calc s * x * s⁻¹ = (x * s) * s⁻¹ := by rw [hx]
        _ = x := by group
  have hsolvS : Group.IsSolvable (Subgroup.centralizer {s} : Subgroup S) := by
    rw [← hfix]; exact h.solv
  set σ : Equiv.Perm (Fin n) := ((e s : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) with hσ
  set a' : Equiv.Perm (Fin n) := ((e a : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) with ha'
  have hσp : σ ^ p = 1 := by
    have : (e s) ^ p = 1 := by rw [← map_pow, hs1, map_one]
    exact congrArg Subtype.val this
  have hcomm : a' * σ = σ * a' := by
    have : e a * e s = e s * e a := by rw [← map_mul, ← map_mul, hsa]
    exact congrArg Subtype.val this
  have hmemf : ∀ x : (Subgroup.centralizer {s} : Subgroup S),
      ((e x.1 : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ∈
        (Subgroup.centralizer {σ} : Subgroup (Equiv.Perm (Fin n))) := by
    intro x
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hx := Subgroup.mem_centralizer_singleton_iff.mp x.2
    have : e x.1 * e s = e s * e x.1 := by rw [← map_mul, ← map_mul, hx]
    exact congrArg Subtype.val this
  let f : (Subgroup.centralizer {s} : Subgroup S) →*
      (Subgroup.centralizer {σ} : Subgroup (Equiv.Perm (Fin n))) :=
    { toFun := fun x => ⟨((e x.1 : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)), hmemf x⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        simp }
  let g : (Subgroup.centralizer {σ} : Subgroup (Equiv.Perm (Fin n))) →* ℤˣ :=
    Equiv.Perm.sign.comp (Subgroup.subtype _)
  have hsolvM : Group.IsSolvable (Subgroup.centralizer {σ} : Subgroup (Equiv.Perm (Fin n))) := by
    have := hsolvS
    refine Group.isSolvable_of_ker_le_range f g ?_
    intro m hm
    have hmA : (m : Equiv.Perm (Fin n)) ∈ alternatingGroup (Fin n) :=
      Equiv.Perm.mem_alternatingGroup.mpr hm
    refine ⟨⟨e.symm ⟨m, hmA⟩, ?_⟩, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_singleton_iff.mp m.2)
    · apply Subtype.ext
      simp [f]
  have hnd := not_dvd_card_centralizer hp hr hr5 hrp hσp hsolvM
  apply hnd
  let am : (Subgroup.centralizer {σ} : Subgroup (Equiv.Perm (Fin n))) :=
    ⟨a', Subgroup.mem_centralizer_singleton_iff.mpr hcomm⟩
  have hamk : am ^ r ^ k = 1 := by
    apply Subtype.ext
    have h2 : (e a) ^ r ^ k = 1 := by rw [← map_pow, ha1, map_one]
    have h3 := congrArg (fun x : alternatingGroup (Fin n) => (x : Equiv.Perm (Fin n))) h2
    simpa [am, ha'] using h3
  have ham1 : am ≠ 1 := by
    intro h1
    apply ha0
    have h2 : ((e a : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) = 1 :=
      congrArg Subtype.val h1
    have : e a = 1 := Subtype.ext h2
    simpa using this
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hr).1 (orderOf_dvd_of_pow_eq_one hamk)
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hj
    exact ham1 hj
  exact (dvd_pow_self r hj0).trans (hj ▸ orderOf_dvd_natCard am)

end CFSG.HardMathSupport.Curtis.Coordinator
