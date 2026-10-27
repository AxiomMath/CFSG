module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3WrBL
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3Wr

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.EvenSporadicStandard.M22Std.S6Check

variable {X : Type} [Group X] [Finite X] {zb : X} {f : X →* Wr} {E : Subgroup X}

omit [Finite X] in
theorem outer_form {y : X} (hy2 : y * y = 1) (hye : (f y).e = true) :
    ∃ p, f y = ⟨p, p⁻¹, true⟩ := by
  have hsq : f y * f y = 1 := by rw [← map_mul, hy2, map_one]
  have := Wr.eq_inv_of_sq_eq_one hye hsq
  exact ⟨(f y).a, Wr.ext rfl this hye⟩

namespace WrSit


theorem E_inf_centralizer_le (h : WrSit X zb f E) {u : Equiv.Perm (Fin 6)}
    (hu : f zb = ⟨u, u⁻¹, true⟩) {g : X} (hg : g ∈ E) (hgC : g ∈ centralizer ({zb} : Set X)) :
    g ∈ (commutator ↥(centralizer ({zb} : Set X))).map (centralizer ({zb} : Set X)).subtype := by
  classical
  set C : Subgroup X := centralizer ({zb} : Set X) with hC
  have hsign : ∀ a : alternatingGroup (Fin 6),
      Equiv.Perm.sign (u⁻¹ * (a : Equiv.Perm (Fin 6)) * u) = 1 := by
    intro a
    have := Equiv.Perm.mem_alternatingGroup.1 a.2
    simp only [map_mul, map_inv, this]
    rcases Int.units_eq_one_or (Equiv.Perm.sign u) with h2 | h2 <;> simp [h2]
  let κ : alternatingGroup (Fin 6) →* alternatingGroup (Fin 6) :=
    { toFun := fun a => ⟨u⁻¹ * (a : Equiv.Perm (Fin 6)) * u,
        Equiv.Perm.mem_alternatingGroup.2 (hsign a)⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a a' => by
        apply Subtype.ext
        simp [mul_assoc] }
  let α : alternatingGroup (Fin 6) →* alternatingGroup (Fin 6) × alternatingGroup (Fin 6) :=
    (MonoidHom.id _).prod κ
  let φ : alternatingGroup (Fin 6) →* X := E.subtype.comp
    ((MulEquiv.ofBijective h.theta h.theta_bijective).symm.toMonoidHom.comp α)
  have hfφ : ∀ a : alternatingGroup (Fin 6),
      f (φ a) = ⟨(a : Equiv.Perm (Fin 6)), u⁻¹ * a * u, false⟩ := by
    intro a
    set g : E := (MulEquiv.ofBijective h.theta h.theta_bijective).symm (α a) with hg
    have hθ : h.theta g = α a :=
      (MulEquiv.ofBijective h.theta h.theta_bijective).apply_symm_apply _
    have h1 : (f g).a = (a : Equiv.Perm (Fin 6)) :=
      congrArg (fun p => (p.1 : Equiv.Perm (Fin 6))) hθ
    have h2 : (f g).b = u⁻¹ * (a : Equiv.Perm (Fin 6)) * u :=
      congrArg (fun p => (p.2 : Equiv.Perm (Fin 6))) hθ
    have he := h.E_flag g.2
    show f (g : X) = _
    exact Wr.ext h1 h2 he
  have hφC : ∀ a, φ a ∈ C := by
    intro a
    rw [hC, mem_centralizer_singleton_iff]
    apply h.inj
    rw [map_mul, map_mul, hfφ, hu]
    simp [mul_assoc]
  let φ' : alternatingGroup (Fin 6) →* ↥C := φ.codRestrict C hφC
  have hb := b_eq_of_mem_centralizer hu hgC (h.E_flag hg)
  have hga : Equiv.Perm.sign (f g).a = 1 := (h.E_sign hg).1
  have hgφ : g = φ ⟨(f g).a, Equiv.Perm.mem_alternatingGroup.2 hga⟩ := by
    apply h.inj
    rw [hfφ]
    exact Wr.ext rfl hb (h.E_flag hg)
  have hperf : (⊤ : Subgroup (alternatingGroup (Fin 6))) = commutator (alternatingGroup (Fin 6)) :=
    (commutator_alternatingGroup_eq_top (by simp)).symm
  have hmem : (⟨(f g).a, Equiv.Perm.mem_alternatingGroup.2 hga⟩ : alternatingGroup (Fin 6)) ∈
      commutator (alternatingGroup (Fin 6)) := by
    rw [← hperf]
    exact Subgroup.mem_top _
  have hmapc : (commutator (alternatingGroup (Fin 6))).map φ' ≤ commutator ↥C := by
    rw [_root_.commutator_def, Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  refine ⟨φ' ⟨(f g).a, Equiv.Perm.mem_alternatingGroup.2 hga⟩, hmapc ⟨_, hmem, rfl⟩, ?_⟩
  exact hgφ.symm

theorem outerWr_of_wrSit (h : WrSit X zb f E) : OuterWr X zb := by
  classical
  have hzo := h.zb_outer
  obtain ⟨u, hu⟩ := h.exists_zb_form
  have hBe : ∀ y : X, y ∉ (Wr.flag.comp f).ker → (f y).e = true := fun y hy => by
    have : ¬ Wr.flag (f y) = 1 := hy
    rw [Wr.flag_eq_one_iff] at this
    simpa using this
  refine ⟨(Wr.flag.comp f).ker, ?_, ?_, ?_, ?_⟩
  · refine Subgroup.index_eq_two_iff.2 ⟨zb, fun b => ?_⟩
    have hz : Wr.flag (f zb) = -1 := (Wr.flag_eq_neg_one_iff _).2 hzo
    show Xor (b * zb ∈ (Wr.flag.comp f).ker) (b ∈ (Wr.flag.comp f).ker)
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, map_mul, hz]
    rcases Int.units_eq_one_or (Wr.flag (f b)) with hb | hb <;> simp [hb]
  · intro hzB
    have h1 : Wr.flag (f zb) = 1 := hzB
    rw [(Wr.flag_eq_neg_one_iff _).2 hzo] at h1
    exact absurd h1 (by decide)
  · intro q hqB hq2 _
    exact h.base_large ((Wr.flag_eq_one_iff _).1 hqB) hq2
  · intro P hP2 hPidx hzbP y0 hy0P hy02 hy0B hy0C hy0S
    have hy0e : (f y0).e = true := hBe y0 hy0B
    obtain ⟨q, hq⟩ := outer_form hy02 hy0e
    have hS2 : Equiv.Perm.sign q ≠ Equiv.Perm.sign u := by
      intro hqu
      apply hy0S
      have hzC : zb ∈ centralizer ({zb} : Set X) := mem_centralizer_singleton_iff.2 rfl
      have hE : y0 * zb ∈ E := by
        rw [h.mem_E_iff, map_mul, hq, hu]
        simp only [Wr.mul_tt, Bool.not_true, map_mul, map_inv, hqu, true_and]
        rcases Int.units_eq_one_or (Equiv.Perm.sign u) with h2 | h2 <;> simp [h2]
      have hC' := h.E_inf_centralizer_le hu hE
        (Subgroup.mul_mem _ hy0C hzC)
      have : y0 = (y0 * zb) * zb := by rw [mul_assoc, h.zb2, mul_one]
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hC')
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers zb))
    by_cases hII : ∀ g : X, (f g).e = false →
        Equiv.Perm.sign (f g).a = Equiv.Perm.sign (f g).b
    ·
      have hmatched : ∀ g : X, Equiv.Perm.sign (f g).a = Equiv.Perm.sign (f g).b := by
        intro g
        by_cases hge : (f g).e = false
        · exact hII g hge
        · have hget : (f g).e = true := by simpa using hge
          have hbase : (f (g * zb)).e = false := by
            rw [map_mul, hu]
            rcases hfg : f g with ⟨a, b, e⟩
            rw [hfg] at hget
            simp only at hget
            subst hget
            rfl
          have h1 := hII (g * zb) hbase
          rw [map_mul, hu] at h1
          rcases hfg : f g with ⟨a, b, e⟩
          rw [hfg] at hget h1
          simp only at hget
          subst hget
          simp only [Wr.mul_tt, map_mul, map_inv] at h1 ⊢
          rw [Int.units_inv_eq_self] at h1
          exact mul_right_cancel h1
      let Θ : X →* ℤˣ :=
        { toFun := fun g => Equiv.Perm.sign (f g).a
          map_one' := by simp [map_one]
          map_mul' := fun g g' => by
            have h2 := hmatched g'
            rw [map_mul]
            rcases hfg : f g with ⟨a, b, e⟩
            rcases hfg' : f g' with ⟨a', b', e'⟩
            rw [hfg'] at h2
            simp only at h2
            cases e <;> simp [Wr.mul_def, map_mul, h2] }
      have hΘz : Θ zb = Equiv.Perm.sign u := by
        show Equiv.Perm.sign (f zb).a = _
        rw [hu]
      have hΘy : Θ y0 = Equiv.Perm.sign q := by
        show Equiv.Perm.sign (f y0).a = _
        rw [hq]
      have hall : ∀ c ∈ alternatingGroup (Fin 6), ∀ d ∈ alternatingGroup (Fin 6),
          ∃ g : X, f g = ⟨c, d, false⟩ := fun c hc d hd => by
        obtain ⟨g, -, hg⟩ := h.E_surj (Equiv.Perm.mem_alternatingGroup.1 hc)
          (Equiv.Perm.mem_alternatingGroup.1 hd)
        exact ⟨g, hg⟩
      refine ⟨fun y hyP hy2 hyB => ?_, fun hconj => ?_⟩
      · have hye := hBe y hyB
        obtain ⟨p, hp⟩ := outer_form hy2 hye
        by_cases hpu : Equiv.Perm.sign p = Equiv.Perm.sign u
        · left
          refine exists_mem_conj_of_flag f h.inj (A := alternatingGroup (Fin 6)) inferInstance
            hall hP2 hPidx h.zb2 hzo hzbP hyP hy2 ?_
          rw [map_mul, hu, hp]
          simp only [Wr.mul_tt, Bool.not_true, Equiv.Perm.mem_alternatingGroup, map_mul, map_inv,
            hpu, true_and]
          rcases Int.units_eq_one_or (Equiv.Perm.sign u) with h2 | h2 <;> simp [h2]
        · right
          have hpq : Equiv.Perm.sign p = Equiv.Perm.sign q := by
            rcases Int.units_eq_one_or (Equiv.Perm.sign p) with h1 | h1 <;>
              rcases Int.units_eq_one_or (Equiv.Perm.sign q) with h2 | h2 <;>
              rcases Int.units_eq_one_or (Equiv.Perm.sign u) with h3 | h3 <;>
              simp_all
          refine exists_mem_conj_of_flag f h.inj (A := alternatingGroup (Fin 6)) inferInstance
            hall hP2 hPidx hy02 hy0e hy0P hyP hy2 ?_
          rw [map_mul, hq, hp]
          simp only [Wr.mul_tt, Bool.not_true, Equiv.Perm.mem_alternatingGroup, map_mul, map_inv,
            hpq, true_and]
          rcases Int.units_eq_one_or (Equiv.Perm.sign q) with h2 | h2 <;> simp [h2]
      · exfalso
        obtain ⟨g, hg⟩ := isConj_iff.1 hconj
        have h1 : Θ y0 = Θ zb := by
          rw [← hg, map_mul, map_mul, map_inv, mul_comm (Θ g) (Θ zb), mul_assoc, mul_inv_cancel,
            mul_one]
        rw [hΘz, hΘy] at h1
        exact hS2 h1
    ·
      push Not at hII
      obtain ⟨g0, hg0e, hg0s⟩ := hII
      have hall : ∀ c ∈ (⊤ : Subgroup (Equiv.Perm (Fin 6))),
          ∀ d ∈ (⊤ : Subgroup (Equiv.Perm (Fin 6))), ∃ g : X, f g = ⟨c, d, false⟩ := by
        intro c _ d _
        by_cases hcd : Equiv.Perm.sign c = Equiv.Perm.sign d
        · exact h.exists_matched hcd
        · rcases hf0 : f g0 with ⟨a0, b0, e0⟩
          rw [hf0] at hg0e hg0s
          simp only at hg0e hg0s
          subst hg0e
          obtain ⟨g1, hg1⟩ := h.exists_matched (c := a0⁻¹ * c) (d := b0⁻¹ * d) (by
            simp only [map_mul, map_inv]
            rcases Int.units_eq_one_or (Equiv.Perm.sign a0) with h1 | h1 <;>
              rcases Int.units_eq_one_or (Equiv.Perm.sign b0) with h2 | h2 <;>
              rcases Int.units_eq_one_or (Equiv.Perm.sign c) with h3 | h3 <;>
              rcases Int.units_eq_one_or (Equiv.Perm.sign d) with h4 | h4 <;>
              simp_all)
          refine ⟨g0 * g1, ?_⟩
          rw [map_mul, hf0, hg1]
          simp
      have hconj : ∀ y ∈ P, y * y = 1 → (f y).e = true → ∃ c ∈ P, y = c⁻¹ * zb * c := by
        intro y hyP hy2 hye
        obtain ⟨p, hp⟩ := outer_form hy2 hye
        refine exists_mem_conj_of_flag f h.inj (A := ⊤) inferInstance hall hP2 hPidx h.zb2 hzo
          hzbP hyP hy2 ⟨?_, trivial, trivial⟩
        rw [map_mul, hu, hp]
        rfl
      exact ⟨fun y hyP hy2 hyB => Or.inl (hconj y hyP hy2 (hBe y hyB)), fun _ =>
        hconj y0 hy0P hy02 hy0e⟩

end WrSit

end CFSG.EvenSporadicStandard.M22Std
