module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21FinA6
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.AutA6Three

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts CFSG.QuasithinUnique.Setup.X3Aut
  AutA6Three CFSG.QuasithinUnique.Out21.A6

namespace AutA6Types

@[expose] def fixes3 (c : List ℕ) : Bool :=
  ord3P.any fun a => Core.cmul c a == Core.cmul a c

@[expose] def invOut : List (List ℕ) :=
  Core.autL.filter fun c => Core.cmul c c == Core.cid && !Core.pslLit.contains c

@[expose] def inPgl (c : List ℕ) : Bool :=
  Core.pslLit.contains c || Core.pslLit.contains (Core.cmul c [0, 5, 7, 8, 1, 3, 4, 6, 2, 9])

theorem pglRepsInvC_eq : pglRepsInvC = [Core.cid, [0, 5, 7, 8, 1, 3, 4, 6, 2, 9]] := by
  decide +kernel

theorem inPglC_code (x : P10) : inPglC (code x) = inPgl (code x) := by
  unfold inPglC inPgl
  rw [pglRepsInvC_eq, List.any_cons, List.any_cons, List.any_nil, Bool.or_false]
  have : Core.cmul (code x) Core.cid = code x := by
    rw [← code_one, ← code_mul, mul_one]
  rw [this]

@[expose] def invFix : List (List ℕ) := invOut.filter fixes3

@[expose] def invNoFix : List (List ℕ) := invOut.filter fun c => !fixes3 c

theorem types_check : invFix.all (fun c => invNoFix.all fun d =>
    !Core.pslLit.contains (Core.cmul c d)) = true := by
  decide +kernel

theorem pgl_check : invOut.all (fun c => fixes3 c || inPgl c) = true := by
  decide +kernel

theorem mem_PslSub_iff_contains (w : AutA6) : w ∈ PslSub ↔ Core.pslLit.contains (cd w) = true := by
  rw [mem_PslSub, mem_psl29_iff, List.contains_iff_mem]
  rfl

theorem mem_inner_iff (α : MulAut (alternatingGroup (Fin 6))) :
    α ∈ (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range ↔
      thetaEquiv.symm α ∈ PslSub := by
  rw [← map_PslSub_eq_inner]
  constructor
  · rintro ⟨b, hb, rfl⟩
    simpa using hb
  · intro h
    exact ⟨_, h, MulEquiv.apply_symm_apply thetaEquiv α⟩

theorem fixes3_iff (y : AutA6) :
    (∃ a : alternatingGroup (Fin 6), orderOf a = 3 ∧ thetaEquiv y a = a) ↔
      fixes3 (cd y) = true := by
  constructor
  · rintro ⟨a, ha, hya⟩
    set w : ↥A6Models.psl29 := psiEquiv.symm a with hw
    set pt : AutA6 := ⟨(w : P10), psl29_le_autA6 w.2⟩ with hpt
    have hθ : thetaEquiv pt = MulAut.conj a := by
      rw [hpt, thetaEquiv_mk, hw, MulEquiv.apply_symm_apply]
    have h1 : thetaEquiv (y * pt * y⁻¹) = thetaEquiv pt := by
      rw [map_mul, map_mul, map_inv, hθ, conj_thetaEquiv_apply, hya]
    have h2 := thetaEquiv.injective h1
    rw [mul_inv_eq_iff_eq_mul] at h2
    have h3 := congrArg cd h2
    rw [cd_mul, cd_mul] at h3
    unfold fixes3
    rw [List.any_eq_true]
    exact ⟨cd pt, code_mem_ord3P_of_orderOf ha, by simpa using h3⟩
  · intro h
    unfold fixes3 at h
    obtain ⟨a0, ha0, hcomm⟩ := List.any_eq_true.mp h
    simp only [beq_iff_eq] at hcomm
    unfold ord3P at ha0
    rw [List.mem_filter] at ha0
    obtain ⟨ha0P, ha0c⟩ := ha0
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at ha0c
    obtain ⟨p, hp, rfl⟩ := exists_psl29_of_code ha0P
    have hp3 : p * (p * p) = 1 := by
      apply code_injective
      rw [code_mul, code_mul, code_one]
      exact ha0c.1
    have hp1 : p ≠ 1 := by
      intro h1
      apply ha0c.2
      rw [h1, code_one]
    set w : ↥A6Models.psl29 := ⟨p, hp⟩ with hw
    set pt : AutA6 := ⟨p, psl29_le_autA6 hp⟩ with hpt
    have hw3 : w ^ 3 = 1 := by
      rw [pow_three]
      exact Subtype.ext hp3
    have hw1 : w ≠ 1 := fun h1 => hp1 (congrArg Subtype.val h1)
    have hx3 : orderOf (psiEquiv w) = 3 := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      refine orderOf_eq_prime ?_ ?_
      · rw [← map_pow, hw3, map_one]
      · intro h1
        apply hw1
        simpa using h1
    refine ⟨psiEquiv w, hx3, ?_⟩
    have hθ : thetaEquiv pt = MulAut.conj (psiEquiv w) := thetaEquiv_mk w
    have hpy : y * pt = pt * y := by
      apply cd_injective
      rw [cd_mul, cd_mul]
      exact hcomm
    have h1 : thetaEquiv y * MulAut.conj (psiEquiv w) * (thetaEquiv y)⁻¹ =
        MulAut.conj (psiEquiv w) := by
      rw [← hθ, ← map_inv, ← map_mul, ← map_mul, hpy, mul_inv_cancel_right]
    rw [conj_thetaEquiv_apply] at h1
    exact CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.inner_conjugation_injective h1

theorem cd_mem_invOut {y : AutA6} (h2 : y * y = 1) (hy : y ∉ PslSub) : cd y ∈ invOut := by
  unfold invOut
  rw [List.mem_filter]
  refine ⟨cd_mem_autL y, ?_⟩
  rw [← cd_mul, h2, cd_one]
  rw [mem_PslSub_iff_contains] at hy
  simp only [beq_self_eq_true, Bool.true_and, Bool.not_eq_eq_eq_not, Bool.not_true] at hy ⊢
  simpa using hy

theorem aut_mul_self {α : MulAut (alternatingGroup (Fin 6))} (h : α * α = 1) :
    thetaEquiv.symm α * thetaEquiv.symm α = 1 := by
  rw [← map_mul, h, map_one]

end AutA6Types

open AutA6Types

theorem mul_not_mem_inner_of_types {α β : MulAut (alternatingGroup (Fin 6))}
    (hα2 : α * α = 1) (hβ2 : β * β = 1)
    (hα : α ∉ (MulAut.conj : alternatingGroup (Fin 6) →*
      MulAut (alternatingGroup (Fin 6))).range)
    (hβ : β ∉ (MulAut.conj : alternatingGroup (Fin 6) →*
      MulAut (alternatingGroup (Fin 6))).range)
    (hαfix : ∃ a, orderOf a = 3 ∧ α a = a) (hβfix : ∀ a, orderOf a = 3 → β a ≠ a) :
    α * β ∉ (MulAut.conj : alternatingGroup (Fin 6) →*
      MulAut (alternatingGroup (Fin 6))).range := by
  intro hαβ
  set y : AutA6 := thetaEquiv.symm α with hy
  set z : AutA6 := thetaEquiv.symm β with hz
  have hyα : thetaEquiv y = α := MulEquiv.apply_symm_apply _ _
  have hzβ : thetaEquiv z = β := MulEquiv.apply_symm_apply _ _
  have hy2 : y * y = 1 := aut_mul_self hα2
  have hz2 : z * z = 1 := aut_mul_self hβ2
  have hyP : y ∉ PslSub := fun h => hα ((mem_inner_iff α).2 h)
  have hzP : z ∉ PslSub := fun h => hβ ((mem_inner_iff β).2 h)
  have hyz : y * z ∈ PslSub := by
    have h := (mem_inner_iff _).1 hαβ
    rwa [map_mul] at h
  have hfy : fixes3 (cd y) = true := (fixes3_iff y).1 (by rw [hyα]; exact hαfix)
  have hfz : fixes3 (cd z) = false := by
    rw [Bool.eq_false_iff]
    intro h
    obtain ⟨a, ha3, ha⟩ := (fixes3_iff z).2 h
    rw [hzβ] at ha
    exact hβfix a ha3 ha
  have hmy : cd y ∈ invFix := by
    unfold invFix
    rw [List.mem_filter]
    exact ⟨cd_mem_invOut hy2 hyP, hfy⟩
  have hmz : cd z ∈ invNoFix := by
    unfold invNoFix
    rw [List.mem_filter]
    exact ⟨cd_mem_invOut hz2 hzP, by rw [hfz]; rfl⟩
  have h1 := List.all_eq_true.mp types_check _ hmy
  have h2 := List.all_eq_true.mp h1 _ hmz
  rw [mem_PslSub_iff_contains, cd_mul] at hyz
  rw [hyz] at h2
  simp at h2

theorem nonempty_mulEquiv_pgl29_of_type {K : Type*} [Group K] (H : Subgroup K) (g : K)
    (A : Subgroup K) (hA : A ≤ H) (e : ↥A ≃* alternatingGroup (Fin 6)) (hgH : g ∈ H)
    (hg2 : g * g = 1) (_hgA : g ∉ A) (hH : H = A ⊔ Subgroup.zpowers g)
    (hn : ∀ a ∈ A, g * a * g⁻¹ ∈ A)
    (hβfix : ∀ a ∈ A, orderOf a = 3 → g * a * g⁻¹ ≠ a)
    (hβout : ∀ b ∈ A, ∃ a ∈ A, g * a * g⁻¹ ≠ b * a * b⁻¹) :
    Nonempty (↥H ≃* ↥A6Models.pgl29) := by
  have hgi : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg2
  set N : Subgroup K := Subgroup.normalizer (A : Set K) with hNdef
  have hAN : A ≤ N := Subgroup.le_normalizer
  have hgN : g ∈ N := by
    rw [hNdef, Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hn h hh, fun hh => ?_⟩
    have h3 := hn _ hh
    have h4 : g * (g * h * g⁻¹) * g⁻¹ = (g * g) * h * (g * g)⁻¹ := by group
    rw [h4, hg2] at h3
    simpa using h3
  have hzN : Subgroup.zpowers g ≤ N := (Subgroup.zpowers_le).2 hgN
  have hHN : H ≤ N := hH ▸ sup_le hAN hzN
  have hdec : ∀ h ∈ H, (∃ a : A, h = a) ∨ (∃ a : A, h = a * g) := by
    intro h hh
    rw [hH, ← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left A _ hzN] at hh
    obtain ⟨a, ha, k, hk, rfl⟩ := Set.mem_mul.mp hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    rcases Int.even_or_odd' n with ⟨m, rfl | rfl⟩
    · left
      refine ⟨⟨a, ha⟩, ?_⟩
      rw [zpow_mul, zpow_two, hg2, one_zpow, mul_one]
    · right
      refine ⟨⟨a, ha⟩, ?_⟩
      rw [zpow_add_one, zpow_mul, zpow_two, hg2, one_zpow, one_mul]
  let Φ : ↥N →* MulAut (alternatingGroup (Fin 6)) :=
    (MulAut.congr e).toMonoidHom.comp A.normalizerMonoidHom
  let Ψ1 : ↥N →* AutA6 := thetaEquiv.symm.toMonoidHom.comp Φ
  have hΦ : ∀ (n : ↥N) (z : alternatingGroup (Fin 6)),
      ((e.symm (Φ n z) : ↥A) : K) = (n : K) * (e.symm z : K) * (n : K)⁻¹ := fun n z => by simp [Φ]; rfl
  let nA : ↥A → ↥N := fun a => ⟨a, hAN a.2⟩
  let ng : ↥N := ⟨g, hgN⟩
  have hinn : ∀ a : ↥A, Φ (nA a) = MulAut.conj (e a) := by
    intro a
    refine MulEquiv.ext fun z => e.symm.injective (Subtype.ext ?_)
    rw [hΦ]
    simp [MulAut.conj_apply, nA]
  have hΨ1 : ∀ n : ↥N, thetaEquiv (Ψ1 n) = Φ n := fun n => MulEquiv.apply_symm_apply _ _
  have hβ2 : Φ ng * Φ ng = 1 := by
    rw [← map_mul]
    have : ng * ng = 1 := Subtype.ext hg2
    rw [this, map_one]
  have hβout' : Φ ng ∉ (MulAut.conj : alternatingGroup (Fin 6) →*
      MulAut (alternatingGroup (Fin 6))).range := by
    rintro ⟨b0, hb0⟩
    obtain ⟨a, haA, hne⟩ := hβout (e.symm b0 : ↥A) (e.symm b0).2
    apply hne
    have h1 := congrArg (fun γ : MulAut (alternatingGroup (Fin 6)) => ((e.symm (γ (e ⟨a, haA⟩)) : ↥A) : K)) hb0
    simp only [hΦ, MulAut.conj_apply, MulEquiv.symm_apply_apply, map_mul, map_inv,
      Subgroup.coe_mul, Subgroup.coe_inv] at h1
    exact h1.symm
  have hβfix' : ∀ a' : alternatingGroup (Fin 6), orderOf a' = 3 → Φ ng a' ≠ a' := by
    intro a' ha3 hfix
    have ha : ((e.symm a' : ↥A) : K) ∈ A := (e.symm a').2
    have ho : orderOf ((e.symm a' : ↥A) : K) = 3 := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ha3]
    apply hβfix _ ha ho
    have h1 := congrArg (fun a'' => ((e.symm a'' : ↥A) : K)) hfix
    simp only [hΦ] at h1
    exact h1
  set z0 : AutA6 := Ψ1 ng with hz0
  have hz0θ : thetaEquiv z0 = Φ ng := hΨ1 ng
  have hz02 : z0 * z0 = 1 := by
    rw [← map_mul]
    have : ng * ng = 1 := Subtype.ext hg2
    rw [this, map_one]
  have hz0P : z0 ∉ PslSub := by
    intro h
    apply hβout'
    rw [mem_inner_iff, ← hz0θ, MulEquiv.symm_apply_apply]
    exact h
  have hz0fix : fixes3 (cd z0) = false := by
    rw [Bool.eq_false_iff]
    intro h
    obtain ⟨a, ha3, ha⟩ := (fixes3_iff z0).2 h
    rw [hz0θ] at ha
    exact hβfix' a ha3 ha
  have hz0mem := cd_mem_invOut hz02 hz0P
  have hz0pgl : inPgl (cd z0) = true := by
    have := List.all_eq_true.mp pgl_check _ hz0mem
    rw [hz0fix, Bool.false_or] at this
    exact this
  have hz0pgl' : ((z0 : AutA6) : P10) ∈ A6Models.pgl29 :=
    (mem_pgl29_iff_code _).2 (by rw [inPglC_code]; exact hz0pgl)
  have hsA : ∀ a : ↥A, Ψ1 (nA a) ∈ PslSub := by
    intro a
    rw [mem_PslSub, ← mem_PslSub]
    have : thetaEquiv.symm (Φ (nA a)) ∈ PslSub := by
      rw [← mem_inner_iff, hinn]
      exact ⟨e a, rfl⟩
    exact this
  have hrange : ∀ (h : K) (hhN : h ∈ N), h ∈ H → ((Ψ1 ⟨h, hhN⟩ : AutA6) : P10) ∈ A6Models.pgl29 := by
    intro h hhN hh
    rcases hdec h hh with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · have h1 : Ψ1 ⟨(a : K), hhN⟩ = Ψ1 (nA a) := rfl
      rw [h1]
      exact psl29_le_pgl29 (hsA a)
    · have h1 : Ψ1 ⟨(a : K) * g, hhN⟩ = Ψ1 (nA a) * z0 := by
        rw [hz0, ← map_mul]
        rfl
      rw [h1]
      exact A6Models.pgl29.mul_mem (psl29_le_pgl29 (hsA a)) hz0pgl'
  let Ψ2 : ↥H →* AutA6 := Ψ1.comp (Subgroup.inclusion hHN)
  let Ψ : ↥H →* ↥A6Models.pgl29 :=
    { toFun := fun h => ⟨((Ψ2 h : AutA6) : P10), hrange h (hHN h.2) h.2⟩
      map_one' := Subtype.ext (congrArg (fun x : AutA6 => (x : P10)) (map_one Ψ2))
      map_mul' := fun x y => Subtype.ext (congrArg (fun x : AutA6 => (x : P10)) (map_mul Ψ2 x y)) }
  have hΨinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_one]
    intro h hh1
    have hΨ1h : Ψ1 ⟨h, hHN h.2⟩ = 1 := Subtype.ext (congrArg (fun x : ↥A6Models.pgl29 => (x : P10)) hh1)
    have hΦ1 : Φ ⟨h, hHN h.2⟩ = 1 := by rw [← hΨ1, hΨ1h, map_one]
    rcases hdec h h.2 with ⟨a, ha⟩ | ⟨a, ha⟩
    · have h1 : (⟨(h : K), hHN h.2⟩ : ↥N) = nA a := Subtype.ext ha
      rw [h1, hinn] at hΦ1
      have h2 : e a = 1 :=
        CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.inner_conjugation_injective
          (by rw [hΦ1, map_one])
      have h3 : a = 1 := by simpa using h2
      exact Subtype.ext (by rw [ha, h3]; rfl)
    · exfalso
      have h1 : (⟨(h : K), hHN h.2⟩ : ↥N) = nA a * ng := Subtype.ext ha
      rw [h1, map_mul, hinn] at hΦ1
      have h2 := eq_inv_of_mul_eq_one_right hΦ1
      apply hβout'
      refine ⟨(e a)⁻¹, ?_⟩
      rw [h2, map_inv]
  have hPsl : ∀ s : AutA6, s ∈ PslSub → ∃ a : ↥A, Ψ1 (nA a) = s := by
    intro s hs
    refine ⟨e.symm (psiEquiv ⟨(s : P10), hs⟩), ?_⟩
    apply thetaEquiv.injective
    rw [hΨ1, hinn, MulEquiv.apply_symm_apply, thetaEquiv_psl s hs]
  have hcos : ∀ x : P10, x ∈ A6Models.pgl29 → x ∉ A6Models.psl29 →
      x * A6Models.tMul⁻¹ ∈ A6Models.psl29 := by
    intro x hx hxn
    obtain ⟨r, hr, hxr⟩ := (mem_pgl29_iff x).1 hx
    simp only [pglReps, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact absurd (by simpa using hxr) hxn
    · exact hxr
  have hz0t := hcos _ hz0pgl' hz0P
  have hz0inv : ((z0 : AutA6) : P10)⁻¹ = (z0 : P10) :=
    inv_eq_of_mul_eq_one_right (by simpa using congrArg Subtype.val hz02)
  have hΨsurj : Function.Surjective Ψ := by
    rintro ⟨q, hq⟩
    set q' : AutA6 := ⟨q, pgl29_le_autA6 hq⟩ with hq'
    by_cases hqP : q ∈ A6Models.psl29
    · obtain ⟨a, ha⟩ := hPsl q' hqP
      exact ⟨⟨(a : K), hA a.2⟩, Subtype.ext (congrArg (fun x : AutA6 => (x : P10)) ha)⟩
    · have hqt := hcos q hq hqP
      have hs : q' * z0 ∈ PslSub := by
        have h1 := A6Models.psl29.mul_mem hqt (A6Models.psl29.inv_mem hz0t)
        have e1 : q * A6Models.tMul⁻¹ * ((z0 : P10) * A6Models.tMul⁻¹)⁻¹ = q * (z0 : P10)⁻¹ := by
          group
        rw [e1, hz0inv] at h1
        exact h1
      obtain ⟨a, ha⟩ := hPsl _ hs
      refine ⟨⟨a * g, H.mul_mem (hA a.2) hgH⟩, Subtype.ext ?_⟩
      have h3 : Ψ1 ⟨(a : K) * g, hHN (H.mul_mem (hA a.2) hgH)⟩ = Ψ1 (nA a * ng) := rfl
      have h4 : ((Ψ ⟨a * g, H.mul_mem (hA a.2) hgH⟩ : ↥A6Models.pgl29) : P10) =
          ((Ψ1 ⟨(a : K) * g, hHN (H.mul_mem (hA a.2) hgH)⟩ : AutA6) : P10) := rfl
      rw [h4, h3, map_mul, ha, mul_assoc, hz02, mul_one]
  exact ⟨MulEquiv.ofBijective Ψ ⟨hΨinj, hΨsurj⟩⟩

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
