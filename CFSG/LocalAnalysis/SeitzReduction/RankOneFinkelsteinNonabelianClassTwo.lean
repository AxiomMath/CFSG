module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneFinkelsteinAbelian
public import CFSG.LocalAnalysis.SeitzReduction.RankOneFinkelsteinNonabelianTrick
public import CFSG.LocalAnalysis.SeitzReduction.RankOneFinkelsteinLayer

public section

namespace CFSG.SeitzReduction.RankOne

open CFSG.ComponentClassification.GMS78.Finkelstein
open scoped commutatorElement

namespace Finkelstein.Hyp

variable {U : Type} [Group U] [Finite U] {n : ℕ} {t y : MulAut U} (h : Finkelstein.Hyp U n t y)
include h

theorem abelian_omega_or_elem (hc : ∀ a b : U, a * b = b * a) :
    (∀ x : U, x ^ 2 = 1 → x ∈ fixSubgroup t) ∨
      ((∀ a : U, a ^ 2 = 1) ∧ Nat.card U = 2 ^ (2 * n)) := by
  classical
  let _ : CommGroup U := { ‹Group U› with mul_comm := hc }
  set E := (powMonoidHom 2 : U →* U).ker with hEdef
  have hE : ∀ u, u ∈ E ↔ u ^ 2 = 1 := fun u => MonoidHom.mem_ker
  have hAE : fixSubgroup t ≤ E := fun a ha =>
    (hE a).mpr (by rw [pow_two]; exact h.mul_self_eq_one_of_mem_fix ha)
  have htE : ∀ x ∈ E, t x ∈ E := fun x hx => by
    rw [hE] at hx ⊢
    rw [← map_pow, hx, map_one]
  by_cases hEA : E ≤ fixSubgroup t
  · exact Or.inl fun x hx => hEA ((hE x).mpr hx)
  ·
    right
    obtain ⟨e₀, he₀E, he₀A⟩ := IsConcreteLE.not_le_iff_exists.mp hEA
    set psiH := psiHomOfComm hc t with hpsiH
    have hpsiE : ∀ e ∈ E, psi t e ∈ fixSubgroup t := by
      intro e he
      have he2 : e * e = 1 := by rw [← pow_two]; exact (hE e).mp he
      have hte2 : t e * t e = 1 := by rw [← map_mul, he2, map_one]
      show t (e⁻¹ * t e) = e⁻¹ * t e
      rw [map_mul, map_inv, h.t_t, inv_eq_of_mul_eq_one_right hte2,
        inv_eq_of_mul_eq_one_right he2]
      exact hc _ _
    have hAPE : fixSubgroup t ≤ E.map psiH := by
      refine h.fix_le_of_invariant (fun x hx => ?_) (fun x hx => ?_) ?_
      · obtain ⟨e, he, rfl⟩ := hx
        rw [show t (psiH e) = psiH e from hpsiE e he]
        exact ⟨e, he, rfl⟩
      · obtain ⟨e, he, rfl⟩ := hx
        refine ⟨y e, ?_, ?_⟩
        · show y e ∈ E
          have he' : e ∈ E := he
          rw [hE] at he' ⊢
          rw [← map_pow, he', map_one]
        · show (y e)⁻¹ * t (y e) = y (e⁻¹ * t e)
          rw [map_mul, map_inv, h.t_y]
      · intro hb
        have h1 : psiH e₀ ∈ E.map psiH := ⟨e₀, he₀E, rfl⟩
        rw [hb, Subgroup.mem_bot] at h1
        exact he₀A (psi_eq_one_iff.mp h1)
    have hEtop : E = ⊤ := by
      by_contra hne
      have : E.Normal := ⟨fun a ha g => by rw [hc g a, mul_inv_cancel_right]; exact ha⟩
      obtain ⟨u, huE, hpu⟩ := h.exists_not_mem_psi_mem htE hne
      have h2 : psi t u * psi t u = 1 := by rw [← pow_two]; exact (hE _).mp hpu
      have key : u * psi t u * (psi t u * psi t (psi t u)) = u := by
        rw [mul_psi, mul_psi, ← map_mul, mul_psi, h.t_t]
      have k2 : psi t u * (psi t u * psi t (psi t u)) = 1 := by
        rw [mul_assoc] at key
        exact mul_left_cancel (key.trans (mul_one u).symm)
      rw [← mul_assoc, h2, one_mul] at k2
      have hpA : psi t u ∈ fixSubgroup t := psi_eq_one_iff.mp k2
      obtain ⟨e, heE, hee⟩ := hAPE hpA
      have h3 : u * e⁻¹ ∈ fixSubgroup t := by
        rw [← psi_eq_one_iff, psi_mul_of_comm hc]
        have h4 : psi t e⁻¹ = (psi t e)⁻¹ := by
          have h5 := psi_mul_of_comm (t := t) hc e e⁻¹
          rw [mul_inv_cancel, psi_eq_one_iff.mpr (one_mem _), eq_comm,
            mul_eq_one_iff_eq_inv'] at h5
          exact h5
        rw [h4]
        have h6 : psi t e = psi t u := hee
        rw [h6, mul_inv_cancel]
      have h7 := mul_mem (hAE h3) heE
      rw [inv_mul_cancel_right] at h7
      exact huE h7
    have hall : ∀ a : U, a ^ 2 = 1 := fun a => (hE a).mp (hEtop ▸ Subgroup.mem_top a)
    refine ⟨hall, ?_⟩
    · have h1 := Subgroup.card_ker_mul_card_range psiH
      have hker : psiH.ker = fixSubgroup t := by
        ext u
        exact MonoidHom.mem_ker.trans psi_eq_one_iff
      have hrange : psiH.range = fixSubgroup t := by
        refine le_antisymm ?_ ?_
        · rintro _ ⟨u, rfl⟩
          exact hpsiE u (hEtop ▸ Subgroup.mem_top u)
        · exact hAPE.trans (Subgroup.map_le_range _ _)
      rw [hker, hrange, h.natCard_fix] at h1
      rw [← h1, ← pow_add, two_mul]

theorem abelian_pow_root (hc : ∀ a b : U, a * b = b * a)
    (hom : ∀ x : U, x ^ 2 = 1 → x ∈ fixSubgroup t) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : ∀ x : U, x ^ 2 ^ k = 1) (hx₀ : ∃ x₀ : U, x₀ ^ 2 ^ (k - 1) ≠ 1) {x : U}
    (hx : x ^ 2 ^ (k - 1) = 1) : ∃ z : U, z ^ 2 = x := by
  classical
  let _ : CommGroup U := { ‹Group U› with mul_comm := hc }
  set sq := (powMonoidHom 2 : U →* U) with hsq
  set P := (powMonoidHom (2 ^ (k - 1)) : U →* U) with hP
  have hkersq : sq.ker = fixSubgroup t := by
    ext x
    refine ⟨fun hx => hom x hx, fun hx => ?_⟩
    show x ^ 2 = 1
    rw [pow_two]
    exact h.mul_self_eq_one_of_mem_fix hx
  have hrangeP : P.range = fixSubgroup t := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, rfl⟩
      apply hom
      show (x ^ 2 ^ (k - 1)) ^ 2 = 1
      rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel hk1]
      exact hk x
    · refine h.fix_le_of_invariant (fun x hx => ?_) (fun x hx => ?_) ?_
      · obtain ⟨u, rfl⟩ := hx
        exact ⟨t u, by simp only [hP, powMonoidHom_apply, map_pow]⟩
      · obtain ⟨u, rfl⟩ := hx
        exact ⟨y u, by simp only [hP, powMonoidHom_apply, map_pow]⟩
      · obtain ⟨x₀, hx₀⟩ := hx₀
        intro hb
        have h1 : P x₀ ∈ P.range := ⟨x₀, rfl⟩
        rw [hb, Subgroup.mem_bot] at h1
        exact hx₀ h1
  have hle : sq.range ≤ P.ker := by
    rintro _ ⟨z, rfl⟩
    show (z ^ 2) ^ 2 ^ (k - 1) = 1
    rw [← pow_mul, ← pow_succ', Nat.sub_add_cancel hk1]
    exact hk z
  have hcard : Nat.card P.ker ≤ Nat.card sq.range := by
    have h1 := Subgroup.card_ker_mul_card_range sq
    have h2 := Subgroup.card_ker_mul_card_range P
    rw [hkersq] at h1
    rw [hrangeP] at h2
    have hA0 : 0 < Nat.card (fixSubgroup t) := Nat.card_pos
    rw [mul_comm] at h2
    exact (Nat.eq_of_mul_eq_mul_left hA0 (h2.trans h1.symm)).le
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard
  have hxP : x ∈ P.ker := hx
  rw [← heq] at hxP
  obtain ⟨z, hz⟩ := hxP
  exact ⟨z, hz⟩

theorem psi_mul_fix {a : U} (ha : a ∈ fixSubgroup t) (x : U) : psi t (x * a) = psi t x := by
  have hta : t a = a := ha
  have hc := h.mem_center_of_mem_fix ha (x⁻¹ * t x)
  unfold psi
  rw [map_mul, hta]
  calc (x * a)⁻¹ * (t x * a) = a⁻¹ * ((x⁻¹ * t x) * a) := by group
    _ = x⁻¹ * t x := by rw [hc]; group

theorem commutator_mul_left (hcomm : ∀ u v : U, ⁅u, v⁆ ∈ fixSubgroup t) (u v w : U) :
    ⁅u * v, w⁆ = ⁅u, w⁆ * ⁅v, w⁆ := by
  calc ⁅u * v, w⁆ = u * ⁅v, w⁆ * (w * u⁻¹ * w⁻¹) := by
        simp only [commutatorElement_def]; group
    _ = ⁅v, w⁆ * ⁅u, w⁆ := by
        rw [h.mem_center_of_mem_fix (hcomm v w) u, commutatorElement_def]; group
    _ = ⁅u, w⁆ * ⁅v, w⁆ := (h.mem_center_of_mem_fix (hcomm v w) _).symm

theorem commutator_mul_right (hcomm : ∀ u v : U, ⁅u, v⁆ ∈ fixSubgroup t) (u v w : U) :
    ⁅u, v * w⁆ = ⁅u, v⁆ * ⁅u, w⁆ := by
  calc ⁅u, v * w⁆ = ⁅u, v⁆ * (v * ⁅u, w⁆ * v⁻¹) := by
        simp only [commutatorElement_def]; group
    _ = ⁅u, v⁆ * ⁅u, w⁆ := by
        rw [h.mem_center_of_mem_fix (hcomm u w) v, mul_inv_cancel_right]

theorem commutator_fix_left {a : U} (ha : a ∈ fixSubgroup t) (v : U) : ⁅a, v⁆ = 1 := by
  rw [commutatorElement_eq_one_iff_mul_comm]
  exact (h.mem_center_of_mem_fix ha v).symm

theorem commutator_sq_left (hcomm : ∀ u v : U, ⁅u, v⁆ ∈ fixSubgroup t) (z v : U) :
    ⁅z ^ 2, v⁆ = 1 := by
  rw [pow_two, h.commutator_mul_left hcomm]
  exact h.mul_self_eq_one_of_mem_fix (hcomm z v)

theorem comm_of_classTwo (hcomm : ∀ u v : U, ⁅u, v⁆ ∈ fixSubgroup t)
    (homega : ∀ u : U, u ^ 2 ∈ fixSubgroup t → psi t u ∈ fixSubgroup t)
    (hsq : ∃ u : U, u ^ 2 ∉ fixSubgroup t) (u v : U) : u * v = v * u := by
  classical
  have hA : fixSubgroup t ≠ ⊤ := by
    intro hA
    obtain ⟨u, hu⟩ := hsq
    exact hu (hA ▸ Subgroup.mem_top _)
  have := h.fix_normal
  have hV := h.quot hA
  have hcV : ∀ a b : U ⧸ fixSubgroup t, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H u =>
      induction b using QuotientGroup.induction_on with
      | H v =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        have : (u * v)⁻¹ * (v * u) = ⁅v⁻¹, u⁻¹⁆ := by
          simp only [commutatorElement_def]; group
        rw [this]
        exact hcomm _ _
  have hmk : ∀ w : U, w ∈ fixSubgroup t ↔ (w : U ⧸ fixSubgroup t) = 1 := fun w =>
    (QuotientGroup.eq_one_iff w).symm
  have hex : ∃ k : ℕ, ∀ w : U, w ^ 2 ^ k ∈ fixSubgroup t := by
    obtain ⟨N, hN⟩ := IsPGroup.iff_card.mp h.pgroup
    exact ⟨N, fun w => by rw [← hN, pow_card_eq_one']; exact one_mem _⟩
  set k := Nat.find hex with hkdef
  have hk : ∀ w : U, w ^ 2 ^ k ∈ fixSubgroup t := Nat.find_spec hex
  have hk2 : 2 ≤ k := by
    by_contra hlt
    obtain ⟨w, hw⟩ := hsq
    apply hw
    have h1 := hk w
    rcases (show k = 0 ∨ k = 1 by omega) with h0 | h0
    · rw [h0, pow_zero, pow_one] at h1
      rw [pow_two]
      exact mul_mem h1 h1
    · rwa [h0, pow_one] at h1
  have hmin : ∃ u₀ : U, u₀ ^ 2 ^ (k - 1) ∉ fixSubgroup t := by
    by_contra hall
    push Not at hall
    exact Nat.find_min hex (show k - 1 < k by omega) hall
  have hθA : ∀ w : U, psi t (w ^ 2 ^ (k - 1)) ∈ fixSubgroup t := fun w => by
    apply homega
    rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ k)]
    exact hk w
  have hmod : ∀ w w' : U, (w ^ 2 ^ (k - 1) * w' ^ 2 ^ (k - 1))⁻¹ * (w * w') ^ 2 ^ (k - 1) ∈
      fixSubgroup t := by
    intro w w'
    rw [← QuotientGroup.eq]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_pow]
    exact (Commute.mul_pow (hcV _ _) _).symm
  let θ : U →* U :=
    { toFun := fun w => psi t (w ^ 2 ^ (k - 1))
      map_one' := by
        show psi t (1 ^ 2 ^ (k - 1)) = 1
        rw [one_pow]
        exact psi_eq_one_iff.mpr (one_mem _)
      map_mul' := fun w w' => by
        show psi t ((w * w') ^ 2 ^ (k - 1)) =
          psi t (w ^ 2 ^ (k - 1)) * psi t (w' ^ 2 ^ (k - 1))
        rw [show (w * w') ^ 2 ^ (k - 1) = w ^ 2 ^ (k - 1) * w' ^ 2 ^ (k - 1) *
            ((w ^ 2 ^ (k - 1) * w' ^ 2 ^ (k - 1))⁻¹ * (w * w') ^ 2 ^ (k - 1)) by group,
          h.psi_mul_fix (hmod w w'), h.psi_mul_of_mem (hθA w)] }
  have hθy : ∀ w, θ (y w) = y (θ w) := fun w => by
    show psi t ((y w) ^ 2 ^ (k - 1)) = y (psi t (w ^ 2 ^ (k - 1)))
    rw [← map_pow, psi_map_of_comm h.comm]
  have homV : ∀ x : U ⧸ fixSubgroup t, x ^ 2 = 1 →
      x ∈ fixSubgroup (quotAut t (map_fix_of_comm (s := t) rfl)) := by
    intro x hx
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective x
    rw [← QuotientGroup.mk_pow, ← hmk] at hx
    exact (quotAut_mk_eq_iff w).mpr (homega w hx)
  have hkV : ∀ x : U ⧸ fixSubgroup t, x ^ 2 ^ k = 1 := by
    intro x
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective x
    rw [← QuotientGroup.mk_pow, ← hmk]
    exact hk w
  have hx₀V : ∃ x₀ : U ⧸ fixSubgroup t, x₀ ^ 2 ^ (k - 1) ≠ 1 := by
    obtain ⟨u₀, hu₀⟩ := hmin
    exact ⟨u₀, by rw [← QuotientGroup.mk_pow]; exact fun h1 => hu₀ ((hmk _).mpr h1)⟩
  have hβθ : ∀ w w' : U, θ w = 1 → ⁅w, w'⁆ = 1 := by
    intro w w' hw
    have hw' : w ^ 2 ^ (k - 1) ∈ fixSubgroup t := psi_eq_one_iff.mp hw
    obtain ⟨z, hz⟩ := hV.abelian_pow_root hcV homV (k := k) (by omega) hkV hx₀V
      (x := (w : U ⧸ fixSubgroup t)) (by rw [← QuotientGroup.mk_pow]; exact (hmk _).mp hw')
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective z
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq] at hz
    rw [show w = z ^ 2 * ((z ^ 2)⁻¹ * w) by group, h.commutator_mul_left hcomm,
      h.commutator_sq_left hcomm, h.commutator_fix_left hz, one_mul]
  have hall := h.trick_bilin θ hθA hθy (β := fun a b => ⁅a, b⁆) (fun a b => hcomm a b)
    (h.commutator_mul_left hcomm) (h.commutator_mul_right hcomm)
    (fun a b => (map_commutatorElement y a b).symm) (fun a => commutatorElement_self a) hβθ u v
  exact commutatorElement_eq_one_iff_mul_comm.mp hall

theorem quot_elem_of_classTwo (hcomm : ∀ u v : U, ⁅u, v⁆ ∈ fixSubgroup t)
    (hnc : ∃ a b : U, a * b ≠ b * a) :
    (∀ u : U, u ^ 2 ∈ fixSubgroup t) ∧ Nat.card U = 2 ^ (3 * n) := by
  classical
  obtain ⟨a, b, hab⟩ := hnc
  have hA : fixSubgroup t ≠ ⊤ := by
    intro hA
    exact hab (h.mem_center_of_mem_fix (hA ▸ Subgroup.mem_top b) a)
  have := h.fix_normal
  have hV := h.quot hA
  have hcV : ∀ a b : U ⧸ fixSubgroup t, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H u =>
      induction b using QuotientGroup.induction_on with
      | H v =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        have : (u * v)⁻¹ * (v * u) = ⁅v⁻¹, u⁻¹⁆ := by
          simp only [commutatorElement_def]; group
        rw [this]
        exact hcomm _ _
  have hmk : ∀ w : U, w ∈ fixSubgroup t ↔ (w : U ⧸ fixSubgroup t) = 1 := fun w =>
    (QuotientGroup.eq_one_iff w).symm
  rcases hV.abelian_omega_or_elem hcV with hom | ⟨hel, hcard⟩
  · exfalso
    have homega : ∀ u : U, u ^ 2 ∈ fixSubgroup t → psi t u ∈ fixSubgroup t := by
      intro u hu
      rw [hmk, QuotientGroup.mk_pow] at hu
      exact (quotAut_mk_eq_iff u).mp (hom _ hu)
    by_cases hsq : ∃ u : U, u ^ 2 ∉ fixSubgroup t
    · exact hab (h.comm_of_classTwo hcomm homega hsq a b)
    · push Not at hsq
      have hB : h.bSub = ⊤ := by
        rw [eq_top_iff]
        intro u _
        exact homega u (hsq u)
      exact hab (h.bSub_comm hA (hB ▸ Subgroup.mem_top a) (hB ▸ Subgroup.mem_top b))
  · refine ⟨fun u => ?_, ?_⟩
    · rw [hmk, QuotientGroup.mk_pow]
      exact hel _
    · rw [h.natCard_eq_quot_mul, hcard, ← pow_add]
      congr 1
      ring



end Finkelstein.Hyp

end CFSG.SeitzReduction.RankOne
