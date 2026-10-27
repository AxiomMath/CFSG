module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21LHomA
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21L

namespace Hom

open Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
  {G : Type*} [Group G]

theorem pow_mem_iff_dvd (M : Subgroup G) [M.Normal] {q : ℕ} (hq : q.Prime) (hMq : M.index = q)
    {h : G} (hh : h ∉ M) (j : ℕ) : h ^ j ∈ M ↔ q ∣ j := by
  have h1 : orderOf (h : G ⧸ M) ∣ q := by
    have := orderOf_dvd_natCard (h : G ⧸ M)
    rwa [← Subgroup.index, hMq] at this
  have h2 : orderOf (h : G ⧸ M) ≠ 1 := by
    intro h3
    rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
    exact hh h3
  have h3 : orderOf (h : G ⧸ M) = q := ((Nat.dvd_prime hq).mp h1).resolve_left h2
  rw [← h3, orderOf_dvd_iff_pow_eq_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]

theorem eq_or_eq_top_of_le (M H : Subgroup G) {q : ℕ} (hq : q.Prime) (hMq : M.index = q)
    (hMH : M ≤ H) : H = M ∨ H = ⊤ := by
  have := (Subgroup.isCoatom_of_index_prime (hMq ▸ hq)).le_iff.mp hMH
  tauto

@[expose] def centE (ρ : G →* (V ≃ₗ[ZMod 2] V)) (e : Module.End (ZMod 2) V) : Subgroup G where
  carrier := {g | er ρ g * e = e * er ρ g}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_mul] at ha hb ⊢
    rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  one_mem' := by simp
  inv_mem' := by
    intro g hg
    simp only [Set.mem_setOf_eq] at hg ⊢
    have h1 : er ρ g * er ρ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have h2 : er ρ g⁻¹ * er ρ g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    calc er ρ g⁻¹ * e = er ρ g⁻¹ * e * (er ρ g * er ρ g⁻¹) := by rw [h1, mul_one]
      _ = er ρ g⁻¹ * (e * er ρ g) * er ρ g⁻¹ := by simp only [mul_assoc]
      _ = er ρ g⁻¹ * (er ρ g * e) * er ρ g⁻¹ := by rw [hg]
      _ = (er ρ g⁻¹ * er ρ g) * e * er ρ g⁻¹ := by simp only [mul_assoc]
      _ = e * er ρ g⁻¹ := by rw [h2, one_mul]

theorem finrank_range_cj (ρ : G →* (V ≃ₗ[ZMod 2] V)) (g : G) (e : Module.End (ZMod 2) V) :
    finrank (ZMod 2) (LinearMap.range (cj ρ g e)) = finrank (ZMod 2) (LinearMap.range e) := by
  have h : (LinearMap.range e).map (ρ g : V →ₗ[ZMod 2] V) = LinearMap.range (cj ρ g e) := by
    ext x
    constructor
    · rintro ⟨y, ⟨w, rfl⟩, rfl⟩
      refine ⟨ρ g w, ?_⟩
      simp [cj_apply, er_apply]
    · rintro ⟨v, rfl⟩
      refine ⟨e (ρ g⁻¹ v), ⟨_, rfl⟩, ?_⟩
      simp [cj_apply, er_apply]
  exact (LinearEquiv.ofSubmodules (ρ g) _ _ h).finrank_eq.symm

theorem eq_one_of_idem_range_top {e : Module.End (ZMod 2) V} (hi : e * e = e)
    (h : LinearMap.range e = ⊤) : e = 1 := by
  ext v
  obtain ⟨w, rfl⟩ : v ∈ LinearMap.range e := by rw [h]; trivial
  have := congrArg (fun y => y w) hi
  simpa using this

theorem eq_of_finrank_range_eq_of_idem {e p : Module.End (ZMod 2) V}
    (hle : LinearMap.range p ≤ LinearMap.range e)
    (hr : finrank (ZMod 2) (LinearMap.range e) ≤ finrank (ZMod 2) (LinearMap.range p)) :
    LinearMap.range p = LinearMap.range e :=
  Submodule.eq_of_le_of_finrank_le hle hr

theorem eq_of_range_eq {a p : Module.End (ZMod 2) V} (hpi : p * p = p) (hpa : p * a = p)
    (hra : LinearMap.range a = LinearMap.range p) : a = p := by
  ext v
  have hav : a v ∈ LinearMap.range p := by rw [← hra]; exact ⟨v, rfl⟩
  obtain ⟨w, hw⟩ := hav
  have h1 : p (a v) = a v := by
    rw [← hw]
    have := congrArg (fun y => y w) hpi
    simpa using this
  have h2 : p (a v) = p v := by
    have := congrArg (fun y => y v) hpa
    simpa using this
  rw [← h1, h2]

theorem orth_of_minimal (ρ : G →* (V ≃ₗ[ZMod 2] V)) (M : Subgroup G) {e e' : Module.End (ZMod 2) V}
    (he : e ∈ cz ρ M) (he' : e' ∈ cz ρ M) (hi : e * e = e) (hi' : e' * e' = e')
    (r : ℕ) (hr : finrank (ZMod 2) (LinearMap.range e) = r)
    (hr' : finrank (ZMod 2) (LinearMap.range e') = r)
    (hmin : ∀ z ∈ cz ρ M, z * z = z → z ≠ 0 → r ≤ finrank (ZMod 2) (LinearMap.range z))
    (hne : e ≠ e') : e * e' = 0 := by
  have hcomm : e * e' = e' * e := ((mem_cz ρ M e').mp he').2 e ((mem_cz ρ M e).mp he).1
  by_contra hp0
  have hpc : e * e' ∈ cz ρ M := Subalgebra.mul_mem _ he he'
  have hpi : e * e' * (e * e') = e * e' := by
    calc e * e' * (e * e') = e * (e' * e) * e' := by simp only [mul_assoc]
      _ = e * (e * e') * e' := by rw [hcomm]
      _ = (e * e) * (e' * e') := by simp only [mul_assoc]
      _ = e * e' := by rw [hi, hi']
  have hrk := hmin _ hpc hpi hp0
  have h1 : LinearMap.range (e * e') ≤ LinearMap.range e := by
    rintro x ⟨y, rfl⟩; exact ⟨e' y, rfl⟩
  have h2 : LinearMap.range (e * e') ≤ LinearMap.range e' := by
    rw [hcomm]; rintro x ⟨y, rfl⟩; exact ⟨e y, rfl⟩
  have hr1 := eq_of_finrank_range_eq_of_idem h1 (by omega)
  have hr2 := eq_of_finrank_range_eq_of_idem h2 (by omega)
  have hpe : e * e' * e = e * e' := by
    calc e * e' * e = e * (e' * e) := by rw [mul_assoc]
      _ = e * (e * e') := by rw [hcomm]
      _ = (e * e) * e' := by rw [← mul_assoc]
      _ = e * e' := by rw [hi]
  have hpe' : e * e' * e' = e * e' := by
    rw [mul_assoc, hi']
  have ha := eq_of_range_eq hpi hpe hr1.symm
  have hb := eq_of_range_eq hpi hpe' hr2.symm
  exact hne (ha.trans hb.symm)

theorem finrank_range_add {F a : Module.End (ZMod 2) V} (hF : F * F = F) (ha : a * a = a)
    (hFa : F * a = 0) (haF : a * F = 0) :
    finrank (ZMod 2) (LinearMap.range (F + a)) =
      finrank (ZMod 2) (LinearMap.range F) + finrank (ZMod 2) (LinearMap.range a) := by
  have hsup : LinearMap.range (F + a) = LinearMap.range F ⊔ LinearMap.range a := by
    apply le_antisymm
    · rintro x ⟨v, rfl⟩
      exact Submodule.add_mem_sup ⟨v, rfl⟩ ⟨v, rfl⟩
    · apply sup_le
      · rintro x ⟨w, rfl⟩
        refine ⟨F w, ?_⟩
        have h1 := congrArg (fun y => y w) hF
        have h2 := congrArg (fun y => y w) haF
        simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply] at h1 h2 ⊢
        rw [h1, h2, add_zero]
      · rintro x ⟨w, rfl⟩
        refine ⟨a w, ?_⟩
        have h1 := congrArg (fun y => y w) ha
        have h2 := congrArg (fun y => y w) hFa
        simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply] at h1 h2 ⊢
        rw [h1, h2, zero_add]
  have hdisj : Disjoint (LinearMap.range F) (LinearMap.range a) := by
    rw [Submodule.disjoint_def]
    rintro x ⟨u, rfl⟩ ⟨w, hw⟩
    have h1 : F (F u) = F u := by
      have := congrArg (fun y => y u) hF
      simpa using this
    have h2 : F (a w) = 0 := by
      have := congrArg (fun y => y w) hFa
      simpa using this
    rw [hw, h1] at h2
    exact h2
  have := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range F) (LinearMap.range a)
  rw [← hsup, disjoint_iff.mp hdisj, finrank_bot, add_zero] at this
  exact this

theorem sum_idem_rank {e : ℕ → Module.End (ZMod 2) V} (n : ℕ)
    (hi : ∀ i < n, e i * e i = e i) (ho : ∀ i < n, ∀ j < n, i ≠ j → e i * e j = 0) :
    (∑ i ∈ Finset.range n, e i) * (∑ i ∈ Finset.range n, e i) = ∑ i ∈ Finset.range n, e i ∧
    finrank (ZMod 2) (LinearMap.range (∑ i ∈ Finset.range n, e i)) =
      ∑ i ∈ Finset.range n, finrank (ZMod 2) (LinearMap.range (e i)) := by
  induction n with
  | zero =>
    refine ⟨by simp, ?_⟩
    have h0 : LinearMap.range (∑ i ∈ Finset.range 0, e i) = ⊥ := by
      rw [Finset.sum_range_zero]; exact LinearMap.range_zero
    rw [h0, finrank_bot]
    simp
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun i hi' => hi i (by omega))
      (fun i hi' j hj' hij => ho i (by omega) j (by omega) hij)
    set F := ∑ i ∈ Finset.range n, e i with hF
    have haF : e n * F = 0 := by
      rw [hF, Finset.mul_sum]
      refine Finset.sum_eq_zero fun i hi' => ?_
      have := Finset.mem_range.mp hi'
      exact ho n (by omega) i (by omega) (by omega)
    have hFa : F * e n = 0 := by
      rw [hF, Finset.sum_mul]
      refine Finset.sum_eq_zero fun i hi' => ?_
      have := Finset.mem_range.mp hi'
      exact ho i (by omega) n (by omega) (by omega)
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    refine ⟨?_, ?_⟩
    · calc (F + e n) * (F + e n) = F * F + F * e n + e n * F + e n * e n := by noncomm_ring
        _ = F + e n := by rw [ih1, hFa, haF, hi n (by omega)]; simp
    · rw [finrank_range_add ih1 (hi n (by omega)) hFa haF, ih2]

theorem comm_mono (ρ : G →* (V ≃ₗ[ZMod 2] V)) {M N : Subgroup G} (h : M ≤ N)
    {z : Module.End (ZMod 2) V} (hz : z ∈ comm ρ N) : z ∈ comm ρ M :=
  (mem_comm ρ M z).mpr fun m hm => (mem_comm ρ N z).mp hz m (h hm)

theorem le_centE (ρ : G →* (V ≃ₗ[ZMod 2] V)) (M : Subgroup G) {e : Module.End (ZMod 2) V}
    (he : e ∈ comm ρ M) : M ≤ centE ρ e := fun m hm => (mem_comm ρ M e).mp he m hm

theorem mem_cz_top_of_centE (ρ : G →* (V ≃ₗ[ZMod 2] V)) (M : Subgroup G)
    {e : Module.End (ZMod 2) V} (he : e ∈ cz ρ M) (h : centE ρ e = ⊤) : e ∈ cz ρ ⊤ := by
  obtain ⟨hec, hez⟩ := (mem_cz ρ M e).mp he
  rw [mem_cz]
  refine ⟨(mem_comm ρ ⊤ e).mpr fun g _ => ?_, fun f hf => hez f (comm_mono ρ le_top hf)⟩
  have : g ∈ centE ρ e := by rw [h]; trivial
  exact this

theorem cj_eq_of_mem_centE (ρ : G →* (V ≃ₗ[ZMod 2] V)) {g : G} {f : Module.End (ZMod 2) V}
    (hg : g ∈ centE ρ f) : cj ρ g f = f := by
  have hg' : er ρ g * f = f * er ρ g := hg
  rw [cj_apply, hg', mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]

theorem mem_centE_of_cj_eq (ρ : G →* (V ≃ₗ[ZMod 2] V)) {g : G} {f : Module.End (ZMod 2) V}
    (h : cj ρ g f = f) : g ∈ centE ρ f := by
  show er ρ g * f = f * er ρ g
  rw [cj_apply] at h
  calc er ρ g * f = er ρ g * f * (er ρ g⁻¹ * er ρ g) := by
        rw [← map_mul, inv_mul_cancel, map_one, mul_one]
    _ = (er ρ g * f * er ρ g⁻¹) * er ρ g := by simp only [mul_assoc]
    _ = f * er ρ g := by rw [h]

theorem simple_of_prime_index (ρ : G →* (V ≃ₗ[ZMod 2] V)) (M : Subgroup G) [M.Normal] {q : ℕ}
    (hq : q.Prime) (hMq : M.index = q) (hdim : ¬ q ∣ finrank (ZMod 2) V) (hG : Simple ρ ⊤) :
    Simple ρ M := by
  classical
  intro z₀ hz₀ hz₀i
  by_contra hcon
  obtain ⟨hz0, hz1⟩ : z₀ ≠ 0 ∧ z₀ ≠ 1 := not_or.mp hcon
  have hS : ∃ n, ∃ z ∈ cz ρ M, z * z = z ∧ z ≠ 0 ∧ finrank (ZMod 2) (LinearMap.range z) = n :=
    ⟨_, z₀, hz₀, hz₀i, hz0, rfl⟩
  obtain ⟨e, he, hei, he0, her⟩ := Nat.find_spec hS
  set r := Nat.find hS with hr
  have hmin : ∀ z ∈ cz ρ M, z * z = z → z ≠ 0 → r ≤ finrank (ZMod 2) (LinearMap.range z) :=
    fun z hz hzi hz0' => Nat.find_min' hS ⟨z, hz, hzi, hz0', rfl⟩
  have he1 : e ≠ 1 := by
    intro h1
    have hrV : r = finrank (ZMod 2) V := by
      rw [← her, h1]
      have : LinearMap.range (1 : Module.End (ZMod 2) V) = ⊤ := LinearMap.range_eq_top.mpr
        Function.surjective_id
      rw [this, finrank_top]
    have h2 := hmin z₀ hz₀ hz₀i hz0
    have h3 : finrank (ZMod 2) (LinearMap.range z₀) ≤ finrank (ZMod 2) V := Submodule.finrank_le _
    have h4 : LinearMap.range z₀ = ⊤ := Submodule.eq_top_of_finrank_eq (by omega)
    exact hz1 (eq_one_of_idem_range_top hz₀i h4)
  have hMH : M ≤ centE ρ e := le_centE ρ M ((mem_cz ρ M e).mp he).1
  rcases eq_or_eq_top_of_le M (centE ρ e) hq hMq hMH with hH | hH
  · have hMne : M ≠ ⊤ := fun h => by
      rw [h, Subgroup.index_top] at hMq
      exact hq.ne_one hMq.symm
    obtain ⟨h, hhM⟩ : ∃ h : G, h ∉ M := by
      by_contra hall
      exact hMne (eq_top_iff.mpr fun x _ => by
        by_contra hx
        exact hall ⟨x, hx⟩)
    let E : ℕ → Module.End (ZMod 2) V := fun i => cj ρ (h ^ i) e
    have hEcz : ∀ i, E i ∈ cz ρ M := fun i => cj_mem_cz ρ M _ he
    have hEi : ∀ i, E i * E i = E i := fun i => by
      show cj ρ (h ^ i) e * cj ρ (h ^ i) e = cj ρ (h ^ i) e
      rw [← map_mul, hei]
    have hE0 : ∀ i, E i ≠ 0 := fun i h0 => he0 ((cj ρ (h ^ i)).map_eq_zero_iff.mp h0)
    have hErk : ∀ i, finrank (ZMod 2) (LinearMap.range (E i)) = r := fun i => by
      rw [← her]; exact finrank_range_cj ρ _ e
    have hEne : ∀ i j, i < q → j < q → i ≠ j → E i ≠ E j := by
      intro i j hi hj hij heq
      wlog hlt : i < j generalizing i j
      · exact this j i hj hi hij.symm heq.symm (by omega)
      have h1 : cj ρ (h ^ i) (cj ρ (h ^ (j - i)) e) = cj ρ (h ^ i) e := by
        rw [← cj_mul, ← pow_add, Nat.add_sub_cancel' hlt.le]; exact heq.symm
      have h2 : cj ρ (h ^ (j - i)) e = e := (cj ρ (h ^ i)).injective h1
      have hmem : h ^ (j - i) ∈ centE ρ e := mem_centE_of_cj_eq ρ h2
      rw [hH] at hmem
      have hd := (pow_mem_iff_dvd M hq hMq hhM (j - i)).mp hmem
      exact absurd (Nat.le_of_dvd (by omega) hd) (by omega)
    have hEo : ∀ i < q, ∀ j < q, i ≠ j → E i * E j = 0 := fun i hi j hj hij =>
      orth_of_minimal ρ M (hEcz i) (hEcz j) (hEi i) (hEi j) r (hErk i) (hErk j) hmin
        (hEne i j hi hj hij)
    obtain ⟨hff, hfrk⟩ := sum_idem_rank (e := E) q (fun i _ => hEi i) hEo
    set f := ∑ i ∈ Finset.range q, E i with hf
    have hfcz : f ∈ cz ρ M := Subalgebra.sum_mem _ fun i _ => hEcz i
    have hfne : f ≠ 0 := by
      intro hf0
      have : f * E 0 = E 0 := by
        rw [hf, Finset.sum_mul, Finset.sum_eq_single 0]
        · exact hEi 0
        · intro i hi hi0
          exact hEo i (Finset.mem_range.mp hi) 0 hq.pos hi0
        · intro h0; exact absurd (Finset.mem_range.mpr hq.pos) h0
      rw [hf0, zero_mul] at this
      exact hE0 0 this.symm
    have hEq : E q = E 0 := by
      have hqM : h ^ q ∈ M := (pow_mem_iff_dvd M hq hMq hhM q).mpr dvd_rfl
      show cj ρ (h ^ q) e = cj ρ (h ^ 0) e
      rw [pow_zero, cj_one]
      exact cj_eq_of_mem_centE ρ (hH ▸ hqM)
    have hcjE : ∀ i, cj ρ h (E i) = E (i + 1) := fun i => by
      show cj ρ h (cj ρ (h ^ i) e) = cj ρ (h ^ (i + 1)) e
      rw [← cj_mul, pow_succ']
    have hcjf : cj ρ h f = f := by
      have h1 : cj ρ h f = ∑ i ∈ Finset.range q, E (i + 1) := by
        rw [hf, map_sum]
        exact Finset.sum_congr rfl fun i _ => hcjE i
      rw [h1]
      have h2 := Finset.sum_range_succ E q
      have h3 := Finset.sum_range_succ' E q
      rw [hEq] at h2
      have : (∑ i ∈ Finset.range q, E (i + 1)) + E 0 = (∑ i ∈ Finset.range q, E i) + E 0 := by
        rw [← h3, h2]
      exact add_right_cancel this
    have hfH : centE ρ f = ⊤ := by
      have hMf : M ≤ centE ρ f := le_centE ρ M ((mem_cz ρ M f).mp hfcz).1
      rcases eq_or_eq_top_of_le M (centE ρ f) hq hMq hMf with hf1 | hf1
      · exact absurd (hf1 ▸ mem_centE_of_cj_eq ρ hcjf) hhM
      · exact hf1
    have hf1 : f = 1 := by
      rcases hG f (mem_cz_top_of_centE ρ M hfcz hfH) hff with h0 | h1
      · exact absurd h0 hfne
      · exact h1
    have hV : finrank (ZMod 2) V = q * r := by
      have : LinearMap.range (1 : Module.End (ZMod 2) V) = ⊤ := LinearMap.range_eq_top.mpr
        Function.surjective_id
      have h5 : finrank (ZMod 2) (LinearMap.range f) = finrank (ZMod 2) V := by
        rw [hf1, this, finrank_top]
      rw [← h5, hfrk]
      simp [hErk]
    exact hdim (hV ▸ dvd_mul_right q r)
  · rcases hG e (mem_cz_top_of_centE ρ M he hH) hei with h | h
    · exact he0 h
    · exact he1 h

end Hom

end CFSG.LocalAnalysis.EvenBN.Tits.I21L
