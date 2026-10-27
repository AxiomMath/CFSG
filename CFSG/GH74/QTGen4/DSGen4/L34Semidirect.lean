module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Tactic.Group

public section

namespace CFSG.GH74.QTGen4.DSGen4.L34

variable {G : Type*} [Group G]

theorem semidirect_aut (N K : Subgroup G) [hNn : N.Normal]
    (hN : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) (hdisj : N ⊓ K = ⊥) (hsup : N ⊔ K = ⊤)
    (δ : K → N)
    (hδ : ∀ k k' : K, (δ (k * k') : G) = (δ k : G) * ((k : G) * (δ k' : G) * (k : G)⁻¹)) :
    ∃ φ : MulAut G, (∀ v : N, φ (v : G) = (v : G)) ∧
      (∀ (v : N) (k : K), φ ((v : G) * (k : G)) = ((v : G) * (δ k : G)) * (k : G)) ∧
      ∀ k : K, φ (k : G) = (δ k : G) * (k : G) := by
  have hfree : ∀ x : G, x ∈ N → x ∈ K → x = 1 := by
    intro x hxN hxK
    have hx : x ∈ N ⊓ K := Subgroup.mem_inf.2 ⟨hxN, hxK⟩
    rw [hdisj, Subgroup.mem_bot] at hx
    exact hx
  have hδ1 : δ 1 = 1 := by
    have h := hδ 1 1
    simp at h
    exact h
  have hbij : Function.Bijective (fun p : N × K => (p.1 : G) * (p.2 : G)) := by
    constructor
    · rintro ⟨v, k⟩ ⟨v', k'⟩ h
      change (v : G) * (k : G) = (v' : G) * (k' : G) at h
      have h1 : (v' : G)⁻¹ * (v : G) = (k' : G) * (k : G)⁻¹ := by
        calc (v' : G)⁻¹ * (v : G) = (v' : G)⁻¹ * ((v : G) * (k : G)) * (k : G)⁻¹ := by group
          _ = (v' : G)⁻¹ * ((v' : G) * (k' : G)) * (k : G)⁻¹ := by rw [h]
          _ = (k' : G) * (k : G)⁻¹ := by group
      have hmem : (k' : G) * (k : G)⁻¹ ∈ N := by
        rw [← h1]
        exact N.mul_mem (N.inv_mem v'.2) v.2
      have h2 : (v' : G)⁻¹ * (v : G) = 1 := by
        rw [h1]
        exact hfree _ hmem (K.mul_mem k'.2 (K.inv_mem k.2))
      have hvv : (v' : G) = (v : G) := inv_mul_eq_one.1 h2
      have hkk : (k : G) = (k' : G) := by
        have h3 : (v : G) * (k : G) = (v : G) * (k' : G) := by rw [h, hvv]
        exact mul_left_cancel h3
      exact Prod.ext (Subtype.ext hvv.symm) (Subtype.ext hkk)
    · intro g
      have hg : g ∈ N ⊔ K := by
        rw [hsup]
        exact Subgroup.mem_top g
      obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_left.1 hg
      exact ⟨(⟨y, hy⟩, ⟨z, hz⟩), hyz⟩
  obtain ⟨E, hE⟩ : ∃ E : N × K ≃ G, ∀ p : N × K, E p = (p.1 : G) * (p.2 : G) :=
    ⟨Equiv.ofBijective _ hbij, fun _ => rfl⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : G → G, ∀ g : G,
      Φ g = ((E.symm g).1 : G) * (δ (E.symm g).2 : G) * ((E.symm g).2 : G) :=
    ⟨fun g => ((E.symm g).1 : G) * (δ (E.symm g).2 : G) * ((E.symm g).2 : G), fun _ => rfl⟩
  have hdec : ∀ x : G, x = ((E.symm x).1 : G) * ((E.symm x).2 : G) := by
    intro x
    have h := E.apply_symm_apply x
    rw [hE] at h
    exact h.symm
  have alg : ∀ p1 p2 q1 q2 e1 e2 : G, (p2 * q1 * p2⁻¹) * e1 = e1 * (p2 * q1 * p2⁻¹) →
      p1 * (p2 * q1 * p2⁻¹) * (e1 * (p2 * e2 * p2⁻¹)) * (p2 * q2) =
        p1 * e1 * p2 * (q1 * e2 * q2) := by
    intro p1 p2 q1 q2 e1 e2 hc
    calc p1 * (p2 * q1 * p2⁻¹) * (e1 * (p2 * e2 * p2⁻¹)) * (p2 * q2)
        = p1 * ((p2 * q1 * p2⁻¹) * e1) * (p2 * e2 * q2) := by group
      _ = p1 * (e1 * (p2 * q1 * p2⁻¹)) * (p2 * e2 * q2) := by rw [hc]
      _ = p1 * e1 * p2 * (q1 * e2 * q2) := by group
  have hmul : ∀ x y : G, Φ (x * y) = Φ x * Φ y := by
    intro x y
    obtain ⟨p, hp⟩ : ∃ p : N × K, E.symm x = p := ⟨_, rfl⟩
    obtain ⟨q, hq⟩ : ∃ q : N × K, E.symm y = q := ⟨_, rfl⟩
    have hx : x = (p.1 : G) * (p.2 : G) := by
      rw [← hp]
      exact hdec x
    have hy : y = (q.1 : G) * (q.2 : G) := by
      rw [← hq]
      exact hdec y
    have hΦx : Φ x = ((p.1 : G) * (δ p.2 : G)) * (p.2 : G) := by
      rw [hΦ, hp]
    have hΦy : Φ y = ((q.1 : G) * (δ q.2 : G)) * (q.2 : G) := by
      rw [hΦ, hq]
    have hc : (p.2 : G) * (q.1 : G) * (p.2 : G)⁻¹ ∈ N := hNn.conj_mem _ q.1.2 _
    have hr : E.symm (x * y) =
        (⟨(p.1 : G) * ((p.2 : G) * (q.1 : G) * (p.2 : G)⁻¹), N.mul_mem p.1.2 hc⟩, p.2 * q.2) := by
      rw [Equiv.symm_apply_eq, hE, hx, hy]
      simp only [Subgroup.coe_mul]
      group
    have hcomm : ((p.2 : G) * (q.1 : G) * (p.2 : G)⁻¹) * (δ p.2 : G) =
        (δ p.2 : G) * ((p.2 : G) * (q.1 : G) * (p.2 : G)⁻¹) :=
      hN _ hc _ (δ p.2).2
    calc Φ (x * y) = ((p.1 : G) * ((p.2 : G) * (q.1 : G) * (p.2 : G)⁻¹)) * (δ (p.2 * q.2) : G) *
          ((p.2 : G) * (q.2 : G)) := by
          rw [hΦ, hr] <;> rfl
      _ = ((p.1 : G) * ((p.2 : G) * (q.1 : G) * (p.2 : G)⁻¹)) *
          ((δ p.2 : G) * ((p.2 : G) * (δ q.2 : G) * (p.2 : G)⁻¹)) * ((p.2 : G) * (q.2 : G)) := by
          rw [hδ p.2 q.2]
      _ = Φ x * Φ y := by
          rw [hΦx, hΦy]
          exact alg _ _ _ _ _ _ hcomm
  have hker : ∀ x : G, Φ x = 1 → x = 1 := by
    intro x hx
    obtain ⟨p, hp⟩ : ∃ p : N × K, E.symm x = p := ⟨_, rfl⟩
    have hx' : x = (p.1 : G) * (p.2 : G) := by
      rw [← hp]
      exact hdec x
    have hΦx : Φ x = ((p.1 : G) * (δ p.2 : G)) * (p.2 : G) := by
      rw [hΦ, hp]
    have h1 : ((p.1 : G) * (δ p.2 : G)) * (p.2 : G) = 1 := hΦx.symm.trans hx
    have hp2N : (p.2 : G) ∈ N := by
      rw [eq_inv_of_mul_eq_one_right h1]
      exact N.inv_mem (N.mul_mem p.1.2 (δ p.2).2)
    have hp2 : (p.2 : G) = 1 := hfree _ hp2N p.2.2
    have hp2' : p.2 = 1 := Subtype.ext hp2
    have hδp2 : δ p.2 = 1 := by
      rw [hp2', hδ1]
    have hp1 : (p.1 : G) = 1 := by
      rw [hδp2, hp2] at h1
      simpa using h1
    rw [hx', hp1, hp2, one_mul]
  have hinj : Function.Injective Φ :=
    (injective_iff_map_eq_one (MonoidHom.mk' Φ hmul)).2 hker
  have hsurj : Function.Surjective Φ := by
    intro g
    obtain ⟨p, hp⟩ : ∃ p : N × K, E.symm g = p := ⟨_, rfl⟩
    have hgp : g = (p.1 : G) * (p.2 : G) := by
      rw [← hp]
      exact hdec g
    refine ⟨E (p.1 * (δ p.2)⁻¹, p.2), ?_⟩
    simp only [hΦ, Equiv.symm_apply_apply]
    rw [hgp, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hbijΦ : Function.Bijective Φ := ⟨hinj, hsurj⟩
  refine ⟨MulEquiv.ofBijective (⟨Φ, hmul⟩ : G →ₙ* G) hbijΦ, ?_, ?_, ?_⟩
  · intro v
    change Φ (v : G) = (v : G)
    have hv : E.symm (v : G) = (v, 1) := E.symm_apply_eq.2 (by simp [hE])
    simp [hΦ, hv, hδ1]
  · intro v k
    change Φ ((v : G) * (k : G)) = ((v : G) * (δ k : G)) * (k : G)
    have hvk : E.symm ((v : G) * (k : G)) = (v, k) := E.symm_apply_eq.2 (hE (v, k)).symm
    simp only [hΦ, hvk]
  · intro k
    change Φ (k : G) = (δ k : G) * (k : G)
    have hk : E.symm (k : G) = (1, k) := E.symm_apply_eq.2 (by simp [hE])
    simp [hΦ, hk]

end CFSG.GH74.QTGen4.DSGen4.L34

end
