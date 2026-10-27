module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldExcl1Burnside
public import CFSG.LocalAnalysis.OddStandard.ChengHeldExcl1Fuse
public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveGeneral

public section

namespace CFSG.OddStandard.ChengHeld

open Subgroup CFSG.OddStandard.ChengHeldData
open CFSG.OddStandard.ChengHeld.ChartShape (cm_eq_one_iff)

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A} {α : ℕ}

theorem Chart4.not_isConj_q_pi_of_W_derived
    (hα : α ≤ 1) (hα1 : α = 1) (c : Chart4 d α) (h : Hyp G A)
    (hP : chPresOK = true) (hQ : chPropsOK = true) (hS2 : chSec2OK = true)
    (hc : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 4) : ¬ IsConj d.q c.pi := by
  intro hfus
  obtain ⟨g, hgq, hW, -⟩ := c.fuse_in_normalizer hα h hP hQ hS2 hc hfus
  have hS := c.sFacts hα h hP hQ
  have hder := hS.W_derived hα1
  have hWmap : c.W.map (MulAut.conj g⁻¹).toMonoidHom = c.W := by
    ext x
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine (hW _).2 ?_
      have : g * (g⁻¹ * w * g) * g⁻¹ = w := by group
      rw [this]
      exact hw
    · intro hx
      exact ⟨g * x * g⁻¹, (hW x).1 hx, by group⟩
  have hqder : d.q ∈ ⁅c.W, c.W⁆ := by
    rw [hder, c.q_eq]
    exact mem_zpowers _
  have hmapder : (⁅c.W, c.W⁆).map (MulAut.conj g⁻¹).toMonoidHom = ⁅c.W, c.W⁆ := by
    rw [Subgroup.map_commutator, hWmap]
  have hπder : c.pi ∈ ⁅c.W, c.W⁆ := by
    have : c.pi ∈ (⁅c.W, c.W⁆).map (MulAut.conj g⁻¹).toMonoidHom :=
      ⟨d.q, hqder, by simpa [MulAut.conj_apply] using hgq⟩
    rwa [hmapder] at this
  rw [hder, ← c.q_eq] at hπder
  have hqq : d.q * d.q = 1 := by
    rw [← pow_two]; exact orderOf_dvd_iff_pow_eq_one.1 (by simp [d.q_ord])
  rcases CFSG.OddStandard.eq_one_or_eq_of_mem_zpowers_of_mul_self hqq hπder with h1 | h1
  · exact c.pi_ne_one h1
  · exact c.pi_ne_q hα h hP hQ h1

theorem Chart4.excl_field_one_core
    (hα : α ≤ 1) (hα1 : α = 1) (c : Chart4 d α) (h : Hyp G A) (hP : chPresOK = true)
    (hQ : chPropsOK = true) (hS2 : chSec2OK = true)
    (hc : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 4)
    (hk' : ∀ k', (c.rep k').isSome → k' = Kind.field) : False := by
  have hnc := c.not_isConj_q_pi_of_W_derived hα hα1 h hP hQ hS2 hc
  obtain ⟨z, hzX, hzQS, hz2, hzq, hzact⟩ := c.exists_z hα h hP hQ hS2 hc hk' hnc
  obtain ⟨hzπ', hzτ', -, hzt'⟩ := c.field_act_parts hzact
  have hzt'' : cj c.t z = c.t⁻¹ := hzt' (by omega)
  unfold cj at hzπ' hzτ' hzt''
  have hcen := c.t_comm hα h hP hQ
  have fr := c.frame
  obtain ⟨hqX, hqc⟩ := d.q_mem_X h
  have hqcomm : ∀ x ∈ d.X, x * d.q = d.q * x := fun x hx =>
    mem_centralizer_singleton_iff.1 (hqc hx)
  have hπ2 : c.pi * c.pi = 1 := by simpa [pow_two] using fr.pi2
  have hπτ : c.pi * c.tau = c.tau * c.pi := (cm_eq_one_iff.1 fr.pi_tau).eq
  have hπX : c.pi ∈ d.X := d.S_le_X c.mem.1
  have hτX : c.tau ∈ d.X := d.S_le_X c.mem.2.1
  have hzπ : z * c.pi = c.pi * z := by
    calc z * c.pi = z * (z⁻¹ * c.pi * z) := by rw [hzπ']
      _ = c.pi * z := by group
  have hτz : c.tau * z = z * (c.pi * c.tau) := by
    calc c.tau * z = z * (z⁻¹ * c.tau * z) := by group
      _ = z * (c.pi * c.tau) := by rw [hzτ']
  have hτπ' : c.tau⁻¹ * c.pi * c.tau = c.pi := by
    calc c.tau⁻¹ * c.pi * c.tau = c.tau⁻¹ * (c.pi * c.tau) := by group
      _ = c.tau⁻¹ * (c.tau * c.pi) := by rw [hπτ]
      _ = c.pi := by group
  have hB : c.tau⁻¹ * z * c.tau = z * c.pi := by
    calc c.tau⁻¹ * z * c.tau = c.tau⁻¹ * z * (c.pi * c.pi) * c.tau := by rw [hπ2, mul_one]
      _ = c.tau⁻¹ * (z * (c.pi * c.tau)) * (c.tau⁻¹ * c.pi * c.tau) := by group
      _ = c.tau⁻¹ * (c.tau * z) * (c.tau⁻¹ * c.pi * c.tau) := by rw [← hτz]
      _ = z * c.pi := by rw [hτπ']; group
  have hinv : z⁻¹ * c.t⁻¹ * z = c.t := by
    calc z⁻¹ * c.t⁻¹ * z = (z⁻¹ * c.t * z)⁻¹ := by group
      _ = (c.t⁻¹)⁻¹ := by rw [hzt'']
      _ = c.t := inv_inv c.t
  have hA : c.t⁻¹ * z * c.t = z * d.q := by
    calc c.t⁻¹ * z * c.t = z * (z⁻¹ * c.t⁻¹ * z) * c.t := by group
      _ = z * c.t * c.t := by rw [hinv]
      _ = z * d.q := by rw [c.q_eq, pow_two]; group
  have hτq : c.tau⁻¹ * d.q * c.tau = d.q := by
    have := hqcomm c.tau hτX
    calc c.tau⁻¹ * d.q * c.tau = c.tau⁻¹ * (d.q * c.tau) := by group
      _ = c.tau⁻¹ * (c.tau * d.q) := by rw [← this]
      _ = d.q := by group
  have hπq : c.pi * d.q = d.q * c.pi := (hqcomm c.pi hπX)
  have h1 : IsConj z (z * c.pi) := isConj_iff.2 ⟨c.tau⁻¹, by rw [← hB]; group⟩
  have h2 : IsConj z (z * (d.q * c.pi)) := by
    refine isConj_iff.2 ⟨c.tau⁻¹ * c.t⁻¹, ?_⟩
    calc c.tau⁻¹ * c.t⁻¹ * z * (c.tau⁻¹ * c.t⁻¹)⁻¹ = c.tau⁻¹ * (c.t⁻¹ * z * c.t) * c.tau := by
          group
      _ = c.tau⁻¹ * (z * d.q) * c.tau := by rw [hA]
      _ = (c.tau⁻¹ * z * c.tau) * (c.tau⁻¹ * d.q * c.tau) := by group
      _ = (z * c.pi) * d.q := by rw [hB, hτq]
      _ = z * (d.q * c.pi) := by rw [mul_assoc, hπq]
  exact c.false_of_fuse_z hα h hP hQ hc hnc
    (fun a ha haQS b hb hbQS => c.mul_mem_QS_of_kinds hα h hP hQ hk' ha haQS hb hbQS)
    hzX hzQS hzq hzπ h1 h2

theorem Chart4.excl_field_core
    (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A) (hP : chPresOK = true) (hQ : chPropsOK = true)
    (hS2 : chSec2OK = true) (hE : chExcl1OK = true)
    (hc : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 4)
    (hk : c.kinds = {Kind.field}) : False := by
  have hk' : ∀ k', (c.rep k').isSome → k' = Kind.field := by
    intro k' hk'
    have hmem : k' ∈ c.kinds := hk'
    rw [hk] at hmem
    exact hmem
  rcases (by omega : α = 0 ∨ α = 1) with hα0 | hα1
  · have hnc := c.not_isConj_q_pi_of_field_zero hα hα0 h hP hQ hS2 hE hk'
    obtain ⟨z, hzX, hzQS, hz2, hzq, hzact⟩ := c.exists_z hα h hP hQ hS2 hc hk' hnc
    have hzt : cj c.t z = c.t := (c.field_act_parts hzact).2.2.1 hα0
    unfold cj at hzt
    have hcomm : z * c.t = c.t * z := by
      calc z * c.t = z * (z⁻¹ * c.t * z) := by rw [hzt]
        _ = c.t * z := by group
    exact hnc (c.fuse_of_commutes hα h hP hQ hc hzQS hzq hcomm)
  · exact c.excl_field_one_core hα hα1 h hP hQ hS2 hc hk'

end CFSG.OddStandard.ChengHeld
