module

public import CFSG.LocalAnalysis.OddStandard.AltStdBalJ
public import CFSG.LocalAnalysis.OddStandard.AltStdSecWreathConfig

public section

namespace CFSG.OddStandard.AltStdSec.Wreath

open Subgroup CFSG.OddStandard.AltStdBal

variable {G : Type} [Group G]

theorem mem_commutator_of_sq_eq_one {K : Subgroup G} {n : ℕ} (e : K ≃* alternatingGroup (Fin n))
    (hn : 8 ≤ n) {a : G} (ha : a ∈ K) (ha2 : a * a = 1) {M : Subgroup G}
    (hM : ∀ c ∈ K, c * a = a * c → c ∈ M) : a ∈ ⁅M, M⁆ := by
  classical
  by_cases ha1 : a = 1
  · rw [ha1]
    exact one_mem _
  have hord : orderOf a = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [sq]; exact ha2) ha1
  have ha2' : orderOf (e ⟨a, ha⟩ : alternatingGroup (Fin n)) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hord]
  have hJ := mem_commutator_centralizer_of_involution (α := Fin n) (by simpa using hn) ha2'
  let f : alternatingGroup (Fin n) →* G := K.subtype.comp e.symm.toMonoidHom
  have h1 := Subgroup.mem_map_of_mem f hJ
  rw [Subgroup.map_commutator] at h1
  have hle : (centralizer ({e ⟨a, ha⟩} : Set (alternatingGroup (Fin n)))).map f ≤ M := by
    rintro _ ⟨c', hc', rfl⟩
    apply hM
    · exact (e.symm c').2
    · have h2 := mem_centralizer_singleton_iff.1 hc'
      have h3 := congrArg e.symm h2
      rw [map_mul, map_mul, MulEquiv.symm_apply_apply] at h3
      exact congrArg Subtype.val h3
  have := Subgroup.commutator_mono hle hle h1
  simpa [f] using this

theorem WConfig.J_of_mem_prodSub {H : Subgroup G} {z : G} (c : WConfig H z) {n : ℕ}
    (e : H ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) {T₁ : Subgroup G} (hT : T₁ ≤ H) {x : G}
    (hx : x ∈ prodSub c T₁ hT) (hx2 : x * x = 1) : J x := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  have hab : a * a = 1 ∧ b * b = 1 := by
    have h1 : Phi z (a * a) (b * b) = 1 := by
      rw [← c.Phi_mul (hT ha) (hT hb)]
      exact hx2
    exact c.Phi_eq_one (mul_mem (hT ha) (hT ha)) (mul_mem (hT hb) (hT hb)) h1
  unfold J
  set M := centralizer ({Phi z a b} : Set G) with hM
  have h1 : a ∈ ⁅M, M⁆ := by
    refine mem_commutator_of_sq_eq_one e hn (hT ha) hab.1 (fun c' hc' hca => ?_)
    rw [hM, mem_centralizer_singleton_iff]
    unfold Phi
    have := c.comm c' hc' b (hT hb)
    calc c' * (a * (z * b * z⁻¹)) = (c' * a) * (z * b * z⁻¹) := by group
      _ = (a * c') * (z * b * z⁻¹) := by rw [hca]
      _ = a * (c' * (z * b * z⁻¹)) := by group
      _ = a * ((z * b * z⁻¹) * c') := by rw [this]
      _ = (a * (z * b * z⁻¹)) * c' := by group
  have h2 : z * b * z⁻¹ ∈ ⁅M, M⁆ := by
    let K : Subgroup G := H.map (MulAut.conj z).toMonoidHom
    let e' : K ≃* alternatingGroup (Fin n) :=
      (Subgroup.equivMapOfInjective H (MulAut.conj z).toMonoidHom
        (MulAut.conj z).injective).symm.trans e
    have hbK : z * b * z⁻¹ ∈ K := ⟨b, hT hb, by simp [MulAut.conj_apply]⟩
    have hsq : (z * b * z⁻¹) * (z * b * z⁻¹) = 1 := by
      calc (z * b * z⁻¹) * (z * b * z⁻¹) = z * (b * b) * z⁻¹ := by group
        _ = 1 := by rw [hab.2]; group
    refine mem_commutator_of_sq_eq_one e' hn hbK hsq (fun c' hc' hcb => ?_)
    obtain ⟨c₀, hc₀, rfl⟩ := hc'
    have hc₀' : (MulAut.conj z).toMonoidHom c₀ = z * c₀ * z⁻¹ := by simp [MulAut.conj_apply]
    rw [hc₀'] at hcb ⊢
    rw [hM, mem_centralizer_singleton_iff]
    unfold Phi
    have h3 := c.comm a (hT ha) c₀ hc₀
    calc (z * c₀ * z⁻¹) * (a * (z * b * z⁻¹)) = ((z * c₀ * z⁻¹) * a) * (z * b * z⁻¹) := by group
      _ = (a * (z * c₀ * z⁻¹)) * (z * b * z⁻¹) := by rw [h3]
      _ = a * ((z * c₀ * z⁻¹) * (z * b * z⁻¹)) := by group
      _ = a * ((z * b * z⁻¹) * (z * c₀ * z⁻¹)) := by rw [hcb]
      _ = (a * (z * b * z⁻¹)) * (z * c₀ * z⁻¹) := by group
  exact mul_mem h1 h2

end CFSG.OddStandard.AltStdSec.Wreath
