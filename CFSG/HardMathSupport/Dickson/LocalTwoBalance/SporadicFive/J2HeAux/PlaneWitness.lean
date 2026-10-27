module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporFiveKit
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.J2HeAux

theorem gLAPPrimeCoreOf_centralizer_conj {M : Type*} [Group M] [Finite M] {R : Subgroup M}
    (p : ℕ) {k : M} (hk : k ∈ R) {d : M}
    (h : CFSG.Open.GLAPPrimeCoreOf p (Subgroup.centralizer ({d} : Set M) ⊓ R) = ⊥) :
    CFSG.Open.GLAPPrimeCoreOf p (Subgroup.centralizer ({k * d * k⁻¹} : Set M) ⊓ R) = ⊥ := by
  have hk1 : ∀ q ∈ R, k * q * k⁻¹ ∈ R := fun q hq => R.mul_mem (R.mul_mem hk hq) (R.inv_mem hk)
  have hk2 : ∀ q ∈ R, k⁻¹ * q * k ∈ R := fun q hq => R.mul_mem (R.mul_mem (R.inv_mem hk) hq) hk
  rw [← CFSG.HardMathSupport.Solomon.Coordinator.map_conj_centralizer_inf hk1 hk2 d,
    ← CFSG.HardMathSupport.Timmesfeld.Coordinator.map_glaPPrimeCoreOf_of_injective p
      (MulAut.conj k).toMonoidHom (MulAut.conj k).injective, h, Subgroup.map_bot]

theorem exists_plane_witness_sq {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (Q : Sylow p G) (hQ : Nat.card Q = p ^ 2) {d₀ : G} (hd₀Q : d₀ ∈ Q) (hd₀ : d₀ ≠ 1)
    (Φ : G → Prop) (hΦ : ∀ g d, Φ d → Φ (g * d * g⁻¹)) (hΦ₀ : Φ d₀)
    (E : Subgroup G) (hE : CFSG.Open.IsElemAbelian p E) (hEc : Nat.card E = p ^ 2) :
    ∃ d ∈ E, d ≠ 1 ∧ Φ d := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P', hP'⟩ := hE.isPGroup.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G Q P'
  have hconj : ∀ x ∈ E, h⁻¹ * x * h ∈ (Q : Subgroup G) := fun x hx => by
    have hxP' : x ∈ (P' : Subgroup G) := hP' hx
    have : (P' : Subgroup G) = (h • Q : Sylow p G) := by rw [hh]
    rw [this, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxP'
    exact hxP'
  set E₀ : Subgroup G := E.map (MulAut.conj h⁻¹).toMonoidHom with hE₀
  have hE₀Q : E₀ ≤ (Q : Subgroup G) := by
    rintro _ ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using hconj x hx
  have hE₀c : Nat.card E₀ = p ^ 2 := by
    rw [hE₀, Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective, hEc]
  have hEQ : E₀ = (Q : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge hE₀Q (by rw [hE₀c]; exact hQ.le)
  have hmem : d₀ ∈ E₀ := by
    rw [hEQ]
    exact hd₀Q
  obtain ⟨x, hxE, hx⟩ := Subgroup.mem_map.1 hmem
  have hx' : h⁻¹ * x * h = d₀ := by simpa [MulAut.conj_apply] using hx
  refine ⟨x, hxE, fun h1 => hd₀ ?_, ?_⟩
  · rw [← hx', h1, mul_one, inv_mul_cancel]
  · have hxeq : x = h * d₀ * h⁻¹ := by
      rw [← hx']
      group
    rw [hxeq]
    exact hΦ h d₀ hΦ₀

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.J2HeAux
