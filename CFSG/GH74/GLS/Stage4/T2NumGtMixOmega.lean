module

public import CFSG.GH74.GLS.Stage4.T2NumGtMixRankK
public import CFSG.GH74.GLS.Stage4.T6X.T6HInv

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.GLS.Stage4.Rest.T2 CFSG.GH74.GLS.Stage4.Rest.T6X CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mx_omega_exists {N : T2N3 G} {u : G} {p : ℕ} (h : T6CtxW N u p) :
    ∃ Ω : Subgroup G, ∀ r, r ∈ Ω ↔ r ∈ R₂ N p ∧ r ^ p ∈ N.X₂ := by
  have hXc : ∀ x ∈ N.X₂, ∀ r ∈ R₂ N p, x * r = r * x := by
    intro x hx r hr
    have := R₂_cent h r hr x hx
    calc x * r = (r * x * r⁻¹) * r := by rw [this]
      _ = r * x := by group
  have hcomm := (R₂_inv_comm h).2
  refine ⟨{ carrier := {r | r ∈ R₂ N p ∧ r ^ p ∈ N.X₂}
            mul_mem' := ?_
            one_mem' := ⟨(R₂ N p).one_mem, by simp⟩
            inv_mem' := ?_ }, fun r => Iff.rfl⟩
  · rintro a b ⟨haR, hap⟩ ⟨hbR, hbp⟩
    obtain ⟨x, hx, hxe⟩ := CFSG.GH74.GLS.Stage4.Rest.T6.t6_pow_mul hXc hcomm haR hbR p
    refine ⟨(R₂ N p).mul_mem haR hbR, ?_⟩
    rw [hxe]
    exact N.X₂.mul_mem (N.X₂.mul_mem hap hbp) hx
  · rintro a ⟨haR, hap⟩
    refine ⟨(R₂ N p).inv_mem haR, ?_⟩
    rw [inv_pow]
    exact N.X₂.inv_mem hap

omit [Finite G] in
theorem mx_omega_inv {N : T2N3 G} {p : ℕ} {Ω : Subgroup G}
    (hΩ : ∀ r, r ∈ Ω ↔ r ∈ R₂ N p ∧ r ^ p ∈ N.X₂) {g : G} (hg : g ∈ M₂ N) {r : G} (hr : r ∈ Ω) :
    g * r * g⁻¹ ∈ Ω := by
  obtain ⟨hrR, hrp⟩ := (hΩ r).1 hr
  refine (hΩ _).2 ⟨R₂_norm N p hg hrR, ?_⟩
  have : (g * r * g⁻¹) ^ p = g * r ^ p * g⁻¹ := by simp
  rw [this]
  exact (Subgroup.mem_normalizer_iff.1 hg _).1 hrp

theorem mx_Omega_u_exp {N : T2N3 G} {u : G} {p : ℕ} (h : T6CtxW N u p) {Ω : Subgroup G}
    (hΩ : ∀ r, r ∈ Ω ↔ r ∈ R₂ N p ∧ r ^ p ∈ N.X₂) {r : G} (hr : r ∈ Ω ⊓ Subgroup.centralizer {u}) :
    r ^ p = 1 := by
  obtain ⟨hrΩ, hru⟩ := hr
  have hrp : r ^ p ∈ N.X₂ := ((hΩ r).1 hrΩ).2
  have hc : r * u = u * r := Subgroup.mem_centralizer_singleton_iff.1 hru
  have hcp : r ^ p * u = u * r ^ p := by
    have := (Commute.pow_left (a := r) (b := u) hc p).eq
    exact this
  exact X₂_u_fix h hrp hcp

theorem mx_Omega_u_card_le {N : T2N3 G} {u : G} {p n : ℕ} (h : T6CtxW N u p) (hp : p.Prime) (hp2 : p ≠ 2)
    {Ω : Subgroup G} (hΩ : ∀ r, r ∈ Ω ↔ r ∈ R₂ N p ∧ r ^ p ∈ N.X₂)
    {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁] [Finite F₂]
    (e₁ : ↥N.K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F₁)
    (e₂ : ↥N.K₂ ≃* Matrix.SpecialLinearGroup (Fin 2) F₂) (hodd₁ : Odd (Nat.card F₁))
    (h₂ : Nat.card F₂ = p ^ n) (h₁ : ¬ p ∣ Nat.card F₁) :
    Nat.card ↥(Ω ⊓ Subgroup.centralizer {u}) ≤ p ^ n * Nat.gcd p (Nat.card ↥N.K₁) := by
  set Ωu : Subgroup G := Ω ⊓ Subgroup.centralizer {u} with hΩu
  have hΩuR : ∀ r ∈ Ωu, r ∈ RA N p u := fun r hr => ⟨((hΩ r).1 hr.1).1, hr.2⟩
  set A : Subgroup G := Ωu.map (MulAut.conj N.a).toMonoidHom with hA
  have hAK : A ≤ N.K₁ ⊔ N.K₂ := by
    rintro _ ⟨r, hr, rfl⟩
    exact RA_conj_K h (hΩuR r hr)
  have hΩup : IsPGroup p ↥Ωu := (R₂_pGroup N hp).to_le (fun r hr => ((hΩ r).1 hr.1).1)
  have hAp : IsPGroup p ↥A := hΩup.map _
  have hAexp : ∀ x ∈ A, x ^ p = 1 := by
    rintro _ ⟨r, hr, rfl⟩
    have h1 := mx_Omega_u_exp h hΩ hr
    show (N.a * r * N.a⁻¹) ^ p = 1
    rw [conj_pow, h1, mul_one, mul_inv_cancel]
  have hcard := rank_pSubgroup_K_gcd hp hp2 e₁ e₂ hodd₁ h₂ h₁ h.sec5.loc.K_comm hAK hAp hAexp
  rwa [hA, Subgroup.card_map_of_injective (MulAut.conj N.a).injective] at hcard

omit [Finite G] in
theorem mx_sec_image {Ω X R : Subgroup G} {V : Type} [AddCommGroup V]
    (π : ↥Ω → V) (hπ0 : ∀ a, π a = 0 ↔ (a : G) ∈ X) (hπadd : ∀ a a', π (a * a') = π a + π a')
    (hXR : X ≤ R) (hRΩ : R ≤ Ω) :
    ∃ E : AddSubgroup V, (∀ r : ↥Ω, (r : G) ∈ R → π r ∈ E) ∧
      (∀ v ∈ E, ∃ r : ↥Ω, (r : G) ∈ R ∧ π r = v) ∧ Nat.card ↥E * Nat.card ↥X = Nat.card ↥R := by
  classical
  let φ : Additive ↥R →+ V :=
    AddMonoidHom.mk' (fun r => π ⟨r.toMul.1, hRΩ r.toMul.2⟩)
      (fun a b => hπadd ⟨a.toMul.1, hRΩ a.toMul.2⟩ ⟨b.toMul.1, hRΩ b.toMul.2⟩)
  have hker : Nat.card ↥φ.ker = Nat.card ↥X := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.toMul.1, (hπ0 _).1 x.2⟩
        invFun := fun y => ⟨Additive.ofMul ⟨y.1, hXR y.2⟩, (hπ0 _).2 y.2⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  have h1 := AddSubgroup.card_ker_mul_card_range φ
  have h2 : Nat.card (Additive ↥R) = Nat.card ↥R := Nat.card_congr Additive.toMul
  refine ⟨φ.range, ?_, ?_, ?_⟩
  · intro r hr
    exact ⟨Additive.ofMul ⟨r.1, hr⟩, rfl⟩
  · rintro v ⟨x, rfl⟩
    exact ⟨⟨x.toMul.1, hRΩ x.toMul.2⟩, x.toMul.2, rfl⟩
  · rw [← h2, ← h1, hker, mul_comm]

end CFSG.GH74.GLS.Stage4.Rest
