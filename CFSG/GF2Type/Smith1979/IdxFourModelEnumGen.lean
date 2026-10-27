module

public import CFSG.GF2Type.Smith1979.GammaU.Enum

public section

namespace CFSG.GF2Type.Smith1979.IdxFour

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.GammaU.Enum

theorem card_of_codes {P : V12 → Prop} {L : List ℕ} (hL : L.Nodup) (hlt : ∀ n ∈ L, n < 4096)
    (h : ∀ y, P y ↔ codeOf y ∈ L) : Nat.card {y : V12 // P y} = L.length := by
  let f : {y : V12 // P y} → ↥L.toFinset := fun y => ⟨codeOf y.1, List.mem_toFinset.2 ((h _).1 y.2)⟩
  have hinj : Function.Injective f := fun a b hab => Subtype.ext (by
    have := congrArg (fun c : ↥L.toFinset => vecOf c.1) hab
    simpa [f, vecOf_codeOf] using this)
  have hsurj : Function.Surjective f := fun ⟨n, hn⟩ => by
    have hn' := List.mem_toFinset.1 hn
    refine ⟨⟨vecOf n, (h _).2 (by rw [codeOf_vecOf (hlt n hn')]; exact hn')⟩, Subtype.ext ?_⟩
    simp [f, codeOf_vecOf (hlt n hn')]
  rw [Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩), Nat.card_eq_fintype_card,
    Fintype.card_coe, List.card_toFinset, hL.dedup]

theorem conj_mem_of_gen {gsN gsH : List (Array ℕ)} (hN : GensOK gsN) {g : Array ℕ}
    (hg : g ∈ gsN) (h : ∀ e ∈ gsH, Rep (genGrp gsH) (mulR g (mulR e (invR g)))) :
    ∀ x ∈ genGrp gsH, eqvOf g (invR g) (hN g hg).2.2.1 (hN g hg).2.2.2 * x *
      (eqvOf g (invR g) (hN g hg).2.2.1 (hN g hg).2.2.2)⁻¹ ∈ genGrp gsH := by
  intro x hx
  set G := eqvOf g (invR g) (hN g hg).2.2.1 (hN g hg).2.2.2 with hG
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨r, hr, hyr⟩ := hy
    obtain ⟨-, U, hU, hUx⟩ := h r hr
    have : G * y * G⁻¹ = U := LinearEquiv.ext fun v => by
      rw [hUx v]
      simp only [LinearEquiv.mul_apply, hG, eqvOf_apply, eqvOf_inv_apply, hyr, linOfRows_mulR]
    rw [this]
    exact hU
  | one => simpa using one_mem _
  | mul y z _ _ hy hz =>
    have : G * (y * z) * G⁻¹ = (G * y * G⁻¹) * (G * z * G⁻¹) := by group
    rw [this]
    exact mul_mem hy hz
  | inv y _ hy =>
    have : G * y⁻¹ * G⁻¹ = (G * y * G⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem hy

theorem conj_mem_of_gens {gsN gsH : List (Array ℕ)} (hN : GensOK gsN)
    (h : ∀ g ∈ gsN, ∀ e ∈ gsH, Rep (genGrp gsH) (mulR g (mulR e (invR g)))) :
    ∀ n ∈ genGrp gsN, ∀ x ∈ genGrp gsH, n * x * n⁻¹ ∈ genGrp gsH := by
  intro n hn
  have hn' : n ∈ Submonoid.closure (GenSet gsN) := by
    rw [← Subgroup.closure_toSubmonoid_of_finite]
    exact hn
  have key : ∀ x : V12 ≃ₗ[ZMod 2] V12, x ∈ genGrp gsH → n * x * n⁻¹ ∈ genGrp gsH := by
    refine Submonoid.closure_induction_left (s := GenSet gsN)
      (motive := fun (n : V12 ≃ₗ[ZMod 2] V12) _ => ∀ x : V12 ≃ₗ[ZMod 2] V12, x ∈ genGrp gsH →
        n * x * n⁻¹ ∈ genGrp gsH) ?_ ?_ hn'
    · intro x hx
      simpa using hx
    · rintro s ⟨r, hr, hs⟩ n' _ ih x hx
      have hs' : s = eqvOf r (invR r) (hN r hr).2.2.1 (hN r hr).2.2.2 :=
        LinearEquiv.ext fun v => hs v
      have e : s * n' * x * (s * n')⁻¹ = s * (n' * x * n'⁻¹) * s⁻¹ := by group
      rw [e, hs']
      exact conj_mem_of_gen hN hr (fun e he => h r hr e he) _ (ih x hx)
  exact fun x hx => key x hx

end CFSG.GF2Type.Smith1979.IdxFour
