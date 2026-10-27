module

public import CFSG.LargeExtraspecial.S3Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith

namespace Sm77

section Index

variable {G : Type*} [Group G]

theorem conj_eq_self_of_commute {t x : G} (h : t * x = x * t) : t * x * t⁻¹ = x := by
  rw [h]
  group

theorem inv_conj_eq_self_of_commute {t x : G} (h : t * x = x * t) : t⁻¹ * x * t = x := by
  calc t⁻¹ * x * t = t⁻¹ * (x * t) := by group
    _ = t⁻¹ * (t * x) := by rw [h]
    _ = x := by group

theorem conj_mem_of_cover {F X : Subgroup G} {c : G} (hXF : X ≤ F) (hcF : c ∈ F)
    (hcov : ∀ f ∈ F, f ∈ X ∨ c⁻¹ * f ∈ X) (hcX : c ∉ X) {x : G} (hx : x ∈ X) :
    c * x * c⁻¹ ∈ X := by
  rcases hcov _ (F.mul_mem (F.mul_mem hcF (hXF hx)) (F.inv_mem hcF)) with h | h
  · exact h
  · exfalso
    apply hcX
    have h' : c⁻¹ = x⁻¹ * (c⁻¹ * (c * x * c⁻¹)) := by group
    have h'' : c⁻¹ ∈ X := by
      rw [h']
      exact X.mul_mem (X.inv_mem hx) h
    simpa using X.inv_mem h''

theorem cover_conj_spec {F X : Subgroup G} {c t : G} (hXF : X ≤ F) (hcF : c ∈ F)
    (hcov : ∀ f ∈ F, f ∈ X ∨ c⁻¹ * f ∈ X) (hcX : c ∉ X) (htF : ∀ f ∈ F, t * f * t⁻¹ ∈ F)
    (htX : ∀ x ∈ X, t * x = x * t) :
    c⁻¹ * (t * c * t⁻¹) ∈ X ∧
      ∀ x ∈ X, c⁻¹ * (t * c * t⁻¹) * x = x * (c⁻¹ * (t * c * t⁻¹)) := by
  have hmem : c⁻¹ * (t * c * t⁻¹) ∈ X := by
    rcases hcov _ (htF c hcF) with h | h
    · exfalso
      apply hcX
      have e : c = t⁻¹ * (t * c * t⁻¹) * t := by group
      rw [e, inv_conj_eq_self_of_commute (htX _ h)]
      exact h
    · exact h
  refine ⟨hmem, fun x hx => ?_⟩
  have hcx := conj_mem_of_cover hXF hcF hcov hcX hx
  have e1 : t * (c * x * c⁻¹) * t⁻¹ = c * x * c⁻¹ :=
    conj_eq_self_of_commute (htX _ hcx)
  have e2 : t * (c * x * c⁻¹) * t⁻¹ =
      t * c * t⁻¹ * (t * x * t⁻¹) * (t * c * t⁻¹)⁻¹ := by group
  rw [conj_eq_self_of_commute (htX x hx)] at e2
  rw [e2] at e1
  calc c⁻¹ * (t * c * t⁻¹) * x
      = c⁻¹ * (t * c * t⁻¹ * x * (t * c * t⁻¹)⁻¹) * (t * c * t⁻¹) := by group
    _ = c⁻¹ * (c * x * c⁻¹) * (t * c * t⁻¹) := by rw [e1]
    _ = x * (c⁻¹ * (t * c * t⁻¹)) := by group

theorem conj_mul_comm_of_fix {F X : Subgroup G} {c t₁ t₂ : G} (hXF : X ≤ F) (hcF : c ∈ F)
    (hcov : ∀ f ∈ F, f ∈ X ∨ c⁻¹ * f ∈ X)
    (h₁F : ∀ f ∈ F, t₁ * f * t₁⁻¹ ∈ F) (h₂F : ∀ f ∈ F, t₂ * f * t₂⁻¹ ∈ F)
    (h₁X : ∀ x ∈ X, t₁ * x = x * t₁) (h₂X : ∀ x ∈ X, t₂ * x = x * t₂) {f : G} (hf : f ∈ F) :
    t₁ * t₂ * f * (t₁ * t₂)⁻¹ = t₂ * t₁ * f * (t₂ * t₁)⁻¹ := by
  have key : ∀ y ∈ X, t₁ * t₂ * y * (t₁ * t₂)⁻¹ = t₂ * t₁ * y * (t₂ * t₁)⁻¹ := by
    intro y hy
    calc t₁ * t₂ * y * (t₁ * t₂)⁻¹ = t₁ * (t₂ * y * t₂⁻¹) * t₁⁻¹ := by group
      _ = y := by rw [conj_eq_self_of_commute (h₂X y hy), conj_eq_self_of_commute (h₁X y hy)]
      _ = t₂ * (t₁ * y * t₁⁻¹) * t₂⁻¹ := by
        rw [conj_eq_self_of_commute (h₁X y hy), conj_eq_self_of_commute (h₂X y hy)]
      _ = t₂ * t₁ * y * (t₂ * t₁)⁻¹ := by group
  by_cases hcX : c ∈ X
  · rcases hcov f hf with h | h
    · exact key f h
    · have : f ∈ X := by simpa using X.mul_mem hcX h
      exact key f this
  rcases hcov f hf with hfX | hfX
  · exact key f hfX
  obtain ⟨hh₁, hc₁⟩ := cover_conj_spec hXF hcF hcov hcX h₁F h₁X
  obtain ⟨hh₂, -⟩ := cover_conj_spec hXF hcF hcov hcX h₂F h₂X
  set h₁ := c⁻¹ * (t₁ * c * t₁⁻¹) with hh₁def
  set h₂ := c⁻¹ * (t₂ * c * t₂⁻¹) with hh₂def
  set y := c⁻¹ * f with hy
  have hf' : f = c * y := by rw [hy]; group
  have e₁ : t₁ * c * t₁⁻¹ = c * h₁ := by rw [hh₁def]; group
  have e₂ : t₂ * c * t₂⁻¹ = c * h₂ := by rw [hh₂def]; group
  have hy₁ := conj_eq_self_of_commute (h₁X y hfX)
  have hy₂ := conj_eq_self_of_commute (h₂X y hfX)
  have hh₂₁ := conj_eq_self_of_commute (h₁X h₂ hh₂)
  have hh₁₂ := conj_eq_self_of_commute (h₂X h₁ hh₁)
  have hcomm : h₁ * h₂ = h₂ * h₁ := hc₁ h₂ hh₂
  calc t₁ * t₂ * f * (t₁ * t₂)⁻¹
      = t₁ * (t₂ * c * t₂⁻¹) * t₁⁻¹ * (t₁ * (t₂ * y * t₂⁻¹) * t₁⁻¹) := by rw [hf']; group
    _ = t₁ * c * t₁⁻¹ * (t₁ * h₂ * t₁⁻¹) * (t₁ * y * t₁⁻¹) := by rw [e₂, hy₂]; group
    _ = c * (h₁ * h₂) * y := by rw [e₁, hh₂₁, hy₁]; group
    _ = c * (h₂ * h₁) * y := by rw [hcomm]
    _ = t₂ * c * t₂⁻¹ * (t₂ * h₁ * t₂⁻¹) * (t₂ * y * t₂⁻¹) := by rw [e₂, hh₁₂, hy₂]; group
    _ = t₂ * (t₁ * c * t₁⁻¹) * t₂⁻¹ * (t₂ * (t₁ * y * t₁⁻¹) * t₂⁻¹) := by rw [e₁, hy₁]; group
    _ = t₂ * t₁ * f * (t₂ * t₁)⁻¹ := by rw [hf']; group

theorem conj_commutator_eq_of_fix [Finite G] {F X : Subgroup G} {c t₁ t₂ : G} (hXF : X ≤ F)
    (hcF : c ∈ F) (hcov : ∀ f ∈ F, f ∈ X ∨ c⁻¹ * f ∈ X)
    (h₁ : t₁ ∈ normalizer (F : Set G)) (h₂ : t₂ ∈ normalizer (F : Set G))
    (h₁X : ∀ x ∈ X, t₁ * x = x * t₁) (h₂X : ∀ x ∈ X, t₂ * x = x * t₂) {f : G} (hf : f ∈ F) :
    t₁ * t₂ * t₁⁻¹ * t₂⁻¹ * f * (t₁ * t₂ * t₁⁻¹ * t₂⁻¹)⁻¹ = f := by
  have h₁F : ∀ f ∈ F, t₁ * f * t₁⁻¹ ∈ F := fun f hf => (mem_normalizer_iff.mp h₁ f).mp hf
  have h₂F : ∀ f ∈ F, t₂ * f * t₂⁻¹ ∈ F := fun f hf => (mem_normalizer_iff.mp h₂ f).mp hf
  have hinv : (t₂ * t₁)⁻¹ ∈ normalizer (F : Set G) := inv_mem (mul_mem h₂ h₁)
  have hf' : (t₂ * t₁)⁻¹ * f * (t₂ * t₁)⁻¹⁻¹ ∈ F := (mem_normalizer_iff.mp hinv f).mp hf
  have e := conj_mul_comm_of_fix hXF hcF hcov h₁F h₂F h₁X h₂X hf'
  calc t₁ * t₂ * t₁⁻¹ * t₂⁻¹ * f * (t₁ * t₂ * t₁⁻¹ * t₂⁻¹)⁻¹
      = t₁ * t₂ * ((t₂ * t₁)⁻¹ * f * (t₂ * t₁)⁻¹⁻¹) * (t₁ * t₂)⁻¹ := by group
    _ = t₂ * t₁ * ((t₂ * t₁)⁻¹ * f * (t₂ * t₁)⁻¹⁻¹) * (t₂ * t₁)⁻¹ := e
    _ = f := by group

end Index

section Smith23

variable {G : Type*} [Group G] [Finite G] (S : Setting G)

open CFSG.RankThree.OrthogonalInvolutions in
theorem conj_sq_of_centralizer_le {F : Subgroup G} (hFQ : F ≤ S.QG) {k : G} (hkM : k ∈ S.M)
    (hkF : ∀ f ∈ F, k * f * k⁻¹ ∈ F) (hk4 : ∀ f ∈ F, k ^ 4 * f * (k ^ 4)⁻¹ = f)
    (hC : ∀ f ∈ F, k ^ 2 * f * (k ^ 2)⁻¹ = f → k * f * k⁻¹ = f) {f : G} (hf : f ∈ F) :
    k ^ 2 * f * (k ^ 2)⁻¹ = f ∨ k ^ 2 * f * (k ^ 2)⁻¹ = f * S.z := by
  set T : S.Qt ≃ₗ[ZMod 2] S.Qt := ((S.ρ ⟨k, hkM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) with hTdef
  have hT : ∀ y ∈ S.QG, T (S.cl y) = S.cl (k * y * k⁻¹) := fun y hy => S.ρ_cl ⟨k, hkM⟩ hy
  have hkz : k * S.z * k⁻¹ = S.z := by
    rw [S.z_comm hkM]
    group
  set n : G → G := fun y => k * y * k⁻¹ * y⁻¹ with hndef
  have hnF : ∀ y ∈ F, n y ∈ F := fun y hy => F.mul_mem (hkF y hy) (F.inv_mem hy)
  have hcln : ∀ y ∈ F, S.cl (n y) = T (S.cl y) + S.cl y := fun y hy => by
    have hyQ := hFQ hy
    rw [S.cl_mul (S.conj_mem_QG hkM hyQ) (S.QG.inv_mem hyQ), S.cl_inv hyQ, hT y hyQ]
  have step1 : ∀ y ∈ F, S.cl (n y) = 0 → k * y * k⁻¹ = y := by
    intro y hy h0
    rcases (S.cl_eq_zero_iff (hFQ (hnF y hy))).mp h0 with h | h
    · calc k * y * k⁻¹ = k * y * k⁻¹ * y⁻¹ * y := by group
        _ = y := by rw [show k * y * k⁻¹ * y⁻¹ = 1 from h, one_mul]
    · have hky : k * y * k⁻¹ = y * S.z := by
        calc k * y * k⁻¹ = k * y * k⁻¹ * y⁻¹ * y := by group
          _ = S.z * y := by rw [show k * y * k⁻¹ * y⁻¹ = S.z from h]
          _ = y * S.z := (S.z_comm_QG (hFQ hy)).symm
      have hk2 : k ^ 2 * y * (k ^ 2)⁻¹ = y := by
        calc k ^ 2 * y * (k ^ 2)⁻¹ = k * (k * y * k⁻¹) * k⁻¹ := by rw [pow_two]; group
          _ = k * (y * S.z) * k⁻¹ := by rw [hky]
          _ = k * y * k⁻¹ * (k * S.z * k⁻¹) := by group
          _ = y := by rw [hky, hkz, mul_assoc, S.z_mul_z, mul_one]
      exact hC y hy hk2
  have hT2 : ∀ y ∈ S.QG, T (T (S.cl y)) = S.cl (k ^ 2 * y * (k ^ 2)⁻¹) := fun y hy => by
    rw [hT y hy, hT _ (S.conj_mem_QG hkM hy)]
    congr 1
    rw [pow_two]
    group
  have hNN : ∀ v : S.Qt, T (T v + v) + (T v + v) = T (T v) + v := fun v => by
    rw [map_add]
    calc T (T v) + T v + (T v + v) = T (T v) + (T v + T v) + v := by abel
      _ = T (T v) + v := by rw [add_self_vec (ZMod 2) (T v), add_zero]
  have hcl2 : ∀ y ∈ F, S.cl (n (n y)) = T (T (S.cl y)) + S.cl y := fun y hy => by
    rw [hcln _ (hnF y hy), hcln y hy, hNN]
  have hfQ := hFQ hf
  have hk2Q : k ^ 2 * f * (k ^ 2)⁻¹ ∈ S.QG := S.conj_mem_QG (pow_mem hkM 2) hfQ
  rw [← S.cl_eq_cl_iff hfQ hk2Q]
  by_contra hne
  have add_eq : ∀ a b : S.Qt, a + b = 0 → b = a := fun a b h => by
    calc b = b + (a + a) := by rw [add_self_vec (ZMod 2) a, add_zero]
      _ = a + b + a := by abel
      _ = a := by rw [h, zero_add]
  have hc2 : S.cl (n (n f)) ≠ 0 := by
    rw [hcl2 f hf, hT2 f hfQ]
    exact fun h => hne (add_eq _ _ h)
  have hT4 : T (T (T (T (S.cl f)))) = S.cl f := by
    rw [hT2 f hfQ, hT2 _ hk2Q]
    congr 1
    calc k ^ 2 * (k ^ 2 * f * (k ^ 2)⁻¹) * (k ^ 2)⁻¹ = k ^ 4 * f * (k ^ 4)⁻¹ := by
          rw [show k ^ 4 = k ^ 2 * k ^ 2 by rw [← pow_add]]
          group
      _ = f := hk4 f hf
  have hc4 : S.cl (n (n (n (n f)))) = 0 := by
    rw [hcl2 _ (hnF _ (hnF f hf)), hcl2 f hf, map_add, map_add, hT4]
    rw [show S.cl f + T (T (S.cl f)) + (T (T (S.cl f)) + S.cl f) =
        (S.cl f + S.cl f) + (T (T (S.cl f)) + T (T (S.cl f))) by abel,
      add_self_vec (ZMod 2), add_self_vec (ZMod 2), add_zero]
  obtain ⟨y', hy'F, hy1, hy2⟩ : ∃ y' ∈ F, S.cl (n (n y')) ≠ 0 ∧ S.cl (n (n (n y'))) = 0 := by
    by_cases h3 : S.cl (n (n (n f))) = 0
    · exact ⟨f, hf, hc2, h3⟩
    · exact ⟨n f, hnF f hf, h3, hc4⟩
  have hyF : n y' ∈ F := hnF y' hy'F
  have hyQ := hFQ hyF
  have hdF : n (n y') ∈ F := hnF _ hyF
  have hdQ := hFQ hdF
  set y := n y' with hydef
  set d := n y with hddef
  have hkd : k * d * k⁻¹ = d := step1 d hdF hy2
  have hky : k * y * k⁻¹ = d * y := by
    rw [hddef, hndef]
    group
  have hky1 : k * y * k⁻¹ ≠ y := fun h => hy1 (by
    have h' : d = 1 := by
      rw [hddef, hndef]
      simp only [h, mul_inv_cancel]
    rw [h', S.cl_one])
  have hk2y : k ^ 2 * y * (k ^ 2)⁻¹ = d * d * y := by
    calc k ^ 2 * y * (k ^ 2)⁻¹ = k * (k * y * k⁻¹) * k⁻¹ := by rw [pow_two]; group
      _ = k * (d * y) * k⁻¹ := by rw [hky]
      _ = (k * d * k⁻¹) * (k * y * k⁻¹) := by group
      _ = d * d * y := by rw [hkd, hky]; group
  have hdd : d ^ 2 = S.z := by
    rcases S.sq_eq_one_or_z hdQ with h | h
    · exfalso
      apply hky1
      apply hC y hyF
      rw [hk2y, ← pow_two, h, one_mul]
    · exact h
  have hyd : y * d = d * y := by
    rw [← S.polar_cl_eq_zero_iff hyQ hdQ]
    have hTd : T (S.cl d) = S.cl d := by rw [hT d hdQ, hkd]
    have hp : polar S.q (T (S.cl y')) (S.cl d) = polar S.q (S.cl y') (S.cl d) := by
      conv_lhs => rw [← hTd]
      exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (S.ρ ⟨k, hkM⟩).2 _ _
    show polar S.q (S.cl (n y')) (S.cl d) = 0
    rw [hcln y' hy'F, polar_add_left, hp, add_self_vec (ZMod 2)]
  have hy2' : (k * y * k⁻¹) ^ 2 = y ^ 2 := by
    rw [conj_pow]
    rcases S.sq_eq_one_or_z hyQ with h | h
    · rw [h]
      group
    · rw [h, hkz]
  have hdy : (d * y) ^ 2 = S.z * y ^ 2 := by
    calc (d * y) ^ 2 = d * (y * d) * y := by rw [pow_two]; group
      _ = d ^ 2 * y ^ 2 := by rw [hyd, pow_two, pow_two]; group
      _ = S.z * y ^ 2 := by rw [hdd]
  rw [hky, hdy] at hy2'
  exact S.z_ne_one (by simpa using hy2')

end Smith23

end Sm77

end CFSG.LargeExtraspecial.DW
