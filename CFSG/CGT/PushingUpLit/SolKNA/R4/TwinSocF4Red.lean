module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp22RestAut

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Generic

section Restrict

variable {A : Type*} [Group A] [Finite A] {T : Subgroup A} [T.Normal]

theorem map_eq_self (hT : IsSimpleGroup ↥T) (hab : ∃ a b : ↥T, a * b ≠ b * a)
    (hC : Subgroup.centralizer (T : Set A) = ⊥) (φ : A ≃* A) : T.map φ.toMonoidHom = T := by
  have hN : (T.map φ.toMonoidHom).Normal := Subgroup.Normal.map inferInstance _ φ.surjective
  have hM : ((T.map φ.toMonoidHom ⊓ T).subgroupOf T).Normal := by
    haveI : (T.map φ.toMonoidHom ⊓ T).Normal := Subgroup.normal_inf_normal _ _
    exact Subgroup.normal_subgroupOf
  haveI := hT
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((T.map φ.toMonoidHom ⊓ T).subgroupOf T) with h | h
  · exfalso
    have hint : T.map φ.toMonoidHom ⊓ T = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hxs : (⟨x, hx.2⟩ : ↥T) ∈ (T.map φ.toMonoidHom ⊓ T).subgroupOf T :=
        Subgroup.mem_subgroupOf.mpr hx
      rw [h] at hxs
      have := (Subgroup.mem_bot.mp hxs)
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
    have hle : T.map φ.toMonoidHom ≤ Subgroup.centralizer (T : Set A) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hc : x * y * x⁻¹ * y⁻¹ ∈ T.map φ.toMonoidHom ⊓ T := by
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · have h1 : y * x⁻¹ * y⁻¹ ∈ T.map φ.toMonoidHom := hN.conj_mem _ (inv_mem hx) y
          have h2 := mul_mem hx h1
          simpa [mul_assoc] using h2
        · have h1 : x * y * x⁻¹ ∈ T := (inferInstance : T.Normal).conj_mem y hy x
          exact mul_mem h1 (inv_mem hy)
      rw [hint, Subgroup.mem_bot] at hc
      have : x * y * x⁻¹ = y := by
        calc x * y * x⁻¹ = x * y * x⁻¹ * y⁻¹ * y := by group
          _ = y := by rw [hc, one_mul]
      calc y * x = x * y * x⁻¹ * x := by rw [this]
        _ = x * y := by group
    rw [hC, le_bot_iff] at hle
    obtain ⟨a, b, hab⟩ := hab
    have hb : ∀ x : ↥T, x = 1 := by
      intro x
      have hx : φ (x : A) ∈ T.map φ.toMonoidHom := ⟨x, x.2, rfl⟩
      rw [hle, Subgroup.mem_bot] at hx
      exact Subtype.ext (by simpa using hx)
    exact hab (by rw [hb a, hb b])
  · have hle : T ≤ T.map φ.toMonoidHom := by
      intro x hx
      have hxs : (⟨x, hx⟩ : ↥T) ∈ (T.map φ.toMonoidHom ⊓ T).subgroupOf T := by
        rw [h]
        exact Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.mp hxs).1
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [Subgroup.card_map_of_injective φ.injective]

theorem mem_iff_apply_mem (hT : IsSimpleGroup ↥T) (hab : ∃ a b : ↥T, a * b ≠ b * a)
    (hC : Subgroup.centralizer (T : Set A) = ⊥) (φ : A ≃* A) (x : A) : x ∈ T ↔ φ x ∈ T := by
  have h := map_eq_self hT hab hC φ
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := φ.injective hyx
    rwa [← this]

@[expose] noncomputable def restrictAut (hT : IsSimpleGroup ↥T) (hab : ∃ a b : ↥T, a * b ≠ b * a)
    (hC : Subgroup.centralizer (T : Set A) = ⊥) (φ : A ≃* A) : MulAut ↥T where
  toFun x := ⟨φ x, (mem_iff_apply_mem hT hab hC φ x).mp x.2⟩
  invFun x := ⟨φ.symm x, by
    rw [mem_iff_apply_mem hT hab hC φ, MulEquiv.apply_symm_apply]
    exact x.2⟩
  left_inv x := Subtype.ext (by simp)
  right_inv x := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)

@[simp] theorem restrictAut_apply (hT : IsSimpleGroup ↥T) (hab : ∃ a b : ↥T, a * b ≠ b * a)
    (hC : Subgroup.centralizer (T : Set A) = ⊥) (φ : A ≃* A) (x : ↥T) :
    ((restrictAut hT hab hC φ x : ↥T) : A) = φ x :=
  rfl

theorem eq_of_conj_eq (hC : Subgroup.centralizer (T : Set A) = ⊥) {g h : A}
    (hgh : ∀ x ∈ T, g * x * g⁻¹ = h * x * h⁻¹) : g = h := by
  have hmem : h⁻¹ * g ∈ Subgroup.centralizer (T : Set A) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have e := hgh x hx
    calc x * (h⁻¹ * g) = h⁻¹ * (h * x * h⁻¹) * g := by group
      _ = h⁻¹ * (g * x * g⁻¹) * g := by rw [e]
      _ = h⁻¹ * g * x := by group
  rw [hC, Subgroup.mem_bot] at hmem
  calc g = h * (h⁻¹ * g) := by group
    _ = h := by rw [hmem, mul_one]

theorem eq_of_restrictAut_eq_conjNormal (hT : IsSimpleGroup ↥T) (hab : ∃ a b : ↥T, a * b ≠ b * a)
    (hC : Subgroup.centralizer (T : Set A) = ⊥) (φ : A ≃* A) (g : A)
    (hψ : restrictAut hT hab hC φ = MulAut.conjNormal g) (a : A) : φ a = g * a * g⁻¹ := by
  have hφT : ∀ x ∈ T, φ x = g * x * g⁻¹ := fun x hx => by
    have := congrArg (fun χ : MulAut ↥T => ((χ ⟨x, hx⟩ : ↥T) : A)) hψ
    simpa using this
  refine eq_of_conj_eq hC fun x hx => ?_
  have hax : a * x * a⁻¹ ∈ T := (inferInstance : T.Normal).conj_mem x hx a
  have e1 : φ (a * x * a⁻¹) = φ a * φ x * (φ a)⁻¹ := by simp
  rw [hφT _ hax, hφT x hx] at e1
  have key : ∀ y ∈ T, (φ a)⁻¹ * (g * a * g⁻¹) * y = y * ((φ a)⁻¹ * (g * a * g⁻¹)) := by
    intro y hy
    have hy' : g⁻¹ * y * g ∈ T := by
      have := (inferInstance : T.Normal).conj_mem y hy g⁻¹
      simpa using this
    have hay : a * (g⁻¹ * y * g) * a⁻¹ ∈ T := (inferInstance : T.Normal).conj_mem _ hy' a
    have e2 : φ (a * (g⁻¹ * y * g) * a⁻¹) = φ a * φ (g⁻¹ * y * g) * (φ a)⁻¹ := by simp
    rw [hφT _ hay, hφT _ hy'] at e2
    have e3 : g * (a * (g⁻¹ * y * g) * a⁻¹) * g⁻¹ = (g * a * g⁻¹) * y * (g * a * g⁻¹)⁻¹ := by group
    have e4 : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    rw [e3, e4] at e2
    calc (φ a)⁻¹ * (g * a * g⁻¹) * y
        = (φ a)⁻¹ * ((g * a * g⁻¹) * y * (g * a * g⁻¹)⁻¹) * (g * a * g⁻¹) := by group
      _ = (φ a)⁻¹ * (φ a * y * (φ a)⁻¹) * (g * a * g⁻¹) := by rw [e2]
      _ = y * ((φ a)⁻¹ * (g * a * g⁻¹)) := by group
  have hmem : (φ a)⁻¹ * (g * a * g⁻¹) ∈ Subgroup.centralizer (T : Set A) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (key y hy).symm
  rw [hC, Subgroup.mem_bot] at hmem
  have hφa : φ a = g * a * g⁻¹ := by
    calc φ a = φ a * ((φ a)⁻¹ * (g * a * g⁻¹)) := by rw [hmem, mul_one]
      _ = g * a * g⁻¹ := by group
  rw [hφa]

theorem eq_self_of_restrictAut_eq_one (hT : IsSimpleGroup ↥T) (hab : ∃ a b : ↥T, a * b ≠ b * a)
    (hC : Subgroup.centralizer (T : Set A) = ⊥) (φ : A ≃* A) (hψ : restrictAut hT hab hC φ = 1)
    (a : A) : φ a = a := by
  have h := eq_of_restrictAut_eq_conjNormal hT hab hC φ 1 (by rw [hψ, map_one]) a
  simpa using h

theorem restrictAut_mul_self (hT : IsSimpleGroup ↥T) (hab : ∃ a b : ↥T, a * b ≠ b * a)
    (hC : Subgroup.centralizer (T : Set A) = ⊥) (φ : A ≃* A) (hφ : ∀ x, φ (φ x) = x) :
    restrictAut hT hab hC φ * restrictAut hT hab hC φ = 1 := by
  ext x
  simp [hφ]

theorem restrictAut_comm_conjNormal (hT : IsSimpleGroup ↥T) (hab : ∃ a b : ↥T, a * b ≠ b * a)
    (hC : Subgroup.centralizer (T : Set A) = ⊥) (φ : A ≃* A) {s : A} (hs : φ s = s) :
    restrictAut hT hab hC φ * MulAut.conjNormal s = MulAut.conjNormal s * restrictAut hT hab hC φ := by
  ext x
  simp [hs]

end Restrict

section Model


@[expose] def AutCentInvR (r : ℕ) : Prop :=
  4 ≤ r → ∀ (A : Type) [Group A] [Finite A] (T : Subgroup A) [T.Normal], IsSimpleGroup ↥T →
    (∃ a b : ↥T, a * b ≠ b * a) → Subgroup.centralizer (T : Set A) = ⊥ → EdgelessFamily ↥T →
    ∀ (R : Subgroup A) (S : Sylow 2 R) (z : A), TightDatum R S z → TightClsR r A R S z →
      ¬ TightInO2 z → TightEdgeless R →
      ∀ ψ : MulAut ↥T, ψ * ψ = 1 →
        (∀ s ∈ (S : Subgroup R).map R.subtype, ψ * MulAut.conjNormal s = MulAut.conjNormal s * ψ) →
          ψ = 1 ∨ ψ = MulAut.conjNormal z

theorem model163R_of_autCentInvR {r : ℕ} (h : AutCentInvR r) : Perp22Rest.Model163R r := by
  intro hr A _ _ T _ hT hab hC hE R S z hd hc hnO hed φ hφ hS
  rcases h hr A T hT hab hC hE R S z hd hc hnO hed (restrictAut hT hab hC φ)
      (restrictAut_mul_self hT hab hC φ hφ)
      (fun s hs => restrictAut_comm_conjNormal hT hab hC φ (hS s hs)) with hψ | hψ
  · exact Or.inl (eq_self_of_restrictAut_eq_one hT hab hC φ hψ)
  · exact Or.inr (eq_of_restrictAut_eq_conjNormal hT hab hC φ z hψ)

end Model

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4
