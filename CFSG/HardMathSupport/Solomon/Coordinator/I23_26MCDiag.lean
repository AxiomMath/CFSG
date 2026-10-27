module

public import CFSG.Quasithin.Background.F918V5GComp
public import CFSG.LocalAnalysis.GLTheoremB.PGroupBasics

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

section Diag

variable {Y : Type*} [Group Y] [Finite Y]

theorem mc_isComponentOf_gLBConj {L : Subgroup Y} (hL : IsComponentOf L ⊤) (g : Y) :
    IsComponentOf (GLBConj g L) ⊤ := by
  have hX : (⊤ : Subgroup Y).map (MulAut.conj g⁻¹).toMonoidHom = ⊤ :=
    Subgroup.map_top_of_surjective _ fun y => ⟨g * y * g⁻¹, by simp [mul_assoc]⟩
  refine ⟨le_top, ?_, ?_⟩
  · have := CFSG.Quasithin.A3.subnormal_map (MulAut.conj g⁻¹).toMonoidHom hL.2.1
    rwa [hX] at this
  · have hq : CFSG.IsQuasisimple ↥L := CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hL.2.2
    exact CFSG.Quasithin.A3.isQuasisimple_iff_open.mp (CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (L.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective) hq)

theorem mc_comm_of_ne {A B : Subgroup Y} (hA : IsComponentOf A ⊤) (hB : IsComponentOf B ⊤)
    (hne : A ≠ B) {x y : Y} (hx : x ∈ A) (hy : y ∈ B) : x * y = y * x := by
  rcases CFSG.Quasithin.F918V5G.isComponentOf_eq_or_commute hA hB with h | h
  · exact absurd h hne
  · exact h x hx y hy

theorem mc_conj_conj (g f : Y) (H : Subgroup Y) :
    GLBConj g (GLBConj f H) = GLBConj (f * g) H := gLBConj_gLBConj g f H

@[expose] def mcD (g k : Y) : Y := k * (g⁻¹ * k * g) * (g * k * g⁻¹)

theorem mc_gLBConj_inv_ne {K₁ : Subgroup Y} {g : Y} (hg3 : g ^ 3 = 1)
    (hne : GLBConj g K₁ ≠ K₁) : GLBConj g⁻¹ K₁ ≠ K₁ ∧ GLBConj g K₁ ≠ GLBConj g⁻¹ K₁ := by
  have hgg : g * g = g⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    exact (pow_three g).symm.trans hg3
  have h1 : GLBConj g⁻¹ K₁ ≠ K₁ := by
    intro h
    apply hne
    have := congrArg (GLBConj g) h
    rw [mc_conj_conj, inv_mul_cancel, gLBConj_one] at this
    exact this.symm
  refine ⟨h1, fun h => h1 ?_⟩
  have := congrArg (GLBConj g) h
  rw [mc_conj_conj, mc_conj_conj, inv_mul_cancel, gLBConj_one, hgg] at this
  exact this

theorem mc_mem_conj {K₁ : Subgroup Y} {g k : Y} (hk : k ∈ K₁) : g⁻¹ * k * g ∈ GLBConj g K₁ :=
  mem_gLBConj.2 (by
    have e : g * (g⁻¹ * k * g) * g⁻¹ = k := by group
    rw [e]; exact hk)

theorem mc_mem_conj_inv {K₁ : Subgroup Y} {g k : Y} (hk : k ∈ K₁) :
    g * k * g⁻¹ ∈ GLBConj g⁻¹ K₁ :=
  mem_gLBConj.2 (by
    rw [inv_inv]
    have e : g⁻¹ * (g * k * g⁻¹) * g = k := by group
    rw [e]; exact hk)

theorem mc_mul_perm {k k' b b' c c' : Y} (h1 : b * k' = k' * b) (h2 : c * k' = k' * c)
    (h3 : c * b' = b' * c) :
    k * b * c * (k' * b' * c') = k * k' * (b * b') * (c * c') :=
  calc k * b * c * (k' * b' * c') = k * b * (c * k') * b' * c' := by group
    _ = k * b * (k' * c) * b' * c' := by rw [h2]
    _ = k * (b * k') * c * b' * c' := by group
    _ = k * (k' * b) * c * b' * c' := by rw [h1]
    _ = k * k' * b * (c * b') * c' := by group
    _ = k * k' * b * (b' * c) * c' := by rw [h3]
    _ = k * k' * (b * b') * (c * c') := by group

section Comm

variable {K₁ : Subgroup Y} (hK₁ : IsComponentOf K₁ ⊤) {g : Y} (hg3 : g ^ 3 = 1)
  (hne : GLBConj g K₁ ≠ K₁)
include hK₁ hg3 hne

theorem mc_comm_12 {x y : Y} (hx : x ∈ GLBConj g K₁) (hy : y ∈ K₁) : x * y = y * x :=
  mc_comm_of_ne (mc_isComponentOf_gLBConj hK₁ g) hK₁ hne hx hy

theorem mc_comm_13 {x y : Y} (hx : x ∈ GLBConj g⁻¹ K₁) (hy : y ∈ K₁) : x * y = y * x :=
  mc_comm_of_ne (mc_isComponentOf_gLBConj hK₁ g⁻¹) hK₁ (mc_gLBConj_inv_ne hg3 hne).1 hx hy

theorem mc_comm_23 {x y : Y} (hx : x ∈ GLBConj g⁻¹ K₁) (hy : y ∈ GLBConj g K₁) :
    x * y = y * x :=
  mc_comm_of_ne (mc_isComponentOf_gLBConj hK₁ g⁻¹) (mc_isComponentOf_gLBConj hK₁ g)
    (mc_gLBConj_inv_ne hg3 hne).2.symm hx hy

theorem mcD_mul {k k' : Y} (hk : k ∈ K₁) (hk' : k' ∈ K₁) :
    mcD g (k * k') = mcD g k * mcD g k' := by
  unfold mcD
  have e : k * k' * (g⁻¹ * (k * k') * g) * (g * (k * k') * g⁻¹) =
      k * k' * ((g⁻¹ * k * g) * (g⁻¹ * k' * g)) * ((g * k * g⁻¹) * (g * k' * g⁻¹)) := by group
  rw [e]
  exact (mc_mul_perm (mc_comm_12 hK₁ hg3 hne (mc_mem_conj hk) hk')
    (mc_comm_13 hK₁ hg3 hne (mc_mem_conj_inv hk) hk')
    (mc_comm_23 hK₁ hg3 hne (mc_mem_conj_inv hk) (mc_mem_conj hk'))).symm

theorem mcD_inv_mul_comm {k : Y} (hk : k ∈ K₁) {y : Y} (hy : y ∈ K₁) :
    y * ((mcD g k)⁻¹ * k) = ((mcD g k)⁻¹ * k) * y := by
  unfold mcD
  have e : (k * (g⁻¹ * k * g) * (g * k * g⁻¹))⁻¹ * k =
      (g * k * g⁻¹)⁻¹ * (g⁻¹ * k * g)⁻¹ := by group
  rw [e]
  have h2 : (g⁻¹ * k * g)⁻¹ ∈ GLBConj g K₁ := (GLBConj g K₁).inv_mem (mc_mem_conj hk)
  have h3 : (g * k * g⁻¹)⁻¹ ∈ GLBConj g⁻¹ K₁ := (GLBConj g⁻¹ K₁).inv_mem (mc_mem_conj_inv hk)
  have e2 := mc_comm_12 hK₁ hg3 hne h2 hy
  have e3 := mc_comm_13 hK₁ hg3 hne h3 hy
  calc y * ((g * k * g⁻¹)⁻¹ * (g⁻¹ * k * g)⁻¹)
      = (y * (g * k * g⁻¹)⁻¹) * (g⁻¹ * k * g)⁻¹ := by group
    _ = ((g * k * g⁻¹)⁻¹ * y) * (g⁻¹ * k * g)⁻¹ := by rw [← e3]
    _ = (g * k * g⁻¹)⁻¹ * (y * (g⁻¹ * k * g)⁻¹) := by group
    _ = (g * k * g⁻¹)⁻¹ * ((g⁻¹ * k * g)⁻¹ * y) := by rw [← e2]
    _ = (g * k * g⁻¹)⁻¹ * (g⁻¹ * k * g)⁻¹ * y := by group

theorem mcD_conj_g {k : Y} (hk : k ∈ K₁) : g⁻¹ * mcD g k * g = mcD g k := by
  have hgg : g * g = g⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    exact (pow_three g).symm.trans hg3
  have hgg' : g⁻¹ * g⁻¹ = g := by
    rw [← mul_inv_rev, hgg, inv_inv]
  have e1 : g⁻¹ * (g⁻¹ * k * g) * g = g * k * g⁻¹ := by
    calc g⁻¹ * (g⁻¹ * k * g) * g = (g⁻¹ * g⁻¹) * k * (g * g) := by group
      _ = g * k * g⁻¹ := by rw [hgg, hgg']
  have e2 : g⁻¹ * (g * k * g⁻¹) * g = k := by group
  unfold mcD
  have e : g⁻¹ * (k * (g⁻¹ * k * g) * (g * k * g⁻¹)) * g =
      (g⁻¹ * k * g) * (g⁻¹ * (g⁻¹ * k * g) * g) * (g⁻¹ * (g * k * g⁻¹) * g) := by group
  rw [e, e1, e2]
  have c1 := mc_comm_12 hK₁ hg3 hne (mc_mem_conj hk) hk
  have c2 := mc_comm_13 hK₁ hg3 hne (mc_mem_conj_inv hk) hk
  calc g⁻¹ * k * g * (g * k * g⁻¹) * k = g⁻¹ * k * g * ((g * k * g⁻¹) * k) := by group
    _ = g⁻¹ * k * g * (k * (g * k * g⁻¹)) := by rw [c2]
    _ = (g⁻¹ * k * g * k) * (g * k * g⁻¹) := by group
    _ = (k * (g⁻¹ * k * g)) * (g * k * g⁻¹) := by rw [c1]
    _ = k * (g⁻¹ * k * g) * (g * k * g⁻¹) := by group

end Comm

theorem mcD_conj {g c k : Y} (hcg : c * g = g * c) :
    c * mcD g k * c⁻¹ = mcD g (c * k * c⁻¹) := by
  have hC : Commute c g := hcg
  have hc1 : c * g⁻¹ = g⁻¹ * c := hC.inv_right.eq
  have hc2 : g * c⁻¹ = c⁻¹ * g := (hC.inv_left.symm).eq
  have hc3 : g⁻¹ * c⁻¹ = c⁻¹ * g⁻¹ := (hC.inv_inv.symm).eq
  have key : ∀ x : Y, c * (g⁻¹ * x * g) * c⁻¹ = g⁻¹ * (c * x * c⁻¹) * g := fun x =>
    calc c * (g⁻¹ * x * g) * c⁻¹ = (c * g⁻¹) * x * (g * c⁻¹) := by group
      _ = (g⁻¹ * c) * x * (c⁻¹ * g) := by rw [hc1, hc2]
      _ = g⁻¹ * (c * x * c⁻¹) * g := by group
  have key' : ∀ x : Y, c * (g * x * g⁻¹) * c⁻¹ = g * (c * x * c⁻¹) * g⁻¹ := fun x =>
    calc c * (g * x * g⁻¹) * c⁻¹ = (c * g) * x * (g⁻¹ * c⁻¹) := by group
      _ = (g * c) * x * (c⁻¹ * g⁻¹) := by rw [hcg, hc3]
      _ = g * (c * x * c⁻¹) * g⁻¹ := by group
  unfold mcD
  have e : c * (k * (g⁻¹ * k * g) * (g * k * g⁻¹)) * c⁻¹ =
      (c * k * c⁻¹) * (c * (g⁻¹ * k * g) * c⁻¹) * (c * (g * k * g⁻¹) * c⁻¹) := by group
  rw [e, key, key']

section Hom

variable {K₁ : Subgroup Y} (hK₁ : IsComponentOf K₁ ⊤) {g : Y} (hg3 : g ^ 3 = 1)
  (hne : GLBConj g K₁ ≠ K₁)

@[expose] noncomputable def mcDHom : ↥K₁ →* Y :=
  MonoidHom.mk' (fun k : ↥K₁ => mcD g (k : Y)) (fun a b => mcD_mul hK₁ hg3 hne a.2 b.2)

include hK₁ hg3 hne in
theorem mc_diag_exists (h3 : 3 ∣ Nat.card (↥K₁ ⧸ Subgroup.center ↥K₁)) :
    ∃ D : Subgroup Y, CFSG.Open.IsQuasisimple ↥D ∧ 3 ∣ Nat.card D ∧
      (∀ d, d ∈ D ↔ ∃ k ∈ K₁, d = mcD g k) ∧ (∀ d ∈ D, g⁻¹ * d * g = d) := by
  let d := mcDHom hK₁ hg3 hne
  have hd : ∀ k : ↥K₁, d k = mcD g (k : Y) := fun k => rfl
  have hker : d.ker ≤ Subgroup.center ↥K₁ := by
    intro x hx
    rw [MonoidHom.mem_ker, hd] at hx
    have h2 : ∀ y ∈ K₁, y * ((mcD g (x : Y))⁻¹ * (x : Y)) = ((mcD g (x : Y))⁻¹ * (x : Y)) * y :=
      fun y hy => mcD_inv_mul_comm hK₁ hg3 hne x.2 hy
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have := h2 y y.2
    rw [hx] at this
    simpa using this
  refine ⟨d.range, ?_, ?_, ?_, ?_⟩
  · have hq : CFSG.IsQuasisimple ↥K₁ := CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hK₁.2.2
    exact CFSG.Quasithin.A3.isQuasisimple_iff_open.mp
      (CFSG.LocalCores.isQuasisimple_of_surjective hq d.rangeRestrict d.rangeRestrict_surjective
        (by rw [MonoidHom.ker_rangeRestrict]; exact hker))
  · have h1 : (Subgroup.center ↥K₁).index ∣ d.ker.index := Subgroup.index_dvd_of_le hker
    rw [Subgroup.index_ker] at h1
    exact h3.trans h1
  · intro y
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, k.2, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
  · rintro _ ⟨k, rfl⟩
    rw [hd]
    exact mcD_conj_g hK₁ hg3 hne k.2

end Hom

end Diag

end CFSG.HardMathSupport.Solomon.Coordinator
