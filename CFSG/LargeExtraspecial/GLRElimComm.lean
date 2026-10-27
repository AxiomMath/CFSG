module

public import CFSG.LargeExtraspecial.GLRElimPhi
public import CFSG.LargeExtraspecial.GLRElimSylow

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLR

open Subgroup Module CFSG.GH74.GLS.Bg.Thompson
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem isPGroup_closure_of_commute {s : Set G} (hcomm : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a)
    (hsq : ∀ a ∈ s, a * a = 1) : IsPGroup 2 (closure s) := by
  have hc := Subgroup.isMulCommutative_closure (k := s) fun a ha b hb _ => hcomm a ha b hb
  have key : ∀ x ∈ closure s, x * x = 1 := by
    intro x hx
    induction hx using closure_induction with
    | mem x hx => exact hsq x hx
    | one => exact mul_one 1
    | mul x y hx hy ihx ihy =>
      have hxy : x * y = y * x :=
        congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : closure s) ⟨y, hy⟩)
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [hxy]
        _ = (x * x) * (y * y) := by group
        _ = 1 := by rw [ihx, ihy, mul_one]
    | inv x _ ihx => rw [← mul_inv_rev, ihx, inv_one]
  intro g
  exact ⟨1, Subtype.ext (by rw [pow_one, pow_two]; exact key g g.2)⟩

variable [Finite G] {S : Setting G} {C : Config S}

namespace Levi

variable (Λ : Levi C)

theorem exists_sylowIn_z_mem_commutator {τ : G} (hτM : τ ∈ S.M) (hτX : τ ∉ C.X)
    (hτL : Λ.Normalizes τ) (hττ : τ * τ = 1) (hβ : IsGoodForm (C.formOf (S.ρ ⟨τ, hτM⟩))) :
    ∃ T, IsSylowIn 2 T (centralizer {τ} ⊓ S.M) ∧ S.z ∈ ⁅T, T⁆ := by
  set β := C.formOf (S.ρ ⟨τ, hτM⟩) with hβdef
  obtain ⟨e, e', v₁, v₂, v₃, hee, he'e', hv₁, hv₂, hv₃, hee', hv₁e, hv₂e', hv₃e⟩ :=
    hβ.exists_vectors
  have hsymm := hβ.symm
  have hf : β (e + e') (e + e') = 0 := by
    simp only [map_add, LinearMap.add_apply, hee, he'e', hee', hsymm e' e, add_zero]
  have hiso : ∀ {x : C.At} (hx : β x x = 0) (a a' : C.At),
      β (transv hx a) (transv hx a') = β a a' := fun hx a a' => transvMap_isometry hsymm hx a a'
  obtain ⟨l₁, hl₁τ, hl₁⟩ := Λ.exists_lift_commute hτM hτX hττ hτL (transv hee) (hiso hee)
  obtain ⟨l₂, hl₂τ, hl₂⟩ := Λ.exists_lift_commute hτM hτX hττ hτL (transv he'e') (hiso he'e')
  obtain ⟨l₃, hl₃τ, hl₃⟩ := Λ.exists_lift_commute hτM hτX hττ hτL (transv hf) (hiso hf)
  have hinj : Function.Injective (fun l : Λ.L => C.resAt (Λ.toXbar l)) :=
    C.resAt_injective.comp Λ.toXbar_bijective.1
  have hcomm' : ∀ (l l' : Λ.L), C.resAt (Λ.toXbar l) * C.resAt (Λ.toXbar l') =
      C.resAt (Λ.toXbar l') * C.resAt (Λ.toXbar l) → (l : G) * l' = l' * l := by
    intro l l' h
    have : l * l' = l' * l := hinj (by simp only [map_mul]; exact h)
    exact congrArg Subtype.val this
  have hsq' : ∀ (l : Λ.L), C.resAt (Λ.toXbar l) * C.resAt (Λ.toXbar l) = 1 →
      (l : G) * l = 1 := by
    intro l h
    have : l * l = 1 := hinj (by simp only [map_mul, map_one]; exact h)
    exact congrArg Subtype.val this
  have htt : ∀ {x y : C.At} (hx : β x x = 0) (hy : β y y = 0), β x y = 0 →
      transv hx * transv hy = transv hy * transv hx := fun hx hy hxy =>
    LinearEquiv.ext fun a => transvMap_comm hsymm hxy a
  have ht2 : ∀ {x : C.At} (hx : β x x = 0), transv hx * transv hx = 1 := fun hx =>
    LinearEquiv.ext fun a => transvMap_transvMap hx a
  have hee'' : β e (e + e') = 0 := by rw [map_add, hee, hee', add_zero]
  have he'e'' : β e' (e + e') = 0 := by rw [map_add, hsymm e' e, hee', he'e', add_zero]
  let E : Subgroup G := closure ({(l₁ : G), (l₂ : G), (l₃ : G)} : Set G)
  have c12 : (l₁ : G) * l₂ = l₂ * l₁ := hcomm' l₁ l₂ (by rw [hl₁, hl₂]; exact htt hee he'e' hee')
  have c13 : (l₁ : G) * l₃ = l₃ * l₁ := hcomm' l₁ l₃ (by rw [hl₁, hl₃]; exact htt hee hf hee'')
  have c23 : (l₂ : G) * l₃ = l₃ * l₂ :=
    hcomm' l₂ l₃ (by rw [hl₂, hl₃]; exact htt he'e' hf he'e'')
  have s1 : (l₁ : G) * l₁ = 1 := hsq' l₁ (by rw [hl₁]; exact ht2 hee)
  have s2 : (l₂ : G) * l₂ = 1 := hsq' l₂ (by rw [hl₂]; exact ht2 he'e')
  have s3 : (l₃ : G) * l₃ = 1 := hsq' l₃ (by rw [hl₃]; exact ht2 hf)
  have hE2 : IsPGroup 2 E := by
    refine isPGroup_closure_of_commute ?_ ?_
    · intro a ha b hb
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
        first
        | rfl
        | exact c12
        | exact c12.symm
        | exact c13
        | exact c13.symm
        | exact c23
        | exact c23.symm
    · intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl | rfl
      · exact s1
      · exact s2
      · exact s3
  have hEC : E ≤ centralizer {τ} ⊓ S.M := by
    refine (closure_le _).mpr ?_
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe, mem_inf,
      mem_centralizer_singleton_iff]
    exact ⟨⟨hl₁τ, S.mem_M_iff.mp (Λ.L_le_M l₁.2)⟩, ⟨hl₂τ, S.mem_M_iff.mp (Λ.L_le_M l₂.2)⟩,
      ⟨hl₃τ, S.mem_M_iff.mp (Λ.L_le_M l₃.2)⟩⟩
  obtain ⟨T, hET, hT⟩ := exists_isSylowIn_le hEC hE2
  have hCQ : S.QG ⊓ centralizer {τ} ≤ T := SylowIn.le_of_normal hT
    (fun q hq => ⟨hq.2, S.QG_le_M hq.1⟩)
    ((Config.isPGroup_QG S).to_le inf_le_left)
    (fun g hg q hq => mem_inf.mpr ⟨S.conj_mem_QG hg.2 hq.1, mem_centralizer_singleton_iff.mpr (by
      have h1 := mem_centralizer_singleton_iff.mp hg.1
      have h2 := mem_centralizer_singleton_iff.mp hq.2
      calc g * q * g⁻¹ * τ = g * q * (g⁻¹ * τ) := by group
        _ = g * q * (τ * g⁻¹) := by
            rw [show g⁻¹ * τ = τ * g⁻¹ by
              calc g⁻¹ * τ = g⁻¹ * (τ * g) * g⁻¹ := by group
                _ = g⁻¹ * (g * τ) * g⁻¹ := by rw [h1]
                _ = τ * g⁻¹ := by group]
        _ = g * (q * τ) * g⁻¹ := by group
        _ = g * (τ * q) * g⁻¹ := by rw [h2]
        _ = (g * τ) * q * g⁻¹ := by group
        _ = (τ * g) * q * g⁻¹ := by rw [h1]
        _ = τ * (g * q * g⁻¹) := by group)⟩)
  have hφT : ∀ v : C.At, β v v = 0 → Λ.phi τ v ∈ T := fun v hv => hCQ
    ⟨Λ.phi_mem_QG hτM hτX v, mem_centralizer_singleton_iff.mpr (Λ.phi_comm hτM hτX hττ hv).symm⟩
  have hcomm_val : ∀ {x : C.At} (hx : β x x = 0) (l : Λ.L), (l : G) * τ = τ * l →
      C.resAt (Λ.toXbar l) = transv hx → ∀ v : C.At, β v v = 0 → β v x = 1 →
        ⁅Λ.phi τ v, (l : G)⁆ = Λ.phi τ x * S.z := by
    intro x hx l hlτ hl v hv hvx
    have hlv : C.resAt (Λ.toXbar l) v = v + x := by rw [hl, transv_apply, hvx, one_smul]
    have h1 := Λ.commutator_phi hτM hτX l.2 hlτ (a := v) (by
      change β (C.resAt (Λ.toXbar l) v) (C.resAt (Λ.toXbar l) v) = 0
      rw [hl, hiso hx]
      exact hv)
    change ⁅Λ.phi τ v, (l : G)⁆ = Λ.phi τ v * Λ.phi τ (C.resAt (Λ.toXbar l) v) at h1
    rw [h1, hlv, Λ.phi_mul_of_eq_one hτM hτX (by
      rw [map_add, LinearMap.add_apply, hv, hsymm x v, hvx, zero_add])]
    congr 2
    rw [← add_assoc, ZModModule.add_self, zero_add]
  have hc₁ := hcomm_val hee l₁ hl₁τ hl₁ v₁ hv₁ hv₁e
  have hc₂ := hcomm_val he'e' l₂ hl₂τ hl₂ v₂ hv₂ hv₂e'
  have hc₃ := hcomm_val hf l₃ hl₃τ hl₃ v₃ hv₃ hv₃e
  refine ⟨T, hT, ?_⟩
  have hzc : ∀ g ∈ S.M, g * S.z = S.z * g := fun g hg => S.z_comm hg
  have hφM : ∀ v, Λ.phi τ v ∈ S.M := fun v => S.QG_le_M (Λ.phi_mem_QG hτM hτX v)
  have hprod : ⁅Λ.phi τ v₁, (l₁ : G)⁆ * ⁅Λ.phi τ v₂, (l₂ : G)⁆ * ⁅Λ.phi τ v₃, (l₃ : G)⁆ = S.z := by
    rw [hc₁, hc₂, hc₃]
    have h12 := Λ.phi_mul_of_eq_zero hτM hτX (a := e) (a' := e')
      (by rw [hsymm e' e]; exact hee')
    have h33 := Λ.phi_mul_self hτM hτX hf
    calc Λ.phi τ e * S.z * (Λ.phi τ e' * S.z) * (Λ.phi τ (e + e') * S.z)
        = Λ.phi τ e * (S.z * Λ.phi τ e') * S.z * (Λ.phi τ (e + e') * S.z) := by group
      _ = Λ.phi τ e * (Λ.phi τ e' * S.z) * S.z * (Λ.phi τ (e + e') * S.z) := by
          rw [hzc _ (hφM e')]
      _ = Λ.phi τ e * Λ.phi τ e' * (S.z * S.z) * (Λ.phi τ (e + e') * S.z) := by group
      _ = Λ.phi τ (e + e') * Λ.phi τ (e + e') * S.z := by
          rw [S.z_mul_z, mul_one, h12, ← mul_assoc]
      _ = S.z := by rw [h33, one_mul]
  rw [← hprod]
  exact mul_mem (mul_mem
    (commutator_mem_commutator (hφT v₁ hv₁) (hET (subset_closure (by simp))))
    (commutator_mem_commutator (hφT v₂ hv₂) (hET (subset_closure (by simp)))))
    (commutator_mem_commutator (hφT v₃ hv₃) (hET (subset_closure (by simp))))

end Levi

end CFSG.LargeExtraspecial.GLR
