module

public import CFSG.LieType.SeitzGeneration.HyperIrrKron
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix
open scoped commutatorElement

variable {F : Type*} [Field F] {p : ℕ}

@[expose] noncomputable def dHom :
    SpecialLinearGroup (Fin p) F →* SpecialLinearGroup (Fin (p * p)) F where
  toFun u := ⟨kr 1 (u : Matrix (Fin p) (Fin p) F), by
    rw [det_kr, Matrix.det_one, u.2]; simp⟩
  map_one' := Subtype.ext (by simp [kr_one])
  map_mul' u v := Subtype.ext (by
    show kr 1 ((u : Matrix (Fin p) (Fin p) F) * (v : Matrix (Fin p) (Fin p) F)) =
      kr 1 (u : Matrix (Fin p) (Fin p) F) * kr 1 (v : Matrix (Fin p) (Fin p) F)
    rw [kr_mul, Matrix.one_mul])

theorem coe_dHom (u : SpecialLinearGroup (Fin p) F) :
    ((dHom u : SpecialLinearGroup (Fin (p * p)) F) : Matrix (Fin (p * p)) (Fin (p * p)) F) =
      kr 1 (u : Matrix (Fin p) (Fin p) F) := rfl

theorem comm_mul_central {G : Type*} [Group G] (a b z z' : G) (hz : ∀ g, g * z = z * g)
    (hz' : ∀ g, g * z' = z' * g) : ⁅a * z, b * z'⁆ = ⁅a, b⁆ := by
  simp only [commutatorElement_def, _root_.mul_inv_rev]
  have e : z * z' * z⁻¹ = z' := by rw [hz' z, mul_assoc, mul_inv_cancel, mul_one]
  calc a * z * (b * z') * (z⁻¹ * a⁻¹) * (z'⁻¹ * b⁻¹)
      = a * (z * b) * z' * (z⁻¹ * a⁻¹) * (z'⁻¹ * b⁻¹) := by group
    _ = a * (b * z) * z' * (z⁻¹ * a⁻¹) * (z'⁻¹ * b⁻¹) := by rw [← hz b]
    _ = a * b * (z * z' * z⁻¹) * a⁻¹ * (z'⁻¹ * b⁻¹) := by group
    _ = a * b * z' * a⁻¹ * (z'⁻¹ * b⁻¹) := by rw [e]
    _ = a * b * (z' * a⁻¹) * (z'⁻¹ * b⁻¹) := by group
    _ = a * b * (a⁻¹ * z') * (z'⁻¹ * b⁻¹) := by rw [← hz' a⁻¹]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem eq_top_of_normal_of_not_mem_center (hn : 3 ≤ p)
    {N : Subgroup (SpecialLinearGroup (Fin p) F)} [N.Normal] {a : SpecialLinearGroup (Fin p) F}
    (haN : a ∈ N) (ha : a ∉ Subgroup.center (SpecialLinearGroup (Fin p) F)) : N = ⊤ := by
  have hsimple := (CFSG.LinearGroups.linear_projective_simple (K := F) (n := p) (by omega)
    (Or.inl hn)).2.1
  have hperf : Group.IsPerfect (SpecialLinearGroup (Fin p) F) :=
    CFSG.LinearGroups.special_linear_isPerfect (by omega) (Or.inl hn)
  set π : SpecialLinearGroup (Fin p) F →* ProjectiveSpecialLinearGroup (Fin p) F :=
    QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin p) F)) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hnorm : (N.map π).Normal := Subgroup.Normal.map inferInstance π hπs
  have hmap : N.map π = ⊤ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (N.map π) with h | h
    · exfalso
      apply ha
      have : π a = 1 := by
        have : π a ∈ N.map π := ⟨a, haN, rfl⟩
        rw [h] at this
        exact (Subgroup.mem_bot.1 this)
      exact (QuotientGroup.eq_one_iff a).1 this
    · exact h
  have hdecomp : ∀ g : SpecialLinearGroup (Fin p) F, ∃ n ∈ N, n⁻¹ * g ∈
      Subgroup.center (SpecialLinearGroup (Fin p) F) := by
    intro g
    have : π g ∈ N.map π := hmap ▸ Subgroup.mem_top _
    obtain ⟨n, hn, hng⟩ := this
    refine ⟨n, hn, ?_⟩
    have h1 : π (n⁻¹ * g) = 1 := by rw [map_mul, map_inv, hng, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff (n⁻¹ * g)).1 h1
  have hcl : commutator (SpecialLinearGroup (Fin p) F) ≤ N := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g _ h _
    obtain ⟨n, hn, hz⟩ := hdecomp g
    obtain ⟨n', hn', hz'⟩ := hdecomp h
    have hg : g = n * (n⁻¹ * g) := by group
    have hh : h = n' * (n'⁻¹ * h) := by group
    have hcomm : ⁅g, h⁆ = ⁅n, n'⁆ := by
      rw [hg, hh]
      exact comm_mul_central n n' _ _ (fun x => (Subgroup.mem_center_iff.1 hz x))
        (fun x => (Subgroup.mem_center_iff.1 hz' x))
    rw [hcomm, commutatorElement_def]
    exact N.mul_mem (N.mul_mem (N.mul_mem hn hn') (N.inv_mem hn)) (N.inv_mem hn')
  rw [eq_top_iff, ← hperf.commutator_eq_top]
  exact hcl

@[expose] def blockSub (hpF : (p : F) ≠ 0) (K' : Subgroup (SpecialLinearGroup (Fin (p * p)) F)) :
    Subgroup (SpecialLinearGroup (Fin p) F) where
  carrier := {g | ∃ h ∈ K', (h : Matrix (Fin (p * p)) (Fin (p * p)) F) =
    Mf (g : Matrix (Fin p) (Fin p) F)}
  mul_mem' := by
    rintro g g' ⟨h, hh, hhe⟩ ⟨h', hh', hhe'⟩
    refine ⟨h * h', K'.mul_mem hh hh', ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hhe, hhe',
      Mf_mul hpF]
  one_mem' := ⟨1, K'.one_mem, by simp [Mf_one]⟩
  inv_mem' := by
    rintro g ⟨h, hh, hhe⟩
    refine ⟨h⁻¹, K'.inv_mem hh, ?_⟩
    have h1 : Mf (g : Matrix (Fin p) (Fin p) F) * Mf ((g⁻¹ : SpecialLinearGroup (Fin p) F) :
        Matrix (Fin p) (Fin p) F) = 1 := by
      rw [Mf_mul hpF, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one, Mf_one]
    have h2 : ((h⁻¹ : SpecialLinearGroup (Fin (p * p)) F) : Matrix (Fin (p * p)) (Fin (p * p)) F) *
        (h : Matrix (Fin (p * p)) (Fin (p * p)) F) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    calc ((h⁻¹ : SpecialLinearGroup (Fin (p * p)) F) : Matrix (Fin (p * p)) (Fin (p * p)) F)
        = ((h⁻¹ : SpecialLinearGroup (Fin (p * p)) F) : Matrix (Fin (p * p)) (Fin (p * p)) F) *
          (Mf (g : Matrix (Fin p) (Fin p) F) * Mf ((g⁻¹ : SpecialLinearGroup (Fin p) F) :
            Matrix (Fin p) (Fin p) F)) := by rw [h1, Matrix.mul_one]
      _ = (((h⁻¹ : SpecialLinearGroup (Fin (p * p)) F) : Matrix (Fin (p * p)) (Fin (p * p)) F) *
          (h : Matrix (Fin (p * p)) (Fin (p * p)) F)) * Mf ((g⁻¹ : SpecialLinearGroup (Fin p) F) :
            Matrix (Fin p) (Fin p) F) := by rw [hhe, Matrix.mul_assoc]
      _ = Mf ((g⁻¹ : SpecialLinearGroup (Fin p) F) : Matrix (Fin p) (Fin p) F) := by
          rw [h2, Matrix.one_mul]

theorem Mf_mem_of_noncentral (hp3 : 3 ≤ p) (hpF : (p : F) ≠ 0)
    {K' : Subgroup (SpecialLinearGroup (Fin (p * p)) F)}
    (hd : ∀ u : SpecialLinearGroup (Fin p) F, dHom u ∈ K') {a : SpecialLinearGroup (Fin p) F}
    (ha : a ∉ Subgroup.center (SpecialLinearGroup (Fin p) F)) (haK : a ∈ blockSub hpF K') :
    ∀ g : SpecialLinearGroup (Fin p) F, ∃ h ∈ K', (h : Matrix (Fin (p * p)) (Fin (p * p)) F) =
      Mf (g : Matrix (Fin p) (Fin p) F) := by
  have hnorm : (blockSub hpF K').Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨h, hh, hhe⟩ := hn
    refine ⟨dHom g * h * (dHom g)⁻¹, K'.mul_mem (K'.mul_mem (hd g) hh) (K'.inv_mem (hd g)), ?_⟩
    rw [← map_inv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hhe,
      coe_dHom, coe_dHom, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    exact kr_one_mul_Mf_mul _ _ _ (by rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one])
  have htop := eq_top_of_normal_of_not_mem_center hp3 (N := blockSub hpF K') haK ha
  intro g
  exact (htop ▸ Subgroup.mem_top g : g ∈ blockSub hpF K')

end CFSG.LieType.SeitzGeneration
