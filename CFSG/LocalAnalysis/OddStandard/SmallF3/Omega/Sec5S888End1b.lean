module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesSign

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

private theorem s888_conj_diff {X : Type} [Group X] {V : Subgroup X} {W : Fin 4 → Subgroup X}
    {ρ : Fin 4 → X} (hVcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hle : ∀ i, W i ≤ V)
    (hrho_mem : ∀ i, ρ i ∈ normalizer (V : Set X))
    (hrho_triv : ∀ i j, i ≠ j → ∀ w ∈ W j, ρ i * w = w * ρ i)
    (i : Fin 4) (w : Fin 4 → X) (hw : ∀ k, w k ∈ W k) :
    (ρ i * (w 0 * w 1 * w 2 * w 3) * (ρ i)⁻¹) * (w 0 * w 1 * w 2 * w 3)⁻¹ =
      (ρ i * w i * (ρ i)⁻¹) * (w i)⁻¹ := by
  letI : CommGroup V := { (inferInstance : Group V) with
    mul_comm := fun a b => Subtype.ext (hVcomm a.1 a.2 b.1 b.2) }
  let wv : Fin 4 → V := fun k => ⟨w k, hle k (hw k)⟩
  let q : V →* V :=
    { toFun := fun v =>
        ⟨ρ i * v.1 * (ρ i)⁻¹, (Subgroup.mem_set_normalizer_iff.mp (hrho_mem i) v.1).mp v.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  have hb : ∀ k, k ≠ i → q (wv k) = wv k := by
    intro k hk
    ext
    show ρ i * w k * (ρ i)⁻¹ = w k
    rw [hrho_triv i k (Ne.symm hk) (w k) (hw k), mul_assoc, mul_inv_cancel, mul_one]
  have hV : q (∏ k, wv k) * (∏ k, wv k)⁻¹ = q (wv i) * (wv i)⁻¹ := by
    rw [map_prod, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    rw [Finset.prod_eq_single i]
    · intro k _ hk
      rw [hb k hk, mul_inv_cancel]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hp : (wv 0 * wv 1 * wv 2 * wv 3) = ∏ k, wv k :=
    (Fin.prod_univ_four wv).symm
  have hV' : q (wv 0 * wv 1 * wv 2 * wv 3) * (wv 0 * wv 1 * wv 2 * wv 3)⁻¹ =
      q (wv i) * (wv i)⁻¹ := by
    rw [hp]
    exact hV
  have := congrArg (Subtype.val) hV'
  simpa [q, wv] using this

private theorem s888_prod_eq_one {X : Type} [Group X] {V : Subgroup X} {W : Fin 4 → Subgroup X}
    {ρ : Fin 4 → X} (hVcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hle : ∀ i, W i ≤ V)
    (hrho_mem : ∀ i, ρ i ∈ normalizer (V : Set X))
    (hrho_inv : ∀ i, ∀ w ∈ W i, ρ i * w * (ρ i)⁻¹ ∈ W i)
    (hrho_triv : ∀ i j, i ≠ j → ∀ w ∈ W j, ρ i * w = w * ρ i)
    (hrho_fpf : ∀ i, ∀ w ∈ W i, w ≠ 1 → ρ i * w * (ρ i)⁻¹ ≠ w)
    (i : Fin 4) (d : Fin 4 → X) (hd : ∀ k, d k ∈ W k)
    (hprod : d 0 * d 1 * d 2 * d 3 = 1) : d i = 1 := by
  have hdiff := s888_conj_diff hVcomm hle hrho_mem hrho_triv i d hd
  have hdiff1 : (ρ i * d i * (ρ i)⁻¹) * (d i)⁻¹ = 1 := by
    have h := hdiff
    rw [hprod] at h
    simpa using h.symm
  have hfix : ρ i * d i * (ρ i)⁻¹ = d i := by
    simpa using (mul_eq_one_iff_eq_inv.mp hdiff1)
  by_contra hne
  exact hrho_fpf i (d i) (hd i) hne hfix

theorem card_V_of_planes {X : Type} [Group X] [Finite X] {V : Subgroup X}
    {W : Fin 4 → Subgroup X} {ρ : Fin 4 → X} (hVcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hle : ∀ i, W i ≤ V) (hcard : ∀ i, Nat.card (W i) = 4)
    (hdecomp : ∀ v ∈ V, ∃ w : Fin 4 → X, (∀ i, w i ∈ W i) ∧ v = w 0 * w 1 * w 2 * w 3)
    (hrho_mem : ∀ i, ρ i ∈ normalizer (V : Set X))
    (hrho_inv : ∀ i, ∀ w ∈ W i, ρ i * w * (ρ i)⁻¹ ∈ W i)
    (hrho_triv : ∀ i j, i ≠ j → ∀ w ∈ W j, ρ i * w = w * ρ i)
    (hrho_fpf : ∀ i, ∀ w ∈ W i, w ≠ 1 → ρ i * w * (ρ i)⁻¹ ≠ w) : Nat.card V = 2 ^ 8 := by
  let Φ : (∀ i, W i) → V := fun w =>
    ⟨w 0 * w 1 * w 2 * w 3,
      V.mul_mem (V.mul_mem (V.mul_mem (hle 0 (w 0).2) (hle 1 (w 1).2))
        (hle 2 (w 2).2)) (hle 3 (w 3).2)⟩
  have hsurj : Function.Surjective Φ := by
    intro v
    obtain ⟨w, hw, hv⟩ := hdecomp v v.2
    refine ⟨fun i => ⟨w i, hw i⟩, ?_⟩
    ext
    simpa [Φ] using hv.symm
  have hinj : Function.Injective Φ := by
    intro w w' h
    funext i
    apply Subtype.ext
    have hval : (w 0 : X) * w 1 * w 2 * w 3 =
        (w' 0 : X) * w' 1 * w' 2 * w' 3 := by
      have := congrArg (Subtype.val) h
      simpa [Φ] using this
    let d : Fin 4 → X := fun k => (w k : X) * ((w' k : X))⁻¹
    have hd : ∀ k, d k ∈ W k := fun k =>
      (W k).mul_mem (w k).2 ((W k).inv_mem (w' k).2)
    have hprod : d 0 * d 1 * d 2 * d 3 = 1 := by
      letI : CommGroup V := { (inferInstance : Group V) with
        mul_comm := fun a b => Subtype.ext (hVcomm a.1 a.2 b.1 b.2) }
      let wv : Fin 4 → V := fun k => ⟨w k, hle k (w k).2⟩
      let wv' : Fin 4 → V := fun k => ⟨w' k, hle k (w' k).2⟩
      have hVeq : (∏ k, wv k) = ∏ k, wv' k := by
        apply Subtype.ext
        simpa [wv, wv', Fin.prod_univ_four] using hval
      have hdv : (∏ k, (wv k * (wv' k)⁻¹)) = 1 := by
        rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, hVeq, mul_inv_cancel]
      have := congrArg (Subtype.val) hdv
      simpa [d, wv, wv', Fin.prod_univ_four] using this
    have hdi : d i = 1 :=
      s888_prod_eq_one hVcomm hle hrho_mem hrho_inv hrho_triv hrho_fpf i d hd hprod
    exact mul_inv_eq_one.mp hdi
  have hbij : Nat.card V = Nat.card (∀ i, W i) :=
    (Nat.card_eq_of_bijective Φ ⟨hinj, hsurj⟩).symm
  rw [hbij, Nat.card_pi]
  simp only [hcard]
  norm_num

end CFSG.OddStandard.SmallF3.Omega
