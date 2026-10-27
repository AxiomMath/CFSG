module

public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Sp6B
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinE4tModel
public import CFSG.Models.Blueprint
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Exits
public import Certificates.Certificate393004

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3.TL4

namespace TwinDisc

namespace ExitE4

open CFSG.EvenSmallLie.Sp6 CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Co3
  CFSG.ClassicalInvolution.Q3.TL4.E4Sp6 CFSG.ClassicalInvolution.Q3.TL4.E4C
  CFSG.ClassicalInvolution.Q3.TL4.E4Sp6Data

theorem centSq_parts :
    ∀ g ∈ enumeration sp6CentQ2, centSqStep (rho ()) (jay ())
      (twin () * rho () * (twin ())⁻¹) (twin () * jay () * (twin ())⁻¹) g = false := by
  have h := Certificates.certificate393004
  simp only [centSqCheck, tab_eq, List.all_eq_true, Bool.not_eq_true'] at h
  exact h

theorem sp62_cent_sq
    {M : Type} [Group M] [Finite M] (hM : CFSG.Blueprint.LieModel M .PSp 3 2 1)
    {K : Subgroup M} {s : M} (hq : Nonempty (↥K ≃* QuaternionGroup 2))
    (hinv : IsUniqueInvolution K s)
    (htw : ∀ c ∈ Subgroup.centralizer ({s} : Set M), conjSub c K = K ∨
      ∀ x ∈ K, ∀ y ∈ conjSub c K, x * y = y * x)
    {K' : Subgroup M} (hK' : K' ∈ CoreAssembly.conjClass K) (hne : K' ≠ K)
    (hle : K' ≤ Subgroup.normalizer (K : Set M)) {q : M} (hqK : ∀ k ∈ K, q * k = k * q)
    (hqK' : ∀ k ∈ K', q * k = k * q) : q * q = 1 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_co3X36 hM
  obtain ⟨φ, hφ, hrange, hKφ⟩ := TwinThmE.exists_emb_of_ident e
    (fun K s hd => E4Sp6.ident_ambient hd) hq hinv htw
  have hmem : ∀ m, φ m ∈ co3X36 := fun m => hrange ▸ ⟨m, rfl⟩
  have hs : φ s = sp6Rep2 :=
    E4Sp6.eq_rep_of_isUniqueInvolution (hKφ ▸ Vtx.isUniqueInvolution_map φ hφ hinv)
  obtain ⟨y, rfl⟩ := hK'
  have hK'φ : (conjSub y K).map φ = conjSub (φ y) K0 := by
    rw [AscQuot.map_conjSub, hKφ]
  have hBK : conjSub (φ y) K0 = conjSub (twin ()) K0 := by
    refine E4Sp6.eq_twin_of_le_normalizer (hmem y) (fun h1 => hne ?_) ?_
    · apply Subgroup.map_injective hφ
      rw [hK'φ, h1, hKφ]
    · rw [← hK'φ, ← hKφ]
      exact (Vtx.map_le_normalizer_map_iff φ hφ).mpr hle
  have hρ : rho () ∈ K0 := Subgroup.subset_closure (Set.mem_insert _ _)
  have hj : jay () ∈ K0 := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hK0 : ∀ z ∈ K0, φ q * z = z * φ q := fun z hz => by
    rw [← hKφ] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    rw [← map_mul, ← map_mul, hqK a ha]
  have hK1 : ∀ z ∈ conjSub (twin ()) K0, φ q * z = z * φ q := fun z hz => by
    rw [← hBK, ← hK'φ] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    rw [← map_mul, ← map_mul, hqK' a ha]
  have hqr : φ q * sp6Rep2 = sp6Rep2 * φ q := by
    rw [← hs]
    exact hK0 _ (hKφ ▸ Subgroup.mem_map_of_mem φ hinv.mem)
  have hQv := (E4Sp6.cover_of_centCheck (by rw [sp6CentQ2, certificate_originalSubgroup])
    exists_word_of_mem_map sp6_cent_check₂).1
  have hqQ : φ q ∈ enumeration sp6CentQ2 := by
    rw [mem_enumeration_iff _ hQv, ← sp6_cent_spec₂.1, sp6Q_originalSubgroup]
    exact mem_centralizerIn.2 ⟨hmem q, hqr⟩
  have hρ1 : twin () * rho () * (twin ())⁻¹ ∈ conjSub (twin ()) K0 := conj_mem_conjSub hρ
  have hj1 : twin () * jay () * (twin ())⁻¹ ∈ conjSub (twin ()) K0 := conj_mem_conjSub hj
  have hstep := centSq_parts (φ q) hqQ
  by_contra hq2
  have hq2' : ¬ φ q * φ q = 1 := fun h1 => hq2 (hφ (by rw [map_mul, h1, map_one]))
  have h1 : decide (φ q * rho () = rho () * φ q) = true := decide_eq_true (hK0 _ hρ)
  have h2 : decide (φ q * jay () = jay () * φ q) = true := decide_eq_true (hK0 _ hj)
  have h3 : decide (φ q * (twin () * rho () * (twin ())⁻¹) =
      (twin () * rho () * (twin ())⁻¹) * φ q) = true := decide_eq_true (hK1 _ hρ1)
  have h4 : decide (φ q * (twin () * jay () * (twin ())⁻¹) =
      (twin () * jay () * (twin ())⁻¹) * φ q) = true := decide_eq_true (hK1 _ hj1)
  have h5 : (!decide (φ q * φ q = 1)) = true := by
    rw [Bool.not_eq_true', decide_eq_false_iff_not]
    exact hq2'
  unfold centSqStep at hstep
  rw [h1, h2, h3, h4, h5] at hstep
  exact absurd hstep (by decide)

theorem sp62_aut_sq
    {M : Type} [Group M] [Finite M] (hM : CFSG.Blueprint.LieModel M .PSp 3 2 1)
    {K : Subgroup M} {s : M} (hq : Nonempty (↥K ≃* QuaternionGroup 2))
    (hinv : IsUniqueInvolution K s)
    (htw : ∀ c ∈ Subgroup.centralizer ({s} : Set M), conjSub c K = K ∨
      ∀ x ∈ K, ∀ y ∈ conjSub c K, x * y = y * x)
    {K' : Subgroup M} (hK' : K' ∈ CoreAssembly.conjClass K) (hne : K' ≠ K)
    (hle : K' ≤ Subgroup.normalizer (K : Set M)) (β : MulAut M) (hβK : ∀ k ∈ K, β k = k)
    (hβK' : ∀ k ∈ K', β k = k) : β * β = 1 := by
  have hinn : CFSG.ComponentClassification.OuterAutomorphisms.inner M = ⊤ :=
    inner_eq_top_of_lieModel_psp_three_two
      (CFSG.Models.LieModel.of_blueprint_of_ne_zero (by norm_num) hM)
  obtain ⟨c, hc⟩ : β ∈ (MulAut.conj : M →* MulAut M).range := by
    have : β ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner M := hinn ▸ Subgroup.mem_top β
    exact this
  have hcomm : ∀ {L : Subgroup M}, (∀ k ∈ L, β k = k) → ∀ k ∈ L, c * k = k * c := by
    intro L hL k hk
    have h1 := hL k hk
    rw [← hc, MulAut.conj_apply] at h1
    calc c * k = c * k * c⁻¹ * c := by group
      _ = k * c := by rw [h1]
  have h2 := sp62_cent_sq hM hq hinv htw hK' hne hle (hcomm hβK) (hcomm hβK')
  rw [← hc, ← map_mul, h2, map_one]

end ExitE4

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
