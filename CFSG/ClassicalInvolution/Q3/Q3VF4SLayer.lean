module

public import CFSG.ClassicalInvolution.Q3.Q3VF4SRelabel
public import CFSG.ClassicalInvolution.Q3.Q3E8BCent
public import CFSG.ClassicalInvolution.Q3.Q3WAPow
public import CFSG.ClassicalInvolution.RouteD.TypeF4PatternLayer
public import Certificates.Certificate3951
public import Certificates.Certificate3952

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3V.F4S

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.NonClassical CFSG.ClassicalInvolution.Q3.Q3V.Lift
  CFSG.ClassicalInvolution.Q3.Q3W
open CFSG.ClassicalInvolution.Models.SymplecticPairs (planeGroup IsHyperbolicPlane stdPlane
  planeGroup_stdPlane isHyperbolicPlane_stdPlane longBlock longInv)

local notation "F₃" => GaloisField 3 1


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {K : Subgroup G}

theorem layerKerCop {c : CCoreR 3 Ω K z} (l : LayerR c) :
    ∀ w ∈ l.Θ.ker, ¬ 3 ∣ orderOf w := fun w hw =>
  Q3Z.orderOf_not_dvd_three_of_center_sp (by norm_num) (l.ker_le hw)

theorem exists_visible_equiv_f4_3 {c : CCoreR 3 Ω K z} (l : LayerR c) {w₀ : G}
    (hw₀ : IsClassicalMember3 ((planeGroup (stdPlane F₃ 3 2)).map l.Θ) w₀) :
    ∃ φ : {N : Subgroup G // N ∈ centralizingMembers Ω {z * w₀, z}} ≃ F4Layer 3 1,
      (∀ N N', Commutes N.1 N'.1 ↔ F4Layer.rel (φ N) (φ N')) ∧
        ∀ h : K ∈ centralizingMembers Ω {z * w₀, z}, φ ⟨K, h⟩ = none := by
  classical
  have hψw : w₀ = l.Θ (longInv F₃ 3 2) :=
    eq_map_longInv_of_involution l.ker_le hw₀.mem hw₀.orderOf_eq_two
  have hKz : K ∈ centralizingMembers Ω {z} := c.hKz
  have hKj₀ : Commutes K ((planeGroup (stdPlane F₃ 3 2)).map l.Θ) :=
    l.commutes_K_map (planeGroup (stdPlane F₃ 3 2))
  have hKvis : K ∈ centralizingMembers Ω {z * w₀, z} := by
    rw [centralizingMembers_mul_iff, mem_centralizingMembers_pair]
    exact ⟨hKz, le_centralizer_of_commutes hKj₀ hw₀.mem⟩
  have hpow : ∀ R ∈ planeGroupSet F₃ 3, Pow3 R := by
    rintro _ ⟨P, hP, rfl⟩
    exact pow3_planeGroupR (by norm_num) hP
  have hcent : ∀ R ∈ planeGroupSet F₃ 3,
      (R.map l.Θ ≤ Subgroup.centralizer ({w₀} : Set G) ↔
        R ≤ Subgroup.centralizer ({longInv F₃ 3 2} : Set (StatedSp 3 F₃))) := by
    intro R hR
    rw [hψw]
    exact (le_centralizer_iff_map3 l.Θ l.ker_le (layerKerCop l) (hpow R hR) (longInv F₃ 3 2)).symm
  have hmem : ∀ ρ : {R : Subgroup (StatedSp 3 F₃) //
      R ∈ planeGroupSet F₃ 3 ∧
        R ≤ Subgroup.centralizer ({longInv F₃ 3 (Fin.last 2)} : Set (StatedSp 3 F₃))},
      ρ.1.map l.Θ ∈ centralizingMembers Ω {z * w₀, z} := by
    rintro ⟨R, hR, hRc⟩
    obtain ⟨P, hP, rfl⟩ := hR
    rw [centralizingMembers_mul_iff, mem_centralizingMembers_pair]
    exact ⟨(l.plane P hP).1, (hcent _ ⟨P, hP, rfl⟩).mpr hRc⟩
  let ι : F4Layer 3 1 → {N : Subgroup G // N ∈ centralizingMembers Ω {z * w₀, z}} :=
    fun a => Option.elim a ⟨K, hKvis⟩ fun ρ => ⟨ρ.1.map l.Θ, hmem ρ⟩
  have hne : ∀ ρ : {R : Subgroup (StatedSp 3 F₃) //
      R ∈ planeGroupSet F₃ 3 ∧
        R ≤ Subgroup.centralizer ({longInv F₃ 3 (Fin.last 2)} : Set (StatedSp 3 F₃))},
      ρ.1.map l.Θ ≠ K := by
    rintro ⟨R, hR, hRc⟩
    obtain ⟨P, hP, rfl⟩ := hR
    exact l.map_planeGroup_ne
  have hinj : Function.Injective ι := by
    intro a b hab
    rcases a with _ | ρ <;> rcases b with _ | ρ'
    · rfl
    · exact absurd (congrArg Subtype.val hab).symm (hne ρ')
    · exact absurd (congrArg Subtype.val hab) (hne ρ)
    · have h : ρ.1.map l.Θ = ρ'.1.map l.Θ := congrArg Subtype.val hab
      exact congrArg some (Subtype.ext (eq_of_map_eq_of_pow3 l.Θ l.ker_le (layerKerCop l)
        (hpow _ ρ.2.1) (hpow _ ρ'.2.1) h))
  have hsurj : Function.Surjective ι := by
    rintro ⟨N, hN⟩
    rw [centralizingMembers_mul_iff, mem_centralizingMembers_pair] at hN
    obtain ⟨hNz, hNw⟩ := hN
    by_cases hNK : N = K
    · exact ⟨none, Subtype.ext hNK.symm⟩
    · obtain ⟨P, hP, hNP⟩ := l.exists_plane_of_ne hNz hNK
      have hRP : planeGroup P ∈ planeGroupSet F₃ 3 := ⟨P, hP, rfl⟩
      have hρc : planeGroup P ≤
          Subgroup.centralizer ({longInv F₃ 3 (Fin.last 2)} : Set (StatedSp 3 F₃)) :=
        (hcent _ hRP).mp (hNP ▸ hNw)
      refine ⟨some ⟨planeGroup P, hRP, hρc⟩, Subtype.ext ?_⟩
      exact hNP.symm
  have key : ∀ a b : F4Layer 3 1, Commutes (ι a).1 (ι b).1 ↔ F4Layer.rel a b := by
    intro a b
    rcases a with _ | ρ <;> rcases b with _ | ρ'
    · exact iff_false_intro (not_commutes_self3 c.hz)
    · exact iff_true_intro (l.commutes_K_map ρ'.1)
    · exact iff_true_intro (l.commutes_K_map ρ.1).symm
    · show Commutes (ρ.1.map l.Θ) (ρ'.1.map l.Θ) ↔ Commutes ρ.1 ρ'.1
      obtain ⟨P, hP, hρ⟩ := ρ.2.1
      obtain ⟨P', hP', hρ'⟩ := ρ'.2.1
      rw [hρ, hρ']
      rw [Frame.commutes_map_planeGroup_iff (by norm_num) l.ker_le hP hP']
      exact (Q3Z.commute_planeGroup_iff Q3Z.gf3_two_ne_zero (by norm_num) hP hP').symm
  refine ⟨(Equiv.ofBijective ι ⟨hinj, hsurj⟩).symm, fun N N' => ?_, fun h => ?_⟩
  · have h1 : ι ((Equiv.ofBijective ι ⟨hinj, hsurj⟩).symm N) = N :=
      (Equiv.ofBijective ι ⟨hinj, hsurj⟩).apply_symm_apply N
    have h2 : ι ((Equiv.ofBijective ι ⟨hinj, hsurj⟩).symm N') = N' :=
      (Equiv.ofBijective ι ⟨hinj, hsurj⟩).apply_symm_apply N'
    have := key ((Equiv.ofBijective ι ⟨hinj, hsurj⟩).symm N)
      ((Equiv.ofBijective ι ⟨hinj, hsurj⟩).symm N')
    rwa [h1, h2] at this
  · exact (Equiv.symm_apply_eq _).mpr (Subtype.ext rfl)

end CFSG.ClassicalInvolution.Q3.Q3V.F4S
