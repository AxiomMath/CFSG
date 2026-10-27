module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6FactDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {A B : Type} [Group A] [Group B]

private lemma twoRes_mono {G : Type} [Group G] {K₁ K₂ : Subgroup G} (h : K₁ ≤ K₂) :
    twoRes K₁ ≤ twoRes K₂ := by
  unfold twoRes
  exact Subgroup.closure_mono fun g hg => ⟨h hg.1, hg.2⟩

private lemma pow_eq_self_of_mul_self_eq_one {G : Type} [Group G] {x : G} (hx : x * x = 1)
    {m : ℕ} (hm : Odd m) : x ^ m = x := by
  obtain ⟨k, rfl⟩ := hm
  rw [pow_succ, pow_mul, pow_two, hx, one_pow, one_mul]

theorem map_twoRes (f : A →* B) (h2 : ∀ k ∈ f.ker, k * k = 1) (H : Subgroup A) :
    (twoRes H).map f = twoRes (H.map f) := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).mpr ?_
    rintro g ⟨hgH, hodd⟩
    exact Subgroup.subset_closure
      ⟨Subgroup.mem_map_of_mem f hgH, hodd.of_dvd_nat (orderOf_map_dvd f g)⟩
  · refine (Subgroup.closure_le _).mpr ?_
    rintro b ⟨hbH, hbodd⟩
    obtain ⟨h, hhH, rfl⟩ := Subgroup.mem_map.mp hbH
    obtain ⟨j, hj⟩ := hbodd
    have hker : h ^ (2 * j + 1) ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_pow, ← hj, pow_orderOf_eq_one]
    have hx : h ^ (2 * j + 1) * h ^ (2 * j + 1) = 1 := h2 _ hker
    have hxm : (h ^ (2 * j + 1)) ^ (2 * j + 1) = h ^ (2 * j + 1) :=
      pow_eq_self_of_mul_self_eq_one hx ⟨j, rfl⟩
    have hkey : (h ^ (2 * j + 2)) ^ (2 * j + 1) = 1 := by
      rw [← pow_mul, show 2 * j + 2 = (2 * j + 1) + 1 from rfl, Nat.succ_mul, pow_add,
        pow_mul, hxm, hx]
    have hodd' : Odd (orderOf (h ^ (2 * j + 2))) :=
      Odd.of_dvd_nat ⟨j, rfl⟩ (orderOf_dvd_iff_pow_eq_one.mpr hkey)
    have hf' : f (h ^ (2 * j + 2)) = f h := by
      rw [map_pow, show 2 * j + 2 = (2 * j + 1) + 1 from rfl, pow_succ, ← hj,
        pow_orderOf_eq_one, one_mul]
    have hgen : h ^ (2 * j + 2) ∈ twoRes H :=
      Subgroup.subset_closure ⟨pow_mem hhH _, hodd'⟩
    have hmem := Subgroup.mem_map_of_mem f hgen
    rwa [hf'] at hmem

theorem map_twoPrimeRes (f : A →* B) (h2 : ∀ k ∈ f.ker, k * k = 1) (H : Subgroup A) :
    (twoPrimeRes H).map f = twoPrimeRes (H.map f) := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).mpr ?_
    rintro g ⟨hgH, k, hk⟩
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (hk ▸ orderOf_map_dvd f g)
    exact Subgroup.subset_closure ⟨Subgroup.mem_map_of_mem f hgH, ⟨i, hi⟩⟩
  · refine (Subgroup.closure_le _).mpr ?_
    rintro b ⟨hbH, i, hi⟩
    obtain ⟨h, hhH, rfl⟩ := Subgroup.mem_map.mp hbH
    have hker : h ^ (2 ^ i) ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_pow, ← hi, pow_orderOf_eq_one]
    have hx : h ^ (2 ^ i) * h ^ (2 ^ i) = 1 := h2 _ hker
    have hpow : h ^ (2 ^ (i + 1)) = 1 := by
      rw [pow_succ', two_mul, pow_add, hx]
    obtain ⟨i', -, hi'⟩ :=
      (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_iff_pow_eq_one.mpr hpow)
    exact Subgroup.mem_map_of_mem f (Subgroup.subset_closure ⟨hhH, ⟨i', hi'⟩⟩)

theorem sq_mem_map_cent (f : A →* B) (hz : f.ker ≤ Subgroup.center A)
    (h2 : ∀ k ∈ f.ker, k * k = 1) (H : Subgroup A) (s : A) {b : B}
    (hb : b ∈ H.map f ⊓ Subgroup.centralizer ({f s} : Set B)) :
    b * b ∈ (H ⊓ Subgroup.centralizer ({s} : Set A)).map f := by
  obtain ⟨hbH, hbc⟩ := Subgroup.mem_inf.mp hb
  obtain ⟨h, hhH, rfl⟩ := Subgroup.mem_map.mp hbH
  have hcomm : f s * f h = f h * f s :=
    Subgroup.mem_centralizer_iff.mp hbc (f s) (by simp)
  set c : A := s * h * s⁻¹ * h⁻¹ with hcdef
  have hcker : c ∈ f.ker := by
    rw [MonoidHom.mem_ker, hcdef]
    simp only [map_mul, map_inv]
    rw [hcomm]
    group
  have hc2 : c * c = 1 := h2 c hcker
  have hccent : ∀ g : A, g * c = c * g := fun g =>
    Subgroup.mem_center_iff.mp (hz hcker) g
  have hsq : (c * h) * (c * h) = h * h := by
    calc (c * h) * (c * h) = c * (h * (c * h)) := by group
      _ = c * ((h * c) * h) := by group
      _ = c * ((c * h) * h) := by rw [hccent h]
      _ = (c * c) * (h * h) := by group
      _ = h * h := by rw [hc2]; group
  have hsch : s * (h * h) * s⁻¹ = h * h := by
    have h1 : s * h * s⁻¹ = c * h := by rw [hcdef]; group
    calc s * (h * h) * s⁻¹ = (s * h * s⁻¹) * (s * h * s⁻¹) := by group
      _ = h * h := by rw [h1, hsq]
  have hcent : h * h ∈ Subgroup.centralizer ({s} : Set A) := by
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    calc s * (h * h) = (s * (h * h) * s⁻¹) * s := by group
      _ = (h * h) * s := by rw [hsch]
  have hmem : h * h ∈ H ⊓ Subgroup.centralizer ({s} : Set A) :=
    Subgroup.mem_inf.mpr ⟨mul_mem hhH hhH, hcent⟩
  have hmap := Subgroup.mem_map_of_mem f hmem
  simpa only [map_mul] using hmap

theorem map_twoRes_cent (f : A →* B) (hz : f.ker ≤ Subgroup.center A)
    (h2 : ∀ k ∈ f.ker, k * k = 1) (H : Subgroup A) (s : A) :
    twoRes (H.map f ⊓ Subgroup.centralizer ({f s} : Set B)) =
      (twoRes (H ⊓ Subgroup.centralizer ({s} : Set A))).map f := by
  set K : Subgroup A := H ⊓ Subgroup.centralizer ({s} : Set A) with hK
  set C : Subgroup B := H.map f ⊓ Subgroup.centralizer ({f s} : Set B) with hC
  have hKC : K.map f ≤ C := by
    rintro b hb
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hb
    obtain ⟨hhH, hhc⟩ := Subgroup.mem_inf.mp hh
    have hsh : s * h = h * s := Subgroup.mem_centralizer_iff.mp hhc s (by simp)
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_map_of_mem f hhH, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    calc f s * f h = f (s * h) := (map_mul f s h).symm
      _ = f (h * s) := by rw [hsh]
      _ = f h * f s := map_mul f h s
  refine le_antisymm ?_ ?_
  · refine (Subgroup.closure_le _).mpr ?_
    rintro b ⟨hbC, hbodd⟩
    obtain ⟨j, hj⟩ := hbodd
    have hsq : b * b ∈ K.map f := sq_mem_map_cent f hz h2 H s hbC
    have hpow : b = (b * b) ^ (j + 1) := by
      rw [show b * b = b ^ 2 from (pow_two b).symm, ← pow_mul,
        show 2 * (j + 1) = 2 * j + 2 from by omega,
        show 2 * j + 2 = (2 * j + 1) + 1 from rfl, pow_succ, ← hj, pow_orderOf_eq_one,
        one_mul]
    have hbK : b ∈ K.map f := by
      rw [hpow]
      exact pow_mem hsq (j + 1)
    have hgen : b ∈ twoRes (K.map f) := Subgroup.subset_closure ⟨hbK, ⟨j, hj⟩⟩
    rwa [← map_twoRes f h2 K] at hgen
  · rw [map_twoRes f h2 K]
    exact twoRes_mono hKC

theorem map_xout (f : A →* B) (hz : f.ker ≤ Subgroup.center A)
    (h2 : ∀ k ∈ f.ker, k * k = 1) (H : Subgroup A) (s : A) :
    twoPrimeRes (twoRes (H.map f ⊓ Subgroup.centralizer ({f s} : Set B))) =
      (twoPrimeRes (twoRes (H ⊓ Subgroup.centralizer ({s} : Set A)))).map f := by
  rw [map_twoRes_cent f hz h2 H s]
  exact (map_twoPrimeRes f h2 (twoRes (H ⊓ Subgroup.centralizer ({s} : Set A)))).symm

end CFSG.OddStandard.SmallF3.Omega
