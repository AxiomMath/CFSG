module

public import CFSG.ClassicalInvolution.AschTight.S1916Local

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1916

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def omegaPrime (K Y' : Subgroup G) : Set (Subgroup G) :=
  CoreAssembly.conjClass K ∪ CoreAssembly.conjClass Y'

theorem conjInvariant_omegaPrime (K Y' : Subgroup G) : ConjInvariant (omegaPrime K Y') := by
  rintro n _ (⟨g, rfl⟩ | ⟨g, rfl⟩)
  · exact Or.inl ⟨n * g, by simp only [conjSub_mul]⟩
  · exact Or.inr ⟨n * g, by simp only [conjSub_mul]⟩

theorem conj_mem_centralizer_iff {z g x : G} :
    x ∈ Subgroup.centralizer ({g * z * g⁻¹} : Set G) ↔
      g⁻¹ * x * g ∈ Subgroup.centralizer ({z} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g⁻¹ * x * g * z = g⁻¹ * (x * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * x) * g := by rw [h]
      _ = z * (g⁻¹ * x * g) := by group
  · intro h
    calc x * (g * z * g⁻¹) = g * ((g⁻¹ * x * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * x * g)) * g⁻¹ := by rw [h]
      _ = g * z * g⁻¹ * x := by group

theorem centralizer_le_normalizer_conjSub {M : Subgroup G} {z : G}
    (hM : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (M : Set G)) (g : G) :
    Subgroup.centralizer ({g * z * g⁻¹} : Set G) ≤
      Subgroup.normalizer ((conjSub g M : Subgroup G) : Set G) := by
  intro x hx
  rw [mem_normalizer_conjSub_iff]
  exact hM (conj_mem_centralizer_iff.mp hx)

theorem conjSub_eq_of_conj_eq {M : Subgroup G} {z g h : G}
    (hM : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (M : Set G))
    (hgh : g * z * g⁻¹ = h * z * h⁻¹) : conjSub g M = conjSub h M := by
  have h1 : h⁻¹ * g ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc h⁻¹ * g * z = h⁻¹ * (g * z * g⁻¹) * g := by group
      _ = h⁻¹ * (h * z * h⁻¹) * g := by rw [hgh]
      _ = z * (h⁻¹ * g) := by group
  have h2 : conjSub (h⁻¹ * g) M = M := mem_normalizer_iff_conjSub_eq.mp (hM h1)
  calc conjSub g M = conjSub h (conjSub (h⁻¹ * g) M) := by rw [← conjSub_mul, mul_inv_cancel_left]
    _ = conjSub h M := by rw [h2]

variable {p f : ℕ} [Fact p.Prime] [Finite G]

theorem not_mem_conjClass_of_centralizes [IsSimpleGroup G] {K : Subgroup G} {z : G}
    (ht : S19R.TightStd p f K z) {Y' : Subgroup G} (hY'z : IsUniqueInvolution Y' z)
    (hKY' : ∀ y ∈ Y', ∀ k ∈ K, ⁅y, k⁆ ∈ oddCoreOf K) : Y' ∉ CoreAssembly.conjClass K := by
  rintro ⟨g, hg⟩
  change conjSub g K = Y' at hg
  have hzK := isUniqueInvolution_of_tight ht.toTightBranch
  have hNC := normalizer_eq_centralizer_of_tight ht.toTightBranch
  have h1 : g * z * g⁻¹ = z := by
    have h2 := hzK.conj g
    rw [hg] at h2
    exact h2.eq hY'z
  have hgN : g ∈ Subgroup.normalizer (K : Set G) := by
    rw [hNC, Subgroup.mem_centralizer_singleton_iff]
    calc g * z = g * z * g⁻¹ * g := by group
      _ = z * g := by rw [h1]
  have hYK : Y' = K := by rw [← hg]; exact mem_normalizer_iff_conjSub_eq.mp hgN
  have hΩ := hypOmegaMod_of_tightD ht
  have hall : ∀ w ∈ K, IsPGroup 2 (Subgroup.zpowers w) → w = 1 ∨ w = z := fun w hw hw2 =>
    hΩ.center_two ht.branch.odd ht.branch.five (CoreAssembly.mem_conjClass_self K) hzK w hw hw2
      (fun y hy => hKY' w (hYK ▸ hw) y hy)
  obtain ⟨Q₀⟩ : Nonempty (Sylow 2 ↥K) := inferInstance
  set R : Subgroup G := (Q₀ : Subgroup ↥K).map K.subtype with hR
  have hRmem : R ∈ RSet (CoreAssembly.conjClass K) :=
    ⟨K, CoreAssembly.mem_conjClass_self K, Q₀, rfl⟩
  have h8 := (exists_ne_comm_of_mem_rSet ht.branch.odd ht.branch.five ht.branch.member hRmem).2
  have hR2 : IsPGroup 2 R := Q₀.isPGroup'.map _
  have hsub : (R : Set G) ⊆ {1, z} := by
    intro w hw
    rcases hall w (Subgroup.map_subtype_le _ hw) (hR2.to_le (Subgroup.zpowers_le.mpr hw)) with
      h | h
    · exact Or.inl h
    · exact Or.inr h
  have := natCard_subgroup_le_two_of_subset hsub
  omega

theorem exists_involution_of_two_dvd {H : Subgroup G} (h2 : 2 ∣ Nat.card H) :
    ∃ y ∈ H, y * y = 1 ∧ y ≠ 1 := by
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have htG : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
  refine ⟨t, t.2, ?_, ?_⟩
  · have := pow_orderOf_eq_one (t : G)
    rwa [htG, pow_two] at this
  · intro h
    rw [h, orderOf_one] at htG
    omega

theorem padicValNat_le_one_of_forall {H : Subgroup G} {z : G}
    (h : ∀ w ∈ H, IsPGroup 2 (Subgroup.zpowers w) → w = 1 ∨ w = z) :
    padicValNat 2 (Nat.card H) ≤ 1 := by
  obtain ⟨P₀⟩ : Nonempty (Sylow 2 ↥H) := inferInstance
  set P : Subgroup G := (P₀ : Subgroup ↥H).map H.subtype with hP
  have hP2 : IsPGroup 2 P := P₀.isPGroup'.map _
  have hsub : (P : Set G) ⊆ {1, z} := by
    intro w hw
    rcases h w (Subgroup.map_subtype_le _ hw) (hP2.to_le (Subgroup.zpowers_le.mpr hw)) with
      h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  have hle := natCard_subgroup_le_two_of_subset hsub
  have hcard : Nat.card P = 2 ^ (Nat.card H).factorization 2 := by
    rw [hP, natCard_eq_of_isSylow2In (isSylow2In_map_sylow H P₀)]
  rw [hcard] at hle
  rw [← Nat.factorization_def _ Nat.prime_two]
  by_contra hlt
  push Not at hlt
  have : 2 ^ 2 ≤ 2 ^ (Nat.card H).factorization 2 := Nat.pow_le_pow_right (by norm_num) hlt
  omega

theorem omega4_base [IsSimpleGroup G] {K : Subgroup G} {z : G} (ht : S19R.TightStd p f K z)
    {Y' : Subgroup G} (hY'N : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (Y' : Set G))
    (hY'z : Y' ≤ Subgroup.centralizer ({z} : Set G))
    (hKY' : ∀ y ∈ Y', ∀ k ∈ K, ⁅y, k⁆ ∈ oddCoreOf K) :
    padicValNat 2 (Nat.card ↥(K ⊓ Y')) ≤ 1 ∧ ⁅K, Y'⁆ ≤ oddCoreOf K ⊓ oddCoreOf Y' := by
  have hzK := isUniqueInvolution_of_tight ht.toTightBranch
  have hNC := normalizer_eq_centralizer_of_tight ht.toTightBranch
  have hKz : K ≤ Subgroup.centralizer ({z} : Set G) := le_centralizer_of_tight ht.toTightBranch
  have hΩ := hypOmegaMod_of_tightD ht
  refine ⟨padicValNat_le_one_of_forall (z := z) fun w hw hw2 => ?_, ?_⟩
  · exact hΩ.center_two ht.branch.odd ht.branch.five (CoreAssembly.mem_conjClass_self K) hzK w
      hw.1 hw2 (fun y hy => hKY' w hw.2 y hy)
  · have hcK : ∀ k ∈ K, ∀ y ∈ Y', ⁅k, y⁆ ∈ oddCoreOf K := by
      intro k hk y hy
      have h1 := (oddCoreOf K).inv_mem (hKY' y hy k hk)
      rwa [commutatorElement_inv] at h1
    have hcY : ∀ k ∈ K, ∀ y ∈ Y', ⁅k, y⁆ ∈ Y' := by
      intro k hk y hy
      rw [commutatorElement_def]
      exact Y'.mul_mem ((Subgroup.mem_normalizer_iff.mp (hY'N (hKz hk)) y).mp hy) (Y'.inv_mem hy)
    have hle : oddCoreOf K ⊓ Y' ≤ oddCoreOf Y' := by
      refine le_oddCoreOf_of_odd inf_le_right (fun y hy => ?_) ?_
      · have hyN : y ∈ Subgroup.normalizer (K : Set G) := hNC ▸ hY'z hy
        exact mem_normalizer_inf (mem_normalizer_oddCoreOf_of_mem_normalizer hyN)
          (Subgroup.le_normalizer hy)
      · have hodd := oddCoreOf_odd_natCard K
        exact hodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
    refine Subgroup.commutator_le.mpr fun k hk y hy =>
      ⟨hcK k hk y hy, hle ⟨hcK k hk y hy, hcY k hk y hy⟩⟩

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1916
