module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelS6Abs

open scoped commutatorElement

theorem commutator_le_of_card_eq_three_mul {G : Type*} [Group G] [Finite G]
    {N K : Subgroup G} [K.Normal] (hKN : K ≤ N) (hc : Nat.card N = 3 * Nat.card K) :
    ⁅N, N⁆ ≤ K := by
  have hcard : Nat.card (K.subgroupOf N) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKN).toEquiv
  haveI : Nonempty K := ⟨1⟩
  have hidx : (K.subgroupOf N).index = 3 := by
    have h := Subgroup.card_mul_index (K.subgroupOf N)
    rw [hcard, hc, mul_comm 3 (Nat.card K)] at h
    exact Nat.mul_left_cancel (Nat.card_pos (α := K)) h
  have hquot : Nat.card (N ⧸ K.subgroupOf N) = 3 := by
    simpa only [Subgroup.index] using hidx
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsCyclic (N ⧸ K.subgroupOf N) := isCyclic_of_prime_card hquot
  have hcomm : IsMulCommutative (N ⧸ K.subgroupOf N) := inferInstance
  have hle : _root_.commutator N ≤ K.subgroupOf N :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hcomm
  have hmap : ⁅N, N⁆ ≤ K ⊓ N := by
    have h := Subgroup.map_mono (f := N.subtype) hle
    rwa [Subgroup.map_subtype_commutator, Subgroup.subgroupOf_map_subtype] at h
  exact hmap.trans inf_le_left

theorem ker_le_of_normal {G : Type*} [Group G] (π : G →* Equiv.Perm (Fin 6))
    (hπ : Function.Surjective π) {T K M : Subgroup G} [M.Normal]
    (hT : T ≤ ⁅T, T⁆) (hNT : π.ker ≤ T) (hTA : T.map π ≤ alternatingGroup (Fin 6))
    (hNK : ⁅π.ker, π.ker⁆ ≤ K) (hKM : K ≤ M) (hM : ¬ M ≤ π.ker) : π.ker ≤ M := by
  haveI hMnorm : (M.map π).Normal := Subgroup.Normal.map ‹M.Normal› π hπ
  have hMnt : Nontrivial (M.map π) := by
    rw [Subgroup.nontrivial_iff_exists_ne_one]
    obtain ⟨m, hmM, hm⟩ := Set.not_subset.mp hM
    exact ⟨π m, Subgroup.mem_map_of_mem π hmM, by simpa [MonoidHom.mem_ker] using hm⟩
  have hAlt : alternatingGroup (Fin 6) ≤ M.map π :=
    Equiv.Perm.alternatingGroup_le_of_normal (α := Fin 6) (by simp) hMnt
  have hTM : T.map π ≤ M.map π := hTA.trans hAlt
  have hTTM : ⁅T, T⁆ ≤ M := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨m₁, hm₁M, hm₁eq⟩ := Subgroup.mem_map.mp (hTM (Subgroup.mem_map_of_mem π hx))
    obtain ⟨m₂, hm₂M, hm₂eq⟩ := Subgroup.mem_map.mp (hTM (Subgroup.mem_map_of_mem π hy))
    set n₁ : G := m₁⁻¹ * x with hn₁
    set n₂ : G := m₂⁻¹ * y with hn₂
    have hn₁ker : n₁ ∈ π.ker := by
      rw [hn₁, MonoidHom.mem_ker, map_mul, map_inv, hm₁eq, inv_mul_cancel]
    have hn₂ker : n₂ ∈ π.ker := by
      rw [hn₂, MonoidHom.mem_ker, map_mul, map_inv, hm₂eq, inv_mul_cancel]
    have hxe : x = m₁ * n₁ := by rw [hn₁]; group
    have hye : y = m₂ * n₂ := by rw [hn₂]; group
    have hm₁φ : QuotientGroup.mk' M m₁ = 1 := (QuotientGroup.eq_one_iff (N := M) m₁).mpr hm₁M
    have hm₂φ : QuotientGroup.mk' M m₂ = 1 := (QuotientGroup.eq_one_iff (N := M) m₂).mpr hm₂M
    have hφx : QuotientGroup.mk' M x = QuotientGroup.mk' M n₁ := by
      rw [hxe, map_mul, hm₁φ, one_mul]
    have hφy : QuotientGroup.mk' M y = QuotientGroup.mk' M n₂ := by
      rw [hye, map_mul, hm₂φ, one_mul]
    have h1 : QuotientGroup.mk' M ⁅x, y⁆ = 1 := by
      rw [map_commutatorElement, hφx, hφy, ← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff (N := M) ⁅n₁, n₂⁆).mpr
        (hKM (hNK (Subgroup.commutator_mem_commutator hn₁ker hn₂ker)))
    exact (QuotientGroup.eq_one_iff (N := M) ⁅x, y⁆).mp h1
  exact hNT.trans (hT.trans hTTM)

theorem card_eq_of_ker_le {G : Type*} [Group G] [Finite G] (π : G →* Equiv.Perm (Fin 6))
    (hπ : Function.Surjective π) {M : Subgroup G} [M.Normal] (hM : π.ker ≤ M) :
    Nat.card M = Nat.card π.ker ∨ Nat.card M = 360 * Nat.card π.ker ∨
      Nat.card M = 720 * Nat.card π.ker := by
  let X : Subgroup (Equiv.Perm (Fin 6)) := M.map π
  have hXN : X.Normal := Subgroup.Normal.map (inferInstance : M.Normal) π hπ
  have hcard : Nat.card π.ker * Nat.card X = Nat.card M := by
    have hidx : (π.ker.subgroupOf M).index = Nat.card X := by
      change π.ker.relIndex M = Nat.card X
      rw [Subgroup.relIndex_ker]
    rw [← hidx, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM).toEquiv]
    exact Subgroup.card_mul_index (H := π.ker.subgroupOf M)
  by_cases hXbot : X = ⊥
  ·
    left
    rw [← hcard, hXbot, Subgroup.card_bot, mul_one]
  ·
    right
    have hnt : Nontrivial X := (Subgroup.nontrivial_iff_ne_bot X).mpr hXbot
    haveI : X.Normal := hXN
    have hA6 : alternatingGroup (Fin 6) ≤ X :=
      Equiv.Perm.alternatingGroup_le_of_normal (α := Fin 6)
        (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num) hnt
    have hA6card : Nat.card (alternatingGroup (Fin 6)) = 360 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    have hdvd360 : 360 ∣ Nat.card X := by
      have := Subgroup.card_dvd_of_le hA6
      rwa [hA6card] at this
    have h720 : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
      rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    have hdvd720 : Nat.card X ∣ 720 := by
      have := Subgroup.card_subgroup_dvd_card X
      rwa [h720] at this
    have hX : Nat.card X = 360 ∨ Nat.card X = 720 := by
      obtain ⟨k, hk⟩ := hdvd360
      have hk_dvd : k ∣ 2 := by
        have h' : Nat.card X ∣ 360 * 2 := by
          rw [show (720 : ℕ) = 360 * 2 by norm_num] at hdvd720
          exact hdvd720
        rw [← mul_dvd_mul_iff_left (show (360 : ℕ) ≠ 0 by norm_num), ← hk]
        exact h'
      rcases (Nat.dvd_prime Nat.prime_two).mp hk_dvd with hk1 | hk2
      · left; rw [hk, hk1, mul_one]
      · right; rw [hk, hk2]
    rcases hX with hX | hX
    · left; rw [← hcard, hX, mul_comm]
    · right; rw [← hcard, hX, mul_comm]

theorem card_eq_of_le_ker {G : Type*} [Group G] [Finite G] {N K M : Subgroup G}
    (hKM : K ≤ M) (hMN : M ≤ N) (hc : Nat.card N = 3 * Nat.card K) :
    Nat.card M = Nat.card K ∨ Nat.card M = Nat.card N := by
  have hKdvdM : Nat.card K ∣ Nat.card M := Subgroup.card_dvd_of_le hKM
  have hMdvdN : Nat.card M ∣ Nat.card N := Subgroup.card_dvd_of_le hMN
  obtain ⟨k, hk⟩ := hKdvdM
  have hk3 : k ∣ 3 := by
    have h' : Nat.card M ∣ Nat.card K * 3 := by
      rw [mul_comm (Nat.card K) 3, ← hc]
      exact hMdvdN
    have h : Nat.card K * k ∣ Nat.card K * 3 := by
      rw [← hk]
      exact h'
    exact (mul_dvd_mul_iff_left (Nat.card_pos.ne' : Nat.card K ≠ 0)).mp h
  rcases (Nat.dvd_prime Nat.prime_three).mp hk3 with hk1 | hk3
  · left; rw [hk, hk1, mul_one]
  · right; rw [hk, hk3, hc, mul_comm]

theorem card_normal_cases {G : Type*} [Group G] [Finite G] (π : G →* Equiv.Perm (Fin 6))
    (hπ : Function.Surjective π) {T K M : Subgroup G} [K.Normal] [M.Normal]
    (hT : T ≤ ⁅T, T⁆) (hNT : π.ker ≤ T) (hTA : T.map π ≤ alternatingGroup (Fin 6))
    (hKN : K ≤ π.ker) (hc : Nat.card π.ker = 3 * Nat.card K) (hKM : K ≤ M) :
    (M ≤ π.ker ∨ π.ker ≤ M) ∧
      (Nat.card M = Nat.card K ∨ Nat.card M = 3 * Nat.card K ∨
        Nat.card M = 3 * Nat.card K * 360 ∨ Nat.card M = 3 * Nat.card K * 720) := by
  by_cases h : M ≤ π.ker
  · refine ⟨Or.inl h, ?_⟩
    rcases card_eq_of_le_ker hKM h hc with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl (h1.trans hc))
  · have hker : π.ker ≤ M :=
      ker_le_of_normal π hπ hT hNT hTA (commutator_le_of_card_eq_three_mul hKN hc) hKM h
    refine ⟨Or.inr hker, ?_⟩
    rcases card_eq_of_ker_le π hπ hker with h1 | h1 | h1
    · exact Or.inr (Or.inl (h1.trans hc))
    · exact Or.inr (Or.inr (Or.inl (by rw [h1, hc]; ring)))
    · exact Or.inr (Or.inr (Or.inr (by rw [h1, hc]; ring)))

theorem eq_bot_of_normal_isPGroup {c : Fin 6} {Y : Subgroup (Equiv.Perm (Fin 6))}
    (hY2 : IsPGroup 2 Y) (hYc : ∀ y ∈ Y, y c = c)
    (hYn : ∀ s : Equiv.Perm (Fin 6), s c = c → ∀ y ∈ Y, s * y * s⁻¹ ∈ Y) : Y = ⊥ := by
  let α := { x : Fin 6 // x ≠ c }
  let φ : Equiv.Perm α →* Equiv.Perm (Fin 6) :=
    Equiv.Perm.ofSubtype (p := fun x : Fin 6 => x ≠ c)
  let Y' : Subgroup (Equiv.Perm α) := Y.comap φ
  have hφinj : Function.Injective φ := by
    change Function.Injective (Equiv.Perm.ofSubtype (p := fun x : Fin 6 => x ≠ c))
    exact Equiv.Perm.ofSubtype_injective
  have hY'2 : IsPGroup 2 Y' := hY2.comap_of_injective φ hφinj
  haveI hY'norm : Y'.Normal :=
    ⟨fun x hx s => by
      change φ (s * x * s⁻¹) ∈ Y
      rw [map_mul, map_mul, map_inv]
      refine hYn (φ s) ?_ (φ x) ?_
      · change Equiv.Perm.ofSubtype s c = c
        exact Equiv.Perm.ofSubtype_apply_of_not_mem s (by simp)
      · change φ x ∈ Y
        exact hx⟩
  have hcardα : Nat.card α = 5 := by
    rw [Nat.card_eq_fintype_card]
    rw [show Fintype.card α = Fintype.card { x : Fin 6 // ¬(x = c) } from rfl]
    rw [Fintype.card_subtype_compl (fun x : Fin 6 => x = c), Fintype.card_subtype_eq,
      Fintype.card_fin]
  haveI : Nontrivial α := by
    refine Fintype.one_lt_card_iff_nontrivial.mp ?_
    rw [← Nat.card_eq_fintype_card, hcardα]
    norm_num
  have hY'bot : Y' = ⊥ := by
    by_contra hne
    have hnt : Nontrivial Y' := (Subgroup.nontrivial_iff_ne_bot Y').mpr hne
    have hle : alternatingGroup α ≤ Y' :=
      Equiv.Perm.alternatingGroup_le_of_normal (by omega) hnt
    have h2 : IsPGroup 2 (alternatingGroup α) := hY'2.to_le hle
    have hcard60 : Nat.card (alternatingGroup α) = 60 := by
      rw [nat_card_alternatingGroup, hcardα]
      decide
    obtain ⟨n, hn⟩ := h2.exists_card_dvd_pow
    rw [hcard60] at hn
    have h3 : (3 : ℕ) ∣ 2 ^ n := dvd_trans (by norm_num) hn
    have h32 : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by decide) h3
    norm_num at h32
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  have hyc : y c = c := hYc y hy
  have hmem : y ∈ φ.range := by
    change y ∈ (Equiv.Perm.ofSubtype (p := fun x : Fin 6 => x ≠ c)).range
    rw [Equiv.Perm.mem_range_ofSubtype_iff]
    intro a ha
    simp only [Set.mem_ofPred_eq]
    rintro rfl
    exact (Equiv.Perm.mem_support.mp ha) hyc
  obtain ⟨x, hx⟩ := hmem
  rw [← hx]
  have hxY' : x ∈ Y' := by
    change φ x ∈ Y
    rw [hx]
    exact hy
  rw [hY'bot, Subgroup.mem_bot] at hxY'
  rw [hxY', map_one]

theorem card_stabilizer (c : Fin 6) :
    Nat.card (MulAction.stabilizer (Equiv.Perm (Fin 6)) c) = 120 := by
  have hmul := Subgroup.card_mul_index (MulAction.stabilizer (Equiv.Perm (Fin 6)) c)
  have hidx : (MulAction.stabilizer (Equiv.Perm (Fin 6)) c).index = 6 := by
    rw [MulAction.index_stabilizer_of_transitive]
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  have hcard : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  rw [hidx, hcard] at hmul
  omega

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelS6Abs
