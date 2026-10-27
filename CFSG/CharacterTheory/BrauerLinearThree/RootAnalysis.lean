module

public import CFSG.CharacterTheory.BrauerLinearThree.RootAnalysisCore

public section

namespace CFSG.BrauerLinearThree

open Matrix CFSG.DesarguesianPlanes

variable {G : Type} [Group G] {F : Type} [Field F] [Finite F] {Z : Subgroup (GL (Fin 2) F)}
  [Z.Normal] {J : G} (φ : Subgroup.centralizer ({J} : Set G) ≃* GL (Fin 2) F ⧸ Z)
  (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F) (hZodd : Odd (Nat.card Z))
  (h2 : (2 : F) ≠ 0) (hJ : orderOf J = 2)

section RootFacts

variable {Y : G} (hY₁ : Y⁻¹ * J * Y = invJ₁ φ) (hY₂ : Y⁻¹ * invJ₁ φ * Y = invJ₂ φ)

omit [Finite F] in
theorem rootSub_01_le_centralizer : rootSub φ Y 0 1 ≤ Subgroup.centralizer {J} := fun _ hx =>
  Subgroup.mem_centralizer_singleton_iff.mpr (commute_J_of_mem_rootX₁ hx).symm

omit [Finite F] in
include hY₁ in
theorem rootSub_12_le_centralizer : rootSub φ Y 1 2 ≤ Subgroup.centralizer {invJ₁ φ} :=
  fun _ hx => Subgroup.mem_centralizer_singleton_iff.mpr (commute_invJ₁_of_mem hY₁ (Or.inl hx)).symm

omit [Finite F] in
include hY₁ in
theorem rootSub_21_le_centralizer : rootSub φ Y 2 1 ≤ Subgroup.centralizer {invJ₁ φ} :=
  fun _ hx => Subgroup.mem_centralizer_singleton_iff.mpr (commute_invJ₁_of_mem hY₁ (Or.inr hx)).symm

omit [Finite F] in
include hY₁ hY₂ in
theorem rootSub_20_le_centralizer : rootSub φ Y 2 0 ≤ Subgroup.centralizer {invJ₂ φ} :=
  fun _ hx => Subgroup.mem_centralizer_singleton_iff.mpr
    (commute_invJ₂_of_mem hY₁ hY₂ (Or.inr hx)).symm

omit [Finite F] in
include hY₁ hY₂ in
theorem rootSub_02_le_centralizer : rootSub φ Y 0 2 ≤ Subgroup.centralizer {invJ₂ φ} :=
  fun _ hx => Subgroup.mem_centralizer_singleton_iff.mpr
    (commute_invJ₂_of_mem hY₁ hY₂ (Or.inl hx)).symm

omit [Finite F] in
theorem pow_ringChar_of_mem_rootSub_01 : ∀ x ∈ rootSub φ Y 0 1, x ^ ringChar F = 1 :=
  fun _ hx => pow_ringChar_of_mem_rootX₁ hx

omit [Finite F] in
theorem pow_ringChar_of_mem_rootSub_12 : ∀ x ∈ rootSub φ Y 1 2, x ^ ringChar F = 1 := by
  rw [rootSub_12]
  exact pow_ringChar_of_mem_map (fun _ h => pow_ringChar_of_mem_rootX₁ h) _

omit [Finite F] in
theorem pow_ringChar_of_mem_rootSub_21 : ∀ x ∈ rootSub φ Y 2 1, x ^ ringChar F = 1 := by
  rw [rootSub_21]
  exact pow_ringChar_of_mem_map (fun _ h => pow_ringChar_of_mem_rootX₂ h) _

omit [Finite F] in
theorem pow_ringChar_of_mem_rootSub_20 : ∀ x ∈ rootSub φ Y 2 0, x ^ ringChar F = 1 := by
  rw [rootSub_20]
  exact pow_ringChar_of_mem_map (fun _ h => pow_ringChar_of_mem_rootX₁ h) _

omit [Finite F] in
theorem pow_ringChar_of_mem_rootSub_02 : ∀ x ∈ rootSub φ Y 0 2, x ^ ringChar F = 1 := by
  rw [rootSub_02]
  exact pow_ringChar_of_mem_map (fun _ h => pow_ringChar_of_mem_rootX₂ h) _

end RootFacts

section Analysis

variable {Y : G} (hY₁ : Y⁻¹ * J * Y = invJ₁ φ) (hY₂ : Y⁻¹ * invJ₁ φ * Y = invJ₂ φ)
  (hcard : Nat.card G * Nat.card Z =
    Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1))
  (N : Subgroup G) (hN : N ≤ Subgroup.centralizer {rootUp φ 1})
  (hNp : IsPGroup (ringChar F) N)
  (hNall : ∀ x ∈ Subgroup.centralizer ({rootUp φ 1} : Set G), ∀ k : ℕ,
    x ^ (ringChar F ^ k) = 1 → x ∈ N)

include hZ hZodd h2 hJ hY₁ hY₂ hNp hNall in
theorem sup_three_le_pcore_of_commutes [Finite G]
    (h01 : Commutes (rootSub φ Y 0 1) (rootSub φ Y 1 2))
    (h20 : Commutes (rootSub φ Y 2 0) (rootSub φ Y 0 1)) :
    rootSub φ Y 0 1 ⊔ rootSub φ Y 1 2 ⊔ rootSub φ Y 2 0 ≤ N ∧
      Nat.card F ^ 3 ∣
        Nat.card (rootSub φ Y 0 1 ⊔ rootSub φ Y 1 2 ⊔ rootSub φ Y 2 0 : Subgroup G) := by
  have hT : ∀ i j, ∀ t, IsTorus φ t → (rootSub φ Y i j).map (conjHom t) = rootSub φ Y i j :=
    fun i j t ht => torus_map_rootSub φ hZ hZodd h2 hJ hY₁ hY₂ ht i j
  refine sup_three_le_pcore φ hZ hZodd h2 hJ N hNp hNall _ _ _
    (rootSub_01_le_centralizer φ) (rootSub_12_le_centralizer φ hY₁)
    (rootSub_20_le_centralizer φ hY₁ hY₂) (card_rootX₁ hZ) (card_rootSub_12 hZ)
    (card_rootSub_20 hZ) (pow_ringChar_of_mem_rootSub_01 φ) (pow_ringChar_of_mem_rootSub_12 φ)
    (pow_ringChar_of_mem_rootSub_20 φ) (hT 0 1) (hT 1 2) (hT 2 0) ?_ ?_ ?_
  · intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact comm_rootX₁ x hx _ (rootUp_one_mem φ)
  · intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (h01 _ (rootUp_one_mem φ) x hx).symm
  · intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact h20 x hx _ (rootUp_one_mem φ)

include hZ hZodd h2 hJ hY₁ hY₂ hcard hN hNp hNall in
theorem cube_dvd_card_centralizer_rootUp_one [Finite G] :
    Nat.card F ^ 3 ∣ Nat.card (Subgroup.centralizer ({rootUp φ 1} : Set G)) := by
  classical
  by_contra hQ₀
  have hp : (ringChar F).Prime := CharP.char_is_prime F _
  have : Fact (ringChar F).Prime := ⟨hp⟩
  obtain ⟨f, hf, hq⟩ := exists_card_eq_ringChar_pow F
  have hT : ∀ i j, ∀ t, IsTorus φ t → (rootSub φ Y i j).map (conjHom t) = rootSub φ Y i j :=
    fun i j t ht => torus_map_rootSub φ hZ hZodd h2 hJ hY₁ hY₂ ht i j
  have hthree : Commutes (rootSub φ Y 0 1) (rootSub φ Y 1 2) →
      Commutes (rootSub φ Y 2 0) (rootSub φ Y 0 1) → False := by
    intro h01 h20
    obtain ⟨hle, hdvd⟩ :=
      sup_three_le_pcore_of_commutes φ hZ hZodd h2 hJ hY₁ hY₂ N hNp hNall h01 h20
    exact hQ₀ (hdvd.trans ((Subgroup.card_dvd_of_le hle).trans (Subgroup.card_dvd_of_le hN)))
  obtain ⟨z, hzN, hzX, hz1, hzp, hzC⟩ : ∃ z ∈ N, z ∈ Subgroup.centralizer (rootX₁ φ : Set G) ∧
      z ≠ 1 ∧ z ^ ringChar F = 1 ∧
      Nat.card F ^ 3 ∣ Nat.card (Subgroup.centralizer ({z} : Set G)) := by
    have hX₁p : IsPGroup (ringChar F) (rootX₁ φ) :=
      isPGroup_of_forall_pow (fun y hy => pow_ringChar_of_mem_rootX₁ hy)
    obtain ⟨U, hXU⟩ := hX₁p.exists_le_sylow
    have hU3 : Nat.card F ^ 3 ∣ Nat.card (U : Subgroup G) := by
      rw [Sylow.card_eq_multiplicity, hq, ← pow_mul]
      apply pow_dvd_pow
      have h3 := cube_dvd_card hZ hcard
      rw [hq, ← pow_mul] at h3
      exact (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp h3
    have hnt : Nontrivial (U : Subgroup G) := by
      refine nontrivial_of_ne (⟨rootUp φ 1, hXU (rootUp_one_mem φ)⟩ : (U : Subgroup G)) 1 ?_
      intro h
      exact rootUp_one_ne_one φ hZ (congrArg Subtype.val h)
    have := U.isPGroup'.center_nontrivial
    obtain ⟨c, hc1⟩ := exists_ne (1 : Subgroup.center (U : Subgroup G))
    have hc₀cent : ∀ y ∈ (U : Subgroup G), y * ((c : (U : Subgroup G)) : G) =
        ((c : (U : Subgroup G)) : G) * y := fun y hy =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp c.2 ⟨y, hy⟩)
    have hc₀1 : ((c : (U : Subgroup G)) : G) ≠ 1 := fun h => hc1 (Subtype.ext (Subtype.ext h))
    obtain ⟨k, hk⟩ := U.isPGroup' (c : (U : Subgroup G))
    have hk' : ((c : (U : Subgroup G)) : G) ^ (ringChar F ^ k) = 1 := by
      simpa using congrArg Subtype.val hk
    obtain ⟨j, hj1, hjp⟩ := exists_pow_ne_one_pow_eq_one hc₀1 hk'
    have hzcent : ∀ y ∈ (U : Subgroup G),
        y * ((c : (U : Subgroup G)) : G) ^ (ringChar F ^ j) =
          ((c : (U : Subgroup G)) : G) ^ (ringChar F ^ j) * y := fun y hy =>
      (Commute.pow_right (hc₀cent y hy) _).eq
    have hzQ : ((c : (U : Subgroup G)) : G) ^ (ringChar F ^ j) ∈
        Subgroup.centralizer ({rootUp φ 1} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hzcent _ (hXU (rootUp_one_mem φ))).symm
    refine ⟨_, hNall _ hzQ 1 (by rw [pow_one]; exact hjp), ?_, hj1, hjp, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact hzcent x (hXU hx)
    · refine hU3.trans (Subgroup.card_dvd_of_le ?_)
      intro y hy
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hzcent y hy)
  set K : Subgroup G := N ⊓ Subgroup.centralizer (rootX₁ φ : Set G) with hK_def
  have hKp : IsPGroup (ringChar F) K := hNp.to_le inf_le_left
  have hKJ : ∀ m ∈ K, J * m * J⁻¹ ∈ K := fun m hm =>
    Subgroup.mem_inf.mpr ⟨conj_J_mem_pcore φ N hN hNp hNall (Subgroup.mem_inf.mp hm).1,
      conj_mem_centralizer_of_map_eq (torus_map_rootX₁ φ hZ hZodd h2 (isTorus_J φ))
        (Subgroup.mem_inf.mp hm).2⟩
  have hKJ₁ : ∀ m ∈ K, invJ₁ φ * m * (invJ₁ φ)⁻¹ ∈ K := fun m hm =>
    Subgroup.mem_inf.mpr ⟨conj_invJ₁_mem_pcore φ N hN hNp hNall (Subgroup.mem_inf.mp hm).1,
      conj_mem_centralizer_of_map_eq (torus_map_rootX₁ φ hZ hZodd h2 (isTorus_invJ₁ φ))
        (Subgroup.mem_inf.mp hm).2⟩
  have hKcard := card_eq_mul_of_isPGroup φ hZ hZodd h2 hJ K hKp hKJ hKJ₁
  have hwX : ∀ w ∈ K, ∀ x ∈ rootX₁ φ, x * w = w * x := fun w hw x hx =>
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hw).2) x hx
  by_cases h12 : (K ⊓ Subgroup.centralizer {invJ₁ φ} : Subgroup G) = ⊥ ∧
      (K ⊓ Subgroup.centralizer {invJ₂ φ} : Subgroup G) = ⊥
  ·
    obtain ⟨e1, e2⟩ := h12
    rw [e1, e2, Subgroup.card_bot, mul_one, mul_one] at hKcard
    have hKle : K ≤ Subgroup.centralizer {J} := by
      have := Subgroup.eq_of_le_of_card_ge
        (inf_le_left : (K ⊓ Subgroup.centralizer {J} : Subgroup G) ≤ K) (le_of_eq hKcard)
      rw [← this]
      exact inf_le_right
    have hzK : z ∈ K := Subgroup.mem_inf.mpr ⟨hzN, hzX⟩
    have hzX₁ : z ∈ rootX₁ φ := mem_rootX₁_of_mem_pcore φ hZ hZodd h2 N hN hNp hzN
      (Subgroup.mem_centralizer_singleton_iff.mp (hKle hzK)).symm
    have := card_centralizer_eq_rootUp_one φ hZ h2 (commute_J_of_mem_rootX₁ hzX₁) hz1 hzp
    exact hQ₀ (this ▸ hzC)
  · rw [not_and_or] at h12
    rcases h12 with h | h
    · obtain ⟨w, hw, hw1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left h
      obtain ⟨hwK, hwJ₁⟩ := Subgroup.mem_inf.mp hw
      have hwN := (Subgroup.mem_inf.mp hwK).1
      rcases pcore_inf_invJ₁_le φ hZ hZodd h2 hJ hY₁ hY₂ N hN hNp hNall with hA | hA
      ·
        have h01 : Commutes (rootSub φ Y 0 1) (rootSub φ Y 1 2) :=
          commutes_rootX₁_of_mem φ hZ hZodd h2 hJ hY₁ hY₂ (by decide)
          (hA (Subgroup.mem_inf.mpr ⟨hwN, hwJ₁⟩)) hw1 (hwX w hwK)
        have h20 : Commutes (rootSub φ Y 2 0) (rootSub φ Y 0 1) := by
          simpa using commutes_succ hZ hZodd h2 hJ hY₁ hY₂
            (commutes_succ hZ hZodd h2 hJ hY₁ hY₂ h01)
        exact hthree h01 h20
      ·
        have h01 : Commutes (rootSub φ Y 0 1) (rootSub φ Y 2 1) :=
          commutes_rootX₁_of_mem φ hZ hZodd h2 hJ hY₁ hY₂ (by decide)
          (hA (Subgroup.mem_inf.mpr ⟨hwN, hwJ₁⟩)) hw1 (hwX w hwK)
        have h12' : Commutes (rootSub φ Y 1 2) (rootSub φ Y 0 2) := by
          simpa using commutes_succ hZ hZodd h2 hJ hY₁ hY₂ h01
        exact hQ₀ (cube_dvd_of_commuting_root_pair φ hZ hZodd h2 hJ hY₁ hY₂ hcard
          (rootSub φ Y 1 2) (rootSub φ Y 0 2) (rootSub_12_le_centralizer φ hY₁)
          (rootSub_02_le_centralizer φ hY₁ hY₂) (card_rootSub_12 hZ) (card_rootSub_02 hZ)
          (pow_ringChar_of_mem_rootSub_12 φ) (pow_ringChar_of_mem_rootSub_02 φ)
          comm_rootSub_12 comm_rootSub_02 (inverts_J_rootSub_12 φ hZ hZodd h2 hJ hY₁ hY₂)
          (inverts_J_rootSub_02 φ hZ hZodd h2 hJ hY₁ hY₂) h12'
          (by simpa [swap01] using rootSub_map_W φ hZ hZodd h2 hJ hY₁ hY₂ 1 2)
          (by simpa [swap01] using rootSub_map_W φ hZ hZodd h2 hJ hY₁ hY₂ 0 2)
          (hT 1 2) (hT 0 2))
    · obtain ⟨w, hw, hw1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left h
      obtain ⟨hwK, hwJ₂⟩ := Subgroup.mem_inf.mp hw
      have hwN := (Subgroup.mem_inf.mp hwK).1
      rcases pcore_inf_invJ₂_le φ hZ hZodd h2 hJ hY₁ hY₂ N hN hNp hNall with hA | hA
      ·
        have h02 : Commutes (rootSub φ Y 0 1) (rootSub φ Y 2 0) :=
          commutes_rootX₁_of_mem φ hZ hZodd h2 hJ hY₁ hY₂ (by decide)
          (hA (Subgroup.mem_inf.mpr ⟨hwN, hwJ₂⟩)) hw1 (hwX w hwK)
        have h01 : Commutes (rootSub φ Y 0 1) (rootSub φ Y 1 2) := by
          have := commutes_succ hZ hZodd h2 hJ hY₁ hY₂ h02
          simp only [Fin.reduceAdd, Fin.isValue] at this
          exact this.symm
        exact hthree h01 h02.symm
      ·
        have h02 : Commutes (rootSub φ Y 0 1) (rootSub φ Y 0 2) :=
          commutes_rootX₁_of_mem φ hZ hZodd h2 hJ hY₁ hY₂ (by decide)
          (hA (Subgroup.mem_inf.mpr ⟨hwN, hwJ₂⟩)) hw1 (hwX w hwK)
        have h21 : Commutes (rootSub φ Y 2 0) (rootSub φ Y 2 1) := by
          simpa using commutes_succ hZ hZodd h2 hJ hY₁ hY₂
            (commutes_succ hZ hZodd h2 hJ hY₁ hY₂ h02)
        exact hQ₀ (cube_dvd_of_commuting_root_pair φ hZ hZodd h2 hJ hY₁ hY₂ hcard
          (rootSub φ Y 2 1) (rootSub φ Y 2 0) (rootSub_21_le_centralizer φ hY₁)
          (rootSub_20_le_centralizer φ hY₁ hY₂) (card_rootSub_21 hZ) (card_rootSub_20 hZ)
          (pow_ringChar_of_mem_rootSub_21 φ) (pow_ringChar_of_mem_rootSub_20 φ)
          comm_rootSub_21 comm_rootSub_20 (inverts_J_rootSub_21 φ hZ hZodd h2 hJ hY₁ hY₂)
          (inverts_J_rootSub_20 φ hZ hZodd h2 hJ hY₁ hY₂) h21.symm
          (by simpa [swap01] using rootSub_map_W φ hZ hZodd h2 hJ hY₁ hY₂ 2 1)
          (by simpa [swap01] using rootSub_map_W φ hZ hZodd h2 hJ hY₁ hY₂ 2 0)
          (hT 2 1) (hT 2 0))

end Analysis

end CFSG.BrauerLinearThree
