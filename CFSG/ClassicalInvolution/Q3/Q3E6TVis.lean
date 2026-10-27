module

public import CFSG.ClassicalInvolution.Q3.Q3URNodes
public import CFSG.ClassicalInvolution.Q3.Q3E8BCent

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3E6T

open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSU
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Q3.Q3W
open CFSG.ClassicalInvolution.RouteD.NonClassical
  (TE6Layer te6Inv Linked NCEdge mem_centralizingMembers_pair centralizingMembers_mul_iff
    le_centralizer_pair_mul_iff le_centralizer_of_commutes suMat_entry_zero_of_commutes
    range_blockEmb_zero_eq_LcU)
open scoped MatrixGroups commutatorElement


section Nodes

variable {m : ℕ} {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem UNodes3.psi_inv3 (c : UCtx3 m Ω K z) (nd : UNodes3 c) {a : ℕ} (ha : a < m) :
    c.d.ψ (zEltU (GaloisField 3 2) 3 1 (nodePair m a ha)) =
      locElt Ω z (nd.w a) (le_centralizingLayer (nd.mem a ha) (nd.isCl a ha).mem) :=
  psiU_root_inv3 c.hm c.d (isLongRootSU2_LcU two_ne_zero_gf9 c.hn _) (nd.img a ha)
    (le_centralizingLayer (nd.mem a ha)) (nd.isCl a ha).mem (nd.isCl a ha).orderOf_eq_two

theorem UNodes3.le_centralizer_iff_root3 (c : UCtx3 m Ω K z) (nd : UNodes3 c) {a : ℕ}
    (ha : a < m) {N : Subgroup G} (hN : N ∈ centralizingMembers Ω {z})
    {ρ : Subgroup (Su (GaloisField 3 2) 3 1 (m + 1))} (hρ : Pow3 ρ)
    (hNρ : locImg Ω z N = ρ.map c.d.ψ) :
    N ≤ Subgroup.centralizer ({nd.w a} : Set G) ↔
      ρ ≤ Subgroup.centralizer
        ({zEltU (GaloisField 3 2) 3 1 (nodePair m a ha)} : Set _) := by
  have hw : nd.w a ∈ locLayer Ω z :=
    le_centralizingLayer (nd.mem a ha) (nd.isCl a ha).mem
  have h1 := le_centralizer_iff_locImg3 c.hΩ c.hex c.hP1 c.hO3 hN ⟨nd.w a, hw⟩
  have h2 := le_centralizer_iff_map3 c.d.ψ c.d.ker_le c.ker_cop hρ
    (zEltU (GaloisField 3 2) 3 1 (nodePair m a ha))
  have h3 : c.d.ψ (zEltU (GaloisField 3 2) 3 1 (nodePair m a ha)) =
      locElt Ω z (nd.w a) hw := UNodes3.psi_inv3 c nd ha
  rw [h2, h3, ← hNρ]
  exact h1

omit [Finite G] in
theorem UNodes3.mem_centralizingMembers_mul3 (c : UCtx3 m Ω K z) (nd : UNodes3 c) {a : ℕ}
    (ha : a < m) (h : a = 0 ∨ 2 ≤ a) : nd.j a ∈ centralizingMembers Ω {z * nd.w 0} := by
  have h0 : 0 < m := by omega
  refine ⟨(nd.mem a ha).1, ?_⟩
  refine (le_centralizer_pair_mul_iff (nd.mem a ha).2).mpr ?_
  rcases h with rfl | h2
  · exact isSubnormal_le (nd.isCl 0 h0).subnormal
  · exact le_centralizer_of_commutes (Gaps.commutes_symm (nd.far 0 h0 a ha (by omega)))
      (nd.isCl 0 h0).mem

omit [Finite G] in
theorem UNodes3.K_mem_centralizingMembers_mul3 (c : UCtx3 m Ω K z) (nd : UNodes3 c)
    (hm : 0 < m) : K ∈ centralizingMembers Ω {z * nd.w 0} :=
  ⟨c.hK, (le_centralizer_pair_mul_iff (isSubnormal_le c.hz.subnormal)).mpr
    (le_centralizer_of_commutes (nd.commK 0 hm) (nd.isCl 0 hm).mem)⟩

end Nodes

section Visible

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem exists_visible_equiv3 (c : UCtx3 5 Ω K z) (nd : UNodes3 c) :
    ∃ φ : {N : Subgroup G // N ∈ centralizingMembers Ω {z * nd.w 0, z}} ≃ TE6Layer 3 1,
      (∀ N N', Commutes N.1 N'.1 ↔ TE6Layer.rel (φ N) (φ N')) ∧
        ∀ h : K ∈ centralizingMembers Ω {z * nd.w 0, z}, φ ⟨K, h⟩ = none := by
  classical
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨c.hK, isSubnormal_le c.hz.subnormal⟩
  have hKvis : K ∈ centralizingMembers Ω {z * nd.w 0, z} := by
    rw [centralizingMembers_mul_iff, mem_centralizingMembers_pair]
    exact ⟨hKz, le_centralizer_of_commutes (nd.commK 0 (by norm_num))
      (nd.isCl 0 (by norm_num)).mem⟩
  have hpow : ∀ ρ ∈ longRootSetU (K := GaloisField 3 2) (p := 3) (f := 1) c.hn, Pow3 ρ := by
    rintro ρ ⟨i, hi⟩
    exact c.pow_three_root hi
  have hmem : ∀ ρ : {R : Subgroup (Su (GaloisField 3 2) 3 1 (5 + 1)) //
      R ∈ longRootSetU (K := GaloisField 3 2) (p := 3) (f := 1) (by norm_num : 2 ≤ 5 + 1) ∧
        R ≤ Subgroup.centralizer ({te6Inv 3 1} : Set _)},
      ∃ L ∈ centralizingMembers Ω {z}, L ≠ K ∧ locImg Ω z L = ρ.1.map c.d.ψ :=
    fun ρ => exists_member_of_rootU3 c.hm c.hΩ c.hex c.hK c.hz c.hP1 c.hO3 c.d ρ.2.1
  choose Lof hLz hLK hLimg using hmem
  have hvis : ∀ ρ, Lof ρ ∈ centralizingMembers Ω {z * nd.w 0, z} := by
    intro ρ
    rw [centralizingMembers_mul_iff, mem_centralizingMembers_pair]
    exact ⟨hLz ρ, (UNodes3.le_centralizer_iff_root3 c nd (by norm_num : 0 < 5) (hLz ρ)
      (hpow _ ρ.2.1) (hLimg ρ)).mpr ρ.2.2⟩
  let ι : TE6Layer 3 1 → {N : Subgroup G // N ∈ centralizingMembers Ω {z * nd.w 0, z}} :=
    fun a => Option.elim a ⟨K, hKvis⟩ fun ρ => ⟨Lof ρ, hvis ρ⟩
  have hinj : Function.Injective ι := by
    intro a b hab
    rcases a with _ | ρ <;> rcases b with _ | ρ'
    · rfl
    · exact absurd (congrArg Subtype.val hab).symm (hLK ρ')
    · exact absurd (congrArg Subtype.val hab) (hLK ρ)
    · have h : Lof ρ = Lof ρ' := congrArg Subtype.val hab
      have himg : ρ.1.map c.d.ψ = ρ'.1.map c.d.ψ := by
        rw [← hLimg ρ, ← hLimg ρ', h]
      exact congrArg some (Subtype.ext (eq_of_map_eq_of_pow3 c.d.ψ c.d.ker_le c.ker_cop
        (hpow _ ρ.2.1) (hpow _ ρ'.2.1) himg))
  have hsurj : Function.Surjective ι := by
    rintro ⟨N, hN⟩
    rw [centralizingMembers_mul_iff, mem_centralizingMembers_pair] at hN
    obtain ⟨hNz, hNw⟩ := hN
    by_cases hNK : N = K
    · exact ⟨none, Subtype.ext hNK.symm⟩
    · obtain ⟨ρ, hρT, hNρ⟩ := exists_root_of_neU3 c.hm c.hΩ c.hex c.hK c.hz c.hP1 c.hO3 c.d
        hNz hNK
      have hρc : ρ ≤ Subgroup.centralizer ({te6Inv 3 1} : Set _) :=
        (UNodes3.le_centralizer_iff_root3 c nd (by norm_num : 0 < 5) hNz (hpow ρ hρT) hNρ).mp
          hNw
      refine ⟨some ⟨ρ, hρT, hρc⟩, Subtype.ext ?_⟩
      exact locImg_injOn3 c.hΩ c.hex c.hP1 c.hO3 (hLz _) hNz
        ((hLimg ⟨ρ, hρT, hρc⟩).trans hNρ.symm)
  have key : ∀ a b : TE6Layer 3 1, Commutes (ι a).1 (ι b).1 ↔ TE6Layer.rel a b := by
    intro a b
    rcases a with _ | ρ <;> rcases b with _ | ρ'
    · exact iff_false_intro (not_commutes_self3 c.hz)
    · exact iff_true_intro (commutes_K_of_neU3 c.hm c.hΩ c.hex c.hK c.hz c.hP1 c.hO3 c.d
        (hLz ρ') (hLK ρ'))
    · exact iff_true_intro (Gaps.commutes_symm (commutes_K_of_neU3 c.hm c.hΩ c.hex c.hK c.hz
        c.hP1 c.hO3 c.d (hLz ρ) (hLK ρ)))
    · obtain ⟨i, hi⟩ := ρ.2.1
      exact c.commutes_iff_root (hLz ρ) (hLz ρ') hi (hLimg ρ) (hLimg ρ')
  refine ⟨(Equiv.ofBijective ι ⟨hinj, hsurj⟩).symm, fun N N' => ?_, fun h => ?_⟩
  · have h1 : ι ((Equiv.ofBijective ι ⟨hinj, hsurj⟩).symm N) = N :=
      (Equiv.ofBijective ι ⟨hinj, hsurj⟩).apply_symm_apply N
    have h2 : ι ((Equiv.ofBijective ι ⟨hinj, hsurj⟩).symm N') = N' :=
      (Equiv.ofBijective ι ⟨hinj, hsurj⟩).apply_symm_apply N'
    have := key ((Equiv.ofBijective ι ⟨hinj, hsurj⟩).symm N)
      ((Equiv.ofBijective ι ⟨hinj, hsurj⟩).symm N')
    rwa [h1, h2] at this
  · exact (Equiv.symm_apply_eq _).mpr (Subtype.ext rfl)

end Visible

section Link

theorem suMat_diag_eq_one_of_pow3 {ρ : Subgroup (Su (GaloisField 3 2) 3 1 (5 + 1))}
    (hρ : Pow3 ρ) (l : Fin (5 + 1))
    (hz : ∀ g ∈ ρ, ∀ k : Fin (5 + 1), k ≠ l → suMat g l k = 0) :
    ∀ g ∈ ρ, suMat g l l = 1 := by
  let χ : ρ →* GaloisField 3 2 :=
    { toFun := fun g => suMat g.1 l l
      map_one' := by simp [suMat_one]
      map_mul' := fun g h => by
        show suMat (g.1 * h.1) l l = suMat g.1 l l * suMat h.1 l l
        rw [suMat_mul, Matrix.mul_apply, Finset.sum_eq_single l]
        · intro k _ hk
          rw [hz g.1 g.2 k hk, zero_mul]
        · intro h
          exact absurd (Finset.mem_univ l) h }
  have hle : ⁅ρ, ρ⁆ ≤ (MonoidHom.ker χ.toHomUnits).map ρ.subtype := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have hab : ⁅a, b⁆ ∈ ρ := by
      rw [commutatorElement_def]
      exact ρ.mul_mem (ρ.mul_mem (ρ.mul_mem ha hb) (ρ.inv_mem ha)) (ρ.inv_mem hb)
    refine ⟨⟨⁅a, b⁆, hab⟩, ?_, rfl⟩
    have h1 : (⟨⁅a, b⁆, hab⟩ : ρ) = ⁅(⟨a, ha⟩ : ρ), (⟨b, hb⟩ : ρ)⁆ := rfl
    rw [SetLike.mem_coe, MonoidHom.mem_ker, h1, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  intro g hg
  obtain ⟨x, hx, hxg⟩ := hle (hρ g hg)
  have hxe : x = (⟨g, hg⟩ : ρ) ^ 3 := Subtype.ext (by simpa using hxg)
  have h1 : χ.toHomUnits x = 1 := hx
  rw [hxe, map_pow] at h1
  have h2 : (suMat g l l) ^ 3 = 1 := by
    have := congrArg Units.val h1
    simpa [χ] using this
  have h3 : (suMat g l l - 1) ^ 3 = 0 := by
    rw [sub_pow_char (p := 3) (suMat g l l) 1, h2]
    simp
  exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0) |>.mp h3)

theorem le_range_blockEmb_of_le_centralizer_zElt3 {ρ : Subgroup (Su (GaloisField 3 2) 3 1 (5 + 1))}
    (hρ : Pow3 ρ)
    (h₂ : ρ ≤ Subgroup.centralizer
      ({zEltU (GaloisField 3 2) 3 1 (nodePair 5 2 (by norm_num))} : Set _))
    (h₃ : ρ ≤ Subgroup.centralizer
      ({zEltU (GaloisField 3 2) 3 1 (nodePair 5 3 (by norm_num))} : Set _))
    (h₄ : ρ ≤ Subgroup.centralizer
      ({zEltU (GaloisField 3 2) 3 1 (nodePair 5 4 (by norm_num))} : Set _)) :
    ρ ≤ (blockEmb (GaloisField 3 2) 3 1 (5 + 1) 2 0 (by norm_num)).range := by
  have h2 := two_ne_zero_gf9
  have hz : ∀ g ∈ ρ, ∀ j k : Fin (5 + 1), j ≠ k → (2 ≤ j.val ∨ 2 ≤ k.val) →
      suMat g j k = 0 := fun g hg =>
    suMat_entry_zero_of_commutes (p := 3) (f := 1) h2
      (Subgroup.mem_centralizer_singleton_iff.mp (h₂ hg))
      (Subgroup.mem_centralizer_singleton_iff.mp (h₃ hg))
      (Subgroup.mem_centralizer_singleton_iff.mp (h₄ hg))
  intro g hg
  rw [mem_range_blockEmb_iff]
  intro l hl
  have hl2 : 2 ≤ l.val := by omega
  have hdiag := suMat_diag_eq_one_of_pow3 hρ l
    (fun g hg k hk => hz g hg l k (Ne.symm hk) (Or.inl hl2)) g hg
  funext a
  rw [CFSG.ClassicalGroups.Unitary.smul_def, Matrix.mulVec_single_one]
  by_cases hal : a = l
  · subst hal
    rw [Pi.single_eq_same]
    exact hdiag
  · rw [Pi.single_eq_of_ne hal]
    exact hz g hg a l hal (Or.inr hl2)

theorem eq_LcU_of_le_centralizer_zElt3 {ρ : Subgroup (Su (GaloisField 3 2) 3 1 (5 + 1))}
    {i : Su (GaloisField 3 2) 3 1 (5 + 1)}
    (hρi : IsLongRootSU2 (GaloisField 3 2) 3 1 (by norm_num : 2 ≤ 5 + 1) ρ i) (hρ : Pow3 ρ)
    (h₂ : ρ ≤ Subgroup.centralizer
      ({zEltU (GaloisField 3 2) 3 1 (nodePair 5 2 (by norm_num))} : Set _))
    (h₃ : ρ ≤ Subgroup.centralizer
      ({zEltU (GaloisField 3 2) 3 1 (nodePair 5 3 (by norm_num))} : Set _))
    (h₄ : ρ ≤ Subgroup.centralizer
      ({zEltU (GaloisField 3 2) 3 1 (nodePair 5 4 (by norm_num))} : Set _)) :
    ρ = LcU (GaloisField 3 2) 3 1 (nodePair 5 0 (by norm_num)) := by
  have h2 := two_ne_zero_gf9
  have hle := le_range_blockEmb_of_le_centralizer_zElt3 hρ h₂ h₃ h₄
  rw [range_blockEmb_zero_eq_LcU (p := 3) (f := 1) h2] at hle
  have hL0 := isLongRootSU2_LcU (p := 3) (f := 1) h2 (by norm_num : 2 ≤ 5 + 1)
    (nodePair 5 0 (by norm_num))
  have hi : i = zEltU (GaloisField 3 2) 3 1 (nodePair 5 0 (by norm_num)) :=
    hL0.eq_of_orderOf_eq_two card_gf9 (by norm_num) (hle hρi.mem)
      (hρi.isClassicalSL2 card_gf9 (by norm_num)).orderOf_eq_two
  rw [hρi.eq_longRootGroupSU h2, hi, ← hL0.eq_longRootGroupSU h2]

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem linked_of_visible3 (c : UCtx3 5 Ω K z) (nd : UNodes3 c) {β : Subgroup G}
    (hβ : β ∈ centralizingMembers Ω {z * nd.w 0}) (hnK : ¬ Commutes K β)
    (hn0 : ¬ Commutes β (nd.j 0)) (hn3 : ¬ Commutes β (nd.j 3)) :
    ∀ R ∈ centralizingMembers Ω {z * nd.w 0, z}, Linked Ω (z * nd.w 0) K R := by
  intro R hR
  have hKx := UNodes3.K_mem_centralizingMembers_mul3 c nd (by norm_num : 0 < 5)
  have hj : ∀ a (ha : a < 5), (a = 0 ∨ 2 ≤ a) → nd.j a ∈ centralizingMembers Ω {z * nd.w 0} :=
    fun a ha h => UNodes3.mem_centralizingMembers_mul3 c nd ha h
  have hK0 : Linked Ω (z * nd.w 0) K (nd.j 0) :=
    (Linked.single ⟨hKx, hβ, hnK⟩).trans (Linked.single ⟨hβ, hj 0 (by norm_num) (Or.inl rfl), hn0⟩)
  have hK3 : Linked Ω (z * nd.w 0) K (nd.j 3) :=
    (Linked.single ⟨hKx, hβ, hnK⟩).trans
      (Linked.single ⟨hβ, hj 3 (by norm_num) (Or.inr (by norm_num)), hn3⟩)
  have hK2 : Linked Ω (z * nd.w 0) K (nd.j 2) :=
    hK3.trans (Linked.single (NCEdge.symm ⟨hj 2 (by norm_num) (Or.inr le_rfl),
      hj 3 (by norm_num) (Or.inr (by norm_num)), nd.adj 2 (by norm_num)⟩))
  have hK4 : Linked Ω (z * nd.w 0) K (nd.j 4) :=
    hK3.trans (Linked.single ⟨hj 3 (by norm_num) (Or.inr (by norm_num)),
      hj 4 (by norm_num) (Or.inr (by norm_num)), nd.adj 3 (by norm_num)⟩)
  have hRx := (mem_centralizingMembers_pair.mp hR).1
  obtain ⟨hRz, hRw⟩ := mem_centralizingMembers_pair.mp (centralizingMembers_mul_iff.mp hR)
  have hstep : ∀ a (ha : a < 5), 2 ≤ a → Linked Ω (z * nd.w 0) K (nd.j a) →
      ¬ Commutes R (nd.j a) → Linked Ω (z * nd.w 0) K R := fun a ha h2a hKa hnc =>
    hKa.trans (Linked.single ⟨hj a ha (Or.inr h2a), hRx, fun hc => hnc (Gaps.commutes_symm hc)⟩)
  by_cases hRK : R = K
  · subst hRK
    exact Relation.ReflTransGen.refl
  obtain ⟨ρ, hρT, hRρ⟩ := exists_root_of_neU3 c.hm c.hΩ c.hex c.hK c.hz c.hP1 c.hO3 c.d hRz hRK
  obtain ⟨i, hi⟩ := hρT
  have hpow : Pow3 ρ := c.pow_three_root hi
  have hρle : ∀ a (ha : a < 5), Commutes R (nd.j a) →
      ρ ≤ Subgroup.centralizer ({zEltU (GaloisField 3 2) 3 1 (nodePair 5 a ha)} : Set _) :=
    fun a ha hc => (UNodes3.le_centralizer_iff_root3 c nd ha hRz hpow hRρ).mp
      (le_centralizer_of_commutes hc (nd.isCl a ha).mem)
  by_cases h2 : Commutes R (nd.j 2)
  · by_cases h3 : Commutes R (nd.j 3)
    · by_cases h4 : Commutes R (nd.j 4)
      · have hρ0 := eq_LcU_of_le_centralizer_zElt3 hi hpow
          (hρle 2 (by norm_num) h2) (hρle 3 (by norm_num) h3) (hρle 4 (by norm_num) h4)
        have hR0 : R = nd.j 0 := locImg_injOn3 c.hΩ c.hex c.hP1 c.hO3 hRz
          (nd.mem 0 (by norm_num)) (by rw [hRρ, hρ0, nd.img 0 (by norm_num)])
        rw [hR0]
        exact hK0
      · exact hstep 4 (by norm_num) (by norm_num) hK4 h4
    · exact hstep 3 (by norm_num) (by norm_num) hK3 h3
  · exact hstep 2 (by norm_num) le_rfl hK2 h2

end Link

end CFSG.ClassicalInvolution.Q3.Q3E6T
