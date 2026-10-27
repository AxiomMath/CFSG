module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXTri
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3A75D4Cover
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3B57N

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Spin
open CFSG.ComponentClassification.Burgoyne.DX
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (linearConjugationHom)
open CFSG.RankThree.Classical.SteinbergBY
  (orthogonal_large_prime_semilinear_field_and_diagonal_gates)
open CFSG.ClassicalInvolution.G2D4Models.Twin (z0 z2 z3 triality_z0 triality_z2 triality_z3)

namespace P58b3D4

theorem not_five_distinct_of_card {α : Type*} [Finite α] (hα : Nat.card α = 4) {a b c d e : α}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (hbc : b ≠ c) (hbd : b ≠ d)
    (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) : False := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have h5 : ({a, b, c, d, e} : Finset α).card = 5 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac, had, hae]),
      Finset.card_insert_of_notMem (by simp [hbc, hbd, hbe]),
      Finset.card_insert_of_notMem (by simp [hcd, hce]), Finset.card_pair hde]
  have h := Finset.card_le_univ ({a, b, c, d, e} : Finset α)
  rw [h5, ← Nat.card_eq_fintype_card, hα] at h
  omega

variable {K : Type} [Field K] [Finite K]

theorem mulEquiv_mem_center {G : Type*} [Group G] (σ : G ≃* G) {w : G} (hw : w ∈ center G) :
    σ w ∈ center G := by
  rw [mem_center_iff] at hw ⊢
  intro g
  obtain ⟨g, rfl⟩ := σ.surjective g
  rw [← map_mul, ← map_mul, hw g]

theorem exists_mulEquiv_apply_eq_negOne8 (h2 : (2 : K) ≠ 0) {z : Sp8 K}
    (hz : z ∈ center (Sp8 K)) (hz1 : z ≠ 1) : ∃ σ : Sp8 K ≃* Sp8 K, σ z = negOne8 K := by
  set ρ := Tri.rhoT K with hρdef
  have hρ : IsTriality ρ := Tri.isTriality_rhoT K
  have e1 : ρ (negOne8 K) = z3 K * z0 K := by
    rw [negOne8_eq_z2_mul_z3, map_mul, triality_z2 h2 ρ hρ, triality_z3 h2 ρ hρ]
  have e2 : ρ (z3 K * z0 K) = z0 K * z2 K := by
    rw [map_mul, triality_z3 h2 ρ hρ, triality_z0 h2 ρ hρ]
  have e3 : ρ (z0 K * z2 K) = negOne8 K := by
    rw [map_mul, triality_z0 h2 ρ hρ, triality_z2 h2 ρ hρ, negOne8_eq_z2_mul_z3]
  have hb : negOne8 K ∈ center (Sp8 K) := negOne8_mem_center K
  have hb₁ : z3 K * z0 K ∈ center (Sp8 K) := e1 ▸ mulEquiv_mem_center ρ hb
  have hb₂ : z0 K * z2 K ∈ center (Sp8 K) := e2 ▸ mulEquiv_mem_center ρ hb₁
  have n0 : negOne8 K ≠ 1 := negOne8_ne_one K h2
  have n1 : z3 K * z0 K ≠ 1 := fun h => n0 (ρ.injective (by rw [e1, h, map_one]))
  have n2 : z0 K * z2 K ≠ 1 := fun h => n1 (ρ.injective (by rw [e2, h, map_one]))
  have n01 : negOne8 K ≠ z3 K * z0 K := fun h =>
    triality_moves_negOne8 h2 hρ (e1.trans h.symm)
  have n12 : z3 K * z0 K ≠ z0 K * z2 K := fun h => n01 (ρ.injective (by rw [e1, e2, h]))
  have n02 : negOne8 K ≠ z0 K * z2 K := fun h =>
    triality_moves_negOne8 h2 hρ ((congrArg ρ h).trans e3)
  have hmem : z = negOne8 K ∨ z = z3 K * z0 K ∨ z = z0 K * z2 K := by
    have : Finite (center (Sp8 K)) :=
      Nat.finite_of_card_ne_zero (by rw [card_center8 K h2]; norm_num)
    by_contra hne
    push Not at hne
    obtain ⟨m0, m1, m2⟩ := hne
    refine not_five_distinct_of_card (α := center (Sp8 K)) (card_center8 K h2)
      (a := 1) (b := ⟨_, hb⟩) (c := ⟨_, hb₁⟩) (d := ⟨_, hb₂⟩) (e := ⟨z, hz⟩) ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ <;> intro h <;> have h' := congrArg Subtype.val h
    · exact n0 h'.symm
    · exact n1 h'.symm
    · exact n2 h'.symm
    · exact hz1 h'.symm
    · exact n01 h'
    · exact n02 h'
    · exact m0 h'.symm
    · exact n12 h'
    · exact m1 h'.symm
    · exact m2 h'.symm
  rcases hmem with rfl | rfl | rfl
  · exact ⟨MulEquiv.refl _, rfl⟩
  · exact ⟨ρ.symm, by rw [← e1, MulEquiv.symm_apply_apply]⟩
  · exact ⟨ρ.symm.trans ρ.symm, by
      rw [MulEquiv.trans_apply, ← e2, MulEquiv.symm_apply_apply, ← e1, MulEquiv.symm_apply_apply]⟩

theorem exists_cover_d4 (hK : Nat.card K = 3) {X : Type} [Group X] (hX : Group.IsPerfect X)
    (e : X ⧸ center X ≃* P8 K) :
    ∃ c : F3D4.Cover (Sp8 K) X, ∀ s, e (QuotientGroup.mk (c.θ s)) = pi8 K s := by
  have hK' : Nat.card K = 3 ^ 1 := by rw [hK, pow_one]
  have hπX : Function.Surjective (e.toMonoidHom.comp (QuotientGroup.mk' (center X))) :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerX : (e.toMonoidHom.comp (QuotientGroup.mk' (center X))).ker ≤ center X := by
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff e e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
    exact hx
  obtain ⟨θ, hθ, hθk, hcomp⟩ := F3D4.exists_cover (F3D4.spin_hasSections hK' le_rfl) hX
    (pi8_surjective K) (ker_pi8 K).le hπX hkerX
  exact ⟨⟨θ, hθ, hθk, F3D4.spin_hasSections hK' le_rfl,
    isPerfect_spinGroup_quadPlus (by norm_num)⟩, fun s => hcomp s⟩

theorem mem_inner_of_mem_pointFamilyAut (hK : Nat.card K = 3) {δ : MulAut (P8 K)}
    (hδ : δ ∈ projectivePointFamilyAut (Q8 K)) {k : ℕ} (hk : Odd k)
    (hδk : δ ^ k ∈ inner (P8 K)) : δ ∈ inner (P8 K) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 3 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨f, hcard, hmod⟩ := exists_model8 K (p := 3)
  obtain ⟨-, ⟨ψ, -, hψker, -⟩, ⟨-, m, hm⟩, -, -, hPA, -⟩ :=
    orthogonal_large_prime_semilinear_field_and_diagonal_gates _ .POmegaPlus
      (Or.inr (Or.inl rfl)) 4 3 f hmod K hcard (MulEquiv.refl _)
  have hδI : δ ∈ matrixProjectiveImage (Q8 K) := hPA ▸ hδ
  have hδL : δ ∈ (linearConjugationHom (Q8 K)).range := by
    have hker : (⟨δ, hδI⟩ : matrixProjectiveImage (Q8 K)) ∈ ψ.ker :=
      MonoidHom.mem_ker.mpr (ringEquiv_eq_one_of_card_eq_three hK _)
    rw [hψker] at hker
    exact hker
  have hI : ((inner (P8 K)).subgroupOf (linearConjugationHom (Q8 K)).range).index = 2 ^ m := hm
  have h := mem_of_pow_mem_of_index_eq_two_pow hI hk (a := ⟨δ, hδL⟩)
    (by rw [mem_subgroupOf, SubgroupClass.coe_pow]; exact hδk)
  exact mem_subgroupOf.mp h


theorem oddAutInnerFix_d4 (hK : Nat.card K = 3) {X : Type} [Group X] (hX : Group.IsPerfect X)
    (e : X ⧸ center X ≃* P8 K) {c : X} (hcZ : c ∈ center X) (hc1 : c ≠ 1) :
    P58b3.OddAutInnerFix X c := by
  intro α hαc k hk hαk
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 3 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK])
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have h2 : (2 : K) ≠ 0 := two_ne_zero8 K hp2
  obtain ⟨cv, -⟩ := exists_cover_d4 hK hX e
  have : Group.IsPerfect (Sp8 K) := cv.perfect
  set α' := cv.lift α with hα'
  have hα's : ∀ s, cv.θ (α' s) = α (cv.θ s) := cv.lift_spec α
  set δ₀ := descend8 K α' with hδ₀
  have hδ₀l : liftAut K hp2 δ₀ = α' := liftAut_descend8 K hp2 α'
  have hcen : ∀ g : Sp8 K, cv.θ g ∈ center X → g ∈ center (Sp8 K) := fun g hg =>
    CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.mem_center_of_commutator_mem_center
      fun y => cv.ker_le (by
        rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact (mem_center_iff.mp hg (cv.θ y)).symm)
  obtain ⟨g₀, hg₀⟩ := cv.surj c
  have hg₀Z : g₀ ∈ center (Sp8 K) := hcen g₀ (by rw [hg₀]; exact hcZ)
  obtain ⟨z, hzZ, hz1, hαz⟩ : ∃ z ∈ center (Sp8 K), z ≠ 1 ∧ α' z = z := by
    by_cases hker : cv.θ.ker = ⊥
    · have hinj : Function.Injective cv.θ := (MonoidHom.ker_eq_bot_iff cv.θ).mp hker
      refine ⟨g₀, hg₀Z, fun h => hc1 (by rw [← hg₀, h, map_one]), ?_⟩
      exact hinj (by rw [hα's, hg₀, hαc])
    · obtain ⟨⟨w, hw⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hker
      have hw1' : w ≠ 1 := fun h => hw1 (Subtype.ext h)
      have hZ4 := card_center8 K h2
      have hne : cv.θ.ker ≠ center (Sp8 K) := by
        intro h
        have hg₀k : g₀ ∈ cv.θ.ker := by rw [h]; exact hg₀Z
        exact hc1 (by rw [← hg₀]; exact MonoidHom.mem_ker.mp hg₀k)
      have h2k : Nat.card cv.θ.ker = 2 := by
        have hd : Nat.card cv.θ.ker ∣ 2 ^ 2 := by
          have h := Subgroup.card_dvd_of_le cv.ker_le
          rw [hZ4] at h
          simpa using h
        obtain ⟨i, hi, hci⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
        interval_cases i
        · exact absurd (Subgroup.eq_bot_of_card_eq _ (by simpa using hci)) hker
        · simpa using hci
        · exact absurd (Subgroup.eq_of_le_of_card_ge cv.ker_le (by rw [hZ4, hci]; norm_num)) hne
      have hαw : α' w ∈ cv.θ.ker := by
        rw [MonoidHom.mem_ker, hα's, MonoidHom.mem_ker.mp hw, map_one]
      have hαw1 : α' w ≠ 1 := fun h => hw1' (α'.injective (h.trans (map_one α').symm))
      obtain ⟨u, -, hu⟩ := (Nat.card_eq_two_iff' (1 : cv.θ.ker)).mp h2k
      have e1 := hu ⟨w, hw⟩ hw1
      have e2 := hu ⟨α' w, hαw⟩ fun h => hαw1 (congrArg Subtype.val h)
      exact ⟨w, cv.ker_le hw, hw1', congrArg Subtype.val (e2.trans e1.symm)⟩
  obtain ⟨σ, hσ⟩ := exists_mulEquiv_apply_eq_negOne8 h2 hzZ hz1
  set δ := descend8 K σ * δ₀ * (descend8 K σ)⁻¹ with hδ
  have hδl : liftAut K hp2 δ = σ * α' * σ⁻¹ := by
    rw [hδ, map_mul, map_mul, map_inv, hδ₀l, liftAut_descend8]
  have hδb : liftAut K hp2 δ (negOne8 K) = negOne8 K := by
    rw [hδl, ← hσ, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hαz]
  have hδF : δ ∈ projectivePointFamilyAut (Q8 K) :=
    (liftAut_negOne8_iff K hp2 (Tri.isTriality_rhoT K) δ).1 hδb
  obtain ⟨x, hx⟩ := hαk
  obtain ⟨g, rfl⟩ := cv.surj x
  have hconj : ∀ g' : Sp8 K, liftAut K hp2 (MulAut.conj (pi8 K g')) = MulAut.conj g' :=
    fun g' => liftAut_unique K hp2 fun s => by
      rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
  have hα'k : α' ^ k = MulAut.conj g := by
    rw [hα', ← cv.lift_pow, ← hx, cv.lift_conj]
  have hδ₀k : δ₀ ^ k = MulAut.conj (pi8 K g) := by
    apply liftAut_injective K hp2
    rw [map_pow, hδ₀l, hα'k, hconj]
  have hδk : δ ^ k ∈ inner (P8 K) := by
    rw [hδ, conj_pow, hδ₀k]
    exact (inner_normal _).conj_mem _ ⟨_, rfl⟩ _
  have hδI := mem_inner_of_mem_pointFamilyAut hK hδF hk hδk
  have hδ₀I : δ₀ ∈ inner (P8 K) := by
    have e : δ₀ = (descend8 K σ)⁻¹ * δ * ((descend8 K σ)⁻¹)⁻¹ := by rw [hδ]; group
    rw [e]
    exact (inner_normal _).conj_mem _ hδI _
  obtain ⟨y, hy⟩ := hδ₀I
  obtain ⟨g', rfl⟩ := pi8_surjective K y
  have hα'c : α' = MulAut.conj g' := by rw [← hδ₀l, ← hy, hconj]
  refine ⟨cv.θ g', MulEquiv.ext fun t => ?_⟩
  obtain ⟨s, rfl⟩ := cv.surj t
  rw [← hα's, hα'c, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem oddAutInnerFix_of_POmegaPlus_four {X : Type} [Group X] (hX : IsQuasisimple X)
    (hm : Blueprint.LieModel (X ⧸ center X) .POmegaPlus 4 3 1) {c : X} (hcZ : c ∈ center X)
    (hc1 : c ≠ 1) : P58b3.OddAutInnerFix X c := by
  rcases hm with ⟨-, hcm⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
  rotate_left
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hcm
  exact oddAutInnerFix_d4 (by rw [hK, pow_one]) hX.1 (coordinatePlusWitnessEquiv K e) hcZ hc1

end P58b3D4

end CFSG.ComponentClassification.HarrisLit.T1
