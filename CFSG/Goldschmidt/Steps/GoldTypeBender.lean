module

public import CFSG.Goldschmidt.Basic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGoldschmidtBender
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvBasic
public import CFSG.GroupTheory.SuzukiTwoGroups
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGoldschmidtBasic

public section

namespace CFSG.Goldschmidt.GoldType

open CFSG.Open
open scoped MatrixGroups Pointwise
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter mem_sylowCenter
  sylowCenter_le benderBorel_sylowCenter normalizer_transitive_center map_center_eq_sylowCenter
  le_sylowCenter_of_card card_sylow_eq_of_mulEquiv)
open CFSG.ComponentClassification.AschbacherToolkit.BenderExt (benderData_of_isBenderGroup)
open CFSG.ComponentClassification.AschbacherToolkit.Goldschmidt (mem_sylowCenter_of_sq_eq_one
  mem_center_of_conj_eq_one conjAct conjAct_apply)

section Omega

variable {G : Type*} [Group G]

theorem omega1_le (T : Subgroup G) : Omega1 T ≤ T :=
  (Subgroup.closure_le _).2 fun _ ht => ht.1

theorem mem_omega1 {T : Subgroup G} {t : G} (ht : t ∈ T) (ht2 : t ^ 2 = 1) : t ∈ Omega1 T :=
  Subgroup.subset_closure ⟨ht, ht2⟩

theorem omega1_eq_self {T : Subgroup G} (h : ∀ t ∈ T, t ^ 2 = 1) : Omega1 T = T :=
  le_antisymm (omega1_le T) fun t ht => mem_omega1 ht (h t ht)

theorem conj_mem_omega1 {T : Subgroup G} {n : G} (hn : n ∈ Subgroup.normalizer (T : Set G))
    {x : G} (hx : x ∈ Omega1 T) : n * x * n⁻¹ ∈ Omega1 T := by
  have h : Omega1 T ≤ (Omega1 T).comap (MulAut.conj n).toMonoidHom := by
    refine (Subgroup.closure_le _).2 fun t ht => ?_
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    change n * t * n⁻¹ ∈ Omega1 T
    refine mem_omega1 ((Subgroup.mem_normalizer_iff.mp hn t).mp ht.1) ?_
    rw [conj_pow, ht.2, mul_one, mul_inv_cancel]
  exact h hx

theorem normalizer_le_normalizer_omega1 (T : Subgroup G) :
    Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer ((Omega1 T : Subgroup G) : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨conj_mem_omega1 hn, fun hx => ?_⟩
  have h := conj_mem_omega1 ((Subgroup.normalizer _).inv_mem hn) hx
  simpa [mul_assoc] using h

end Omega

section Bender

variable {X : Type} [Group X] [Finite X]

theorem omega1_eq_sylowCenter_of_bender
    (hX : fusionIsBenderGroup X) (T : Sylow 2 X) :
    Omega1 (T : Subgroup X) = sylowCenter (T : Subgroup X) := by
  obtain ⟨q, k, hq4, hB⟩ := (benderData_of_isBenderGroup hX).borel
  obtain ⟨-, hZ2, -, -⟩ := benderBorel_sylowCenter hB T
  refine le_antisymm ((Subgroup.closure_le _).2 fun t ht => ?_) fun z hz => ?_
  · exact mem_sylowCenter_of_sq_eq_one hB (by omega) T ht.1 ht.2
  · exact mem_omega1 (sylowCenter_le _ hz) (hZ2 z hz)

theorem omega1_props_of_bender
    (hX : fusionIsBenderGroup X) (T : Sylow 2 X) :
    4 ≤ Nat.card (Omega1 (T : Subgroup X)) ∧
    ∀ x ∈ Omega1 (T : Subgroup X), ∀ y ∈ Omega1 (T : Subgroup X), x ≠ 1 → y ≠ 1 →
      ∃ n ∈ Subgroup.normalizer ((Omega1 (T : Subgroup X) : Subgroup X) : Set X),
        n⁻¹ * x * n = y := by
  obtain ⟨q, k, hq4, hB⟩ := (benderData_of_isBenderGroup hX).borel
  obtain ⟨hSE, hZ2, hZcard, -⟩ := benderBorel_sylowCenter hB T
  have hΩ := omega1_eq_sylowCenter_of_bender hX T
  refine ⟨by rw [hΩ, hZcard]; exact hq4, fun x hx y hy hx1 hy1 => ?_⟩
  rw [hΩ] at hx hy
  obtain ⟨n, hn, hxy⟩ := normalizer_transitive_center hSE hZ2 hx hy hx1 hy1
  exact ⟨n, normalizer_le_normalizer_omega1 _ hn, hxy⟩

theorem sq_eq_one_of_bender_of_comm
    (hX : fusionIsBenderGroup X) (T : Sylow 2 X)
    (hT : IsMulCommutative (T : Subgroup X)) {t : X} (ht : t ∈ (T : Subgroup X)) :
    t ^ 2 = 1 := by
  obtain ⟨q, k, hq4, hB⟩ := (benderData_of_isBenderGroup hX).borel
  obtain ⟨-, hZ2, -, -⟩ := benderBorel_sylowCenter hB T
  refine hZ2 t (mem_sylowCenter.mpr ⟨ht, fun s hs => ?_⟩)
  exact congrArg Subtype.val (hT.is_comm.comm ⟨s, hs⟩ ⟨t, ht⟩)

theorem isMulCommutative_of_psl2_even
    {f : ℕ} (hf : 2 ≤ f) (e : X ≃* PSL(2, GaloisField 2 f))
    (T : Sylow 2 X) : IsMulCommutative (T : Subgroup X) := by
  have : Finite PSL(2, GaloisField 2 f) := Finite.of_equiv X e.toEquiv
  have hB := (CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_1
    f hf).map_mulEquiv e.symm
  obtain ⟨-, -, hZ, hT⟩ := benderBorel_sylowCenter hB T
  have hle := le_sylowCenter_of_card (T := (T : Subgroup X)) (by rw [hZ, hT, pow_one])
  exact ⟨⟨fun a b => Subtype.ext ((mem_sylowCenter.mp (hle b.2)).2 a a.2)⟩⟩

omit [Finite X] in
theorem exists_ne_one_of_two_lt {S : Subgroup X} [Finite S] (h : 2 < Nat.card S) :
    ∃ a ∈ S, ∃ b ∈ S, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  classical
  have : Fintype S := Fintype.ofFinite _
  obtain ⟨a, b, c, hab, hac, hbc⟩ :=
    (Fintype.two_lt_card_iff (α := S)).mp (by rwa [← Nat.card_eq_fintype_card])
  have hne : ∀ u v : S, u ≠ v → (u : X) ≠ v := fun u v h h' => h (Subtype.ext h')
  have h1 : ∀ u : S, u ≠ 1 → (u : X) ≠ 1 := fun u h h' => h (Subtype.ext h')
  by_cases ha : a = 1
  · exact ⟨b, b.2, c, c.2, h1 b fun h => hab (ha.trans h.symm),
      h1 c fun h => hac (ha.trans h.symm), hne b c hbc⟩
  by_cases hb : b = 1
  · exact ⟨a, a.2, c, c.2, h1 a ha, h1 c fun h => hbc (hb.trans h.symm), hne a c hac⟩
  · exact ⟨a, a.2, b, b.2, h1 a ha, h1 b hb, hne a b hab⟩

theorem commutator_le_sylowCenter_of_bender
    (hX : fusionIsBenderGroup X) (T : Sylow 2 X) :
    ⁅(T : Subgroup X), (T : Subgroup X)⁆ ≤ sylowCenter (T : Subgroup X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨q, k, hq4, hB⟩ := (benderData_of_isBenderGroup hX).borel
  obtain ⟨-, ⟨D, hDcyc, -, -, hsup⟩, -, -, -⟩ := hB T
  obtain ⟨hSE, hZ2, hZcard, -⟩ := benderBorel_sylowCenter hB T
  by_cases hab : IsMulCommutative (T : Subgroup X)
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_eq_one_iff_mul_comm.mpr
      (congrArg Subtype.val (hab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))]
    exact (sylowCenter _).one_mem
  have hDle : D ≤ Subgroup.normalizer ((T : Subgroup X) : Set X) := by
    rw [← hsup]
    exact le_sup_right
  have hinv : ∀ x : (T : Subgroup X), orderOf x = 2 →
      (x : X) ∈ sylowCenter (T : Subgroup X) ∧ (x : X) ≠ 1 := by
    intro x hx
    have hx2 : x ^ 2 = 1 := by
      have h := pow_orderOf_eq_one x
      rwa [hx] at h
    refine ⟨mem_sylowCenter_of_sq_eq_one hB (by omega) T x.2 (by
      simpa using congrArg Subtype.val hx2), fun h => ?_⟩
    have h1 : x = 1 := Subtype.ext h
    rw [h1, orderOf_one] at hx
    omega
  have hord : ∀ z (hz : z ∈ sylowCenter (T : Subgroup X)), z ≠ 1 →
      orderOf (⟨z, sylowCenter_le _ hz⟩ : (T : Subgroup X)) = 2 := by
    intro z hz hz1
    refine orderOf_eq_prime (Subtype.ext (by simpa using hZ2 z hz)) fun h => hz1 ?_
    exact congrArg Subtype.val h
  have hS : CFSG.GroupTheory.IsSuzukiTwoGroup (T : Subgroup X) := by
    refine ⟨inferInstance, T.isPGroup', hab, ?_, (conjAct hDle).range, ?_, ?_⟩
    · obtain ⟨a, ha, b, hb, ha1, hb1, hab'⟩ :=
        exists_ne_one_of_two_lt (S := sylowCenter (T : Subgroup X)) (by omega)
      exact ⟨_, _, hord a ha ha1, hord b hb hb1, fun h => hab' (congrArg Subtype.val h)⟩
    · have : IsCyclic D := hDcyc
      exact isCyclic_of_surjective _ (conjAct hDle).rangeRestrict_surjective
    · intro x y hx hy
      obtain ⟨hxZ, hx1⟩ := hinv x hx
      obtain ⟨hyZ, hy1⟩ := hinv y hy
      obtain ⟨n, hn, hny⟩ := normalizer_transitive_center hSE hZ2 hxZ hyZ hx1 hy1
      rw [← hsup] at hn
      have hn' : n ∈ ((T : Subgroup X) : Set X) * (D : Set X) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hDle]
        exact hn
      obtain ⟨t, ht, d, hd, rfl⟩ := Set.mem_mul.mp hn'
      refine ⟨conjAct hDle ⟨d⁻¹, D.inv_mem hd⟩, ⟨_, rfl⟩, Subtype.ext ?_⟩
      rw [conjAct_apply]
      have htx : t * (x : X) = x * t := (mem_sylowCenter.mp hxZ).2 t ht
      change d⁻¹ * (x : X) * d⁻¹⁻¹ = y
      rw [← hny]
      calc d⁻¹ * (x : X) * d⁻¹⁻¹ = d⁻¹ * (t⁻¹ * (t * x)) * d := by group
        _ = d⁻¹ * (t⁻¹ * (x * t)) * d := by rw [htx]
        _ = (t * d)⁻¹ * x * (t * d) := by group
  obtain ⟨-, hZΦ, hΦC, -⟩ := hS.higman
  rw [← Subgroup.map_subtype_commutator, ← hΦC, ← hZΦ, map_center_eq_sylowCenter]

theorem centralizer_le_of_card_sylow {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    {R : Sylow 2 G}
    (hSE : fusionStronglyEmbedded (Subgroup.normalizer ((R : Subgroup G) : Set G)))
    (hcard : Nat.card (Sylow 2 G) = Nat.card (R : Subgroup G) + 1) :
    Subgroup.centralizer ((R : Subgroup G) : Set G) ≤ R := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro c hc
  have hcomm : ∀ r ∈ (R : Subgroup G), Commute r c := Subgroup.mem_centralizer_iff.mp hc
  have hcN : c ∈ Subgroup.normalizer ((R : Subgroup G) : Set G) :=
    Subgroup.centralizer_le_normalizer _ hc
  have hcR : c • R = R := Sylow.smul_eq_iff_mem_normalizer.mpr hcN
  have h2 : 1 < Nat.card (Sylow 2 G) := by
    rw [hcard]
    have := Nat.card_pos (α := (R : Subgroup G))
    omega
  have : Nontrivial (Sylow 2 G) := Finite.one_lt_card_iff_nontrivial.mp h2
  obtain ⟨S₀, h₀⟩ := exists_ne R
  have hcS₀ : c • S₀ ≠ R := by
    intro h
    apply h₀
    calc S₀ = c⁻¹ • (c • S₀) := (inv_smul_smul c S₀).symm
      _ = c⁻¹ • (c • R) := by rw [h, hcR]
      _ = R := inv_smul_smul c R
  obtain ⟨r, hr, hrS⟩ :=
    CFSG.ComponentClassification.AschbacherToolkit.Bender.Omega.exists_smul_eq hSE hcard h₀ hcS₀
  have hpow : ∀ n : ℕ, c ^ n • S₀ = r ^ n • S₀ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, mul_smul, ← hrS, ← mul_smul, ← ((hcomm r hr).pow_right n).eq, mul_smul, ih,
        ← mul_smul, ← pow_succ']
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp R.isPGroup'
  have hrN : r ^ (2 ^ k) = 1 := by
    have h := pow_card_eq_one' (G := (R : Subgroup G)) (x := ⟨r, hr⟩)
    rw [hk] at h
    simpa using congrArg Subtype.val h
  have hd0 : c ^ (2 ^ k) • S₀ = S₀ := by rw [hpow, hrN, one_smul]
  have hfix : ∀ S : Sylow 2 G, MulAut.conj (c ^ (2 ^ k)) • S = S := by
    intro S
    rw [← Sylow.smul_def]
    by_cases hS : S = R
    · rw [hS]
      exact Sylow.smul_eq_iff_mem_normalizer.mpr ((Subgroup.normalizer _).pow_mem hcN _)
    · obtain ⟨r', hr', rfl⟩ :=
        CFSG.ComponentClassification.AschbacherToolkit.Bender.Omega.exists_smul_eq hSE hcard
          h₀ hS
      rw [← mul_smul, ← ((hcomm r' hr').pow_right (2 ^ k)).eq, mul_smul, hd0]
  have hconj : MulAut.conj (c ^ (2 ^ k)) = 1 :=
    CFSG.ComponentClassification.AschbacherToolkit.Bender.Omega.eq_one_of_forall_smul_eq R hSE.1
      _ hfix
  have hcenter : Subgroup.center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · exact h
    · exfalso
      apply hSE.1
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_normalizer_iff]
      intro t
      have hx : x ∈ Subgroup.center G := by rw [h]; exact Subgroup.mem_top x
      rw [← (Subgroup.mem_center_iff.mp hx t), mul_inv_cancel_right]
  have hc1 : c ^ (2 ^ k) = 1 := by
    have h := mem_center_of_conj_eq_one hconj
    rwa [hcenter, Subgroup.mem_bot] at h
  have hp : IsPGroup 2 (Subgroup.zpowers c) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hc1)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hmem : c ∈ Subgroup.zpowers c ⊓ (R : Subgroup G) := by
    rw [← hp.inf_normalizer_sylow R]
    exact ⟨Subgroup.mem_zpowers c, hcN⟩
  exact hmem.2

theorem card_sylow_eq_card_add_one_of_mulEquiv {G G' : Type*} [Group G] [Group G'] [Finite G]
    (e : G ≃* G') {R' : Sylow 2 G'}
    (h : Nat.card (Sylow 2 G') = Nat.card (R' : Subgroup G') + 1) (R : Sylow 2 G) :
    Nat.card (Sylow 2 G) = Nat.card (R : Subgroup G) + 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite G' := Finite.of_equiv G e.toEquiv
  rw [card_sylow_eq_of_mulEquiv e 2, h, Sylow.card_eq_multiplicity R',
    Sylow.card_eq_multiplicity R, Nat.card_congr e.toEquiv]

open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
  CFSG.ComponentClassification.AschbacherToolkit.Bender in
theorem card_sylow_of_bender
    (hX : fusionIsBenderGroup X) (R : Sylow 2 X) :
    Nat.card (Sylow 2 X) = Nat.card (R : Subgroup X) + 1 := by
  rcases hX with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · have : Finite PSL(2, GaloisField 2 f) := Finite.of_equiv X e.toEquiv
    obtain ⟨R'⟩ := (inferInstance : Nonempty (Sylow 2 PSL(2, GaloisField 2 f)))
    obtain ⟨-, -, -, hR'⟩ := benderBorel_sylowCenter
      (CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_1 f hf) R'
    refine card_sylow_eq_card_add_one_of_mulEquiv e (R' := R') ?_ R
    rw [CFSG.Walter.psl2_even_card_sylow (by omega), hR', pow_one]
  · let k := GaloisField 2 f
    let K := FiniteField.Extension k 2 2
    let J := binaryQuadraticHermitian f (by omega)
    let : CharP K 2 := CharP.of_ringHom_of_ne_zero (algebraMap k K) 2 (by norm_num)
    have hKcard : Nat.card K = (2 ^ f) ^ 2 := by
      rw [FiniteField.natCard_extension, GaloisField.card 2 f (by omega)]
    have hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f :=
      quadraticBinaryFrobenius_fixed_card f (by omega)
    have hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl
    let e₁ := (projectiveSpecialUnitary_equiv_PSU3Model J f hf hJ hKcard hfixed).some
    have hmodel : PSU3Model f = PSU3 2 f := CFSG.Models.benderPSU3Model_eq_psu3 f
    let e₂ : ProjectiveSpecialUnitaryMatrixGroup J ≃* PSU3 2 f :=
      e₁.trans (MulEquiv.subgroupCongr hmodel)
    obtain ⟨S, hS⟩ := UnitaryAut.exists_sylow_eq_root J f hf hKcard hfixed hJ
    have h := (UnitaryAut.normalizer_and_card_sylow J f hf hKcard hfixed hJ).2
    rw [← hS] at h
    exact card_sylow_eq_card_add_one_of_mulEquiv (e.trans e₂.symm) h R
  · let e' : X ≃* SuzukiMatrixGroup a := e.trans (SuzukiAut.suzukiEquiv a).symm
    obtain ⟨S, hS⟩ := SuzukiAut.exists_sylow_eq_rootSub a (by omega)
    have h := (SuzukiAut.normalizer_and_card_sylow a (by omega)).2
    rw [← hS] at h
    exact card_sylow_eq_card_add_one_of_mulEquiv e' h R

theorem centralizer_le_of_bender
    (hX : fusionIsBenderGroup X) (T : Sylow 2 X) :
    Subgroup.centralizer ((T : Subgroup X) : Set X) ≤ T := by
  have hD := benderData_of_isBenderGroup hX
  obtain ⟨q, k, -, hB⟩ := hD.borel
  have : IsSimpleGroup X := hD.simple
  exact centralizer_le_of_card_sylow (hB T).1 (card_sylow_of_bender hX T)

end Bender

end CFSG.Goldschmidt.GoldType
