module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListSp4
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6A312Over

public section

namespace CFSG.QuasithinUnique.Unc25G2

namespace A312Sub

open Matrix CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Setup.X6
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot
open CFSG.QuasithinUnique.Vol2Native.A312L

@[expose] def Q1 {X : Type} [Group X] (B : Subgroup X) : Prop :=
  ∃ n : ℕ, IsPSL 2 2 n (ModO2 B)

theorem Q1.of_mulEquiv {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y] (e : X ≃* Y)
    {B : Subgroup X} (h : Q1 (B.map e.toMonoidHom)) : Q1 B := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, IsPSL.of_mulEquiv (A312.modO2Equiv (mapEquiv e B)) hn⟩

section Levi

variable {K : Type} [Field K]

theorem over_of_rank2_levi {S : Type} [Group S] [Finite S] (hq : CFSG.IsQuasisimple S)
    {U : Subgroup S} {P : Fin 2 → Subgroup S} (hU : IsSylowTwoOf U ⊤)
    (hP : ResidualOvergroupsAt S U P) [Finite K] [CharP K 2] {f : ℕ} (hf : Nat.card K = 2 ^ f)
    (hf2 : 2 ≤ f) (g : ∀ j, ↥(perfectCore (P j)) →* SpecialLinearGroup (Fin 2) K)
    (hg : ∀ j, Function.Surjective (g j)) (hker : ∀ j, IsPGroup 2 (g j).ker) :
    Over S Q1 := by
  have hK4 : ∃ s : Finset K, s.card = 4 := by
    refine exists_finset_card_four ?_
    rw [hf]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  have hsimple := sl2_isSimple hK4
  have hnab := sl2_nonabelian hK4
  have hsolvker : ∀ j, Group.IsSolvable (g j).ker := by
    intro j
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := (hker j).isNilpotent
    infer_instance
  refine Over.of_sylow (fun e B h => Q1.of_mulEquiv e h) U hU fun B hB hBtop => ?_
  obtain ⟨j, rfl⟩ := rank2_eq_perfectCore hq hP
    (fun j => ⟨SpecialLinearGroup (Fin 2) K, inferInstance, hsimple, hnab, g j, hg j, hsolvker j⟩)
    hB hBtop
  have h2f : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  exact ⟨f, ⟨Nat.prime_two, by omega, le_rfl, by
      intro h
      have := congrArg Prod.snd h
      simp only at this
      omega, by
      intro h
      have := congrArg Prod.snd h
      simp only at this
      omega⟩, K, inferInstance, inferInstance, hf,
    ⟨(modO2EquivOfHom hnab (g j) (hg j) (hker j)).trans sl2EquivStatedProj⟩⟩

end Levi

theorem over_of_rank2_solvable {S : Type} [Group S] [Finite S] (hq : CFSG.IsQuasisimple S)
    {U : Subgroup S} {P : Fin 2 → Subgroup S} (hU : IsSylowTwoOf U ⊤)
    (hP : ResidualOvergroupsAt S U P) (hsolv : ∀ j, perfectCore (P j) = ⊥) :
    Over S (fun _ => False) := by
  refine over_of_solvable_overgroups hq U hU fun M hUM hMtop => ?_
  by_contra hns
  obtain ⟨j, -, hd⟩ := hP.2.2.2.2.1 M hUM hMtop hns
  apply hns
  rw [isSolvable_iff_perfectCore_eq_bot, ← dInf_eq_perfectCore, hd, dInf_eq_perfectCore]
  exact hsolv j

section Three

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K] [Finite K]

theorem over_linear3 [CharP K 2] {f : ℕ} (hf : Nat.card K = 2 ^ f) {S : Type} [Group S]
    [Finite S] (hq : CFSG.IsQuasisimple S) (π : SpecialLinearGroup (Fin 3) K →* S)
    (hπ : Function.Surjective π) (hker : π.ker ≤ scalars 3 K)
    (hSyl : IsSylowTwoOf ((unitriangular 3 K).map π) ⊤) : Over S Q1 := by
  have hK : ∃ k : ℕ, Nat.card K = 2 ^ k := ⟨f, hf⟩
  have hres := linear_three_residual_of_cover hK π hπ hker
  have hinj : ∀ j : Fin 2, ∀ x ∈ perfectCore (Q3 K j), ∀ y ∈ perfectCore (Q3 K j),
      π x = π y → x = y := by
    intro j x hx y hy hxy
    have hz : x⁻¹ * y ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
    have hzN : x⁻¹ * y ∈ perfectCore (Q3 K j) := mul_mem (inv_mem hx) hy
    have h1 := blk3_scalars j ⟨x⁻¹ * y, hzN⟩ (hker hz)
    exact inv_mul_eq_one.mp (congrArg Subtype.val h1)
  have hpos : 1 < Nat.card K := Finite.one_lt_card
  by_cases h4 : 4 ≤ Nat.card K
  · have hK4 := exists_finset_card_four h4
    have hf2 : 2 ≤ f := by
      by_contra hlt
      rw [hf] at h4
      have : f ≤ 1 := by omega
      have h2 : 2 ^ f ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
      omega
    let eN : ∀ j : Fin 2, ↥(perfectCore (Q3 K j)) ≃* ↥(perfectCore ((Q3 K j).map π)) :=
      fun j => perfectCoreMapEquiv π (Q3 K j) (hinj j)
    refine over_of_rank2_levi hq hSyl hres hf hf2
      (fun j => (blk3 j).comp (eN j).symm.toMonoidHom)
      (fun j => (blk3_surjective hK4 j).comp (eN j).symm.surjective) fun j z => ?_
    obtain ⟨k, hk⟩ := blk3_ker_isPGroup hK j ⟨(eN j).symm z.1, z.2⟩
    have h1 : ((eN j).symm z.1) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    refine ⟨k, Subtype.ext ?_⟩
    show z.1 ^ 2 ^ k = 1
    have : (eN j).symm (z.1 ^ 2 ^ k) = 1 := by rw [map_pow]; exact h1
    exact (map_eq_one_iff _ (eN j).symm.injective).mp this
  · have hf1 : f = 1 := by
      by_contra hne
      rcases Nat.lt_or_ge f 2 with hlt | hge
      · have : f = 0 := by omega
        subst this
        simp at hf
        omega
      · apply h4
        rw [hf]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hge
    subst hf1
    have hK2 : Nat.card K = 2 := by rw [hf]; norm_num
    have hbot : ∀ j : Fin 2, perfectCore (Q3 K j) = ⊥ := by
      intro j
      have hSL : Group.IsSolvable (SpecialLinearGroup (Fin 2) K) := by
        refine isSolvable_of_card_two_three (a := 1) (b := 1) ?_
        rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK2]
        norm_num
      have hkerS : Group.IsSolvable (blk3 (K := K) j).ker := by
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        have := (blk3_ker_isPGroup hK j).isNilpotent
        infer_instance
      have hN : Group.IsSolvable ↥(perfectCore (Q3 K j)) :=
        Group.isSolvable_of_ker_le_range (blk3 (K := K) j).ker.subtype (blk3 j)
          (by rw [Subgroup.range_subtype])
      have := (isSolvable_iff_perfectCore_eq_bot (perfectCore (Q3 K j))).mp hN
      rwa [perfectCore_eq_self_of_perfect (perfectCore_perfect _)] at this
    exact Over.of_false (over_of_rank2_solvable hq hSyl hres
      (fun j => by rw [← map_perfectCore, hbot j, Subgroup.map_bot]))

theorem over_projectiveSL3 [CharP K 2] {f : ℕ} (hf : Nat.card K = 2 ^ f)
    (hq : CFSG.IsQuasisimple (projectiveSL 3 K)) : Over (projectiveSL 3 K) Q1 := by
  obtain ⟨P, hP⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := 3) (by norm_num)
  have hT₀ : IsSylowTwoOf (projUnitriangular 3 K) ⊤ :=
    hP ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
  exact over_linear3 hf hq (proj 3 K) (proj_surjective 3 K) (ker_proj 3 K).le hT₀

theorem over_l3even : ∀ (X : Type) [Group X] [Finite X] (f : ℕ), CFSG.IsQuasisimple X → 1 ≤ f →
    IsPSL 3 2 f X → Over X Q1 := by
  intro X _ _ f hq hf hX
  obtain ⟨-, K, hF, hFin, hcard, ⟨e⟩⟩ := hX
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hcard
  let e' : X ≃* projectiveSL 3 K := e.trans (statedSLEquivProjectiveSL 3 K)
  have hq' : CFSG.IsQuasisimple (projectiveSL 3 K) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e' hq
  exact Over.of_mulEquiv e' (fun B h => Q1.of_mulEquiv e' h) (over_projectiveSL3 hcard hq')

end Three

section Sp4

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

variable {K : Type} [Field K] [Finite K]

theorem over_projSp4 [CharP K 2] {f : ℕ} (hf : Nat.card K = 2 ^ f) (hf2 : 2 ≤ f)
    (hq : CFSG.IsQuasisimple (StatedProj (StatedSp 2 K))) :
    Over (StatedProj (StatedSp 2 K)) Q1 := by
  have hK : ∃ k : ℕ, Nat.card K = 2 ^ k := ⟨f, hf⟩
  have hK4 : ∃ s : Finset K, s.card = 4 := by
    refine exists_finset_card_four ?_
    rw [hf]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  have hres : ResidualOvergroupsAt (StatedProj (StatedSp 2 K)) (projUnipotent 2 K)
      (fun j : Fin 2 => (Q2 K j).map (proj 2 K)) := symplectic_two_residualOvergroupsAt hK
  obtain ⟨P, hP⟩ := exists_sylow_projUnipotent (K := K) 2 (r := 2) (by norm_num)
  have hU : IsSylowTwoOf (projUnipotent 2 K) ⊤ :=
    hP ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
  have hinj : ∀ j : Fin 2, ∀ x ∈ perfectCore (Q2 K j), ∀ y ∈ perfectCore (Q2 K j),
      proj 2 K x = proj 2 K y → x = y := fun j x _ y _ h => proj_injective_charTwo h
  let eN : ∀ j : Fin 2, ↥(perfectCore (Q2 K j)) ≃* ↥(perfectCore ((Q2 K j).map (proj 2 K))) :=
    fun j => perfectCoreMapEquiv (proj 2 K) (Q2 K j) (hinj j)
  refine over_of_rank2_levi hq hU hres hf hf2
    (fun j => (blkN j).comp (eN j).symm.toMonoidHom)
    (fun j => (blkN_surjective hK4 j).comp (eN j).symm.surjective) fun j z => ?_
  obtain ⟨k, hk⟩ := blkN_ker_isPGroup hK j ⟨(eN j).symm z.1, z.2⟩
  have h1 : ((eN j).symm z.1) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  refine ⟨k, Subtype.ext ?_⟩
  show z.1 ^ 2 ^ k = 1
  have : (eN j).symm (z.1 ^ 2 ^ k) = 1 := by rw [map_pow]; exact h1
  exact (map_eq_one_iff _ (eN j).symm.injective).mp this

end Sp4

theorem over_sp4 : ∀ (X : Type) [Group X] [Finite X] (f : ℕ), CFSG.IsQuasisimple X → 2 ≤ f →
    IsPSp4 2 f X → Over X Q1 := by
  intro X _ _ f hq hf hX
  obtain ⟨-, K, hF, hFin, hcard, ⟨e⟩⟩ := hX
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hcard
  have hq' := CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq
  exact Over.of_mulEquiv e (fun B h => Q1.of_mulEquiv e h) (over_projSp4 hcard hf hq')


end A312Sub

end CFSG.QuasithinUnique.Unc25G2
