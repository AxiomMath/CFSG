module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBG2Basic
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBG2Split
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBG2ThreeRoots
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67A2Sylow
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67A2Diag
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67A2Torus
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67A2Hom
public import CFSG.RankThree.Chevalley.SteinbergCAG2ToralPrimePlane
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcConj
public import CFSG.LieType.Chevalley.RootCharacterConjugation
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LieType.Chevalley.SignKernelComponentPerfect
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.Chevalley.SteinbergCEG2EvenLocalCoreCommutator
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.Walter.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.RankThree.Chevalley
  CFSG.RankThree.Chevalley.EvenG2 CFSG.GH74.GLS.Stage2.Bender.Thm1
open CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.RankTwo
open scoped Pointwise commutatorElement MatrixGroups

local notation "RA2" => CFSG.LieType.RootSystem.roots
  (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A 2) (∅ : Set (Fin 2))

section Numbers

theorem natCard_torusGroup_G2
    (K : Type) [Field K] [Finite K] :
    Nat.card (torusGroup .G2 K) = (Nat.card K - 1) ^ 2 := by
  obtain ⟨e, -⟩ := G2_F4_torus_coordinates .G2 (Or.inl rfl) K
  rw [← Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_units]
  simp [Tag.rank]

theorem factorization_three_lt_sl3 {q : ℕ} (hq : 4 ≤ q) (h3 : 3 ∣ q - 1) :
    ((q - 1) ^ 2 * (1 + q)).factorization 3 <
      (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))).factorization 3 := by
  have hid : q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) =
      ((q - 1) ^ 2 * (1 + q)) * (q ^ 3 * (q ^ 2 + q + 1)) := by
    have h1 : 1 ≤ q := by omega
    have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ h1
    have h3' : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ h1
    zify [h1, h2, h3']
    ring
  have hA : (q - 1) ^ 2 * (1 + q) ≠ 0 := by
    have : 0 < q - 1 := by omega
    positivity
  have hC : q ^ 3 * (q ^ 2 + q + 1) ≠ 0 := by positivity
  have hdvd : 3 ∣ q ^ 3 * (q ^ 2 + q + 1) := by
    refine Dvd.dvd.mul_left ?_ _
    obtain ⟨k, hk⟩ := h3
    have hqk : q = 3 * k + 1 := by omega
    subst hqk
    exact ⟨3 * k ^ 2 + 3 * k + 1, by ring⟩
  rw [hid, Nat.factorization_mul hA hC, Finsupp.add_apply]
  have := Nat.Prime.factorization_pos_of_dvd Nat.prime_three hC hdvd
  omega

end Numbers

section Diag


private theorem cube_root_of_orderOf_eq_three'' {L : Type} [Field L] {ζ : Lˣ}
    (hζ : orderOf ζ = 3) : (ζ : L) ^ 2 + (ζ : L) + 1 = 0 ∧ (ζ : L) ≠ 1 := by
  have hζ1 : (ζ : L) ≠ 1 := fun h => by
    have : ζ = 1 := Units.ext h
    rw [this, orderOf_one] at hζ
    omega
  refine ⟨?_, hζ1⟩
  have h3 : (ζ : L) ^ 3 = 1 := by
    have := pow_orderOf_eq_one ζ
    rw [hζ] at this
    exact congrArg Units.val this |>.trans (by simp)
  have h0 : ((ζ : L) - 1) * ((ζ : L) ^ 2 + (ζ : L) + 1) = 0 := by linear_combination h3
  exact (mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hζ1)

theorem exists_conj_to_diag_three (K : Type) [Field K] [Finite K] (h3 : 3 ∣ Nat.card K - 1)
    {x : adjointGroup .G2 K} (hx : orderOf x = 3) :
    ∃ ι : Matrix.SpecialLinearGroup (Fin 3) K →* ↥(adjointGroup .G2 K), Function.Injective ι ∧
      (∀ γ ∈ RA2, ∀ c : K, ι (CFSG.LieType.Steinberg.SL.x 2 K γ c) = a2y γ c) ∧
      ∃ (g : ↥(adjointGroup .G2 K)) (s : Matrix.SpecialLinearGroup (Fin 3) K),
        (∀ i j : Fin 3, i ≠ j → (s : Matrix (Fin 3) (Fin 3) K) i j = 0) ∧ ι s = g * x * g⁻¹ := by
  classical
  obtain ⟨ι, hι, hιx⟩ := exists_a2Hom_injective (K := K)
  have hE : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨y, hy⟩ := exists_conj_le_range_of_three_dvd_sub_one h3 ι hι (Subgroup.zpowers x) hE
  have hyx : y * x * y⁻¹ ∈ ι.range := hy ⟨x, Subgroup.mem_zpowers x, rfl⟩
  obtain ⟨s, hs⟩ := hyx
  obtain ⟨ζ, hζ⟩ := exists_units_orderOf_eq_of_dvd_card_sub_one (k := K) Nat.prime_three h3
  obtain ⟨hω, hω1⟩ := cube_root_of_orderOf_eq_three'' hζ
  have hs3 : s ^ 3 = 1 := by
    apply hι
    rw [map_pow, hs, map_one]
    have : (y * x * y⁻¹) ^ 3 = y * x ^ 3 * y⁻¹ := by
      rw [conj_pow]
    rw [this, ← hx, pow_orderOf_eq_one]
    group
  obtain ⟨y₂, hy₂⟩ := exists_diagonalizing_of_commuting_cube_one (ζ : K) hω hω1
    (Subgroup.zpowers s)
    (fun z hz => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hs3, one_zpow])
    (fun z hz z' hz' => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
      obtain ⟨k', rfl⟩ := Subgroup.mem_zpowers_iff.1 hz'
      exact (Commute.zpow_zpow_self s k k').eq)
  refine ⟨ι, hι, hιx, ι y₂ * y, y₂ * s * y₂⁻¹, hy₂ s (Subgroup.mem_zpowers s), ?_⟩
  rw [map_mul, map_mul, map_inv, hs]
  group

end Diag

section Central


theorem mem_center_of_rootChar_g2a_eq_one (K : Type) [Field K] [Finite K] [CharP K 2]
    (ι : Matrix.SpecialLinearGroup (Fin 3) K →* ↥(adjointGroup .G2 K))
    (hι : Function.Injective ι)
    (hιx : ∀ γ ∈ RA2, ∀ c : K, ι (CFSG.LieType.Steinberg.SL.x 2 K γ c) = a2y γ c)
    {a : Fin Tag.G2.rank → Kˣ} (hap : a ^ 3 = 1) (ha0 : rootChar a g2a = 1)
    {s : Matrix.SpecialLinearGroup (Fin 3) K}
    (hd : ∀ i j : Fin 3, i ≠ j → (s : Matrix (Fin 3) (Fin 3) K) i j = 0)
    (hs : ((ι s : ↥(adjointGroup .G2 K)) : ModGL .G2 K) = rootDiagUnit .G2 a) :
    s ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) := by
  classical
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have hcomm : ∀ {β : Fin Tag.G2.rank → ℤ}, IsRoot .G2 β → rootChar a β = 1 → ∀ c : K,
      (rootDiagUnit .G2 a : ModGL .G2 K) * pinnedX .G2 K β c =
        pinnedX .G2 K β c * rootDiagUnit .G2 a := by
    intro β hβ hχ c
    have h := rootDiagUnit_conj_pinnedX (K := K) a hβ c
    rw [hχ, Units.val_one, one_mul] at h
    exact mul_inv_eq_iff_eq_mul.1 h
  have hx1 : IsRoot .G2 (Pi.single (⟨0, by decide⟩ : Fin Tag.G2.rank) (1 : ℤ)) :=
    isRoot_single .G2 _
  have hx3 : IsRoot .G2 (g2CommRoot 3) := root_isRoot 3 (by norm_num)
  have hg2a : (Pi.single (⟨0, by decide⟩ : Fin Tag.G2.rank) (1 : ℤ)) = g2a := by
    rw [g2a_eq_single]
    rfl
  have hχ1 : rootChar a (Pi.single (⟨0, by decide⟩ : Fin Tag.G2.rank) (1 : ℤ)) = 1 := by
    rw [hg2a]
    exact ha0
  have hχ3 : rootChar a (g2CommRoot 3) = 1 := by
    have hr3 : (g2CommRoot 3 : Fin Tag.G2.rank → ℤ) = g2a + (3 : ℤ) • g2r := by
      decide +kernel
    have hr : rootChar a g2r ^ (3 : ℤ) = 1 := by
      have := rootChar_pow_of_pow_eq_one hap g2r
      simpa [zpow_ofNat] using this
    rw [hr3, rootChar_add, rootChar_zsmul, ha0, hr, one_mul]
  have hc01 : ∀ c : K, ι s * ι (Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 3) ≠ 1 by decide) c) = ι (Matrix.SpecialLinearGroup.transvection
        (show (0 : Fin 3) ≠ 1 by decide) c) * ι s := by
    intro c
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hs, phi_T01 ι hιx c,
      CFSG.StandardType.RootCentExc.coe_xPar_eq_pinnedX h2 _ hx1 c]
    exact hcomm hx1 hχ1 c
  have hc12 : ∀ c : K, ι s * ι (Matrix.SpecialLinearGroup.transvection
      (show (1 : Fin 3) ≠ 2 by decide) c) = ι (Matrix.SpecialLinearGroup.transvection
        (show (1 : Fin 3) ≠ 2 by decide) c) * ι s := by
    intro c
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hs, phi_T12 ι hιx c,
      CFSG.StandardType.RootCentExc.coe_xPar_eq_pinnedX h2 _ hx3 c]
    exact hcomm hx3 hχ3 c
  have hsT01 : s * Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) 1 =
      Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) 1 * s := by
    apply hι
    rw [map_mul, map_mul]
    exact hc01 1
  have hsT12 : s * Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) 1 =
      Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) 1 * s := by
    apply hι
    rw [map_mul, map_mul]
    exact hc12 1
  have e01 := congrArg (fun m : Matrix.SpecialLinearGroup (Fin 3) K =>
    (m : Matrix (Fin 3) (Fin 3) K) 0 1) hsT01
  have e12 := congrArg (fun m : Matrix.SpecialLinearGroup (Fin 3) K =>
    (m : Matrix (Fin 3) (Fin 3) K) 1 2) hsT12
  simp only [Matrix.SpecialLinearGroup.coe_mul, CFSG.LinearGroups.coe_transvection] at e01 e12
  have h01 : (s : Matrix (Fin 3) (Fin 3) K) 0 0 = (s : Matrix (Fin 3) (Fin 3) K) 1 1 := by
    have := e01
    simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.single_apply] at this
    linear_combination this
  have h12 : (s : Matrix (Fin 3) (Fin 3) K) 1 1 = (s : Matrix (Fin 3) (Fin 3) K) 2 2 := by
    have := e12
    simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.single_apply] at this
    linear_combination this
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  have hsc : (s : Matrix (Fin 3) (Fin 3) K) =
      Matrix.scalar (Fin 3) ((s : Matrix (Fin 3) (Fin 3) K) 0 0) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      fin_cases i <;> simp [Matrix.scalar_apply, h01, h12]
    · simp [Matrix.scalar_apply, hd i j hij, Matrix.diagonal_apply_ne _ hij]
  refine ⟨(s : Matrix (Fin 3) (Fin 3) K) 0 0, ?_, ?_⟩
  · have hdet := s.2
    rw [hsc] at hdet
    simpa [Matrix.det_diagonal] using hdet
  · exact hsc.symm

end Central

section BTThree


theorem oddPCoreInClosure_three_of_central_image (K : Type) [Field K] [Finite K] [CharP K 2]
    (h3 : 3 ∣ Nat.card K - 1) (h4 : 4 ≤ Nat.card K)
    (ι : Matrix.SpecialLinearGroup (Fin 3) K →* ↥(adjointGroup .G2 K)) (hι : Function.Injective ι)
    {x g : ↥(adjointGroup .G2 K)} {s : Matrix.SpecialLinearGroup (Fin 3) K}
    (hs : s ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K))
    (hg : ι s = g * x * g⁻¹) :
    OddPCoreInClosure 3 ↥(Subgroup.centralizer ({x} : Set (adjointGroup .G2 K))) := by
  classical
  have hp3K : ¬ 3 ∣ Nat.card K := fun h => by
    have h1 : 3 ∣ Nat.card K - (Nat.card K - 1) := Nat.dvd_sub h h3
    rw [Nat.sub_sub_self (Nat.card_pos (α := K))] at h1
    omega
  let F : ↥(adjointGroup .G2 K) →* ↥(adjointGroup .G2 K) := (MulAut.conj g).toMonoidHom
  have hF : Function.Injective F := (MulAut.conj g).injective
  have hFx : F x = ι s := by
    rw [hg]
    rfl
  obtain ⟨T', hT'c, hT'card⟩ : ∃ T' : Subgroup (adjointGroup .G2 K),
      T' ≤ Subgroup.centralizer ({x} : Set _) ∧ Nat.card T' = Nat.card ι.range := by
    refine ⟨ι.range.comap F, fun t ht => ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      apply hF
      rw [map_mul, map_mul, hFx]
      obtain ⟨t', ht'⟩ := Subgroup.mem_comap.1 ht
      rw [← ht', ← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hs t')]
    · have h1 : (ι.range.comap F).map F = ι.range := by
        rw [Subgroup.map_comap_eq]
        exact inf_eq_right.2 (by
          rw [MonoidHom.range_eq_top_of_surjective F (MulAut.conj g).surjective]
          exact le_top)
      calc Nat.card (ι.range.comap F) = Nat.card ((ι.range.comap F).map F) :=
            (Subgroup.card_map_of_injective hF).symm
        _ = Nat.card ι.range := by rw [h1]
  have hrange : Nat.card ι.range =
      Nat.card K ^ 3 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1)) := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hι).toEquiv,
      LinearFlag.card_SL_eq (by norm_num), show Finset.Icc 2 3 = {2, 3} by decide,
      Finset.prod_pair (by norm_num)]
  refine OddPCoreInClosure.of_odd_core fun N hN hcop => ?_
  haveI := hN
  refine odd_card_of_normal_of_big_p_part Nat.prime_three hp3K
    (Subgroup.centralizer ({x} : Set (adjointGroup .G2 K))) ?_ N hcop
  have hdvd : Nat.card T' ∣ Nat.card (Subgroup.centralizer ({x} : Set (adjointGroup .G2 K))) :=
    Subgroup.card_dvd_of_le hT'c
  have hC0 : Nat.card (Subgroup.centralizer ({x} : Set (adjointGroup .G2 K))) ≠ 0 :=
    Nat.card_pos.ne'
  have hle := (Nat.factorization_le_iff_dvd (Nat.card_pos (α := T')).ne' hC0).2 hdvd 3
  have hlt := factorization_three_lt_sl3 h4 h3
  rw [natCard_torusGroup_G2]
  rw [hT'card, hrange] at hle
  omega

end BTThree

section Main


theorem oddPCoreInClosure_centralizer_split_three (K : Type) [Field K] [Finite K] [CharP K 2]
    (h3 : 3 ∣ Nat.card K - 1) {x : adjointGroup .G2 K} (hx : orderOf x = 3) :
    OddPCoreInClosure 3 ↥(Subgroup.centralizer ({x} : Set (adjointGroup .G2 K))) := by
  classical
  have h4 : 4 ≤ Nat.card K := by
    have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
    have := Nat.le_of_dvd (by omega) h3
    omega
  obtain ⟨ι, hι, hιx, g, s, hd, hgs⟩ := exists_conj_to_diag_three K h3 hx
  have hgx : g * x * g⁻¹ ∈ (torusGroup .G2 K).subgroupOf (adjointGroup .G2 K) := by
    rw [Subgroup.mem_subgroupOf, ← hgs]
    exact phi_diag_mem_torusGroup ι hιx s hd
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hgx
  have hao : orderOf (rootDiagUnit .G2 a) = 3 := by
    rw [← ha, orderOf_injective _ (adjointGroup .G2 K).subtype_injective,
      show g * x * g⁻¹ = (MulAut.conj g).toMonoidHom x from rfl,
      orderOf_injective _ (MulAut.conj g).injective x, hx]
  have hoa : orderOf a = 3 := by rw [← orderOf_rootDiagUnit (K := K), hao]
  have hap : a ^ 3 = 1 := hoa ▸ pow_orderOf_eq_one a
  have ha1 : a ≠ 1 := fun h => by
    rw [h, orderOf_one] at hoa
    omega
  by_cases ha0 : rootChar a g2a = 1
  · have hscent : s ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) :=
      mem_center_of_rootChar_g2a_eq_one K ι hι hιx hap ha0 hd (by rw [hgs]; exact ha)
    exact oddPCoreInClosure_three_of_central_image K h3 h4 ι hι hscent hgs
  · exact oddPCoreInClosure_of_toral_cases K Nat.prime_three h3 h4 ha
      (toral_centralizer_cases_G2_three K h4 a hap ha1 ha0)

end Main

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
