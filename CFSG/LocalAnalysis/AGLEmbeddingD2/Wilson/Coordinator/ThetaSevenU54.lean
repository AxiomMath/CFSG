module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.ThetaCentralQuot
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThreeCore.Facts
public import CFSG.RankThree.PartTwo.Sec21.Item233Res3ProofU54

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator.U54

open CFSG.RankThree.LocalRank Subgroup Matrix
open CFSG.LieType.Universal.Unitary (SU mem_SU)
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.RankThree.PartOne (suQ)
open CFSG.RankThree.PartOne.KFU (gu5 Xm b6 phi6 phi6_fst phi6_snd ker_phi6 centralizer_b6_facts
  block_of_gram suBlock6 suBlock6_mem_centralizer card_center_range_suBlock6
  perfectResidual_centralizer_b6 isQuasisimple_perfectResidual_centralizer_b6 bA6 phiA6 ker_phiA6
  su3Emb su3Emb_mem_centralizer perfectResidual_centralizer_bA6
  isQuasisimple_perfectResidual_centralizer_bA6 card_center_SU_three card_center_mulEquiv
  su3Emb_injective)
open CFSG.RankThree.PartTwo.Sec21.Item233Res3Proof (K16 card_K16 σ16 SU54 U54 qU
  isCentralPQuot_qU projSUEquivU54 σ16_involutive)

theorem card_ker_qU : Nat.card qU.ker = 5 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ψ₀ : SU54 ≃* CFSG.Assembly.LowTwoRank.StatedSU 5 (2 ^ 2) K16 :=
    CFSG.LieType.Universal.Unitary.equivStatedSU card_K16 5
  let N : Subgroup ↥(CFSG.Assembly.LowTwoRank.StatedSU 5 (2 ^ 2) K16) :=
    (CFSG.Assembly.LowTwoRank.StatedScalars (Fin 5) K16).subgroupOf
      (CFSG.Assembly.LowTwoRank.StatedSU 5 (2 ^ 2) K16)
  have hker :
      qU.ker = N.comap (ψ₀ : SU54 →* ↥(CFSG.Assembly.LowTwoRank.StatedSU 5 (2 ^ 2) K16)) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_comap]
    exact QuotientGroup.eq_one_iff _
  rw [hker, Subgroup.comap_equiv_eq_map_symm, Subgroup.card_map_of_injective (MulEquiv.injective _),
    (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two card_K16 (n := 5) (by norm_num)).2.2]
  norm_num

theorem pow_fifteen_eq_one (u : K16ˣ) : u ^ (3 * 5) = 1 := by
  have h : Nat.card K16ˣ = 3 * 5 := by
    rw [Nat.card_units, card_K16]
    norm_num
  rw [← h]
  exact pow_card_eq_one'

section Block

variable {K : Type} [Field K] (σ : K ≃+* K)

theorem det_blockFive (a b c d u : K) :
    (!![a, b, 0, 0, 0; c, d, 0, 0, 0; 0, 0, u, 0, 0; 0, 0, 0, σ a, -σ b;
      0, 0, 0, -σ c, σ d] : Matrix (Fin 5) (Fin 5) K).det =
      (a * d - b * c) * u * (σ a * σ d - σ b * σ c) := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Fin.succAbove]
  ring

theorem gu5_two_two_eq_one_of_det {ζ : Kˣ} (hζ : σ (ζ : K) = ζ) (h1 : ζ ≠ 1) (h2 : ζ ^ 2 ≠ 1)
    {g : ↥(SU σ 5)} (hg : g ∈ centralizer ({b6 σ ζ hζ} : Set ↥(SU σ 5)))
    (hdet : (Xm g).det = 1) : gu5 g 2 2 = 1 := by
  obtain ⟨e02, e03, e04, e12, e13, e14, e20, e21, e23, e24, e30, e31, e32, e40, e41, e42, -,
    i, ii, iii, iv⟩ := centralizer_b6_facts σ hζ h1 h2 hg
  have hdet' := hdet
  rw [Matrix.det_fin_two_of] at hdet'
  obtain ⟨y00, y10, y11, y01⟩ := block_of_gram σ hdet' i ii iii iv
  have hσdet : σ (gu5 g 0 0) * σ (gu5 g 1 1) - σ (gu5 g 0 1) * σ (gu5 g 1 0) = 1 := by
    have := congrArg σ hdet'
    simpa [map_sub, map_mul] using this
  have hg5 : gu5 g = !![gu5 g 0 0, gu5 g 0 1, 0, 0, 0; gu5 g 1 0, gu5 g 1 1, 0, 0, 0;
      0, 0, gu5 g 2 2, 0, 0; 0, 0, 0, σ (gu5 g 0 0), -σ (gu5 g 0 1);
      0, 0, 0, -σ (gu5 g 1 0), σ (gu5 g 1 1)] := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [e02, e03, e04, e12, e13, e14, e20, e21, e23, e24, e30, e31, e32, e40, e41, e42, y00,
        y10, y11, y01]
  have hd : (gu5 g).det = 1 := (mem_SU.1 g.2).1
  rw [hg5, det_blockFive, hdet', hσdet, one_mul, mul_one] at hd
  exact hd

variable [CharP K 2]

theorem ker_fst_phi6 (hσσ : ∀ x, σ (σ x) = x) {ζ : Kˣ} (hζ : σ (ζ : K) = ζ) (h1 : ζ ≠ 1)
    (h2 : ζ ^ 2 ≠ 1) :
    ((MonoidHom.fst Kˣ Kˣ).comp (phi6 σ hζ h1 h2)).ker =
      (suBlock6 σ hσσ).range.subgroupOf (centralizer ({b6 σ ζ hζ} : Set ↥(SU σ 5))) := by
  rw [← ker_phi6 σ hσσ hζ h1 h2]
  ext g
  simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_fst]
  constructor
  · intro h
    have hdet : (Xm (g : ↥(SU σ 5))).det = 1 := by
      have := congrArg (fun u : Kˣ => (u : K)) h
      simp only [phi6_fst, Units.val_one] at this
      exact this
    refine Prod.ext h (Units.ext ?_)
    rw [phi6_snd, Prod.snd_one, Units.val_one]
    exact gu5_two_two_eq_one_of_det σ hζ h1 h2 g.2 hdet
  · intro h
    rw [h, Prod.fst_one]

end Block

theorem isSimpleGroup_range_su3Emb : IsSimpleGroup ↥(su3Emb σ16).range ∧
    ∃ a b : ↥(su3Emb σ16).range, a * b ≠ b * a := by
  have hc : center ↥(su3Emb σ16).range = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    rw [← card_center_mulEquiv (MonoidHom.ofInjective (su3Emb_injective σ16)),
      card_center_SU_three card_K16 le_rfl]
    norm_num
  have hq : CFSG.IsQuasisimple ↥(su3Emb σ16).range := by
    obtain ⟨ζ, hζ1⟩ := CFSG.RankThree.PartTwo.Sec21.Item233Res3Proof.exists_mu3_ne_one
    have hfix := CFSG.RankThree.PartTwo.Sec21.Item233Res3Proof.σ16_mu3 ζ
    have h1 : (ζ : K16ˣ) ≠ 1 := fun h => hζ1 (Subtype.ext h)
    have h3 : (ζ : K16ˣ) ^ 3 = 1 := (mem_rootsOfUnity 3 _).mp ζ.2
    have h2 : (ζ : K16ˣ) ^ 2 ≠ 1 := by
      intro h
      apply h1
      calc (ζ : K16ˣ) = (ζ : K16ˣ) ^ 3 * ((ζ : K16ˣ) ^ 2)⁻¹ := by group
        _ = 1 := by rw [h3, h, inv_one, one_mul]
    have := isQuasisimple_perfectResidual_centralizer_bA6 card_K16 le_rfl hfix h1 h2
    rwa [perfectResidual_centralizer_bA6 card_K16 le_rfl hfix h1 h2] at this
  have := hq.2.1
  have hs : IsSimpleGroup ↥(su3Emb σ16).range := isSimpleGroup_of_center_eq_bot hc
  exact ⟨hs, exists_mul_ne_of_center_eq_bot hc⟩

theorem isSimpleGroup_range_suBlock6 : IsSimpleGroup ↥(suBlock6 σ16 σ16_involutive).range ∧
    ∃ a b : ↥(suBlock6 σ16 σ16_involutive).range, a * b ≠ b * a := by
  have hc : center ↥(suBlock6 σ16 σ16_involutive).range = ⊥ :=
    Subgroup.eq_bot_of_card_eq _ (card_center_range_suBlock6 σ16 σ16_involutive)
  have hq : CFSG.IsQuasisimple ↥(suBlock6 σ16 σ16_involutive).range := by
    obtain ⟨ζ, hζ1⟩ := CFSG.RankThree.PartTwo.Sec21.Item233Res3Proof.exists_mu3_ne_one
    have hfix := CFSG.RankThree.PartTwo.Sec21.Item233Res3Proof.σ16_mu3 ζ
    have h1 : (ζ : K16ˣ) ≠ 1 := fun h => hζ1 (Subtype.ext h)
    have h3 : (ζ : K16ˣ) ^ 3 = 1 := (mem_rootsOfUnity 3 _).mp ζ.2
    have h2 : (ζ : K16ˣ) ^ 2 ≠ 1 := by
      intro h
      apply h1
      calc (ζ : K16ˣ) = (ζ : K16ˣ) ^ 3 * ((ζ : K16ˣ) ^ 2)⁻¹ := by group
        _ = 1 := by rw [h3, h, inv_one, one_mul]
    have hK4 : 4 ≤ Nat.card K16 := by rw [card_K16]; norm_num
    have := isQuasisimple_perfectResidual_centralizer_b6 σ16 σ16_involutive hK4 hfix h1 h2
    rwa [perfectResidual_centralizer_b6 σ16 σ16_involutive hK4 hfix h1 h2] at this
  have := hq.2.1
  have hs : IsSimpleGroup ↥(suBlock6 σ16 σ16_involutive).range :=
    isSimpleGroup_of_center_eq_bot hc
  exact ⟨hs, exists_mul_ne_of_center_eq_bot hc⟩

theorem thetaCent_U54 {y : U54} (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) :
    aschbacherSolvableCore 3 (centralizer ({y} : Set U54)) = ⊥ := by
  have hq := isCentralPQuot_qU
  obtain ⟨x, hxy, hx3⟩ := hq.exists_lift hy3
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hy1 (by rw [← hxy, map_one])
  obtain ⟨h, ζ, hζ, h1, h2, hcase⟩ :=
    CFSG.RankThree.PartTwo.Sec21.U5Lines.exists_conj_eq_bA6_or_b6 card_K16 hx3 hx1
  rw [ThreeCore.aschbacherSolvableCore_three_centralizer_eq_bot_iff (MulAut.conj (qU h)) y]
  have hconj : (MulAut.conj (qU h)) y = qU (h * x * h⁻¹) := by
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, hxy]
  have hx3' : (h * x * h⁻¹) ^ 3 = 1 := by rw [conj_pow, hx3, mul_one, mul_inv_cancel]
  rw [hconj]
  rcases hcase with heq | heq
  · rw [heq] at hx3' ⊢
    obtain ⟨hs, hnc⟩ := isSimpleGroup_range_su3Emb
    exact aschbacherSolvableCore_eq_bot_of_quot hq.surjective hq.central card_ker_qU
      pow_fifteen_eq_one (hq.map_centralizer hx3')
      (by rintro _ ⟨u, rfl⟩; exact su3Emb_mem_centralizer σ16 hζ u) hnc (phiA6 σ16 hζ h1 h2)
      (ker_phiA6 σ16 hζ h1 h2)
  · rw [heq] at hx3' ⊢
    obtain ⟨hs, hnc⟩ := isSimpleGroup_range_suBlock6
    exact aschbacherSolvableCore_eq_bot_of_quot hq.surjective hq.central card_ker_qU
      pow_fifteen_eq_one (hq.map_centralizer hx3')
      (by rintro _ ⟨A, rfl⟩; exact suBlock6_mem_centralizer σ16 σ16_involutive hζ A) hnc
      ((MonoidHom.fst K16ˣ K16ˣ).comp (phi6 σ16 hζ h1 h2))
      (ker_fst_phi6 σ16 σ16_involutive hζ h1 h2)

theorem thetaCent_of_u54 {X : Type} [Group X] [Finite X] (e : X ≃* projSU 5 2 2) (b : X)
    (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1) :
    aschbacherSolvableCore 3 (centralizer ({b} : Set X)) = ⊥ := by
  let e' : X ≃* U54 := e.trans projSUEquivU54
  rw [ThreeCore.aschbacherSolvableCore_three_centralizer_eq_bot_iff e' b]
  exact thetaCent_U54 (by rw [← map_pow, hb3, map_one]) (by rwa [ne_eq, MulEquiv.map_eq_one_iff])

end CFSG.AGLEmbeddingD2.Wilson.Coordinator.U54
