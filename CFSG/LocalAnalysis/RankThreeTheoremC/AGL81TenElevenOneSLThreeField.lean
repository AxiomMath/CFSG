module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiAct
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusBase
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenNineWTransfer
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenNineWLinear

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3E27

open Subgroup CFSG.RankThree.PartTwo.Sec4 CFSG.Open CFSG.AGLEmbedding Matrix
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
  CFSG.ComponentClassification.CatalogueBHigherLinearAction
open scoped commutatorElement

theorem normal_eq_top_or_le_center' {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q)
    {N : Subgroup Q} (hN : N.Normal) : N = ⊤ ∨ N ≤ Subgroup.center Q := by
  obtain ⟨hp, hs⟩ := hQ
  have := hN.map (QuotientGroup.mk' (Subgroup.center Q)) (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (N.map (QuotientGroup.mk' (Subgroup.center Q))) with h | h
  · right
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  · left
    have hsup : N ⊔ Subgroup.center Q = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center Q)) N
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hcomm : commutator Q ≤ N :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
    exact eq_top_iff.mpr (hp ▸ hcomm)

theorem aschbacherSolvableCore_eq_bot_of_mulEquiv {L : Type*} [Group L] [Finite L]
    (hq : CFSG.Open.IsQuasisimple L) {F : Type*} [Field F]
    (φ : L ≃* SpecialLinearGroup (Fin 3) F) :
    CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 L = ⊥ := by
  obtain ⟨hsol, -, h3, -⟩ :=
    CFSG.RankThree.LocalRank.solvable_prime_complement_core_characterization (H := L)
      Nat.prime_three
  rcases normal_eq_top_or_le_center' hq
      (CFSG.RankThree.LocalRank.aschbacherSolvableCore_normal 3 L) with h | h
  · exfalso
    rw [h] at hsol
    haveI := hsol
    haveI : Group.IsSolvable L := solvable_of_surjective
      (f := (Subgroup.topEquiv (G := L)).toMonoidHom) (Subgroup.topEquiv (G := L)).surjective
    have hder : ∀ k, derivedSeries L k = ⊤ := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => rw [derivedSeries_succ, ih]; exact hq.1
    obtain ⟨k, hk⟩ := (isSolvable_def L).1 inferInstance
    rw [hder k] at hk
    have hall : ∀ x : L, x = 1 := fun x => by
      have := Subgroup.mem_top x
      rwa [hk, Subgroup.mem_bot] at this
    haveI := hq.2.toNontrivial
    obtain ⟨x, y, hxy⟩ := exists_pair_ne (L ⧸ Subgroup.center L)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    exact hxy (by rw [hall x, hall y])
  · refine eq_bot_iff.2 fun x hx => ?_
    have hxZ := h hx
    have hφZ : φ x ∈ Subgroup.center (SpecialLinearGroup (Fin 3) F) := by
      rw [← Subgroup.map_center_eq φ]
      exact ⟨x, hxZ, rfl⟩
    obtain ⟨r, hr, hrx⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hφZ
    rw [Fintype.card_fin] at hr
    have hφ3 : φ x ^ 3 = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_pow, ← hrx, ← map_pow, hr, map_one,
        Matrix.SpecialLinearGroup.coe_one]
    have hx3 : x ^ 3 = 1 := φ.injective (by rw [map_pow, hφ3, map_one])
    have hxθ : (⟨x, hx⟩ : CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 L) ^ 3 = 1 :=
      Subtype.ext (by simpa using hx3)
    have hdvd := orderOf_dvd_of_pow_eq_one hxθ
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h1
    · rw [orderOf_eq_one_iff] at h1
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val h1
    · have h4 := orderOf_dvd_natCard
        (⟨x, hx⟩ : CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 L)
      rw [h1] at h4
      exact absurd h4 h3

theorem coe_slPiTrueEquiv_symm {q : ℕ} {K : Type} [Field K] (u : SpecialLinearGroup (Fin 3) K) :
    (((slPiTrueEquiv q K).symm u : slPi true 3 q K) : GL (Fin 3) K) =
      Matrix.SpecialLinearGroup.toGL u := by
  rw [← toGL_slPiTrueEquiv, MulEquiv.apply_symm_apply]

variable {Y : Type} [Group Y] [Finite Y]

theorem exists_slPi_field_of_not_inner_wPre
    {L P : Subgroup Y} [hLn : L.Normal] (hCP : CompParab L P) {n : ℕ} (hn : 1 ≤ n)
    (φ : L ≃* SpecialLinearGroup (Fin 3) (GaloisField 2 n))
    (hrk : Open.pRank 3 (wPre P) ≤ 1) {a : Y} (ha3 : a ^ 3 = 1)
    (haN : a ∈ Subgroup.normalizer (P : Set Y))
    (hout : ¬ ∃ v ∈ wPre P, ∀ w ∈ wPre P, ⁅a * v, w⁆ ∈ pCoreOf 2 P) :
    ∃ (e : L ≃* slPi true 3 (2 ^ n) (GaloisField 2 n)) (f₀ : ℕ), n = 3 * f₀ ∧
      ∃ σ : GaloisField 2 n ≃+* GaloisField 2 n,
        ((∀ c, σ c = c ^ piCard true (2 ^ f₀)) ∨ ∀ c, σ c = c ^ (piCard true (2 ^ f₀) ^ 2)) ∧
        ∃ g : GL (Fin 3) (GaloisField 2 n), ∀ s : slPi true 3 (2 ^ n) (GaloisField 2 n),
          ((slAct e ⟨a, mem_normalizer_of_normal a⟩ s : slPi true 3 (2 ^ n) (GaloisField 2 n)) :
            GL (Fin 3) (GaloisField 2 n)) = g * frobGL σ s * g⁻¹ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := GaloisField 2 n with hF
  have hFc : Nat.card F = 2 ^ n := GaloisField.card 2 n (by omega)
  have hK : PiField true 2 n F := ⟨Nat.prime_two, hn, hFc⟩
  have hq := hCP.comp.2.2
  haveI : Group.IsPerfect L := ⟨hq.1⟩
  set e₀ : L ⧸ Subgroup.center L ≃* projectiveSL 3 F :=
    QuotientGroup.congr (Subgroup.center L) (scalars 3 F) φ
      (by rw [scalars_eq_center]; exact Subgroup.map_center_eq φ) with he₀def
  have hρ : ∀ g, e₀ (QuotientGroup.mk (φ.symm.toMonoidHom g)) = proj 3 F g := fun g => by
    rw [he₀def, QuotientGroup.congr_mk]
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    rfl
  obtain ⟨σ, -, I, hσs, -, hI, hcomap, hne, -⟩ :=
    CFSG.AGLEmbedding.exists_comap_eq_flagStabilizer hCP.odd (by norm_num) e₀
      (ρ := φ.symm.toMonoidHom) φ.symm.surjective hρ hCP.parab
  have hbij : Function.Bijective σ :=
    (Nat.bijective_iff_surjective_and_card σ).2 ⟨hσs, (Nat.card_congr φ.toEquiv).symm⟩
  set S := MulEquiv.ofBijective σ hbij with hS
  set e : L ≃* slPi true 3 (2 ^ n) F := S.symm.trans (slPiTrueEquiv (2 ^ n) F).symm with he
  have hθ := aschbacherSolvableCore_eq_bot_of_mulEquiv hq φ
  have hx3 : (⟨a, mem_normalizer_of_normal a⟩ : Subgroup.normalizer (L : Set Y)) ^ 3 = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow]; exact ha3)
  rcases slAct_pgl_or_field_linear hK hθ e _ hx3 with ⟨y, -, hy⟩ | ⟨-, f₀, hf, σ', hσ', g, -, hg⟩
  · exfalso
    apply hout
    haveI : KFactProofs.FieldIndexP.OddPrime 3 := ⟨Nat.prime_three, by decide⟩
    have hker : σ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin 3) F) := by
      rw [(MonoidHom.ker_eq_bot_iff σ).2 hbij.1]
      exact bot_le
    refine FieldIndexW.actsInnerlyW_linear_of_compatP 3 hCP le_rfl σ hσs hker hI (hne hCP.ne_top)
      hcomap y haN (fun x => ?_) ⟨1, fun w _ => by rw [pow_one, ha3, one_mul, mul_one]⟩ hrk
    have hes : e.symm ((slPiTrueEquiv (2 ^ n) F).symm x) = σ x := by
      rw [he, MulEquiv.symm_trans_apply, MulEquiv.symm_symm, MulEquiv.symm_symm,
        MulEquiv.apply_symm_apply, hS, MulEquiv.ofBijective_apply]
    have h1 := hy ((slPiTrueEquiv (2 ^ n) F).symm x)
    rw [slAct_apply, hes, coe_slPiTrueEquiv_symm] at h1
    set X := L.normalizerMonoidHom ⟨a, mem_normalizer_of_normal a⟩ (σ x) with hX
    have h2 : Matrix.SpecialLinearGroup.toGL (S.symm X) =
        Matrix.SpecialLinearGroup.toGL (slConjugation 3 F y x) := by
      rw [toGL_slConjugation, ← h1, he, MulEquiv.trans_apply, coe_slPiTrueEquiv_symm]
    have h3 : X = σ (slConjugation 3 F y x) := by
      have := Matrix.SpecialLinearGroup.toGL_injective h2
      rw [← this, ← MulEquiv.ofBijective_apply σ hbij, ← hS, MulEquiv.apply_symm_apply]
    have h4 : (MulAut.conjNormal a : MulAut L) (σ x) = X := by
      apply Subtype.ext
      rw [MulAut.conjNormal_apply, hX, coe_normalizerMonoidHom]
      rfl
    rw [h4, h3, mul_inv_cancel]
    exact one_mem _
  · exact ⟨e, f₀, hf, σ', hσ', g, hg⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3E27
