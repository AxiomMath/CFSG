module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2C2

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ} {t : G}
  {M₀ : Subgroup G} {x₀ : G} {q : ℕ} {W : Subgroup G}

structure S2Hall (S L D : Subgroup G) (y : G) (B' : Subgroup G) : Prop where
  D_le : D ≤ B'
  y_norm : y ∈ Subgroup.normalizer (B' : Set G)
  eq_sup : B' = D ⊔ conjR D y
  conj_le : conjR D y ≤ Subgroup.normalizer (D : Set G)
  le_R : B' ≤ Subgroup.normalizer (thompsonJ S : Set G)
  le_L₀ : B' ≤ Subgroup.normalizer (conjJoin S L : Set G)
  odd : Odd (Nat.card B')

namespace S2Base

variable (B : S2Base T M H S L D n t M₀ x₀ q W)
include B

theorem rebase {r : G} (hr : r ∈ thompsonJ S) :
    S2Base T M H S L D n t M₀ (x₀ * r) q W := by
  have hrS : r ∈ S := thompsonJ_le_self S hr
  refine ⟨B.cfg, ⟨B.su.D, B.su.hSM, B.su.hMT, B.su.h2, M₀.mul_mem B.hx₀ (B.hSM hrS), ?_,
    B.su.loc, ?_⟩⟩
  · intro h
    apply B.hx₀S
    have := S.mul_mem h (S.inv_mem hrS)
    simpa using this
  · intro hle
    have hrU : r ∈ Subgroup.normalizer (blockU L : Set G) :=
      C1.mem_normalizer_blockU (B.R_le_normalizer_L hr)
    have hrB : r ∈ Subgroup.normalizer (baum S : Set G) := by
      rw [B.baum_eq]; exact Subgroup.le_normalizer hr
    have hrQ : r ∈ Subgroup.normalizer ((baum S ⊓ Subgroup.centralizer (blockU L : Set G) :
        Subgroup G) : Set G) := C5.mem_normalizer_inf hrB (C5.mem_normalizer_centralizer hrU)
    have h' : conjR (conjR (blockU L) x₀) r ≤ baum S ⊓ Subgroup.centralizer (blockU L : Set G) := by
      rw [conjR_conjR]; exact hle
    have h'' := conjR_le_iff.1 h'
    rw [conjR_eq_of_mem_normalizer (Subgroup.inv_mem _ hrQ)] at h''
    exact B.su.good h''

theorem RD_inf_hall {B' : Subgroup G} (hDB : D ≤ B') (hRB : thompsonJ S ⊓ B' = ⊥) :
    (thompsonJ S ⊔ D) ⊓ B' = D := by
  apply le_antisymm
  · rintro f ⟨hfRD, hfB⟩
    obtain ⟨r₁, hr₁, d, hd, hfd⟩ := B.RD_decomp f hfRD
    have hr₁B : r₁ ∈ B' := by
      have : r₁ = f * d⁻¹ := by rw [hfd]; group
      rw [this]
      exact B'.mul_mem hfB (B'.inv_mem (hDB hd))
    have hmem : r₁ ∈ thompsonJ S ⊓ B' := ⟨hr₁, hr₁B⟩
    rw [hRB, Subgroup.mem_bot] at hmem
    rw [hfd, hmem, one_mul]
    exact hd
  · exact le_inf le_sup_right hDB

theorem exists_stageC (h246 : Lemma246Double) :
    ∃ (y : G) (B' : Subgroup G),
      S2Base T M H S L D n t M₀ y q W ∧ S2Hall S L D y B' := by
  obtain ⟨r₀, B', hr₀, hDB, hB'K, hRB', hdec, hodd, hyB⟩ := B.exists_hall h246
  set R := thompsonJ S with hRdef
  have hr₀' : r₀⁻¹ ∈ R := R.inv_mem hr₀
  have By : S2Base T M H S L D n t M₀ (x₀ * r₀⁻¹) q W := B.rebase hr₀'
  set y := x₀ * r₀⁻¹ with hydef
  have hcomp : IsComplementIn R (R ⊔ D ⊔ conjR D x₀) B' := ⟨hB'K, hRB', hdec⟩
  have hKN : R ⊔ D ⊔ conjR D x₀ ≤ Subgroup.normalizer (R : Set G) := B.K_le_normalizer_R
  have hB'N : B' ≤ Subgroup.normalizer (R : Set G) := hB'K.trans hKN
  have hDyB : conjR D y ≤ B' := by
    have := conjR_mono hDB y
    rwa [conjR_eq_of_mem_normalizer hyB] at this
  have hDyN : conjR D y ≤ Subgroup.normalizer ((R ⊔ D : Subgroup G) : Set G) :=
    By.conjD_le_normalizer_RD h246
  have hconj_le : conjR D y ≤ Subgroup.normalizer (D : Set G) := by
    refine le_normalizer_of_conj_mem fun e he d hd => ?_
    have h1 : e * d * e⁻¹ ∈ R ⊔ D :=
      (Subgroup.mem_normalizer_iff.1 (hDyN he) d).1 (Subgroup.mem_sup_right hd)
    have h2 : e * d * e⁻¹ ∈ B' :=
      B'.mul_mem (B'.mul_mem (hDyB he) (hDB hd)) (B'.inv_mem (hDyB he))
    have hm : e * d * e⁻¹ ∈ (R ⊔ D) ⊓ B' := ⟨h1, h2⟩
    rwa [B.RD_inf_hall hDB hRB'] at hm
  have hD'K : conjR D x₀ ≤ R ⊔ conjR D y := by
    intro z hz
    have hw : r₀ * z * r₀⁻¹ ∈ conjR D y := by
      rw [show conjR D y = conjR (conjR D x₀) r₀⁻¹ from (conjR_conjR D x₀ r₀⁻¹).symm, mem_conjR]
      have e : r₀⁻¹ * (r₀ * z * r₀⁻¹) * r₀⁻¹⁻¹ = z := by group
      rw [e]; exact hz
    have hwR : (r₀ * z * r₀⁻¹) * r₀ * (r₀ * z * r₀⁻¹)⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.1 (hB'N (hDyB hw)) r₀).1 hr₀
    have e : z = (r₀⁻¹ * ((r₀ * z * r₀⁻¹) * r₀ * (r₀ * z * r₀⁻¹)⁻¹)) * (r₀ * z * r₀⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (R.mul_mem hr₀' hwR))
      (Subgroup.mem_sup_right hw)
  have hRDDy : R ⊔ (D ⊔ conjR D y) = R ⊔ D ⊔ conjR D x₀ := by
    apply le_antisymm
    · exact sup_le (le_sup_of_le_left le_sup_left) (sup_le (le_sup_of_le_left le_sup_right)
        (hDyB.trans hB'K))
    · exact sup_le (sup_le le_sup_left (le_sup_of_le_right le_sup_left))
        (hD'K.trans (sup_le le_sup_left (le_sup_of_le_right le_sup_right)))
  have hB'le : D ⊔ conjR D y ≤ B' := sup_le hDB hDyB
  have heq : B' = D ⊔ conjR D y := by
    have hN' : D ⊔ conjR D y ≤ Subgroup.normalizer (R : Set G) := hB'le.trans hB'N
    have hc := card_sup_mul_card_inf hN'
    have hbot : (D ⊔ conjR D y) ⊓ R = ⊥ := by
      rw [eq_bot_iff, ← hRB', inf_comm]
      exact inf_le_inf_left R hB'le
    rw [hbot, Subgroup.card_bot, mul_one, sup_comm (D ⊔ conjR D y) R, hRDDy] at hc
    have hcardK := hcomp.card_mul R_le_K hKN
    have hRpos : 0 < Nat.card ↥R := Nat.card_pos
    have hcc : Nat.card ↥R * Nat.card ↥B' = Nat.card ↥R * Nat.card ↥(D ⊔ conjR D y : Subgroup G) := by
      rw [← hcardK, hc]
      ring
    exact (Subgroup.eq_of_le_of_card_ge hB'le
      (Nat.eq_of_mul_eq_mul_left hRpos hcc).le).symm
  refine ⟨y, B', By, ⟨hDB, hyB, heq, hconj_le, hB'N, ?_, hodd⟩⟩
  rw [heq]
  exact sup_le (B.D_le_L₀.trans Subgroup.le_normalizer) (By.conjD_le_normalizer_L₀ h246)

end S2Base

end CFSG.QuasithinUnique.Lin2
