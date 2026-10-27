module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.CaseBFactors
public import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardProductCentre
public import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardProductParabolic

public section

open Subgroup
open CFSG.LocalAnalysis.ComponentInitial LinearFlag FieldFourCover
open CFSG.LocalAnalysis.EvenBN.LinearThree
open CFSG.OddStandard.Seitz77 (Datum)

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A}

namespace CFSG.LocalAnalysis.EvenBN.LinearThree.CaseBNotation

theorem nonempty_of_oddCore {f : ℕ} (hf : 3 ≤ f) {Vi : Subgroup G}
    (w : WData d Vi (2 ^ f)) {K : Type} [Field K] [Finite K] (D : LeviData A Vi K)
    (hKc : Nat.card K = 2 ^ f) (hB : w.CaseB D.lev.range)
    (hO : ⁅CFSG.Open.standardComponentOddCore w.Nbar, w.Ebar D.lev.range⁆ = ⊥) :
    Nonempty (CaseBNotation w D) := by
  obtain ⟨σ, W₁, M₁, ℓ, hW₁W, hW₁₂, hW₁sup, hW₁card, hbij, hℓinj, hℓM₁, hℓdiag, hcomm, hcen₂,
    hnat, hcen₁, hM₁N, hM₁W, hM₁eq, hW₁ℓ, hM₁₂, hM₁comm, hℓbar, hσc, hσinj, hσE, hσon, hσXY,
    hsup⟩ := CaseBModule.exists_caseB_notation hf w hKc D hB hO
  exact ⟨⟨W₁, M₁, ℓ, hW₁W, hW₁₂, hW₁sup, hW₁card, hbij, hℓinj, hℓM₁, hℓdiag, hcomm, hcen₂, hnat,
    hcen₁, hM₁N, hM₁W, hM₁eq, hW₁ℓ, hM₁₂, hM₁comm, σ, hℓbar, hσc, hσinj, hσE, hσon, hσXY, hO,
    hsup⟩⟩

end CFSG.LocalAnalysis.EvenBN.LinearThree.CaseBNotation

namespace CFSG.ComponentClassification.GS79bSec5

private theorem exists_mul_ne_mul_of_isQuasisimple {H : Type*} [Group H]
    (hq : CFSG.Open.IsQuasisimple H) : ∃ x y : H, x * y ≠ y * x := by
  have hnt : Nontrivial H := CFSG.ComponentClassification.Quasisimple.nontrivial hq
  have hperf : Group.IsPerfect H := ⟨hq.1⟩
  have hnon : ¬ IsMulCommutative H :=
    @Group.IsPerfect.not_isMulCommutative H _ hnt hperf
  rw [isMulCommutative_iff] at hnon
  push Not at hnon
  exact hnon

omit [Finite G]
  in
private theorem mem_center_of_mul_conj_eq_one {P : Subgroup G} {t : G} (ht : t * t = 1)
    (hc : P.map (MulAut.conj t).toMonoidHom ≤ centralizer (P : Set G)) {x : P}
    (hx : (x : G) * (t * (x : G) * t) = 1) : x ∈ center P := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hx' : (x : G) = t * (x : G)⁻¹ * t := by
    calc (x : G) = (t * x * t)⁻¹ := eq_inv_of_mul_eq_one_left hx
      _ = t⁻¹ * (x : G)⁻¹ * t⁻¹ := by group
      _ = t * (x : G)⁻¹ * t := by rw [htinv]
  have hmem : (x : G) ∈ centralizer (P : Set G) := by
    rw [hx']
    exact hc (conj_mem_map_conj ht (inv_mem x.2))
  rw [mem_center_iff]
  intro y
  exact Subtype.ext ((Subgroup.mem_centralizer_iff.1 hmem) y y.2)

omit [Finite G]
  in
private theorem le_sup_map_conj_of_surj {P A : Subgroup G} {t : G} (ht : t * t = 1)
    (honto : ∀ y ∈ A, ∃ x ∈ P, x * (t * x * t) = y) :
    A ≤ P ⊔ P.map (MulAut.conj t).toMonoidHom := by
  intro y hy
  obtain ⟨x, hx, hxy⟩ := honto y hy
  rw [← hxy]
  exact Subgroup.mul_mem_sup hx (conj_mem_map_conj ht hx)

omit [Finite G]
  in
private theorem map_conj_ne_of_not_commuting {P : Subgroup G} {t : G}
    (hc : P.map (MulAut.conj t).toMonoidHom ≤ centralizer (P : Set G))
    (hnab : ∃ x ∈ P, ∃ y ∈ P, x * y ≠ y * x) :
    P.map (MulAut.conj t).toMonoidHom ≠ P := by
  intro h
  have hle : P ≤ centralizer (P : Set G) := by
    calc P = P.map (MulAut.conj t).toMonoidHom := h.symm
      _ ≤ centralizer (P : Set G) := hc
  obtain ⟨x, hx, y, hy, hxy⟩ := hnab
  exact hxy (Subgroup.mem_centralizer_iff.1 (hle hx) y hy).symm

omit [Finite G]
  in
private theorem sup_map_sup_eq {P Q R S : Subgroup G} {g : G} (hPR : P ≤ R) (hQS : Q ≤ S)
    (hRP : R ≤ P ⊔ Q) (hSQ : S ≤ P ⊔ Q) :
    (P ⊔ Q) ⊔ (P ⊔ Q).map (MulAut.conj g).toMonoidHom =
      (R ⊔ R.map (MulAut.conj g).toMonoidHom) ⊔ (S ⊔ S.map (MulAut.conj g).toMonoidHom) := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.map_sup]
    apply sup_le
    · apply sup_le
      · exact hPR.trans (le_sup_left.trans le_sup_left)
      · exact hQS.trans (le_sup_left.trans le_sup_right)
    · apply sup_le
      · exact (Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hPR).trans
          (le_sup_right.trans le_sup_left)
      · exact (Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hQS).trans
          (le_sup_right.trans le_sup_right)
  · apply sup_le
    · apply sup_le
      · exact hRP.trans le_sup_left
      · exact (Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hRP).trans le_sup_right
    · apply sup_le
      · exact hSQ.trans le_sup_left
      · exact (Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hSQ).trans le_sup_right

omit [Finite G]
  in
private theorem nonempty_center_quotient_equiv {A P : Subgroup G} {t : G} {K : Type} [Field K]
    (ht : t * t = 1) (hq : CFSG.Open.IsQuasisimple ↥P)
    (hc : P.map (MulAut.conj t).toMonoidHom ≤ centralizer (P : Set G))
    (hmem : ∀ x ∈ P, x * (t * x * t) ∈ A)
    (honto : ∀ y ∈ A, ∃ x ∈ P, x * (t * x * t) = y)
    (e : (A ⧸ center A) ≃* projectiveSL 3 K) :
    Nonempty (↥P ⧸ center ↥P ≃* projectiveSL 3 K) := by
  have hperf : Group.IsPerfect ↥P := ⟨hq.1⟩
  let hc' : ∀ x ∈ P, ∀ y ∈ P.map (MulAut.conj t).toMonoidHom, x * y = y * x :=
    fun x hx y hy => Subgroup.mem_centralizer_iff.1 (hc hy) x hx
  let δA : P →* A := (diagHom ht hc').codRestrict A (fun x => hmem x x.2)
  have hsurj : Function.Surjective δA := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, hxy⟩ := honto y hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hker : δA.ker ≤ center P := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    exact mem_center_of_mul_conj_eq_one ht hc (congrArg Subtype.val hx)
  exact ⟨(@CFSG.ComponentClassification.PerfectCentralQuotient.equivalence ↥P A _ _
    hperf δA hsurj hker).trans e⟩

theorem exists_seitz43_product {K : Type} [Field K] [Finite K] [CharP K 2]
    (F : FrameData A d.V K) (e : (A ⧸ center A) ≃* projectiveSL 3 K) {f : ℕ} (hf : 3 ≤ f)
    (hKc : Nat.card K = 2 ^ f)
    (w₀ : WData d (F.rad 0) (2 ^ f)) (w₁ : WData d (F.rad 1) (2 ^ f))
    (hB₀ : w₀.CaseB (F.leviData 0).lev.range) (hB₁ : w₁.CaseB (F.leviData 1).lev.range)
    (hO₀ : ⁅CFSG.Open.standardComponentOddCore w₀.Nbar, w₀.Ebar (F.leviData 0).lev.range⁆ = ⊥)
    (hO₁ : ⁅CFSG.Open.standardComponentOddCore w₁.Nbar, w₁.Ebar (F.leviData 1).lev.range⁆ = ⊥) :
    ∃ (N₀ : CaseBNotation w₀ (F.leviData 0)) (N₁ : CaseBNotation w₁ (F.leviData 1)),
      CFSG.Open.IsQuasisimple ↥(N₀.ℓ.range ⊔ N₁.ℓ.range) ∧
      (N₀.ℓ.range ⊔ N₁.ℓ.range).map (MulAut.conj d.t).toMonoidHom ≤
        centralizer ((N₀.ℓ.range ⊔ N₁.ℓ.range : Subgroup G) : Set G) ∧
      (N₀.ℓ.range ⊔ N₁.ℓ.range).map (MulAut.conj d.t).toMonoidHom ≠ N₀.ℓ.range ⊔ N₁.ℓ.range ∧
      Odd (Nat.card (center ↥((N₀.ℓ.range ⊔ N₁.ℓ.range) ⊔
        (N₀.ℓ.range ⊔ N₁.ℓ.range).map (MulAut.conj d.t).toMonoidHom))) ∧
      Nonempty (↥(N₀.ℓ.range ⊔ N₁.ℓ.range) ⧸ center ↥(N₀.ℓ.range ⊔ N₁.ℓ.range) ≃*
        projectiveSL 3 K) ∧
      A ≤ (N₀.ℓ.range ⊔ N₁.ℓ.range) ⊔ (N₀.ℓ.range ⊔ N₁.ℓ.range).map (MulAut.conj d.t).toMonoidHom ∧
      CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf w₀.N =
        N₀.M₁ ⊔ N₀.M₁.map (MulAut.conj d.t).toMonoidHom ∧
      CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf w₁.N =
        N₁.M₁ ⊔ N₁.M₁.map (MulAut.conj d.t).toMonoidHom ∧
      (N₀.ℓ.range ⊔ N₁.ℓ.range) ⊔ (N₀.ℓ.range ⊔ N₁.ℓ.range).map (MulAut.conj d.t).toMonoidHom =
        CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf w₀.N ⊔
          CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf w₁.N ∧
      Nat.card (CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf w₀.N) =
        ((2 ^ f) ^ 3 * ((2 ^ f) ^ 2 - 1)) ^ 2 ∧
      Nat.card (CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf w₁.N) =
        ((2 ^ f) ^ 3 * ((2 ^ f) ^ 2 - 1)) ^ 2 := by
  obtain ⟨N₀⟩ := CaseBNotation.nonempty_of_oddCore hf w₀ (F.leviData 0) hKc hB₀ hO₀
  obtain ⟨N₁⟩ := CaseBNotation.nonempty_of_oddCore hf w₁ (F.leviData 1) hKc hB₁ hO₁
  have hf2 : 2 ≤ f := by omega
  obtain ⟨N₁', hq, hc, hmem, honto, hM₀, hM₁⟩ :=
    N₀.exists_swapFactors_frameData N₁ hKc hf2 hKc
  set G₁ : Subgroup G := N₀.ℓ.range ⊔ N₁'.ℓ.range with hG₁
  have hcyc : ∀ S : Sylow 2 (centralizer (A : Set G)), IsCyclic ↥S := by
    intro S
    exact isCyclic_of_surjective (hH := d.sector.cyclic) (Sylow.equiv d.R S).toMonoidHom
      (Sylow.equiv d.R S).surjective
  have hnab : ∃ x ∈ G₁, ∃ y ∈ G₁, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := exists_mul_ne_mul_of_isQuasisimple hq
    refine ⟨x, x.2, y, y.2, fun h => ?_⟩
    exact hxy (Subtype.ext h)
  have hne : G₁.map (MulAut.conj d.t).toMonoidHom ≠ G₁ :=
    map_conj_ne_of_not_commuting hc hnab
  have hAP : A ≤ G₁ ⊔ G₁.map (MulAut.conj d.t).toMonoidHom :=
    le_sup_map_conj_of_surj d.t_mul_self honto
  have hodd := odd_card_center_sup_map_conj (A := A) (P := G₁) (t := d.t)
    d.sector.t_order (CFSG.OddStandard.t_mem_centralizer d.sector) hcyc hc hAP hnab
  have hquot : Nonempty (↥G₁ ⧸ center ↥G₁ ≃* projectiveSL 3 K) :=
    nonempty_center_quotient_equiv d.t_mul_self hq hc hmem honto e
  have hℓ₀ : N₀.ℓ.range ≤ N₀.M₁ := by
    rw [← N₀.M₁_eq]
    exact le_sup_right
  have hℓ₁ : N₁'.ℓ.range ≤ N₁'.M₁ := by
    rw [← N₁'.M₁_eq]
    exact le_sup_right
  have hres₀ := N₀.perfectResidualOf_N_eq hB₀ hf2 hKc
  have hres₁ := N₁'.perfectResidualOf_N_eq hB₁ hf2 hKc
  have hcard₀ := N₀.card_perfectResidualOf_N hB₀ hf2 hKc hKc
  have hcard₁ := N₁'.card_perfectResidualOf_N hB₁ hf2 hKc hKc
  have hsup : G₁ ⊔ G₁.map (MulAut.conj d.t).toMonoidHom =
      CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf w₀.N ⊔
        CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf w₁.N := by
    rw [hres₀, hres₁, hG₁]
    exact sup_map_sup_eq (g := d.t) hℓ₀ hℓ₁ hM₀ hM₁
  exact ⟨N₀, N₁', hq, hc, hne, hodd, hquot, hAP, hres₀, hres₁, hsup, hcard₀, hcard₁⟩

end CFSG.ComponentClassification.GS79bSec5

end
