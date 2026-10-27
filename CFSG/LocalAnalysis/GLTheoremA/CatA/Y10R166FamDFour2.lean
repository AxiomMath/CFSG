module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166FamDFour

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open Subgroup CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.SeitzReduction.OmegaPilot CFSG.SeitzReduction.SymplecticPilot
open DFour

variable {F : Type} [Field F] [Finite F] [CharP F 2]

section CertsLabelToModel

theorem exists_mulEquiv_statedOmega_of_isLabel {K : Type} [Group K] [Finite K] {n : ℕ}
    (hn : 2 ≤ n) (hK : HasLabel K (fun l : GLALabel => l = ⟨.D, 4, n⟩))
    (hZ : Subgroup.center K = ⊥) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      Nat.card F = 2 ^ n ∧ Nonempty (K ≃* StatedOmega (StatedQuadPlus 4 F)) := by
  obtain ⟨-, -, hM⟩ := quasisimple_markedModel_of_isLabel hK
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .POmegaPlus 4 2 n := by
    simpa [CFSG.StandardType.MarkedModel, CFSG.StandardType.markTag,
      CFSG.StandardType.markRank, CFSG.StandardType.markChar, CFSG.StandardType.markDeg,
      if_neg (by norm_num : (4 : ℕ) ≠ 3)] using hM
  obtain ⟨-, F, hfield, hfinite, hcard, ⟨e⟩⟩ := hM'.statedClassicalModel (by decide)
  letI : Field F := hfield
  letI : Finite F := hfinite
  haveI : Fintype F := Fintype.ofFinite F
  have hcard' : Fintype.card F = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  haveI : CharP F 2 := charP_of_card_eq_prime_pow hcard' 
  have hZΩ : Subgroup.center (StatedOmega (StatedQuadPlus 4 F)) =
      (StatedScalars (Fin 4 ⊕ Fin 4) F).subgroupOf (StatedOmega (StatedQuadPlus 4 F)) :=
    CFSG.LieType.Universal.Spin.center_statedOmega_quadPlus (by norm_num)
  have hZbot : Subgroup.center (StatedOmega (StatedQuadPlus 4 F)) = ⊥ := by
    rw [hZΩ]
    refine CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot
      (Q := CFSG.LieType.Universal.Spin.quadPlus 4 F)
      (CFSG.LieType.Universal.Spin.coe_quadPlus 4 F) ?_
    refine ⟨fun a => if a = Sum.inl (0 : Fin 4) then 1
      else if a = Sum.inr (0 : Fin 4) then 1 else 0, ?_⟩
    rw [CFSG.LieType.Universal.Spin.coe_quadPlus]
    simp [StatedQuadPlus]
  let eProj : StatedProj (StatedOmega (StatedQuadPlus 4 F)) ≃*
      StatedOmega (StatedQuadPlus 4 F) :=
    (QuotientGroup.quotientMulEquivOfEq hZΩ).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hZbot).trans QuotientGroup.quotientBot)
  let eZ : K ≃* K ⧸ Subgroup.center K :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  exact ⟨F, hfield, hfinite, inferInstance, hcard, ⟨eZ.trans (e.trans eProj)⟩⟩

end CertsLabelToModel

private theorem center_statedOmega_quadPlus_eq_bot {n : ℕ} (hn : 3 ≤ n) :
    Subgroup.center (StatedOmega (StatedQuadPlus n F)) = ⊥ := by
  haveI : NeZero n := ⟨by omega⟩
  rw [CFSG.LieType.Universal.Spin.center_statedOmega_quadPlus hn]
  refine CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot
    (Q := CFSG.LieType.Universal.Spin.quadPlus n F)
    (CFSG.LieType.Universal.Spin.coe_quadPlus n F) ?_
  refine ⟨fun a => if a = Sum.inl (0 : Fin n) then 1
    else if a = Sum.inr (0 : Fin n) then 1 else 0, ?_⟩
  rw [CFSG.LieType.Universal.Spin.coe_quadPlus]
  simp [StatedQuadPlus]

private theorem rootsOfUnity_mem_and_ne_one_of_orderOf {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {s : Fˣ} (hs : orderOf s = q) : s ∈ rootsOfUnity q F ∧ s ≠ 1 ∧ s * s ≠ 1 := by
  have hsμ : s ∈ rootsOfUnity q F := by
    rw [mem_rootsOfUnity q s, ← hs]
    exact pow_orderOf_eq_one s
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hs
    exact hq.ne_one hs.symm
  have hs2 : s * s ≠ 1 := by
    intro h
    have hdvd : orderOf s ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
    have hle : orderOf s ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have h3 : 3 ≤ q := by have := hq.two_le; omega
    rw [hs] at hle
    omega
  exact ⟨hsμ, hs1, hs2⟩

section CertsModelFamily


theorem evenRank_statedOmega_quadPlus_four {n : ℕ} (hn : 2 ≤ n)
    (hFcard : Nat.card F = 2 ^ n) :
    evenRank (StatedOmega (StatedQuadPlus 4 F)) = 4 := by
  have hlab := hasLabel_statedOmega_quadPlus_four (F := F) hn hFcard
  have hK : Rk2IsLabel (StatedOmega (StatedQuadPlus 4 F)) ⟨.D, 4, n⟩ := hlab
  have hup : evenRank (StatedOmega (StatedQuadPlus 4 F)) ≤ 4 :=
    (rk2_eUpAt_of_tables rk2KRank rk2Upper_holds
      (K := StatedOmega (StatedQuadPlus 4 F)) (lab := ⟨.D, 4, n⟩) hK).bd (Or.inr rfl) hn
  have hF4 : 4 ≤ Nat.card F := by
    rw [hFcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hodd : Odd (Nat.card F - 1) := by
    rw [hFcard]
    have h2even : Even (2 ^ n) := even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))
    have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    exact Nat.Even.sub_odd hpos h2even odd_one
  obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd (n := Nat.card F - 1) (by
    rw [hFcard]
    have : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega)
  have hq2 : q ≠ 2 := by
    intro h
    subst h
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hqdvd)
  exact le_antisymm hup
    (four_le_evenRank_statedOmega_quadPlus hF4 hq hq2 hqdvd hFcard hn)

private theorem shape_statedOmega_quadPlus_four {n : ℕ} (hn : 2 ≤ n)
    (hFcard : Nat.card F = 2 ^ n)
    (he : 4 ≤ evenRank (StatedOmega (StatedQuadPlus 4 F))) :
    ∀ lab : GLALabel,
      HasLabel (StatedOmega (StatedQuadPlus 4 F)) (fun l : GLALabel => l = lab) →
      JShape lab (3 ∣ Nat.card (Subgroup.center (StatedOmega (StatedQuadPlus 4 F))))
        ⟨.D, 3, n⟩ := by
  intro lab hlab
  have hR : HasLabel (StatedOmega (StatedQuadPlus 4 F))
      (fun l : GLALabel => l = ⟨.D, 4, n⟩) := hasLabel_statedOmega_quadPlus_four hn hFcard
  rcases label_eq_or_BC (K := StatedOmega (StatedQuadPlus 4 F)) he hlab hR with
    heq | ⟨-, h2, -, -⟩
  · subst heq
    exact ⟨rfl, Or.inr (Or.inl ⟨rfl, rfl, by norm_num⟩)⟩
  · exact absurd h2 (by simp)

private theorem dvd_card_quot_center_JOmega {p q n : ℕ} (hF4 : 4 ≤ Nat.card F)
    (hn : 2 ≤ n) (hFcard : Nat.card F = 2 ^ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpvd : p ∣ 2 ^ n + 1) (hq : q.Prime) (hq2 : q ≠ 2)
    (hqdvd : q ∣ Nat.card F - 1) :
    p * q ∣ Nat.card (↥(OmegaSiegel.JOmega (F := F) hF4) ⧸
      Subgroup.center ↥(OmegaSiegel.JOmega (F := F) hF4)) := by
  have hJlab := hasLabel_JOmega hF4 hn hFcard
  have hGA : CFSG.Open.GriessAllModelsStatement :=
    CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
  have hmult := linearDThree_mult (J := ↥(OmegaSiegel.JOmega (F := F) hF4)) (n := n)
    hn hJlab hGA
  have hpdvd2 : p ∣ 2 ^ (2 * n) - 1 := by
    have hfac : 2 ^ (2 * n) - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
      rw [show 2 * n = n * 2 by omega, pow_mul, show (1 : ℕ) = 1 ^ 2 by norm_num,
        Nat.sq_sub_sq]
      ring
    rw [hfac]
    exact dvd_mul_of_dvd_left hpvd _
  have hqdvd2 : q ∣ 2 ^ (2 * n) - 1 := by
    have hq' : q ∣ 2 ^ n - 1 := by rwa [hFcard] at hqdvd
    have hfac : 2 ^ (2 * n) - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
      rw [show 2 * n = n * 2 by omega, pow_mul, show (1 : ℕ) = 1 ^ 2 by norm_num,
        Nat.sq_sub_sq]
      ring
    rw [hfac]
    exact dvd_mul_of_dvd_right hq' _
  have hpq : p ≠ q := by
    intro hpq
    have hq' : q ∣ 2 ^ n - 1 := by rwa [hFcard] at hqdvd
    have hp' : q ∣ 2 ^ n + 1 := hpq ▸ hpvd
    have hsub : q ∣ (2 ^ n + 1) - (2 ^ n - 1) := Nat.dvd_sub hp' hq'
    have h2 : (2 ^ n + 1) - (2 ^ n - 1) = 2 := by omega
    rw [h2] at hsub
    exact hp2 (hpq ▸ (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hsub)
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.coprime_primes hp hq).2 hpq)
    (hmult.2.2.2 p hp hp2 hpdvd2) (hmult.2.2.2 q hq hq2 hqdvd2)

theorem concl166S_siegelTorus {p q n : ℕ} {s : Fˣ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hn : 2 ≤ n) (hFcard : Nat.card F = 2 ^ n) (hpvd : p ∣ 2 ^ n + 1)
    (hq : q.Prime) (hq2 : q ≠ 2) (hqdvd : q ∣ Nat.card F - 1) (hs : orderOf s = q) :
    ∃ (B' : Subgroup (StatedOmega (StatedQuadPlus 4 F)))
      (x' : StatedOmega (StatedQuadPlus 4 F))
      (J : Subgroup (StatedOmega (StatedQuadPlus 4 F))),
      Concl166S (StatedOmega (StatedQuadPlus 4 F)) p q B' x' J := by
  classical
  have hF4 : 4 ≤ Nat.card F := by
    rw [hFcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have heven : evenRank (StatedOmega (StatedQuadPlus 4 F)) = 4 :=
    evenRank_statedOmega_quadPlus_four hn hFcard
  have he : 4 ≤ evenRank (StatedOmega (StatedQuadPlus 4 F)) := by rw [heven]
  have hZR := center_statedOmega_quadPlus_eq_bot (F := F) (n := 4) (by norm_num)
  obtain ⟨hsμ, hs1, hs2⟩ := rootsOfUnity_mem_and_ne_one_of_orderOf hq hq2 hs
  set B : Subgroup (StatedOmega (StatedQuadPlus 4 F)) := OmegaSiegel.BOmega (F := F) hF4 q
  set x : StatedOmega (StatedQuadPlus 4 F) := OmegaSiegel.xOmega (F := F) s
  set J : Subgroup (StatedOmega (StatedQuadPlus 4 F)) := OmegaSiegel.JOmega (F := F) hF4
  set S : Subgroup (StatedOmega (StatedQuadPlus 4 F)) := OmegaSiegel.SOmega (F := F) hF4
  set E : Subgroup (StatedOmega (StatedQuadPlus 4 F)) := ED4Gen (F := F) hF4 s
  have hB : IsElemAbelian q B := OmegaSiegel.isElemAbelian_BOmega hF4 q hqdvd
  have hx : x ∈ B := OmegaSiegel.xOmega_mem_BOmega hF4 hq hqdvd hs
  have hx1 : x ≠ 1 := OmegaSiegel.xOmega_ne_one hF4 hs1
  have hrankB : Nat.card B = q ^ evenRank (StatedOmega (StatedQuadPlus 4 F)) := by
    rw [heven]
    exact OmegaSiegel.card_BOmega hF4 q hq hqdvd
  have hcent : Subgroup.centralizer ({x} : Set (StatedOmega (StatedQuadPlus 4 F))) =
      (omegaLeviGL F 4).subgroupOf (StatedOmega (StatedQuadPlus 4 F)) :=
    centralizer_siegelTorus_singleton (F := F) hF4 (s := s) hs2
  have hJx : J ≤ Subgroup.centralizer ({x} : Set (StatedOmega (StatedQuadPlus 4 F))) := by
    have h := JOmega_le_centralizer_xOmega hF4 s
    rw [hcent] at h ⊢
    exact h
  have hJq : CFSG.IsQuasisimple ↥J := isQuasisimple_JOmega hF4
  have hcomm : ∀ g ∈ Subgroup.centralizer ({x} : Set (StatedOmega (StatedQuadPlus 4 F))),
      ∀ h ∈ Subgroup.centralizer ({x} : Set (StatedOmega (StatedQuadPlus 4 F))),
      g * h * g⁻¹ * h⁻¹ ∈ J := by
    intro g hg h hh
    rw [hcent] at hg hh
    have hg' : ((g : StatedOmega (StatedQuadPlus 4 F)) : GL (Fin 4 ⊕ Fin 4) F) ∈
        omegaLeviGL F 4 := Subgroup.mem_subgroupOf.1 hg
    have hh' : ((h : StatedOmega (StatedQuadPlus 4 F)) : GL (Fin 4 ⊕ Fin 4) F) ∈
        omegaLeviGL F 4 := Subgroup.mem_subgroupOf.1 hh
    have hmem : ((g : StatedOmega (StatedQuadPlus 4 F)) : GL (Fin 4 ⊕ Fin 4) F) *
        ((h : StatedOmega (StatedQuadPlus 4 F)) : GL (Fin 4 ⊕ Fin 4) F) *
        ((g : StatedOmega (StatedQuadPlus 4 F)) : GL (Fin 4 ⊕ Fin 4) F)⁻¹ *
        ((h : StatedOmega (StatedQuadPlus 4 F)) : GL (Fin 4 ⊕ Fin 4) F)⁻¹ ∈
        omegaLeviSL F 4 :=
      commutator_omegaLeviGL_le (Subgroup.commutator_mem_commutator hg' hh')
    rw [show J = (omegaLeviSL F 4).subgroupOf
      (StatedOmega (StatedQuadPlus 4 F)) from JOmega_eq_omegaLeviSL_subgroupOf hF4]
    exact Subgroup.mem_subgroupOf.2 hmem
  have hJlab := hasLabel_JOmega hF4 hn hFcard
  have hshape := shape_statedOmega_quadPlus_four (F := F) hn hFcard he
  have hGA : CFSG.Open.GriessAllModelsStatement :=
    CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
  have hmult := linearDThree_mult (J := ↥J) (n := n) hn hJlab hGA
  have hsix := hmult.1
  have hodd := hmult.2.1
  have hm2 : evenRank (StatedOmega (StatedQuadPlus 4 F)) + 2 ≤ twoRank ↥J := by
    rw [heven]
    have h4n : 4 * n ≤ twoRank ↥J := hmult.2.2.1
    omega
  have hdvd := dvd_card_quot_center_JOmega (F := F) hF4 hn hFcard hp hp2 hpvd hq hq2 hqdvd
  have hE : IsElemAbelian q E := isElemAbelian_ED4Gen hF4 hq hqdvd hs
  have hEcard : Nat.card E = q ^ 3 := card_ED4Gen hF4 hq hqdvd hs
  have hEB : E ≤ B := ED4Gen_le_BOmega hF4 hq hqdvd hs
  have hxE : x ∈ E := xOmega_mem_ED4Gen hF4 s
  have he3 : GLAPLayer q (J ⊓ Subgroup.centralizer (E : Set
      (StatedOmega (StatedQuadPlus 4 F)))) ≠ ⊥ :=
    glaPLayer_JOmega_inf_centralizer_ED4Gen_ne_bot hF4 hq hqdvd hs
  have hBJ : B ≤ J ⊔ Subgroup.zpowers x :=
    OmegaSiegel.BOmega_le_sup_JOmega_zpowers hF4 hq hq2 hqdvd hs
  have hrankinf : evenRank (StatedOmega (StatedQuadPlus 4 F)) ≤
      CFSG.Open.pRank q (B ⊓ J) + 2 := by
    rw [heven]
    have h3 : 3 ≤ CFSG.Open.pRank q (B ⊓ J) := by
      simpa [B, J] using OmegaSiegel.pRank_BOmega_inf_JOmega_ge_three hF4 q hq hqdvd
    omega
  have hS2 : IsPGroup 2 S := OmegaSiegel.isPGroup_two_SOmega hF4 hFcard
  have hSJ : S ≤ J := OmegaSiegel.SOmega_le_JOmega hF4
  have hBS : B ≤ Subgroup.normalizer (S : Set (StatedOmega (StatedQuadPlus 4 F))) :=
    OmegaSiegel.BOmega_le_normalizer_SOmega hF4 q
  have hBJS : B ⊓ J ⊓ Subgroup.centralizer (S : Set
      (StatedOmega (StatedQuadPlus 4 F))) ≤ Subgroup.zpowers x :=
    OmegaSiegel.BOmega_inf_JOmega_inf_centralizer_le_zpowers hF4 hq hq2 hqdvd hs
  have hsu : 3 ∣ Nat.card (Subgroup.center (StatedOmega (StatedQuadPlus 4 F))) →
      (∃ lab : GLALabel, HasLabel (StatedOmega (StatedQuadPlus 4 F))
        (fun l : GLALabel => l = lab) ∧
        ((lab.tag = .twA ∧ lab.rank = 5) ∨ lab.tag = .twE6)) →
      J = ⊤ ∧ q = 3 ∧ ∀ k : StatedOmega (StatedQuadPlus 4 F), k * x = x * k := by
    intro h3 _
    exact absurd h3 (by rw [hZR]; simp)
  exact ⟨B, x, J, concl166S_of_witness (K := StatedOmega (StatedQuadPlus 4 F)) hq hq2 hB hx
    hx1 hrankB he hJx hJq hcomm ⟨.D, 3, n⟩ hJlab hshape hm2 hodd hdvd (Or.inl hsix) E hEB hE hEcard
    hxE he3 hBJ hrankinf S hSJ hS2 hBS hBJS hsu⟩

theorem exists_concl166S_statedOmega_quadPlus_four {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hn : 2 ≤ n) (hFcard : Nat.card F = 2 ^ n) (hpvd : p ∣ 2 ^ n + 1) :
    ∃ (q : ℕ) (B' : Subgroup (StatedOmega (StatedQuadPlus 4 F)))
      (x' : StatedOmega (StatedQuadPlus 4 F))
      (J : Subgroup (StatedOmega (StatedQuadPlus 4 F))),
      Concl166S (StatedOmega (StatedQuadPlus 4 F)) p q B' x' J := by
  have hF4 : 4 ≤ Nat.card F := by
    rw [hFcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hodd : Odd (Nat.card F - 1) := by
    rw [hFcard]
    have h2even : Even (2 ^ n) := even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))
    have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    exact Nat.Even.sub_odd hpos h2even odd_one
  obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd (n := Nat.card F - 1) (by
    rw [hFcard]
    have : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega)
  have hq2 : q ≠ 2 := by
    intro h
    subst h
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hqdvd)
  haveI : Fact q.Prime := ⟨hq⟩
  have hqdvd' : q ∣ Nat.card Fˣ := by rwa [Nat.card_units]
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) q hqdvd'
  exact ⟨q, concl166S_siegelTorus (F := F) hp hp2 hn hFcard hpvd hq hq2 hqdvd hs⟩

theorem i166On_famDFour_of_transport
    (htr : ∀ {K R : Type} [Group K] [Finite K] [Group R] [Finite R], (K ≃* R) → ∀ {p : ℕ},
      (∃ (q : ℕ) (B' : Subgroup R) (x' : R) (J : Subgroup R), Concl166S R p q B' x' J) →
      ∃ (q : ℕ) (B' : Subgroup K) (x' : K) (J : Subgroup K), Concl166S K p q B' x' J) :
    I166On (fun lab p z => i166FamD lab p z ∧ lab.rank = 4) := by
  intro K _ _ lab p hlab hfam hp hp2 hns he hr
  obtain ⟨t, r, s⟩ := lab
  obtain ⟨⟨ht, hn, hpvd⟩, hr4⟩ := hfam
  subst ht
  subst hr4
  have hZ : Subgroup.center K = ⊥ :=
    rk2_center_eq_bot_of_large hlab (Or.inr (Or.inl rfl)) hn
  obtain ⟨F, hfield, hfinite, hchar, hcard, ⟨e⟩⟩ :=
    exists_mulEquiv_statedOmega_of_isLabel (K := K) (n := s) hn hlab hZ
  letI : Field F := hfield
  letI : Finite F := hfinite
  letI : CharP F 2 := hchar
  exact htr e (exists_concl166S_statedOmega_quadPlus_four (F := F) hp hp2 hn hcard hpvd)

theorem i166On_famD_of_transport
    (htr : ∀ {K R : Type} [Group K] [Finite K] [Group R] [Finite R], (K ≃* R) → ∀ {p : ℕ},
      (∃ (q : ℕ) (B' : Subgroup R) (x' : R) (J : Subgroup R), Concl166S R p q B' x' J) →
      ∃ (q : ℕ) (B' : Subgroup K) (x' : K) (J : Subgroup K), Concl166S K p q B' x' J)
    (h5 : I166On (fun lab p z => i166FamD lab p z ∧ 5 ≤ lab.rank)) :
    I166On i166FamD := by
  intro K _ _ lab p hlab hfam hp hp2 hns he hr
  by_cases h5' : 5 ≤ lab.rank
  · exact h5 K lab p hlab ⟨hfam, h5'⟩ hp hp2 hns he hr
  · have hbd : evenRank K ≤ lab.rank :=
      (rk2_eUpAt_of_tables rk2KRank rk2Upper_holds (K := K) (lab := lab) hlab).bd
        (Or.inr hfam.1) hfam.2.1
    have hrank4 : lab.rank = 4 := by omega
    exact i166On_famDFour_of_transport htr K lab p hlab ⟨hfam, hrank4⟩ hp hp2 hns he hr

end CertsModelFamily

end CFSG.LocalAnalysis.GLTheoremA.Y10F
