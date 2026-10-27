module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019Quot
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S267
open scoped commutatorElement

section Act

variable {Ω : Type} [Group Ω]

@[expose] noncomputable def actQuot (S : Subgroup Ω) [S.Normal] :
    Ω →* MulAut (↥S ⧸ Subgroup.center ↥S) where
  toFun g := QuotientGroup.congr (Subgroup.center ↥S) (Subgroup.center ↥S)
    (MulAut.conjNormal g : ↥S ≃* ↥S) (Subgroup.map_center_eq _)
  map_one' := by
    apply MulEquiv.ext
    intro x
    induction x using QuotientGroup.induction_on with
    | H k =>
      rw [MulAut.one_apply, QuotientGroup.congr_mk]
      congr 1
      apply Subtype.ext
      simp
  map_mul' g h := by
    apply MulEquiv.ext
    intro x
    induction x using QuotientGroup.induction_on with
    | H k =>
      rw [MulAut.mul_apply, QuotientGroup.congr_mk, QuotientGroup.congr_mk, QuotientGroup.congr_mk]
      congr 1
      apply Subtype.ext
      simp only [MulAut.mul_apply, MulAut.conjNormal_apply, map_mul, Subgroup.coe_mul, mul_assoc]

theorem actQuot_mk (S : Subgroup Ω) [S.Normal] (g : Ω) (s : ↥S) :
    actQuot S g (QuotientGroup.mk s) =
      QuotientGroup.mk (MulAut.conjNormal g s : ↥S) :=
  QuotientGroup.congr_mk _ _ _ (Subgroup.map_center_eq _) _

theorem commutator_actQuot_le_center (S : Subgroup Ω) [S.Normal] {K : Subgroup Ω}
    (hK : ∀ k ∈ K, actQuot S k = 1) : ⁅S, K⁆ ≤ (Subgroup.center ↥S).map S.subtype := by
  rw [Subgroup.commutator_le]
  intro s hs k hk
  set t : ↥S := ⟨s, hs⟩ with ht
  have h1 : actQuot S k (QuotientGroup.mk t⁻¹) = QuotientGroup.mk t⁻¹ := by
    rw [hK k hk, MulAut.one_apply]
  rw [actQuot_mk, QuotientGroup.eq] at h1
  refine ⟨((MulAut.conjNormal k t⁻¹ : ↥S)⁻¹ * t⁻¹)⁻¹, Subgroup.inv_mem _ h1, ?_⟩
  simp only [Subgroup.coe_subtype, Subgroup.coe_inv, Subgroup.coe_mul, MulAut.conjNormal_apply,
    ht, commutatorElement_def]
  group

theorem le_centralizer_of_actQuot_eq_one (S : Subgroup Ω) [S.Normal] (hS : ⁅S, S⁆ = S)
    {K : Subgroup Ω} (hK : ∀ k ∈ K, actQuot S k = 1) : K ≤ Subgroup.centralizer (S : Set Ω) := by
  have h1 := commutator_actQuot_le_center S hK
  have hZ : ⁅(Subgroup.center ↥S).map S.subtype, S⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨s, hs⟩)
  have h2 : ⁅⁅S, K⁆, S⁆ = ⊥ := le_bot_iff.1 ((Subgroup.commutator_mono h1 le_rfl).trans hZ.le)
  have h3 : ⁅⁅K, S⁆, S⁆ = ⊥ := by rw [Subgroup.commutator_comm K S]; exact h2
  have h4 : ⁅⁅S, S⁆, K⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h2 h3
  rw [hS, Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at h4
  exact h4

theorem commutator_self_eq_of_isQuasisimple {S : Subgroup Ω} (hSq : CFSG.Open.IsQuasisimple ↥S) :
    ⁅S, S⁆ = S := by
  have h := congrArg (Subgroup.map S.subtype) hSq.1
  rw [commutator_def, Subgroup.map_commutator] at h
  simpa only [Subgroup.map_top, Subgroup.range_subtype] using h

end Act

section Main

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem exists_elemAbelian_aut_rank_ge_three {p : ℕ} (hp : p.Prime) {S B D : Subgroup Ω}
    (hSn : S.Normal) (hSq : CFSG.Open.IsQuasisimple ↥S) (hSp : GLAPPrimeCore p ↥S = ⊥)
    (hBel : IsElemAbelian p B) (hCD : B ⊓ centModSubgroup p S ≤ D)
    (hrel : (B ⊓ centModSubgroup p S).relIndex D = p) (hD : p ^ 2 * Nat.card D ≤ Nat.card B) :
    ∃ A : Subgroup (MulAut (↥S ⧸ Subgroup.center ↥S)), IsElemAbelian p A ∧ p ^ 3 ≤ Nat.card A := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hSperf : ⁅S, S⁆ = S := commutator_self_eq_of_isQuasisimple hSq
  have hcore : GLAPPrimeCoreOf p S = ⊥ := glaPPrimeCoreOf_eq_bot hSp
  set φ : ↥B →* MulAut (↥S ⧸ Subgroup.center ↥S) := (actQuot S).comp B.subtype with hφ
  have hkerC : φ.ker ≤ (B ⊓ centModSubgroup p S).subgroupOf B := by
    intro x hx
    have hx1 : φ x = 1 := hx
    have hcen : (x : Ω) ∈ Subgroup.centralizer (S : Set Ω) := by
      refine le_centralizer_of_actQuot_eq_one S hSperf (K := Subgroup.zpowers (x : Ω)) ?_
        (Subgroup.mem_zpowers _)
      intro k hk
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
      rw [map_zpow]
      have : actQuot S (x : Ω) = 1 := hx1
      rw [this, one_zpow]
    refine ⟨x.2, ⟨?_, fun l hl => ?_⟩⟩
    · rw [Subgroup.normalizer_eq_top_iff.2 hSn]
      exact Subgroup.mem_top _
    · rw [hcore, Subgroup.mem_bot, commutatorElement_def]
      have h1 : l * (x : Ω) = (x : Ω) * l := Subgroup.mem_centralizer_iff.1 hcen l hl
      show l * (x : Ω) * l⁻¹ * (x : Ω)⁻¹ = 1
      rw [h1]
      group
  have hkerle : Nat.card φ.ker ≤ Nat.card ↥(B ⊓ centModSubgroup p S) := by
    calc Nat.card φ.ker ≤ Nat.card ↥((B ⊓ centModSubgroup p S).subgroupOf B) :=
          Subgroup.card_le_of_le hkerC
      _ = Nat.card ↥(B ⊓ centModSubgroup p S) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hsplit : Nat.card B = Nat.card φ.range * Nat.card φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker]
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  have hrangeEl : IsElemAbelian p φ.range := by
    have h1 : IsElemAbelian p (⊤ : Subgroup ↥B) := by
      have := isElemAbelian_subgroupOf hBel B
      rwa [Subgroup.subgroupOf_self] at this
    rw [MonoidHom.range_eq_map]
    exact CFSG.SectionRank.isElemAbelian_map h1 φ
  refine ⟨φ.range, hrangeEl, ?_⟩
  have hCpos : 0 < Nat.card ↥(B ⊓ centModSubgroup p S) := Nat.card_pos
  have hDcard : p * Nat.card ↥(B ⊓ centModSubgroup p S) = Nat.card D := by
    have := relIndex_mul_card_of_le hCD
    rw [hrel] at this
    exact this
  have h1 : p ^ 3 * Nat.card ↥(B ⊓ centModSubgroup p S) ≤
      Nat.card φ.range * Nat.card ↥(B ⊓ centModSubgroup p S) := by
    calc p ^ 3 * Nat.card ↥(B ⊓ centModSubgroup p S)
        = p ^ 2 * (p * Nat.card ↥(B ⊓ centModSubgroup p S)) := by ring
      _ = p ^ 2 * Nat.card D := by rw [hDcard]
      _ ≤ Nat.card B := hD
      _ = Nat.card φ.range * Nat.card φ.ker := hsplit
      _ ≤ Nat.card φ.range * Nat.card ↥(B ⊓ centModSubgroup p S) :=
          Nat.mul_le_mul_left _ hkerle
  exact Nat.le_of_mul_le_mul_right h1 hCpos

theorem s2019FactAmbiguous_of_aut (h : S2019FactAmbAut) : S2019FactAmbiguous := by
  intro p q hp hp2 hq hq2 hqp Ω _ _ S B D J hSn hSq hSp hcat hBel hSB hrank
  intro hC hDB hCD hrel hD hJ hBJ hcm T hTS hT2 hJT
  exfalso
  let eS : PQuot p S ≃* ↥S :=
    (QuotientGroup.quotientMulEquivOfEq hSp).trans QuotientGroup.quotientBot
  let eSS : PSimple p S ≃* (↥S ⧸ Subgroup.center ↥S) :=
    QuotientGroup.congr _ _ eS (Subgroup.map_center_eq eS)
  have hcat' : catalogIs (↥S ⧸ Subgroup.center ↥S) (ambiguousChev q) :=
    (catalogIs_congr eSS).1 hcat
  obtain ⟨A, hA, hcard⟩ := exists_elemAbelian_aut_rank_ge_three hp hSn hSq hSp hBel hCD hrel hD
  have hlt := h p q hp hp2 hq hq2 hqp _ hcat' A hA
  have : p ^ 2 ≤ p ^ 3 := Nat.pow_le_pow_right hp.pos (by norm_num)
  omega

end Main

end CFSG.LocalAnalysis.GLTheoremA.S2019

end
