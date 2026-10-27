module

public import CFSG.RankThree.PartTwo.KFacts.L34Aut
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryUnipotentCentralizer
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFamAltAutThree
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallM11Local
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CaseTwoLocalL28
public import CFSG.GH74.KGroups.A6
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Gen
import CFSG.HardMathSupport.Solomon.Coordinator.L3BL34
import CFSG.Quasithin.Background.L34OutFacts

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup

namespace InnerQ.KFC1

@[expose] def SqInner (K : Type*) [Group K] (T : Subgroup K) : Prop :=
  ∀ f : MulAut K, (∀ b ∈ T, f b = b) → ∃ t ∈ T, f ^ 2 = MulAut.conj t

variable {K K' : Type*} [Group K] [Group K'] {T : Subgroup K}

theorem sqInner_of_conj (h : ∀ f : MulAut K, (∀ b ∈ T, f b = b) → ∃ t ∈ T, f = MulAut.conj t) :
    SqInner K T := fun f hf => by
  obtain ⟨t, ht, rfl⟩ := h f hf
  exact ⟨t * t, mul_mem ht ht, by rw [pow_two, map_mul]⟩

theorem sqInner_of_autFixInner {K : Type} [Group K] {p : ℕ} {T : Sylow p K}
    (h : CFSG.AGLEmbedding.KFactProofs.SmallIdent.AutFixInner p K T)
    (hC : ∀ k : K, (∀ b ∈ (T : Subgroup K), k * b = b * k) → k ∈ (T : Subgroup K)) :
    SqInner K T := sqInner_of_conj fun f hf => by
  obtain ⟨k, rfl⟩ := h f hf
  refine ⟨k, hC k fun b hb => ?_, rfl⟩
  have := hf b hb
  rw [MulAut.conj_apply] at this
  calc k * b = k * b * k⁻¹ * k := by group
    _ = b * k := by rw [this]

theorem SqInner.map (e : K ≃* K') (h : SqInner K T) : SqInner K' (T.map e.toMonoidHom) := by
  intro f hf
  set g : MulAut K := (e.trans f).trans e.symm with hg
  have hgT : ∀ b ∈ T, g b = b := fun b hb => by
    have := hf (e b) ⟨b, hb, rfl⟩
    simp [hg, this]
  obtain ⟨t, ht, hgt⟩ := h g hgT
  refine ⟨e t, ⟨t, ht, rfl⟩, ?_⟩
  ext y
  have h1 := congrArg (fun φ : MulAut K => φ (e.symm y)) hgt
  simp only [pow_two, MulAut.mul_apply, MulAut.conj_apply, hg, MulEquiv.trans_apply] at h1
  have h2 := congrArg e h1
  simp only [MulEquiv.apply_symm_apply, map_mul, map_inv] at h2
  simpa [pow_two, MulAut.mul_apply, MulAut.conj_apply] using h2

theorem SqInner.of_equiv {T' : Subgroup K'} (e : K ≃* K') (hT : ∀ g, g ∈ T ↔ e g ∈ T')
    (h : SqInner K T) : SqInner K' T' := by
  have : T' = T.map e.toMonoidHom := by
    ext y
    rw [Subgroup.mem_map_equiv, hT, MulEquiv.apply_symm_apply]
  exact this ▸ h.map e

theorem SqInner.of_sylow {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {S : Sylow p G}
    (h : SqInner G S) (T : Sylow p G) : SqInner G T := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G S T
  refine SqInner.of_equiv (MulAut.conj g) (fun y => ?_) h
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · intro hy
    exact ⟨y, hy, rfl⟩
  · rintro ⟨z, hz, hzy⟩
    rw [MulAut.smul_def] at hzy
    rw [(MulAut.conj g).injective hzy] at hz
    exact hz

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.PartTwo.KFacts.L34 in
theorem sqInner_eZero {k : Type*} [Field k] (hk : Nat.card k = 4) :
    SqInner (projectiveSL 3 k) (eZero k) := by
  obtain ⟨σ, hσ⟩ := CFSG.Quasithin.L34Out.exists_frob hk
  intro f hf
  obtain ⟨e, he, rfl | rfl⟩ := (forall_fixes_eZero_iff hk hσ f).mp hf
  · exact ⟨e * e, mul_mem he he, by rw [pow_two, map_mul]⟩
  · refine ⟨e * e, mul_mem he he, ?_⟩
    have hβe : betaAut σ e = e := betaAut_fixed hk hσ he
    have hcomm : betaAut σ * MulAut.conj e = MulAut.conj e * betaAut σ := by
      refine MulEquiv.ext fun y => ?_
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hβe]
    rw [pow_two, mul_assoc, ← mul_assoc (betaAut σ), hcomm, mul_assoc,
      betaAut_mul_self hk hσ, mul_one, ← map_mul]

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.PartTwo.KFacts.L34 in
theorem sqInner_l34 {K : Type} [Group K] [Finite K]
    (hK : CFSG.RankThree.PartOne.Census3.IsoLie K (.A 2 ⟨2, 2, Nat.prime_two, by norm_num⟩))
    (T : Sylow 3 K) : SqInner K T := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hv, ⟨e⟩⟩ := hK
  have hL := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.isLThreeFour_of_index ⟨_, hv⟩
    ⟨2, 2, Nat.prime_two, by norm_num⟩ rfl ⟨rfl, rfl⟩ e
  obtain ⟨k, _, hk, ⟨φ⟩⟩ := CFSG.HardMathSupport.Solomon.Coordinator.exists_equiv_projectiveSL hL
  haveI : Finite (projectiveSL 3 k) := Finite.of_equiv K φ
  obtain ⟨S⟩ : Nonempty (Sylow 3 (projectiveSL 3 k)) := inferInstance
  have hE : SqInner (projectiveSL 3 k) S := by
    set S₀ : Sylow 3 (projectiveSL 3 k) := Sylow.ofCard (eZero k) (card_eZero_eq hk)
    exact (sqInner_eZero hk).of_sylow (S := S₀) S
  set T' : Sylow 3 (projectiveSL 3 k) := Sylow.ofCard ((T : Subgroup K).map φ.toMonoidHom) (by
    rw [Subgroup.card_map_of_injective φ.injective, Sylow.card_eq_multiplicity,
      Nat.card_congr φ.toEquiv])
  have h' := hE.of_sylow T'
  refine SqInner.of_equiv φ.symm (fun g => ?_) h'
  show g ∈ (T : Subgroup K).map φ.toMonoidHom ↔ φ.symm g ∈ (T : Subgroup K)
  exact Subgroup.mem_map_equiv

theorem sqInner_u3 {K : Type} [Group K] [Finite K] {q : TauCeti.PrimePower} (hq : q.p = 3)
    (hK : CFSG.RankThree.PartOne.Census3.IsoLie K (.twistedA 2 q)) (T : Sylow 3 K) :
    SqInner K T := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hv, he⟩ := hK
  exact sqInner_of_conj fun f hf =>
    CFSG.AGLEmbedding.kFactUnitaryUnipotentCentralizer K 3 ⟨_, hv⟩ ⟨q, hq, rfl⟩ he T f hf

theorem sqInner_a6 {K : Type} [Group K] [Finite K]
    (hK : Nonempty (K ≃* alternatingGroup (Fin 6))) (T : Sylow 3 K)
    (hT : CFSG.Open.IsElemAbelian 3 (T : Subgroup K)) (h9 : Nat.card (T : Subgroup K) = 9) :
    SqInner K T := by
  obtain ⟨e⟩ := CFSG.GH74.KGroups.A6.equiv_of_alt6 hK
  refine sqInner_of_autFixInner
    (CFSG.AGLEmbedding.KFactProofs.SmallIdent.autFixInner_of_isAltTwoP_three hK T) fun k hk => ?_
  refine CFSG.GH74.KGroups.A6.centralizer3 e _ ⟨fun a ha b hb => ?_, hT.2⟩ h9 k hk
  have := hT.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
  exact congrArg Subtype.val this

theorem sqInner_m11 {K : Type}
    [Group K] [Finite K] (hK : Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic .M11).Group))
    (T : Sylow 3 K)
    (hC : ∀ k : K, (∀ b ∈ (T : Subgroup K), k * b = b * k) → k ∈ (T : Subgroup K)) :
    SqInner K T :=
  sqInner_of_autFixInner (CFSG.AGLEmbedding.KFactProofs.SmallIdent.autFixInner_m11 hK T) hC

theorem sqInner_l28 {K : Type} [Group K] [Finite K]
    (hK : CFSG.AGLEmbedding.IsCaseTwoGroup 3 K) (T : Sylow 3 K) : SqInner K T := by
  obtain ⟨ε₀⟩ := CFSG.AGLEmbedding.KFactProofs.L28Local.nonempty_equiv_G8 hK
  exact sqInner_of_conj (CFSG.AGLEmbedding.KFactProofs.L28Local.l28Data_of_equiv ε₀ T).aut

end InnerQ.KFC1

end CFSG.LocalAnalysis.RankThreeTheoremC
