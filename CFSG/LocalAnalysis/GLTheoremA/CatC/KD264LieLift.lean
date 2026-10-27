module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCoreS
public import CFSG.GroupTheory.PLayer.CenterQuotientAction

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.OuterAutomorphisms

@[expose] noncomputable def kd264Rho {Y : Type} [Group Y] {K B : Subgroup Y}
    (hBN : B ≤ Subgroup.normalizer (K : Set Y)) {S : Type} [Group S]
    (eK : ↥K ⧸ Subgroup.center ↥K ≃* S) : ↥B →* MulAut S :=
  (MulAut.congr eK).toMonoidHom.comp (CFSG.normalizerToCenterQuotientAut K B hBN)

theorem ker_kd264Rho {Y : Type} [Group Y] {K B : Subgroup Y} (hperf : Group.IsPerfect ↥K)
    (hBN : B ≤ Subgroup.normalizer (K : Set Y)) {S : Type} [Group S]
    (eK : ↥K ⧸ Subgroup.center ↥K ≃* S) :
    (kd264Rho hBN eK).ker = (B ⊓ Subgroup.centralizer (K : Set Y)).subgroupOf B := by
  ext b
  rw [MonoidHom.mem_ker, kd264Rho, MonoidHom.comp_apply,
    ← ker_normalizerToCenterQuotientAut hperf hBN, MonoidHom.mem_ker]
  exact (MulAut.congr eK).map_eq_one_iff

theorem card_range_kd264Rho_mul {Y : Type} [Group Y] [Finite Y] {K B : Subgroup Y}
    (hperf : Group.IsPerfect ↥K) (hBN : B ≤ Subgroup.normalizer (K : Set Y)) {S : Type}
    [Group S] (eK : ↥K ⧸ Subgroup.center ↥K ≃* S) :
    Nat.card (kd264Rho hBN eK).range * Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) =
      Nat.card B := by
  set H : Subgroup ↥B := (B ⊓ Subgroup.centralizer (K : Set Y)).subgroupOf B with hH
  have hidx : Nat.card (kd264Rho hBN eK).range = H.index := by
    rw [← Subgroup.index_ker (kd264Rho hBN eK), ker_kd264Rho hperf hBN eK]
  have hcard : Nat.card ↥H = Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show B ⊓ Subgroup.centralizer (K : Set Y) ≤ B from inf_le_left)).toEquiv
  rw [hidx, ← hcard]
  exact (Nat.mul_comm _ _).trans (Subgroup.card_mul_index H)

theorem kd264Rho_mem_range_conj {Y : Type} [Group Y] {K B : Subgroup Y}
    (hBN : B ≤ Subgroup.normalizer (K : Set Y)) {S : Type} [Group S]
    (eK : ↥K ⧸ Subgroup.center ↥K ≃* S) (b : ↥B) (l : ↥K)
    (h : ∀ y ∈ K, (b : Y)⁻¹ * y * b = (l : Y)⁻¹ * y * l) :
    kd264Rho hBN eK b ∈ (MulAut.conj : S →* MulAut S).range := by
  have hb : normalizerConjAutOfMem K B hBN b = MulAut.conj l := by
    ext k
    simp only [MulAut.conj_apply, normalizerConjAutOfMem,
      Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_mul, Subgroup.coe_inv]
    have hk := h (l * k * l⁻¹) (K.mul_mem (K.mul_mem l.2 k.2) (K.inv_mem l.2))
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hk
    have hk' : (b : Y)⁻¹ * ((l : Y) * (k : Y) * (l : Y)⁻¹) * (b : Y) = (k : Y) := by
      rw [hk]; group
    calc (b : Y) * (k : Y) * (b : Y)⁻¹
        = (b : Y) * ((b : Y)⁻¹ * ((l : Y) * (k : Y) * (l : Y)⁻¹) * (b : Y)) *
            (b : Y)⁻¹ := by rw [hk']
      _ = (l : Y) * (k : Y) * (l : Y)⁻¹ := by group
  have hq : normalizerToCenterQuotientAut K B hBN b =
      MulAut.conj (QuotientGroup.mk' (Subgroup.center ↥K) l) := by
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H k =>
      change normalizerToCenterQuotientAut K B hBN b
          ((QuotientGroup.mk' (Subgroup.center ↥K)) k) =
        MulAut.conj ((QuotientGroup.mk' (Subgroup.center ↥K)) l)
          ((QuotientGroup.mk' (Subgroup.center ↥K)) k)
      rw [← normalizerConjAutOfMem_comp_mk K B hBN b k, hb]
      simp [MulAut.conj_apply]
  have hfinal : kd264Rho hBN eK b =
      MulAut.conj (eK (QuotientGroup.mk' (Subgroup.center ↥K) l)) := by
    rw [kd264Rho, MonoidHom.comp_apply, hq]
    ext x
    simp [MulAut.congr, MulAut.conj_apply]
  exact ⟨_, hfinal.symm⟩

@[expose] def KD264LiftGood (p : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K B : Subgroup Y)
    (hBN : B ≤ Subgroup.normalizer (K : Set Y)) (S : Type) [Group S] [Finite S]
    (eK : ↥K ⧸ Subgroup.center ↥K ≃* S) (F : Subgroup (MulAut S)),
    F ≤ (kd264Rho hBN eK).range → IsGood p F →
    GLAPLayer p (K ⊓ Subgroup.centralizer
      (((F.comap (kd264Rho hBN eK)).map B.subtype : Subgroup Y) : Set Y)) ≠ ⊥

@[expose] def KD264LiftLow (p : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K B : Subgroup Y)
    (hBN : B ≤ Subgroup.normalizer (K : Set Y)) (d : TauCeti.ValidLieTypeIndex)
    [Finite (TauCeti.CFSGIndex.lie d).Group]
    (eK : ↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group) (m : ℕ),
    CFSG.Open.IsQuasisimple ↥K → IsElemAbelian p B → IsMaxRankIn p B ⊤ →
    Nat.card (kd264Rho hBN eK).range = p ^ m →
    ∀ k, i5LowBound p d.1 k → k ≤ m

@[expose] def KD264LiftNoMult (p : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K B : Subgroup Y)
    (hBN : B ≤ Subgroup.normalizer (K : Set Y)) (d : TauCeti.ValidLieTypeIndex)
    [Finite (TauCeti.CFSGIndex.lie d).Group]
    (eK : ↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group) (m : ℕ),
    CFSG.Open.IsQuasisimple ↥K → GLAPPrimeCore p ↥K = ⊥ → IsElemAbelian p B →
    IsMaxRankIn p B ⊤ → Nat.card (kd264Rho hBN eK).range = p ^ m →
    p ≠ d.1.characteristic → ¬ multIdx p d.1 →
    CFSG.Open.pRank p (⊤ : Subgroup (TauCeti.CFSGIndex.lie d).Group) ≤ m ∧
    ∀ a ∈ (kd264Rho hBN eK).range, a ∉ (MulAut.conj :
        (TauCeti.CFSGIndex.lie d).Group →* MulAut (TauCeti.CFSGIndex.lie d).Group).range →
      ∀ E : Subgroup (TauCeti.CFSGIndex.lie d).Group, E ≤ fixSubgroup a → IsElemAbelian p E →
        CFSG.Open.pRank p E + 1 ≤ m

@[expose] def KD264LiftField (p : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K B : Subgroup Y)
    (hBN : B ≤ Subgroup.normalizer (K : Set Y)) (d : TauCeti.ValidLieTypeIndex)
    [Finite (TauCeti.CFSGIndex.lie d).Group]
    (eK : ↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group) (m : ℕ),
    CFSG.Open.IsQuasisimple ↥K → IsElemAbelian p B → IsMaxRankIn p B ⊤ →
    Nat.card (kd264Rho hBN eK).range = p ^ m →
    p = 3 → ∀ a ∈ (kd264Rho hBN eK).range,
      a ∉ innAutDerived (TauCeti.CFSGIndex.lie d).Group →
      ∀ k, i5FieldBound d.1 k → k + 1 ≤ m

@[expose] def KD264LiftMRJ (p : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K B : Subgroup Y)
    (hBN : B ≤ Subgroup.normalizer (K : Set Y)) (d : TauCeti.ValidLieTypeIndex)
    [Finite (TauCeti.CFSGIndex.lie d).Group]
    (eK : ↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group) (m : ℕ),
    CFSG.Open.IsQuasisimple ↥K → IsElemAbelian p B → IsMaxRankIn p B ⊤ →
    Nat.card (kd264Rho hBN eK).range = p ^ m →
    ∀ β ∈ (kd264Rho hBN eK).range, β ≠ 1 →
    ∀ J : Subgroup (TauCeti.CFSGIndex.lie d).Group, GLAPComponent p (fixSubgroup β) J →
    ∀ e : TauCeti.ValidLieTypeIndex,
      Nonempty (↥J ⧸ Subgroup.center ↥J ≃* (TauCeti.CFSGIndex.lie e).Group) →
      lpEpsIdx p e.1 → p - 1 ≤ m

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
