module

public import CFSG.ClassicalInvolution.Q3.Q3T7Q22Sect
public import CFSG.ClassicalInvolution.Q3.Q3T7Q22TSF
public import CFSG.ClassicalInvolution.Q3.Q3T8ThompsonD
public import CFSG.ClassicalInvolution.Q3.Q3T7Q2204

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

abbrev _root_.CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S22.Big
    :=
  @CFSG.ClassicalInvolution.Asc77.S22.Big

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
    CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
    CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Disconnected
namespace T7J
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.T7J
section Twins
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem twin_le_trivialOnQuot
    (hΩ : Q3T8.Asc77.HypOmegaMod Ω) {J J' : Subgroup G} {z : G}
    (hJ : J ∈ Ω) (hJ' : J' ∈ Ω) (hne : J ≠ J') (hz : IsUniqueInvolution J z)
    (hz' : IsUniqueInvolution J' z) : J ≤ trivialOnQuot J' := by
  have h4 := hΩ.omega4 J hJ J' hJ' hne
  have hmem : z ∈ J ⊓ J' := ⟨hz.mem, hz'.mem⟩
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  have hdvd : 2 ∣ Nat.card ↥(J ⊓ J') := by
    have := Subgroup.orderOf_dvd_natCard (J ⊓ J') hmem
    rwa [hz2] at this
  have hpos : Nat.card ↥(J ⊓ J') ≠ 0 := Nat.card_pos.ne'
  have h1 : 1 ≤ padicValNat 2 (Nat.card ↥(J ⊓ J')) :=
    (padicValNat_dvd_iff_le (p := 2) hpos).mp (by simpa using hdvd)
  have heq : padicValNat 2 (Nat.card ↥(J ⊓ J')) = 1 := le_antisymm h4.1 h1
  exact le_trivialOnQuot_of_commutator_le ((h4.2 heq).trans inf_le_right)
end Twins
section Setting
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem comm₁₃
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) : u₁ * u₃ = u₃ * u₁ :=
  T7B.comm_of_mul_self_eq_one h.sq₁ h.sq₃ h.hz.sq h.comm_z₁ (h.hB.2 _ h.mem_B_13)

theorem exists_sylow_triple
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) :
    ∃ R R' R₃ : Subgroup G, IsSylow2In R K ∧ IsSylow2In R' K' ∧ IsSylow2In R₃ K₃ ∧
      u₁ ∈ R ∧ u₂ ∈ R' ∧ u₃ ∈ R₃ ∧ Commutes R R' ∧ Commutes R R₃ ∧ Commutes R' R₃ := by
  have hΩ : Q3T7M.HM Ω := h.stand.modU
  have hK : K ∈ Ω := h.stand.mem
  have hK' : K' ∈ Ω := h.hK'.1
  have hK₃ : K₃ ∈ Ω := h.hK₃.1
  have hz := h.hz
  have hz' := h.hzK'
  have hz₃ := h.hzK₃
  have hne : K' ≠ K := h.hne
  have hne₃ : K₃ ≠ K := h.hK₃K
  have hne₃' : K₃ ≠ K' := h.hK₃K'
  set Z₁ := Subgroup.zpowers u₁ with hZ₁
  set Z₂ := Subgroup.zpowers u₂ with hZ₂
  set Z₃ := Subgroup.zpowers u₃ with hZ₃
  have p₁ : IsPGroup 2 ↥Z₁ := T7A.isPGroup_zpowers_of_orderOf_four h.hu₁.2
  have p₂ : IsPGroup 2 ↥Z₂ := T7A.isPGroup_zpowers_of_orderOf_four h.hu₂.2
  have p₃ : IsPGroup 2 ↥Z₃ := T7A.isPGroup_zpowers_of_orderOf_four h.hu₃.2
  have cm : ∀ {a b : G}, a * b = b * a → Commutes (Subgroup.zpowers a) (Subgroup.zpowers b) := by
    intro a b hab x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow (show Commute a b from hab) i j).eq
  have c12 : Commutes Z₁ Z₂ := cm h.comm₁₂
  have c13 : Commutes Z₁ Z₃ := cm (Q3T8.Asc77.T7J.comm₁₃ h)
  have c23 : Commutes Z₂ Z₃ := cm h.comm₂₃
  have hP12 : IsPGroup 2 ↥(Z₁ ⊔ Z₂) :=
    p₁.to_sup_of_normal_right' p₂ (T7A.le_normalizer_of_commutes c12.symm)
  have hP : IsPGroup 2 ↥((Z₁ ⊔ Z₂) ⊔ Z₃) :=
    hP12.to_sup_of_normal_right' p₃ (sup_le (T7A.le_normalizer_of_commutes c13.symm)
      (T7A.le_normalizer_of_commutes c23.symm))
  set P := (Z₁ ⊔ Z₂) ⊔ Z₃ with hPdef
  have hZ₁P : Z₁ ≤ P := le_sup_left.trans le_sup_left
  have hZ₂P : Z₂ ≤ P := le_sup_right.trans le_sup_left
  have hZ₃P : Z₃ ≤ P := le_sup_right
  have hz₁P : u₁ ∈ P := hZ₁P (Subgroup.mem_zpowers u₁)
  have hz₂P : u₂ ∈ P := hZ₂P (Subgroup.mem_zpowers u₂)
  have hz₃P : u₃ ∈ P := hZ₃P (Subgroup.mem_zpowers u₃)
  have nK₁ : K ≤ Subgroup.normalizer (K' : Set G) :=
    hΩ.le_normalizer_of_twin hK hK' hne.symm hz hz'
  have nK₂ : K ≤ Subgroup.normalizer (K₃ : Set G) :=
    hΩ.le_normalizer_of_twin hK hK₃ hne₃.symm hz hz₃
  have nK₃ : K' ≤ Subgroup.normalizer (K₃ : Set G) :=
    hΩ.le_normalizer_of_twin hK' hK₃ hne₃'.symm hz' hz₃
  have nK₄ : K' ≤ Subgroup.normalizer (K : Set G) := hΩ.le_normalizer_of_twin hK' hK hne hz' hz
  have nK₅ : K₃ ≤ Subgroup.normalizer (K : Set G) :=
    hΩ.le_normalizer_of_twin hK₃ hK hne₃ hz₃ hz
  have nK₆ : K₃ ≤ Subgroup.normalizer (K' : Set G) :=
    hΩ.le_normalizer_of_twin hK₃ hK' hne₃' hz₃ hz'
  have hPK : P ≤ Subgroup.normalizer (K : Set G) :=
    sup_le (sup_le ((Subgroup.zpowers_le.mpr h.hu₁.1).trans Subgroup.le_normalizer)
      ((Subgroup.zpowers_le.mpr h.hu₂.1).trans nK₄))
      ((Subgroup.zpowers_le.mpr h.hu₃.1).trans nK₅)
  have hPK' : P ≤ Subgroup.normalizer (K' : Set G) :=
    sup_le (sup_le ((Subgroup.zpowers_le.mpr h.hu₁.1).trans nK₁)
      ((Subgroup.zpowers_le.mpr h.hu₂.1).trans Subgroup.le_normalizer))
      ((Subgroup.zpowers_le.mpr h.hu₃.1).trans nK₆)
  have hPK₃ : P ≤ Subgroup.normalizer (K₃ : Set G) :=
    sup_le (sup_le ((Subgroup.zpowers_le.mpr h.hu₁.1).trans nK₂)
      ((Subgroup.zpowers_le.mpr h.hu₂.1).trans nK₃))
      ((Subgroup.zpowers_le.mpr h.hu₃.1).trans Subgroup.le_normalizer)
  obtain ⟨R, hR, hRfix⟩ := exists_sylow_normalized hP hPK
  have hPR : P ≤ Subgroup.normalizer (R : Set G) := fun x hx =>
    mem_normalizer_iff_conjSub_eq.mpr (hRfix x hx)
  have hu₁R : u₁ ∈ R := T7B.mem_of_normalizes hR p₁ h.hu₁.1 (hRfix u₁ hz₁P)
  have hP₁ : IsPGroup 2 ↥(P ⊔ R) := hP.to_sup_of_normal_right' hR.2.1 hPR
  have hPR₁ : P ⊔ R ≤ Subgroup.normalizer (K' : Set G) := sup_le hPK' (hR.1.trans nK₁)
  obtain ⟨R', hR', hR'fix⟩ := exists_sylow_normalized hP₁ hPR₁
  have hPR' : P ⊔ R ≤ Subgroup.normalizer (R' : Set G) := fun x hx =>
    mem_normalizer_iff_conjSub_eq.mpr (hR'fix x hx)
  have hPle₁ : P ≤ P ⊔ R := le_sup_left
  have hu₂R' : u₂ ∈ R' := T7B.mem_of_normalizes hR' p₂ h.hu₂.1 (hR'fix u₂ (hPle₁ hz₂P))
  have hP₂ : IsPGroup 2 ↥((P ⊔ R) ⊔ R') := hP₁.to_sup_of_normal_right' hR'.2.1 hPR'
  have hPR₂ : (P ⊔ R) ⊔ R' ≤ Subgroup.normalizer (K₃ : Set G) :=
    sup_le (sup_le hPK₃ (hR.1.trans nK₂)) (hR'.1.trans nK₃)
  obtain ⟨R₃, hR₃, hR₃fix⟩ := exists_sylow_normalized hP₂ hPR₂
  have hPR₃ : (P ⊔ R) ⊔ R' ≤ Subgroup.normalizer (R₃ : Set G) := fun x hx =>
    mem_normalizer_iff_conjSub_eq.mpr (hR₃fix x hx)
  have hPle₂ : P ⊔ R ≤ (P ⊔ R) ⊔ R' := le_sup_left
  have hu₃R₃ : u₃ ∈ R₃ :=
    T7B.mem_of_normalizes hR₃ p₃ h.hu₃.1 (hR₃fix u₃ (hPle₂ (hPle₁ hz₃P)))
  have hQ : IsPGroup 2 ↥(((P ⊔ R) ⊔ R') ⊔ R₃) := hP₂.to_sup_of_normal_right' hR₃.2.1 hPR₃
  have hRQ : R ≤ ((P ⊔ R) ⊔ R') ⊔ R₃ := le_sup_right.trans (le_sup_left.trans le_sup_left)
  have hR'Q : R' ≤ ((P ⊔ R) ⊔ R') ⊔ R₃ := le_sup_right.trans le_sup_left
  have hR₃Q : R₃ ≤ ((P ⊔ R) ⊔ R') ⊔ R₃ := le_sup_right
  refine ⟨R, R', R₃, hR, hR', hR₃, hu₁R, hu₂R', hu₃R₃, ?_, ?_, ?_⟩
  · exact hΩ.commutes_of_twin_of_isPGroup hK hK' hne.symm hz hz' hR.1 hR'.1
      (hQ.to_le (sup_le hRQ hR'Q))
  · exact hΩ.commutes_of_twin_of_isPGroup hK hK₃ hne₃.symm hz hz₃ hR.1 hR₃.1
      (hQ.to_le (sup_le hRQ hR₃Q))
  · exact hΩ.commutes_of_twin_of_isPGroup hK' hK₃ hne₃'.symm hz' hz₃ hR'.1 hR₃.1
      (hQ.to_le (sup_le hR'Q hR₃Q))
end Setting
end T7J
section Residual

@[expose] def Hyp22FourthTwin
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃ →
      ∃ K₄ ∈ twinSet Ω K, K₄ ≠ K ∧ K₄ ≠ K' ∧ K₄ ≠ K₃

theorem hyp22Hyp51u_of_fourthTwin [Fact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp22Hyp51u] (hres :
    TwinSqAlphaRows 3) (h4 : Q3T8.Asc77.Hyp22FourthTwin) :
    Q3T8.Asc77.Hyp22Hyp51u := Fact.out
end Residual
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
namespace Hyp22Setting
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.Hyp22Setting
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem not_mu_S3_S4
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) {W : Subgroup G}
    (hW : W ∈ WSet Ω) : ¬ MuIsoS3 Ω W ∧ ¬ MuIsoS4 Ω W := by
  have hΩ : Q3T7M.HM Ω := h.stand.modU
  have hK : K ∈ Ω := h.stand.mem
  have hK'Ω : K' ∈ Ω := h.hK'.1
  have hK₃Ω : K₃ ∈ Ω := h.hK₃.1
  have hP : Q3T8.Asc77.PartIHyp Ω := ⟨hΩ, h.stand.cls, h.stand.aEmpty⟩
  obtain ⟨R, R', R₃, hRsyl, hR'syl, hR₃syl, hRR', hRR₃, hR'R₃⟩ :=
    Q3T8.Asc77.T7B.exists_threeTwinSylow hΩ hK h.hz h.hK' h.hK₃ h.hne h.hK₃K h.hK₃K'
  
  have hRn : R ≤ Subgroup.normalizer (R' : Set G) := T7A.le_normalizer_of_commutes hRR'.symm
  have hP2 : IsPGroup 2 ↥(R ⊔ R') := hRsyl.2.1.to_sup_of_normal_right' hR'syl.2.1 hRn
  have hPn : R ⊔ R' ≤ Subgroup.normalizer (R₃ : Set G) := sup_le
    (T7A.le_normalizer_of_commutes hRR₃.symm) (T7A.le_normalizer_of_commutes hR'R₃.symm)
  have hQ2 : IsPGroup 2 ↥((R ⊔ R') ⊔ R₃) := hP2.to_sup_of_normal_right' hR₃syl.2.1 hPn
  obtain ⟨S, hS⟩ := hQ2.exists_le_sylow
  have hRS : R ≤ (S : Subgroup G) := le_sup_left.trans (le_sup_left.trans hS)
  have hR'S : R' ≤ (S : Subgroup G) := le_sup_right.trans (le_sup_left.trans hS)
  have hR₃S : R₃ ≤ (S : Subgroup G) := le_sup_right.trans hS
  obtain ⟨g, hg⟩ := Q3T8.Asc77.Thompson.exists_conj_mem_DSet hΩ hW S
  have hRD : conjSub g R ∈ DSet Ω W := hg R (mem_RSet_of_isSylow2In hK hRsyl) hRS
  have hR'D : conjSub g R' ∈ DSet Ω W := hg R' (mem_RSet_of_isSylow2In hK'Ω hR'syl) hR'S
  have hR₃D : conjSub g R₃ ∈ DSet Ω W := hg R₃ (mem_RSet_of_isSylow2In hK₃Ω hR₃syl) hR₃S
  have hKg : conjSub g K ∈ Ω := hΩ.conjInvariant g K hK
  have hK'g : conjSub g K' ∈ Ω := hΩ.conjInvariant g K' hK'Ω
  have hK₃g : conjSub g K₃ ∈ Ω := hΩ.conjInvariant g K₃ hK₃Ω
  have hRsylg : IsSylow2In (conjSub g R) (conjSub g K) := hRsyl.conj g
  have hR'sylg : IsSylow2In (conjSub g R') (conjSub g K') := hR'syl.conj g
  have hR₃sylg : IsSylow2In (conjSub g R₃) (conjSub g K₃) := hR₃syl.conj g
  have hTT := Q3T8.Asc77.Thompson.isTT_muDelta (hΩ : Q3T8.Asc77.HypOmegaMod Ω) hW
      (Q3CL.thompsonCube hP W hW)
  obtain ⟨r, hr, hrW⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩ hW hRD
  obtain ⟨r', hr', hr'W⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩ hW hR'D
  obtain ⟨t', ht', ht'W⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩ hW hR₃D
  obtain ⟨a, ha, haeq⟩ := exists_muDelta_eq_piG hRD hr hrW
  obtain ⟨b, hb, hbeq⟩ := exists_muDelta_eq_piG hR'D hr' hr'W
  obtain ⟨c, hc, hceq⟩ := exists_muDelta_eq_piG hR₃D ht' ht'W
  have hKK' : conjSub g K ≠ conjSub g K' := fun e => h.hne.symm ((conjSub_inj g).mp e)
  have hKK₃ : conjSub g K ≠ conjSub g K₃ := fun e => h.hK₃K ((conjSub_inj g).mp e).symm
  have hK'K₃ : conjSub g K' ≠ conjSub g K₃ := fun e => h.hK₃K' ((conjSub_inj g).mp e).symm
  have hab : a ≠ b := fun e =>
    Q3T8.Asc77.piG_ne_of_ne_members hΩ hW hRD hR'D hKg hK'g hRsylg hR'sylg hKK' hr hr' hr'W
      (haeq.symm.trans ((congrArg Subtype.val e).trans hbeq))
  have hac : a ≠ c := fun e =>
    Q3T8.Asc77.piG_ne_of_ne_members hΩ hW hRD hR₃D hKg hK₃g hRsylg hR₃sylg hKK₃ hr ht' ht'W
      (haeq.symm.trans ((congrArg Subtype.val e).trans hceq))
  have hbc : b ≠ c := fun e =>
    Q3T8.Asc77.piG_ne_of_ne_members hΩ hW hR'D hR₃D hK'g hK₃g hR'sylg hR₃sylg hK'K₃ hr' ht' ht'W
      (hbeq.symm.trans ((congrArg Subtype.val e).trans hceq))
  have hab' : a * b = b * a :=
    muGroup_comm_of_comm hRD hR'D hr hr' ((hRR'.conjSub g) r hr r' hr') haeq hbeq
  have hac' : a * c = c * a :=
    muGroup_comm_of_comm hRD hR₃D hr ht' ((hRR₃.conjSub g) r hr t' ht') haeq hceq
  have hbc' : b * c = c * b :=
    muGroup_comm_of_comm hR'D hR₃D hr' ht' ((hR'R₃.conjSub g) r' hr' t' ht') hbeq hceq
  constructor
  · rintro ⟨e⟩
    have hTT3 := T7A.isTT_map_equiv hTT e
    exact T7A.no_two_commuting_perm3 hTT3 _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      (fun e2 => hab (e.injective e2)) (by rw [← map_mul, ← map_mul, hab'])
  · rintro ⟨e⟩
    have hTT4 := T7A.isTT_map_equiv hTT e
    exact T7A.no_three_commuting_perm4 hTT4 _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
      (fun e2 => hab (e.injective e2)) (fun e2 => hac (e.injective e2))
      (fun e2 => hbc (e.injective e2))
      (by rw [← map_mul, ← map_mul, hab']) (by rw [← map_mul, ← map_mul, hac'])
      (by rw [← map_mul, ← map_mul, hbc'])
end Hyp22Setting
namespace T7S22
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.T7S22
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem perp_of_twin
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) {L : Subgroup G}
    (hL : L ∈ twinSet Ω K) : KPerp Ω L = twinSet Ω L := by
  have h1 := (CFSG.ClassicalInvolution.Q3.Q3T7M.l6_3 G Ω h.stand.modU K h.stand.mem L hL).1
  rw [← h1, twinSet_eq_of_mem_twinSet h.hz hL]
  exact h.perp

theorem dComp_subset_twinSet
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) :
    dComp Ω K ⊆ twinSet Ω K := by
  have hΩ : Q3T7M.HM Ω := h.stand.modU
  intro J hJ
  have hJ' : Relation.ReflTransGen (fun M N : Subgroup G => N ∈ Ω ∧ Disconnected.dAdj Ω M N) K J :=
    hJ
  clear hJ
  induction hJ' with
  | refl => exact mem_twinSet_self h.stand.mem h.hz
  | @tail M N _ hstep ih =>
    obtain ⟨hNΩ, hadj⟩ := hstep
    have hMΩ : M ∈ Ω := ih.1
    have hpM := Q3T8.Asc77.T7S22.perp_of_twin h ih
    have htM : twinSet Ω M = twinSet Ω K := twinSet_eq_of_mem_twinSet h.hz ih
    have key : N ∈ omegaNbr Ω M → N ∈ twinSet Ω K := fun hN => by
      have hN' : N ∈ KPerp Ω M := Set.mem_insert_of_mem _ hN
      rwa [hpM, htM] at hN'
    rcases hadj with hN | hM
    · exact key hN
    · exact key (Q3CL.T3.omegaNbr_symm (Q3T8.Asc77.l6_2) hΩ hNΩ hMΩ hM)
end T7S22

end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
namespace S22
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.S22
set_option linter.unusedSectionVars false
open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
section Setting
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem Big.of_four
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) {K₄ : Subgroup G}
    (hK₄ : K₄ ∈ twinSet Ω K) (h1 : K₄ ≠ K) (h2 : K₄ ≠ K') (h3 : K₄ ≠ K₃) : Q3T8.Asc77.S22.Big Ω K :=
  ⟨K, K', K₃, K₄, mem_twinSet_self h.stand.mem h.hz, h.hK', h.hK₃, hK₄, h.hne.symm,
    h.hK₃K.symm, h1.symm, h.hK₃K'.symm, h2.symm, h3.symm⟩

theorem hyp22Setting_of_sylows
    {K K' K₃ : Subgroup G} {z : G} (hst : Q3T8.Asc77.AscStand Ω K)
    (hz : IsUniqueInvolution K z) (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K)
    (hperp : KPerp Ω K = twinSet Ω K) (hK₃ : K₃ ∈ twinSet Ω K) (hK₃K : K₃ ≠ K)
    (hK₃K' : K₃ ≠ K') {R R' R₃ : Subgroup G} (hR : IsSylow2In R K) (hR' : IsSylow2In R' K')
    (hR₃ : IsSylow2In R₃ K₃) (c₁₂ : Commutes R R') (c₁₃ : Commutes R R₃)
    (c₂₃ : Commutes R' R₃) {u₁ u₂ u₃ : G} (h₁ : u₁ ∈ R) (h₂ : u₂ ∈ R') (h₃ : u₃ ∈ R₃)
    (o₁ : orderOf u₁ = 4) (o₂ : orderOf u₂ = 4) (o₃ : orderOf u₃ = 4) :
    Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃ := by
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hK'
  have hzK₃ : IsUniqueInvolution K₃ z := isUniqueInvolution_of_mem_twinSet hz hK₃
  have hB := Q3T8.Asc77.T7B.isElemAbelian2_B hst.hyp hst.mem hK'.1 hK₃.1 hne hK₃K hK₃K' hz hzK' hzK₃
    (hR.1 h₁) (hR'.1 h₂) (hR₃.1 h₃) o₁ o₂ o₃ (c₁₂ u₁ h₁ u₂ h₂) (c₁₃ u₁ h₁ u₃ h₃)
    (c₂₃ u₂ h₂ u₃ h₃)
  exact
    { stand := hst
      hz := hz
      hK' := hK'
      hne := hne
      perp := hperp
      hK₃ := hK₃
      hK₃K := hK₃K
      hK₃K' := hK₃K'
      hu₁ := ⟨hR.1 h₁, o₁⟩
      hu₂ := ⟨hR'.1 h₂, o₂⟩
      hu₃ := ⟨hR₃.1 h₃, o₃⟩
      hB := hB }

theorem closure_rotate
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) :
    Subgroup.closure ({u₂ * u₃, z, u₃ * u₁} : Set G) =
      Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    · exact T7B.mem_closure_thd
    · exact T7B.mem_closure_snd
    · rw [← Q3T8.Asc77.T7J.comm₁₃ h]
      exact h.mem_B_13
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    · have e : u₁ * u₂ = z * ((u₂ * u₃) * (u₃ * u₁)) := by
        calc u₁ * u₂ = (z * z) * (u₁ * u₂) := by rw [h.hz.sq, one_mul]
          _ = z * (z * u₁ * u₂) := by group
          _ = z * (u₁ * z * u₂) := by rw [h.comm_z₁]
          _ = z * (u₂ * z * u₁) := by
              rw [show u₁ * z * u₂ = u₁ * (z * u₂) by group, h.comm_z₂,
                show u₂ * z * u₁ = u₂ * (z * u₁) by group, h.comm_z₁,
                show u₁ * (u₂ * z) = (u₁ * u₂) * z by group,
                show u₂ * (u₁ * z) = (u₂ * u₁) * z by group, h.comm₁₂]
          _ = z * ((u₂ * u₃) * (u₃ * u₁)) := by
              rw [show (u₂ * u₃) * (u₃ * u₁) = u₂ * (u₃ * u₃) * u₁ by group, h.sq₃]
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp)))
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)

theorem rotate
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) :
    Q3T8.Asc77.Hyp22Setting Ω K' K₃ K z u₂ u₃ u₁ := by
  have hΩ : Q3T7M.HM Ω := h.stand.modU
  have hK : K ∈ Ω := h.stand.mem
  have hKK' : K ∈ twinSet Ω K' := by
    rw [twinSet_eq_of_mem_twinSet h.hz h.hK']
    exact mem_twinSet_self hK h.hz
  have hperp : KPerp Ω K' = KPerp Ω K := ((CFSG.ClassicalInvolution.Q3.Q3T7M.l6_3 G Ω hΩ K hK K'
      h.hK').1).symm
  have htw : twinSet Ω K' = twinSet Ω K := twinSet_eq_of_mem_twinSet h.hz h.hK'
  refine
    { stand := h.stand.of_mem h.hK'.1
      hz := h.hzK'
      hK' := by rw [htw]; exact h.hK₃
      hne := h.hK₃K'
      perp := by rw [hperp, htw]; exact h.perp
      hK₃ := hKK'
      hK₃K := h.hne.symm
      hK₃K' := h.hK₃K.symm
      hu₁ := h.hu₂
      hu₂ := h.hu₃
      hu₃ := h.hu₁
      hB := ?_ }
  rw [Q3T8.Asc77.S22.closure_rotate h]
  exact h.hB

theorem isElemAbelian2_closure
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) :
    IsElemAbelian2 (Subgroup.closure ({u₁ * u₂, z} : Set G)) 2 := by
  have hne : u₁ * u₂ ≠ z := by
    intro he
    have hK' : K' ∈ Ω := h.hK'.1
    have hK : K ∈ Ω := h.stand.mem
    refine Q3T8.Asc77.T7A.not_mem_inf_of_orderOf_four h.stand.modU hK hK' h.hne h.hu₂.2 ?_ h.hu₂.1
    have : u₂ = u₁⁻¹ * z := by rw [← he]; group
    rw [this]
    exact K.mul_mem (K.inv_mem h.hu₁.1) h.hz.mem
  have h1 : u₁ * u₂ ≠ 1 := by
    intro he
    have hK' : K' ∈ Ω := h.hK'.1
    have hK : K ∈ Ω := h.stand.mem
    refine Q3T8.Asc77.T7A.not_mem_inf_of_orderOf_four h.stand.modU hK hK' h.hne h.hu₂.2 ?_ h.hu₂.1
    have : u₂ = u₁⁻¹ := eq_inv_of_mul_eq_one_right he
    rw [this]
    exact K.inv_mem h.hu₁.1
  have hcomm : (u₁ * u₂) * z = z * (u₁ * u₂) := by
    calc (u₁ * u₂) * z = u₁ * (u₂ * z) := by group
      _ = u₁ * (z * u₂) := by rw [h.comm_z₂]
      _ = (u₁ * z) * u₂ := by group
      _ = (z * u₁) * u₂ := by rw [h.comm_z₁]
      _ = z * (u₁ * u₂) := by group
  exact T7A.isElemAbelian2_closure_pair h.sq_12 h.hz.sq h1 h.hz.ne_one hne hcomm
end Setting
end S22
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
    CFSG.ClassicalInvolution.Disconnected

theorem twinFrame_tag_of_model
    (hTSF :
    Q3T8.Asc77.TwinSquareFact3) {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)} (hΦ :
    Q3T7M.HM Φ)
    {tg : StatedLieTag} {k ee : ℕ} (M : Q3T8.Asc77.Ih8Model Φ tg k ee) (hdisc : ¬ DConnected Φ)
    {A A' B : Subgroup X} {z u₁ u₂ τ ε : X} (h : TwinFrame Φ A A' B z u₁ u₂ τ ε) :
    (tg = .PSL ∧ k = 4 ∧ 3 % 4 = 1) ∨ (tg = .PSU ∧ k = 4 ∧ 3 % 4 = 3) := by
  classical
  obtain ⟨hA, hA', hB, hne, hzA, hzA', h₁, h₂, o₁, o₂, htB, he, he2, he1, hrel⟩ := h
  by_cases hG2d4 : tg = .G2 ∨ tg = .trialityD4
  · exfalso
    have hsimple : IsSimpleGroup X := M.isSimpleGroup_of_g2d4 (by norm_num) hG2d4
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with hc | hc
    · apply he1
      have := hc ▸ he
      simpa using this
    · obtain ⟨zz, hzz⟩ := hΦ.classical A hA
      obtain ⟨x, hx, y, hy, hxy⟩ := Q3T8.Asc77.ih8_exists_noncomm hzz
      have hy' : y ∈ Subgroup.center X := hc ▸ Subgroup.mem_top y
      exact hxy (Subgroup.mem_center_iff.mp hy' x)
  push Not at hG2d4
  obtain ⟨hG2, hD4⟩ := hG2d4
  have hee : ee = 1 := M.exp_eq_f hD4
  rcases Uniform.tag_casesU (by norm_num) M.isFundTag M.admissible hG2 hD4 with hconn | hsmall
  · exact absurd (Uniform.dConnected_of_connectedU M hΦ ⟨A, hA⟩ hG2 hD4 hconn) hdisc
  obtain ⟨RA, hRA, rfl⟩ := (M.mem_iff A).mp hA
  obtain ⟨RA', hRA', rfl⟩ := (M.mem_iff A').mp hA'
  obtain ⟨RB, hRB, rfl⟩ := (M.mem_iff B).mp hB
  have hpA := M.gen3 hG2 hD4 hRA
  have hpA' := M.gen3 hG2 hD4 hRA'
  have hpB := M.gen3 hG2 hD4 hRB
  have hRR : RA ≠ RA' := fun h => hne (by rw [h])
  have hexM := M.exactMembers3 hΦ hG2 hD4
  obtain ⟨hcommR, -⟩ := Uniform.ih8_twin_data3 hΦ hexM M.ker_le_center (M.ker_pow_three hD4) hpA
      (M.map_mem hRA)
    (M.map_mem hRA') hne hzA hzA'
  have hnpsl : ¬ (tg = .PSL ∧ k = 2) := by
    rintro ⟨rfl, rfl⟩
    have hfin := M.finite_K (by norm_num)
    have htopR : ∀ R ∈ M.cls, R = ⊤ := by
      intro R hR
      obtain ⟨eR⟩ := M.cls_equiv_sl2 (by norm_num) (by decide) (by decide) hR
      have hcard : Nat.card ↥R = Nat.card (modelUniv .PSL 2 3 ee Fact.out).K := by
        rw [Nat.card_congr eR.toEquiv]
        exact Nat.card_congr (Equiv.refl _)
      exact Subgroup.eq_top_of_card_eq R hcard
    exact hne (by rw [htopR RA hRA, htopR RA' hRA'])
  have hmain : ((tg = .PSp ∧ k = 2) ∨ (tg = .PSL ∧ k = 4) ∨ (tg = .PSU ∧ k = 4) ∨
      (tg = .POmegaOdd ∧ k = 3) ∨ (tg = .POmegaPlus ∧ k = 4) ∨ (tg = .POmegaMinus ∧ k = 4)) →
      (tg = .PSL ∧ k = 4 ∧ 3 % 4 = 1) ∨ (tg = .PSU ∧ k = 4 ∧ 3 % 4 = 3) := by
    intro hsix
    obtain ⟨eA⟩ := M.cls_equiv_sl2 (by norm_num) hG2 hD4 hRA
    obtain ⟨eA'⟩ := M.cls_equiv_sl2 (by norm_num) hG2 hD4 hRA'
    obtain ⟨eB⟩ := M.cls_equiv_sl2 (by norm_num) hG2 hD4 hRB
    have hodd := M.natCard_galoisField_odd (by norm_num)
    have hinjA := M.injOn_fund hnpsl (M.cls_sub hRA)
    have hinjA' := M.injOn_fund hnpsl (M.cls_sub hRA')
    have hinjB := M.injOn_fund hnpsl (M.cls_sub hRB)
    have hxR : sl2Inv eA ∈ RA := sl2Inv_mem eA
    have hx'R : sl2Inv eA' ∈ RA' := sl2Inv_mem eA'
    have hx2 : sl2Inv eA * sl2Inv eA = 1 := sl2Inv_mul_self hodd eA
    have hx'2 : sl2Inv eA' * sl2Inv eA' = 1 := sl2Inv_mul_self hodd eA'
    have hx1 : sl2Inv eA ≠ 1 := sl2Inv_ne_one hodd eA
    have hx'1 : sl2Inv eA' ≠ 1 := sl2Inv_ne_one hodd eA'
    
    have hψx : M.ψ (sl2Inv eA) = z := by
      have hmem : M.ψ (sl2Inv eA) ∈ RA.map M.ψ := Subgroup.mem_map_of_mem _ hxR
      have hsq : M.ψ (sl2Inv eA) * M.ψ (sl2Inv eA) = 1 := by rw [← map_mul, hx2, map_one]
      rcases hzA.unique _ hmem hsq with h | h
      · exact absurd (hinjA _ hxR h) hx1
      · exact h
    have hψx' : M.ψ (sl2Inv eA') = z := by
      have hmem : M.ψ (sl2Inv eA') ∈ RA'.map M.ψ := Subgroup.mem_map_of_mem _ hx'R
      have hsq : M.ψ (sl2Inv eA') * M.ψ (sl2Inv eA') = 1 := by rw [← map_mul, hx'2, map_one]
      rcases hzA'.unique _ hmem hsq with h | h
      · exact absurd (hinjA' _ hx'R h) hx'1
      · exact h
    
    obtain ⟨a₁, ha₁, hψa₁⟩ := Subgroup.mem_map.mp h₁
    obtain ⟨a₂, ha₂, hψa₂⟩ := Subgroup.mem_map.mp h₂
    obtain ⟨b, hb, hψb⟩ := Subgroup.mem_map.mp htB.mem
    obtain ⟨c₀, hψc₀⟩ := M.surj ε
    have ha₁sq : a₁ * a₁ = sl2Inv eA := by
      have : a₁ * a₁ * (sl2Inv eA)⁻¹ = 1 := by
        apply hinjA _ (RA.mul_mem (RA.mul_mem ha₁ ha₁) (RA.inv_mem hxR))
        rw [map_mul, map_mul, map_inv, hψa₁, hψx, o₁, mul_inv_cancel]
      exact mul_inv_eq_one.mp this
    have ha₂sq : a₂ * a₂ = sl2Inv eA' := by
      have : a₂ * a₂ * (sl2Inv eA')⁻¹ = 1 := by
        apply hinjA' _ (RA'.mul_mem (RA'.mul_mem ha₂ ha₂) (RA'.inv_mem hx'R))
        rw [map_mul, map_mul, map_inv, hψa₂, hψx', o₂, mul_inv_cancel]
      exact mul_inv_eq_one.mp this
    have hbsq : b * b = 1 := by
      apply hinjB _ (RB.mul_mem hb hb)
      rw [map_mul, hψb, htB.sq]
    
    have hQS := ModelFacts.modelClauseZero tg k 3 ee Fact.out M.isFundTag M.admissible
    have hNnorm : (Subgroup.zpowers ε).Normal := ⟨fun n hn g => by
      obtain ⟨m, rfl⟩ := hn
      have hc : Commute g ε := Subgroup.mem_center_iff.mp he g
      have := (hc.zpow_right m).eq
      rw [this, mul_inv_cancel_right]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers ε) m⟩
    have hc₀ : c₀ ∈ Subgroup.center (modelUniv tg k 3 ee Fact.out).K :=
      comap_le_center_of_normal_pGroup hQS.1 M.ψ M.ker_le_center
        (Q3T8.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one he2)
        (show M.ψ c₀ ∈ Subgroup.zpowers ε from hψc₀ ▸ Subgroup.mem_zpowers ε)
    
    obtain ⟨κ, hκc, hκeq⟩ : ∃ κ ∈ Subgroup.center (modelUniv tg k 3 ee Fact.out).K,
        a₁ * a₂ * c₀ = b * κ := by
      refine ⟨b⁻¹ * (a₁ * a₂ * c₀), M.ker_le_center ?_, by group⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hψb, map_mul, map_mul, hψa₁, hψa₂, hψc₀, ← hrel,
        inv_mul_cancel]
    have hc12 : a₁ * a₂ = a₂ * a₁ := hcommR a₁ ha₁ a₂ ha₂
    have hcc : ∀ y, y * c₀ = c₀ * y := Subgroup.mem_center_iff.mp hc₀
    have hκκ : ∀ y, y * κ = κ * y := Subgroup.mem_center_iff.mp hκc
    have e1 : a₁ * a₂ * (a₁ * a₂) = (a₁ * a₁) * (a₂ * a₂) := by
      calc a₁ * a₂ * (a₁ * a₂) = a₁ * (a₂ * a₁) * a₂ := by group
        _ = a₁ * (a₁ * a₂) * a₂ := by rw [← hc12]
        _ = (a₁ * a₁) * (a₂ * a₂) := by group
    have e2 : (a₁ * a₂ * c₀) * (a₁ * a₂ * c₀) = (a₁ * a₁) * (a₂ * a₂) * (c₀ * c₀) := by
      calc (a₁ * a₂ * c₀) * (a₁ * a₂ * c₀) = a₁ * a₂ * (c₀ * (a₁ * a₂)) * c₀ := by group
        _ = a₁ * a₂ * ((a₁ * a₂) * c₀) * c₀ := by rw [← hcc (a₁ * a₂)]
        _ = (a₁ * a₂ * (a₁ * a₂)) * (c₀ * c₀) := by group
        _ = (a₁ * a₁) * (a₂ * a₂) * (c₀ * c₀) := by rw [e1]
    have e3 : (b * κ) * (b * κ) = κ * κ := by
      calc (b * κ) * (b * κ) = b * (κ * b) * κ := by group
        _ = b * (b * κ) * κ := by rw [← hκκ b]
        _ = (b * b) * (κ * κ) := by group
        _ = κ * κ := by rw [hbsq, one_mul]
    have e4 : sl2Inv eA * sl2Inv eA' * (c₀ * c₀) = κ * κ := by
      rw [← ha₁sq, ← ha₂sq, ← e2, hκeq, e3]
    have hc₀inv : c₀⁻¹ ∈ Subgroup.center (modelUniv tg k 3 ee Fact.out).K :=
      Subgroup.inv_mem _ hc₀
    have hswap : κ * c₀⁻¹ = c₀⁻¹ * κ := Subgroup.mem_center_iff.mp hc₀inv κ
    have hζ : κ * c₀⁻¹ ∈ Subgroup.center (modelUniv tg k 3 ee Fact.out).K :=
      Subgroup.mul_mem _ hκc hc₀inv
    have e5 : (κ * c₀⁻¹) * (κ * c₀⁻¹) = sl2Inv eA * sl2Inv eA' := by
      calc (κ * c₀⁻¹) * (κ * c₀⁻¹) = κ * (c₀⁻¹ * κ) * c₀⁻¹ := by group
        _ = κ * (κ * c₀⁻¹) * c₀⁻¹ := by rw [← hswap]
        _ = (κ * κ) * (c₀⁻¹ * c₀⁻¹) := by group
        _ = (sl2Inv eA * sl2Inv eA' * (c₀ * c₀)) * (c₀⁻¹ * c₀⁻¹) := by rw [e4]
        _ = sl2Inv eA * sl2Inv eA' := by group
    have hxx' : sl2Inv eA * sl2Inv eA' ∈ Subgroup.center (modelUniv tg k 3 ee Fact.out).K := by
      rw [← e5]; exact Subgroup.mul_mem _ hζ hζ
    have := hTSF tg k ee hee M.admissible hsix RA (M.cls_sub hRA) RA' (M.cls_sub hRA') hRR
      hcommR _ hxR _ hx'R hx2 hx1 hx'2 hx'1 hxx' ⟨_, hζ, e5⟩
    exact Or.inr ⟨this.1, this.2, by norm_num⟩
  rcases hsmall with ⟨rfl, hk⟩ | ⟨rfl, hk⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hk2 : 2 ≤ k := M.admissible.2.2.1
    have hk' : k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases hk' with rfl | rfl | rfl
    · exact absurd ⟨rfl, rfl⟩ hnpsl
    · exfalso
      have := four_le_of_commutes_psl (by norm_num) (le_refl 3) (M.cls_sub hRA) (M.cls_sub hRA')
          hRR hcommR
      omega
    · exact hmain (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · have hk3 : 3 ≤ k := M.admissible.2.2.1
    have hk' : k = 3 ∨ k = 4 := by omega
    rcases hk' with rfl | rfl
    · exfalso
      have := four_le_of_commutes_psu (by norm_num) M.admissible (M.cls_sub hRA) (M.cls_sub hRA')
          hRR hcommR
      omega
    · exact hmain (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  · exact hmain (Or.inl ⟨rfl, rfl⟩)
  · exact hmain (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
  · exact hmain (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))
  · exact hmain (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))))
section Wrapper
variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem twinFrame_tag
    (hTSF : Q3T8.Asc77.TwinSquareFact3) (hΦ : Q3T7M.HM Φ) (D :
    Q3T8.Asc77.OmegaLie Φ) (hcard : D.card = 1) (hgen : omegaGen Φ = ⊤)
    (hdisc : ¬ DConnected Φ) {A A' B : Subgroup X} {z u₁ u₂ t e : X}
    (h : TwinFrame Φ A A' B z u₁ u₂ t e) (i : Fin D.card) :
    (D.tag i = .PSL ∧ D.rank i = 4 ∧ 3 % 4 = 1) ∨
      (D.tag i = .PSU ∧ D.rank i = 4 ∧ 3 % 4 = 3) :=
  Q3T8.Asc77.twinFrame_tag_of_model hTSF hΦ
    { isFundTag := D.isFundTag i
      admissible := D.admissible i
      exp_eq := D.exp_eq i
      ψ := D.hom i
      ker_le_center := D.ker_le_center i
      surj := D.hom_surjective_of_gen hcard hgen i
      cls := D.cls i
      cls_sub := fun _ hR => hR.1
      mem_iff := fun _ => D.mem_iff_exists_cls hcard i
      cls_conj := fun _ hR g => D.cls_conj hΦ.conjInvariant i hR g } hdisc h
end Wrapper
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
