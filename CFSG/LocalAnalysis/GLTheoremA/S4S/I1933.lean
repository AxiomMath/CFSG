module

public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs
import CFSG.HardMathSupport.Solomon.Coordinator.I19_1Main
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.HardMathSupport.Solomon.LocalBalance.Defs
public import CFSG.LocalAnalysis.GLTheoremB.ComponentTools
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem commutator_le_self_1933 {T B : Subgroup G}
    (h : B ≤ Subgroup.normalizer (T : Set G)) : (⁅T, B⁆ : Subgroup G) ≤ T := by
  refine Subgroup.commutator_le.2 fun t ht β hβ => ?_
  have h1 : β * t⁻¹ * β⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 (h hβ) t⁻¹).1 (T.inv_mem ht)
  have h2 : ⁅t, β⁆ = t * (β * t⁻¹ * β⁻¹) := by simp [commutatorElement_def, mul_assoc]
  rw [h2]
  exact T.mul_mem ht h1

private theorem barX_oPPrimeP_1933 (p : ℕ) (X : Subgroup G) :
    barX p X (oPPrimeP p X) = CFSG.pCore p (↥X ⧸ GLAPPrimeCore p ↥X) := by
  have hJg : (oPPrimeP p X).subgroupOf X =
      (CFSG.pCore p (↥X ⧸ GLAPPrimeCore p ↥X)).comap (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) :=
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
  show ((oPPrimeP p X).subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) = _
  rw [hJg]
  exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _

private theorem barX_le_centralizer_1933 {p : ℕ} {X S T : Subgroup G}
    (h : ∀ t ∈ T, ∀ s ∈ S, ⁅t, s⁆ ∈ GLAPPrimeCoreOf p X) :
    barX p X S ≤ Subgroup.centralizer (barX p X T : Set (↥X ⧸ GLAPPrimeCore p ↥X)) := by
  refine barX_le_centralizer fun s hs t ht _ _ => ?_
  have h3 := Subgroup.inv_mem _ (h t ht s hs)
  rwa [commutatorElement_inv] at h3

private theorem eq_bot_of_le_fitting_1933 {Q : Type} [Group Q] [Finite Q]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hcore : CFSG.pPrimeCore p Q = ⊥)
    {T : Subgroup Q} (hT : IsPGroup 2 T)
    (hc : T ≤ Subgroup.centralizer (CFSG.generalizedFitting Q : Set Q)) : T = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h1 : T ≤ CFSG.fittingSubgroup Q := by
    have h := CFSG.ComponentClassification.GeneralizedFitting.centralizer_le_fitting Q
    rw [← CFSG.generalizedFitting_eq_componentClassification] at h
    exact hc.trans h
  have hpT : IsPGroup p T :=
    (CFSG.pCore_isPGroup (p := p) (G := Q)).to_le (h1.trans (CFSG.Fitting_eq_pcore Q p hcore).le)
  exact disjoint_self.1 (IsPGroup.disjoint_of_ne 2 p hp2.symm T T hT hpT)

private theorem le_glaPPrimeCoreOf_of_component_commutators_1933 {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {X S : Subgroup G} (hS2 : IsPGroup 2 S) (hSX : S ≤ X)
    (hQ : (⁅oPPrimeP p X, S⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p X)
    (hJ : ∀ J : Subgroup G, GLAPComponent p X J → (⁅J, S⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p X) :
    S ≤ GLAPPrimeCoreOf p X := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcore : CFSG.pPrimeCore p (↥X ⧸ GLAPPrimeCore p ↥X) = ⊥ :=
    CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot p
  have hS2' : IsPGroup 2 (barX p X S) :=
    (hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSX).symm).map _
  have hF : CFSG.generalizedFitting (↥X ⧸ GLAPPrimeCore p ↥X) ≤
      Subgroup.centralizer (barX p X S : Set (↥X ⧸ GLAPPrimeCore p ↥X)) := by
    rw [CFSG.generalizedFitting.eq_sup]
    refine sup_le ?_ ?_
    · rw [CFSG.Fitting_eq_pcore _ p hcore, Subgroup.le_centralizer_iff, ← barX_oPPrimeP_1933 p X]
      exact barX_le_centralizer_1933 fun t ht s hs => Subgroup.commutator_le.1 hQ t ht s hs
    · refine sSup_le fun K hK => ?_
      obtain ⟨L, hL, rfl⟩ := exists_glaPComponent_barX_eq X ((CFSG.isComponent_iff_open K).1 hK)
      rw [Subgroup.le_centralizer_iff]
      exact barX_le_centralizer_1933 fun l hl s hs => Subgroup.commutator_le.1 (hJ L hL) l hl s hs
  have hbot : barX p X S = ⊥ :=
    eq_bot_of_le_fitting_1933 hp hp2 hcore hS2' (Subgroup.le_centralizer_iff.2 hF)
  intro s hs
  have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨s, hSX hs⟩ ∈ barX p X S :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hs)
  rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact ⟨⟨s, hSX hs⟩, h1, rfl⟩

private theorem commutator_component_le_core_1933 {p k : ℕ} (hp : p.Prime) {B D T X J : Subgroup G}
    (hX : InDelta p X D T) (hJ : GLAPComponent p X J)
    (hBN : B ≤ Subgroup.normalizer (J : Set G))
    (hbal : IsCompTwoPrimaryWeaklyLocallyBalanced p k B J)
    (hDB : D ≤ B) (hcard : Nat.card D = p ^ k)
    (hT2 : IsPGroup 2 T) (hBT : B ≤ Subgroup.normalizer (T : Set G)) :
    (⁅J, (⁅T, B⁆ : Subgroup G)⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p X := by
  by_cases hn : (⁅J, T⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p X
  · exact (Subgroup.commutator_mono le_rfl (commutator_le_self_1933 hBT)).trans hn
  obtain ⟨hTN, hDN, hker, -, hle⟩ := hX.conclusions_nocard h1Stmt_zero hp hJ hn
  have hA : autBar p B J =
      (B.subgroupOf (Subgroup.normalizer (J : Set G))).map (barAut p J) := by
    unfold autBar
    rw [inf_eq_left.2 hBN]
  have hE : IsEkIn p k (autBar p B J)
      ((D.subgroupOf (Subgroup.normalizer (J : Set G))).map (barAut p J)) := by
    refine ⟨?_, isElemAbelian_map (isElemAbelian_subgroupOf hX.elem) _,
      (card_map_barAut hDN hker).trans hcard⟩
    rw [hA]
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, (Subgroup.mem_subgroupOf).2 (hDB ((Subgroup.mem_subgroupOf).1 hx)), rfl⟩
  have hnorm := map_subgroupOf_le_normalizer_map (p := p) (S := T) hBT hBN
  have hodd := hbal _ hE _ innerAut_le_map (hA ▸ hnorm)
  have hWK : (⁅T, B⁆ : Subgroup G) ≤ centralizerQuot J (GLAPPrimeCoreOf p J) := by
    refine Subgroup.commutator_le.2 fun t ht β hβ => ?_
    have htN := hTN ht
    have hβN := hBN hβ
    have hcN : ⁅t, β⁆ ∈ Subgroup.normalizer (J : Set G) := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem htN hβN) (inv_mem htN)) (inv_mem hβN)
    refine (mem_centralizerQuot_iff_barAut_eq_one p ⟨⁅t, β⁆, hcN⟩).2 ?_
    have e : (⟨⁅t, β⁆, hcN⟩ : ↥(Subgroup.normalizer (J : Set G))) =
        ⁅(⟨t, htN⟩ : ↥(Subgroup.normalizer (J : Set G))), ⟨β, hβN⟩⁆ := rfl
    have hg := Subgroup.commutator_mem_commutator
      (hle ⟨⟨t, htN⟩, (Subgroup.mem_subgroupOf).2 ht, rfl⟩)
      (show barAut p J ⟨β, hβN⟩ ∈ autBar p B J from
        ⟨⟨β, hβN⟩, (Subgroup.mem_subgroupOf).2 ⟨hβ, hβN⟩, rfl⟩)
    rw [← map_commutatorElement, ← e] at hg
    have htβ : ⁅t, β⁆ ∈ T :=
      commutator_le_self_1933 hBT (Subgroup.commutator_mem_commutator ht hβ)
    obtain ⟨m, hm⟩ := hT2 ⟨⁅t, β⁆, htβ⟩
    have hpow : (barAut p J ⟨⁅t, β⁆, hcN⟩) ^ (2 ^ m) = 1 := by
      rw [← map_pow]
      have h1 : (⟨⁅t, β⁆, hcN⟩ : ↥(Subgroup.normalizer (J : Set G))) ^ (2 ^ m) = 1 :=
        Subtype.ext (by simpa using congrArg Subtype.val hm)
      rw [h1, map_one]
    have h1 : orderOf (barAut p J ⟨⁅t, β⁆, hcN⟩) ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hpow
    have h2 := Subgroup.orderOf_dvd_natCard _ hg
    have hcop := Nat.Coprime.pow_left m (Nat.coprime_two_left.2 hodd)
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd h1 h2))
  refine Subgroup.commutator_le.2 fun x hx w hw => ?_
  obtain ⟨-, -, hc⟩ := hWK hw
  exact CFSG.LocalAnalysis.GLTheoremB.glaPPrimeCoreOf_le_of_isSubnormal hp hJ.2.1 (hc x hx)

theorem i1933At_holds (G : Type) [Group G] [Finite G] (p : ℕ) : I1933At G p := by
  intro hp hp2 _ _ _ B D k b hB hk hD hbB hb1 hJ T hT2 hBT hTΔ
  have hBb : ∀ g ∈ B, g * b = b * g := fun g hg => elemAbelian_commute hB hg hbB
  have hBX : B ≤ Subgroup.centralizer ({b} : Set G) := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.2 (hBb g hg)
  have hDX : D ≤ Subgroup.centralizer ({b} : Set G) := hD.1.trans hBX
  have hTX : T ≤ Subgroup.centralizer ({b} : Set G) := hTΔ.trans inf_le_right
  have hin : InDelta p (Subgroup.centralizer ({b} : Set G)) D T :=
    InDelta.of_le_gLADelta hp hDX hD.2.1 (ne_bot_of_card hp hk hD.2.2) hTX (hTΔ.trans inf_le_left)
  have hST : (⁅T, B⁆ : Subgroup G) ≤ T := commutator_le_self_1933 hBT
  have hQ : (⁅oPPrimeP p (Subgroup.centralizer ({b} : Set G)), (⁅T, B⁆ : Subgroup G)⁆ :
      Subgroup G) ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({b} : Set G)) :=
    (Subgroup.commutator_mono le_rfl hST).trans (hin.commutator_oPrimePOf_le h1Stmt_zero hp)
  exact le_glaPPrimeCoreOf_of_component_commutators_1933 hp hp2 (hT2.to_le hST) (hST.trans hTX) hQ
    fun J hJc => commutator_component_le_core_1933 hp hin hJc (hJ J hJc).1 (hJ J hJc).2 hD.1
      hD.2.2 hT2 hBT

end CFSG.LocalAnalysis.GLTheoremA
