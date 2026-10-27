module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenI112
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Layer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.LocalAnalysis.GLTheoremB.CentralizerLift
public import CFSG.Quasithin.Background.F918V5GComp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Timmesfeld.ComponentBalance (LComm lbp lphi lphi_apply gLBConj_lbp_ne
  mem_of_zpow_mem)

variable {Ω : Type} [Group Ω] [Finite Ω]

private theorem centModSubgroup_eq_of_genHyp {Q : TauCeti.LieTypeIndex → Prop} {p q : ℕ}
    {S B : Subgroup Ω} (H : GenHyp Q p q S B) :
    centModSubgroup p S = Subgroup.centralizer (S : Set Ω) := by
  ext x
  refine ⟨fun hx => Subgroup.mem_centralizer_iff.2 fun s hs => ?_,
    fun hx => centMod_iff.1 (CFSG.LocalAnalysis.GLTheoremA.centMod_of_mem_centralizer hx)⟩
  have h := (mem_centModSubgroup.1 hx).2 s hs
  have hbot : GLAPPrimeCoreOf p S = ⊥ := by
    unfold GLAPPrimeCoreOf
    rw [H.core, Subgroup.map_bot]
  rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
  exact h

private theorem isElemAbelian_zpowers {ε : Ω} (hε3 : ε ^ 3 = 1) :
    IsElemAbelian 3 (Subgroup.zpowers ε) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
  · rcases a with ⟨_, i, rfl⟩
    rcases b with ⟨_, j, rfl⟩
    exact Subtype.ext (Commute.zpow_zpow_self ε i j).eq
  · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hε3, one_zpow]

private theorem sup_zpowers_of_not_mem {H M : Subgroup Ω} {ε : Ω}
    (hcomm : ∀ h ∈ H, h * ε = ε * h) (hε3 : ε ^ 3 = 1) (hHM : H ≤ M) (hεM : ε ∉ M) :
    Nat.card ↥(H ⊔ Subgroup.zpowers ε) = 3 * Nat.card H ∧
      (H ⊔ Subgroup.zpowers ε) ⊓ M = H := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hHN : H ≤ Subgroup.normalizer (Subgroup.zpowers ε : Set Ω) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro n
    have hc : Commute h ε := hcomm h hh
    constructor
    · intro hn
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
      rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
      exact Subgroup.zpow_mem_zpowers ε k
    · intro hn
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hn
      have : n = ε ^ k := by
        have e1 : n = h⁻¹ * (h * n * h⁻¹) * h := by group
        rw [e1, ← hk, mul_assoc, ← (hc.zpow_right k).eq, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [this]
      exact Subgroup.zpow_mem_zpowers ε k
  have hmem : ∀ x, x ∈ H ⊔ Subgroup.zpowers ε ↔
      ∃ h ∈ H, ∃ n ∈ Subgroup.zpowers ε, h * n = x := by
    intro x
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hHN, Set.mem_mul]
    simp only [SetLike.mem_coe]
  have hkey : ∀ n ∈ Subgroup.zpowers ε, n ∈ M → n = 1 := by
    intro n hn hnM
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    by_contra hne
    have hk : ¬ ((3 : ℕ) : ℤ) ∣ k := by
      rintro ⟨j, rfl⟩
      apply hne
      rw [zpow_mul, show ((3 : ℕ) : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, hε3, one_zpow]
    exact hεM (mem_of_zpow_mem Nat.prime_three hε3 hk hnM)
  have hε1 : ε ≠ 1 := fun h => hεM (h ▸ M.one_mem)
  have hord : orderOf ε = 3 := orderOf_eq_prime hε3 hε1
  refine ⟨?_, le_antisymm ?_ (le_inf le_sup_left hHM)⟩
  · let φ : ↥H × ↥(Subgroup.zpowers ε) → ↥(H ⊔ Subgroup.zpowers ε) := fun x =>
      ⟨(x.1 : Ω) * x.2, (hmem _).2 ⟨_, x.1.2, _, x.2.2, rfl⟩⟩
    have hφi : Function.Injective φ := by
      rintro ⟨h₁, n₁⟩ ⟨h₂, n₂⟩ hφ
      have h12 : (h₁ : Ω) * n₁ = h₂ * n₂ := congrArg Subtype.val hφ
      have hn : (n₂ : Ω) * (n₁ : Ω)⁻¹ = 1 := by
        refine hkey _ (Subgroup.mul_mem _ n₂.2 (Subgroup.inv_mem _ n₁.2)) ?_
        have e1 : (n₂ : Ω) * (n₁ : Ω)⁻¹ = (h₂ : Ω)⁻¹ * h₁ := by
          calc (n₂ : Ω) * (n₁ : Ω)⁻¹ = (h₂ : Ω)⁻¹ * (h₂ * n₂) * (n₁ : Ω)⁻¹ := by group
            _ = (h₂ : Ω)⁻¹ * (h₁ * n₁) * (n₁ : Ω)⁻¹ := by rw [h12]
            _ = (h₂ : Ω)⁻¹ * h₁ := by group
        rw [e1]
        exact hHM (H.mul_mem (H.inv_mem h₂.2) h₁.2)
      have hn' : (n₂ : Ω) = n₁ := mul_inv_eq_one.1 hn
      have hh' : (h₁ : Ω) = h₂ := by
        rw [hn'] at h12
        exact mul_right_cancel h12
      exact Prod.ext (Subtype.ext hh') (Subtype.ext hn'.symm)
    have hφs : Function.Surjective φ := by
      rintro ⟨x, hx⟩
      obtain ⟨h, hh, n, hn, rfl⟩ := (hmem x).1 hx
      exact ⟨(⟨h, hh⟩, ⟨n, hn⟩), rfl⟩
    rw [← Nat.card_congr (Equiv.ofBijective φ ⟨hφi, hφs⟩), Nat.card_prod, Nat.card_zpowers,
      hord, mul_comm]
  · rintro x ⟨hx, hxM⟩
    obtain ⟨h, hh, n, hn, rfl⟩ := (hmem x).1 hx
    have hnM : n ∈ M := by
      have := M.mul_mem (M.inv_mem (hHM hh)) hxM
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
    rw [hkey n hn hnM, mul_one]
    exact hh

private theorem zmod3_ne : (0 : ZMod 3) ≠ 1 ∧ (0 : ZMod 3) ≠ 2 ∧ (1 : ZMod 3) ≠ 2 := by
  decide

private theorem sup_zpowers_le {H K : Subgroup Ω} {ε : Ω} (hH : H ≤ K) (hε : ε ∈ K) :
    H ⊔ Subgroup.zpowers ε ≤ K :=
  sup_le hH ((Subgroup.zpowers_le).2 hε)

theorem genStep3On_holds {Q : TauCeti.LieTypeIndex → Prop} (h2 : GenCompQuasiOn Q) :
    GenStep3On Q := by
  intro p q Ω _ _ S B H hI B' d J hT hnJ
  obtain ⟨⟨hB'el, hB'c, hB'case⟩, hdB', hdS, hJ⟩ := hT
  have hBB' : Nat.card B ≤ Nat.card B' := by
    rcases hB'case with rfl | ⟨h, -⟩
    · exact le_rfl
    · exact h
  obtain ⟨hp3, hrel, hcard9, ⟨e, heJ, he3, heC, R, hRJ, hR, hR2, heR⟩, -⟩ :=
    hI B' d J hB'el hBB' hdB' hdS hJ hnJ
  subst hp3
  have hp : Nat.Prime 3 := H.pPrime
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  have hdp : d ^ 3 = 1 := hB'el.2 d hdB'
  obtain ⟨g, hgB, hgN⟩ : ∃ g ∈ B', g ∉ Subgroup.normalizer (J : Set Ω) := by
    by_contra h
    push Not at h
    exact hnJ h
  have hg3 : g ^ 3 = 1 := hB'el.2 g hgB
  have hJS : J ≤ S := hJ.1.trans inf_le_left
  have hcompM : ∀ x ∈ B', CFSG.Open.IsComponentOf (GLBConj x J)
      (S ⊓ Subgroup.centralizer ({d} : Set Ω)) := by
    intro x hx
    have hxM : x ∈ Subgroup.normalizer
        ((S ⊓ Subgroup.centralizer ({d} : Set Ω) : Subgroup Ω) : Set Ω) := by
      refine mem_normalizer_inf ?_ (Subgroup.le_normalizer
        (Subgroup.mem_centralizer_singleton_iff.2 (hB'el.comm hx hdB')))
      rw [Subgroup.normalizer_eq_top_iff.2 H.normal]
      exact Subgroup.mem_top x
    have hJ' : GLAPComponent 3 (S ⊓ Subgroup.centralizer ({d} : Set Ω)) (GLBConj x J) := by
      have := glaPComponent_gLBConj hJ x
      rwa [mem_normalizer_iff_gLBConj_eq.1 hxM] at this
    exact ⟨hJ'.1, hJ'.2.1, isQuasisimple_of_genCompQuasiOn h2 H hdp hdS hJ'⟩
  have hlbp : ∀ k : ZMod 3, lbp 3 g k ∈ B' := fun k => by
    unfold lbp
    exact B'.pow_mem hgB _
  set Jk : ZMod 3 → Subgroup Ω := fun k => GLBConj (lbp 3 g k) J with hJk
  set ε : ZMod 3 → Ω := fun k => lphi 3 g J k ⟨e, heJ⟩ with hε
  have hεJ : ∀ k, ε k ∈ Jk k := by
    intro k
    show lphi 3 g J k ⟨e, heJ⟩ ∈ GLBConj (lbp 3 g k) J
    rw [mem_gLBConj, lphi_apply]
    have : lbp 3 g k * ((lbp 3 g k)⁻¹ * e * lbp 3 g k) * (lbp 3 g k)⁻¹ = e := by group
    rw [this]
    exact heJ
  have hε3 : ∀ k, ε k ^ 3 = 1 := by
    intro k
    show (lphi 3 g J k ⟨e, heJ⟩) ^ 3 = 1
    rw [← map_pow]
    have : (⟨e, heJ⟩ : ↥J) ^ 3 = 1 := Subtype.ext he3
    rw [this, map_one]
  have hεC : ∀ k, ε k ∉ Subgroup.centralizer (Jk k : Set Ω) := by
    intro k hC
    apply heC
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    set t := lbp 3 g k
    have hjk : t⁻¹ * j * t ∈ Jk k := by
      show t⁻¹ * j * t ∈ GLBConj t J
      rw [mem_gLBConj]
      have : t * (t⁻¹ * j * t) * t⁻¹ = j := by group
      rw [this]
      exact hj
    have h1 : t⁻¹ * j * t * (t⁻¹ * e * t) = t⁻¹ * e * t * (t⁻¹ * j * t) := by
      have := Subgroup.mem_centralizer_iff.1 hC _ hjk
      rwa [show ε k = t⁻¹ * e * t from lphi_apply 3 g J k ⟨e, heJ⟩] at this
    calc j * e = t * (t⁻¹ * j * t * (t⁻¹ * e * t)) * t⁻¹ := by group
      _ = t * (t⁻¹ * e * t * (t⁻¹ * j * t)) * t⁻¹ := by rw [h1]
      _ = e * j := by group
  have hJcomm : ∀ i j : ZMod 3, i ≠ j → ∀ x ∈ Jk i, ∀ y ∈ Jk j, x * y = y * x := by
    intro i j hij
    rcases CFSG.Quasithin.F918V5G.isComponentOf_eq_or_commute (hcompM _ (hlbp i))
        (hcompM _ (hlbp j)) with h | h
    · exact absurd h (gLBConj_lbp_ne hp hg3 hgN hij)
    · exact h
  have hJ0 : Jk 0 = J := by
    show GLBConj (lbp 3 g 0) J = J
    rw [show lbp 3 g 0 = 1 by unfold lbp; rw [ZMod.val_zero, pow_zero]]
    exact CFSG.LocalAnalysis.GLTheoremB.gLBConj_one J
  have hε0 : ε 0 = e := by
    show lphi 3 g J 0 ⟨e, heJ⟩ = e
    rw [lphi_apply, show lbp 3 g 0 = 1 by unfold lbp; rw [ZMod.val_zero, pow_zero]]
    group
  set C : Subgroup Ω := B' ⊓ Subgroup.centralizer (J : Set Ω) with hC
  have hCJ : ∀ k, C ≤ Subgroup.centralizer (Jk k : Set Ω) := by
    intro k c hc
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    set t := lbp 3 g k
    have hxJ : t * x * t⁻¹ ∈ J := mem_gLBConj.1 hx
    have h1 : Commute c (t * x * t⁻¹) := (Subgroup.mem_centralizer_iff.1 hc.2 _ hxJ).symm
    have hct : Commute t c := hB'el.comm (hlbp k) hc.1
    have h2 : Commute c (t⁻¹ * (t * x * t⁻¹) * t) :=
      ((hct.inv_left.symm).mul_right h1).mul_right hct.symm
    rw [show t⁻¹ * (t * x * t⁻¹) * t = x by group] at h2
    exact h2.symm.eq
  have hεcomm : ∀ i j : ZMod 3, i ≠ j → ε i ∈ Subgroup.centralizer (Jk j : Set Ω) := by
    intro i j hij
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (hJcomm i j hij (ε i) (hεJ i) x hx).symm
  obtain ⟨h01, h02, h12⟩ := zmod3_ne
  set H₁ : Subgroup Ω := C ⊔ Subgroup.zpowers (ε 0) with hH₁
  set H₂ : Subgroup Ω := H₁ ⊔ Subgroup.zpowers (ε 1) with hH₂
  set H₃ : Subgroup Ω := H₂ ⊔ Subgroup.zpowers (ε 2) with hH₃
  have hH₁C : ∀ k, k ≠ 0 → H₁ ≤ Subgroup.centralizer (Jk k : Set Ω) := fun k hk =>
    sup_zpowers_le (hCJ k) (hεcomm 0 k hk.symm)
  have hH₂C : H₂ ≤ Subgroup.centralizer (Jk 2 : Set Ω) :=
    sup_zpowers_le (hH₁C 2 h02.symm) (hεcomm 1 2 h12)
  have hcommOf : ∀ {K : Subgroup Ω} (k : ZMod 3), K ≤ Subgroup.centralizer (Jk k : Set Ω) →
      ∀ h ∈ K, h * ε k = ε k * h := fun k hK h hh =>
    (Subgroup.mem_centralizer_iff.1 (hK hh) _ (hεJ k)).symm
  obtain ⟨hc₁, hi₁⟩ := sup_zpowers_of_not_mem (hcommOf 0 (hCJ 0)) (hε3 0) (hCJ 0) (hεC 0)
  obtain ⟨hc₂, hi₂⟩ := sup_zpowers_of_not_mem (hcommOf 1 (hH₁C 1 h01.symm)) (hε3 1)
    (hH₁C 1 h01.symm) (hεC 1)
  obtain ⟨hc₃, hi₃⟩ := sup_zpowers_of_not_mem (hcommOf 2 hH₂C) (hε3 2) hH₂C (hεC 2)
  have hCel : IsElemAbelian 3 C :=
    ⟨⟨⟨fun a b => Subtype.ext (hB'el.comm a.2.1 b.2.1)⟩⟩, fun x hx => hB'el.2 x hx.1⟩
  have hcommZ : ∀ {K : Subgroup Ω} (k : ZMod 3), K ≤ Subgroup.centralizer (Jk k : Set Ω) →
      ∀ a ∈ K, ∀ c ∈ Subgroup.zpowers (ε k), a * c = c * a := by
    intro K k hK a ha c hc
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
    exact ((Commute.zpow_right (hcommOf k hK a ha) n)).eq
  have hH₁el : IsElemAbelian 3 H₁ :=
    IsElemAbelian.sup_of_commute hCel (isElemAbelian_zpowers (hε3 0)) (hcommZ 0 (hCJ 0))
  have hH₂el : IsElemAbelian 3 H₂ :=
    IsElemAbelian.sup_of_commute hH₁el (isElemAbelian_zpowers (hε3 1))
      (hcommZ 1 (hH₁C 1 h01.symm))
  have hH₃el : IsElemAbelian 3 H₃ :=
    IsElemAbelian.sup_of_commute hH₂el (isElemAbelian_zpowers (hε3 2)) (hcommZ 2 hH₂C)
  have hdC : d ∈ C := by
    refine ⟨hdB', Subgroup.mem_centralizer_iff.2 fun j hj => ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.1 (hJ.1 hj).2
  have hCH₃ : C ≤ H₃ := le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hCN : ∀ {Y : Subgroup Ω}, Y ≤ J → C ≤ Subgroup.normalizer (Y : Set Ω) := by
    intro Y hY c hc
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun y hy => ?_)
    exact Subgroup.mem_centralizer_iff.1 hc.2 y (hY hy)
  have hεN : ∀ {Y : Subgroup Ω}, Y ≤ J → ∀ k, k ≠ 0 → ε k ∈ Subgroup.normalizer (Y : Set Ω) := by
    intro Y hY k hk
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun y hy => ?_)
    have h1 := Subgroup.mem_centralizer_iff.1 (hεcomm k 0 hk) y (by rw [hJ0]; exact hY hy)
    exact h1
  have hH₃N : ∀ {Y : Subgroup Ω}, Y ≤ J → ε 0 ∈ Subgroup.normalizer (Y : Set Ω) →
      H₃ ≤ Subgroup.normalizer (Y : Set Ω) := fun hY h0 =>
    sup_zpowers_le (sup_zpowers_le (sup_zpowers_le (hCN hY) h0) (hεN hY 1 h01.symm))
      (hεN hY 2 h02.symm)
  have hNJ : H₃ ≤ Subgroup.normalizer (J : Set Ω) :=
    hH₃N le_rfl (by rw [hε0]; exact Subgroup.le_normalizer heJ)
  have hNR : H₃ ≤ Subgroup.normalizer (R : Set Ω) := hH₃N hRJ (by rw [hε0]; exact heR)
  have hcardB' : Nat.card B' ≤ 27 * Nat.card C := by
    have h1 := Subgroup.relIndex_mul_card (H := Subgroup.normalizer (J : Set Ω)) (K := B')
    rw [hrel, inf_comm] at h1
    rw [← h1]
    calc 3 * Nat.card ↥(B' ⊓ Subgroup.normalizer (J : Set Ω)) ≤ 3 * (9 * Nat.card C) :=
          Nat.mul_le_mul_left 3 hcard9
      _ = 27 * Nat.card C := by ring
  have hcardB'' : Nat.card H₃ = 27 * Nat.card C := by
    rw [hc₃, hc₂, hc₁]
    ring
  have hcent : H₃ ⊓ centModSubgroup 3 S = B' ⊓ centModSubgroup 3 S := by
    rw [centModSubgroup_eq_of_genHyp H]
    have hSJ : ∀ k, Subgroup.centralizer (S : Set Ω) ≤ Subgroup.centralizer (Jk k : Set Ω) :=
      fun k => Subgroup.centralizer_le ((hcompM _ (hlbp k)).1.trans inf_le_left)
    apply le_antisymm
    · rintro x ⟨hx, hxS⟩
      have hx₂ : x ∈ H₂ := by rw [← hi₃]; exact ⟨hx, hSJ 2 hxS⟩
      have hx₁ : x ∈ H₁ := by rw [← hi₂]; exact ⟨hx₂, hSJ 1 hxS⟩
      have hx₀ : x ∈ C := by rw [← hi₁]; exact ⟨hx₁, hSJ 0 hxS⟩
      exact ⟨hx₀.1, hxS⟩
    · rintro x ⟨hx, hxS⟩
      have hxC : x ∈ C := ⟨hx, Subgroup.centralizer_le hJS hxS⟩
      exact ⟨hCH₃ hxC, hxS⟩
  refine ⟨H₃, ⟨⟨hH₃el, ?_, Or.inr ⟨?_, R, hR, hR2, hNR⟩⟩, hCH₃ hdC, hdS, hJ⟩, hNJ⟩
  · rw [hcent]
    exact hB'c
  · rw [hcardB'']
    exact hBB'.trans hcardB'

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen
