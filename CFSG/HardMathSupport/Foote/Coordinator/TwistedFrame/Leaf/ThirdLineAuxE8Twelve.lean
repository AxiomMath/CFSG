module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ThirdLineAuxCore
public import CFSG.RankThree.PartOne.KE.E8TwelveData
public import CFSG.RankThree.PartOne.KD4L.TrialityLayer

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.ThirdLineAux

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne
open CFSG.RankThree.E6 (chainRoot weylMatrix weylMatrix_mulVec weylMatrix_pow)

open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE
open CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
open scoped Matrix Pointwise MatrixGroups

set_option linter.unusedSectionVars false


theorem ncard_classSetL_le (rows : List LineRow) (j : ℕ) :
    (classSetL rows j).ncard ≤ (lineClassRoots rows j).length := by
  have h : classSetL rows j =
      (fun l => toVec Tag.E8.rank l) '' {l | l ∈ lineClassRoots rows j} := by
    ext α
    simp only [classSetL, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact ⟨l, hl, rfl⟩
    · rintro ⟨l, hl, rfl⟩
      exact ⟨l, hl, rfl⟩
  rw [h]
  calc _ ≤ {l | l ∈ lineClassRoots rows j}.ncard :=
        Set.ncard_image_le (List.finite_toSet _)
    _ = (lineClassRoots rows j).toFinset.card := by
        rw [← List.coe_toFinset, Set.ncard_coe_finset]
    _ ≤ _ := List.toFinset_card_le _

theorem e8T12_classes_le : ∀ j < 14, (lineClassRoots e8T12Rows j).length ≤ 24 := by
  decide +kernel


theorem twThirdLine_e8Twelve_aux (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hp7 : 7 < p) (hpq : ¬ p ∣ Nat.card K)
    (hord12 : orderOf ((Nat.card K : ℕ) : ZMod p) = 12)
    (hΦ : ((Nat.card K : ℕ) : ZMod p) ^ 4 - ((Nat.card K : ℕ) : ZMod p) ^ 2 + 1 = 0)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL .E8 L) (hnm : n ∈ monomialSubgroup .E8 L)
    (hnW : weylQuotientHom .E8 L ⟨n, hnm⟩ = (coxeterSystem .E8).wordProd e8T12WW) :
    TwThirdLine .E8 K p := by
  classical
  have hD4 : CFSG.RankThree.PartOne.KE.D4TrialityLayer Tag.E8 :=
    CFSG.RankThree.PartOne.KD4L.d4TrialityLayer_E8
  have : Fact p.Prime := ⟨hp⟩
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  set Φ : ModGL .E8 L →* ModGL .E8 L := Units.map (entrywiseHom Fr) with hΦdef
  have hFr' : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact hFr' c
  have hℓq : ℓ ∣ Nat.card K := by
    rw [hK]
    exact dvd_pow_self _ (by omega)
  have hℓ : ℓ.Prime := Fact.out
  have hnC : n ∈ adjointGroup .E8 L := monomialSubgroup_le_adjointGroup' hnm
  have hinj0 : Function.Injective (rootDiagUnitHom .E8 L) := rootDiagUnit_injective
  have hnWv : ∀ u, weylQuotientHom .E8 L ⟨n, hnm⟩ • u = e8T12V *ᵥ u := fun u => by
    rw [hnW]
    exact e8T12_weylImage u
  have hordW : ¬ p ∣ Nat.card (WeylGroup .E8) :=
    not_dvd_card_weylGroup_E hp hp7 (Or.inr (Or.inr rfl))
  have hT : twistedTorusOf n Φ = (fixedCharTuples e8T12V Fr).map (rootDiagUnitHom .E8 L) := by
    rw [← twistedFixedTuples_eq_fixedCharTuples hnWv Fr]
    exact twistedTorus_eq_map_twistedFixedTuples_of_weylImage hnm _ rfl Fr
  set G1 := fixedBlockTuples e8T12V Fr
    (e8T12Bas e8T12B1List e8T12B2List '' {i : Fin Tag.E8.rank | (i : ℕ) < 4}) with hG1
  set G2 := fixedBlockTuples e8T12V Fr
    (e8T12Bas e8T12B2List e8T12B1List '' {i : Fin Tag.E8.rank | (i : ℕ) < 4}) with hG2
  set N : ℕ := (Nat.card K ^ 4 - Nat.card K ^ 2 + 1) ^ 2 with hNdef
  set Z0 : Subgroup (ModGL .E8 L) := (G1 ⊔ G2).map (rootDiagUnitHom .E8 L) with hZ0def
  have hZ0le : Z0 ≤ twistedTorusOf n Φ := by
    rw [hT]
    exact Subgroup.map_mono (sup_le inf_le_left inf_le_left)
  have hZ0card : Nat.card Z0 = N := by
    rw [hZ0def, Subgroup.card_map_of_injective hinj0]
    exact e8T12_card_sup Fr hFr hℓ hℓq hq2
  have h24 : Nat.card K ^ 2 ≤ Nat.card K ^ 4 :=
    Nat.pow_le_pow_right (lt_of_lt_of_le (by norm_num) hq2) (by norm_num)
  have hN : N ≠ 0 := pow_ne_zero 2 (by omega)
  have hord : p ^ (Nat.card (adjointGroup .E8 K)).factorization p = p ^ N.factorization p :=
    e8T12_ordProj hp hp3 hpq hord12
  obtain ⟨g0, hg0C, hg0, hperf, hconj⟩ := sigma_untwisted_sylow .E8 1
    (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hf hK L hp hp3 n hnC Z0 hZ0le hN hZ0card hord
  have hconj' : ∀ Q : Subgroup (adjointGroup .E8 K), IsPGroup p Q →
      ∃ c : adjointGroup .E8 K, ∀ y ∈ Q,
        g0⁻¹ * adjEmb .E8 K L (c * y * c⁻¹) * g0 ∈ twistedTorusOf n Φ := by
    intro Q hQ
    obtain ⟨c, hc⟩ := hconj Q hQ
    exact ⟨c, fun y hy => hZ0le ((mem_subtorusImage_iff _ _ _ _).1 (hc y hy))⟩
  have hbfix : ∀ b : Fin Tag.E8.rank → Lˣ, rootDiagUnit .E8 b ∈ twistedTorusOf n Φ →
      b ∈ fixedCharTuples e8T12V Fr := by
    intro b hbT
    rw [hT] at hbT
    obtain ⟨b', hb', hb'e⟩ := hbT
    have : b' = b := hinj0 hb'e
    rw [← this]
    exact hb'
  have hbound : ∀ b : Fin Tag.E8.rank → Lˣ, rootDiagUnit .E8 b ∈ twistedTorusOf n Φ →
      (∀ i, b i ^ p = 1) → b ≠ 1 → (rootCharKernel b).ncard ≤ 24 := by
    intro b hbT hbp hb1
    have hcls : ∀ j, j < 14 → (classSetL e8T12Rows j).ncard ≤ 24 := fun j hj =>
      (ncard_classSetL_le _ _).trans (e8T12_classes_le j hj)
    rcases e8T12_kernel_structure Fr hFr hp hp3 hΦ (hbfix b hbT) hbp hb1 with
      h0 | ⟨cc, hcc, hker', -⟩ | ⟨cc, hcc, hker', -⟩
    · rw [h0, Set.ncard_empty]
      omega
    · rw [hker']
      refine hcls _ ?_
      revert cc
      have : ∀ c ∈ e8T12D4Certs, c.cls < 14 := by decide +kernel
      exact fun cc hcc _ => this cc hcc
    · rw [hker']
      refine hcls _ ?_
      revert cc
      have : ∀ c ∈ e8T12TwoA2Certs, c.cls < 14 := by decide +kernel
      exact fun cc hcc _ => this cc hcc
  have hperx : ∀ (x c : adjointGroup .E8 K) (b : Fin Tag.E8.rank → Lˣ), orderOf x = p →
      g0⁻¹ * adjEmb .E8 K L (c * x * c⁻¹) * g0 ∈ twistedTorusOf n Φ →
      rootDiagUnit .E8 b = g0⁻¹ * adjEmb .E8 K L (c * x * c⁻¹) * g0 →
      (rootCharKernel b).Nonempty →
      ¬ Group.IsSolvable ↥(Subgroup.centralizer ({x} : Set (adjointGroup .E8 K))) := by
    intro x c b hx hh hb hne
    have hbh' : rootDiagUnit .E8 b = g0⁻¹ * adjEmb .E8 K L (c * x * c⁻¹) * g0 := hb
    have hordh : orderOf (g0⁻¹ * adjEmb .E8 K L (c * x * c⁻¹) * g0) = p := by
      have e1 : orderOf (g0⁻¹ * adjEmb .E8 K L (c * x * c⁻¹) * g0) =
          orderOf (adjEmb .E8 K L (c * x * c⁻¹)) := by
        have := orderOf_injective (MulAut.conj g0⁻¹).toMonoidHom (MulAut.conj g0⁻¹).injective
          (adjEmb .E8 K L (c * x * c⁻¹))
        simpa [MulAut.conj_apply] using this
      have e2 : orderOf (adjEmb .E8 K L (c * x * c⁻¹)) = orderOf (c * x * c⁻¹) :=
        orderOf_injective (adjEmb .E8 K L) adjEmb_injective _
      have e3 : orderOf (c * x * c⁻¹) = orderOf x := by
        have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective x
        simpa [MulAut.conj_apply] using this
      rw [e1, e2, e3, hx]
    have hbp : orderOf (rootDiagUnit .E8 b) = p := by rw [hbh']; exact hordh
    have hap := pow_eq_one_of_orderOf_rootDiagUnit hbp
    have hb1 := ne_one_of_orderOf_rootDiagUnit hp hbp
    have hkd := e8T12_kernel_structure Fr hFr hp hp3 hΦ (hbfix b (hbh' ▸ hh)) hap hb1
    rcases hkd with hA | ⟨cc, hcc, hker', hgood⟩ | ⟨cc, hcc, hker', hgood⟩
    · exfalso
      rw [hA] at hne
      exact Set.not_nonempty_empty hne
    ·
      obtain ⟨hS1, u, hu, hcertw⟩ := D4Cert.sound hgood
      obtain ⟨-, -, -, hab, hbc, hac, ha, hbl, hcl, -⟩ := hgood
      set v : WeylGroup .E8 := (coxeterSystem .E8).wordProd cc.w with hv
      have hSeq : rootCharKernel b = (fun γ => v • γ) '' parabolicRoots .E8 (d4Nodes .E8) :=
        hker'.trans hS1
      have hcert : ∃ u ∈ parabolicWeylGroup .E8 (d4Nodes .E8),
          ∀ α ∈ parabolicRoots .E8 (d4Nodes .E8),
            (v⁻¹ * weylQuotientHom .E8 L ⟨n, hnm⟩ * v) • α =
              u • permLattice (List.formPerm [cc.a, cc.b, cc.c]) α := by
        rw [hnW]
        exact ⟨u, hu, hcertw⟩
      obtain ⟨P, hfam, hP1, h₀, hh₀⟩ := e8_d4_family hD4 hf hK v n hnm hnC cc.a cc.b cc.c hab hbc
        hac (by rcases ha with h | h | h <;> simp [h]) (by rcases hbl with h | h | h <;> simp [h])
        (by rcases hcl with h | h | h <;> simp [h]) hcert
      obtain ⟨ψ, hψinj, -, -, -, -, hPψ, -⟩ := e8_perx_core Fr hFr n g0 hg0C hg0 hperf hp hordW
        hx c hbh' hh hSeq (d4Set_isRoot v) (d4Set_neg v) hfam
      exact not_isSolvable_of_embedding ψ hψinj (hfam.2.1 ()) (hPψ ())
    ·
      obtain ⟨hS1, hex12, hex21, hπ₁, hπ₂, horth⟩ :=
        TwoA2Cert.sound (M := e8T12V) (Wl := e8T12VList) e8T12V_eq hgood
      obtain ⟨k₂, _, _, _, hk₂⟩ := exists_finite_field_isAlgClosure ℓ (2 * f) (by omega) K L
      obtain ⟨P, hfam⟩ := e8_two_A2_family hf Fr hFr' hk₂ e8T12V n hnm hnWv
        ((coxeterSystem .E8).wordProd cc.w₁) ((coxeterSystem .E8).wordProd cc.w₂) hex12 hex21 hπ₁
        hπ₂ horth
      have hSeq : rootCharKernel b = sigmaSetE8 ((coxeterSystem .E8).wordProd cc.w₁) ∪
          sigmaSetE8 ((coxeterSystem .E8).wordProd cc.w₂) := hker'.trans hS1
      obtain ⟨ψ, hψinj, -, -, -, -, hPψ, -⟩ := e8_perx_core Fr hFr n g0 hg0C hg0 hperf hp hordW
        hx c hbh' hh hSeq (twoA2Set_isRoot _ _) (twoA2Set_neg _ _) hfam
      exact not_isSolvable_of_embedding ψ hψinj (hfam.2.1 ()) (hPψ ())
  exact twThirdLine_of_kernel Φ n g0 hp hconj' 24 (by rw [card_rootFinset_E8]; norm_num) hbound
    hperx

theorem twThirdLine_e8Twelve (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = 12) : TwThirdLine .E8 K p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨ℓ, f, hℓ, hchar, hf, hK⟩ := exists_char_pow K
  let L := AlgebraicClosure K
  haveI : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have hq0 : ((Nat.card K : ℕ) : ZMod p) ≠ 0 := fun h => by
    rw [h, orderOf_zero] at hord
    omega
  have hdvd : 12 ∣ p - 1 := hord ▸ ZMod.orderOf_dvd_card_sub_one hq0
  have hp7 : 7 < p := by omega
  have hpq : ¬ p ∣ Nat.card K := fun h => hq0 ((ZMod.natCast_eq_zero_iff _ _).2 h)
  have hΦ' := phi12_of_orderOf hord
  have hcm := canonicalRep_mem_monomialSubgroup L ((coxeterSystem .E8).wordProd e8T12WW)
  have hnW : weylQuotientHom .E8 L ⟨canonicalRep (coxeterSystem .E8) L
      ((coxeterSystem .E8).wordProd e8T12WW), hcm⟩ = (coxeterSystem .E8).wordProd e8T12WW :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep _)
  exact twThirdLine_e8Twelve_aux K hf hK hp (by omega) hp7 hpq hord hΦ' L _ hcm hnW

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.ThirdLineAux
