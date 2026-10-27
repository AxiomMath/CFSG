module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Native

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo.SeitzRows

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.LocalRank CFSG.RankThree.PartOne
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.KE
  CFSG.RankThree.Classical2 CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
open CFSG.RankThree.E6 (chainRoot weylMatrix weylMatrix_mulVec)
open CFSG.RankThree.Chevalley (exhaustionPhi)
open scoped Matrix Pointwise MatrixGroups

set_option linter.unusedSectionVars false

section Family


theorem e8Five_family_card {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {L : Type} [Field L]
    [IsAlgClosed L] {k : Type} [Field k] [Algebra k L] [IsAlgClosure k L]
    (hk : Nat.card k = ℓ ^ f) (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    (n : ModGL Tag.E8 L) (hnm : n ∈ monomialSubgroup Tag.E8 L)
    (hnW : ∀ u, weylQuotientHom Tag.E8 L ⟨n, hnm⟩ • u = ((1 : ℤ) • weylMatrix e8F5U) *ᵥ u)
    (v : WeylGroup Tag.E8)
    (hsplit : ∃ π : Equiv.Perm (Fin 5), ∀ i j : Fin 5, i ≠ j →
      weylMatrix e8F5U *ᵥ sigmaRootE8A4 v i j = sigmaRootE8A4 v (π i) (π j)) :
    ∃ P : Unit → Subgroup (ModGL Tag.E8 L), IsSigmaFamily n Fr (sigmaSetE8A4 v) P ∧
      P () = rootSpan Tag.E8 L (sigmaSetE8A4 v) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom Fr)) ∧
      Nat.card (P ()) = Nat.card SL(5, k) := by
  classical
  have hFrbij : Function.Bijective Fr := ⟨Fr.injective, fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (show 0 < ℓ ^ f from pow_pos hℓ.pos f)
    exact ⟨x, by rw [hFr, hx]⟩⟩
  choose! ε hε using fun (i j : Fin 5) (hij : i ≠ j) =>
    rhoSigmaE8A4_transvection (L := L) v i j hij
  have htor : ∀ b : Fin Tag.E8.rank → Lˣ, ∃ d : Fin 5 → Lˣ, ∀ A : SL(5, L),
      rootDiagUnit Tag.E8 b * rhoSigmaE8A4 L v A * (rootDiagUnit Tag.E8 b)⁻¹ =
        rhoSigmaE8A4 L v (conjDiagn d A) := fun b =>
    ⟨fun i => rootChar b (wbE8A4 v i), fun A => rhoSigmaE8A4_torus v b A⟩
  have hdiag : ∀ A : SL(5, L), (∀ i j, i ≠ j → (A : Matrix (Fin 5) (Fin 5) L) i j = 0) →
      rhoSigmaE8A4 L v A ∈ torusGroup Tag.E8 L := fun A hA => rhoSigmaE8A4_diagonal v A hA
  have hrange := rhoSigmaE8A4_range (L := L) v
  obtain ⟨π, hπ⟩ := hsplit
  have hconj : ∀ i j : Fin 5, i ≠ j → ∃ b : Lˣ, ∀ c : L,
      n * pinnedX Tag.E8 L (sigmaRootE8A4 v i j) c * n⁻¹ =
        pinnedX Tag.E8 L (sigmaRootE8A4 v (π i) (π j)) ((b : L) * c) := fun i j hij => by
    obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hnm (isRoot_sigmaRootE8A4 v hij)
    refine ⟨μ, fun c => ?_⟩
    rw [hμ c, hnW, one_smul, hπ i j hij]
  obtain ⟨Φ', hΦ', b, hshape⟩ := exists_aut_of_rootData_n (τ := Tag.E8) (ν := 5)
    (rhoSigmaE8A4 L v) (rhoSigmaE8A4_injective v) (sigmaRootE8A4 v) ε hε Fr hFrbij n
    (fun i j => (π i, π j)) (fun i j hij => π.injective.ne hij)
    (fun i j hij => ⟨π.symm i, π.symm j, π.symm.injective.ne hij, by simp⟩) hconj
  have hshape' : ∀ (i j : Fin 5) (hij : i ≠ j) (t : L),
      ((Φ' (Matrix.SpecialLinearGroup.transvection hij t) : SL(5, L)) :
        Matrix (Fin 5) (Fin 5) L) = 1 + single (π i) (π j) ((b i j : L) * t ^ ℓ ^ f) :=
    fun i j hij t => by rw [hshape i j hij t, hFr]
  obtain ⟨P, hP, hP1, hP2⟩ := an_family_split hℓ hf hk (by norm_num) (sigmaSetE8A4_isRoot v)
    (rhoSigmaE8A4 L v) (rhoSigmaE8A4_injective v) hrange htor hdiag Fr n Φ' hΦ' π b hshape'
  obtain ⟨-, ⟨H, hH⟩, -, -, -, -⟩ :=
    sln_root_permuting_frobenius_fixed_split hℓ hf hk (by norm_num) π Φ' b hshape'
  refine ⟨P, hP, by rw [hP1, hrange], ?_⟩
  let θ : SL(5, k) →* SL(5, L) := (MulAut.conj H).toMonoidHom.comp
    (Matrix.SpecialLinearGroup.map (algebraMap k L))
  have hθinj : Function.Injective θ := (MulAut.conj H).injective.comp
    (specialLinearGroup_map_injective (algebraMap k L).injective)
  have hfix : fixSubgroup Φ' = θ.range := by
    ext X
    rw [hH X]
    constructor
    · rintro ⟨Y, rfl⟩
      exact ⟨Y, by simp [θ, MulAut.conj_apply]⟩
    · rintro ⟨Y, rfl⟩
      exact ⟨Y, by simp [θ, MulAut.conj_apply]⟩
  rw [hP2, Subgroup.card_map_of_injective (rhoSigmaE8A4_injective v), hfix]
  exact (Nat.card_congr (MonoidHom.ofInjective hθinj).toEquiv).symm

theorem e8Five_centralizer_layer (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp7 : 7 < p) (hordq : orderOf ((Nat.card K : ℕ) : ZMod p) = 5)
    {x : adjointGroup .E8 K} (hx : orderOf x = p) :
    (∀ u ∈ Subgroup.centralizer ({x} : Set (adjointGroup .E8 K)),
      ∀ v ∈ Subgroup.centralizer ({x} : Set (adjointGroup .E8 K)), u * v = v * u) ∨
    (CFSG.IsQuasisimple (⁅Subgroup.centralizer ({x} : Set (adjointGroup .E8 K)),
        Subgroup.centralizer ({x} : Set (adjointGroup .E8 K))⁆ : Subgroup (adjointGroup .E8 K)) ∧
      Nat.card (⁅Subgroup.centralizer ({x} : Set (adjointGroup .E8 K)),
        Subgroup.centralizer ({x} : Set (adjointGroup .E8 K))⁆ : Subgroup (adjointGroup .E8 K)) =
        Nat.card SL(5, K)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 < p := by omega
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨ℓ, f, hℓ, hchar, hf, hK⟩ := exists_charP_card K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  let L := AlgebraicClosure K
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hnm := canonicalRep_mem_monomialSubgroup L e8F5U
  set n : ModGL .E8 L := canonicalRep (coxeterSystem .E8) L e8F5U with hndef
  have hπ : weylQuotientHom .E8 L ⟨n, hnm⟩ = e8F5U :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep e8F5U)
  have hnW : ∀ u, weylQuotientHom .E8 L ⟨n, hnm⟩ • u = ((1 : ℤ) • weylMatrix e8F5U) *ᵥ u :=
    fun u => by rw [hπ, one_smul, weylMatrix_mulVec]
  have hq0 : ((Nat.card K : ℕ) : ZMod p) ≠ 0 := by
    intro h
    rw [h, orderOf_eq_zero_iff'.2] at hordq
    · exact absurd hordq (by norm_num)
    · intro n hn h'
      rw [zero_pow hn.ne'] at h'
      exact zero_ne_one h'
  have hpq : ¬ p ∣ Nat.card K := fun h => hq0 ((ZMod.natCast_eq_zero_iff _ _).2 h)
  have h5 : ((Nat.card K : ℕ) : ZMod p) ^ 5 = 1 := hordq ▸ pow_orderOf_eq_one _
  have h1 : ((Nat.card K : ℕ) : ZMod p) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hordq
    exact absurd hordq (by norm_num)
  have hΦ' : ((Nat.card K : ℕ) : ZMod p) ^ 4 + ((Nat.card K : ℕ) : ZMod p) ^ 3 +
      ((Nat.card K : ℕ) : ZMod p) ^ 2 + ((Nat.card K : ℕ) : ZMod p) + 1 = 0 := by
    have hmul : (((Nat.card K : ℕ) : ZMod p) - 1) * (((Nat.card K : ℕ) : ZMod p) ^ 4 +
        ((Nat.card K : ℕ) : ZMod p) ^ 3 + ((Nat.card K : ℕ) : ZMod p) ^ 2 +
        ((Nat.card K : ℕ) : ZMod p) + 1) = 0 := by
      linear_combination h5
    rcases mul_eq_zero.1 hmul with h | h
    · exact absurd (sub_eq_zero.1 h) h1
    · exact h
  have hΦ := e8Five_hΦ_one (p := p) _ hΦ'
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  set Φ : ModGL .E8 L →* ModGL .E8 L := Units.map (entrywiseHom Fr) with hΦdef
  have hFr' : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact hFr' c
  have hℓq : ℓ ∣ Nat.card K := by
    rw [hK]
    exact dvd_pow_self _ (by omega)
  have hnC : n ∈ adjointGroup .E8 L := monomialSubgroup_le_adjointGroup' hnm
  have hinj0 : Function.Injective (rootDiagUnitHom .E8 L) := rootDiagUnit_injective
  have hT : twistedTorusOf n Φ =
      (fixedCharTuples (e8FiveM 1) Fr).map (rootDiagUnitHom .E8 L) := by
    have h := twistedFixedTuples_eq_fixedCharTuples hnW Fr
    rw [show e8FiveM 1 = (1 : ℤ) • weylMatrix e8F5U from rfl, ← h]
    exact twistedTorus_eq_map_twistedFixedTuples_of_weylImage hnm _ rfl Fr
  set G4 := fixedBlockTuples (e8FiveM 1) Fr
    (e8FiveCols 4 1 '' {i : Fin Tag.E8.rank | (i : ℕ) < 4}) with hG4
  set G0 := fixedBlockTuples (e8FiveM 1) Fr
    (e8FiveCols 0 1 '' {i : Fin Tag.E8.rank | (i : ℕ) < 4}) with hG0
  set N : ℕ := (((Nat.card K : ℤ) ^ 4 + 1 * (Nat.card K : ℤ) ^ 3 + (Nat.card K : ℤ) ^ 2 +
    1 * (Nat.card K : ℤ) + 1).natAbs) ^ 2 with hNdef
  set Z0 : Subgroup (ModGL .E8 L) := (G4 ⊔ G0).map (rootDiagUnitHom .E8 L) with hZ0def
  have hZ0le : Z0 ≤ twistedTorusOf n Φ := by
    rw [hT]
    exact Subgroup.map_mono (sup_le inf_le_left inf_le_left)
  have hZ0card : Nat.card Z0 = N := by
    rw [hZ0def, Subgroup.card_map_of_injective hinj0]
    exact e8Five_card_sup 1 (Or.inl rfl) Fr hFr hℓ hℓq hq2
  have hN : N ≠ 0 := by
    refine pow_ne_zero 2 (Int.natAbs_ne_zero.2 ?_)
    have := e8FiveP_eval_ne_zero 1 (Or.inl rfl) hq2
    rwa [e8FiveP_eval] at this
  have hord : p ^ (Nat.card (adjointGroup .E8 K)).factorization p = p ^ N.factorization p :=
    e8Five_ordProj K 1 (Or.inl rfl) hp hp5 (Or.inl rfl) hordq hpq hΦ
  obtain ⟨g0, hg0C, hg0, hperf, hconj⟩ := sigma_untwisted_sylow .E8 1
    (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hf hK L hp (by omega) n hnC Z0 hZ0le hN hZ0card hord
  obtain ⟨c, hc⟩ := hconj (Subgroup.zpowers x)
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one]))
  have hxc : c * x * c⁻¹ ∈ subtorusImage (adjEmb .E8 K L) g0 Z0 := hc x (Subgroup.mem_zpowers x)
  have hh : g0⁻¹ * adjEmb .E8 K L (c * x * c⁻¹) * g0 ∈ twistedTorusOf n Φ :=
    hZ0le ((mem_subtorusImage_iff _ _ _ _).1 hxc)
  have hordW : ¬ p ∣ Nat.card (WeylGroup .E8) :=
    not_dvd_card_weylGroup_E hp hp7 (Or.inr (Or.inr rfl))
  set ι : adjointGroup .E8 K →* ModGL .E8 L := adjEmb .E8 K L with hιdef
  set h : ModGL .E8 L := g0⁻¹ * ι (c * x * c⁻¹) * g0 with hhdef
  have hh' := hh
  rw [hT] at hh'
  obtain ⟨b, hb, hbh⟩ := hh'
  have hbh' : rootDiagUnit .E8 b = h := hbh
  have hordh : orderOf h = p := by
    have e1 : orderOf h = orderOf (ι (c * x * c⁻¹)) := by
      have := orderOf_injective (MulAut.conj g0⁻¹).toMonoidHom (MulAut.conj g0⁻¹).injective
        (ι (c * x * c⁻¹))
      rw [hhdef]
      simpa [MulAut.conj_apply] using this
    have e2 : orderOf (ι (c * x * c⁻¹)) = orderOf (c * x * c⁻¹) :=
      orderOf_injective ι adjEmb_injective _
    have e3 : orderOf (c * x * c⁻¹) = orderOf x := by
      have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective x
      simpa [MulAut.conj_apply] using this
    rw [e1, e2, e3, hx]
  have hbp : orderOf (rootDiagUnit .E8 b) = p := by rw [hbh']; exact hordh
  have hap := pow_eq_one_of_orderOf_rootDiagUnit hbp
  have hb1 := ne_one_of_orderOf_rootDiagUnit hp hbp
  have hker : ∀ a : Fin Tag.E8.rank → Lˣ, rootDiagUnit .E8 a = h →
      rootCharKernel a = rootCharKernel b := fun a ha => by
    have : a = b := hinj0 (ha.trans hbh'.symm)
    rw [this]
  have core : ∀ (S : Set (Fin Tag.E8.rank → ℤ)), rootCharKernel b = S →
      (∀ α ∈ S, IsRoot .E8 α) → (∀ α ∈ S, -α ∈ S) →
      ∀ {ι' : Type} (P : ι' → Subgroup (ModGL .E8 L)), (∀ i, Finite (P i)) →
        (∀ i, CFSG.IsQuasisimple (P i)) → (∀ i, P i ≤ rootSpan .E8 L S) →
        (∀ i, P i ≤ twistedFixedPoints n Φ) → (∀ i, P i ≤ adjointGroup .E8 L) →
        (∀ i, ∀ y ∈ torusGroup .E8 L ⊔ rootSpan .E8 L S, y ∈ twistedFixedPoints n Φ →
          ∀ u ∈ P i, y * u * y⁻¹ ∈ P i) →
        (∀ y ∈ torusGroup .E8 L ⊔ rootSpan .E8 L S, y ∈ twistedFixedPoints n Φ →
          (∀ i, ∀ u ∈ P i, y * u = u * y) → y ∈ subtorusSigma n Φ S) →
        ∃ ψ : Subgroup.centralizer ({x} : Set (adjointGroup .E8 K)) →* ModGL .E8 L,
          Function.Injective ψ ∧
          (∀ y, ψ y = g0⁻¹ * ι (c * (y : adjointGroup .E8 K) * c⁻¹) * g0) ∧
          (∀ y, ψ y ∈ torusGroup .E8 L ⊔ rootSpan .E8 L S) ∧
          (∀ y, n * Φ (ψ y) * n⁻¹ = ψ y) ∧ (∀ y, ψ y ∈ adjointGroup .E8 L) ∧
          (∀ i, P i ≤ ψ.range) := by
    intro S hSeq hS hSn ι' P hPfin hPq hPQ hPR hPadj hPnorm hPcent
    have hsub : S ⊆ rootCharKernel b := fun α hα => by rw [hSeq]; exact hα
    have hle := rootSpan_le_centralizer (K := L) b hsub
    have hcS : c * x * c⁻¹ ∈ subtorusImage ι g0 (subtorusSigma n Φ S) := by
      rw [mem_subtorusImage_iff]
      refine Subgroup.mem_inf.2 ⟨hh, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
      have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hle hg)
      rw [hbh'] at h1
      exact h1
    have hkerZ : ∀ a : Fin Tag.E8.rank → Lˣ, rootDiagUnit .E8 a = h → rootCharKernel a ⊆ S :=
      fun a ha => by rw [hker a ha, hSeq]
    obtain ⟨ψ, hψinj, hψ, hψHQ, hψR, hψadj, hPψ, -⟩ :=
      sigma_embedding_data ι adjEmb_injective adjEmb_mem Φ (adjEmb_frobenius Fr hFr) n g0
        hg0C hg0 hperf hp hordW hS hSn P hPfin hPq hPQ hPR hPadj hPnorm hPcent hx c hcS hkerZ
    exact ⟨ψ, hψinj, hψ, hψHQ, hψR, hψadj, hPψ⟩
  have hkd := e8Five_kernel_of_fixed 1 (Or.inl rfl) Fr hFr hp hp5 hΦ hb hap hb1
  have hrootneg : ∀ α ∈ rootCharKernel b, -α ∈ rootCharKernel b := fun α hα =>
    ⟨IsRoot.neg hα.1, by rw [CFSG.RankThree.Chevalley.rootChar_neg', hα.2, inv_one]⟩
  rcases hkd with hA | ⟨v, hSeq, hs, hu⟩
  ·
    have hspan : rootSpan .E8 L (rootCharKernel b) = ⊥ := by
      rw [hA]
      simp [rootSpan]
    obtain ⟨ψ, hψinj, hψ, hψHQ, hψR, hψadj, -⟩ := core (rootCharKernel b) rfl
      (fun α hα => hα.1) hrootneg (ι' := Empty) (fun e => e.elim) (fun e => e.elim)
      (fun e => e.elim) (fun e => e.elim) (fun e => e.elim) (fun e => e.elim) (fun e => e.elim)
      (fun y hy hyR _ => by
        rw [hspan, sup_bot_eq] at hy
        refine Subgroup.mem_inf.2 ⟨mem_twistedTorusOf.2 ⟨hy, hyR⟩, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        rw [hspan] at hg
        have : g = 1 := hg
        rw [this, one_mul, mul_one])
    refine Or.inl fun u hu v hv => ?_
    have hψu := hψHQ ⟨u, hu⟩
    have hψv := hψHQ ⟨v, hv⟩
    rw [hspan, sup_bot_eq] at hψu hψv
    obtain ⟨bu, hbu⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hψu
    have hcomm : ψ ⟨u, hu⟩ * ψ ⟨v, hv⟩ = ψ ⟨v, hv⟩ * ψ ⟨u, hu⟩ := by
      rw [hbu]
      exact rootDiagUnit_mul_comm_of_mem_torusGroup bu hψv
    have := hψinj (show ψ (⟨u, hu⟩ * ⟨v, hv⟩) = ψ (⟨v, hv⟩ * ⟨u, hu⟩) by
      rw [map_mul, map_mul]; exact hcomm)
    exact congrArg Subtype.val this
  ·
    obtain ⟨P, hP, hP1, hcardP⟩ := e8Five_family_card hℓ hf (k := K) hK Fr hFr' n hnm hnW v (hs rfl)
    obtain ⟨hPfin, hPq, hPQ, hPR, hPadj, hPnorm, hPcent⟩ := hP
    obtain ⟨ψ, hψinj, hψ, hψHQ, hψR, hψadj, hPψ⟩ := core (sigmaSetE8A4 v) hSeq
      (sigmaSetE8A4_isRoot v) (sigmaSetE8A4_neg v) P hPfin hPq hPQ hPR hPadj hPnorm hPcent
    have hcomm : ⁅ψ.range, ψ.range⁆ = P () := by
      refine commutator_range_eq_of_family ψ (H := torusGroup .E8 L)
        (Q := rootSpan .E8 L (sigmaSetE8A4 v)) (R := twistedFixedPoints n Φ) ?_ ?_ hψHQ
        (fun y => mem_twistedFixedPoints.2 (hψR y)) hP1 (hPψ ()) ?_
      · exact CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan (sigmaSetE8A4_isRoot v)
      · intro a ha a' ha'
        obtain ⟨b₁, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ha
        exact rootDiagUnit_mul_comm_of_mem_torusGroup b₁ ha'
      · exact Subgroup.isPerfect_iff.1 (hPq ()).1
    obtain ⟨hq, hmapψ, hmapsub⟩ := isQuasisimple_commutator_of_embedding ψ hψinj (hPq ()) hcomm
    refine Or.inr ⟨hq, ?_⟩
    rw [← hmapsub, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), ← hcardP,
      ← hmapψ, Subgroup.card_map_of_injective hψinj]

end Family

end CFSG.HardMathSupport.Timmesfeld.LocalTwo.SeitzRows
