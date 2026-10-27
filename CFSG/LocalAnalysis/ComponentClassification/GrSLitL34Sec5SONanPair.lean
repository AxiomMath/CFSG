module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SONanConfig
public import CFSG.GroupTheory.PCore.QuasisimpleNormalCore
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitL34FUSylow
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SKernelClosure
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.GroupTheory.PCore.SubgroupCore
public import CFSG.GroupTheory.QuasiDihedralFusion.Basic
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingLemma34Sylow
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SONanGluing
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.Blueprint.NativeSporadic (IsSporadic)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ONPar
open scoped commutatorElement

private theorem two_dvd_card_carrier_on :
    2 ∣ Nat.card (Blueprint.NativeSporadic.Carrier .ONan) := by
  have hPv : 2 ∣ Nat.card CFSG.ONSchreier.Pv := by
    have hcard : Nat.card CFSG.Sporadic.ONOddCore.omegaP = 8 :=
      CFSG.Sporadic.ONOddCore.card_omegaP
    have hx : ∃ x ∈ CFSG.Sporadic.ONOddCore.omegaP, x ≠ 1 := by
      by_contra h
      push Not at h
      have hbot : CFSG.Sporadic.ONOddCore.omegaP = ⊥ := by
        rw [eq_bot_iff]
        intro y hy
        simpa using h y hy
      rw [hbot] at hcard
      simp at hcard
    obtain ⟨x, hx, hx1⟩ := hx
    have hsq : x * x = 1 := by
      have : CFSG.IsElementaryAbelian 2 CFSG.Sporadic.ONOddCore.omegaP :=
        CFSG.Sporadic.ONOddCore.omegaP_elementary
      have h := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2)
        (A := CFSG.Sporadic.ONOddCore.omegaP) x hx
      simpa [pow_two] using h
    have hxP : x ∈ CFSG.ONSchreier.Pv := by
      have h1 : CFSG.Sporadic.ONOddCore.omegaP ≤ CFSG.ONSchreier.onT := by
        rw [← CFSG.Sporadic.ONOddCore.omegaT_map]
        exact Subgroup.map_subtype_le _
      exact h1 hx |> fun h => CFSG.ONSchreier.onT_le h
    have h2 : orderOf (⟨x, hxP⟩ : ↥CFSG.ONSchreier.Pv) = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_eq_prime hsq hx1
    exact h2 ▸ orderOf_dvd_natCard (⟨x, hxP⟩ : ↥CFSG.ONSchreier.Pv)
  have hcard : Nat.card (Blueprint.NativeSporadic.Carrier .ONan) =
      Nat.card ↥CFSG.ONSchreier.Pv :=
    Nat.card_congr CFSG.ONSchreier.onEquivPv.toEquiv
  rw [hcard]
  exact hPv

private theorem wGroup_seed
    {G : Type} [Group G] [Finite G] {t : G} {P W : Subgroup G} (hc : ONanWConfig G t P W) :
    ∃ A : Subgroup G, A ≤ centralizer ({t} : Set G) ∧ IsElemTwo A ∧ Nat.card A = 16 ∧
      wGroup A = W := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hON : IsSporadic (↥P ⧸ pPrimeCore 2 ↥P) .ONan := hc.isSporadic_pPrimeCore
  obtain ⟨R₀⟩ := Sylow.nonempty (p := 2) (G := ↥P)
  let R : Subgroup G := (R₀ : Subgroup ↥P).map P.subtype
  have hR : IsSylowTwoIn R P := ⟨map_subtype_le _, R₀, by rw [subgroupOf_map_subtype_eq]⟩
  obtain ⟨hEe, hEcard⟩ := omSub_sqSub_of_on hON hR
  have hEP : omSub (sqSub R) ≤ P := (omSub_sqSub_le R).trans hR.1
  obtain ⟨hAe, hAcard⟩ :=
    card_sup_zpowers_of_on hc.order_two hc.le_centralizer hON hEP hEe hEcard
  have hAle : omSub (sqSub R) ⊔ zpowers t ≤ centralizer ({t} : Set G) := by
    refine sup_le (hEP.trans hc.le_centralizer) (zpowers_le.mpr ?_)
    rw [mem_centralizer_singleton_iff]
  exact ⟨omSub (sqSub R) ⊔ zpowers t, hAle, hAe, hAcard, hc.wGroup_eq _ hAle hAe (by omega)⟩


private theorem exists_sylow_twoIn_normalizer_t {G : Type} [Group G] [Finite G] {t : G}
    {W M : Subgroup G} (_hM : M = normalizer (W : Set G)) (htM : t ∈ M) (ht2 : orderOf t = 2) :
    ∃ S : Subgroup G, IsSylowTwoIn S M ∧ t ∈ S := by
  have hz : IsPGroup 2 ↥(zpowers (⟨t, htM⟩ : ↥M)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, ht2, pow_one]
  obtain ⟨Q, hQ⟩ := hz.exists_le_sylow
  exact ⟨(Q : Subgroup ↥M).map M.subtype, ⟨map_subtype_le _, Q,
      (Subgroup.comap_map_eq_self_of_injective M.subtype_injective _).symm⟩,
    ⟨⟨t, htM⟩, hQ (mem_zpowers (⟨t, htM⟩ : ↥M)), rfl⟩⟩

private theorem component_pair_facts {X : Type} [Group X] [Finite X] {L : Subgroup X} {tb : X}
    (hL : IsComponent L) (hZ : Subgroup.center ↥L = ⊥)
    (hne : L.map (MulAut.conj tb).toMonoidHom ≠ L)
    (hpair : ∀ x : X, L.map (MulAut.conj x).toMonoidHom = L ∨
      L.map (MulAut.conj x).toMonoidHom = L.map (MulAut.conj tb).toMonoidHom) :
    IsComponent (L.map (MulAut.conj tb).toMonoidHom) ∧
      ⁅L, L.map (MulAut.conj tb).toMonoidHom⁆ = ⊥ ∧
      L ⊓ L.map (MulAut.conj tb).toMonoidHom = ⊥ ∧
      (L ⊔ L.map (MulAut.conj tb).toMonoidHom).Normal ∧
      (∀ x : X, (L ⊔ L.map (MulAut.conj tb).toMonoidHom).map (MulAut.conj x).toMonoidHom =
        L ⊔ L.map (MulAut.conj tb).toMonoidHom) := by
  classical
  have hcomp : IsComponent (L.map (MulAut.conj tb).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj tb) hL
  have hcomm : ⁅L, L.map (MulAut.conj tb).toMonoidHom⁆ = ⊥ := by
    rcases CFSG.LocalCores.distinct_components_commute hL hcomp with h | h
    · exact absurd h.symm hne
    · exact h
  have hdisj : L ⊓ L.map (MulAut.conj tb).toMonoidHom = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    have hcomm' : ⁅L.map (MulAut.conj tb).toMonoidHom, L⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]; exact hcomm
    have hcen : x ∈ Subgroup.centralizer (L : Set X) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm' hx2
    have hxZ : (⟨x, hx1⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hcen (y : X) y.2)
    rw [hZ] at hxZ
    have hxZ' : (⟨x, hx1⟩ : ↥L) = 1 := by simpa using hxZ
    have hx1' : x = 1 := congrArg Subtype.val hxZ'
    simp [hx1']
  have hcomp2 : ∀ x : X, (L.map (MulAut.conj tb).toMonoidHom).map
      (MulAut.conj x).toMonoidHom = L.map (MulAut.conj (x * tb)).toMonoidHom := by
    intro x
    rw [Subgroup.map_map]
    congr 1
    ext y
    simp [MulAut.conj_apply, mul_assoc]
  have himg : ∀ x : X,
      (L.map (MulAut.conj x).toMonoidHom = L ∧
        (L.map (MulAut.conj tb).toMonoidHom).map (MulAut.conj x).toMonoidHom =
          L.map (MulAut.conj tb).toMonoidHom) ∨
      (L.map (MulAut.conj x).toMonoidHom = L.map (MulAut.conj tb).toMonoidHom ∧
        (L.map (MulAut.conj tb).toMonoidHom).map (MulAut.conj x).toMonoidHom = L) := by
    intro x
    have himp : ∀ (hx : L.map (MulAut.conj x).toMonoidHom = L)
        (hy : (L.map (MulAut.conj tb).toMonoidHom).map (MulAut.conj x).toMonoidHom = L),
        False := by
      intro hx hy
      have hE : L.map (MulAut.conj x).toMonoidHom =
          (L.map (MulAut.conj tb).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
        rw [hx, hy]
      exact hne (Subgroup.map_injective (MulAut.conj x).injective hE.symm)
    have himp2 : ∀ (hx : L.map (MulAut.conj x).toMonoidHom =
          L.map (MulAut.conj tb).toMonoidHom)
        (hy : (L.map (MulAut.conj tb).toMonoidHom).map (MulAut.conj x).toMonoidHom =
          L.map (MulAut.conj tb).toMonoidHom), False := by
      intro hx hy
      have hE : L.map (MulAut.conj x).toMonoidHom =
          (L.map (MulAut.conj tb).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
        rw [hx, hy]
      exact hne (Subgroup.map_injective (MulAut.conj x).injective hE).symm
    rcases hpair x with hx | hx
    · rcases hpair (x * tb) with hy | hy
      · exact (himp hx (by rw [hcomp2 x]; exact hy)).elim
      · exact Or.inl ⟨hx, by rw [hcomp2 x]; exact hy⟩
    · rcases hpair (x * tb) with hy | hy
      · exact Or.inr ⟨hx, by rw [hcomp2 x]; exact hy⟩
      · exact (himp2 hx (by rw [hcomp2 x]; exact hy)).elim
  have hmap : ∀ x : X, (L ⊔ L.map (MulAut.conj tb).toMonoidHom).map
      (MulAut.conj x).toMonoidHom = L ⊔ L.map (MulAut.conj tb).toMonoidHom := by
    intro x
    rw [Subgroup.map_sup]
    rcases himg x with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, sup_comm]
  refine ⟨hcomp, hcomm, hdisj, ?_, hmap⟩
  refine Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr ?_)
  intro x _
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact hmap x

private def ONanPairSeed {G : Type} [Group G] [Finite G] (t : G) (_W M S A₀ : Subgroup G) : Prop :=
  IsSylowTwoIn S M ∧ t ∈ S ∧ A₀ ≤ S ∧ IsElemTwo A₀ ∧ 32 ≤ Nat.card A₀ ∧
    S ≤ normalizer (A₀ : Set G) ∧ IsThreeConnected S

private theorem onan_pair_sylow_fusion_of_seed
    {G : Type} [Group G] [Finite G] {t : G} {P W M : Subgroup G} (hc : ONanWConfig G t P W)
    (hM : M = normalizer (W : Set G)) {S A₀ : Subgroup G} (hseed : ONanPairSeed t W M S A₀) :
    Odd M.index ∧ ∀ g : G, g⁻¹ * t * g ∈ M → ∃ m ∈ M, g⁻¹ * t * g = m⁻¹ * t * m := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hSyl, htS, hA₀S, hA₀e, hA₀card, hSA₀, h3⟩ := hseed
  obtain ⟨A, hAC, hAe, hAcard, hWA⟩ := wGroup_seed hc
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [hc.order_two] at h
    simpa [pow_two] using h
  have hSylA : IsSylowTwoIn S (normalizer (wGroup A : Set G)) := by
    rw [hWA]
    exact hM ▸ hSyl
  have hB : GWTwoBalanced G := hc.gwTwoBalanced
  obtain ⟨Q, hQ⟩ := (sylow_and_fusion_of_threeConnected hB hAe (by omega) hSylA h3).1
  have hrank : ∀ b ∈ S, b * b = 1 → 3 ≤ pRank 2 ↥(S ⊓ centralizer ({b} : Set G)) := by
    intro b hbS hb2
    have hbN : b ∈ normalizer (A₀ : Set G) := hSA₀ hbS
    have hcard := GrSLit.card_le_card_inf_centralizer_sq hA₀e hbN hb2
    have hCe : IsElemTwo (A₀ ⊓ centralizer ({b} : Set G)) := hA₀e.mono inf_le_left
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hCe.isPGroup
    have h32 : 32 ≤ Nat.card ↥(A₀ ⊓ centralizer ({b} : Set G)) ^ 2 :=
      le_trans hA₀card hcard
    have h32' : 32 ≤ (2 ^ n) ^ 2 := hn ▸ h32
    have hn3 : 3 ≤ n := by
      by_contra h
      push Not at h
      interval_cases n <;> norm_num at h32'
    have hC8 : 8 ≤ Nat.card ↥(A₀ ⊓ centralizer ({b} : Set G)) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
        _ = Nat.card ↥(A₀ ⊓ centralizer ({b} : Set G)) := hn.symm
    refine le_trans (hCe.three_le_pRank hC8) (Sol78.pRank_le_of_le ?_)
    exact le_inf (inf_le_left.trans hA₀S) inf_le_right
  refine ⟨CFSG.ComponentClassification.AschbacherStrongEmbedding.Lemma34.odd_index_of_sylow_le
    (S := Q) (H := M) (by rw [hQ]; exact hSyl.1), ?_⟩
  intro g hg
  have hne1 : g⁻¹ * t * g ≠ 1 := by
    intro h
    have h1 : t = 1 := by
      have := congrArg (fun z => g * z * g⁻¹) h
      simpa [mul_assoc] using this
    have h2 := hc.order_two
    rw [h1, orderOf_one] at h2
    omega
  have hb2 : (g⁻¹ * t * g) * (g⁻¹ * t * g) = 1 := by
    rw [show (g⁻¹ * t * g) * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g by group, ht2]
    group
  have hord : orderOf (g⁻¹ * t * g) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hb2) hne1
  have hQgrp : IsPGroup 2 ↥(zpowers (g⁻¹ * t * g)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hord, pow_one]
  have hzM : zpowers (g⁻¹ * t * g) ≤ M := zpowers_le.mpr hg
  obtain ⟨c, hcM, hcS⟩ := hSyl.exists_conj_le (H := M) hzM hQgrp
  have hcm : (g * c⁻¹)⁻¹ * t * (g * c⁻¹) ∈ S := by
    have h := hcS (g⁻¹ * t * g) (mem_zpowers (g⁻¹ * t * g))
    simpa [mul_assoc] using h
  have hb2' : ((g * c⁻¹)⁻¹ * t * (g * c⁻¹)) * ((g * c⁻¹)⁻¹ * t * (g * c⁻¹)) = 1 := by
    rw [show ((g * c⁻¹)⁻¹ * t * (g * c⁻¹)) * ((g * c⁻¹)⁻¹ * t * (g * c⁻¹)) =
      (g * c⁻¹)⁻¹ * (t * t) * (g * c⁻¹) by group, ht2]
    group
  obtain ⟨m, hm, hmeq⟩ := conj_eq_of_threeConnected hB hAe (by omega) hSylA h3 t htS
    (g * c⁻¹) hcm (hrank t htS ht2) (hrank _ hcm hb2')
  have hmW : m ∈ normalizer (W : Set G) := hWA ▸ hm
  have hmM : m ∈ M := hM.symm ▸ hmW
  refine ⟨m * c, M.mul_mem hmM hcM, ?_⟩
  rw [show (m * c)⁻¹ * t * (m * c) = c⁻¹ * (m⁻¹ * t * m) * c by group, ← hmeq]
  group


private theorem pPrimeCore_eq_bot_of_component_on
    {X : Type} [Group X] [Finite X] {L : Subgroup X}
    (hL : IsComponent L) (hZ : Subgroup.center ↥L = ⊥) (hLON : IsSporadic ↥L .ONan) :
    pPrimeCore 2 ↥L = ⊥ := by
  have hdvd : 2 ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) := by
    rw [hZ]
    have h1 : Nat.card (↥L ⧸ (⊥ : Subgroup ↥L)) = Nat.card ↥L :=
      Nat.card_congr (QuotientGroup.quotientBot (G := ↥L)).toEquiv
    rw [h1]
    obtain ⟨e⟩ := hLON
    have h2 : Nat.card ↥L = Nat.card (Blueprint.NativeSporadic.Carrier .ONan) :=
      Nat.card_congr e.toEquiv
    rw [h2]
    exact two_dvd_card_carrier_on
  have hN : pPrimeCore 2 ↥(Subgroup.center ↥L) = ⊥ := by
    rw [hZ]
    refine le_antisymm ?_ bot_le
    intro x hx
    have hx1 : x = 1 := Subsingleton.elim x 1
    rw [hx1]
    exact Subgroup.one_mem _
  exact CFSG.pPrimeCore_eq_bot_of_normal_quotient_simple (p := 2) Nat.prime_two hN hL.1.2.1 hdvd

private theorem isSporadic_quot_pPrimeCore_of_component_on
    {X : Type} [Group X] [Finite X] {L : Subgroup X}
    (hL : IsComponent L) (hZ : Subgroup.center ↥L = ⊥) (hLON : IsSporadic ↥L .ONan) :
    IsSporadic (↥L ⧸ pPrimeCore 2 ↥L) .ONan := by
  have hO : pPrimeCore 2 ↥L = ⊥ := pPrimeCore_eq_bot_of_component_on hL hZ hLON
  obtain ⟨e⟩ := hLON
  refine ⟨(QuotientGroup.quotientMulEquivOfEq hO).trans
    ((QuotientGroup.quotientBot (G := ↥L)).trans e)⟩

private theorem isSylowTwoIn_inf_oddIn_eq_bot {G : Type} [Group G] [Finite G]
    {W M S : Subgroup G} (_hM : M = normalizer (W : Set G)) (hSyl : IsSylowTwoIn S M) :
    S ⊓ oddIn M = ⊥ := by
  have hOodd : Nat.Coprime 2 (Nat.card (oddIn M)) := by
    rw [oddIn, Subgroup.card_map_of_injective M.subtype_injective]
    exact CFSG.coprime_card_pPrimeCore 2 ↥M
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxS, hxO⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨n, hn⟩ := hSyl.isPGroup ⟨x, hxS⟩
  have h1 : orderOf x ∣ 2 ^ n := by
    apply orderOf_dvd_of_pow_eq_one
    simpa using congrArg Subtype.val hn
  have h2 : orderOf x ∣ Nat.card (oddIn M) := Subgroup.orderOf_dvd_natCard _ hxO
  have h3 : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left n hOodd) h1 h2
  simpa using orderOf_eq_one_iff.mp h3


private theorem isSylowTwoIn_inf_of_normal_subgroup {Y : Type} [Group Y] [Finite Y]
    {Q : Sylow 2 Y} {H : Subgroup Y} [H.Normal] : IsSylowTwoIn ((Q : Subgroup Y) ⊓ H) H := by
  refine ⟨inf_le_right, QuasiDihedralFusion.sylowInfNormal Q H, ?_⟩
  rw [QuasiDihedralFusion.sylowInfNormal_coe]
  ext x
  simp [Subgroup.mem_subgroupOf]


private theorem pair_component_sylows {X : Type} [Group X] [Finite X] {L : Subgroup X} {tb : X}
    (hL : IsComponent L) (hZ : Subgroup.center ↥L = ⊥)
    (hne : L.map (MulAut.conj tb).toMonoidHom ≠ L)
    (hpair : ∀ x : X, L.map (MulAut.conj x).toMonoidHom = L ∨
      L.map (MulAut.conj x).toMonoidHom = L.map (MulAut.conj tb).toMonoidHom)
    (Q : Sylow 2 X) :
    IsSylowTwoIn ((Q : Subgroup X) ⊓ (L ⊔ L.map (MulAut.conj tb).toMonoidHom))
        (L ⊔ L.map (MulAut.conj tb).toMonoidHom) ∧
      IsSylowTwoIn ((Q : Subgroup X) ⊓ L) L ∧
      IsSylowTwoIn ((Q : Subgroup X) ⊓ L.map (MulAut.conj tb).toMonoidHom)
        (L.map (MulAut.conj tb).toMonoidHom) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hL2, hcomm, hdisj, hHnorm, hHmap⟩ := component_pair_facts hL hZ hne hpair
  let H : Subgroup X := L ⊔ L.map (MulAut.conj tb).toMonoidHom
  have : H.Normal := hHnorm
  have hcent : L.map (MulAut.conj tb).toMonoidHom ≤ Subgroup.centralizer (L : Set X) := by
    have h' : ⁅L.map (MulAut.conj tb).toMonoidHom, L⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]; exact hcomm
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h'
  have hcent' : L ≤ Subgroup.centralizer (L.map (MulAut.conj tb).toMonoidHom : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hHnormL : H ≤ Subgroup.normalizer (L : Set X) :=
    sup_le Subgroup.le_normalizer (hcent.trans (Subgroup.centralizer_le_normalizer (L : Set X)))
  have hHnormL₂ : H ≤ Subgroup.normalizer (L.map (MulAut.conj tb).toMonoidHom : Set X) :=
    sup_le (hcent'.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
  have hHinf : IsSylowTwoIn ((Q : Subgroup X) ⊓ H) H :=
    isSylowTwoIn_inf_of_normal_subgroup (Q := Q) (H := H)
  have hLinf : IsSylowTwoIn (((Q : Subgroup X) ⊓ H) ⊓ L) L :=
    CFSG.ComponentClassification.TBLit.L34FU.isSylowTwoIn_inf hHinf le_sup_left hHnormL
  have hL2inf : IsSylowTwoIn (((Q : Subgroup X) ⊓ H) ⊓ L.map (MulAut.conj tb).toMonoidHom)
      (L.map (MulAut.conj tb).toMonoidHom) :=
    CFSG.ComponentClassification.TBLit.L34FU.isSylowTwoIn_inf hHinf le_sup_right hHnormL₂
  have h1 : ((Q : Subgroup X) ⊓ H) ⊓ L = (Q : Subgroup X) ⊓ L := by
    rw [inf_assoc]
    congr 1
    exact inf_eq_right.mpr (le_sup_left : L ≤ H)
  have h2 : ((Q : Subgroup X) ⊓ H) ⊓ L.map (MulAut.conj tb).toMonoidHom =
      (Q : Subgroup X) ⊓ L.map (MulAut.conj tb).toMonoidHom := by
    rw [inf_assoc]
    congr 1
    exact inf_eq_right.mpr (le_sup_right : L.map (MulAut.conj tb).toMonoidHom ≤ H)
  exact ⟨hHinf, h1 ▸ hLinf, h2 ▸ hL2inf⟩


private theorem pair_eights
    {X : Type} [Group X] [Finite X] {L : Subgroup X} {tb : X}
    (hL : IsComponent L) (hZ : Subgroup.center ↥L = ⊥) (hLON : IsSporadic ↥L .ONan)
    (hne : L.map (MulAut.conj tb).toMonoidHom ≠ L)
    (hpair : ∀ x : X, L.map (MulAut.conj x).toMonoidHom = L ∨
      L.map (MulAut.conj x).toMonoidHom = L.map (MulAut.conj tb).toMonoidHom)
    (Q : Sylow 2 X) :
    ∃ E₁ E₂ : Subgroup X, E₁ ≤ (Q : Subgroup X) ∧ E₂ ≤ (Q : Subgroup X) ∧
      IsElemTwo (E₁ ⊔ E₂) ∧ Nat.card ↥(E₁ ⊔ E₂) = 64 ∧
      (∀ x ∈ (Q : Subgroup X), (E₁ ⊔ E₂).map (MulAut.conj x).toMonoidHom = E₁ ⊔ E₂) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hL2, hcomm, hdisj, hHnorm, hHmap⟩ := component_pair_facts hL hZ hne hpair
  obtain ⟨hHinf, hR₁, hR₂⟩ := pair_component_sylows hL hZ hne hpair Q
  have hON₁ : IsSporadic (↥L ⧸ pPrimeCore 2 ↥L) .ONan :=
    isSporadic_quot_pPrimeCore_of_component_on hL hZ hLON
  have hON₂ : IsSporadic (↥(L.map (MulAut.conj tb).toMonoidHom) ⧸
      pPrimeCore 2 ↥(L.map (MulAut.conj tb).toMonoidHom)) .ONan := by
    obtain ⟨e⟩ := hON₁
    let σ := Subgroup.equivMapOfInjective L (MulAut.conj tb).toMonoidHom
      (MulAut.conj tb).injective
    refine ⟨(QuotientGroup.congr (pPrimeCore 2 ↥(L.map (MulAut.conj tb).toMonoidHom))
      (pPrimeCore 2 ↥L) σ.symm ?_).trans e⟩
    exact CFSG.pPrimeCore_map_iso 2 σ.symm
  obtain ⟨hE₁e, hE₁c⟩ := omSub_sqSub_of_on hON₁ hR₁
  obtain ⟨hE₂e, hE₂c⟩ := omSub_sqSub_of_on hON₂ hR₂
  have hE₁le : omSub (sqSub ((Q : Subgroup X) ⊓ L)) ≤ (Q : Subgroup X) :=
    (omSub_sqSub_le _).trans inf_le_left
  have hE₂le : omSub (sqSub ((Q : Subgroup X) ⊓ L.map (MulAut.conj tb).toMonoidHom)) ≤
      (Q : Subgroup X) :=
    (omSub_sqSub_le _).trans inf_le_left
  have hE₁L : omSub (sqSub ((Q : Subgroup X) ⊓ L)) ≤ L :=
    (omSub_sqSub_le _).trans inf_le_right
  have hE₂L : omSub (sqSub ((Q : Subgroup X) ⊓ L.map (MulAut.conj tb).toMonoidHom)) ≤
      L.map (MulAut.conj tb).toMonoidHom :=
    (omSub_sqSub_le _).trans inf_le_right
  have hcommE : ∀ x ∈ omSub (sqSub ((Q : Subgroup X) ⊓ L)),
      ∀ y ∈ omSub (sqSub ((Q : Subgroup X) ⊓ L.map (MulAut.conj tb).toMonoidHom)),
      x * y = y * x := by
    intro x hx y hy
    have hxL := hE₁L hx
    have hyL := hE₂L hy
    have hcen : L ≤ Subgroup.centralizer (L.map (MulAut.conj tb).toMonoidHom : Set X) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    exact (Subgroup.mem_centralizer_iff.mp (hcen hxL) y hyL).symm
  have hinter : omSub (sqSub ((Q : Subgroup X) ⊓ L)) ⊓
      omSub (sqSub ((Q : Subgroup X) ⊓ L.map (MulAut.conj tb).toMonoidHom)) = ⊥ := by
    rw [eq_bot_iff]
    refine le_trans (inf_le_inf (omSub_sqSub_le _) (omSub_sqSub_le _)) ?_
    rw [← hdisj]
    exact inf_le_inf inf_le_right inf_le_right
  have hsupE : IsElemTwo (omSub (sqSub ((Q : Subgroup X) ⊓ L)) ⊔
      omSub (sqSub ((Q : Subgroup X) ⊓ L.map (MulAut.conj tb).toMonoidHom))) :=
    IsElemTwo.sup hE₁e hE₂e hcommE
  have hcomp2 : ∀ x : X, (L.map (MulAut.conj tb).toMonoidHom).map
      (MulAut.conj x).toMonoidHom = L.map (MulAut.conj (x * tb)).toMonoidHom := by
    intro x
    rw [Subgroup.map_map]
    congr 1
    ext y
    simp [MulAut.conj_apply, mul_assoc]
  have hcardE : Nat.card ↥(omSub (sqSub ((Q : Subgroup X) ⊓ L)) ⊔
      omSub (sqSub ((Q : Subgroup X) ⊓ L.map (MulAut.conj tb).toMonoidHom))) = 64 := by
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (H := X)
      (L := omSub (sqSub ((Q : Subgroup X) ⊓ L)))
      (R := omSub (sqSub ((Q : Subgroup X) ⊓ L.map (MulAut.conj tb).toMonoidHom)))
      hcommE).1
    rw [hinter, Subgroup.card_bot, mul_one, hE₁c, hE₂c] at h
    exact h
  have hinv : ∀ x ∈ (Q : Subgroup X), (omSub (sqSub ((Q : Subgroup X) ⊓ L)) ⊔
      omSub (sqSub ((Q : Subgroup X) ⊓ L.map (MulAut.conj tb).toMonoidHom))).map
      (MulAut.conj x).toMonoidHom = omSub (sqSub ((Q : Subgroup X) ⊓ L)) ⊔
      omSub (sqSub ((Q : Subgroup X) ⊓ L.map (MulAut.conj tb).toMonoidHom)) := by
    intro x hxQ
    have hQx : (Q : Subgroup X).map (MulAut.conj x).toMonoidHom = Q :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hxQ)
    have hx1 : (omSub (sqSub ((Q : Subgroup X) ⊓ L))).map (MulAut.conj x).toMonoidHom =
        omSub (sqSub ((Q : Subgroup X) ⊓ L.map (MulAut.conj x).toMonoidHom)) := by
      rw [omSub_map _ (MulAut.conj x).injective, sqSub_map,
        Subgroup.map_inf _ _ _ (MulAut.conj x).injective, hQx]
    have hx2 : (omSub (sqSub ((Q : Subgroup X) ⊓
        L.map (MulAut.conj tb).toMonoidHom))).map (MulAut.conj x).toMonoidHom =
        omSub (sqSub ((Q : Subgroup X) ⊓ L.map (MulAut.conj (x * tb)).toMonoidHom)) := by
      rw [omSub_map _ (MulAut.conj x).injective, sqSub_map,
        Subgroup.map_inf _ _ _ (MulAut.conj x).injective, hQx, hcomp2 x]
    rw [Subgroup.map_sup, hx1, hx2]
    rcases hpair x with h1 | h1 <;> rcases hpair (x * tb) with h2 | h2
    · exfalso
      have hE : L.map (MulAut.conj x).toMonoidHom =
          (L.map (MulAut.conj tb).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
        rw [hcomp2 x, h1, h2]
      exact hne (Subgroup.map_injective (MulAut.conj x).injective hE).symm
    · rw [h1, h2]
    · rw [h1, h2, sup_comm]
    · exfalso
      have hE : L.map (MulAut.conj x).toMonoidHom =
          (L.map (MulAut.conj tb).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
        rw [hcomp2 x, h1, h2]
      exact hne (Subgroup.map_injective (MulAut.conj x).injective hE).symm
  exact ⟨_, _, hE₁le, hE₂le, hsupE, hcardE, hinv⟩


private theorem exists_pair_seed
    {G : Type} [Group G] [Finite G] {t : G} {P W M : Subgroup G} (hc : ONanWConfig G t P W)
    (hM : M = normalizer (W : Set G)) (htM : t ∈ M)
    {L : Subgroup (↥M ⧸ pPrimeCore 2 ↥M)} (hL : IsComponent L)
    (hZ : Subgroup.center ↥L = ⊥) (hLON : IsSporadic ↥L .ONan)
    (hne : L.map (MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨t, htM⟩)).toMonoidHom ≠ L)
    (hpair : ∀ x : ↥M ⧸ pPrimeCore 2 ↥M,
      L.map (MulAut.conj x).toMonoidHom = L ∨
      L.map (MulAut.conj x).toMonoidHom =
        L.map (MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨t, htM⟩)).toMonoidHom) :
    ∃ S A₀ : Subgroup G, ONanPairSeed t W M S A₀ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hSyl, htS⟩ := exists_sylow_twoIn_normalizer_t hM htM hc.order_two
  obtain ⟨P_M, hP_M⟩ := hSyl.2
  let π : ↥M →* (↥M ⧸ pPrimeCore 2 ↥M) := QuotientGroup.mk' (pPrimeCore 2 ↥M)
  let Q : Sylow 2 (↥M ⧸ pPrimeCore 2 ↥M) :=
    P_M.mapSurjective (f := π) (QuotientGroup.mk'_surjective _)
  have hQcoe : (Q : Subgroup (↥M ⧸ pPrimeCore 2 ↥M)) = (S.subgroupOf M).map π := by
    rw [Sylow.coe_mapSurjective]
    exact congrArg (fun K => K.map π) hP_M
  obtain ⟨E₁, E₂, hE₁Q, hE₂Q, hsupE, hcardE, hinv⟩ :=
    pair_eights hL hZ hLON hne hpair Q
  have hPbarQ : E₁ ⊔ E₂ ≤ (Q : Subgroup (↥M ⧸ pPrimeCore 2 ↥M)) := sup_le hE₁Q hE₂Q
  have hS'O : S.subgroupOf M ⊓ pPrimeCore 2 ↥M = ⊥ := by
    have h := isSylowTwoIn_inf_oddIn_eq_bot hM hSyl
    have hmap : (S.subgroupOf M ⊓ pPrimeCore 2 ↥M).map M.subtype = S ⊓ oddIn M := by
      rw [Subgroup.map_inf _ _ _ M.subtype_injective, oddIn,
        Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hSyl.1]
    exact Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective |>.mp (by rw [hmap, h])
  have hinjS : Function.Injective (π.comp (S.subgroupOf M).subtype) := by
    intro x y hxy
    have hxy' : π (x : ↥M) = π (y : ↥M) := hxy
    have h1 : ((x : ↥M)⁻¹ * (y : ↥M)) ∈ pPrimeCore 2 ↥M := by
      have h2 : QuotientGroup.mk' (pPrimeCore 2 ↥M) ((x : ↥M)⁻¹ * (y : ↥M)) = 1 := by
        have h3 : π ((x : ↥M)⁻¹ * (y : ↥M)) = 1 := by
          rw [map_mul, map_inv, hxy', inv_mul_cancel]
        exact h3
      exact (QuotientGroup.eq_one_iff _).mp h2
    have h3 : ((x : ↥M)⁻¹ * (y : ↥M)) ∈ S.subgroupOf M :=
      (S.subgroupOf M).mul_mem ((S.subgroupOf M).inv_mem x.2) y.2
    have h4 : ((x : ↥M)⁻¹ * (y : ↥M)) = 1 := by
      have h5 : ((x : ↥M)⁻¹ * (y : ↥M)) ∈ S.subgroupOf M ⊓ pPrimeCore 2 ↥M :=
        Subgroup.mem_inf.mpr ⟨h3, h1⟩
      rwa [hS'O, Subgroup.mem_bot] at h5
    exact Subtype.ext (inv_mul_eq_one.mp h4)
  have hA₀'e : IsElemTwo ((E₁ ⊔ E₂).comap π ⊓ S.subgroupOf M) := by
    constructor
    · intro x hx y hy
      have hxP : π x ∈ E₁ ⊔ E₂ := Subgroup.mem_comap.mp (Subgroup.mem_inf.mp hx).1
      have hyP : π y ∈ E₁ ⊔ E₂ := Subgroup.mem_comap.mp (Subgroup.mem_inf.mp hy).1
      have hxs : x ∈ S.subgroupOf M := (Subgroup.mem_inf.mp hx).2
      have hys : y ∈ S.subgroupOf M := (Subgroup.mem_inf.mp hy).2
      have hmul : π (x * y) = π (y * x) := by
        rw [map_mul, map_mul, hsupE.1 (π x) hxP (π y) hyP]
      have hxy := hinjS (a₁ := ⟨x * y, (S.subgroupOf M).mul_mem hxs hys⟩)
        (a₂ := ⟨y * x, (S.subgroupOf M).mul_mem hys hxs⟩) hmul
      exact Subtype.ext_iff.mp hxy
    · intro x hx
      have hxP : π x ∈ E₁ ⊔ E₂ := Subgroup.mem_comap.mp (Subgroup.mem_inf.mp hx).1
      have hxs : x ∈ S.subgroupOf M := (Subgroup.mem_inf.mp hx).2
      have hmul : π (x * x) = π 1 := by
        simp [map_mul, hsupE.2 (π x) hxP]
      have hxx := hinjS (a₁ := ⟨x * x, (S.subgroupOf M).mul_mem hxs hxs⟩)
        (a₂ := ⟨1, (S.subgroupOf M).one_mem⟩) hmul
      exact Subtype.ext_iff.mp hxx
  have hex : ∀ p : ↥(E₁ ⊔ E₂), ∃ s : ↥M, s ∈ S.subgroupOf M ∧ π s = (p : ↥M ⧸ pPrimeCore 2 ↥M) := by
    intro p
    have hp : (p : ↥M ⧸ pPrimeCore 2 ↥M) ∈ (Q : Subgroup (↥M ⧸ pPrimeCore 2 ↥M)) :=
      hPbarQ p.2
    rw [hQcoe] at hp
    obtain ⟨s, hs, hπ⟩ := Subgroup.mem_map.mp hp
    exact ⟨s, hs, hπ⟩
  have hcard_le : Nat.card ↥(E₁ ⊔ E₂) ≤
      Nat.card ↥((E₁ ⊔ E₂).comap π ⊓ S.subgroupOf M) := by
    have hinj : Function.Injective (fun p : ↥(E₁ ⊔ E₂) =>
        (⟨(hex p).choose, Subgroup.mem_inf.mpr ⟨by
          rw [Subgroup.mem_comap, (hex p).choose_spec.2]; exact p.2,
          (hex p).choose_spec.1⟩⟩ :
          ↥((E₁ ⊔ E₂).comap π ⊓ S.subgroupOf M))) := by
      intro p q hpq
      have hp : π ((hex p).choose) = (p : ↥M ⧸ pPrimeCore 2 ↥M) := (hex p).choose_spec.2
      have hq : π ((hex q).choose) = (q : ↥M ⧸ pPrimeCore 2 ↥M) := (hex q).choose_spec.2
      have hval : ((hex p).choose : ↥M) = ((hex q).choose : ↥M) := congrArg Subtype.val hpq
      have h1 : (p : ↥M ⧸ pPrimeCore 2 ↥M) = (q : ↥M ⧸ pPrimeCore 2 ↥M) := by
        rw [← hp, ← hq, congrArg (fun z : ↥M => π z) hval]
      exact Subtype.ext h1
    exact Nat.card_le_card_of_injective _ hinj
  have hA₀le : ((E₁ ⊔ E₂).comap π ⊓ S.subgroupOf M).map M.subtype ≤ S := by
    refine le_trans (Subgroup.map_mono inf_le_right) ?_
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hSyl.1]
  have hA₀e : IsElemTwo (((E₁ ⊔ E₂).comap π ⊓ S.subgroupOf M).map M.subtype) := by
    constructor
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simpa using congrArg M.subtype (hA₀'e.1 x hx y hy)
    · rintro _ ⟨x, hx, rfl⟩
      simpa using congrArg M.subtype (hA₀'e.2 x hx)
  have hA₀card : 32 ≤ Nat.card ↥(((E₁ ⊔ E₂).comap π ⊓ S.subgroupOf M).map M.subtype) := by
    rw [Subgroup.card_map_of_injective M.subtype_injective]
    omega
  have hconjcomap : ∀ (g : ↥M) (K : Subgroup (↥M ⧸ pPrimeCore 2 ↥M)),
      (K.comap π).map (MulAut.conj g).toMonoidHom =
        (K.map (MulAut.conj (π g)).toMonoidHom).comap π := by
    intro g K
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      rw [Subgroup.mem_comap] at hy ⊢
      rw [← hyx]
      have hπ : π ((MulAut.conj g).toMonoidHom y) = (MulAut.conj (π g)).toMonoidHom (π y) := by
        simp [MulAut.conj_apply]
      rw [hπ]
      exact Subgroup.mem_map.mpr ⟨π y, hy, rfl⟩
    · intro hx
      rw [Subgroup.mem_comap] at hx
      obtain ⟨k, hk, hkπ⟩ := Subgroup.mem_map.mp hx
      refine Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, ?_, ?_⟩
      · rw [Subgroup.mem_comap]
        have hπ : π (g⁻¹ * x * g) = (π g)⁻¹ * π x * π g := by
          rw [map_mul, map_mul, map_inv]
        have hconj : (MulAut.conj (π g)).toMonoidHom k = π g * k * (π g)⁻¹ := by
          simp [MulAut.conj_apply]
        rw [hπ, ← hkπ, hconj,
          show (π g)⁻¹ * (π g * k * (π g)⁻¹) * (π g) = k by group]
        exact hk
      · show MulAut.conj g (g⁻¹ * x * g) = x
        rw [MulAut.conj_apply]; group
  have hA₀norm : S ≤ Subgroup.normalizer
      (((E₁ ⊔ E₂).comap π ⊓ S.subgroupOf M).map M.subtype : Set G) := by
    intro s hs
    have hsM : s ∈ M := hSyl.1 hs
    have hstep : ∀ g ∈ S.subgroupOf M,
        ((E₁ ⊔ E₂).comap π ⊓ S.subgroupOf M).map (MulAut.conj g).toMonoidHom =
          (E₁ ⊔ E₂).comap π ⊓ S.subgroupOf M := by
      intro g hg
      have hπg : π g ∈ (Q : Subgroup (↥M ⧸ pPrimeCore 2 ↥M)) := by
        rw [hQcoe]; exact Subgroup.mem_map.mpr ⟨g, hg, rfl⟩
      have hS'inv : (S.subgroupOf M).map (MulAut.conj g).toMonoidHom = S.subgroupOf M :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hg)
      rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, hconjcomap g (E₁ ⊔ E₂),
        hinv (π g) hπg, hS'inv]
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hg : (⟨s, hsM⟩ : ↥M) ∈ S.subgroupOf M := hs
    have hcomp : (MulAut.conj s).toMonoidHom.comp M.subtype =
        M.subtype.comp (MulAut.conj (⟨s, hsM⟩ : ↥M)).toMonoidHom := by
      ext y
      rfl
    calc (((E₁ ⊔ E₂).comap π ⊓ S.subgroupOf M).map M.subtype).map
          (MulAut.conj s).toMonoidHom
        = ((E₁ ⊔ E₂).comap π ⊓ S.subgroupOf M).map
            ((MulAut.conj s).toMonoidHom.comp M.subtype) := by
          rw [Subgroup.map_map]
      _ = ((E₁ ⊔ E₂).comap π ⊓ S.subgroupOf M).map
            (M.subtype.comp (MulAut.conj (⟨s, hsM⟩ : ↥M)).toMonoidHom) := by rw [hcomp]
      _ = (((E₁ ⊔ E₂).comap π ⊓ S.subgroupOf M).map
            (MulAut.conj (⟨s, hsM⟩ : ↥M)).toMonoidHom).map M.subtype := by
          rw [Subgroup.map_map]
      _ = ((E₁ ⊔ E₂).comap π ⊓ S.subgroupOf M).map M.subtype := by
          rw [hstep ⟨s, hsM⟩ hg]
  exact ⟨S, _, hSyl, htS, hA₀le, hA₀e, hA₀card, hA₀norm,
    isThreeConnected_of_normal hSyl.isPGroup hA₀le hA₀norm hA₀e hA₀card⟩

theorem onan_pair_sylow_fusion
    {G : Type} [Group G] [Finite G] {t : G} {P W M : Subgroup G} (hc : ONanWConfig G t P W)
    (hM : M = normalizer (W : Set G)) (htM : t ∈ M)
    {L : Subgroup (↥M ⧸ pPrimeCore 2 ↥M)} (hL : IsComponent L) (hZ : center ↥L = ⊥)
    (hLON : IsSporadic ↥L .ONan)
    (hne : L.map (MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨t, htM⟩)).toMonoidHom ≠ L)
    (hpair : ∀ x : ↥M ⧸ pPrimeCore 2 ↥M, L.map (MulAut.conj x).toMonoidHom = L ∨
      L.map (MulAut.conj x).toMonoidHom =
        L.map (MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨t, htM⟩)).toMonoidHom) :
    Odd M.index ∧ ∀ g : G, g⁻¹ * t * g ∈ M → ∃ m ∈ M, g⁻¹ * t * g = m⁻¹ * t * m := by
  obtain ⟨S, A₀, hseed⟩ := exists_pair_seed hc hM htM hL hZ hLON hne hpair
  exact onan_pair_sylow_fusion_of_seed hc hM hseed


end CFSG.ComponentClassification.GrSLit.L34Sec5S
