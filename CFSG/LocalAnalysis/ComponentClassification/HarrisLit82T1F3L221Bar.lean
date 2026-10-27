module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3Sat
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotIso
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T23Basic
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreQuotient
public import CFSG.GroupTheory.PCore.PrimeSetCore
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.ClassicalInvolution.Asc77.Lemma310
public import CFSG.ClassicalInvolution.Asc77.ThmEStatement
public import CFSG.ClassicalInvolution.Asc77.WP1Section18
public import CFSG.ClassicalInvolution.Asc77.WP1Section6
public import CFSG.ClassicalInvolution.Balance.QNineFuzzyFree
public import CFSG.ClassicalInvolution.Balance.Theorem5Models
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Conj
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Roots
public import CFSG.ClassicalInvolution.ModelFacts.Orth15D4Ord
public import CFSG.ClassicalInvolution.ModelFacts.Orth15Std
public import CFSG.ClassicalInvolution.Q3.Step
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Steinberg.CentralExt.PSL2Multiplier
public import CFSG.LocalAnalysis.ComponentClassification.CatalogSchreierCases
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesC
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35LieHalf
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3Props
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T23Defs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36SporMult
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModels
public import CFSG.LocalAnalysis.ComponentClassification.OddSelector
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdFamilies
public import CFSG.Monster.B.TwoA.Base.FourNorm
public import CFSG.Monster.SteinbergMY443SimpleIsomorphism
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.Sporadic.HeldB.Common
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Sporadic.SuzOddCore.SmallActionData
public import CFSG.Walter.J1
public import CFSG.YGroups.DCE.MaximalB
public import CFSG.YGroups.Y443.Native.Parabolic2CheckB
public import CFSG.YGroups.Y443.Native.Parabolic2CheckW
public import Certificates.Certificate10025
public import Certificates.Certificate8171
public import Certificates.Kernel.J4Count.FixC
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase
public import Certificates.Kernel.SporSch.J4S.NoCP

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace F3L221

theorem map_pPrimeCore_of_surjective {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (f : A →* B) (hf : Function.Surjective f) (hker : ¬ 2 ∣ Nat.card f.ker) :
    (pPrimeCore 2 A).map f = pPrimeCore 2 B := by
  rw [← GSThmB.OddQuot.comap_pPrimeCore_of_surjective f hf hker]
  exact map_comap_eq_self_of_surjective hf _

variable {X : Type} [Group X] [Finite X]

theorem map_pPrimeCore_eq_inf {L : Subgroup X} (hL : L.IsSubnormal) :
    (pPrimeCore 2 ↥L).map L.subtype = L ⊓ pPrimeCore 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key := CFSG.LocalCores.prime_set_core_subnormal_intersection
    {q : Nat.Primes | q.val ≠ 2} hL
  rwa [← pPrimeCore_eq_piCore, ← pPrimeCore_eq_piCore] at key

theorem mem_of_isSubnormal_of_odd_index {Y : Type*} [Group Y] [Finite Y] {H : Subgroup Y}
    (hH : H.IsSubnormal) {y : Y} {n : ℕ} (hy : y ^ 2 ^ n = 1) : ¬ 2 ∣ H.index → y ∈ H := by
  induction hH with
  | top => exact fun _ => mem_top y
  | step H K hHK hK hHn ih =>
    intro hodd
    have hyK : y ∈ K := ih fun h2 => hodd (h2.trans (Subgroup.index_dvd_of_le hHK))
    set y' : ↥K := ⟨y, hyK⟩ with hy'
    have hrel : ¬ 2 ∣ Nat.card (↥K ⧸ H.subgroupOf K) := by
      intro h2
      apply hodd
      rw [← Subgroup.relIndex_mul_index hHK]
      exact Dvd.dvd.mul_right h2 _
    have h1 : (QuotientGroup.mk y' : ↥K ⧸ H.subgroupOf K) ^ 2 ^ n = 1 := by
      rw [← QuotientGroup.mk_pow]
      have h3 : y' ^ 2 ^ n = 1 := Subtype.ext (by simpa [hy'] using hy)
      rw [h3, QuotientGroup.mk_one]
    have h2 := orderOf_dvd_natCard (QuotientGroup.mk y' : ↥K ⧸ H.subgroupOf K)
    have h3 := orderOf_dvd_of_pow_eq_one h1
    have hcop : Nat.Coprime (2 ^ n) (Nat.card (↥K ⧸ H.subgroupOf K)) :=
      Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (by omega)))
    have h4 : orderOf (QuotientGroup.mk y' : ↥K ⧸ H.subgroupOf K) = 1 :=
      Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd h3 h2)
    rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h4
    exact h4

theorem mem_of_mem_sup_pPrimeCore {L : Subgroup X} (hL : L.IsSubnormal) {y : X}
    (hy : y ∈ L ⊔ pPrimeCore 2 X) {n : ℕ} (hyn : y ^ 2 ^ n = 1) : y ∈ L := by
  set O := pPrimeCore 2 X with hO
  set B := L ⊔ O with hB
  have hLB : L ≤ B := le_sup_left
  have hOB : O ≤ B := le_sup_right
  have e1 := Subgroup.relIndex_mul_card (H := L) (K := B)
  rw [inf_eq_left.mpr hLB] at e1
  have e2 := Subgroup.relIndex_mul_card (H := O) (K := B)
  rw [inf_eq_left.mpr hOB] at e2
  have e3 : O.relIndex B = O.relIndex L := Subgroup.relIndex_sup_right L O
  have e4 := Subgroup.relIndex_mul_card (H := O) (K := L)
  have hpos : 0 < O.relIndex L := by
    rcases Nat.eq_zero_or_pos (O.relIndex L) with h0 | h0
    · rw [h0, zero_mul] at e4
      exact absurd e4.symm (Nat.card_pos (α := ↥L)).ne'
    · exact h0
  have e5 : L.relIndex B * Nat.card ↥(O ⊓ L) = Nat.card O := by
    have h1 : O.relIndex L * (L.relIndex B * Nat.card ↥(O ⊓ L)) = O.relIndex L * Nat.card O := by
      calc O.relIndex L * (L.relIndex B * Nat.card ↥(O ⊓ L))
          = L.relIndex B * (O.relIndex L * Nat.card ↥(O ⊓ L)) := by ring
        _ = L.relIndex B * Nat.card L := by rw [e4]
        _ = Nat.card B := e1
        _ = O.relIndex B * Nat.card O := e2.symm
        _ = O.relIndex L * Nat.card O := by rw [e3]
    exact Nat.eq_of_mul_eq_mul_left hpos h1
  have hodd : ¬ 2 ∣ (L.subgroupOf B).index := by
    intro h2
    have h3 : 2 ∣ Nat.card O := by
      rw [← e5]
      exact Dvd.dvd.mul_right h2 _
    exact (Nat.not_even_iff_odd.mpr (odd_card_pPrimeCore_two X)) (even_iff_two_dvd.mpr h3)
  have h := mem_of_isSubnormal_of_odd_index (H := L.subgroupOf B) hL.subgroupOf
    (y := (⟨y, hy⟩ : ↥B)) (n := n) (Subtype.ext (by simpa using hyn)) hodd
  exact h

theorem oPrimeResidualOf_eq_self {L : Subgroup X} (hL : Group.IsPerfect ↥L) :
    GH74.GLS.oPrimeResidualOf 2 L = L := by
  unfold GH74.GLS.oPrimeResidualOf
  rw [T23.oPrimeResidual_two_eq_top hL, ← MonoidHom.range_eq_map, range_subtype]

theorem conj_mem_of_commutator_mem {L : Subgroup X} (hL : L.IsSubnormal)
    (hLp : Group.IsPerfect ↥L) {k : X}
    (hk : ∀ l ∈ L, k * l * k⁻¹ * l⁻¹ ∈ pPrimeCore 2 X) : ∀ l ∈ L, k * l * k⁻¹ ∈ L := by
  intro l hl
  have hl' : l ∈ GH74.GLS.oPrimeResidualOf 2 L := by rw [oPrimeResidualOf_eq_self hLp]; exact hl
  obtain ⟨x, hx, rfl⟩ := hl'
  clear hl
  change k * (x : X) * k⁻¹ ∈ L
  unfold GH74.GLS.oPrimeResidual at hx
  induction hx using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨n, hn⟩ := hw
    have hwn : (w : X) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hmem : k * (w : X) * k⁻¹ ∈ L ⊔ pPrimeCore 2 X := by
      have h1 : k * (w : X) * k⁻¹ = (k * (w : X) * k⁻¹ * (w : X)⁻¹) * (w : X) := by group
      rw [h1]
      exact mul_mem (mem_sup_right (hk w w.2)) (mem_sup_left w.2)
    refine mem_of_mem_sup_pPrimeCore hL hmem (n := n) ?_
    rw [conj_pow, hwn, mul_one, mul_inv_cancel]
  | one => simp
  | mul a b _ _ ha hb =>
    have h1 : k * ((a * b : ↥L) : X) * k⁻¹ = (k * (a : X) * k⁻¹) * (k * (b : X) * k⁻¹) := by
      simp only [Subgroup.coe_mul]
      group
    rw [h1]
    exact mul_mem ha hb
  | inv a _ ha =>
    have h1 : k * ((a⁻¹ : ↥L) : X) * k⁻¹ = (k * (a : X) * k⁻¹)⁻¹ := by
      simp only [Subgroup.coe_inv]
      group
    rw [h1]
    exact inv_mem ha

theorem isTwoComponentIn_map_mk {L : Subgroup X} (hL : IsTwoComponentIn L ⊤) :
    IsTwoComponentIn (L.map (QuotientGroup.mk' (pPrimeCore 2 X))) ⊤ ∧
      Nonempty (↥L ⧸ pPrimeCore 2 ↥L ≃* ↥(L.map (QuotientGroup.mk' (pPrimeCore 2 X)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 X) with hπ
  have hLs : L.IsSubnormal := by
    have h := hL.2.1.map (f := (⊤ : Subgroup X).subtype) (fun x => ⟨⟨x, mem_top x⟩, rfl⟩)
    rwa [subgroupOf_map_subtype, inf_top_eq] at h
  set Lb := L.map π with hLb
  let ψ : ↥L →* ↥Lb := (π.comp L.subtype).codRestrict _ (fun x => mem_map_of_mem π x.2)
  have hψs : Function.Surjective ψ := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker : ψ.ker = pPrimeCore 2 ↥L := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have hx' : π (x : X) = 1 := congrArg Subtype.val hx
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at hx'
      have h1 : (x : X) ∈ (pPrimeCore 2 ↥L).map L.subtype := by
        rw [map_pPrimeCore_eq_inf hLs]
        exact mem_inf.mpr ⟨x.2, hx'⟩
      obtain ⟨y, hy, hyx⟩ := h1
      rw [show x = y from Subtype.ext hyx.symm]
      exact hy
    · intro hx
      apply Subtype.ext
      change π (x : X) = 1
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      have h1 : (x : X) ∈ (pPrimeCore 2 ↥L).map L.subtype := ⟨x, hx, rfl⟩
      rw [map_pPrimeCore_eq_inf hLs] at h1
      exact (mem_inf.mp h1).2
  let e : ↥L ⧸ pPrimeCore 2 ↥L ≃* ↥Lb :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)
  have hq : IsTwoQuasisimple (↥L ⧸ pPrimeCore 2 ↥L) := by
    have : Group.IsPerfect ↥L := hL.2.2.1
    refine ⟨Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _), ?_⟩
    have hbot : pPrimeCore 2 (↥L ⧸ pPrimeCore 2 ↥L) = ⊥ := pPrimeCore_quotient_eq_bot Nat.prime_two
    exact LocalCores.isQuasisimple_of_mulEquiv
      ((QuotientGroup.quotientBot).symm.trans (QuotientGroup.quotientMulEquivOfEq hbot.symm))
      hL.2.2.2
  refine ⟨⟨le_top, (hLs.map (QuotientGroup.mk'_surjective _)).subgroupOf,
    isTwoQuasisimple_of_mulEquiv e hq⟩, ⟨e⟩⟩

theorem isSolvableTwoComponentIn_map_mk {z : X} (hz : orderOf z = 2) {K : Subgroup X}
    (hK : IsSolvableTwoComponentIn K (centralizer {z})) :
    IsSolvableTwoComponentIn (K.map (QuotientGroup.mk' (pPrimeCore 2 X)))
      (centralizer {(QuotientGroup.mk z : X ⧸ pPrimeCore 2 X)}) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 X) with hπ
  set C := centralizer ({z} : Set X) with hC
  set C' := centralizer ({(QuotientGroup.mk z : X ⧸ pPrimeCore 2 X)} :
    Set (X ⧸ pPrimeCore 2 X)) with hC'
  have hzz : z * z = 1 := by rw [← sq, ← hz, pow_orderOf_eq_one]
  have hCmap : C.map π = C' := map_centralizer_eq (odd_card_pPrimeCore_two X) hzz
  have hodd2 : ¬ 2 ∣ Nat.card (pPrimeCore 2 X) := fun h2 =>
    (Nat.not_even_iff_odd.mpr (odd_card_pPrimeCore_two X)) (even_iff_two_dvd.mpr h2)
  let φ : ↥C →* ↥C' := (π.comp C.subtype).codRestrict _ (fun x => hCmap ▸ mem_map_of_mem π x.2)
  have hφs : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    rw [← hCmap] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  set Kb := K.map π with hKb
  let ψ : ↥K →* ↥Kb := (π.comp K.subtype).codRestrict _ (fun x => mem_map_of_mem π x.2)
  have hψs : Function.Surjective ψ := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hkerodd : ∀ {A : Subgroup X} (f : ↥A →* X ⧸ pPrimeCore 2 X), (∀ a : ↥A, f a = π a) →
      ¬ 2 ∣ Nat.card f.ker := by
    intro A f hf h2
    have hle : f.ker.map A.subtype ≤ pPrimeCore 2 X := by
      rintro _ ⟨x, hx, rfl⟩
      have hx' : π (x : X) = 1 := by rw [← hf]; exact hx
      rwa [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at hx'
    have hc : Nat.card f.ker ∣ Nat.card (pPrimeCore 2 X) := by
      rw [← Subgroup.card_map_of_injective A.subtype_injective]
      exact Subgroup.card_dvd_of_le hle
    exact hodd2 (h2.trans hc)
  have hφk : ¬ 2 ∣ Nat.card φ.ker := by
    have h1 : φ.ker = (C'.subtype.comp φ).ker := by
      ext x
      simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply]
      exact ⟨fun h => by rw [h, map_one], fun h => Subtype.ext h⟩
    rw [h1]
    exact hkerodd _ (fun _ => rfl)
  have hψk : ¬ 2 ∣ Nat.card ψ.ker := by
    have h1 : ψ.ker = (Kb.subtype.comp ψ).ker := by
      ext x
      simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply]
      exact ⟨fun h => by rw [h, map_one], fun h => Subtype.ext h⟩
    rw [h1]
    exact hkerodd _ (fun _ => rfl)
  have hOK : (pPrimeCore 2 ↥Kb).map Kb.subtype = ((pPrimeCore 2 ↥K).map K.subtype).map π := by
    rw [← map_pPrimeCore_of_surjective ψ hψs hψk, map_map, map_map]
    rfl
  have hOC : (pPrimeCore 2 ↥C').map C'.subtype = ((pPrimeCore 2 ↥C).map C.subtype).map π := by
    rw [← map_pPrimeCore_of_surjective φ hφs hφk, map_map, map_map]
    rfl
  obtain ⟨e₀⟩ := GSThmB.OddQuot.nonempty_pPrimeCore_equiv_of_surjective ψ hψs hψk
  refine ⟨(map_mono hK.1).trans hCmap.le, ?_, ?_, ?_⟩
  · have hmap : (K.subgroupOf C).map φ = Kb.subgroupOf C' := by
      ext ⟨y, hy⟩
      constructor
      · rintro ⟨x, hx, hxy⟩
        exact ⟨x, hx, congrArg Subtype.val hxy⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hK.1 hx⟩, hx, rfl⟩
    rw [← hmap]
    exact hK.2.1.map hφs
  · rw [hOK, hOC, hK.2.2.1]
  · rcases hK.2.2.2 with h1 | h1
    · obtain ⟨ε⟩ := h1
      exact .inl ⟨e₀.symm.trans ε⟩
    · obtain ⟨ε⟩ := h1
      exact .inr ⟨e₀.symm.trans ε⟩

theorem commutator_le_of_bar {L K : Subgroup X} (hL : IsTwoComponentIn L ⊤)
    (h : ∀ k ∈ K, ∀ l ∈ L, (QuotientGroup.mk k : X ⧸ pPrimeCore 2 X) * QuotientGroup.mk l =
      QuotientGroup.mk l * QuotientGroup.mk k) :
    ⁅K, L⁆ ≤ (pPrimeCore 2 ↥L).map L.subtype := by
  have hLs : L.IsSubnormal := by
    have h' := hL.2.1.map (f := (⊤ : Subgroup X).subtype) (fun x => ⟨⟨x, mem_top x⟩, rfl⟩)
    rwa [subgroupOf_map_subtype, inf_top_eq] at h'
  have hcomm : ∀ k ∈ K, ∀ l ∈ L, k * l * k⁻¹ * l⁻¹ ∈ pPrimeCore 2 X := by
    intro k hk l hl
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv, h k hk l hl]
    group
  rw [Subgroup.commutator_le]
  intro k hk l hl
  have hkl : k * l * k⁻¹ ∈ L := conj_mem_of_commutator_mem hLs hL.2.2.1 (hcomm k hk) l hl
  rw [map_pPrimeCore_eq_inf hLs, commutatorElement_def]
  exact mem_inf.mpr ⟨mul_mem hkl (inv_mem hl), hcomm k hk l hl⟩

theorem oPrimeResidualOf_le_of_bar {L K : Subgroup X} (hL : IsTwoComponentIn L ⊤)
    (h : GH74.GLS.oPrimeResidualOf 2 (K.map (QuotientGroup.mk' (pPrimeCore 2 X))) ≤
      L.map (QuotientGroup.mk' (pPrimeCore 2 X))) :
    GH74.GLS.oPrimeResidualOf 2 K ≤ L := by
  have hLs : L.IsSubnormal := by
    have h' := hL.2.1.map (f := (⊤ : Subgroup X).subtype) (fun x => ⟨⟨x, mem_top x⟩, rfl⟩)
    rwa [subgroupOf_map_subtype, inf_top_eq] at h'
  set π := QuotientGroup.mk' (pPrimeCore 2 X) with hπ
  unfold GH74.GLS.oPrimeResidualOf GH74.GLS.oPrimeResidual
  rw [MonoidHom.map_closure, closure_le]
  rintro _ ⟨x, ⟨n, hn⟩, rfl⟩
  have hxn : (x : X) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hx : π (x : X) ∈ GH74.GLS.oPrimeResidualOf 2 (K.map π) := by
    refine ⟨⟨π x, mem_map_of_mem π x.2⟩, Subgroup.subset_closure ⟨n, ?_⟩, rfl⟩
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← map_pow, hxn, map_one]
  obtain ⟨l, hl, hlx⟩ := h hx
  have hlx' : l⁻¹ * (x : X) ∈ pPrimeCore 2 X := by
    have h1 : (QuotientGroup.mk l : X ⧸ pPrimeCore 2 X) = QuotientGroup.mk (x : X) := hlx
    exact QuotientGroup.eq.mp h1
  have hmem : (x : X) ∈ L ⊔ pPrimeCore 2 X := by
    rw [show (x : X) = l * (l⁻¹ * x) by group]
    exact mul_mem (mem_sup_left hl) (mem_sup_right hlx')
  exact mem_of_mem_sup_pPrimeCore hLs hmem hxn

end F3L221

end CFSG.ComponentClassification.HarrisLit.T1
