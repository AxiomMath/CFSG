module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ThirdLineAuxCore
public import CFSG.RankThree.PartOne.KE6.Phi6Solvable

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.ThirdLineAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.E6 CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KE6
open CFSG.RankThree.PartOne.KE (twistedTorus mem_twistedTorus adjEmb adjEmb_injective adjEmb_mem
  adjEmb_frobenius sigma_embedding_data subtorusImage mem_subtorusImage_iff twistedTorusOf
  twistedFixedPoints mem_twistedFixedPoints subtorusSigma subtorusSigma_le_twistedTorusOf
  pow_eq_one_of_orderOf_rootDiagUnit ne_one_of_orderOf_rootDiagUnit)
open CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
open scoped Matrix Pointwise

set_option linter.unusedSectionVars false


theorem twThirdLine_e6Six (K : Type) [Field K] [Finite K] (hK3 : 3 ≤ Nat.card K) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p)
    (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = 6) : TwThirdLine .E6 K p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 < p := by omega
  obtain ⟨ℓ, f, hℓ', hchar, hf, hK⟩ := exists_char_pow K
  let L := AlgebraicClosure K
  haveI : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  haveI : Fintype K := Fintype.ofFinite K
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hℓ : ℓ.Prime := Fact.out
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hFrK : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact hFr c
  have hq0 : ((ℓ ^ f : ℕ) : L) = 0 := by
    rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow (by omega)]
  have hΦ' : ((Nat.card K : ℕ) : ZMod p) ^ 2 - ((Nat.card K : ℕ) : ZMod p) + 1 = 0 :=
    phi6_of_orderOf hord
  have hpq : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 - (Nat.card K : ℤ) + 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    exact hΦ'
  have hpq' : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 - ((ℓ ^ f : ℕ) : ℤ) + 1 := by
    rw [hK] at hpq
    exact hpq
  obtain ⟨hpL, ⟨ζ, hζ⟩, hr⟩ := phi6_prime_setup hq0 hp hpq'
  have hp7 : 7 ≤ p := (e6Six_data hp hp3 hpq).2.2.2.2.1
  have hordW : ¬ p ∣ Nat.card (WeylGroup Tag.E6) := by
    have : Fintype (WeylGroup Tag.E6) := Fintype.ofFinite _
    rw [(CFSG.RankThree.Chevalley.E6_weyl_length_polynomial).2]
    intro hd
    have h51840 : p ∣ 2 ^ 7 * 3 ^ 4 * 5 := by norm_num; exact hd
    rcases (Nat.Prime.dvd_mul hp).1 h51840 with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · exact absurd (Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)) (by omega)
      · exact absurd (Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)) (by omega)
    · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
  obtain ⟨g0, hg0C, hg0, hperf, hconj⟩ := e6_six_frame K hf hK hp hp3 hpq L
  have hnC : phi6N L ∈ adjointGroup .E6 L := canonicalRep_mem_adjointGroup _ L _
  have htri : ∀ h : ModGL Tag.E6 L, h ∈ phi6TorusTorsion L Fr p → h ≠ 1 →
      torusRootKernel h = ∅ ∨
      (∃ w : WeylGroup Tag.E6,
        (w • ·) '' torusRootKernel h = parabolicRoots Tag.E6 support13) ∨
      ∃ w : WeylGroup Tag.E6,
        (w • ·) '' torusRootKernel h = parabolicRoots Tag.E6 supportA2A2 := by
    intro h hhT hh1
    have : NeZero p := ⟨hp.ne_zero⟩
    obtain ⟨⟨a, a'⟩, hab⟩ := (mem_phi6TorusTorsion_iff hFr hζ hr h).1 hhT
    have hab0 : (a, a') ≠ 0 := fun h0 => hh1 (by rw [← hab, h0, ofAdd_zero, map_one])
    have hker0 : torusRootKernel h = rootKernel (eisensteinColumn (((ℓ ^ f : ℕ)) : ZMod p) a a') := by
      rw [← hab]
      exact torusRootKernel_phi3TorsionHom hζ _ a a'
    rw [hker0]
    exact rootKernel_eisenstein_trichotomy hp3 hr hab0
  have hbound : ∀ b : Fin Tag.E6.rank → Lˣ, rootDiagUnit .E6 b ∈ twistedTorusOf (phi6N L)
      (Units.map (entrywiseHom Fr)) → (∀ i, b i ^ p = 1) → b ≠ 1 →
      (rootCharKernel b).ncard ≤ 12 := by
    intro b hbT hbp hb1
    have hhp : rootDiagUnit .E6 b ^ p = 1 := by
      have h1 : rootDiagUnit .E6 (b ^ p) = rootDiagUnit .E6 b ^ p :=
        ((rootDiagUnitHom .E6 L).map_pow b p)
      have h2 : b ^ p = 1 := funext fun i => by simpa using hbp i
      rw [← h1, h2, rootDiagUnit_one]
    have hh1 : rootDiagUnit .E6 b ≠ 1 := fun h => hb1 (by
      apply rootDiagUnit_injective (τ := .E6) (K := L)
      rw [h, rootDiagUnit_one])
    have hkb : torusRootKernel (rootDiagUnit .E6 b) = rootCharKernel b :=
      torusRootKernel_rootDiagUnit b
    rcases htri _ ⟨hbT, hhp⟩ hh1 with h0 | ⟨w, hw⟩ | ⟨w, hw⟩
    · rw [hkb] at h0
      rw [h0, Set.ncard_empty]
      omega
    · rw [hkb] at hw
      have := Set.ncard_image_of_injective (rootCharKernel b) (MulAction.injective w)
      rw [hw, ncard_parabolicRoots_support13] at this
      omega
    · rw [hkb] at hw
      have := Set.ncard_image_of_injective (rootCharKernel b) (MulAction.injective w)
      rw [hw, ncard_parabolicRoots_supportA2A2] at this
      omega
  have hperx : ∀ (x c : adjointGroup .E6 K) (b : Fin Tag.E6.rank → Lˣ), orderOf x = p →
      g0⁻¹ * adjEmb .E6 K L (c * x * c⁻¹) * g0 ∈ twistedTorusOf (phi6N L)
        (Units.map (entrywiseHom Fr)) →
      rootDiagUnit .E6 b = g0⁻¹ * adjEmb .E6 K L (c * x * c⁻¹) * g0 →
      (rootCharKernel b).Nonempty →
      ¬ Group.IsSolvable ↥(Subgroup.centralizer ({x} : Set (adjointGroup .E6 K))) := by
    intro x c b hx hh hb hne
    set ι : adjointGroup .E6 K →* ModGL .E6 L := adjEmb .E6 K L with hιdef
    set h : ModGL .E6 L := g0⁻¹ * ι (c * x * c⁻¹) * g0 with hhdef
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
    have hhp : h ^ p = 1 := hordh ▸ pow_orderOf_eq_one h
    have hh1 : h ≠ 1 := fun h1 => by
      rw [h1, orderOf_one] at hordh
      exact hp.one_lt.ne hordh
    have hhT : h ∈ phi6TorusTorsion L Fr p := ⟨hh, hhp⟩
    have hkb : torusRootKernel h = rootCharKernel b := by
      rw [← hb]
      exact torusRootKernel_rootDiagUnit b
    have hrootneg : ∀ α ∈ torusRootKernel h, -α ∈ torusRootKernel h := fun α hα => by
      rw [hkb] at hα ⊢
      exact ⟨CFSG.LieType.Chevalley.IsRoot.neg hα.1, by rw [rootChar_neg', hα.2, inv_one]⟩
    have hNorm : torusGroup .E6 L ⊔ rootSpan .E6 L (torusRootKernel h) ≤
        Subgroup.normalizer (rootSpan .E6 L (torusRootKernel h) : Set (ModGL .E6 L)) :=
      torusGroup_sup_rootSpan_le_normalizer fun α hα => hα.1
    have finish : ∀ (S : Set (Fin Tag.E6.rank → ℤ)) (hS : ∀ α ∈ S, IsRoot Tag.E6 α)
        (hSn : ∀ α ∈ S, -α ∈ S) (hSeq : S = torusRootKernel h)
        (P : Subgroup (ModGL .E6 L)) (hPfin : Finite P)
        (hPq : CFSG.IsQuasisimple P) (hPQ : P ≤ rootSpan .E6 L S)
        (hPR : P ≤ twistedFixedPoints (phi6N L) (Units.map (entrywiseHom Fr)))
        (hPadj : P ≤ adjointGroup .E6 L)
        (hPnorm : ∀ y ∈ torusGroup .E6 L ⊔ rootSpan .E6 L S,
          y ∈ twistedFixedPoints (phi6N L) (Units.map (entrywiseHom Fr)) →
          ∀ u ∈ P, y * u * y⁻¹ ∈ P)
        (hPcent : ∀ y ∈ torusGroup .E6 L ⊔ rootSpan .E6 L S,
          y ∈ twistedFixedPoints (phi6N L) (Units.map (entrywiseHom Fr)) →
          (∀ u ∈ P, y * u = u * y) →
          y ∈ subtorusSigma (phi6N L) (Units.map (entrywiseHom Fr)) S),
        ¬ Group.IsSolvable ↥(Subgroup.centralizer ({x} : Set (adjointGroup .E6 K))) := by
      intro S hS hSn hSeq P hPfin hPq hPQ hPR hPadj hPnorm hPcent
      have hcS : c * x * c⁻¹ ∈ subtorusImage ι g0
          (subtorusSigma (phi6N L) (Units.map (entrywiseHom Fr)) S) := by
        rw [mem_subtorusImage_iff]
        refine Subgroup.mem_inf.2 ⟨hh, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
        have hle := rootSpan_le_centralizer (K := L) b (S := S) (by
          rw [hSeq, hkb])
        have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hle hg)
        rw [hb] at h1
        exact h1
      have hkerZ : ∀ a : Fin Tag.E6.rank → Lˣ,
          rootDiagUnit .E6 a = g0⁻¹ * ι (c * x * c⁻¹) * g0 → rootCharKernel a ⊆ S :=
        fun a ha => by
          have : a = b := rootDiagUnit_injective (ha.trans hb.symm)
          rw [this, hSeq, hkb]
      obtain ⟨ψ, hψinj, -, -, -, -, hPψ, -⟩ := sigma_embedding_data (ι' := Unit) ι
        adjEmb_injective adjEmb_mem (Units.map (entrywiseHom Fr)) (adjEmb_frobenius Fr hFrK)
        (phi6N L) g0 hg0C hg0 hperf hp hordW hS hSn (fun _ => P) (fun _ => hPfin)
        (fun _ => hPq) (fun _ => hPQ) (fun _ => hPR) (fun _ => hPadj)
        (fun _ y hy hyR u hu => hPnorm y hy hyR u hu)
        (fun y hy hyR hc => hPcent y hy hyR (fun u hu => hc () u hu)) hx c hcS hkerZ
      exact not_isSolvable_of_embedding ψ hψinj hPq (hPψ ())
    rcases htri h hhT hh1 with hreg | hA2 | hA2A2
    · exfalso
      rw [hkb] at hreg
      exact Set.not_nonempty_empty (hreg ▸ hne)
    ·
      obtain ⟨hfin, hqs, -, hC6, hcentQ⟩ := phi6_A2_case (K := K) hℓ hf hK hFr hp hp3 hpq' hh
        hordh hA2
      refine finish (torusRootKernel h) (fun α hα => (by rw [hkb] at hα; exact hα.1)) hrootneg
        rfl (phi6Qθ L Fr (torusRootKernel h)) hfin hqs inf_le_left inf_le_right
        (inf_le_left.trans (rootSpan_le_adjointGroup L _))
        (fun y hy hyR u hu => phi6Qθ_conj_mem (hNorm hy) hyR hu) (fun y hy hyR hc => ?_)
      have hyH : y ∈ torusGroup .E6 L := hC6 ⟨hy, Subgroup.mem_centralizer_iff.2 fun u hu =>
        (hc u hu).symm⟩
      have hcent := hcentQ y hyH (fun u hu => hc u hu)
      exact Subgroup.mem_inf.2 ⟨mem_twistedTorus.2 ⟨hyH, mem_twistedFixedPoints.1 hyR⟩,
        Subgroup.mem_centralizer_iff.2 fun g hg => (hcent g hg).symm⟩
    ·
      obtain ⟨hfin, hqs, -, -, -, hC6, hcentQ⟩ := phi6_A2A2_case (K := K) hℓ hf hK hFr hp hp3
        hpq' hh hordh hA2A2
      refine finish (torusRootKernel h) (fun α hα => (by rw [hkb] at hα; exact hα.1)) hrootneg
        rfl (phi6P L Fr (torusRootKernel h)) hfin hqs ((phi6P_le _).trans inf_le_left)
        ((phi6P_le _).trans inf_le_right)
        ((phi6P_le _).trans (inf_le_left.trans (rootSpan_le_adjointGroup L _)))
        (fun y hy hyR u hu => phi6P_conj_mem (hNorm hy) hyR hu) (fun y hy hyR hc => ?_)
      have hyH : y ∈ torusGroup .E6 L := hC6 ⟨hy, Subgroup.mem_centralizer_iff.2 fun u hu =>
        (hc u hu).symm⟩
      have hcent := hcentQ y hyH (fun u hu => hc u hu)
      exact Subgroup.mem_inf.2 ⟨mem_twistedTorus.2 ⟨hyH, mem_twistedFixedPoints.1 hyR⟩,
        Subgroup.mem_centralizer_iff.2 fun g hg => (hcent g hg).symm⟩
  refine twThirdLine_of_kernel (Units.map (entrywiseHom Fr)) (phi6N L) g0 hp hconj 12
    (by rw [card_rootFinset_E6]; norm_num) hbound hperx

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.ThirdLineAux
