module

public import CFSG.GH74.Generic.BProg.B2.TwoA7Term
public import CFSG.GH74.Generic.Sections
public import CFSG.GH74.GLS.TwoThin.DPair

public section

namespace CFSG.GH74.Generic.BProg.B2.SD.TwoA7TermG

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.GH74.Generic CFSG.GH74.Generic.BProg
  CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial
  CFSG.ABGLocalTools CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
open CFSG.GH74.Generic.BProg.B2.SD.TwoA7Term
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def PumpupTwoA7GH : Prop :=
  ∀ (H : Type) [Group H] [Finite H], pPrimeCore 2 H = ⊥ → IsKGroupNative H →
    ∀ (L I : Subgroup H) (s : H) (K₀ : Type) [Group K₀], GHList (↥L ⧸ center ↥L) →
      IsComponent L → orderOf s = 2 → s ∈ I →
      I ≤ L → IsPCompIn 2 (centralizer ({s} : Set H)) I → IsDoubleCoverOfAlt K₀ 7 →
      (∃ φ : ↥I →* K₀, Function.Surjective φ ∧ Odd (Nat.card φ.ker)) → I = L

theorem pumpup_trivial (hK : PumpupTwoA7GH) (hkgh : KGH G) (hG : IsKProperSimple G) {u y : G}
    {I K' : Subgroup G}
    (hu2 : orderOf u = 2) (hIc : IsPCompIn 2 (centralizer ({u} : Set G)) I) (huI : u ∈ I)
    (hcov : IsDoubleCoverOfAlt (↥I ⧸ pPrimeCore 2 ↥I) 7) (hy2 : orderOf y = 2)
    (hyu : y ∈ centralizer ({u} : Set G)) (hyI : y ∈ centralizerSection I (pPrimeCoreOf 2 I))
    (hK'p : IsPCompIn 2 (pumpUp 2 I y) K') : PumpTrivial u y I K' := by
  obtain ⟨Λ, hΛX, hΛlay, hΛpc, hΛuniq, hΛW, h2el, hcovΛ⟩ := pumpup_cover hy2 hIc hyI
  have huY : u ∈ centralizer ({y} : Set G) := mem_centralizer_symm hyu
  set Y' := centralizer ({y} : Set G) with hY'
  have hso : orderOf (⟨u, huY⟩ : ↥Y') = 2 := orderOf_mk_centralizer huY hu2
  have hΛC := le_centralizer_mk (isPCompIn_two_iff.mp hΛW).1 huY
  have hΛ2 := isTwoComponent_centralizer_mk hΛW huY
  obtain ⟨hΛE, hJsub, L, hL, hcases, hLJ, hLsJ, hiff⟩ := pumpupY_structure hso hΛC hΛ2
  obtain ⟨hK'2, hK'J⟩ := isTwoComponent_of_isPCompIn_pumpUp hΛlay hΛE hK'p
  have himg := (hiff _ hK'2).mp hK'J
  have hΛI : Λ ≤ I := hΛX.trans inf_le_left
  have hΛY : Λ ≤ Y' := hΛX.trans inf_le_right
  obtain ⟨φ, hφs, hφo, hφρ⟩ := exists_phi hΛI hΛY hcovΛ
  have hu2' : u ^ (2 ^ 1) = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hu2, ← pow_one 2] at this
  have huΛ : u ∈ Λ := h2el u (Subgroup.mem_inf.mpr ⟨huI, huY⟩) ⟨1, hu2'⟩
  have hsmem : barMk ↥Y' ⟨u, huY⟩ ∈ (Λ.subgroupOf Y').map (barMk ↥Y') :=
    ⟨⟨u, huY⟩, Subgroup.mem_subgroupOf.mpr huΛ, rfl⟩
  have hvert : conjSub (barMk ↥Y' ⟨u, huY⟩)⁻¹ L = L ∧
      (Λ.subgroupOf Y').map (barMk ↥Y') ≤ L := by
    rcases hcases with h | ⟨hLs, hAB, hAD⟩
    · exact h
    · exfalso
      have hmem : barMk ↥Y' ⟨u, huY⟩ ∈ L ⊔ conjSub (barMk ↥Y' ⟨u, huY⟩)⁻¹ L := by
        obtain ⟨l, hl⟩ := hAD hsmem
        have := swapDiag_mem_sup hAB l
        rw [hl] at this
        exact this
      exact hLs (conjSub_eq_of_mem_sup hAB (inv_mem hmem))
  have himgL : (K'.subgroupOf Y').map (barMk ↥Y') = L := by
    rcases himg with h | h
    · exact h
    · rw [h, hvert.1]
  have hK'Y : K' ≤ Y' := hK'p.1.trans (pumpUp_le_centralizer I y)
  have hR1 : u ∈ normalizer (K' : Set G) := by
    refine mem_normalizer_of_map_normalizes hK'Y hK'2 huY ?_
    rw [himgL]
    exact map_conj_eq_of_mem L (hvert.2 hsmem)
  have hIC : (Λ.subgroupOf Y').map (barMk ↥Y') ≤
      centralizer ({barMk ↥Y' ⟨u, huY⟩} : Set (barQ ↥Y')) :=
    (Subgroup.map_mono hΛC).trans (map_centralizer_barMk hso).le
  have hIpc : IsPCompIn 2 (centralizer ({barMk ↥Y' ⟨u, huY⟩} : Set (barQ ↥Y')))
      ((Λ.subgroupOf Y').map (barMk ↥Y')) :=
    isPCompIn_two_iff.mpr ⟨hIC, isTwoComponent_map_barMk hso hΛC hΛ2⟩
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hy2
    omega
  have hGH : GHList (↥L ⧸ center ↥L) := ghList_of_quasisimple hG.1 hG.2.1 hkgh hy2 hL.1
  have hIeqL : (Λ.subgroupOf Y').map (barMk ↥Y') = L :=
    hK (barQ ↥Y') (pPrimeCore_quotient_eq_bot ↥Y') (isKGroupNative_barQ_centralizer hG hy1) L _
      (barMk ↥Y' ⟨u, huY⟩) _ hGH hL (orderOf_barMk hso) hsmem hvert.2 hIpc hcov ⟨φ, hφs, hφo⟩
  have hIpsub : ((Λ.subgroupOf Y').map (barMk ↥Y')).IsSubnormal := by
    rw [hIeqL]
    exact hL.2
  have hcore : pPrimeCore 2 ↥((Λ.subgroupOf Y').map (barMk ↥Y')) = ⊥ := by
    rw [CatalogueBAlternating.primeCore_two_eq_oddCore
      (G := ↥((Λ.subgroupOf Y').map (barMk ↥Y')))]
    exact OddCore.subnormal_corefree oddCore_barQ _
      (Components.chain_of_mathlib_subnormal hIpsub)
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    have hle : φ.ker ≤ pPrimeCore 2 ↥((Λ.subgroupOf Y').map (barMk ↥Y')) :=
      le_sSup ⟨φ.normal_ker, Nat.coprime_two_left.mpr hφo⟩
    rw [hcore] at hle
    exact le_bot_iff.mp hle
  have hφb : Function.Bijective φ := ⟨hφinj, hφs⟩
  obtain ⟨e1⟩ := hat_equiv_subgroupOf hK'Y
  obtain ⟨e2⟩ := hat_equiv_map
    (Components.mathlib_subnormal_of_chain hK'2.1 Subgroup.IsSubnormal.top)
  let eφ : ↥((Λ.subgroupOf Y').map (barMk ↥Y')) ≃* (↥I ⧸ pPrimeCore 2 ↥I) :=
    MulEquiv.ofBijective φ hφb
  have hR2 : Nonempty ((↥K' ⧸ pPrimeCore 2 ↥K') ≃* (↥I ⧸ pPrimeCore 2 ↥I)) :=
    ⟨(((e1.trans e2).trans (MulEquiv.subgroupCongr himgL)).trans
      (MulEquiv.subgroupCongr hIeqL.symm)).trans eφ⟩
  refine ⟨hK'Y, hR1, hR2, ?_, ⟨Λ, hΛW, hΛI, hcovΛ, h2el, hK'2, ?_⟩⟩
  ·
    intro q hq hyq
    have hqs : q ∈ centralizerSection I (pPrimeCoreOf 2 I) := hq.2
    have hqY : q ∈ Y' := by
      rw [hY', Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff.mp hg]
      exact hyq
    have hqX : q ∈ normalizer ((I ⊓ Y' : Subgroup G) : Set G) :=
      TwoThin.mem_normalizer_inf hqs.1 (Subgroup.le_normalizer hqY)
    have hΛq : ∀ a ∈ Λ, q * a * q⁻¹ ∈ Λ := fun a ha =>
      conj_mem_of_unique_isPCompIn hΛpc hΛuniq hqX ha
    have hstar : ∀ (a : G) (ha : a ∈ Λ), barMk ↥Y' (⟨q, hqY⟩ * ⟨a, hΛY ha⟩ * ⟨q, hqY⟩⁻¹) =
        barMk ↥Y' ⟨a, hΛY ha⟩ := by
      intro a ha
      have haq : q * a * q⁻¹ ∈ Λ := hΛq a ha
      have hbΛ : q * a * q⁻¹ * a⁻¹ ∈ Λ := mul_mem haq (inv_mem ha)
      have hbO : q * a * q⁻¹ * a⁻¹ ∈ pPrimeCoreOf 2 I := by
        have := inv_mem (hqs.2.2 a (hΛI ha))
        simpa [commutatorElement_def, mul_assoc] using this
      have h1 : hatMap hΛI ⟨q * a * q⁻¹ * a⁻¹, hbΛ⟩ = 1 := (hatMap_eq_one_iff hΛI _).mpr hbO
      have h2 := hφρ _ hbΛ
      rw [h1] at h2
      have h3 : (⟨barMk ↥Y' ⟨q * a * q⁻¹ * a⁻¹, hΛY hbΛ⟩,
          ⟨⟨_, hΛY hbΛ⟩, Subgroup.mem_subgroupOf.mpr hbΛ, rfl⟩⟩ :
            ↥((Λ.subgroupOf Y').map (barMk ↥Y'))) = 1 :=
        hφb.1 (h2.trans (map_one φ).symm)
      have h4 : barMk ↥Y' ⟨q * a * q⁻¹ * a⁻¹, hΛY hbΛ⟩ = 1 := congrArg Subtype.val h3
      have h5 : (⟨q * a * q⁻¹ * a⁻¹, hΛY hbΛ⟩ : ↥Y') =
          ⟨q, hqY⟩ * ⟨a, hΛY ha⟩ * ⟨q, hqY⟩⁻¹ * ⟨a, hΛY ha⟩⁻¹ := rfl
      rw [h5, map_mul, mul_eq_one_iff_eq_inv, ← map_inv] at h4
      rw [h4]
      simp
    have hπ : ∀ m ∈ K'.subgroupOf Y',
        barMk ↥Y' (⟨q, hqY⟩ * m * ⟨q, hqY⟩⁻¹) = barMk ↥Y' m := by
      intro m hm
      have hmL : barMk ↥Y' m ∈ (Λ.subgroupOf Y').map (barMk ↥Y') := by
        rw [hIeqL, ← himgL]
        exact ⟨m, hm, rfl⟩
      obtain ⟨a', ha', hmm⟩ := hmL
      have ha'Λ : (a' : G) ∈ Λ := Subgroup.mem_subgroupOf.mp ha'
      have h1 := hstar a' ha'Λ
      have e1 : barMk ↥Y' (⟨q, hqY⟩ * m * ⟨q, hqY⟩⁻¹) =
          barMk ↥Y' ⟨q, hqY⟩ * barMk ↥Y' m * (barMk ↥Y' ⟨q, hqY⟩)⁻¹ := by simp [map_mul]
      have e2 : barMk ↥Y' (⟨q, hqY⟩ * a' * ⟨q, hqY⟩⁻¹) =
          barMk ↥Y' ⟨q, hqY⟩ * barMk ↥Y' a' * (barMk ↥Y' ⟨q, hqY⟩)⁻¹ := by simp [map_mul]
      rw [e1, ← hmm, ← e2]
      exact h1
    have hcs := mem_centralizerSection_of_map_eq hK'Y hK'2 hqY hπ
    show q ∈ centralizer ({y} : Set G) ⊓ centralizerSection K' (pPrimeCoreOf 2 K')
    refine Subgroup.mem_inf.mpr ⟨?_, hcs⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.mp hg]
    exact hyq
  · rw [himgL, hIeqL]

theorem isTwoTerminal_of_twoA7 (hK : PumpupTwoA7GH) (hkgh : KGH G) (hG : IsKProperSimple G) {u : G}
    {I : Subgroup G} (hILo : IsILo 2 u I) (huI : u ∈ I)
    (hcov : IsDoubleCoverOfAlt (↥I ⧸ pPrimeCore 2 ↥I) 7) : IsTwoTerminal u I := by
  refine ⟨hILo, ?_, ?_⟩
  · intro y K' hlt
    obtain ⟨-, ⟨hy2, -, -⟩, hyu, hyI, hK'p⟩ := hlt
    have htr := TwoA7TermG.pumpup_trivial hK hkgh hG hILo.1 hILo.2.2 huI hcov hy2 hyu hyI hK'p
    exact ⟨htr.normalizes, htr.hat⟩
  · intro Q hQ y K' hlt hyQ hyc
    obtain ⟨-, ⟨hy2, -, -⟩, hyu, hyI, hK'p⟩ := hlt
    have htr := TwoA7TermG.pumpup_trivial hK hkgh hG hILo.1 hILo.2.2 huI hcov hy2 hyu hyI hK'p
    exact TwoA7Term.sylow_clause hILo.1 hILo.2.2 huI hyu htr hQ hyc

end CFSG.GH74.Generic.BProg.B2.SD.TwoA7TermG
