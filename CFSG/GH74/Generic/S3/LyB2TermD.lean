module

public import CFSG.GH74.GLS.TwoThin.DPair

public section

namespace CFSG.GH74.GLS.TwoThin

open Subgroup Blueprint Assembly.LowTwoRank CFSG.ComponentClassification
  CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

section DPairC

variable {G : Type} [Group G] [Finite G]

@[expose] def ClsClosed (Cls : G → Subgroup G → Prop) : Prop :=
  ∀ (x : G) (K : Subgroup G) (x' : G) (K' : Subgroup G), IsB2Pair x K → Cls x K →
    PumpUpLT 2 x K x' K' → (x ∈ K ∨ x' ∈ K) →
      InB2 (↥K' ⧸ pPrimeCore 2 ↥K') ∧ Cls x' K'

theorem dpair_analysisC (Cls : G → Subgroup G → Prop) (hC : ClsClosed Cls) {x : G} {K : Subgroup G}
    (hP : IsB2Pair x K) (hcls : Cls x K) (hxK : x ∈ K)
    (hmax : ∀ (x' : G) (K' : Subgroup G), IsB2Pair x' K' → Cls x' K' → hatCard K' ≤ hatCard K)
    {x' : G} {K' : Subgroup G} (hlt : PumpUpLT 2 x K x' K') :
    x ∈ normalizer (K' : Set G) ∧
      Nonempty ((↥K' ⧸ pPrimeCore 2 ↥K') ≃* (↥K ⧸ pPrimeCore 2 ↥K)) ∧
      (∀ q ∈ CxK x K, x' * q = q * x' → q ∈ CxK x' K') := by
  have hcl := hC x K x' K' hP hcls hlt (Or.inl hxK)
  have hP' : IsB2Pair x' K' := ⟨hlt.2.1, hcl.1⟩
  have hcard : hatCard K' ≤ hatCard K := hmax x' K' hP' hcl.2
  obtain ⟨⟨hxo, -, hKc⟩, ⟨hx'o, -, -⟩, hx'x, hx'K, hK'p⟩ := hlt
  obtain ⟨Λ, hΛX, hΛlay, hΛpc, hΛuniq, hΛW, h2el, hcovΛ⟩ := pumpup_cover hx'o hKc hx'K
  have hxY : x ∈ centralizer ({x'} : Set G) := mem_centralizer_symm hx'x
  set Y' := centralizer ({x'} : Set G) with hY'
  have hso : orderOf (⟨x, hxY⟩ : ↥Y') = 2 := orderOf_mk_centralizer hxY hxo
  have hΛC := le_centralizer_mk (isPCompIn_two_iff.mp hΛW).1 hxY
  have hΛ2 := isTwoComponent_centralizer_mk hΛW hxY
  obtain ⟨hΛE, hJsub, L, hL, hcases, hLJ, hLsJ, hiff⟩ := pumpupY_structure hso hΛC hΛ2
  obtain ⟨hK'2, hK'J⟩ := isTwoComponent_of_isPCompIn_pumpUp hΛlay hΛE hK'p
  have himg := (hiff _ hK'2).mp hK'J
  have hΛK : Λ ≤ K := hΛX.trans inf_le_left
  have hΛY : Λ ≤ Y' := hΛX.trans inf_le_right
  obtain ⟨φ, hφs, hφo, hφρ⟩ := exists_phi hΛK hΛY hcovΛ
  have hx2 : x ^ (2 ^ 1) = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hxo, ← pow_one 2] at this
  have hxΛ : x ∈ Λ := h2el x (Subgroup.mem_inf.mpr ⟨hxK, hxY⟩) ⟨1, hx2⟩
  have hsmem : barMk ↥Y' ⟨x, hxY⟩ ∈ (Λ.subgroupOf Y').map (barMk ↥Y') :=
    ⟨⟨x, hxY⟩, Subgroup.mem_subgroupOf.mpr hxΛ, rfl⟩
  have hvert : conjSub (barMk ↥Y' ⟨x, hxY⟩)⁻¹ L = L ∧
      (Λ.subgroupOf Y').map (barMk ↥Y') ≤ L := by
    rcases hcases with h | ⟨hLs, hAB, hAD⟩
    · exact h
    · exfalso
      have hmem : barMk ↥Y' ⟨x, hxY⟩ ∈ L ⊔ conjSub (barMk ↥Y' ⟨x, hxY⟩)⁻¹ L := by
        obtain ⟨l, hl⟩ := hAD hsmem
        have := swapDiag_mem_sup hAB l
        rw [hl] at this
        exact this
      exact hLs (conjSub_eq_of_mem_sup hAB (inv_mem hmem))
  have himgL : (K'.subgroupOf Y').map (barMk ↥Y') = L := by
    rcases himg with h | h
    · exact h
    · rw [h, hvert.1]
  have hK'Y : K' ≤ Y' := hK'p.1.trans (pumpUp_le_centralizer K x')
  have hR1 : x ∈ normalizer (K' : Set G) := by
    refine mem_normalizer_of_map_normalizes hK'Y hK'2 hxY ?_
    rw [himgL]
    exact map_conj_eq_of_mem L (hvert.2 hsmem)
  obtain ⟨e1⟩ := hat_equiv_subgroupOf hK'Y
  obtain ⟨e2⟩ := hat_equiv_map
    (Components.mathlib_subnormal_of_chain hK'2.1 Subgroup.IsSubnormal.top)
  have hK'L : Nat.card (↥K' ⧸ pPrimeCore 2 ↥K') = Nat.card ↥L := by
    rw [Nat.card_congr (e1.trans e2).toEquiv]
    exact Nat.card_congr (MulEquiv.subgroupCongr himgL).toEquiv
  let I : Subgroup (barQ ↥Y') := (Λ.subgroupOf Y').map (barMk ↥Y')
  have hIL : Nat.card ↥I ≤ Nat.card ↥L := Subgroup.card_le_of_le hvert.2
  have hKI : Nat.card (↥K ⧸ pPrimeCore 2 ↥K) ≤ Nat.card ↥I :=
    Nat.card_le_card_of_surjective φ hφs
  have hcard' : Nat.card (↥K' ⧸ pPrimeCore 2 ↥K') ≤ Nat.card (↥K ⧸ pPrimeCore 2 ↥K) := hcard
  have hIeqL : I = L := Subgroup.eq_of_le_of_card_ge hvert.2 (by omega)
  have hIK : Nat.card ↥I ≤ Nat.card (↥K ⧸ pPrimeCore 2 ↥K) := by omega
  have hφb : Function.Bijective φ := hφs.bijective_of_nat_card_le hIK
  let eφ : ↥I ≃* (↥K ⧸ pPrimeCore 2 ↥K) := MulEquiv.ofBijective φ hφb
  have hR2 : Nonempty ((↥K' ⧸ pPrimeCore 2 ↥K') ≃* (↥K ⧸ pPrimeCore 2 ↥K)) :=
    ⟨(((e1.trans e2).trans (MulEquiv.subgroupCongr himgL)).trans
      (MulEquiv.subgroupCongr hIeqL.symm)).trans eφ⟩
  refine ⟨hR1, hR2, ?_⟩
  intro q hq hxq
  have hqs : q ∈ centralizerSection K (pPrimeCoreOf 2 K) := hq.2
  have hqY : q ∈ Y' := by
    rw [hY', Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.mp hg]
    exact hxq
  have hqX : q ∈ normalizer ((K ⊓ Y' : Subgroup G) : Set G) :=
    mem_normalizer_inf hqs.1 (Subgroup.le_normalizer hqY)
  have hΛq : ∀ a ∈ Λ, q * a * q⁻¹ ∈ Λ := fun a ha =>
    conj_mem_of_unique_isPCompIn hΛpc hΛuniq hqX ha
  have hstar : ∀ (a : G) (ha : a ∈ Λ), barMk ↥Y' (⟨q, hqY⟩ * ⟨a, hΛY ha⟩ * ⟨q, hqY⟩⁻¹) =
      barMk ↥Y' ⟨a, hΛY ha⟩ := by
    intro a ha
    have haq : q * a * q⁻¹ ∈ Λ := hΛq a ha
    have hbΛ : q * a * q⁻¹ * a⁻¹ ∈ Λ := mul_mem haq (inv_mem ha)
    have hbO : q * a * q⁻¹ * a⁻¹ ∈ pPrimeCoreOf 2 K := by
      have := inv_mem (hqs.2.2 a (hΛK ha))
      simpa [commutatorElement_def, mul_assoc] using this
    have h1 : hatMap hΛK ⟨q * a * q⁻¹ * a⁻¹, hbΛ⟩ = 1 := (hatMap_eq_one_iff hΛK _).mpr hbO
    have h2 := hφρ _ hbΛ
    rw [h1] at h2
    have h3 : (⟨barMk ↥Y' ⟨q * a * q⁻¹ * a⁻¹, hΛY hbΛ⟩,
        ⟨⟨_, hΛY hbΛ⟩, Subgroup.mem_subgroupOf.mpr hbΛ, rfl⟩⟩ : ↥I) = 1 :=
      hφb.1 (h2.trans (map_one φ).symm)
    have h4 : barMk ↥Y' ⟨q * a * q⁻¹ * a⁻¹, hΛY hbΛ⟩ = 1 := congrArg Subtype.val h3
    have h5 : (⟨q * a * q⁻¹ * a⁻¹, hΛY hbΛ⟩ : ↥Y') =
        ⟨q, hqY⟩ * ⟨a, hΛY ha⟩ * ⟨q, hqY⟩⁻¹ * ⟨a, hΛY ha⟩⁻¹ := rfl
    rw [h5, map_mul, mul_eq_one_iff_eq_inv, ← map_inv] at h4
    rw [h4]
    simp
  have hπ : ∀ m ∈ K'.subgroupOf Y', barMk ↥Y' (⟨q, hqY⟩ * m * ⟨q, hqY⟩⁻¹) = barMk ↥Y' m := by
    intro m hm
    have hmL : barMk ↥Y' m ∈ I := by
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
  show q ∈ centralizer ({x'} : Set G) ⊓ centralizerSection K' (pPrimeCoreOf 2 K')
  refine Subgroup.mem_inf.mpr ⟨?_, hcs⟩
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  rw [Set.mem_singleton_iff.mp hg]
  exact hxq

theorem isTwoTerminal_of_mu_maxC (Cls : G → Subgroup G → Prop) (hC : ClsClosed Cls) {x : G}
    {K : Subgroup G} (hP : IsB2Pair x K) (hcls : Cls x K) (hxK : x ∈ K)
    (hmax : ∀ (x' : G) (K' : Subgroup G), IsB2Pair x' K' → Cls x' K' →
      hatCard K' < hatCard K ∨ (hatCard K' = hatCard K ∧ sylVal x' K' ≤ sylVal x K)) :
    IsTwoTerminal x K := by
  have hmax1 : ∀ (x' : G) (K' : Subgroup G), IsB2Pair x' K' → Cls x' K' → hatCard K' ≤ hatCard K :=
    fun x' K' h hc => (hmax x' K' h hc).elim le_of_lt (fun h => h.1.le)
  refine ⟨hP.1, fun x' K' hlt => ?_, ?_⟩
  · obtain ⟨h1, h2, -⟩ := dpair_analysisC Cls hC hP hcls hxK hmax1 hlt
    exact ⟨h1, h2⟩
  · intro Q hQ x' K' hlt hx'Q hx'c
    obtain ⟨-, ⟨e⟩, hR3⟩ := dpair_analysisC Cls hC hP hcls hxK hmax1 hlt
    have hcl := hC x K x' K' hP hcls hlt (Or.inl hxK)
    have hP' : IsB2Pair x' K' := ⟨hlt.2.1, hcl.1⟩
    have hQle : Q ≤ CxK x' K' := fun q hq => hR3 q (hQ.le hq) (hx'c q hq)
    have hceq : hatCard K' = hatCard K := Nat.card_congr e.toEquiv
    have hsyl : sylVal x' K' ≤ sylVal x K := by
      rcases hmax x' K' hP' hcl.2 with h | h
      · omega
      · exact h.2
    have hcardQ : Nat.card Q = 2 ^ sylVal x K := hQ.card_eq
    have hdvd : Nat.card Q ∣ Nat.card ↥(CxK x' K') := Subgroup.card_dvd_of_le hQle
    rw [hcardQ] at hdvd
    have hC'ne : Nat.card ↥(CxK x' K') ≠ 0 := Nat.card_pos.ne'
    have hle : sylVal x K ≤ sylVal x' K' :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hC'ne).mp hdvd
    refine CFSG.ABGLocalTools.isSylowOf_of_card hQle ?_
    rw [hcardQ]
    exact congrArg (2 ^ ·) (le_antisymm hle hsyl)

end DPairC

end CFSG.GH74.GLS.TwoThin
