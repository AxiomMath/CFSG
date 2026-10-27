module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSigKey

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup

variable {X : Type} [Group X]

theorem fixedLayer_coreQuot_equiv [Finite X] {J E : Subgroup X}
    (hJq : IsQuasisimple (↥J ⧸ pPrimeCore 2 ↥J)) (hE : E ≤ UnbalancedLayer.coreActionKernel J)
    (hE2 : IsPGroup 2 E) :
    Nonempty (↥(GSLit.fixedLayer J E) ⧸ pPrimeCore 2 ↥(GSLit.fixedLayer J E) ≃*
      ↥J ⧸ pPrimeCore 2 ↥J) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set JE := GSLit.fixedLayer J E with hJE
  have hJEJ : JE ≤ J := (GSLit.fixedLayer_le_inf J E).trans inf_le_left
  obtain ⟨hsup, -⟩ := GSLit.fixedLayer_sup_pPrimeCore hJq hE hE2
  set Y := JE.subgroupOf J with hYdef
  have hY : Function.Surjective ((QuotientGroup.mk' (pPrimeCore 2 ↥J)).comp Y.subtype) := by
    have h1 : Y ⊔ pPrimeCore 2 ↥J = ⊤ := by
      have h2 : (JE ⊔ (pPrimeCore 2 ↥J).map J.subtype).subgroupOf J = ⊤ := by
        rw [hsup]
        exact subgroupOf_self J
      rwa [subgroupOf_sup hJEJ (map_subtype_le _), subgroupOf_map_subtype_self] at h2
    rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, range_subtype]
    have h2 := congrArg (Subgroup.map (QuotientGroup.mk' (pPrimeCore 2 ↥J))) h1
    rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h2
  obtain ⟨φ, -⟩ := UnbalancedGS.FixedPrimeLayer.exists_quotient_mulEquiv Y hY
  exact ⟨(Sol78.coreQuotCongr (subgroupOfEquivOfLe hJEJ)).symm.trans φ⟩

theorem factorization_two_card_alt {n m : ℕ} (hn : 2 ≤ n) (hnm : n ≤ m) :
    (Nat.card (alternatingGroup (Fin n))).factorization 2 ≤
        (Nat.card (alternatingGroup (Fin m))).factorization 2 ∧
      (Odd n → n < m → (Nat.card (alternatingGroup (Fin n))).factorization 2 + 1 ≤
        (Nat.card (alternatingGroup (Fin m))).factorization 2) := by
  have hk : ∀ k : ℕ, 2 ≤ k → (Nat.card (alternatingGroup (Fin k))).factorization 2 + 1 =
      (k.factorial).factorization 2 := by
    intro k hk
    have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr hk
    have h1 := two_mul_nat_card_alternatingGroup (α := Fin k)
    rw [Nat.card_perm, Nat.card_fin] at h1
    rw [← h1, Nat.factorization_mul two_ne_zero Nat.card_pos.ne', Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_two, add_comm]
  have hdvd : ∀ a b : ℕ, a ≤ b → (a.factorial).factorization 2 ≤ (b.factorial).factorization 2 :=
    fun a b hab => (Nat.factorization_le_iff_dvd (Nat.factorial_ne_zero a)
      (Nat.factorial_ne_zero b)).mpr (Nat.factorial_dvd_factorial hab) 2
  have h1 := hk n hn
  have h2 := hk m (hn.trans hnm)
  refine ⟨by have := hdvd n m hnm; omega, fun hodd hlt => ?_⟩
  have h3 := hdvd (n + 1) m hlt
  have h4 : ((n + 1).factorial).factorization 2 = (n + 1).factorization 2 +
      (n.factorial).factorization 2 := by
    rw [Nat.factorial_succ, Nat.factorization_mul (Nat.succ_ne_zero n) (Nat.factorial_ne_zero n),
      Finsupp.add_apply]
  have h5 : 0 < (n + 1).factorization 2 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_two (Nat.succ_ne_zero n)
      (even_iff_two_dvd.mp (Odd.add_one hodd))
  omega

theorem mem_normalizer_coreActionKernel {M : Subgroup X} {g : X}
    (hg : g ∈ normalizer (M : Set X)) :
    g ∈ normalizer ((UnbalancedLayer.coreActionKernel M : Subgroup X) : Set X) := by
  rw [mem_normalizer_iff]
  intro h
  refine ⟨fun hh => conj_mem_coreActionKernel hg hh, fun hh => ?_⟩
  have h1 := conj_mem_coreActionKernel (inv_mem hg) hh
  simpa [mul_assoc] using h1

theorem mem_normalizer_fusionZStar {M : Subgroup X} {g : X} (hg : g ∈ normalizer (M : Set X)) :
    g ∈ normalizer (((Open.fusionZStar ↥M).map M.subtype : Subgroup X) : Set X) := by
  have hM : M.map (MulAut.conj g).toMonoidHom = M := mem_normalizer_iff_map_conj_eq.mp hg
  let φ : M ≃* M := ((MulAut.conj g).subgroupMap M).trans (MulEquiv.subgroupCongr hM)
  have hφ : ∀ x : M, ((φ x : M) : X) = g * x * g⁻¹ := fun x => rfl
  have hZ := FooteLit.fusionZStar_map_mulEquiv φ
  rw [mem_normalizer_iff_map_conj_eq]
  conv_rhs => rw [← hZ]
  ext y
  simp only [mem_map]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨φ x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨(x : X), ⟨x, hx, rfl⟩, rfl⟩

theorem factorization_two_card_of_alt [Finite X] {M : Subgroup X} {m : ℕ}
    (eM : ↥M ⧸ Open.fusionZStar ↥M ≃* alternatingGroup (Fin m)) :
    (Nat.card M).factorization 2 = (Nat.card ↥(Open.fusionZStar ↥M)).factorization 2 +
      (Nat.card (alternatingGroup (Fin m))).factorization 2 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Open.fusionZStar ↥M)
  rw [Nat.card_congr eM.toEquiv] at h1
  rw [h1, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply, add_comm]

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  (S : Sig36 X t J n e E D)
include S

theorem mem_coreActionKernel_of_le (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    {M : Subgroup X}
    (hJM : J ≤ M) {u : X} (hut : u ∈ centralizer ({t} : Set X))
    (huM : u ∈ UnbalancedLayer.coreActionKernel M) : u ∈ UnbalancedLayer.coreActionKernel J := by
  have hJn := S.centralizer_le_normalizer hT13 hML hSch hut
  refine ⟨hJn, fun j hj => ?_⟩
  have hw : j⁻¹ * u⁻¹ * j * u ∈ J := by
    have h1 : u⁻¹ * j * u ∈ J := by
      have := (mem_normalizer_iff.mp (inv_mem hJn) j).mp hj
      rwa [inv_inv] at this
    have h2 : j⁻¹ * u⁻¹ * j * u = j⁻¹ * (u⁻¹ * j * u) := by group
    rw [h2]
    exact mul_mem (inv_mem hj) h1
  have hwO : j⁻¹ * u⁻¹ * j * u ∈ (pPrimeCore 2 ↥M).map M.subtype := huM.2 j (hJM hj)
  have hle : J ⊓ (pPrimeCore 2 ↥M).map M.subtype ≤ (pPrimeCore 2 ↥J).map J.subtype := by
    refine le_pPrimeCore_map inf_le_left ?_ ?_
    · intro g hg
      exact inf_mem_normalizer' (le_normalizer hg)
        (le_normalizer_pPrimeCore (le_normalizer (hJM hg)))
    · have h1 : Nat.card ↥(J ⊓ (pPrimeCore 2 ↥M).map M.subtype) ∣
          Nat.card ↥((pPrimeCore 2 ↥M).map M.subtype) := card_dvd_of_le inf_le_right
      rw [card_map_of_injective M.subtype_injective] at h1
      exact Nat.Coprime.coprime_dvd_right h1 pPrimeCore_coprime_card
  exact hle ⟨hw, hwO⟩

theorem factorization_two_le_of_kernel (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    {Y M : Subgroup X} (hMY : M ≤ Y)
    (hMpc : IsPComponent 2 (M.subgroupOf Y)) (hJM : J ≤ M) {u : X} (hu : orderOf u = 2)
    (huY : u ∈ Y) (hut : u ∈ centralizer ({t} : Set X))
    (huM : u ∈ UnbalancedLayer.coreActionKernel M) :
    (Nat.card M).factorization 2 ≤ (Nat.card J).factorization 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu2 : IsPGroup 2 (zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu, pow_one])
  have huJ := S.mem_coreActionKernel_of_le hT13 hML hSch hJM hut huM
  have hMq : IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 M Y hMY).mp hMpc).2.2
  have hJq : IsQuasisimple (↥J ⧸ pPrimeCore 2 ↥J) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 J _ S.pair.1.2.1).mp S.pair.1.2.2.1).2.2
  have hMsub : (M.subgroupOf Y).IsSubnormal := hMpc.choose_spec.2.1
  have hEM : zpowers u ≤ UnbalancedLayer.coreActionKernel M := zpowers_le.mpr huM
  have hEJ : zpowers u ≤ UnbalancedLayer.coreActionKernel J := zpowers_le.mpr huJ
  set Mu := GSLit.fixedLayer M (zpowers u) with hMudef
  have hMuC : Mu ≤ Y ⊓ centralizer ((zpowers u : Subgroup X) : Set X) :=
    (GSLit.fixedLayer_le_inf M (zpowers u)).trans (inf_le_inf_right _ hMY)
  have hMupc := GSLit.fixedLayer_isPComponent hMY hMsub (zpowers_le.mpr huY) hEM hu2 hMq
  have hMuperf : ⁅Mu, Mu⁆ = Mu := UnbalancedCorr.commutator_eq_of_isPComponent hMuC hMupc
  have hMuq : IsQuasisimple (↥Mu ⧸ pPrimeCore 2 ↥Mu) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 Mu _ hMuC).mp hMupc).2.2
  have hMuu : Mu ≤ centralizer ({u} : Set X) := by
    have h1 := hMuC.trans inf_le_right
    rwa [UnbalancedLayer.centralizer_zpowers_eq] at h1
  have hJuMu : GSLit.fixedLayer J (zpowers u) ≤ Mu := by
    refine GSLit.fixedLayer_le_of_twoElements hJq hEJ hu2 fun x hx hk => ?_
    rw [hMudef, GSLit.fixedLayer_eq_closure hMq hEM hu2]
    exact subset_closure ⟨⟨hJM hx.1, hx.2⟩, hk⟩
  have hkey := S.factorization_two_le hT13 hML hSch hu hut huJ hMuu hMuperf hMuq hJuMu
  obtain ⟨φ⟩ := fixedLayer_coreQuot_equiv hMq hEM hu2
  rw [factorization_two_eq_of_coreQuot φ,
    ← factorization_two_eq_of_coreQuot (MulEquiv.refl (↥M ⧸ pPrimeCore 2 ↥M))] at hkey
  exact hkey

theorem exact_of_pumped (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    {Y M : Subgroup X} (hMY : M ≤ Y)
    (hMpc : IsPComponent 2 (M.subgroupOf Y)) (htM : t ∈ normalizer (M : Set X)) (hJM : J ≤ M)
    {m : ℕ} (hnm : n ≤ m) (eM : ↥M ⧸ Open.fusionZStar ↥M ≃* alternatingGroup (Fin m)) :
    Open.fusionZStar ↥M = pPrimeCore 2 ↥M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have hZeven : 2 ∣ Nat.card ↥(Open.fusionZStar ↥M) := by
    obtain ⟨z, hz, hzO⟩ : ∃ z ∈ Open.fusionZStar ↥M, z ∉ pPrimeCore 2 ↥M := by
      by_contra h
      push Not at h
      exact hne (le_antisymm h (Sol78.pPrimeCore_le_fusionZStar _))
    have hzc : QuotientGroup.mk' (pPrimeCore 2 ↥M) z ∈ center (↥M ⧸ pPrimeCore 2 ↥M) := by
      rw [Sol78.fusionZStar_eq_comap, mem_comap] at hz
      exact hz
    have hZ2 : IsPGroup 2 (center (↥M ⧸ pPrimeCore 2 ↥M)) :=
      Sol78.center_isPGroup_two (pPrimeCore_quotient_pPrimeCore_eq_bot 2)
    obtain ⟨k, hk⟩ := hZ2 ⟨_, hzc⟩
    have hne1 : QuotientGroup.mk' (pPrimeCore 2 ↥M) z ≠ 1 := by
      rwa [QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
    have hk' : (QuotientGroup.mk' (pPrimeCore 2 ↥M) z) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk')
    have h2 : 2 ∣ orderOf (QuotientGroup.mk' (pPrimeCore 2 ↥M) z) := by
      rcases j with _ | j
      · rw [pow_zero, orderOf_eq_one_iff] at hj
        exact absurd hj hne1
      · rw [hj, pow_succ]
        exact dvd_mul_left 2 _
    have h3 := orderOf_map_dvd (QuotientGroup.mk' (pPrimeCore 2 ↥M)) z
    have h4 := orderOf_dvd_natCard (⟨z, hz⟩ : ↥(Open.fusionZStar ↥M))
    rw [Subgroup.orderOf_mk] at h4
    exact h2.trans (h3.trans h4)
  have hK₀even : Even (Nat.card ↥((Open.fusionZStar ↥M).map M.subtype)) := by
    rw [card_map_of_injective M.subtype_injective]
    exact even_iff_two_dvd.mpr hZeven
  have ht2 : t ^ 2 ^ 1 = 1 := by rw [pow_one, ← S.pair.1.1, pow_orderOf_eq_one]
  obtain ⟨u, huK₀, hu, hut⟩ :=
    exists_involution_commute_of_even ht2 (mem_normalizer_fusionZStar htM) hK₀even
  obtain ⟨u', hu'Z, rfl⟩ := huK₀
  have huM : (u' : X) ∈ UnbalancedLayer.coreActionKernel M := by
    refine ⟨le_normalizer u'.2, fun j hj => ?_⟩
    have hzc : QuotientGroup.mk' (pPrimeCore 2 ↥M) u' ∈ center (↥M ⧸ pPrimeCore 2 ↥M) := by
      have hu'Z' : u' ∈ Open.fusionZStar ↥M := hu'Z
      rw [Sol78.fusionZStar_eq_comap, mem_comap] at hu'Z'
      exact hu'Z'
    have hc := mem_center_iff.mp hzc (QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨j, hj⟩)
    have h1 : QuotientGroup.mk' (pPrimeCore 2 ↥M) ((⟨j, hj⟩ : ↥M)⁻¹ * u'⁻¹ * ⟨j, hj⟩ * u') = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_assoc _ _ (QuotientGroup.mk' _ u'),
        hc]
      group
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact ⟨_, h1, by simp⟩
  have hkey := S.factorization_two_le_of_kernel hT13 hML hSch hMY hMpc hJM hu (hMY u'.2)
    (mem_centralizer_singleton_iff.mpr hut) huM
  have hM := factorization_two_card_of_alt eM
  have hZpos : 0 < (Nat.card ↥(Open.fusionZStar ↥M)).factorization 2 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' hZeven
  have hJ := factorization_two_eq_of_coreQuot e
  have hAlt := (factorization_two_card_alt (by have := S.nine_le; omega) hnm).1
  omega

theorem odd_kernel_of_pumped (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    {Y M : Subgroup X} (hMY : M ≤ Y)
    (hMpc : IsPComponent 2 (M.subgroupOf Y)) (htY : t ∈ Y) (htM : t ∈ normalizer (M : Set X))
    (hJM : J ≤ M) {m : ℕ} (hnm : n < m)
    (eM : ↥M ⧸ Open.fusionZStar ↥M ≃* alternatingGroup (Fin m)) :
    ¬ Even (Nat.card ↥(Y ⊓ UnbalancedLayer.coreActionKernel M)) := by
  intro hev
  have ht2 : t ^ 2 ^ 1 = 1 := by rw [pow_one, ← S.pair.1.1, pow_orderOf_eq_one]
  have htK : t ∈ normalizer ((Y ⊓ UnbalancedLayer.coreActionKernel M : Subgroup X) : Set X) :=
    inf_mem_normalizer' (le_normalizer htY) (mem_normalizer_coreActionKernel htM)
  obtain ⟨u, ⟨huY, huM⟩, hu, hut⟩ := exists_involution_commute_of_even ht2 htK hev
  have hkey := S.factorization_two_le_of_kernel hT13 hML hSch hMY hMpc hJM hu huY
    (mem_centralizer_singleton_iff.mpr hut) huM
  have hM := factorization_two_card_of_alt eM
  have hJ := factorization_two_eq_of_coreQuot e
  have hAlt := (factorization_two_card_alt (by have := S.nine_le; omega) hnm.le).2 S.pair.2.1 hnm
  omega

theorem normalizer_of_pumped (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    {Y M : Subgroup X} (hMY : M ≤ Y)
    (hMpc : IsPComponent 2 (M.subgroupOf Y)) (htY : t ∈ Y) (htM : t ∈ normalizer (M : Set X))
    (hJM : J ≤ M) {m : ℕ} (hnm : n < m)
    (eM : ↥M ⧸ Open.fusionZStar ↥M ≃* alternatingGroup (Fin m)) :
    Y ≤ normalizer (M : Set X) := by
  classical
  intro h hh
  by_contra hne
  obtain ⟨hMhY, hMhpc⟩ := isPComponent_conj hMY hMpc hh
  have hne' : M ≠ M.map (MulAut.conj h).toMonoidHom := fun heq =>
    hne (mem_normalizer_iff_map_conj_eq.mpr heq.symm)
  have hle := GSThmB.B5a.le_coreActionKernel_of_ne hMY hMhY hMpc hMhpc hne'
  apply S.odd_kernel_of_pumped hT13 hML hSch hMY hMpc htY htM hJM hnm eM
  have h1 : Nat.card ↥(M.map (MulAut.conj h).toMonoidHom) ∣
      Nat.card ↥(Y ⊓ UnbalancedLayer.coreActionKernel M) := card_dvd_of_le (le_inf hMhY hle)
  have h2 : 2 ∣ Nat.card ↥(M.map (MulAut.conj h).toMonoidHom) := by
    rw [card_map_of_injective (MulAut.conj h).injective]
    by_contra h3
    have h4 := Nat.factorization_eq_zero_of_not_dvd h3
    have hM := factorization_two_card_of_alt eM
    have hAlt := (factorization_two_card_alt (by have := S.nine_le; omega) hnm.le).2
      S.pair.2.1 hnm
    omega
  exact even_iff_two_dvd.mpr (h2.trans h1)

theorem kernel_le_core_of_pumped (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    {Y M : Subgroup X} (hMY : M ≤ Y)
    (hMpc : IsPComponent 2 (M.subgroupOf Y)) (htY : t ∈ Y) (htM : t ∈ normalizer (M : Set X))
    (hJM : J ≤ M) {m : ℕ} (hnm : n < m)
    (eM : ↥M ⧸ Open.fusionZStar ↥M ≃* alternatingGroup (Fin m)) :
    Y ⊓ UnbalancedLayer.coreActionKernel M ≤ (pPrimeCore 2 ↥Y).map Y.subtype := by
  have hYN := S.normalizer_of_pumped hT13 hML hSch hMY hMpc htY htM hJM hnm eM
  have hodd := S.odd_kernel_of_pumped hT13 hML hSch hMY hMpc htY htM hJM hnm eM
  refine le_pPrimeCore_map inf_le_left (fun y hy => inf_mem_normalizer' (le_normalizer hy)
    (mem_normalizer_coreActionKernel (hYN hy))) ?_
  exact Nat.coprime_two_left.mpr (Nat.not_even_iff_odd.mp hodd)

end Sig36

end CFSG.ComponentClassification.SolMax
