module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEnd413Simple
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma412c
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitFrontier46
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotIso
public import CFSG.LocalAnalysis.ComponentInitial.EmptyLayerCharTwo
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.CharacterTheory.Semidihedral.InvolutionFusion
public import CFSG.CharacterTheory.Semidihedral.Local.LocalNormalizerQuotients
public import CFSG.GroupTheory.QuasiDihedralFusion.Basic
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKGFieldClass
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitStatement412
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Open.GorensteinHaradaSectionalRankFourMilestoneDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools
open Standing.Setup42
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

namespace HarrisEnd

theorem isQuasisimple_of_isSimpleGroup {D : Type*} [Group D] [IsSimpleGroup D]
    (hnab : ∃ a b : D, a * b ≠ b * a) : IsQuasisimple D := by
  have hc : center D = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center D) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      apply hab
      have ha : a ∈ center D := by rw [h]; exact Subgroup.mem_top a
      exact ((Subgroup.mem_center_iff.mp ha) b).symm
  let e : D ⧸ center D ≃* D :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  have hcomm : commutator D = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator D) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      apply hab
      have hmem : ⁅a, b⁆ ∈ commutator D :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_def, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
        at hmem
      exact hmem
    · exact h
  refine ⟨⟨hcomm⟩, e.isSimpleGroup, e.symm hnab.choose, e.symm hnab.choose_spec.choose,
    fun h => hnab.choose_spec.choose_spec (e.symm.injective ?_)⟩
  rw [map_mul, map_mul, h]

theorem isQuasisimple_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (hG : IsQuasisimple G) : IsQuasisimple H :=
  LocalCores.isQuasisimple_of_surjective hG e.toMonoidHom e.surjective (by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr e.injective]
    exact bot_le)

end HarrisEnd

namespace Standing.Setup42

variable {h : Standing t L p f} {hS : IsSylowOf 2 S (centralizer ({t} : Set X))}

theorem exists_closure_card_le_four (hσ : Setup42 h hS w z) {P : Subgroup X} (hPS : P ≤ S) :
    ∃ s : Finset X, s.card ≤ 4 ∧ closure (s : Set X) = P := by
  classical
  set H := centralizer ({t} : Set X) with hH
  have hPH : P ≤ H := hPS.trans hS.le
  set Q := (P.subgroupOf H).map h.rho with hQdef
  have hQ : Q ≤ (S.subgroupOf H).map h.rho := map_mono fun x hx => hPS hx
  obtain ⟨s, hs3, hsQ⟩ := hσ.gen3 Q hQ
  have hlift : ∀ q ∈ s, ∃ x : H, (x : X) ∈ P ∧ h.rho x = q := by
    intro q hq
    have hq' : q ∈ Q := hsQ ▸ subset_closure hq
    obtain ⟨x, hx, rfl⟩ := hq'
    exact ⟨x, hx, rfl⟩
  choose! lift hliftP hliftρ using hlift
  set s₀ : Finset X := s.image (fun q => (lift q : X)) with hs₀
  have hs₀P : (s₀ : Set X) ⊆ P := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
    exact hliftP q hq
  have hs₀card : s₀.card ≤ 3 := Finset.card_image_le.trans hs3
  have hdec : ∀ y ∈ P, ∃ r ∈ closure (s₀ : Set X), ∃ k : ℤ, y = r * t ^ k := by
    intro y hy
    have hyQ : h.rho ⟨y, hPH hy⟩ ∈ Q := ⟨⟨y, hPH hy⟩, hy, rfl⟩
    rw [← hsQ] at hyQ
    have hle : closure (s : Set (MulAut (Bar L))) ≤
        ((closure (s₀ : Set X)).subgroupOf H).map h.rho := by
      rw [closure_le]
      intro q hq
      exact ⟨lift q, mem_subgroupOf.mpr (subset_closure (Finset.mem_image_of_mem _ hq)),
        hliftρ q hq⟩
    obtain ⟨r, hr, hrρ⟩ := hle hyQ
    have hrP : (r : X) ∈ P := (closure_le P).mpr hs₀P hr
    have hmem : (r : X)⁻¹ * y ∈ S := S.mul_mem (S.inv_mem (hPS hrP)) (hPS hy)
    have h1 : h.rho ⟨(r : X)⁻¹ * y, hS.le hmem⟩ = 1 := by
      have : (⟨(r : X)⁻¹ * y, hS.le hmem⟩ : H) = r⁻¹ * ⟨y, hPH hy⟩ := rfl
      rw [this, map_mul, map_inv, hrρ, inv_mul_cancel]
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (h.mem_zpowers_of_rho_eq_one hS hmem h1)
    exact ⟨r, hr, k, by rw [hk]; group⟩
  by_cases htP : t ∈ P
  · refine ⟨insert t s₀, (Finset.card_insert_le _ _).trans (by omega), le_antisymm ?_ ?_⟩
    · rw [closure_le, Finset.coe_insert]
      exact Set.insert_subset htP hs₀P
    · intro y hy
      obtain ⟨r, hr, k, rfl⟩ := hdec y hy
      refine mul_mem ((Subgroup.closure_mono ?_) hr) (zpow_mem (subset_closure ?_) k)
      · rw [Finset.coe_insert]
        exact Set.subset_insert _ _
      · rw [Finset.coe_insert]
        exact Set.mem_insert _ _
  · refine ⟨s₀, by omega, le_antisymm ((closure_le P).mpr hs₀P) fun y hy => ?_⟩
    obtain ⟨r, hr, k, rfl⟩ := hdec y hy
    have hrP : r ∈ P := (closure_le P).mpr hs₀P hr
    have htk : t ^ k ∈ P := by
      have := P.mul_mem (P.inv_mem hrP) hy
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
    have ht2 : t ^ 2 = 1 := by rw [← h.config.orderOf_eq, pow_orderOf_eq_one]
    have htk1 : t ^ k = 1 := by
      rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
      · rw [zpow_mul, show t ^ (2 : ℤ) = 1 by exact_mod_cast ht2, one_zpow]
      · exfalso
        rw [zpow_add, zpow_mul, show t ^ (2 : ℤ) = 1 by exact_mod_cast ht2, one_zpow, one_mul,
          zpow_one] at htk
        exact htP htk
    rw [htk1, mul_one]
    exact hr

end Standing.Setup42

namespace Setting46e

theorem centralizer_layer_eq (hs : Setting46e t L p f S w z V i j)
    (h412 : IsLemma412 L p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j)) :
    centralizer (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :
        Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) =
      pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
  rw [← h412.pCore_eq.2, h412.pCore_eq.1]

theorem tBar_not_mem_centralizer_layer (hs : Setting46e t L p f S w z V i j)
    (h412 : IsLemma412 L p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j)) :
    hs.setup.tBar i j ∉ centralizer (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :
      Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) := by
  rw [hs.centralizer_layer_eq h412]
  exact hs.tBar_not_mem_pCore

theorem centralizer_layer_inf_centralizer_tBar (hs : Setting46e t L p f S w z V i j)
    (h412 : IsLemma412 L p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j)) :
    centralizer (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :
        Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ⊓ centralizer {hs.setup.tBar i j} =
      zpowers (betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
  rw [hs.centralizer_layer_eq h412]
  exact hs.pCore_inf_centralizer_tBar

theorem betaBar_ne_one (hs : Setting46e t L p f S w z V i j) :
    betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) ≠ 1 := by
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  set M := centralizer ({β} : Set X) with hM
  intro h1
  have hβ2 : β ^ 2 = 1 := hs.setup.sq_eq_one_of_mem_X (beta_mem_X i j)
  let b : ↥M := ⟨β, mem_centralizer_singleton_iff.mpr rfl⟩
  have hb2 : IsPGroup 2 (zpowers b) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers]
    exact ⟨1, by
      rw [pow_one]
      refine orderOf_eq_prime (Subtype.ext (by rw [Subgroup.coe_pow, hβ2, Subgroup.coe_one]))
        fun h => hs.beta.ne_one (congrArg Subtype.val h)⟩
  have := GSThmB.OddQuot.injOn_of_isPGroup hb2 (mem_zpowers b) (one_mem _)
    (by rw [map_one]; exact h1)
  exact hs.beta.ne_one (congrArg Subtype.val this)

theorem prime_p (hs : Setting46e t L p f S w z V i j) : p.Prime := hs.standing.config.prime

theorem p_ne_two (hs : Setting46e t L p f S w z V i j) : p ≠ 2 := hs.standing.config.ne_two

theorem even_f (hs : Setting46e t L p f S w z V i j) : Even f :=
  hs.standing.dihedral.even p f hs.standing.config.prime hs.standing.config.ne_two
    hs.standing.config.lieModel

theorem one_le_half (hs : Setting46e t L p f S w z V i j) : 1 ≤ f / 2 := by
  obtain ⟨k, hk⟩ := hs.even_f
  have := hs.standing.config.one_le
  omega

theorem sixteen_dvd (hs : Setting46e t L p f S w z V i j) : 16 ∣ p ^ (2 * (f / 2)) - 1 := by
  obtain ⟨k, hk⟩ := hs.even_f
  rw [show 2 * (f / 2) = f by omega]
  exact hs.standing.sixteen

theorem nonempty_KBar_equiv (hs : Setting46e t L p f S w z V i j)
    (h412 : IsLemma412 L p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j)) :
    Nonempty (↥(KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ≃*
      Bar (centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j))) := by
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  set M := centralizer ({β} : Set X) with hM
  set K := centralizerResidual L β with hK
  have hKM : K ≤ M := K_le_centralizer_beta i j
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥M) with hπ
  have hker : ¬ 2 ∣ Nat.card π.ker := GSThmB.OddQuot.not_two_dvd_card_ker
  obtain ⟨e₁⟩ := GSThmB.OddQuot.nonempty_pPrimeCore_equiv_of_surjective
    (π.subgroupMap (K.subgroupOf M)) (π.subgroupMap_surjective _)
    (GSThmB.OddQuot.not_two_dvd_card_ker_subgroupMap π hker _)
  have e₂ : ↥(KBar L β) ⧸ pPrimeCore 2 ↥(KBar L β) ≃* ↥(KBar L β) :=
    (QuotientGroup.quotientMulEquivOfEq h412.oddCore_KBar).trans QuotientGroup.quotientBot
  have hk1 : ¬ 2 ∣ Nat.card (subgroupOfEquivOfLe hKM).toMonoidHom.ker := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr (subgroupOfEquivOfLe hKM).injective, card_bot]
    norm_num
  obtain ⟨e₃⟩ := GSThmB.OddQuot.nonempty_pPrimeCore_equiv_of_surjective
    (subgroupOfEquivOfLe hKM).toMonoidHom (subgroupOfEquivOfLe hKM).surjective hk1
  exact ⟨e₂.symm.trans (e₁.symm.trans e₃)⟩

theorem lieModel_KBar (hs : Setting46e t L p f S w z V i j)
    (h412 : IsLemma412 L p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j)) :
    Blueprint.LieModel ↥(KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j)) .PSL 2 p (f / 2) := by
  obtain ⟨e⟩ := hs.nonempty_KBar_equiv h412
  exact lieModel_psl2_of_mulEquiv e hs.lemma45.lieModel

theorem isSylowOf_map_T (hs : Setting46e t L p f S w z V i j) :
    IsSylowOf 2 (((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w).subgroupOf
        (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))).map
        (QuotientGroup.mk' (pPrimeCore 2
          ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))))
      (centralizer ({hs.setup.tBar i j} :
        Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  set M := centralizer ({β} : Set X) with hM
  set T := zpowers t ⊔ (S ⊓ L) ⊔ zpowers w with hT
  have htM := hs.setup.t_mem_centralizer_beta i j
  have hT1 : IsSylowOf 2 T (centralizer ({t} : Set X) ⊓ M) := hs.lemma45.isSylowOf_T
  have hTM : T ≤ M := hT1.le.trans inf_le_right
  have hT2 : IsSylowOf 2 (T.subgroupOf M)
      (centralizer ({(⟨t, htM⟩ : ↥M)} : Set ↥M)) := by
    rw [← isSylowOf_map_subtype_iff M, map_subtype_centralizer htM, subgroupOf_map_subtype,
      inf_of_le_left hTM]
    exact hT1
  have hmap := HarrisLit.isSylowOf_map (QuotientGroup.mk' (pPrimeCore 2 ↥M)) hT2
  have htt : (⟨t, htM⟩ : ↥M) * ⟨t, htM⟩ = 1 := by
    have ht2 : t ^ 2 = 1 := by
      rw [← hs.standing.config.orderOf_eq]
      exact pow_orderOf_eq_one t
    exact Subtype.ext (by rw [Subgroup.coe_mul, ← sq, ht2, Subgroup.coe_one])
  rw [← GSThmB.OddQuot.centralizer_singleton_map_eq htt] at hmap
  exact hmap

theorem exists_closure_card_le_four (hs : Setting46e t L p f S w z V i j)
    {P : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))}
    (hP : P ≤ centralizer {hs.setup.tBar i j}) (hP2 : IsPGroup 2 P) :
    ∃ s : Finset (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)), s.card ≤ 4 ∧
      closure (s : Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) = P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let M := centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)
  let π := QuotientGroup.mk' (pPrimeCore 2 ↥M)
  let T := zpowers t ⊔ (S ⊓ L) ⊔ zpowers w
  have hsyl := hs.isSylowOf_map_T
  obtain ⟨Q, hQ, hPQ⟩ := exists_isSylowOf_ge hP2 hP
  obtain ⟨k, -, hk⟩ := hsyl.exists_mem_conj hQ
  let P₁ := P.map (MulAut.conj k⁻¹).toMonoidHom
  have hP₁T : P₁ ≤ (T.subgroupOf M).map π := by
    rintro _ ⟨x, hx, rfl⟩
    have := (hk x).mp (hPQ hx)
    rw [show (MulAut.conj k⁻¹).toMonoidHom x = k⁻¹ * x * k by simp]
    exact this
  let P₂ := T.subgroupOf M ⊓ P₁.comap π
  have hP₂map : P₂.map π = P₁ := GSThmB.OddQuot.map_inf_comap_eq hP₁T
  have hP₂S : P₂.map M.subtype ≤ S := by
    rintro _ ⟨x, hx, rfl⟩
    exact hs.setup.T_le hx.1
  obtain ⟨s₂, hs₂, hs₂c⟩ := hs.setup.exists_closure_card_le_four hP₂S
  obtain ⟨s₃, hs₃, hs₃c⟩ := HarrisEnd.exists_finset_closure_eq_of_map M.subtype_injective hs₂c
  refine ⟨(s₃.image π).image (MulAut.conj k), ?_, ?_⟩
  · exact Finset.card_image_le.trans (Finset.card_image_le.trans (hs₃.trans hs₂))
  · rw [Finset.coe_image, Finset.coe_image]
    have h1 : closure (π '' (s₃ : Set ↥M)) = P₁ := by
      rw [← MonoidHom.map_closure, hs₃c, hP₂map]
    have h3 : P₁.map (MulAut.conj k).toMonoidHom = P := by
      change (P.map (MulAut.conj k⁻¹).toMonoidHom).map (MulAut.conj k).toMonoidHom = P
      rw [map_map]
      convert map_id P
      ext x
      simp
    calc closure (⇑(MulAut.conj k) '' (π '' (s₃ : Set ↥M)))
        = closure ((MulAut.conj k).toMonoidHom '' (π '' (s₃ : Set ↥M))) := rfl
      _ = (closure (π '' (s₃ : Set ↥M))).map (MulAut.conj k).toMonoidHom :=
          (MonoidHom.map_closure _ _).symm
      _ = P₁.map (MulAut.conj k).toMonoidHom := by rw [h1]
      _ = P := h3

theorem _root_.CFSG.ComponentClassification.HarrisLit.HarrisEnd.factorization_two_card_quotient
    {G : Type*} [Group G] [Finite G] (N : Subgroup G) [N.Normal] (hN : Odd (Nat.card N)) :
    (Nat.card G).factorization 2 = (Nat.card (G ⧸ N)).factorization 2 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, Nat.factorization_mul Nat.card_pos.ne'
    Nat.card_pos.ne', Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd
      (fun h => (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr h)), add_zero]

theorem factorization_card_KBar (hs : Setting46e t L p f S w z V i j)
    (h412 : IsLemma412 L p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j))
    {m : ℕ} (e : ↥(S ⊓ L) ≃* DihedralGroup (2 ^ m)) :
    (Nat.card ↥(KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j))).factorization 2 = m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j) with hK
  obtain ⟨eK⟩ := hs.nonempty_KBar_equiv h412
  rw [Nat.card_congr eK.toEquiv, ← HarrisEnd.factorization_two_card_quotient _
    (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (Nat.prime_two.coprime_iff_not_dvd.mp
      pPrimeCore_coprime_card)))]
  have hD := hs.lemma45.isSylowOf_Dstar.card_eq
  have hidx := relIndex_mul_card (inf_le_left : S ⊓ L ⊓ K ≤ S ⊓ L)
  rw [hs.lemma45.relIndex_Dstar, Nat.card_congr e.toEquiv, DihedralGroup.nat_card, hD] at hidx
  have h2 : 2 ^ (Nat.card K).factorization 2 = 2 ^ m :=
    Nat.eq_of_mul_eq_mul_left (by norm_num) hidx
  exact Nat.pow_right_injective le_rfl h2

theorem exists_orderOf_eq_twoPart_KBar (hs : Setting46e t L p f S w z V i j)
    (h412 : IsLemma412 L p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j)) :
    ∃ d ∈ centralizer ({hs.setup.tBar i j} :
        Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))), ∃ e : ℕ, 3 ≤ e ∧
      orderOf d = 2 ^ e ∧
      2 ^ e = 2 ^ (Nat.card ↥(KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j))).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm, ⟨e⟩⟩ := hs.setup.dihedral
  let M := centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)
  let π := QuotientGroup.mk' (pPrimeCore 2 ↥M)
  let γ : X := (e.symm (DihedralGroup.r 1) : ↥(S ⊓ L))
  have hγD : γ ∈ S ⊓ L := (e.symm (DihedralGroup.r 1)).2
  have hγM : γ ∈ M := hs.setup.D_le_centralizer_beta i j hγD
  have hγord : orderOf γ = 2 ^ m := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
  have htM := hs.setup.t_mem_centralizer_beta i j
  have hγt : (⟨γ, hγM⟩ : ↥M) * ⟨t, htM⟩ = ⟨t, htM⟩ * ⟨γ, hγM⟩ :=
    Subtype.ext (mem_centralizer_singleton_iff.mp (hs.sylow.le hγD.1))
  refine ⟨π ⟨γ, hγM⟩, ?_, m, hm, ?_, ?_⟩
  · rw [mem_centralizer_singleton_iff]
    change π ⟨γ, hγM⟩ * π ⟨t, htM⟩ = π ⟨t, htM⟩ * π ⟨γ, hγM⟩
    rw [← map_mul, ← map_mul, hγt]
  · have hord : orderOf (⟨γ, hγM⟩ : ↥M) = 2 ^ m := by rw [Subgroup.orderOf_mk, hγord]
    have hp : IsPGroup 2 (zpowers (⟨γ, hγM⟩ : ↥M)) := by
      rw [IsPGroup.iff_card, Nat.card_zpowers, hord]
      exact ⟨m, rfl⟩
    have hc := GSThmB.OddQuot.card_map_of_isPGroup hp
    rw [MonoidHom.map_zpowers, Nat.card_zpowers, Nat.card_zpowers, hord] at hc
    exact hc
  · rw [hs.factorization_card_KBar h412 e]

theorem isOfType_layer_of_isSimpleGroup (hs : Setting46e t L p f S w z V i j)
    (h412 : IsLemma412 L p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j))
    [IsSimpleGroup ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))] :
    IsOfType (HarrisF p) ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) := by
  rcases h412.lemma46d with h | ⟨K₁, K₂, hsup, hinf, hcomm, -, ⟨e₁⟩, ⟨e₂⟩, hlie, -, -⟩
  · exact h.2
  · exfalso
    set E := layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) with hE
    have hnt : ∀ {Y : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))},
        Nonempty (↥Y ≃* ↥(KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j))) → Y ≠ ⊥ := by
      intro Y ⟨e⟩ hY
      obtain ⟨a, b, hab⟩ := nonabelian_of_lieModel_psl2 hlie
      have h1 : Nat.card ↥(KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j)) = 1 := by
        rw [← Nat.card_congr e.toEquiv, hY, card_bot]
      have : Subsingleton ↥(KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :=
        (Nat.card_eq_one_iff_unique.mp h1).1
      exact hab (Subsingleton.elim _ _)
    have hK₁E : K₁ ≤ E := hsup ▸ le_sup_left
    have hK₂E : K₂ ≤ E := hsup ▸ le_sup_right
    have hn : (K₁.subgroupOf E).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [mem_subgroupOf] at hn ⊢
      have hgN : (g : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∈ normalizer (K₁ : Set _) := by
        have hle : K₁ ⊔ K₂ ≤ normalizer (K₁ : Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) :=
          sup_le le_normalizer (fun y hy => Subgroup.centralizer_le_normalizer _
            (mem_centralizer_iff.mpr fun x hx => (mem_centralizer_iff.mp (hcomm hx) y hy).symm))
        exact hle (by rw [hsup]; exact g.2)
      exact (mem_normalizer_iff.mp hgN n).mp hn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K₁.subgroupOf E) with h | h
    · rw [subgroupOf_eq_bot, disjoint_iff, inf_of_le_left hK₁E] at h
      exact hnt ⟨e₁⟩ h
    · apply hnt ⟨e₂⟩
      rw [eq_bot_iff, ← hinf]
      intro x hx
      refine ⟨?_, hx⟩
      have : (⟨x, hK₂E hx⟩ : ↥E) ∈ K₁.subgroupOf E := h ▸ mem_top _
      exact this

theorem not_lieModel_L4U4_of_isSimpleGroup (hs : Setting46e t L p f S w z V i j)
    (h412 : IsLemma412 L p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j))
    (h47 : IsLemma47 p (w ^ (orderOf w / 2) * t ^ i * z ^ j))
    [IsSimpleGroup ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))] :
    ∀ k : ℕ, 1 ≤ k →
      ¬ Blueprint.LieModel ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) .PSL 4 p k ∧
      ¬ Blueprint.LieModel ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) .PSU 4 p k := by
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  set M := centralizer ({β} : Set X) with hM
  set E := layer (MBar β) with hE
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥M) with hπ
  have hKE := hs.KBar_le_layer
  obtain ⟨a, b, hab⟩ := nonabelian_of_lieModel_psl2 (hs.lieModel_KBar h412)
  have hEnab : ∃ a b : ↥E, a * b ≠ b * a := ⟨⟨a, hKE a.2⟩, ⟨b, hKE b.2⟩, fun h => hab
    (Subtype.ext (by have := congrArg Subtype.val h; simpa using this))⟩
  have hEq : IsQuasisimple ↥E := HarrisEnd.isQuasisimple_of_isSimpleGroup hEnab
  have hcomp : IsComponent E :=
    ⟨hEq, (@normal_of_characteristic _ _ E LocalCores.layer_characteristic).isSubnormal⟩
  obtain ⟨J, hJ, hJE⟩ :=
    LocalAnalysis.ComponentInitial.exists_isPComponent_of_isComponent 2 hcomp
  have hker : ¬ 2 ∣ Nat.card π.ker := GSThmB.OddQuot.not_two_dvd_card_ker
  have hOE : pPrimeCore 2 ↥E = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pPrimeCore 2 ↥E) with h | h
    · exact h
    · exfalso
      have hodd := pPrimeCore_coprime_card (p := 2) (G := ↥E)
      rw [h, card_top] at hodd
      have heven : 2 ∣ Nat.card ↥(KBar L β) :=
        even_iff_two_dvd.mp (even_card_of_lieModel_psl2 hs.p_ne_two (hs.lieModel_KBar h412))
      have hdvd : Nat.card ↥(KBar L β) ∣ Nat.card ↥E := by
        rw [← Nat.card_congr (subgroupOfEquivOfLe hKE).toEquiv]
        exact Subgroup.card_subgroup_dvd_card _
      exact Nat.prime_two.coprime_iff_not_dvd.mp hodd (heven.trans hdvd)
  have hZE : Open.fusionZStar ↥E = ⊥ := by
    rw [eq_bot_iff]
    intro l hl
    rw [GSThmB.OddQuot.mem_fusionZStar_iff, hOE] at hl
    have hcen : l ∈ center ↥E := mem_center_iff.mpr fun m => by
      have := hl m
      rw [mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this.symm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥E) with h | h
    · rw [h] at hcen
      exact hcen
    · exfalso
      obtain ⟨x, y, hxy⟩ := hEnab
      apply hxy
      have hx : x ∈ center ↥E := by rw [h]; exact mem_top x
      exact ((mem_center_iff.mp hx) y).symm
  have hk1 : ¬ 2 ∣ Nat.card (MulEquiv.subgroupCongr hJE).toMonoidHom.ker := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr (MulEquiv.subgroupCongr hJE).injective, card_bot]
    norm_num
  obtain ⟨eZ⟩ := GSThmB.OddQuot.nonempty_quotient_fusionZStar_equiv π hker J
  obtain ⟨eZ₂⟩ := GSThmB.OddQuot.nonempty_fusionZStar_equiv_of_surjective
    (MulEquiv.subgroupCongr hJE).toMonoidHom (MulEquiv.subgroupCongr hJE).surjective hk1
  have eZ' : ↥J ⧸ Open.fusionZStar ↥J ≃* ↥E :=
    eZ.trans (eZ₂.trans ((QuotientGroup.quotientMulEquivOfEq hZE).trans QuotientGroup.quotientBot))
  obtain ⟨eO⟩ := GSThmB.OddQuot.nonempty_pPrimeCore_equiv_of_surjective (π.subgroupMap J)
    (π.subgroupMap_surjective J) (GSThmB.OddQuot.not_two_dvd_card_ker_subgroupMap π hker J)
  obtain ⟨eO₂⟩ := GSThmB.OddQuot.nonempty_pPrimeCore_equiv_of_surjective
    (MulEquiv.subgroupCongr hJE).toMonoidHom (MulEquiv.subgroupCongr hJE).surjective hk1
  have eO' : ↥J ⧸ pPrimeCore 2 ↥J ≃* ↥E :=
    eO.trans (eO₂.trans ((QuotientGroup.quotientMulEquivOfEq hOE).trans QuotientGroup.quotientBot))
  have h2q : IsTwoQuasisimple ↥J :=
    ⟨ClassicalInvolution.LBalanceProof.isPerfect_of_isPComponent hJ,
      HarrisEnd.isQuasisimple_of_mulEquiv eO'.symm hEq⟩
  intro k hk
  have hno := h47 J hJ k hk
  refine ⟨fun hL => hno ⟨h2q, ↥E, inferInstance, Or.inl hL, ⟨eZ'⟩⟩,
    fun hU => hno ⟨h2q, ↥E, inferInstance, Or.inr hU, ⟨eZ'⟩⟩⟩

end Setting46e

end CFSG.ComponentClassification.HarrisLit
