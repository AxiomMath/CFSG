module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7SecL
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitLayerTools
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafL34Swap
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.PCore.PrimeSetCore
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bRows
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Basic
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpNotLie
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

namespace NFPump

theorem not_dvd_card_coreQuot {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : ¬ p ∣ Nat.card (G ⧸ Open.fusionZStar G)) :
    ¬ p ∣ Nat.card (G ⧸ pPrimeCore 2 G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := G ⧸ pPrimeCore 2 G with hQ
  have hO : pPrimeCore 2 Q = ⊥ := pPrimeCore_quotient_eq_bot Nat.prime_two
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp (Sol78.center_isPGroup_two hO)
  have hcard : Nat.card Q = Nat.card (Q ⧸ center Q) * Nat.card (center Q) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  rw [Nat.card_congr (Sol78.coreQuotientCenterEquiv G).toEquiv, hk] at hcard
  intro hdvd
  rw [hcard] at hdvd
  rcases (Nat.Prime.dvd_mul hp).mp hdvd with h1 | h1
  · exact h h1
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h1))

variable {H : Type*} [Group H] [Finite H]

theorem pPrimeCore_subgroupOf_of_isSubnormal {M : Subgroup H} (hM : M.IsSubnormal) :
    (pPrimeCore 2 H).subgroupOf M = pPrimeCore 2 ↥M := by
  apply map_injective M.subtype_injective
  rw [subgroupOf_map_subtype, UnbalancedCorr.map_pPrimeCore_eq_inf_of_isSubnormal hM, inf_comm]

theorem card_map_mk_of_isSubnormal {M : Subgroup H} (hM : M.IsSubnormal) :
    Nat.card (M.map (QuotientGroup.mk' (pPrimeCore 2 H))) = Nat.card (↥M ⧸ pPrimeCore 2 ↥M) := by
  rw [← relIndex_ker, QuotientGroup.ker_mk', relIndex, pPrimeCore_subgroupOf_of_isSubnormal hM]
  rfl

theorem card_coreQuot_dvd_card_map (K : Subgroup H) :
    Nat.card (↥K ⧸ pPrimeCore 2 ↥K) ∣ Nat.card (K.map (QuotientGroup.mk' (pPrimeCore 2 H))) := by
  rw [← relIndex_ker, QuotientGroup.ker_mk', relIndex]
  have hle : (pPrimeCore 2 H).subgroupOf K ≤ pPrimeCore 2 ↥K := by
    refine le_sSup ⟨inferInstance, ?_⟩
    have h1 : Nat.card ↥((pPrimeCore 2 H).subgroupOf K) ∣ Nat.card ↥(pPrimeCore 2 H) := by
      have h2 := card_map_of_injective (K := (pPrimeCore 2 H).subgroupOf K) K.subtype_injective
      rw [subgroupOf_map_subtype] at h2
      rw [← h2]
      exact card_dvd_of_le inf_le_left
    exact Nat.Coprime.coprime_dvd_right h1 pPrimeCore_coprime_card
  exact index_dvd_of_le hle

omit [Finite H] in
theorem card_sup_dvd_of_commute {A C : Subgroup H} (hc : ∀ x ∈ A, ∀ z ∈ C, x * z = z * x) :
    Nat.card ↥(A ⊔ C) ∣ Nat.card A * Nat.card C := by
  have hc' : ∀ (x : A) (z : C), Commute (A.subtype x) (C.subtype z) := fun x z => hc x x.2 z z.2
  have hrange := MonoidHom.noncommCoprod_range A.subtype C.subtype hc'
  rw [range_subtype, range_subtype] at hrange
  rw [← hrange, ← Nat.card_prod]
  exact card_range_dvd _

theorem not_dvd_seven_of_swap {t : H} (ht : orderOf t = 2) {M T K : Subgroup H}
    (hM : IsPComponent 2 M) (hne : M ≠ conjugate M t)
    (hTC : T ≤ (M ⊔ conjugate M t) ⊓ centralizer ({t} : Set H))
    (hT : IsPComponent 2 (T.subgroupOf ((M ⊔ conjugate M t) ⊓ centralizer ({t} : Set H))))
    (h7 : ¬ 7 ∣ Nat.card (↥T ⧸ Open.fusionZStar ↥T)) (hKM : K ≤ M ⊔ conjugate M t) :
    ¬ 7 ∣ Nat.card (↥K ⧸ pPrimeCore 2 ↥K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp7 : Nat.Prime 7 := by norm_num
  obtain ⟨e⟩ := CatLeaf.swap_case_type ht M hM hne T hTC hT
  have hM7 : ¬ 7 ∣ Nat.card (↥M ⧸ pPrimeCore 2 ↥M) := by
    apply not_dvd_card_coreQuot hp7 (by norm_num)
    rwa [← Nat.card_congr e.toEquiv]
  have hMt : IsPComponent 2 (conjugate M t) := UnbalancedLayer.isPComponent_conjugate hM t
  let eMt : ↥M ≃* ↥(conjugate M t) :=
    M.equivMapOfInjective (MulAut.conj t⁻¹).toMonoidHom (MulAut.conj t⁻¹).injective
  have hMt7 : ¬ 7 ∣ Nat.card (↥(conjugate M t) ⧸ pPrimeCore 2 ↥(conjugate M t)) := by
    rwa [← Nat.card_congr (Sol78.coreQuotCongr eMt).toEquiv]
  have hMs : M.IsSubnormal :=
    ((CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 M).mp hM).1
  have hMts : (conjugate M t).IsSubnormal :=
    ((CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 _).mp hMt).1
  have hcomm : ⁅M, conjugate M t⁆ ≤ pPrimeCore 2 H := by
    have hMne : ¬ M ≤ conjugate M t := fun hle =>
      hne (CatalogueBPrimeJoin.eq_of_le 2 M _ hM hMt hle)
    rcases CatalogueBPrimeJoin.contains_or_normalizes_core 2 M _ hM hMts with hle | ⟨-, hc⟩
    · exact absurd hle hMne
    · refine hc.trans ?_
      rw [UnbalancedCorr.map_pPrimeCore_eq_inf_of_isSubnormal hMs]
      exact inf_le_right
  set π := QuotientGroup.mk' (pPrimeCore 2 H) with hπ
  have hcπ : ∀ x ∈ M.map π, ∀ z ∈ (conjugate M t).map π, x * z = z * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨z, hz, rfl⟩
    have h1 : ⁅x, z⁆ ∈ pPrimeCore 2 H := hcomm (commutator_mem_commutator hx hz)
    have h2 : π ⁅x, z⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr h1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h2
    exact h2
  have hKle : K.map π ≤ M.map π ⊔ (conjugate M t).map π := by
    rw [← Subgroup.map_sup]
    exact map_mono hKM
  have hdvd : Nat.card (↥K ⧸ pPrimeCore 2 ↥K) ∣
      Nat.card ↥(M.map π) * Nat.card ↥((conjugate M t).map π) :=
    (card_coreQuot_dvd_card_map K).trans ((card_dvd_of_le hKle).trans
      (card_sup_dvd_of_commute hcπ))
  rw [card_map_mk_of_isSubnormal hMs, card_map_mk_of_isSubnormal hMts] at hdvd
  intro h7K
  rcases (Nat.Prime.dvd_mul hp7).mp (h7K.trans hdvd) with h1 | h1
  · exact hM7 h1
  · exact hMt7 h1

end NFPump

namespace Hyp52

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X} {y : X}

theorem B_le_normalizer_centralizer_secB0 (hc : h.SecCond y) :
    h.B ≤ normalizer (centralizer (h.secB0 y : Set X) : Set X) := fun _ hb =>
  B5a.mem_normalizer_centralizer (Hyp52.SecCond.B_le_G0 hc hb)

theorem V_le_layerIn_centralizer_secB0 (hc : h.SecCond y) :
    h.V ≤ layerIn (centralizer (h.secB0 y : Set X)) := by
  have h1 := GrSLit.pLayer_inf_centralizer_le_of_normalizes (B5a.isPGroup_B h)
    (B_le_normalizer_centralizer_secB0 hc)
  have hCB : centralizer (h.B : Set X) ≤ centralizer (h.secB0 y : Set X) :=
    centralizer_le (SetLike.coe_subset_coe.mpr (h.secB0_le_B y))
  rw [inf_of_le_right hCB] at h1
  exact (B5a.V_le_layerIn_centralizer h).trans h1

theorem exists_orbit_component_secJ0 (hc : h.SecCond y) :
    ∃ M : Subgroup X, M ≤ centralizer (h.secB0 y : Set X) ∧
      IsPComponent 2 (M.subgroupOf (centralizer (h.secB0 y : Set X))) ∧
      h.secJ0 y ≤ M ⊔ conjugate M h.a ∧
      IsPComponent 2 ((h.secJ0 y).subgroupOf
        ((M ⊔ conjugate M h.a) ⊓ centralizer ({h.a} : Set X))) ∧
      h.V ≤ M ⊔ conjugate M h.a := by
  have haY : h.a ∈ centralizer (h.secB0 y : Set X) := a_mem_centralizer_secB0
  have hTE : h.secJ0 y ≤ (pLayer ↥(centralizer (h.secB0 y : Set X)) 2).map
      (centralizer (h.secB0 y : Set X)).subtype := Seven.J0_le_Lay h y
  obtain ⟨M, hMY, hM, hJM, hJpc⟩ := UnbalancedCorr.exists_orbit_component h.orderOf_a haY
    (h.secJ0_le y) isPComponent_secJ0 hTE
  refine ⟨M, hMY, hM, hJM, hJpc, ?_⟩
  obtain ⟨-, hEN, -⟩ := UnbalancedCorr.iSup_conjugate_eq_orbit haY hMY hM
    (le_inf hJM ((h.secJ0_le y).trans inf_le_left)) hJpc
  have hJB : GSLit.fixedLayer h.J h.B ≤ h.secJ0 y :=
    (GSLit.fixedLayer_nested (B5a.isQuasisimple_J h) (h.B_le.trans inf_le_right)
      (B5a.isPGroup_B h) (h.secB0_le_B y)).1
  show layerIn (normalizer (h.B : Set X)) ≤ _
  rw [← h.conjClosure_eq]
  exact B5a.conjClosure_le (hJB.trans hJM) ((V_le_layerIn_centralizer_secB0 hc).trans hEN)

theorem eq_of_secJ0_le {M M' : Subgroup X} (hMY : M ≤ centralizer (h.secB0 y : Set X))
    (hM : IsPComponent 2 (M.subgroupOf (centralizer (h.secB0 y : Set X))))
    (hM'Y : M' ≤ centralizer (h.secB0 y : Set X))
    (hM' : IsPComponent 2 (M'.subgroupOf (centralizer (h.secB0 y : Set X))))
    (hJM : h.secJ0 y ≤ M) (hJM' : h.secJ0 y ≤ M') : M = M' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  set Y := centralizer (h.secB0 y : Set X) with hY
  have hne' : M.subgroupOf Y ≠ M'.subgroupOf Y := fun heq => hne (by
    have h1 := congrArg (Subgroup.map Y.subtype) heq
    rwa [map_subgroupOf_eq_of_le hMY, map_subgroupOf_eq_of_le hM'Y] at h1)
  obtain ⟨-, -, hc⟩ :=
    CatalogueBPrimeJoin.mutual_normalization_core_commutation 2 _ _ hM hM' hne'
  have : Group.IsPerfect ↥(h.secJ0 y) :=
    B5a.isPerfect_of_isPComponent_subgroupOf (h.secJ0_le y) isPComponent_secJ0
  set O := ((pPrimeCore 2 ↥(M.subgroupOf Y)).map (M.subgroupOf Y).subtype).map Y.subtype
    with hO
  have hJO : h.secJ0 y ≤ O := by
    rw [← B5a.commutator_self_of_isPerfect (J := h.secJ0 y)]
    refine (commutator_mono hJM hJM').trans ?_
    rw [← map_subgroupOf_eq_of_le hMY, ← map_subgroupOf_eq_of_le hM'Y, ← map_commutator]
    exact map_mono (hc.trans inf_le_left)
  have hcardO : Nat.card O = Nat.card (pPrimeCore 2 ↥(M.subgroupOf Y)) := by
    rw [hO, card_map_of_injective Y.subtype_injective,
      card_map_of_injective (M.subgroupOf Y).subtype_injective]
  have hodd : Nat.Coprime 2 (Nat.card ↥(h.secJ0 y)) := by
    have h1 : Nat.card ↥(h.secJ0 y) ∣ Nat.card O := card_dvd_of_le hJO
    rw [hcardO] at h1
    exact Nat.Coprime.coprime_dvd_right h1 pPrimeCore_coprime_card
  have htop : pPrimeCore 2 ↥(h.secJ0 y) = ⊤ :=
    top_unique (le_sSup ⟨inferInstance, by rwa [card_top]⟩)
  have hq := isQuasisimple_secJ0 (h := h) (y := y)
  have hnt := LocalCores.isQuasisimple_nontrivial hq
  have h1 : Nat.card (↥(h.secJ0 y) ⧸ pPrimeCore 2 ↥(h.secJ0 y)) = 1 := by
    rw [← index_eq_card, htop, index_top]
  exact (Finite.one_lt_card_iff_nontrivial.mpr hnt).ne' h1

theorem mem_normalizer_of_secJ0 {M : Subgroup X} (hMY : M ≤ centralizer (h.secB0 y : Set X))
    (hM : IsPComponent 2 (M.subgroupOf (centralizer (h.secB0 y : Set X))))
    (hJM : h.secJ0 y ≤ M) {x : X} (hxG : x ∈ h.secG0 y)
    (hxJ : x ∈ normalizer (h.secJ0 y : Set X)) : x ∈ normalizer (M : Set X) := by
  have hxY : conjugate (centralizer (h.secB0 y : Set X)) x = centralizer (h.secB0 y : Set X) :=
    conjugate_eq_of_mem_normalizer (B5a.mem_normalizer_centralizer hxG)
  obtain ⟨hle, hpc⟩ := Six.isPComponent_conjugate hMY hM x
  rw [hxY] at hle hpc
  have hJx : h.secJ0 y ≤ conjugate M x := by
    rw [← conjugate_eq_of_mem_normalizer hxJ]
    exact map_mono hJM
  exact mem_normalizer_of_conjugate_eq (eq_of_secJ0_le hMY hM hle hpc hJM hJx).symm

theorem card_secJ0_row515 (h15 : h.Row515) :
    Nat.card (↥((h.secJ0 y).subgroupOf (centralizer (h.secB0 y : Set X))) ⧸
        pPrimeCore 2 ↥((h.secJ0 y).subgroupOf (centralizer (h.secB0 y : Set X)))) = 360 ∧
      Nat.card (↥((h.secJ0 y).subgroupOf (centralizer (h.secB0 y : Set X))) ⧸
        Open.fusionZStar ↥((h.secJ0 y).subgroupOf (centralizer (h.secB0 y : Set X)))) = 360 := by
  set J' := (h.secJ0 y).subgroupOf (centralizer (h.secB0 y : Set X)) with hJ'
  have hJY : h.secJ0 y ≤ centralizer (h.secB0 y : Set X) := (h.secJ0_le y).trans inf_le_right
  obtain ⟨eJ⟩ := h15.1
  obtain ⟨e0⟩ := nonempty_secJ0_equiv (h := h) (y := y)
  let e1 : ↥J' ≃* ↥(h.secJ0 y) := subgroupOfEquivOfLe hJY
  let eQ := (Sol78.coreQuotCongr e1).trans (e0.trans eJ)
  have hO : Nat.card (↥J' ⧸ pPrimeCore 2 ↥J') = 360 := by
    rw [SolMax.card_of_mulEquiv_alt (by norm_num) eQ]
    decide
  refine ⟨hO, ?_⟩
  have hZ := B5a.center_eq_bot_of_equiv_alternating (by norm_num) eQ
  rw [← Nat.card_congr (Sol78.coreQuotientCenterEquiv _).toEquiv,
    Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot).toEquiv, hO]

theorem conjugate_a_eq_of_row515 (h15 : h.Row515) {M : Subgroup X}
    (hMY : M ≤ centralizer (h.secB0 y : Set X))
    (hM : IsPComponent 2 (M.subgroupOf (centralizer (h.secB0 y : Set X))))
    (hJM : h.secJ0 y ≤ M ⊔ conjugate M h.a)
    (hJpc : IsPComponent 2 ((h.secJ0 y).subgroupOf
      ((M ⊔ conjugate M h.a) ⊓ centralizer ({h.a} : Set X))))
    (hVM : h.V ≤ M ⊔ conjugate M h.a) : conjugate M h.a = M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  set Y := centralizer (h.secB0 y : Set X) with hY
  have haY : h.a ∈ Y := a_mem_centralizer_secB0
  set t : ↥Y := ⟨h.a, haY⟩ with ht
  have hto : orderOf t = 2 := by rw [Subgroup.orderOf_mk]; exact h.orderOf_a
  have hMaY : conjugate M h.a ≤ Y := UnbalancedCorr.conjugate_le_of_mem hMY haY
  have hLY : M ⊔ conjugate M h.a ≤ Y := sup_le hMY hMaY
  have hconj : conjugate (M.subgroupOf Y) t = (conjugate M h.a).subgroupOf Y :=
    conjugate_subgroupOf_eq M Y t
  have hsup : M.subgroupOf Y ⊔ conjugate (M.subgroupOf Y) t =
      (M ⊔ conjugate M h.a).subgroupOf Y := by
    rw [hconj, subgroupOf_sup hMY hMaY]
  have hCeq : (M.subgroupOf Y ⊔ conjugate (M.subgroupOf Y) t) ⊓ centralizer ({t} : Set Y) =
      ((M ⊔ conjugate M h.a) ⊓ centralizer ({h.a} : Set X)).subgroupOf Y := by
    rw [hsup, UGSChain.centralizer_mk_eq_subgroupOf haY]
    ext z
    simp only [mem_inf, mem_subgroupOf]
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, z.2⟩⟩
  have hne' : M.subgroupOf Y ≠ conjugate (M.subgroupOf Y) t := by
    rw [hconj]
    intro heq
    apply hne
    have h1 := congrArg (Subgroup.map Y.subtype) heq
    rw [map_subgroupOf_eq_of_le hMY, map_subgroupOf_eq_of_le hMaY] at h1
    exact h1.symm
  have hJL : h.secJ0 y ≤ (M ⊔ conjugate M h.a) ⊓ centralizer ({h.a} : Set X) :=
    le_inf hJM ((h.secJ0_le y).trans inf_le_left)
  have hTC : (h.secJ0 y).subgroupOf Y ≤
      (M.subgroupOf Y ⊔ conjugate (M.subgroupOf Y) t) ⊓ centralizer ({t} : Set Y) := by
    rw [hCeq]
    exact fun z hz => mem_subgroupOf.mpr (hJL (mem_subgroupOf.mp hz))
  have hT : IsPComponent 2 (((h.secJ0 y).subgroupOf Y).subgroupOf
      ((M.subgroupOf Y ⊔ conjugate (M.subgroupOf Y) t) ⊓ centralizer ({t} : Set Y))) := by
    rw [hCeq, UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff'
      (inf_le_left.trans hLY) 2 Nat.prime_two]
    exact hJpc
  have h7T : ¬ 7 ∣ Nat.card (↥((h.secJ0 y).subgroupOf Y) ⧸
      Open.fusionZStar ↥((h.secJ0 y).subgroupOf Y)) := by
    rw [(card_secJ0_row515 h15).2]
    norm_num
  have hKV : h.K ≤ h.V := le_sup_left.trans h.layer_eq_K.le
  have hKY : h.K ≤ Y := hKV.trans (hVM.trans hLY)
  have hKL : h.K.subgroupOf Y ≤ M.subgroupOf Y ⊔ conjugate (M.subgroupOf Y) t := by
    rw [hsup]
    exact fun z hz => mem_subgroupOf.mpr (hVM (hKV (mem_subgroupOf.mp hz)))
  have h7K : 7 ∣ Nat.card (↥(h.K.subgroupOf Y) ⧸ pPrimeCore 2 ↥(h.K.subgroupOf Y)) := by
    obtain ⟨eK⟩ := h15.2.2
    let e1 : ↥(h.K.subgroupOf Y) ≃* ↥h.K := subgroupOfEquivOfLe hKY
    rw [SolMax.card_of_mulEquiv_alt (by norm_num) ((Sol78.coreQuotCongr e1).trans eK)]
    decide
  exact NFPump.not_dvd_seven_of_swap hto hM hne' hTC hT h7T hKL h7K

theorem exists_component_row515 (hc : h.SecCond y) (h15 : h.Row515) :
    ∃ M : Subgroup X, M ≤ centralizer (h.secB0 y : Set X) ∧
      IsPComponent 2 (M.subgroupOf (centralizer (h.secB0 y : Set X))) ∧
      h.V ≤ M ∧ h.secJ0 y ≤ M ∧
      IsPComponent 2 ((h.secJ0 y).subgroupOf (M ⊓ centralizer ({h.a} : Set X))) ∧
      (∀ x ∈ h.secG0 y, x ∈ normalizer (h.secJ0 y : Set X) → x ∈ normalizer (M : Set X)) ∧
      conjugate M h.a = M := by
  obtain ⟨M, hMY, hM, hJM, hJpc, hVM⟩ := exists_orbit_component_secJ0 hc
  have hMa := conjugate_a_eq_of_row515 h15 hMY hM hJM hJpc hVM
  rw [hMa, sup_idem] at hJM hJpc hVM
  exact ⟨M, hMY, hM, hVM, hJM, hJpc,
    fun x hxG hxJ => mem_normalizer_of_secJ0 hMY hM hJM hxG hxJ, hMa⟩

end Hyp52

end CFSG.ComponentClassification.GSThmB
