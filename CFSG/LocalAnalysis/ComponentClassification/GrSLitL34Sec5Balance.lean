module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitGW35
public import CFSG.ClassicalInvolution.Balance.Basic
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitConn

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

theorem le_pPrimeCore_of_commute {X : Type} [Group X] [Finite X] {D : Subgroup X}
    (hodd : Odd (Nat.card D))
    (hO22 : ∀ m ∈ oTwoPrimeTwo X, ∀ d ∈ D, m * d * m⁻¹ * d⁻¹ ∈ pPrimeCore 2 X)
    (hM : ∀ M : Subgroup X, IsPComponent 2 M → ∀ m ∈ M, ∀ d ∈ D,
      m * d * m⁻¹ * d⁻¹ ∈ pPrimeCore 2 X) :
    D ≤ pPrimeCore 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 X) with hπ
  set K : Subgroup X := (centralizer ((D.map π : Subgroup _) : Set (X ⧸ pPrimeCore 2 X))).comap π
    with hK
  have hmemK : ∀ m : X, (∀ d ∈ D, m * d * m⁻¹ * d⁻¹ ∈ pPrimeCore 2 X) → m ∈ K := by
    intro m hm
    rw [hK, mem_comap, mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    have h1 : π (m * d * m⁻¹ * d⁻¹) = 1 := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hm d hd
    simp only [map_mul, map_inv] at h1
    have h2 : π m * π d = π d * π m := by
      calc π m * π d = π m * π d * (π m)⁻¹ * (π d)⁻¹ * (π d * π m) := by group
        _ = π d * π m := by rw [h1, one_mul]
    exact h2.symm
  have hL : lTwoPrimeTwo X ≤ K :=
    sup_le (sSup_le fun M hM' m hm => hmemK m (hM M hM' m hm)) fun m hm => hmemK m (hO22 m hm)
  have hF : generalizedFitting (X ⧸ pPrimeCore 2 X) ≤
      centralizer ((D.map π : Subgroup _) : Set (X ⧸ pPrimeCore 2 X)) := by
    rw [← map_lTwoPrimeTwo]
    exact (map_mono hL).trans (map_comap_le _ _)
  have := generalizedFitting_normal (X := X ⧸ pPrimeCore 2 X)
  set A := centralizer ((generalizedFitting (X ⧸ pPrimeCore 2 X) : Subgroup _) :
    Set (X ⧸ pPrimeCore 2 X)) with hA
  have hDA : D.map π ≤ A := by
    intro y hy
    rw [hA, mem_centralizer_iff]
    intro f hf
    exact (mem_centralizer_iff.mp (hF hf) y hy).symm
  have hAF : A ≤ generalizedFitting _ := centralizer_generalizedFitting_le _
  have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    (mem_centralizer_iff.mp ha b (hAF hb)).symm
  have hA2 : IsPGroup 2 A :=
    isPGroup_two_of_normal_comm (CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 2) hAab
  have hD2 : IsPGroup 2 (D.map π) := hA2.to_le hDA
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := ↥(D.map π))).mp hD2
  have hdvd : Nat.card (D.map π) ∣ Nat.card D := card_map_dvd D π
  have hk0 : k = 0 := by
    by_contra hk0
    rw [hk] at hdvd
    have h2 : 2 ∣ Nat.card D := (dvd_pow_self 2 hk0).trans hdvd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  rw [hk0, pow_zero] at hk
  intro d hd
  have hdm : π d ∈ D.map π := ⟨d, hd, rfl⟩
  have h1 : π d = 1 := by
    have := (card_eq_one.mp hk)
    rw [this] at hdm
    exact mem_bot.mp hdm
  rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1

variable {G : Type} [Group G] [Finite G]

theorem eq_of_pPrimeCore_sup_eq {M K : Subgroup G} (hKM : K ≤ M)
    (hKn : (K.subgroupOf M).Normal) (hperf : Group.IsPerfect M)
    (h : (pPrimeCore 2 M).map M.subtype ⊔ K = M) : K = M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O : Subgroup M := pPrimeCore 2 M
  set K' : Subgroup M := K.subgroupOf M with hK'
  have hsup : O ⊔ K' = ⊤ := by
    apply map_injective M.subtype_injective
    rw [Subgroup.map_sup, hK', map_subgroupOf_eq_of_le hKM, h, ← MonoidHom.range_eq_map,
      range_subtype]
  have hidx : Odd K'.index := by
    have h1 : K'.index = K'.relIndex O := by
      rw [← relIndex_top_right, ← hsup, relIndex_sup_right]
    rw [h1]
    exact (Nat.coprime_two_left.mp pPrimeCore_coprime_card).of_dvd_nat
      (index_dvd_card (K'.subgroupOf O))
  have htop := ClassicalInvolution.Balance.eq_top_of_perfect_of_odd_index
    hperf.commutator_eq_top K' hidx
  apply le_antisymm hKM
  intro m hm
  have : (⟨m, hm⟩ : M) ∈ K' := htop ▸ mem_top _
  exact this

omit [Finite G] in
theorem commutator_le_of_le_normalizer {M D : Subgroup G}
    (hD : D ≤ normalizer (M : Set G)) : ⁅M, D⁆ ≤ M := by
  rw [commutator_le]
  intro m hm d hd
  rw [commutatorElement_def]
  have h1 : d * m⁻¹ * d⁻¹ ∈ M := (mem_normalizer_iff.mp (hD hd) _).mp (inv_mem hm)
  rw [mul_assoc, mul_assoc]
  exact mul_mem hm (by rw [← mul_assoc]; exact h1)

omit [Finite G] in
theorem centralizer_zpowers_eq (x : G) :
    centralizer ((zpowers x : Subgroup G) : Set G) = centralizer ({x} : Set G) := by
  rw [zpowers_eq_closure, centralizer_closure]

theorem z2z2_mul_self : ∀ a : Multiplicative (ZMod 2) × Multiplicative (ZMod 2), a * a = 1 := by
  decide

theorem gwTwoBalanced_of_locallyTwoBalanced (hSol : SolomonCommutingCoreInput)
    (hloc : LocallyTwoBalanced G) : GWTwoBalanced G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro E hE x hx hxE
  obtain ⟨φ⟩ := hE
  have hE2 : ∀ e ∈ E, e * e = 1 := by
    intro e he
    have h2 : φ (⟨e, he⟩ * ⟨e, he⟩) = 1 := by
      rw [map_mul]
      exact z2z2_mul_self _
    exact congrArg Subtype.val (φ.injective (h2.trans (map_one φ).symm))
  have hE4 : Nat.card E = 4 := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_prod, Nat.card_eq_fintype_card,
      Fintype.card_multiplicative, ZMod.card]
  have hCx := centralizer_zpowers_eq x
  rw [← hCx]
  set C := centralizer ((zpowers x : Subgroup G) : Set G) with hC
  set Δ : Subgroup G := ⨅ (e : G) (_ : e ∈ E) (_ : e ≠ 1),
    (pPrimeCore 2 (centralizer ({e} : Set G))).map (centralizer ({e} : Set G)).subtype with hΔ
  set D : Subgroup G := Δ ⊓ C with hD
  set OC : Subgroup G := (pPrimeCore 2 C).map C.subtype with hOC
  show D ≤ OC
  by_contra hnot
  have hx1 : x ≠ 1 := by rintro rfl; simp at hx
  have hxx : x * x = 1 := by rw [← pow_two, ← hx, pow_orderOf_eq_one]
  have hsol : ∀ e ∈ E, e ≠ 1 →
      (⁅(oTwoPrimeTwo ↥C).map C.subtype,
          (pPrimeCore 2 (centralizer ({e} : Set G))).map (centralizer ({e} : Set G)).subtype ⊓ C⁆
          ≤ OC) ∧
        ∀ L : Subgroup G, L ≤ C → IsPComponent 2 (L.subgroupOf C) →
          (pPrimeCore 2 (centralizer ({e} : Set G))).map (centralizer ({e} : Set G)).subtype ⊓ C
            ≤ normalizer (L : Set G) ∧
          (¬ ⁅L, (pPrimeCore 2 (centralizer ({e} : Set G))).map
              (centralizer ({e} : Set G)).subtype ⊓ C⁆ ≤ (pPrimeCore 2 L).map L.subtype →
            zpowers e ⊓ normalizer (L : Set G) ≠ ⊥ ∧
              (pPrimeCore 2 L).map L.subtype ⊔ ⁅L, (pPrimeCore 2 (centralizer ({e} : Set G))).map
                (centralizer ({e} : Set G)).subtype ⊓ C⁆ = L ∧
              (pPrimeCore 2 L).map L.subtype ⊔ ⁅L, zpowers e ⊓ normalizer (L : Set G)⁆ = L) := by
    intro e he he1
    have hS : zpowers e ≠ ⊥ := fun h => he1 (zpowers_eq_bot.mp h)
    have hT : zpowers x ≠ ⊥ := fun h => hx1 (zpowers_eq_bot.mp h)
    have hcommS := (isElemTwo_zpowers (hE2 e he)).1
    have h2S := (isElemTwo_zpowers (hE2 e he)).2
    have hcommT := (isElemTwo_zpowers hxx).1
    have h2T := (isElemTwo_zpowers hxx).2
    have hST : ∀ a ∈ zpowers e, ∀ b ∈ zpowers x, a * b = b * a := by
      intro a ha b hb
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hb
      exact (Commute.zpow_zpow (show Commute e x from hxE e he) i j).eq
    have h := hSol G (zpowers e) (zpowers x) hS hT hcommS h2S hcommT h2T hST
    obtain ⟨⟨h1, -⟩, h2, -⟩ := h
    rw [centralizer_zpowers_eq e] at h1 h2
    exact ⟨h1, h2⟩
  have hEne : ∃ e ∈ E, e ≠ 1 := by
    by_contra hne
    push Not at hne
    have : Nat.card E = 1 := card_eq_one.mpr (eq_bot_iff.mpr fun e he => hne e he)
    omega
  obtain ⟨e₀, he₀, he₀1⟩ := hEne
  have hDe : ∀ e ∈ E, e ≠ 1 → D ≤
      (pPrimeCore 2 (centralizer ({e} : Set G))).map (centralizer ({e} : Set G)).subtype ⊓ C := by
    intro e he he1
    refine le_inf (inf_le_left.trans ?_) inf_le_right
    exact (iInf_le _ e).trans ((iInf_le _ he).trans (iInf_le _ he1))
  obtain ⟨M, hMC, hM, hMD⟩ : ∃ M : Subgroup G, M ≤ C ∧ IsPComponent 2 (M.subgroupOf C) ∧
      ¬ ⁅M, D⁆ ≤ (pPrimeCore 2 M).map M.subtype := by
    by_contra hall
    push Not at hall
    apply hnot
    have hDC : D ≤ C := inf_le_right
    have hle : D.subgroupOf C ≤ pPrimeCore 2 ↥C := by
      apply le_pPrimeCore_of_commute
      · rw [Nat.card_congr (subgroupOfEquivOfLe hDC).toEquiv]
        refine Odd.of_dvd_nat ?_ (card_dvd_of_le (hDe e₀ he₀ he₀1))
        refine Odd.of_dvd_nat ?_ (card_dvd_of_le inf_le_left)
        rw [card_map_of_injective (subtype_injective _)]
        exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
      · intro m hm d hd
        have hm' : (m : G) ∈ (oTwoPrimeTwo ↥C).map C.subtype := mem_map_of_mem C.subtype hm
        have h2 : C.subtype (m * d * m⁻¹ * d⁻¹) ∈ OC := by
          have := commutator_mem_commutator hm' (hDe e₀ he₀ he₀1 (mem_subgroupOf.mp hd))
          rw [commutatorElement_def] at this
          simpa using (hsol e₀ he₀ he₀1).1 this
        exact (mem_map_iff_mem C.subtype_injective).mp h2
      · intro M' hM' m hm d hd
        set M : Subgroup G := M'.map C.subtype with hMdef
        have hMC : M ≤ C := map_subtype_le _
        have hMs : M.subgroupOf C = M' := comap_map_eq_self_of_injective C.subtype_injective _
        have hMp : IsPComponent 2 (M.subgroupOf C) := hMs ▸ hM'
        have hmM : (m : G) ∈ M := mem_map_of_mem C.subtype hm
        have h2 : (m : G) * d * (m : G)⁻¹ * (d : G)⁻¹ ∈ (pPrimeCore 2 M).map M.subtype := by
          have := commutator_mem_commutator hmM (mem_subgroupOf.mp hd : (d : G) ∈ D)
          rw [commutatorElement_def] at this
          exact hall M hMC hMp this
        have h3 : C.subtype (m * d * m⁻¹ * d⁻¹) ∈ OC := by
          have e : C.subtype (m * d * m⁻¹ * d⁻¹) = (m : G) * d * (m : G)⁻¹ * (d : G)⁻¹ := by
            simp
          rw [e]
          exact GSLit.map_pPrimeCore_le_of_isPComponent hMC hMp h2
        exact (mem_map_iff_mem C.subtype_injective).mp h3
    have h := map_mono (f := C.subtype) hle
    rwa [map_subgroupOf_eq_of_le hDC] at h
  have hMN : ∀ e ∈ E, e ≠ 1 → e ∈ normalizer (M : Set G) ∧
      (pPrimeCore 2 M).map M.subtype ⊔ ⁅M, (pPrimeCore 2 (centralizer ({e} : Set G))).map
        (centralizer ({e} : Set G)).subtype ⊓ C⁆ = M ∧
      (pPrimeCore 2 M).map M.subtype ⊔ ⁅M, zpowers e⁆ = M := by
    intro e he he1
    have hmon : ¬ ⁅M, (pPrimeCore 2 (centralizer ({e} : Set G))).map
        (centralizer ({e} : Set G)).subtype ⊓ C⁆ ≤ (pPrimeCore 2 M).map M.subtype :=
      fun h => hMD ((commutator_mono le_rfl (hDe e he he1)).trans h)
    obtain ⟨hne, h2, h3⟩ := ((hsol e he he1).2 M hMC hM).2 hmon
    have heN : e ∈ normalizer (M : Set G) := by
      by_contra heN
      apply hne
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨hy1, hy2⟩ := mem_inf.mp hy
      rcases (LocalB.mem_zpowers_iff_of_involution e y (orderOf_eq_prime
        (by rw [pow_two, hE2 e he]) he1)).mp hy1 with h | h
      · exact h ▸ one_mem _
      · exact absurd (h ▸ hy2) heN
    have hzN : zpowers e ⊓ normalizer (M : Set G) = zpowers e :=
      inf_eq_left.mpr (zpowers_le.mpr heN)
    rw [hzN] at h3
    exact ⟨heN, h2, h3⟩
  have hperf : Group.IsPerfect M := by
    have h1 := ClassicalInvolution.LBalanceProof.isPerfect_of_isPComponent hM
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hMC).toMonoidHom)
      (subgroupOfEquivOfLe hMC).surjective
  obtain ⟨he₀N, hD₀, hz₀⟩ := hMN e₀ he₀ he₀1
  have hnormal : ∀ A : Subgroup G, A ≤ normalizer (M : Set G) →
      (⁅M, A⁆.subgroupOf M).Normal := by
    intro A hA
    rw [normal_subgroupOf_iff (commutator_le_of_le_normalizer hA)]
    intro k m hk hm
    have h1 : ⁅M, A⁆ ≤ (⁅M, A⁆).comap (MulAut.conj m).toMonoidHom := by
      rw [commutator_le]
      intro a ha b hb
      rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have e1 : m * ⁅a, b⁆ * m⁻¹ = ⁅m * a, b⁆ * ⁅m, b⁆⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e1]
      exact mul_mem (commutator_mem_commutator (mul_mem hm ha) hb)
        (inv_mem (commutator_mem_commutator hm hb))
    exact h1 hk
  have hEN : E ≤ normalizer (M : Set G) := by
    intro e he
    by_cases he1 : e = 1
    · rw [he1]; exact one_mem _
    · exact (hMN e he he1).1
  have hDeN : (pPrimeCore 2 (centralizer ({e₀} : Set G))).map
      (centralizer ({e₀} : Set G)).subtype ⊓ C ≤ normalizer (M : Set G) :=
    ((hsol e₀ he₀ he₀1).2 M hMC hM).1
  have hT1 : ⁅M, zpowers e₀⁆ = M := eq_of_pPrimeCore_sup_eq
    (commutator_le_of_le_normalizer (zpowers_le.mpr he₀N))
    (hnormal _ (zpowers_le.mpr he₀N)) hperf hz₀
  have hT2 : ⁅M, (pPrimeCore 2 (centralizer ({e₀} : Set G))).map
      (centralizer ({e₀} : Set G)).subtype ⊓ C⁆ = M :=
    eq_of_pPrimeCore_sup_eq (commutator_le_of_le_normalizer hDeN) (hnormal _ hDeN) hperf hD₀
  have hMx : M ≤ centralizer ({x} : Set G) := hCx ▸ hMC
  have hMpx : IsPComponent 2 (M.subgroupOf (centralizer ({x} : Set G))) := hCx ▸ hM
  have hT2x : ⁅M, (pPrimeCore 2 (centralizer ({e₀} : Set G))).map
      (centralizer ({e₀} : Set G)).subtype ⊓ centralizer ({x} : Set G)⁆ = M := hCx ▸ hT2
  have hU : GSUnbalancingTriple x e₀ M := by
    rw [gsUnbalancingTriple_iff]
    exact ⟨hx, orderOf_eq_prime (by rw [pow_two, hE2 e₀ he₀]) he₀1,
      (hxE e₀ he₀).symm, hMx, hMpx, hT1, hT2x⟩
  have hEC : E ≤ centralizer ({x} : Set G) := fun e he =>
    mem_centralizer_singleton_iff.mpr (hxE e he)
  have hbal := hloc M ⟨x, e₀, hU⟩ x hx hMx E (le_inf hEN hEC) ⟨φ⟩
  rw [← hCx] at hbal
  have hΔW : Δ ≤ wGroup E := by
    refine le_trans ?_ (le_iSup _ E)
    refine le_trans ?_ (le_iSup _ le_rfl)
    refine le_trans ?_ (le_iSup _ (by rw [hE4]))
    exact le_iSup (fun _ : ∀ b ∈ E, b * b = 1 => Δ) hE2
  have hle : ⁅M, D⁆ ≤ OC := (commutator_mono le_rfl (inf_le_inf_right C hΔW)).trans hbal
  apply hMD
  have hMD' : ⁅M, D⁆ ≤ M ⊓ OC := le_inf (commutator_le_of_le_normalizer
    ((hDe e₀ he₀ he₀1).trans hDeN)) hle
  refine hMD'.trans (UnbalancedGS.inf_le_map_pPrimeCore_two ?_ ?_)
  · exact fun m hm => UnbalancedGS.normalizer_le_normalizer_map_of_characteristic C
      (pPrimeCore 2 C) (le_normalizer (hMC hm))
  · rw [hOC, card_map_of_injective (subtype_injective _)]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card

end CFSG.ComponentClassification.GrSLit.GrS5
