module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitLocalBalance
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitGWCore
public import CFSG.ClassicalInvolution.Balance.LocalBalance

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.LocalBalance

variable {G : Type} [Group G] [Finite G]

theorem subgroupOf_oddCore_centralizer_le (C : Subgroup G) (e : C) :
    ((pPrimeCore 2 (centralizer ({(e : G)} : Set G))).map
        (centralizer ({(e : G)} : Set G)).subtype).subgroupOf C ≤
      (pPrimeCore 2 (centralizer ({e} : Set C))).map (centralizer ({e} : Set C)).subtype := by
  set O := (pPrimeCore 2 (centralizer ({(e : G)} : Set G))).map
    (centralizer ({(e : G)} : Set G)).subtype with hO
  apply le_map_pPrimeCore
  · intro x hx
    rw [mem_subgroupOf] at hx
    obtain ⟨y, -, hy⟩ := hx
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    have h := mem_centralizer_singleton_iff.mp y.2
    simp only [coe_mul]
    rw [← hy]
    exact h
  · intro c hc x hx
    rw [mem_subgroupOf] at hx ⊢
    have hc' : (c : G) ∈ centralizer ({(e : G)} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp hc)
    obtain ⟨y, hy, hyx⟩ := hx
    have hn : (pPrimeCore 2 (centralizer ({(e : G)} : Set G))).Normal := inferInstance
    refine ⟨⟨c, hc'⟩ * y * ⟨c, hc'⟩⁻¹, hn.conj_mem y hy _, ?_⟩
    simp only [coe_subtype, coe_mul, coe_inv]
    rw [← hyx]
    rfl
  · have h1 : Nat.card (O.subgroupOf C) ∣ Nat.card O := by
      rw [← Subgroup.card_map_of_injective C.subtype_injective, subgroupOf_map_subtype]
      exact Subgroup.card_dvd_of_le inf_le_left
    exact (odd_card_map_pPrimeCore _).of_dvd_nat h1

theorem eq_one_of_mul_self_of_mem_pPrimeCore {H : Type*} [Group H] [Finite H] {x : H}
    (hx2 : x * x = 1) (hxO : x ∈ pPrimeCore 2 H) : x = 1 := by
  have hdvd : orderOf x ∣ Nat.card (pPrimeCore 2 H) := by
    rw [← Subgroup.orderOf_mk x hxO]
    exact orderOf_dvd_natCard _
  have hodd : Odd (orderOf x) :=
    Nat.coprime_two_left.mp ((pPrimeCore_coprime_card (p := 2) (G := H)).coprime_dvd_right hdvd)
  have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, hx2])
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at hodd
    exact absurd hodd (by decide)

omit [Finite G] in
theorem conjSub_map {H : Type*} [Group H] (φ : G →* H) (g : G) (L : Subgroup G) :
    conjSub (φ g) (L.map φ) = (conjSub g L).map φ := by
  ext y
  simp only [conjSub, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨_, ⟨l, hl, rfl⟩, rfl⟩
    exact ⟨g * l * g⁻¹, ⟨l, hl, rfl⟩, by simp [map_mul, map_inv]⟩
  · rintro ⟨_, ⟨l, hl, rfl⟩, rfl⟩
    exact ⟨φ l, ⟨l, hl, rfl⟩, by simp [map_mul, map_inv]⟩

theorem commutator_deltaCore_le_of_isLocallyTwoBalanced {a : G} {J E : Subgroup G}
    (hJa : J ≤ centralizer ({a} : Set G))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G))))
    {K : Subgroup (centralizer ({a} : Set G) ⧸ pPrimeCore 2 (centralizer ({a} : Set G)))}
    (hK : K = (J.subgroupOf (centralizer ({a} : Set G))).map
      (QuotientGroup.mk' (pPrimeCore 2 (centralizer ({a} : Set G)))))
    (hbal : IsLocallyTwoBalanced (K ⧸ center K))
    (hE : E ≤ centralizer ({a} : Set G) ⊓ normalizer (J : Set G)) (hE4 : Nat.card E = 4)
    (hE2 : ∀ e ∈ E, e * e = 1) :
    ⁅J, (⨅ (e : G) (_ : e ∈ E) (_ : e ≠ 1), (pPrimeCore 2 (centralizer ({e} : Set G))).map
        (centralizer ({e} : Set G)).subtype) ⊓ centralizer ({a} : Set G)⁆ ≤
      (pPrimeCore 2 (centralizer ({a} : Set G))).map (centralizer ({a} : Set G)).subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  subst hK
  set C := centralizer ({a} : Set G) with hC
  set π := QuotientGroup.mk' (pPrimeCore 2 C) with hπ
  set W : Subgroup G := (⨅ (e : G) (_ : e ∈ E) (_ : e ≠ 1),
    (pPrimeCore 2 (centralizer ({e} : Set G))).map (centralizer ({e} : Set G)).subtype) ⊓ C
    with hW
  have hEC : E ≤ C := fun e he => (mem_inf.mp (hE he)).1
  have hWC : W ≤ C := inf_le_right
  set EC : Subgroup C := E.subgroupOf C with hECdef
  set WC : Subgroup C := W.subgroupOf C with hWCdef
  set JC : Subgroup C := J.subgroupOf C with hJCdef
  have h1 : WC ≤ deltaCore EC := by
    rw [deltaCore_eq_iInf_pPrimeCore]
    intro w hw
    simp only [mem_iInf]
    intro e he he1
    rw [hWCdef, mem_subgroupOf] at hw
    have hw1 := (mem_inf.mp hw).1
    simp only [mem_iInf] at hw1
    have hwe := hw1 (e : G) he (fun h => he1 (Subtype.ext h))
    exact subgroupOf_oddCore_centralizer_le C e (by rw [mem_subgroupOf]; exact hwe)
  have hEC2 : ∀ f ∈ EC, f * f = 1 := fun f hf => Subtype.ext (hE2 f hf)
  have h2 := map_deltaCore_le_of_surjective π (QuotientGroup.mk'_surjective _) hEC2
  set F : Subgroup (C ⧸ pPrimeCore 2 C) := EC.map π with hF
  have hO : CFSG.pPrimeCore 2 (C ⧸ pPrimeCore 2 C) = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot 2
  obtain ⟨K', hK', -, hJK', -⟩ := hJ
  rw [← hJK'] at hK'
  set K : Subgroup (C ⧸ pPrimeCore 2 C) := JC.map π with hK
  have hinj : ∀ x ∈ EC, π x = 1 → x = 1 := fun x hx h1 =>
    eq_one_of_mul_self_of_mem_pPrimeCore (hEC2 x hx) ((QuotientGroup.eq_one_iff x).mp h1)
  have hF4 : Nat.card F = 4 := by
    have hbij : Function.Bijective (π.subgroupMap EC) := by
      refine ⟨?_, π.subgroupMap_surjective EC⟩
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      rw [mem_bot]
      exact Subtype.ext (hinj x x.2 (congrArg Subtype.val (MonoidHom.mem_ker.mp hx)))
    rw [hF, ← Nat.card_congr (Equiv.ofBijective _ hbij), ← hE4]
    exact Nat.card_congr (subgroupOfEquivOfLe hEC).toEquiv
  have hF2 : ∀ f ∈ F, f * f = 1 := by
    rintro _ ⟨e, he, rfl⟩
    rw [← map_mul, hEC2 e he, map_one]
  have hFL : ∀ f ∈ F, conjSub f K = K := by
    rintro _ ⟨e, he, rfl⟩
    rw [hK, conjSub_map]
    congr 1
    have heN : (e : G) ∈ normalizer (J : Set G) := (mem_inf.mp (hE he)).2
    ext y
    rw [mem_conjSub_iff, hJCdef, mem_subgroupOf, mem_subgroupOf]
    constructor
    · intro hy
      have := (mem_normalizer_iff.mp heN _).mp hy
      simpa [mul_assoc] using this
    · intro hy
      have := (mem_normalizer_iff.mp (inv_mem heN) _).mp hy
      simpa [mul_assoc] using this
  set D : Subgroup (C ⧸ pPrimeCore 2 C) := deltaCore F with hD
  have hDF : ∀ f ∈ F, f ≠ 1 → D ≤ Assembly.Dichotomy.involutionOddCore f :=
    fun f hf hf1 => deltaCore_le_involutionOddCore hf hf1
  have hcomm : ∀ d ∈ D, ∀ x ∈ K, d * x = x * d := by
    by_cases hcen : ∃ f ∈ F, f ≠ 1 ∧ ∀ x ∈ K, f * x = x * f
    · obtain ⟨f, hfF, hf1, hfK⟩ := hcen
      have hKC : K ≤ centralizer ({f} : Set _) := fun x hx =>
        mem_centralizer_singleton_iff.mpr (hfK x hx).symm
      intro d hd
      exact commute_of_isComponent_centralizer (hDF f hfF hf1 hd) hKC
        (CFSG.LocalCores.component_overgroup hK' hKC)
    · push Not at hcen
      have hfaith : ∀ f ∈ F, f ≠ 1 → ¬ ∀ x ∈ K, f * x = x * f := by
        intro f hf hf1 h
        obtain ⟨x, hx, hxne⟩ := hcen f hf hf1
        exact hxne (h x hx)
      obtain ⟨f₀, hf₀F, hf₀1⟩ : ∃ f ∈ F, f ≠ 1 := by
        have : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by rw [hF4]; norm_num)
        obtain ⟨⟨f, hf⟩, hne⟩ := exists_ne (1 : F)
        exact ⟨f, hf, fun h => hne (Subtype.ext h)⟩
      have hDn : ∀ d ∈ D, conjSub d K = K := fun d hd =>
        conjSub_eq_of_mem_involutionOddCore hK' (hF2 f₀ hf₀F) (hFL f₀ hf₀F)
          (hDF f₀ hf₀F hf₀1 hd)
      exact commute_of_faithful hK' hbal hF4 hF2 hFL hfaith hDn hDF
  have h4 : ⁅JC, WC⁆ ≤ pPrimeCore 2 C := by
    rw [commutator_le]
    intro j hj w hw
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, ← hπ, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    have hwD : π w ∈ D := h2 ⟨w, h1 hw, rfl⟩
    have hjK : π j ∈ K := by rw [hK]; exact ⟨j, hj, rfl⟩
    exact (hcomm _ hwD _ hjK).symm
  have h5 : ⁅J, W⁆ = ⁅JC, WC⁆.map C.subtype := by
    rw [Subgroup.map_commutator, hJCdef, hWCdef, map_subgroupOf_eq_of_le hJa,
      map_subgroupOf_eq_of_le hWC]
  rw [h5]
  exact Subgroup.map_mono h4

end CFSG.ComponentClassification.GrSLit
