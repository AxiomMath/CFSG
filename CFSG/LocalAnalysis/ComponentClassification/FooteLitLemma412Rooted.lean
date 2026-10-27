module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma412Inner
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma49K
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitSec4KnownInputs

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ABGLocalTools GSThmB

variable {G : Type} [Group G] {L : Subgroup G}

section Action

variable {M : Subgroup G}

@[expose] noncomputable def footeAct (ε : M ⧸ pPrimeCore 2 M ≃* L ⧸ Open.fusionZStar L) :
    ↥(normalizer (M : Set G)) →* MulAut (L ⧸ Open.fusionZStar L) :=
  (MulAut.congr ε).toMonoidHom.comp (oddBarConj M)

@[expose] noncomputable def footePsi (ε : M ⧸ pPrimeCore 2 M ≃* L ⧸ Open.fusionZStar L) :
    ↥M →* L ⧸ Open.fusionZStar L :=
  ε.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 M))

theorem footePsi_surjective (ε : M ⧸ pPrimeCore 2 M ≃* L ⧸ Open.fusionZStar L) :
    Function.Surjective (footePsi ε) :=
  ε.surjective.comp (QuotientGroup.mk'_surjective _)

theorem footePsi_eq_one_iff (ε : M ⧸ pPrimeCore 2 M ≃* L ⧸ Open.fusionZStar L) (m : ↥M) :
    footePsi ε m = 1 ↔ m ∈ pPrimeCore 2 ↥M := by
  rw [footePsi, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_eq_one_iff _ ε.injective,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem footeAct_footePsi (ε : M ⧸ pPrimeCore 2 M ≃* L ⧸ Open.fusionZStar L)
    (x : ↥(normalizer (M : Set G))) (m : ↥M) :
    footeAct ε x (footePsi ε m) =
      footePsi ε ⟨(x : G) * m * (x : G)⁻¹, (mem_normalizer_iff.mp x.2 m).mp m.2⟩ := by
  rw [footeAct, footePsi, MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom, MulAut.congr_apply]
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [QuotientGroup.mk'_apply, oddBarConj_apply_mk]
  rfl

theorem mem_coreActionKernel_of_footeAct_eq_one
    (ε : M ⧸ pPrimeCore 2 M ≃* L ⧸ Open.fusionZStar L) {x : ↥(normalizer (M : Set G))}
    (hx : footeAct ε x = 1) : (x : G) ∈ coreActionKernel M := by
  apply mem_coreActionKernel_of_oddBarConj_eq_one
  have h1 : (MulAut.congr ε) (oddBarConj M x) = 1 := hx
  rwa [map_eq_one_iff _ (MulAut.congr ε).injective] at h1

theorem footeAct_eq_one_of_mem_coreActionKernel
    (ε : M ⧸ pPrimeCore 2 M ≃* L ⧸ Open.fusionZStar L) {x : ↥(normalizer (M : Set G))}
    (hx : (x : G) ∈ coreActionKernel M) : footeAct ε x = 1 := by
  rw [footeAct, MonoidHom.comp_apply, oddBarConj_eq_one_of_mem_coreActionKernel' hx, map_one]

theorem mem_sup_of_footeAct_mem_range (ε : M ⧸ pPrimeCore 2 M ≃* L ⧸ Open.fusionZStar L)
    {x : ↥(normalizer (M : Set G))}
    (hx : footeAct ε x ∈ (MulAut.conj : (L ⧸ Open.fusionZStar L) →* _).range) :
    (x : G) ∈ M ⊔ coreActionKernel M := by
  obtain ⟨s, hs⟩ := hx
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (ε.symm s)
  have hmN : (m : G) ∈ normalizer (M : Set G) := le_normalizer m.2
  have hΦm : footeAct ε ⟨m, hmN⟩ = MulAut.conj s := by
    rw [footeAct, MonoidHom.comp_apply, oddBarConj_eq_conj' m hmN]
    show MulAut.congr ε (MulAut.conj ((m : M ⧸ pPrimeCore 2 M))) = MulAut.conj s
    rw [MulAut.congr_conj, hm, MulEquiv.apply_symm_apply]
  have hC : footeAct ε ((⟨m, hmN⟩ : ↥(normalizer (M : Set G)))⁻¹ * x) = 1 := by
    rw [map_mul, map_inv, hΦm, hs, inv_mul_cancel]
  have hmw := mem_coreActionKernel_of_footeAct_eq_one ε hC
  have hmw' : (m : G)⁻¹ * x ∈ coreActionKernel M := by simpa using hmw
  rw [show (x : G) = (m : G) * ((m : G)⁻¹ * x) by group]
  exact mul_mem (mem_sup_left m.2) (mem_sup_right hmw')

end Action

variable [Finite G]

theorem four_le_card_of_isSylowOf_centralizer (hST : GSThmB.SuzukiTausskyInput)
    {C : Subgroup G} {E : Subgroup G} (hEC : E ≤ C) (hE2 : ∀ x ∈ E, x ^ 2 = 1)
    (hE8 : Nat.card E = 8) {u : G} (hu2 : u ^ 2 = 1) (huC : u ∉ C)
    (huN : u ∈ normalizer (C : Set G)) {P : Subgroup G}
    (hP : IsSylowOf 2 P (C ⊓ centralizer ({u} : Set G))) : 4 ≤ Nat.card P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu1 : u ≠ 1 := fun h1 => huC (h1 ▸ one_mem C)
  have hu : orderOf u = 2 := orderOf_eq_prime hu2 hu1
  have huu : u * u = 1 := by rw [← sq]; exact hu2
  set Z := C ⊔ zpowers u with hZ
  have hZC : Z ≤ normalizer (C : Set G) := sup_le le_normalizer (zpowers_le.mpr huN)
  have hup : IsPGroup 2 (zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu, pow_one])
  obtain ⟨S₀, hS₀, huS₀⟩ := exists_isSylowOf_ge_of_le (le_sup_right : zpowers u ≤ Z) hup
  have huS₀' : u ∈ S₀ := huS₀ (mem_zpowers u)
  set T := S₀ ⊓ C with hT
  have hTC : IsSylowOf 2 T C := hS₀.inf_of_le_normalizer le_sup_left hZC
  have huT : u ∈ normalizer (T : Set G) := by
    rw [mem_normalizer_iff]
    intro y
    have e1 := mem_normalizer_iff.mp (le_normalizer huS₀' : u ∈ normalizer (S₀ : Set G)) y
    have e2 := mem_normalizer_iff.mp huN y
    exact ⟨fun hy => mem_inf.mpr ⟨e1.mp (mem_inf.mp hy).1, e2.mp (mem_inf.mp hy).2⟩,
      fun hy => mem_inf.mpr ⟨e1.mpr (mem_inf.mp hy).1, e2.mpr (mem_inf.mp hy).2⟩⟩
  have hEp : IsPGroup 2 E := IsPGroup.of_card (n := 3) (by rw [hE8]; norm_num)
  obtain ⟨k, -, hk⟩ := exists_conj_le_of_isSylowOf hTC hEC hEp
  set F := conjugate E k with hF
  have hFT : F ≤ T := conjugate_le_of_forall hk
  have hF2 : ∀ x ∈ F, x ^ 2 = 1 := sq_eq_one_of_mem_conjugate hE2 k
  have hF8 : Nat.card F = 8 := by rw [hF, card_conjugate_eq_card, hE8]
  have hTeven : Even (Nat.card T) := by
    refine even_iff_two_dvd.mpr ((show 2 ∣ 8 by norm_num).trans ?_)
    rw [← hF8]
    exact Subgroup.card_dvd_of_le hFT
  obtain ⟨t₀, ht₀T, ht₀, ht₀u⟩ := exists_involution_commute_of_even hTeven hu2 huT
  by_contra hlt
  push Not at hlt
  have hTu : Nat.card ↥(T ⊓ centralizer ({u} : Set G)) ≤ 2 := by
    have hp' : IsPGroup 2 ↥(T ⊓ centralizer ({u} : Set G)) :=
      hTC.isPGroup.to_le inf_le_left
    obtain ⟨k', -, hk'⟩ := exists_conj_le_of_isSylowOf hP
      (inf_le_inf_right _ (inf_le_right : T ≤ C)) hp'
    have h1 : Nat.card ↥(T ⊓ centralizer ({u} : Set G)) ≤ Nat.card P := by
      rw [← card_conjugate_eq_card _ k']
      exact Subgroup.card_le_of_le (conjugate_le_of_forall hk')
    have h2 : Nat.card P ≠ 3 := by
      intro h3
      obtain ⟨m, hm⟩ := hP.isPGroup.exists_card_eq
      rw [hm] at h3
      rcases m with _ | _ | m
      · norm_num at h3
      · norm_num at h3
      · have : 4 ≤ 2 ^ (m + 2) := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ (m + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
    omega
  set A := T ⊓ centralizer ({u} : Set G) with hA
  have hsub : ((S₀ ⊓ centralizer ({u} : Set G) : Subgroup G) : Set G) ⊆
      (A : Set G) ∪ (fun a => a * u) '' (A : Set G) := by
    intro s hs
    have hsS₀ : s ∈ S₀ := (mem_inf.mp hs).1
    have hsu : s ∈ centralizer ({u} : Set G) := (mem_inf.mp hs).2
    have hsZ' : s ∈ ((zpowers u ⊔ C : Subgroup G) : Set G) := by
      rw [sup_comm]
      exact hS₀.le hsS₀
    rw [coe_mul_of_left_le_normalizer_right (zpowers u) C (zpowers_le.mpr huN)] at hsZ'
    obtain ⟨v, hv, c, hc, hvc⟩ := Set.mem_mul.mp hsZ'
    have hv' : v = 1 ∨ v = u := by
      by_cases hv1 : v = 1
      · exact Or.inl hv1
      · exact Or.inr (eq_of_mem_zpowers_of_sq hu2 hv1 hv)
    rcases hv' with hv1 | hv1
    · left
      rw [hv1, one_mul] at hvc
      rw [← hvc]
      exact mem_inf.mpr ⟨mem_inf.mpr ⟨hvc ▸ hsS₀, hc⟩, hvc ▸ hsu⟩
    · right
      rw [hv1] at hvc
      have hcS₀ : c ∈ S₀ := by
        have h1 := mul_mem (inv_mem huS₀') hsS₀
        rwa [← hvc, inv_mul_cancel_left] at h1
      have huu' : u ∈ centralizer ({u} : Set G) := mem_centralizer_singleton_iff.mpr rfl
      have hcu : c ∈ centralizer ({u} : Set G) := by
        have h1 := mul_mem (inv_mem huu') hsu
        rwa [← hvc, inv_mul_cancel_left] at h1
      refine ⟨c, mem_inf.mpr ⟨mem_inf.mpr ⟨hcS₀, hc⟩, hcu⟩, ?_⟩
      rw [← hvc]
      exact mem_centralizer_singleton_iff.mp hcu
  have hcard_le : Nat.card ↥(S₀ ⊓ centralizer ({u} : Set G)) ≤ 4 := by
    calc Nat.card ↥(S₀ ⊓ centralizer ({u} : Set G))
        = ((S₀ ⊓ centralizer ({u} : Set G) : Subgroup G) : Set G).ncard :=
          (Nat.card_coe_set_eq _)
      _ ≤ ((A : Set G) ∪ (fun a => a * u) '' (A : Set G)).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ (A : Set G).ncard + ((fun a => a * u) '' (A : Set G)).ncard := Set.ncard_union_le _ _
      _ ≤ (A : Set G).ncard + (A : Set G).ncard :=
          Nat.add_le_add_left (Set.ncard_image_le (Set.toFinite (A : Set G))) _
      _ = Nat.card A + Nat.card A := by rw [← Nat.card_coe_set_eq (A : Set G)]; rfl
      _ ≤ 4 := by omega
  have ht₀2 : t₀ ^ 2 = 1 := by rw [← ht₀]; exact pow_orderOf_eq_one t₀
  have ht₀1 : t₀ ≠ 1 := fun h1 => by rw [h1, orderOf_one] at ht₀; omega
  have hut₀ : u ≠ t₀ := fun h1 => huC (h1 ▸ (mem_inf.mp ht₀T).2)
  have hV := isKleinFour_sup_zpowers ht₀2 hu2 ht₀1 hu1 hut₀ ht₀u
  have hVS : zpowers t₀ ⊔ zpowers u ≤ S₀ ⊓ centralizer ({u} : Set G) := by
    refine sup_le (zpowers_le.mpr (mem_inf.mpr ⟨(mem_inf.mp ht₀T).1,
      mem_centralizer_singleton_iff.mpr ht₀u⟩)) (zpowers_le.mpr (mem_inf.mpr ⟨huS₀',
      mem_centralizer_singleton_iff.mpr rfl⟩))
  have hcard_ge := Subgroup.card_le_of_le hVS
  rw [hV.card_four] at hcard_ge
  have hFS₀ : F ≤ S₀ := hFT.trans inf_le_left
  exact card_inf_centralizer_ne_four hST hS₀.isPGroup hFS₀ hF2 hF8 huS₀' hu (by omega)

theorem exists_isKleinFour_of_le_range {X Q : Type*} [Group X] [Finite X] [Group Q] [Finite Q]
    (φ : X →* Q) (hker : ¬ 2 ∣ Nat.card φ.ker) {J : Subgroup Q} (hJ : J ≤ φ.range)
    (hJr : 2 ≤ CFSG.pRank 2 ↥J) : ∃ V : Subgroup X, IsKleinFour V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : CFSG.pRank 2 ↥J ≤ CFSG.pRank 2 ↥φ.range :=
    pRank_le_pRank_of_injective one_lt_two (Subgroup.inclusion hJ)
      (Subgroup.inclusion_injective hJ)
  have h2 : CFSG.pRank 2 ↥φ.range = CFSG.pRank 2 X := by
    rw [← UnbalancedLayer.pRank_eq_of_mulEquiv one_lt_two (QuotientGroup.quotientKerEquivRange φ),
      GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two φ.ker hker]
  have h3 : 2 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup X) := by
    rw [← SectionRank.pRank_eq_open_pRank_top]
    omega
  obtain ⟨E, -, hE, hEcard⟩ := SectionRank.exists_pRank one_lt_two (⊤ : Subgroup X)
  have hE4 : 4 ≤ Nat.card E := by
    rw [hEcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ CFSG.Open.pRank 2 (⊤ : Subgroup X) := Nat.pow_le_pow_right (by norm_num) h3
  obtain ⟨V, hV, -⟩ := exists_isKleinFour_le hE.2 hE4
  exact ⟨V, hV⟩

theorem FooteBadPair.exists_isKleinFour (h : FooteSec4 G L) (h47 : FooteThm47Statement)
    (hST : GSThmB.SuzukiTausskyInput) (hAsc : Foote5.AschbacherCentralCoreInput)
    (h2An : GSThmB.Solomon2AnInput) (hA5 : GSThmB.AschbacherTheorem5Input)
    (hE8 : FooteL2FourgroupE8) (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts)
    (hcalc : FooteSmallCentralizers) (hRO : FooteL2RootedOuter) {M : Subgroup G}
    (hM : IsFooteM L M) (hH : ∀ t : G, FooteInCC M t → ∀ u ∈ footeK L t, FooteInCC M u → u = t)
    (hPE : FooteEvenOrNormalizes M) {z g : G} (hp : FooteBadPair M z g) :
    ∃ V : Subgroup G, IsKleinFour V ∧
      V ≤ coreActionKernel M ⊓ centralizer ({g⁻¹ * z * g} : Set G) := by
  by_contra hno
  push Not at hno
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set u := g⁻¹ * z * g with hudef
  set C := coreActionKernel M with hCdef
  set D := C ⊓ centralizer ({u} : Set G) with hDdef
  set Mg := conjugate M g with hMg
  have hM' := isFooteM_conjugate h hM g
  have hu2 : u ^ 2 = 1 := by rw [← hp.orderOf_conj]; exact pow_orderOf_eq_one _
  have huN : u ∈ normalizer (M : Set G) := hp.2.2.2.1
  have huCN : u ∈ normalizer (C : Set G) := normalizer_le_normalizer_coreActionKernel M huN
  have huCg : u ∈ coreActionKernel Mg := hp.mem_coreActionKernel_conjugate
  have hNg : conjugate (normalizer (M : Set G)) g = normalizer (Mg : Set G) :=
    UnbalancedCorr.conjugate_normalizer M g
  have hCuN : centralizer ({u} : Set G) ≤ normalizer (Mg : Set G) := hNg ▸ hp.centralizer_le
  have huC : u ∉ C := fun h1 => hp.false_of_involution h h47 hST hM hp.orderOf_conj h1 huCg rfl
  have hinv : ∀ a ∈ D, ∀ b ∈ D, orderOf a = 2 → orderOf b = 2 → a * b = b * a → b = a := by
    intro a ha b hb ha2 hb2 hab
    by_contra hne
    have ha2' : a ^ 2 = 1 := by rw [← ha2]; exact pow_orderOf_eq_one a
    have hb2' : b ^ 2 = 1 := by rw [← hb2]; exact pow_orderOf_eq_one b
    have ha1 : a ≠ 1 := fun h1 => by rw [h1, orderOf_one] at ha2; omega
    have hb1 : b ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hb2; omega
    exact hno _ (isKleinFour_sup_zpowers ha2' hb2' ha1 hb1 hne hab)
      (sup_le (zpowers_le.mpr ha) (zpowers_le.mpr hb))
  obtain ⟨E₀, hE₀2, hE₀8, hE₀C⟩ := hM.exists_card_eight h
  obtain ⟨P, hP⟩ := exists_isSylowOf 2 D
  have hP4 : 4 ≤ Nat.card P :=
    four_le_card_of_isSylowOf_centralizer hST hE₀C hE₀2 hE₀8 hu2 huC huCN hP
  have hPp : IsPGroup 2 P := hP.isPGroup
  obtain ⟨w, hwP, hw, hwZ⟩ : ∃ w ∈ P, orderOf w = 2 ∧ ∀ x ∈ P, x * w = w * x := by
    have : Nontrivial ↥P := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    have hZnt : Nontrivial ↥(center ↥P) := hPp.center_nontrivial
    obtain ⟨m, hm⟩ := (hPp.to_subgroup (center ↥P)).exists_card_eq
    have hm1 : m ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hm
      exact (Finite.one_lt_card_iff_nontrivial.mpr hZnt).ne' hm
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := ↥(center ↥P)) 2
      (by rw [hm]; exact dvd_pow_self 2 hm1)
    refine ⟨((c : ↥P) : G), (c : ↥P).2, by rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hc],
      fun x hx => ?_⟩
    have h1 := mem_center_iff.mp c.2 ⟨x, hx⟩
    exact congrArg Subtype.val h1
  have hwD : w ∈ D := hP.le hwP
  have hw2 : w ^ 2 = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
  have hw1 : w ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hw; omega
  have hPinv : ∀ x ∈ P, x ^ 2 = 1 → x = 1 ∨ x = w := by
    intro x hx hx2
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · exact Or.inr (hinv x (hP.le hx) w hwD (orderOf_eq_prime hx2 hx1) hw (hwZ x hx) |>.symm)
  obtain ⟨y, hyP, hy4, hyw⟩ : ∃ y ∈ P, y ^ 4 = 1 ∧ y ^ 2 = w := by
    have hex : ∃ x ∈ P, x ^ 2 ≠ 1 := by
      by_contra hall
      push Not at hall
      have hsub : (P : Set G) ⊆ {1, w} := fun x hx => by
        rcases hPinv x hx (hall x hx) with h1 | h1
        · exact Or.inl h1
        · exact Or.inr h1
      have : Nat.card P ≤ 2 := by
        calc Nat.card P = (P : Set G).ncard := (Nat.card_coe_set_eq _)
          _ ≤ ({1, w} : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
          _ ≤ ({w} : Set G).ncard + 1 := Set.ncard_insert_le 1 {w}
          _ = 2 := by rw [Set.ncard_singleton]
      omega
    obtain ⟨x, hxP, hx2⟩ := hex
    obtain ⟨k, hk⟩ := hPp ⟨x, hxP⟩
    have hk' : x ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    obtain ⟨j, hj, hjx⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk')
    have hj2 : 2 ≤ j := by
      by_contra hj2
      push Not at hj2
      apply hx2
      have : orderOf x ∣ 2 := by
        rw [hjx]
        exact (pow_dvd_pow 2 (by omega : j ≤ 1)).trans (by rw [pow_one])
      exact orderOf_dvd_iff_pow_eq_one.mp this
    set y := x ^ 2 ^ (j - 2) with hydef
    have hdiv : 2 ^ j = 2 ^ (j - 2) * 4 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
      congr 1
      omega
    have hyo : orderOf y = 4 := by
      rw [hydef, orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero)
        (by rw [hjx, hdiv]; exact dvd_mul_right _ _), hjx, hdiv,
        Nat.mul_div_cancel_left _ (by positivity)]
    have hyP : y ∈ P := pow_mem hxP _
    have hy4 : y ^ 4 = 1 := by rw [← hyo]; exact pow_orderOf_eq_one y
    have hy2o : orderOf (y ^ 2) = 2 := by
      rw [orderOf_pow_of_dvd (by norm_num) (by rw [hyo]; norm_num), hyo]
    have hy2 : (y ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact hy4
    rcases hPinv (y ^ 2) (pow_mem hyP 2) hy2 with h1 | h1
    · rw [h1, orderOf_one] at hy2o
      omega
    · exact ⟨y, hyP, hy4, h1⟩
  have hwC : w ∈ C := (mem_inf.mp hwD).1
  have hwu : w * u = u * w := mem_centralizer_singleton_iff.mp (mem_inf.mp hwD).2
  have hwout : w ∉ Mg ⊔ coreActionKernel Mg := fun hin =>
    hp.false_of_inner h h47 hST hAsc h2An hA5 hE8 hK hcalc hM hH hPE hw hwC hwu hin
  have hCw : centralizer ({w} : Set G) ≤ normalizer (M : Set G) := by
    by_contra hCw
    obtain ⟨V, hV, hVD⟩ := exists_isKleinFour_of_footeInCC h h47 hST hAsc h2An hM ⟨hw, hwC, hCw⟩
      hu2 (mem_centralizer_singleton_iff.mpr hwu.symm) huN
    exact hno V hV hVD
  obtain ⟨-, ⟨ε⟩⟩ := hM'.quotient h
  have hPN : P ≤ normalizer (Mg : Set G) := (hP.le.trans inf_le_right).trans hCuN
  set Φ := footeAct (M := Mg) ε with hΦ
  set ψ := footePsi (M := Mg) ε with hψ
  have hwN : w ∈ normalizer (Mg : Set G) := hPN hwP
  have hPC : ∀ x ∈ P, x ∈ coreActionKernel Mg → x = 1 := by
    intro x hxP hxC
    by_contra hx1
    obtain ⟨k, hk⟩ := hPp ⟨x, hxP⟩
    have hk' : x ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    obtain ⟨j, -, hjx⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk')
    have hj1 : j ≠ 0 := by
      rintro rfl
      exact hx1 (orderOf_eq_one_iff.mp (by rw [hjx, pow_zero]))
    have hdiv : 2 ^ j = 2 ^ (j - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    have hx'o : orderOf (x ^ 2 ^ (j - 1)) = 2 := by
      rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero)
        (by rw [hjx, hdiv]; exact dvd_mul_right _ _), hjx, hdiv,
        Nat.mul_div_cancel_left _ (by positivity)]
    have hx'2 : (x ^ 2 ^ (j - 1)) ^ 2 = 1 := by
      have := pow_orderOf_eq_one (x ^ 2 ^ (j - 1))
      rwa [hx'o] at this
    rcases hPinv _ (pow_mem hxP _) hx'2 with h1 | h1
    · rw [h1, orderOf_one] at hx'o
      omega
    · exact hwout (mem_sup_right (h1 ▸ pow_mem hxC _))
  set ŷ := Φ ⟨y, hPN hyP⟩ with hŷ
  have hŷ2 : ŷ ^ 2 = Φ ⟨w, hwN⟩ := by
    rw [hŷ, ← map_pow]
    congr 1
    exact Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hyw)
  have hŷ4 : ŷ ^ 4 = 1 := by
    rw [hŷ, ← map_pow]
    rw [show (⟨y, hPN hyP⟩ : ↥(normalizer (Mg : Set G))) ^ 4 = 1 from
      Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hy4), map_one]
  have hŵ1 : ŷ ^ 2 ≠ 1 := fun h1 => hwout (mem_sup_right
    (mem_coreActionKernel_of_footeAct_eq_one ε (hŷ2 ▸ h1)))
  have hŵout : ŷ ^ 2 ∉ (MulAut.conj : (L ⧸ Open.fusionZStar L) →* _).range := fun h1 =>
    hwout (mem_sup_of_footeAct_mem_range ε (hŷ2 ▸ h1))
  obtain ⟨hJs, hJr, hJc⟩ := hRO _ h.footeFamilyType ŷ hŷ4 hŵ1 hŵout
  set F := MonoidHom.eqLocus (ŷ ^ 2).toMonoidHom (MonoidHom.id (L ⧸ Open.fusionZStar L)) with hF
  set X := Mg ⊓ centralizer ({w} : Set G) with hX
  set X' := X.subgroupOf Mg with hX'
  have hO : ∀ o : ↥Mg, o ∈ pPrimeCore 2 ↥Mg → ψ o = 1 := fun o ho =>
    (footePsi_eq_one_iff ε o).mpr ho
  have hXF : X'.map ψ = F := by
    apply le_antisymm
    · rintro _ ⟨m, hm, rfl⟩
      have hmw : (m : G) * w = w * m := mem_centralizer_singleton_iff.mp (mem_inf.mp hm).2
      show (ŷ ^ 2) (ψ m) = ψ m
      rw [hŷ2, hΦ, hψ, footeAct_footePsi]
      congr 1
      apply Subtype.ext
      show w * m * w⁻¹ = m
      rw [← hmw]
      group
    · intro s hs
      obtain ⟨m, rfl⟩ := footePsi_surjective ε s
      have hs' : Φ ⟨w, hwN⟩ (ψ m) = ψ m := by
        rw [← hŷ2]
        exact hs
      rw [hΦ, hψ, footeAct_footePsi] at hs'
      have h1 : ψ (m⁻¹ * ⟨w * m * w⁻¹, (mem_normalizer_iff.mp hwN m).mp m.2⟩) = 1 := by
        rw [map_mul, map_inv, hψ, hs', inv_mul_cancel]
      have h2 := (footePsi_eq_one_iff ε _).mp h1
      have h3 : (m : G)⁻¹ * (w * m * w⁻¹) ∈ oddCoreIn Mg := ⟨_, h2, rfl⟩
      obtain ⟨o, ho, hmo⟩ := exists_mul_mem_centralizer_of_odd (odd_card_oddCoreIn Mg) hw2
        (mem_normalizer_oddCoreIn hwN) h3
      obtain ⟨o', ho', rfl⟩ := ho
      refine ⟨m * o', ?_, ?_⟩
      · exact mem_subgroupOf.mpr (mem_inf.mpr ⟨(m * o').2, hmo⟩)
      · rw [map_mul, hO o' ho', mul_one]
  set J' := ⁅X', X'⁆ with hJ'
  have hJ'F : J'.map ψ = ⁅F, F⁆ := by rw [hJ', Subgroup.map_commutator, hXF]
  set J := J'.map Mg.subtype with hJ
  have hXMg : X ≤ Mg := inf_le_left
  have hJX : J ≤ X := by
    rw [hJ, hJ']
    have hcX : ⁅X', X'⁆ ≤ X' := (Subgroup.commutator_le).mpr fun a ha b hb => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
    refine (map_mono hcX).trans ?_
    rw [hX', Subgroup.subgroupOf_map_subtype]
    exact inf_le_left
  have hJN : J ≤ normalizer (M : Set G) := hJX.trans (inf_le_right.trans hCw)
  have hnormJ : ∀ v ∈ normalizer (Mg : Set G), v * w = w * v →
      ∀ j ∈ J, v * j * v⁻¹ ∈ J := by
    intro v hv hvw j hj
    obtain ⟨j', hj', rfl⟩ := mem_map.mp hj
    let σ : ↥Mg →* ↥Mg :=
      { toFun := fun m => ⟨v * m * v⁻¹, (mem_normalizer_iff.mp hv m).mp m.2⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
    have hσX : X'.map σ ≤ X' := by
      rintro _ ⟨m, hm, rfl⟩
      refine mem_subgroupOf.mpr (mem_inf.mpr ⟨(σ m).2, ?_⟩)
      have hmw : (m : G) * w = w * m := mem_centralizer_singleton_iff.mp (mem_inf.mp hm).2
      show v * m * v⁻¹ ∈ centralizer ({w} : Set G)
      rw [mem_centralizer_singleton_iff]
      have hvw' : v⁻¹ * w = w * v⁻¹ := (Commute.inv_left (hvw : Commute v w)).eq
      calc v * m * v⁻¹ * w = v * m * (v⁻¹ * w) := by group
        _ = v * m * (w * v⁻¹) := by rw [hvw']
        _ = v * (m * w) * v⁻¹ := by group
        _ = v * (w * m) * v⁻¹ := by rw [hmw]
        _ = (v * w) * m * v⁻¹ := by group
        _ = (w * v) * m * v⁻¹ := by rw [hvw]
        _ = w * (v * m * v⁻¹) := by group
    have hσJ : J'.map σ ≤ J' := by
      rw [hJ', Subgroup.map_commutator]
      exact commutator_mono hσX hσX
    exact ⟨σ j', hσJ ⟨j', hj', rfl⟩, rfl⟩
  have huu : u * u = 1 := by rw [← sq]; exact hu2
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  have huNg : u ∈ normalizer (Mg : Set G) := hCuN (mem_centralizer_singleton_iff.mpr rfl)
  have huJ : u ∈ normalizer (J : Set G) := by
    rw [mem_normalizer_iff]
    intro x
    refine ⟨hnormJ u huNg hwu.symm x, fun hx => ?_⟩
    have h1 := hnormJ u huNg hwu.symm _ hx
    have h2 : u * (u * x * u⁻¹) * u⁻¹ = x := by
      calc u * (u * x * u⁻¹) * u⁻¹ = (u * u) * x * (u * u)⁻¹ := by group
        _ = x := by rw [huu]; group
    rwa [h2] at h1
  set Y := ((J ⊓ C).subgroupOf Mg).map ψ with hYdef
  have hJ'mem : ∀ j' ∈ J', (j' : G) ∈ J := fun j' hj' => ⟨j', hj', rfl⟩
  have hYJ : Y ≤ ⁅F, F⁆ := by
    rw [← hJ'F]
    refine map_mono fun y hy => ?_
    obtain ⟨j', hj', hjy⟩ := mem_map.mp (mem_inf.mp (mem_subgroupOf.mp hy)).1
    rw [show y = j' from Subtype.ext hjy.symm]
    exact hj'
  have hConj : ∀ j ∈ J, ∀ y ∈ J ⊓ C, j * y * j⁻¹ ∈ J ⊓ C := by
    intro j hj y hy
    refine mem_inf.mpr ⟨mul_mem (mul_mem hj (mem_inf.mp hy).1) (inv_mem hj), ?_⟩
    exact (mem_normalizer_iff.mp (normalizer_le_normalizer_coreActionKernel M (hJN hj)) y).mp
      (mem_inf.mp hy).2
  have hYn : (Y.subgroupOf ⁅F, F⁆).Normal := by
    constructor
    intro a ha b
    obtain ⟨y', hy', hya⟩ := mem_map.mp (mem_subgroupOf.mp ha)
    have hb : (b : L ⧸ Open.fusionZStar L) ∈ J'.map ψ := by rw [hJ'F]; exact b.2
    obtain ⟨j', hj', hjb⟩ := mem_map.mp hb
    rw [mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hya, ← hjb,
      ← map_inv, ← map_mul, ← map_mul]
    refine ⟨j' * y' * j'⁻¹, mem_subgroupOf.mpr ?_, rfl⟩
    exact hConj _ (hJ'mem j' hj') _ (mem_subgroupOf.mp hy')
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hJs _ hYn with hY0 | hY1
  ·
    have hY0' : ∀ y ∈ (J ⊓ C).subgroupOf Mg, ψ y = 1 := by
      intro y hy
      have h2 : (⟨ψ y, hYJ ⟨y, hy, rfl⟩⟩ : ↥⁅F, F⁆) ∈ Y.subgroupOf ⁅F, F⁆ := ⟨y, hy, rfl⟩
      rw [hY0, mem_bot] at h2
      exact congrArg Subtype.val h2
    have hPfix : ∀ p (hp' : p ∈ P), Φ ⟨p, hPN hp'⟩ = 1 ∨ Φ ⟨p, hPN hp'⟩ = ŷ ^ 2 := by
      intro p hp'
      apply hJc
      intro jb hjb
      obtain ⟨j', hj', rfl⟩ := mem_map.mp (by rw [hJ'F]; exact hjb : jb ∈ J'.map ψ)
      rw [hΦ, hψ, footeAct_footePsi]
      have hpw : p * w = w * p := hwZ p hp'
      have hjJ := hJ'mem j' hj'
      have hpC : p ∈ C := (mem_inf.mp (hP.le hp')).1
      have hc : (⟨p * j' * p⁻¹, (mem_normalizer_iff.mp (hPN hp') j').mp j'.2⟩ : ↥Mg) * j'⁻¹ ∈
          (J ⊓ C).subgroupOf Mg := by
        rw [mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
        refine mem_inf.mpr ⟨mul_mem (hnormJ p (hPN hp') hpw _ hjJ) (inv_mem hjJ), ?_⟩
        have h1 : (j' : G) * p⁻¹ * (j' : G)⁻¹ ∈ C :=
          (mem_normalizer_iff.mp (normalizer_le_normalizer_coreActionKernel M (hJN hjJ)) _).mp
            (inv_mem hpC)
        rw [show p * (j' : G) * p⁻¹ * (j' : G)⁻¹ = p * ((j' : G) * p⁻¹ * (j' : G)⁻¹) by group]
        exact mul_mem hpC h1
      have h1 := hY0' _ hc
      rw [map_mul, map_inv, mul_inv_eq_one] at h1
      exact h1
    have hPsub : (P : Set G) ⊆ {1, w} := by
      intro p hp'
      rcases hPfix p hp' with h1 | h1
      · exact Or.inl (hPC p hp' (mem_coreActionKernel_of_footeAct_eq_one ε h1))
      · right
        rw [hŷ2] at h1
        have h2 : Φ ((⟨w, hwN⟩ : ↥(normalizer (Mg : Set G)))⁻¹ * ⟨p, hPN hp'⟩) = 1 := by
          rw [map_mul, map_inv, h1, inv_mul_cancel]
        have h3 := mem_coreActionKernel_of_footeAct_eq_one ε h2
        have h4 := hPC _ (mul_mem (inv_mem hwP) hp') (by simpa using h3)
        rw [inv_mul_eq_one] at h4
        exact h4.symm
    have : Nat.card P ≤ 2 := by
      calc Nat.card P = (P : Set G).ncard := (Nat.card_coe_set_eq _)
        _ ≤ ({1, w} : Set G).ncard := Set.ncard_le_ncard hPsub (Set.toFinite _)
        _ ≤ ({w} : Set G).ncard + 1 := Set.ncard_insert_le 1 {w}
        _ = 2 := by rw [Set.ncard_singleton]
    omega
  ·
    have hJY : ⁅F, F⁆ ≤ Y := fun x hx => by
      have h1 : (⟨x, hx⟩ : ↥⁅F, F⁆) ∈ Y.subgroupOf ⁅F, F⁆ := hY1 ▸ mem_top _
      exact h1
    set D' := (J ⊓ C) ⊓ centralizer ({u} : Set G) with hD'
    set D'' := D'.subgroupOf Mg with hD''
    set φ := ψ.comp D''.subtype with hφ
    have hker : ¬ 2 ∣ Nat.card φ.ker := by
      have hle : φ.ker.map D''.subtype ≤ pPrimeCore 2 ↥Mg := by
        rintro _ ⟨x, hx, rfl⟩
        exact (footePsi_eq_one_iff ε _).mp hx
      have h1 : Nat.card φ.ker ∣ Nat.card (pPrimeCore 2 ↥Mg) := by
        rw [← card_map_of_injective D''.subtype_injective]
        exact Subgroup.card_dvd_of_le hle
      intro h2
      exact (Nat.not_even_iff_odd.mpr (odd_card_pPrimeCore_two ↥Mg))
        (even_iff_two_dvd.mpr (h2.trans h1))
    have hrange : ⁅F, F⁆ ≤ φ.range := by
      intro x hx
      obtain ⟨y', hy', rfl⟩ := mem_map.mp (hJY hx)
      have hyJC : (y' : G) ∈ J ⊓ C := mem_subgroupOf.mp hy'
      set O := oddCoreIn Mg ⊓ (J ⊓ C) with hOdef
      have hOodd : Odd (Nat.card O) :=
        Odd.of_dvd_nat (odd_card_oddCoreIn Mg) (Subgroup.card_dvd_of_le inf_le_left)
      have huO : u ∈ normalizer (O : Set G) := by
        rw [mem_normalizer_iff]
        intro x
        have e1 := mem_normalizer_iff.mp (mem_normalizer_oddCoreIn huNg) x
        have e2 := mem_normalizer_iff.mp huJ x
        have e3 := mem_normalizer_iff.mp huCN x
        rw [hOdef, mem_inf, mem_inf, mem_inf, mem_inf, e1, e2, e3]
      have hd : (y' : G)⁻¹ * (u * y' * u⁻¹) ∈ O := by
        refine mem_inf.mpr ⟨?_, ?_⟩
        · have h1 := (mem_coreActionKernel.mp huCg).2 y' y'.2
          rw [huinv] at h1 ⊢
          rwa [show (y' : G)⁻¹ * u * y' * u = (y' : G)⁻¹ * (u * y' * u) by group] at h1
        · have h1 := (mem_normalizer_iff.mp huJ _).mp (mem_inf.mp hyJC).1
          have h2 := (mem_normalizer_iff.mp huCN _).mp (mem_inf.mp hyJC).2
          exact mem_inf.mpr ⟨mul_mem (inv_mem (mem_inf.mp hyJC).1) h1,
            mul_mem (inv_mem (mem_inf.mp hyJC).2) h2⟩
      obtain ⟨o, ho, hyo⟩ := exists_mul_mem_centralizer_of_odd hOodd hu2 huO hd
      obtain ⟨o'', ho'', ho''o⟩ := (mem_inf.mp ho).1
      have hoJC : o ∈ J ⊓ C := (mem_inf.mp ho).2
      have ho' : (o'' : G) = o := ho''o
      refine ⟨⟨y' * o'', mem_subgroupOf.mpr (mem_inf.mpr ⟨?_, ?_⟩)⟩, ?_⟩
      · rw [Subgroup.coe_mul, ho']
        exact mul_mem hyJC hoJC
      · rw [Subgroup.coe_mul, ho']
        exact hyo
      · show ψ (y' * o'') = ψ y'
        rw [map_mul, hO o'' ho'', mul_one]
    obtain ⟨V, hV⟩ := exists_isKleinFour_of_le_range φ hker hrange hJr
    set V' := (V.map D''.subtype).map Mg.subtype with hV'
    have hinj : Function.Injective (Mg.subtype.comp D''.subtype) :=
      Mg.subtype_injective.comp D''.subtype_injective
    have hV'K : IsKleinFour ↥V' := by
      refine isKleinFour_of_card_eq_four ?_ ?_
      · rw [hV', card_map_of_injective Mg.subtype_injective,
          card_map_of_injective D''.subtype_injective, hV.card_four]
      · rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
        rw [← map_pow, ← map_pow, sq_eq_one_of_isKleinFour hV hv, map_one, map_one]
    refine hno V' hV'K ?_
    rintro _ ⟨_, ⟨v, -, rfl⟩, rfl⟩
    have h1 := mem_subgroupOf.mp v.2
    exact mem_inf.mpr ⟨(mem_inf.mp (mem_inf.mp h1).1).2, (mem_inf.mp h1).2⟩

end CFSG.ComponentClassification.FooteLit
