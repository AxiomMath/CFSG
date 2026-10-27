module

public import CFSG.Assembly.Defs
import CFSG.Assembly.OddCoreElimination.TwoGroups
import CFSG.LocalAnalysis.ComponentInitial.IsolatedInvolutionSplit

public section

namespace CFSG.Assembly.Dichotomy

variable {G : Type*} [Group G]

theorem two_le_and_orderOf_sq_pow_eq_two {r : G} {m : ℕ} (hm : orderOf r = 2 ^ m)
    (hr : r ^ 2 ≠ 1) : 2 ≤ m ∧ orderOf ((r ^ 2 ^ (m - 2)) ^ 2) = 2 := by
  have h2 : 2 ≤ m := by
    by_contra hlt
    apply hr
    rw [← orderOf_dvd_iff_pow_eq_one, hm]
    interval_cases m <;> norm_num
  refine ⟨h2, ?_⟩
  rw [← pow_mul, ← pow_succ, show m - 2 + 1 = m - 1 by omega,
    orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) (hm ▸ pow_dvd_pow 2 (Nat.sub_le m 1)), hm,
    Nat.pow_div (Nat.sub_le m 1) two_pos, show m - (m - 1) = 1 by omega, pow_one]

private theorem le_centralizer_of_isElemAbelian {V : Subgroup G} (hV : IsElemAbelian 2 V) :
    V ≤ Subgroup.centralizer (V : Set G) := by
  have := hV.1
  exact Subgroup.le_centralizer V

private theorem eq_one_or_eq_of_mem_zpowers {z x : G} (hz : orderOf z = 2)
    (hx : x ∈ Subgroup.zpowers z) : x = 1 ∨ x = z := by
  classical
  have hfin : IsOfFinOrder z := orderOf_pos_iff.mp (by rw [hz]; norm_num)
  rw [hfin.mem_zpowers_iff_mem_range_orderOf, hz] at hx
  simp only [Finset.mem_image, Finset.mem_range] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  interval_cases a <;> simp

private theorem mul_mem_iff_of_relIndex_eq_two {H K : Subgroup G} (h : H.relIndex K = 2)
    {a b : G} (ha : a ∈ K) (hb : b ∈ K) : a * b ∈ H ↔ (a ∈ H ↔ b ∈ H) :=
  Subgroup.mul_mem_iff_of_index_two (H := H.subgroupOf K) h (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)

private theorem eight_le_of_four_lt_two_pow {k : ℕ} (h : 4 < 2 ^ k) : 8 ≤ 2 ^ k := by
  by_contra hlt
  have hk : k < 3 := by
    by_contra hk
    exact hlt ((Nat.pow_le_pow_right two_pos (not_lt.mp hk)).trans' (by norm_num))
  interval_cases k <;> norm_num at h

variable [Finite G]

private theorem three_le_pRank_of_le {H E : Subgroup G} (hEH : E ≤ H) (hE : IsElemAbelian 2 E)
    (hE8 : 8 ≤ Nat.card E) : 3 ≤ pRank 2 H := by
  obtain ⟨k, hk⟩ := (CFSG.RankThreeCoreUniqueness.Helpers.elementary_isPGroup 2 E hE).exists_card_eq
  have h3 : 3 ≤ k := by
    by_contra hlt
    have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right two_pos (by omega)
    omega
  exact h3.trans (CFSG.SectionRank.le_pRank one_lt_two hEH hE hk)

private theorem exists_elemAbelian_eight {H : Subgroup G} (h : 3 ≤ pRank 2 H) :
    ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian 2 E ∧ Nat.card E = 8 := by
  obtain ⟨E, hEH, hE, hcard⟩ := CFSG.SectionRank.exists_pRank one_lt_two H
  have hdiv : 2 ^ 3 ∣ Nat.card E := by
    rw [hcard]
    exact Nat.pow_dvd_pow 2 h
  obtain ⟨F, hFcard, -, hFE⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two
    (H := (⊥ : Subgroup G)) (L := E) (by simp) hdiv bot_le
  exact ⟨F, hFE.trans hEH,
    CFSG.LargeEvenClassification.Helpers.elementary_subgroup_of_le E F hE hFE,
    by simpa using hFcard⟩

private theorem exists_elemAbelian_adjoin {V : Subgroup G} {t : G} {r : ℕ}
    (hV : IsElemAbelian 2 V) (hVc : Nat.card V = 2 ^ r) (ht : orderOf t = 2) (htV : t ∉ V)
    (htC : t ∈ Subgroup.centralizer (V : Set G)) :
    ∃ E : Subgroup G, V ≤ E ∧ t ∈ E ∧ E ≤ V ⊔ Subgroup.zpowers t ∧ IsElemAbelian 2 E ∧
      Nat.card E = 2 ^ (r + 1) := by
  obtain ⟨E, hVE, hTE, hE, hEc, hEle⟩ :=
    CFSG.LargeEvenClassification.Helpers.commuting_disjoint_elementary_product (secondRank := 1)
      V (Subgroup.zpowers t) hV (CFSG.ProperTwoGeneratedCore.involution_zpowers_elementary t ht)
      hVc (by rw [Nat.card_zpowers, ht, pow_one])
      (Subgroup.le_centralizer_iff.mpr (Subgroup.zpowers_le.mpr htC))
      (CFSG.ProperTwoGeneratedCore.involution_zpowers_disjoint V t ht htV)
  exact ⟨E, hVE, hTE (Subgroup.mem_zpowers t), hEle, hE, hEc⟩

theorem centralizer_unique_involution {R : Subgroup G} (hR : IsPGroup 2 R) {z : G}
    (hzR : z ∈ R) (hz : orderOf z = 2)
    (huniq : ∀ x ∈ R ⊓ Subgroup.centralizer ({z} : Set G), orderOf x = 2 → x = z) :
    R ≤ Subgroup.centralizer ({z} : Set G) ∧ ∀ x ∈ R, orderOf x = 2 → x = z := by
  have hz1 : (⟨z, hzR⟩ : R) ≠ 1 := by
    intro h
    have h' : z = 1 := congrArg Subtype.val h
    rw [h', orderOf_one] at hz
    norm_num at hz
  have : Nontrivial R := ⟨⟨_, _, hz1⟩⟩
  have hZ : Nontrivial (Subgroup.center R) := hR.center_nontrivial
  obtain ⟨w, hw⟩ : ∃ w : Subgroup.center R, orderOf w = 2 := by
    obtain ⟨n, hn, hcard⟩ := ((hR.to_subgroup _).nontrivial_iff_card).mp hZ
    exact exists_prime_orderOf_dvd_card' 2 (by rw [hcard]; exact dvd_pow_self 2 hn.ne')
  have hcomm : ∀ x ∈ R, x * ((w : R) : G) = ((w : R) : G) * x := fun x hx =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp w.2 ⟨x, hx⟩)
  have hwz : ((w : R) : G) = z := by
    refine huniq _ ⟨(w : R).2, Subgroup.mem_centralizer_singleton_iff.mpr (hcomm z hzR).symm⟩ ?_
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hw]
  have hRz : R ≤ Subgroup.centralizer ({z} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hwz ▸ hcomm x hx)
  exact ⟨hRz, fun x hx hx2 => huniq x ⟨hx, hRz hx⟩ hx2⟩

theorem four_involution_centralizer_rank_bound {S : Subgroup G} (hS : IsPGroup 2 S) {t : G}
    (htS : t ∈ S) (hC : IsElemAbelian 2 (S ⊓ Subgroup.centralizer ({t} : Set G)))
    (hC4 : Nat.card (S ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) = 4) :
    pRank 2 S ≤ 2 := by
  classical
  set C := S ⊓ Subgroup.centralizer ({t} : Set G) with hCdef
  let V : Subgroup S := C.subgroupOf S
  let e : V ≃* C := Subgroup.subgroupOfEquivOfLe inf_le_left
  have hV : CFSG.Open.IsElemAbelian 2 V :=
    CFSG.RankThreeCoreUniqueness.Helpers.elementary_transport 2 C V e.symm hC
  have hV4 : Nat.card V = 4 := (Nat.card_congr e.toEquiv).trans hC4
  have hVt : Subgroup.centralizer ({(⟨t, htS⟩ : S)} : Set S) = V := by
    ext x
    simp only [V, hCdef, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff, x.2, true_and]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have htV : (⟨t, htS⟩ : S) ∈ V := hVt ▸ Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hcent : Subgroup.centralizer (V : Set S) = V := by
    refine le_antisymm ((Subgroup.centralizer_le (Set.singleton_subset_iff.mpr htV)).trans
      hVt.le) ?_
    have := hV.1
    exact Subgroup.le_centralizer V
  obtain ⟨H, hHcyc, hHind⟩ : ∃ H : Subgroup S, IsCyclic H ∧ H.index ≤ 2 := by
    rcases CFSG.RankTwoShapes.selfCentralizing_four_shapes hS V hV.1 hV.2 hV4 hcent
      with ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
    · refine CFSG.LocalAnalysis.ComponentInitial.exists_cyclic_index_le_two_of_mulEquiv e
        (H₀ := Subgroup.zpowers (DihedralGroup.r 1)) inferInstance (le_of_eq ?_)
      have hm : 2 ^ (n - 1) ≠ 0 := pow_ne_zero _ two_ne_zero
      have h1 := Subgroup.card_mul_index
        (Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup (2 ^ (n - 1))))
      rw [Nat.card_zpowers, DihedralGroup.orderOf_r_one, DihedralGroup.nat_card] at h1
      have hpos : 0 < 2 ^ (n - 1) := Nat.pos_of_ne_zero hm
      nlinarith
    · obtain ⟨-, -, -, -, hcyc, -, hidx⟩ := CFSG.Semidihedral.normal_form n hn
      exact CFSG.LocalAnalysis.ComponentInitial.exists_cyclic_index_le_two_of_mulEquiv e hcyc
        hidx.le
  have h := CFSG.LocalAnalysis.ComponentInitial.cyclic_index_two_rank_bound hHcyc hHind
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h
  rw [assembly_pRank_eq_open,
    CFSG.RankThreeCoreUniqueness.Helpers.pRank_subgroup_eq_internal_top 2 (by decide) S]
  exact h

private theorem relIndex_centralizer_le_two {S A : Subgroup G} (hS : IsPGroup 2 S)
    (hAS : A ≤ S) (hSA : S ≤ Subgroup.normalizer (A : Set G)) (hA : IsElemAbelian 2 A)
    (hA4 : Nat.card A = 4) : (S ⊓ Subgroup.centralizer (A : Set G)).relIndex S ≤ 2 := by
  let A' := A.subgroupOf S
  have : A'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hAS).mpr hSA
  have hA' : CFSG.Open.IsElemAbelian 2 A' :=
    CFSG.RankThreeCoreUniqueness.Helpers.elementary_transport 2 A A'
      (Subgroup.subgroupOfEquivOfLe hAS).symm hA
  have hA'4 : Nat.card A' = 4 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAS).toEquiv).trans hA4
  obtain ⟨-, -, hind⟩ := CFSG.ProperTwoGeneratedCore.normal_four_centralizer_index hS A' hA' hA'4
  have heq : Subgroup.centralizer (A' : Set S) =
      (S ⊓ Subgroup.centralizer (A : Set G)).subgroupOf S := by
    ext x
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_iff]
    constructor
    · intro h
      exact ⟨x.2, fun a ha => congrArg Subtype.val (h ⟨a, hAS ha⟩ ha)⟩
    · rintro ⟨-, h⟩ y hy
      exact Subtype.ext (h y hy)
  rw [Subgroup.relIndex, ← heq]
  exact hind

theorem isolated_four_centralizer_structure {S A V : Subgroup G} (hS : IsPGroup 2 S)
    (hrank : 3 ≤ pRank 2 S) (hAS : A ≤ S) (hSA : S ≤ Subgroup.normalizer (A : Set G))
    (hA : IsElemAbelian 2 A) (hA4 : Nat.card A = 4) (hVS : V ≤ S) (hV : IsElemAbelian 2 V)
    (hV4 : Nat.card V = 4) (hVrank : pRank 2 (S ⊓ Subgroup.centralizer (V : Set G)) = 2) :
    (S ⊓ Subgroup.centralizer (A : Set G)).relIndex S = 2 ∧
    ¬ V ≤ S ⊓ Subgroup.centralizer (A : Set G) ∧
    ∃ z : G, orderOf z = 2 ∧ V ⊓ (S ⊓ Subgroup.centralizer (A : Set G)) = Subgroup.zpowers z ∧
      (∀ x ∈ V ⊓ (S ⊓ Subgroup.centralizer (A : Set G)), x = 1 ∨ x = z) ∧
      ∀ v ∈ V, v ∉ S ⊓ Subgroup.centralizer (A : Set G) →
      ∀ R : Subgroup G,
        R = S ⊓ Subgroup.centralizer (A : Set G) ⊓ Subgroup.centralizer ({v} : Set G) →
        V = Subgroup.closure ({z, v} : Set G) ∧
        S ⊓ Subgroup.centralizer (V : Set G) = S ⊓ Subgroup.centralizer ({v} : Set G) ∧
        S ⊓ Subgroup.centralizer ({v} : Set G) = Subgroup.zpowers v ⊔ R ∧
        Disjoint (Subgroup.zpowers v) R ∧
        (∀ x ∈ S ⊓ Subgroup.centralizer ({v} : Set G), x ∈ R ∨ v * x ∈ R) ∧
        4 ≤ Nat.card R ∧ (∀ x ∈ R, orderOf x = 2 → x = z) ∧ ∃ r ∈ R, r ^ 2 = z := by
  classical
  set S₀ := S ⊓ Subgroup.centralizer (A : Set G) with hS₀
  have hVab : V ≤ Subgroup.centralizer (V : Set G) := le_centralizer_of_isElemAbelian hV
  have hVC : V ≤ S ⊓ Subgroup.centralizer (V : Set G) := le_inf hVS hVab
  have hno8 : ∀ E : Subgroup G, E ≤ S ⊓ Subgroup.centralizer (V : Set G) →
      IsElemAbelian 2 E → 8 ≤ Nat.card E → False := fun E hE hEe hE8 => by
    have := three_le_pRank_of_le hE hEe hE8
    omega
  have hVS₀ : ¬ V ≤ S₀ := by
    intro hle
    have hVA : V ≤ Subgroup.centralizer (A : Set G) := hle.trans inf_le_right
    by_cases hVeqA : V = A
    · subst hVeqA
      obtain ⟨E, hES, hE, hE8⟩ := exists_elemAbelian_eight hrank
      have := three_le_pRank_inf_centralizer hS hAS hSA hA hA4 hES hE hE8
      omega
    · have hAV : A ≤ Subgroup.centralizer (V : Set G) := Subgroup.le_centralizer_iff.mp hVA
      have hE : IsElemAbelian 2 (V ⊔ A) :=
        CFSG.ProperTwoGeneratedCore.commuting_elementary_sup V A hV hA hVA
      refine hno8 (V ⊔ A) (le_inf (sup_le hVS hAS) (sup_le hVab hAV)) hE ?_
      obtain ⟨k, hk⟩ :=
        (CFSG.RankThreeCoreUniqueness.Helpers.elementary_isPGroup 2 _ hE).exists_card_eq
      have h4 : 4 ≤ Nat.card (V ⊔ A : Subgroup G) := hV4 ▸ Subgroup.card_le_of_le le_sup_left
      have hne : Nat.card (V ⊔ A : Subgroup G) ≠ 4 := by
        intro h
        have h1 : V = V ⊔ A := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h, hV4])
        have h2 : A ≤ V := h1 ▸ le_sup_right
        exact hVeqA (Subgroup.eq_of_le_of_card_ge h2 (by rw [hV4, hA4])).symm
      rw [hk] at h4 hne ⊢
      exact eight_le_of_four_lt_two_pow (lt_of_le_of_ne h4 (Ne.symm hne))
  obtain ⟨v₀, hv₀V, hv₀S₀⟩ := IsConcreteLE.not_le_iff_exists.mp hVS₀
  have hind2 : S₀.relIndex S = 2 := by
    have hle : S₀.relIndex S ≤ 2 := relIndex_centralizer_le_two hS hAS hSA hA hA4
    have hne1 : S₀.relIndex S ≠ 1 := fun h1 =>
      hv₀S₀ (Subgroup.relIndex_eq_one.mp h1 (hVS hv₀V))
    have hne0 : S₀.relIndex S ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  have hpar : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S₀ ↔ (a ∈ S₀ ↔ b ∈ S₀) := fun a ha b hb =>
    mul_mem_iff_of_relIndex_eq_two hind2 ha hb
  have hVS₀2 : S₀.relIndex V = 2 := by
    rw [Subgroup.relIndex_eq_two_iff_exists_notMem_and]
    refine ⟨v₀, hv₀V, hv₀S₀, fun b hb => ?_⟩
    by_cases hbS₀ : b ∈ S₀
    · exact Or.inr hbS₀
    · exact Or.inl ((hpar b (hVS hb) v₀ (hVS hv₀V)).mpr (iff_of_false hbS₀ hv₀S₀))
  have hcard2 : Nat.card (V ⊓ S₀ : Subgroup G) = 2 := by
    have h := Subgroup.relIndex_mul_card (H := S₀) (K := V)
    rw [hVS₀2, hV4, inf_comm] at h
    omega
  obtain ⟨z, hzVS₀, hz1⟩ : ∃ z ∈ V ⊓ S₀, z ≠ 1 := by
    by_contra hcon
    push Not at hcon
    rw [(Subgroup.eq_bot_iff_forall _).mpr hcon, Subgroup.card_bot] at hcard2
    norm_num at hcard2
  have hz2 : orderOf z = 2 := orderOf_eq_prime (hV.2 z hzVS₀.1) hz1
  have hzpow : V ⊓ S₀ = Subgroup.zpowers z := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzVS₀) ?_).symm
    rw [hcard2, Nat.card_zpowers, hz2]
  have hzuniq : ∀ x ∈ V ⊓ S₀, x = 1 ∨ x = z := fun x hx =>
    eq_one_or_eq_of_mem_zpowers hz2 (hzpow ▸ hx)
  refine ⟨hind2, hVS₀, z, hz2, hzpow, hzuniq, ?_⟩
  intro v hvV hvS₀ R hR
  have hvS : v ∈ S := hVS hvV
  have hv1 : v ≠ 1 := fun h => hvS₀ (h ▸ S₀.one_mem)
  have hv2 : orderOf v = 2 := orderOf_eq_prime (hV.2 v hvV) hv1
  have hvv : v * v = 1 := by rw [← sq]; exact hV.2 v hvV
  have hzV : z ∈ V := hzVS₀.1
  have hzS₀ : z ∈ S₀ := hzVS₀.2
  have hzv : z * v = v * z := Subgroup.mem_centralizer_iff.mp (hVab hvV) z hzV
  have hVcl : V = Subgroup.closure ({z, v} : Set G) := by
    set H := Subgroup.closure ({z, v} : Set G)
    have hle : H ≤ V := (Subgroup.closure_le V).mpr (by
      intro x hx
      rcases hx with rfl | rfl
      · exact hzV
      · exact hvV)
    have hzH : Subgroup.zpowers z ≤ H :=
      Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert z _))
    have hvH : v ∈ H := Subgroup.subset_closure (Set.mem_insert_of_mem z rfl)
    have hdvd4 : Nat.card H ∣ 4 := hV4 ▸ Subgroup.card_dvd_of_le hle
    have hdvd2 : 2 ∣ Nat.card H := by
      have := Subgroup.card_dvd_of_le hzH
      rwa [Nat.card_zpowers, hz2] at this
    have hne2 : Nat.card H ≠ 2 := by
      intro h2
      have hHz : Subgroup.zpowers z = H :=
        Subgroup.eq_of_le_of_card_ge hzH (by rw [h2, Nat.card_zpowers, hz2])
      have hvz : v ∈ V ⊓ S₀ := hzpow ▸ hHz ▸ hvH
      exact hvS₀ hvz.2
    have hH4 : Nat.card H = 4 := by
      have hle4 := Nat.le_of_dvd (by norm_num) hdvd4
      interval_cases h : Nat.card H <;> simp_all
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hV4, hH4])).symm
  have hCV : ∀ x, x ∈ Subgroup.centralizer (V : Set G) ↔ x * z = z * x ∧ x * v = v * x := by
    intro x
    rw [hVcl, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
    exact ⟨fun h => ⟨h.1.symm, h.2.symm⟩, fun h => ⟨h.1.symm, h.2.symm⟩⟩
  have hRS₀ : R ≤ S₀ := hR ▸ inf_le_left
  have hRv : R ≤ Subgroup.centralizer ({v} : Set G) := hR ▸ inf_le_right
  have hRS : R ≤ S := hRS₀.trans inf_le_left
  have hzR : z ∈ R := by
    rw [hR]
    exact Subgroup.mem_inf.mpr ⟨hzS₀, Subgroup.mem_centralizer_singleton_iff.mpr hzv⟩
  have hvR : v ∉ R := fun h => hvS₀ (hRS₀ h)
  have hdec : ∀ x ∈ S ⊓ Subgroup.centralizer ({v} : Set G), x ∈ R ∨ v * x ∈ R := by
    intro x hx
    have hxv : x * v = v * x := Subgroup.mem_centralizer_singleton_iff.mp hx.2
    rw [hR]
    by_cases hxS₀ : x ∈ S₀
    · exact Or.inl (Subgroup.mem_inf.mpr ⟨hxS₀, hx.2⟩)
    · refine Or.inr (Subgroup.mem_inf.mpr ⟨(hpar v hvS x hx.1).mpr (iff_of_false hvS₀ hxS₀), ?_⟩)
      rw [Subgroup.mem_centralizer_singleton_iff, mul_assoc, hxv]
  have hRuniq : ∀ u ∈ R ⊓ Subgroup.centralizer ({z} : Set G), orderOf u = 2 → u = z := by
    intro u hu hu2
    by_contra huz
    have huS₀ : u ∈ S₀ := hRS₀ hu.1
    have huV : u ∉ V := by
      intro huV
      rcases hzuniq u ⟨huV, huS₀⟩ with h | h
      · rw [h, orderOf_one] at hu2
        norm_num at hu2
      · exact huz h
    have huC : u ∈ Subgroup.centralizer (V : Set G) :=
      (hCV u).mpr ⟨Subgroup.mem_centralizer_singleton_iff.mp hu.2,
        Subgroup.mem_centralizer_singleton_iff.mp (hRv hu.1)⟩
    obtain ⟨E, -, -, hEle, hE, hEc⟩ :=
      exists_elemAbelian_adjoin (r := 2) hV (by rw [hV4]; norm_num) hu2 huV huC
    exact hno8 E (hEle.trans (sup_le hVC (Subgroup.zpowers_le.mpr ⟨hRS hu.1, huC⟩))) hE
      (by rw [hEc]; norm_num)
  obtain ⟨hRz, hRinv⟩ := centralizer_unique_involution (hS.to_le hRS) hzR hz2 hRuniq
  have hCSV : S ⊓ Subgroup.centralizer (V : Set G) = S ⊓ Subgroup.centralizer ({v} : Set G) := by
    refine le_antisymm (inf_le_inf_left _
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hvV))) fun x hx => ?_
    refine ⟨hx.1, (hCV x).mpr ⟨?_, Subgroup.mem_centralizer_singleton_iff.mp hx.2⟩⟩
    rcases hdec x hx with hxR | hvxR
    · exact Subgroup.mem_centralizer_singleton_iff.mp (hRz hxR)
    · have h1 : v * x * z = z * (v * x) := Subgroup.mem_centralizer_singleton_iff.mp (hRz hvxR)
      calc x * z = (v * v) * x * z := by rw [hvv, one_mul]
        _ = v * (v * x * z) := by simp only [mul_assoc]
        _ = v * (z * (v * x)) := by rw [h1]
        _ = (v * z) * v * x := by simp only [mul_assoc]
        _ = (z * v) * v * x := by rw [hzv]
        _ = z * (v * v) * x := by simp only [mul_assoc]
        _ = z * x := by rw [hvv, mul_one]
  have hsup : S ⊓ Subgroup.centralizer ({v} : Set G) = Subgroup.zpowers v ⊔ R := by
    refine le_antisymm (fun x hx => ?_) (sup_le (Subgroup.zpowers_le.mpr
      ⟨hvS, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩) (le_inf hRS hRv))
    rcases hdec x hx with hxR | hvxR
    · exact Subgroup.mem_sup_right hxR
    · have hx' : x = v * (v * x) := by rw [← mul_assoc, hvv, one_mul]
      rw [hx']
      exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers v) hvxR
  have hdisj : Disjoint (Subgroup.zpowers v) R :=
    (CFSG.ProperTwoGeneratedCore.involution_zpowers_disjoint R v hv2 hvR).symm
  obtain ⟨r, hrR, hr⟩ : ∃ r ∈ R, r ^ 2 ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hR1z : ∀ x ∈ R, x = 1 ∨ x = z := by
      intro x hx
      by_cases hx1 : x = 1
      · exact Or.inl hx1
      · exact Or.inr (hRinv x hx (orderOf_eq_prime (hcon x hx) hx1))
    have hCv : S ⊓ Subgroup.centralizer ({v} : Set G) = V := by
      refine le_antisymm (fun x hx => ?_) (hCSV ▸ hVC)
      rcases hdec x hx with hxR | hvxR
      · rcases hR1z x hxR with rfl | rfl
        · exact V.one_mem
        · exact hzV
      · have hx' : x = v * (v * x) := by rw [← mul_assoc, hvv, one_mul]
        rw [hx']
        rcases hR1z _ hvxR with h | h <;> rw [h]
        · rw [mul_one]
          exact hvV
        · exact V.mul_mem hvV hzV
    have := four_involution_centralizer_rank_bound hS hvS (by rw [hCv]; exact hV)
      (by rw [hCv]; exact hV4)
    omega
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp (hS.to_le hRS)) ⟨r, hrR⟩
  have hm' : orderOf r = 2 ^ m := (Subgroup.orderOf_coe (⟨r, hrR⟩ : R)).trans hm
  obtain ⟨hm2, hsq⟩ := two_le_and_orderOf_sq_pow_eq_two hm' hr
  have hcardR : 4 ≤ Nat.card R := by
    have hdvd := Subgroup.orderOf_dvd_natCard R hrR
    rw [hm'] at hdvd
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right two_pos hm2
      _ ≤ Nat.card R := Nat.le_of_dvd Nat.card_pos hdvd
  exact ⟨hVcl, hCSV, hsup, hdisj, hdec, hcardR, hRinv, r ^ 2 ^ (m - 2), R.pow_mem hrR _,
    hRinv _ (R.pow_mem (R.pow_mem hrR _) 2) hsq⟩

end CFSG.Assembly.Dichotomy
