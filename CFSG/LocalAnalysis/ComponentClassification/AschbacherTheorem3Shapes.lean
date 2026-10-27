module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Statement
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitTwoGroupShapes
public import CFSG.StronglyEmbedded.TheoremSE.BenderLowRank
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3

open CFSG.ComponentClassification.AschbacherToolkit

variable {X : Type} [Group X] [Finite X]

theorem isCyclic_or_isQuaternion_of_atMostOneInvolution {R : Subgroup X} (hR : IsPGroup 2 R)
    (h : AtMostOneInvolution R) : IsCyclic R ∨ IsQuaternionTwoGroup R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrank : ¬ BenderSuzuki.PFchapter1section1.TwoRankAtLeastTwo R := by
    rintro ⟨E, hcard, hsq⟩
    obtain ⟨u, hu, v, hv, hu1, hv1, hvu⟩ := exists_two_ne_one (X := R) (E := E) hcard.ge
    have hu2 : orderOf u = 2 :=
      orderOf_eq_prime (by simpa using congrArg Subtype.val (hsq ⟨u, hu⟩)) hu1
    have hv2 : orderOf v = 2 :=
      orderOf_eq_prime (by simpa using congrArg Subtype.val (hsq ⟨v, hv⟩)) hv1
    exact hvu (h v u hv2 hu2)
  have hS : IsPGroup 2 (⊤ : Subgroup R) := hR.to_subgroup ⊤
  have hidx : ¬ 2 ∣ (⊤ : Subgroup R).index := by
    rw [Subgroup.index_top]
    norm_num
  let φ : R ≃* ((hS.toSylow hidx : Sylow 2 R) : Subgroup R) :=
    Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr (IsPGroup.toSylow_coe hS hidx).symm)
  rcases BenderSuzuki.sylowTwo_cyclic_or_quaternion_of_not_twoRank hrank (hS.toSylow hidx) with
    hc | ⟨r, hr3, ⟨e⟩⟩
  · exact Or.inl (isCyclic_of_injective φ.toMonoidHom φ.injective)
  · exact Or.inr ⟨r, hr3, ⟨φ.trans e⟩⟩

theorem isCyclic_or_isDihedral_of_hasDihedralGenerators {R : Subgroup X} (hR : IsPGroup 2 R)
    (h : HasDihedralGenerators R) : IsCyclic R ∨ IsDihedralTwoGroup R := by
  obtain ⟨x, y, hgen, hy2, hyx, -⟩ := h
  rcases GorensteinWalter.isCyclic_or_dihedral_of_generators x y hgen.symm hy2 hyx with
    hc | he
  · exact Or.inl hc
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hR) x
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  ·
    left
    rw [pow_zero, orderOf_eq_one_iff] at hk
    rw [hk, Subgroup.zpowers_one_eq_bot, bot_sup_eq] at hgen
    exact isCyclic_iff_exists_zpowers_eq_top.mpr ⟨y, hgen⟩
  · right
    rw [hk, show k = k + 1 - 1 by omega] at he
    exact ⟨k + 1, by omega, he⟩

theorem shape_of_index_two {S R : Subgroup X} (hS : IsPGroup 2 S) (hRS : R ≤ S)
    (hidx : R.relIndex S = 2) {b : X} (hbS : b ∈ S) (hbR : b ∉ R) (hb : orderOf b = 2)
    (hC : Nat.card (R ⊓ Subgroup.centralizer {b} : Subgroup X) ≤ 2) :
    IsCyclic R ∨ IsQuaternionTwoGroup R ∨ IsDihedralTwoGroup R := by
  set P : Subgroup S := R.subgroupOf S
  have hb' : orderOf (⟨b, hbS⟩ : S) = 2 := by rw [Subgroup.orderOf_mk]; exact hb
  have hbP : (⟨b, hbS⟩ : S) ∉ P := by
    rw [Subgroup.mem_subgroupOf]
    exact hbR
  have hC' : Nat.card (P ⊓ Subgroup.centralizer ({⟨b, hbS⟩} : Set S) : Subgroup S) ≤ 2 := by
    refine le_trans ?_ hC
    rw [← Subgroup.card_map_of_injective S.subtype_injective]
    apply Subgroup.card_le_of_le
    rintro _ ⟨x, hx, rfl⟩
    have hxP : x ∈ P := hx.1
    have hxC : x * ⟨b, hbS⟩ = ⟨b, hbS⟩ * x := Subgroup.mem_centralizer_singleton_iff.mp hx.2
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp hxP,
      Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hxC)⟩
  let e : P ≃* R := Subgroup.subgroupOfEquivOfLe hRS
  have hR2 : IsPGroup 2 R := hS.to_le hRS
  rcases index_two_small_centralizer_shape hS P hidx hb' hbP hC' with h1 | h1
  · rcases isCyclic_or_isQuaternion_of_atMostOneInvolution hR2 (h1.of_mulEquiv e) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases isCyclic_or_isDihedral_of_hasDihedralGenerators hR2 (h1.of_mulEquiv e) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

omit [Finite X] in
theorem conj_eq_inv_of_mem_zpowers {c u d : X} (hinv : u * c * u⁻¹ = c⁻¹)
    (hd : d ∈ Subgroup.zpowers c) : u * d * u⁻¹ = d⁻¹ := by
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
  have h := congrArg (· ^ j) hinv
  rw [conj_zpow, inv_zpow'] at h
  rw [h, zpow_neg]

theorem shape_of_inverting {R : Subgroup X} (hR : IsPGroup 2 R) {c u : X} (hcR : c ∈ R)
    (hidx : (Subgroup.zpowers c).relIndex R = 2) (huR : u ∈ R)
    (huc : u ∉ Subgroup.zpowers c) (hinv : u * c * u⁻¹ = c⁻¹) :
    IsCyclic R ∨ IsQuaternionTwoGroup R ∨ IsDihedralTwoGroup R := by
  set C := Subgroup.zpowers c with hCdef
  set C' : Subgroup R := C.subgroupOf R with hC'def
  have hC'idx : C'.index = 2 := hidx
  set u' : R := ⟨u, huR⟩ with hu'def
  have hu'C : u' ∉ C' := by
    rw [Subgroup.mem_subgroupOf]
    exact huc
  have hdecomp : ∀ r : R, r ∉ C' → ((r : X) * u⁻¹) ∈ C := by
    intro r hr
    have hmem : r * u'⁻¹ ∈ C' := by
      rw [Subgroup.mul_mem_iff_of_index_two hC'idx]
      exact iff_of_false hr (fun h => hu'C (by simpa using C'.inv_mem h))
    exact Subgroup.mem_subgroupOf.mp hmem
  have hu2C : u ^ 2 ∈ C := by
    have h := hdecomp u' hu'C
    rw [show (u' : X) * u⁻¹ = 1 by simp [hu'def]] at h
    have hu2 : u' * u' ∈ C' := by
      rw [Subgroup.mul_mem_iff_of_index_two hC'idx]
    rw [pow_two]
    exact Subgroup.mem_subgroupOf.mp hu2
  by_cases hu2 : u ^ 2 = 1
  ·
    set x : R := ⟨c, hcR⟩
    have hgen : Subgroup.zpowers x ⊔ Subgroup.zpowers u' = ⊤ := by
      set K := Subgroup.zpowers x ⊔ Subgroup.zpowers u'
      have hCK : C' ≤ K := by
        intro r hr
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hr)
        have hr' : r = x ^ j := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hj.symm)
        rw [hr']
        exact Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers x j)
      have hmul := Subgroup.relIndex_mul_index hCK
      rw [hC'idx] at hmul
      have hKidx : K.index = 1 := by
        have hdvd : K.index ∣ 2 := ⟨_, by rw [mul_comm]; exact hmul.symm⟩
        rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
        · exact h1
        · exfalso
          rw [h2] at hmul
          have hrel : C'.relIndex K = 1 := by omega
          rw [Subgroup.relIndex_eq_one] at hrel
          exact hu'C (hrel (Subgroup.mem_sup_right (Subgroup.mem_zpowers u')))
      exact Subgroup.index_eq_one.mp hKidx
    have hdih : HasDihedralGenerators R := by
      refine ⟨x, u', hgen, Subtype.ext (by simpa using hu2), Subtype.ext (by simpa using hinv),
        fun hmem => hu'C ?_⟩
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
      rw [Subgroup.mem_subgroupOf, ← hj, Subgroup.coe_zpow]
      exact Subgroup.zpow_mem_zpowers c j
    rcases isCyclic_or_isDihedral_of_hasDihedralGenerators hR hdih with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  ·
    have hinvC : ∀ s : R, orderOf s = 2 → (s : X) ∈ C := by
      intro s hs
      by_contra hsC
      have hd := hdecomp s (fun h => hsC (Subgroup.mem_subgroupOf.mp h))
      set d := (s : X) * u⁻¹
      have hsd : (s : X) = d * u := by simp [d]
      have hsq : (s : X) ^ 2 = u ^ 2 := by
        have hdu := conj_eq_inv_of_mem_zpowers hinv hd
        calc (s : X) ^ 2 = (d * u) * (d * u) := by rw [pow_two, hsd]
          _ = d * (u * d * u⁻¹) * (u * u) := by group
          _ = u ^ 2 := by rw [hdu, pow_two]; group
      have hs2 : (s : X) ^ 2 = 1 := by
        rw [← Subgroup.coe_pow, ← hs, pow_orderOf_eq_one, Subgroup.coe_one]
      exact hu2 (hsq ▸ hs2)
    have hcyc : AtMostOneInvolution C := atMostOneInvolution_of_isCyclic
    have hone : AtMostOneInvolution R := by
      intro s t hs ht
      have hsC := hinvC s hs
      have htC := hinvC t ht
      have h := hcyc ⟨s, hsC⟩ ⟨t, htC⟩ (by rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hs])
        (by rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, ht])
      exact Subtype.ext (congrArg (fun w : C => (w : X)) h)
    rcases isCyclic_or_isQuaternion_of_atMostOneInvolution hR hone with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

end CFSG.ComponentClassification.AschbacherTheorem3
