module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestDefs
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabThCensus
public import CFSG.Sporadic.Th.Max3.Maximal

public section

namespace CFSG.KC.ThThreeCov

open CFSG CFSG.StandardType CFSG.StandardType.SporadicShape CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Max3 CFSG.HardMathSupport.Dickson.I271

theorem inv_conj_mem {G : Type*} [Group G] {p : ℕ} (P : Sylow p G) (k : G) {x : G}
    (hx : x ∈ ((k • P : Sylow p G) : Subgroup G)) : k⁻¹ * x * k ∈ (P : Subgroup G) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
  simpa [MulAut.smul_def, MulAut.conj_inv_apply] using hx

theorem mem_conjPre {G : Type*} [Group G] (Y : Subgroup G) (k g : G) :
    g ∈ Y.comap (MulAut.conj k⁻¹).toMonoidHom ↔ k⁻¹ * g * k ∈ Y := by
  simp [Subgroup.mem_comap, MulAut.conj_apply]

theorem controlsAt_of_isConj {K : Type} [Group K] {x y : K} {Y : Subgroup K}
    (hY : SporKRestControlsAt x Y) (hxy : IsConj x y) (hyY : y ∈ Y) :
    SporKRestControlsAt y Y := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hxy
  have hcY : c⁻¹ ∈ Y := hY c⁻¹ (by rw [inv_inv, hc]; exact hyY)
  intro g hg
  have h2 : c⁻¹ * g ∈ Y := hY _ (by
    have : (c⁻¹ * g)⁻¹ * x * (c⁻¹ * g) = g⁻¹ * (c * x * c⁻¹) * g := by group
    rw [this, hc]
    exact hg)
  simpa using Y.mul_mem (Y.inv_mem hcY) h2

theorem generating_of_coatom {K : Type} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    {M S : Subgroup K} (hM : IsCoatom M) (hMS : ∀ P : Sylow p K, ¬ (P : Subgroup K) ≤ M)
    (hS : IsPGroup p S) {r : K} {Z : Set K}
    (hZ : ∀ z ∈ Z, ∃ t ∈ S, IsConj r t ∧ z * t = t * z) (hMZ : M ≤ Subgroup.closure Z)
    {c : K} (hc : IsConj r c) : SporKRestGenerating p c := by
  rintro Y ⟨Q, hQY⟩ hctl
  obtain ⟨Q', hSQ'⟩ := hS.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K Q Q'
  have hQ' : ∀ u ∈ (Q' : Subgroup K), k⁻¹ * u * k ∈ Y := by
    intro u hu
    rw [← hk] at hu
    exact hQY (inv_conj_mem Q k hu)
  have hZY : ∀ z ∈ Z, k⁻¹ * z * k ∈ Y := by
    intro z hz
    obtain ⟨t, htS, hrt, hzt⟩ := hZ z hz
    have htY : k⁻¹ * t * k ∈ Y := hQ' t (hSQ' htS)
    have hct : IsConj c (k⁻¹ * t * k) :=
      hc.symm.trans (hrt.trans (isConj_iff.2 ⟨k⁻¹, by group⟩))
    refine controlsAt_of_isConj hctl hct htY _ ?_
    have hzt' : z⁻¹ * t * z = t := by
      rw [mul_assoc, ← hzt, ← mul_assoc, inv_mul_cancel, one_mul]
    have e : (k⁻¹ * z * k)⁻¹ * (k⁻¹ * t * k) * (k⁻¹ * z * k) = k⁻¹ * t * k := by
      calc (k⁻¹ * z * k)⁻¹ * (k⁻¹ * t * k) * (k⁻¹ * z * k) = k⁻¹ * (z⁻¹ * t * z) * k := by group
        _ = k⁻¹ * t * k := by rw [hzt']
    rw [e]
    exact htY
  have hMY₁ : M ≤ Y.comap (MulAut.conj k⁻¹).toMonoidHom := by
    refine hMZ.trans ?_
    rw [Subgroup.closure_le]
    intro z hz
    exact (mem_conjPre Y k z).2 (hZY z hz)
  have hY₁ : Y.comap (MulAut.conj k⁻¹).toMonoidHom = ⊤ := by
    rcases hMY₁.eq_or_lt with h | h
    · exact absurd (fun u hu => h ▸ (mem_conjPre Y k u).2 (hQ' u hu)) (hMS Q')
    · exact hM.2 _ h
  rw [eq_top_iff]
  intro h _
  have h1 : k * h * k⁻¹ ∈ Y.comap (MulAut.conj k⁻¹).toMonoidHom := by
    rw [hY₁]
    exact Subgroup.mem_top _
  simpa [mul_assoc] using (mem_conjPre Y k _).1 h1

theorem closure_le_of_right_closed {G : Type*} [Group G] [Finite G] (gens : Set G)
    (s : Set G) (h1 : (1 : G) ∈ s) (hs : ∀ x ∈ s, ∀ g ∈ gens, x * g ∈ s) :
    (Subgroup.closure gens : Set G) ⊆ s := by
  intro x hx
  have hx' : x ∈ Submonoid.closure gens := by
    rw [← Subgroup.closure_toSubmonoid_of_finite]
    exact hx
  exact Submonoid.closure_induction_right (motive := fun x _ => x ∈ s) h1
    (fun x _ y hy ih => hs x ih y hy) hx'


structure TabFacts (T G : ℕ → J) : Prop where
  t0 : T 0 = 1
  step : ∀ j, 0 < j → j < 81 → ∃ p < j, ∃ i < 2, T j = T p * G i
  clos : ∀ j < 81, ∀ i < 2, ∃ l < 81, T j * G i = T l
  inj : ∀ j < 81, ∀ l < 81, T j = T l → j = l

@[expose] def ClassGen (T : ℕ → J) (r : J) : Prop :=
  ∃ Z : Set J, (∀ z ∈ Z, ∃ j < 81, IsConj r (T j) ∧ z * T j = T j * z) ∧
    x ∈ Subgroup.closure Z ∧ y ∈ Subgroup.closure Z

theorem exists_S [Finite J] {T G : ℕ → J} (hT : TabFacts T G) :
    ∃ S : Subgroup J, IsPGroup 3 S ∧ ∀ j < 81, T j ∈ S := by
  set S : Subgroup J := Subgroup.closure (G '' Set.Iio 2) with hS
  have hmem : ∀ j < 81, T j ∈ S := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · rw [hT.t0]
        exact S.one_mem
      · obtain ⟨p, hp, i, hi, e⟩ := hT.step j hj0 hj
        rw [e]
        exact S.mul_mem (ih _ hp (by omega)) (Subgroup.subset_closure ⟨i, hi, rfl⟩)
  have hsub : (S : Set J) ⊆ T '' Set.Iio 81 := by
    refine closure_le_of_right_closed _ _ ⟨0, by norm_num, hT.t0⟩ ?_
    rintro _ ⟨j, hj, rfl⟩ _ ⟨i, hi, rfl⟩
    obtain ⟨l, hl, hl'⟩ := hT.clos j hj i hi
    exact ⟨l, hl, hl'.symm⟩
  have hset : (S : Set J) = ↑((Finset.range 81).image T) := by
    ext u
    constructor
    · intro hu
      obtain ⟨n, hn, rfl⟩ := hsub hu
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨n, Finset.mem_range.2 hn, rfl⟩)
    · intro hu
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hu)
      exact hmem n (Finset.mem_range.1 hn)
  have hcard : Nat.card S = 81 := by
    have h1 : Nat.card S = ((Finset.range 81).image T).card := by
      rw [← Set.ncard_coe_finset, ← hset]
      exact Nat.card_coe_set_eq _
    rw [h1, Finset.card_image_of_injOn, Finset.card_range]
    intro n hn m hm hnm
    exact hT.inj n (Finset.mem_range.1 (Finset.mem_coe.1 hn)) m
      (Finset.mem_range.1 (Finset.mem_coe.1 hm)) hnm
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact ⟨S, IsPGroup.of_card (n := 4) (by rw [hcard]; norm_num), hmem⟩

theorem class_generating [Finite J] {T : ℕ → J}
    {S : Subgroup J} (hSp : IsPGroup 3 S) (hS : ∀ j < 81, T j ∈ S) {r : J} (hr : ClassGen T r)
    (hco : IsCoatom M) (hMS : ∀ P : Sylow 3 J, ¬ (P : Subgroup J) ≤ M) {w : J}
    (hw : IsConj r w) : SporKRestGenerating 3 w := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Z, hZ, hx, hy⟩ := hr
  refine generating_of_coatom (S := S) (Z := Z) hco hMS hSp ?_ ?_ hw
  · intro z hz
    obtain ⟨j, hj, hc, hcomm⟩ := hZ z hz
    exact ⟨T j, hS j hj, hc, hcomm⟩
  · refine (Subgroup.closure_le _).2 ?_
    rintro u (rfl | rfl)
    · exact hx
    · exact hy

theorem cover_of
    {T G : ℕ → J} (hT : TabFacts T G) (hA : ClassGen T thS)
    (hB : ClassGen T thZ) (hC : ClassGen T thU) : SporKRestCover 3 J := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [natCard_J]; norm_num)
  have hco : IsCoatom M := isCoatom_M CFSG.Sporadic.Th.th_kernel_facts
  have hMS : ∀ P : Sylow 3 J, ¬ (P : Subgroup J) ≤ M := by
    intro P hP
    have h1 : Nat.card P = 3 ^ 10 := by
      have hf : (90745943887872000 : ℕ).factorization 3 = 10 := by
        rw [show (90745943887872000 : ℕ) = 3 ^ 10 * 1536790528000 by norm_num,
          Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
          Nat.factorization_pow, Finsupp.smul_apply, Nat.prime_three.factorization_self,
          Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
        simp
      rw [P.card_eq_multiplicity, natCard_J, hf]
    have h2 : Nat.card (P : Subgroup J) ∣ Nat.card M := Subgroup.card_dvd_of_le hP
    rw [h1, card_M] at h2
    norm_num at h2
  obtain ⟨S, hSp, hS⟩ := exists_S hT
  intro E hE hcard
  have hE1 : E ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hcard
    norm_num at hcard
  obtain ⟨⟨u, hu⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hE1
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  have huo : orderOf u = 3 := orderOf_eq_prime (hE.2 u hu) hu1'
  obtain ⟨k, c, hc, e, he, hke⟩ := th_census u huo
  obtain ⟨hoS, hoZ, hoU⟩ := th_orderOf
  have hc3 : c ^ 3 = 1 := by
    rcases hc with rfl | rfl | rfl
    · have := pow_orderOf_eq_one thS
      rwa [hoS] at this
    · have := pow_orderOf_eq_one thZ
      rwa [hoZ] at this
    · have := pow_orderOf_eq_one thU
      rwa [hoU] at this
  have hfin : ∀ w, w ≠ 1 → IsConj c w → w ∈ E → ∃ x ∈ E, x ≠ 1 ∧ SporKRestGenerating 3 x := by
    intro w hw1 hcw hwE
    refine ⟨w, hwE, hw1, ?_⟩
    rcases hc with rfl | rfl | rfl
    · exact class_generating hSp hS hA hco hMS hcw
    · exact class_generating hSp hS hB hco hMS hcw
    · exact class_generating hSp hS hC hco hMS hcw
  rcases he with rfl | rfl
  · exact hfin u hu1' (isConj_iff.2 ⟨k, by rw [← hke, pow_one]⟩) hu
  · have hc2 : (c ^ 2)⁻¹ = c := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ]
      exact hc3
    refine hfin u⁻¹ (inv_ne_one.2 hu1') (isConj_iff.2 ⟨k, ?_⟩) (E.inv_mem hu)
    rw [← hke]
    calc k * c * k⁻¹ = k * (c ^ 2)⁻¹ * k⁻¹ := by rw [hc2]
      _ = (k * c ^ 2 * k⁻¹)⁻¹ := by group

end CFSG.KC.ThThreeCov

end
