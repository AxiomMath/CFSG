module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5InvolutionFiveBar
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveConj
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5InvolutionFive
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5InvolutionRankTwo

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace Involution

open SectionSix

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

theorem mem_normalizer_of_centralizes {O A : Subgroup G} (hOA : O ≤ A) {y : G}
    (hy : aschbacherThm5Centralizes O A y) : y ∈ Subgroup.normalizer (A : Set G) := by
  have h : ∀ a ∈ A, y⁻¹ * a * (y⁻¹)⁻¹ ∈ A := by
    intro a ha
    have h1 := hOA (hy a⁻¹ (A.inv_mem ha))
    rw [inv_inv] at h1
    have h2 : y⁻¹ * a * (y⁻¹)⁻¹ = (y⁻¹ * a * y * a⁻¹) * a := by group
    rw [h2]
    exact A.mul_mem h1 ha
  have := AschbacherToolkit.mem_normalizer_of_conj_le h
  simpa using (Subgroup.normalizer (A : Set G)).inv_mem this

omit [Finite G] in
theorem center_eq_bot_of_simple {X : Type*} [Group X] [IsSimpleGroup X]
    (hX : Group.IsPerfect X) : Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    have hcomm : commutator X = ⊥ := by
      rw [eq_bot_iff, _root_.commutator_def, Subgroup.commutator_le]
      intro x _ y _
      have hy : y ∈ Subgroup.center X := h ▸ Subgroup.mem_top y
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.mp hy x)
    have htop : (⊤ : Subgroup X) = ⊥ := hX.commutator_eq_top.symm.trans hcomm
    obtain ⟨x, y, hxy⟩ := exists_pair_ne X
    have hx : x ∈ (⊥ : Subgroup X) := htop ▸ Subgroup.mem_top x
    have hy : y ∈ (⊥ : Subgroup X) := htop ▸ Subgroup.mem_top y
    rw [Subgroup.mem_bot] at hx hy
    exact hxy (hx.trans hy.symm)

omit [Finite G] in
@[expose] noncomputable def conjFactorsEquiv (g : G) (k : Fin r) :
    Abar k ≃* conjFactors D Abar g k :=
  (Abar k).equivMapOfInjective _ (Conj.quotientEquiv (MulAut.conj g⁻¹) D).injective

omit [Finite G] in
theorem centralizes_mul {A : Subgroup G} (hAD : A ≤ D) {x y : G}
    (hx : x ∈ Subgroup.normalizer (D : Set G)) (hy : y ∈ Subgroup.normalizer (D : Set G))
    (hxc : aschbacherThm5Centralizes (aschbacherThm5Core D) A x)
    (hyc : aschbacherThm5Centralizes (aschbacherThm5Core D) A y) :
    aschbacherThm5Centralizes (aschbacherThm5Core D) A (x * y) := by
  have h1 := (centralizes_iff_mem_centralizer D A hAD ⟨x, hx⟩).mp hxc
  have h2 := (centralizes_iff_mem_centralizer D A hAD ⟨y, hy⟩).mp hyc
  have := (centralizes_iff_mem_centralizer D A hAD (⟨x, hx⟩ * ⟨y, hy⟩)).mpr
    (by rw [map_mul]; exact Subgroup.mul_mem _ h1 h2)
  exact this

theorem map_other_factor (hyp : Hyp61 G D r Abar)
    (hfin : ∀ i j m : Fin r, i ≠ j → m ≠ i → m = j) {h : G}
    (hh : h ∈ Subgroup.normalizer (D : Set G)) {i j i' j' : Fin r} (hii' : i ≠ i')
    (hjj' : j ≠ j')
    (hij : (aschbacherThm5Preimage D (Abar i)).map (MulAut.conj h).toMonoidHom =
      aschbacherThm5Preimage D (Abar j)) :
    (aschbacherThm5Preimage D (Abar i')).map (MulAut.conj h).toMonoidHom =
      aschbacherThm5Preimage D (Abar j') := by
  obtain ⟨n, hn⟩ := hyp.hperm h hh i'
  have hnj : n ≠ j := by
    rintro rfl
    apply hii'
    apply hyp.hdistinct
    apply preimage_injective D
    apply Subgroup.map_injective (f := (MulAut.conj h).toMonoidHom) (MulAut.conj h).injective
    rw [hij, hn]
  rw [hn, hfin j j' n hjj' hnj]

theorem mem_factor_of_centralizes (hin : SectionSevenBase) (hC : Counterexample G D r Abar)
    {t g : G} (h : Hyp71 D t g) {j m : Fin r} (hjm : j ≠ m)
    (htj : aschbacherThm5Centralizes (aschbacherThm5Core (rightConjugate D g))
      (aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g j)) t)
    {c : G} (hc2 : orderOf c = 2) (hct : c * t = t * c)
    (hcH : Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (D : Set G))
    (hcm : c ∈ Subgroup.normalizer
      (aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m) : Set G))
    (htm : t ∈ Subgroup.normalizer
      (aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m) : Set G)) :
    t ∈ aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m) := by
  have hC' := hC.conj g
  set L := aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m) with hL
  have hN' : Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G) =
      rightConjugate (Subgroup.normalizer (D : Set G)) g := normalizer_rightConjugate D g
  have htN' : t ∈ Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G) :=
    hN' ▸ h.mem_conjugate
  have hpg : ∀ x : G, orderOf x = 2 → IsPGroup 2 (Subgroup.zpowers x) := fun x hx =>
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨x, hxL, hx2, hxc⟩ := exists_involution_commute (hpg c hc2) hcm (factor_even hC'.hyp m)
  set X := L ⊓ Subgroup.centralizer ({c} : Set G) with hX
  have hxX : x ∈ X := Subgroup.mem_inf.mpr ⟨hxL, Subgroup.mem_centralizer_singleton_iff.mpr hxc⟩
  have hXeven : Even (Nat.card X) := by
    have hdvd := Subgroup.orderOf_dvd_natCard X hxX
    rw [hx2] at hdvd
    exact even_iff_two_dvd.mpr hdvd
  have htX : t ∈ Subgroup.normalizer (X : Set G) := by
    apply AschbacherToolkit.mem_normalizer_of_conj_le
    intro v hv
    obtain ⟨hvL, hvC⟩ := Subgroup.mem_inf.mp hv
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp htm v).mp hvL, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hvc : v * c = c * v := Subgroup.mem_centralizer_singleton_iff.mp hvC
    have hct' : c * t⁻¹ = t⁻¹ * c := by
      calc c * t⁻¹ = t⁻¹ * (t * c) * t⁻¹ := by group
        _ = t⁻¹ * (c * t) * t⁻¹ := by rw [hct]
        _ = t⁻¹ * c := by group
    calc t * v * t⁻¹ * c = t * v * (t⁻¹ * c) := by group
      _ = t * v * (c * t⁻¹) := by rw [hct']
      _ = t * (v * c) * t⁻¹ := by group
      _ = t * (c * v) * t⁻¹ := by rw [hvc]
      _ = (t * c) * v * t⁻¹ := by group
      _ = (c * t) * v * t⁻¹ := by rw [hct]
      _ = c * (t * v * t⁻¹) := by group
  obtain ⟨w, hwX', hw2, hwt⟩ := exists_involution_commute (hpg t h.orderOf_eq) htX hXeven
  have hwX := Subgroup.mem_inf.mp hwX'
  by_contra htL
  have hwtne : t ≠ w := fun heq => htL (heq ▸ hwX.1)
  have hw1 : w ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hw2
    omega
  have hwH : w ∈ Subgroup.normalizer (D : Set G) := hcH hwX.2
  have hwN' : w ∈ Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G) :=
    Subgroup.le_normalizer (preimage_le _ _ hwX.1)
  have htt : t * t = 1 := by rw [← pow_two, ← h.orderOf_eq, pow_orderOf_eq_one]
  have hww : w * w = 1 := by rw [← pow_two, ← hw2, pow_orderOf_eq_one]
  have htw : t * w = w * t := hwt.symm
  apply no_four_group hin hC (h.not_mem hC.hyp)
    (hUH := fun u hu => by
      rcases mem_fourGroupOfPair.mp hu with rfl | rfl | rfl | rfl
      · exact Subgroup.one_mem _
      · exact h.mem
      · exact hwH
      · exact Subgroup.mul_mem _ h.mem hwH)
    (isFourGroup_fourGroupOfPair h.orderOf_eq hw2 htw hwtne)
  intro u hu hu1
  rw [← hN']
  rcases mem_fourGroupOfPair.mp hu with rfl | rfl | rfl | rfl
  · exact absurd rfl hu1
  · exact hN' ▸ h.centralizer_le
  · exact centralizer_le_of_mem_factor hC' hwX.1 (two_power_of_orderOf hw2) hw1
  · have hwj : aschbacherThm5Centralizes (aschbacherThm5Core (rightConjugate D g))
        (aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g j)) w :=
      cross_factor_centralizes _ _ hC'.hyp.hcomm j m hjm w hwX.1
    have hsq : (t * w) ^ 2 = 1 := by
      rw [pow_two]
      calc t * w * (t * w) = t * (w * t) * w := by group
        _ = t * (t * w) * w := by rw [htw]
        _ = (t * t) * (w * w) := by group
        _ = 1 := by rw [htt, hww, one_mul]
    exact centralizer_le_of_centralizes hC' j (two_power_of_sq hsq) hu1
      (centralizes_mul (preimage_le _ _) htN' hwN' htj hwj)

theorem lemma_7_5 (hin : SectionSevenInputs) (hC : Counterexample G D r Abar) {t g : G}
    (h : Hyp71 D t g)
    (hcent : ∃ j : Fin r, aschbacherThm5Centralizes (aschbacherThm5Core D)
      (aschbacherThm5Preimage D (Abar j)) (g * t * g⁻¹)) (k : Fin r) :
    (aschbacherThm5Preimage D (Abar k)).map (MulAut.conj t).toMonoidHom ≠
      aschbacherThm5Preimage D (Abar k) := by
  intro hk
  have hbase : SectionSevenBase := hin.toSectionSevenBase
  have hyp := hC.hyp
  have hfix := fixes_all_of_fixes hbase hC h hk
  have hg : g ∉ Subgroup.normalizer (D : Set G) := h.not_mem hyp
  have hsd := hin.lemma_7_4_dihedral hC t g h.mem h.orderOf_eq hg hcent hfix
  obtain ⟨hr2, -⟩ := r_eq_two_and_rank hbase hC h
  have hfin : ∀ i j m : Fin r, i ≠ j → m ≠ i → m = j := by
    intro i j m hij hmi
    rw [Ne, Fin.ext_iff] at hij hmi
    rw [Fin.ext_iff]
    omega
  obtain ⟨i₀, i₁, h01⟩ : ∃ i₀ i₁ : Fin r, i₀ ≠ i₁ :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff]⟩
  have hpg : ∀ x : G, orderOf x = 2 → IsPGroup 2 (Subgroup.zpowers x) := fun x hx =>
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  have hne1 : ∀ x : G, orderOf x = 2 → x ≠ 1 := by
    rintro x hx rfl
    rw [orderOf_one] at hx
    omega
  obtain ⟨a, ha, ha2, hat⟩ := lemma_7_2_right hC h.orderOf_eq i₀
    (Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hfix i₀))
  have haN₁ : a ∈ Subgroup.normalizer (aschbacherThm5Preimage D (Abar i₁) : Set G) :=
    mem_normalizer_of_centralizes (core_le_preimage D _)
      (cross_factor_centralizes D Abar hyp.hcomm i₁ i₀ h01.symm a ha)
  obtain ⟨x, hx, hx2, hxa⟩ := exists_involution_commute (hpg a ha2) haN₁ (factor_even hyp i₁)
  set X := aschbacherThm5Preimage D (Abar i₁) ⊓ Subgroup.centralizer ({a} : Set G) with hX
  have hXeven : Even (Nat.card X) := by
    have hdvd := Subgroup.orderOf_dvd_natCard X
      (Subgroup.mem_inf.mpr ⟨hx, Subgroup.mem_centralizer_singleton_iff.mpr hxa⟩)
    rw [hx2] at hdvd
    exact even_iff_two_dvd.mpr hdvd
  have htX : t ∈ Subgroup.normalizer (X : Set G) := by
    apply AschbacherToolkit.mem_normalizer_of_conj_le
    intro v hv
    obtain ⟨hvA, hvC⟩ := Subgroup.mem_inf.mp hv
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp
      (Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hfix i₁)) v).mp hvA, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hva : v * a = a * v := Subgroup.mem_centralizer_singleton_iff.mp hvC
    have hat' : a * t⁻¹ = t⁻¹ * a := by
      calc a * t⁻¹ = t⁻¹ * (t * a) * t⁻¹ := by group
        _ = t⁻¹ * (a * t) * t⁻¹ := by rw [hat]
        _ = t⁻¹ * a := by group
    calc t * v * t⁻¹ * a = t * v * (a * t⁻¹) := by rw [hat']; group
      _ = t * (v * a) * t⁻¹ := by group
      _ = t * (a * v) * t⁻¹ := by rw [hva]
      _ = (t * a) * v * t⁻¹ := by group
      _ = (a * t) * v * t⁻¹ := by rw [hat]
      _ = a * (t * v * t⁻¹) := by group
  obtain ⟨b, hbX, hb2, hbt⟩ := exists_involution_commute (hpg t h.orderOf_eq) htX hXeven
  obtain ⟨hb, hbC⟩ := Subgroup.mem_inf.mp hbX
  have hab : a * b = b * a := (Subgroup.mem_centralizer_singleton_iff.mp hbC).symm
  have hne : a ≠ b := by
    intro heq
    have haD : a ∈ D := preimage_le D _ ha
    have hq₀ := (mem_preimage_iff D _ ⟨a, haD⟩).mp ha
    have hq₁ := (mem_preimage_iff D _ ⟨a, haD⟩).mp (heq ▸ hb)
    have hperf := semisimple_perfect _ (hyp.hsemisimple i₀)
    have : IsSimpleGroup (Abar i₀) := (hsd i₀).1
    have hz : (⟨_, hq₀⟩ : Abar i₀) ∈ Subgroup.center (Abar i₀) := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hyp.hcomm i₀ i₁ h01 y y.2 _ hq₁)
    rw [center_eq_bot_of_simple hperf, Subgroup.mem_bot] at hz
    have h1 : QuotientGroup.mk' (aschbacherThm5OddCore D) (⟨a, haD⟩ : D) = 1 :=
      congrArg Subtype.val hz
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have hodd := Subgroup.orderOf_dvd_natCard (aschbacherThm5OddCore D) h1
    rw [Subgroup.orderOf_mk, ha2] at hodd
    exact (Nat.not_even_iff_odd.mpr (oddCore_odd D)) (even_iff_two_dvd.mpr hodd)
  have hC' := hC.conj g
  have hN' : Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G) =
      rightConjugate (Subgroup.normalizer (D : Set G)) g := normalizer_rightConjugate D g
  have haN' : a ∈ Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G) :=
    hN' ▸ h.centralizer_le (Subgroup.mem_centralizer_singleton_iff.mpr hat)
  have hbN' : b ∈ Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G) :=
    hN' ▸ h.centralizer_le (Subgroup.mem_centralizer_singleton_iff.mpr hbt)
  have htN' : t ∈ Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G) :=
    hN' ▸ h.mem_conjugate
  have hHH : rightConjugate (Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G))
      g⁻¹ = Subgroup.normalizer (D : Set G) := by
    rw [hN', rightConjugate_mul, mul_inv_cancel, rightConjugate_one]
  have hg' : g⁻¹ ∉ Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G) := by
    intro hmem
    rw [hN', mem_rightConjugate_iff] at hmem
    apply hg
    have : g * g⁻¹ * g⁻¹ = g⁻¹ := by group
    rw [this] at hmem
    simpa using (Subgroup.normalizer (D : Set G)).inv_mem hmem
  have haC : Subgroup.centralizer ({a} : Set G) ≤ rightConjugate
      (Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G)) g⁻¹ :=
    hHH ▸ centralizer_le_of_mem_factor hC ha (two_power_of_orderOf ha2) (hne1 a ha2)
  have hbC' : Subgroup.centralizer ({b} : Set G) ≤ rightConjugate
      (Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G)) g⁻¹ :=
    hHH ▸ centralizer_le_of_mem_factor hC hb (two_power_of_orderOf hb2) (hne1 b hb2)
  have hsd' : ∀ m, IsSimpleGroup (conjFactors D Abar g m) ∧
      AschbacherKnownGroup.HasDihedralSylowTwo (conjFactors D Abar g m) := by
    intro m
    have := (hsd m).1
    exact ⟨isSimpleGroup_of_mulEquiv (conjFactorsEquiv g m),
      hasDihedralSylowTwo_of_mulEquiv (conjFactorsEquiv g m) (hsd m).2⟩
  have hfinal : ∀ m : Fin r, aschbacherThm5Centralizes (aschbacherThm5Core (rightConjugate D g))
      (aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m)) (a * b) → False :=
    fun m hm => false_of_product_centralizes hbase hC h01 ha hb ha2 hb2 hab hne (hsd i₀).2 hg
      ⟨m, (centralizes_conj_iff D Abar g m (a * b)).mp hm⟩
  set a' : Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G) := ⟨a, haN'⟩
  set b' : Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G) := ⟨b, hbN'⟩
  have ha'2 : orderOf a' = 2 := by rw [Subgroup.orderOf_mk, ha2]
  have hb'2 : orderOf b' = 2 := by rw [Subgroup.orderOf_mk, hb2]
  have hab' : a' * b' = b' * a' := Subtype.ext hab
  have hmixed : ∀ c c' : G, orderOf c = 2 → c * t = t * c → c' * t = t * c' →
      Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (D : Set G) →
      c ∈ Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G) →
      c' ∈ Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G) →
      (aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g i₀)).map
        (MulAut.conj c).toMonoidHom =
        aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g i₀) →
      (aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g i₀)).map
        (MulAut.conj c').toMonoidHom =
        aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g i₁) → False := by
    intro c c' hc2 hct hc't hcH hcN hc'N hcfix hc'swap
    obtain ⟨j, hj⟩ := hcent
    have htj := (centralizes_conj_iff D Abar g j t).mpr hj
    obtain ⟨m, hjm⟩ : ∃ m : Fin r, j ≠ m := ⟨if j = i₀ then i₁ else i₀, by
      split_ifs with hj0
      · rw [hj0]; exact h01
      · exact hj0⟩
    have hcall : ∀ n : Fin r,
        (aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g n)).map
          (MulAut.conj c).toMonoidHom =
          aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g n) := by
      intro n
      by_cases hn : n = i₀
      · rw [hn]; exact hcfix
      · rw [hfin i₀ i₁ n h01 hn]
        exact map_other_factor hC'.hyp hfin hcN h01 h01 hcfix
    have htjN := mem_normalizer_of_centralizes (core_le_preimage _ _) htj
    have htm : (aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m)).map
        (MulAut.conj t).toMonoidHom =
        aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m) :=
      map_other_factor hC'.hyp hfin htN' hjm hjm
        (Subgroup.mem_normalizer_iff_map_conj_eq.mp htjN)
    have htL := mem_factor_of_centralizes hbase hC h hjm htj hc2 hct hcH
      (Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hcall m))
      (Subgroup.mem_normalizer_iff_map_conj_eq.mpr htm)
    have hc'1 := map_other_factor hC'.hyp hfin hc'N h01 h01.symm hc'swap
    have hc'm : (aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m)).map
        (MulAut.conj c').toMonoidHom =
        aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g j) := by
      by_cases hm0 : m = i₀
      · rw [hm0] at hjm ⊢
        rw [hfin i₀ i₁ j h01 hjm]
        exact hc'swap
      · have hm1 : m = i₁ := hfin i₀ i₁ m h01 hm0
        rw [hm1] at hjm ⊢
        rw [hfin i₁ i₀ j (Ne.symm h01) hjm]
        exact hc'1
    have htLj : t ∈ aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g j) := by
      rw [← hc'm]
      refine ⟨t, htL, ?_⟩
      change c' * t * c'⁻¹ = t
      rw [hc't]
      group
    have htD : t ∈ rightConjugate D g := preimage_le _ _ htL
    have hq_m := (mem_preimage_iff (rightConjugate D g) _ ⟨t, htD⟩).mp htL
    have hq_j := (mem_preimage_iff (rightConjugate D g) _ ⟨t, htD⟩).mp htLj
    have hperf := semisimple_perfect _ (hC'.hyp.hsemisimple m)
    have : IsSimpleGroup (conjFactors D Abar g m) := (hsd' m).1
    have hz : (⟨_, hq_m⟩ : conjFactors D Abar g m) ∈ Subgroup.center (conjFactors D Abar g m) := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hC'.hyp.hcomm m j hjm.symm y y.2 _ hq_j)
    rw [center_eq_bot_of_simple hperf, Subgroup.mem_bot] at hz
    have h1 : QuotientGroup.mk' (aschbacherThm5OddCore (rightConjugate D g))
        (⟨t, htD⟩ : rightConjugate D g) = 1 := congrArg Subtype.val hz
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have hodd := Subgroup.orderOf_dvd_natCard _ h1
    rw [Subgroup.orderOf_mk, h.orderOf_eq] at hodd
    exact (Nat.not_even_iff_odd.mpr (oddCore_odd _)) (even_iff_two_dvd.mpr hodd)
  have haH := centralizer_le_of_mem_factor hC ha (two_power_of_orderOf ha2) (hne1 a ha2)
  have hbH := centralizer_le_of_mem_factor hC hb (two_power_of_orderOf hb2) (hne1 b hb2)
  obtain ⟨ja, hja⟩ := hC'.hyp.hperm a haN' i₀
  obtain ⟨jb, hjb⟩ := hC'.hyp.hperm b hbN' i₀
  by_cases hsa : ja = i₀
  · rw [hsa] at hja
    by_cases hsb : jb = i₀
    · rw [hsb] at hjb
      exact hfinal i₀ (centralizes_of_normalizes hbase hC' hg' ha'2 hb'2 hab' haC hbC' i₀
        (hsd' i₀) hja hjb)
    · rw [hfin i₀ i₁ jb h01 hsb] at hjb
      exact hmixed a b ha2 hat hbt haH haN' hbN' hja hjb
  · rw [hfin i₀ i₁ ja h01 hsa] at hja
    by_cases hsb : jb = i₀
    · rw [hsb] at hjb
      exact hmixed b a hb2 hbt hat hbH hbN' haN' hjb hja
    · rw [hfin i₀ i₁ jb h01 hsb] at hjb
      exact hfinal i₀ (centralizes_of_swap hC' hg' ha'2 hb'2 hab' haC hbC' h01 (hsd' i₀).1
        hja hjb)

end Involution

end CFSG.ComponentClassification.AschbacherTheorem5
