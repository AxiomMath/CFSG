module

public import CFSG.LargeExtraspecial.S12TriA
public import CFSG.Fischer.Classification.Basic.Trichotomy
public import CFSG.Fischer.Classification.PartII.O3.Kill
public import CFSG.Fischer.Classification.PartII.O3.Single

public section

namespace CFSG.LargeExtraspecial.S12Tri

open Subgroup CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification

variable {X : Type} [Group X] {D : Set X}

theorem hyp_map {Y : Type} [Group Y] (hH : Hyp X D) (φ : X ≃* Y) : Hyp Y (φ '' D) := by
  refine ⟨pair_map hH.pair φ, ?_, ?_⟩
  · rw [← Subgroup.map_center_eq φ, hH.center, Subgroup.map_bot]
  · have := hH.simple
    exact (commutatorEquiv φ).symm.isSimpleGroup

theorem nonabelian_map {Y : Type} [Group Y] (φ : X ≃* Y)
    (hna : ∃ a b : commutator X, a * b ≠ b * a) : ∃ a b : commutator Y, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := hna
  refine ⟨commutatorEquiv φ a, commutatorEquiv φ b, fun h => hab ?_⟩
  rw [← map_mul, ← map_mul] at h
  exact (commutatorEquiv φ).injective h

theorem pair_normal_two_eq_bot (hP : Pair X D) (hZ : center X = ⊥)
    (hc : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → x * y = y * x → ∃ s ∈ D, s * y = y * s ∧ s * x ≠ x * s)
    (P : Subgroup X) (hPn : P.Normal) (hP2 : IsPGroup 2 P) : P = ⊥ := by
  have no3 : ∀ x ∈ P, orderOf x ≠ 3 := by
    intro x hx h3
    obtain ⟨k, hk⟩ := hP2 ⟨x, hx⟩
    have hdvd : orderOf x ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
    rw [h3] at hdvd
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd) (by norm_num)
  have key : ∀ p ∈ P, ∀ d ∈ D, p * d * p⁻¹ = d := by
    intro p hp d hd
    by_contra hne
    have he : p * d * p⁻¹ ∈ D := Pair.conj_mem hP hd p
    set e := p * d * p⁻¹ with he_def
    have hdeP : d * e ∈ P := by
      have h1 : d * p * d⁻¹ ∈ P := hPn.conj_mem p hp d
      have h2 : d * e = d * p * d⁻¹ * p⁻¹ := by rw [he_def, Pair.inv_eq hP hd]; group
      rw [h2]
      exact P.mul_mem h1 (P.inv_mem hp)
    have hcomm : d * e = e * d := by
      by_contra h
      exact no3 _ hdeP (Pair.orderOf_mul_eq_three hP hd he h)
    obtain ⟨s, hs, hse, hsd⟩ := hc d hd e he (fun h => hne h.symm) hcomm
    have hmem : s * (d * e) * s⁻¹ * (d * e)⁻¹ ∈ P :=
      P.mul_mem (hPn.conj_mem _ hdeP s) (P.inv_mem hdeP)
    have heq : s * (d * e) * s⁻¹ * (d * e)⁻¹ = (s * d) ^ 2 := by
      rw [mul_inv_rev, Pair.inv_eq hP hs, Pair.inv_eq hP hd, Pair.inv_eq hP he]
      calc s * (d * e) * s * (e * d) = s * d * (e * s) * e * d := by group
        _ = s * d * s * (e * e) * d := by rw [← hse]; group
        _ = s * d * (s * d) := by rw [Pair.mul_self hP he, mul_one, mul_assoc (s * d) s d]
        _ = (s * d) ^ 2 := (sq _).symm
    have h3 : orderOf ((s * d) ^ 2) = 3 := by
      rw [orderOf_pow' _ (by norm_num), Pair.orderOf_mul_eq_three hP hs hd hsd]
      norm_num
    exact no3 _ (heq ▸ hmem) h3
  rw [eq_bot_iff]
  intro p hp
  have hpZ : p ∈ center X := (Pair.mem_center_iff hP).2 fun e he => by
    have := key p hp e he
    calc e * p = p * e * p⁻¹ * p := by rw [this]
      _ = p * e := by group
  rw [hZ] at hpZ
  exact hpZ

theorem ncard_localClass_le_three (hH : Hyp X D) (hna : ∃ a b : commutator X, a * b ≠ b * a)
    {d : X} (hd : d ∈ D) (h3 : HasNormalPSubgroup 3 (LocalQuotient D d)) :
    (LocalClass D d).ncard ≤ 3 := by
  have hS : O3.Setting X D := ⟨hH, hna, d, hd, O3.Pair.exists_core_move hH.pair h3⟩
  by_cases hpw : ∀ y ∈ LocalClass D d, ∀ z ∈ LocalClass D d, y ≠ z → y * z ≠ z * y
  · exact hS.ncard_localClass_le_three_of_pairwise hd hpw
  · push Not at hpw
    obtain ⟨y, hy, z, hz, hyz, hc⟩ := hpw
    obtain ⟨a, ha, b, hb, hab, w, hw, v, hv, hnv⟩ := hS.exists_nonwit hd hy hz hyz hc
    obtain ⟨_, -, -, -, -, -, hconf⟩ := hS.exists_confAt_of_nonwit ha hb hab hw hv hnv
    exact (hconf.false hS).elim

theorem four_le_ncard_localClass (hP : Pair X D) {d : X}
    (hpair : ∃ x ∈ LocalClass D d, ∃ y ∈ LocalClass D d, x ≠ y ∧ x * y = y * x)
    (hcond : ∀ x ∈ LocalClass D d, ∀ y ∈ LocalClass D d, x ≠ y → x * y = y * x →
      ∃ s ∈ LocalClass D d, s * y = y * s ∧ s * x ≠ x * s) :
    4 ≤ (LocalClass D d).ncard := by
  have := Pair.finite hP
  obtain ⟨x, hx, y, hy, hxy, hc⟩ := hpair
  obtain ⟨s, hs, hsy, hsx⟩ := hcond x hx y hy hxy hc
  have hx2 : x * x = 1 := Pair.mul_self hP hx.1
  have hback : ∀ g, x * (x * g * x) * x = g := fun g => by
    calc x * (x * g * x) * x = (x * x) * g * (x * x) := by group
      _ = g := by rw [hx2, one_mul, mul_one]
  have ht : x * s * x ∈ LocalClass D d := by
    refine ⟨Pair.mul_mul_mem hP hx.1 hs.1, fun h => hs.2.1 ?_, ?_⟩
    · rw [← hback s, h]
      calc x * d * x = d * x * x := by rw [hx.2.2]
        _ = d := by rw [mul_assoc, hx2, mul_one]
    · calc x * s * x * d = x * s * (x * d) := by group
        _ = x * s * (d * x) := by rw [hx.2.2]
        _ = x * (s * d) * x := by group
        _ = x * (d * s) * x := by rw [hs.2.2]
        _ = (x * d) * s * x := by group
        _ = (d * x) * s * x := by rw [hx.2.2]
        _ = d * (x * s * x) := by group
  have hxs : x ≠ s := fun h => hsx (by rw [h])
  have hys : y ≠ s := fun h => hsx (by rw [← h, hc])
  have hxt : x ≠ x * s * x := fun h => hxs (by
    rw [← hback s, ← h, hx2, one_mul])
  have hst : s ≠ x * s * x := fun h => hsx (by
    calc s * x = x * s * x * x := by rw [← h]
      _ = x * s := by rw [mul_assoc, hx2, mul_one])
  have hyt : y ≠ x * s * x := fun h => hys (by
    calc y = x * y * x := by rw [hc, mul_assoc, hx2, mul_one]
      _ = x * (x * s * x) * x := by rw [← h]
      _ = s := hback s)
  have hsub : ({x, y, s, x * s * x} : Set X) ⊆ LocalClass D d := by
    intro z hz
    rcases hz with rfl | rfl | rfl | rfl
    exacts [hx, hy, hs, ht]
  have h4 : ({x, y, s, x * s * x} : Set X).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair hst]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hys, hyt⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hxy, hxs, hxt⟩
  calc 4 = ({x, y, s, x * s * x} : Set X).ncard := h4.symm
    _ ≤ (LocalClass D d).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)

theorem mem_normalizer_of_conj {G : Type*} [Group G] {N : Subgroup G} {c : G}
    (h1 : ∀ n ∈ N, c * n * c⁻¹ ∈ N) (h2 : ∀ n ∈ N, c⁻¹ * n * c ∈ N) :
    c ∈ normalizer (N : Set G) := by
  rw [mem_normalizer_iff]
  intro n
  refine ⟨h1 n, fun h => ?_⟩
  have := h2 _ h
  simpa [mul_assoc] using this

open Classical in
@[expose] noncomputable def piHom {d : X} (h2 : (commutator X).index = 2) (hd2 : d * d = 1) :
    centralizer ({d} : Set X) →* X where
  toFun x := if (x : X) ∈ commutator X then x else x * d
  map_one' := by simp [(commutator X).one_mem]
  map_mul' x y := by
    have hyd : (y : X) * d = d * y := mem_centralizer_singleton_iff.mp y.2
    have hm := Subgroup.mul_mem_iff_of_index_two h2 (a := (x : X)) (b := (y : X))
    simp only [coe_mul]
    by_cases hx : (x : X) ∈ commutator X <;> by_cases hy : (y : X) ∈ commutator X
    · rw [ite_eq_left (hm.2 (iff_of_true hx hy)), ite_eq_left hx, ite_eq_left hy]
    · rw [ite_eq_right (fun h => hy ((hm.1 h).1 hx)), ite_eq_left hx, ite_eq_right hy, mul_assoc]
    · rw [ite_eq_right (fun h => hx ((hm.1 h).2 hy)), ite_eq_right hx, ite_eq_left hy, mul_assoc,
        mul_assoc, hyd]
    · rw [ite_eq_left (hm.2 (iff_of_false hx hy)), ite_eq_right hx, ite_eq_right hy]
      calc (x : X) * y = x * (d * d) * y := by rw [hd2, mul_one]
        _ = x * d * (d * y) := by group
        _ = x * d * (y * d) := by rw [hyd]

open Classical in
theorem piHom_apply {d : X} (h2 : (commutator X).index = 2) (hd2 : d * d = 1)
    (x : centralizer ({d} : Set X)) :
    piHom h2 hd2 x = if (x : X) ∈ commutator X then (x : X) else x * d := rfl

theorem index_commutator_eq_two (hP : Pair X D) {d : X} (hdX : d ∉ commutator X) :
    (commutator X).index = 2 := by
  have := Pair.finite hP
  have hle := Pair.index_commutator_le_two hP
  have h0 : (commutator X).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 : (commutator X).index ≠ 1 := fun h =>
    hdX (by rw [Subgroup.index_eq_one.mp h]; exact mem_top d)
  omega

theorem localGroup_le_centralizer_self (d : X) :
    LocalGroup D d ≤ centralizer ({d} : Set X) := by
  rw [LocalGroup, closure_le]
  intro f hf
  exact mem_centralizer_singleton_iff.mpr hf.2.2

theorem conj_mem_localGroup_of_commute (hP : Pair X D) {d c : X} (hc : c * d = d * c) {l : X}
    (hl : l ∈ LocalGroup D d) : c * l * c⁻¹ ∈ LocalGroup D d := by
  have hle : (LocalGroup D d).map (MulAut.conj c).toMonoidHom ≤ LocalGroup D d := by
    rw [LocalGroup, MonoidHom.map_closure, closure_le]
    rintro _ ⟨f, hf, rfl⟩
    refine subset_closure ⟨Pair.conj_mem hP hf.1 c, fun h => hf.2.1 ?_, ?_⟩
    · have h' : c * f * c⁻¹ = c * d * c⁻¹ := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
        rw [h, hc, mul_inv_cancel_right]
      simpa using h'
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have hc' : c⁻¹ * d = d * c⁻¹ := (Commute.inv_left (show Commute c d from hc)).eq
      calc c * f * c⁻¹ * d = c * f * (c⁻¹ * d) := by group
        _ = c * (f * d) * c⁻¹ := by rw [hc']; group
        _ = c * (d * f) * c⁻¹ := by rw [hf.2.2]
        _ = (c * d) * f * c⁻¹ := by group
        _ = d * (c * f * c⁻¹) := by rw [hc]; group
  exact hle ⟨l, hl, rfl⟩

theorem triGood_of_local (hH : Hyp X D) (hna : ∃ a b : commutator X, a * b ≠ b * a) {d : X}
    (hd : d ∈ D) (hdX : d ∉ commutator X)
    (hcent : ∀ y : X, y * d = d * y → (∀ f ∈ LocalClass D d, y * f = f * y) → y = 1 ∨ y = d)
    (hpair : ∃ x ∈ LocalClass D d, ∃ y ∈ LocalClass D d, x ≠ y ∧ x * y = y * x)
    (hcond : ∀ x ∈ LocalClass D d, ∀ y ∈ LocalClass D d, x ≠ y → x * y = y * x →
      ∃ s ∈ LocalClass D d, s * y = y * s ∧ s * x ≠ x * s) :
    TriGood X d := by
  classical
  have hP := hH.pair
  have := Pair.finite hP
  have h2 := index_commutator_eq_two hP hdX
  have hd2 : d * d = 1 := Pair.mul_self hP hd
  have hLC := localGroup_le_centralizer_self (D := D) d
  set L := LocalGroup D d with hL
  set π : L →* X := (piHom h2 hd2).comp (Subgroup.inclusion hLC) with hπ
  have hπv : ∀ l : L, π l = if (l : X) ∈ commutator X then (l : X) else l * d := fun l =>
    piHom_apply h2 hd2 _
  have hfX : ∀ f ∈ D, f ∉ commutator X := fun f hf h => hdX (by
    have h1 := Pair.mul_inv_mem_commutator hP hd hf
    have h3 : d⁻¹ ∈ commutator X := by
      simpa using (commutator X).mul_mem ((commutator X).inv_mem h) h1
    simpa using (commutator X).inv_mem h3)
  set N := π.range with hN
  have hNC : N ≤ commutator X ⊓ centralizer {d} := by
    rintro _ ⟨l, rfl⟩
    have hld : (l : X) * d = d * l := mem_centralizer_singleton_iff.mp (hLC l.2)
    rw [hπv]
    split_ifs with h
    · exact ⟨h, hLC l.2⟩
    · refine mem_inf.mpr ⟨(Subgroup.mul_mem_iff_of_index_two h2).2 (iff_of_false h hdX), ?_⟩
      rw [mem_centralizer_singleton_iff, ← mul_assoc, ← hld]
  have hconj : ∀ c ∈ commutator X ⊓ centralizer {d}, ∀ n ∈ N, c * n * c⁻¹ ∈ N := by
    rintro c ⟨hcX, hcd⟩ _ ⟨l, rfl⟩
    have hcd' : c * d = d * c := mem_centralizer_singleton_iff.mp hcd
    have hl' : c * l * c⁻¹ ∈ L := conj_mem_localGroup_of_commute hP hcd' l.2
    have hmem : c * l * c⁻¹ ∈ commutator X ↔ (l : X) ∈ commutator X := by
      refine ⟨fun h => ?_, fun h => (inferInstance : (commutator X).Normal).conj_mem _ h c⟩
      have := (inferInstance : (commutator X).Normal).conj_mem _ h c⁻¹
      simpa [mul_assoc] using this
    refine ⟨⟨_, hl'⟩, ?_⟩
    rw [hπv, hπv]
    by_cases h : (l : X) ∈ commutator X
    · rw [ite_eq_left (hmem.2 h), ite_eq_left h]
    · rw [ite_eq_right (mt hmem.1 h), ite_eq_right h]
      have hc' : c⁻¹ * d = d * c⁻¹ := (Commute.inv_left (show Commute c d from hcd')).eq
      calc c * l * c⁻¹ * d = c * l * (c⁻¹ * d) := by group
        _ = c * (l * d) * c⁻¹ := by rw [hc']; group
  have hNn : commutator X ⊓ centralizer {d} ≤ normalizer (N : Set X) := fun c hc =>
    mem_normalizer_of_conj (hconj c hc) (by simpa using hconj c⁻¹ (inv_mem hc))
  have hCN : ∀ c ∈ commutator X ⊓ centralizer {d}, (∀ n ∈ N, c * n = n * c) → c = 1 := by
    rintro c ⟨hcX, hcd⟩ hcN
    have hcd' : c * d = d * c := mem_centralizer_singleton_iff.mp hcd
    have hcf : ∀ f ∈ LocalClass D d, c * f = f * c := by
      intro f hf
      have hfL : f ∈ L := subset_closure hf
      have hn : f * d ∈ N := ⟨⟨f, hfL⟩, by rw [hπv, ite_eq_right (hfX f hf.1)]⟩
      have h1 := hcN _ hn
      calc c * f = c * (f * d) * d⁻¹ := by group
        _ = f * d * c * d⁻¹ := by rw [h1]
        _ = f * (d * c) * d⁻¹ := by group
        _ = f * (c * d) * d⁻¹ := by rw [hcd']
        _ = f * c := by group
    rcases hcent c hcd' hcf with h | h
    · exact h
    · exact absurd (h ▸ hcX) hdX
  have hker : π.ker = center L := by
    ext l
    rw [MonoidHom.mem_ker, hπv, Subgroup.mem_center_iff]
    constructor
    · intro h g
      split_ifs at h with hl
      · rw [Subtype.ext (show (l : X) = ((1 : L) : X) from h), mul_one, one_mul]
      · have hl' : (l : X) = d := by
          calc (l : X) = l * d * d := by rw [mul_assoc, hd2, mul_one]
            _ = d := by rw [h, one_mul]
        apply Subtype.ext
        simp only [coe_mul]
        rw [hl']
        exact mem_centralizer_singleton_iff.mp (hLC g.2)
    · intro h
      have hlf : ∀ f ∈ LocalClass D d, (l : X) * f = f * l := fun f hf =>
        (congrArg Subtype.val (h ⟨f, subset_closure hf⟩)).symm
      have hld : (l : X) * d = d * l := mem_centralizer_singleton_iff.mp (hLC l.2)
      rcases hcent l hld hlf with h1 | h1
      · rw [ite_eq_left (by rw [h1]; exact one_mem _), h1]
      · rw [ite_eq_right (by rw [h1]; exact hdX), h1, hd2]
  let e : LocalQuotient D d ≃* N :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange π)
  have hS := hH.simple
  have hZ := hH.center
  have hPH := Pair.pair_localQuotient hP hZ hS hna hd
  have hZH := Pair.center_localQuotient hP hZ hS hd
  have hcondH : ∀ x ∈ LocalImages D d, ∀ y ∈ LocalImages D d, x ≠ y → x * y = y * x →
      ∃ s ∈ LocalImages D d, s * y = y * s ∧ s * x ≠ x * s := by
    intro x hx y hy hxy hc
    rw [← range_starImage] at hx hy
    obtain ⟨f, rfl⟩ := hx
    obtain ⟨g, rfl⟩ := hy
    have hfg : (f : X) ≠ g := fun h => hxy (congrArg _ (Subtype.ext h))
    have hc' : (f : X) * g = g * f := (Pair.starImage_commute_iff hP f g).1 hc
    obtain ⟨s, hs, hsg, hsf⟩ := hcond f f.2 g g.2 hfg hc'
    refine ⟨starImage D d ⟨s, hs⟩, by rw [← range_starImage]; exact ⟨_, rfl⟩, ?_, ?_⟩
    · exact (Pair.starImage_commute_iff hP ⟨s, hs⟩ g).2 hsg
    · exact fun h => hsf ((Pair.starImage_commute_iff hP ⟨s, hs⟩ f).1 h)
  have hO2 := pair_normal_two_eq_bot hPH hZH hcondH
  have hO3 : ∀ M : Subgroup (LocalQuotient D d), M.Normal → IsPGroup 3 M → M = ⊥ := by
    intro M hM hM3
    by_contra hne
    have h1 := ncard_localClass_le_three hH hna hd ⟨M, hM, hne, hM3⟩
    have h2' := four_le_ncard_localClass hP hpair hcond
    omega
  have hHns : ¬ Group.IsSolvable (LocalQuotient D d) := by
    have := Pair.finite hPH
    obtain ⟨q, hq⟩ := Pair.nonempty hPH
    have htop : (⊤ : Subgroup (LocalQuotient D d)) ≠ ⊥ := fun h => Pair.ne_one hPH hq (by
      have hq' := mem_top q
      rwa [h, mem_bot] at hq')
    obtain ⟨M, hMn, -, hMbot, hmin⟩ := CFSG.exists_minimal_normal_le ⊤ inferInstance htop
    intro hsol
    exact Pair.not_isSolvable_of_minimal hPH hZH hO2 hO3 hMn hMbot hmin inferInstance
  refine triGood_of_normal hNC hNn hCN ?_ ?_
  · exact fun hsol => hHns (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom)
      e.injective)
  · intro P hPn hP2
    have hP' := hO2 (P.map e.symm.toMonoidHom) (hPn.map _ e.symm.surjective)
      (hP2.map _)
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.symm.injective).mp hP'

end CFSG.LargeExtraspecial.S12Tri
