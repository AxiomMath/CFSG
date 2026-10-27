module

public import CFSG.Fischer.Classification.PartII.O3.Witness

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer

namespace O3

variable {X : Type} [Group X] {E : Set X}

section Orbit

@[expose] def conjOrbit (K : Subgroup X) (a : X) : Set X := {b | ∃ k ∈ K, k * a * k⁻¹ = b}

theorem conjOrbit_eq (K : Subgroup X) (a : X) :
    conjOrbit K a =
      MulAction.orbit (K.map (ConjAct.toConjAct : X ≃* ConjAct X).toMonoidHom) a := by
  ext b
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨ConjAct.toConjAct k, k, hk, rfl⟩, ConjAct.toConjAct_smul k a⟩
  · rintro ⟨⟨g, k, hk, rfl⟩, rfl⟩
    exact ⟨k, hk, (ConjAct.toConjAct_smul k a).symm⟩

theorem ncard_conjOrbit_dvd [Finite X] (K : Subgroup X) (a : X) :
    (conjOrbit K a).ncard ∣ Nat.card K := by
  rw [conjOrbit_eq, ← MulAction.index_stabilizer]
  refine (Subgroup.index_dvd_card _).trans ?_
  rw [Subgroup.card_map_of_injective (ConjAct.toConjAct : X ≃* ConjAct X).injective]

theorem exists_ncard_conjOrbit_eq_pow [Finite X] {K : Subgroup X} (hK : IsPGroup 3 K) (a : X) :
    ∃ n, (conjOrbit K a).ncard = 3 ^ n := by
  rw [conjOrbit_eq]
  obtain ⟨n, hn⟩ := (hK.map (ConjAct.toConjAct : X ≃* ConjAct X).toMonoidHom).card_orbit a
  exact ⟨n, by rwa [Nat.card_coe_set_eq] at hn⟩

end Orbit

section Order

theorem mem_normalizer_of_mul_self {g : X} {P : Subgroup X} (hg : g * g = 1)
    (hgP : ∀ r ∈ P, g * r * g⁻¹ ∈ P) : g ∈ Subgroup.normalizer (P : Set X) := by
  have hinv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  refine Subgroup.mem_normalizer_iff.2 fun r => ⟨hgP r, fun h => ?_⟩
  have h' := hgP _ h
  rwa [hinv, show g * (g * r * g) * g = g * g * r * (g * g) by group, hg, one_mul,
    mul_one] at h'

theorem Pair.exists_card_sup_eq (hP : Pair X E) {d x : X} (hd : d ∈ E) (hx : x ∈ E)
    (hdx : d * x = x * d) (P : Subgroup X)
    (hdP : ∀ r ∈ P, d * r * d⁻¹ ∈ P) (hxP : ∀ r ∈ P, x * r * x⁻¹ ∈ P) :
    ∃ m ≤ 4, Nat.card ((Subgroup.zpowers d ⊔ Subgroup.zpowers x) ⊔ P : Subgroup X) =
      Nat.card P * m := by
  have := Pair.finite hP
  set H := Subgroup.zpowers d ⊔ Subgroup.zpowers x
  have hdN := mem_normalizer_of_mul_self (Pair.mul_self hP hd) hdP
  have hxN := mem_normalizer_of_mul_self (Pair.mul_self hP hx) hxP
  have hHN : H ≤ Subgroup.normalizer (P : Set X) :=
    sup_le ((Subgroup.zpowers_le).2 hdN) ((Subgroup.zpowers_le).2 hxN)
  have hdx' : Subgroup.zpowers d ≤ Subgroup.normalizer (Subgroup.zpowers x : Set X) := by
    refine (Subgroup.zpowers_le).2 (mem_normalizer_of_mul_self (Pair.mul_self hP hd) ?_)
    rintro _ ⟨n, rfl⟩
    exact ⟨n, by rw [← conj_zpow, hdx, mul_inv_cancel_right]⟩
  have hH4 : Nat.card H ≤ 4 := by
    rw [← SetLike.coe_sort_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hdx']
    refine (Set.natCard_mul_le).trans ?_
    rw [SetLike.coe_sort_coe, SetLike.coe_sort_coe, Nat.card_zpowers, Nat.card_zpowers,
      Pair.orderOf_eq_two hP hd, Pair.orderOf_eq_two hP hx]
  refine ⟨Nat.card ((H : Set X).image ((↑) : X → X ⧸ P)), ?_, ?_⟩
  · exact (Nat.card_image_le (Set.toFinite _)).trans (by rwa [SetLike.coe_sort_coe])
  · rw [← SetLike.coe_sort_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hHN,
      Subgroup.card_mul_eq_card_subgroup_mul_card_quotient]

end Order

namespace Setting

variable (hS : Setting X E)
include hS

theorem fib_eq_of_pairwise {d x : X} (hd : d ∈ E) (hx : x ∈ LocalClass E d)
    (hpw : ∀ y ∈ LocalClass E d, ∀ z ∈ LocalClass E d, y ≠ z → y * z ≠ z * y) :
    fib E d x = LocalClass E d := by
  have hP := hS.pair
  refine Set.Subset.antisymm (fun y hy => Pair.mem_localClass_of_mem_fib hP hx hy)
    fun y hy => ?_
  by_cases hyx : y = x
  · rw [hyx]
    exact Pair.mem_fib_self hP hx.1
  have hxy : x * y ≠ y * x := hpw x hx y hy (Ne.symm hyx)
  by_contra hny
  obtain ⟨w, hw⟩ := hS.exists_isWit hx.1 hy.1 hxy
  have hdmu : d ∈ muSet E x y := ⟨mem_localClass_symm hd hx, mem_localClass_symm hd hy⟩
  have hnd : ¬ IsWit E d x y := fun h => hny ⟨hy.1, h.2⟩
  have hwd : w * d = d * w := Pair.commute_of_isWit hP hw hdmu hnd
  have hwD : w ∈ LocalClass E d := ⟨hw.1.1.1, fun h => hnd (h ▸ hw), hwd⟩
  exact hpw w hwD x hx hw.1.1.2.1 hw.1.1.2.2

theorem ncard_localClass_le_three_of_pairwise {d : X} (hd : d ∈ E)
    (hpw : ∀ y ∈ LocalClass E d, ∀ z ∈ LocalClass E d, y ≠ z → y * z ≠ z * y) :
    (LocalClass E d).ncard ≤ 3 := by
  have hP := hS.pair
  have := Pair.finite hP
  rcases (LocalClass E d).eq_empty_or_nonempty with h0 | ⟨x, hx⟩
  · rw [h0, Set.ncard_empty]
    omega
  have hfib := hS.fib_eq_of_pairwise hd hx hpw
  have hDorb : LocalClass E d = conjOrbit (core E d) x := by
    rw [← hfib]
    ext y
    constructor
    · intro hy
      obtain ⟨r, hr, rfl⟩ := Pair.exists_conj_of_mem_fib hP hx.1 hy
      exact ⟨r, hr, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      exact Pair.conj_mem_fib hP hx hr
  obtain ⟨n, hn⟩ := exists_ncard_conjOrbit_eq_pow (isPGroup_core E d) x
  rw [← hDorb] at hn
  obtain ⟨c, hc, hcd⟩ : ∃ c ∈ E, c * d ≠ d * c := by
    by_contra! hall
    have hdZ : d ∈ Subgroup.center X := (Pair.mem_center_iff hP).2 hall
    rw [hS.hyp.center, Subgroup.mem_bot] at hdZ
    exact Pair.ne_one hP hd hdZ
  have hdc : d * c ≠ c * d := fun h => hcd h.symm
  have hcount := Pair.card_A hP hd (k := (LocalClass E d).ncard) (l := 0)
    (m := (muSet E d c).ncard) (Nat.card_coe_set_eq _)
    (fun f hf => by rw [Nat.card_coe_set_eq, Pair.ncard_localClass_eq hP hf.1 hd])
    (fun f hf => by
      rw [Nat.card_coe_set_eq, Set.ncard_eq_zero]
      ext y
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hyd hyf
      exact hpw y hyd f hf hyf.2.1 hyf.2.2)
    (fun c' hc' hc'd => by
      rw [Nat.card_coe_set_eq]
      exact hS.ncard_muSet_eq hd hc hdc hd hc' fun h => hc'd h.symm)
  rcases (muSet E d c).eq_empty_or_nonempty with hμ0 | ⟨f, hf⟩
  · rw [hμ0, Set.ncard_empty, mul_zero, hn] at hcount
    have h := (Nat.mul_eq_zero.1 hcount.symm)
    rcases h with h | h
    · omega
    · rw [hn]
      omega
  have hfD : f ∈ LocalClass E d := hf.1
  have hfib' := hS.fib_eq_of_pairwise hd hfD hpw
  have hμorb : muSet E d c = conjOrbit (core E d ⊓ Subgroup.centralizer {c}) f := by
    ext g
    constructor
    · rintro ⟨hgd, hgc⟩
      by_cases hgf : g = f
      · exact ⟨1, one_mem _, by rw [hgf]; group⟩
      have hfg : f * g ∈ core E d := (hfib' ▸ hgd : g ∈ fib E d f).2
      have hfgc : f * g ∈ Subgroup.centralizer ({c} : Set X) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        rw [mul_assoc, hgc.2.2, ← mul_assoc, hf.2.2.2, mul_assoc]
      have hnc : g * f ≠ f * g := fun h => hpw f hfD g hgd (Ne.symm hgf) h.symm
      exact ⟨f * g, ⟨hfg, hfgc⟩, Pair.mul_conj_eq hP hfD.1 hgd.1 hnc⟩
    · rintro ⟨r, ⟨hr, hrc⟩, rfl⟩
      have hrc' : c * r = r * c := (Subgroup.mem_centralizer_singleton_iff.1 hrc).symm
      have hmem : r * f * r⁻¹ ∈ LocalClass E d :=
        Pair.mem_localClass_of_mem_fib hP hfD (Pair.conj_mem_fib hP hfD hr)
      refine ⟨hmem, Pair.conj_mem hP hfD.1 r, fun h => hcd ?_, ?_⟩
      · rw [← h]
        exact hmem.2.2
      · have hrc'' : r⁻¹ * c = c * r⁻¹ := by
          rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hrc', mul_assoc, mul_inv_cancel, mul_one]
        calc r * f * r⁻¹ * c = r * f * (c * r⁻¹) := by rw [mul_assoc, hrc'']
          _ = r * (f * c) * r⁻¹ := by group
          _ = r * (c * f) * r⁻¹ := by rw [hf.2.2.2]
          _ = c * (r * f * r⁻¹) := by rw [← mul_assoc, ← hrc', mul_assoc, mul_assoc]; group
  obtain ⟨b, hb⟩ := exists_ncard_conjOrbit_eq_pow
    ((isPGroup_core E d).to_inf_left (K := Subgroup.centralizer {c})) f
  rw [← hμorb] at hb
  set S := (Subgroup.zpowers d ⊔ Subgroup.zpowers x) ⊔ core E d
  have hSd : ∀ g ∈ S, g * d = d * g := by
    have hle : S ≤ Subgroup.centralizer ({d} : Set X) := by
      refine sup_le (sup_le ?_ ?_) (core_le_centralizer E d)
      · exact (Subgroup.zpowers_le).2 (Subgroup.mem_centralizer_singleton_iff.2 rfl)
      · exact (Subgroup.zpowers_le).2 (Subgroup.mem_centralizer_singleton_iff.2 hx.2.2)
    exact fun g hg => (Subgroup.mem_centralizer_singleton_iff.1 (hle hg))
  have hKS : Subgroup.closure (insert d (LocalClass E d)) ≤ S := by
    rw [Subgroup.closure_le]
    rintro y (rfl | hy)
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
    · have hxy : x * y ∈ core E d := (hfib ▸ hy : y ∈ fib E d x).2
      have hy' : y = x * (x * y) := by rw [← mul_assoc, Pair.mul_self hP hx.1, one_mul]
      rw [hy']
      exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))
        (Subgroup.mem_sup_right hxy)
  have hAorb : {c' | c' ∈ E ∧ c' * d ≠ d * c'} = conjOrbit S c := by
    ext c'
    constructor
    · rintro ⟨hc', hc'd⟩
      obtain ⟨g, hg, rfl⟩ := Pair.exists_conj_far hP hS.hyp.center hS.hyp.simple hS.nab hd hc
        hcd c' hc' hc'd
      exact ⟨g, hKS hg, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact Pair.conj_mem_farClass hP (hSd g hg) ⟨hc, hcd⟩
  obtain ⟨m, hm4, hSm⟩ := Pair.exists_card_sup_eq hP hd hx.1 hx.2.2.symm (core E d)
    (fun r hr => Pair.conj_mem_core_of_commute hP rfl hr)
    (fun r hr => conj_mem_core (mem_localGroup hx) hr)
  have hAdvd : {c' | c' ∈ E ∧ c' * d ≠ d * c'}.ncard ∣ Nat.card (core E d) * m := by
    rw [hAorb, ← hSm]
    exact ncard_conjOrbit_dvd S c
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 3)).1 (isPGroup_core E d)
  have hm0 : 0 < m := by
    have := Nat.card_pos (α := S)
    rw [hSm] at this
    exact Nat.pos_of_mul_pos_left this
  rw [Nat.card_coe_set_eq, hn, hb, Nat.sub_zero] at hcount
  rw [hn]
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · interval_cases n <;> norm_num
  exfalso
  have hcop : Nat.Coprime (3 ^ n - 1) 3 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro h3
    have h1 : 3 ∣ 3 ^ n := dvd_pow_self 3 (by omega)
    have h2 : 1 ≤ 3 ^ n := Nat.one_le_pow _ _ (by norm_num)
    have h4 := Nat.dvd_sub h1 h3
    rw [show 3 ^ n - (3 ^ n - 1) = 1 by omega] at h4
    omega
  have hdvd1 : 3 ^ n - 1 ∣ Nat.card (core E d) * m * 3 ^ b := by
    exact (Dvd.intro_left _ hcount.symm).trans (mul_dvd_mul_right hAdvd _)
  rw [ha, mul_comm (3 ^ a) m, mul_assoc] at hdvd1
  have hdvd2 : 3 ^ n - 1 ∣ m :=
    (Nat.Coprime.pow_right (a + b) hcop |>.dvd_of_dvd_mul_right (by rwa [pow_add]))
  have hle := Nat.le_of_dvd hm0 hdvd2
  have h9 : 9 ≤ 3 ^ n := by
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  omega

end Setting

end O3

end CFSG.Fischer.Classification
