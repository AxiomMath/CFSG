module

public import CFSG.GH74.GLS.IVK.L2.Involutions
public import CFSG.GH74.GLS.IVK.L2.Transport

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup Matrix CFSG CFSG.GorensteinWalter CFSG.ABGLocalTools CFSG.ABGDGroups

section L114

variable {F : Type} [Field F] [Finite F]

theorem exists_eps_mod_four_of_odd {q : ℕ} (hq : Odd q) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ (q : ℤ) ≡ ε [ZMOD 4] := by
  obtain ⟨k, hk⟩ := hq
  by_cases h : k % 2 = 0
  · refine ⟨1, Or.inl rfl, ?_⟩
    unfold Int.ModEq
    omega
  · refine ⟨-1, Or.inr rfl, ?_⟩
    unfold Int.ModEq
    omega

theorem ne_two_of_card_eq_prime_pow (hF : L2Field F) {p n : ℕ} (hq : Nat.card F = p ^ n) : p ≠ 2 := by
  rintro rfl
  have h := hF.1
  rw [hq] at h
  have hn : n ≠ 0 := by
    rintro rfl
    have := hF.2
    rw [hq] at this
    simp at this
  exact (Nat.not_even_iff_odd.2 h) (by simpa [Nat.even_pow] using hn)

theorem not_dvd_card_centralizer_involution (hF : L2Field F) {p n : ℕ} (hp : p.Prime)
    (hq : Nat.card F = p ^ n) {A : PGL2 F} (hA : orderOf A = 2) :
    ¬ p ∣ Nat.card ↥(centralizer ({A} : Set (PGL2 F))) := by
  have hOPP := isOddPrimePower_of_L2Field hF
  obtain ⟨ε, hε1, hε⟩ := exists_eps_mod_four_of_odd hF.1
  have key := pgl2_involution_centralizer_dihedral hOPP hF.2 hε1 hε hA
  have hn : n ≠ 0 := by
    rintro rfl
    have := hF.2
    rw [hq] at this
    simp at this
  have hpq : p ∣ Nat.card F := by rw [hq]; exact dvd_pow_self p hn
  have hp2 : p ≠ 2 := ne_two_of_card_eq_prime_pow hF hq
  intro hdvd
  have hm : ∃ m : ℕ, ((m : ℤ) = Nat.card F - ε ∨ (m : ℤ) = Nat.card F + ε) ∧
      Nat.card ↥(centralizer ({A} : Set (PGL2 F))) = 2 * m := by
    by_cases hAK : A ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range
    · obtain ⟨m, hm, ⟨e⟩⟩ := key.1 hAK
      have hm0 : m ≠ 0 := by
        rintro rfl
        have := hF.2
        omega
      have : NeZero m := ⟨hm0⟩
      refine ⟨m, Or.inl hm, ?_⟩
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    · obtain ⟨m, hm, ⟨e⟩⟩ := key.2 hAK
      have hm0 : m ≠ 0 := by
        rintro rfl
        have := hF.2
        omega
      have : NeZero m := ⟨hm0⟩
      refine ⟨m, Or.inr hm, ?_⟩
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  obtain ⟨m, hm, hcard⟩ := hm
  rw [hcard] at hdvd
  have hpm : p ∣ m := by
    rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h) hp2
    · exact h
  have hpm' : (p : ℤ) ∣ (m : ℤ) := Int.natCast_dvd_natCast.2 hpm
  have hpq' : (p : ℤ) ∣ (Nat.card F : ℤ) := Int.natCast_dvd_natCast.2 hpq
  have hpε : (p : ℤ) ∣ ε := by
    rcases hm with h | h
    · have := dvd_sub hpq' hpm'
      rw [h] at this
      simpa using this
    · have := dvd_sub hpm' hpq'
      rw [h] at this
      simpa using this
  have h1 : (p : ℤ) ∣ 1 := by
    rcases hε1 with rfl | rfl
    · exact hpε
    · simpa using hpε
  have := Int.eq_one_of_dvd_one (Int.natCast_nonneg p) h1
  have h1 : p = 1 := by exact_mod_cast this
  exact hp.one_lt.ne' h1

theorem isCyclic_of_isPGroup_pgl2
    (hF : L2Field F) {p n : ℕ} (hp : p.Prime)
    (hq : Nat.card F = p ^ n) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrp : r ≠ p)
    (R : Subgroup (PGL2 F)) (hR : IsPGroup r R) : IsCyclic R := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact r.Prime := ⟨hr⟩
  have hOPP := isOddPrimePower_of_L2Field hF
  have hp2 : p ≠ 2 := ne_two_of_card_eq_prime_pow hF hq
  set toPGL := Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F) with htoPGL
  have hinj : Function.Injective toPGL := Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  have hidx : toPGL.range.index = 2 := pgl2_psl2Range_index_eq_two F hOPP
  have : toPGL.range.Normal := Subgroup.normal_of_index_eq_two hidx
  have hRJ : R ≤ toPGL.range := by
    intro g hg
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hR) ⟨g, hg⟩
    have hodd : Odd (orderOf g) := by
      rw [show orderOf g = orderOf (⟨g, hg⟩ : R) from (Subgroup.orderOf_mk g hg).symm, hk]
      exact (hr.odd_of_ne_two hr2).pow
    obtain ⟨m, hm⟩ := hodd
    have hg2 : g ^ 2 ∈ toPGL.range := by
      have := Subgroup.pow_index_mem toPGL.range g
      rwa [hidx] at this
    have : g = (g ^ 2) ^ (m + 1) := by
      rw [← pow_mul]
      have h1 : g ^ (orderOf g) = 1 := pow_orderOf_eq_one g
      rw [hm] at h1
      calc g = g ^ (2 * m + 1) * g := by rw [h1, one_mul]
        _ = g ^ (2 * (m + 1)) := by rw [← pow_succ]; congr 1
    rw [this]
    exact Subgroup.pow_mem _ hg2 _
  set K₀ : Subgroup (PSL2 F) := R.comap toPGL with hK₀def
  have hK₀r : IsPGroup r K₀ := by
    rw [IsPGroup.iff_orderOf]
    rintro ⟨x, hx⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hR) ⟨toPGL x, hx⟩
    refine ⟨k, ?_⟩
    rw [Subgroup.orderOf_mk, ← orderOf_injective toPGL hinj x, ← Subgroup.orderOf_mk (toPGL x) hx, hk]
  have hK₀odd : Odd (Nat.card K₀) := by
    obtain ⟨k, hk⟩ := hK₀r.exists_card_eq
    rw [hk]
    exact (hr.odd_of_ne_two hr2).pow
  have hmap : K₀.map toPGL = R := by
    rw [hK₀def, Subgroup.map_comap_eq]
    exact inf_eq_right.2 hRJ
  rcases psl2_odd_isCyclic_or_exists_pSubgroup hq hp2 K₀ hK₀odd with hc | ⟨N, hNK, hN1, hNp, -⟩
  · have : IsCyclic ↥(K₀.map toPGL) :=
      isCyclic_of_surjective (toPGL.subgroupMap K₀) (toPGL.subgroupMap_surjective K₀)
    rw [hmap] at this
    exact this
  · exfalso
    obtain ⟨k, hk⟩ := hNp.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact hN1 (Subgroup.card_eq_one.1 hk)
    have hdvd : p ∣ Nat.card N := by rw [hk]; exact dvd_pow_self p hk0
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := N) p hdvd
    have hxK : (x : PSL2 F) ∈ K₀ := hNK x.2
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.1 hK₀r) ⟨(x : PSL2 F), hxK⟩
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hx] at hj
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hj
      exact hp.one_lt.ne' hj
    have : r ∣ p := by rw [hj]; exact dvd_pow_self r hj0
    exact hrp ((Nat.prime_dvd_prime_iff_eq hr hp).1 this)

end L114

section L114Main

theorem ivk_1_14 :
    ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (H : Type) [Group H] [Finite H]
      (_ : H ≃* GL (Fin 2) F) (p n : ℕ), p.Prime → Nat.card F = p ^ n →
        (∀ U : Subgroup H, Nat.card ↥U = 4 → ¬ U ≤ center H →
          ¬ p ∣ Nat.card ↥(centralizer ((U.map (QuotientGroup.mk' (center H)) :
            Subgroup (H ⧸ center H)) : Set (H ⧸ center H)))) ∧
        ∀ r : ℕ, r.Prime → Odd r → ∀ X : Subgroup (H ⧸ center H),
          ¬ Nonempty (↥X ≃* DihedralGroup r × DihedralGroup r) := by
  intro F _ _ hF H _ _ e p n hp hq
  classical
  have : Fact p.Prime := ⟨hp⟩
  let Φ : H ⧸ center H ≃* PGL2 F :=
    QuotientGroup.congr (center H) (center (GL (Fin 2) F)) e (Subgroup.map_center_eq e)
  have hnocomm : ∀ u v : H ⧸ center H, orderOf u = 2 → orderOf v = p → u * v = v * u → False := by
    intro u v hu hv hc
    have hA : orderOf (Φ u) = 2 := by rw [MulEquiv.orderOf_eq]; exact hu
    have hmem : Φ v ∈ centralizer ({Φ u} : Set (PGL2 F)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      rw [← map_mul, ← map_mul, hc]
    apply not_dvd_card_centralizer_involution hF hp hq hA
    have := Subgroup.orderOf_dvd_natCard (centralizer ({Φ u} : Set (PGL2 F))) hmem
    rwa [MulEquiv.orderOf_eq, hv] at this
  refine ⟨?_, ?_⟩
  · intro U hU4 hUc hdvd
    obtain ⟨x, hxU, hxc⟩ : ∃ x ∈ U, x ∉ center H := by
      by_contra hcon
      push Not at hcon
      exact hUc hcon
    set Ubar : Subgroup (H ⧸ center H) := U.map (QuotientGroup.mk' (center H)) with hUbar
    have hxbar : ((x : H ⧸ center H)) ∈ Ubar := ⟨x, hxU, rfl⟩
    have hx1 : (x : H ⧸ center H) ≠ 1 := by
      intro h
      exact hxc ((QuotientGroup.eq_one_iff x).1 h)
    have hord4 : orderOf (x : H ⧸ center H) ∣ 2 ^ 2 := by
      have h1 : orderOf (x : H ⧸ center H) ∣ orderOf x :=
        orderOf_map_dvd (QuotientGroup.mk' (center H)) x
      have h2 : orderOf x ∣ Nat.card U := Subgroup.orderOf_dvd_natCard U hxU
      rw [hU4] at h2
      exact h1.trans (by simpa using h2)
    obtain ⟨m, hm2, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord4
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hm
      exact hx1 hm
    have hev : 2 ∣ orderOf (x : H ⧸ center H) := by
      rw [hm]
      exact dvd_pow_self 2 hm0
    have hord0 : orderOf (x : H ⧸ center H) ≠ 0 := by
      rw [hm]
      exact pow_ne_zero _ (by norm_num)
    have hu : orderOf ((x : H ⧸ center H) ^ (orderOf (x : H ⧸ center H) / 2)) = 2 :=
      orderOf_pow_orderOf_div hord0 hev
    have huU : (x : H ⧸ center H) ^ (orderOf (x : H ⧸ center H) / 2) ∈ Ubar :=
      Subgroup.pow_mem _ hxbar _
    obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := ↥(centralizer (Ubar : Set (H ⧸ center H)))) p hdvd
    have hvc : (v : H ⧸ center H) ∈ centralizer (Ubar : Set (H ⧸ center H)) := v.2
    rw [Subgroup.mem_centralizer_iff] at hvc
    exact hnocomm _ _ hu (by rw [Subgroup.orderOf_coe]; exact hv) (hvc _ huU)
  · intro r hr hrodd X hX
    obtain ⟨θ⟩ := hX
    have : Fact r.Prime := ⟨hr⟩
    have : NeZero r := ⟨hr.ne_zero⟩
    have hr2 : r ≠ 2 := by
      rintro rfl
      exact absurd hrodd (by decide)
    by_cases hrp : r = p
    · subst hrp
      have h1 : orderOf (θ.symm (DihedralGroup.sr 0, 1)) = 2 := by
        rw [MulEquiv.orderOf_eq, Prod.orderOf]
        simp [DihedralGroup.orderOf_sr]
      have h2 : orderOf (θ.symm (1, DihedralGroup.r 1)) = r := by
        rw [MulEquiv.orderOf_eq, Prod.orderOf]
        simp [DihedralGroup.orderOf_r_one]
      refine hnocomm ((θ.symm (DihedralGroup.sr 0, 1) : X) : H ⧸ center H)
        ((θ.symm (1, DihedralGroup.r 1) : X) : H ⧸ center H) ?_ ?_ ?_
      · rw [Subgroup.orderOf_coe]; exact h1
      · rw [Subgroup.orderOf_coe]; exact h2
      · rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul]
        simp
    · exfalso
      obtain ⟨P⟩ : Nonempty (Sylow r X) := inferInstance
      let f : X →* PGL2 F := Φ.toMonoidHom.comp X.subtype
      have hf : Function.Injective f := Φ.injective.comp X.subtype_injective
      have hPcyc : IsCyclic (P : Subgroup X) := by
        have hP' : IsPGroup r ((P : Subgroup X).map f) := P.isPGroup'.map f
        have hc := isCyclic_of_isPGroup_pgl2 hF hp hq hr hr2 hrp _ hP'
        exact ((Subgroup.equivMapOfInjective (P : Subgroup X) f hf).isCyclic).2 hc
      obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (P : Subgroup X))
      have hXcard : Nat.card X = 2 * r * (2 * r) := by
        rw [Nat.card_congr θ.toEquiv, Nat.card_prod, DihedralGroup.nat_card]
      have hr2dvd : r ^ 2 ∣ Nat.card (P : Subgroup X) := by
        rw [Sylow.card_eq_multiplicity]
        have hne : Nat.card X ≠ 0 := Nat.card_pos.ne'
        have h4 : r ^ 2 ∣ Nat.card X := ⟨4, by rw [hXcard]; ring⟩
        have h2 := (hr.pow_dvd_iff_le_factorization hne).1 h4
        exact pow_dvd_pow r h2
      have hdvd2r : Nat.card (P : Subgroup X) ∣ 2 * r := by
        rw [← hg]
        have h1 : orderOf ((g : X)) = orderOf g := Subgroup.orderOf_coe g
        rw [← h1, ← MulEquiv.orderOf_eq θ (g : X), Prod.orderOf]
        refine Nat.lcm_dvd ?_ ?_
        · exact (_root_.orderOf_dvd_natCard _).trans (by rw [DihedralGroup.nat_card])
        · exact (_root_.orderOf_dvd_natCard _).trans (by rw [DihedralGroup.nat_card])
      have h4 : r ^ 2 ∣ 2 * r := hr2dvd.trans hdvd2r
      have hr_dvd : r ∣ 2 := by
        have : r * r ∣ r * 2 := by simpa [pow_two, mul_comm] using h4
        exact Nat.dvd_of_mul_dvd_mul_left hr.pos this
      have h5 := Nat.le_of_dvd (by norm_num) hr_dvd
      have h6 := hr.two_le
      omega

end L114Main

end CFSG.GH74.GLS.IVK
