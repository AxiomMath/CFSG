module

public import CFSG.ClassicalInvolution.AschTight.Sec19Targets2
import CFSG.ClassicalInvolution.SmallCases.NobqTransfer

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight


section Helpers

variable {G : Type} [Group G]

theorem tl3_conjSub_eq_of_mem_normalizer {K : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (K : Set G)) : conjSub n K = K := by
  ext x
  rw [mem_conjSub_iff]
  have := Subgroup.mem_normalizer_iff.mp (inv_mem hn) x
  simpa using this.symm

theorem tl3_natCard_conjSub (n : G) (K : Subgroup G) : Nat.card (conjSub n K) = Nat.card K :=
  Subgroup.card_map_of_injective (MulAut.conj n).injective

theorem tl3_not_isMulCommutative_conjSub {P : Subgroup G}
    (h : ∃ x ∈ P, ∃ y ∈ P, x * y ≠ y * x) (g : G) : ¬ IsMulCommutative ↥(conjSub g P) := by
  intro hc
  obtain ⟨x, hx, y, hy, hxy⟩ := h
  have h1 := hc.is_comm.comm (⟨g * x * g⁻¹, conj_mem_conjSub hx⟩ : ↥(conjSub g P))
    ⟨g * y * g⁻¹, conj_mem_conjSub hy⟩
  have h2 := congrArg Subtype.val h1
  simp only [Subgroup.coe_mul] at h2
  apply hxy
  have h3 : g * (x * y) * g⁻¹ = g * (y * x) * g⁻¹ := by
    calc g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
      _ = g * y * g⁻¹ * (g * x * g⁻¹) := h2
      _ = g * (y * x) * g⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel h3)

theorem tl3_closure_twoElements_conjSub {M : Subgroup G}
    (hgen : Subgroup.closure {x : G | x ∈ M ∧ IsPGroup 2 (Subgroup.zpowers x)} = M) (g : G) :
    Subgroup.closure {x : G | x ∈ conjSub g M ∧ IsPGroup 2 (Subgroup.zpowers x)} =
      conjSub g M := by
  refine le_antisymm ((Subgroup.closure_le _).mpr fun x hx => hx.1) ?_
  conv_lhs => rw [← hgen]
  rw [conjSub, MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨x, ⟨hxM, hx2⟩, rfl⟩
  refine ⟨⟨x, hxM, rfl⟩, ?_⟩
  rw [← MonoidHom.map_zpowers]
  exact hx2.map _

end Helpers


section Main

variable {G : Type} [Group G] [Finite G]

theorem hypOmegaGen_of_datum {R : Subgroup G} (S : Sylow 2 R)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2)))) {t : G}
    (ht : t ∈ (S : Subgroup R).map R.subtype) (hto : orderOf t = 2)
    (hRC : R ≤ Subgroup.centralizer ({t} : Set G))
    (hRn : (R.subgroupOf (Subgroup.centralizer ({t} : Set G))).Normal) :
    HypOmegaGen (CoreAssembly.conjClass
      (Subgroup.closure {x : G | x ∈ R ∧ IsPGroup 2 (Subgroup.zpowers x)})) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := Subgroup.centralizer ({t} : Set G) with hC
  set K0 : Subgroup G :=
    Subgroup.closure {x : G | x ∈ R ∧ IsPGroup 2 (Subgroup.zpowers x)} with hK0
  have hCR : C ≤ Subgroup.normalizer (R : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRC).mp hRn
  have hK0R : K0 ≤ R := (Subgroup.closure_le _).mpr fun x hx => hx.1
  have htR : t ∈ R := Subgroup.map_subtype_le _ ht
  have ht2 : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hto]; norm_num)
  have htK0 : t ∈ K0 := Subgroup.subset_closure ⟨htR, ht2⟩
  have hgen0 : Subgroup.closure {x : G | x ∈ K0 ∧ IsPGroup 2 (Subgroup.zpowers x)} = K0 := by
    refine le_antisymm ((Subgroup.closure_le _).mpr fun x hx => hx.1) ?_
    refine (Subgroup.closure_le _).mpr fun x hx => Subgroup.subset_closure ⟨?_, hx.2⟩
    exact Subgroup.subset_closure hx
  have hconj : ∀ c ∈ C, ∀ x ∈ K0, c * x * c⁻¹ ∈ K0 := by
    intro c hc
    have hle : K0 ≤ K0.comap (MulAut.conj c).toMonoidHom := by
      refine (Subgroup.closure_le _).mpr fun y hy => ?_
      refine Subgroup.subset_closure ⟨?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (hCR hc) y).mp hy.1
      · rw [← MonoidHom.map_zpowers]
        exact hy.2.map _
    exact fun x hx => hle hx
  have hCK0 : C ≤ Subgroup.normalizer (K0 : Set G) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hconj c hc x, fun hx => ?_⟩
    have := hconj c⁻¹ (C.inv_mem hc) _ hx
    simpa [mul_assoc] using this
  have huniq : IsUniqueInvolution K0 t := by
    refine ⟨htK0, ?_, ?_, ?_⟩
    · intro h
      rw [h, orderOf_one] at hto
      norm_num at hto
    · rw [← pow_two]
      exact hto ▸ pow_orderOf_eq_one t
    · intro y hy hyy
      by_cases hy1 : y = 1
      · exact Or.inl hy1
      · right
        have hord : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two]; exact hyy) hy1
        exact eq_of_orderOf_eq_two_of_quaternion_sylow htR hto hRC S hS (hK0R hy) hord
  set S0 : Subgroup G := (S : Subgroup R).map R.subtype with hS0def
  have hS0p : IsPGroup 2 S0 := S.isPGroup'.map R.subtype
  have hS0K0 : S0 ≤ K0 := by
    intro s hs
    refine Subgroup.subset_closure ⟨Subgroup.map_subtype_le _ hs, ?_⟩
    exact hS0p.to_le (Subgroup.zpowers_le.mpr hs)
  have hSyl : IsSylow2In S0 K0 :=
    ⟨hS0K0, hS0p, fun V hVK hV2 hle => (isSylow2Of_map_subtype S).2.2 V (hVK.trans hK0R) hV2 hle⟩
  have hnc : ∃ x ∈ S0, ∃ y ∈ S0, x * y ≠ y * x := by
    obtain ⟨r, hr, ⟨e⟩⟩ := hS
    have hn : NeZero (2 ^ (r - 2)) := ⟨by positivity⟩
    have h2 : 2 ≤ 2 ^ (r - 2) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (r - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    let e' : S0 ≃* QuaternionGroup (2 ^ (r - 2)) :=
      (Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype R.subtype_injective).symm.trans e
    obtain ⟨a, b, hab⟩ := Nobq.exists_not_commute_of_mulEquiv_quaternionGroup h2 e'
    exact ⟨a, a.2, b, b.2, fun h => hab (Subtype.ext h)⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro n _ ⟨g, rfl⟩
    exact ⟨n * g, conjSub_mul n g K0⟩
  · rintro _ ⟨g, rfl⟩
    exact ⟨⟨_, huniq.conj g⟩, _, hSyl.conj g, tl3_not_isMulCommutative_conjSub hnc g⟩
  · rintro _ ⟨g, rfl⟩
    exact Or.inl (tl3_closure_twoElements_conjSub hgen0 g)
  · rintro _ ⟨g, rfl⟩ _ ⟨h, rfl⟩ P Q hP hQ
    have h1 := hP.conj g⁻¹
    have h2 := hQ.conj h⁻¹
    rw [conjSub_inv_conjSub] at h1 h2
    rw [← tl3_natCard_conjSub g⁻¹ P, ← tl3_natCard_conjSub h⁻¹ Q]
    exact h1.natCard_eq h2
  · rintro _ ⟨g, rfl⟩ _ ⟨h, rfl⟩ hne
    dsimp only at hne ⊢
    by_cases h2 : 2 ∣ Nat.card ↥(conjSub g K0 ⊓ conjSub h K0)
    · exfalso
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(conjSub g K0 ⊓ conjSub h K0)) 2 h2
      have hyo : orderOf (y : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hy
      have hyy : (y : G) * y = 1 := by rw [← pow_two]; exact hyo ▸ pow_orderOf_eq_one _
      have hy1 : (y : G) ≠ 1 := fun h' => by rw [h', orderOf_one] at hyo; norm_num at hyo
      have e1 : (y : G) = g * t * g⁻¹ := ((huniq.conj g).unique y y.2.1 hyy).resolve_left hy1
      have e2 : (y : G) = h * t * h⁻¹ := ((huniq.conj h).unique y y.2.2 hyy).resolve_left hy1
      have egh : g * t * g⁻¹ = h * t * h⁻¹ := e1.symm.trans e2
      have hcomm : t * (h⁻¹ * g) = (h⁻¹ * g) * t := by
        calc t * (h⁻¹ * g) = h⁻¹ * (h * t * h⁻¹) * g := by group
          _ = h⁻¹ * (g * t * g⁻¹) * g := by rw [egh]
          _ = (h⁻¹ * g) * t := by group
      have hmem : h⁻¹ * g ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm
      have hfix := tl3_conjSub_eq_of_mem_normalizer (hCK0 hmem)
      apply hne
      calc conjSub g K0 = conjSub (h * (h⁻¹ * g)) K0 := by rw [mul_inv_cancel_left]
        _ = conjSub h (conjSub (h⁻¹ * g) K0) := conjSub_mul _ _ _
        _ = conjSub h K0 := by rw [hfix]
    · have h0 : padicValNat 2 (Nat.card ↥(conjSub g K0 ⊓ conjSub h K0)) = 0 :=
        padicValNat.eq_zero_of_not_dvd h2
      exact ⟨by omega, fun h1 => by omega⟩
  · rintro _ ⟨g, rfl⟩ J _ _ z hz v _ _ _ hvz
    have e : z = g * t * g⁻¹ := hz.eq (huniq.conj g)
    subst e
    have hvC : g⁻¹ * v * g ∈ C := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc g⁻¹ * v * g * t = g⁻¹ * (v * (g * t * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * t * g⁻¹) * v) * g := by rw [hvz]
        _ = t * (g⁻¹ * v * g) := by group
    have hN := hCK0 hvC
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [mem_conjSub_iff, mem_conjSub_iff]
    have := Subgroup.mem_normalizer_iff.mp hN (g⁻¹ * x * g)
    have e1 : g⁻¹ * (v * x * v⁻¹) * g = g⁻¹ * v * g * (g⁻¹ * x * g) * (g⁻¹ * v * g)⁻¹ := by group
    rw [e1]
    exact this

end Main


end CFSG.ClassicalInvolution.Q3
