module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.FiLocal
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.OuterTrivial

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving CFSG.Blueprint
  CFSG.HardMathSupport.Solomon.LocalBalance

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def Fi23ThreeTranspositionFixed : Prop :=
  ∀ s : CFSG.Sporadic.Fi23.J, orderOf s = 3 → ∃ e ∈ CFSG.Sporadic.Fi23.D23, e * s = s * e

section Basic

open CFSG.Sporadic.Fi23


theorem D23_mul_self {x : J} (hx : x ∈ D23) : x * x = 1 := by
  have h := pow_orderOf_eq_one x
  rw [orderOf_of_isConj hx, sq] at h
  exact h

theorem D23_ne_one {x : J} (hx : x ∈ D23) : x ≠ 1 := by
  intro h
  have h2 := orderOf_of_isConj hx
  rw [h, orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem D23_conj {x : J} (hx : x ∈ D23) (g : J) : g * x * g⁻¹ ∈ D23 :=
  IsConj.trans hx (isConj_iff.2 ⟨g, rfl⟩)

theorem D23_cube {x y : J} (hx : x ∈ D23) (hy : y ∈ D23) (hne : x * y ≠ y * x) :
    x * y * (x * y) * (x * y) = 1 := by
  rcases orderOf_mul_of_isConj hx hy with h | h | h
  · exfalso
    apply hne
    have h1 : x * y = 1 := orderOf_eq_one_iff.1 h
    have h2 : y = x⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [h2, mul_inv_cancel, inv_mul_cancel]
  · exfalso
    apply hne
    have h3 := pow_orderOf_eq_one (x * y)
    rw [h, sq] at h3
    have h4 : x * y = (x * y)⁻¹ := eq_inv_of_mul_eq_one_left h3
    have hx2 : x⁻¹ = x := inv_eq_of_mul_eq_one_right (D23_mul_self hx)
    have hy2 : y⁻¹ = y := inv_eq_of_mul_eq_one_right (D23_mul_self hy)
    rw [h4, mul_inv_rev, hx2, hy2]
  · have h3 := pow_orderOf_eq_one (x * y)
    rw [h, pow_three'] at h3
    exact h3

theorem cube_of_orderOf_three {s : J} (hs : orderOf s = 3) : s * s * s = 1 := by
  have h := pow_orderOf_eq_one s
  rw [hs, pow_three'] at h
  exact h

theorem fi23_exists_fixed_ne {s : J} (hs : orderOf s = 3) {i : Fin 31671} (hi : s • i = i) :
    ∃ j : Fin 31671, j ≠ i ∧ s • j = j := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 (Subgroup.zpowers s) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs, pow_one])
  have hmod := hp.card_modEq_card_fixedPoints (Fin 31671)
  have hfix : ∀ j : Fin 31671, s • j = j →
      j ∈ MulAction.fixedPoints (Subgroup.zpowers s) (Fin 31671) := by
    intro j hj g
    have hg : (g : J) ∈ MulAction.stabilizer J j :=
      Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 hj) g.2
    exact MulAction.mem_stabilizer_iff.1 hg
  by_contra hne
  simp only [not_exists, not_and] at hne
  have hsub : MulAction.fixedPoints (Subgroup.zpowers s) (Fin 31671) = {i} := by
    ext j
    rw [Set.mem_singleton_iff]
    constructor
    · intro hj
      by_contra hji
      exact hne j hji (hj ⟨s, Subgroup.mem_zpowers s⟩)
    · rintro rfl
      exact hfix _ hi
  have h1 : Nat.card ({i} : Set (Fin 31671)) = 1 := Nat.card_unique
  rw [hsub, Nat.card_fin, h1] at hmod
  exact absurd hmod (by decide)

end Basic

section Local

open CFSG.Sporadic.Fi23


theorem fi23_local_d {s : J} (hs : orderOf s = 3) (hsd : s * d = d * s) (x : J)
    (hx : x ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({s} : Set J))) (hxd : x * d = d * x) :
    x = 1 ∨ x = d := by
  set N := GLAPPrimeCoreOf 3 (Subgroup.centralizer ({s} : Set J)) with hN
  set M : Subgroup Cd := (N ⊓ Cd).subgroupOf Cd with hM
  set s₀ : Cd := ⟨s, mem_Cd.2 hsd⟩ with hs₀
  have hs3 := cube_of_orderOf_three hs
  have hs₀3 : s₀ * s₀ * s₀ = 1 := Subtype.ext hs3
  have hdd : dCd * dCd = 1 := Subtype.ext d_sq
  have hds : dCd * s₀ = s₀ * dCd := Subtype.ext hsd.symm
  have hker : ∀ u : Cd, rho u = 1 → u = 1 ∨ u = dCd := fun u hu =>
    eq_one_or_eq_of_mem_zpowers hdd (by rw [← ker_rho]; exact hu)
  obtain ⟨t, ht⟩ := MonoidHom.mem_range.1
    (show rho s₀ ∈ pi22.range by rw [← range_rho]; exact MonoidHom.mem_range.2 ⟨s₀, rfl⟩)
  have ht3 : t * t * t = 1 := by
    apply pi22_injective
    rw [map_mul, map_mul, ht, ← map_mul, ← map_mul, hs₀3, map_one, map_one]
  have ht1 : t ≠ 1 := by
    intro h
    have h1 : rho s₀ = 1 := by rw [← ht, h, map_one]
    rcases hker s₀ h1 with h2 | h2
    · have h3 : s = 1 := congrArg Subtype.val h2
      rw [h3, orderOf_one] at hs
      exact absurd hs (by norm_num)
    · have h3 : s = d := congrArg Subtype.val h2
      rw [h3, orderOf_d] at hs
      exact absurd hs (by norm_num)
  have hto : orderOf t = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime (by rw [pow_three']; exact ht3) ht1
  set K : Subgroup CFSG.Sporadic.Fi22.J := (M.map rho).comap pi22 with hK
  have hKC : K ≤ Subgroup.centralizer ({t} : Set CFSG.Sporadic.Fi22.J) := by
    intro k hk
    obtain ⟨m, hm, hmk⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hk)
    have hmN : (m : J) ∈ N := (Subgroup.mem_subgroupOf.1 hm).1
    have hms : (m : J) * s = s * (m : J) :=
      (Subgroup.mem_centralizer_singleton_iff (g := s)).1 (GLAPPrimeCoreOf_le _ hmN)
    have hms₀ : m * s₀ = s₀ * m := Subtype.ext hms
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply pi22_injective
    rw [map_mul, map_mul, ← hmk, ht, ← map_mul, ← map_mul, hms₀]
  have hKn : ∀ y ∈ Subgroup.centralizer ({t} : Set CFSG.Sporadic.Fi22.J), ∀ k ∈ K,
      y * k * y⁻¹ ∈ K := by
    intro y hy k hk
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.1 (pi22_mem_range y)
    have hyt : y * t = t * y := (Subgroup.mem_centralizer_singleton_iff (g := t)).1 hy
    have hu : rho (g * s₀ * g⁻¹ * s₀⁻¹) = 1 := by
      have e : y * t * y⁻¹ * t⁻¹ = 1 := by rw [hyt, mul_inv_cancel_right, mul_inv_cancel]
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hg, ← ht, ← map_inv pi22 y,
        ← map_inv pi22 t, ← map_mul pi22, ← map_mul pi22, ← map_mul pi22, e, map_one]
    have hgC : (g : J) ∈ Subgroup.centralizer ({s} : Set J) := by
      rcases hker _ hu with h | h
      · have h' := congrArg Subtype.val h
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
          Subgroup.coe_inv, Subgroup.coe_one, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h'
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact h'
      · exfalso
        have h' := congrArg Subtype.val h
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
          Subgroup.coe_inv, dCd_val, mul_inv_eq_iff_eq_mul] at h'
        exact d_ne_one (@eq_one_of_conj_eq_mul J (inferInstance : Group J) d s (g : J)
          hsd.symm d_sq hs3 h')
    obtain ⟨m, hm, hmk⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hk)
    have hmN : (m : J) ∈ N := (Subgroup.mem_subgroupOf.1 hm).1
    have hgmN : ((g * m * g⁻¹ : Cd) : J) ∈ N := by
      have := GLAPPrimeCoreOf_conj_mem (g : J) hgC _ hmN
      simpa using this
    refine Subgroup.mem_comap.2 (Subgroup.mem_map.2 ⟨g * m * g⁻¹,
      Subgroup.mem_subgroupOf.2 ⟨hgmN, (g * m * g⁻¹).2⟩, ?_⟩)
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hg, hmk]
  have hKcop : Nat.Coprime 3 (Nat.card K) := by
    have h1 : Nat.card K = Nat.card (K.map pi22) :=
      (Subgroup.card_map_of_injective pi22_injective).symm
    have h3 : Nat.card (K.map pi22) ∣ Nat.card (M.map rho) :=
      Subgroup.card_dvd_of_le (Subgroup.map_comap_le _ _)
    have h4 : Nat.card (M.map rho) ∣ Nat.card M := Subgroup.card_map_dvd M rho
    have h5 : Nat.card M = Nat.card ↥(N ⊓ Cd) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    have h6 : Nat.card ↥(N ⊓ Cd) ∣ Nat.card N := Subgroup.card_dvd_of_le inf_le_left
    have hcop := coprime_card_GLAPPrimeCoreOf Nat.prime_three
      (Subgroup.centralizer ({s} : Set J))
    rw [h1]
    rw [h5] at h4
    exact Nat.Coprime.coprime_dvd_right (h3.trans (h4.trans h6)) hcop
  have hKle := le_GLAPPrimeCoreOf_of_normal hKC hKn hKcop
  rw [oPrimeCoreTrivialAt_Fi22J t hto] at hKle
  set x₀ : Cd := ⟨x, mem_Cd.2 hxd⟩ with hx₀
  have hx₀M : x₀ ∈ M := Subgroup.mem_subgroupOf.2 ⟨hx, x₀.2⟩
  obtain ⟨k, hk⟩ := MonoidHom.mem_range.1
    (show rho x₀ ∈ pi22.range by rw [← range_rho]; exact MonoidHom.mem_range.2 ⟨x₀, rfl⟩)
  have hkK : k ∈ K := Subgroup.mem_comap.2 (by rw [hk]; exact Subgroup.mem_map_of_mem rho hx₀M)
  have hk1 : k = 1 := Subgroup.mem_bot.1 (hKle hkK)
  have hρ : rho x₀ = 1 := by rw [← hk, hk1, map_one]
  rcases hker x₀ hρ with h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (congrArg Subtype.val h)

theorem fi23_local {s : J} (hs : orderOf s = 3) {e : J} (he : e ∈ D23) (hes : e * s = s * e)
    (n : J) (hn : n ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({s} : Set J)))
    (hne : n * e = e * n) : n = 1 ∨ n = e := by
  obtain ⟨g, hg⟩ := isConj_iff.1 (show IsConj d e from he)
  have hs' : orderOf (g⁻¹ * s * g) = 3 := by
    have h := CFSG.Sporadic.Fi23.orderOf_conj g⁻¹ s
    rw [inv_inv] at h
    rw [h, hs]
  have hs'd : g⁻¹ * s * g * d = d * (g⁻¹ * s * g) := by
    rw [← hg] at hes
    calc g⁻¹ * s * g * d = g⁻¹ * (s * (g * d * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * d * g⁻¹ * s) * g := by rw [hes]
      _ = d * (g⁻¹ * s * g) := by group
  have hn' := @conj_mem_gLAPPrimeCoreOf_centralizer J (inferInstance : Group J) 3 g⁻¹ s n hn
  rw [inv_inv] at hn'
  have hn'd : g⁻¹ * n * g * d = d * (g⁻¹ * n * g) := by
    rw [← hg] at hne
    calc g⁻¹ * n * g * d = g⁻¹ * (n * (g * d * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * d * g⁻¹ * n) * g := by rw [hne]
      _ = d * (g⁻¹ * n * g) := by group
  rcases fi23_local_d hs' hs'd _ hn' hn'd with h | h
  · left
    calc n = g * (g⁻¹ * n * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  · right
    calc n = g * (g⁻¹ * n * g) * g⁻¹ := by group
      _ = e := by rw [h, hg]

theorem gLAPPrimeCoreOf_fi23_eq_bot {s : J} (hs : orderOf s = 3) {e : J} (he : e ∈ D23)
    (hes : e * s = s * e) : GLAPPrimeCoreOf 3 (Subgroup.centralizer ({s} : Set J)) = ⊥ := by
  obtain ⟨i, hi⟩ := (isConj_d_iff e).1 he
  have hsi : s • i = i := by
    refine (smul_eq_iff s i i).2 ?_
    rw [hi, ← hes, mul_inv_cancel_right]
  obtain ⟨j, hji, hsj⟩ := fi23_exists_fixed_ne hs hsi
  have hfD : conjPt j.val ∈ D23 := (isConj_d_iff _).2 ⟨j, rfl⟩
  have hfs : conjPt j.val * s = s * conjPt j.val := by
    have h := (smul_eq_iff s j j).1 hsj
    calc conjPt j.val * s = s * conjPt j.val * s⁻¹ * s := by rw [h]
      _ = s * conjPt j.val := by group
  have hef : e ≠ conjPt j.val := by
    intro h
    apply hji
    apply Fin.ext
    have h' : conjPt j.val = conjPt i.val := by rw [hi]; exact h.symm
    exact conjPt_inj (by rw [orb_size]; exact j.2) (by rw [orb_size]; exact i.2) h'
  exact @gLAPPrimeCoreOf_eq_bot_of_two_fixed J (inferInstance : Group J) inferInstance D23
    (fun x hx => D23_mul_self hx) (fun x hx => D23_ne_one hx)
    (fun x hx y hy hxy => D23_cube hx hy hxy) (fun x hx g => D23_conj hx g) s e (conjPt j.val)
    he hfD hef hes hfs (fun x hx hxs n hn hnx => fi23_local hs hx hxs n hn hnx)

theorem oPrimeCoreTrivialAt_Fi23J_of_fixed (h : Fi23ThreeTranspositionFixed) :
    OPrimeCoreTrivialAt 3 J := by
  intro s hs
  obtain ⟨e, he, hes⟩ := h s hs
  exact gLAPPrimeCoreOf_fi23_eq_bot hs he hes

theorem sporadicOPrimeHolds_Fi23_three_of_fixed (h : Fi23ThreeTranspositionFixed) :
    SporadicOPrimeHolds .Fi23 3 := by
  intro S _ _ _ ⟨e⟩
  have e0 : S ≃* NativeSporadic.Fi23 := e
  exact @OPrimeCoreTrivialAt.of_mulEquiv 3 S _ ↥J inferInstance (e0.trans fi23EquivJ)
    (oPrimeCoreTrivialAt_Fi23J_of_fixed h)

theorem sporadicOnePairHolds_Fi23_three_of_fixed
    (h : Fi23ThreeTranspositionFixed) : SporadicOnePairHolds .Fi23 3 :=
  ⟨sporadicOPrimeHolds_Fi23_three_of_fixed h, sporadicOuterHolds_Fi23 3⟩

end Local

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
