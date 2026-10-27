module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCentralizer

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane

open CFSG.Open

variable {G : Type*} [Group G] {p : ℕ}

theorem exists_closure_pair_of_mem (hp : p.Prime) {D : Subgroup G}
    (hDp : ∀ x ∈ D, x ^ p = 1) (hcard : Nat.card D = p ^ 2) {d : G} (hd : d ∈ D)
    (hd1 : d ≠ 1) : ∃ e ∈ D, Subgroup.closure {d, e} = D := by
  have := Fact.mk hp
  have hfin : Finite D := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hp.ne_zero)
  have hzd : Nat.card (Subgroup.zpowers d) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hDp d hd) hd1]
  have hzle : Subgroup.zpowers d ≤ D := (Subgroup.zpowers_le).2 hd
  have hfinz : Finite (Subgroup.zpowers d) :=
    Finite.of_injective (Subgroup.inclusion hzle) (Subgroup.inclusion_injective hzle)
  obtain ⟨e, heD, he⟩ : ∃ e ∈ D, e ∉ Subgroup.zpowers d := by
    by_contra hcon
    push Not at hcon
    have h1 := Subgroup.card_le_of_le (fun x hx => hcon x hx : D ≤ Subgroup.zpowers d)
    rw [hcard, hzd] at h1
    nlinarith [hp.one_lt]
  refine ⟨e, heD, ?_⟩
  have hHD : Subgroup.closure ({d, e} : Set G) ≤ D :=
    (Subgroup.closure_le D).2 (by simp [Set.insert_subset_iff, hd, heD])
  have hfinH : Finite (Subgroup.closure ({d, e} : Set G)) :=
    Finite.of_injective (Subgroup.inclusion hHD) (Subgroup.inclusion_injective hHD)
  obtain ⟨k, hk, hkH⟩ := (Nat.dvd_prime_pow hp).1 (hcard ▸ Subgroup.card_dvd_of_le hHD)
  have hzH : Subgroup.zpowers d ≤ Subgroup.closure ({d, e} : Set G) :=
    (Subgroup.zpowers_le).2 (Subgroup.subset_closure (by simp))
  have heH : e ∈ Subgroup.closure ({d, e} : Set G) := Subgroup.subset_closure (by simp)
  have hk2 : k = 2 := by
    by_contra hk2
    have hle : Nat.card (Subgroup.closure ({d, e} : Set G)) ≤
        Nat.card (Subgroup.zpowers d) := by
      rw [hkH, hzd]
      calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
        _ = p := pow_one p
    exact he ((Subgroup.eq_of_le_of_card_ge hzH hle) ▸ heH)
  exact Subgroup.eq_of_le_of_card_ge hHD (by rw [hcard, hkH, hk2])

theorem exists_ne_one_ker_of_isCyclic (hp : p.Prime) {D : Subgroup G}
    (hDp : ∀ x ∈ D, x ^ p = 1) (hcard : Nat.card D = p ^ 2) {Q : Type*} [Group Q] (ψ : G →* Q)
    (hψ : IsCyclic (D.map ψ)) : ∃ d ∈ D, d ≠ 1 ∧ ψ d = 1 := by
  by_contra hcon
  push Not at hcon
  set f := ψ.comp D.subtype
  have hrange : f.range = D.map ψ := by rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hinj : Function.Injective f.rangeRestrict := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : ψ x = 1 := congrArg Subtype.val hx
    by_contra hx1
    exact hcon x x.2 (fun h => hx1 (Subtype.ext h)) h1
  have : IsCyclic f.range := by rw [hrange]; exact hψ
  have hDcyc : IsCyclic D := isCyclic_of_injective _ hinj
  have hfin : Finite D := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hp.ne_zero)
  have hexp : Monoid.exponent D ∣ p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
    Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hDp x x.2)
  rw [IsCyclic.exponent_eq_card, hcard] at hexp
  have := Nat.le_of_dvd hp.pos hexp
  nlinarith [hp.one_lt]

theorem commute_of_mem_GLAPPrimeCoreOf [Finite G] (hp : p.Prime) {C Q : Subgroup G}
    (hQC : Q ≤ C) (hQn : ∀ g ∈ C, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) (hQp : ∀ q ∈ Q, q ^ p = 1)
    {x : G} (hx : x ∈ GLAPPrimeCoreOf p C) {q : G} (hq : q ∈ Q) : x * q = q * x := by
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
  set q' : C := ⟨q, hQC hq⟩
  have hzQ : (y : G) * q * (y : G)⁻¹ * q⁻¹ ∈ Q :=
    Q.mul_mem (hQn _ y.2 q hq) (Q.inv_mem hq)
  have hzN : y * q' * y⁻¹ * q'⁻¹ ∈ GLAPPrimeCore p C := by
    have h1 : q' * y⁻¹ * q'⁻¹ ∈ GLAPPrimeCore p C :=
      (GLAPPrimeCore.normal p C).conj_mem _ (inv_mem hy) q'
    have h2 := (GLAPPrimeCore p C).mul_mem hy h1
    rwa [← mul_assoc, ← mul_assoc] at h2
  set z : GLAPPrimeCore p C := ⟨_, hzN⟩
  have hzp : ((z : C) : G) ^ p = 1 := hQp _ hzQ
  have hcop := coprime_card_GLAPPrimeCore hp C
  have hz : z = 1 := by
    have h1 : orderOf z ∣ p := orderOf_dvd_of_pow_eq_one (by
      apply Subtype.ext
      apply Subtype.ext
      simpa using hzp)
    have h2 : orderOf z ∣ Nat.card (GLAPPrimeCore p C) := orderOf_dvd_natCard z
    have h3 := Nat.dvd_gcd h1 h2
    rw [hcop.gcd_eq_one, Nat.dvd_one] at h3
    exact orderOf_eq_one_iff.1 h3
  have hz' : (y : G) * q * (y : G)⁻¹ * q⁻¹ = 1 :=
    congrArg (fun w : GLAPPrimeCore p C => ((w : C) : G)) hz
  have h := congrArg (· * q) hz'
  simp only [inv_mul_cancel_right, one_mul] at h
  have h' := congrArg (· * (y : G)) h
  simp only [inv_mul_cancel_right] at h'
  exact h'

theorem localDelta_commute [Finite G] (hp : p.Prime) {H D V : Subgroup G} {d : G} (hdD : d ∈ D)
    (hd1 : d ≠ 1) (hDH : D ≤ H) (hVH : V ≤ H) (hVd : V ≤ Subgroup.centralizer {d})
    (hVn : ∀ g ∈ H, g * d = d * g → ∀ v ∈ V, g * v * g⁻¹ ∈ V) (hVp : ∀ v ∈ V, v ^ p = 1)
    {x : G} (hx : x ∈ localDelta p H D) {v : G} (hv : v ∈ V) : x * v = v * x := by
  obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.1 hx
  set d' : H := ⟨d, hDH hdD⟩
  have hd'D : d' ∈ D.subgroupOf H := Subgroup.mem_subgroupOf.2 hdD
  have hd'1 : d' ≠ 1 := fun h => hd1 (congrArg Subtype.val h)
  have hx'' := GLADelta_le_GLAPPrimeCoreOf p hd'D hd'1 hx'
  have hQC : V.subgroupOf H ≤ Subgroup.centralizer {d'} := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.1 hg]
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hVd (Subgroup.mem_subgroupOf.1 hw)) d rfl)
  have hQn : ∀ g ∈ Subgroup.centralizer {d'}, ∀ q ∈ V.subgroupOf H,
      g * q * g⁻¹ ∈ V.subgroupOf H := by
    intro g hg q hq
    rw [Subgroup.mem_subgroupOf]
    have hgd : (g : G) * d = d * g :=
      (congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hg d' rfl)).symm
    exact hVn g g.2 hgd q (Subgroup.mem_subgroupOf.1 hq)
  have hQp : ∀ q ∈ V.subgroupOf H, q ^ p = 1 := fun q hq =>
    Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hVp _ (Subgroup.mem_subgroupOf.1 hq))
  have h := commute_of_mem_GLAPPrimeCoreOf hp hQC hQn hQp hx'' (q := (⟨v, hVH hv⟩ : H))
    (Subgroup.mem_subgroupOf.2 hv)
  exact congrArg Subtype.val h

theorem characteristic_of_max {C U : Subgroup G} (hUC : U ≤ C)
    (hUab : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x) (hUp : ∀ x ∈ U, x ^ p = 1)
    (hUcard : p ^ 2 < Nat.card U)
    (hmax : ∀ E : Subgroup G, E ≤ C → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) →
      (∀ x ∈ E, x ^ p = 1) → p ^ 2 < Nat.card E → E ≤ U) :
    (U.subgroupOf C).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro φ y hy
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hy
  set E := ((U.subgroupOf C).map φ.toMonoidHom).map C.subtype
  have hEC : E ≤ C := Subgroup.map_subtype_le _
  have hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩ _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    simp only [Subgroup.coe_subtype]
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul]
    congr 2
    exact Subtype.ext (hUab _ (Subgroup.mem_subgroupOf.1 ha) _ (Subgroup.mem_subgroupOf.1 hb))
  have hEp : ∀ x ∈ E, x ^ p = 1 := by
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    simp only [Subgroup.coe_subtype]
    rw [← SubmonoidClass.coe_pow, ← map_pow]
    have : a ^ p = 1 := Subtype.ext (by
      rw [SubmonoidClass.coe_pow]; exact hUp _ (Subgroup.mem_subgroupOf.1 ha))
    rw [this, map_one]
    rfl
  have hEcard : Nat.card E = Nat.card U := by
    rw [Subgroup.card_map_of_injective C.subtype_injective,
      Subgroup.card_map_of_injective φ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUC).toEquiv]
  have hle := hmax E hEC hEab hEp (hEcard ▸ hUcard)
  exact Subgroup.mem_subgroupOf.2 (hle ⟨_, ⟨u, hu, rfl⟩, rfl⟩)

theorem conj_mem_of_max {C U : Subgroup G} (hUC : U ≤ C)
    (hUab : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x) (hUp : ∀ x ∈ U, x ^ p = 1)
    (hUcard : p ^ 2 < Nat.card U)
    (hmax : ∀ E : Subgroup G, E ≤ C → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) →
      (∀ x ∈ E, x ^ p = 1) → p ^ 2 < Nat.card E → E ≤ U)
    {g : G} (hg : ∀ c ∈ C, g * c * g⁻¹ ∈ C) : ∀ u ∈ U, g * u * g⁻¹ ∈ U := by
  set E := U.map (MulAut.conj g).toMonoidHom
  have hEC : E ≤ C := by
    rintro _ ⟨u, hu, rfl⟩
    exact hg u (hUC hu)
  have hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hUab a ha b hb]
  have hEp : ∀ x ∈ E, x ^ p = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hUp a ha, map_one]
  have hEcard : Nat.card E = Nat.card U :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hle := hmax E hEC hEab hEp (hEcard ▸ hUcard)
  intro u hu
  exact hle ⟨u, hu, rfl⟩

end CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane
