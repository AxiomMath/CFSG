module

public import CFSG.LargeExtraspecial.A2ModPLb

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.A2Mod

open Module Matrix CFSG.RankThree.OrthogonalInvolutions OrthoF2

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : SpecialLinearGroup (Fin n) (ZMod 2) →* (V ≃ₗ[ZMod 2] V)}

theorem range_inf_range_eq_bot_of_equivariant (hn : 3 ≤ n)
    {P Pd : (Fin n → ZMod 2) →ₗ[ZMod 2] V} (hP : Function.Injective P)
    (hPd : Function.Injective Pd)
    (hPe : ∀ (g : SpecialLinearGroup (Fin n) (ZMod 2)) (x : Fin n → ZMod 2),
      P ((g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) = ρ g (P x))
    (hPde : ∀ (g : SpecialLinearGroup (Fin n) (ZMod 2)) (φ : Fin n → ZMod 2),
      Pd (contra g φ) = ρ g (Pd φ)) :
    LinearMap.range P ⊓ LinearMap.range Pd = ⊥ := by
  set U := (LinearMap.range P ⊓ LinearMap.range Pd).comap P with hUdef
  have hmemU : ∀ x, x ∈ U ↔ ∃ φ, Pd φ = P x := fun x => by
    rw [hUdef, Submodule.mem_comap, Submodule.mem_inf]
    exact ⟨fun h => LinearMap.mem_range.mp h.2,
      fun h => ⟨LinearMap.mem_range_self P x, LinearMap.mem_range.mpr h⟩⟩
  have hU : ∀ g : SpecialLinearGroup (Fin n) (ZMod 2), ∀ x ∈ U,
      (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x ∈ U := by
    intro g x hx
    obtain ⟨φ, hφ⟩ := (hmemU x).mp hx
    exact (hmemU _).mpr ⟨contra g φ, by rw [hPde, hφ, hPe]⟩
  rcases eq_bot_or_eq_top_of_invariant U hU with hbot | htop
  · rw [eq_bot_iff]
    intro y hy
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp (Submodule.mem_inf.mp hy).1
    have hxU : x ∈ U := (hmemU x).mpr (LinearMap.mem_range.mp (Submodule.mem_inf.mp hy).2)
    rw [hbot, Submodule.mem_bot] at hxU
    rw [hxU, map_zero]
    exact Submodule.zero_mem _
  · exfalso
    have hall : ∀ x, ∃ φ, Pd φ = P x := fun x => (hmemU x).mp (by rw [htop]; exact trivial)
    choose f hf using hall
    have hfe : ∀ (g : SpecialLinearGroup (Fin n) (ZMod 2)) (x : Fin n → ZMod 2),
        f ((g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) = contra g (f x) := fun g x =>
      hPd (by rw [hf, hPe, ← hf x, hPde])
    have h0 := eq_zero_of_equivariant hn hfe
    have hn0 : 0 < n := by omega
    have he : (Pi.single (⟨0, hn0⟩ : Fin n) 1 : Fin n → ZMod 2) ≠ 0 :=
      Pi.single_ne_zero_iff.mpr one_ne_zero
    exact he (hP (by rw [← hf, h0, map_zero, map_zero]))

theorem finrank_range_sup_range_eq [FiniteDimensional (ZMod 2) V]
    {P Pd : (Fin n → ZMod 2) →ₗ[ZMod 2] V} (hP : Function.Injective P)
    (hPd : Function.Injective Pd) (hdisj : LinearMap.range P ⊓ LinearMap.range Pd = ⊥) :
    finrank (ZMod 2) ↥(LinearMap.range P ⊔ LinearMap.range Pd) = 2 * n := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range P) (LinearMap.range Pd)
  rw [hdisj, finrank_bot, add_zero, LinearMap.finrank_range_of_inj hP,
    LinearMap.finrank_range_of_inj hPd, Module.finrank_fin_fun] at h
  rw [h, two_mul]

variable [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
  {c d : (Fin n → ZMod 2) → V}

omit [FiniteDimensional (ZMod 2) V] in
theorem IsPointCentreMap.map_eq_zero (hA : A2Action (transvectionSet n (ZMod 2)) Q ρ)
    (hn : 2 ≤ n) (hc : IsPointCentreMap ρ c) (x : Fin n → ZMod 2) : Q (c x) = 0 := by
  by_cases hx : x = 0
  · rw [hx, hc.1, QuadraticMap.map_zero]
  obtain ⟨φ, hφ, hφx⟩ := exists_ne_zero_dotProduct_eq_zero hn x
  exact (hA.isTypeA (tv_mem_transvectionSet hx hφ hφx)).2.2.2.2 _ ((hc.2 x hx).2 φ hφ hφx)

omit [FiniteDimensional (ZMod 2) V] in
theorem IsHyperplaneCentreMap.map_eq_zero (hA : A2Action (transvectionSet n (ZMod 2)) Q ρ)
    (hn : 2 ≤ n) (hd : IsHyperplaneCentreMap ρ d) (φ : Fin n → ZMod 2) : Q (d φ) = 0 := by
  by_cases hφ : φ = 0
  · rw [hφ, hd.1, QuadraticMap.map_zero]
  obtain ⟨x, hx, hxφ⟩ := exists_ne_zero_dotProduct_eq_zero hn φ
  rw [dotProduct_comm] at hxφ
  exact (hA.isTypeA (tv_mem_transvectionSet hx hφ hxφ)).2.2.2.2 _ ((hd.2 φ hφ).2 x hx hxφ)

theorem exists_pointMaps_of_centreMaps (hA : A2Action (transvectionSet n (ZMod 2)) Q ρ)
    (hn : 4 ≤ n) (hc : IsPointCentreMap ρ c) (hd : IsHyperplaneCentreMap ρ d) :
    ∃ (P : (Fin n → ZMod 2) →ₗ[ZMod 2] V) (Pd : (Fin n → ZMod 2) →ₗ[ZMod 2] V),
      Function.Injective P ∧ Function.Injective Pd ∧
      (∀ (g : SpecialLinearGroup (Fin n) (ZMod 2)) (x : Fin n → ZMod 2),
        P ((g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) = ρ g (P x)) ∧
      (∀ (g : SpecialLinearGroup (Fin n) (ZMod 2)) (φ : Fin n → ZMod 2),
        Pd (contra g φ) = ρ g (Pd φ)) ∧
      (∀ v φ : Fin n → ZMod 2, v ≠ 0 → φ ≠ 0 → φ ⬝ᵥ v = 0 →
        commSpace (ρ (tv v φ)) = Submodule.span (ZMod 2) {P v, Pd φ}) ∧
      LinearMap.range P ⊓ LinearMap.range Pd = ⊥ ∧
      (∀ x, Q (P x) = 0) ∧ (∀ φ, Q (Pd φ) = 0) ∧
      commSpaceOf ρ ⊤ = LinearMap.range P ⊔ LinearMap.range Pd := by
  have hn3 : 3 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  let P : (Fin n → ZMod 2) →ₗ[ZMod 2] V :=
    { toFun := c
      map_add' := hc.map_add hA hn hd
      map_smul' := fun a x => by
        rcases zmod2_eq_zero_or_eq_one a with rfl | rfl
        · simp only [zero_smul, RingHom.id_apply, hc.1]
        · simp only [one_smul, RingHom.id_apply] }
  let Pd : (Fin n → ZMod 2) →ₗ[ZMod 2] V :=
    { toFun := d
      map_add' := hd.map_add hA hn hc
      map_smul' := fun a φ => by
        rcases zmod2_eq_zero_or_eq_one a with rfl | rfl
        · simp only [zero_smul, RingHom.id_apply, hd.1]
        · simp only [one_smul, RingHom.id_apply] }
  have hP : Function.Injective P := hc.injective hA hn3
  have hPd : Function.Injective Pd := hd.injective hA hn3
  have hPe : ∀ (g : SpecialLinearGroup (Fin n) (ZMod 2)) (x : Fin n → ZMod 2),
      P ((g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) = ρ g (P x) := hc.map_mulVec hA hn3
  have hPde : ∀ (g : SpecialLinearGroup (Fin n) (ZMod 2)) (φ : Fin n → ZMod 2),
      Pd (contra g φ) = ρ g (Pd φ) := hd.map_contra hA hn3
  refine ⟨P, Pd, hP, hPd, hPe, hPde,
    fun v φ hv hφ hvφ => commSpace_tv_eq_span hA hn3 hc hd hv hφ hvφ,
    range_inf_range_eq_bot_of_equivariant hn3 hP hPd hPe hPde, hc.map_eq_zero hA hn2,
    hd.map_eq_zero hA hn2, le_antisymm ?_ (sup_le ?_ ?_)⟩
  · rw [← closure_transvectionSet (n := n) (F := ZMod 2), commSpaceOf_closure]
    refine iSup₂_le fun t ht => ?_
    obtain ⟨v, φ, hv, hφ, hvφ, rfl⟩ := mem_transvectionSet.mp ht
    rw [commSpace_tv_eq_span hA hn3 hc hd hv hφ hvφ, Submodule.span_le]
    rintro y (rfl | rfl)
    · exact Submodule.mem_sup_left (LinearMap.mem_range_self P v)
    · exact Submodule.mem_sup_right (LinearMap.mem_range_self Pd φ)
  · intro y hy
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
    by_cases hx : x = 0
    · rw [hx, map_zero]
      exact Submodule.zero_mem _
    obtain ⟨φ, hφ, hφx⟩ := exists_ne_zero_dotProduct_eq_zero hn2 x
    exact commSpace_le_commSpaceOf ρ (Subgroup.mem_top _) ((hc.2 x hx).2 φ hφ hφx)
  · intro y hy
    obtain ⟨φ, rfl⟩ := LinearMap.mem_range.mp hy
    by_cases hφ : φ = 0
    · rw [hφ, map_zero]
      exact Submodule.zero_mem _
    obtain ⟨x, hx, hxφ⟩ := exists_ne_zero_dotProduct_eq_zero hn2 φ
    rw [dotProduct_comm] at hxφ
    exact commSpace_le_commSpaceOf ρ (Subgroup.mem_top _) ((hd.2 φ hφ).2 x hx hxφ)

theorem exists_pointMaps (hA : A2Action (transvectionSet n (ZMod 2)) Q ρ) (hn : 5 ≤ n) :
    ∃ (P : (Fin n → ZMod 2) →ₗ[ZMod 2] V) (Pd : (Fin n → ZMod 2) →ₗ[ZMod 2] V),
      Function.Injective P ∧ Function.Injective Pd ∧
      (∀ (g : SpecialLinearGroup (Fin n) (ZMod 2)) (x : Fin n → ZMod 2),
        P ((g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) = ρ g (P x)) ∧
      (∀ (g : SpecialLinearGroup (Fin n) (ZMod 2)) (φ : Fin n → ZMod 2),
        Pd (contra g φ) = ρ g (Pd φ)) ∧
      (∀ v φ : Fin n → ZMod 2, v ≠ 0 → φ ≠ 0 → φ ⬝ᵥ v = 0 →
        commSpace (ρ (tv v φ)) = Submodule.span (ZMod 2) {P v, Pd φ}) ∧
      LinearMap.range P ⊓ LinearMap.range Pd = ⊥ ∧
      (∀ x, Q (P x) = 0) ∧ (∀ φ, Q (Pd φ) = 0) ∧
      commSpaceOf ρ ⊤ = LinearMap.range P ⊔ LinearMap.range Pd := by
  obtain ⟨c, hc⟩ := exists_isPointCentreMap fun v hv => exists_isPointCentre hA hn hv
  obtain ⟨d, hd⟩ := exists_isHyperplaneCentreMap fun φ hφ => exists_isHyperplaneCentre hA hn hφ
  exact exists_pointMaps_of_centreMaps hA (by omega) hc hd

theorem exists_pointMaps_of_concurrent (hA : A2Action (transvectionSet n (ZMod 2)) Q ρ)
    (hn : 4 ≤ n) {v₀ φ₀ : Fin n → ZMod 2} (hv₀ : v₀ ≠ 0) (hφ₀ : φ₀ ≠ 0)
    (hcA : ∃ p : V, p ≠ 0 ∧ ∀ a ∈ pointGroup v₀, a ≠ 1 → p ∈ commSpace (ρ a))
    (hcB : ∃ p : V, p ≠ 0 ∧ ∀ a ∈ hyperplaneGroup φ₀, a ≠ 1 → p ∈ commSpace (ρ a)) :
    ∃ (P : (Fin n → ZMod 2) →ₗ[ZMod 2] V) (Pd : (Fin n → ZMod 2) →ₗ[ZMod 2] V),
      Function.Injective P ∧ Function.Injective Pd ∧
      (∀ (g : SpecialLinearGroup (Fin n) (ZMod 2)) (x : Fin n → ZMod 2),
        P ((g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) = ρ g (P x)) ∧
      (∀ (g : SpecialLinearGroup (Fin n) (ZMod 2)) (φ : Fin n → ZMod 2),
        Pd (contra g φ) = ρ g (Pd φ)) ∧
      (∀ v φ : Fin n → ZMod 2, v ≠ 0 → φ ≠ 0 → φ ⬝ᵥ v = 0 →
        commSpace (ρ (tv v φ)) = Submodule.span (ZMod 2) {P v, Pd φ}) ∧
      LinearMap.range P ⊓ LinearMap.range Pd = ⊥ ∧
      (∀ x, Q (P x) = 0) ∧ (∀ φ, Q (Pd φ) = 0) ∧
      commSpaceOf ρ ⊤ = LinearMap.range P ⊔ LinearMap.range Pd := by
  obtain ⟨p, hp⟩ := hcA
  obtain ⟨q, hq⟩ := hcB
  obtain ⟨c, hc⟩ := exists_isPointCentreMap fun v hv =>
    exists_isPointCentre_of_isPointCentre hv₀ ((isPointCentre_iff hv₀).mpr hp) hv
  obtain ⟨d, hd⟩ := exists_isHyperplaneCentreMap fun φ hφ =>
    exists_isHyperplaneCentre_of_isHyperplaneCentre hφ₀ ((isHyperplaneCentre_iff hφ₀).mpr hq) hφ
  exact exists_pointMaps_of_centreMaps hA hn hc hd

theorem exists_pointMaps_or_finrank_le (hA : A2Action (transvectionSet n (ZMod 2)) Q ρ)
    (hn : 4 ≤ n) :
    (∃ (P : (Fin n → ZMod 2) →ₗ[ZMod 2] V) (Pd : (Fin n → ZMod 2) →ₗ[ZMod 2] V),
      Function.Injective P ∧ Function.Injective Pd ∧
      (∀ (g : SpecialLinearGroup (Fin n) (ZMod 2)) (x : Fin n → ZMod 2),
        P ((g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) = ρ g (P x)) ∧
      (∀ (g : SpecialLinearGroup (Fin n) (ZMod 2)) (φ : Fin n → ZMod 2),
        Pd (contra g φ) = ρ g (Pd φ)) ∧
      (∀ v φ : Fin n → ZMod 2, v ≠ 0 → φ ≠ 0 → φ ⬝ᵥ v = 0 →
        commSpace (ρ (tv v φ)) = Submodule.span (ZMod 2) {P v, Pd φ}) ∧
      LinearMap.range P ⊓ LinearMap.range Pd = ⊥ ∧
      (∀ x, Q (P x) = 0) ∧ (∀ φ, Q (Pd φ) = 0) ∧
      commSpaceOf ρ ⊤ = LinearMap.range P ⊔ LinearMap.range Pd) ∨
      finrank (ZMod 2) (commSpaceOf ρ ⊤) ≤ n + 3 := by
  have hn0 : 0 < n := by omega
  set i : Fin n := ⟨0, hn0⟩
  have hei : (Pi.single i 1 : Fin n → ZMod 2) ≠ 0 := Pi.single_ne_zero_iff.mpr one_ne_zero
  by_cases h : (∃ p : V, p ≠ 0 ∧ ∀ a ∈ pointGroup (Pi.single i 1), a ≠ 1 → p ∈ commSpace (ρ a)) ∧
      ∃ p : V, p ≠ 0 ∧ ∀ a ∈ hyperplaneGroup (Pi.single i 1), a ≠ 1 → p ∈ commSpace (ρ a)
  · exact .inl (exists_pointMaps_of_concurrent hA hn hei hei h.1 h.2)
  · have := finrank_commSpaceOf_top_le_of_not_concurrent hA i h
    exact .inr (by omega)

theorem false_of_irreducible (hA : A2Action (transvectionSet n (ZMod 2)) Q ρ) (hn : 5 ≤ n)
    (hirr : ∀ W : Submodule (ZMod 2) V, (∀ x, ∀ w ∈ W, ρ x w ∈ W) → W = ⊥ ∨ W = ⊤) : False := by
  obtain ⟨P, Pd, hP, hPd, hPe, -, -, hdisj, -⟩ := exists_pointMaps hA hn
  have hn0 : 0 < n := by omega
  set e : Fin n → ZMod 2 := Pi.single (⟨0, hn0⟩ : Fin n) 1
  have he : e ≠ 0 := Pi.single_ne_zero_iff.mpr one_ne_zero
  have hinv : ∀ (g : SpecialLinearGroup (Fin n) (ZMod 2)), ∀ w ∈ LinearMap.range P,
      ρ g w ∈ LinearMap.range P := by
    intro g w hw
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hw
    exact LinearMap.mem_range.mpr ⟨_, hPe g x⟩
  rcases hirr _ hinv with h | h
  · have hmem := LinearMap.mem_range_self P e
    rw [h, Submodule.mem_bot] at hmem
    exact he (hP (by rw [hmem, map_zero]))
  · have hmem : Pd e ∈ LinearMap.range P ⊓ LinearMap.range Pd :=
      Submodule.mem_inf.mpr ⟨by rw [h]; exact trivial, LinearMap.mem_range_self _ _⟩
    rw [hdisj, Submodule.mem_bot] at hmem
    exact he (hPd (by rw [hmem, map_zero]))

end CFSG.LargeExtraspecial.A2Mod
