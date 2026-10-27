module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74ThreeNorm

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open CFSG Subgroup CFSG.LieType.Universal.Spin

variable {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
  (hK : Nat.card K = p ^ f)
include hp hp2 hK

theorem eq_of_mem_spinJ_odd {J : Subgroup (spinGroup (quadOdd 3 K))}
    (hJ : J = spinJ₁ K ∨ J = spinJ₂ K ∨ J = spinJ₃ K) :
    (spinZ K ∈ J → J = spinJ₁ K) ∧ (tSeven K ∈ J → J = spinJ₂ K) ∧
      (spinZ K * tSeven K ∈ J → J = spinJ₃ K) := by
  obtain ⟨hzz, hz1, hzc, -, ht1, htc, hz1J, ht2J, hzt3J, -⟩ := spinZ_facts hp hp2 hK
  have hzt1 : spinZ K * tSeven K ≠ 1 := fun h => htc (by
    rw [(eq_inv_of_mul_eq_one_right h).trans (inv_eq_of_mul_eq_one_right hzz)]
    exact hzc)
  have hinf := fun y : spinGroup (quadOdd 3 K) => spinJ_inf_eq_one_odd (K := K) hp hp2 hK (y := y)
  rcases hJ with rfl | rfl | rfl
  · exact ⟨fun _ => rfl, fun h => absurd ((hinf _).1 h ht2J) ht1,
      fun h => absurd ((hinf _).2.1 h hzt3J) hzt1⟩
  · exact ⟨fun h => absurd ((hinf _).1 hz1J h) hz1, fun _ => rfl,
      fun h => absurd ((hinf _).2.2 h hzt3J) hzt1⟩
  · exact ⟨fun h => absurd ((hinf _).2.1 hz1J h) hz1, fun h => absurd ((hinf _).2.2 ht2J h) ht1,
      fun _ => rfl⟩

variable {G : Type} [Group G] [Finite G] {φ : spinGroup (quadOdd 3 K) →* G}
  (hφ : Function.Injective φ) {D : Subgroup G}
  (hCD : (centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K)))).map φ ≤ D)
  (hCn : ∀ d ∈ D, ∀ x ∈ (centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K)))).map φ,
    d * x * d⁻¹ ∈ (centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K)))).map φ)
  (hodd : Odd (((centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K)))).map φ).relIndex D))
include hφ hCD hCn hodd

theorem map_conj_centralizer_tSeven {g : G} (hg : g ∈ normalizer (D : Set G)) :
    ((centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K)))).map φ).map
        (MulAut.conj g).toMonoidHom =
      (centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K)))).map φ := by
  set C := centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))) with hC
  set C' := C.map φ with hC'
  set Cg := C'.map (MulAut.conj g).toMonoidHom with hCg
  have hgD : ∀ x ∈ D, g * x * g⁻¹ ∈ D := fun x hx => (mem_normalizer_iff.mp hg x).mp hx
  have hgD' : ∀ x ∈ D, g⁻¹ * x * g ∈ D := fun x hx => by
    have := (mem_normalizer_iff.mp (inv_mem hg) x).mp hx
    rwa [inv_inv] at this
  have hCgD : Cg ≤ D := by
    rintro _ ⟨x, hx, rfl⟩
    exact hgD x (hCD hx)
  have hCgn : ∀ d ∈ D, ∀ y ∈ Cg, d * y * d⁻¹ ∈ Cg := by
    rintro d hd _ ⟨x, hx, rfl⟩
    refine ⟨(g⁻¹ * d * g) * x * (g⁻¹ * d * g)⁻¹, hCn _ (hgD' d hd) x hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hDg : D.map (MulAut.conj g).toMonoidHom = D := by
    refine eq_of_le_of_card_ge ?_ (card_map_of_injective (MulAut.conj g).injective).ge
    rintro _ ⟨x, hx, rfl⟩
    exact hgD x hx
  have hoddg : Odd (Cg.relIndex D) := by
    rw [← hDg, hCg, relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
    exact hodd
  have hodd' : Odd (Cg.relIndex C') := by
    have hn : (Cg.subgroupOf D).Normal := ⟨fun n hn d => by
      rw [mem_subgroupOf] at hn ⊢
      simp only [coe_mul, coe_inv]
      exact hCgn d d.2 n hn⟩
    have h1 : (Cg.subgroupOf D).relIndex (Cg.subgroupOf D ⊔ C'.subgroupOf D) =
        (Cg.subgroupOf D).relIndex (C'.subgroupOf D) := relIndex_sup_left _ _
    have h2 : (Cg.subgroupOf D).relIndex (Cg.subgroupOf D ⊔ C'.subgroupOf D) ∣
        (Cg.subgroupOf D).index := relIndex_dvd_index_of_le le_sup_left
    have h3 : (Cg.subgroupOf D).relIndex (C'.subgroupOf D) = Cg.relIndex C' :=
      relIndex_subgroupOf hCD
    rw [← h3, ← h1]
    exact Odd.of_dvd_nat hoddg h2
  have hrange : C' ≤ φ.range := by
    rintro _ ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  set N : Subgroup ↥C := (Cg.comap φ).subgroupOf C with hN
  have hNn : N.Normal := ⟨fun n hn c => by
    rw [hN, mem_subgroupOf, mem_comap] at hn ⊢
    simp only [coe_mul, coe_inv, map_mul, map_inv]
    exact hCgn _ (hCD ⟨c, c.2, rfl⟩) _ hn⟩
  have hNi : N.index = Cg.relIndex C' := by
    change (Cg.comap φ).relIndex C = _
    rw [← relIndex_map_map_of_injective _ _ hφ, map_comap_eq, ← hC', inf_comm,
      ← inf_relIndex_right, inf_assoc, inf_of_le_right hrange, inf_relIndex_right]
  have hNtop : N = ⊤ := eq_top_of_normal_of_odd_index hp hp2 hK (N := N) (by
    rw [hNi]
    exact fun h2 => (Nat.not_even_iff_odd.mpr hodd') (even_iff_two_dvd.mpr h2))
  have hle : C' ≤ Cg := by
    rintro _ ⟨c, hc, rfl⟩
    have h1 : (⟨c, hc⟩ : ↥C) ∈ N := hNtop ▸ mem_top _
    exact h1
  exact (eq_of_le_of_card_ge hle
    (by rw [hCg, card_map_of_injective (MulAut.conj g).injective])).symm

theorem map_conj_spinJ {g : G} (hg : g ∈ normalizer (D : Set G))
    {J : Subgroup (spinGroup (quadOdd 3 K))} (hJ : J = spinJ₁ K ∨ J = spinJ₂ K ∨ J = spinJ₃ K) :
    ∃ J' : Subgroup (spinGroup (quadOdd 3 K)), (J' = spinJ₁ K ∨ J' = spinJ₂ K ∨ J' = spinJ₃ K) ∧
      (J.map φ).map (MulAut.conj g).toMonoidHom = J'.map φ := by
  have hCg := map_conj_centralizer_tSeven hp hp2 hK hφ hCD hCn hodd hg
  obtain ⟨l1, l2, l3⟩ := spinJ_le_centralizer (K := K) hp hp2 hK
  obtain ⟨n1, n2, n3⟩ := normal_spinJ_odd (K := K) hp hp2 hK
  have hJC : J ≤ centralizer {tSeven K} := by
    rcases hJ with rfl | rfl | rfl
    · exact l1
    · exact l2
    · exact l3
  have hJn : (J.subgroupOf (centralizer {tSeven K})).Normal := by
    rcases hJ with rfl | rfl | rfl
    · exact n1
    · exact n2
    · exact n3
  set Jg := (J.map φ).map (MulAut.conj g).toMonoidHom with hJg
  have hJgC : Jg ≤ (centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K)))).map φ := by
    rw [← hCg]
    exact map_mono (map_mono hJC)
  have hrange : Jg ≤ φ.range := by
    intro x hx
    obtain ⟨y, -, hyx⟩ := hJgC hx
    exact ⟨y, hyx⟩
  set P := Jg.comap φ with hP
  have hPmap : P.map φ = Jg := map_comap_eq_self hrange
  have hPC : P ≤ centralizer {tSeven K} := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hJgC hx
    rw [← hφ hyx]
    exact hy
  have hPn : (P.subgroupOf (centralizer {tSeven K})).Normal := by
    constructor
    intro x hx c
    rw [mem_subgroupOf, mem_comap] at hx ⊢
    have hc : φ c ∈ ((centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K)))).map φ).map
        (MulAut.conj g).toMonoidHom := by
      rw [hCg]
      exact ⟨c, c.2, rfl⟩
    obtain ⟨_, ⟨c₀, hc₀, rfl⟩, hc'⟩ := hc
    obtain ⟨_, ⟨j, hj, rfl⟩, hj'⟩ := hx
    have hcj : c₀ * j * c₀⁻¹ ∈ J :=
      mem_subgroupOf.mp (hJn.conj_mem ⟨j, hJC hj⟩ (mem_subgroupOf.mpr hj) ⟨c₀, hc₀⟩)
    refine ⟨φ (c₀ * j * c₀⁻¹), ⟨_, hcj, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hc' hj' ⊢
    simp only [coe_mul, coe_inv, map_mul, map_inv]
    rw [← hc', ← hj']
    group
  let e : ↥J ≃* ↥P := (J.equivMapOfInjective φ hφ).trans
    (((J.map φ).equivMapOfInjective _ (MulAut.conj g).injective).trans
      ((P.equivMapOfInjective φ hφ).trans (MulEquiv.subgroupCongr hPmap)).symm)
  exact ⟨P, eq_spinJ_of_normal_of_mulEquiv hp hp2 hK hPC hPn hJ e.symm, hPmap.symm⟩

omit [Finite K] hp hp2 hK [Finite G] hCD hCn hodd in
theorem mem_of_map_conj_eq {g : G} {J J' : Subgroup (spinGroup (quadOdd 3 K))}
    (h : (J.map φ).map (MulAut.conj g).toMonoidHom = J'.map φ) {x y : spinGroup (quadOdd 3 K)}
    (hx : x ∈ J) (hy : g * φ x * g⁻¹ = φ y) : y ∈ J' := by
  have hφy : φ y ∈ J'.map φ := by
    rw [← h, ← hy]
    exact ⟨φ x, ⟨x, hx, rfl⟩, rfl⟩
  obtain ⟨y', hy', hyy⟩ := hφy
  rw [← hφ hyy]
  exact hy'

theorem map_conj_spinJ_of_fix {g : G} (hg : g ∈ normalizer (D : Set G))
    (hz : g * φ (spinZ K) * g⁻¹ = φ (spinZ K)) (ht : g * φ (tSeven K) * g⁻¹ = φ (tSeven K))
    {J : Subgroup (spinGroup (quadOdd 3 K))} (hJ : J = spinJ₁ K ∨ J = spinJ₂ K ∨ J = spinJ₃ K) :
    (J.map φ).map (MulAut.conj g).toMonoidHom = J.map φ := by
  obtain ⟨J', hJ', h⟩ := map_conj_spinJ hp hp2 hK hφ hCD hCn hodd hg hJ
  obtain ⟨-, -, -, -, -, -, hz1, ht2, hzt3, -⟩ := spinZ_facts hp hp2 hK
  obtain ⟨f1, f2, f3⟩ := eq_of_mem_spinJ_odd hp hp2 hK hJ'
  rw [h]
  congr 1
  rcases hJ with rfl | rfl | rfl
  · exact f1 (mem_of_map_conj_eq hφ h hz1 hz)
  · exact f2 (mem_of_map_conj_eq hφ h ht2 ht)
  · refine f3 (mem_of_map_conj_eq hφ h hzt3 ?_)
    rw [map_mul]
    calc g * (φ (spinZ K) * φ (tSeven K)) * g⁻¹ =
        (g * φ (spinZ K) * g⁻¹) * (g * φ (tSeven K) * g⁻¹) := by group
      _ = φ (spinZ K) * φ (tSeven K) := by rw [hz, ht]

theorem map_conj_spinJ_of_swap {n : G} (hn : n ∈ normalizer (D : Set G))
    (h1 : n * φ (tSeven K) * n⁻¹ = φ (spinZ K)) (h2 : n * φ (spinZ K) * n⁻¹ = φ (tSeven K)) :
    ((spinJ₁ K).map φ).map (MulAut.conj n).toMonoidHom = (spinJ₂ K).map φ ∧
      ((spinJ₂ K).map φ).map (MulAut.conj n).toMonoidHom = (spinJ₁ K).map φ ∧
      ((spinJ₃ K).map φ).map (MulAut.conj n).toMonoidHom = (spinJ₃ K).map φ := by
  obtain ⟨-, -, hzc, -, -, -, hz1, ht2, hzt3, -⟩ := spinZ_facts hp hp2 hK
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨J', hJ', h⟩ := map_conj_spinJ hp hp2 hK hφ hCD hCn hodd hn (Or.inl rfl)
    rw [h, (eq_of_mem_spinJ_odd hp hp2 hK hJ').2.1
      (mem_of_map_conj_eq hφ h hz1 h2)]
  · obtain ⟨J', hJ', h⟩ := map_conj_spinJ hp hp2 hK hφ hCD hCn hodd hn (Or.inr (Or.inl rfl))
    rw [h, (eq_of_mem_spinJ_odd hp hp2 hK hJ').1
      (mem_of_map_conj_eq hφ h ht2 h1)]
  · obtain ⟨J', hJ', h⟩ := map_conj_spinJ hp hp2 hK hφ hCD hCn hodd hn (Or.inr (Or.inr rfl))
    refine h.trans ?_
    rw [(eq_of_mem_spinJ_odd hp hp2 hK hJ').2.2
      (mem_of_map_conj_eq hφ h hzt3 ?_)]
    calc n * φ (spinZ K * tSeven K) * n⁻¹ =
        (n * φ (spinZ K) * n⁻¹) * (n * φ (tSeven K) * n⁻¹) := by rw [map_mul]; group
      _ = φ (tSeven K) * φ (spinZ K) := by rw [h1, h2]
      _ = φ (spinZ K * tSeven K) := by rw [← map_mul, mem_center_iff.mp hzc (tSeven K)]

end CFSG.ComponentClassification.HarrisLit.T1.S74
