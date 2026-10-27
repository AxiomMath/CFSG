module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.CrossDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.FamilyTools
public import CFSG.Open.StatedDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

open CFSG.Open

private theorem diagGL_mem_scalars {L : Type} [Field L] {n : ℕ} {u : Fin n → Lˣ}
    (h : diagGL n u ∈ StatedScalars (Fin n) L) : ∃ s : Lˣ, ∀ i, u i = s := by
  obtain ⟨s, hs⟩ := h
  refine ⟨s, fun i => ?_⟩
  have := congrArg (fun g : GL (Fin n) L => (g : Matrix (Fin n) (Fin n) L) i i) hs
  simp [coe_diagGL, Matrix.GeneralLinearGroup.coe_scalar] at this
  exact Units.ext this.symm

private def expVec {G : Type*} [CommGroup G] (m : ℕ) (c : Fin 4 → G) : Fin (5 + m) → G :=
  Fin.append (![c 0, c 1, c 2, c 3, (c 0 * c 1 * c 2 * c 3)⁻¹] : Fin 5 → G) (fun _ => 1)

private theorem expVec_mul {G : Type*} [CommGroup G] (m : ℕ) (c c' : Fin 4 → G) :
    expVec m (c * c') = expVec m c * expVec m c' := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · fin_cases j <;> simp [expVec, mul_comm, mul_left_comm, mul_assoc, mul_inv]
  · simp [expVec]

private theorem prod_expVec {G : Type*} [CommGroup G] (m : ℕ) (c : Fin 4 → G) :
    ∏ i, expVec m c i = 1 := by
  rw [Fin.prod_univ_add]
  simp [expVec, Fin.prod_univ_five]

private theorem expVec_castAdd {G : Type*} [CommGroup G] (m : ℕ) (c : Fin 4 → G) (j : Fin 4) :
    expVec m c (Fin.castAdd m j.castSucc) = c j := by
  fin_cases j <;> simp [expVec]

private theorem expVec_natAdd {G : Type*} [CommGroup G] (m : ℕ) (c : Fin 4 → G) (j : Fin m) :
    expVec m c (Fin.natAdd 5 j) = 1 := by
  simp [expVec]

theorem exists_elemAbelian_four_projDiag {L : Type} [Field L] [Finite L] {n p : ℕ} (hp : p.Prime)
    (hn : 5 ≤ n) (hnp : 6 ≤ n ∨ ¬ p ∣ n) {ζ : Lˣ} (hζ : orderOf ζ = p)
    (H : Subgroup (GL (Fin n) L))
    (hH : ∀ u : Fin n → Lˣ, (∀ i, u i ∈ Subgroup.zpowers ζ) → (∀ i : Fin n, 5 ≤ i.val → u i = 1) →
      ∏ i, u i = 1 → diagGL n u ∈ H) :
    ∃ E : Subgroup (StatedProj H), IsElemAbelian p E ∧ Nat.card E = p ^ 4 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 5 + m := ⟨n - 5, by omega⟩
  set Z : Subgroup Lˣ := Subgroup.zpowers ζ with hZdef
  have hZcard : Nat.card Z = p := by rw [hZdef, Nat.card_zpowers, hζ]
  have hZpow : ∀ x : Z, x ^ p = 1 := fun x => by rw [← hZcard]; exact pow_card_eq_one'
  let u : (Fin 4 → Z) → Fin (5 + m) → Lˣ := fun c i => ((expVec (G := Z) m c i : Z) : Lˣ)
  have hu_mem : ∀ c : Fin 4 → Z, diagGL (5 + m) (u c) ∈ H := by
    intro c
    refine hH _ (fun i => (expVec m c i).2) ?_ ?_
    · intro i hi
      induction i using Fin.addCases with
      | left j => exact absurd hi (by simp)
      | right j => simp [u, expVec_natAdd]
    · have h2 := congrArg (fun z : Z => (z : Lˣ)) (prod_expVec m c)
      simpa [u, Subgroup.coe_prod] using h2
  let ψ : (Fin 4 → Z) →* H :=
    MonoidHom.mk' (fun c => ⟨diagGL (5 + m) (u c), hu_mem c⟩) (fun c c' => by
      apply Subtype.ext
      show diagGL (5 + m) (u (c * c')) = diagGL (5 + m) (u c) * diagGL (5 + m) (u c')
      rw [← map_mul]
      congr 1
      funext i
      simp [u, expVec_mul])
  let θ : (Fin 4 → Z) →* StatedProj H := (QuotientGroup.mk' _).comp ψ
  have hθinj : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro c hc
    have h1 : ψ c ∈ (StatedScalars (Fin (5 + m)) L).subgroupOf H := (QuotientGroup.eq_one_iff _).1 hc
    have h2 : diagGL (5 + m) (u c) ∈ StatedScalars (Fin (5 + m)) L := h1
    obtain ⟨s, hs⟩ := diagGL_mem_scalars h2
    have hsZ : s ∈ Z := hs (Fin.castAdd m 0) ▸ (expVec m c (Fin.castAdd m 0)).2
    have hall : ∀ i, expVec m c i = ⟨s, hsZ⟩ := fun i => Subtype.ext (hs i)
    have hs1 : (⟨s, hsZ⟩ : Z) = 1 := by
      rcases hnp with h6 | hnd
      · have := hall (Fin.natAdd 5 ⟨0, by omega⟩)
        rw [expVec_natAdd] at this
        exact this.symm
      · have h3 : (⟨s, hsZ⟩ : Z) ^ (5 + m) = 1 := by
          have := prod_expVec m c
          simpa [hall, Finset.prod_const] using this
        have h4 : (⟨s, hsZ⟩ : Z) ^ p = 1 := hZpow _
        have hcop : Nat.Coprime p (5 + m) := (Nat.Prime.coprime_iff_not_dvd hp).2 hnd
        have h5 : (⟨s, hsZ⟩ : Z) ^ p.gcd (5 + m) = 1 := pow_gcd_eq_one.2 ⟨h4, h3⟩
        rwa [hcop.gcd_eq_one, pow_one] at h5
    funext j
    have := hall (Fin.castAdd m j.castSucc)
    rw [expVec_castAdd, hs1] at this
    simpa using this
  refine ⟨θ.range, ⟨inferInstance, ?_⟩, ?_⟩
  · rintro _ ⟨c, rfl⟩
    rw [← map_pow]
    have : c ^ p = 1 := by funext i; simp [hZpow]
    rw [this, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hθinj).toEquiv, Nat.card_pi]
    simp [hZcard]

open scoped commutatorElement

private theorem comm_permGL_diagGL {L : Type} [Field L] (n : ℕ) (σ : Equiv.Perm (Fin n))
    (u : Fin n → Lˣ) :
    ⁅(permGL n σ : GL (Fin n) L), (diagGL n u : GL (Fin n) L)⁆ =
      diagGL n (fun i => u (σ⁻¹ i) * (u i)⁻¹) := by
  rw [commutatorElement_def, permGL_mul_diagGL_mul_inv, ← map_inv, ← map_mul]
  rfl

private noncomputable def torus5 {L : Type} [Field L] (ζ : Lˣ) : Subgroup (GL (Fin 5) L) :=
  Subgroup.map (diagGL 5) (Subgroup.pi Set.univ fun _ => Subgroup.zpowers ζ)

private theorem diagGL_mem_torus5 {L : Type} [Field L] {ζ : Lˣ} {u : Fin 5 → Lˣ}
    (hu : ∀ i, u i ∈ Subgroup.zpowers ζ) : (diagGL 5 u : GL (Fin 5) L) ∈ torus5 ζ :=
  Subgroup.mem_map.2 ⟨u, (Subgroup.mem_pi _).2 (fun i _ => hu i), rfl⟩

private theorem zpowers_pow_five {L : Type} [Field L] {ζ : Lˣ} (hζ : orderOf ζ = 5) {x : Lˣ}
    (hx : x ∈ Subgroup.zpowers ζ) : x ^ 5 = 1 := by
  have hcard : Nat.card (Subgroup.zpowers ζ) = 5 := by rw [Nat.card_zpowers, hζ]
  have h := pow_card_eq_one' (G := Subgroup.zpowers ζ) (x := ⟨x, hx⟩)
  rw [hcard] at h
  simpa using congrArg Subtype.val h

private theorem pow_five_of_mem_torus5 {L : Type} [Field L] {ζ : Lˣ} (hζ : orderOf ζ = 5)
    {g : GL (Fin 5) L} (hg : g ∈ torus5 ζ) : g ^ 5 = 1 := by
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hg
  rw [← map_pow]
  have : u ^ 5 = 1 := by
    funext i
    exact zpowers_pow_five hζ ((Subgroup.mem_pi _).1 hu i (Set.mem_univ i))
  rw [this, map_one]

private theorem rot_mem_normalizer_torus5 {L : Type} [Field L] {ζ : Lˣ} (σ : Equiv.Perm (Fin 5)) :
    (permGL 5 σ : GL (Fin 5) L) ∈ Subgroup.normalizer (torus5 ζ : Set (GL (Fin 5) L)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hh
    rw [permGL_mul_diagGL_mul_inv]
    exact diagGL_mem_torus5 (fun i => (Subgroup.mem_pi _).1 hu (σ⁻¹ i) (Set.mem_univ _))
  · intro hh
    obtain ⟨u, hu, hu'⟩ := Subgroup.mem_map.1 hh
    have : h = permGL 5 σ⁻¹ * diagGL 5 u * (permGL 5 σ⁻¹)⁻¹ := by
      rw [hu', map_inv, inv_inv]
      group
    rw [this, permGL_mul_diagGL_mul_inv]
    exact diagGL_mem_torus5 (fun i => (Subgroup.mem_pi _).1 hu _ (Set.mem_univ _))

private theorem isPGroup_torus5_sup {L : Type} [Field L] {ζ : Lˣ} (hζ : orderOf ζ = 5) :
    IsPGroup 5 ↥(torus5 ζ ⊔ Subgroup.zpowers (permGL 5 (finRotate 5) : GL (Fin 5) L)) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hT : IsPGroup 5 ↥(torus5 ζ : Subgroup (GL (Fin 5) L)) := by
    intro x
    exact ⟨1, by apply Subtype.ext; simpa using pow_five_of_mem_torus5 hζ x.2⟩
  have hC : IsPGroup 5 ↥(Subgroup.zpowers (permGL 5 (finRotate 5) : GL (Fin 5) L)) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers, pow_one]
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow]
    have : (finRotate 5) ^ 5 = 1 := by decide
    rw [this, map_one]
  exact IsPGroup.to_sup_of_normal_left' hT hC (Subgroup.zpowers_le.2 (rot_mem_normalizer_torus5 _))

private theorem mk_eq_one_iff {L : Type} [Field L] {n : ℕ} (H : Subgroup (GL (Fin n) L)) (g : H) :
    (QuotientGroup.mk' ((StatedScalars (Fin n) L).subgroupOf H) g = 1) ↔
      (g : GL (Fin n) L) ∈ StatedScalars (Fin n) L :=
  (QuotientGroup.eq_one_iff g).trans Subgroup.mem_subgroupOf

theorem exists_not_cyclic_derived_projFive {L : Type} [Field L] [Finite L] {ζ : Lˣ}
    (hζ : orderOf ζ = 5) (H : Subgroup (GL (Fin 5) L))
    (hd : diagGL 5 ![ζ, ζ⁻¹, 1, 1, 1] ∈ H) (hc : permGL 5 (finRotate 5) ∈ H) :
    ∃ U : Subgroup (StatedProj H), IsPGroup 5 U ∧ ¬ IsCyclic ↥⁅U, U⁆ := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hv : ∀ i, (![ζ, ζ⁻¹, 1, 1, 1] : Fin 5 → Lˣ) i ∈ Subgroup.zpowers ζ := by
    intro i
    fin_cases i
    · exact Subgroup.mem_zpowers ζ
    · exact Subgroup.inv_mem _ (Subgroup.mem_zpowers ζ)
    · exact Subgroup.one_mem _
    · exact Subgroup.one_mem _
    · exact Subgroup.one_mem _
  let π : H →* StatedProj H := QuotientGroup.mk' _
  let c' : H := ⟨permGL 5 (finRotate 5), hc⟩
  let d' : H := ⟨diagGL 5 ![ζ, ζ⁻¹, 1, 1, 1], hd⟩
  let U : Subgroup (StatedProj H) := Subgroup.closure {π c', π d'}
  have hcU : π c' ∈ U := Subgroup.subset_closure (by simp)
  have hdU : π d' ∈ U := Subgroup.subset_closure (by simp)
  refine ⟨U, ?_, ?_⟩
  · have hP := (isPGroup_torus5_sup (L := L) hζ).comap_subtype (K := H)
    have hP' := hP.map π
    have hle : U ≤ Subgroup.map π (Subgroup.comap H.subtype
        (torus5 ζ ⊔ Subgroup.zpowers (permGL 5 (finRotate 5) : GL (Fin 5) L))) := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact ⟨c', Subgroup.mem_comap.2 (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)), rfl⟩
      · exact ⟨d', Subgroup.mem_comap.2 (Subgroup.mem_sup_left (diagGL_mem_torus5 hv)), rfl⟩
    exact hP'.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  · intro hcyc
    have hcomm1 : ⁅π c', π d'⁆ ∈ ⁅U, U⁆ := Subgroup.commutator_mem_commutator hcU hdU
    have hU1 : ⁅π c', π d'⁆ ∈ U := by
      rw [commutatorElement_def]
      exact U.mul_mem (U.mul_mem (U.mul_mem hcU hdU) (U.inv_mem hcU)) (U.inv_mem hdU)
    have hcomm2 : ⁅π c', ⁅π c', π d'⁆⁆ ∈ ⁅U, U⁆ := Subgroup.commutator_mem_commutator hcU hU1
    let v : Fin 5 → Lˣ := ![ζ, ζ⁻¹, 1, 1, 1]
    let a : Fin 5 → Lˣ := fun i => v ((finRotate 5)⁻¹ i) * (v i)⁻¹
    let b : Fin 5 → Lˣ := fun i => a ((finRotate 5)⁻¹ i) * (a i)⁻¹
    have hav : ∀ i, a i ∈ Subgroup.zpowers ζ := fun i =>
      Subgroup.mul_mem _ (hv _) (Subgroup.inv_mem _ (hv _))
    have hbv : ∀ i, b i ∈ Subgroup.zpowers ζ := fun i =>
      Subgroup.mul_mem _ (hav _) (Subgroup.inv_mem _ (hav _))
    have ζne : ζ⁻¹ ≠ 1 := by
      intro h
      have h1 : ζ = 1 := inv_eq_one.1 h
      rw [h1, orderOf_one] at hζ
      omega
    have r0 : (finRotate 5)⁻¹ 0 = 4 := by decide
    have r2 : (finRotate 5)⁻¹ 2 = 1 := by decide
    have r3 : (finRotate 5)⁻¹ 3 = 2 := by decide
    have r4 : (finRotate 5)⁻¹ 4 = 3 := by decide
    have ha0 : a 0 = ζ⁻¹ := by simp [a, v, r0]
    have ha2 : a 2 = ζ⁻¹ := by simp [a, v, r2]
    have ha3 : a 3 = 1 := by simp [a, v, r3]
    have ha4 : a 4 = 1 := by simp [a, v, r4]
    have hb3 : b 3 = ζ⁻¹ := by simp [b, r3, ha2, ha3]
    have hb4 : b 4 = 1 := by simp [b, r4, ha3, ha4]
    have hax : ((⁅c', d'⁆ : H) : GL (Fin 5) L) = diagGL 5 a :=
      comm_permGL_diagGL 5 (finRotate 5) v
    have hbx : ((⁅c', ⁅c', d'⁆⁆ : H) : GL (Fin 5) L) = diagGL 5 b := by
      have h1 : ((⁅c', ⁅c', d'⁆⁆ : H) : GL (Fin 5) L) =
          ⁅(c' : GL (Fin 5) L), ((⁅c', d'⁆ : H) : GL (Fin 5) L)⁆ := rfl
      rw [h1, hax]
      exact comm_permGL_diagGL 5 (finRotate 5) a
    have hπ1 : ⁅π c', π d'⁆ = π ⁅c', d'⁆ := (map_commutatorElement π c' d').symm
    have hπ2 : ⁅π c', ⁅π c', π d'⁆⁆ = π ⁅c', ⁅c', d'⁆⁆ := by
      rw [hπ1, ← map_commutatorElement]
    have hx5 : (⁅π c', π d'⁆) ^ 5 = 1 := by
      rw [hπ1, ← map_pow]
      have : (⁅c', d'⁆ : H) ^ 5 = 1 := by
        apply Subtype.ext
        show ((⁅c', d'⁆ : H) : GL (Fin 5) L) ^ 5 = 1
        rw [hax]
        exact pow_five_of_mem_torus5 hζ (diagGL_mem_torus5 hav)
      rw [this, map_one]
    have hy5 : (⁅π c', ⁅π c', π d'⁆⁆) ^ 5 = 1 := by
      rw [hπ2, ← map_pow]
      have : (⁅c', ⁅c', d'⁆⁆ : H) ^ 5 = 1 := by
        apply Subtype.ext
        show ((⁅c', ⁅c', d'⁆⁆ : H) : GL (Fin 5) L) ^ 5 = 1
        rw [hbx]
        exact pow_five_of_mem_torus5 hζ (diagGL_mem_torus5 hbv)
      rw [this, map_one]
    have hx1 : ⁅π c', π d'⁆ ≠ 1 := by
      rw [hπ1]
      intro h
      have h1 := (mk_eq_one_iff H _).1 h
      rw [hax] at h1
      obtain ⟨s, hs⟩ := diagGL_mem_scalars h1
      have e0 := hs 0
      have e3 := hs 3
      rw [ha0] at e0
      rw [ha3] at e3
      exact ζne (e0.trans e3.symm)
    have hxy : ∀ k : ℤ, (⁅π c', π d'⁆) ^ k ≠ ⁅π c', ⁅π c', π d'⁆⁆ := by
      intro k hk
      rw [hπ2, hπ1, ← map_zpow] at hk
      have h1 := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 hk)
      have h2 : ((((⁅c', d'⁆ : H) ^ k)⁻¹ * ⁅c', ⁅c', d'⁆⁆ : H) : GL (Fin 5) L) =
          diagGL 5 ((a ^ k)⁻¹ * b) := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow, hax, hbx, ← map_zpow, ← map_inv,
          ← map_mul]
      rw [h2] at h1
      obtain ⟨s, hs⟩ := diagGL_mem_scalars h1
      have e3 := hs 3
      have e4 := hs 4
      simp [ha3, ha4, hb3, hb4] at e3 e4
      exact ζne (e3.trans e4.symm)
    have hy1 : ⁅π c', ⁅π c', π d'⁆⁆ ≠ 1 := by
      intro h
      apply hxy 0
      rw [zpow_zero, h]
    let x : ↥⁅U, U⁆ := ⟨⁅π c', π d'⁆, hcomm1⟩
    let y : ↥⁅U, U⁆ := ⟨⁅π c', ⁅π c', π d'⁆⁆, hcomm2⟩
    have hxo : orderOf x = 5 := by
      rw [show orderOf x = orderOf (⁅π c', π d'⁆) from Subgroup.orderOf_mk _ hcomm1]
      exact orderOf_eq_prime hx5 hx1
    have hyo : orderOf y = 5 := by
      rw [show orderOf y = orderOf (⁅π c', ⁅π c', π d'⁆⁆) from Subgroup.orderOf_mk _ hcomm2]
      exact orderOf_eq_prime hy5 hy1
    have heq : Subgroup.zpowers x = Subgroup.zpowers y := by
      rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers, hxo, hyo]
    have hymem : y ∈ Subgroup.zpowers x := heq ▸ Subgroup.mem_zpowers y
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hymem
    exact hxy k (by simpa [x, y] using congrArg Subtype.val hk)

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
