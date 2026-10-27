module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerActionLie
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerActionN1Common

open scoped Matrix

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerAction

open CFSG.Open (StatedClassicalModel StatedProj StatedSU StatedScalars)
open CFSG.LocalAnalysis.RankThreeTheoremC.NineSubgroup (dglHom coe_dglHom dglHom_unitary)

section Matrices

private noncomputable def permGL (n : ℕ) (F : Type) [Field F] :
    Equiv.Perm (Fin n) →* GL (Fin n) F :=
  (Matrix.permMatrixHom : Equiv.Perm (Fin n) →* Matrix (Fin n) (Fin n) F).toHomUnits

private theorem coe_permGL {n : ℕ} {F : Type} [Field F] (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    ((permGL n F σ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j =
      if i = σ j then 1 else 0 := by
  simp only [permGL, MonoidHom.coe_toHomUnits, Matrix.permMatrixHom_apply, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, Equiv.Perm.inv_eq_iff_eq]

private theorem det_permGL {n : ℕ} {F : Type} [Field F] {σ : Equiv.Perm (Fin n)}
    (hσ : Equiv.Perm.sign σ = 1) :
    ((permGL n F σ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1 := by
  simp [permGL, Matrix.det_permutation, hσ]

private theorem permGL_unitary {n q : ℕ} {F : Type} [Field F] (hq : q ≠ 0)
    (σ : Equiv.Perm (Fin n)) :
    (((permGL n F σ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map (· ^ q))ᵀ *
      ((permGL n F σ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
  ext i k
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, coe_permGL, ite_pow,
    one_pow, zero_pow hq, ite_mul, one_mul, zero_mul, Matrix.one_apply, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, EmbeddingLike.apply_eq_iff_eq]

private theorem sign_eq_one_of_pow_eq_one {n p : ℕ} (hp : Odd p) {σ : Equiv.Perm (Fin n)}
    (h : σ ^ p = 1) : Equiv.Perm.sign σ = 1 := by
  have h1 : Equiv.Perm.sign σ ^ p = 1 := by rw [← map_pow, h, map_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h' | h'
  · exact h'
  · rw [h', hp.neg_one_pow] at h1
    exact absurd h1 (by decide)

private theorem permGL_mul_dglHom {n : ℕ} {F : Type} [Field F] (σ : Equiv.Perm (Fin n))
    (t : Fin n → Fˣ) :
    permGL n F σ * dglHom n t = dglHom n (fun i => t (σ⁻¹ i)) * permGL n F σ := by
  refine Units.ext ?_
  ext i j
  rw [Units.val_mul, Units.val_mul, coe_dglHom, coe_dglHom, Matrix.mul_diagonal,
    Matrix.diagonal_mul, coe_permGL]
  by_cases h : i = σ j
  · subst h
    simp
  · simp [h]

private noncomputable def diagGroup (n : ℕ) (F : Type) [Field F] (T : Subgroup Fˣ) :
    Subgroup (GL (Fin n) F) :=
  (Subgroup.pi Set.univ fun _ : Fin n => T).map (dglHom n)

private theorem mem_diagGroup {n : ℕ} {F : Type} [Field F] {T : Subgroup Fˣ}
    {g : GL (Fin n) F} :
    g ∈ diagGroup n F T ↔ ∃ t : Fin n → Fˣ, (∀ i, t i ∈ T) ∧ dglHom n t = g := by
  simp [diagGroup, Subgroup.mem_map, Subgroup.mem_pi]

private theorem permGL_conj_mem {n : ℕ} {F : Type} [Field F] {T : Subgroup Fˣ}
    (σ : Equiv.Perm (Fin n)) {g : GL (Fin n) F} (hg : g ∈ diagGroup n F T) :
    permGL n F σ * g * (permGL n F σ)⁻¹ ∈ diagGroup n F T := by
  obtain ⟨t, ht, rfl⟩ := mem_diagGroup.1 hg
  rw [mul_inv_eq_iff_eq_mul.2 (permGL_mul_dglHom σ t)]
  exact mem_diagGroup.2 ⟨_, fun i => ht _, rfl⟩

private theorem permGL_mem_normalizer {n : ℕ} {F : Type} [Field F] (T : Subgroup Fˣ)
    (σ : Equiv.Perm (Fin n)) :
    permGL n F σ ∈ Subgroup.normalizer (diagGroup n F T : Set (GL (Fin n) F)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨permGL_conj_mem σ, fun h => ?_⟩
  have h2 := permGL_conj_mem σ⁻¹ h
  have e : permGL n F σ⁻¹ * (permGL n F σ * g * (permGL n F σ)⁻¹) * (permGL n F σ⁻¹)⁻¹ = g := by
    rw [map_inv]
    group
  rwa [e] at h2

private theorem isPGroup_diagGroup {n : ℕ} {F : Type} [Field F] {T : Subgroup Fˣ} {p a : ℕ}
    (hT : ∀ t ∈ T, t ^ p ^ a = 1) : IsPGroup p (diagGroup n F T) := by
  rintro ⟨g, hg⟩
  obtain ⟨t, ht, rfl⟩ := mem_diagGroup.1 hg
  refine ⟨a, Subtype.ext ?_⟩
  have h1 : t ^ p ^ a = 1 := funext fun i => hT _ (ht i)
  change (dglHom n t) ^ p ^ a = 1
  rw [← map_pow, h1, map_one]

private theorem isPGroup_zpowers {G : Type*} [Group G] {p : ℕ} {b : G} (hb : b ^ p = 1) :
    IsPGroup p (Subgroup.zpowers b) := by
  rintro ⟨_, k, rfl⟩
  refine ⟨1, Subtype.ext ?_⟩
  simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb, one_zpow]

private def twoPoint {n : ℕ} {G : Type*} [Group G] (z : G) (i₀ i₁ : Fin n) : Fin n → G :=
  fun i => if i = i₀ then z else if i = i₁ then z⁻¹ else 1

private theorem twoPoint_fst {n : ℕ} {G : Type*} [Group G] (z : G) (i₀ i₁ : Fin n) :
    twoPoint z i₀ i₁ i₀ = z := by simp [twoPoint]

private theorem twoPoint_snd {n : ℕ} {G : Type*} [Group G] (z : G) {i₀ i₁ : Fin n}
    (h : i₁ ≠ i₀) : twoPoint z i₀ i₁ i₁ = z⁻¹ := by simp [twoPoint, h]

private theorem twoPoint_of_ne {n : ℕ} {G : Type*} [Group G] (z : G) {i₀ i₁ j : Fin n}
    (h0 : j ≠ i₀) (h1 : j ≠ i₁) : twoPoint z i₀ i₁ j = 1 := by simp [twoPoint, h0, h1]

private theorem prod_twoPoint {n : ℕ} {F : Type} [Field F] (z : Fˣ) {i₀ i₁ : Fin n}
    (h : i₁ ≠ i₀) : ∏ i, ((twoPoint z i₀ i₁ i : Fˣ) : F) = 1 := by
  rw [Finset.prod_eq_mul i₀ i₁ h.symm]
  · rw [twoPoint_fst, twoPoint_snd z h]
    simp
  · intro j _ hj
    rw [twoPoint_of_ne z hj.1 hj.2]
    simp
  · simp
  · simp

private theorem dglHom_mem_SU {n q : ℕ} {F : Type} [Field F] (hq : q ≠ 0) {δ : Fin n → Fˣ}
    (hdet : ∏ i, ((δ i : Fˣ) : F) = 1) (hδ : ∀ i, (δ i) ^ (q + 1) = 1) :
    dglHom n δ ∈ StatedSU n q F :=
  Subgroup.subset_closure
    ⟨by rw [coe_dglHom, Matrix.det_diagonal]; exact hdet,
      dglHom_unitary hq δ fun i => by rw [← Units.val_pow_eq_pow_val, hδ i, Units.val_one]⟩

private theorem permGL_mem_SU {n q p : ℕ} {F : Type} [Field F] (hq : q ≠ 0) (hp : Odd p)
    {σ : Equiv.Perm (Fin n)} (hσ : σ ^ p = 1) : permGL n F σ ∈ StatedSU n q F :=
  Subgroup.subset_closure ⟨det_permGL (sign_eq_one_of_pow_eq_one hp hσ), permGL_unitary hq σ⟩

private theorem entry_of_comm {n : ℕ} {F : Type} [Field F] (σ : Equiv.Perm (Fin n))
    (δ : Fin n → Fˣ) (c : Fˣ)
    (h : dglHom n δ * permGL n F σ * Matrix.GeneralLinearGroup.scalar (Fin n) c =
      permGL n F σ * dglHom n δ) (j : Fin n) : δ (σ j) * c = δ j := by
  have h1 := congrArg (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F) (σ j) j) h
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, coe_dglHom, Matrix.scalar_apply,
    Matrix.mul_diagonal, Matrix.diagonal_mul, coe_permGL, if_true] at h1
  exact Units.ext (by simpa using h1)

end Matrices

private theorem exists_pSubgroup_noncomm {K : Type} [Group K] {ι : Type} [Fintype ι]
    [DecidableEq ι] {F : Type} [Field F] {H : Subgroup (GL ι F)} (e : K ≃* StatedProj H)
    {p : ℕ} {Q : Subgroup (GL ι F)} (hQ : IsPGroup p Q) {x y : GL ι F} (hxQ : x ∈ Q)
    (hyQ : y ∈ Q) (hxH : x ∈ H) (hyH : y ∈ H)
    (hnc : ∀ c : Fˣ, x * y * Matrix.GeneralLinearGroup.scalar ι c ≠ y * x) :
    ∃ (R : Subgroup K) (a b : K), IsPGroup p R ∧ a ∈ R ∧ b ∈ R ∧ a * b ≠ b * a := by
  let π : H →* StatedProj H := QuotientGroup.mk' ((StatedScalars ι F).subgroupOf H)
  refine ⟨((Q.subgroupOf H).map π).comap e.toMonoidHom, e.symm (π ⟨x, hxH⟩),
    e.symm (π ⟨y, hyH⟩),
    ((hQ.comap_subtype).map π).comap_of_injective e.toMonoidHom e.injective, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_comap]
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_map_of_mem π hxQ
  · rw [Subgroup.mem_comap]
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_map_of_mem π hyQ
  · intro hab
    have h1 := congrArg e hab
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h1
    rw [← map_mul, ← map_mul] at h1
    have h2 := QuotientGroup.eq.1 h1
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 h2
    refine hnc c ?_
    have hc' : Matrix.GeneralLinearGroup.scalar ι c = (x * y)⁻¹ * (y * x) := hc
    rw [hc', mul_inv_cancel_left]

private theorem exists_noncomm_psu {K : Type} [Group K] {n q p a : ℕ} {F : Type} [Field F]
    [Finite F] (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ≤ n) (hn : 3 ≤ n) (hq : q ≠ 0)
    {z : Fˣ} (hz1 : z ≠ 1) (hza : z ^ p ^ a = 1) (hzq : z ^ (q + 1) = 1)
    (hz3 : n = 3 → z ^ 3 ≠ 1) (e : K ≃* StatedProj (StatedSU n q F)) :
    ∃ (R : Subgroup K) (x y : K), IsPGroup p R ∧ x ∈ R ∧ y ∈ R ∧ x * y ≠ y * x := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card' (G := Equiv.Perm (Fin n)) p (by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    exact Nat.dvd_factorial hp.pos hpn)
  have hσp : σ ^ p = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ
    exact hp.one_lt.ne hσ
  obtain ⟨i₀, hi₀⟩ : ∃ i, σ i ≠ i := not_forall.1 fun h => hσ1 (Equiv.ext h)
  obtain ⟨i₁, hi₁⟩ : ∃ i₁, σ i₀ = i₁ := ⟨_, rfl⟩
  have h10 : i₁ ≠ i₀ := hi₁ ▸ hi₀
  have h2 : σ i₁ ≠ i₀ := by
    intro h
    obtain ⟨k, hk⟩ := hpodd
    have hfix : ∀ m : ℕ, (σ ^ (2 * m)) i₀ = i₀ := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        have hsq : (σ ^ 2) i₀ = i₀ := by rw [pow_two, Equiv.Perm.mul_apply, hi₁, h]
        rw [Nat.mul_succ, pow_add, Equiv.Perm.mul_apply, hsq, ih]
    have h3 : (σ ^ p) i₀ = σ i₀ := by
      rw [hk, pow_succ', Equiv.Perm.mul_apply, hfix k]
    rw [hσp, Equiv.Perm.one_apply, hi₁] at h3
    exact h10 h3.symm
  have h21 : σ i₁ ≠ i₁ := fun h => h10 (σ.injective (h.trans hi₁.symm))
  let T : Subgroup Fˣ := (powMonoidHom (p ^ a) : Fˣ →* Fˣ).ker
  have hT : ∀ t ∈ T, t ^ p ^ a = 1 := fun t ht => by simpa [T] using ht
  have hb : (permGL n F σ) ^ p = 1 := by rw [← map_pow, hσp, map_one]
  have hQ : IsPGroup p (diagGroup n F T ⊔ Subgroup.zpowers (permGL n F σ) : Subgroup _) :=
    (isPGroup_diagGroup hT).to_sup_of_normal_left' (isPGroup_zpowers hb)
      (Subgroup.zpowers_le.2 (permGL_mem_normalizer T σ))
  have hδT : ∀ i, twoPoint z i₀ i₁ i ∈ T := by
    intro i
    simp only [twoPoint]
    split_ifs
    · simpa [T] using hza
    · simpa [T, inv_pow] using hza
    · exact one_mem _
  have hδq : ∀ i, (twoPoint z i₀ i₁ i) ^ (q + 1) = 1 := by
    intro i
    simp only [twoPoint]
    split_ifs <;> simp [inv_pow, hzq]
  have hdU : dglHom n (twoPoint z i₀ i₁) ∈ StatedSU n q F :=
    dglHom_mem_SU hq (prod_twoPoint z h10) hδq
  have hbU : permGL n F σ ∈ StatedSU n q F := permGL_mem_SU hq hpodd hσp
  refine exists_pSubgroup_noncomm e hQ (x := dglHom n (twoPoint z i₀ i₁))
    (y := permGL n F σ) (Subgroup.mem_sup_left (mem_diagGroup.2 ⟨_, hδT, rfl⟩))
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) hdU hbU ?_
  intro c hc
  have hj := entry_of_comm σ (twoPoint z i₀ i₁) c hc
  have e1 : z⁻¹ * c = z := by
    have h := hj i₀
    rwa [hi₁, twoPoint_snd z h10, twoPoint_fst] at h
  have e2 : c = z⁻¹ := by
    have h := hj i₁
    rwa [twoPoint_of_ne z h2 h21, twoPoint_snd z h10, one_mul] at h
  rcases (show n = 3 ∨ 4 ≤ n by omega) with hn3 | hn4
  · apply hz3 hn3
    rw [e2] at e1
    calc z ^ 3 = z ^ 2 * z := by group
      _ = z ^ 2 * (z⁻¹ * z⁻¹) := by rw [e1]
      _ = 1 := by group
  · obtain ⟨j, -, hj'⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({i₀, i₁, σ.symm i₀} : Finset (Fin n))) (t := Finset.univ)
      (by
        calc _ ≤ 3 := Finset.card_le_three
          _ < n := lt_of_lt_of_le (by norm_num) hn4
          _ = _ := by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj'
    obtain ⟨hj0, hj1, hj2⟩ := hj'
    have hσj0 : σ j ≠ i₀ := fun h => hj2 (by rw [← h]; simp)
    have hσj1 : σ j ≠ i₁ := fun h => hj0 (σ.injective (h.trans hi₁.symm))
    have h := hj j
    rw [twoPoint_of_ne z hj0 hj1, twoPoint_of_ne z hσj0 hσj1, one_mul] at h
    rw [e2] at h
    exact hz1 (inv_eq_one.1 h)

theorem n1PSU_holds : N1PSU := by
  intro K _ _ n ℓ f hmodel p hp hp2 hpn hpq hspec S hS hSidx
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨hℓ, -, hn3, -⟩, F, instF, instFin, hF, ⟨e⟩⟩ := hmodel
  have hq0 : ℓ ^ f ≠ 0 := (pow_pos hℓ.pos f).ne'
  have hpn' : p ≤ n := Nat.le_of_dvd (by omega) hpn
  have hcard : (ℓ ^ f + 1) ∣ Nat.card Fˣ := by
    rw [Nat.card_units, hF]
    have := Nat.sq_sub_sq (ℓ ^ f) 1
    rw [one_pow] at this
    rw [this]
    exact Dvd.intro _ rfl
  have hpcard : p ∣ Nat.card Fˣ := hpq.trans hcard
  obtain ⟨R, x, y, hR, hx, hy, hxy⟩ :
      ∃ (R : Subgroup K) (x y : K), IsPGroup p R ∧ x ∈ R ∧ y ∈ R ∧ x * y ≠ y * x := by
    by_cases h3 : n = 3
    · subst h3
      have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hpn
      subst hp3
      have h9 : 9 ∣ ℓ ^ f + 1 := by
        by_contra h9
        exact hspec ⟨rfl, rfl, h9⟩
      obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
      have hz9 : orderOf (g ^ (orderOf g / 9)) = 9 :=
        orderOf_pow_orderOf_div (by rw [hg]; exact Nat.card_pos.ne')
          (by rw [hg]; exact h9.trans hcard)
      refine exists_noncomm_psu (a := 2) hp hp2 hpn' hn3 hq0 (z := g ^ (orderOf g / 9))
        ?_ ?_ ?_ ?_ e
      · intro h
        rw [h, orderOf_one] at hz9
        omega
      · have := pow_orderOf_eq_one (g ^ (orderOf g / 9))
        rw [hz9] at this
        simpa using this
      · exact orderOf_dvd_iff_pow_eq_one.1 (by rw [hz9]; exact h9)
      · intro _ h
        have := orderOf_dvd_iff_pow_eq_one.2 h
        rw [hz9] at this
        omega
    · obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hpcard
      refine exists_noncomm_psu (a := 1) hp hp2 hpn' (by omega) hq0 (z := z) ?_ ?_ ?_
        (fun h => absurd h h3) e
      · intro h
        rw [h, orderOf_one] at hz
        exact hp.one_lt.ne hz
      · simpa using orderOf_dvd_iff_pow_eq_one.1 (dvd_of_eq hz)
      · exact orderOf_dvd_iff_pow_eq_one.1 (by rw [hz]; exact hpq)
  exact not_isMulCommutative_of_noncomm_pSubgroup hR hx hy hxy hS hSidx

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerAction
