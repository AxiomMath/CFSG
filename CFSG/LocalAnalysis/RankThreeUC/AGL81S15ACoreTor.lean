module

public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.ACore

open CFSG.Open CFSG.SectionRank CFSG.SectionRank.OddCover

section Cyclic

variable {C : Type} [CommGroup C] [Finite C] {r : ℕ}

theorem le_card_pow_ker [hr : Fact r.Prime] (h : r ∣ Nat.card C) :
    r ≤ Nat.card (powMonoidHom r : C →* C).ker := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := C) r h
  have hxk : x ∈ (powMonoidHom r : C →* C).ker := by
    rw [MonoidHom.mem_ker, powMonoidHom_apply, ← hx]
    exact pow_orderOf_eq_one x
  have : Nat.card (Subgroup.zpowers x) ≤ Nat.card (powMonoidHom r : C →* C).ker := by
    apply Subgroup.card_le_of_le
    rw [Subgroup.zpowers_le]
    exact hxk
  rwa [Nat.card_zpowers, hx] at this

theorem card_pow_ker_le [IsCyclic C] (hr : 0 < r) :
    Nat.card (powMonoidHom r : C →* C).ker ≤ r := by
  classical
  haveI := Fintype.ofFinite C
  have h := IsCyclic.card_pow_eq_one_le (α := C) hr
  have e : Nat.card (powMonoidHom r : C →* C).ker =
      (Finset.univ.filter (fun a : C => a ^ r = 1)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rfl
  rw [e]
  exact h

theorem card_le_mul_card_pow_range [hr : Fact r.Prime] [IsCyclic C] :
    Nat.card C ≤ r * Nat.card (powMonoidHom r : C →* C).range := by
  have h1 := Subgroup.card_ker_mul_card_range (powMonoidHom r : C →* C)
  have h2 := card_pow_ker_le (C := C) hr.out.pos
  calc Nat.card C = Nat.card (powMonoidHom r : C →* C).ker *
        Nat.card (powMonoidHom r : C →* C).range := h1.symm
    _ ≤ r * Nat.card (powMonoidHom r : C →* C).range := Nat.mul_le_mul_right _ h2

theorem le_pow_range_of_ne_top [hr : Fact r.Prime] [hC : IsCyclic C] (hCr : IsPGroup r C)
    {H : Subgroup C} (hH : H ≠ ⊤) :
    H ≤ (powMonoidHom r : C →* C).range := by
  intro z hz
  by_contra hzr
  apply hH
  obtain ⟨g, hg⟩ := hC.exists_generator
  obtain ⟨n, hn⟩ : ∃ n : ℕ, g ^ n = z := by
    have := hg z
    rw [Subgroup.mem_zpowers_iff] at this
    obtain ⟨k, hk⟩ := this
    refine ⟨(k % (orderOf g : ℤ)).toNat, ?_⟩
    rw [← hk, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by
      exact_mod_cast (orderOf_pos g).ne')), zpow_mod_orderOf]
  have hnr : ¬ r ∣ n := by
    rintro ⟨k, rfl⟩
    exact hzr ⟨g ^ k, by rw [powMonoidHom_apply, ← pow_mul, mul_comm, hn]⟩
  have hord : orderOf g = Nat.card C := orderOf_eq_card_of_forall_mem_zpowers hg
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hCr
  have hcop : Nat.Coprime (orderOf g) n := by
    rw [hord, ha]
    exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hr.out).2 hnr)
  have hzord : orderOf z = orderOf g := by
    rw [← hn, orderOf_pow' _ (by
      rintro rfl
      simp at hnr), Nat.Coprime.gcd_eq_one hcop, Nat.div_one]
  have hcard : Nat.card (Subgroup.zpowers z) = Nat.card C := by
    rw [Nat.card_zpowers, hzord, hord]
  have htop : Subgroup.zpowers z = ⊤ := Subgroup.eq_top_of_card_eq _ hcard
  rw [eq_top_iff, ← htop, Subgroup.zpowers_le]
  exact hz

end Cyclic

section Omega

variable {C : Type} [CommGroup C] {r k : ℕ}

@[expose] def omegaSub (r k : ℕ) (C₀ : Subgroup C) : Subgroup (Fin (k + 1) → C) where
  carrier := {t | ∏ i, t i = 1 ∧ ∃ z ∈ C₀, ∀ i, t i ^ r = z}
  mul_mem' := by
    rintro s t ⟨hs, z, hz, hsz⟩ ⟨ht, w, hw, htw⟩
    refine ⟨by simp [Finset.prod_mul_distrib, hs, ht], z * w, C₀.mul_mem hz hw, fun i => ?_⟩
    simp [mul_pow, hsz i, htw i]
  one_mem' := ⟨by simp, 1, C₀.one_mem, fun i => by simp⟩
  inv_mem' := by
    rintro t ⟨ht, z, hz, htz⟩
    exact ⟨by simp [Finset.prod_inv_distrib, ht], z⁻¹, C₀.inv_mem hz,
      fun i => by simp [inv_pow, htz i]⟩

@[expose] def omegaPsi (r k : ℕ) (C₀ : Subgroup C) : omegaSub r k C₀ →* C :=
  (powMonoidHom r : C →* C).comp
    ((Pi.evalMonoidHom (fun _ : Fin (k + 1) => C) 0).comp (omegaSub r k C₀).subtype)

theorem omega_pow_eq {C₀ : Subgroup C} {t : Fin (k + 1) → C} (ht : t ∈ omegaSub r k C₀)
    (i : Fin (k + 1)) : t i ^ r = t 0 ^ r := by
  obtain ⟨-, z, -, hz⟩ := ht
  rw [hz i, hz 0]

theorem mem_range_omegaPsi {C₀ : Subgroup C} (hC₀ : ∀ z ∈ C₀, z ^ (k + 1) = 1) {z : C}
    (hz : z ∈ C₀ ⊓ (powMonoidHom r : C →* C).range) : z ∈ (omegaPsi r k C₀).range := by
  obtain ⟨hzC, y, hy⟩ := hz
  rw [powMonoidHom_apply] at hy
  let t : Fin (k + 1) → C := Fin.cons (y ^ k)⁻¹ (fun _ => y)
  have hprod : ∏ i, t i = 1 := by
    rw [Fin.prod_univ_succ]
    simp [t]
  have hpow : ∀ i, t i ^ r = z := by
    refine Fin.cases ?_ (fun j => ?_)
    · have hzk : z ^ k = z⁻¹ := by
        have := hC₀ z hzC
        rw [pow_succ] at this
        exact eq_inv_of_mul_eq_one_left this
      simp only [t, Fin.cons_zero]
      rw [inv_pow, ← pow_mul, mul_comm, pow_mul, hy, hzk, inv_inv]
    · simp [t, hy]
  have htm : t ∈ omegaSub r k C₀ := ⟨hprod, z, hzC, hpow⟩
  exact ⟨⟨t, htm⟩, by simp [omegaPsi, hpow 0]⟩

theorem card_omega_ge [Finite C] {C₀ : Subgroup C} (hC₀ : ∀ z ∈ C₀, z ^ (k + 1) = 1) :
    Nat.card (powMonoidHom r : C →* C).ker ^ k *
        Nat.card ↥(C₀ ⊓ (powMonoidHom r : C →* C).range) ≤ Nat.card (omegaSub r k C₀) := by
  rw [← Subgroup.card_ker_mul_card_range (omegaPsi r k C₀)]
  refine Nat.mul_le_mul ?_ ?_
  ·
    have hx : ∀ (x : Fin k → (powMonoidHom r : C →* C).ker) (i : Fin k), (x i : C) ^ r = 1 :=
      fun x i => by
        have := (x i).2
        rwa [MonoidHom.mem_ker, powMonoidHom_apply] at this
    have hprodr : ∀ x : Fin k → (powMonoidHom r : C →* C).ker,
        ((∏ i, (x i : C))⁻¹) ^ r = 1 := fun x => by
      rw [inv_pow, ← Finset.prod_pow]
      simp [hx x]
    let g : (Fin k → (powMonoidHom r : C →* C).ker) → (omegaPsi r k C₀).ker := fun x =>
      ⟨⟨Fin.cons (∏ i, (x i : C))⁻¹ (fun i => (x i : C)), by
        refine ⟨by rw [Fin.prod_univ_succ]; simp, 1, C₀.one_mem, fun i => ?_⟩
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa only [Fin.cons_zero] using hprodr x
        · simpa only [Fin.cons_succ] using hx x j⟩, by
        rw [MonoidHom.mem_ker]
        simpa [omegaPsi] using hprodr x⟩
    have hg : Function.Injective g := by
      intro x y hxy
      funext i
      apply Subtype.ext
      have := congrArg (fun w : (omegaPsi r k C₀).ker => (w.1 : Fin (k + 1) → C) i.succ) hxy
      simpa [g] using this
    have := Nat.card_le_card_of_injective g hg
    rwa [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin k), Fintype.card_fin] at this
  ·
    exact Subgroup.card_le_of_le (fun z hz => mem_range_omegaPsi hC₀ hz)

end Omega

section Toral

variable {F : Type} [Field F] [Fintype F] {C : Type} [CommGroup C] [Finite C]

omit [Fintype F] in
theorem scalar_eq_diagHom_const (m : ℕ) (u : Fˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin m) u = diagHom m (fun _ => u) := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_scalar, coe_diagHom]
  rfl

open scoped Classical in
theorem toral_lower_bound_succ {r k : ℕ} [hr : Fact r.Prime] [Nontrivial C] (hCc : IsCyclic C)
    (hCr : IsPGroup r C) (e : C →* Fˣ) (he : Function.Injective e)
    (G : Subgroup (GL (Fin (k + 1)) F)) (hGSL : G ≤ StatedSL (k + 1) F)
    (hdiag : ∀ t : Fin (k + 1) → C, ∏ i, t i = 1 → diagHom (k + 1) (fun i => e (t i)) ∈ G)
    (Z : Subgroup (GL (Fin (k + 1)) F)) (hZG : Z ≤ G)
    (hZsc : Z ≤ StatedScalars (Fin (k + 1)) F) [(Z.subgroupOf G).Normal] :
    k - (if ∀ z : C, Matrix.GeneralLinearGroup.scalar (Fin (k + 1)) (e z) ∈ Z then 1 else 0) ≤
      CFSG.Open.pRank r (⊤ : Subgroup (↥G ⧸ Z.subgroupOf G)) := by
  classical
  set C₀ : Subgroup C := Z.comap ((Matrix.GeneralLinearGroup.scalar (Fin (k + 1))).comp e)
    with hC₀def
  have hmemC₀ : ∀ z : C, z ∈ C₀ ↔ Matrix.GeneralLinearGroup.scalar (Fin (k + 1)) (e z) ∈ Z :=
    fun z => Iff.rfl
  have hC₀m : ∀ z ∈ C₀, z ^ (k + 1) = 1 := by
    intro z hz
    have h1 := hGSL (hZG ((hmemC₀ z).1 hz))
    rw [CFSG.Open.StatedAPI.mem_statedSL_iff, scalar_eq_diagHom_const, det_diagHom,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
    apply he
    rw [map_pow, map_one]
    exact Units.ext (by simpa using h1)
  let φ0 : omegaSub r k C₀ →* G :=
    MonoidHom.codRestrict ((diagHom (k + 1)).comp
      ((MonoidHom.compLeft e (Fin (k + 1))).comp (omegaSub r k C₀).subtype)) G
      (fun t => hdiag t t.2.1)
  let φ : omegaSub r k C₀ →* ↥G ⧸ Z.subgroupOf G := (QuotientGroup.mk' (Z.subgroupOf G)).comp φ0
  have hφ0 : ∀ t : omegaSub r k C₀, (φ0 t : GL (Fin (k + 1)) F) =
      diagHom (k + 1) (fun i => e ((t : Fin (k + 1) → C) i)) := fun t => rfl
  have hφker : ∀ t : omegaSub r k C₀, φ t = 1 ↔
      diagHom (k + 1) (fun i => e ((t : Fin (k + 1) → C) i)) ∈ Z := by
    intro t
    change QuotientGroup.mk (φ0 t) = (1 : ↥G ⧸ Z.subgroupOf G) ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, hφ0]
  have hkerconst : ∀ t : φ.ker, (∀ i, (t.1 : Fin (k + 1) → C) i = (t.1 : Fin (k + 1) → C) 0) ∧
      (t.1 : Fin (k + 1) → C) 0 ∈ C₀ := by
    intro t
    have h1 := (hφker t.1).1 (MonoidHom.mem_ker.1 t.2)
    obtain ⟨u, hu⟩ := hZsc h1
    have hu' : (fun _ : Fin (k + 1) => u) = fun i => e ((t.1 : Fin (k + 1) → C) i) :=
      diagHom_injective (K := F) (k + 1) (by rw [← scalar_eq_diagHom_const]; exact hu)
    have hcoord : ∀ i, e ((t.1 : Fin (k + 1) → C) i) = u := fun i => (congrFun hu' i).symm
    have hconst : ∀ i, (t.1 : Fin (k + 1) → C) i = (t.1 : Fin (k + 1) → C) 0 := fun i =>
      he ((hcoord i).trans (hcoord 0).symm)
    refine ⟨hconst, (hmemC₀ _).2 ?_⟩
    have : diagHom (k + 1) (fun i => e ((t.1 : Fin (k + 1) → C) i)) =
        Matrix.GeneralLinearGroup.scalar (Fin (k + 1)) (e ((t.1 : Fin (k + 1) → C) 0)) := by
      rw [scalar_eq_diagHom_const]
      congr 1
      funext i
      rw [hconst i]
    rw [← this]
    exact h1
  have hkerle : Nat.card φ.ker ≤ Nat.card C₀ := by
    let f : φ.ker → C₀ := fun t => ⟨(t.1 : Fin (k + 1) → C) 0, (hkerconst t).2⟩
    have hf : Function.Injective f := by
      intro t t' h
      apply Subtype.ext
      apply Subtype.ext
      funext i
      have h0 : (t.1 : Fin (k + 1) → C) 0 = (t'.1 : Fin (k + 1) → C) 0 :=
        congrArg Subtype.val h
      rw [(hkerconst t).1 i, (hkerconst t').1 i, h0]
    exact Nat.card_le_card_of_injective f hf
  have hpowker : ∀ t : omegaSub r k C₀, φ (t ^ r) = 1 := by
    intro t
    rw [hφker]
    obtain ⟨-, z, hz, htz⟩ := t.2
    have : diagHom (k + 1) (fun i => e (((t ^ r : omegaSub r k C₀) : Fin (k + 1) → C) i)) =
        Matrix.GeneralLinearGroup.scalar (Fin (k + 1)) (e z) := by
      rw [scalar_eq_diagHom_const]
      congr 1
      funext i
      change e ((t : Fin (k + 1) → C) i ^ r) = e z
      rw [htz i]
    rw [this]
    exact (hmemC₀ z).1 hz
  have hElem : IsElemAbelian r φ.range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨s, hs⟩ := MonoidHom.mem_range.1 a.2
      obtain ⟨t, ht⟩ := MonoidHom.mem_range.1 b.2
      apply Subtype.ext
      change (a : ↥G ⧸ Z.subgroupOf G) * b = b * a
      rw [← hs, ← ht, ← map_mul, ← map_mul, mul_comm s t]
    · obtain ⟨t, rfl⟩ := MonoidHom.mem_range.1 hy
      rw [← map_pow]
      exact hpowker t
  have hpgroup : IsPGroup r φ.range := fun y => ⟨1, Subtype.ext (by simpa using hElem.2 y y.2)⟩
  obtain ⟨κ, hκ⟩ := hpgroup.exists_card_eq
  have hrk : r ≤ Nat.card (powMonoidHom r : C →* C).ker := by
    obtain ⟨n, hn, hnc⟩ := hCr.nontrivial_iff_card.1 inferInstance
    exact le_card_pow_ker (hnc ▸ dvd_pow_self r hn.ne')
  have hΩ := card_omega_ge (r := r) (k := k) hC₀m
  have hΩ' : r ^ k * Nat.card ↥(C₀ ⊓ (powMonoidHom r : C →* C).range) ≤
      Nat.card (omegaSub r k C₀) :=
    (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hrk k)).trans hΩ
  have hiso := Subgroup.card_ker_mul_card_range φ
  have hker_pos : 0 < Nat.card φ.ker := Nat.card_pos
  have hC₀pos : 0 < Nat.card C₀ := Nat.card_pos
  have hrpos : 0 < r := hr.out.pos
  have hle : k - (if ∀ z : C, Matrix.GeneralLinearGroup.scalar (Fin (k + 1)) (e z) ∈ Z
      then 1 else 0) ≤ κ := by
    by_cases htop : C₀ = ⊤
    · have hall : ∀ z : C, Matrix.GeneralLinearGroup.scalar (Fin (k + 1)) (e z) ∈ Z := fun z =>
        (hmemC₀ z).1 (htop ▸ Subgroup.mem_top z)
      rw [if_pos hall]
      have h1 : C₀ ⊓ (powMonoidHom r : C →* C).range = (powMonoidHom r : C →* C).range := by
        rw [htop, top_inf_eq]
      have h2 := card_le_mul_card_pow_range (C := C) (r := r)
      have h3 : Nat.card C = Nat.card C₀ := by
        rw [htop, Subgroup.card_top]
      rw [h1] at hΩ'
      have h4 : r ^ k * Nat.card (powMonoidHom r : C →* C).range ≤
          r * Nat.card (powMonoidHom r : C →* C).range * Nat.card φ.range := by
        calc r ^ k * Nat.card (powMonoidHom r : C →* C).range
            ≤ Nat.card (omegaSub r k C₀) := hΩ'
          _ = Nat.card φ.ker * Nat.card φ.range := hiso.symm
          _ ≤ Nat.card C * Nat.card φ.range := Nat.mul_le_mul_right _ (h3 ▸ hkerle)
          _ ≤ (r * Nat.card (powMonoidHom r : C →* C).range) * Nat.card φ.range :=
              Nat.mul_le_mul_right _ h2
      have h5 : r ^ k ≤ r * Nat.card φ.range := by
        have hpos : 0 < Nat.card (powMonoidHom r : C →* C).range := Nat.card_pos
        have : r ^ k * Nat.card (powMonoidHom r : C →* C).range ≤
            (r * Nat.card φ.range) * Nat.card (powMonoidHom r : C →* C).range := by
          calc _ ≤ _ := h4
            _ = _ := by ring
        exact Nat.le_of_mul_le_mul_right this hpos
      rw [hκ] at h5
      have : r ^ k ≤ r ^ (κ + 1) := by simpa [pow_succ, mul_comm] using h5
      have := (Nat.pow_le_pow_iff_right hr.out.one_lt).1 this
      omega
    · have hnall : ¬ ∀ z : C, Matrix.GeneralLinearGroup.scalar (Fin (k + 1)) (e z) ∈ Z := by
        intro h
        exact htop (Subgroup.eq_top_iff' _ |>.2 fun z => (hmemC₀ z).2 (h z))
      rw [if_neg hnall]
      have h1 : C₀ ⊓ (powMonoidHom r : C →* C).range = C₀ :=
        inf_eq_left.2 (le_pow_range_of_ne_top hCr htop)
      rw [h1] at hΩ'
      have h4 : r ^ k * Nat.card C₀ ≤ Nat.card C₀ * Nat.card φ.range := by
        calc r ^ k * Nat.card C₀ ≤ Nat.card (omegaSub r k C₀) := hΩ'
          _ = Nat.card φ.ker * Nat.card φ.range := hiso.symm
          _ ≤ Nat.card C₀ * Nat.card φ.range := Nat.mul_le_mul_right _ hkerle
      have h5 : r ^ k ≤ Nat.card φ.range := by
        have : r ^ k * Nat.card C₀ ≤ Nat.card φ.range * Nat.card C₀ := by
          calc _ ≤ _ := h4
            _ = _ := by ring
        exact Nat.le_of_mul_le_mul_right this hC₀pos
      rw [hκ] at h5
      have := (Nat.pow_le_pow_iff_right hr.out.one_lt).1 h5
      omega
  have hpr := le_pRank hr.out.one_lt (H := ⊤) (E := φ.range) le_top hElem hκ
  omega

open scoped Classical in
theorem toral_lower_bound {F : Type} [Field F] [Fintype F] {r m : ℕ} [Fact r.Prime]
    (hm : 1 ≤ m) {C : Type} [CommGroup C] [Finite C] [Nontrivial C] (hCc : IsCyclic C)
    (hCr : IsPGroup r C) (e : C →* Fˣ) (he : Function.Injective e)
    (G : Subgroup (GL (Fin m) F)) (hGSL : G ≤ StatedSL m F)
    (hdiag : ∀ t : Fin m → C, ∏ i, t i = 1 → diagHom m (fun i => e (t i)) ∈ G)
    (Z : Subgroup (GL (Fin m) F)) (hZG : Z ≤ G) (hZsc : Z ≤ StatedScalars (Fin m) F)
    [(Z.subgroupOf G).Normal] :
    m - 1 - (if ∀ z : C, Matrix.GeneralLinearGroup.scalar (Fin m) (e z) ∈ Z then 1 else 0) ≤
      CFSG.Open.pRank r (⊤ : Subgroup (↥G ⧸ Z.subgroupOf G)) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simpa using toral_lower_bound_succ hCc hCr e he G hGSL hdiag Z hZG hZsc

end Toral

end CFSG.LocalAnalysis.RankThreeUC.S15.ACore
