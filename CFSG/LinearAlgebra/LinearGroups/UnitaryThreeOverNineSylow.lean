module

public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineGroups
public import CFSG.LieType.Steinberg.CentralExt.UnitaryThreeSylow

public section

namespace CFSG.LinearGroups.UnitaryThreeOverNine

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg

variable {F : Type} [Field F]

@[expose] def diagThreeHom : (Fin 3 → Fˣ) →* GL (Fin 3) F where
  toFun := diagGL
  map_one' := Units.ext (by rw [coe_diagGL, Units.val_one]; simp)
  map_mul' d e := Units.ext (by
    rw [Units.val_mul, coe_diagGL, coe_diagGL, coe_diagGL, diagonal_mul_diagonal]
    simp)

theorem diagThreeHom_apply (d : Fin 3 → Fˣ) : (diagThreeHom d : GL (Fin 3) F) = diagGL d := rfl

@[expose] def wreathSwapMat : Matrix (Fin 3) (Fin 3) F := !![-1, 0, 0; 0, 0, 1; 0, 1, 0]

theorem wreathSwapMat_mul_self :
    (wreathSwapMat : Matrix (Fin 3) (Fin 3) F) * wreathSwapMat = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [wreathSwapMat, Matrix.mul_apply, Fin.sum_univ_three]

@[expose] def wGL : GL (Fin 3) F :=
  ⟨wreathSwapMat, wreathSwapMat, wreathSwapMat_mul_self, wreathSwapMat_mul_self⟩

theorem coe_wGL : ((wGL : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = wreathSwapMat := rfl

theorem wGL_mul_self : (wGL : GL (Fin 3) F) * wGL = 1 := Units.ext wreathSwapMat_mul_self

theorem wGL_sq : (wGL : GL (Fin 3) F) ^ 2 = 1 := by rw [sq, wGL_mul_self]

theorem wGL_inv : (wGL : GL (Fin 3) F)⁻¹ = wGL := inv_eq_of_mul_eq_one_right wGL_mul_self

theorem wGL_ne_one : (wGL : GL (Fin 3) F) ≠ 1 := by
  intro h
  have := congrFun (congrFun (congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) h)
    1) 1
  simp [coe_wGL, wreathSwapMat] at this

theorem wGL_conj_diagGL (d : Fin 3 → Fˣ) :
    (wGL : GL (Fin 3) F)⁻¹ * diagGL d * wGL = diagGL ![d 0, d 2, d 1] := by
  rw [wGL_inv]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_wGL, coe_diagGL, coe_diagGL]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [wreathSwapMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul_diagonal]

theorem diagGL_ne_diagGL_mul_wGL (y y' : Fin 3 → Fˣ) :
    diagGL y ≠ diagGL y' * (wGL : GL (Fin 3) F) := by
  intro h
  have := congrFun (congrFun (congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) h)
    1) 2
  simp [coe_diagGL, coe_wGL, wreathSwapMat, Matrix.mul_apply, Fin.sum_univ_three] at this
  exact (y' 1).ne_zero this.symm

theorem diagGL_mul_wGL_pow_inj {x x' : Fin 3 → Fˣ} {e e' : ℕ} (he : e < 2) (he' : e' < 2)
    (h : diagGL x * (wGL : GL (Fin 3) F) ^ e = diagGL x' * wGL ^ e') : e = e' ∧ x = x' := by
  interval_cases e <;> interval_cases e'
  · rw [pow_zero, mul_one, mul_one] at h
    exact ⟨rfl, diagGL_injective h⟩
  · rw [pow_zero, mul_one, pow_one] at h
    exact absurd h (diagGL_ne_diagGL_mul_wGL _ _)
  · rw [pow_zero, mul_one, pow_one] at h
    exact absurd h.symm (diagGL_ne_diagGL_mul_wGL _ _)
  · exact ⟨rfl, diagGL_injective (mul_right_cancel h)⟩

theorem diagGL_mem_statedSU (hF : Nat.card F = 9) (d : Fin 3 → Fˣ) (hd : ∀ k, d k ^ 4 = 1)
    (hdet : d 0 * d 1 * d 2 = 1) : diagGL d ∈ StatedSU 3 3 F := by
  rw [← SetLike.mem_coe, coe_statedSU hF, Set.mem_ofPred_eq, coe_diagGL]
  refine ⟨?_, ?_⟩
  · rw [Matrix.diagonal_map (by simp), Matrix.diagonal_transpose, diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1
    funext k
    have := congrArg Units.val (hd k)
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at this
    rw [← pow_succ, this]
  · rw [Matrix.det_diagonal, Fin.prod_univ_three]
    have := congrArg Units.val hdet
    simpa using this

theorem wGL_mem_statedSU (hF : Nat.card F = 9) : (wGL : GL (Fin 3) F) ∈ StatedSU 3 3 F := by
  rw [← SetLike.mem_coe, coe_statedSU hF, Set.mem_ofPred_eq, coe_wGL]
  refine ⟨?_, ?_⟩
  · have hmap : (wreathSwapMat : Matrix (Fin 3) (Fin 3) F).map (· ^ 3) = wreathSwapMat := by
      ext a b
      fin_cases a <;> fin_cases b <;> norm_num [wreathSwapMat]
    have htr : (wreathSwapMat : Matrix (Fin 3) (Fin 3) F)ᵀ = wreathSwapMat := by
      ext a b
      fin_cases a <;> fin_cases b <;> simp [wreathSwapMat]
    rw [hmap, htr, wreathSwapMat_mul_self]
  · simp [wreathSwapMat, Matrix.det_fin_three]

theorem sq_eq_neg_one_of_orderOf {i : Fˣ} (hi : orderOf i = 4) : (i : F) ^ 2 = -1 := by
  have h4 : i ^ 4 = 1 := by rw [← hi]; exact pow_orderOf_eq_one i
  have h2 : i ^ 2 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hi]; norm_num)
  have h4' : ((i : F) ^ 2) * ((i : F) ^ 2) = 1 := by
    have := congrArg Units.val h4
    rw [Units.val_pow_eq_pow_val, Units.val_one] at this
    rw [← pow_add]
    exact this
  rcases mul_self_eq_one_iff.mp h4' with h | h
  · exact absurd (Units.ext (by rw [Units.val_pow_eq_pow_val, h, Units.val_one])) h2
  · exact h

theorem exists_units_orderOf_eq_four (hF : Nat.card F = 9) : ∃ i : Fˣ, orderOf i = 4 := by
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; norm_num)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf g = 8 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hF]
  refine ⟨g ^ 2, ?_⟩
  rw [orderOf_pow_of_dvd (by norm_num) (by rw [hord]; norm_num), hord]

theorem wreath_sylow_model (hF : Nat.card F = 9) (i : Fˣ) (hi : orderOf i = 4) :
    (∃ s t w : StatedSU 3 3 F,
      ((s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = diagonal ![(i : F)⁻¹, (i : F), 1] ∧
      ((t : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = diagonal ![(i : F)⁻¹, 1, (i : F)] ∧
      ((w : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = !![-1, 0, 0; 0, 0, 1; 0, 1, 0]) ∧
    ∀ s t w : StatedSU 3 3 F,
      ((s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = diagonal ![(i : F)⁻¹, (i : F), 1] →
      ((t : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = diagonal ![(i : F)⁻¹, 1, (i : F)] →
      ((w : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = !![-1, 0, 0; 0, 0, 1; 0, 1, 0] →
      s * t = t * s ∧ orderOf s = 4 ∧ orderOf t = 4 ∧
      Subgroup.zpowers s ⊓ Subgroup.zpowers t = ⊥ ∧ orderOf w = 2 ∧
      w ∉ Subgroup.closure {s, t} ∧ w⁻¹ * s * w = t ∧ w⁻¹ * t * w = s ∧
      Nat.card (Subgroup.closure {s, t, w}) = 32 ∧
      (∃ P : Sylow 2 (StatedSU 3 3 F), (P : Subgroup (StatedSU 3 3 F)) =
        Subgroup.closure {s, t, w}) ∧
      ((((s * t) ^ 2 : StatedSU 3 3 F) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        diagonal ![1, -1, -1] ∧
      orderOf ((s * t) ^ 2) = 2 ∧ (s * t) ^ 2 ∈ Subgroup.closure {s, t, w} ∧
      ∀ g ∈ Subgroup.closure {s, t, w}, g * (s * t) ^ 2 = (s * t) ^ 2 * g := by
  have hi4 : i ^ 4 = 1 := by rw [← hi]; exact pow_orderOf_eq_one i
  have hi2 : (i : F) ^ 2 = -1 := sq_eq_neg_one_of_orderOf hi
  have hi2ne : i ^ 2 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hi]; norm_num)
  have hi4' : i⁻¹ ^ 4 = 1 := by rw [inv_pow, hi4, inv_one]
  set ds : Fin 3 → Fˣ := ![i⁻¹, i, 1] with hds
  set dt : Fin 3 → Fˣ := ![i⁻¹, 1, i] with hdt
  have hds_coe : (fun k => ((ds k : Fˣ) : F)) = ![(i : F)⁻¹, (i : F), 1] := by
    funext k
    fin_cases k <;> simp [ds]
  have hdt_coe : (fun k => ((dt k : Fˣ) : F)) = ![(i : F)⁻¹, 1, (i : F)] := by
    funext k
    fin_cases k <;> simp [dt]
  have hds4 : ∀ k, ds k ^ 4 = 1 := fun k => by fin_cases k <;> simp [ds, hi4, hi4']
  have hdt4 : ∀ k, dt k ^ 4 = 1 := fun k => by fin_cases k <;> simp [dt, hi4, hi4']
  have hsmem := diagGL_mem_statedSU hF ds hds4 (by simp [ds])
  have htmem := diagGL_mem_statedSU hF dt hdt4 (by simp [dt])
  have hwmem := wGL_mem_statedSU (F := F) hF
  refine ⟨⟨⟨diagGL ds, hsmem⟩, ⟨diagGL dt, htmem⟩, ⟨wGL, hwmem⟩, ?_, ?_, rfl⟩, ?_⟩
  · change ((diagGL ds : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = _
    rw [coe_diagGL, hds_coe]
  · change ((diagGL dt : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = _
    rw [coe_diagGL, hdt_coe]
  intro s t w hs ht hw
  have hsG : (s : GL (Fin 3) F) = diagThreeHom ds :=
    Units.ext (by rw [hs, diagThreeHom_apply, coe_diagGL, hds_coe])
  have htG : (t : GL (Fin 3) F) = diagThreeHom dt :=
    Units.ext (by rw [ht, diagThreeHom_apply, coe_diagGL, hdt_coe])
  have hwG : (w : GL (Fin 3) F) = wGL := Units.ext (by rw [hw, coe_wGL]; rfl)
  have hdsdt : ds * dt = dt * ds := mul_comm _ _
  have hst : s * t = t * s := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hsG, htG, ← map_mul, ← map_mul, hdsdt])
  have hord4 : ∀ d : Fin 3 → Fˣ, d 1 = i ∨ d 2 = i → (∀ k, d k ^ 4 = 1) → orderOf d = 4 := by
    intro d hd hd4
    have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := d) (fun h => hi2ne ?_)
      (by funext k; simp [hd4 k])
    · rw [h]
      norm_num
    · rcases hd with hd | hd
      · have := congrFun h 1
        simpa [hd] using this
      · have := congrFun h 2
        simpa [hd] using this
  have hs4 : orderOf s = 4 := by
    rw [← Subgroup.orderOf_coe, hsG, orderOf_injective _ diagGL_injective]
    exact hord4 ds (Or.inl rfl) hds4
  have ht4 : orderOf t = 4 := by
    rw [← Subgroup.orderOf_coe, htG, orderOf_injective _ diagGL_injective]
    exact hord4 dt (Or.inr rfl) hdt4
  have hw2 : orderOf w = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [← Subgroup.orderOf_coe, hwG]
    exact orderOf_eq_prime wGL_sq wGL_ne_one
  have hwst : w⁻¹ * s * w = t := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hsG, htG, hwG, diagThreeHom_apply,
      diagThreeHom_apply, wGL_conj_diagGL]
    congr 1)
  have hwts : w⁻¹ * t * w = s := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hsG, htG, hwG, diagThreeHom_apply,
      diagThreeHom_apply, wGL_conj_diagGL]
    congr 1)
  have hinter : Subgroup.zpowers s ⊓ Subgroup.zpowers t = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hgs, hgt⟩
    obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp hgs
    obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.mp hgt
    have h1 : diagThreeHom (ds ^ a) = (diagThreeHom (dt ^ b) : GL (Fin 3) F) := by
      have := congrArg Subtype.val hb
      rw [Subgroup.coe_zpow, Subgroup.coe_zpow, htG, hsG, ← map_zpow, ← map_zpow] at this
      exact this.symm
    have h2 := diagGL_injective h1
    have h3 : i ^ a = 1 := by
      have := congrFun h2 1
      simpa [ds, dt] using this
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    rw [Subgroup.coe_zpow, hsG, ← map_zpow, Subgroup.coe_one]
    have : ds ^ a = 1 := by
      funext k
      fin_cases k <;> simp [ds, h3]
    rw [this, map_one]
  have hdiag : Subgroup.closure ({s, t} : Set (StatedSU 3 3 F)) ≤
      (diagThreeHom.range).comap (StatedSU 3 3 F).subtype := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨ds, hsG.symm⟩
    · exact ⟨dt, htG.symm⟩
  have hwout : w ∉ Subgroup.closure {s, t} := by
    intro hwc
    obtain ⟨d, hd⟩ := hdiag hwc
    apply diagGL_ne_diagGL_mul_wGL d 1
    rw [← diagThreeHom_apply, ← diagThreeHom_apply, map_one, one_mul, hd]
    exact hwG
  set S := Subgroup.closure ({s, t, w} : Set (StatedSU 3 3 F)) with hS
  have hsS : s ∈ S := Subgroup.subset_closure (Set.mem_insert _ _)
  have htS : t ∈ S := Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hwS : w ∈ S := Subgroup.subset_closure (Set.mem_insert_of_mem _
    (Set.mem_insert_of_mem _ rfl))
  have hw2' : w ^ 2 = 1 := by rw [← hw2]; exact pow_orderOf_eq_one w
  let Φ : Fin 4 × Fin 4 × Fin 2 → S := fun abe =>
    ⟨s ^ (abe.1 : ℕ) * t ^ (abe.2.1 : ℕ) * w ^ (abe.2.2 : ℕ),
      S.mul_mem (S.mul_mem (S.pow_mem hsS _) (S.pow_mem htS _)) (S.pow_mem hwS _)⟩
  have hΦG : ∀ abe : Fin 4 × Fin 4 × Fin 2, (((Φ abe : StatedSU 3 3 F)) : GL (Fin 3) F) =
      diagGL (ds ^ (abe.1 : ℕ) * dt ^ (abe.2.1 : ℕ)) * wGL ^ (abe.2.2 : ℕ) := fun abe => by
    change (((s ^ (abe.1 : ℕ) * t ^ (abe.2.1 : ℕ) * w ^ (abe.2.2 : ℕ) : StatedSU 3 3 F)) :
      GL (Fin 3) F) = _
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow, Subgroup.coe_pow,
      hsG, htG, hwG, ← map_pow, ← map_pow, ← map_mul, diagThreeHom_apply]
  have hΦinj : Function.Injective Φ := by
    rintro ⟨a, b, e⟩ ⟨a', b', e'⟩ h
    have h1 := congrArg (fun z : S => ((z : StatedSU 3 3 F) : GL (Fin 3) F)) h
    simp only [hΦG] at h1
    obtain ⟨he, hx⟩ := diagGL_mul_wGL_pow_inj e.2 e'.2 h1
    have ha : i ^ (a : ℕ) = i ^ (a' : ℕ) := by
      have := congrFun hx 1
      simpa [ds, dt] using this
    have hb : i ^ (b : ℕ) = i ^ (b' : ℕ) := by
      have := congrFun hx 2
      simpa [ds, dt] using this
    rw [pow_inj_mod, hi] at ha hb
    have ha' : (a : ℕ) = a' := by
      rwa [Nat.mod_eq_of_lt a.2, Nat.mod_eq_of_lt a'.2] at ha
    have hb' : (b : ℕ) = b' := by
      rwa [Nat.mod_eq_of_lt b.2, Nat.mod_eq_of_lt b'.2] at hb
    rw [Fin.ext ha', Fin.ext hb', Fin.ext he]
  have hΦsurj : Function.Surjective Φ := by
    rintro ⟨g, hg⟩
    obtain ⟨a, b, e, he, rfl⟩ := exists_zpow_mul_zpow_mul_pow hst hwst.symm hw2' hg
    obtain ⟨a', ha', haeq⟩ := exists_lt_orderOf_zpow_eq (x := s) (by rw [hs4]; norm_num) a
    obtain ⟨b', hb', hbeq⟩ := exists_lt_orderOf_zpow_eq (x := t) (by rw [ht4]; norm_num) b
    rw [hs4] at ha'
    rw [ht4] at hb'
    refine ⟨(⟨a', ha'⟩, ⟨b', hb'⟩, ⟨e, he⟩), Subtype.ext ?_⟩
    change s ^ a' * t ^ b' * w ^ e = s ^ a * t ^ b * w ^ e
    rw [haeq, hbeq]
  have hcardS : Nat.card S = 32 := by
    rw [← Nat.card_congr (Equiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩)]
    simp
  have hSyl : ∃ P : Sylow 2 (StatedSU 3 3 F), (P : Subgroup (StatedSU 3 3 F)) = S := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hP : IsPGroup 2 S := IsPGroup.of_card (n := 5) (by rw [hcardS]; norm_num)
    have hind : S.index = 189 := by
      have h := S.card_mul_index
      rw [hcardS, card_statedSU hF] at h
      omega
    exact ⟨hP.toSylow (by rw [hind]; decide), rfl⟩
  have hi2u : i ^ 2 = -1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hi2, Units.val_neg,
    Units.val_one])
  have hprod : (ds * dt) ^ 2 = ![1, -1, -1] := by
    funext k
    fin_cases k
    · change (i⁻¹ * i⁻¹) ^ 2 = 1
      rw [← sq, ← pow_mul]
      exact hi4'
    · change (i * 1) ^ 2 = -1
      rw [mul_one, hi2u]
    · change (1 * i) ^ 2 = -1
      rw [one_mul, hi2u]
  have hxG : (((s * t) ^ 2 : StatedSU 3 3 F) : GL (Fin 3) F) = diagThreeHom ![1, -1, -1] := by
    rw [Subgroup.coe_pow, Subgroup.coe_mul, hsG, htG, ← map_mul, ← map_pow, hprod]
  have hxmat : ((((s * t) ^ 2 : StatedSU 3 3 F) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      diagonal ![1, -1, -1] := by
    rw [hxG, diagThreeHom_apply, coe_diagGL]
    congr 1
    funext k
    fin_cases k <;> simp
  have hxord : orderOf ((s * t) ^ 2) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [← Subgroup.orderOf_coe, hxG, orderOf_injective _ diagGL_injective]
    have h3 : (3 : F) = 0 := by
      have := (unitaryFieldData_of_card hF).charP
      exact_mod_cast CharP.cast_eq_zero F 3
    have hneg : (-1 : Fˣ) ≠ 1 := by
      intro h
      have := congrArg Units.val h
      simp only [Units.val_neg, Units.val_one] at this
      have h2 : (2 : F) = 0 := by linear_combination -this
      have : (1 : F) = 0 := by linear_combination h3 - h2
      exact one_ne_zero this
    refine orderOf_eq_prime (by funext k; fin_cases k <;> simp) fun h => hneg ?_
    have := congrFun h 1
    simpa using this
  have hxS : (s * t) ^ 2 ∈ S := S.pow_mem (S.mul_mem hsS htS) 2
  have hcst : Commute s t := hst
  have hxs : s * (s * t) ^ 2 = (s * t) ^ 2 * s :=
    (((Commute.refl s).mul_right hcst).pow_right 2).eq
  have hxt : t * (s * t) ^ 2 = (s * t) ^ 2 * t :=
    ((hcst.symm.mul_right (Commute.refl t)).pow_right 2).eq
  have hxw : w * (s * t) ^ 2 = (s * t) ^ 2 * w := by
    have hconj : w⁻¹ * (s * t) ^ 2 * w = (s * t) ^ 2 := Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hxG, hwG, diagThreeHom_apply,
        wGL_conj_diagGL]
      congr 1)
    calc w * (s * t) ^ 2 = w * (w⁻¹ * (s * t) ^ 2 * w) := by rw [hconj]
      _ = (s * t) ^ 2 * w := by group
  have hcent : S ≤ Subgroup.centralizer {(s * t) ^ 2} := by
    rw [hS, Subgroup.closure_le]
    rintro g (rfl | rfl | rfl) <;> rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    · exact hxs
    · exact hxt
    · exact hxw
  exact ⟨hst, hs4, ht4, hinter, hw2, hwout, hwst, hwts, hcardS, hSyl, hxmat, hxord, hxS,
    fun g hg => Subgroup.mem_centralizer_singleton_iff.mp (hcent hg)⟩

end CFSG.LinearGroups.UnitaryThreeOverNine
