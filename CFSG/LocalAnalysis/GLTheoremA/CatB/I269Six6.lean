module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I269Six5

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I269Six

open CFSG.LocalAnalysis.GLTheoremA.LevelLieU6
open CFSG.Fischer
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (primeFormUnitary)
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo (hF4 bar hF4_bar)
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open scoped commutatorElement

abbrev piS : M6 →* S6 := QuotientGroup.mk' Zs

theorem piS_eq_one {x : M6} : piS x = 1 ↔ x ∈ Zs := by
  rw [piS, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem Zs_central {z : M6} (hz : z ∈ Zs) (x : M6) : z * x = x * z := by
  obtain ⟨c, hc⟩ := mem_Zs.1 hz
  apply Subtype.ext
  show (z : GL (Fin 6) F4) * x = x * z
  rw [hc]
  exact Matrix.GeneralLinearGroup.scalar_commute c (x : GL (Fin 6) F4)

theorem scalar_mem_M6 (c : F4ˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 6) c ∈ CFSG.Open.StatedSU 6 (2 ^ 1) F4 := by
  have h3 : (c : F4) ^ 3 = 1 := f4_cube _ (Units.ne_zero c)
  apply CFSG.LocalAnalysis.GLTheoremA.LevelLieU.mem_statedSU_of 6
  · rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, show (6 : ℕ) = 3 * 2 from rfl,
      pow_mul, h3, one_pow]
  · rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_map (map_zero bar),
      Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    simp only [Function.comp_apply, hF4_bar, bar, frobenius_def, ← pow_succ]
    rw [show (2 : ℕ) + 1 = 3 from rfl]
    simpa using h3

theorem scalar_inj {c c' : F4ˣ} (h : Matrix.GeneralLinearGroup.scalar (Fin 6) c =
    Matrix.GeneralLinearGroup.scalar (Fin 6) c') : c = c' := by
  have := congrFun (congrFun (congrArg (fun g : GL (Fin 6) F4 => (g : Matrix (Fin 6) (Fin 6) F4)) h) 0) 0
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at this
  exact Units.ext this

noncomputable def scalarUnit (z : Zs) : F4ˣ := (mem_Zs.1 z.2).choose

theorem scalarUnit_spec (z : Zs) :
    ((z : M6) : GL (Fin 6) F4) = Matrix.GeneralLinearGroup.scalar (Fin 6) (scalarUnit z) :=
  (mem_Zs.1 z.2).choose_spec

theorem card_Zs : Nat.card Zs = 3 := by
  let f : F4ˣ → Zs := fun c => ⟨⟨Matrix.GeneralLinearGroup.scalar (Fin 6) c, scalar_mem_M6 c⟩,
    mem_Zs.2 ⟨c, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro c c' h
      exact scalar_inj (congrArg (fun z : Zs => ((z : M6) : GL (Fin 6) F4)) h)
    · intro z
      refine ⟨scalarUnit z, Subtype.ext (Subtype.ext ?_)⟩
      exact (scalarUnit_spec z).symm
  rw [Nat.card_congr (Equiv.ofBijective f hf).symm, Nat.card_eq_fintype_card, Fintype.card_units,
    F4.card]

abbrev Eh (Ē : Subgroup S6) : Subgroup M6 := Ē.comap piS

theorem card_Eh (Ē : Subgroup S6) : Nat.card (Eh Ē) = Nat.card Ē * 3 := by
  have hsurj : Function.Surjective piS := QuotientGroup.mk'_surjective Zs
  have hk : Nat.card (Eh Ē) * (Eh Ē).index = Nat.card M6 := Subgroup.card_mul_index (Eh Ē)
  have hk' : Nat.card Ē * Ē.index = Nat.card S6 := Subgroup.card_mul_index Ē
  have hi : (Eh Ē).index = Ē.index := Subgroup.index_comap_of_surjective Ē hsurj
  have hq : Nat.card M6 = Nat.card S6 * Nat.card Zs :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup Zs
  have hpos : 0 < Ē.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
  have key : Nat.card (Eh Ē) * Ē.index = Nat.card Ē * 3 * Ē.index := by
    calc Nat.card (Eh Ē) * Ē.index = Nat.card (Eh Ē) * (Eh Ē).index := by rw [hi]
      _ = Nat.card M6 := hk
      _ = Nat.card S6 * Nat.card Zs := hq
      _ = Nat.card Ē * Ē.index * Nat.card Zs := by rw [hk']
      _ = Nat.card Ē * 3 * Ē.index := by rw [card_Zs]; ring
  exact Nat.eq_of_mul_eq_mul_right hpos key

theorem cube_mul_of_central {G : Type} [Group G] {x y z : G} (hz : ∀ w : G, z * w = w * z)
    (hxy : x * y = z * (y * x)) (hz3 : z ^ 3 = 1) : (x * y) ^ 3 = x ^ 3 * y ^ 3 := by
  set c := z⁻¹ with hcdef
  have hc : ∀ w : G, c * w = w * c := by
    intro w
    calc c * w = c * (w * z) * c := by rw [hcdef]; group
      _ = c * (z * w) * c := by rw [hz w]
      _ = w * c := by rw [hcdef]; group
  have hyx : y * x = c * (x * y) := by rw [hcdef, hxy, inv_mul_cancel_left]
  have hc3 : c * c * c = 1 := by rw [← pow_three', hcdef, inv_pow, hz3, inv_one]
  have hl : ∀ a b : G, a * (c * b) = c * (a * b) := fun a b => by
    rw [← mul_assoc, ← hc a, mul_assoc]
  have hcc : ∀ a b : G, a * (c * c * b) = c * c * (a * b) := fun a b => by
    rw [mul_assoc, hl, hl, ← mul_assoc]
  have s1 : (x * y) * (x * y) = c * (x * x * (y * y)) := by
    calc (x * y) * (x * y) = x * (y * x) * y := by simp only [mul_assoc]
      _ = x * (c * (x * y)) * y := by rw [hyx]
      _ = c * (x * (x * y)) * y := by rw [hl]
      _ = c * (x * x * (y * y)) := by simp only [mul_assoc]
  have s2 : (y * y) * x = c * c * (x * (y * y)) := by
    calc (y * y) * x = y * (y * x) := by rw [mul_assoc]
      _ = y * (c * (x * y)) := by rw [hyx]
      _ = c * (y * (x * y)) := by rw [hl]
      _ = c * ((y * x) * y) := by rw [mul_assoc]
      _ = c * (c * (x * y) * y) := by rw [hyx]
      _ = c * c * (x * (y * y)) := by simp only [mul_assoc]
  calc (x * y) ^ 3 = (x * y) ^ 2 * (x * y) := by rw [← pow_succ]
    _ = c * (x * x * (y * y)) * (x * y) := by rw [pow_two, s1]
    _ = c * (x * x * ((y * y) * x) * y) := by simp only [mul_assoc]
    _ = c * (x * x * (c * c * (x * (y * y))) * y) := by rw [s2]
    _ = c * (c * c * (x * x * (x * (y * y))) * y) := by rw [hcc (x * x)]
    _ = c * c * c * (x * x * x * (y * y * y)) := by simp only [mul_assoc]
    _ = x ^ 3 * y ^ 3 := by rw [hc3, one_mul]; simp only [pow_three, mul_assoc]

theorem Zs_cube {z : M6} (hz : z ∈ Zs) : z ^ 3 = 1 := by
  obtain ⟨c, hc⟩ := mem_Zs.1 hz
  apply Subtype.ext
  show (z : GL (Fin 6) F4) ^ 3 = 1
  rw [hc, ← map_pow]
  have : c ^ 3 = 1 := Units.ext (by simpa using f4_cube _ (Units.ne_zero c))
  rw [this, map_one]

variable {Ē : Subgroup S6}

theorem Eh_comm (hcomm : ∀ x ∈ Ē, ∀ y ∈ Ē, x * y = y * x) {h k : M6} (hh : h ∈ Eh Ē)
    (hk : k ∈ Eh Ē) : ⁅h, k⁆ ∈ Zs := by
  rw [← piS_eq_one, map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.2 (hcomm _ hh _ hk)

theorem Eh_cube (hexp : ∀ x ∈ Ē, x ^ 3 = 1) {h : M6} (hh : h ∈ Eh Ē) : h ^ 3 ∈ Zs := by
  rw [← piS_eq_one, map_pow]
  exact hexp _ hh

theorem Eh_cube_mul (hcomm : ∀ x ∈ Ē, ∀ y ∈ Ē, x * y = y * x) {h k : M6} (hh : h ∈ Eh Ē)
    (hk : k ∈ Eh Ē) : (h * k) ^ 3 = h ^ 3 * k ^ 3 := by
  have hz := Eh_comm hcomm hh hk
  apply cube_mul_of_central (fun w => Zs_central hz w) _ (Zs_cube hz)
  rw [commutatorElement_def]; group

noncomputable def cubeHom (hcomm : ∀ x ∈ Ē, ∀ y ∈ Ē, x * y = y * x) (hexp : ∀ x ∈ Ē, x ^ 3 = 1) :
    Eh Ē →* Zs where
  toFun h := ⟨h.1 ^ 3, Eh_cube hexp h.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' h k := Subtype.ext (Eh_cube_mul hcomm h.2 k.2)

theorem exists_split (hcomm : ∀ x ∈ Ē, ∀ y ∈ Ē, x * y = y * x) (hexp : ∀ x ∈ Ē, x ^ 3 = 1)
    (hcardĒ : Nat.card Ē = 9) : ∃ g ∈ Eh Ē, g ∉ Zs ∧ g ^ 3 = 1 := by
  set f := cubeHom hcomm hexp with hfdef
  have hEh : Nat.card (Eh Ē) = 27 := by rw [card_Eh, hcardĒ]
  have hq : Nat.card f.ker * Nat.card f.range = 27 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv] at h1
    rw [← hEh, h1, mul_comm]
  have hr : Nat.card f.range ≤ 3 := by
    have := Subgroup.card_le_card_group f.range
    rwa [card_Zs] at this
  have hk9 : 9 ≤ Nat.card f.ker := by
    have : 27 ≤ Nat.card f.ker * 3 := by rw [← hq]; exact Nat.mul_le_mul_left _ hr
    omega
  by_contra hno
  push Not at hno
  have hsub : f.ker ≤ (Zs.comap (Eh Ē).subtype) := by
    intro g hg
    have hg' : g.1 ∈ Zs := by
      by_contra hnz
      exact hno g.1 g.2 hnz (by
        have := congrArg Subtype.val (MonoidHom.mem_ker.1 hg)
        simpa [hfdef, cubeHom] using this)
    exact hg'
  have hle : Nat.card f.ker ≤ 3 := by
    have h2 := Subgroup.card_le_of_le hsub
    have h3 : Nat.card (Zs.comap (Eh Ē).subtype) ≤ Nat.card Zs :=
      Nat.card_le_card_of_injective (fun g => (⟨g.1.1, g.2⟩ : Zs))
        (by
          intro a b hab
          have h1 := congrArg Subtype.val hab
          exact Subtype.ext (Subtype.ext h1))
    have hZ := card_Zs
    omega
  omega

theorem conj_Zs (Q : primeFormUnitary hF4 (idGram F4 6)) {z : M6} (hz : z ∈ Zs) :
    conjM6 Q z ∈ Zs := by
  obtain ⟨c, hc⟩ := mem_Zs.1 hz
  refine mem_Zs.2 ⟨c, ?_⟩
  rw [conjM6_apply, hc, ← Matrix.GeneralLinearGroup.scalar_commute c (Q : GL (Fin 6) F4)]
  group

theorem key_bot {Ê J : Subgroup M6} (hperf : ⁅J, J⁆ = J)
    (hcomm : ∀ h ∈ Ê, ∀ k ∈ Ê, ⁅h, k⁆ ∈ Zs) (hcube : ∀ h ∈ Ê, h ^ 3 ∈ Zs)
    (hcard : 9 < Nat.card Ê) (hJ : ∀ u ∈ J, ∀ h ∈ Ê, u * h = h * u)
    {g : M6} (hgÊ : g ∈ Ê) (hgZ : g ∉ Zs) (hg3 : g ^ 3 = 1) : J = ⊥ := by
  have hg3' : (g : GL (Fin 6) F4) ^ 3 = 1 := by
    have := congrArg Subtype.val hg3
    simpa using this
  by_cases hrk : ∀ c : F4, 3 ≤ (((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) -
      Matrix.scalar (Fin 6) c).rank
  · exact bot_of_perfect_rank hperf (mem_UG_of_M6 g) hg3'
      (fun u hu => congrArg Subtype.val (hJ u hu g hgÊ)) hrk
  push Not at hrk
  obtain ⟨lm, hlt⟩ := hrk
  obtain ⟨P, d, hd⟩ := exists_diag6 ⟨(g : GL (Fin 6) F4), mem_UG_of_M6 g⟩
    (by apply Subtype.ext; simpa using hg3')
  set Q : primeFormUnitary hF4 (idGram F4 6) := P⁻¹ with hQ
  have hDd : mM6 (conjM6 Q g) = Matrix.diagonal d := by
    rw [← hd]
    show (((conjM6 Q g : M6) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = _
    rw [conjM6_apply]
    simp [hQ, Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc]
  have hdet : ∏ i, d i = 1 := by
    rw [← Matrix.det_diagonal, ← hDd]
    exact det_M6 _
  have hDZ : conjM6 Q g ∉ Zs := by
    intro hD
    apply hgZ
    obtain ⟨c, hc⟩ := mem_Zs.1 hD
    refine mem_Zs.2 ⟨c, ?_⟩
    have h1 : (g : GL (Fin 6) F4) = (P : GL (Fin 6) F4) * ((conjM6 Q g : M6) : GL (Fin 6) F4) *
        ((P : GL (Fin 6) F4))⁻¹ := by
      rw [conjM6_apply, hQ]; simp [mul_assoc]
    rw [h1, hc, ← Matrix.GeneralLinearGroup.scalar_commute c (P : GL (Fin 6) F4)]
    group
  have hns : ∃ i, d i ≠ lm := by
    by_contra hall
    push Not at hall
    have hprod : ∏ i, d i = lm ^ 6 := by simp [hall, Finset.prod_const]
    have hlm0 : lm ≠ 0 := by
      rintro rfl
      rw [hprod] at hdet
      norm_num at hdet
    apply hDZ
    refine mem_Zs.2 ⟨Units.mk0 lm hlm0, ?_⟩
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Units.val_mk0]
    exact hDd.trans (congrArg Matrix.diagonal (funext hall))
  have hrk' : (Matrix.diagonal d - Matrix.scalar (Fin 6) lm).rank ≤ 2 := by
    have e : mM6 (conjM6 Q g) = (Q : GL (Fin 6) F4) * (g : GL (Fin 6) F4) *
        ((Q : GL (Fin 6) F4))⁻¹ := by
      show (((conjM6 Q g : M6) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = _
      rw [conjM6_apply]
      simp only [Units.val_mul]
    rw [← hDd, e]
    rw [← rank_conj_sub_scalar (Q : GL (Fin 6) F4) (g : GL (Fin 6) F4) lm] at hlt
    exact (Nat.lt_succ_iff.1 hlt)
  obtain ⟨i1, i2, hne, hS, h1, h2, h12⟩ := struct_of_diag d lm hdet hns hrk'
  have hDÊ : conjM6 Q g ∈ Ê.map (conjM6 Q).toMonoidHom := Subgroup.mem_map_of_mem _ hgÊ
  have hmap := T1_bot (Ê := Ê.map (conjM6 Q).toMonoidHom) (J := J.map (conjM6 Q).toMonoidHom)
    (by rw [← Subgroup.map_commutator, hperf])
    (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_commutatorElement]
      exact conj_Zs Q (hcomm x hx y hy))
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow]
      exact conj_Zs Q (hcube x hx))
    (by rw [Subgroup.card_map_of_injective (conjM6 Q).injective]; exact hcard)
    (by
      rintro _ ⟨u, hu, rfl⟩ _ ⟨h, hh, rfl⟩
      rw [← map_mul, ← map_mul, hJ u hu h hh])
    hDd hDÊ hne hS h1 h2 h12
  rw [Subgroup.eq_bot_iff_forall]
  intro u hu
  have hmem : conjM6 Q u ∈ J.map (conjM6 Q).toMonoidHom := Subgroup.mem_map_of_mem _ hu
  rw [hmap, Subgroup.mem_bot] at hmem
  exact (Subgroup.mem_bot).2 ((conjM6 Q).injective (by simpa using hmem))


theorem conj_cen {c : M6} (hc : c ∈ Zs) (x y : M6) : x * (c * y) * x⁻¹ = c * (x * y * x⁻¹) := by
  rw [show x * (c * y) * x⁻¹ = (x * c) * y * x⁻¹ by group, ← Zs_central hc x]
  group

theorem conj_cen' {c : M6} (hc : c ∈ Zs) (x y : M6) : x⁻¹ * (c * y) * x = c * (x⁻¹ * y * x) := by
  have := conj_cen hc x⁻¹ y
  simpa using this

theorem comm_comm_of {u v h : M6} (ha : ⁅u, h⁆ ∈ Zs) (hb : ⁅v, h⁆ ∈ Zs) :
    ⁅u, v⁆ * h = h * ⁅u, v⁆ := by
  set a := ⁅u, h⁆ with ha_def
  set b := ⁅v, h⁆ with hb_def
  have R1 : u * h * u⁻¹ = a * h := by rw [ha_def, commutatorElement_def]; group
  have R2 : v * h * v⁻¹ = b * h := by rw [hb_def, commutatorElement_def]; group
  have ha' : a⁻¹ ∈ Zs := Zs.inv_mem ha
  have hb' : b⁻¹ ∈ Zs := Zs.inv_mem hb
  have R3 : u⁻¹ * h * u = a⁻¹ * h := by
    have e1 : u⁻¹ * (a * h) * u = h := by rw [← R1]; group
    have e2 : u⁻¹ * (a * h) * u = a * (u⁻¹ * h * u) := by
      calc u⁻¹ * (a * h) * u = (u⁻¹ * a) * h * u := by group
        _ = (a * u⁻¹) * h * u := by rw [Zs_central ha u⁻¹]
        _ = a * (u⁻¹ * h * u) := by group
    calc u⁻¹ * h * u = a⁻¹ * (a * (u⁻¹ * h * u)) := by group
      _ = a⁻¹ * h := by rw [← e2, e1]
  have R4 : v⁻¹ * h * v = b⁻¹ * h := by
    have e1 : v⁻¹ * (b * h) * v = h := by rw [← R2]; group
    have e2 : v⁻¹ * (b * h) * v = b * (v⁻¹ * h * v) := by
      calc v⁻¹ * (b * h) * v = (v⁻¹ * b) * h * v := by group
        _ = (b * v⁻¹) * h * v := by rw [Zs_central hb v⁻¹]
        _ = b * (v⁻¹ * h * v) := by group
    calc v⁻¹ * h * v = b⁻¹ * (b * (v⁻¹ * h * v)) := by group
      _ = b⁻¹ * h := by rw [← e2, e1]
  have hwh : ⁅u, v⁆ * h * ⁅u, v⁆⁻¹ = h := by
    rw [commutatorElement_def]
    calc u * v * u⁻¹ * v⁻¹ * h * (u * v * u⁻¹ * v⁻¹)⁻¹
        = u * (v * (u⁻¹ * (v⁻¹ * h * v) * u) * v⁻¹) * u⁻¹ := by group
      _ = u * (v * (u⁻¹ * (b⁻¹ * h) * u) * v⁻¹) * u⁻¹ := by rw [R4]
      _ = u * (v * (b⁻¹ * (a⁻¹ * h)) * v⁻¹) * u⁻¹ := by
          rw [conj_cen' hb' u h, R3]
      _ = u * (b⁻¹ * (a⁻¹ * (v * h * v⁻¹))) * u⁻¹ := by
          rw [show v * (b⁻¹ * (a⁻¹ * h)) * v⁻¹ = b⁻¹ * (v * (a⁻¹ * h) * v⁻¹) from conj_cen hb' v _,
            conj_cen ha' v h]
      _ = u * (b⁻¹ * (a⁻¹ * (b * h))) * u⁻¹ := by rw [R2]
      _ = u * (a⁻¹ * h) * u⁻¹ := by
          rw [show b⁻¹ * (a⁻¹ * (b * h)) = a⁻¹ * h by
            rw [← mul_assoc b⁻¹ a⁻¹, Zs_central hb' a⁻¹, mul_assoc a⁻¹ b⁻¹, ← mul_assoc b⁻¹ b h,
              inv_mul_cancel, one_mul]]
      _ = a⁻¹ * (u * h * u⁻¹) := conj_cen ha' u h
      _ = a⁻¹ * (a * h) := by rw [R1]
      _ = h := by group
  calc ⁅u, v⁆ * h = (⁅u, v⁆ * h * ⁅u, v⁆⁻¹) * ⁅u, v⁆ := by group
    _ = h * ⁅u, v⁆ := by rw [hwh]


theorem comm_cen_factor {j k z w : M6} (hz : z ∈ Zs) (hw : w ∈ Zs) :
    ⁅j * z, k * w⁆ = ⁅j, k⁆ := by
  have hz1 : z * (k * w) * z⁻¹ = k * w := by
    rw [Zs_central hz (k * w), mul_assoc, mul_inv_cancel, mul_one]
  have hw1 : ∀ x : M6, w * x * w⁻¹ = x := fun x => by
    rw [Zs_central hw x, mul_assoc, mul_inv_cancel, mul_one]
  rw [commutatorElement_def, commutatorElement_def]
  calc j * z * (k * w) * (j * z)⁻¹ * (k * w)⁻¹
      = j * (z * (k * w) * z⁻¹) * j⁻¹ * w⁻¹ * k⁻¹ := by group
    _ = j * (k * w) * j⁻¹ * w⁻¹ * k⁻¹ := by rw [hz1]
    _ = j * k * (w * j⁻¹ * w⁻¹) * k⁻¹ := by group
    _ = j * k * j⁻¹ * k⁻¹ := by rw [hw1 j⁻¹]

theorem perfect_triv_S6 {Ē : Subgroup S6} (hcomm : ∀ x ∈ Ē, ∀ y ∈ Ē, x * y = y * x)
    (hexp : ∀ x ∈ Ē, x ^ 3 = 1) (hcardĒ : Nat.card Ē = 9) {P : Subgroup S6}
    (hP : ⁅P, P⁆ = P) (hPC : ∀ x ∈ P, ∀ y ∈ Ē, x * y = y * x) : P = ⊥ := by
  have hsurj : Function.Surjective piS := QuotientGroup.mk'_surjective Zs
  set Pt : Subgroup M6 := P.comap piS with hPt
  set J : Subgroup M6 := ⁅Pt, Pt⁆ with hJ
  have hJC : ∀ u ∈ J, ∀ h ∈ Eh Ē, u * h = h * u := by
    have hle : J ≤ Subgroup.centralizer (Eh Ē : Set M6) := by
      rw [hJ]
      refine Subgroup.commutator_le.2 (fun u hu v hv => ?_)
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have ha : ⁅u, h⁆ ∈ Zs := by
        rw [← piS_eq_one, map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.2 (hPC _ hu _ hh)
      have hb : ⁅v, h⁆ ∈ Zs := by
        rw [← piS_eq_one, map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.2 (hPC _ hv _ hh)
      exact (comm_comm_of ha hb).symm
    intro u hu h hh
    exact (Subgroup.mem_centralizer_iff.1 (hle hu) h hh).symm
  have hJperf : ⁅J, J⁆ = J := by
    apply le_antisymm
    · refine Subgroup.commutator_le.2 (fun a ha b hb => ?_)
      rw [commutatorElement_def]
      exact J.mul_mem (J.mul_mem (J.mul_mem ha hb) (J.inv_mem ha)) (J.inv_mem hb)
    · have hPJ : J.map piS = P := by
        rw [hJ, Subgroup.map_commutator, hPt, Subgroup.map_comap_eq_self_of_surjective hsurj]
        exact hP
      have hcover : ∀ u ∈ Pt, ∃ j ∈ J, j⁻¹ * u ∈ Zs := by
        intro u hu
        have hmem : piS u ∈ J.map piS := by rw [hPJ]; exact hu
        obtain ⟨j, hj, hjeq⟩ := Subgroup.mem_map.1 hmem
        refine ⟨j, hj, piS_eq_one.1 ?_⟩
        rw [map_mul, map_inv, hjeq, inv_mul_cancel]
      refine Subgroup.commutator_le.2 (fun u hu v hv => ?_)
      obtain ⟨j, hj, hjz⟩ := hcover u hu
      obtain ⟨k, hk, hkw⟩ := hcover v hv
      have hu_eq : u = j * (j⁻¹ * u) := by group
      have hv_eq : v = k * (k⁻¹ * v) := by group
      rw [hu_eq, hv_eq, comm_cen_factor hjz hkw]
      exact Subgroup.commutator_mem_commutator hj hk
  have hcard27 : 9 < Nat.card (Eh Ē) := by rw [card_Eh, hcardĒ]; norm_num
  obtain ⟨g, hgÊ, hgZ, hg3⟩ := exists_split hcomm hexp hcardĒ
  have hJbot : J = ⊥ :=
    key_bot hJperf (fun h hh k hk => Eh_comm hcomm hh hk) (fun h hh => Eh_cube hexp hh) hcard27 hJC
      hgÊ hgZ hg3
  rw [← hP]
  refine le_antisymm ?_ bot_le
  refine Subgroup.commutator_le.2 (fun x hx y hy => ?_)
  obtain ⟨u, rfl⟩ := hsurj x
  obtain ⟨v, rfl⟩ := hsurj y
  have huJ : ⁅u, v⁆ ∈ J := Subgroup.commutator_mem_commutator hx hy
  rw [hJbot, Subgroup.mem_bot] at huJ
  rw [Subgroup.mem_bot, ← map_commutatorElement, huJ, map_one]

theorem solvable_centralizer {Ē : Subgroup S6} (hcomm : ∀ x ∈ Ē, ∀ y ∈ Ē, x * y = y * x)
    (hexp : ∀ x ∈ Ē, x ^ 3 = 1) (hcardĒ : Nat.card Ē = 9) :
    Group.IsSolvable (Subgroup.centralizer (Ē : Set S6)) := by
  apply isSolvable_of_no_perfect
  intro K hK
  have hPperf : ⁅K.map (Subgroup.centralizer (Ē : Set S6)).subtype,
      K.map (Subgroup.centralizer (Ē : Set S6)).subtype⁆ =
      K.map (Subgroup.centralizer (Ē : Set S6)).subtype := by
    rw [← Subgroup.map_commutator, hK]
  have hP := perfect_triv_S6 hcomm hexp hcardĒ hPperf (fun x hx y hy => by
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hx
    exact (Subgroup.mem_centralizer_iff.1 k.2 y hy).symm)
  rw [Subgroup.eq_bot_iff_forall]
  intro k hk
  have hmem : (k : S6) ∈ K.map (Subgroup.centralizer (Ē : Set S6)).subtype :=
    Subgroup.mem_map_of_mem _ hk
  rw [hP, Subgroup.mem_bot] at hmem
  exact Subgroup.mem_bot.2 (Subtype.ext hmem)


end CFSG.LocalAnalysis.GLTheoremA.I269Six
