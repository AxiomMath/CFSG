module

public import CFSG.GH74.GLS.LU.Local.FiveSL3

public section

open scoped MatrixGroups Matrix

namespace CFSG.GH74.GLS.LU.Local.Five

namespace E125

variable {G : Type} [Group G]

abbrev Vec : Type := Fin 3 → ZMod 5

structure Frame (E : Subgroup G) (x : Fin 3 → G) : Prop where
  closure_eq : Subgroup.closure (Set.range x) = E
  comm : ∀ i j, x i * x j = x j * x i
  pow_five : ∀ i, x i ^ 5 = 1
  card : Nat.card E = 125

section Coord

variable {x : Fin 3 → G}

@[expose] def coord (x : Fin 3 → G) (a : Vec) : G :=
  x 0 ^ (a 0).val * x 1 ^ (a 1).val * x 2 ^ (a 2).val

theorem pow_val_add {g : G} (hg : g ^ 5 = 1) (a b : ZMod 5) :
    g ^ (a + b).val = g ^ a.val * g ^ b.val := by
  rw [ZMod.val_add, ← pow_eq_pow_mod _ hg, pow_add]

theorem mul_rearr {M : Type} [Monoid M] {p0 p1 p2 q0 q1 q2 : M} (h1 : p2 * q0 = q0 * p2)
    (h2 : p1 * q0 = q0 * p1) (h3 : p2 * q1 = q1 * p2) :
    p0 * p1 * p2 * (q0 * q1 * q2) = p0 * q0 * (p1 * q1) * (p2 * q2) := by
  calc p0 * p1 * p2 * (q0 * q1 * q2) = p0 * p1 * (p2 * q0) * q1 * q2 := by simp only [mul_assoc]
    _ = p0 * p1 * (q0 * p2) * q1 * q2 := by rw [h1]
    _ = p0 * (p1 * q0) * p2 * q1 * q2 := by simp only [mul_assoc]
    _ = p0 * (q0 * p1) * p2 * q1 * q2 := by rw [h2]
    _ = p0 * q0 * p1 * (p2 * q1) * q2 := by simp only [mul_assoc]
    _ = p0 * q0 * p1 * (q1 * p2) * q2 := by rw [h3]
    _ = p0 * q0 * (p1 * q1) * (p2 * q2) := by simp only [mul_assoc]

theorem coord_add (hcomm : ∀ i j, x i * x j = x j * x i) (hord : ∀ i, x i ^ 5 = 1) (a b : Vec) :
    coord x (a + b) = coord x a * coord x b := by
  have hpp : ∀ i j (m n : ℕ), x i ^ m * x j ^ n = x j ^ n * x i ^ m :=
    fun i j m n => Commute.pow_pow (hcomm i j) m n
  simp only [coord, Pi.add_apply, pow_val_add (hord _)]
  exact (mul_rearr (hpp 2 0 _ _) (hpp 1 0 _ _) (hpp 2 1 _ _)).symm

@[simp] theorem coord_zero : coord x 0 = 1 := by simp [coord]

theorem coord_single (j : Fin 3) (c : ZMod 5) : coord x (Pi.single j c) = x j ^ c.val := by
  fin_cases j <;> simp [coord]

theorem coord_comm (hcomm : ∀ i j, x i * x j = x j * x i) (hord : ∀ i, x i ^ 5 = 1) (a b : Vec) :
    coord x a * coord x b = coord x b * coord x a := by
  rw [← coord_add hcomm hord, ← coord_add hcomm hord, add_comm]

theorem coord_neg (hcomm : ∀ i j, x i * x j = x j * x i) (hord : ∀ i, x i ^ 5 = 1) (a : Vec) :
    coord x (-a) = (coord x a)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← coord_add hcomm hord, neg_add_cancel, coord_zero]

theorem coord_mem {E : Subgroup G} (hxE : Subgroup.closure (Set.range x) = E) (a : Vec) :
    coord x a ∈ E := by
  have hx : ∀ i, x i ∈ E := fun i => hxE ▸ Subgroup.subset_closure ⟨i, rfl⟩
  exact E.mul_mem (E.mul_mem (E.pow_mem (hx 0) _) (E.pow_mem (hx 1) _)) (E.pow_mem (hx 2) _)

theorem exists_coord_eq {E : Subgroup G} (hxE : Subgroup.closure (Set.range x) = E)
    (hcomm : ∀ i j, x i * x j = x j * x i) (hord : ∀ i, x i ^ 5 = 1) {e : G} (he : e ∈ E) :
    ∃ a, coord x a = e := by
  let S : Subgroup G :=
    { carrier := Set.range (coord x)
      one_mem' := ⟨0, coord_zero⟩
      mul_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
        exact ⟨a + b, coord_add hcomm hord a b⟩
      inv_mem' := by
        rintro _ ⟨a, rfl⟩
        exact ⟨-a, coord_neg hcomm hord a⟩ }
  have hx : ∀ i, x i ∈ S := fun i => by
    refine ⟨Pi.single i 1, ?_⟩
    have h1 : (1 : ZMod 5).val = 1 := by decide
    rw [coord_single, h1, pow_one]
  have hle : Subgroup.closure (Set.range x) ≤ S :=
    (Subgroup.closure_le S).mpr (by rintro _ ⟨i, rfl⟩; exact hx i)
  exact hle (hxE ▸ he)

theorem card_vec : Nat.card Vec = 125 := by
  simp [Nat.card_eq_fintype_card, ZMod.card]

theorem coord_bijective {E : Subgroup G} (hF : Frame E x) :
    Function.Bijective (fun a : Vec => (⟨coord x a, coord_mem hF.closure_eq a⟩ : E)) := by
  have hsurj :
      Function.Surjective (fun a : Vec => (⟨coord x a, coord_mem hF.closure_eq a⟩ : E)) := by
    rintro ⟨e, he⟩
    obtain ⟨a, ha⟩ := exists_coord_eq hF.closure_eq hF.comm hF.pow_five he
    exact ⟨a, Subtype.ext ha⟩
  exact hsurj.bijective_of_nat_card_le (by rw [card_vec, hF.card])

theorem coord_injective {E : Subgroup G} (hF : Frame E x) : Function.Injective (coord x) :=
  fun _ _ h => (coord_bijective hF).1 (Subtype.ext h)

@[expose] noncomputable def coordEquiv {E : Subgroup G} (hF : Frame E x) : Vec ≃ E :=
  Equiv.ofBijective _ (coord_bijective hF)

@[expose] noncomputable def uncoord {E : Subgroup G} (hF : Frame E x) (e : E) : Vec :=
  (coordEquiv hF).symm e

theorem coord_uncoord {E : Subgroup G} (hF : Frame E x) (e : E) : coord x (uncoord hF e) = e :=
  congrArg Subtype.val ((coordEquiv hF).apply_symm_apply e)

end Coord

section Conj

variable {E : Subgroup G} {x : Fin 3 → G}

abbrev Nrm (E : Subgroup G) : Subgroup G := Subgroup.normalizer (E : Set G)

theorem conj_mem {m : G} (hm : m ∈ Nrm E) {e : G} (he : e ∈ E) : m * e * m⁻¹ ∈ E :=
  (Subgroup.mem_normalizer_iff.mp hm e).mp he

@[expose] noncomputable def conjFun (hF : Frame E x) (m : Nrm E) (a : Vec) : Vec :=
  uncoord hF ⟨(m : G) * coord x a * (m : G)⁻¹, conj_mem m.2 (coord_mem hF.closure_eq a)⟩

theorem coord_conjFun (hF : Frame E x) (m : Nrm E) (a : Vec) :
    coord x (conjFun hF m a) = (m : G) * coord x a * (m : G)⁻¹ :=
  coord_uncoord hF _

theorem conjFun_add (hF : Frame E x) (m : Nrm E) (a b : Vec) :
    conjFun hF m (a + b) = conjFun hF m a + conjFun hF m b := by
  apply coord_injective hF
  rw [coord_conjFun, coord_add hF.comm hF.pow_five, coord_add hF.comm hF.pow_five,
    coord_conjFun, coord_conjFun]
  group

theorem conjFun_zero (hF : Frame E x) (m : Nrm E) : conjFun hF m 0 = 0 := by
  apply coord_injective hF
  rw [coord_conjFun, coord_zero]
  group

theorem conjFun_mul (hF : Frame E x) (m m' : Nrm E) (a : Vec) :
    conjFun hF (m * m') a = conjFun hF m (conjFun hF m' a) := by
  apply coord_injective hF
  rw [coord_conjFun, coord_conjFun, coord_conjFun, Subgroup.coe_mul]
  group

theorem conjFun_one (hF : Frame E x) (a : Vec) : conjFun hF 1 a = a := by
  apply coord_injective hF
  rw [coord_conjFun]
  simp

@[expose] noncomputable def conjV (hF : Frame E x) (m : Nrm E) : Vec →+ Vec where
  toFun := conjFun hF m
  map_zero' := conjFun_zero hF m
  map_add' := conjFun_add hF m

end Conj

section Rho

variable {E : Subgroup G} {x : Fin 3 → G}

@[expose] noncomputable def rhoM (hF : Frame E x) :
    Nrm E →* Matrix (Fin 3) (Fin 3) (ZMod 5) where
  toFun m := LinearMap.toMatrix' ((conjV hF m).toZModLinearMap 5)
  map_one' := by
    have : (conjV hF 1).toZModLinearMap 5 = LinearMap.id :=
      LinearMap.ext fun a => conjFun_one hF a
    rw [this, LinearMap.toMatrix'_id]
  map_mul' m m' := by
    have : (conjV hF (m * m')).toZModLinearMap 5 =
        ((conjV hF m).toZModLinearMap 5).comp ((conjV hF m').toZModLinearMap 5) :=
      LinearMap.ext fun a => conjFun_mul hF m m' a
    rw [this, LinearMap.toMatrix'_comp]

theorem rhoM_mulVec (hF : Frame E x) (m : Nrm E) (v : Vec) :
    rhoM hF m *ᵥ v = conjFun hF m v :=
  LinearMap.toMatrix'_mulVec _ v

@[expose] noncomputable def rho (hF : Frame E x) : Nrm E →* GL (Fin 3) (ZMod 5) :=
  (rhoM hF).toHomUnits

theorem coe_rho (hF : Frame E x) (m : Nrm E) :
    ((rho hF m : GL (Fin 3) (ZMod 5)) : Matrix (Fin 3) (Fin 3) (ZMod 5)) = rhoM hF m := rfl

theorem coord_rho_mulVec (hF : Frame E x) (m : Nrm E) (v : Vec) :
    coord x ((rho hF m : Matrix (Fin 3) (Fin 3) (ZMod 5)) *ᵥ v) =
      (m : G) * coord x v * (m : G)⁻¹ := by
  rw [coe_rho, rhoM_mulVec, coord_conjFun]

theorem matrix_ext_single {M M' : Matrix (Fin 3) (Fin 3) (ZMod 5)}
    (h : ∀ b, M *ᵥ Pi.single b 1 = M' *ᵥ Pi.single b 1) : M = M' :=
  Matrix.ext fun a b => by simpa [Matrix.mulVec_single_one] using congrFun (h b) a

theorem comm_of_mem (hF : Frame E x) {e e' : G} (he : e ∈ E) (he' : e' ∈ E) :
    e * e' = e' * e := by
  obtain ⟨a, rfl⟩ := exists_coord_eq hF.closure_eq hF.comm hF.pow_five he
  obtain ⟨b, rfl⟩ := exists_coord_eq hF.closure_eq hF.comm hF.pow_five he'
  exact coord_comm hF.comm hF.pow_five a b

theorem rho_eq_one_iff (hF : Frame E x) (hC : ∀ m ∈ Nrm E, (∀ e ∈ E, m * e = e * m) → m ∈ E)
    (m : Nrm E) : rho hF m = 1 ↔ (m : G) ∈ E := by
  constructor
  · intro h
    refine hC m m.2 fun e he => ?_
    obtain ⟨a, rfl⟩ := exists_coord_eq hF.closure_eq hF.comm hF.pow_five he
    have h1 : (rho hF m : Matrix (Fin 3) (Fin 3) (ZMod 5)) *ᵥ a = a := by
      rw [h]; simp
    have h2 := coord_rho_mulVec hF m a
    rw [h1] at h2
    calc (m : G) * coord x a = ((m : G) * coord x a * (m : G)⁻¹) * m := by group
      _ = coord x a * m := by rw [← h2]
  · intro hm
    refine Units.ext (matrix_ext_single fun b => ?_)
    apply coord_injective hF
    rw [coord_rho_mulVec]
    have hc := comm_of_mem hF hm (coord_mem hF.closure_eq (Pi.single b (1 : ZMod 5)))
    simp only [Units.val_one, Matrix.one_mulVec]
    rw [hc]
    group

end Rho

section Transvections

variable {E : Subgroup G} {x : Fin 3 → G}

@[expose] def tr (i : Fin 3) (γ : Fin 3 → ZMod 5) : Matrix (Fin 3) (Fin 3) (ZMod 5) :=
  Matrix.of fun a b => (1 : Matrix (Fin 3) (Fin 3) (ZMod 5)) a b + if a = i then γ b else 0

theorem tr_mulVec_single (i : Fin 3) (γ : Fin 3 → ZMod 5) (b : Fin 3) :
    tr i γ *ᵥ Pi.single b 1 = Pi.single b 1 + Pi.single i (γ b) := by
  ext a
  simp [tr, Matrix.one_apply, Pi.single_apply]

theorem tr_apply_of_ne {i b : Fin 3} (hb : i ≠ b) (γ : Fin 3 → ZMod 5) : tr i γ i b = γ b := by
  simp [tr, Matrix.one_apply, hb]

theorem tr_pi_single (i j : Fin 3) (a : ZMod 5) :
    tr i (Pi.single j a) = 1 + Matrix.single i j a := by
  ext p q
  by_cases hp : p = i <;> by_cases hq : q = j <;>
    simp [tr, Matrix.single_apply, Pi.single_apply, hp, hq, eq_comm, ite_and]

theorem rho_shape (hF : Frame E x) (i : Fin 3) (r : Nrm E)
    (hRx : (r : G) * x i * (r : G)⁻¹ = x i)
    (hRc : ∀ j, ∃ c : ℕ, (r : G) * x j * (r : G)⁻¹ = x j * x i ^ c) :
    ∃ γ : Fin 3 → ZMod 5, γ i = 0 ∧
      (rho hF r : Matrix (Fin 3) (Fin 3) (ZMod 5)) = tr i γ := by
  choose c hc using hRc
  have h1 : (1 : ZMod 5).val = 1 := by decide
  refine ⟨fun b => if b = i then 0 else (c b : ZMod 5), by simp, ?_⟩
  refine matrix_ext_single fun b => ?_
  rw [tr_mulVec_single]
  apply coord_injective hF
  rw [coord_rho_mulVec, coord_add hF.comm hF.pow_five, coord_single, coord_single, h1, pow_one]
  by_cases hb : b = i
  · subst hb
    simp [hRx]
  · simp only [hb, ite_false, ZMod.val_natCast, hc b]
    rw [← pow_eq_pow_mod _ (hF.pow_five i)]

private theorem mem_sup_mul {E L : Subgroup G} (h : ∀ l ∈ L, ∀ e ∈ E, l * e * l⁻¹ ∈ E) {y : G}
    (hy : y ∈ E ⊔ L) : ∃ e ∈ E, ∃ l ∈ L, y = e * l := by
  let S : Subgroup G :=
    { carrier := {y | ∃ e ∈ E, ∃ l ∈ L, y = e * l}
      one_mem' := ⟨1, E.one_mem, 1, L.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨e, he, l, hl, rfl⟩ ⟨e', he', l', hl', rfl⟩
        refine ⟨e * (l * e' * l⁻¹), E.mul_mem he (h l hl e' he'), l * l', L.mul_mem hl hl', ?_⟩
        group
      inv_mem' := by
        rintro _ ⟨e, he, l, hl, rfl⟩
        refine ⟨l⁻¹ * e⁻¹ * l⁻¹⁻¹, h l⁻¹ (L.inv_mem hl) e⁻¹ (E.inv_mem he), l⁻¹, L.inv_mem hl, ?_⟩
        group }
  have hE : E ≤ S := fun e he => ⟨e, he, 1, L.one_mem, by simp⟩
  have hL : L ≤ S := fun l hl => ⟨1, E.one_mem, l, hl, by simp⟩
  exact sup_le hE hL hy

theorem shape_of_mem_sup (hF : Frame E x)
    (hC : ∀ m ∈ Nrm E, (∀ e ∈ E, m * e = e * m) → m ∈ E) {i : Fin 3} {R' : Subgroup G}
    (hRN : R' ≤ Nrm E) (hRx : ∀ r ∈ R', r * x i * r⁻¹ = x i)
    (hRc : ∀ r ∈ R', ∀ j, ∃ c : ℕ, r * x j * r⁻¹ = x j * x i ^ c) (y : Nrm E)
    (hy : (y : G) ∈ R' ⊔ E) :
    ∃ γ : Fin 3 → ZMod 5, γ i = 0 ∧
      (rho hF y : Matrix (Fin 3) (Fin 3) (ZMod 5)) = tr i γ := by
  rw [sup_comm] at hy
  obtain ⟨e, he, r, hr, hyer⟩ := mem_sup_mul (fun l hl e he => conj_mem (hRN hl) he) hy
  have hy' : y = (⟨e, Subgroup.le_normalizer he⟩ : Nrm E) * ⟨r, hRN hr⟩ := Subtype.ext hyer
  obtain ⟨γ, h0, hγ⟩ := rho_shape hF i ⟨r, hRN hr⟩ (hRx r hr) (hRc r hr)
  refine ⟨γ, h0, ?_⟩
  have hker : rho hF ⟨e, Subgroup.le_normalizer he⟩ = 1 := (rho_eq_one_iff hF hC _).mpr he
  rw [hy', map_mul, hker, one_mul]
  exact hγ

theorem card_range_comp_rho (hF : Frame E x)
    (hC : ∀ m ∈ Nrm E, (∀ e ∈ E, m * e = e * m) → m ∈ E) {X : Subgroup G} (hX : X ≤ Nrm E)
    (hEX : E ≤ X) :
    Nat.card ((rho hF).comp (Subgroup.inclusion hX)).range * 125 = Nat.card X := by
  set f := (rho hF).comp (Subgroup.inclusion hX) with hf
  have hker : f.ker = E.subgroupOf X := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact rho_eq_one_iff hF hC _
  have h1 := Subgroup.index_ker f
  have h2 := Subgroup.index_mul_card f.ker
  have h3 : Nat.card f.ker = 125 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEX).toEquiv, hF.card]
  rw [h1, h3] at h2
  exact h2

theorem transvection_mem_range (hF : Frame E x)
    (hC : ∀ m ∈ Nrm E, (∀ e ∈ E, m * e = e * m) → m ∈ E) {i j k : Fin 3} (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) (hcov : ∀ l, l = i ∨ l = j ∨ l = k) {R' : Subgroup G}
    (hRN : R' ≤ Nrm E) (hRx : ∀ r ∈ R', r * x i * r⁻¹ = x i)
    (hRc : ∀ r ∈ R', ∀ j, ∃ c : ℕ, r * x j * r⁻¹ = x j * x i ^ c)
    (hRcard : Nat.card ↥(R' ⊔ E) = 5 ^ 5) (a : ZMod 5) :
    Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij a) ∈
      (rho hF).range := by
  have hX : R' ⊔ E ≤ Nrm E := sup_le hRN E.le_normalizer
  have hEX : E ≤ R' ⊔ E := le_sup_right
  set f := (rho hF).comp (Subgroup.inclusion hX) with hf
  have hcard : Nat.card f.range = 25 := by
    have h : Nat.card f.range * 125 = Nat.card ↥(R' ⊔ E) := card_range_comp_rho hF hC hX hEX
    rw [hRcard] at h
    omega
  have hshape : ∀ g ∈ f.range, ∃ γ : Fin 3 → ZMod 5, γ i = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) = tr i γ := by
    rintro _ ⟨y, rfl⟩
    exact shape_of_mem_sup hF hC hRN hRx hRc (Subgroup.inclusion hX y) y.2
  let param : f.range → ZMod 5 × ZMod 5 := fun g =>
    ((g.1 : Matrix (Fin 3) (Fin 3) (ZMod 5)) i j, (g.1 : Matrix (Fin 3) (Fin 3) (ZMod 5)) i k)
  have hparam : ∀ (g : f.range) (γ : Fin 3 → ZMod 5),
      (g.1 : Matrix (Fin 3) (Fin 3) (ZMod 5)) = tr i γ → param g = (γ j, γ k) := by
    intro g γ hg
    simp only [param, hg, tr_apply_of_ne hij, tr_apply_of_ne hik]
  have hinj : Function.Injective param := by
    intro g g' h
    obtain ⟨γ, h0, hg⟩ := hshape g.1 g.2
    obtain ⟨γ', h0', hg'⟩ := hshape g'.1 g'.2
    rw [hparam g γ hg, hparam g' γ' hg'] at h
    have hγ : γ = γ' := by
      funext l
      rcases hcov l with h1 | h1 | h1 <;> rw [h1]
      · rw [h0, h0']
      · exact (Prod.ext_iff.mp h).1
      · exact (Prod.ext_iff.mp h).2
    subst hγ
    exact Subtype.ext (Units.ext (hg.trans hg'.symm))
  have hbij : Function.Bijective param := by
    refine hinj.bijective_of_nat_card_le ?_
    rw [hcard]
    simp
  obtain ⟨g, hg⟩ := hbij.2 (a, 0)
  obtain ⟨γ, h0, hγ⟩ := hshape g.1 g.2
  rw [hparam g γ hγ] at hg
  have hja : γ j = a := (Prod.ext_iff.mp hg).1
  have hk0 : γ k = 0 := (Prod.ext_iff.mp hg).2
  have hγeq : γ = Pi.single j a := by
    funext l
    rcases hcov l with h1 | h1 | h1 <;> rw [h1]
    · simp [h0, hij]
    · simpa using hja
    · simpa [hjk.symm] using hk0
  have hgT : g.1 =
      Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij a) := by
    refine Units.ext ?_
    rw [hγ, hγeq, tr_pi_single, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      Matrix.SpecialLinearGroup.transvection_coe]
  rw [← hgT]
  obtain ⟨y, hy⟩ := g.2
  exact ⟨Subgroup.inclusion hX y, hy⟩

theorem exists_third (i j : Fin 3) (hij : i ≠ j) :
    ∃ k : Fin 3, i ≠ k ∧ j ≠ k ∧ ∀ l, l = i ∨ l = j ∨ l = k := by
  revert i j
  decide

end Transvections

end E125

end CFSG.GH74.GLS.LU.Local.Five
