module

public import CFSG.Quasithin.H13.GoldschmidtCTKFamL5Quo
public import Mathlib.Algebra.Field.ZMod

public section

open CFSG.Quasithin.H13.CTK.L5

local instance CFSG.HardMathSupport.Cooperstein.Proving.instFactPrimeTwo : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

namespace CFSG.HardMathSupport.Cooperstein.Proving

variable {V : Type} [CommGroup V] [Module (ZMod 2) (Additive V)]

theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

@[expose] def natAdd (φ : MulAut V) : Additive V ≃+ Additive V :=
  MulEquiv.toAdditive (φ : V ≃* V)

theorem natAdd_smul (φ : MulAut V) (c : ZMod 2) (w : Additive V) :
    natAdd φ (c • w) = c • natAdd φ w := by
  rcases zmod2_cases c with rfl | rfl
  · simp
  · simp

@[expose] def natEquiv (φ : MulAut V) : Additive V ≃ₗ[ZMod 2] Additive V :=
  (natAdd φ).toLinearEquiv (natAdd_smul φ)

theorem natEquiv_apply (φ : MulAut V) (w : Additive V) :
    natEquiv φ w = Additive.ofMul (φ (Additive.toMul w)) := rfl

@[expose] def natAct : MulAut V →* (Additive V ≃ₗ[ZMod 2] Additive V) where
  toFun := natEquiv
  map_one' := by
    ext w
    rfl
  map_mul' φ ψ := by
    ext w
    rfl

theorem mem_fixV_iff (S : Subgroup (MulAut V)) (v : V) :
    Additive.ofMul v ∈ fixV (K := ZMod 2) (natAct (V := V)) S ↔ ∀ g ∈ S, g v = v := by
  show (∀ g ∈ S, natEquiv g (Additive.ofMul v) = Additive.ofMul v) ↔ _
  constructor
  · intro h g hg
    have := h g hg
    rw [natEquiv_apply] at this
    exact Additive.ofMul.injective this
  · intro h g hg
    show Additive.ofMul (g v) = Additive.ofMul v
    rw [h g hg]

theorem fixV_eq_bot_iff (S : Subgroup (MulAut V)) :
    fixV (K := ZMod 2) (natAct (V := V)) S = ⊥ ↔ ∀ v : V, (∀ g ∈ S, g v = v) → v = 1 := by
  constructor
  · intro h v hv
    have hmem := (mem_fixV_iff S v).2 hv
    rw [h, Submodule.mem_bot] at hmem
    exact Additive.ofMul.injective (hmem.trans rfl)
  · intro h
    rw [eq_bot_iff]
    intro w hw
    rw [Submodule.mem_bot]
    have hv : Additive.toMul w = 1 := by
      apply h
      intro g hg
      have this : natEquiv g w = w := hw g hg
      rw [natEquiv_apply] at this
      exact Additive.toMul.injective (congrArg Additive.toMul this)
    exact (Additive.toMul.injective hv).trans rfl

theorem two_pow_mod_three_even (d : ℕ) (h : 2 ^ d % 3 = 1) : Even d := by
  rcases Nat.even_or_odd d with he | ho
  · exact he
  · exfalso
    obtain ⟨k, rfl⟩ := ho
    have h4 : 4 ^ k % 3 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    have : 2 ^ (2 * k + 1) = 2 * 4 ^ k := by
      rw [pow_succ, pow_mul]
      norm_num
      ring
    rw [this] at h
    generalize 4 ^ k = t at h h4
    omega

def Cen (g : MulAut V) : Subgroup V where
  carrier := {v | g v = v}
  mul_mem' := fun {u w} (hu : g u = u) (hw : g w = w) => show g (u * w) = u * w from by
    rw [map_mul, hu, hw]
  one_mem' := show g 1 = 1 from map_one g
  inv_mem' := fun {u} (hu : g u = u) => show g u⁻¹ = u⁻¹ from by
    rw [map_inv, hu]

theorem mem_Cen (g : MulAut V) (v : V) : v ∈ Cen g ↔ g v = v := Iff.rfl

theorem fixed_zpowers (φ : MulAut V) (v : V) (h : φ v = v) :
    ∀ g ∈ Subgroup.zpowers φ, g v = v := fun g hg =>
  MulAction.mem_stabilizer_iff.1 (Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 h) hg)

theorem fixV_zpowers_iff (φ : MulAut V) (v : V) :
    Additive.ofMul v ∈ fixV (K := ZMod 2) (natAct (V := V)) (Subgroup.zpowers φ) ↔ φ v = v := by
  rw [mem_fixV_iff]
  exact ⟨fun h => h φ (Subgroup.mem_zpowers φ), fun h => fixed_zpowers φ v h⟩

theorem card_fixV_zpowers (φ : MulAut V) [Finite V] :
    Nat.card ↥(fixV (K := ZMod 2) (natAct (V := V)) (Subgroup.zpowers φ)) = Nat.card ↥(Cen φ) := by
  refine Nat.card_congr (Equiv.subtypeEquiv Additive.toMul ?_)
  intro w
  have := fixV_zpowers_iff φ (Additive.toMul w)
  rw [mem_Cen]
  simpa using this

theorem card_Cen_conj (x a : MulAut V) [Finite V] :
    Nat.card ↥(Cen (x * a * x⁻¹)) = Nat.card ↥(Cen a) := by
  have h1 : ∀ v : V, (x * a * x⁻¹) (x v) = x (a v) := fun v => by
    simp [MulAut.mul_apply, MulAut.inv_apply]
  have h : ∀ v : V, v ∈ Cen a ↔ x v ∈ Cen (x * a * x⁻¹) := fun v => by
    rw [mem_Cen, mem_Cen, h1, EmbeddingLike.apply_eq_iff_eq]
  exact (Nat.card_congr (Equiv.subtypeEquiv (x : V ≃* V).toEquiv h)).symm

theorem Cen_inf_trivial (x a a' : MulAut V)
    (hx : ∀ v : V, (∀ g ∈ Subgroup.zpowers x, g v = v) → v = 1)
    (hprod : a * a' = x) :
    ∀ v : V, v ∈ Cen a → v ∈ Cen a' → v = 1 := by
  intro v hv hv'
  apply hx v
  apply fixed_zpowers x v
  rw [← hprod]
  show (a * a') v = v
  rw [MulAut.mul_apply]
  have h' : a' v = v := hv'
  rw [h', hv]

theorem card_mul_le_card (a a' : MulAut V) [Finite V]
    (hI : ∀ v : V, v ∈ Cen a → v ∈ Cen a' → v = 1) :
    Nat.card ↥(Cen a) * Nat.card ↥(Cen a') ≤ Nat.card V := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun p : ↥(Cen a) × ↥(Cen a') => (p.1 : V) * (p.2 : V)) ?_
  rintro ⟨c, c'⟩ ⟨d, d'⟩ h
  have h' : (c : V) * (c' : V) = (d : V) * (d' : V) := h
  have h2 : (d : V)⁻¹ * (c : V) = (d' : V) * (c' : V)⁻¹ := by
    calc (d : V)⁻¹ * (c : V) = (d : V)⁻¹ * ((c : V) * (c' : V)) * (c' : V)⁻¹ := by group
      _ = (d : V)⁻¹ * ((d : V) * (d' : V)) * (c' : V)⁻¹ := by rw [h']
      _ = (d' : V) * (c' : V)⁻¹ := by group
  have hL : (d : V)⁻¹ * (c : V) ∈ Cen a :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ d.2) c.2
  have hR : (d' : V) * (c' : V)⁻¹ ∈ Cen a' :=
    Subgroup.mul_mem _ d'.2 (Subgroup.inv_mem _ c'.2)
  have hL' : (d' : V) * (c' : V)⁻¹ ∈ Cen a := h2 ▸ hL
  have h1 : (d' : V) * (c' : V)⁻¹ = 1 := hI _ hL' hR
  have hd : (d' : V) = (c' : V) := mul_inv_eq_one.1 h1
  have h3 : (d : V)⁻¹ * (c : V) = 1 := by rw [h2, h1]
  have hc : (d : V) = (c : V) := inv_mul_eq_one.1 h3
  exact Prod.ext (Subtype.ext hc.symm) (Subtype.ext hd.symm)

theorem card_le_sq [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (a : MulAut V) (ha : a ^ 2 = 1) :
    Nat.card V ≤ Nat.card ↥(Cen a) * Nat.card ↥(Cen a) := by
  let f0 : V →* V := MonoidHom.mk' (fun v : V => v⁻¹ * a v) (fun u v => by
    simp only [map_mul, mul_inv]
    ac_rfl)
  have hinv : ∀ u : V, u⁻¹ = u := fun u => inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hV u)
  have hsq : ∀ u : V, a (a u) = u := fun u => by
    have := congrArg (fun g : MulAut V => g u) ha
    simpa [pow_two, MulAut.mul_apply] using this
  have hker : f0.ker = Cen a := by
    ext v
    rw [MonoidHom.mem_ker, mem_Cen]
    show v⁻¹ * a v = 1 ↔ a v = v
    rw [inv_mul_eq_one, eq_comm]
  have hrange : f0.range ≤ Cen a := by
    rintro _ ⟨v, rfl⟩
    rw [mem_Cen]
    show a (v⁻¹ * a v) = v⁻¹ * a v
    rw [map_mul, map_inv, hsq, hinv (a v), hinv v]
    exact mul_comm _ _
  have h1 := Subgroup.card_mul_index f0.ker
  rw [Subgroup.index_ker, hker] at h1
  rw [← h1]
  exact Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hrange)

theorem card_fixV_sq_eq_of_inverts [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (a x : MulAut V)
    (ha : a ^ 2 = 1) (hx3 : x ^ 3 = 1) (hinv : a * x * a⁻¹ = x⁻¹)
    (hx : CFSG.Quasithin.H13.CTK.L5.fixV (K := ZMod 2) (natAct (V := V))
      (Subgroup.zpowers x) = ⊥) :
    Nat.card (CFSG.Quasithin.H13.CTK.L5.fixV (K := ZMod 2) (natAct (V := V))
      (Subgroup.zpowers a)) ^ 2 = Nat.card V := by
  have hx' := (fixV_eq_bot_iff _).1 hx
  have hax : a * x = x⁻¹ * a := mul_inv_eq_iff_eq_mul.1 hinv
  have hxx : x⁻¹ * x⁻¹ = x := by
    calc x⁻¹ * x⁻¹ = x⁻¹ * x⁻¹ * x ^ 3 := by rw [hx3, mul_one]
      _ = x := by group
  have hprod : a * (x * a * x⁻¹) = x := by
    calc a * (x * a * x⁻¹) = (a * x) * a * x⁻¹ := by group
      _ = x⁻¹ * (a * a) * x⁻¹ := by rw [hax]; group
      _ = x⁻¹ * x⁻¹ := by rw [← sq, ha, mul_one]
      _ = x := hxx
  have hI := Cen_inf_trivial x a (x * a * x⁻¹) hx' hprod
  have hc' := card_Cen_conj x a
  rw [card_fixV_zpowers a, sq]
  apply le_antisymm
  · have h1 := card_mul_le_card a (x * a * x⁻¹) hI
    rw [hc'] at h1
    exact h1
  · exact card_le_sq hV a ha

@[expose] def Nh (h : MulAut V) : V →* V :=
  MonoidHom.mk' (fun v : V => v * h v * h (h v)) (fun u v => by
    simp only [map_mul]
    ac_rfl)

theorem Nh_apply (h : MulAut V) (v : V) : Nh h v = v * h v * h (h v) := rfl

theorem Nh_fixed (h : MulAut V) (hh3 : ∀ u : V, h (h (h u)) = u) (v : V) :
    h (Nh h v) = Nh h v := by
  rw [Nh_apply, map_mul, map_mul, hh3]
  ac_rfl

theorem Nh_of_fixed (h : MulAut V) (hV : ∀ v : V, v ^ 2 = 1) (c : V) (hc : h c = c) :
    Nh h c = c := by
  have hc2 : c * c = 1 := by rw [← pow_two]; exact hV c
  rw [Nh_apply, hc, hc, hc2, one_mul]

theorem Nh_comm (k h : MulAut V) (hkh : k * h = h * k) (v : V) :
    k (Nh h v) = Nh h (k v) := by
  have hk : ∀ u : V, k (h u) = h (k u) := fun u => by
    have := congrArg (fun g : MulAut V => g u) hkh
    simpa [MulAut.mul_apply] using this
  rw [Nh_apply, Nh_apply, map_mul, map_mul]
  simp only [hk]

theorem Nh_Nh_eq_one (h k : MulAut V) (hhk : h * k = k * h)
    (hh3 : ∀ u : V, h (h (h u)) = u) (hk3 : ∀ u : V, k (k (k u)) = u)
    (hfree : ∀ w : V, (∀ g ∈ Subgroup.closure ({h, k} : Set (MulAut V)), g w = w) → w = 1)
    (v : V) : Nh h (Nh k v) = 1 := by
  have hw : ∀ g ∈ Subgroup.closure ({h, k} : Set (MulAut V)),
      g (Nh h (Nh k v)) = Nh h (Nh k v) := by
    intro g hg
    refine MulAction.mem_stabilizer_iff.1 ((Subgroup.closure_le _).2 ?_ hg)
    intro g' hg'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg'
    rcases hg' with e | e <;> rw [e]
    · exact MulAction.mem_stabilizer_iff.2 (Nh_fixed h hh3 _)
    · refine MulAction.mem_stabilizer_iff.2 ?_
      show k (Nh h (Nh k v)) = Nh h (Nh k v)
      rw [Nh_comm k h hhk.symm (Nh k v), Nh_fixed k hk3 v]
  exact hfree _ hw

theorem comm_apply_of (x y : MulAut V) (hxy : x * y = y * x) (u : V) :
    y (x u) = x (y u) := by
  have := congrArg (fun g : MulAut V => g u) hxy.symm
  simpa [MulAut.mul_apply] using this

theorem Nh_prod_four (x y : MulAut V) (hxy : x * y = y * x)
    (hy3 : ∀ u : V, y (y (y u)) = u) (v : V) :
    Nh x v * Nh y v * Nh (x * y) v * Nh (x * y ^ 2) v =
      v * Nh x (Nh y v) * (v * v) := by
  have hc := comm_apply_of x y hxy
  have e2 : ∀ u : V, (x * y ^ 2) u = x (y (y u)) := fun u => by
    simp only [sq, MulAut.mul_apply]
  simp only [Nh_apply, e2, MulAut.mul_apply, map_mul, hc, hy3]
  ac_rfl

theorem sq_eq_one_mod (v : V) : v ^ 2 = 1 := by
  have h0 : ((2 : ℕ) : ZMod 2) = 0 := rfl
  have h : (2 : ℕ) • Additive.ofMul v = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2), h0, zero_smul]
  have h' : Additive.ofMul (v ^ 2) = 0 := by
    rw [ofMul_pow]; exact h
  exact ofMul_eq_zero.1 h'

theorem apply_cube_of (g : MulAut V) (hg : g ^ 3 = 1) (u : V) : g (g (g u)) = u := by
  have := congrArg (fun k : MulAut V => k u) hg
  simpa [pow_three, mul_assoc, MulAut.mul_apply] using this

theorem mul_comm_of_apply (a b : MulAut V) (h : ∀ v : V, a (b v) = b (a v)) : a * b = b * a := by
  apply MulEquiv.ext
  intro v
  show a (b v) = b (a v)
  exact h v

theorem mem_pair_fst (a b : MulAut V) : a ∈ Subgroup.closure ({a, b} : Set (MulAut V)) :=
  Subgroup.subset_closure (Set.mem_insert _ _)

theorem mem_pair_snd (a b : MulAut V) : b ∈ Subgroup.closure ({a, b} : Set (MulAut V)) :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem card_fixV_eq_Cen (φ : MulAut V) :
    Nat.card ↥(fixV (K := ZMod 2) (natAct (V := V)) (Subgroup.zpowers φ)) = Nat.card ↥(Cen φ) := by
  refine Nat.card_congr (Equiv.subtypeEquiv Additive.toMul ?_)
  intro w
  have := fixV_zpowers_iff φ (Additive.toMul w)
  rw [mem_Cen]
  simpa using this

theorem fixed_free_of_gen (x y : MulAut V)
    (hE : fixV (K := ZMod 2) (natAct (V := V)) (Subgroup.closure ({x, y} : Set (MulAut V))) = ⊥)
    (h k : MulAut V) (hx : x ∈ Subgroup.closure ({h, k} : Set (MulAut V)))
    (hy : y ∈ Subgroup.closure ({h, k} : Set (MulAut V))) :
    ∀ w : V, (∀ g ∈ Subgroup.closure ({h, k} : Set (MulAut V)), g w = w) → w = 1 := by
  intro w hw
  have hle : Subgroup.closure ({x, y} : Set (MulAut V)) ≤
      Subgroup.closure ({h, k} : Set (MulAut V)) := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with e | e <;> rw [e]
    · exact hx
    · exact hy
  exact (fixV_eq_bot_iff _).1 hE w (fun g hg => hw g (hle hg))

theorem Nh_pair_kill (x y a b : MulAut V)
    (hE : fixV (K := ZMod 2) (natAct (V := V)) (Subgroup.closure ({x, y} : Set (MulAut V))) = ⊥)
    (hab : a * b = b * a) (ha3 : ∀ u : V, a (a (a u)) = u) (hb3 : ∀ u : V, b (b (b u)) = u)
    (hV : ∀ v : V, v ^ 2 = 1)
    (hxa : x ∈ Subgroup.closure ({a, b} : Set (MulAut V)))
    (hyb : y ∈ Subgroup.closure ({a, b} : Set (MulAut V))) :
    (∀ c : V, b c = c → Nh a c = 1) ∧ (∀ c : V, a c = c → Nh b c = 1) := by
  have hf1 := fixed_free_of_gen x y hE a b hxa hyb
  have hf2 := fixed_free_of_gen x y hE b a
    (by rw [Set.pair_comm]; exact hxa) (by rw [Set.pair_comm]; exact hyb)
  have hs1 := Nh_Nh_eq_one a b hab ha3 hb3 hf1
  have hs2 := Nh_Nh_eq_one b a hab.symm hb3 ha3 hf2
  refine ⟨fun c hc => ?_, fun c hc => ?_⟩
  · have := hs1 c
    rwa [Nh_of_fixed b hV c hc] at this
  · have := hs2 c
    rwa [Nh_of_fixed a hV c hc] at this

theorem prod_four_eq (x y : MulAut V)
    (hE : fixV (K := ZMod 2) (natAct (V := V)) (Subgroup.closure ({x, y} : Set (MulAut V))) = ⊥)
    (hV : ∀ v : V, v ^ 2 = 1) (hxy : x * y = y * x)
    (hx3 : ∀ u : V, x (x (x u)) = u) (hy3 : ∀ u : V, y (y (y u)) = u) (v : V) :
    Nh x v * Nh y v * Nh (x * y) v * Nh (x * y ^ 2) v = v := by
  have hfree := fixed_free_of_gen x y hE x y (mem_pair_fst x y) (mem_pair_snd x y)
  rw [Nh_prod_four x y hxy hy3 v, Nh_Nh_eq_one x y hxy hx3 hy3 hfree v]
  have hvv : v * v = 1 := by rw [← pow_two]; exact hV v
  rw [mul_one, hvv, mul_one]

theorem card_eq_mul_fixV_of_three_sq (x y : MulAut V) (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1)
    (hxy : x * y = y * x) (hx1 : x ≠ 1) (hy : y ∉ Subgroup.zpowers x)
    (hE : CFSG.Quasithin.H13.CTK.L5.fixV (K := ZMod 2) (natAct (V := V))
      (Subgroup.closure ({x, y} : Set (MulAut V))) = ⊥) :
    Nat.card V =
      Nat.card ↥(fixV (K := ZMod 2) (natAct (V := V)) (Subgroup.zpowers x)) *
      Nat.card ↥(fixV (K := ZMod 2) (natAct (V := V)) (Subgroup.zpowers y)) *
      Nat.card ↥(fixV (K := ZMod 2) (natAct (V := V)) (Subgroup.zpowers (x * y))) *
      Nat.card ↥(fixV (K := ZMod 2) (natAct (V := V)) (Subgroup.zpowers (x * y ^ 2))) := by
  have hV : ∀ v : V, v ^ 2 = 1 := sq_eq_one_mod
  have hC : Commute x y := hxy
  have hx3f := apply_cube_of x hx3
  have hy3f := apply_cube_of y hy3
  have hcxy3 : (x * y) ^ 3 = 1 := by rw [hC.mul_pow, hx3, hy3, one_mul]
  have hcxy2 : (x * y ^ 2) ^ 3 = 1 := by
    rw [(hC.pow_right 2).mul_pow, hx3, one_mul, pow_right_comm, hy3, one_pow]
  have hxyf := apply_cube_of (x * y) hcxy3
  have hxy2f := apply_cube_of (x * y ^ 2) hcxy2
  have hc := comm_apply_of x y hxy
  have hy_xxy : y ∈ Subgroup.closure ({x, x * y} : Set (MulAut V)) := by
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ (mem_pair_fst x (x * y)))
      (mem_pair_snd x (x * y))
    simpa using this
  have hsq : y ^ 2 ∈ Subgroup.closure ({x, x * y ^ 2} : Set (MulAut V)) := by
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ (mem_pair_fst x (x * y ^ 2)))
      (mem_pair_snd x (x * y ^ 2))
    simpa using this
  have hy_xxy2 : y ∈ Subgroup.closure ({x, x * y ^ 2} : Set (MulAut V)) := by
    have h4 := pow_mem hsq 2
    rwa [show (y ^ 2) ^ 2 = y ^ 3 * y from by group, hy3, one_mul] at h4
  have hx_yxy : x ∈ Subgroup.closure ({y, x * y} : Set (MulAut V)) := by
    have := Subgroup.mul_mem _ (mem_pair_snd y (x * y))
      (Subgroup.inv_mem _ (mem_pair_fst y (x * y)))
    simpa using this
  have e_xy2y : x * y ^ 2 * y = x := by
    rw [show x * y ^ 2 * y = x * y ^ 3 from by group, hy3, mul_one]
  have hx_yxy2 : x ∈ Subgroup.closure ({y, x * y ^ 2} : Set (MulAut V)) := by
    have := Subgroup.mul_mem _ (mem_pair_snd y (x * y ^ 2)) (mem_pair_fst y (x * y ^ 2))
    rwa [e_xy2y] at this
  have hyK : y ∈ Subgroup.closure ({x * y, x * y ^ 2} : Set (MulAut V)) := by
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ (mem_pair_fst (x * y) (x * y ^ 2)))
      (mem_pair_snd (x * y) (x * y ^ 2))
    rwa [show (x * y)⁻¹ * (x * y ^ 2) = y from by group] at this
  have hxK : x ∈ Subgroup.closure ({x * y, x * y ^ 2} : Set (MulAut V)) := by
    have := Subgroup.mul_mem _ (mem_pair_fst (x * y) (x * y ^ 2)) (Subgroup.inv_mem _ hyK)
    simpa using this
  have hab2 : x * (x * y) = (x * y) * x := mul_comm_of_apply _ _ fun v => by
    simp [MulAut.mul_apply, hc, hx3f, hy3f]
  have hab3 : x * (x * y ^ 2) = (x * y ^ 2) * x := mul_comm_of_apply _ _ fun v => by
    simp [sq, MulAut.mul_apply, hc, hx3f, hy3f]
  have hab4 : y * (x * y) = (x * y) * y := mul_comm_of_apply _ _ fun v => by
    simp [MulAut.mul_apply, hc, hx3f, hy3f]
  have hab5 : y * (x * y ^ 2) = (x * y ^ 2) * y := mul_comm_of_apply _ _ fun v => by
    simp [sq, MulAut.mul_apply, hc, hx3f, hy3f]
  have hab6 : (x * y) * (x * y ^ 2) = (x * y ^ 2) * (x * y) := mul_comm_of_apply _ _ fun v => by
    simp [sq, MulAut.mul_apply, hc, hx3f, hy3f]
  have K1 := Nh_pair_kill x y x y hE hxy hx3f hy3f hV (mem_pair_fst x y) (mem_pair_snd x y)
  have K2 := Nh_pair_kill x y x (x * y) hE hab2 hx3f hxyf hV (mem_pair_fst x (x * y)) hy_xxy
  have K3 := Nh_pair_kill x y x (x * y ^ 2) hE hab3 hx3f hxy2f hV
    (mem_pair_fst x (x * y ^ 2)) hy_xxy2
  have K4 := Nh_pair_kill x y y (x * y) hE hab4 hy3f hxyf hV hx_yxy (mem_pair_fst y (x * y))
  have K5 := Nh_pair_kill x y y (x * y ^ 2) hE hab5 hy3f hxy2f hV hx_yxy2
    (mem_pair_fst y (x * y ^ 2))
  have K6 := Nh_pair_kill x y (x * y) (x * y ^ 2) hE hab6 hxyf hxy2f hV hxK hyK
  let F : V → ↥(Cen x) × ↥(Cen y) × ↥(Cen (x * y)) × ↥(Cen (x * y ^ 2)) := fun v =>
    (⟨Nh x v, (mem_Cen _ _).2 (Nh_fixed x hx3f v)⟩,
      ⟨Nh y v, (mem_Cen _ _).2 (Nh_fixed y hy3f v)⟩,
      ⟨Nh (x * y) v, (mem_Cen _ _).2 (Nh_fixed (x * y) hxyf v)⟩,
      ⟨Nh (x * y ^ 2) v, (mem_Cen _ _).2 (Nh_fixed (x * y ^ 2) hxy2f v)⟩)
  have hF : Function.Bijective F := by
    refine ⟨?_, ?_⟩
    · intro v w hvw
      simp only [F, Prod.mk.injEq, Subtype.mk.injEq] at hvw
      obtain ⟨e1, e2, e3, e4⟩ := hvw
      calc v = Nh x v * Nh y v * Nh (x * y) v * Nh (x * y ^ 2) v :=
            (prod_four_eq x y hE hV hxy hx3f hy3f v).symm
        _ = Nh x w * Nh y w * Nh (x * y) w * Nh (x * y ^ 2) w := by rw [e1, e2, e3, e4]
        _ = w := prod_four_eq x y hE hV hxy hx3f hy3f w
    · rintro ⟨⟨c1, hc1⟩, ⟨c2, hc2⟩, ⟨c3, hc3⟩, ⟨c4, hc4⟩⟩
      have hc1' : x c1 = c1 := (mem_Cen _ _).1 hc1
      have hc2' : y c2 = c2 := (mem_Cen _ _).1 hc2
      have hc3' : (x * y) c3 = c3 := (mem_Cen _ _).1 hc3
      have hc4' : (x * y ^ 2) c4 = c4 := (mem_Cen _ _).1 hc4
      refine ⟨c1 * c2 * c3 * c4, ?_⟩
      simp only [F, Prod.mk.injEq, Subtype.mk.injEq]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [map_mul, K1.1 c2 hc2', K2.1 c3 hc3', K3.1 c4 hc4', Nh_of_fixed x hV c1 hc1',
          mul_one, one_mul]
      · simp only [map_mul, K1.2 c1 hc1', K4.1 c3 hc3', K5.1 c4 hc4', Nh_of_fixed y hV c2 hc2',
          mul_one, one_mul]
      · simp only [map_mul, K2.2 c1 hc1', K4.2 c2 hc2', K6.1 c4 hc4', Nh_of_fixed (x * y) hV c3 hc3',
          mul_one, one_mul]
      · simp only [map_mul, K3.2 c1 hc1', K5.2 c2 hc2', K6.2 c3 hc3', Nh_of_fixed (x * y ^ 2) hV c4 hc4',
          mul_one, one_mul]
  rw [Nat.card_congr (Equiv.ofBijective F hF), card_fixV_eq_Cen x, card_fixV_eq_Cen y,
    card_fixV_eq_Cen (x * y), card_fixV_eq_Cen (x * y ^ 2), Nat.card_prod, Nat.card_prod,
    Nat.card_prod]
  ring

end CFSG.HardMathSupport.Cooperstein.Proving

end
