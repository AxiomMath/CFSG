module

public import CFSG.RankThree.PartOne.K1327.Trick

public section

namespace CFSG.AGLEmbedding.KFactProofs.Fi22Five

open CFSG.Open

variable {G : Type*} [Group G]

structure PlaneData (x y : G) : Prop where
  x_pow : x ^ 5 = 1
  y_pow : y ^ 5 = 1
  comm : x * y = y * x
  ne : ∀ v : Fin 2 → ZMod 5, v ≠ 0 → x ^ (v 0).val * y ^ (v 1).val ≠ 1

theorem pow_eq_one_of_mem_closure {S : Set G} (hcomm : S.Pairwise Commute) {n : ℕ}
    (hS : ∀ s ∈ S, s ^ n = 1) : ∀ g ∈ Subgroup.closure S, g ^ n = 1 := by
  have := Subgroup.isMulCommutative_closure hcomm
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem s hs => exact hS s hs
  | one => exact one_pow n
  | mul x y hx hy hx' hy' =>
    rw [(show Commute x y from setLike_mul_comm hx hy).mul_pow, hx', hy', one_mul]
  | inv x hx hx' => rw [inv_pow, hx', inv_one]

@[expose] def planeMap (x y : G) (v : Fin 2 → ZMod 5) : G := x ^ (v 0).val * y ^ (v 1).val

theorem PlaneData.planeMap_add {x y : G} (hD : PlaneData x y) (v w : Fin 2 → ZMod 5) :
    planeMap x y (v + w) = planeMap x y v * planeMap x y w := by
  have hadd : ∀ (g : G), g ^ 5 = 1 → ∀ a b : ZMod 5, g ^ (a + b).val = g ^ a.val * g ^ b.val := by
    intro g hg a b
    rw [ZMod.val_add, ← pow_eq_pow_mod _ hg, pow_add]
  have hc : ∀ m k : ℕ, Commute (x ^ m) (y ^ k) := fun m k => Commute.pow_pow hD.comm m k
  simp only [planeMap, Pi.add_apply, hadd x hD.x_pow, hadd y hD.y_pow]
  simp only [mul_assoc]
  rw [(hc _ _).left_comm]

@[expose] def planeHom {x y : G} (hD : PlaneData x y) : Multiplicative (Fin 2 → ZMod 5) →* G :=
  MonoidHom.mk' (fun v => planeMap x y (Multiplicative.toAdd v)) fun _ _ =>
    hD.planeMap_add _ _

theorem PlaneData.injective {x y : G} (hD : PlaneData x y) : Function.Injective (planeHom hD) := by
  rw [injective_iff_map_eq_one]
  intro v hv
  by_contra hne
  exact hD.ne (Multiplicative.toAdd v) (fun h => hne (by simpa using h)) hv

theorem PlaneData.range_eq {x y : G} (hD : PlaneData x y) :
    (planeHom hD).range = Subgroup.closure ({x, y} : Set G) := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    show planeMap x y (Multiplicative.toAdd v) ∈ _
    refine Subgroup.mul_mem _ (Subgroup.pow_mem _ ?_ _) (Subgroup.pow_mem _ ?_ _)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
  · rw [Subgroup.closure_le]
    intro g hg
    have h1 : (1 : ZMod 5).val = 1 := rfl
    rcases hg with hg | hg
    · refine ⟨Multiplicative.ofAdd (Pi.single 0 1), ?_⟩
      show planeMap x y (Pi.single 0 1) = g
      rw [hg]
      simp [planeMap, h1]
    · rw [Set.mem_singleton_iff] at hg
      refine ⟨Multiplicative.ofAdd (Pi.single 1 1), ?_⟩
      show planeMap x y (Pi.single 1 1) = g
      rw [hg]
      simp [planeMap, h1]

theorem PlaneData.closure_facts {x y : G} (hD : PlaneData x y) :
    IsElemAbelian 5 (Subgroup.closure ({x, y} : Set G)) ∧
    Nat.card (Subgroup.closure ({x, y} : Set G)) = 5 ^ 2 ∧
    ∀ t ∈ Subgroup.closure ({x, y} : Set G), ∃ v : Fin 2 → ZMod 5, t = planeMap x y v := by
  have hrc : ({x, y} : Set G).Pairwise Commute := by
    rintro a (rfl | rfl) b (rfl | rfl) hab
    · exact absurd rfl hab
    · exact hD.comm
    · exact hD.comm.symm
    · exact absurd rfl hab
  refine ⟨⟨Subgroup.isMulCommutative_closure hrc, pow_eq_one_of_mem_closure hrc ?_⟩, ?_, ?_⟩
  · rintro s (rfl | rfl)
    exacts [hD.x_pow, hD.y_pow]
  · rw [← hD.range_eq, ← Nat.card_congr (MonoidHom.ofInjective hD.injective).toEquiv,
      Nat.card_congr Multiplicative.toAdd]
    simp
  · intro t ht
    rw [← hD.range_eq] at ht
    obtain ⟨v, rfl⟩ := ht
    exact ⟨Multiplicative.toAdd v, rfl⟩


theorem PlaneData.map {H : Type*} [Group H] {x y : G} (hD : PlaneData x y) (φ : G ≃* H) :
    PlaneData (φ x) (φ y) where
  x_pow := by rw [← map_pow, hD.x_pow, map_one]
  y_pow := by rw [← map_pow, hD.y_pow, map_one]
  comm := by rw [← map_mul, ← map_mul, hD.comm]
  ne v hv h := by
    refine hD.ne v hv (φ.injective ?_)
    rw [map_one, ← h]
    simp only [map_mul, map_pow]

theorem closure_pair_map {H : Type*} [Group H] (x y : G) (φ : G ≃* H) :
    Subgroup.closure ({φ x, φ y} : Set H) =
      (Subgroup.closure ({x, y} : Set G)).map φ.toMonoidHom := by
  rw [MonoidHom.map_closure, Set.image_pair]
  rfl

@[expose] def NormData (x y : G) : Prop :=
  ∀ v : Fin 2 → ZMod 5, v ≠ 0 → ∃ n ∈ Subgroup.normalizer
    ((Subgroup.closure ({x, y} : Set G) : Subgroup G) : Set G), n * x * n⁻¹ = planeMap x y v

theorem NormData.map {H : Type*} [Group H] [Finite G] {x y : G} (hN : NormData x y) (φ : G ≃* H) :
    NormData (φ x) (φ y) := by
  have : Finite H := Finite.of_equiv G φ.toEquiv
  intro v hv
  obtain ⟨n, hn, hnx⟩ := hN v hv
  refine ⟨φ n, ?_, ?_⟩
  · rw [closure_pair_map]
    refine Subgroup.mem_normalizer_fintype fun t ht => ?_
    obtain ⟨s, hs, rfl⟩ := ht
    refine ⟨n * s * n⁻¹, ?_, by simp⟩
    exact (Subgroup.mem_normalizer_iff.1 hn s).1 hs
  · rw [← map_mul, ← map_inv, ← map_mul, hnx]
    simp [planeMap]

@[expose] def StarData (x y : G) : Prop :=
  ∀ V : Subgroup G, IsPGroup 2 V → V ≤ Subgroup.centralizer {x} →
    y ∈ Subgroup.normalizer (V : Set G) → V = ⊥

theorem StarData.map {H : Type*} [Group H] {x y : G} (hS : StarData x y) (φ : G ≃* H) :
    StarData (φ x) (φ y) := by
  intro V hV hVx hVy
  have h := hS (V.comap φ.toMonoidHom) ?_ ?_ ?_
  · rw [eq_bot_iff] at h ⊢
    intro v hv
    have h1 : φ.symm v ∈ V.comap φ.toMonoidHom := by simpa using hv
    have h2 := h h1
    rw [Subgroup.mem_bot] at h2 ⊢
    simpa using congrArg φ h2
  · intro g
    obtain ⟨k, hk⟩ := hV ⟨φ g.1, g.2⟩
    have h1 : φ g.1 ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have h2 : g.1 ^ 2 ^ k = 1 := φ.injective (by rw [map_pow, map_one]; exact h1)
    exact ⟨k, Subtype.ext h2⟩
  · intro v hv
    have := hVx hv
    rw [Subgroup.mem_centralizer_singleton_iff] at this ⊢
    exact φ.injective (by simpa using this)
  · refine Subgroup.mem_normalizer_iff.2 fun v => ?_
    have := Subgroup.mem_normalizer_iff.1 hVy (φ v)
    simpa using this

theorem mem_normalizer_closure_pair [Finite G] {x y n : G}
    (hx : n * x * n⁻¹ ∈ Subgroup.closure ({x, y} : Set G))
    (hy : n * y * n⁻¹ ∈ Subgroup.closure ({x, y} : Set G)) :
    n ∈ Subgroup.normalizer ((Subgroup.closure ({x, y} : Set G) : Subgroup G) : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun t ht => ?_
  induction ht using Subgroup.closure_induction with
  | mem s hs =>
    rcases hs with rfl | hs
    · exact hx
    · rw [Set.mem_singleton_iff.1 hs]
      exact hy
  | one => simp
  | mul a b _ _ ha hb =>
    have : n * (a * b) * n⁻¹ = (n * a * n⁻¹) * (n * b * n⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    have : n * a⁻¹ * n⁻¹ = (n * a * n⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ ha

section Reductions

theorem orbits_core {x y : G} (hD : PlaneData x y) (hN : NormData x y) (O : Set G)
    (hO : O ⊆ ((Subgroup.closure ({x, y} : Set G) : Subgroup G) : Set G) \ {1})
    (hinv : ∀ n ∈ Subgroup.normalizer
      ((Subgroup.closure ({x, y} : Set G) : Subgroup G) : Set G), ∀ t ∈ O, n * t * n⁻¹ ∈ O) :
    O.ncard = 0 ∨ O.ncard = 5 ^ 2 - 1 := by
  obtain ⟨-, hcard, hmem⟩ := hD.closure_facts
  have hne1 : ∀ v : Fin 2 → ZMod 5, planeMap x y v ≠ 1 → v ≠ 0 := by
    rintro v h rfl
    exact h (by simp [planeMap])
  by_cases hO0 : O = ∅
  · left
    simp [hO0]
  right
  obtain ⟨t₀, ht₀⟩ := Set.nonempty_iff_ne_empty.2 hO0
  obtain ⟨v₀, hv₀⟩ := hmem t₀ (hO ht₀).1
  have hv₀ne : v₀ ≠ 0 := hne1 v₀ (hv₀ ▸ (hO ht₀).2)
  obtain ⟨n₀, hn₀, hn₀x⟩ := hN v₀ hv₀ne
  have hxO : x ∈ O := by
    have h := hinv n₀⁻¹ (Subgroup.inv_mem _ hn₀) t₀ ht₀
    rw [hv₀, ← hn₀x] at h
    simpa [mul_assoc] using h
  have hall : O = ((Subgroup.closure ({x, y} : Set G) : Subgroup G) : Set G) \ {1} := by
    apply Set.Subset.antisymm hO
    intro t ht
    obtain ⟨v, rfl⟩ := hmem t ht.1
    obtain ⟨n, hn, hnx⟩ := hN v (hne1 v ht.2)
    rw [← hnx]
    exact hinv n hn x hxO
  rw [hall, Set.ncard_sdiff_singleton_of_mem (Subgroup.one_mem _)]
  have := Nat.card_coe_set_eq ((Subgroup.closure ({x, y} : Set G) : Subgroup G) : Set G)
  rw [← this]
  exact congrArg (· - 1) hcard


theorem noTwo_core {G : Type} [Group G] [Finite G] {x y : G} (hD : PlaneData x y)
    (hN : NormData x y) (hS : StarData x y) (U : Subgroup G) (hU : IsPGroup 2 U)
    (hSU : Subgroup.closure ({x, y} : Set G) ≤ Subgroup.normalizer (U : Set G)) : U = ⊥ := by
  obtain ⟨hab, hcard, hmem⟩ := hD.closure_facts
  have hcop : ¬ 5 ∣ Nat.card U := by
    obtain ⟨k, hk⟩ := hU.exists_card_eq
    rw [hk]
    intro h
    have := (Nat.Prime.dvd_of_dvd_pow (by norm_num) h)
    omega
  have hgen := CFSG.RankThree.PartOne.K1327.le_iSup_centralizers (p := 5) (by norm_num) hab hcard
    hSU hcop
  have hxy : x * y = y * x := hD.comm
  have hxy' : y⁻¹ * x = x * y⁻¹ := by
    calc y⁻¹ * x = y⁻¹ * (x * y) * y⁻¹ := by group
      _ = y⁻¹ * (y * x) * y⁻¹ := by rw [hxy]
      _ = x * y⁻¹ := by group
  have hb : ∀ b : {s : Subgroup.closure ({x, y} : Set G) // s ≠ 1},
      U ⊓ Subgroup.centralizer {(b.val : G)} = ⊥ := by
    rintro ⟨⟨b, hbS⟩, hb1⟩
    obtain ⟨v, hv⟩ := hmem b hbS
    have hv0 : v ≠ 0 := by
      rintro rfl
      exact hb1 (Subtype.ext (by simpa [planeMap] using hv))
    obtain ⟨n, hn, hnx⟩ := hN v hv0
    rw [← hv] at hnx
    have hy : y ∈ Subgroup.closure ({x, y} : Set G) := Subgroup.subset_closure (by simp)
    have hs : n * y * n⁻¹ ∈ Subgroup.closure ({x, y} : Set G) :=
      (Subgroup.mem_normalizer_iff.1 hn y).1 hy
    have hsU := Subgroup.mem_normalizer_iff.1 (hSU hs)
    have hV := hS ((U.comap (MulAut.conj n).toMonoidHom) ⊓ Subgroup.centralizer {x}) ?_
      inf_le_right ?_
    · rw [eq_bot_iff]
      intro u hu
      obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.1 hu
      have hub : u * b = b * u := Subgroup.mem_centralizer_singleton_iff.1 hu2
      have hu' : n⁻¹ * u * n ∈
          (U.comap (MulAut.conj n).toMonoidHom) ⊓ Subgroup.centralizer {x} := by
        refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
        · simpa [MulAut.conj_apply, mul_assoc] using hu1
        · rw [Subgroup.mem_centralizer_singleton_iff]
          have : x = n⁻¹ * b * n := by rw [← hnx]; group
          rw [this]
          calc n⁻¹ * u * n * (n⁻¹ * b * n) = n⁻¹ * (u * b) * n := by group
            _ = n⁻¹ * (b * u) * n := by rw [hub]
            _ = n⁻¹ * b * n * (n⁻¹ * u * n) := by group
      rw [hV, Subgroup.mem_bot] at hu'
      rw [Subgroup.mem_bot]
      calc u = n * (n⁻¹ * u * n) * n⁻¹ := by group
        _ = 1 := by rw [hu']; group
    ·
      refine IsPGroup.to_le ?_ inf_le_left
      intro g
      obtain ⟨k, hk⟩ := hU ⟨(MulAut.conj n) g.1, g.2⟩
      have h1 : (MulAut.conj n g.1) ^ 2 ^ k = 1 := by
        have := congrArg Subtype.val hk
        simpa using this
      have h2 : g.1 ^ 2 ^ k = 1 := (MulAut.conj n).injective (by rw [map_pow, map_one]; exact h1)
      exact ⟨k, Subtype.ext h2⟩
    ·
      refine Subgroup.mem_normalizer_iff.2 fun g => ?_
      have hconj : n * (y * g * y⁻¹) * n⁻¹ =
          n * y * n⁻¹ * (n * g * n⁻¹) * (n * y * n⁻¹)⁻¹ := by group
      constructor
      · intro hg
        obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.1 hg
        refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
        · show n * (y * g * y⁻¹) * n⁻¹ ∈ U
          rw [hconj]
          exact (hsU (n * g * n⁻¹)).1 (by simpa [MulAut.conj_apply] using hg1)
        · rw [Subgroup.mem_centralizer_singleton_iff] at hg2 ⊢
          calc y * g * y⁻¹ * x = y * g * (y⁻¹ * x) := by group
            _ = y * g * (x * y⁻¹) := by rw [hxy']
            _ = y * (g * x) * y⁻¹ := by group
            _ = y * (x * g) * y⁻¹ := by rw [hg2]
            _ = (y * x) * g * y⁻¹ := by group
            _ = (x * y) * g * y⁻¹ := by rw [hxy]
            _ = x * (y * g * y⁻¹) := by group
      · intro hg
        obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.1 hg
        refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
        · have h : n * (y * g * y⁻¹) * n⁻¹ ∈ U := hg1
          rw [hconj] at h
          simpa [MulAut.conj_apply] using (hsU (n * g * n⁻¹)).2 h
        · rw [Subgroup.mem_centralizer_singleton_iff] at hg2 ⊢
          calc g * x = y⁻¹ * (y * g * y⁻¹) * (y * x) := by group
            _ = y⁻¹ * (y * g * y⁻¹) * (x * y) := by rw [hxy]
            _ = y⁻¹ * ((y * g * y⁻¹) * x) * y := by group
            _ = y⁻¹ * (x * (y * g * y⁻¹)) * y := by rw [hg2]
            _ = (y⁻¹ * x * y) * g := by group
            _ = x * g := by rw [hxy', inv_mul_cancel_right]
  refine eq_bot_iff.2 (hgen.trans (iSup_le fun b => (hb b).le))


theorem PlaneData.exists_conj_closure [Finite G] {x y : G} (hD : PlaneData x y) {m : ℕ}
    (hm : Nat.card G = 5 ^ 2 * m) (hm5 : ¬ 5 ∣ m) (T : Sylow 5 G) :
    ∃ g : G, Subgroup.closure ({g * x * g⁻¹, g * y * g⁻¹} : Set G) = (T : Subgroup G) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hm0 : m ≠ 0 := by
    rintro rfl
    have := Nat.card_pos (α := G)
    omega
  have hf : (Nat.card G).factorization 5 = 2 := by
    rw [hm, Nat.factorization_mul (by norm_num) hm0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hm5, add_zero]
    rw [show (5 : ℕ) ^ 2 = 5 ^ 2 from rfl, Nat.Prime.factorization_pow (by norm_num)]
    simp
  let S₀ : Sylow 5 G := Sylow.ofCard (Subgroup.closure ({x, y} : Set G))
    (by rw [hD.closure_facts.2.1, hf])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S₀ T
  refine ⟨g, ?_⟩
  have h := closure_pair_map x y (MulAut.conj g)
  simp only [MulAut.conj_apply] at h
  rw [h, ← hg, Sylow.coe_subgroup_smul]
  rfl

structure FiveData (G : Type) [Group G] [Finite G] : Prop where
  out : ∃ (x y : G) (m : ℕ), PlaneData x y ∧ Nat.card G = 5 ^ 2 * m ∧ ¬ 5 ∣ m ∧
    NormData x y ∧ StarData x y

theorem FiveData.of_mulEquiv {G H : Type} [Group G] [Group H] [Finite G] [Finite H]
    (hG : FiveData G) (φ : G ≃* H) : FiveData H := by
  obtain ⟨x, y, m, hD, hm, hm5, hN, hS⟩ := hG.out
  exact ⟨⟨φ x, φ y, m, hD.map φ, by rw [← hm]; exact Nat.card_congr φ.toEquiv.symm, hm5,
    hN.map φ, hS.map φ⟩⟩

theorem FiveData.orbits {G : Type} [Group G] [Finite G] (hG : FiveData G) (T : Sylow 5 G)
    (O : Set G) (hO : O ⊆ ((T : Subgroup G) : Set G) \ {1})
    (hinv : ∀ n ∈ Subgroup.normalizer ((T : Subgroup G) : Set G), ∀ t ∈ O, n * t * n⁻¹ ∈ O) :
    O.ncard = 0 ∨ O.ncard = 5 ^ 2 - 1 := by
  obtain ⟨x, y, m, hD, hm, hm5, hN, -⟩ := hG.out
  obtain ⟨g, hg⟩ := hD.exists_conj_closure hm hm5 T
  have h1 : g * x * g⁻¹ = MulAut.conj g x := rfl
  have h2 : g * y * g⁻¹ = MulAut.conj g y := rfl
  rw [h1, h2] at hg
  rw [← hg] at hO hinv
  exact orbits_core (hD.map (MulAut.conj g)) (hN.map (MulAut.conj g)) O hO hinv

theorem FiveData.noTwo {G : Type} [Group G] [Finite G] (hG : FiveData G) (S : Sylow 5 G)
    (U : Subgroup G) (hU : IsPGroup 2 U)
    (hSU : (S : Subgroup G) ≤ Subgroup.normalizer (U : Set G)) :
    U = ⊥ := by
  obtain ⟨x, y, m, hD, hm, hm5, hN, hS⟩ := hG.out
  obtain ⟨g, hg⟩ := hD.exists_conj_closure hm hm5 S
  have h1 : g * x * g⁻¹ = MulAut.conj g x := rfl
  have h2 : g * y * g⁻¹ = MulAut.conj g y := rfl
  rw [h1, h2] at hg
  rw [← hg] at hSU
  exact noTwo_core (hD.map (MulAut.conj g)) (hN.map (MulAut.conj g)) (hS.map (MulAut.conj g)) U
    hU hSU

end Reductions

end CFSG.AGLEmbedding.KFactProofs.Fi22Five
