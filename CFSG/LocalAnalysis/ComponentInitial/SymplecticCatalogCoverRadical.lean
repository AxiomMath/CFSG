module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticSixCoverCore

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticCatalogCover

open Matrix CFSG.Assembly.LowTwoRank SymplecticFlag SymplecticTorusWeyl SymplecticSixCover
open scoped commutatorElement

variable {n : ℕ} {K : Type} [Field K]

variable (n K) in
@[expose] def symGroupN : Subgroup (StatedSp n K) where
  carrier := {g | ∃ (B : Matrix (Fin n) (Fin n) K) (hB : Bᵀ = B), g = upperUnipotentSp n K hB}
  one_mem' := ⟨0, transpose_zero, upperUnipotentSp_zero.symm⟩
  mul_mem' := by
    rintro _ _ ⟨B, hB, rfl⟩ ⟨B', hB', rfl⟩
    exact ⟨B + B', _, upperUnipotentSp_mul hB hB'⟩
  inv_mem' := by
    rintro _ ⟨B, hB, rfl⟩
    refine ⟨-B, by rw [transpose_neg, hB], ?_⟩
    rw [inv_eq_iff_mul_eq_one, upperUnipotentSp_mul, ← upperUnipotentSp_zero]
    exact upperUnipotentSp_congr n _ _ (add_neg_cancel B)

theorem tauCoord_mem_symGroupN (i j : Fin n) (a : K) : tauCoord i j a ∈ symGroupN n K :=
  ⟨_, _, rfl⟩

theorem symGroupN_mul_comm {g g' : StatedSp n K} (hg : g ∈ symGroupN n K)
    (hg' : g' ∈ symGroupN n K) : g * g' = g' * g := by
  obtain ⟨B, hB, rfl⟩ := hg
  obtain ⟨B', hB', rfl⟩ := hg'
  exact commute_upperUnipotentSp hB hB'

variable (n) in
@[expose] def symPairs : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => p.1 ≤ p.2

theorem mem_symPairs {p : Fin n × Fin n} : p ∈ symPairs n ↔ p.1 ≤ p.2 := by
  simp [symPairs]

theorem symCoord_apply_of_ne {i j a b : Fin n} (c : K) (h : (i, j) ≠ (a, b))
    (h' : (j, i) = (a, b) → i = j) : symCoord i j c a b = 0 := by
  unfold symCoord
  split_ifs with hij
  · subst hij
    rw [single_apply, ite_eq_right_iff]
    rintro ⟨rfl, rfl⟩
    exact absurd rfl h
  · rw [Matrix.add_apply, single_apply, single_apply, ite_eq_right_iff.mpr, ite_eq_right_iff.mpr,
      add_zero]
    · rintro ⟨rfl, rfl⟩
      exact absurd (h' rfl) hij
    · rintro ⟨rfl, rfl⟩
      exact absurd rfl h

theorem eq_sum_symCoord_n {B : Matrix (Fin n) (Fin n) K} (hB : Bᵀ = B) :
    B = ∑ p ∈ symPairs n, symCoord p.1 p.2 (B p.1 p.2) := by
  have hsymm : ∀ a b, B a b = B b a := fun a b => by simpa using (congrFun₂ hB b a)
  ext a b
  rw [Matrix.sum_apply]
  rcases le_or_gt a b with hab | hab
  · rw [Finset.sum_eq_single (a, b)]
    · show B a b = symCoord a b (B a b) a b
      unfold symCoord
      split_ifs with h
      · subst h
        rw [single_apply_same]
      · rw [Matrix.add_apply, single_apply_same, single_apply, ite_eq_right_iff.mpr, add_zero]
        rintro ⟨rfl, -⟩
        exact absurd rfl h
    · intro p hp hpab
      refine symCoord_apply_of_ne _ (fun h => hpab (Prod.ext_iff.mpr (Prod.mk.inj h)))
        fun h => ?_
      have hp' := mem_symPairs.mp hp
      obtain ⟨h1, h2⟩ := Prod.mk.inj h
      rw [h1, h2] at hp' ⊢
      exact le_antisymm hp' hab
    · intro h
      exact absurd (mem_symPairs.mpr hab) h
  · rw [Finset.sum_eq_single (b, a)]
    · show B a b = symCoord b a (B b a) a b
      have hba : b ≠ a := hab.ne
      unfold symCoord
      rw [ite_eq_right hba, Matrix.add_apply, single_apply, ite_eq_right_iff.mpr, zero_add,
        single_apply_same, hsymm]
      rintro ⟨rfl, -⟩
      exact absurd rfl hba
    · intro p hp hpba
      refine symCoord_apply_of_ne _ (fun h => ?_) fun h => ?_
      · obtain ⟨h1, h2⟩ := Prod.mk.inj h
        have hp' := mem_symPairs.mp hp
        rw [h1, h2] at hp'
        exact absurd hp' (not_le.mpr hab)
      · obtain ⟨h1, h2⟩ := Prod.mk.inj h
        exact absurd (Prod.ext_iff.mpr ⟨h2, h1⟩) hpba
    · intro h
      exact absurd (mem_symPairs.mpr hab.le) h

theorem sum_symCoord_transpose (B : Matrix (Fin n) (Fin n) K) (S : Finset (Fin n × Fin n)) :
    (∑ p ∈ S, symCoord p.1 p.2 (B p.1 p.2))ᵀ = ∑ p ∈ S, symCoord p.1 p.2 (B p.1 p.2) := by
  rw [transpose_sum]
  exact Finset.sum_congr rfl fun p _ => symCoord_transpose _ _ _

theorem exists_weight_sep_n [CharP K 2] {r : K} (hr0 : r ≠ 0) (hr1 : r ≠ 1) {i j k l : Fin n}
    (hij : i ≤ j) (hkl : k ≤ l) (hne : (i, j) ≠ (k, l)) :
    ∃ t : Fin n → Kˣ, (t k : K) * t l = 1 ∧ (t i : K) * t j ≠ 1 := by
  set u : Kˣ := Units.mk0 r hr0 with hu
  have hur : (u : K) = r := rfl
  have hr2 : r * r ≠ 1 := by rw [← sq]; exact sq_ne_one_of_ne_one hr1
  by_cases hA : ∃ m, (m = i ∨ m = j) ∧ m ≠ k ∧ m ≠ l
  · obtain ⟨m, hm, hmk, hml⟩ := hA
    refine ⟨Function.update 1 m u, ?_, ?_⟩
    · rw [Function.update_of_ne hmk.symm, Function.update_of_ne hml.symm]
      simp
    · by_cases hi : i = m <;> by_cases hj : j = m
      · rw [hi, hj, Function.update_self, hur]
        exact hr2
      · rw [hi, Function.update_self, Function.update_of_ne hj, Pi.one_apply, Units.val_one,
          mul_one, hur]
        exact hr1
      · rw [hj, Function.update_self, Function.update_of_ne hi, Pi.one_apply, Units.val_one,
          one_mul, hur]
        exact hr1
      · rcases hm with rfl | rfl
        · exact absurd rfl hi
        · exact absurd rfl hj
  · push Not at hA
    have hi : i = k ∨ i = l := by
      by_contra h
      push Not at h
      exact h.2 (hA i (Or.inl rfl) h.1)
    have hj : j = k ∨ j = l := by
      by_contra h
      push Not at h
      exact h.2 (hA j (Or.inr rfl) h.1)
    have hkl' : k ≠ l := by
      rintro rfl
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> exact hne rfl
    have hsep : ∀ a b : Fin n, a ≠ b →
        ∃ t : Fin n → Kˣ, (t a : K) * t b = 1 ∧ (t a : K) * t a ≠ 1 := fun a b hab =>
      ⟨Function.update (Function.update 1 a u) b u⁻¹, by
        rw [Function.update_self, Function.update_of_ne hab, Function.update_self,
          Units.mul_inv], by
        rw [Function.update_of_ne hab, Function.update_self, hur]
        exact hr2⟩
    rcases hi with hik | hil <;> rcases hj with hjk | hjl
    · obtain ⟨t, ht1, ht2⟩ := hsep k l hkl'
      exact ⟨t, ht1, by rw [hik, hjk]; exact ht2⟩
    · exact absurd (by rw [hik, hjl]) hne
    · rw [hil, hjk] at hij
      exact absurd (le_antisymm hkl hij) hkl'
    · obtain ⟨t, ht1, ht2⟩ := hsep l k hkl'.symm
      exact ⟨t, by rw [mul_comm]; exact ht1, by rw [hil, hjl]; exact ht2⟩

section Cover

variable [CharP K 2] {E : Type*} [Group E] {θ : E →* StatedSp n K}
  (hθ : Function.Surjective θ) (hC : θ.ker ≤ Subgroup.center E)

omit [CharP K 2] in
include hC in
theorem commutatorElement_mem_center_of_symGroupN {x y : E} (hx : θ x ∈ symGroupN n K)
    (hy : θ y ∈ symGroupN n K) : ⁅x, y⁆ ∈ Subgroup.center E :=
  hC (by
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact symGroupN_mul_comm hx hy)

variable [Finite K]

include hθ hC in
theorem mul_comm_of_tauCoord_ne_n (hK : 4 ≤ Nat.card K) {i j k l : Fin n} (hij : i ≤ j)
    (hkl : k ≤ l) (hne : (i, j) ≠ (k, l)) {x y : E} {a b : K} (hx : θ x = tauCoord i j a)
    (hy : θ y = tauCoord k l b) : x * y = y * x := by
  obtain ⟨r, hr0, hr1⟩ := LinearCover.exists_ne_zero_ne_one_of_three_le (K := K) (by omega)
  obtain ⟨t, htkl, htij⟩ := exists_weight_sep_n hr0 hr1 hij hkl hne
  obtain ⟨g, hg⟩ := hθ (torusHom t)
  have hyV : θ y ∈ symGroupN n K := by
    rw [hy]
    exact tauCoord_mem_symGroupN k l b
  have hcen : ∀ (e : E) (s : K), θ e = tauCoord i j s → ⁅e, y⁆ ∈ Subgroup.center E :=
    fun e s he => commutatorElement_mem_center_of_symGroupN hC
      (by rw [he]; exact tauCoord_mem_symGroupN i j s) hyV
  have h := SymplecticCoverFour.commutatorElement_eq_one_of_weight hθ hC
    (ψ := fun s => tauCoord i j s) (fun s s' => tauCoord_add i j s s') htij hcen
    (fun s => by rw [hg, torusHom_mul_tauCoord_mul_inv])
    (by rw [hg, hy, torusHom_mul_tauCoord_mul_inv, htkl, one_mul]) hx
  exact commutatorElement_eq_one_iff_mul_comm.1 h

theorem exists_pair_embedding (hn : 2 ≤ n) (i j : Fin n) :
    ∃ f : Fin 2 → Fin n, Function.Injective f ∧ ∃ i' j' : Fin 2, f i' = i ∧ f j' = j := by
  have hinj : ∀ a b : Fin n, a ≠ b → Function.Injective ![a, b] := fun a b hab x y h => by
    fin_cases x <;> fin_cases y
    · rfl
    · exact absurd h hab
    · exact absurd h.symm hab
    · rfl
  by_cases hij : i = j
  · subst hij
    obtain ⟨k, hk⟩ : ∃ k : Fin n, k ≠ i := by
      by_contra h
      push Not at h
      have h0 := h ⟨0, by omega⟩
      have h1 := h ⟨1, by omega⟩
      have : (⟨0, by omega⟩ : Fin n) = ⟨1, by omega⟩ := h0.trans h1.symm
      exact absurd (congrArg Fin.val this) (by simp)
    exact ⟨![i, k], hinj i k hk.symm, 0, 0, rfl, rfl⟩
  · exact ⟨![i, j], hinj i j hij, 0, 1, rfl, rfl⟩

omit [Finite K] in
include hθ hC in
theorem mul_comm_of_tauCoord_same_n [Finite K] [Finite E] (hn : 2 ≤ n) (hK : 4 ≤ Nat.card K)
    (h2 : IsPGroup 2 θ.ker) {i j : Fin n} {x y : E} {a b : K} (hx : θ x = tauCoord i j a)
    (hy : θ y = tauCoord i j b) : x * y = y * x := by
  obtain ⟨f, hf, i', j', hi, hj⟩ := exists_pair_embedding hn i j
  set ι := embedSp (K := K) f hf
  have : Group.IsPerfect (StatedSp 2 K) := isPerfect_statedSp_of_four_le hK 2
  have : Group.IsPerfect ι.range := Group.IsPerfect.range _
  set F := ⁅ι.range.comap θ, ι.range.comap θ⁆
  obtain ⟨θF, hθF, hθFι⟩ := exists_derivedComap_cover hθ ι (embedSp_injective hf)
  have hθFker : ∀ z : F, θF z = 1 ↔ θ z = 1 := fun z => by
    rw [← hθFι, ← map_one ι]
    exact (embedSp_injective hf).eq_iff.symm
  have : Group.IsPerfect F := isPerfect_derivedComap hθ hC _
  have hcenF : θF.ker ≤ Subgroup.center F := fun z hz => Subgroup.mem_center_iff.mpr fun g =>
    Subtype.ext (Subgroup.mem_center_iff.mp (hC ((hθFker z).mp hz)) g)
  have h2F : IsPGroup 2 θF.ker := fun z => by
    obtain ⟨m, hm⟩ := h2 ⟨(z : F), (hθFker z).mp z.2⟩
    exact ⟨m, Subtype.ext (Subtype.ext (by
      simpa using congrArg (fun w : θ.ker => (w : E)) hm))⟩
  have : Finite F := Subtype.finite
  have hbot := SymplecticCoverFour.ker_eq_bot_of_statedSp hθF hcenF (by omega) h2F
  have hinj : ∀ g ∈ F, θ g = 1 → g = 1 := fun g hg hθg => by
    have hk : (⟨g, hg⟩ : F) ∈ θF.ker := (hθFker _).mpr hθg
    rw [hbot, Subgroup.mem_bot] at hk
    exact congrArg Subtype.val hk
  have hmem : ∀ c : K, tauCoord i j c ∈ ι.range := fun c =>
    ⟨tauCoord i' j' c, by rw [embedSp_tauCoord, hi, hj]⟩
  refine mul_comm_of_derivedComap hθ hC ι.range hinj (by rw [hx]; exact hmem a)
    (by rw [hy]; exact hmem b) ?_
  rw [hx, hy]
  exact symGroupN_mul_comm (tauCoord_mem_symGroupN i j a) (tauCoord_mem_symGroupN i j b)

omit [Finite K] in
include hθ hC in
theorem mul_comm_of_tauCoord_n [Finite K] [Finite E] (hn : 2 ≤ n) (hK : 4 ≤ Nat.card K)
    (h2 : IsPGroup 2 θ.ker) {i j k l : Fin n} {x y : E} {a b : K} (hx : θ x = tauCoord i j a)
    (hy : θ y = tauCoord k l b) : x * y = y * x := by
  have norm : ∀ (i j : Fin n) (a : K), ∃ i' j', i' ≤ j' ∧ tauCoord i j a = tauCoord i' j' a :=
    fun i j a => by
      rcases le_total i j with h | h
      · exact ⟨i, j, h, rfl⟩
      · exact ⟨j, i, h, tauCoord_comm i j a⟩
  obtain ⟨i', j', hij, hx'⟩ := norm i j a
  obtain ⟨k', l', hkl, hy'⟩ := norm k l b
  rw [hx'] at hx
  rw [hy'] at hy
  by_cases he : (i', j') = (k', l')
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    exact mul_comm_of_tauCoord_same_n hθ hC hn hK h2 hx hy
  · exact mul_comm_of_tauCoord_ne_n hθ hC hK hij hkl he hx hy

omit [CharP K 2] [Finite K] in
include hθ in
theorem mem_closure_of_mem_symGroupN (hn : 0 < n) {z : E} (hz : θ z ∈ symGroupN n K) :
    z ∈ Subgroup.closure {w | ∃ (i j : Fin n) (a : K), θ w = tauCoord i j a} := by
  set H := Subgroup.closure {w : E | ∃ (i j : Fin n) (a : K), θ w = tauCoord i j a}
  obtain ⟨B, hB, hzB⟩ := hz
  have key : ∀ S : Finset (Fin n × Fin n), ∃ w ∈ H,
      θ w = upperUnipotentSp n K (sum_symCoord_transpose B S) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      refine ⟨1, one_mem _, ?_⟩
      rw [map_one, ← upperUnipotentSp_zero]
      exact upperUnipotentSp_congr n _ _ (by simp)
    | insert q S hq ih =>
      obtain ⟨w, hw, hθw⟩ := ih
      obtain ⟨e, he⟩ := hθ (tauCoord q.1 q.2 (B q.1 q.2))
      refine ⟨e * w, mul_mem (Subgroup.subset_closure ⟨_, _, _, he⟩) hw, ?_⟩
      rw [map_mul, he, hθw, tauCoord, upperUnipotentSp_mul]
      exact upperUnipotentSp_congr n _ _
        (Finset.sum_insert (f := fun p : Fin n × Fin n => symCoord p.1 p.2 (B p.1 p.2)) hq).symm
  obtain ⟨w, hw, hθw⟩ := key (symPairs n)
  have hθw' : θ w = θ z := by
    rw [hθw, hzB]
    exact upperUnipotentSp_congr n _ _ (eq_sum_symCoord_n hB).symm
  have hk : w⁻¹ * z ∈ H := Subgroup.subset_closure ⟨⟨0, hn⟩, ⟨0, hn⟩, 0, by
    rw [map_mul, map_inv, hθw', inv_mul_cancel, tauCoord_zero]⟩
  have := mul_mem hw hk
  rwa [mul_inv_cancel_left] at this

include hθ hC in
theorem mul_comm_of_mem_symGroupN [Finite E] (hn : 2 ≤ n) (hK : 4 ≤ Nat.card K)
    (h2 : IsPGroup 2 θ.ker) {x y : E} (hx : θ x ∈ symGroupN n K) (hy : θ y ∈ symGroupN n K) :
    x * y = y * x := by
  set G₀ : Set E := {z | ∃ (i j : Fin n) (a : K), θ z = tauCoord i j a}
  have hG₀ : G₀.Pairwise Commute := fun z hz w hw _ => by
    obtain ⟨i, j, a, hz⟩ := hz
    obtain ⟨k, l, b, hw⟩ := hw
    exact mul_comm_of_tauCoord_n hθ hC hn hK h2 hz hw
  have hcomm : IsMulCommutative (Subgroup.closure G₀) := Subgroup.isMulCommutative_closure hG₀
  have h := hcomm.is_comm.comm
    (⟨x, mem_closure_of_mem_symGroupN hθ (by omega) hx⟩ : Subgroup.closure G₀)
    ⟨y, mem_closure_of_mem_symGroupN hθ (by omega) hy⟩
  exact congrArg Subtype.val h

end Cover

end CFSG.LocalAnalysis.ComponentInitial.SymplecticCatalogCover
