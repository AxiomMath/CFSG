module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.NaturalBridgeHeart

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique Equiv Equiv.Perm
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

variable {n : ℕ}

private theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  revert a; decide

private theorem zmod2_eq_add_add (a b : ZMod 2) : a = b + (a + b) := by
  revert a b; decide

private theorem zmod2_eq_of_add_eq_zero {a b : ZMod 2} (h : a + b = 0) : a = b := by
  revert a b; decide

private theorem perm_inv_apply_self {α : Type*} (σ : Perm α) (x : α) : σ⁻¹ (σ x) = x :=
  σ.symm_apply_apply x

private theorem perm_apply_inv_self {α : Type*} (σ : Perm α) (x : α) : σ (σ⁻¹ x) = x :=
  σ.apply_symm_apply x

@[expose] noncomputable def altHeartCoord (k : Fin n) : altHeart n →+ (Fin n → ZMod 2) :=
  QuotientAddGroup.lift (evenWeightOnes n)
    { toFun := fun y i => (y : Fin n → ZMod 2) i - (y : Fin n → ZMod 2) k
      map_zero' := by ext; simp
      map_add' := fun y z => by
        ext i
        simp only [AddSubgroup.coe_add, Pi.add_apply]
        abel }
    (fun y hy => by
      obtain ⟨c, hc⟩ := exists_forall_eq_of_mem_evenWeightOnes hy
      rw [AddMonoidHom.mem_ker]
      ext i
      simp [hc])

theorem altHeartCoord_mk (k : Fin n) (y : evenWeight n) (i : Fin n) :
    altHeartCoord k (y : altHeart n) i = (y : Fin n → ZMod 2) i - (y : Fin n → ZMod 2) k :=
  rfl

theorem altHeartCoord_self (k : Fin n) (v : altHeart n) : altHeartCoord k v k = 0 := by
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective v
  exact sub_self _

theorem altHeartCoord_altAct {k : Fin n} {σ : Perm (Fin n)} (hσ : σ k = k) (v : altHeart n)
    (i : Fin n) : altHeartCoord k (altAct σ v) i = altHeartCoord k v (σ⁻¹ i) := by
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective v
  have hk : σ⁻¹ k = k := by rw [Perm.inv_eq_iff_eq, hσ]
  rw [altAct_mk, altHeartCoord_mk, altHeartCoord_mk, evenWeightPerm_apply, evenWeightPerm_apply,
    hk]

theorem altHeartCoord_injective (k : Fin n) : Function.Injective (altHeartCoord k) := by
  refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective v
  refine (QuotientAddGroup.eq_zero_iff _).2
    (mem_evenWeightOnes_of_forall_eq (c := (y : Fin n → ZMod 2) k) fun i => ?_)
  have h := congrFun hv i
  rw [altHeartCoord_mk, Pi.zero_apply] at h
  exact sub_eq_zero.1 h

theorem exists_alt_fix_apply_eq {N : ℕ} (hN : 5 ≤ N) {k j i : Fin N} (hjk : j ≠ k)
    (hik : i ≠ k) : ∃ g ∈ alternatingGroup (Fin N), g k = k ∧ g j = i := by
  by_cases hij : j = i
  · exact ⟨1, one_mem _, rfl, hij⟩
  obtain ⟨a, ha1, ha2, -, -⟩ := exists_ne_four hN k j i i
  obtain ⟨b, hb1, hb2, -, hb4⟩ := exists_ne_four hN k j i a
  refine ⟨swap j i * swap a b, ?_, ?_, ?_⟩
  · rw [mem_alternatingGroup, map_mul, sign_swap hij, sign_swap (Ne.symm hb4)]
    decide
  · rw [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm ha1) (Ne.symm hb1),
      swap_apply_of_ne_of_ne (Ne.symm hjk) (Ne.symm hik)]
  · rw [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm ha2) (Ne.symm hb2), swap_apply_left]

theorem cocycle_apply_fixed_eq_zero {N : ℕ} (hN : 7 ≤ N) {k j : Fin N}
    (d : Perm (Fin N) → Fin N → ZMod 2)
    (hd : ∀ σ ∈ alternatingGroup (Fin N), σ k = k → ∀ τ ∈ alternatingGroup (Fin N), τ k = k →
      ∀ i, d (σ * τ) i = d σ i + d τ (σ⁻¹ i))
    {σ : Perm (Fin N)} (hσ : σ ∈ alternatingGroup (Fin N)) (hσk : σ k = k) (hσj : σ j = j) :
    d σ j = 0 := by
  set s : Finset (Fin N) := ({k, j} : Finset (Fin N))ᶜ with hs
  have hks : k ∉ s := by simp [hs]
  have hjs : j ∉ s := by simp [hs]
  have hcard : 5 ≤ Nat.card s := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, hs, Finset.card_compl, Fintype.card_fin]
    have := Finset.card_le_two (a := k) (b := j)
    omega
  have hfix : ∀ g : alternatingGroup s, ∀ i ∉ s,
      (alternatingGroup.ofSubtype s g : Perm (Fin N)) i = i := fun g i hi => by
    rw [alternatingGroup.coe_ofSubtype]
    exact Perm.ofSubtype_apply_of_not_mem _ hi
  have hfix' : ∀ g : alternatingGroup s,
      (alternatingGroup.ofSubtype s g : Perm (Fin N))⁻¹ j = j := fun g => by
    rw [Perm.inv_eq_iff_eq, hfix g j hjs]
  let ψ : alternatingGroup s →* Multiplicative (ZMod 2) :=
    MonoidHom.mk' (fun g => Multiplicative.ofAdd
      (d (alternatingGroup.ofSubtype s g : Perm (Fin N)) j)) fun g g' => by
      simp only [map_mul, Subgroup.coe_mul]
      rw [hd _ (SetLike.coe_mem _) (hfix g k hks) _ (SetLike.coe_mem _) (hfix g' k hks), hfix' g]
      rfl
  have hsupp : σ.support ⊆ s := by
    intro i hi
    rw [Perm.mem_support] at hi
    simp only [hs, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => hi (by rw [h]; exact hσk), fun h => hi (by rw [h]; exact hσj)⟩
  obtain ⟨g, hg⟩ := (alternatingGroup.mem_range_ofSubtype_iff s ⟨σ, hσ⟩).2 hsupp
  have hψ : ψ g = 1 := MonoidHom.mem_ker.1 (Abelianization.commutator_subset_ker ψ
    (by rw [commutator_alternatingGroup_eq_top hcard]; exact Subgroup.mem_top g))
  have hgσ : (alternatingGroup.ofSubtype s g : Perm (Fin N)) = σ := congrArg Subtype.val hg
  change Multiplicative.ofAdd (d (alternatingGroup.ofSubtype s g : Perm (Fin N)) j) = 1 at hψ
  rw [hgσ, ofAdd_eq_one] at hψ
  exact hψ

theorem exists_cobound_of_cocycle_stab {N : ℕ} (hN : 7 ≤ N) (k : Fin N)
    (d : Perm (Fin N) → Fin N → ZMod 2)
    (hd : ∀ σ ∈ alternatingGroup (Fin N), σ k = k → ∀ τ ∈ alternatingGroup (Fin N), τ k = k →
      ∀ i, d (σ * τ) i = d σ i + d τ (σ⁻¹ i)) :
    ∃ x : Fin N → ZMod 2, ∀ g ∈ alternatingGroup (Fin N), g k = k → ∀ i,
      d g i = x (g⁻¹ i) + x i := by
  classical
  obtain ⟨j, hj, -, -, -⟩ := exists_ne_four (by omega : 5 ≤ N) k k k k
  have hwd : ∀ a ∈ alternatingGroup (Fin N), a k = k → ∀ b ∈ alternatingGroup (Fin N),
      b k = k → a j = b j → d b (b j) = d a (a j) := by
    intro a ha hak b hb hbk hab
    have htA : a⁻¹ * b ∈ alternatingGroup (Fin N) := mul_mem (inv_mem ha) hb
    have hak' : a⁻¹ k = k := by rw [Perm.inv_eq_iff_eq, hak]
    have htk : (a⁻¹ * b) k = k := by rw [Perm.mul_apply, hbk, hak']
    have htj : (a⁻¹ * b) j = j := by rw [Perm.mul_apply, ← hab, perm_inv_apply_self]
    have h := hd a ha hak (a⁻¹ * b) htA htk (b j)
    rw [mul_inv_cancel_left, ← hab, perm_inv_apply_self,
      cocycle_apply_fixed_eq_zero hN d hd htA htk htj, add_zero] at h
    rw [← hab]
    exact h
  let x : Fin N → ZMod 2 := fun i =>
    if hi : ∃ g ∈ alternatingGroup (Fin N), g k = k ∧ g j = i then d hi.choose i else 0
  have hx : ∀ a ∈ alternatingGroup (Fin N), a k = k → x (a j) = d a (a j) := by
    intro a ha hak
    have hi : ∃ g ∈ alternatingGroup (Fin N), g k = k ∧ g j = a j := ⟨a, ha, hak, rfl⟩
    obtain ⟨h1, h2, h3⟩ := hi.choose_spec
    simp only [x, dite_eq_left hi]
    have h := hwd a ha hak _ h1 h2 h3.symm
    rwa [h3] at h
  refine ⟨x, fun g hg hgk i => ?_⟩
  have hgk' : g⁻¹ k = k := by rw [Perm.inv_eq_iff_eq, hgk]
  by_cases hik : i = k
  · rw [hik, hgk', cocycle_apply_fixed_eq_zero hN d hd hg hgk hgk, zmod2_add_self]
  obtain ⟨a, ha, hak, haj⟩ := exists_alt_fix_apply_eq (by omega) hj hik
  have hb : g⁻¹ * a ∈ alternatingGroup (Fin N) := mul_mem (inv_mem hg) ha
  have hbk : (g⁻¹ * a) k = k := by rw [Perm.mul_apply, hak, hgk']
  have h1 := hx a ha hak
  have h2 := hx (g⁻¹ * a) hb hbk
  have h3 := hd g hg hgk (g⁻¹ * a) hb hbk i
  rw [mul_inv_cancel_left] at h3
  rw [Perm.mul_apply, haj] at h2
  rw [haj] at h1
  rw [h2, h1, h3]
  exact zmod2_eq_add_add _ _

theorem altCocycle_eq_zero_of_fix {N : ℕ} (hN : 7 ≤ N) (Δ : Finset (Fin N))
    (hΓ : ∃ k : Fin N, k ∉ Δ) (P : Subgroup (Equiv.Perm (Fin N)))
    (hPA : P ≤ alternatingGroup (Fin N)) (hPfix : ∀ p ∈ P, ∀ i : Fin N, i ∉ Δ → p i = i)
    (hPtrans : ∀ i ∈ Δ, ∀ j ∈ Δ, ∃ p ∈ P, p i = j)
    (c : Equiv.Perm (Fin N) → CFSG.RankThree.PartTwo.altHeart N)
    (hc : ∀ σ ∈ alternatingGroup (Fin N), ∀ τ ∈ alternatingGroup (Fin N),
      c (σ * τ) = c σ + altAct σ (c τ))
    (hcP : ∀ p ∈ P, c p = 0) {h : Equiv.Perm (Fin N)} (hhA : h ∈ alternatingGroup (Fin N))
    (hhfix : ∀ i : Fin N, i ∉ Δ → h i = i) : c h = 0 := by
  obtain ⟨k, hk⟩ := hΓ
  obtain ⟨x, hx⟩ := exists_cobound_of_cocycle_stab hN k (fun σ => altHeartCoord k (c σ))
    fun σ hσ hσk τ hτ _ i => by
      simp only [hc σ hσ τ hτ, map_add, Pi.add_apply, altHeartCoord_altAct hσk]
  have hxP : ∀ p ∈ P, ∀ i, x (p⁻¹ i) = x i := by
    intro p hp i
    have h0 := hx p (hPA hp) (hPfix p hp k hk) i
    simp only [hcP p hp, map_zero, Pi.zero_apply] at h0
    exact zmod2_eq_of_add_eq_zero h0.symm
  have hxΔ : ∀ i ∈ Δ, ∀ j ∈ Δ, x i = x j := by
    intro i hi j hj
    obtain ⟨p, hp, rfl⟩ := hPtrans i hi j hj
    rw [← hxP p hp (p i), perm_inv_apply_self]
  apply altHeartCoord_injective k
  rw [map_zero]
  funext i
  rw [hx h hhA (hhfix k hk) i, Pi.zero_apply]
  by_cases hiΔ : i ∈ Δ
  · have hhi : h⁻¹ i ∈ Δ := by
      by_contra hn
      have h' := hhfix _ hn
      rw [perm_apply_inv_self] at h'
      exact hn (by rw [← h']; exact hiΔ)
    rw [hxΔ _ hhi i hiΔ, zmod2_add_self]
  · rw [show h⁻¹ i = i by rw [Perm.inv_eq_iff_eq]; exact (hhfix i hiΔ).symm, zmod2_add_self]

end CFSG.HardMathSupport.Cooperstein.Coordinator
