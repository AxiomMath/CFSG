module

public import CFSG.HardMathSupport.Solomon.Coordinator.Defs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open scoped commutatorElement

@[expose] def mcltf_Facts (W : Type) [Group W] : Prop :=
  (Group.IsSolvable W →
      (∀ φ : MulAut W, φ ^ 3 = 1 → ∃ w : W, φ = MulAut.conj w) ∧
        Subgroup.center W = ⊥ ∧ ∀ q : ℕ, q.Prime → q ∣ Nat.card W → q = 2 ∨ q = 3) ∧
    (¬ Group.IsSolvable W →
      (IsSimpleGroup ↥(⨅ n : ℕ, derivedSeries W n) ∧
        ∃ a b : ↥(⨅ n : ℕ, derivedSeries W n), a * b ≠ b * a) ∧
      ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ Nat.card W → q ∣ Nat.card ↥(⨅ n : ℕ, derivedSeries W n))

section Transport

variable {W W' : Type} [Group W] [Group W']

theorem mcltf_map_iInf_derivedSeries (e : W ≃* W') :
    (⨅ n : ℕ, derivedSeries W n).map e.toMonoidHom = ⨅ n : ℕ, derivedSeries W' n := by
  rw [Subgroup.map_iInf _ e.injective]
  exact iInf_congr fun n => map_derivedSeries_eq e.surjective n

@[expose] noncomputable def mcltf_iInfEquiv (e : W ≃* W') :
    ↥(⨅ n : ℕ, derivedSeries W n) ≃* ↥(⨅ n : ℕ, derivedSeries W' n) :=
  (e.subgroupMap _).trans (MulEquiv.subgroupCongr (mcltf_map_iInf_derivedSeries e))

@[expose] def mcltf_autConj (e : W ≃* W') (φ : MulAut W) : MulAut W' :=
  (e.symm.trans φ).trans e

theorem mcltf_autConj_apply (e : W ≃* W') (φ : MulAut W) (x : W') :
    mcltf_autConj e φ x = e (φ (e.symm x)) :=
  rfl

theorem mcltf_autConj_pow (e : W ≃* W') (φ : MulAut W) (k : ℕ) :
    mcltf_autConj e φ ^ k = mcltf_autConj e (φ ^ k) := by
  induction k with
  | zero => ext x; simp [mcltf_autConj_apply]
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    ext x
    simp [mcltf_autConj_apply]

theorem mcltf_facts_of_mulEquiv (e : W ≃* W') (h : mcltf_Facts W') : mcltf_Facts W := by
  obtain ⟨h1, h2⟩ := h
  have hsolv : Group.IsSolvable W ↔ Group.IsSolvable W' :=
    ⟨fun _ => Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective,
      fun _ => Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective⟩
  have hcard : Nat.card W = Nat.card W' := Nat.card_congr e.toEquiv
  have hcardD : Nat.card ↥(⨅ n : ℕ, derivedSeries W n) =
      Nat.card ↥(⨅ n : ℕ, derivedSeries W' n) := Nat.card_congr (mcltf_iInfEquiv e).toEquiv
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · obtain ⟨ha, hc, hp⟩ := h1 (hsolv.mp hs)
    refine ⟨fun φ hφ => ?_, ?_, fun q hq hqd => hp q hq (hcard ▸ hqd)⟩
    · have hφ' : mcltf_autConj e φ ^ 3 = 1 := by
        rw [mcltf_autConj_pow, hφ]
        ext x
        simp [mcltf_autConj_apply]
      obtain ⟨w', hw'⟩ := ha _ hφ'
      refine ⟨e.symm w', MulEquiv.ext fun x => ?_⟩
      have hx := congrArg (fun ψ : MulAut W' => ψ (e x)) hw'
      simp only [mcltf_autConj_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply] at hx
      rw [MulAut.conj_apply]
      apply e.injective
      rw [hx, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    · rw [← Subgroup.map_eq_bot_iff_of_injective (f := e.toMonoidHom) _ e.injective]
      have := Subgroup.map_center_eq e
      exact this.trans hc
  · obtain ⟨⟨hsimp, a, b, hab⟩, hp⟩ := h2 (fun h => hs (hsolv.mpr h))
    refine ⟨⟨(mcltf_iInfEquiv e).isSimpleGroup, (mcltf_iInfEquiv e).symm a,
      (mcltf_iInfEquiv e).symm b, fun h => hab ?_⟩, fun q hq hq2 hqd => ?_⟩
    · have := congrArg (mcltf_iInfEquiv e) h
      simpa using this
    · rw [hcardD]
      exact hp q hq hq2 (hcard ▸ hqd)

end Transport

section Criteria

variable {W : Type} [Group W]

theorem mcltf_commutator_eq_self (L : Subgroup W) [IsSimpleGroup L]
    (hna : ∃ a b : L, a * b ≠ b * a) : ⁅L, L⁆ = L := by
  rw [← Subgroup.isPerfect_iff, Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator L) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    have hc : ⁅a, b⁆ ∈ commutator L := by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact hab hc
  · exact h

theorem mcltf_facts_of_derived (L : Subgroup W) (k : ℕ) (hk : derivedSeries W k = L)
    (hs : IsSimpleGroup L) (hna : ∃ a b : L, a * b ≠ b * a)
    (hq : ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ Nat.card W → q ∣ Nat.card L) : mcltf_Facts W := by
  have hperf := mcltf_commutator_eq_self L hna
  have hD : ∀ j : ℕ, derivedSeries W (k + j) = L := by
    intro j
    induction j with
    | zero => exact hk
    | succ j ih => rw [← add_assoc, derivedSeries_succ, ih, hperf]
  have hinf : (⨅ n : ℕ, derivedSeries W n) = L := by
    refine le_antisymm ((iInf_le _ k).trans hk.le) (le_iInf fun n => ?_)
    rcases le_total n k with hnk | hkn
    · exact hk.symm.le.trans (derivedSeries_antitone W hnk)
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkn
      exact (hD j).symm.le
  have hns : ¬ Group.IsSolvable W := by
    rintro ⟨n, hn⟩
    have hle : L ≤ derivedSeries W n := by
      rw [← hinf]
      exact iInf_le _ n
    rw [hn, le_bot_iff] at hle
    obtain ⟨a, b, hab⟩ := hna
    apply hab
    have ha : (a : W) = 1 := Subgroup.mem_bot.mp (hle ▸ a.2)
    have hb : (b : W) = 1 := Subgroup.mem_bot.mp (hle ▸ b.2)
    exact Subtype.ext (by simp [ha, hb])
  refine ⟨fun h => absurd h hns, fun _ => ?_⟩
  rw [hinf]
  exact ⟨⟨hs, hna⟩, hq⟩

theorem mcltf_facts_of_derived_index_two [Finite W] (L : Subgroup W) (k : ℕ)
    (hk : derivedSeries W k = L) (hs : IsSimpleGroup L) (hna : ∃ a b : L, a * b ≠ b * a)
    (hidx : L.index = 2) : mcltf_Facts W := by
  refine mcltf_facts_of_derived L k hk hs hna fun q hq hq2 hqd => ?_
  rw [← L.card_mul_index, hidx] at hqd
  exact (Nat.Coprime.dvd_mul_right ((Nat.coprime_primes hq Nat.prime_two).mpr hq2)).mp hqd

theorem mcltf_exists_ne_of_perfect {G : Type*} [Group G] [Nontrivial G] (h : commutator G = ⊤) :
    ∃ a b : G, a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  have : IsMulCommutative G := ⟨⟨hc⟩⟩
  obtain ⟨x, hx⟩ := exists_ne (1 : G)
  have hmem : x ∈ commutator G := h ▸ Subgroup.mem_top x
  rw [commutator_eq_bot G, Subgroup.mem_bot] at hmem
  exact hx hmem

theorem mcltf_facts_of_simple [IsSimpleGroup W] (hna : ∃ a b : W, a * b ≠ b * a) :
    mcltf_Facts W := by
  refine mcltf_facts_of_derived ⊤ 0 (derivedSeries_zero W)
    (Subgroup.topEquiv.isSimpleGroup) ?_ fun q _ _ hqd => ?_
  · obtain ⟨a, b, hab⟩ := hna
    exact ⟨⟨a, Subgroup.mem_top a⟩, ⟨b, Subgroup.mem_top b⟩, fun h => hab (by
      simpa using congrArg Subtype.val h)⟩
  · rwa [Subgroup.card_top]

theorem mcltf_facts_of_solvable (hsol : Group.IsSolvable W)
    (haut : ∀ φ : MulAut W, φ ^ 3 = 1 → ∃ w : W, φ = MulAut.conj w)
    (hZ : Subgroup.center W = ⊥) (hp : ∀ q : ℕ, q.Prime → q ∣ Nat.card W → q = 2 ∨ q = 3) :
    mcltf_Facts W :=
  ⟨fun _ => ⟨haut, hZ, hp⟩, fun h => absurd hsol h⟩

end Criteria

section Inner

variable {G : Type*} [Group G]

theorem mcltf_eq_conj_of_eqOn (T : Set G) (hT : ∀ g : G, ∀ x ∈ T, g * x * g⁻¹ ∈ T)
    (hC : ∀ z : G, (∀ x ∈ T, z * x = x * z) → z = 1) (φ : MulAut G) (g : G)
    (h : ∀ x ∈ T, φ x = g * x * g⁻¹) : φ = MulAut.conj g := by
  ext y
  rw [MulAut.conj_apply]
  have hw : y⁻¹ * g⁻¹ * φ y * g = 1 := by
    refine hC _ fun x hx => ?_
    have h1 := h _ (hT y x hx)
    rw [map_mul, map_mul, map_inv, h x hx] at h1
    have h2 : (y⁻¹ * g⁻¹ * φ y * g) * x * (y⁻¹ * g⁻¹ * φ y * g)⁻¹ = x := by
      calc (y⁻¹ * g⁻¹ * φ y * g) * x * (y⁻¹ * g⁻¹ * φ y * g)⁻¹
          = y⁻¹ * g⁻¹ * (φ y * (g * x * g⁻¹) * (φ y)⁻¹) * g * y := by group
        _ = y⁻¹ * g⁻¹ * (g * (y * x * y⁻¹) * g⁻¹) * g * y := by rw [h1]
        _ = x := by group
    calc (y⁻¹ * g⁻¹ * φ y * g) * x
        = (y⁻¹ * g⁻¹ * φ y * g) * x * (y⁻¹ * g⁻¹ * φ y * g)⁻¹ * (y⁻¹ * g⁻¹ * φ y * g) := by
          group
      _ = x * (y⁻¹ * g⁻¹ * φ y * g) := by rw [h2]
  calc φ y = g * y * (y⁻¹ * g⁻¹ * φ y * g) * g⁻¹ := by group
    _ = g * y * g⁻¹ := by rw [hw, mul_one]

end Inner

end CFSG.HardMathSupport.Solomon.Coordinator
