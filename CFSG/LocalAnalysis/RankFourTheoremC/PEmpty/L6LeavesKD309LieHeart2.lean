module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309LieHeart

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309L

theorem card_V3 : Nat.card V3 = 5 ^ 3 := by
  rw [Nat.card_eq_fintype_card]
  simp [Fintype.card_fun]

theorem card_dichotomy (F : AddSubgroup V3) (h0 : F ≠ ⊥) (h1 : F ≠ ⊤) :
    Nat.card F = 5 ∨ Nat.card F = 25 := by
  have hdvd : Nat.card F ∣ 5 ^ 3 := card_V3 ▸ AddSubgroup.card_addSubgroup_dvd_card F
  obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_five).mp hdvd
  interval_cases i
  · exact absurd (AddSubgroup.eq_bot_of_card_eq F (by simpa using hi')) h0
  · left
    simpa using hi'
  · right
    simpa using hi'
  · exact absurd ((AddSubgroup.card_eq_iff_eq_top F).mp (by rw [hi', card_V3])) h1

theorem line_of_card_five (F : AddSubgroup V3) (h : Nat.card F = 5) :
    ∃ v : V3, v ≠ 0 ∧ ∀ x, x ∈ F ↔ ∃ c : ZMod 5, x = c • v := by
  have hne : F ≠ ⊥ := by
    intro hb
    rw [hb] at h
    simp at h
  obtain ⟨⟨v, hvF⟩, hv0⟩ := (AddSubgroup.ne_bot_iff_exists_ne_zero).mp hne
  have hv0' : v ≠ 0 := fun h0 => hv0 (Subtype.ext h0)
  have h5v : (5 : ℕ) • v = 0 := by
    have : (5 : ℕ) • v = ((5 : ℕ) : ZMod 5) • v := (Nat.cast_smul_eq_nsmul (ZMod 5) 5 v).symm
    rw [this]
    rw [ZMod.natCast_self, zero_smul]
  have hord : addOrderOf v = 5 := by
    haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    exact addOrderOf_eq_prime h5v hv0'
  have hle : AddSubgroup.zmultiples v ≤ F := (AddSubgroup.zmultiples_le).mpr hvF
  have hcard : Nat.card (AddSubgroup.zmultiples v) = 5 := by
    rw [Nat.card_zmultiples, hord]
  have heq : AddSubgroup.zmultiples v = F :=
    AddSubgroup.eq_of_le_of_card_ge hle (by rw [h, hcard])
  refine ⟨v, hv0', fun x => ⟨fun hx => ?_, ?_⟩⟩
  · rw [← heq] at hx
    obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
    exact ⟨(n : ZMod 5), (Int.cast_smul_eq_zsmul (ZMod 5) n v).symm⟩
  · rintro ⟨c, rfl⟩
    rw [← heq]
    have : c • v = (c.val : ℕ) • v := by
      rw [← Nat.cast_smul_eq_nsmul (ZMod 5), ZMod.natCast_zmod_val]
    rw [this]
    exact AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples v) _

theorem single_one_eq (k : Fin 3) : (Pi.single k 1 : V3) = fun j => if k = j then 1 else 0 := by
  funext j
  simp [Pi.single_apply, eq_comm]

theorem functional_eq_dot (χ : V3 →+ ZMod 5) (x : V3) :
    χ x = (fun i => χ (Pi.single i 1)) ⬝ᵥ x := by
  have h := LinearMap.pi_apply_eq_sum_univ (χ.toZModLinearMap 5) x
  simp only [AddMonoidHom.coe_toZModLinearMap] at h
  rw [h, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [single_one_eq, smul_eq_mul, mul_comm]

theorem plane_of_card_25 (F : AddSubgroup V3) (h : Nat.card F = 25) :
    ∃ u : V3, u ≠ 0 ∧ ∀ x, x ∈ F ↔ u ⬝ᵥ x = 0 := by
  have hq : Nat.card (V3 ⧸ F) = 5 := by
    have := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup F
    rw [card_V3, h] at this
    omega
  haveI : IsAddCyclic (V3 ⧸ F) := by
    haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    exact isAddCyclic_of_prime_card hq
  let ψ : (V3 ⧸ F) ≃+ ZMod 5 :=
    (zmodAddCyclicAddEquiv (G := V3 ⧸ F) inferInstance).symm.trans
      (ZMod.ringEquivCongr hq).toAddEquiv
  let χ : V3 →+ ZMod 5 := (ψ : (V3 ⧸ F) →+ ZMod 5).comp (QuotientAddGroup.mk' F)
  have hχ : ∀ x, χ x = 0 ↔ x ∈ F := by
    intro x
    change ψ (QuotientAddGroup.mk x) = 0 ↔ _
    rw [map_eq_zero_iff _ ψ.injective, QuotientAddGroup.eq_zero_iff]
  refine ⟨fun i => χ (Pi.single i 1), ?_, fun x => ?_⟩
  · intro h0
    have hall : ∀ x, x ∈ F := fun x => (hχ x).mp (by rw [functional_eq_dot, h0]; simp)
    have : F = ⊤ := by
      rw [eq_top_iff]
      exact fun x _ => hall x
    rw [this, AddSubgroup.card_top, card_V3] at h
    norm_num at h
  · rw [← hχ, functional_eq_dot]

theorem prop_of_ker_eq {u u' : V3} (hu : u ≠ 0) (hu' : u' ≠ 0)
    (h : ∀ x, u ⬝ᵥ x = 0 ↔ u' ⬝ᵥ x = 0) : ∃ c : ZMod 5, c ≠ 0 ∧ u' = c • u := by
  have hinv : ∀ a : ZMod 5, a ≠ 0 → a * a⁻¹ = 1 := by decide +kernel
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, u ⬝ᵥ x₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hu
    funext i
    have := hcon (Pi.single i 1)
    simpa using this
  set a := u ⬝ᵥ x₀ with ha
  have hai := hinv a hx₀
  set c := (u' ⬝ᵥ x₀) * a⁻¹ with hc
  have key : ∀ x, u' ⬝ᵥ x = c * (u ⬝ᵥ x) := by
    intro x
    have hmem : u ⬝ᵥ (x - ((u ⬝ᵥ x) * a⁻¹) • x₀) = 0 := by
      rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, ← ha]
      linear_combination (-(u ⬝ᵥ x)) * hai
    have := (h _).mp hmem
    rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, sub_eq_zero] at this
    rw [this, hc]
    ring
  refine ⟨c, ?_, ?_⟩
  · intro hc0
    apply hu'
    funext i
    have := key (Pi.single i 1)
    simpa [hc0] using this
  · funext i
    have := key (Pi.single i 1)
    simpa using this

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309L
