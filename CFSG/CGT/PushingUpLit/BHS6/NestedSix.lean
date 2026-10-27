module

public import CFSG.CGT.PushingUpLit.BHS.SymNatOrbitsSL
public import CFSG.CGT.PushingUpLit.BHS6.NestedPerm

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.Quasithin.A1b CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {n : ℕ}

theorem mem_setStab_of_support {S : Finset (Fin n)} {t : Equiv.Perm (Fin n)}
    (h : t.support ⊆ S ∨ Disjoint t.support S) : t ∈ setStab S := by
  rw [mem_setStab]
  intro x
  by_cases hx : t x = x
  · rw [hx]
  · have hxs : x ∈ t.support := Equiv.Perm.mem_support.2 hx
    have htxs : t x ∈ t.support := Equiv.Perm.apply_mem_support.2 hxs
    rcases h with h | h
    · exact ⟨fun _ => h hxs, fun _ => h htxs⟩
    · exact ⟨fun hS => absurd hS (Finset.disjoint_left.1 h htxs),
        fun hS => absurd hS (Finset.disjoint_left.1 h hxs)⟩

theorem coreAct_swap_mul_inv {a b : Fin n} (hab : a ≠ b) (v : ↥(coreMod n)) :
    coreAct n (Equiv.swap a b) v * v⁻¹ = if vcoord v a = vcoord v b then 1 else pairVec a b := by
  classical
  have hz : ∀ x y : ZMod 2, (x = y → x + y = 0) ∧ (x ≠ y → x + y = 1) := by decide
  apply vcoord_ext
  intro i
  rw [vcoord_mul, vcoord_coreAct, Equiv.swap_inv, coreMod_inv_eq]
  by_cases hia : i = a
  · subst hia
    rw [Equiv.swap_apply_left]
    split_ifs with h
    · rw [vcoord_one]
      exact (hz _ _).1 h.symm
    · rw [vcoord_pairVec]
      simp only [ite_true, hab, ite_false, add_zero]
      exact (hz _ _).2 fun h' => h h'.symm
  · by_cases hib : i = b
    · subst hib
      rw [Equiv.swap_apply_right]
      split_ifs with h
      · rw [vcoord_one]
        exact (hz _ _).1 h
      · rw [vcoord_pairVec]
        simp only [hia, ite_false, ite_true, zero_add]
        exact (hz _ _).2 h
    · rw [Equiv.swap_apply_of_ne_of_ne hia hib]
      split_ifs with h
      · rw [vcoord_one]
        exact (hz _ _).1 rfl
      · rw [vcoord_pairVec]
        simp only [hia, hib, ite_false, add_zero]
        exact (hz _ _).1 rfl

theorem coreAct_mem_commV_of_mem_setStab (hn : Odd n) {F : Subgroup (Equiv.Perm (Fin n))}
    {x₀ : Fin n} (hsame : ∀ a, (∃ f ∈ F, f a ≠ a) → ∃ f ∈ F, f x₀ = a)
    {y : Equiv.Perm (Fin n)} (hy : y ∈ setStab (movFin F)) {w : ↥(coreMod n)}
    (hw : w ∈ commV (F.map (coreAct n))) : coreAct n y w ∈ commV (F.map (coreAct n)) := by
  have hst : ∀ x, y⁻¹ x ∈ movFin F ↔ x ∈ movFin F := fun x =>
    mem_setStab.1 ((setStab (movFin F)).inv_mem hy) x
  rw [mem_commV_iff_of_orbit hn hsame] at hw ⊢
  intro i hi
  rw [vcoord_coreAct]
  refine hw _ fun f hf => ?_
  by_contra hne
  have h1 : y⁻¹ i ∈ movFin F := mem_movFin.2 ⟨f, hf, hne⟩
  rw [hst] at h1
  obtain ⟨f', hf', hf'i⟩ := mem_movFin.1 h1
  exact hf'i (hi f' hf')

theorem card_movFin_eq_six_of_irr (hn : Odd n) {F : Subgroup (Equiv.Perm (Fin n))}
    (hF : opResidual 2 F = F)
    (hirr : IsIrrSection (F.map (coreAct n))
      (commV (F.map (coreAct n)) ⊔ fixV (F.map (coreAct n))) (fixV (F.map (coreAct n))))
    (k : ℕ) (hSL : IsSLNatSection (F.map (coreAct n)) (commV (F.map (coreAct n)))
      (fixV (F.map (coreAct n)) ⊓ commV (F.map (coreAct n))) k) :
    k = 2 ∧ (movFin F).card = 6 := by
  obtain ⟨x₀, hx₀⟩ := exists_moved_of_irr hirr
  have hsame : ∀ a, (∃ f ∈ F, f a ≠ a) → ∃ f ∈ F, f x₀ = a :=
    fun a ha => same_orbit_of_moved hn hF hirr ha hx₀
  have hm3 : 3 ≤ (movFin F).card := three_le_card_movFin hF hx₀
  have h3n : 3 ≤ n := hm3.trans ((Finset.card_le_univ _).trans_eq (Fintype.card_fin n))
  have hadd := card_movFin_add F
  have hcV : Nat.card (commV (F.map (coreAct n))) * 2 = 2 ^ (movFin F).card := by
    have hcount := card_commV_mul hn hx₀ hsame
    have h2 : 2 ^ n = 2 ^ (movFin F).card * 2 ^ Nat.card {i : Fin n // ∀ f ∈ F, f i = i} := by
      rw [← pow_add, hadd]
    rw [h2, mul_right_comm] at hcount
    exact Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos _) hcount
  have hSL₀ := hSL
  obtain ⟨-, θ, β, hβs, hβk, -⟩ := hSL₀
  have hβcard : Nat.card (commV (F.map (coreAct n))) =
      Nat.card ↥(fixV (F.map (coreAct n)) ⊓ commV (F.map (coreAct n))) *
        Nat.card (GaloisField 2 k) ^ 2 := by
    have h := Subgroup.card_ker_mul_card_range β
    rw [MonoidHom.range_eq_top.2 hβs, Subgroup.card_top, hβk,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv] at h
    rw [← h]
    congr 1
    change Nat.card (Fin 2 → GaloisField 2 k) = _
    rw [Nat.card_fun, Nat.card_fin]
  have hC2 := card_fixV_inf_commV_le_two hsame
  have hC1 : 0 < Nat.card ↥(fixV (F.map (coreAct n)) ⊓ commV (F.map (coreAct n))) := Nat.card_pos
  have hm6 : (movFin F).card = 6 := by
    by_contra hne
    have hm34 : (movFin F).card = 3 ∨ (movFin F).card = 4 := by
      by_contra h'
      exact hne (card_movFin_eq_six_of_SL hn hF hx₀ hsame hSL (by omega))
    have hq : Nat.card (GaloisField 2 k) = 2 := by
      obtain ⟨q, hq⟩ : ∃ q, Nat.card (GaloisField 2 k) = q := ⟨_, rfl⟩
      obtain ⟨c, hc⟩ : ∃ c, Nat.card ↥(fixV (F.map (coreAct n)) ⊓ commV (F.map (coreAct n))) = c :=
        ⟨_, rfl⟩
      rw [hq, hc] at hβcard
      rw [hc] at hC1 hC2
      rw [hq]
      have hM : c * q ^ 2 * 2 = 8 ∨ c * q ^ 2 * 2 = 16 := by
        rcases hm34 with h | h <;> rw [h, hβcard] at hcV <;> norm_num at hcV <;> omega
      have hq3 : q ≤ 3 := by rcases hM with h | h <;> nlinarith
      interval_cases c <;> interval_cases q <;> omega
    have hFc : Nat.card F = 6 := by
      refine (Subgroup.card_map_of_injective (coreAct_injective h3n)).symm.trans
        ((Nat.card_congr θ.toEquiv).trans ?_)
      rw [natCard_SL2, hq]
      norm_num
    rcases hm34 with h3 | h4
    · have h1 := Subgroup.card_le_of_le (le_altOn_movFin hF)
      rw [card_altOn (by omega), h3, hFc] at h1
      norm_num at h1
    · have hdvd : (MulAction.orbit F x₀).ncard ∣ Nat.card F := by
        rw [← MulAction.index_stabilizer]
        exact Subgroup.index_dvd_card _
      have horb : MulAction.orbit F x₀ = ↑(movFin F) := by
        ext y
        rw [Finset.mem_coe]
        constructor
        · rintro ⟨⟨f, hf⟩, rfl⟩
          exact apply_mem_movFin hf (mem_movFin.2 hx₀)
        · intro hy
          obtain ⟨f, hf, rfl⟩ := hsame y (mem_movFin.1 hy)
          exact ⟨⟨f, hf⟩, rfl⟩
      rw [horb, Set.ncard_coe_finset, h4, hFc] at hdvd
      norm_num at hdvd
  have hq4 : Nat.card (GaloisField 2 k) = 4 := by
    obtain ⟨q, hq⟩ : ∃ q, Nat.card (GaloisField 2 k) = q := ⟨_, rfl⟩
    obtain ⟨c, hc⟩ : ∃ c, Nat.card ↥(fixV (F.map (coreAct n)) ⊓ commV (F.map (coreAct n))) = c :=
      ⟨_, rfl⟩
    rw [hq, hc] at hβcard
    rw [hc] at hC1 hC2
    rw [hq]
    rw [hm6, hβcard] at hcV
    norm_num at hcV
    have hq6 : q ≤ 6 := by nlinarith
    interval_cases c <;> interval_cases q <;> omega
  exact ⟨eq_two_of_natCard_galoisField hq4, hm6⟩

theorem exists_even_conj_inside (hn : Odd n) {T' : Set (Equiv.Perm (Fin n))}
    {t₀ : Equiv.Perm (Fin n)} (ht₀ : t₀ ∈ T') (hs : ∀ t ∈ T', t.IsSwap)
    (hc : ∀ t ∈ T', ∀ t' ∈ T', t * t' = t' * t) {Ω : Finset (Fin n)} (hΩ : Ω.card = 6) :
    ∃ π ∈ alternatingGroup (Fin n), (∀ y ∈ Subgroup.closure T', π * y * π⁻¹ ∈ setStab Ω) ∧
      ∃ a ∈ Ω, ∃ b ∈ Ω, a ≠ b ∧ π * t₀ * π⁻¹ = Equiv.swap a b := by
  classical
  obtain ⟨T'', hT'', hs'', hc'', hcard⟩ := exists_isMaxSwapGroup_ge hn hs hc
  have hn6 : 6 ≤ n := by
    have := Finset.card_le_univ Ω
    simpa [hΩ] using this
  have hn7 : 7 ≤ n := by
    obtain ⟨j, hj⟩ := hn
    omega
  have ht₀'' : t₀ ∈ T'' := hT'' ht₀
  have h3 : 1 < (T'' \ {t₀}).ncard := by
    rw [Set.ncard_sdiff_singleton_of_mem ht₀'', hcard]
    omega
  obtain ⟨t₁, t₂, ht₁, ht₂, h12⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).1 h3
  have ht₁'' : t₁ ∈ T'' := ht₁.1
  have ht₂'' : t₂ ∈ T'' := ht₂.1
  have h10 : t₁ ≠ t₀ := fun h => ht₁.2 (Set.mem_singleton_iff.2 h)
  have h20 : t₂ ≠ t₀ := fun h => ht₂.2 (Set.mem_singleton_iff.2 h)
  have hd01 : Disjoint t₀.support t₁.support :=
    disjoint_support_of_commute (hs'' _ ht₀'') (hs'' _ ht₁'') (hc'' _ ht₀'' _ ht₁'')
      (Ne.symm h10)
  have hd02 : Disjoint t₀.support t₂.support :=
    disjoint_support_of_commute (hs'' _ ht₀'') (hs'' _ ht₂'') (hc'' _ ht₀'' _ ht₂'')
      (Ne.symm h20)
  have hd12 : Disjoint t₁.support t₂.support :=
    disjoint_support_of_commute (hs'' _ ht₁'') (hs'' _ ht₂'') (hc'' _ ht₁'' _ ht₂'') h12
  have hsupp : ∀ t ∈ T'', t.support.card = 2 := fun t ht => by
    obtain ⟨x, y, hxy, rfl⟩ := hs'' t ht
    exact Equiv.Perm.card_support_swap hxy
  set S₁ : Finset (Fin n) := t₀.support ∪ t₁.support ∪ t₂.support with hS₁
  have hS₁card : S₁.card = 6 := by
    rw [hS₁, Finset.card_union_of_disjoint (Finset.disjoint_union_left.2 ⟨hd02, hd12⟩),
      Finset.card_union_of_disjoint hd01, hsupp _ ht₀'', hsupp _ ht₁'', hsupp _ ht₂'']
  have hstab : ∀ t ∈ T'', t ∈ setStab S₁ := by
    intro t ht
    apply mem_setStab_of_support
    by_cases hti : t = t₀ ∨ t = t₁ ∨ t = t₂
    · left
      rcases hti with rfl | rfl | rfl <;> intro x hx <;> simp [hS₁, hx]
    · right
      push Not at hti
      rw [hS₁]
      exact Finset.disjoint_union_right.2 ⟨Finset.disjoint_union_right.2
        ⟨disjoint_support_of_commute (hs'' _ ht) (hs'' _ ht₀'') (hc'' _ ht _ ht₀'') hti.1,
          disjoint_support_of_commute (hs'' _ ht) (hs'' _ ht₁'') (hc'' _ ht _ ht₁'') hti.2.1⟩,
          disjoint_support_of_commute (hs'' _ ht) (hs'' _ ht₂'') (hc'' _ ht _ ht₂'') hti.2.2⟩
  have hcl : Subgroup.closure T'' ≤ setStab S₁ := (Subgroup.closure_le _).2 hstab
  let e : {x // x ∈ S₁} ≃ {x // x ∈ Ω} :=
    Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe, hS₁card, hΩ])
  set σ := e.extendSubtype with hσdef
  have hσ : ∀ z, σ z ∈ Ω ↔ z ∈ S₁ := fun z => by
    by_cases hz : z ∈ S₁
    · exact ⟨fun _ => hz, fun _ => e.extendSubtype_mem z hz⟩
    · exact ⟨fun h => absurd h (e.extendSubtype_not_mem z hz), fun h => absurd h hz⟩
  have ht₀S : t₀ ∈ setStab S₁ := hstab t₀ ht₀''
  obtain ⟨π, hπΩ, hπsign⟩ : ∃ π : Equiv.Perm (Fin n), (∀ z, π z ∈ Ω ↔ z ∈ S₁) ∧
      Equiv.Perm.sign π = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · exact ⟨σ, hσ, h⟩
    · refine ⟨σ * t₀, fun z => ?_, ?_⟩
      · rw [Equiv.Perm.mul_apply, hσ, mem_setStab.1 ht₀S z]
      · rw [Equiv.Perm.sign_mul, h, (hs'' t₀ ht₀'').sign_eq]
        decide
  refine ⟨π, Equiv.Perm.mem_alternatingGroup.mpr hπsign, fun y hy => ?_, ?_⟩
  · have hyS : y ∈ setStab S₁ := hcl (Subgroup.closure_mono hT'' hy)
    rw [mem_setStab] at hyS ⊢
    intro z
    have h1 : (π * y * π⁻¹) z = π (y (π⁻¹ z)) := rfl
    rw [h1, hπΩ, hyS, ← hπΩ, perm_apply_inv_self]
  · obtain ⟨a₀, b₀, hab, h0⟩ := hs'' t₀ ht₀''
    have ha₀ : a₀ ∈ S₁ := by
      have : a₀ ∈ t₀.support := by
        rw [Equiv.Perm.mem_support, h0, Equiv.swap_apply_left]
        exact hab.symm
      simp [hS₁, this]
    have hb₀ : b₀ ∈ S₁ := by
      have : b₀ ∈ t₀.support := by
        rw [Equiv.Perm.mem_support, h0, Equiv.swap_apply_right]
        exact hab
      simp [hS₁, this]
    refine ⟨π a₀, (hπΩ a₀).2 ha₀, π b₀, (hπΩ b₀).2 hb₀, π.injective.ne hab, ?_⟩
    rw [h0]
    exact (Equiv.swap_apply_apply π a₀ b₀).symm

end CFSG.CGT.PushingUpLit.BHS6
