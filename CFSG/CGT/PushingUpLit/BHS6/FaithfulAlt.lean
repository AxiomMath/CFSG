module

public import CFSG.CGT.PushingUpLit.BHS.SymNatMaxSwap
public import CFSG.CGT.PushingUpLit.BHS6.BlockFixed

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.QuasithinUnique.Setup.Offender
  CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

section Perm

variable {n : ℕ}

theorem vcoord_pairVec_perm (s : Equiv.Perm (Fin n)) {x y : Fin n} (hx : s x = x) (hy : s y = y)
    (i : Fin n) : vcoord (pairVec x y) (s i) = vcoord (pairVec x y) i := by
  classical
  have h1 : s i = x ↔ i = x := ⟨fun h => s.injective (h.trans hx.symm), fun h => h ▸ hx⟩
  have h2 : s i = y ↔ i = y := ⟨fun h => s.injective (h.trans hy.symm), fun h => h ▸ hy⟩
  rw [vcoord_pairVec, vcoord_pairVec]
  simp only [h1, h2]

theorem isSwap_apply_apply {t : Equiv.Perm (Fin n)} (ht : t.IsSwap) (x : Fin n) : t (t x) = x := by
  have h2 := sq_eq_one_of_isSwap ht
  have := congrArg (fun f : Equiv.Perm (Fin n) => f x) h2
  simpa [pow_two] using this

theorem pairVec_swap_mem_fixV {T : Set (Equiv.Perm (Fin n))} (hT : ∀ t ∈ T, t.IsSwap)
    (hc : ∀ t ∈ T, ∀ t' ∈ T, t * t' = t' * t) {t : Equiv.Perm (Fin n)} (ht : t ∈ T)
    {x : Fin n} (hx : t x ≠ x) :
    pairVec x (t x) ∈ fixV ((Subgroup.closure T).map (coreAct n)) := by
  classical
  rw [mem_fixV_map_closure_iff]
  intro s hs i
  have htt : t (t x) = x := isSwap_apply_apply (hT t ht) x
  by_cases hst : s = t
  · subst hst
    have e1 := eq_swap_of_isSwap_apply_ne (hT s hs) hx
    by_cases hix : i = x
    · subst hix
      rw [vcoord_pairVec, vcoord_pairVec]
      simp [hx, hx.symm]
    · by_cases hixs : i = s x
      · subst hixs
        rw [htt, vcoord_pairVec, vcoord_pairVec]
        simp [hx, hx.symm]
      · have h3 : s i = i := by
          have h := congrArg (fun f => f i) e1
          exact h.trans (Equiv.swap_apply_of_ne_of_ne hix hixs)
        rw [h3]
  · have hsx : s x = x := apply_eq_of_commute_swap (hT t ht) (hT s hs) (hc t ht s hs)
      (Ne.symm hst) hx
    have hstx : s (t x) = t x := apply_eq_of_commute_swap (hT t ht) (hT s hs) (hc t ht s hs)
      (Ne.symm hst) (by rw [htt]; exact fun h => hx h.symm)
    exact vcoord_pairVec_perm s hsx hstx i

theorem apply_mem_pair_of_fixes {σ : Equiv.Perm (Fin n)} {x y : Fin n} (hxy : x ≠ y)
    (h : ∀ i, vcoord (pairVec x y) (σ i) = vcoord (pairVec x y) i) : σ x = x ∨ σ x = y := by
  classical
  have h1 := h x
  rw [vcoord_pairVec, vcoord_pairVec] at h1
  by_contra hcon
  rw [not_or] at hcon
  simp [hcon.1, hcon.2, hxy] at h1

theorem exists_third_fixed (hn : Odd n) {T : Set (Equiv.Perm (Fin n))}
    (hT : ∀ t ∈ T, t.IsSwap) (hc : ∀ t ∈ T, ∀ t' ∈ T, t * t' = t' * t) {x y : Fin n}
    (hxy : x ≠ y) (hx : ∀ t ∈ T, t x = x) (hy : ∀ t ∈ T, t y = y) :
    ∃ z, z ≠ x ∧ z ≠ y ∧ ∀ t ∈ T, t z = z := by
  classical
  by_contra hcon
  have hall : ∀ z, z ≠ x → z ≠ y → ∃ t ∈ T, t z ≠ z := by
    intro z hzx hzy
    by_contra h
    exact hcon ⟨z, hzx, hzy, fun t ht => by_contra fun h' => h ⟨t, ht, h'⟩⟩
  set H : Subgroup (Equiv.Perm (Fin n)) := Subgroup.closure T with hH
  have hHp : IsPGroup 2 ↥H := fun h => ⟨1, by
    apply Subtype.ext
    simpa using sq_eq_one_of_mem_closure hT hc h.2⟩
  have hmod := hHp.card_modEq_card_fixedPoints (Fin n)
  have hfp : MulAction.fixedPoints ↥H (Fin n) = {x, y} := by
    ext z
    constructor
    · intro hz
      by_contra hzn
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hzn
      obtain ⟨t, ht, htz⟩ := hall z hzn.1 hzn.2
      exact htz (hz ⟨t, Subgroup.subset_closure ht⟩)
    · intro hz h
      have hzT : ∀ t ∈ T, t z = z := by
        rcases hz with rfl | rfl
        · exact hx
        · exact hy
      exact apply_eq_of_mem_closure hzT h.2
  rw [hfp, Nat.card_coe_set_eq, Set.ncard_pair hxy, Nat.card_eq_fintype_card,
    Fintype.card_fin] at hmod
  have h1 := Nat.odd_iff.mp hn
  unfold Nat.ModEq at hmod
  omega

theorem mem_closure_of_good {T : Set (Equiv.Perm (Fin n))} (hT : ∀ t ∈ T, t.IsSwap)
    (hc : ∀ t ∈ T, ∀ t' ∈ T, t * t' = t' * t) :
    ∀ k : ℕ, ∀ σ : Equiv.Perm (Fin n), σ.support.card = k →
      (∀ x, σ x ≠ x → ∃ t ∈ T, t x ≠ x ∧ σ x = t x) → σ ∈ Subgroup.closure T := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro σ hk hgood
    by_cases hσ : σ = 1
    · rw [hσ]
      exact Subgroup.one_mem _
    obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
      by_contra h
      exact hσ (Equiv.ext fun x => by_contra fun hx => h ⟨x, hx⟩)
    obtain ⟨t, htT, htx, hσx⟩ := hgood x hx
    have hts : t = Equiv.swap x (t x) := eq_swap_of_isSwap_apply_ne (hT t htT) htx
    have htt : ∀ y, t (t y) = y := isSwap_apply_apply (hT t htT)
    have hσtx : σ (t x) = x := by
      have hne : σ (t x) ≠ t x := by
        intro h
        apply htx
        exact σ.injective (h.trans hσx.symm)
      obtain ⟨s, hsT, hs, hσs⟩ := hgood (t x) hne
      have hst : s = t := by
        by_contra hst
        have := apply_eq_of_commute_swap (hT t htT) (hT s hsT) (hc t htT s hsT) (Ne.symm hst)
          (show t (t x) ≠ t x by rw [htt]; exact fun h => htx h.symm)
        exact hs this
      subst hst
      rw [hσs, htt]
    have hfixed : ∀ y, σ y = y → (t * σ) y = y := by
      intro y hy
      rw [Equiv.Perm.mul_apply, hy]
      by_contra hty
      have hyx : y = x ∨ y = t x := by
        by_contra hcon
        rw [not_or] at hcon
        apply hty
        rw [hts]
        exact Equiv.swap_apply_of_ne_of_ne hcon.1 hcon.2
      rcases hyx with rfl | rfl
      · exact hx hy
      · rw [hσtx] at hy
        exact htx hy.symm
    have hgood' : ∀ y, (t * σ) y ≠ y → ∃ s ∈ T, s y ≠ y ∧ (t * σ) y = s y := by
      intro y hy
      have hσy : σ y ≠ y := fun h => hy (hfixed y h)
      obtain ⟨s, hsT, hs, hσs⟩ := hgood y hσy
      by_cases hst : s = t
      · subst hst
        exfalso
        apply hy
        rw [Equiv.Perm.mul_apply, hσs, htt]
      · refine ⟨s, hsT, hs, ?_⟩
        have hts' : t (s y) = s y := by
          by_contra h
          have := apply_eq_of_commute_swap (hT t htT) (hT s hsT) (hc t htT s hsT) (Ne.symm hst) h
          rw [isSwap_apply_apply (hT s hsT)] at this
          exact hs this.symm
        rw [Equiv.Perm.mul_apply, hσs, hts']
    have hsub : (t * σ).support ⊂ σ.support := by
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨x, Equiv.Perm.mem_support.mpr hx, ?_⟩
        rw [Equiv.Perm.mem_support, not_not, Equiv.Perm.mul_apply, hσx, htt]
      · intro y hy
        rw [Equiv.Perm.mem_support] at hy ⊢
        exact fun h => hy (hfixed y h)
    have hlt : (t * σ).support.card < k := hk ▸ Finset.card_lt_card hsub
    have hmem := ih _ hlt (t * σ) rfl hgood'
    have : σ = t⁻¹ * (t * σ) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.subset_closure htT)) hmem

theorem mem_closure_of_fixes (hn : Odd n) {T : Set (Equiv.Perm (Fin n))}
    (hT : ∀ t ∈ T, t.IsSwap) (hc : ∀ t ∈ T, ∀ t' ∈ T, t * t' = t' * t)
    {π : Equiv.Perm (Fin n)}
    (h : ∀ v : ↥(coreMod n), v ∈ fixV ((Subgroup.closure T).map (coreAct n)) →
      coreAct n π v = v) : π ∈ Subgroup.closure T := by
  classical
  have hfix : ∀ v ∈ fixV ((Subgroup.closure T).map (coreAct n)), ∀ i, vcoord v (π⁻¹ i) =
      vcoord v i := fun v hv i => by
    have := congrArg (fun w => vcoord w i) (h v hv)
    simpa [vcoord_coreAct] using this
  have hfix' : ∀ v ∈ fixV ((Subgroup.closure T).map (coreAct n)), ∀ i, vcoord v (π i) =
      vcoord v i := fun v hv i => by
    have := hfix v hv (π i)
    simpa using this.symm
  have hgood : ∀ x, π x ≠ x → ∃ t ∈ T, t x ≠ x ∧ π x = t x := by
    intro x hx
    by_cases hxs : ∃ t ∈ T, t x ≠ x
    · obtain ⟨t, htT, htx⟩ := hxs
      have hv := pairVec_swap_mem_fixV hT hc htT htx
      rcases apply_mem_pair_of_fixes (Ne.symm htx) (hfix' _ hv) with h1 | h1
      · exact absurd h1 hx
      · exact ⟨t, htT, htx, h1⟩
    · exfalso
      have hxO : ∀ t ∈ T, t x = x := fun t ht => by_contra fun h' => hxs ⟨t, ht, h'⟩
      by_cases hyO : ∀ t ∈ T, t (π x) = π x
      · obtain ⟨z, hzx, hzy, hz⟩ := exists_third_fixed hn hT hc (Ne.symm hx) hxO hyO
        have hv : pairVec x z ∈ fixV ((Subgroup.closure T).map (coreAct n)) := by
          rw [mem_fixV_map_closure_iff]
          exact fun s hs i => vcoord_pairVec_perm s (hxO s hs) (hz s hs) i
        rcases apply_mem_pair_of_fixes (Ne.symm hzx) (hfix' _ hv) with h1 | h1
        · exact hx h1
        · exact hzy h1.symm
      · obtain ⟨t, htT, hty⟩ : ∃ t ∈ T, t (π x) ≠ π x := by
          by_contra hcon
          exact hyO fun t ht => by_contra fun h' => hcon ⟨t, ht, h'⟩
        have hv := pairVec_swap_mem_fixV hT hc htT hty
        rcases apply_mem_pair_of_fixes (σ := π⁻¹) (Ne.symm hty) (hfix _ hv) with h1 | h1
        · exact hx (by simpa using h1.symm)
        · have h2 : π⁻¹ (π x) = x := by simp
          rw [h2] at h1
          have h3 : t x = π x :=
            calc t x = t (t (π x)) := by rw [← h1]
              _ = π x := isSwap_apply_apply (hT t htT) _
          exact hx (by rw [← h3, hxO t htT])
  exact mem_closure_of_good hT hc _ π rfl hgood

theorem commute_of_isSwap_of_pow_two_pow_eq_one {s t : Equiv.Perm (Fin n)} (hs : s.IsSwap)
    (ht : t.IsSwap) (h : ∃ k : ℕ, (s * t) ^ 2 ^ k = 1) : s * t = t * s := by
  classical
  by_cases hst : s = t
  · rw [hst]
  by_contra hnc
  have hex : ∃ x, s x ≠ x ∧ t x ≠ x := by
    by_contra hcon
    apply hnc
    refine Equiv.Perm.Disjoint.commute fun x => ?_
    by_contra hx
    rw [not_or] at hx
    exact hcon ⟨x, hx.1, hx.2⟩
  obtain ⟨x, hsx, htx⟩ := hex
  have e1 := eq_swap_of_isSwap_apply_ne hs hsx
  have e2 := eq_swap_of_isSwap_apply_ne ht htx
  have hyz : s x ≠ t x := fun h' => hst (e1.trans ((congrArg (Equiv.swap x) h').trans e2.symm))
  have h3 : (s * t).IsThreeCycle := by
    have e3 : s * t = Equiv.swap x (s x) * Equiv.swap x (t x) := by rw [← e1, ← e2]
    rw [e3]
    exact Equiv.Perm.isThreeCycle_swap_mul_swap_same hsx.symm htx.symm hyz
  obtain ⟨k, hk⟩ := h
  have hdvd : orderOf (s * t) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  rw [h3.orderOf] at hdvd
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
  omega

theorem card_closure_le_two_pow {G : Type*} [Group G] [Finite G] {T : Set G} (hfin : T.Finite)
    (hsq : ∀ t ∈ T, t ^ 2 = 1) (hc : ∀ t ∈ T, ∀ t' ∈ T, t * t' = t' * t) :
    Nat.card (Subgroup.closure T) ≤ 2 ^ T.ncard := by
  classical
  revert hsq hc
  induction T, hfin using Set.Finite.induction_on with
  | empty =>
    intro _ _
    simp
  | @insert a S haS hS ih =>
    intro hsq hc
    have ih' := ih (fun t ht => hsq t (Set.mem_insert_of_mem a ht))
      (fun t ht t' ht' => hc t (Set.mem_insert_of_mem a ht) t' (Set.mem_insert_of_mem a ht'))
    set H : Subgroup G := Subgroup.closure S with hH
    have haH : ∀ h ∈ H, a * h = h * a := by
      have hle : H ≤ Subgroup.centralizer ({a} : Set G) := by
        refine (Subgroup.closure_le _).2 fun s hs => ?_
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        exact (hc a (Set.mem_insert a S) s (Set.mem_insert_of_mem a hs)).symm
      intro h hh
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hh)).symm
    have ha2 : a * a = 1 := by
      have := hsq a (Set.mem_insert a S)
      rwa [pow_two] at this
    let K : Subgroup G :=
      { carrier := {x | x ∈ H ∨ ∃ h ∈ H, x = a * h}
        one_mem' := Or.inl H.one_mem
        mul_mem' := by
          rintro x y (hx | ⟨h, hh, rfl⟩) (hy | ⟨h', hh', rfl⟩)
          · exact Or.inl (H.mul_mem hx hy)
          · exact Or.inr ⟨x * h', H.mul_mem hx hh', by
              rw [← mul_assoc, ← haH x hx, mul_assoc]⟩
          · exact Or.inr ⟨h * y, H.mul_mem hh hy, by group⟩
          · refine Or.inl ?_
            have : a * h * (a * h') = h * h' := by
              calc a * h * (a * h') = a * (h * a) * h' := by group
                _ = a * (a * h) * h' := by rw [haH h hh]
                _ = (a * a) * h * h' := by group
                _ = h * h' := by rw [ha2, one_mul]
            rw [this]
            exact H.mul_mem hh hh'
        inv_mem' := by
          rintro x (hx | ⟨h, hh, rfl⟩)
          · exact Or.inl (H.inv_mem hx)
          · refine Or.inr ⟨h⁻¹, H.inv_mem hh, ?_⟩
            have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
            rw [mul_inv_rev, hainv, ← haH h⁻¹ (H.inv_mem hh)] }
    have hKle : Subgroup.closure (insert a S) ≤ K := by
      refine (Subgroup.closure_le _).2 ?_
      rintro x (rfl | hx)
      · exact Or.inr ⟨1, H.one_mem, by simp⟩
      · exact Or.inl (Subgroup.subset_closure hx)
    have hKcard : Nat.card K ≤ 2 * Nat.card H := by
      have h1 : Nat.card K = (K : Set G).ncard := Nat.card_coe_set_eq (K : Set G)
      have h2 : Nat.card H = (H : Set G).ncard := Nat.card_coe_set_eq (H : Set G)
      have hsub : (K : Set G) ⊆ (H : Set G) ∪ (fun h => a * h) '' (H : Set G) := by
        rintro x (hx | ⟨h, hh, rfl⟩)
        · exact Or.inl hx
        · exact Or.inr ⟨h, hh, rfl⟩
      calc Nat.card K = (K : Set G).ncard := h1
        _ ≤ ((H : Set G) ∪ (fun h => a * h) '' (H : Set G)).ncard :=
            Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ (H : Set G).ncard + ((fun h => a * h) '' (H : Set G)).ncard := Set.ncard_union_le _ _
        _ ≤ (H : Set G).ncard + (H : Set G).ncard :=
            Nat.add_le_add_left (Set.ncard_image_le (Set.toFinite _)) _
        _ = 2 * Nat.card H := by rw [h2]; ring
    calc Nat.card (Subgroup.closure (insert a S)) ≤ Nat.card K := Subgroup.card_le_of_le hKle
      _ ≤ 2 * Nat.card H := hKcard
      _ ≤ 2 * 2 ^ S.ncard := Nat.mul_le_mul_left 2 ih'
      _ = 2 ^ (insert a S).ncard := by rw [Set.ncard_insert_of_notMem haS hS, pow_succ, mul_comm]

theorem two_mul_ncard_le {T : Set (Equiv.Perm (Fin n))} (hT : ∀ t ∈ T, t.IsSwap)
    (hc : ∀ t ∈ T, ∀ t' ∈ T, t * t' = t' * t) : 2 * T.ncard ≤ n := by
  obtain ⟨σ, -, hσ⟩ := exists_prod_swaps hT hc
  have h1 := Equiv.Perm.sum_cycleType_le σ
  rw [hσ, Multiset.sum_replicate, Fintype.card_fin, smul_eq_mul] at h1
  omega

@[expose] def IsSwapGroupOfSize (Y : Subgroup (Equiv.Perm (Fin n))) (k : ℕ) : Prop :=
  ∃ T : Set (Equiv.Perm (Fin n)), (∀ t ∈ T, t.IsSwap) ∧ (∀ t ∈ T, ∀ t' ∈ T, t * t' = t' * t) ∧
    T.ncard = k ∧ Y = Subgroup.closure T

end Perm

section Faithful

variable {W : Type} [CommGroup W] [Finite W] {E : Subgroup (MulAut W)} {n : ℕ}

theorem alt_family (hW : ∀ w : W, w ^ 2 = 1) (hn : Odd n) (h5 : 5 ≤ n) (D : AltNatData E n)
    {Q : Subgroup (MulAut W)} (hQ : IsPGroup 2 Q)
    (hQN : Q ≤ Subgroup.normalizer (E : Set (MulAut W)))
    {𝒜 : Set (Subgroup (MulAut W))} (hne : 𝒜.Nonempty)
    (h𝒜 : ∀ A ∈ 𝒜, A ≤ Q ∧ IsElemAbelian2 A ∧ A ≠ ⊥ ∧
      Nat.card W ≤ Nat.card A * Nat.card (fixV A)) :
    fixV E = ⊥ ∧ Function.Bijective D.β ∧ Function.Bijective (D.psi hn h5) ∧
      (∀ A ∈ 𝒜, E ⊔ A = Subgroup.normalizer (E : Set (MulAut W))) ∧
      (∃ k : ℕ, 1 ≤ k ∧ 2 * k ≤ n ∧
        IsSwapGroupOfSize (((⨆ A ∈ 𝒜, A).subgroupOf
          (Subgroup.normalizer (E : Set (MulAut W)))).map (D.psi hn h5)) k ∧
        Nat.card ↥(⨆ A ∈ 𝒜, A) = 2 ^ k ∧
        ((∃ A ∈ 𝒜, Nat.card ↥A = 2 ^ ((n - 1) / 2)) →
          IsMaxSwapGroup (((⨆ A ∈ 𝒜, A).subgroupOf
            (Subgroup.normalizer (E : Set (MulAut W)))).map (D.psi hn h5)))) ∧
      ∀ Q'' : Subgroup (MulAut W), IsPGroup 2 Q'' →
        Q'' ≤ Subgroup.normalizer (E : Set (MulAut W)) → fixV (⨆ A ∈ 𝒜, A) ≤ fixV Q'' →
          Q'' ≤ ⨆ A ∈ 𝒜, A := by
  classical
  have h3 : 3 ≤ n := by omega
  set N : Subgroup (MulAut W) := Subgroup.normalizer (E : Set (MulAut W)) with hN
  set ψ : ↥N →* Equiv.Perm (Fin n) := D.psi hn h5 with hψ
  have hψinj : Function.Injective ψ := D.psi_injective hn h5
  obtain ⟨A₀, hA₀⟩ := hne
  have hA₀N : A₀ ≤ N := (h𝒜 A₀ hA₀).1.trans hQN
  have hfixE : fixV E = ⊥ := by
    obtain ⟨-, hAe, hAne, hAw⟩ := h𝒜 A₀ hA₀
    exact (alt_core hW hn h5 D hA₀N hAe hAw (alt_commutator_ne_bot D hn h5 hA₀N hAne)).1
  have hβinj : Function.Injective D.β := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have := (D.ker_iff hn h3 w).mp hw
    rw [hfixE, Subgroup.mem_bot] at this
    exact this
  have hθ : ∀ A ∈ 𝒜, ∃ θX : ↥(E ⊔ A) ≃* Equiv.Perm (Fin n),
      ∀ (x : ↥(E ⊔ A)) (w : W), D.β ((x : MulAut W) w) = coreAct n (θX x) (D.β w) := by
    intro A hA
    obtain ⟨hAQ, hAe, hAne, hAw⟩ := h𝒜 A hA
    have hAN : A ≤ N := hAQ.trans hQN
    obtain ⟨-, θX, -, hθXβ, -, -, -⟩ :=
      alt_core hW hn h5 D hAN hAe hAw (alt_commutator_ne_bot D hn h5 hAN hAne)
    exact ⟨θX, hθXβ⟩
  have hsupN : ∀ A ∈ 𝒜, E ⊔ A ≤ N := fun A hA =>
    sup_le Subgroup.le_normalizer ((h𝒜 A hA).1.trans hQN)
  have hψθ : ∀ (A : Subgroup (MulAut W)) (hA : A ∈ 𝒜) (θX : ↥(E ⊔ A) ≃* Equiv.Perm (Fin n)),
      (∀ (x : ↥(E ⊔ A)) (w : W), D.β ((x : MulAut W) w) = coreAct n (θX x) (D.β w)) →
      ∀ x : ↥(E ⊔ A), ψ ⟨x, hsupN A hA x.2⟩ = θX x := by
    intro A hA θX hθXβ x
    exact D.perm_unique h3 fun w => (D.psi_spec hn h5 ⟨x, hsupN A hA x.2⟩ w).symm.trans
      (hθXβ x w)
  have hsup : ∀ A ∈ 𝒜, E ⊔ A = N := by
    intro A hA
    obtain ⟨θX, hθXβ⟩ := hθ A hA
    refine le_antisymm (hsupN A hA) fun y hy => ?_
    obtain ⟨x, hx⟩ := θX.surjective (ψ ⟨y, hy⟩)
    have hxy : (⟨x, hsupN A hA x.2⟩ : ↥N) = ⟨y, hy⟩ :=
      hψinj ((hψθ A hA θX hθXβ x).trans hx)
    have hxy' : (x : MulAut W) = y := congrArg Subtype.val hxy
    rw [← hxy']
    exact x.2
  have hψsurj : Function.Surjective ψ := by
    intro σ
    obtain ⟨θX, hθXβ⟩ := hθ A₀ hA₀
    obtain ⟨x, hx⟩ := θX.surjective σ
    exact ⟨⟨x, hsupN A₀ hA₀ x.2⟩, (hψθ A₀ hA₀ θX hθXβ x).trans hx⟩
  have hβbij : Function.Bijective D.β := ⟨hβinj, D.surj⟩
  set J : Subgroup (MulAut W) := ⨆ A ∈ 𝒜, A with hJ
  have hAJ : ∀ A ∈ 𝒜, A ≤ J := fun A hA => le_iSup₂_of_le A hA le_rfl
  have hJQ : J ≤ Q := iSup₂_le fun A hA => (h𝒜 A hA).1
  have hJN : J ≤ N := hJQ.trans hQN
  have hBA : ∀ A ∈ 𝒜, ∃ T : Set (Equiv.Perm (Fin n)), (∀ t ∈ T, t.IsSwap) ∧
      (∀ t ∈ T, ∀ t' ∈ T, t * t' = t' * t) ∧ (A.subgroupOf N).map ψ = Subgroup.closure T := by
    intro A hA
    obtain ⟨hAQ, hAe, hAne, hAw⟩ := h𝒜 A hA
    have hAN : A ≤ N := hAQ.trans hQN
    have hcB : ∀ a ∈ (A.subgroupOf N).map ψ, ∀ b ∈ (A.subgroupOf N).map ψ, a * b = b * a := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hAe.1 _ (Subgroup.mem_subgroupOf.mp hx) _ (Subgroup.mem_subgroupOf.mp hy))
    obtain ⟨⟨T, hTswap, hTcomm, hBT⟩, -, -⟩ :=
      sym_offender_generated_weak n hn h3 hcB (D.card_le_offender hn h5 hAN hAw)
    exact ⟨T, hTswap, hTcomm, hBT⟩
  set Jh : Subgroup (Equiv.Perm (Fin n)) := (J.subgroupOf N).map ψ with hJh
  have hBAJh : ∀ A ∈ 𝒜, (A.subgroupOf N).map ψ ≤ Jh := by
    rintro A hA _ ⟨x, hx, rfl⟩
    exact ⟨x, Subgroup.mem_subgroupOf.mpr (hAJ A hA (Subgroup.mem_subgroupOf.mp hx)), rfl⟩
  have hJh2 : ∀ y ∈ Jh, ∃ k : ℕ, y ^ 2 ^ k = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨k, hk⟩ := hQ ⟨(x : MulAut W), hJQ (Subgroup.mem_subgroupOf.mp hx)⟩
    refine ⟨k, ?_⟩
    rw [← map_pow]
    have : x ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [this, map_one]
  set T' : Set (Equiv.Perm (Fin n)) := {t | t.IsSwap ∧ t ∈ Jh} with hT'
  have hT'comm : ∀ t ∈ T', ∀ t' ∈ T', t * t' = t' * t := by
    rintro t ⟨ht, htJ⟩ t' ⟨ht', ht'J⟩
    exact commute_of_isSwap_of_pow_two_pow_eq_one ht ht' (hJh2 _ (Jh.mul_mem htJ ht'J))
  have hBAle : ∀ A ∈ 𝒜, (A.subgroupOf N).map ψ ≤ Subgroup.closure T' := by
    intro A hA
    obtain ⟨T, hTs, -, hBT⟩ := hBA A hA
    rw [hBT]
    refine (Subgroup.closure_le _).2 fun t ht => Subgroup.subset_closure ⟨hTs t ht, ?_⟩
    exact hBAJh A hA (hBT ▸ Subgroup.subset_closure ht)
  let K : Subgroup (MulAut W) := ((Subgroup.closure T').comap ψ).map N.subtype
  have hAK : ∀ A ∈ 𝒜, A ≤ K := by
    intro A hA x hx
    have hxN : x ∈ N := (h𝒜 A hA).1.trans hQN hx
    exact ⟨⟨x, hxN⟩, hBAle A hA ⟨⟨x, hxN⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩, rfl⟩
  have hJK : J ≤ K := iSup₂_le hAK
  have hJhle : Jh ≤ Subgroup.closure T' := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨x', hx'ψ, hx'⟩ := hJK (Subgroup.mem_subgroupOf.mp hx)
    have : x' = x := Subtype.ext hx'
    rw [← this]
    exact hx'ψ
  have hJheq : Jh = Subgroup.closure T' :=
    le_antisymm hJhle ((Subgroup.closure_le _).2 fun t ht => ht.2)
  have hT'ne : T'.Nonempty := by
    obtain ⟨T, hTs, -, hBT⟩ := hBA A₀ hA₀
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    have hTe : T = ∅ := by
      rw [← Set.subset_empty_iff, ← hcon]
      intro t ht
      exact ⟨hTs t ht, hBAJh A₀ hA₀ (hBT ▸ Subgroup.subset_closure ht)⟩
    rw [hTe, Subgroup.closure_empty] at hBT
    apply (h𝒜 A₀ hA₀).2.2.1
    rw [eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_bot]
    have h1 : ψ ⟨a, hA₀N ha⟩ ∈ (A₀.subgroupOf N).map ψ :=
      ⟨⟨a, hA₀N ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
    rw [hBT, Subgroup.mem_bot, ← map_one ψ] at h1
    exact congrArg Subtype.val (hψinj h1)
  have hT'fin : T'.Finite := Set.toFinite T'
  have hT'swap : ∀ t ∈ T', t.IsSwap := fun t ht => ht.1
  have hT'sq : ∀ t ∈ T', t ^ 2 = 1 := fun t ht => sq_eq_one_of_isSwap ht.1
  have hk1 : 1 ≤ T'.ncard := (Set.ncard_pos hT'fin).2 hT'ne
  have hk2 : 2 * T'.ncard ≤ n := two_mul_ncard_le hT'swap hT'comm
  have hJcard : Nat.card ↥J = 2 ^ T'.ncard := by
    have h1 : Nat.card ↥J = Nat.card ↥Jh := by
      rw [hJh, Subgroup.card_map_of_injective hψinj]
      exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJN).toEquiv).symm
    rw [h1, hJheq]
    exact le_antisymm (card_closure_le_two_pow hT'fin hT'sq hT'comm)
      (two_pow_ncard_le_card_closure hT'fin hT'swap hT'comm)
  have hswapJ : IsSwapGroupOfSize Jh T'.ncard := ⟨T', hT'swap, hT'comm, rfl, hJheq⟩
  have hmaxJ : (∃ A ∈ 𝒜, Nat.card ↥A = 2 ^ ((n - 1) / 2)) → IsMaxSwapGroup Jh := by
    rintro ⟨A, hA, hAcard⟩
    have hle : Nat.card ↥A ≤ Nat.card ↥J := Subgroup.card_le_of_le (hAJ A hA)
    rw [hAcard, hJcard] at hle
    have h1 : (n - 1) / 2 ≤ T'.ncard := (Nat.pow_le_pow_iff_right (by norm_num)).1 hle
    have h2 : T'.ncard ≤ (n - 1) / 2 := by
      obtain ⟨j, hj⟩ := hn
      omega
    have h3 : T'.ncard = (n - 1) / 2 := le_antisymm h2 h1
    rw [h3] at hswapJ
    exact hswapJ
  refine ⟨hfixE, hβbij, ⟨hψinj, hψsurj⟩, hsup,
    ⟨T'.ncard, hk1, hk2, hswapJ, hJcard, hmaxJ⟩, ?_⟩
  intro Q'' hQ'' hQ''N hfix q hq
  have hqN : q ∈ N := hQ''N hq
  have hπ : ψ ⟨q, hqN⟩ ∈ Subgroup.closure T' := by
    apply mem_closure_of_fixes hn (fun t ht => ht.1) hT'comm
    intro v hv
    obtain ⟨w, rfl⟩ := D.surj v
    have hwJ : w ∈ fixV J := by
      intro a ha
      have haN : a ∈ N := hJN ha
      have hψa : ψ ⟨a, haN⟩ ∈ Subgroup.closure T' :=
        hJhle ⟨⟨a, haN⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
      have h1 : coreAct n (ψ ⟨a, haN⟩) (D.β w) = D.β w := hv _ (Subgroup.mem_map_of_mem _ hψa)
      have h2 : D.β (a w) = D.β w := by
        rw [D.psi_spec hn h5 ⟨a, haN⟩ w]
        exact h1
      exact hβinj h2
    have hqw : q w = w := hfix hwJ q hq
    rw [← D.psi_spec hn h5 ⟨q, hqN⟩ w, hqw]
  rw [← hJheq] at hπ
  obtain ⟨x, hx, hxq⟩ := hπ
  have hxe : x = ⟨q, hqN⟩ := hψinj hxq
  have hx' : (⟨q, hqN⟩ : ↥N) ∈ J.subgroupOf N := hxe ▸ hx
  exact Subgroup.mem_subgroupOf.mp hx'

end Faithful

end CFSG.CGT.PushingUpLit.BHS6
