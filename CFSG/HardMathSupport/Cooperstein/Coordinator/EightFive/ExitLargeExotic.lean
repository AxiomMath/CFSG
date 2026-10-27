module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ExitLargeEq
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ExitLargeFpf
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ExitQuot
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.StepLarge

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin Equiv Equiv.Perm MulAction

theorem exists_mem_sylow_not_mem_alternatingGroup {α : Type*} [Fintype α] [DecidableEq α]
    [Nontrivial α] (P : Sylow 2 (Perm α)) :
    ∃ r ∈ (P : Subgroup (Perm α)), r ∉ alternatingGroup α := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra h
  push Not at h
  have hdvd := Subgroup.index_dvd_of_le (show (P : Subgroup (Perm α)) ≤ alternatingGroup α from h)
  rw [alternatingGroup.index_eq_two] at hdvd
  exact P.not_dvd_index hdvd

variable {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {m n : ℕ} {ψ : ↥H →* Perm (Fin n)}

theorem largeKappa_surjective (hψ : Function.Injective ψ)
    (hAlt : alternatingGroup (Fin n) ≤ ψ.range) {ι : Fin m ↪ Fin n} (hmn : m + 2 ≤ n)
    (R' : Sylow 2 (Perm ↥(Set.range ι)ᶜ)) : Function.Surjective (largeKappa ψ ι R') := by
  classical
  have : Nontrivial ↥(Set.range ι)ᶜ := by
    obtain ⟨p, hp⟩ := exists_notMem_of_card_lt (Finset.univ.map ι) (by simp; omega)
    obtain ⟨q, hq⟩ := exists_notMem_of_card_lt (insert p (Finset.univ.map ι))
      (by have := Finset.card_insert_le p (Finset.univ.map ι); simp at this ⊢; omega)
    simp only [Finset.mem_insert, not_or] at hq
    have hpR : p ∈ (Set.range ι)ᶜ := fun ⟨i, hi⟩ => hp (hi ▸ Finset.mem_map_of_mem ι
      (Finset.mem_univ i))
    have hqR : q ∈ (Set.range ι)ᶜ := fun ⟨i, hi⟩ => hq.2 (hi ▸ Finset.mem_map_of_mem ι
      (Finset.mem_univ i))
    exact ⟨⟨⟨p, hpR⟩, ⟨q, hqR⟩, fun h => hq.1 (congrArg Subtype.val h).symm⟩⟩
  obtain ⟨r, hrR, hrA⟩ := exists_mem_sylow_not_mem_alternatingGroup R'
  intro σ
  by_cases hσ : σ ∈ alternatingGroup (Fin m)
  · have hmemK : ∀ τ, ((altRho hψ hAlt).comp (altLift ι)) τ ∈ largeK ψ ι R' := fun τ =>
      altRho_altLift_mem_largeK hψ hAlt τ
    set e := ((altRho hψ hAlt).comp (altLift ι)).codRestrict _ hmemK with he_def
    have he : ∀ τ, largeKappa ψ ι R' (e τ) = τ := fun τ =>
      restrictHom_eq_of_eq_altLift (apply_altRho hψ hAlt _)
    exact ⟨e ⟨σ, hσ⟩, he _⟩
  ·
    set π : Perm (Fin n) := viaEmbedding σ ι * ofSubtype r with hπ
    have hin : ∀ i, π (ι i) = ι (σ i) := fun i => by
      rw [hπ, Perm.mul_apply, ofSubtype_apply_of_not_mem r (fun h => h ⟨i, rfl⟩),
        viaEmbedding_apply]
    have hout : ∀ x (hx : x ∈ (Set.range ι)ᶜ), π x = r ⟨x, hx⟩ := fun x hx => by
      rw [hπ, Perm.mul_apply, ofSubtype_apply_of_mem r hx,
        viaEmbedding_apply_of_notMem _ _ _ (r ⟨x, hx⟩).2]
    have hstab : π ∈ permSetStab (Set.range ι)ᶜ := by
      intro x
      by_cases hx : x ∈ (Set.range ι)ᶜ
      · rw [hout x hx]
        exact ⟨fun _ => hx, fun _ => (r ⟨x, hx⟩).2⟩
      · obtain ⟨i, rfl⟩ := not_not.1 hx
        rw [hin]
        exact ⟨fun h => absurd ⟨σ i, rfl⟩ h, fun h => absurd h hx⟩
    have hres : restrictSet (Set.range ι)ᶜ ⟨π, hstab⟩ = r :=
      Equiv.ext fun x => Subtype.ext (hout x x.2)
    have hπA : π ∈ alternatingGroup (Fin n) := by
      rw [mem_alternatingGroup] at hσ hrA ⊢
      rw [hπ, map_mul, sign_viaEmbedding, sign_ofSubtype, Int.units_ne_iff_eq_neg.1 hσ,
        Int.units_ne_iff_eq_neg.1 hrA]
      decide
    obtain ⟨h, hh⟩ := hAlt hπA
    have hK : (h : MulAut V) ∈ largeK ψ ι R' :=
      coe_mem_preSub.2 (by rw [hh]; exact mem_restrictPre.2 ⟨hstab, hres ▸ hrR⟩)
    refine ⟨⟨h, hK⟩, (restrictHom_eq_iff _ σ).2 fun i => ?_⟩
    change ψ h (ι i) = ι (σ i)
    rw [hh, hin]

theorem exitLargeExotic : ExitLargeExotic := by
  intro V _ _ hV n hn H ψ hψ hAlt hT₁ A hA hmin ι R' hAK hC hex
  classical
  obtain ⟨-, hE2, hE3⟩ := hex
  have hKW := largeK_le_stabSub ψ ι R'
  set W := fixV (largeQ ψ ι R') with hW
  set κ := largeKappa ψ ι R' with hκ
  set ψW := autSubLift κ hKW hC with hψW
  have hψWtop : ψW.range = ⊤ := by
    rw [hψW, range_autSubLift, MonoidHom.range_eq_top]
    exact largeKappa_surjective hψ hAlt (by omega) R'
  obtain ⟨a, ha, ha1⟩ : ∃ a : MulAut V, ∃ ha : a ∈ A, κ ⟨a, hAK ha⟩ ≠ 1 := by
    obtain ⟨g, hg, hgi⟩ : ∃ g ∈ (A.subgroupOf H).map ψ, g (ι 0) ≠ ι 0 := by
      by_contra h
      push Not at h
      have hsub : orbit ((A.subgroupOf H).map ψ) (ι 0) ⊆ {ι 0} := by
        intro y hy
        obtain ⟨g, hg, rfl⟩ := mem_orbit_iff_perm.1 hy
        exact h g hg
      have h2 := Set.ncard_le_ncard hsub (Set.finite_singleton _)
      rw [Set.ncard_singleton, ← Nat.card_coe_set_eq] at h2
      have := hmin (ι 0)
      omega
    obtain ⟨a', ha', rfl⟩ := mem_map_subgroupOf.1 hg
    refine ⟨a', ha', fun h => hgi ?_⟩
    have := restrictHom_apply_apply (hK := largeK_le ψ ι R') ⟨(a' : MulAut V), hAK ha'⟩ 0
    change ι (κ ⟨a', hAK ha'⟩ 0) = _ at this
    rw [h, Perm.one_apply] at this
    exact this.symm
  have hAW : ∀ b ∈ A, ∀ w ∈ W, b w ∈ W := fun b hb w hw => ((hKW (hAK hb)) w).2 hw
  have hWA : commSub W A ≠ ⊥ := fun hbot =>
    ha1 (hC ⟨a, hAK ha⟩ fun w hw => (commSub_eq_bot_iff.1 hbot) hw a ha)
  have hoffW := isFFStarOffender_autSub hA hAW hWA (autSub_mono hAK W)
  rcases natVia_or_altRho_altLift_mem_centQuot hV hψ hAlt (by norm_num) (by omega) hT₁ hA hAK hC
      ha ha1 (hE3 hψWtop _ hoffW) with h | hVE
  · exact h
  exfalso
  set ρE : alternatingGroup (Fin 8) →* MulAut V := (altRho hψ hAlt).comp (altLift ι) with hρE
  have hmemK : ∀ σ, ρE σ ∈ largeK ψ ι R' := fun σ => altRho_altLift_mem_largeK hψ hAlt σ
  set e := ρE.codRestrict _ hmemK with he_def
  have he : ∀ σ, κ (e σ) = σ := fun σ => restrictHom_eq_of_eq_altLift (apply_altRho hψ hAlt _)
  set P : Subgroup V := (commV (altPre ψW)).map W.subtype with hP
  have hWP : ∀ σ : alternatingGroup (Fin 8), ∀ w ∈ W, ρE σ w * w⁻¹ ∈ P := by
    intro σ w hw
    have hx : ((autSubHom hKW (e σ) : ↥(autSub (largeK ψ ι R') W)) : MulAut ↥W) ∈ altPre ψW :=
      coe_mem_altPre_iff.2 (by rw [hψW, autSubLift_apply, he]; exact σ.2)
    exact ⟨_, mul_inv_mem_commV hx ⟨w, hw⟩, rfl⟩
  have hVP : ∀ σ : alternatingGroup (Fin 8), ∀ v, ρE σ v * v⁻¹ ∈ P := by
    intro σ v
    have key := sub_mem_of_perfect (commutator_alternatingGroup_eq_top
        (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega))
      (autToEnd.comp ρE) Set.univ {x | Additive.toMul x ∈ W} (Subgroup.toAddSubgroup P)
      (fun g w _ => by
        change ρE g (Additive.toMul w) / Additive.toMul w ∈ W
        rw [div_eq_mul_inv]
        exact hVE g _)
      (fun g t ht => by
        change ρE g (Additive.toMul t) / Additive.toMul t ∈ P
        rw [div_eq_mul_inv]
        exact hWP g _ ht)
      σ (Additive.ofMul v) (Set.mem_univ _)
    change ρE σ v / v ∈ P at key
    rwa [div_eq_mul_inv] at key
  have hfixle : ∀ σ τ : alternatingGroup (Fin 8), (σ : Perm (Fin 8)).IsThreeCycle → σ * τ = τ * σ →
      fixV (Subgroup.zpowers (ρE σ)) ≤ fixV (Subgroup.zpowers (ρE τ)) := by
    intro σ τ hσ hστ v hv
    rw [mem_fixV_zpowers_iff] at hv ⊢
    obtain ⟨u', hu', hu'eq⟩ := hVP τ v
    have hfix : ρE σ (ρE τ v * v⁻¹) = ρE τ v * v⁻¹ := by
      have hc : ρE σ * ρE τ = ρE τ * ρE σ := by rw [← map_mul, ← map_mul, hστ]
      have h1 : ρE σ (ρE τ v) = ρE τ (ρE σ v) := congrArg (fun φ : MulAut V => φ v) hc
      rw [map_mul, map_inv, h1, hv]
    have hx3 : (ψW (autSubHom hKW (e σ))).IsThreeCycle := by
      rw [hψW, autSubLift_apply, he]
      exact hσ
    have hbot := hE2 _ hx3
    have hu'1 : u' = 1 := by
      have hmem : u' ∈ fixV (Subgroup.zpowers
          ((autSubHom hKW (e σ) : ↥(autSub (largeK ψ ι R') W)) : MulAut ↥W)) ⊓
            commV (altPre ψW) := by
        refine ⟨mem_fixV_zpowers_iff.2 (Subtype.ext ?_), hu'⟩
        rw [coe_autSubHom_apply]
        change ρE σ (u' : V) = u'
        rw [show (u' : V) = ρE τ v * v⁻¹ from hu'eq]
        exact hfix
      rw [hbot] at hmem
      exact hmem
    have h1 : ρE τ v * v⁻¹ = 1 := by
      rw [← hu'eq, hu'1]
      rfl
    exact mul_inv_eq_one.1 h1
  obtain ⟨σ₀, hσ₀⟩ := exists_isThreeCycle (m := 8) (by norm_num)
  set C₀ := fixV (Subgroup.zpowers (ρE σ₀)) with hC₀
  have hle3 : ∀ σ τ : alternatingGroup (Fin 8), (σ : Perm (Fin 8)).IsThreeCycle →
      (τ : Perm (Fin 8)).IsThreeCycle →
        fixV (Subgroup.zpowers (ρE σ)) ≤ fixV (Subgroup.zpowers (ρE τ)) := by
    intro σ τ hσ hτ
    obtain ⟨π, hπ3, hπσ, hπτ⟩ := exists_isThreeCycle_commute_commute (n := 8) le_rfl hσ hτ
    set π' : alternatingGroup (Fin 8) := ⟨π, hπ3.mem_alternatingGroup⟩ with hπ'
    exact (hfixle σ π' hσ (Subtype.ext hπσ.eq.symm)).trans (hfixle π' τ hπ3 (Subtype.ext hπτ.eq))
  have hconst : ∀ σ : alternatingGroup (Fin 8), (σ : Perm (Fin 8)).IsThreeCycle →
      fixV (Subgroup.zpowers (ρE σ)) = C₀ := fun σ hσ =>
    le_antisymm (hle3 σ σ₀ hσ hσ₀) (hle3 σ₀ σ hσ₀ hσ)
  set Δ : Finset (Fin n) := (Finset.univ.map ι)ᶜ with hΔ
  have hΔcard : Δ.card + 6 ≤ n := by
    rw [hΔ, Finset.card_compl, Fintype.card_fin, Finset.card_map, Finset.card_univ,
      Fintype.card_fin]
    omega
  have hmemΔ : ∀ i, i ∉ Set.range ι → i ∈ Δ := fun i hi => by
    rw [hΔ, Finset.mem_compl, Finset.mem_map]
    rintro ⟨j, -, hj⟩
    exact hi ⟨j, hj⟩
  have hCΔ : ∀ x : ↥H, (ψ x).IsThreeCycle → (∀ i ∈ Δ, ψ x i = i) →
      fixV (Subgroup.zpowers (x : MulAut V)) = C₀ := by
    intro x hx3 hxΔ
    have hfix : ∀ i, i ∉ Set.range ι → ψ x i = i := fun i hi => hxΔ i (hmemΔ i hi)
    have hst : ψ x ∈ permSetStab (Set.range ι) := by
      intro y
      by_cases hy : y ∈ Set.range ι
      · refine ⟨fun _ => hy, fun _ => ?_⟩
        by_contra hxy
        have h2 : ψ x y = y := (ψ x).injective (hfix _ hxy)
        exact hxy (by rw [h2]; exact hy)
      · rw [hfix y hy]
    set k : ↥(preSub ψ (permSetStab (Set.range ι))) := ⟨x, coe_mem_preSub.2 hst⟩ with hk
    have h3' := isThreeCycle_restrictHom (hK := le_rfl) k hx3 hfix
    have hve := viaEmbedding_restrictHom (hK := le_rfl) k hfix
    set σ : alternatingGroup (Fin 8) :=
      ⟨restrictHom ψ ι (preSub ψ (permSetStab (Set.range ι))) le_rfl k, h3'.mem_alternatingGroup⟩
      with hσ
    have hρσ : ρE σ = x := altRho_eq hψ hAlt (h := x) (σ := altLift ι σ)
      (by rw [coe_altLift]; exact hve.symm)
    rw [← hρσ]
    exact hconst σ h3'
  have hCall : ∀ y : ↥H, (ψ y).IsThreeCycle → fixV (Subgroup.zpowers (y : MulAut V)) = C₀ :=
    fun y hy => fixV_zpowers_eq_of_fix hAlt Δ hΔcard hCΔ hy
  have hCL := fixV_altPre_eq_of_forall (by omega) hψ hAlt hCall
  obtain ⟨W', _, _, G, φ, e', hW', hφ, hφA, h3, -, -, -, hB⟩ :=
    exists_quot hV (by omega) hψ hAlt fun y hy => (hCall y hy).trans hCL.symm
  obtain ⟨B', hB'G, hB'1, hB'el, hB'card, -⟩ := hB A hA
  exact absurd hB'card (not_le.2 (card_mul_card_fixV_lt_of_threeCycle hW' (by omega) (by omega)
    hφ hφA h3 hB'G hB'1 hB'el))

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
