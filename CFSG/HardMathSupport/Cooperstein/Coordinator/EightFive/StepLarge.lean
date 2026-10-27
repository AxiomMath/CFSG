module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ToolLarge
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ToolOrbit
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ToolFaith
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Perfect

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin CFSG.RankThree.PartTwo Equiv Equiv.Perm MulAction
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender

@[expose] def ExitLargeNat : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ n : ℕ, (n = 12 ∨ n = 16) →
    ∀ (H : Subgroup (MulAut V)) (ψ : ↥H →* Perm (Fin n)), Function.Injective ψ →
      alternatingGroup (Fin n) ≤ ψ.range → TPerm (n - 1) →
      ∀ A : Subgroup (MulAut V), IsFFStarOffender H A →
      (∀ i : Fin n, 4 ≤ Nat.card (orbit ((A.subgroupOf H).map ψ) i)) →
      ∀ ι : Fin 8 ↪ Fin n, ∀ R' : Sylow 2 (Perm ↥(Set.range ι)ᶜ), A ≤ largeK ψ ι R' →
      ∀ hC : (∀ k : ↥(largeK ψ ι R'), (∀ w ∈ fixV (largeQ ψ ι R'), (k : MulAut V) w = w) →
          largeKappa ψ ι R' k = 1),
        NatVia (autSubLift (largeKappa ψ ι R') (largeK_le_stabSub ψ ι R') hC)
          (commV (autSub (largeK ψ ι R') (fixV (largeQ ψ ι R')))) →
        IsPretransitive ((A.subgroupOf (largeK ψ ι R')).map (largeKappa ψ ι R')) (Fin 8) →
        NatVia ψ (commV H)

@[expose] def ExitLargeExotic : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ n : ℕ, (n = 12 ∨ n = 16) →
    ∀ (H : Subgroup (MulAut V)) (ψ : ↥H →* Perm (Fin n)), Function.Injective ψ →
      alternatingGroup (Fin n) ≤ ψ.range → TPerm (n - 1) →
      ∀ A : Subgroup (MulAut V), IsFFStarOffender H A →
      (∀ i : Fin n, 4 ≤ Nat.card (orbit ((A.subgroupOf H).map ψ) i)) →
      ∀ ι : Fin 8 ↪ Fin n, ∀ R' : Sylow 2 (Perm ↥(Set.range ι)ᶜ), A ≤ largeK ψ ι R' →
      ∀ hC : (∀ k : ↥(largeK ψ ι R'), (∀ w ∈ fixV (largeQ ψ ι R'), (k : MulAut V) w = w) →
          largeKappa ψ ι R' k = 1),
        Exotic (autSubLift (largeKappa ψ ι R') (largeK_le_stabSub ψ ι R') hC) →
        NatVia ψ (commV H)

variable {V : Type} [CommGroup V] [Finite V] {H : Subgroup (MulAut V)} {n : ℕ}
  {ψ : ↥H →* Perm (Fin n)} {A : Subgroup (MulAut V)}

theorem natVia_of_exitLargeNat (hexit : ExitLargeNat) {m : ℕ} (hm : m = 8)
    (hn : n = 12 ∨ n = 16) (hV : ∀ v : V, v ^ 2 = 1) (hψ : Function.Injective ψ)
    (hAlt : alternatingGroup (Fin n) ≤ ψ.range) (hT₁ : TPerm (n - 1)) (hA : IsFFStarOffender H A)
    (hmin : ∀ i : Fin n, 4 ≤ Nat.card (orbit ((A.subgroupOf H).map ψ) i)) (ι : Fin m ↪ Fin n)
    (R' : Sylow 2 (Perm ↥(Set.range ι)ᶜ)) (hAK : A ≤ largeK ψ ι R')
    (hC : ∀ k : ↥(largeK ψ ι R'), (∀ w ∈ fixV (largeQ ψ ι R'), (k : MulAut V) w = w) →
      largeKappa ψ ι R' k = 1)
    (hnat : NatVia (autSubLift (largeKappa ψ ι R') (largeK_le_stabSub ψ ι R') hC)
      (commV (autSub (largeK ψ ι R') (fixV (largeQ ψ ι R')))))
    (htr : IsPretransitive ((A.subgroupOf (largeK ψ ι R')).map (largeKappa ψ ι R')) (Fin m)) :
    NatVia ψ (commV H) := by
  subst hm
  exact hexit V hV n hn H ψ hψ hAlt hT₁ A hA hmin ι R' hAK hC hnat htr

theorem natVia_of_exitLargeExotic (hexit : ExitLargeExotic) {m : ℕ} (hm : m = 8)
    (hn : n = 12 ∨ n = 16) (hV : ∀ v : V, v ^ 2 = 1) (hψ : Function.Injective ψ)
    (hAlt : alternatingGroup (Fin n) ≤ ψ.range) (hT₁ : TPerm (n - 1)) (hA : IsFFStarOffender H A)
    (hmin : ∀ i : Fin n, 4 ≤ Nat.card (orbit ((A.subgroupOf H).map ψ) i)) (ι : Fin m ↪ Fin n)
    (R' : Sylow 2 (Perm ↥(Set.range ι)ᶜ)) (hAK : A ≤ largeK ψ ι R')
    (hC : ∀ k : ↥(largeK ψ ι R'), (∀ w ∈ fixV (largeQ ψ ι R'), (k : MulAut V) w = w) →
      largeKappa ψ ι R' k = 1)
    (hex : Exotic (autSubLift (largeKappa ψ ι R') (largeK_le_stabSub ψ ι R') hC)) :
    NatVia ψ (commV H) := by
  subst hm
  exact hexit V hV n hn H ψ hψ hAlt hT₁ A hA hmin ι R' hAK hC hex

theorem step_large (hV : ∀ v : V, v ^ 2 = 1) (hψ : Function.Injective ψ)
    (hAlt : alternatingGroup (Fin n) ≤ ψ.range) (hA : IsFFStarOffender H A) (hn : 9 ≤ n)
    (hT : ∀ m, 8 ≤ m → m < n → TPerm m)
    (hmin : ∀ i : Fin n, 4 ≤ Nat.card (orbit ((A.subgroupOf H).map ψ) i))
    (hintr : ¬ IsPretransitive ((A.subgroupOf H).map ψ) (Fin n))
    (hexitN : ExitLargeNat) (hexitE : ExitLargeExotic) : NatVia ψ (commV H) := by
  classical
  have : Finite (MulAut V) := Finite.of_injective _ DFunLike.coe_injective
  have hE : IsExp2 ((A.subgroupOf H).map ψ) := isExp2_map_subgroupOf hA.2.2.1
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin n))
    (fun i => Nat.card (orbit ((A.subgroupOf H).map ψ) i))
    (⟨⟨0, by omega⟩, Finset.mem_univ _⟩ : (Finset.univ : Finset (Fin n)).Nonempty)
  have hfin := Set.toFinite (orbit ((A.subgroupOf H).map ψ) i₀)
  have hscard : hfin.toFinset.card = Nat.card (orbit ((A.subgroupOf H).map ψ) i₀) := by
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hfin]
  obtain ⟨m, hmdef⟩ : ∃ m, m + hfin.toFinset.card = n := ⟨n - hfin.toFinset.card, by
    have := Finset.card_le_univ hfin.toFinset
    rw [Fintype.card_fin] at this
    omega⟩
  obtain ⟨ι, hι⟩ := exists_embedding_range_compl hfin.toFinset hmdef
  have hιΓ : ∀ x, x ∈ Set.range ι ↔ x ∉ orbit ((A.subgroupOf H).map ψ) i₀ := fun x =>
    (hι x).trans (by rw [Set.Finite.mem_toFinset])
  have hΓinv : ∀ g ∈ (A.subgroupOf H).map ψ, g ∈ permSetStab (Set.range ι) := fun g hg x => by
    rw [hιΓ, hιΓ, apply_mem_orbit_iff hg]
  have hΓcinv : ∀ g ∈ (A.subgroupOf H).map ψ, g ∈ permSetStab (Set.range ι)ᶜ := fun g hg => by
    rw [permSetStab_compl]
    exact hΓinv g hg
  obtain ⟨j₀, hj₀⟩ : ∃ j, j ∈ Set.range ι := by
    by_contra h
    push Not at h
    exact hintr (isPretransitive_of_forall_mem_orbit fun j => by
      by_contra hj
      exact h j ((hιΓ j).2 hj))
  have hsm : Nat.card (orbit ((A.subgroupOf H).map ψ) i₀) ≤ m := by
    refine (hi₀ j₀ (Finset.mem_univ _)).trans ?_
    have hsub : orbit ((A.subgroupOf H).map ψ) j₀ ⊆ Set.range ι := by
      intro y hy
      obtain ⟨g, hg, rfl⟩ := mem_orbit_iff_perm.1 hy
      exact (hΓinv g hg j₀).2 hj₀
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq] at h1
    have h2 := Finite.card_range_le ι
    rw [Nat.card_fin] at h2
    exact h1.trans h2
  have hs4 := hmin i₀
  have hRp : IsPGroup 2 ((((A.subgroupOf H).map ψ).subgroupOf
      (permSetStab (Set.range ι)ᶜ)).map (restrictSet (Set.range ι)ᶜ)) := by
    rintro ⟨_, g, hg, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    have hgg : g * g = 1 := Subtype.ext (hE _ hg)
    rw [SubgroupClass.coe_pow, pow_one, ← map_pow, sq, hgg, map_one]
    rfl
  obtain ⟨R', hRR'⟩ := hRp.exists_le_sylow
  have hAK : A ≤ largeK ψ ι R' := fun a ha => by
    have hg : ψ ⟨a, hA.1 ha⟩ ∈ (A.subgroupOf H).map ψ := ⟨⟨a, hA.1 ha⟩, ha, rfl⟩
    exact (coe_mem_preSub (x := ⟨a, hA.1 ha⟩)).2
      (mem_restrictPre.2 ⟨hΓcinv _ hg, hRR' ⟨⟨_, hΓcinv _ hg⟩, hg, rfl⟩⟩)
  have hmemK : ∀ σ, ((altRho hψ hAlt).comp (altLift ι)) σ ∈ largeK ψ ι R' := fun σ =>
    altRho_altLift_mem_largeK hψ hAlt σ
  set e := ((altRho hψ hAlt).comp (altLift ι)).codRestrict _ hmemK with he_def
  have he : ∀ σ, largeKappa ψ ι R' (e σ) = σ := fun σ =>
    restrictHom_eq_of_eq_altLift (apply_altRho hψ hAlt _)
  have hκA : alternatingGroup (Fin m) ≤ (largeKappa ψ ι R').range := fun σ hσ =>
    ⟨e ⟨σ, hσ⟩, he _⟩
  have hEB : ∀ g ∈ (A.subgroupOf H).map ψ, ∃ b ∈ (A.subgroupOf (largeK ψ ι R')).map
      (largeKappa ψ ι R'), ∀ j, ι (b j) = g (ι j) := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨largeKappa ψ ι R' ⟨a, hAK ha⟩, ⟨⟨a, hAK ha⟩, ha, rfl⟩, fun j =>
      restrictHom_apply_apply (hK := largeK_le ψ ι R') ⟨(a : MulAut V), hAK ha⟩ j⟩
  have hBexp : IsExp2 ((A.subgroupOf (largeK ψ ι R')).map (largeKappa ψ ι R')) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul]
    have : a * a = 1 := Subtype.ext (by
      rw [Subgroup.coe_mul, ← pow_two]
      exact hA.2.2.1.2 _ ha)
    rw [this, map_one]
  have horbB : ∀ i, 4 ≤ Nat.card (orbit ((A.subgroupOf (largeK ψ ι R')).map
      (largeKappa ψ ι R')) i) := fun i =>
    (hmin (ι i)).trans (card_orbit_le_card_orbit ι hEB i)
  have hm8 : 8 ≤ m := by
    have h4 := four_dvd_of_four_le_card_orbit hBexp horbB
    rw [Nat.card_fin] at h4
    obtain ⟨k, hk⟩ := h4
    omega
  have hn1216 : m = 8 → n = 12 ∨ n = 16 := fun hm => by
    obtain ⟨d, hd⟩ := hE.card_orbit i₀
    have key : Nat.card (orbit ((A.subgroupOf H).map ψ) i₀) = 4 ∨
        Nat.card (orbit ((A.subgroupOf H).map ψ) i₀) = 8 := by
      rw [hd] at hs4 hsm ⊢
      rcases Nat.lt_or_ge d 2 with h | h
      · interval_cases d <;> norm_num at hs4
      · rcases Nat.lt_or_ge d 4 with h' | h'
        · interval_cases d <;> norm_num
        · have h16 : 2 ^ 4 ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) h'
          norm_num at h16
          omega
    omega
  have hQ : IsPGroup 2 (largeQ ψ ι R') := isPGroup_largeQ hψ R'.isPGroup'
  have hker : ∀ k : ↥(largeK ψ ι R'), largeKappa ψ ι R' k = 1 →
      ∀ w ∈ fixV (largeQ ψ ι R'), (k : MulAut V) w = w := fun k hk w hw =>
    largeKappa_eq_one_fix hk hw
  obtain ⟨σ₃, hσ₃⟩ := exists_isThreeCycle (m := m) (by omega)
  have hσ3 : σ₃ ^ 3 = 1 :=
    Subtype.ext (by rw [SubgroupClass.coe_pow, ← hσ₃.orderOf, pow_orderOf_eq_one]; rfl)
  have hx3 : (e σ₃ : MulAut V) ^ 3 = 1 := by
    change ((altRho hψ hAlt).comp (altLift ι) σ₃) ^ 3 = 1
    rw [← map_pow, hσ3, map_one]
  have hx1 : (e σ₃ : MulAut V) ≠ 1 := fun h => by
    have h1 : altRho hψ hAlt (altLift ι σ₃) = altRho hψ hAlt (altLift ι 1) := by
      rw [map_one, map_one]
      exact h
    exact hσ₃.ne_one (congrArg Subtype.val (altLift_injective ι (altRho_injective hψ hAlt h1)))
  have hC := faithW hV (by omega) (largeKappa ψ ι R') hκA hQ largeK_le_normalizer hker (e σ₃)
    (Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hx3)) hx1 (by rw [he]; exact σ₃.2)
    fun q hq => commute_altRho_altLift_of_mem_largeQ hψ hAlt σ₃ hq
  have hψWinj := autSubLift_injective (hKW := largeK_le_stabSub ψ ι R') (hC := hC) hker
  have hψWA : alternatingGroup (Fin m) ≤
      (autSubLift (largeKappa ψ ι R') (largeK_le_stabSub ψ ι R') hC).range := by
    rw [range_autSubLift]
    exact hκA
  have hWA : commSub (fixV (largeQ ψ ι R')) A ≠ ⊥ := by
    intro hbot
    have i : Fin m := ⟨0, by omega⟩
    obtain ⟨g, hg, hgi⟩ : ∃ g ∈ (A.subgroupOf H).map ψ, g (ι i) ≠ ι i := by
      by_contra h
      push Not at h
      have hsub : orbit ((A.subgroupOf H).map ψ) (ι i) ⊆ {ι i} := by
        intro y hy
        obtain ⟨g, hg, rfl⟩ := mem_orbit_iff_perm.1 hy
        exact h g hg
      have h2 := Set.ncard_le_ncard hsub (Set.finite_singleton _)
      rw [Set.ncard_singleton, ← Nat.card_coe_set_eq] at h2
      have := hmin (ι i)
      omega
    obtain ⟨a, ha, rfl⟩ := mem_map_subgroupOf.1 hg
    have hκa : largeKappa ψ ι R' ⟨a, hAK ha⟩ ≠ 1 := fun h => hgi (by
      have := restrictHom_apply_apply (hK := largeK_le ψ ι R') ⟨(a : MulAut V), hAK ha⟩ i
      change ι (largeKappa ψ ι R' ⟨a, hAK ha⟩ i) = _ at this
      rw [h, Perm.one_apply] at this
      exact this.symm)
    exact hκa (hC ⟨a, hAK ha⟩ fun w hw => (commSub_eq_bot_iff.1 hbot) hw _ ha)
  have hoffW := isFFStarOffender_autSub hA
    (fun a ha w hw => ((largeK_le_stabSub ψ ι R' (hAK ha)) w).2 hw) hWA (autSub_mono hAK _)
  have hT₁ : TPerm (n - 1) := hT (n - 1) (by omega) (by omega)
  rcases hT m hm8 (by omega) (↥(fixV (largeQ ψ ι R')))
      (fun v => Subtype.ext (by rw [SubgroupClass.coe_pow, hV]; rfl)) _ _ hψWinj hψWA
      ⟨_, hoffW⟩ with hnat | ⟨h7, -⟩ | ⟨h8, hex⟩
  ·
    have hcount := card_altHeart_le_of_natVia hψWinj hnat hoffW
    have hBeq : ((autSub A (fixV (largeQ ψ ι R'))).subgroupOf
        (autSub (largeK ψ ι R') (fixV (largeQ ψ ι R')))).map
          (autSubLift (largeKappa ψ ι R') (largeK_le_stabSub ψ ι R') hC) =
        (A.subgroupOf (largeK ψ ι R')).map (largeKappa ψ ι R') := by
      apply le_antisymm
      · rintro _ ⟨φ, hφ, rfl⟩
        obtain ⟨g, hg, hgφ⟩ := mem_autSub.1 (Subgroup.mem_subgroupOf.1 hφ)
        have hφ' : φ = autSubHom (largeK_le_stabSub ψ ι R') ⟨g, hAK hg⟩ :=
          Subtype.ext (by rw [← hgφ]; rfl)
        rw [hφ', autSubLift_apply]
        exact ⟨⟨g, hAK hg⟩, hg, rfl⟩
      · rintro _ ⟨k, hk, rfl⟩
        rw [← autSubLift_apply (hKW := largeK_le_stabSub ψ ι R') (hC := hC)]
        exact ⟨autSubHom _ k,
          mem_autSub.2 ⟨Subgroup.inclusion (largeK_le_stabSub ψ ι R') k, hk, rfl⟩, rfl⟩
    rw [hBeq] at hcount
    obtain ⟨hm8', -, htr⟩ := natFF_orbit (by omega) hBexp horbB hcount
    exact natVia_of_exitLargeNat hexitN hm8' (hn1216 hm8') hV hψ hAlt hT₁ hA hmin ι R' hAK hC
      hnat htr
  · omega
  · exact natVia_of_exitLargeExotic hexitE h8 (hn1216 h8) hV hψ hAlt hT₁ hA hmin ι R' hAK hC hex

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
