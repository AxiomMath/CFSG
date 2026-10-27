module

public import CFSG.Foundations.QuasisimpleMulEquiv

public section

namespace CFSG.LocalCores

open Subgroup

universe u

section Quasisimple

variable {G : Type*} [Group G]

theorem perfect_double_commutator {P X : Subgroup G} (hP : Group.IsPerfect P)
    (h : ⁅⁅P, X⁆, P⁆ = ⊥) : ⁅P, X⁆ = ⊥ := by
  have h2 : ⁅⁅X, P⁆, P⁆ = ⊥ := by
    rw [Subgroup.commutator_comm X P]
    exact h
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := P) (H₂ := P) (H₃ := X) h h2
  rwa [Subgroup.isPerfect_iff.mp hP] at h3

theorem isQuasisimple_nontrivial {Q : Type*} [Group Q] (hQ : IsQuasisimple Q) : Nontrivial Q := by
  obtain ⟨-, -, a, b, hab⟩ := hQ
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨a * b, b * a, fun h => hab ?_⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]

theorem isQuasisimple_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hA : IsQuasisimple A) : IsQuasisimple B :=
  hA.of_mulEquiv e.symm

theorem quasisimple_normal_subgroups {Q : Type*} [Group Q] (hQ : IsQuasisimple Q)
    {N : Subgroup Q} (hN : N.Normal) : N = ⊤ ∨ N ≤ center Q := by
  obtain ⟨hp, hs, -⟩ := hQ
  have := hN.map (QuotientGroup.mk' (center Q)) (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' (center Q))) with
    h | h
  · right
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  · left
    have hsup : N ⊔ center Q = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (center Q)) N
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hZ : ⁅center Q, center Q⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.center_le_centralizer _)
    have hmap : (⊤ : Subgroup Q).map (QuotientGroup.mk' N) =
        (center Q).map (QuotientGroup.mk' N) := by
      rw [← hsup, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
    have hcomm : commutator Q ≤ N := by
      rw [_root_.commutator_def, ← QuotientGroup.ker_mk' N, ← Subgroup.map_eq_bot_iff,
        Subgroup.map_commutator, hmap, ← Subgroup.map_commutator, hZ, Subgroup.map_bot]
    rw [Group.isPerfect_def] at hp
    exact eq_top_iff.mpr (hp ▸ hcomm)

end Quasisimple

section Components

variable {G : Type*} [Group G]

theorem component_overgroup {K H : Subgroup G} (hK : IsComponent K) (hKH : K ≤ H) :
    IsComponent (K.subgroupOf H) :=
  ⟨isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKH).symm hK.1, hK.2.subgroupOf⟩

theorem isComponent_map_mulEquiv {H : Type*} [Group H] (f : G ≃* H) {K : Subgroup G}
    (hK : IsComponent K) : IsComponent (K.map f.toMonoidHom) :=
  ⟨isQuasisimple_of_mulEquiv (K.equivMapOfInjective f.toMonoidHom f.injective) hK.1,
    hK.2.map f.surjective⟩

theorem map_map_symm {H : Type*} [Group H] (f : G ≃* H) (K : Subgroup G) :
    (K.map f.toMonoidHom).map f.symm.toMonoidHom = K := by
  rw [Subgroup.map_map]
  convert Subgroup.map_id K
  ext x
  simp

theorem component_isomorphism {H : Type*} [Group H] (f : G ≃* H) :
    (∀ K : Subgroup G, IsComponent K ↔ IsComponent (K.map f.toMonoidHom)) ∧
      Set.BijOn (fun K : Subgroup G => K.map f.toMonoidHom) {K | IsComponent K}
        {L | IsComponent L} := by
  have hiff : ∀ K : Subgroup G, IsComponent K ↔ IsComponent (K.map f.toMonoidHom) :=
    fun K => ⟨fun hK => isComponent_map_mulEquiv f hK, fun hK => by
      simpa only [map_map_symm] using isComponent_map_mulEquiv f.symm hK⟩
  refine ⟨hiff, fun K hK => (hiff K).mp hK, fun K _ L _ h => ?_, fun L hL => ?_⟩
  · exact Subgroup.map_injective f.injective h
  · refine ⟨L.map f.symm.toMonoidHom, isComponent_map_mulEquiv f.symm hL, ?_⟩
    have := map_map_symm f.symm L
    simpa only [MulEquiv.symm_symm] using this

theorem le_of_subgroupOf_le {K H L : Subgroup G} (hKL : K ≤ L)
    (h : K.subgroupOf L ≤ H.subgroupOf L) : K ≤ H := by
  have := Subgroup.map_mono (f := L.subtype) h
  rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr hKL] at this
  exact this.trans inf_le_left

theorem commutator_inf_eq_bot_of_subgroupOf {K H L : Subgroup G} (hKL : K ≤ L)
    (h : ⁅K.subgroupOf L, H.subgroupOf L⁆ = ⊥) : ⁅K, H ⊓ L⁆ = ⊥ := by
  have := congrArg (Subgroup.map L.subtype) h
  rwa [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr hKL, Subgroup.map_bot] at this

end Components

section Dichotomy

theorem component_normal_subgroup_aux (n : ℕ) :
    ∀ (G : Type u) [Group G] [Finite G], Nat.card G = n → ∀ {K N : Subgroup G},
      IsComponent K → N.Normal → K ≤ N ∨ ⁅K, N⁆ = ⊥ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ hcard K N hK hN
  by_cases hKtop : K = ⊤
  · subst hKtop
    have hQ : IsQuasisimple G := isQuasisimple_of_mulEquiv Subgroup.topEquiv hK.1
    rcases quasisimple_normal_subgroups hQ hN with h | h
    · exact Or.inl (le_of_eq h.symm)
    · exact Or.inr (Subgroup.commutator_top_left_eq_bot_iff_le_center.mpr h)
  obtain ⟨M, hMn, hKM, hMlt⟩ := hK.2.lt_normal.resolve_left hKtop
  have hMcard : Nat.card M < n := by
    rw [← hcard, ← Subgroup.card_top (G := G)]
    exact Subgroup.card_lt_of_lt hMlt
  rcases ih _ hMcard M rfl (component_overgroup hK hKM) (hN.subgroupOf M) with h | h
  · exact Or.inl (le_of_subgroupOf_le hKM h)
  · right
    have hKNM : ⁅K, N ⊓ M⁆ = ⊥ := commutator_inf_eq_bot_of_subgroupOf hKM h
    have hle : ⁅K, N⁆ ≤ N ⊓ M := by
      have : ⁅K, N⁆ ≤ ⁅M, N⁆ := Subgroup.commutator_mono hKM le_rfl
      exact this.trans ((Subgroup.commutator_le_inf M N).trans (inf_comm M N).le)
    have hP : Group.IsPerfect K := hK.1.1
    refine perfect_double_commutator hP (le_bot_iff.mp ?_)
    calc ⁅⁅K, N⁆, K⁆ ≤ ⁅N ⊓ M, K⁆ := Subgroup.commutator_mono hle le_rfl
      _ = ⁅K, N ⊓ M⁆ := Subgroup.commutator_comm _ _
      _ = ⊥ := hKNM

variable {G : Type u} [Group G]

theorem component_normal_subgroup [Finite G] {K N : Subgroup G} (hK : IsComponent K)
    (hN : N.Normal) : K ≤ N ∨ ⁅K, N⁆ = ⊥ :=
  component_normal_subgroup_aux _ G rfl hK hN

theorem component_subnormal_subgroup [Finite G] {K U : Subgroup G} (hK : IsComponent K)
    (hU : U.IsSubnormal) : K ≤ U ∨ ⁅K, U⁆ = ⊥ := by
  induction hU with
  | top => exact Or.inl le_top
  | step A L hAL _ hAn ih =>
    rcases ih with hKL | hKL
    · rcases component_normal_subgroup (component_overgroup hK hKL) hAn with h | h
      · exact Or.inl (le_of_subgroupOf_le hKL h)
      · right
        have := commutator_inf_eq_bot_of_subgroupOf hKL h
        rwa [inf_eq_left.mpr hAL] at this
    · exact Or.inr (le_bot_iff.mp (hKL ▸ Subgroup.commutator_mono le_rfl hAL))

theorem component_solvable_centralizer [Finite G] {R : Subgroup G} (hRs : Group.IsSolvable R)
    (hR : R.IsSubnormal) : (∀ K : Subgroup G, IsComponent K → ⁅K, R⁆ = ⊥) ∧ ⁅layer G, R⁆ = ⊥ := by
  have hK : ∀ K : Subgroup G, IsComponent K → ⁅K, R⁆ = ⊥ := by
    intro K hK
    rcases component_subnormal_subgroup hK hR with h | h
    · exfalso
      have : Group.IsSolvable K :=
        Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective h)
      have : Nontrivial K := isQuasisimple_nontrivial hK.1
      have : Group.IsPerfect K := hK.1.1
      exact Group.IsPerfect.not_isSolvable K inferInstance
    · exact h
  refine ⟨hK, Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (sSup_le fun K hKc => ?_)⟩
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hK K hKc)

theorem distinct_components_commute [Finite G] {K L : Subgroup G} (hK : IsComponent K)
    (hL : IsComponent L) : K = L ∨ ⁅K, L⁆ = ⊥ := by
  rcases component_subnormal_subgroup hK hL.2 with hKL | h
  · rcases component_subnormal_subgroup hL hK.2 with hLK | h'
    · exact Or.inl (le_antisymm hKL hLK)
    · right
      rw [Subgroup.commutator_comm]
      exact h'
  · exact Or.inr h

end Dichotomy

section Layer

variable {G : Type*} [Group G]

theorem layer_characteristic : (layer G).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro φ
  have hbij := (component_isomorphism φ).2
  change MulEquiv.mapSubgroup φ (sSup {K : Subgroup G | IsComponent K}) = layer G
  rw [OrderIso.map_sSup, ← sSup_image]
  exact congrArg sSup hbij.image_eq

theorem fitting_layer_commute [Finite G] : ⁅fittingSubgroup G, layer G⁆ = ⊥ := by
  rw [Subgroup.commutator_comm]
  exact (component_solvable_centralizer (G := G) inferInstance
    fittingSubgroup_normal.isSubnormal).2

theorem generalized_fitting_characteristic :
    (generalizedFitting G).Characteristic ∧ (generalizedFitting G).Normal := by
  have hc : (generalizedFitting G).Characteristic := by
    rw [Subgroup.characteristic_iff_map_eq]
    intro φ
    have h1 := Subgroup.characteristic_iff_map_eq.mp fittingSubgroup_characteristic φ
    have h2 := Subgroup.characteristic_iff_map_eq.mp layer_characteristic φ
    change (fittingSubgroup G ⊔ layer G).map φ.toMonoidHom = fittingSubgroup G ⊔ layer G
    rw [Subgroup.map_sup, h1, h2]
  exact ⟨hc, inferInstance⟩

end Layer

end CFSG.LocalCores
