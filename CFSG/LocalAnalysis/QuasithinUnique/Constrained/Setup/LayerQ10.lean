module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerQ9
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerQ5
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerQ6
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerQ8

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.QuasithinUnique.Setup.Offender CFSG.Quasithin.B6 CFSG.QuasithinUnique
open scoped commutatorElement

universe v

theorem conjSub_map_subgroupOf {G Y : Type*} [Group G] [Group Y] {K : Subgroup G}
    (θ : ↥K →* Y) {a : G} (ha : a ∈ K) {S S' : Subgroup G} (h : conjSub a S = S') :
    conjSub (θ ⟨a, ha⟩) ((S.subgroupOf K).map θ) = (S'.subgroupOf K).map θ := by
  rw [conjSub_map_hom, ← h]
  congr 1
  show conjSub (⟨a, ha⟩ : ↥K) (S.comap K.subtype) = (conjSub a S).comap K.subtype
  rw [conjSub_comap]
  rfl

variable {k : Type*} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

theorem quadBestOffendersNormalize [CharP k 2] [Finite V] : QuadBestOffendersNormalize k V := by
  classical
  have : Finite (V ≃ₗ[k] V) := finite_linearEquiv
  intro G A hAG hAel hquad hmax L hL a₀ ha₀
  by_contra hmove
  obtain ⟨s, Lfam, hs, hinj, hcomp, hperm, htrans⟩ := exists_orbit_family hAG hL ha₀ hmove
  have hq : ∀ i, CFSG.IsQuasisimple ↥(Lfam i) := fun i => isQuasisimple_of_isComponentIn (hcomp i)
  have hcomm : ∀ i j, i ≠ j → ⁅Lfam i, Lfam j⁆ = ⊥ := fun i j hij =>
    commutator_eq_bot_of_isComponentIn_ne (hcomp i) (hcomp j) (fun h => hij (hinj h))
  obtain ⟨hAnH, hHA, hperf, hno, hch⟩ := product_facts hs Lfam hinj hq hcomm hperm htrans
  obtain ⟨H, hH⟩ : ∃ H : Subgroup (V ≃ₗ[k] V), H = ⨆ i, Lfam i := ⟨_, rfl⟩
  rw [← hH] at hAnH hHA hperf hno hch
  have hLle : ∀ i, Lfam i ≤ H := fun i => hH ▸ le_iSup Lfam i
  let i0 : Fin s := ⟨0, by omega⟩
  have hHne : ¬ (⊤ : Submodule k V) ≤ fixGL H := fun hle =>
    not_top_le_fix_of_quasisimple (hq i0) (hle.trans fun v hv x hx => hv x (hLle i0 hx))
  obtain ⟨I, hI⟩ := perfect_section hAnH hAel hHA hperf hno hch hHne hquad hmax
  have hHA' : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[k] V)) (H ⊔ A) I :=
    isInvariant_sup_subgroup hI.inv_H hI.inv_A
  obtain ⟨θ, hθ⟩ : ∃ θ : ↥(H ⊔ A) →* ((↥I ⧸ fixIn H I) ≃ₗ[k] (↥I ⧸ fixIn H I)),
      θ = actW H A I hAnH hHA' := ⟨_, rfl⟩
  obtain ⟨Lbar, hLbar⟩ : ∃ Lbar : Fin s → Subgroup ((↥I ⧸ fixIn H I) ≃ₗ[k] (↥I ⧸ fixIn H I)),
      ∀ i, Lbar i = ((Lfam i).subgroupOf (H ⊔ A)).map θ :=
    ⟨fun i => ((Lfam i).subgroupOf (H ⊔ A)).map θ, fun i => rfl⟩
  obtain ⟨Abar, hAbar⟩ : ∃ Abar : Subgroup ((↥I ⧸ fixIn H I) ≃ₗ[k] (↥I ⧸ fixIn H I)),
      Abar = (A.subgroupOf (H ⊔ A)).map θ := ⟨_, rfl⟩
  have hLleHA : ∀ i, Lfam i ≤ H ⊔ A := fun i => (hLle i).trans le_sup_left
  have hact : ∀ (S : Subgroup (V ≃ₗ[k] V)) (hS : S ≤ H ⊔ A),
      (actOn H A I hAnH hHA' S hS).range = (S.subgroupOf (H ⊔ A)).map θ := fun S hS => by
    rw [hθ]
    exact actOn_range hAnH hHA' S hS
  have hperfL : ∀ i, Group.IsPerfect ↥(Lbar i) := by
    intro i
    rw [hLbar i, ← hact (Lfam i) (hLleHA i)]
    have := (hq i).1
    exact Group.IsPerfect.range _
  have hcommL : ∀ i j, i ≠ j → ∀ x ∈ Lbar i, ∀ y ∈ Lbar j, x * y = y * x := by
    intro i j hij x hx y hy
    rw [hLbar] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 (hcomm i j hij)
      (Subgroup.mem_subgroupOf.1 hx')
    have h2 := Subgroup.mem_centralizer_iff.1 h1 (y' : V ≃ₗ[k] V) (Subgroup.mem_subgroupOf.1 hy')
    exact h2.symm
  have hbarH : (H.subgroupOf (H ⊔ A)).map θ = ⨆ i, Lbar i := by
    have hsub : H.subgroupOf (H ⊔ A) = ⨆ i, (Lfam i).subgroupOf (H ⊔ A) := by
      apply Subgroup.map_injective (H ⊔ A).subtype_injective
      rw [Subgroup.map_subgroupOf_eq_of_le le_sup_left, Subgroup.map_iSup]
      calc H = ⨆ i, Lfam i := hH
        _ = _ := iSup_congr fun i => (Subgroup.map_subgroupOf_eq_of_le (hLleHA i)).symm
    rw [hsub, Subgroup.map_iSup]
    exact iSup_congr fun i => (hLbar i).symm
  have hHbar_ne : (H.subgroupOf (H ⊔ A)).map θ ≠ ⊥ := by
    have := hI.Hbar_ne
    rwa [hact H le_sup_left] at this
  have hrel : ∀ i j, (∃ a ∈ A, conjSub a (Lfam i) = Lfam j) →
      ∃ g, conjSub g (Lbar i) = Lbar j := by
    rintro i j ⟨a, ha, h⟩
    refine ⟨θ ⟨a, Subgroup.mem_sup_right ha⟩, ?_⟩
    rw [hLbar, hLbar]
    exact conjSub_map_subgroupOf θ _ h
  have hLbar_ne : ∀ i, Lbar i ≠ ⊥ := by
    intro j hj
    apply hHbar_ne
    rw [hbarH, eq_bot_iff]
    refine iSup_le fun i => ?_
    obtain ⟨g, hg⟩ := hrel i j (htrans i j)
    have : Lbar i = ⊥ := by
      apply (conjSub g).injective
      rw [hg, hj, (conjSub g).map_bot]
    exact this.le
  have hntL : ∀ i, Nontrivial ↥(Lbar i) := fun i =>
    (Subgroup.nontrivial_iff_ne_bot _).2 (hLbar_ne i)
  have hirrL : IsIrrAct (⨆ i, Lbar i) := by
    rw [← hbarH, hθ]
    exact isIrrAct_actW hAnH hHA' hI.inv_H hI.irr
  have hAbel : CFSG.IsElementaryAbelian 2 ↥Abar := by
    have := hI.Abar_elem
    rw [hact A le_sup_right, ← hAbar] at this
    exact this
  have hAbquad : ∀ a ∈ Abar, ∀ b ∈ Abar, ∀ w, b (a w - w) = a w - w := by
    have := hI.Abar_quad
    rw [hact A le_sup_right, ← hAbar] at this
    exact fun a ha b hb w => this a ha b hb w
  have hAboff : Nat.card (↥I ⧸ fixIn H I) ≤ Nat.card ↥Abar * Nat.card ↥(fixGL Abar) := by
    have := hI.Abar_off
    rw [hact A le_sup_right, ← hAbar] at this
    exact this
  have hpermL : ∀ b ∈ Abar, ∀ i, ∃ j, conjSub b (Lbar i) = Lbar j := by
    intro b hb i
    rw [hAbar] at hb
    obtain ⟨x, hx, rfl⟩ := hb
    obtain ⟨j, hj⟩ := hperm (x : V ≃ₗ[k] V) (Subgroup.mem_subgroupOf.1 hx) i
    refine ⟨j, ?_⟩
    rw [hLbar, hLbar]
    exact conjSub_map_subgroupOf θ x.2 hj
  have htransL : ∀ i j, ∃ b ∈ Abar, conjSub b (Lbar i) = Lbar j := by
    intro i j
    obtain ⟨a, ha, h⟩ := htrans i j
    refine ⟨θ ⟨a, Subgroup.mem_sup_right ha⟩, ?_, ?_⟩
    · rw [hAbar]
      exact ⟨⟨a, Subgroup.mem_sup_right ha⟩, ha, rfl⟩
    · rw [hLbar, hLbar]
      exact conjSub_map_subgroupOf θ _ h
  have hWnt : Nontrivial (↥I ⧸ fixIn H I) := by
    by_contra hcon
    have hsub : Subsingleton (↥I ⧸ fixIn H I) := not_nontrivial_iff_subsingleton.1 hcon
    apply hI.irr.1
    intro u hu l hl
    have h0 : (Submodule.Quotient.mk (⟨u, hu⟩ : ↥I) : ↥I ⧸ fixIn H I) = 0 :=
      Subsingleton.elim _ _
    exact ((Submodule.Quotient.mk_eq_zero _).1 h0) l hl
  have hWfin : Finite (↥I ⧸ fixIn H I) := inferInstance
  have := hAbel
  exact no_transitive_perfect_orbit_k (W := ↥I ⧸ fixIn H I) hs Lbar hcommL hperfL hntL hirrL
    Abar hAbquad hAboff hpermL htransL

end CFSG.QuasithinUnique.Setup.Layer
