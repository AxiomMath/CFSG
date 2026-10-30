module

public import CFSG.GroupTheory.InvolutionCentralizerOrder
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.GH312.DihedralPerm
public import CFSG.GH74.GLS.TwoThin.Count

public section

open Subgroup

namespace CFSG.EvenSporadicStandard.TwoHS.GH312

private lemma conj_mem_iff {G : Type*} [Group G] {H : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  rw [CFSG.conjugate, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    convert hy using 1
    group
  · intro hx
    refine ⟨g * x * g⁻¹, hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

private lemma conjugate_one {G : Type*} [Group G] (H : Subgroup G) :
    CFSG.conjugate H 1 = H := by
  rw [CFSG.conjugate]
  simp only [inv_one, map_one]
  exact Subgroup.map_id H

private lemma map_aut_eq_iff_map_inv_eq {G : Type*} [Group G] (H : Subgroup G)
    (e : MulAut G) :
    H.map e.toMonoidHom = H ↔ H.map (e⁻¹).toMonoidHom = H := by
  constructor
  · intro h
    have key := congrArg (Subgroup.map (e⁻¹).toMonoidHom) h
    rw [Subgroup.map_map] at key
    have hcomp : (e⁻¹).toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
      ext x; simp
    rw [hcomp, Subgroup.map_id] at key
    exact key.symm
  · intro h
    have key := congrArg (Subgroup.map e.toMonoidHom) h
    rw [Subgroup.map_map] at key
    have hcomp : e.toMonoidHom.comp (e⁻¹).toMonoidHom = MonoidHom.id G := by
      ext x; simp
    rw [hcomp, Subgroup.map_id] at key
    exact key.symm

private lemma mem_normalizer_iff_conjugate_eq {G : Type*} [Group G] {H : Subgroup G} {g : G} :
    g ∈ Subgroup.normalizer (H : Set G) ↔ CFSG.conjugate H g = H := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, CFSG.conjugate]
  have hsymm : MulAut.conj (g⁻¹) = (MulAut.conj g)⁻¹ := by
    ext x; simp [MulAut.conj_apply]
  rw [hsymm]
  exact map_aut_eq_iff_map_inv_eq H (MulAut.conj g)

private lemma conjugate_conjugate {G : Type*} [Group G] (H : Subgroup G) (g h : G) :
    CFSG.conjugate (CFSG.conjugate H g) h = CFSG.conjugate H (g * h) := by
  ext x
  rw [conj_mem_iff, conj_mem_iff, conj_mem_iff]
  constructor <;> intro hx
  · convert hx using 1
    group
  · convert hx using 1
    group

private lemma mem_centralizer_singleton_iff_conj {G : Type*} [Group G] {u x : G} :
    x ∈ Subgroup.centralizer ({u} : Set G) ↔ MulAut.conj u x = x := by
  rw [Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
  constructor
  · intro h
    calc u * x * u⁻¹ = (x * u) * u⁻¹ := by rw [h]
      _ = x := by group
  · intro h
    calc x * u = (u * x * u⁻¹) * u := by rw [h]
      _ = u * x := by group

private lemma mul_conj_mem_centralizer {G : Type*} [Group G] {u t : G} (hu : u * u = 1)
    (hc : MulAut.conj u⁻¹ t * t = t * MulAut.conj u⁻¹ t) :
    t * MulAut.conj u⁻¹ t ∈ Subgroup.centralizer ({u} : Set G) := by
  rw [mem_centralizer_singleton_iff_conj]
  have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hσ : MulAut.conj u⁻¹ = MulAut.conj u := by rw [hu']
  have hσ2 : MulAut.conj u⁻¹ * MulAut.conj u⁻¹ = 1 := by
    rw [← MonoidHom.map_mul]
    rw [show u⁻¹ * u⁻¹ = 1 by rw [hu', hu]]
    exact map_one _
  have happly : MulAut.conj u⁻¹ (MulAut.conj u⁻¹ t) = t := by
    change (MulAut.conj u⁻¹ * MulAut.conj u⁻¹) t = t
    rw [hσ2]
    rfl
  rw [map_mul]
  rw [← hσ, happly]
  exact hc

theorem nonempty_mulEquiv_alternatingGroup_five_of_two_components
    {X : Type*} [Group X] [Finite X] {u : X} (hu : u * u = 1) (hu1 : u ≠ 1)
    (e : ↥(Subgroup.centralizer ({u} : Set X)) ≃* DihedralGroup 4 × Equiv.Perm (Fin 5))
    {T₁ T₂ : Subgroup X} (hne : T₁ ≠ T₂) (hsimple : IsSimpleGroup T₁)
    (hnonab : ∃ a b : T₁, a * b ≠ b * a) (hcomm : T₁ ≤ Subgroup.centralizer (T₂ : Set X))
    (hperm : ∀ x : X, CFSG.conjugate T₁ x = T₁ ∨ CFSG.conjugate T₁ x = T₂)
    (hconj : ∃ g : X, CFSG.conjugate T₁ g = T₂) :
    Nonempty (↥T₁ ≃* alternatingGroup (Fin 5)) := by
  classical
  set C : Subgroup X := Subgroup.centralizer ({u} : Set X) with hC
  have huC : u ∈ C := by
    rw [hC]
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hu_inv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  let z : ↥C := e.symm (DihedralGroup.r 2, 1)
  have hz : z = ⟨u, huC⟩ := by
    have hzu_mem_center : (⟨u, huC⟩ : ↥C) ∈ Subgroup.center ↥C := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp y.2
    rcases (mem_center_iff_of_mulEquiv_dihedral_prod_perm e ⟨u, huC⟩).mp hzu_mem_center with
      h1 | h1
    · exact absurd (Subtype.ext_iff.mp h1) hu1
    · exact h1.symm
  let K : Subgroup ↥C := altSubgroup.comap e.toMonoidHom
  have hKcard : Nat.card ↥K = 60 := by
    obtain ⟨ee⟩ := nonempty_mulEquiv_alternatingGroup_comap_altSubgroup e
    change Nat.card ↥(altSubgroup.comap e.toMonoidHom) = 60
    rw [Nat.card_congr ee.toEquiv, nat_card_alternatingGroup]
    simp only [Nat.card_fin]
    norm_num
  have hK_ne : K ≠ ⊥ := by
    intro h
    have h1 : Nat.card ↥K = 1 := by rw [h]; exact Subgroup.card_bot
    rw [hKcard] at h1
    norm_num at h1
  have h4T1 : 4 ∣ Nat.card ↥T₁ :=
    CFSG.GH74.GLS.TwoThin.four_dvd_card_of_simple_nonabelian hnonab
  have hT1even : Even (Nat.card ↥T₁) := even_iff_two_dvd.mpr ((by norm_num : 2 ∣ 4).trans h4T1)
  obtain ⟨g₀, hg₀⟩ := hconj
  have hT2iso : ↥T₁ ≃* ↥T₂ := by
    rw [← hg₀]
    exact T₁.equivMapOfInjective (MulAut.conj g₀⁻¹).toMonoidHom
      (MulAut.conj g₀⁻¹).injective
  have hT2simple : IsSimpleGroup ↥T₂ := (MulEquiv.isSimpleGroup_congr hT2iso).mp hsimple
  have hnonabT2 : ∃ a b : ↥T₂, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    refine ⟨hT2iso a, hT2iso b, fun h => hab ?_⟩
    exact hT2iso.injective (by simpa [map_mul] using h)
  have hT2even : Even (Nat.card ↥T₂) := by
    rw [← Nat.card_congr hT2iso.toEquiv]; exact hT1even
  have hT2comm : T₂ ≤ Subgroup.centralizer (T₁ : Set X) :=
    Subgroup.le_centralizer_iff.mp hcomm
  have hZ2 : Subgroup.center ↥T₂ = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥T₂) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnonabT2
      have ha : a ∈ Subgroup.center ↥T₂ := by rw [h]; exact Subgroup.mem_top a
      exact hab (Subgroup.mem_center_iff.mp ha b).symm
  have hT12bot : T₁ ⊓ T₂ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hxcenter : (⟨x, hx.2⟩ : ↥T₂) ∈ Subgroup.center ↥T₂ := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp (hcomm hx.1) y.1 y.2
    rw [hZ2] at hxcenter
    exact Subtype.ext_iff.mp (Subgroup.mem_bot.mp hxcenter)
  by_cases hswap : CFSG.conjugate T₁ u = T₂
  ·
    have hctT2 : ∀ t : ↥T₁, MulAut.conj u⁻¹ (t : X) ∈ T₂ := by
      intro t
      have hmem : MulAut.conj u⁻¹ (t : X) ∈ CFSG.conjugate T₁ u :=
        Subgroup.mem_map.mpr ⟨(t : X), t.2, rfl⟩
      rwa [hswap] at hmem
    have hct_comm : ∀ t : ↥T₁,
        MulAut.conj u⁻¹ (t : X) * (t : X) = (t : X) * MulAut.conj u⁻¹ (t : X) := by
      intro t
      exact Subgroup.mem_centralizer_iff.mp (hcomm t.2) _ (hctT2 t)
    let phi : ↥T₁ →* ↥C :=
      { toFun := fun t => ⟨(t : X) * MulAut.conj u⁻¹ (t : X),
            mul_conj_mem_centralizer hu (hct_comm t)⟩
        map_one' := by
          apply Subtype.ext
          simp
        map_mul' := by
          intro s t
          apply Subtype.ext
          simp only [Subgroup.coe_mul]
          rw [map_mul]
          have hst : MulAut.conj u⁻¹ (s : X) * (t : X) = (t : X) * MulAut.conj u⁻¹ (s : X) :=
            Subgroup.mem_centralizer_iff.mp (hcomm t.2) _ (hctT2 s)
          calc (s : X) * (t : X) * (MulAut.conj u⁻¹ (s : X) * MulAut.conj u⁻¹ (t : X))
              = (s : X) * ((t : X) * MulAut.conj u⁻¹ (s : X)) * MulAut.conj u⁻¹ (t : X) := by
                group
            _ = (s : X) * (MulAut.conj u⁻¹ (s : X) * (t : X)) * MulAut.conj u⁻¹ (t : X) := by
                rw [← hst]
            _ = ((s : X) * MulAut.conj u⁻¹ (s : X)) * ((t : X) * MulAut.conj u⁻¹ (t : X)) := by
                group }
    have hphi_ker : ∀ x : ↥T₁, phi x = 1 → x = 1 := by
      intro x hx
      have hx' : (x : X) * MulAut.conj u⁻¹ (x : X) = 1 := by
        have h := congrArg Subtype.val hx
        dsimp only [phi] at h
        simpa using h
      have hσ : MulAut.conj u⁻¹ (x : X) = (x : X)⁻¹ := by
        calc MulAut.conj u⁻¹ (x : X)
            = (x : X)⁻¹ * ((x : X) * MulAut.conj u⁻¹ (x : X)) := by group
          _ = (x : X)⁻¹ := by rw [hx', mul_one]
      have hmem : MulAut.conj u⁻¹ (x : X) ∈ T₁ ⊓ T₂ :=
        ⟨hσ ▸ T₁.inv_mem x.2, hctT2 x⟩
      rw [hT12bot] at hmem
      have h1 : MulAut.conj u⁻¹ (x : X) = 1 := Subgroup.mem_bot.mp hmem
      have h2 : (x : X)⁻¹ = 1 := by rw [← hσ, h1]
      exact Subtype.ext (inv_eq_one.mp h2)
    have hphi_inj : Function.Injective phi := by
      intro s t h
      have h1 : s * t⁻¹ = 1 := hphi_ker (s * t⁻¹) (by rw [map_mul, map_inv, h, mul_inv_cancel])
      exact mul_inv_eq_one.mp h1
    let S : Subgroup ↥C := phi.range
    have hSiso : ↥T₁ ≃* ↥S := MonoidHom.ofInjective hphi_inj
    have hSsimple : IsSimpleGroup ↥S := (MulEquiv.isSimpleGroup_congr hSiso).mp hsimple
    have hSnonab : ∃ a b : ↥S, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := hnonab
      refine ⟨hSiso a, hSiso b, fun h => hab ?_⟩
      exact hSiso.injective (by simpa [map_mul] using h)
    have hS_eq : S = K := eq_comap_altSubgroup_of_isSimpleGroup e S hSsimple hSnonab
    obtain ⟨ee⟩ := nonempty_mulEquiv_alternatingGroup_comap_altSubgroup e
    exact ⟨hSiso.trans ((MulEquiv.subgroupCongr hS_eq).trans ee)⟩
  ·
    have hT1norm : CFSG.conjugate T₁ u = T₁ := (hperm u).resolve_right hswap
    have hT2norm : CFSG.conjugate T₂ u = T₂ := by
      have hcg : CFSG.conjugate T₂ u = CFSG.conjugate T₁ (g₀ * u) := by
        rw [← hg₀, conjugate_conjugate]
      rw [hcg]
      rcases hperm (g₀ * u) with h | h
      · exfalso
        have h2 : CFSG.conjugate T₂ u = T₁ := by rw [hcg, h]
        have h3 : CFSG.conjugate T₁ u = T₂ := by
          calc CFSG.conjugate T₁ u = CFSG.conjugate (CFSG.conjugate T₂ u) u := by rw [← h2]
            _ = CFSG.conjugate T₂ (u * u) := by rw [conjugate_conjugate]
            _ = T₂ := by rw [hu]; exact conjugate_one T₂
        exact hne (hT1norm.symm.trans h3)
      · exact h
    by_cases hT1C : T₁ ≤ C
    ·
      let S : Subgroup ↥C := T₁.subgroupOf C
      have hSiso : ↥S ≃* ↥T₁ := Subgroup.subgroupOfEquivOfLe hT1C
      have hSsimple : IsSimpleGroup ↥S := (MulEquiv.isSimpleGroup_congr hSiso).mpr hsimple
      have hSnonab : ∃ a b : ↥S, a * b ≠ b * a := by
        obtain ⟨a, b, hab⟩ := hnonab
        refine ⟨hSiso.symm a, hSiso.symm b, fun h => hab ?_⟩
        simpa [map_mul] using congrArg hSiso h
      have hS_eq : S = K := eq_comap_altSubgroup_of_isSimpleGroup e S hSsimple hSnonab
      obtain ⟨ee⟩ := nonempty_mulEquiv_alternatingGroup_comap_altSubgroup e
      exact ⟨hSiso.symm.trans ((MulEquiv.subgroupCongr hS_eq).trans ee)⟩
    · by_cases hT2C : T₂ ≤ C
      ·
        let S : Subgroup ↥C := T₂.subgroupOf C
        have hSiso : ↥S ≃* ↥T₂ := Subgroup.subgroupOfEquivOfLe hT2C
        have hSsimple : IsSimpleGroup ↥S := (MulEquiv.isSimpleGroup_congr hSiso).mpr hT2simple
        have hSnonab : ∃ a b : ↥S, a * b ≠ b * a := by
          obtain ⟨a, b, hab⟩ := hnonabT2
          refine ⟨hSiso.symm a, hSiso.symm b, fun h => hab ?_⟩
          simpa [map_mul] using congrArg hSiso h
        have hS_eq : S = K := eq_comap_altSubgroup_of_isSimpleGroup e S hSsimple hSnonab
        obtain ⟨ee⟩ := nonempty_mulEquiv_alternatingGroup_comap_altSubgroup e
        exact ⟨hT2iso.trans (hSiso.symm.trans ((MulEquiv.subgroupCongr hS_eq).trans ee))⟩
      ·
        let A : Subgroup ↥C := T₁.subgroupOf C
        let A' : Subgroup ↥C := T₂.subgroupOf C
        let M : Subgroup ↥C := A ⊔ A'
        have hA_even : Even (Nat.card ↥A) := by
          have h1 : Nat.card ↥A = Nat.card ↥(T₁ ⊓ C) := by
            change Nat.card ↥(T₁.subgroupOf C) = Nat.card ↥(T₁ ⊓ C)
            rw [← Subgroup.card_map_of_injective (f := C.subtype)
                  (K := T₁.subgroupOf C) C.subtype_injective,
              Subgroup.subgroupOf_map_subtype]
          rw [h1]
          exact CFSG.GroupTheory.even_card_inf_centralizer_of_mem_normalizer hu
            ((mem_normalizer_iff_conjugate_eq (H := T₁) (g := u)).mpr hT1norm) hT1even
        have hA'_even : Even (Nat.card ↥A') := by
          have h1 : Nat.card ↥A' = Nat.card ↥(T₂ ⊓ C) := by
            change Nat.card ↥(T₂.subgroupOf C) = Nat.card ↥(T₂ ⊓ C)
            rw [← Subgroup.card_map_of_injective (f := C.subtype)
                  (K := T₂.subgroupOf C) C.subtype_injective,
              Subgroup.subgroupOf_map_subtype]
          rw [h1]
          exact CFSG.GroupTheory.even_card_inf_centralizer_of_mem_normalizer hu
            ((mem_normalizer_iff_conjugate_eq (H := T₂) (g := u)).mpr hT2norm) hT2even
        have hA_ne : A ≠ ⊥ := by
          intro h
          have h1 : Nat.card ↥A = 1 := by rw [h]; exact Subgroup.card_bot
          rw [h1] at hA_even
          norm_num at hA_even
        have hA'_ne : A' ≠ ⊥ := by
          intro h
          have h1 : Nat.card ↥A' = 1 := by rw [h]; exact Subgroup.card_bot
          rw [h1] at hA'_even
          norm_num at hA'_even
        have hAcomm : ∀ a ∈ A, ∀ b ∈ A', a * b = b * a := by
          intro a ha b hb
          apply Subtype.ext
          have haT1 : (a : X) ∈ T₁ :=
            Subgroup.mem_subgroupOf.mp (show a ∈ T₁.subgroupOf C from ha)
          have hbT2 : (b : X) ∈ T₂ :=
            Subgroup.mem_subgroupOf.mp (show b ∈ T₂.subgroupOf C from hb)
          exact (Subgroup.mem_centralizer_iff.mp (hcomm haT1) (b : X) hbT2).symm
        have hdisj : A ⊓ A' = ⊥ := by
          rw [eq_bot_iff]
          intro x hx
          rw [Subgroup.mem_bot]
          have hxT1 : (x : X) ∈ T₁ :=
            Subgroup.mem_subgroupOf.mp (show x ∈ T₁.subgroupOf C from hx.1)
          have hxT2 : (x : X) ∈ T₂ :=
            Subgroup.mem_subgroupOf.mp (show x ∈ T₂.subgroupOf C from hx.2)
          have hmem : (x : X) ∈ T₁ ⊓ T₂ := ⟨hxT1, hxT2⟩
          rw [hT12bot] at hmem
          exact Subtype.ext (Subgroup.mem_bot.mp hmem)
        by_cases hsplit : ∃ c : ↥C, CFSG.conjugate T₁ (c : X) = T₂
        ·
          exfalso
          obtain ⟨c, hc_swap⟩ := hsplit
          have hc_swapT2 : CFSG.conjugate T₂ c = T₁ := by
            have h1 : CFSG.conjugate T₂ c = CFSG.conjugate T₁ (c * c) := by
              rw [← hc_swap, conjugate_conjugate]
            rw [h1]
            rcases hperm (c * c) with h | h
            · exact h
            · exfalso
              have h2 : CFSG.conjugate T₂ c = T₂ := by rw [h1, h]
              have h3 : CFSG.conjugate T₂ c⁻¹ = T₁ := by
                have hh : CFSG.conjugate (CFSG.conjugate T₁ c) c⁻¹ = T₁ := by
                  rw [conjugate_conjugate, mul_inv_cancel, conjugate_one]
                rwa [hc_swap] at hh
              have h4 : CFSG.conjugate T₂ c⁻¹ = T₂ := by
                have hh : CFSG.conjugate (CFSG.conjugate T₂ c) c⁻¹ = T₂ := by
                  rw [conjugate_conjugate, mul_inv_cancel, conjugate_one]
                rwa [h2] at hh
              exact hne (h3.symm.trans h4)
          have hc_swap_inv : CFSG.conjugate T₁ c⁻¹ = T₂ := by
            have hh : CFSG.conjugate (CFSG.conjugate T₂ c) c⁻¹ = T₂ := by
              rw [conjugate_conjugate, mul_inv_cancel, conjugate_one]
            rwa [hc_swapT2] at hh
          have hpermT2 : ∀ y : X, CFSG.conjugate T₂ y = T₁ ∨ CFSG.conjugate T₂ y = T₂ := by
            intro y
            have hcy : CFSG.conjugate T₂ y = CFSG.conjugate T₁ (g₀ * y) := by
              rw [← hg₀, conjugate_conjugate]
            rw [hcy]
            exact hperm (g₀ * y)
          have hconjA_elem : ∀ g : ↥C, ∀ a ∈ A,
              (MulAut.conj g) a ∈ A ∨ (MulAut.conj g) a ∈ A' := by
            intro g a ha
            have haT1 : (a : X) ∈ T₁ :=
              Subgroup.mem_subgroupOf.mp (show a ∈ T₁.subgroupOf C from ha)
            have hx : ((MulAut.conj g) a : X) = (g : X) * (a : X) * (g : X)⁻¹ := by
              simp [MulAut.conj_apply]
            have hmem : ((MulAut.conj g) a : X) ∈ CFSG.conjugate T₁ ((g : X)⁻¹) := by
              rw [conj_mem_iff, hx]
              convert haT1 using 1
              group
            rcases hperm ((g : X)⁻¹) with h | h <;> rw [h] at hmem
            · exact Or.inl (Subgroup.mem_subgroupOf.mpr hmem)
            · exact Or.inr (Subgroup.mem_subgroupOf.mpr hmem)
          have hconjA'_elem : ∀ g : ↥C, ∀ b ∈ A',
              (MulAut.conj g) b ∈ A ∨ (MulAut.conj g) b ∈ A' := by
            intro g b hb
            have hbT2 : (b : X) ∈ T₂ :=
              Subgroup.mem_subgroupOf.mp (show b ∈ T₂.subgroupOf C from hb)
            have hx : ((MulAut.conj g) b : X) = (g : X) * (b : X) * (g : X)⁻¹ := by
              simp [MulAut.conj_apply]
            have hmem : ((MulAut.conj g) b : X) ∈ CFSG.conjugate T₂ ((g : X)⁻¹) := by
              rw [conj_mem_iff, hx]
              convert hbT2 using 1
              group
            rcases hpermT2 ((g : X)⁻¹) with h | h <;> rw [h] at hmem
            · exact Or.inl (Subgroup.mem_subgroupOf.mpr hmem)
            · exact Or.inr (Subgroup.mem_subgroupOf.mpr hmem)
          have hM_normal : M.Normal := by
            rw [Subgroup.normal_iff_map_conj_eq]
            intro g
            apply Subgroup.eq_of_le_of_card_ge
            · rw [Subgroup.map_sup]
              apply sup_le
              · rintro _ ⟨a, ha, rfl⟩
                rcases hconjA_elem g a ha with h | h
                · exact Subgroup.mem_sup_left h
                · exact Subgroup.mem_sup_right h
              · rintro _ ⟨b, hb, rfl⟩
                rcases hconjA'_elem g b hb with h | h
                · exact Subgroup.mem_sup_left h
                · exact Subgroup.mem_sup_right h
            · exact (Subgroup.card_map_of_injective
                (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective).ge
          have hmapA : A.map (MulAut.conj c) = A' := by
            ext x
            constructor
            · rintro ⟨a, ha, rfl⟩
              have haT1 : (a : X) ∈ T₁ :=
                Subgroup.mem_subgroupOf.mp (show a ∈ T₁.subgroupOf C from ha)
              have hx : ((MulAut.conj c) a : X) = (c : X) * (a : X) * (c : X)⁻¹ := by
                simp [MulAut.conj_apply]
              have hmem : ((MulAut.conj c) a : X) ∈ CFSG.conjugate T₁ c⁻¹ := by
                rw [conj_mem_iff, hx]
                convert haT1 using 1
                group
              rw [hc_swap_inv] at hmem
              exact Subgroup.mem_subgroupOf.mpr hmem
            · intro hx
              have hxT2 : (x : X) ∈ T₂ :=
                Subgroup.mem_subgroupOf.mp (show x ∈ T₂.subgroupOf C from hx)
              have hxT1 : (x : X) ∈ CFSG.conjugate T₁ c⁻¹ := by
                rw [hc_swap_inv]; exact hxT2
              have hin : (c : X)⁻¹ * (x : X) * (c : X) ∈ T₁ := by
                simpa using (conj_mem_iff.mp hxT1)
              have hinC : (c : X)⁻¹ * (x : X) * (c : X) ∈ C :=
                C.mul_mem (C.mul_mem (C.inv_mem c.2) x.2) c.2
              refine ⟨⟨(c : X)⁻¹ * (x : X) * (c : X), hinC⟩, ?_, ?_⟩
              · exact (Subgroup.mem_subgroupOf (H := T₁) (K := C)).mpr hin
              · apply Subtype.ext
                simp [MulAut.conj_apply]
                group
          have hmapA'_le : A'.map (MulAut.conj c) ≤ A := by
            rintro _ ⟨b, hb, rfl⟩
            have hbT2 : (b : X) ∈ T₂ :=
              Subgroup.mem_subgroupOf.mp (show b ∈ T₂.subgroupOf C from hb)
            have hx : ((MulAut.conj c) b : X) = (c : X) * (b : X) * (c : X)⁻¹ := by
              simp [MulAut.conj_apply]
            have hc_swapT2_inv : CFSG.conjugate T₂ c⁻¹ = T₁ := by
              rw [← hc_swap, conjugate_conjugate, mul_inv_cancel, conjugate_one]
            have hmem : ((MulAut.conj c) b : X) ∈ CFSG.conjugate T₂ c⁻¹ := by
              rw [conj_mem_iff, hx]
              convert hbT2 using 1
              group
            rw [hc_swapT2_inv] at hmem
            exact Subgroup.mem_subgroupOf.mpr hmem
          have hA_card_eq : Nat.card ↥A' = Nat.card ↥A := by
            rw [← hmapA, Subgroup.card_map_of_injective (MulAut.conj c).injective]
          have hK_simple : IsSimpleGroup ↥K := by
            obtain ⟨ee⟩ := nonempty_mulEquiv_alternatingGroup_comap_altSubgroup e
            exact (MulEquiv.isSimpleGroup_congr ee).mpr alternatingGroup.isSimpleGroup_five
          have hK_normal : K.Normal := inferInstance
          have hKnonab : ∃ a b : ↥K, a * b ≠ b * a := by
            obtain ⟨ee⟩ := nonempty_mulEquiv_alternatingGroup_comap_altSubgroup e
            have h5 : ∃ a b : alternatingGroup (Fin 5), a * b ≠ b * a := by
              decide +kernel
            obtain ⟨a, b, hab⟩ := h5
            refine ⟨ee.symm a, ee.symm b, fun h => hab ?_⟩
            have h' := congrArg ee h
            simpa only [map_mul, MulEquiv.apply_symm_apply] using h'
          let gmul : (↥A) × (↥A') → ↥C := fun x => (x.1 : ↥C) * (x.2 : ↥C)
          have gmul_mul : ∀ x y : (↥A) × (↥A'), gmul (x * y) = gmul x * gmul y := by
            rintro ⟨a1, b1⟩ ⟨a2, b2⟩
            apply Subtype.ext
            dsimp only [gmul]
            simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
            have hX : (a2 : X) * (b1 : X) = (b1 : X) * (a2 : X) :=
              congrArg Subtype.val (hAcomm a2 a2.2 b1 b1.2)
            calc (a1 : X) * (a2 : X) * ((b1 : X) * (b2 : X))
                = (a1 : X) * ((a2 : X) * (b1 : X)) * (b2 : X) := by group
              _ = (a1 : X) * ((b1 : X) * (a2 : X)) * (b2 : X) := by rw [hX]
              _ = (a1 : X) * (b1 : X) * ((a2 : X) * (b2 : X)) := by group
          let f : (↥A) × (↥A') →* ↥C :=
            { toFun := gmul
              map_one' := by simp [gmul]
              map_mul' := gmul_mul }
          have hf_inj : Function.Injective f := by
            rintro ⟨a1, b1⟩ ⟨a2, b2⟩ h
            have h' : (a1 : X) * (b1 : X) = (a2 : X) * (b2 : X) := congrArg Subtype.val h
            have hA1 : (a1 : X) ∈ T₁ :=
              (Subgroup.mem_subgroupOf (H := T₁) (K := C)).mp
                (show (a1 : ↥C) ∈ T₁.subgroupOf C from a1.2)
            have hA2 : (a2 : X) ∈ T₁ :=
              (Subgroup.mem_subgroupOf (H := T₁) (K := C)).mp
                (show (a2 : ↥C) ∈ T₁.subgroupOf C from a2.2)
            have hB1 : (b1 : X) ∈ T₂ :=
              (Subgroup.mem_subgroupOf (H := T₂) (K := C)).mp
                (show (b1 : ↥C) ∈ T₂.subgroupOf C from b1.2)
            have hB2 : (b2 : X) ∈ T₂ :=
              (Subgroup.mem_subgroupOf (H := T₂) (K := C)).mp
                (show (b2 : ↥C) ∈ T₂.subgroupOf C from b2.2)
            have key : (a2 : X)⁻¹ * (a1 : X) = (b2 : X) * (b1 : X)⁻¹ := by
              calc (a2 : X)⁻¹ * (a1 : X)
                  = (a2 : X)⁻¹ * ((a1 : X) * (b1 : X)) * (b1 : X)⁻¹ := by group
                _ = (a2 : X)⁻¹ * ((a2 : X) * (b2 : X)) * (b1 : X)⁻¹ := by rw [h']
                _ = (b2 : X) * (b1 : X)⁻¹ := by group
            have hin : (a2 : X)⁻¹ * (a1 : X) ∈ T₁ ⊓ T₂ :=
              ⟨T₁.mul_mem (T₁.inv_mem hA2) hA1,
                by rw [key]; exact T₂.mul_mem hB2 (T₂.inv_mem hB1)⟩
            rw [hT12bot] at hin
            have h1 : (a1 : ↥C) = (a2 : ↥C) := by
              have hh : (a2 : X)⁻¹ * (a1 : X) = 1 := Subgroup.mem_bot.mp hin
              apply Subtype.ext
              exact (inv_mul_eq_one.mp hh).symm
            have h2 : (b1 : ↥C) = (b2 : ↥C) := by
              have hh : (a2 : X)⁻¹ * (a1 : X) = 1 := Subgroup.mem_bot.mp hin
              rw [key] at hh
              apply Subtype.ext
              exact (mul_inv_eq_one.mp hh).symm
            exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
          have hf_range : f.range = M := by
            apply le_antisymm
            · rintro _ ⟨x, rfl⟩
              exact Subgroup.mul_mem_sup (show ((x.1 : ↥C)) ∈ A from x.1.2)
                (show ((x.2 : ↥C)) ∈ A' from x.2.2)
            · apply sup_le
              · intro a ha
                refine ⟨(⟨a, ha⟩, 1), ?_⟩
                apply Subtype.ext
                dsimp only [f, gmul]
                simp
              · intro b hb
                refine ⟨(1, ⟨b, hb⟩), ?_⟩
                apply Subtype.ext
                dsimp only [f, gmul]
                simp
          let iso : (↥A) × (↥A') ≃* ↥M :=
            (MonoidHom.ofInjective hf_inj).trans (MulEquiv.subgroupCongr hf_range)
          have iso_coe : ∀ x : (↥A) × (↥A'), ((iso x : ↥M) : ↥C) = f x := by
            intro x; rfl
          have hKnotle : ¬ K ≤ M := by
            intro hKM
            let inc : ↥K →* ↥M := Subgroup.inclusion hKM
            let projA : ↥M →* ↥A := (MonoidHom.fst ↥A ↥A').comp iso.symm.toMonoidHom
            have hmemA' : ∀ k : ↥K, projA (inc k) = 1 → ((inc k : ↥M) : ↥C) ∈ A' := by
              intro k hk
              have h1 : (iso.symm (inc k)).1 = 1 := by simpa [projA] using hk
              have hfiso : ((iso (iso.symm (inc k)) : ↥M) : ↥C) = f (iso.symm (inc k)) :=
                iso_coe _
              rw [iso.apply_symm_apply] at hfiso
              rw [hfiso]
              change ((iso.symm (inc k)).1 : ↥C) * ((iso.symm (inc k)).2 : ↥C) ∈ A'
              rw [h1]
              simpa using (iso.symm (inc k)).2.2
            by_cases htriv : ∀ k : ↥K, projA (inc k) = 1
            · exfalso
              have hKleA' : K ≤ A' := by
                intro k hk
                exact hmemA' ⟨k, hk⟩ (htriv ⟨k, hk⟩)
              have hKleA : K ≤ A := by
                have hKmap : K.map (MulAut.conj c) = K :=
                  (Subgroup.normal_iff_map_conj_eq.mp hK_normal) c
                calc K = K.map (MulAut.conj c) := hKmap.symm
                  _ ≤ A'.map (MulAut.conj c) := Subgroup.map_mono hKleA'
                  _ ≤ A := hmapA'_le
              exact hK_ne (le_bot_iff.mp (hdisj ▸ le_inf hKleA hKleA'))
            · exfalso
              push Not at htriv
              obtain ⟨k0, hk0⟩ := htriv
              have hker_ne_top : (projA.comp inc).ker ≠ ⊤ := by
                intro htop
                have hk0' : k0 ∈ (projA.comp inc).ker := by rw [htop]; exact Subgroup.mem_top _
                exact hk0 (by simpa [MonoidHom.mem_ker] using hk0')
              have hker_bot : (projA.comp inc).ker = ⊥ := by
                rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (projA.comp inc).ker with h | h
                · exact h
                · exact absurd h hker_ne_top
              have hinj : Function.Injective (projA.comp inc) := by
                rw [← MonoidHom.ker_eq_bot_iff]; exact hker_bot
              let S : Subgroup ↥C := ((projA.comp inc).range).map A.subtype
              have hS_le_A : S ≤ A := Subgroup.map_subtype_le _
              have hSiso : ↥K ≃* ↥S :=
                (MonoidHom.ofInjective hinj).trans
                  (Subgroup.equivMapOfInjective (projA.comp inc).range A.subtype A.subtype_injective)
              have hSsimple : IsSimpleGroup ↥S := (MulEquiv.isSimpleGroup_congr hSiso).mp hK_simple
              have hSnonab : ∃ a b : ↥S, a * b ≠ b * a := by
                obtain ⟨a, b, hab⟩ := hKnonab
                refine ⟨hSiso a, hSiso b, fun h => hab ?_⟩
                exact hSiso.injective (by simpa [map_mul] using h)
              have hS_eq : S = K := eq_comap_altSubgroup_of_isSimpleGroup e S hSsimple hSnonab
              have hAle : Nat.card ↥K ≤ Nat.card ↥A := by
                have hdvd := Subgroup.card_dvd_of_le hS_le_A
                rw [hS_eq] at hdvd
                exact Nat.le_of_dvd Nat.card_pos hdvd
              have hMcard : Nat.card ↥M = Nat.card ↥A * Nat.card ↥A' := by
                rw [← Nat.card_congr iso.toEquiv, Nat.card_prod]
              have hCcard : Nat.card ↥C = 960 := by
                rw [Nat.card_congr e.toEquiv, Nat.card_prod, DihedralGroup.nat_card,
                  Nat.card_perm]
                have : Nat.card (Fin 5) = 5 := by simp
                rw [this]
                norm_num
              have hle3600 : 3600 ≤ Nat.card ↥C := by
                calc 3600 = 60 * 60 := by norm_num
                  _ ≤ Nat.card ↥A * Nat.card ↥A :=
                      Nat.mul_le_mul (by rw [← hKcard]; exact hAle)
                        (by rw [← hKcard]; exact hAle)
                  _ = Nat.card ↥A * Nat.card ↥A' := by rw [hA_card_eq]
                  _ = Nat.card ↥M := hMcard.symm
                  _ ≤ Nat.card ↥C := Subgroup.card_le_card_group M
              rw [hCcard] at hle3600
              norm_num at hle3600
          have hM_ne : M ≠ ⊥ := by
            intro hM
            have hAle : A ≤ ⊥ := by rw [← hM]; exact le_sup_left
            exact hA_ne (le_bot_iff.mp hAle)
          rcases mem_or_comap_altSubgroup_le_of_normal e M hM_normal hM_ne with hzM | hKM
          ·
            have hzrange : z ∈ f.range := by rw [hf_range]; exact hzM
            obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hzrange
            have hz_eq : (x.1 : ↥C) * (x.2 : ↥C) = z := hx
            have hzX : (x.1 : X) * (x.2 : X) = u := by
              have hh := congrArg Subtype.val hz_eq
              rw [hz] at hh
              simpa using hh
            have hx1_ne : (x.1 : ↥C) ≠ 1 := by
              intro hx1
              have hzA' : z ∈ A' := by
                rw [← hz_eq, hx1, one_mul]
                exact x.2.2
              have huT2 : u ∈ T₂ := by
                have hthis : (⟨u, huC⟩ : ↥C) ∈ A' := hz ▸ hzA'
                exact Subgroup.mem_subgroupOf.mp
                  (show (⟨u, huC⟩ : ↥C) ∈ T₂.subgroupOf C from hthis)
              exact hT1C (fun t ht => Subgroup.mem_centralizer_singleton_iff.mpr
                ((Subgroup.mem_centralizer_iff.mp (hcomm ht) u huT2).symm))
            have hx2_ne : (x.2 : ↥C) ≠ 1 := by
              intro hx2
              have hzA : z ∈ A := by
                rw [← hz_eq, hx2, mul_one]
                exact x.1.2
              have huT1 : u ∈ T₁ := by
                have hthis : (⟨u, huC⟩ : ↥C) ∈ A := hz ▸ hzA
                exact Subgroup.mem_subgroupOf.mp
                  (show (⟨u, huC⟩ : ↥C) ∈ T₁.subgroupOf C from hthis)
              exact hT2C (fun t ht => Subgroup.mem_centralizer_singleton_iff.mpr
                ((Subgroup.mem_centralizer_iff.mp (hT2comm ht) u huT1).symm))
            have hMKbot : M ⊓ K = ⊥ := by
              rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((M ⊓ K).subgroupOf K) with h | h
              · have hd := Subgroup.subgroupOf_eq_bot.mp h
                rw [disjoint_iff] at hd
                rwa [inf_assoc, inf_idem] at hd
              · exact absurd ((Subgroup.subgroupOf_eq_top.mp h).trans inf_le_left) hKnotle
            have hMleD : M ≤ dihedralSubgroup.comap e.toMonoidHom := by
              have hcommbot : ⁅M, K⁆ = ⊥ := by
                apply le_bot_iff.mp
                calc ⁅M, K⁆ ≤ M ⊓ K := le_inf (Subgroup.commutator_le_left M K)
                        (Subgroup.commutator_le_right M K)
                  _ = ⊥ := hMKbot
              have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommbot
              rwa [centralizer_comap_altSubgroup e] at hle
            have hMcard : Nat.card ↥M = Nat.card ↥A * Nat.card ↥A' := by
              rw [← Nat.card_congr iso.toEquiv, Nat.card_prod]
            have hAdvd8 : Nat.card ↥A * Nat.card ↥A' ∣ 8 := by
              rw [← hMcard, ← card_comap_dihedralSubgroup e]
              exact Subgroup.card_dvd_of_le hMleD
            have hAeq2 : Nat.card ↥A = 2 := by
              have hsq : Nat.card ↥A * Nat.card ↥A ∣ 8 := by rwa [hA_card_eq] at hAdvd8
              have hle : Nat.card ↥A * Nat.card ↥A ≤ 8 := Nat.le_of_dvd (by norm_num) hsq
              have hAle2 : Nat.card ↥A ≤ 2 := by nlinarith [Nat.card_pos (α := ↥A)]
              have hAge2 : 2 ≤ Nat.card ↥A :=
                Nat.le_of_dvd Nat.card_pos (even_iff_two_dvd.mp hA_even)
              exact le_antisymm hAle2 hAge2
            have hordA : orderOf x.1 = 2 := by
              have hdvd : orderOf x.1 ∣ 2 := by
                simpa [hAeq2] using Subgroup.orderOf_dvd_natCard A x.1.2
              have hne : orderOf x.1 ≠ 1 := fun h => hx1_ne (by
                have hh := congrArg Subtype.val (orderOf_eq_one_iff.mp h)
                simpa using hh)
              exact (Nat.dvd_prime Nat.prime_two).mp hdvd |>.resolve_left hne
            have hpowA : x.1 ^ 2 = 1 := by
              have h := pow_orderOf_eq_one x.1
              rwa [hordA] at h
            have hpowC : (x.1 : ↥C) ^ 2 = 1 := by
              have hh := congrArg Subtype.val hpowA
              simpa only [Subgroup.coe_pow, Subgroup.coe_one] using hh
            have hordC : orderOf (x.1 : ↥C) = 2 := by
              haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
              exact orderOf_eq_prime hpowC hx1_ne
            have hAzp : A = Subgroup.zpowers (x.1 : ↥C) := by
              symm
              apply Subgroup.eq_of_le_of_card_ge
              · exact Subgroup.zpowers_le.mpr x.1.2
              · rw [Nat.card_zpowers, hordC, ← hAeq2]
            have hcent : T₁ ⊓ Subgroup.centralizer ({(x.1 : X)} : Set X) =
                Subgroup.zpowers (x.1 : X) := by
              apply le_antisymm
              · intro t ht
                have htT1 : t ∈ T₁ := ht.1
                have htcomm : t * (x.1 : X) = (x.1 : X) * t :=
                  Subgroup.mem_centralizer_singleton_iff.mp ht.2
                have ht2 : t * (x.2 : X) = (x.2 : X) * t :=
                  (Subgroup.mem_centralizer_iff.mp (hcomm htT1) (x.2 : X) x.2.2).symm
                have htC : t ∈ C := by
                  rw [hC, Subgroup.mem_centralizer_singleton_iff]
                  rw [← hzX]
                  calc t * ((x.1 : X) * (x.2 : X))
                      = (t * (x.1 : X)) * (x.2 : X) := by group
                    _ = ((x.1 : X) * t) * (x.2 : X) := by rw [htcomm]
                    _ = (x.1 : X) * (t * (x.2 : X)) := by group
                    _ = (x.1 : X) * ((x.2 : X) * t) := by rw [ht2]
                    _ = ((x.1 : X) * (x.2 : X)) * t := by group
                have htA : (⟨t, htC⟩ : ↥C) ∈ A :=
                  (Subgroup.mem_subgroupOf (H := T₁) (K := C)).mpr htT1
                rw [hAzp] at htA
                obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp htA
                rw [Subgroup.mem_zpowers_iff]
                refine ⟨k, ?_⟩
                have hh := congrArg Subtype.val hk
                simpa using hh
              · rw [Subgroup.zpowers_le]
                refine ⟨(Subgroup.mem_subgroupOf (H := T₁) (K := C)).mp
                    (show (x.1 : ↥C) ∈ T₁.subgroupOf C from x.1.2), ?_⟩
                exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
            have hx1T1 : (x.1 : X) ∈ T₁ :=
              (Subgroup.mem_subgroupOf (H := T₁) (K := C)).mp
                (show (x.1 : ↥C) ∈ T₁.subgroupOf C from x.1.2)
            have hordX : orderOf (x.1 : X) = 2 := by
              have hpow : (x.1 : X) ^ 2 = 1 := by
                have hh := congrArg Subtype.val hpowC
                simpa only [Subgroup.coe_pow, Subgroup.coe_one] using hh
              have hne : (x.1 : X) ≠ 1 := fun h => hx1_ne (Subtype.ext h)
              haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
              exact orderOf_eq_prime hpow hne
            exact (CFSG.GroupTheory.not_four_dvd_card_of_inf_centralizer_eq_zpowers
              hx1T1 hordX hcent) h4T1
          · exact absurd hKM hKnotle
        ·
          have hno : ∀ c : ↥C, CFSG.conjugate T₁ (c : X) = T₁ := by
            intro c
            rcases hperm (c : X) with h | h
            · exact h
            · exact absurd ⟨c, h⟩ hsplit
          have hnormT1 : C ≤ Subgroup.normalizer (T₁ : Set X) := by
            intro c hc
            rw [mem_normalizer_iff_conjugate_eq]
            exact hno ⟨c, hc⟩
          have hnormT2 : C ≤ Subgroup.normalizer (T₂ : Set X) := by
            intro c hc
            rw [mem_normalizer_iff_conjugate_eq]
            have hcg : CFSG.conjugate T₂ c = CFSG.conjugate T₁ (g₀ * c) := by
              rw [← hg₀, conjugate_conjugate]
            rw [hcg]
            rcases hperm (g₀ * c) with h | h
            · exfalso
              have h2 : CFSG.conjugate T₂ c = T₁ := by rw [hcg, h]
              have h3 : CFSG.conjugate T₁ c⁻¹ = T₂ := by
                calc CFSG.conjugate T₁ c⁻¹ = CFSG.conjugate (CFSG.conjugate T₂ c) c⁻¹ := by
                      rw [← h2]
                  _ = CFSG.conjugate T₂ (c * c⁻¹) := by rw [conjugate_conjugate]
                  _ = T₂ := by rw [mul_inv_cancel]; exact conjugate_one T₂
              have h4 : CFSG.conjugate T₁ c⁻¹ = T₁ := by
                have := hno (⟨c⁻¹, C.inv_mem hc⟩ : ↥C)
                simpa using this
              exact hne (h4.symm.trans h3)
            · exact h
          have hA_normal : A.Normal := by
            rw [Subgroup.normal_subgroupOf_iff_le_normalizer_inf]
            rw [Subgroup.le_normalizer_iff]
            intro c hc x hx
            exact ⟨(Subgroup.le_normalizer_iff.mp hnormT1) c hc x hx.1,
              C.mul_mem (C.mul_mem hc hx.2) (C.inv_mem hc)⟩
          have hA'_normal : A'.Normal := by
            rw [Subgroup.normal_subgroupOf_iff_le_normalizer_inf]
            rw [Subgroup.le_normalizer_iff]
            intro c hc x hx
            exact ⟨(Subgroup.le_normalizer_iff.mp hnormT2) c hc x hx.1,
              C.mul_mem (C.mul_mem hc hx.2) (C.inv_mem hc)⟩
          rcases mem_or_comap_altSubgroup_le_of_normal e A hA_normal hA_ne with hzA | hKA
          · exfalso
            have huT1 : u ∈ T₁ := by
              have hthis : (⟨u, huC⟩ : ↥C) ∈ A := hz ▸ hzA
              exact Subgroup.mem_subgroupOf.mp (show (⟨u, huC⟩ : ↥C) ∈ T₁.subgroupOf C from hthis)
            exact hT2C (fun t ht =>
              Subgroup.mem_centralizer_singleton_iff.mpr
                ((Subgroup.mem_centralizer_iff.mp (hT2comm ht) u huT1).symm))
          · rcases mem_or_comap_altSubgroup_le_of_normal e A' hA'_normal hA'_ne with hzA' | hKA'
            · exfalso
              have huT2 : u ∈ T₂ := by
                have hthis : (⟨u, huC⟩ : ↥C) ∈ A' := hz ▸ hzA'
                exact Subgroup.mem_subgroupOf.mp (show (⟨u, huC⟩ : ↥C) ∈ T₂.subgroupOf C from hthis)
              exact hT1C (fun t ht =>
                Subgroup.mem_centralizer_singleton_iff.mpr
                  ((Subgroup.mem_centralizer_iff.mp (hcomm ht) u huT2).symm))
            · exfalso
              have hKle : K ≤ A ⊓ A' := le_inf hKA hKA'
              rw [hdisj] at hKle
              exact hK_ne (le_bot_iff.mp hKle)
end CFSG.EvenSporadicStandard.TwoHS.GH312
