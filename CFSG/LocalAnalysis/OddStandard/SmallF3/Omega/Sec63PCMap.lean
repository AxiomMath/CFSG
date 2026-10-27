module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PCDef
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PTSub
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Trans

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem map_inf_centralizer_singleton {X : Type} [Group X] (f : X →* G)
    (hf : Function.Injective f) (Y : Subgroup X) (y : X) :
    (Y ⊓ centralizer ({y} : Set X)).map f = Y.map f ⊓ centralizer ({f y} : Set G) := by
  apply le_antisymm
  · rintro z hz
    rcases Subgroup.mem_map.mp hz with ⟨w, hw, rfl⟩
    obtain ⟨hwY, hwy⟩ := Subgroup.mem_inf.mp hw
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_map_of_mem f hwY, ?_⟩
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hwy]
  · intro z hz
    obtain ⟨hzY, hzc⟩ := Subgroup.mem_inf.mp hz
    rcases Subgroup.mem_map.mp hzY with ⟨w, hwY, rfl⟩
    refine Subgroup.mem_map_of_mem f (Subgroup.mem_inf.mpr ⟨hwY, ?_⟩)
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    exact hf (by rw [map_mul, map_mul, Subgroup.mem_centralizer_singleton_iff.mp hzc])

private theorem map_closure_involutions {X : Type} [Group X] (f : X →* G)
    (hf : Function.Injective f) {R : Subgroup X} :
    (closure {r : X | r ∈ R ∧ orderOf r = 2}).map f =
      closure {r : G | r ∈ R.map f ∧ orderOf r = 2} := by
  rw [MonoidHom.map_closure]
  congr 1
  ext r
  constructor
  · rintro ⟨p, ⟨hpR, hp2⟩, rfl⟩
    exact ⟨⟨p, hpR, rfl⟩, by rw [orderOf_injective f hf p]; exact hp2⟩
  · rintro ⟨⟨p, hpR, hpr⟩, hr2⟩
    refine ⟨p, ⟨hpR, ?_⟩, hpr⟩
    rw [← orderOf_injective f hf p, hpr]
    exact hr2

theorem sec63PC_sl23PocketIn_map_iff {X : Type} [Group X] (f : X →* G)
    (hf : Function.Injective f) {Y K : Subgroup X} {y : X} :
    Sl23PocketIn (Y.map f) (f y) (K.map f) ↔ Sl23PocketIn Y y K := by
  let A : Subgroup X := Y ⊓ centralizer ({y} : Set X)
  have hA : A.map f = Y.map f ⊓ centralizer ({f y} : Set G) :=
    map_inf_centralizer_singleton f hf Y y
  have hmem : f y ∈ K.map f ↔ y ∈ K := Subgroup.mem_map_iff_mem hf
  have hle : K.map f ≤ Y.map f ⊓ centralizer ({f y} : Set G) ↔ K ≤ A := by
    rw [← hA]
    exact Subgroup.map_le_map_iff_of_injective hf
  constructor
  · intro h
    unfold Sl23PocketIn at h ⊢
    obtain ⟨h1, h2, h3, h4⟩ := h
    have hKA : K ≤ A := hle.mp h2
    let ε : ↥A ≃* ↥(A.map f) := A.equivMapOfInjective f hf
    have heq : (K.subgroupOf A).map ε.toMonoidHom =
        (K.map f).subgroupOf (A.map f) := by
      apply Subgroup.map_injective (Subgroup.subtype_injective (A.map f))
      rw [Subgroup.map_map]
      have hcomp : ((A.map f).subtype).comp ε.toMonoidHom = f.comp A.subtype := by
        ext m
        rfl
      rw [hcomp, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hKA,
        Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (Subgroup.map_mono hKA)]
    refine ⟨hmem.mp h1, hKA, ?_, ?_⟩
    · have hsn : ((K.subgroupOf A).map ε.toMonoidHom).IsSubnormal := by
        rw [heq, hA]
        exact h3
      have h' := Subgroup.IsSubnormal.map (f := ε.symm.toMonoidHom) ε.symm.surjective hsn
      rwa [CFSG.LocalCores.map_map_symm] at h'
    · exact isSL23Mod_of_mulEquiv (K.equivMapOfInjective f hf).symm h4
  · intro h
    unfold Sl23PocketIn at h ⊢
    obtain ⟨h1, h2, h3, h4⟩ := h
    have hKA : K ≤ A := h2
    let ε : ↥A ≃* ↥(A.map f) := A.equivMapOfInjective f hf
    have heq : (K.subgroupOf A).map ε.toMonoidHom =
        (K.map f).subgroupOf (A.map f) := by
      apply Subgroup.map_injective (Subgroup.subtype_injective (A.map f))
      rw [Subgroup.map_map]
      have hcomp : ((A.map f).subtype).comp ε.toMonoidHom = f.comp A.subtype := by
        ext m
        rfl
      rw [hcomp, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hKA,
        Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (Subgroup.map_mono hKA)]
    refine ⟨hmem.mpr h1, hle.mpr hKA, ?_, ?_⟩
    · have hsn : ((K.subgroupOf A).map ε.toMonoidHom).IsSubnormal :=
        Subgroup.IsSubnormal.map (f := ε.toMonoidHom) ε.surjective h3
      rw [heq, hA] at hsn
      exact hsn
    · exact isSL23Mod_of_mulEquiv (K.equivMapOfInjective f hf) h4

theorem sec63PC_isI4PlusIn_map_iff {X : Type} [Group X] (f : X →* G)
    (hf : Function.Injective f) {Y : Subgroup X} {y : X} :
    IsI4PlusIn (Y.map f) (f y) ↔ IsI4PlusIn Y y := by
  have hord : orderOf (f y) = orderOf y := orderOf_injective f hf y
  constructor
  · rintro ⟨h2, K₁, hK₁⟩
    have hK₁Y : K₁ ≤ Y.map f := le_trans hK₁.2.1 inf_le_left
    have hK₁r : K₁ ≤ f.range := le_trans hK₁Y (Subgroup.map_le_range f Y)
    have hEq : (K₁.comap f).map f = K₁ := Subgroup.map_comap_eq_self hK₁r
    refine ⟨?_, K₁.comap f, ?_⟩
    · rw [← hord]; exact h2
    · exact (sec63PC_sl23PocketIn_map_iff f hf).mp (by rwa [hEq])
  · rintro ⟨h2, K, hK⟩
    exact ⟨by rw [hord, h2], K.map f, (sec63PC_sl23PocketIn_map_iff f hf).mpr hK⟩

theorem sec63PC_map_conj_of_mem {Y : Subgroup G} {g : G} (hg : g ∈ Y) :
    Y.map (MulAut.conj g).toMonoidHom = Y := by
  apply le_antisymm
  · rintro z ⟨y, hy, rfl⟩
    show g * y * g⁻¹ ∈ Y
    exact Y.mul_mem (Y.mul_mem hg hy) (Y.inv_mem hg)
  · intro y hy
    refine ⟨g⁻¹ * y * g, ?_, ?_⟩
    · show g⁻¹ * y * g ∈ Y
      exact Y.mul_mem (Y.mul_mem (Y.inv_mem hg) hy) hg
    · show g * (g⁻¹ * y * g) * g⁻¹ = y
      group

theorem sec63PC_at_map_iff [Finite G] {X : Type} [Group X] (f : X →* G)
    (hf : Function.Injective f) {Y V : Subgroup X} {b : X} :
    Sec63PCAt (Y.map f) (V.map f) (f b) ↔ Sec63PCAt Y V b := by
  have hA : (Y ⊓ centralizer ({b} : Set X)).map f =
      Y.map f ⊓ centralizer ({f b} : Set G) :=
    map_inf_centralizer_singleton f hf Y b
  unfold Sec63PCAt
  constructor
  · rintro (h12 | ⟨Vb', hc', hL', hu', h2', R', hR'2, hR'le, hR'8, hR'gen⟩)
    · exact Or.inl ((sec63PC_isI4PlusIn_map_iff f hf).mp h12)
    · have hVb'le : Vb' ≤ f.range :=
        le_trans (le_trans hc'.1 inf_le_left) (Subgroup.map_le_range f Y)
      let Vb : Subgroup X := Vb'.comap f
      have hVbmf : Vb.map f = Vb' := Subgroup.map_comap_eq_self hVb'le
      refine Or.inr ⟨Vb, ?_, ?_, ?_, ?_, ?_⟩
      · refine (sec63PT_isComponentIn_map_iff f hf).mp ?_
        rw [hVbmf, hA]
        exact hc'
      · refine (sec63PT_isL29_map_iff f hf).mp ?_
        rw [hVbmf]
        exact hL'
      · intro K hK
        apply Subgroup.map_injective hf
        rw [hVbmf]
        have hK' : IsComponentIn (K.map f)
            (Y.map f ⊓ centralizer ({f b} : Set G)) := by
          have htmp := (sec63PT_isComponentIn_map_iff f hf).mpr hK
          rwa [hA] at htmp
        exact hu' (K.map f) hK'
      · intro Q hQ hQle
        have hQV : Q ≤ V := le_trans (le_trans hQle inf_le_left) inf_le_left
        have hQcb : Q ≤ centralizer ({b} : Set X) :=
          le_trans (le_trans hQle inf_le_left) inf_le_right
        have hQVb : Q ≤ centralizer (Vb : Set X) := le_trans hQle inf_le_right
        have hmapcb : (centralizer ({b} : Set X)).map f ≤
            centralizer ({f b} : Set G) := by
          simpa using Subgroup.map_centralizer_le_centralizer_image ({b} : Set X) f
        have hmapVb : (centralizer (Vb : Set X)).map f ≤
            centralizer (Vb' : Set G) := by
          have h := Subgroup.map_centralizer_le_centralizer_image (Vb : Set X) f
          rw [← Subgroup.coe_map f Vb, hVbmf] at h
          exact h
        have hle' : Q.map f ≤ V.map f ⊓ centralizer ({f b} : Set G) ⊓
            centralizer (Vb' : Set G) :=
          le_inf (le_inf (Subgroup.map_mono hQV)
            ((Subgroup.map_mono hQcb).trans hmapcb))
            ((Subgroup.map_mono hQVb).trans hmapVb)
        have hcard := h2' (Q.map f) (hQ.map f) hle'
        rwa [Subgroup.card_map_of_injective hf] at hcard
      · have hR'V : R' ≤ V.map f := le_trans hR'le inf_le_left
        have hR'cb : R' ≤ centralizer ({f b} : Set G) := le_trans hR'le inf_le_right
        have hR'le_range : R' ≤ f.range := le_trans hR'V (Subgroup.map_le_range f V)
        let R : Subgroup X := R'.comap f
        have hRmap : R.map f = R' := Subgroup.map_comap_eq_self hR'le_range
        refine ⟨R, hR'2.comap_of_injective f hf, ?_, ?_, ?_⟩
        · have hRV : R ≤ V :=
            (Subgroup.map_le_map_iff_of_injective hf).mp (by rw [hRmap]; exact hR'V)
          have hRcb : R ≤ centralizer ({b} : Set X) := by
            intro r hr
            rw [Subgroup.mem_centralizer_singleton_iff]
            apply hf
            rw [map_mul, map_mul]
            have hr' := hR'cb (by rw [← hRmap]; exact Subgroup.mem_map_of_mem f hr)
            exact Subgroup.mem_centralizer_singleton_iff.mp hr'
          exact le_inf hRV hRcb
        · rw [← Subgroup.card_map_of_injective hf (K := R), hRmap]
          exact hR'8
        · apply Subgroup.map_injective hf
          rw [hRmap, map_closure_involutions f hf, hRmap]
          exact hR'gen
  · rintro (h12 | ⟨Vb, hc, hL, hu, h2, R, hR2, hRle, hR8, hRgen⟩)
    · exact Or.inl ((sec63PC_isI4PlusIn_map_iff f hf).mpr h12)
    · refine Or.inr ⟨Vb.map f, ?_, ?_, ?_, ?_, ?_⟩
      · have htmp := (sec63PT_isComponentIn_map_iff f hf).mpr hc
        rwa [hA] at htmp
      · exact (sec63PT_isL29_map_iff f hf).mpr hL
      · intro K' hK'
        have hK'le : K' ≤ f.range :=
          le_trans (le_trans hK'.1 inf_le_left) (Subgroup.map_le_range f Y)
        have hK'map : (K'.comap f).map f = K' := Subgroup.map_comap_eq_self hK'le
        have hKc : IsComponentIn (K'.comap f) (Y ⊓ centralizer ({b} : Set X)) := by
          refine (sec63PT_isComponentIn_map_iff f hf).mp ?_
          rw [hK'map, hA]
          exact hK'
        rw [← hK'map, hu (K'.comap f) hKc]
      · intro Q' hQ' hQ'le
        let Q : Subgroup X := Q'.comap f
        have hQ'le_range : Q' ≤ f.range :=
          le_trans (le_trans (le_trans hQ'le inf_le_left) inf_le_left)
            (Subgroup.map_le_range f V)
        have hQmap : Q.map f = Q' := Subgroup.map_comap_eq_self hQ'le_range
        have hQle : Q ≤ V ⊓ centralizer ({b} : Set X) ⊓ centralizer (Vb : Set X) := by
          refine le_inf (le_inf ?_ ?_) ?_
          · exact (Subgroup.map_le_map_iff_of_injective hf).mp (by
              rw [hQmap]; exact le_trans (le_trans hQ'le inf_le_left) inf_le_left)
          · intro q hq
            rw [Subgroup.mem_centralizer_singleton_iff]
            apply hf
            rw [map_mul, map_mul]
            have hq' := le_trans (le_trans hQ'le inf_le_left) inf_le_right
              (by rw [← hQmap]; exact Subgroup.mem_map_of_mem f hq)
            exact Subgroup.mem_centralizer_singleton_iff.mp hq'
          · intro q hq
            rw [Subgroup.mem_centralizer_iff]
            intro v hv
            apply hf
            rw [map_mul, map_mul]
            have hq' := le_trans hQ'le inf_le_right
              (by rw [← hQmap]; exact Subgroup.mem_map_of_mem f hq)
            rw [Subgroup.mem_centralizer_iff] at hq'
            exact hq' (f v) (Subgroup.mem_map_of_mem f hv)
        have hcard := h2 Q (hQ'.comap_of_injective f hf) hQle
        rw [← Subgroup.card_map_of_injective (f := f) hf (K := Q)] at hcard
        rwa [hQmap] at hcard
      · have hR_V : R ≤ V := le_trans hRle inf_le_left
        have hR_cb : R ≤ centralizer ({b} : Set X) := le_trans hRle inf_le_right
        refine ⟨R.map f, hR2.map f, ?_, ?_, ?_⟩
        · have hRcb : R.map f ≤ centralizer ({f b} : Set G) :=
            (Subgroup.map_mono hR_cb).trans (by
              simpa using Subgroup.map_centralizer_le_centralizer_image ({b} : Set X) f)
          exact le_inf (Subgroup.map_mono hR_V) hRcb
        · rw [Subgroup.card_map_of_injective hf]
          exact hR8
        · conv_lhs => rw [hRgen]
          exact map_closure_involutions f hf

theorem sec63PC_isI4PlusIn_conj {Y : Subgroup G} {y g : G} (hg : g ∈ Y) (h : IsI4PlusIn Y y) :
    IsI4PlusIn Y (g * y * g⁻¹) := by
  have h' : IsI4PlusIn (Y.map (MulAut.conj g).toMonoidHom) (MulAut.conj g y) :=
    (sec63PC_isI4PlusIn_map_iff (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).mpr h
  rwa [sec63PC_map_conj_of_mem hg, MulAut.conj_apply] at h'

theorem sec63PC_at_conj [Finite G] {Y V : Subgroup G} {b g : G} (hgY : g ∈ Y) (hgV : g ∈ V)
    (h : Sec63PCAt Y V b) : Sec63PCAt Y V (g * b * g⁻¹) := by
  have h' : Sec63PCAt (Y.map (MulAut.conj g).toMonoidHom) (V.map (MulAut.conj g).toMonoidHom)
      (MulAut.conj g b) :=
    (sec63PC_at_map_iff (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).mpr h
  rwa [sec63PC_map_conj_of_mem hgY, sec63PC_map_conj_of_mem hgV, MulAut.conj_apply] at h'

theorem sec63PC_fact_conj [Finite G] {Y : Subgroup G} {s g : G} (hg : g ∈ Y)
    (h : Sec63PCFact Y s) : Sec63PCFact Y (g * s * g⁻¹) := by
  unfold Sec63PCFact at h
  intro V hV hVL b hbV hb2
  have he_apply : (MulAut.conj g⁻¹) (g * s * g⁻¹) = s := by
    rw [MulAut.conj_apply]
    group
  have hYmap : Y.map (MulAut.conj g⁻¹).toMonoidHom = Y :=
    sec63PC_map_conj_of_mem (Y.inv_mem hg)
  have hcentral : (Y ⊓ centralizer ({g * s * g⁻¹} : Set G)).map
      (MulAut.conj g⁻¹).toMonoidHom = Y ⊓ centralizer ({s} : Set G) := by
    rw [CFSG.centralizer_inter_map (MulAut.conj g⁻¹) Y (g * s * g⁻¹), hYmap, he_apply]
  have hV₀ : IsComponentIn (V.map (MulAut.conj g⁻¹).toMonoidHom)
      (Y ⊓ centralizer ({s} : Set G)) := by
    have hpre : IsComponentIn (V.map (MulAut.conj g⁻¹).toMonoidHom)
        ((Y ⊓ centralizer ({g * s * g⁻¹} : Set G)).map
          (MulAut.conj g⁻¹).toMonoidHom) :=
      (sec63PT_isComponentIn_map_iff (MulAut.conj g⁻¹).toMonoidHom
        (MulAut.conj g⁻¹).injective).mpr hV
    rwa [hcentral] at hpre
  have hL₀ : IsL29 (V.map (MulAut.conj g⁻¹).toMonoidHom) :=
    (sec63PT_isL29_map_iff (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective).mpr hVL
  let b₀ : G := (MulAut.conj g⁻¹).toMonoidHom b
  have hb₀V : b₀ ∈ V.map (MulAut.conj g⁻¹).toMonoidHom :=
    Subgroup.mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hbV
  have hb₀2 : orderOf b₀ = 2 := by
    rw [show b₀ = (MulAut.conj g⁻¹).toMonoidHom b from rfl,
      orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective b, hb2]
  have hmain : Sec63PCAt Y (V.map (MulAut.conj g⁻¹).toMonoidHom) b₀ :=
    h _ hV₀ hL₀ b₀ hb₀V hb₀2
  have h' : Sec63PCAt (Y.map (MulAut.conj g).toMonoidHom)
      ((V.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom)
      ((MulAut.conj g).toMonoidHom b₀) :=
    (sec63PC_at_map_iff (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).mpr hmain
  have hVmap : (V.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = V := by
    rw [Subgroup.map_map]
    have hcomp : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
        MonoidHom.id G := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [hcomp, Subgroup.map_id]
  have hb0 : (MulAut.conj g).toMonoidHom b₀ = b := by
    rw [show b₀ = (MulAut.conj g⁻¹).toMonoidHom b from rfl]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [sec63PC_map_conj_of_mem hg, hVmap, hb0] at h'
  exact h'

end CFSG.OddStandard.SmallF3.Omega
