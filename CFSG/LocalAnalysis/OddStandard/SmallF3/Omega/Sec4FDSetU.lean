module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FDLift
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FDCompGen
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrInner

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G Pr : Type} [Group G] [Group Pr] {L : Subgroup G} {s : G} {X : Subgroup Pr} [X.Normal]
  {y : Pr} {ρ : ↥L →* ↥X}

private theorem oddCentralCover_of_ker_le {A B : Type} [Group A] [Group B] (φ : A →* B)
    (hsurj : Function.Surjective φ) {N : Subgroup A} (hker : φ.ker ≤ N) (hNc : N ≤ center A)
    (hNodd : Odd (Nat.card N)) : OddCentralCover φ :=
  ⟨hsurj, hker.trans hNc, hNodd.of_dvd_nat (Subgroup.card_dvd_of_le hker)⟩

private theorem isComponentIn_map_iff' {A M : Type} [Group A] [Group M] (f : A →* M)
    (hf : Function.Injective f) {K H : Subgroup A} :
    IsComponentIn (K.map f) (H.map f) ↔ IsComponentIn K H := by
  constructor
  · intro h
    have hle : K ≤ H := (Subgroup.map_le_map_iff_of_injective hf).mp h.1
    refine ⟨hle, ?_⟩
    let e : ↥H ≃* ↥(H.map f) := H.equivMapOfInjective f hf
    have heq : (K.subgroupOf H).map e.toMonoidHom = (K.map f).subgroupOf (H.map f) := by
      apply Subgroup.map_injective (Subgroup.subtype_injective (H.map f))
      rw [Subgroup.map_map]
      have hcomp : ((H.map f).subtype).comp e.toMonoidHom = f.comp H.subtype := by
        ext m
        rfl
      rw [hcomp, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hle,
        Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (Subgroup.map_mono hle)]
    have h' : IsComponent ((K.subgroupOf H).map e.toMonoidHom) := by
      rw [heq]
      exact h.2
    have hc := CFSG.LocalCores.isComponent_map_mulEquiv e.symm h'
    have heq' : ((K.map f).subgroupOf (H.map f)).map e.symm.toMonoidHom = K.subgroupOf H := by
      rw [← heq, CFSG.LocalCores.map_map_symm]
    rw [heq] at hc
    rw [heq'] at hc
    exact hc
  · intro h
    refine ⟨Subgroup.map_mono h.1, ?_⟩
    let e : ↥H ≃* ↥(H.map f) := H.equivMapOfInjective f hf
    have heq : (K.subgroupOf H).map e.toMonoidHom = (K.map f).subgroupOf (H.map f) := by
      apply Subgroup.map_injective (Subgroup.subtype_injective (H.map f))
      rw [Subgroup.map_map]
      have hcomp : ((H.map f).subtype).comp e.toMonoidHom = f.comp H.subtype := by
        ext m
        rfl
      rw [hcomp, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le h.1,
        Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (Subgroup.map_mono h.1)]
    rw [← heq]
    exact CFSG.LocalCores.isComponent_map_mulEquiv e h.2

theorem Sec4FDCover.exists_component_of_component [Finite G] [Finite Pr]
    (h : Sec4FDCover L s X y ρ) {v : G} (hvL : v ∈ L) (hvs : v * s = s * v) (hvv : v * v = 1)
    {K : Subgroup Pr}
    (hK : IsComponentIn K (X ⊓ centralizer ({y} : Set Pr) ⊓
      centralizer ({((ρ ⟨v, hvL⟩ : ↥X) : Pr)} : Set Pr)))
    (hoc : oddCore ↥K = ⊥) (hlie : LieModel ↥K .PSp 2 3 1) :
    ∃ K' : Subgroup G,
      IsComponentIn K' (L ⊓ centralizer ({s} : Set G) ⊓ centralizer ({v} : Set G)) ∧
        LieModel (↥K' ⧸ oddCore ↥K') .PSp 2 3 1 := by
  have hvv' : (⟨v, hvL⟩ : ↥L) * ⟨v, hvL⟩ = 1 := Subtype.ext (by simpa using hvv)
  let ρv : Pr := ((ρ ⟨v, hvL⟩ : ↥X) : Pr)
  let Y₂ : Subgroup G := L ⊓ centralizer ({s} : Set G) ⊓ centralizer ({v} : Set G)
  let Z : Subgroup Pr := X ⊓ centralizer ({y} : Set Pr) ⊓ centralizer ({ρv} : Set Pr)
  have hmemY₂ : ∀ d : ↥Y₂, (d : G) ∈ L ∧ (d : G) * s = s * (d : G) ∧
      (d : G) * v = v * (d : G) := by
    intro d
    obtain ⟨⟨hdL, hds⟩, hdv⟩ := Subgroup.mem_inf.mp d.2
    exact ⟨hdL, Subgroup.mem_centralizer_singleton_iff.mp hds,
      Subgroup.mem_centralizer_singleton_iff.mp hdv⟩
  let f : ↥Y₂ →* ↥L := Y₂.subtype.codRestrict L (fun d => (hmemY₂ d).1)
  have hf_inj : Function.Injective f := fun _ _ hab =>
    Subtype.ext (congrArg (fun x : ↥L => (x : G)) hab)
  let g : ↥Y₂ →* ↥X := ρ.comp f
  have hg_coe : ∀ d : ↥Y₂,
      ((g d : ↥X) : Pr) = ((ρ ⟨(d : G), (hmemY₂ d).1⟩ : ↥X) : Pr) := fun _ => rfl
  have hgZ : ∀ d : ↥Y₂, ((g d : ↥X) : Pr) ∈ Z := by
    intro d
    obtain ⟨hdL, hds, hdv⟩ := hmemY₂ d
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨(g d).2, ?_⟩, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff, hg_coe d]
      exact h.image_comm hdL hds
    · rw [Subgroup.mem_centralizer_singleton_iff, hg_coe d]
      have hconj : (⟨(d : G), hdL⟩ : ↥L) * ⟨v, hvL⟩ = ⟨v, hvL⟩ * ⟨(d : G), hdL⟩ :=
        Subtype.ext hdv
      have hmap : ρ ((⟨(d : G), hdL⟩ : ↥L) * ⟨v, hvL⟩) =
          ρ ((⟨v, hvL⟩ : ↥L) * ⟨(d : G), hdL⟩) :=
        congrArg (fun t : ↥L => ρ t) hconj
      rw [map_mul, map_mul] at hmap
      exact congrArg (fun x : ↥X => (x : Pr)) hmap
  let ρ₂ : ↥Y₂ →* ↥Z := (X.subtype.comp g).codRestrict Z hgZ
  have hρ₂_coe : ∀ d : ↥Y₂, ((ρ₂ d : ↥Z) : Pr) = ((g d : ↥X) : Pr) := fun _ => rfl
  have hsurj : Function.Surjective ρ₂ := by
    intro z
    obtain ⟨⟨hzX, hzy⟩, hzρv⟩ := Subgroup.mem_inf.mp z.2
    have hzy' : (z : Pr) * y = y * (z : Pr) := Subgroup.mem_centralizer_singleton_iff.mp hzy
    have hzρv' : (z : Pr) * ρv = ρv * (z : Pr) :=
      Subgroup.mem_centralizer_singleton_iff.mp hzρv
    obtain ⟨d, hdL, hds, hρd⟩ := h.exists_lift hzX hzy'
    have hdv : d * v = v * d := by
      let w : ↥L := (⟨d, hdL⟩ : ↥L) * ⟨v, hvL⟩ * (⟨d, hdL⟩ : ↥L)⁻¹
      have hww : w * w = 1 := by
        apply Subtype.ext
        change (d * v * d⁻¹) * (d * v * d⁻¹) = 1
        rw [show (d * v * d⁻¹) * (d * v * d⁻¹) = d * (v * v) * d⁻¹ by group, hvv]
        group
      have hρw : ρ w = ρ ⟨v, hvL⟩ := by
        change ρ ((⟨d, hdL⟩ : ↥L) * ⟨v, hvL⟩ * (⟨d, hdL⟩ : ↥L)⁻¹) = ρ ⟨v, hvL⟩
        apply Subtype.ext
        change ((ρ ((⟨d, hdL⟩ : ↥L) * ⟨v, hvL⟩ * (⟨d, hdL⟩ : ↥L)⁻¹) : ↥X) : Pr) = ρv
        have h4 : ((ρ ((⟨d, hdL⟩ : ↥L) * ⟨v, hvL⟩ * (⟨d, hdL⟩ : ↥L)⁻¹) : ↥X) : Pr) =
            ((ρ ⟨d, hdL⟩ : ↥X) : Pr) * ρv * ((ρ ⟨d, hdL⟩ : ↥X) : Pr)⁻¹ := by
          have h3 : ρ ((⟨d, hdL⟩ : ↥L) * ⟨v, hvL⟩ * (⟨d, hdL⟩ : ↥L)⁻¹) =
              ρ ⟨d, hdL⟩ * ρ ⟨v, hvL⟩ * (ρ ⟨d, hdL⟩)⁻¹ := by
            rw [map_mul, map_mul, map_inv]
          simpa [ρv] using congrArg (fun x : ↥X => (x : Pr)) h3
        rw [h4, hρd, hzρv']
        group
      have hwv : w = ⟨v, hvL⟩ := h.cover.eq_of_mul_self_eq_one hww hvv' hρw
      have hwval : d * v * d⁻¹ = v := congrArg Subtype.val hwv
      exact mul_inv_eq_iff_eq_mul.mp hwval
    have hdY₂ : d ∈ Y₂ :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr
          ⟨hdL, Subgroup.mem_centralizer_singleton_iff.mpr hds⟩,
        Subgroup.mem_centralizer_singleton_iff.mpr hdv⟩
    refine ⟨⟨d, hdY₂⟩, Subtype.ext ?_⟩
    show ((g ⟨d, hdY₂⟩ : ↥X) : Pr) = (z : Pr)
    rw [hg_coe]
    have hpir : ((ρ ⟨d, (hmemY₂ ⟨d, hdY₂⟩).1⟩ : ↥X) : Pr) =
        ((ρ ⟨d, hdL⟩ : ↥X) : Pr) :=
      congrArg (fun x : ↥X => (x : Pr)) (congrArg (fun t : ↥L => ρ t) (Subtype.ext rfl))
    rw [hpir]
    exact hρd
  have hρ₂ : OddCentralCover ρ₂ := by
    refine oddCentralCover_of_ker_le ρ₂ hsurj (N := (ρ.ker).comap f) ?_ ?_ ?_
    · intro n hn
      rw [Subgroup.mem_comap]
      have hgn : g n = 1 := by
        apply Subtype.ext
        have h1 : ((ρ₂ n : ↥Z) : Pr) = 1 := by rw [hn]; rfl
        rwa [hρ₂_coe n] at h1
      exact MonoidHom.mem_ker.mpr hgn
    · intro n hn
      have hn' : f n ∈ ρ.ker := Subgroup.mem_comap.mp hn
      have hnc : f n ∈ center ↥L := h.cover.ker_le_center hn'
      rw [Subgroup.mem_center_iff]
      intro m
      apply hf_inj
      rw [map_mul, map_mul]
      exact Subgroup.mem_center_iff.mp hnc (f m)
    · exact h.cover.odd_card_ker.of_dvd_nat
        (Subgroup.card_comap_dvd_of_injective (ρ.ker) f hf_inj)
  haveI : Finite ↥Y₂ := Subtype.finite
  haveI : Finite ↥Z := Subtype.finite
  have htopZ : ((⊤ : Subgroup ↥Z).map Z.subtype) = Z := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hK₁ : IsComponentIn (K.subgroupOf Z) ⊤ := by
    refine (isComponentIn_map_iff' Z.subtype Z.subtype_injective).mp ?_
    rwa [Subgroup.map_subgroupOf_eq_of_le hK.1, htopZ]
  have hoc₁ : oddCore ↥(K.subgroupOf Z) = ⊥ :=
    CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog.oddCore_eq_bot_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hK.1).symm hoc
  obtain ⟨K₂, hK₂, ⟨e4⟩⟩ := sec4FD_exists_component_lift ρ₂ hρ₂ hK₁ hoc₁
  have htopY : ((⊤ : Subgroup ↥Y₂).map Y₂.subtype) = Y₂ := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hK'map : IsComponentIn (K₂.map Y₂.subtype) ((⊤ : Subgroup ↥Y₂).map Y₂.subtype) :=
    isComponentIn_map_of_injective Y₂.subtype Y₂.subtype_injective hK₂
  refine ⟨K₂.map Y₂.subtype, ?_, ?_⟩
  · rw [htopY] at hK'map
    exact hK'map
  · let e0 : ↥(K.subgroupOf Z) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hK.1
    let e2 : ↥K₂ ≃* ↥(K₂.map Y₂.subtype) :=
      K₂.equivMapOfInjective Y₂.subtype Y₂.subtype_injective
    obtain ⟨e3⟩ := nonempty_quotient_oddCore_mulEquiv e2
    exact LieModel.of_mulEquiv ((e3.symm.trans e4).trans e0).symm hlie

end CFSG.OddStandard.SmallF3.Omega
