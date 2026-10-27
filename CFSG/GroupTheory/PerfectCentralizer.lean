module

public import CFSG.Quasithin.Background.B1MoreQuot
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.Quasithin

open scoped commutatorElement Pointwise

variable {W : Type*} [CommGroup W] [Finite W]

theorem MulAut.eq_one_of_mul_mem_center {H : Type*} [Group H] [Finite H]
    (hH : Group.IsPerfect H) (σ : MulAut H)
    (hσ : ∀ h : H, σ h * h⁻¹ ∈ Subgroup.center H) : σ = 1 := by
  classical
  let f : H →* ↥(Subgroup.center H) :=
    { toFun := fun h => (⟨σ h * h⁻¹, hσ h⟩ : ↥(Subgroup.center H))
      map_one' := by
        apply Subtype.ext
        show σ 1 * 1⁻¹ = 1
        simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subtype.coe_mk]
        have hc : x * (σ y * y⁻¹) = (σ y * y⁻¹) * x := Subgroup.mem_center_iff.mp (hσ y) x
        have hcinv : (σ y * y⁻¹) * x⁻¹ = x⁻¹ * (σ y * y⁻¹) := by
          rw [show (σ y * y⁻¹) * x⁻¹ = x⁻¹ * (x * (σ y * y⁻¹)) * x⁻¹ by group, hc]
          group
        calc σ (x * y) * (x * y)⁻¹ = σ x * σ y * (y⁻¹ * x⁻¹) := by rw [map_mul, mul_inv_rev]
          _ = σ x * σ y * y⁻¹ * x⁻¹ := by group
          _ = σ x * ((σ y * y⁻¹) * x⁻¹) := by group
          _ = σ x * (x⁻¹ * (σ y * y⁻¹)) := by rw [hcinv]
          _ = σ x * x⁻¹ * (σ y * y⁻¹) := by group }
  haveI : Group.IsPerfect ↥f.range := Group.IsPerfect.range f
  haveI : IsMulCommutative ↥f.range :=
    IsMulCommutative.of_comm fun a b =>
      Subtype.ext (Subtype.ext (Subgroup.mem_center_iff.mp b.1.2 a.1.1))
  haveI : Subsingleton ↥f.range := Group.IsPerfect.subsingleton_of_isMulCommutative
  have hf : ∀ h : H, f h = 1 := by
    intro h
    have h1 : (⟨f h, h, rfl⟩ : ↥f.range) = 1 := Subsingleton.elim _ _
    exact congrArg Subtype.val h1
  ext h
  have h2 : σ h * h⁻¹ = 1 := congrArg Subtype.val (hf h)
  exact mul_inv_eq_one.mp h2

theorem centralizes_of_commutator_mem_center {H : Subgroup (MulAut W)}
    (hH : ⁅H, H⁆ = H) {x : MulAut W}
    (hxN : x ∈ Subgroup.normalizer (H : Set (MulAut W)))
    (hx : ∀ h ∈ H, ⁅x, h⁆ ∈ (Subgroup.center ↥H).map H.subtype) :
    x ∈ Subgroup.centralizer (H : Set (MulAut W)) := by
  let σ : MulAut ↥H := H.normalizerMonoidHom ⟨x, hxN⟩
  have hσ : ∀ h : ↥H, σ h * h⁻¹ ∈ Subgroup.center ↥H := by
    intro h
    obtain ⟨z, hz, hzval⟩ := Subgroup.mem_map.mp (hx h.1 h.2)
    have hcoord : (σ h * h⁻¹ : ↥H) = z := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_inv,
        Subgroup.normalizerMonoidHom_apply_apply_coe,
        show (z : MulAut W) = ⁅x, (h : MulAut W)⁆ from hzval, commutatorElement_def]
    rwa [hcoord]
  have hperf : Group.IsPerfect ↥H := Subgroup.isPerfect_iff.mpr hH
  have hσ1 : σ = 1 := MulAut.eq_one_of_mul_mem_center hperf σ hσ
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have h1 : σ ⟨h, hh⟩ = ⟨h, hh⟩ := by rw [hσ1]; rfl
  have h2 : x * h * x⁻¹ = h := by
    have := congrArg Subtype.val h1
    simpa [σ, Subgroup.normalizerMonoidHom_apply_apply_coe] using this
  calc h * x = (x * h * x⁻¹) * x := by rw [h2]
    _ = x * h := by group

theorem mem_center_of_commutator_mem_center {K : Type*} [Group K] [Finite K]
    (hK : Group.IsPerfect K) {h : K} (hc : ∀ k : K, ⁅h, k⁆ ∈ Subgroup.center K) :
    h ∈ Subgroup.center K := by
  have hσ : ∀ k : K, MulAut.conj h k * k⁻¹ ∈ Subgroup.center K := by
    intro k
    rw [MulAut.conj_apply]
    simpa [commutatorElement_def] using hc k
  have h1 : MulAut.conj h = 1 := MulAut.eq_one_of_mul_mem_center hK (MulAut.conj h) hσ
  rw [Subgroup.mem_center_iff]
  intro k
  have hk : h * k * h⁻¹ = k := by
    have := congrArg (fun φ : MulAut K => φ k) h1
    simpa [MulAut.conj_apply] using this
  calc k * h = (h * k * h⁻¹) * h := by rw [hk]
    _ = h * k := by group

theorem centralizes_of_resAut_mem_centralizer {H : Subgroup (MulAut W)}
    {A' : Subgroup W} (hH : ⁅H, H⁆ = H) (hHA : H ≤ stabSub A')
    (hCA : ∀ h : ↥H, (h : MulAut W) ∈ centSub A' → h ∈ Subgroup.center ↥H)
    {s : MulAut W} (hsN : s ∈ Subgroup.normalizer (H : Set (MulAut W)))
    (hsA : s ∈ stabSub A')
    (hs : resAut A' ⟨s, hsA⟩ ∈
      Subgroup.centralizer (autSub H A' : Set (MulAut (↥A')))) :
    s ∈ Subgroup.centralizer (H : Set (MulAut W)) := by
  refine centralizes_of_commutator_mem_center hH hsN fun h hh => ?_
  have hshH : ⁅s, h⁆ ∈ H := by
    have h1 : s * h * s⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp hsN h).mp hh
    exact H.mul_mem h1 (H.inv_mem hh)
  have hshC : ⁅s, h⁆ ∈ centSub A' := by
    rw [mem_centSub]
    intro a ha
    have hinv : h⁻¹ ∈ H := H.inv_mem hh
    have hsA' : s⁻¹ ∈ stabSub A' := inv_mem hsA
    have h1 : h⁻¹ a ∈ A' := (mem_stabSub.mp (hHA hinv) a).mpr ha
    have h2 : s⁻¹ (h⁻¹ a) ∈ A' := (mem_stabSub.mp hsA' (h⁻¹ a)).mpr h1
    have hmem : resAut A' ⟨h, hHA hh⟩ ∈ autSub H A' :=
      mem_autSub.mpr ⟨⟨h, hHA hh⟩, hh, rfl⟩
    have hcomm := Subgroup.mem_centralizer_iff.mp hs _ hmem
    have hkey := congrArg (fun φ : MulAut ↥A' => φ ⟨s⁻¹ (h⁻¹ a), h2⟩) hcomm
    simp only [MulAut.mul_apply] at hkey
    have hkey' := congrArg Subtype.val hkey
    change ((resHom A' ⟨h, hHA hh⟩) ((resHom A' ⟨s, hsA⟩) ⟨s⁻¹ (h⁻¹ a), h2⟩) : W) =
      ((resHom A' ⟨s, hsA⟩) ((resHom A' ⟨h, hHA hh⟩) ⟨s⁻¹ (h⁻¹ a), h2⟩) : W) at hkey'
    simp only [resHom_apply] at hkey'
    rw [show s (s⁻¹ (h⁻¹ a)) = h⁻¹ a by simp [MulAut.inv_apply],
      show h (h⁻¹ a) = a by simp [MulAut.inv_apply]] at hkey'
    have h4 : ⁅s, h⁆ a = s (h (s⁻¹ (h⁻¹ a))) := by
      rw [commutatorElement_def]
      simp only [MulAut.mul_apply, MulAut.inv_apply]
    rw [h4, ← hkey']
  have hmem := hCA ⟨⁅s, h⁆, hshH⟩ hshC
  exact Subgroup.mem_map.mpr ⟨⟨⁅s, h⁆, hshH⟩, hmem, rfl⟩

theorem centralizes_of_quotHom_mem_centralizer {H : Subgroup (MulAut W)}
    {A' : Subgroup W} (hH : ⁅H, H⁆ = H) (hHA : H ≤ stabSub A')
    (hCW : ∀ h : ↥H, (h : MulAut W) ∈ centQuot A' → h ∈ Subgroup.center ↥H)
    {s : MulAut W} (hsN : s ∈ Subgroup.normalizer (H : Set (MulAut W)))
    (hsA : s ∈ stabSub A')
    (hs : quotHom A' ⟨s, hsA⟩ ∈
      Subgroup.centralizer (autQuot H A' : Set (MulAut (W ⧸ A')))) :
    s ∈ Subgroup.centralizer (H : Set (MulAut W)) := by
  refine centralizes_of_commutator_mem_center hH hsN fun h hh => ?_
  have hshH : ⁅s, h⁆ ∈ H := by
    have h1 : s * h * s⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp hsN h).mp hh
    exact H.mul_mem h1 (H.inv_mem hh)
  have hshC : ⁅s, h⁆ ∈ centQuot A' := by
    have hmem : quotHom A' ⟨h, hHA hh⟩ ∈ autQuot H A' :=
      mem_autQuot.mpr ⟨⟨h, hHA hh⟩, hh, rfl⟩
    have hcomm := Subgroup.mem_centralizer_iff.mp hs _ hmem
    have hprod : quotHom A' ⟨⁅s, h⁆, hHA hshH⟩ = 1 := by
      have hmap := map_commutatorElement (quotHom A')
        (⟨s, hsA⟩ : stabSub A') ⟨h, hHA hh⟩
      have hR : ⁅(quotHom A') ⟨s, hsA⟩, (quotHom A') ⟨h, hHA hh⟩⁆ = 1 := by
        rw [commutatorElement_def]
        calc (quotHom A') ⟨s, hsA⟩ * (quotHom A') ⟨h, hHA hh⟩ *
              ((quotHom A') ⟨s, hsA⟩)⁻¹ * ((quotHom A') ⟨h, hHA hh⟩)⁻¹
            = (quotHom A') ⟨h, hHA hh⟩ * (quotHom A') ⟨s, hsA⟩ *
              ((quotHom A') ⟨s, hsA⟩)⁻¹ * ((quotHom A') ⟨h, hHA hh⟩)⁻¹ := by rw [hcomm]
          _ = 1 := by group
      have hc : quotHom A' ⁅(⟨s, hsA⟩ : stabSub A'), ⟨h, hHA hh⟩⁆ = 1 := by
        rw [hmap, hR]
      have he : (⟨⁅s, h⁆, hHA hshH⟩ : stabSub A') =
          ⁅(⟨s, hsA⟩ : stabSub A'), ⟨h, hHA hh⟩⁆ := by
        apply Subtype.ext
        rfl
      exact he.symm ▸ hc
    rw [← MonoidHom.mem_ker, ker_quotHom, Subgroup.mem_subgroupOf] at hprod
    exact hprod
  have hmem := hCW ⟨⁅s, h⁆, hshH⟩ hshC
  exact Subgroup.mem_map.mpr ⟨⟨⁅s, h⁆, hshH⟩, hmem, rfl⟩

private noncomputable def toAutSub {H : Subgroup (MulAut W)} {A' : Subgroup W}
    (hHA : H ≤ stabSub A') : ↥H →* ↥(autSub H A') where
  toFun h := ⟨resHom A' ⟨h, hHA h.2⟩, mem_autSub.mpr ⟨⟨h, hHA h.2⟩, h.2, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    change (resHom A' (1 : stabSub A') : MulAut ↥A') = 1
    rw [map_one]
  map_mul' x y := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    change (resHom A' ((⟨x, hHA x.2⟩ : stabSub A') * ⟨y, hHA y.2⟩) : MulAut ↥A') =
      (resHom A' ⟨x, hHA x.2⟩ : MulAut ↥A') * resHom A' ⟨y, hHA y.2⟩
    rw [map_mul]

private noncomputable def toAutQuot {H : Subgroup (MulAut W)} {A' : Subgroup W}
    (hHA : H ≤ stabSub A') : ↥H →* ↥(autQuot H A') where
  toFun h := ⟨quotHom A' ⟨h, hHA h.2⟩, mem_autQuot.mpr ⟨⟨h, hHA h.2⟩, h.2, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    change (quotHom A' (1 : stabSub A') : MulAut (W ⧸ A')) = 1
    rw [map_one]
  map_mul' x y := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    change (quotHom A' ((⟨x, hHA x.2⟩ : stabSub A') * ⟨y, hHA y.2⟩) : MulAut (W ⧸ A')) =
      (quotHom A' ⟨x, hHA x.2⟩ : MulAut (W ⧸ A')) * quotHom A' ⟨y, hHA y.2⟩
    rw [map_mul]

private theorem toAutSub_surjective {H : Subgroup (MulAut W)} {A' : Subgroup W}
    (hHA : H ≤ stabSub A') : Function.Surjective (toAutSub hHA) := by
  rintro ⟨φ, hφ⟩
  obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
  exact ⟨⟨(g : MulAut W), hg⟩, by simp [toAutSub]⟩


private theorem toAutQuot_surjective {H : Subgroup (MulAut W)} {A' : Subgroup W}
    (hHA : H ≤ stabSub A') : Function.Surjective (toAutQuot hHA) := by
  rintro ⟨φ, hφ⟩
  obtain ⟨g, hg, rfl⟩ := mem_autQuot.mp hφ
  exact ⟨⟨(g : MulAut W), hg⟩, by simp [toAutQuot]⟩

private theorem toAutSub_ker {H : Subgroup (MulAut W)} {A' : Subgroup W}
    (hHA : H ≤ stabSub A') (h : ↥H) :
    toAutSub hHA h = 1 ↔ (h : MulAut W) ∈ centSub A' := by
  constructor
  · intro h1
    have h2 : resHom A' ⟨h, hHA h.2⟩ = 1 := by
      simpa [toAutSub] using congrArg Subtype.val h1
    rw [← MonoidHom.mem_ker, ker_resHom, Subgroup.mem_subgroupOf] at h2
    exact h2
  · intro h1
    have h2 : resHom A' ⟨h, hHA h.2⟩ = 1 := by
      rw [← MonoidHom.mem_ker, ker_resHom, Subgroup.mem_subgroupOf]
      exact h1
    exact Subtype.ext (by simpa [toAutSub] using h2)

private theorem toAutQuot_ker {H : Subgroup (MulAut W)} {A' : Subgroup W}
    (hHA : H ≤ stabSub A') (h : ↥H) :
    toAutQuot hHA h = 1 ↔ (h : MulAut W) ∈ centQuot A' := by
  constructor
  · intro h1
    have h2 : quotHom A' ⟨h, hHA h.2⟩ = 1 := by
      simpa [toAutQuot] using congrArg Subtype.val h1
    rw [← MonoidHom.mem_ker, ker_quotHom, Subgroup.mem_subgroupOf] at h2
    exact h2
  · intro h1
    have h2 : quotHom A' ⟨h, hHA h.2⟩ = 1 := by
      rw [← MonoidHom.mem_ker, ker_quotHom, Subgroup.mem_subgroupOf]
      exact h1
    exact Subtype.ext (by simpa [toAutQuot] using h2)

private theorem ker_toAutQuot_le_ker_center {H : Subgroup (MulAut W)} {A' : Subgroup W}
    (hHA : H ≤ stabSub A')
    (hCW : ∀ h : ↥H, (h : MulAut W) ∈ centQuot A' → h ∈ Subgroup.center ↥H) :
    (toAutQuot hHA).ker ≤
      ((QuotientGroup.mk' (Subgroup.center ↥(autSub H A'))).comp
        (toAutSub hHA)).ker := by
  intro h hh
  rw [MonoidHom.mem_ker] at hh ⊢
  have hcentH : h ∈ Subgroup.center ↥H := hCW h ((toAutQuot_ker hHA h).mp hh)
  have hcentA : toAutSub hHA h ∈ Subgroup.center ↥(autSub H A') := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨k, rfl⟩ := toAutSub_surjective hHA g
    change toAutSub hHA k * toAutSub hHA h = toAutSub hHA h * toAutSub hHA k
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hcentH k]
  have h1 : ((QuotientGroup.mk' (Subgroup.center ↥(autSub H A'))).comp
      (toAutSub hHA)) h = QuotientGroup.mk (toAutSub hHA h) := rfl
  rw [h1, QuotientGroup.eq_one_iff]
  exact hcentA

private theorem mem_center_of_ker_center {H : Subgroup (MulAut W)} {A' : Subgroup W}
    (hH : ⁅H, H⁆ = H) (hHA : H ≤ stabSub A')
    (hCA : ∀ h : ↥H, (h : MulAut W) ∈ centSub A' → h ∈ Subgroup.center ↥H) :
    ∀ h : ↥H,
      ((QuotientGroup.mk' (Subgroup.center ↥(autSub H A'))).comp (toAutSub hHA)) h = 1 →
        h ∈ Subgroup.center ↥H := by
  intro h hh
  have hperfH : Group.IsPerfect ↥H := Subgroup.isPerfect_iff.mpr hH
  have hhA : toAutSub hHA h ∈ Subgroup.center ↥(autSub H A') := by
    rw [← QuotientGroup.eq_one_iff (N := Subgroup.center ↥(autSub H A')), ← hh]
    rfl
  refine mem_center_of_commutator_mem_center hperfH (h := h) fun k => ?_
  have hfix : ((⁅h, k⁆ : ↥H) : MulAut W) ∈ centSub A' := by
    rw [← toAutSub_ker hHA ⁅h, k⁆]
    change toAutSub hHA ⁅h, k⁆ = 1
    have hmap : toAutSub hHA ⁅h, k⁆ = ⁅toAutSub hHA h, toAutSub hHA k⁆ :=
      map_commutatorElement _ h k
    have hcomm : toAutSub hHA k * toAutSub hHA h = toAutSub hHA h * toAutSub hHA k :=
      Subgroup.mem_center_iff.mp hhA (toAutSub hHA k)
    rw [hmap, commutatorElement_def,
      show toAutSub hHA h * toAutSub hHA k = toAutSub hHA k * toAutSub hHA h from hcomm.symm]
    group
  exact hCA ⁅h, k⁆ hfix

theorem exists_surjective_center_quotient {H : Subgroup (MulAut W)} {A' : Subgroup W}
    (hH : ⁅H, H⁆ = H) (hHA : H ≤ stabSub A')
    (hCA : ∀ h : ↥H, (h : MulAut W) ∈ centSub A' → h ∈ Subgroup.center ↥H)
    (hCW : ∀ h : ↥H, (h : MulAut W) ∈ centQuot A' → h ∈ Subgroup.center ↥H) :
    ∃ f : ↥(autQuot H A') →* ↥(autSub H A') ⧸ Subgroup.center ↥(autSub H A'),
      Function.Surjective f ∧ f.ker ≤ Subgroup.center ↥(autQuot H A') := by
  classical
  let ρA := toAutSub hHA
  let ρB := toAutQuot hHA
  let φ : ↥H →* ↥(autSub H A') ⧸ Subgroup.center ↥(autSub H A') :=
    (QuotientGroup.mk' (Subgroup.center ↥(autSub H A'))).comp ρA
  have hφsurj : Function.Surjective φ :=
    (QuotientGroup.mk'_surjective _).comp (toAutSub_surjective hHA)
  have hker : ρB.ker ≤ φ.ker := ker_toAutQuot_le_ker_center hHA hCW
  have hKcenter : ∀ h : ↥H, φ h = 1 → h ∈ Subgroup.center ↥H :=
    mem_center_of_ker_center hH hHA hCA
  let F := (QuotientGroup.lift ρB.ker φ hker).comp
    (QuotientGroup.quotientKerEquivOfSurjective ρB (toAutQuot_surjective hHA)).symm.toMonoidHom
  have hF : ∀ h : ↥H, F (ρB h) = φ h := by
    intro h
    change (QuotientGroup.lift ρB.ker φ hker)
      ((QuotientGroup.quotientKerEquivOfSurjective ρB (toAutQuot_surjective hHA)).symm
        ((QuotientGroup.quotientKerEquivOfSurjective ρB (toAutQuot_surjective hHA))
          (QuotientGroup.mk h))) = φ h
    rw [MulEquiv.symm_apply_apply, QuotientGroup.lift_mk']
  refine ⟨F, ?_, ?_⟩
  · intro y
    obtain ⟨h, rfl⟩ := hφsurj y
    exact ⟨ρB h, hF h⟩
  · intro x hx
    obtain ⟨h, rfl⟩ := toAutQuot_surjective hHA x
    have hx' : φ h = 1 := by rw [← hF h]; exact hx
    have hcentH : h ∈ Subgroup.center ↥H := hKcenter h hx'
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨k, rfl⟩ := toAutQuot_surjective hHA y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hcentH k]

theorem autQuot_zpowers {V : Type*} [CommGroup V] [Finite V] {U : Subgroup V} {x : MulAut V}
    (hx : x ∈ stabSub U) :
    autQuot (Subgroup.zpowers x) U = Subgroup.zpowers (quotHom U ⟨x, hx⟩) := by
  ext φ
  rw [mem_autQuot, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨n, ?_⟩
    have hgn : g = (⟨x, hx⟩ : stabSub U) ^ n :=
      Subtype.ext (by rw [Subgroup.coe_zpow]; exact hn.symm)
    rw [hgn, map_zpow]
  · rintro ⟨n, rfl⟩
    refine ⟨(⟨x, hx⟩ : stabSub U) ^ n, ?_, ?_⟩
    · rw [Subgroup.coe_zpow]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) n
    · rw [map_zpow]

end CFSG.GroupTheory
