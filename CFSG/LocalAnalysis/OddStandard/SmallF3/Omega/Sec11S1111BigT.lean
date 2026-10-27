module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11S1111InputsB4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec11_dihSd_of_input [Finite G] (hB4 : Asc82InputDihSd) {H R D X : Subgroup G} {t : G}
    (hR : IsSylow2Of R H) (htH : t ∈ H) (hDH : D ≤ H)
    (hX : X = Subgroup.closure {s : G | ∃ h ∈ H, s = h⁻¹ * t * h})
    (htD : t ∈ D) (hDX : D ≤ X) (hdih : IsDih2 D) (h8 : 8 ≤ Nat.card ↥D)
    (hcl : ∀ x ∈ H, x ∈ normalizer (D : Set G) → x ∉ D → orderOf x = 2 →
      ∀ d ∈ D, orderOf d = 2 → ∀ g ∈ H, g⁻¹ * x * g ≠ d) :
    ∃ P : Subgroup G, IsSylow2Of P X ∧ IsDihSd P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hgens : {s : G | ∃ h ∈ H, s = h⁻¹ * t * h} ⊆ (H : Set G) := by
    rintro s ⟨h, hh, rfl⟩
    exact H.mul_mem (H.mul_mem (H.inv_mem hh) htH) hh
  have hXH : X ≤ H := by
    rw [hX, Subgroup.closure_le]
    exact hgens
  have hconj : ∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X := by
    intro h hh x hx
    have hx' : x ∈ Subgroup.closure {s : G | ∃ h' ∈ H, s = h'⁻¹ * t * h'} := by
      rw [← hX]; exact hx
    have hsub : {s : G | ∃ h' ∈ H, s = h'⁻¹ * t * h'} ⊆
        (X.comap (MulAut.conj h).toMonoidHom : Set G) := by
      rintro s ⟨h', hh', rfl⟩
      show MulAut.conj h (h'⁻¹ * t * h') ∈ X
      rw [MulAut.conj_apply]
      have hkey : h * (h'⁻¹ * t * h') * h⁻¹ = (h' * h⁻¹)⁻¹ * t * (h' * h⁻¹) := by
        group
      rw [hkey, hX]
      exact Subgroup.subset_closure ⟨h' * h⁻¹, H.mul_mem hh' (H.inv_mem hh), rfl⟩
    have hmem : x ∈ X.comap (MulAut.conj h).toMonoidHom :=
      (Subgroup.closure_le (X.comap (MulAut.conj h).toMonoidHom)).mpr hsub hx'
    simpa [MulAut.conj_apply] using hmem
  have hHnormX : H ≤ normalizer (X : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hconj h hh x
    · intro hx
      have hx' := hconj h⁻¹ (H.inv_mem hh) (h * x * h⁻¹) hx
      have hcan : h⁻¹ * (h * x * h⁻¹) * (h⁻¹)⁻¹ = x := by group
      rwa [hcan] at hx'
  have hR' : CFSG.ABGLocalTools.IsSylowOf 2 R H :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr hR
  have hInf : CFSG.ABGLocalTools.IsSylowOf 2 (R ⊓ X) X :=
    CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer hR' hXH hHnormX
  have hSylow2 : IsSylow2Of (R ⊓ X) X :=
    CFSG.ABGLocalTools.isSylowOf_iff.mp hInf
  have hPleH : R ⊓ X ≤ H := inf_le_left.trans hR.1
  have hInf' : CFSG.ABGLocalTools.IsSylowOf 2 ((R ⊓ X).subgroupOf H) (X.subgroupOf H) := by
    refine (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff H).mp ?_
    rwa [Subgroup.map_subgroupOf_eq_of_le hPleH, Subgroup.map_subgroupOf_eq_of_le hXH]
  have hDsub_le : D.subgroupOf H ≤ X.subgroupOf H := by
    intro d hd
    rw [Subgroup.mem_subgroupOf] at hd ⊢
    exact hDX hd
  have hXsub_normal : (X.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXH).mpr hHnormX
  have hNormClosure_le :
      Subgroup.normalClosure (D.subgroupOf H : Set ↥H) ≤ X.subgroupOf H := by
    haveI := hXsub_normal
    exact Subgroup.normalClosure_le_normal hDsub_le
  have hNormClosure_ge :
      X.subgroupOf H ≤ Subgroup.normalClosure (D.subgroupOf H : Set ↥H) := by
    intro y hy
    have hyG : (y : G) ∈ X := Subgroup.mem_subgroupOf.mp hy
    have hgen : ∀ s ∈ {s : G | ∃ h ∈ H, s = h⁻¹ * t * h},
        s ∈ (Subgroup.normalClosure (D.subgroupOf H : Set ↥H)).map H.subtype := by
      rintro s ⟨h, hh, rfl⟩
      refine Subgroup.mem_map.mpr ⟨⟨h, hh⟩⁻¹ * ⟨t, htH⟩ * ⟨h, hh⟩, ?_, ?_⟩
      · have htmem : (⟨t, htH⟩ : ↥H) ∈ D.subgroupOf H := by
          rw [Subgroup.mem_subgroupOf]; exact htD
        have htmem' : (⟨t, htH⟩ : ↥H) ∈
            Subgroup.normalClosure (D.subgroupOf H : Set ↥H) :=
          Subgroup.le_normalClosure htmem
        exact (Subgroup.normalClosure_normal (s := (D.subgroupOf H : Set ↥H))).conj_mem'
          ⟨t, htH⟩ htmem' ⟨h, hh⟩
      · rfl
    have hXleMap :
        X ≤ (Subgroup.normalClosure (D.subgroupOf H : Set ↥H)).map H.subtype := by
      rw [hX, Subgroup.closure_le]
      exact hgen
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp (hXleMap hyG)
    have hzy' : z = y := Subtype.ext hzy
    rwa [hzy'] at hz
  have hNormClosure :
      Subgroup.normalClosure (D.subgroupOf H : Set ↥H) = X.subgroupOf H :=
    le_antisymm hNormClosure_le hNormClosure_ge
  have hDdih' : CFSG.ComponentClassification.AschbacherTheorem3.IsDihedralTwoGroup
      (D.subgroupOf H) := by
    obtain ⟨m, hm, ⟨e⟩⟩ := hdih
    refine ⟨m + 1, Nat.succ_le_succ hm, ?_⟩
    rw [Nat.add_sub_cancel]
    exact ⟨(Subgroup.subgroupOfEquivOfLe hDH).trans e⟩
  have h8' : 8 ≤ Nat.card ↥(D.subgroupOf H) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDH).toEquiv]
    exact h8
  have hcl' : ∀ x ∈ normalizer (D.subgroupOf H : Set ↥H), x ∉ D.subgroupOf H →
      orderOf x = 2 → ∀ d ∈ D.subgroupOf H, orderOf d = 2 →
      ∀ g : ↥H, g⁻¹ * x * g ≠ d := by
    intro x hxnorm hxnot hxord d hdmem hdord g h
    have hxnormG : (x : G) ∈ normalizer (D : Set G) := by
      have hmem : x ∈ (normalizer D).subgroupOf H := by
        rw [Subgroup.subgroupOf_normalizer_eq hDH]
        exact hxnorm
      exact Subgroup.mem_subgroupOf.mp hmem
    have hxnotD : (x : G) ∉ D := fun hxD => hxnot (Subgroup.mem_subgroupOf.mpr hxD)
    have hxordG : orderOf (x : G) = 2 := (Subgroup.orderOf_coe x).trans hxord
    have hdD : (d : G) ∈ D := Subgroup.mem_subgroupOf.mp hdmem
    have hdordG : orderOf (d : G) = 2 := (Subgroup.orderOf_coe d).trans hdord
    have heq : (g : G)⁻¹ * (x : G) * (g : G) = (d : G) := by
      simpa using congr_arg Subtype.val h
    exact hcl (x : G) x.2 hxnormG hxnotD hxordG (d : G) hdD hdordG (g : G) g.2 heq
  have hP' : CFSG.ABGLocalTools.IsSylowOf 2 ((R ⊓ X).subgroupOf H)
      (Subgroup.normalClosure (D.subgroupOf H : Set ↥H)) := by
    rw [hNormClosure]; exact hInf'
  have hφ : ↥((R ⊓ X).subgroupOf H) ≃* ↥(R ⊓ X) :=
    Subgroup.subgroupOfEquivOfLe hPleH
  have hDihSd : IsDihSd (R ⊓ X) := by
    rcases hB4 ↥H (D.subgroupOf H) hDdih' h8' hcl' ((R ⊓ X).subgroupOf H) hP' with
      ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
    · exact Or.inl ⟨n - 1, Nat.sub_le_sub_right hn 1, ⟨hφ.symm.trans e⟩⟩
    · exact Or.inr ⟨n, hn, ⟨hφ.symm.trans e⟩⟩
  exact ⟨R ⊓ X, hSylow2, hDihSd⟩

end CFSG.OddStandard.SmallF3.Omega
