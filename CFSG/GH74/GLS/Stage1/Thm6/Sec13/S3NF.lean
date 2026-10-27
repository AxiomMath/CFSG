module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.S3Norm
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Grow
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.S3Orbit

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

theorem sq_le_of_relIndex_le_two {P K : Subgroup G} (h2 : K.relIndex P ≤ 2)
    (h0 : K.relIndex P ≠ 0) : sq P ≤ K := by
  have hsq : ∀ a ∈ P, a * a ∈ K := by
    intro a ha
    have h12 : K.relIndex P = 1 ∨ K.relIndex P = 2 := by omega
    rcases h12 with h1 | h2'
    · rw [relIndex_eq_one] at h1
      exact K.mul_mem (h1 ha) (h1 ha)
    · have hidx : (K.subgroupOf P).index = 2 := h2'
      have := Subgroup.mul_self_mem_of_index_two hidx ⟨a, ha⟩
      exact (mem_subgroupOf.1 this)
  unfold sq
  rw [closure_le]
  rintro _ ⟨h, hh, rfl⟩
  exact hsq h hh

namespace Ctx3

variable {x : G} {T V H : Subgroup G} {f : G} {D : Subgroup G} (c : Ctx3 G x T V H f)
include c

theorem normal_four_le_H0 [Finite G] (h9 : IG_9_16) (hD : DData V (Hzero H f) D)
    (hVsq : V ≤ sq (Hzero H f)) {W : Subgroup G} (hW : IsFourGroup W) (hWS : W ≤ H ⊔ T)
    (hWn : ∀ s ∈ H ⊔ T, ∀ w ∈ W, s * w * s⁻¹ ∈ W) : W ≤ Hzero H f := by
  intro w hwW
  by_contra hwP
  have hwS : w ∈ H ⊔ T := hWS hwW
  have hnormP := c.Hstar_norm_H0 h9 hD
  have hZ1lt : W ⊓ Hzero H f < W := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro h
    apply hwP
    have : w ∈ W ⊓ Hzero H f := by rw [h]; exact hwW
    exact this.2
  have hZ1card : Nat.card ↥(W ⊓ Hzero H f) ≤ 2 := by
    have h1 := Subgroup.card_lt_of_lt hZ1lt
    have h2 : Nat.card ↥(W ⊓ Hzero H f) ∣ 4 := by
      have := Subgroup.card_dvd_of_le (inf_le_left : W ⊓ Hzero H f ≤ W)
      rwa [hW.2] at this
    have h3 : Nat.card ↥(W ⊓ Hzero H f) ≠ 3 := by
      intro h
      rw [h] at h2
      norm_num at h2
    rw [hW.2] at h1
    omega
  have hZ1norm : ∀ s ∈ H ⊔ T, ∀ z ∈ W ⊓ Hzero H f, s * z * s⁻¹ ∈ W ⊓ Hzero H f :=
    fun s hs z hz => ⟨hWn s hs z hz.1, hnormP s hs z hz.2⟩
  have hZ1cent := central_of_card_le_two hZ1card hZ1norm
  have hcls : cls (Hzero H f) w ⊆ (fun z => z * w) '' ((W ⊓ Hzero H f : Subgroup G) : Set G) := by
    rintro _ ⟨h, hh, rfl⟩
    refine ⟨h * w * h⁻¹ * w⁻¹, ⟨?_, ?_⟩, by show h * w * h⁻¹ * w⁻¹ * w = h * w * h⁻¹; group⟩
    · have h1 : h * w * h⁻¹ ∈ W := hWn h (Subgroup.mem_sup_left (c.H0_le hh)) w hwW
      exact W.mul_mem h1 (W.inv_mem hwW)
    · have h1 : w * h⁻¹ * w⁻¹ ∈ Hzero H f := hnormP w hwS h⁻¹ ((Hzero H f).inv_mem hh)
      have e : h * w * h⁻¹ * w⁻¹ = h * (w * h⁻¹ * w⁻¹) := by group
      rw [e]
      exact (Hzero H f).mul_mem hh h1
  have hclscard : Nat.card (cls (Hzero H f) w) ≤ 2 := by
    have h1 : Nat.card (cls (Hzero H f) w) = (cls (Hzero H f) w).ncard :=
      (Nat.card_coe_set_eq _).symm
    have h2 : (cls (Hzero H f) w).ncard ≤
        ((fun z => z * w) '' ((W ⊓ Hzero H f : Subgroup G) : Set G)).ncard :=
      Set.ncard_le_ncard hcls (Set.toFinite _)
    have h3 : ((fun z => z * w) '' ((W ⊓ Hzero H f : Subgroup G) : Set G)).ncard ≤
        ((W ⊓ Hzero H f : Subgroup G) : Set G).ncard := Set.ncard_image_le (Set.toFinite _)
    have h4 : ((W ⊓ Hzero H f : Subgroup G) : Set G).ncard = Nat.card ↥(W ⊓ Hzero H f) :=
      Nat.card_coe_set_eq _
    omega
  have horb := card_cls_mul' (Hzero H f) w
  have hKpos : 0 < Nat.card ↥(Hzero H f ⊓ centralizer ({w} : Set G)) := Nat.card_pos
  have hKcard : Nat.card (Hzero H f) ≤ 2 * Nat.card ↥(Hzero H f ⊓ centralizer ({w} : Set G)) := by
    calc Nat.card (Hzero H f) = Nat.card (cls (Hzero H f) w) *
          Nat.card ↥(Hzero H f ⊓ centralizer ({w} : Set G)) := horb.symm
      _ ≤ 2 * Nat.card ↥(Hzero H f ⊓ centralizer ({w} : Set G)) := Nat.mul_le_mul_right _ hclscard
  by_cases hwH : w ∈ H
  ·
    obtain ⟨-, hP4⟩ := c.card_cenMod_w_le h9 hD.le_V hD.comm hwH hwP
    have hsub : Hzero H f ⊓ centralizer ({w} : Set G) ≤
        Hzero H f ⊓ cenMod H D w (c.D_norm hD.le_V) := by
      rintro g ⟨hgP, hgC⟩
      refine ⟨hgP, c.H0_le hgP, ?_⟩
      have := mem_centralizer_iff.1 hgC w rfl
      have e : w * g * w⁻¹ * g⁻¹ = 1 := by
        calc w * g * w⁻¹ * g⁻¹ = (g * w) * w⁻¹ * g⁻¹ := by rw [this]
          _ = 1 := by group
      rw [e]
      exact D.one_mem
    have h1 := Subgroup.card_le_of_le hsub
    have h3 := hD.card
    have hDpos : 0 < Nat.card D := Nat.card_pos
    omega
  ·
    have hKP : Hzero H f ⊓ centralizer ({w} : Set G) ≤ Hzero H f := inf_le_left
    have hrel := relIndex_mul_card (Hzero H f ⊓ centralizer ({w} : Set G)) (Hzero H f)
    rw [inf_of_le_left hKP] at hrel
    have hrel2 : (Hzero H f ⊓ centralizer ({w} : Set G)).relIndex (Hzero H f) ≤ 2 := by
      by_contra hgt
      have hgt' : 3 ≤ (Hzero H f ⊓ centralizer ({w} : Set G)).relIndex (Hzero H f) := by omega
      have := Nat.mul_le_mul_right (Nat.card ↥(Hzero H f ⊓ centralizer ({w} : Set G))) hgt'
      omega
    have hrel0 : (Hzero H f ⊓ centralizer ({w} : Set G)).relIndex (Hzero H f) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hrel
      have : 0 < Nat.card (Hzero H f) := Nat.card_pos
      omega
    have hsqK := sq_le_of_relIndex_le_two hrel2 hrel0
    have hVK : V ≤ Hzero H f ⊓ centralizer ({w} : Set G) := hVsq.trans hsqK
    have hwC : w ∈ centralizer (V : Set G) := by
      rw [mem_centralizer_iff]
      intro v hv
      have := mem_centralizer_iff.1 (hVK hv).2 w rfl
      exact this.symm
    have : w ∈ (H ⊔ T) ⊓ centralizer (V : Set G) := ⟨hwS, hwC⟩
    rw [c.Hstar_inf_C] at this
    exact hwH this

theorem normal_four_eq_V [Finite G] (h9 : IG_9_16) (hD : DData V (Hzero H f) D)
    (hVsq : V ≤ sq (Hzero H f))
    (hQ : ∀ w ∈ Hzero H f, w * w = 1 → w ∉ V → ∀ z ∈ V, ∃ h ∈ Hzero H f, ⁅w, h⁆ = z)
    {W : Subgroup G} (hW : IsFourGroup W) (hWS : W ≤ H ⊔ T)
    (hWn : ∀ s ∈ H ⊔ T, ∀ w ∈ W, s * w * s⁻¹ ∈ W) : W = V := by
  have hWP := c.normal_four_le_H0 h9 hD hVsq hW hWS hWn
  by_contra hne
  have hWV : ¬ W ≤ V := by
    intro h
    exact hne (Subgroup.eq_of_le_of_card_ge h (le_of_eq (by rw [hW.2, c.out.V_four.2])))
  obtain ⟨w, hwW, hwV⟩ := IsConcreteLE.not_le_iff_exists.1 hWV
  have hwP : w ∈ Hzero H f := hWP hwW
  have hw2 : w * w = 1 := (hW.1 w hwW).1
  have hVW : V ≤ W := by
    intro z hz
    obtain ⟨h, hh, hwh⟩ := hQ w hwP hw2 hwV z hz
    have h1 : h * w⁻¹ * h⁻¹ ∈ W := hWn h (Subgroup.mem_sup_left (c.H0_le hh)) w⁻¹ (W.inv_mem hwW)
    have h2 : w * (h * w⁻¹ * h⁻¹) ∈ W := W.mul_mem hwW h1
    have e : w * (h * w⁻¹ * h⁻¹) = ⁅w, h⁆ := by
      simp only [commutatorElement_def]; group
    rw [e, hwh] at h2
    exact h2
  have heq : V = W := Subgroup.eq_of_le_of_card_ge hVW (le_of_eq (by rw [hW.2, c.out.V_four.2]))
  exact hwV (heq ▸ hwW)

theorem Hstar_sylow_top [Finite G] (h9 : IG_9_16) (hD : DData V (Hzero H f) D)
    (hVsq : V ≤ sq (Hzero H f))
    (hQ : ∀ w ∈ Hzero H f, w * w = 1 → w ∉ V → ∀ z ∈ V, ∃ h ∈ Hzero H f, ⁅w, h⁆ = z) :
    Sylow2In (H ⊔ T) ⊤ := by
  obtain ⟨S', hS', hSS'⟩ := SylowIn.exists_ge (p := 2) (le_top : H ⊔ T ≤ ⊤) c.Hstar_two
  have hS'2 : IsPGroup 2 ↥S' := hS'.isPGroup
  have hEq : H ⊔ T = S' := by
    by_contra hne
    have hlt : H ⊔ T < S' := lt_of_le_of_ne hSS' hne
    obtain ⟨d, hdS', hdS, hdN⟩ := exists_mem_normalizer_not_mem hS'2 hlt
    have hdn : ∀ s ∈ H ⊔ T, d * s * d⁻¹ ∈ H ⊔ T := fun s hs => (mem_normalizer_iff.1 hdN s).1 hs
    have hdn' : ∀ s ∈ H ⊔ T, d⁻¹ * s * d ∈ H ⊔ T := by
      intro s hs
      have := (mem_normalizer_iff.1 hdN (d⁻¹ * s * d)).2
      have e : d * (d⁻¹ * s * d) * d⁻¹ = s := by group
      rw [e] at this
      exact this hs
    have hVS : V ≤ H ⊔ T := c.out.V_le.trans le_sup_right
    have hfour : IsFourGroup (cj d V) := by
      refine ⟨fun a ha => ?_, by rw [card_cj]; exact c.out.V_four.2⟩
      have hv : d⁻¹ * a * d ∈ V := mem_cj.1 ha
      refine ⟨?_, fun b hb => ?_⟩
      · have h1 := c.out.V_sq hv
        have : a * a = d * ((d⁻¹ * a * d) * (d⁻¹ * a * d)) * d⁻¹ := by group
        rw [this, h1]; group
      · have hv' : d⁻¹ * b * d ∈ V := mem_cj.1 hb
        have h1 := c.out.V_comm hv hv'
        calc a * b = d * ((d⁻¹ * a * d) * (d⁻¹ * b * d)) * d⁻¹ := by group
          _ = d * ((d⁻¹ * b * d) * (d⁻¹ * a * d)) * d⁻¹ := by rw [h1]
          _ = b * a := by group
    have hcjS : cj d V ≤ H ⊔ T := by
      intro a ha
      have hv : d⁻¹ * a * d ∈ V := mem_cj.1 ha
      have := hdn _ (hVS hv)
      have e : d * (d⁻¹ * a * d) * d⁻¹ = a := by group
      rw [e] at this
      exact this
    have hcjn : ∀ s ∈ H ⊔ T, ∀ a ∈ cj d V, s * a * s⁻¹ ∈ cj d V := by
      intro s hs a ha
      rw [mem_cj] at ha ⊢
      have hs' := hdn' s hs
      have hv := mem_normalizer_iff.1 (c.Hstar_le_N hs') (d⁻¹ * a * d)
      have e : d⁻¹ * (s * a * s⁻¹) * d = (d⁻¹ * s * d) * (d⁻¹ * a * d) * (d⁻¹ * s * d)⁻¹ := by group
      rw [e]
      exact (hv.1 ha)
    have hVeq := c.normal_four_eq_V h9 hD hVsq hQ hfour hcjS hcjn
    have hdNV : d ∈ normalizer (V : Set G) := by
      rw [mem_normalizer_iff]
      intro v
      constructor
      · intro hv
        have : d * v * d⁻¹ ∈ cj d V := by
          rw [mem_cj]
          have e : d⁻¹ * (d * v * d⁻¹) * d = v := by group
          rw [e]; exact hv
        rwa [hVeq] at this
      · intro hv
        have : d * v * d⁻¹ ∈ cj d V := by rw [hVeq]; exact hv
        have h2 := mem_cj.1 this
        have e : d⁻¹ * (d * v * d⁻¹) * d = v := by group
        rwa [e] at h2
    have hle : H ⊔ T ⊔ zpowers d ≤ S' := sup_le hSS' ((zpowers_le).2 hdS')
    have hp2 : IsPGroup 2 ↥(H ⊔ T ⊔ zpowers d) := hS'2.to_le hle
    have hleN : H ⊔ T ⊔ zpowers d ≤ normalizer (V : Set G) :=
      sup_le c.Hstar_le_N ((zpowers_le).2 hdNV)
    have hEq' := eq_of_sylow_le c.hp.Hstar_sylow hleN le_sup_left hp2
    apply hdS
    rw [← hEq']
    exact Subgroup.mem_sup_right (mem_zpowers d)
  rw [hEq]
  exact hS'

end Ctx3

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
