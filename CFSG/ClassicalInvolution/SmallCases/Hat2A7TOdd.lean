module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7TTwoTight

public section

namespace CFSG.ClassicalInvolution.Hat2A7T

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Hat2A7

section Index

variable {F : Type*} [Group F] [Finite F]

theorem exists_conj_ge_of_odd_relIndex {C N : Subgroup F} (hodd : Odd (N.relIndex C))
    {R : Subgroup F} (hRC : R ≤ C) (hR2 : IsPGroup 2 R) :
    ∃ c ∈ C, ∀ r ∈ R, c⁻¹ * r * c ∈ N := by
  let N' : Subgroup ↥C := N.subgroupOf C
  let R' : Subgroup ↥C := R.subgroupOf C
  have hR'2 : IsPGroup 2 ↥R' := hR2.comap_subtype
  have hcard : Nat.card (↥C ⧸ N') = N.relIndex C := rfl
  have hmod := hR'2.card_modEq_card_fixedPoints (↥C ⧸ N')
  have hne : Nat.card (MulAction.fixedPoints ↥R' (↥C ⧸ N')) ≠ 0 := by
    intro h0
    rw [h0, hcard] at hmod
    have h2 : 2 ∣ N.relIndex C := Nat.modEq_zero_iff_dvd.mp hmod
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  obtain ⟨⟨q, hq⟩⟩ := (Nat.card_pos_iff.mp (Nat.pos_of_ne_zero hne)).1
  induction q using QuotientGroup.induction_on with
  | H c =>
    refine ⟨c, c.2, fun r hr => ?_⟩
    have h1 := MulAction.mem_fixedPoints.mp hq ⟨⟨r, hRC hr⟩, hr⟩
    have h2 : (((⟨r, hRC hr⟩ : ↥C) * c : ↥C) : ↥C ⧸ N') = (c : ↥C ⧸ N') := h1
    have h3 := QuotientGroup.eq.mp h2
    have h5 : ((((⟨r, hRC hr⟩ : ↥C) * c)⁻¹ * c : ↥C) : F) ∈ N := h3
    have h6 : (c : F)⁻¹ * r⁻¹ * c ∈ N := by
      have : (((⟨r, hRC hr⟩ : ↥C) * c)⁻¹ * c : ↥C) = (c⁻¹ * ⟨r, hRC hr⟩⁻¹ * c : ↥C) := by group
      rw [this] at h5
      simpa using h5
    have := N.inv_mem h6
    simpa [mul_assoc] using this

end Index

section Odd

variable {F : Type} [Group F] [Finite F]

theorem twoTightClass_of_odd_relIndex {K : Subgroup F} {z : F} (hK : IsClassical2A7 ⊤ K z)
    (hodd : Odd ((Subgroup.centralizer ({z} : Set F) ⊓ Subgroup.normalizer (K : Set F)).relIndex
      (Subgroup.centralizer ({z} : Set F)))) : TwoTightClass K := by
  intro w L hL ⟨g, hLg⟩ R hRC hR2
  have hLc : IsClassical2A7 ⊤ (K.map (MulAut.conj g).toMonoidHom) (g * z * g⁻¹) :=
    isClassical2A7_map_conj hK g
  rw [← hLg] at hLc
  have hwz : g * z * g⁻¹ = w :=
    hL.eq_of_orderOf_eq_two (hLg ▸ hLc.mem) hLc.orderOf_eq_two
  set C : Subgroup F := Subgroup.centralizer ({z} : Set F) with hCdef
  set R₀ : Subgroup F := R.map (MulAut.conj g⁻¹).toMonoidHom with hR₀
  have hR₀C : R₀ ≤ C := by
    rintro _ ⟨r, hr, rfl⟩
    rw [hCdef, Subgroup.mem_centralizer_singleton_iff]
    have h1 : r * w = w * r := Subgroup.mem_centralizer_singleton_iff.mp (hRC hr)
    show g⁻¹ * r * g⁻¹⁻¹ * z = z * (g⁻¹ * r * g⁻¹⁻¹)
    rw [← hwz] at h1
    calc g⁻¹ * r * g⁻¹⁻¹ * z = g⁻¹ * (r * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * r) * g := by rw [h1]
      _ = z * (g⁻¹ * r * g⁻¹⁻¹) := by group
  obtain ⟨c, hcC, hc⟩ := exists_conj_ge_of_odd_relIndex hodd hR₀C (hR2.map _)
  have hcz : c * z * c⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hcC
    rw [this]
    group
  have hLw : IsClassical2A7 ⊤ (K.map (MulAut.conj (g * c)).toMonoidHom) w := by
    have h1 := isClassical2A7_map_conj hK (g * c)
    have h2 : g * c * z * (g * c)⁻¹ = w :=
      calc g * c * z * (g * c)⁻¹ = g * (c * z * c⁻¹) * g⁻¹ := by group
        _ = g * z * g⁻¹ := by rw [hcz]
        _ = w := hwz
    rwa [h2] at h1
  refine ⟨_, hLw, ⟨g * c, rfl⟩, fun r hr => ?_⟩
  have hm : (g * c)⁻¹ * r * (g * c) ∈ Subgroup.normalizer (K : Set F) := by
    have h1 := (hc (g⁻¹ * r * g) ⟨r, hr, by simp⟩).2
    have h2 : c⁻¹ * (g⁻¹ * r * g) * c = (g * c)⁻¹ * r * (g * c) := by group
    rwa [h2] at h1
  rw [← map_conj_eq_iff_mem_normalizer, map_map_conj]
  have h3 : r * (g * c) = (g * c) * ((g * c)⁻¹ * r * (g * c)) := by group
  rw [h3, ← map_map_conj, map_conj_eq_iff_mem_normalizer.mpr hm]

theorem commOrEq_of_odd_relIndex (hZ : CenterTrivial F) (IH : ClassicalCommuteBelow F)
    (P1 : ClassicalQuasisimple F) {K : Subgroup F} {z : F} (hK : IsClassical2A7 ⊤ K z)
    (hodd : Odd ((Subgroup.centralizer ({z} : Set F) ⊓ Subgroup.normalizer (K : Set F)).relIndex
      (Subgroup.centralizer ({z} : Set F)))) {g : F}
    (hg : (g * z * g⁻¹) * z = z * (g * z * g⁻¹)) :
    CommOrEq K (K.map (MulAut.conj g).toMonoidHom) :=
  commOrEq_of_twoTight hZ IH P1 hK (twoTightClass_of_odd_relIndex hK hodd) hg

theorem false_of_odd_twins_of_cliqueInv_subsingleton [IsSimpleGroup F]
    (hnab : ∃ a b : F, a * b ≠ b * a) (IH : ClassicalCommuteBelow F) (P1 : ClassicalQuasisimple F)
    {K : Subgroup F} {z : F} (hK : IsClassical2A7 ⊤ K z)
    (hodd : Odd ((Subgroup.centralizer ({z} : Set F) ⊓ Subgroup.normalizer (K : Set F)).relIndex
      (Subgroup.centralizer ({z} : Set F))))
    (hcl : ∀ u ∈ cliqueInv K, u = z) : False :=
  false_of_noBadPair_of_cliqueInv_subsingleton hnab hK
    (fun _ hg => commOrEq_of_odd_relIndex (fun x hx => Hat2A7.center_trivial_of_simple hnab x hx)
      IH P1 hK hodd hg) hcl

end Odd

end CFSG.ClassicalInvolution.Hat2A7T
