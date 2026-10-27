module

public import CFSG.CGT.PushingUpLit.SolKR2.Pair

public section

namespace CFSG.CGT.PushingUpLit.SolKR2

open CFSG CFSG.RankThree.GF2n.Tim78
open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup)
open CFSG.RankThree.GF2n (conjSubgroup_mul conjSubgroup_one conjSubgroup_eq_self_iff
  card_conjSubgroup inSubgroup_pCore_two mem_normalizer_map_subtype_of_characteristic)

variable {G : Type} [Group G] [Finite G] {M B : Subgroup G}

namespace R2

variable (h : R2 M B)
include h

theorem exists_noncomm_delta_base {g : G}
    (hg : conjSubgroup g (omegaTwoSub B) ≤ Subgroup.centralizer (omegaTwoSub B : Set G))
    (hne : conjSubgroup g (omegaTwoSub B) ≠ omegaTwoSub B) :
    ∃ e : G, conjSubgroup e (omegaTwoSub B) ≤ Subgroup.centralizer (omegaTwoSub B : Set G) ∧
      ¬ ∀ a ∈ conjSubgroup e (omegaTwoSub B), ∀ b ∈ conjSubgroup g (omegaTwoSub B),
        a * b = b * a := by
  classical
  by_contra hcon
  have hcomm : ∀ e : G, conjSubgroup e (omegaTwoSub B) ≤
      Subgroup.centralizer (omegaTwoSub B : Set G) →
      ∀ a ∈ conjSubgroup e (omegaTwoSub B), ∀ b ∈ conjSubgroup g (omegaTwoSub B),
        a * b = b * a := fun e he a ha b hb => by
    by_contra hab
    exact hcon ⟨e, he, fun hall => hab (hall a ha b hb)⟩
  have H := h.s3hyp
  have : Finite (Subgroup G) :=
    Finite.of_injective (SetLike.coe : Subgroup G → Set G) SetLike.coe_injective
  set U := omegaTwoSub B with hU
  set Sg : Set (Subgroup G) := {E | (∃ k : G, E = conjSubgroup k U) ∧
    E ≤ Subgroup.centralizer (U : Set G)} with hSg
  have hstep : ∀ E ∈ Sg, conjSubgroup g⁻¹ E ∈ Sg := by
    rintro E ⟨⟨k, rfl⟩, hE⟩
    refine ⟨⟨g⁻¹ * k, (conjSubgroup_mul _ _ _).symm⟩, fun z hz => ?_⟩
    rw [mem_conjSubgroup, inv_inv] at hz
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hgu : g * u * g⁻¹ ∈ conjSubgroup g U := by
      rw [mem_conjSubgroup, show g⁻¹ * (g * u * g⁻¹) * g = u by group]
      exact hu
    have h1 := hcomm k hE _ hz _ hgu
    calc u * z = g⁻¹ * ((g * u * g⁻¹) * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * (g * u * g⁻¹)) * g := by rw [h1]
      _ = z * u := by group
  let f : ↥Sg → ↥Sg := fun D => ⟨conjSubgroup g⁻¹ D, hstep D D.2⟩
  have hf : Function.Injective f := by
    intro D D' hDD
    have h1 : conjSubgroup g⁻¹ (D : Subgroup G) = conjSubgroup g⁻¹ D' := congrArg Subtype.val hDD
    have h2 := congrArg (conjSubgroup g) h1
    rw [← conjSubgroup_mul, ← conjSubgroup_mul, mul_inv_cancel, conjSubgroup_one,
      conjSubgroup_one] at h2
    exact Subtype.ext h2
  have hsurj := Finite.injective_iff_surjective.mp hf
  have hstep' : ∀ E ∈ Sg, conjSubgroup g E ∈ Sg := fun E hE => by
    obtain ⟨⟨E', hE'⟩, he⟩ := hsurj ⟨E, hE⟩
    have e : conjSubgroup g⁻¹ E' = E := congrArg Subtype.val he
    rw [← e, ← conjSubgroup_mul, mul_inv_cancel, conjSubgroup_one]
    exact hE'
  set R := ⨆ D : ↥Sg, (D : Subgroup G) with hRdef
  have hnormR : ∀ x : G, (∀ D ∈ Sg, conjSubgroup x D ∈ Sg) →
      x ∈ Subgroup.normalizer (R : Set G) := by
    intro x hx
    rw [← conjSubgroup_eq_self_iff]
    refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [card_conjSubgroup])
    rw [conjSubgroup, Subgroup.map_le_iff_le_comap]
    refine iSup_le fun D => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_iSup (fun D : ↥Sg => (D : Subgroup G)) ⟨_, hx D D.2⟩
  have hgR : g ∈ Subgroup.normalizer (R : Set G) := hnormR g hstep'
  have hMR : M ≤ Subgroup.normalizer (R : Set G) := fun m hm => hnormR m fun D hD => by
    obtain ⟨⟨k, rfl⟩, hDc⟩ := hD
    refine ⟨⟨m * k, (conjSubgroup_mul _ _ _).symm⟩, fun z hz => ?_⟩
    rw [mem_conjSubgroup] at hz
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hu' : m⁻¹ * u * m ∈ U := by
      have := (Subgroup.mem_normalizer_iff.mp (h.normalizer_U.ge (M.inv_mem hm)) u).mp hu
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp (hDc hz) _ hu'
    calc u * z = m * ((m⁻¹ * u * m) * (m⁻¹ * z * m)) * m⁻¹ := by group
      _ = m * ((m⁻¹ * z * m) * (m⁻¹ * u * m)) * m⁻¹ := by rw [h1]
      _ = z * u := by group
  set V := conjSubgroup g U with hV
  have hVSg : V ∈ Sg := ⟨⟨g, rfl⟩, hg⟩
  have hVR : V ≤ R := le_iSup (fun D : ↥Sg => (D : Subgroup G)) ⟨V, hVSg⟩
  have hRV : R ≤ Subgroup.normalizer (V : Set G) := by
    refine iSup_le fun D => ?_
    obtain ⟨⟨k, hk⟩, hDc⟩ := D.2
    intro d hd
    refine Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun c hc => ?_)
    rw [hk] at hd hDc
    exact (hcomm k hDc d hd c hc).symm
  have hV2 : IsPGroup 2 V := (Pair.isPGroup_U h).map (MulAut.conj g).toMonoidHom
  have hVO : V ≤ inSubgroup (pCore 2) R := le_inSubgroup_pCore hVR hRV hV2
  have hV1 : V ≠ ⊥ := by
    intro hbot
    have := Pair.card_conj_U h g
    rw [← hV, hbot, Subgroup.card_bot] at this
    omega
  have hO1 : inSubgroup (pCore 2) R ≠ ⊥ := fun hbot => hV1 (by rw [eq_bot_iff, ← hbot]; exact hVO)
  have hMO : M ≤ Subgroup.normalizer ((inSubgroup (pCore 2) R : Subgroup G) : Set G) :=
    fun m hm => mem_normalizer_map_subtype_of_characteristic (hMR hm) (pCore 2 R)
  have hNO := H.normalizer_eq_of hO1 (inSubgroup_pCore_two R).1 hMO
  have hgM : g ∈ M := by
    rw [← hNO]
    exact mem_normalizer_map_subtype_of_characteristic hgR (pCore 2 R)
  exact hne (conjSubgroup_eq_self_iff.mpr (H.normal hgM))

theorem exists_noncomm_delta {f g' : G}
    (hg : conjSubgroup g' (omegaTwoSub B) ≤
      Subgroup.centralizer (conjSubgroup f (omegaTwoSub B) : Set G))
    (hne : conjSubgroup g' (omegaTwoSub B) ≠ conjSubgroup f (omegaTwoSub B)) :
    ∃ e : G, conjSubgroup e (omegaTwoSub B) ≤
        Subgroup.centralizer (conjSubgroup f (omegaTwoSub B) : Set G) ∧
      ¬ ∀ a ∈ conjSubgroup e (omegaTwoSub B), ∀ b ∈ conjSubgroup g' (omegaTwoSub B),
        a * b = b * a := by
  have hfg : conjSubgroup g' (omegaTwoSub B) = conjSubgroup f (conjSubgroup (f⁻¹ * g')
      (omegaTwoSub B)) := by rw [← conjSubgroup_mul, mul_inv_cancel_left]
  have hg0 : conjSubgroup (f⁻¹ * g') (omegaTwoSub B) ≤
      Subgroup.centralizer (omegaTwoSub B : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hx' : f * x * f⁻¹ ∈ conjSubgroup g' (omegaTwoSub B) := by
      rw [hfg, mem_conjSubgroup, show f⁻¹ * (f * x * f⁻¹) * f = x by group]
      exact hx
    have hu' : f * u * f⁻¹ ∈ conjSubgroup f (omegaTwoSub B) := by
      rw [mem_conjSubgroup, show f⁻¹ * (f * u * f⁻¹) * f = u by group]
      exact hu
    have h1 := Subgroup.mem_centralizer_iff.mp (hg hx') _ hu'
    calc u * x = f⁻¹ * ((f * u * f⁻¹) * (f * x * f⁻¹)) * f := by group
      _ = f⁻¹ * ((f * x * f⁻¹) * (f * u * f⁻¹)) * f := by rw [h1]
      _ = x * u := by group
  have hne0 : conjSubgroup (f⁻¹ * g') (omegaTwoSub B) ≠ omegaTwoSub B := fun he =>
    hne (by rw [hfg, he])
  obtain ⟨e₀, he₀, hnc⟩ := h.exists_noncomm_delta_base hg0 hne0
  refine ⟨f * e₀, ?_, fun hall => hnc fun a ha b hb => ?_⟩
  · intro z hz
    rw [conjSubgroup_mul, mem_conjSubgroup] at hz
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hu' : f⁻¹ * u * f ∈ omegaTwoSub B := mem_conjSubgroup.mp hu
    have h1 := Subgroup.mem_centralizer_iff.mp (he₀ hz) _ hu'
    calc u * z = f * ((f⁻¹ * u * f) * (f⁻¹ * z * f)) * f⁻¹ := by group
      _ = f * ((f⁻¹ * z * f) * (f⁻¹ * u * f)) * f⁻¹ := by rw [h1]
      _ = z * u := by group
  · have ha' : f * a * f⁻¹ ∈ conjSubgroup (f * e₀) (omegaTwoSub B) := by
      rw [conjSubgroup_mul, mem_conjSubgroup, show f⁻¹ * (f * a * f⁻¹) * f = a by group]
      exact ha
    have hb' : f * b * f⁻¹ ∈ conjSubgroup g' (omegaTwoSub B) := by
      rw [hfg, mem_conjSubgroup, show f⁻¹ * (f * b * f⁻¹) * f = b by group]
      exact hb
    have h1 := hall _ ha' _ hb'
    calc a * b = f⁻¹ * ((f * a * f⁻¹) * (f * b * f⁻¹)) * f := by group
      _ = f⁻¹ * ((f * b * f⁻¹) * (f * a * f⁻¹)) * f := by rw [h1]
      _ = b * a := by group

end R2

end CFSG.CGT.PushingUpLit.SolKR2
