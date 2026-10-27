module

public import CFSG.LocalAnalysis.EvenBN.Tits.Sec4Classes
public import CFSG.LocalAnalysis.EvenBN.Tits.Model.E32OrbitsTwo

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Sporadic.Schreier.Tits

namespace Data

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem Hyp.mem_normalizer_tSup_iff (hd : d.Hyp)
    {X : Subgroup (Equiv.Perm (Fin 1755))} (hXD : X ≤ titsD) {x : G}
    (hx : x ∈ centralizer ({d.t} : Set G)) :
    x ∈ normalizer ((d.liftSub X ⊔ zpowers d.t : Subgroup G) : Set G) ↔
      (d.ρ ⟨x, hx⟩ : Equiv.Perm (Fin 1755)) ∈ normalizer (X : Set (Equiv.Perm (Fin 1755))) := by
  set r : Equiv.Perm (Fin 1755) := ↑(d.ρ ⟨x, hx⟩) with hr
  have hXrD : X.map (MulAut.conj r).toMonoidHom ≤ titsD := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (Model.conj_mem_titsD_iff (d.ρ ⟨x, hx⟩).2 (titsD_le_titsA (hXD hy))).2 (hXD hy)
  have hxt : (zpowers d.t).map (MulAut.conj x).toMonoidHom = zpowers d.t := by
    rw [MonoidHom.map_zpowers]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [mem_centralizer_singleton_iff.1 hx, mul_inv_cancel_right]
  have hmap : (d.liftSub X ⊔ zpowers d.t).map (MulAut.conj x).toMonoidHom =
      d.liftSub (X.map (MulAut.conj r).toMonoidHom) ⊔ zpowers d.t := by
    rw [Subgroup.map_sup, hd.map_conj_liftSub hx hXD, hxt]
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.mem_normalizer_iff_map_conj_eq]
  change (d.liftSub X ⊔ zpowers d.t).map (MulAut.conj x).toMonoidHom = _ ↔
    X.map (MulAut.conj r).toMonoidHom = X
  rw [hmap]
  constructor
  · intro h
    apply d.liftSub_injective hXrD hXD
    apply le_antisymm
    · intro y hy
      have hy' : y ∈ d.liftSub X ⊔ zpowers d.t := h ▸ mem_sup_left hy
      exact (hd.tSup_facts (d.liftSub_le X)).2.1 y hy' (d.liftSub_le _ hy)
    · intro y hy
      have hy' : y ∈ d.liftSub (X.map (MulAut.conj r).toMonoidHom) ⊔ zpowers d.t :=
        h.symm ▸ mem_sup_left hy
      exact (hd.tSup_facts (d.liftSub_le _)).2.1 y hy' (d.liftSub_le _ hy)
  · intro h
    rw [h]

theorem Hyp.orbit_eq_lift_image
    (hd : d.Hyp) {X K : Subgroup (Equiv.Perm (Fin 1755))} (hXD : X ≤ titsD) (hKD : K ≤ titsD)
    (hKN : K ≤ normalizer (X : Set (Equiv.Perm (Fin 1755)))) {a : Equiv.Perm (Fin 1755)}
    (ha : a ∈ titsD) {S : Set (Equiv.Perm (Fin 1755))}
    (hS : ∀ r ∈ titsA ⊓ normalizer (X : Set (Equiv.Perm (Fin 1755))), r * a * r⁻¹ ∈ S)
    (hS' : ∀ s ∈ S, ∃ r ∈ K, r * a * r⁻¹ = s) :
    {y | ∃ x ∈ normalizer ((d.liftSub X ⊔ zpowers d.t : Subgroup G) : Set G) ⊓
        centralizer ({d.t} : Set G), x * d.lift a * x⁻¹ = y} = d.lift '' S := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hxN, hxC⟩ := mem_inf.1 hx
    have hρ := (hd.mem_normalizer_tSup_iff hXD hxC).1 hxN
    set r : Equiv.Perm (Fin 1755) := ↑(d.ρ ⟨x, hxC⟩) with hr
    have hrA : r ∈ titsA := (d.ρ ⟨x, hxC⟩).2
    have hraD : r * a * r⁻¹ ∈ titsD := (Model.conj_mem_titsD_iff hrA (titsD_le_titsA ha)).2 ha
    refine ⟨r * a * r⁻¹, hS r (mem_inf.2 ⟨hrA, hρ⟩), ?_⟩
    exact (hd.conj_lift_eq hxC ha hraD (by rw [hr]; group)).symm
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨r, hrK, rfl⟩ := hS' s hs
    have hrD : r ∈ titsD := hKD hrK
    have hrC : d.lift r ∈ centralizer ({d.t} : Set G) := hd.L_le (d.lift_mem r)
    have hρr : (d.ρ ⟨d.lift r, hrC⟩ : Equiv.Perm (Fin 1755)) = r := hd.ρ_lift hrD
    refine ⟨d.lift r, mem_inf.2 ⟨(hd.mem_normalizer_tSup_iff hXD hrC).2 (by
      rw [hρr]; exact hKN hrK), hrC⟩, ?_⟩
    rw [d.lift_conj hrD ha]

theorem parrottV_eleven_ne_titsZ
    : Model.parrottV 11 ≠ titsZ := fun h => by
  have := Model.eElt_injOn (a := 8) (b := 16) (by norm_num) (by norm_num)
    (by rw [Model.elt_values.2.2.1, Model.elt_values.2.1, h, Model.parrottV_twelve_eq])
  exact absurd this (by decide)

theorem Hyp.orbits_A
    (hd : d.Hyp) :
    d.z ∈ d.zL ∩ d.A ∧ (∀ x ∈ d.M ⊓ centralizer ({d.t} : Set G), x * d.z * x⁻¹ = d.z) ∧
      {y | ∃ x ∈ d.M ⊓ centralizer ({d.t} : Set G), x * d.pv 11 * x⁻¹ = y} =
        (d.zL ∩ d.A) \ {d.z} ∧ ((d.zL ∩ d.A) \ {d.z}).ncard = 10 ∧
      {y | ∃ x ∈ d.M ⊓ centralizer ({d.t} : Set G), x * d.pv 10 * x⁻¹ = y} = d.vL ∩ d.A ∧
      (d.vL ∩ d.A).ncard = 20 := by
  have hED : Model.hatE ≤ titsD := Model.hatE_le_titsJ.trans titsJ_le_titsD
  have hv11 : Model.parrottV 11 ∈ titsD := (Model.parrottV_mem_titsD_iff (by norm_num)).2
    (by decide)
  have hv10 : Model.parrottV 10 ∈ titsD := (Model.parrottV_mem_titsD_iff (by norm_num)).2
    (by decide)
  have hv11E : Model.parrottV 11 ∈ Model.hatE := by
    rw [← Model.elt_values.2.2.1]
    exact Model.eElt_mem (by norm_num)
  have hv10E : Model.parrottV 10 ∈ Model.hatE := by
    rw [← Model.elt_values.2.2.2.1]
    exact Model.eElt_mem (by norm_num)
  have hHN : titsH ≤ normalizer (Model.hatE : Set (Equiv.Perm (Fin 1755))) :=
    CFSG.Quasithin.le_extSub.trans Model.twoF4H_le_normalizer_hatE
  have hfix : ∀ r ∈ titsA ⊓ normalizer (Model.hatE : Set (Equiv.Perm (Fin 1755))),
      r * titsZ * r⁻¹ = titsZ := by
    intro r hr
    rw [Model.titsA_inf_normalizer_hatE] at hr
    rw [mem_centralizer_singleton_iff.1 (Model.twoF4H_le_centralizer_titsZ hr),
      mul_inv_cancel_right]
  obtain ⟨hlong, hlong10⟩ := Model.hatE_long
  obtain ⟨hshort, hshort20⟩ := Model.hatE_short
  have hzL : d.zL ∩ d.A = d.lift '' {x | x ∈ Model.hatE ∧ Model.IsLong x} :=
    (hd.zL_vL_inter hED).1
  have hvL : d.vL ∩ d.A = d.lift '' {x | x ∈ Model.hatE ∧ Model.IsShort x} :=
    (hd.zL_vL_inter hED).2
  have hzL' : (d.zL ∩ d.A) \ {d.z} =
      d.lift '' {e | e ∈ Model.hatE ∧ Model.IsLong e ∧ e ≠ titsZ} := by
    rw [hzL]
    ext y
    constructor
    · rintro ⟨⟨x, ⟨hx, hxl⟩, rfl⟩, hy⟩
      exact ⟨x, ⟨hx, hxl, fun h => hy (by rw [h, d.lift_titsZ]; rfl)⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hxl, hxz⟩, rfl⟩
      refine ⟨⟨x, ⟨hx, hxl⟩, rfl⟩, fun h => hxz ?_⟩
      rw [Set.mem_singleton_iff, ← d.lift_titsZ] at h
      exact d.lift_inj (hED hx) titsZ_mem_titsD h
  refine ⟨⟨⟨1, one_mem _, by group⟩, mem_sup_left (mem_liftSub.2 ⟨titsZ,
    Model.titsZ_mem_hatE, titsZ_mem_titsD, d.lift_titsZ⟩)⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨hxN, hxC⟩ := mem_inf.1 hx
    have hρ := (hd.mem_normalizer_tSup_iff hED hxC).1 hxN
    have h := hfix _ (mem_inf.2 ⟨(d.ρ ⟨x, hxC⟩).2, hρ⟩)
    rw [← d.lift_titsZ]
    exact hd.conj_lift_eq hxC titsZ_mem_titsD titsZ_mem_titsD (by
      calc (d.ρ ⟨x, hxC⟩ : Equiv.Perm (Fin 1755)) * titsZ =
          (d.ρ ⟨x, hxC⟩ : Equiv.Perm (Fin 1755)) * titsZ * (d.ρ ⟨x, hxC⟩ :
            Equiv.Perm (Fin 1755))⁻¹ * d.ρ ⟨x, hxC⟩ := by group
        _ = titsZ * d.ρ ⟨x, hxC⟩ := by rw [h])
  · rw [hzL', hlong]
    refine hd.orbit_eq_lift_image hED titsH_le_titsD hHN hv11 (fun r hr => ?_)
      (fun s hs => hs)
    obtain ⟨hrA, hrN⟩ := mem_inf.1 hr
    rw [← hlong]
    refine ⟨(mem_normalizer_iff.1 hrN _).1 hv11E, Model.isLong_parrottV_eleven.conj hrA,
      fun he => parrottV_eleven_ne_titsZ ?_⟩
    calc Model.parrottV 11 = r⁻¹ * (r * Model.parrottV 11 * r⁻¹) * r := by group
      _ = r⁻¹ * (r * titsZ * r⁻¹) * r := by rw [he, hfix r hr]
      _ = titsZ := by group
  · rw [hzL', d.ncard_lift_image (fun x hx => hED hx.1), hlong10]
  · rw [hvL, hshort]
    refine hd.orbit_eq_lift_image hED titsH_le_titsD hHN hv10 (fun r hr => ?_)
      (fun s hs => hs)
    obtain ⟨hrA, hrN⟩ := mem_inf.1 hr
    rw [← hshort]
    exact ⟨(mem_normalizer_iff.1 hrN _).1 hv10E, Model.isShort_parrottV_ten.conj hrA⟩
  · rw [hvL, d.ncard_lift_image (fun x hx => hED hx.1), hshort20]

theorem Hyp.orbits_B
    (hd : d.Hyp) :
    {y | ∃ x ∈ d.N ⊓ centralizer ({d.t} : Set G), x * d.z * x⁻¹ = y} = d.zL ∩ d.B ∧
      d.zL ∩ d.B = {d.z, d.pv 11, d.z * d.pv 11} ∧ (d.zL ∩ d.B).ncard = 3 ∧
      {y | ∃ x ∈ d.N ⊓ centralizer ({d.t} : Set G), x * d.pv 10 * x⁻¹ = y} ∪
          {y | ∃ x ∈ d.N ⊓ centralizer ({d.t} : Set G), x * d.pv 9 * x⁻¹ = y} =
        d.vL ∩ d.B ∧
      Disjoint {y | ∃ x ∈ d.N ⊓ centralizer ({d.t} : Set G), x * d.pv 10 * x⁻¹ = y}
        {y | ∃ x ∈ d.N ⊓ centralizer ({d.t} : Set G), x * d.pv 9 * x⁻¹ = y} ∧
      {y | ∃ x ∈ d.N ⊓ centralizer ({d.t} : Set G), x * d.pv 10 * x⁻¹ = y}.ncard = 4 ∧
      {y | ∃ x ∈ d.N ⊓ centralizer ({d.t} : Set G), x * d.pv 9 * x⁻¹ = y}.ncard = 24 := by
  have hFD : Model.parrottF ≤ titsD := Model.parrottF_le_titsD
  have hv9 : Model.parrottV 9 ∈ titsD := (Model.parrottV_mem_titsD_iff (by norm_num)).2
    (by decide)
  have hv10 : Model.parrottV 10 ∈ titsD := (Model.parrottV_mem_titsD_iff (by norm_num)).2
    (by decide)
  have hv11 : Model.parrottV 11 ∈ titsD := (Model.parrottV_mem_titsD_iff (by norm_num)).2
    (by decide)
  have hv9F : Model.parrottV 9 ∈ Model.parrottF := subset_closure ⟨9, by simp, rfl⟩
  have hv10F : Model.parrottV 10 ∈ Model.parrottF := subset_closure ⟨10, by simp, rfl⟩
  have hzF : titsZ ∈ Model.parrottF := by
    rw [← Model.parrottV_twelve_eq]
    exact subset_closure ⟨12, by simp, rfl⟩
  have hv10U : Model.parrottV 10 ∈ Model.parrottU 10 := subset_closure ⟨10, by norm_num, rfl⟩
  have hNN : titsN ≤ normalizer (Model.parrottF : Set (Equiv.Perm (Fin 1755))) :=
    CFSG.Quasithin.le_extSub.trans Model.twoF4N_le_normalizer_parrottF
  obtain ⟨hlong, hlong3, hlongc⟩ := Model.parrottF_long
  obtain ⟨hs10, hs10c⟩ := Model.parrottF_short_ten
  obtain ⟨hs9, hs9c⟩ := Model.parrottF_short_nine
  have hv9U : Model.parrottV 9 ∉ Model.parrottU 10 := by
    have h : Model.parrottV 9 ∈
        {f | ∃ n ∈ titsN, n * Model.parrottV 9 * n⁻¹ = f} := ⟨1, one_mem _, by group⟩
    rw [← hs9] at h
    exact h.2.2
  have hzL : d.zL ∩ d.B = d.lift '' {x | x ∈ Model.parrottF ∧ Model.IsLong x} :=
    (hd.zL_vL_inter hFD).1
  have hvL : d.vL ∩ d.B = d.lift '' {x | x ∈ Model.parrottF ∧ Model.IsShort x} :=
    (hd.zL_vL_inter hFD).2
  have hNU : ∀ r ∈ titsA ⊓ normalizer (Model.parrottF : Set (Equiv.Perm (Fin 1755))),
      r ∈ normalizer (Model.parrottU 10 : Set (Equiv.Perm (Fin 1755))) := fun r hr =>
    Model.twoF4N_le_normalizer_parrottU_ten (Model.titsA_inf_normalizer_parrottF ▸ hr)
  have hO10 : {y | ∃ x ∈ d.N ⊓ centralizer ({d.t} : Set G), x * d.pv 10 * x⁻¹ = y} =
      d.lift '' {f | f ∈ Model.parrottF ∧ Model.IsShort f ∧ f ∈ Model.parrottU 10} := by
    rw [hs10]
    refine hd.orbit_eq_lift_image hFD titsN_le_titsD hNN hv10 (fun r hr => ?_) (fun s hs => hs)
    obtain ⟨hrA, hrN⟩ := mem_inf.1 hr
    rw [← hs10]
    exact ⟨(mem_normalizer_iff.1 hrN _).1 hv10F, Model.isShort_parrottV_ten.conj hrA,
      (mem_normalizer_iff.1 (hNU r hr) _).1 hv10U⟩
  have hO9 : {y | ∃ x ∈ d.N ⊓ centralizer ({d.t} : Set G), x * d.pv 9 * x⁻¹ = y} =
      d.lift '' {f | f ∈ Model.parrottF ∧ Model.IsShort f ∧ f ∉ Model.parrottU 10} := by
    rw [hs9]
    refine hd.orbit_eq_lift_image hFD titsN_le_titsD hNN hv9 (fun r hr => ?_) (fun s hs => hs)
    obtain ⟨hrA, hrN⟩ := mem_inf.1 hr
    rw [← hs9]
    exact ⟨(mem_normalizer_iff.1 hrN _).1 hv9F, Model.isShort_parrottV_nine.conj hrA,
      fun h => hv9U ((mem_normalizer_iff.1 (hNU r hr) _).2 h)⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hzL, hlong, ← d.lift_titsZ]
    exact hd.orbit_eq_lift_image hFD titsN_le_titsD hNN titsZ_mem_titsD (fun r hr => by
      obtain ⟨hrA, hrN⟩ := mem_inf.1 hr
      rw [← hlong]
      exact ⟨(mem_normalizer_iff.1 hrN _).1 hzF, Model.isLong_titsZ.conj hrA⟩)
      (fun s hs => hs)
  · rw [hzL, hlong3, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton,
      d.lift_titsZ, d.lift_mul titsZ_mem_titsD hv11, d.lift_titsZ]
    rfl
  · rw [hzL, d.ncard_lift_image (fun x hx => hFD hx.1), hlongc]
  · rw [hO10, hO9, ← Set.image_union, hvL]
    congr 1
    ext f
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · rintro (⟨hf, hs, -⟩ | ⟨hf, hs, -⟩) <;> exact ⟨hf, hs⟩
    · rintro ⟨hf, hs⟩
      by_cases hU : f ∈ Model.parrottU 10
      · exact Or.inl ⟨hf, hs, hU⟩
      · exact Or.inr ⟨hf, hs, hU⟩
  · rw [hO10, hO9, Set.disjoint_left]
    rintro y ⟨f₁, ⟨hf₁, -, hU₁⟩, rfl⟩ ⟨f₂, ⟨hf₂, -, hU₂⟩, he⟩
    rw [d.lift_inj (hFD hf₂) (hFD hf₁) he] at hU₂
    exact hU₂ hU₁
  · rw [hO10, d.ncard_lift_image (fun x hx => hFD hx.1), hs10c]
  · rw [hO9, d.ncard_lift_image (fun x hx => hFD hx.1), hs9c]

end Data

end CFSG.LocalAnalysis.EvenBN.Tits
