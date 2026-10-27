module

public import CFSG.GH74.Uniqueness.SU.SU13TA9Trans9

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU13.TB

variable {G : Type} [Group G] [Finite G] {z : G}

theorem NHE_map (E : Subgroup (Hc z)) :
    NHE (E.map (incl z)) z = (NHE E (zH z)).map (incl z) := by
  ext g
  constructor
  · rintro ⟨hgN, hgC⟩
    have hgz : g * z = z * g := Subgroup.mem_centralizer_singleton_iff.mp hgC
    let γ : Hc z := ⟨g, Subgroup.mem_centralizer_singleton_iff.mpr hgz⟩
    refine ⟨γ, ⟨?_, Subgroup.mem_centralizer_singleton_iff.mpr (mul_zH γ)⟩, rfl⟩
    refine Subgroup.mem_normalizer_fintype (fun n hn => ?_)
    have h1 : incl z (γ * n * γ⁻¹) ∈ E.map (incl z) :=
      (Subgroup.mem_normalizer_iff.mp hgN (incl z n)).mp ⟨n, hn, rfl⟩
    exact (Subgroup.mem_map_iff_mem incl_injective).mp h1
  · rintro ⟨γ, ⟨hγN, hγC⟩, rfl⟩
    refine ⟨?_, Subgroup.mem_centralizer_singleton_iff.mpr (coe_mul_z γ)⟩
    refine Subgroup.mem_normalizer_fintype (fun n hn => ?_)
    obtain ⟨x, hx, rfl⟩ := (show n ∈ E.map (incl z) from hn)
    have hmem : γ * x * γ⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hγN x).mp hx
    exact ⟨γ * x * γ⁻¹, hmem, by simp [incl_apply]⟩

@[expose] noncomputable def EPart9.transfer {e : Elts (Hc z) (zH z)} {e9 : Elts9 (zH z) e}
    {f : FPart (zH z) e} (p : EPart9 (zH z) e e9 f) :
    EPart9 z e.transfer e9.transfer f.transfer where
  E := p.E.map (incl z)
  Es := p.Es.map (incl z)
  D := p.D.map (incl z)
  S₂ := p.S₂.map (incl z)
  r := (p.r : G)
  s₁_mem := ⟨e.s₁, p.s₁_mem, rfl⟩
  s₂_mem := ⟨e.s₂, p.s₂_mem, rfl⟩
  s₄_mem := ⟨e9.s₄, p.s₄_mem, rfl⟩
  E_gen := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨i, j, k, h⟩ := p.E_gen a ha
    refine ⟨i, j, k, ?_⟩
    have := congrArg (incl z) h
    simpa [map_mul, map_zpow, Elts.transfer_s₁, Elts.transfer_s₂, Elts9.transfer_s₄, incl_apply] using this
  E_card := by rw [Subgroup.card_map_of_injective incl_injective]; exact p.E_card
  E_abel := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (p.E_abel a ha b hb)
  E_exp := by
    rintro _ ⟨a, ha, rfl⟩
    have := congrArg (incl z) (p.E_exp a ha)
    simpa [map_pow] using this
  Es_ge := Subgroup.map_mono p.Es_ge
  Es_p := IsPGroup.map p.Es_p _
  Es_card := by rw [Subgroup.card_map_of_injective incl_injective]; exact p.Es_card
  Es_comm := by
    rintro _ ⟨x, -, rfl⟩
    exact coe_mul_z x
  Es_max := by
    intro R hRz hR hEsR
    have hRrange : R ≤ (incl z).range := fun r hr =>
      ⟨⟨r, Subgroup.mem_centralizer_singleton_iff.mpr (hRz r hr)⟩, rfl⟩
    have hmap : (R.comap (incl z)).map (incl z) = R := by
      rw [Subgroup.map_comap_eq]
      exact inf_eq_right.mpr hRrange
    have hR' : R.comap (incl z) = p.Es := p.Es_max _ (fun x _ => mul_zH x)
      (hR.comap_of_injective _ incl_injective) (Subgroup.map_le_iff_le_comap.mp hEsR)
    rw [← hmap, hR']
  E_unique := by
    intro A hA hAcard hAab
    obtain ⟨hmap, hle, hcard⟩ := pullback hA
    have hab' : ∀ a ∈ A.comap (incl z), ∀ b ∈ A.comap (incl z), a * b = b * a := fun a ha b hb =>
      incl_injective (by rw [map_mul, map_mul]; exact hAab _ ha _ hb)
    have := p.E_unique _ hle (hcard.trans hAcard) hab'
    rw [← hmap, this]
  cent := by
    have h := congrArg (Subgroup.map (incl z)) p.cent
    rw [centralizer_zH, inf_top_eq, map_centralizer_subgroup, Subgroup.map_sup,
      MonoidHom.map_zpowers] at h
    exact h
  t_norm := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨e.t * a * e.t⁻¹, p.t_norm a ha, by simp [incl_apply, Elts.transfer_t]⟩
  x_norm := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨e9.x * a * e9.x⁻¹, p.x_norm a ha, by simp [incl_apply, Elts9.transfer_x]⟩
  noOdd := by
    intro N hN hnorm hodd
    rw [NHE_map] at hN hnorm
    obtain ⟨hmap, hle, hcard⟩ := pullback hN
    have hN' : N.comap (incl z) ≤ p.E := by
      refine p.noOdd _ hle (fun g hg n hn => ?_) (hcard ▸ hodd)
      have h1 := hnorm (incl z g) ⟨g, hg, rfl⟩ (incl z n) hn
      show incl z (g * n * g⁻¹) ∈ N
      rwa [map_mul, map_mul, map_inv]
    rw [← hmap]
    exact Subgroup.map_mono hN'
  irred := by
    intro P hP hs₁ hinv
    rw [NHE_map] at hinv
    have hPrange : P ≤ (p.E.map (incl z)) := hP
    obtain ⟨hmap, hle, -⟩ := pullback hPrange
    have hs₁' : e.s₁ ∈ P.comap (incl z) := hs₁
    have := p.irred _ hle hs₁' (fun g hg q hq => by
      have h1 := hinv (incl z g) ⟨g, hg, rfl⟩ (incl z q) hq
      show incl z (g * q * g⁻¹) ∈ P
      rwa [map_mul, map_mul, map_inv])
    rw [← hmap, this]
  invClass := by
    intro u hu hou huz
    rw [NHE_map] at hu ⊢
    obtain ⟨u', hu', rfl⟩ := hu
    have hou' : orderOf u' = 2 := by
      have h := hou
      rw [show incl z u' = (u' : G) from rfl, Subgroup.orderOf_coe] at h
      exact h
    obtain ⟨g, hg, hgt⟩ := p.invClass u' hu' hou' (fun h => huz (by rw [h]; rfl))
    exact ⟨incl z g, ⟨g, hg, rfl⟩, by simpa [incl_apply, Elts.transfer_t] using congrArg (incl z) hgt⟩
  S₂_syl := by
    rw [NHE_map]
    exact isSylowIn_map p.S₂_syl
  S₂_z := ⟨zH z, p.S₂_z, rfl⟩
  S₂_cen := by
    rintro _ ⟨y, hy, rfl⟩ hord hc
    have : y = zH z := p.S₂_cen y hy (by rw [← Subgroup.orderOf_coe]; exact hord) (fun s hs =>
      incl_injective (by
        have := hc (incl z s) ⟨s, hs, rfl⟩
        rwa [map_mul, map_mul]))
    rw [this]
    rfl
  D_le_F := Subgroup.map_mono p.D_le_F
  D_le_E := Subgroup.map_mono p.D_le_E
  D_card := by rw [Subgroup.card_map_of_injective incl_injective]; exact p.D_card
  E_eq := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨i, d, hd, h⟩ := p.E_eq a ha
    refine ⟨i, incl z d, ⟨d, hd, rfl⟩, ?_⟩
    have := congrArg (incl z) h
    simpa [map_mul, map_zpow, Elts.transfer_s₁, incl_apply] using this
  r_mem := ⟨p.r, p.r_mem, rfl⟩
  r_ord := by rw [Subgroup.orderOf_coe]; exact p.r_ord
  r_pow := congrArg Subtype.val p.r_pow
  r_norm := by
    rintro _ ⟨d, hd, rfl⟩
    exact ⟨p.r * d * p.r⁻¹, p.r_norm d hd, rfl⟩
  t_D := by
    rintro _ ⟨d, hd, rfl⟩
    exact ⟨e.t * d * e.t⁻¹, p.t_D d hd, by simp [incl_apply, Elts.transfer_t]⟩
  t_r := by
    have h := Subgroup.mem_map_of_mem (incl z) p.t_r
    rw [MonoidHom.map_zpowers] at h
    simpa [incl_apply, Elts.transfer_t] using h
  t_r_ne := fun h => p.t_r_ne (incl_injective (by simpa [incl_apply, Elts.transfer_t] using h))

@[expose] noncomputable def Loc9.transfer (L : Loc9 (Hc z) (zH z)) : Loc9 G z where
  e := L.e.transfer
  e9 := L.e9.transfer
  f := L.f.transfer
  p3 := L.p3.transfer
  E := EPart9.transfer L.E
  m := by
    have := L.m.transfer
    exact this

end CFSG.GH74.Uniqueness.SU.SU13
