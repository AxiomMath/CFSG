module

public import CFSG.GH74.Uniqueness.SU.SU13Data

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU13.TB

variable {G : Type} [Group G] (z : G)

abbrev Hc : Type := ↥(centralizer ({z} : Set G))

@[expose] def zH : Hc z := ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

@[expose] def incl : Hc z →* G := (centralizer ({z} : Set G)).subtype

variable {z}

theorem incl_injective : Function.Injective (incl z) := (centralizer ({z} : Set G)).subtype_injective

theorem incl_apply (x : Hc z) : incl z x = (x : G) := rfl

theorem coe_mul_z (x : Hc z) : (x : G) * z = z * (x : G) :=
  Subgroup.mem_centralizer_singleton_iff.mp x.2

theorem mul_zH (x : Hc z) : x * zH z = zH z * x := Subtype.ext (coe_mul_z x)

theorem centralizer_zH : centralizer ({zH z} : Set (Hc z)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  exact Subgroup.mem_centralizer_singleton_iff.mpr (mul_zH x)

theorem map_centralizer_singleton (x : Hc z) :
    (centralizer ({x} : Set (Hc z))).map (incl z) =
      centralizer ({(x : G)} : Set G) ⊓ centralizer ({z} : Set G) := by
  ext g
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    incl_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨congrArg Subtype.val hy, coe_mul_z y⟩
  · rintro ⟨hg1, hg2⟩
    exact ⟨⟨g, Subgroup.mem_centralizer_singleton_iff.mpr hg2⟩, Subtype.ext hg1, rfl⟩

theorem map_centralizer_subgroup (E : Subgroup (Hc z)) :
    (centralizer (E : Set (Hc z))).map (incl z) =
      centralizer ((E.map (incl z) : Subgroup G) : Set G) ⊓ centralizer ({z} : Set G) := by
  ext g
  simp only [Subgroup.mem_map, Subgroup.mem_inf, incl_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨?_, y.2⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp hy) x hx)
  · rintro ⟨hg1, hg2⟩
    refine ⟨⟨g, hg2⟩, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hg1) (x : G) ⟨x, hx, rfl⟩)

theorem isSylowIn_map [Finite G] {X P : Subgroup (Hc z)} (h : IsSylowIn X P) :
    IsSylowIn (X.map (incl z)) (P.map (incl z)) := by
  obtain ⟨hPX, k, m, hk, hm, hX⟩ := isSylowIn_iff_card.mp h
  refine isSylowIn_iff_card.mpr ⟨Subgroup.map_mono hPX, k, m, ?_, hm, ?_⟩
  · rw [Subgroup.card_map_of_injective incl_injective, hk]
  · rw [Subgroup.card_map_of_injective incl_injective, hX]

theorem pullback {F : Subgroup (Hc z)} {N : Subgroup G} (hN : N ≤ F.map (incl z)) :
    (N.comap (incl z)).map (incl z) = N ∧ N.comap (incl z) ≤ F ∧
      Nat.card (N.comap (incl z)) = Nat.card N := by
  have h1 : (N.comap (incl z)).map (incl z) = N := by
    rw [Subgroup.map_comap_eq]
    refine inf_eq_right.mpr (hN.trans ?_)
    rintro _ ⟨y, _, rfl⟩
    exact ⟨y, rfl⟩
  refine ⟨h1, ?_, ?_⟩
  · intro n hn
    obtain ⟨y, hy, hyn⟩ := hN hn
    rw [← incl_injective hyn]
    exact hy
  · rw [← Subgroup.card_map_of_injective incl_injective, h1]

section Structures

variable [Finite G]

@[expose] noncomputable def Elts.transfer (e : Elts (Hc z) (zH z)) : Elts G z where
  s₁ := (e.s₁ : G)
  s₂ := (e.s₂ : G)
  s₃ := (e.s₃ : G)
  t := (e.t : G)
  s₁_comm := coe_mul_z e.s₁
  s₂_comm := coe_mul_z e.s₂
  s₃_comm := coe_mul_z e.s₃
  s₁_ord := by rw [Subgroup.orderOf_coe]; exact e.s₁_ord
  s₂_ord := by rw [Subgroup.orderOf_coe]; exact e.s₂_ord
  s₃_ord := by rw [Subgroup.orderOf_coe]; exact e.s₃_ord
  t_comm := coe_mul_z e.t
  t_ord := by rw [Subgroup.orderOf_coe]; exact e.t_ord
  t_ne := fun h => e.t_ne (Subtype.ext h)
  t_s₂ := congrArg Subtype.val e.t_s₂
  t_s₁ := congrArg Subtype.val e.t_s₁
  class3 := fun u hu hord => by
    have huH : u ∈ centralizer ({z} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr hu
    obtain ⟨h, -, hh⟩ := e.class3 ⟨u, huH⟩ (mul_zH _) (by rw [Subgroup.orderOf_mk]; exact hord)
    refine ⟨(h : G), coe_mul_z h, ?_⟩
    rcases hh with h1 | h1 | h1
    · exact Or.inl (congrArg Subtype.val h1)
    · exact Or.inr (Or.inl (congrArg Subtype.val h1))
    · exact Or.inr (Or.inr (congrArg Subtype.val h1))
  class2 := fun u v hu hv hou hov huz hvz => by
    have huH : u ∈ centralizer ({z} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr hu
    have hvH : v ∈ centralizer ({z} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr hv
    obtain ⟨h, -, hh⟩ := e.class2 ⟨u, huH⟩ ⟨v, hvH⟩ (mul_zH _) (mul_zH _)
      (by rw [Subgroup.orderOf_mk]; exact hou) (by rw [Subgroup.orderOf_mk]; exact hov)
      (fun h' => huz (congrArg Subtype.val h')) (fun h' => hvz (congrArg Subtype.val h'))
    exact ⟨(h : G), coe_mul_z h, congrArg Subtype.val hh⟩

omit [Finite G] in
theorem Elts.transfer_s₁ (e : Elts (Hc z) (zH z)) : e.transfer.s₁ = (e.s₁ : G) := rfl

omit [Finite G] in
theorem Elts.transfer_s₂ (e : Elts (Hc z) (zH z)) : e.transfer.s₂ = (e.s₂ : G) := rfl

omit [Finite G] in
theorem Elts.transfer_t (e : Elts (Hc z) (zH z)) : e.transfer.t = (e.t : G) := rfl

@[expose] noncomputable def FPart10.transfer {e : Elts (Hc z) (zH z)} (f : FPart10 (zH z) e) :
    FPart10 z e.transfer where
  F := f.F.map (incl z)
  F_comm := by
    rintro _ ⟨y, -, rfl⟩
    exact coe_mul_z y
  z_mem := ⟨zH z, f.z_mem, rfl⟩
  F_s₁ := by
    rintro _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (f.F_s₁ y hy)
  cent := by
    have h := congrArg (Subgroup.map (incl z)) f.cent
    rw [centralizer_zH, inf_top_eq, map_centralizer_singleton, Subgroup.map_sup,
      MonoidHom.map_zpowers] at h
    exact h
  F_noOdd := by
    intro N hN hnorm hodd
    obtain ⟨hmap, hle, hcard⟩ := pullback hN
    have hN' : N.comap (incl z) = ⊥ := by
      refine f.F_noOdd _ hle (fun x hx n hn => ?_) (hcard ▸ hodd)
      have h1 : incl z x * incl z n * (incl z x)⁻¹ ∈ N := hnorm _ ⟨x, hx, rfl⟩ _ hn
      show incl z (x * n * x⁻¹) ∈ N
      rwa [map_mul, map_mul, map_inv]
    rw [← hmap, hN', Subgroup.map_bot]
  F_socle := by
    intro N hN hnorm hne
    obtain ⟨hmap, hle, hcard⟩ := pullback hN
    have hne' : N.comap (incl z) ≠ ⊥ := fun h => hne (by rw [← hmap, h, Subgroup.map_bot])
    have hz := f.F_socle _ hle (fun x hx n hn => by
      have h1 : incl z x * incl z n * (incl z x)⁻¹ ∈ N := hnorm _ ⟨x, hx, rfl⟩ _ hn
      show incl z (x * n * x⁻¹) ∈ N
      rwa [map_mul, map_mul, map_inv]) hne'
    exact hz
  T₁ := f.T₁.map (incl z)
  T₁_syl := by
    have h := isSylowIn_map f.T₁_syl
    rwa [centralizer_zH, inf_top_eq, map_centralizer_singleton] at h
  T₁_z := ⟨zH z, f.T₁_z, rfl⟩
  T₁_uniq := by
    rintro _ ⟨y, hy, rfl⟩ h2
    have : y = zH z := f.T₁_uniq y hy (by rwa [← Subgroup.orderOf_coe])
    rw [this]
    rfl
  T₁_quat := by
    obtain ⟨k, hk, ⟨e'⟩⟩ := f.T₁_quat
    exact ⟨k, hk, ⟨(Subgroup.equivMapOfInjective f.T₁ (incl z) incl_injective).symm.trans e'⟩⟩
  F_five := by
    obtain ⟨u, hu, ho⟩ := f.F_five
    exact ⟨incl z u, ⟨u, hu, rfl⟩, by rw [← ho, ← Subgroup.orderOf_coe]; rfl⟩
  F_seven := by
    obtain ⟨u, hu, ho⟩ := f.F_seven
    exact ⟨incl z u, ⟨u, hu, rfl⟩, by rw [← ho, ← Subgroup.orderOf_coe]; rfl⟩

theorem P3Part.transfer {e : Elts (Hc z) (zH z)} (p : P3Part (zH z) e) : P3Part z e.transfer := by
  refine ⟨?_⟩
  have h := isSylowIn_map p.syl
  rw [centralizer_zH, inf_top_eq, map_centralizer_singleton, MonoidHom.map_zpowers] at h
  exact h

theorem EPart10.transfer {e : Elts (Hc z) (zH z)} (p : EPart10 (zH z) e) :
    EPart10 z e.transfer := by
  obtain ⟨E, Es, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := p.ex
  refine ⟨⟨E.map (incl z), Es.map (incl z), ⟨e.s₁, h1, rfl⟩, Subgroup.map_mono h2, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩⟩
  · rw [Subgroup.card_map_of_injective incl_injective, h3]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (h4 a ha b hb)
  · exact IsPGroup.map h5 _
  · rw [Subgroup.card_map_of_injective incl_injective, h6]
  · rintro _ ⟨x, -, rfl⟩
    exact coe_mul_z x
  · intro R hRz hR hEsR
    have hRrange : R ≤ (incl z).range := fun r hr =>
      ⟨⟨r, Subgroup.mem_centralizer_singleton_iff.mpr (hRz r hr)⟩, rfl⟩
    have hmap : (R.comap (incl z)).map (incl z) = R := by
      rw [Subgroup.map_comap_eq]
      exact inf_eq_right.mpr hRrange
    have hR' : R.comap (incl z) = Es := h8 _ (fun x _ => mul_zH x)
      (hR.comap_of_injective _ incl_injective) (Subgroup.map_le_iff_le_comap.mp hEsR)
    rw [← hmap, hR']
  · constructor
    · intro A hA hAcard hAab
      obtain ⟨hmap, hle, hcard⟩ := pullback hA
      have hab' : ∀ a ∈ A.comap (incl z), ∀ b ∈ A.comap (incl z), a * b = b * a := fun a ha b hb =>
        incl_injective (by rw [map_mul, map_mul]; exact hAab _ ha _ hb)
      have := h9 _ hle (hcard.trans hAcard) hab'
      rw [← hmap, this]
    · have h := congrArg (Subgroup.map (incl z)) h10
      rw [centralizer_zH, inf_top_eq, map_centralizer_subgroup, Subgroup.map_sup,
        MonoidHom.map_zpowers] at h
      exact h

omit [Finite G] in
theorem oc_map (M : Subgroup (Hc z)) : oc (M.map (incl z)) = (oc M).map (incl z) := by
  unfold oc
  have h := CFSG.pPrimeCore_map_iso 2 (Subgroup.equivMapOfInjective M (incl z) incl_injective)
  rw [← h, Subgroup.map_map, Subgroup.map_map]
  congr 1

@[expose] noncomputable def MbarEquiv (M : Subgroup (Hc z)) :
    Mbar M ≃* Mbar (M.map (incl z)) :=
  QuotientGroup.congr _ _ (Subgroup.equivMapOfInjective M (incl z) incl_injective)
    (CFSG.pPrimeCore_map_iso 2 (Subgroup.equivMapOfInjective M (incl z) incl_injective))

theorem MPart10.transfer {e : Elts (Hc z) (zH z)} (p : MPart10 (zH z) e) :
    MPart10 z e.transfer := by
  have hM : (centralizer ({e.s₂} : Set (Hc z)) ⊓ centralizer ({zH z} : Set (Hc z))).map (incl z) =
      centralizer ({e.transfer.s₂} : Set G) ⊓ centralizer ({z} : Set G) := by
    rw [centralizer_zH, inf_top_eq, map_centralizer_singleton]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [← hM, Subgroup.card_map_of_injective incl_injective]
    exact p.card
  · rw [← hM]
    obtain ⟨φ⟩ := p.gl
    exact ⟨(MbarEquiv _).symm.trans φ⟩
  · intro x hx htx
    rw [← hM, oc_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have h1 : e.t * y = y * e.t := incl_injective (by rw [map_mul, map_mul]; exact htx)
    have h2 := Subgroup.mem_map_of_mem (incl z) (p.cent_t y hy h1)
    rwa [MonoidHom.map_zpowers] at h2

@[expose] noncomputable def Loc10.transfer (L : Loc10 (Hc z) (zH z)) : Loc10 G z where
  e := L.e.transfer
  f := L.f.transfer
  p3 := L.p3.transfer
  m := L.m.transfer
  E := L.E.transfer

end Structures

end CFSG.GH74.Uniqueness.SU.SU13
