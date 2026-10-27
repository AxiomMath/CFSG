module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutGen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3D4Props
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A6Aut
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix

public section

namespace CFSG.QuasithinUnique.Setup.X3Aut

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts

theorem ShortGen.of_mulEquiv {G H : Type*} [Group G] [Group H] {I : Subgroup G}
    (Θ : G ≃* H) (h : ShortGen G I) : ShortGen H (I.map Θ.toMonoidHom) := by
  intro A hA hel
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA'bot : A.map Θ.symm.toMonoidHom ≠ ⊥ := fun h0 =>
    hA ((Subgroup.map_eq_bot_iff_of_injective (f := Θ.symm.toMonoidHom) A Θ.symm.injective).mp h0)
  have hA'el : CFSG.IsElementaryAbelian 2 ↥(A.map Θ.symm.toMonoidHom) := by
    have := hel
    exact IsElementaryAbelian.map Θ.symm.toMonoidHom
  obtain ⟨r, m, hcard, hr1, hr3, hmr, c, hcI, hgen⟩ := h _ hA'bot hA'el
  refine ⟨r, m, ?_, hr1, hr3, hmr, fun i => Θ (c i), fun i => ⟨c i, hcI i, rfl⟩, ?_⟩
  · rw [← hcard]
    exact (Subgroup.card_map_of_injective Θ.symm.injective).symm
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have h1 := hgen hy
    have h2 : Θ.toMonoidHom y ∈ (Subgroup.closure (⋃ i,
        ((((A.map Θ.symm.toMonoidHom).map (MulAut.conj (c i)).toMonoidHom : Subgroup G)) : Set G))).map
          Θ.toMonoidHom := Subgroup.mem_map_of_mem _ h1
    rw [MonoidHom.map_closure] at h2
    refine Subgroup.closure_mono ?_ h2
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp hi
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp ha'
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    refine Subgroup.mem_map.mpr ⟨a, ha, ?_⟩
    simp [MulAut.conj_apply]

@[expose] def conjHom : AutA6 →* MulAut ↥A6Models.psl29 where
  toFun := CFSG.QuasithinUnique.DoubleA3.conjAut
  map_one' := by
    refine MulEquiv.ext fun x => ?_
    apply Subtype.ext
    show ((1 : AutA6) : P10) * (x : P10) * ((1 : AutA6) : P10)⁻¹ = (x : P10)
    simp
  map_mul' a b := by
    refine MulEquiv.ext fun x => ?_
    apply Subtype.ext
    show ((a * b : AutA6) : P10) * (x : P10) * ((a * b : AutA6) : P10)⁻¹ =
      (a : P10) * ((b : P10) * (x : P10) * (b : P10)⁻¹) * (a : P10)⁻¹
    simp only [Subgroup.coe_mul]
    group

noncomputable def psiEquiv : ↥A6Models.psl29 ≃* alternatingGroup (Fin 6) :=
  (CFSG.QuasithinUnique.DoubleA3.exists_psl_equiv).choose

noncomputable def thetaEquiv : AutA6 ≃* MulAut (alternatingGroup (Fin 6)) :=
  (MulEquiv.ofBijective conjHom ⟨CFSG.QuasithinUnique.DoubleA3.conjAut_injective,
    CFSG.QuasithinUnique.DoubleA3.conjAut_surjective⟩).trans (MulAut.congr psiEquiv)

theorem thetaEquiv_psl (b : AutA6) (hb : b ∈ PslSub) :
    thetaEquiv b = MulAut.conj (psiEquiv ⟨(b : P10), hb⟩) := by
  refine MulEquiv.ext fun z => ?_
  show psiEquiv (CFSG.QuasithinUnique.DoubleA3.conjAut b (psiEquiv.symm z)) =
    psiEquiv ⟨(b : P10), hb⟩ * z * (psiEquiv ⟨(b : P10), hb⟩)⁻¹
  have h : CFSG.QuasithinUnique.DoubleA3.conjAut b (psiEquiv.symm z) =
      (⟨(b : P10), hb⟩ : ↥A6Models.psl29) * psiEquiv.symm z * (⟨(b : P10), hb⟩ : ↥A6Models.psl29)⁻¹ :=
    Subtype.ext rfl
  rw [h, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem map_PslSub_eq_inner :
    PslSub.map thetaEquiv.toMonoidHom =
      (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range := by
  ext f
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨psiEquiv ⟨(b : P10), hb⟩, (thetaEquiv_psl b hb).symm⟩
  · rintro ⟨g, rfl⟩
    have hg : ((psiEquiv.symm g : ↥A6Models.psl29) : P10) ∈ A6Models.autA6 :=
      psl29_le_autA6 (psiEquiv.symm g).2
    refine ⟨⟨((psiEquiv.symm g : ↥A6Models.psl29) : P10), hg⟩, (psiEquiv.symm g).2, ?_⟩
    show thetaEquiv _ = _
    rw [thetaEquiv_psl _ (psiEquiv.symm g).2]
    simp

theorem card_mulAut_alt6 : Nat.card (MulAut (alternatingGroup (Fin 6))) = 1440 := by
  rw [← Nat.card_congr thetaEquiv.toEquiv]
  exact card_autA6

theorem index_inner_alt6 :
    (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range.index = 4 := by
  have h1 := Subgroup.card_mul_index
    (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range
  have h2 : Nat.card (MulAut.conj : alternatingGroup (Fin 6) →*
      MulAut (alternatingGroup (Fin 6))).range = 360 :=
    CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.inner_card
  rw [h2, card_mulAut_alt6] at h1
  omega

noncomputable def kappaEquiv : ↥PslSub ≃* alternatingGroup (Fin 6) :=
  (Subgroup.subgroupOfEquivOfLe psl29_le_autA6).trans psiEquiv

theorem closure_map_equiv {G K : Type*} [Group G] [Group K] (κ : G ≃* K) {S : Set G}
    (h : Subgroup.closure S = ⊤) : Subgroup.closure (κ '' S) = ⊤ := by
  have h1 := congrArg (Subgroup.map κ.toMonoidHom) h
  rw [MonoidHom.map_closure] at h1
  rw [eq_top_iff]
  intro z _
  have hz : z ∈ (⊤ : Subgroup G).map κ.toMonoidHom := ⟨κ.symm z, trivial, by simp⟩
  rw [← h1] at hz
  exact hz

theorem d3_alt6 : ∀ a : alternatingGroup (Fin 6), a ≠ 1 → a * a = 1 →
    ∃ g : Fin 3 → alternatingGroup (Fin 6),
      Subgroup.closure (Set.range fun i => g i * a * (g i)⁻¹) = ⊤ := by
  intro a ha1 haa
  let a' : ↥PslSub := kappaEquiv.symm a
  have hka : kappaEquiv a' = a := kappaEquiv.apply_symm_apply a
  have ha'1 : a' ≠ 1 := by
    intro h
    apply ha1
    rw [← hka, h, map_one]
  have ha'a : a' * a' = 1 := by
    apply kappaEquiv.injective
    rw [map_mul, map_one, hka, haa]
  obtain ⟨g'', hgP, hgen⟩ := d3_model (a := (a' : AutA6)) a'.2 (fun h => ha'1 (Subtype.ext h))
    (congrArg Subtype.val ha'a)
  let u : Fin 3 → ↥PslSub := fun i => ⟨g'' i, hgP i⟩ * a' * ⟨g'' i, hgP i⟩⁻¹
  have hu : Subgroup.closure (Set.range u) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hz : (z : AutA6) ∈ Subgroup.closure
        (Set.range fun i => g'' i * (a' : AutA6) * (g'' i)⁻¹) := hgen z.2
    have himg : PslSub.subtype '' Set.range u =
        Set.range fun i => g'' i * (a' : AutA6) * (g'' i)⁻¹ := by
      ext x
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨u i, ⟨i, rfl⟩, rfl⟩
    rw [← himg, ← MonoidHom.map_closure] at hz
    obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hz
    have hwz' : w = z := Subtype.ext hwz
    rwa [hwz'] at hw
  refine ⟨fun i => kappaEquiv ⟨g'' i, hgP i⟩, ?_⟩
  have h2 := closure_map_equiv kappaEquiv hu
  have himg2 : (kappaEquiv : ↥PslSub → alternatingGroup (Fin 6)) '' Set.range u =
      Set.range fun i => kappaEquiv ⟨g'' i, hgP i⟩ * a * (kappaEquiv ⟨g'' i, hgP i⟩)⁻¹ := by
    ext x
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      refine ⟨i, ?_⟩
      simp [u, a']
    · rintro ⟨i, rfl⟩
      refine ⟨u i, ⟨i, rfl⟩, ?_⟩
      simp [u, a']
  rwa [himg2] at h2

theorem d4_alt6 : ∀ A : Subgroup (MulAut (alternatingGroup (Fin 6))), A ≠ ⊥ →
    CFSG.IsElementaryAbelian 2 ↥A →
    ∃ r m : ℕ, Nat.card A = 2 ^ r ∧ 1 ≤ r ∧ r ≤ 3 ∧ m * r ≤ 6 ∧
      ∃ s : Fin m → alternatingGroup (Fin 6),
        (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range ≤
          Subgroup.closure (⋃ i, ((A.map (MulAut.conj (MulAut.conj (s i))).toMonoidHom :
            Subgroup (MulAut (alternatingGroup (Fin 6)))) :
              Set (MulAut (alternatingGroup (Fin 6))))) := by
  have hSG := ShortGen.of_mulEquiv thetaEquiv shortGen_model
  rw [map_PslSub_eq_inner] at hSG
  intro A hA hel
  obtain ⟨r, m, hcard, hr1, hr3, hmr, c, hcI, hgen⟩ := hSG A hA hel
  have hex : ∀ i, ∃ s : alternatingGroup (Fin 6), MulAut.conj s = c i := fun i => hcI i
  choose s hs using hex
  refine ⟨r, m, hcard, hr1, hr3, hmr, s, ?_⟩
  obtain rfl : c = fun i => MulAut.conj (s i) := funext fun i => (hs i).symm
  exact hgen

theorem a6ShortGeneration : CFSG.QuasithinUnique.Setup.X3.A6ShortGeneration :=
  ⟨card_mulAut_alt6, index_inner_alt6, d3_alt6, d4_alt6⟩

end CFSG.QuasithinUnique.Setup.X3Aut
