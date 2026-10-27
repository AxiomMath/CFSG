module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeToralPlane
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeField

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Roots


theorem rootDiagUnit_mem_adjointGroup_of_roots {τ : Tag} {L : Type} [Field L]
    {a : Fin τ.rank → Lˣ} (hroot : ∀ j, ∃ u : Lˣ, u ^ τ.cartan.det = a j) :
    rootDiagUnit τ a ∈ adjointGroup τ L := by
  choose u hu using hroot
  have he : rootDiagUnit τ a = ((List.finRange τ.rank).map fun j =>
      torusElt τ L j (∏ i, u i ^ τ.cartan.adjugate i j)).prod := by
    rw [list_prod_torusElt_eq_rootDiagUnit, cartanChar_prod_zpow_eq_smul (Matrix.adjugate_mul _)]
    congr 1
    funext l
    exact (hu l).symm
  rw [he]
  refine Subgroup.list_prod_mem _ fun g hg => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
  exact torusElt_mem_adjointGroup i _

end Roots

section Inndiag


@[expose] noncomputable def e6InndiagGL (K : Type) [Field K] : Subgroup (ModGL Tag.E6 K) :=
  adjointGroup Tag.E6 K ⊔ (rootDiagUnitHom (τ := Tag.E6) (K := K)).range

theorem adjointGroup_le_e6InndiagGL (K : Type) [Field K] :
    adjointGroup Tag.E6 K ≤ e6InndiagGL K :=
  le_sup_left

theorem rootDiagUnit_mem_e6InndiagGL {K : Type} [Field K] (a : Fin Tag.E6.rank → Kˣ) :
    rootDiagUnit Tag.E6 a ∈ e6InndiagGL K :=
  le_sup_right (b := (rootDiagUnitHom (τ := Tag.E6) (K := K)).range) ⟨a, rfl⟩

theorem e6InndiagGL_le_normalizer (K : Type) [Field K] :
    e6InndiagGL K ≤ Subgroup.normalizer (adjointGroup Tag.E6 K : Set (ModGL Tag.E6 K)) := by
  refine sup_le Subgroup.le_normalizer ?_
  rintro _ ⟨a, rfl⟩
  exact (root_diagonal_conjugation Tag.E6 K a).2.2

@[expose] noncomputable def e6InndiagConj (K : Type) [Field K] :
    ↥(e6InndiagGL K) →* MulAut (adjointGroup Tag.E6 K) :=
  (conjNormalizerHom (e6InndiagGL K) (adjointGroup Tag.E6 K)).comp
    (Subgroup.inclusion (le_inf le_rfl (e6InndiagGL_le_normalizer K)))

theorem e6InndiagConj_apply {K : Type} [Field K] (g : ↥(e6InndiagGL K))
    (h : adjointGroup Tag.E6 K) :
    ((e6InndiagConj K g h : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
      (g : ModGL Tag.E6 K) * h * (g : ModGL Tag.E6 K)⁻¹ :=
  rfl

theorem mem_e6InndiagGL_iff {K : Type} [Field K] {g : ModGL Tag.E6 K} :
    g ∈ e6InndiagGL K ↔ g ∈ Subgroup.closure ((adjointGroup Tag.E6 K : Set (ModGL Tag.E6 K)) ∪
      ((rootDiagUnitHom (τ := Tag.E6) (K := K)).range : Set (ModGL Tag.E6 K))) := by
  rw [e6InndiagGL, Subgroup.sup_eq_closure]

theorem range_e6InndiagConj (K : Type) [Field K] :
    (e6InndiagConj K).range = e6Inndiag K := by
  apply le_antisymm
  · rintro _ ⟨⟨g, hg⟩, rfl⟩
    have key : ∀ (x : ModGL Tag.E6 K) (hx : x ∈ Subgroup.closure
        ((adjointGroup Tag.E6 K : Set (ModGL Tag.E6 K)) ∪
          ((rootDiagUnitHom (τ := Tag.E6) (K := K)).range : Set (ModGL Tag.E6 K)))),
        e6InndiagConj K ⟨x, mem_e6InndiagGL_iff.2 hx⟩ ∈ e6Inndiag K := by
      intro x hx
      induction hx using Subgroup.closure_induction with
      | mem x hx =>
        rcases hx with hx | ⟨a, rfl⟩
        · exact le_sup_left (b := (rootDiagAutHom Tag.E6 K).range)
            ⟨⟨x, hx⟩, MulEquiv.ext fun h => Subtype.ext rfl⟩
        · exact le_sup_right (a := innerAut (adjointGroup Tag.E6 K))
            ⟨a, MulEquiv.ext fun h => Subtype.ext rfl⟩
      | one =>
        rw [show (⟨1, mem_e6InndiagGL_iff.2 (Subgroup.one_mem _)⟩ : ↥(e6InndiagGL K)) = 1
          from rfl, map_one]
        exact (e6Inndiag K).one_mem
      | mul x y hx hy ihx ihy =>
        rw [show (⟨x * y, mem_e6InndiagGL_iff.2 (Subgroup.mul_mem _ hx hy)⟩ :
            ↥(e6InndiagGL K)) = ⟨x, mem_e6InndiagGL_iff.2 hx⟩ * ⟨y, mem_e6InndiagGL_iff.2 hy⟩
          from rfl, map_mul]
        exact (e6Inndiag K).mul_mem ihx ihy
      | inv x hx ihx =>
        rw [show (⟨x⁻¹, mem_e6InndiagGL_iff.2 (Subgroup.inv_mem _ hx)⟩ : ↥(e6InndiagGL K)) =
            (⟨x, mem_e6InndiagGL_iff.2 hx⟩)⁻¹ from rfl, map_inv]
        exact (e6Inndiag K).inv_mem ihx
    exact key g (mem_e6InndiagGL_iff.1 hg)
  · refine sup_le ?_ ?_
    · rintro _ ⟨g, rfl⟩
      exact ⟨⟨g, adjointGroup_le_e6InndiagGL K g.2⟩, MulEquiv.ext fun h => Subtype.ext rfl⟩
    · rintro _ ⟨a, rfl⟩
      exact ⟨⟨_, rootDiagUnit_mem_e6InndiagGL a⟩, MulEquiv.ext fun h => Subtype.ext rfl⟩

end Inndiag

section BaseChange


theorem map_e6InndiagGL_le {K L : Type} [Field K] [Field L] (ι : K →+* L)
    (hroot : ∀ c : Kˣ, ∃ u : Lˣ, u ^ 3 = Units.map ι.toMonoidHom c) :
    (e6InndiagGL K).map (baseChangeGL ι) ≤ adjointGroup Tag.E6 L := by
  rw [e6InndiagGL, Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rintro _ ⟨g, hg, rfl⟩
    exact baseChangeGL_mem_adjointGroup ι hg
  · rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    change baseChangeGL ι (rootDiagUnit Tag.E6 a) ∈ _
    rw [baseChangeGL_rootDiagUnit]
    refine rootDiagUnit_mem_adjointGroup_of_roots fun j => ?_
    obtain ⟨u, hu⟩ := hroot (a j)
    refine ⟨u, ?_⟩
    rw [det_cartan_E6, show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast]
    exact hu

end BaseChange

section Faithful


theorem e6InndiagConj_injective (K : Type) [Field K] [Finite K] (hK : 4 ≤ Nat.card K) :
    Function.Injective (e6InndiagConj K) := by
  refine (injective_iff_map_eq_one _).2 fun g hg => ?_
  set L := AlgebraicClosure K
  set ι : K →+* L := algebraMap K L
  obtain ⟨hinj, -, hcent, -⟩ :=
    Chevalley_large_finite_root_centralizer_faithfulness_of_four_le Tag.E6 K hK L ι
  have hroot : ∀ c : Kˣ, ∃ u : Lˣ, u ^ 3 = Units.map ι.toMonoidHom c := by
    intro c
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (ι c) (n := 3) (by norm_num)
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow (by norm_num)] at hz
      exact c.ne_zero (ι.injective (hz.symm.trans (map_zero ι).symm))
    exact ⟨Units.mk0 z hz0, Units.ext (by simpa using hz)⟩
  have hgL : baseChangeGL ι (g : ModGL Tag.E6 K) ∈ adjointGroup Tag.E6 L :=
    map_e6InndiagGL_le ι hroot (Subgroup.mem_map_of_mem _ g.2)
  have h1 : baseChangeGL ι (g : ModGL Tag.E6 K) = 1 := by
    refine hcent _ hgL fun h hh => ?_
    obtain ⟨h', hh', rfl⟩ := hh
    have e := congrArg (fun φ : MulAut (adjointGroup Tag.E6 K) =>
      ((φ ⟨h', hh'⟩ : adjointGroup Tag.E6 K) : ModGL Tag.E6 K)) hg
    simp only [e6InndiagConj_apply, MulAut.one_apply] at e
    rw [← map_mul, ← map_mul]
    congr 1
    calc (g : ModGL Tag.E6 K) * h' = (g * h' * (g : ModGL Tag.E6 K)⁻¹) * g := by group
      _ = h' * g := by rw [e]
  exact Subtype.ext (hinj (h1.trans (map_one _).symm))

end Faithful

theorem exists_cubeExt (K : Type) [Field K] [Finite K] :
    ∃ K₁ : IntermediateField K (AlgebraicClosure K), Finite K₁ ∧
      ∀ c : Kˣ, ∃ u : K₁ˣ, u ^ 3 = Units.map (algebraMap K K₁).toMonoidHom c := by
  choose r hr using fun c : K =>
    IsAlgClosed.exists_pow_nat_eq (algebraMap K (AlgebraicClosure K) c) (n := 3) (by norm_num)
  have hmem : ∀ c, r c ∈ IntermediateField.adjoin K (Set.range r) := fun c =>
    IntermediateField.subset_adjoin K _ ⟨c, rfl⟩
  refine ⟨IntermediateField.adjoin K (Set.range r), ?_, fun c => ?_⟩
  · have : FiniteDimensional K (IntermediateField.adjoin K (Set.range r)) :=
      IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
    exact Module.finite_of_finite K
  · set u : IntermediateField.adjoin K (Set.range r) := ⟨r c, hmem c⟩
    have hu : u ^ 3 = algebraMap K _ (c : K) := Subtype.ext (by
      change r c ^ 3 = algebraMap K (AlgebraicClosure K) c
      exact hr c)
    have h0 : u ≠ 0 := by
      intro h
      rw [h, zero_pow (by norm_num)] at hu
      exact c.ne_zero ((algebraMap K _).injective (hu.symm.trans (map_zero _).symm))
    exact ⟨Units.mk0 u h0, Units.ext (by simpa using hu)⟩

section Plane

open CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny


theorem exists_isotropic_plane_of_lift {K : Type} [Field K] {X : Type*} [Group X]
    {G : Subgroup (ModGL Tag.E6 K)} (c : ↥G →* MulAut X) (hc : Function.Injective c)
    {K₁ : Type} [Field K₁] [Finite K₁] (ι₁ : K →+* K₁)
    (hG : G.map (baseChangeGL ι₁) ≤ adjointGroup Tag.E6 K₁)
    {D : Subgroup (MulAut X)} (hDc : D ≤ c.range) (hD : IsElemAbelian 3 D)
    (hcard : Nat.card D = 3 ^ 3) :
    ∃ E : Subgroup (MulAut X), E ≤ D ∧ 3 ^ 2 ≤ Nat.card E ∧
      ∀ x y : ↥(e6Data_valid.minGroup K₁),
        (e6Isogeny K₁ x : ModGL Tag.E6 K₁) ∈ ((E.comap c).map G.subtype).map (baseChangeGL ι₁) →
        (e6Isogeny K₁ y : ModGL Tag.E6 K₁) ∈ ((E.comap c).map G.subtype).map (baseChangeGL ι₁) →
        x * y = y * x := by
  classical
  set θ : ModGL Tag.E6 K →* ModGL Tag.E6 K₁ := baseChangeGL ι₁ with hθ
  have hθinj : Function.Injective θ := baseChangeGL_injective ι₁
  set M := G.map θ with hM
  set φ : ↥(e6Data_valid.minGroup K₁) →* ModGL Tag.E6 K₁ :=
    (adjointGroup Tag.E6 K₁).subtype.comp (e6Isogeny K₁) with hφ
  set S := M.comap φ with hS
  set ρ : ↥S →* ↥M := (φ.comp S.subtype).codRestrict M fun s => s.2 with hρ
  set eM : ↥G ≃* ↥M := Subgroup.equivMapOfInjective G θ hθinj with heM
  set π : ↥S →* MulAut X := c.comp (eM.symm.toMonoidHom.comp ρ) with hπ
  have hcen : ∀ s : ↥S, π s = 1 → (s : ↥(e6Data_valid.minGroup K₁)) ∈
      Subgroup.center ↥(e6Data_valid.minGroup K₁) := by
    intro s hs
    have h1 : eM.symm (ρ s) = 1 := hc (hs.trans (map_one _).symm)
    have h2 : ρ s = 1 := eM.symm.injective (h1.trans (map_one eM.symm).symm)
    have h2' : (ρ s : ModGL Tag.E6 K₁) = 1 := congrArg Subtype.val h2
    have h3 : e6Isogeny K₁ (s : ↥(e6Data_valid.minGroup K₁)) = 1 := Subtype.ext h2'
    rw [← CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center]
    exact h3
  have hker : π.ker ≤ Subgroup.center ↥S := by
    intro s hs
    have hc := hcen s hs
    rw [Subgroup.mem_center_iff]
    intro t
    exact Subtype.ext (Subgroup.mem_center_iff.1 hc t)
  have hker3 : Nat.card π.ker ∣ 3 := by
    have hle : π.ker.map S.subtype ≤ Subgroup.center ↥(e6Data_valid.minGroup K₁) := by
      rintro _ ⟨s, hs, rfl⟩
      exact hcen s hs
    rw [← Subgroup.card_map_of_injective S.subtype_injective]
    refine (Subgroup.card_dvd_of_le hle).trans ?_
    rw [(CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e6 K₁).1]
    exact Nat.gcd_dvd_left 3 _
  have hlift : ∀ g : ↥G, ∃ s : ↥S, ρ s = eM g := by
    intro g
    have hθg : θ g ∈ adjointGroup Tag.E6 K₁ := hG (Subgroup.mem_map_of_mem _ g.2)
    obtain ⟨s, hs⟩ := e6Isogeny_surjective K₁ ⟨θ g, hθg⟩
    have hsS : s ∈ S := by
      change φ s ∈ M
      rw [show φ s = θ g from congrArg Subtype.val hs]
      exact Subgroup.mem_map_of_mem _ g.2
    have hv : ((e6Isogeny K₁ s : adjointGroup Tag.E6 K₁) : ModGL Tag.E6 K₁) = θ g :=
      congrArg Subtype.val hs
    exact ⟨⟨s, hsS⟩, Subtype.ext hv⟩
  have hDπ : D ≤ π.range := by
    intro d hd
    obtain ⟨g, rfl⟩ := hDc hd
    obtain ⟨s, hs⟩ := hlift g
    refine ⟨s, ?_⟩
    change c (eM.symm (ρ s)) = _
    rw [hs, MulEquiv.symm_apply_apply]
  obtain ⟨E, hED, hE9, hEab⟩ :=
    exists_le_comap_commute_of_ker_dvd_three π hker hker3 hDπ hD hcard
  refine ⟨E, hED, hE9, fun x y hx hy => ?_⟩
  have key : ∀ z : ↥(e6Data_valid.minGroup K₁), (e6Isogeny K₁ z : ModGL Tag.E6 K₁) ∈
      ((E.comap c).map G.subtype).map θ → ∃ hz : z ∈ S, (⟨z, hz⟩ : ↥S) ∈ E.comap π := by
    intro z hz
    obtain ⟨_, ⟨g, hgE, rfl⟩, hgz⟩ := hz
    have hgz' : φ z = θ g := hgz.symm
    have hzS : z ∈ S := by
      change φ z ∈ M
      rw [hgz']
      exact Subgroup.mem_map_of_mem _ g.2
    refine ⟨hzS, ?_⟩
    have hρz : ρ ⟨z, hzS⟩ = eM g := Subtype.ext hgz'
    change c (eM.symm (ρ ⟨z, hzS⟩)) ∈ E
    rw [hρz, MulEquiv.symm_apply_apply]
    exact hgE
  obtain ⟨hxS, hxE⟩ := key x hx
  obtain ⟨hyS, hyE⟩ := key y hy
  exact congrArg Subtype.val (hEab _ hxE _ hyE)

theorem exists_isotropic_plane_e6Inndiag (K : Type) [Field K] [Finite K] (hK : 4 ≤ Nat.card K)
    {K₁ : Type} [Field K₁] [Finite K₁] (ι₁ : K →+* K₁)
    (hroot : ∀ c : Kˣ, ∃ u : K₁ˣ, u ^ 3 = Units.map ι₁.toMonoidHom c)
    {D : Subgroup (MulAut (adjointGroup Tag.E6 K))} (hDd : D ≤ e6Inndiag K)
    (hD : IsElemAbelian 3 D) (hcard : Nat.card D = 3 ^ 3) :
    ∃ E : Subgroup (MulAut (adjointGroup Tag.E6 K)), E ≤ D ∧ 3 ^ 2 ≤ Nat.card E ∧
      ∀ x y : ↥(e6Data_valid.minGroup K₁),
        (e6Isogeny K₁ x : ModGL Tag.E6 K₁) ∈
          ((E.comap (e6InndiagConj K)).map (e6InndiagGL K).subtype).map (baseChangeGL ι₁) →
        (e6Isogeny K₁ y : ModGL Tag.E6 K₁) ∈
          ((E.comap (e6InndiagConj K)).map (e6InndiagGL K).subtype).map (baseChangeGL ι₁) →
        x * y = y * x :=
  exists_isotropic_plane_of_lift (e6InndiagConj K) (e6InndiagConj_injective K hK) ι₁
    (map_e6InndiagGL_le ι₁ hroot) (by rw [range_e6InndiagConj]; exact hDd) hD hcard

end Plane

end CFSG.HardMathSupport.Timmesfeld.CrossChar
