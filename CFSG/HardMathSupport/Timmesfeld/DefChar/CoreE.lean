module

public import CFSG.LieType.Chevalley.E6FieldGraphFieldPointwiseCentralizer
public import CFSG.LieType.Chevalley.EvenExceptionalActorCoverage
public import CFSG.LieType.Chevalley.ParabolicDiagonalFieldNormalizers
public import CFSG.GH74.GLS.Stage2.OddAut.RPData
public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreExcGeneric
public import CFSG.HardMathSupport.Timmesfeld.DefChar.OuterE
public import CFSG.HardMathSupport.Timmesfeld.Balance.Basic

public section

namespace CFSG.HardMathSupport.Timmesfeld.DefChar

open CFSG.Blueprint.Chevalley CFSG.Blueprint CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.FieldGraphFieldPointwise CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Transport

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance

theorem gLAPPrimeCoreOf_map_mulEquiv_E {M M' : Type} [Group M] [Group M'] (p : ℕ) (φ : M ≃* M')
    (B : Subgroup M) :
    GLAPPrimeCoreOf p (B.map φ.toMonoidHom) = (GLAPPrimeCoreOf p B).map φ.toMonoidHom := by
  let e : ↥B ≃* ↥(B.map φ.toMonoidHom) :=
    Subgroup.equivMapOfInjective B φ.toMonoidHom φ.injective
  have h := CFSG.HardMathSupport.Timmesfeld.Balance.gLAPPrimeCoreOf_eq_map_of_mulEquiv p
    (φ.toMonoidHom.comp B.subtype) e (fun x => rfl)
  rw [h]
  unfold GLAPPrimeCoreOf
  rw [Subgroup.map_map]

theorem gLAPPrimeCoreOf_inf_centralizer_of_congr_E {S Y : Type} [Group S] [Group Y] (p : ℕ)
    (e : S ≃* Y) (H : Subgroup (MulAut S)) (x : MulAut S)
    (h : GLAPPrimeCoreOf p (H.map (MulAut.congr e).toMonoidHom ⊓
      Subgroup.centralizer ({MulAut.congr e x} : Set (MulAut Y))) = ⊥) :
    GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({x} : Set (MulAut S))) = ⊥ := by
  set φ := MulAut.congr e with hφ
  have hmap : H.map φ.toMonoidHom ⊓ Subgroup.centralizer ({φ x} : Set (MulAut Y)) =
      (H ⊓ Subgroup.centralizer ({x} : Set (MulAut S))).map φ.toMonoidHom := by
    ext z
    obtain ⟨y, rfl⟩ := φ.surjective z
    simp only [Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_centralizer_iff,
      Set.mem_singleton_iff, forall_eq]
    constructor
    · rintro ⟨⟨y', hy', hyy'⟩, hc⟩
      have : y' = y := φ.injective hyy'
      subst this
      refine ⟨y', ⟨hy', ?_⟩, rfl⟩
      apply φ.injective
      simpa using hc
    · rintro ⟨y', ⟨hy', hc⟩, hyy'⟩
      have : y' = y := φ.injective hyy'
      subst this
      refine ⟨⟨y', hy', rfl⟩, ?_⟩
      have := congrArg φ hc
      simpa using this
  rw [hmap, gLAPPrimeCoreOf_map_mulEquiv_E] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).1 h

end Transport


variable {τ : Tag} {K : Type} [Field K]

theorem inv_mul_apply_mem_parabolicRadical {J : Set (Fin τ.rank)} (hJ : J ≠ Set.univ)
    {α : MulAut (adjointGroup τ K)}
    (hα : ∀ x : adjointGroup τ K, (x : ModGL τ K) ∈ parabolicRadical τ K J → α x = x)
    (y : adjointGroup τ K) (hy : (y : ModGL τ K) ∈ parabolicSubgroup τ K J) :
    ((y⁻¹ * α y : adjointGroup τ K) : ModGL τ K) ∈ parabolicRadical τ K J := by
  have hQC : parabolicRadical τ K J ≤ adjointGroup τ K :=
    (parabolicRadical_le_posUnipotent J).trans posUnipotent_le_adjointGroup
  set h : adjointGroup τ K := y⁻¹ * α y with hh
  have hcomm : ∀ q ∈ parabolicRadical τ K J, (q : ModGL τ K) * (h : ModGL τ K) =
      (h : ModGL τ K) * q := by
    intro q hq
    set q' : adjointGroup τ K := ⟨q, hQC hq⟩ with hq'
    have hconj : (y * q' * y⁻¹ : adjointGroup τ K) ∈ {x : adjointGroup τ K |
        (x : ModGL τ K) ∈ parabolicRadical τ K J} := by
      show ((y : ModGL τ K) * q * (y : ModGL τ K)⁻¹) ∈ parabolicRadical τ K J
      exact (Subgroup.mem_normalizer_iff.1 (parabolicSubgroup_le_normalizer_parabolicRadical J hy)
        q).1 hq
    have h1 := hα _ hconj
    rw [map_mul, map_mul, map_inv, hα q' hq] at h1
    have h2 : h * q' = q' * h := by
      rw [hh]
      calc y⁻¹ * α y * q' = y⁻¹ * (α y * q' * (α y)⁻¹) * α y := by group
        _ = y⁻¹ * (y * q' * y⁻¹) * α y := by rw [h1]
        _ = q' * (y⁻¹ * α y) := by group
    have := congrArg Subtype.val h2
    exact this.symm
  have hN : (h : ModGL τ K) ∈ Subgroup.normalizer (parabolicRadical τ K J : Set (ModGL τ K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      rw [← hcomm q hq]
      simpa using hq
    · intro hq
      have h1 := hcomm _ hq
      have h2 : q = (h : ModGL τ K) * q * (h : ModGL τ K)⁻¹ := by
        have : (h : ModGL τ K) * q * (h : ModGL τ K)⁻¹ * (h : ModGL τ K) =
            (h : ModGL τ K) * ((h : ModGL τ K) * q * (h : ModGL τ K)⁻¹) := h1
        have h3 := mul_left_cancel (a := (h : ModGL τ K)) (by
          calc (h : ModGL τ K) * q = (h : ModGL τ K) * q * (h : ModGL τ K)⁻¹ * (h : ModGL τ K) := by
                group
            _ = _ := this)
        exact h3
      rw [h2]
      exact hq
  have hP : (h : ModGL τ K) ∈ parabolicSubgroup τ K J := by
    rw [← adjointGroup_inf_normalizer_parabolicRadical]
    exact Subgroup.mem_inf.2 ⟨h.2, hN⟩
  have hC : (h : ModGL τ K) ∈ Subgroup.centralizer (parabolicRadical τ K J : Set (ModGL τ K)) :=
    Subgroup.mem_centralizer_iff.2 hcomm
  exact (Chevalley_proper_parabolic_root_radical_self_centralizing τ K hJ).2
    (Subgroup.mem_inf.2 ⟨hP, hC⟩)

variable [Finite K]

theorem exists_unit_rootCoord_conj_borel {c : ModGL τ K} (hc : c ∈ borelGroup τ K)
    (k : Fin τ.rank) :
    ∃ χ : Kˣ, ∀ (s : K) (m : Fin τ.rank),
      rootCoord (single_pos m) (c * xUnit τ K k s * c⁻¹) = if k = m then (χ : K) * s else 0 := by
  have hc' : c ∈ (borelGroup τ K : Set (ModGL τ K)) := hc
  rw [(triangular_borel_structure.{0, 0} τ K).2.2.2.2.2.1] at hc'
  obtain ⟨u, hu, t, ht, rfl⟩ := hc'
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  refine ⟨b k, fun s m => ?_⟩
  have e : u * rootDiagUnit τ b * xUnit τ K k s * (u * rootDiagUnit τ b)⁻¹ =
      u * (rootDiagUnit τ b * xUnit τ K k s * (rootDiagUnit τ b)⁻¹) * u⁻¹ := by group
  have e2 : rootDiagUnit τ b * xUnit τ K k s * (rootDiagUnit τ b)⁻¹ =
      xUnit τ K k ((b k : K) * s) := by
    rw [← pinnedX_single τ K k s, rootDiagUnit_conj_pinnedX b (isRoot_single τ k), rootChar_single,
      pinnedX_single]
  rw [e, e2, rootCoord_conj _ hu (mem_heightSeries_single (xUnit_mem_posUnipotent k _) m),
    rootCoord_single_xUnit]

omit [Finite K] in
theorem coe_apply_mem_posUnipotent {J : Set (Fin τ.rank)} (hJ : J ≠ Set.univ)
    {α : MulAut (adjointGroup τ K)}
    (hα : ∀ x : adjointGroup τ K, (x : ModGL τ K) ∈ parabolicRadical τ K J → α x = x)
    (u : adjointGroup τ K) (hu : (u : ModGL τ K) ∈ posUnipotent τ K) :
    ((α u : adjointGroup τ K) : ModGL τ K) ∈ posUnipotent τ K := by
  have h := inv_mul_apply_mem_parabolicRadical hJ hα u (posUnipotent_le_parabolicSubgroup J hu)
  have e : ((α u : adjointGroup τ K) : ModGL τ K) =
      (u : ModGL τ K) * ((u⁻¹ * α u : adjointGroup τ K) : ModGL τ K) := by
    simp
  rw [e]
  exact mul_mem hu (parabolicRadical_le_posUnipotent J h)

theorem mem_borelGroup_of_fixes_radical {J : Set (Fin τ.rank)} (hJ : J ≠ Set.univ)
    {α N : MulAut (adjointGroup τ K)} (hN : N ∈ unipotentPairAut τ K) {c : adjointGroup τ K}
    (hαN : α = MulAut.conj c * N)
    (hα : ∀ x : adjointGroup τ K, (x : ModGL τ K) ∈ parabolicRadical τ K J → α x = x) :
    (c : ModGL τ K) ∈ borelGroup τ K := by
  have hle : ∀ v : ModGL τ K, v ∈ posUnipotent τ K →
      (c : ModGL τ K) * v * (c : ModGL τ K)⁻¹ ∈ posUnipotent τ K := by
    intro v hv
    set v' : adjointGroup τ K := ⟨v, posUnipotent_le_adjointGroup hv⟩ with hv'
    have hu' : ((N⁻¹ v' : adjointGroup τ K) : ModGL τ K) ∈ posUnipotent τ K :=
      Subgroup.mem_subgroupOf.1 (apply_mem_of_mem_pairAut (inv_mem hN)
        (Subgroup.mem_subgroupOf.2 hv))
    have h1 := coe_apply_mem_posUnipotent hJ hα (N⁻¹ v') hu'
    have e : α (N⁻¹ v') = c * v' * c⁻¹ := by
      rw [hαN]
      simp [hv']
    rw [e] at h1
    exact h1
  have hmap : (posUnipotent τ K).map (MulAut.conj (c : ModGL τ K)).toMonoidHom ≤
      posUnipotent τ K := by
    rintro _ ⟨v, hv, rfl⟩
    exact hle v hv
  have heq := Subgroup.eq_of_le_of_card_ge hmap (by
    rw [Subgroup.card_map_of_injective (MulAut.conj (c : ModGL τ K)).injective])
  have hnorm : (c : ModGL τ K) ∈ Subgroup.normalizer (posUnipotent τ K : Set (ModGL τ K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro v
    constructor
    · exact hle v
    · intro hv
      rw [← heq] at hv
      obtain ⟨w, hw, hwv⟩ := hv
      have : w = v := by
        have h2 : (c : ModGL τ K) * w * (c : ModGL τ K)⁻¹ =
            (c : ModGL τ K) * v * (c : ModGL τ K)⁻¹ := hwv
        simpa using h2
      rwa [← this]
  rw [← (borel_self_normalizers τ K).1]
  exact Subgroup.mem_inf.2 ⟨c.2, hnorm⟩

theorem mem_diagonalFieldActors_E6_of_fixes_radical {J : Set (Fin Tag.E6.rank)}
    (hJ : J ≠ Set.univ) {α : MulAut (adjointGroup Tag.E6 K)}
    (hα : ∀ x : adjointGroup Tag.E6 K, (x : ModGL Tag.E6 K) ∈ parabolicRadical Tag.E6 K J →
      α x = x) :
    α ∈ diagonalFieldActors Tag.E6 K := by
  obtain ⟨c, a, σ, ε, hαN⟩ := exists_conj_mul_exactNormalAut (K := K) (τ := Tag.E6) (Or.inl rfl) α
  have hN := exactNormalAut_mem (τ := Tag.E6) (K := K) a σ (ε : ℕ)
  have hc := mem_borelGroup_of_fixes_radical hJ hN hαN hα
  obtain ⟨ε, hε⟩ := ε
  have hε2 : ε = 0 ∨ ε = 1 := by
    have : exactE Tag.E6 = 2 := rfl
    omega
  rcases hε2 with rfl | rfl
  · refine (EvenExceptionalActorCoverage.mem_diagonalFieldActors_iff α).2
      ⟨c, c.2, a, σ, fun x => ?_⟩
    rw [hαN, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      coe_exactNormalAut, exactQ_zero, Subgroup.coe_inv]
    group
  · exfalso
    set ρ := exactPerm Tag.E6 1 with hρ
    have hρ0 : ρ ⟨0, by decide⟩ = ⟨5, by decide⟩ := by
      rw [hρ]; decide
    have hρ5 : ρ ⟨5, by decide⟩ = ⟨0, by decide⟩ := by
      rw [hρ]; decide
    have key : ∀ i : Fin Tag.E6.rank,
        rootCoord (single_pos (ρ i)) ((α (adjX Tag.E6 K i 1) : adjointGroup Tag.E6 K) :
          ModGL Tag.E6 K) ≠ 0 := by
      intro i
      obtain ⟨χ, hχ⟩ := exists_unit_rootCoord_conj_borel hc (ρ i)
      have e : ((α (adjX Tag.E6 K i 1) : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
          (c : ModGL Tag.E6 K) * xUnit Tag.E6 K (ρ i) ((a (ρ i) : K) * σ 1) *
            (c : ModGL Tag.E6 K)⁻¹ := by
        rw [hαN, MulAut.mul_apply, MulAut.conj_apply, exactNormalAut_adjX]
        rfl
      rw [e, hχ]
      simp only [↓reduceIte, map_one, mul_one]
      exact mul_ne_zero χ.ne_zero (a (ρ i)).ne_zero
    have claim1 : ∀ j : Fin Tag.E6.rank, j ∉ J → ρ j = j := by
      intro j hj
      have hfix := hα (adjX Tag.E6 K j 1) (xUnit_mem_parabolicRadical hj 1)
      have h1 := key j
      rw [hfix] at h1
      change rootCoord _ (xUnit Tag.E6 K j 1) ≠ 0 at h1
      rw [rootCoord_single_xUnit] at h1
      by_contra hne
      exact h1 (by simp [Ne.symm hne])
    have claim2 : ∀ i : Fin Tag.E6.rank, i ∈ J → ρ i ∈ J → ρ i = i := by
      intro i hi hρi
      have hh := inv_mul_apply_mem_parabolicRadical hJ hα (adjX Tag.E6 K i 1)
        (posUnipotent_le_parabolicSubgroup J (xUnit_mem_posUnipotent i 1))
      have e : ((α (adjX Tag.E6 K i 1) : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
          xUnit Tag.E6 K i 1 * (((adjX Tag.E6 K i 1)⁻¹ * α (adjX Tag.E6 K i 1) :
            adjointGroup Tag.E6 K) : ModGL Tag.E6 K) := by
        simp [adjX]
      have hsub : parabolicRadicalRoots Tag.E6 J ⊆ coordKerRoots (Pi.single (ρ i) 1 :
          Fin Tag.E6.rank → ℤ) := by
        intro β hβ
        obtain ⟨hr, hpos, j, hj, hβj⟩ := mem_parabolicRadicalRoots_iff.1 hβ
        refine ⟨hr, hpos, by rw [height_single]; omega, ?_⟩
        rintro rfl
        have : j = ρ i := by
          by_contra hne
          exact hβj (Pi.single_eq_of_ne hne 1)
        exact hj (this ▸ hρi)
      have h0 : rootCoord (single_pos (ρ i)) (((adjX Tag.E6 K i 1)⁻¹ * α (adjX Tag.E6 K i 1) :
          adjointGroup Tag.E6 K) : ModGL Tag.E6 K) = 0 :=
        rootCoord_of_mem_coordKer _ (rootSpan_mono hsub hh)
      have h1 := key i
      rw [e, rootCoord_mul _ (mem_heightSeries_single (xUnit_mem_posUnipotent i 1) _)
        (mem_heightSeries_single (parabolicRadical_le_posUnipotent J hh) _), h0, add_zero,
        rootCoord_single_xUnit] at h1
      by_contra hne
      exact h1 (by simp [Ne.symm hne])
    by_cases h0 : (⟨0, by decide⟩ : Fin Tag.E6.rank) ∈ J
    · by_cases h5 : (⟨5, by decide⟩ : Fin Tag.E6.rank) ∈ J
      · have := claim2 ⟨0, by decide⟩ h0 (by rw [hρ0]; exact h5)
        rw [hρ0] at this
        exact absurd this (by decide)
      · have := claim1 ⟨5, by decide⟩ h5
        rw [hρ5] at this
        exact absurd this (by decide)
    · have := claim1 ⟨0, by decide⟩ h0
      rw [hρ0] at this
      exact absurd this (by decide)

section PChar

open Subgroup CFSG.GH74.GLS.Stage2.OddAut

theorem pCharData_adjoint_top (τ : Tag) (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime]
    [CharP K p]
    (hact : ∀ {J : Set (Fin τ.rank)}, J ≠ Set.univ → ∀ α : MulAut (adjointGroup τ K),
      (∀ x : adjointGroup τ K, (x : ModGL τ K) ∈ parabolicRadical τ K J → α x = x) →
        α ∈ diagonalFieldActors τ K) :
    PCharData (adjointGroup τ K) p ⊤ := by
  classical
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element τ
  obtain ⟨⟨U, hU⟩, -⟩ := exceptional_ordinary_Sylow_opposition τ K p w₀ hw₀
  have hB := borel_self_normalizers τ K
  have hBC : borelGroup τ K ≤ adjointGroup τ K := by
    rw [← hB.1]
    exact inf_le_left
  have hBN : ∀ b ∈ borelGroup τ K,
      b ∈ Subgroup.normalizer (posUnipotent τ K : Set (ModGL τ K)) := by
    intro b hb
    rw [← hB.1] at hb
    exact hb.2
  refine PCharData.of_standard (A := ⊤) (fun _ _ => Subgroup.mem_top _) U ?_
  intro P hNP hPtop
  have hBle : borelGroup τ K ≤ P.map (adjointGroup τ K).subtype := by
    intro b hb
    have hbC : b ∈ adjointGroup τ K := hBC hb
    have hbN : (⟨b, hbC⟩ : adjointGroup τ K) ∈
        Subgroup.normalizer ((U : Subgroup (adjointGroup τ K)) : Set (adjointGroup τ K)) := by
      rw [hU, Subgroup.mem_normalizer_iff]
      intro u
      have := Subgroup.mem_normalizer_iff.1 (hBN b hb) (u : ModGL τ K)
      constructor
      · intro hu
        exact Subgroup.mem_subgroupOf.2 (this.1 (Subgroup.mem_subgroupOf.1 hu))
      · intro hu
        exact Subgroup.mem_subgroupOf.2 (this.2 (Subgroup.mem_subgroupOf.1 hu))
    exact ⟨_, hNP hbN, rfl⟩
  have hP'C : P.map (adjointGroup τ K).subtype ≤ adjointGroup τ K := Subgroup.map_subtype_le _
  have hcl := (borel_overgroup_classification τ K).1 _ hBle hP'C
  set P' : Subgroup (ModGL τ K) := P.map (adjointGroup τ K).subtype with hP'
  set J : Set (Fin τ.rank) := {i | weylElt τ K i 1 ∈ P'} with hJdef
  have hJ : J ≠ Set.univ := by
    intro h
    apply hPtop
    have hP'top : P' = adjointGroup τ K := by
      rw [hcl, h, (standard_parabolic_cells τ K).2.2.2.2.2.1]
    rw [eq_top_iff]
    intro x _
    have hx : (x : ModGL τ K) ∈ P' := by rw [hP'top]; exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  have hLevi := parabolic_root_radical_Levi_factors τ K J
  have hPJ : ∀ y : adjointGroup τ K, y ∈ P → (y : ModGL τ K) ∈ parabolicSubgroup τ K J := by
    intro y hy
    rw [← hcl]
    exact ⟨y, hy, rfl⟩
  have hQP : parabolicRadicalIn τ K J ≤ P := by
    intro x hx
    have h1 : (x : ModGL τ K) ∈ parabolicSubgroup τ K J := hLevi.1 (mem_parabolicRadicalIn.1 hx)
    rw [← hcl] at h1
    obtain ⟨y, hy, hyx⟩ := h1
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  have hQn : ((parabolicRadicalIn τ K J).subgroupOf P).Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hxQ : ((x : adjointGroup τ K) : ModGL τ K) ∈ parabolicRadical τ K J :=
      mem_parabolicRadicalIn.1 (Subgroup.mem_subgroupOf.1 hx)
    have hxP : ((x : adjointGroup τ K) : ModGL τ K) ∈ parabolicSubgroup τ K J := hLevi.1 hxQ
    have hgP := hPJ (g : adjointGroup τ K) g.2
    have key := hLevi.2.1.conj_mem
      (⟨((x : adjointGroup τ K) : ModGL τ K), hxP⟩ : ↥(parabolicSubgroup τ K J))
      (Subgroup.mem_subgroupOf.2 hxQ) ⟨((g : adjointGroup τ K) : ModGL τ K), hgP⟩
    have key' := Subgroup.mem_subgroupOf.1 key
    refine Subgroup.mem_subgroupOf.2 (mem_parabolicRadicalIn.2 ?_)
    simpa using key'
  have hQC : parabolicRadical τ K J ≤ adjointGroup τ K := parabolicRadical_le_adjointGroup J
  have hQp : IsPGroup p (parabolicRadicalIn τ K J) := by
    obtain ⟨-, hQp, -⟩ := hLevi.2.2.2.2.2.2.2.2.2.2.2.2 p
    exact hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQC).symm
  have hrigL :=
    (exact_parabolic_diagonal_field_normalizers_characteristic_p_ordinary (p := p) τ K hJ).2.2.2.1
  refine ⟨parabolicRadicalIn τ K J, hQP, hQn, hQp, fun α hαA hfix => ?_⟩
  obtain ⟨z, ⟨z', hz', hzz⟩, hzα⟩ := (hrigL α).1
    ⟨hact hJ α fun x hx => hfix x (mem_parabolicRadicalIn.2 hx), hfix⟩
  have hzQ : z ∈ parabolicRadicalIn τ K J := by
    rw [← hzz]
    exact z'.2
  exact ⟨z, hzQ, hzα⟩

end PChar

theorem mem_diagonalFieldActors_of_E7_E8 (hτ : τ = .E7 ∨ τ = .E8) (α : MulAut (adjointGroup τ K)) :
    α ∈ diagonalFieldActors τ K := by
  obtain ⟨g, a, σ, ε, hα⟩ := (ordinary_E_exact_automorphism_normal_form τ
    (by rcases hτ with rfl | rfl <;> simp) K).2.2 α
  have hε : (ε : ℕ) = 0 := by
    have h1 : exactE τ = 1 := by rcases hτ with rfl | rfl <;> rfl
    have := ε.2
    omega
  refine (EvenExceptionalActorCoverage.mem_diagonalFieldActors_iff α).2 ⟨g, g.2, a, σ, fun x => ?_⟩
  rw [hα x, hε, exactQ_zero]
  group


section Main

open CFSG.Open CFSG.LieType.BorelTits CFSG.GH74.GLS.Stage2.OddAut
  CFSG.HardMathSupport.Solomon.LocalBalance

theorem gLAPPrimeCoreOf_centralizer_eq_bot_adjoint_E (τ : Tag) (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (hact : ∀ {J : Set (Fin τ.rank)}, J ≠ Set.univ → ∀ α : MulAut (adjointGroup τ K),
      (∀ x : adjointGroup τ K, (x : ModGL τ K) ∈ parabolicRadical τ K J → α x = x) →
        α ∈ diagonalFieldActors τ K)
    (H : Subgroup (MulAut (adjointGroup τ K))) (hH : innerAut (adjointGroup τ K) ≤ H)
    {x : MulAut (adjointGroup τ K)} (hx : x ∈ innerAut (adjointGroup τ K)) (hxo : orderOf x = p) :
    GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({x} : Set (MulAut (adjointGroup τ K)))) = ⊥ := by
  have hcen := center_adjointGroup_eq_bot (τ := τ) (K := K)
  exact gLAPPrimeCoreOf_centralizer_eq_bot_of_parCharP (holds_adjointGroup_tag τ K p) hcen
    (parCharP_of_data hcen (pCharData_adjoint_top τ K p hact)) (A := ⊤) le_top hH hx hxo

theorem innerCoreFree_of_bridge_E {τ : Tag}
    (hact : ∀ (K : Type) [Field K] [Finite K] {J : Set (Fin τ.rank)}, J ≠ Set.univ →
      ∀ α : MulAut (adjointGroup τ K),
      (∀ x : adjointGroup τ K, (x : ModGL τ K) ∈ parabolicRadical τ K J → α x = x) →
        α ∈ diagonalFieldActors τ K)
    {c : TauCeti.PrimePower → TauCeti.LieTypeIndex} (hbr : CFSG.TauCetiBridge.UntwistedBridge τ c)
    (q : TauCeti.PrimePower) (hv : (c q).Valid) (S : Type) [Group S]
    (e0 : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨c q, hv⟩) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p = q.p) :
    ∀ x ∈ innerAut S, orderOf x = p → ∀ H : Subgroup (MulAut S), innerAut S ≤ H →
      GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({x} : Set (MulAut S))) = ⊥ := by
  intro x hx hxo H hH
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hKq : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card _ _ q.exponent_pos.ne'
  have hq2 : q.p ≠ 2 := hpq ▸ hp2
  obtain ⟨eB⟩ := hbr q hv hq2 (GaloisField q.p q.exponent)
    (by rw [hKq]; simp [TauCeti.PrimePower.card_def])
  let e : S ≃* adjointGroup τ (GaloisField q.p q.exponent) :=
    e0.trans (eB.symm.trans adjointEquivQuotient.symm)
  have hKchar : CharP (GaloisField q.p q.exponent) q.p := inferInstance
  have hpc : Fact p.Prime := ⟨hp⟩
  subst hpq
  refine gLAPPrimeCoreOf_inf_centralizer_of_congr_E q.p e H x ?_
  have hS : (MulAut.congr e) x ∈ innerAut (adjointGroup τ (GaloisField q.p q.exponent)) := by
    obtain ⟨g, rfl⟩ := hx
    refine ⟨e g, ?_⟩
    ext y
    simp [MulAut.congr_apply, MulAut.conj_apply]
  refine gLAPPrimeCoreOf_centralizer_eq_bot_adjoint_E τ _ q.p (hact _) _ ?_ hS ?_
  · rintro _ ⟨g, rfl⟩
    refine ⟨MulAut.conj (e.symm g), hH ⟨e.symm g, rfl⟩, ?_⟩
    ext y
    simp [MulAut.congr_apply, MulAut.conj_apply]
  · rw [MulEquiv.orderOf_eq]
    exact hxo

end Main

section Families

theorem defCharInnerCoreFreeFamE6 : DefCharInnerCoreFreeFam .E6 := by
  intro S _ _ _ _ idx hidx hS p hp hp2 hch x hx hxo H hH
  obtain ⟨q, hq⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hq
  subst hq
  obtain ⟨e0⟩ := hS
  have hpq : p = q.p := by simpa using hch.symm
  exact innerCoreFree_of_bridge_E (τ := .E6)
    (fun K _ _ J hJ α hα => mem_diagonalFieldActors_E6_of_fixes_radical hJ hα)
    CFSG.TauCetiBridge.chevalleyBridges.e6 q hv S e0 hp hp2 hpq x hx hxo H hH

theorem defCharInnerCoreFreeFamE7 : DefCharInnerCoreFreeFam .E7 := by
  intro S _ _ _ _ idx hidx hS p hp hp2 hch x hx hxo H hH
  obtain ⟨q, hq⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hq
  subst hq
  obtain ⟨e0⟩ := hS
  have hpq : p = q.p := by simpa using hch.symm
  exact innerCoreFree_of_bridge_E (τ := .E7)
    (fun K _ _ J hJ α hα => mem_diagonalFieldActors_of_E7_E8 (Or.inl rfl) α)
    CFSG.TauCetiBridge.chevalleyBridges.e7 q hv S e0 hp hp2 hpq x hx hxo H hH

theorem defCharInnerCoreFreeFamE8 : DefCharInnerCoreFreeFam .E8 := by
  intro S _ _ _ _ idx hidx hS p hp hp2 hch x hx hxo H hH
  obtain ⟨q, hq⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hq
  subst hq
  obtain ⟨e0⟩ := hS
  have hpq : p = q.p := by simpa using hch.symm
  exact innerCoreFree_of_bridge_E (τ := .E8)
    (fun K _ _ J hJ α hα => mem_diagonalFieldActors_of_E7_E8 (Or.inr rfl) α)
    CFSG.TauCetiBridge.chevalleyBridges.e8 q hv S e0 hp hp2 hpq x hx hxo H hH

end Families


end CFSG.HardMathSupport.Timmesfeld.DefChar
