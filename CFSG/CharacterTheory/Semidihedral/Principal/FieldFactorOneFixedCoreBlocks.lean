module

public import CFSG.CharacterTheory.Semidihedral.Principal.FreeSixCharacterDefectFour
public import CFSG.CharacterTheory.Semidihedral.Principal.TwoLinearLocalBlocks
public import CFSG.CharacterTheory.Semidihedral.Principal.DefectKleinFourExactOrder
public import CFSG.CharacterTheory.Semidihedral.StationaryOddLocalization

public section

open scoped Classical

namespace CFSG.Semidihedral.Principal.FieldFactorOneFixedCore

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal CFSG.Semidihedral.Principal.FreeSix

variable {G : Type} [Group G]

theorem exists_conj_eq_of_mem_dV {V E : Subgroup G} (hED : E ≤ dV V)
    (hDVE : ∀ x ∈ dV V, ∃ v ∈ V, ∃ e ∈ E, x = v * e) {d : G} (hd : d ∈ dV V) :
    ∃ e₀ ∈ E, ∀ e ∈ E, d⁻¹ * e * d = e₀⁻¹ * e * e₀ := by
  obtain ⟨v, hv, e₀, he₀, rfl⟩ := hDVE d hd
  refine ⟨e₀, he₀, fun e he => ?_⟩
  have hve : v * e = e * v := Subgroup.mem_centralizer_iff.mp (hED he) v hv
  calc (v * e₀)⁻¹ * e * (v * e₀) = e₀⁻¹ * (v⁻¹ * (e * v)) * e₀ := by group
    _ = e₀⁻¹ * (v⁻¹ * (v * e)) * e₀ := by rw [hve]
    _ = e₀⁻¹ * e * e₀ := by group

theorem linear_conj_eq_of_mem_dV {V E : Subgroup G} (hED : E ≤ dV V)
    (hDVE : ∀ x ∈ dV V, ∃ v ∈ V, ∃ e ∈ E, x = v * e) (μ : E →* ℂˣ) {d : G} (hd : d ∈ dV V)
    (e e' : E) (he' : (e' : G) = d⁻¹ * e * d) : μ e' = μ e := by
  obtain ⟨e₀, he₀, hconj⟩ := exists_conj_eq_of_mem_dV hED hDVE hd
  have h : e' = (⟨e₀, he₀⟩ : E)⁻¹ * e * ⟨e₀, he₀⟩ := Subtype.ext (by
    rw [he', hconj e e.2]
    rfl)
  rw [h, map_mul, map_mul, map_inv, mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]

theorem eq_or_eq_conj_of_mem_linearOrbit {V E K : Subgroup G} (hED : E ≤ dV V)
    (hDVE : ∀ x ∈ dV V, ∃ v ∈ V, ∃ e ∈ E, x = v * e) {y : G}
    (hK : ∀ x ∈ K, x ∈ dV V ∨ y⁻¹ * x ∈ dV V)
    {μ ν : E →* ℂˣ} (hν : ν ∈ linearOrbit E μ (K : Set G)) :
    ν = μ ∨ ∀ e e' : E, (e' : G) = y⁻¹ * e * y → ν e = μ e' := by
  obtain ⟨x, hxK, hνx⟩ := hν
  rcases hK x hxK with hD | hD
  · left
    refine MonoidHom.ext fun e => ?_
    obtain ⟨e₀, he₀, hconj⟩ := exists_conj_eq_of_mem_dV hED hDVE hD
    have hmem : x⁻¹ * (e : G) * x ∈ E := by
      rw [hconj e e.2]
      exact E.mul_mem (E.mul_mem (E.inv_mem he₀) e.2) he₀
    rw [hνx e ⟨_, hmem⟩ rfl]
    exact linear_conj_eq_of_mem_dV hED hDVE μ hD e ⟨_, hmem⟩ rfl
  · right
    intro e e' he'
    set d := y⁻¹ * x with hd
    obtain ⟨e₀, he₀, hconj⟩ := exists_conj_eq_of_mem_dV hED hDVE hD
    have hx : x = y * d := by rw [hd, mul_inv_cancel_left]
    have hmem : x⁻¹ * (e : G) * x ∈ E := by
      have h1 : x⁻¹ * (e : G) * x = d⁻¹ * (e' : G) * d := by rw [he', hx]; group
      rw [h1, hconj e' e'.2]
      exact E.mul_mem (E.mul_mem (E.inv_mem he₀) e'.2) he₀
    rw [hνx e ⟨_, hmem⟩ rfl]
    refine linear_conj_eq_of_mem_dV hED hDVE μ hD e' ⟨_, hmem⟩ ?_
    change x⁻¹ * (e : G) * x = d⁻¹ * (e' : G) * d
    rw [he', hx]
    group

theorem exists_inflation_of_mem_linearOrbit [Finite G] {V E : Subgroup G} (hV : IsKleinFour V)
    (hED : E ≤ dV V) (hDVE : ∀ x ∈ dV V, ∃ v ∈ V, ∃ e ∈ E, x = v * e)
    (hEodd : Odd (Nat.card E)) (ω : dV V →* ℂˣ) (hωV : ∀ x : dV V, (x : G) ∈ V → ω x = 1)
    {μ' : E →* ℂˣ} (hμ' : μ' ∈ linearOrbit E (ω.comp (Subgroup.inclusion hED)) (mV V : Set G)) :
    ∃ ν : dV V →* ℂˣ,
      ∀ (x : dV V) (v : G) (e : E), v ∈ V → (x : G) = v * e → ν x = μ' e := by
  obtain ⟨m, hm, hνm⟩ := hμ'
  refine ⟨ω.comp (dConj hm), fun x v e hv hx => ?_⟩
  have hv' : m⁻¹ * v * m ∈ V := by
    have h' := (Subgroup.mem_normalizer_iff.mp ((mV V).inv_mem hm) v).mp hv
    rwa [inv_inv] at h'
  have he' : m⁻¹ * (e : G) * m ∈ E := by
    have h' := conj_mem_of_mem hV hED hDVE hEodd ((mV V).inv_mem hm) e.2
    rwa [inv_inv] at h'
  have hsplit : dConj hm x = (⟨m⁻¹ * v * m, le_dV hV hv'⟩ : dV V) *
      ⟨m⁻¹ * e * m, hED he'⟩ := by
    apply Subtype.ext
    change m⁻¹ * (x : G) * m = m⁻¹ * v * m * (m⁻¹ * e * m)
    rw [hx]
    group
  rw [MonoidHom.comp_apply, hsplit, map_mul, hωV _ hv', one_mul,
    hνm e ⟨m⁻¹ * e * m, he'⟩ rfl]
  rfl

theorem closure_pair_cT_eq_subgroupOf {t s : G} (hs : s ∈ cT t) :
    Subgroup.closure ({⟨t, element_mem_centralizer_zpowers t⟩, ⟨s, hs⟩} : Set (cT t)) =
      (Subgroup.closure ({t, s} : Set G)).subgroupOf (cT t) := by
  have hle : Subgroup.closure ({t, s} : Set G) ≤ cT t := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact element_mem_centralizer_zpowers x
    · exact hs
  apply Subgroup.map_injective (cT t).subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le hle, MonoidHom.map_closure, Set.image_pair]
  rfl

theorem card_centralizer_cT (t s : G) (hs : s ∈ cT t) :
    Nat.card (Subgroup.centralizer ({⟨s, hs⟩} : Set (cT t))) =
      Nat.card (Subgroup.centralizer ({t} : Set G) ⊓
        Subgroup.centralizer ({s} : Set G) : Subgroup G) := by
  have hmap : (Subgroup.centralizer ({⟨s, hs⟩} : Set (cT t))).map (cT t).subtype =
      Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({s} : Set G) := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.coe_subtype, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨?_, congrArg Subtype.val hy⟩
      exact (Subgroup.mem_centralizer_iff.mp y.2 t (Subgroup.mem_zpowers t)).symm
    · rintro ⟨hxt, hxs⟩
      refine ⟨⟨x, ?_⟩, Subtype.ext hxs, rfl⟩
      show x ∈ Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)
      rw [StationaryOddLocalization.centralizer_zpowers_eq]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hxt
  rw [← hmap, Subgroup.card_map_of_injective (cT t).subtype_injective]

theorem blocksIrr_comp_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {χ : Y → ℂ}
    (hχ : χ ∈ CFSG.BlocksIrr Y) : χ ∘ e ∈ CFSG.BlocksIrr X := by
  obtain ⟨W, hW, hM, hF, ρ, hirr, rfl⟩ := hχ
  exact ⟨W, hW, hM, hF, ρ.comp e.toMonoidHom,
    CFSG.LyonsUnitaryFour.isIrreducible_comp_surjective e.toMonoidHom e.surjective ρ hirr, rfl⟩

theorem eq_one_or_eq_of_mem_zpowers_involution {g x : G} (hg : orderOf g = 2)
    (hx : x ∈ Subgroup.zpowers g) : x = 1 ∨ x = g := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← zpow_mod_orderOf, hg]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    simp only [Nat.cast_ofNat, h, zpow_zero]
  · right
    simp only [Nat.cast_ofNat, h, zpow_one]

theorem exists_block_four_characters [Fintype G] {V E : Subgroup G} (hV : IsKleinFour V)
    {t s y : G} (htV : t ∈ V) (hsV : s ∈ V) (hsC : s ∈ cT t) (hs2 : orderOf s = 2)
    (ht2 : orderOf t = 2) (hst : s ≠ t)
    (hcl : Subgroup.closure ({⟨t, element_mem_centralizer_zpowers t⟩, ⟨s, hsC⟩} : Set (cT t)) =
      V.subgroupOf (cT t))
    (hDmem : ∀ x : G, t * x = x * t → s * x = x * s → x ∈ dV V)
    (hED : E ≤ dV V) (hVE : V ⊓ E = ⊥) (hDVE : ∀ x ∈ dV V, ∃ v ∈ V, ∃ e ∈ E, x = v * e)
    (hEodd : Odd (Nat.card E)) (hyC : y ∈ cT t) (hyM : y ∈ mV V) (hys : y * s * y⁻¹ = t * s)
    (hK : ∀ x ∈ cT t ⊓ mV V, x ∈ dV V ∨ y⁻¹ * x ∈ dV V)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basisC : FiniteIrreducibleCharacterBasis (cT t)) (label : basisC.index)
    (hD : coefficientBlockDefect basisC ideal 2 label (V.subgroupOf (cT t)))
    (μ : E →* ℂˣ) (ν : dV V →* ℂˣ)
    (hν : ∀ (x : dV V) (v : G) (e : E), v ∈ V → (x : G) = v * e → ν x = μ e)
    (horbit : (linearOrbit E μ ((cT t ⊓ mV V : Subgroup G) : Set G)).ncard = 2)
    (hs : IsPGroup 2 (Subgroup.zpowers (⟨s, hsC⟩ : cT t)))
    (basisCs : FiniteIrreducibleCharacterBasis (Subgroup.centralizer
      (Subgroup.zpowers (⟨s, hsC⟩ : cT t) : Set (cT t))))
    {dec : DecidablePred fun n => ∃ ν' ∈ linearOrbit E μ ((cT t ⊓ mV V : Subgroup G) : Set G),
        AffordsInflation basisCs (fun x => ((x : cT t) : G)) V ν' n}
    (hfib : brauerFiberBlocks basisC ideal 2 ⟨s, hsC⟩ hs basisCs label =
      (@Finset.filter _ _ dec Finset.univ).image
        (coefficientBlock basisCs (localizedComplexIntegerRing ideal))) :
    ∃ (θ : Fin 4 → basisC.index) (f : ℕ), Function.Injective θ ∧
      coefficientBlock basisC (localizedComplexIntegerRing ideal) label =
        Finset.univ.image θ ∧
      0 < f ∧ (∀ i, Module.finrank ℂ (basisC.representation (θ i)).vector = f) ∧
      ((basisC.representation (θ 0)).character ⟨t, element_mem_centralizer_zpowers t⟩ = f ∧
        (basisC.representation (θ 1)).character ⟨t, element_mem_centralizer_zpowers t⟩ = f ∧
        (basisC.representation (θ 2)).character ⟨t, element_mem_centralizer_zpowers t⟩ =
          -(f : ℂ) ∧
        (basisC.representation (θ 3)).character ⟨t, element_mem_centralizer_zpowers t⟩ =
          -(f : ℂ)) ∧
      ((basisC.representation (θ 0)).character ⟨s, hsC⟩ = 2 ∧
        (basisC.representation (θ 1)).character ⟨s, hsC⟩ = -2 ∧
        (basisC.representation (θ 2)).character ⟨s, hsC⟩ = 0 ∧
        (basisC.representation (θ 3)).character ⟨s, hsC⟩ = 0) ∧
      (∀ x, x ∉ involutionLocalSection t →
        ((basisC.representation (θ 0)).character + (basisC.representation (θ 1)).character -
          (basisC.representation (θ 2)).character - (basisC.representation (θ 3)).character) x =
            0) ∧
      coefficientCharacterSpace basisC
          (coefficientBlock basisC (localizedComplexIntegerRing ideal) label) ⊓
          sectionSupported (involutionLocalSection t) =
        Submodule.span ℂ {(basisC.representation (θ 0)).character +
          (basisC.representation (θ 1)).character - (basisC.representation (θ 2)).character -
            (basisC.representation (θ 3)).character} := by
  have hEC : E ≤ cT t := hED.trans (dV_le_cT htV)
  let eE : E.subgroupOf (cT t) ≃* E := Subgroup.subgroupOfEquivOfLe hEC
  have heE : ∀ e, (eE e : G) = ((e : cT t) : G) := fun e => rfl
  have hyEmem : ∀ e ∈ E, y⁻¹ * e * y ∈ E := fun e he => by
    have h := conj_mem_of_mem hV hED hDVE hEodd ((mV V).inv_mem hyM) he
    rwa [inv_inv] at h
  let yConj : E →* E :=
    { toFun := fun e => ⟨y⁻¹ * e * y, hyEmem e e.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hyConj : ∀ e, (yConj e : G) = y⁻¹ * e * y := fun e => rfl
  let μ' : E.subgroupOf (cT t) →* ℂˣ := μ.comp eE.toMonoidHom
  let μ₁ : E →* ℂˣ := μ.comp yConj
  let μ₁' : E.subgroupOf (cT t) →* ℂˣ := μ₁.comp eE.toMonoidHom
  have hcentV : ∀ x : Subgroup.centralizer (Subgroup.zpowers (⟨s, hsC⟩ : cT t) : Set (cT t)),
      ((x : cT t) : G) ∈ dV V := by
    intro x
    apply hDmem
    · exact Subgroup.mem_centralizer_iff.mp (x : cT t).2 t (Subgroup.mem_zpowers t)
    · exact congrArg Subtype.val
        (Subgroup.mem_centralizer_iff.mp x.2 (⟨s, hsC⟩ : cT t)
          (Subgroup.mem_zpowers (⟨s, hsC⟩ : cT t)))
  let cHom : Subgroup.centralizer (Subgroup.zpowers (⟨s, hsC⟩ : cT t) : Set (cT t)) →* dV V :=
    { toFun := fun x => ⟨((x : cT t) : G), hcentV x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let ν₀ := ν.comp cHom
  let ν₁ := (ν.comp (dConj hyM)).comp cHom
  obtain ⟨n₀, hn₀⟩ := exists_label_of_hom basisCs ν₀
  obtain ⟨n₁, hn₁⟩ := exists_label_of_hom basisCs ν₁
  have hVmem : ∀ v : cT t,
      v ∈ Subgroup.closure ({(⟨t, element_mem_centralizer_zpowers t⟩ : cT t),
        (⟨s, hsC⟩ : cT t)} : Set (cT t)) ↔ (v : G) ∈ V := by
    intro v
    rw [hcl, Subgroup.mem_subgroupOf]
  have hWv : ∀ v ∈ V, y⁻¹ * v * y ∈ V := by
    intro v hv
    have h := (Subgroup.mem_normalizer_iff.mp ((mV V).inv_mem hyM) v).mp hv
    rwa [inv_inv] at h
  have hdec : ∀ x : Subgroup.centralizer (Subgroup.zpowers (⟨s, hsC⟩ : cT t) : Set (cT t)),
      ∃ v ∈ V, ∃ e : E, ((x : cT t) : G) = v * e := by
    intro x
    obtain ⟨v, hv, e, he, hx⟩ := hDVE _ (hcentV x)
    exact ⟨v, hv, ⟨e, he⟩, hx⟩
  have hν₀ : ∀ (x : Subgroup.centralizer (Subgroup.zpowers (⟨s, hsC⟩ : cT t) : Set (cT t)))
      (v : G) (e : E),
      v ∈ V → ((x : cT t) : G) = v * e → ν₀ x = μ e :=
    fun x v e hv hx => hν (cHom x) v e hv hx
  have hν₁ : ∀ (x : Subgroup.centralizer (Subgroup.zpowers (⟨s, hsC⟩ : cT t) : Set (cT t)))
      (v : G) (e : E),
      v ∈ V → ((x : cT t) : G) = v * e → ν₁ x = μ₁ e := by
    intro x v e hv hx
    refine hν _ (y⁻¹ * v * y) (yConj e) (hWv v hv) ?_
    change y⁻¹ * ((x : cT t) : G) * y = _
    rw [hx, hyConj]
    group
  have hμmem : μ ∈ linearOrbit E μ ((cT t ⊓ mV V : Subgroup G) : Set G) :=
    ⟨1, Subgroup.one_mem _, fun e e' he' => by
      rw [show e' = e from Subtype.ext (by rw [he']; group)]⟩
  have hμ₁mem : μ₁ ∈ linearOrbit E μ ((cT t ⊓ mV V : Subgroup G) : Set G) :=
    ⟨y, ⟨hyC, hyM⟩, fun e e' he' => by
      change μ (yConj e) = μ e'
      rw [show yConj e = e' from Subtype.ext he'.symm]⟩
  have horbit' : ∀ ν' ∈ linearOrbit E μ ((cT t ⊓ mV V : Subgroup G) : Set G),
      ν' = μ ∨ ν' = μ₁ := by
    intro ν' hν'
    rcases eq_or_eq_conj_of_mem_linearOrbit hED hDVE hK hν' with h | h
    · exact Or.inl h
    · exact Or.inr (MonoidHom.ext fun e => h e (yConj e) rfl)
  have hμne : μ₁' ≠ μ' := by
    intro h
    have h' : μ₁ = μ := by
      refine MonoidHom.ext fun e => ?_
      have := congrArg (fun χ : E.subgroupOf (cT t) →* ℂˣ => χ (eE.symm e)) h
      simpa [μ₁', μ'] using this
    have hsub : linearOrbit E μ ((cT t ⊓ mV V : Subgroup G) : Set G) ⊆ {μ} := by
      intro ν' hν'
      rcases horbit' ν' hν' with h1 | h1
      · exact h1
      · rw [h1, h']
        rfl
    have := Set.ncard_le_ncard hsub (Set.finite_singleton μ)
    rw [horbit, Set.ncard_singleton] at this
    omega
  have hfilter : (@Finset.filter _ _ dec Finset.univ) = {n₀, n₁} := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨ν', hν', hn⟩
      rcases horbit' ν' hν' with h | h
      · left
        apply basisCs.distinct
        funext x
        obtain ⟨v, hv, e, hx⟩ := hdec x
        change (basisCs.representation n).character x = (basisCs.representation n₀).character x
        rw [hn x v e hv hx, hn₀, h, hν₀ x v e hv hx]
      · right
        apply basisCs.distinct
        funext x
        obtain ⟨v, hv, e, hx⟩ := hdec x
        change (basisCs.representation n).character x = (basisCs.representation n₁).character x
        rw [hn x v e hv hx, hn₁, h, hν₁ x v e hv hx]
    · rintro (h | h) <;> rw [h]
      · exact ⟨μ, hμmem, fun x v e hv hx => by rw [hn₀, hν₀ x v e hv hx]⟩
      · exact ⟨μ₁, hμ₁mem, fun x v e hv hx => by rw [hn₁, hν₁ x v e hv hx]⟩
  have hfiber : brauerFiberBlocks basisC ideal 2 (⟨s, hsC⟩ : cT t) hs basisCs label =
      {coefficientBlock basisCs (localizedComplexIntegerRing ideal) n₀,
        coefficientBlock basisCs (localizedComplexIntegerRing ideal) n₁} := by
    rw [hfib, hfilter, Finset.image_insert, Finset.image_singleton]
  have htcent : ∀ g : cT t, g * (⟨t, element_mem_centralizer_zpowers t⟩ : cT t) =
      (⟨t, element_mem_centralizer_zpowers t⟩ : cT t) * g := fun g =>
    Subtype.ext (Subgroup.mem_centralizer_iff.mp g.2 t (Subgroup.mem_zpowers t)).symm
  have ht : orderOf (⟨t, element_mem_centralizer_zpowers t⟩ : cT t) = 2 := by
    rw [Subgroup.orderOf_mk]; exact ht2
  have hs2' : orderOf (⟨s, hsC⟩ : cT t) = 2 := by rw [Subgroup.orderOf_mk]; exact hs2
  have hst' : (⟨s, hsC⟩ : cT t) ≠ (⟨t, element_mem_centralizer_zpowers t⟩ : cT t) := fun h =>
    hst (congrArg Subtype.val h)
  have hEodd' : Odd (Nat.card (E.subgroupOf (cT t))) := by
    rw [Nat.card_congr eE.toEquiv]
    exact hEodd
  have hED' : E.subgroupOf (cT t) ≤
      Subgroup.centralizer (Subgroup.zpowers (⟨s, hsC⟩ : cT t) : Set (cT t)) := by
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    have hc : (⟨s, hsC⟩ : cT t) * e = e * (⟨s, hsC⟩ : cT t) :=
      Subtype.ext (Subgroup.mem_centralizer_iff.mp (hED he) s hsV)
    exact (Commute.zpow_left hc k).eq
  have hDVE' : ∀ x ∈ Subgroup.centralizer (Subgroup.zpowers (⟨s, hsC⟩ : cT t) : Set (cT t)),
      ∃ v ∈ Subgroup.closure ({(⟨t, element_mem_centralizer_zpowers t⟩ : cT t),
        (⟨s, hsC⟩ : cT t)} : Set (cT t)),
        ∃ e ∈ E.subgroupOf (cT t), x = v * e := by
    intro x hx
    obtain ⟨v, hv, e, hxe⟩ := hdec ⟨x, hx⟩
    refine ⟨⟨v, le_cT hV htV hv⟩, (hVmem _).mpr hv, ⟨e, hEC e.2⟩, e.2, ?_⟩
    exact Subtype.ext hxe
  have hVE' : Subgroup.closure ({(⟨t, element_mem_centralizer_zpowers t⟩ : cT t),
    (⟨s, hsC⟩ : cT t)} : Set (cT t)) ⊓ E.subgroupOf (cT t) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨h1, h2'⟩ := Subgroup.mem_inf.mp hx
    have hmem : (x : G) ∈ V ⊓ E := Subgroup.mem_inf.mpr ⟨(hVmem x).mp h1, h2'⟩
    rw [hVE, Subgroup.mem_bot] at hmem
    exact (Subgroup.mem_bot).mpr (Subtype.ext hmem)
  have hyV : (⟨y, hyC⟩ : cT t) ∈ Subgroup.normalizer
      (Subgroup.closure ({(⟨t, element_mem_centralizer_zpowers t⟩ : cT t),
        (⟨s, hsC⟩ : cT t)} : Set (cT t)) : Set (cT t)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [hVmem, hVmem]
    exact Subgroup.mem_normalizer_iff.mp hyM h
  have hys' : (⟨y, hyC⟩ : cT t) * (⟨s, hsC⟩ : cT t) * (⟨y, hyC⟩ : cT t)⁻¹
      = (⟨t, element_mem_centralizer_zpowers t⟩ : cT t) * (⟨s, hsC⟩ : cT t) := Subtype.ext hys
  have hμ₁ : ∀ e e' : E.subgroupOf (cT t),
      (e' : cT t) = (⟨y, hyC⟩ : cT t)⁻¹ * e * ⟨y, hyC⟩ → μ₁' e = μ' e' := by
    intro e e' he'
    change μ (yConj (eE e)) = μ (eE e')
    congr 1
    apply Subtype.ext
    rw [hyConj, heE, heE, he']
    rfl
  have hν₀' : ∀ (x : Subgroup.centralizer (Subgroup.zpowers (⟨s, hsC⟩ : cT t) : Set (cT t)))
      (v : cT t)
      (e : E.subgroupOf (cT t)),
      v ∈ Subgroup.closure ({(⟨t, element_mem_centralizer_zpowers t⟩ : cT t),
        (⟨s, hsC⟩ : cT t)} : Set (cT t)) →
        (x : cT t) = v * e → ν₀ x = μ' e := by
    intro x v e hv hx
    exact hν₀ x v (eE e) ((hVmem v).mp hv) (by rw [hx]; rfl)
  have hν₁' : ∀ (x : Subgroup.centralizer (Subgroup.zpowers (⟨s, hsC⟩ : cT t) : Set (cT t)))
      (v : cT t)
      (e : E.subgroupOf (cT t)),
      v ∈ Subgroup.closure ({(⟨t, element_mem_centralizer_zpowers t⟩ : cT t),
        (⟨s, hsC⟩ : cT t)} : Set (cT t)) →
        (x : cT t) = v * e → ν₁ x = μ₁' e := by
    intro x v e hv hx
    exact hν₁ x v (eE e) ((hVmem v).mp hv) (by rw [hx]; rfl)
  rw [← hcl] at hD
  obtain ⟨θ, f, hθinj, hθb, hf, hdeg, ht0, ht1, ht2', ht3, hs0, hs1, hs2'', hs3, -, -, hsupp, -,
      -, hspan, -, -⟩ :=
    central_involution_two_linear_local_blocks_four_characters_and_section_line basisC ideal
      (⟨t, element_mem_centralizer_zpowers t⟩ : cT t)
      (⟨s, hsC⟩ : cT t) htcent ht hs2' hst' hs basisCs (E.subgroupOf (cT t)) hEodd' hED' hDVE' hVE'
      ⟨y, hyC⟩ hyV hys' μ' μ₁' hμ₁ hμne ν₀ ν₁ hν₀' hν₁' n₀ n₁ hn₀ hn₁ label hD hfiber
  exact ⟨θ, f, hθinj, hθb, hf, hdeg, ⟨ht0, ht1, ht2', ht3⟩, ⟨hs0, hs1, hs2'', hs3⟩, hsupp, hspan⟩

theorem three_local_blocks_valuation [Fintype G] {V E : Subgroup G} (hV : IsKleinFour V)
    {t s y : G} (htV : t ∈ V) (hsV : s ∈ V) (ht1 : t ≠ 1) (ht2 : orderOf t = 2)
    (hs2 : orderOf s = 2) (hst : s ≠ t) (hsC : s ∈ cT t)
    (hcl : Subgroup.closure ({⟨t, element_mem_centralizer_zpowers t⟩, ⟨s, hsC⟩} : Set (cT t)) =
      V.subgroupOf (cT t))
    (hDmem : ∀ x : G, t * x = x * t → s * x = x * s → x ∈ dV V)
    (hED : E ≤ dV V) (hVE : V ⊓ E = ⊥) (hDVE : ∀ x ∈ dV V, ∃ v ∈ V, ∃ e ∈ E, x = v * e)
    (hEodd : Odd (Nat.card E)) (hyC : y ∈ cT t) (hyM : y ∈ mV V) (hys : y * s * y⁻¹ = t * s)
    (hK : ∀ x ∈ cT t ⊓ mV V, x ∈ dV V ∨ y⁻¹ * x ∈ dV V)
    (hAut : Function.Surjective V.normalizerMonoidHom)
    (hfour : ∀ U : Subgroup G, IsKleinFour U → t ∈ U → U ≤ cT t →
      ∃ c ∈ cT t, U.map (MulAut.conj c).toMonoidHom = V)
    (ω : dV V →* ℂˣ) (hωV : ∀ x : dV V, (x : G) ∈ V → ω x = 1)
    (hωstab : ∀ m ∈ mV V, (∀ x y : dV V, (y : G) = m⁻¹ * x * m → ω y = ω x) → m ∈ dV V)
    (hinv : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → IsConj x y)
    (hclasses : ∀ z : cT t, orderOf z = 2 →
      IsConj z ⟨t, element_mem_centralizer_zpowers t⟩ ∨ IsConj z ⟨s, hsC⟩)
    (p : ℕ) (hp : p.Prime)
    (hpdeg : ∀ (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
      [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
      (basisC : FiniteIrreducibleCharacterBasis (cT t)) (label : basisC.index),
      coefficientBlockDefect basisC ideal 2 label (V.subgroupOf (cT t)) →
      ∀ θ ∈ coefficientBlock basisC (localizedComplexIntegerRing ideal) label,
        ¬ p ∣ Module.finrank ℂ (basisC.representation θ).vector) :
    3 * (padicValNat p (Nat.card (cT t)) : ℤ) -
        2 * (padicValNat p (Nat.card (Subgroup.centralizer ({⟨s, hsC⟩} : Set (cT t)))) : ℤ) ≤
      padicValNat p (Nat.card G) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨basisM⟩ := finiteIrreducibleCharacterBasis_exists (G := mV V)
  obtain ⟨basisMD⟩ := finiteIrreducibleCharacterBasis_exists (G := dInM V)
  obtain ⟨basisEM⟩ := finiteIrreducibleCharacterBasis_exists (G := eInM V E)
  obtain ⟨basisC⟩ := finiteIrreducibleCharacterBasis_exists (G := cT t)
  obtain ⟨basisK⟩ := finiteIrreducibleCharacterBasis_exists (G := kInC V t)
  obtain ⟨basisKD⟩ := finiteIrreducibleCharacterBasis_exists (G := dInK V t)
  obtain ⟨basisCD⟩ := finiteIrreducibleCharacterBasis_exists (G := dInC V t)
  obtain ⟨⟨ideal, hmax, h2mem⟩, hchar⟩ :=
    CFSG.BlockBasics.residue_prime_existence 2 Nat.prime_two
  have : ideal.IsMaximal := hmax
  have : CharP (ComplexAlgebraicIntegers ⧸ ideal) 2 := hchar ideal hmax h2mem
  obtain ⟨-, -, -, -, -, -, μs, hμsΩ, hΩj2, -, -, A, Aj, B, b, -, -, -, -, -, -, hBdef, hbdef,
      hbinj, hfiber, -, hscl, -⟩ :=
    free_six_character_normalizer_orbit_defect_four_block basis ideal V hV t htV ht1 E hED hVE
      hDVE hEodd hAut hfour ω hωV hωstab basisM basisMD basisEM basisC basisK basisKD basisCD
  have hs2' : orderOf (⟨s, hsC⟩ : cT t) = 2 := by rw [Subgroup.orderOf_mk]; exact hs2
  have hst' : ((⟨s, hsC⟩ : cT t) : G) ≠ t := hst
  have hs : IsPGroup 2 (Subgroup.zpowers (⟨s, hsC⟩ : cT t)) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hs2', pow_one]
  have hsJ : ((⟨s, hsC⟩ : cT t) : G) ∉ Subgroup.zpowers t := by
    intro h
    rcases eq_one_or_eq_of_mem_zpowers_involution ht2 h with h' | h'
    · change s = 1 at h'
      rw [h', orderOf_one] at hs2
      exact absurd hs2 (by norm_num)
    · exact hst h'
  obtain ⟨-, hsfib⟩ := hscl ⟨s, hsC⟩ hsV hsJ
  obtain ⟨basisCs⟩ := finiteIrreducibleCharacterBasis_exists (G := Subgroup.centralizer
    (Subgroup.zpowers (⟨s, hsC⟩ : cT t) : Set (cT t)))
  obtain ⟨-, hfib⟩ := hsfib hs basisCs
  have hblock : ∀ j : Fin 3, ∃ (θ : Fin 4 → basisC.index) (fj : ℕ), Function.Injective θ ∧
      coefficientBlock basisC (localizedComplexIntegerRing ideal) (b j) =
        Finset.univ.image θ ∧
      0 < fj ∧ (∀ i, Module.finrank ℂ (basisC.representation (θ i)).vector = fj) ∧
      ((basisC.representation (θ 0)).character ⟨t, element_mem_centralizer_zpowers t⟩ = fj ∧
        (basisC.representation (θ 1)).character ⟨t, element_mem_centralizer_zpowers t⟩ = fj ∧
        (basisC.representation (θ 2)).character ⟨t, element_mem_centralizer_zpowers t⟩ =
          -(fj : ℂ) ∧
        (basisC.representation (θ 3)).character ⟨t, element_mem_centralizer_zpowers t⟩ =
          -(fj : ℂ)) ∧
      ((basisC.representation (θ 0)).character ⟨s, hsC⟩ = 2 ∧
        (basisC.representation (θ 1)).character ⟨s, hsC⟩ = -2 ∧
        (basisC.representation (θ 2)).character ⟨s, hsC⟩ = 0 ∧
        (basisC.representation (θ 3)).character ⟨s, hsC⟩ = 0) ∧
      (∀ x, x ∉ involutionLocalSection t →
        ((basisC.representation (θ 0)).character + (basisC.representation (θ 1)).character -
          (basisC.representation (θ 2)).character - (basisC.representation (θ 3)).character) x =
            0) ∧
      coefficientCharacterSpace basisC
          (coefficientBlock basisC (localizedComplexIntegerRing ideal) (b j)) ⊓
          sectionSupported (involutionLocalSection t) =
        Submodule.span ℂ {(basisC.representation (θ 0)).character +
          (basisC.representation (θ 1)).character - (basisC.representation (θ 2)).character -
            (basisC.representation (θ 3)).character} := by
    intro j
    obtain ⟨ν, hν⟩ := exists_inflation_of_mem_linearOrbit hV hED hDVE hEodd ω hωV (hμsΩ j)
    exact exists_block_four_characters hV htV hsV hsC hs2 ht2 hst hcl hDmem hED hVE hDVE hEodd
      hyC hyM hys hK ideal basisC (b j) (hbdef j) (μs j) ν hν (hΩj2 j) hs basisCs (hfib j)
  choose θ fd hθinj hθb hfd hθdeg hθt hθs hαsupp hαspan using hblock
  have hpf : ∀ j, ¬ p ∣ fd j := by
    intro j h
    have hmem : θ j 0 ∈ coefficientBlock basisC (localizedComplexIntegerRing ideal) (b j) := by
      rw [hθb j]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ 0)
    apply hpdeg ideal basisC (b j) (hbdef j) (θ j 0) hmem
    rw [hθdeg j 0]
    exact h
  have hpf3 : ¬ p ∣ fd 0 * fd 1 * fd 2 := by
    intro h
    rcases (Nat.Prime.dvd_mul hp).mp h with h' | h'
    · rcases (Nat.Prime.dvd_mul hp).mp h' with h'' | h''
      · exact hpf 0 h''
      · exact hpf 1 h''
    · exact hpf 2 h'
  have hbinj' : Function.Injective fun j =>
      coefficientBlock basisC (localizedComplexIntegerRing ideal) (b j) := by
    intro j k hjk
    by_contra hne
    exact hbinj j k hne hjk
  obtain ⟨-, Φ, hh, -, -, -, -, -, -, -, -, -, hval⟩ :=
    defect_klein_four_three_local_blocks_exact_nonprincipal_order basis ideal hinv t ht2
      (isPGroup_zpowers hV htV) basisC ⟨s, hsC⟩ hs2' hst' hclasses B V hV hBdef
      (fun j => coefficientBlock basisC (localizedComplexIntegerRing ideal) (b j)) hbinj'
      hfiber θ hθinj hθb fd hfd hθdeg hθt hθs hαsupp hαspan
  exact (hval p hp hpf3).2

end CFSG.Semidihedral.Principal.FieldFactorOneFixedCore
