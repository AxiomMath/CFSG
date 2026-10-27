module

public import CFSG.LocalAnalysis.ComponentClassification.GS82HConfigNorm
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinInteraction
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotIso
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBSharedCore

public section

namespace CFSG.ComponentClassification.GS82PumpInputs.P10

open CFSG Subgroup GSThmB.HConfig LocalAnalysis.ComponentInitial
open scoped commutatorElement

theorem center_eq_bot_of_mulEquiv' {S T : Type*} [Group S] [Group T] (e : S ≃* T)
    (h : center T = ⊥) : center S = ⊥ := by
  have h1 : (center S).map e.toMonoidHom = center T := Subgroup.map_center_eq e
  rw [h] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1

theorem eq_one_of_central_of_centerless {Q : Type*} [Group Q] (S : Finset (Subgroup Q))
    (hcomm : ∀ A ∈ S, ∀ A' ∈ S, A ≠ A' → ⁅A, A'⁆ = ⊥) (hZ : ∀ A ∈ S, center ↥A = ⊥) :
    ∀ z ∈ sSup (S : Set (Subgroup Q)),
      (∀ y ∈ sSup (S : Set (Subgroup Q)), y * z = z * y) → z = 1 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro z hz _
    simpa using hz
  | insert A S hAS ih =>
    intro z hz hzc
    have hcomm' : ∀ A ∈ S, ∀ A' ∈ S, A ≠ A' → ⁅A, A'⁆ = ⊥ := fun A₁ h₁ A₂ h₂ hne =>
      hcomm A₁ (Finset.mem_insert_of_mem h₁) A₂ (Finset.mem_insert_of_mem h₂) hne
    have hZ' : ∀ A ∈ S, center ↥A = ⊥ := fun A₁ h₁ => hZ A₁ (Finset.mem_insert_of_mem h₁)
    have hsup : sSup (((insert A S : Finset (Subgroup Q))) : Set (Subgroup Q)) =
        A ⊔ sSup (S : Set (Subgroup Q)) := by
      rw [Finset.coe_insert, sSup_insert]
    have hAS' : ⁅A, sSup (S : Set (Subgroup Q))⁆ = ⊥ := by
      rw [commutator_comm, commutator_eq_bot_iff_le_centralizer]
      refine sSup_le fun A' hA' => ?_
      rw [← commutator_eq_bot_iff_le_centralizer, commutator_comm]
      exact hcomm A (Finset.mem_insert_self A S) A' (Finset.mem_insert_of_mem hA')
        (fun h => hAS (h ▸ hA'))
    rw [hsup] at hz hzc
    have hz' : z ∈ ((A ⊔ sSup (S : Set (Subgroup Q)) : Subgroup Q) : Set Q) := hz
    rw [coe_sup_of_commutator_eq_bot hAS'] at hz'
    obtain ⟨a, ha, e, he, rfl⟩ := hz'
    have ha1 : a = 1 := by
      have hmem : (⟨a, ha⟩ : ↥A) ∈ center ↥A := by
        rw [mem_center_iff]
        intro x
        have h1 := hzc x (mem_sup_left x.2)
        have hxe : (x : Q) * e = e * x := (commute_of_commutator_eq_bot' hAS' x.2 he).eq
        apply Subtype.ext
        change (x : Q) * a = a * x
        have h2 : (x : Q) * a * e = a * x * e := by
          calc (x : Q) * a * e = x * (a * e) := by group
            _ = a * e * x := h1
            _ = a * (e * x) := by group
            _ = a * (x * e) := by rw [hxe]
            _ = a * x * e := by group
        exact mul_right_cancel h2
      rw [hZ A (Finset.mem_insert_self A S)] at hmem
      exact congrArg Subtype.val (mem_bot.mp hmem)
    subst ha1
    show 1 * e = 1
    rw [one_mul]
    refine ih hcomm' hZ' e he fun y hy => ?_
    have h1 := hzc y (mem_sup_right hy)
    simpa using h1

variable {H : Type} [Group H] [Finite H]

abbrev oL (L : Subgroup H) : Subgroup H := (pPrimeCore 2 ↥L).map L.subtype

theorem odd_card_oL (L : Subgroup H) : Odd (Nat.card ↥(oL L)) := by
  rw [oL, Subgroup.card_map_of_injective L.subtype_injective]
  exact Nat.coprime_two_left.mp pPrimeCore_coprime_card

theorem le_oL_of_normalized {D U : Subgroup H} (hUD : U ≤ D) (hDU : D ≤ normalizer (U : Set H))
    (hU : Odd (Nat.card ↥U)) : U ≤ oL D := by
  have hle : U.subgroupOf D ≤ pPrimeCore 2 ↥D := by
    refine le_sSup ⟨normal_subgroupOf_of_le_normalizer hDU, ?_⟩
    have h1 : Nat.card ↥(U.subgroupOf D) = Nat.card ↥U := by
      rw [← Subgroup.card_map_of_injective D.subtype_injective, subgroupOf_map_subtype,
        inf_eq_left.mpr hUD]
    rw [h1]
    exact Nat.coprime_two_left.mpr hU
  intro x hx
  exact ⟨⟨x, hUD hx⟩, hle (mem_subgroupOf.mpr hx), rfl⟩

theorem isPComponent_cj_subgroupOf {X K : Subgroup H} (hKX : K ≤ X)
    (hK : IsPComponent 2 (K.subgroupOf X)) {g : H} (hg : g ∈ normalizer (X : Set H)) :
    cj g K ≤ X ∧ IsPComponent 2 ((cj g K).subgroupOf X) := by
  have hle : cj g K ≤ X := by
    rintro _ ⟨k, hk, rfl⟩
    exact (mem_normalizer_iff.mp hg k).mp (hKX hk)
  refine ⟨hle, ?_⟩
  let φ : MulAut ↥X := X.normalizerMonoidHom ⟨g, hg⟩
  have hφ : ∀ x : ↥X, ((φ x : ↥X) : H) = g * x * g⁻¹ := fun x => rfl
  have h1 := LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 φ hK
  convert h1 using 1
  ext y
  rw [mem_subgroupOf, mem_cj, Subgroup.mem_map_equiv, mem_subgroupOf]
  have h2 : ((φ.symm y : ↥X) : H) = g⁻¹ * y * g := by
    have h3 : φ (φ.symm y) = y := φ.apply_symm_apply y
    have h4 := congrArg Subtype.val h3
    rw [hφ] at h4
    calc ((φ.symm y : ↥X) : H) = g⁻¹ * (g * (φ.symm y : ↥X) * g⁻¹) * g := by group
      _ = g⁻¹ * y * g := by rw [h4]
  rw [h2]

theorem normalizer_and_commutator_of_isPComponent {X L L' : Subgroup H} (hLX : L ≤ X)
    (hL'X : L' ≤ X) (hL : IsPComponent 2 (L.subgroupOf X)) (hL' : IsPComponent 2 (L'.subgroupOf X))
    (hne : L ≠ L') : L' ≤ normalizer (L : Set H) ∧ ⁅L, L'⁆ ≤ oL L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne' : L.subgroupOf X ≠ L'.subgroupOf X := fun h => hne (by
    rw [← inf_eq_left.mpr hLX, ← inf_eq_left.mpr hL'X, ← subgroupOf_map_subtype,
      ← subgroupOf_map_subtype, h])
  obtain ⟨h1, -, h3⟩ := CatalogueBPrimeJoin.mutual_normalization_core_commutation 2 _ _ hL hL' hne'
  have hO : ((pPrimeCore 2 ↥(L.subgroupOf X)).map (L.subgroupOf X).subtype).map X.subtype =
      oL L := by
    let e := subgroupOfEquivOfLe hLX
    rw [oL, ← pPrimeCore_map_iso 2 e, Subgroup.map_map, Subgroup.map_map]
    rfl
  refine ⟨fun x hx => ?_, ?_⟩
  · have hx' : (⟨x, hL'X hx⟩ : ↥X) ∈ normalizer ((L.subgroupOf X : Subgroup ↥X) : Set ↥X) :=
      h1 (mem_subgroupOf.mpr hx)
    rw [mem_normalizer_iff] at hx' ⊢
    intro y
    by_cases hy : y ∈ X
    · have h4 := hx' ⟨y, hy⟩
      rw [mem_subgroupOf, mem_subgroupOf] at h4
      exact h4
    · constructor
      · intro h
        exact absurd (hLX h) hy
      · intro h
        exfalso
        apply hy
        have h5 : x * y * x⁻¹ ∈ X := hLX h
        have h6 : x⁻¹ * (x * y * x⁻¹) * x ∈ X :=
          mul_mem (mul_mem (inv_mem (hL'X hx)) h5) (hL'X hx)
        rwa [show x⁻¹ * (x * y * x⁻¹) * x = y by group] at h6
  · have h4 : ⁅L, L'⁆ = (⁅L.subgroupOf X, L'.subgroupOf X⁆).map X.subtype := by
      rw [Subgroup.map_commutator, map_subgroupOf_eq_of_le hLX, map_subgroupOf_eq_of_le hL'X]
    rw [h4, ← hO]
    exact Subgroup.map_mono (h3.trans inf_le_left)

theorem center_ne_bot_of_mem_orbJoin {M X B K : Subgroup H} {w : H} (hXM : X ≤ M)
    (hBX : B ≤ normalizer (X : Set H)) (hKX : K ≤ X) (hK : IsPComponent 2 (K.subgroupOf X))
    (hw : orderOf w = 2) (hwD : w ∈ orbJoin B K)
    (hwM : w ∈ (Open.fusionZStar ↥M).map M.subtype) :
    center (↥K ⧸ pPrimeCore 2 ↥K) ≠ ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hZ
  set L₀ : Set (Subgroup H) := {L | ∃ g ∈ B, L = cj g K} with hL₀
  have hmem : ∀ L ∈ L₀, L ≤ X ∧ IsPComponent 2 (L.subgroupOf X) := by
    rintro L ⟨g, hg, rfl⟩
    exact isPComponent_cj_subgroupOf hKX hK (hBX hg)
  have hZL : ∀ L ∈ L₀, center (↥L ⧸ pPrimeCore 2 ↥L) = ⊥ := by
    rintro L ⟨g, hg, rfl⟩
    let e : ↥K ≃* ↥(cj g K) := K.equivMapOfInjective _ (MulAut.conj g).injective
    exact center_eq_bot_of_mulEquiv'
      (QuotientGroup.congr _ _ e (pPrimeCore_map_iso 2 e)).symm hZ
  have hLD : ∀ L ∈ L₀, L ≤ orbJoin B K := by
    rintro L ⟨g, hg, rfl⟩
    exact cj_le_orbJoin hg
  have hDX : orbJoin B K ≤ X := iSup₂_le fun g hg => (hmem _ ⟨g, hg, rfl⟩).1
  have hDsup : orbJoin B K = sSup L₀ :=
    le_antisymm (iSup₂_le fun g hg => le_sSup ⟨g, hg, rfl⟩) (sSup_le hLD)
  set D := orbJoin B K with hDdef
  have hDN : ∀ L ∈ L₀, D ≤ normalizer (L : Set H) := by
    intro L hL
    rw [hDsup]
    refine sSup_le fun L' hL' => ?_
    by_cases h : L = L'
    · subst h
      exact le_normalizer
    · exact (normalizer_and_commutator_of_isPComponent (hmem L hL).1 (hmem L' hL').1
        (hmem L hL).2 (hmem L' hL').2 h).1
  have hOLD : ∀ L ∈ L₀, oL L ≤ oL D := fun L hL =>
    le_oL_of_normalized ((map_subtype_le _).trans (hLD L hL))
      ((hDN L hL).trans (UnbalancedGS.normalizer_le_normalizer_map_of_characteristic L
        (pPrimeCore 2 ↥L))) (odd_card_oL L)
  have hNOD : D ≤ normalizer ((oL D : Subgroup H) : Set H) :=
    le_normalizer.trans (UnbalancedGS.normalizer_le_normalizer_map_of_characteristic D
      (pPrimeCore 2 ↥D))
  have hODL : ∀ L ∈ L₀, oL D ⊓ L ≤ oL L := by
    intro L hL
    refine le_oL_of_normalized inf_le_right (fun x hx => ?_)
      (Odd.of_dvd_nat (odd_card_oL D) (Subgroup.card_dvd_of_le inf_le_left))
    have h1 := hNOD (hLD L hL hx)
    have h2 : x ∈ normalizer (L : Set H) := le_normalizer hx
    rw [mem_normalizer_iff] at h1 h2 ⊢
    intro y
    rw [mem_inf, mem_inf, h1 y, h2 y]
  set π : ↥D →* ↥D ⧸ pPrimeCore 2 ↥D := QuotientGroup.mk' (pPrimeCore 2 ↥D) with hπ
  have hπker : ∀ d : ↥D, π d = 1 ↔ (d : H) ∈ oL D := by
    intro d
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, oL]
    constructor
    · intro h
      exact ⟨d, h, rfl⟩
    · rintro ⟨d', hd', hd'd⟩
      rwa [← Subtype.ext hd'd]
  let img : Subgroup H → Subgroup (↥D ⧸ pPrimeCore 2 ↥D) := fun L => (L.subgroupOf D).map π
  have himgZ : ∀ L ∈ L₀, center ↥(img L) = ⊥ := by
    intro L hL
    let ψ : ↥L →* ↥D ⧸ pPrimeCore 2 ↥D := π.comp (Subgroup.inclusion (hLD L hL))
    have hrange : ψ.range = img L := by
      ext q
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨Subgroup.inclusion (hLD L hL) x, mem_subgroupOf.mpr x.2, rfl⟩
      · rintro ⟨d, hd, rfl⟩
        exact ⟨⟨d, mem_subgroupOf.mp hd⟩, rfl⟩
    have hker : ψ.ker = pPrimeCore 2 ↥L := by
      ext x
      rw [MonoidHom.mem_ker]
      change π (Subgroup.inclusion (hLD L hL) x) = 1 ↔ _
      rw [hπker]
      change (x : H) ∈ oL D ↔ _
      constructor
      · intro h
        obtain ⟨y, hy, hyx⟩ := hODL L hL ⟨h, x.2⟩
        rwa [← Subtype.ext hyx]
      · intro h
        exact hOLD L hL ⟨x, h, rfl⟩
    let e₁ : ↥L ⧸ pPrimeCore 2 ↥L ≃* ↥(img L) :=
      ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivRange ψ)).trans (MulEquiv.subgroupCongr hrange)
    exact center_eq_bot_of_mulEquiv' e₁.symm (hZL L hL)
  have himgC : ∀ L ∈ L₀, ∀ L' ∈ L₀, img L ≠ img L' → ⁅img L, img L'⁆ = ⊥ := by
    intro L hL L' hL' hne
    have hLL' : L ≠ L' := fun h => hne (h ▸ rfl)
    have hc := (normalizer_and_commutator_of_isPComponent (hmem L hL).1 (hmem L' hL').1
      (hmem L hL).2 (hmem L' hL').2 hLL').2
    have h1 : ⁅L.subgroupOf D, L'.subgroupOf D⁆ ≤ π.ker := by
      rw [commutator_le]
      intro x hx y hy
      rw [MonoidHom.mem_ker, hπker]
      exact hOLD L hL (hc (commutator_mem_commutator (mem_subgroupOf.mp hx)
        (mem_subgroupOf.mp hy)))
    change ⁅(L.subgroupOf D).map π, (L'.subgroupOf D).map π⁆ = ⊥
    rw [← Subgroup.map_commutator, eq_bot_iff]
    rintro _ ⟨z, hz, rfl⟩
    exact (MonoidHom.mem_ker.mp (h1 hz)).symm ▸ one_mem _
  have hfin : L₀.Finite := Set.toFinite L₀
  set S : Finset (Subgroup (↥D ⧸ pPrimeCore 2 ↥D)) := hfin.toFinset.image img with hS
  have hStop : ∀ d : ↥D, π d ∈ sSup (S : Set (Subgroup (↥D ⧸ pPrimeCore 2 ↥D))) := by
    set W : Subgroup ↥D := (sSup (S : Set (Subgroup (↥D ⧸ pPrimeCore 2 ↥D)))).comap π
    have hW : orbJoin B K ≤ W.map D.subtype := by
      refine iSup₂_le fun g hg => ?_
      intro x hx
      refine ⟨⟨x, cj_le_orbJoin hg hx⟩, ?_, rfl⟩
      have hL : cj g K ∈ L₀ := ⟨g, hg, rfl⟩
      have h1 : img (cj g K) ∈ S := Finset.mem_image.mpr ⟨_, hfin.mem_toFinset.mpr hL, rfl⟩
      exact le_sSup (show img (cj g K) ∈ (S : Set _) from h1)
        ⟨⟨x, cj_le_orbJoin hg hx⟩, mem_subgroupOf.mpr hx, rfl⟩
    intro d
    obtain ⟨d', hd', hd'd⟩ := hW d.2
    exact (Subtype.ext hd'd : d' = d) ▸ hd'
  have hMN : D ≤ normalizer ((oL M ⊓ D : Subgroup H) : Set H) := by
    intro x hx
    have h1 := UnbalancedGS.normalizer_le_normalizer_map_of_characteristic M (pPrimeCore 2 ↥M)
      (le_normalizer (hXM (hDX hx)))
    have h2 : x ∈ normalizer (D : Set H) := le_normalizer hx
    rw [mem_normalizer_iff] at h1 h2 ⊢
    intro y
    rw [mem_inf, mem_inf, h1 y, h2 y]
  have hMD : oL M ⊓ D ≤ oL D := le_oL_of_normalized inf_le_right hMN
    (Odd.of_dvd_nat (odd_card_oL M) (Subgroup.card_dvd_of_le inf_le_left))
  have hwc : ∀ y ∈ sSup (S : Set (Subgroup (↥D ⧸ pPrimeCore 2 ↥D))),
      y * π ⟨w, hwD⟩ = π ⟨w, hwD⟩ * y := by
    intro y _
    obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥D) y
    obtain ⟨k, hk, hkw⟩ := hwM
    have hdM : (d : H) ∈ M := hXM (hDX d.2)
    have h1 : ⁅k, (⟨d, hdM⟩ : ↥M)⁆ ∈ pPrimeCore 2 ↥M := GSThmB.OddQuot.mem_fusionZStar_iff.mp hk _
    have h2 : ⁅w, (d : H)⁆ ∈ oL M ⊓ D := by
      refine ⟨⟨_, h1, ?_⟩, ?_⟩
      · rw [← hkw]
        rfl
      · rw [commutatorElement_def]
        exact D.mul_mem (D.mul_mem (D.mul_mem hwD d.2) (D.inv_mem hwD)) (D.inv_mem d.2)
    have h3 : π ⁅(⟨w, hwD⟩ : ↥D), d⁆ = 1 := (hπker _).mpr (hMD h2)
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h3
    exact h3.symm
  have hScomm : ∀ A ∈ S, ∀ A' ∈ S, A ≠ A' → ⁅A, A'⁆ = ⊥ := by
    intro A hA A' hA' hne
    obtain ⟨L, hL, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨L', hL', rfl⟩ := Finset.mem_image.mp hA'
    exact himgC L (hfin.mem_toFinset.mp hL) L' (hfin.mem_toFinset.mp hL') hne
  have hSZ : ∀ A ∈ S, center ↥A = ⊥ := by
    intro A hA
    obtain ⟨L, hL, rfl⟩ := Finset.mem_image.mp hA
    exact himgZ L (hfin.mem_toFinset.mp hL)
  have h1 := eq_one_of_central_of_centerless S hScomm hSZ (π ⟨w, hwD⟩) (hStop _) hwc
  rw [hπker] at h1
  have h2 : orderOf w ∣ Nat.card ↥(oL D) := Subgroup.orderOf_dvd_natCard (oL D) h1
  rw [hw] at h2
  exact (Nat.not_even_iff_odd.mpr (odd_card_oL D)) (even_iff_two_dvd.mpr h2)

end CFSG.ComponentClassification.GS82PumpInputs.P10
