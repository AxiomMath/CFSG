module

public import CFSG.LocalAnalysis.ComponentClassification.GS82DPrimeLift
public import CFSG.LocalAnalysis.ComponentClassification.GS82DPrimeBasic

public section

namespace CFSG.ComponentClassification.GS82PumpInputs.DPrime

open CFSG Subgroup GH74.GLS GH74.GLS.TwoThin CFSG.LocalAnalysis.ComponentInitial

variable {Y : Type} [Group Y] [Finite Y]

theorem exists_diag_sl2
    {t s : Y} (hs : ∀ y : Y, s * y = y * s) (hs2 : s * s = 1)
    {L : Subgroup (barQ Y)} (hAB : ⁅L, conjSub (barMk Y t)⁻¹ L⁆ = ⊥)
    {N : Subgroup Y} {q₀ : ℕ} (hq₀ : Odd q₀) (h5 : 5 ≤ q₀)
    (hNSL : HarrisLit.IsSLTwoOver q₀ (↥N ⧸ pPrimeCore 2 ↥N)) (hsN : s ∈ N)
    (hNδ : N.map (barMk Y) ≤ (swapDiag hAB).range) :
    ∃ (P : Subgroup (barQ Y)) (u : barQ Y), P ≤ L ∧ Group.IsPerfect ↥P ∧
      HarrisLit.IsSLTwoOver q₀ (↥P ⧸ pPrimeCore 2 ↥P) ∧ u ∈ P ∧ u * u = 1 ∧
      u * ((barMk Y t)⁻¹ * u * barMk Y t) = barMk Y s ∧ ∀ x ∈ L, u * x = x * u := by
  set π := barMk Y with hπ
  set δ := swapDiag hAB with hδ
  set Nb := N.map π with hNb
  let πN : ↥N →* ↥Nb := (π.comp N.subtype).codRestrict Nb fun n => ⟨n, n.2, rfl⟩
  have hπN : Function.Surjective πN := by
    rintro ⟨_, n, hn, rfl⟩
    exact ⟨⟨n, hn⟩, rfl⟩
  have hπNk : Odd (Nat.card πN.ker) := by
    have hk : πN.ker = (π.domRestrict N).ker := MonoidHom.ker_codRestrict _ _ _
    rw [hk]
    exact OddKernel.odd_card_restriction_kernel π odd_card_ker_barMk N
  obtain ⟨eN⟩ := nonempty_coreQuotEquiv_of_surjective πN hπN hπNk
  have hNbSL : HarrisLit.IsSLTwoOver q₀ (↥Nb ⧸ pPrimeCore 2 ↥Nb) :=
    isSLTwoOver_of_coreEquiv eN hNSL
  set E := Nb.comap δ with hE
  let ρ : ↥E →* ↥Nb := (δ.comp E.subtype).codRestrict Nb fun e => e.2
  have hρ : Function.Surjective ρ := by
    rintro ⟨a, ha⟩
    obtain ⟨l, hl⟩ := hNδ ha
    exact ⟨⟨l, show δ l ∈ Nb by rw [hl]; exact ha⟩, Subtype.ext hl⟩
  have hρker : ρ.ker ≤ center ↥E := by
    intro e he
    have h1 : δ (e : ↥L) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp he)
    have h2 : (e : ↥L) ∈ center ↥L := ker_swapDiag_le_center hAB (MonoidHom.mem_ker.mpr h1)
    exact mem_center_iff.mpr fun g => Subtype.ext (mem_center_iff.mp h2 g)
  have hsc : ∀ z : barQ Y, π s * z = z * π s := by
    intro z
    obtain ⟨y, rfl⟩ := barMk_surjective z
    rw [← map_mul, ← map_mul, hs y]
  set c : ↥Nb := ⟨π s, mem_map_of_mem π hsN⟩ with hcdef
  have hc : c ∈ center ↥Nb := mem_center_iff.mpr fun g => Subtype.ext (hsc g).symm
  have hcc : c * c = 1 := Subtype.ext (by
    change π s * π s = 1
    rw [← map_mul, hs2, map_one])
  obtain ⟨P₀, hP₀, hP₀SL, e, heP, hee, hρe⟩ :=
    exists_sl2_section_lift ρ hρ hρker hq₀ h5 hNbSL hc hcc
  set P : Subgroup (barQ Y) := (P₀.map E.subtype).map L.subtype with hP
  let eP : ↥P₀ ≃* ↥P := (P₀.equivMapOfInjective E.subtype E.subtype_injective).trans
    ((P₀.map E.subtype).equivMapOfInjective L.subtype L.subtype_injective)
  set u : barQ Y := ((e : ↥L) : barQ Y) with hu
  have hδu : u * ((barMk Y t)⁻¹ * u * barMk Y t) = π s := by
    have h1 : δ (e : ↥L) = π s := congrArg Subtype.val hρe
    rw [hδ, swapDiag_apply] at h1
    exact h1
  refine ⟨P, u, map_subtype_le _, ?_, isSLTwoOver_of_mulEquiv eP hP₀SL,
    ⟨e, ⟨e, heP, rfl⟩, rfl⟩, ?_, hδu, ?_⟩
  · have := hP₀
    exact Group.IsPerfect.ofSurjective (f := eP.toMonoidHom) eP.surjective
  · change ((e : ↥L) : barQ Y) * ((e : ↥L) : barQ Y) = 1
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hee]
    rfl
  · intro x hx
    have hxu : x * ((barMk Y t)⁻¹ * u * barMk Y t) = ((barMk Y t)⁻¹ * u * barMk Y t) * x :=
      commute_of_commutator_conj_eq_bot hAB hx (conj_mem_conjSub (e : ↥L).2)
    have h1 : u * ((barMk Y t)⁻¹ * u * barMk Y t) * x = x * (u * ((barMk Y t)⁻¹ * u * barMk Y t))
      := by rw [hδu]; exact hsc x
    have h2 : u * x * ((barMk Y t)⁻¹ * u * barMk Y t) =
        x * u * ((barMk Y t)⁻¹ * u * barMk Y t) := by
      calc u * x * ((barMk Y t)⁻¹ * u * barMk Y t)
          = u * (x * ((barMk Y t)⁻¹ * u * barMk Y t)) := by group
        _ = u * ((barMk Y t)⁻¹ * u * barMk Y t) * x := by rw [hxu]; group
        _ = x * u * ((barMk Y t)⁻¹ * u * barMk Y t) := by rw [h1]; group
    exact mul_right_cancel h2

end CFSG.ComponentClassification.GS82PumpInputs.DPrime
