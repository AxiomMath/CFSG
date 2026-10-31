module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.MinRep
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.E7Neg
public import CFSG.LieType.Steinberg.CentralExt.FieldFourMultiplier
public import CFSG.Quasithin.Background.SmithCurtisChevType

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.Quasithin.SmithCurtis.Chev CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule


section Iso

variable {K : Type} [Field K] [Finite K]

theorem eltElement_neg_simpleRoot' (i : Fin (Tag.rank .E7)) (c : K) :
    (rootOperatorFamily .E7).eltElement (-simpleRoot .E7 i) c = yElement i c :=
  Subtype.ext ((rootOperatorFamily .E7).eltUnit_neg_simple i c)

theorem e7Isogeny_xm_single_eq (i : Fin (Tag.rank .E7)) (c : K) :
    Isogeny.e7Isogeny K (e7Data_valid.xm K (Pi.single i 1) c) = xC .E7 K i c := by
  rw [Isogeny.e7Isogeny_xm_single, eltElement_simpleRoot]
  rfl

theorem e7Isogeny_nt (a : Fin (Tag.rank .E7)) (s : Kˣ) :
    ((Isogeny.e7Isogeny K (e7Data_valid.nt K a s) : ↥(adjointGroup .E7 K)) : ModGL .E7 K) =
      weylElt .E7 K a s := by
  rw [weylElt_eq_xUnit_mul]
  change ((Isogeny.e7Isogeny K (e7Data_valid.xm K (Pi.single a 1) s *
    e7Data_valid.xm K (-Pi.single a 1) (-((s⁻¹ : Kˣ) : K)) *
      e7Data_valid.xm K (Pi.single a 1) s) : ↥(adjointGroup .E7 K)) : ModGL .E7 K) = _
  rw [map_mul, map_mul, Isogeny.e7Isogeny_xm_single, Isogeny.e7Isogeny_xm_neg_single,
    eltElement_simpleRoot, eltElement_neg_simpleRoot']
  rfl

theorem e7Isogeny_nm (a : Fin (Tag.rank .E7)) :
    Isogeny.e7Isogeny K (e7Data_valid.nm K a) = nC .E7 K a :=
  Subtype.ext (e7Isogeny_nt a 1)

theorem e7Isogeny_hm (a : Fin (Tag.rank .E7)) (s : Kˣ) :
    Isogeny.e7Isogeny K (e7Data_valid.hm K a s) = dC .E7 K a s := by
  refine Subtype.ext ?_
  change ((Isogeny.e7Isogeny K (e7Data_valid.nt K a s * (e7Data_valid.nt K a 1)⁻¹) :
    ↥(adjointGroup .E7 K)) : ModGL .E7 K) = _
  rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, e7Isogeny_nt, e7Isogeny_nt,
    weylElt_inv]
  rfl

end Iso

theorem e7_dominant : ∀ a : Fin e7Data.d, (∀ i, e7Data.wt a i ≠ -1) → a = ⟨0, by decide⟩ := by
  decide +kernel

theorem e7_reach : reachCheck e7Data 0 30 = true := by decide +kernel

abbrev e7n6 : Fin (Tag.rank .E7) := ⟨6, by decide⟩

theorem e7_wt_zero_aux : ∀ s : Fin (Tag.rank .E7),
    e7Data.wt 0 s = if s = e7n6 then 1 else 0 := by
  decide +kernel

theorem e7_wt_zero (s : Fin Tag.E7.rank) : e7Data.wt 0 s = if s = e7n6 then 1 else 0 :=
  e7_wt_zero_aux s

theorem e7_wt_one : e7Data.wt (↑(⟨0, by decide⟩ : Fin e7Data.d)) e7n6 = 1 := by decide +kernel

section Group

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem coprime_two_card_sub_one : Nat.Coprime 2 (Nat.card K - 1) := by
  have hlt : 1 < Nat.card K := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  have hev : Even (Nat.card K) := by
    have := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card]
    exact Nat.even_iff.2 ((FiniteField.even_card_iff_char_two (F := K)).1 (ringChar.eq K 2))
  obtain ⟨r, hr⟩ := hev
  rw [Nat.coprime_two_left]
  exact ⟨r - 1, by omega⟩

theorem e7Isogeny_injective : Function.Injective (Isogeny.e7Isogeny K) := by
  rw [← MonoidHom.ker_eq_bot_iff, CentralExt.FieldFour.e7Isogeny_ker_eq_center]
  have h1 := (CentralExt.MinusculeClosed.card_center_e7 K).1
  rw [(coprime_two_card_sub_one (K := K)).gcd_eq_one] at h1
  exact Subgroup.eq_bot_of_card_eq _ (by simpa using h1)

@[expose] def e7Equiv : ↥(e7Data_valid.minGroup K) ≃* ↥(adjointGroup .E7 K) :=
  MulEquiv.ofBijective (Isogeny.e7Isogeny K) ⟨e7Isogeny_injective, Isogeny.e7Isogeny_surjective K⟩

@[expose] def e7Datum : CurtisDatum ↥(adjointGroup .E7 K) (coxeterSystem .E7) 2 :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  chevDatum .E7 K 2 exists_weyl_neg_E7

variable (K) in
@[expose] def e7Psi : ↥(adjointGroup .E7 K) →* ↥(e7Data_valid.minGroup K) :=
  (e7Equiv (K := K)).symm.toMonoidHom

theorem e7Psi_xC (i : Fin (Tag.rank .E7)) (c : K) :
    e7Psi K (xC .E7 K i c) = e7Data_valid.xm K (Pi.single i 1) c :=
  (e7Equiv (K := K)).symm_apply_eq.2 (e7Isogeny_xm_single_eq i c).symm

theorem e7Psi_nC (i : Fin (Tag.rank .E7)) : e7Psi K (nC .E7 K i) = e7Data_valid.nm K i :=
  (e7Equiv (K := K)).symm_apply_eq.2 (e7Isogeny_nm i).symm

theorem e7Psi_dC (i : Fin (Tag.rank .E7)) (t : Kˣ) :
    e7Psi K (dC .E7 K i t) = e7Data_valid.hm K i t :=
  (e7Equiv (K := K)).symm_apply_eq.2 (e7Isogeny_hm i t).symm

variable (K) in
@[expose] def e7Rep56 : Representation K ↥(adjointGroup .E7 K) (Fin e7Data.d →₀ K) :=
  pullRep e7Data_valid (e7Psi K)

@[expose] def e7Y56 : Fin e7Data.d →₀ K := Finsupp.single ⟨0, by decide⟩ 1

@[expose] def e7Chi56 (g : ↥(adjointGroup .E7 K)) : K := e7Rep56 K g e7Y56 ⟨0, by decide⟩

theorem e7_hX (i : Fin (Tag.rank .E7)) :
    ∃ g ∈ (e7Datum (K := K)).U, e7Psi K g = e7Data_valid.xm K (Pi.single i 1) 1 :=
  ⟨xC .E7 K i 1, (e7Datum (K := K)).X_le i (xC_mem_X (hw := exists_weyl_neg_E7) i 1),
    e7Psi_xC i 1⟩

theorem isSimpleRep_e7Rep56 : IsSimpleRep (e7Rep56 K) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  isSimpleRep_pullRep (hV := e7Data_valid) (K := K) (e7Psi K) (e7Datum (K := K))
    (e7Equiv (K := K)).symm.surjective e7_hX e7_dominant e7_reach

theorem e7Y56_mem_fixU : (e7Y56 : Fin e7Data.d →₀ K) ∈ (e7Datum (K := K)).fixU (e7Rep56 K) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  single_mem_fixU (hV := e7Data_valid) (K := K) (e7Psi K) (e7Datum (K := K)) e7_hX e7_dominant

theorem e7Y56_ne_zero : (e7Y56 : Fin e7Data.d →₀ K) ≠ 0 := by
  intro h
  have := congrArg (fun v : Fin e7Data.d →₀ K => v ⟨0, by decide⟩) h
  simp [e7Y56] at this

theorem e7Chi56_dC (s : Fin (Tag.rank .E7)) (u : Kˣ) :
    e7Chi56 (dC .E7 K s u) = ((u ^ (if s = e7n6 then (1 : ℤ) else 0) : Kˣ) : K) := by
  unfold e7Chi56 e7Rep56 e7Y56
  have h := minRep_hm_single e7Data_valid (K := K) s u ⟨0, by decide⟩
  have hw : e7Data.wt (↑(⟨0, by decide⟩ : Fin e7Data.d)) s = if s = e7n6 then 1 else 0 :=
    e7_wt_zero s
  rw [pullRep_apply, e7Psi_dC, h, hw]
  simp

theorem e7Rep56_H (h : ↥(adjointGroup .E7 K)) (hh : h ∈ (e7Datum (K := K)).H) :
    e7Rep56 K h e7Y56 = e7Chi56 h • e7Y56 :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  pullRep_H_smul (hV := e7Data_valid) (K := K) (e7Psi K) (e7Datum (K := K)) e7_hX e7_dominant hh

theorem e7_heckeT_y (s : Fin (Tag.rank .E7)) [Fintype K] :
    (e7Datum (K := K)).heckeT (e7Rep56 K) s e7Y56 =
      ∑ c : K, minRep e7Data_valid K (e7Data_valid.xm K (Pi.single s 1) c * e7Data_valid.nm K s)
        e7Y56 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold e7Datum
  rw [heckeT_chevDatum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [e7Rep56, pullRep_apply, map_mul, e7Psi_xC, e7Psi_nC]

theorem e7Rep56_isChevType :
    IsChevType .E7 K 2 exists_weyl_neg_E7 (e7Rep56 K) e7Y56 e7Chi56 (Finset.univ.erase e7n6) := by
  have := Fintype.ofFinite K
  refine ⟨e7Y56_mem_fixU, e7Y56_ne_zero, e7Rep56_H, fun s => ?_⟩
  by_cases hs : s = e7n6
  · subst hs
    refine ⟨fun h => absurd rfl (Finset.mem_erase.1 h).1, fun h => ?_⟩
    exfalso
    obtain ⟨h1, h2⟩ := h
    have h1' : ∀ u : Kˣ, (u : K) = 1 := fun u => by
      have := h1 u
      rwa [e7Chi56_dC, if_pos rfl, zpow_one] at this
    have h3 : (e7Datum (K := K)).heckeT (e7Rep56 K) e7n6 e7Y56 = -(∑ c : K, c) • e7Y56 :=
      (e7_heckeT_y e7n6).trans (sum_xm_nm_of_wt_one (hV := e7Data_valid)
        (a₀ := ⟨0, by decide⟩) (s := e7n6) e7_wt_one)
    have h4 : -(∑ c : K, c) • e7Y56 = 0 := h3.symm.trans h2
    rw [sum_eq_one_of_units_eq_one h1'] at h4
    exact e7Y56_ne_zero (by simpa using h4)
  · have hw : e7Data.wt (↑(⟨0, by decide⟩ : Fin e7Data.d)) s = 0 := by
      have := e7_wt_zero s
      rw [if_neg hs] at this
      exact this
    refine ⟨fun _ => ⟨fun u => ?_, ?_⟩, fun _ => Finset.mem_erase.2 ⟨hs, Finset.mem_univ _⟩⟩
    · rw [e7Chi56_dC, if_neg hs, zpow_zero]
      rfl
    · exact (e7_heckeT_y s).trans (sum_xm_nm_of_wt_zero (hV := e7Data_valid)
        (a₀ := ⟨0, by decide⟩) (s := s) hw)

theorem e7_iso_56 {V : Type*} [AddCommGroup V] [Module K V]
    {ρ : Representation K ↥(adjointGroup .E7 K) V} (hρ : IsSimpleRep ρ) {y : V}
    (ht : IsChevType .E7 K 2 exists_weyl_neg_E7 ρ y e7Chi56 (Finset.univ.erase e7n6)) :
    ∃ β : (Fin e7Data.d →₀ K) ≃ₗ[K] V, ∀ (g : ↥(adjointGroup .E7 K)) (v : Fin e7Data.d →₀ K),
      β (e7Rep56 K g v) = ρ g (β v) :=
  iso_of_isChevType isSimpleRep_e7Rep56 hρ e7Rep56_isChevType ht

end Group

end CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors
