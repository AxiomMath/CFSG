module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
public import CFSG.CharacterTheory.Semidihedral.CentralHall

public section

namespace CFSG.Semidihedral.OddCoreQuotient

universe u v

variable {E : Type u} [Group E]

theorem pPrimeCore_map_le_of_surjective [Finite E] (p : ℕ) [Fact p.Prime]
    {F : Type v} [Group F] (f : E →* F) (hf : Function.Surjective f) :
    (CFSG.pPrimeCore p E).map f ≤ CFSG.pPrimeCore p F := by
  apply le_sSup
  constructor
  · exact Subgroup.Normal.map inferInstance f hf
  · exact Nat.Coprime.of_dvd_right (Subgroup.card_map_dvd _ f)
      (CFSG.pPrimeCore_coprime_card (p := p) (G := E))

theorem pPrimeCore_map_quotient_le [Finite E] (p : ℕ) [Fact p.Prime]
    (A : Subgroup E) [A.Normal] :
    (CFSG.pPrimeCore p E).map (QuotientGroup.mk' A) ≤
      CFSG.pPrimeCore p (E ⧸ A) :=
  pPrimeCore_map_le_of_surjective p _ (QuotientGroup.mk'_surjective A)

theorem kernel_le_quotient_preimage (A : Subgroup E) [A.Normal]
    (B : Subgroup (E ⧸ A)) : A ≤ B.comap (QuotientGroup.mk' A) := by
  simpa only [QuotientGroup.ker_mk'] using
    (Subgroup.ker_le_comap (f := QuotientGroup.mk' A) (H := B))

theorem quotient_preimage_kernel_card (A : Subgroup E) [A.Normal]
    (B : Subgroup (E ⧸ A)) :
    Nat.card (A.subgroupOf (B.comap (QuotientGroup.mk' A))) = Nat.card A :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (kernel_le_quotient_preimage A B)).toEquiv

theorem quotient_preimage_kernel_index (A : Subgroup E) [A.Normal]
    (B : Subgroup (E ⧸ A)) :
    (A.subgroupOf (B.comap (QuotientGroup.mk' A))).index = Nat.card B := by
  let R := B.comap (QuotientGroup.mk' A)
  let f := (QuotientGroup.mk' A).domRestrict R
  have hker : f.ker = A.subgroupOf R := by
    simpa only [f, QuotientGroup.ker_mk'] using
      (MonoidHom.ker_domRestrict R (QuotientGroup.mk' A))
  have hrange : f.range = B := by
    change ((QuotientGroup.mk' A).domRestrict R).range = B
    rw [MonoidHom.domRestrict_range]
    exact Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective A) B
  change (A.subgroupOf R).index = Nat.card B
  rw [← hker, Subgroup.index_ker, hrange]

theorem central_subgroupOf_le_center (A R : Subgroup E)
    (hA : A ≤ Subgroup.center E) : A.subgroupOf R ≤ Subgroup.center R := by
  intro a ha
  rw [Subgroup.mem_center_iff]
  intro r
  apply Subtype.ext
  exact (Subgroup.mem_center_iff.mp (hA ha)) (r : E)

theorem quotient_preimage_kernel_isPGroup (p : ℕ) (A : Subgroup E) [A.Normal]
    (hAp : IsPGroup p A) (B : Subgroup (E ⧸ A)) :
    IsPGroup p (A.subgroupOf (B.comap (QuotientGroup.mk' A))) :=
  hAp.of_equiv (Subgroup.subgroupOfEquivOfLe
    (kernel_le_quotient_preimage A B)).symm

theorem quotient_preimage_kernel_coprime_index [Finite E]
    (p : ℕ) [Fact p.Prime] (A : Subgroup E) [A.Normal]
    (hAp : IsPGroup p A) (B : Subgroup (E ⧸ A))
    (hB : Nat.Coprime p (Nat.card B)) :
    Nat.Coprime (Nat.card (A.subgroupOf (B.comap (QuotientGroup.mk' A))))
      (A.subgroupOf (B.comap (QuotientGroup.mk' A))).index := by
  obtain ⟨k, hk⟩ := hAp.exists_card_eq
  rw [quotient_preimage_kernel_card, quotient_preimage_kernel_index, hk]
  exact hB.pow_left k

theorem quotient_core_preimage_normal (p : ℕ) (A : Subgroup E) [A.Normal] :
    ((CFSG.pPrimeCore p (E ⧸ A)).comap (QuotientGroup.mk' A)).Normal :=
  Subgroup.Normal.comap inferInstance _

theorem quotient_core_preimage_kernel_coprime_index [Finite E]
    (p : ℕ) [Fact p.Prime] (A : Subgroup E) [A.Normal]
    (hAp : IsPGroup p A) :
    Nat.Coprime
      (Nat.card (A.subgroupOf
        ((CFSG.pPrimeCore p (E ⧸ A)).comap (QuotientGroup.mk' A))))
      (A.subgroupOf
        ((CFSG.pPrimeCore p (E ⧸ A)).comap (QuotientGroup.mk' A))).index :=
  quotient_preimage_kernel_coprime_index p A hAp _
    (CFSG.pPrimeCore_coprime_card (p := p) (G := E ⧸ A))

theorem kernel_complement_map_eq_range {F : Type v} [Group F]
    (f : E →* F) (D : Subgroup E) (hD : f.ker.IsComplement' D) :
    D.map f = f.range := by
  have hker : f.ker.map f = ⊥ :=
    (Subgroup.map_eq_bot_iff (H := f.ker) (f := f)).mpr le_rfl
  have h := congrArg (Subgroup.map f) hD.sup_eq_top
  simpa [Subgroup.map_sup, hker, Subgroup.map_top] using h

theorem quotient_preimage_complement_map_eq (A : Subgroup E) [A.Normal]
    (B : Subgroup (E ⧸ A))
    (D : Subgroup (B.comap (QuotientGroup.mk' A)))
    (hD : (A.subgroupOf (B.comap (QuotientGroup.mk' A))).IsComplement' D) :
    (D.map (B.comap (QuotientGroup.mk' A)).subtype).map
      (QuotientGroup.mk' A) = B := by
  let R := B.comap (QuotientGroup.mk' A)
  let f := (QuotientGroup.mk' A).domRestrict R
  have hker : f.ker = A.subgroupOf R := by
    simpa only [f, QuotientGroup.ker_mk'] using
      (MonoidHom.ker_domRestrict R (QuotientGroup.mk' A))
  have hrange : f.range = B := by
    change ((QuotientGroup.mk' A).domRestrict R).range = B
    rw [MonoidHom.domRestrict_range]
    exact Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective A) B
  rw [Subgroup.map_map]
  change D.map f = B
  exact (kernel_complement_map_eq_range f D (by simpa only [hker] using hD)).trans hrange

theorem exists_normal_coprime_lift [Finite E] (p : ℕ) [Fact p.Prime]
    (A : Subgroup E) [A.Normal] (hA : A ≤ Subgroup.center E)
    (hAp : IsPGroup p A) (B : Subgroup (E ⧸ A)) [B.Normal]
    (hB : Nat.Coprime p (Nat.card B)) :
    ∃ D : Subgroup E, D.Normal ∧ Nat.Coprime p (Nat.card D) ∧
      D ≤ B.comap (QuotientGroup.mk' A) ∧ D.map (QuotientGroup.mk' A) = B := by
  let R := B.comap (QuotientGroup.mk' A)
  let H := A.subgroupOf R
  have hH : H ≤ Subgroup.center R := central_subgroupOf_le_center A R hA
  have hHcop : Nat.Coprime (Nat.card H) H.index :=
    quotient_preimage_kernel_coprime_index p A hAp B hB
  let D := CFSG.Semidihedral.centralHallComplement H hH hHcop
  have hDchar : D.Characteristic := inferInstance
  have hDcard : Nat.card D = Nat.card B :=
    (CFSG.Semidihedral.centralHallComplement_card H hH hHcop).trans
      (quotient_preimage_kernel_index A B)
  have hDcomp : H.IsComplement' D :=
    CFSG.Semidihedral.centralHallComplement_isComplement H hH hHcop
  refine ⟨D.map R.subtype, inferInstance, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective R.subtype_injective, hDcard]
    exact hB
  · exact Subgroup.map_subtype_le D
  · exact quotient_preimage_complement_map_eq A B D hDcomp

theorem pPrimeCore_map_quotient_of_central [Finite E] (p : ℕ) [Fact p.Prime]
    (A : Subgroup E) (hA : A ≤ Subgroup.center E) (hAp : IsPGroup p A) :
    let : A.Normal := Subgroup.normal_of_le_center hA
    (CFSG.pPrimeCore p E).map (QuotientGroup.mk' A) = CFSG.pPrimeCore p (E ⧸ A) := by
  let : A.Normal := Subgroup.normal_of_le_center hA
  apply le_antisymm (pPrimeCore_map_quotient_le p A)
  obtain ⟨D, hDnormal, hDcop, _, hDmap⟩ :=
    exists_normal_coprime_lift p A hA hAp (CFSG.pPrimeCore p (E ⧸ A))
      (CFSG.pPrimeCore_coprime_card (p := p) (G := E ⧸ A))
  rw [← hDmap]
  exact Subgroup.map_mono (le_sSup ⟨hDnormal, hDcop⟩)

theorem pPrimeCore_quotient_eq_bot_of_central [Finite E] (p : ℕ) [Fact p.Prime]
    (A : Subgroup E) (hA : A ≤ Subgroup.center E) (hAp : IsPGroup p A)
    (hcore : CFSG.pPrimeCore p E = ⊥) :
    let : A.Normal := Subgroup.normal_of_le_center hA
    CFSG.pPrimeCore p (E ⧸ A) = ⊥ := by
  let : A.Normal := Subgroup.normal_of_le_center hA
  change CFSG.pPrimeCore p (E ⧸ A) = ⊥
  rw [← pPrimeCore_map_quotient_of_central p A hA hAp, hcore, Subgroup.map_bot]

end CFSG.Semidihedral.OddCoreQuotient
