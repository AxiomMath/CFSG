module

public import CFSG.ClassicalInvolution.LBalance.Proof.Tools
public import CFSG.LocalAnalysis.ComponentClassification.CentralQuotientComponents
public import CFSG.LocalAnalysis.ComponentClassification.SolvablePrimeCoreLayerLift

public section

namespace CFSG.ClassicalInvolution.LBalanceProof

open CFSG CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial CFSG.LocalCores
  CFSG.GroupTheory Subgroup
open scoped commutatorElement

section

variable {X : Type} [Group X] [Finite X]

theorem balanced_of_pPrimeCore_ne_bot
    (IH : ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < Nat.card X → LBalanceAt Y)
    (hN : pPrimeCore 2 X ≠ ⊥) : LBalanceAt X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro A hA K hK
  set N := pPrimeCore 2 X with hNdef
  have hNn : N.Normal := pPrimeCore_normal
  have hNodd : Odd (Nat.card N) := by
    have := ComponentClassification.OddCore.odd_card X
    rwa [← CatalogueBAlternating.primeCore_two_eq_oddCore] at this
  have hcop : Nat.Coprime 2 (Nat.card N) := (Nat.coprime_two_left).2 hNodd
  let q := QuotientGroup.mk' N
  have : Fact (IsPGroup 2 A) := ⟨hA⟩
  have hcent : centralizer ((A.map q : Subgroup (X ⧸ N)) : Set (X ⧸ N)) =
      (centralizer (A : Set X)).map q :=
    centralizer_map_quotient_eq_map_centralizer 2 A N hNn hcop
  let f : centralizer (A : Set X) →* centralizer ((A.map q : Subgroup (X ⧸ N)) : Set (X ⧸ N)) :=
    (q.comp (centralizer (A : Set X)).subtype).codRestrict _
      (fun c => by rw [hcent]; exact ⟨c, c.2, rfl⟩)
  have hf_val : ∀ c, ((f c : centralizer ((A.map q : Subgroup (X ⧸ N)) : Set (X ⧸ N))) : X ⧸ N) = q c :=
    fun c => rfl
  have hf_surj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    rw [hcent] at hy
    obtain ⟨c, hc, rfl⟩ := hy
    exact ⟨⟨c, hc⟩, Subtype.ext rfl⟩
  have hf_ker : Odd (Nat.card f.ker) := by
    have hinj : Function.Injective
        ((((centralizer (A : Set X)).subtype.comp f.ker.subtype).codRestrict N
          (fun c => by
            have h1 : f (c : centralizer (A : Set X)) = 1 := c.2
            have h2 := congrArg Subtype.val h1
            change q (c : centralizer (A : Set X)) = 1 at h2
            exact (QuotientGroup.eq_one_iff _).1 h2)) : f.ker →* N) := by
      intro a b hab
      have h1 := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h1)
    exact Odd.of_dvd_nat hNodd (Subgroup.card_dvd_of_injective _ hinj)
  have hK2 : TwoComponents.IsTwoComponent K := (CatalogueBAlternating.pComponent_two_iff K).1 hK
  have hKf : IsPComponent 2 (K.map f) :=
    (CatalogueBAlternating.pComponent_two_iff _).2
      (OddKernelTwoComponents.image f hf_surj hf_ker K hK2)
  have hcard : Nat.card (X ⧸ N) < Nat.card X := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    have h2 : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot N).2 hN
    have h3 : 0 < Nat.card (X ⧸ N) := Nat.card_pos
    nlinarith
  have hIH := IH (X ⧸ N) hcard (A.map q) (hA.map q) (K.map f) hKf
  have hcorefree : pPrimeCore 2 (X ⧸ N) = ⊥ := CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 2
  rw [pLayer_eq_layer_of_pPrimeCore_eq_bot hcorefree] at hIH
  have hKp : Group.IsPerfect K := isPerfect_of_isPComponent hK
  have : Group.IsPerfect (K.map (centralizer (A : Set X)).subtype) :=
    Group.IsPerfect.map (centralizer (A : Set X)).subtype
  have himg : (K.map (centralizer (A : Set X)).subtype).map (QuotientGroup.mk' (pPrimeCore 2 X)) ≤
      layer (X ⧸ pPrimeCore 2 X) := by
    refine le_trans (le_of_eq ?_) hIH
    rw [Subgroup.map_map, Subgroup.map_map]
    rfl
  have hsolv : Group.IsSolvable (pPrimeCore 2 X) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ hNodd
  exact CatalogueBPrimeJoin.solvable_prime_complement_core_perfect_layer_lift hsolv inferInstance himg
theorem balanced_of_center_ne_bot
    (IH : ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < Nat.card X → LBalanceAt Y)
    (hO : pPrimeCore 2 X = ⊥) (hZ : center X ≠ ⊥) : LBalanceAt X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro A hA
  have hZ2 : IsPGroup 2 (center X) :=
    CFSG.isPGroup_of_nilpotent_normal (center X) inferInstance inferInstance hO
  let q := QuotientGroup.mk' (center X)
  set C := centralizer (A : Set X) with hC
  intro K hK
  let D : Subgroup (X ⧸ center X) := C.map q
  let Ĉ : Subgroup (X ⧸ center X) :=
    centralizer ((A.map q : Subgroup (X ⧸ center X)) : Set (X ⧸ center X))
  have hDle : D ≤ Ĉ := by
    rintro _ ⟨c, hc, rfl⟩
    change q c ∈ centralizer ((A.map q : Subgroup (X ⧸ center X)) : Set (X ⧸ center X))
    rw [mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact mem_centralizer_iff.1 hc a ha
  have hDnormal : (D.subgroupOf Ĉ).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : (n : X ⧸ center X) ∈ D := hn
    obtain ⟨c, hc, hcn⟩ := hn'
    rw [QuotientGroup.mk'_apply] at hcn
    obtain ⟨gX, hgX⟩ := QuotientGroup.mk_surjective (g : X ⧸ center X)
    have hgmem : (g : X ⧸ center X) ∈ Ĉ := g.2
    have key : gX * c * gX⁻¹ ∈ C := by
      rw [hC, mem_centralizer_iff]
      intro a ha
      have h1 : (QuotientGroup.mk a : X ⧸ center X) * (QuotientGroup.mk gX) =
          (QuotientGroup.mk gX) * (QuotientGroup.mk a) := by
        have := mem_centralizer_iff.1 hgmem (QuotientGroup.mk a) ⟨a, ha, rfl⟩
        rw [← hgX] at this
        exact this
      have h2 : gX⁻¹ * a⁻¹ * gX * a ∈ center X := by
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h1
        simpa [mul_assoc] using h1
      have h3 : gX⁻¹ * a * gX = a * (gX⁻¹ * a⁻¹ * gX * a)⁻¹ := by group
      have hca : a * c = c * a := mem_centralizer_iff.1 hc a ha
      have hw : Commute c (gX⁻¹ * a⁻¹ * gX * a)⁻¹ := Subgroup.mem_center_iff.1 (inv_mem h2) c
      have hca' : Commute c a := hca.symm
      have hc3 : Commute c (gX⁻¹ * a * gX) := by rw [h3]; exact hca'.mul_right hw
      calc a * (gX * c * gX⁻¹) = gX * ((gX⁻¹ * a * gX) * c) * gX⁻¹ := by group
        _ = gX * (c * (gX⁻¹ * a * gX)) * gX⁻¹ := by rw [hc3.eq]
        _ = (gX * c * gX⁻¹) * a := by group
    change ((g * n * g⁻¹ : Ĉ) : X ⧸ center X) ∈ D
    refine ⟨gX * c * gX⁻¹, key, ?_⟩
    rw [QuotientGroup.mk'_apply]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hgX, hcn]
    rfl
  have hDn := hDnormal
  let f0 : C →* D := (q.comp C.subtype).codRestrict D (fun c => ⟨c, c.2, rfl⟩)
  have hf0_surj : Function.Surjective f0 := by
    rintro ⟨y, c, hc, rfl⟩
    exact ⟨⟨c, hc⟩, Subtype.ext rfl⟩
  have hf0_ker : ∀ c : C, c ∈ f0.ker → (c : X) ∈ center X := by
    intro c hc
    have h1 : q (c : X) = 1 := congrArg Subtype.val hc
    exact (QuotientGroup.eq_one_iff _).1 h1
  have hf0_central : f0.ker ≤ Subgroup.center C := by
    intro c hc
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hf0_ker c hc) g)
  have hf0_p : IsPGroup 2 f0.ker := by
    let ι : f0.ker →* center X :=
      (C.subtype.comp f0.ker.subtype).codRestrict (center X) (fun c => hf0_ker c c.2)
    have hinj : Function.Injective ι := by
      intro a b hab
      have h1 := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h1)
    exact hZ2.of_injective ι hinj
  have hbij := CatalogueBPrimeJoin.central_p_quotient_p_component_bijection (p := 2) f0
    hf0_surj hf0_central hf0_p
  have hKD : IsPComponent 2 (K.map f0) := hbij.1.mapsTo hK
  let e : D.subgroupOf Ĉ ≃* D := Subgroup.subgroupOfEquivOfLe hDle
  have hKN : IsPComponent 2 ((K.map f0).map e.symm.toMonoidHom) :=
    LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 e.symm hKD
  have hKC : IsPComponent 2 (((K.map f0).map e.symm.toMonoidHom).map (D.subgroupOf Ĉ).subtype) :=
    CatalogueBAlternating.pComponent_of_normal_subgroup 2 (D.subgroupOf Ĉ) _ hKN
  have hcard : Nat.card (X ⧸ center X) < Nat.card X := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center X)
    have h2 : 1 < Nat.card (center X) := (Subgroup.one_lt_card_iff_ne_bot _).2 hZ
    have h3 : 0 < Nat.card (X ⧸ center X) := Nat.card_pos
    nlinarith
  have hIH := IH (X ⧸ center X) hcard (A.map q) (hA.map q) _ hKC
  have himg : ((((K.map f0).map e.symm.toMonoidHom).map (D.subgroupOf Ĉ).subtype).map
      Ĉ.subtype) = (K.map C.subtype).map q := by
    simp only [Subgroup.map_map]
    congr 1
  rw [himg] at hIH
  have hq_ker : q.ker = center X := QuotientGroup.ker_mk' _
  have hq_bij := CatalogueBPrimeJoin.central_p_quotient_p_component_bijection (p := 2) q
    (QuotientGroup.mk'_surjective _) hq_ker.le (by rw [hq_ker]; exact hZ2)
  have hlayer : pLayer (X ⧸ center X) 2 ≤ (pLayer X 2).map q := by
    refine sSup_le fun M hM => ?_
    obtain ⟨L, hL, rfl⟩ := hq_bij.1.surjOn hM
    exact Subgroup.map_mono (le_sSup hL)
  have hKle : K.map C.subtype ≤ pLayer X 2 ⊔ center X := by
    have := Subgroup.map_le_iff_le_comap.1 (hIH.trans hlayer)
    rwa [Subgroup.comap_map_eq, hq_ker] at this
  have hKp : Group.IsPerfect K := isPerfect_of_isPComponent hK
  have : Group.IsPerfect (K.map C.subtype) := Group.IsPerfect.map C.subtype
  have := CatalogueBPrimeJoin.pLayer_characteristic (G := X) (p := 2)
  exact perfect_le_of_le_sup_solvable (K.map C.subtype) (pLayer X 2) (center X) hKle
end

end CFSG.ClassicalInvolution.LBalanceProof
