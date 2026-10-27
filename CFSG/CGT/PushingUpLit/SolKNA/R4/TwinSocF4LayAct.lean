module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp22RestLayer

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Balance
open CFSG.CGT.PushingUpLit.SolKNA.R4.Perp22Rest
open scoped commutatorElement

section Act

variable {Y : Type} [Group Y] [Finite Y]

abbrev LayerΓ (K' : Subgroup Y) (c : Y) : Type :=
  ↥(Subgroup.normalizer ((secH K' c : Subgroup ↥(Subgroup.centralizer ({c} : Set Y))) :
    Set ↥(Subgroup.centralizer ({c} : Set Y))))

@[expose] noncomputable def LayerΓ.toY (K' : Subgroup Y) (c : Y) : LayerΓ K' c →* Y :=
  (Subgroup.centralizer ({c} : Set Y)).subtype.comp (Subgroup.normalizer _).subtype

theorem LayerΓ.toY_comm (K' : Subgroup Y) (c : Y) (g : LayerΓ K' c) :
    c * LayerΓ.toY K' c g = LayerΓ.toY K' c g * c := by
  have := Subgroup.mem_centralizer_singleton_iff.mp (g : ↥(Subgroup.centralizer ({c} : Set Y))).2
  exact this.symm

@[expose] noncomputable def layerAct (K' : Subgroup Y) (c : Y) :
    LayerΓ K' c →* MulAut (SecQ K' c) :=
  Perp22.actQuot (secH K' c)

@[expose] noncomputable def LayerΓ.ofNormalizer {K' : Subgroup Y} {c x : Y}
    (hxC : x ∈ Subgroup.centralizer ({c} : Set Y)) (hx : x ∈ Subgroup.normalizer (K' : Set Y)) :
    LayerΓ K' c :=
  ⟨⟨x, hxC⟩, mem_normalizer_secH hxC hx⟩

theorem LayerΓ.toY_ofNormalizer {K' : Subgroup Y} {c x : Y}
    (hxC : x ∈ Subgroup.centralizer ({c} : Set Y)) (hx : x ∈ Subgroup.normalizer (K' : Set Y)) :
    LayerΓ.toY K' c (LayerΓ.ofNormalizer hxC hx) = x := rfl

@[expose] noncomputable def LayerΓ.ofMem {K' : Subgroup Y} {c : Y} (h : ↥(secH K' c)) : LayerΓ K' c :=
  ⟨(h : ↥(Subgroup.centralizer ({c} : Set Y))), Subgroup.le_normalizer h.2⟩

theorem LayerΓ.toY_ofMem {K' : Subgroup Y} {c : Y} (h : ↥(secH K' c)) :
    LayerΓ.toY K' c (LayerΓ.ofMem h) = (((h : ↥(Subgroup.centralizer ({c} : Set Y))) : Y)) := rfl

theorem layerAct_of_mem {K' : Subgroup Y} {c : Y} (h : ↥(secH K' c)) :
    layerAct K' c (LayerΓ.ofMem h) =
      MulAut.conj (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH K' c)) h) := by
  ext y
  induction y using QuotientGroup.induction_on with
  | H x =>
    show Perp22.actQuot (secH K' c) _ (QuotientGroup.mk x) = _
    rw [Perp22.actQuot_apply_mk, MulAut.conj_apply, QuotientGroup.mk'_apply]
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    rfl

theorem LayerΓ.toY_injective (K' : Subgroup Y) (c : Y) : Function.Injective (LayerΓ.toY K' c) :=
  (Subgroup.centralizer ({c} : Set Y)).subtype_injective.comp (Subgroup.normalizer _).subtype_injective

@[expose] noncomputable def layerK (K' K : Subgroup Y) (c : Y) : Subgroup (LayerΓ K' c) :=
  K.comap (LayerΓ.toY K' c)

@[expose] noncomputable def layerO (K' K : Subgroup Y) (c : Y) : Subgroup (LayerΓ K' c) :=
  (oddCoreIn K).comap (LayerΓ.toY K' c)

theorem odd_card_layerO (K' K : Subgroup Y) (c : Y) : Odd (Nat.card ↥(layerO K' K c)) := by
  have hle : (layerO K' K c).map (LayerΓ.toY K' c) ≤ oddCoreIn K := Subgroup.map_comap_le _ _
  have h1 := Subgroup.card_dvd_of_le hle
  rw [Subgroup.card_map_of_injective (LayerΓ.toY_injective K' c)] at h1
  exact (odd_card_oddCoreIn K).of_dvd_nat h1

theorem isPGroup_zpowers_of_pow {G : Type*} [Group G] {v : G} {k : ℕ} (h : v ^ 2 ^ k = 1) :
    IsPGroup 2 ↥(Subgroup.zpowers v) := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h)
  exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])

theorem exists_sylow_centralized' {R : Subgroup Y} {C : Subgroup Y} {v : ↥C} {k : ℕ}
    (hvN : v ∈ Subgroup.normalizer ((tightCore (R.subgroupOf C) : Subgroup ↥C) : Set ↥C))
    (hv2 : v ^ 2 ^ k = 1)
    (hvt : ∀ x ∈ tightCore (R.subgroupOf C), ⁅((v : ↥C) : Y), ((x : ↥C) : Y)⁆ ∈ oddCoreIn R) :
    ∃ P : Subgroup ↥C, IsSylow2In P (tightCore (R.subgroupOf C)) ∧ ∀ x ∈ P, v * x * v⁻¹ = x := by
  classical
  have hW2 : IsPGroup 2 ↥(Subgroup.zpowers v) := isPGroup_zpowers_of_pow hv2
  have hWN : Subgroup.zpowers v ≤ Subgroup.normalizer ((tightCore (R.subgroupOf C) :
      Subgroup ↥C) : Set ↥C) := Subgroup.zpowers_le.mpr hvN
  obtain ⟨P, hP, hfix⟩ := AscQuot.exists_sylow_normalized' hW2 hWN
  refine ⟨P, hP, fun x hx => ?_⟩
  have hvP : conjSub v P = P := hfix v (Subgroup.mem_zpowers v)
  have hy : v * x * v⁻¹ * x⁻¹ ∈ P := by
    have h1 : v * x * v⁻¹ ∈ conjSub v P := conj_mem_conjSub hx
    rw [hvP] at h1
    exact P.mul_mem h1 (P.inv_mem hx)
  have hxK : x ∈ tightCore (R.subgroupOf C) := hP.1 hx
  have hcomm := hvt x hxK
  have hodd : Odd (Nat.card (oddCoreIn R)) := odd_card_oddCoreIn R
  have h2 : IsPGroup 2 (Subgroup.zpowers (((v * x * v⁻¹ * x⁻¹ : ↥C)) : Y)) := by
    have e : Subgroup.zpowers (((v * x * v⁻¹ * x⁻¹ : ↥C)) : Y) =
        (Subgroup.zpowers (v * x * v⁻¹ * x⁻¹)).map C.subtype :=
      (MonoidHom.map_zpowers C.subtype (v * x * v⁻¹ * x⁻¹)).symm
    rw [e]
    exact (hP.2.1.to_le (Subgroup.zpowers_le.mpr hy)).map _
  have h3 : (((v * x * v⁻¹ * x⁻¹ : ↥C)) : Y) = 1 := by
    refine eq_one_of_isPGroup_of_mem_odd hodd ?_ h2
    have : (((v * x * v⁻¹ * x⁻¹ : ↥C)) : Y) = ⁅((v : ↥C) : Y), ((x : ↥C) : Y)⁆ := by
      simp [commutatorElement_def]
    rw [this]
    exact hcomm
  have h4 : v * x * v⁻¹ * x⁻¹ = 1 := Subtype.ext h3
  calc v * x * v⁻¹ = (v * x * v⁻¹ * x⁻¹) * x := by group
    _ = x := by rw [h4, one_mul]

theorem exists_layerElt_of_centralizes {K' : Subgroup Y} {c t : Y}
    (htC : t ∈ Subgroup.centralizer ({c} : Set Y)) (ht' : (⟨t, htC⟩ : ↥(Subgroup.centralizer ({c} : Set Y))) ∈
      secH K' c) (ht2 : t * t = 1) (q : SecQ K' c)
    (hq : q * QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH K' c)) (⟨⟨t, htC⟩, ht'⟩ : ↥(secH K' c)) =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH K' c)) (⟨⟨t, htC⟩, ht'⟩ : ↥(secH K' c)) * q) :
    ∃ h : ↥(secH K' c), h * (⟨⟨t, htC⟩, ht'⟩ : ↥(secH K' c)) = (⟨⟨t, htC⟩, ht'⟩ : ↥(secH K' c)) * h ∧
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH K' c)) h = q := by
  classical
  set tH : ↥(secH K' c) := ⟨⟨t, htC⟩, ht'⟩ with htH
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htH2 : tH ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    exact Subtype.ext (Subtype.ext ht2)
  haveI : Fact (IsPGroup 2 ↥(Subgroup.zpowers tH)) := ⟨isPGroup_zpowers_of_pow htH2⟩
  have hcop : Nat.Coprime 2 (Nat.card ↥(classicalInvolutionOddCore ↥(secH K' c))) :=
    Nat.coprime_two_left.mpr (CFSG.ComponentClassification.OddCore.odd_card ↥(secH K' c))
  have h := CFSG.centralizer_map_quotient_eq_map_centralizer 2 (Subgroup.zpowers tH)
    (classicalInvolutionOddCore ↥(secH K' c)) inferInstance hcop
  have hqm : q ∈ Subgroup.centralizer
      (((Subgroup.zpowers tH).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH K' c))) :
        Subgroup (SecQ K' c)) : Set (SecQ K' c)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
    rw [map_zpow]
    exact ((Commute.zpow_left (show Commute _ q from hq.symm) n)).eq
  simp only at h
  rw [h] at hqm
  obtain ⟨h₀, hh₀, hh₀q⟩ := hqm
  refine ⟨h₀, ?_, hh₀q⟩
  have := Subgroup.mem_centralizer_iff.mp hh₀ tH (Subgroup.mem_zpowers tH)
  exact this.symm

end Act

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4
