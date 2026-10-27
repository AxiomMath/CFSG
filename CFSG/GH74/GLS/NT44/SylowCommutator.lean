module

public import CFSG.GH74.GLS.NT44.PermutationCommutator
public import Certificates.Certificate1212003
public import CFSG.GH74.GLS.Stage1.Thm4.Alt51Q1
public import CFSG.GH74.GLS.C3.Layer1.Defs
public import CFSG.Mathlib.GroupTheory.Sylow.InvariantTransport
public import CFSG.GroupTheory.AutomorphismAction.MapEqOfMapsTo
public import TauCeti.GroupTheory.QuotientGroup.MulAut

public section

namespace CFSG.GH74.GLS.NT44

open CFSG.GH74.GLS.NT44.PermutationInputs
open CFSG.GH74.GLS.NT44.PermutationNative
open CFSG.GH74.GLS.NT44.PermutationActions
open CFSG.GH74.GLS.NT44.PermutationSylow
open CFSG.GH74.GLS

theorem exists_witness_of_faithful_action
    (hcheck : bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true)
    (hfixed : ∀ (B : Subgroup (MulAut Khat)),
      B ≤ T hcheck →
      Nonempty (B ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) →
      ∃ (s : B) (w : Khat), orderOf s = 2 ∧ orderOf w = 2 ∧
        w ∈ Subgroup.center Khat ∧
        w ∈ Subgroup.closure {d : Khat | ∃ (c : Khat) (a : B),
          c ∈ P0 hcheck ∧ (s : MulAut Khat) c = c ∧
          d = c⁻¹ * (a : MulAut Khat) c})
    (A : Type) [Group A]
    (hA : Nonempty (A ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))))
    (ρ : A →* MulAut Khat) (hρ : Function.Injective ρ)
    (P : Sylow 2 Khat)
    (hP : ∀ (a : A) (c : Khat), c ∈ (P : Subgroup Khat) →
      (ρ a) c ∈ (P : Subgroup Khat)) :
    ∃ (s : A) (w : Khat), orderOf s = 2 ∧ orderOf w = 2 ∧
      w ∈ Subgroup.center Khat ∧
      w ∈ Subgroup.closure {d : Khat | ∃ (c : Khat) (a : A),
        c ∈ (P : Subgroup Khat) ∧ (ρ s) c = c ∧
        d = c⁻¹ * (ρ a) c} := by
  classical
  obtain ⟨-, -, hcenterCard, -, -, htSylow, hcomap, -, -, -, -⟩ :=
    original_p0_sylow_preimage_spec hcheck
  have hcenterCard' : Nat.card (Subgroup.center Khat) = 2 ^ 4 := by
    rw [hcenterCard]; norm_num
  have hcenter : IsPGroup 2 (Subgroup.center Khat) :=
    IsPGroup.of_card hcenterCard'
  have hcardC4 : Nat.card (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) = 2 ^ 4 := by
    simp [ZMod.card]
  have hAcard : Nat.card A = 2 ^ 4 := by
    obtain ⟨e⟩ := hA
    rw [Nat.card_congr e.toEquiv, hcardC4]
  have hBcard : Nat.card ↥ρ.range = 2 ^ 4 := by
    have hbij : Function.Bijective ρ.rangeRestrict :=
      ⟨fun x y h => hρ (Subtype.ext_iff.mp h), MonoidHom.rangeRestrict_surjective ρ⟩
    rw [← Nat.card_congr (Equiv.ofBijective ρ.rangeRestrict hbij), hAcard]
  have hBpg : IsPGroup 2 ↥ρ.range := IsPGroup.of_card hBcard
  have hBP : ∀ β : MulAut Khat, β ∈ ρ.range →
      (P : Subgroup Khat).map β.toMonoidHom = (P : Subgroup Khat) := by
    intro β hβ
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hβ
    exact CFSG.GroupTheory.map_eq_of_mapsTo (ρ a) (fun c hc => hP a c hc)
  obtain ⟨α, hPα, hBα⟩ :=
    CFSG.SylowAction.exists_simultaneous_conjugation (p := 2) hcenter
      (tSylow hcheck) ρ.range hBpg P hBP
  have hP0 : (P : Subgroup Khat).map α.toMonoidHom = P0 hcheck := by
    rw [hPα, htSylow, hcomap]
  set f : MulAut Khat →* MulAut Khat := (MulAut.conj α).toMonoidHom with hf
  set B' : Subgroup (MulAut Khat) := ρ.range.map f with hB'def
  have hB'T : B' ≤ T hcheck := by
    rw [hB'def, hf, ← htSylow]
    exact hBα
  have hB'C4 : Nonempty (↥B' ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) := by
    obtain ⟨e⟩ := hA
    have hbij : Function.Bijective ρ.rangeRestrict :=
      ⟨fun x y h => hρ (Subtype.ext_iff.mp h), MonoidHom.rangeRestrict_surjective ρ⟩
    have e1 : ↥B' ≃* ↥ρ.range :=
      (Subgroup.equivMapOfInjective ρ.range f (MulAut.conj α).injective).symm
    have e2 : ↥ρ.range ≃* A := (MulEquiv.ofBijective ρ.rangeRestrict hbij).symm
    exact ⟨e1.trans (e2.trans e)⟩
  obtain ⟨s', w', hs'2, hw'2, hw'cen, hw'clos⟩ := hfixed B' hB'T hB'C4
  obtain ⟨b, hb, hbs⟩ := Subgroup.mem_map.mp s'.2
  obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hb
  refine ⟨a, (α⁻¹ : MulAut Khat) w', ?_, ?_, ?_, ?_⟩
  ·
    have hbs' : (MulAut.conj α) (ρ a) = (s' : MulAut Khat) := by
      simpa only [hf, MulEquiv.coe_toMonoidHom] using hbs
    have hs'2' : orderOf (s' : MulAut Khat) = 2 := by simpa using hs'2
    have h1 : orderOf (ρ a) = orderOf (s' : MulAut Khat) := by
      rw [orderOf_eq_orderOf_iff]
      intro n
      rw [← hbs']
      rw [(map_pow (MulAut.conj α) (ρ a) n).symm]
      exact (MulAut.conj α).map_eq_one_iff.symm
    have h2 : orderOf a = orderOf (ρ a) := by
      rw [orderOf_eq_orderOf_iff]
      intro n
      rw [(map_pow ρ a n).symm]
      exact (map_eq_one_iff ρ hρ).symm
    exact h2.trans (h1.trans hs'2')
  ·
    have h1 : orderOf ((α⁻¹ : MulAut Khat) w') = orderOf w' := by
      rw [orderOf_eq_orderOf_iff]
      intro n
      rw [← map_pow (α⁻¹ : MulAut Khat) w' n]
      exact (MulEquiv.map_eq_one_iff (α⁻¹ : MulAut Khat))
    exact h1.trans hw'2
  ·
    rw [Subgroup.mem_center_iff] at hw'cen ⊢
    intro y
    apply α.injective
    calc α (y * (α⁻¹ : MulAut Khat) w') = α y * w' := by simp
      _ = w' * α y := hw'cen (α y)
      _ = α ((α⁻¹ : MulAut Khat) w' * y) := by simp
  ·
    set S : Set Khat := {d : Khat | ∃ (c : Khat) (a0 : A),
      c ∈ (P : Subgroup Khat) ∧ (ρ a) c = c ∧ d = c⁻¹ * (ρ a0) c} with hSdef
    set S' : Set Khat := {d : Khat | ∃ (c : Khat) (a : ↥B'),
      c ∈ P0 hcheck ∧ (s' : MulAut Khat) c = c ∧
      d = c⁻¹ * (a : MulAut Khat) c} with hS'def
    have hbs' : (MulAut.conj α) (ρ a) = (s' : MulAut Khat) := by
      simpa only [hf, MulEquiv.coe_toMonoidHom] using hbs
    have hconj_apply : ∀ (x : MulAut Khat) (y : Khat),
        ((MulAut.conj α) x) (α y) = α (x y) := by
      intro x y
      simp only [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply,
        MulEquiv.symm_apply_apply]
    have hSS' : ∀ d ∈ S, α d ∈ S' := by
      rintro d ⟨c, a0, hcP, hfix, rfl⟩
      refine ⟨α c, ⟨(MulAut.conj α) (ρ a0),
        Subgroup.mem_map_of_mem f (MonoidHom.mem_range.mpr ⟨a0, rfl⟩)⟩, ?_, ?_, ?_⟩
      · rw [← hP0]
        exact Subgroup.mem_map_of_mem α.toMonoidHom hcP
      · rw [← hbs', hconj_apply]
        exact congrArg α hfix
      · simp only [map_mul, map_inv, hconj_apply]
    have hS'S : ∀ d' ∈ S', ∃ d ∈ S, α d = d' := by
      rintro d' ⟨c', a', hc'P0, hfix', rfl⟩
      have hc'mem : c' ∈ (P : Subgroup Khat).map α.toMonoidHom := by
        rw [hP0]; exact hc'P0
      obtain ⟨c, hcP, rfl⟩ := Subgroup.mem_map.mp hc'mem
      obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp a'.2
      obtain ⟨a0, rfl⟩ := MonoidHom.mem_range.mp hb
      have hba' : (MulAut.conj α) (ρ a0) = (a' : MulAut Khat) := by
        simpa only [hf, MulEquiv.coe_toMonoidHom] using hba
      refine ⟨c⁻¹ * (ρ a0) c, ⟨c, a0, hcP, ?_, rfl⟩, ?_⟩
      ·
        have hfix'' : ((MulAut.conj α) (ρ a)) (α c) = α c := by
          rw [hbs']
          exact hfix'
        have hval : α ((ρ a) c) = α c := by
          rw [hconj_apply] at hfix''
          exact hfix''
        exact α.injective hval
      ·
        rw [map_mul, map_inv, ← hba']
        simp only [MulEquiv.coe_toMonoidHom, hconj_apply]
    have hSet : S' = α.toMonoidHom '' S := by
      ext d
      constructor
      · intro hd
        obtain ⟨d0, hd0, hd0eq⟩ := hS'S d hd
        exact ⟨d0, hd0, hd0eq⟩
      · rintro ⟨d0, hd0, rfl⟩
        exact hSS' d0 hd0
    have hclos : Subgroup.closure S' = (Subgroup.closure S).map α.toMonoidHom := by
      rw [MonoidHom.map_closure, hSet]
    have hmem : w' ∈ (Subgroup.closure S).map α.toMonoidHom := by
      rw [← hclos]
      exact hw'clos
    obtain ⟨y, hy, hwy⟩ := Subgroup.mem_map.mp hmem
    have hyw : y = (α⁻¹ : MulAut Khat) w' := by
      apply α.injective
      have hwy' : α y = w' := by simpa using hwy
      rw [hwy']
      exact (MulEquiv.apply_symm_apply α w').symm
    rwa [hyw] at hy

theorem exists_witness_of_mulEquiv
    (hcheck : bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true)
    (hfixed : ∀ (B : Subgroup (MulAut Khat)),
      B ≤ T hcheck →
      Nonempty (B ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) →
      ∃ (s : B) (w : Khat), orderOf s = 2 ∧ orderOf w = 2 ∧
        w ∈ Subgroup.center Khat ∧
        w ∈ Subgroup.closure {d : Khat | ∃ (c : Khat) (a : B),
          c ∈ P0 hcheck ∧ (s : MulAut Khat) c = c ∧
          d = c⁻¹ * (a : MulAut Khat) c})
    (Q : Type) [Group Q] (E : Khat ≃* Q)
    (A : Type) [Group A]
    (hA : Nonempty (A ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))))
    (ρ : A →* MulAut Q) (hρ : Function.Injective ρ)
    (P : Sylow 2 Q)
    (hP : ∀ (a : A) (c : Q), c ∈ (P : Subgroup Q) →
      (ρ a) c ∈ (P : Subgroup Q)) :
    ∃ (s : A) (w : Q), orderOf s = 2 ∧ orderOf w = 2 ∧
      w ∈ Subgroup.center Q ∧
      w ∈ Subgroup.closure {d : Q | ∃ (c : Q) (a : A),
        c ∈ (P : Subgroup Q) ∧ (ρ s) c = c ∧
        d = c⁻¹ * (ρ a) c} := by
  classical
  let : Finite Q := Finite.of_injective (E.symm : Q → Khat) E.symm.injective
  let ρK : A →* MulAut Khat := (MulAut.congr E.symm).toMonoidHom.comp ρ
  have hρK : Function.Injective ρK := by
    intro a b hab
    apply hρ
    exact (MulAut.congr E.symm).injective hab
  have hequiv : ∀ (a : A) (c : Khat), E ((ρK a) c) = (ρ a) (E c) := by
    intro a c
    simp only [ρK, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
      MulEquiv.trans_apply, MulEquiv.symm_symm, MulEquiv.apply_symm_apply]
  let PK : Sylow 2 Khat := P.mapSurjective (f := E.symm.toMonoidHom) E.symm.surjective
  have hPKcoe : (PK : Subgroup Khat) = (P : Subgroup Q).map E.symm.toMonoidHom :=
    Sylow.coe_mapSurjective E.symm.surjective P
  have hPKinv : ∀ (a : A) (c : Khat), c ∈ (PK : Subgroup Khat) →
      (ρK a) c ∈ (PK : Subgroup Khat) := by
    intro a c hc
    rw [hPKcoe] at hc ⊢
    obtain ⟨cQ, hcQ, rfl⟩ := Subgroup.mem_map.mp hc
    have h1 : (ρK a) (E.symm.toMonoidHom cQ) = E.symm.toMonoidHom ((ρ a) cQ) := by
      simp only [ρK, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
        MulEquiv.trans_apply, MulEquiv.symm_symm, MulEquiv.apply_symm_apply]
    rw [h1]
    exact Subgroup.mem_map_of_mem E.symm.toMonoidHom (hP a cQ hcQ)
  obtain ⟨s, wK, hs2, hwK2, hwKcen, hwKclos⟩ :=
    exists_witness_of_faithful_action hcheck hfixed A hA ρK hρK PK hPKinv
  refine ⟨s, E wK, hs2, ?_, ?_, ?_⟩
  · have h1 : orderOf (E wK) = orderOf wK := by
      rw [orderOf_eq_orderOf_iff]
      intro n
      rw [(map_pow E wK n).symm]
      exact (MulEquiv.map_eq_one_iff E)
    exact h1.trans hwK2
  · rw [Subgroup.mem_center_iff] at hwKcen ⊢
    intro y
    obtain ⟨x, rfl⟩ := E.surjective y
    calc E x * E wK = E (x * wK) := by simp
      _ = E (wK * x) := by rw [hwKcen x]
      _ = E wK * E x := by simp
  · set SQ : Set Q := {d : Q | ∃ (c : Q) (a0 : A),
      c ∈ (P : Subgroup Q) ∧ (ρ s) c = c ∧ d = c⁻¹ * (ρ a0) c} with hSQdef
    set SK : Set Khat := {d : Khat | ∃ (c : Khat) (a0 : A),
      c ∈ (PK : Subgroup Khat) ∧ (ρK s) c = c ∧ d = c⁻¹ * (ρK a0) c} with hSKdef
    have hSK_SQ : ∀ d ∈ SK, E d ∈ SQ := by
      rintro d ⟨c, a0, hcP, hfix, rfl⟩
      have hc' : c ∈ (P : Subgroup Q).map E.symm.toMonoidHom := by
        rw [← hPKcoe]; exact hcP
      obtain ⟨cQ, hcQ, rfl⟩ := Subgroup.mem_map.mp hc'
      refine ⟨cQ, a0, hcQ, ?_, ?_⟩
      · have h := congrArg E hfix
        simpa only [hequiv, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] using h
      · simp only [map_mul, map_inv, hequiv, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    have hSQ_SK : ∀ d ∈ SQ, ∃ d0 ∈ SK, E d0 = d := by
      rintro d ⟨cQ, a0, hcQ, hfix, rfl⟩
      have hcK : E.symm cQ ∈ (PK : Subgroup Khat) := by
        rw [hPKcoe]
        exact Subgroup.mem_map_of_mem E.symm.toMonoidHom hcQ
      refine ⟨(E.symm cQ)⁻¹ * (ρK a0) (E.symm cQ), ⟨E.symm cQ, a0, hcK, ?_, rfl⟩, ?_⟩
      · apply E.injective
        rw [hequiv s (E.symm cQ)]
        simp only [MulEquiv.apply_symm_apply]
        exact hfix
      · simp only [map_mul, map_inv, hequiv, MulEquiv.apply_symm_apply]
    have hSet : SQ = E.toMonoidHom '' SK := by
      ext d
      constructor
      · intro hd
        obtain ⟨d0, hd0, rfl⟩ := hSQ_SK d hd
        exact ⟨d0, hd0, rfl⟩
      · rintro ⟨d0, hd0, rfl⟩
        exact hSK_SQ d0 hd0
    have hclos : Subgroup.closure SQ = (Subgroup.closure SK).map E.toMonoidHom := by
      rw [MonoidHom.map_closure, hSet]
    have hmem : E wK ∈ (Subgroup.closure SK).map E.toMonoidHom :=
      Subgroup.mem_map_of_mem E.toMonoidHom hwKclos
    rwa [← hclos] at hmem

private theorem exists_involution_mem_zStar_sylow_commutator_closure_of_fixed
    (hcheck : bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true)
    (hfixed : ∀ (B : Subgroup (MulAut Khat)),
      B ≤ T hcheck →
      Nonempty (B ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) →
      ∃ (s : B) (w : Khat), orderOf s = 2 ∧ orderOf w = 2 ∧
        w ∈ Subgroup.center Khat ∧
        w ∈ Subgroup.closure {d : Khat | ∃ (c : Khat) (a : B),
          c ∈ P0 hcheck ∧ (s : MulAut Khat) c = c ∧
          d = c⁻¹ * (a : MulAut Khat) c})
    {G : Type} [Group G] [Finite G] (L : Subgroup G)
    (hL : CFSG.IsQuasisimple (CFSG.GH74.GLS.kBar L))
    (hL34 : CFSG.GH74.GLS.IsL34Quotient (CFSG.GH74.GLS.kBar L))
    (h16 : Nat.card (Subgroup.center (CFSG.GH74.GLS.kBar L)) = 16)
    (A : Type) [Group A]
    (hA : Nonempty
      (A ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))))
    (ρ : A →* MulAut L)
    (hfaithful : Function.Injective
      (fun a : A => MulAut.mapQuotient (CFSG.pPrimeCore 2 L) (ρ a)))
    (P : Sylow 2 L)
    (hP : ∀ (a : A) (c : L), c ∈ (P : Subgroup L) →
      (ρ a) c ∈ (P : Subgroup L)) :
    ∃ (s : A) (w : L),
      orderOf s = 2 ∧ orderOf w = 2 ∧
      w ∈ (P : Subgroup L) ∧
      (w : G) ∈ CFSG.GH74.GLS.zStar L ∧
      w ∈ Subgroup.closure
        {d : L | ∃ (c : L) (a : A),
          c ∈ (P : Subgroup L) ∧ (ρ s) c = c ∧
          d = c⁻¹ * (ρ a) c} := by
  classical
  let Q := CFSG.GH74.GLS.kBar L
  have : Finite Q := inferInstance
  let q : ↥L →* Q := CFSG.GH74.GLS.Stage1.Thm2.Recip.hatMk L
  have hqsurj : Function.Surjective q := by
    simpa only [q] using CFSG.GH74.GLS.Stage1.Thm2.Recip.hatMk_surjective L
  let PQ : Sylow 2 Q := P.mapSurjective (f := q) hqsurj
  have hPQcoe : (PQ : Subgroup Q) = (P : Subgroup ↥L).map q :=
    Sylow.coe_mapSurjective hqsurj P
  let ρQ : A →* MulAut Q :=
    (MulAut.mapQuotient (CFSG.pPrimeCore 2 ↥L)).comp ρ
  have hρQ : Function.Injective ρQ := hfaithful
  have hequiv : ∀ (a : A) (c : ↥L), q ((ρ a) c) = (ρQ a) (q c) := by
    intro a c
    simp only [q, ρQ, MonoidHom.comp_apply]
    exact (MulAut.mapQuotient_mk (CFSG.pPrimeCore 2 ↥L) (ρ a) c).symm
  have hPQinv : ∀ (a : A) (c : Q), c ∈ (PQ : Subgroup Q) →
      (ρQ a) c ∈ (PQ : Subgroup Q) := by
    intro a c hc
    rw [hPQcoe] at hc ⊢
    obtain ⟨cL, hcL, rfl⟩ := Subgroup.mem_map.mp hc
    rw [← hequiv a cL]
    exact Subgroup.mem_map_of_mem q (hP a cL hcL)
  obtain ⟨b, lambda, e, hqcomp, hqsurjQ, hlam, hlam_eq, hqe, hlamker, hmap, hqker, -⟩ :=
    CFSG.GH74.GLS.NT44.actualCoverOfL34 Q hL hL34 h16
  obtain ⟨e0, -, -, -⟩ := PermutationModel.fullTwoCover_equiv_original_model hcheck
  have hE : Khat ≃* Q := e0.symm.trans e
  obtain ⟨s, wQ, hs2, hwQ2, hwQcen, hwQclos⟩ :=
    exists_witness_of_mulEquiv hcheck hfixed Q hE A hA ρQ hρQ PQ hPQinv
  set SQ : Set Q := {d : Q | ∃ (c : Q) (a0 : A),
      c ∈ (PQ : Subgroup Q) ∧ (ρQ s) c = c ∧ d = c⁻¹ * (ρQ a0) c} with hSQdef
  have hSQ_sub : SQ ⊆ (PQ : Subgroup Q) := by
    rintro d ⟨c, a0, hc, -, rfl⟩
    exact (PQ : Subgroup Q).mul_mem ((PQ : Subgroup Q).inv_mem hc) (hPQinv a0 c hc)
  have hwQmem : wQ ∈ (PQ : Subgroup Q) :=
    (Subgroup.closure_le (PQ : Subgroup Q)).mpr hSQ_sub hwQclos
  rw [hPQcoe] at hwQmem
  obtain ⟨w, hwP, hwq⟩ := Subgroup.mem_map.mp hwQmem
  have hqinj : ∀ x : ↥P, q (x : ↥L) = 1 → x = 1 := by
    intro x hx
    have hx2 : ∃ k : ℕ, (x : ↥L) ^ (2 ^ k) = 1 := by
      obtain ⟨k, hk⟩ := P.isPGroup' x
      exact ⟨k, by simpa using congrArg (fun z : ↥P => (z : ↥L)) hk⟩
    have hxL : (x : ↥L) = 1 :=
      CFSG.GH74.GLS.Stage1.Thm4.Alt51.eq_one_of_hat_eq_one
        (K := L) (x : ↥L) hx hx2
    exact Subtype.ext (by simpa using hxL)
  have hqinj_inj : Function.Injective (q.comp (P : Subgroup ↥L).subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact hqinj x hx
  refine ⟨s, w, hs2, ?_, hwP, ?_, ?_⟩
  ·
    have hwne : w ≠ 1 := by
      intro h
      have h1 : orderOf wQ = 1 := by rw [← hwq, h]; simp
      rw [hwQ2] at h1
      exact (by norm_num : (2 : ℕ) ≠ 1) h1
    have hwpow : w ^ 2 = 1 := by
      have hwQpow : wQ ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by norm_num [hwQ2])
      have hq1 : q (w ^ 2) = 1 := by rw [map_pow, hwq, hwQpow]
      have hw2in : w ^ 2 ∈ (P : Subgroup ↥L) := (P : Subgroup ↥L).pow_mem hwP 2
      have h : (⟨w ^ 2, hw2in⟩ : ↥P) = 1 := hqinj ⟨w ^ 2, hw2in⟩ hq1
      simpa using congrArg Subtype.val h
    exact orderOf_eq_prime hwpow hwne
  ·
    rw [CFSG.GH74.GLS.Stage1.Thm4.Alt51.mem_zStar_iff_hat_mem_center]
    simpa only [q, hwq] using hwQcen
  ·
    set SL : Set ↥L := {d : ↥L | ∃ (c : ↥L) (a0 : A),
        c ∈ (P : Subgroup ↥L) ∧ (ρ s) c = c ∧ d = c⁻¹ * (ρ a0) c} with hSLdef
    have hSL_sub : SL ⊆ (P : Subgroup ↥L) := by
      rintro d ⟨c, a0, hc, -, rfl⟩
      exact (P : Subgroup ↥L).mul_mem ((P : Subgroup ↥L).inv_mem hc) (hP a0 c hc)
    have hSL_SQ : ∀ d ∈ SL, q d ∈ SQ := by
      rintro d ⟨c, a0, hcP, hfix, rfl⟩
      refine ⟨q c, a0, Subgroup.mem_map_of_mem q hcP, ?_, ?_⟩
      · rw [← hequiv s c]
        exact congrArg q hfix
      · simp only [map_mul, map_inv, hequiv]
    have hSQ_SL : ∀ d ∈ SQ, ∃ d0 ∈ SL, q d0 = d := by
      rintro d ⟨cQ, a0, hcQ, hfix, rfl⟩
      rw [hPQcoe] at hcQ
      obtain ⟨c, hcP, rfl⟩ := Subgroup.mem_map.mp hcQ
      refine ⟨c⁻¹ * (ρ a0) c, ⟨c, a0, hcP, ?_, rfl⟩, ?_⟩
      · have hfixq : q ((ρ s) c) = q c := by rw [hequiv, hfix]
        have heqsub : (⟨(ρ s) c, hP s c hcP⟩ : ↥P) = ⟨c, hcP⟩ :=
          hqinj_inj (by simpa using hfixq)
        exact congrArg Subtype.val heqsub
      · simp only [map_mul, map_inv, hequiv]
    have hSet : SQ = q '' SL := by
      ext d
      constructor
      · intro hd
        obtain ⟨d0, hd0, hd0eq⟩ := hSQ_SL d hd
        exact ⟨d0, hd0, hd0eq⟩
      · rintro ⟨d0, hd0, rfl⟩
        exact hSL_SQ d0 hd0
    have hclos : Subgroup.closure SQ = (Subgroup.closure SL).map q := by
      rw [MonoidHom.map_closure, hSet]
    have hmem : wQ ∈ (Subgroup.closure SL).map q := by
      rw [← hclos]
      exact hwQclos
    obtain ⟨d, hd, hqd⟩ := Subgroup.mem_map.mp hmem
    have hdP : d ∈ (P : Subgroup ↥L) := (Subgroup.closure_le (P : Subgroup ↥L)).mpr hSL_sub hd
    have heq : (⟨d, hdP⟩ : ↥P) = ⟨w, hwP⟩ := by
      apply hqinj_inj
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
      rw [hqd, hwq]
    have hdw : d = w := congrArg Subtype.val heq
    rwa [hdw] at hd

theorem exists_involution_mem_zStar_sylow_commutator_closure
    {G : Type} [Group G] [Finite G] (L : Subgroup G)
    (hL : CFSG.IsQuasisimple (CFSG.GH74.GLS.kBar L))
    (hL34 : CFSG.GH74.GLS.IsL34Quotient (CFSG.GH74.GLS.kBar L))
    (h16 : Nat.card (Subgroup.center (CFSG.GH74.GLS.kBar L)) = 16)
    (A : Type) [Group A]
    (hA : Nonempty
      (A ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))))
    (ρ : A →* MulAut L)
    (hfaithful : Function.Injective
      (fun a : A => MulAut.mapQuotient (CFSG.pPrimeCore 2 L) (ρ a)))
    (P : Sylow 2 L)
    (hP : ∀ (a : A) (c : L), c ∈ (P : Subgroup L) →
      (ρ a) c ∈ (P : Subgroup L)) :
    ∃ (s : A) (w : L),
      orderOf s = 2 ∧ orderOf w = 2 ∧
      w ∈ (P : Subgroup L) ∧
      (w : G) ∈ CFSG.GH74.GLS.zStar L ∧
      w ∈ Subgroup.closure
        {d : L | ∃ (c : L) (a : A),
          c ∈ (P : Subgroup L) ∧ (ρ s) c = c ∧
          d = c⁻¹ * (ρ a) c} := by
  exact exists_involution_mem_zStar_sylow_commutator_closure_of_fixed
    Certificates.certificate1212003
    (fun B hBT hB =>
      CFSG.GH74.GLS.NT44.PermutationCommutator.exists_central_involution_mem_commutator_closure
        Certificates.certificate1212003 B hBT hB)
    L hL hL34 h16 A hA ρ hfaithful P hP

end CFSG.GH74.GLS.NT44
