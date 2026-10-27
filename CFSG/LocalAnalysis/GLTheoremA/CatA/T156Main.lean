module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156Trans
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156Facts
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Trans
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156Layer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T156

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.S267
open scoped commutatorElement

section Identities

variable {G : Type} [Group G] [Finite G]

theorem map_centralizer_subgroupOf {H L : Subgroup G} {b : G} (hLH : L ≤ H) (hb : b ∈ H) :
    ((L.subgroupOf H) ⊓ Subgroup.centralizer ({(⟨b, hb⟩ : ↥H)} : Set ↥H) : Subgroup ↥H).map H.subtype =
      L ⊓ Subgroup.centralizer ({b} : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyL, hyC⟩ := Subgroup.mem_inf.1 hy
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.1 hyL, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hyC ⊢
    have := congrArg Subtype.val hyC
    simpa using this
  · intro hx
    obtain ⟨hxL, hxC⟩ := Subgroup.mem_inf.1 hx
    refine ⟨⟨x, hLH hxL⟩, ?_, rfl⟩
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.2 hxL, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hxC ⊢
    apply Subtype.ext
    simpa using hxC

theorem map_centralizer_omega {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {A : Type} [Group A] [Finite A]
    {M : Subgroup A} {b : A} (π : A →* Ω) (hN : ¬ p ∣ Nat.card π.ker) (hp : p.Prime)
    (hE : IsPGroup p (Subgroup.zpowers b)) (hEM : Subgroup.zpowers b ≤ Subgroup.normalizer (M : Set A)) :
    (M ⊓ Subgroup.centralizer ({b} : Set A)).map π =
      M.map π ⊓ Subgroup.centralizer ({π b} : Set Ω) := by
  rw [← centralizer_zpowers_eq b, map_inf_centralizer hp π hN hE hEM, MonoidHom.map_zpowers,
    centralizer_zpowers_eq]

end Identities

section Injective

variable {G : Type} [Group G] [Finite G]

theorem injOn_of_pgroup {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {A : Type} [Group A] [Finite A]
    (hp : p.Prime) (π : A →* Ω) (hN : ¬ p ∣ Nat.card π.ker) {P : Subgroup A} (hP : IsPGroup p P)
    {u v : A} (hu : u ∈ P) (hv : v ∈ P) (huv : π u = π v) : u = v := by
  have h1 : u * v⁻¹ ∈ P ⊓ π.ker := by
    rw [Subgroup.mem_inf]
    refine ⟨P.mul_mem hu (P.inv_mem hv), ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, huv, mul_inv_cancel]
  rw [inf_ker_eq_bot' hp π hN hP, Subgroup.mem_bot] at h1
  exact (mul_inv_eq_one.1 h1)

theorem mem_map_iff_of_injOn {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {A : Type} [Group A] [Finite A]
    (hp : p.Prime) (π : A →* Ω) (hN : ¬ p ∣ Nat.card π.ker) {P T : Subgroup A} (hP : IsPGroup p P)
    (hTP : T ≤ P) {x : A} (hx : x ∈ P) : π x ∈ T.map π ↔ x ∈ T := by
  constructor
  · intro h
    obtain ⟨t, ht, hte⟩ := Subgroup.mem_map.1 h
    have : t = x := injOn_of_pgroup hp π hN hP (hTP ht) hx hte
    rw [← this]
    exact ht
  · intro h
    exact Subgroup.mem_map_of_mem π h

end Injective

section CentMod

variable {G : Type} [Group G] [Finite G]

theorem map_centMod_subgroupOf {p : ℕ} (hp : p.Prime) {H L B : Subgroup G} (hLH : L ≤ H) (hBH : B ≤ H)
    (hHN : H ≤ Subgroup.normalizer (L : Set G)) :
    ((B.subgroupOf H) ⊓ centModSubgroup p (L.subgroupOf H)).map H.subtype =
      B ⊓ centModSubgroup p L := by
  have hNH : ¬ p ∣ Nat.card (H.subtype : ↥H →* G).ker := not_dvd_card_ker_subtype hp H
  have hKL : (L.subgroupOf H).map H.subtype = L := Subgroup.map_subgroupOf_eq_of_le hLH
  have hiff : ∀ y : ↥H, y ∈ Subgroup.normalizer ((L.subgroupOf H : Subgroup ↥H) : Set ↥H) →
      (y ∈ centModSubgroup p (L.subgroupOf H) ↔ (y : G) ∈ centModSubgroup p L) := by
    intro y hy
    have h := mem_centModSubgroup_map_iff hp H.subtype hNH hy
    rw [hKL] at h
    exact h
  have hNorm : ∀ h : ↥H, h ∈ Subgroup.normalizer ((L.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
    intro h
    have hKH : (L.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).2 hHN
    rw [Subgroup.normalizer_eq_top_iff.2 hKH]
    exact Subgroup.mem_top h
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyB, hyC⟩ := Subgroup.mem_inf.1 hy
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.1 hyB, ?_⟩
    exact (hiff y (hNorm y)).1 hyC
  · intro hx
    obtain ⟨hxB, hxC⟩ := Subgroup.mem_inf.1 hx
    have hxH : x ∈ H := hBH hxB
    refine ⟨⟨x, hxH⟩, Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.2 hxB, ?_⟩, rfl⟩
    exact (hiff ⟨x, hxH⟩ (hNorm _)).2 hxC

end CentMod

end CFSG.LocalAnalysis.GLTheoremA.T156

end

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T156

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.S267
open scoped commutatorElement

section Core

variable {G : Type} [Group G] [Finite G]

set_option maxHeartbeats 400000 in
theorem concl_of_H {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hΩ : T156FactOmega p)
    {B L : Subgroup G} {b : G} {H : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (PQuot p L))
    (hBN : B ≤ Subgroup.normalizer (L : Set G)) (hel : IsElemAbelian p B) (hb : b ∈ B)
    (hCh : IsChevSimple 2 (PSimple p L))
    (hDd : ∀ c ∈ B, NonInnDiag p c L → FieldOn p c L ∨ (p = 3 ∧ IsTD4 3 L))
    (hR : R2Prop p b L)
    (hcent : p = 3 → IsTD4 3 L → centCard2 3 L b = Nat.sqrt (card2 3 L))
    (hcard : p ^ 3 * Nat.card ↥(B ⊓ centModSubgroup p L) ≤ Nat.card B)
    (hLH : L ≤ H) (hBH : B ≤ H) (hHN : H ≤ Subgroup.normalizer (L : Set G)) :
    (Ipart p L b ≠ ⊥ ∧
        (∀ c ∈ B, CentMod p (Ipart p L b) c ↔ c ∈ Subgroup.zpowers b ⊔ (B ⊓ centModSubgroup p L)) ∧
        InnDiagOn p B (Ipart p L b)) ∨
      (p = 3 ∧ catalogIs (PSimple 3 L) S9.isU3eight) := by
  classical
  have hNH : ¬ p ∣ Nat.card (H.subtype : ↥H →* G).ker := not_dvd_card_ker_subtype hp H
  have hNH3 : ¬ 3 ∣ Nat.card (H.subtype : ↥H →* G).ker := not_dvd_card_ker_subtype Nat.prime_three H
  have hKL : (L.subgroupOf H).map H.subtype = L := Subgroup.map_subgroupOf_eq_of_le hLH
  have hKH : (L.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).2 hHN
  have hHnorm : ∀ h : ↥H, h ∈ Subgroup.normalizer ((L.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
    intro h
    rw [Subgroup.normalizer_eq_top_iff.2 hKH]
    exact Subgroup.mem_top h
  have hN0n : (GLAPPrimeCoreOf p (L.subgroupOf H)).Normal := by
    have h := normalizer_le_normalizer_glaPPrimeCoreOf p (L.subgroupOf H)
    rw [Subgroup.normalizer_eq_top_iff.2 hKH, top_le_iff] at h
    exact Subgroup.normalizer_eq_top_iff.1 h
  haveI := hN0n
  set N0 : Subgroup ↥H := GLAPPrimeCoreOf p (L.subgroupOf H) with hN0def
  set π : ↥H →* ↥H ⧸ N0 := QuotientGroup.mk' N0 with hπdef
  have hN : ¬ p ∣ Nat.card π.ker := by
    rw [hπdef, QuotientGroup.ker_mk']
    exact not_dvd_card_glaPPrimeCoreOf hp _
  set K₀ : Subgroup ↥H := L.subgroupOf H with hK₀def
  set S : Subgroup (↥H ⧸ N0) := K₀.map π with hSdef
  set BH : Subgroup ↥H := B.subgroupOf H with hBHdef
  set A : Subgroup (↥H ⧸ N0) := BH.map π with hAdef
  set bH : ↥H := ⟨b, hBH hb⟩ with hbHdef
  set bΩ : ↥H ⧸ N0 := π bH with hbΩdef
  have hbHB : bH ∈ BH := Subgroup.mem_subgroupOf.2 hb
  have hBHel : IsElemAbelian p BH := isElemAbelian_subgroupOf hel H
  have hBHp : IsPGroup p BH := isPGroup_of_isElemAbelian hBHel
  have hBHN : BH ≤ Subgroup.normalizer ((K₀ : Subgroup ↥H) : Set ↥H) := fun c _ => hHnorm c
  have hbp : bH ^ p = 1 := Subtype.ext (by simpa using hel.2 b hb)
  have hcomm : ∀ c : ↥H, c ∈ BH → c * bH = bH * c := by
    intro c hc
    have hcB : (c : G) ∈ B := Subgroup.mem_subgroupOf.1 hc
    have h := congrArg Subtype.val (hel.1.is_comm.comm ⟨(c : G), hcB⟩ ⟨b, hb⟩)
    exact Subtype.ext h
  set JH : Subgroup ↥H := GLAPLayer p (K₀ ⊓ Subgroup.centralizer ({bH} : Set ↥H)) with hJHdef
  have hYG : (K₀ ⊓ Subgroup.centralizer ({bH} : Set ↥H)).map H.subtype = L ⊓ Subgroup.centralizer ({b} : Set G) :=
    map_centralizer_subgroupOf hLH (hBH hb)
  have hEp : IsPGroup p (Subgroup.zpowers bH) := isPGroup_zpowers_of_pow_eq_one hbp
  have hEM : Subgroup.zpowers bH ≤ Subgroup.normalizer (K₀ : Set ↥H) := Subgroup.zpowers_le.2 (hHnorm bH)
  have hYΩ : (K₀ ⊓ Subgroup.centralizer ({bH} : Set ↥H)).map π = S ⊓ Subgroup.centralizer ({bΩ} : Set (↥H ⧸ N0)) :=
    map_centralizer_omega π hN hp hEp hEM
  have hJG : JH.map H.subtype = Ipart p L b := by
    rw [hJHdef, map_glaPLayer hp H.subtype hNH, hYG]
  have hJΩ : JH.map π = Ipart p S bΩ := by
    rw [hJHdef, map_glaPLayer hp π hN, hYΩ]
  set eL : PQuot p L ≃* PQuot p S := compIso hp hKL π hN with heLdef
  have hqPS : CFSG.Open.IsQuasisimple (PQuot p S) := hq.of_mulEquiv eL.symm
  have hSp : GLAPPrimeCore p ↥S = ⊥ := by
    have h1 : (GLAPPrimeCoreOf p K₀).map π = GLAPPrimeCoreOf p S := map_glaPPrimeCoreOf hp π hN K₀
    have h2 : (GLAPPrimeCoreOf p K₀).map π = ⊥ := by
      rw [Subgroup.map_eq_bot_iff]
      rw [hπdef, QuotientGroup.ker_mk']
    have h3 : GLAPPrimeCoreOf p S = ⊥ := by rw [← h1, h2]
    exact (Subgroup.map_eq_bot_iff_of_injective _ S.subtype_injective).1 h3
  have eS : PQuot p S ≃* ↥S := (QuotientGroup.quotientMulEquivOfEq hSp).trans QuotientGroup.quotientBot
  have hqS : CFSG.Open.IsQuasisimple ↥S := hqPS.of_mulEquiv eS.symm
  have hChS : IsChevSimple 2 (PSimple p S) := isChevSimple_congr (psimpleIso eL) hCh
  have hSn : S.Normal := hKH.map π (QuotientGroup.mk'_surjective N0)
  have hNS : A ≤ Subgroup.normalizer (S : Set (↥H ⧸ N0)) := by
    intro a ha
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 ha
    exact map_normalizer_mem π (hHnorm c)
  have hAel : IsElemAbelian p A := CFSG.SectionRank.isElemAbelian_map hBHel π
  have hbA : bΩ ∈ A := Subgroup.mem_map_of_mem π hbHB
  have hNbΩ : bΩ ∈ Subgroup.normalizer (S : Set (↥H ⧸ N0)) := hNS hbA
  have hRb : R2Prop p bΩ S := by
    rcases hR with hF | ⟨hp3, hT, hNI⟩
    · left
      exact fieldOn_to_Omega eL hNbΩ (compIso_rel hp hKL π hN (hHnorm bH)) hF
    · right
      refine ⟨hp3, (isTD4_congr hp3 eL).1 hT, hNbΩ, ?_⟩
      intro hI
      apply hNI.2
      have hN3 : ¬ 3 ∣ Nat.card π.ker := by rw [← hp3]; exact hN
      have h1 : InducesInnerMod 3 K₀ bH := inducesInnerMod_of_map Nat.prime_three π hN3 (hHnorm bH) hI
      have h2 := inducesInnerMod_map Nat.prime_three H.subtype hNH3 h1
      rw [hKL] at h2
      exact h2
  have hcentS : (p = 3 → IsTD4 3 S → centCard2 3 S bΩ = Nat.sqrt (card2 3 S)) := by
    intro h3 hT'
    have hT : IsTD4 3 L := (isTD4_congr h3 eL).2 hT'
    have c1 := centCard2_compIso hp hKL π hN (hHnorm bH)
    have c2 := card2_compIso hp hKL π hN
    rw [h3] at c1 c2
    rw [← c2]
    rw [← c1]
    exact hcent h3 hT
  have hcardS : p ^ 3 * Nat.card ↥(A ⊓ centModSubgroup p S) ≤ Nat.card A := by
    have e1 : Nat.card ↥(A ⊓ centModSubgroup p S) = Nat.card ↥(BH ⊓ centModSubgroup p K₀) :=
      card_inf_centModSubgroup_map hp π hN hBHp hBHN
    have e2 : Nat.card ↥(BH ⊓ centModSubgroup p K₀) = Nat.card ↥(B ⊓ centModSubgroup p L) := by
      rw [← map_centMod_subgroupOf hp hLH hBH hHN]
      exact (Subgroup.card_map_of_injective H.subtype_injective).symm
    have e3a : Nat.card A = Nat.card BH := card_map_of_isPGroup hp π hN hBHp
    have e3b : Nat.card BH = Nat.card B := by
      have h := Subgroup.card_map_of_injective (f := H.subtype) H.subtype_injective (K := BH)
      rw [Subgroup.map_subgroupOf_eq_of_le hBH] at h
      exact h.symm
    rw [e1, e2, e3a, e3b]
    exact hcard
  have hdich : ∀ c ∈ A, NonInnDiag p c S → FieldOn p c S ∨ (p = 3 ∧ IsTD4 3 S) := by
    intro c hc hND
    obtain ⟨cH, hcH, rfl⟩ := Subgroup.mem_map.1 hc
    have hcB : (cH : G) ∈ B := Subgroup.mem_subgroupOf.1 hcH
    have hA'S : Subgroup.zpowers (π cH) ≤ Subgroup.normalizer (S : Set (↥H ⧸ N0)) :=
      Subgroup.zpowers_le.2 (hNS (Subgroup.mem_map_of_mem π hcH))
    have hcorr : ∀ a' ∈ Subgroup.zpowers (π cH), ∃ a ∈ Subgroup.zpowers (cH : G),
        ∀ x x', indRel p L a x x' ↔ indRel p S a' (eL x) (eL x') := by
      intro a' ha'
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha'
      refine ⟨(cH : G) ^ n, Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) n, fun x x' => ?_⟩
      have h := compIso_rel hp hKL π hN (hHnorm (cH ^ n)) x x'
      rw [Subgroup.coe_zpow, map_zpow] at h
      exact h
    have hND' : NonInnDiag p (cH : G) L := by
      refine ⟨hBN hcB, fun hI => hND.2 ?_⟩
      exact innDiagOn_to_Omega eL hA'S hcorr hI
    rcases hDd (cH : G) hcB hND' with hF | ⟨h3, hT⟩
    · left
      exact fieldOn_to_Omega eL (hNS (Subgroup.mem_map_of_mem π hcH))
        (compIso_rel hp hKL π hN (hHnorm cH)) hF
    · right
      exact ⟨h3, (isTD4_congr h3 eL).1 hT⟩
  have hfin := hΩ hp hp2 (↥H ⧸ N0) S A bΩ hSn hqS hSp hChS hNS hAel hbA hRb hcentS hcardS hdich
  rcases hfin with ⟨hI, hcentΩ, hinnΩ⟩ | ⟨hp3, hU⟩
  · left
    have hne1 := glaPLayer_map_ne_bot_iff hp H.subtype hNH (K₀ ⊓ Subgroup.centralizer ({bH} : Set ↥H))
    rw [hYG] at hne1
    have hne2 := glaPLayer_map_ne_bot_iff hp π hN (K₀ ⊓ Subgroup.centralizer ({bH} : Set ↥H))
    rw [hYΩ] at hne2
    have hJne : JH ≠ ⊥ := hne2.1 hI
    have hcN : ∀ c : ↥H, c ∈ BH → c ∈ Subgroup.normalizer ((JH : Subgroup ↥H) : Set ↥H) := by
      intro c hc
      exact normalizes_glaPLayer (normalizes_inf_centralizer_singleton (hHnorm c) (hcomm c hc))
    have hBnorm : B ≤ Subgroup.normalizer ((Ipart p L b : Subgroup G) : Set G) := by
      intro c hc
      have hcH : (⟨c, hBH hc⟩ : ↥H) ∈ BH := Subgroup.mem_subgroupOf.2 hc
      have h := map_normalizer_mem H.subtype (hcN _ hcH)
      rw [hJG] at h
      exact h
    have hcentG : ∀ c ∈ B, CentMod p (Ipart p L b) c ↔
        c ∈ Subgroup.zpowers b ⊔ (B ⊓ centModSubgroup p L) := by
      intro c hc
      have hcH : (⟨c, hBH hc⟩ : ↥H) ∈ BH := Subgroup.mem_subgroupOf.2 hc
      set cH : ↥H := ⟨c, hBH hc⟩ with hcHdef
      have s1 : c ∈ centModSubgroup p (Ipart p L b) ↔ cH ∈ centModSubgroup p JH := by
        have h := mem_centModSubgroup_map_iff hp H.subtype hNH (hcN cH hcH)
        rw [hJG] at h
        exact h.symm
      have s2 : cH ∈ centModSubgroup p JH ↔ π cH ∈ centModSubgroup p (Ipart p S bΩ) := by
        have h := mem_centModSubgroup_map_iff hp π hN (hcN cH hcH)
        rw [hJΩ] at h
        exact h
      set T : Subgroup ↥H := Subgroup.zpowers bH ⊔ (BH ⊓ centModSubgroup p K₀) with hTdef
      have hTBH : T ≤ BH := sup_le (Subgroup.zpowers_le.2 hbHB) inf_le_left
      have hTΩ : T.map π = Subgroup.zpowers bΩ ⊔ (A ⊓ centModSubgroup p S) := by
        rw [hTdef, Subgroup.map_sup, MonoidHom.map_zpowers, map_inf_centModSubgroup hp π hN hBHN]
      have hTG : T.map H.subtype = Subgroup.zpowers b ⊔ (B ⊓ centModSubgroup p L) := by
        rw [hTdef, Subgroup.map_sup, MonoidHom.map_zpowers, map_centMod_subgroupOf hp hLH hBH hHN]
        rfl
      have key1 : π cH ∈ Subgroup.zpowers bΩ ⊔ (A ⊓ centModSubgroup p S) ↔ cH ∈ T := by
        rw [← hTΩ]
        exact mem_map_iff_of_injOn hp π hN hBHp hTBH hcH
      have key2 : cH ∈ T ↔ c ∈ Subgroup.zpowers b ⊔ (B ⊓ centModSubgroup p L) := by
        rw [← hTG]
        exact (Subgroup.mem_map_iff_mem H.subtype_injective).symm
      have s3 : CentMod p (Ipart p S bΩ) (π cH) ↔ π cH ∈ Subgroup.zpowers bΩ ⊔ (A ⊓ centModSubgroup p S) :=
        hcentΩ (π cH) (Subgroup.mem_map_of_mem π hcH)
      rw [centMod_iff, s1, s2, ← centMod_iff, s3, key1, key2]
    have hcorr : ∀ a ∈ B, ∃ a' ∈ A, ∀ x x',
        indRel p (Ipart p L b) a x x' ↔ indRel p (JH.map π) a' (compIso hp hJG π hN x) (compIso hp hJG π hN x') := by
      intro a ha
      have haH : (⟨a, hBH ha⟩ : ↥H) ∈ BH := Subgroup.mem_subgroupOf.2 ha
      refine ⟨π ⟨a, hBH ha⟩, Subgroup.mem_map_of_mem π haH, fun x x' => ?_⟩
      exact compIso_rel hp hJG π hN (hcN _ haH) x x'
    rw [← hJΩ] at hinnΩ
    refine ⟨?_, hcentG, ?_⟩
    · exact hne1.2 hJne
    · exact innDiagOn_of_Omega (compIso hp hJG π hN) hBnorm hcorr hinnΩ
  · right
    exact ⟨hp3, (psimple3_congr hp3 eL _).2 hU⟩

end Core

theorem i156At_of_facts {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hΩ : T156FactOmega p) : I156At G p := by
  intro B x L b hstar hC hD hb hR hcent hcard
  have hL : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L := hstar.1.1.1.2.2
  have hq := isQuasisimple_pQuot_of_glaPComponent hp hL
  have hHN : B ⊔ L ≤ Subgroup.normalizer (L : Set G) :=
    sup_le hstar.1.2.2 (fun l hl => Subgroup.le_normalizer hl)
  exact concl_of_H hp hp2 hΩ hq hstar.1.2.2 hstar.1.1.1.1.1 hb hC hD hR hcent hcard
    le_sup_right le_sup_left hHN

theorem i156At_of_facts' (hΩ : ∀ p : ℕ, T156FactOmega p) (G : Type) [Group G] [Finite G] (m : ℕ)
    (hctx : ThmACtx G m) (p : ℕ) (hp : p ∈ Mu G m) : I156At G p :=
  i156At_of_facts hp.1.1 hp.1.2.1 (hΩ p)

end CFSG.LocalAnalysis.GLTheoremA.T156

end
