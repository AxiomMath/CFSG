module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenSL2Y
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenBorelCase
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenSylowTransfer
public import CFSG.LocalAnalysis.AGL81I.Section3.SL2AutOuter
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenNormalizer

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open Matrix
open scoped MatrixGroups
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

variable {H : Type} [Group H] [Finite H]

theorem borelSL_le_normalizer_unipSL {F : Type} [Field F] :
    CFSG.PSL2Table.borelSL F ≤
      Subgroup.normalizer (CFSG.PSL2Table.unipSL F : Set (SL(2, F))) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨h10, h00, h11⟩ := (CFSG.PSL2Table.mem_unipSL_iff x).mp hx
    let t : F := ((x : Matrix (Fin 2) (Fin 2) F)) 0 1
    have hxeq : x = CFSG.PSL2Table.unip t := by
      apply CFSG.PSL2Table.SL_ext <;> simp [t, h10, h00, h11]
    rw [hxeq, CFSG.PSL2Table.conj_unip_of_borel
      ((CFSG.PSL2Table.mem_borelSL_iff g).mp hg)]
    exact CFSG.PSL2Table.unip_mem_unipSL _
  · intro hx
    obtain ⟨h10, h00, h11⟩ := (CFSG.PSL2Table.mem_unipSL_iff _).mp hx
    let t : F := (((g * x * g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) 0 1
    have hxeq : g * x * g⁻¹ = CFSG.PSL2Table.unip t := by
      apply CFSG.PSL2Table.SL_ext <;> simp [t, h10, h00, h11]
    have hg' : g⁻¹ ∈ CFSG.PSL2Table.borelSL F := (CFSG.PSL2Table.borelSL F).inv_mem hg
    have hy : g⁻¹ * (g * x * g⁻¹) * g ∈ CFSG.PSL2Table.unipSL F := by
      rw [hxeq]
      have hconj : g⁻¹ * CFSG.PSL2Table.unip t * g =
          CFSG.PSL2Table.unip
            ((((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) 0 0 ^ 2 * t) := by
        simpa using CFSG.PSL2Table.conj_unip_of_borel
          ((CFSG.PSL2Table.mem_borelSL_iff g⁻¹).mp hg') t
      rw [hconj]
      exact CFSG.PSL2Table.unip_mem_unipSL _
    have he : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rwa [he] at hy

theorem normalizer_unipSL_eq_borelSL {F : Type} [Field F] [Finite F] :
    Subgroup.normalizer (CFSG.PSL2Table.unipSL F : Set (SL(2, F))) =
      CFSG.PSL2Table.borelSL F := by
  have hne : Subgroup.normalizer
      (CFSG.PSL2Table.unipSL F : Set (SL(2, F))) ≠ ⊤ := by
    intro htop
    have hmem : CFSG.PSL2Table.weyl (F := F) ∈
        Subgroup.normalizer (CFSG.PSL2Table.unipSL F : Set (SL(2, F))) := by
      rw [htop]
      exact Subgroup.mem_top _
    have hconj : CFSG.PSL2Table.weyl * CFSG.PSL2Table.unip (1 : F) *
        CFSG.PSL2Table.weyl⁻¹ ∈ CFSG.PSL2Table.unipSL F :=
      (Subgroup.mem_normalizer_iff.mp hmem _).mp (CFSG.PSL2Table.unip_mem_unipSL 1)
    have h10 := (CFSG.PSL2Table.mem_unipSL_iff _).mp hconj |>.1
    rw [CFSG.PSL2Table.conj_unip_apply_10, CFSG.PSL2Table.coe_weyl] at h10
    norm_num at h10
  rcases borelSL_overgroup_eq_borelSL_or_top (F := F)
      (borelSL_le_normalizer_unipSL (F := F)) with h | h
  · exact h
  · exact absurd h hne

theorem borel_le_normalizer_unipotent {F : Type} [Field F] :
    CFSG.PSL2Table.borel F ≤
      Subgroup.normalizer (CFSG.PSL2Table.unipotent F : Set (PSL(2, F))) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨t, rfl⟩ := (CFSG.PSL2Table.mem_unipotent_iff_exists x).mp hx
    obtain ⟨a, ha⟩ := CFSG.PSL2Table.borel_conj_unip hg t
    rw [ha]
    exact CFSG.PSL2Table.mk_unip_mem_unipotent _
  · intro hx
    obtain ⟨t, ht⟩ := (CFSG.PSL2Table.mem_unipotent_iff_exists _).mp hx
    have hg' : g⁻¹ ∈ CFSG.PSL2Table.borel F := (CFSG.PSL2Table.borel F).inv_mem hg
    obtain ⟨a, ha⟩ := CFSG.PSL2Table.borel_conj_unip hg' t
    have ha' : g⁻¹ * CFSG.PSL2Table.mk (CFSG.PSL2Table.unip t) * g =
        CFSG.PSL2Table.mk (CFSG.PSL2Table.unip ((a : F) ^ 2 * t)) := by
      simpa using ha
    have he : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rw [← he, ht, ha']
    exact CFSG.PSL2Table.mk_unip_mem_unipotent _

theorem normalizer_unipotent_eq_borel {F : Type} [Field F] [Finite F]
    (h2 : (2 : F) ≠ 0) :
    Subgroup.normalizer (CFSG.PSL2Table.unipotent F : Set (PSL(2, F))) =
      CFSG.PSL2Table.borel F := by
  have hne : Subgroup.normalizer
      (CFSG.PSL2Table.unipotent F : Set (PSL(2, F))) ≠ ⊤ := by
    intro htop
    have hmem : CFSG.PSL2Table.mk (CFSG.PSL2Table.weyl (F := F)) ∈
        Subgroup.normalizer (CFSG.PSL2Table.unipotent F : Set (PSL(2, F))) := by
      rw [htop]
      exact Subgroup.mem_top _
    have hx : CFSG.PSL2Table.mk (CFSG.PSL2Table.unip (1 : F)) ∈
        CFSG.PSL2Table.unipotent F := CFSG.PSL2Table.mk_unip_mem_unipotent _
    have hx1 : CFSG.PSL2Table.mk (CFSG.PSL2Table.unip (1 : F)) ≠ 1 := by
      intro h
      exact one_ne_zero ((CFSG.PSL2Table.mk_unip_eq_one_iff h2 1).mp h)
    have hconj : CFSG.PSL2Table.mk (CFSG.PSL2Table.weyl (F := F)) *
        CFSG.PSL2Table.mk (CFSG.PSL2Table.unip (1 : F)) *
        (CFSG.PSL2Table.mk (CFSG.PSL2Table.weyl (F := F)))⁻¹ ∈
        CFSG.PSL2Table.unipotent F :=
      (Subgroup.mem_normalizer_iff.mp hmem _).mp hx
    have hwb := (CFSG.PSL2Table.unipotent_conj_mem_iff h2 hx hx1
      (CFSG.PSL2Table.mk (CFSG.PSL2Table.weyl (F := F)))).mp hconj
    rw [CFSG.PSL2Table.mk_mem_borel_iff] at hwb
    exact weyl_not_mem_borelSL hwb
  rcases borel_overgroup_eq_borel_or_top (F := F)
      (borel_le_normalizer_unipotent (F := F)) with h | h
  · exact h
  · exact absurd h hne

theorem not_dvd_sq_sub_one {p : ℕ} (hp : p.Prime) : ¬ p ∣ p ^ 2 - 1 := by
  intro h
  have hsq : p ∣ p ^ 2 := by
    rw [pow_two]
    exact dvd_mul_right p p
  have hle : 1 ≤ p ^ 2 := by
    have := hp.two_le
    nlinarith
  have h1 : p ∣ 1 := by
    have hd := Nat.dvd_sub hsq h
    rwa [show p ^ 2 - (p ^ 2 - 1) = 1 by omega] at hd
  exact hp.not_dvd_one h1

theorem factorization_card_SL2_zmod (p : ℕ) [Fact p.Prime] :
    (Nat.card (SL(2, ZMod p))).factorization p = 1 := by
  have hp := Fact.out (p := p.Prime)
  have hcard : Nat.card (SL(2, ZMod p)) = p * (p ^ 2 - 1) := by
    rw [CFSG.PSL2Table.card_SL, ZMod.card]
  have hnonzero : p ^ 2 - 1 ≠ 0 := by
    have h1 : 1 < p ^ 2 := by
      have := hp.two_le
      nlinarith
    omega
  rw [hcard, Nat.factorization_mul hp.ne_zero hnonzero]
  change p.factorization p + (p ^ 2 - 1).factorization p = 1
  rw [hp.factorization_self, Nat.factorization_eq_zero_of_not_dvd (not_dvd_sq_sub_one hp),
    add_zero]

theorem factorization_card_PSL2_zmod (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    (Nat.card (PSL(2, ZMod p))).factorization p = 1 := by
  have hp := Fact.out (p := p.Prime)
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      ((ZMod.natCast_eq_zero_iff 2 p).mp h))
  have hcard : Nat.card (PSL(2, ZMod p)) * 2 = p * (p ^ 2 - 1) := by
    rw [CFSG.PSL2Table.card_PSL (F := ZMod p) h2, ZMod.card]
  have hnonzero : p ^ 2 - 1 ≠ 0 := by
    have h1 : 1 < p ^ 2 := by
      have := hp.two_le
      nlinarith
    omega
  have hfac : (Nat.card (PSL(2, ZMod p)) * 2).factorization p = 1 := by
    rw [hcard, Nat.factorization_mul hp.ne_zero hnonzero]
    change p.factorization p + (p ^ 2 - 1).factorization p = 1
    rw [hp.factorization_self, Nat.factorization_eq_zero_of_not_dvd (not_dvd_sq_sub_one hp),
      add_zero]
  have hfacL : (Nat.card (PSL(2, ZMod p)) * 2).factorization p =
      (Nat.card (PSL(2, ZMod p))).factorization p := by
    have h2fac : (2 : ℕ).factorization p = 0 := by
      rw [Nat.factorization_eq_zero_of_not_dvd]
      intro h2dvd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2dvd)
    rw [Nat.factorization_mul (Nat.card_pos.ne') (by norm_num)]
    change (Nat.card (PSL(2, ZMod p))).factorization p + (2 : ℕ).factorization p =
      (Nat.card (PSL(2, ZMod p))).factorization p
    rw [h2fac, add_zero]
  rw [hfacL] at hfac
  exact hfac

theorem card_unipSL_zmod (p : ℕ) [Fact p.Prime] :
    Nat.card (CFSG.PSL2Table.unipSL (ZMod p)) = p := by
  rw [CFSG.PSL2Table.card_unipSL, ZMod.card]

theorem card_unipotent_zmod (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    Nat.card (CFSG.PSL2Table.unipotent (ZMod p)) = p := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp
      ((ZMod.natCast_eq_zero_iff 2 p).mp h))
  rw [CFSG.PSL2Table.card_unipotent (F := ZMod p) h2, ZMod.card]

theorem exists_isSLType_borel_or_top {I D P Y : Subgroup H} {p d : ℕ} [Fact p.Prime]
    (hhyp : ThreeTenHyp I D P Y p d) (hcase : IsSLType 2 (ZMod p) ↥I) :
    Y ⊓ I = I ∨ ∃ e : ↥I ≃* SL(2, ZMod p),
      Y ⊓ I = ((CFSG.PSL2Table.borelSL (ZMod p)).map e.symm.toMonoidHom).map I.subtype := by
  obtain ⟨hp, hp2, hd, hd2, hdp, hI, hD, hDne, hP, hYlt, hγ, hN⟩ := hhyp
  obtain ⟨e0⟩ := hcase
  have hPI : P ≤ I := p_sylow_le_of_oPPrimeHull_eq hp hI hP
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf p P I := hP.of_le hPI le_top
  obtain ⟨S, hS⟩ := hPsyl.exists_sylow_eq_subgroupOf
  let SU : Sylow p (SL(2, ZMod p)) :=
    Sylow.ofCard (CFSG.PSL2Table.unipSL (ZMod p)) (by
      rw [card_unipSL_zmod, factorization_card_SL2_zmod, pow_one])
  have hSUcoe : (SU : Subgroup (SL(2, ZMod p))) =
      CFSG.PSL2Table.unipSL (ZMod p) := Sylow.coe_ofCard _ _
  let T : Sylow p (SL(2, ZMod p)) := S.mapSurjective (f := e0.toMonoidHom) e0.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SL(2, ZMod p)) SU T
  have hcoe : (T : Subgroup (SL(2, ZMod p))) =
      (CFSG.PSL2Table.unipSL (ZMod p)).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, hSUcoe, Subgroup.pointwise_smul_def]
    change Subgroup.map (MulAut.conj g).toMonoidHom
        (CFSG.PSL2Table.unipSL (ZMod p)) =
      Subgroup.map (MulAut.conj g).toMonoidHom (CFSG.PSL2Table.unipSL (ZMod p))
    rfl
  have hQcoe : (P.subgroupOf I).map e0.toMonoidHom =
      (T : Subgroup (SL(2, ZMod p))) := by
    rw [← hS, ← Sylow.coe_mapSurjective (f := e0.toMonoidHom) (hf := e0.surjective)]
  let e1 : ↥I ≃* SL(2, ZMod p) := e0.trans (MulAut.conj g⁻¹)
  have hQmap : (P.subgroupOf I).map e1.toMonoidHom =
      CFSG.PSL2Table.unipSL (ZMod p) := by
    calc (P.subgroupOf I).map e1.toMonoidHom
        = ((P.subgroupOf I).map e0.toMonoidHom).map
            (MulAut.conj g⁻¹).toMonoidHom := by
          dsimp only [e1]
          change Subgroup.map ((MulAut.conj g⁻¹).toMonoidHom.comp e0.toMonoidHom)
              (P.subgroupOf I) =
            Subgroup.map (MulAut.conj g⁻¹).toMonoidHom
              (Subgroup.map e0.toMonoidHom (P.subgroupOf I))
          rw [Subgroup.map_map]
      _ = ((CFSG.PSL2Table.unipSL (ZMod p)).map
            (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom := by
          rw [hQcoe, hcoe]
      _ = CFSG.PSL2Table.unipSL (ZMod p) := by
          rw [Subgroup.map_map]
          have hprod : MulAut.conj g⁻¹ * MulAut.conj g = 1 := by
            rw [← map_mul, inv_mul_cancel, map_one]
          have hone : (MulAut.conj g⁻¹).toMonoidHom.comp
              (MulAut.conj g).toMonoidHom = MonoidHom.id _ := by
            refine MonoidHom.ext fun x => ?_
            change (MulAut.conj g⁻¹ * MulAut.conj g) x = x
            rw [hprod]
            rfl
          rw [hone, Subgroup.map_id]
  have hNsub : Subgroup.normalizer ((P.subgroupOf I) : Set ↥I) ≤ (Y ⊓ I).subgroupOf I := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    have hxN : (x : H) ∈ Subgroup.normalizer (P : Set H) := by
      rw [← Subgroup.subgroupOf_normalizer_eq hPI] at hx
      exact hx
    exact ⟨hN ⟨hxN, x.2⟩, x.2⟩
  have hborel_le : CFSG.PSL2Table.borelSL (ZMod p) ≤
      ((Y ⊓ I).subgroupOf I).map e1.toMonoidHom := by
    calc CFSG.PSL2Table.borelSL (ZMod p)
        = Subgroup.normalizer
            (((P.subgroupOf I).map e1.toMonoidHom) : Set (SL(2, ZMod p))) := by
          rw [hQmap, normalizer_unipSL_eq_borelSL]
      _ = (Subgroup.normalizer ((P.subgroupOf I) : Set ↥I)).map e1.toMonoidHom := by
          rw [← Subgroup.map_equiv_normalizer_eq]
      _ ≤ ((Y ⊓ I).subgroupOf I).map e1.toMonoidHom := Subgroup.map_mono hNsub
  rcases borelSL_overgroup_eq_borelSL_or_top (F := ZMod p) hborel_le with h | h
  · refine Or.inr ⟨e1, ?_⟩
    have hsymm : (CFSG.PSL2Table.borelSL (ZMod p)).map e1.symm.toMonoidHom =
        (Y ⊓ I).subgroupOf I :=
      (Subgroup.map_symm_eq_iff_map_eq (H := CFSG.PSL2Table.borelSL (ZMod p))
        (K := (Y ⊓ I).subgroupOf I) (e := e1)).mpr h
    calc Y ⊓ I = ((Y ⊓ I).subgroupOf I).map I.subtype := by
          rw [Subgroup.map_subgroupOf_eq_of_le (inf_le_right : Y ⊓ I ≤ I)]
      _ = ((CFSG.PSL2Table.borelSL (ZMod p)).map e1.symm.toMonoidHom).map I.subtype := by
          rw [← hsymm]
  · left
    have hsymm : (⊤ : Subgroup (SL(2, ZMod p))).map e1.symm.toMonoidHom =
        (Y ⊓ I).subgroupOf I :=
      (Subgroup.map_symm_eq_iff_map_eq (H := (⊤ : Subgroup (SL(2, ZMod p))))
        (K := (Y ⊓ I).subgroupOf I) (e := e1)).mpr h
    have htop : (⊤ : Subgroup (SL(2, ZMod p))).map e1.symm.toMonoidHom = ⊤ :=
      Subgroup.map_top_of_surjective _ e1.symm.surjective
    have hTtop : (Y ⊓ I).subgroupOf I = ⊤ := by rw [← hsymm, htop]
    calc Y ⊓ I = ((Y ⊓ I).subgroupOf I).map I.subtype := by
          rw [Subgroup.map_subgroupOf_eq_of_le (inf_le_right : Y ⊓ I ≤ I)]
      _ = (⊤ : Subgroup ↥I).map I.subtype := by rw [hTtop]
      _ = I := by
          simpa using Subgroup.subgroupOf_map_subtype (⊤ : Subgroup H) I

theorem exists_isPSLType_borel_or_top {I D P Y : Subgroup H} {p d : ℕ} [Fact p.Prime]
    (hhyp : ThreeTenHyp I D P Y p d) (hcase : IsPSLType 2 (ZMod p) ↥I) :
    Y ⊓ I = I ∨ ∃ e : ↥I ≃* PSL(2, ZMod p),
      Y ⊓ I = ((CFSG.PSL2Table.borel (ZMod p)).map e.symm.toMonoidHom).map I.subtype := by
  obtain ⟨hp, hp2, hd, hd2, hdp, hI, hD, hDne, hP, hYlt, hγ, hN⟩ := hhyp
  obtain ⟨e0⟩ := hcase
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      ((ZMod.natCast_eq_zero_iff 2 p).mp h))
  have hPI : P ≤ I := p_sylow_le_of_oPPrimeHull_eq hp hI hP
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf p P I := hP.of_le hPI le_top
  obtain ⟨S, hS⟩ := hPsyl.exists_sylow_eq_subgroupOf
  let SU : Sylow p (PSL(2, ZMod p)) :=
    Sylow.ofCard (CFSG.PSL2Table.unipotent (ZMod p)) (by
      rw [card_unipotent_zmod p hp2, factorization_card_PSL2_zmod p hp2, pow_one])
  have hSUcoe : (SU : Subgroup (PSL(2, ZMod p))) =
      CFSG.PSL2Table.unipotent (ZMod p) := Sylow.coe_ofCard _ _
  let T : Sylow p (PSL(2, ZMod p)) := S.mapSurjective (f := e0.toMonoidHom) e0.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (PSL(2, ZMod p)) SU T
  have hcoe : (T : Subgroup (PSL(2, ZMod p))) =
      (CFSG.PSL2Table.unipotent (ZMod p)).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, hSUcoe, Subgroup.pointwise_smul_def]
    change Subgroup.map (MulAut.conj g).toMonoidHom
        (CFSG.PSL2Table.unipotent (ZMod p)) =
      Subgroup.map (MulAut.conj g).toMonoidHom (CFSG.PSL2Table.unipotent (ZMod p))
    rfl
  have hQcoe : (P.subgroupOf I).map e0.toMonoidHom =
      (T : Subgroup (PSL(2, ZMod p))) := by
    rw [← hS, ← Sylow.coe_mapSurjective (f := e0.toMonoidHom) (hf := e0.surjective)]
  let e1 : ↥I ≃* PSL(2, ZMod p) := e0.trans (MulAut.conj g⁻¹)
  have hQmap : (P.subgroupOf I).map e1.toMonoidHom =
      CFSG.PSL2Table.unipotent (ZMod p) := by
    calc (P.subgroupOf I).map e1.toMonoidHom
        = ((P.subgroupOf I).map e0.toMonoidHom).map
            (MulAut.conj g⁻¹).toMonoidHom := by
          dsimp only [e1]
          change Subgroup.map ((MulAut.conj g⁻¹).toMonoidHom.comp e0.toMonoidHom)
              (P.subgroupOf I) =
            Subgroup.map (MulAut.conj g⁻¹).toMonoidHom
              (Subgroup.map e0.toMonoidHom (P.subgroupOf I))
          rw [Subgroup.map_map]
      _ = ((CFSG.PSL2Table.unipotent (ZMod p)).map
            (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom := by
          rw [hQcoe, hcoe]
      _ = CFSG.PSL2Table.unipotent (ZMod p) := by
          rw [Subgroup.map_map]
          have hprod : MulAut.conj g⁻¹ * MulAut.conj g = 1 := by
            rw [← map_mul, inv_mul_cancel, map_one]
          have hone : (MulAut.conj g⁻¹).toMonoidHom.comp
              (MulAut.conj g).toMonoidHom = MonoidHom.id _ := by
            refine MonoidHom.ext fun x => ?_
            change (MulAut.conj g⁻¹ * MulAut.conj g) x = x
            rw [hprod]
            rfl
          rw [hone, Subgroup.map_id]
  have hNsub : Subgroup.normalizer ((P.subgroupOf I) : Set ↥I) ≤ (Y ⊓ I).subgroupOf I := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    have hxN : (x : H) ∈ Subgroup.normalizer (P : Set H) := by
      rw [← Subgroup.subgroupOf_normalizer_eq hPI] at hx
      exact hx
    exact ⟨hN ⟨hxN, x.2⟩, x.2⟩
  have hborel_le : CFSG.PSL2Table.borel (ZMod p) ≤
      ((Y ⊓ I).subgroupOf I).map e1.toMonoidHom := by
    calc CFSG.PSL2Table.borel (ZMod p)
        = Subgroup.normalizer
            (((P.subgroupOf I).map e1.toMonoidHom) : Set (PSL(2, ZMod p))) := by
          rw [hQmap, normalizer_unipotent_eq_borel h2]
      _ = (Subgroup.normalizer ((P.subgroupOf I) : Set ↥I)).map e1.toMonoidHom := by
          rw [← Subgroup.map_equiv_normalizer_eq]
      _ ≤ ((Y ⊓ I).subgroupOf I).map e1.toMonoidHom := Subgroup.map_mono hNsub
  rcases borel_overgroup_eq_borel_or_top (F := ZMod p) hborel_le with h | h
  · refine Or.inr ⟨e1, ?_⟩
    have hsymm : (CFSG.PSL2Table.borel (ZMod p)).map e1.symm.toMonoidHom =
        (Y ⊓ I).subgroupOf I :=
      (Subgroup.map_symm_eq_iff_map_eq (H := CFSG.PSL2Table.borel (ZMod p))
        (K := (Y ⊓ I).subgroupOf I) (e := e1)).mpr h
    calc Y ⊓ I = ((Y ⊓ I).subgroupOf I).map I.subtype := by
          rw [Subgroup.map_subgroupOf_eq_of_le (inf_le_right : Y ⊓ I ≤ I)]
      _ = ((CFSG.PSL2Table.borel (ZMod p)).map e1.symm.toMonoidHom).map I.subtype := by
          rw [← hsymm]
  · left
    have hsymm : (⊤ : Subgroup (PSL(2, ZMod p))).map e1.symm.toMonoidHom =
        (Y ⊓ I).subgroupOf I :=
      (Subgroup.map_symm_eq_iff_map_eq (H := (⊤ : Subgroup (PSL(2, ZMod p))))
        (K := (Y ⊓ I).subgroupOf I) (e := e1)).mpr h
    have htop : (⊤ : Subgroup (PSL(2, ZMod p))).map e1.symm.toMonoidHom = ⊤ :=
      Subgroup.map_top_of_surjective _ e1.symm.surjective
    have hTtop : (Y ⊓ I).subgroupOf I = ⊤ := by rw [← hsymm, htop]
    calc Y ⊓ I = ((Y ⊓ I).subgroupOf I).map I.subtype := by
          rw [Subgroup.map_subgroupOf_eq_of_le (inf_le_right : Y ⊓ I ≤ I)]
      _ = (⊤ : Subgroup ↥I).map I.subtype := by rw [hTtop]
      _ = I := by
          simpa using Subgroup.subgroupOf_map_subtype (⊤ : Subgroup H) I

@[expose] def MulAutTrivialOfCoprimeOrder (X : Type) [Group X] (d : ℕ) : Prop :=
  ¬ d ∣ Nat.card X → ∀ δ : MulAut X, orderOf δ = d → δ = 1

theorem i_le_Y_of_borel {I D P Y : Subgroup H} {p d : ℕ}
    (hhyp : ThreeTenHyp I D P Y p d) (hAut : MulAutTrivialOfCoprimeOrder ↥I d)
    (B : Subgroup H) (hBle : B ≤ Y ⊓ I)
    (hBmax : ∀ C, B ≤ C → C ≤ Y ⊓ I → C = B ∨ C = I) (hBcase : Y ⊓ I = B)
    (hDbot : D ⊓ I = ⊥) (hSyl : CFSG.ABGLocalTools.IsSylowOf d (D ⊓ I) I) : I ≤ Y := by
  have hbase : ThreeTenHyp I D P Y p d := hhyp
  obtain ⟨hp, hp2, hd, hd2, hdp, hI, hD, hDne, hP, hYlt, hγ, hN⟩ := hhyp
  haveI : Fact d.Prime := ⟨hd⟩
  by_cases hdvd : d ∣ Nat.card ↥I
  · have hfacpos : 0 < (Nat.card ↥I).factorization d :=
      hd.factorization_pos_of_dvd Nat.card_pos.ne' hdvd
    have hcard : Nat.card ↥(D ⊓ I) = d ^ (Nat.card ↥I).factorization d := hSyl.card_eq
    have hdvd' : d ∣ Nat.card ↥(D ⊓ I) := by
      rw [hcard]
      exact dvd_pow_self d (by omega)
    have hcardbot : Nat.card ↥(D ⊓ I) = 1 := by rw [hDbot]; simp
    rw [hcardbot] at hdvd'
    exact absurd hdvd' hd.not_dvd_one
  · have hInormal : I.Normal := normal_of_oPPrimeHull_eq hI
    haveI : I.Normal := hInormal
    have htriv : ∀ x ∈ D, MulAut.conjNormal (G := H) (H := I) x = 1 := by
      intro x hx
      by_contra hx1
      let φ : H →* MulAut ↥I := MulAut.conjNormal (G := H) (H := I)
      let M : Subgroup (MulAut ↥I) := D.map φ
      have hMpg : IsPGroup d M := hD.isPGroup.map φ
      have hMne : M ≠ ⊥ := by
        intro hbot
        have hmem : φ x ∈ M := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
        rw [hbot] at hmem
        exact hx1 (Subgroup.mem_bot.mp hmem)
      have hdvdM : d ∣ Nat.card M := by
        rcases hMpg.card_eq_or_dvd with h1 | h1
        · exact absurd (Subgroup.card_eq_one.mp h1) hMne
        · exact h1
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' d hdvdM
      obtain ⟨z, hzD, hzy⟩ := Subgroup.mem_map.mp y.2
      have hzord : orderOf (φ z) = d := by
        rw [hzy, Subgroup.orderOf_coe, hy]
      have hz1 : φ z = 1 := hAut hdvd (φ z) hzord
      rw [hz1] at hzord
      have hd1 : d = 1 := by simpa using hzord.symm
      exact hd.ne_one hd1
    have hcent : D ≤ Subgroup.centralizer (I : Set H) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hx1 : MulAut.conjNormal (G := H) (H := I) x = 1 := htriv x hx
      have hconj : MulAut.conjNormal (G := H) (H := I) x ⟨y, hy⟩ = ⟨y, hy⟩ := by
        rw [hx1]
        rfl
      have hxy : x * y * x⁻¹ = y := by
        have h := congrArg Subtype.val hconj
        simpa [MulAut.conjNormal_apply] using h
      have hxy' : x * y = y * x := by
        calc x * y = x * y * x⁻¹ * x := by group
          _ = y * x := by rw [hxy]
      exact hxy'.symm
    have hIcent : I ≤ Subgroup.centralizer (D : Set H) := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (Subgroup.mem_centralizer_iff.mp (hcent hx) y hy).symm
    have hIleN : I ≤ Subgroup.normalizer (D : Set H) :=
      hIcent.trans (Subgroup.centralizer_le_normalizer (D : Set H))
    have hsup_le_N : I ⊔ D ≤ Subgroup.normalizer (D : Set H) :=
      sup_le hIleN (Subgroup.le_normalizer)
    have hsupY : I ⊔ D ≤ Y := by
      intro z hz
      exact normalizer_D_inter_le_Y hbase ⟨hsup_le_N hz, hz⟩
    exact absurd hsupY (not_le_of_gt hYlt)

theorem i_le_Y_of_threeTenHyp_of_isSLType {I D P Y : Subgroup H} {p d : ℕ}
    (hhyp : ThreeTenHyp I D P Y p d) (hcase : IsSLType 2 (ZMod p) ↥I) : I ≤ Y := by
  have hbase : ThreeTenHyp I D P Y p d := hhyp
  obtain ⟨hp, hp2, hd, hd2, hdp, hI, hD, hDne, hP, hYlt, hγ, hN⟩ := hhyp
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact d.Prime := ⟨hd⟩
  rcases exists_isSLType_borel_or_top hbase hcase with htop | ⟨e, hB⟩
  · exact inf_eq_right.mp htop
  · have hbot : D ⊓ I = ⊥ :=
      D_inf_I_eq_bot_of_isSLType (B := Y ⊓ I) hbase e rfl hB
    have hInormal : I.Normal := normal_of_oPPrimeHull_eq hI
    haveI : I.Normal := hInormal
    have hSyl : CFSG.ABGLocalTools.IsSylowOf d (D ⊓ I) I :=
      isSylowOf_inf_of_normal (p := d) hInormal hD
    have hAut : MulAutTrivialOfCoprimeOrder ↥I d := by
      intro hnd δ hδ
      exact mulAut_eq_one_of_not_dvd_card hp hd hd2 hnd hcase δ hδ
    exact i_le_Y_of_borel hbase hAut (Y ⊓ I) le_rfl
      (fun C hBC hCY => Or.inl (le_antisymm (by simpa using hCY) hBC)) rfl hbot hSyl

theorem card_outer_PSL2_dvd_two (p : ℕ) [Fact p.Prime] :
    Nat.card (Outer (PSL(2, ZMod p))) ∣ 2 := by
  have hp := Fact.out (p := p.Prime)
  have hcard : Nat.card (ZMod p) = p ^ 1 := by rw [Nat.card_zmod, pow_one]
  have h := (CFSG.LocalAnalysis.ComponentInitial.linear_two_outer_order_divisor
    (p := p) (f := 1) hp (ZMod p) hcard).1
  have h' : Nat.card (Outer (PSL(2, ZMod p))) ∣ Nat.gcd 2 (p ^ 1 - 1) := by
    simpa using h
  exact h'.trans (by simpa using Nat.gcd_dvd_left 2 (p - 1))

theorem mulAut_eq_one_of_not_dvd_card_isPSLType {I : Type} [Group I] [Finite I] {p d : ℕ}
    (hp : p.Prime) (hd : d.Prime) (hd2 : d ≠ 2) (hnd : ¬ d ∣ Nat.card I)
    (hI : IsPSLType 2 (ZMod p) I) (δ : MulAut I) (hδ : orderOf δ = d) : δ = 1 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := hI
  have houtI : Nat.card (Outer I) ∣ 2 := by
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
    exact card_outer_PSL2_dvd_two p
  let q : Outer I := QuotientGroup.mk' (inner I) δ
  have hqd : orderOf q ∣ d := by
    rw [← hδ]
    exact orderOf_map_dvd (QuotientGroup.mk' (inner I)) δ
  have hq2 : orderOf q ∣ 2 := (orderOf_dvd_natCard q).trans houtI
  have hq1 : orderOf q = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hq2 with h1 | h2
    · exact h1
    · exfalso
      have h2d : 2 ∣ d := by rw [h2] at hqd; exact hqd
      have h2eq : 2 = d := ((Nat.dvd_prime hd).mp h2d).resolve_left (by norm_num)
      exact hd2 h2eq.symm
  have hqeq : q = 1 := orderOf_eq_one_iff.mp hq1
  have hδinner : δ ∈ inner I := (QuotientGroup.eq_one_iff δ).mp hqeq
  obtain ⟨g, hg⟩ := hδinner
  have hdvdI : d ∣ Nat.card I := by
    calc d = orderOf (MulAut.conj g) := by rw [hg, hδ]
      _ ∣ orderOf g := orderOf_map_dvd (MulAut.conj : I →* MulAut I) g
      _ ∣ Nat.card I := orderOf_dvd_natCard g
  exact (hnd hdvdI).elim

theorem i_le_Y_of_threeTenHyp_of_isPSLType {I D P Y : Subgroup H} {p d : ℕ}
    (hhyp : ThreeTenHyp I D P Y p d) (hcase : IsPSLType 2 (ZMod p) ↥I) : I ≤ Y := by
  have hbase : ThreeTenHyp I D P Y p d := hhyp
  obtain ⟨hp, hp2, hd, hd2, hdp, hI, hD, hDne, hP, hYlt, hγ, hN⟩ := hhyp
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact d.Prime := ⟨hd⟩
  rcases exists_isPSLType_borel_or_top hbase hcase with htop | ⟨e, hB⟩
  · exact inf_eq_right.mp htop
  · have hbot : D ⊓ I = ⊥ :=
      D_inf_I_eq_bot_of_isPSLType (B := Y ⊓ I) hbase e rfl hB
    have hInormal : I.Normal := normal_of_oPPrimeHull_eq hI
    haveI : I.Normal := hInormal
    have hSyl : CFSG.ABGLocalTools.IsSylowOf d (D ⊓ I) I :=
      isSylowOf_inf_of_normal (p := d) hInormal hD
    have hAut : MulAutTrivialOfCoprimeOrder ↥I d := by
      intro hnd δ hδ
      exact mulAut_eq_one_of_not_dvd_card_isPSLType hp hd hd2 hnd hcase δ hδ
    exact i_le_Y_of_borel hbase hAut (Y ⊓ I) le_rfl
      (fun C hBC hCY => Or.inl (le_antisymm (by simpa using hCY) hBC)) rfl hbot hSyl

theorem threeTenSL2Vacuity_holds : ThreeTenSL2Vacuity := by
  refine threeTenSL2Vacuity_of_I_le_Y ?_
  intro H _ _ I D P Y p d hhyp htype
  rcases htype with h | h
  · exact i_le_Y_of_threeTenHyp_of_isSLType hhyp h
  · exact i_le_Y_of_threeTenHyp_of_isPSLType hhyp h

end CFSG.LocalAnalysis.AGL81I.Section3
