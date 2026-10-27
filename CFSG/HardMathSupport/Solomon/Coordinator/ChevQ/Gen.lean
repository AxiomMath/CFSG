module

public import CFSG.HardMathSupport.Dickson.I271.Glue
public import CFSG.LocalAnalysis.AGLEmbeddingD2.LieCross
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Models
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Indices
public import CFSG.HardMathSupport.Solomon.Coordinator.I27_1Fam
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.Seitz.Defs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Dickson.I271 CFSG.HardMathSupport.Timmesfeld.ComponentBalance
  CFSG.LieType.Seitz CFSG.AGLEmbeddingD2

section Image

variable {X : Type} [Group X] [Finite X]

theorem card_autImage {B K : Subgroup X} (hperf : commutator ↥K = ⊤) :
    Nat.card (autImage B K) = autOrderIn B K := by
  unfold autImage actHom
  rw [← Subgroup.relIndex_ker, ker_i271Act hperf (MulEquiv.refl (↥K ⧸ Subgroup.center ↥K)),
    Subgroup.relIndex_subgroupOf (inf_le_right : B ⊓ Subgroup.normalizer (K : Set X) ≤
      Subgroup.normalizer (K : Set X))]
  rfl

theorem isElemAbelian_autImage {p : ℕ} {B K : Subgroup X} (hB : IsElemAbelian p B) :
    IsElemAbelian p (autImage B K) := by
  have hNbel : IsElemAbelian p (B ⊓ Subgroup.normalizer (K : Set X)) :=
    i271_isElemAbelian_of_le hB inf_le_left
  exact CFSG.SectionRank.isElemAbelian_map
    (i271_isElemAbelian_subgroupOf (Subgroup.normalizer (K : Set X)) hNbel) (actHom K)

theorem exists_sub_autImage {p k : ℕ} (hp : p.Prime) {B K : Subgroup X}
    (hB : IsElemAbelian p B) (hperf : commutator ↥K = ⊤) (hk : p ^ k ∣ autOrderIn B K) :
    ∃ E : Subgroup (MulAut (↥K ⧸ Subgroup.center ↥K)), E ≤ autImage B K ∧ IsElemAbelian p E ∧
      Nat.card E = p ^ k := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨D, hD⟩ := Sylow.exists_subgroup_card_pow_prime p
    (show p ^ k ∣ Nat.card ↥(autImage B K) by rw [card_autImage hperf]; exact hk)
  refine ⟨D.map (autImage B K).subtype, Subgroup.map_subtype_le D,
    i271_isElemAbelian_of_le (isElemAbelian_autImage hB) (Subgroup.map_subtype_le D), ?_⟩
  rw [Subgroup.card_map_of_injective (autImage B K).subtype_injective]
  exact hD

theorem card_eq_autOrderIn_mul {B K : Subgroup X} (hBN : B ≤ Subgroup.normalizer (K : Set X)) :
    Nat.card B = autOrderIn B K * Nat.card (B ⊓ Subgroup.centralizer (K : Set X) : Subgroup X) := by
  have h := Subgroup.relIndex_mul_card (H := Subgroup.centralizer (K : Set X)) (K := B)
  rw [inf_comm, ← i271h_autOrderIn_eq_relIndex hBN] at h
  exact h.symm

theorem pRank_eq_add_autOrderIn {p r : ℕ} (hp : p.Prime) {B K : Subgroup X}
    (hBel : IsElemAbelian p B) (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hr : autOrderIn B K = p ^ r) :
    CFSG.Open.pRank p B = CFSG.Open.pRank p (B ⊓ Subgroup.centralizer (K : Set X)) + r := by
  have hCel : IsElemAbelian p (B ⊓ Subgroup.centralizer (K : Set X)) :=
    i271_isElemAbelian_of_le hBel inf_le_left
  obtain ⟨m, hm⟩ := i271_exists_card_eq hp hBel
  obtain ⟨c, hc⟩ := i271_exists_card_eq hp hCel
  have h := card_eq_autOrderIn_mul hBN
  rw [hm, hr, hc, ← pow_add] at h
  have := Nat.pow_right_injective hp.two_le h
  rw [i271_pRank_eq hp hBel hm, i271_pRank_eq hp hCel hc]
  omega

theorem autImage_le_range_conj {B K : Subgroup X} (h : InducesInnerIn B K) :
    autImage B K ≤ (MulAut.conj : (↥K ⧸ Subgroup.center ↥K) →* MulAut (↥K ⧸ Subgroup.center ↥K)).range := by
  intro e he
  obtain ⟨b, hbN, hbB, rfl⟩ := mem_autImage.1 he
  obtain ⟨k, hk, hkc⟩ := h b ⟨hbB, hbN⟩
  refine ⟨QuotientGroup.mk ⟨k, hk⟩, ?_⟩
  ext s
  induction s using QuotientGroup.induction_on with
  | H x =>
    rw [actHom_mk]
    show (QuotientGroup.mk (⟨k, hk⟩ * x * ⟨k, hk⟩⁻¹ : ↥K) : ↥K ⧸ Subgroup.center ↥K) = _
    congr 1
    apply Subtype.ext
    have h1 : (x : X) * ((k : X)⁻¹ * b) = ((k : X)⁻¹ * b) * x :=
      Subgroup.mem_centralizer_iff.1 hkc x x.2
    show (k : X) * x * (k : X)⁻¹ = b * (x : X) * b⁻¹
    calc (k : X) * x * (k : X)⁻¹
        = (k : X) * ((x : X) * ((k : X)⁻¹ * b)) * ((k : X)⁻¹ * b)⁻¹ * (k : X)⁻¹ := by group
      _ = (k : X) * (((k : X)⁻¹ * b) * x) * ((k : X)⁻¹ * b)⁻¹ * (k : X)⁻¹ := by rw [h1]
      _ = b * (x : X) * b⁻¹ := by group

end Image

section Seitz

theorem closure_eq_seitzHyperGamma {S : Type*} [Group S] (p : ℕ) (E : Subgroup (MulAut S)) :
    Subgroup.closure {s : S | ∃ F ≤ E, F.relIndex E = p ∧ ∀ f ∈ F, f s = s} =
      seitzHyperGamma p E := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    rintro s ⟨F, hFE, hrel, hs⟩
    exact (le_iSup₂_of_le (f := fun (F : Subgroup (MulAut S)) (_ : F ≤ E ∧ F.relIndex E = p) =>
      fixedPoints F) F ⟨hFE, hrel⟩ le_rfl) (mem_fixedPoints.2 hs)
  · refine iSup₂_le fun F hF s hs => ?_
    exact Subgroup.subset_closure ⟨F, hF.1, hF.2, mem_fixedPoints.1 hs⟩

theorem planeGen_of_kfact (hS : KFactSeitzRankTwo) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {S : Type} [Group S] (d : TauCeti.ValidLieTypeIndex)
    (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) (hdp : p ≠ d.1.characteristic)
    (hex : ¬ IsD2SeitzException p d.1) {E : Subgroup (MulAut S)} (hE : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ 2) :
    Subgroup.closure {s : S | ∃ f ∈ E, f ≠ 1 ∧ f s = s} = ⊤ := by
  let φ : MulAut S ≃* MulAut (TauCeti.CFSGIndex.lie d).Group := MulAut.congr e
  have hE' : IsElemAbelian p (E.map φ.toMonoidHom) :=
    CFSG.SectionRank.isElemAbelian_map hE φ.toMonoidHom
  have hcard' : Nat.card (E.map φ.toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective φ.injective]
    exact hcard
  have h := hS d p hp hp2 hdp hex (E.map φ.toMonoidHom) hE' hcard'
  have himg : e '' {s : S | ∃ f ∈ E, f ≠ 1 ∧ f s = s} =
      {k : (TauCeti.CFSGIndex.lie d).Group | ∃ f ∈ E.map φ.toMonoidHom, f ≠ 1 ∧ f k = k} := by
    ext k
    constructor
    · rintro ⟨s, ⟨f, hf, hf1, hfs⟩, rfl⟩
      refine ⟨φ f, ⟨f, hf, rfl⟩, fun h1 => hf1 (φ.injective (by rw [h1, map_one])), ?_⟩
      show e (f (e.symm (e s))) = e s
      rw [e.symm_apply_apply, hfs]
    · rintro ⟨_, ⟨f, hf, rfl⟩, hf1, hk⟩
      refine ⟨e.symm k, ⟨f, hf, fun h1 => hf1 (by rw [show φ.toMonoidHom f = φ f from rfl, h1,
        map_one]), ?_⟩, e.apply_symm_apply k⟩
      have : e (f (e.symm k)) = k := hk
      apply e.injective
      rw [this, e.apply_symm_apply]
  have hmap : (Subgroup.closure {s : S | ∃ f ∈ E, f ≠ 1 ∧ f s = s}).map e.toMonoidHom = ⊤ := by
    rw [MonoidHom.map_closure]
    show Subgroup.closure (e '' {s : S | ∃ f ∈ E, f ≠ 1 ∧ f s = s}) = ⊤
    rw [himg]
    exact h
  have : (Subgroup.closure {s : S | ∃ f ∈ E, f ≠ 1 ∧ f s = s}).map e.toMonoidHom =
      (⊤ : Subgroup S).map e.toMonoidHom := by
    rw [hmap, Subgroup.map_top, MonoidHom.range_eq_top_of_surjective _ e.surjective]
  exact Subgroup.map_injective e.injective this

theorem isLThreeFour_of_index {S : Type} [Group S] (d : TauCeti.ValidLieTypeIndex)
    (q : TauCeti.PrimePower) (hd : d.1 = .A 2 q) (hq : IsTwoPow q 2)
    (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) : IsLThreeFour S := by
  obtain ⟨d, hv⟩ := d
  simp only at hd
  subst hd
  have hm := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.lieModel_typeA 2 q hv
  rcases hm.2 with hcm | ⟨hn, -⟩
  · obtain ⟨-, F, hF, hFin, hcard, ⟨f⟩⟩ := hcm
    refine ⟨F, hF, hFin, ?_, ⟨e.trans f⟩⟩
    rw [hcard, hq.1, hq.2]
    norm_num
  · omega

end Seitz

section Apply

variable {X : Type} [Group X] [Finite X]

theorem caseA_of_plane (hS : KFactSeitzRankTwo) {p : ℕ} {K B : Subgroup X} (hH : I271Hyp p K B)
    (hNorm : I271Norm p K B) (hc : 2 ≤ CFSG.Open.pRank p (B ⊓ Subgroup.centralizer (K : Set X)))
    (hZ : CFSG.Open.pRank p (Subgroup.center ↥K) ≤ 1) (d : TauCeti.ValidLieTypeIndex)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hdp : p ≠ d.1.characteristic) (hex : ¬ IsD2SeitzException p d.1) : I271CaseA p K B := by
  have hperf : commutator ↥K = ⊤ := (i116e_isQuasisimple hH.core hH.comp).1
  have hBel : IsElemAbelian p B := hH.scp.2.1
  obtain ⟨r, hr⟩ := exists_pow_autOrderIn hH.prime hBel hNorm.1
  have hr2 : 2 ≤ r := (Nat.pow_le_pow_iff_right hH.prime.one_lt).1 (hr ▸ hNorm.2)
  obtain ⟨E, hEA, hEel, hEcard⟩ := exists_sub_autImage (k := 2) hH.prime hBel hperf
    (hr ▸ pow_dvd_pow p hr2)
  exact caseA_of_planeGen hH hNorm.1 hc hZ E hEA hEel hEcard
    (planeGen_of_kfact hS hH.prime hH.odd d e hdp hex hEel hEcard)

theorem caseA_of_cube {p : ℕ} {K B : Subgroup X} (hH : I271Hyp p K B)
    (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hc : CFSG.Open.pRank p (B ⊓ Subgroup.centralizer (K : Set X)) = 1)
    (hZ : CFSG.Open.pRank p (Subgroup.center ↥K) ≤ 1)
    (hgen : ∀ E : Subgroup (MulAut (↥K ⧸ Subgroup.center ↥K)), E ≤ autImage B K →
      IsElemAbelian p E → Nat.card E = p ^ 3 → seitzHyperGamma p E = ⊤) :
    I271CaseA p K B := by
  have hperf : commutator ↥K = ⊤ := (i116e_isQuasisimple hH.core hH.comp).1
  have hBel : IsElemAbelian p B := hH.scp.2.1
  obtain ⟨r, hr⟩ := exists_pow_autOrderIn hH.prime hBel hBN
  have hm := pRank_eq_add_autOrderIn hH.prime hBel hBN hr
  have h4 := hH.rank_four
  have hr3 : 3 ≤ r := by omega
  obtain ⟨E, hEA, hEel, hEcard⟩ := exists_sub_autImage (k := 3) hH.prime hBel hperf
    (hr ▸ pow_dvd_pow p hr3)
  exact caseA_of_hyperGen3 hH hBN hZ E hEA hEcard
    (by rw [closure_eq_seitzHyperGamma]; exact hgen E hEA hEel hEcard)

end Apply

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
