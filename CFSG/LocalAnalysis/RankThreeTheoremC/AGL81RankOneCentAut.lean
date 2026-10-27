module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentStepFourTwo

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent

open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

section Aut

variable {K : Type} [Group K]

theorem conj_range_normal : (MulAut.conj : K →* MulAut K).range.Normal := by
  refine ⟨?_⟩
  rintro _ ⟨k, rfl⟩ σ
  exact ⟨σ k, mulAut_conj_apply_eq σ k⟩

theorem conj_injective_of_center (hZ : Subgroup.center K = ⊥) :
    Function.Injective (MulAut.conj : K →* MulAut K) :=
  RankOneSylow.conj_injective fun k hk => by
    have : k ∈ Subgroup.center K := Subgroup.mem_center_iff.mpr fun k' => (hk k').symm
    rw [hZ] at this
    exact Subgroup.mem_bot.mp this

theorem centralizer_conj_range_eq_bot (hZ : Subgroup.center K = ⊥) :
    Subgroup.centralizer ((MulAut.conj : K →* MulAut K).range : Set (MulAut K)) = ⊥ := by
  rw [eq_bot_iff]
  intro σ hσ
  rw [Subgroup.mem_bot]
  ext k
  have h := Subgroup.mem_centralizer_iff.mp hσ (MulAut.conj k) ⟨k, rfl⟩
  have h2 : MulAut.conj (σ k) = MulAut.conj k := by
    rw [mulAut_conj_apply_eq, ← h, mul_inv_cancel_right]
  simpa using conj_injective_of_center hZ h2

theorem stepThreeGroup_conj_range {p : ℕ} (hZ : Subgroup.center K = ⊥)
    (h : StepThreeGroup p K) : StepThreeGroup p ↥(MulAut.conj : K →* MulAut K).range := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  exact ⟨i, hi, ⟨(MonoidHom.ofInjective (conj_injective_of_center hZ)).symm.trans e⟩⟩

theorem isSylowOf_map_range {p : ℕ} [Fact p.Prime] [Finite K] {A : Type} [Group A] [Finite A]
    (f : K →* A) (hf : Function.Injective f) (T : Sylow p K) :
    CFSG.ABGLocalTools.IsSylowOf p ((T : Subgroup K).map f) f.range := by
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨Subgroup.map_le_range _ _, T.2.map f, ?_⟩
  rw [MonoidHom.range_eq_map, Subgroup.relIndex_map_map_of_injective _ _ hf,
    Subgroup.relIndex_top_right]
  exact T.not_dvd_index

end Aut

variable {G : Type} [Group G] [Finite G]

section Generic

variable {p : ℕ} [Fact p.Prime] {C : Subgroup G}
  {K : Subgroup (C ⧸ primeComplementCore (G := C) p)} [hK : K.Normal]

local notation "φ" => RankOneSylow.act (primeComplementCore (G := C) p) K

theorem map_comap_act_eq :
    (K.comap (QuotientGroup.mk' (primeComplementCore (G := C) p))).map φ =
      (MulAut.conj : ↥K →* MulAut ↥K).range := by
  ext σ
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨_, hx⟩, (RankOneSylow.act_eq_conj hx).symm⟩
  · rintro ⟨k, rfl⟩
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (primeComplementCore (G := C) p) (k : _)
    have hxK : x ∈ K.comap (QuotientGroup.mk' (primeComplementCore (G := C) p)) := by
      rw [Subgroup.mem_comap, hx]
      exact k.2
    refine ⟨x, hxK, ?_⟩
    rw [RankOneSylow.act_eq_conj hxK]
    congr 1
    exact Subtype.ext hx

theorem exists_sylow_act (hZ : Subgroup.center ↥K = ⊥) {B : Subgroup G}
    (hBC : CFSG.ABGLocalTools.IsSylowOf p B C) :
    ∃ T : Sylow p ↥K, ((B ⊓ hyp111Pre p C K).subgroupOf C).map φ =
      (T : Subgroup ↥K).map (MulAut.conj : ↥K →* MulAut ↥K) := by
  set O := primeComplementCore (G := C) p with hO
  set Kp := hyp111Pre p C K with hKp
  set B₁ := B ⊓ Kp with hB₁
  set Kc : Subgroup C := K.comap (QuotientGroup.mk' O) with hKc
  set ψ : ↥K →* MulAut ↥K := MulAut.conj with hψ
  have hψi : Function.Injective ψ := conj_injective_of_center hZ
  have hKpC : Kp ≤ C := Subgroup.map_subtype_le _
  have hKpc : Kp.subgroupOf C = Kc := Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
  set f : ↥Kc →* ↥K := (QuotientGroup.mk' O).subgroupComap K with hf
  have hfs : Function.Surjective f :=
    MonoidHom.subgroupComap_surjective _ _ (QuotientGroup.mk'_surjective O)
  have hφf : ∀ x : ↥Kc, φ (x : C) = ψ (f x) := fun x => by
    rw [RankOneSylow.act_eq_conj x.2]
    rfl
  have hB₁syl : CFSG.ABGLocalTools.IsSylowOf p B₁ Kp :=
    hBC.inf_of_le_normalizer hKpC (le_normalizer_hyp111Pre hK)
  have hB₁c : CFSG.ABGLocalTools.IsSylowOf p (B₁.subgroupOf C) Kc := by
    rw [← hKpc, ← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff C, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (inf_le_right.trans hKpC),
      inf_eq_left.mpr hKpC]
    exact hB₁syl
  obtain ⟨Q, hQ⟩ := hB₁c
  refine ⟨Q.mapSurjective hfs, ?_⟩
  rw [Sylow.coe_mapSurjective]
  ext h
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hu' := hu
    rw [← hQ] at hu'
    obtain ⟨x, hx, rfl⟩ := hu'
    exact ⟨f x, ⟨x, hx, rfl⟩, (hφf x).symm⟩
  · rintro ⟨k, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨(x : C), ?_, hφf x⟩
    rw [← hQ]
    exact ⟨x, hx, rfl⟩

theorem isSylowOf_act (hZ : Subgroup.center ↥K = ⊥) {B : Subgroup G}
    (hBC : CFSG.ABGLocalTools.IsSylowOf p B C) :
    CFSG.ABGLocalTools.IsSylowOf p (((B ⊓ hyp111Pre p C K).subgroupOf C).map φ)
      (MulAut.conj : ↥K →* MulAut ↥K).range := by
  obtain ⟨T, hT⟩ := exists_sylow_act hZ hBC
  rw [hT]
  exact isSylowOf_map_range _ (conj_injective_of_center hZ) T

end Generic

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent
