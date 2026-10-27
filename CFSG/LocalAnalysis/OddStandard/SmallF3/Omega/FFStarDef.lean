module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFMonoE16
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFSimCard
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OmegaProj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Basic
public import Certificates.Data.ExceptionalSL3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {c : ZMod 3}

@[expose] noncomputable def ffStar (hQ : Q.Nondegenerate) (S : Subgroup (OGroup Q)) :
    Subgroup ↥(omegaProj hQ) :=
  (S.subgroupOf (omegaGroup hQ)).map (omegaToProj hQ)

@[expose] noncomputable def ffLift (hQ : Q.Nondegenerate) (U : Subgroup ↥(omegaProj hQ)) :
    Subgroup (OGroup Q) :=
  (U.comap (omegaToProj hQ)).map (omegaGroup hQ).subtype

private lemma card_comap_eq_card_ker_mul_card_of_le_range {G G' : Type*} [Group G] [Group G']
    (f : G →* G') {H : Subgroup G'} (hH : H ≤ f.range) :
    Nat.card (H.comap f) = Nat.card f.ker * Nat.card H := by
  let g : H.comap f →* G' := f.comp (H.comap f).subtype
  have hrange : g.range = H := by
    ext y
    simp only [MonoidHom.mem_range, g, MonoidHom.comp_apply, Subgroup.coe_subtype]
    constructor
    · rintro ⟨x, rfl⟩
      exact x.2
    · intro hy
      obtain ⟨k, hk⟩ := hH hy
      exact ⟨⟨k, by show f k ∈ H; rw [hk]; exact hy⟩, hk⟩
  have hker : Nat.card g.ker = Nat.card f.ker := by
    refine Nat.card_congr ⟨fun x => ⟨x.1.1, x.2⟩, fun x => ⟨⟨x.1, ?_⟩, x.2⟩,
      fun x => rfl, fun x => rfl⟩
    rw [Subgroup.mem_comap, x.2]
    exact H.one_mem
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv, hrange, hker] at h
  exact h.trans (Nat.mul_comm _ _)

theorem mem_ffStar_iff (hQ : Q.Nondegenerate) {S : Subgroup (OGroup Q)} {w : ↥(omegaProj hQ)} :
    w ∈ ffStar hQ S ↔ ∃ g : ↥(omegaGroup hQ), (g : OGroup Q) ∈ S ∧ omegaToProj hQ g = w := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg, rfl⟩

theorem mem_ffLift_iff (hQ : Q.Nondegenerate) {U : Subgroup ↥(omegaProj hQ)} {g : OGroup Q} :
    g ∈ ffLift hQ U ↔ ∃ h : g ∈ omegaGroup hQ, omegaToProj hQ ⟨g, h⟩ ∈ U := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.2, ha⟩
  · rintro ⟨h, hh⟩
    exact ⟨⟨g, h⟩, hh, rfl⟩

theorem ffLift_le_omega (hQ : Q.Nondegenerate) (U : Subgroup ↥(omegaProj hQ)) :
    ffLift hQ U ≤ omegaGroup hQ := by
  rintro g ⟨a, -, rfl⟩
  exact a.2

theorem ffStar_ffLift (hQ : Q.Nondegenerate) (U : Subgroup ↥(omegaProj hQ)) :
    ffStar hQ (ffLift hQ U) = U := by
  apply le_antisymm
  · intro w hw
    rw [mem_ffStar_iff] at hw
    obtain ⟨g, hg, rfl⟩ := hw
    rw [mem_ffLift_iff] at hg
    obtain ⟨h, hh⟩ := hg
    have hgg : (⟨(g : OGroup Q), h⟩ : ↥(omegaGroup hQ)) = g := Subtype.ext rfl
    rwa [hgg] at hh
  · intro w hw
    rw [mem_ffStar_iff]
    obtain ⟨g, hg⟩ := omegaToProj_surjective hQ w
    refine ⟨g, ?_, hg⟩
    rw [mem_ffLift_iff]
    exact ⟨g.2, by rw [hg]; exact hw⟩

theorem ffLift_injective (hQ : Q.Nondegenerate) : Function.Injective (ffLift hQ) := by
  intro U₁ U₂ h
  rw [← ffStar_ffLift hQ U₁, ← ffStar_ffLift hQ U₂, h]

theorem ffLift_ffStar (hQ : Q.Nondegenerate) {S : Subgroup (OGroup Q)} (hS : S ≤ omegaGroup hQ)
    (hπ : piOrth Q ∈ S) : ffLift hQ (ffStar hQ S) = S := by
  apply le_antisymm
  · intro g hg
    rw [mem_ffLift_iff] at hg
    obtain ⟨hmem, hU⟩ := hg
    rw [mem_ffStar_iff] at hU
    obtain ⟨s, hs, hse⟩ := hU
    rcases omegaToProj_eq_iff hQ hse.symm with h | h
    · have hg' : g = (s : OGroup Q) := h.symm
      rw [hg']
      exact hs
    · have hgs : (s : OGroup Q) = piOrth Q * g := h
      have hg' : g = piOrth Q * (s : OGroup Q) := by
        rw [hgs, ← mul_assoc, piOrth_mul_self, one_mul]
      rw [hg']
      exact S.mul_mem hπ hs
  · intro g hg
    rw [mem_ffLift_iff]
    refine ⟨hS hg, ?_⟩
    rw [mem_ffStar_iff]
    exact ⟨⟨g, hS hg⟩, hg, rfl⟩

theorem ffLift_card (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (U : Subgroup ↥(omegaProj hQ)) :
    Nat.card ↥(ffLift hQ U) = 2 * Nat.card ↥U := by
  have hle : U ≤ (omegaToProj hQ).range := by
    rw [MonoidHom.range_eq_top_of_surjective (omegaToProj hQ) (omegaToProj_surjective hQ)]
    exact le_top
  have hker : Nat.card (omegaToProj hQ).ker = 2 := by
    have h1 := Subgroup.card_ker_mul_card_of_surjective (f := omegaToProj hQ)
      (omegaToProj_surjective hQ)
    rw [ff_natCard_omegaProj_six_minus hQ hdim hsgn,
      natCard_omegaGroup_six_minus hQ hdim hsgn] at h1
    omega
  have he : Nat.card ↥(U.comap (omegaToProj hQ)) = Nat.card ↥(ffLift hQ U) :=
    Nat.card_congr (Subgroup.equivMapOfInjective (U.comap (omegaToProj hQ))
      (omegaGroup hQ).subtype (Subgroup.subtype_injective (omegaGroup hQ))).toEquiv
  rw [← he, card_comap_eq_card_ker_mul_card_of_le_range (omegaToProj hQ) hle, hker]

@[expose] noncomputable def ffB1 (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c) :
    Subgroup ↥(omegaProj hQ) :=
  ffStar hQ (ffB0 fr)

@[expose] noncomputable def ffP1 (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c) :
    Subgroup ↥(omegaProj hQ) :=
  ffStar hQ (ffP0 hQ fr)

theorem ffB0_le_omega (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c) :
    ffB0 fr ≤ omegaGroup hQ :=
  (ffB0_le_ffP0 hQ fr).trans (ffP0_le_omega hQ fr)

theorem ffLift_ffB1 (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c) :
    ffLift hQ (ffB1 hQ fr) = ffB0 fr := by
  rw [ffB1]
  exact ffLift_ffStar hQ (ffB0_le_omega hQ fr) (piOrth_mem_ffB0 fr)

theorem ffLift_ffP1 (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c) :
    ffLift hQ (ffP1 hQ fr) = ffP0 hQ fr := by
  rw [ffP1]
  exact ffLift_ffStar hQ (ffP0_le_omega hQ fr)
    ((ffB0_le_ffP0 hQ fr) (piOrth_mem_ffB0 fr))

theorem ffB1_card (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (fr : NFrame Q (Fin 6) c) : Nat.card ↥(ffB1 hQ fr) = 16 := by
  have h := ffLift_card hQ hdim hsgn (ffB1 hQ fr)
  rw [ffLift_ffB1, ffB0_card] at h
  omega

theorem ffB1_elemAb2 (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (fr : NFrame Q (Fin 6) c) : IsElemAb2 (ffB1 hQ fr) 4 := by
  have hcomm : ∀ (a : ↥(omegaProj hQ)), a ∈ ffB1 hQ fr → ∀ (b : ↥(omegaProj hQ)),
      b ∈ ffB1 hQ fr → a * b = b * a := by
    intro a ha b hb
    have ha' : a ∈ ffStar hQ (ffB0 fr) := ha
    have hb' : b ∈ ffStar hQ (ffB0 fr) := hb
    rw [mem_ffStar_iff] at ha' hb'
    obtain ⟨g, hg, hga⟩ := ha'
    obtain ⟨g', hg', hgb⟩ := hb'
    rw [← hga, ← hgb, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (ffB0_comm fr hg hg')
  have hsq : ∀ x ∈ ffB1 hQ fr, x * x = 1 := by
    intro x hx
    have hx' : x ∈ ffStar hQ (ffB0 fr) := hx
    rw [mem_ffStar_iff] at hx'
    obtain ⟨g, hg, hgx⟩ := hx'
    rw [← hgx, ← map_mul]
    have h2 : g * g = 1 := Subtype.ext (ffB0_mul_self fr hg)
    rw [h2, map_one]
  refine ⟨?_, ?_⟩
  · refine ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, ?_⟩
    intro x hx
    rw [pow_two]
    exact hsq x hx
  · rw [ffB1_card hQ hdim hsgn fr]
    norm_num

theorem ffP1_card (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (fr : NFrame Q (Fin 6) c) : Nat.card ↥(ffP1 hQ fr) = 2 ^ 7 := by
  have h := ffLift_card hQ hdim hsgn (ffP1 hQ fr)
  rw [ffLift_ffP1, ffP0_card] at h
  norm_num at h ⊢
  omega

theorem ffP1_sylow (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (fr : NFrame Q (Fin 6) c) :
    IsSylow2Of (ffP1 hQ fr) (⊤ : Subgroup ↥(omegaProj hQ)) := by
  refine ⟨le_top, IsPGroup.of_card (p := 2) (n := 7) (ffP1_card hQ hdim hsgn fr), ?_⟩
  rw [Subgroup.relIndex_top_right]
  have h := Subgroup.card_mul_index (H := ffP1 hQ fr)
  rw [ffP1_card hQ hdim hsgn fr, ff_natCard_omegaProj_six_minus hQ hdim hsgn] at h
  have hidx : (ffP1 hQ fr).index = 25515 := by omega
  rw [hidx]
  norm_num

theorem ffB1_le_ffP1 (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c) :
    ffB1 hQ fr ≤ ffP1 hQ fr := by
  intro y hy
  have hy' : y ∈ ffStar hQ (ffB0 fr) := hy
  show y ∈ ffStar hQ (ffP0 hQ fr)
  rw [mem_ffStar_iff] at hy' ⊢
  obtain ⟨g, hg, hge⟩ := hy'
  exact ⟨g, ffB0_le_ffP0 hQ fr hg, hge⟩

theorem ffB1_normalE16 (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (fr : NFrame Q (Fin 6) c) :
    IsNormalE16In (ffP1 hQ fr) (ffB1 hQ fr) := by
  refine ⟨ffB1_le_ffP1 hQ fr, ffB1_elemAb2 hQ hdim hsgn fr, ?_⟩
  rw [Subgroup.normal_subgroupOf_iff (ffB1_le_ffP1 hQ fr)]
  intro h k hh hk
  have hh' : h ∈ ffStar hQ (ffB0 fr) := hh
  have hk' : k ∈ ffStar hQ (ffP0 hQ fr) := hk
  rw [mem_ffStar_iff] at hh' hk'
  obtain ⟨g', hg', hg'e⟩ := hh'
  obtain ⟨g, hg, hge⟩ := hk'
  obtain ⟨K, hK, hKe⟩ := (mem_ffB0_iff fr).mp hg'
  obtain ⟨σ, -, J, -, hJe⟩ := (mem_ffP0_iff hQ fr).mp hg
  show k * h * k⁻¹ ∈ ffStar hQ (ffB0 fr)
  rw [mem_ffStar_iff]
  refine ⟨g * g' * g⁻¹, ?_, ?_⟩
  · rw [mem_ffB0_iff]
    refine ⟨K.map σ.toEmbedding, by rw [Finset.card_map]; exact hK, ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hJe, hKe,
      ffMono_conj_signChange]
  · rw [map_mul, map_mul, map_inv, hge, hg'e]

theorem ffLift_isLiftE16 (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (fr : NFrame Q (Fin 6) c) {U : Subgroup ↥(omegaProj hQ)}
    (hU : U ≤ ffP1 hQ fr) (hE : IsElemAb2 U 4) : IsLiftE16 hQ fr (ffLift hQ U) := by
  have habel : CFSG.Open.IsElemAbelian 2 U := hE.1
  have hcardU : Nat.card ↥U = 16 := by
    have h := hE.2
    norm_num at h ⊢
    exact h
  have hpi : piOrth Q ∈ omegaGroup hQ := ff_piOrth_mem_omegaGroup_six_minus hQ hdim hsgn
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    rw [mem_ffLift_iff] at hg
    obtain ⟨hm, hU'⟩ := hg
    have hU'' : omegaToProj hQ ⟨g, hm⟩ ∈ ffStar hQ (ffP0 hQ fr) := hU hU'
    rw [mem_ffStar_iff] at hU''
    obtain ⟨p, hp, hpe⟩ := hU''
    rcases omegaToProj_eq_iff hQ hpe.symm with h | h
    · have hg' : g = (p : OGroup Q) := h.symm
      rw [hg']
      exact hp
    · have hp' : (p : OGroup Q) = piOrth Q * g := h
      have hg' : g = piOrth Q * (p : OGroup Q) := by
        rw [hp', ← mul_assoc, piOrth_mul_self, one_mul]
      rw [hg']
      exact Subgroup.mul_mem _ (ffB0_le_ffP0 hQ fr (piOrth_mem_ffB0 fr)) hp
  · rw [mem_ffLift_iff]
    refine ⟨hpi, ?_⟩
    have h1 : omegaToProj hQ ⟨piOrth Q, hpi⟩ = 1 :=
      (omegaToProj_eq_one_iff hQ _).mpr (Or.inr rfl)
    rw [h1]
    exact U.one_mem
  · rw [ffLift_card hQ hdim hsgn U, hcardU]
  · intro u hu
    have hu' : u ∈ omegaGroup hQ := ffLift_le_omega hQ U hu
    have hxU : omegaToProj hQ ⟨u, hu'⟩ ∈ U := ((mem_ffLift_iff hQ).mp hu).2
    have hsq : omegaToProj hQ ⟨u, hu'⟩ * omegaToProj hQ ⟨u, hu'⟩ = 1 := by
      simpa [pow_two] using habel.2 _ hxU
    have hmap : omegaToProj hQ ⟨u * u, (omegaGroup hQ).mul_mem hu' hu'⟩ = 1 := by
      rw [show (⟨u * u, (omegaGroup hQ).mul_mem hu' hu'⟩ : ↥(omegaGroup hQ)) =
        ⟨u, hu'⟩ * ⟨u, hu'⟩ from rfl, map_mul]
      exact hsq
    rcases (omegaToProj_eq_one_iff hQ ⟨u * u, (omegaGroup hQ).mul_mem hu' hu'⟩).mp hmap with
      h | h
    · exact Or.inl h
    · exact Or.inr h
  · intro u hu v hv
    have hu' : u ∈ omegaGroup hQ := ffLift_le_omega hQ U hu
    have hv' : v ∈ omegaGroup hQ := ffLift_le_omega hQ U hv
    have hxU : omegaToProj hQ ⟨u, hu'⟩ ∈ U := ((mem_ffLift_iff hQ).mp hu).2
    have hyU : omegaToProj hQ ⟨v, hv'⟩ ∈ U := ((mem_ffLift_iff hQ).mp hv).2
    have hcomm : omegaToProj hQ ⟨u, hu'⟩ * omegaToProj hQ ⟨v, hv'⟩ =
        omegaToProj hQ ⟨v, hv'⟩ * omegaToProj hQ ⟨u, hu'⟩ := by
      haveI : IsMulCommutative U := habel.1
      exact congrArg Subtype.val (mul_comm' (⟨_, hxU⟩ : U) (⟨_, hyU⟩ : U))
    have heq : omegaToProj hQ ⟨u * v, (omegaGroup hQ).mul_mem hu' hv'⟩ =
        omegaToProj hQ ⟨v * u, (omegaGroup hQ).mul_mem hv' hu'⟩ := by
      rw [show (⟨u * v, (omegaGroup hQ).mul_mem hu' hv'⟩ : ↥(omegaGroup hQ)) =
          ⟨u, hu'⟩ * ⟨v, hv'⟩ from rfl,
        show (⟨v * u, (omegaGroup hQ).mul_mem hv' hu'⟩ : ↥(omegaGroup hQ)) =
          ⟨v, hv'⟩ * ⟨u, hu'⟩ from rfl, map_mul, map_mul]
      exact hcomm
    rcases omegaToProj_eq_iff hQ heq with h | h
    · exact Or.inl h.symm
    · have h2 : v * u = piOrth Q * (u * v) := h
      exact Or.inr (by rw [h2, ← mul_assoc, piOrth_mul_self, one_mul])

theorem ffP1_E16_unique (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (fr : NFrame Q (Fin 6) c) {U₁ U₂ : Subgroup ↥(omegaProj hQ)}
    (h₁ : U₁ ≤ ffP1 hQ fr) (e₁ : IsElemAb2 U₁ 4) (h₂ : U₂ ≤ ffP1 hQ fr) (e₂ : IsElemAb2 U₂ 4)
    (n₁ : U₁ ≠ ffB1 hQ fr) (n₂ : U₂ ≠ ffB1 hQ fr) : U₁ = U₂ := by
  have hl₁ : IsLiftE16 hQ fr (ffLift hQ U₁) := ffLift_isLiftE16 hQ hdim hsgn fr h₁ e₁
  have hl₂ : IsLiftE16 hQ fr (ffLift hQ U₂) := ffLift_isLiftE16 hQ hdim hsgn fr h₂ e₂
  have hne₁ : ffLift hQ U₁ ≠ ffB0 fr := by
    intro h
    rw [← ffLift_ffB1 hQ fr] at h
    exact n₁ (ffLift_injective hQ h)
  have hne₂ : ffLift hQ U₂ ≠ ffB0 fr := by
    intro h
    rw [← ffLift_ffB1 hQ fr] at h
    exact n₂ (ffLift_injective hQ h)
  exact ffLift_injective hQ (ff_liftE16_unique hQ fr hl₁ hl₂ hne₁ hne₂)

end CFSG.OddStandard.SmallF3.Omega
