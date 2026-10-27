module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFSimCard
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFMonoE16
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OmegaProj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs
public import Certificates.Data.ExceptionalSL3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {c : ZMod 3}

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

@[expose] noncomputable def hPm (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c) :
    Subgroup (ProjOrth Q) :=
  (ffP0 hQ fr).map (toProj Q)

theorem mem_hPm_iff (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c) {y : ProjOrth Q} :
    y ∈ hPm hQ fr ↔ ∃ g ∈ ffP0 hQ fr, toProj Q g = y :=
  Subgroup.mem_map

theorem comap_hPm (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c) :
    (hPm hQ fr).comap (toProj Q) = ffP0 hQ fr := by
  rw [hPm, Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  exact sup_eq_left.mpr fun g hg => by
    rcases mem_piGroup_iff.mp hg with rfl | rfl
    · exact (ffP0 hQ fr).one_mem
    · exact ffB0_le_ffP0 hQ fr (piOrth_mem_ffB0 fr)

theorem hPm_le_omegaProj (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c) :
    hPm hQ fr ≤ omegaProj hQ :=
  Subgroup.map_mono (ffP0_le_omega hQ fr)

theorem hPm_card (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (fr : NFrame Q (Fin 6) c) : Nat.card (hPm hQ fr) = 2 ^ 7 := by
  have h0 : 0 < Module.finrank (ZMod 3) V := by rw [hdim]; norm_num
  have hker : (toProj Q).ker = piGroup Q := QuotientGroup.ker_mk' (piGroup Q)
  have hker_le : (toProj Q).ker ≤ ffP0 hQ fr := by
    rw [hker]
    intro g hg
    rcases mem_piGroup_iff.mp hg with rfl | rfl
    · exact (ffP0 hQ fr).one_mem
    · exact ffB0_le_ffP0 hQ fr (piOrth_mem_ffB0 fr)
  have h := Subgroup.relIndex_mul_card (H := (toProj Q).ker) (K := ffP0 hQ fr)
  rw [Subgroup.relIndex_ker] at h
  rw [inf_eq_left.mpr hker_le, hker, card_piGroup (Q := Q) h0, ffP0_card] at h
  unfold hPm
  norm_num at h ⊢
  omega

theorem hPm_sylow (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (fr : NFrame Q (Fin 6) c) :
    IsSylow2Of (hPm hQ fr) (omegaProj hQ) := by
  refine ⟨hPm_le_omegaProj hQ fr,
    IsPGroup.of_card (p := 2) (n := 7) (hPm_card hQ hdim hsgn fr), ?_⟩
  have h := Subgroup.relIndex_mul_card (H := hPm hQ fr) (K := omegaProj hQ)
  rw [inf_eq_left.mpr (hPm_le_omegaProj hQ fr)] at h
  rw [hPm_card hQ hdim hsgn fr, ff_natCard_omegaProj_six_minus hQ hdim hsgn] at h
  have hidx : (hPm hQ fr).relIndex (omegaProj hQ) = 25515 := by
    norm_num at h
    omega
  rw [hidx]
  norm_num

theorem mem_normalizer_of_toProj (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c) {t : OGroup Q}
    (ht : toProj Q t ∈ normalizer (hPm hQ fr : Set (ProjOrth Q))) :
    t ∈ normalizer (ffP0 hQ fr : Set (OGroup Q)) := by
  haveI : Finite (ffP0 hQ fr) :=
    Nat.finite_of_card_ne_zero (by rw [ffP0_card hQ fr]; norm_num)
  apply Subgroup.mem_normalizer_fintype
  intro u hu
  have htu : toProj Q (t * u * t⁻¹) ∈ hPm hQ fr := by
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp ht (toProj Q u)).mp
      ((mem_hPm_iff hQ fr).mpr ⟨u, hu, rfl⟩)
  have h2 := Subgroup.mem_comap.mpr htu
  rwa [comap_hPm hQ fr] at h2

theorem isLiftE16_comap (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (fr : NFrame Q (Fin 6) c) {B : Subgroup (ProjOrth Q)}
    (hB : B ≤ hPm hQ fr) (hE : IsElemAb2 B 4) : IsLiftE16 hQ fr (B.comap (toProj Q)) := by
  have h0 : 0 < Module.finrank (ZMod 3) V := by rw [hdim]; norm_num
  have hcardB : Nat.card B = 16 := by
    have h := hE.2
    norm_num at h ⊢
    exact h
  have hrange : B ≤ (toProj Q).range := by
    rw [MonoidHom.range_eq_top_of_surjective (toProj Q) (QuotientGroup.mk'_surjective (piGroup Q))]
    exact le_top
  have hker : Nat.card (toProj Q).ker = 2 := by
    rw [QuotientGroup.ker_mk']
    exact card_piGroup (Q := Q) h0
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    have hg' : g ∈ (hPm hQ fr).comap (toProj Q) :=
      Subgroup.mem_comap.mpr (hB (Subgroup.mem_comap.mp hg))
    rwa [comap_hPm hQ fr] at hg'
  · rw [Subgroup.mem_comap, toProj_piOrth]
    exact B.one_mem
  · have h := card_comap_eq_card_ker_mul_card_of_le_range (toProj Q) hrange
    rw [hker, hcardB] at h
    norm_num at h
    exact h
  · intro u hu
    have hsq : toProj Q (u * u) = 1 := by
      rw [map_mul]
      simpa [pow_two] using hE.1.2 (toProj Q u) (Subgroup.mem_comap.mp hu)
    have hmem : u * u ∈ piGroup Q := by
      rw [← QuotientGroup.ker_mk' (piGroup Q)]
      exact MonoidHom.mem_ker.mpr hsq
    exact mem_piGroup_iff.mp hmem
  · intro u hu v hv
    haveI : IsMulCommutative B := hE.1.1
    have hcomm : toProj Q u * toProj Q v = toProj Q v * toProj Q u :=
      congrArg Subtype.val (mul_comm' (⟨toProj Q u, Subgroup.mem_comap.mp hu⟩ : B)
        (⟨toProj Q v, Subgroup.mem_comap.mp hv⟩ : B))
    have heq : toProj Q (u * v) = toProj Q (v * u) := by
      rw [map_mul, map_mul]
      exact hcomm
    have hmem : (v * u)⁻¹ * (u * v) ∈ piGroup Q := by
      rw [← QuotientGroup.ker_mk' (piGroup Q)]
      exact MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, heq, inv_mul_cancel])
    rcases mem_piGroup_iff.mp hmem with h | h
    · left
      exact (inv_mul_eq_one.mp h).symm
    · right
      have huv : u * v = (v * u) * piOrth Q := by rw [← h, mul_inv_cancel_left]
      rw [huv, mul_piOrth_comm]

theorem map_toProj_isElemAb2 (hdim : 0 < Module.finrank (ZMod 3) V) {U : Subgroup (OGroup Q)}
    {k : ℕ} (hπ : piOrth Q ∈ U) (hc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    (hs : ∀ a ∈ U, a * a = 1) (hcard : Nat.card U = 2 ^ (k + 1)) :
    IsElemAb2 (U.map (toProj Q)) k := by
  have hker_le : (toProj Q).ker ≤ U := by
    rw [QuotientGroup.ker_mk']
    intro g hg
    rcases mem_piGroup_iff.mp hg with rfl | rfl
    · exact U.one_mem
    · exact hπ
  have hrange : U.map (toProj Q) ≤ (toProj Q).range := by
    rw [MonoidHom.range_eq_top_of_surjective (toProj Q) (QuotientGroup.mk'_surjective (piGroup Q))]
    exact le_top
  have hcomm : ∀ a ∈ U.map (toProj Q), ∀ b ∈ U.map (toProj Q), a * b = b * a := by
    intro a ha b hb
    rw [Subgroup.mem_map] at ha hb
    obtain ⟨a', ha', ha'e⟩ := ha
    obtain ⟨b', hb', hb'e⟩ := hb
    rw [← ha'e, ← hb'e, ← map_mul, ← map_mul]
    exact congrArg (toProj Q) (hc a' ha' b' hb')
  have hsq : ∀ x ∈ U.map (toProj Q), x * x = 1 := by
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨a, ha, hae⟩ := hx
    rw [← hae, ← map_mul, hs a ha, map_one]
  have hcardmap : Nat.card (U.map (toProj Q)) = 2 ^ k := by
    have h := card_comap_eq_card_ker_mul_card_of_le_range (toProj Q) hrange
    rw [Subgroup.comap_map_eq, sup_eq_left.mpr hker_le] at h
    have hker : Nat.card (toProj Q).ker = 2 := by
      rw [QuotientGroup.ker_mk']
      exact card_piGroup (Q := Q) hdim
    rw [hker, hcard] at h
    rw [pow_succ] at h
    omega
  refine ⟨?_, hcardmap⟩
  · refine ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, ?_⟩
    intro x hx
    rw [pow_two]
    exact hsq x hx

theorem map_toProj_compl (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c)
    {B D : Subgroup (OGroup Q)} (hπ : piOrth Q ∈ B) (hD : D ≤ ffP0 hQ fr) (hinf : B ⊓ D = ⊥)
    (hB : B ≤ ffP0 hQ fr) (hprod : ∀ g ∈ ffP0 hQ fr, ∃ b ∈ B, ∃ d ∈ D, g = b * d) :
    B.map (toProj Q) ⊓ D.map (toProj Q) = ⊥ ∧
      B.map (toProj Q) ⊔ D.map (toProj Q) = hPm hQ fr := by
  constructor
  · apply le_antisymm _ bot_le
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxB, hxD⟩ := hx
    rw [Subgroup.mem_map] at hxB hxD
    obtain ⟨b, hb, rfl⟩ := hxB
    obtain ⟨d, hd, hde⟩ := hxD
    have hmem : d⁻¹ * b ∈ piGroup Q := by
      rw [← QuotientGroup.ker_mk' (piGroup Q)]
      exact MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hde, inv_mul_cancel])
    have hd1 : d = 1 := by
      have hdB : d ∈ B := by
        rcases mem_piGroup_iff.mp hmem with h | h
        · have hdb : d = b := inv_mul_eq_one.mp h
          rw [hdb]; exact hb
        · have hb_eq : b = d * piOrth Q := by rw [← h, mul_inv_cancel_left]
          have hdb : d = b * piOrth Q := by
            rw [hb_eq, mul_assoc, piOrth_mul_self, mul_one]
          rw [hdb]; exact B.mul_mem hb hπ
      have hdBD : d ∈ B ⊓ D := ⟨hdB, hd⟩
      rw [hinf] at hdBD
      exact Subgroup.mem_bot.mp hdBD
    rw [← hde, hd1, map_one]
    exact Subgroup.mem_bot.mpr rfl
  · apply le_antisymm
    · exact sup_le (Subgroup.map_mono hB) (Subgroup.map_mono hD)
    · intro y hy
      rw [mem_hPm_iff] at hy
      obtain ⟨g, hg, rfl⟩ := hy
      obtain ⟨b, hb, d, hd, rfl⟩ := hprod g hg
      rw [map_mul]
      exact Subgroup.mul_mem_sup (Subgroup.mem_map.mpr ⟨b, hb, rfl⟩)
        (Subgroup.mem_map.mpr ⟨d, hd, rfl⟩)

end CFSG.OddStandard.SmallF3.Omega
