module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentQuot
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentA8
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverExternalOuter
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.QuasithinUnique.Id2519.Tab

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint
open CFSG.ComponentClassification CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.J2Cover CFSG.ComponentClassification.J2Cover.External
open CFSG.Sporadic.Schreier
open scoped commutatorElement

theorem card_centralizer_involution_P {p : P} (hp : orderOf p = 2) :
    Nat.card (Subgroup.centralizer ({p} : Set P)) = 240 ∨
      Nat.card (Subgroup.centralizer ({p} : Set P)) = 1920 := by
  have hp' : orderOf (p : Equiv.Perm (Fin 315)) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact hp
  obtain ⟨r, hr, c, hcP, hpc⟩ := inner_classes.1 (p : Equiv.Perm (Fin 315)) p.2 hp'
  have hmap : (Subgroup.centralizer ({p} : Set P)).map P.subtype =
      centralizerIn P (p : Equiv.Perm (Fin 315)) := by
    ext x
    rw [mem_centralizerIn]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy)⟩
    · rintro ⟨hx, hxp⟩
      exact ⟨⟨x, hx⟩, Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext hxp), rfl⟩
  have hcard : Nat.card (Subgroup.centralizer ({p} : Set P)) =
      Nat.card (centralizerIn P (p : Equiv.Perm (Fin 315))) := by
    rw [← hmap, Subgroup.card_map_of_injective P.subtype_injective]
  rw [hcard, hpc, centralizerIn_conj P hcP, Subgroup.card_map_of_injective (MulAut.conj c).injective]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  obtain ⟨-, -, h1c, -, h2c⟩ := inner_classes
  rcases hr with rfl | rfl
  · left
    rw [h1c]
    exact cent2B_facts.2.1
  · right
    rw [h2c]
    exact cent2A_facts.2.1

section Main

variable {G : Type} [Group G] [Finite G]

theorem tabIdentFor_j2
    : TabIdentFor (@Ident.FamSporadic .J2) := by
  intro G _ _ X K t hs hX
  obtain ⟨e0⟩ := hX
  have hQ : Subgroup.center NativeSporadic.J2 = ⊥ := by
    have h := Subgroup.map_center_eq nativeEquivP
    rw [center_P] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ nativeEquivP.injective).mp h
  have hZ : Subgroup.center ↥X = CFSG.pCore 2 ↥X := hs.center_eq_pCore e0 hQ
  let e' : (↥X ⧸ Subgroup.center ↥X) ≃* P :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans e0).trans nativeEquivP
  have hπ := quotProj_surjective e'
  have hker := quotProj_ker e'
  set α := quotAct (quotProj e') hπ hker hs.tN with hαdef
  have hα2 : α * α = 1 := quotAct_mul_self (quotProj e') hπ hker hs.tN hs.sq
  have hα1 : α ≠ 1 := quotAct_ne_one (quotProj e') hπ hker hs.tN hs.quasi hs.comm
  have hord : orderOf α = 2 := orderOf_eq_prime (by rw [sq]; exact hα2) hα1
  let ρ : ↥K →* P := (quotProj e').comp (Subgroup.inclusion hs.K_le)
  have hρinj : Function.Injective ρ := hs.injective_proj hs.ktype (quotProj e') hker
  have hKcard : Nat.card ρ.range = Nat.card ↥K :=
    (Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv).symm
  have hKfix : ρ.range ≤ fixSub α := by
    rintro _ ⟨k, rfl⟩
    rw [mem_fixSub]
    have hkt : (k : G) * t = t * (k : G) := Subgroup.mem_centralizer_singleton_iff.mp
      (hs.K_le_cent k.2)
    have hy : ((Subgroup.inclusion hs.K_le k : X) : G) =
        t * ((Subgroup.inclusion hs.K_le k : X) : G) * t⁻¹ := by
      rw [Subgroup.coe_inclusion]
      calc (k : G) = (k * t) * t⁻¹ := by group
        _ = (t * k) * t⁻¹ := by rw [hkt]
    exact quotAct_apply (quotProj e') hπ hker hs.tN _ _ hy
  have hCfix : ((X ⊓ Subgroup.centralizer ({t} : Set G)).subgroupOf X).map (quotProj e') ≤
      fixSub α := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_fixSub]
    have hxt : (x : G) * t = t * (x : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_subgroupOf.mp hx).2
    have hy : (x : G) = t * (x : G) * t⁻¹ := by
      calc (x : G) = (x * t) * t⁻¹ := by group
        _ = (t * x) * t⁻¹ := by rw [hxt]
    exact quotAct_apply (quotProj e') hπ hker hs.tN x x hy
  by_cases hin : α ∈ OuterAutomorphisms.inner P
  ·
    exfalso
    obtain ⟨p, hp⟩ := hin
    have hp2 : p * p = 1 := by
      have h1 : MulAut.conj (p * p) = 1 := by rw [map_mul, hp, hα2]
      have h2 : p * p ∈ Subgroup.center P := by
        rw [Subgroup.mem_center_iff]
        intro q
        have h3 := congrArg (fun σ : MulAut P => σ q) h1
        simp only [MulAut.conj_apply, MulAut.one_apply] at h3
        calc q * (p * p) = (p * p * q * (p * p)⁻¹) * (p * p) := by rw [h3]
          _ = p * p * q := by group
      rw [center_P, Subgroup.mem_bot] at h2
      exact h2
    have hp1 : p ≠ 1 := by
      rintro rfl
      apply hα1
      rw [← hp, map_one]
    have hpo : orderOf p = 2 := orderOf_eq_prime (by rw [sq]; exact hp2) hp1
    have hfix : fixSub α = Subgroup.centralizer ({p} : Set P) := by
      ext q
      rw [mem_fixSub, ← hp, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
      constructor
      · intro h
        calc q * p = (p * q * p⁻¹) * p := by rw [h]
          _ = p * q := by group
      · intro h
        calc p * q * p⁻¹ = (q * p) * p⁻¹ := by rw [h]
          _ = q := by group
    have hdvd : Nat.card ↥K ∣ Nat.card (Subgroup.centralizer ({p} : Set P)) := by
      rw [← hKcard, ← hfix]
      exact Subgroup.card_dvd_of_le hKfix
    have hle := Nat.le_of_dvd Nat.card_pos hdvd
    rcases card_centralizer_involution_P hpo with h | h <;> rw [h] at hdvd hle <;>
      rcases hs.ktype with hb | hl | ha
    · have := hb.card_ge
      omega
    · rw [hl.card_eq] at hdvd
      omega
    · rw [ha.card_eq] at hdvd
      omega
    · have := hb.card_ge
      omega
    · rw [hl.card_eq] at hdvd
      omega
    · rw [ha.card_eq] at hdvd
      omega
  ·
    obtain ⟨g, hg⟩ := exists_conj_beta_of_outer hord hin
    have hFcard : Nat.card (fixSub α) = 336 := by
      rw [hg]
      exact card_fixSub_conj_beta g
    have hKdvd : Nat.card ↥K ∣ 336 := by
      rw [← hKcard, ← hFcard]
      exact Subgroup.card_dvd_of_le hKfix
    have hL32 : IsL32 K := by
      rcases hs.ktype with hb | hl | ha
      · exfalso
        have h1 := hb.card_ge
        have h2 := Nat.le_of_dvd (by norm_num) hKdvd
        omega
      · exact hl
      · exfalso
        rw [ha.card_eq] at hKdvd
        omega
    have hK168 : Nat.card ↥K = 168 := hL32.card_eq
    have hcomm : ⁅fixSub α, fixSub α⁆ ≤ ρ.range :=
      commutator_le_of_card_eq_two_mul hKfix (by rw [hFcard, hKcard, hK168])
    have hKeq : K = CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf
        (X ⊓ Subgroup.centralizer ({t} : Set G)) := by
      refine hs.eq_perfectResidual_of_map (quotProj e') hker.le ?_
      rw [hs.map_subgroupOf_eq_range]
      exact (Subgroup.commutator_mono hCfix hCfix).trans hcomm
    have hout : InducesOuter t X :=
      ⟨hs.tN, fun hinn => hin (quotAct_mem_inner_of_inducesInner (quotProj e') hπ hker hs.tN hs.sq
        hinn)⟩
    refine ⟨?_, hKeq, fun hb => ?_, fun _ => Or.inr ⟨hL32, ⟨e'.trans nativeEquivP.symm⟩, hout⟩,
      fun ha => ?_⟩
    · rw [hZ]
      exact CFSG.pCore_isPGroup
    · have h1 := hb.card_ge
      omega
    · have h1 := ha.card_eq
      omega

end Main

end CFSG.QuasithinUnique.Id2519.Tab
