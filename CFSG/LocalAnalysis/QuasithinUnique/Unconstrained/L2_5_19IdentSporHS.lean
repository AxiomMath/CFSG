module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentSocleQuot
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentSporHSTwoB
public import CFSG.Sporadic.SmallOddCore.HSAut

public section

namespace CFSG.QuasithinUnique.Id2519.SporHS

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint
open CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th.Native
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.QuasithinUnique.Id2519.Tab
open scoped commutatorElement

section Facts

theorem no_big_prime_dvd (a b c : ℕ) :
    ∀ p : ℕ, p.Prime → 17 ≤ p → ¬ p ∣ 2 ^ a * 3 ^ b * 5 ^ c := by
  intro p hp h17 hd
  rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
      omega
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h)
      omega
  · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5)).1 (hp.dvd_of_dvd_pow h)
    omega

theorem center_hs
    : Subgroup.center NativeSporadic.HS = ⊥ :=
  center_eq_bot_of_simple_nonabelian CFSG.Sporadic.HS.fam_hs_simplicity.2.2 hs_not_comm

end Facts

theorem fix_data
    (α : MulAut hsP) (hα2 : α * α = 1) (hα1 : α ≠ 1) :
    ∃ r ∈ hsRows, ∃ g ∈ hsP, ∃ x : hsR,
      (∀ p : hsP, ((α p : hsP) : Equiv.Perm (Fin 3850)) = (x : Equiv.Perm (Fin 3850)) * p *
        (x : Equiv.Perm (Fin 3850))⁻¹) ∧
      (x : Equiv.Perm (Fin 3850)) = g * tp 3850 r.rep * g⁻¹ ∧
      (fixSubgroup α).map hsP.subtype =
        (hsP ⊓ Subgroup.centralizer ({tp 3850 r.rep} : Set (Equiv.Perm (Fin 3850)))).map
          (MulAut.conj g).toMonoidHom := by
  obtain ⟨eAut, heAut, -⟩ := hs_full_automorphism_model
  obtain ⟨x, hx⟩ := eAut.surjective α
  have hxform : ∀ p : hsP, ((α p : hsP) : Equiv.Perm (Fin 3850)) =
      (x : Equiv.Perm (Fin 3850)) * p * (x : Equiv.Perm (Fin 3850))⁻¹ := by
    intro p
    rw [← hx]
    exact heAut x p
  have hxx : x * x = 1 := by
    apply eAut.injective
    rw [map_mul, hx, hα2, map_one]
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hα1 (by rw [← hx, map_one])
  have hxord : orderOf (x : Equiv.Perm (Fin 3850)) = 2 := by
    have h2 : (x : Equiv.Perm (Fin 3850)) ^ 2 = 1 := by
      rw [pow_two, ← Subgroup.coe_mul, hxx, Subgroup.coe_one]
    refine orderOf_eq_prime h2 ?_
    intro h
    exact hx1 (Subtype.ext h)
  obtain ⟨-, -, -, hrows, hcover, -, -, -⟩ := hs_involution_centralizers
  obtain ⟨r, hr, g, hg, hxg⟩ := hcover (x : Equiv.Perm (Fin 3850)) x.2 hxord
  refine ⟨r, hr, g, hg, x, hxform, hxg, ?_⟩
  set t := tp 3850 r.rep with ht
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    have h1 : (x : Equiv.Perm (Fin 3850)) * (p : Equiv.Perm (Fin 3850)) *
        (x : Equiv.Perm (Fin 3850))⁻¹ = p := by
      rw [← hxform p]
      exact congrArg Subtype.val (mem_fixSubgroup.1 hp)
    have hgP : g⁻¹ * (p : Equiv.Perm (Fin 3850)) * g ∈ hsP :=
      hsP.mul_mem (hsP.mul_mem (hsP.inv_mem hg) p.2) hg
    have h1' : (g * t * g⁻¹) * (p : Equiv.Perm (Fin 3850)) * (g * t * g⁻¹)⁻¹ = p := by
      rw [← hxg]
      exact h1
    have h2 : g⁻¹ * (p : Equiv.Perm (Fin 3850)) * g =
        t * (g⁻¹ * (p : Equiv.Perm (Fin 3850)) * g) * t⁻¹ := by
      calc g⁻¹ * (p : Equiv.Perm (Fin 3850)) * g
          = g⁻¹ * ((g * t * g⁻¹) * (p : Equiv.Perm (Fin 3850)) * (g * t * g⁻¹)⁻¹) * g := by
            rw [h1']
        _ = t * (g⁻¹ * (p : Equiv.Perm (Fin 3850)) * g) * t⁻¹ := by group
    refine ⟨g⁻¹ * (p : Equiv.Perm (Fin 3850)) * g,
      ⟨hgP, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩, ?_⟩
    · calc g⁻¹ * (p : Equiv.Perm (Fin 3850)) * g * t
          = (t * (g⁻¹ * (p : Equiv.Perm (Fin 3850)) * g) * t⁻¹) * t := by rw [← h2]
        _ = t * (g⁻¹ * (p : Equiv.Perm (Fin 3850)) * g) := by group
    · show g * (g⁻¹ * (p : Equiv.Perm (Fin 3850)) * g) * g⁻¹ = (p : Equiv.Perm (Fin 3850))
      group
  · rintro ⟨c, ⟨hcP, hcC⟩, rfl⟩
    have hc : c * t = t * c := Subgroup.mem_centralizer_singleton_iff.1 hcC
    have hqP : (MulAut.conj g) c ∈ hsP := by
      rw [MulAut.conj_apply]
      exact hsP.mul_mem (hsP.mul_mem hg hcP) (hsP.inv_mem hg)
    refine ⟨⟨(MulAut.conj g) c, hqP⟩, ?_, rfl⟩
    refine mem_fixSubgroup.2 ?_
    apply Subtype.ext
    rw [hxform]
    show (x : Equiv.Perm (Fin 3850)) * ((MulAut.conj g) c) * (x : Equiv.Perm (Fin 3850))⁻¹ =
      (MulAut.conj g) c
    rw [hxg, MulAut.conj_apply]
    calc g * t * g⁻¹ * (g * c * g⁻¹) * (g * t * g⁻¹)⁻¹ = g * (t * c * t⁻¹) * g⁻¹ := by group
      _ = g * c * g⁻¹ := by
        have : t * c * t⁻¹ = c := by rw [← hc]; group
        rw [this]

noncomputable def fixEquiv {α : MulAut hsP} {t g : Equiv.Perm (Fin 3850)}
    (h : (fixSubgroup α).map hsP.subtype =
      (hsP ⊓ Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 3850)))).map
        (MulAut.conj g).toMonoidHom) :
    ↥(fixSubgroup α) ≃* ↥(hsP ⊓ Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 3850)))) :=
  (Subgroup.equivMapOfInjective _ hsP.subtype hsP.subtype_injective).trans
    ((MulEquiv.subgroupCongr h).trans
      (Subgroup.equivMapOfInjective _ (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm)

theorem hsRows_cases {r : ClassRow} (hr : r ∈ hsRows) :
    r.centOrder = 7680 ∨
    (r.rep = hsCentTbl 12 ∧
      r.centGens = [hsCentTbl 13, hsCentTbl 14, hsCentTbl 15, hsCentTbl 16] ∧
      r.centOrder = 2880 ∧ r.outer = false) ∨
    (r.rep = hsCentTbl 21 ∧ r.centOrder = 40320) ∨ r.centOrder = 1920 := by
  simp only [hsRows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h
  · left
    rw [h]
  · right
    left
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [h]
  · right
    right
    left
    refine ⟨?_, ?_⟩ <;> rw [h]
  · right
    right
    right
    rw [h]

theorem tabIdentFor_hs_of
    (hout : ¬ HasKComponent ↥(hsP ⊓ Subgroup.centralizer
      ({tp 3850 (hsCentTbl 21)} : Set (Equiv.Perm (Fin 3850))))) :
    TabIdentFor (@Ident.FamSporadic .HS) := by
  intro G _ _ X K t hs hX
  obtain ⟨e0⟩ := hX
  have hZ : Subgroup.center ↥X = CFSG.pCore 2 ↥X := hs.center_eq_pCore e0 center_hs
  let e' : (↥X ⧸ Subgroup.center ↥X) ≃* hsP :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans e0).trans hsPermEquiv
  have hπ := quotProj_surjective e'
  have hker := quotProj_ker e'
  set α := quotAct (quotProj e') hπ hker hs.tN with hαdef
  have hα2 : α * α = 1 := quotAct_mul_self (quotProj e') hπ hker hs.tN hs.sq
  have hα1 : α ≠ 1 := quotAct_ne_one (quotProj e') hπ hker hs.tN hs.quasi hs.comm
  have hKcomp := hs.hasKComponent_fix_quot hs.ktype (quotProj e') hπ hker
  let ρ : ↥K →* hsP := (quotProj e').comp (Subgroup.inclusion hs.K_le)
  have hρinj : Function.Injective ρ := hs.injective_proj hs.ktype (quotProj e') hker
  have hKcard : Nat.card ρ.range = Nat.card ↥K :=
    (Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv).symm
  have hKfix : ρ.range ≤ fixSubgroup α := by
    rintro _ ⟨k, rfl⟩
    rw [mem_fixSubgroup]
    have hkt : (k : G) * t = t * (k : G) := Subgroup.mem_centralizer_singleton_iff.mp
      (hs.K_le_cent k.2)
    have hy : ((Subgroup.inclusion hs.K_le k : X) : G) =
        t * ((Subgroup.inclusion hs.K_le k : X) : G) * t⁻¹ := by
      rw [Subgroup.coe_inclusion]
      calc (k : G) = (k * t) * t⁻¹ := by group
        _ = (t * k) * t⁻¹ := by rw [hkt]
    exact quotAct_apply (quotProj e') hπ hker hs.tN _ _ hy
  have hCfix : ((X ⊓ Subgroup.centralizer ({t} : Set G)).subgroupOf X).map (quotProj e') ≤
      fixSubgroup α := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_fixSubgroup]
    have hxt : (x : G) * t = t * (x : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_subgroupOf.mp hx).2
    have hy : (x : G) = t * (x : G) * t⁻¹ := by
      calc (x : G) = (x * t) * t⁻¹ := by group
        _ = (t * x) * t⁻¹ := by rw [hxt]
    exact quotAct_apply (quotProj e') hπ hker hs.tN x x hy
  obtain ⟨r, hr, g, hg, x, hxform, hxg, hFmap⟩ := fix_data α hα2 hα1
  obtain ⟨-, -, -, hrows, -, -, -, -⟩ := hs_involution_centralizers
  obtain ⟨-, -, hrout, hrC, hrcard, -⟩ := hrows r hr
  have hFcard : Nat.card ↥(fixSubgroup α) = r.centOrder := by
    rw [← Subgroup.card_map_of_injective hsP.subtype_injective, hFmap,
      Subgroup.card_map_of_injective (MulAut.conj g).injective, hrcard]
  rcases hsRows_cases hr with h0 | ⟨hrep, hgens, hord, hrouter⟩ | ⟨hrep, hord⟩ | h3
  ·
    exfalso
    obtain ⟨B, -, hB⟩ := hKcomp
    have hd : Nat.card ↥B ∣ 7680 := by
      rw [← h0, ← hFcard]
      exact Subgroup.card_subgroup_dvd_card B
    refine hB.false_of_dvd hd (by norm_num) (by norm_num) fun p hp h17 => ?_
    have e : 2 * 7680 = 2 ^ 10 * 3 ^ 1 * 5 ^ 1 := by norm_num
    rw [e]
    exact no_big_prime_dvd 10 1 1 p hp h17
  ·
    have hFc : Nat.card ↥(fixSubgroup α) = 2880 := by rw [hFcard, hord]
    have hrinP : tp 3850 r.rep ∈ hsP := by
      by_contra hn
      have := hrout.2 hn
      rw [hrouter] at this
      exact absurd this (by decide)
    have hxP : (x : Equiv.Perm (Fin 3850)) ∈ hsP := by
      rw [hxg]
      exact hsP.mul_mem (hsP.mul_mem hg hrinP) (hsP.inv_mem hg)
    have hin : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner hsP := by
      refine ⟨⟨x, hxP⟩, MulEquiv.ext fun p => Subtype.ext ?_⟩
      rw [hxform p]
      simp [MulAut.conj_apply]
    have hind : CFSG.QuasithinUnique.Ch1.InducesInner t X :=
      inducesInner_of_quotAct_mem_inner (quotProj e') hπ hker hs.tN hs.quasi.1 hs.sq hin
    have hKdvd : Nat.card ↥K ∣ 2880 := by
      rw [← hKcard, ← hFc]
      exact Subgroup.card_dvd_of_le hKfix
    have hK360 : Nat.card ↥K = 360 := KOrder.eq_of_dvd_2880 hs.ktype.kOrder hKdvd
    have hA6 : IsA6 K := by
      rcases hs.ktype with hb | hl | ha
      · exfalso
        have := hb.card_ge
        omega
      · exfalso
        have := hl.card_eq
        omega
      · exact ha
    have hC : hsP ⊓ Subgroup.centralizer ({tp 3850 r.rep} : Set (Equiv.Perm (Fin 3850))) =
        genOf 3850 twoBGens := by
      rw [← hrC]
      exact congrArg (genOf 3850) hgens
    have hFcomm : Nat.card ↥(⁅fixSubgroup α, fixSubgroup α⁆) ≤ 360 := by
      have h1 : (⁅fixSubgroup α, fixSubgroup α⁆).map hsP.subtype =
          (⁅genOf 3850 twoBGens, genOf 3850 twoBGens⁆).map (MulAut.conj g).toMonoidHom := by
        rw [Subgroup.map_commutator, hFmap, hC, Subgroup.map_commutator]
      calc Nat.card ↥(⁅fixSubgroup α, fixSubgroup α⁆)
          = Nat.card ↥((⁅fixSubgroup α, fixSubgroup α⁆).map hsP.subtype) :=
            (Subgroup.card_map_of_injective hsP.subtype_injective).symm
        _ = Nat.card ↥((⁅genOf 3850 twoBGens, genOf 3850 twoBGens⁆).map
              (MulAut.conj g).toMonoidHom) := by rw [h1]
        _ = Nat.card ↥⁅genOf 3850 twoBGens, genOf 3850 twoBGens⁆ :=
            Subgroup.card_map_of_injective (MulAut.conj g).injective
        _ ≤ 360 := card_commutator_twoB_le
    have hperfK : ⁅ρ.range, ρ.range⁆ = ρ.range := by
      have hperf : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hs.perfect_K
      have h1 : ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = (⊤ : Subgroup ↥K) := by
        rw [← commutator_def]
        exact Group.IsPerfect.commutator_eq_top
      rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, h1]
    have hle : ρ.range ≤ ⁅fixSubgroup α, fixSubgroup α⁆ := by
      calc ρ.range = ⁅ρ.range, ρ.range⁆ := hperfK.symm
        _ ≤ ⁅fixSubgroup α, fixSubgroup α⁆ := Subgroup.commutator_mono hKfix hKfix
    have hcomm : ⁅fixSubgroup α, fixSubgroup α⁆ ≤ ρ.range :=
      (Subgroup.eq_of_le_of_card_ge hle (by rw [hKcard, hK360]; exact hFcomm)).symm.le
    have hKeq : K = CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf
        (X ⊓ Subgroup.centralizer ({t} : Set G)) := by
      refine hs.eq_perfectResidual_of_map (quotProj e') hker.le ?_
      rw [hs.map_subgroupOf_eq_range]
      exact (Subgroup.commutator_mono hCfix hCfix).trans hcomm
    have hL32 : ¬ IsL32 K := fun hl => by
      have := hl.card_eq
      omega
    refine ⟨?_, hKeq, fun hb => ?_, fun hl => absurd hl hL32, fun _ => ?_⟩
    · rw [hZ]
      exact CFSG.pCore_isPGroup
    · have := hb.card_ge
      omega
    · exact Or.inr (Or.inr (Or.inl ⟨hA6, ⟨e'.trans hsPermEquiv.symm⟩, hind⟩))
  ·
    exfalso
    obtain ⟨B, hBc, hB⟩ := hKcomp
    have hC : hsP ⊓ Subgroup.centralizer ({tp 3850 r.rep} : Set (Equiv.Perm (Fin 3850))) =
        hsP ⊓ Subgroup.centralizer ({tp 3850 (hsCentTbl 21)} : Set (Equiv.Perm (Fin 3850))) := by
      rw [hrep]
    have hFmap' : (fixSubgroup α).map hsP.subtype =
        (hsP ⊓ Subgroup.centralizer ({tp 3850 (hsCentTbl 21)} : Set (Equiv.Perm (Fin 3850)))).map
          (MulAut.conj g).toMonoidHom := by
      rw [hFmap, hC]
    exact hout (HasKComponent.of_mulEquiv (fixEquiv hFmap') ⟨B, hBc, hB⟩)
  ·
    exfalso
    obtain ⟨B, -, hB⟩ := hKcomp
    have hd : Nat.card ↥B ∣ 1920 := by
      rw [← h3, ← hFcard]
      exact Subgroup.card_subgroup_dvd_card B
    refine hB.false_of_dvd hd (by norm_num) (by norm_num) fun p hp h17 => ?_
    have e : 2 * 1920 = 2 ^ 8 * 3 ^ 1 * 5 ^ 1 := by norm_num
    rw [e]
    exact no_big_prime_dvd 8 1 1 p hp h17

end CFSG.QuasithinUnique.Id2519.SporHS
