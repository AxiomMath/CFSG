module

public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.CoverBound
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.CoverPullback
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6Center
public import CFSG.LieType.Steinberg.CentralExt.F4TwoMultiplier
public import CFSG.Monster.B.E6.GStarStructure
public import CFSG.RankThree.PartOne.S11d.PerfectCentral
public import CFSG.Mathlib.GroupTheory.AutomorphismNormalFactors
public import CFSG.Mathlib.GroupTheory.CentralTwoKernel

public section

open Subgroup CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Chevalley.C2E6Std
  CFSG.EvenSmallLie.TwoE6

namespace CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover

theorem card_center_twistedE6Group : Nat.card (center (twistedE6Group 2 1)) = 3 := by
  have h := (TwistedE6Closed.card_center_fixedGroup (k := GaloisField 2 (2 * 1))
    (θ := frobQ 2 1) (q := 2) (by rw [GaloisField.card 2 (2 * 1) (by norm_num)])
    (fun c => by rw [frobQ_apply, pow_one])).1
  exact h

theorem odd_split (P : Type) [Group P] [Finite P] (η : P →* twistedE6Group 2 1)
    (hη : Function.Surjective η) (hc : η.ker ≤ center P) (hodd : Odd (Nat.card η.ker)) :
    ∃ σ : twistedE6Group 2 1 →* P, ∀ g, η (σ g) = g :=
  TwistedE6Closed.twistedE6_exists_section_of_coprime (k := GaloisField 2 (2 * 1))
    (θ := frobQ 2 1) (frobQ_frobQ 2 1 le_rfl) (p := 2) hη hc (Nat.coprime_two_left.2 hodd)


theorem ker_isogenyStd_eq_center : isogenyStd.ker = center (twistedE6Group 2 1) := by
  refine le_antisymm ker_isogenyStd_le_center fun z hz => ?_
  have h : isogenyStd z ∈ center stdGroup :=
    Subgroup.map_center_le_center isogenyStd_surjective ⟨z, hz, rfl⟩
  rw [CFSG.Monster.B.E6.center_stdGroup, mem_bot] at h
  exact MonoidHom.mem_ker.2 h

theorem card_ker_isogenyStd : Nat.card isogenyStd.ker = 3 := by
  rw [ker_isogenyStd_eq_center, card_center_twistedE6Group]

variable {E : Type} [Group E] [Finite E] [Group.IsPerfect E] {π : E →* stdGroup}

theorem derived_fibre_facts (hπ : Function.Surjective π) (hc : π.ker ≤ center E) :
    ∃ (D : Type) (_ : Group D) (_ : Finite D) (η : D →* twistedE6Group 2 1) (φ : D →* E),
      Function.Surjective η ∧ η.ker ≤ center D ∧ Nat.card η.ker ≤ 4 ∧
      (∀ c ∈ η.ker, c ^ 2 = 1) ∧ Function.Surjective φ ∧
      ∀ d, π (φ d) = isogenyStd (η d) := by
  have := isPerfect_twistedE6Group
  have := finite_twistedE6Group
  have hρ : Function.Surjective (fibreHom π) := fun u => by
    obtain ⟨x, hx⟩ := hπ (isogenyStd u)
    exact ⟨⟨(x, u), hx⟩, rfl⟩
  have hρc : (fibreHom π).ker ≤ center (fibre π) := by
    intro x hx
    have hc' : (x : E × twistedE6Group 2 1) ∈ center (E × twistedE6Group 2 1) := by
      rw [Subgroup.center_prod]
      refine ⟨hc (fst_mem_ker_of_mem_ker_fibreHom hx), ?_⟩
      rw [show (x : E × twistedE6Group 2 1).2 = 1 from hx]
      exact one_mem _
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (mem_center_iff.1 hc' y)
  obtain ⟨hDperf, hηs, hηc⟩ :=
    CFSG.RankThree.CentralLiftU.derived_restrict_facts (fibreHom π) hρ hρc
  have : Finite (fibre π) := finite_fibre
  have : Group.IsPerfect (commutator (fibre π)) := hDperf
  have h2 : IsPGroup 2 ((fibreHom π).comp (commutator (fibre π)).subtype).ker :=
    CFSG.LieType.Steinberg.CentralExt.F4Two.isPGroup_two_ker_of_odd_split odd_split _ hηs hηc
  have hmap : (commutator (fibre π)).map (fibreFst π) = ⊤ := by
    rw [commutator_def, map_commutator, ← MonoidHom.range_eq_map,
      (fibreFst π).range_eq_top.2 fibreFst_surjective, ← commutator_def,
      Group.IsPerfect.commutator_eq_top]
  have hφ : Function.Surjective ((fibreFst π).comp (commutator (fibre π)).subtype) := by
    intro e
    obtain ⟨d, hd, rfl⟩ : e ∈ (commutator (fibre π)).map (fibreFst π) := hmap ▸ mem_top e
    exact ⟨⟨d, hd⟩, rfl⟩
  refine ⟨commutator (fibre π), inferInstance, inferInstance,
    (fibreHom π).comp (commutator (fibre π)).subtype,
    (fibreFst π).comp (commutator (fibre π)).subtype, hηs, hηc,
    card_ker_le_four _ hηs hηc h2, fun c hc => sq_eq_one_of_mem_ker _ hηs hηc h2 hc, hφ,
    fun d => mem_fibre.1 (d : fibre π).2⟩

theorem pow_six_and_card_le (hπ : Function.Surjective π) (hc : π.ker ≤ center E) :
    (∀ m ∈ π.ker, m ^ 6 = 1) ∧ Nat.card π.ker ≤ 12 := by
  have := finite_twistedE6Group
  obtain ⟨D, _, _, η, φ, hηs, -, h4, hsq, hφ, hfib⟩ := derived_fibre_facts hπ hc
  obtain ⟨R, hRdef⟩ : ∃ R : Subgroup D, R = (isogenyStd.comp η).ker := ⟨_, rfl⟩
  have hmemR : ∀ d, d ∈ R ↔ isogenyStd (η d) = 1 := fun d => by
    rw [hRdef, MonoidHom.mem_ker, MonoidHom.comp_apply]
  have hR : ∀ m ∈ π.ker, ∃ d ∈ R, φ d = m := fun m hm => by
    obtain ⟨d, rfl⟩ := hφ m
    refine ⟨d, ?_, rfl⟩
    rw [hmemR, ← hfib]
    exact hm
  refine ⟨fun m hm => ?_, ?_⟩
  · obtain ⟨d, hd, rfl⟩ := hR m hm
    have h3 : (η d) ^ 3 = 1 := pow_three_eq_one_of_mem_ker_isogenyStd ((hmemR d).1 hd)
    have hd3 : d ^ 3 ∈ η.ker := by rw [MonoidHom.mem_ker, map_pow, h3]
    rw [← map_pow, show d ^ 6 = (d ^ 3) ^ 2 by group, hsq _ hd3, map_one]
  ·
    have hle : π.ker ≤ R.map φ := fun m hm => by
      obtain ⟨d, hd, hdm⟩ := hR m hm
      exact ⟨d, hd, hdm⟩
    have h1 : Nat.card π.ker ≤ Nat.card R :=
      (Subgroup.card_le_of_le hle).trans (Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd R φ))
    let ψ : R →* isogenyStd.ker :=
      (η.comp R.subtype).codRestrict isogenyStd.ker fun r => by
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype]
        exact (hmemR r).1 r.2
    have hψk : Nat.card ψ.ker ≤ Nat.card η.ker := by
      refine Nat.card_le_card_of_injective
        (fun r => (⟨((r : R) : D), ?_⟩ : η.ker)) fun r s hrs => ?_
      · have h := congrArg Subtype.val (MonoidHom.mem_ker.1 r.2)
        exact h
      · have h := congrArg (fun x : η.ker => (x : D)) hrs
        exact Subtype.ext (Subtype.ext h)
    have hψr : Nat.card ψ.range ≤ 3 := by
      rw [← card_ker_isogenyStd]
      exact Subgroup.card_le_card_group _
    have hcard : Nat.card R = Nat.card ψ.ker * Nat.card ψ.range := by
      rw [← Subgroup.index_ker, Subgroup.card_mul_index]
    calc Nat.card π.ker ≤ Nat.card R := h1
      _ = Nat.card ψ.ker * Nat.card ψ.range := hcard
      _ ≤ 4 * 3 := Nat.mul_le_mul (hψk.trans h4) hψr
      _ = 12 := by norm_num

open CFSG.GroupTheory

theorem exists_sc_map_mod_twoKernel (hπ : Function.Surjective π) (hc : π.ker ≤ center E) :
    ∃ μ : twistedE6Group 2 1 →* E ⧸ centralTwoKernel hc,
      Function.Surjective μ ∧ μ.ker ≤ center (twistedE6Group 2 1) ∧
      ∀ u, centralTwoQuotientMap hc (μ u) = isogenyStd u := by
  classical
  obtain ⟨D, _, _, η, φ, hη, -, -, hsq, hφ, hfib⟩ := derived_fibre_facts hπ hc
  have hZ : η.ker.map φ = centralTwoKernel hc := by
    ext z
    constructor
    · rintro ⟨d, hd, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [MonoidHom.mem_ker, hfib, MonoidHom.mem_ker.mp hd, map_one]
      · rw [← map_pow, hsq d hd, map_one]
    · intro hz
      obtain ⟨d, rfl⟩ := hφ z
      have hd : η d ∈ isogenyStd.ker := by
        rw [MonoidHom.mem_ker, ← hfib]
        exact hz.1
      have hd3 : d ^ 3 ∈ η.ker := by
        rw [MonoidHom.mem_ker, map_pow]
        exact pow_three_eq_one_of_mem_ker_isogenyStd hd
      refine ⟨d ^ 3, hd3, ?_⟩
      rw [map_pow, show 3 = 2 + 1 from rfl, pow_succ, hz.2, one_mul]
  let q := QuotientGroup.mk' (centralTwoKernel hc)
  have hkill : η.ker ≤ (q.comp φ).ker := by
    intro d hd
    change q (φ d) = 1
    exact (QuotientGroup.eq_one_iff _).mpr (hZ ▸ ⟨d, hd, rfl⟩)
  let μ := η.liftOfSurjective hη ⟨q.comp φ, hkill⟩
  have hμ : ∀ d, μ (η d) = q (φ d) := fun d =>
    MonoidHom.liftOfRightInverse_comp_apply η _
      (Function.rightInverse_surjInv hη) ⟨q.comp φ, hkill⟩ d
  have hs : Function.Surjective μ := by
    intro y
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (centralTwoKernel hc) y
    obtain ⟨d, rfl⟩ := hφ z
    exact ⟨η d, hμ d⟩
  have hcomp : ∀ u, centralTwoQuotientMap hc (μ u) = isogenyStd u := by
    intro u
    obtain ⟨d, rfl⟩ := hη u
    rw [hμ, centralTwoQuotientMap_mk, hfib]
  refine ⟨μ, hs, ?_, hcomp⟩
  intro u hu
  apply ker_isogenyStd_le_center
  rw [MonoidHom.mem_ker, ← hcomp, MonoidHom.mem_ker.mp hu, map_one]

theorem centralTwoQuotientMap_ker_cube_eq_one (hπ : Function.Surjective π)
    (hc : π.ker ≤ center E) {z : E ⧸ centralTwoKernel hc}
    (hz : z ∈ (centralTwoQuotientMap hc).ker) : z ^ 3 = 1 := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (centralTwoKernel hc) z
  have hx : x ∈ π.ker := hz
  have hx6 := (pow_six_and_card_le hπ hc).1 x hx
  rw [← map_pow]
  apply (QuotientGroup.eq_one_iff _).mpr
  refine ⟨π.ker.pow_mem hx 3, ?_⟩
  simpa only [← pow_mul, show 3 * 2 = 6 from rfl] using hx6

theorem centralTwoQuotientMap_ker_isPGroup_three (hπ : Function.Surjective π)
    (hc : π.ker ≤ center E) : IsPGroup 3 (centralTwoQuotientMap hc).ker := by
  intro z
  refine ⟨1, ?_⟩
  apply Subtype.ext
  simpa using centralTwoQuotientMap_ker_cube_eq_one hπ hc z.property

omit [Finite E] [Group.IsPerfect E]
  in
theorem sc_map_mod_twoKernel_equivariant (hc : π.ker ≤ center E)
    (μ : twistedE6Group 2 1 →* E ⧸ centralTwoKernel hc)
    (hμ : ∀ u, centralTwoQuotientMap hc (μ u) = isogenyStd u)
    (α : MulAut E) (δ : MulAut stdGroup)
    (hα : ∀ z, π (α z) = δ (π z))
    (β : MulAut (twistedE6Group 2 1))
    (hβ : ∀ u, isogenyStd (β u) = δ (isogenyStd u)) :
    ∀ u, CFSG.GroupTheory.MulAut.quotientNormal α (centralTwoKernel hc)
        (centralTwoKernel_map_eq hc α δ hα) (μ u) = μ (β u) := by
  let αq := CFSG.GroupTheory.MulAut.quotientNormal α (centralTwoKernel hc)
    (centralTwoKernel_map_eq hc α δ hα)
  have ha : ∀ q, centralTwoQuotientMap hc (αq q) = δ (centralTwoQuotientMap hc q) := by
    intro q
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (centralTwoKernel hc) q
    change centralTwoQuotientMap hc (αq (z : E ⧸ centralTwoKernel hc)) = δ (π z)
    rw [CFSG.GroupTheory.MulAut.quotientNormal_mk]
    exact hα z
  have heq := CFSG.RankThree.PartOne.hom_eq_of_div_central
    isPerfect_twistedE6Group (αq.toMonoidHom.comp μ) (μ.comp β.toMonoidHom) fun u => by
      apply centralTwoQuotientMap_ker_le_center hc
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      change centralTwoQuotientMap hc (αq (μ u)) * (centralTwoQuotientMap hc (μ (β u)))⁻¹ = 1
      rw [ha, hμ, hμ, hβ, mul_inv_cancel]
  exact fun u => DFunLike.congr_fun heq u

end CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover
