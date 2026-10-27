module

public import CFSG.LocalAnalysis.GLTheoremA.Basic
public import CFSG.HardMathSupport.Solomon.LocalBalance.BarAut
public import CFSG.RankThree.PartTwo.Sec13.F135LastAct
public import CFSG.HardMathSupport.Solomon.LocalBalance.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barAut_mk)
open scoped commutatorElement

variable {Ω : Type} [Group Ω]

@[expose] noncomputable def simpleAct (p : ℕ) (S : Subgroup Ω) :
    ↥(Subgroup.normalizer (S : Set Ω)) →* MulAut (PSimple p S) :=
  (CFSG.RankThree.PartTwo.Sec13.F135Last.centerQuotMulAut (PQuot p S)).comp (barAut p S)

theorem mem_glaPPrimeCoreOf_iff' {p : ℕ} {S : Subgroup Ω} (x : ↥S) :
    (x : Ω) ∈ GLAPPrimeCoreOf p S ↔ x ∈ GLAPPrimeCore p ↥S :=
  ⟨fun ⟨c', hc', hv⟩ => by
    have : c' = x := Subtype.ext hv
    rwa [this] at hc', fun h => ⟨x, h, rfl⟩⟩

theorem barAut_eq_one_iff_mem_centMod {p : ℕ} {S : Subgroup Ω} {g : Ω}
    (hg : g ∈ Subgroup.normalizer (S : Set Ω)) :
    barAut p S ⟨g, hg⟩ = 1 ↔ g ∈ centModSubgroup p S := by
  constructor
  · intro h
    refine ⟨hg, fun l hl => ?_⟩
    have hl' : l⁻¹ ∈ S := S.inv_mem hl
    have h1 := congrArg (fun φ : MulAut (↥S ⧸ GLAPPrimeCore p ↥S) =>
      φ (QuotientGroup.mk ⟨l⁻¹, hl'⟩)) h
    simp only [MulAut.one_apply, barAut_mk] at h1
    have h2 := QuotientGroup.eq.1 h1.symm
    have hmem := (mem_glaPPrimeCoreOf_iff' (p := p) (S := S) _).2 h2
    have e : ⁅l, g⁆ = (((⟨l⁻¹, hl'⟩ : ↥S)⁻¹ *
        S.normalizerMonoidHom ⟨g, hg⟩ ⟨l⁻¹, hl'⟩ : ↥S) : Ω) := by
      show ⁅l, g⁆ = (l⁻¹)⁻¹ * (g * l⁻¹ * g⁻¹)
      rw [commutatorElement_def]
      group
    rw [e]
    exact hmem
  · intro h
    refine MulEquiv.ext fun q => ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    rw [barAut_mk, MulAut.one_apply]
    refine (QuotientGroup.eq.2 ?_).symm
    have hc := h.2 (y : Ω)⁻¹ (S.inv_mem y.2)
    have e : ⁅(y : Ω)⁻¹, g⁆ = ((y⁻¹ * S.normalizerMonoidHom ⟨g, hg⟩ y : ↥S) : Ω) := by
      show ⁅(y : Ω)⁻¹, g⁆ = (y : Ω)⁻¹ * (g * y * g⁻¹)
      rw [commutatorElement_def]
      group
    rw [e] at hc
    exact (mem_glaPPrimeCoreOf_iff' _).1 hc

theorem perfect_of_commutator_self_eq {S : Subgroup Ω} (hperf : ⁅S, S⁆ = S) :
    commutator ↥S = ⊤ := by
  apply Subgroup.map_injective S.subtype_injective
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
    hperf]

theorem automorphism_eq_one_of_center_quot {Q : Type*} [Group Q] (hQ : commutator Q = ⊤)
    (σ : MulAut Q) (h : ∀ x : Q, x * (σ x)⁻¹ ∈ Subgroup.center Q) : σ = 1 := by
  let c : Q →* ↥(Subgroup.center Q) :=
    { toFun := fun x => ⟨x * (σ x)⁻¹, h x⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        show x * y * (σ (x * y))⁻¹ = x * (σ x)⁻¹ * (y * (σ y)⁻¹)
        have hy := Subgroup.mem_center_iff.1 (h y) ((σ x)⁻¹)
        rw [map_mul, mul_inv_rev]
        calc x * y * ((σ y)⁻¹ * (σ x)⁻¹) = x * ((y * (σ y)⁻¹) * (σ x)⁻¹) := by group
          _ = x * ((σ x)⁻¹ * (y * (σ y)⁻¹)) := by rw [hy]
          _ = x * (σ x)⁻¹ * (y * (σ y)⁻¹) := by group }
  have hker : commutator Q ≤ c.ker :=
    Abelianization.commutator_subset_ker c
  refine MulEquiv.ext fun x => ?_
  have hx : x ∈ c.ker := hker (hQ ▸ Subgroup.mem_top x)
  rw [MonoidHom.mem_ker] at hx
  have hx' : x * (σ x)⁻¹ = 1 := congrArg Subtype.val hx
  rw [MulAut.one_apply]
  exact (mul_inv_eq_one.1 hx').symm

theorem simpleAct_eq_one_iff {p : ℕ} {S : Subgroup Ω} (hperf : ⁅S, S⁆ = S) {g : Ω}
    (hg : g ∈ Subgroup.normalizer (S : Set Ω)) :
    simpleAct p S ⟨g, hg⟩ = 1 ↔ g ∈ centModSubgroup p S := by
  rw [← barAut_eq_one_iff_mem_centMod hg]
  constructor
  · intro h
    have hQ : commutator (PQuot p S) = ⊤ := by
      have hS := perfect_of_commutator_self_eq hperf
      have h1 := Subgroup.map_commutator (⊤ : Subgroup ↥S) ⊤
        (QuotientGroup.mk' (GLAPPrimeCore p ↥S))
      rw [← commutator_def, hS, ← MonoidHom.range_eq_map,
        QuotientGroup.range_mk', ← commutator_def] at h1
      exact h1.symm
    refine automorphism_eq_one_of_center_quot hQ _ fun x => ?_
    have h1 := congrArg (fun φ : MulAut (PSimple p S) =>
      φ (QuotientGroup.mk x : PSimple p S)) h
    simp only [MulAut.one_apply] at h1
    have h2 : ((barAut p S ⟨g, hg⟩ x : PQuot p S) : PSimple p S) = (x : PSimple p S) := h1
    have h3 := QuotientGroup.eq.1 h2.symm
    have hw := (Subgroup.center (PQuot p S)).inv_mem h3
    have e1 : x * (barAut p S ⟨g, hg⟩ x)⁻¹ =
        x * (x⁻¹ * barAut p S ⟨g, hg⟩ x)⁻¹ * x⁻¹ := by group
    have e2 : x * (x⁻¹ * barAut p S ⟨g, hg⟩ x)⁻¹ * x⁻¹ = (x⁻¹ * barAut p S ⟨g, hg⟩ x)⁻¹ := by
      rw [Subgroup.mem_center_iff.1 hw x]
      group
    rw [e1, e2]
    exact hw
  · intro h
    show (CFSG.RankThree.PartTwo.Sec13.F135Last.centerQuotMulAut (PQuot p S))
      (barAut p S ⟨g, hg⟩) = 1
    rw [h, map_one]

variable [Finite Ω]

theorem card_le_card_inf_centMod_mul_pow {p : ℕ} (hp : p.Prime) {S B : Subgroup Ω} (hS : S.Normal)
    (hperf : ⁅S, S⁆ = S) (hB : IsElemAbelian p B) :
    Nat.card B ≤ Nat.card ↥(B ⊓ centModSubgroup p S) *
      p ^ CFSG.Open.pRank p (⊤ : Subgroup (MulAut (PSimple p S))) := by
  have hBN : B ≤ Subgroup.normalizer (S : Set Ω) := by
    rw [Subgroup.normalizer_eq_top_iff.2 hS]
    exact le_top
  let f : ↥B →* MulAut (PSimple p S) := (simpleAct p S).comp (Subgroup.inclusion hBN)
  have hker : f.ker = (centModSubgroup p S).subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact simpleAct_eq_one_iff hperf (hBN b.2)
  have hkcard : Nat.card f.ker = Nat.card ↥(B ⊓ centModSubgroup p S) := by
    rw [hker, ← Subgroup.card_map_of_injective (f := B.subtype) B.subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_comm]
  have hsplit : Nat.card B = Nat.card f.range * Nat.card f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  have hR : IsElemAbelian p f.range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
      obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 b.2
      apply Subtype.ext
      change (a : MulAut (PSimple p S)) * b = b * a
      rw [← hx, ← hz, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (congrArg Subtype.val (hB.1.is_comm.comm x z))
    · obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hy
      rw [← map_pow]
      have : x ^ p = 1 := Subtype.ext (hB.2 x x.2)
      rw [this, map_one]
  have hRp : IsPGroup p f.range := by
    haveI : Fact p.Prime := ⟨hp⟩
    refine fun g => ⟨1, ?_⟩
    rw [pow_one]
    exact Subtype.ext (by simpa using hR.2 g g.2)
  obtain ⟨j, hj⟩ := (haveI : Fact p.Prime := ⟨hp⟩; IsPGroup.iff_card.1 hRp)
  have hjle : j ≤ CFSG.Open.pRank p (⊤ : Subgroup (MulAut (PSimple p S))) :=
    CFSG.SectionRank.le_pRank hp.one_lt le_top hR hj
  rw [hsplit, hkcard, mul_comm, hj]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hp.pos hjle)

end CFSG.LocalAnalysis.GLTheoremA.S267
