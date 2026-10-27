module

public import CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair.JRadical
public import CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair.SpanAll
public import CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair.EntryOdd
public import CFSG.RankThree.PartOne.SEITZ6.G2Big
public import CFSG.RankThree.PartOne.SEITZ2.G2Outer
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsG2Data

public section

namespace CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne CFSG.RankThree.PartOne.SEITZ3
  CFSG.RankThree.PartOne.SEITZ6 CFSG.RankThree.PartOne.SEITZ2

variable {K : Type} [Field K]

theorem wtRoot_long : ∀ τ ∈ longPos, wtRoot (rt τ) = 1 ∨ wtRoot (rt τ) = -1 := by
  decide +kernel

section Certs

variable (k : Subfield K) {R : Subgroup (adjointGroup .G2 K)}
  (hR : ∀ p < 12, ∀ c ∈ k, xp p c ∈ R)

include hR in
theorem longEntriesIn_of_hcon (g : adjointGroup .G2 K)
    (hcon : ∀ r ∈ R, ∀ r' ∈ R, coordAt (rt 10) ((r * g * r') • rootVec .G2 K (rt 7)) ∈ k) :
    ∀ r ∈ R, ∀ r' ∈ R, LongEntriesIn k (r * g * r') := by
  intro r hr r' hr' σ hσ τ hτ
  obtain ⟨mσ, hmσ, εσ, hεσ, hσ7⟩ := reach_longO k hR σ hσ
  obtain ⟨τ', hτ', hττ'⟩ := neg_long τ hτ
  obtain ⟨mτ, hmτ, ετ, hετ, hτ7⟩ := reach_longO k hR τ' hτ'
  have h1 := hcon (mτ⁻¹ * r) (R.mul_mem (R.inv_mem hmτ) hr) (r' * mσ) (R.mul_mem hr' hmσ)
  have hvσ : rootVec .G2 K (rt σ) = εσ • (mσ • rootVec .G2 K (rt 7)) := by
    rw [hσ7, smul_smul, sq_sign hεσ, one_smul]
  have hvτ : rootVec .G2 K (rt τ') = ετ • (mτ • rootVec .G2 K (rt 7)) := by
    rw [hτ7, smul_smul, sq_sign hετ, one_smul]
  have hz : (r * g * r') • rootVec .G2 K (rt σ) =
      εσ • ((r * g * r' * mσ) • rootVec .G2 K (rt 7)) := by
    rw [hvσ, smul_smul_comm, mul_smul (r * g * r') mσ]
  have hneg : rt τ' = -rt τ := hττ'
  have key : (wtRoot (rt τ) : K) * coordAt (rt τ) ((r * g * r') • rootVec .G2 K (rt σ)) =
      (ετ * (wtRoot (rt 10) : K) * εσ) *
        coordAt (rt 10) ((mτ⁻¹ * r * g * (r' * mσ)) • rootVec .G2 K (rt 7)) := by
    have s1 : (wtRoot (rt τ) : K) * coordAt (rt τ) ((r * g * r') • rootVec .G2 K (rt σ)) =
        jFormO K (rootVec .G2 K (rt τ')) ((r * g * r') • rootVec .G2 K (rt σ)) :=
      (jFormO_rootVec_left' hneg _).symm
    rw [s1, hvτ, LinearMap.map_smul₂, smul_eq_mul, jFormO_smul_left, hz,
      smul_smul_comm mτ⁻¹ εσ, ← mul_smul, jFormO_rootVec_left' neg_rt10.symm, coordAt_smul]
    have e : mτ⁻¹ * (r * g * r' * mσ) = mτ⁻¹ * r * g * (r' * mσ) := by group
    rw [e]
    ring
  have hw : (wtRoot (rt τ) : K) ≠ 0 := by
    rcases wtRoot_long τ hτ with h | h <;> rw [h] <;> simp
  have e : coordAt (rt τ) ((r * g * r') • rootVec .G2 K (rt σ)) =
      (wtRoot (rt τ) : K)⁻¹ * ((wtRoot (rt τ) : K) *
        coordAt (rt τ) ((r * g * r') • rootVec .G2 K (rt σ))) := (inv_mul_cancel_left₀ hw _).symm
  rw [e, key]
  have hpm : ∀ {ε : K}, (ε = 1 ∨ ε = -1) → ε ∈ k := fun {ε} h => by
    rcases h with rfl | rfl
    · exact k.one_mem
    · exact k.neg_mem k.one_mem
  exact k.mul_mem (k.inv_mem (intCast_mem k _))
    (k.mul_mem (k.mul_mem (k.mul_mem (hpm hετ) (intCast_mem k _)) (hpm hεσ)) h1)

include hR in
theorem jRat_of_long (h2 : (2 : K) ≠ 0) (g : adjointGroup .G2 K)
    (hlong : ∀ r ∈ R, ∀ r' ∈ R, LongEntriesIn k (r * g * r')) (a b : Label .G2) :
    jFormO K (Finsupp.single a 1) (g • (Finsupp.single b 1 : RootModule .G2 K)) ∈ k := by
  have hgen : ∀ r' ∈ R, ∀ β ∈ longPos, ∀ x ∈ Submodule.span k (longOrbit R),
      jFormO K x (g • (r' • rootVec .G2 K (rt β))) ∈ k := by
    intro r' hr' β hβ x hx
    refine jFormO_mem_of_span k (fun r hr σ hσ => ?_) hx
    rw [jFormO_smul_left, ← mul_smul, ← mul_smul]
    obtain ⟨σ', hσ', hσσ'⟩ := neg_long σ hσ
    have hneg : rt σ = -rt σ' := neg_eq_iff_eq_neg.1 hσσ'.symm
    rw [jFormO_rootVec_left' hneg]
    exact k.mul_mem (intCast_mem k _) (hlong r⁻¹ (R.inv_mem hr) r' hr' β hβ σ' hσ')
  have hall : ∀ y ∈ Submodule.span k (longOrbit R), ∀ x ∈ Submodule.span k (longOrbit R),
      jFormO K x (g • y) ∈ k := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨r', hr', β, hβ, rfl⟩ := hy
      exact fun x hx => hgen r' hr' β hβ x hx
    | zero => exact fun x _ => by simp [k.zero_mem]
    | add y z _ _ hy hz =>
      exact fun x hx => by
        rw [smul_add, map_add]
        exact k.add_mem (hy x hx) (hz x hx)
    | smul c y _ hy =>
      exact fun x hx => by
        have : c • y = (c : K) • y := rfl
        rw [this, smul_smul_comm g (c : K) y, map_smul]
        exact k.mul_mem c.2 (hy x hx)
  exact hall _ (single_mem_spanA k hR h2 b) _ (single_mem_spanA k hR h2 a)

theorem jFormO_mapRange (σ : K ≃+* K) (a : Label .G2) (y : RootModule .G2 K) :
    jFormO K (Finsupp.single a 1)
      (Finsupp.mapRange σ.toRingHom σ.toRingHom.map_zero y) =
      σ (jFormO K (Finsupp.single a 1) y) := by
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [Finsupp.mapRange_add (fun _ _ => map_add _ _ _), map_add, hx, hy, map_add, map_add]
  | single b r =>
    have e1 : ∀ t : K, jFormO K (Finsupp.single a 1) (Finsupp.single b t) = t * (jLabO a b : K) :=
      fun t => by
        rw [← Finsupp.smul_single_one b t, map_smul, jFormO_single, smul_eq_mul]
    rw [Finsupp.mapRange_single, e1, e1]
    simp

variable [Finite K]

theorem mem_g2Fixed_of_jRat (σ : K ≃+* K) (h2 : (2 : K) ≠ 0) (g : adjointGroup .G2 K)
    (hJ : ∀ a b : Label .G2, jFormO K (Finsupp.single a 1) (g • (Finsupp.single b 1 :
      RootModule .G2 K)) ∈ fixSubfield σ) : g ∈ g2Fixed σ := by
  set g' : adjointGroup .G2 K := CFSG.Quasithin.H13.Sec53F.G2.fieldAut K σ g with hg'
  have hg'v : ((g' : adjointGroup .G2 K) : ModGL .G2 K) =
      Units.map (entrywiseHom σ.toRingHom) (g : ModGL .G2 K) :=
    CFSG.Quasithin.H13.Sec53F.G2.fieldAut_apply σ g
  have hg'b : ∀ b : Label .G2, g' • (Finsupp.single b 1 : RootModule .G2 K) =
      Finsupp.mapRange σ.toRingHom σ.toRingHom.map_zero (g • (Finsupp.single b 1 :
        RootModule .G2 K)) := by
    intro b
    rw [smul_eq_end, hg'v, Units.coe_map]
    change entrywise σ.toRingHom _ (Finsupp.single b 1) = _
    rw [entrywise_single]
    rfl
  have hJeq : ∀ a b : Label .G2, jFormO K (Finsupp.single a 1)
      (g' • (Finsupp.single b 1 : RootModule .G2 K)) =
      jFormO K (Finsupp.single a 1) (g • (Finsupp.single b 1 : RootModule .G2 K)) := by
    intro a b
    rw [hg'b, jFormO_mapRange]
    exact (mem_fixSubfield σ).1 (hJ a b)
  have hall : ∀ x y : RootModule .G2 K, jFormO K x (g' • y) = jFormO K x (g • y) := by
    have key : (jFormO K).compl₂ ((g' : ModGL .G2 K) : Module.End K (RootModule .G2 K)) =
        (jFormO K).compl₂ ((g : ModGL .G2 K) : Module.End K (RootModule .G2 K)) := by
      refine LinearMap.ext_basis Finsupp.basisSingleOne Finsupp.basisSingleOne fun a b => ?_
      simp only [Finsupp.coe_basisSingleOne, LinearMap.compl₂_apply]
      exact hJeq a b
    exact fun x y => LinearMap.congr_fun₂ key x y
  have hmem : g⁻¹ * g' ∈ jTriv K := by
    intro x y
    rw [mul_smul, jFormO_smul_right, inv_inv, hall, jFormO_invariant]
  rw [jTriv_eq_bot h2, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  have hfix : Units.map (entrywiseHom σ.toRingHom) (g : ModGL .G2 K) = (g : ModGL .G2 K) := by
    rw [← hg'v, ← hmem]
  exact mem_rat_of_entrywise_fixed σ hfix

theorem rat_root_mem (σ : K ≃+* K) {p : ℕ} (hp : p < 12) {c : K} (hc : c ∈ fixSubfield σ) :
    xp p c ∈ g2Fixed σ :=
  mem_rat_of_entrywise_fixed σ (xp_entrywise_fixed σ hp ((mem_fixSubfield σ).1 hc))

theorem exists_bad_entryA (σ : K ≃+* K) (h2 : (2 : K) ≠ 0) (g : adjointGroup .G2 K)
    (hg : g ∉ g2Fixed σ) :
    ∃ r ∈ g2Fixed σ, ∃ r' ∈ g2Fixed σ,
      coordAt (rt 10) ((r * g * r') • rootVec .G2 K (rt 7)) ∉ fixSubfield σ := by
  by_contra hcon
  push Not at hcon
  have hR : ∀ p < 12, ∀ c ∈ fixSubfield σ, xp p c ∈ g2Fixed σ :=
    fun p hp c hc => rat_root_mem σ hp hc
  exact hg (mem_g2Fixed_of_jRat σ h2 g (jRat_of_long (fixSubfield σ) hR h2 g
    (longEntriesIn_of_hcon (fixSubfield σ) hR g hcon)))

end Certs

end CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair
