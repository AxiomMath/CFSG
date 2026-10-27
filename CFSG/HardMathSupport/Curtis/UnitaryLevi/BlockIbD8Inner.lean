module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbGeneric
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbDParab
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbD8Tits
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc.Glue
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusNodeGroup
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeAut
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbDOut

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.AGLEmbedding.ParabPrime (perfectJoin perfectJoin_le perfectJoin_perfect le_perfectJoin
  le_normalizer_perfectJoin)
open CFSG.AGLEmbedding.ToralCensus (eq_one_of_commute_of_perfect_cyclic mem_zpowers_of_commute_of_pow)
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc
open scoped commutatorElement

variable {Y : Type} [Group Y] [Finite Y] {Lb Pb D : Subgroup Y} {x : Y}

theorem mem_sup_centralizer_of_mem_normalizer (hCP : CompParabE Lb Pb) {u : Y}
    (hu : u ∈ Lb ⊔ Subgroup.centralizer (Lb : Set Y))
    (huP : u ∈ Subgroup.normalizer (Pb : Set Y)) :
    u ∈ Pb ⊔ Subgroup.centralizer (Lb : Set Y) := by
  have hPL : Pb ≤ Lb := hCP.parab.1
  have hcomm : ∀ a ∈ Lb, ∀ b ∈ Subgroup.centralizer (Lb : Set Y), a * b = b * a :=
    fun a ha b hb => Subgroup.mem_centralizer_iff.1 hb a ha
  obtain ⟨l, hl, c, hc, rfl⟩ := exists_mul_of_mem_sup_commute hcomm hu
  have hlP : l ∈ Subgroup.normalizer (Pb : Set Y) := by
    apply Subgroup.mem_normalizer_fintype
    intro g hg
    have hcg : g * c = c * g := Subgroup.mem_centralizer_iff.1 hc g (hPL hg)
    have h1 := (Subgroup.mem_normalizer_iff.1 huP g).1 hg
    have e : l * c * g * (l * c)⁻¹ = l * g * l⁻¹ := by
      calc l * c * g * (l * c)⁻¹ = l * (c * g) * c⁻¹ * l⁻¹ := by group
        _ = l * (g * c) * c⁻¹ * l⁻¹ := by rw [hcg]
        _ = l * g * l⁻¹ := by group
    rw [e] at h1
    exact h1
  exact Subgroup.mul_mem_sup (mem_of_mem_normalizer_of_isParabolicTwo_d hCP.parab hl hlP) hc

theorem inner_part_trivial_d8 (hP : BlockIbParab Lb Pb) (hD : BlockIbData Lb Pb D x)
    (hT : IsClassicalTwoOrG2 (↥Lb ⧸ Subgroup.center ↥Lb))
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥Lb ⧸ Subgroup.center ↥Lb) .POmegaPlus 4 2 1)
    {U : Subgroup Y} (hUP : U ≤ Subgroup.normalizer (Pb : Set Y))
    (hUD : U ≤ Subgroup.centralizer (D : Set Y)) (hU3 : IsPGroup 3 U) :
    ∀ u ∈ U, u ∈ Lb ⊔ Subgroup.centralizer (Lb : Set Y) → u ∈ Subgroup.centralizer (Lb : Set Y) := by
  intro u hu hulc
  have hCP : CompParabE Lb Pb := CompParab.toE (compParab_of_blockIb hP hD hT)
  obtain ⟨ρ, hρker, hρJ, v₀, hv₀⟩ := exists_centCycBar hCP Nat.prime_three hD.Dperf hD.Dle
    hD.Dcyc hD.Dcarry hD.hx hD.hx3 hD.hxC hD.free
  obtain ⟨S₀, hS₀, -⟩ := hv₀.parab
  have huPC : u ∈ Pb ⊔ Subgroup.centralizer (Lb : Set Y) :=
    mem_sup_centralizer_of_mem_normalizer hCP hulc (hUP hu)
  set D' : Subgroup ↥(Pb ⊔ Subgroup.centralizer (Lb : Set Y)) := D.subgroupOf (Pb ⊔ Subgroup.centralizer (Lb : Set Y)) with hD'
  set Dh : Subgroup (↥Lb ⧸ Subgroup.center ↥Lb) := D'.map ρ with hDh
  have hD'map : D'.map (Pb ⊔ Subgroup.centralizer (Lb : Set Y)).subtype = D := Subgroup.map_subgroupOf_eq_of_le hD.Dle
  have hD'perf : ⁅D', D'⁆ = D' := by
    apply Subgroup.map_injective (Pb ⊔ Subgroup.centralizer (Lb : Set Y)).subtype_injective
    rw [Subgroup.map_commutator, hD'map, hD.Dperf]
  have hDhperf : ⁅Dh, Dh⁆ = Dh := by
    rw [hDh, ← Subgroup.map_commutator, hD'perf]
  have hDhJ : Dh ≤ jBar Lb Pb := by
    rintro _ ⟨g, -, rfl⟩
    exact hρJ g
  have hxM : x ∈ Pb ⊔ Subgroup.centralizer (Lb : Set Y) := hD.Dle hD.hx
  set xM : ↥(Pb ⊔ Subgroup.centralizer (Lb : Set Y)) := ⟨x, hxM⟩ with hxMdef
  set v : ↥Lb ⧸ Subgroup.center ↥Lb := ρ xM with hv
  have hvDh : v ∈ Dh := ⟨xM, Subgroup.mem_subgroupOf.2 hD.hx, rfl⟩
  have hv3 : v ^ 3 = 1 := by
    rw [hv, ← map_pow]
    have : xM ^ 3 = 1 := Subtype.ext hD.hx3
    rw [this, map_one]
  have hv1 : v ≠ 1 := fun h1 => hD.hxC ((hρker xM).1 h1)
  have hordv : orderOf v = 3 := orderOf_eq_prime hv3 hv1
  have hvK : v ∈ perfectJoin (jBar Lb Pb) := le_perfectJoin hDhJ hDhperf hvDh
  have hK : perfectJoin (jBar Lb Pb) ≠ ⊥ := fun h => hv1 (by
    have := hvK
    rw [h, Subgroup.mem_bot] at this
    exact this)
  have h3 := three_mem_perfectJoin_of_model_d8 hmodel S₀ (jBar Lb Pb) hS₀ hK
  set uM : ↥(Pb ⊔ Subgroup.centralizer (Lb : Set Y)) := ⟨u, huPC⟩ with huMdef
  set y : ↥Lb ⧸ Subgroup.center ↥Lb := ρ uM with hy
  obtain ⟨k, hk⟩ := hU3 ⟨u, hu⟩
  have hyk : y ^ 3 ^ k = 1 := by
    rw [hy, ← map_pow]
    have : uM ^ 3 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [this, map_one]
  have hyK : y ∈ perfectJoin (jBar Lb Pb) := h3 y (hρJ uM) ⟨k, hyk⟩
  have hycomm : ∀ a ∈ Dh, a * y = y * a := by
    rintro _ ⟨d, hd, rfl⟩
    have hdD : (d : Y) ∈ D := Subgroup.mem_subgroupOf.1 hd
    have h1 : (d : Y) * u = u * d := Subgroup.mem_centralizer_iff.1 (hUD hu) d hdD
    rw [hy, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext h1
  by_contra hyne
  have hy1 : y ≠ 1 := fun h1 => hyne ((hρker uM).1 h1)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hyk)
  have hj1 : j ≠ 0 := by
    rintro rfl
    exact hy1 (orderOf_eq_one_iff.1 (by simpa using hj))
  have h3dvd : 3 ∣ orderOf y := by
    rw [hj]
    exact dvd_pow_self 3 hj1
  have hord0 : orderOf y ≠ 0 := by rw [hj]; positivity
  set y' := y ^ (orderOf y / 3) with hy'
  have hy'ord : orderOf y' = 3 := orderOf_pow_orderOf_div hord0 h3dvd
  have hy'3 : y' ^ 3 = 1 := by rw [← hy'ord]; exact pow_orderOf_eq_one y'
  have hy'K : y' ∈ perfectJoin (jBar Lb Pb) := Subgroup.pow_mem _ hyK _
  have hcycK : ∀ Q : Subgroup (↥Lb ⧸ Subgroup.center ↥Lb), Q ≤ perfectJoin (jBar Lb Pb) →
      IsPGroup 3 Q → IsCyclic Q := fun Q hQ hQp =>
    hv₀.cyc (perfectJoin (jBar Lb Pb)) (perfectJoin_le _) (perfectJoin_perfect _) Q hQ hQp
  have hy'v : Commute y' v := by
    have : Commute y v := (hycomm v hvDh).symm
    exact this.pow_left _
  have hy'zp : y' ∈ Subgroup.zpowers v :=
    mem_zpowers_of_commute_of_pow hcycK hy'K hvK hy'v hy'3 hordv
  have hy'Dh : y' ∈ Dh := (Subgroup.zpowers_le.2 hvDh) hy'zp
  have hcycD : ∀ Q : Subgroup (↥Lb ⧸ Subgroup.center ↥Lb), Q ≤ Dh → IsPGroup 3 Q → IsCyclic Q :=
    fun Q hQ hQp => hv₀.cyc Dh hDhJ hDhperf Q hQ hQp
  have hy'c : ∀ a ∈ Dh, a * y' = y' * a := fun a ha => (Commute.pow_right (hycomm a ha : Commute a y) _).eq
  have := eq_one_of_commute_of_perfect_cyclic Nat.prime_three hDhperf hcycD hy'Dh hy'c hy'3
  rw [this, orderOf_one] at hy'ord
  omega

theorem not_nine_dvd_card_outer_d8 (hP : BlockIbParab Lb Pb)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥Lb ⧸ Subgroup.center ↥Lb)
      .POmegaPlus 4 2 1) :
    ¬ 9 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥Lb) := by
  have : Group.IsPerfect ↥Lb := Group.isPerfect_def.mpr hP.comp.2.2.1
  have h1 := card_outer_dvd_card_outer_centerQuotient ↥Lb
  have h2 := CFSG.EvenSmallLie.OmegaEight.card_outer_le_six hmodel
  have h3 : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥Lb) ≤ 6 :=
    (Nat.le_of_dvd (Nat.card_pos) h1).trans h2
  intro h9
  have := Nat.le_of_dvd Nat.card_pos h9
  omega

theorem hBA_d8 (hP : BlockIbParab Lb Pb) (hD : BlockIbData Lb Pb D x)
    (hT : IsClassicalTwoOrG2 (↥Lb ⧸ Subgroup.center ↥Lb))
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥Lb ⧸ Subgroup.center ↥Lb)
      .POmegaPlus 4 2 1)
    {U : Subgroup Y} (hUL : U ≤ Subgroup.normalizer (Lb : Set Y))
    (hUP : U ≤ Subgroup.normalizer (Pb : Set Y)) (hUD : U ≤ Subgroup.centralizer (D : Set Y))
    (hU3 : IsPGroup 3 U) :
    ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.centralizer (Lb : Set Y) := by
  intro a ha b hb
  obtain ⟨h1, -⟩ := three_pgroup_normalizer_out hUL hU3 (not_nine_dvd_card_outer_d8 hP hmodel)
  exact inner_part_trivial_d8 hP hD hT hmodel hUP hUD hU3 _
    (U.mul_mem (U.mul_mem (U.mul_mem ha hb) (U.inv_mem ha)) (U.inv_mem hb)) (h1 a ha b hb)

theorem hBR_d8 (hP : BlockIbParab Lb Pb) (hD : BlockIbData Lb Pb D x)
    (hT : IsClassicalTwoOrG2 (↥Lb ⧸ Subgroup.center ↥Lb))
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥Lb ⧸ Subgroup.center ↥Lb)
      .POmegaPlus 4 2 1)
    {E : Subgroup Y} (hEL : E ≤ Subgroup.normalizer (Lb : Set Y))
    (hEP : E ≤ Subgroup.normalizer (Pb : Set Y)) (hED : E ≤ Subgroup.centralizer (D : Set Y))
    (hE9 : Nat.card E = 3 ^ 2) :
    E ⊓ Subgroup.centralizer (Lb : Set Y) ≠ ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE3 : IsPGroup 3 E := IsPGroup.of_card hE9
  obtain ⟨-, h2⟩ := three_pgroup_normalizer_out hEL hE3 (not_nine_dvd_card_outer_d8 hP hmodel)
  have hle : E ⊓ (Lb ⊔ Subgroup.centralizer (Lb : Set Y)) ≤
      E ⊓ Subgroup.centralizer (Lb : Set Y) := fun u hu =>
    ⟨hu.1, inner_part_trivial_d8 hP hD hT hmodel hEP hED hE3 u hu.1 hu.2⟩
  intro hbot
  have hcard : Nat.card ↥(E ⊓ (Lb ⊔ Subgroup.centralizer (Lb : Set Y))) ≤ 1 := by
    have := Subgroup.card_le_of_le hle
    rw [hbot] at this
    simpa using this
  rw [hE9] at h2
  omega

end CFSG.HardMathSupport.Curtis.UnitaryLevi
