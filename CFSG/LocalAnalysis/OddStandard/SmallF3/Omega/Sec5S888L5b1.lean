module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888L5a3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888EA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888Stmts

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r : G}
  {B A K₁ K₂ : Subgroup G} {h : G}

private theorem s888L5b1_le_normalizer (h514 : Asc82Lemma514) (h52a : Asc82Lemma52a)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h) {U : Subgroup G}
    (hU : U ≤ normalizer (Qsub K₁ K₂ h : Set G) ⊓ centralizer ({t} : Set G)) :
    U ≤ normalizer (L : Set G) ⊓ normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) := by
  intro y hy
  have hyN : y ∈ normalizer (Qsub K₁ K₂ h : Set G) := (hU hy).1
  have hyt : y ∈ centralizer ({t} : Set G) := (hU hy).2
  have hyz : y ∈ centralizer ({z} : Set G) := sec5b517_normalizer_le h514 c hyN
  exact ⟨mem_normalizer_of_conjugate_eq (sec5_conj_L h52a c hyt),
    mem_normalizer_of_conjugate_eq (sec5_conj_K12 h52a c hyt hyz)⟩

private theorem s888L5b1_elemAbelianModC6 (h514 : Asc82Lemma514) (h516a : Asc82Lemma516a)
    (h52a : Asc82Lemma52a) (hF3 : Asc82FactOm6CentD)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h) {U : Subgroup G}
    (hU : U ≤ normalizer (Qsub K₁ K₂ h : Set G) ⊓ centralizer ({t} : Set G))
    (hab : IsElemAbelianModSub
      (centralizerMod z (normalizer (Qsub K₁ K₂ h : Set G)) (Qsub K₁ K₂ h)) U) :
    IsElemAbelianModSub (Sec5C6 L K₁ K₂) U := by
  intro a ha b hb
  have hC6 := centralizerMod_inf_centralizer_le_C6 h514 h516a h52a hF3 c
  have hat : a ∈ centralizer ({t} : Set G) := (hU ha).2
  have hbt : b ∈ centralizer ({t} : Set G) := (hU hb).2
  have hat' : a⁻¹ ∈ centralizer ({t} : Set G) := inv_mem hat
  have hbt' : b⁻¹ ∈ centralizer ({t} : Set G) := inv_mem hbt
  obtain ⟨hcomm, hsq⟩ := hab a ha b hb
  have hcomm' : a * b * a⁻¹ * b⁻¹ ∈ centralizer ({t} : Set G) :=
    mul_mem (mul_mem (mul_mem hat hbt) hat') hbt'
  exact ⟨hC6 ⟨hcomm, hcomm'⟩, hC6 ⟨hsq, mul_mem hat hat⟩⟩

theorem relIndex_C6_le_four (h514 : Asc82Lemma514) (h516a : Asc82Lemma516a)
    (h52a : Asc82Lemma52a) (hF3 : Asc82FactOm6CentD) (hF6 : Asc82FactOm6NRank)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h) {U : Subgroup G}
    (hU : U ≤ normalizer (Qsub K₁ K₂ h : Set G) ⊓ centralizer ({t} : Set G))
    (hab : IsElemAbelianModSub
      (centralizerMod z (normalizer (Qsub K₁ K₂ h : Set G)) (Qsub K₁ K₂ h)) U) :
    (Sec5C6 L K₁ K₂).relIndex U ≤ 4 := by
  have hULE := s888L5b1_le_normalizer h514 h52a c hU
  have hC6 := s888L5b1_elemAbelianModC6 h514 h516a h52a hF3 c hU hab
  obtain ⟨m, hm⟩ := relIndex_eq_two_pow_of_elemAb hC6
  have hle := hF6 G L z K₁ K₂ c.toSec5Setting.isOm6Z2 (sec5b517_oddCore_bot c) c.pocket.1
    c.pocket₁ c.pocket₂ c.ne c.comm c.prod m U hULE hC6 hm
  rw [hm]
  calc 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hle
    _ = 4 := by norm_num

end CFSG.OddStandard.SmallF3.Omega
