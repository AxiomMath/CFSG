module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.StdSmallCore
public import CFSG.LocalAnalysis.GLTheoremA.S12.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

@[expose] def StdCovSchurAt : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X), CFSG.Open.IsQuasisimple ↥K → SmallType 3 K →
    Nat.card ↥(Subgroup.center ↥K) ∣ 6

@[expose] def StdCovListAt : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), CFSG.Open.IsQuasisimple ↥L →
    IsChevSimple 2 (PSimple 3 L) → Even (Nat.card ↥(Subgroup.center ↥L)) →
    (∃ E : Subgroup (MulAut ↥L), IsElemAbelian 3 E ∧ 3 ^ 3 ≤ Nat.card ↥E) →
    catalogIs (PSimple 3 L) S9.isList67

@[expose] def stdCovConj {G : Type} [Group G] (L : Subgroup G) (b : G)
    (hb : b ∈ Subgroup.normalizer (L : Set G)) : ↥L ≃* ↥L where
  toFun l := ⟨b * l * b⁻¹, (Subgroup.mem_normalizer_iff.1 hb l).1 l.2⟩
  invFun l := ⟨b⁻¹ * l * b⁻¹⁻¹, (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hb) l).1 l.2⟩
  left_inv l := by ext; simp [mul_assoc]
  right_inv l := by ext; simp [mul_assoc]
  map_mul' l m := by ext; simp [mul_assoc]

theorem stdCov_aut_rank {G : Type} [Group G] [Finite G] {B : Subgroup G} {x : G} {L : Subgroup G}
    (h : IsSStarMax 3 B x L) (hB3 : 3 ^ 4 ≤ Nat.card ↥B) :
    ∃ E : Subgroup (MulAut ↥L), IsElemAbelian 3 E ∧ 3 ^ 3 ≤ Nat.card ↥E := by
  have hess := IsSStarMax.essential h
  have hxB : x ∈ B := hess.1
  have hx1 : x ≠ 1 := hess.2.1
  have hBel : IsElemAbelian 3 B := (IsSStarMax.bmax h).1
  have hxp : x ^ 3 = 1 := hBel.2 x hxB
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := (IsSStarMax.component h).1
  have hnorm : B ≤ Subgroup.normalizer (L : Set G) := IsSStarMax.normalizes h
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let φ : ↥B →* MulAut ↥L :=
    { toFun := fun b => stdCovConj L (b : G) (hnorm b.2)
      map_one' := by ext l; simp [stdCovConj]
      map_mul' := fun a b => by ext l; simp [stdCovConj, mul_assoc] }
  have hsub : ∀ b ∈ φ.ker, (b : G) ∈ Subgroup.zpowers x := by
    intro b hb
    rw [MonoidHom.mem_ker] at hb
    have hcC : (b : G) ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have h1 : ((φ b) ⟨l, hl⟩ : ↥L) = ⟨l, hl⟩ := by rw [hb]; rfl
      have h2 : (b : G) * l * (b : G)⁻¹ = l := congrArg Subtype.val h1
      exact (mul_inv_eq_iff_eq_mul.1 h2).symm
    have hc3 : (b : G) ^ 3 = 1 := hBel.2 _ b.2
    have hcx : (b : G) * x = x * (b : G) :=
      congrArg Subtype.val (hBel.1.is_comm.comm (⟨(b : G), b.2⟩ : ↥B) ⟨x, hxB⟩)
    exact three_complement h hcC hc3 hcx
  have hker : Nat.card ↥φ.ker ≤ 3 := by
    have hinj : Function.Injective
        (fun c : ↥φ.ker => (⟨(c.1 : G), hsub c.1 c.2⟩ : ↥(Subgroup.zpowers x))) := by
      intro c d hcd
      have h := congrArg (fun w : ↥(Subgroup.zpowers x) => (w : G)) hcd
      exact Subtype.ext (Subtype.ext h)
    have hle := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_zpowers, orderOf_eq_prime hxp hx1] at hle
    exact hle
  have hE : IsElemAbelian 3 φ.range := by
    refine ⟨⟨⟨fun f g => ?_⟩⟩, ?_⟩
    · obtain ⟨f, hf⟩ := f
      obtain ⟨g, hg⟩ := g
      obtain ⟨b, rfl⟩ := MonoidHom.mem_range.1 hf
      obtain ⟨c, rfl⟩ := MonoidHom.mem_range.1 hg
      apply Subtype.ext
      have hbc : b * c = c * b := hBel.1.is_comm.comm b c
      show φ b * φ c = φ c * φ b
      rw [← map_mul, ← map_mul, hbc]
    · intro f hf
      obtain ⟨b, rfl⟩ := MonoidHom.mem_range.1 hf
      rw [← map_pow]
      have hb3 : b ^ 3 = 1 := Subtype.ext (by simpa using hBel.2 _ b.2)
      rw [hb3, map_one]
  refine ⟨φ.range, hE, ?_⟩
  have hcard := Subgroup.card_ker_mul_card_range φ
  have h1 : 3 ^ 4 ≤ Nat.card ↥φ.ker * Nat.card ↥φ.range := by
    rw [hcard]
    exact hB3
  have h2 : Nat.card ↥φ.ker * Nat.card ↥φ.range ≤ 3 * Nat.card ↥φ.range :=
    Nat.mul_le_mul_right _ hker
  have h3 : 3 * 3 ^ 3 ≤ 3 * Nat.card ↥φ.range := by
    have h4 : 3 * 3 ^ 3 = 3 ^ 4 := by norm_num
    rw [h4]
    exact le_trans h1 h2
  exact Nat.le_of_mul_le_mul_left h3 (by norm_num)

end CFSG.LocalAnalysis.GLTheoremA
