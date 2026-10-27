module

import CFSG.HardMathSupport.Timmesfeld.Proving.CommutingProduct
import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterInversion
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.BM

open CFSG.HardMathSupport.Timmesfeld.Proving CFSG.HardMathSupport.Timmesfeld.SporadicBalance

theorem pow_card_le_card_iSup_of_commuting {G : Type} [Group G] [Finite G] (m : ℕ)
    (S : Finset (Subgroup G))
    (hc : ∀ A ∈ S, ∀ B ∈ S, A ≠ B → ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hm : ∀ A ∈ S, m * Nat.card ↥(Subgroup.center ↥A) ≤ Nat.card ↥A) :
    m ^ S.card ≤ Nat.card ↥(⨆ A ∈ S, A) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert A S hA ih =>
    have hih := ih (fun A' hA' B hB => hc A' (Finset.mem_insert_of_mem hA') B
      (Finset.mem_insert_of_mem hB)) fun A' hA' => hm A' (Finset.mem_insert_of_mem hA')
    rw [Finset.card_insert_of_notMem hA, Finset.iSup_insert, pow_succ]
    set P : Subgroup G := ⨆ B ∈ S, B
    have hPA : ∀ a ∈ A, ∀ b ∈ P, a * b = b * a := by
      have hle : P ≤ Subgroup.centralizer (A : Set G) :=
        iSup₂_le fun B hB b hb => Subgroup.mem_centralizer_iff.2 fun a ha =>
          hc A (Finset.mem_insert_self A S) B (Finset.mem_insert_of_mem hB)
            (by rintro rfl; exact hA hB) a ha b hb
      exact fun a ha b hb => Subgroup.mem_centralizer_iff.1 (hle hb) a ha
    have hinf : Nat.card ↥(A ⊓ P) ≤ Nat.card ↥(Subgroup.center ↥A) :=
      Nat.card_le_card_of_injective
        (fun x => ⟨⟨x.1, (Subgroup.mem_inf.1 x.2).1⟩, Subgroup.mem_center_iff.2 fun g =>
          Subtype.ext (hPA g g.2 x.1 (Subgroup.mem_inf.1 x.2).2)⟩)
        fun x y hxy => Subtype.ext (congrArg (fun z : Subgroup.center ↥A => ((z : ↥A) : G)) hxy)
    have key : m * Nat.card ↥P * Nat.card ↥(A ⊓ P) ≤
        Nat.card ↥(A ⊔ P) * Nat.card ↥(A ⊓ P) := by
      rw [card_sup_mul_card_inf A P hPA]
      calc m * Nat.card ↥P * Nat.card ↥(A ⊓ P)
          = m * Nat.card ↥(A ⊓ P) * Nat.card ↥P := by ring
        _ ≤ m * Nat.card ↥(Subgroup.center ↥A) * Nat.card ↥P :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hinf)
        _ ≤ Nat.card ↥A * Nat.card ↥P :=
          Nat.mul_le_mul_right _ (hm A (Finset.mem_insert_self A S))
    calc m ^ S.card * m = m * m ^ S.card := mul_comm _ _
      _ ≤ m * Nat.card ↥P := Nat.mul_le_mul_left _ hih
      _ ≤ Nat.card ↥(A ⊔ P) := Nat.le_of_mul_le_mul_right key Nat.card_pos

theorem mem_map_conj_iff {G : Type} [Group G] {K : Subgroup G} {g y : G} :
    y ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ K := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem map_conj_mul {G : Type} [Group G] (K : Subgroup G) (g₁ g₂ : G) :
    K.map (MulAut.conj (g₁ * g₂)).toMonoidHom =
      (K.map (MulAut.conj g₂).toMonoidHom).map (MulAut.conj g₁).toMonoidHom := by
  ext y
  simp only [mem_map_conj_iff, mul_inv_rev, mul_assoc]

theorem map_conj_one {G : Type} [Group G] (K : Subgroup G) :
    K.map (MulAut.conj (1 : G)).toMonoidHom = K := by
  ext y
  simp only [mem_map_conj_iff, inv_one, one_mul, mul_one]

theorem card_map_conj {G : Type} [Group G] (K : Subgroup G) (g : G) :
    Nat.card ↥(K.map (MulAut.conj g).toMonoidHom) = Nat.card ↥K :=
  Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective

theorem card_center_map_conj {G : Type} [Group G] (K : Subgroup G) (g : G) :
    Nat.card ↥(Subgroup.center ↥(K.map (MulAut.conj g).toMonoidHom)) =
      Nat.card ↥(Subgroup.center ↥K) :=
  (Nat.card_congr (Subgroup.centerCongr (K.equivMapOfInjective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective)).toEquiv).symm

theorem simple_normalizes_of_commuting_conj {G : Type} [Group G] [Finite G] {H J : Subgroup G}
    (hH : IsSimpleGroup ↥H) (m : ℕ)
    (hcomm : ∀ g₁ ∈ H, ∀ g₂ ∈ H, J.map (MulAut.conj g₁).toMonoidHom ≠
      J.map (MulAut.conj g₂).toMonoidHom → ∀ a ∈ J.map (MulAut.conj g₁).toMonoidHom,
      ∀ b ∈ J.map (MulAut.conj g₂).toMonoidHom, a * b = b * a)
    (hJ : m * Nat.card ↥(Subgroup.center ↥J) ≤ Nat.card ↥J)
    (hk : ∀ k : ℕ, m ^ k ≤ Nat.card G → k.factorial < Nat.card ↥H) :
    ∀ h ∈ H, ∀ j ∈ J, h * j * h⁻¹ ∈ J := by
  classical
  haveI : Fintype ↥H := Fintype.ofFinite _
  obtain ⟨S, hS⟩ : ∃ S : Finset (Subgroup G),
      ∀ A, A ∈ S ↔ ∃ g : ↥H, J.map (MulAut.conj (g : G)).toMonoidHom = A :=
    ⟨Finset.univ.image fun g : ↥H => J.map (MulAut.conj (g : G)).toMonoidHom, fun A => by simp⟩
  have hfac : S.card.factorial < Nat.card ↥H := by
    refine hk _ ((pow_card_le_card_iSup_of_commuting m S ?_ ?_).trans
      (Subgroup.card_le_card_group _))
    · intro A hA B hB hne a ha b hb
      obtain ⟨g₁, rfl⟩ := (hS A).1 hA
      obtain ⟨g₂, rfl⟩ := (hS B).1 hB
      exact hcomm g₁ g₁.2 g₂ g₂.2 hne a ha b hb
    · intro A hA
      obtain ⟨g, rfl⟩ := (hS A).1 hA
      rw [card_map_conj, card_center_map_conj]
      exact hJ
  letI : MulAction ↥H ↥S :=
    { smul := fun h A => ⟨A.1.map (MulAut.conj (h : G)).toMonoidHom, by
        obtain ⟨g, hg⟩ := (hS A.1).1 A.2
        exact (hS _).2 ⟨h * g, by rw [← hg]; exact map_conj_mul J h g⟩⟩
      one_smul := fun A => Subtype.ext (map_conj_one A.1)
      mul_smul := fun h₁ h₂ A => Subtype.ext (map_conj_mul A.1 h₁ h₂) }
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hH (MulAction.toPermHom ↥H ↥S).ker _
    with hbot | htop
  · have hle := Nat.card_le_card_of_injective _ ((MonoidHom.ker_eq_bot_iff _).1 hbot)
    rw [Nat.card_perm, Nat.card_eq_finsetCard] at hle
    exact absurd hfac (not_lt.2 hle)
  · intro h hh j hj
    have hJS : J ∈ S := (hS J).2 ⟨1, map_conj_one J⟩
    have hker : (⟨h, hh⟩ : ↥H) ∈ (MulAction.toPermHom ↥H ↥S).ker := by
      rw [htop]
      exact Subgroup.mem_top _
    have hfix : MulAction.toPermHom ↥H ↥S ⟨h, hh⟩ ⟨J, hJS⟩ = ⟨J, hJS⟩ :=
      congrArg (fun σ : Equiv.Perm ↥S => σ ⟨J, hJS⟩) (MonoidHom.mem_ker.1 hker)
    have hJ' : J.map (MulAut.conj h).toMonoidHom = J := congrArg Subtype.val hfix
    have hmem : h * j * h⁻¹ ∈ J.map (MulAut.conj h).toMonoidHom := by
      rw [mem_map_conj_iff, show h⁻¹ * (h * j * h⁻¹) * h = j by group]
      exact hj
    rwa [hJ'] at hmem

theorem lemmaInv_core {G : Type} [Group G] [Finite G] {α s : G} (hα : α * α = 1)
    (hinv : α * s * α⁻¹ = s⁻¹) {H J : Subgroup G} (hH : IsSimpleGroup ↥H)
    (hHα : ∀ h ∈ H, α * h = h * α)
    (hHn : ∀ q : G, α * q = q * α → s * q = q * s → ∀ h ∈ H, q * h * q⁻¹ ∈ H)
    (hCQ : ∀ q : G, α * q = q * α → s * q = q * s → (∀ h ∈ H, q * h = h * q) → q = 1)
    (hJs : ∀ j ∈ J, s * j = j * s) (hHJ : ∀ h ∈ H, ∀ j ∈ J, h * j * h⁻¹ ∈ J)
    (hcomm : J.map (MulAut.conj α).toMonoidHom = J ∨
      ∀ a ∈ J, ∀ b ∈ J.map (MulAut.conj α).toMonoidHom, a * b = b * a)
    (hnab : ∃ a b : ↥J, a * b ≠ b * a) : Nat.card ↥H ∣ Nat.card ↥J ^ 2 := by
  have hdich : ∀ X : Subgroup G, (∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X) →
      H ≤ X ∨ ∀ x ∈ H, x ∈ X → x = 1 := by
    intro X hX
    have hN : (X.subgroupOf H).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using hX g g.2 n hn⟩
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hH _ hN with h | h
    · exact Or.inr fun x hx hxX =>
        Subgroup.disjoint_def.1 (Subgroup.subgroupOf_eq_bot.1 h) hxX hx
    · exact Or.inl (Subgroup.subgroupOf_eq_top.1 h)
  have hcent : ∀ X : Subgroup G, (∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X) →
      (∀ x ∈ H, x ∈ X → x = 1) → ∀ d ∈ X, α * d = d * α → s * d = d * s → d = 1 := by
    intro X hX hdis d hd hαd hsd
    refine hCQ d hαd hsd fun h hh => ?_
    have h1 : d * h * d⁻¹ * h⁻¹ ∈ H := H.mul_mem (hHn d hαd hsd h hh) (H.inv_mem hh)
    have h2 : d * h * d⁻¹ * h⁻¹ ∈ X := by
      rw [show d * h * d⁻¹ * h⁻¹ = d * (h * d⁻¹ * h⁻¹) by simp only [mul_assoc]]
      exact X.mul_mem hd (hX h hh _ (X.inv_mem hd))
    have h3 := hdis _ h1 h2
    rwa [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
  set J' := J.map (MulAut.conj α).toMonoidHom with hJ'
  have hmemJ' : ∀ y, y ∈ J' ↔ α⁻¹ * y * α ∈ J := fun y => mem_map_conj_iff
  have hαJ : ∀ j ∈ J, α * j * α⁻¹ ∈ J' := fun j hj => by
    rw [hmemJ', show α⁻¹ * (α * j * α⁻¹) * α = j by group]
    exact hj
  have hHJ' : ∀ h ∈ H, ∀ y ∈ J', h * y * h⁻¹ ∈ J' := fun h hh y hy => by
    rw [hmemJ'] at hy ⊢
    have c : Commute α h := hHα h hh
    have e : α⁻¹ * (h * y * h⁻¹) * α = h * (α⁻¹ * y * α) * h⁻¹ :=
      calc α⁻¹ * (h * y * h⁻¹) * α = α⁻¹ * h * y * (h⁻¹ * α) := by simp only [mul_assoc]
        _ = h * α⁻¹ * y * (α * h⁻¹) := by rw [c.inv_left.eq, ← c.inv_right.eq]
        _ = h * (α⁻¹ * y * α) * h⁻¹ := by simp only [mul_assoc]
    rw [e]
    exact hHJ h hh _ hy
  rcases hdich J hHJ with hle | hdisJ
  · exact (Subgroup.card_dvd_of_le hle).trans (dvd_pow_self _ two_ne_zero)
  by_cases hJJ : J' = J
  ·
    exfalso
    have hinvJ := inv_of_fixedPointFree_involution (Q := J) hα
      (fun q hq => by rw [← hJJ]; exact hαJ q hq)
      fun q hq hq' => hcent J hHJ hdisJ q hq (mul_inv_eq_iff_eq_mul.1 hq') (hJs q hq)
    obtain ⟨a, b, hab⟩ := hnab
    refine hab (Subtype.ext ?_)
    have e : ((a : G) * b)⁻¹ = (a : G)⁻¹ * (b : G)⁻¹ := by
      rw [← hinvJ _ (J.mul_mem a.2 b.2), ← hinvJ _ a.2, ← hinvJ _ b.2]
      group
    simpa using congrArg (·⁻¹) e
  · have hc : ∀ a ∈ J, ∀ b ∈ J', a * b = b * a := hcomm.resolve_left hJJ
    have hHK : ∀ h ∈ H, ∀ x ∈ J ⊔ J', h * x * h⁻¹ ∈ J ⊔ J' := by
      intro h hh x hx
      have hle : J ⊔ J' ≤ (J ⊔ J').comap (MulAut.conj h).toMonoidHom :=
        sup_le (fun y hy => Subgroup.mem_comap.2 (Subgroup.mem_sup_left (hHJ h hh y hy)))
          fun y hy => Subgroup.mem_comap.2 (Subgroup.mem_sup_right (hHJ' h hh y hy))
      exact hle hx
    rcases hdich (J ⊔ J') hHK with hle | hdisK
    · refine (Subgroup.card_dvd_of_le hle).trans ⟨Nat.card ↥(J ⊓ J'), ?_⟩
      rw [card_sup_mul_card_inf J J' hc, hJ', card_map_conj, sq]
    have hd : ∀ j ∈ J, α * j * α⁻¹ = j⁻¹ := by
      intro j hj
      have hjt : j * (α * j * α⁻¹) = α * j * α⁻¹ * j := hc j hj _ (hαJ j hj)
      have hαd : α * (j * (α * j * α⁻¹)) = j * (α * j * α⁻¹) * α := by
        refine mul_inv_eq_iff_eq_mul.1 ?_
        calc α * (j * (α * j * α⁻¹)) * α⁻¹ = α * j * α⁻¹ * (α * α * j * (α * α)⁻¹) := by
              group
          _ = j * (α * j * α⁻¹) := by rw [hα, inv_one, one_mul, mul_one, hjt]
      have hsj : Commute s j := hJs j hj
      have hst : Commute s (α * j * α⁻¹) := by
        have h1 := hsj.map (MulAut.conj α)
        rw [MulAut.conj_apply, MulAut.conj_apply, hinv] at h1
        exact Commute.inv_left_iff.1 h1
      exact eq_inv_of_mul_eq_one_right (hcent _ hHK hdisK _
        (mul_mem (Subgroup.mem_sup_left hj) (Subgroup.mem_sup_right (hαJ j hj))) hαd
        (hsj.mul_right hst))
    refine absurd (Subgroup.eq_of_le_of_card_ge (fun y hy => ?_) (card_map_conj J α).ge) hJJ
    rw [hmemJ'] at hy
    have h1 := hd _ hy
    rw [show α * (α⁻¹ * y * α) * α⁻¹ = y by group] at h1
    rw [h1]
    exact J.inv_mem hy

end CFSG.HardMathSupport.Dickson.Sec6.BM
