module

public import CFSG.CGT.Foote82.T66.Basic
public import CFSG.HardMathSupport.Cooperstein.Coordinator.NaturalBridgeHeart
import CFSG.CGT.Foote82.Lemma62Tools
import CFSG.Quasithin.Background.G11Basic

public section

namespace CFSG.CGT.Foote82

namespace CaseIHeart

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo CFSG.QuasithinUnique
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open CFSG.HardMathSupport.Cooperstein.Coordinator
open Equiv Equiv.Perm

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

structure HeartFor (X : Subgroup (GLV V)) (N : ℕ) (ρ : ↥X →* Perm (Fin N))
    (X' : Subgroup (GLV V)) (β : ↥(commSpace X' ⊤) →+ altHeart N) : Prop where
  le : X' ≤ X
  mem_iff : ∀ x : ↥X, (x : GLV V) ∈ X' ↔ ρ x ∈ alternatingGroup (Fin N)
  surj : Function.Surjective β
  ker : β.ker = ((fixedSpace X').comap (commSpace X' ⊤).subtype).toAddSubgroup
  equiv : ∀ (x : ↥X) (w w' : ↥(commSpace X' ⊤)), (w' : V) = (x : GLV V) (w : V) →
    ∀ y : evenWeight N, β w = (y : altHeart N) → β w' = (evenWeightPerm (ρ x) y : altHeart N)

variable {X X' : Subgroup (GLV V)} {N : ℕ} {ρ : ↥X →* Perm (Fin N)}
  {β : ↥(commSpace X' ⊤) →+ altHeart N}

theorem commSpace_inf_fixedSpace_eq_bot {c : GLV V} (hc : Odd (orderOf c)) :
    fixedSpace (Subgroup.zpowers c) ⊓ commSpace (Subgroup.zpowers c) ⊤ = ⊥ :=
  (isCompl_fixedSpace_commSpace (by rwa [Nat.card_zpowers])).inf_eq_bot

theorem exists_fixed_add_comm {c : GLV V} (hc : Odd (orderOf c)) (v : V) :
    ∃ v₀ v₁, c v₀ = v₀ ∧ v₁ ∈ commSpace (Subgroup.zpowers c) ⊤ ∧ v = v₀ + v₁ := by
  have h := (isCompl_fixedSpace_commSpace (K := Subgroup.zpowers c)
    (by rwa [Nat.card_zpowers])).sup_eq_top
  have hv : v ∈ fixedSpace (Subgroup.zpowers c) ⊔ commSpace (Subgroup.zpowers c) ⊤ := by
    rw [h]; exact Submodule.mem_top
  obtain ⟨v₀, hv₀, v₁, hv₁, rfl⟩ := Submodule.mem_sup.1 hv
  exact ⟨v₀, v₁, hv₀ c (Subgroup.mem_zpowers c), hv₁, rfl⟩

theorem eq_of_supp_three {p q r : Fin N} (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r)
    (x : Fin N → ZMod 2) (hsum : ∑ i, x i = 0) (hsupp : ∀ i, i ≠ p → i ≠ q → i ≠ r → x i = 0) :
    x = 0 ∨ x = (pairEW p q : Fin N → ZMod 2) ∨ x = (pairEW q r : Fin N → ZMod 2) ∨
      x = (pairEW p r : Fin N → ZMod 2) := by
  have hsum' : x p + x q + x r = 0 := by
    rw [← hsum, ← Finset.sum_subset (Finset.subset_univ {p, q, r})
      (fun i _ hi => by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
        exact hsupp i hi.1 hi.2.1 hi.2.2)]
    rw [Finset.sum_insert (by simp [hpq, hpr]), Finset.sum_insert (by simp [hqr]),
      Finset.sum_singleton, add_assoc]
  have key : ∀ i, x i = (if i = p then x p else 0) + (if i = q then x q else 0) +
      (if i = r then x r else 0) := by
    intro i
    by_cases hip : i = p
    · subst hip; simp [hpq, hpr]
    by_cases hiq : i = q
    · subst hiq; simp [hip, hqr]
    by_cases hir : i = r
    · subst hir; simp [hip, hiq]
    · simp [hip, hiq, hir, hsupp i hip hiq hir]
  have hcases : ∀ a b c : ZMod 2, a + b + c = 0 →
      (a = 0 ∧ b = 0 ∧ c = 0) ∨ (a = 1 ∧ b = 1 ∧ c = 0) ∨ (a = 0 ∧ b = 1 ∧ c = 1) ∨
        (a = 1 ∧ b = 0 ∧ c = 1) := by decide
  rcases hcases _ _ _ hsum' with ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩
  · left
    funext i
    rw [key i, ha, hb, hc]
    simp
  · right; left
    funext i
    rw [key i, ha, hb, hc, pairEW_apply]
    by_cases hir : i = r
    · subst hir; simp [Ne.symm hpr, Ne.symm hqr]
    · simp [hir]
  · right; right; left
    funext i
    rw [key i, ha, hb, hc, pairEW_apply]
    by_cases hip : i = p
    · subst hip; simp [hpq, hpr]
    · simp [hip]
  · right; right; right
    funext i
    rw [key i, ha, hb, hc, pairEW_apply]
    by_cases hiq : i = q
    · subst hiq; simp [Ne.symm hpq, hqr]
    · simp [hiq]

theorem sum_evenWeight (y : evenWeight N) : ∑ i, (y : Fin N → ZMod 2) i = 0 := by
  have := y.2
  simp only [evenWeight, AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply] at this
  exact this

theorem sub_supp (τ : Perm (Fin N)) (y : evenWeight N) (i : Fin N) (hi : τ⁻¹ i = i) :
    ((evenWeightPerm τ y - y : evenWeight N) : Fin N → ZMod 2) i = 0 := by
  show (y : Fin N → ZMod 2) (τ⁻¹ i) - (y : Fin N → ZMod 2) i = 0
  rw [hi, sub_self]

theorem commSpace_zpowers_le {c : GLV V} (hcX' : c ∈ X') :
    commSpace (Subgroup.zpowers c) ⊤ ≤ commSpace X' ⊤ :=
  commSpace_mono (Subgroup.zpowers_le.2 hcX') le_rfl

theorem injOn (hH : HeartFor X N ρ X' β) {c : GLV V} (hcX' : c ∈ X') (hodd : Odd (orderOf c))
    {w : ↥(commSpace X' ⊤)} (hw : (w : V) ∈ commSpace (Subgroup.zpowers c) ⊤) (h0 : β w = 0) :
    (w : V) = 0 := by
  have hker : w ∈ β.ker := h0
  rw [hH.ker] at hker
  have hfix : (w : V) ∈ fixedSpace X' := hker
  have hfixc : (w : V) ∈ fixedSpace (Subgroup.zpowers c) := fun k hk =>
    hfix k (Subgroup.zpowers_le.2 hcX' hk)
  have := commSpace_inf_fixedSpace_eq_bot hodd
  have hmem : (w : V) ∈ fixedSpace (Subgroup.zpowers c) ⊓ commSpace (Subgroup.zpowers c) ⊤ :=
    ⟨hfixc, hw⟩
  rw [this] at hmem
  exact (Submodule.mem_bot _).1 hmem

theorem image_le (hH : HeartFor X N ρ X' β) {c : GLV V} (hcX : c ∈ X) (hcX' : c ∈ X')
    (hodd : Odd (orderOf c)) (T : AddSubgroup (altHeart N))
    (hT : ∀ (k : ℤ) (y : evenWeight N),
      ((evenWeightPerm (ρ ⟨c, hcX⟩ ^ k) y - y : evenWeight N) : altHeart N) ∈ T)
    {w : ↥(commSpace X' ⊤)} (hw : (w : V) ∈ commSpace (Subgroup.zpowers c) ⊤) : β w ∈ T := by
  let Wsub : Submodule (ZMod 2) V :=
    { carrier := {v | ∃ hv : v ∈ commSpace X' ⊤, β ⟨v, hv⟩ ∈ T}
      add_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨(commSpace X' ⊤).add_mem ha hb, ?_⟩
        have : (⟨a + b, (commSpace X' ⊤).add_mem ha hb⟩ : ↥(commSpace X' ⊤)) =
          ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
        rw [this, map_add]
        exact T.add_mem ha' hb'
      zero_mem' := ⟨(commSpace X' ⊤).zero_mem, by
        have : (⟨0, (commSpace X' ⊤).zero_mem⟩ : ↥(commSpace X' ⊤)) = 0 := rfl
        rw [this, map_zero]; exact T.zero_mem⟩
      smul_mem' := by
        rintro a v ⟨hv, hv'⟩
        refine ⟨(commSpace X' ⊤).smul_mem a hv, ?_⟩
        rcases (show a = 0 ∨ a = 1 by revert a; decide) with rfl | rfl
        · have : (⟨(0 : ZMod 2) • v, (commSpace X' ⊤).smul_mem 0 hv⟩ : ↥(commSpace X' ⊤)) = 0 :=
            Subtype.ext (zero_smul _ v)
          rw [this, map_zero]; exact T.zero_mem
        · have : (⟨(1 : ZMod 2) • v, (commSpace X' ⊤).smul_mem 1 hv⟩ : ↥(commSpace X' ⊤)) =
              ⟨v, hv⟩ := Subtype.ext (one_smul _ v)
          rw [this]; exact hv' }
  have hle : commSpace (Subgroup.zpowers c) ⊤ ≤ Wsub := by
    refine commSpace_le_iff.2 fun k hk v _ => ?_
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    obtain ⟨v₀, v₁, hv₀, hv₁, rfl⟩ := exists_fixed_add_comm hodd v
    have hv₀' : (c ^ i) v₀ = v₀ := by
      have : c ^ i ∈ MulAction.stabilizer (GLV V) v₀ :=
        Subgroup.zpow_mem _ (MulAction.mem_stabilizer_iff.2 hv₀) i
      exact MulAction.mem_stabilizer_iff.1 this
    have e : (c ^ i) (v₀ + v₁) - (v₀ + v₁) = (c ^ i) v₁ - v₁ := by
      rw [map_add, hv₀']; abel
    rw [e]
    have hv₁' : v₁ ∈ commSpace X' ⊤ := commSpace_zpowers_le hcX' hv₁
    have hciX' : c ^ i ∈ X' := Subgroup.zpow_mem _ hcX' i
    have hciv : (c ^ i) v₁ ∈ commSpace X' ⊤ :=
      invariant_commSpace (fun k' hk' k hk => X'.mul_mem (X'.mul_mem hk' hk) (X'.inv_mem hk'))
        (invariant_top X') _ hciX' _ hv₁'
    refine ⟨(commSpace X' ⊤).sub_mem hciv hv₁', ?_⟩
    obtain ⟨y, hy⟩ := QuotientAddGroup.mk_surjective (β ⟨v₁, hv₁'⟩)
    have hX : c ^ i ∈ X := Subgroup.zpow_mem _ hcX i
    have h1 := hH.equiv ⟨c ^ i, hX⟩ ⟨v₁, hv₁'⟩ ⟨_, hciv⟩ rfl y hy.symm
    have h2 : (⟨(c ^ i) v₁ - v₁, (commSpace X' ⊤).sub_mem hciv hv₁'⟩ : ↥(commSpace X' ⊤)) =
        ⟨_, hciv⟩ - ⟨v₁, hv₁'⟩ := rfl
    rw [h2, map_sub, h1, ← hy]
    have h3 : ρ ⟨c ^ i, hX⟩ = ρ ⟨c, hcX⟩ ^ i := by
      rw [← map_zpow]; rfl
    rw [h3]
    exact hT i y
  obtain ⟨hw', hwT⟩ := hle hw
  exact hwT

theorem card_eq_two_pow (W : Submodule (ZMod 2) V) :
    Nat.card W = 2 ^ Module.finrank (ZMod 2) W := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (FiniteField.pow_finrank_eq_natCard 2 W).symm

theorem finrank_commSpace_le_two (hH : HeartFor X N ρ X' β) (hinj : Function.Injective ρ)
    {c : GLV V} (hcX : c ∈ X) (hcX' : c ∈ X') (h3 : (ρ ⟨c, hcX⟩).IsThreeCycle) :
    Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers c) ⊤) ≤ 2 := by
  classical
  set σ := ρ ⟨c, hcX⟩ with hσ
  have hord : orderOf c = 3 := by
    have h1 : orderOf (⟨c, hcX⟩ : ↥X) = 3 := by
      rw [← orderOf_injective ρ hinj, ← hσ, h3.orderOf]
    rwa [Subgroup.orderOf_mk] at h1
  have hodd : Odd (orderOf c) := by rw [hord]; decide
  obtain ⟨p, hp⟩ : ∃ p, p ∈ σ.support := by
    have : σ.support.Nonempty := by
      rw [← Finset.card_pos, h3.card_support]; norm_num
    exact this
  have hsupp : σ.support = {p, σ p, σ (σ p)} := (h3.support_eq_iff_mem_support).2 hp
  have hσp : σ p ≠ p := Equiv.Perm.mem_support.1 hp
  have hσ3 : σ ^ 3 = 1 := by rw [← h3.orderOf]; exact pow_orderOf_eq_one σ
  have hpq : p ≠ σ p := Ne.symm hσp
  have hqr : σ p ≠ σ (σ p) := fun h => hσp (σ.injective h).symm
  have hpr : p ≠ σ (σ p) := by
    intro h
    have h' : σ (σ (σ p)) = σ p := by rw [← h]
    have h3p : σ (σ (σ p)) = p := by
      have := congrArg (fun f : Perm (Fin N) => f p) hσ3
      simpa [pow_succ, Perm.mul_apply] using this
    rw [h3p] at h'
    exact hσp h'.symm
  let Δ3 : AddSubgroup (evenWeight N) :=
    { carrier := {x | ∀ i, i ≠ p → i ≠ σ p → i ≠ σ (σ p) → (x : Fin N → ZMod 2) i = 0}
      add_mem' := fun {a b} ha hb i h1 h2 h3' => by
        show (a : Fin N → ZMod 2) i + (b : Fin N → ZMod 2) i = 0
        rw [ha i h1 h2 h3', hb i h1 h2 h3', add_zero]
      zero_mem' := fun _ _ _ _ => rfl
      neg_mem' := fun {a} ha i h1 h2 h3' => by
        have := ha i h1 h2 h3'
        simp [this] }
  let T : AddSubgroup (altHeart N) := Δ3.map (QuotientAddGroup.mk' (evenWeightOnes N))
  have hT : ∀ (k : ℤ) (y : evenWeight N),
      ((evenWeightPerm (σ ^ k) y - y : evenWeight N) : altHeart N) ∈ T := by
    intro k y
    refine ⟨_, fun i h1 h2 h3' => sub_supp _ y i ?_, rfl⟩
    have hi : σ i = i := by
      by_contra hi
      have : i ∈ σ.support := Equiv.Perm.mem_support.2 hi
      rw [hsupp] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      tauto
    have : (σ ^ k)⁻¹ ∈ MulAction.stabilizer (Perm (Fin N)) i :=
      Subgroup.inv_mem _ (Subgroup.zpow_mem _ (MulAction.mem_stabilizer_iff.2 hi) k)
    exact MulAction.mem_stabilizer_iff.1 this
  have hcardΔ : Nat.card Δ3 ≤ 4 := by
    let g : Δ3 → Fin 4 := fun x =>
      if (x : evenWeight N) = 0 then 0
      else if ((x : evenWeight N) : Fin N → ZMod 2) = (pairEW p (σ p) : Fin N → ZMod 2) then 1
      else if ((x : evenWeight N) : Fin N → ZMod 2) = (pairEW (σ p) (σ (σ p)) : Fin N → ZMod 2)
        then 2 else 3
    have hg : Function.Injective g := by
      intro x₁ x₂ h
      have hx : ∀ x : Δ3, ((x : evenWeight N) : Fin N → ZMod 2) = 0 ∨
          ((x : evenWeight N) : Fin N → ZMod 2) = (pairEW p (σ p) : Fin N → ZMod 2) ∨
          ((x : evenWeight N) : Fin N → ZMod 2) = (pairEW (σ p) (σ (σ p)) : Fin N → ZMod 2) ∨
          ((x : evenWeight N) : Fin N → ZMod 2) = (pairEW p (σ (σ p)) : Fin N → ZMod 2) :=
        fun x => eq_of_supp_three hpq hqr hpr _ (sum_evenWeight _) x.2
      have hne : ∀ a b c' d : Fin N, a ≠ b → (pairEW a b : Fin N → ZMod 2) ≠ 0 := by
        intro a b _ _ hab h
        have := congrFun h a
        rw [pairEW_apply] at this
        simp [hab] at this
      have hne12 : (pairEW p (σ p) : Fin N → ZMod 2) ≠ (pairEW (σ p) (σ (σ p)) : Fin N → ZMod 2) :=
        fun h => by
          have := congrFun h p
          simp [pairEW_apply, hpq, hpr] at this
      have hne13 : (pairEW p (σ p) : Fin N → ZMod 2) ≠ (pairEW p (σ (σ p)) : Fin N → ZMod 2) :=
        fun h => by
          have := congrFun h (σ p)
          simp [pairEW_apply, hpq, hqr, Ne.symm hpq] at this
      have hne23 : (pairEW (σ p) (σ (σ p)) : Fin N → ZMod 2) ≠ (pairEW p (σ (σ p)) : Fin N → ZMod 2) :=
        fun h => by
          have := congrFun h p
          simp [pairEW_apply, hpq, hpr] at this
      have hz : ∀ x : Δ3, (x : evenWeight N) = 0 ↔ ((x : evenWeight N) : Fin N → ZMod 2) = 0 :=
        fun x => ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩
      apply Subtype.ext
      apply Subtype.ext
      rcases hx x₁ with h1 | h1 | h1 | h1 <;> rcases hx x₂ with h2 | h2 | h2 | h2 <;>
        simp only [g, hz, h1, h2, hne p (σ p) p p hpq, hne (σ p) (σ (σ p)) p p hqr,
          hne p (σ (σ p)) p p hpr, hne12, hne13, hne23, Ne.symm hne12, Ne.symm hne13,
          Ne.symm hne23, if_true, if_false, eq_self_iff_true] at h ⊢ <;>
        first | rfl | exact absurd h (by decide)
    have := Nat.card_le_card_of_injective g hg
    simpa using this
  have hcardT : Nat.card T ≤ 4 := by
    refine le_trans (Nat.card_le_card_of_surjective (fun x : Δ3 =>
      (⟨QuotientAddGroup.mk' (evenWeightOnes N) (x : evenWeight N), (x : evenWeight N), x.2,
        rfl⟩ : T)) ?_) hcardΔ
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  let f : ↥(commSpace (Subgroup.zpowers c) ⊤) → T := fun w =>
    ⟨β ⟨w, commSpace_zpowers_le hcX' w.2⟩,
      image_le hH hcX hcX' hodd T hT (w := ⟨w, commSpace_zpowers_le hcX' w.2⟩) w.2⟩
  have hf : Function.Injective f := by
    intro w₁ w₂ h
    have h1 : β ⟨w₁, commSpace_zpowers_le hcX' w₁.2⟩ = β ⟨w₂, commSpace_zpowers_le hcX' w₂.2⟩ :=
      congrArg Subtype.val h
    have h2 : β (⟨w₁, commSpace_zpowers_le hcX' w₁.2⟩ - ⟨w₂, commSpace_zpowers_le hcX' w₂.2⟩) = 0 :=
      by rw [map_sub, h1, sub_self]
    have h3 := injOn hH hcX' hodd (w := _ - _)
      ((commSpace (Subgroup.zpowers c) ⊤).sub_mem w₁.2 w₂.2) h2
    exact Subtype.ext (sub_eq_zero.1 h3)
  have hcard := (Nat.card_le_card_of_injective f hf).trans hcardT
  rw [card_eq_two_pow] at hcard
  by_contra hlt
  push Not at hlt
  have : 2 ^ 3 ≤ 2 ^ Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers c) ⊤) :=
    Nat.pow_le_pow_right (by norm_num) hlt
  omega

@[expose] noncomputable def pairFun (a b : Fin N) : altHeart N →+ ZMod 2 :=
  QuotientAddGroup.lift (evenWeightOnes N)
    { toFun := fun x => (x : Fin N → ZMod 2) a + (x : Fin N → ZMod 2) b
      map_zero' := by simp
      map_add' := fun x y => by
        show (x + y : Fin N → ZMod 2) a + (x + y : Fin N → ZMod 2) b = _
        simp only [Pi.add_apply]
        ring }
    (fun x hx => by
      obtain ⟨κ, hκ⟩ := exists_forall_eq_of_mem_evenWeightOnes hx
      show (x : Fin N → ZMod 2) a + (x : Fin N → ZMod 2) b = 0
      rw [hκ a, hκ b]
      exact CharTwo.add_self_eq_zero κ)

theorem pairFun_mk (a b : Fin N) (x : evenWeight N) :
    pairFun a b (x : altHeart N) = (x : Fin N → ZMod 2) a + (x : Fin N → ZMod 2) b := rfl

theorem le_finrank_of_dual {c : GLV V} (hcX' : c ∈ X') {r : ℕ} (w : Fin r → ↥(commSpace X' ⊤))
    (hw : ∀ i, (w i : V) ∈ commSpace (Subgroup.zpowers c) ⊤) (φ : Fin r → (altHeart N →+ ZMod 2))
    (hφ : ∀ i k, φ i (β (w k)) = if i = k then 1 else 0) :
    r ≤ Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers c) ⊤) := by
  classical
  let incl : ↥(commSpace (Subgroup.zpowers c) ⊤) →+ ↥(commSpace X' ⊤) :=
    (Submodule.inclusion (commSpace_zpowers_le hcX')).toAddMonoidHom
  let Φ0 : ↥(commSpace (Subgroup.zpowers c) ⊤) →+ (Fin r → ZMod 2) :=
    { toFun := fun v i => φ i (β (incl v))
      map_zero' := by funext i; simp
      map_add' := fun a b => by funext i; simp }
  let Φ : ↥(commSpace (Subgroup.zpowers c) ⊤) →ₗ[ZMod 2] (Fin r → ZMod 2) :=
    { toFun := Φ0
      map_add' := Φ0.map_add
      map_smul' := fun a v => by
        rcases (show a = 0 ∨ a = 1 by revert a; decide) with rfl | rfl
        · simp
        · simp }
  have hΦ : ∀ k, Φ ⟨w k, hw k⟩ = Pi.single k 1 := by
    intro k
    funext i
    have h1 : incl ⟨w k, hw k⟩ = w k := Subtype.ext rfl
    have h2 : Φ ⟨w k, hw k⟩ i = φ i (β (incl ⟨w k, hw k⟩)) := rfl
    rw [h2, h1, hφ, Pi.single_apply]
  have hrange : LinearMap.range Φ = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun (ZMod 2) (Fin r)).span_eq, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rw [Pi.basisFun_apply]
    exact ⟨_, hΦ k⟩
  have := LinearMap.finrank_range_le Φ
  rw [hrange, finrank_top, Module.finrank_fin_fun] at this
  exact this

theorem exists_comm_vec (hH : HeartFor X N ρ X' β) {c : GLV V} (hcX : c ∈ X) (hcX' : c ∈ X')
    (y : evenWeight N) :
    ∃ w : ↥(commSpace X' ⊤), (w : V) ∈ commSpace (Subgroup.zpowers c) ⊤ ∧
      β w = ((evenWeightPerm (ρ ⟨c, hcX⟩) y - y : evenWeight N) : altHeart N) := by
  obtain ⟨u, hu⟩ := hH.surj (y : altHeart N)
  have hcu : c (u : V) ∈ commSpace X' ⊤ :=
    invariant_commSpace (fun k' hk' k hk => X'.mul_mem (X'.mul_mem hk' hk) (X'.inv_mem hk'))
      (invariant_top X') _ hcX' _ u.2
  refine ⟨⟨_, hcu⟩ - u, sub_mem_commSpace (Subgroup.mem_zpowers c) Submodule.mem_top, ?_⟩
  rw [map_sub, hH.equiv ⟨c, hcX⟩ u ⟨_, hcu⟩ rfl y hu, hu]
  rfl

theorem coord_comm_pair (σ : Perm (Fin N)) (a b j : Fin N) :
    ((evenWeightPerm σ (pairEW a b) - pairEW a b : evenWeight N) : Fin N → ZMod 2) j =
      ((if j = σ a then 1 else 0) + (if j = σ b then 1 else 0)) -
        ((if j = a then 1 else 0) + (if j = b then 1 else 0)) := by
  rw [evenWeightPerm_pairEW]
  show (pairEW (σ a) (σ b) : Fin N → ZMod 2) j - (pairEW a b : Fin N → ZMod 2) j = _
  rw [pairEW_apply, pairEW_apply]

theorem pairFun_comm (σ : Perm (Fin N)) (a b x y : Fin N) :
    pairFun a b (((evenWeightPerm σ (pairEW x y) - pairEW x y : evenWeight N)) : altHeart N) =
      ((((if a = σ x then 1 else 0) + (if a = σ y then 1 else 0)) -
        ((if a = x then 1 else 0) + (if a = y then 1 else 0))) +
      (((if b = σ x then 1 else 0) + (if b = σ y then 1 else 0)) -
        ((if b = x then 1 else 0) + (if b = y then 1 else 0))) : ZMod 2) := by
  rw [pairFun_mk, coord_comm_pair, coord_comm_pair]

theorem orbit_ne {σ : Perm (Fin N)} (hσ3 : σ ^ 3 = 1) {p : Fin N} (hp : σ p ≠ p) :
    p ≠ σ p ∧ σ p ≠ σ (σ p) ∧ p ≠ σ (σ p) ∧ σ (σ (σ p)) = p := by
  have h3p : σ (σ (σ p)) = p := by
    have := congrArg (fun f : Perm (Fin N) => f p) hσ3
    simpa [pow_succ, Perm.mul_apply] using this
  refine ⟨Ne.symm hp, fun h => hp (σ.injective h).symm, fun h => ?_, h3p⟩
  have h' : σ (σ (σ p)) = σ p := by rw [← h]
  rw [h3p] at h'
  exact hp h'.symm

theorem two_le_finrank (hH : HeartFor X N ρ X' β) {c : GLV V} (hcX : c ∈ X) (hcX' : c ∈ X')
    (hσ3 : ρ ⟨c, hcX⟩ ^ 3 = 1) {p : Fin N} (hp : ρ ⟨c, hcX⟩ p ≠ p) :
    2 ≤ Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers c) ⊤) := by
  set σ := ρ ⟨c, hcX⟩ with hσ
  obtain ⟨h1, h2, h3, h4⟩ := orbit_ne hσ3 hp
  obtain ⟨w₁, hw₁, hβ₁⟩ := exists_comm_vec hH hcX hcX' (pairEW p (σ p))
  obtain ⟨w₂, hw₂, hβ₂⟩ := exists_comm_vec hH hcX hcX' (pairEW (σ p) (σ (σ p)))
  rw [← hσ] at hβ₁ hβ₂
  have f : ∀ (a b x y : Fin N), pairFun a b (β (if (x, y) = (p, σ p) then w₁ else w₂)) =
      pairFun a b (β (if (x, y) = (p, σ p) then w₁ else w₂)) := fun _ _ _ _ => rfl
  have f11 : pairFun p (σ p) (β w₁) = 1 := by
    rw [hβ₁, pairFun_comm]; simp [h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3]; try decide
  have f12 : pairFun p (σ p) (β w₂) = 0 := by
    rw [hβ₂, pairFun_comm, h4]; simp [h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3]; try decide
  have f21 : pairFun p (σ (σ p)) (β w₁) = 0 := by
    rw [hβ₁, pairFun_comm]; simp [h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3]; try decide
  have f22 : pairFun p (σ (σ p)) (β w₂) = 1 := by
    rw [hβ₂, pairFun_comm, h4]; simp [h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3]; try decide
  refine le_finrank_of_dual (β := β) hcX' ![w₁, w₂] (fun i => by fin_cases i <;> assumption)
    ![pairFun p (σ p), pairFun p (σ (σ p))] fun i k => ?_
  fin_cases i <;> fin_cases k <;> simp [f11, f12, f21, f22]

theorem four_le_finrank (hH : HeartFor X N ρ X' β) {c : GLV V} (hcX : c ∈ X) (hcX' : c ∈ X')
    (hσ3 : ρ ⟨c, hcX⟩ ^ 3 = 1) {p d : Fin N} (hp : ρ ⟨c, hcX⟩ p ≠ p)
    (hd : ρ ⟨c, hcX⟩ d ≠ d) (hdp : d ≠ p) (hdq : d ≠ ρ ⟨c, hcX⟩ p)
    (hdr : d ≠ ρ ⟨c, hcX⟩ (ρ ⟨c, hcX⟩ p)) :
    4 ≤ Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers c) ⊤) := by
  set σ := ρ ⟨c, hcX⟩ with hσ
  obtain ⟨h1, h2, h3, h4⟩ := orbit_ne hσ3 hp
  obtain ⟨k1, k2, k3, k4⟩ := orbit_ne hσ3 hd
  have e1 : σ d ≠ p := fun h => hdr (by rw [← h, k4])
  have e2 : σ d ≠ σ p := fun h => hdp (σ.injective h)
  have e3 : σ d ≠ σ (σ p) := fun h => hdq (σ.injective h)
  have e4 : σ (σ d) ≠ p := fun h => hdq (by rw [← h, k4])
  have e5 : σ (σ d) ≠ σ p := fun h => hdr (by
    have := congrArg σ h
    rw [k4] at this
    exact this)
  have e6 : σ (σ d) ≠ σ (σ p) := fun h => hdp (σ.injective (σ.injective h))
  obtain ⟨w₁, hw₁, hβ₁⟩ := exists_comm_vec hH hcX hcX' (pairEW p (σ p))
  obtain ⟨w₂, hw₂, hβ₂⟩ := exists_comm_vec hH hcX hcX' (pairEW (σ p) (σ (σ p)))
  obtain ⟨w₃, hw₃, hβ₃⟩ := exists_comm_vec hH hcX hcX' (pairEW d (σ d))
  obtain ⟨w₄, hw₄, hβ₄⟩ := exists_comm_vec hH hcX hcX' (pairEW (σ d) (σ (σ d)))
  rw [← hσ] at hβ₁ hβ₂ hβ₃ hβ₄
  have F : ∀ (a b x y : Fin N) (w : ↥(commSpace X' ⊤)),
      β w = ((evenWeightPerm σ (pairEW x y) - pairEW x y : evenWeight N) : altHeart N) →
      pairFun a b (β w) =
      ((((if a = σ x then 1 else 0) + (if a = σ y then 1 else 0)) -
        ((if a = x then 1 else 0) + (if a = y then 1 else 0))) +
      (((if b = σ x then 1 else 0) + (if b = σ y then 1 else 0)) -
        ((if b = x then 1 else 0) + (if b = y then 1 else 0))) : ZMod 2) :=
    fun a b x y w h => by rw [h, pairFun_comm]
  have f11 : pairFun p (σ p) (β w₁) = 1 := by
    rw [F _ _ _ _ _ hβ₁]; simp [h4, k4, h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3, k1, k2, k3, Ne.symm k1, Ne.symm k2, Ne.symm k3, hdp, hdq, hdr, Ne.symm hdp, Ne.symm hdq, Ne.symm hdr, e1, e2, e3, e4, e5, e6, Ne.symm e1, Ne.symm e2, Ne.symm e3, Ne.symm e4, Ne.symm e5, Ne.symm e6]; try decide
  have f12 : pairFun p (σ p) (β w₂) = 0 := by
    rw [F _ _ _ _ _ hβ₂]; simp [h4, k4, h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3, k1, k2, k3, Ne.symm k1, Ne.symm k2, Ne.symm k3, hdp, hdq, hdr, Ne.symm hdp, Ne.symm hdq, Ne.symm hdr, e1, e2, e3, e4, e5, e6, Ne.symm e1, Ne.symm e2, Ne.symm e3, Ne.symm e4, Ne.symm e5, Ne.symm e6]; try decide
  have f13 : pairFun p (σ p) (β w₃) = 0 := by
    rw [F _ _ _ _ _ hβ₃]; simp [h4, k4, h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3, k1, k2, k3, Ne.symm k1, Ne.symm k2, Ne.symm k3, hdp, hdq, hdr, Ne.symm hdp, Ne.symm hdq, Ne.symm hdr, e1, e2, e3, e4, e5, e6, Ne.symm e1, Ne.symm e2, Ne.symm e3, Ne.symm e4, Ne.symm e5, Ne.symm e6]; try decide
  have f14 : pairFun p (σ p) (β w₄) = 0 := by
    rw [F _ _ _ _ _ hβ₄]; simp [h4, k4, h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3, k1, k2, k3, Ne.symm k1, Ne.symm k2, Ne.symm k3, hdp, hdq, hdr, Ne.symm hdp, Ne.symm hdq, Ne.symm hdr, e1, e2, e3, e4, e5, e6, Ne.symm e1, Ne.symm e2, Ne.symm e3, Ne.symm e4, Ne.symm e5, Ne.symm e6]; try decide
  have f21 : pairFun p (σ (σ p)) (β w₁) = 0 := by
    rw [F _ _ _ _ _ hβ₁]; simp [h4, k4, h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3, k1, k2, k3, Ne.symm k1, Ne.symm k2, Ne.symm k3, hdp, hdq, hdr, Ne.symm hdp, Ne.symm hdq, Ne.symm hdr, e1, e2, e3, e4, e5, e6, Ne.symm e1, Ne.symm e2, Ne.symm e3, Ne.symm e4, Ne.symm e5, Ne.symm e6]; try decide
  have f22 : pairFun p (σ (σ p)) (β w₂) = 1 := by
    rw [F _ _ _ _ _ hβ₂]; simp [h4, k4, h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3, k1, k2, k3, Ne.symm k1, Ne.symm k2, Ne.symm k3, hdp, hdq, hdr, Ne.symm hdp, Ne.symm hdq, Ne.symm hdr, e1, e2, e3, e4, e5, e6, Ne.symm e1, Ne.symm e2, Ne.symm e3, Ne.symm e4, Ne.symm e5, Ne.symm e6]; try decide
  have f23 : pairFun p (σ (σ p)) (β w₃) = 0 := by
    rw [F _ _ _ _ _ hβ₃]; simp [h4, k4, h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3, k1, k2, k3, Ne.symm k1, Ne.symm k2, Ne.symm k3, hdp, hdq, hdr, Ne.symm hdp, Ne.symm hdq, Ne.symm hdr, e1, e2, e3, e4, e5, e6, Ne.symm e1, Ne.symm e2, Ne.symm e3, Ne.symm e4, Ne.symm e5, Ne.symm e6]; try decide
  have f24 : pairFun p (σ (σ p)) (β w₄) = 0 := by
    rw [F _ _ _ _ _ hβ₄]; simp [h4, k4, h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3, k1, k2, k3, Ne.symm k1, Ne.symm k2, Ne.symm k3, hdp, hdq, hdr, Ne.symm hdp, Ne.symm hdq, Ne.symm hdr, e1, e2, e3, e4, e5, e6, Ne.symm e1, Ne.symm e2, Ne.symm e3, Ne.symm e4, Ne.symm e5, Ne.symm e6]; try decide
  have f31 : pairFun d (σ d) (β w₁) = 0 := by
    rw [F _ _ _ _ _ hβ₁]; simp [h4, k4, h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3, k1, k2, k3, Ne.symm k1, Ne.symm k2, Ne.symm k3, hdp, hdq, hdr, Ne.symm hdp, Ne.symm hdq, Ne.symm hdr, e1, e2, e3, e4, e5, e6, Ne.symm e1, Ne.symm e2, Ne.symm e3, Ne.symm e4, Ne.symm e5, Ne.symm e6]; try decide
  have f32 : pairFun d (σ d) (β w₂) = 0 := by
    rw [F _ _ _ _ _ hβ₂]; simp [h4, k4, h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3, k1, k2, k3, Ne.symm k1, Ne.symm k2, Ne.symm k3, hdp, hdq, hdr, Ne.symm hdp, Ne.symm hdq, Ne.symm hdr, e1, e2, e3, e4, e5, e6, Ne.symm e1, Ne.symm e2, Ne.symm e3, Ne.symm e4, Ne.symm e5, Ne.symm e6]; try decide
  have f33 : pairFun d (σ d) (β w₃) = 1 := by
    rw [F _ _ _ _ _ hβ₃]; simp [h4, k4, h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3, k1, k2, k3, Ne.symm k1, Ne.symm k2, Ne.symm k3, hdp, hdq, hdr, Ne.symm hdp, Ne.symm hdq, Ne.symm hdr, e1, e2, e3, e4, e5, e6, Ne.symm e1, Ne.symm e2, Ne.symm e3, Ne.symm e4, Ne.symm e5, Ne.symm e6]; try decide
  have f34 : pairFun d (σ d) (β w₄) = 0 := by
    rw [F _ _ _ _ _ hβ₄]; simp [h4, k4, h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3, k1, k2, k3, Ne.symm k1, Ne.symm k2, Ne.symm k3, hdp, hdq, hdr, Ne.symm hdp, Ne.symm hdq, Ne.symm hdr, e1, e2, e3, e4, e5, e6, Ne.symm e1, Ne.symm e2, Ne.symm e3, Ne.symm e4, Ne.symm e5, Ne.symm e6]; try decide
  have f41 : pairFun d (σ (σ d)) (β w₁) = 0 := by
    rw [F _ _ _ _ _ hβ₁]; simp [h4, k4, h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3, k1, k2, k3, Ne.symm k1, Ne.symm k2, Ne.symm k3, hdp, hdq, hdr, Ne.symm hdp, Ne.symm hdq, Ne.symm hdr, e1, e2, e3, e4, e5, e6, Ne.symm e1, Ne.symm e2, Ne.symm e3, Ne.symm e4, Ne.symm e5, Ne.symm e6]; try decide
  have f42 : pairFun d (σ (σ d)) (β w₂) = 0 := by
    rw [F _ _ _ _ _ hβ₂]; simp [h4, k4, h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3, k1, k2, k3, Ne.symm k1, Ne.symm k2, Ne.symm k3, hdp, hdq, hdr, Ne.symm hdp, Ne.symm hdq, Ne.symm hdr, e1, e2, e3, e4, e5, e6, Ne.symm e1, Ne.symm e2, Ne.symm e3, Ne.symm e4, Ne.symm e5, Ne.symm e6]; try decide
  have f43 : pairFun d (σ (σ d)) (β w₃) = 0 := by
    rw [F _ _ _ _ _ hβ₃]; simp [h4, k4, h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3, k1, k2, k3, Ne.symm k1, Ne.symm k2, Ne.symm k3, hdp, hdq, hdr, Ne.symm hdp, Ne.symm hdq, Ne.symm hdr, e1, e2, e3, e4, e5, e6, Ne.symm e1, Ne.symm e2, Ne.symm e3, Ne.symm e4, Ne.symm e5, Ne.symm e6]; try decide
  have f44 : pairFun d (σ (σ d)) (β w₄) = 1 := by
    rw [F _ _ _ _ _ hβ₄]; simp [h4, k4, h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3, k1, k2, k3, Ne.symm k1, Ne.symm k2, Ne.symm k3, hdp, hdq, hdr, Ne.symm hdp, Ne.symm hdq, Ne.symm hdr, e1, e2, e3, e4, e5, e6, Ne.symm e1, Ne.symm e2, Ne.symm e3, Ne.symm e4, Ne.symm e5, Ne.symm e6]; try decide
  refine le_finrank_of_dual (β := β) hcX' ![w₁, w₂, w₃, w₄] (fun i => by fin_cases i <;> assumption)
    ![pairFun p (σ p), pairFun p (σ (σ p)), pairFun d (σ d), pairFun d (σ (σ d))] fun i k => ?_
  fin_cases i <;> fin_cases k <;> simp [f11, f12, f13, f14, f21, f22, f23, f24, f31, f32, f33, f34, f41, f42, f43, f44]

theorem mem_comm_of_mem (hH : HeartFor X N ρ X' β) {x : GLV V} (hx : x ∈ X')
    (w : ↥(commSpace X' ⊤)) : x (w : V) ∈ commSpace X' ⊤ :=
  invariant_commSpace (fun k' hk' k hk => X'.mul_mem (X'.mul_mem hk' hk) (X'.inv_mem hk'))
    (invariant_top X') _ hx _ w.2

theorem HeartFor.hasIrrTildeV (hH : HeartFor X N ρ X' β) (hN : 4 ≤ N)
    (honto : ∀ σ ∈ alternatingGroup (Fin N), ∃ x : ↥X, (x : GLV V) ∈ X' ∧ ρ x = σ) :
    HasIrrTildeV X' := by
  refine ⟨lt_of_le_of_ne inf_le_right fun h => ?_, fun J hJ hCJ hJA => ?_⟩
  · haveI := altHeart_nontrivial (n := N) (by omega)
    obtain ⟨a, ha⟩ := exists_ne (0 : altHeart N)
    obtain ⟨w, rfl⟩ := hH.surj a
    apply ha
    have hw : (w : V) ∈ tildeVBot X' := by rw [h]; exact w.2
    have hk : w ∈ β.ker := by rw [hH.ker]; exact hw.1
    exact hk
  · let U : AddSubgroup (altHeart N) :=
      ((J.comap (commSpace X' ⊤).subtype).toAddSubgroup).map β
    have hU : ∀ σ ∈ alternatingGroup (Fin N), ∀ y : evenWeight N, (y : altHeart N) ∈ U →
        (evenWeightPerm σ y : altHeart N) ∈ U := by
      rintro σ hσ y ⟨w, hwJ, hw⟩
      obtain ⟨x, hxX', rfl⟩ := honto σ hσ
      refine ⟨⟨_, mem_comm_of_mem hH hxX' w⟩, hJ _ hxX' _ hwJ, ?_⟩
      exact hH.equiv x w ⟨_, mem_comm_of_mem hH hxX' w⟩ rfl y hw
    rcases altHeart_irreducible hN U hU with hU0 | hU1
    · left
      refine le_antisymm (fun v hv => ?_) hCJ
      have hvA := hJA hv
      have hmem : β ⟨v, hvA⟩ ∈ U := ⟨⟨v, hvA⟩, hv, rfl⟩
      rw [hU0] at hmem
      have hk : (⟨v, hvA⟩ : ↥(commSpace X' ⊤)) ∈ β.ker := AddSubgroup.mem_bot.1 hmem
      rw [hH.ker] at hk
      exact ⟨hk, hvA⟩
    · right
      refine le_antisymm hJA fun v hv => ?_
      have hmem : β ⟨v, hv⟩ ∈ U := by rw [hU1]; trivial
      obtain ⟨w, hwJ, hw⟩ := hmem
      have hk : (⟨v, hv⟩ : ↥(commSpace X' ⊤)) - w ∈ β.ker := by
        rw [AddMonoidHom.mem_ker, map_sub, hw, sub_self]
      rw [hH.ker] at hk
      have hC : (v - (w : V) : V) ∈ fixedSpace X' ⊓ commSpace X' ⊤ :=
        ⟨hk, (commSpace X' ⊤).sub_mem hv w.2⟩
      have := J.add_mem (hCJ hC) hwJ
      simpa using this

theorem HeartFor.faithful (hH : HeartFor X N ρ X' β) (hinj : Function.Injective ρ) (hN : 5 ≤ N) :
    FaithfulTildeV X' := by
  intro ℓ hℓ hfix
  have hℓX : ℓ ∈ X := hH.le hℓ
  have hρ : ρ ⟨ℓ, hℓX⟩ = 1 := by
    refine perm_eq_one_of_altHeart_fixed hN _ fun y => ?_
    obtain ⟨w, hw⟩ := hH.surj (y : altHeart N)
    have h1 := hH.equiv ⟨ℓ, hℓX⟩ w ⟨_, mem_comm_of_mem hH hℓ w⟩ rfl y hw
    rw [← h1, ← hw]
    have hk : (⟨_, mem_comm_of_mem hH hℓ w⟩ : ↥(commSpace X' ⊤)) - w ∈ β.ker := by
      rw [hH.ker]; exact hfix w w.2
    rw [AddMonoidHom.mem_ker, map_sub, sub_eq_zero] at hk
    exact hk
  have : (⟨ℓ, hℓX⟩ : ↥X) = 1 := hinj (by rw [hρ, map_one])
  exact congrArg Subtype.val this

theorem HeartFor.isAltNaturalModule (hH : HeartFor X N ρ X' β)
    (honto : ∀ σ ∈ alternatingGroup (Fin N), ∃ x : ↥X, (x : GLV V) ∈ X' ∧ ρ x = σ) :
    IsAltNaturalModule X' N := by
  let α : ↥X' →* alternatingGroup (Fin N) :=
    (ρ.comp (Subgroup.inclusion hH.le)).codRestrict (alternatingGroup (Fin N))
      (fun x => (hH.mem_iff _).1 x.2)
  refine ⟨α, fun σ => ?_, β, hH.surj, hH.ker, fun ℓ w w' hw y hy =>
    hH.equiv (Subgroup.inclusion hH.le ℓ) w w' hw y hy⟩
  obtain ⟨x, hxX', hx⟩ := honto σ σ.2
  exact ⟨⟨x, hxX'⟩, Subtype.ext hx⟩

theorem image_le_of_perfect (hH : HeartFor X N ρ X' β) {Y : Subgroup (GLV V)} (hYX' : Y ≤ X')
    (hperf : ⁅Y, Y⁆ = Y) (T : AddSubgroup (altHeart N))
    (hT : ∀ (y : GLV V) (hy : y ∈ Y) (x : evenWeight N),
      ((evenWeightPerm (ρ ⟨y, hH.le (hYX' hy)⟩) x - x : evenWeight N) : altHeart N) ∈ T)
    {w : ↥(commSpace X' ⊤)} (hw : (w : V) ∈ commSpace Y ⊤) : β w ∈ T := by
  let Wsub : Submodule (ZMod 2) V :=
    { carrier := {v | ∃ hv : v ∈ commSpace X' ⊤, β ⟨v, hv⟩ ∈ T}
      add_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨(commSpace X' ⊤).add_mem ha hb, ?_⟩
        have : (⟨a + b, (commSpace X' ⊤).add_mem ha hb⟩ : ↥(commSpace X' ⊤)) =
          ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
        rw [this, map_add]
        exact T.add_mem ha' hb'
      zero_mem' := ⟨(commSpace X' ⊤).zero_mem, by
        have : (⟨0, (commSpace X' ⊤).zero_mem⟩ : ↥(commSpace X' ⊤)) = 0 := rfl
        rw [this, map_zero]; exact T.zero_mem⟩
      smul_mem' := by
        rintro a v ⟨hv, hv'⟩
        refine ⟨(commSpace X' ⊤).smul_mem a hv, ?_⟩
        rcases (show a = 0 ∨ a = 1 by revert a; decide) with rfl | rfl
        · have : (⟨(0 : ZMod 2) • v, (commSpace X' ⊤).smul_mem 0 hv⟩ : ↥(commSpace X' ⊤)) = 0 :=
            Subtype.ext (zero_smul _ v)
          rw [this, map_zero]; exact T.zero_mem
        · have : (⟨(1 : ZMod 2) • v, (commSpace X' ⊤).smul_mem 1 hv⟩ : ↥(commSpace X' ⊤)) =
              ⟨v, hv⟩ := Subtype.ext (one_smul _ v)
          rw [this]; exact hv' }
  have hle : commSpace Y (commSpace Y ⊤) ≤ Wsub := by
    refine commSpace_le_iff.2 fun y hy u hu => ?_
    have hu' : u ∈ commSpace X' ⊤ := commSpace_mono hYX' le_rfl hu
    have hyu : y u ∈ commSpace X' ⊤ := mem_comm_of_mem hH (hYX' hy) ⟨u, hu'⟩
    refine ⟨(commSpace X' ⊤).sub_mem hyu hu', ?_⟩
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (β ⟨u, hu'⟩)
    have h1 := hH.equiv ⟨y, hH.le (hYX' hy)⟩ ⟨u, hu'⟩ ⟨_, hyu⟩ rfl x hx.symm
    have h2 : (⟨y u - u, (commSpace X' ⊤).sub_mem hyu hu'⟩ : ↥(commSpace X' ⊤)) =
        ⟨_, hyu⟩ - ⟨u, hu'⟩ := rfl
    rw [h2, map_sub, h1, ← hx]
    exact hT y hy x
  rw [← commSpace_commSpace_top_of_perfect hperf] at hw
  obtain ⟨hv, hwT⟩ := hle hw
  exact hwT

end CaseIHeart

end CFSG.CGT.Foote82
