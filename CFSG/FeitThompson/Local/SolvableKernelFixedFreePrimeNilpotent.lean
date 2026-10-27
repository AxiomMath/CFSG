module

public import Mathlib.GroupTheory.Nilpotent
import CFSG.FeitThompson.Foundations.MinimalNormalSolvableElemAbelian
import CFSG.FeitThompson.Foundations.OrderDescentProperSubgroup
import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
import CFSG.FeitThompson.Local.NilpotentElementaryChiefCentralization
import CFSG.FeitThompson.Local.NormalNilpotentCentralizesChiefFactors
import CFSG.FeitThompson.Local.FixedFreeComplementsInvariantSections

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup QuotientGroup Pointwise

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

universe u

variable {G : Type*} [Group G] {H R L : Subgroup G} {p : ℕ}

theorem eq_bot_of_normal_lt_map_mk' [L.Normal] (hLH : L ≤ H)
    (hmax : ∀ K : Subgroup G, K.Normal → K < H → L ≤ K → K = L)
    {K : Subgroup (G ⧸ L)} (hK : K.Normal) (hlt : K < H.map (mk' L)) : K = ⊥ := by
  have hsurj : Function.Surjective (mk' L) := mk'_surjective L
  have hLK : L ≤ K.comap (mk' L) := by
    intro x hx
    simp [Subgroup.mem_comap, (QuotientGroup.eq_one_iff x).2 hx]
  have hle : K.comap (mk' L) ≤ H := by
    have h := Subgroup.comap_mono (f := mk' L) hlt.le
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.2 hLH] at h
  have hne : K.comap (mk' L) ≠ H := by
    intro h
    exact hlt.ne (by rw [← h, Subgroup.map_comap_eq_self_of_surjective hsurj])
  have heq : K.comap (mk' L) = L := hmax _ (hK.comap _) (lt_of_le_of_ne hle hne) hLK
  rw [← Subgroup.map_comap_eq_self_of_surjective hsurj K, heq, QuotientGroup.map_mk'_self]

section Descent

theorem coe_subgroupOf_mul_coe_subgroupOf_eq_univ [L.Normal] :
    ((L.subgroupOf (L ⊔ R) : Subgroup ↥(L ⊔ R)) : Set ↥(L ⊔ R)) *
      ((R.subgroupOf (L ⊔ R) : Subgroup ↥(L ⊔ R)) : Set ↥(L ⊔ R)) = Set.univ := by
  refine Set.eq_univ_iff_forall.2 fun x => ?_
  have hx : (x : G) ∈ (L : Set G) * (R : Set G) := by
    rw [← Subgroup.normal_mul]; exact x.2
  obtain ⟨l, hl, r, hr, hlr⟩ := hx
  exact ⟨⟨l, mem_sup_left hl⟩, by simpa [Subgroup.mem_subgroupOf] using hl,
    ⟨r, mem_sup_right hr⟩, by simpa [Subgroup.mem_subgroupOf] using hr, Subtype.ext hlr⟩

theorem subgroupOf_inf_subgroupOf_eq_bot (hinf : H ⊓ R = ⊥) (hLH : L ≤ H) :
    (L.subgroupOf (L ⊔ R) : Subgroup ↥(L ⊔ R)) ⊓ R.subgroupOf (L ⊔ R) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf] at hx
  have hmem : (x : G) ∈ H ⊓ R := ⟨hLH hx.1, hx.2⟩
  rw [hinf, Subgroup.mem_bot] at hmem
  exact Subtype.ext hmem

theorem subgroupOf_inf_centralizer_eq_bot (hCH : H ⊓ centralizer (R : Set G) = ⊥) (hLH : L ≤ H) :
    (L.subgroupOf (L ⊔ R) : Subgroup ↥(L ⊔ R)) ⊓
      centralizer ((R.subgroupOf (L ⊔ R) : Subgroup ↥(L ⊔ R)) : Set ↥(L ⊔ R)) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hx
  obtain ⟨hxL, hxC⟩ := hx
  have hxc : (x : G) ∈ centralizer (R : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have := hxC (⟨r, mem_sup_right hr⟩ : ↥(L ⊔ R))
      (by simpa [Subgroup.mem_subgroupOf] using hr)
    exact congrArg Subtype.val this
  have hmem : (x : G) ∈ H ⊓ centralizer (R : Set G) := ⟨hLH hxL, hxc⟩
  rw [hCH, Subgroup.mem_bot] at hmem
  exact Subtype.ext hmem

end Descent

private theorem isNilpotent_aux (hp : p.Prime) :
    ∀ (n : ℕ) (G : Type u) (_ : Group G) (_ : Finite G) (H R : Subgroup G), H.Normal →
      (H : Set G) * (R : Set G) = Set.univ → H ⊓ R = ⊥ → Nat.card R = p →
      H ⊓ centralizer (R : Set G) = ⊥ → Group.IsSolvable ↥H → Nat.card ↥H ≤ n →
      Group.IsNilpotent ↥H := by
  intro n
  induction n with
  | zero =>
    intro G _ _ H R _ _ _ _ _ _ hcard
    exact absurd hcard (by simpa using Nat.card_pos.ne')
  | succ n ih =>
    intro G _ _ H R hHnormal hprod hinf hR hCH hHsol hcard
    rcases eq_or_ne H ⊥ with rfl | hHbot
    · exact Group.isNilpotent_of_subsingleton
    obtain ⟨L, ⟨⟨hLnormal, hLH⟩, hmax⟩⟩ :=
      exists_maximal_of_wellFoundedGT (fun K : Subgroup G => K.Normal ∧ K < H)
        ⟨⊥, inferInstance, bot_lt_iff_ne_bot.2 hHbot⟩
    have hmax' : ∀ K : Subgroup G, K.Normal → K < H → L ≤ K → K = L :=
      fun K hK hKH hLK => le_antisymm (hmax ⟨hK, hKH⟩ hLK) hLK
    have hLsol : Group.IsSolvable ↥L := isSolvable_of_le hLH.le
    have hLnil : Group.IsNilpotent ↥L := by
      have hcard' : Nat.card (L.subgroupOf (L ⊔ R) : Subgroup ↥(L ⊔ R)) ≤ n := by
        have h1 : Nat.card (L.subgroupOf (L ⊔ R) : Subgroup ↥(L ⊔ R)) = Nat.card ↥L :=
          Nat.card_eq_of_bijective _ (Subgroup.subgroupOfEquivOfLe le_sup_left).bijective
        have h2 : Nat.card ↥L < Nat.card ↥H := natCard_lt_natCard_of_lt hLH
        omega
      have hsol' : Group.IsSolvable ↥(L.subgroupOf (L ⊔ R) : Subgroup ↥(L ⊔ R)) :=
        Group.isSolvable_of_isSolvable_injective
          (f := (Subgroup.subgroupOfEquivOfLe (le_sup_left (b := R))).toMonoidHom)
          (by simpa using (Subgroup.subgroupOfEquivOfLe (le_sup_left (b := R))).injective)
      have hnil' := ih ↥(L ⊔ R) inferInstance inferInstance (L.subgroupOf (L ⊔ R))
        (R.subgroupOf (L ⊔ R)) inferInstance coe_subgroupOf_mul_coe_subgroupOf_eq_univ
        (subgroupOf_inf_subgroupOf_eq_bot hinf hLH.le)
        (by
          rw [Nat.card_eq_of_bijective _
            (Subgroup.subgroupOfEquivOfLe (le_sup_right (a := L))).bijective]
          exact hR)
        (subgroupOf_inf_centralizer_eq_bot hCH hLH.le) hsol' hcard'
      exact Group.nilpotent_of_mulEquiv (_h := hnil')
        (Subgroup.subgroupOfEquivOfLe (le_sup_left (b := R)))
    have hNbot : H.map (mk' L) ≠ ⊥ := by
      rw [map_mk'_eq_quotientFactor]
      exact quotientFactor_ne_bot H L hLH
    have hNsol : Group.IsSolvable ↥(H.map (mk' L)) := isSolvable_map (mk' L) H
    obtain ⟨q, d, hq, hd, ⟨ee⟩⟩ :=
      exists_prime_nonempty_mulEquiv_of_isSolvable_of_forall_normal_lt_eq_bot hNbot
        fun K hK hKN => eq_bot_of_normal_lt_map_mk' hLH.le hmax' hK hKN
    have ee' : (↥H ⧸ L.subgroupOf H) ≃* Multiplicative (Fin d → ZMod q) :=
      (quotientFactorMulEquiv H L).trans
        ((MulEquiv.subgroupCongr (map_mk'_eq_quotientFactor H L).symm).trans ee)
    exact isNilpotent_of_isNilpotent_of_elementaryQuotient hprod hinf hp hR hCH hLH hLnil hq hd ee'

theorem isNilpotent_of_isSolvable_of_natCard_eq_prime {G : Type u} [Group G] [Finite G]
    {H R : Subgroup G} {p : ℕ} [H.Normal] [Group.IsSolvable ↥H]
    (hprod : (H : Set G) * (R : Set G) = Set.univ) (hinf : H ⊓ R = ⊥) (hp : p.Prime)
    (hR : Nat.card R = p) (hCH : H ⊓ centralizer (R : Set G) = ⊥) : Group.IsNilpotent ↥H :=
  isNilpotent_aux hp (Nat.card ↥H) G inferInstance inferInstance H R inferInstance hprod hinf hR
    hCH inferInstance le_rfl

theorem exists_central_series_of_isSolvable_of_natCard_eq_prime {G : Type u} [Group G] [Finite G]
    {H R : Subgroup G} {p : ℕ} [H.Normal] [Group.IsSolvable ↥H]
    (hprod : (H : Set G) * (R : Set G) = Set.univ) (hinf : H ⊓ R = ⊥) (hp : p.Prime)
    (hR : Nat.card R = p) (hCH : H ⊓ centralizer (R : Set G) = ⊥) :
    ∃ (n : ℕ) (X : ℕ → Subgroup G), X 0 = ⊥ ∧ X n = H ∧ Monotone X ∧ (∀ i, (X i).Normal) ∧
      ∀ i, ⁅H, X (i + 1)⁆ ≤ X i := by
  have : Group.IsSolvable ↥R := isSolvable_of_natCard_eq_prime hp hR
  have : Group.IsSolvable G := isSolvable_of_mul_coe_eq_univ hprod
  have hnil : Group.IsNilpotent ↥H :=
    isNilpotent_of_isSolvable_of_natCard_eq_prime hprod hinf hp hR hCH
  exact exists_central_series_of_forall_isChiefFactor H
    ((isNilpotent_iff_forall_isChiefFactor H).1 hnil)

end CFSG.FeitThompson
