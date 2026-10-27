module

public import CFSG.LocalAnalysis.OddStandard.AltNoHePerm
import all CFSG.LocalAnalysis.OddStandard.AltNoHePerm
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.RowAlt

open CFSG Subgroup Equiv Equiv.Perm Equiv.Perm.OnCycleFactors CFSG.OddStandard.AltNoHe
open scoped commutatorElement

section Perm

variable {α : Type*} [Fintype α] [DecidableEq α] {G : Type*} [Group G] {ε : G →* Perm α} {t : G}

omit [Fintype α] [DecidableEq α] in
@[simp] theorem centHom_coe (x : centralizer ({t} : Set G)) :
    ((centHom ε t x : centralizer ({ε t} : Set (Perm α))) : Perm α) = ε x := by
  rfl

theorem quotP_apply_coe (x : centralizer ({t} : Set G)) (c : (ε t).cycleFactorsFinset) :
    ((quotP ε t x c : (ε t).cycleFactorsFinset) : Perm α) = ε x * c * (ε x)⁻¹ := by
  change ((toPermHom (ε t) (centHom ε t x) c : (ε t).cycleFactorsFinset) : Perm α) = _
  rw [coe_toPermHom, centHom_coe]

theorem quotP_eq_one_iff (x : centralizer ({t} : Set G)) :
    quotP ε t x = 1 ↔ ∀ c ∈ (ε t).cycleFactorsFinset, Commute (ε x) c := by
  change toPermHom (ε t) (centHom ε t x) = 1 ↔ _
  rw [← MonoidHom.mem_ker, mem_ker_toPermHom_iff]
  rfl

omit [Fintype α] [DecidableEq α] in
theorem quotF_eq_one_iff (x : centralizer ({t} : Set G)) :
    quotF ε t x = 1 ↔ ∀ y, ε t y = y → ε x y = y := by
  constructor
  · intro h y hy
    have h1 := DFunLike.congr_fun h ⟨y, hy⟩
    exact congrArg Subtype.val h1
  · intro h
    ext ⟨y, hy⟩
    exact h y hy

theorem sign_cycleFactor {g c : Perm α} (hg : g * g = 1) (hc : c ∈ g.cycleFactorsFinset) :
    sign c = -1 := by
  rw [(mem_cycleFactorsFinset_iff.1 hc).1.sign, card_support_eq_two_of_mem_cycleFactorsFinset hg hc]
  rfl

omit [Fintype α] [DecidableEq α] in
theorem map_comm (x : centralizer ({t} : Set G)) : ε x * ε t = ε t * ε x := by
  rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp x.2]

theorem apply_eq_or_apply_eq (ht2 : ε t * ε t = 1) {x : centralizer ({t} : Set G)}
    (hx : quotP ε t x = 1) {a : α} (ha : ε t a ≠ a) : ε x a = a ∨ ε x a = ε t a := by
  set g := ε t
  set k := centHom ε t x
  have hk : k ∈ (toPermHom g).ker := by
    rw [mem_ker_toPermHom_iff]
    exact (quotP_eq_one_iff x).1 hx
  have hxs : a ∈ g.support := mem_support.2 ha
  have hc : g.cycleOf a ∈ g.cycleFactorsFinset := cycleOf_mem_cycleFactorsFinset_iff.2 hxs
  have hcomm := (mem_ker_toPermHom_iff g k).1 hk _ hc
  have hcx : g.cycleOf a a = g a := cycleOf_apply_self g a
  have hcne : g.cycleOf a a ≠ a := by rw [hcx]; exact ha
  have hkx : (k : Perm α) a ∈ (g.cycleOf a).support := by
    rw [mem_support]
    intro h
    have h1 : g.cycleOf a ((k : Perm α) a) = (k : Perm α) (g.cycleOf a a) :=
      (DFunLike.congr_fun hcomm.eq a).symm
    rw [h] at h1
    exact hcne ((k : Perm α).injective h1).symm
  obtain ⟨b, b', hbb, hs⟩ := Finset.card_eq_two.1
    (card_support_eq_two_of_mem_cycleFactorsFinset ht2 hc)
  have hxs' : a ∈ (g.cycleOf a).support := mem_support.2 hcne
  have hcxs : g.cycleOf a a ∈ (g.cycleOf a).support := apply_mem_support.2 hxs'
  rw [hs, Finset.mem_insert, Finset.mem_singleton] at hxs' hcxs hkx
  change (k : Perm α) a = a ∨ (k : Perm α) a = g a
  rw [← hcx]
  grind

theorem pair_cases (ht2 : ε t * ε t = 1) {x : centralizer ({t} : Set G)} (hx : quotP ε t x = 1)
    {a : α} (ha : ε t a ≠ a) :
    (ε x a = a ∧ ε x (ε t a) = ε t a) ∨ (ε x a = ε t a ∧ ε x (ε t a) = a) := by
  have hc : ε x (ε t a) = ε t (ε x a) := DFunLike.congr_fun (map_comm x) a
  have htt : ε t (ε t a) = a := DFunLike.congr_fun ht2 a
  rcases apply_eq_or_apply_eq ht2 hx ha with h | h
  · exact .inl ⟨h, by rw [hc, h]⟩
  · exact .inr ⟨h, by rw [hc, h, htt]⟩

theorem commutatorElement_apply_eq_self (ht2 : ε t * ε t = 1) {x y : centralizer ({t} : Set G)}
    (hx : quotP ε t x = 1) (hy : quotP ε t y = 1) {a : α} (ha : ε t a ≠ a) :
    ε ((⁅x, y⁆ : centralizer ({t} : Set G)) : G) a = a := by
  have hinv : ∀ {w : centralizer ({t} : Set G)}, quotP ε t w = 1 →
      (ε w)⁻¹ a = ε w a ∧ (ε w)⁻¹ (ε t a) = ε w (ε t a) := by
    intro w hw
    rcases pair_cases ht2 hw ha with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by rw [h1, Perm.inv_eq_iff_eq, h1], by rw [h2, Perm.inv_eq_iff_eq, h2]⟩
    · exact ⟨by rw [h1, Perm.inv_eq_iff_eq, h2], by rw [h2, Perm.inv_eq_iff_eq, h1]⟩
  have hεc : ε ((⁅x, y⁆ : centralizer ({t} : Set G)) : G) =
      ε x * ε y * (ε x)⁻¹ * (ε y)⁻¹ := by
    rw [commutatorElement_def]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
  rw [hεc]
  simp only [Perm.mul_apply]
  obtain ⟨hxa, hxb⟩ := hinv hx
  obtain ⟨hya, hyb⟩ := hinv hy
  rcases pair_cases ht2 hx ha with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases pair_cases ht2 hy ha with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    simp only [hxa, hxb, hya, h1, h2, h3, h4]

@[expose] noncomputable def jointKer (ε : G →* Perm α) (t : G) :
    Subgroup (centralizer ({t} : Set G)) :=
  (quotP ε t).ker ⊓ (quotF ε t).ker

theorem jointKer_normal : (jointKer ε t).Normal := by
  unfold jointKer
  infer_instance

theorem jointKer_apply (ht2 : ε t * ε t = 1) {n : centralizer ({t} : Set G)}
    (hn : n ∈ jointKer ε t) (y : α) : ε n y = y ∨ ε n y = ε t y := by
  by_cases hy : ε t y = y
  · exact .inl ((quotF_eq_one_iff n).1 (MonoidHom.mem_ker.mp hn.2) y hy)
  · exact apply_eq_or_apply_eq ht2 (MonoidHom.mem_ker.mp hn.1) hy

theorem jointKer_mul_self (hinj : Function.Injective ε) (ht2 : ε t * ε t = 1)
    {n : centralizer ({t} : Set G)} (hn : n ∈ jointKer ε t) : n * n = 1 := by
  apply Subtype.ext
  apply hinj
  rw [Subgroup.coe_mul, Subgroup.coe_one, map_mul, map_one]
  ext y
  have hc : ε n (ε t y) = ε t (ε n y) := DFunLike.congr_fun (map_comm n) y
  have htt : ε t (ε t y) = y := DFunLike.congr_fun ht2 y
  rw [Perm.mul_apply, Perm.one_apply]
  rcases jointKer_apply ht2 hn y with h | h
  · rw [h, h]
  · rw [h, hc, h, htt]

theorem jointKer_comm (hinj : Function.Injective ε) (ht2 : ε t * ε t = 1)
    {a b : centralizer ({t} : Set G)} (ha : a ∈ jointKer ε t) (hb : b ∈ jointKer ε t) :
    a * b = b * a :=
  quot_comm hinj ht2 a b ha.1 ha.2 hb.1 hb.2

theorem exists_jointKer_eq_mul (hinj : Function.Injective ε)
    (hsurj : ∀ p ∈ alternatingGroup α, ∃ x, ε x = p) (ht2 : ε t * ε t = 1) {c d : Perm α}
    (hc : c ∈ (ε t).cycleFactorsFinset) (hd : d ∈ (ε t).cycleFactorsFinset) :
    ∃ b : centralizer ({t} : Set G), b ∈ jointKer ε t ∧ ε b = c * d := by
  have hA : c * d ∈ alternatingGroup α := by
    rw [mem_alternatingGroup, map_mul, sign_cycleFactor ht2 hc, sign_cycleFactor ht2 hd]
    rfl
  obtain ⟨x, hx⟩ := hsurj _ hA
  have hcd : c * d ∈ centralizer ({ε t} : Set (Perm α)) := by
    rw [mem_centralizer_singleton_iff]
    exact ((self_mem_cycle_factors_commute hc).mul_left (self_mem_cycle_factors_commute hd)).eq
  have hxC : x ∈ centralizer ({t} : Set G) := mem_centralizer_of_eq hinj hcd hx
  refine ⟨⟨x, hxC⟩, ⟨MonoidHom.mem_ker.mpr ?_, MonoidHom.mem_ker.mpr ?_⟩, hx⟩
  · rw [quotP_eq_one_iff]
    intro e he
    change Commute (ε x) e
    rw [hx]
    exact (cycleFactorsFinset_mem_commute' _ hc he).mul_left
      (cycleFactorsFinset_mem_commute' _ hd he)
  · rw [quotF_eq_one_iff]
    intro y hy'
    change ε x y = y
    have hny : y ∉ (ε t).support := fun h => (mem_support.mp h) hy'
    have hdy : d y = y := by
      by_contra h
      exact hny (mem_cycleFactorsFinset_support_le hd (mem_support.mpr h))
    have hcy : c y = y := by
      by_contra h
      exact hny (mem_cycleFactorsFinset_support_le hc (mem_support.mpr h))
    rw [hx, Perm.mul_apply, hdy, hcy]

theorem quotP_eq_one_of_forall_commute (hinj : Function.Injective ε)
    (hsurj : ∀ p ∈ alternatingGroup α, ∃ x, ε x = p) (ht2 : ε t * ε t = 1)
    (h3 : 3 ≤ (ε t).cycleFactorsFinset.card) {x : centralizer ({t} : Set G)}
    (hx : ∀ n ∈ jointKer ε t, x * n * x⁻¹ = n) : quotP ε t x = 1 := by
  refine Equiv.ext fun c₁ => ?_
  by_contra hne
  have hne' : quotP ε t x c₁ ≠ c₁ := hne
  set c₂ := quotP ε t x c₁ with hc₂
  obtain ⟨c₃, hc₃P, h31, h32⟩ : ∃ c₃ ∈ (ε t).cycleFactorsFinset, c₃ ≠ (c₁ : Perm α) ∧
      c₃ ≠ (c₂ : Perm α) := by
    have hcard : 0 < (((ε t).cycleFactorsFinset.erase c₁).erase c₂).card := by
      have h1 := Finset.pred_card_le_card_erase (s := (ε t).cycleFactorsFinset)
        (a := (c₁ : Perm α))
      have h2 := Finset.pred_card_le_card_erase (s := (ε t).cycleFactorsFinset.erase c₁)
        (a := (c₂ : Perm α))
      omega
    obtain ⟨c₃, hc₃⟩ := Finset.card_pos.mp hcard
    rw [Finset.mem_erase, Finset.mem_erase] at hc₃
    exact ⟨c₃, hc₃.2.2, hc₃.2.1, hc₃.1⟩
  set c₄ := quotP ε t x ⟨c₃, hc₃P⟩ with hc₄
  have h42 : (c₄ : Perm α) ≠ c₂ := by
    intro h
    have h' := (quotP ε t x).injective (Subtype.ext h : c₄ = c₂)
    exact h31 (congrArg Subtype.val h')
  obtain ⟨b, hbN, hb⟩ := exists_jointKer_eq_mul hinj hsurj ht2 c₁.2 hc₃P
  have hεb : ε x * ((c₁ : Perm α) * c₃) * (ε x)⁻¹ = (c₁ : Perm α) * c₃ := by
    have h := congrArg (fun w : centralizer ({t} : Set G) => ε (w : G)) (hx b hbN)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hb] at h
    exact h
  have hε : ε x * ((c₁ : Perm α) * c₃) * (ε x)⁻¹ = (c₂ : Perm α) * c₄ := by
    have e1 : ε x * (c₁ : Perm α) * (ε x)⁻¹ = c₂ := (quotP_apply_coe x c₁).symm
    have e3 : ε x * c₃ * (ε x)⁻¹ = c₄ := (quotP_apply_coe x ⟨c₃, hc₃P⟩).symm
    calc ε x * ((c₁ : Perm α) * c₃) * (ε x)⁻¹
        = (ε x * c₁ * (ε x)⁻¹) * (ε x * c₃ * (ε x)⁻¹) := by group
      _ = c₂ * c₄ := by rw [e1, e3]
  rw [hε] at hεb
  obtain ⟨a, ha⟩ : ∃ a, (c₂ : Perm α) a ≠ a := by
    by_contra h
    push Not at h
    exact (mem_cycleFactorsFinset_iff.1 c₂.2).1.ne_one (Equiv.ext h)
  have hdisj := cycleFactorsFinset_pairwise_disjoint (ε t)
  have hd21 : Disjoint (c₂ : Perm α) c₁ := hdisj c₂.2 c₁.2 (fun h => hne' (Subtype.ext h))
  have hd23 : Disjoint (c₂ : Perm α) c₃ := hdisj c₂.2 hc₃P (fun h => h32 h.symm)
  have hd24 : Disjoint (c₂ : Perm α) c₄ := hdisj c₂.2 c₄.2 (fun h => h42 h.symm)
  have h1a : (c₁ : Perm α) a = a := (hd21 a).resolve_left ha
  have h3a : c₃ a = a := (hd23 a).resolve_left ha
  have h4a : (c₄ : Perm α) a = a := (hd24 a).resolve_left ha
  have h := DFunLike.congr_fun hεb a
  rw [Perm.mul_apply, Perm.mul_apply, h4a, h3a, h1a] at h
  exact ha h

theorem quotP_eq_one_of_card_le_two (h2 : (ε t).cycleFactorsFinset.card ≤ 2)
    {x : centralizer ({t} : Set G)} (hodd : Odd (orderOf x)) : quotP ε t x = 1 := by
  have hdvd1 : orderOf (quotP ε t x) ∣ orderOf x := orderOf_map_dvd _ _
  have hdvd2 : orderOf (quotP ε t x) ∣ Nat.card (Perm (ε t).cycleFactorsFinset) :=
    orderOf_dvd_natCard _
  rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_coe] at hdvd2
  set k := (ε t).cycleFactorsFinset.card with hk
  have hf : k.factorial ∣ 2 := by
    interval_cases k <;> decide
  have hodd' : Odd (orderOf (quotP ε t x)) := Odd.of_dvd_nat hodd hdvd1
  rw [← orderOf_eq_one_iff]
  rcases (Nat.dvd_prime Nat.prime_two).mp (hdvd2.trans hf) with h1 | h1
  · exact h1
  · rw [h1] at hodd'
    exact absurd hodd' (by decide)

end Perm

end CFSG.ComponentClassification.HarrisLit.T1.RowAlt
