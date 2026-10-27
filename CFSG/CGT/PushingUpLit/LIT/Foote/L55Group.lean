module

import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG.Open (IsElemAbelian)

variable {G : Type} [Group G]

theorem exists_involution_mem_zpowers {a : G} (h2 : ∃ n : ℕ, a ^ 2 ^ n = 1) (h1 : a ≠ 1) :
    ∃ i ∈ Subgroup.zpowers a, i ≠ 1 ∧ i * i = 1 := by
  obtain ⟨n, hn⟩ := h2
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hn)
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact h1 (orderOf_eq_one_iff.1 (by simpa using hj))
  refine ⟨a ^ 2 ^ (j - 1), Subgroup.pow_mem _ (Subgroup.mem_zpowers a) _, ?_, ?_⟩
  · intro h
    have hd := orderOf_dvd_of_pow_eq_one h
    rw [hj] at hd
    have h3 := Nat.le_of_dvd (by positivity) hd
    have h4 : 2 ^ (j - 1) < 2 ^ j := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  · rw [← pow_add, ← two_mul, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hj0),
      ← hj]
    exact pow_orderOf_eq_one a

theorem isElemAbelian_of_le {V E : Subgroup G} (hV : IsElemAbelian 2 V) (hEV : E ≤ V) :
    IsElemAbelian 2 E := CFSG.Open.IsElemAbelian.mono hV hEV

theorem isElemAbelian_map {E : Subgroup G} (hE : IsElemAbelian 2 E) (f : G ≃* G) :
    IsElemAbelian 2 (E.map f.toMonoidHom) := CFSG.Open.IsElemAbelian.map hE _

section Finite

variable [Finite G]

theorem exists_ne_one_commute_of_normal {T X : Subgroup G}
    (hT : IsPGroup 2 T) (hXT : X ≤ T) (hXn : ∀ t ∈ T, ∀ x ∈ X, t * x * t⁻¹ ∈ X) (hX : X ≠ ⊥) :
    ∃ x ∈ X, x ≠ 1 ∧ ∀ t ∈ T, t * x = x * t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent ↥T := hT.isNilpotent
  let X' : Subgroup ↥T := X.subgroupOf T
  have hX'n : X'.Normal := ⟨fun x hx t => by
    show ((t * x * t⁻¹ : ↥T) : G) ∈ X
    have : ((t * x * t⁻¹ : ↥T) : G) = (t : G) * (x : G) * (t : G)⁻¹ := rfl
    rw [this]
    exact hXn t t.2 x hx⟩
  have hX'ne : X' ≠ ⊥ := by
    intro h
    apply hX
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hXT hx⟩ : ↥T) ∈ X' := hx
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  have hne := Group.IsNilpotent.inf_center_ne_bot_of_normal hX'ne
  obtain ⟨z, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hzX : ((z : ↥T) : G) ∈ X := (Subgroup.mem_inf.1 z.2).1
  have hzc := Subgroup.mem_center_iff.1 (Subgroup.mem_inf.1 z.2).2
  refine ⟨((z : ↥T) : G), hzX, fun h => hz1 (Subtype.ext (Subtype.ext h)), fun t ht => ?_⟩
  exact congrArg Subtype.val (hzc ⟨t, ht⟩)

theorem exists_fourGroup_centralizer {V : Subgroup G}
    (hV : IsElemAbelian 2 V) {t : G} (ht : t * t = 1) (htV : ∀ v ∈ V, t * v * t⁻¹ ∈ V)
    (h8 : 8 ≤ Nat.card V) :
    ∃ E : Subgroup G, E ≤ V ∧ IsElemAbelian 2 E ∧ Nat.card E = 4 ∧ ∀ e ∈ E, e * t = t * e := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm : ∀ u ∈ V, ∀ v ∈ V, u * v = v * u := fun u hu v hv => by
    have := hV.1
    exact setLike_mul_comm hu hv
  have hsq : ∀ v ∈ V, v * v = 1 := fun v hv => by simpa [pow_two] using hV.2 v hv
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  set C : Subgroup G := V ⊓ Subgroup.centralizer ({t} : Set G) with hC
  let f : ↥V →* ↥V := MonoidHom.mk'
    (fun v => ⟨(v : G) * (t * (v : G) * t⁻¹), V.mul_mem v.2 (htV v v.2)⟩) (by
      intro u v
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      have hav : (t * (u : G) * t⁻¹) * (v : G) = (v : G) * (t * (u : G) * t⁻¹) :=
        hcomm _ (htV u u.2) v v.2
      calc (u : G) * v * (t * ((u : G) * v) * t⁻¹)
          = (u : G) * (v * (t * (u : G) * t⁻¹)) * (t * (v : G) * t⁻¹) := by group
        _ = (u : G) * ((t * (u : G) * t⁻¹) * v) * (t * (v : G) * t⁻¹) := by rw [hav]
        _ = (u : G) * (t * (u : G) * t⁻¹) * ((v : G) * (t * (v : G) * t⁻¹)) := by group)
  have hfv : ∀ v : ↥V, ((f v : ↥V) : G) = (v : G) * (t * (v : G) * t⁻¹) := fun v => rfl
  have hker : f.ker ≤ C.subgroupOf V := by
    intro v hv
    rw [MonoidHom.mem_ker] at hv
    have h1 : (v : G) * (t * (v : G) * t⁻¹) = 1 := by
      have := congrArg Subtype.val hv
      rw [hfv] at this
      simpa using this
    have h2 : t * (v : G) * t⁻¹ = (v : G) := by
      have hvi : (v : G) * (v : G) = 1 := hsq v v.2
      have h3 : t * (v : G) * t⁻¹ = (v : G)⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [h3]
      exact inv_eq_of_mul_eq_one_right hvi
    refine Subgroup.mem_subgroupOf.2 ⟨v.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    calc (v : G) * t = (t * (v : G) * t⁻¹) * t := by rw [h2]
      _ = t * (v : G) := by group
  have hrange : f.range ≤ C.subgroupOf V := by
    rintro _ ⟨v, rfl⟩
    have hv' := htV v v.2
    have hcv : (v : G) * (t * (v : G) * t⁻¹) = (t * (v : G) * t⁻¹) * (v : G) :=
      hcomm _ v.2 _ hv'
    refine Subgroup.mem_subgroupOf.2 ⟨(f v).2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    rw [hfv]
    calc ((v : G) * (t * (v : G) * t⁻¹)) * t
        = ((t * (v : G) * t⁻¹) * (v : G)) * t := by rw [hcv]
      _ = (t * (v : G) * t⁻¹) * (t * t * (v : G) * (t * t)⁻¹) * t := by rw [ht]; group
      _ = t * ((v : G) * (t * (v : G) * t⁻¹)) := by group
  have hcardC : Nat.card ↥(C.subgroupOf V) = Nat.card ↥C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hmul := Subgroup.card_ker_mul_card_range f
  have hle : Nat.card ↥V ≤ Nat.card ↥C * Nat.card ↥C := by
    rw [← hmul, ← hcardC]
    exact Nat.mul_le_mul (Subgroup.card_le_of_le hker) (Subgroup.card_le_of_le hrange)
  have h3 : 3 ≤ Nat.card ↥C := by
    by_contra hlt
    push Not at hlt
    have : Nat.card ↥C * Nat.card ↥C ≤ 2 * 2 := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hCp : IsPGroup 2 ↥C := fun g => ⟨1, Subtype.ext (by
    have hg : (g : G) ∈ V := (Subgroup.mem_inf.1 g.2).1
    simpa [pow_two] using hsq g hg)⟩
  obtain ⟨n, hn⟩ := hCp.exists_card_eq
  have hn2 : 2 ≤ n := by
    by_contra hlt
    push Not at hlt
    have h4 : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hn] at h3
    omega
  have hdvd : 2 ^ 2 ∣ Nat.card ↥C := by
    rw [hn]
    exact pow_dvd_pow 2 hn2
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥C) 2 hdvd
  refine ⟨K.map C.subtype, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact (Subgroup.mem_inf.1 x.2).1
  · refine isElemAbelian_of_le hV ?_
    rintro _ ⟨x, -, rfl⟩
    exact (Subgroup.mem_inf.1 x.2).1
  · rw [Subgroup.card_map_of_injective C.subtype_injective, hK]
    norm_num
  · rintro _ ⟨x, -, rfl⟩
    have := (Subgroup.mem_inf.1 x.2).2
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact this

end Finite

end CFSG.CGT.PushingUpLit.LIT.Foote
