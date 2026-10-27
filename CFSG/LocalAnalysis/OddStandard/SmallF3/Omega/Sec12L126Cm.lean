module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Blueprint.Chevalley
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec126_comm_mem {V : Subgroup G} (hV : CFSG.Open.IsElemAbelian 2 V) {s : G}
    (hs : s * s = 1) (hsN : s ∈ normalizer (V : Set G)) {v : G} (hv : v ∈ V) :
    s * v * s⁻¹ * v⁻¹ ∈ V ⊓ centralizer ({s} : Set G) := by
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hsv : s * v * s⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hsN v).mp hv
  have hv2 : v * v = 1 := hV.mul_self_eq_one hv
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have hcomm : v * (s * v * s⁻¹) = (s * v * s⁻¹) * v :=
    hV.comm hv hsv
  rw [Subgroup.mem_inf]
  refine ⟨V.mul_mem hsv (V.inv_mem hv), ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff, hvi, hsi]
  rw [hsi] at hcomm
  symm
  calc s * (s * v * s * v) = (s * s) * v * s * v := by simp only [mul_assoc]
    _ = v * s * v := by rw [hs, one_mul]
    _ = v * s * v * (s * s) := by rw [hs, mul_one]
    _ = (v * (s * v * s)) * s := by simp only [mul_assoc]
    _ = (s * v * s * v) * s := by rw [hcomm]

theorem sec126_conj_mem {V : Subgroup G} (hV : CFSG.Open.IsElemAbelian 2 V) {s : G}
    (hs : s * s = 1) (hsN : s ∈ normalizer (V : Set G)) {v : G} (hv : v ∈ V) :
    ∃ d ∈ V ⊓ centralizer ({s} : Set G), v * s * v⁻¹ = d * s := by
  refine ⟨(s * v * s⁻¹ * v⁻¹)⁻¹, Subgroup.inv_mem _ (sec126_comm_mem hV hs hsN hv), ?_⟩
  group

theorem sec126_exists_commMap {V : Subgroup G} (hV : CFSG.Open.IsElemAbelian 2 V) {s : G}
    (hs : s * s = 1) (hsN : s ∈ normalizer (V : Set G)) :
    ∃ ρ : ↥V →* ↥V, ∀ v : ↥V, ((ρ v : ↥V) : G) = s * v * s⁻¹ * (v : G)⁻¹ := by
  refine ⟨MonoidHom.mk' (fun v : ↥V => ⟨s * v * s⁻¹ * (v : G)⁻¹,
    (sec126_comm_mem hV hs hsN v.2).1⟩) ?_, fun v => rfl⟩
  intro a b
  apply Subtype.ext
  have ha' : s * (a : G) * s⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hsN a).mp a.2
  have hb' : s * (b : G) * s⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hsN b).mp b.2
  have hc := hV.comm (V.mul_mem hb' (V.inv_mem b.2)) (V.inv_mem a.2)
  change s * ((a : G) * b) * s⁻¹ * ((a : G) * b)⁻¹ =
    s * (a : G) * s⁻¹ * (a : G)⁻¹ * (s * (b : G) * s⁻¹ * (b : G)⁻¹)
  calc s * ((a : G) * b) * s⁻¹ * ((a : G) * b)⁻¹
      = (s * (a : G) * s⁻¹) * ((s * (b : G) * s⁻¹) * (b : G)⁻¹ * (a : G)⁻¹) := by group
    _ = (s * (a : G) * s⁻¹) * ((a : G)⁻¹ * ((s * (b : G) * s⁻¹) * (b : G)⁻¹)) := by rw [hc]
    _ = _ := by group

theorem sec126_card_le_sq [Finite G] {V : Subgroup G} (hV : CFSG.Open.IsElemAbelian 2 V)
    {s : G} (hs : s * s = 1) (hsN : s ∈ normalizer (V : Set G)) :
    Nat.card ↥V ≤ Nat.card ↥(V ⊓ centralizer ({s} : Set G)) ^ 2 := by
  obtain ⟨ρ, hρ⟩ := sec126_exists_commMap hV hs hsN
  set D : Subgroup G := V ⊓ centralizer ({s} : Set G) with hD
  have hDV : D ≤ V := inf_le_left
  have hker : ρ.ker = D.subgroupOf V := by
    ext v
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hD, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h' : s * (v : G) * s⁻¹ * (v : G)⁻¹ = 1 := by rw [← hρ, h]; rfl
      refine ⟨v.2, ?_⟩
      calc (v : G) * s = (s * (v : G) * s⁻¹ * (v : G)⁻¹) * ((v : G) * s) := by rw [h', one_mul]
        _ = s * v := by group
    · rintro ⟨-, h⟩
      apply Subtype.ext
      rw [hρ]
      change _ = (1 : G)
      rw [← h]
      group
  have hrange : ρ.range ≤ D.subgroupOf V := by
    rintro _ ⟨v, rfl⟩
    rw [Subgroup.mem_subgroupOf, hρ]
    exact sec126_comm_mem hV hs hsN v.2
  have hcard : Nat.card ↥(D.subgroupOf V) = Nat.card ↥D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDV).toEquiv
  have h1 := Subgroup.card_ker_mul_card_range ρ
  rw [hker, hcard] at h1
  have h2 : Nat.card ↥ρ.range ≤ Nat.card ↥D := by
    rw [← hcard]; exact Subgroup.card_le_of_le hrange
  rw [← h1, pow_two]
  exact Nat.mul_le_mul le_rfl h2

theorem sec126_exists_conj [Finite G] {V : Subgroup G} (hV : CFSG.Open.IsElemAbelian 2 V)
    {s : G} (hs : s * s = 1) (hsN : s ∈ normalizer (V : Set G))
    (hc : Nat.card ↥V = Nat.card ↥(V ⊓ centralizer ({s} : Set G)) ^ 2) {d : G}
    (hd : d ∈ V ⊓ centralizer ({s} : Set G)) : ∃ v ∈ V, v⁻¹ * s * v = s * d := by
  obtain ⟨ρ, hρ⟩ := sec126_exists_commMap hV hs hsN
  set D : Subgroup G := V ⊓ centralizer ({s} : Set G) with hD
  have hDV : D ≤ V := inf_le_left
  have hker : ρ.ker = D.subgroupOf V := by
    ext v
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hD, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h' : s * (v : G) * s⁻¹ * (v : G)⁻¹ = 1 := by rw [← hρ, h]; rfl
      refine ⟨v.2, ?_⟩
      calc (v : G) * s = (s * (v : G) * s⁻¹ * (v : G)⁻¹) * ((v : G) * s) := by rw [h', one_mul]
        _ = s * v := by group
    · rintro ⟨-, h⟩
      apply Subtype.ext
      rw [hρ]
      change _ = (1 : G)
      rw [← h]
      group
  have hrange : ρ.range ≤ D.subgroupOf V := by
    rintro _ ⟨v, rfl⟩
    rw [Subgroup.mem_subgroupOf, hρ]
    exact sec126_comm_mem hV hs hsN v.2
  have hcard : Nat.card ↥(D.subgroupOf V) = Nat.card ↥D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDV).toEquiv
  have h1 := Subgroup.card_ker_mul_card_range ρ
  rw [hker, hcard, hc, pow_two] at h1
  have hpos : 0 < Nat.card ↥D := Nat.card_pos
  have h3 : Nat.card ↥ρ.range = Nat.card ↥D := Nat.eq_of_mul_eq_mul_left hpos h1
  have hr : ρ.range = D.subgroupOf V := by
    refine Subgroup.eq_of_le_of_card_ge hrange ?_
    rw [hcard, h3]
  have hdV : (⟨d, hDV hd⟩ : ↥V) ∈ ρ.range := by
    rw [hr, Subgroup.mem_subgroupOf]
    exact hd
  obtain ⟨v, hv⟩ := hdV
  have hv' : s * (v : G) * s⁻¹ * (v : G)⁻¹ = d := by rw [← hρ, hv]
  have hv2 : (v : G) * v = 1 := hV.mul_self_eq_one v.2
  have hvi : (v : G)⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  refine ⟨v, v.2, ?_⟩
  rw [← hv', hvi, hsi]
  calc (v : G) * s * v = (s * s) * v * s * v := by rw [hs, one_mul]
    _ = s * (s * v * s * v) := by simp only [mul_assoc]

end CFSG.OddStandard.SmallF3.Omega
