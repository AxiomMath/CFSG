module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecShape3Basic
public import CFSG.LocalAnalysis.OddStandard.AltStdBalSigma

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup CFSG.OddStandard.AltStdBal

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

theorem false_of_sylow_shape3_aux (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    {u : G} (hu : u ∈ centralizer ({z} : Set G)) (huL : u ∉ L ⊔ Q) (hu2 : u ^ 2 = z)
    (S : Sylow 2 G) (hSC : (S : Subgroup G) ≤ centralizer ({z} : Set G))
    (huS : u ∈ (S : Subgroup G)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsimple := h.std.simple
  have hnonab := h.std.nonab
  set U : Subgroup G := (S : Subgroup G) ⊓ (L ⊔ Q) with hU
  have hUT : U ≤ (S : Subgroup G) := inf_le_left
  have hUdvd : U.relIndex (S : Subgroup G) ∣ 2 := by
    rw [relIndex_dvd_two_iff']
    refine ⟨u⁻¹, (S : Subgroup G).inv_mem huS, fun b hb => ?_⟩
    rcases mem_sup_or_inv_mul_mem_sup h d hu huL (hSC hb) with hb' | hb'
    · exact Or.inr ⟨hb, hb'⟩
    · exact Or.inl ⟨(S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem huS) hb, hb'⟩
  have huU : u ∉ U := fun hmem => huL hmem.2
  have hUidx : U.relIndex (S : Subgroup G) = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hUdvd with h1 | h2
    · exfalso
      exact huU ((relIndex_eq_one.1 h1) huS)
    · exact h2
  have hu4 : orderOf u = 4 := orderOf_eq_four_of_sq_eq d hu2
  have hmin : ∀ y ∈ (S : Subgroup G), y ∉ U → orderOf u ≤ orderOf y := by
    intro y hyS hyU
    have hyL : y ∉ L ⊔ Q := fun hmem => hyU ⟨hyS, hmem⟩
    have hyC : y ∈ centralizer ({z} : Set G) := hSC hyS
    have h1 : u⁻¹ * y ∈ L ⊔ Q := by
      rcases mem_sup_or_inv_mul_mem_sup h d hu huL hyC with h1 | h1
      · exact absurd h1 hyL
      · exact h1
    have hy2 : ¬ y * y = 1 := by
      intro hy1
      have hc' := inv_conj_mul_mem_L h d hQ2 hu h1
      have hyy : y * y = z * (u⁻¹ * (u⁻¹ * y) * u * (u⁻¹ * y)) := by
        calc y * y = (u * (u⁻¹ * y)) * (u * (u⁻¹ * y)) := by group
          _ = (u * u) * (u⁻¹ * (u⁻¹ * y) * u * (u⁻¹ * y)) := by group
          _ = z * (u⁻¹ * (u⁻¹ * y) * u * (u⁻¹ * y)) := by rw [← sq, hu2]
      rw [hyy] at hy1
      have : z = (u⁻¹ * (u⁻¹ * y) * u * (u⁻¹ * y))⁻¹ := eq_inv_of_mul_eq_one_left hy1
      exact z_not_mem_L h d (by rw [this]; exact inv_mem hc')
    have hy1 : y ≠ 1 := fun h1 => hyU (h1 ▸ U.one_mem)
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 S.isPGroup' (⟨y, hyS⟩ : (S : Subgroup G))
    have hk' : orderOf y = 2 ^ k :=
      (Subgroup.orderOf_coe (⟨y, hyS⟩ : (S : Subgroup G))).trans hk
    rw [hu4, hk']
    have hk2 : 2 ≤ k := by
      by_contra hlt
      push Not at hlt
      interval_cases k
      · exact hy1 (orderOf_eq_one_iff.1 (by simpa using hk'))
      · apply hy2
        have : orderOf y = 2 := by simpa using hk'
        rw [← sq]
        exact pow_orderOf_eq_one y ▸ (by rw [this])
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
  have hconj : ∀ g : G, g⁻¹ * u * g ∉ U := by
    intro g hg
    have hsq := sq_mem_L_of_mem_sup d hQ2 hg.2
    have : (g⁻¹ * u * g) ^ 2 = g⁻¹ * z * g := by
      rw [← hu2, sq, sq]
      group
    rw [this] at hsq
    have := not_conj_mem_L h d hQ2 g⁻¹
    rw [inv_inv] at this
    exact this hsq
  obtain ⟨N, hN, hNidx⟩ := ThompsonIndexTwo.exists_normal_index_two_of_thompson S.isPGroup'
    S.not_dvd_index hUT hUidx huS huU hmin hconj
  rcases hN.eq_bot_or_eq_top with h1 | h1
  · rw [h1, Subgroup.index_bot] at hNidx
    have := isCyclic_of_prime_card (α := G) hNidx
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (IsCyclic.commGroup.mul_comm a b)
  · rw [h1, Subgroup.index_top] at hNidx
    exact absurd hNidx (by norm_num)

theorem not_le_centralizer_of_sylow_shape3 (h : Setting G L n) (d : Cyc L Q z)
    (hQ2 : Nat.card Q = 2) {u : G} (hu : u ∈ centralizer ({z} : Set G)) (huL : u ∉ L ⊔ Q)
    (hu2 : u ^ 2 = z) (S : Sylow 2 G) :
    ¬ (S : Subgroup G) ≤ centralizer ({z} : Set G) := by
  classical
  intro hSC
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({z} : Set G) with hC
  have hu4 : orderOf u = 4 := orderOf_eq_four_of_sq_eq d hu2
  have hSp : IsPGroup 2 ((S : Subgroup G).subgroupOf C) :=
    S.isPGroup'.of_equiv (subgroupOfEquivOfLe hSC).symm
  have hSidx : ¬ 2 ∣ ((S : Subgroup G).subgroupOf C).index := by
    intro hd
    have h1 := Subgroup.relIndex_mul_index hSC
    apply S.not_dvd_index
    rw [← h1]
    exact Dvd.dvd.mul_right hd _
  let SC : Sylow 2 C := hSp.toSylow hSidx
  have hSCeq : (SC : Subgroup C) = (S : Subgroup G).subgroupOf C :=
    IsPGroup.toSylow_coe hSp hSidx
  have hup : IsPGroup 2 (zpowers (⟨u, hu⟩ : C)) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hu4]; norm_num)
  obtain ⟨P, hP⟩ := hup.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C P SC
  have hcu : c * (⟨u, hu⟩ : C) * c⁻¹ ∈ (SC : Subgroup C) := by
    rw [← hc, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨_, hP (mem_zpowers _), by simp [MulAut.conj_apply]⟩
  rw [hSCeq, Subgroup.mem_subgroupOf] at hcu
  have hcu' : (c : G) * u * (c : G)⁻¹ ∈ (S : Subgroup G) := by simpa using hcu
  have hcC : (c : G) ∈ C := c.2
  have hu'C : (c : G) * u * (c : G)⁻¹ ∈ C :=
    C.mul_mem (C.mul_mem hcC hu) (C.inv_mem hcC)
  have hu'L : (c : G) * u * (c : G)⁻¹ ∉ L ⊔ Q := by
    intro hmem
    apply huL
    have := conj_mem_sup h d hQ2 (C.inv_mem hcC) hmem
    simpa [mul_assoc] using this
  have hu'2 : ((c : G) * u * (c : G)⁻¹) ^ 2 = z := by
    have hzc : (c : G) * z * (c : G)⁻¹ = z := by
      have := mem_centralizer_singleton_iff.1 hcC
      calc (c : G) * z * (c : G)⁻¹ = z * (c : G) * (c : G)⁻¹ := by rw [← this]
        _ = z := by group
    calc ((c : G) * u * (c : G)⁻¹) ^ 2 = (c : G) * u ^ 2 * (c : G)⁻¹ := by
          rw [sq, sq]; group
      _ = z := by rw [hu2, hzc]
  exact false_of_sylow_shape3_aux h d hQ2 hu'C hu'L hu'2 S hSC hcu'

theorem exists_growth_shape3 (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    {u : G} (hu : u ∈ centralizer ({z} : Set G)) (huL : u ∉ L ⊔ Q) (hu2 : u ^ 2 = z)
    {R : Subgroup G} (hRC : R ≤ centralizer ({z} : Set G)) (hR : IsPGroup 2 R)
    (hRmax : ∀ R' : Subgroup G, R' ≤ centralizer ({z} : Set G) → IsPGroup 2 R' → R ≤ R' →
      R' = R) :
    ∃ x y₀ : G, (∀ r ∈ R, x * r * x⁻¹ ∈ R) ∧ (∀ r ∈ R, x⁻¹ * r * x ∈ R) ∧ y₀ ∈ R ∧ y₀ ∈ L ∧
      y₀ ≠ 1 ∧ y₀ * y₀ = 1 ∧ (∀ r ∈ R, r * y₀ = y₀ * r) ∧ x * z * x⁻¹ = y₀ * z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzR : z ∈ R := mem_of_maximal d hRC hR hRmax
  have hzz := d.mul_self
  obtain ⟨S, hRS⟩ := hR.exists_le_sylow
  have hne : R ≠ (S : Subgroup G) := fun hRS' =>
    not_le_centralizer_of_sylow_shape3 h d hQ2 hu huL hu2 S (hRS' ▸ hRC)
  have hnil : Group.IsNilpotent (S : Subgroup G) := S.isPGroup'.isNilpotent
  have hlt : R.subgroupOf (S : Subgroup G) < ⊤ := by
    refine lt_top_iff_ne_top.2 fun htop => hne ?_
    refine le_antisymm hRS fun s hs => ?_
    have : (⟨s, hs⟩ : (S : Subgroup G)) ∈ R.subgroupOf (S : Subgroup G) := by
      rw [htop]
      trivial
    exact this
  have hgrow := Group.normalizerCondition_of_isNilpotent (G := (S : Subgroup G))
    (R.subgroupOf (S : Subgroup G)) hlt
  obtain ⟨⟨x, hxS⟩, hxN, hxH⟩ := IsConcreteLE.exists_of_lt hgrow
  have hxR : x ∉ R := fun hx => hxH hx
  have hconj : ∀ r ∈ R, x * r * x⁻¹ ∈ R := fun r hr =>
    (mem_normalizer_iff.1 hxN ⟨r, hRS hr⟩).1 hr
  have hconj' : ∀ r ∈ R, x⁻¹ * r * x ∈ R := by
    intro r hr
    have hS' : x⁻¹ * r * x ∈ (S : Subgroup G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hxS) (hRS hr)) hxS
    have h1 := (mem_normalizer_iff.1 hxN ⟨x⁻¹ * r * x, hS'⟩).2
    have h2 : x * (x⁻¹ * r * x) * x⁻¹ = r := by group
    have h3 : x * (x⁻¹ * r * x) * x⁻¹ ∈ R := by
      rw [h2]
      exact hr
    exact h1 h3
  set w := x * z * x⁻¹ with hw
  have hwR : w ∈ R := hconj z hzR
  have hwC : ∀ r ∈ R, r * w = w * r := by
    intro r hr
    have hzc : (x⁻¹ * r * x) * z = z * (x⁻¹ * r * x) :=
      mem_centralizer_singleton_iff.1 (hRC (hconj' r hr))
    calc r * w = x * ((x⁻¹ * r * x) * z) * x⁻¹ := by rw [hw]; group
      _ = x * (z * (x⁻¹ * r * x)) * x⁻¹ := by rw [hzc]
      _ = w * r := by rw [hw]; group
  have hwne : w ≠ z := by
    intro hwz
    apply hxR
    have hxC : x ∈ centralizer ({z} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc x * z = x * z * x⁻¹ * x := by group
        _ = z * x := by rw [← hw, hwz]
    have hle : R ⊔ Subgroup.zpowers x ≤ (S : Subgroup G) :=
      sup_le hRS (Subgroup.zpowers_le.2 hxS)
    have hp : IsPGroup 2 ↥(R ⊔ Subgroup.zpowers x) := S.isPGroup'.to_le hle
    have hC : R ⊔ Subgroup.zpowers x ≤ centralizer ({z} : Set G) :=
      sup_le hRC (Subgroup.zpowers_le.2 hxC)
    have := hRmax _ hC hp le_sup_left
    rw [← this]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hww : w * w = 1 := by
    rw [hw]
    calc x * z * x⁻¹ * (x * z * x⁻¹) = x * (z * z) * x⁻¹ := by group
      _ = 1 := by rw [hzz]; group
  have hwL : w ∉ L := not_conj_mem_L h d hQ2 x
  obtain ⟨l, hl, hwl⟩ : ∃ l ∈ L, w = l * z := by
    by_cases hwQ : w ∈ L ⊔ Q
    · obtain ⟨l, hl, q, hq, hlq⟩ := (mem_sup_iff_mul d).1 hwQ
      rcases eq_one_or_eq_of_card_eq_two d hQ2 hq with rfl | rfl
      · exact absurd (by rw [← hlq, mul_one]; exact hl) hwL
      · exact ⟨l, hl, hlq.symm⟩
    · exfalso
      obtain ⟨l, hl, hwl⟩ := sq_mem_mul_L_of_outer h d hQ2 hu huL hu2 (hRC hwR) hwQ
      rw [hww] at hwl
      apply z_not_mem_L h d
      have : z = l⁻¹ := by
        have h1 : z * l = 1 := hwl.symm
        exact eq_inv_of_mul_eq_one_left h1
      rw [this]
      exact inv_mem hl
  have hlz : l * z = z * l := mem_centralizer_singleton_iff.1 (le_centralizer_single h d hl)
  have hlw : l = w * z := by rw [hwl, mul_assoc, hzz, mul_one]
  refine ⟨x, l, hconj, hconj', hlw ▸ Subgroup.mul_mem _ hwR hzR, hl, ?_, ?_, ?_, hwl⟩
  · intro hl1
    apply hwne
    rw [hwl, hl1, one_mul]
  · have h1 : (l * z) * (l * z) = 1 := by rw [← hwl]; exact hww
    calc l * l = (l * z) * (l * z) * (z * z)⁻¹ := by
          rw [hzz]
          calc l * l = l * (z * z) * l := by rw [hzz]; group
            _ = l * z * (z * l) := by group
            _ = (l * z) * (l * z) := by rw [← hlz]
            _ = _ := by group
      _ = 1 := by rw [h1, hzz]; group
  · intro r hr
    have hrz : r * z = z * r := mem_centralizer_singleton_iff.1 (hRC hr)
    rw [hlw]
    calc r * (w * z) = (r * w) * z := by group
      _ = (w * r) * z := by rw [hwC r hr]
      _ = w * (r * z) := by group
      _ = w * (z * r) := by rw [hrz]
      _ = (w * z) * r := by group

end CFSG.OddStandard.AltStdSec
