module

public import CFSG.GH74.GLS.C3.Prop121.CzCoord
public import CFSG.Dihedral.Glauberman.DicksonMaxExist

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Subgroup Equiv Perm CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer2.Model

theorem isSylow_of_maximal_central {M : Type*} [Group M] [Finite M] {D : Subgroup M}
    (hD : IsPGroup 2 D) {z : M} (hDz : ∀ d ∈ D, d * z = z * d)
    (hzn : ∀ m ∈ Subgroup.normalizer (D : Set M), m * z = z * m)
    (hmax : ∀ P : Subgroup M, IsPGroup 2 P → D ≤ P → (∀ p ∈ P, p * z = z * p) → P = D) :
    ∃ P : Sylow 2 M, (P : Subgroup M) = D := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hDP⟩ := hD.exists_le_sylow
  refine ⟨P, le_antisymm ?_ hDP⟩
  by_contra hnot
  have hPnil : Group.IsNilpotent ↥(P : Subgroup M) := (P.isPGroup').isNilpotent
  let D' : Subgroup ↥(P : Subgroup M) := D.subgroupOf (P : Subgroup M)
  have hD'top : D' < ⊤ := by
    refine lt_top_iff_ne_top.2 (fun htop => hnot ?_)
    intro p hp
    have : (⟨p, hp⟩ : ↥(P : Subgroup M)) ∈ D' := by rw [htop]; trivial
    exact this
  have hnc : D' < Subgroup.normalizer (D' : Set ↥(P : Subgroup M)) :=
    Group.normalizerCondition_of_isNilpotent D' hD'top
  obtain ⟨n, hn, hnD'⟩ := IsConcreteLE.exists_of_lt hnc
  have hnN : (n : M) ∈ Subgroup.normalizer (D : Set M) := by
    rw [Subgroup.mem_normalizer_iff]
    intro d
    constructor
    · intro hd
      exact (Subgroup.mem_normalizer_iff.1 hn ⟨d, hDP hd⟩).1 hd
    · intro hd
      have hdP : d ∈ (P : Subgroup M) := by
        have h1 : (n : M)⁻¹ * ((n : M) * d * (n : M)⁻¹) * (n : M) ∈ (P : Subgroup M) :=
          P.mul_mem (P.mul_mem (P.inv_mem n.2) (hDP hd)) n.2
        have e : (n : M)⁻¹ * ((n : M) * d * (n : M)⁻¹) * (n : M) = d := by group
        rwa [e] at h1
      exact (Subgroup.mem_normalizer_iff.1 hn ⟨d, hdP⟩).2 hd
  have hP'P : D ⊔ Subgroup.zpowers (n : M) ≤ (P : Subgroup M) :=
    sup_le hDP (Subgroup.zpowers_le.2 n.2)
  have hle : D ⊔ Subgroup.zpowers (n : M) ≤ Subgroup.centralizer ({z} : Set M) :=
    sup_le (fun d hd => Subgroup.mem_centralizer_singleton_iff.2 (hDz d hd))
      (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 (hzn _ hnN)))
  have h1 := hmax (D ⊔ Subgroup.zpowers (n : M)) (P.isPGroup'.to_le hP'P) le_sup_left
    (fun p hp => Subgroup.mem_centralizer_singleton_iff.1 (hle hp))
  have h2 : (n : M) ∈ D ⊔ Subgroup.zpowers (n : M) :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  rw [h1] at h2
  exact hnD' h2

section Config

variable {G : Type} [Group G] [Finite G] {n : ℕ} {x : G} {K T Q S : Subgroup G} {a : G}

omit [Finite G] in
theorem card_inf_conj (g a b : G) :
    Nat.card ↥(centralizer ({g * a * g⁻¹} : Set G) ⊓ centralizer ({g * b * g⁻¹} : Set G)) =
      Nat.card ↥(centralizer ({a} : Set G) ⊓ centralizer ({b} : Set G)) := by
  have key1 : ∀ (c : G) (e : G), c * (g * e * g⁻¹) = (g * e * g⁻¹) * c →
      g⁻¹ * c * g ∈ centralizer ({e} : Set G) := by
    intro c e h
    rw [mem_centralizer_singleton_iff]
    calc g⁻¹ * c * g * e = g⁻¹ * (c * (g * e * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * e * g⁻¹) * c) * g := by rw [h]
      _ = e * (g⁻¹ * c * g) := by group
  have key2 : ∀ (c : G) (e : G), c * e = e * c →
      g * c * g⁻¹ ∈ centralizer ({g * e * g⁻¹} : Set G) := by
    intro c e h
    rw [mem_centralizer_singleton_iff]
    calc g * c * g⁻¹ * (g * e * g⁻¹) = g * (c * e) * g⁻¹ := by group
      _ = g * (e * c) * g⁻¹ := by rw [h]
      _ = (g * e * g⁻¹) * (g * c * g⁻¹) := by group
  refine Nat.card_congr
    { toFun := fun c => ⟨g⁻¹ * c.1 * g, Subgroup.mem_inf.2
        ⟨key1 c.1 a (mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 c.2).1),
          key1 c.1 b (mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 c.2).2)⟩⟩
      invFun := fun c => ⟨g * c.1 * g⁻¹, Subgroup.mem_inf.2
        ⟨key2 c.1 a (mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 c.2).1),
          key2 c.1 b (mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 c.2).2)⟩⟩
      left_inv := fun c => Subtype.ext (by group)
      right_inv := fun c => Subtype.ext (by group) }

theorem exists_D8_data
    (hC : pRank 2 G ≤ 4) (hn : n = 5 ∨ n = 6) (h : IsAConfig n x K T Q S a)
    {t u g : G} (hS : Stage3Loc n x K Q t u g) :
    ∃ z : G, z ∈ K ∧ z * z = 1 ∧ z ≠ 1 ∧
      Nat.card ↥(centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G)) =
        (if n = 5 then 24 else 72) ∧
      ∃ D : Subgroup G, D ≤ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) ∧ z ∈ D ∧
        Nonempty (↥D ≃* DihedralGroup 4) := by
  classical
  have hn' : n = 5 ∨ n = 6 ∨ n = 7 := by omega
  have hG4 : pRank 2 G ≤ 4 := hC
  obtain ⟨y₀, hy₀Q, hy₀1, hy₀x, hQall, hy2, hx2, hxy, ht3', ht1, hp, hs, htxx⟩ := Q_facts hS
  have hg2 : g * g = 1 := by rw [← sq]; exact hS.g_sq
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg2
  let cg : G ≃* G := MulAut.conj g
  have hcg : ∀ z : G, cg z = g * z * g⁻¹ := fun z => rfl
  have hcgcg : ∀ z : G, cg (cg z) = z := by
    intro z
    rw [hcg, hcg]
    calc g * (g * z * g⁻¹) * g⁻¹ = (g * g) * z * (g⁻¹ * g⁻¹) := by group
      _ = z := by
        have h1 : g⁻¹ * g⁻¹ = 1 := by rw [hginv]; exact hg2
        rw [hg2, h1]; group
  have ht'K : cg t ∈ K := hS.gt_K
  have ht'3 : cg t * cg t * cg t = 1 := by rw [← map_mul, ← map_mul, ht3', map_one]
  have ht'1 : cg t ≠ 1 := fun h1 => ht1 (cg.injective (by rw [h1, map_one]))
  obtain ⟨u₁, hu₁2, hu₁x, hu₁t, hu₁y⟩ := exists_u1 hn' hG4 h hy₀Q hy₀1 hy₀x ht'K ht'3 ht'1
  obtain ⟨σ, hσ3, hσ1, hcard⟩ := card_centralizer_x_t' hn' hG4 h ht'K ht'3 ht'1
  have hzK : cg x ∈ K := hS.g_Q x hS.x_mem
  have hzz : cg x * cg x = 1 := by rw [← map_mul, hx2, map_one]
  have hz1 : cg x ≠ 1 := fun h1 => hS.x_ne (cg.injective (by rw [h1, map_one]))
  have hcardz : Nat.card ↥(centralizer ({cg x} : Set G) ⊓ centralizer ({t} : Set G)) =
      (if n = 5 then 24 else 72) := by
    have e : t = g * (cg t) * g⁻¹ := by
      show t = g * (g * t * g⁻¹) * g⁻¹
      calc t = (g * g) * t * (g⁻¹ * g⁻¹) := by
            have h1 : g⁻¹ * g⁻¹ = 1 := by rw [hginv]; exact hg2
            rw [hg2, h1]; group
        _ = g * (g * t * g⁻¹) * g⁻¹ := by group
    have h1 := card_inf_conj g x (cg t)
    rw [← e] at h1
    rw [show cg x = g * x * g⁻¹ from rfl, h1, hcard]
    rcases hn with rfl | rfl
    · rw [card_centralizer_ord3_five hσ3 hσ1]; simp
    · rw [card_centralizer_ord3_six hσ3 hσ1]; simp
  set w : G := cg u₁ with hw
  set q : G := cg y₀ with hq
  have hww : w * w = 1 := by rw [hw, ← map_mul, hu₁2, map_one]
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
  have hqq : q * q = 1 := by rw [hq, ← map_mul, hy2, map_one]
  have hqinv : q⁻¹ = q := inv_eq_of_mul_eq_one_right hqq
  have hqK : q ∈ K := hS.g_Q y₀ hy₀Q
  have hwt : w * t = t * w := by
    have : t = cg (cg t) := (hcgcg t).symm
    calc w * t = cg u₁ * cg (cg t) := by rw [hw, ← this]
      _ = cg (u₁ * cg t) := by rw [map_mul]
      _ = cg (cg t * u₁) := by rw [hu₁t]
      _ = t * w := by rw [map_mul, hcgcg, hw]
  have hwz : w * cg x = cg x * w := by
    calc w * cg x = cg (u₁ * x) := by rw [hw, map_mul]
      _ = cg (x * u₁) := by rw [hu₁x]
      _ = cg x * w := by rw [map_mul, hw]
  have hqt : q * t = t * q := (hS.t_comm_K q hqK).symm
  have hqz : q * cg x = cg x * q := by
    calc q * cg x = cg (y₀ * x) := by rw [hq, map_mul]
      _ = cg (x * y₀) := by rw [hxy]
      _ = cg x * q := by rw [map_mul, hq]
  have hu₁yQ : u₁ * y₀ * u₁⁻¹ = x * y₀ := by
    have hmem : u₁ * y₀ * u₁⁻¹ ∈ Q :=
      h.Q_normal u₁ (mem_centralizer_singleton_iff.2 hu₁x) y₀ hy₀Q
    rcases hQall _ hmem with h1 | h1 | h1 | h1
    · exfalso
      apply hy₀1
      calc y₀ = u₁⁻¹ * (u₁ * y₀ * u₁⁻¹) * u₁ := by group
        _ = 1 := by rw [h1]; group
    · exfalso
      apply hy₀x
      have h2 : u₁ * y₀ = x * u₁ := by
        calc u₁ * y₀ = (u₁ * y₀ * u₁⁻¹) * u₁ := by group
          _ = x * u₁ := by rw [h1]
      calc y₀ = u₁⁻¹ * (u₁ * y₀) := by group
        _ = u₁⁻¹ * (x * u₁) := by rw [h2]
        _ = u₁⁻¹ * (u₁ * x) := by rw [hu₁x]
        _ = x := by group
    · exact absurd h1 hu₁y
    · exact h1
  have hwq : w * q * w⁻¹ = cg x * q := by
    calc w * q * w⁻¹ = cg (u₁ * y₀ * u₁⁻¹) := by rw [hw, hq, map_mul, map_mul, map_inv]
      _ = cg (x * y₀) := by rw [hu₁yQ]
      _ = cg x * q := by rw [map_mul, hq]
  let ρ : G := w * q
  have hρρ : ρ * ρ = cg x := by
    calc ρ * ρ = (w * q * w⁻¹) * q := by
          simp only [ρ]; rw [hwinv]; group
      _ = cg x * (q * q) := by rw [hwq]; group
      _ = cg x := by rw [hqq, mul_one]
  have hρ2 : ρ ^ 2 = cg x := by rw [sq]; exact hρρ
  have hρ4 : ρ ^ 4 = 1 := by
    calc ρ ^ 4 = (ρ ^ 2) ^ 2 := by group
      _ = 1 := by rw [hρ2, sq]; exact hzz
  have hρord : orderOf ρ = 4 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h1 : ¬ ρ ^ 2 ^ 1 = 1 := by
      rw [pow_one, hρ2]; exact hz1
    have h2 : ρ ^ 2 ^ (1 + 1) = 1 := by simpa using hρ4
    simpa using orderOf_eq_prime_pow h1 h2
  have hwρ : w * ρ * w⁻¹ = ρ⁻¹ := by
    have hρinv : ρ⁻¹ = q * w := by
      simp only [ρ]; rw [mul_inv_rev, hqinv, hwinv]
    rw [hρinv, hwinv]
    simp only [ρ]
    calc w * (w * q) * w = (w * w) * q * w := by group
      _ = q * w := by rw [hww]; group
  have hwρ' : ∀ c ∈ zpowers ρ, w * c * w⁻¹ = c⁻¹ := by
    intro c hc
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hc
    rw [← conj_zpow, hwρ, inv_zpow]
  have hwnot : w ∉ zpowers ρ := by
    intro hmem
    obtain ⟨i, hi⟩ := mem_zpowers_iff.1 hmem
    have hcomm : w * ρ = ρ * w := by
      rw [← hi]
      exact ((Commute.refl ρ).zpow_left i).eq
    have h1 : ρ = ρ⁻¹ := by
      calc ρ = ρ * w * w⁻¹ := by group
        _ = w * ρ * w⁻¹ := by rw [hcomm]
        _ = ρ⁻¹ := hwρ
    have h2 : ρ * ρ = 1 := by
      calc ρ * ρ = ρ * ρ⁻¹ := by rw [← h1]
        _ = 1 := mul_inv_cancel ρ
    exact hz1 (hρρ ▸ h2)
  have hcyc : IsCyclic (zpowers ρ) := inferInstance
  have hne := CFSG.Glauberman.Dickson.nonempty_sup_zpowers_mulEquiv_dihedral (zpowers ρ) hcyc w hwnot hww hwρ'
  have hc : Nat.card (zpowers ρ) = 4 := by rw [Nat.card_zpowers, hρord]
  rw [hc] at hne
  have hρC : ρ ∈ centralizer ({cg x} : Set G) ⊓ centralizer ({t} : Set G) := by
    refine ⟨mem_centralizer_singleton_iff.2 ?_, mem_centralizer_singleton_iff.2 ?_⟩
    · simp only [ρ]
      calc w * q * cg x = w * (q * cg x) := by group
        _ = w * (cg x * q) := by rw [hqz]
        _ = (w * cg x) * q := by group
        _ = (cg x * w) * q := by rw [hwz]
        _ = cg x * (w * q) := by group
    · simp only [ρ]
      calc w * q * t = w * (q * t) := by group
        _ = w * (t * q) := by rw [hqt]
        _ = (w * t) * q := by group
        _ = (t * w) * q := by rw [hwt]
        _ = t * (w * q) := by group
  have hwC : w ∈ centralizer ({cg x} : Set G) ⊓ centralizer ({t} : Set G) :=
    ⟨mem_centralizer_singleton_iff.2 hwz, mem_centralizer_singleton_iff.2 hwt⟩
  refine ⟨cg x, hzK, hzz, hz1, hcardz, zpowers ρ ⊔ zpowers w, ?_, ?_, hne⟩
  · exact sup_le (zpowers_le.2 hρC) (zpowers_le.2 hwC)
  · have : cg x = ρ ^ 2 := hρ2.symm
    rw [this]
    exact mem_sup_left (pow_mem (mem_zpowers ρ) 2)

end Config

end CFSG.GH74.GLS.C3.Prop121
