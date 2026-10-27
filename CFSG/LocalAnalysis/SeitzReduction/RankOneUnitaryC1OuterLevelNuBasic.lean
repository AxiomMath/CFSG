module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterLevelWeight
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1NcycBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup

theorem outerNu_card_le_of_isCyclic {H : Type*} [Group H] [Finite H] [IsCyclic H] {n : ℕ}
    (hn : 0 < n) (hpow : ∀ a : H, a ^ n = 1) : Nat.card H ≤ n := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := H)
  rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
  exact orderOf_le_of_pow_eq_one hn (hpow g)

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem outerNu_card_le (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {P : Subgroup G}
    (hPT : P ≤ T) {n : ℕ} (hn : 0 < n) (hpow : ∀ s ∈ P, s ^ n ∈ szT₁ L T ⊔ zpowers t) :
    Nat.card P ≤ Nat.card (P ⊓ (szT₁ L T ⊔ zpowers t) : Subgroup G) * n := by
  have : Finite (MulAut L) := finite_mulAut L
  obtain ⟨φ, hker, hcyc⟩ := h.exists_outHom_of_card_sylow hS2
  have : IsCyclic φ.range := hcyc
  let ψ : P →* φ.range := φ.rangeRestrict.comp (Subgroup.inclusion hPT)
  have hψ : ∀ s : P, ψ s = 1 ↔ ((s : G) ∈ szT₁ L T ⊔ zpowers t) := by
    intro s
    have e : ψ s = 1 ↔ φ (Subgroup.inclusion hPT s) = 1 := by
      constructor
      · intro h1
        exact congrArg Subtype.val h1
      · intro h1
        exact Subtype.ext h1
    rw [e]
    exact hker _
  have h1 := Subgroup.card_ker_mul_card_range ψ
  have hk : Nat.card ψ.ker ≤ Nat.card (P ⊓ (szT₁ L T ⊔ zpowers t) : Subgroup G) := by
    refine Nat.card_le_card_of_injective
      (fun s => (⟨((s : P) : G), mem_inf.mpr ⟨(s : P).2, (hψ s).mp s.2⟩⟩ :
        (P ⊓ (szT₁ L T ⊔ zpowers t) : Subgroup G))) ?_
    intro a b hab
    have h1 : (((a : ψ.ker) : P) : G) = (((b : ψ.ker) : P) : G) :=
      congrArg (fun x : (P ⊓ (szT₁ L T ⊔ zpowers t) : Subgroup G) => (x : G)) hab
    exact Subtype.ext (Subtype.ext h1)
  have hr : Nat.card ψ.range ≤ n := by
    refine outerNu_card_le_of_isCyclic hn fun a => ?_
    obtain ⟨s, hs⟩ := a.2
    apply Subtype.ext
    show (a : φ.range) ^ n = 1
    rw [← hs, ← map_pow]
    exact (hψ _).mpr (by rw [SubgroupClass.coe_pow]; exact hpow _ s.2)
  rw [← h1]
  exact Nat.mul_le_mul hk hr

theorem outerNu_card_le_of_central (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {P : Subgroup G}
    (hPT : P ≤ T) (hpow : ∀ s ∈ P, s ^ 4 = 1) {a : G} (haT : a ∈ T) (ha2 : a ^ 2 = 1)
    (haS : a ∉ szT₁ L T ⊔ zpowers t) (hac : ∀ s ∈ P, s * a = a * s) :
    Nat.card P ≤ 8 * 2 ^ f := by
  obtain ⟨-, -, hCA, -⟩ := h.outer_facts_of_card_sylow hS2 haT ha2 haS
  have hat : a * t = t * a := mem_centralizer_singleton_iff.mp (h.le haT)
  have hle : P ⊓ (szT₁ L T ⊔ zpowers t) ≤ szA L T t := by
    intro s hs
    obtain ⟨hsP, hsS⟩ := mem_inf.mp hs
    obtain ⟨y, hy, z, hz, rfl⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ hsS
    have hza : a * z = z * a := commute_of_mem_zpowers hz hat
    have hya : a * y = y * a := by
      have e := hac _ hsP
      have e2 : y * a * z = a * y * z := by
        calc y * a * z = y * (a * z) := by group
          _ = y * (z * a) := by rw [hza]
          _ = y * z * a := by group
          _ = a * (y * z) := e
          _ = a * y * z := by group
      exact (mul_right_cancel e2).symm
    exact mul_mem (szA₁_le_szA L T t (hCA y hy hya)) (zpowers_le.mpr (mem_szA_right L T t) hz)
  have h1 := h.outerNu_card_le hS2 hPT (n := 4) (by norm_num)
    (fun s hs => by rw [hpow s hs]; exact one_mem _)
  have h2 := Subgroup.card_le_of_le hle
  rw [(h.szA_facts_of_card_sylow hS2).1] at h2
  calc Nat.card P ≤ Nat.card (P ⊓ (szT₁ L T ⊔ zpowers t) : Subgroup G) * 4 := h1
    _ ≤ 2 * 2 ^ f * 4 := Nat.mul_le_mul_right 4 h2
    _ = 8 * 2 ^ f := by ring

theorem outerNu_mem_szA₁_of_mem_szA (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {x : G}
    (hxA : x ∈ szA L T t) (hxT : x ∈ szT₁ L T) : x ∈ szA₁ (szT₁ L T) := by
  obtain ⟨-, -, -, -, hdisj, -⟩ := h.start_of_card_sylow hS2
  have htA₁ : t ∈ centralizer (szA₁ (szT₁ L T) : Set G) :=
    centralizer_le (szA₁_le _) h.mem_centralizer_szT₁
  obtain ⟨a, ha, z, hz, rfl⟩ := exists_mul_eq_of_mem_sup_zpowers htA₁ hxA
  have hzT : z ∈ szT₁ L T := by
    have := mul_mem (inv_mem (szA₁_le _ ha)) hxT
    rwa [inv_mul_cancel_left] at this
  have hz1 : z = 1 := by
    have : z ∈ szT₁ L T ⊓ zpowers t := mem_inf.mpr ⟨hzT, hz⟩
    rw [hdisj] at this
    exact (mem_bot.mp this)
  rw [hz1, mul_one]
  exact ha

theorem outerNu_le_of_sq_mem (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hv : ∃ v ∈ T, v ^ 2 = 1 ∧ v ∉ szT₁ L T ⊔ zpowers t) {P : Subgroup G} (hPT : P ≤ T)
    (htP : t ∉ P) (hsq : ∀ s ∈ P, s ^ 2 ∈ szA L T t) (hcard : (2 ^ f) ^ 3 ≤ Nat.card P) :
    P ≤ szT₁ L T ⊔ zpowers t := by
  intro s₀ hs₀P
  by_contra hs₀S
  obtain ⟨v, hvT, hv2, hvS⟩ := hv
  obtain ⟨W, hWT₁, -, hWcard, -, -, -, hWiff⟩ := h.exists_W_of_card_sylow hS2 hvT hv2 hvS
  obtain ⟨-, -, -, hTN₁, hdisj, -⟩ := h.start_of_card_sylow hS2
  obtain ⟨-, -, -, hsqT₁, -, hA₁sq, -⟩ := h.facts_of_card_sylow hS2
  have htC := h.mem_centralizer_szT₁
  have ht2 : t * t = 1 := by rw [← sq, h.sq_eq_one]
  have hvt : v * t = t * v := mem_centralizer_singleton_iff.mp (h.le hvT)
  have hvv : v * v = 1 := by rw [← sq, hv2]
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
  have hAS : szA L T t ≤ szT₁ L T ⊔ zpowers t := sup_le_sup_right (szA₁_le _) _
  have hclaim : ∀ s ∈ P, s ∉ szT₁ L T ⊔ zpowers t → s * v⁻¹ ∈ W ⊔ zpowers t := by
    intro s hs hsS
    have hsv := h.mul_inv_mem_of_sq_mem_of_card_sylow hS2 (hPT hs) hvT (hAS (hsq s hs))
      (by rw [hv2]; exact one_mem _) hsS hvS
    obtain ⟨y, hy, z, hz, hyz⟩ := exists_mul_eq_of_mem_sup_zpowers htC hsv
    have hzv : v * z = z * v := commute_of_mem_zpowers hz hvt
    have hzy : y * z = z * y :=
      commute_of_mem_zpowers hz (mem_centralizer_iff.mp htC y hy)
    have hz2 : z * z = 1 := by
      rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hz with rfl | rfl
      · exact mul_one 1
      · exact ht2
    have hs_eq : s = y * z * v := by
      rw [hyz, mul_assoc, inv_mul_cancel, mul_one]
    have hs2 : s ^ 2 = y * (v * y * v⁻¹) := by
      rw [hs_eq, sq, hvinv]
      calc y * z * v * (y * z * v) = y * (z * v) * (y * z) * v := by group
        _ = y * (v * z) * (z * y) * v := by rw [← hzv, hzy]
        _ = y * v * (z * z) * y * v := by group
        _ = y * (v * y * v) := by rw [hz2]; group
    have hvy : v * y * v⁻¹ ∈ szT₁ L T := (mem_normalizer_iff.mp (hTN₁ hvT) y).mp hy
    have hs2A₁ : s ^ 2 ∈ szA₁ (szT₁ L T) :=
      h.outerNu_mem_szA₁_of_mem_szA hS2 (hsq s hs) (by rw [hs2]; exact mul_mem hy hvy)
    have hyW : y ∈ W := by
      refine (hWiff y hy).mp ?_
      have hy2 : y⁻¹ * y⁻¹ ∈ szA₁ (szT₁ L T) := by
        rw [← mul_inv_rev, ← sq]
        exact inv_mem (hsqT₁ y hy)
      have e : y⁻¹ * (v * y * v⁻¹) = (y⁻¹ * y⁻¹) * s ^ 2 := by rw [hs2]; group
      rw [e]
      exact mul_mem hy2 hs2A₁
    rw [← hyz]
    exact mul_mem (mem_sup_left hyW) (mem_sup_right hz)
  have hQ : P ⊓ (szT₁ L T ⊔ zpowers t) ≤ W ⊔ zpowers t := by
    intro q hq
    obtain ⟨hqP, hqS⟩ := mem_inf.mp hq
    have hqs : q * s₀ ∉ szT₁ L T ⊔ zpowers t := fun hm => hs₀S (by
      have := mul_mem (inv_mem hqS) hm
      rwa [inv_mul_cancel_left] at this)
    have h1 := hclaim (q * s₀) (mul_mem hqP hs₀P) hqs
    have h2 := hclaim s₀ hs₀P hs₀S
    have e : q = (q * s₀ * v⁻¹) * (s₀ * v⁻¹)⁻¹ := by group
    rw [e]
    exact mul_mem h1 (inv_mem h2)
  have htW : t ∉ W := fun htW => by
    have : t ∈ szT₁ L T ⊓ zpowers t := mem_inf.mpr ⟨hWT₁ htW, mem_zpowers t⟩
    rw [hdisj, mem_bot] at this
    have h1 : orderOf t = 1 := by rw [this, orderOf_one]
    rw [h.inv] at h1
    exact absurd h1 (by norm_num)
  have htNW : t ∈ normalizer (W : Set G) :=
    mem_normalizer_of_forall_inv_mul_mul_mem fun y hy => by
      have e := mem_centralizer_iff.mp htC y (hWT₁ hy)
      rw [mul_assoc, e, inv_mul_cancel_left]
      exact hy
  have hWt : Nat.card (W ⊔ zpowers t : Subgroup G) = 2 * (2 ^ f) ^ 2 := by
    have h1 := RankOne.Endings.relIndex_sup_zpowers_eq_two htW htNW ht2
    have h2 := relIndex_mul_card (H := W) (K := W ⊔ zpowers t)
    rw [h1, inf_of_le_left le_sup_left, hWcard] at h2
    exact h2.symm
  have hP2 := h.outerNu_card_le hS2 hPT two_pos (fun s hs => hAS (hsq s hs))
  have hq4 : 4 ≤ 2 ^ f :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.two_le
  have hQge : Nat.card (W ⊔ zpowers t : Subgroup G) ≤
      Nat.card (P ⊓ (szT₁ L T ⊔ zpowers t) : Subgroup G) := by
    rw [hWt]
    have h3 : 4 * (2 ^ f) ^ 2 ≤ (2 ^ f) ^ 3 := by
      calc 4 * (2 ^ f) ^ 2 ≤ 2 ^ f * (2 ^ f) ^ 2 := Nat.mul_le_mul_right _ hq4
        _ = (2 ^ f) ^ 3 := by ring
    omega
  have hQeq := eq_of_le_of_card_ge hQ hQge
  have htQ : t ∈ P ⊓ (szT₁ L T ⊔ zpowers t) := by
    rw [hQeq]
    exact mem_sup_right (mem_zpowers t)
  exact htP (mem_inf.mp htQ).1

end U3Start

namespace U3C1OuterStage

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}
  {d : G} {V U U₁ : Subgroup G} {k : ℕ}

section Nu

variable (h : U3C1OuterStage G L f t T d V U U₁ k)
include h

theorem comm_t_eq_of_commute (hμV : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G))) {c w y r : G}
    (hc : c ∈ szT₁ L T) (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) (hy : y ∈ szT₁ L T)
    (hr : r ∈ U₁ ⊓ centralizer (szT₁ L T : Set G))
    (hcomm : c * w * t * (y * r) = y * r * (c * w * t)) :
    r * t * r⁻¹ * t⁻¹ = y⁻¹ * c * y * c⁻¹ := by
  have hs := h.t_conj_mem_V₁ hr
  have e1 : t * y = y * t := (h.t_comm hy).symm
  have e2 : w * y = y * w := (mem_centralizer_iff.mp (mem_inf.mp hw).2 y hy).symm
  have e3 : w * (t * r * t⁻¹) = (t * r * t⁻¹) * w := h.V₁_comm hμV hlam w hw _ hs
  have e4 : t * r * t⁻¹ * c⁻¹ = c⁻¹ * (t * r * t⁻¹) :=
    (mem_centralizer_iff.mp (mem_inf.mp hs).2 c⁻¹ (inv_mem hc)).symm
  have key : c * w * t * (y * r) * (c * w * t)⁻¹ = c * y * c⁻¹ * (t * r * t⁻¹) := by
    calc c * w * t * (y * r) * (c * w * t)⁻¹ = c * w * (t * y) * r * t⁻¹ * w⁻¹ * c⁻¹ := by
          group
      _ = c * (w * y) * (t * r * t⁻¹) * w⁻¹ * c⁻¹ := by rw [e1]; group
      _ = c * y * (w * (t * r * t⁻¹)) * w⁻¹ * c⁻¹ := by rw [e2]; group
      _ = c * y * (t * r * t⁻¹ * c⁻¹) := by rw [e3]; group
      _ = c * y * c⁻¹ * (t * r * t⁻¹) := by rw [e4]; group
  have E : c * y * c⁻¹ * (t * r * t⁻¹) = y * r := by
    rw [← key, hcomm, mul_inv_cancel_right]
  calc r * t * r⁻¹ * t⁻¹ = y⁻¹ * (y * r) * (t * r * t⁻¹)⁻¹ := by group
    _ = y⁻¹ * (c * y * c⁻¹ * (t * r * t⁻¹)) * (t * r * t⁻¹)⁻¹ := by rw [E]
    _ = y⁻¹ * c * y * c⁻¹ := by group

theorem mem_V_of_comm_t_mem_szA₁ {r : G} (hr : r ∈ U₁ ⊓ centralizer (szT₁ L T : Set G))
    (hσ : r * t * r⁻¹ * t⁻¹ ∈ szA₁ (szT₁ L T)) : r ∈ V := by
  obtain ⟨K, _, _, _, v, μ, hK, hc, -⟩ := h.coords
  have h1 : (r * t * r⁻¹ * t⁻¹) ^ 2 ^ k = 1 := by
    obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by have := h.one_le; omega⟩
    rw [hj, pow_succ', pow_mul, hc.sq_eq_one hσ, one_pow]
  refine h.mem_V_of_mem_V₁_of_mem_sup hr (h.mem_sup_of_S_eq_zero hK hc (mem_inf.mp hr).1 ?_)
  rw [h1, hc.v_one]


end Nu

end U3C1OuterStage

end CFSG.SeitzReduction.RankOne
