module

public import CFSG.GH74.GLS.SP.Local.SPLCtT1
public import CFSG.GH74.GLS.SP.Local.SPLCtWS
public import CFSG.GH74.GLS.SP.Local.SPLCtC1a

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

section CtT

theorem normalizes_of_index_two {G : Type} [Group G] [Finite G] {B Y : Subgroup G} (hBY : B ≤ Y)
    (hcard : Nat.card ↥Y = 2 * Nat.card ↥B) : ∀ y ∈ Y, ∀ a ∈ B, y * a * y⁻¹ ∈ B := by
  have hidx : (B.subgroupOf Y).index = 2 := by
    have h1 := Subgroup.card_mul_index (B.subgroupOf Y)
    have h2 : Nat.card ↥(B.subgroupOf Y) = Nat.card ↥B :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBY).toEquiv
    rw [h2, hcard] at h1
    have hpos : 0 < Nat.card ↥B := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (by rw [h1]; ring)
  have hnorm : (B.subgroupOf Y).Normal := Subgroup.normal_of_index_eq_two hidx
  intro y hy a ha
  exact hnorm.conj_mem ⟨a, hBY ha⟩ ha ⟨y, hy⟩

variable {G : Type} [Group G] [Finite G] (D : SPLNot1 G)

theorem I_center_trivial (hs : SPLSetup D.toSPLNot0) {ζ : G} (hζ : ζ ∈ D.Ict)
    (hc : ∀ i ∈ D.Ict, ζ * i = i * ζ) : ζ = 1 := by
  have hsimple := I_simple D hs
  have hmem : (⟨ζ, hζ⟩ : ↥D.Ict) ∈ center ↥D.Ict := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc g g.2).symm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥D.Ict) with h | h
  · rw [h, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  · exfalso
    have hcomm : ∀ a ∈ D.Ict, ∀ b ∈ D.Ict, a * b = b * a := by
      intro a ha b hb
      have ha' : (⟨a, ha⟩ : ↥D.Ict) ∈ center ↥D.Ict := by rw [h]; trivial
      exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp ha' ⟨b, hb⟩)).symm
    have hbot : D.Ict ≤ ⊥ := by
      calc D.Ict = ⁅D.Ict, D.Ict⁆ := (Ict_perfect D hs).symm
        _ ≤ ⊥ := by
          rw [commutator_le]
          intro a ha b hb
          rw [Subgroup.mem_bot]
          exact commutatorElement_eq_one_iff_mul_comm.mpr (hcomm a ha b hb)
    obtain ⟨g, hg⟩ := exists_ne (1 : ↥D.Ict)
    apply hg
    exact Subtype.ext (Subgroup.mem_bot.mp (hbot g.2))

theorem ctT_exists (hs : SPLSetup D.toSPLNot0) (hA : SPLCtA D) {u : G} (hu : SPLCtU D u) :
    ∃ T T₀ T₁ : Subgroup G, ∃ y : G, SPLCtT D T T₀ T₁ y := by
  obtain ⟨T, T₁, hTle, hTp, hTmax, hztT, hT₁eq, hT₁S, hT₁dih, hCz⟩ := ctT_pre D hs
  obtain ⟨B₁, B₂, y, hB₁T, hB₂T, hyT, hy2, hTeq, hcomm, hinf, d₁, d₂, d₃, d₄⟩ :=
    ct1a D hs hu T hTle hTp hTmax
  have hn3 : 3 ≤ D.n := three_le_n D.toSPLNot0 hs.odd_q hs.q_ge
  have hyy : y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy2, pow_two] at this
  have hT₁I : T₁ ≤ D.Ict := by rw [hT₁eq]; exact inf_le_right
  have hT₁T : T₁ ≤ T := by rw [hT₁eq]; exact inf_le_left
  have hcardB : ∀ B : Subgroup G, IVK.IsDihedralOrder ↥B (2 ^ (D.n - 1)) →
      IVK.IsDihedralOrder ↥(B ⊔ zpowers y) (2 ^ D.n) → ∀ a ∈ B, y * a * y⁻¹ ∈ B := by
    intro B hB hBy
    refine normalizes_of_index_two (Y := B ⊔ zpowers y) le_sup_left ?_ y
      (Subgroup.mem_sup_right (mem_zpowers y))
    rw [CtW.card_of_isDihedralOrder hB, CtW.card_of_isDihedralOrder hBy]
    obtain ⟨j, hj⟩ : ∃ j, D.n = j + 1 := ⟨D.n - 1, by omega⟩
    rw [hj, Nat.add_sub_cancel, pow_succ, mul_comm]
  have hy₁ := hcardB B₁ d₁ d₃
  have hy₂ := hcardB B₂ d₂ d₄
  have hzT : D.z ∈ T := hztT (Subgroup.mem_sup_left (mem_zpowers _))
  have htT : D.t ∈ T := hztT (Subgroup.mem_sup_right (mem_zpowers _))
  have hT₁n : ∀ c ∈ T, ∀ a ∈ T₁, c * a * c⁻¹ ∈ T₁ := by
    intro c hc a ha
    rw [hT₁eq]
    refine ⟨T.mul_mem (T.mul_mem hc (hT₁T ha)) (T.inv_mem hc), ?_⟩
    exact hA.I_normal c (hTle hc) a (hT₁I ha)
  have hzT₁ : ∀ a ∈ T₁, D.z * a = a * D.z := fun a ha =>
    z_central_in_K D hs (mem_zpowers D.z) a (Ict_le_K D hs (hT₁I ha))
  have hinfU : (zpowers D.z ⊔ zpowers D.t) ⊓ T₁ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    exact V_inf_IF₀ D hs hx.1 (Subgroup.mem_sup_left (hT₁I hx.2))
  have hzt : D.z ≠ D.t := fun h => hs.syl.t_nconj (h ▸ IsConj.refl _)
  obtain ⟨X, y₀, hXT, hXn, hzX, hXmin, hXdih, hXcomm, hXinf, hXC, hy₀T, hy₀2, hTeq', hXy, hT₁y⟩ :=
    lemmaW_sub hn3 T B₁ B₂ T₁ y D.z D.t hB₁T hB₂T hyT hT₁T hzT htT hcomm hinf hyy hy₁ hy₂ hTeq
      d₁ d₂ d₃ d₄ hT₁n hT₁dih hs.syl.z_inv hs.syl.t_ord
      (fun c hc => mem_centralizer_singleton_iff.mp (hTle hc)) hzt hzT₁ hinfU hCz
  have hcenI : ∀ c ∈ X, ∀ i ∈ D.Ict, c * i = i * c := by
    let N : Subgroup G := centralizer (D.Ict : Set G) ⊓ T
    have hNT : N ≤ T := inf_le_right
    have hNinv : ∀ c ∈ T, ∀ a ∈ N, c * a * c⁻¹ ∈ N := by
      intro c hc a ha
      refine ⟨?_, T.mul_mem (T.mul_mem hc ha.2) (T.inv_mem hc)⟩
      show c * a * c⁻¹ ∈ centralizer (D.Ict : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro i hi
      have hj : c⁻¹ * i * c ∈ D.Ict := by
        have := hA.I_normal c⁻¹ (D.Ct.inv_mem (hTle hc)) i hi
        simpa using this
      have haj : a * (c⁻¹ * i * c) = (c⁻¹ * i * c) * a :=
        (Subgroup.mem_centralizer_iff.mp ha.1 _ hj).symm
      calc i * (c * a * c⁻¹) = c * ((c⁻¹ * i * c) * a) * c⁻¹ := by group
        _ = c * (a * (c⁻¹ * i * c)) * c⁻¹ := by rw [haj]
        _ = (c * a * c⁻¹) * i := by group
    have hzN : D.z ∈ N := by
      refine ⟨?_, hzT⟩
      show D.z ∈ centralizer (D.Ict : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro i hi
      exact (z_central_in_K D hs (mem_zpowers D.z) i (Ict_le_K D hs hi)).symm
    intro c hc i hi
    have hcN : c ∈ N := hXmin N hNT hNinv hzN hc
    exact (Subgroup.mem_centralizer_iff.mp hcN.1 i hi).symm
  have hT₀mem : ∀ c : G, c ∈ X ↔ c ∈ T ∧ ∀ i ∈ D.Ict, c * i = i * c := by
    intro c
    constructor
    · intro hc
      exact ⟨hXT hc, hcenI c hc⟩
    · rintro ⟨hcT, hci⟩
      obtain ⟨x, hx, ζ, hζ, -, rfl⟩ :=
        hXC c hcT (fun a ha => hci a (hT₁I ha))
      have hζI : ζ ∈ D.Ict := hT₁I hζ
      have hζc : ∀ i ∈ D.Ict, ζ * i = i * ζ := by
        intro i hi
        have h1 := hci i hi
        have h2 := hcenI x hx i hi
        have : x * (ζ * i) = x * (i * ζ) := by
          calc x * (ζ * i) = (x * ζ) * i := by group
            _ = i * (x * ζ) := h1
            _ = (i * x) * ζ := by group
            _ = (x * i) * ζ := by rw [h2]
            _ = x * (i * ζ) := by group
        exact mul_left_cancel this
      have hζ1 : ζ = 1 := I_center_trivial D hs hζI hζc
      rw [hζ1, mul_one]
      exact hx
  refine ⟨T, X, T₁, y₀, ?_⟩
  refine
    { T_le := hTle
      T_p := hTp
      T_max := hTmax
      zt_le := hztT
      T₁_eq := hT₁eq
      T₁_S₁ := hT₁S
      T₁_dih := hT₁dih
      T₀_mem := hT₀mem
      z_T₀ := hzX
      t_T₀ := (hT₀mem D.t).mpr ⟨htT, fun i hi =>
        (mem_centralizer_singleton_iff.mp (Ict_le_Ct D hs hi)).symm⟩
      T₀_dih := hXdih
      T₀_T₁ := hXcomm
      T₀_inf_T₁ := hXinf
      y_mem := hy₀T
      y_sq := hy₀2
      T_eq := hTeq'
      T₀y_dih := hXy
      T₁y_dih := hT₁y
      T₀_norm := fun c hc a ha => hXn c hc a ha
      T₁_norm := hT₁n }

end CtT

end CFSG.GH74.GLS.SP.Local
