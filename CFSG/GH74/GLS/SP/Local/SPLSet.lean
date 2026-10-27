module

public import CFSG.GH74.GLS.SP.Local.SPLGlue
public import CFSG.GH74.GLS.SP.Local.SPLSL2Input
public import CFSG.GH74.GLS.LU.Local.CStruct2

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

namespace CFSG.GH74.GLS.SP.Local

section Torus

variable {G : Type} [Group G] (D : SPLNot1 G)

theorem t_conj_K₁₀ [Finite G] (hs : SPLSetup D.toSPLNot0) : ∀ x ∈ D.K₁, D.t * x * D.t⁻¹ ∈ D.K₂ := by
  intro x hx
  have h := hs.syl.t_swap
  rw [← h]
  exact ⟨x, hx, by simp [MulAut.conj_apply]⟩

theorem h₂_mem_K₂ [Finite G] (hs : SPLSetup D.toSPLNot0) (hh : D.h₁ ∈ D.K₁) : D.h₂ ∈ D.K₂ :=
  t_conj_K₁₀ D hs _ hh

theorem H₁_le_K₁₀ (hh : D.h₁ ∈ D.K₁) : D.H₁ ≤ D.K₁ := by
  show zpowers D.h₁ ≤ D.K₁
  rw [Subgroup.zpowers_le]
  exact hh

theorem H₂_le_K₂₀ [Finite G] (hs : SPLSetup D.toSPLNot0) (hh : D.h₁ ∈ D.K₁) : D.H₂ ≤ D.K₂ := by
  show zpowers D.h₂ ≤ D.K₂
  rw [Subgroup.zpowers_le]
  exact h₂_mem_K₂ D hs hh

theorem H₁_H₂_comm₀ [Finite G] (hs : SPLSetup D.toSPLNot0) (hh : D.h₁ ∈ D.K₁) :
    ∀ a ∈ D.H₁, ∀ b ∈ D.H₂, a * b = b * a := fun a ha b hb =>
  hs.comps.comm a (H₁_le_K₁₀ D hh ha) b (H₂_le_K₂₀ D hs hh hb)

theorem eq_one_or_z {D : SPLNot0 G} [Finite G] (hs : SPLSetup D) {y : G} (hy : y ∈ zpowers D.z) :
    y = 1 ∨ y = D.z := by
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
  have h2 : D.z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hs.z_sq
  rcases Int.even_or_odd' i with ⟨k, rfl | rfl⟩
  · left; rw [zpow_mul, h2, one_zpow]
  · right; rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem pow_half_eq_z [Finite G] (hs : SPLSetup D.toSPLNot0) (hh : D.h₁ ∈ D.K₁)
    (hord : orderOf D.h₁ = D.q - 1) : D.h₁ ^ ((D.q - 1) / 2) = D.z := by
  obtain ⟨m, hm⟩ := hs.odd_q
  have hq1 : D.q - 1 = 2 * m := by omega
  have hm0 : 0 < m := by
    have := hs.q_ge
    omega
  have hhalf : (D.q - 1) / 2 = m := by omega
  rw [hhalf]
  have hy : D.h₁ ^ m ∈ D.K₁ := Subgroup.pow_mem _ hh _
  have hy2 : D.h₁ ^ m * D.h₁ ^ m = 1 := by
    rw [← pow_add, ← two_mul, ← hq1, ← hord]
    exact pow_orderOf_eq_one D.h₁
  have hyz : D.h₁ ^ m ∈ zpowers D.z := involution_mem_zpowers₁ hs.comps hs.odd_q hy hy2
  rcases eq_one_or_z hs hyz with h | h
  · exfalso
    have hdvd : orderOf D.h₁ ∣ m := orderOf_dvd_of_pow_eq_one h
    have := Nat.le_of_dvd hm0 hdvd
    rw [hord] at this
    omega
  · exact h

theorem z_mem_H₁₀ [Finite G] (hs : SPLSetup D.toSPLNot0) (hh : D.h₁ ∈ D.K₁)
    (hord : orderOf D.h₁ = D.q - 1) : D.z ∈ D.H₁ := by
  rw [← pow_half_eq_z D hs hh hord]
  exact Subgroup.pow_mem _ (mem_zpowers _) _

theorem z_mem_H₂₀ [Finite G] (hs : SPLSetup D.toSPLNot0) (hh : D.h₁ ∈ D.K₁)
    (hord : orderOf D.h₁ = D.q - 1) : D.z ∈ D.H₂ := by
  have h := pow_half_eq_z D hs hh hord
  have e : D.h₂ ^ ((D.q - 1) / 2) = D.t * D.h₁ ^ ((D.q - 1) / 2) * D.t⁻¹ := by
    unfold SPLNot1.h₂
    rw [conj_pow]
  have h2 : D.h₂ ^ ((D.q - 1) / 2) = D.z := by
    rw [e, h]
    have hc := hs.syl.comm_z hs.syl.t_mem
    calc D.t * D.z * D.t⁻¹ = D.z * D.t * D.t⁻¹ := by rw [hc]
      _ = D.z := by group
  rw [← h2]
  exact Subgroup.pow_mem _ (mem_zpowers _) _

theorem H_inter₀ [Finite G] (hs : SPLSetup D.toSPLNot0) (hh : D.h₁ ∈ D.K₁)
    (hord : orderOf D.h₁ = D.q - 1) : D.H₁ ⊓ D.H₂ = zpowers D.z := by
  apply le_antisymm
  · intro x ⟨hx1, hx2⟩
    have : x ∈ D.K₁ ⊓ D.K₂ := ⟨H₁_le_K₁₀ D hh hx1, H₂_le_K₂₀ D hs hh hx2⟩
    rwa [hs.comps.inf_eq] at this
  · exact le_inf (Subgroup.zpowers_le.mpr (z_mem_H₁₀ D hs hh hord))
      (Subgroup.zpowers_le.mpr (z_mem_H₂₀ D hs hh hord))

theorem pow_half_mem_zpowers [Finite G] (hs : SPLSetup D.toSPLNot0) (hh : D.h₁ ∈ D.K₁)
    (hord : orderOf D.h₁ = D.q - 1) {u : G} (hu : u ∈ D.H) :
    u ^ ((D.q - 1) / 2) ∈ zpowers D.z := by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute (H₁_H₂_comm₀ D hs hh) hu
  have hcomm : Commute a b := H₁_H₂_comm₀ D hs hh a ha b hb
  rw [hcomm.mul_pow]
  have h2 : D.h₂ ^ ((D.q - 1) / 2) = D.z := by
    have e : D.h₂ ^ ((D.q - 1) / 2) = D.t * D.h₁ ^ ((D.q - 1) / 2) * D.t⁻¹ := by
      unfold SPLNot1.h₂
      rw [conj_pow]
    rw [e, pow_half_eq_z D hs hh hord]
    have hc := hs.syl.comm_z hs.syl.t_mem
    calc D.t * D.z * D.t⁻¹ = D.z * D.t * D.t⁻¹ := by rw [hc]
      _ = D.z := by group
  have h1 := pow_half_eq_z D hs hh hord
  have ha' : a ^ ((D.q - 1) / 2) ∈ zpowers D.z := by
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
    rw [← h1]
    refine mem_zpowers_iff.mpr ⟨i, ?_⟩
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
  have hb' : b ^ ((D.q - 1) / 2) ∈ zpowers D.z := by
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hb
    rw [← h2]
    refine mem_zpowers_iff.mpr ⟨i, ?_⟩
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
  exact Subgroup.mul_mem _ ha' hb'

theorem norm_le_C₀ [Finite G] (hs : SPLSetup D.toSPLNot0) (hh : D.h₁ ∈ D.K₁)
    (hord : orderOf D.h₁ = D.q - 1) : normalizer (D.H : Set G) ≤ D.C := by
  intro g hg
  have hgh : g * D.h₁ * g⁻¹ ∈ D.H :=
    (mem_normalizer_iff.mp hg D.h₁).mp (Subgroup.mem_sup_left (mem_zpowers _))
  have h1 := pow_half_mem_zpowers D hs hh hord hgh
  rw [conj_pow, pow_half_eq_z D hs hh hord] at h1
  have hz1 : D.z ≠ 1 := by
    intro h
    have := hs.syl.z_inv
    rw [h, orderOf_one] at this
    omega
  rcases eq_one_or_z hs h1 with h | h
  · exfalso
    apply hz1
    have : D.z = g⁻¹ * (g * D.z * g⁻¹) * g := by group
    rw [this, h]; group
  · exact mem_centralizer_singleton_iff.mpr (by
      have : g * D.z = D.z * g := by
        calc g * D.z = (g * D.z * g⁻¹) * g := by group
          _ = D.z * g := by rw [h]
      exact this)

theorem card_mul_relIndex' {U V : Subgroup G} (h : U ≤ V) :
    Nat.card ↥U * U.relIndex V = Nat.card ↥V := by
  have h1 := Subgroup.card_mul_index (U.subgroupOf V)
  have h2 : Nat.card ↥(U.subgroupOf V) = Nat.card ↥U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv
  rw [h2] at h1
  exact h1

theorem H_sylow₀ [Finite G] (hs : SPLSetup D.toSPLNot0) (hh : D.h₁ ∈ D.K₁)
    (hord : orderOf D.h₁ = D.q - 1)
    (hsyl : ¬ 2 ∣ (zpowers D.h₁ ⊓ ((D.S : Subgroup G) ⊓ D.K₁)).relIndex (zpowers D.h₁)) :
    ¬ 2 ∣ (D.H ⊓ D.S₁).relIndex D.H := by
  set T₁ : Subgroup G := zpowers D.h₁ ⊓ ((D.S : Subgroup G) ⊓ D.K₁) with hT₁
  set T₂ : Subgroup G := T₁.map (MulAut.conj D.t).toMonoidHom with hT₂
  set U : Subgroup G := T₁ ⊔ T₂ with hU
  set r : ℕ := T₁.relIndex (zpowers D.h₁) with hr
  have hT₁A : T₁ ≤ D.H₁ := inf_le_left
  have hT₂B : T₂ ≤ D.H₂ := by
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp (hT₁A hy)
    refine mem_zpowers_iff.mpr ⟨i, ?_⟩
    rw [← hi]
    unfold SPLNot1.h₂
    rw [conj_zpow]
    simp [MulAut.conj_apply]
  have hT₁S : T₁ ≤ D.S₁ := fun x hx =>
    (show (D.S : Subgroup G) ⊓ D.K₁ ≤ D.S₁ from inf_le_inf_left _ le_sup_left) hx.2
  have hT₂S : T₂ ≤ D.S₁ := by
    rintro x ⟨y, hy, rfl⟩
    have := t_normalizes_S₁ hs y (hT₁S hy)
    simpa [MulAut.conj_apply] using this
  have hUle : U ≤ D.H ⊓ D.S₁ :=
    sup_le (le_inf (hT₁A.trans le_sup_left) hT₁S) (le_inf (hT₂B.trans le_sup_right) hT₂S)
  have hcommA : ∀ a ∈ D.H₁, ∀ b ∈ D.H₂, a * b = b * a := H₁_H₂_comm₀ D hs hh
  have hcommT : ∀ a ∈ T₁, ∀ b ∈ T₂, a * b = b * a :=
    fun a ha b hb => hcommA a (hT₁A ha) b (hT₂B hb)
  have hA2 : Nat.card ↥(D.H₁ ⊓ D.H₂) = 2 := by
    rw [H_inter₀ D hs hh hord, Nat.card_zpowers, hs.syl.z_inv]
  have hzT₁ : D.z ∈ T₁ := ⟨z_mem_H₁₀ D hs hh hord, hs.syl.z_mem, z_mem_K₁ hs⟩
  have hzT₂ : D.z ∈ T₂ := by
    refine ⟨D.z, hzT₁, ?_⟩
    have hc := hs.syl.comm_z hs.syl.t_mem
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc D.t * D.z * D.t⁻¹ = D.z * D.t * D.t⁻¹ := by rw [hc]
      _ = D.z := by group
  have hT2 : Nat.card ↥(T₁ ⊓ T₂) = 2 := by
    have : T₁ ⊓ T₂ = zpowers D.z := by
      apply le_antisymm
      · exact (inf_le_inf hT₁A hT₂B).trans (le_of_eq (H_inter₀ D hs hh hord))
      · exact le_inf (Subgroup.zpowers_le.mpr hzT₁) (Subgroup.zpowers_le.mpr hzT₂)
    rw [this, Nat.card_zpowers, hs.syl.z_inv]
  have hH := card_sup_mul_card_inf_of_commute hcommA
  have hUc := card_sup_mul_card_inf_of_commute hcommT
  rw [hA2] at hH
  rw [hT2] at hUc
  have hH₂card : Nat.card ↥D.H₂ = Nat.card ↥D.H₁ := by
    unfold SPLNot1.H₂ SPLNot1.H₁
    rw [Nat.card_zpowers, Nat.card_zpowers]
    have := MulEquiv.orderOf_eq (MulAut.conj D.t) D.h₁
    simpa [MulAut.conj_apply, SPLNot1.h₂] using this
  have hT₂card : Nat.card ↥T₂ = Nat.card ↥T₁ :=
    Subgroup.card_map_of_injective (MulAut.conj D.t).injective
  have hr1 : Nat.card ↥T₁ * r = Nat.card ↥D.H₁ := card_mul_relIndex' hT₁A
  have hHcard : Nat.card ↥D.H * 2 = (Nat.card ↥T₁ * r) * (Nat.card ↥T₁ * r) := by
    have : Nat.card ↥(D.H₁ ⊔ D.H₂) = Nat.card ↥D.H := rfl
    rw [← this, hH, hH₂card, ← hr1]
  have hUcard : Nat.card ↥U * 2 = Nat.card ↥T₁ * Nat.card ↥T₁ := by
    rw [hT₂card] at hUc
    exact hUc
  have hHU : Nat.card ↥D.H = Nat.card ↥U * (r * r) := by
    have h2 : Nat.card ↥D.H * 2 = (Nat.card ↥U * (r * r)) * 2 := by
      rw [hHcard]
      calc Nat.card ↥T₁ * r * (Nat.card ↥T₁ * r)
          = (Nat.card ↥T₁ * Nat.card ↥T₁) * (r * r) := by ring
        _ = (Nat.card ↥U * 2) * (r * r) := by rw [hUcard]
        _ = (Nat.card ↥U * (r * r)) * 2 := by ring
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h2
  have hUH : U ≤ D.H := hUle.trans inf_le_left
  have hUidx : Nat.card ↥U * U.relIndex D.H = Nat.card ↥D.H := card_mul_relIndex' hUH
  have hUpos : 0 < Nat.card ↥U := Nat.card_pos
  have hidx : U.relIndex D.H = r * r := by
    apply Nat.eq_of_mul_eq_mul_left hUpos
    rw [hUidx, hHU]
  have hdvd : (D.H ⊓ D.S₁).relIndex D.H ∣ U.relIndex D.H :=
    Subgroup.relIndex_dvd_of_le_left D.H hUle
  intro h2
  have h3 : 2 ∣ r * r := by rw [← hidx]; exact h2.trans hdvd
  have h4 : 2 ∣ r := (Nat.Prime.dvd_mul Nat.prime_two).mp h3 |>.elim id id
  exact hsyl h4

theorem F_norm_H₀ [Finite G] (hs : SPLSetup D.toSPLNot0)
    (hF : ∀ f ∈ D.F, ∀ k ∈ zpowers D.h₁, f * k * f⁻¹ ∈ zpowers D.h₁) : Normalizes D.F D.H := by
  have hinv : D.t⁻¹ = D.t := inv_eq_of_mul_eq_one_right (t_mul_t₀ hs)
  have hH₁ : Normalizes D.F D.H₁ := fun f hf k hk => hF f hf k hk
  have hH₂ : Normalizes D.F D.H₂ := by
    intro f hf k hk
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hk
    have hf' : D.t⁻¹ * f * D.t ∈ D.F := by
      have := t_normalizes_F hs f hf
      rw [hinv] at this ⊢
      exact this
    have e : f * (D.h₂ ^ i) * f⁻¹ =
        D.t * ((D.t⁻¹ * f * D.t) * D.h₁ ^ i * (D.t⁻¹ * f * D.t)⁻¹) * D.t⁻¹ := by
      unfold SPLNot1.h₂
      rw [conj_zpow]
      group
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp (hF _ hf' (D.h₁ ^ i) (Subgroup.zpow_mem _ (mem_zpowers _) i))
    rw [e, ← hj]
    refine mem_zpowers_iff.mpr ⟨j, ?_⟩
    unfold SPLNot1.h₂
    rw [conj_zpow]
  exact normalizes_sup hH₁ hH₂

theorem spl2Set_of_torus [Finite G] (hs : SPLSetup D.toSPLNot0)
    (hh : D.h₁ ∈ D.K₁) (hord : orderOf D.h₁ = D.q - 1)
    (hw : D.w₁ ∈ (D.S : Subgroup G) ⊓ D.K₁) (hwsq : D.w₁ * D.w₁ = D.z)
    (hinv : ∀ k ∈ zpowers D.h₁, D.w₁ * k * D.w₁⁻¹ = k⁻¹)
    (hnorm : normalizer (zpowers D.h₁ : Set G) ⊓ D.K₁ = zpowers D.h₁ ⊔ zpowers D.w₁)
    (hsyl : ¬ 2 ∣ (zpowers D.h₁ ⊓ ((D.S : Subgroup G) ⊓ D.K₁)).relIndex (zpowers D.h₁))
    (hF : ∀ f ∈ D.F, ∀ k ∈ zpowers D.h₁, f * k * f⁻¹ ∈ zpowers D.h₁) : SPL2Set D where
  cen_S₁ := cen_S₁_eq hs
  F_inf_K := F_inf_K_eq hs
  h₁_mem := hh
  h₁_ord := hord
  H_inter := H_inter₀ D hs hh hord
  w₁_mem := hw.2
  w₁_sq := hwsq
  w₁_inv := hinv
  nbhd := hnorm
  H_sylow := H_sylow₀ D hs hh hord hsyl
  w₁_mem_S₁ := (show (D.S : Subgroup G) ⊓ D.K₁ ≤ D.S₁ from inf_le_inf_left _ le_sup_left) hw
  F_norm_H := F_norm_H₀ D hs hF
  norm_le_C := norm_le_C₀ D hs hh hord

end Torus

theorem splLeafSet_of_input (hin : SL2OddAutTorus) : SPLLeafSet := by
  intro G _ _ hG D₀ hs
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQcard : Nat.card ↥(((D₀.S : Subgroup G) ⊓ D₀.K₁).subgroupOf D₀.K₁) =
      2 ^ (Nat.card ↥D₀.K₁).factorization 2 := by
    rw [← Q₁_card hs]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  let Q : Sylow 2 ↥D₀.K₁ := Sylow.ofCard (((D₀.S : Subgroup G) ⊓ D₀.K₁).subgroupOf D₀.K₁) hQcard
  have hQmap : (Q : Subgroup ↥D₀.K₁).map D₀.K₁.subtype = (D₀.S : Subgroup G) ⊓ D₀.K₁ := by
    show (((D₀.S : Subgroup G) ⊓ D₀.K₁).subgroupOf D₀.K₁).map D₀.K₁.subtype = _
    rw [Subgroup.subgroupOf_map_subtype, inf_assoc, inf_idem]
  have hcen : ∀ f ∈ D₀.F, ∀ x ∈ (Q : Subgroup ↥D₀.K₁).map D₀.K₁.subtype, f * x = x * f := by
    intro f hf x hx
    rw [hQmap] at hx
    have hx' : x ∈ D₀.S₁ :=
      (show (D₀.S : Subgroup G) ⊓ D₀.K₁ ≤ D₀.S₁ from inf_le_inf_left _ le_sup_left) hx
    exact (mem_centralizer_iff.mp (F_le_centralizer_S₁ D₀ hf) x hx').symm
  obtain ⟨h, w, hhK, hwQ, hord, hwsq, hinv, hnorm, hsyl, hF⟩ :=
    hin G D₀.K₁ D₀.q hs.comps.sl₁ hs.odd_q hs.q_ge D₀.z hs.comps.cen₁ Q D₀.F
      (F_normalizes_K₁ hs) hcen (fun f hf => F_odd D₀ hf)
  rw [hQmap] at hwQ hsyl
  exact ⟨⟨D₀, h, w⟩, rfl, spl2Set_of_torus ⟨D₀, h, w⟩ hs hhK hord hwQ hwsq hinv hnorm hsyl hF⟩

end CFSG.GH74.GLS.SP.Local
