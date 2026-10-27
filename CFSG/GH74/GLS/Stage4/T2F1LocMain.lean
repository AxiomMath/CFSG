module

public import CFSG.GH74.GLS.Stage4.T2F1LocB
public import CFSG.GH74.GLS.Stage4.T2F1LocFuse
public import CFSG.GH74.GLS.Stage4.T2F1LocTransport
public import CFSG.GH74.GLS.Stage4.T2F1LocConjQ
public import CFSG.GH74.GLS.Stage4.T2F1Red
public import CFSG.GH74.GLS.Stage4.T2P52Done
public import CFSG.GH74.GLS.Stage4.T2Bad3

public noncomputable section

namespace CFSG.GH74.GLS.Stage4.Rest.F1Loc

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4
  CFSG.GH74.GLS.Stage4.Rest CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2
  CFSG.GH74.GLS.IVK CFSG.Assembly.LowTwoRank
open scoped Pointwise

section Aux

theorem eq_one_of_central_odd {X : Type} [Group X] [Finite X] (hbot : pPrimeCore 2 X = ⊥) {x : X}
    (hc : ∀ y : X, x * y = y * x) (hodd : Odd (orderOf x)) : x = 1 := by
  let Z : Subgroup X := Subgroup.zpowers x
  have hZn : Z.Normal := ⟨fun n hn g => by
    obtain ⟨k, rfl⟩ := hn
    have : g * x ^ k * g⁻¹ = x ^ k := by
      rw [(Commute.zpow_right (show Commute g x from (hc g).symm) k).eq]; group
    rw [this]; exact Subgroup.zpow_mem_zpowers x k⟩
  have hcop : Nat.Coprime 2 (Nat.card Z) := by
    rw [Nat.card_zpowers]
    exact Nat.coprime_two_left.2 hodd
  have hle : Z ≤ pPrimeCore 2 X := le_sSup ⟨hZn, hcop⟩
  rw [hbot] at hle
  exact Subgroup.mem_bot.1 (hle (Subgroup.mem_zpowers x))

theorem sylow_equiv {G : Type} [Group G] [Finite G] (S₁ S₂ : Sylow 2 G) :
    Nonempty (↥(S₁ : Subgroup G) ≃* ↥(S₂ : Subgroup G)) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S₁ S₂
  have h : MulAut.conj g • (S₁ : Subgroup G) = (S₂ : Subgroup G) := by
    rw [← hg, Sylow.coe_subgroup_smul]
  exact ⟨(Subgroup.equivSMul (MulAut.conj g) (S₁ : Subgroup G)).trans (MulEquiv.subgroupCongr h)⟩


theorem f_eq_one_of_trivial {G : Type} [Group G] [Finite G] {N : T2N3 G} {u : G}
    (hSec : Ch6Sec5 N u) {f : G} (hf : f ∈ N.F) (hfS : ∀ s ∈ N.S, f * s = s * f)
    (hodd : Odd (orderOf f)) (hc₁ : ∀ x ∈ N.K₁, x * f = f * x) (hc₂ : ∀ x ∈ N.K₂, x * f = f * x) :
    f = 1 := by
  have hLoc := hSec.loc
  have hF5 := hSec.F5
  have hfz : f * N.z = N.z * f := hfS _ hLoc.z_mem_S
  have hfC : f ∈ Subgroup.centralizer ({N.z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 hfz
  have hle : N.K₁ ⊔ N.K₂ ⊔ N.S ⊔ N.F ≤ Subgroup.centralizer ({f} : Set G) := by
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · exact fun x hx => Subgroup.mem_centralizer_singleton_iff.2 (hc₁ x hx)
    · exact fun x hx => Subgroup.mem_centralizer_singleton_iff.2 (hc₂ x hx)
    · exact fun x hx => Subgroup.mem_centralizer_singleton_iff.2 (hfS x hx).symm
    · exact fun x hx => Subgroup.mem_centralizer_singleton_iff.2 (hF5.F_comm x hx f hf)
  have hcen : ∀ y : ↥(Subgroup.centralizer ({N.z} : Set G)),
      (⟨f, hfC⟩ : ↥(Subgroup.centralizer ({N.z} : Set G))) * y = y * ⟨f, hfC⟩ := by
    intro y
    apply Subtype.ext
    have := Subgroup.mem_centralizer_singleton_iff.1 (hle (hF5.C_le y.2))
    exact this.symm
  have hodd' : Odd (orderOf (⟨f, hfC⟩ : ↥(Subgroup.centralizer ({N.z} : Set G)))) := by
    rw [← Subgroup.orderOf_coe]; exact hodd
  have := eq_one_of_central_odd hLoc.O2prime hcen hodd'
  exact congrArg Subtype.val this


theorem mem_F_of_centralizes {G : Type} [Group G] [Finite G] {N : T2N3 G} {u : G}
    (hSec : Ch6Sec5 N u) {g : G} (hg : ∀ s ∈ N.S, g * s = s * g) (hodd : Odd (orderOf g)) :
    g ∈ N.F := by
  have hLoc := hSec.loc
  have hF5 := hSec.F5
  have hmem : g ∈ Subgroup.zpowers N.z ⊔ N.F := by
    rw [← hF5.centS]
    exact Subgroup.mem_centralizer_iff.2 (fun s hs => (hg s hs).symm)
  have hcomm : ∀ a ∈ Subgroup.zpowers N.z, ∀ b ∈ N.F, a * b = b * a := by
    rintro _ ⟨i, rfl⟩ b hb
    have hbC : b ∈ Subgroup.centralizer (N.S : Set G) := by
      rw [hF5.centS]; exact Subgroup.mem_sup_right hb
    have hbz : N.z * b = b * N.z := by
      have := Subgroup.mem_centralizer_iff.1 hbC N.z hLoc.z_mem_S
      exact this
    exact (Commute.zpow_left (show Commute N.z b from hbz) i).eq
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_comm hcomm hmem
  have hzz : N.z * N.z = 1 := by
    have h := pow_orderOf_eq_one N.z
    rw [hLoc.z_ord, sq] at h
    exact h
  rcases mem_zpowers_sq_cases hzz ha with h | h
  · rw [h, one_mul]; exact hb
  · exfalso
    have hzb : N.z * b = b * N.z := hcomm N.z (Subgroup.mem_zpowers _) b hb
    obtain ⟨o, ho⟩ := hodd
    have hpow : (a * b) ^ (orderOf (a * b)) = 1 := pow_orderOf_eq_one _
    rw [ho, h, (Commute.mul_pow (show Commute N.z b from hzb)), pow_succ, pow_mul,
      show N.z ^ 2 = 1 by rw [pow_two]; exact hzz, one_pow, one_mul] at hpow
    have hzF : N.z ∈ N.F := by
      have : N.z = (b ^ (2 * o + 1))⁻¹ := by
        rw [eq_inv_iff_mul_eq_one]; exact hpow
      rw [this]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hb _)
    have := hF5.F_odd _ hzF
    rw [hLoc.z_ord] at this
    exact absurd this (by decide)

end Aux


section Core

variable {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {z t : G} {K₁ K₂ : Subgroup G}
  {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem f1_core
    (hL : SDWreathedLayer) (hL3 : LU.Local.L3Cover) (hIVK : IVK_4_1_R_L3) {n : ℕ} (hn : 3 ≤ n)
    (hStd : Std G) (hSet : Ch6Setup G Gs (3 ^ n) (3 ^ n) z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t)
    (hab : ∀ T : Subgroup G, IsPGroup 3 ↥T → ∀ x ∈ T, ∀ y ∈ T, x * y = y * x)
    {N : T2N3 G} {u : G} (hz : N.z = z) (hK₁ : N.K₁ = K₁) (hK₂ : N.K₂ = K₂)
    (hq₁ : N.q₁ = 3 ^ n) (hq₂ : N.q₂ = 3 ^ n) (hSec : Ch6Sec5 N u)
    (hC : Ch6Coord N.toT2N2.toT2N1) {r : ℕ} (hrp : r.Prime) (hr5 : 5 ≤ r) {f : G}
    (hfo : orderOf f = r) (hf : f ∈ N.F) (hfS : ∀ s ∈ N.S, f * s = s * f) :
    ∃ m : ℕ, ∃ hzC : z ∈ Subgroup.centralizer ({f} : Set G), n = r * m ∧
      Hyp94Loc (↥(Subgroup.centralizer ({f} : Set G)) ⧸ pPrimeCore 2 ↥(Subgroup.centralizer ({f} : Set G)))
        Gs (QuotientGroup.mk (⟨z, hzC⟩ : ↥(Subgroup.centralizer ({f} : Set G)))) .G2 3 m := by
  have hLoc := hSec.loc
  have hF5 := hSec.F5
  have : Finite F₁ := hSet.finite₁
  have : Finite F₂ := hSet.finite₂
  have hodd : Odd r := hrp.odd_of_ne_two (by omega)
  have : Fact (Nat.Prime r) := ⟨hrp⟩
  have hfr : f ^ r = 1 := by rw [← hfo]; exact pow_orderOf_eq_one f
  have hq : N.q₁ = N.q₂ := hq₁.trans hq₂.symm
  have hcard₁ : Nat.card F₁ = N.q₁ := by rw [hq₁]; exact hSet.card₁
  have hcard₂ : Nat.card F₂ = N.q₂ := by rw [hq₂]; exact hSet.card₂
  have hw₁w₂ : N.w₁ * N.w₂ = N.w₂ * N.w₁ :=
    hSet.comm N.w₁ (hK₁ ▸ hLoc.w₁_mem) N.w₂ (hK₂ ▸ hLoc.w₂_mem)
  obtain ⟨φ₁, σ₁, hφ₁, hrange₁, hneg₁, -, -, -, hHK₁, hσ₁⟩ := coord_fieldAut hSec hC hcard₁ hf hfS
  obtain ⟨φ₂, σ₂, hφ₂, hrange₂, hneg₂, -, -, -, hHK₂, hσ₂⟩ :=
    coord_fieldAut₂ hSec hq hC hcard₂ hf hfS
  have hσ₁r : σ₁ ^ r = 1 := pow_eq_one_of_pow_eq_one φ₁ hφ₁ f σ₁ hσ₁ hfr
  have hσ₂r : σ₂ ^ r = 1 := pow_eq_one_of_pow_eq_one φ₂ hφ₂ f σ₂ hσ₂ hfr
  have h₁₂ : σ₁ = 1 → σ₂ = 1 := fun h1 =>
    sigma₂_eq_one_of_sigma₁_eq_one hL hL3 hIVK hn hStd hSet hRem hab hz hK₁ hK₂ hq₁ hq₂ hSec hf hodd
      hfr hHK₁ hσ₁ hφ₂ hHK₂ hσ₂ h1
  have h₂₁ : σ₂ = 1 → σ₁ = 1 := fun h2 =>
    sigma₂_eq_one_of_sigma₁_eq_one (N := N.swap) (u := u) hL hL3 hIVK hn hStd (hSet.swap rfl)
      hRem.swap hab hz hK₂ hK₁ hq₂ hq₁ (hSec.swap hq) hf hodd hfr hHK₂ hσ₂ hφ₁ hHK₁ hσ₁ h2
  have hσ₁ne : σ₁ ≠ 1 := by
    intro h1
    have h2 := h₁₂ h1
    have hodd' : Odd (orderOf f) := by rw [hfo]; exact hodd
    have hc₁ : ∀ x ∈ N.K₁, x * f = f * x := by
      intro x hx
      rw [← hrange₁] at hx
      obtain ⟨M, rfl⟩ := hx
      have := centralizes_of_eq_one φ₁ f σ₁ hσ₁ h1 M
      calc φ₁ M * f = (f * φ₁ M * f⁻¹) * f := by rw [this]
        _ = f * φ₁ M := by group
    have hc₂ : ∀ x ∈ N.K₂, x * f = f * x := by
      intro x hx
      rw [← hrange₂] at hx
      obtain ⟨M, rfl⟩ := hx
      have := centralizes_of_eq_one φ₂ f σ₂ hσ₂ h2 M
      calc φ₂ M * f = (f * φ₂ M * f⁻¹) * f := by rw [this]
        _ = f * φ₂ M := by group
    have hf1 := f_eq_one_of_trivial hSec hf hfS hodd' hc₁ hc₂
    rw [hf1, orderOf_one] at hfo
    omega
  have hr₁ : orderOf σ₁ = r := orderOf_eq_prime hσ₁r hσ₁ne
  have hr₂ : orderOf σ₂ = r := orderOf_eq_prime hσ₂r (fun h2 => hσ₁ne (h₂₁ h2))
  obtain ⟨m₁, hm₁c, hm₁⟩ := card_fixF_eq σ₁ Nat.prime_three (show Nat.card F₁ = 3 ^ n from hSet.card₁)
  obtain ⟨m₂, hm₂c, hm₂⟩ := card_fixF_eq σ₂ Nat.prime_three (show Nat.card F₂ = 3 ^ n from hSet.card₂)
  rw [hr₁] at hm₁
  rw [hr₂] at hm₂
  have hrpos : 0 < r := hrp.pos
  obtain rfl : m₂ = m₁ := Nat.eq_of_mul_eq_mul_right hrpos (hm₂.trans hm₁.symm)
  have hm1 : 1 ≤ m₂ := by
    rcases Nat.eq_zero_or_pos m₂ with h | h
    · rw [h, zero_mul] at hm₁; omega
    · exact h
  have hnm : n = r * m₂ := by rw [← hm₁, mul_comm]
  obtain ⟨a', hfa', ha'z, ha'u⟩ :=
    exists_fusion_elt hSec hf hodd hfr hw₁w₂ hφ₁ hr₁ hHK₁ hσ₁ hφ₂ hr₂ hHK₂ hσ₂
  obtain ⟨t', ht'S, g₁, g₂, hGC⟩ := f1_charts hn hSet hRem hz hK₁ hK₂ hq₁ hq₂ hSec hodd hfr hf hfS
    hφ₁ (hrange₁.trans hK₁) (hneg₁.trans hz) hσ₁ hφ₂ (hrange₂.trans hK₂) (hneg₂.trans hz) hσ₂
  have hctx := t2Ctx_of hSet hRem hLoc hz hK₁ hK₂ hq₁ hq₂
  let S₂ : Sylow 2 G := hLoc.S_pGroup.toSylow hLoc.S_sylow
  have hS₂ : (S₂ : Subgroup G) = N.S := IsPGroup.toSylow_coe _ _
  have hu2 : u * u = 1 := by
    have h := pow_orderOf_eq_one u
    rw [hLoc.u_ord, sq] at h
    exact h
  have hu1 : u ≠ 1 := by
    intro h
    have := hLoc.u_ord
    rw [h, orderOf_one] at this
    omega
  obtain ⟨S₀, S', ⟨e⟩⟩ := hSet.S_iso
  obtain ⟨e'⟩ := sylow_equiv S₂ S₀
  obtain ⟨p, fe, -, -, -, hp, hp2, hmodel, -⟩ := hSet.model
  have hH := hyp94Loc_of_gchart (m := m₂) hm1 (show Nat.card (fixF σ₁) = 3 ^ m₂ from hm₁c)
    (show Nat.card (fixF σ₂) = 3 ^ m₂ from hm₂c) hGC S₂ (fun s hs => (hfS s (hS₂ ▸ hs)).symm)
    (by rw [hS₂, ← hz]; exact hLoc.z_mem_S)
    (fun s hs => by rw [← hz]; exact (hLoc.z_cent_S s (hS₂ ▸ hs)).symm)
    (fun x hx hc => hctx.ZS x (hS₂ ▸ hx) (fun s hs => hc s (hS₂.symm ▸ hs)))
    (hS₂ ▸ hLoc.u_mem_S) hu2 hu1 (by rw [← hz]; exact hLoc.u_ne) (by rw [← hz]; exact hLoc.u_comm.symm)
    ⟨S', ⟨e'.trans e⟩⟩ ⟨p, fe, hp, hp2, hmodel⟩
    ⟨a', hfa', by rw [← hz]; exact ha'z, by rw [← hz]; exact ha'u⟩
  obtain ⟨hzC, hH'⟩ := hH
  exact ⟨m₂, hzC, hnm, hH'⟩

end Core


section Final

theorem ch6T2F1Local_proved
    (hL : SDWreathedLayer) (hL3 : LU.Local.L3Cover) (hIVK : IVK_4_1_R_L3) : Ch6T2F1Local := by
  intro G _ _ hStd hr3 Gs _ n hn hAt hBad z K₁ K₂ F₁ F₂ _ _ t hSet hRem r hrp hr5 f hfo hSyl
  have hn0 : n ≠ 0 := by omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨N₁, u, hz, hK₁, hK₂, hq₁, hq₂, hLoc, hCoord⟩ :=
    ch6T2P51 G Gs (3 ^ n) (3 ^ n) z K₁ K₂ F₁ F₂ t hSet hRem rfl
  obtain ⟨F, hF5⟩ :=
    ch6T2P52 G Gs (3 ^ n) (3 ^ n) z K₁ K₂ F₁ F₂ t hSet hRem N₁ u hz hK₁ hK₂ hq₁ hq₂ hLoc hCoord
  obtain ⟨a, haU, hW⟩ :=
    ch6T2P53 G hr3 Gs (3 ^ n) (3 ^ n) z K₁ K₂ F₁ F₂ t hSet hRem ⟨N₁, F⟩ u hz hK₁ hK₂ hq₁ hq₂ hLoc
      hCoord hF5
  let N : T2N3 G := ⟨⟨N₁, F⟩, a⟩
  have hSec : Ch6Sec5 N u := ⟨hLoc, hF5, hW, haU⟩
  obtain ⟨P₀, hP₀⟩ := t2_bad3 hSet hBad
  have hab3 := t2F1_three_abelian hn0 hSet hLoc hK₁ hK₂ hq₁ hq₂
  have hno : ∀ T : Subgroup G, IsPGroup 3 ↥T → ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := by
    intro T hT x hx y hy
    obtain ⟨P, hTP⟩ := hT.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P₀ P
    have hx' := hTP hx
    have hy' := hTP hy
    rw [← hg, Sylow.coe_subgroup_smul] at hx' hy'
    obtain ⟨x', hx'', hxx⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hx'
    obtain ⟨y', hy'', hyy⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hy'
    have hc : x' * y' = y' * x' := hab3 (P₀ : Subgroup G) hP₀ P₀.isPGroup' x' hx'' y' hy''
    have hxx' : x = g * x' * g⁻¹ := by
      rw [← hxx]; simp [MulAut.smul_def, MulAut.conj_apply]
    have hyy' : y = g * y' * g⁻¹ := by
      rw [← hyy]; simp [MulAut.smul_def, MulAut.conj_apply]
    rw [hxx', hyy']
    calc g * x' * g⁻¹ * (g * y' * g⁻¹) = g * (x' * y') * g⁻¹ := by group
      _ = g * (y' * x') * g⁻¹ := by rw [hc]
      _ = g * y' * g⁻¹ * (g * x' * g⁻¹) := by group
  obtain ⟨S, hSz, hfS⟩ := hSyl
  let S₂ : Sylow 2 G := hLoc.S_pGroup.toSylow hLoc.S_sylow
  have hS₂ : (S₂ : Subgroup G) = N.S := IsPGroup.toSylow_coe _ _
  have hNz : ∀ s ∈ (S₂ : Subgroup G), s * z = z * s := fun s hs => by
    rw [← hz]; exact hLoc.z_cent_S s (hS₂ ▸ hs)
  obtain ⟨c, hcz, hc⟩ := exists_conj_sylow_centralizer S S₂ hSz hNz
  have hzN : z ∈ (S₂ : Subgroup G) := by rw [hS₂, ← hz]; exact hLoc.z_mem_S
  have hzS : z ∈ (S : Subgroup G) := by
    have := conj_sylow_onto S S₂ c hc z hzN
    have e : c⁻¹ * z * c = z := by
      calc c⁻¹ * z * c = c⁻¹ * (z * c) := by group
        _ = c⁻¹ * (c * z) := by rw [hcz]
        _ = z := by group
    rwa [e] at this
  have hzC : z ∈ Subgroup.centralizer ({f} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hfS z hzS)
  have hf'S : ∀ s ∈ N.S, (c * f * c⁻¹) * s = s * (c * f * c⁻¹) := by
    intro s hs
    have hmem := conj_sylow_onto S S₂ c hc s (hS₂ ▸ hs)
    have h1 : (c⁻¹ * s * c) * f = f * (c⁻¹ * s * c) := Subgroup.mem_centralizer_iff.1 hfS _ hmem
    calc (c * f * c⁻¹) * s = c * (f * (c⁻¹ * s * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * s * c) * f) * c⁻¹ := by rw [h1]
      _ = s * (c * f * c⁻¹) := by group
  have hfo' : orderOf (c * f * c⁻¹) = r := by
    have := MulEquiv.orderOf_eq (MulAut.conj c) f
    rw [MulAut.conj_apply] at this
    rw [this, hfo]
  have hrodd : Odd r := hrp.odd_of_ne_two (by omega)
  have hf'F : c * f * c⁻¹ ∈ N.F :=
    mem_F_of_centralizes hSec hf'S (by rw [hfo']; exact hrodd)
  obtain ⟨m, hzC', hnm, hH⟩ := f1_core hL hL3 hIVK hn hStd hSet hRem hno hz hK₁ hK₂ hq₁ hq₂ hSec
    hCoord hrp hr5 hfo' hf'F hf'S
  refine ⟨m, hzC, hnm, ?_⟩
  obtain ⟨e, he⟩ := exists_quot_equiv_of_conj f c
  refine hyp94Loc_of_mulEquiv e ?_
  have hcz' : c * z * c⁻¹ = z := by rw [hcz]; group
  have hx' : c * z * c⁻¹ ∈ Subgroup.centralizer ({c * f * c⁻¹} : Set G) := by rw [hcz']; exact hzC'
  rw [he z hzC hx']
  have : (⟨c * z * c⁻¹, hx'⟩ : ↥(Subgroup.centralizer ({c * f * c⁻¹} : Set G))) = ⟨z, hzC'⟩ :=
    Subtype.ext hcz'
  rw [this]
  exact hH

end Final

end CFSG.GH74.GLS.Stage4.Rest.F1Loc
