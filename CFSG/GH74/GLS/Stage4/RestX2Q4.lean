module

public import CFSG.GH74.GLS.Stage4.RestX2Q3
public import CFSG.GH74.GLS.Stage4.RestX2Q2
public import CFSG.GH74.GLS.Stage4.T9Inequiv

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.BNPair CFSG.Assembly.LowTwoRank DodecA CFSG.GH74.GLS.Stage4.Rest.T6
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

structure RootGrp (D : Ch6Notation G) (E K : Subgroup G) (q : ℕ) : Prop where
  card : Nat.card ↥E = q
  pow : ∃ n : ℕ, q = D.p ^ n
  le : E ≤ K
  exp : ∀ x ∈ E, x ^ D.p = 1
  zc : ∀ x ∈ E, D.z * x * D.z⁻¹ = x
  ui : ∀ x ∈ E, D.u * x * D.u⁻¹ = x⁻¹
  hinv : HInv D.H E

section Root

variable {D : Ch6Notation G}

theorem AllX2Hyp.rootGrp_X₁' (hh : AllX2Hyp D) : RootGrp D D.X₁' D.K₁ D.q₁ where
  card := hh.basics.card_X₁'
  pow := hh.basics.q₁_pow
  le := by rw [hh.basics.K₁_eq]; exact le_sup_right
  exp := hh.basics.X₁'_exp
  zc := hh.basics.z_comm_X₁'
  ui := hh.u_inv₁'
  hinv := hh.basics.H_norm_X₁'

theorem AllX2Hyp.rootGrp_X₂ (hh : AllX2Hyp D) : RootGrp D D.X₂ D.K₂ D.q₂ where
  card := hh.basics.card_X₂
  pow := hh.basics.q₂_pow
  le := by rw [hh.basics.K₂_eq]; exact le_sup_left
  exp := hh.basics.X₂_exp
  zc := hh.basics.z_comm_X₂
  ui := hh.u_inv₂
  hinv := hh.basics.H_norm_X₂

theorem AllX2Hyp.rootGrp_X₂' (hh : AllX2Hyp D) : RootGrp D D.X₂' D.K₂ D.q₂ where
  card := hh.basics.card_X₂'
  pow := hh.basics.q₂_pow
  le := by rw [hh.basics.K₂_eq]; exact le_sup_right
  exp := hh.basics.X₂'_exp
  zc := hh.basics.z_comm_X₂'
  ui := hh.u_inv₂'
  hinv := hh.basics.H_norm_X₂'

theorem RootGrp.conj_pGroup (hb : Ch6Basics D) {E K : Subgroup G} {q : ℕ} (hE : RootGrp D E K q) (g : G) :
    IsPGroup D.p ↥(conjBy g E) := by
  have : Fact D.p.Prime := ⟨hb.prime⟩
  obtain ⟨n, hn⟩ := hE.pow
  exact IsPGroup.of_card (n := n) (by rw [DodecA.card_conjBy, hE.card, hn])

theorem RootGrp.cent_u {E K : Subgroup G} {q : ℕ} (hE : RootGrp D E K q) :
    conjBy D.a E ≤ Subgroup.centralizer ({D.u} : Set G) := by
  intro x hx
  rw [mem_conjBy_iff] at hx
  have h := hE.zc _ hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 : (D.a * x * D.a⁻¹) * D.z = D.z * (D.a * x * D.a⁻¹) := by
    calc (D.a * x * D.a⁻¹) * D.z = (D.z * (D.a * x * D.a⁻¹) * D.z⁻¹) * D.z := by rw [h]
      _ = D.z * (D.a * x * D.a⁻¹) := by group
  have : x * D.u = D.u * x := by
    simp only [Ch6Notation.u]
    calc x * (D.a⁻¹ * D.z * D.a) = D.a⁻¹ * ((D.a * x * D.a⁻¹) * D.z) * D.a := by group
      _ = D.a⁻¹ * (D.z * (D.a * x * D.a⁻¹)) * D.a := by rw [h1]
      _ = D.a⁻¹ * D.z * D.a * x := by group
  exact this

theorem RootGrp.cent_zu (hh : AllX2Hyp D) {E K : Subgroup G} {q : ℕ} (hE : RootGrp D E K q) :
    conjBy (D.a ^ 2) E ≤ Subgroup.centralizer ({D.z * D.u} : Set G) := by
  have hb := hh.basics
  intro x hx
  rw [mem_conjBy_iff] at hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hx' : D.a⁻¹ * x * D.a ∈ E := by
    have := hE.hinv ((D.a ^ 3)⁻¹) (D.H.inv_mem hb.a_cube) _ hx
    have e : (D.a ^ 3)⁻¹ * (D.a ^ 2 * x * (D.a ^ 2)⁻¹) * ((D.a ^ 3)⁻¹)⁻¹ = D.a⁻¹ * x * D.a := by group
    rwa [e] at this
  have h := hE.zc _ hx'
  have h1 : (D.a⁻¹ * x * D.a) * D.z = D.z * (D.a⁻¹ * x * D.a) := by
    calc (D.a⁻¹ * x * D.a) * D.z = (D.z * (D.a⁻¹ * x * D.a) * D.z⁻¹) * D.z := by rw [h]
      _ = D.z * (D.a⁻¹ * x * D.a) := by group
  have e : D.z * D.u = D.a * D.z * D.a⁻¹ := hh.a_conj₁.symm
  rw [e]
  calc x * (D.a * D.z * D.a⁻¹) = D.a * ((D.a⁻¹ * x * D.a) * D.z) * D.a⁻¹ := by group
    _ = D.a * (D.z * (D.a⁻¹ * x * D.a)) * D.a⁻¹ := by rw [h1]
    _ = D.a * D.z * D.a⁻¹ * x := by group

end Root

section Pairs

variable {D : Ch6Notation G}

theorem RootGrp.inf_bot (hh : AllX2Hyp D) {E F : Subgroup G} {q q' : ℕ} (hE : RootGrp D E D.K₂ q)
    (hF : RootGrp D F D.K₁ q') : E ⊓ F = ⊥ := by
  have hb := hh.basics
  rw [eq_bot_iff]
  intro x hx
  have hxz : x ∈ Subgroup.zpowers D.z := hh.K_inter ⟨hF.le hx.2, hE.le hx.1⟩
  rcases t2C_zpowers_cases hb.z_mul_z hxz with h1 | h1
  · exact h1
  · exfalso
    have h2 := hE.exp x hx.1
    rw [h1] at h2
    have h3 : orderOf D.z ∣ D.p := orderOf_dvd_of_pow_eq_one h2
    rw [hb.z_ord] at h3
    exact hb.p_ne_two ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hb.prime).1 h3).symm

theorem conjBy_inf_bot {E F : Subgroup G} (g : G) (h : E ⊓ F = ⊥) : conjBy g E ⊓ conjBy g F = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hx' : g * x * g⁻¹ ∈ E ⊓ F := ⟨mem_conjBy_iff.1 hx.1, mem_conjBy_iff.1 hx.2⟩
  rw [h] at hx'
  have h1 : g * x * g⁻¹ = 1 := Subgroup.mem_bot.1 hx'
  have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
  rw [this, h1]
  simp

end Pairs

section PairLemmas

theorem pairData_one {N₄ : T2N4 G} (hh : AllX2Hyp N₄.toCh6) {E F : Subgroup G} {q q' : ℕ}
    (hE : RootGrp N₄.toCh6 E N₄.K₂ q) (hF : RootGrp N₄.toCh6 F N₄.K₁ q')
    (cE : conjBy N₄.a E ≤ Subgroup.centralizer (N₄.X₁ : Set G))
    (cF : conjBy N₄.a F ≤ Subgroup.centralizer (N₄.X₁ : Set G)) :
    PairData N₄.toT2N3.swap N₄.p N₄.toCh6.u (conjBy N₄.a E) (conjBy N₄.a F) where
  p₁ := hE.conj_pGroup hh.basics _
  p₂ := hF.conj_pGroup hh.basics _
  C₁ := cE
  C₂ := cF
  z₁ := fun r hr => by
    have h : N₄.z * r * N₄.z⁻¹ = r⁻¹ := (z_inv_conjBy_a hh hE.zc hE.ui).1 r hr
    show N₄.z * r * N₄.z⁻¹ * r ∈ N₄.X₁
    rw [h]; simp
  z₂ := fun r hr => by
    have h : N₄.z * r * N₄.z⁻¹ = r⁻¹ := (z_inv_conjBy_a hh hF.zc hF.ui).1 r hr
    show N₄.z * r * N₄.z⁻¹ * r ∈ N₄.X₁
    rw [h]; simp
  v₁ := hE.cent_u
  v₂ := hF.cent_u
  comm := comm_conjBy₂ (fun x hx y hy => (hh.basics.K_comm y (hF.le hy) x (hE.le hx)).symm) N₄.a
  inf := conjBy_inf_bot _ (RootGrp.inf_bot hh hE hF)

theorem pairData_two {N₄ : T2N4 G} (hh : AllX2Hyp N₄.toCh6) {E F : Subgroup G} {q q' : ℕ}
    (hE : RootGrp N₄.toCh6 E N₄.K₂ q) (hF : RootGrp N₄.toCh6 F N₄.K₁ q')
    (cE : conjBy (N₄.a ^ 2) E ≤ Subgroup.centralizer (N₄.X₁ : Set G))
    (cF : conjBy (N₄.a ^ 2) F ≤ Subgroup.centralizer (N₄.X₁ : Set G)) :
    PairData N₄.toT2N3.swap N₄.p (N₄.toT2N3.swap.z * N₄.toCh6.u) (conjBy (N₄.a ^ 2) E)
      (conjBy (N₄.a ^ 2) F) where
  p₁ := hE.conj_pGroup hh.basics _
  p₂ := hF.conj_pGroup hh.basics _
  C₁ := cE
  C₂ := cF
  z₁ := fun r hr => by
    have h : N₄.z * r * N₄.z⁻¹ = r⁻¹ := (z_inv_conjBy_a hh hE.zc hE.ui).2 r hr
    show N₄.z * r * N₄.z⁻¹ * r ∈ N₄.X₁
    rw [h]; simp
  z₂ := fun r hr => by
    have h : N₄.z * r * N₄.z⁻¹ = r⁻¹ := (z_inv_conjBy_a hh hF.zc hF.ui).2 r hr
    show N₄.z * r * N₄.z⁻¹ * r ∈ N₄.X₁
    rw [h]; simp
  v₁ := hE.cent_zu hh
  v₂ := hF.cent_zu hh
  comm := comm_conjBy₂ (fun x hx y hy => (hh.basics.K_comm y (hF.le hy) x (hE.le hx)).symm) (N₄.a ^ 2)
  inf := conjBy_inf_bot _ (RootGrp.inf_bot hh hE hF)

end PairLemmas

section Orientation

theorem allX2_pairs {N₄ : T2N4 G} (hh : AllX2Hyp N₄.toCh6) {α γ : Bool} (hαγ : α ≠ γ)
    (hSh : N₄.toCh6.Shape α false γ false) :
    ∃ E₁ E₂ : Subgroup G, (E₁ = N₄.X₂ ∨ E₁ = N₄.X₂') ∧ (E₂ = N₄.X₂ ∨ E₂ = N₄.X₂') ∧
      PairData N₄.toT2N3.swap N₄.p N₄.toCh6.u (conjBy N₄.a E₁) (conjBy N₄.a N₄.X₁') ∧
      PairData N₄.toT2N3.swap N₄.p (N₄.toT2N3.swap.z * N₄.toCh6.u) (conjBy (N₄.a ^ 2) E₂)
        (conjBy (N₄.a ^ 2) N₄.X₁') ∧
      Nat.card ↥(conjBy N₄.a E₁) * Nat.card ↥(conjBy N₄.a N₄.X₁') = N₄.q₁ * N₄.q₂ ∧
      Nat.card ↥(conjBy (N₄.a ^ 2) E₂) * Nat.card ↥(conjBy (N₄.a ^ 2) N₄.X₁') = N₄.q₁ * N₄.q₂ := by
  have hb := hh.basics
  obtain ⟨hPα, hPβ, hPγ, hPδ⟩ := Ch6Notation.shape_le hSh
  rw [Ch6Notation.B_false] at hPβ hPδ
  have hX₁' := hh.rootGrp_X₁'
  have hX₂ := hh.rootGrp_X₂
  have hX₂' := hh.rootGrp_X₂'
  have hcards : ∀ (g : G) {E F : Subgroup G} {q q' : ℕ}, RootGrp N₄.toCh6 E N₄.K₂ q →
      RootGrp N₄.toCh6 F N₄.K₁ q' → Nat.card ↥(conjBy g E) * Nat.card ↥(conjBy g F) = q' * q := by
    intro g E F q q' hE hF
    rw [DodecA.card_conjBy, DodecA.card_conjBy, hE.card, hF.card, mul_comm]
  cases α <;> cases γ
  · exact absurd rfl hαγ
  ·
    have hAm : (Ch6Notation.A N₄.toCh6 false) = N₄.X₁ := Ch6Notation.A_false
    have hAm' : (Ch6Notation.A N₄.toCh6 true) = N₄.X₁' := Ch6Notation.A_true
    rw [hAm] at hPα
    rw [hAm'] at hPγ
    have hm := hh.mirror
    have c1 : conjBy ((N₄.toCh6.mirror).a ^ 2) N₄.toCh6.mirror.X₁ ≤ N₄.toCh6.mirror.P := by
      show conjBy (N₄.toCh6.a⁻¹ ^ 2) N₄.toCh6.X₁ ≤ N₄.toCh6.P
      rw [conjBy_inv_a_sq_eq hb hb.H_norm_X₁]; exact hPα
    have c2 : conjBy (N₄.toCh6.mirror).a N₄.toCh6.mirror.X₁' ≤ N₄.toCh6.mirror.P := by
      show conjBy N₄.toCh6.a⁻¹ N₄.toCh6.X₁' ≤ N₄.toCh6.P
      rw [conjBy_inv_a_eq hb hb.H_norm_X₁']; exact hPγ
    have c4 : conjBy ((N₄.toCh6.mirror).a ^ 2) N₄.toCh6.mirror.X₂ ≤ N₄.toCh6.mirror.P := by
      show conjBy (N₄.toCh6.a⁻¹ ^ 2) N₄.toCh6.X₂ ≤ N₄.toCh6.P
      rw [conjBy_inv_a_sq_eq hb hb.H_norm_X₂]; exact hPβ
    obtain ⟨hA₂, hA₃, hA₄, hA₅⟩ := allX2_cont hm c1 c2 c4
    have e1 : conjBy (N₄.a⁻¹) N₄.X₂ = conjBy (N₄.a ^ 2) N₄.X₂ := conjBy_inv_a_eq hb hb.H_norm_X₂
    have e2 : conjBy ((N₄.a⁻¹) ^ 2) N₄.X₂' = conjBy N₄.a N₄.X₂' := conjBy_inv_a_sq_eq hb hb.H_norm_X₂'
    have e3 : conjBy (N₄.a⁻¹) N₄.X₁' = conjBy (N₄.a ^ 2) N₄.X₁' := conjBy_inv_a_eq hb hb.H_norm_X₁'
    have e4 : conjBy ((N₄.a⁻¹) ^ 2) N₄.X₁' = conjBy N₄.a N₄.X₁' := conjBy_inv_a_sq_eq hb hb.H_norm_X₁'
    have hA₂' : conjBy (N₄.a ^ 2) N₄.X₂ ≤ Subgroup.centralizer (N₄.X₁ : Set G) := by rw [← e1]; exact hA₂
    have hA₃' : conjBy N₄.a N₄.X₂' ≤ Subgroup.centralizer (N₄.X₁ : Set G) := by rw [← e2]; exact hA₃
    have hA₄' : conjBy (N₄.a ^ 2) N₄.X₁' ≤ Subgroup.centralizer (N₄.X₁ : Set G) := by rw [← e3]; exact hA₄
    have hA₅' : conjBy N₄.a N₄.X₁' ≤ Subgroup.centralizer (N₄.X₁ : Set G) := by rw [← e4]; exact hA₅
    exact ⟨N₄.X₂', N₄.X₂, Or.inr rfl, Or.inl rfl, pairData_one hh hX₂' hX₁' hA₃' hA₅',
      pairData_two hh hX₂ hX₁' hA₂' hA₄', hcards _ hX₂' hX₁', hcards _ hX₂ hX₁'⟩
  ·
    have hAm : (Ch6Notation.A N₄.toCh6 false) = N₄.X₁ := Ch6Notation.A_false
    have hAm' : (Ch6Notation.A N₄.toCh6 true) = N₄.X₁' := Ch6Notation.A_true
    rw [hAm'] at hPα
    rw [hAm] at hPγ
    obtain ⟨hA₂, hA₃, hA₄, hA₅⟩ := allX2_cont hh hPγ hPα hPδ
    exact ⟨N₄.X₂, N₄.X₂', Or.inl rfl, Or.inr rfl, pairData_one hh hX₂ hX₁' hA₂ hA₄,
      pairData_two hh hX₂' hX₁' hA₃ hA₅, hcards _ hX₂ hX₁', hcards _ hX₂' hX₁'⟩
  · exact absurd rfl hαγ

end Orientation

section Assembly

variable {D : Ch6Notation G}

theorem S6Shape.mem_R₂_of_inv (hS : S6Shape D) (hb : Ch6Basics D) {y : G} (hyP : y ∈ D.P)
    (hy : D.z * y * D.z⁻¹ = y⁻¹) : y ∈ D.R₂ := by
  have hX₁K : D.X₁ ≤ D.K₁ := by rw [hb.K₁_eq]; exact le_sup_left
  have hnorm : D.X₁ ≤ normalizer (D.R₂ : Set G) := by
    intro x hx
    rw [mem_normalizer_iff]
    intro r
    constructor
    · intro hr
      exact hS.K₁_normR₂ x (hX₁K hx) r hr
    · intro hr
      have := hS.K₁_normR₂ x⁻¹ (D.K₁.inv_mem (hX₁K hx)) _ hr
      simpa [mul_assoc] using this
  have hmul : (↑(D.R₂ ⊔ D.X₁) : Set G) = (D.R₂ : Set G) * (D.X₁ : Set G) :=
    coe_mul_of_right_le_normalizer_left D.R₂ D.X₁ hnorm
  have hyP' : y ∈ (D.R₂ : Set G) * (D.X₁ : Set G) := by
    rw [← hmul, ← hS.P_eq]
    exact hyP
  obtain ⟨r, hr, x, hx, rfl⟩ := hyP'
  have hzr : D.z * r * D.z⁻¹ ∈ D.R₂ := hS.K₁_normR₂ _ hb.z_mem_K₁ r hr
  have hzx : D.z * x * D.z⁻¹ = x := hb.z_comm_X₁ x hx
  have hxr : x * (D.z * r * D.z⁻¹) * x⁻¹ ∈ D.R₂ := hS.K₁_normR₂ x (hX₁K hx) _ hzr
  have h2 : (D.z * r * D.z⁻¹) * x = x⁻¹ * r⁻¹ := by
    have e : D.z * (r * x) * D.z⁻¹ = (D.z * r * D.z⁻¹) * (D.z * x * D.z⁻¹) := by group
    rw [e, hzx] at hy
    rw [hy]
    group
  have hxx : x * x ∈ D.R₂ := by
    have e : x * x = (x * (D.z * r * D.z⁻¹) * x⁻¹)⁻¹ * r⁻¹ := by
      calc x * x = (x * (D.z * r * D.z⁻¹) * x⁻¹)⁻¹ * (x * ((D.z * r * D.z⁻¹) * x)) := by group
        _ = (x * (D.z * r * D.z⁻¹) * x⁻¹)⁻¹ * (x * (x⁻¹ * r⁻¹)) := by rw [h2]
        _ = (x * (D.z * r * D.z⁻¹) * x⁻¹)⁻¹ * r⁻¹ := by group
    rw [e]
    exact D.R₂.mul_mem (D.R₂.inv_mem hxr) (D.R₂.inv_mem hr)
  have hxR : x ∈ D.R₂ := by
    obtain ⟨k, hk⟩ := hb.prime.odd_of_ne_two hb.p_ne_two
    have h6 : (x * x) ^ k * x = 1 := by
      rw [← pow_two, ← pow_mul, ← pow_succ, ← hk]
      exact hb.X₁_exp x hx
    have : x = ((x * x) ^ k)⁻¹ := eq_inv_of_mul_eq_one_right h6
    rw [this]
    exact D.R₂.inv_mem (pow_mem hxx k)
  exact D.R₂.mul_mem hr hxR

theorem AllX2Hyp.of_good (hPre : Ch6Pre D) (hS6 : S6Core D) : AllX2Hyp D where
  basics := hPre.basics
  K_inter := hPre.pre.K_inter
  P_pGroup := hS6.P_pGroup
  P_normH := hS6.P_normH
  X₂_central := hS6.X₂_central
  X₁_le := by rw [hS6.P_eq]; exact le_sup_right
  inv_R₂ := fun _ hy hz => S6Shape.mem_R₂_of_inv hS6.toShape hPre.basics hy hz
  R₂_comm := hS6.R₂_comm
  u_inv₁ := hPre.pre.u_inv_X₁
  u_inv₁' := hPre.pre.u_inv_X₁'
  u_inv₂ := hPre.pre.u_inv_X₂
  u_inv₂' := hPre.pre.u_inv_X₂'
  a_conj₁ := hPre.a_conj.2.1
  a_conj₂ := hPre.a_conj.2.2.2

end Assembly

section Main

theorem good_data [Finite G] {N : T2N3 G} {u : G} (hctx : T6.T6Ctx N u 3)
    (hSle : N.S ≤ ⨆ g ∈ N.Nsub, conjBy g (N.K₁ ⊔ N.K₂))
    (hcard : Nat.card ↥(T6.R₂ N 3) = N.q₁ ^ 2 * N.q₂ ^ 3) {P₀ : Subgroup G} (hP₀F : P₀ ≤ N.F)
    (hP₀p : IsPGroup 3 ↥P₀)
    (hSyl : ∃ T : Sylow 3 G, (T : Subgroup G) = (T6.R₂ N 3 ⊔ N.X₁) ⊔ P₀) :
    S6Core (⟨N, 3, P₀, T6.R₂ N 3 ⊔ N.X₁⟩ : T2N4 G).toCh6 ∧
      Ch6Pre (⟨N, 3, P₀, T6.R₂ N 3 ⊔ N.X₁⟩ : T2N4 G).toCh6 := by
  have hS6 := T6.s6Core_of_parts hctx hcard P₀ hP₀F hP₀p hSyl
  have hshape := T9.t9_shape_core (N4 := (⟨N, 3, P₀, T6.R₂ N 3 ⊔ N.X₁⟩ : T2N4 G)) hctx hS6.toShape
  have hNum₄ : Ch6NumD 3 N.q₁ N.q₂ :=
    ⟨hctx.prime, hctx.p_ne_two, hctx.q₁_pow, hctx.q₂_pow, hctx.q_rel⟩
  exact ⟨hS6, Ch6Pre.of_stages_core (N := (⟨N, 3, P₀, T6.R₂ N 3 ⊔ N.X₁⟩ : T2N4 G)) hNum₄ hctx.sec5
    hSle hS6 hshape⟩

end Main

end CFSG.GH74.GLS.Stage4.Rest
