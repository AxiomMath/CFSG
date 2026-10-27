module

public import CFSG.GH74.GLS.IVK.L2.BNMatrices
public import CFSG.GH74.GLS.IVK.L2.BNRankOne

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG.Assembly.LowTwoRank
open scoped MatrixGroups Pointwise

namespace L2BN

variable {F : Type} [Field F]

section Groups

noncomputable abbrev BB (H₁ : Subgroup (GL (Fin 2) F)) : Subgroup (GL (Fin 2) F) :=
  normalizer (((uHom F).range : Subgroup (GL (Fin 2) F)) : Set (GL (Fin 2) F)) ⊓ H₁

noncomputable abbrev DD (H₁ : Subgroup (GL (Fin 2) F)) : Subgroup (GL (Fin 2) F) :=
  diagGL F ⊓ H₁

noncomputable abbrev NN (H₁ : Subgroup (GL (Fin 2) F)) : Subgroup (GL (Fin 2) F) :=
  normalizer ((DD H₁ : Subgroup (GL (Fin 2) F)) : Set (GL (Fin 2) F)) ⊓ H₁

variable {H₁ : Subgroup (GL (Fin 2) F)}

theorem BB_le_H₁ : BB H₁ ≤ H₁ := inf_le_right

theorem NN_le_H₁ : NN H₁ ≤ H₁ := inf_le_right

theorem mem_DD_of {g : GL (Fin 2) F} (h1 : g ∈ diagGL F) (h2 : g ∈ H₁) : g ∈ DD H₁ :=
  Subgroup.mem_inf.2 ⟨h1, h2⟩

theorem uT_mem_H₁ (hH : StatedSL 2 F ≤ H₁) (t : F) : uT t ∈ H₁ := hH (uT_mem_statedSL t)

theorem wGL_mem_H₁ (hH : StatedSL 2 F ≤ H₁) : wGL F ∈ H₁ := hH wGL_mem_statedSL

theorem U_le_H₁ (hH : StatedSL 2 F ≤ H₁) : (uHom F).range ≤ H₁ := fun g hg => by
  obtain ⟨t, rfl⟩ := (mem_range_uHom_iff' g).1 hg
  exact uT_mem_H₁ hH t

theorem U_le_B (hH : StatedSL 2 F ≤ H₁) : (uHom F).range ≤ BB H₁ :=
  le_inf Subgroup.le_normalizer (U_le_H₁ hH)

theorem D_le_B : DD H₁ ≤ BB H₁ := fun _ hg => ⟨diag_mem_normalizer_U hg.1, hg.2⟩

theorem D_le_N : DD H₁ ≤ NN H₁ := fun _ hg => ⟨Subgroup.le_normalizer hg, hg.2⟩

theorem B_c_zero {g : GL (Fin 2) F} (hg : g ∈ BB H₁) : g.1 1 0 = 0 :=
  c_eq_zero_of_mem_normalizer_U hg.1

theorem uT_inv_mul_aux (s : F) (g : GL (Fin 2) F) : g = uT s * (uT (-s) * g) := by
  rw [← mul_assoc, uT_mul, add_neg_cancel, uT_zero, one_mul]

theorem mem_B_of_c_zero (hH : StatedSL 2 F ≤ H₁) {g : GL (Fin 2) F} (hgH : g ∈ H₁)
    (hg : g.1 1 0 = 0) : g ∈ BB H₁ := by
  have hδ : uT (-(g.1 0 1 / g.1 1 1)) * g ∈ DD H₁ :=
    mem_DD_of (upper_decomp_left hg) (mul_mem (uT_mem_H₁ hH _) hgH)
  rw [uT_inv_mul_aux (g.1 0 1 / g.1 1 1) g]
  exact mul_mem (U_le_B hH (uT_mem_range _)) (D_le_B hδ)

theorem B_eq (hH : StatedSL 2 F ≤ H₁) : BB H₁ = (uHom F).range ⊔ DD H₁ := by
  apply le_antisymm
  · intro g hg
    have hδ : uT (-(g.1 0 1 / g.1 1 1)) * g ∈ DD H₁ :=
      mem_DD_of (upper_decomp_left (B_c_zero hg)) (mul_mem (uT_mem_H₁ hH _) (BB_le_H₁ hg))
    rw [uT_inv_mul_aux (g.1 0 1 / g.1 1 1) g]
    exact mul_mem (Subgroup.mem_sup_left (uT_mem_range _)) (Subgroup.mem_sup_right hδ)
  · exact sup_le (U_le_B hH) D_le_B

theorem exists_dg [Finite F] (hF : 3 < Nat.card F) (hH : StatedSL 2 F ≤ H₁) :
    ∃ a : Fˣ, (a : F) ≠ (a : F)⁻¹ ∧ dg a a⁻¹ ∈ DD H₁ := by
  obtain ⟨a, ha⟩ := exists_ne_inv hF
  refine ⟨a, ha, dg_mem_diagGL _ _, hH (dg_mem_statedSL ?_)⟩
  simp

theorem N_cases [Finite F] (hH : StatedSL 2 F ≤ H₁) (hF : 3 < Nat.card F) {g : GL (Fin 2) F}
    (hg : g ∈ NN H₁) : (g.1 0 1 = 0 ∧ g.1 1 0 = 0) ∨ (g.1 0 0 = 0 ∧ g.1 1 1 = 0) := by
  obtain ⟨a, ha, hδ⟩ := exists_dg hF hH
  have := (Subgroup.mem_normalizer_iff.1 (Subgroup.mem_inf.1 hg).1 (dg a a⁻¹)).1 hδ
  exact diag_or_antidiag ha this.1 rfl

theorem w_mem_N (hH : StatedSL 2 F ≤ H₁) : wGL F ∈ NN H₁ := by
  refine Subgroup.mem_inf.2 ⟨?_, wGL_mem_H₁ hH⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hw := wGL_mem_H₁ hH
  rw [Subgroup.mem_inf, Subgroup.mem_inf, ← wGL_conj_mem_diagGL_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, mul_mem (mul_mem hw h2) (inv_mem hw)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have := mul_mem (mul_mem (inv_mem hw) h2) hw
    simpa [mul_assoc] using this

theorem N_eq [Finite F] (hH : StatedSL 2 F ≤ H₁) (hF : 3 < Nat.card F) :
    NN H₁ = DD H₁ ⊔ zpowers (wGL F) := by
  apply le_antisymm
  · intro g hg
    rcases N_cases hH hF hg with ⟨h01, h10⟩ | ⟨h00, h11⟩
    · exact Subgroup.mem_sup_left (mem_DD_of ((mem_diagGL_iff g).2 ⟨h01, h10⟩) (NN_le_H₁ hg))
    · have hd : g * (wGL F)⁻¹ ∈ DD H₁ :=
        mem_DD_of (mul_wGL_inv_mem_diagGL h00 h11)
          (mul_mem (NN_le_H₁ hg) (inv_mem (wGL_mem_H₁ hH)))
      have : g = (g * (wGL F)⁻¹) * wGL F := by group
      rw [this]
      exact mul_mem (Subgroup.mem_sup_left hd) (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  · exact sup_le D_le_N ((Subgroup.zpowers_le).2 (w_mem_N hH))

theorem B_inf_N_le [Finite F] (hH : StatedSL 2 F ≤ H₁) (hF : 3 < Nat.card F) :
    BB H₁ ⊓ NN H₁ ≤ DD H₁ := by
  intro g hg
  obtain ⟨hgB, hgN⟩ := hg
  rcases N_cases hH hF hgN with ⟨h01, h10⟩ | ⟨h00, h11⟩
  · exact mem_DD_of ((mem_diagGL_iff g).2 ⟨h01, h10⟩) (NN_le_H₁ hgN)
  · exfalso
    have hc := B_c_zero hgB
    have := det_ne_zero g
    rw [h00, h11, hc] at this
    simp at this

theorem N_cases' [Finite F] (hH : StatedSL 2 F ≤ H₁) (hF : 3 < Nat.card F) {g : GL (Fin 2) F}
    (hg : g ∈ NN H₁) : g ∈ BB H₁ ∨ g * (wGL F)⁻¹ ∈ BB H₁ := by
  rcases N_cases hH hF hg with ⟨h01, h10⟩ | ⟨h00, h11⟩
  · exact Or.inl (D_le_B (mem_DD_of ((mem_diagGL_iff g).2 ⟨h01, h10⟩) (NN_le_H₁ hg)))
  · exact Or.inr (D_le_B (mem_DD_of (mul_wGL_inv_mem_diagGL h00 h11)
      (mul_mem (NN_le_H₁ hg) (inv_mem (wGL_mem_H₁ hH)))))

theorem bruhat (hH : StatedSL 2 F ≤ H₁) {g : GL (Fin 2) F} (hg : g ∈ H₁) :
    g ∈ BB H₁ ∨ ∃ b₁ ∈ BB H₁, ∃ b₂ ∈ BB H₁, g = b₁ * wGL F * b₂ := by
  by_cases hc : g.1 1 0 = 0
  · exact Or.inl (mem_B_of_c_zero hH hg hc)
  · right
    obtain ⟨s, s', m, hgm, hm00, hm11⟩ := bruhat_core hc
    have hmH : m ∈ H₁ := by
      have : m = (uT s)⁻¹ * g * (uT s')⁻¹ := by
        rw [hgm]
        group
      rw [this]
      exact mul_mem (mul_mem (inv_mem (uT_mem_H₁ hH s)) hg) (inv_mem (uT_mem_H₁ hH s'))
    have hδ : m * (wGL F)⁻¹ ∈ DD H₁ :=
      mem_DD_of (mul_wGL_inv_mem_diagGL hm00 hm11)
        (mul_mem hmH (inv_mem (wGL_mem_H₁ hH)))
    refine ⟨uT s * (m * (wGL F)⁻¹), mul_mem (U_le_B hH (uT_mem_range s)) (D_le_B hδ), uT s',
      U_le_B hH (uT_mem_range s'), ?_⟩
    rw [hgm]
    group

theorem ne_aux [Finite F] (hH : StatedSL 2 F ≤ H₁) (hF : 3 < Nat.card F) {n : GL (Fin 2) F}
    (hn : n ∈ NN H₁) (hnB : n ∉ BB H₁) : ∃ b ∈ BB H₁, n * b * n ∉ BB H₁ := by
  rcases N_cases hH hF hn with ⟨h01, h10⟩ | ⟨h00, h11⟩
  · exact absurd (D_le_B (mem_DD_of ((mem_diagGL_iff n).2 ⟨h01, h10⟩) (NN_le_H₁ hn))) hnB
  · exact ⟨uT 1, U_le_B hH (uT_mem_range 1),
      fun hB => antidiag_four_not_upper h00 h11 (B_c_zero hB)⟩

theorem four_mem (hH : StatedSL 2 F ≤ H₁) {u : GL (Fin 2) F} (hu : u ∈ (uHom F).range)
    (hu1 : u ≠ 1) :
    wGL F * u * (wGL F)⁻¹ ∈ (BB H₁ : Set (GL (Fin 2) F)) * {wGL F} *
      (((uHom F).range : Subgroup (GL (Fin 2) F)) : Set (GL (Fin 2) F)) := by
  obtain ⟨t, rfl⟩ := (mem_range_uHom_iff' u).1 hu
  have ht : t ≠ 0 := fun h => hu1 (by rw [h, uT_zero])
  rw [four_identity ht]
  have hd : dg (Units.mk0 t ht)⁻¹ (Units.mk0 t ht) ∈ DD H₁ :=
    mem_DD_of (dg_mem_diagGL _ _) (hH (dg_mem_statedSL (by simp [ht])))
  exact ⟨_, ⟨uT (-t⁻¹) * dg (Units.mk0 t ht)⁻¹ (Units.mk0 t ht),
    mul_mem (U_le_B hH (uT_mem_range _)) (D_le_B hd), wGL F, rfl, rfl⟩,
    uT (-t⁻¹), uT_mem_range _, rfl⟩

end Groups

section Assembly

variable {H₁ : Subgroup (GL (Fin 2) F)}

def wH (hH : StatedSL 2 F ≤ H₁) : ↥H₁ := ⟨wGL F, wGL_mem_H₁ hH⟩

def wN (hH : StatedSL 2 F ≤ H₁) : ↥((NN H₁).subgroupOf H₁) :=
  ⟨wH hH, Subgroup.mem_subgroupOf.2 (w_mem_N hH)⟩

theorem tits_and_split [Finite F] (hH : StatedSL 2 F ≤ H₁) (hF : 3 < Nat.card F) :
    ∃ (_ : (BNPair.cartan ((BB H₁).subgroupOf H₁) ((NN H₁).subgroupOf H₁)).Normal)
      (S : Finset (BNPair.WeylGroup ((BB H₁).subgroupOf H₁) ((NN H₁).subgroupOf H₁))),
      S.card = 1 ∧ BNPair.IsTitsSystem ((BB H₁).subgroupOf H₁) ((NN H₁).subgroupOf H₁) S ∧
        BNPair.IsSplit ((BB H₁).subgroupOf H₁) ((NN H₁).subgroupOf H₁)
          ((uHom F).range.subgroupOf H₁) := by
  have hnorm : (BNPair.cartan ((BB H₁).subgroupOf H₁) ((NN H₁).subgroupOf H₁)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn1 := Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hn)
    have hnB : ((n : ↥H₁) : GL (Fin 2) F) ∈ BB H₁ := Subgroup.mem_subgroupOf.1 hn1.1
    have hnN : ((n : ↥H₁) : GL (Fin 2) F) ∈ NN H₁ := Subgroup.mem_subgroupOf.1 hn1.2
    have hgN : ((g : ↥H₁) : GL (Fin 2) F) ∈ NN H₁ := Subgroup.mem_subgroupOf.1 g.2
    have hnD := B_inf_N_le hH hF ⟨hnB, hnN⟩
    have hconj := (Subgroup.mem_normalizer_iff.1 (Subgroup.mem_inf.1 hgN).1 _).1 hnD
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf]
    exact ⟨D_le_B hconj, D_le_N hconj⟩
  refine ⟨hnorm, {((wN hH : ↥((NN H₁).subgroupOf H₁)) :
    BNPair.WeylGroup ((BB H₁).subgroupOf H₁) ((NN H₁).subgroupOf H₁))}, Finset.card_singleton _,
    ?_, ?_⟩
  · refine isTitsSystem_of_rankOne _ _ (wN hH) ?_ ?_ ?_ ?_ ?_
    · intro h
      have : (wGL F).1 1 0 = 0 := B_c_zero (Subgroup.mem_subgroupOf.1 h)
      simp at this
    · have : (wGL F) ^ 2 ∈ BB H₁ := by
        rw [pow_two]
        exact D_le_B (mem_DD_of wGL_sq_mem_diagGL (mul_mem (wGL_mem_H₁ hH) (wGL_mem_H₁ hH)))
      exact Subgroup.mem_subgroupOf.2 this
    · intro n
      have hn : ((n : ↥H₁) : GL (Fin 2) F) ∈ NN H₁ := Subgroup.mem_subgroupOf.1 n.2
      rcases N_cases' hH hF hn with h | h
      · exact Or.inl (Subgroup.mem_subgroupOf.2 h)
      · exact Or.inr (Subgroup.mem_subgroupOf.2 h)
    · intro x
      rcases bruhat hH x.2 with h | ⟨b₁, hb₁, b₂, hb₂, hx⟩
      · exact Or.inl (Subgroup.mem_subgroupOf.2 h)
      · right
        refine ⟨⟨b₁, BB_le_H₁ hb₁⟩ * wH hH, ⟨⟨b₁, BB_le_H₁ hb₁⟩,
          Subgroup.mem_subgroupOf.2 hb₁, wH hH, rfl, rfl⟩, ⟨b₂, BB_le_H₁ hb₂⟩,
          Subgroup.mem_subgroupOf.2 hb₂, ?_⟩
        apply Subtype.ext
        exact hx.symm
    · intro n hn
      have hnN : ((n : ↥H₁) : GL (Fin 2) F) ∈ NN H₁ := Subgroup.mem_subgroupOf.1 n.2
      have hnB : ((n : ↥H₁) : GL (Fin 2) F) ∉ BB H₁ :=
        fun h => hn (Subgroup.mem_subgroupOf.2 h)
      obtain ⟨b, hb, hnb⟩ := ne_aux hH hF hnN hnB
      exact ⟨⟨b, BB_le_H₁ hb⟩, Subgroup.mem_subgroupOf.2 hb,
        fun h => hnb (Subgroup.mem_subgroupOf.1 h)⟩
  · have hcomm : ∀ a b : ↥((uHom F).range.subgroupOf H₁), a * b = b * a := by
      intro a b
      obtain ⟨s, hs⟩ := (mem_range_uHom_iff' _).1 (Subgroup.mem_subgroupOf.1 a.2)
      obtain ⟨t, ht⟩ := (mem_range_uHom_iff' _).1 (Subgroup.mem_subgroupOf.1 b.2)
      apply Subtype.ext
      apply Subtype.ext
      show ((a : ↥H₁) : GL (Fin 2) F) * ((b : ↥H₁) : GL (Fin 2) F) =
        ((b : ↥H₁) : GL (Fin 2) F) * ((a : ↥H₁) : GL (Fin 2) F)
      rw [hs, ht, uT_mul, uT_mul, add_comm]
    have : IsMulCommutative ↥((uHom F).range.subgroupOf H₁) := ⟨⟨fun a b => hcomm a b⟩⟩
    refine ⟨CommGroup.isNilpotent, ?_⟩
    ext x
    constructor
    · intro hx
      have hxB : (x : GL (Fin 2) F) ∈ BB H₁ := Subgroup.mem_subgroupOf.1 hx
      have hdd := upper_decomp_right (B_c_zero hxB)
      have hdH : (x : GL (Fin 2) F) *
          uT (-((x : GL (Fin 2) F).1 0 1 / (x : GL (Fin 2) F).1 0 0)) ∈ H₁ :=
        mul_mem x.2 (uT_mem_H₁ hH _)
      have hdD := mem_DD_of hdd hdH
      refine ⟨⟨_, hdH⟩, Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.2 (D_le_B hdD),
        Subgroup.mem_subgroupOf.2 (D_le_N hdD)⟩,
        ⟨uT ((x : GL (Fin 2) F).1 0 1 / (x : GL (Fin 2) F).1 0 0), uT_mem_H₁ hH _⟩,
        Subgroup.mem_subgroupOf.2 (uT_mem_range _), ?_⟩
      apply Subtype.ext
      show (x : GL (Fin 2) F) *
          uT (-((x : GL (Fin 2) F).1 0 1 / (x : GL (Fin 2) F).1 0 0)) *
        uT ((x : GL (Fin 2) F).1 0 1 / (x : GL (Fin 2) F).1 0 0) = x
      rw [mul_assoc, uT_mul, neg_add_cancel, uT_zero, mul_one]
    · rintro ⟨d, hd, u, hu, rfl⟩
      exact mul_mem (Subgroup.mem_inf.1 hd).1
        (Subgroup.mem_subgroupOf.2 (U_le_B hH (Subgroup.mem_subgroupOf.1 hu)))

end Assembly

end L2BN

open L2BN in
theorem ivk_1_6 :
    ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ H₁ : Subgroup (GL (Fin 2) F),
      StatedSL 2 F ≤ H₁ →
        ∀ U D₁ B N : Subgroup (GL (Fin 2) F), U = (uHom F).range → D₁ = diagGL F ⊓ H₁ →
          B = normalizer (U : Set (GL (Fin 2) F)) ⊓ H₁ → N = normalizer (D₁ : Set (GL (Fin 2) F)) ⊓ H₁ →
            B = U ⊔ D₁ ∧ N = D₁ ⊔ zpowers (wGL F) ∧
            (∃ (_ : (BNPair.cartan (B.subgroupOf H₁) (N.subgroupOf H₁)).Normal)
                (S : Finset (BNPair.WeylGroup (B.subgroupOf H₁) (N.subgroupOf H₁))),
              S.card = 1 ∧ BNPair.IsTitsSystem (B.subgroupOf H₁) (N.subgroupOf H₁) S ∧
                BNPair.IsSplit (B.subgroupOf H₁) (N.subgroupOf H₁) (U.subgroupOf H₁)) ∧
            ∀ u ∈ U, u ≠ 1 →
              wGL F * u * (wGL F)⁻¹ ∈ (B : Set (GL (Fin 2) F)) * {wGL F} * (U : Set (GL (Fin 2) F)) := by
  intro F _ _ hF H₁ hH U D₁ B N hU hD hB hN
  subst hU hD hB hN
  exact ⟨B_eq hH, N_eq hH hF.2, tits_and_split hH hF.2, fun u hu hu1 => four_mem hH hu hu1⟩

end CFSG.GH74.GLS.IVK
