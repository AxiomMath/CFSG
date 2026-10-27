module

public import CFSG.GH74.GLS.SP.Local.SPLOrdBr
public import CFSG.GH74.GLS.SP.Local.SPLOrdL2
public import CFSG.GH74.GLS.SP.Local.SPLOrdG6

public section

open Subgroup DihedralGroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP CFSG.GorensteinWalter
open scoped Pointwise commutatorElement

namespace CFSG.GH74.GLS.SP.Local

section G9

theorem pgl2_commutator_index_two {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (h5 : 5 ≤ Nat.card F) : (commutator (PGL2 F)).index = 2 := by
  have hL : IVK.L2Field F := ⟨hodd, by omega⟩
  have hpp : IsOddPrimePower (Nat.card F) := IVK.isOddPrimePower_of_L2Field hL
  have hq3 : 3 < Nat.card F := by omega
  have hcomm : commutator (PGL2 F) =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range :=
    pgl2_commutator_eq_psl2_range_of_card_gt_three F hpp hq3
  rw [hcomm]
  exact pgl2_psl2Range_index_eq_two F hpp

variable {G : Type} [Group G] [Finite G] (D : SPLNot3 G)

theorem sigma_count (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) {s : ℕ}
    (hsq : s = if D.q % 4 = 1 then D.q + 1 else D.q - 1) :
    Nat.card {i : ↥D.I // i * sigmaAut D hc i = 1} * s = Nat.card ↥D.I := by
  classical
  obtain ⟨hNn, F₀, hF1, hF2, hFq, ⟨eP⟩⟩ := hc.quot
  have hNnormal := hNn
  set Y : Subgroup G := D.I ⊔ zpowers D.x with hYdef
  have hYCt : Y ≤ D.Ct := M_le_Ct D hc
  have hxY : D.x ∈ Y := Subgroup.mem_sup_right (mem_zpowers _)
  have hIY : D.I ≤ Y := le_sup_left
  let x' : ↥Y := ⟨D.x, hxY⟩
  have hInormal : (D.I.subgroupOf Y).Normal := ⟨fun n hn g => by
    show ((g * n * g⁻¹ : ↥Y) : G) ∈ D.I
    exact I_normalized D hc g (hYCt g.2) n hn⟩
  have hY : ∀ y : ↥Y, ∃ i ∈ D.I.subgroupOf Y, ∃ k : ℤ, y = i * x' ^ k := by
    intro y
    obtain ⟨i, hi, w, hw, hiw⟩ := mem_sup_of_le_normalizer (x_le_normalizer_I D hc) y.2
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
    refine ⟨⟨i, hIY hi⟩, hi, k, Subtype.ext ?_⟩
    simpa [x'] using hiw
  have hN' : (zpowers (D.x ^ 2)).subgroupOf Y = zpowers (x' ^ 2) := by
    ext y
    rw [Subgroup.mem_subgroupOf, mem_zpowers_iff, mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext (by simpa [x'] using hk)⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by simpa [x'] using congrArg Subtype.val hk⟩
  have hIN : D.I.subgroupOf Y ⊓ (zpowers (D.x ^ 2)).subgroupOf Y = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hy1, hy2⟩
    have h : (y : G) ∈ D.I ⊓ zpowers (D.x ^ 2) := ⟨hy1, hy2⟩
    rw [Z_inf_I D hc] at h
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp h))
  have hqF : Nat.card F₀ = D.q := hFq
  have hcardP : Nat.card (↥Y ⧸ (zpowers (D.x ^ 2)).subgroupOf Y) = D.q * (D.q ^ 2 - 1) := by
    rw [Nat.card_congr eP.toEquiv, CFSG.GorensteinWalter.pgl2_card_formula F₀, hqF]
  have hcard : 2 * Nat.card ↥(D.I.subgroupOf Y) =
      Nat.card (↥Y ⧸ (zpowers (D.x ^ 2)).subgroupOf Y) := by
    rw [hcardP, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hIY).toEquiv,
      ← card_K₁ (D := D.toSPLNot0) hs]
    exact card_K₁_eq D hs hc
  have hodd : Odd (Nat.card F₀) := by rw [hqF]; exact hs.odd_q
  have h5 : 5 ≤ Nat.card F₀ := by rw [hqF]; exact hs.q_ge
  have hq5 := hs.q_ge
  obtain ⟨ε, hε1, hε, hsε⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ (D.q : ℤ) ≡ ε [ZMOD 4] ∧
      (s : ℤ) = D.q + ε := by
    by_cases h : D.q % 4 = 1
    · refine ⟨1, Or.inl rfl, ?_, ?_⟩
      · unfold Int.ModEq; omega
      · rw [hsq]; simp only [h, ite_true]; push_cast; ring
    · have hq3 : D.q % 4 = 3 := by
        obtain ⟨m, hm⟩ := hs.odd_q
        omega
      refine ⟨-1, Or.inr rfl, ?_, ?_⟩
      · unfold Int.ModEq; omega
      · rw [hsq]; simp only [h, ite_false]; push_cast [show 1 ≤ D.q by omega]; ring
  obtain ⟨-, hcnt, huniq⟩ := pgl2_outer_involution_count (F := F₀) hodd h5 (ε := ε) hε1
    (by rw [hqF]; exact hε) (s := s) (by rw [hqF]; exact hsε)
  have hidx := pgl2_commutator_index_two (F := F₀) hodd h5
  let eQ := eP
  let J : Subgroup (↥Y ⧸ (zpowers (D.x ^ 2)).subgroupOf Y) :=
    (commutator (PGL2 F₀)).comap eQ.toMonoidHom
  have hJ2 : J.index = 2 := by
    have h := Subgroup.index_comap_of_surjective (f := eQ.toMonoidHom)
      (H := commutator (PGL2 F₀)) eQ.surjective
    exact h.trans hidx
  have hJ : ∀ H : Subgroup (↥Y ⧸ (zpowers (D.x ^ 2)).subgroupOf Y), H.index = 2 → H = J := by
    intro H hH
    have hmap : (H.map eQ.toMonoidHom).index = 2 :=
      (Subgroup.index_map_equiv (H := H) eQ).trans hH
    have := huniq _ hmap
    have h2 : H = (H.map eQ.toMonoidHom).comap eQ.toMonoidHom :=
      (Subgroup.comap_map_eq_self_of_injective eQ.injective H).symm
    rw [h2, this]
  have hcount : Nat.card {y : ↥Y ⧸ (zpowers (D.x ^ 2)).subgroupOf Y // orderOf y = 2 ∧ y ∉ J} *
      (2 * s) = Nat.card (↥Y ⧸ (zpowers (D.x ^ 2)).subgroupOf Y) := by
    have e1 : Nat.card {y : ↥Y ⧸ (zpowers (D.x ^ 2)).subgroupOf Y // orderOf y = 2 ∧ y ∉ J} =
        Nat.card {y : PGL2 F₀ // orderOf y = 2 ∧ y ∉ commutator (PGL2 F₀)} := by
      refine Nat.card_congr (Equiv.subtypeEquiv eQ.toEquiv fun y => ?_)
      show orderOf y = 2 ∧ y ∉ J ↔ orderOf (eQ y) = 2 ∧ eQ y ∉ commutator (PGL2 F₀)
      rw [MulEquiv.orderOf_eq]
      rfl
    rw [e1, hcnt, Nat.card_congr eQ.toEquiv]
  have habs := sigma_count_abstract (D.I.subgroupOf Y) ((zpowers (D.x ^ 2)).subgroupOf Y) x' hY hN' hIN
    J hJ2 hJ s hcount hcard
  have hcI : Nat.card ↥(D.I.subgroupOf Y) = Nat.card ↥D.I :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hIY).toEquiv
  rw [hcI] at habs
  rw [← habs]
  congr 1
  refine Nat.card_congr ?_
  exact
    { toFun := fun j => ⟨⟨(j.1 : G), hIY j.1.2⟩, j.1.2, by
          apply Subtype.ext
          have h' : ((j.1 : ↥D.I) : G) * (D.x * (j.1 : G) * D.x⁻¹) = 1 := by
            have := congrArg Subtype.val j.2
            simpa [sigmaAut_apply] using this
          exact h'⟩
      invFun := fun i => ⟨⟨(i.1 : G), i.2.1⟩, by
          apply Subtype.ext
          have h' : (i.1 : G) * (D.x * (i.1 : G) * D.x⁻¹) = 1 := congrArg Subtype.val i.2.2
          show (i.1 : G) * ((sigmaAut D hc ⟨(i.1 : G), i.2.1⟩ : ↥D.I) : G) = 1
          rw [sigmaAut_apply]
          exact h'⟩
      left_inv := fun j => rfl
      right_inv := fun i => rfl }

end G9

end CFSG.GH74.GLS.SP.Local
