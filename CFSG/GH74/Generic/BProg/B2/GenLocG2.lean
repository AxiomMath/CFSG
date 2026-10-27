module

public import CFSG.GH74.Generic.BProg.B2.GenLocG2Outer
public import CFSG.GH74.Generic.BProg.B2.GenLocG2Inner
import CFSG.GH74.Generic.BProg.B2.PumpupOutOrdersAux
import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Exc

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG Subgroup CFSG.GH74.Generic.BProg CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab (mem_zpowers_of_sq)

open scoped MatrixGroups

@[expose] def PuG2Odd (H : Type) [Group H] : Prop :=
  ∃ f : ℕ, 3 ≤ f ∧ Odd f ∧ LieModel H .G2 0 3 f

section Basic

variable {J : Type} [Group J] [Finite J] {f : ℕ}

omit [Finite J] in
theorem g2_two_dvd_card (hJ : LieModel J .G2 0 3 f) : 2 ∣ Nat.card J := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨F, _, hFin, hF, ⟨e⟩⟩ := CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab.exists_equiv_of_lieModel hJ
  rw [Nat.card_congr e.toEquiv]
  show 2 ∣ Nat.card (CFSG.Blueprint.Chevalley.adjointGroup CFSG.Blueprint.Chevalley.Tag.G2 F)
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hF]
  exact Nat.dvd_trans (by norm_num : 2 ∣ 16)
    (CFSG.GH74.Generic.BProg.B2.PumpupOutOrders.sixteen_dvd_ordG2 (Odd.pow (by decide)))

end Basic

section Basic2

variable {J : Type} [Group J] [Finite J] {f : ℕ}

theorem g2_exists_involution (hJ : LieModel J .G2 0 3 f) : ∃ v : J, orderOf v = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact exists_prime_orderOf_dvd_card' (G := J) 2 (g2_two_dvd_card hJ)

omit [Finite J] in
theorem g2_isSimple (hJ : LieModel J .G2 0 3 f) : IsSimpleGroup J :=
  (CFSG.LieType.Simplicity.fam_g2_simplicity J 3 f
    (CFSG.GH74.GLS.IVK.chevalleyExceptionalModel_of_lieModel_G2 hJ)).2

theorem g2_center_trivial (hf : 3 ≤ f) (hJ : LieModel J .G2 0 3 f) :
    ∀ z : J, (∀ g : J, g * z = z * g) → z = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨v, hv⟩ := g2_exists_involution hJ
  obtain ⟨F, _, _, S, hF, hSz⟩ :=
    CFSG.GH74.GLS.IVK.GHInv.exists_shape_G2 Nat.prime_three (by norm_num) hJ v hv
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 ≤ 3 ^ 3 := by norm_num
      _ ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  exact GenLocG2Outer.g2_center_trivial_of_shape (g2_isSimple hJ) S
    (GenLocG2Outer.isQuasisimple_I₁ S h4)

end Basic2

section Decomp

variable {J : Type} [Group J] [Finite J] {f : ℕ}

theorem GenLocG2.outer_decomp (hf : 3 ≤ f) (hJ : LieModel J .G2 0 3 f) {D : Subgroup (MulAut J)}
    (hD : CFSG.IsElementaryAbelian 2 ↥D) {σ : MulAut J} (hσD : σ ∈ D)
    (hσout : σ ∉ (MulAut.conj : J →* MulAut J).range) :
    ∃ B : Subgroup J, CFSG.IsElementaryAbelian 2 ↥B ∧ (∀ b ∈ B, σ b = b) ∧
      B.map (MulAut.conj : J →* MulAut J) ⊔ Subgroup.zpowers σ = D ∧
      Nat.card ↥D = 2 * Nat.card ↥B := by
  obtain ⟨hDab, hDsq⟩ := WeakSigGen.forall_of_isElementaryAbelian hD
  have hZ := g2_center_trivial hf hJ
  have hinj := GenLocBasic.conj_injective_of_center_trivial hZ
  have hσ2 : σ * σ = 1 := hDsq σ hσD
  have hmul : ∀ d ∈ D, d ∉ (MulAut.conj : J →* MulAut J).range → d * σ ∈
      (MulAut.conj : J →* MulAut J).range := fun d hd hdi =>
    g2_mul_mem_inn (by omega) hJ (hDsq d hd) hσ2 (hDab d hd σ hσD) hdi hσout
  obtain ⟨D', hD'⟩ : ∃ D' : Subgroup (MulAut J), D' = D ⊓ (MulAut.conj : J →* MulAut J).range :=
    ⟨_, rfl⟩
  have hD'D : D' ≤ D := hD' ▸ inf_le_left
  have hD'inn : D' ≤ (MulAut.conj : J →* MulAut J).range := hD' ▸ inf_le_right
  obtain ⟨hmap, -⟩ := map_comap_conj_of_le_inn hZ hD'inn
  refine ⟨D'.comap (MulAut.conj : J →* MulAut J), ?_, ?_, ?_, ?_⟩
  · refine WeakSigGen.isElementaryAbelian_of_forall (fun b hb c hc => ?_) (fun b hb => ?_)
    · apply hinj
      rw [map_mul, map_mul]
      exact hDab _ (hD'D hb) _ (hD'D hc)
    · apply hinj
      rw [map_mul, map_one]
      exact hDsq _ (hD'D hb)
  · intro b hb
    have hbD : (MulAut.conj b : MulAut J) ∈ D := hD'D hb
    have hc : σ * MulAut.conj b = MulAut.conj b * σ := hDab σ hσD _ hbD
    rw [GenLocG2Outer.aut_mul_conj] at hc
    exact hinj (mul_right_cancel hc)
  · rw [hmap]
    apply le_antisymm
    · exact sup_le hD'D (zpowers_le.2 hσD)
    · intro d hd
      by_cases hdi : d ∈ (MulAut.conj : J →* MulAut J).range
      · exact mem_sup_left (hD' ▸ ⟨hd, hdi⟩)
      · have hd2 : σ * d ∈ D' := by
          rw [hD']
          refine ⟨mul_mem hσD hd, ?_⟩
          have := hmul d hd hdi
          rwa [hDab d hd σ hσD] at this
        have : d = σ * (σ * d) := by rw [← mul_assoc, hσ2, one_mul]
        rw [this]
        exact mul_mem (mem_sup_right (mem_zpowers σ)) (mem_sup_left hd2)
  · have hcardB : Nat.card ↥D' = Nat.card ↥(D'.comap (MulAut.conj : J →* MulAut J)) := by
      have := Subgroup.card_map_of_injective (K := D'.comap (MulAut.conj : J →* MulAut J)) hinj
      rw [hmap] at this
      exact this
    have hidx : (D'.subgroupOf D).index = 2 := by
      rw [Subgroup.index_eq_two_iff]
      refine ⟨⟨σ, hσD⟩, ?_⟩
      rintro ⟨b, hbD⟩
      by_cases hbi : b ∈ (MulAut.conj : J →* MulAut J).range
      · right
        refine ⟨show b ∈ D' from hD' ▸ ⟨hbD, hbi⟩, fun h => hσout ?_⟩
        have hbs : b * σ ∈ (MulAut.conj : J →* MulAut J).range := hD'inn h
        have : σ = b⁻¹ * (b * σ) := by group
        rw [this]
        exact mul_mem (inv_mem hbi) hbs
      · left
        refine ⟨show b * σ ∈ D' from hD' ▸ ⟨mul_mem hbD hσD, hmul b hbD hbi⟩, fun h => hbi (hD'inn h)⟩
    have h1 := Subgroup.card_mul_index (D'.subgroupOf D)
    rw [hidx] at h1
    have h2 : Nat.card ↥(D'.subgroupOf D) = Nat.card ↥D' :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD'D).toEquiv
    rw [← h1, h2, hcardB]
    ring

end Decomp

section Z1

variable {J : Type} [Group J] [Finite J]

theorem GenLocG2.fixedIn_zpowers_le_gammaSub {D : Subgroup (MulAut J)} (hD2 : pRank 2 ↥D ≤ 2) {x : MulAut J}
    (hxD : x ∈ D) (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    fixedIn J (zpowers x) ≤ gammaSub J D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hx2) hx1
  have hEA : CFSG.IsElementaryAbelian 2 ↥(zpowers x) := by
    refine WeakSigGen.isElementaryAbelian_of_forall (fun u hu v hv => ?_) (fun u hu => ?_)
    · rcases mem_zpowers_of_sq hx2 hu with rfl | rfl <;> rcases mem_zpowers_of_sq hx2 hv with rfl | rfl <;> simp
    · rcases mem_zpowers_of_sq hx2 hu with rfl | rfl
      · simp
      · exact hx2
  have hcard : Nat.card ↥(zpowers x) = 2 ^ 1 := by rw [Nat.card_zpowers, hxo]; norm_num
  have hrk : pRank 2 ↥(zpowers x) = 1 := CFSG.pRank_eq_of_card_eq_pow one_lt_two hcard
  exact le_iSup₂_of_le (zpowers x) (zpowers_le.2 hxD)
    (le_iSup_of_le (by rw [hrk]; omega) le_rfl)

end Z1

section G7

variable {J : Type} [Group J] [Finite J] {f : ℕ}

theorem genSub_g2 (hf : 3 ≤ f) (hodd : Odd f) (hJ : LieModel J .G2 0 3 f) : GenSub J := by
  intro D hD hrk
  obtain ⟨hDab, hDsq⟩ := WeakSigGen.forall_of_isElementaryAbelian hD
  have hZ := g2_center_trivial hf hJ
  have hinj := GenLocBasic.conj_injective_of_center_trivial hZ
  have hDcard : Nat.card ↥D = 2 ^ pRank 2 ↥D := WeakSigGen.card_eq_two_pow_pRank hD
  by_cases hDinn : D ≤ (MulAut.conj : J →* MulAut J).range
  ·
    obtain ⟨hmap, hrank⟩ := map_comap_conj_of_le_inn hZ hDinn
    set B := D.comap (MulAut.conj : J →* MulAut J) with hBdef
    have hB : CFSG.IsElementaryAbelian 2 ↥B := by
      refine WeakSigGen.isElementaryAbelian_of_forall (fun b hb c hc => ?_) (fun b hb => ?_)
      · apply hinj
        rw [map_mul, map_mul]
        exact hDab _ hb _ hc
      · apply hinj
        rw [map_mul, map_one]
        exact hDsq _ hb
    obtain ⟨hBab, hBsq⟩ := WeakSigGen.forall_of_isElementaryAbelian hB
    have hord : ∀ b ∈ B, b ≠ 1 → orderOf b = 2 := fun b hb hb1 => by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime (by rw [sq]; exact hBsq b hb) hb1
    have hgen : ∀ t ∈ B, ∀ u ∈ B, t ≠ 1 → u ≠ 1 → t ≠ u →
        centralizer ({t} : Set J) ⊔ centralizer ({u} : Set J) = ⊤ := fun t ht u hu ht1 hu1 htu =>
      g2_sup_centralizer_eq_top (by omega) hJ (by rw [← sq]; exact (hord t ht ht1) ▸ pow_orderOf_eq_one t)
        (by rw [← sq]; exact (hord u hu hu1) ▸ pow_orderOf_eq_one u) ht1 hu1 htu (hBab t ht u hu)
    rw [← hmap]
    rcases hrk with h2 | h3
    · exact gammaSub_inner_two hB (by rw [hrank]; exact h2) hgen
    · refine gammaSub_inner_three hB (by rw [hrank]; exact h3) (fun t ht ht1 => ?_) hgen
      refine g2_centralizer_le_iSup_four hf hJ hB ?_ ht ht1
      rw [WeakSigGen.card_eq_two_pow_pRank hB, hrank, h3]
      norm_num
  ·
    obtain ⟨σ, hσD, hσout⟩ : ∃ σ ∈ D, σ ∉ (MulAut.conj : J →* MulAut J).range := by
      by_contra hcon
      push Not at hcon
      exact hDinn hcon
    have hσ2 : σ * σ = 1 := hDsq σ hσD
    have hσ1 : σ ≠ 1 := fun h => hσout ⟨1, by rw [h, map_one]⟩
    obtain ⟨B, hB, hBσ, hDB, hcard⟩ := GenLocG2.outer_decomp hf hJ hD hσD hσout
    obtain ⟨hBab, hBsq⟩ := WeakSigGen.forall_of_isElementaryAbelian hB
    have hord : ∀ b ∈ B, b ≠ 1 → orderOf b = 2 := fun b hb hb1 => by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime (by rw [sq]; exact hBsq b hb) hb1
    have hconj_mem : ∀ b ∈ B, (MulAut.conj b : MulAut J) ∈ D := fun b hb =>
      hDB ▸ mem_sup_left (mem_map_of_mem _ hb)
    rcases hrk with h2 | h3
    ·
      have hD4 : Nat.card ↥D = 4 := by rw [hDcard, h2]; norm_num
      have hB2 : Nat.card ↥B = 2 := by omega
      obtain ⟨d, hd, hd1⟩ : ∃ d ∈ B, d ≠ 1 := by
        have : Nontrivial ↥B := Finite.one_lt_card_iff_nontrivial.1 (by omega)
        obtain ⟨x, hx⟩ := exists_ne (1 : ↥B)
        exact ⟨x, x.2, fun h => hx (Subtype.ext h)⟩
      have hdo := hord d hd hd1
      have hconj2 : (MulAut.conj d : MulAut J) * MulAut.conj d = 1 := by
        rw [← map_mul, hBsq d hd, map_one]
      have hconj1 : (MulAut.conj d : MulAut J) ≠ 1 := fun h => hd1 (hinj (h.trans (map_one _).symm))
      have hP1 := GenLocG2.fixedIn_zpowers_le_gammaSub (D := D) h2.le (hconj_mem d hd) hconj2 hconj1
      have hP2 := GenLocG2.fixedIn_zpowers_le_gammaSub (D := D) h2.le hσD hσ2 hσ1
      have hG4 := g2_sup_centralizer_fixed_eq_top hf hodd hJ hσ2 hσout hdo (hBσ d hd)
      have hcle : centralizer ({d} : Set J) ≤ fixedIn J (zpowers (MulAut.conj d : MulAut J)) := by
        intro x hx
        refine (GenLocG2Basic.mem_fixedIn_zpowers _ x).2 ?_
        rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
        exact (Subgroup.mem_centralizer_singleton_iff.1 hx).symm
      rw [eq_top_iff, ← hG4]
      exact sup_le (hcle.trans hP1) hP2
    ·
      have hD8 : Nat.card ↥D = 8 := by rw [hDcard, h3]; norm_num
      have hB4 : Nat.card ↥B = 4 := by omega
      obtain ⟨t, ht, u, hu, ht1, hu1, htu⟩ := GenLocBasic.exists_two_ne_one (B := B) (by omega)
      have G6t := g2_centralizer_le_gammaSub_outer hf hodd hJ hσ2 hσout hB hB4 hBσ ht ht1
      have G6u := g2_centralizer_le_gammaSub_outer hf hodd hJ hσ2 hσout hB hB4 hBσ hu hu1
      rw [hDB] at G6t G6u
      have hQ := g2_outer_fixed_qShape4 hf hodd hJ hσ2 hσout
      have hmemt : t ∈ fixedIn J (zpowers σ) := (GenLocG2Basic.mem_fixedIn_zpowers σ t).2 (hBσ t ht)
      have hmemu : u ∈ fixedIn J (zpowers σ) := (GenLocG2Basic.mem_fixedIn_zpowers σ u).2 (hBσ u hu)
      have hto : orderOf (⟨t, hmemt⟩ : ↥(fixedIn J (zpowers σ))) = 2 := by
        rw [Subgroup.orderOf_mk]; exact hord t ht ht1
      have huo : orderOf (⟨u, hmemu⟩ : ↥(fixedIn J (zpowers σ))) = 2 := by
        rw [Subgroup.orderOf_mk]; exact hord u hu hu1
      have hne : (⟨t, hmemt⟩ : ↥(fixedIn J (zpowers σ))) ≠ ⟨u, hmemu⟩ := fun h =>
        htu (congrArg Subtype.val h)
      have hgen := ree_sup_centralizer_eq_top hQ hto huo hne
      have hJ₀ : fixedIn J (zpowers σ) ≤ gammaSub J D := by
        intro x hx
        have hx' : (⟨x, hx⟩ : ↥(fixedIn J (zpowers σ))) ∈
            centralizer ({⟨t, hmemt⟩} : Set ↥(fixedIn J (zpowers σ))) ⊔
              centralizer ({⟨u, hmemu⟩} : Set ↥(fixedIn J (zpowers σ))) := by
          rw [hgen]; trivial
        have hmapx := Subgroup.mem_map_of_mem (fixedIn J (zpowers σ)).subtype hx'
        rw [Subgroup.map_sup] at hmapx
        refine (sup_le ?_ ?_ : _ ≤ gammaSub J D) hmapx
        · rintro _ ⟨y, hy, rfl⟩
          have hy' := Subgroup.mem_centralizer_singleton_iff.1
            (show y ∈ centralizer ({⟨t, hmemt⟩} : Set ↥(fixedIn J (zpowers σ))) from hy)
          exact G6t (Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val hy'))
        · rintro _ ⟨y, hy, rfl⟩
          have hy' := Subgroup.mem_centralizer_singleton_iff.1
            (show y ∈ centralizer ({⟨u, hmemu⟩} : Set ↥(fixedIn J (zpowers σ))) from hy)
          exact G6u (Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val hy'))
      have hG4 := g2_sup_centralizer_fixed_eq_top hf hodd hJ hσ2 hσout (hord t ht ht1) (hBσ t ht)
      rw [eq_top_iff, ← hG4]
      exact sup_le G6t hJ₀

end G7

section Family

variable {J : Type} [Group J] [Finite J] {f : ℕ}

theorem genLoc_g2 (h : PuG2Odd J) : GenLoc J := by
  obtain ⟨f, hf, hodd, hJ⟩ := h
  exact (genProp_of_genSub (genSub_g2 hf hodd hJ)).genLoc

theorem genLoc4_g2 (h : PuG2Odd J) : GenLoc4 J := (genLoc_g2 h).genLoc4

end Family

end CFSG.GH74.Generic.BProg.B2
