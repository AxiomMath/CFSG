module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.TorusLocal
public import CFSG.LocalAnalysis.AGLEmbeddingD2.PairMaximal
public import CFSG.Sporadic.Schreier.M11
public import Certificates.Certificate19762
public import Certificates.Certificate19763
import CFSG.RankThree.PartOne.KP.SporadicDefs
import CFSG.Sporadic.Bridge.M11

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.AGLEmbedding.MaxD2
open CFSG.Blueprint CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.CatalogueSchreierAlternating Certificates.MaxD2Perm

@[expose] def m11Pairs : Set (NativeSporadic.M11 × NativeSporadic.M11) :=
  {p | orderOf p.1 = 2 ∧ orderOf p.2 = 4 ∧ orderOf (p.1 * p.2) = 11 ∧
    orderOf (p.1 * p.2 * p.1⁻¹ * p.2⁻¹) = 6 ∧
    orderOf (p.1 * p.2 * p.1 * p.2⁻¹ * p.1 * p.2 * p.2) = 5}

theorem m11_pair_count :
    Nat.card m11Pairs = 7920 := by
  obtain ⟨-, hT⟩ := Certificates.certificate19762
  rw [← hT]
  refine card_eq_length _
    (fun p : NativeSporadic.M11 × NativeSporadic.M11 =>
      ((p.1 : Equiv.Perm (Fin 11)), (p.2 : Equiv.Perm (Fin 11))))
    (fun p q h => Prod.ext (Subtype.ext (congrArg Prod.fst h))
      (Subtype.ext (congrArg Prod.snd h))) _
    (((m11Elements_nodup.filter _).product (m11Elements_nodup.filter _)).filter _) ?_
  rintro ⟨g, h⟩
  simp only [List.mem_filter, List.mem_product, mem_m11Elements, Bool.and_eq_true,
    Prod.mk.injEq]
  constructor
  · rintro ⟨⟨⟨hg, hg2⟩, hh, hh4⟩, ⟨hgh, hgc⟩, hgw⟩
    exact ⟨(⟨g, hg⟩, ⟨h, hh⟩), ⟨(m11_orderOf_eq_iff _ (by norm_num)).2 hg2,
      (m11_orderOf_eq_iff _ (by norm_num)).2 hh4,
      (m11_orderOf_eq_iff _ (by norm_num)).2 hgh,
      (m11_orderOf_eq_iff _ (by norm_num)).2 hgc,
      (m11_orderOf_eq_iff _ (by norm_num)).2 hgw⟩, rfl, rfl⟩
  · rintro ⟨⟨x, y⟩, ⟨hx, hy, hxy, hxc, hxw⟩, rfl, rfl⟩
    exact ⟨⟨⟨x.2, (m11_orderOf_eq_iff x (by norm_num)).1 hx⟩, y.2,
      (m11_orderOf_eq_iff y (by norm_num)).1 hy⟩,
      ⟨(m11_orderOf_eq_iff (x * y) (by norm_num)).1 hxy,
        (m11_orderOf_eq_iff (x * y * x⁻¹ * y⁻¹) (by norm_num)).1 hxc⟩,
      (m11_orderOf_eq_iff (x * y * x * y⁻¹ * x * y * y) (by norm_num)).1 hxw⟩

theorem mem_m11Pairs_map
    (φ : MulAut NativeSporadic.M11) : (φ m11a, φ m11b) ∈ m11Pairs := by
  obtain ⟨ha, hb, hab, hc, -, -, -⟩ := at_m11_image_pair_count
  have hw : orderOf (m11a * m11b * m11a * m11b⁻¹ * m11a * m11b * m11b) = 5 :=
    (m11_orderOf_eq_iff _ (by norm_num)).2 Certificates.certificate19762.1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show orderOf (φ m11a) = 2
    rw [MulEquiv.orderOf_eq]
    exact ha
  · show orderOf (φ m11b) = 4
    rw [MulEquiv.orderOf_eq]
    exact hb
  · show orderOf (φ m11a * φ m11b) = 11
    rw [← map_mul, MulEquiv.orderOf_eq]
    exact hab
  · show orderOf (φ m11a * φ m11b * (φ m11a)⁻¹ * (φ m11b)⁻¹) = 6
    rw [show φ m11a * φ m11b * (φ m11a)⁻¹ * (φ m11b)⁻¹ =
      φ (m11a * m11b * m11a⁻¹ * m11b⁻¹) by simp only [map_mul, map_inv], MulEquiv.orderOf_eq]
    exact hc
  · show orderOf (φ m11a * φ m11b * φ m11a * (φ m11b)⁻¹ * φ m11a * φ m11b * φ m11b) = 5
    rw [show φ m11a * φ m11b * φ m11a * (φ m11b)⁻¹ * φ m11a * φ m11b * φ m11b =
      φ (m11a * m11b * m11a * m11b⁻¹ * m11a * m11b * m11b) by
        simp only [map_mul, map_inv], MulEquiv.orderOf_eq]
    exact hw

theorem card_mulAut_m11_le :
    Nat.card (MulAut NativeSporadic.M11) ≤ 7920 := by
  have hinj : Function.Injective fun φ : MulAut NativeSporadic.M11 => (φ m11a, φ m11b) :=
    Subtype.val_injective.comp (imagePairEvaluation_injective m11a m11b m11_closure_eq_top)
  calc Nat.card (MulAut NativeSporadic.M11)
      ≤ Nat.card m11Pairs := Nat.card_le_card_of_injective
        (fun φ => ⟨(φ m11a, φ m11b), mem_m11Pairs_map φ⟩) fun φ ψ h => hinj (congrArg Subtype.val h)
    _ = 7920 := m11_pair_count

theorem card_outer_m11 :
    Nat.card (Outer NativeSporadic.M11) = 1 := by
  have haut := card_mulAut_m11_le
  have hquot := (inner NativeSporadic.M11).card_eq_card_quotient_mul_card_subgroup
  rw [m11_inner_card] at hquot
  have hpos : 0 < Nat.card (Outer NativeSporadic.M11) := Nat.card_pos
  change Nat.card (MulAut NativeSporadic.M11 ⧸ inner NativeSporadic.M11) = 1
  change 0 < Nat.card (MulAut NativeSporadic.M11 ⧸ inner NativeSporadic.M11) at hpos
  omega

theorem m11_tab_a : TabRep (#[0, 9, 2, 10, 6, 5, 4, 8, 7, 1, 3] : Tab) m11gA := by
  unfold TabRep
  decide

theorem m11_tab_b : TabRep (#[3, 4, 7, 2, 5, 8, 6, 0, 1, 9, 10] : Tab) m11gB := by
  unfold TabRep
  decide

theorem m11ThreeData_hS : ∀ j,
    TabRep (m11ThreeData.gT.getD j (idTab 11)) ([m11gA, m11gB].getD j 1) :=
  rep_getD_of_forall (L := [#[0, 9, 2, 10, 6, 5, 4, 8, 7, 1, 3],
    #[3, 4, 7, 2, 5, 8, 6, 0, 1, 9, 10]]) (P := [m11gA, m11gB]) rfl (by
    intro i hi
    have hi' : i < 2 := hi
    interval_cases i
    · exact m11_tab_a
    · exact m11_tab_b)

theorem orderOf_two_zmod_three : orderOf ((2 : ℕ) : ZMod 3) = 3 - 1 := by
  rw [orderOf_eq_iff (by norm_num)]
  decide

theorem m11_three_local_check : check m11ThreeData = true :=
  Certificates.certificate19763

theorem m11_three_localData :
    ∃ R : Subgroup (Equiv.Perm (Fin 11)), LocalData 3 4 2 12 NativeSporadic.M11 R := by
  have hG : Subgroup.closure {g | g ∈ [m11gA, m11gB]} = NativeSporadic.M11 := by
    rw [m11_eq]
    congr 1
    ext g
    simp
  have h := localData_of_check (S := [m11gA, m11gB]) (D := m11ThreeData) rfl
    (by show Nat.Prime 3; norm_num) m11ThreeData_hS
    (by
      have h1 : [m11gA, m11gB].length = 2 := rfl
      have h2 : m11ThreeData.gT.size = 2 := rfl
      rw [h1, h2])
    (by rw [hG]; exact card_M11)
    ⟨4, 0, by show (144 : ℕ) = 3 ^ 2 * (2 ^ 4 * 3 ^ 0); norm_num⟩ m11_three_local_check
  rwa [hG] at h

theorem kFactM11Three :
    KFactM11Three := by
  intro L _ _ ⟨e⟩
  obtain ⟨eC⟩ := CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv
  let e' : L ≃* ↥NativeSporadic.M11 := e.trans eC.symm
  refine ⟨?_, fun S => ?_⟩
  · rw [CFSG.RankThree.PartOne.card_outer_eq_of_mulEquiv e', card_outer_m11]
  · obtain ⟨R₀, hR₀⟩ := m11_three_localData
    have hT := torusLocal_of_localData hR₀ (by norm_num) orderOf_two_zmod_three (by norm_num)
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h := torusLocal_sylow e' hT (by
      rw [hT.1, card_M11, factorization_eq_of_pow_dvd Nat.prime_three (k := 2) (by norm_num)
        (by norm_num) (by norm_num)]) S
    exact ⟨h.1, h.2.2.1, h.2.1⟩

end CFSG.AGLEmbeddingD2
