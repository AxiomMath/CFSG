module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnSp8b
import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnSp8c
public import CFSG.RankThree.SteinbergR3ECASymplecticPrimeSubfield

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265A

open CFSG.Open
open CFSG.RankThree.Classical (spEnd)
open CFSG.LocalAnalysis.GLTheoremA.CatB.U4Sp8 (Sp8Class exists_class_spSupported dimension_count
  sp8_blocks exists_mul_of_mem_sup isSimpleGroup_sp_three card_sp_three
  not_comm_of_simple_of_card card_special_unitary_four)

private theorem layer_ne_bot_of_normal_factor {G : Type} [Group G] [Finite G]
    {Y P Q : Subgroup G} (hY : Y = P ⊔ Q) (hc : ∀ a ∈ P, ∀ b ∈ Q, a * b = b * a)
    {M : Subgroup ↥P} (hM : M.Normal) {T : Type} [Group T] [IsSimpleGroup T] (e : ↥M ≃* T)
    (hT : ¬ (Nat.card T).Prime) (h3 : 3 ∣ Nat.card T) : GLAPLayer 3 Y ≠ ⊥ := by
  subst hY
  let eA : ↥(M.map P.subtype) ≃* T :=
    (Subgroup.equivMapOfInjective M P.subtype P.subtype_injective).symm.trans e
  haveI : IsSimpleGroup ↥(M.map P.subtype) := eA.isSimpleGroup
  have hA : Nat.card ↥(M.map P.subtype) = Nat.card T := Nat.card_congr eA.toEquiv
  have hnc : ∃ a b : ↥(M.map P.subtype), a * b ≠ b * a := by
    by_contra hcon
    exact not_comm_of_simple_of_card (T := ↥(M.map P.subtype)) (by rwa [hA])
      fun a b => by_contra fun hab => hcon ⟨a, b, hab⟩
  have hn : ((M.map P.subtype).subgroupOf (P ⊔ Q)).Normal := by
    refine ⟨fun k hk x => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    obtain ⟨m, hm, hmk⟩ := Subgroup.mem_map.1 hk
    obtain ⟨a, ha, b, hb, hx⟩ := exists_mul_of_mem_sup hc x.2
    refine Subgroup.mem_map.2 ⟨⟨a, ha⟩ * m * ⟨a, ha⟩⁻¹, hM.conj_mem m hm ⟨a, ha⟩, ?_⟩
    have hbm : (m : G) * b = b * m := hc m m.2 b hb
    simp only [Subgroup.coe_subtype] at hmk
    simp only [map_mul, map_inv, Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, hx,
      ← hmk]
    calc a * ↑m * a⁻¹ = a * (↑m * b) * b⁻¹ * a⁻¹ := by group
      _ = a * (b * ↑m) * b⁻¹ * a⁻¹ := by rw [hbm]
      _ = a * b * ↑m * (a * b)⁻¹ := by group
  intro hbot
  have hle := CFSG.HardMathSupport.Solomon.Coordinator.le_glaPLayer_of_normal_simple
    Nat.prime_three ((Subgroup.map_subtype_le M).trans le_sup_left) hn hnc (by rw [hA]; exact h3)
  rw [hbot, le_bot_iff] at hle
  have h1 := Subgroup.card_eq_one.2 hle
  rw [hA] at h1
  rw [h1] at h3
  norm_num at h3

private theorem fixedRank_eq_one_of_layer_eq_bot {s : StatedSp 4 (ZMod 2)} {s₀ m : ℕ}
    {A₀ A₁ : Subgroup (StatedSp 4 (ZMod 2))} (hc : Sp8Class s s₀ m A₀ A₁)
    (hL : GLAPLayer 3 (Subgroup.centralizer ({s} : Set (StatedSp 4 (ZMod 2)))) = ⊥) :
    s₀ = 1 := by
  have hsum := hc.sum_eq
  have hm : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 := by have := hc.one_le; omega
  rcases hm with rfl | rfl | rfl | rfl
  ·
    obtain rfl : s₀ = 3 := by omega
    obtain ⟨-, ⟨e₀⟩⟩ := hc.fixed.resolve_left (by omega)
    haveI := isSimpleGroup_sp_three
    exact absurd hL (layer_ne_bot_of_normal_factor hc.centralizer_eq hc.commute (M := ⊤)
      inferInstance (Subgroup.topEquiv.trans e₀) (by rw [card_sp_three]; norm_num)
      (by rw [card_sp_three]; norm_num))
  ·
    obtain rfl : s₀ = 2 := by omega
    obtain ⟨-, ⟨e₀⟩⟩ := hc.fixed.resolve_left (by omega)
    obtain ⟨eS⟩ := CFSG.RankThree.CASymplecticSubfield.nonempty_statedSp_two_mulEquiv_perm
      (k := ZMod 2) (ZMod.card 2)
    let φ := (e₀.trans eS).symm
    haveI : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    have h360 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    exact absurd hL (layer_ne_bot_of_normal_factor hc.centralizer_eq hc.commute
      ((inferInstance : (alternatingGroup (Fin 6)).Normal).map φ.toMonoidHom φ.surjective)
      (Subgroup.equivMapOfInjective _ φ.toMonoidHom φ.injective).symm
      (by rw [h360]; norm_num) (by rw [h360]; norm_num))
  · omega
  ·
    obtain ⟨E, _, hE, W, _, _, _, Hf, hsymm, hsep, hdim, ⟨e₁⟩⟩ := hc.unitary
    obtain ⟨-, -, -, -, hker, -, -⟩ :=
      CFSG.LinearGroups.unitary_full_group_order hE hsymm hsep hdim (by norm_num)
    haveI := CFSG.LargeExtraspecial.S14.PSLPSU10.isSimpleGroup_sesqSpecialUnitaryGroup hE hsymm
      hsep hdim (by norm_num) (by norm_num)
    have hcard := card_special_unitary_four hE hsymm hsep hdim
    let φ := e₁.symm
    exact absurd hL (layer_ne_bot_of_normal_factor (hc.centralizer_eq.trans (sup_comm _ _))
      (fun a ha b hb => (hc.commute b hb a ha).symm)
      ((CFSG.LinearGroups.unitaryDet Hf).normal_ker.map φ.toMonoidHom φ.surjective)
      ((Subgroup.equivMapOfInjective _ φ.toMonoidHom φ.injective).symm.trans
        ((MulEquiv.subgroupCongr hker).trans (Subgroup.subgroupOfEquivOfLe
          (CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup_le Hf))))
      (by rw [hcard]; norm_num) (by rw [hcard]; norm_num))

theorem finrank_ker_eq_two_of_layer_eq_bot {s : StatedSp 4 (ZMod 2)} (hs3 : s ^ 3 = 1)
    (hs1 : s ≠ 1)
    (hL : GLAPLayer 3 (Subgroup.centralizer ({s} : Set (StatedSp 4 (ZMod 2)))) = ⊥) :
    Module.finrank (ZMod 2) ↥(LinearMap.ker (spEnd s - 1)) = 2 := by
  obtain ⟨s₀, hc⟩ := exists_class_spSupported hs3 hs1
  obtain ⟨s₁, hs₁, hs4⟩ := dimension_count hs3 hs1
  have blocks := sp8_blocks s (orderOf_eq_prime hs3 hs1)
  have h1 := fixedRank_eq_one_of_layer_eq_bot hc hL
  have hsum := hc.sum_eq
  rw [← blocks.fixed_eq, hs₁]
  omega

end CFSG.LocalAnalysis.GLTheoremA.S265A

end
