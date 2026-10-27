module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.I1435.PSp43Centralizer
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.I1435.Common

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435

open Subgroup CFSG.Open CFSG.GH74.Exceptional

theorem card_centralizer_conj {G : Type*} [Group G] (h a : G) :
    Nat.card (centralizer ({h * a * h⁻¹} : Set G)) = Nat.card (centralizer ({a} : Set G)) := by
  refine Nat.card_congr ((MulAut.conj h⁻¹).toEquiv.subtypeEquiv fun y => ?_)
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, inv_inv,
    SetLike.mem_coe, mem_centralizer_singleton_iff]
  constructor
  · intro H
    calc h⁻¹ * y * h * a = h⁻¹ * (y * (h * a * h⁻¹)) * h := by group
      _ = h⁻¹ * ((h * a * h⁻¹) * y) * h := by rw [H]
      _ = a * (h⁻¹ * y * h) := by group
  · intro H
    calc y * (h * a * h⁻¹) = h * ((h⁻¹ * y * h) * a) * h⁻¹ := by group
      _ = h * (a * (h⁻¹ * y * h)) * h⁻¹ := by rw [H]
      _ = h * a * h⁻¹ * y := by group

section Case

variable {X : Type} [Group X] [Finite X]

theorem sylow_psp43_W3 {K : Subgroup X} {P : Sylow 3 X} (e : ↥(P : Subgroup X) ≃* W3)
    (ψ : ↥K ≃* PSp43) (Q : Sylow 3 PSp43) : Nonempty (↥(Q : Subgroup PSp43) ≃* W3) := by
  have hQ : Nat.card (Q : Subgroup PSp43) = 81 :=
    card_sylow_three (m := 320) (by rw [card_PSp43]) (by norm_num) Q
  set H₁ : Subgroup ↥K := (Q : Subgroup PSp43).map ψ.symm.toMonoidHom
  set H : Subgroup X := H₁.map K.subtype
  have hHc : Nat.card H = 81 := by
    rw [card_map_of_injective K.subtype_injective, card_map_of_injective ψ.symm.injective, hQ]
  have hHp : IsPGroup 3 H := IsPGroup.of_card (n := 4) (by rw [hHc]; norm_num)
  obtain ⟨eH⟩ := nonempty_mulEquiv_W3 e hHp hHc
  exact ⟨((equivMapOfInjective _ _ ψ.symm.injective).trans
    (equivMapOfInjective H₁ K.subtype K.subtype_injective)).trans eH⟩

theorem psp43_case {K : Subgroup X} (hKn : K.Normal) {P : Sylow 3 X}
    (e : ↥(P : Subgroup X) ≃* W3) (ψ : ↥K ≃* PSp43) {x : X}
    (hxJ : x ∈ Open.thompsonSubgroup (P : Subgroup X)) (hx1 : x ≠ 1)
    (hlines : conjLinesIn (Open.thompsonSubgroup (P : Subgroup X)) x = 3)
    (hd1 : ∀ D : Subgroup X, D ≤ Open.thompsonSubgroup (P : Subgroup X) →
      (∀ g ∈ normalizer (Open.thompsonSubgroup (P : Subgroup X) : Set X), ∀ d ∈ D,
        g * d * g⁻¹ ∈ D) →
        D = ⊥ ∨ D = Open.thompsonSubgroup (P : Subgroup X)) :
    x ∈ K ∧ Nat.card ↥(K ⊓ centralizer ({x} : Set X)) = 108 := by
  set E := Open.thompsonSubgroup (P : Subgroup X) with hE
  have hK3 : 3 ∣ Nat.card K := by
    rw [Nat.card_congr ψ.toEquiv, card_PSp43]
    norm_num
  have hEK : E ≤ K := thompson_le_of_three_dvd hKn e hd1 hK3
  have hxK : x ∈ K := hEK hxJ
  refine ⟨hxK, ?_⟩
  have hEB : E = baseIn e := thompsonSubgroup_eq_baseIn e
  set F : Subgroup PSp43 := (E.subgroupOf K).map ψ.toMonoidHom with hF
  have hFc : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [SetLike.mem_coe, mem_subgroupOf, hEB] at ha hb
    exact baseIn_comm e ha hb
  have hFcard : Nat.card F = 27 := by
    rw [hF, card_map_of_injective ψ.injective, Nat.card_congr (subgroupOfEquivOfLe hEK).toEquiv,
      hEB, card_baseIn]
  obtain ⟨g, hg⟩ := exists_conj_eq (sylow_psp43_W3 e ψ) hFc (fun a ha b hb => E0_comm ha hb)
    hFcard card_E0
  set ψ' : ↥K ≃* PSp43 := ψ.trans (MulAut.conj g⁻¹) with hψ'
  have hF' : (E.subgroupOf K).map ψ'.toMonoidHom = E0 := map_trans_conj ψ _ hg
  have hxE0 : ψ' ⟨x, hxK⟩ ∈ E0 := by
    rw [← hF']
    exact mem_map_of_mem _ (show (⟨x, hxK⟩ : ↥K) ∈ E.subgroupOf K from hxJ)
  obtain ⟨s, hs⟩ := hxE0
  have hs0 : Multiplicative.toAdd s ≠ 0 := by
    intro h0
    have hs1 : s = 1 := Multiplicative.toAdd.injective h0
    rw [hs1, map_one] at hs
    have : (⟨x, hxK⟩ : ↥K) = 1 := ψ'.injective (by rw [← hs, map_one])
    exact hx1 (congrArg Subtype.val this)
  by_cases ha : aniso (Multiplicative.toAdd s)
  · rw [card_inf_centralizer_eq ψ' hxK, ← hs]
    have hconj := levPSp_conj (aTab (code (Multiplicative.toAdd s))) s
    rw [aniso_check _ ha] at hconj
    rw [← card_centralizer_conj (levPSp (aTab (code (Multiplicative.toAdd s)))) (uPSp s), hconj,
      card_centralizer_uPSp]
  · exfalso
    set c := code (Multiplicative.toAdd s)
    have hact : ∀ i : Fin 4, ψ' (ψ'.symm (levPSp (wTab c i)) * ⟨x, hxK⟩ *
        (ψ'.symm (levPSp (wTab c i)))⁻¹) = uPSp (Multiplicative.ofAdd
          (levAct (levA (wTab c i)) (Multiplicative.toAdd s))) := by
      intro i
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, ← hs, levPSp_conj]
    refine conjLinesIn_ne_three hEK ψ'.toMonoidHom ψ'.injective hxK
      (fun i => ψ'.symm (levPSp (wTab c i))) (fun i => ?_) (fun i j hij => ?_) hlines
    · show ψ' _ ∈ (E.subgroupOf K).map ψ'.toMonoidHom
      rw [hact i, hF']
      exact ⟨_, rfl⟩
    · change zpowers (ψ' _) = zpowers (ψ' _) at hij
      rw [hact i, hact j] at hij
      by_contra hne
      obtain ⟨d1, d2, d3⟩ := nonAniso_check _ hs0 ha i j hne
      rcases eq_of_zpowers_eq hij with h | h | h
      · exact d1 h
      · exact d2 h
      · exact d3 h

end Case

end CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435
