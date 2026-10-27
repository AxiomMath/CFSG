module

public import CFSG.LocalAnalysis.GH72.Sec4Iso
import CFSG.LocalAnalysis.GH72.Coprime
import CFSG.GroupTheory.PGroup.LtInfNormalizer
public import CFSG.LocalAnalysis.GH72.Sec4K0

public section

namespace CFSG.GH72

open Subgroup

namespace G4b

section Hyperplane

variable {G : Type} [Group G] [Finite G]

theorem exists_centralizer_ne_bot {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E P : Subgroup G}
    (hE2 : ∀ e ∈ E, e * e = 1) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hP : IsPGroup p P)
    (hP1 : P ≠ ⊥) (hEP : E ≤ normalizer (P : Set G)) :
    ∃ T ≤ E, Nat.card E ≤ 2 * Nat.card T ∧ P ⊓ centralizer (T : Set G) ≠ ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  set Z : Subgroup G := P ⊓ centralizer (P : Set G) with hZ
  have hZ1 : Z ≠ ⊥ := by
    have : Nontrivial P := (nontrivial_iff_ne_bot P).2 hP1
    have hc := hP.center_nontrivial
    obtain ⟨c, hc1⟩ := exists_ne (1 : center P)
    intro hZb
    apply hc1
    have hmem : ((c : P) : G) ∈ Z := by
      refine mem_inf.2 ⟨(c : P).2, ?_⟩
      rw [mem_centralizer_iff]
      intro h hh
      exact congrArg Subtype.val (mem_center_iff.1 c.2 ⟨h, hh⟩)
    rw [hZb, mem_bot] at hmem
    exact Subtype.ext (Subtype.ext hmem)
  have hZodd : Odd (Nat.card Z) := odd_card_of_le inf_le_left (odd_card_of_isPGroup hp hp2 hP)
  have hZab : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := fun a ha b hb =>
    (mem_centralizer_iff.1 (mem_inf.1 hb).2 a (mem_inf.1 ha).1)
  have hEZ : E ≤ normalizer (Z : Set G) := fun e he =>
    mem_normalizer_inf (hEP he) (mem_normalizer_centralizer (hEP he))
  have hsplit : ∀ n : ℕ, ∀ W : Subgroup G, Nat.card W = n → W ≤ Z → W ≠ ⊥ →
      E ≤ normalizer (W : Set G) → ∃ W' ≤ W, W' ≠ ⊥ ∧ E ≤ normalizer (W' : Set G) ∧
        ∀ e ∈ E, (∀ w ∈ W', e * w * e⁻¹ = w) ∨ (∀ w ∈ W', e * w * e⁻¹ = w⁻¹) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro W hWn hWZ hW1 hEW
      by_cases hall : ∀ e ∈ E, (∀ w ∈ W, e * w * e⁻¹ = w) ∨ (∀ w ∈ W, e * w * e⁻¹ = w⁻¹)
      · exact ⟨W, le_rfl, hW1, hEW, hall⟩
      · obtain ⟨e, he, hne⟩ := not_forall₂.1 hall
        obtain ⟨hne₁, hne₂⟩ := not_or.1 hne
        have he1 : e ≠ 1 := fun h => hne₁ fun w _ => by rw [h]; group
        have he2 : orderOf e = 2 := orderOf_eq_prime (by rw [pow_two]; exact hE2 e he) he1
        have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb => hZab a (hWZ ha) b (hWZ hb)
        have hWodd : Odd (Nat.card W) := odd_card_of_le hWZ hZodd
        set W' : Subgroup G := W ⊓ C e with hW'
        have hW'lt : W' < W := by
          refine lt_of_le_of_ne inf_le_left fun h => hne₁ fun w hw => ?_
          have hw' : w ∈ W' := h ▸ hw
          have := mem_centralizer_singleton_iff.1 (mem_inf.1 hw').2
          rw [← this]
          group
        have hW'1 : W' ≠ ⊥ := by
          intro h
          apply hne₂
          intro w hw
          have hdec := inf_centralizer_sup_commutator_zpowers hWab hWodd he2 (hEW he)
          rw [← hW', h, bot_sup_eq] at hdec
          rw [← hdec] at hw
          exact ((mem_commutator_zpowers_iff hWab hWodd he2 (hEW he)).1 hw).2
        have hEW' : E ≤ normalizer (W' : Set G) := fun f hf =>
          mem_normalizer_inf (hEW hf) (le_normalizer
            (mem_centralizer_singleton_iff.2 (hEc f hf e he)))
        obtain ⟨W'', hW''W', hW''⟩ := ih (Nat.card W') (hWn ▸ card_lt_of_lt hW'lt) W' rfl
          (inf_le_left.trans hWZ) hW'1 hEW'
        exact ⟨W'', hW''W'.trans inf_le_left, hW''⟩
  obtain ⟨W, hWZ, hW1, -, hW⟩ := hsplit _ Z rfl le_rfl hZ1 hEZ
  set T : Subgroup G := E ⊓ centralizer (W : Set G) with hT
  have hcen : ∀ {e : G}, (∀ w ∈ W, e * w * e⁻¹ = w) → e ∈ centralizer (W : Set G) := by
    intro e he
    rw [mem_centralizer_iff]
    intro w hw
    calc w * e = e * w * e⁻¹ * e := by rw [he w hw]
      _ = e * w := by group
  refine ⟨T, inf_le_left, ?_, ?_⟩
  · by_cases hET : E ≤ T
    · have : T = E := le_antisymm inf_le_left hET
      rw [this]
      omega
    · obtain ⟨e₁, he₁, he₁T⟩ := SetLike.not_le_iff_exists.1 hET
      have he₁inv : ∀ w ∈ W, e₁ * w * e₁⁻¹ = w⁻¹ := by
        rcases hW e₁ he₁ with h | h
        · exact absurd (mem_inf.2 ⟨he₁, hcen h⟩) he₁T
        · exact h
      have hle : E ≤ T ⊔ zpowers e₁ := by
        intro e he
        by_cases heT : e ∈ T
        · exact mem_sup_left heT
        · have heinv : ∀ w ∈ W, e * w * e⁻¹ = w⁻¹ := by
            rcases hW e he with h | h
            · exact absurd (mem_inf.2 ⟨he, hcen h⟩) heT
            · exact h
          have hprod : e₁ * e ∈ T := by
            refine mem_inf.2 ⟨mul_mem he₁ he, hcen fun w hw => ?_⟩
            calc e₁ * e * w * (e₁ * e)⁻¹ = e₁ * (e * w * e⁻¹) * e₁⁻¹ := by group
              _ = (e₁ * w * e₁⁻¹)⁻¹ := by rw [heinv w hw]; group
              _ = w := by rw [he₁inv w hw, inv_inv]
          have e' : e = e₁ * (e₁ * e) := by
            rw [← mul_assoc, hE2 e₁ he₁, one_mul]
          rw [e']
          exact mul_mem (mem_sup_right (mem_zpowers e₁)) (mem_sup_left hprod)
      have he₁1 : e₁ ≠ 1 := fun h => he₁T (h ▸ one_mem T)
      have hzc : Nat.card (zpowers e₁) = 2 := by
        rw [Nat.card_zpowers]
        exact orderOf_eq_prime (by rw [pow_two]; exact hE2 e₁ he₁) he₁1
      have hTz : T ⊓ zpowers e₁ = ⊥ := by
        rw [eq_bot_iff]
        intro y hy
        obtain ⟨hyT, hyz⟩ := mem_inf.1 hy
        rcases CFSG.CGT.Foote81L6.TStruct.eq_one_or_eq_of_mem_zpowers (hE2 e₁ he₁) hyz with
          rfl | rfl
        · exact one_mem _
        · exact absurd hyT he₁T
      have hzT : zpowers e₁ ≤ normalizer (T : Set G) := by
        rw [zpowers_le]
        refine mem_normalizer_inf (le_normalizer he₁) (mem_normalizer_centralizer ?_)
        rw [mem_normalizer_iff_map_conj_eq']
        apply le_antisymm
        · rintro _ ⟨w, hw, rfl⟩
          rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, he₁inv w hw]
          exact inv_mem hw
        · intro w hw
          refine ⟨w⁻¹, inv_mem hw, ?_⟩
          rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, he₁inv _ (inv_mem hw), inv_inv]
      have hcard := CFSG.CGT.Foote81L6.card_sup_of_le_normalizer hzT hTz
      rw [hzc] at hcard
      calc Nat.card E ≤ Nat.card ↥(T ⊔ zpowers e₁) := card_le_of_le hle
        _ = 2 * Nat.card T := by rw [hcard, mul_comm]
  · intro h
    apply hW1
    rw [eq_bot_iff]
    intro w hw
    have hw' : w ∈ P ⊓ centralizer (T : Set G) := by
      refine mem_inf.2 ⟨(mem_inf.1 (hWZ hw)).1, ?_⟩
      rw [mem_centralizer_iff]
      intro t ht
      exact (mem_centralizer_iff.1 (mem_inf.1 ht).2 w hw).symm
    rw [h] at hw'
    exact hw'

end Hyperplane

end G4b

namespace Sec4Setting

open G4b

variable {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G)

theorem exists_ne_of_isKleinFour {V : Subgroup G} (hV : IsKleinFour V) (v : G) :
    ∃ w ∈ V, w ≠ 1 ∧ w ≠ v := by
  by_contra h
  have h' : ∀ w ∈ V, w ≠ 1 → w = v := fun w hw hw1 => by
    by_contra hwv
    exact h ⟨w, hw, hw1, hwv⟩
  by_cases hv : v ∈ V
  · have hle : V ≤ zpowers v := fun w hw => by
      by_cases hw1 : w = 1
      · rw [hw1]
        exact one_mem _
      · rw [h' w hw hw1]
        exact mem_zpowers v
    have hv2 : v ^ 2 = 1 := by
      rw [pow_two]
      exact congrArg Subtype.val (IsKleinFour.mul_self (⟨v, hv⟩ : V))
    have h1 := card_le_of_le hle
    rw [Nat.card_zpowers, hV.card_four] at h1
    have h2 := orderOf_le_of_pow_eq_one (by norm_num) hv2
    omega
  · have hle : V ≤ ⊥ := fun w hw => by
      by_cases hw1 : w = 1
      · rw [hw1]
        exact one_mem _
      · exact absurd (h' w hw hw1 ▸ hw) hv
    have h1 := card_le_of_le hle
    rw [card_bot, hV.card_four] at h1
    omega

theorem centralizer_ne_top {A T : Subgroup G} (hAS : A ≤ 𝔖.S) (hA : IsE16 A) (hTA : T ≤ A)
    (hT : T ≠ ⊥) : centralizer (T : Set G) ≠ ⊤ := by
  have hA2 : IsPGroup 2 A := IsPGroup.of_card (n := 4) (by rw [hA.2]; norm_num)
  obtain ⟨t, htT, ht1, htt⟩ := exists_involution (hA2.to_le hTA) hT
  intro hC
  have hcen : ∀ g : G, g * t * g⁻¹ = t := fun g => by
    have hg : g ∈ centralizer (T : Set G) := hC ▸ mem_top g
    have h := mem_centralizer_iff.1 hg t htT
    calc g * t * g⁻¹ = t * g * g⁻¹ := by rw [h]
      _ = t := by group
  have htA : t ∈ A := hTA htT
  have hconj : ∀ {u : G}, IsConj t u → u = t := fun hu => by
    obtain ⟨c, hc⟩ := isConj_iff.1 hu
    rw [← hc, hcen c]
  by_cases htX : t ∈ 𝔖.X A
  · obtain ⟨w, hwX, hw1, hwt⟩ := exists_ne_of_isKleinFour (isKleinFour_X 𝔖 hAS hA) t
    obtain ⟨n, -, hn⟩ := exists_mem_normalizer_conj_eq_of_mem_X 𝔖 hAS hA hwX hw1
    obtain ⟨m, -, hm⟩ := exists_mem_normalizer_conj_eq_of_mem_X 𝔖 hAS hA htX ht1
    have hz : 𝔖.z₁ = t := by
      have e : 𝔖.z₁ = m⁻¹ * (m * 𝔖.z₁ * m⁻¹) * m⁻¹⁻¹ := by group
      rw [e, hm, hcen m⁻¹]
    exact hwt (by rw [← hn, hz, hcen n])
  by_cases htY : t ∈ 𝔖.Y A
  · obtain ⟨w, hwY, hw1, hwt⟩ := exists_ne_of_isKleinFour (isKleinFour_Y 𝔖 hAS hA) t
    obtain ⟨n, -, hn⟩ := exists_mem_normalizer_conj_eq_of_mem_Y 𝔖 hAS hA hwY hw1
    obtain ⟨m, -, hm⟩ := exists_mem_normalizer_conj_eq_of_mem_Y 𝔖 hAS hA htY ht1
    have hz : 𝔖.z₂ = t := by
      have e : 𝔖.z₂ = m⁻¹ * (m * 𝔖.z₂ * m⁻¹) * m⁻¹⁻¹ := by group
      rw [e, hm, hcen m⁻¹]
    exact hwt (by rw [← hn, hz, hcen n])
  have htS₁ : t ∉ 𝔖.S₁ := fun h => htX (mem_inf.2 ⟨htA, h⟩)
  have htS₂ : t ∉ 𝔖.S₂ := fun h => htY (mem_inf.2 ⟨htA, h⟩)
  have ht2 : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact htt) ht1
  have htS : t ∈ 𝔖.S₁ ⊔ 𝔖.S₂ := by rw [𝔖.decomp.sup_eq]; exact hAS htA
  obtain ⟨x₁, hx₁, hx₁1, -⟩ := exists_ne_of_isKleinFour (isKleinFour_X 𝔖 hAS hA) 1
  obtain ⟨x₂, hx₂, hx₂1, hx₂x₁⟩ := exists_ne_of_isKleinFour (isKleinFour_X 𝔖 hAS hA) x₁
  obtain ⟨y, hy, hy1, -⟩ := exists_ne_of_isKleinFour (isKleinFour_Y 𝔖 hAS hA) 1
  have hdiag : ∀ {x : G}, x ∈ 𝔖.X A → x ≠ 1 → x * y = t := by
    intro x hx hx1
    have hxS₁ : x ∈ 𝔖.S₁ := X_le_S₁ 𝔖 hx
    have hyS₂ : y ∈ 𝔖.S₂ := Y_le_S₂ 𝔖 hy
    have hn₁ : x * y ∉ 𝔖.S₁ := fun h => hy1 ((𝔖.decomp.mul_mem_left_iff hxS₁ hyS₂).1 h)
    have hn₂ : x * y ∉ 𝔖.S₂ := fun h => hx1 ((𝔖.decomp.mul_mem_right_iff hxS₁ hyS₂).1 h)
    have hxy1 : x * y ≠ 1 := fun h => hn₁ (h ▸ one_mem _)
    have hxy2 : (x * y) ^ 2 = 1 := by
      have hc : y * x = x * y := (mem_centralizer_iff.1 (S₂_le_centralizer_S₁ 𝔖 hyS₂) x hxS₁).symm
      rw [pow_two]
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [hc]
        _ = (x * x) * (y * y) := by group
        _ = 1 := by rw [mul_self_eq_one_of_isE16 hA (X_le_A 𝔖 hx),
              mul_self_eq_one_of_isE16 hA (Y_le_A 𝔖 hy), one_mul]
    exact hconj (𝔖.fusion.conj₃ t htS (x * y) (mul_mem_sup hxS₁ hyS₂) htS₁ htS₂ hn₁ hn₂ ht2
      (orderOf_eq_prime hxy2 hxy1))
  exact hx₂x₁ (mul_right_cancel ((hdiag hx₂ hx₂1).trans (hdiag hx₁ hx₁1).symm))


theorem prop_4_6_of
    (h44 : ∀ H : Subgroup G, H ≠ ⊤ → (∀ t, ¬ IsIsolatedIn H t) →
      ∀ A : Subgroup G, A ≤ H → IsE16 A → ∀ J : Subgroup G, O2 H ⊔ A ≤ J → J ≤ H →
      CFSG.ABGLocalTools.IsSylowOf 2 ((𝔖.S₁ ⊓ J) ⊔ (𝔖.S₂ ⊓ J)) J →
      ∃ L₁ L₂ : Subgroup (Bar H), L₁ ≤ bar H J ∧ L₂ ≤ bar H J ∧ L₁ ⊓ L₂ = ⊥ ∧
        L₂ ≤ centralizer (L₁ : Set (Bar H)) ∧ ((L₁ ⊔ L₂).subgroupOf (bar H J)).Normal ∧
        bar H J = (L₁ ⊔ L₂) ⊔ (bar H J ⊓ normalizer (bar H A : Set (Bar H))) ∧
        IsL2PGL2OrA7OrV4 L₁ ∧ IsL2PGL2OrA7OrV4 L₂ ∧
        CFSG.ABGLocalTools.IsSylowOf 2 (bar H 𝔖.S₁ ⊓ L₁) L₁ ∧
        CFSG.ABGLocalTools.IsSylowOf 2 (bar H 𝔖.S₂ ⊓ L₂) L₂ ∧
        bar H 𝔖.S₁ ⊓ bar H J ≤ L₁ ∧ bar H 𝔖.S₂ ⊓ bar H J ≤ L₂ ∧
        (L₁.subgroupOf (bar H J)).Normal ∧ (L₂.subgroupOf (bar H J)).Normal)
    (h44J : ∀ H : Subgroup G, H ≠ ⊤ → (∀ t, ¬ IsIsolatedIn H t) →
      ∀ A : Subgroup G, A ≤ H → A ≤ 𝔖.S → IsE16 A →
      CFSG.ABGLocalTools.IsSylowOf 2 ((𝔖.S : Subgroup G) ⊓ H) H →
      CFSG.ABGLocalTools.IsSylowOf 2 ((𝔖.S₁ ⊓ (O2 H ⊔ A)) ⊔ (𝔖.S₂ ⊓ (O2 H ⊔ A)))
        (O2 H ⊔ A))
    (h315 : ∀ z₁ z₂ : G, (z₁ ∈ 𝔖.S₁ ∧ orderOf z₁ = 2 ∧ 𝔖.S₁ ≤ C z₁) →
      (z₂ ∈ 𝔖.S₂ ∧ orderOf z₂ = 2 ∧ 𝔖.S₂ ≤ C z₂) →
      (∃ H₁ : Subgroup (Bar (C z₁)), bar (C z₁) 𝔖.S₁ ⊓ H₁ = ⊥ ∧ bar (C z₁) 𝔖.S₁ ⊔ H₁ = ⊤ ∧
        H₁ ≤ centralizer (bar (C z₁) 𝔖.S₁ : Set (Bar (C z₁))) ∧
        bar (C z₁) 𝔖.S₂ ≤ ⁅H₁, H₁⁆ ∧ IsL2OrA7 (⁅H₁, H₁⁆ : Subgroup (Bar (C z₁))) 7) ∧
      (∃ K₁ : Subgroup (Bar (C z₂)), bar (C z₂) 𝔖.S₂ ⊓ K₁ = ⊥ ∧ bar (C z₂) 𝔖.S₂ ⊔ K₁ = ⊤ ∧
        K₁ ≤ centralizer (bar (C z₂) 𝔖.S₂ : Set (Bar (C z₂))) ∧
        bar (C z₂) 𝔖.S₁ ≤ ⁅K₁, K₁⁆ ∧
        (IsL2OrA7 (⁅K₁, K₁⁆ : Subgroup (Bar (C z₂))) 5 ∨ ⁅K₁, K₁⁆ = bar (C z₂) 𝔖.S₁)))
    (h317 : ∀ z₁ z₂ : G, (z₁ ∈ 𝔖.S₁ ∧ orderOf z₁ = 2 ∧ 𝔖.S₁ ≤ C z₁) →
      (z₂ ∈ 𝔖.S₂ ∧ orderOf z₂ = 2 ∧ 𝔖.S₂ ≤ C z₂) → HasNormalTwoComplement (C (z₁ * z₂)))
    (A : Subgroup G) (hA : IsE16 A) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (P₁ P₂ : Subgroup G) (h₁ : IsMaxInvIn p A ⊤ P₁) (h₂ : IsMaxInvIn p A ⊤ P₂) :
    ∃ g ∈ normalizer (A : Set G), P₁.map (MulAut.conj g).toMonoidHom = P₂ := by
  have : Fact p.Prime := ⟨hp⟩
  suffices key : ∀ A : Subgroup G, A ≤ 𝔖.S → IsE16 A → ∀ Q₁ Q₂ : Subgroup G,
      IsMaxInvIn p A ⊤ Q₁ → IsMaxInvIn p A ⊤ Q₂ →
      ∃ g ∈ normalizer (A : Set G), Q₁.map (MulAut.conj g).toMonoidHom = Q₂ by
    obtain ⟨x, hAx, -⟩ := exists_map_conj_sylow 𝔖 ⊤ A le_top hA
    have htop : (⊤ : Subgroup G).map (MulAut.conj x).toMonoidHom = ⊤ :=
      map_top_of_surjective _ (MulAut.conj x).surjective
    obtain ⟨g, hg, hgP⟩ := G4b.exists_conj_of_map_conj (H := ⊤) x (fun Q₁ Q₂ hQ₁ hQ₂ => by
      rw [htop] at hQ₁ hQ₂ ⊢
      obtain ⟨g, hg, hgQ⟩ := key _ hAx (G4b.IsE16.map hA _) Q₁ Q₂ hQ₁ hQ₂
      exact ⟨g, mem_inf.2 ⟨mem_top g, hg⟩, hgQ⟩) h₁ h₂
    exact ⟨g, (mem_inf.1 hg).2, hgP⟩
  intro A hAS hA
  clear h₁ h₂ P₁ P₂
  have hA2 : IsPGroup 2 A := IsPGroup.of_card (n := 4) (by rw [hA.2]; norm_num)
  have hO : CFSG.oddCore G = ⊥ := 𝔖.mc.hyp.1
  have T45 : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H → ∀ Q₁ Q₂ : Subgroup G, IsMaxInvIn p A H Q₁ →
      IsMaxInvIn p A H Q₂ →
      ∃ g ∈ H ⊓ normalizer (A : Set G), Q₁.map (MulAut.conj g).toMonoidHom = Q₂ :=
    fun H hH hAH Q₁ Q₂ hQ₁ hQ₂ =>
      lemma_4_5_of 𝔖 h44 h44J h315 h317 H hH A hAH hA p hp hp2 Q₁ Q₂ hQ₁ hQ₂
  let Rel : Subgroup G → Subgroup G → Prop := fun Q₁ Q₂ =>
    ∃ g ∈ normalizer (A : Set G), Q₁.map (MulAut.conj g).toMonoidHom = Q₂
  have Rel_refl : ∀ Q, Rel Q Q := fun Q => ⟨1, one_mem _, map_conj_one Q⟩
  have Rel_symm : ∀ {Q₁ Q₂}, Rel Q₁ Q₂ → Rel Q₂ Q₁ := by
    rintro Q₁ Q₂ ⟨g, hg, rfl⟩
    exact ⟨g⁻¹, inv_mem hg, CFSG.GH72.map_conj_inv_map_conj Q₁ g⟩
  have Rel_trans : ∀ {Q₁ Q₂ Q₃}, Rel Q₁ Q₂ → Rel Q₂ Q₃ → Rel Q₁ Q₃ := by
    rintro Q₁ Q₂ Q₃ ⟨g, hg, rfl⟩ ⟨h, hh, rfl⟩
    exact ⟨h * g, mul_mem hh hg, (G4b.map_conj_map_conj Q₁ g h).symm⟩
  have Rel_map : ∀ {Q : Subgroup G} {g : G}, g ∈ normalizer (A : Set G) →
      Rel Q (Q.map (MulAut.conj g).toMonoidHom) := fun hg => ⟨_, hg, rfl⟩
  have hmax_map : ∀ {Q : Subgroup G} {g : G}, g ∈ normalizer (A : Set G) →
      IsMaxInvIn p A ⊤ Q → IsMaxInvIn p A ⊤ (Q.map (MulAut.conj g).toMonoidHom) := by
    intro Q g hg hQ
    have h := G4b.IsMaxInvIn.map hQ (MulAut.conj g)
    rwa [mem_normalizer_iff_map_conj_eq'.1 hg,
      map_top_of_surjective _ (MulAut.conj g).surjective] at h
  intro P₁ P₂ h₁ h₂
  by_contra hcon
  set 𝓒 : Set (Subgroup G × Subgroup G) :=
    {pq | IsMaxInvIn p A ⊤ pq.1 ∧ IsMaxInvIn p A ⊤ pq.2 ∧ ¬ Rel pq.1 pq.2} with h𝓒
  obtain ⟨⟨Q₁, Q₂⟩, ⟨hQ₁, hQ₂, hQ⟩, hmax⟩ := Set.exists_max_image 𝓒
    (fun pq => Nat.card ↥(pq.1 ⊓ pq.2)) (Set.toFinite _) ⟨(P₁, P₂), h₁, h₂, hcon⟩
  have hkey : ∀ R₁ R₂ : Subgroup G, IsMaxInvIn p A ⊤ R₁ → IsMaxInvIn p A ⊤ R₂ →
      Nat.card ↥(Q₁ ⊓ Q₂) < Nat.card ↥(R₁ ⊓ R₂) → Rel R₁ R₂ := fun R₁ R₂ hR₁ hR₂ hlt => by
    by_contra hR
    exact absurd (hmax (R₁, R₂) ⟨hR₁, hR₂, hR⟩) (not_le.2 hlt)
  apply hQ
  set D : Subgroup G := Q₁ ⊓ Q₂ with hD
  have hDQ₁ : D < Q₁ := lt_of_le_of_ne inf_le_left fun h => hQ (by
    have hle : Q₁ ≤ Q₂ := h ▸ inf_le_right
    rw [hQ₁.2.2.2 Q₂ le_top hQ₂.2.1 hQ₂.2.2.1 hle]
    exact Rel_refl Q₁)
  have hDQ₂ : D < Q₂ := lt_of_le_of_ne inf_le_right fun h => hQ (by
    have hle : Q₂ ≤ Q₁ := h ▸ inf_le_left
    rw [hQ₂.2.2.2 Q₁ le_top hQ₁.2.1 hQ₁.2.2.1 hle]
    exact Rel_refl Q₂)
  have hAQ : ∀ {Q : Subgroup G}, IsMaxInvIn p A ⊤ Q → ∀ {K : Subgroup G},
      A ≤ normalizer (K : Set G) → A ≤ normalizer ((Q ⊓ K : Subgroup G) : Set G) :=
    fun hQ _ hK a ha => mem_normalizer_inf (hQ.2.2.1 ha) (hK ha)
  have chain : ∀ K : Subgroup G, K ≠ ⊤ → A ≤ K →
      Nat.card D < Nat.card ↥(Q₁ ⊓ K) → Nat.card D < Nat.card ↥(Q₂ ⊓ K) → Rel Q₁ Q₂ := by
    intro K hK hAK h₁K h₂K
    have hAK' : A ≤ normalizer (K : Set G) := hAK.trans le_normalizer
    obtain ⟨P₁', hP₁', hle₁⟩ := exists_isMaxInvIn_ge (A := A) (H := K) inf_le_right
      (hQ₁.2.1.to_le inf_le_left) (hAQ hQ₁ hAK')
    obtain ⟨P₂', hP₂', hle₂⟩ := exists_isMaxInvIn_ge (A := A) (H := K) inf_le_right
      (hQ₂.2.1.to_le inf_le_left) (hAQ hQ₂ hAK')
    obtain ⟨k, hk, hkP⟩ := T45 K hK hAK P₁' P₂' hP₁' hP₂'
    have hkA : k ∈ normalizer (A : Set G) := (mem_inf.1 hk).2
    obtain ⟨R₁, hR₁, hP₁R₁⟩ := exists_isMaxInvIn_ge (A := A) (H := ⊤) le_top hP₁'.2.1 hP₁'.2.2.1
    obtain ⟨R₂, hR₂, hP₂R₂⟩ := exists_isMaxInvIn_ge (A := A) (H := ⊤) le_top hP₂'.2.1 hP₂'.2.2.1
    have hc₁ : Rel R₁ Q₁ := hkey R₁ Q₁ hR₁ hQ₁ (lt_of_lt_of_le h₁K
      (card_le_of_le (le_inf (hle₁.trans hP₁R₁) inf_le_left)))
    have hc₂ : Rel R₂ Q₂ := hkey R₂ Q₂ hR₂ hQ₂ (lt_of_lt_of_le h₂K
      (card_le_of_le (le_inf (hle₂.trans hP₂R₂) inf_le_left)))
    have hR₁k := hmax_map hkA hR₁
    have hc₃ : Rel (R₁.map (MulAut.conj k).toMonoidHom) R₂ :=
      hkey _ R₂ hR₁k hR₂ (lt_of_lt_of_le h₂K (card_le_of_le (le_inf
        ((hle₂.trans (hkP ▸ map_mono hP₁R₁)) : Q₂ ⊓ K ≤ R₁.map (MulAut.conj k).toMonoidHom)
        (hle₂.trans hP₂R₂))))
    exact Rel_trans (Rel_symm hc₁) (Rel_trans (Rel_map hkA) (Rel_trans hc₃ hc₂))
  by_cases hD1 : D = ⊥
  ·
    have hQ₁1 : Q₁ ≠ ⊥ := fun h => (hDQ₁.trans_le h.le).ne (hD1 ▸ rfl) |>.elim
    have hQ₂1 : Q₂ ≠ ⊥ := fun h => (hDQ₂.trans_le h.le).ne (hD1 ▸ rfl) |>.elim
    have hA2' : ∀ e ∈ A, e * e = 1 := fun e he => mul_self_eq_one_of_isE16 hA he
    have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => comm_of_isE16 hA ha hb
    obtain ⟨T₁, hT₁A, hT₁c, hT₁⟩ :=
      exists_centralizer_ne_bot hp hp2 hA2' hAc hQ₁.2.1 hQ₁1 hQ₁.2.2.1
    obtain ⟨T₂, hT₂A, hT₂c, hT₂⟩ :=
      exists_centralizer_ne_bot hp hp2 hA2' hAc hQ₂.2.1 hQ₂1 hQ₂.2.2.1
    set T : Subgroup G := T₁ ⊓ T₂ with hT
    have hT1 : T ≠ ⊥ := by
      intro h
      have hn : T₂ ≤ normalizer (T₁ : Set G) := fun t ht =>
        mem_normalizer_of_conj_mem (fun s hs => by
            rw [comm_of_isE16 hA (hT₂A ht) (hT₁A hs), mul_assoc, mul_inv_cancel, mul_one]
            exact hs)
          (fun s hs => by
            rw [mul_assoc, comm_of_isE16 hA (hT₁A hs) (hT₂A ht), ← mul_assoc, inv_mul_cancel,
              one_mul]
            exact hs)
      have hcard := CFSG.CGT.Foote81L6.card_sup_of_le_normalizer hn h
      have hle := card_le_of_le (sup_le hT₁A hT₂A)
      rw [hcard, hA.2] at hle
      rw [hA.2] at hT₁c hT₂c
      nlinarith
    set K : Subgroup G := centralizer (T : Set G) with hK
    have hAK : A ≤ K := by
      intro a ha
      rw [hK, mem_centralizer_iff]
      intro t ht
      exact comm_of_isE16 hA (hT₁A (mem_inf.1 ht).1) ha
    have hKtop : K ≠ ⊤ := centralizer_ne_top 𝔖 hAS hA (inf_le_left.trans hT₁A) hT1
    have hcardD : Nat.card D = 1 := by rw [hD1, card_bot]
    have hpos : ∀ {Q : Subgroup G} {T' : Subgroup G}, T ≤ T' →
        Q ⊓ centralizer (T' : Set G) ≠ ⊥ → Nat.card D < Nat.card ↥(Q ⊓ K) := by
      intro Q T' hTT' hne
      rw [hcardD, one_lt_card_iff_ne_bot]
      intro h
      apply hne
      rw [eq_bot_iff, ← h]
      exact inf_le_inf_left _ (centralizer_le (SetLike.coe_subset_coe.2 hTT'))
    exact chain K hKtop hAK (hpos inf_le_left hT₁) (hpos inf_le_right hT₂)
  ·
    set K : Subgroup G := normalizer (D : Set G) with hK
    have hAK : A ≤ K := fun a ha => mem_normalizer_inf (hQ₁.2.2.1 ha) (hQ₂.2.2.1 ha)
    have hKtop : K ≠ ⊤ := by
      intro h
      have hDn : D.Normal := normalizer_eq_top_iff.1 h
      have hle : D ≤ CFSG.oddCore G :=
        le_sSup ⟨hDn, odd_card_of_isPGroup hp hp2 (hQ₁.2.1.to_le inf_le_left)⟩
      rw [hO] at hle
      exact hD1 (eq_bot_iff.2 hle)
    have hgrow : ∀ {Q : Subgroup G}, IsMaxInvIn p A ⊤ Q → D < Q →
        Nat.card D < Nat.card ↥(Q ⊓ K) := by
      intro Q hQ hDQ
      have : Group.IsNilpotent Q := hQ.2.1.isNilpotent
      exact card_lt_of_lt (CFSG.GroupTheory.lt_inf_normalizer_of_isNilpotent hDQ)
    exact chain K hKtop hAK (hgrow hQ₁ hDQ₁) (hgrow hQ₂ hDQ₂)

end Sec4Setting

end CFSG.GH72
