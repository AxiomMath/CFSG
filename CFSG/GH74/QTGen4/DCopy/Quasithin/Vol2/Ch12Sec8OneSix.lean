module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneSix
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneSixStmt
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneThirteen
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneThirteenFour

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace L128P

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem lt_zU_of_elemAbelian_F4 (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4) {T L V : Subgroup G}
    {n : ℕ} {V₁ V₂ : Subgroup G} (hs : Setting1282One G T L V n V₁ V₂)
    (D : HatModelU (u128 V V₁)) {a : G} (ha : a ∈ V₂) (haV₁ : a ∉ V₁)
    {Y : Subgroup (D.V ≃ₗ[ZMod 2] D.V)}
    (hYΓ : Y ≤ D.img (Subgroup.normalizer (V₁ : Set G))) (hYv : ∀ y ∈ Y, y (D.π a) = D.π a)
    (hY3 : IsElemAbelian 3 Y) (hY9 : Nat.card Y = 9) : V₁ < zU128 V V₁ := by
  classical
  have hle : V₁ ≤ zU128 V V₁ := hs.le_centerOf_F4 h1222 h12213
  refine lt_of_le_of_ne hle fun heq => ?_
  obtain ⟨-, -, hab⟩ := hs.hyp.card_sq
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hs.v1.2.1
  have hV₂4 : Nat.card V₂ = 4 := by simpa using hs.v2.2.1
  obtain ⟨z, hz, hz1, -, -, -⟩ := exists_gens hV₁2 hV₂4
  set C := centralizerMod V₁ (Subgroup.normalizer (V₁ : Set G)) V₂ with hCdef
  have hCN : C ≤ Subgroup.normalizer (u128 V V₁ : Set G) := fun x hx =>
    le_normalizer_conjClosure V _ hx.1
  have haV := hs.v2.1 ha
  have haU : a ∈ u128 V V₁ := le_conjClosure V _ haV
  have hYC : Y ≤ D.img C := by
    intro y hy
    obtain ⟨h, hh, hhN, rfl⟩ := (L128A.HatU.mem_img D).1 (hYΓ hy)
    refine (L128A.HatU.mem_img D).2 ⟨h, ?_, hhN, rfl⟩
    have h1 := hYv _ hy
    have heq' : centerOf (u128 V V₁) = V₁ := heq.symm
    rw [D.ρ_π ⟨h, hhN⟩ a haU, D.π_eq_iff _ (L128A.HatU.conj_mem hhN haU) a haU, heq'] at h1

    set c := (h * a * h⁻¹)⁻¹ * a with hcdef
    have hcV := hs.v1.1 h1
    have hha : h * a * h⁻¹ = a * c⁻¹ := by rw [hcdef]; group
    have hcomm : h * a * h⁻¹ * a⁻¹ ∈ V₁ := by
      rw [hha, hab a haV c⁻¹ (V.inv_mem hcV)]
      have e : c⁻¹ * a * a⁻¹ = c⁻¹ := by group
      rw [e]
      exact V₁.inv_mem h1
    have hhz : h * z * h⁻¹ = z := L1297.conj_eq_of_mem_normalizer hV₁2 hz hh
    refine ⟨hh, hh, fun w hw => ?_⟩
    rcases eq_of_mem_four hs.le hV₁2 hV₂4 hz hz1 haV₁ ha hw with e | e | e | e <;> rw [e]
    · simp
    · rw [hhz, mul_inv_cancel]
      exact V₁.one_mem
    · exact hcomm
    · have e2 : h * (z * a) * h⁻¹ * (z * a)⁻¹ = (h * z * h⁻¹) * (h * a * h⁻¹ * a⁻¹) * z⁻¹ := by
        group
      rw [e2, hhz]
      have hc' : h * a * h⁻¹ * a⁻¹ ∈ V := hs.v1.1 hcomm
      rw [hab z (hs.v1.1 hz) _ hc']
      have e3 : h * a * h⁻¹ * a⁻¹ * z * z⁻¹ = h * a * h⁻¹ * a⁻¹ := by group
      rw [e3]
      exact hcomm
  have hpr : 2 ≤ CFSG.Open.pRank 3 (D.img C) :=
    CFSG.SectionRank.le_pRank (by norm_num) hYC hY3 (by rw [hY9]; norm_num)
  rw [L1294.img_eq_range D hCN, ← pRank_top_subtype (p := 3)] at hpr
  have h2 := two_le_pRank_of_surjective' Nat.prime_three (by norm_num)
    (D.ρ.comp (Subgroup.inclusion hCN)).rangeRestrict
    (MonoidHom.rangeRestrict_surjective _) hpr
  rw [pRank_top_subtype (p := 3)] at h2
  have h3 : CFSG.Open.pRank 3 C ≤ 1 := thirteen_eight_F4 h1222 h12213 hs
  omega

end L128P

open L128P in

theorem lemma12_8_13_six_hat_of_F4 (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4)
    (h1228 : Stmt12_2_8_F4) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h5 : Lemma12_8_8_five_F4) (hKG : A7NatFact12813) : Lemma12_8_13_six_hat_F4 := by
  intro G _ _ T L V n V₁ V₂ hs hn D hC4
  obtain ⟨k, hk, hkN⟩ := exists_not_mem_normalizer_F4 h1222 hs
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hs.v1.2.1
  have hV₂4 : Nat.card V₂ = 4 := by simpa using hs.v2.2.1
  obtain ⟨-, -, -, a, haV₂, haV₁⟩ := exists_gens hV₁2 hV₂4
  have S := setting128A_F4 h1222 h12213 hs
  have hUeq := uA_eq_F4 h1222 hs
  have hgood : L128A.Good V₁ (oTwoUpper (p128 T L V)) k := ⟨hk, hkN⟩
  have hG := S.twelve_three_of_eq hgood hUeq D (four_lt_relIndex_F4 h1222 h12213 hs) haV₂ haV₁
  set Γ := D.img (Subgroup.normalizer (V₁ : Set G)) with hΓ
  set v := D.π a with hv
  set W := D.hat (u128 V V₁ ⊓ Subgroup.centralizer (V₂ : Set G) ⊓
    rconj (u128 V V₁ ⊓ Subgroup.centralizer (V₂ : Set G)) k) with hW
  set X := D.img (rconj (u128 V V₁ ⊓ Subgroup.centralizer (V₂ : Set G)) k) with hX
  set X₀ := D.img (rconj (centerOf (u128 V V₁)) k) with hX₀

  obtain ⟨S', hS'syl, hXS', -⟩ := hG.four
  have hS'Γ := isSylowTwoOf_of_stabilizer hS'syl hG.odd_index
  have hS'v : ∀ s ∈ S', s v = v := fun s hs' =>
    MulAction.mem_stabilizer_iff.1 (hS'syl.1 hs').2
  obtain ⟨Up, hUpS, hUpv, hvUp, hcases⟩ :=
    hKG D.V D.B Γ S' v hC4 hG.alt hG.nondegenerate hG.isometry hS'Γ hG.point hS'v

  have hUE : ∀ w ∈ Up, w ∈ W → w = 0 := by
    intro w hwU hwW
    by_contra hw0
    have hspan : (⟨w, hwW⟩ : W) ∉ (ZMod 2) ∙ (⟨v, hG.mem_W⟩ : W) := by
      intro hmem
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
      have hc' : c • v = w := by
        have := congrArg Subtype.val hc
        simpa using this
      rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
      · exact hw0 (by rw [← hc', zero_smul])
      · rw [one_smul] at hc'
        exact hvUp (by rw [hc']; exact hwU)
    obtain ⟨f, hf, hker⟩ := Submodule.exists_le_ker_of_notMem hspan
    have hfv : f ⟨v, hG.mem_W⟩ = 0 :=
      LinearMap.mem_ker.1 (hker (Submodule.mem_span_singleton_self _))
    obtain ⟨x, hxX, hx⟩ := hG.transvection_full f hfv
    have h1 := hx ⟨w, hwW⟩
    have hf1 : f ⟨w, hwW⟩ = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) _ hf
    rw [hf1, one_smul] at h1
    have h1' : x w = w + v := by simpa using h1
    have hxw : x w ∈ Up := hUpS x (hXS' hxX) w hwU
    apply hvUp
    have e : v = x w - w := by
      rw [h1']
      abel
    rw [e]
    exact Up.sub_mem hxw hwU

  have hXU : ∀ x ∈ X, ∀ u ∈ Up, x u = u := by
    intro x hx u hu
    have h1 := hG.commutator_le x hx u (hUpv u hu)
    have h2 : x u - u ∈ Up := Up.sub_mem (hUpS x (hXS' hx) u hu) hu
    exact sub_eq_zero.1 (hUE _ h2 h1)
  have hXel : IsElemAbelian 2 X :=
    ⟨⟨⟨fun a b => Subtype.ext (hG.X_comm _ a.2 _ b.2)⟩⟩, fun x hx => by
      rw [sq]
      exact hG.X_sq x hx⟩

  have hrank := hG.rank
  have hW3 := two_mul_finrank_le_of_isotropic D.B hG.alt hG.nondegenerate W hG.isotropic
  rw [hC4.1] at hrank hW3
  have hlog : 2 ≤ Nat.log 2 (X₀.relIndex X) := by omega
  have hne : X₀.relIndex X ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hidx : 4 ≤ X₀.relIndex X :=
    (Nat.pow_le_pow_right (by norm_num) hlog).trans (Nat.pow_log_le_self 2 hne)
  have hcardX := Subgroup.relIndex_mul_card X₀ X
  rw [inf_eq_left.2 hG.X₀_le] at hcardX
  rcases hcases with h2 | ⟨h4, Y, hYΓ, hYv, hY3, hY9⟩
  ·
    have hX2 := h2 X hXS' hXel hXU
    have := Nat.le_mul_of_pos_right (X₀.relIndex X) (Nat.card_pos (α := ↥X₀))
    omega
  ·
    have hX4 := h4 X hXS' hXel hXU
    have hZ := lt_zU_of_elemAbelian_F4 h1222 h12213 hs D haV₂ haV₁ hYΓ hYv hY3 hY9
    have h4' := thirteen_four_F4 h1222 h12213 h1228 h37 h38 h39 h5 hs hn (oTwoUpper_le _ hk) hkN hZ
    have hTU : T ≤ Subgroup.normalizer (u128 V V₁ : Set G) :=
      (hs.almostSpecial_F4 h1222 h12213).G22_three.2
    have hX₀ne : X₀ ≠ ⊥ := by
      intro hb
      apply h4'
      intro z hz
      have hzA : z ∈ rconj (centerOf (L128A.uA V₂ V₁)) k := by
        rw [hUeq]
        exact hz
      have hzT : z ∈ T := S.rconj_wA_le_T hgood
        (L128A.Setting.rconj_centerOf_le_rconj_wA V₂ V₁ k hzA)
      have hzN : z ∈ Subgroup.normalizer (u128 V V₁ : Set G) := hTU hzT
      have hρ : D.ρ ⟨z, hzN⟩ = 1 := by
        have h5' : D.ρ ⟨z, hzN⟩ ∈ X₀ := L128A.HatU.rho_mem_img D hz hzN
        rw [hb] at h5'
        exact Subgroup.mem_bot.1 h5'
      exact ⟨hs.v1.2.2 hzT, normalizer_le_normalizer_centerOf _ hzN,
        (L128A.HatU.rho_eq_one_iff D ⟨z, hzN⟩).1 hρ⟩
    have hX₀2 : 2 ≤ Nat.card X₀ := (Subgroup.one_lt_card_iff_ne_bot X₀).2 hX₀ne
    have := Nat.mul_le_mul_left (X₀.relIndex X) hX₀2
    omega

end CFSG.Quasithin.H13
