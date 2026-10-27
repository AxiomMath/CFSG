module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Der10One
public import CFSG.GH74.GLS.Stage2.Final.L26.G2Three
public import CFSG.GH74.GLS.Stage2.Final.L26.G2Lift

public section

open Subgroup CFSG CFSG.LocalCores CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Bender.Thm2
open CFSG.GH74.GLS.Stage2.Final.L26 (sl2_three_key' pow_eight_of_two_pow card_eq_of_hasSL2Model_three
  WBar_normal WBar_two_pow WBar_le_generalizedFitting)
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage2.Final.Thm4.L192

section Setup

variable {G : Type} [Group G] [Finite G] {z : G}

@[expose] def HDet (z : G) (𝒦 : Subgroup (CentralizerBar z)) : Prop :=
  ∀ c ∈ LBar z, (∃ a : ℕ, orderOf c = 2 ^ a) → c ^ 2 ∈ 𝒦 → ∀ g : CentralizerBar z, ⁅c, g⁆ ∈ 𝒦

omit [Finite G] in
theorem commutator_top_le_of_hdet {𝒦 : Subgroup (CentralizerBar z)} (hdet : HDet z 𝒦)
    {V : Subgroup (CentralizerBar z)} (hVL : V ≤ LBar z)
    (hV2 : ∀ v ∈ V, ∃ a : ℕ, orderOf v = 2 ^ a) (hVsq : ∀ v ∈ V, v ^ 2 ∈ 𝒦) :
    ⁅(⊤ : Subgroup (CentralizerBar z)), V⁆ ≤ 𝒦 := by
  refine Subgroup.commutator_le.mpr fun g _ v hv => ?_
  have h := hdet v (hVL hv) (hV2 v hv) (hVsq v hv) g
  rw [← commutatorElement_inv]
  exact 𝒦.inv_mem h

theorem generic_case {k : Kind} {S : Subgroup G} (ctx : Stage2Ctx G z k S)
    (hr : ¬ (k = Kind.m12 ∨ (k = Kind.g2 ∧ ¬ G2Big z S)))
    (𝒦 : Subgroup (CentralizerBar z)) (hdet : HDet z 𝒦) : LBar z ≤ 𝒦 := by
  obtain ⟨U, hUS, h4, hnorm⟩ := exists_normal_four_S ctx
  have hUL : U ≤ LC z := ctx.data.base.four_le U hUS h4 hnorm
  have hUC : U ≤ Cen z := hUL.trans (LC_le_Cen z)
  have h4bar := isFour_barOf z hUC h4
  refine (ctx.LBar_le_commutator hr hUS h4 hnorm).trans
    (commutator_top_le_of_hdet hdet (barOf_le_LBar hUL) (isFour_orderOf h4bar) ?_)
  intro v hv
  have : IsElementaryAbelian 2 ↥(barOf z U) := h4bar.1
  rw [elemPow_eq_one_of_isElementaryAbelian v hv]
  exact 𝒦.one_mem


end Setup

section G2Three

theorem sl23_sq : ∀ b : SL23, b ^ 8 = 1 → ∀ g : SL23, g * b ^ 2 = b ^ 2 * g := by
  decide +kernel

theorem nonempty_mulEquiv_sl23 {Y : Type} [Group Y] {L : Subgroup Y}
    (h : HasSL2Model ↥L (fun r => r = 3)) : Nonempty (↥L ≃* SL23) := by
  obtain ⟨F, hF, hFin, hq, ⟨e⟩⟩ := h
  have hq' : Nat.card F = 3 := hq
  have : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = Fintype.card (ZMod 3) := by
    rw [← Nat.card_eq_fintype_card, hq', ZMod.card]
  let φ : F ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq hcard
  exact ⟨(e.trans (specialLinearGroupEquivStatedSL 2 F).symm).trans (slMapEquiv φ)⟩

theorem sq_central_of_pow_eight {Y : Type} [Group Y] {L : Subgroup Y}
    (h : HasSL2Model ↥L (fun r => r = 3)) {b : Y} (hb : b ∈ L) (hb8 : b ^ 8 = 1) :
    ∀ g ∈ L, g * b ^ 2 = b ^ 2 * g := by
  obtain ⟨Φ⟩ := nonempty_mulEquiv_sl23 h
  intro g hg
  have h8 : (Φ ⟨b, hb⟩) ^ 8 = 1 := by
    have : (⟨b, hb⟩ : ↥L) ^ 8 = 1 := Subtype.ext (by simpa using hb8)
    rw [← map_pow, this, map_one]
  have h1 := sl23_sq (Φ ⟨b, hb⟩) h8 (Φ ⟨g, hg⟩)
  have h2 : (⟨g, hg⟩ : ↥L) * ⟨b, hb⟩ ^ 2 = ⟨b, hb⟩ ^ 2 * ⟨g, hg⟩ :=
    Φ.injective (by rw [map_mul, map_mul, map_pow]; exact h1)
  exact congrArg Subtype.val h2

theorem exists_order_three {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y}
    (h : HasSL2Model ↥L (fun r => r = 3)) (hZ : Nat.card (center ↥L) = 2) :
    ∃ l ∈ L, l ^ 3 = 1 ∧ ¬ ∀ g ∈ L, g * l = l * g := by
  have hcard := card_eq_of_hasSL2Model_three h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 3 (by rw [hcard]; norm_num)
  refine ⟨x, x.2, ?_, ?_⟩
  · have := pow_orderOf_eq_one x
    rw [hx] at this
    simpa using congrArg Subtype.val this
  · intro hall
    have hxc : x ∈ center ↥L := Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hall g g.2)
    have h3 : orderOf (⟨x, hxc⟩ : center ↥L) ∣ Nat.card (center ↥L) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hx, hZ] at h3
    omega


variable {G : Type} [Group G] [Finite G] {z : G}

theorem g2_three_case {k : Kind} {S : Subgroup G} (ctx : Stage2Ctx G z k S) (hg : Stage1G2 G z S)
    (hnb : ¬ G2Big z S) (𝒦 : Subgroup (CentralizerBar z)) [𝒦.Normal] (hdet : HDet z 𝒦) :
    ∀ c ∈ LBar z, (∃ a : ℕ, orderOf c = 2 ^ a) → c ∈ 𝒦 := by
  obtain ⟨U, hUS, h4, hnorm⟩ := exists_normal_four_S ctx
  have hUL : U ≤ LC z := hg.base.four_le U hUS h4 hnorm
  have hUC : U ≤ Cen z := hUL.trans (LC_le_Cen z)
  obtain ⟨r₁, r₂, L₁, L₂, hsh⟩ := hg.shape
  have hsh' := hsh
  obtain ⟨hodd₁, hodd₂, hgt₁, hprod, m₁, m₂, -⟩ := hsh
  have hr₂le : r₂ ≤ 3 := by
    by_contra hcon
    exact hnb ⟨r₁, r₂, L₁, L₂, by omega, hsh'⟩
  have hr₂ge : 2 ≤ r₂ := by
    obtain ⟨F, hF, hFin, hq, -⟩ := m₂
    have : 1 < Nat.card F := Finite.one_lt_card
    have hq' : Nat.card F = r₂ := hq
    omega
  have hr₂ : r₂ = 3 := by
    have := Nat.odd_iff.mp hodd₂
    omega
  subst hr₂
  obtain ⟨hq₁, hZ₁, hinv₁⟩ := sl2_model_facts hodd₁ (by omega) m₁
  obtain ⟨hZ₂, hinv₂⟩ := sl2_model_center_inv hodd₂ m₂
  obtain ⟨hsup, hcomm, hcard⟩ := hprod
  have hcomm' : ∀ a ∈ L₂, ∀ b ∈ L₁, a * b = b * a := fun a ha b hb => (hcomm b hb a ha).symm
  have hinf : Nat.card ↥(L₂ ⊓ L₁) = 2 := by rwa [inf_comm]
  have h4bar := isFour_barOf z hUC h4
  have hUle : barOf z U ≤ L₁ ⊔ L₂ := by rw [hsup]; exact barOf_le_LBar hUL
  have hUsq : ∀ v ∈ barOf z U, v ^ 2 ∈ 𝒦 := by
    intro v hv
    have : IsElementaryAbelian 2 ↥(barOf z U) := h4bar.1
    rw [elemPow_eq_one_of_isElementaryAbelian v hv]
    exact 𝒦.one_mem
  have hL₁ : L₁ ≤ ⁅(⊤ : Subgroup (CentralizerBar z)), barOf z U⁆ :=
    le_commutator_top_of_two_comps hq₁ hcomm
      (fun a ha hc => central_mem_of_card_inf hcomm hZ₁ hcard ha hc) hinv₂ h4bar hUle
  have hK₁ : L₁ ≤ 𝒦 := hL₁.trans (commutator_top_le_of_hdet hdet (barOf_le_LBar hUL)
    (isFour_orderOf h4bar) hUsq)
  have hZ₂K : ∀ b ∈ L₂, (∀ g ∈ L₂, g * b = b * g) → b ∈ 𝒦 := fun b hb hc =>
    hK₁ (central_mem_of_card_inf hcomm' hZ₂ hinf hb hc)
  have hL₂le : L₂ ≤ LBar z := by rw [← hsup]; exact le_sup_right
  have hb₂ : ∀ b ∈ L₂, b ^ 8 = 1 → b ∈ 𝒦 := by
    intro b hb hb8
    obtain ⟨l, hlL, hl3, hlnc⟩ := exists_order_three m₂ hZ₂
    have hl3c : ∀ g ∈ L₂, g * l ^ 3 = l ^ 3 * g := by
      intro g _
      rw [hl3]
      simp
    have hbord : ∃ a : ℕ, orderOf b = 2 ^ a := by
      obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
        (show orderOf b ∣ 2 ^ 3 from orderOf_dvd_of_pow_eq_one hb8)
      exact ⟨a, ha⟩
    have hb2K : b ^ 2 ∈ 𝒦 :=
      hZ₂K (b ^ 2) (L₂.pow_mem hb 2) (sq_central_of_pow_eight m₂ hb hb8)
    have hcb := hdet b (hL₂le hb) hbord hb2K
    have hcl : ∀ l' : CentralizerBar z, ⁅l', b⁆ ∈ 𝒦 := fun l' => by
      rw [← commutatorElement_inv]
      exact 𝒦.inv_mem (hcb l')
    rcases sl2_three_key' m₂ l hlL hl3c hlnc b hb hb8 with hcen | ⟨s, hsL, hsc, hbs | hbs⟩
    · exact hZ₂K b hb hcen
    · rw [hbs]
      exact 𝒦.mul_mem (hZ₂K s hsL hsc) (Normal.conj_mem inferInstance _ (hcl l) l)
    · rw [hbs]
      exact 𝒦.mul_mem (hZ₂K s hsL hsc) (Normal.conj_mem' inferInstance _ (hcl l⁻¹) l)
  intro c hc ⟨e, he⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm (hsup ▸ hc)
  have hab : (a * b) ^ (2 ^ e) = 1 := by rw [← he]; exact pow_orderOf_eq_one _
  have hb8 : b ^ 8 = 1 := by
    have h1 : a ^ (2 ^ e) * b ^ (2 ^ e) = 1 := by
      rw [← (show Commute a b from hcomm a ha b hb).mul_pow]
      exact hab
    have h2 : b ^ (2 ^ e) = (a ^ (2 ^ e))⁻¹ := eq_inv_of_mul_eq_one_right h1
    have h3 : b ^ (2 ^ e) ∈ L₁ ⊓ L₂ :=
      ⟨by rw [h2]; exact L₁.inv_mem (L₁.pow_mem ha _), L₂.pow_mem hb _⟩
    have h4' : (b ^ (2 ^ e)) ^ 2 = 1 := by
      have := pow_card_eq_one' (G := ↥(L₁ ⊓ L₂)) (x := ⟨b ^ (2 ^ e), h3⟩)
      rw [hcard] at this
      exact congrArg Subtype.val this
    have h5 : b ^ (2 ^ (e + 1)) = 1 := by
      rw [pow_succ, pow_mul]
      exact h4'
    have := pow_eight_of_two_pow (card_eq_of_hasSL2Model_three m₂) (⟨b, hb⟩ : ↥L₂)
      ⟨e + 1, Subtype.ext (by simpa using h5)⟩
    simpa using congrArg Subtype.val this
  exact 𝒦.mul_mem (hK₁ ha) (hb₂ b hb hb8)

end G2Three

section M12

theorem q8_sq_central : ∀ x g : QuaternionGroup 2, g * x ^ 2 = x ^ 2 * g := by decide

theorem sq_central_of_q8 {Y : Type} [Group Y] {A : Subgroup Y}
    (hA : Nonempty (↥A ≃* QuaternionGroup 2)) {x g : Y} (hx : x ∈ A) (hg : g ∈ A) :
    g * x ^ 2 = x ^ 2 * g := by
  obtain ⟨φ⟩ := hA
  have h1 := q8_sq_central (φ ⟨x, hx⟩) (φ ⟨g, hg⟩)
  have h2 : (⟨g, hg⟩ : ↥A) * ⟨x, hx⟩ ^ 2 = ⟨x, hx⟩ ^ 2 * ⟨g, hg⟩ :=
    φ.injective (by rw [map_mul, map_mul, map_pow]; exact h1)
  exact congrArg Subtype.val h2

variable {G : Type} [Group G] [Finite G] {z : G}

theorem m12_case {k : Kind} {S : Subgroup G} (ctx : Stage2Ctx G z k S) (hM : Stage1M12 G z S)
    (𝒦 : Subgroup (CentralizerBar z)) [𝒦.Normal]
    (hz : toBar z ⟨z, mem_Cen_self z⟩ ∈ 𝒦) (hdet : HDet z 𝒦) :
    ∀ c ∈ LBar z, (∃ a : ℕ, orderOf c = 2 ^ a) → c ∈ 𝒦 := by
  obtain ⟨A, B, hprod, hAq, hBq, -⟩ := hM.W_shape
  obtain ⟨A', ⟨eA'⟩, hLeq, hresW, hFst, hWA, -⟩ := hM.L_shape
  have hprod' := hprod
  obtain ⟨hsup, hcommAB, -⟩ := hprod
  obtain ⟨ζ, hζA, hζB, hζ1, hζsq, hAB, -, hcen', -⟩ := q8_central_product hprod' hAq hBq
  obtain ⟨zb, hzb⟩ : ∃ zb, zb = toBar z ⟨z, mem_Cen_self z⟩ := ⟨_, rfl⟩
  have hzbc : zb ∈ center (CentralizerBar z) := hzb ▸ toBar_z_mem_center z
  have hzbW : zb ∈ WBar z := by
    have := centralizer_generalizedFitting_le (CentralizerBar z)
      (Subgroup.mem_centralizer_iff.mpr fun y _ => Subgroup.mem_center_iff.mp hzbc y)
    rw [hFst] at this
    exact hzb ▸ this
  have hz2 : z ^ 2 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [ctx.orderOf_z] at this
  have hzb1 : zb ≠ 1 := by
    intro h1
    have hsq : (⟨z, mem_Cen_self z⟩ : ↥(Cen z)) ^ 2 = 1 := Subtype.ext hz2
    have := eq_one_of_toBar_eq_one z hsq (hzb ▸ h1)
    have hz1 : z = 1 := congrArg Subtype.val this
    have h2 := ctx.orderOf_z
    rw [hz1, orderOf_one] at h2
    omega
  have hzbζ : zb = ζ := by
    have := hcen' zb hzbW (fun g _ => Subgroup.mem_center_iff.mp hzbc g)
    rcases mem_zpowers_involution hζsq this with h1 | h1
    · exact absurd h1 hzb1
    · exact h1
  have hζK : ζ ∈ 𝒦 := by
    rw [← hzbζ, hzb]
    exact hz
  have hLWA : LBar z = WBar z ⊔ A' := hLeq.trans hresW
  have hWL : WBar z ≤ LBar z := hLWA ▸ le_sup_left
  have hW2 : ∀ w ∈ WBar z, ∃ a : ℕ, w ^ (2 ^ a) = 1 := WBar_two_pow z
  have hζAc : ∀ g ∈ A, g * ζ = ζ * g := fun g hg => hcommAB g hg ζ hζB
  have hζBc : ∀ g ∈ B, g * ζ = ζ * g := fun g hg => (hcommAB ζ hζA g hg).symm
  have cenA := center_q8 hAq hζA hζ1 hζAc
  have cenB := center_q8 hBq hζB hζ1 hζBc
  have hsqK : ∀ w ∈ WBar z, w ^ 2 ∈ 𝒦 := by
    intro w hw
    rw [← hsup] at hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Local.exists_mul_of_mem_sup_of_commute hcommAB hw
    rw [(show Commute a b from hcommAB a ha b hb).mul_pow]
    have h1 : a ^ 2 ∈ 𝒦 := by
      rcases cenA (a ^ 2) (A.pow_mem ha 2) (fun g hg => sq_central_of_q8 hAq ha hg) with h | h
      · rw [h]; exact 𝒦.one_mem
      · rw [h]; exact hζK
    have h2 : b ^ 2 ∈ 𝒦 := by
      rcases cenB (b ^ 2) (B.pow_mem hb 2) (fun g hg => sq_central_of_q8 hBq hb hg) with h | h
      · rw [h]; exact 𝒦.one_mem
      · rw [h]; exact hζK
    exact 𝒦.mul_mem h1 h2
  have hord2 : ∀ w ∈ WBar z, ∃ a : ℕ, orderOf w = 2 ^ a := by
    intro w hw
    obtain ⟨a, ha⟩ := hW2 w hw
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one ha)
    exact ⟨j, hj⟩
  have hWK : WBar z ≤ 𝒦 := by
    rw [← hWA]
    refine Subgroup.commutator_le.mpr fun w hw a _ => ?_
    exact hdet w (hWL hw) (hord2 w hw) (hsqK w hw) a
  have hA3 : ∀ a ∈ A', a ^ 3 = 1 := by
    have hcardA' : Nat.card ↥A' = 3 := by
      rw [Nat.card_congr eA'.toEquiv, Nat.card_eq_fintype_card]
      simp
    intro a ha
    have := pow_card_eq_one' (G := ↥A') (x := ⟨a, ha⟩)
    rw [hcardA'] at this
    exact congrArg Subtype.val this
  intro c hc ⟨e, he⟩
  rw [hLWA] at hc
  have hWn : (WBar z).Normal := WBar_normal z
  obtain ⟨w, hw, a, ha, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hc
  have hce : (w * a) ^ (2 ^ e) = 1 := by rw [← he]; exact pow_orderOf_eq_one _
  have haW : a ∈ WBar z := by
    have h1 : orderOf (QuotientGroup.mk' (WBar z) a) ∣ 3 :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hA3 a ha, map_one])
    have h2 : orderOf (QuotientGroup.mk' (WBar z) a) ∣ 2 ^ e := by
      refine orderOf_dvd_of_pow_eq_one ?_
      have hw1 : QuotientGroup.mk' (WBar z) w = 1 := (QuotientGroup.eq_one_iff w).mpr hw
      have : QuotientGroup.mk' (WBar z) (w * a) = QuotientGroup.mk' (WBar z) a := by
        rw [map_mul, hw1, one_mul]
      rw [← this, ← map_pow, hce, map_one]
    have h3 : Nat.Coprime 3 (2 ^ e) := Nat.Coprime.pow_right e (by norm_num)
    have h4 := Nat.eq_one_of_dvd_coprimes h3 h1 h2
    exact (QuotientGroup.eq_one_iff a).mp (orderOf_eq_one_iff.mp h4)
  exact 𝒦.mul_mem (hWK hw) (hWK haW)

end M12

theorem twoElt_mem_of_hdet {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}
    (ctx : Stage2Ctx G z k S) (𝒦 : Subgroup (CentralizerBar z)) [𝒦.Normal]
    (hz : toBar z ⟨z, mem_Cen_self z⟩ ∈ 𝒦) (hdet : HDet z 𝒦) :
    ∀ c ∈ LBar z, (∃ a : ℕ, orderOf c = 2 ^ a) → c ∈ 𝒦 := by
  by_cases hr : k = Kind.m12 ∨ (k = Kind.g2 ∧ ¬ G2Big z S)
  · have hd := ctx.data
    rcases hr with hm | ⟨hg2, hnb⟩
    · subst hm
      cases hd with
      | m12 hM => exact m12_case ctx hM 𝒦 hz hdet
    · subst hg2
      cases hd with
      | g2 hg => exact g2_three_case ctx hg hnb 𝒦 hdet
  · intro c hc _
    exact generic_case ctx hr 𝒦 hdet hc


end CFSG.GH74.GLS.Stage2.Final.Thm4.L192
