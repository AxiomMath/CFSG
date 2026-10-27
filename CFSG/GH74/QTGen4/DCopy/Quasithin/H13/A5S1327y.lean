module

public import CFSG.Quasithin.H13.A5S1327y
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1327q

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.S14110
open CFSG.LieType.BorelTits
open scoped commutatorElement

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem false_of_pCoreOf_le_UH_F4 (h331 : Stmt3_3_1_F4)
    (h1222 : Stmt12_2_2_F4) (h5172 : Stmt5_1_7_two_F4) (h1332 : Stmt13_3_2_F4)
    (h137 : EmptyFaithfulMultiple.Input137) (h1391 : Theorem1391Statement) {H : Subgroup G}
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hsolv : Group.IsSolvable ↥H) (hS3 : ¬ Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3)))
    {hU : IsElemAbelian 2 (S.UH H)} {K₁ K₂ : Subgroup (MulAut (IntMod (S.UH H) hU))}
    (B : TwoBlocks hU H T K₁ K₂) (htop : commV K₁ ⊔ commV K₂ = ⊤)
    (hcent : T ⊓ Subgroup.centralizer (oTwoUpper H : Set G) = ⊥)
    (hR : pCoreOf 2 H ≤ S.UH H) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ H := hH.1.1
  have hUH : (S.UH H) ≤ H := conjClosure_le fun h hh z hz =>
    H.mul_mem (H.mul_mem hh (hTH (mem_quasithinOmegaOneCenter_iff.mp hz).1)) (H.inv_mem hh)
  have hCU : H ⊓ Subgroup.centralizer ((S.UH H) : Set G) ≤ (S.UH H) :=
    (S.centralizer_UH_le_pCoreOf_all_F4 h331 h1222 h5172 hH hHZ hsolv).trans hR
  have hHN : H ≤ Subgroup.normalizer ((S.UH H) : Set G) := B.le_norm
  have hU2 : IsPGroup 2 ↥(S.UH H) := fun g => ⟨1, Subtype.ext (by simpa using hU.2 g g.2)⟩
  have B' := B.symm
  have htop' : commV K₂ ⊔ commV K₁ = ⊤ := by rw [sup_comm]; exact htop

  obtain ⟨c₁, hc₁L, hc₁N, hc₁3, hc₁K, hc₁1⟩ := B.exists_c hCU
  set X₁ := blk hU K₁ ⊔ Subgroup.zpowers c₁ with hX₁def
  have hX₁ : A4Data X₁ (blk hU K₁) c₁ := B.a4Data hc₁N hc₁3 hc₁K hc₁1
  have hX₁L : X₁ ≤ twoResidual H := B.blockX_le_twoResidual hUH hc₁L hc₁N hc₁3 hc₁K hc₁1
  have hc₁H : c₁ ∈ H := twoResidual_le H hc₁L

  obtain ⟨t, htT, ht⟩ := B.swap
  obtain ⟨t₀, ht₀T, rfl⟩ := (mem_autI hU).1 htT
  have ht₀H : (t₀ : G) ∈ H := hTH ht₀T
  set c₂ := (t₀ : G) * c₁ * (t₀ : G)⁻¹ with hc₂def
  have hc₂N : c₂ ∈ Subgroup.normalizer ((S.UH H) : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ t₀.2 hc₁N) (Subgroup.inv_mem _ t₀.2)
  have hc₂v : convI hU ⟨c₂, hc₂N⟩ = convI hU t₀ * convI hU ⟨c₁, hc₁N⟩ * (convI hU t₀)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]; rfl
  have hc₂K : convI hU ⟨c₂, hc₂N⟩ ∈ K₂ := by
    rw [hc₂v, ← ht, B1.mem_conjAut]
    simpa [mul_assoc] using hc₁K
  have hc₂1 : convI hU ⟨c₂, hc₂N⟩ ≠ 1 := by
    rw [hc₂v]
    intro h
    apply hc₁1
    have e : convI hU ⟨c₁, hc₁N⟩ = (convI hU t₀)⁻¹ *
        (convI hU t₀ * convI hU ⟨c₁, hc₁N⟩ * (convI hU t₀)⁻¹) * convI hU t₀ := by group
    rw [e, h]; group
  have hc₂3 : c₂ ^ 3 = 1 := by rw [hc₂def, conj_pow, hc₁3]; group
  have hc₂L : c₂ ∈ twoResidual H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_twoResidual H ht₀H) c₁).mp hc₁L
  have hc₂H : c₂ ∈ H := twoResidual_le H hc₂L
  set X₂ := blk hU K₂ ⊔ Subgroup.zpowers c₂ with hX₂def
  have hX₂L : X₂ ≤ twoResidual H := B'.blockX_le_twoResidual hUH hc₂L hc₂N hc₂3 hc₂K hc₂1
  have hcjX : cj (t₀ : G) X₁ = X₂ := by
    unfold cj
    rw [hX₁def, Subgroup.map_sup, MonoidHom.map_zpowers]
    have h1 := TwoBlocks.cj_blk t₀.2 ht
    unfold cj at h1
    rw [h1]
    rfl
  have hX₂ : A4Data (cj (t₀ : G) X₁) ((blk hU K₁).map (MulAut.conj (t₀ : G)).toMonoidHom)
      (MulAut.conj (t₀ : G) c₁) := hX₁.map (MulAut.conj (t₀ : G))

  have hX12 : ∀ g ∈ X₁, g ∈ X₂ → g = 1 := by
    intro g hg1 hg2
    have hgH : g ∈ H := twoResidual_le H (hX₁L hg1)
    have hgN := hHN hgH
    have h1 := TwoBlocks.convI_mem_of_mem_blockX hc₁N hc₁K hg1 hgN
    have h2 := TwoBlocks.convI_mem_of_mem_blockX hc₂N hc₂K hg2 hgN
    have h3 : convI hU ⟨g, hgN⟩ ∈ K₁ ⊓ K₂ := ⟨h1, h2⟩
    rw [B.inf, Subgroup.mem_bot] at h3
    have hgU : g ∈ (S.UH H) := hCU ⟨hgH, (convI_eq_one_iff hU _).1 h3⟩
    obtain ⟨hgU₁, hgK₁⟩ := mem_blk.1 (TwoBlocks.mem_blk_of_mem_blockX hc₁N hc₁3 hc₁K hg1 hgU)
    obtain ⟨hgU₂, hgK₂⟩ := mem_blk.1 (TwoBlocks.mem_blk_of_mem_blockX hc₂N hc₂3 hc₂K hg2 hgU)
    have h4 : IntMod.mk hU ⟨g, hgU⟩ ∈ commV K₁ ⊓ commV K₂ := ⟨hgK₁, hgK₂⟩
    rw [B.commV_inf, Subgroup.mem_bot] at h4
    exact congrArg IntMod.val h4

  have hK1K12 : convI hU ⟨c₁, hc₁N⟩ ∈ K₂ ⊔ K₁ := Subgroup.mem_sup_right hc₁K
  have hK2K12 : convI hU ⟨c₂, hc₂N⟩ ∈ K₁ ⊔ K₂ := Subgroup.mem_sup_right hc₂K
  have hc₁c₂ : c₁ * c₂ = c₂ * c₁ := by
    have h1 : c₁ * c₂ * c₁⁻¹ ∈ X₂ :=
      B'.conj_mem_blockX_of htop' hCU hc₂L hc₂N hc₂3 hc₂K hc₂1 hc₁H hc₁N
        (B'.conjAut_K1 hK1K12) (Subgroup.mem_sup_right (Subgroup.mem_zpowers c₂))
    have h2 : c₂ * c₁⁻¹ * c₂⁻¹ ∈ X₁ :=
      B.conj_mem_blockX_of htop hCU hc₁L hc₁N hc₁3 hc₁K hc₁1 hc₂H hc₂N
        (B.conjAut_K1 hK2K12) (Subgroup.inv_mem _ (Subgroup.mem_sup_right
          (Subgroup.mem_zpowers c₁)))
    have h3 : c₁ * c₂ * c₁⁻¹ * c₂⁻¹ ∈ X₁ := by
      have e : c₁ * c₂ * c₁⁻¹ * c₂⁻¹ = c₁ * (c₂ * c₁⁻¹ * c₂⁻¹) := by group
      rw [e]; exact X₁.mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers c₁)) h2
    have h4 : c₁ * c₂ * c₁⁻¹ * c₂⁻¹ ∈ X₂ :=
      X₂.mul_mem h1 (X₂.inv_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers c₂)))
    have h5 := hX12 _ h3 h4
    calc c₁ * c₂ = (c₁ * c₂ * c₁⁻¹ * c₂⁻¹) * (c₂ * c₁) := by group
      _ = c₂ * c₁ := by rw [h5, one_mul]

  have hcomm : ∀ x ∈ X₁, ∀ y ∈ cj (t₀ : G) X₁, x * y = y * x := by
    intro x hx y hy
    rw [hcjX] at hy
    obtain ⟨w₁, hw₁, a, rfl⟩ := (TwoBlocks.mem_sup_zpowers_iff
      (TwoBlocks.mem_normalizer_blk hc₁N hc₁K)).1 hx
    obtain ⟨w₂, hw₂, b, rfl⟩ := (TwoBlocks.mem_sup_zpowers_iff
      (TwoBlocks.mem_normalizer_blk hc₂N hc₂K)).1 hy
    obtain ⟨hw₁U, hw₁K⟩ := mem_blk.1 hw₁
    obtain ⟨hw₂U, hw₂K⟩ := mem_blk.1 hw₂
    have hww : Commute w₁ w₂ := B2F.isElemAbelian_comm hU hw₁U hw₂U
    have hcw₂ : Commute c₁ w₂ := by
      have h1 : convI hU ⟨c₁, hc₁N⟩ (IntMod.mk hU ⟨w₂, hw₂U⟩) = IntMod.mk hU ⟨w₂, hw₂U⟩ :=
        B.apply_eq₁ hc₁K hw₂K
      have h2 := congrArg IntMod.val h1
      rw [convI_apply_val] at h2
      have h3 : c₁ * w₂ * c₁⁻¹ = w₂ := h2
      show c₁ * w₂ = w₂ * c₁
      calc c₁ * w₂ = (c₁ * w₂ * c₁⁻¹) * c₁ := by group
        _ = w₂ * c₁ := by rw [h3]
    have hcw₁ : Commute c₂ w₁ := by
      have h1 : convI hU ⟨c₂, hc₂N⟩ (IntMod.mk hU ⟨w₁, hw₁U⟩) = IntMod.mk hU ⟨w₁, hw₁U⟩ :=
        B.apply_eq₂ hc₂K hw₁K
      have h2 := congrArg IntMod.val h1
      rw [convI_apply_val] at h2
      have h3 : c₂ * w₁ * c₂⁻¹ = w₁ := h2
      show c₂ * w₁ = w₁ * c₂
      calc c₂ * w₁ = (c₂ * w₁ * c₂⁻¹) * c₂ := by group
        _ = w₁ * c₂ := by rw [h3]
    have hcc : Commute c₁ c₂ := hc₁c₂
    have h1 : Commute (w₁ * c₁ ^ a) w₂ := Commute.mul_left hww (hcw₂.zpow_left a)
    have h2 : Commute (w₁ * c₁ ^ a) (c₂ ^ b) :=
      Commute.mul_left (hcw₁.symm.zpow_right b) ((hcc.zpow_left a).zpow_right b)
    exact Commute.mul_right h1 h2

  have hUX : (S.UH H) ≤ X₁ ⊔ X₂ :=
    (TwoBlocks.le_blk_sup htop).trans (sup_le_sup le_sup_left le_sup_left)
  have hX12L : X₁ ⊔ X₂ = twoResidual H := by
    refine le_antisymm (sup_le hX₁L hX₂L) fun x hx => ?_
    have hxH : x ∈ H := twoResidual_le H hx
    have hxN := hHN hxH
    have hφ3 : ∀ (d : G) (hd : d ∈ Subgroup.normalizer ((S.UH H) : Set G)), d ^ 3 = 1 →
        convI hU ⟨d, hd⟩ ^ 3 = 1 := fun d hd hd3 => by
      rw [← map_pow]
      have : (⟨d, hd⟩ : ↥(Subgroup.normalizer ((S.UH H) : Set G))) ^ 3 = 1 := Subtype.ext hd3
      rw [this, map_one]
    have hL := B.autI_twoResidual_eq hc₁K (hφ3 c₁ hc₁N hc₁3) hc₁1 hc₂K (hφ3 c₂ hc₂N hc₂3) hc₂1
    have hxL : convI hU ⟨x, hxN⟩ ∈ autI hU (twoResidual H) := convI_mem_autI hU hx hxN
    rw [hL] at hxL
    have hcz : ∀ a ∈ Subgroup.zpowers (convI hU ⟨c₁, hc₁N⟩),
        ∀ b ∈ Subgroup.zpowers (convI hU ⟨c₂, hc₂N⟩), a * b = b * a := fun a ha b hb =>
      B.comm a ((Subgroup.zpowers_le).2 hc₁K ha) b ((Subgroup.zpowers_le).2 hc₂K hb)
    obtain ⟨p, ⟨i, rfl⟩, q, ⟨j, rfl⟩, hpq⟩ := S1417.exists_mul_of_mem_sup_of_commute hcz hxL
    have hdN : c₁ ^ i * c₂ ^ j ∈ Subgroup.normalizer ((S.UH H) : Set G) :=
      Subgroup.mul_mem _ (Subgroup.zpow_mem _ hc₁N i) (Subgroup.zpow_mem _ hc₂N j)
    have hdv : convI hU ⟨c₁ ^ i * c₂ ^ j, hdN⟩ =
        convI hU ⟨c₁, hc₁N⟩ ^ i * convI hU ⟨c₂, hc₂N⟩ ^ j := by
      rw [← map_zpow, ← map_zpow, ← map_mul]; rfl
    have huN : x * (c₁ ^ i * c₂ ^ j)⁻¹ ∈ Subgroup.normalizer ((S.UH H) : Set G) :=
      Subgroup.mul_mem _ hxN (Subgroup.inv_mem _ hdN)
    have huv : convI hU ⟨x * (c₁ ^ i * c₂ ^ j)⁻¹, huN⟩ = 1 := by
      rw [show (⟨x * (c₁ ^ i * c₂ ^ j)⁻¹, huN⟩ : ↥(Subgroup.normalizer ((S.UH H) : Set G))) =
        ⟨x, hxN⟩ * (⟨c₁ ^ i * c₂ ^ j, hdN⟩)⁻¹ from rfl, map_mul, map_inv, hdv, hpq,
        mul_inv_cancel]
    have huU : x * (c₁ ^ i * c₂ ^ j)⁻¹ ∈ (S.UH H) := hCU ⟨H.mul_mem hxH (H.inv_mem (H.mul_mem
      (H.zpow_mem hc₁H i) (H.zpow_mem hc₂H j))), (convI_eq_one_iff hU _).1 huv⟩
    have e : x = (x * (c₁ ^ i * c₂ ^ j)⁻¹) * c₁ ^ i * c₂ ^ j := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hUX huU)
      (Subgroup.mem_sup_left (Subgroup.zpow_mem _ (Subgroup.mem_sup_right
        (Subgroup.mem_zpowers c₁)) i)))
      (Subgroup.mem_sup_right (Subgroup.zpow_mem _ (Subgroup.mem_sup_right
        (Subgroup.mem_zpowers c₂)) j))

  set M₁ := Subgroup.normalizer (oTwoUpper H : Set G) with hM₁def
  have hXi := S.isXiStar_oTwoUpper_F4 h331 h1222 h5172 h1332 hH hHZ hsolv hS3
  have hUq := h137 G T S.h13.simple S.h13.nonabelian S.h13.qtke S.h13.sylow _ hXi
  have hM₁max : quasithinIsMaxTwoLocal M₁ := hUq.1.1
  have hTM₁ : T ≤ M₁ := le_sup_right.trans hUq.1.2
  have hHM₁ : H ≤ M₁ := le_normalizer_oTwoUpper H
  have hLH : oTwoUpper H = twoResidual H := (twoResidual_eq_oTwoUpper' H).symm

  have hOU : pCoreOf 2 (oTwoUpper H) = (S.UH H) := by
    apply le_antisymm
    · refine le_trans ?_ hR
      refine le_pCoreOf_of_le_normalizer ((pCoreOf_le 2 _).trans (oTwoUpper_le H)) ?_
        (pCoreOf_isPGroup 2 _)
      exact (le_normalizer_oTwoUpper H).trans (normalizer_le_normalizer_pCoreOf 2 _)
    · refine le_pCoreOf_of_le_normalizer ?_ ((oTwoUpper_le H).trans hHN) hU2
      rw [hLH, ← hX12L]; exact hUX
  have hM₁U : M₁ ≤ Subgroup.normalizer ((S.UH H) : Set G) := by
    rw [← hOU]; exact normalizer_le_normalizer_pCoreOf 2 _
  have hQ : pCoreOf 2 M₁ = (S.UH H) := by
    apply le_antisymm
    · refine le_trans ?_ hR
      refine le_pCoreOf_of_le_normalizer ?_ (hHM₁.trans (le_normalizer_pCoreOf 2 M₁))
        (pCoreOf_isPGroup 2 _)
      exact (pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_le S.h13.sylow hTM₁)).trans hTH
    · exact le_pCoreOf_of_le_normalizer (hUH.trans hHM₁) hM₁U hU2
  have hQne : pCoreOf 2 M₁ ≠ ⊥ := by
    rw [hQ]
    intro h
    have hz : S.z ∈ (S.UH H) := le_conjClosure _ _ S.z_mem_omegaOneCenter
    rw [h, Subgroup.mem_bot] at hz
    exact S.z_ne_one hz
  have hcharM : CharTwo M₁ := S.charTwo_of_inH ⟨hTM₁, hQne⟩
  have hrank : CFSG.Open.pRank 3 M₁ ≤ 2 :=
    S.pRank_le_two_of_isTwoLocal hM₁max.1 Nat.prime_three (by norm_num)
  have hX₁M₁ : X₁ ≤ M₁ := hX₁L.trans ((twoResidual_le H).trans hHM₁)

  have hX₁s : (X₁.subgroupOf M₁).IsSubnormal := by
    have hLn : ((oTwoUpper H).subgroupOf M₁).Normal := Subgroup.normal_in_normalizer
    refine Subgroup.IsSubnormal.step _ _ ?_ hLn.isSubnormal ?_
    · intro x hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      rw [hLH]; exact hX₁L hx
    · refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hn ⊢
      have hgL : ((g : ↥M₁) : G) ∈ twoResidual H := by
        rw [twoResidual_eq_oTwoUpper']
        exact Subgroup.mem_subgroupOf.mp g.2
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact B.conj_mem_blockX htop hCU hc₁L hc₁N hc₁3 hc₁K hc₁1 hgL hn

  have hne : cj (t₀ : G) X₁ ≠ X₁ := by
    rw [hcjX]
    intro h
    have hle : blk hU K₂ ≤ blk hU K₁ := by
      intro x hx
      have hxX : x ∈ X₁ := h ▸ Subgroup.mem_sup_left hx
      exact TwoBlocks.mem_blk_of_mem_blockX hc₁N hc₁3 hc₁K hxX (blk_le K₂ hx)
    have h4 : Nat.card ↥(blk hU K₂) ≤ Nat.card ↥(blk hU K₁ ⊓ blk hU K₂) :=
      Subgroup.card_le_of_le (le_inf hle le_rfl)
    have hinf : blk hU K₁ ⊓ blk hU K₂ = ⊥ := by
      refine eq_bot_iff.mpr fun g hg => ?_
      obtain ⟨hgU, hg1⟩ := mem_blk.1 hg.1
      obtain ⟨hgU', hg2⟩ := mem_blk.1 hg.2
      have h5 : IntMod.mk hU ⟨g, hgU⟩ ∈ commV K₁ ⊓ commV K₂ := ⟨hg1, hg2⟩
      rw [B.commV_inf, Subgroup.mem_bot] at h5
      exact Subgroup.mem_bot.mpr (congrArg IntMod.val h5)
    rw [hinf, Subgroup.card_bot, card_blk, (S1417.card_of_actsAsNaturalL2 B.nat₂).2] at h4
    omega
  have hDC : ∀ m ∈ M₁, cj m X₁ = X₁ ∨ ∀ x ∈ X₁, ∀ y ∈ cj m X₁, x * y = y * x := fun m hm =>
    (commute_or_eq_of_isSubnormal hcharM hX₁M₁ (cj_le hX₁M₁ hm) hX₁s (isSubnormal_cj hX₁s hm)
      hX₁ (hX₁.map (MulAut.conj m))).imp_left Eq.symm
  have hTC : TwoConj M₁ X₁ (cj (t₀ : G) X₁) :=
    ⟨hne, ⟨t₀, hTM₁ ht₀T, rfl⟩, two_conj hX₁ hX₁M₁ hDC hrank (hTM₁ ht₀T) hne⟩

  have hJH := (E2_3_two_sylow_of_isSolvable hU (S.hyp501.minParabolic_of_isHStar_F4 h331 hH).1
    hsolv (fun p hp hp2 => by
      obtain ⟨-, hq⟩ := isSQTKSub_of_inH S.h13.qtke S.h13.simple S.h13.nonabelian hH.1
      have : Fact p.Prime := ⟨hp⟩
      have h1 := hq p hp hp2
      rwa [← pRank_top_subtype]) (conjClosure_isTwoReducedIn_of_charTwo
        (isSylowTwoOf_of_le S.h13.sylow hTH) (S.charTwo_of_inH hH.1) le_rfl).2.2
    (S.thompsonJ_not_le_centralizer_UH_F4 h331 h5172 hH hHZ)).2
  rw [B.eqJ] at hJH
  have hJK : autI hU (thompsonJ T) ≤ K₁ ⊔ K₂ := hJH.1
  have hJnorm : ∀ j ∈ thompsonJ T, ∀ x ∈ X₁, j * x * j⁻¹ ∈ X₁ := by
    intro j hj x hx
    have hjH : j ∈ H := hTH (thompsonJ_le_self T hj)
    have hjN := hHN hjH
    exact B.conj_mem_blockX_of htop hCU hc₁L hc₁N hc₁3 hc₁K hc₁1 hjH hjN
      (B.conjAut_K1 (hJK (convI_mem_autI hU hj hjN))) hx
  have hJle : ⁅X₁, thompsonJ T⁆ ≤ X₁ := by
    refine Subgroup.commutator_le.2 fun x hx j hj => ?_
    rw [commutatorElement_def]
    have e : x * j * x⁻¹ * j⁻¹ = x * (j * x⁻¹ * j⁻¹) := by group
    rw [e]
    exact X₁.mul_mem hx (hJnorm j hj _ (X₁.inv_mem hx))

  obtain ⟨s₁, s₂, a₁, a₂, hd⟩ :=
    S1417.exists_sylowData hJH B.nat₁ B.nat₂ B.comm B.inf B.commV_inf htop
  have hs₁sq : s₁ ^ 2 = 1 := by
    rcases hd.inf₁ (s₁ ^ 2) (Subgroup.pow_mem _ hd.s₁_mem_S 2) (K₁.pow_mem hd.s₁_mem_L 2) with
      h | h
    · exact h
    · exfalso
      apply hd.s₁_ne
      have : s₁ * s₁ = s₁ * 1 := by rw [← sq, h, mul_one]
      exact mul_left_cancel this
  obtain ⟨j₁, hj₁J, hj₁⟩ := (mem_autI hU).1 hd.s₁_mem_S
  have hnc : s₁ * convI hU ⟨c₁, hc₁N⟩ ≠ convI hU ⟨c₁, hc₁N⟩ * s₁ := by
    obtain ⟨e, -, -⟩ := B.nat₁
    have hc₁3' : convI hU ⟨c₁, hc₁N⟩ ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨c₁, hc₁N⟩ : ↥(Subgroup.normalizer ((S.UH H) : Set G))) ^ 3 = 1 := Subtype.ext hc₁3
      rw [this, map_one]
    intro h
    refine SL2_inv_comm_cube (e ⟨s₁, hd.s₁_mem_L⟩) (e ⟨_, hc₁K⟩) ⟨?_, ?_, ?_, ?_⟩ ?_
    · rw [← map_pow]
      have : (⟨s₁, hd.s₁_mem_L⟩ : ↥K₁) ^ 2 = 1 := Subtype.ext hs₁sq
      rw [this, map_one]
    · intro h1
      apply hd.s₁_ne
      have := congrArg Subtype.val ((map_eq_one_iff e e.injective).mp h1)
      exact this
    · rw [← map_pow]
      have : (⟨_, hc₁K⟩ : ↥K₁) ^ 3 = 1 := Subtype.ext hc₁3'
      rw [this, map_one]
    · intro h1
      apply hc₁1
      exact congrArg Subtype.val ((map_eq_one_iff e e.injective).mp h1)
    · rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext h
  have hJ : ⁅X₁, thompsonJ T⁆ = X₁ := by
    refine le_antisymm hJle ?_
    have hgN : ⁅c₁, (j₁ : G)⁆ ∈ ⁅X₁, thompsonJ T⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_sup_right (Subgroup.mem_zpowers c₁)) hj₁J
    refine A4Data.le_of_mem hX₁ hJle hgN ?_ fun u hu => ?_
    · intro hgW
      have hgU : ⁅c₁, (j₁ : G)⁆ ∈ (S.UH H) := blk_le K₁ hgW
      have hgN' : ⁅c₁, (j₁ : G)⁆ ∈ Subgroup.normalizer ((S.UH H) : Set G) :=
        Subgroup.le_normalizer hgU
      have h1 : convI hU ⟨⁅c₁, (j₁ : G)⁆, hgN'⟩ = 1 :=
        (convI_eq_one_iff hU _).2 (Subgroup.mem_centralizer_iff.2 fun v hv =>
          (B2F.isElemAbelian_comm hU hv hgU))
      have h2 : convI hU ⟨⁅c₁, (j₁ : G)⁆, hgN'⟩ = convI hU ⟨c₁, hc₁N⟩ * s₁ *
          (convI hU ⟨c₁, hc₁N⟩)⁻¹ * s₁⁻¹ := by
        rw [← hj₁, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
        rfl
      rw [h2] at h1
      apply hnc
      have h3 : convI hU ⟨c₁, hc₁N⟩ * s₁ * (convI hU ⟨c₁, hc₁N⟩)⁻¹ = s₁ :=
        mul_inv_eq_one.mp h1
      calc s₁ * convI hU ⟨c₁, hc₁N⟩ = (convI hU ⟨c₁, hc₁N⟩ * s₁ * (convI hU ⟨c₁, hc₁N⟩)⁻¹) *
            convI hU ⟨c₁, hc₁N⟩ := by rw [h3]
        _ = convI hU ⟨c₁, hc₁N⟩ * s₁ := by group
    · have huX : u ∈ X₁ := Subgroup.mem_sup_left hu
      have hc₁X : c₁ ∈ X₁ := Subgroup.mem_sup_right (Subgroup.mem_zpowers c₁)
      have h1 : ⁅u * c₁, (j₁ : G)⁆ ∈ ⁅X₁, thompsonJ T⁆ :=
        Subgroup.commutator_mem_commutator (X₁.mul_mem huX hc₁X) hj₁J
      have h2 : ⁅u, (j₁ : G)⁆ ∈ ⁅X₁, thompsonJ T⁆ := Subgroup.commutator_mem_commutator huX hj₁J
      have e : u * ⁅c₁, (j₁ : G)⁆ * u⁻¹ = ⁅u * c₁, (j₁ : G)⁆ * ⁅u, (j₁ : G)⁆⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)

  have hK : M₁ ⊓ Subgroup.centralizer ((X₁ ⊔ cj (t₀ : G) X₁ : Subgroup G) : Set G) = ⊥ := by
    rw [hcjX, hX12L, ← hLH]
    set K := M₁ ⊓ Subgroup.centralizer (oTwoUpper H : Set G) with hKdef
    have hKT : K ⊓ T = ⊥ := by
      rw [eq_bot_iff, ← hcent]
      exact fun x hx => ⟨hx.2, hx.1.2⟩
    have hKQ : ∀ k ∈ K, ∀ q ∈ pCoreOf 2 M₁, k * q = q * k := by
      intro k hk q hq
      have hqM : q ∈ M₁ := pCoreOf_le 2 M₁ hq
      have hkq : k * q * k⁻¹ * q⁻¹ ∈ pCoreOf 2 M₁ := by
        have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M₁ hk.1) q).mp hq
        exact Subgroup.mul_mem _ this (Subgroup.inv_mem _ hq)
      have hkq' : k * q * k⁻¹ * q⁻¹ ∈ K := by
        have h1 : q * k⁻¹ * q⁻¹ ∈ K := by
          refine ⟨M₁.mul_mem (M₁.mul_mem hqM (M₁.inv_mem hk.1)) (M₁.inv_mem hqM), ?_⟩
          have := conj_mem_centralizer_of_mem_normalizer hqM (Subgroup.inv_mem _ hk.2)
          exact this
        have e : k * q * k⁻¹ * q⁻¹ = k * (q * k⁻¹ * q⁻¹) := by group
        rw [e]; exact K.mul_mem hk h1
      have hQT : pCoreOf 2 M₁ ≤ T :=
        pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_le S.h13.sylow hTM₁)
      have h1 : k * q * k⁻¹ * q⁻¹ ∈ K ⊓ T := ⟨hkq', hQT hkq⟩
      rw [hKT, Subgroup.mem_bot] at h1
      calc k * q = (k * q * k⁻¹ * q⁻¹) * (q * k) := by group
        _ = q * k := by rw [h1, one_mul]
    refine eq_bot_iff.mpr fun k hk => ?_
    have hkC : k ∈ M₁ ⊓ Subgroup.centralizer (pCoreOf 2 M₁ : Set G) :=
      ⟨hk.1, Subgroup.mem_centralizer_iff.2 fun q hq => (hKQ k hk q hq).symm⟩
    have hkQ := hcharM hkC
    have hkT : k ∈ T := pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_le S.h13.sylow hTM₁) hkQ
    have : k ∈ K ⊓ T := ⟨hk, hkT⟩
    rwa [hKT] at this

  have hWQ : blk hU K₁ ≤ pCoreOf 2 M₁ := by rw [hQ]; exact blk_le K₁
  have hW'Q : (blk hU K₁).map (MulAut.conj (t₀ : G)).toMonoidHom ≤ pCoreOf 2 M₁ := by
    have h1 := TwoBlocks.cj_blk t₀.2 ht
    unfold cj at h1
    rw [h1, hQ]; exact blk_le K₂
  have hQR : pCoreOf 2 M₁ ≤ T :=
    pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_le S.h13.sylow hTM₁)
  have hiso := nonempty_mulEquiv_wreath_of_two_conj S.h13.sylow hTM₁ hX₁ hX₂ hTC hX₁M₁
    (cj_le hX₁M₁ (hTM₁ ht₀T)) hcomm hWQ hW'Q hQR le_rfl hJ hK
  exact h1391 G T S.h13.simple S.h13.nonabelian S.h13.qtke S.h13.sylow M₁ hM₁max hTM₁ hiso

end Setting

end CFSG.Quasithin.H13.A5
