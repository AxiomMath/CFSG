module

public import CFSG.HardMathSupport.Curtis.Proving.OddLiftOrder
public import CFSG.HardMathSupport.Curtis.Proving.OddLiftCentralisesBlockU
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs

public section

namespace CFSG.HardMathSupport.Curtis.Proving

open CFSG.QuasithinUnique CFSG.AGLEmbedding

theorem commutator_inf_centre_of_step_i {G : Type} [Group G] [Finite G] {M L Q : Subgroup G}
    (hML : IsTwoPrimeComponent M L) (hL : IsShort2 L) (_hQM : Q ≤ M) (hQ3 : IsPGroup 3 ↥Q)
    (_hQN : Q ≤ Subgroup.normalizer (L : Set G))
    (_hcent : barM M Q ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hstep : ∀ t : ↥L, Odd (orderOf (t : G)) →
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) (⟨(t : G), hML.le t.2⟩ : ↥M) ∈
        ⁅barM M Q, barM M Q⁆ →
      ⁅blockU L, Subgroup.zpowers (t : G)⁆ ≤ blockZ L) :
    ⁅barM M Q, barM M Q⁆ ⊓
      (barM M L ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hzc, hzL, -⟩
  let φ : ↥L →* (↥M ⧸ CFSG.pCore 2 ↥M) :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hML.le)
  have hzQ : z ∈ barM M Q := Subgroup.commutator_le_of_le le_rfl le_rfl hzc
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hzQ
  obtain ⟨k, hk⟩ := hQ3 ⟨(w : G), (Subgroup.mem_subgroupOf).1 hw⟩
  have hwpow : w ^ (3 ^ k) = 1 := Subtype.ext (by
    have := congrArg Subtype.val hk
    simpa using this)
  have hzpow : (QuotientGroup.mk' (CFSG.pCore 2 ↥M) w) ^ (3 ^ k) = 1 := by
    rw [← map_pow, hwpow, map_one]
  obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.1 hzL
  let l : ↥L := ⟨(y : G), (Subgroup.mem_subgroupOf).1 hy⟩
  have hφl : φ l = QuotientGroup.mk' (CFSG.pCore 2 ↥M) w := hyz
  have hr : Odd (3 ^ k) := Odd.pow (by decide)
  obtain ⟨t, hφt, hodd⟩ := exists_odd_order_lift φ l hr (by rw [hφl]; exact hzpow)
  have hodd' : Odd (orderOf (t : G)) := by
    rw [Subgroup.orderOf_coe]
    exact hodd
  have hcomm : (QuotientGroup.mk' (CFSG.pCore 2 ↥M) (⟨(t : G), hML.le t.2⟩ : ↥M)) ∈
      ⁅barM M Q, barM M Q⁆ := by
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (⟨(t : G), hML.le t.2⟩ : ↥M) =
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) w := hφt.trans hφl
    rw [h1]
    exact hzc
  have htriv := hstep t hodd' hcomm
  have ht1 : (t : G) = 1 := eq_one_of_odd_mod_blockZ hL t.2 hodd' htriv
  have ht_one : t = 1 := Subtype.ext ht1
  rw [Subgroup.mem_bot, ← hφl, ← hφt, ht_one, map_one]

end CFSG.HardMathSupport.Curtis.Proving

end
