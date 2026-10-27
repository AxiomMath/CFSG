module

public import CFSG.ClassicalInvolution.Asc77.AscQuot614Basic
public import CFSG.ClassicalInvolution.Asc77.AscSixModCent

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic
open scoped commutatorElement

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

namespace AscQuot

theorem isUniqueInvolution_map_mk {K X : Subgroup G} [X.Normal] (hKX : K ⊓ X = ⊥) {z : G}
    (hz : IsUniqueInvolution K z) :
    IsUniqueInvolution (K.map (QuotientGroup.mk' X)) (QuotientGroup.mk' X z) where
  mem := Subgroup.mem_map_of_mem _ hz.mem
  ne_one := by
    intro h
    have h1 : z ∈ X := by rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    have : z ∈ K ⊓ X := ⟨hz.mem, h1⟩
    rw [hKX, Subgroup.mem_bot] at this
    exact hz.ne_one this
  sq := by rw [← map_mul, hz.sq, map_one]
  unique := by
    rintro y ⟨k, hk, rfl⟩ hy
    have h1 : k * k ∈ X := by
      rw [← map_mul, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy
      exact hy
    have h2 : k * k ∈ K ⊓ X := ⟨K.mul_mem hk hk, h1⟩
    rw [hKX, Subgroup.mem_bot] at h2
    rcases hz.unique k hk h2 with h | h
    · left
      rw [h, map_one]
    · right
      rw [h]

theorem commutator_le_oddCoreOf_of_congr [Finite G] (hp : p ≠ 2)
    (hΩ : HypOmegaMod p f Ω) (h62 : L6_2On Ω) (X : Subgroup G)
    (hRX : ∀ R ∈ RSet Ω, Commutes R X) {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) {z t : G}
    (hz : IsUniqueInvolution K z) (ht : IsUniqueInvolution J t) (hzt' : z ≠ t)
    (hzt : t⁻¹ * z ∈ X) : ⁅J, K⁆ ≤ oddCoreOf K := by
  have hJt : J ∉ twinSet Ω K := by
    rintro ⟨-, z', hKz', hJz'⟩
    exact hzt' ((hz.eq hKz').trans (ht.eq hJz').symm)
  have hVcomm : ∀ V : Subgroup G, IsSylow2In V J → ⁅V, K⁆ ≤ oddCoreOf K := by
    intro V hV
    have hVR : V ∈ RSet Ω := mem_RSet_of_isSylow2In hJ hV
    have h8 := hΩ.eight_le_of_mem_RSet hp hVR
    have htV : t ∈ V := mem_of_uniqueInvolution ht hV.1 hV.2.1 (by omega)
    have hzx : z = t * (t⁻¹ * z) := by group
    have hVz : V ≤ Subgroup.centralizer ({z} : Set G) := by
      intro r hr
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : r * (t⁻¹ * z) = (t⁻¹ * z) * r := hRX V hVR r hr _ hzt
      have h2 : t * r = r * t := ht.commute_of_mem (hV.1 hr)
      calc r * z = r * (t * (t⁻¹ * z)) := by rw [← hzx]
        _ = (r * t) * (t⁻¹ * z) := by rw [← mul_assoc]
        _ = (t * r) * (t⁻¹ * z) := by rw [← h2]
        _ = t * (r * (t⁻¹ * z)) := by rw [mul_assoc]
        _ = t * ((t⁻¹ * z) * r) := by rw [h1]
        _ = z * r := by group
    have hVsyl : IsSylow2In V (J ⊓ Subgroup.centralizer ({z} : Set G)) :=
      ⟨le_inf hV.1 hVz, hV.2.1, fun V' hV'le hV'2 hle => hV.2.2 V' (hV'le.trans inf_le_left)
        hV'2 hle⟩
    have hnonab := (hΩ.isQuatSub_of_mem_RSet hp hVR).exists_not_commute
    rcases h62 K hK z hz J hJ hJt t ht V hVsyl htV with ⟨hVt, -⟩ | ⟨hVt, -⟩ | ⟨hVU, -⟩ |
      ⟨-, hcomm⟩
    · exfalso
      have ht2 : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht.sq) ht.ne_one
      have : Nat.card V = 2 := by rw [hVt, Nat.card_zpowers, ht2]
      omega
    · exfalso
      have ht2 : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht.sq) ht.ne_one
      have : Nat.card V = 2 := by rw [hVt, Nat.card_zpowers, ht2]
      omega
    · exfalso
      obtain ⟨-, -, -, hcyc, -⟩ := hVU
      obtain ⟨x, hx, y, hy, hxy⟩ := hnonab
      let _ : CommGroup ↥V := IsCyclic.commGroup
      have := mul_comm (⟨x, hx⟩ : ↥V) ⟨y, hy⟩
      exact hxy (congrArg Subtype.val this)
    · exact hcomm
  have hle : J ≤ centModOddCore K := by
    refine hΩ.le_of_forall_isSylow2In hJ fun V hV => ?_
    intro v hv k hk
    exact hVcomm V hV (Subgroup.commutator_mem_commutator hv hk)
  exact Subgroup.commutator_le.mpr fun j hj k hk => hle hj k hk

theorem commutes_of_congr [Finite G] (hp : p ≠ 2) (_hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (h62 : L6_2On Ω) (X : Subgroup G) (hRX : ∀ R ∈ RSet Ω, Commutes R X) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {z t : G} (hz : IsUniqueInvolution K z)
    (ht : IsUniqueInvolution J t) (hzt : t⁻¹ * z ∈ X) :
    ⁅K, J⁆ ≤ oddCoreOf K ⊓ oddCoreOf J := by
  by_cases hzt' : z = t
  · exact hΩ.comm_le_oddCore_of_twin hK hJ hKJ hz (hzt' ▸ ht)
  have hzt'' : z⁻¹ * t ∈ X := by
    have := X.inv_mem hzt
    simpa using this
  refine le_inf ?_ ?_
  · rw [Subgroup.commutator_comm]
    exact commutator_le_oddCoreOf_of_congr hp hΩ h62 X hRX hK hJ hz ht hzt' hzt
  · exact commutator_le_oddCoreOf_of_congr hp hΩ h62 X hRX hJ hK ht hz (Ne.symm hzt') hzt''

theorem omega4_quot [Finite G] (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (h62 : L6_2On Ω) (X : Subgroup G) [X.Normal] (hRX : ∀ R ∈ RSet Ω, Commutes R X)
    (hXK : ∀ K ∈ Ω, Odd (Nat.card ↥(X ⊓ K))) {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (hKJ : K ≠ J) :
    padicValNat 2 (Nat.card ↥(K.map (QuotientGroup.mk' X) ⊓ J.map (QuotientGroup.mk' X))) ≤ 1 ∧
      (padicValNat 2 (Nat.card ↥(K.map (QuotientGroup.mk' X) ⊓ J.map (QuotientGroup.mk' X))) = 1 →
        ⁅K.map (QuotientGroup.mk' X), J.map (QuotientGroup.mk' X)⁆ ≤
          oddCoreOf (K.map (QuotientGroup.mk' X)) ⊓ oddCoreOf (J.map (QuotientGroup.mk' X))) := by
  by_cases heven : 2 ∣ Nat.card ↥(K.map (QuotientGroup.mk' X) ⊓ J.map (QuotientGroup.mk' X))
  swap
  · rw [padicValNat.eq_zero_of_not_dvd heven]
    exact ⟨zero_le_one, fun h => absurd h (by norm_num)⟩
  obtain ⟨z, hz⟩ := hΩ.exists_uniqueInvolution hp hq hK
  obtain ⟨t, ht⟩ := hΩ.exists_uniqueInvolution hp hq hJ
  have hz' := isUniqueInvolution_map_mk_of_odd (hXK K hK) hz
  have ht' := isUniqueInvolution_map_mk_of_odd (hXK J hJ) ht
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(K.map (QuotientGroup.mk' X) ⊓ J.map (QuotientGroup.mk' X))) 2 heven
  have haG : orderOf (a : G ⧸ X) = 2 := by rw [Subgroup.orderOf_coe]; exact ha
  have hasq : (a : G ⧸ X) * (a : G ⧸ X) = 1 := by
    have := pow_orderOf_eq_one (a : G ⧸ X)
    rwa [haG, pow_two] at this
  have hane : (a : G ⧸ X) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at haG
    omega
  have haz : (a : G ⧸ X) = QuotientGroup.mk' X z :=
    (hz'.unique _ a.2.1 hasq).resolve_left hane
  have hat : (a : G ⧸ X) = QuotientGroup.mk' X t :=
    (ht'.unique _ a.2.2 hasq).resolve_left hane
  have hzt : t⁻¹ * z ∈ X := by
    have := hat.symm.trans haz
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at this
    exact this
  have hcomm : ⁅K, J⁆ ≤ oddCoreOf K ⊓ oddCoreOf J :=
    commutes_of_congr hp hq hΩ h62 X hRX hK hJ hKJ hz ht hzt
  have hKX : Commutes K X := commutes_of_mem hp hq hΩ X hRX hK
  have hsub : ∀ b ∈ K.map (QuotientGroup.mk' X) ⊓ J.map (QuotientGroup.mk' X),
      IsPGroup 2 (Subgroup.zpowers b) → b = 1 ∨ b = QuotientGroup.mk' X z := by
    intro b hb hb2
    obtain ⟨hbK, ⟨j, hj, hjb⟩⟩ := Subgroup.mem_inf.mp hb
    have hb2' : IsPGroup 2 (Subgroup.zpowers (⟨b, hbK⟩ : ↥(K.map (QuotientGroup.mk' X)))) := by
      obtain ⟨n, hn⟩ := hb2.exists_card_eq
      refine IsPGroup.of_card (n := n) ?_
      rw [Nat.card_zpowers, Subgroup.orderOf_mk, ← Nat.card_zpowers]
      exact hn
    obtain ⟨k, hkb, hk2⟩ := exists_isPGroup_zpowers_lift (quotRestrict K X)
      (quotRestrict_surjective K X) hb2'
    have hkb' : QuotientGroup.mk' X (k : G) = b := congrArg Subtype.val hkb
    have hxX : (j⁻¹ * (k : G)) ∈ X := by
      have : QuotientGroup.mk' X j = QuotientGroup.mk' X (k : G) := hjb.trans hkb'.symm
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at this
      exact this
    have hkc : ∀ k' ∈ K, ⁅(k : G), k'⁆ ∈ oddCoreOf K := by
      intro k' hk'
      have h1 : ⁅j⁻¹ * (k : G), k'⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.mpr (hKX k' hk' _ hxX).symm
      have h2 : ⁅j, k'⁆ ∈ oddCoreOf K := by
        rw [← commutatorElement_inv]
        exact (oddCoreOf K).inv_mem
          (hcomm (Subgroup.commutator_mem_commutator hk' hj)).1
      have e : ⁅(k : G), k'⁆ = ⁅j, k'⁆ := by
        have e1 : (k : G) = j * (j⁻¹ * (k : G)) := by group
        rw [e1]
        simp only [commutatorElement_def] at h1 ⊢
        have : (j * (j⁻¹ * (k : G))) * k' * (j * (j⁻¹ * (k : G)))⁻¹ * k'⁻¹ =
            j * ((j⁻¹ * (k : G)) * k' * (j⁻¹ * (k : G))⁻¹ * k'⁻¹) * j⁻¹ *
              (j * k' * j⁻¹ * k'⁻¹) := by
          group
        rw [this, h1]
        group
      rw [e]
      exact h2
    have hk2' : IsPGroup 2 (Subgroup.zpowers (k : G)) := by
      obtain ⟨n, hn⟩ := hk2.exists_card_eq
      refine IsPGroup.of_card (n := n) ?_
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, ← Nat.card_zpowers]
      exact hn
    rcases hΩ.center_two hp hq hK hz (k : G) k.2 hk2' hkc with h | h
    · left
      rw [← hkb', h, map_one]
    · right
      rw [← hkb', h]
  have hv2 : padicValNat 2 (Nat.card ↥(K.map (QuotientGroup.mk' X) ⊓
      J.map (QuotientGroup.mk' X))) ≤ 1 :=
    padicValNat_natCard_le_one_of_forall_isPGroup hsub
  refine ⟨hv2, fun _ => ?_⟩
  rw [← Subgroup.map_commutator]
  calc Subgroup.map (QuotientGroup.mk' X) ⁅K, J⁆
      ≤ Subgroup.map (QuotientGroup.mk' X) (oddCoreOf K ⊓ oddCoreOf J) := Subgroup.map_mono hcomm
    _ ≤ Subgroup.map (QuotientGroup.mk' X) (oddCoreOf K) ⊓
        Subgroup.map (QuotientGroup.mk' X) (oddCoreOf J) := Subgroup.map_inf_le _ _ _
    _ = oddCoreOf (K.map (QuotientGroup.mk' X)) ⊓ oddCoreOf (J.map (QuotientGroup.mk' X)) := by
      rw [oddCoreOf_map_mk_of_odd (hXK K hK), oddCoreOf_map_mk_of_odd (hXK J hJ)]

end AscQuot

end CFSG.ClassicalInvolution.Asc77
