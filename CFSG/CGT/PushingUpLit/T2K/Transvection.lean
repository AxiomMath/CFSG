module

public import CFSG.CGT.PushingUpLit.T2K.Offender

public section

namespace CFSG.CGT.PushingUpLit.T2K

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

theorem zpow_eq_one_or_self {G : Type} [Group G] {z : G} (hz : z ^ 2 = 1) (k : ℤ) :
    z ^ k = 1 ∨ z ^ k = z := by
  have hz' : z ^ (2 : ℤ) = 1 := by simpa using hz
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [zpow_mul, hz', one_zpow]
  · right
    rw [zpow_add, zpow_mul, hz', one_zpow, one_mul, zpow_one]

theorem fixed_of_fixed_sq {W : Type*} [CommGroup W] (hW : ∀ w : W, w * w = 1) (φ : W → W)
    (hmul : ∀ a b, φ (a * b) = φ a * φ b) (h4 : ∀ w, φ (φ (φ (φ w))) = w)
    (H : ∀ u, φ (φ u) = u → φ u = u) (v : W) : φ v = v := by
  obtain ⟨v1, hv1⟩ : ∃ x, φ v = x := ⟨_, rfl⟩
  obtain ⟨v2, hv2⟩ : ∃ x, φ v1 = x := ⟨_, rfl⟩
  obtain ⟨v3, hv3⟩ : ∃ x, φ v2 = x := ⟨_, rfl⟩
  have hv4 : φ v3 = v := by rw [← hv3, ← hv2, ← hv1]; exact h4 v
  have hsq : ∀ a b : W, (a * b) * (a * b) = 1 := fun a b => by
    calc (a * b) * (a * b) = (a * a) * (b * b) := by rw [mul_mul_mul_comm]
      _ = 1 := by rw [hW, hW, mul_one]
  have e1 : v3 * v1 = v2 * v := by
    have h1 : φ (φ (v2 * v)) = v2 * v := by
      rw [hmul, hv3, hv1, hmul, hv4, hv2, mul_comm]
    have := H (v2 * v) h1
    rwa [hmul, hv3, hv1] at this
  have e5 : v3 * v2 = v1 * v := by
    have hone : (v3 * v2) * (v1 * v) = 1 := by
      calc (v3 * v2) * (v1 * v) = (v3 * v1) * (v2 * v) := mul_mul_mul_comm _ _ _ _
        _ = (v2 * v) * (v2 * v) := by rw [e1]
        _ = 1 := hsq _ _
    calc v3 * v2 = (v3 * v2) * ((v1 * v) * (v1 * v)) := by rw [hsq, mul_one]
      _ = ((v3 * v2) * (v1 * v)) * (v1 * v) := (mul_assoc _ _ _).symm
      _ = v1 * v := by rw [hone, one_mul]
  have e6 : φ (φ (v1 * v)) = v1 * v := by
    rw [hmul, hv2, hv1, hmul, hv3, hv2, e5]
  have e7 : v2 * v1 = v1 * v := by
    have := H (v1 * v) e6
    rwa [hmul, hv2, hv1] at this
  have e8 : v2 = v := by
    have : v2 * v1 = v * v1 := by rw [e7, mul_comm]
    exact mul_right_cancel this
  apply H v
  rw [hv1, hv2, e8]

theorem centralizes_of_fixed_sq {G : Type} [Group G] {V : Subgroup G} (hV : IsElemAbelian 2 V)
    {y : G} (hy : y ∈ Subgroup.normalizer (V : Set G)) (hy4 : y ^ 4 = 1)
    (H : ∀ u ∈ V, y ^ 2 * u * (y ^ 2)⁻¹ = u → y * u * y⁻¹ = u) :
    ∀ v ∈ V, y * v * y⁻¹ = v := by
  classical
  let _ : CommGroup ↥V := commGroupOfElemAbelian hV
  intro v hv
  let φ : MulAut ↥V := conjAct V ⟨y, hy⟩
  have hφ : ∀ w : ↥V, ((φ w : ↥V) : G) = y * w * y⁻¹ := fun w => conjAct_apply' V ⟨y, hy⟩ w
  have hW : ∀ w : ↥V, w * w = 1 := fun w => Subtype.ext (by simpa [sq] using hV.2 w w.2)
  have h4 : ∀ w : ↥V, φ (φ (φ (φ w))) = w := by
    intro w
    apply Subtype.ext
    rw [hφ, hφ, hφ, hφ]
    have hy4' : y * y * y * y = 1 := by simpa [pow_succ, mul_assoc] using hy4
    have e : y * (y * (y * (y * (w : G) * y⁻¹) * y⁻¹) * y⁻¹) * y⁻¹ =
        (y * y * y * y) * (w : G) * (y * y * y * y)⁻¹ := by group
    rw [e, hy4']
    group
  have H' : ∀ u : ↥V, φ (φ u) = u → φ u = u := by
    intro u hu
    apply Subtype.ext
    have h1 : y ^ 2 * (u : G) * (y ^ 2)⁻¹ = (u : G) := by
      have := congrArg (fun w : ↥V => (w : G)) hu
      simp only [hφ] at this
      calc y ^ 2 * (u : G) * (y ^ 2)⁻¹ = (y * y) * (u : G) * (y * y)⁻¹ := by rw [pow_two]
        _ = y * (y * (u : G) * y⁻¹) * y⁻¹ := by group
        _ = (u : G) := this
    rw [hφ]
    exact H u u.2 h1
  have := fixed_of_fixed_sq (W := ↥V) hW (fun w => φ w) (fun a b => map_mul φ a b) h4 H' ⟨v, hv⟩
  have h5 := congrArg (fun w : ↥V => (w : G)) this
  simpa [hφ] using h5

namespace NatBlock

variable {G : Type} [Group G] [Finite G] {L M : Subgroup G} {n : ℕ}

theorem centralizes_of_index_le_two (h : NatBlock L n) (hLM : L ≤ M)
    (hMN : M ≤ Subgroup.normalizer (L : Set G)) {t : G} (htM : t ∈ M) (ht2 : t ^ 2 = 1)
    (hidx : Nat.card ↥(blockU L) ≤
      2 * Nat.card ↥(blockU L ⊓ Subgroup.centralizer ({t} : Set G))) :
    t ∈ Subgroup.centralizer (blockU L : Set G) := by
  classical
  by_contra htV
  set V : Subgroup G := blockU L with hVdef
  have hMV : M ≤ Subgroup.normalizer (V : Set G) := le_normalizer_blockU_of_le hMN
  have ht1 : t ≠ 1 := fun h1 => htV (h1 ▸ one_mem _)
  have hord : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  set A : Subgroup G := Subgroup.zpowers t with hA
  have hAM : A ≤ M := (Subgroup.zpowers_le).2 htM
  have hAe : IsElemAbelian 2 A := by
    refine isElemAbelian_of_forall' (fun a ha b hb => ?_) (fun a ha => ?_)
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact (Commute.zpow_zpow_self t i j).eq
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht2, one_zpow]
  have hAV : ¬ A ≤ Subgroup.centralizer (V : Set G) := fun hAV => htV (hAV (Subgroup.mem_zpowers t))
  have hAC : A ⊓ Subgroup.centralizer (V : Set G) = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun a ha => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha.1
    rcases zpow_eq_one_or_self ht2 k with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ ha.2) htV
  have hrel : (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A = 2 := by
    rw [hAC, Subgroup.relIndex_bot_left, hA, Nat.card_zpowers, hord]
  have hCA : V ⊓ Subgroup.centralizer (A : Set G) = V ⊓ Subgroup.centralizer ({t} : Set G) := by
    refine le_antisymm (inf_le_inf_left _ (Subgroup.centralizer_le
      (Set.singleton_subset_iff.2 (Subgroup.mem_zpowers t)))) (inf_le_inf_left _ ?_)
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    have : t * c = c * t := (Subgroup.mem_centralizer_singleton_iff.1 hc).symm
    exact ((Commute.zpow_left (show Commute t c from this) k)).eq
  have hwtA : wtG V A = 2 * Nat.card ↥(V ⊓ Subgroup.centralizer ({t} : Set G)) := by
    unfold wtG
    rw [hrel, hCA]
  have hwt0 : wtG V ⊥ = Nat.card ↥V := by
    unfold wtG
    have : V ⊓ Subgroup.centralizer ((⊥ : Subgroup G) : Set G) = V := by
      refine inf_eq_left.2 fun v _ => Subgroup.mem_centralizer_iff.2 fun x hx => ?_
      have : x = 1 := Subgroup.mem_bot.1 hx
      rw [this]
      simp
    rw [this, bot_inf_eq, Subgroup.relIndex_bot_left, Subgroup.card_bot, one_mul]
  have hOff : IsOffG V A := by
    refine ⟨hAM.trans hMV, hAV, fun a ha b hb => ?_, fun a ha => ?_, fun B hBA => ?_⟩
    · rw [commutatorElement_eq_one_iff_mul_comm.2 (isElemAbelian_comm' hAe ha hb)]
      exact one_mem _
    · rw [hAe.2 a ha]
      exact one_mem _
    · by_cases hB : B = ⊥
      · rw [hB, hwt0, hwtA]
        exact hidx
      · have hBA' : B = A := by
          obtain ⟨b, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hB
          obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hBA b.2)
          rcases zpow_eq_one_or_self ht2 k with h1 | h1
          · exact absurd (Subtype.ext (hk.symm.trans h1)) hb1
          · have htB : t ∈ B := by
              have : (b : G) = t := hk.symm.trans h1
              rw [← this]
              exact b.2
            exact le_antisymm hBA ((Subgroup.zpowers_le).2 htB)
        rw [hBA']
  obtain ⟨h1, -, -⟩ := h.offender_of_isOffG hLM hMN hAM hAe hOff hAV
  rw [hrel] at h1
  have h2 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h.two_le
  omega

end NatBlock

end CFSG.CGT.PushingUpLit.T2K
