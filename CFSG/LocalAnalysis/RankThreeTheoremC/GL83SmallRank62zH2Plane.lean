module

import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zH2Rank
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62ySetup
import CFSG.HardMathSupport.Timmesfeld.Proving.ElemAbelianSubgroup
import CFSG.RankThree.PartOne.HNB.Tools
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

theorem k631b_mem_zpowers_two {t z : G} (ht : t ^ 2 = 1) (hz : z ∈ zpowers t) :
    z = 1 ∨ z = t := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hz
  have h2 : t ^ (2 : ℤ) = 1 := by simpa using ht
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · left
    obtain ⟨m, rfl⟩ : 2 ∣ n := Int.dvd_of_emod_eq_zero h
    rw [zpow_mul, h2, one_zpow]
  · right
    have hn : n = 2 * (n / 2) + 1 := by omega
    rw [hn, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem k631b_centralizer_eq_normalizer {t : G} (ht : t ^ 2 = 1) (ht1 : t ≠ 1) :
    centralizer ({t} : Set G) = normalizer (zpowers t : Set G) := by
  refine le_antisymm (fun g hg => ?_) (fun g hg => ?_)
  · have hg' : g ∈ centralizer ((zpowers t : Subgroup G) : Set G) := by
      rw [mem_centralizer_iff]
      intro y hy
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hy
      exact (Commute.zpow_left (show Commute t g from (mem_centralizer_singleton_iff.mp hg).symm)
        n).eq
    exact centralizer_le_normalizer _ hg'
  · have h1 : g * t * g⁻¹ ∈ zpowers t := (mem_normalizer_iff.mp hg t).mp (mem_zpowers t)
    rcases k631b_mem_zpowers_two ht h1 with h | h
    · exact absurd (conj_eq_one_iff.mp h) ht1
    · exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp h)

theorem k631b_isTwoLocal_centralizer {t : G} (ht : t ^ 2 = 1) (ht1 : t ≠ 1) :
    IsTwoLocal (centralizer ({t} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨zpowers t, by rwa [Ne, zpowers_eq_bot], ?_, k631b_centralizer_eq_normalizer ht ht1⟩
  exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime ht ht1, pow_one])

variable [Finite G]

omit [Finite G] in
theorem k631b_card_plane {f : ℕ} (hf : f.Prime) (hf2 : f ≠ 2) {F : Subgroup G}
    (hFe : IsElemAbelian f F) (hF4 : Nat.card F = f ^ 4) {t y g : G} (ht : t ^ 2 = 1)
    (htF : t ∈ normalizer (F : Set G)) (hgF : g ∈ normalizer (F : Set G))
    (hyF : ∀ a ∈ F, y * a * y⁻¹ = a⁻¹) (hg : g * t * g⁻¹ = t * y) :
    Nat.card (F ⊓ centralizer ({t} : Set G) : Subgroup G) = f ^ 2 := by
  obtain ⟨k, hk⟩ := hf.odd_of_ne_two hf2
  have hcommF : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := by
    have := hFe.1
    exact fun a ha b hb => setLike_mul_comm (s := F) ha hb
  have hexp : ∀ a ∈ F, a ^ f = 1 := hFe.2
  have htt : t * t = 1 := by rw [← sq]; exact ht
  have hσF : ∀ a ∈ F, t * a * t⁻¹ ∈ F := fun a ha => (mem_normalizer_iff.mp htF a).mp ha
  have hσσ : ∀ x : G, t * (t * x * t⁻¹) * t⁻¹ = x := by
    intro x
    calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t * t)⁻¹ := by group
      _ = x := by rw [htt]; group
  set Cp : Subgroup G := F ⊓ centralizer ({t} : Set G) with hCp
  set Cm : Subgroup G := F ⊓ centralizer ({t * y} : Set G) with hCm
  have hCp_mem : ∀ b ∈ F, t * b * t⁻¹ = b → b ∈ Cp := by
    intro b hbF he
    refine ⟨hbF, mem_centralizer_singleton_iff.mpr ?_⟩
    calc b * t = (t * b * t⁻¹) * t := by rw [he]
      _ = t * b := by group
  have hCm_mem : ∀ c ∈ F, t * c⁻¹ * t⁻¹ = c → c ∈ Cm := by
    intro c hcF he
    refine ⟨hcF, mem_centralizer_singleton_iff.mpr ?_⟩
    have hyc : y * c = c⁻¹ * y := by
      have := hyF c hcF
      calc y * c = (y * c * y⁻¹) * y := by group
        _ = c⁻¹ * y := by rw [this]
    calc c * (t * y) = (t * c⁻¹ * t⁻¹) * (t * y) := by rw [he]
      _ = t * (c⁻¹ * y) := by group
      _ = t * (y * c) := by rw [hyc]
      _ = (t * y) * c := by group
  have hdec : F ≤ Cp ⊔ Cm := by
    intro a ha
    obtain ⟨τ, hτ⟩ : ∃ τ : G, τ = t * a * t⁻¹ := ⟨_, rfl⟩
    have hτF : τ ∈ F := hτ ▸ hσF a ha
    have hτσ : t * τ * t⁻¹ = a := by rw [hτ]; exact hσσ a
    have hcAτ : Commute a τ := hcommF a ha τ hτF
    obtain ⟨m, hm⟩ : ∃ m : ℕ, m = k + 1 := ⟨_, rfl⟩
    have hb : (a * τ) ^ m ∈ Cp := by
      refine hCp_mem _ (F.pow_mem (F.mul_mem ha hτF) m) ?_
      rw [← conj_pow]
      have h1 : t * (a * τ) * t⁻¹ = (t * a * t⁻¹) * (t * τ * t⁻¹) := by group
      rw [h1, ← hτ, hτσ, hcommF τ hτF a ha]
    have hc : (a * τ⁻¹) ^ m ∈ Cm := by
      refine hCm_mem _ (F.pow_mem (F.mul_mem ha (F.inv_mem hτF)) m) ?_
      rw [← inv_pow, ← conj_pow]
      have h1 : t * (a * τ⁻¹)⁻¹ * t⁻¹ = (t * τ * t⁻¹) * (t * a⁻¹ * t⁻¹) := by group
      have h2 : t * a⁻¹ * t⁻¹ = τ⁻¹ := by rw [hτ]; group
      rw [h1, h2, hτσ]
    have habc : a = (a * τ) ^ m * (a * τ⁻¹) ^ m := by
      have hcm : a ^ m * τ ^ m = τ ^ m * a ^ m := (hcAτ.pow_pow m m).eq
      have h1 : a = a ^ m * a ^ m := by
        rw [← pow_add, show m + m = f + 1 by omega, pow_succ, hexp a ha, one_mul]
      calc a = a ^ m * a ^ m := h1
        _ = a ^ m * (a ^ m * τ ^ m) * (τ ^ m)⁻¹ := by group
        _ = a ^ m * (τ ^ m * a ^ m) * (τ ^ m)⁻¹ := by rw [hcm]
        _ = (a ^ m * τ ^ m) * (a ^ m * (τ ^ m)⁻¹) := by group
        _ = (a * τ) ^ m * (a * τ⁻¹) ^ m := by
            rw [hcAτ.mul_pow, hcAτ.inv_right.mul_pow, inv_pow]
    have := mul_mem_sup hb hc
    rwa [← habc] at this
  have hinf : Cp ⊓ Cm = ⊥ := by
    refine eq_bot_iff.mpr fun z hz => ?_
    rw [Subgroup.mem_bot]
    obtain ⟨⟨hzF, hzt⟩, -, hzty⟩ := hz
    have hzt' : z * t = t * z := mem_centralizer_singleton_iff.mp hzt
    have hzty' : z * (t * y) = (t * y) * z := mem_centralizer_singleton_iff.mp hzty
    have hyz : y * z = z⁻¹ * y := by
      have := hyF z hzF
      calc y * z = (y * z * y⁻¹) * y := by group
        _ = z⁻¹ * y := by rw [this]
    have h1 : t * z * y = t * z⁻¹ * y := by
      calc t * z * y = z * t * y := by rw [← hzt']
        _ = z * (t * y) := by group
        _ = (t * y) * z := hzty'
        _ = t * (y * z) := by group
        _ = t * (z⁻¹ * y) := by rw [hyz]
        _ = t * z⁻¹ * y := by group
    have hzz : z = z⁻¹ := mul_left_cancel (mul_right_cancel h1)
    have hzz1 : z * z = 1 := mul_eq_one_iff_eq_inv.mpr hzz
    have hzf := hexp z hzF
    rw [hk, pow_succ, pow_mul, sq, hzz1, one_pow, one_mul] at hzf
    exact hzf
  have hcard : Nat.card Cm = Nat.card Cp := by
    refine Nat.card_congr
      { toFun := fun x => ⟨g⁻¹ * x * g, ?_⟩
        invFun := fun x => ⟨g * x * g⁻¹, ?_⟩
        left_inv := fun x => Subtype.ext (by group)
        right_inv := fun x => Subtype.ext (by group) }
    · have hx := x.2
      refine ⟨(mem_normalizer_iff''.mp hgF x).mp hx.1, mem_centralizer_singleton_iff.mpr ?_⟩
      have hx2 : (x : G) * (t * y) = (t * y) * x := mem_centralizer_singleton_iff.mp hx.2
      rw [← hg] at hx2
      calc g⁻¹ * x * g * t = g⁻¹ * (x * (g * t * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * t * g⁻¹) * x) * g := by rw [hx2]
        _ = t * (g⁻¹ * x * g) := by group
    · have hx := x.2
      refine ⟨(mem_normalizer_iff.mp hgF x).mp hx.1, mem_centralizer_singleton_iff.mpr ?_⟩
      have hx2 : (x : G) * t = t * x := mem_centralizer_singleton_iff.mp hx.2
      rw [← hg]
      calc g * x * g⁻¹ * (g * t * g⁻¹) = g * (x * t) * g⁻¹ := by group
        _ = g * (t * x) * g⁻¹ := by rw [hx2]
        _ = (g * t * g⁻¹) * (g * x * g⁻¹) := by group
  obtain ⟨-, hc⟩ := k631b_join_elem (A := Cp) (B := Cm) (fun a ha b hb => hcommF a ha.1 b hb.1) hinf
    (CFSG.HardMathSupport.Timmesfeld.Proving.isElemAbelian_of_le hFe inf_le_left)
    (CFSG.HardMathSupport.Timmesfeld.Proving.isElemAbelian_of_le hFe inf_le_left)
  have hFeq : Cp ⊔ Cm = F := le_antisymm (sup_le inf_le_left inf_le_left) hdec
  rw [hFeq, hF4, hcard] at hc
  have h1 : Nat.card Cp * Nat.card Cp = f ^ 2 * f ^ 2 := by
    rw [← hc]
    ring
  exact Nat.mul_self_inj.mp h1

omit [Finite G] in
theorem k631b_normalizer_inf {R V : Subgroup G} {u : G} (hVR : V ≤ normalizer (R : Set G))
    (huV : u ∈ V) (hVc : IsMulCommutative V) :
    V ≤ normalizer ((R ⊓ centralizer ({u} : Set G) : Subgroup G) : Set G) := by
  intro v hv
  have h1 := mem_normalizer_iff.mp (hVR hv)
  have h2 := mem_normalizer_iff.mp
    (CFSG.RankThree.PartOne.HNB.mem_normalizer_centralizer_of_commute (a := v) (b := u)
      (setLike_mul_comm (s := V) hv huV))
  refine mem_normalizer_iff.mpr fun x => ?_
  simp only [Subgroup.mem_inf]
  exact and_congr (h1 x) (h2 x)

theorem k631b_comm_props {f : ℕ} (hf : f.Prime) (hf2 : f ≠ 2) {R V : Subgroup G} {u : G}
    (hR : IsPGroup 2 R) (hVR : V ≤ normalizer (R : Set G)) (huV : u ∈ V)
    (hVc : IsMulCommutative V) (hV2 : Nat.card V = f ^ 2) :
    IsPGroup 2 (⁅R ⊓ centralizer ({u} : Set G), V⁆ : Subgroup G) ∧
      ⁅R ⊓ centralizer ({u} : Set G), V⁆ ≤ centralizer ({u} : Set G) ∧
      V ≤ normalizer ((⁅R ⊓ centralizer ({u} : Set G), V⁆ : Subgroup G) : Set G) ∧
      ⁅⁅R ⊓ centralizer ({u} : Set G), V⁆, V⁆ = ⁅R ⊓ centralizer ({u} : Set G), V⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVK := k631b_normalizer_inf hVR huV hVc
  have hYK : ⁅R ⊓ centralizer ({u} : Set G), V⁆ ≤ R ⊓ centralizer ({u} : Set G) :=
    (le_normalizer_iff_commutator_le_left (H := V)
      (K := R ⊓ centralizer ({u} : Set G))).mp hVK
  have hK2 : IsPGroup 2 ↥(R ⊓ centralizer ({u} : Set G)) := hR.to_le inf_le_left
  refine ⟨hR.to_le (hYK.trans inf_le_left), hYK.trans inf_le_right,
    normalizer_commutator_ge_right _ _, ?_⟩
  obtain ⟨j, hj⟩ := hK2.exists_card_eq
  have hcop : Nat.Coprime (Nat.card V) (Nat.card (R ⊓ centralizer ({u} : Set G) : Subgroup G)) := by
    rw [hV2, hj]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hf Nat.prime_two).mpr hf2)
  have : Group.IsNilpotent ↥(R ⊓ centralizer ({u} : Set G)) := hK2.isNilpotent
  exact CFSG.RankThree.PartOne.HNB.commutator_double_eq_self_of_coprime_solvable V _ hVK hcop
    inferInstance

theorem k631b_plane_exists (hchar : IsCharTwoType G) {f : ℕ} (hf : f.Prime) (hf2 : f ≠ 2)
    {t : G} (ht : t ^ 2 = 1) (ht1 : t ≠ 1) {V : Subgroup G}
    (hVt : V ≤ centralizer ({t} : Set G)) (hVe : IsElemAbelian f V) (hV2 : Nat.card V = f ^ 2) :
    ∃ u ∈ V, u ≠ 1 ∧
      ⁅pCoreOf 2 (centralizer ({t} : Set G)) ⊓ centralizer ({u} : Set G), V⁆ ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR2 : IsPGroup 2 (pCoreOf 2 (centralizer ({t} : Set G))) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hVR : V ≤ normalizer (pCoreOf 2 (centralizer ({t} : Set G)) : Set G) :=
    hVt.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hchar' := hchar _ (k631b_isTwoLocal_centralizer ht ht1)
  by_contra hcon
  push Not at hcon
  have hle : ∀ y ∈ V, y ≠ 1 →
      pCoreOf 2 (centralizer ({t} : Set G)) ⊓ centralizer ({y} : Set G) ≤
        centralizer (V : Set G) :=
    fun y hy hy1 => commutator_eq_bot_iff_le_centralizer.mp (hcon y hy hy1)
  have hRV := sr629_le_of_forall_inf_centralizer_le_plane hf hVe hV2 hVR
    (sr629_coprime_card_of_isPGroup_two hf hf2 hR2) hle
  have hV1 : V ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hV2
    have : 1 < f ^ 2 := Nat.one_lt_pow (by norm_num) hf.one_lt
    omega
  obtain ⟨⟨v, hv⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hV1
  have hv1' : v ≠ 1 := fun h => hv1 (Subtype.ext h)
  have hvC : v ∈ centralizer ((pCoreOf 2 (centralizer ({t} : Set G)) : Subgroup G) : Set G) := by
    rw [mem_centralizer_iff]
    intro r hr
    exact (mem_centralizer_iff.mp (hRV hr) v hv).symm
  have hvR : v ∈ pCoreOf 2 (centralizer ({t} : Set G)) := hchar' ⟨hVt hv, hvC⟩
  exact sr629_not_mem_of_isPGroup_two hf hf2 hR2 hv1' (hVe.2 v hv) hvR

theorem k631b_plane_Y (hchar : IsCharTwoType G) {f : ℕ} (hf : f.Prime) (hf2 : f ≠ 2) {t : G}
    (ht : t ^ 2 = 1) (ht1 : t ≠ 1) {V : Subgroup G} (hVt : V ≤ centralizer ({t} : Set G))
    (hVe : IsElemAbelian f V) (hV2 : Nat.card V = f ^ 2) :
    ∃ u ∈ V, u ≠ 1 ∧ ∃ Y : Subgroup G, Y ≠ ⊥ ∧ IsPGroup 2 Y ∧ Y ≤ centralizer ({u} : Set G) ∧
      V ≤ normalizer (Y : Set G) ∧ ⁅Y, V⁆ = Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, huV, hu1, hne⟩ := k631b_plane_exists hchar hf hf2 ht ht1 hVt hVe hV2
  have hR2 : IsPGroup 2 (pCoreOf 2 (centralizer ({t} : Set G))) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hVR : V ≤ normalizer (pCoreOf 2 (centralizer ({t} : Set G)) : Set G) :=
    hVt.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  obtain ⟨hY2, hYC, hVY, hYY⟩ := k631b_comm_props hf hf2 hR2 hVR huV hVe.1 hV2
  exact ⟨u, huV, hu1, _, hne, hY2, hYC, hVY, hYY⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
