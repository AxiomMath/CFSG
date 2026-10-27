module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614HKbar
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Lines

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614H

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
open CFSG.OrderReductions.FrattiniAutomorphisms (quotientAutomorphism quotientAutomorphism_apply)

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H S K : Subgroup G} {x z : G}

noncomputable def kbarAct (K : Subgroup G) : normalizer (K : Set G) →* MulAut (Kbar K) :=
  (quotientAutomorphism (CFSG.pPrimeCore 3 K)).comp K.normalizerMonoidHom

theorem kbarAct_mk (g : normalizer (K : Set G)) (k : K) :
    kbarAct K g (kbarMk K k) =
      kbarMk K ⟨g * k * (g : G)⁻¹, (mem_normalizer_iff.mp g.2 k).mp k.2⟩ := by
  rw [kbarAct, MonoidHom.comp_apply, quotientAutomorphism_apply]
  rfl

theorem kbarAct_of_mem (k : K) :
    kbarAct K ⟨k, le_normalizer k.2⟩ = MulAut.conj (kbarMk K k) := by
  ext a
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective _ a
  rw [kbarAct_mk, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  rfl

theorem center_eq_bot_of_simple {T : Type*} [Group T] [IsSimpleGroup T]
    (hnab : ∃ a b : T, a * b ≠ b * a) : center T = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center T) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have hb : b ∈ center T := by
      rw [h]
      trivial
    exact hab (mem_center_iff.mp hb a)

theorem x_not_mem_zpowers (hyp : Hyp P M x z H S) : x ∉ zpowers z := by
  intro hx
  have hB := (SmallRankPlane.of_situation hyp.setting hyp.situation hyp.point
    hyp.central).card_eq
  rw [sup_eq_right.mpr (zpowers_le.mpr hx), Nat.card_zpowers, orderOf_z hyp] at hB
  norm_num at hB

theorem exists_b (kOut : KFactOutThreePrimeSimple) (hyp : Hyp P M x z H S)
    (h618 : Stage618 M H K z) (hcard : Nat.card (Kbar K) = 60 ∨ Nat.card (Kbar K) = 168) :
    ∃ b : G, b ∈ zpowers x ⊔ zpowers z ∧ b ∉ zpowers z ∧
      ⁅zpowers b, K⁆ ≤ pCoreOf 2 H := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := isSimpleGroup_kbar hyp h618
  have hnab := exists_ne_comm_kbar hyp h618
  have hBH : zpowers x ⊔ zpowers z ≤ H := hyp.optimal.ext.pair.le
  have hxB : x ∈ zpowers x ⊔ zpowers z := mem_sup_left (mem_zpowers x)
  have hxN : x ∈ normalizer (K : Set G) := h618.comp.normal (hBH hxB)
  have hzK : z ∈ K := z_mem h618
  have hxz : x * z = z * x :=
    (mem_centralizer_iff.mp hyp.central.centralizes x hyp.point.mem)
  set φ := kbarAct K ⟨x, hxN⟩ with hφ
  have hφ3 : φ ^ 3 = 1 := by
    rw [hφ, ← map_pow]
    have h : (⟨x, hxN⟩ : normalizer (K : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hyp.point.pow_eq_one)
    rw [h, map_one]
  have hz3 := orderOf_zbar hyp h618
  have hP3 : ∃ Q : Subgroup (Kbar K), Nat.card Q = 3 ∧ ¬ 3 ∣ Q.index := by
    refine ⟨zpowers (zbar h618), by rw [Nat.card_zpowers, hz3], fun hdvd => ?_⟩
    have h := card_mul_index (zpowers (zbar h618))
    rw [Nat.card_zpowers, hz3] at h
    obtain ⟨c, hc⟩ := hdvd
    rcases hcard with h' | h' <;> rw [h', hc] at h <;> omega
  obtain ⟨kb, hkb⟩ := kOut (Kbar K) (isKGroup_kbar hyp h618) (isSimpleGroup_kbar hyp h618)
    hnab hP3 φ ⟨1, by rw [pow_one]; exact hφ3⟩
  have hkz : kb * zbar h618 = zbar h618 * kb := by
    have h1 : φ (zbar h618) = zbar h618 := by
      rw [hφ, kbarAct_mk]
      congr 1
      exact Subtype.ext (by simp [hxz, mul_assoc])
    rw [hkb, MulAut.conj_apply] at h1
    calc kb * zbar h618 = kb * zbar h618 * kb⁻¹ * kb := by group
      _ = zbar h618 * kb := by rw [h1]
  have hkb3 : kb ^ 3 = 1 := by
    have h1 : MulAut.conj (kb ^ 3) = 1 := by rw [map_pow, ← hkb, hφ3]
    have h2 : kb ^ 3 ∈ center (Kbar K) := by
      rw [mem_center_iff]
      intro g
      have h3 := congrArg (fun ψ : MulAut (Kbar K) => ψ g) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h3
      calc g * kb ^ 3 = kb ^ 3 * g * (kb ^ 3)⁻¹ * kb ^ 3 := by rw [h3]
        _ = kb ^ 3 * g := by group
    rw [center_eq_bot_of_simple hnab] at h2
    exact h2
  have hkbZ : kb ∈ zpowers (zbar h618) := by
    have hp1 : IsPGroup 3 (zpowers kb) := (CFSG.Open.isElemAbelian_zpowers hkb3).isPGroup
    have hz3' : zbar h618 ^ 3 = 1 := by
      have h := pow_orderOf_eq_one (zbar h618)
      rwa [hz3] at h
    have hp2 : IsPGroup 3 (zpowers (zbar h618)) :=
      (CFSG.Open.isElemAbelian_zpowers hz3').isPGroup
    have hn : zpowers kb ≤ normalizer (zpowers (zbar h618) : Set (Kbar K)) := by
      rw [zpowers_le]
      exact centralizer_le_normalizer _
        (mem_centralizer_iff.mpr (fun h hh => by
          obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hh
          exact ((Commute.zpow_right (show Commute kb (zbar h618) from hkz) i).eq).symm))
    have hp := IsPGroup.to_sup_of_normal_right' hp1 hp2 hn
    obtain ⟨n, hn'⟩ := IsPGroup.iff_card.mp hp
    have hdvd : 3 ^ n ∣ Nat.card (Kbar K) := hn' ▸ card_subgroup_dvd_card _
    have hn1 : n ≤ 1 := by
      by_contra h
      have h9 : 9 ∣ Nat.card (Kbar K) :=
        (pow_dvd_pow 3 (by omega : 2 ≤ n)).trans hdvd
      rcases hcard with h' | h' <;> rw [h'] at h9 <;> norm_num at h9
    have hle : Nat.card (zpowers kb ⊔ zpowers (zbar h618) : Subgroup (Kbar K)) ≤
        Nat.card (zpowers (zbar h618)) := by
      rw [hn', Nat.card_zpowers, hz3]
      calc 3 ^ n ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hn1
        _ = 3 := by norm_num
    have heq := eq_of_le_of_card_ge (le_sup_right (a := zpowers kb)) hle
    rw [heq]
    exact mem_sup_left (mem_zpowers kb)
  obtain ⟨i, hi⟩ := mem_zpowers_iff.mp hkbZ
  have hzi : (z ^ i)⁻¹ ∈ K := inv_mem (zpow_mem hzK i)
  have hziN : (z ^ i)⁻¹ ∈ normalizer (K : Set G) := le_normalizer hzi
  refine ⟨x * (z ^ i)⁻¹,
    mul_mem hxB (inv_mem (mem_sup_right (zpow_mem (mem_zpowers z) i))), fun hb => ?_, ?_⟩
  · apply x_not_mem_zpowers hyp
    have h := mul_mem hb (zpow_mem (mem_zpowers z) i)
    rwa [inv_mul_cancel_right] at h
  · have hbN : x * (z ^ i)⁻¹ ∈ normalizer (K : Set G) := mul_mem hxN hziN
    have hact : kbarAct K ⟨x * (z ^ i)⁻¹, hbN⟩ = 1 := by
      have h1 : (⟨x * (z ^ i)⁻¹, hbN⟩ : normalizer (K : Set G)) =
          ⟨x, hxN⟩ * ⟨(z ^ i)⁻¹, hziN⟩ := rfl
      have h2 : kbarAct K ⟨(z ^ i)⁻¹, hziN⟩ = MulAut.conj kb⁻¹ := by
        have h3 : kbarMk K ⟨(z ^ i)⁻¹, hzi⟩ = kb⁻¹ := by
          have h4 : (⟨(z ^ i)⁻¹, hzi⟩ : K) = ((⟨z, hzK⟩ : K) ^ i)⁻¹ := Subtype.ext (by simp)
          rw [h4, map_inv, map_zpow, ← hi]
        rw [kbarAct_of_mem ⟨_, hzi⟩, h3]
      rw [h1, map_mul, ← hφ, hkb, h2, ← map_mul, mul_inv_cancel, map_one]
    have hker : zpowers (x * (z ^ i)⁻¹) ≤ (kbarAct K).ker.map (normalizer (K : Set G)).subtype :=
      zpowers_le.mpr ⟨⟨_, hbN⟩, hact, rfl⟩
    rw [commutator_le]
    intro g hg k hk
    obtain ⟨⟨g, hgN⟩, hg1, rfl⟩ := hker hg
    have hgk : g * k * g⁻¹ ∈ K := (mem_normalizer_iff.mp hgN k).mp hk
    have h1 := congrArg (fun ψ : MulAut (Kbar K) => ψ (kbarMk K ⟨k, hk⟩)) hg1
    simp only [MulAut.one_apply] at h1
    rw [kbarAct_mk] at h1
    have h2 : kbarMk K ⟨g * k * g⁻¹ * k⁻¹, mul_mem hgk (inv_mem hk)⟩ = 1 := by
      have h3 : (⟨g * k * g⁻¹ * k⁻¹, mul_mem hgk (inv_mem hk)⟩ : K) =
          ⟨g * k * g⁻¹, hgk⟩ * (⟨k, hk⟩ : K)⁻¹ := rfl
      rw [h3, map_mul, map_inv, h1, mul_inv_cancel]
    have h4 := (kbarMk_eq_one_iff hyp h618 _).1 h2
    rwa [commutatorElement_def]

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614H
