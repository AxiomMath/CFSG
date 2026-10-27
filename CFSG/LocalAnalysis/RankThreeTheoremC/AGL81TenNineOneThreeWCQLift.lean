module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCQChain
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeCfgHolds

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers
open Subgroup
open TenNineOneThree (IsWClosedIn)

namespace TenNineOneThree

section Lift

variable {H B : Type*} [Group H] [Group B]

theorem map_map_conj (π : H →* B) (A : Subgroup H) (y : H) :
    (A.map π).map (MulAut.conj (π y)).toMonoidHom =
      (A.map (MulAut.conj y).toMonoidHom).map π := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext a
  simp [MulAut.conj_apply]

theorem map_conj_mul (A : Subgroup H) (w g : H) :
    A.map (MulAut.conj (w * g)).toMonoidHom =
      (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj w).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext a
  simp [MulAut.conj_apply, mul_assoc]

theorem IsWClosedIn.map_conj_eq {Q A Y : Subgroup H} (hA : IsWClosedIn Q A Y) (hQY : Q ≤ Y)
    {q : H} (hq : q ∈ Q) : A.map (MulAut.conj q).toMonoidHom = A := by
  refine hA.2 q (hQY hq) ?_
  rintro _ ⟨a, ha, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact Q.mul_mem (Q.mul_mem hq (hA.1 ha)) (Q.inv_mem hq)

variable [Finite H] {p : ℕ} [Fact p.Prime]

theorem isWClosedIn_map (π : H →* B) {Q A Y : Subgroup H} (hQ : IsSylowIn p Q Y)
    (hA : IsWClosedIn Q A Y) : IsWClosedIn (Q.map π) (A.map π) (Y.map π) := by
  classical
  refine ⟨Subgroup.map_mono hA.1, ?_⟩
  rintro _ ⟨y, hy, rfl⟩ hmap
  have hAY : A ≤ Y := hA.1.trans hQ.le
  set W : Subgroup H := Q ⊔ (π.ker ⊓ Y) with hW
  have hWY : W ≤ Y := sup_le hQ.le inf_le_right
  have hAyW : A.map (MulAut.conj y).toMonoidHom ≤ W := by
    rintro _ ⟨a, ha, rfl⟩
    have hm : π (y * a * y⁻¹) ∈ Q.map π := by
      refine hmap ⟨π a, ⟨a, ha, rfl⟩, ?_⟩
      simp [MulAut.conj_apply]
    obtain ⟨q, hq, hqe⟩ := hm
    have hk : q⁻¹ * (y * a * y⁻¹) ∈ π.ker ⊓ Y := by
      refine ⟨?_, ?_⟩
      · exact π.mem_ker.mpr (by rw [map_mul, map_inv, hqe, inv_mul_cancel])
      · exact Y.mul_mem (Y.inv_mem (hQ.le hq))
          (Y.mul_mem (Y.mul_mem hy (hAY ha)) (Y.inv_mem hy))
    have he : (MulAut.conj y).toMonoidHom a = q * (q⁻¹ * (y * a * y⁻¹)) := by
      simp [MulAut.conj_apply]
    rw [he]
    exact W.mul_mem (mem_sup_left hq) (mem_sup_right hk)
  have hQW : IsSylowIn p Q W := by
    refine ⟨le_sup_left, hQ.isPGroup, fun hdvd => hQ.not_dvd_relIndex ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex Q W Y le_sup_left hWY]
    exact Dvd.dvd.mul_right hdvd _
  have hQWc : Nat.card (Q.subgroupOf W) = p ^ (Nat.card W).factorization p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQW.le).toEquiv, hQW.card_eq]
  set E : Subgroup W := (A.map (MulAut.conj y).toMonoidHom).subgroupOf W with hE
  have hEp : IsPGroup p E :=
    ((hQ.isPGroup.to_le hA.1).map _).comap_of_injective W.subtype W.subtype_injective
  obtain ⟨w, hw⟩ := exists_conj_le_of_card_full hQWc hEp
  have hg : (w : H)⁻¹ * y ∈ Y := Y.mul_mem (Y.inv_mem (hWY w.2)) hy
  have hle : A.map (MulAut.conj ((w : H)⁻¹ * y)).toMonoidHom ≤ Q := by
    rintro _ ⟨a, ha, rfl⟩
    have hmem : (⟨y * a * y⁻¹, hAyW ⟨a, ha, by simp [MulAut.conj_apply]⟩⟩ : W) ∈ E :=
      Subgroup.mem_subgroupOf.mpr ⟨a, ha, by simp [MulAut.conj_apply]⟩
    have h1 := Subgroup.mem_subgroupOf.mp (hw _ hmem)
    have h2 : ((w⁻¹ * ⟨y * a * y⁻¹, hAyW ⟨a, ha, by simp [MulAut.conj_apply]⟩⟩ * w : W) : H) =
        (MulAut.conj ((w : H)⁻¹ * y)).toMonoidHom a := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    convert h1 using 1
    exact h2.symm
  have hfix := hA.2 _ hg hle
  have hWQ : W.map π ≤ Q.map π := by
    rw [hW, Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).mpr inf_le_left, sup_bot_eq]
  have hwQ : π w ∈ Q.map π := hWQ (Subgroup.mem_map_of_mem π w.2)
  obtain ⟨q, hq, hqw⟩ := hwQ
  have hy' : y = (w : H) * ((w : H)⁻¹ * y) := by group
  rw [map_map_conj, hy', map_conj_mul, hfix, ← map_map_conj, ← hqw, map_map_conj,
    hA.map_conj_eq hQ.le hq]

end Lift

section Transfer

variable {G : Type*} [Group G]

theorem IsWClosedIn.subgroupOf {H Q A Y : Subgroup G} (hA : IsWClosedIn Q A Y) (hAH : A ≤ H) :
    IsWClosedIn (Q.subgroupOf H) (A.subgroupOf H) (Y.subgroupOf H) := by
  refine ⟨fun x hx => Subgroup.mem_subgroupOf.mpr (hA.1 (Subgroup.mem_subgroupOf.mp hx)), ?_⟩
  intro g hg hle
  have hle' : A.map (MulAut.conj (g : G)).toMonoidHom ≤ Q := by
    rintro _ ⟨a, ha, rfl⟩
    have h := hle ⟨⟨a, hAH ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
    simpa [Subgroup.mem_subgroupOf, MulAut.conj_apply] using h
  have heq := hA.2 _ (Subgroup.mem_subgroupOf.mp hg) hle'
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [Subgroup.mem_subgroupOf, ← heq]
    exact ⟨a, Subgroup.mem_subgroupOf.mp ha, by simp [MulAut.conj_apply]⟩
  · intro hx
    have hx' : (x : G) ∈ A.map (MulAut.conj (g : G)).toMonoidHom := by
      rw [heq]
      exact Subgroup.mem_subgroupOf.mp hx
    obtain ⟨a, ha, hax⟩ := hx'
    refine ⟨⟨a, hAH ha⟩, Subgroup.mem_subgroupOf.mpr ha, Subtype.ext ?_⟩
    simpa [MulAut.conj_apply] using hax

theorem isSylowIn_subgroupOf {p : ℕ} {H M Q : Subgroup G} (hQ : IsSylowIn p Q (H ⊓ M)) :
    IsSylowIn p (Q.subgroupOf H) (M.subgroupOf H) := by
  have hQH : Q ≤ H := hQ.le.trans inf_le_left
  have hMH : (H ⊓ M).subgroupOf H = M.subgroupOf H := by
    ext x
    simp [Subgroup.mem_subgroupOf]
  refine ⟨fun x hx => Subgroup.mem_subgroupOf.mpr
      (hQ.le (Subgroup.mem_subgroupOf.mp hx)).2,
    hQ.isPGroup.comap_of_injective H.subtype H.subtype_injective, fun hdvd => hQ.not_dvd_relIndex ?_⟩
  have h := Subgroup.relIndex_subgroupOf (H := Q) (K := H ⊓ M) (L := H) inf_le_left
  rw [hMH] at h
  rw [← h]
  exact hdvd

end Transfer

end TenNineOneThree

variable (G : Type) [Group G] [Finite G]

@[expose] def AGL81TenNineOneThreeAiCfg : Prop :=
  Setting G → ∀ (P : Sylow 3 G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)), AGL81CfgData 3 P M H Q K →
    ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    Nonempty (↥(barM M L) ≃* alternatingGroup (Fin 7)) → H ⊓ M ≤ normalizer (L : Set G) →
    ∃ Q' : Subgroup G, IsSylowIn 3 Q' (H ⊓ M) ∧ Q ≤ Q' ∧
      ∃ A₁ A₂ : Subgroup G, A₁ ≤ Q' ⊓ L ∧ A₂ ≤ Q' ⊓ L ∧ Nat.card A₁ = 3 ∧ Nat.card A₂ = 3 ∧
        A₁ ≠ A₂ ∧ IsWClosedIn Q' A₁ (H ⊓ M ⊓ normalizer (L : Set G)) ∧
        IsWClosedIn Q' A₂ (H ⊓ M ⊓ normalizer (L : Set G))

variable {G}

section Derive

variable {H : Subgroup G} {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} [K.Normal]

theorem map_ker_agl81PiHat : (agl81PiHat H K).ker.map H.subtype = d1PlusCore 3 H K := by
  unfold agl81PiHat d1PlusCore
  rw [← MonoidHom.comap_ker, MonoidHom.ker_rangeRestrict,
    CFSG.Sporadic.Recognition.LyonsSims.ker_conjNormal_eq_centralizer K]

theorem mem_d1PlusCore_of_mem_ker {x : H} (hx : x ∈ (agl81PiHat H K).ker) :
    (x : G) ∈ d1PlusCore 3 H K := by
  rw [← map_ker_agl81PiHat]
  exact ⟨x, hx, rfl⟩

theorem eq_one_of_mem_d1PlusCore {Q' : Subgroup G} (hQ' : IsPGroup 3 Q')
    (hX : ¬ 3 ∣ Nat.card (d1PlusCore 3 H K)) {x : G} (hxQ : x ∈ Q')
    (hxX : x ∈ d1PlusCore 3 H K) : x = 1 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hQ') ⟨x, hxQ⟩
  rw [Subgroup.orderOf_mk] at hk
  have hdvd : orderOf x ∣ Nat.card (d1PlusCore 3 H K) := Subgroup.orderOf_dvd_natCard _ hxX
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rwa [pow_zero, orderOf_eq_one_iff] at hk
  · exact absurd ((dvd_pow_self 3 hk0.ne').trans (hk ▸ hdvd)) hX

theorem card_map_agl81PiHat_or {A : Subgroup G} (hAH : A ≤ H) (hA3 : Nat.card A = 3) :
    Nat.card ((A.subgroupOf H).map (agl81PiHat H K)) = 3 ∨ A ≤ d1PlusCore 3 H K := by
  have hcA : Nat.card (A.subgroupOf H) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv, hA3]
  have hd := Subgroup.card_map_dvd (H := A.subgroupOf H) (agl81PiHat H K)
  rw [hcA] at hd
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
  · right
    have hbot := Subgroup.eq_bot_of_card_eq _ h1
    rw [Subgroup.map_eq_bot_iff] at hbot
    intro a ha
    exact mem_d1PlusCore_of_mem_ker (x := ⟨a, hAH ha⟩) (hbot (Subgroup.mem_subgroupOf.mpr ha))
  · exact Or.inl h3

theorem inf_eq_bot_of_card_three {A₁ A₂ : Subgroup G} (h1 : Nat.card A₁ = 3)
    (h2 : Nat.card A₂ = 3) (hne : A₁ ≠ A₂) {b : G} (hb1 : b ∈ A₁) (hb2 : b ∈ A₂) : b = 1 := by
  by_contra hb
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hob : orderOf b = 3 := by
    have hd : orderOf b ∣ 3 := by
      rw [← h1, ← Subgroup.orderOf_mk b hb1]
      exact orderOf_dvd_natCard _
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hb
    · exact h
  have hz : Nat.card (zpowers b) = 3 := by rw [Nat.card_zpowers, hob]
  have e1 : zpowers b = A₁ :=
    Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hb1) (by rw [hz, h1])
  have e2 : zpowers b = A₂ :=
    Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hb2) (by rw [hz, h2])
  exact hne (e1.symm.trans e2)

theorem exists_orderOf_three_of_card {A : Subgroup G} (h : Nat.card A = 3) :
    ∃ a ∈ A, orderOf a = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := A) 3 (by rw [h])
  exact ⟨a, a.2, by rw [← Subgroup.orderOf_coe] at ha; exact ha⟩

end Derive

theorem agl81TenNineOneThreeWCQCfg_of_ai (hAi : AGL81TenNineOneThreeAiCfg G) :
    AGL81TenNineOneThreeWCQCfg G := by
  intro hS P M H Q K hd L hL he hYL hKn
  haveI := hKn
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q', hQ'Y, hQQ', A₁, A₂, h1L, h2L, h1c, h2c, hne, hw1, hw2⟩ :=
    hAi hS P M H Q K hd L hL he hYL
  rw [inf_eq_left.mpr hYL] at hw1 hw2
  refine ⟨Q', hQ'Y, hQQ', ?_⟩
  have hQ'H : Q' ≤ H := hQ'Y.le.trans inf_le_left
  have h1H : A₁ ≤ H := (h1L.trans inf_le_left).trans hQ'H
  have h2H : A₂ ≤ H := (h2L.trans inf_le_left).trans hQ'H
  have hYH : (H ⊓ M).subgroupOf H = M.subgroupOf H := by
    ext x
    simp [Subgroup.mem_subgroupOf]
  have hSyl := TenNineOneThree.isSylowIn_subgroupOf hQ'Y
  have hwc : ∀ {A : Subgroup G}, A ≤ H → IsWClosedIn Q' A (H ⊓ M) →
      IsWClosedIn (agl81QHat G H Q' K) ((A.subgroupOf H).map (agl81PiHat H K))
        (agl81YHat G M H K) := by
    intro A hAH hw
    have h := hw.subgroupOf hAH
    rw [hYH] at h
    rw [agl81QHat_eq, agl81YHat_eq]
    exact TenNineOneThree.isWClosedIn_map _ hSyl h
  have hQ'p : IsPGroup 3 Q' := hQ'Y.isPGroup
  have hcop : ¬ 3 ∣ Nat.card (d1PlusCore 3 H K) → ∀ {A : Subgroup G}, A ≤ Q' ⊓ L →
      Nat.card A = 3 → Nat.card ((A.subgroupOf H).map (agl81PiHat H K)) = 3 := by
    intro hX A hAL hA3
    rcases card_map_agl81PiHat_or (K := K) ((hAL.trans inf_le_left).trans hQ'H) hA3 with h | h
    · exact h
    · exfalso
      obtain ⟨a, ha, ha3⟩ := exists_orderOf_three_of_card hA3
      have := eq_one_of_mem_d1PlusCore hQ'p hX ((hAL ha).1) (h ha)
      rw [this, orderOf_one] at ha3
      omega
  have hdist : ¬ 3 ∣ Nat.card (d1PlusCore 3 H K) →
      (A₁.subgroupOf H).map (agl81PiHat H K) ≠ (A₂.subgroupOf H).map (agl81PiHat H K) := by
    intro hX heq
    obtain ⟨b, hb2, hb3⟩ := exists_orderOf_three_of_card h2c
    have hb1 : b ∉ A₁ := fun hb1 => by
      have := inf_eq_bot_of_card_three h1c h2c hne hb1 hb2
      rw [this, orderOf_one] at hb3
      omega
    have hbm : agl81PiHat H K ⟨b, h2H hb2⟩ ∈ (A₁.subgroupOf H).map (agl81PiHat H K) := by
      rw [heq]
      exact ⟨⟨b, h2H hb2⟩, Subgroup.mem_subgroupOf.mpr hb2, rfl⟩
    obtain ⟨a, ha, hab⟩ := hbm
    have hk : a⁻¹ * ⟨b, h2H hb2⟩ ∈ (agl81PiHat H K).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]
    have hxQ : ((a⁻¹ * ⟨b, h2H hb2⟩ : H) : G) ∈ Q' := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact Q'.mul_mem (Q'.inv_mem ((h1L (Subgroup.mem_subgroupOf.mp ha)).1)) (h2L hb2).1
    have h1 := eq_one_of_mem_d1PlusCore hQ'p hX hxQ (mem_d1PlusCore_of_mem_ker hk)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    have : b = (a : G) := by
      have := congrArg (fun z => (a : G) * z) h1
      simpa [mul_assoc] using this
    exact hb1 (this ▸ Subgroup.mem_subgroupOf.mp ha)
  have hrk := agl81NineThreeRankCfg_holds hS 3 P M H Q K hd
  have hnot : ¬ (A₁ ≤ d1PlusCore 3 H K ∧ A₂ ≤ d1PlusCore 3 H K) := by
    rintro ⟨hx1, hx2⟩
    obtain ⟨a, ha1, ha3⟩ := exists_orderOf_three_of_card h1c
    obtain ⟨b, hb2, hb3⟩ := exists_orderOf_three_of_card h2c
    have hab : b ∉ zpowers a := fun hb => by
      have hza : zpowers a ≤ A₁ := (Subgroup.zpowers_le).mpr ha1
      have := inf_eq_bot_of_card_three h1c h2c hne (hza hb) hb2
      rw [this, orderOf_one] at hb3
      omega
    have hnc : ¬ IsCyclic (A₁ ⊔ A₂ : Subgroup G) :=
      TenNineOneThree.not_isCyclic_of_mem (mem_sup_left ha1) (mem_sup_right hb2) ha3 hb3 hab
    have hp : IsPGroup 3 (A₁ ⊔ A₂ : Subgroup G) :=
      hQ'p.to_le (sup_le (h1L.trans inf_le_left) (h2L.trans inf_le_left))
    have h2 := two_le_pRank_of_not_isCyclic Nat.prime_three (by norm_num) hp hnc
    have hm := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) (sup_le hx1 hx2)
    omega
  rcases card_map_agl81PiHat_or (K := K) h1H h1c with h1 | h1
  · refine ⟨_, h1, hwc h1H hw1, fun hX => ⟨_, hcop hX h2L h2c, hwc h2H hw2, (hdist hX).symm⟩⟩
  · rcases card_map_agl81PiHat_or (K := K) h2H h2c with h2 | h2
    · refine ⟨_, h2, hwc h2H hw2, fun hX => ⟨_, hcop hX h1L h1c, hwc h1H hw1, hdist hX⟩⟩
    · exact absurd ⟨h1, h2⟩ hnot

end CFSG.LocalAnalysis.RankThreeTheoremC
