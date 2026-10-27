
module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSub
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporNorm
public import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalCore
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

theorem card_evenWeight_three : Nat.card (evenWeight 3) = 4 := by
  classical
  have h : Nat.card (evenWeight 3) = Nat.card {x : Fin 3 → ZMod 2 // ∑ i, x i = 0} := by
    apply Nat.card_congr
    exact (Equiv.subtypeEquivRight (fun x => by simp [evenWeight, AddMonoidHom.mem_ker]))
  rw [h, Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

theorem conj_mem_commutator {G : Type*} [Group G] {H₁ H₂ : Subgroup G} {g : G}
    (h1 : g ∈ Subgroup.normalizer (H₁ : Set G)) (h2 : g ∈ Subgroup.normalizer (H₂ : Set G))
    {x : G} (hx : x ∈ ⁅H₁, H₂⁆) : g * x * g⁻¹ ∈ ⁅H₁, H₂⁆ := by
  have hmap : (⁅H₁, H₂⁆).map (MulAut.conj g).toMonoidHom ≤ ⁅H₁, H₂⁆ := by
    rw [Subgroup.map_commutator]
    refine Subgroup.commutator_mono ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.1 h1 y).1 hy
    · rintro _ ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.1 h2 y).1 hy
  exact hmap ⟨x, hx, rfl⟩

theorem alt3_commutator_bound {G : Type*} [Group G] [Finite G] {K B : Subgroup G}
    (hB : IsChi0Block K B) (h3 : IsAltType B 3) {Q : Subgroup G} (hQK : Q ≤ K)
    (hQn : (Q.subgroupOf K).Normal) (hQ : IsPGroup 2 Q) :
    ∃ b : G, b ∈ K ∧ orderOf b = 3 ∧ Nat.card ↥⁅Q, Subgroup.zpowers b⁆ ≤ 4 := by
  classical
  obtain ⟨⟨hshort, hBK, hsub⟩, -⟩ := hB
  obtain ⟨α, hαs, hαk, β, hβs, hβk, -⟩ := h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc3 : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  have h3dvd : 3 ∣ Nat.card ↥B := by
    have := Subgroup.card_dvd_of_surjective hαs
    rwa [hc3] at this
  obtain ⟨b₀, hb₀⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
  set b : G := (b₀ : G) with hbdef
  have hbB : b ∈ B := b₀.2
  have hbK : b ∈ K := hBK hbB
  have hord : orderOf b = 3 := by rw [hbdef, Subgroup.orderOf_coe, hb₀]
  have hodd : Odd (orderOf b) := by rw [hord]; decide
  refine ⟨b, hbK, hord, ?_⟩
  set C : Subgroup G := ⁅Q, Subgroup.zpowers b⁆ with hC
  have hQ' : IsPGroup 2 (Q.subgroupOf K) := hQ.comap_subtype
  have hb'K : (⟨b, hbK⟩ : ↥K) ∈ B.subgroupOf K := hbB
  have hoddK : Odd (orderOf (⟨b, hbK⟩ : ↥K)) := by
    rw [← Subgroup.orderOf_coe (⟨b, hbK⟩ : ↥K)]
    exact hodd
  have hmapQ : (Q.subgroupOf K).map K.subtype = Q := by
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.2 hQK
  have hmapP : (Subgroup.zpowers (⟨b, hbK⟩ : ↥K)).map K.subtype = Subgroup.zpowers b :=
    MonoidHom.map_zpowers K.subtype _
  have hmapB : (B.subgroupOf K).map K.subtype = B := by
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.2 hBK
  have hCmap : (⁅Q.subgroupOf K, Subgroup.zpowers (⟨b, hbK⟩ : ↥K)⁆).map K.subtype = C := by
    rw [Subgroup.map_commutator, hmapQ, hmapP]
  have hCB : C ≤ B := by
    have h1 := commutator_le_of_isSubnormal hsub hQ' hb'K hoddK
    have h2 := Subgroup.map_mono (f := K.subtype) h1
    rwa [hCmap, hmapB] at h2
  have hidem : ⁅C, Subgroup.zpowers b⁆ = C := by
    have h1 := commutator_zpowers_idem hQ' hoddK
    have h2 := congrArg (Subgroup.map K.subtype) h1
    rw [Subgroup.map_commutator, Subgroup.map_commutator, hmapQ, hmapP] at h2
    exact h2
  have hCQ : C ≤ Q := by
    rw [hC, Subgroup.commutator_le]
    intro q hq p hp
    have hpK : p ∈ K := by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hp
      exact K.zpow_mem hbK n
    have hconj := (Subgroup.normal_subgroupOf_iff hQK).1 hQn
    have h1 : p * q⁻¹ * p⁻¹ ∈ Q := hconj (q⁻¹) p (Q.inv_mem hq) hpK
    have h2 : ⁅q, p⁆ = q * (p * q⁻¹ * p⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [h2]
    exact Q.mul_mem hq h1
  have hEn : ((Q ⊓ B).subgroupOf B).Normal := by
    rw [Subgroup.normal_subgroupOf_iff (inf_le_right : Q ⊓ B ≤ B)]
    intro h g hh hg
    refine ⟨?_, B.mul_mem (B.mul_mem hg hh.2) (B.inv_mem hg)⟩
    exact (Subgroup.normal_subgroupOf_iff hQK).1 hQn h g hh.1 (hBK hg)
  have hE2 : IsPGroup 2 (Q ⊓ B : Subgroup G) := hQ.to_le inf_le_left
  have hEle : Q ⊓ B ≤ pCoreOf 2 B :=
    CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 (Q ⊓ B) B inf_le_right hEn hE2
  have hCQb : C ≤ blockQ B := fun c hc => hEle (Subgroup.mem_inf.2 ⟨hCQ hc, hCB hc⟩)
  have hCU : C ≤ blockU B := by
    rw [← hidem]
    exact Subgroup.commutator_mono hCQb (Subgroup.zpowers_le.2 hbB)
  obtain ⟨hUle, hUexp⟩ := hshort.2.2.1
  have hcomm : ∀ x ∈ blockU B, ∀ y ∈ blockU B, x * y = y * x := by
    intro x hx y hy
    exact Subgroup.mem_centralizer_iff.1 (hUle hy).2 x (hUle hx).1
  have hexp : ∀ x ∈ blockU B, x * x = 1 := fun x hx => by
    rw [← pow_two]
    exact hUexp x hx
  have hbn : b ∈ Subgroup.normalizer (blockQ B : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 B hbB
  have hnorm : ∀ x ∈ blockU B, b * x * b⁻¹ ∈ blockU B := fun x hx =>
    conj_mem_commutator hbn (Subgroup.le_normalizer hbB) hx
  have hb3 : b * b * b = 1 := by
    have := pow_orderOf_eq_one b
    rw [hord] at this
    simpa [pow_succ] using this
  obtain ⟨hVU, hVc⟩ := commutator_zpowers_inf_centralizer (blockU B) b hb3 hnorm hcomm hexp
  have hCV : C ≤ ⁅blockU B, Subgroup.zpowers b⁆ :=
    calc C = ⁅C, Subgroup.zpowers b⁆ := hidem.symm
      _ ≤ ⁅blockU B, Subgroup.zpowers b⁆ := Subgroup.commutator_mono hCU le_rfl
  set V : Subgroup G := ⁅blockU B, Subgroup.zpowers b⁆ with hV
  have hinj : Function.Injective (β.comp (V.subgroupOf (blockU B)).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx' : (x : ↥(blockU B)) ∈ β.ker := hx
    rw [hβk, Subgroup.mem_subgroupOf] at hx'
    have hxc : b * (((x : ↥(blockU B)) : G)) = ((x : ↥(blockU B)) : G) * b := by
      have := Subgroup.mem_centralizer_iff.1 hx'.2 b hbB
      exact this
    have hxV : (((x : ↥(blockU B)) : G)) ∈ V := x.2
    have h1 := hVc _ hxV hxc
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    apply Subtype.ext
    exact h1
  have hcardV : Nat.card (V.subgroupOf (blockU B)) ≤ 4 := by
    have h1 := Nat.card_le_card_of_injective _ hinj
    have h2 : Nat.card (Multiplicative (evenWeight 3)) = 4 := by
      rw [Nat.card_congr Multiplicative.toAdd]
      exact card_evenWeight_three
    rwa [h2] at h1
  calc Nat.card ↥C ≤ Nat.card ↥V := Subgroup.card_le_of_le hCV
    _ = Nat.card (V.subgroupOf (blockU B)) :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVU).toEquiv).symm
    _ ≤ 4 := hcardV

end CFSG.QuasithinUnique.Vol2Native.L239
