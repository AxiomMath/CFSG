module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A1Pre
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A2Quot
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SMHom
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A1Tau

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z g : G} {B K : Subgroup G}

theorem sec8t84a2_exists_L1 (h8B : Asc82Lemma8B) (hK : Sec8T84K G t L S z g B K) :
    ∃ L1 : Subgroup G, L1 ≤ K ∧ B ≤ L1 ∧ Nat.card L1 = 2 ^ 8 ∧ t ∉ L1 ∧
      K = zpowers t ⊔ L1 ∧ ∀ h ∈ Hsub8 t B K, ∀ x ∈ L1, h * x * h⁻¹ ∈ L1 := by
  have hctx : Sec8Ctx G t L S z g B := hK.ctx
  have htK : t ∈ K := hK.A_le sec8t84a1_t_mem_A
  have hBK : B ≤ K := sec8t84a1_B_le_A.trans hK.A_le
  have hcent : ∀ k ∈ K, ∀ b ∈ B, k * b = b * k := fun k hk b hb =>
    (Subgroup.mem_centralizer_iff.mp (hK.le_C hk).2 b hb).symm
  have hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b :=
    fun b hb b' hb' => sec8t84a1_B_comm hctx hb hb'
  have hBs : ∀ b ∈ B.subgroupOf K, ∀ k : ↥K, b * k = k * b := by
    intro b hb k
    apply Subtype.ext
    exact (hcent k k.2 (b : G) (Subgroup.mem_subgroupOf.mp hb)).symm
  have hKc : ∀ x y : ↥K, x * y * x⁻¹ * y⁻¹ ∈ B.subgroupOf K := by
    intro x y
    rw [Subgroup.mem_subgroupOf]
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hK.comm_le x x.2 y y.2
  have hK2 : ∀ x : ↥K, x * x ∈ B.subgroupOf K := by
    intro x
    rw [Subgroup.mem_subgroupOf]
    simpa only [Subgroup.coe_mul] using hK.sq_le x x.2
  have hVc : ∀ u v : ↥B, u * v = v * u := by
    intro u v
    apply Subtype.ext
    exact sec8t84a1_B_comm hctx u.2 v.2
  have hV2 : ∀ v : ↥B, v * v = 1 := by
    intro v
    apply Subtype.ext
    rw [Subgroup.coe_one]
    exact sec8t84a1_B_sq hctx v.2
  have hV16 : Nat.card ↥B = 16 := sec8t84a1_B_card hctx
  let t' : ↥K := ⟨t, htK⟩
  have ht : t' ∉ B.subgroupOf K := by
    intro h
    exact sec8t84a1_t_not_mem_B hctx (Subgroup.mem_subgroupOf.mp h)
  obtain ⟨τ, hτval⟩ := sec9m_exists_commHom (M := K) (B := B) (a := t) hBc
    (fun m hm b hb => (Subgroup.mem_centralizer_iff.mp (hK.le_C hm).2 b hb).symm)
    (fun m hm => hK.comm_le m hm t htK)
  have hτsurj : Function.Surjective τ := by
    intro v
    obtain ⟨k, hk, hkeq⟩ := hK.tau (v : G) v.2
    refine ⟨⟨k, hk⟩, ?_⟩
    apply Subtype.ext
    rw [hτval]
    exact hkeq
  have hτBs : ∀ b ∈ B.subgroupOf K, τ b = 1 := by
    intro b hb
    apply Subtype.ext
    rw [hτval b, Subgroup.coe_one]
    have hbt : (b : G) * t = t * (b : G) :=
      (sec8t84a1_t_comm hctx (Subgroup.mem_subgroupOf.mp hb)).symm
    rw [hbt]
    group
  have hτker : ∀ k : ↥K, τ k = 1 → k ∈ B.subgroupOf K ∨ ∃ b ∈ B.subgroupOf K, k = t' * b := by
    intro k hk
    have hcomm : (k : G) * t = t * (k : G) := by
      have h1 : (k : G) * t * (k : G)⁻¹ * t⁻¹ = 1 := by
        have h2 := congrArg (fun z : ↥B => (z : G)) hk
        rw [hτval k, Subgroup.coe_one] at h2
        exact h2
      calc (k : G) * t = ((k : G) * t * (k : G)⁻¹ * t⁻¹) * (t * (k : G)) := by group
        _ = t * (k : G) := by rw [h1, one_mul]
    have hA : (k : G) ∈ Asub8 t B := by
      have hmem : (k : G) ∈ K ⊓ centralizer ({t} : Set G) :=
        ⟨k.2, Subgroup.mem_centralizer_singleton_iff.mpr hcomm⟩
      rwa [hK.cent_t] at hmem
    rcases sec8t84a1_mem_A hctx hA with hb | ⟨b, hb, heq⟩
    · exact Or.inl (Subgroup.mem_subgroupOf.mpr hb)
    · refine Or.inr ⟨⟨b, hBK hb⟩, Subgroup.mem_subgroupOf.mpr hb, ?_⟩
      apply Subtype.ext
      exact heq
  let βK : ↥K → ↥K → ↥B := fun x y =>
    ⟨⁅(x : G), (y : G)⁆, by rw [commutatorElement_def]; exact hK.comm_le x x.2 y y.2⟩
  have hβval : ∀ x y : ↥K, ((βK x y : ↥B) : G) = ⁅(x : G), (y : G)⁆ := fun x y => rfl
  have hβl : ∀ x x' y : ↥K, βK (x * x') y = βK x y * βK x' y := by
    intro x x' y
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [hβval (x * x') y, hβval x y, hβval x' y]
    simp only [Subgroup.coe_mul]
    rw [commutatorElement_mul_left_eq_conj_mul]
    have hx'B : ⁅(x' : G), (y : G)⁆ ∈ B := by
      rw [commutatorElement_def]; exact hK.comm_le x' x'.2 y y.2
    have hxB : ⁅(x : G), (y : G)⁆ ∈ B := by
      rw [commutatorElement_def]; exact hK.comm_le x x.2 y y.2
    have hxc : (x : G) * ⁅(x' : G), (y : G)⁆ * (x : G)⁻¹ = ⁅(x' : G), (y : G)⁆ := by
      rw [hcent x x.2 _ hx'B]; group
    rw [hxc]
    exact (hBc _ hxB _ hx'B).symm
  have hβr : ∀ x y y' : ↥K, βK x (y * y') = βK x y * βK x y' := by
    intro x y y'
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [hβval x (y * y'), hβval x y, hβval x y']
    simp only [Subgroup.coe_mul]
    rw [commutatorElement_mul_right_eq_mul_conj]
    have hxy'B : ⁅(x : G), (y' : G)⁆ ∈ B := by
      rw [commutatorElement_def]; exact hK.comm_le x x.2 y' y'.2
    have hyc : (y : G) * ⁅(x : G), (y' : G)⁆ * (y : G)⁻¹ = ⁅(x : G), (y' : G)⁆ := by
      rw [hcent y y.2 _ hxy'B]; group
    calc ⁅(x : G), (y : G)⁆ * (y : G) * ⁅(x : G), (y' : G)⁆ * (y : G)⁻¹
        = ⁅(x : G), (y : G)⁆ * ((y : G) * ⁅(x : G), (y' : G)⁆ * (y : G)⁻¹) := by group
      _ = ⁅(x : G), (y : G)⁆ * ⁅(x : G), (y' : G)⁆ := by rw [hyc]
  have hβBl : ∀ b ∈ B.subgroupOf K, ∀ y : ↥K, βK b y = 1 := by
    intro b hb y
    apply Subtype.ext
    rw [hβval b y, Subgroup.coe_one, commutatorElement_eq_one_iff_mul_comm]
    exact (hcent y y.2 (b : G) (Subgroup.mem_subgroupOf.mp hb)).symm
  have hβBr : ∀ b ∈ B.subgroupOf K, ∀ x : ↥K, βK x b = 1 := by
    intro b hb x
    apply Subtype.ext
    rw [hβval x b, Subgroup.coe_one, commutatorElement_eq_one_iff_mul_comm]
    exact hcent x x.2 (b : G) (Subgroup.mem_subgroupOf.mp hb)
  have halt : ∀ x : ↥K, βK x x = 1 := by
    intro x
    apply Subtype.ext
    rw [hβval x x, Subgroup.coe_one, commutatorElement_self]
  have hβt : ∀ x : ↥K, βK x t' = τ x := by
    intro x
    apply Subtype.ext
    rw [hβval x t', hτval x]
    rfl
  let σ : ↥(Hsub8 t B K) → ↥K ≃* ↥K := fun x =>
    K.normalizerMonoidHom ⟨(x : G),
      Subgroup.mem_normalizer_iff.mpr (sec8t84a1_mem_H.mp x.2).2.1⟩
  have hσapply : ∀ (x : ↥(Hsub8 t B K)) (k : ↥K),
      ((σ x k : ↥K) : G) = (x : G) * (k : G) * (x : G)⁻¹ := fun x k =>
    Subgroup.normalizerMonoidHom_apply_apply_coe K
      ⟨(x : G), Subgroup.mem_normalizer_iff.mpr (sec8t84a1_mem_H.mp x.2).2.1⟩ k
  let ρ : ↥(Hsub8 t B K) → ↥B ≃* ↥B := fun x =>
    B.normalizerMonoidHom ⟨(x : G),
      sec8t84a1_N_le_normalizer h8B hctx (sec8t84a1_mem_H.mp x.2).1⟩
  have hρapply : ∀ (x : ↥(Hsub8 t B K)) (b : ↥B),
      ((ρ x b : ↥B) : G) = (x : G) * (b : G) * (x : G)⁻¹ := fun x b =>
    Subgroup.normalizerMonoidHom_apply_apply_coe B
      ⟨(x : G), sec8t84a1_N_le_normalizer h8B hctx (sec8t84a1_mem_H.mp x.2).1⟩ b
  have hσBs : ∀ (x : ↥(Hsub8 t B K)) (k : ↥K),
      σ x k ∈ B.subgroupOf K ↔ k ∈ B.subgroupOf K := by
    intro x k
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hσapply x k]
    exact (Subgroup.mem_normalizer_iff.mp
      (sec8t84a1_N_le_normalizer h8B hctx (sec8t84a1_mem_H.mp x.2).1) (k : G)).symm
  have hσt : ∀ x : ↥(Hsub8 t B K), σ x t' = t' := by
    intro x
    apply Subtype.ext
    rw [hσapply x t']
    change (x : G) * t * (x : G)⁻¹ = t
    rw [(sec8t84a1_mem_H.mp x.2).2.2]
    group
  have hτσ : ∀ (x : ↥(Hsub8 t B K)) (k : ↥K), τ (σ x k) = ρ x (τ k) := by
    intro x k
    apply Subtype.ext
    rw [hτval (σ x k), hσapply x k, hρapply x (τ k), hτval k]
    exact sec8t84a1_tau_conj (sec8t84a1_mem_H.mp x.2).2.2
  have hβσ : ∀ (x : ↥(Hsub8 t B K)) (k k' : ↥K),
      βK (σ x k) (σ x k') = ρ x (βK k k') := by
    intro x k k'
    apply Subtype.ext
    rw [hβval (σ x k) (σ x k'), hσapply x k, hσapply x k',
      hρapply x (βK k k'), hβval k k']
    exact (conjugate_commutatorElement (g₁ := (k : G)) (g₂ := (k' : G)) (g₃ := (x : G))).symm
  obtain ⟨L1', hBsL1', htL1', hcover, hinv⟩ :=
    sec8t84a2_quot_split (K := ↥K) (V := ↥B) (X := ↥(Hsub8 t B K))
      (Bs := B.subgroupOf K) hBs hKc hK2 hVc hV2 hV16 t' ht τ hτsurj hτBs hτker
      βK hβl hβr hβBl hβBr halt hβt σ ρ hσBs hσt hτσ hβσ
  let L1 : Subgroup G := L1'.map K.subtype
  have hL1_le_K : L1 ≤ K := by
    intro x hx
    obtain ⟨a, _ha, rfl⟩ := Subgroup.mem_map.mp hx
    exact a.2
  have hB_le_L1 : B ≤ L1 := by
    intro b hb
    dsimp only [L1]
    exact Subgroup.mem_map.mpr
      ⟨⟨b, hBK hb⟩, hBsL1' (Subgroup.mem_subgroupOf.mpr hb), rfl⟩
  have hidx : L1'.index = 2 := by
    rw [Subgroup.index_eq_two_iff_exists_notMem_and]
    exact ⟨t', htL1', fun b => (hcover b).symm⟩
  have hcardL1' : Nat.card L1' = 2 ^ 8 := by
    have h := Subgroup.card_mul_index (H := L1')
    rw [hidx, hK.card] at h
    norm_num at h
    omega
  have hcard : Nat.card L1 = 2 ^ 8 := by
    dsimp only [L1]
    rw [Subgroup.card_subtype K L1', hcardL1']
  have htL1G : t ∉ L1 := by
    intro ht
    dsimp only [L1] at ht
    obtain ⟨a, ha, haeq⟩ := Subgroup.mem_map.mp ht
    have haz : a = t' := by
      apply Subtype.ext
      exact haeq
    rw [haz] at ha
    exact htL1' ha
  have hsup : K = zpowers t ⊔ L1 := by
    apply le_antisymm
    · intro x hx
      let x' : ↥K := ⟨x, hx⟩
      rcases hcover x' with hx' | hx'
      · exact Subgroup.mem_sup_right (Subgroup.mem_map.mpr ⟨x', hx', rfl⟩)
      · have hxt : x * t ∈ L1 := Subgroup.mem_map.mpr ⟨x' * t', hx', rfl⟩
        have htinv : t⁻¹ ∈ zpowers t := (Subgroup.zpowers t).inv_mem (Subgroup.mem_zpowers t)
        have hxeq : x = (x * t) * t⁻¹ := by group
        rw [hxeq, sup_comm]
        exact Subgroup.mul_mem_sup hxt htinv
    · rw [sup_le_iff]
      exact ⟨Subgroup.zpowers_le.mpr htK, hL1_le_K⟩
  have hinvL1 : ∀ h ∈ Hsub8 t B K, ∀ x ∈ L1, h * x * h⁻¹ ∈ L1 := by
    intro h hh x hx
    dsimp only [L1] at hx ⊢
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_map.mpr
      ⟨σ ⟨h, hh⟩ a, hinv ⟨h, hh⟩ a ha, hσapply ⟨h, hh⟩ a⟩
  exact ⟨L1, hL1_le_K, hB_le_L1, hcard, htL1G, hsup, hinvL1⟩

end CFSG.OddStandard.SmallF3.Omega
