module

public import CFSG.GH74.GLS.C3.Layer1.Th2P617K
public import CFSG.GH74.GLS.C3.Layer1.Th2P617I
public import CFSG.GH74.GLS.C3.Layer1.Th2P617J
public import CFSG.GH74.GLS.C3.Layer1.Th2P64K

public section

namespace CFSG.GH74.GLS.Th2.Obs

open Equiv Equiv.Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK
  CFSG.GH74.GLS.Th2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {x y : G} {K T S : Subgroup G}

omit [Finite G] in
theorem mem_normalizer_of_conj_mem' {H : Subgroup G} {v : G} (h1 : ∀ n ∈ H, v * n * v⁻¹ ∈ H)
    (h2 : ∀ n ∈ H, v⁻¹ * n * v ∈ H) : v ∈ normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨h1 n, fun hn => ?_⟩
  have := h2 _ hn
  simpa [mul_assoc] using this

theorem false_of_zE (hL34 : B_gen4_noL34_elem) (h102 : B_ivk_10_2) (hG : C3Hyp G)
    (hs : Th2Std x y K T S) (h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7)))
    (hQ2 : pRank 2 ↥(T ⊓ CxK x K) ≤ 2) {B : Subgroup G}
    (hB : IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B) {b : G} {J : Subgroup G} (hobs : Obstr52 B b J)
    {U E : Subgroup G} (hU : IsFourSub (T ⊓ K) U) (hES : IsS (T ⊓ CxK x K) E)
    (hE2 : 2 ≤ pRank 2 ↥E) (hBdef : B = U ⊔ E) {z : G} (hzU : z ∈ U) (hz1 : z ≠ 1)
    (hzc : ∀ p ∈ T ⊓ K, p * z = z * p)
    (hzu : ∀ w ∈ T ⊓ K, (∀ p ∈ T ⊓ K, p * w = w * p) → w = 1 ∨ w = z)
    (hP8 : Nat.card ↥(T ⊓ K) = 8) {e : G} (heE : e ∈ E) (he1 : e ≠ 1) (hb : b = z * e) :
    False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eK⟩ := h7
  have hcen := centerlessBar_of_A7 ⟨eK⟩
  have hcd := hs.commDisj hcen
  have hG4 : pRank 2 G ≤ 4 := hG.pRank_eq_four.le
  have hKn := hs.K_normal_A7 hG ⟨eK⟩
  have hE4 : IsE 4 ⊤ B := isE_of_isSn le_top hB le_rfl
  have hBel : CFSG.IsElementaryAbelian 2 ↥B := hE4.2.1
  have hBR : B ≤ (T ⊓ K) ⊔ (T ⊓ CxK x K) := hB.1.1
  have hBT : B ≤ T := hBR.trans (sup_le inf_le_left inf_le_left)
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hBel
  obtain ⟨eJ⟩ := hobs.nonempty_A7_of_rank_four hG4 hBel
  have hEQ : E ≤ T ⊓ CxK x K := hES.1
  have hUP : U ≤ T ⊓ K := hU.1
  have hUB : U ≤ B := hBdef ▸ le_sup_left
  have hEB : E ≤ B := hBdef ▸ le_sup_right
  have hzB : z ∈ B := hUB hzU
  have heB : e ∈ B := hEB heE
  have hbB : b ∈ B := hobs.mem
  have hzP : z ∈ T ⊓ K := hUP hzU
  have hecomm : ∀ p ∈ T ⊓ K, p * e = e * p := fun p hp => hcd.comm p hp e (hEQ heE)
  have hbP : b ∉ T ⊓ K := by
    intro hbP
    have hzinv : z⁻¹ ∈ T ⊓ K := (T ⊓ K).inv_mem hzP
    have heP : e ∈ T ⊓ K := by
      have := (T ⊓ K).mul_mem hzinv hbP
      rwa [hb, ← mul_assoc, inv_mul_cancel, one_mul] at this
    exact he1 (hcd.eq_one_of_mem heP (hEQ heE))
  have hbE : b ∉ E := by
    intro hbE
    have hzE : z ∈ E := by
      have := E.mul_mem hbE (E.inv_mem heE)
      rwa [hb, mul_assoc, mul_inv_cancel, mul_one] at this
    exact hz1 (hcd.eq_one_of_mem hzP (hEQ hzE))
  have hbC : b ∉ CxK x K := by
    intro hbC
    have hzC : z ∈ CxK x K := by
      have := (CxK x K).mul_mem hbC ((CxK x K).inv_mem (hEQ heE).2)
      rwa [hb, mul_assoc, mul_inv_cancel, mul_one] at this
    exact hz1 (hcd.eq_one_of_mem hzP ⟨hzP.1, hzC⟩)
  set V : Subgroup G := T ⊓ centralizer ({b} : Set G) with hV
  have hBV : B ≤ V := fun β hβ => ⟨hBT hβ, hobs.B_le_centralizer hBel hβ⟩
  have hVN : V ≤ normalizer (J : Set G) := inf_le_right.trans (hobs.centralizer_le_normalizer hG4 hBel)
  have hV2 : IsPGroup 2 ↥V := hs.T_pGroup.to_inf_left
  have hPV : T ⊓ K ≤ V := by
    intro p hp
    refine ⟨hp.1, mem_centralizer_singleton_iff.2 ?_⟩
    rw [hb]
    calc p * (z * e) = (p * z) * e := by group
      _ = (z * p) * e := by rw [hzc p hp]
      _ = z * (p * e) := by group
      _ = z * (e * p) := by rw [hecomm p hp]
      _ = z * e * p := by group
  obtain ⟨F, t, hF, ht, hdis, hrange⟩ := hobs.exists_image_B hG4 hBel eJ hBV hVN
  set ψ := actOn eJ hVN with hψ
  have hWmem : ∀ β (hβ : β ∈ B), ψ ⟨β, hBV hβ⟩ ∈ F ⊔ zpowers t := fun β hβ => by
    rw [← hrange]
    exact ⟨⟨β, hβ⟩, rfl⟩
  have hWsurj : ∀ w ∈ F ⊔ zpowers t, ∃ β, ∃ hβ : β ∈ B, ψ ⟨β, hBV hβ⟩ = w := by
    intro w hw
    rw [← hrange] at hw
    obtain ⟨⟨β, hβ⟩, rfl⟩ := hw
    exact ⟨β, hβ, rfl⟩
  have hKnJ : ∀ m ∈ centralizer ({b} : Set G), ∀ k ∈ J, m * k * m⁻¹ ∈ J := fun m hm k hk =>
    (Subgroup.mem_normalizer_iff.1 (hobs.centralizer_le_normalizer hG4 hBel hm) k).1 hk
  have hPinj : ∀ p ∈ T ⊓ K, ∀ hp : p ∈ V, ψ ⟨p, hp⟩ = 1 → p = 1 := by
    intro p hpP hpV hψ1
    by_contra hp1
    set N : Subgroup G := (T ⊓ K) ⊓ CxK b J with hN
    have hpN : p ∈ N := ⟨hpP, hpV.2, (actOn_eq_one_iff eJ hVN hpV).1 hψ1⟩
    have hN1 : N ≠ ⊥ := fun h => hp1 (by
      have := h ▸ hpN
      simpa using this)
    have hconj : ∀ v ∈ V, ∀ n ∈ N, v * n * v⁻¹ ∈ N := by
      intro v hv n hn
      refine ⟨?_, CxK_conj_mem hKnJ hv.2 hn.2⟩
      exact (Subgroup.mem_normalizer_iff.1 (hs.mem_normalizer_P hKn hv.1) n).1 hn.1
    have hNn : V ≤ normalizer (N : Set G) := fun v hv =>
      mem_normalizer_of_conj_mem' (hconj v hv) (fun n hn => by
        simpa using hconj v⁻¹ (V.inv_mem hv) n hn)
    have hbN := hobs.b_mem_of_normal_ker hG4 hBel hE4.2.2 (X := V) hV2 hBV (N := N)
      (fun n hn => hPV hn.1) hNn inf_le_right hN1
    exact hbP hbN.1
  have hEinj : ∀ g ∈ E, ∀ hg : g ∈ V, ψ ⟨g, hg⟩ = 1 → g = 1 := by
    intro g hgE hgV hψ1
    have hgs : g ∈ centralizerSection J (pPrimeCoreOf 2 J) := (actOn_eq_one_iff eJ hVN hgV).1 hψ1
    rcases hobs.B_inf_ker hG4 hBel hE4.2.2 (hEB hgE) hgs with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hgE) hbE
  let ι : ↥(E.subgroupOf V) →* Perm (Fin 7) := ψ.comp (E.subgroupOf V).subtype
  have hιinj : Function.Injective ι := by
    refine (injective_iff_map_eq_one ι).2 fun a ha => ?_
    obtain ⟨⟨g, hgV⟩, hgE⟩ := a
    have : g = 1 := hEinj g hgE hgV ha
    subst this
    rfl
  have hE4' : Nat.card ↥E = 4 := by
    have h1 := C3.Layer1.Back.card_eq_two_pow_pRank hES.2.1
    have h2 : pRank 2 ↥E ≤ 2 := (C3.Layer1.Back.pRank_mono' hEQ).trans hQ2
    have h3 : pRank 2 ↥E = 2 := le_antisymm h2 hE2
    rw [h1, h3]; norm_num
  have hHcard : Nat.card ↥ι.range = 4 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hιinj).toEquiv]
    have : Nat.card ↥(E.subgroupOf V) = Nat.card ↥E :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hEB.trans hBV)).toEquiv
    rw [this, hE4']
  have hHW : ι.range ≤ F ⊔ zpowers t := by
    rintro _ ⟨⟨⟨g, hgV⟩, hgE⟩, rfl⟩
    exact hWmem g (hEB hgE)
  have htH : t ∉ ι.range := by
    rintro ⟨⟨⟨g, hgV⟩, hgE⟩, hgt⟩
    have hgψ : ψ ⟨g, hgV⟩ = t := hgt
    have hesw : (a7Act J eJ ⟨g, hVN hgV⟩).IsSwap := by
      have : a7Act J eJ ⟨g, hVN hgV⟩ = ψ ⟨g, hgV⟩ := rfl
      rw [this, hgψ]
      exact ht
    exact false_of_swap_in_E_A7 hL34 h102 hG hs ⟨eK⟩ hBel hobs eJ hzP.2 hzB (hEQ heE).2 heB
      hb.symm hbC (hEQ hgE).2 (hEB hgE) (hVN hgV) hesw
  obtain ⟨u₁, hu₁U, hu₁1, hu₁z⟩ : ∃ u ∈ U, u ≠ 1 ∧ u ≠ z := by
    by_contra hcon
    push Not at hcon
    have hUz : U ≤ zpowers z := fun u hu => by
      by_cases h1 : u = 1
      · rw [h1]; exact one_mem _
      · rw [hcon u hu h1]; exact mem_zpowers z
    have hzo : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact hBsq z hzB) hz1
    have := Subgroup.card_le_of_le hUz
    rw [Nat.card_zpowers, hzo, hU.2.2] at this
    omega
  obtain ⟨p, hpP, hpu⟩ : ∃ p ∈ T ⊓ K, p * u₁ ≠ u₁ * p := by
    by_contra hcon
    push Not at hcon
    rcases hzu u₁ (hUP hu₁U) (fun p hp => hcon p hp) with h | h
    · exact hu₁1 h
    · exact hu₁z h
  have hpV : p ∈ V := hPV hpP
  have hnormU := normal_of_isFourSub_of_card_eight hP8 hU
  have hpB : ∀ β ∈ B, p * β * p⁻¹ ∈ B := by
    intro β hβ
    have hβ' : β ∈ U ⊔ E := hBdef ▸ hβ
    obtain ⟨u, hu, e', he', rfl⟩ := exists_mul_of_mem_sup_of_commute
      (fun u hu q hq => hBc u (hUB hu) q (hEB hq)) hβ'
    have hc : p * e' * p⁻¹ = e' := by
      calc p * e' * p⁻¹ = e' * p * p⁻¹ := by rw [hcd.comm p hpP e' (hEQ he')]
        _ = e' := by group
    have h1 : p * (u * e') * p⁻¹ = (p * u * p⁻¹) * e' := by
      calc p * (u * e') * p⁻¹ = (p * u * p⁻¹) * (p * e' * p⁻¹) := by group
        _ = (p * u * p⁻¹) * e' := by rw [hc]
    rw [h1]
    exact B.mul_mem (hUB (hnormU u hu p hpP)) (hEB he')
  have hgN : ∀ w ∈ F ⊔ zpowers t, ψ ⟨p, hpV⟩ * w * (ψ ⟨p, hpV⟩)⁻¹ ∈ F ⊔ zpowers t := by
    intro w hw
    obtain ⟨β, hβ, rfl⟩ := hWsurj w hw
    have hpβ := hpB β hβ
    have hpβV : p * β * p⁻¹ ∈ V := hBV hpβ
    have : ψ ⟨p, hpV⟩ * ψ ⟨β, hBV hβ⟩ * (ψ ⟨p, hpV⟩)⁻¹ = ψ ⟨p * β * p⁻¹, hpβV⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [this]
    exact hWmem _ hpβ
  have hgH : ∀ h ∈ ι.range, ψ ⟨p, hpV⟩ * h = h * ψ ⟨p, hpV⟩ := by
    rintro _ ⟨⟨⟨g, hgV⟩, hgE⟩, rfl⟩
    show ψ ⟨p, hpV⟩ * ψ ⟨g, hgV⟩ = ψ ⟨g, hgV⟩ * ψ ⟨p, hpV⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcd.comm p hpP g (hEQ hgE))
  have hcent := IsRootFour.centralizes_of_normalizes hF ht hdis hgN hHW hHcard htH hgH
  have hu₁V : u₁ ∈ V := hBV (hUB hu₁U)
  have hψc : ψ ⟨p, hpV⟩ * ψ ⟨u₁, hu₁V⟩ = ψ ⟨u₁, hu₁V⟩ * ψ ⟨p, hpV⟩ :=
    hcent _ (hWmem u₁ (hUB hu₁U))
  have hcomm_mem : p * u₁ * p⁻¹ * u₁⁻¹ ∈ T ⊓ K :=
    (T ⊓ K).mul_mem ((T ⊓ K).mul_mem ((T ⊓ K).mul_mem hpP (hUP hu₁U)) ((T ⊓ K).inv_mem hpP))
      ((T ⊓ K).inv_mem (hUP hu₁U))
  have hcommV : p * u₁ * p⁻¹ * u₁⁻¹ ∈ V := hPV hcomm_mem
  have hψcomm : ψ ⟨p * u₁ * p⁻¹ * u₁⁻¹, hcommV⟩ = 1 := by
    have h1 : (⟨p * u₁ * p⁻¹ * u₁⁻¹, hcommV⟩ : ↥V) = ⟨p, hpV⟩ * ⟨u₁, hu₁V⟩ * ⟨p, hpV⟩⁻¹ *
        ⟨u₁, hu₁V⟩⁻¹ := rfl
    rw [h1, map_mul, map_mul, map_mul, map_inv, map_inv]
    have h2 : ⁅ψ ⟨p, hpV⟩, ψ ⟨u₁, hu₁V⟩⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 hψc
    rw [commutatorElement_def] at h2
    exact h2
  have h3 := hPinj _ hcomm_mem hcommV hψcomm
  have h4 : ⁅p, u₁⁆ = 1 := by
    rw [commutatorElement_def]
    exact h3
  exact hpu (commutatorElement_eq_one_iff_mul_comm.1 h4)

end CFSG.GH74.GLS.Th2.Obs
