module

public import CFSG.GH74.GLS.C3.Layer1.Th2P412Cls
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.IG1516
public import CFSG.GH74.GLS.C3.Layer1.Th2P615Fus
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.P43f
  CFSG.GH74.GLS.C3.Layer1.Back CFSG.GH74.GLS.C3.Layer1.Bk
open scoped commutatorElement

namespace Th2.P43f

variable {G : Type} [Group G] {x : G} {K T S : Subgroup G} {a z : G} {psi : G → Equiv.Perm (Fin 7)}

namespace Frame

variable (F : Frame x K T S a z psi)

include F

theorem relIndex_le_two [Finite G] : T.relIndex S ≤ 2 := by
  have hcard : Nat.card ↥S ≤ 2 * Nat.card ↥T := by
    have hcover : (S : Set G) ⊆ (T : Set G) ∪ (fun t => a * t) '' (T : Set G) := by
      intro s hs
      rcases F.S_cases s hs with h | h
      · exact Or.inl h
      · exact Or.inr ⟨a⁻¹ * s, h, by group⟩
    have h1 : (S : Set G).ncard ≤ ((T : Set G) ∪ (fun t => a * t) '' (T : Set G)).ncard :=
      Set.ncard_le_ncard hcover (Set.toFinite _)
    have h2 := Set.ncard_union_le (T : Set G) ((fun t => a * t) '' (T : Set G))
    have h3 : ((fun t => a * t) '' (T : Set G)).ncard ≤ (T : Set G).ncard :=
      Set.ncard_image_le (Set.toFinite _)
    have h4 : Nat.card ↥S = (S : Set G).ncard := Nat.card_coe_set_eq (S : Set G)
    have h5 : Nat.card ↥T = (T : Set G).ncard := Nat.card_coe_set_eq (T : Set G)
    omega
  have hmul := Subgroup.relIndex_mul_card T S
  have hTS : T ≤ S := F.core.T_le_S
  rw [inf_eq_left.2 hTS] at hmul
  have hpos : 0 < Nat.card ↥T := Nat.card_pos
  by_contra hcon
  push Not at hcon
  have : 3 * Nat.card ↥T ≤ Nat.card ↥S := by
    rw [← hmul]
    exact Nat.mul_le_mul_right _ hcon
  omega

theorem isConj_x_or_v_of_involution [Finite G] (hG : C3Hyp G) {y : G} (hs : Th2Std x y K T S)
    (e7 : kBar K ≃* alternatingGroup (Fin 7)) (hP2 : 2 ≤ pRank 2 ↥(T ⊓ K))
    (hQ4 : Nat.card ↥(T ⊓ CxK x K) = 4) {u : G} (hu2 : orderOf u = 2) :
    IsConj x u ∨ IsConj (z * x) u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu1 : u * u = 1 := by
    have h1 : u ^ 2 = 1 := by rw [← hu2]; exact pow_orderOf_eq_one u
    rwa [sq] at h1
  have hup : IsPGroup 2 ↥(zpowers u) :=
    (CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one (by rw [← sq] at hu1; exact hu1)).isPGroup 2 _
  obtain ⟨g, -, hgW⟩ := Th2.exists_cj_le_of_isSylowOf hs.sylowS le_top hup
  have hmem : g * u * g⁻¹ ∈ S := by
    refine hgW ((mem_cj_iff g _ _).2 ?_)
    have e : g⁻¹ * (g * u * g⁻¹) * g = u := by group
    rw [e]
    exact mem_zpowers u
  have hord : orderOf (g * u * g⁻¹) = 2 := by
    rw [CFSG.BenderGlauberman.orderOf_conj_eq]; exact hu2
  have hsq : (g * u * g⁻¹) * (g * u * g⁻¹) = 1 := by
    calc (g * u * g⁻¹) * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
      _ = 1 := by rw [hu1]; group
  have hne : g * u * g⁻¹ ≠ 1 := by
    intro h
    have : orderOf (g * u * g⁻¹) = 1 := by rw [h]; exact orderOf_one
    omega
  have hT : ∀ u₁ : G, u₁ ∈ T → u₁ * u₁ = 1 → u₁ ≠ 1 → IsConj u₁ u →
      IsConj x u ∨ IsConj (z * x) u := by
    intro u₁ h1 h2 h3 h4
    rcases F.isConj_x_or_v_of_involution_T hG hs e7 hP2 hQ4 h1 h2 h3 with h5 | h5
    · exact Or.inl (h5.trans h4)
    · exact Or.inr (h5.trans h4)
  have hconj : IsConj (g * u * g⁻¹) u := isConj_iff.2 ⟨g⁻¹, by group⟩
  by_cases hTmem : g * u * g⁻¹ ∈ T
  · exact hT _ hTmem hsq hne hconj
  ·
    have hperf : (g * u * g⁻¹) ∈ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ ⊔ ⊥ := by
      rw [sup_bot_eq]
      have : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤ := by
        obtain ⟨hsimple, hnab, -⟩ := isKProperSimple_iff.1 hG.kproper
        have hnormal : (⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆).Normal := by
          have : (commutator G).Normal := inferInstance
          simpa [commutator_def] using this
        have := hnormal
        rcases hsimple.eq_bot_or_eq_top_of_normal (⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆) with h | h
        · exfalso
          obtain ⟨p, q, hpq⟩ := hnab
          apply hpq
          have h1 : ⁅p, q⁆ ∈ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ :=
            Subgroup.commutator_mem_commutator (Subgroup.mem_top p) (Subgroup.mem_top q)
          rw [h, Subgroup.mem_bot] at h1
          exact commutatorElement_eq_one_iff_mul_comm.1 h1
        · exact h
      rw [this]
      exact Subgroup.mem_top _
    obtain ⟨c, -, hcT, -⟩ := Stage1.Thm3.Sec5.ig_15_16_ext_thm G ⊤ S T ⊥ (g * u * g⁻¹) hs.sylowS
      F.core.T_le_S F.relIndex_le_two bot_le (fun _ _ n hn => by
        rw [Subgroup.mem_bot] at hn
        rw [hn]; simp) (by rw [Subgroup.card_bot]; exact odd_one) hmem hord hperf
    have hcsq : (c⁻¹ * (g * u * g⁻¹) * c) * (c⁻¹ * (g * u * g⁻¹) * c) = 1 := by
      calc (c⁻¹ * (g * u * g⁻¹) * c) * (c⁻¹ * (g * u * g⁻¹) * c)
          = c⁻¹ * ((g * u * g⁻¹) * (g * u * g⁻¹)) * c := by group
        _ = 1 := by rw [hsq]; group
    have hcne : c⁻¹ * (g * u * g⁻¹) * c ≠ 1 := by
      intro h
      apply hne
      calc g * u * g⁻¹ = c * (c⁻¹ * (g * u * g⁻¹) * c) * c⁻¹ := by group
        _ = 1 := by rw [h]; group
    have hcconj : IsConj (c⁻¹ * (g * u * g⁻¹) * c) u := by
      have : IsConj (c⁻¹ * (g * u * g⁻¹) * c) (g * u * g⁻¹) := isConj_iff.2 ⟨c, by group⟩
      exact this.trans hconj
    exact hT _ hcT hcsq hcne hcconj

end Frame

end Th2.P43f

@[expose] def B_prop412a_Cv : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K T S : Subgroup G),
    Th2Std x y K T S → Nonempty (kBar K ≃* alternatingGroup (Fin 7)) →
      Nat.card ↥(T ⊓ CxK x K) = 4 → T < S → CFSG.IsElementaryAbelian 2 ↥(T ⊓ CxK x K) →
        ¬ IsTerminalPair 2 x K →
        ∀ v : G, orderOf v = 2 → (∀ s ∈ S, s * v = v * s) → (¬ ∃ c : G, c * x * c⁻¹ = v) →
          Group.IsSolvable ↥(centralizer ({v} : Set G))

theorem b_prop412a_3b_nt_of (hc5 : B_thm2_cent5) (hCv : B_prop412a_Cv) : B_prop412a_3b_nt := by
  intro G _ _ hG x y K T S hs h7 hQ4 hTS hQel hnt u hu2 hux
  obtain ⟨e7⟩ := h7
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPd8 : IsD8 (T ⊓ K) := isD8_of_inf_alt7 hs.T_pGroup hs.sylow_P e7
  obtain ⟨D, hDP, hDel, hD4, -⟩ := hPd8.exists_four_containing (p := 1) (one_mem _) (mul_one 1)
  have hD2 : pRank 2 ↥D = 2 := by
    have h1 := card_eq_two_pow_pRank hDel
    rw [hD4] at h1
    have h2 : (2 : ℕ) ^ 2 = 2 ^ pRank 2 ↥D := by simpa using h1
    exact (Nat.pow_right_injective le_rfl h2).symm
  have hP2 : 2 ≤ pRank 2 ↥(T ⊓ K) := hD2.symm.le.trans (pRank_mono' hDP)
  obtain ⟨a, z, psi, F⟩ := exists_frame hc5 hG hs e7 hQ4 hTS hP2 hQel
  have hcls := F.isConj_x_or_v_of_involution hG hs e7 hP2 hQ4 hu2
  have hv : IsConj (z * x) u := hcls.resolve_left (fun h => hux (isConj_iff.1 h))
  have hzx : z * x = x * z := F.core.comm_P_conj z F.z_mem x F.x_mem
  have hvsq : (z * x) * (z * x) = 1 := by
    calc (z * x) * (z * x) = z * (x * z) * x := by group
      _ = z * (z * x) * x := by rw [← hzx]
      _ = (z * z) * (x * x) := by group
      _ = 1 := by rw [F.z_sq, F.x_sq, one_mul]
  have hvne : z * x ≠ 1 := by
    intro h
    have hxz : x = z := by
      have : x = z⁻¹ := by
        calc x = z⁻¹ * (z * x) := by group
          _ = z⁻¹ := by rw [h, mul_one]
      rw [this]
      exact inv_eq_of_mul_eq_one_right F.z_sq
    have : x ∈ (T ⊓ K) ⊓ conjugate (T ⊓ K) a := ⟨hxz ▸ F.z_mem, F.x_mem⟩
    rw [F.core.P_inf_conj, Subgroup.mem_bot] at this
    exact F.x_ne this
  have hvord : orderOf (z * x) = 2 := orderOf_eq_prime (by rwa [sq]) hvne
  have hvS : ∀ s ∈ S, s * (z * x) = (z * x) * s := by
    intro s hs'
    have h1 := F.S_centralizes_v s hs'
    calc s * (z * x) = (s * (z * x) * s⁻¹) * s := by group
      _ = (z * x) * s := by rw [h1]
  have hvx : ¬ ∃ c : G, c * x * c⁻¹ = z * x := fun ⟨c, hc⟩ =>
    F.not_isConj_v_of_Q hG hs e7 hP2 hQ4 ⟨F.x_mem_T, F.x_mem_CxK⟩ F.x_sq F.x_ne
      (isConj_iff.2 ⟨c, hc⟩)
  have hsolv := hCv G hG x y K T S hs ⟨e7⟩ hQ4 hTS hQel hnt (z * x) hvord hvS hvx
  obtain ⟨d, hd⟩ := isConj_iff.1 hv
  refine isSolvable_centralizer_of_conj (u := u) (v := z * x) (d := d⁻¹) ?_ hsolv
  rw [← hd]
  group

end CFSG.GH74.GLS
