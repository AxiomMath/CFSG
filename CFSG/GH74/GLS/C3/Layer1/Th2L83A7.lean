module

public import CFSG.GH74.GLS.C3.Layer1.Th2L83Alt
public import CFSG.GH74.GLS.C3.Layer1.Th2L83A7Fin

public section

namespace CFSG.GH74.GLS.Th2.L83

open Equiv Equiv.Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.GLS.Th2

variable {G : Type} [Group G] [Finite G]

theorem le_pRank_of_index {B F : Subgroup G} (r : ℕ) (hFB : F ≤ B)
    (hBel : CFSG.IsElementaryAbelian 2 ↥B) (hB : r + 1 ≤ pRank 2 ↥B)
    (h : ∀ a ∈ B, ∀ b ∈ B, a ∉ F → b ∉ F → a * b ∈ F) : r ≤ pRank 2 ↥F := by
  have hFel : CFSG.IsElementaryAbelian 2 ↥F := Th2.elemAbelian_of_le hBel hFB
  have h1 := card_le_two_mul_of_mul_mem hFB h
  rw [C3.Layer1.Back.card_eq_two_pow_pRank hBel,
    C3.Layer1.Back.card_eq_two_pow_pRank hFel] at h1
  have h2 : 2 ^ pRank 2 ↥B ≤ 2 ^ (1 + pRank 2 ↥F) := by
    calc 2 ^ pRank 2 ↥B ≤ 2 * 2 ^ pRank 2 ↥F := h1
      _ = 2 ^ 1 * 2 ^ pRank 2 ↥F := by rw [pow_one]
      _ = 2 ^ (1 + pRank 2 ↥F) := by rw [pow_add]
  have h3 : pRank 2 ↥B ≤ 1 + pRank 2 ↥F :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h2
  omega

theorem l83_A7_core {K X M P B D : Subgroup G} {r : ℕ}
    (hKX : ∀ a ∈ X, ∀ k ∈ K, a * k * a⁻¹ ∈ K)
    (hP : IsSylowOf 2 P K) (hBX : B ≤ X)
    (hBel : CFSG.IsElementaryAbelian 2 ↥B) (hBr : r + 1 ≤ pRank 2 ↥B)
    (hD : IsDSub K P D) (hDB : D ≤ B)
    (hN : ∀ F : Subgroup G, F ≤ B → r ≤ pRank 2 ↥F → normalizer (F : Set G) ≤ M) :
    K ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hDP, hPK, hDel, hDcard, e, hcnt⟩ := hD
  obtain ⟨g, hinj, hrange⟩ := A7Aux.exists_conj hP e (card_sylow_A7 hP ⟨e⟩)
  have hDeq : D = A7Aux.pull (A7Aux.thetaP hP.le e g) IVK.A7.Wsub :=
    A7Aux.eq_pull_W hP e g hinj hrange hDP hDel hDcard hcnt
  let Mo : AltModel hKX 7 := AltModel.ofIso hKX (by norm_num) (by norm_num) e g
  have hψθ : ∀ (d : G) (hdP : d ∈ P) (hdX : d ∈ X),
      Mo.ψ ⟨d, hdX⟩ = A7Aux.thetaP hP.le e g ⟨d, hdP⟩ := by
    intro d hdP hdX
    rw [AltModel.ofIso_inner (hKX := hKX) (by norm_num) (by norm_num) e g (hP.le hdP) hdX]
    rw [A7Aux.thetaP_apply', AltModel.ofIso_Φ (hKX := hKX)]
  have hWψ : ∀ w ∈ IVK.A7.Wsub, ∃ (d : G) (hdD : d ∈ D),
      Mo.ψ ⟨d, hBX (hDB hdD)⟩ = w := by
    intro w hw
    obtain ⟨p, hp⟩ := A7Aux.Wsub_le_range hrange hw
    have hpD : (p : G) ∈ D := by
      rw [hDeq]
      exact A7Aux.mem_pull.2 ⟨p.2, by
        have : A7Aux.thetaP hP.le e g ⟨(p : G), p.2⟩ = w := hp
        rw [this]; exact hw⟩
    refine ⟨p, hpD, ?_⟩
    rw [hψθ (p : G) p.2 (hBX (hDB hpD))]
    exact hp
  have hBZ : ∀ (b : G) (hbB : b ∈ B), ZVals (Mo.ψ ⟨b, hBX hbB⟩) := by
    intro b hbB
    refine centralizer_Wsub_zvals _ ?_
    intro w hw
    obtain ⟨d, hdD, rfl⟩ := hWψ w hw
    have hcomm : b * d = d * b :=
      (C3.Layer1.Back.forall_of_isElementaryAbelian hBel).1 b hbB d (hDB hdD)
    have e1 : (⟨b, hBX hbB⟩ : ↥X) * ⟨d, hBX (hDB hdD)⟩ =
        ⟨d, hBX (hDB hdD)⟩ * ⟨b, hBX hbB⟩ := Subtype.ext hcomm
    have := congrArg Mo.ψ e1
    rwa [map_mul, map_mul] at this
  have key : ∀ c : Perm (Fin 7),
      (∀ σ τ : Perm (Fin 7), ZVals σ → ZVals τ → σ * c ≠ c * σ → τ * c ≠ c * τ →
        (σ * τ) * c = c * (σ * τ)) →
      r ≤ pRank 2 ↥(commSub X B Mo.ψ c) := by
    intro c hc
    refine le_pRank_of_index r commSub_le hBel hBr ?_
    intro a haB b hbB haF hbF
    have haX := hBX haB
    have hbX := hBX hbB
    have hab : a * b ∈ B := B.mul_mem haB hbB
    refine mem_commSub.2 ⟨hBX hab, hab, ?_⟩
    have hna : ¬ (Mo.ψ ⟨a, haX⟩ * c = c * Mo.ψ ⟨a, haX⟩) := fun hh =>
      haF (mem_commSub.2 ⟨haX, haB, hh⟩)
    have hnb : ¬ (Mo.ψ ⟨b, hbX⟩ * c = c * Mo.ψ ⟨b, hbX⟩) := fun hh =>
      hbF (mem_commSub.2 ⟨hbX, hbB, hh⟩)
    have := hc _ _ (hBZ a haB) (hBZ b hbB) hna hnb
    have hm : Mo.ψ ⟨a * b, hBX hab⟩ = Mo.ψ ⟨a, haX⟩ * Mo.ψ ⟨b, hbX⟩ := by
      rw [← map_mul]; rfl
    rw [hm]; exact this
  have k1 := key c1 fun σ τ hσ hτ => coset_c1 hσ hτ
  have k2 := key c2 fun σ τ hσ hτ => coset_c2 hσ hτ
  have k3 := key c3 fun σ τ hσ hτ => coset_c3 hσ hτ
  set F1 := commSub X B Mo.ψ c1
  set F2 := commSub X B Mo.ψ c2
  set F3 := commSub X B Mo.ψ c3
  refine K_le_of_cover hKX {F1, F2, F3} ?_ ?_ ?_ ?_
  · intro F hF
    have hFB : F ≤ B := by rcases hF with rfl | rfl | rfl <;> exact commSub_le
    exact ⟨hFB.trans hBX, (CFSG.IsElementaryAbelian.isPGroup 2 ↥B).to_le hFB⟩
  · intro F hF
    have hrk : r ≤ pRank 2 ↥F ∧ F ≤ B := by
      rcases hF with rfl | rfl | rfl <;> exact ⟨‹_›, commSub_le⟩
    exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer (F : Set G)).trans (hN F hrk.2 hrk.1))
  · exact pPrimeCoreOf_le_of_normalizers hKX r hBel hBX hBr hN
  · have hmem : ∀ c : Perm (Fin 7), c.IsThreeCycle → ∀ F ∈ ({F1, F2, F3} : Set (Subgroup G)),
        (∀ f : ↥X, (f : G) ∈ F → Mo.ψ f * c = c * Mo.ψ f) →
        c ∈ ⨆ F ∈ ({F1, F2, F3} : Set (Subgroup G)), (alternatingGroup (Fin 7) ⊓
          ⨅ (f : ↥X) (_ : (f : G) ∈ F),
            centralizer ({Mo.ψ f} : Set (Perm (Fin 7)))) := by
      intro c hc F hF hcomm
      refine Subgroup.mem_iSup_of_mem F (Subgroup.mem_iSup_of_mem hF
        (Subgroup.mem_inf.2 ⟨hc.mem_alternatingGroup, ?_⟩))
      rw [Subgroup.mem_iInf]
      intro f
      rw [Subgroup.mem_iInf]
      intro hf
      exact Subgroup.mem_centralizer_singleton_iff.2 (hcomm f hf).symm
    have hc2 : c2.IsThreeCycle :=
      Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)
    have hc3 : c3.IsThreeCycle :=
      Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)
    have hcomm : ∀ (c : Perm (Fin 7)) (F : Subgroup G),
        F = commSub X B Mo.ψ c →
        ∀ f : ↥X, (f : G) ∈ F → Mo.ψ f * c = c * Mo.ψ f := by
      intro c F hF f hf
      rw [hF] at hf
      obtain ⟨hbX, -, hc⟩ := mem_commSub.1 hf
      exact hc
    refine Mo.top_of_gen {F1, F2, F3} ?_
    refine alt_le_of_c123 _ ?_ ?_ ?_
    · exact hmem c1 c1_three F1 (by simp) (hcomm c1 F1 rfl)
    · exact hmem c2 hc2 F2 (by simp) (hcomm c2 F2 rfl)
    · exact hmem c3 hc3 F3 (by simp) (hcomm c3 F3 rfl)

end CFSG.GH74.GLS.Th2.L83
