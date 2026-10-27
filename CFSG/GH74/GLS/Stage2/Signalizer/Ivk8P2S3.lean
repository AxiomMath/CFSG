module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S3B
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S3C
import CFSG.GH74.AS16.Standard
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8Stmt813

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Final.Thm4 CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S3

theorem prop18_12_of (hMin : MinIndexL34) (hInv : InvSec)
    (h171 : Prop17_1) (h181 : Prop18_1) (hAB : IG_11_7) (h1123 : IG_11_23)
    (hL31 : Lemma31Narrow) (hKA : IVK_8_13_lift) (hKB : KB813) : Prop18_12 := by
  intro G _ _ z k S M p hctx V hVP hVel hVnc hVrk H hH hzVH
  have hS2 : Stage2Ctx G z k S := hctx.base.ctx.ctx
  have hM : M = centralizer ({z} : Set G) := (h171 G z k S M hctx.base.ctx hctx.base.fail).1
  have hz2 : orderOf z = 2 := hS2.orderOf_z
  have hp : p.Prime := hctx.prime
  have hp2 : p ≠ 2 := hctx.odd
  have hzH : z ∈ H := hzVH (Subgroup.mem_sup_left (Subgroup.mem_zpowers z))
  have hVH : V ≤ H := le_trans le_sup_right hzVH
  by_cases hFs : Fs H ≤ M
  · exact Or.inl ⟨hFs, z_mem_Op_two hzH hz2 (hM ▸ hFs)⟩
  right
  have hCM : ∀ v ∈ V, v ≠ 1 → centralizer ({v} : Set G) ≤ M := fun v hv hv1 =>
    cent_le_M h181 hctx hVP hVel hVrk hv hv1
  have hFm : Fm H ≤ M := Fm_le_M hAB h1123 hp hp2 hz2 hM hVP hVel hVnc hCM hzH hVH
  obtain ⟨J, hJ, hJM⟩ := exists_comp_not_le hFs hFm
  have hq : IsQuasisimple ↥J := quasisimple_of_isCompIn hJ
  have hc2 : ∀ K₁ K₂ K₃ : Subgroup ↥H, IsComponent K₁ → IsComponent K₂ → IsComponent K₃ →
      K₁ = K₂ ∨ K₁ = K₃ ∨ K₂ = K₃ := fun K₁ K₂ K₃ h₁ h₂ h₃ =>
    comps_le_two hL31 hS2 hH.1 hzH h₁ h₂ h₃
  have hVN : V ≤ normalizer (J : Set G) := by
    intro v hv
    have hodd : Odd (orderOf v) := by
      by_cases hv1 : v = 1
      · rw [hv1, orderOf_one]; exact odd_one
      · rw [orderOf_eq_of_elem hp hVel hv hv1]; exact hp.odd_of_ne_two hp2
    exact mem_normalizer_of_odd hc2 hJ (hVH hv) hodd
  have hVJ : V ⊓ centralizer (J : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Subgroup.mem_bot]
    by_contra hv1
    apply hJM
    have hJle : J ≤ centralizer ({v} : Set G) := fun j hj =>
      Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hv.2 j hj)
    exact hJle.trans (hCM v hv.1 hv1)
  have hVne : V ≠ ⊥ := fun h => hVnc (by rw [h]; infer_instance)
  have hVnc' : ¬ V ≤ centralizer (J : Set G) := fun h =>
    hVne ((inf_eq_left.mpr h).symm.trans hVJ)
  have hPp : IsPGroup p ↥(Op p M) := isPGroup_Op p hp M
  have hzN : z ∈ normalizer (J : Set G) :=
    z_mem_normalizer hp hz2 hM hzH hJ hPp (le_normalizer_Op p M) (Op_le p M) hVP hVN hVnc'
  have hJz : ⁅J, zpowers z⁆ = J := commutator_eq hM hJ hzN hJM
  set P' : Subgroup G := Op p M ⊓ (H ⊓ normalizer (J : Set G)) with hP'
  have hP'p : IsPGroup p ↥P' := hPp.to_le inf_le_left
  have hP'le : P' ≤ H ⊓ normalizer (J : Set G) := inf_le_right
  have hP'z : ∀ x ∈ P', z * x = x * z := fun x hx => by
    have : x ∈ M := Op_le p M hx.1
    rw [hM] at this
    exact (Subgroup.mem_centralizer_singleton_iff.mp this).symm
  have hP'n : ∀ c ∈ H ⊓ normalizer (J : Set G), c * z = z * c → c ∈ normalizer (P' : Set G) := by
    intro c hc hcz
    have hcM : c ∈ M := by
      rw [hM]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hcz
    exact mem_normalizer_inf (le_normalizer_Op p M hcM) (Subgroup.le_normalizer hc)
  have hVP' : V ≤ P' := le_inf hVP (le_inf hVH hVN)
  have hP'nc : ¬ P' ≤ centralizer (J : Set G) := fun h => hVnc' (hVP'.trans h)
  obtain ⟨-, hKA2⟩ := hKA G z k S hS2 H J hH.1 hJ hz2 hzN hJz p P' hp hp2 hP'p hP'le hP'z hP'n
    hP'nc
  rcases hKA2 with ⟨x, hxP, hxle⟩ | ⟨hL34, hp3, hrel, hunit⟩
  · exact absurd (isCyclic_of_le_sup (hP'le hxP).2 hVN (hVP'.trans hxle) hVJ) hVnc
  have hVcard : Nat.card ↥V = 9 := by
    have hle : Nat.card ↥V ≤ 9 := card_le_of_relIndex hVP' hVJ hrel
    obtain ⟨V₀, hV₀V, -, hV₀c⟩ := exists_plane hp hVel hVnc
    have hge : p ^ 2 ≤ Nat.card ↥V := hV₀c ▸ Subgroup.card_le_of_le hV₀V
    subst hp3
    omega
  have hZ : Odd (Nat.card ↥(center ↥J)) := center_odd hMin hInv hS2 hq hL34
  have hrk : 4 ≤ pRank 2 (↥J ⧸ center ↥J) := (hKB _ hL34).1
  have hG4 : pRank 2 G ≤ 4 := hS2.std.rank.2
  have hnoinv : ∀ c ∈ centralizer (J : Set G), orderOf c ≠ 2 := fun c hc hc2 =>
    no_involution_centralizer hZ hrk hG4 hc hc2
  have hCHodd : Odd (Nat.card ↥(H ⊓ centralizer (J : Set G))) := by
    by_contra hnodd
    have heven : 2 ∣ Nat.card ↥(H ⊓ centralizer (J : Set G)) :=
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hnodd)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := ↥(H ⊓ centralizer (J : Set G))) 2 heven
    exact hnoinv (c : G) c.2.2 (by rw [Subgroup.orderOf_coe, hc])
  have hEm : Em H = J := by
    refine Em_eq_of_comps hJ fun K hK => ?_
    rcases AS16.isCompIn_commute hK hJ with h | h
    · exact h
    · exfalso
      obtain ⟨t, htK, ht2⟩ := AS16.exists_involution_of_isQuasisimple (quasisimple_of_isCompIn hK)
      exact hnoinv t (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h htK) ht2
  subst hEm
  exact ⟨hp3, hVcard, lieModel_pPrimeCore hq hZ hL34, hunit, hCHodd⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
