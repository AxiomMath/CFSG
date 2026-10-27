module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmESev1
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmEOrb4

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open scoped commutatorElement

namespace ThmE

section Orb6

variable {r : ℕ} {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCex.W_abelian (c : MinCex r Ω K S R W H) : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := by
  obtain ⟨η, -, -, -, habel, -⟩ := c.exists_eta (TwinThmEW.etaAbelian_of_gen c.stand.hyp)
  exact habel

theorem orb4_swap_htd {u t : G} (ht2 : t * t = 1) (huu' : u * (t * u * t⁻¹) = (t * u * t⁻¹) * u) :
    (u * (t * u * t⁻¹)) * t = t * (u * (t * u * t⁻¹)) := by
  have e1 : t * (t * u * t⁻¹) * t⁻¹ = u := by
    have : t * (t * u * t⁻¹) * t⁻¹ = (t * t) * u * (t * t)⁻¹ := by group
    rw [this, ht2]
    group
  have e : t * (u * (t * u * t⁻¹)) * t⁻¹ = u * (t * u * t⁻¹) := by
    calc t * (u * (t * u * t⁻¹)) * t⁻¹ = (t * u * t⁻¹) * (t * (t * u * t⁻¹) * t⁻¹) := by group
      _ = (t * u * t⁻¹) * u := by rw [e1]
      _ = u * (t * u * t⁻¹) := huu'.symm
  exact (mul_inv_eq_iff_eq_mul.mp e).symm

theorem MinCex.goodFourD_of_commute (c : MinCex r Ω K S R W H) {z g t : G}
    (hz : IsUniqueInvolution K z) (hzH : Subgroup.centralizer ({z} : Set G) ≤ H) (hg : g ∉ H)
    (ht : t = g * z * g⁻¹) (htS : t ∈ (S : Subgroup G)) (hcomm : t * z = z * t) :
    TwinThmEW.GoodFourWD (S : Subgroup G) H W t := by
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  have hA : EtaAbelian Ω := TwinThmEW.etaAbelian_of_gen hΩ
  have hM : EtaMeet Ω := TwinThmEW.etaMeet_of_gen hΩ
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  obtain ⟨-, hWS, hWn⟩ := c.stand.hW
  obtain ⟨K', hK'tw, hne, R', hR', hR'K', hR'S⟩ := c.stand.twin
  have hWab := c.W_abelian
  have hK : K ∈ Ω := c.stand.mem
  have hC : ∀ M ∈ Ω, IsUniqueInvolution M z → ∀ x ∈ M, orderOf x = 4 → t * x ≠ x * t := by
    have := c.hC_of_conj hz hzH hg
    rwa [← ht] at this
  have hfour : ∀ {M R₀ : Subgroup G}, M ∈ Ω → R₀ ∈ RSet Ω → R₀ ≤ M → R₀ ≤ (S : Subgroup G) →
      IsCyclic ↥(M ⊓ W) ∧ ∃ u ∈ M ⊓ W, orderOf u = 4 :=
    fun hM' hR₀ hR₀M hR₀S => c.exists_order_four_of_inf_W hA hM hM' hR₀ hR₀M hR₀S
  have hcentW : ∀ {K₀ J R₀ R₂ : Subgroup G}, K₀ ∈ twinSet Ω K → J ∈ KPerp Ω K₀ → R₀ ∈ RSet Ω →
      R₀ ≤ K₀ → R₀ ≤ (S : Subgroup G) → R₂ ∈ RSet Ω → R₂ ≤ J → R₂ ≤ (S : Subgroup G) →
      ∀ a ∈ R₀ ⊔ R₂, a ∈ W → a ≠ 1 → a * a = 1 → Subgroup.centralizer ({a} : Set G) ≤ H :=
    fun {_ J R₀ R₂} hK₀tw hJ hR₀ hR₀K₀ hR₀S hR₂ hR₂J hR₂S a ha haW ha1 ha2 =>
      c.hyp.cent _ hK₀tw.1
        (TwinThmEW.inf_W_mem_USet' hΩ c.stand.hW.1 c.stand.hW.2.1 hK₀tw.1 hR₀ hR₀K₀ hR₀S) _ hJ R₀ R₂ hR₀
        hR₀K₀ hR₀S hR₂ hR₂J hR₂S (TwinThmEW.commutes_or_eq_of_le_sylow hΩ hR₀ hR₂ hR₀S hR₂S) a ha haW ha1 ha2
  have ht2 : t * t = 1 := by
    rw [ht]
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hz.sq]; group
  have hWt : ∀ x ∈ W, t * x * t⁻¹ ∈ W := fun x hx => by
    have := conj_mem_conjSub (n := t) hx
    rwa [hWn t htS] at this
  have hK'Ω : K' ∈ Ω := hK'tw.1
  have hKtw : K ∈ twinSet Ω K := ⟨hK, z, hz, hz⟩
  obtain ⟨-, z', hzz', hz'K'⟩ := id hK'tw
  have hz' : IsUniqueInvolution K' z := by
    have := hz.eq hzz'
    rwa [← this] at hz'K'
  have htzt : t * z * t⁻¹ = z := by rw [hcomm]; group
  have hconjt : ∀ M : Subgroup G, IsUniqueInvolution M z → IsUniqueInvolution (conjSub t M) z := by
    intro M hMz
    have := hMz.conj t
    rwa [htzt] at this
  have hK'perp : K' ∈ KPerp Ω K := TwinThmE.mem_kPerp_of_twin_gen hΩ hK'Ω hK hz' hz
  have hmemR : ∀ u : G, u ∈ K → u ∈ W → u ∈ R := fun u huK huW => by
    have : u ∈ K ⊓ (S : Subgroup G) := ⟨huK, hWS huW⟩
    rwa [inf_S_eq_of_mem_RSet' hΩ hK hRR hRK hRS] at this
  have hmemR' : ∀ u : G, u ∈ K' → u ∈ W → u ∈ R' := fun u huK huW => by
    have : u ∈ K' ⊓ (S : Subgroup G) := ⟨huK, hWS huW⟩
    rwa [inf_S_eq_of_mem_RSet' hΩ hK'Ω hR' hR'K' hR'S] at this
  have hRR'2 : IsPGroup 2 ↥(R ⊔ R') := S.isPGroup'.to_le (sup_le hRS hR'S)
  have hswap : ∀ {K₀ R₀ : Subgroup G} {u : G}, K₀ ∈ twinSet Ω K → R₀ ∈ RSet Ω → R₀ ≤ K₀ →
      R₀ ≤ (S : Subgroup G) → conjSub t K₀ ≠ K₀ → u ∈ R₀ → u ∈ W → orderOf u = 4 →
      (∀ a ∈ R₀ ⊔ conjSub t R₀, a ∈ W → a ≠ 1 → a * a = 1 →
        Subgroup.centralizer ({a} : Set G) ≤ H) → TwinThmEW.GoodFourWD (S : Subgroup G) H W t := by
    intro K₀ R₀ u hK₀tw hR₀ hR₀K hR₀S hnK hu huW hu4 h2
    have hK₀Ω : K₀ ∈ Ω := hK₀tw.1
    have hz₀ : IsUniqueInvolution K₀ z := by
      obtain ⟨-, z'', hzK, hzK₀⟩ := hK₀tw
      have := hz.eq hzK
      rwa [← this] at hzK₀
    have hKtΩ : conjSub t K₀ ∈ Ω := hΩ.conjInvariant t K₀ hK₀Ω
    have hRtΩ : conjSub t R₀ ∈ RSet Ω := RSet.conj hΩ.conjInvariant hR₀ t
    have hRtS : conjSub t R₀ ≤ (S : Subgroup G) := TwinThmEW.orb4_conjSub_le_of_mem htS hR₀S
    have hRne : R₀ ≠ conjSub t R₀ :=
      orb4_rset_ne_of_ne hΩ hK₀Ω hKtΩ (Ne.symm hnK) hR₀ hR₀K (conjSub_mono hR₀K)
    have hcm : Commutes R₀ (conjSub t R₀) := TwinThmEW.orb4_rset_commutes hΩ S hR₀ hRtΩ hR₀S hRtS hRne
    have hu'R : t * u * t⁻¹ ∈ conjSub t R₀ := conj_mem_conjSub hu
    have hu'4 : orderOf (t * u * t⁻¹) = 4 := by rw [orderOf_conj_mul_inv_eq]; exact hu4
    exact goodFourD_pair' hΩ S hWn hWab hK₀Ω hKtΩ (Ne.symm hnK) hz₀ (hconjt K₀ hz₀) hR₀ hRtΩ
      hR₀K (conjSub_mono hR₀K) hR₀S hRtS hcomm hu hu4 huW hu'R hu'4 (hWt u huW)
      (orb4_swap_htd ht2 (hcm u hu _ hu'R)) hzH h2
  by_cases hnK : conjSub t K = K
  · by_cases hnK' : conjSub t K' = K'
    · obtain ⟨hcycK, u, huKW, hu4⟩ := hfour hK hRR hRK hRS
      obtain ⟨hcycK', u', hu'KW, hu'4⟩ := hfour hK'Ω hR' hR'K' hR'S
      have huR := hmemR u huKW.1 huKW.2
      have hu'R := hmemR' u' hu'KW.1 hu'KW.2
      have hRne : R ≠ R' := orb4_rset_ne_of_ne hΩ hK hK'Ω (Ne.symm hne) hRR hRK hR'K'
      have hcomm' : Commutes R R' := TwinThmEW.orb4_rset_commutes hΩ S hRR hR' hRS hR'S hRne
      have hinv : ∀ (M : Subgroup G), M ∈ Ω → IsUniqueInvolution M z → conjSub t M = M →
          IsCyclic ↥(M ⊓ W) → ∀ x ∈ M, x ∈ W → orderOf x = 4 → t * x * t⁻¹ = x⁻¹ := by
        intro M hM' hzM htM hMW x hxM hxW hx4
        have h1 : t * x * t⁻¹ ∈ M ⊓ W := by
          refine ⟨?_, ?_⟩
          · have := conj_mem_conjSub (n := t) hxM
            rwa [htM] at this
          · exact hWt x hxW
        rcases eq_or_eq_inv_of_orderOf_four_of_cyclic hMW ⟨hxM, hxW⟩ h1
          hx4 (by rw [orderOf_conj_mul_inv_eq, hx4]) with h | h
        · exfalso
          apply hC M hM' hzM x hxM hx4
          calc t * x = (t * x * t⁻¹) * t := by group
            _ = x * t := by rw [h]
        · exact h
      have huu' : u * u' = u' * u := hcomm' u huR u' hu'R
      have hd2 : (u * u') * (u * u') = 1 := by
        calc (u * u') * (u * u') = u * (u' * u) * u' := by group
          _ = u * (u * u') * u' := by rw [huu']
          _ = (u * u) * (u' * u') := by group
          _ = 1 := by
            rw [sq_eq_of_orderOf_four hz huKW.1 hu4, sq_eq_of_orderOf_four hz' hu'KW.1 hu'4, hz.sq]
      have htd : (u * u') * t = t * (u * u') := by
        have htW : conjSub t K = K := hnK
        have e : t * (u * u') * t⁻¹ = u * u' := by
          calc t * (u * u') * t⁻¹ = (t * u * t⁻¹) * (t * u' * t⁻¹) := by group
            _ = u⁻¹ * u'⁻¹ := by
              rw [hinv K hK hz hnK hcycK u huKW.1 huKW.2 hu4,
                hinv K' hK'Ω hz' hnK' hcycK' u' hu'KW.1 hu'KW.2 hu'4]
            _ = (u' * u)⁻¹ := by group
            _ = (u * u')⁻¹ := by rw [huu']
            _ = u * u' := inv_eq_of_mul_eq_one_right hd2
        exact (mul_inv_eq_iff_eq_mul.mp e).symm
      exact goodFourD_pair' hΩ S hWn hWab hK hK'Ω (Ne.symm hne) hz hz' hRR hR' hRK hR'K' hRS hR'S
        hcomm huR hu4 huKW.2 hu'R hu'4 hu'KW.2 htd hzH
        (fun a ha haW ha1 ha2 => hcentW hKtw hK'perp hRR hRK hRS hR' hR'K' hR'S a ha haW ha1 ha2)
    · obtain ⟨hcycK', u', hu'KW, hu'4⟩ := hfour hK'Ω hR' hR'K' hR'S
      have hKtΩ : conjSub t K' ∈ Ω := hΩ.conjInvariant t K' hK'Ω
      have hJ : conjSub t K' ∈ KPerp Ω K' :=
        TwinThmE.mem_kPerp_of_twin_gen hΩ hKtΩ hK'Ω (hconjt K' hz') hz'
      exact hswap hK'tw hR' hR'K' hR'S hnK' (hmemR' u' hu'KW.1 hu'KW.2) hu'KW.2 hu'4
        (fun a ha haW ha1 ha2 => hcentW hK'tw hJ hR' hR'K' hR'S (RSet.conj hΩ.conjInvariant hR' t)
          (conjSub_mono hR'K') (TwinThmEW.orb4_conjSub_le_of_mem htS hR'S) a ha haW ha1 ha2)
  · obtain ⟨hcycK, u, huKW, hu4⟩ := hfour hK hRR hRK hRS
    have hKtΩ : conjSub t K ∈ Ω := hΩ.conjInvariant t K hK
    have hJ : conjSub t K ∈ KPerp Ω K := TwinThmE.mem_kPerp_of_twin_gen hΩ hKtΩ hK (hconjt K hz) hz
    exact hswap hKtw hRR hRK hRS hnK (hmemR u huKW.1 huKW.2) huKW.2 hu4
      (fun a ha haW ha1 ha2 => hcentW hKtw hJ hRR hRK hRS (RSet.conj hΩ.conjInvariant hRR t)
        (conjSub_mono hRK) (TwinThmEW.orb4_conjSub_le_of_mem htS hRS) a ha haW ha1 ha2)

end Orb6

end ThmE

end CFSG.CGT.PushingUpLit.SolKNA.R4
