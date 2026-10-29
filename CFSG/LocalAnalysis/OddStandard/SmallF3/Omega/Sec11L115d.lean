module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L115dD
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L115dE
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L115dF
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L115b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L115c
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L118DS
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109A2Card

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]
variable {t z : G} {L S : Subgroup G} {K1 K2 T R : Subgroup G}

theorem sec11d_pair_le (hp : Asc82Pre11) (hctx : Sec11Ctx G t L S z K1 K2 T R) :
    zpowers t ⊔ zpowers z ≤ secD K1 K2 R := by
  obtain ⟨-, -, -, -, -, -, htS, hzS, -⟩ := sec11L114_data hp hctx
  obtain ⟨htQ, hzQ⟩ := sec11L114_cent_Q hp hctx
  have hSR : S ≤ R := hctx.S_le.trans hctx.T_le
  exact sup_le (zpowers_le.2 ⟨htQ, hSR htS⟩) (zpowers_le.2 ⟨hzQ, hSR hzS⟩)

theorem sec11d_set (hp : Asc82Pre11) (hctx : Sec11Ctx G t L S z K1 K2 T R) :
    Sec11dSet t z K1 K2 R := by
  obtain ⟨hRN, hK0⟩ := asc82Lemma115c_of hp G t L S z K1 K2 T R hctx
  exact ⟨sec11c_split_of hp hctx.toSec10Ctx, sec11c_KD_le_K0 (sec11d_pair_le hp hctx), hRN, hK0⟩

theorem sec11d_Q_le_KD (hs : Sec11dSet t z K1 K2 R) : secQ K1 K2 ≤ secKD (secD K1 K2 R) :=
  fun q hq => sec11d_cent_mem_KD hs.K0_eq hs.KD_le (hs.split.split.right_le (hs.split.Q_le hq))
    fun d hd => (Subgroup.mem_centralizer_iff.mp hd.1 q hq).symm

theorem sec11d_card_CTQ (h : IsD8 (secCTQ K1 K2 T)) : Nat.card ↥(secCTQ K1 K2 T) = 8 := by
  obtain ⟨e⟩ := h
  have h1 := Nat.card_congr e.toEquiv
  rw [DihedralGroup.nat_card] at h1
  omega

theorem sec11d_big (hp : Asc82Pre11) (hctx : Sec11Ctx G t L S z K1 K2 T R)
    (hD8 : IsD8 (secCTQ K1 K2 T)) : ¬ secD K1 K2 R ≤ zpowers t ⊔ zpowers z := by
  intro hle
  obtain ⟨ht2, hz2, htz, ht1, hz1, hne, -⟩ := sec11L114_data hp hctx
  have h4 : Nat.card ↥(zpowers t ⊔ zpowers z) = 4 :=
    sec11L114_pair_card ht2 hz2 htz ht1 hz1 hne
  have hCD : secCTQ K1 K2 T ≤ secD K1 K2 R := inf_le_inf_left _ hctx.T_le
  have h := Subgroup.card_le_of_le (hCD.trans hle)
  have h8 := sec11d_card_CTQ hD8
  omega

theorem sec11d_cl (hp : Asc82Pre11) (h112 : Asc82Lemma112)
    (hctx : Sec11Ctx G t L S z K1 K2 T R) (hbig : ¬ secD K1 K2 R ≤ zpowers t ⊔ zpowers z) :
    ∃ Y : Subgroup G, Sec11dCl (secD K1 K2 R) Y t z := by
  obtain ⟨ht2, hz2, htz, ht1, hz1, hne, -⟩ := sec11L114_data hp hctx
  have hWD := sec11d_pair_le hp hctx
  have hDih : IsDihSd (secD K1 K2 R) := asc82Lemma114_of hp h112 G t L S z K1 K2 T R hctx
  obtain ⟨Y, hYD, hYc, hYi⟩ := sec11_isDihSd_exists_cyclic hDih
  have hpsp : IsPSp43 L := (hp.basic G t L S z hctx.toSec10Z).1
  have hzQ : z ∈ secQ K1 K2 :=
    (sec10KS_Q_elem hp.facts.pockets5 hp.facts.centZ5 hpsp hctx.toSec10Ctx).1
  exact ⟨Y, {
    cyc := hYc
    le := hYD
    idx := hYi
    p2 := sec11_isDihSd_isPGroup hDih
    t_mem := hWD (mem_sup_left (mem_zpowers t))
    z_mem := hWD (mem_sup_right (mem_zpowers z))
    t_sq := ht2
    z_sq := hz2
    t_ne := ht1
    z_ne := hz1
    tz_ne := hne
    tz_comm := htz
    z_cent := fun d hd => (Subgroup.mem_centralizer_iff.mp hd.1 z hzQ).symm
    cent := fun d hd hdt => sec11L114_cent_D hp h112 hctx hd hdt
    big := hbig }⟩

theorem asc82Lemma115d_of (hp : Asc82Pre11) (h112 : Asc82Lemma112) : Asc82Lemma115d := by
  intro G _ _ t L S z K1 K2 T R hctx
  by_cases hRTD : R = T ⊔ secD K1 K2 R
  · exact Or.inl hRTD
  refine Or.inr ?_
  obtain ⟨h6, hD8⟩ : Nonempty (↥(secMstar t S L) ≃* Equiv.Perm (Fin 6)) ∧
      IsD8 (secCTQ K1 K2 T) := by
    rcases h112 G t L S z K1 K2 T R hctx with ⟨hA6, -⟩ | ⟨h6, r, -, -, hD8, -⟩
    · exact absurd (le_antisymm
        ((asc82Lemma115b_of hp h112 G t L S z K1 K2 T R hctx hA6).le.trans le_sup_left)
        (sup_le hctx.T_le inf_le_right)) hRTD
    · exact ⟨h6, hD8⟩
  have hTR : T ≤ R := hctx.T_le
  have hDR : secD K1 K2 R ≤ R := inf_le_right
  have hSR : S ≤ R := hctx.S_le.trans hTR
  have hRQ : R ≤ normalizer (secQ K1 K2 : Set G) := hctx.sylowR.1
  have hTDR : T ⊔ secD K1 K2 R ≤ R := sup_le hTR hDR
  have hRD : ∀ g ∈ R, ∀ d ∈ secD K1 K2 R, g * d * g⁻¹ ∈ secD K1 K2 R := fun g hg d hd =>
    (Subgroup.mem_normalizer_iff.mp (sec11c_normalizer_D hRQ hg) d).mp hd
  have hTN : ∀ a ∈ T, ∀ n ∈ secD K1 K2 R, a * n * a⁻¹ ∈ secD K1 K2 R := fun a ha n hn =>
    hRD a (hTR ha) n hn
  have hCT : ∀ c ∈ R, c * t = t * c → c ∈ T := fun c hc hct =>
    hctx.S_le (sec11L114_cent_le hctx.sylow hctx.sylowR.2.1 hSR hc hct)
  have hz : ∀ g : G, g * t * g⁻¹ ≠ z := fun g h =>
    sec10_not_conj_z hp.s3.l37 hctx.toSec10Ctx g (by rw [← h]; group)
  obtain ⟨Y, hCl⟩ := sec11d_cl hp h112 hctx (sec11d_big hp hctx hD8)
  obtain ⟨hone, hgen⟩ := sec11d_R_side hDR hRD hCT hz hCl
  obtain ⟨x0, hx0R, hx0⟩ : ∃ x0 ∈ R, x0 ∉ T ⊔ secD K1 K2 R := by
    by_contra hcon
    push Not at hcon
    exact hRTD (le_antisymm (fun x hx => hcon x hx) hTDR)
  have hs := sec11d_set hp hctx
  obtain ⟨ρ, hρ⟩ := sec11d_exists_rho hs.split (sec11d_pair_le hp hctx) hs.RN hs.K0_eq
  have hker : ∀ y : ↥R, (y : G) ∈ secD K1 K2 R → ρ y = 1 := fun y hy =>
    hρ.ker_of_mem hs.split hy
  have hker' : ∀ y : ↥R, ρ y = 1 → (y : G) ∈ secD K1 K2 R := fun y hy =>
    hρ.mem_of_ker hs.split (sec11d_Q_le_KD hs) hRQ hy
  have hrel : (Sec11dPsi hTR ρ).relIndex ρ.range = 2 :=
    sec11dPsi_relIndex hTR hDR hTN hker hker' hx0R hx0 fun k hk hkT => hone x0 hx0R hx0 k hk hkT
  have hcard : 64 ≤ Nat.card ↥(Sec11dPsi hTR ρ) :=
    sec11dPsi_card hTR (sec11d_card_T hp hctx.toSec10Z hctx.sylowT h6)
      (sec11d_card_CTQ hD8).le fun s hs' => ⟨(hker' _ hs').1, s.2⟩
  have hf := hp.facts
  have hpsp : IsPSp43 L := (hp.basic G t L S z hctx.toSec10Z).1
  have hcomm : ⁅K1, K2⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    exact Subgroup.mem_centralizer_iff.mpr fun b hb' =>
      (sec10Z_comm hf.pockets5 hpsp hctx.toSec10Ctx a ha b hb').symm
  obtain ⟨e1, e2⟩ := sec10KS_equiv hf.pockets5 hf.centZ5 hpsp hctx.toSec10Ctx
  obtain ⟨s, hsP, hsK⟩ := sec10A2_exists_swap_elem hf hp.basic hctx.toSec10Ctx
  have hsS : s ∈ S := hsP.1
  have hsC : s ∈ L ⊓ centralizer ({z} : Set G) :=
    ⟨hsP.2, Subgroup.mem_centralizer_singleton_iff.mpr (hctx.central s hsS)⟩
  have hsw := sec10A2_swap hf hp.basic hctx.toSec10Ctx s hsC hsK
  have hsT : s ∈ T := hctx.S_le hsS
  obtain ⟨-, -, hTK0, -⟩ := asc82Step111T_of hp G t L S z K1 K2 T hctx.toSec10Ctx hctx.hyp
    hctx.sylowT hctx.S_le
  have hsN : ∀ n ∈ oddCoreIn (secK0 t z), s * n * s⁻¹ ∈ oddCoreIn (secK0 t z) := fun n hn =>
    sec11_conj_mem_oddCoreIn (hTK0 hsT) hn
  obtain ⟨-, -, -, -, -, -, -, -, hQS⟩ := sec11L114_data hp hctx
  obtain ⟨ψ, hψΦ, hψΨ, hψ2, hψ1, hψK2, hψout⟩ := hf.autK5 G K1 K2 hcomm
    (sec10KS_card_sup hf.pockets5 hf.centZ5 hpsp hctx.toSec10Ctx) e1 e2 ρ.range
    (Sec11dPsi hTR ρ) (sec11dPsi_le hTR) (sec11dPhi_pgroup hctx.sylowR.2.1) hrel hcard
    (hρ.conj_mem_psi hs.split hTR (hQS.trans hctx.S_le))
    (hρ.swap_mem_psi hs.split hTR hsT hsN hsw)
  obtain ⟨x1, rfl⟩ := hψΦ
  have hx1T : (x1 : G) ∉ T ⊔ secD K1 K2 R := fun hx =>
    hψΨ (sec11dPsi_mem_of_mem_sup hTR hDR hTN hker hx)
  have hx1inv : (x1 : G)⁻¹ ∉ T ⊔ secD K1 K2 R := fun hx => hx1T (by
    have := (T ⊔ secD K1 K2 R).inv_mem hx
    rwa [inv_inv] at this)
  refine ⟨x1, x1.2, ?_, hρ.commutator_le hs hψK2, hρ.isOuterOn hs hψ1 hψout,
    hρ.sq_comm_mem hs hψ2, ?_⟩
  · refine le_antisymm (fun g hg => ?_) (sup_le hTDR (zpowers_le.2 x1.2))
    by_cases hgT : g ∈ T ⊔ secD K1 K2 R
    · exact Subgroup.mem_sup_left hgT
    · have h1 := hone (x1 : G) x1.2 hx1T g hg hgT
      have e : g = (x1 : G) * ((x1 : G)⁻¹ * g) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (mem_zpowers _))
        (Subgroup.mem_sup_left h1)
  · have h1 := hgen (x1 : G)⁻¹ (R.inv_mem x1.2) hx1inv
    rwa [inv_inv] at h1

end CFSG.OddStandard.SmallF3.Omega
