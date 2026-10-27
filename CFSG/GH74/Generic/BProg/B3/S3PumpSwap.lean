module

public import CFSG.GH74.Generic.BProg.B3.S3PumpSData
public import CFSG.Sporadic.Th.KernelOrder
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Assembly.CompletedOddCoreElimination
public import CFSG.GH74.E2.ComponentsShape
public import CFSG.GH74.GLS.Bg.Iii2.L41Comp
public import CFSG.GH74.GLS.C3.Layer1.Th2V2Core
public import CFSG.GH74.Generic.BProg.B3.S3FusionT
public import CFSG.GH74.Generic.BProg.B3.S3L3Facts
public import CFSG.GH74.Generic.S45.LUniLift
public import CFSG.GroupTheory.ElementaryAbelianBasis
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.Sporadic.Th.Max3.Packet
public import CFSG.Sporadic.Th.Max3.Quotient
public import Certificates.Certificate10091Base
public import Certificates.Certificate5007

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3PumpSwap

open CFSG CFSG.GH74.Generic.BProg.B3.S3Fusion Subgroup
open scoped commutatorElement

theorem swap_dichotomy {H : Type*} [Group H] (α : H ≃* H) {J N : Subgroup H}
    (hJN : ∀ h : H, ∃ j ∈ J, ∃ n ∈ N, h = j * n) (hcomm : ∀ j ∈ J, ∀ n ∈ N, j * n = n * j)
    (hJperf : ⁅J, J⁆ = J)
    (hJq : ∀ A : Subgroup H, A ≤ J → (∀ a ∈ A, ∀ j ∈ J, j * a * j⁻¹ ∈ A) →
      (∀ a ∈ A, ∀ j ∈ J, a * j = j * a) ∨ J ≤ A) :
    (∀ a ∈ J, α a ∈ N) ∨ J ≤ J.map α.toMonoidHom := by
  set D : Subgroup H := J.map α.toMonoidHom with hD
  have hJnorm : ∀ h : H, ∀ a ∈ J, h * a * h⁻¹ ∈ J := by
    intro h a ha
    obtain ⟨j, hj, n, hn, rfl⟩ := hJN h
    have hna : n * a = a * n := (hcomm a ha n hn).symm
    have : j * n * a * (j * n)⁻¹ = j * a * j⁻¹ := by
      calc j * n * a * (j * n)⁻¹ = j * (n * a) * n⁻¹ * j⁻¹ := by group
        _ = j * (a * n) * n⁻¹ * j⁻¹ := by rw [hna]
        _ = j * a * j⁻¹ := by group
    rw [this]
    exact J.mul_mem (J.mul_mem hj ha) (J.inv_mem hj)
  have hDnorm : ∀ h : H, ∀ d ∈ D, h * d * h⁻¹ ∈ D := by
    rintro h _ ⟨a, ha, rfl⟩
    refine ⟨(α.symm h) * a * (α.symm h)⁻¹, hJnorm _ a ha, ?_⟩
    simp
  have hDperf : ⁅D, D⁆ = D := by
    rw [hD, ← Subgroup.map_commutator, hJperf]
  rcases hJq (D ⊓ J) inf_le_right (fun a ha j hj => ⟨hDnorm j a ha.1, hJnorm j a ha.2⟩) with
    hcen | hJA
  · left
    have hcommDJ : ∀ d ∈ D, ∀ j ∈ J, ⁅d, j⁆ ∈ D ⊓ J := by
      intro d hd j hj
      refine ⟨?_, ?_⟩
      · have e : ⁅d, j⁆ = d * (j * d⁻¹ * j⁻¹) := by simp only [commutatorElement_def]; group
        rw [e]
        exact D.mul_mem hd (hDnorm j d⁻¹ (D.inv_mem hd))
      · have e : ⁅d, j⁆ = (d * j * d⁻¹) * j⁻¹ := by simp only [commutatorElement_def]
        rw [e]
        exact J.mul_mem (hJnorm d j hj) (J.inv_mem hj)
    have hcentral : ∀ c ∈ D ⊓ J, ∀ h : H, c * h = h * c := by
      intro c hc h
      obtain ⟨j', hj', n', hn', rfl⟩ := hJN h
      calc c * (j' * n') = (c * j') * n' := (mul_assoc _ _ _).symm
        _ = (j' * c) * n' := by rw [hcen c hc j' hj']
        _ = j' * (c * n') := mul_assoc _ _ _
        _ = j' * (n' * c) := by rw [hcomm c hc.2 n' hn']
        _ = (j' * n') * c := (mul_assoc _ _ _).symm
    have hDJle : ⁅D, J⁆ ≤ D ⊓ J := Subgroup.commutator_le.mpr hcommDJ
    have h1 : ⁅⁅D, J⁆, D⁆ = ⊥ := by
      rw [eq_bot_iff]
      refine Subgroup.commutator_le.mpr fun c hc d _ => ?_
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact hcentral c (hDJle hc) d
    have h2 : ⁅⁅J, D⁆, D⁆ = ⊥ := by rw [Subgroup.commutator_comm J D]; exact h1
    have h3 : ⁅⁅D, D⁆, J⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
    rw [hDperf] at h3
    have hDJ : ∀ d ∈ D, ∀ j ∈ J, d * j = j * d := by
      intro d hd j hj
      have : ⁅d, j⁆ ∈ (⊥ : Subgroup H) := h3 ▸ Subgroup.commutator_mem_commutator hd hj
      rwa [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    have hDN : D ≤ N := by
      calc D = ⁅D, D⁆ := hDperf.symm
        _ ≤ N := by
          refine Subgroup.commutator_le.mpr fun d₁ hd₁ d₂ hd₂ => ?_
          have hdec : ∀ d ∈ D, ∃ z : H, (∀ h : H, z * h = h * z) ∧ ∃ n ∈ N, d = z * n := by
            intro d hd
            obtain ⟨j₀, hj₀, n₀, hn₀, rfl⟩ := hJN d
            refine ⟨j₀, ?_, n₀, hn₀, rfl⟩
            intro h
            obtain ⟨j', hj', n', hn', rfl⟩ := hJN h
            have hj₀c : j₀ * j' = j' * j₀ := by
              have := hDJ (j₀ * n₀) hd j' hj'
              have hn₀j : n₀ * j' = j' * n₀ := (hcomm j' hj' n₀ hn₀).symm
              calc j₀ * j' = j₀ * j' * n₀ * n₀⁻¹ := by group
                _ = j₀ * (j' * n₀) * n₀⁻¹ := by rw [mul_assoc j₀ j' n₀]
                _ = j₀ * (n₀ * j') * n₀⁻¹ := by rw [hn₀j]
                _ = (j₀ * n₀) * j' * n₀⁻¹ := by group
                _ = j' * (j₀ * n₀) * n₀⁻¹ := by rw [this]
                _ = j' * j₀ := by
                  calc j' * (j₀ * n₀) * n₀⁻¹ = j' * j₀ * (n₀ * n₀⁻¹) := by group
                    _ = j' * j₀ := by rw [mul_inv_cancel, mul_one]
            have hj₀n : j₀ * n' = n' * j₀ := hcomm j₀ hj₀ n' hn'
            calc j₀ * (j' * n') = (j₀ * j') * n' := (mul_assoc _ _ _).symm
              _ = (j' * j₀) * n' := by rw [hj₀c]
              _ = j' * (j₀ * n') := mul_assoc _ _ _
              _ = j' * (n' * j₀) := by rw [hj₀n]
              _ = (j' * n') * j₀ := (mul_assoc _ _ _).symm
          obtain ⟨z₁, hz₁, n₁, hn₁, rfl⟩ := hdec d₁ hd₁
          obtain ⟨z₂, hz₂, n₂, hn₂, rfl⟩ := hdec d₂ hd₂
          rw [commutatorElement_central_mul_left hz₁, commutatorElement_central_mul_right hz₂,
            commutatorElement_def]
          exact N.mul_mem (N.mul_mem (N.mul_mem hn₁ hn₂) (N.inv_mem hn₁)) (N.inv_mem hn₂)
    intro a ha
    exact hDN ⟨a, ha, rfl⟩
  · right
    intro j hj
    exact (hJA hj).1


theorem swap_dichotomy_of_inj {H P : Type*} [Group H] [Group P] (φ : P →* H)
    (α : H ≃* H) {N : Subgroup H} (hPN : ∀ h : H, ∃ p : P, ∃ n ∈ N, h = φ p * n)
    (hcomm : ∀ (p : P), ∀ n ∈ N, φ p * n = n * φ p)
    (hPperf : ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ = ⊤)
    (hPq : ∀ A : Subgroup P, A.Normal → A ≤ center P ∨ A = ⊤) :
    (∀ p : P, α (φ p) ∈ N) ∨ φ.range ≤ φ.range.map α.toMonoidHom := by
  have hJperf : ⁅φ.range, φ.range⁆ = φ.range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, hPperf]
  have key := swap_dichotomy α (J := φ.range) (N := N)
    (fun h => by
      obtain ⟨p, n, hn, rfl⟩ := hPN h
      exact ⟨φ p, ⟨p, rfl⟩, n, hn, rfl⟩)
    (by
      rintro _ ⟨p, rfl⟩ n hn
      exact hcomm p n hn)
    hJperf
    (by
      intro A hAJ hAn
      have hnormal : (A.comap φ).Normal := ⟨fun a ha p => by
        show φ (p * a * p⁻¹) ∈ A
        rw [map_mul, map_mul, map_inv]
        exact hAn _ ha _ ⟨p, rfl⟩⟩
      rcases hPq (A.comap φ) hnormal with hc | htop
      · left
        intro a ha j hj
        obtain ⟨a₀, rfl⟩ := hAJ ha
        obtain ⟨p, rfl⟩ := hj
        have := Subgroup.mem_center_iff.mp (hc ha) p
        rw [← map_mul, ← map_mul, this]
      · right
        rintro _ ⟨p, rfl⟩
        have : p ∈ A.comap φ := by rw [htop]; exact Subgroup.mem_top p
        exact this)
  rcases key with h | h
  · exact Or.inl fun p => h _ ⟨p, rfl⟩
  · exact Or.inr h

section Core

variable {Θ : Type*} {X : Type} [Group Θ] [Group X]

theorem key_core (f : Θ →* X) (Q : Subgroup Θ) [hQ : Q.Normal] (hker : f.ker ≤ Q)
    (hodd : ∀ q ∈ Q, Odd (orderOf q)) {Kb : Subgroup X} {u : X} {SX : Subgroup X}
    (hS : SData X Kb u SX) (hu1 : u ≠ 1) (hu2 : u * u = 1)
    (hKc : ∀ k ∈ Kb, (∀ g ∈ Kb, g * k = k * g) → k = 1)
    (hSR : SX ≤ f.range) (hRperf : ⁅f.range, f.range⁆ = f.range)
    (hRle : ∀ l ∈ f.range, ∃ m ∈ Kb, l * m⁻¹ ∈ centralizer (Kb : Set X))
    (hRu : ∀ l ∈ f.range, l * u = u * l) (α : (Θ ⧸ Q) ≃* (Θ ⧸ Q)) (yθ xθ : Θ) (hyθ : f yθ = u)
    (hαy : α (yθ : Θ ⧸ Q) = (yθ : Θ ⧸ Q)) (hαx : α (xθ : Θ ⧸ Q) = ((xθ * yθ : Θ) : Θ ⧸ Q))
    (P : Subgroup Θ) (hPperf : ⁅P, P⁆ = P) (hPC : ∀ p ∈ P, f p ∈ centralizer (Kb : Set X))
    (hxP : ∃ p ∈ P, (p : Θ ⧸ Q) = (xθ : Θ ⧸ Q)) : False := by
  classical
  have h1 := hS.inter_map_trivial f Q hodd hSR
  have h2 : ∀ θ₁ θ₂ : Θ, f θ₁ ∈ SX → f θ₂ ∈ SX → (θ₁ : Θ ⧸ Q) = θ₂ → f θ₁ = f θ₂ := by
    intro θ₁ θ₂ h₁ h₂ e
    have hq : θ₁⁻¹ * θ₂ ∈ Q := QuotientGroup.eq.1 e
    have := h1 ((f θ₁)⁻¹ * f θ₂) ⟨SX.mul_mem (SX.inv_mem h₁) h₂, θ₁⁻¹ * θ₂, hq, by simp⟩
    exact inv_mul_eq_one.1 this
  have hsplit := exists_split hS hRperf hRle hRu
  obtain ⟨ψ, hψ⟩ := exists_psi f Q hker
  let φ : ↥SX →* Θ ⧸ Q := ψ.comp (Subgroup.inclusion hSR)
  have hφ : ∀ (s : ↥SX) (θ : Θ), f θ = (s : X) → φ s = (θ : Θ ⧸ Q) := by
    intro s θ h
    have : (⟨(s : X), hSR s.2⟩ : f.range) = ⟨f θ, ⟨θ, rfl⟩⟩ := Subtype.ext h.symm
    show ψ ⟨(s : X), hSR s.2⟩ = _
    rw [this]
    exact hψ θ
  let N : Subgroup (Θ ⧸ Q) := ((centralizer (Kb : Set X)).comap f).map (QuotientGroup.mk' Q)
  have hPN : ∀ h : Θ ⧸ Q, ∃ p : ↥SX, ∃ n ∈ N, h = φ p * n := by
    intro h
    obtain ⟨θ, rfl⟩ := QuotientGroup.mk_surjective h
    obtain ⟨s, hs, c, hc, hl⟩ := hsplit (f θ) ⟨θ, rfl⟩
    obtain ⟨θ₁, hθ₁⟩ := hSR hs
    refine ⟨⟨s, hs⟩, ((θ₁⁻¹ * θ : Θ) : Θ ⧸ Q), ⟨θ₁⁻¹ * θ, ?_, rfl⟩, ?_⟩
    · show f (θ₁⁻¹ * θ) ∈ centralizer (Kb : Set X)
      rw [map_mul, map_inv, hθ₁, hl]
      simpa using hc
    · rw [hφ ⟨s, hs⟩ θ₁ hθ₁, ← QuotientGroup.mk_mul]
      simp
  have hcomm' : ∀ (p : ↥SX) (b : Θ), f b ∈ centralizer (Kb : Set X) →
      φ p * (b : Θ ⧸ Q) = (b : Θ ⧸ Q) * φ p := by
    intro p b hfb
    obtain ⟨a, ha⟩ := hSR p.2
    rw [hφ p a ha]
    show (a : Θ ⧸ Q) * (b : Θ ⧸ Q) = (b : Θ ⧸ Q) * (a : Θ ⧸ Q)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    apply hker
    rw [MonoidHom.mem_ker]
    have hc : f a * f b = f b * f a :=
      mem_centralizer_iff.mp hfb (f a) (hS.le_Kb (by rw [ha]; exact p.2))
    rw [map_mul, map_inv, map_mul, map_mul, hc, inv_mul_cancel]
  have hcomm : ∀ (p : ↥SX), ∀ n ∈ N, φ p * n = n * φ p := by
    intro p n hn
    obtain ⟨b, hb, rfl⟩ := hn
    exact hcomm' p b hb
  have hdich := swap_dichotomy_of_inj φ α hPN hcomm hS.perfTop
    (fun A hA => @SData.normal_P X _ Kb u SX hS A hA)
  have hyN : ∀ θ : Θ, f θ ∈ centralizer (Kb : Set X) → (θ : Θ ⧸ Q) = (yθ : Θ ⧸ Q) → False := by
    intro θ hθ he
    have hq : θ⁻¹ * yθ ∈ Q := QuotientGroup.eq.1 he
    have hr : Odd (orderOf ((f θ)⁻¹ * u)) := by
      have := (hodd _ hq).of_dvd_nat (orderOf_map_dvd f (θ⁻¹ * yθ))
      rwa [map_mul, map_inv, hyθ] at this
    have huK : u ∈ Kb := hS.le_Kb hS.mem
    have hcu : f θ * u = u * f θ := (mem_centralizer_iff.mp hθ u huK).symm
    have hcr : Commute (f θ) ((f θ)⁻¹ * u) := by
      refine (Commute.refl (f θ)).inv_right.mul_right ?_
      exact hcu
    have hueq : u = f θ * ((f θ)⁻¹ * u) := by group
    obtain ⟨k, hk⟩ := hr
    have hupow : u ^ (2 * k + 1) = u := by
      rw [pow_succ, pow_mul, sq, hu2, one_pow, one_mul]
    have hrpow : ((f θ)⁻¹ * u) ^ (2 * k + 1) = 1 := by
      rw [← hk]
      exact pow_orderOf_eq_one _
    have hu' : u = f θ ^ (2 * k + 1) := by
      have h3 := congrArg (fun z => z ^ (2 * k + 1)) hueq
      rw [hupow, hcr.mul_pow, hrpow, mul_one] at h3
      exact h3
    have huC : u ∈ centralizer (Kb : Set X) := by
      rw [hu']
      exact (centralizer (Kb : Set X)).pow_mem hθ _
    exact hu1 (hKc u huK fun g hg => (mem_centralizer_iff.mp huC g hg))
  have hφu : φ ⟨u, hS.mem⟩ = (yθ : Θ ⧸ Q) := hφ ⟨u, hS.mem⟩ yθ hyθ
  rcases hdich with hA | hB
  ·
    have hmem : α (φ ⟨u, hS.mem⟩) ∈ N := hA _
    rw [hφu, hαy] at hmem
    obtain ⟨θ, hθ, he⟩ := hmem
    exact hyN θ hθ he
  ·
    obtain ⟨p, hpP, hpx⟩ := hxP
    let P1 : Subgroup (Θ ⧸ Q) := (P.map (QuotientGroup.mk' Q)).map α.toMonoidHom
    have hP1perf : ⁅P1, P1⁆ = P1 := by
      have e1 : ⁅P.map (QuotientGroup.mk' Q), P.map (QuotientGroup.mk' Q)⁆ =
          P.map (QuotientGroup.mk' Q) := by
        rw [← Subgroup.map_commutator, hPperf]
      show ⁅(P.map (QuotientGroup.mk' Q)).map α.toMonoidHom,
        (P.map (QuotientGroup.mk' Q)).map α.toMonoidHom⁆ = _
      rw [← Subgroup.map_commutator, e1]
    have hP1comm : ∀ h ∈ P1, ∀ j ∈ φ.range, h * j = j * h := by
      rintro _ ⟨_, ⟨π, hπ, rfl⟩, rfl⟩ j hj
      obtain ⟨j', ⟨s, rfl⟩, hjj⟩ := hB hj
      rw [← hjj]
      show α (π : Θ ⧸ Q) * α (φ s) = α (φ s) * α (π : Θ ⧸ Q)
      rw [← map_mul, ← map_mul, (hcomm' s π (hPC π hπ)).symm]
    have hP1N : P1 ≤ N := by
      have hdec : ∀ d ∈ P1, ∃ z : Θ ⧸ Q, (∀ w : Θ ⧸ Q, z * w = w * z) ∧ ∃ n ∈ N, d = z * n := by
        intro d hd
        obtain ⟨s, n, hn, rfl⟩ := hPN d
        refine ⟨φ s, ?_, n, hn, rfl⟩
        intro w
        obtain ⟨s', n', hn', rfl⟩ := hPN w
        have hzs' : φ s * φ s' = φ s' * φ s := by
          have h3 := hP1comm _ hd (φ s') ⟨s', rfl⟩
          have h4 := hcomm s' n hn
          have h5 : φ s * φ s' * n = φ s' * φ s * n := by
            calc φ s * φ s' * n = φ s * (φ s' * n) := mul_assoc _ _ _
              _ = φ s * (n * φ s') := by rw [h4]
              _ = (φ s * n) * φ s' := (mul_assoc _ _ _).symm
              _ = φ s' * (φ s * n) := h3
              _ = φ s' * φ s * n := (mul_assoc _ _ _).symm
          exact mul_right_cancel h5
        have hzn' : φ s * n' = n' * φ s := hcomm s n' hn'
        calc φ s * (φ s' * n') = (φ s * φ s') * n' := (mul_assoc _ _ _).symm
          _ = (φ s' * φ s) * n' := by rw [hzs']
          _ = φ s' * (φ s * n') := mul_assoc _ _ _
          _ = φ s' * (n' * φ s) := by rw [hzn']
          _ = (φ s' * n') * φ s := (mul_assoc _ _ _).symm
      calc P1 = ⁅P1, P1⁆ := hP1perf.symm
        _ ≤ N := by
          refine Subgroup.commutator_le.mpr fun d₁ hd₁ d₂ hd₂ => ?_
          obtain ⟨z₁, hz₁, n₁, hn₁, rfl⟩ := hdec d₁ hd₁
          obtain ⟨z₂, hz₂, n₂, hn₂, rfl⟩ := hdec d₂ hd₂
          rw [commutatorElement_central_mul_left hz₁, commutatorElement_central_mul_right hz₂,
            commutatorElement_def]
          exact N.mul_mem (N.mul_mem (N.mul_mem hn₁ hn₂) (N.inv_mem hn₁)) (N.inv_mem hn₂)
    have hxN : (xθ : Θ ⧸ Q) ∈ N := by
      rw [← hpx]
      exact ⟨p, hPC p hpP, rfl⟩
    have hαxP1 : α (xθ : Θ ⧸ Q) ∈ P1 := ⟨(xθ : Θ ⧸ Q), ⟨p, hpP, hpx⟩, rfl⟩
    rw [hαx] at hαxP1
    have hxyN : ((xθ * yθ : Θ) : Θ ⧸ Q) ∈ N := hP1N hαxP1
    have hyN' : (yθ : Θ ⧸ Q) ∈ N := by
      have e : (yθ : Θ ⧸ Q) = ((xθ : Θ ⧸ Q))⁻¹ * ((xθ * yθ : Θ) : Θ ⧸ Q) := by
        rw [QuotientGroup.mk_mul]
        group
      rw [e]
      exact N.mul_mem (N.inv_mem hxN) hxyN
    obtain ⟨θ, hθ, he⟩ := hyN'
    exact hyN θ hθ he

end Core

end S3PumpSwap

end CFSG.GH74.Generic.BProg.B3
