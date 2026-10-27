module

public import CFSG.GH74.Generic.BProg.B3.S3FusionSD

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3Fusion

open Subgroup
open scoped commutatorElement

theorem swap_le_of_inj {H P : Type*} [Group H] [Group P] (φ : P →* H) (hφ : Function.Injective φ)
    (α : H ≃* H) {N : Subgroup H} (hPN : ∀ h : H, ∃ p : P, ∃ n ∈ N, h = φ p * n)
    (hcomm : ∀ (p : P), ∀ n ∈ N, φ p * n = n * φ p) (hPperf : ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ = ⊤)
    (hPq : ∀ A : Subgroup P, A.Normal → A ≤ center P ∨ A = ⊤) {py : P} (hpy2 : py * py = 1)
    (hpyun : ∀ i : P, i * i = 1 → i = 1 ∨ i = py) (hα : α (φ py) ∉ φ.range) :
    ∀ p : P, α (φ p) ∈ N := by
  have hJperf : ⁅φ.range, φ.range⁆ = φ.range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, hPperf]
  have key := swap_le α (J := φ.range) (N := N) (jy := φ py)
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
    ⟨py, rfl⟩ (by rw [← map_mul, hpy2, map_one])
    (by
      rintro _ ⟨p, rfl⟩ hp2
      have : p * p = 1 := hφ (by rw [map_mul, hp2, map_one])
      rcases hpyun p this with h | h
      · left; rw [h, map_one]
      · right; rw [h])
    hα
  exact fun p => key _ ⟨p, rfl⟩

section SDataP

variable {X : Type} [Group X] {Kb : Subgroup X} {u : X} {SX : Subgroup X}

theorem SData.perfTop (hS : SData X Kb u SX) : ⁅(⊤ : Subgroup ↥SX), (⊤ : Subgroup ↥SX)⁆ = ⊤ := by
  have hperf : Group.IsPerfect ↥SX := Subgroup.isPerfect_iff.2 hS.perf
  exact (_root_.commutator_def _).symm.trans hperf.commutator_eq_top

theorem SData.normal_P (hS : SData X Kb u SX) (A : Subgroup ↥SX) [hA : A.Normal] :
    A ≤ center ↥SX ∨ A = ⊤ := by
  have hAle : A.map SX.subtype ≤ SX := Subgroup.map_subtype_le A
  have hnorm : ∀ a ∈ A.map SX.subtype, ∀ s ∈ SX, s * a * s⁻¹ ∈ A.map SX.subtype := by
    rintro _ ⟨a, ha, rfl⟩ s hs
    exact ⟨⟨s, hs⟩ * a * ⟨s, hs⟩⁻¹, hA.conj_mem a ha ⟨s, hs⟩, by simp⟩
  rcases hS.normal_quasi _ hAle hnorm with hc | htop
  · left
    intro a ha
    rw [Subgroup.mem_center_iff]
    intro s
    exact Subtype.ext (hc (a : X) ⟨a, ha, rfl⟩ (s : X) s.2).symm
  · right
    apply top_unique
    intro a _
    obtain ⟨a', ha', e⟩ := htop a.2
    have : a' = a := Subtype.ext e
    rw [← this]
    exact ha'

theorem exists_split (hS : SData X Kb u SX) {R : Subgroup X} (hRperf : ⁅R, R⁆ = R)
    (hRle : ∀ l ∈ R, ∃ m ∈ Kb, l * m⁻¹ ∈ centralizer (Kb : Set X)) (hRu : ∀ l ∈ R, l * u = u * l) :
    ∀ l ∈ R, ∃ s ∈ SX, ∃ c ∈ centralizer (Kb : Set X), l = s * c := by
  set Cb : Subgroup X := centralizer (Kb : Set X) with hCb
  have hle : ⁅Cb, Cb⁆ ≤ Cb := commutator_le_self' Cb
  have hAB : ∀ a ∈ Kb, ∀ b ∈ Cb, a * b = b * a := fun a ha b hb => mem_centralizer_iff.mp hb a ha
  have hu : u ∈ Kb := hS.le_Kb hS.mem
  let W : Subgroup X :=
    { carrier := {g | ∃ k ∈ SX, ∃ c ∈ ⁅Cb, Cb⁆, g = k * c}
      one_mem' := ⟨1, one_mem _, 1, one_mem _, (mul_one 1).symm⟩
      mul_mem' := by
        rintro _ _ ⟨k₁, hk₁, c₁, hc₁, rfl⟩ ⟨k₂, hk₂, c₂, hc₂, rfl⟩
        refine ⟨k₁ * k₂, SX.mul_mem hk₁ hk₂, c₁ * c₂, mul_mem hc₁ hc₂, ?_⟩
        have e : c₁ * k₂ = k₂ * c₁ := (mem_centralizer_iff.mp (hle hc₁) k₂ (hS.le_Kb hk₂)).symm
        calc k₁ * c₁ * (k₂ * c₂) = k₁ * (c₁ * k₂) * c₂ := by group
          _ = k₁ * (k₂ * c₁) * c₂ := by rw [e]
          _ = k₁ * k₂ * (c₁ * c₂) := by group
      inv_mem' := by
        rintro _ ⟨k, hk, c, hc, rfl⟩
        refine ⟨k⁻¹, SX.inv_mem hk, c⁻¹, inv_mem hc, ?_⟩
        have e : k⁻¹ * c⁻¹ = c⁻¹ * k⁻¹ :=
          mem_centralizer_iff.mp (hle (inv_mem hc)) k⁻¹ (Kb.inv_mem (hS.le_Kb hk))
        rw [mul_inv_rev, e] }
  have hcu : ∀ l ∈ R, ∀ m ∈ Kb, l * m⁻¹ ∈ Cb → m * u = u * m := by
    intro l hl m hm hc
    have hcu : (l * m⁻¹) * u = u * (l * m⁻¹) := (mem_centralizer_iff.mp hc u hu).symm
    have hlu := hRu l hl
    have : (l * m⁻¹) * (m * u) = (l * m⁻¹) * (u * m) := by
      calc (l * m⁻¹) * (m * u) = l * u := by group
        _ = u * l := hlu
        _ = u * ((l * m⁻¹) * m) := by group
        _ = (u * (l * m⁻¹)) * m := by group
        _ = ((l * m⁻¹) * u) * m := by rw [hcu]
        _ = (l * m⁻¹) * (u * m) := by group
    exact mul_left_cancel this
  have hRW : R ≤ W := by
    calc R = ⁅R, R⁆ := hRperf.symm
      _ ≤ W := by
        refine Subgroup.commutator_le.mpr fun l₁ hl₁ l₂ hl₂ => ?_
        obtain ⟨m₁, hm₁, hc₁⟩ := hRle l₁ hl₁
        obtain ⟨m₂, hm₂, hc₂⟩ := hRle l₂ hl₂
        have e₁ : l₁ = m₁ * (l₁ * m₁⁻¹) := by
          have := hAB m₁ hm₁ _ hc₁
          calc l₁ = (l₁ * m₁⁻¹) * m₁ := by group
            _ = m₁ * (l₁ * m₁⁻¹) := this.symm
        have e₂ : l₂ = m₂ * (l₂ * m₂⁻¹) := by
          have := hAB m₂ hm₂ _ hc₂
          calc l₂ = (l₂ * m₂⁻¹) * m₂ := by group
            _ = m₂ * (l₂ * m₂⁻¹) := this.symm
        rw [e₁, e₂, commutatorElement_mul_mul_of_commute hAB hm₁ hm₂ hc₁ hc₂]
        exact ⟨⁅m₁, m₂⁆, hS.comm_mem m₁ hm₁ m₂ hm₂ (hcu l₁ hl₁ m₁ hm₁ hc₁) (hcu l₂ hl₂ m₂ hm₂ hc₂),
          ⁅l₁ * m₁⁻¹, l₂ * m₂⁻¹⁆, Subgroup.commutator_mem_commutator hc₁ hc₂, rfl⟩
  intro l hl
  obtain ⟨s, hs, c, hc, rfl⟩ := hRW hl
  exact ⟨s, hs, c, hle hc, rfl⟩

end SDataP

section Psi

variable {Θ X : Type*} [Group Θ] [Group X]

theorem exists_psi (f : Θ →* X) (Q : Subgroup Θ) [Q.Normal] (hQ : f.ker ≤ Q) :
    ∃ ψ : f.range →* Θ ⧸ Q, ∀ θ : Θ, ψ ⟨f θ, ⟨θ, rfl⟩⟩ = (θ : Θ ⧸ Q) := by
  have hsurj := f.rangeRestrict_surjective
  refine ⟨(f.rangeRestrict).liftOfRightInverse (Function.surjInv hsurj)
    (Function.rightInverse_surjInv hsurj) ⟨QuotientGroup.mk' Q, ?_⟩, fun θ => ?_⟩
  · rw [MonoidHom.ker_rangeRestrict, QuotientGroup.ker_mk']
    exact hQ
  · exact MonoidHom.liftOfRightInverse_comp_apply (f.rangeRestrict) (Function.surjInv hsurj)
      (Function.rightInverse_surjInv hsurj) ⟨QuotientGroup.mk' Q, _⟩ θ

end Psi

section Core

variable {Θ : Type*} {X : Type} [Group Θ] [Group X]

theorem SData.inter_map_trivial {Kb : Subgroup X} {u : X} {SX : Subgroup X} (hS : SData X Kb u SX)
    (f : Θ →* X) (Q : Subgroup Θ) [hQ : Q.Normal] (hodd : ∀ q ∈ Q, Odd (orderOf q))
    (hSR : SX ≤ f.range) : ∀ a ∈ SX ⊓ Q.map f, a = 1 := by
  refine hS.odd_normal (SX ⊓ Q.map f) inf_le_left ?_ ?_
  · intro a ha s hs
    refine ⟨SX.mul_mem (SX.mul_mem hs ha.1) (SX.inv_mem hs), ?_⟩
    obtain ⟨q, hq, rfl⟩ := ha.2
    obtain ⟨θ₀, rfl⟩ := hSR hs
    exact ⟨θ₀ * q * θ₀⁻¹, hQ.conj_mem q hq θ₀, by simp⟩
  · rintro a ⟨-, q, hq, rfl⟩
    exact (hodd q hq).of_dvd_nat (orderOf_map_dvd f q)

theorem swap_core (f : Θ →* X) (Q : Subgroup Θ) [hQ : Q.Normal] (hker : f.ker ≤ Q)
    (hodd : ∀ q ∈ Q, Odd (orderOf q)) {Kb : Subgroup X} {u : X} {SX : Subgroup X}
    (hS : SData X Kb u SX) (hu2 : u * u = 1) (hSR : SX ≤ f.range) (hRperf : ⁅f.range, f.range⁆ = f.range)
    (hRle : ∀ l ∈ f.range, ∃ m ∈ Kb, l * m⁻¹ ∈ centralizer (Kb : Set X))
    (hRu : ∀ l ∈ f.range, l * u = u * l) (α : (Θ ⧸ Q) ≃* (Θ ⧸ Q)) (yθ : Θ) (hyθ : f yθ = u)
    (hα : ∀ θ' : Θ, f θ' ∈ SX → α (yθ : Θ ⧸ Q) ≠ (θ' : Θ ⧸ Q)) :
    ∀ θ : Θ, f θ ∈ SX → ∃ θc : Θ, f θc ∈ centralizer (Kb : Set X) ∧
      α (θ : Θ ⧸ Q) = (θc : Θ ⧸ Q) := by
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
  have hφinj : Function.Injective φ := by
    intro s₁ s₂ e
    obtain ⟨θ₁, hθ₁⟩ := hSR s₁.2
    obtain ⟨θ₂, hθ₂⟩ := hSR s₂.2
    have e' : (θ₁ : Θ ⧸ Q) = θ₂ := by rw [← hφ s₁ θ₁ hθ₁, ← hφ s₂ θ₂ hθ₂, e]
    have := h2 θ₁ θ₂ (hθ₁ ▸ s₁.2) (hθ₂ ▸ s₂.2) e'
    exact Subtype.ext (hθ₁.symm.trans (this.trans hθ₂))
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
  have hcomm : ∀ (p : ↥SX), ∀ n ∈ N, φ p * n = n * φ p := by
    intro p n hn
    obtain ⟨b, hb, rfl⟩ := hn
    obtain ⟨a, ha⟩ := hSR p.2
    rw [hφ p a ha]
    show (a : Θ ⧸ Q) * (b : Θ ⧸ Q) = (b : Θ ⧸ Q) * (a : Θ ⧸ Q)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    apply hker
    rw [MonoidHom.mem_ker]
    have hfb : f b ∈ centralizer (Kb : Set X) := hb
    have hc : f a * f b = f b * f a :=
      mem_centralizer_iff.mp hfb (f a) (hS.le_Kb (by rw [ha]; exact p.2))
    rw [map_mul, map_inv, map_mul, map_mul, hc, inv_mul_cancel]
  have hpy2 : (⟨u, hS.mem⟩ : ↥SX) * ⟨u, hS.mem⟩ = 1 := Subtype.ext hu2
  have hpyun : ∀ i : ↥SX, i * i = 1 → i = 1 ∨ i = ⟨u, hS.mem⟩ := by
    intro i hi
    rcases hS.inv (i : X) i.2 (by simpa using congrArg Subtype.val hi) with h | h
    · left; exact Subtype.ext h
    · right; exact Subtype.ext h
  have hαφ : α (φ ⟨u, hS.mem⟩) ∉ φ.range := by
    rw [hφ ⟨u, hS.mem⟩ yθ hyθ]
    rintro ⟨s, hs⟩
    obtain ⟨θ', hθ'⟩ := hSR s.2
    rw [hφ s θ' hθ'] at hs
    exact hα θ' (by rw [hθ']; exact s.2) hs.symm
  have key := swap_le_of_inj φ hφinj α hPN hcomm hS.perfTop
    (fun A hA => @SData.normal_P X _ Kb u SX hS A hA) hpy2 hpyun hαφ
  intro θ hθ
  have := key ⟨f θ, hθ⟩
  rw [hφ ⟨f θ, hθ⟩ θ rfl] at this
  obtain ⟨θc, hθc, e⟩ := this
  exact ⟨θc, hθc, e.symm⟩

end Core

end S3Fusion

end CFSG.GH74.Generic.BProg.B3
