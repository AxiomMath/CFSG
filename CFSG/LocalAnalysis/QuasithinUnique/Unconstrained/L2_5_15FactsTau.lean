module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15FactsSL3
public meta import Mathlib
public meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15FactsGen
public meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15FactsSL3
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15FactsTauInputs
public import Certificates.Certificate4041
public import Certificates.Certificate4145

public section

namespace CFSG.QuasithinUnique.Unc25K1

open CFSG.Open CFSG.Quasithin

theorem rcof_rmul (x y : R9) : rcof (rmul x y) = rmul (rcof x) (rcof y) := by
  simp only [rcof, rmul, R9.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

theorem rdet_rcof (x : R9) : rdet (rcof x) = rdet x ^ 2 := by
  simp only [rdet, rcof]
  ring

theorem rcof_rcof (x : R9) (h : rdet x = 1) : rcof (rcof x) = x := by
  have key : rcof (rcof x) = ⟨rdet x * x.a, rdet x * x.b, rdet x * x.c, rdet x * x.d,
      rdet x * x.e, rdet x * x.f, rdet x * x.g, rdet x * x.h, rdet x * x.i⟩ := by
    simp only [rcof, rdet, R9.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring
  rw [key, h]
  obtain ⟨a, b, c, d, e, f, g, h', i⟩ := x
  simp

@[expose] def tauFun (x : S3) : S3 :=
  ofR9 (rcof (rr x)) (by rw [rdet_rcof, rr_det]; norm_num)

theorem rr_tauFun (x : S3) : rr (tauFun x) = rcof (rr x) := rr_ofR9 _ _

theorem tauFun_mul (x y : S3) : tauFun (x * y) = tauFun x * tauFun y := by
  apply rr_inj
  rw [rr_tauFun, rr_mul, rr_mul, rr_tauFun, rr_tauFun, rcof_rmul]

theorem tauFun_tauFun (x : S3) : tauFun (tauFun x) = x := by
  apply rr_inj
  rw [rr_tauFun, rr_tauFun, rcof_rcof _ (rr_det x)]

@[expose] def tauAut : MulAut S3 where
  toFun := tauFun
  invFun := tauFun
  left_inv := tauFun_tauFun
  right_inv := tauFun_tauFun
  map_mul' := tauFun_mul

theorem tau_tau (x : S3) : tauAut (tauAut x) = x := tauFun_tauFun x

theorem tau_mul_tau : tauAut * tauAut = 1 := by
  apply MulEquiv.ext
  intro x
  exact tau_tau x

theorem raw_notinner :
    ∀ r ∈ rawList, rmul r (rr x1S) ≠ rmul (rcof (rr x1S)) r :=
  Certificates.certificate4041.1

theorem raw_R1 : ∀ r ∈ rawList, rmul r (rcof r) = rone →
    ∃ h ∈ rawList, rmul r (rcof h) = h :=
  Certificates.certificate4041.2.1

theorem raw_R2 :
    ∀ r ∈ rawList, (∀ t ∈ TlS.map rr, rmul r (rcof t) = rmul t r) →
    rmul r (rcof r) = rr u0S :=
  Certificates.certificate4041.2.2.1

theorem raw_noE8 :
    ∀ a ∈ invR, ∀ b ∈ invR, ∀ c ∈ invR, rmul a b = rmul b a → rmul a c = rmul c a →
    rmul b c = rmul c b → a ≠ b → c ≠ a → c ≠ b → c ≠ rmul a b → False :=
  Certificates.certificate4041.2.2.2.1

theorem raw_klein :
    ∀ a ∈ invR, ∀ b ∈ invR, a ≠ b → rmul a b = rmul b a →
    ∃ g ∈ rawList, rmul g (rr u0S) = rmul a g ∧ rmul g (rr d2S) = rmul b g :=
  Certificates.certificate4041.2.2.2.2.1

theorem raw_cent : ∀ r ∈ rawList, rmul r (rr u0S) = rmul (rr u0S) r →
    rmul r (rr d2S) = rmul (rr d2S) r →
    r = rone ∨ r = rr u0S ∨ r = rr d2S ∨ r = rmul (rr u0S) (rr d2S) :=
  Certificates.certificate4041.2.2.2.2.2.1

theorem small_facts : rmul (rr d2S) (rr d2S) = rone ∧
    rmul (rr u0S) (rr d2S) = rmul (rr d2S) (rr u0S) ∧ rr d2S ≠ rone ∧ rr u0S ≠ rr d2S ∧
    rcof (rr u0S) = rr u0S ∧ rcof (rr d2S) = rr d2S :=
  Certificates.certificate4041.2.2.2.2.2.2

theorem mem_invR {x : S3} (h1 : x ≠ 1) (h2 : x * x = 1) : rr x ∈ invR := by
  unfold invR
  rw [List.mem_filter]
  refine ⟨rr_mem x, ?_⟩
  have a : rr x ≠ rone := fun h => h1 ((rr_eq_one_iff x).2 h)
  have b : rmul (rr x) (rr x) = rone := by rw [← rr_mul, h2, rr_one]
  simp [a, b]

theorem tau_not_inner (g : S3) : MulAut.conj g ≠ tauAut := by
  intro h
  have h0 := congrArg (fun α : MulAut S3 => α x1S) h
  have h1 : g * x1S * g⁻¹ = tauFun x1S := h0
  have h2 : g * x1S = tauFun x1S * g := by
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1
  have h3 : rmul (rr g) (rr x1S) = rmul (rcof (rr x1S)) (rr g) := by
    rw [← rr_mul, ← rr_tauFun, ← rr_mul, h2]
  exact raw_notinner (rr g) (rr_mem g) h3

theorem R1S {g : S3} (hg : g * tauAut g = 1) : ∃ h : S3, g * tauAut h = h := by
  have h1 : rmul (rr g) (rcof (rr g)) = rone := by
    rw [← rr_tauFun, ← rr_mul]
    exact (rr_eq_one_iff _).1 hg
  obtain ⟨h', hh', hgh⟩ := raw_R1 (rr g) (rr_mem g) h1
  have hrr : rr (ofR9 h' (det_of_mem_rawList hh')) = h' := rr_ofR9 _ _
  refine ⟨ofR9 h' (det_of_mem_rawList hh'), rr_inj ?_⟩
  show rr (g * tauFun (ofR9 h' (det_of_mem_rawList hh'))) = rr (ofR9 h' (det_of_mem_rawList hh'))
  rw [rr_mul, rr_tauFun, hrr]
  exact hgh

theorem R2S {g : S3} (hg : ∀ t ∈ TlS, g * tauAut t = t * g) : g * tauAut g = u0S := by
  apply rr_inj
  show rr (g * tauFun g) = rr u0S
  rw [rr_mul, rr_tauFun]
  apply raw_R2 (rr g) (rr_mem g)
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ht
  have h2 := congrArg rr (hg s hs)
  rw [rr_mul, rr_mul, show rr (tauAut s) = rcof (rr s) from rr_tauFun s] at h2
  exact h2

theorem noE8S {a b c : S3} (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) (hc1 : c ≠ 1) (hca : c ≠ a)
    (hcb : c ≠ b) (hcab : c ≠ a * b) (haa : a * a = 1) (hbb : b * b = 1) (hcc : c * c = 1)
    (hab' : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b) : False := by
  refine raw_noE8 (rr a) (mem_invR ha1 haa) (rr b) (mem_invR hb1 hbb) (rr c) (mem_invR hc1 hcc)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← rr_mul, ← rr_mul, hab']
  · rw [← rr_mul, ← rr_mul, hac]
  · rw [← rr_mul, ← rr_mul, hbc]
  · exact fun h => hab ((rr_eq_iff a b).2 h)
  · exact fun h => hca ((rr_eq_iff c a).2 h)
  · exact fun h => hcb ((rr_eq_iff c b).2 h)
  · exact fun h => hcab ((rr_eq_iff c (a * b)).2 (by rw [rr_mul]; exact h))

theorem tau_u0S : tauAut u0S = u0S :=
  rr_inj (by
    show rr (tauFun u0S) = rr u0S
    rw [rr_tauFun]
    exact small_facts.2.2.2.2.1)

theorem tau_d2S : tauAut d2S = d2S :=
  rr_inj (by
    show rr (tauFun d2S) = rr d2S
    rw [rr_tauFun]
    exact small_facts.2.2.2.2.2)

theorem kleinS {a b : S3} (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) (haa : a * a = 1)
    (hbb : b * b = 1) (hcomm : a * b = b * a) :
    ∃ g : S3, g * u0S * g⁻¹ = a ∧ g * d2S * g⁻¹ = b := by
  obtain ⟨g', hg', h1, h2⟩ := raw_klein (rr a) (mem_invR ha1 haa) (rr b) (mem_invR hb1 hbb)
    (fun h => hab ((rr_eq_iff a b).2 h)) (by rw [← rr_mul, ← rr_mul, hcomm])
  refine ⟨ofR9 g' (det_of_mem_rawList hg'), ?_, ?_⟩
  · rw [mul_inv_eq_iff_eq_mul]
    apply rr_inj
    rw [rr_mul, rr_mul, rr_ofR9]
    exact h1
  · rw [mul_inv_eq_iff_eq_mul]
    apply rr_inj
    rw [rr_mul, rr_mul, rr_ofR9]
    exact h2

theorem centS {x : S3} (h1 : x * u0S = u0S * x) (h2 : x * d2S = d2S * x) :
    x = 1 ∨ x = u0S ∨ x = d2S ∨ x = u0S * d2S := by
  have := raw_cent (rr x) (rr_mem x) (by rw [← rr_mul, ← rr_mul, h1])
    (by rw [← rr_mul, ← rr_mul, h2])
  rcases this with h | h | h | h
  · exact Or.inl ((rr_eq_one_iff x).2 h)
  · exact Or.inr (Or.inl ((rr_eq_iff x u0S).2 h))
  · exact Or.inr (Or.inr (Or.inl ((rr_eq_iff x d2S).2 h)))
  · exact Or.inr (Or.inr (Or.inr ((rr_eq_iff x (u0S * d2S)).2 (by rw [rr_mul]; exact h))))

theorem conj_injective_S3 : Function.Injective (MulAut.conj : S3 →* MulAut S3) := by
  intro g h hgh
  have hc : ∀ x : S3, g * x * g⁻¹ = h * x * h⁻¹ := fun x => by
    have := congrArg (fun α : MulAut S3 => α x) hgh
    exact this
  have hz : h⁻¹ * g ∈ Subgroup.center S3 := by
    rw [Subgroup.mem_center_iff]
    intro y
    have e : h⁻¹ * g * y = y * (h⁻¹ * g) := by
      calc h⁻¹ * g * y = h⁻¹ * (g * y * g⁻¹) * g := by group
        _ = h⁻¹ * (h * y * h⁻¹) * g := by rw [hc y]
        _ = y * (h⁻¹ * g) := by group
    exact e.symm
  rw [center_S3_eq_bot, Subgroup.mem_bot] at hz
  exact (inv_mul_eq_one.1 hz).symm

theorem aut_cases (hb : Nat.card (MulAut S3) ≤ 2 * Nat.card S3) (α : MulAut S3) :
    ∃ g : S3, α = MulAut.conj g ∨ α = MulAut.conj g * tauAut := by
  let Φ : S3 × Bool → MulAut S3 := fun p => if p.2 then MulAut.conj p.1 * tauAut else MulAut.conj p.1
  have hΦ : Function.Injective Φ := by
    rintro ⟨g, ε⟩ ⟨h, δ⟩ hgh
    cases ε <;> cases δ
    · have : MulAut.conj g = MulAut.conj h := hgh
      rw [conj_injective_S3 this]
    · exfalso
      have h1 : MulAut.conj g = MulAut.conj h * tauAut := hgh
      apply tau_not_inner (h⁻¹ * g)
      rw [map_mul, map_inv, h1]
      group
    · exfalso
      have h1 : MulAut.conj g * tauAut = MulAut.conj h := hgh
      apply tau_not_inner (g⁻¹ * h)
      rw [map_mul, map_inv, ← h1]
      group
    · have h1 : MulAut.conj g * tauAut = MulAut.conj h * tauAut := hgh
      have : MulAut.conj g = MulAut.conj h := mul_right_cancel h1
      rw [conj_injective_S3 this]
  have hbij : Function.Bijective Φ := by
    refine hΦ.bijective_of_nat_card_le ?_
    rw [Nat.card_prod]
    simpa [mul_comm] using hb
  obtain ⟨⟨g, ε⟩, hge⟩ := hbij.2 α
  cases ε
  · exact ⟨g, Or.inl hge.symm⟩
  · exact ⟨g, Or.inr hge.symm⟩

theorem z4S (hb : Nat.card (MulAut S3) ≤ 2 * Nat.card S3) {u : S3} (hu1 : u ≠ 1)
    (hu2 : u * u = 1) (β : MulAut S3) (hfix : ∀ s : S3, s * u = u * s → s ^ 3 = 1 → β s = s)
    (hinner : ∀ g : S3, β ≠ MulAut.conj g) : ∀ w : S3, β (β w) = u * w * u⁻¹ := by
  obtain ⟨h, hh⟩ := hconjS u hu1 (by rw [sq]; exact hu2)
  obtain ⟨g, hg | hg⟩ := aut_cases hb β
  · exact absurd hg (hinner g)
  · have hβ : ∀ w, β w = g * tauAut w * g⁻¹ := fun w => by rw [hg]; rfl
    have hg' : ∀ t ∈ TlS, (h⁻¹ * g * tauAut h) * tauAut t = t * (h⁻¹ * g * tauAut h) := by
      intro t ht
      obtain ⟨ht1, ht3⟩ := (hTlS t).2 ht
      have hs1 : (h * t * h⁻¹) * u = u * (h * t * h⁻¹) := by
        rw [← hh]
        calc h * t * h⁻¹ * (h * u0S * h⁻¹) = h * (t * u0S) * h⁻¹ := by group
          _ = h * (u0S * t) * h⁻¹ := by rw [ht1]
          _ = h * u0S * h⁻¹ * (h * t * h⁻¹) := by group
      have hs3 : (h * t * h⁻¹) ^ 3 = 1 := by
        have : (h * t * h⁻¹) ^ 3 = h * t ^ 3 * h⁻¹ := conj_pow
        rw [this, ht3]
        group
      have hfx := hfix _ hs1 hs3
      rw [hβ, map_mul, map_mul, map_inv] at hfx
      calc h⁻¹ * g * tauAut h * tauAut t
          = h⁻¹ * (g * (tauAut h * tauAut t * (tauAut h)⁻¹) * g⁻¹) * (g * tauAut h) := by group
        _ = h⁻¹ * (h * t * h⁻¹) * (g * tauAut h) := by rw [hfx]
        _ = t * (h⁻¹ * g * tauAut h) := by group
    have hR2 := R2S hg'
    have hgg : g * tauAut g = u := by
      have e : h * ((h⁻¹ * g * tauAut h) * tauAut (h⁻¹ * g * tauAut h)) * h⁻¹ = g * tauAut g := by
        rw [map_mul, map_mul, map_inv, tau_tau]
        group
      rw [← e, hR2, hh]
    intro w
    rw [hβ, hβ, map_mul, map_mul, map_inv, tau_tau, ← hgg]
    group

theorem outerS {g g' : S3} (hg : g * tauAut g = 1) (hg' : g' * tauAut g' = 1) :
    ∃ h : S3, h⁻¹ * g * tauAut h = g' := by
  obtain ⟨h₁, hh₁⟩ := R1S hg
  obtain ⟨h₂, hh₂⟩ := R1S hg'
  refine ⟨h₁ * h₂⁻¹, ?_⟩
  have e1 : g' = h₂ * (tauAut h₂)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    exact hh₂
  rw [e1, map_mul, map_inv]
  calc (h₁ * h₂⁻¹)⁻¹ * g * (tauAut h₁ * (tauAut h₂)⁻¹)
      = h₂ * h₁⁻¹ * (g * tauAut h₁) * (tauAut h₂)⁻¹ := by group
    _ = h₂ * h₁⁻¹ * h₁ * (tauAut h₂)⁻¹ := by rw [hh₁]
    _ = h₂ * (tauAut h₂)⁻¹ := by group

theorem kleinOuterS {a b : S3} (hg : ∃ g : S3, g * u0S * g⁻¹ = a ∧ g * d2S * g⁻¹ = b) :
    ∃ β : MulAut S3, β * β = 1 ∧ (∀ h : S3, β ≠ MulAut.conj h) ∧ β a = a ∧ β b = b := by
  obtain ⟨g, ha, hb⟩ := hg
  have hβ : ∀ x, (MulAut.conj g * tauAut * (MulAut.conj g)⁻¹) x =
      g * tauAut (g⁻¹ * x * g) * g⁻¹ := fun x => rfl
  refine ⟨MulAut.conj g * tauAut * (MulAut.conj g)⁻¹, ?_, ?_, ?_, ?_⟩
  · calc MulAut.conj g * tauAut * (MulAut.conj g)⁻¹ * (MulAut.conj g * tauAut * (MulAut.conj g)⁻¹)
        = MulAut.conj g * (tauAut * tauAut) * (MulAut.conj g)⁻¹ := by group
      _ = 1 := by rw [tau_mul_tau]; group
  · intro h hh
    apply tau_not_inner (g⁻¹ * h * g)
    have : tauAut = (MulAut.conj g)⁻¹ * MulAut.conj h * MulAut.conj g := by
      rw [← hh]
      group
    rw [map_mul, map_mul, map_inv]
    exact this.symm
  · rw [hβ]
    have : g⁻¹ * a * g = u0S := by rw [← ha]; group
    rw [this, tau_u0S, ha]
  · rw [hβ]
    have : g⁻¹ * b * g = d2S := by rw [← hb]; group
    rw [this, tau_d2S, hb]

end CFSG.QuasithinUnique.Unc25K1
