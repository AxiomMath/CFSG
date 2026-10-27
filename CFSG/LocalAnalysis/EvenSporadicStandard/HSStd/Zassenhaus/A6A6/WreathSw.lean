module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.A6A6.WreathNS

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.A6A6

open Subgroup CFSG.EvenSporadicStandard.M22Std

variable {V : Type} [Group V] {G : Type} [Group G] {ρ : G →* MulAut V}

theorem cj_mul (g h : G) (H : Subgroup G) : cj (g * h) H = cj g (cj h H) := by
  ext y
  rw [mem_cj, mem_cj, mem_cj]
  simp [mul_assoc]

theorem cj_one (H : Subgroup G) : cj 1 H = H := by
  ext y
  rw [mem_cj]
  simp

theorem rho_apply_inv (g : G) (v : V) : ρ g (ρ g⁻¹ v) = v := by
  simp

theorem xor_aux : ∀ a b c : Bool, xor a (xor b c) = xor (xor a c) b := by decide

@[expose] def Bsub (c : Config ρ) : Bool → Subgroup V
  | false => c.U₁
  | true => c.U₂

@[expose] def Gfix (c : Config ρ) : Bool → Subgroup G
  | false => c.D
  | true => c.C

@[expose] def Gact (c : Config ρ) : Bool → Subgroup G
  | false => c.C
  | true => c.D

theorem mem_Bsub (c : Config ρ) (i : Bool) (v : V) :
    v ∈ Bsub c i ↔ ∀ x ∈ Gfix c i, ρ x v = v := by
  cases i
  · exact (c.D_fix v).symm
  · exact (c.C_fix v).symm

theorem finite_U₁ (c : Config ρ) : Finite c.U₁ :=
  Nat.finite_of_card_ne_zero (by rw [c.card_U₁]; omega)

structure SwapData (c : Config ρ) where
  hconj : ∀ g : G, (cj g c.C = c.C ∧ cj g c.D = c.D) ∨ (cj g c.C = c.D ∧ cj g c.D = c.C)
  g₁ : G
  hg₁ : cj g₁ c.C = c.D

namespace SwapData

variable {c : Config ρ} (d : SwapData c)

open Classical in
noncomputable def e (_d : SwapData c) (g : G) : Bool := decide (cj g c.C = c.D)

theorem e_eq_false_of {g : G} (h : cj g c.C = c.C) : d.e g = false := by
  simp [e, h, c.C_ne_D]

theorem e_eq_true_of {g : G} (h : cj g c.C = c.D) : d.e g = true := by
  simp [e, h]

theorem spec (g : G) : (d.e g = false ∧ cj g c.C = c.C ∧ cj g c.D = c.D) ∨
    (d.e g = true ∧ cj g c.C = c.D ∧ cj g c.D = c.C) := by
  rcases d.hconj g with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨d.e_eq_false_of h1, h1, h2⟩
  · exact Or.inr ⟨d.e_eq_true_of h1, h1, h2⟩

theorem e_one : d.e (1 : G) = false := d.e_eq_false_of (cj_one _)

theorem e_g₁ : d.e d.g₁ = true := d.e_eq_true_of d.hg₁

theorem e_mul (g h : G) : d.e (g * h) = xor (d.e g) (d.e h) := by
  rcases d.spec g with ⟨hg, g1, g2⟩ | ⟨hg, g1, g2⟩ <;>
    rcases d.spec h with ⟨hh, h1, h2⟩ | ⟨hh, h1, h2⟩ <;> rw [hg, hh]
  · exact d.e_eq_false_of (by rw [cj_mul, h1, g1])
  · exact d.e_eq_true_of (by rw [cj_mul, h1, g2])
  · exact d.e_eq_true_of (by rw [cj_mul, h1, g1])
  · exact d.e_eq_false_of (by rw [cj_mul, h1, g2])

theorem e_inv_g₁ : d.e d.g₁⁻¹ = true := by
  have h := d.e_mul d.g₁ d.g₁⁻¹
  rw [mul_inv_cancel, d.e_one, d.e_g₁] at h
  cases h' : d.e d.g₁⁻¹
  · rw [h'] at h
    simp at h
  · rfl

theorem cj_Gfix (g : G) (i : Bool) : cj g (Gfix c i) = Gfix c (xor i (d.e g)) := by
  rcases d.spec g with ⟨hg, g1, g2⟩ | ⟨hg, g1, g2⟩ <;> cases i <;> simp [hg, Gfix, g1, g2]

theorem cj_Gact (g : G) (i : Bool) : cj g (Gact c i) = Gact c (xor i (d.e g)) := by
  rcases d.spec g with ⟨hg, g1, g2⟩ | ⟨hg, g1, g2⟩ <;> cases i <;> simp [hg, Gact, g1, g2]

theorem blk (g : G) (i : Bool) {v : V} (hv : v ∈ Bsub c i) : ρ g v ∈ Bsub c (xor i (d.e g)) := by
  rw [mem_Bsub] at hv ⊢
  exact fix_map (d.cj_Gfix g i) hv

theorem e_Gact (i : Bool) {x : G} (hx : x ∈ Gact c i) : d.e x = false := by
  have hK : x ∈ c.C ⊔ c.D := by
    cases i
    · exact Subgroup.mem_sup_left hx
    · exact Subgroup.mem_sup_right hx
  apply d.e_eq_false_of
  ext y
  rw [mem_cj]
  have := sup_mem_normalizer c.comm x⁻¹ (inv_mem hK) y
  simpa [mul_assoc] using this.symm

@[expose] noncomputable def iota : Bool → c.U₁ →* V
  | false => c.U₁.subtype
  | true => (ρ d.g₁).toMonoidHom.comp c.U₁.subtype

theorem iota_true (u : c.U₁) : d.iota true u = ρ d.g₁ (u : V) := rfl

theorem iota_mem (i : Bool) (u : c.U₁) : d.iota i u ∈ Bsub c i := by
  cases i
  · exact u.2
  · have := d.blk d.g₁ false (c := c) (v := (u : V)) u.2
    rw [d.iota_true]
    simpa [d.e_g₁, Bsub] using this

theorem iota_inj (i : Bool) : Function.Injective (d.iota i) := by
  cases i
  · exact Subtype.val_injective
  · intro u u' h
    exact Subtype.val_injective ((ρ d.g₁).injective h)

theorem iota_surj (i : Bool) {v : V} (hv : v ∈ Bsub c i) : ∃ u, d.iota i u = v := by
  cases i
  · exact ⟨⟨v, hv⟩, rfl⟩
  · have h := d.blk d.g₁⁻¹ true hv
    rw [d.e_inv_g₁] at h
    refine ⟨⟨ρ d.g₁⁻¹ v, by simpa [Bsub] using h⟩, ?_⟩
    exact rho_apply_inv d.g₁ v

theorem ex (g : G) (i : Bool) (u : c.U₁) :
    ∃ u' : c.U₁, d.iota (xor i (d.e g)) u' = ρ g (d.iota i u) :=
  d.iota_surj _ (d.blk g i (d.iota_mem i u))

noncomputable def phiFun (g : G) (i : Bool) (u : c.U₁) : c.U₁ := Classical.choose (d.ex g i u)

theorem phiFun_spec (g : G) (i : Bool) (u : c.U₁) :
    d.iota (xor i (d.e g)) (d.phiFun g i u) = ρ g (d.iota i u) :=
  Classical.choose_spec (d.ex g i u)

noncomputable def phiHom (g : G) (i : Bool) : c.U₁ →* c.U₁ where
  toFun := d.phiFun g i
  map_one' := by
    apply d.iota_inj (xor i (d.e g))
    rw [d.phiFun_spec, map_one, map_one, map_one]
  map_mul' u u' := by
    apply d.iota_inj (xor i (d.e g))
    simp only [map_mul, d.phiFun_spec]

theorem phiHom_inj (g : G) (i : Bool) : Function.Injective (d.phiHom g i) := by
  intro u u' h
  have h' : ρ g (d.iota i u) = ρ g (d.iota i u') := by
    rw [← d.phiFun_spec g i u, ← d.phiFun_spec g i u']
    exact congrArg (d.iota _) h
  exact d.iota_inj i ((ρ g).injective h')

noncomputable def phi (g : G) (i : Bool) : MulAut c.U₁ :=
  haveI := finite_U₁ c
  MulEquiv.ofBijective (d.phiHom g i) (Finite.injective_iff_bijective.1 (d.phiHom_inj g i))

theorem iota_phi (g : G) (i : Bool) (u : c.U₁) :
    d.iota (xor i (d.e g)) (d.phi g i u) = ρ g (d.iota i u) :=
  d.phiFun_spec g i u

theorem phi_mul (g h : G) (i : Bool) :
    d.phi (g * h) i = d.phi g (xor i (d.e h)) * d.phi h i := by
  apply MulEquiv.ext
  intro u
  apply d.iota_inj (xor (xor i (d.e h)) (d.e g))
  have hj : xor i (d.e (g * h)) = xor (xor i (d.e h)) (d.e g) := by
    rw [d.e_mul, xor_aux]
  have L := d.iota_phi (g * h) i u
  rw [hj] at L
  have R := d.iota_phi g (xor i (d.e h)) (d.phi h i u)
  have R2 := d.iota_phi h i u
  show d.iota _ (d.phi (g * h) i u) = d.iota _ (d.phi g (xor i (d.e h)) (d.phi h i u))
  rw [L, R, R2]
  simp [map_mul]

theorem phi_one (i : Bool) : d.phi 1 i = 1 := by
  have h := d.phi_mul 1 1 i
  rw [one_mul, d.e_one, Bool.xor_false] at h
  exact mul_left_cancel (a := d.phi 1 i) (by rw [mul_one]; exact h.symm)

theorem phi_inv (g : G) (i : Bool) : d.phi g⁻¹ (xor i (d.e g)) = (d.phi g i)⁻¹ := by
  have h := d.phi_mul g⁻¹ g i
  rw [inv_mul_cancel, d.phi_one] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem phi_conj (g x : G) (i : Bool) (hx : d.e x = false) :
    d.phi (g * x * g⁻¹) (xor i (d.e g)) = d.phi g i * d.phi x i * (d.phi g i)⁻¹ := by
  have h1 := d.phi_mul g x i
  rw [hx, Bool.xor_false] at h1
  have h2 := d.phi_mul (g * x * g⁻¹) g i
  rw [show g * x * g⁻¹ * g = g * x by group, h1] at h2
  exact eq_mul_inv_of_mul_eq h2.symm

theorem phi_g₁ : d.phi d.g₁ false = 1 := by
  apply MulEquiv.ext
  intro u
  apply d.iota_inj true
  have h := d.iota_phi d.g₁ false u
  rw [d.e_g₁, Bool.false_xor] at h
  rw [h]
  rfl

noncomputable def aHom : c.C →* MulAut c.U₁ :=
  MonoidHom.mk' (fun x => d.phi x.1 false) (by
    intro x y
    rw [Subgroup.coe_mul, d.phi_mul, d.e_Gact false y.2, Bool.xor_false])

noncomputable def A : Subgroup (MulAut c.U₁) := d.aHom.range

theorem J (y : G) (hy : y ∈ c.C) : d.phi (d.g₁ * y * d.g₁⁻¹) true = d.phi y false := by
  have h := d.phi_conj d.g₁ y false (d.e_Gact false hy)
  rw [d.e_g₁, d.phi_g₁, Bool.false_xor] at h
  simpa using h

theorem claim_act (i : Bool) {x : G} (hx : x ∈ Gact c i) : d.phi x i ∈ d.A := by
  cases i
  · exact ⟨⟨x, hx⟩, rfl⟩
  · have hy : d.g₁⁻¹ * x * d.g₁ ∈ c.C := by
      have : x ∈ cj d.g₁ c.C := by rw [d.hg₁]; exact hx
      exact mem_cj.1 this
    have h := d.J _ hy
    rw [show d.g₁ * (d.g₁⁻¹ * x * d.g₁) * d.g₁⁻¹ = x by group] at h
    rw [h]
    exact ⟨⟨_, hy⟩, rfl⟩

theorem claim_rev (i : Bool) {a : MulAut c.U₁} (ha : a ∈ d.A) :
    ∃ x ∈ Gact c i, a = d.phi x i := by
  obtain ⟨⟨y, hy⟩, rfl⟩ := ha
  cases i
  · exact ⟨y, hy, rfl⟩
  · refine ⟨d.g₁ * y * d.g₁⁻¹, ?_, (d.J y hy).symm⟩
    have : d.g₁ * y * d.g₁⁻¹ ∈ cj d.g₁ c.C := by
      rw [mem_cj]
      simpa [mul_assoc] using hy
    rw [d.hg₁] at this
    exact this

theorem conj_mem (g : G) (i : Bool) {a : MulAut c.U₁} (ha : a ∈ d.A) :
    d.phi g i * a * (d.phi g i)⁻¹ ∈ d.A := by
  obtain ⟨x, hx, rfl⟩ := d.claim_rev i ha
  rw [← d.phi_conj g x i (d.e_Gact i hx)]
  apply d.claim_act
  have : g * x * g⁻¹ ∈ cj g (Gact c i) := by
    rw [mem_cj]
    simpa [mul_assoc] using hx
  rwa [d.cj_Gact] at this

theorem phi_mem_norm (g : G) (i : Bool) :
    d.phi g i ∈ normalizer (d.A : Set (MulAut c.U₁)) := by
  rw [mem_set_normalizer_iff]
  intro n
  simp only [SetLike.mem_coe]
  refine ⟨fun h => d.conj_mem g i h, fun h => ?_⟩
  have := d.conj_mem g⁻¹ (xor i (d.e g)) h
  rw [d.phi_inv] at this
  have e : (d.phi g i)⁻¹ * (d.phi g i * n * (d.phi g i)⁻¹) * ((d.phi g i)⁻¹)⁻¹ = n := by group
  rwa [e] at this

theorem aHom_injective (hV : Nat.card V = 256) (hρ : Function.Injective ρ) :
    Function.Injective d.aHom := by
  rw [injective_iff_map_eq_one]
  intro x hx
  apply Subtype.ext
  have h1 : ∀ v ∈ c.U₁, ρ x v = v := by
    intro v hv
    have h := d.iota_phi x.1 false ⟨v, hv⟩
    rw [d.e_Gact false x.2, Bool.xor_false] at h
    have hx' : d.phi x.1 false = 1 := hx
    rw [hx'] at h
    exact h.symm
  exact c.eq_one_of_fix hV hρ x.1 h1 (fun v hv => (c.C_fix v).2 hv x x.2)

noncomputable def eA (hV : Nat.card V = 256) (hρ : Function.Injective ρ) :
    d.A ≃* alternatingGroup (Fin 6) :=
  (MonoidHom.ofInjective (d.aHom_injective hV hρ)).symm.trans c.eC

end SwapData

theorem Config.exists_wreath_swap [Finite G] (hσ : NormalizerHom) (hc : ∀ x y : V, x * y = y * x)
    (hs : ∀ x : V, x * x = 1) (hV : Nat.card V = 256) (hρ : Function.Injective ρ)
    {c : Config ρ} (d : SwapData c) :
    ∃ f : G →* Equiv.Perm (Fin 2 × Fin 6), Function.Injective f ∧ ∀ g, f g ∈ wreathS6Z2 := by
  have := finite_U₁ c
  obtain ⟨σ, hσi⟩ := hσ c.U₁ (fun x y => Subtype.ext (hc x y)) (fun x => Subtype.ext (hs x))
    c.card_U₁ d.A ⟨d.eA hV hρ⟩
  refine exists_wr_hom d.e (fun g i => σ ⟨d.phi g i, d.phi_mem_norm g i⟩) d.e_mul ?_ ?_
  · intro g h i
    rw [← map_mul]
    congr 1
    exact Subtype.ext (d.phi_mul g h i)
  · intro g hg h0 h1
    have a0 : d.phi g false = 1 := congrArg Subtype.val (hσi (h0.trans (map_one σ).symm))
    have a1 : d.phi g true = 1 := congrArg Subtype.val (hσi (h1.trans (map_one σ).symm))
    apply c.eq_one_of_fix hV hρ g
    · intro v hv
      have h := d.iota_phi g false ⟨v, hv⟩
      rw [hg, Bool.xor_false, a0] at h
      exact h.symm
    · intro v hv
      obtain ⟨u, rfl⟩ := d.iota_surj true (c := c) hv
      have h := d.iota_phi g true u
      rw [hg, Bool.xor_false, a1] at h
      exact h.symm

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.A6A6
