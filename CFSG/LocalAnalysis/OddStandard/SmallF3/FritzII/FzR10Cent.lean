module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10Gen
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzRFu
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzDefs

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Certificates.FzR10 Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau : G} {T₂ : Subgroup G}
variable (D : FzRNum t x₁ x₂ lam rho tau T₂)

private theorem fzrAux_conj_eq_one (a g : G) : g * a * g⁻¹ = 1 ↔ a = 1 := by
  constructor
  · intro h
    have h' := congrArg (fun x => g⁻¹ * x * g) h
    simpa [mul_assoc] using h'
  · rintro rfl
    simp

private theorem fzrAux_conj_pow_eq_one (a g : G) (n : ℕ) :
    (g * a * g⁻¹) ^ n = 1 ↔ a ^ n = 1 := by
  rw [conj_pow]
  constructor
  · intro h
    have h' := congrArg (fun x => g⁻¹ * x * g) h
    simpa [mul_assoc] using h'
  · intro h
    rw [h]
    simp

private theorem fzrAux_ordClass_conj (a g : G) :
    fzrOrdClass (g * a * g⁻¹) = fzrOrdClass a := by
  unfold fzrOrdClass
  rw [fzrAux_conj_eq_one, fzrAux_conj_pow_eq_one, fzrAux_conj_pow_eq_one,
    fzrAux_conj_pow_eq_one]

private theorem fzrAux_cent_iff {u x : ℕ} (hu : u < 512) (hx : x < 512) :
    x ∈ fzrCent (fzrPar D) u ↔ fzrMu D x ∈ invCent (fzrMu D u) := by
  rw [fzrCent, Finset.mem_filter, Finset.mem_range]
  rw [invCent, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨-, he⟩
    have h1 := fzrMu_mul D hx hu
    have h2 := fzrMu_mul D hu hx
    rw [he] at h1
    rw [← h1, ← h2]
  · intro hcomm
    refine ⟨hx, ?_⟩
    apply fzrMu_inj D ((fzrPar_mul D).lt x u hx hu) ((fzrPar_mul D).lt u x hu hx)
    rw [fzrMu_mul D hx hu, fzrMu_mul D hu hx]
    exact hcomm

open Classical in
private noncomputable def fzrAux_psi (g : G) (x : ℕ) : ℕ :=
  if hx : g⁻¹ * fzrMu D x * g ∈ T₂ then Classical.choose (fzrMu_surj D hx) else 0

private theorem fzrAux_psi_spec {g : G} {x : ℕ}
    (hx : g⁻¹ * fzrMu D x * g ∈ T₂) :
    fzrAux_psi D g x < 512 ∧ fzrMu D (fzrAux_psi D g x) = g⁻¹ * fzrMu D x * g := by
  unfold fzrAux_psi
  rw [dif_pos hx]
  exact Classical.choose_spec (fzrMu_surj D hx)

private theorem fzrAux_th_conj (t a g : G) :
    (∃ b : G, b * t * b⁻¹ = g⁻¹ * a * g) ↔ (∃ b : G, b * t * b⁻¹ = a) := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨g * b, ?_⟩
    calc
      (g * b) * t * (g * b)⁻¹ = g * (b * t * b⁻¹) * g⁻¹ := by group
      _ = g * (g⁻¹ * a * g) * g⁻¹ := by rw [hb]
      _ = a := by group
  · rintro ⟨b, hb⟩
    refine ⟨g⁻¹ * b, ?_⟩
    calc
      (g⁻¹ * b) * t * (g⁻¹ * b)⁻¹ = g⁻¹ * (b * t * b⁻¹) * g := by group
      _ = g⁻¹ * a * g := by rw [hb]

theorem fzr_cent_embed (h : Ctx t L S x₁ x₂ lam rho tau) (hT2 : IsFzT2 t x₁ x₂ S T₂) {u : ℕ}
    (hu : fzrTh D u) :
    ∃ (H₁ : Subgroup G) (ψ : ℕ → ℕ), H₁ ≤ S ∧ t ∈ H₁ ∧
      Set.BijOn ψ (↑(fzrCent (fzrPar D) u)) {n | n < 512 ∧ fzrMu D n ∈ H₁} ∧
      ∀ x ∈ fzrCent (fzrPar D) u,
        fzrKey (fzrPar D) (fzrTh D) (ψ x) = fzrKey (fzrPar D) (fzrTh D) x := by
  obtain ⟨hu_lt, g₀, hg₀⟩ := hu
  let u₀ : G := fzrMu D u
  have hu' : ∃ h' : G, h'⁻¹ * t * h' = u₀ := by
    refine ⟨g₀⁻¹, ?_⟩
    simpa [u₀] using hg₀
  obtain ⟨g, hgt, htrans⟩ :=
    fzr_transport (fzr_isSylowOf_S h.toCtx0) hT2.isPGroup hT2.S_le hu'
  set H₁ : Subgroup G := (T₂ ⊓ invCent u₀).map (MulAut.conj g⁻¹).toMonoidHom with hH₁
  set ψ : ℕ → ℕ := fzrAux_psi D g with hψ
  have hHmem : ∀ y : G, y ∈ H₁ ↔ ∃ c ∈ T₂ ⊓ invCent u₀, g⁻¹ * c * g = y := by
    intro y
    rw [hH₁, Subgroup.mem_map]
    constructor
    · rintro ⟨c, hc, hcy⟩
      exact ⟨c, hc, by simpa [MulAut.conj_apply] using hcy⟩
    · rintro ⟨c, hc, hcy⟩
      exact ⟨c, hc, by simpa [MulAut.conj_apply] using hcy⟩
  have hH₁S : H₁ ≤ S := by
    intro y hy
    obtain ⟨c, hc, hcy⟩ := (hHmem y).mp hy
    rw [← hcy]
    exact htrans c hc
  have htH₁ : t ∈ H₁ := by
    refine (hHmem t).mpr ⟨u₀, ⟨fzrMu_mem D u, ?_⟩, ?_⟩
    · simp [invCent, Subgroup.mem_centralizer_singleton_iff]
    · simpa [MulAut.conj_apply] using hgt
  have hψspec : ∀ x, g⁻¹ * fzrMu D x * g ∈ T₂ →
      ψ x < 512 ∧ fzrMu D (ψ x) = g⁻¹ * fzrMu D x * g := by
    intro x hx
    rw [hψ]
    exact fzrAux_psi_spec D hx
  have hcent_mem : ∀ {x : ℕ}, x ∈ fzrCent (fzrPar D) u →
      fzrMu D x ∈ T₂ ⊓ invCent u₀ := by
    intro x hx
    change x ∈ fzrCent (fzrPar D) u at hx
    have hxlt : x < 512 := Finset.mem_range.mp (Finset.mem_filter.mp hx).1
    exact ⟨fzrMu_mem D x, (fzrAux_cent_iff D hu_lt hxlt).mp hx⟩
  have hconjT : ∀ {x : ℕ}, x ∈ fzrCent (fzrPar D) u →
      g⁻¹ * fzrMu D x * g ∈ T₂ := by
    intro x hx
    apply hT2.S_le
    apply hH₁S
    exact (hHmem _).mpr ⟨fzrMu D x, hcent_mem hx, rfl⟩
  have hmaps : Set.MapsTo ψ ↑(fzrCent (fzrPar D) u)
      {n | n < 512 ∧ fzrMu D n ∈ H₁} := by
    intro x hx
    have hψx := hψspec x (hconjT hx)
    exact ⟨hψx.1, by rw [hψx.2]; exact (hHmem _).mpr ⟨fzrMu D x, hcent_mem hx, rfl⟩⟩
  have hinj : Set.InjOn ψ ↑(fzrCent (fzrPar D) u) := by
    intro x hx y hy hxy
    change x ∈ fzrCent (fzrPar D) u at hx
    change y ∈ fzrCent (fzrPar D) u at hy
    have hxlt : x < 512 := Finset.mem_range.mp (Finset.mem_filter.mp hx).1
    have hylt : y < 512 := Finset.mem_range.mp (Finset.mem_filter.mp hy).1
    have hxψ := hψspec x (hconjT hx)
    have hyψ := hψspec y (hconjT hy)
    have hconj : g⁻¹ * fzrMu D x * g = g⁻¹ * fzrMu D y * g := by
      rw [← hxψ.2, ← hyψ.2, hxy]
    have hmu : fzrMu D x = fzrMu D y := by
      have h' := congrArg (fun z => g * z * g⁻¹) hconj
      simpa [mul_assoc] using h'
    exact fzrMu_inj D hxlt hylt hmu
  have hsurj : Set.SurjOn ψ ↑(fzrCent (fzrPar D) u)
      {n | n < 512 ∧ fzrMu D n ∈ H₁} := by
    intro n hn
    have hnlt : n < 512 := hn.1
    obtain ⟨c, hc, hcn⟩ := (hHmem (fzrMu D n)).mp hn.2
    have hcn' : g⁻¹ * c * g = fzrMu D n := by
      simpa [MulAut.conj_apply] using hcn
    obtain ⟨x, hxlt, hxmu⟩ := fzrMu_surj D hc.1
    refine ⟨x, ?_, ?_⟩
    · change x ∈ fzrCent (fzrPar D) u
      exact (fzrAux_cent_iff D hu_lt hxlt).mpr (by rw [hxmu]; exact hc.2)
    · have hxT : g⁻¹ * fzrMu D x * g ∈ T₂ := by
        rw [hxmu, hcn']
        exact fzrMu_mem D n
      have hψx := hψspec x hxT
      apply fzrMu_inj D hψx.1 hnlt
      rw [hψx.2, hxmu, hcn']
  have hkey : ∀ x ∈ fzrCent (fzrPar D) u,
      fzrKey (fzrPar D) (fzrTh D) (ψ x) = fzrKey (fzrPar D) (fzrTh D) x := by
    intro x hx
    change x ∈ fzrCent (fzrPar D) u at hx
    have hxlt : x < 512 := Finset.mem_range.mp (Finset.mem_filter.mp hx).1
    have hψx := hψspec x (hconjT hx)
    have hkord : kord (fzrPar D).e (ψ x) = kord (fzrPar D).e x := by
      rw [fzrMu_kord D hψx.1, fzrMu_kord D hxlt, hψx.2]
      simpa using fzrAux_ordClass_conj (fzrMu D x) g⁻¹
    have hth : fzrTh D (ψ x) ↔ fzrTh D x := by
      simp only [fzrTh]
      simp [hψx.1, hxlt, hψx.2, fzrAux_th_conj t (fzrMu D x) g]
    rw [fzrKey, fzrKey, hkord]
    by_cases hthx : fzrTh D x
    · rw [if_pos (hth.mpr hthx), if_pos hthx]
    · rw [if_neg (fun hh => hthx (hth.mp hh)), if_neg hthx]
  exact ⟨H₁, ψ, hH₁S, htH₁, ⟨hmaps, hinj, hsurj⟩, hkey⟩

end CFSG.OddStandard.SmallF3.FritzII
