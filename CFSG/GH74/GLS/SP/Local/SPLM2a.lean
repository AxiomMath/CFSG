module

public import CFSG.GH74.GLS.SP.Local.SPLWt1
public import CFSG.GH74.GLS.SP.Local.SPLSet

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem conjBy_t_le_K₂ (D : SPLNot3 G) (hs : SPLSetup D.toSPLNot0) {X : Subgroup G} (hX : X ≤ D.K₁) :
    conjBy D.t X ≤ D.K₂ := by
  intro x hx
  rw [mem_conjBy_iff] at hx
  have h := t_conj_K₁ D hs _ (hX hx)
  have e : D.t * (D.t * x * D.t⁻¹) * D.t⁻¹ = x := by
    have : D.t * (D.t * x * D.t⁻¹) * D.t⁻¹ = (D.t * D.t) * x * (D.t * D.t)⁻¹ := by group
    rw [this, t_mul_t D hs]
    simp
  rwa [e] at h

theorem inf_conjBy_t_eq_bot (D : SPLNot3 G) (hs : SPLSetup D.toSPLNot0) {X : Subgroup G}
    (hX : X ≤ D.K₁) (hXe : IsEAb D.p X) : X ⊓ conjBy D.t X = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx1, hx2⟩
  have hxK : x ∈ D.K₁ ⊓ D.K₂ := ⟨hX hx1, conjBy_t_le_K₂ D hs hX hx2⟩
  rw [hs.comps.inf_eq] at hxK
  rcases eq_one_or_z hs hxK with h | h
  · rw [h]; exact Subgroup.one_mem _
  · exfalso
    have hz : D.z ∈ X := h ▸ hx1
    have h' := hXe.2 D.z hz
    have h2 : orderOf D.z ∣ D.p := orderOf_dvd_of_pow_eq_one h'
    rw [hs.syl.z_inv] at h2
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hs.prime).mp h2
    exact hs.p_ne_two this.symm

theorem spl3X_of_sl2 (D : SPLNot3 G) (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1)
    {X : Subgroup G} (hXK : X ≤ D.K₁) (hXc : Nat.card ↥X = D.q) (hXe : IsEAb D.p X)
    (hXn : ∀ g ∈ zpowers D.h₁, ∀ x ∈ X, g * x * g⁻¹ ∈ X) (hXne : X ≠ conjBy D.w₁ X)
    (hKX : D.K₁ = X ⊔ conjBy D.w₁ X)
    (htwo : ∀ W : Subgroup G, W ≤ D.K₁ → IsPGroup D.p ↥W → Nat.card ↥W = D.q →
      (∀ g ∈ zpowers D.h₁, ∀ x ∈ W, g * x * g⁻¹ ∈ W) → W = X ∨ W = conjBy D.w₁ X)
    (hX₁ : D.X₁ = X) (hX₁' : D.X₁' = conjBy D.w₁ X) (hY : D.Y₁ = ⁅D.X, zpowers D.t⁆) :
    SPL3X D := by
  have : Fact D.p.Prime := ⟨hs.prime⟩
  obtain ⟨k, -, hqk⟩ := hs.q_pow
  have hHX : Normalizes D.H X := by
    intro h hh x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute (H₁_H₂_comm D hs h1) hh
    have hbx : b * x = x * b := (hs.comps.comm x (hXK hx) b (H₂_le_K₂ D hs h1 hb)).symm
    have e : a * b * x * (a * b)⁻¹ = a * x * a⁻¹ := by
      calc a * b * x * (a * b)⁻¹ = a * (b * x) * b⁻¹ * a⁻¹ := by group
        _ = a * (x * b) * b⁻¹ * a⁻¹ := by rw [hbx]
        _ = a * x * a⁻¹ := by group
    rw [e]
    exact hXn a ha x hx
  have hw : D.w₁ ∈ normalizer (D.H : Set G) := w₁_mem_normalizer D hs h1
  have hHX' : Normalizes D.H (conjBy D.w₁ X) := hHX.map_conjBy hw
  have hw₁F : D.w₁ ∈ normalizer (D.F : Set G) := by
    refine normalizer_of_both (fun f hf => ?_) (fun f hf => ?_)
    · have e : D.w₁ * f * D.w₁⁻¹ = f := by rw [← F_cen_w₁ D h1 f hf]; group
      rw [e]; exact hf
    · have e : D.w₁⁻¹ * f * D.w₁ = f := by
        have hc := F_cen_w₁ D h1 f hf
        calc D.w₁⁻¹ * f * D.w₁ = D.w₁⁻¹ * (f * D.w₁) := by group
          _ = D.w₁⁻¹ * (D.w₁ * f) := by rw [hc]
          _ = f := by group
      rw [e]; exact hf
  have hFX : Normalizes D.F X := by
    intro f hf x hx
    let W : Subgroup G := X.map (MulAut.conj f).toMonoidHom
    have hmemW : ∀ y, y ∈ W ↔ ∃ x ∈ X, f * x * f⁻¹ = y := by
      intro y
      simp [W, Subgroup.mem_map, MulAut.conj_apply]
    have hWK : W ≤ D.K₁ := by
      intro y hy
      obtain ⟨x', hx', rfl⟩ := (hmemW y).mp hy
      exact F_normalizes_K₁ hs f hf x' (hXK hx')
    have hWcard : Nat.card ↥W = D.q := by
      rw [Subgroup.card_map_of_injective (MulAut.conj f).injective]; exact hXc
    have hWp : IsPGroup D.p ↥W := IsPGroup.of_card (n := k) (by rw [hWcard, hqk])
    have hWH : ∀ g ∈ zpowers D.h₁, ∀ y ∈ W, g * y * g⁻¹ ∈ W := by
      intro g hg y hy
      obtain ⟨x', hx', rfl⟩ := (hmemW y).mp hy
      have hgH : f⁻¹ * g * f ∈ D.H := by
        have := h1.F_norm_H f⁻¹ (D.F.inv_mem hf) g (H₁_le_H D hg)
        simpa using this
      refine (hmemW _).mpr ⟨(f⁻¹ * g * f) * x' * (f⁻¹ * g * f)⁻¹, hHX _ hgH x' hx', ?_⟩
      group
    rcases htwo W hWK hWp hWcard hWH with hW | hW
    · have : f * x * f⁻¹ ∈ W := (hmemW _).mpr ⟨x, hx, rfl⟩
      rwa [hW] at this
    · exfalso
      have hAB : ∀ x ∈ X, f * x * f⁻¹ ∈ conjBy D.w₁ X := fun x hx => by
        have : f * x * f⁻¹ ∈ W := (hmemW _).mpr ⟨x, hx, rfl⟩
        rwa [hW] at this
      have hc := F_cen_w₁ D h1 f hf
      have hconj : D.w₁ * f * D.w₁⁻¹ = f := by rw [← hc]; group
      have hconj' : D.w₁ * f⁻¹ * D.w₁⁻¹ = f⁻¹ := by
        have := congrArg (fun y => y⁻¹) hconj
        simpa [mul_assoc] using this
      have hBA : ∀ y ∈ conjBy D.w₁ X, f * y * f⁻¹ ∈ X := by
        intro y hy
        have hyK : y ∈ D.K₁ := by
          have : conjBy D.w₁ X ≤ D.K₁ := conjBy_le_of_mem h1.w₁_mem hXK
          exact this hy
        rw [mem_conjBy_iff] at hy
        have h2 := hAB _ hy
        rw [mem_conjBy_iff] at h2
        have hzy : D.z * y * D.z⁻¹ = y := by
          rw [← hs.comps.cz₁ hyK]
          group
        have e : D.w₁ * (f * (D.w₁ * y * D.w₁⁻¹) * f⁻¹) * D.w₁⁻¹ = f * y * f⁻¹ := by
          calc D.w₁ * (f * (D.w₁ * y * D.w₁⁻¹) * f⁻¹) * D.w₁⁻¹
              = (D.w₁ * f * D.w₁⁻¹) * ((D.w₁ * D.w₁) * y * (D.w₁ * D.w₁)⁻¹) *
                  (D.w₁ * f⁻¹ * D.w₁⁻¹) := by group
            _ = f * (D.z * y * D.z⁻¹) * f⁻¹ := by rw [hconj, hconj', h1.w₁_sq]
            _ = f * y * f⁻¹ := by rw [hzy]
        rwa [e] at h2
      have hodd := F_odd D.toSPLNot0 hf
      exact hXne (le_antisymm (le_of_swap_odd hodd hAB hBA) (le_of_swap_odd hodd hBA hAB))
  have hFX' : Normalizes D.F (conjBy D.w₁ X) := hFX.map_conjBy hw₁F
  have hcomm : ∀ a ∈ X, ∀ b ∈ conjBy D.t X, a * b = b * a := fun a ha b hb =>
    hs.comps.comm a (hXK ha) b (conjBy_t_le_K₂ D hs hXK hb)
  have hinter := inf_conjBy_t_eq_bot D hs hXK hXe
  obtain ⟨φ, hφ, hYe, hYi, hYc⟩ := Y1_spec (t_mul_t D hs) hXe hcomm hinter
  have hDX : D.X = X ⊔ conjBy D.t X := by rw [SPLNot3.X, SPLNot3.X₂, hX₁]
  refine
    { X₁_le := hX₁ ▸ hXK
      X₁'_le := hX₁' ▸ conjBy_le_of_mem h1.w₁_mem hXK
      X₁_card := hX₁ ▸ hXc
      X₁'_card := by rw [hX₁', card_conjBy]; exact hXc
      X₁_eab := hX₁ ▸ hXe
      X₁'_eab := hX₁' ▸ isEAb_conjBy hXe _
      X₁_ne := by rw [hX₁, hX₁']; exact hXne
      K₁_eq := by rw [hX₁, hX₁']; exact hKX
      X₁'_eq := by rw [hX₁, hX₁']
      H_X₁ := hX₁ ▸ hHX
      H_X₁' := hX₁' ▸ hHX'
      two := fun W hWK hWp hWc hWH => by
        rw [hX₁, hX₁']
        exact htwo W hWK hWp hWc (fun g hg x hx => hWH g (H₁_le_H D hg) x hx)
      F_X₁ := hX₁ ▸ hFX
      F_X₁' := hX₁' ▸ hFX'
      Y₁_eq := hY
      Y₁_le := by
        intro y hy
        rw [hY, hDX] at hy
        obtain ⟨u, hu⟩ := φ.surjective ⟨y, hy⟩
        have hy' : y = (u : G) * (D.t * (u : G)⁻¹ * D.t⁻¹) := by
          rw [← hφ u, hu]
        rw [hy', hDX]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left u.2)
          (Subgroup.mem_sup_right (mem_conjBy_conj (t_mul_t D hs) (X.inv_mem u.2)))
      Y₁_card := by rw [hY, hDX, hYc]; exact hXc
      Y₁_eab := by rw [hY, hDX]; exact hYe
      Y₁_inv := by rw [hY, hDX]; exact hYi }

theorem exists_X (D₂ : SPLNot2 G) (hs : SPLSetup D₂.toSPLNot0) (h1 : SPL2Set D₂.toSPLNot1) :
    ∃ X₁ X₁' Y₁ : Subgroup G, ∀ a : G, SPL3X (⟨D₂, X₁, X₁', Y₁, a⟩ : SPLNot3 G) := by
  obtain ⟨X, hXK, hXc, hXe, hXn, hXne, hKX, htwo, -, -⟩ :=
    sl2_rootGroups D₂.K₁ D₂.q D₂.p hs.prime hs.comps.sl₁ hs.odd_q hs.q_ge hs.q_pow D₂.z
      hs.comps.cen₁ D₂.h₁ D₂.w₁ h1.h₁_mem h1.w₁_mem h1.h₁_ord h1.w₁_sq h1.w₁_inv h1.nbhd
  refine ⟨X, conjBy D₂.w₁ X, ⁅X ⊔ conjBy D₂.t X, zpowers D₂.t⁆, fun a => ?_⟩
  exact spl3X_of_sl2 ⟨D₂, X, conjBy D₂.w₁ X, ⁅X ⊔ conjBy D₂.t X, zpowers D₂.t⁆, a⟩ hs h1 hXK hXc hXe
    hXn hXne hKX htwo rfl rfl rfl

end CFSG.GH74.GLS.SP.Local
