module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Diag.Setup
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.CentralCover

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open Subgroup CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78
open scoped commutatorElement

variable {H : Type} [Group H] {T W W' M K : Subgroup H} {s : H}

@[expose] def diagA (M W' : Subgroup H) : Subgroup H :=
  conjClosure M W' ⊓ centralizer (W' : Set H)

theorem mem_diagP₂_conj {M W' : Subgroup H} {s a : H} (ha : a ∈ conjClosure M W') :
    s * a * s⁻¹ ∈ diagP₂ M W' s :=
  ⟨a, ha, by simp [MulAut.conj_apply]⟩

theorem DiagData.mem_P₁_conj (h : DiagData T W W' M K s) {b : H} (hb : b ∈ diagP₂ M W' s) :
    s * b * s⁻¹ ∈ conjClosure M W' := by
  have : s * b * s⁻¹ ∈ (diagP₂ M W' s).map (MulAut.conj s).toMonoidHom :=
    ⟨b, hb, by simp [MulAut.conj_apply]⟩
  rwa [h.map_conj_P₂_s] at this

theorem DiagData.mem_P₁_of_conj (h : DiagData T W W' M K s) {a u : H} (ha : a ∈ conjClosure M W')
    (hu : u ∈ W') : u * a * u⁻¹ ∈ conjClosure M W' := by
  have : u * a * u⁻¹ ∈ (conjClosure M W').map (MulAut.conj u).toMonoidHom :=
    ⟨a, ha, by simp [MulAut.conj_apply]⟩
  rwa [h.map_conj_P₁ hu] at this

theorem DiagData.mem_P₂_of_conj (h : DiagData T W W' M K s) {b u : H}
    (hb : b ∈ diagP₂ M W' s) (hu : u ∈ W') : u * b * u⁻¹ ∈ diagP₂ M W' s := by
  have : u * b * u⁻¹ ∈ (diagP₂ M W' s).map (MulAut.conj u).toMonoidHom :=
    ⟨b, hb, by simp [MulAut.conj_apply]⟩
  rwa [h.map_conj_P₂ hu] at this

variable [Finite H]

@[expose] def diagΔ (h : DiagData T W W' M K s) : ↥(diagA M W') →* H :=
  MonoidHom.mk' (fun a => (a : H) * (s * (a : H) * s⁻¹)) (by
    intro a b
    have hc : (b : H) * (s * (a : H) * s⁻¹) = (s * (a : H) * s⁻¹) * (b : H) :=
      h.commute b b.2.1 _ (mem_diagP₂_conj a.2.1)
    show ((a : H) * b) * (s * ((a : H) * b) * s⁻¹) =
      ((a : H) * (s * a * s⁻¹)) * ((b : H) * (s * b * s⁻¹))
    calc ((a : H) * b) * (s * ((a : H) * b) * s⁻¹)
        = (a : H) * (b * (s * a * s⁻¹)) * (s * b * s⁻¹) := by group
      _ = (a : H) * ((s * a * s⁻¹) * b) * (s * b * s⁻¹) := by rw [hc]
      _ = _ := by group)

theorem diagΔ_apply (h : DiagData T W W' M K s) (a : ↥(diagA M W')) :
    diagΔ h a = (a : H) * (s * (a : H) * s⁻¹) := rfl

theorem DiagData.commute_W' (h : DiagData T W W' M K s) (a : ↥(diagA M W')) {u : H} (hu : u ∈ W') :
    u * diagΔ h a = diagΔ h a * u := by
  have hv : s⁻¹ * u * s ∈ W' := by
    have := h.conj_mem s⁻¹ (W.inv_mem h.s_mem) u hu
    simpa using this
  have hva : (s⁻¹ * u * s) * (a : H) = (a : H) * (s⁻¹ * u * s) := mem_centralizer_iff.1 a.2.2 _ hv
  have hua : u * (a : H) = (a : H) * u := mem_centralizer_iff.1 a.2.2 _ hu
  have hc : u * (s * (a : H) * s⁻¹) = (s * (a : H) * s⁻¹) * u := by
    calc u * (s * (a : H) * s⁻¹) = s * ((s⁻¹ * u * s) * (a : H)) * s⁻¹ := by group
      _ = s * ((a : H) * (s⁻¹ * u * s)) * s⁻¹ := by rw [hva]
      _ = (s * (a : H) * s⁻¹) * u := by group
  rw [diagΔ_apply]
  calc u * ((a : H) * (s * (a : H) * s⁻¹)) = (u * (a : H)) * (s * (a : H) * s⁻¹) := by group
    _ = ((a : H) * u) * (s * (a : H) * s⁻¹) := by rw [hua]
    _ = (a : H) * (u * (s * (a : H) * s⁻¹)) := by group
    _ = (a : H) * ((s * (a : H) * s⁻¹) * u) := by rw [hc]
    _ = ((a : H) * (s * (a : H) * s⁻¹)) * u := by group

theorem DiagData.commute_s (h : DiagData T W W' M K s) (a : ↥(diagA M W')) :
    s * diagΔ h a = diagΔ h a * s := by
  have hsc : s * (s * (a : H) * s⁻¹) * s⁻¹ = (a : H) := by
    have e : (s * s) * (a : H) = (a : H) * (s * s) := by
      have := mem_centralizer_iff.1 a.2.2 (s ^ 2) h.sq_mem
      simpa [pow_two] using this
    calc s * (s * (a : H) * s⁻¹) * s⁻¹ = ((s * s) * (a : H)) * (s * s)⁻¹ := by group
      _ = ((a : H) * (s * s)) * (s * s)⁻¹ := by rw [e]
      _ = (a : H) := by group
  have hca : (s * (a : H) * s⁻¹) * (a : H) = (a : H) * (s * (a : H) * s⁻¹) :=
    (h.commute a a.2.1 _ (mem_diagP₂_conj a.2.1)).symm
  rw [diagΔ_apply]
  calc s * ((a : H) * (s * (a : H) * s⁻¹))
      = (s * (a : H) * s⁻¹) * (s * (s * (a : H) * s⁻¹) * s⁻¹) * s := by group
    _ = (s * (a : H) * s⁻¹) * (a : H) * s := by rw [hsc]
    _ = (a : H) * (s * (a : H) * s⁻¹) * s := by rw [hca]

theorem DiagData.commute_W (h : DiagData T W W' M K s) (a : ↥(diagA M W')) {g : H} (hg : g ∈ W) :
    g * diagΔ h a = diagΔ h a * g := by
  rcases h.cover g hg with h1 | h1
  · exact h.commute_W' a h1
  · have hg' : g = s * (s⁻¹ * g) := by group
    have h2 := h.commute_W' a h1
    have h3 := h.commute_s a
    calc g * diagΔ h a = s * ((s⁻¹ * g) * diagΔ h a) := by rw [hg']; group
      _ = s * (diagΔ h a * (s⁻¹ * g)) := by rw [h2]
      _ = (s * diagΔ h a) * (s⁻¹ * g) := by group
      _ = (diagΔ h a * s) * (s⁻¹ * g) := by rw [h3]
      _ = diagΔ h a * g := by group

theorem DiagData.diagΔ_mem (h : DiagData T W W' M K s) (a : ↥(diagA M W')) :
    diagΔ h a ∈ centralizer ((W ⊔ T : Subgroup H) : Set H) := by
  refine mem_centralizer_sup.2 ⟨mem_centralizer_iff.2 fun g hg => ?_, ?_⟩
  · exact h.commute_W a hg
  · exact (centralizer (T : Set H)).mul_mem (h.P₁_le_centralizer a.2.1)
      (h.P₂_le_centralizer (mem_diagP₂_conj a.2.1))

theorem DiagData.ker_le_center (h : DiagData T W W' M K s) :
    (diagΔ h).ker ≤ center ↥(diagA M W') := by
  intro a ha
  have h1 : (a : H) * (s * (a : H) * s⁻¹) = 1 := ha
  have h2 : (a : H) ∈ diagP₂ M W' s := by
    have : (a : H) = (s * (a : H) * s⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact (diagP₂ M W' s).inv_mem (mem_diagP₂_conj a.2.1)
  rw [Subgroup.mem_center_iff]
  intro b
  exact Subtype.ext (h.commute b b.2.1 a h2)

omit [Finite H] in
theorem DiagData.mem_centralizer_W (h : DiagData T W W' M K s) {x : H} (hx : x ∈ K) :
    ∀ g ∈ W, g * x = x * g := fun g hg =>
  mem_centralizer_iff.1 (mem_centralizer_sup.1 (h.isComp_K.1 hx)).1 g hg

theorem DiagData.decomp (h : DiagData T W W' M K s) {a b : H} (ha : a ∈ conjClosure M W')
    (hb : b ∈ diagP₂ M W' s) (hx : a * b ∈ K) :
    (∀ u ∈ W', a⁻¹ * (u * a * u⁻¹) ∈ conjClosure M W' ⊓ diagP₂ M W' s) ∧
      a⁻¹ * (s * b * s⁻¹) ∈ conjClosure M W' ⊓ diagP₂ M W' s ∧
      b = (a⁻¹ * (s * b * s⁻¹)) * (s * a * s⁻¹) := by
  refine ⟨?_, ?_⟩
  · intro u hu
    have hxu : u * (a * b) = (a * b) * u := h.mem_centralizer_W hx u (h.W'_le hu)
    have e : a⁻¹ * (u * a * u⁻¹) = b * (u * b * u⁻¹)⁻¹ := by
      have hu' : u * (a * b) * u⁻¹ = a * b := by rw [hxu]; group
      calc a⁻¹ * (u * a * u⁻¹) = a⁻¹ * (u * (a * b) * u⁻¹) * (u * b * u⁻¹)⁻¹ := by group
        _ = a⁻¹ * (a * b) * (u * b * u⁻¹)⁻¹ := by rw [hu']
        _ = b * (u * b * u⁻¹)⁻¹ := by group
    refine ⟨(conjClosure M W').mul_mem ((conjClosure M W').inv_mem ha) (h.mem_P₁_of_conj ha hu), ?_⟩
    rw [e]
    exact (diagP₂ M W' s).mul_mem hb ((diagP₂ M W' s).inv_mem (h.mem_P₂_of_conj hb hu))
  · have hc : s * a * s⁻¹ ∈ diagP₂ M W' s := mem_diagP₂_conj ha
    have hd : s * b * s⁻¹ ∈ conjClosure M W' := h.mem_P₁_conj hb
    have hxs : s * (a * b) = (a * b) * s := h.mem_centralizer_W hx s h.s_mem
    have hs' : s * (a * b) * s⁻¹ = a * b := by rw [hxs]; group
    have hdc : (s * b * s⁻¹) * (s * a * s⁻¹) = (s * a * s⁻¹) * (s * b * s⁻¹) :=
      h.commute _ hd _ hc
    have hcd : (s * a * s⁻¹) * (s * b * s⁻¹) = a * b := by
      rw [← hs']
      group
    have hζ : a⁻¹ * (s * b * s⁻¹) = b * (s * a * s⁻¹)⁻¹ := by
      calc a⁻¹ * (s * b * s⁻¹) = a⁻¹ * ((s * b * s⁻¹) * (s * a * s⁻¹)) * (s * a * s⁻¹)⁻¹ := by
            group
        _ = a⁻¹ * ((s * a * s⁻¹) * (s * b * s⁻¹)) * (s * a * s⁻¹)⁻¹ := by rw [hdc]
        _ = a⁻¹ * (a * b) * (s * a * s⁻¹)⁻¹ := by rw [hcd]
        _ = b * (s * a * s⁻¹)⁻¹ := by group
    refine ⟨⟨(conjClosure M W').mul_mem ((conjClosure M W').inv_mem ha) hd, ?_⟩, ?_⟩
    · rw [hζ]
      exact (diagP₂ M W' s).mul_mem hb ((diagP₂ M W' s).inv_mem hc)
    · rw [hζ]
      group

theorem DiagData.K_le_range (h : DiagData T W W' M K s) : K ≤ (diagΔ h).range := by
  have hKperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.1 h.isComp_K.isQuasisimple.1
  calc K = ⁅K, K⁆ := hKperf.symm
    _ ≤ (diagΔ h).range := by
      refine commutator_le.2 fun x hx y hy => ?_
      obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_mul (h.K_le_sup hx)
      obtain ⟨a', ha', b', hb', rfl⟩ := h.exists_mul (h.K_le_sup hy)
      obtain ⟨hu, hs, hbe⟩ := h.decomp ha hb hx
      obtain ⟨hu', hs', hbe'⟩ := h.decomp ha' hb' hy
      have hP₁ : ∀ z ∈ conjClosure M W' ⊓ diagP₂ M W' s, ∀ g ∈ conjClosure M W' ⊔ diagP₂ M W' s,
          z * g = g * z := fun z hz g hg => h.inf_central hz hg
      have hle₁ : ∀ g ∈ conjClosure M W', g ∈ conjClosure M W' ⊔ diagP₂ M W' s := fun g hg =>
        (le_sup_left : conjClosure M W' ≤ _) hg
      have hle₂ : ∀ g ∈ diagP₂ M W' s, g ∈ conjClosure M W' ⊔ diagP₂ M W' s := fun g hg =>
        (le_sup_right : diagP₂ M W' s ≤ _) hg
      have hcom : ⁅a, a'⁆ ∈ diagA M W' := by
        refine ⟨?_, ?_⟩
        · simp only [commutatorElement_def]
          exact (conjClosure M W').mul_mem ((conjClosure M W').mul_mem
            ((conjClosure M W').mul_mem ha ha') ((conjClosure M W').inv_mem ha))
            ((conjClosure M W').inv_mem ha')
        · refine mem_centralizer_iff.2 fun u hu₀ => ?_
          have e1 : u * a * u⁻¹ = a * (a⁻¹ * (u * a * u⁻¹)) := by group
          have e2 : u * a' * u⁻¹ = a' * (a'⁻¹ * (u * a' * u⁻¹)) := by group
          have hz1 := hu u hu₀
          have hz2 := hu' u hu₀
          have h3 : u * ⁅a, a'⁆ * u⁻¹ = ⁅a, a'⁆ := by
            calc u * ⁅a, a'⁆ * u⁻¹ = ⁅u * a * u⁻¹, u * a' * u⁻¹⁆ := by
                  simp only [commutatorElement_def]; group
              _ = ⁅a * (a⁻¹ * (u * a * u⁻¹)), a' * (a'⁻¹ * (u * a' * u⁻¹))⁆ := by
                  rw [← e1, ← e2]
              _ = ⁅a, a' * (a'⁻¹ * (u * a' * u⁻¹))⁆ := by
                  refine commutatorElement_mul_of_commute (hP₁ _ hz1 _ (hle₁ _
                    ((conjClosure M W').mul_mem ha' hz2.1)))
              _ = ⁅a, a'⁆ := by
                  refine commutatorElement_of_commute_mul (h.commute a ha _ hz2.2)
          calc u * ⁅a, a'⁆ = (u * ⁅a, a'⁆ * u⁻¹) * u := by group
            _ = ⁅a, a'⁆ * u := by rw [h3]
      refine ⟨⟨⁅a, a'⁆, hcom⟩, ?_⟩
      rw [diagΔ_apply]
      show ⁅a, a'⁆ * (s * ⁅a, a'⁆ * s⁻¹) = ⁅a * b, a' * b'⁆
      have hc : s * a * s⁻¹ ∈ diagP₂ M W' s := mem_diagP₂_conj ha
      have hc' : s * a' * s⁻¹ ∈ diagP₂ M W' s := mem_diagP₂_conj ha'
      have hb2 : b = (s * a * s⁻¹) * (a⁻¹ * (s * b * s⁻¹)) := by
        rw [(h.commute _ hs.1 _ hc).symm, ← hbe]
      have hb2' : b' = (s * a' * s⁻¹) * (a'⁻¹ * (s * b' * s⁻¹)) := by
        rw [(h.commute _ hs'.1 _ hc').symm, ← hbe']
      have hbb : ⁅b, b'⁆ = ⁅s * a * s⁻¹, s * a' * s⁻¹⁆ := by
        rw [hb2, hb2']
        rw [commutatorElement_mul_of_commute (hP₁ _ hs _ (hle₂ _
          ((diagP₂ M W' s).mul_mem hc' hs'.2))),
          commutatorElement_of_commute_mul (h.commute _ hs'.1 _ hc).symm]
      rw [commutatorElement_mul_mul h.commute ha ha' hb hb', hbb]
      simp only [commutatorElement_def]
      group

end CFSG.EvenSporadicStandard.Induction.Junction
