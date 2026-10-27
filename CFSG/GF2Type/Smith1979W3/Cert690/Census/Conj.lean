module

public import CFSG.GF2Type.Smith1979W3.Cert690.Statements
public import CFSG.RankThree.OrthogonalInvolutions.Conjugacy

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.GF2Type.Smith1979W3.Cert690

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.O62

variable {G : Type*} [Group G]

@[expose] def conjSub (H : Subgroup G) (g : G) : Subgroup G :=
  H.map (MulAut.conj g).toMonoidHom

theorem mem_conjSub {H : Subgroup G} {g x : G} :
    x ∈ conjSub H g ↔ g⁻¹ * x * g ∈ H := by
  rw [conjSub, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hxy⟩
    simp only [MulEquiv.coe_toMonoidHom] at hxy
    rw [MulAut.conj_apply] at hxy
    rw [← hxy, show g⁻¹ * (g * y * g⁻¹) * g = y by group]
    exact hy
  · intro hx
    refine ⟨g⁻¹ * x * g, hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem conjSub_conjSub_inv (H : Subgroup G) (g : G) :
    conjSub (conjSub H g) g⁻¹ = H := by
  ext x
  rw [mem_conjSub, mem_conjSub]
  simp only [inv_inv]
  rw [show g⁻¹ * (g * x * g⁻¹) * g = x by group]

theorem map_centralizer_mulEquiv {G' : Type*} [Group G'] (e : G ≃* G') (S : Set G) :
    Subgroup.centralizer (e '' S) = (Subgroup.centralizer S).map e.toMonoidHom := by
  ext x
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_map]
  constructor
  · intro hx
    refine ⟨e.symm x, ?_, by simp⟩
    intro s hs
    have h := hx (e s) (Set.mem_image_of_mem e hs)
    apply e.injective
    change e (s * e.symm x) = e (e.symm x * s)
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact h
  · rintro ⟨y, hy, rfl⟩ z hz
    obtain ⟨s, hs, rfl⟩ := hz
    change e s * e y = e y * e s
    rw [← map_mul, ← map_mul]
    exact congrArg e ((Subgroup.mem_centralizer_iff.mp hy) s hs)

theorem map_normalizer_mulEquiv (H : Subgroup G) (e : G ≃* G) :
    Subgroup.normalizer ((H.map e.toMonoidHom : Subgroup G) : Set G) =
      (Subgroup.normalizer (H : Set G)).map e.toMonoidHom :=
  (Subgroup.map_equiv_normalizer_eq H e).symm

theorem mem_normalizer_conjSub_iff {L : Subgroup G} {g h : G} :
    h ∈ Subgroup.normalizer ((conjSub L g : Subgroup G) : Set G) ↔
      g⁻¹ * h * g ∈ Subgroup.normalizer (L : Set G) := by
  have hmap := map_normalizer_mulEquiv L (MulAut.conj g)
  rw [conjSub, hmap]
  rw [Subgroup.mem_map_equiv]
  have hsymm : (MulAut.conj g).symm h = g⁻¹ * h * g := by
    rw [MulEquiv.symm_apply_eq]
    simp only [MulAut.conj_apply]
    group
  rw [hsymm]

theorem centralizer_conjSub (L : Subgroup G) (g : G) :
    Subgroup.centralizer ((conjSub L g : Subgroup G) : Set G) =
      conjSub (Subgroup.centralizer (L : Set G)) g := by
  rw [conjSub]
  exact map_centralizer_mulEquiv (MulAut.conj g) (L : Set G)

theorem conjSub_le_O {minus : Bool} {H : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)}
    {g : V₀ ≃ₗ[ZMod 2] V₀} (hH : H ≤ O₀ minus) (hg : g ∈ O₀ minus) :
    conjSub H g ≤ O₀ minus := by
  rintro _ ⟨h, hh, rfl⟩
  change g * h * g⁻¹ ∈ O₀ minus
  exact mul_mem (mul_mem hg (hH hh)) (inv_mem hg)

@[expose] def NoNormalTwo (H : Subgroup G) : Prop :=
  ∀ N : Subgroup G, N ≤ H →
    (∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) → IsPGroup 2 N → N = ⊥

theorem noNormalTwo_conjSub {H : Subgroup G} {g : G} (h : NoNormalTwo H) :
    NoNormalTwo (conjSub H g) := by
  intro N hN hnorm hN2
  let N' : Subgroup G := N.map (MulAut.conj g⁻¹).toMonoidHom
  have hN' : N' ≤ H := by
    calc N' ≤ (conjSub H g).map (MulAut.conj g⁻¹).toMonoidHom := Subgroup.map_mono hN
      _ = H := conjSub_conjSub_inv H g
  have hnorm' : ∀ h' ∈ H, ∀ n ∈ N', h' * n * h'⁻¹ ∈ N' := by
    intro h' hh' n hn
    obtain ⟨m, hm, rfl⟩ := hn
    refine Subgroup.mem_map.mpr ⟨g * h' * g⁻¹ * m * (g * h' * g⁻¹)⁻¹, ?_, ?_⟩
    · exact hnorm _ (Subgroup.mem_map.mpr ⟨h', hh', by simp [MulAut.conj_apply]⟩) m hm
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have hP : IsPGroup 2 N' := IsPGroup.map hN2 (MulAut.conj g⁻¹).toMonoidHom
  have hbot : N' = ⊥ := h N' hN' hnorm' hP
  apply le_antisymm _ bot_le
  intro x hx
  have hy : g⁻¹ * x * g ∈ N' :=
    Subgroup.mem_map.mpr ⟨x, hx, by simp [MulAut.conj_apply]⟩
  rw [hbot, Subgroup.mem_bot] at hy
  rw [Subgroup.mem_bot]
  calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    _ = 1 := by rw [hy]; group

@[expose] def IrreducibleSub (H : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)) : Prop :=
  ∀ W : Submodule (ZMod 2) V₀, (∀ h ∈ H, ∀ w ∈ W, h w ∈ W) → W = ⊥ ∨ W = ⊤

theorem irreducibleSub_conj {H : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)}
    {g : V₀ ≃ₗ[ZMod 2] V₀} (h : IrreducibleSub H) :
    IrreducibleSub (conjSub H g) := by
  intro W hW
  let W' : Submodule (ZMod 2) V₀ := W.map (g.symm : V₀ →ₗ[ZMod 2] V₀)
  have hWin : ∀ h' ∈ H, ∀ w ∈ W', h' w ∈ W' := by
    intro h' hh' w hw
    obtain ⟨z, hz, rfl⟩ := hw
    have hmem : g * h' * g⁻¹ ∈ conjSub H g :=
      Subgroup.mem_map.mpr ⟨h', hh', by simp [MulAut.conj_apply]⟩
    refine Submodule.mem_map.mpr ⟨(g * h' * g⁻¹) z, hW _ hmem z hz, ?_⟩
    simp only [LinearEquiv.coe_coe, LinearEquiv.coe_inv, LinearEquiv.mul_apply]
    simp
  rcases h W' hWin with hbot | htop
  · left
    have hW' : W = W'.map (g : V₀ →ₗ[ZMod 2] V₀) := by
      rw [← Submodule.map_comp]
      rw [show ((g : V₀ →ₗ[ZMod 2] V₀).comp (g.symm : V₀ →ₗ[ZMod 2] V₀)) = LinearMap.id by
        ext x; simp]
      rw [Submodule.map_id]
    rw [hW', hbot, Submodule.map_bot]
  · right
    have hW' : W = W'.map (g : V₀ →ₗ[ZMod 2] V₀) := by
      rw [← Submodule.map_comp]
      rw [show ((g : V₀ →ₗ[ZMod 2] V₀).comp (g.symm : V₀ →ₗ[ZMod 2] V₀)) = LinearMap.id by
        ext x; simp]
      rw [Submodule.map_id]
    rw [hW', htop, Submodule.map_top, LinearMap.range_eq_top.mpr g.surjective]

theorem censusCond_conj {minus : Bool} {H L : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)} {b : V₀}
    {g : V₀ ≃ₗ[ZMod 2] V₀} (h : CensusCond minus H L b) (hg : g ∈ O₀ minus) :
    CensusCond minus (conjSub H g) (conjSub L g) (g b) := by
  unfold CensusCond at h ⊢
  obtain ⟨hLH, hfix, hinv, hcard, hnorm, hpgr⟩ := h
  refine ⟨Subgroup.map_mono hLH, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    change (g * y * g⁻¹) (g b) = g b
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, LinearEquiv.mul_apply]
    simp [hfix y hy]
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    change (g * y * g⁻¹) * (g * y * g⁻¹) = 1
    rw [show g * y * g⁻¹ * (g * y * g⁻¹) = g * (y * y) * g⁻¹ by group]
    rw [hinv y hy]
    group
  · have hcard' : Nat.card ↥(conjSub L g) = Nat.card ↥L := by
      rw [conjSub]
      exact Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
        (MulAut.conj g).injective
    rw [hcard']
    exact hcard
  · intro h' hh'
    obtain ⟨h, hh, rfl⟩ := hh'
    change g * h * g⁻¹ ∈ Subgroup.normalizer
        ((conjSub L g : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)) :
          Set (V₀ ≃ₗ[ZMod 2] V₀)) ↔
      (g * h * g⁻¹) (g b) = g b
    have h1 := mem_normalizer_conjSub_iff (L := L) (g := g) (h := g * h * g⁻¹)
    have h2 : g⁻¹ * (g * h * g⁻¹) * g = h := by group
    rw [h1, h2, hnorm h hh]
    change h b = b ↔ (g * h * g⁻¹) (g b) = g b
    have heq : (g * h * g⁻¹) (g b) = g (h b) := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, LinearEquiv.mul_apply]
      rw [show g⁻¹ (g b) = b by simp]
    rw [heq]
    exact ⟨fun hb => congrArg g hb, fun hb => g.injective hb⟩
  · have hmap : (H ⊓ Subgroup.centralizer (L : Set (V₀ ≃ₗ[ZMod 2] V₀))).map
          (MulAut.conj g).toMonoidHom =
        conjSub H g ⊓ Subgroup.centralizer
          ((conjSub L g : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)) : Set (V₀ ≃ₗ[ZMod 2] V₀)) := by
      rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective, centralizer_conjSub]
      rfl
    rw [← hmap]
    exact IsPGroup.map hpgr (MulAut.conj g).toMonoidHom

theorem isTypeA_conj {minus : Bool} {t g : V₀ ≃ₗ[ZMod 2] V₀} (h : IsTypeA (qModel minus) t 2)
    (hg : g ∈ O₀ minus) : IsTypeA (qModel minus) (g * t * g⁻¹) 2 := by
  unfold IsTypeA at h ⊢
  obtain ⟨hiso, htne, ht2, hdim, hvan⟩ := h
  have hgm : ∀ v, qModel minus (g v) = qModel minus v :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg
  have hgi : ∀ v, qModel minus (g⁻¹ v) = qModel minus v :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (inv_mem hg)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    rw [hgm, hiso, hgi]
  · intro h1
    apply htne
    have := congrArg (fun e => g⁻¹ * e * g) h1
    simpa [mul_assoc] using this
  · calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  · rw [CFSG.RankThree.OrthogonalInvolutions.commSpace_conj, LinearEquiv.finrank_map_eq]
    exact hdim
  · intro x hx
    rw [CFSG.RankThree.OrthogonalInvolutions.commSpace_conj] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    change qModel minus (g y) = 0
    rw [hgm]
    exact hvan y hy

theorem conjVec_ne_zero {b : V₀} {g : V₀ ≃ₗ[ZMod 2] V₀} (hb : b ≠ 0) : g b ≠ 0 := by
  intro h
  exact hb (by simpa using congrArg g.symm h)

theorem conjVec_qModel {minus : Bool} {b : V₀} {g : V₀ ≃ₗ[ZMod 2] V₀}
    (hg : g ∈ O₀ minus) : qModel minus (g b) = qModel minus b :=
  TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg b

theorem conj_mem_omega₀ {minus : Bool} {g x : V₀ ≃ₗ[ZMod 2] V₀}
    (hg : g ∈ O₀ minus) (hx : x ∈ Ω₀ minus) : g * x * g⁻¹ ∈ Ω₀ minus := by
  rw [Ω₀, CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup] at hx ⊢
  refine ⟨mul_mem (mul_mem hg hx.1) (inv_mem hg), ?_⟩
  rw [CFSG.RankThree.OrthogonalInvolutions.commSpace_conj, LinearEquiv.finrank_map_eq]
  exact hx.2

theorem map_conj_omega_eq {minus : Bool} {g : V₀ ≃ₗ[ZMod 2] V₀} (hg : g ∈ O₀ minus) :
    (Ω₀ minus).map (MulAut.conj g).toMonoidHom = Ω₀ minus := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    change g * x * g⁻¹ ∈ Ω₀ minus
    exact conj_mem_omega₀ hg hx
  · intro x hx
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, ?_, ?_⟩
    · have hg' : g⁻¹ ∈ O₀ minus := inv_mem hg
      have := conj_mem_omega₀ (minus := minus) hg' hx
      simpa using this
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

theorem map_conj_O_eq {minus : Bool} {g : V₀ ≃ₗ[ZMod 2] V₀} (hg : g ∈ O₀ minus) :
    (O₀ minus).map (MulAut.conj g).toMonoidHom = O₀ minus := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    change g * x * g⁻¹ ∈ O₀ minus
    exact mul_mem (mul_mem hg hx) (inv_mem hg)
  · intro x hx
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, ?_, ?_⟩
    · exact mul_mem (mul_mem (inv_mem hg) hx) hg
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

theorem conjSub_eq_omega_iff {minus : Bool} {H : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)}
    {g : V₀ ≃ₗ[ZMod 2] V₀} (hg : g ∈ O₀ minus) :
    conjSub H g = Ω₀ minus ↔ H = Ω₀ minus := by
  constructor
  · intro h
    calc H = conjSub (conjSub H g) g⁻¹ := (conjSub_conjSub_inv H g).symm
      _ = conjSub (Ω₀ minus) g⁻¹ := by rw [h]
      _ = Ω₀ minus := by
        rw [conjSub]
        exact map_conj_omega_eq (inv_mem hg)
  · intro h
    rw [h, conjSub]
    exact map_conj_omega_eq hg

theorem conjSub_eq_O_iff {minus : Bool} {H : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)}
    {g : V₀ ≃ₗ[ZMod 2] V₀} (hg : g ∈ O₀ minus) :
    conjSub H g = O₀ minus ↔ H = O₀ minus := by
  constructor
  · intro h
    calc H = conjSub (conjSub H g) g⁻¹ := (conjSub_conjSub_inv H g).symm
      _ = conjSub (O₀ minus) g⁻¹ := by rw [h]
      _ = O₀ minus := by
        rw [conjSub]
        exact map_conj_O_eq (inv_mem hg)
  · intro h
    rw [h, conjSub]
    exact map_conj_O_eq hg

theorem exists_conj_KPGL_iff {minus : Bool} {H : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)}
    {g : V₀ ≃ₗ[ZMod 2] V₀} (hg : g ∈ O₀ minus) :
    (∃ k ∈ O₀ minus, ∀ x, x ∈ conjSub H g ↔ k⁻¹ * x * k ∈ KPGL) →
      ∃ k ∈ O₀ minus, ∀ x, x ∈ H ↔ k⁻¹ * x * k ∈ KPGL := by
  rintro ⟨k, hk, hkH⟩
  refine ⟨g⁻¹ * k, mul_mem (inv_mem hg) hk, fun x => ?_⟩
  have hx : x ∈ H ↔ g * x * g⁻¹ ∈ conjSub H g := by
    rw [mem_conjSub]
    constructor
    · intro h
      rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group]
    · intro h
      rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at h
  rw [hx, hkH (g * x * g⁻¹)]
  rw [show k⁻¹ * (g * x * g⁻¹) * k = (g⁻¹ * k)⁻¹ * x * (g⁻¹ * k) by group]

@[expose] def CensusPlusConcl : Subgroup (V₀ ≃ₗ[ZMod 2] V₀) → Prop :=
  fun H => H = Ω₀ false ∨ H = O₀ false ∨
    ∃ g ∈ O₀ false, ∀ x, x ∈ H ↔ g⁻¹ * x * g ∈ KPGL

@[expose] def CensusMinusConcl : Subgroup (V₀ ≃ₗ[ZMod 2] V₀) → Prop :=
  fun H => H = Ω₀ true ∨ H = O₀ true

theorem census_reduction {minus : Bool} (b₀ : V₀)
    (Concl : Subgroup (V₀ ≃ₗ[ZMod 2] V₀) → Prop)
    (hconj : ∀ b : V₀, b ≠ 0 → qModel minus b = 0 → ∃ g ∈ O₀ minus, g b = b₀)
    (hback : ∀ H g, g ∈ O₀ minus → Concl (conjSub H g) → Concl H)
    (hmain : ∀ H : Subgroup (V₀ ≃ₗ[ZMod 2] V₀), H ≤ O₀ minus →
      NoNormalTwo H → IrreducibleSub H →
      ∀ L : Subgroup (V₀ ≃ₗ[ZMod 2] V₀), CensusCond minus H L b₀ →
      (∃ t ∈ L, IsTypeA (qModel minus) t 2) → Concl H) :
    ∀ H : Subgroup (V₀ ≃ₗ[ZMod 2] V₀), H ≤ O₀ minus →
      NoNormalTwo H → IrreducibleSub H →
      (∃ b : V₀, b ≠ 0 ∧ qModel minus b = 0 ∧
        ∃ L : Subgroup (V₀ ≃ₗ[ZMod 2] V₀), CensusCond minus H L b ∧
          ∃ t ∈ L, IsTypeA (qModel minus) t 2) → Concl H := by
  intro H hH hN hI ⟨b, hb0, hbq, L, hC, t, htL, htA⟩
  obtain ⟨g, hg, hgb⟩ := hconj b hb0 hbq
  have hHg : conjSub H g ≤ O₀ minus := conjSub_le_O hH hg
  have hN' : NoNormalTwo (conjSub H g) := noNormalTwo_conjSub hN
  have hI' : IrreducibleSub (conjSub H g) := irreducibleSub_conj hI
  have hC' : CensusCond minus (conjSub H g) (conjSub L g) b₀ := by
    have := censusCond_conj hC hg
    simpa [hgb] using this
  have htA' : IsTypeA (qModel minus) (g * t * g⁻¹) 2 := isTypeA_conj htA hg
  have htL' : g * t * g⁻¹ ∈ conjSub L g :=
    Subgroup.mem_map.mpr ⟨t, htL, by simp [MulAut.conj_apply]⟩
  exact hback H g hg (hmain (conjSub H g) hHg hN' hI' (conjSub L g) hC' ⟨_, htL', htA'⟩)

theorem censusPlus_of_reduction (b₀ : V₀)
    (hconj : ∀ b : V₀, b ≠ 0 → qModel false b = 0 → ∃ g ∈ O₀ false, g b = b₀)
    (hmain : ∀ H : Subgroup (V₀ ≃ₗ[ZMod 2] V₀), H ≤ O₀ false →
      NoNormalTwo H → IrreducibleSub H →
      ∀ L : Subgroup (V₀ ≃ₗ[ZMod 2] V₀), CensusCond false H L b₀ →
      (∃ t ∈ L, IsTypeA (qModel false) t 2) → CensusPlusConcl H) :
    CensusPlusProp := by
  unfold CensusPlusProp
  intro H hH hN hI hb
  refine census_reduction (minus := false) b₀ CensusPlusConcl hconj ?_ hmain H hH hN hI ?_
  · intro H' g hg hconcl
    rcases hconcl with h | h | ⟨k, hk, hkH⟩
    · exact Or.inl ((conjSub_eq_omega_iff (minus := false) hg).mp h)
    · exact Or.inr (Or.inl ((conjSub_eq_O_iff (minus := false) hg).mp h))
    · exact Or.inr (Or.inr (exists_conj_KPGL_iff (minus := false) hg ⟨k, hk, hkH⟩))
  · exact hb

theorem censusMinus_of_reduction (b₀ : V₀)
    (hconj : ∀ b : V₀, b ≠ 0 → qModel true b = 0 → ∃ g ∈ O₀ true, g b = b₀)
    (hmain : ∀ H : Subgroup (V₀ ≃ₗ[ZMod 2] V₀), H ≤ O₀ true →
      NoNormalTwo H → IrreducibleSub H →
      ∀ L : Subgroup (V₀ ≃ₗ[ZMod 2] V₀), CensusCond true H L b₀ →
      (∃ t ∈ L, IsTypeA (qModel true) t 2) → CensusMinusConcl H) :
    CensusMinusProp := by
  unfold CensusMinusProp
  intro H hH hN hI hb
  refine census_reduction (minus := true) b₀ CensusMinusConcl hconj ?_ hmain H hH hN hI ?_
  · intro H' g hg hconcl
    rcases hconcl with h | h
    · exact Or.inl ((conjSub_eq_omega_iff (minus := true) hg).mp h)
    · exact Or.inr ((conjSub_eq_O_iff (minus := true) hg).mp h)
  · exact hb

end CFSG.GF2Type.Smith1979W3.Cert690

end
