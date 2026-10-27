module

public import CFSG.GH74.GLS.Stage2.Signalizer.L46EAutD1Aut
public import CFSG.GH74.GLS.IVK.L2.Lemma19Aux
public import CFSG.GH74.GLS.Stage2.Signalizer.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L46E

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups commutatorElement

variable {F : Type} [Field F] [Finite F]

section Rho

variable {G : Type} [Group G] (ρ : G →* MulAut (projectiveSL 3 F))

theorem Rho_center (hρi : Function.Injective ρ) (hρr : ρ.range = linearAutGroup 3 F) {g : G}
    (hg : ∀ h, g * h = h * g) : g = 1 := by
  apply hρi
  rw [map_one]
  apply eq_one_of_commute_conj
  intro x
  have hx : MulAut.conj x ∈ ρ.range := hρr ▸ Iaut_le_D ⟨x, rfl⟩
  obtain ⟨h, hh⟩ := hx
  rw [← hh, ← map_mul, ← map_mul, hg h]

theorem Rho_commutator (hρi : Function.Injective ρ) (hρr : ρ.range = linearAutGroup 3 F) :
    commutator G = (Iaut F).comap ρ := by
  apply le_antisymm
  · rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_comap, map_commutatorElement]
    simp only [commutatorElement_def]
    exact comm_mem_Iaut (hρr ▸ ⟨a, rfl⟩) (hρr ▸ ⟨b, rfl⟩)
  · intro g hg
    have h1 : ρ g ∈ (commutator G).map ρ := by
      rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top, hρr,
        commutator_D_eq_Iaut]
      exact Subgroup.mem_comap.1 hg
    obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.1 h1
    rwa [← hρi hyg]

theorem Rho_coprime_three (hF4 : Nat.card F = 4) (hρi : Function.Injective ρ)
    (hρr : ρ.range = linearAutGroup 3 F) {g : G} (hg : Nat.Coprime (orderOf g) 3) :
    g ∈ commutator G := by
  rw [Rho_commutator ρ hρi hρr, Subgroup.mem_comap]
  refine mem_Iaut_of_coprime_three hF4 (hρr ▸ ⟨g, rfl⟩) hg ?_
  rw [← map_pow, pow_orderOf_eq_one, map_one]



theorem Rho_exists_psi (hρi : Function.Injective ρ) (hρr : ρ.range = linearAutGroup 3 F) :
    ∃ ψ : projectiveSL 3 F →* G, (∀ x, ρ (ψ x) = MulAut.conj x) ∧ Function.Injective ψ ∧
      ψ.range = commutator G := by
  let ι : projectiveSL 3 F →* ↥ρ.range :=
    (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).codRestrict ρ.range
      (fun x => hρr ▸ Iaut_le_D ⟨x, rfl⟩)
  let ψ : projectiveSL 3 F →* G := ((MonoidHom.ofInjective hρi).symm.toMonoidHom).comp ι
  have hψ : ∀ x, ρ (ψ x) = MulAut.conj x := by
    intro x
    have := (MonoidHom.ofInjective hρi).apply_symm_apply (ι x)
    have h2 := congrArg (fun z : ↥ρ.range => (z : MulAut (projectiveSL 3 F))) this
    exact h2
  have hinj : Function.Injective ψ := by
    intro a b hab
    apply conj_injective_P3 (F := F)
    rw [← hψ a, ← hψ b, hab]
  refine ⟨ψ, hψ, hinj, ?_⟩
  ext g
  rw [Rho_commutator ρ hρi hρr, Subgroup.mem_comap]
  constructor
  · rintro ⟨x, rfl⟩
    rw [hψ]
    exact ⟨x, rfl⟩
  · rintro ⟨x, hx⟩
    refine ⟨x, hρi ?_⟩
    rw [hψ]
    exact hx


theorem Rho_normal_ge (hρi : Function.Injective ρ) (hρr : ρ.range = linearAutGroup 3 F)
    {Q : Subgroup G} (hQ : Q.Normal) (hQ1 : Q ≠ ⊥) : commutator G ≤ Q := by
  obtain ⟨ψ, hψ, hψinj, hψr⟩ := Rho_exists_psi ρ hρi hρr
  have hQ0n : (Q.comap ψ).Normal := hQ.comap ψ
  have hsimple := isSimpleGroup_P3 (F := F)
  have hLn : (ψ.range).Normal := by rw [hψr]; infer_instance
  have hQ0 : Q.comap ψ ≠ ⊥ := by
    obtain ⟨q, hq1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hQ1
    have hq1' : (q : G) ≠ 1 := fun h => hq1 (Subtype.ext h)
    have hρq : ρ q ≠ 1 := fun h => hq1' (hρi (by rw [h, map_one]))
    by_contra hbot
    apply hρq
    apply eq_one_of_commute_conj
    intro x
    have h1 : ((ψ x) * q * (ψ x)⁻¹ * q⁻¹) ∈ Q := by
      have := hQ.conj_mem q q.2 (ψ x)
      exact Q.mul_mem this (Q.inv_mem q.2)
    have h2 : ((ψ x) * q * (ψ x)⁻¹ * q⁻¹) ∈ ψ.range := by
      have hq' : (q : G) * (ψ x)⁻¹ * (q : G)⁻¹ ∈ ψ.range :=
        hLn.conj_mem _ (ψ.range.inv_mem ⟨x, rfl⟩) q
      have := ψ.range.mul_mem (⟨x, rfl⟩ : ψ x ∈ ψ.range) hq'
      simpa [mul_assoc] using this
    obtain ⟨y, hy⟩ := h2
    have hyQ : y ∈ Q.comap ψ := by rw [Subgroup.mem_comap, hy]; exact h1
    rw [hbot, Subgroup.mem_bot] at hyQ
    rw [hyQ, map_one] at hy
    have h3 : (ψ x) * q * (ψ x)⁻¹ * (q : G)⁻¹ = 1 := hy.symm
    have h4 : (ψ x) * q = q * (ψ x) := by
      have h5 : (ψ x) * q * (ψ x)⁻¹ = q := by
        have := h3
        rw [mul_inv_eq_one] at this
        exact this
      calc (ψ x) * q = (ψ x) * q * (ψ x)⁻¹ * ψ x := by group
        _ = q * ψ x := by rw [h5]
    have := congrArg ρ h4
    rw [map_mul, map_mul, hψ] at this
    exact this.symm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Q.comap ψ) with h | h
  · exact absurd h hQ0
  · rw [← hψr]
    rintro _ ⟨y, rfl⟩
    have : y ∈ Q.comap ψ := h ▸ Subgroup.mem_top y
    exact this

end Rho


section Ambient

variable {Y : Type} [Group Y] {K : Subgroup Y} [K.Normal]

theorem pgl3four_odd_inner {F : Type} [Field F] [Finite F] (hF4 : Nat.card F = 4)
    (e : ↥K ≃* Matrix.ProjGenLinGroup (Fin 3) F) {y : Y} (hy : Odd (orderOf y)) :
    ∃ k₀ ∈ K, ∀ k ∈ K, y * k * y⁻¹ = k₀ * k * k₀⁻¹ := by
  classical
  let ρ : ↥K →* MulAut (projectiveSL 3 F) := (pglToAut F).comp e.toMonoidHom
  have hρi : Function.Injective ρ := (pglToAut_injective (F := F)).comp e.injective
  have hρr : ρ.range = linearAutGroup 3 F := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 e.surjective, Subgroup.map_top,
      range_pglToAut]
  obtain ⟨ψ, hψ, hψinj, hψr⟩ := Rho_exists_psi ρ hρi hρr
  let ψY : projectiveSL 3 F →* Y := K.subtype.comp ψ
  have hψYinj : Function.Injective ψY := K.subtype_injective.comp hψinj
  have hLn : (ψY.range).Normal := by
    have : ψY.range = ⁅K, K⁆ := by
      rw [← Subgroup.map_subtype_commutator, ← hψr, MonoidHom.range_comp]
    rw [this]
    infer_instance
  have : (ψY.range).Normal := hLn
  let eL : projectiveSL 3 F ≃* ↥ψY.range := MonoidHom.ofInjective hψYinj
  let κ : Y →* MulAut (projectiveSL 3 F) :=
    (MulAut.congr eL.symm).toMonoidHom.comp (MulAut.conjNormal : Y →* MulAut ↥ψY.range)
  have hκ : ∀ (g : Y) (x : projectiveSL 3 F), ψY (κ g x) = g * ψY x * g⁻¹ := by
    intro g x
    have h1 : eL (κ g x) = MulAut.conjNormal g (eL x) := by
      simp [κ, MulAut.congr_apply]
    have h2 := congrArg (fun z : ↥ψY.range => (z : Y)) h1
    simpa [eL, MonoidHom.ofInjective_apply, MulAut.conjNormal_apply] using h2
  have hκK : ∀ k : ↥K, κ (k : Y) = ρ k := by
    intro k
    ext x
    apply hψYinj
    have h1 := hκ (k : Y) x
    have h2 : ψ (ρ k x) = k * ψ x * k⁻¹ := by
      apply hρi
      rw [hψ, map_mul, map_mul, map_inv, hψ, mulAut_mul_conj_mul_inv]
    rw [h1]
    simp [ψY, h2]
  have hdvd : (κ y) ^ (orderOf y) = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hDmem : κ y ∈ linearAutGroup 3 F :=
    mem_linearAutGroup_of_odd_pow (ringAut_sq_of_card_four hF4) hy hdvd
  rw [← hρr] at hDmem
  obtain ⟨k₀, hk₀⟩ := hDmem
  refine ⟨(k₀ : Y), k₀.2, fun k hk => ?_⟩
  obtain ⟨a, ha⟩ : ∃ a : Y, a = (k₀ : Y) := ⟨_, rfl⟩
  set w : Y := a⁻¹ * y with hw
  have hκw : κ w = 1 := by rw [hw, map_mul, map_inv, ha, hκK, hk₀, inv_mul_cancel]
  have hwk : w * k * w⁻¹ = k := by
    have hu : w * k * w⁻¹ ∈ K := (inferInstance : K.Normal).conj_mem k hk w
    have : (⟨w * k * w⁻¹, hu⟩ : ↥K) = ⟨k, hk⟩ := by
      apply hρi
      rw [← hκK ⟨w * k * w⁻¹, hu⟩, ← hκK ⟨k, hk⟩]
      show κ (w * k * w⁻¹) = κ k
      rw [map_mul, map_mul, hκw, one_mul, map_inv, hκw, inv_one, mul_one]
    exact congrArg Subtype.val this
  rw [← ha]
  calc y * k * y⁻¹ = a * (w * k * w⁻¹) * a⁻¹ := by rw [hw]; group
    _ = a * k * a⁻¹ := by rw [hwk]

end Ambient


section KFacts

variable {Y : Type} [Group Y] {K : Subgroup Y} [K.Normal]

omit [K.Normal] in
theorem exists_rho (hK : IsPGL3Four ↥K) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (ρ : ↥K →* MulAut (projectiveSL 3 F)),
      Nat.card F = 4 ∧ Function.Injective ρ ∧ ρ.range = linearAutGroup 3 F := by
  obtain ⟨F, hF, hFin, hF4, ⟨e⟩⟩ := hK
  refine ⟨F, hF, hFin, (pglToAut F).comp e.toMonoidHom, hF4,
    (pglToAut_injective (F := F)).comp e.injective, ?_⟩
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 e.surjective, Subgroup.map_top, range_pglToAut]

omit [K.Normal] in
theorem pgl3four_center (hK : IsPGL3Four ↥K) {g : Y} (hg : g ∈ K) (h : ∀ k ∈ K, g * k = k * g) :
    g = 1 := by
  obtain ⟨F, _, _, ρ, hF4, hρi, hρr⟩ := exists_rho hK
  have := Rho_center ρ hρi hρr (g := ⟨g, hg⟩) (fun h' => Subtype.ext (h h'.1 h'.2))
  exact congrArg Subtype.val this

omit [K.Normal] in
theorem pgl3four_coprime_three (hK : IsPGL3Four ↥K) {g : Y} (hg : g ∈ K)
    (h3 : Nat.Coprime (orderOf g) 3) : g ∈ ⁅K, K⁆ := by
  obtain ⟨F, _, _, ρ, hF4, hρi, hρr⟩ := exists_rho hK
  have h1 : Nat.Coprime (orderOf (⟨g, hg⟩ : ↥K)) 3 := by
    rw [Subgroup.orderOf_mk]; exact h3
  have h2 := Rho_coprime_three ρ hF4 hρi hρr h1
  rw [← Subgroup.map_subtype_commutator]
  exact ⟨⟨g, hg⟩, h2, rfl⟩

omit [K.Normal] in
theorem pgl3four_normal_ge (hK : IsPGL3Four ↥K) {Q : Subgroup Y} (hQK : Q ≤ K)
    (hQn : ∀ q ∈ Q, ∀ k ∈ K, k * q * k⁻¹ ∈ Q) (hQ1 : Q ≠ ⊥) : ⁅K, K⁆ ≤ Q := by
  obtain ⟨F, _, _, ρ, hF4, hρi, hρr⟩ := exists_rho hK
  have hQ'n : (Q.subgroupOf K).Normal := ⟨fun q hq k => by
    rw [Subgroup.mem_subgroupOf] at hq ⊢
    exact hQn q hq k k.2⟩
  have hQ'1 : Q.subgroupOf K ≠ ⊥ := by
    intro hbot
    apply hQ1
    refine (Subgroup.eq_bot_iff_forall _).2 fun q hq => ?_
    have : (⟨q, hQK hq⟩ : ↥K) ∈ Q.subgroupOf K := Subgroup.mem_subgroupOf.2 hq
    rw [hbot, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  have h1 := Rho_normal_ge ρ hρi hρr hQ'n hQ'1
  rw [← Subgroup.map_subtype_commutator]
  rintro _ ⟨c, hc, rfl⟩
  exact Subgroup.mem_subgroupOf.1 (h1 hc)

theorem pgl3four_odd_inner' (hK : IsPGL3Four ↥K) {y : Y} (hy : Odd (orderOf y)) :
    ∃ k₀ ∈ K, ∀ k ∈ K, y * k * y⁻¹ = k₀ * k * k₀⁻¹ := by
  obtain ⟨F, hF, hFin, hF4, ⟨e⟩⟩ := hK
  exact pgl3four_odd_inner hF4 e hy

end KFacts

section L2Four

open CFSG.GorensteinWalter in
theorem isL2_four {I : Type} [Group I] (h : CFSG.GH74.GLS.IVK.IsL2 I (fun q => q = 4)) :
    IsSimpleGroup I ∧ ∃ t : I, t ≠ 1 ∧ t * t = 1 := by
  obtain ⟨F₀, _, _, hq, ⟨e⟩⟩ := h
  have hq' : Nat.card F₀ = 4 := hq
  let e' : I ≃* PSL2 F₀ := CFSG.GH74.GLS.IVK.toPSL e
  have hs : IsSimpleGroup (PSL2 F₀) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  refine ⟨e'.isSimpleGroup, ?_⟩
  obtain ⟨y, hy1, hy2⟩ := CFSG.GH74.GLS.IVK.exists_involution_psl2 (F := F₀)
  refine ⟨e'.symm y, fun h => hy1 (e'.symm.injective (by rw [h, map_one])), ?_⟩
  rw [← map_mul]
  have : y * y = 1 := by
    apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
    rw [map_mul, map_one, ← pow_two]
    exact hy2
  rw [this, map_one]

end L2Four



end CFSG.GH74.GLS.Stage2.Signalizer.L46E
