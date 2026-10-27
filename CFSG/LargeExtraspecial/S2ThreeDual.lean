module

public import CFSG.LargeExtraspecial.S2Three

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module CFSG.RankThree.OrthogonalInvolutions OrthoF2
open LinearMap (BilinForm)

namespace S2

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {f : BilinForm (ZMod 2) V}
variable [FiniteDimensional (ZMod 2) V]
variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]
variable (ρ : TauCeti.BilinForm.isometryGroup f →* (M ≃ₗ[ZMod 2] M))

omit [FiniteDimensional (ZMod 2) M] in
theorem sp_commSpace_spT_le (hf : f.IsAlt) (hnd : f.Nondegenerate) (h4 : 4 ≤ finrank (ZMod 2) V)
    {ι : V →ₗ[ZMod 2] M} (hι : Function.Injective ι)
    (hιρ : ∀ g x, ρ g (ι x) = ι ((g : V ≃ₗ[ZMod 2] V) x))
    (hcomm : ∀ g v, ρ g v - v ∈ LinearMap.range ι) {a : V} (ha0 : a ≠ 0) (v : M) :
    ρ (spT hf a) v - v ∈ (ZMod 2) ∙ ι a := by
  set δ : M →ₗ[ZMod 2] M := (ρ (spT hf a) : M →ₗ[ZMod 2] M) - 1 with hδ
  have hδv : ∀ w, ρ (spT hf a) w - w = δ w := fun w => rfl
  have hδι : ∀ x, δ (ι x) = f x a • ι a := fun x => by
    rw [← hδv, hιρ, spT_apply, map_add, map_smul, add_sub_cancel_left]
  by_contra hv
  rw [hδv] at hv
  obtain ⟨x₀, hx₀⟩ := hcomm (spT hf a) v
  rw [hδv] at hx₀
  have hx₀a : x₀ ∉ (ZMod 2) ∙ a := by
    intro h
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp h
    rw [← hx₀, map_smul] at hv
    exact hv (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  have hli : LinearIndependent (ZMod 2) ![a, x₀] := by
    refine linearIndependent_pair_iff.mpr ⟨ha0,
      fun h => hx₀a (by rw [h]; exact Submodule.zero_mem _),
      fun h => hx₀a (by rw [← h]; exact Submodule.mem_span_singleton_self a)⟩
  have hinv : ∀ g ∈ TauCeti.BilinForm.isometryGroup f, g a = a →
      ∀ x ∈ Submodule.span (ZMod 2) {a, x₀}, g x ∈ Submodule.span (ZMod 2) {a, x₀} := by
    intro g hg hga x hx
    set g' : TauCeti.BilinForm.isometryGroup f := ⟨g, hg⟩
    have hgx₀ : g x₀ ∈ Submodule.span (ZMod 2) {a, x₀} := by
      obtain ⟨y, hy⟩ := hcomm g' v
      have h1 : ι (g x₀) = δ (ρ g' v) := by
        change ι ((g' : V ≃ₗ[ZMod 2] V) x₀) = _
        rw [← hιρ, hx₀, ← hδv, ← hδv, rho_spT_sub ρ hf g' a v]
        change ρ (spT hf (g a)) (ρ g' v) - ρ g' v = _
        rw [hga]
      have h2 : ρ g' v = v + ι y := by rw [hy]; abel
      rw [h2, map_add, hδι, ← hx₀, ← map_smul, ← map_add] at h1
      rw [hι h1]
      exact Submodule.add_mem _ (Submodule.subset_span (by simp))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hx
    rw [map_add, map_smul, map_smul, hga]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ hgx₀)
  have h := sp_finrank_stab_invariant hf hnd ha0 hinv
  rw [finrank_span_pair hli] at h
  omega

theorem sp_timmesfeld_2_3_2 (hf : f.IsAlt) (hnd : f.Nondegenerate)
    (h4 : 4 ≤ finrank (ZMod 2) V) (hind : IsIndecomposable ρ) {ι : V →ₗ[ZMod 2] M}
    (hι : Function.Injective ι) (hιρ : ∀ g x, ρ g (ι x) = ι ((g : V ≃ₗ[ZMod 2] V) x))
    (hcomm : ∀ g v, ρ g v - v ∈ LinearMap.range ι) :
    finrank (ZMod 2) M ≤ finrank (ZMod 2) V + 1 := by
  have hF : (⊥ : Submodule (ZMod 2) V) ⊓ spPerp f ⊥ = ⊥ := bot_inf_eq _
  have htop : ∀ x : V, x ∈ spPerp f (⊥ : Submodule (ZMod 2) V) := fun x => by
    rw [spPerp_bot]
    exact Submodule.mem_top
  set δ : V → M →ₗ[ZMod 2] M := fun a => (ρ (spT hf a) : M →ₗ[ZMod 2] M) - 1 with hδ
  have hδv : ∀ a w, ρ (spT hf a) w - w = δ a w := fun _ _ => rfl
  have hδι : ∀ a x, δ a (ι x) = f x a • ι a := fun a x => by
    rw [← hδv, hιρ, spT_apply, map_add, map_smul, add_sub_cancel_left]
  have hιa : ∀ a : V, a ≠ 0 → ι a ≠ 0 := fun a ha h => ha (hι (by rw [h, map_zero]))
  classical
  have hφ : ∀ a : V, a ≠ 0 → ∃ φ : Module.Dual (ZMod 2) M, φ (ι a) = 1 :=
    fun a ha => Module.Projective.exists_dual_eq_one (ZMod 2) (hιa a ha)
  let lam : V → Module.Dual (ZMod 2) M := fun a =>
    if h : a ≠ 0 then (Classical.choose (hφ a h)).comp (δ a) else 0
  have hlam : ∀ a : V, a ≠ 0 → ∀ v, δ a v = lam a v • ι a := by
    intro a ha v
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
      (sp_commSpace_spT_le ρ hf hnd h4 hι hιρ hcomm ha v)
    have hspec := Classical.choose_spec (hφ a ha)
    simp only [lam, dite_eq_left ha, LinearMap.comp_apply]
    rw [← hδv, ← hc, map_smul, hspec, smul_eq_mul, mul_one]
  have hcoef : ∀ a : V, a ≠ 0 → ∀ c d : ZMod 2, c • ι a = d • ι a → c = d := by
    intro a ha c d h
    rcases zmod2_eq_zero_or_eq_one c with rfl | rfl <;>
      rcases zmod2_eq_zero_or_eq_one d with rfl | rfl
    · rfl
    · rw [zero_smul, one_smul] at h
      exact absurd h.symm (hιa a ha)
    · rw [zero_smul, one_smul] at h
      exact absurd h (hιa a ha)
    · rfl
  have hlamι : ∀ a : V, a ≠ 0 → ∀ x, lam a (ι x) = f x a := fun a ha x =>
    (hcoef a ha _ _ (by rw [← hlam a ha, hδι])).symm
  have hequiv : ∀ (g : TauCeti.BilinForm.isometryGroup f) (a : V), a ≠ 0 → ∀ v,
      lam ((g : V ≃ₗ[ZMod 2] V) a) (ρ g v) = lam a v := by
    intro g a ha v
    have hga : (g : V ≃ₗ[ZMod 2] V) a ≠ 0 := fun h => ha (g.1.map_eq_zero_iff.mp h)
    refine hcoef _ hga _ _ ?_
    rw [← hlam _ hga, ← hδv, ← rho_spT_sub ρ hf g a v, hδv, hlam a ha, map_smul, hιρ]
  have hTinv : ∀ b : V, ∀ w, ρ (spT hf b) (ρ (spT hf b) w) = w := fun b w => by
    rw [← LinearEquiv.mul_apply, ← map_mul,
      show spT hf b * spT hf b = 1 from Subtype.ext (by
        change spTransvection f hf b * spTransvection f hf b = 1
        rw [← spSiegel_zero_one]
        exact spSiegel_mul_self hf (map_zero _) 1), map_one]
    rfl
  have hadd1 : ∀ a b : V, a ≠ 0 → b ≠ 0 → f a b = 1 → ∀ v,
      lam (a + b) v = lam a v + lam b v := by
    intro a b ha hb hab v
    have h1 := hequiv (spT hf b) a ha (ρ (spT hf b) v)
    rw [hTinv, spT_apply, hab, one_smul] at h1
    rw [h1, show ρ (spT hf b) v = v + lam b v • ι b by
      rw [← hlam b hb, ← hδv]; abel, map_add, map_smul, hlamι a ha, smul_eq_mul,
      isAlt_symm hf b a, hab, mul_one]
  have hlam0 : lam 0 = 0 := by simp [lam]
  have hdef : ∀ a b a' b' : V, a ≠ 0 → b ≠ 0 → a' ≠ 0 → b' ≠ 0 → f a b = 0 → b ≠ a →
      f a' b' = 0 → b' ≠ a' → lam (a + b) + lam a + lam b = lam (a' + b') + lam a' + lam b' := by
    intro a b a' b' ha hb ha' hb' hab hne hab' hne'
    have hab0 : a + b ≠ 0 := fun h => hne (by
      rw [add_eq_zero_iff_eq_neg, vec_neg] at h
      exact h.symm)
    obtain ⟨g, hg, hga, hgb⟩ := exists_mem_spRadGen_apply_eq_orth hf hnd hF (htop a) (htop b)
      (htop a') (htop b') ha hb ha' hb' hab hne hab' hne'
    set g' : TauCeti.BilinForm.isometryGroup f := ⟨g, (spRadGen_le_spFix ⊥ hg).1⟩
    have hga' : (g' : V ≃ₗ[ZMod 2] V) a = a' := hga
    have hgb' : (g' : V ≃ₗ[ZMod 2] V) b = b' := hgb
    have hει : ∀ y, (lam (a + b) + lam a + lam b) (ι y) = 0 := by
      intro y
      simp only [LinearMap.add_apply]
      rw [hlamι _ hab0, hlamι a ha, hlamι b hb, map_add]
      ring_nf
      reduce_mod_char
    have hvan : ∀ w, (lam (a + b) + lam a + lam b) (ρ g' w) =
        (lam (a + b) + lam a + lam b) w := by
      intro w
      obtain ⟨y, hy⟩ := hcomm g' w
      have h2 : ρ g' w = w + ι y := by rw [hy]; abel
      rw [h2, map_add, hει, add_zero]
    have hε' : ∀ u, (lam (a' + b') + lam a' + lam b') (ρ g' u) =
        (lam (a + b) + lam a + lam b) u := by
      intro u
      simp only [LinearMap.add_apply]
      rw [← hga', ← hgb', ← map_add, hequiv g' _ hab0, hequiv g' a ha, hequiv g' b hb]
    ext w
    have hw : w = ρ g' (ρ g'⁻¹ w) := by
      rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
    rw [hw, hvan, hε']
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : V, a₀ ≠ 0 :=
    (Module.finrank_pos_iff_exists_ne_zero (R := ZMod 2)).mp (by omega)
  obtain ⟨b₀, hb₀perp, hb₀⟩ : ∃ b₀ ∈ spPerp f ((ZMod 2) ∙ a₀), b₀ ∉ (ZMod 2) ∙ a₀ := by
    by_contra! h
    have hle := Submodule.finrank_mono h
    rw [LinearMap.BilinForm.finrank_orthogonal hnd, finrank_span_singleton ha₀] at hle
    omega
  have hab₀ : f a₀ b₀ = 0 := (mem_spPerp.mp hb₀perp) a₀ (Submodule.mem_span_singleton_self a₀)
  have hb₀0 : b₀ ≠ 0 := fun h => hb₀ (by rw [h]; exact Submodule.zero_mem _)
  have hb₀a₀ : b₀ ≠ a₀ := fun h => hb₀ (by rw [h]; exact Submodule.mem_span_singleton_self a₀)
  set ε₀ := lam (a₀ + b₀) + lam a₀ + lam b₀ with hε₀
  set N₀ := fixOf ρ (Set.range (spTransvection f hf)) with hN₀
  have hN₀mem : ∀ v, (∀ a : V, a ≠ 0 → lam a v = 0) → v ∈ N₀ := by
    intro v hv g ⟨a, ha⟩
    have hg : g = spT hf a := Subtype.ext ha.symm
    rw [hg]
    by_cases ha0 : a = 0
    · rw [ha0]
      change ρ (spT hf 0) v = v
      rw [show spT hf 0 = 1 from Subtype.ext (by
        ext x
        change spTransvection f hf 0 x = x
        rw [spTransvection_apply, smul_zero, add_zero]), map_one]
      rfl
    · have := hlam a ha0 v
      rw [hv a ha0, zero_smul, ← hδv, sub_eq_zero] at this
      exact this
  set n := finrank (ZMod 2) V with hn
  set e := Module.finBasis (ZMod 2) V with he
  let Ψ : M →ₗ[ZMod 2] (Fin n → ZMod 2) × ZMod 2 :=
    (LinearMap.pi fun i => lam (e i)).prod ε₀
  have hker : LinearMap.ker Ψ ≤ N₀ := by
    intro v hv
    have hv1 : ∀ i, lam (e i) v = 0 := fun i => congrFun (congrArg Prod.fst hv) i
    have hv2 : ε₀ v = 0 := congrArg Prod.snd hv
    have hadd : ∀ x y : V, lam (x + y) v = lam x v + lam y v := by
      intro x y
      by_cases hx : x = 0
      · rw [hx, zero_add, hlam0, LinearMap.zero_apply, zero_add]
      by_cases hy : y = 0
      · rw [hy, add_zero, hlam0, LinearMap.zero_apply, add_zero]
      by_cases hxy : y = x
      · rw [hxy, vec_add_self x, hlam0, LinearMap.zero_apply, zmod2_add_self]
      rcases zmod2_eq_zero_or_eq_one (f x y) with h0 | h1
      · have h := congrArg (fun φ => φ v) (hdef x y a₀ b₀ hx hy ha₀ hb₀0 h0 hxy hab₀ hb₀a₀)
        rw [← hε₀, hv2] at h
        simp only [LinearMap.add_apply] at h
        rw [add_assoc, add_eq_zero_iff_eq_neg, zmod2_neg] at h
        exact h
      · exact hadd1 x y hx hy h1 v
    let H : V →ₗ[ZMod 2] ZMod 2 :=
      { toFun := fun a => lam a v
        map_add' := hadd
        map_smul' := fun c x => by
          rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
          · rw [zero_smul, hlam0, LinearMap.zero_apply, RingHom.id_apply, zero_smul]
          · rw [one_smul, RingHom.id_apply, one_smul] }
    have hH : H = 0 := e.ext fun i => hv1 i
    exact hN₀mem v fun a _ => LinearMap.congr_fun hH a
  have hdimΨ := LinearMap.finrank_range_add_finrank_ker Ψ
  have hrange : finrank (ZMod 2) (LinearMap.range Ψ) ≤ n + 1 := by
    have := Submodule.finrank_le (LinearMap.range Ψ)
    rwa [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_self] at this
  have hkerN := Submodule.finrank_mono hker
  have hN₀fix : ∀ v ∈ N₀, ∀ g, ρ g v = v := by
    intro v hv g
    have hcl := fixOf_closure ρ (S := Set.range (spTransvection f hf))
      (fun t ⟨a, ha⟩ => ha ▸ spTransvection_mem_isometryGroup hf a)
    rw [hN₀, ← hcl] at hv
    exact hv g (sp_le_closure_spTransvection hf hnd g.2)
  have hN₀ι : N₀ ⊓ LinearMap.range ι = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨hwN, x, rfl⟩
    have hx0 : x = 0 := by
      refine hnd.1 x fun a => ?_
      by_cases ha : a = 0
      · rw [ha, map_zero]
      have h1 := hlam a ha (ι x)
      rw [hlamι a ha, ← hδv, sub_eq_zero.mpr (hwN (spT hf a) ⟨a, rfl⟩)] at h1
      exact hcoef a ha _ _ (by rw [zero_smul]; exact h1.symm)
    rw [hx0, map_zero]
    exact Submodule.zero_mem _
  have hιdim : finrank (ZMod 2) (LinearMap.range ι) = n :=
    LinearMap.finrank_range_of_inj hι
  have hιinv : ∀ g, ∀ w ∈ LinearMap.range ι, ρ g w ∈ LinearMap.range ι := by
    rintro g _ ⟨x, rfl⟩
    exact ⟨_, (hιρ g x).symm⟩
  have hN₀inv : ∀ g, ∀ w ∈ N₀, ρ g w ∈ N₀ := fun g w hw => by rw [hN₀fix w hw g]; exact hw
  have hιne : LinearMap.range ι ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hιdim
    omega
  by_contra hcon
  push Not at hcon
  have hN₀ne : N₀ ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hkerN
    omega
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range ι) N₀
  rw [inf_comm, hN₀ι, finrank_bot, add_zero, hιdim] at hsup
  by_cases htop : LinearMap.range ι ⊔ N₀ = ⊤
  · have hc : IsCompl (LinearMap.range ι) N₀ :=
      ⟨disjoint_iff.mpr (by rw [inf_comm]; exact hN₀ι), codisjoint_iff.mpr htop⟩
    rcases hind _ _ hιinv hN₀inv hc with h | h
    · exact hιne h
    · exact hN₀ne h
  · obtain ⟨v, -, hv⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.mpr htop)
    set M' := LinearMap.range ι ⊔ (ZMod 2) ∙ v with hM'
    have hvι : v ∉ LinearMap.range ι := fun h => hv (Submodule.mem_sup_left h)
    have hM'dim : finrank (ZMod 2) M' = n + 1 := by
      have h1 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range ι) ((ZMod 2) ∙ v)
      have hinf : LinearMap.range ι ⊓ (ZMod 2) ∙ v = ⊥ := by
        rw [eq_bot_iff]
        rintro w ⟨hwι, hwv⟩
        rcases mem_span_singleton_iff.mp hwv with h | h
        · exact (Submodule.mem_bot _).mpr h
        · exact absurd (h ▸ hwι) hvι
      have hv0 : v ≠ 0 := fun h => hvι (h ▸ Submodule.zero_mem _)
      rw [hinf, finrank_bot, add_zero, hιdim, finrank_span_singleton hv0] at h1
      exact h1
    have hM'N : M' ⊓ N₀ = ⊥ := by
      rw [eq_bot_iff]
      rintro w ⟨hwM, hwN⟩
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hwM
      rcases mem_span_singleton_iff.mp hz with hz0 | hzv
      · rw [hz0, add_zero] at hwN ⊢
        have : y ∈ N₀ ⊓ LinearMap.range ι := ⟨hwN, hy⟩
        rw [hN₀ι] at this
        exact this
      · rw [hzv] at hwN
        exfalso
        apply hv
        have : v = (y + v) - y := by abel
        rw [this, sup_comm]
        exact Submodule.sub_mem _ (Submodule.mem_sup_left hwN) (Submodule.mem_sup_right hy)
    have hM'top : M' ⊔ N₀ = ⊤ := by
      refine Submodule.eq_top_of_finrank_eq ?_
      have h1 := Submodule.finrank_sup_add_finrank_inf_eq M' N₀
      rw [hM'N, finrank_bot, add_zero, hM'dim] at h1
      have h2 := Submodule.finrank_le (M' ⊔ N₀)
      omega
    have hM'inv : ∀ g, ∀ w ∈ M', ρ g w ∈ M' := by
      intro g w hw
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hw
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
      obtain ⟨x, hx⟩ := hcomm g v
      have hgv : ρ g v = v + ι x := by rw [hx]; abel
      rw [map_add, map_smul, hgv, smul_add]
      refine Submodule.add_mem _ (Submodule.mem_sup_left (hιinv g y hy)) ?_
      refine Submodule.add_mem _ (Submodule.mem_sup_right (Submodule.smul_mem _ _
        (Submodule.mem_span_singleton_self v))) ?_
      exact Submodule.mem_sup_left (Submodule.smul_mem _ _ ⟨x, rfl⟩)
    have hc : IsCompl M' N₀ := ⟨disjoint_iff.mpr hM'N, codisjoint_iff.mpr hM'top⟩
    rcases hind _ _ hM'inv hN₀inv hc with h | h
    · rw [h, finrank_bot] at hM'dim
      omega
    · exact hN₀ne h

end S2

end CFSG.LargeExtraspecial
