module

public import CFSG.LargeExtraspecial.S2SixSpAut

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module CFSG.RankThree.OrthogonalInvolutions OrthoF2
open LinearMap (BilinForm)

namespace S2

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {f : BilinForm (ZMod 2) V}

theorem spSiegel_mem_spG (hf : f.IsAlt) (p u : V) (c : ZMod 2) : spSiegel f hf p u c ∈ SpG f := by
  by_cases hpu : f p u = 0
  · exact spSiegel_mem_isometryGroup hf hpu c
  · rw [spSiegel, dite_eq_right hpu]
    exact one_mem _

theorem spSiegel_mul (hf : f.IsAlt) {p u u' : V} (hpu : f p u = 0) (hpu' : f p u' = 0)
    (c c' : ZMod 2) :
    spSiegel f hf p u c * spSiegel f hf p u' c' = spSiegel f hf p (u + u') (c + c' + f u' u) := by
  have hpuu : f p (u + u') = 0 := by rw [map_add, hpu, hpu', add_zero]
  have hup : f u p = 0 := by rw [isAlt_symm hf, hpu]
  have hu'p : f u' p = 0 := by rw [isAlt_symm hf, hpu']
  ext x
  rw [LinearEquiv.mul_apply, spSiegel_apply hf hpu', spSiegel_apply hf hpu,
    spSiegel_apply hf hpuu]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    hf.self_eq_zero, hu'p, hpu, mul_zero, add_zero]
  refine eq_of_one_smul_eq ?_
  match_scalars <;> ring1

theorem sp_eq_of_spSiegel_eq (hf : f.IsAlt) {F : Submodule (ZMod 2) V} {p p₁ u u' : V}
    (hpp₁ : f p p₁ = 1) (hu : u ∈ spPerp f (F ⊔ Submodule.span (ZMod 2) {p, p₁}))
    (hu' : u' ∈ spPerp f (F ⊔ Submodule.span (ZMod 2) {p, p₁})) {c c' : ZMod 2}
    (h : spSiegel f hf p u c = spSiegel f hf p u' c') : u = u' ∧ c = c' := by
  obtain ⟨-, hpu, hp₁u⟩ := mem_spPerp_sup_span_pair.mp hu
  obtain ⟨-, hpu', hp₁u'⟩ := mem_spPerp_sup_span_pair.mp hu'
  have hp₁p : f p₁ p = 1 := by rw [isAlt_symm hf, hpp₁]
  have e := congrArg (fun g : V ≃ₗ[ZMod 2] V => g p₁) h
  rw [spSiegel_apply hf hpu, spSiegel_apply hf hpu', hp₁p, one_smul, one_smul, mul_one,
    mul_one, hp₁u, hp₁u', zero_add, zero_add, add_assoc, add_assoc] at e
  have e' := add_left_cancel e
  have hc := congrArg (fun x => f x p₁) e'
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hpp₁,
    mul_one] at hc
  rw [isAlt_symm hf u p₁, hp₁u, isAlt_symm hf u' p₁, hp₁u', zero_add, zero_add] at hc
  refine ⟨?_, hc⟩
  rw [hc] at e'
  exact add_right_cancel e'

theorem sp_exists_eq_spSiegel_perp (hf : f.IsAlt) (hnd : f.Nondegenerate)
    {F : Submodule (ZMod 2) V} {p p₁ : V} (hpF : p ∈ spPerp f F) (hp0 : p ≠ 0)
    (hpp₁ : f p p₁ = 1) {t : V ≃ₗ[ZMod 2] V} (ht : t ∈ spRadFix f F p) :
    ∃ u ∈ spPerp f (F ⊔ Submodule.span (ZMod 2) {p, p₁}), ∃ c, t = spSiegel f hf p u c := by
  obtain ⟨u, huF, hpu, c, rfl⟩ := (mem_spRadFix_iff hf hnd hp0 hpF).mp ht
  refine ⟨u + f u p₁ • p, ?_, c, (spSiegel_add_smul hf hpu _ c).symm⟩
  rw [mem_spPerp_sup_span_pair]
  refine ⟨Submodule.add_mem _ huF (Submodule.smul_mem _ _ hpF), ?_, ?_⟩
  · rw [map_add, map_smul, hpu, hf.self_eq_zero, smul_zero, add_zero]
  · rw [map_add, map_smul, isAlt_symm hf p₁ p, hpp₁, smul_eq_mul, mul_one, isAlt_symm hf p₁ u,
      zmod2_add_self]

variable [FiniteDimensional (ZMod 2) V]

theorem sp_timmesfeld_2_4_of_map_zero (hf : f.IsAlt) (hnd : f.Nondegenerate)
    {F : Submodule (ZMod 2) V} (hF : F ⊓ spPerp f F = ⊥) {φ : V → V} (h0 : φ 0 = 0)
    (hφ : ∀ x ∈ spPerp f F, φ x ∈ spPerp f F)
    (hcomm : ∀ g ∈ spFix f F, ∀ x ∈ spPerp f F, φ (g x) = g (φ x)) :
    ∃ c : ZMod 2, ∀ x ∈ spPerp f F, φ x = c • x := by
  by_cases hne : spPerp f F = ⊥
  · exact ⟨0, fun x hx => by
      rw [hne, Submodule.mem_bot] at hx
      rw [hx, h0, smul_zero]⟩
  obtain ⟨p₀, hp₀F, hp₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hfix : φ p₀ ∈ (ZMod 2) ∙ p₀ := by
    refine sp_fixed_mem_span_of_spRadFix hf hnd hF hp₀F hp₀0 (hφ p₀ hp₀F) fun t ht => ?_
    rw [← hcomm t (spRadFix_le_spFix F p₀ ht) p₀ hp₀F, ht.1.2.1]
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hfix
  refine ⟨c, fun x hx => ?_⟩
  by_cases hx0 : x = 0
  · rw [hx0, h0, smul_zero]
  obtain ⟨g, hg, hgx⟩ := exists_mem_spRadGen_apply_eq hf hnd hF hp₀F hx hp₀0 hx0
  rw [← hgx, hcomm g (spRadGen_le_spFix F hg) p₀ hp₀F, ← hc, map_smul]

namespace SpAutOn

variable {F : Submodule (ZMod 2) V} {α : SpG f → SpG f}

theorem eq_self_of_finrank_two (hα : SpAutOn F α) (hf : f.IsAlt) (hnd : f.Nondegenerate)
    (hF : F ⊓ spPerp f F = ⊥) (hdim : finrank (ZMod 2) (spPerp f F) = 2 * 1) {p p₁ : V}
    (hpF : p ∈ spPerp f F) (hp₁F : p₁ ∈ spPerp f F) (hpp₁ : f p p₁ = 1)
    (hαp : SpMapsRad F α p p) (t : SpG f) (ht : (t : V ≃ₗ[ZMod 2] V) ∈ spRadFix f F p) :
    α t = t := by
  obtain ⟨hp0, -, -⟩ := linearIndependent_pair_iff.mp (linearIndependent_of_apply_eq_one hf hpp₁)
  have hK0 : spPerp f (F ⊔ Submodule.span (ZMod 2) {p, p₁}) = ⊥ := by
    have := finrank_spPerp_sup_span_pair hf hnd hF hpF hp₁F hpp₁
    exact Submodule.finrank_eq_zero.mp (by omega)
  have hform : ∀ s : SpG f, (s : V ≃ₗ[ZMod 2] V) ∈ spRadFix f F p →
      ∃ c, (s : V ≃ₗ[ZMod 2] V) = spSiegel f hf p 0 c := by
    intro s hs
    obtain ⟨u, hu, c, hsu⟩ := sp_exists_eq_spSiegel_perp hf hnd hpF hp0 hpp₁ hs
    rw [hK0, Submodule.mem_bot] at hu
    exact ⟨c, by rw [hsu, hu]⟩
  have h00 : spSiegel f hf p 0 0 = 1 := by
    ext x
    rw [spSiegel_apply hf (map_zero _)]
    simp
  obtain ⟨c, hc⟩ := hform t ht
  rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
  · have ht1 : t = 1 := Subtype.ext (by rw [hc, h00]; rfl)
    rw [ht1, hα.map_one]
  · obtain ⟨c', hc'⟩ := hform (α t) ((hαp t ht.2).mp ht)
    rcases zmod2_eq_zero_or_eq_one c' with rfl | rfl
    · exfalso
      have h1 : α t = α 1 := by
        rw [hα.map_one]
        exact Subtype.ext (by rw [hc', h00]; rfl)
      have := congrArg Subtype.val (hα.inj _ _ ht.2 (one_mem _) h1)
      rw [hc] at this
      have h2 := sp_eq_of_spSiegel_eq (F := F) hf hpp₁ (u := 0) (u' := 0)
        (Submodule.zero_mem _) (Submodule.zero_mem _) (c := 1) (c' := 0) (this.trans h00.symm)
      exact one_ne_zero h2.2
    · exact Subtype.ext (hc'.trans hc.symm)

theorem eq_self_of_forall_levi (hα : SpAutOn F α) (hf : f.IsAlt) (hnd : f.Nondegenerate)
    (hF : F ⊓ spPerp f F = ⊥) {m : ℕ} (hm : 2 ≤ m) (hdim : finrank (ZMod 2) (spPerp f F) = 2 * m)
    {p p₁ : V} (hpF : p ∈ spPerp f F) (hp₁F : p₁ ∈ spPerp f F) (hpp₁ : f p p₁ = 1)
    (hαp : SpMapsRad F α p p)
    (hY : ∀ g : SpG f,
      (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup (F ⊔ Submodule.span (ZMod 2) {p, p₁}) → α g = g)
    (t : SpG f) (ht : (t : V ≃ₗ[ZMod 2] V) ∈ spRadFix f F p) : α t = t := by
  obtain ⟨hp0, -, -⟩ := linearIndependent_pair_iff.mp (linearIndependent_of_apply_eq_one hf hpp₁)
  set K := F ⊔ Submodule.span (ZMod 2) {p, p₁} with hKdef
  have hK : K ⊓ spPerp f K = ⊥ := sup_span_pair_inf_spPerp_eq_bot hf hF hpF hp₁F hpp₁
  have hKdim : finrank (ZMod 2) (spPerp f K) + 2 = finrank (ZMod 2) (spPerp f F) :=
    finrank_spPerp_sup_span_pair hf hnd hF hpF hp₁F hpp₁
  let T : V → ZMod 2 → SpG f := fun u c => ⟨spSiegel f hf p u c, spSiegel_mem_spG hf p u c⟩
  have hTL : ∀ u ∈ spPerp f K, ∀ c, (T u c : V ≃ₗ[ZMod 2] V) ∈ spRadFix f F p := fun u hu c =>
    (mem_spRadFix_iff hf hnd hp0 hpF).mpr
      ⟨u, (mem_spPerp_sup_span_pair.mp hu).1, (mem_spPerp_sup_span_pair.mp hu).2.1, c, rfl⟩
  have hTF : ∀ u ∈ spPerp f K, ∀ c, (T u c : V ≃ₗ[ZMod 2] V) ∈ fixGroup F :=
    fun u hu c => (hTL u hu c).2
  have hform : ∀ s : SpG f, (s : V ≃ₗ[ZMod 2] V) ∈ spRadFix f F p →
      ∃ u ∈ spPerp f K, ∃ c, s = T u c := by
    intro s hs
    obtain ⟨u, hu, c, hsu⟩ := sp_exists_eq_spSiegel_perp hf hnd hpF hp0 hpp₁ hs
    exact ⟨u, hu, c, Subtype.ext hsu⟩
  have huniq : ∀ u ∈ spPerp f K, ∀ u' ∈ spPerp f K, ∀ c c', T u c = T u' c' → u = u' ∧ c = c' :=
    fun u hu u' hu' c c' h => sp_eq_of_spSiegel_eq hf hpp₁ hu hu' (congrArg Subtype.val h)
  have hmul : ∀ u ∈ spPerp f K, ∀ u' ∈ spPerp f K, ∀ c c',
      T u c * T u' c' = T (u + u') (c + c' + f u' u) := fun u hu u' hu' c c' =>
    Subtype.ext (spSiegel_mul hf (mem_spPerp_sup_span_pair.mp hu).2.1
      (mem_spPerp_sup_span_pair.mp hu').2.1 c c')
  have hT00 : T 0 0 = 1 := Subtype.ext (by
    ext x
    change spSiegel f hf p 0 0 x = x
    rw [spSiegel_apply hf (map_zero _)]
    simp)
  have h0K : (0 : V) ∈ spPerp f K := Submodule.zero_mem _
  have hconj : ∀ y : SpG f, (y : V ≃ₗ[ZMod 2] V) ∈ fixGroup K → ∀ u ∈ spPerp f K, ∀ c,
      y * T u c * y⁻¹ = T ((y : V ≃ₗ[ZMod 2] V) u) c := by
    intro y hy u hu c
    obtain ⟨-, hyp, -⟩ := mem_fixGroup_sup_span_pair.mp hy
    refine Subtype.ext ?_
    change (y : V ≃ₗ[ZMod 2] V) * spSiegel f hf p u c * (y : V ≃ₗ[ZMod 2] V)⁻¹ = _
    rw [spSiegel_conj hf y.2 (mem_spPerp_sup_span_pair.mp hu).2.1, hyp]
  have hyK : ∀ y : SpG f, (y : V ≃ₗ[ZMod 2] V) ∈ fixGroup K → ∀ u ∈ spPerp f K,
      (y : V ≃ₗ[ZMod 2] V) u ∈ spPerp f K := fun y hy u hu => apply_mem_spPerp y.2 hy hu
  have hyF : ∀ y : SpG f, (y : V ≃ₗ[ZMod 2] V) ∈ fixGroup K →
      (y : V ≃ₗ[ZMod 2] V) ∈ fixGroup F := fun y hy => fixGroup_anti le_sup_left hy
  have hαconj : ∀ y : SpG f, (y : V ≃ₗ[ZMod 2] V) ∈ fixGroup K → ∀ s : SpG f,
      (s : V ≃ₗ[ZMod 2] V) ∈ fixGroup F → α (y * s * y⁻¹) = y * α s * y⁻¹ := by
    intro y hy s hs
    rw [hα.map_mul _ _ (sp_coe_mul_mem_fixGroup (hyF y hy) hs)
      (sp_coe_inv_mem_fixGroup (hyF y hy)), hα.map_mul _ _ (hyF y hy) hs,
      hα.map_inv (hyF y hy), hY y hy]
  have htrans : ∀ u ∈ spPerp f K, ∀ u' ∈ spPerp f K, u ≠ 0 → u' ≠ 0 →
      ∃ y : SpG f, (y : V ≃ₗ[ZMod 2] V) ∈ fixGroup K ∧ (y : V ≃ₗ[ZMod 2] V) u = u' := by
    intro u hu u' hu' hu0 hu'0
    obtain ⟨y, hy, hyu⟩ := exists_mem_spRadGen_apply_eq hf hnd hK hu hu' hu0 hu'0
    have hyS := spRadGen_le_spFix K hy
    exact ⟨⟨y, hyS.1⟩, hyS.2, hyu⟩
  have hα01 : α (T 0 1) = T 0 1 := by
    obtain ⟨u₁, hu₁, c₁, h₁⟩ := hform _ ((hαp _ (hTF 0 h0K 1)).mp (hTL 0 h0K 1))
    have hu₁0 : u₁ = 0 := by
      by_contra hu₁0
      obtain ⟨w, hwK, hw⟩ := sp_exists_partner hf hnd hK hu₁ hu₁0
      have hw0 : w ≠ 0 := by
        rintro rfl
        rw [map_zero] at hw
        exact zero_ne_one hw
      have hwu : w ≠ u₁ := by
        rintro rfl
        rw [hf.self_eq_zero] at hw
        exact zero_ne_one hw
      obtain ⟨y, hy, hyu⟩ := htrans u₁ hu₁ w hwK hu₁0 hw0
      have e := hαconj y hy (T 0 1) (hTF 0 h0K 1)
      rw [hconj y hy 0 h0K 1, map_zero, h₁, hconj y hy u₁ hu₁ c₁, hyu] at e
      exact hwu (huniq u₁ hu₁ w hwK c₁ c₁ e).1.symm
    rw [hu₁0] at h₁
    rcases zmod2_eq_zero_or_eq_one c₁ with hc | hc
    · exfalso
      rw [hc, hT00, ← hα.map_one] at h₁
      have := huniq 0 h0K 0 h0K 1 0 (by rw [hT00]; exact hα.inj _ _ (hTF 0 h0K 1) (one_mem _) h₁)
      exact one_ne_zero this.2
    · rw [h₁, hc]
  have hα0c : ∀ c, α (T 0 c) = T 0 c := by
    intro c
    rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
    · rw [hT00, hα.map_one]
    · exact hα01
  have hex : ∀ v : V, ∃ u : V, ∃ c : ZMod 2, v ∈ spPerp f K →
      u ∈ spPerp f K ∧ α (T v 0) = T u c := by
    intro v
    by_cases hv : v ∈ spPerp f K
    · obtain ⟨u, hu, c, h⟩ := hform _ ((hαp _ (hTF v hv 0)).mp (hTL v hv 0))
      exact ⟨u, c, fun _ => ⟨hu, h⟩⟩
    · exact ⟨0, 0, fun h => absurd h hv⟩
  choose φ lam hφ using hex
  have hφK : ∀ v ∈ spPerp f K, φ v ∈ spPerp f K := fun v hv => (hφ v hv).1
  have hφT : ∀ v ∈ spPerp f K, α (T v 0) = T (φ v) (lam v) := fun v hv => (hφ v hv).2
  have hadd : ∀ v ∈ spPerp f K, ∀ w ∈ spPerp f K,
      φ (v + w) = φ v + φ w ∧ lam (v + w) + f w v = lam v + lam w + f (φ w) (φ v) := by
    intro v hv w hw
    have hvw := Submodule.add_mem _ hv hw
    have e1 : T v 0 * T w 0 = T (v + w) 0 * T 0 (f w v) := by
      rw [hmul v hv w hw, hmul (v + w) hvw 0 h0K]
      simp only [add_zero, zero_add, map_zero, LinearMap.zero_apply]
    have e2 := congrArg α e1
    rw [hα.map_mul _ _ (hTF v hv 0) (hTF w hw 0), hα.map_mul _ _ (hTF _ hvw 0) (hTF 0 h0K _),
      hφT v hv, hφT w hw, hφT _ hvw, hα0c, hmul _ (hφK v hv) _ (hφK w hw),
      hmul _ (hφK _ hvw) 0 h0K] at e2
    simp only [add_zero, map_zero, LinearMap.zero_apply] at e2
    obtain ⟨h1, h2⟩ := huniq _ (Submodule.add_mem _ (hφK v hv) (hφK w hw)) _ (hφK _ hvw) _ _ e2
    exact ⟨h1.symm, h2.symm⟩
  have hequiv : ∀ y : SpG f, (y : V ≃ₗ[ZMod 2] V) ∈ fixGroup K → ∀ v ∈ spPerp f K,
      φ ((y : V ≃ₗ[ZMod 2] V) v) = (y : V ≃ₗ[ZMod 2] V) (φ v) ∧
        lam ((y : V ≃ₗ[ZMod 2] V) v) = lam v := by
    intro y hy v hv
    have e := hαconj y hy (T v 0) (hTF v hv 0)
    rw [hconj y hy v hv 0, hφT _ (hyK y hy v hv), hφT v hv, hconj y hy _ (hφK v hv)] at e
    exact huniq _ (hφK _ (hyK y hy v hv)) _ (hyK y hy _ (hφK v hv)) _ _ e
  have hφ0 : φ 0 = 0 := by
    have := (hadd 0 h0K 0 h0K).1
    rwa [add_zero, vec_add_self] at this
  obtain ⟨c, hc⟩ := sp_timmesfeld_2_4_of_map_zero hf hnd hK hφ0 hφK fun g hg x hx =>
    (hequiv ⟨g, hg.1⟩ hg.2 x hx).1
  have hc1 : c = 1 := by
    rcases zmod2_eq_zero_or_eq_one c with h0 | h1
    · exfalso
      obtain ⟨v, hvK, hv0⟩ : ∃ v ∈ spPerp f K, v ≠ 0 :=
        Submodule.exists_mem_ne_zero_of_ne_bot fun h => by
          rw [h, finrank_bot] at hKdim
          omega
      have hφv : φ v = 0 := by rw [hc v hvK, h0, zero_smul]
      have e := hφT v hvK
      rw [hφv, ← hα0c] at e
      have := huniq v hvK 0 h0K 0 _ (hα.inj _ _ (hTF v hvK 0) (hTF 0 h0K _) e)
      exact hv0 this.1
    · exact h1
  have hφid : ∀ v ∈ spPerp f K, φ v = v := fun v hv => by rw [hc v hv, hc1, one_smul]
  have hlam : ∀ v ∈ spPerp f K, lam v = 0 := by
    intro v hv
    by_cases hv0 : v = 0
    · have := (hadd 0 h0K 0 h0K).2
      rw [hv0]
      simp only [add_zero, map_zero, hφ0, zmod2_add_self] at this
      exact this
    obtain ⟨w, hwK, hw⟩ := sp_exists_partner hf hnd hK hv hv0
    have hw0 : w ≠ 0 := by
      rintro rfl
      rw [map_zero] at hw
      exact zero_ne_one hw
    have hvw0 : v + w ≠ 0 := by
      intro h
      rw [add_eq_zero_iff_eq_neg, vec_neg] at h
      rw [h, hf.self_eq_zero] at hw
      exact zero_ne_one hw
    have hvwK := Submodule.add_mem _ hv hwK
    obtain ⟨y₁, hy₁, hy₁v⟩ := htrans v hv w hwK hv0 hw0
    obtain ⟨y₂, hy₂, hy₂v⟩ := htrans v hv (v + w) hvwK hv0 hvw0
    have h1 : lam w = lam v := by rw [← hy₁v]; exact (hequiv y₁ hy₁ v hv).2
    have h2 : lam (v + w) = lam v := by rw [← hy₂v]; exact (hequiv y₂ hy₂ v hv).2
    have h3 := (hadd v hv w hwK).2
    rw [hφid v hv, hφid w hwK, add_left_inj, h1, h2, zmod2_add_self] at h3
    exact h3
  obtain ⟨u, hu, c', rfl⟩ := hform t ht
  have e : T u c' = T u 0 * T 0 c' := by
    rw [hmul u hu 0 h0K]
    simp only [add_zero, zero_add, map_zero, LinearMap.zero_apply]
  rw [e, hα.map_mul _ _ (hTF u hu 0) (hTF 0 h0K c'), hφT u hu, hα0c, hφid u hu, hlam u hu]

end SpAutOn

end S2

end CFSG.LargeExtraspecial
