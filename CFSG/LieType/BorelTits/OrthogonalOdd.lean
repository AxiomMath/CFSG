module

public import CFSG.LieType.BorelTits.OrthogonalEichler
public import CFSG.LieType.BorelTits.OrthogonalModels
public import CFSG.LieType.BorelTits.Anisotropic
public import CFSG.LieType.BorelTits.IsotropicKernel
public import CFSG.LieType.BorelTits.CentralQuotient
public import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.LieType.BorelTits

universe u v w

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

namespace ReflForm

variable (F : ReflForm K V)

theorem perp_eq_self_of_two_mul_finrank [FiniteDimensional K V] {W : Submodule K V}
    (hW : F.IsTotallyIsotropic W) (hd : 2 * Module.finrank K W = Module.finrank K V) :
    F.perp W = W := by
  have := F.finrank_perp W
  exact (Submodule.eq_of_le_of_finrank_eq hW (by omega)).symm

theorem det_eq_one_of_isometry [FiniteDimensional K V] (hσ : F.σ = RingEquiv.refl K)
    {g : V →ₗ[K] V} (hg : ∀ u v, F.β (g u) (g v) = F.β u v) {L : Submodule K V}
    (hL : F.perp L = L) (hgL : L ≤ L.comap g) : LinearMap.det g = 1 := by
  let φ : V →ₗ[K] Module.Dual K L :=
    { toFun := fun v =>
        { toFun := fun l => F.β l v
          map_add' := fun l l' => F.add_left _ _ _
          map_smul' := fun c l => by
            simp only [Submodule.coe_smul, F.smul_left, hσ, RingEquiv.refl_apply, smul_eq_mul,
              RingHom.id_apply] }
      map_add' := fun v v' => LinearMap.ext fun l => F.add_right _ _ _
      map_smul' := fun c v => LinearMap.ext fun l => F.smul_right _ _ _ }
  have hφ : ∀ v (l : L), φ v l = F.β l v := fun _ _ => rfl
  have hker : LinearMap.ker φ = L := by
    refine le_antisymm (fun v hv => ?_) fun v hv => ?_
    · have hv' : v ∈ F.perp L := fun l hl => by
        have := LinearMap.congr_fun (LinearMap.mem_ker.mp hv) ⟨l, hl⟩
        rwa [hφ] at this
      rwa [hL] at hv'
    · have hv' : v ∈ F.perp L := by rwa [hL]
      exact LinearMap.mem_ker.mpr (LinearMap.ext fun l => by rw [hφ, hv' l l.2]; rfl)
  let φ' := L.liftQ φ hker.ge
  have hφ'inj : Function.Injective φ' := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ hker.le
  have hdim : Module.finrank K (V ⧸ L) = Module.finrank K (Module.Dual K L) := by
    rw [Subspace.dual_finrank_eq]
    have h1 := Submodule.finrank_quotient_add_finrank L
    have h2 := F.finrank_perp L
    rw [hL] at h2
    omega
  let e : (V ⧸ L) ≃ₗ[K] Module.Dual K L := LinearEquiv.ofBijective φ'
    ⟨hφ'inj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hφ'inj⟩
  have he : ∀ v, e (Submodule.Quotient.mk v) = φ v := fun _ => rfl
  have key : (g.restrict hgL).dualMap ∘ₗ ((e : (V ⧸ L) →ₗ[K] Module.Dual K L) ∘ₗ
      L.mapQ L g hgL ∘ₗ (e.symm : Module.Dual K L →ₗ[K] V ⧸ L)) = LinearMap.id := by
    refine LinearMap.ext fun ψ => ?_
    obtain ⟨q, rfl⟩ := e.surjective ψ
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective L q
    refine LinearMap.ext fun l => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      Submodule.mapQ_apply, LinearMap.id_apply]
    simp only [he, LinearMap.dualMap_apply, LinearMap.restrict_apply, hφ]
    exact hg l v
  have hdet := congrArg LinearMap.det key
  rw [LinearMap.det_comp, LinearMap.det_dualMap, LinearMap.det_conj, LinearMap.det_id] at hdet
  rw [LinearMap.det_eq_det_mul_det L g hgL]
  exact hdet

end ReflForm

variable {H : Type w} [Group H]

section Middle

variable (F : ReflForm K V) (ρ : H →* Module.End K V)

theorem triv_of_isotropic_fixed_mem [Finite V] (p : ℕ) [Fact p.Prime] [CharP K p]
    (hρ : IsIsometric F ρ) {X : Submodule K V} (hX : F.IsTotallyIsotropic X) (S : Subgroup H)
    (hS : IsPGroup p S) (hstab : ∀ g ∈ S, ∀ v ∈ X, ρ g v ∈ X)
    (hmax : ∀ v ∈ F.perp X, F.β v v = 0 → (∀ g ∈ S, ρ g v - v ∈ X) → v ∈ X) :
    ∀ g ∈ S, ∀ v ∈ F.perp X, ρ g v - v ∈ X := by
  set Φ := relFix F ρ X S with hΦ
  suffices hΦtop : F.perp X ≤ Φ by
    intro g hg v hv
    exact (hΦtop hv).2 g hg
  by_contra hne
  have hΦle : Φ ≤ F.perp X := relFix_le_perp F ρ X S
  have hΦlt : Φ < F.perp X := lt_of_le_of_ne hΦle fun h => hne h.symm.le
  have hXle : X ≤ F.perp Φ := le_perp_relFix F ρ X S
  have hXne : X ≠ F.perp Φ := by
    intro h
    have hpp : F.perp (F.perp Φ) = F.perp X := by rw [← h]
    have : FiniteDimensional K V := Module.Finite.of_finite
    rw [F.perp_perp] at hpp
    exact hΦlt.ne hpp
  have hXlt : X < F.perp Φ := lt_of_le_of_ne hXle hXne
  have hstabΦ : ∀ g ∈ S, ∀ v ∈ Φ, ρ g v ∈ Φ := fun g hg v hv =>
    apply_mem_relFix F ρ hX hstab hg hv
  have hstabΦperp : ∀ g ∈ S, ∀ v ∈ F.perp Φ, ρ g v ∈ F.perp Φ := fun g hg v hv =>
    hρ.apply_mem_perp_of_forall (fun w hw => hstabΦ g⁻¹ (inv_mem hg) w hw) hv
  obtain ⟨v, hvΦ, hvX, hvfix⟩ :=
    exists_mem_notMem_forall_sub_mem ρ p S hS hXlt hstab hstabΦperp
  have hvperp : v ∈ F.perp X := F.perp_antitone (le_relFix F ρ hX hstab) hvΦ
  have hvin : v ∈ Φ := ⟨hvperp, hvfix⟩
  exact hvX (hmax v hvperp (hvΦ v hvin) hvfix)

end Middle

section Criterion

variable (Φ : QuadForm K V) (h2 : (2 : K) ≠ 0) {ρ : H →* Module.End K V}

include h2 in
theorem sub_mem_of_isotropic_fixed [FiniteDimensional K V] (hρ : IsIsometric Φ.polar ρ)
    {A : Submodule K V} (hA : Φ.polar.IsTotallyIsotropic A)
    (hd : 2 * (Module.finrank K A + 1) = Module.finrank K V) {S : Subgroup H}
    (hstab : ∀ g ∈ S, ∀ v ∈ A, ρ g v ∈ A) {v : V} (hv : v ∈ Φ.polar.perp A) (hvA : v ∉ A)
    (hvv : Φ.polar.β v v = 0) (hvfix : ∀ g ∈ S, ρ g v - v ∈ A) :
    ∀ g ∈ S, ∀ w ∈ Φ.polar.perp A, ρ g w - w ∈ A := by
  have hA₁iso : Φ.polar.IsTotallyIsotropic (A ⊔ K ∙ v) := hA.sup_span hv hvv
  have hA₁perp : Φ.polar.perp (A ⊔ K ∙ v) = A ⊔ K ∙ v :=
    Φ.polar.perp_eq_self_of_two_mul_finrank hA₁iso
      (by rw [Submodule.finrank_sup_span_singleton hvA]; omega)
  have hA₁fix : ∀ g ∈ S, ∀ z ∈ A ⊔ K ∙ v, ρ g z - z ∈ A := by
    intro g hg z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hz
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
    have : ρ g (a + c • v) - (a + c • v) = (ρ g a - a) + c • (ρ g v - v) := by
      rw [map_add, map_smul]
      module
    rw [this]
    exact add_mem (sub_mem (hstab g hg a ha) ha) (Submodule.smul_mem _ c (hvfix g hg))
  intro g hg w hw
  have hmem : ρ g w - w ∈ A ⊔ K ∙ v := by
    rw [← hA₁perp]
    intro z hz
    have h1 := hρ g (ρ g⁻¹ z) w
    rw [rep_apply_inv_apply] at h1
    rw [Φ.polar.β_sub_right, h1, ← Φ.polar.β_sub_left]
    exact hw _ (hA₁fix g⁻¹ (inv_mem hg) z hz)
  by_cases hvw : Φ.polar.β v w = 0
  ·
    have hwA₁ : w ∈ A ⊔ K ∙ v := by
      rw [← hA₁perp, Φ.polar.perp_sup]
      exact ⟨hw, Φ.polar.mem_perp_span_singleton.mpr hvw⟩
    exact hA₁fix g hg w hwA₁
  ·
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hmem
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
    have hnorm := hρ g w w
    rw [show ρ g w = w + (a + c • v) by rw [hab]; abel] at hnorm
    have haw : Φ.polar.β a w = 0 := hw a ha
    have hwa : Φ.polar.β w a = 0 := Φ.polar.refl _ _ haw
    have haa : Φ.polar.β a a = 0 := hA ha a ha
    have hav : Φ.polar.β a v = 0 := hv a ha
    have hva : Φ.polar.β v a = 0 := Φ.polar.refl _ _ hav
    simp only [Φ.polar.add_left, Φ.polar.add_right, Φ.polar.smul_right, Φ.polar_smul_left, haw,
      hwa, haa, hav, hva, hvv] at hnorm
    rw [Φ.polar_symm w v] at hnorm
    have hc : c = 0 := by
      have : (2 * Φ.polar.β v w) * c = 0 := by linear_combination hnorm
      exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero h2 hvw)
    rw [← hab, hc, zero_smul, add_zero]
    exact ha

include h2 in
theorem triv_of_two_mul_finrank_succ [Finite V] (p : ℕ) [Fact p.Prime] [CharP K p]
    (hρ : IsIsometric Φ.polar ρ) {A : Submodule K V} (hA : Φ.polar.IsTotallyIsotropic A)
    (hd : 2 * (Module.finrank K A + 1) = Module.finrank K V) (S : Subgroup H)
    (hS : IsPGroup p S) (hstab : ∀ g ∈ S, ∀ v ∈ A, ρ g v ∈ A) :
    ∀ g ∈ S, ∀ v ∈ Φ.polar.perp A, ρ g v - v ∈ A := by
  have : FiniteDimensional K V := Module.Finite.of_finite
  by_cases hex : ∃ v ∈ Φ.polar.perp A, v ∉ A ∧ Φ.polar.β v v = 0 ∧ ∀ g ∈ S, ρ g v - v ∈ A
  · obtain ⟨v, hv, hvA, hvv, hvfix⟩ := hex
    exact sub_mem_of_isotropic_fixed Φ h2 hρ hA hd hstab hv hvA hvv hvfix
  · exact triv_of_isotropic_fixed_mem Φ.polar ρ p hρ hA S hS hstab fun v hv hvv hvfix => by
      by_contra hvA
      exact hex ⟨v, hv, hvA, hvv, hvfix⟩

include h2 in
theorem apply_mem_of_det_eq_one [FiniteDimensional K V] {A L : Submodule K V}
    (hL : Φ.polar.IsTotallyIsotropic L) (hLd : 2 * Module.finrank K L = Module.finrank K V)
    (hAL : A ≤ L) (hrank : Module.finrank K L = Module.finrank K A + 1) {g : V →ₗ[K] V}
    (hg : ∀ u v, Φ.polar.β (g u) (g v) = Φ.polar.β u v) (hdet : LinearMap.det g = 1)
    (hgA : ∀ v ∈ Φ.polar.perp A, g v ∈ Φ.polar.perp A) : ∀ v ∈ L, g v ∈ L := by
  have hLperp : Φ.polar.perp L = L := Φ.polar.perp_eq_self_of_two_mul_finrank hL hLd
  have hLA : L ≤ Φ.polar.perp A := hL.trans (Φ.polar.perp_antitone hAL)
  obtain ⟨e, heL, heA⟩ : ∃ e ∈ L, e ∉ A := IsConcreteLE.exists_of_lt
    (lt_of_le_of_ne hAL fun h => by rw [h] at hrank; omega)
  have hLe : L = A ⊔ K ∙ e := (Submodule.eq_of_le_of_finrank_eq
    (sup_le hAL ((Submodule.span_singleton_le_iff_mem _ _).mpr heL))
    (by rw [Submodule.finrank_sup_span_singleton heA, hrank])).symm
  by_contra! hcon
  obtain ⟨u, huL, hguL⟩ := hcon
  have hfA : g u ∈ Φ.polar.perp A := hgA u (hLA huL)
  have hff : Φ.polar.β (g u) (g u) = 0 := by rw [hg]; exact hL huL u huL
  have hef : Φ.polar.β e (g u) ≠ 0 := by
    intro hef
    apply hguL
    rw [← hLperp, hLe, Φ.polar.perp_sup]
    exact ⟨hfA, Φ.polar.mem_perp_span_singleton.mpr hef⟩
  obtain ⟨f, hfdef⟩ : ∃ f, f = (Φ.polar.β e (g u))⁻¹ • g u := ⟨_, rfl⟩
  have hef' : Φ.polar.β e f = 1 := by rw [hfdef, Φ.polar.smul_right, inv_mul_cancel₀ hef]
  have hfA' : f ∈ Φ.polar.perp A := by
    rw [hfdef]
    exact Submodule.smul_mem _ _ hfA
  have hff' : Φ.polar.β f f = 0 := by
    rw [hfdef, Φ.polar_smul_left, Φ.polar.smul_right, hff, mul_zero, mul_zero]
  have hfL : f ∉ L := fun h => hguL (by
    have := L.smul_mem (Φ.polar.β e (g u)) h
    rwa [hfdef, smul_smul, mul_inv_cancel₀ hef, one_smul] at this)
  have hfnA : f ∉ A := fun h => hfL (hAL h)
  have hM : Φ.polar.IsTotallyIsotropic (A ⊔ K ∙ f) := (hL.mono hAL).sup_span hfA' hff'
  have hMperp : Φ.polar.perp (A ⊔ K ∙ f) = A ⊔ K ∙ f :=
    Φ.polar.perp_eq_self_of_two_mul_finrank hM
      (by rw [Submodule.finrank_sup_span_singleton hfnA, ← hrank, hLd])
  have hgLM : ∀ v ∈ L, g v ∈ A ⊔ K ∙ f := by
    intro v hv
    rw [← hMperp, Φ.polar.perp_sup]
    refine ⟨hgA v (hLA hv), Φ.polar.mem_perp_span_singleton.mpr ?_⟩
    rw [hfdef, Φ.polar_smul_left, hg, hL hv u huL, mul_zero]
  have hQe : Φ.Q e = 0 := Φ.Q_eq_zero_of_polar_self h2 (hL heL e heL)
  have hQf : Φ.Q f = 0 := Φ.Q_eq_zero_of_polar_self h2 hff'
  have hQw : Φ.Q (e - f) = -1 := by
    rw [sub_eq_add_neg, Φ.Q_add, ← neg_one_smul K f, Φ.Q_smul, hQe, hQf, Φ.polar.smul_right,
      hef']
    ring
  have hwA : ∀ a ∈ A, Φ.reflect (e - f) a = a := fun a ha =>
    Φ.reflect_apply_of_polar_eq_zero (by
      rw [Φ.polar.β_sub_left, hL (hAL ha) e heL, Φ.polar.refl _ _ (hfA' a ha), sub_zero])
  have hwf : Φ.reflect (e - f) f = e := by
    rw [Φ.reflect_apply, Φ.polar.β_sub_left, hef', hff', hQw]
    module
  have hrM : ∀ v ∈ A ⊔ K ∙ f, Φ.reflect (e - f) v ∈ L := by
    intro v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
    rw [map_add, map_smul, hwA a ha, hwf, hLe]
    exact add_mem (Submodule.mem_sup_left ha)
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e)))
  have hdet' := Φ.polar.det_eq_one_of_isometry Φ.polar_σ (g := Φ.reflect (e - f) ∘ₗ g)
    (fun u v => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, Φ.polar_map_of_Q (Φ.Q_reflect (e - f)), hg])
    hLperp fun v hv => hrM _ (hgLM v hv)
  rw [LinearMap.det_comp, Φ.det_reflect (by rw [hQw]; exact neg_ne_zero.mpr one_ne_zero), hdet,
    mul_one] at hdet'
  exact h2 (by linear_combination -hdet')

include h2 in
theorem holds_of_quadForm [Finite H] [Finite V] (p : ℕ) [Fact p.Prime] [CharP K p]
    (hd : 3 ≤ Module.finrank K V) (hρ : IsIsometric Φ.polar ρ) (hinj : Function.Injective ρ)
    (hdet : ∀ h, LinearMap.det (ρ h) = 1)
    (heich : ∀ x y, Φ.Q x = 0 → Φ.polar.β x y = 0 → ∃ h : H, ∀ v, ρ h v = Φ.eichler x y v) :
    Holds H p := by
  have : FiniteDimensional K V := Module.Finite.of_finite
  refine holds_of_isoFlags Φ.polar ρ p hρ hinj (fun W hW hWiso => ?_) (fun R _ _ => ?_)
  ·
    obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    obtain ⟨u, hu⟩ : ∃ u, Φ.polar.β w u = 1 := by
      by_contra! h
      apply hw0
      refine Φ.polar.nondeg w fun v => ?_
      by_contra hv
      apply h ((Φ.polar.β w v)⁻¹ • v)
      rw [Φ.polar.smul_right, inv_mul_cancel₀ hv]
    have hww : Φ.polar.β w w = 0 := hWiso hwW w hwW
    have hQw : Φ.Q w = 0 := Φ.Q_eq_zero_of_polar_self h2 hww
    have huw : Φ.polar.β u w = 1 := by rw [Φ.polar_symm, hu]
    have hQf : Φ.Q (u + (-Φ.Q u) • w) = 0 := by
      rw [Φ.Q_add, Φ.Q_smul, hQw, Φ.polar.smul_right, huw]
      ring
    have hfw : Φ.polar.β (u + (-Φ.Q u) • w) w = 1 := by
      rw [Φ.polar.add_left, Φ.polar_smul_left, hww, huw]
      ring
    obtain ⟨y, hfy, hy⟩ := Φ.exists_polar_eq_zero_Q_ne_zero hd (u + (-Φ.Q u) • w)
    obtain ⟨h, hh⟩ := heich _ y hQf hfy
    refine ⟨h, w, hwW, fun hmem => hy ?_⟩
    have h0 : Φ.polar.β (ρ h w - w) w = 0 := hWiso hwW _ (sub_mem hmem hwW)
    have h3 : ρ h w - w = y - (Φ.Q y + Φ.polar.β y w) • (u + (-Φ.Q u) • w) := by
      rw [hh, Φ.eichler_apply, hfw, one_smul]
      module
    rw [h3, Φ.polar.β_sub_left, Φ.polar_smul_left, hfw] at h0
    linear_combination -h0
  ·
    obtain ⟨X, m, hX0, hXmono, hXiso, hXrank, hXstable, hrefine, hmax⟩ :=
      exists_isotropicChain_refining Φ.polar (isoSeq Φ.polar ρ R) (isoSeq_zero Φ.polar ρ R)
        (isoSeq_mono Φ.polar ρ R) (isoSeq_isTotallyIsotropic Φ.polar ρ R)
    have hU'p : IsPGroup p (flagKernel ρ (isoCompletion Φ.polar X m)) :=
      isPGroup_flagKernel ρ p hinj (isoCompletion_zero hX0 m) (isoCompletion_top hX0 m)
    have hU'stab : flagKernel ρ (isoCompletion Φ.polar X m) ≤ flagStab ρ X := by
      refine (flagKernel_le_flagStab ρ _).trans (flagStab_le_flagStab ρ fun k => ⟨min k m, ?_⟩)
      rw [isoCompletion_of_le (min_le_right k m)]
      rcases le_total k m with hkm | hkm
      · rw [min_eq_left hkm]
      · rw [min_eq_right hkm, hXstable k hkm]
    have hstep : ∀ k < m, Φ.polar.perp (X (k + 1)) ≠ X (k + 1) → ∀ v ∈ Φ.polar.perp (X k),
        (∀ g ∈ flagKernel ρ (isoCompletion Φ.polar X m), ρ g v - v ∈ X k) → v ∈ X (k + 1) := by
      intro k hk hne v hv hfix
      by_contra hvX
      have hlt : X k < X (k + 1) := by
        refine lt_of_le_of_ne (hXmono (Nat.le_succ k)) fun h => ?_
        have := hXrank (k + 1) (by omega)
        rw [← h, hXrank k (by omega)] at this
        omega
      obtain ⟨x, hx, hxk⟩ := IsConcreteLE.exists_of_lt hlt
      have hQx : Φ.Q x = 0 := Φ.Q_eq_zero_of_polar_self h2 (hXiso (k + 1) hx x hx)
      have hXk1 : X (k + 1) = X k ⊔ K ∙ x := by
        refine (Submodule.eq_of_le_of_finrank_eq
          (sup_le (hXmono (Nat.le_succ k)) ((Submodule.span_singleton_le_iff_mem _ _).mpr hx))
          ?_).symm
        rw [Submodule.finrank_sup_span_singleton hxk, hXrank k (by omega),
          hXrank (k + 1) (by omega)]
      have hU : ∀ y ∈ Φ.polar.perp (X (k + 1)), ∃ h ∈ flagKernel ρ (isoCompletion Φ.polar X m),
          ∀ v, ρ h v = Φ.eichler x y v := by
        intro y hy
        obtain ⟨h, hh⟩ := heich x y hQx (hy x hx)
        refine ⟨h, mem_flagKernel_isoCompletion ρ hXmono hXiso hk hx hy
          (a := y - Φ.Q y • x) (sub_mem hy (Submodule.smul_mem _ _ (hXiso (k + 1) hx))) (-1)
          fun v => ?_, hh⟩
        rw [hh, Φ.eichler_apply, neg_one_mul, neg_smul, ← sub_eq_add_neg]
      by_cases hxv : Φ.polar.β x v = 0
      ·
        have hvperp : v ∈ Φ.polar.perp (X (k + 1)) := by
          rw [hXk1, Φ.polar.perp_sup]
          exact ⟨hv, Φ.polar.mem_perp_span_singleton.mpr hxv⟩
        obtain ⟨y, hy, hyv⟩ : ∃ y ∈ Φ.polar.perp (X (k + 1)), Φ.polar.β y v ≠ 0 := by
          by_contra! h
          apply hvX
          have hpp : v ∈ Φ.polar.perp (Φ.polar.perp (X (k + 1))) := fun y hy => h y hy
          rwa [Φ.polar.perp_perp] at hpp
        obtain ⟨h, hhU, hh⟩ := hU y hy
        have := hfix h hhU
        rw [hh, Φ.eichler_apply, hxv, zero_smul, add_zero, sub_sub_cancel_left, ← neg_smul,
          Submodule.smul_mem_iff _ (neg_ne_zero.mpr hyv)] at this
        exact hxk this
      ·
        obtain ⟨y, hy, hyX⟩ := IsConcreteLE.exists_of_lt
          (lt_of_le_of_ne (hXiso (k + 1)) (Ne.symm hne))
        obtain ⟨h, hhU, hh⟩ := hU y hy
        have hmem : Φ.polar.β x v • y ∈ X (k + 1) := by
          have h1 := hfix h hhU
          have h3 : Φ.polar.β x v • y = (ρ h v - v) + (Φ.polar.β x v * Φ.Q y +
              Φ.polar.β y v) • x := by
            rw [hh, Φ.eichler_apply]
            module
          rw [h3]
          exact add_mem (hXmono (Nat.le_succ k) h1) (Submodule.smul_mem _ _ hx)
        exact hyX ((Submodule.smul_mem_iff _ hxv).mp hmem)
    by_cases hL : Φ.polar.perp (X m) = X m
    ·
      have hm : Module.finrank K (X m) = m := hXrank m le_rfl
      have hdm : 2 * m = Module.finrank K V := by
        have := Φ.polar.finrank_perp (X m)
        rw [hL, hm] at this
        omega
      refine exists_sylow_normalizer_le_of_isotropicChain Φ.polar ρ p hρ R X m (m - 1)
        (Nat.sub_le m 1) hX0 hXmono hXiso hXrank hXstable hrefine _ hU'p hU'stab
        (fun k hk => hstep k (by omega) fun h => ?_) (fun S hS hSstab g hg v hv => ?_)
        (fun S hseq k hk1 hk2 => ?_)
      · have := Φ.polar.finrank_perp (X (k + 1))
        rw [h, hXrank (k + 1) (by omega)] at this
        omega
      · exact triv_of_two_mul_finrank_succ Φ h2 p hρ (hXiso (m - 1))
          (by rw [hXrank (m - 1) (by omega)]; omega) S hS (fun g hg w hw => (hSstab hg 0 w hw).1)
          g hg v hv
      ·
        rw [show k = m by omega]
        have hA : ∀ h ∈ Subgroup.normalizer ((S : Subgroup H) : Set H), ∀ v ∈ X (m - 1),
            ρ h v ∈ X (m - 1) := fun h hh v hv => by
          have := apply_mem_isoSeq Φ.polar ρ hρ S (m - 1) hh (v := v)
          rw [hseq, min_self] at this
          exact this hv
        have key : ∀ h ∈ Subgroup.normalizer ((S : Subgroup H) : Set H), ∀ v ∈ X m,
            ρ h v ∈ X m := fun h hh =>
          apply_mem_of_det_eq_one Φ h2 (hXiso m) (by rw [hm]; omega) (hXmono (Nat.sub_le m 1))
            (by rw [hm, hXrank (m - 1) (by omega)]; omega) (hρ h) (hdet h)
            fun v hv => hρ.apply_mem_perp_of_forall (fun w hw => hA _ (inv_mem hh) w hw) hv
        intro h hh j v hv
        exact ⟨key h hh v hv, key h⁻¹ (inv_mem hh) v hv⟩
    ·
      refine exists_sylow_normalizer_le_of_isotropicChain Φ.polar ρ p hρ R X m m le_rfl hX0
        hXmono hXiso hXrank hXstable hrefine _ hU'p hU'stab (fun k hk => hstep k hk fun h => ?_)
        (fun S hS hSstab g hg v hv => ?_) (fun S _ k hk1 hk2 => absurd hk2 (by omega))
      · apply hL
        have h1 := Φ.polar.finrank_perp (X (k + 1))
        have h3 := Φ.polar.finrank_perp (X m)
        have h4 := Submodule.finrank_mono (hXiso m)
        rw [h, hXrank (k + 1) hk] at h1
        rw [hXrank m le_rfl] at h3 h4
        rw [show m = k + 1 by omega, h]
      · exact triv_of_anisotropic Φ.polar ρ p hρ (hXiso m) hmax S hS
          (fun g hg w hw => (hSstab hg 0 w hw).1) g hg v hv

end Criterion

section Models

open Matrix CFSG.Assembly.LowTwoRank

theorem two_ne_zero_of_charP_ne_two {F : Type*} [Field F] (p : ℕ) [Fact p.Prime] [CharP F p]
    (hp : p ≠ 2) : (2 : F) ≠ 0 := by
  intro h
  have : p ∣ 2 := (CharP.cast_eq_zero_iff F p 2).mp (by exact_mod_cast h)
  exact hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp this)

theorem holds_statedOmega_of_quadForm {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] (Φ : QuadForm K (ι → K))
    (h2 : (2 : K) ≠ 0) (hι : 3 ≤ Fintype.card ι) : Holds (StatedOmega Φ.Q) p := by
  refine holds_of_quadForm Φ h2 p (by rwa [Module.finrank_fintype_fun_eq_card])
    (isIsometric_natRep_statedOmega Φ) (natRep_injective _) (fun h => ?_)
    (fun x y hx hxy => ?_)
  · have : natRep (StatedOmega Φ.Q) h = Matrix.toLin' ((h : GL ι K) : Matrix ι ι K) :=
      LinearMap.ext fun v => by rw [natRep_apply, Matrix.toLin'_apply]
    rw [this, LinearMap.det_toLin']
    exact det_eq_one_of_mem_statedOmega Φ.Q h.2
  · obtain ⟨A, hA, hAv⟩ := exists_mem_statedOmega_eichler Φ h2 hι hx hxy
    exact ⟨⟨A, hA⟩, fun v => by rw [natRep_apply]; exact hAv v⟩

variable (n : ℕ) (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]

theorem holds_statedOmega_quadOdd (hp : p ≠ 2) (hn : 1 ≤ n) :
    Holds (StatedOmega (StatedQuadOdd n K)) p := by
  have h2 := two_ne_zero_of_charP_ne_two (F := K) p hp
  have hι : 3 ≤ Fintype.card (Fin n ⊕ Fin n ⊕ Unit) := by
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
    omega
  exact holds_statedOmega_of_quadForm p (quadOddForm n K h2) h2 hι

theorem holds_statedOmega_quadPlus (hp : p ≠ 2) (hn : 2 ≤ n) :
    Holds (StatedOmega (StatedQuadPlus n K)) p := by
  have hι : 3 ≤ Fintype.card (Fin n ⊕ Fin n) := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  exact holds_statedOmega_of_quadForm p (quadPlusForm n K) (two_ne_zero_of_charP_ne_two p hp) hι

theorem holds_statedOmega_quadMinus (hp : p ≠ 2) (hn : 2 ≤ n) (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Holds (StatedOmega (StatedQuadMinus n K b c)) p := by
  have hι : 3 ≤ Fintype.card (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  exact holds_statedOmega_of_quadForm p (quadMinusForm n K b c hirr)
    (two_ne_zero_of_charP_ne_two p hp) hι

theorem holds_statedProj_statedOmega_quadOdd (hp : p ≠ 2) (hn : 1 ≤ n) :
    Holds (StatedProj (StatedOmega (StatedQuadOdd n K))) p :=
  Holds.statedProj _ (holds_statedOmega_quadOdd n K p hp hn)

theorem holds_statedProj_statedOmega_quadPlus (hp : p ≠ 2) (hn : 2 ≤ n) :
    Holds (StatedProj (StatedOmega (StatedQuadPlus n K))) p :=
  Holds.statedProj _ (holds_statedOmega_quadPlus n K p hp hn)

theorem holds_statedProj_statedOmega_quadMinus (hp : p ≠ 2) (hn : 2 ≤ n) (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Holds (StatedProj (StatedOmega (StatedQuadMinus n K b c))) p :=
  Holds.statedProj _ (holds_statedOmega_quadMinus n K p hp hn b c hirr)

end Models

end CFSG.LieType.BorelTits
