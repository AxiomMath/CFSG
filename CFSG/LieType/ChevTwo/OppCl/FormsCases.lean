module

public import CFSG.LieType.ChevTwo.OppCl.Defs
import CFSG.LieType.ChevTwo.OppCl.FormsCasesCtx
import CFSG.LieType.ChevTwo.OppCl.FormsCasesGR
import CFSG.LieType.ChevTwo.OppCl.FormsCasesGL
import CFSG.LieType.ChevTwo.OppCl.FormsCasesMR
import CFSG.LieType.ChevTwo.OppCl.FormsCasesML
import CFSG.LieType.ChevTwo.OppCl.FormsCasesZ
import CFSG.LieType.ChevTwo.OppCl.FormsCasesZD

public section

namespace CFSG.LieType.ChevTwo.OppCl

open CFSG.LieType.BorelTits

section Cases

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [Finite V] {H : Type} [Group H]

variable {Φ : ReflForm F V} {Sing : V → Prop} {TS : Submodule F V → Prop}
  {ρ : H →* Module.End F V} {p : ℕ} [Fact p.Prime]
  {Rh : Subgroup (Equiv.Perm V)} {X : ℕ → Submodule F V} {m : ℕ} {M W' : Submodule F V}

theorem caseM_swap (hp2 : p ≠ 2) (C : RaiseCtx Φ Sing TS ρ p Rh X m M W') (x : H)
    (hx : x ∈ flagKernel ρ (isoCompletion Φ X m)) (hxc : CommR ρ Rh x)
    (hM : ∃ y ∈ M, ρ x y ≠ y) :
    ∃ a : V →ₗ[F] V, (∀ r ∈ Rh, ∀ v, r (a v) = a (r v)) ∧ (∀ v, a v ∈ M) ∧
      (∀ v ∈ M ⊔ W', a v = 0) ∧ ∃ w ∈ X m, a w ≠ 0 := by
  obtain ⟨y, hyM, hy⟩ := hM
  exact exists_equivariant_swap p hp2 Rh C.hs C.hR M (X m) (M ⊔ W') C.hMinv
    (fun r hr v hv => C.hXinv r hr m v hv) (FormsCases.ctx_sup_inv C)
    (FormsCases.ctx_disj C).symm (ρ x - 1) (FormsCases.comm_sub_one hxc C.hs)
    (fun v hv => by simpa using FormsCases.fk_mid hx (FormsCases.ctx_M_le_perp C hv))
    ⟨y, hyM, sub_ne_zero.mpr hy⟩

theorem realize_mid (C : RaiseCtx Φ Sing TS ρ p Rh X m M W') (a : V →ₗ[F] V) (ha : ∀ v, a v ∈ M)
    (ha0 : ∀ v ∈ M ⊔ W', a v = 0) :
    ∃ u ∈ Urad Φ ρ W', ∀ w ∈ X m, ρ u w - w - a w ∈ W' :=
  FormsCases.realize_mid_core C a ha ha0

theorem lift_mid (hp2 : p ≠ 2) (C : RaiseCtx Φ Sing TS ρ p Rh X m M W') (a : V →ₗ[F] V)
    (hac : ∀ r ∈ Rh, ∀ v, r (a v) = a (r v)) (u₀ : H) (hu₀ : u₀ ∈ Urad Φ ρ W')
    (hlead : ∀ w ∈ X m, ρ u₀ w - w - a w ∈ W') :
    ∃ y ∈ Urad Φ ρ W', CommR ρ Rh y ∧ ∀ w ∈ X m, ρ y w - w - a w ∈ W' :=
  FormsCases.lift_mid_core hp2 C a hac u₀ hu₀ hlead

theorem caseG_raise (hp2 : p ≠ 2) (C : RaiseCtx Φ Sing TS ρ p Rh X m M W') (x : H)
    (hx : x ∈ flagKernel ρ (isoCompletion Φ X m)) (hxc : CommR ρ Rh x)
    (hG : ∃ w ∈ X m, ρ x w ≠ w) :
    ∃ (g : V →ₗ[F] V) (k : ℕ), (∀ r ∈ Rh, ∀ v, r (g v) = g (r v)) ∧ (∀ v, g (g v) = 0) ∧
      (∀ v, g v ∈ X m) ∧ (∀ v ∈ M ⊔ W', g v = 0) ∧ ∃ v ∈ X k, g v ∉ X k := by
  obtain ⟨w, hw, hρw⟩ := hG
  have hN : ∀ k, ∀ v ∈ X (min (k + 1) m), (ρ x - 1) v ∈ X (min k m) := by
    intro k v hv
    simp only [LinearMap.sub_apply, Module.End.one_apply]
    by_cases hk : k < m
    · rw [min_eq_left (by omega : k + 1 ≤ m)] at hv
      rw [min_eq_left hk.le]
      exact FormsCases.fk_low hx hk hv
    · push_neg at hk
      rw [min_eq_right (by omega : m ≤ k + 1)] at hv
      rw [min_eq_right hk]
      exact sub_mem (FormsCases.fs_apply (flagKernel_le_flagStab ρ _ hx) le_rfl hv) hv
  obtain ⟨g, k, hgc, hg2, hgW, hgD, v, hv, hgv⟩ := exists_raising p hp2 Rh C.hs C.hR
    (fun k => X (min k m)) (by simpa using C.hX0)
    (fun a b hab => C.hXmono (min_le_min_right m hab))
    (fun r hr k v hv => C.hXinv r hr (min k m) v hv) (X m) (M ⊔ W')
    (fun k => C.hXmono (min_le_right k m)) (FormsCases.ctx_sup_inv C) (FormsCases.ctx_disj C)
    (ρ x - 1) hN (FormsCases.comm_sub_one hxc C.hs)
    ⟨m, w, by simpa using hw, by simpa using sub_ne_zero.mpr hρw⟩
  exact ⟨g, min k m, hgc, hg2, hgW, hgD, v, hv, hgv⟩

theorem realize_levi (C : RaiseCtx Φ Sing TS ρ p Rh X m M W') (g : V →ₗ[F] V)
    (hg2 : ∀ v, g (g v) = 0) (hgW : ∀ v, g v ∈ X m) (hgD : ∀ v ∈ M ⊔ W', g v = 0) :
    ∃ u : H, LevProp Φ ρ (X m) g u := FormsCases.realize_levi_core C g hg2 hgW hgD

theorem lift_levi (hp2 : p ≠ 2) (C : RaiseCtx Φ Sing TS ρ p Rh X m M W') (g : V →ₗ[F] V)
    (hgc : ∀ r ∈ Rh, ∀ v, r (g v) = g (r v)) (u₀ : H) (hu₀ : LevProp Φ ρ (X m) g u₀) :
    ∃ y : H, CommR ρ Rh y ∧ LevProp Φ ρ (X m) g y :=
  FormsCases.lift_levi_core hp2 C g hgc u₀ hu₀

theorem caseZ_dual (hp2 : p ≠ 2) (C : RaiseCtx Φ Sing TS ρ p Rh X m M W')
    (hZtype : EA2 Φ Sing ρ ∨
      ∀ (h : H) (w : V), Sing (ρ h w - w) → Φ.β w (ρ h w - w) = 0)
    (x : H) (hx : x ∈ flagKernel ρ (isoCompletion Φ X m)) (hxc : CommR ρ Rh x)
    (hZ : (∀ w ∈ X m, ρ x w = w) ∧ (∀ y ∈ M, ρ x y = y) ∧ ∃ w ∈ W', ρ x w ≠ w) :
    ∃ c : V →ₗ[F] V, (∀ r ∈ Rh, ∀ v, r (c v) = c (r v)) ∧ (∀ v, c v ∈ W') ∧
      (∀ v ∈ M ⊔ W', c v = 0) ∧ (∀ u v, Φ.β (c u) v = Φ.β u (c v)) ∧ (∃ w ∈ X m, c w ≠ 0) ∧
      (EA2 Φ Sing ρ ∨ ∀ u, Φ.β u (c u) = 0) :=
  FormsCases.caseZ_dual_core hp2 C hZtype x hx hxc hZ

theorem realize_siegel (C : RaiseCtx Φ Sing TS ρ p Rh X m M W') (c : V →ₗ[F] V)
    (hcW' : ∀ v, c v ∈ W') (hc0 : ∀ v ∈ M ⊔ W', c v = 0) (hsa : ∀ u v, Φ.β (c u) v = Φ.β u (c v))
    (hdiag : EA2 Φ Sing ρ ∨ ∀ u, Φ.β u (c u) = 0) :
    ∃ u : H, ∀ v, ρ u v = v + c v := FormsCases.realize_siegel_core C c hcW' hc0 hsa hdiag

theorem trichotomy (C : RaiseCtx Φ Sing TS ρ p Rh X m M W') (x : H) (hx1 : x ≠ 1) :
    (∃ w ∈ X m, ρ x w ≠ w) ∨ (∃ y ∈ M, ρ x y ≠ y) ∨
      ((∀ w ∈ X m, ρ x w = w) ∧ (∀ y ∈ M, ρ x y = y) ∧ ∃ w ∈ W', ρ x w ≠ w) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  have h3' := h3 h1 h2
  apply hx1
  apply C.hinj
  ext v
  obtain ⟨w, hw, μ, hμ, w', hw', rfl⟩ : ∃ w ∈ X m, ∃ μ ∈ M, ∃ w' ∈ W', v = w + μ + w' := by
    have hv : v ∈ X m ⊔ M ⊔ W' := by rw [C.hsplit.sup_eq]; exact Submodule.mem_top
    obtain ⟨a, ha, w', hw', rfl⟩ := Submodule.mem_sup.mp hv
    obtain ⟨w, hw, μ, hμ, rfl⟩ := Submodule.mem_sup.mp ha
    exact ⟨w, hw, μ, hμ, w', hw', rfl⟩
  simp [map_add, h1 w hw, h2 μ hμ, h3' w' hw']

theorem caseG (hp2 : p ≠ 2) (C : RaiseCtx Φ Sing TS ρ p Rh X m M W') (x : H)
    (hx : x ∈ flagKernel ρ (isoCompletion Φ X m)) (hxc : CommR ρ Rh x)
    (hG : ∃ w ∈ X m, ρ x w ≠ w) :
    ∃ y : H, CommR ρ Rh y ∧ y ∉ flagStab ρ (isoCompletion Φ X m) := by
  obtain ⟨g, k, hgc, hg2, hgW, hgD, v, hv, hgv⟩ := caseG_raise hp2 C x hx hxc hG
  obtain ⟨u, hu⟩ := realize_levi C g hg2 hgW hgD
  obtain ⟨y, hyc, hyL⟩ := lift_levi hp2 C g hgc u hu
  refine ⟨y, hyc, fun hy => ?_⟩
  have hkm : k < m := by
    by_contra hkm
    push_neg at hkm
    exact hgv (C.hXmono hkm (hgW v))
  have h1 : ρ y v ∈ X k := FormsCases.fs_apply hy hkm.le hv
  rw [hyL.1 v (C.hXmono hkm.le hv)] at h1
  exact hgv (by simpa using sub_mem h1 hv)

theorem caseM (hp2 : p ≠ 2) (C : RaiseCtx Φ Sing TS ρ p Rh X m M W') (x : H)
    (hx : x ∈ flagKernel ρ (isoCompletion Φ X m)) (hxc : CommR ρ Rh x)
    (hM : ∃ y ∈ M, ρ x y ≠ y) :
    ∃ y : H, CommR ρ Rh y ∧ y ∉ flagStab ρ (isoCompletion Φ X m) := by
  obtain ⟨a, hac, haM, haD, w, hw, haw⟩ := caseM_swap hp2 C x hx hxc hM
  obtain ⟨u₀, hu₀, hlead⟩ := realize_mid C a haM haD
  obtain ⟨y, -, hyc, hylead⟩ := lift_mid hp2 C a hac u₀ hu₀ hlead
  refine ⟨y, hyc, fun hy => ?_⟩
  have h1 : ρ y w ∈ X m := FormsCases.fs_apply hy le_rfl hw
  have h2 := hylead w hw
  have h3 : a w + (ρ y w - w - a w) ∈ X m := by
    have := sub_mem h1 hw
    convert this using 1
    abel
  have h4 : a w + (ρ y w - w - a w) ∈ M ⊔ W' :=
    add_mem (Submodule.mem_sup_left (haM w)) (Submodule.mem_sup_right h2)
  have h5 : a w + (ρ y w - w - a w) = 0 :=
    Submodule.disjoint_def.mp (FormsCases.ctx_disj C) _ h3 h4
  have h7 : a w ∈ W' := by
    have : a w = -(ρ y w - w - a w) := eq_neg_of_add_eq_zero_left h5
    rw [this]
    exact neg_mem h2
  exact haw (Submodule.disjoint_def.mp C.hsplit.disj_M _ (haM w) h7)

theorem caseZ (hp2 : p ≠ 2) (C : RaiseCtx Φ Sing TS ρ p Rh X m M W')
    (hZtype : EA2 Φ Sing ρ ∨
      ∀ (h : H) (w : V), Sing (ρ h w - w) → Φ.β w (ρ h w - w) = 0)
    (x : H) (hx : x ∈ flagKernel ρ (isoCompletion Φ X m)) (hxc : CommR ρ Rh x)
    (hZ : (∀ w ∈ X m, ρ x w = w) ∧ (∀ y ∈ M, ρ x y = y) ∧ ∃ w ∈ W', ρ x w ≠ w) :
    ∃ y : H, CommR ρ Rh y ∧ y ∉ flagStab ρ (isoCompletion Φ X m) := by
  obtain ⟨c, hcc, hcW', hc0, hsa, ⟨w, hw, hcw⟩, hdiag⟩ := caseZ_dual hp2 C hZtype x hx hxc hZ
  obtain ⟨u, hu⟩ := realize_siegel C c hcW' hc0 hsa hdiag
  refine ⟨u, fun r hr v => ?_, fun hy => ?_⟩
  · rw [hu, hu, (C.hs hr).1, hcc r hr v]
  · have h1 : ρ u w ∈ X m := FormsCases.fs_apply hy le_rfl hw
    rw [hu] at h1
    have h2 : c w ∈ X m := by simpa using sub_mem h1 hw
    exact hcw (Submodule.disjoint_def.mp (FormsCases.ctx_disj' C) _ h2 (hcW' w))

end Cases

section Forms3

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [Finite V] {H : Type} [Group H]
variable (Φ : ReflForm F V) (Sing : V → Prop) (TS : Submodule F V → Prop)
  (ρ : H →* Module.End F V) (p : ℕ) [Fact p.Prime]

theorem raise_form (P : Equiv.Perm V → Prop) (hP : ∀ r, P r → SemiIso Φ r)
    (hσ : ∀ c, Φ.σ (Φ.σ c) = c) (hsymm : ∀ u v, Φ.β v u = Φ.σ (Φ.β u v))
    (hSing : ∀ v, Sing v → Φ.β v v = 0) (hTS : ∀ U, TS U → Φ.IsTotallyIsotropic U)
    (hTSsing : ∀ U, TS U → ∀ v ∈ U, Sing v) (hρ : IsIsometric Φ ρ)
    (hinj : Function.Injective ρ) (hE0 : EA0 Φ Sing ρ) (hE1 : EA1 Φ Sing ρ)
    (hZtype : EA2 Φ Sing ρ ∨
      ∀ (h : H) (w : V), Sing (ρ h w - w) → Φ.β w (ρ h w - w) = 0)
    (hsplit : ∀ Rh : Subgroup (Equiv.Perm V), Rh ≤ semilinGroup F V → (∀ r ∈ Rh, P r) →
      IsPGroup p Rh → ∀ W : Submodule F V, TS W → (∀ r ∈ Rh, ∀ v ∈ W, r v ∈ W) →
        ∃ M W' : Submodule F V, Split3 Φ TS W M W' ∧ (∀ r ∈ Rh, ∀ v ∈ M, r v ∈ M) ∧
          (∀ r ∈ Rh, ∀ v ∈ W', r v ∈ W'))
    (𝔉 : Subgroup H → ℕ → Submodule F V)
    (hflag : ∀ Q : Subgroup H, IsPGroup 2 Q → ∃ (X : ℕ → Submodule F V) (m : ℕ), X 0 = ⊥ ∧
      Monotone X ∧ (∀ k, TS (X k)) ∧ 𝔉 Q = isoCompletion Φ X m)
    (hinvF : ∀ Q : Subgroup H, IsPGroup 2 Q → ∀ r : Equiv.Perm V, r ∈ semilinGroup F V →
      P r → NormQ ρ r Q → NormQ ρ r⁻¹ Q → ∀ k, ∀ v ∈ 𝔉 Q k, r v ∈ 𝔉 Q k)
    (hp2 : p ≠ 2) : RaiseProp P ρ 𝔉 p := by
  intro Rh hs hPR hRp hN Q hQ hNQ x hx hx1 hxc
  obtain ⟨X, m, hX0, hmono, hts, hF⟩ := hflag Q hQ
  set X' : ℕ → Submodule F V := fun k => X (min k m) with hX'
  have hcomp : isoCompletion Φ X' m = isoCompletion Φ X m := by
    funext k
    unfold isoCompletion
    split_ifs with h1 h2
    · simp only [hX', min_eq_left h1]
    · simp only [hX', min_eq_left (by omega : 2 * m + 1 - k ≤ m)]
    · rfl
  have hX'0 : X' 0 = ⊥ := by simpa [hX'] using hX0
  have hX'mono : Monotone X' := fun a b hab => hmono (min_le_min_right m hab)
  have hX'ts : ∀ k, TS (X' k) := fun k => hts _
  have hinv : ∀ r ∈ Rh, ∀ k, ∀ v ∈ X' k, r v ∈ X' k := by
    intro r hr k v hv
    have h := hinvF Q hQ r (hs hr) (hPR r hr) (hNQ r hr) (hNQ r⁻¹ (inv_mem hr))
    have hk : min k m ≤ m := min_le_right k m
    have hv' : v ∈ 𝔉 Q (min k m) := by rw [hF, isoCompletion_of_le hk]; exact hv
    have := h (min k m) v hv'
    rw [hF, isoCompletion_of_le hk] at this
    exact this
  obtain ⟨M, W', hS, hMinv, hW'inv⟩ := hsplit Rh hs hPR hRp (X' m) (hX'ts m)
    (fun r hr v hv => hinv r hr m v hv)
  have C : RaiseCtx Φ Sing TS ρ p Rh X' m M W' :=
    { hσ := hσ, hsymm := hsymm, hSing := hSing, hTS := hTS, hTSsing := hTSsing, hρ := hρ,
      hinj := hinj, hE0 := hE0, hE1 := hE1, hs := hs, hiso := fun r hr => hP r (hPR r hr),
      hR := hRp, hN := hN, hX0 := hX'0, hXmono := hX'mono, hXts := hX'ts, hXinv := hinv,
      hsplit := hS, hMinv := hMinv, hW'inv := hW'inv }
  have hx' : x ∈ flagKernel ρ (isoCompletion Φ X' m) := by rw [hcomp, ← hF]; exact hx
  rw [hF, ← hcomp]
  rcases trichotomy C x hx1 with hG | hM | hZ
  · exact caseG hp2 C x hx' hxc hG
  · exact caseM hp2 C x hx' hxc hM
  · exact caseZ hp2 C hZtype x hx' hxc hZ

end Forms3

end CFSG.LieType.ChevTwo.OppCl
