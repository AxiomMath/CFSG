module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21LModATwist

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21L

open Module Subgroup

section Base

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

structure A6Base (J : Subgroup (V ≃ₗ[ZMod 2] V)) (a : V ≃ₗ[ZMod 2] V) : Prop where
  dim : finrank (ZMod 2) V = 8
  mem : a ∈ J
  ord : orderOf a = 5
  fix : ∀ v : V, a v = v → v = 0
  iso : Nonempty (J ≃* alternatingGroup (Fin 6))

variable {J : Subgroup (V ≃ₗ[ZMod 2] V)} {a : V ≃ₗ[ZMod 2] V}

theorem modA_finite (B : A6Base J a) : Module.Finite (ZMod 2) V :=
  Module.finite_of_finrank_pos (by rw [B.dim]; norm_num)

theorem modA_finite_GL (B : A6Base J a) : Finite (V ≃ₗ[ZMod 2] V) := by
  haveI := modA_finite B
  haveI : Finite V := Module.finite_of_finite (ZMod 2)
  exact Finite.of_injective (fun e : V ≃ₗ[ZMod 2] V => (e : V → V)) DFunLike.coe_injective

theorem modA_pow_five (B : A6Base J a) : a ^ 5 = 1 := by
  rw [← B.ord]
  exact pow_orderOf_eq_one a

theorem modA_stable_dim (B : A6Base J a) {U : Submodule (ZMod 2) V}
    (hU : ∀ g ∈ J, Stable g U) :
    finrank (ZMod 2) U = 0 ∨ finrank (ZMod 2) U = 4 ∨ finrank (ZMod 2) U = 8 := by
  haveI := modA_finite B
  have hdvd := four_dvd_finrank_of_stable (modA_pow_five B) (hU a B.mem)
    (fun u _ hu => B.fix u hu)
  have hle := Submodule.finrank_le U
  rw [B.dim] at hle
  obtain ⟨k, hk⟩ := hdvd
  omega

theorem modA_stable_le_four (B : A6Base J a) {M U : Submodule (ZMod 2) V}
    (hM : finrank (ZMod 2) M = 4) (hU : ∀ g ∈ J, Stable g U) (hUM : U ≤ M) : U = ⊥ ∨ U = M := by
  haveI := modA_finite B
  have hle : finrank (ZMod 2) U ≤ 4 := hM ▸ Submodule.finrank_mono hUM
  rcases modA_stable_dim B hU with h0 | h4 | h8
  · exact Or.inl (Submodule.finrank_eq_zero.mp h0)
  · exact Or.inr (Submodule.eq_of_le_of_finrank_eq hUM (by rw [h4, hM]))
  · omega

theorem modA_exists_four (B : A6Base J a) :
    ∃ M : Submodule (ZMod 2) V, finrank (ZMod 2) M = 4 ∧ ∀ g ∈ J, Stable g M := by
  by_contra hno
  obtain ⟨e⟩ := B.iso
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by rw [B.dim]; norm_num)
  let φ : alternatingGroup (Fin 6) →* (V ≃ₗ[ZMod 2] V) := J.subtype.comp e.symm.toMonoidHom
  have hirr : ∀ U : Submodule (ZMod 2) V, (∀ g, ∀ u ∈ U, φ g u ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    have hJU : ∀ g ∈ J, Stable g U := fun g hg u hu => by
      simpa [φ] using hU (e ⟨g, hg⟩) u hu
    haveI := modA_finite B
    rcases modA_stable_dim B hJU with h0 | h4 | h8
    · exact Or.inl (Submodule.finrank_eq_zero.mp h0)
    · exact absurd ⟨U, h4, hJU⟩ hno
    · exact Or.inr (Submodule.eq_top_of_finrank_eq (by rw [h8, B.dim]))
  have := modA_finrank_irred φ hirr
  rw [B.dim] at this
  omega

end Base

section Four

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {J : Subgroup (V ≃ₗ[ZMod 2] V)} {a : V ≃ₗ[ZMod 2] V}

theorem modA_resJ_injective (B : A6Base J a) {M : Submodule (ZMod 2) V}
    (hM : finrank (ZMod 2) M = 4) (sM : ∀ g ∈ J, Stable g M) :
    Function.Injective (modA_resJ J M sM) := by
  obtain ⟨e⟩ := B.iso
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  haveI : IsSimpleGroup J := e.isSimpleGroup
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MonoidHom.ker (modA_resJ J M sM)) with h | h
  · exact h
  · exfalso
    have hker : (⟨a, B.mem⟩ : J) ∈ MonoidHom.ker (modA_resJ J M sM) := by rw [h]; trivial
    rw [MonoidHom.mem_ker] at hker
    have hz : ∀ u ∈ M, u = 0 := fun u hu => B.fix u (by
      have := congrArg (fun f : M ≃ₗ[ZMod 2] M => ((f ⟨u, hu⟩ : M) : V)) hker
      simpa [modA_resJ_apply] using this)
    have hbot : M = ⊥ := eq_bot_iff.mpr fun u hu => (Submodule.mem_bot _).mpr (hz u hu)
    rw [hbot, finrank_bot] at hM
    omega

theorem modA_faithful (B : A6Base J a)
    {M : Submodule (ZMod 2) V} (hM : finrank (ZMod 2) M = 4) (sM : ∀ g ∈ J, Stable g M) :
    ∀ g ∈ J, (∀ v ∈ M, g v = v) → g = 1 := by
  intro g hg hfix
  have hinj := modA_resJ_injective B hM sM
  have h1 : modA_resJ J M sM ⟨g, hg⟩ = modA_resJ J M sM 1 := by
    rw [map_one]
    exact LinearEquiv.ext fun u => Subtype.ext (hfix u u.2)
  exact congrArg Subtype.val (hinj h1)

theorem modA_irred (B : A6Base J a) {M : Submodule (ZMod 2) V} (hM : finrank (ZMod 2) M = 4)
    (sM : ∀ g ∈ J, Stable g M) :
    ∀ U : Submodule (ZMod 2) M, (∀ g : J, ∀ u ∈ U, modA_resJ J M sM g u ∈ U) → U = ⊥ ∨ U = ⊤ := by
  intro U hU
  have hW : ∀ g ∈ J, Stable g (U.map M.subtype) := by
    rintro g hg _ ⟨u, hu, rfl⟩
    exact ⟨modA_resJ J M sM ⟨g, hg⟩ u, hU ⟨g, hg⟩ u hu, rfl⟩
  rcases modA_stable_le_four B hM hW (Submodule.map_subtype_le M U) with h | h
  · left
    exact Submodule.map_injective_of_injective M.injective_subtype (by rw [h, Submodule.map_bot])
  · right
    exact Submodule.map_injective_of_injective M.injective_subtype
      (by rw [h, Submodule.map_subtype_top])

theorem modA_end (B : A6Base J a) {M : Submodule (ZMod 2) V}
    (hM : finrank (ZMod 2) M = 4) (sM : ∀ g ∈ J, Stable g M) (f : M →ₗ[ZMod 2] M)
    (hf : ∀ (g : J) (u : M), f (modA_resJ J M sM g u) = modA_resJ J M sM g (f u)) :
    f = 0 ∨ f = 1 := by
  obtain ⟨e⟩ := B.iso
  haveI : Nontrivial M := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  let φ : alternatingGroup (Fin 6) →* (M ≃ₗ[ZMod 2] M) :=
    (modA_resJ J M sM).comp e.symm.toMonoidHom
  have hirr : ∀ U : Submodule (ZMod 2) M, (∀ g, ∀ u ∈ U, φ g u ∈ U) → U = ⊥ ∨ U = ⊤ :=
    fun U hU => modA_irred B hM sM U fun g u hu => by simpa [φ] using hU (e g) u hu
  exact modA_end_scalar φ hirr hM f fun g u => by simpa [φ] using hf (e.symm g) u

theorem modA_cent (B : A6Base J a) {M : Submodule (ZMod 2) V}
    (hM : finrank (ZMod 2) M = 4) (sM : ∀ g ∈ J, Stable g M) (n : M ≃ₗ[ZMod 2] M)
    (hn : ∀ g : J, n * modA_resJ J M sM g = modA_resJ J M sM g * n) : n = 1 := by
  obtain ⟨e⟩ := B.iso
  exact modA_cent_trivial e (modA_resJ J M sM) hM (modA_irred B hM sM) n hn

end Four

section Twist

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {J : Subgroup (V ≃ₗ[ZMod 2] V)} {a T : V ≃ₗ[ZMod 2] V}

structure A6Twist (J : Subgroup (V ≃ₗ[ZMod 2] V)) (a T : V ≃ₗ[ZMod 2] V) : Prop where
  sq : T * T = 1
  norm : ∀ g ∈ J, T * g * T ∈ J
  comm : T * a = a * T
  nc : ¬ ∀ g ∈ J, T * g = g * T

theorem modA_T_T (Tw : A6Twist J a T) (v : V) : T (T v) = v := by
  have := congrArg (fun m : V ≃ₗ[ZMod 2] V => m v) Tw.sq
  simpa using this

@[expose] def modA_cT (Tw : A6Twist J a T) : MulAut J where
  toFun g := ⟨T * g * T, Tw.norm g g.2⟩
  invFun g := ⟨T * g * T, Tw.norm g g.2⟩
  left_inv g := Subtype.ext (by
    show T * (T * (g : V ≃ₗ[ZMod 2] V) * T) * T = g
    calc T * (T * (g : V ≃ₗ[ZMod 2] V) * T) * T = (T * T) * g * (T * T) := by
          simp only [mul_assoc]
      _ = g := by rw [Tw.sq, one_mul, mul_one])
  right_inv g := Subtype.ext (by
    show T * (T * (g : V ≃ₗ[ZMod 2] V) * T) * T = g
    calc T * (T * (g : V ≃ₗ[ZMod 2] V) * T) * T = (T * T) * g * (T * T) := by
          simp only [mul_assoc]
      _ = g := by rw [Tw.sq, one_mul, mul_one])
  map_mul' g h := Subtype.ext (by
    show T * ((g : V ≃ₗ[ZMod 2] V) * h) * T = (T * g * T) * (T * h * T)
    calc T * ((g : V ≃ₗ[ZMod 2] V) * h) * T = T * g * 1 * h * T := by simp only [mul_assoc, mul_one]
      _ = T * g * (T * T) * h * T := by rw [Tw.sq]
      _ = (T * g * T) * (T * h * T) := by simp only [mul_assoc])

theorem modA_cT_sq (Tw : A6Twist J a T) : modA_cT Tw * modA_cT Tw = 1 := by
  refine MulEquiv.ext fun g => Subtype.ext ?_
  show T * (T * (g : V ≃ₗ[ZMod 2] V) * T) * T = g
  calc T * (T * (g : V ≃ₗ[ZMod 2] V) * T) * T = (T * T) * g * (T * T) := by
        simp only [mul_assoc]
    _ = g := by rw [Tw.sq, one_mul, mul_one]

theorem modA_cT_ne_one (Tw : A6Twist J a T) : modA_cT Tw ≠ 1 := by
  intro h
  apply Tw.nc
  intro g hg
  have h1 : T * g * T = g := by
    have := congrArg (fun c : MulAut J => ((c ⟨g, hg⟩ : J) : V ≃ₗ[ZMod 2] V)) h
    exact this
  calc T * g = T * g * (T * T) := by rw [Tw.sq, mul_one]
    _ = (T * g * T) * T := by simp only [mul_assoc]
    _ = g * T := by rw [h1]

theorem modA_cT_fixes (B : A6Base J a) (Tw : A6Twist J a T) :
    ∃ y : J, orderOf y = 5 ∧ modA_cT Tw y = y := by
  refine ⟨⟨a, B.mem⟩, ?_, Subtype.ext ?_⟩
  · rw [← B.ord]
    exact (Subgroup.orderOf_coe (⟨a, B.mem⟩ : J)).symm
  · show T * a * T = a
    calc T * a * T = (a * T) * T := by rw [Tw.comm]
      _ = a := by rw [mul_assoc, Tw.sq, mul_one]

end Twist

section Hom

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {J : Subgroup (V ≃ₗ[ZMod 2] V)} {a T : V ≃ₗ[ZMod 2] V}

theorem modA_twist_zero (B : A6Base J a) (Tw : A6Twist J a T)
    {M : Submodule (ZMod 2) V} (hM : finrank (ZMod 2) M = 4) (sM : ∀ g ∈ J, Stable g M)
    (ψ : M →ₗ[ZMod 2] M)
    (hψ : ∀ (g : J) (u : M),
      ψ (modA_resJ J M sM g u) = modA_resJ J M sM (modA_cT Tw g) (ψ u)) : ψ = 0 := by
  haveI := modA_finite B
  haveI := modA_finite_GL B
  haveI : Finite J := Finite.of_injective (Subtype.val : J → V ≃ₗ[ZMod 2] V) Subtype.val_injective
  have hker : ∀ g : J, ∀ u ∈ LinearMap.ker ψ, modA_resJ J M sM g u ∈ LinearMap.ker ψ := by
    intro g u hu
    rw [LinearMap.mem_ker] at hu ⊢
    rw [hψ, hu, map_zero]
  rcases modA_irred B hM sM _ hker with h | h
  · exfalso
    obtain ⟨e⟩ := B.iso
    have hinj : Function.Injective ψ := LinearMap.ker_eq_bot.mp h
    have hsurj : Function.Surjective ψ := LinearMap.injective_iff_surjective.mp hinj
    let ψ' : M ≃ₗ[ZMod 2] M := LinearEquiv.ofBijective ψ ⟨hinj, hsurj⟩
    refine modA_no_twist e hM (modA_resJ J M sM) (modA_resJ_injective B hM sM)
      (modA_cent B hM sM) (modA_cT Tw) (modA_cT_sq Tw) (modA_cT_ne_one Tw)
      (modA_cT_fixes B Tw) ψ' fun g => ?_
    refine LinearEquiv.ext fun w => ?_
    have h1 := hψ g (ψ'.symm w)
    have h2 : ψ (ψ'.symm w) = w := ψ'.apply_symm_apply w
    rw [h2] at h1
    show _ = ψ' (modA_resJ J M sM g (ψ'.symm w))
    exact h1.symm
  · exact LinearMap.ker_eq_top.mp h

theorem modA_stable_map (Tw : A6Twist J a T) {M : Submodule (ZMod 2) V}
    (sM : ∀ g ∈ J, Stable g M) : ∀ g ∈ J, Stable g (M.map (T : V →ₗ[ZMod 2] V)) := by
  rintro g hg _ ⟨u, hu, rfl⟩
  refine ⟨(T * g * T) u, sM _ (Tw.norm g hg) u hu, ?_⟩
  show T (T (g (T u))) = g (T u)
  exact modA_T_T Tw _

theorem modA_hom12 (B : A6Base J a) (Tw : A6Twist J a T)
    {M : Submodule (ZMod 2) V} (hM : finrank (ZMod 2) M = 4) (sM : ∀ g ∈ J, Stable g M)
    (f : V →ₗ[ZMod 2] V) (hf : ∀ g ∈ J, ∀ v, f (g v) = g (f v))
    (hf12 : ∀ v ∈ M, f v ∈ M.map (T : V →ₗ[ZMod 2] V)) : ∀ v ∈ M, f v = 0 := by
  have hmem : ∀ v ∈ M, T (f v) ∈ M := by
    intro v hv
    obtain ⟨m, hm, hfm⟩ := hf12 v hv
    have : T (f v) = m := by
      rw [← hfm]
      exact modA_T_T Tw m
    rw [this]
    exact hm
  let ψ : M →ₗ[ZMod 2] M := (T.toLinearMap ∘ₗ f).restrict hmem
  have hψ : ∀ (g : J) (u : M),
      ψ (modA_resJ J M sM g u) = modA_resJ J M sM (modA_cT Tw g) (ψ u) := by
    intro g u
    refine Subtype.ext ?_
    show T (f ((g : V ≃ₗ[ZMod 2] V) (u : V))) =
      (T * (g : V ≃ₗ[ZMod 2] V) * T) (T (f (u : V)))
    rw [hf g g.2 u]
    show _ = T ((g : V ≃ₗ[ZMod 2] V) (T (T (f (u : V)))))
    rw [modA_T_T Tw]
  have h0 := modA_twist_zero B Tw hM sM ψ hψ
  intro v hv
  have h1 := congrArg (fun φ : M →ₗ[ZMod 2] M => ((φ ⟨v, hv⟩ : M) : V)) h0
  have h2 : T (f v) = 0 := h1
  have h3 := congrArg T h2
  rwa [modA_T_T Tw, map_zero] at h3

theorem modA_hom21 (B : A6Base J a) (Tw : A6Twist J a T)
    {M : Submodule (ZMod 2) V} (hM : finrank (ZMod 2) M = 4) (sM : ∀ g ∈ J, Stable g M)
    (f : V →ₗ[ZMod 2] V) (hf : ∀ g ∈ J, ∀ v, f (g v) = g (f v))
    (hf21 : ∀ v ∈ M.map (T : V →ₗ[ZMod 2] V), f v ∈ M) :
    ∀ v ∈ M.map (T : V →ₗ[ZMod 2] V), f v = 0 := by
  have hmem : ∀ v ∈ M, f (T v) ∈ M := fun v hv => hf21 _ ⟨v, hv, rfl⟩
  let ψ : M →ₗ[ZMod 2] M := (f ∘ₗ T.toLinearMap).restrict hmem
  have hψ : ∀ (g : J) (u : M),
      ψ (modA_resJ J M sM g u) = modA_resJ J M sM (modA_cT Tw g) (ψ u) := by
    intro g u
    refine Subtype.ext ?_
    show f (T ((g : V ≃ₗ[ZMod 2] V) (u : V))) =
      (T * (g : V ≃ₗ[ZMod 2] V) * T) (f (T (u : V)))
    rw [← hf (T * g * T) (Tw.norm g g.2) (T u)]
    show _ = f (T ((g : V ≃ₗ[ZMod 2] V) (T (T (u : V)))))
    rw [modA_T_T Tw]
  have h0 := modA_twist_zero B Tw hM sM ψ hψ
  rintro _ ⟨u, hu, rfl⟩
  have h1 := congrArg (fun φ : M →ₗ[ZMod 2] M => ((φ ⟨u, hu⟩ : M) : V)) h0
  exact h1

end Hom

section Decomp

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {J : Subgroup (V ≃ₗ[ZMod 2] V)} {a T : V ≃ₗ[ZMod 2] V}

theorem modA_finrank_map {M : Submodule (ZMod 2) V}
    (hM : finrank (ZMod 2) M = 4) (g : V ≃ₗ[ZMod 2] V) :
    finrank (ZMod 2) (M.map (g : V →ₗ[ZMod 2] V)) = 4 :=
  (LinearEquiv.finrank_map_eq g M).trans hM

theorem modA_inf_eq_bot (B : A6Base J a) (Tw : A6Twist J a T)
    {M : Submodule (ZMod 2) V} (hM : finrank (ZMod 2) M = 4) (sM : ∀ g ∈ J, Stable g M) :
    M ⊓ M.map (T : V →ₗ[ZMod 2] V) = ⊥ := by
  have hst : ∀ g ∈ J, Stable g (M ⊓ M.map (T : V →ₗ[ZMod 2] V)) := fun g hg u hu =>
    ⟨sM g hg u hu.1, modA_stable_map Tw sM g hg u hu.2⟩
  rcases modA_stable_le_four B hM hst inf_le_left with h | h
  · exact h
  · exfalso
    have hle : ∀ v ∈ M, v ∈ M.map (T : V →ₗ[ZMod 2] V) := fun v hv => by
      have : v ∈ M ⊓ M.map (T : V →ₗ[ZMod 2] V) := by rw [h]; exact hv
      exact this.2
    have h0 := modA_hom12 B Tw hM sM LinearMap.id (fun g _ v => rfl) hle
    have hbot : M = ⊥ := eq_bot_iff.mpr fun v hv => (Submodule.mem_bot _).mpr (h0 v hv)
    rw [hbot, finrank_bot] at hM
    omega

theorem modA_isCompl (B : A6Base J a) (Tw : A6Twist J a T)
    {M : Submodule (ZMod 2) V} (hM : finrank (ZMod 2) M = 4) (sM : ∀ g ∈ J, Stable g M) :
    IsCompl M (M.map (T : V →ₗ[ZMod 2] V)) := by
  haveI := modA_finite B
  have hinf := modA_inf_eq_bot B Tw hM sM
  have hd := modA_finrank_map hM T
  have hsup : M ⊔ M.map (T : V →ₗ[ZMod 2] V) = ⊤ := by
    have := Submodule.finrank_sup_add_finrank_inf_eq M (M.map (T : V →ₗ[ZMod 2] V))
    rw [hinf, finrank_bot, hM, hd] at this
    exact Submodule.eq_top_of_finrank_eq (by rw [B.dim]; omega)
  exact ⟨disjoint_iff.mpr hinf, codisjoint_iff.mpr hsup⟩

theorem modA_exists_proj {M N : Submodule (ZMod 2) V} (hc : IsCompl M N) :
    ∃ p : V →ₗ[ZMod 2] V, (∀ v, p v ∈ M) ∧ (∀ v, p v = 0 → v ∈ N) ∧
      ∀ g : V ≃ₗ[ZMod 2] V, Stable g M → Stable g N → ∀ v, p (g v) = g (p v) := by
  have hpm : ∀ m ∈ M, M.projection N hc m = m := fun m hm =>
    Submodule.projection_apply_of_mem_left hc hm
  have hpn : ∀ n ∈ N, M.projection N hc n = 0 := fun n hn =>
    Submodule.projection_apply_of_mem_right hc hn
  refine ⟨M.projection N hc, fun v => Submodule.projection_apply_mem hc v,
    fun v hv => (Submodule.projection_apply_eq_zero_iff hc).mp hv, ?_⟩
  intro g hgM hgN v
  have hv : v ∈ M ⊔ N := by rw [hc.sup_eq_top]; trivial
  obtain ⟨m, hm, n, hn, rfl⟩ := Submodule.mem_sup.mp hv
  have e1 : M.projection N hc (g m) = g m := hpm _ (hgM m hm)
  have e2 : M.projection N hc (g n) = 0 := hpn _ (hgN n hn)
  have e3 := hpm m hm
  have e4 := hpn n hn
  simp only [map_add, e1, e2, e3, e4, map_zero, add_zero]

theorem modA_four_eq (B : A6Base J a) (Tw : A6Twist J a T)
    {M : Submodule (ZMod 2) V} (hM : finrank (ZMod 2) M = 4) (sM : ∀ g ∈ J, Stable g M)
    {U : Submodule (ZMod 2) V} (hU : ∀ g ∈ J, Stable g U) (hd : finrank (ZMod 2) U = 4) :
    U = M ∨ U = M.map (T : V →ₗ[ZMod 2] V) := by
  haveI := modA_finite B
  by_contra hcon
  push Not at hcon
  obtain ⟨hne1, hne2⟩ := hcon
  have hUM : U ⊓ M = ⊥ := by
    have hst : ∀ g ∈ J, Stable g (U ⊓ M) := fun g hg u hu =>
      ⟨hU g hg u hu.1, sM g hg u hu.2⟩
    rcases modA_stable_le_four B hM hst inf_le_right with h | h
    · exact h
    · exfalso
      have hMU : M ≤ U := fun v hv => by
        have : v ∈ U ⊓ M := by rw [h]; exact hv
        exact this.1
      exact hne1 (Submodule.eq_of_le_of_finrank_eq hMU (by rw [hd, hM])).symm
  have hMU' : M ⊓ U = ⊥ := by rw [inf_comm]; exact hUM
  have hc : IsCompl M U := by
    refine ⟨disjoint_iff.mpr hMU', codisjoint_iff.mpr ?_⟩
    have := Submodule.finrank_sup_add_finrank_inf_eq M U
    rw [hMU', finrank_bot, hM, hd] at this
    exact Submodule.eq_top_of_finrank_eq (by rw [B.dim]; omega)
  obtain ⟨p, hp1, hp2, hp3⟩ := modA_exists_proj hc
  have h0 := modA_hom21 B Tw hM sM p (fun g hg v => hp3 g (sM g hg) (hU g hg) v)
    (fun v _ => hp1 v)
  have hle : M.map (T : V →ₗ[ZMod 2] V) ≤ U := fun v hv => hp2 v (h0 v hv)
  exact hne2 (Submodule.eq_of_le_of_finrank_eq hle
    (by rw [hd, modA_finrank_map hM T])).symm

theorem modA_classify (B : A6Base J a) (Tw : A6Twist J a T)
    {M : Submodule (ZMod 2) V} (hM : finrank (ZMod 2) M = 4) (sM : ∀ g ∈ J, Stable g M)
    {U : Submodule (ZMod 2) V} (hU : ∀ g ∈ J, Stable g U) :
    U = ⊥ ∨ U = M ∨ U = M.map (T : V →ₗ[ZMod 2] V) ∨ U = ⊤ := by
  haveI := modA_finite B
  rcases modA_stable_dim B hU with h0 | h4 | h8
  · exact Or.inl (Submodule.finrank_eq_zero.mp h0)
  · rcases modA_four_eq B Tw hM sM hU h4 with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Submodule.eq_top_of_finrank_eq (by rw [h8, B.dim]))))

theorem modA_comm_eq_id (B : A6Base J a)
    {M : Submodule (ZMod 2) V} (hM : finrank (ZMod 2) M = 4) (sM : ∀ g ∈ J, Stable g M)
    {n : V ≃ₗ[ZMod 2] V} (hf : ∀ g ∈ J, ∀ v, n (g v) = g (n v)) (hnM : ∀ v ∈ M, n v ∈ M) :
    ∀ v ∈ M, n v = v := by
  let f₁ : M →ₗ[ZMod 2] M := (n : V →ₗ[ZMod 2] V).restrict hnM
  have hf₁ : ∀ (g : J) (u : M),
      f₁ (modA_resJ J M sM g u) = modA_resJ J M sM g (f₁ u) := fun g u =>
    Subtype.ext (hf g g.2 u)
  rcases modA_end B hM sM f₁ hf₁ with h | h
  · exfalso
    have hbot : M = ⊥ := eq_bot_iff.mpr fun v hv => by
      rw [Submodule.mem_bot]
      have h1 : n v = 0 := congrArg (fun φ : M →ₗ[ZMod 2] M => ((φ ⟨v, hv⟩ : M) : V)) h
      exact n.injective (by rw [h1, map_zero])
    rw [hbot, finrank_bot] at hM
    omega
  · intro v hv
    exact congrArg (fun φ : M →ₗ[ZMod 2] M => ((φ ⟨v, hv⟩ : M) : V)) h

theorem modA_centralizer (B : A6Base J a) (Tw : A6Twist J a T)
    {M : Submodule (ZMod 2) V} (hM : finrank (ZMod 2) M = 4) (sM : ∀ g ∈ J, Stable g M) :
    centralizer (J : Set (V ≃ₗ[ZMod 2] V)) = ⊥ := by
  have sM2 := modA_stable_map Tw sM
  have hM2 := modA_finrank_map hM T
  have hc := modA_isCompl B Tw hM sM
  refine eq_bot_iff.mpr fun n hn => ?_
  rw [Subgroup.mem_bot]
  have hf : ∀ g ∈ J, ∀ v, n (g v) = g (n v) := fun g hg v => by
    have h1 := mem_centralizer_iff.mp hn g hg
    exact (congrArg (fun m : V ≃ₗ[ZMod 2] V => m v) h1).symm
  have hst : ∀ {U : Submodule (ZMod 2) V}, (∀ g ∈ J, Stable g U) →
      ∀ g ∈ J, Stable g (U.map (n : V →ₗ[ZMod 2] V)) := by
    intro U hU g hg _ ⟨u, hu, hv⟩
    exact ⟨g u, hU g hg u hu, by rw [← hv]; exact hf g hg u⟩
  have e1 : M.map (n : V →ₗ[ZMod 2] V) = M := by
    rcases modA_four_eq B Tw hM sM (hst sM) (modA_finrank_map hM n) with h | h
    · exact h
    · exfalso
      have h0 := modA_hom12 B Tw hM sM n hf (fun v hv => h ▸ ⟨v, hv, rfl⟩)
      have hbot : M = ⊥ := eq_bot_iff.mpr fun v hv => by
        rw [Submodule.mem_bot]
        have h1 : n v = 0 := h0 v hv
        exact n.injective (by rw [h1, map_zero])
      rw [hbot, finrank_bot] at hM
      omega
  have e2 : (M.map (T : V →ₗ[ZMod 2] V)).map (n : V →ₗ[ZMod 2] V) =
      M.map (T : V →ₗ[ZMod 2] V) := by
    rcases modA_four_eq B Tw hM sM (hst sM2) (modA_finrank_map hM2 n) with h | h
    · exfalso
      have h0 := modA_hom21 B Tw hM sM n hf (fun v hv => h ▸ ⟨v, hv, rfl⟩)
      have hbot : M.map (T : V →ₗ[ZMod 2] V) = ⊥ := eq_bot_iff.mpr fun v hv => by
        rw [Submodule.mem_bot]
        have h1 : n v = 0 := h0 v hv
        exact n.injective (by rw [h1, map_zero])
      rw [hbot, finrank_bot] at hM2
      omega
    · exact h
  have s1 : ∀ v ∈ M, n v = v :=
    modA_comm_eq_id B hM sM hf fun v hv => e1 ▸ ⟨v, hv, rfl⟩
  have s2 : ∀ v ∈ M.map (T : V →ₗ[ZMod 2] V), n v = v := by
    have hM2' : finrank (ZMod 2) (M.map (T : V →ₗ[ZMod 2] V)) = 4 := hM2
    exact modA_comm_eq_id B hM2' (fun g hg => sM2 g hg) hf fun v hv => e2 ▸ ⟨v, hv, rfl⟩
  refine LinearEquiv.ext fun v => ?_
  have hv : v ∈ M ⊔ M.map (T : V →ₗ[ZMod 2] V) := by rw [hc.sup_eq_top]; trivial
  obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add, s1 m₁ hm₁, s2 m₂ hm₂]
  rfl

theorem modA_perm (B : A6Base J a) (Tw : A6Twist J a T)
    {M : Submodule (ZMod 2) V} (hM : finrank (ZMod 2) M = 4) (sM : ∀ g ∈ J, Stable g M)
    {n : V ≃ₗ[ZMod 2] V} (hn : ∀ g ∈ J, n⁻¹ * g * n ∈ J) :
    (M.map (n : V →ₗ[ZMod 2] V) = M ∧
        (M.map (T : V →ₗ[ZMod 2] V)).map (n : V →ₗ[ZMod 2] V) = M.map (T : V →ₗ[ZMod 2] V)) ∨
      (M.map (n : V →ₗ[ZMod 2] V) = M.map (T : V →ₗ[ZMod 2] V) ∧
        (M.map (T : V →ₗ[ZMod 2] V)).map (n : V →ₗ[ZMod 2] V) = M) := by
  have sM2 := modA_stable_map Tw sM
  have hM2 := modA_finrank_map hM T
  have hst : ∀ {U : Submodule (ZMod 2) V}, (∀ g ∈ J, Stable g U) →
      ∀ g ∈ J, Stable g (U.map (n : V →ₗ[ZMod 2] V)) := by
    intro U hU g hg _ ⟨u, hu, hv⟩
    refine ⟨(n⁻¹ * g * n) u, hU _ (hn g hg) u hu, ?_⟩
    rw [← hv]
    simp [LinearEquiv.mul_apply]
  have hne : M ≠ M.map (T : V →ₗ[ZMod 2] V) := by
    intro h
    have h1 := modA_inf_eq_bot B Tw hM sM
    rw [← h, inf_idem] at h1
    rw [h1, finrank_bot] at hM
    omega
  have hinj : Function.Injective (Submodule.map (n : V →ₗ[ZMod 2] V)) :=
    Submodule.map_injective_of_injective n.injective
  rcases modA_four_eq B Tw hM sM (hst sM) (modA_finrank_map hM n) with e1 | e1 <;>
    rcases modA_four_eq B Tw hM sM (hst sM2) (modA_finrank_map hM2 n) with e2 | e2
  · exact absurd (hinj (e2.trans e1.symm)).symm hne
  · exact Or.inl ⟨e1, e2⟩
  · exact Or.inr ⟨e1, e2⟩
  · exact absurd (hinj (e1.trans e2.symm)) hne

end Decomp

end CFSG.LocalAnalysis.EvenBN.Tits.I21L
