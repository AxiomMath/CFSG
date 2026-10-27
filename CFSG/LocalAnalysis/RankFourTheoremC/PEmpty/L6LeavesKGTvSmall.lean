module

public import CFSG.HardMathSupport.Solomon.Coordinator.I28_5Linear

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGTv

open Module CFSG.ComponentClassification.OutcomeLocal CFSG.HardMathSupport.Solomon.Coordinator

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

theorem commute_tv_apply (φ : Dual (ZMod 2) M) (a : M) (h : φ a = 0) (hφ : φ ≠ 0) (ha : a ≠ 0)
    {z : LinearMap.GeneralLinearGroup (ZMod 2) M} (hz : z * tv φ a h = tv φ a h * z) :
    (z : M →ₗ[ZMod 2] M) a = a ∧ ∀ v, φ ((z : M →ₗ[ZMod 2] M) v) = φ v := by
  have key : ∀ v, φ v • (z : M →ₗ[ZMod 2] M) a = φ ((z : M →ₗ[ZMod 2] M) v) • a := by
    intro v
    have := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2) M =>
      (g : M →ₗ[ZMod 2] M) v) hz
    simp only [i285_mul_apply, tv_apply, map_add, map_smul] at this
    exact add_left_cancel this
  have hza0 : (z : M →ₗ[ZMod 2] M) a ≠ 0 := by
    intro h0
    apply ha
    have := i285_inv_apply_apply z a
    rw [h0, map_zero] at this
    exact this.symm
  obtain ⟨v₀, hv₀⟩ := exists_apply_eq_one hφ
  have h1 := key v₀
  rw [hv₀, one_smul] at h1
  have hφz : φ ((z : M →ₗ[ZMod 2] M) v₀) = 1 := by
    rcases zmod2_eq_zero_or_one (φ ((z : M →ₗ[ZMod 2] M) v₀)) with h0 | h0
    · rw [h0, zero_smul] at h1
      exact absurd h1 hza0
    · exact h0
  rw [hφz, one_smul] at h1
  refine ⟨h1, fun v => ?_⟩
  have h2 := key v
  rw [h1] at h2
  exact (smul_left_injective (ZMod 2) ha h2).symm

theorem pow_twentyfour_eq_one {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Finite E]
    (hE : Nat.card E ≤ 4) (g : LinearMap.GeneralLinearGroup (ZMod 2) E) : g ^ 24 = 1 := by
  have := Fintype.ofFinite E
  let π : (E ≃ₗ[ZMod 2] E) →* Equiv.Perm E :=
    { toFun := fun e => e.toEquiv
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let ψ : LinearMap.GeneralLinearGroup (ZMod 2) E →* Equiv.Perm E :=
    π.comp (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) E).toMonoidHom
  have hψ : Function.Injective ψ := by
    intro a b hab
    apply (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) E).injective
    ext x
    exact congrArg (fun p : Equiv.Perm E => p x) hab
  apply hψ
  rw [map_pow, map_one]
  have h1 : (ψ g) ^ (Nat.card (Equiv.Perm E)) = 1 := pow_card_eq_one'
  have h2 : Nat.card (Equiv.Perm E) ∣ 24 := by
    rw [Nat.card_perm]
    interval_cases (Nat.card E) <;> decide
  obtain ⟨k, hk⟩ := h2
  rw [hk, pow_mul, h1, one_pow]

theorem ker_ne_top {φ : Dual (ZMod 2) M} (hφ : φ ≠ 0) : LinearMap.ker φ ≠ ⊤ := by
  intro h
  exact hφ (LinearMap.ker_eq_top.mp h)

theorem pow_eq_one_of_commute_tv [Finite M] (hM : Nat.card M ≤ 16) (φ : Dual (ZMod 2) M) (a : M)
    (h : φ a = 0) (hφ : φ ≠ 0) (ha : a ≠ 0) {z : LinearMap.GeneralLinearGroup (ZMod 2) M}
    (hz : z * tv φ a h = tv φ a h * z) : z ^ 96 = 1 := by
  have : Module.Finite (ZMod 2) M := Module.Finite.of_finite
  set K : Submodule (ZMod 2) M := LinearMap.ker φ with hK
  set A : Submodule (ZMod 2) M := Submodule.span (ZMod 2) {a} with hA
  set H : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) M) :=
    Subgroup.centralizer ({tv φ a h} : Set (LinearMap.GeneralLinearGroup (ZMod 2) M)) with hH
  have hmemH : ∀ g : LinearMap.GeneralLinearGroup (ZMod 2) M,
      g ∈ H ↔ g * tv φ a h = tv φ a h * g := by
    intro g
    rw [hH, Subgroup.mem_centralizer_singleton_iff]
  have hfix : ∀ g ∈ H, (g : M →ₗ[ZMod 2] M) a = a ∧ ∀ v, φ ((g : M →ₗ[ZMod 2] M) v) = φ v :=
    fun g hg => commute_tv_apply φ a h hφ ha ((hmemH g).1 hg)
  have haK : a ∈ K := by
    rw [hK, LinearMap.mem_ker]
    exact h
  have hRK : H ≤ i285_stab K := by
    refine i285_le_stab fun g hg v hv => ?_
    rw [hK, LinearMap.mem_ker] at hv ⊢
    rw [(hfix g hg).2 v, hv]
  have hRA : H ≤ i285_stab A := by
    refine i285_le_stab fun g hg v hv => ?_
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [map_smul, (hfix g hg).1]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a)
  set E := ↥K ⧸ A.comap K.subtype with hEdef
  have hEfin : Finite E := Finite.of_surjective (Submodule.mkQ (A.comap K.subtype))
    (Submodule.mkQ_surjective _)
  have hcardE : Nat.card E ≤ 4 := by
    have hdM : finrank (ZMod 2) M ≤ 4 := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := M), Nat.card_zmod] at hM
      by_contra hlt
      have : 2 ^ 5 ≤ 2 ^ finrank (ZMod 2) M := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hKlt : finrank (ZMod 2) K < finrank (ZMod 2) M := Submodule.finrank_lt (ker_ne_top hφ)
    have hsum : finrank (ZMod 2) E + finrank (ZMod 2) (A.comap K.subtype) =
        finrank (ZMod 2) K := Submodule.finrank_quotient_add_finrank (A.comap K.subtype)
    have hA1 : 1 ≤ finrank (ZMod 2) (A.comap K.subtype) := by
      rw [Submodule.one_le_finrank_iff]
      intro hbot
      have hmem : (⟨a, haK⟩ : ↥K) ∈ A.comap K.subtype :=
        Submodule.mem_comap.mpr (Submodule.mem_span_singleton_self a)
      rw [hbot, Submodule.mem_bot] at hmem
      exact ha (congrArg Subtype.val hmem)
    have hE2 : finrank (ZMod 2) E ≤ 2 := by omega
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := E), Nat.card_zmod]
    calc 2 ^ finrank (ZMod 2) E ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hE2
      _ = 4 := by norm_num
  have hz' : z ∈ H := (hmemH z).2 hz
  set Φ := i285_secHom hRK hRA with hΦdef
  have hΦ : (Φ ⟨z, hz'⟩) ^ 24 = 1 := pow_twentyfour_eq_one hcardE _
  have hz24 : z ^ 24 ∈ H := H.pow_mem hz' 24
  have hU : z ^ 24 ∈ i285_U3 K A := by
    refine ⟨fun v => ?_, fun v hv => ?_, fun v hv => ?_⟩
    · rw [hK, LinearMap.mem_ker, map_sub, (hfix _ hz24).2 v, sub_self]
    · have h1 : Φ (⟨z, hz'⟩ ^ 24) = 1 := by rw [map_pow, hΦ]
      have h2 := congrArg (fun f : LinearMap.GeneralLinearGroup (ZMod 2) E =>
        (f : E →ₗ[ZMod 2] E) (Submodule.Quotient.mk ⟨v, hv⟩)) h1
      rw [hΦdef, i285_secHom_mk] at h2
      change Submodule.Quotient.mk _ = Submodule.Quotient.mk _ at h2
      rw [Submodule.Quotient.eq] at h2
      exact h2
    · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
      rw [map_smul, (hfix _ hz24).1]
  have h4 := i285_pow_four hU
  rw [← pow_mul] at h4
  exact h4

theorem false_of_commute_tv [Finite M] (hM : Nat.card M ≤ 16) (φ : Dual (ZMod 2) M) (a : M)
    (h : φ a = 0) (hφ : φ ≠ 0) (ha : a ≠ 0) {z : LinearMap.GeneralLinearGroup (ZMod 2) M}
    (hz : z * tv φ a h = tv φ a h * z) {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q) (hzq : orderOf z = q) :
    False := by
  have h96 := pow_eq_one_of_commute_tv hM φ a h hφ ha hz
  have hdvd : q ∣ 96 := hzq ▸ orderOf_dvd_of_pow_eq_one h96
  have h2 : (96 : ℕ) = 2 ^ 5 * 3 := by norm_num
  rw [h2] at hdvd
  rcases (Nat.Prime.dvd_mul hq).1 hdvd with h5 | h3
  · have := Nat.le_of_dvd (by norm_num) (Nat.Prime.dvd_of_dvd_pow hq h5)
    omega
  · have := Nat.le_of_dvd (by norm_num) h3
    omega

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGTv
