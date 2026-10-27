module

public import CFSG.GroupTheory.SteinbergCBHHBExtraspecialModule
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.LinearAlgebra.PrimitiveRootEigenspaces
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.FPFS

open Module CFSG.GroupTheory.HallHigmanB

variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W]

noncomputable def adOp (A : (Module.End K W)ˣ) : Module.End K (Module.End K W) :=
  (LinearMap.mulLeft K (A : Module.End K W)).comp
    (LinearMap.mulRight K ((A⁻¹ : (Module.End K W)ˣ) : Module.End K W))

theorem mem_ker_adOp_sub_one (A : (Module.End K W)ˣ) (φ : Module.End K W) :
    φ ∈ LinearMap.ker (adOp A - 1) ↔ (A : Module.End K W) * φ = φ * (A : Module.End K W) := by
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
  change (A : Module.End K W) * φ * ((A⁻¹ : (Module.End K W)ˣ) : Module.End K W) = φ ↔ _
  constructor
  · intro h
    calc (A : Module.End K W) * φ = (A : Module.End K W) * φ *
        ((A⁻¹ : (Module.End K W)ˣ) : Module.End K W) * (A : Module.End K W) := by
          rw [mul_assoc _ _ (A : Module.End K W), Units.inv_mul, mul_one]
      _ = φ * (A : Module.End K W) := by rw [h]
  · intro h
    rw [h, mul_assoc, Units.mul_inv, mul_one]

theorem sq_le_pred_mul_finrank_ker_ad [FiniteDimensional K W] [IsAlgClosed K] {p : ℕ}
    [hp : Fact p.Prime] [NeZero (p : K)] (A : (Module.End K W)ˣ) (hAp : A ^ p = 1)
    (hfix : ∀ w : W, (A : Module.End K W) w = w → w = 0) :
    finrank K W ^ 2 ≤ (p - 1) * finrank K (LinearMap.ker (adOp A - 1)) := by
  classical
  obtain ⟨ε, hε⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K p
  set g : W ≃ₗ[K] W := LinearMap.GeneralLinearGroup.generalLinearEquiv K W A with hg
  have hgp : g ^ p = 1 := by rw [hg, ← map_pow, hAp, map_one]
  have hp2 : p ≥ 2 := hp.out.two_le
  set n : Fin p → ℕ := fun i =>
    finrank K (Module.End.eigenspace g.toLinearMap (ε ^ (((i : ℕ)) : ℤ))) with hn
  have hint := CFSG.proposition_2_4_a hgp hp2 hε
  have hdim : finrank K W = ∑ i, n i := by
    have e := LinearEquiv.ofBijective (DirectSum.coeLinearMap fun i : Fin p =>
      Module.End.eigenspace g.toLinearMap (ε ^ (((i : ℕ)) : ℤ))) hint
    rw [← e.finrank_eq, Module.finrank_directSum]
  have hcomm := CFSG.proposition_2_4_g hgp hp2 hε 0
  have hgA : g.toLinearMap = (A : Module.End K W) := rfl
  have hker : LinearMap.ker (adOp A - 1) =
      CFSG.intertwiningSubmodule g.toLinearMap (ε ^ (0 : ℤ) • g.toLinearMap) := by
    ext φ
    rw [mem_ker_adOp_sub_one, zpow_zero, one_smul, hgA]
    rfl
  have hc : finrank K (LinearMap.ker (adOp A - 1)) = ∑ i, n i * n i := by
    rw [hker, hcomm]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hn]
    rw [add_zero, zpow_natCast]
  have h0 : n ⟨0, hp.out.pos⟩ = 0 := by
    simp only [hn]
    rw [Nat.cast_zero, zpow_zero]
    have : Module.End.eigenspace g.toLinearMap (1 : K) = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      rw [Module.End.mem_eigenspace_iff, one_smul] at hw
      exact (Submodule.mem_bot K).2 (hfix w hw)
    rw [this]
    exact finrank_bot K W
  set s : Finset (Fin p) := Finset.univ.erase ⟨0, hp.out.pos⟩ with hs
  have hscard : s.card = p - 1 := by
    rw [hs, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hsum1 : ∑ i, n i = ∑ i ∈ s, n i := by
    rw [hs, Finset.sum_erase _ h0]
  have hsum2 : ∑ i, n i * n i = ∑ i ∈ s, n i ^ 2 := by
    rw [hs, Finset.sum_erase _ (by rw [h0]; rfl)]
    exact Finset.sum_congr rfl fun i _ => (sq (n i)).symm
  have hcs := sq_sum_le_card_mul_sum_sq (s := s) (f := n)
  rw [hdim, hc, hsum1, hsum2, ← hscard]
  exact hcs


theorem arith_final {p d m q a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime) (hq2 : q ≠ 2)
    (hd2 : 2 ≤ d) (hAC : d ^ 2 ≤ (p - 1) * m) (hB : p * m ≤ d ^ 2 - 1 + p)
    (hcong : d ^ 2 ≡ 1 [MOD p]) (hpow : d ^ 2 = q ^ a) : False := by
  have hp0 : 0 < p := hp.pos
  have h5 : 1 ≤ d ^ 2 := by nlinarith
  have hdp : d ≤ p - 1 := by
    by_contra h
    have h2 : p * d ^ 2 ≤ p * ((p - 1) * m) := Nat.mul_le_mul_left p hAC
    have h4 : (p - 1) * (p * m) ≤ (p - 1) * (d ^ 2 - 1 + p) := Nat.mul_le_mul_left _ hB
    obtain ⟨p', hp'⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    subst hp'
    simp only [Nat.add_sub_cancel] at h2 h4 h
    have h6 : d ^ 2 - 1 + (p' + 1) = d ^ 2 + p' := by omega
    rw [h6] at h4
    have h7 : (p' + 1) * d ^ 2 ≤ p' * d ^ 2 + p' * p' := by
      calc (p' + 1) * d ^ 2 ≤ (p' + 1) * (p' * m) := h2
        _ = p' * ((p' + 1) * m) := by ring
        _ ≤ p' * (d ^ 2 + p') := h4
        _ = p' * d ^ 2 + p' * p' := by ring
    have h8 : d ^ 2 ≤ p' * p' := by nlinarith
    have h9 : p' * p' < d ^ 2 := by nlinarith
    omega
  have hdvd : p ∣ (d - 1) * (d + 1) := by
    have h1' : 1 ≤ d := by omega
    have h2 : (d - 1) * (d + 1) = d ^ 2 - 1 := by
      zify [h1', h5]
      ring
    rw [h2]
    exact (Nat.modEq_iff_dvd' h5).1 hcong.symm
  have hdp1 : d + 1 = p := by
    rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
    · have := Nat.le_of_dvd (by omega) h
      omega
    · have := Nat.le_of_dvd (by omega) h
      omega
  have hp_odd : Odd p := hp.odd_of_ne_two hp2
  have hd_even : Even d := by
    obtain ⟨k, hk⟩ := hp_odd
    exact ⟨k, by omega⟩
  have h2d : 2 ∣ d ^ 2 := dvd_pow (even_iff_two_dvd.1 hd_even) (by norm_num)
  rw [hpow] at h2d
  have : 2 ∣ q := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2d
  exact hq2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).1 this).symm


section IrreducibleCore

variable {G : Type*} [Group G]

theorem irreducible_core_coprime [IsAlgClosed K] [FiniteDimensional K W] [Nontrivial W]
    [Finite G] {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    [NeZero (p : K)] (hGq : IsPGroup q G)
    (ρ : G →* (Module.End K W)ˣ) (hρ : Function.Injective ρ)
    (hsc : ∀ c ∈ Subgroup.center G, ∃ μ : K,
      ((ρ c : (Module.End K W)ˣ) : Module.End K W) = μ • 1)
    (hcl : ∀ s t : G, t * s * t⁻¹ * s⁻¹ ∈ Subgroup.center G)
    (hirr : ∀ W₁ : Submodule K W, (∀ g : G, ∀ w ∈ W₁,
      ((ρ g : (Module.End K W)ˣ) : Module.End K W) w ∈ W₁) → W₁ = ⊥ ∨ W₁ = ⊤)
    (hnab : ∃ g : G, g ∉ Subgroup.center G) (A : (Module.End K W)ˣ) (θ : MulAut G)
    (hAθ : ∀ g, A * ρ g * A⁻¹ = ρ (θ g)) (hAP : A ^ p = 1)
    (hfpf : ∀ g : G, g⁻¹ * θ g ∈ Subgroup.center G → g ∈ Subgroup.center G) :
    ∃ w : W, w ≠ 0 ∧ (A : Module.End K W) w = w := by
  classical
  by_contra hno
  push Not at hno
  have hfix : ∀ w : W, (A : Module.End K W) w = w → w = 0 := fun w hw => by
    by_contra h
    exact hno w h hw
  have : Fintype (G ⧸ Subgroup.center G) := Fintype.ofFinite _
  have hp0 : 0 < p := hp.out.pos
  set b := Basis.mk (linearIndependent_rho_out ρ hρ hsc hcl)
    (span_range_rho_out ρ hsc hirr).ge with hbdef
  have hbx : ∀ x, b x = ((ρ x.out : (Module.End K W)ˣ) : Module.End K W) := fun x => by
    rw [hbdef, Basis.mk_apply]
  have hθZ : ∀ (φ : MulAut G), ∀ c ∈ Subgroup.center G, φ c ∈ Subgroup.center G := by
    intro φ c hc
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro g
    obtain ⟨g', rfl⟩ := φ.surjective g
    rw [← map_mul, ← map_mul, hc g']
  have hθmap : (Subgroup.center G).map θ.toMonoidHom = Subgroup.center G := by
    refine le_antisymm ?_ fun c hc => ⟨θ.symm c, hθZ θ.symm c hc, by simp⟩
    rintro _ ⟨c, hc, rfl⟩
    exact hθZ θ c hc
  set π : Equiv.Perm (G ⧸ Subgroup.center G) :=
    (QuotientGroup.congr (Subgroup.center G) (Subgroup.center G) θ hθmap).toEquiv with hπdef
  have hπ : ∀ g : G, π (g : G ⧸ Subgroup.center G) = ((θ g : G) : G ⧸ Subgroup.center G) :=
    fun g => QuotientGroup.congr_mk _ _ _ _ g
  have hπpow : ∀ (n : ℕ) (g : G), (π ^ n) (g : G ⧸ Subgroup.center G) =
      (((θ ^ n) g : G) : G ⧸ Subgroup.center G) := by
    intro n
    induction n with
    | zero => intro g; rfl
    | succ n ih =>
      intro g
      rw [pow_succ', Equiv.Perm.mul_apply, ih, hπ, pow_succ', MulAut.mul_apply]
  have hAθn : ∀ (n : ℕ) (g : G), A ^ n * ρ g * (A ^ n)⁻¹ = ρ ((θ ^ n) g) := by
    intro n
    induction n with
    | zero => intro g; simp
    | succ n ih =>
      intro g
      rw [pow_succ' θ n, MulAut.mul_apply, ← hAθ, ← ih, pow_succ' A n]
      group
  have hθP : ∀ g, (θ ^ p) g = g := fun g => hρ (by rw [← hAθn, hAP]; group)
  have hmemc : ∀ x : G ⧸ Subgroup.center G,
      (π x).out⁻¹ * θ x.out ∈ Subgroup.center G := fun x => by
    refine QuotientGroup.eq.1 ?_
    rw [QuotientGroup.out_eq', ← hπ, QuotientGroup.out_eq']
  set c : G ⧸ Subgroup.center G → K := fun x => centralScalar ρ hsc ⟨_, hmemc x⟩ with hcdef
  have hT : ∀ x, adOp A (b x) = c x • b (π x) := by
    intro x
    rw [hbx, hbx]
    change (A : Module.End K W) * ((ρ x.out : (Module.End K W)ˣ) : Module.End K W) *
      ((A⁻¹ : (Module.End K W)ˣ) : Module.End K W) = _
    rw [← Units.val_mul, ← Units.val_mul, hAθ]
    have h1 : θ x.out = (π x).out * ((π x).out⁻¹ * θ x.out) := by group
    rw [h1, map_mul, Units.val_mul]
    change _ * ((ρ ((⟨_, hmemc x⟩ : Subgroup.center G) : G) : (Module.End K W)ˣ) :
      Module.End K W) = _
    rw [centralScalar_spec ρ hsc, mul_smul_comm, mul_one]
  have he : π 1 = 1 := by
    rw [← QuotientGroup.mk_one, hπ, map_one]
  have hπP : ∀ x, (π ^ p) x = x := fun x => by
    rw [← QuotientGroup.out_eq' x, hπpow, hθP]
  have hfree : ∀ x : G ⧸ Subgroup.center G, x ≠ 1 → ∀ i j, i < p → j < p →
      (π ^ i) x = (π ^ j) x → i = j := by
    intro x hx i j hi hj hij
    have hper : Function.minimalPeriod π x = p := by
      have hdvd : Function.minimalPeriod π x ∣ p := by
        refine Function.IsPeriodicPt.minimalPeriod_dvd ?_
        change (⇑π)^[p] x = x
        rw [← Equiv.Perm.coe_pow, funext hπP]
      rcases (Nat.dvd_prime hp.out).1 hdvd with h1 | h1
      · exfalso
        apply hx
        have h2 : π x = x := by
          have h3 := Function.iterate_minimalPeriod (f := π) (x := x)
          rwa [h1, Function.iterate_one] at h3
        rw [← QuotientGroup.out_eq' x, hπ] at h2
        have h3 := QuotientGroup.eq.1 h2.symm
        rw [← QuotientGroup.out_eq' x]
        exact (QuotientGroup.eq_one_iff _).2 (hfpf _ h3)
      · exact h1
    have hi' : i < Function.minimalPeriod π x := hper ▸ hi
    have hj' : j < Function.minimalPeriod π x := hper ▸ hj
    rw [Equiv.Perm.coe_pow, Equiv.Perm.coe_pow] at hij
    exact Function.iterate_injOn_Iio_minimalPeriod hi' hj' hij
  have hB := mul_finrank_ker_sub_one_le b (adOp A) π c hT hp0 1 he hπP hfree
  have hd2 := finrank_sq_eq_card_quotient_center ρ hρ hsc hcl hirr
  rw [← Nat.card_eq_fintype_card, ← hd2] at hB
  have hAC := sq_le_pred_mul_finrank_ker_ad A hAP hfix
  have hcong : Nat.card (G ⧸ Subgroup.center G) ≡ 1 [MOD p] := by
    have h1 : (π ^ p ^ 1 = 1) := by
      ext x
      rw [pow_one]
      exact hπP x
    have h2 := Equiv.Perm.card_compl_support_modEq (p := p) (n := 1) h1
    have h3 : (Equiv.Perm.support π)ᶜ = {1} := by
      ext x
      simp only [Finset.mem_compl, Equiv.Perm.mem_support, not_not, Finset.mem_singleton]
      constructor
      · intro hx
        by_contra hne
        have h4 := hfree x hne 0 1 hp0 hp.out.one_lt (by simpa using hx.symm)
        omega
      · rintro rfl
        exact he
    rw [h3, Finset.card_singleton] at h2
    rw [Nat.card_eq_fintype_card]
    exact h2.symm
  have hcard : 2 ≤ Nat.card (G ⧸ Subgroup.center G) := by
    obtain ⟨g, hg⟩ := hnab
    have hne : ((g : G ⧸ Subgroup.center G)) ≠ 1 := fun h =>
      hg ((QuotientGroup.eq_one_iff g).1 h)
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card_iff.2 ⟨_, _, hne⟩
  have hd2' : 2 ≤ finrank K W := by
    by_contra h
    have : finrank K W ≤ 1 := by omega
    have : finrank K W ^ 2 ≤ 1 := by nlinarith
    omega
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card.1 (hGq.to_quotient (Subgroup.center G)))
  exact arith_final hp.out hp2 hq.out hq2 hd2' hAC hB (by rw [hd2]; exact hcong)
    (by rw [hd2, ha])

end IrreducibleCore


section Extraspecial

variable {G : Type*} [Group G] {U : Type*} [AddCommGroup U] [Module K U]

theorem extraspecial_core_coprime [IsAlgClosed K] [FiniteDimensional K U] [Nontrivial U]
    [Finite G] {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    [NeZero (p : K)] (hGq : IsPGroup q G) (ρ : G →* (Module.End K U)ˣ)
    (hρ : Function.Injective ρ)
    (hsc : ∀ c ∈ Subgroup.center G, ∃ μ : K,
      ((ρ c : (Module.End K U)ˣ) : Module.End K U) = μ • 1)
    (hcl : ∀ s t : G, t * s * t⁻¹ * s⁻¹ ∈ Subgroup.center G)
    (hnab : ∃ g : G, g ∉ Subgroup.center G) (y : (Module.End K U)ˣ) (θ : MulAut G)
    (hyθ : ∀ g, y * ρ g * y⁻¹ = ρ (θ g)) (hyP : y ^ p = 1)
    (hfpf : ∀ g : G, g⁻¹ * θ g ∈ Subgroup.center G → g ∈ Subgroup.center G) :
    ∃ u : U, u ≠ 0 ∧ (y : Module.End K U) u = u := by
  classical
  have hp0 : 0 < p := hp.out.pos
  have hθZ : ∀ c ∈ Subgroup.center G, θ c = c := fun c hc => hρ (by
    obtain ⟨μ, hμ⟩ := hsc c hc
    rw [← hyθ]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hμ, mul_smul_comm, mul_one, smul_mul_assoc, Units.mul_inv])
  have hyθn : ∀ (n : ℕ) (g : G), y ^ n * ρ g * (y ^ n)⁻¹ = ρ ((θ ^ n) g) := by
    intro n
    induction n with
    | zero => intro g; simp
    | succ n ih =>
      intro g
      rw [pow_succ' θ n, MulAut.mul_apply, ← hyθ, ← ih, pow_succ' y n]
      group
  have hθP : ∀ g, (θ ^ p) g = g := fun g => hρ (by rw [← hyθn, hyP]; group)
  obtain ⟨W, hW0, hWinv, hWmin⟩ := exists_minimal_invariant ρ
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.2 hW0
  set ρW := restrictRep ρ W hWinv with hρWdef
  have hρW := restrictRep_injective hGq ρ hρ hsc W hW0 hWinv
  have hscW : ∀ c ∈ Subgroup.center G, ∃ μ : K,
      ((ρW c : (Module.End K W)ˣ) : Module.End K W) = μ • 1 := fun c hc => by
    obtain ⟨μ, hμ⟩ := hsc c hc
    refine ⟨μ, LinearMap.ext fun w => Subtype.ext ?_⟩
    rw [restrictRep_apply, hμ]
    rfl
  have hirrW := restrictRep_irreducible ρ W hWinv hWmin
  obtain ⟨A, hAP, hAρ⟩ := exists_intertwiner ρW hρW hscW hcl hirrW θ hθZ hp0 hθP
  have hAinv : ∀ g, ((A⁻¹ : (Module.End K W)ˣ) : Module.End K W) *
      ((ρW g : (Module.End K W)ˣ) : Module.End K W) =
      ((ρW (θ.symm g) : (Module.End K W)ˣ) : Module.End K W) *
        ((A⁻¹ : (Module.End K W)ˣ) : Module.End K W) := fun g => by
    have h1 := hAρ (θ.symm g)
    rw [MulEquiv.apply_symm_apply] at h1
    rw [← Units.val_mul, ← Units.val_mul, ← h1]
    congr 1
    group
  have hyinv : ∀ g, (y : Module.End K U) * ((ρ (θ.symm g) : (Module.End K U)ˣ) :
      Module.End K U) = ((ρ g : (Module.End K U)ˣ) : Module.End K U) * (y : Module.End K U) :=
    fun g => by
      have h1 := hyθ (θ.symm g)
      rw [MulEquiv.apply_symm_apply] at h1
      rw [← Units.val_mul, ← Units.val_mul, ← h1]
      congr 1
      group
  set M := homRep ρW ρ with hMdef
  have hτmem : ∀ φ ∈ M, (y : Module.End K U) ∘ₗ φ ∘ₗ
      ((A⁻¹ : (Module.End K W)ˣ) : Module.End K W) ∈ M := by
    intro φ hφ g
    refine LinearMap.ext fun w => ?_
    have h1 := congrArg (fun F : Module.End K W => F w) (hAinv g)
    have h2 := congrArg (fun F : W →ₗ[K] U => F (((A⁻¹ : (Module.End K W)ˣ) :
      Module.End K W) w)) (hφ (θ.symm g))
    have h3 := congrArg (fun F : Module.End K U => F (φ (((A⁻¹ : (Module.End K W)ˣ) :
      Module.End K W) w))) (hyinv g)
    simp only [Module.End.mul_apply, LinearMap.comp_apply] at h1 h2 h3 ⊢
    rw [h1, h2, h3]
  let τ : Module.End K M :=
    { toFun := fun φ => ⟨(y : Module.End K U) ∘ₗ φ.1 ∘ₗ
        ((A⁻¹ : (Module.End K W)ˣ) : Module.End K W), hτmem φ.1 φ.2⟩
      map_add' := fun φ ψ => by
        apply Subtype.ext
        simp [LinearMap.comp_add, LinearMap.add_comp]
      map_smul' := fun a φ => by
        apply Subtype.ext
        simp [LinearMap.comp_smul, LinearMap.smul_comp] }
  have hsub : W.subtype ∈ M := fun g => LinearMap.ext fun w => rfl
  have hMnt : Nontrivial M := ⟨⟨⟨_, hsub⟩, 0, fun h => by
    have := congrArg Subtype.val h
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    have h2 := congrArg (fun F : W →ₗ[K] U => F w) this
    simp only [Submodule.subtype_apply, ZeroMemClass.coe_zero, LinearMap.zero_apply] at h2
    exact hw (Subtype.ext h2)⟩⟩
  obtain ⟨ζ, hζ⟩ := Module.End.exists_eigenvalue τ
  obtain ⟨φ₀, hφ₀e, hφ₀0⟩ := hζ.exists_hasEigenvector
  have hτφ : τ φ₀ = ζ • φ₀ := Module.End.mem_eigenspace_iff.1 hφ₀e
  set φ := (φ₀ : W →ₗ[K] U) with hφdef
  have hφeq : ∀ g w, φ (((ρW g : (Module.End K W)ˣ) : Module.End K W) w) =
      ((ρ g : (Module.End K U)ˣ) : Module.End K U) (φ w) := fun g w =>
    congrArg (fun F : W →ₗ[K] U => F w) (φ₀.2 g)
  have hφy : ∀ w, (y : Module.End K U) (φ w) = ζ • φ ((A : Module.End K W) w) := fun w => by
    have h1 := congrArg (fun ψ : M => (ψ : W →ₗ[K] U) ((A : Module.End K W) w)) hτφ
    simp only [τ, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply] at h1
    rw [← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply] at h1
    exact h1
  have hφinj : Function.Injective φ := by
    have hker : ∀ g, ∀ w ∈ LinearMap.ker φ,
        ((ρW g : (Module.End K W)ˣ) : Module.End K W) w ∈ LinearMap.ker φ := by
      intro g w hw
      rw [LinearMap.mem_ker] at hw ⊢
      rw [hφeq, hw, map_zero]
    rcases hirrW _ hker with h | h
    · exact LinearMap.ker_eq_bot.1 h
    · exfalso
      apply hφ₀0
      apply Subtype.ext
      exact LinearMap.ker_eq_top.1 h
  set W' := LinearMap.range φ with hW'def
  have hW'inv : ∀ g, ∀ u ∈ W', ((ρ g : (Module.End K U)ˣ) : Module.End K U) u ∈ W' := by
    rintro g _ ⟨w, rfl⟩
    exact ⟨_, hφeq g w⟩
  have hW'y : ∀ u ∈ W', (y : Module.End K U) u ∈ W' := by
    rintro _ ⟨w, rfl⟩
    exact ⟨ζ • (A : Module.End K W) w, by rw [map_smul, hφy w]⟩
  have hW'ypow : ∀ (n : ℕ), ∀ u ∈ W', ((y ^ n : (Module.End K U)ˣ) : Module.End K U) u ∈ W' := by
    intro n
    induction n with
    | zero => intro u hu; simpa using hu
    | succ n ih =>
      intro u hu
      rw [pow_succ', Units.val_mul, Module.End.mul_apply]
      exact hW'y _ (ih u hu)
  have hW'yinv : ∀ u ∈ W', ((y⁻¹ : (Module.End K U)ˣ) : Module.End K U) u ∈ W' := by
    intro u hu
    have : y⁻¹ = y ^ (p - 1) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel hp0, hyP]
    rw [this]
    exact hW'ypow _ u hu
  have hW'0 : W' ≠ ⊥ := by
    intro h
    apply hφ₀0
    apply Subtype.ext
    exact LinearMap.range_eq_bot.1 h
  have hW'min : ∀ W₁ : Submodule K U, W₁ ≤ W' → (∀ g, ∀ w ∈ W₁,
      ((ρ g : (Module.End K U)ˣ) : Module.End K U) w ∈ W₁) → W₁ = ⊥ ∨ W₁ = W' := by
    intro W₁ hW₁ hW₁inv
    have hinv : ∀ g, ∀ w ∈ W₁.comap φ,
        ((ρW g : (Module.End K W)ˣ) : Module.End K W) w ∈ W₁.comap φ := by
      intro g w hw
      rw [Submodule.mem_comap] at hw ⊢
      rw [hφeq]
      exact hW₁inv g _ hw
    have hmap : (W₁.comap φ).map φ = W₁ := by
      rw [Submodule.map_comap_eq, inf_eq_right.2 hW₁]
    rcases hirrW _ hinv with h | h
    · left
      rw [← hmap, h, Submodule.map_bot]
    · right
      rw [← hmap, h, Submodule.map_top]
  have : Nontrivial W' := Submodule.nontrivial_iff_ne_bot.2 hW'0
  set ρ' := restrictRep ρ W' hW'inv with hρ'def
  have hρ' := restrictRep_injective hGq ρ hρ hsc W' hW'0 hW'inv
  have hsc' : ∀ c ∈ Subgroup.center G, ∃ μ : K,
      ((ρ' c : (Module.End K W')ˣ) : Module.End K W') = μ • 1 := fun c hc => by
    obtain ⟨μ, hμ⟩ := hsc c hc
    refine ⟨μ, LinearMap.ext fun w => Subtype.ext ?_⟩
    rw [restrictRep_apply, hμ]
    rfl
  have hirr' := restrictRep_irreducible ρ W' hW'inv hW'min
  let y' : (Module.End K W')ˣ :=
    { val := (y : Module.End K U).restrict hW'y
      inv := ((y⁻¹ : (Module.End K U)ˣ) : Module.End K U).restrict hW'yinv
      val_inv := by
        refine LinearMap.ext fun w => Subtype.ext ?_
        change (y : Module.End K U) (((y⁻¹ : (Module.End K U)ˣ) : Module.End K U) w) = w
        rw [← Module.End.mul_apply, Units.mul_inv, Module.End.one_apply]
      inv_val := by
        refine LinearMap.ext fun w => Subtype.ext ?_
        change ((y⁻¹ : (Module.End K U)ˣ) : Module.End K U) ((y : Module.End K U) w) = w
        rw [← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply] }
  have hy'θ : ∀ g, y' * ρ' g * y'⁻¹ = ρ' (θ g) := fun g => by
    apply Units.ext
    refine LinearMap.ext fun w => Subtype.ext ?_
    have h1 := congrArg (fun F : Module.End K U => F w) (congrArg Units.val (hyθ g))
    simp only [Units.val_mul, Module.End.mul_apply] at h1
    rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply]
    exact h1
  have hy'P : y' ^ p = 1 := by
    apply Units.ext
    refine LinearMap.ext fun w => Subtype.ext ?_
    have hpow : ∀ (n : ℕ) (w : W'), (((y' ^ n : (Module.End K W')ˣ) : Module.End K W') w : U) =
        ((y ^ n : (Module.End K U)ˣ) : Module.End K U) w := by
      intro n
      induction n with
      | zero => intro w; rfl
      | succ n ih =>
        intro w
        rw [pow_succ', Units.val_mul, Module.End.mul_apply, pow_succ', Units.val_mul,
          Module.End.mul_apply, ← ih]
        rfl
    rw [hpow, hyP]
    rfl
  obtain ⟨w, hw0, hw⟩ := irreducible_core_coprime hp2 hq2 hGq ρ' hρ' hsc' hcl hirr' hnab y' θ
    hy'θ hy'P hfpf
  refine ⟨(w : U), fun h => hw0 (Subtype.ext h), ?_⟩
  exact congrArg Subtype.val hw

end Extraspecial

end CFSG.LocalAnalysis.RankThreeTheoremC.FPFS
