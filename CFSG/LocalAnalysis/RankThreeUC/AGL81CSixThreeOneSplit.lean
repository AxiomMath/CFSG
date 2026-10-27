module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneSympDefs
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneReducible
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneDickson
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.Quasithin.Background.SmithCurtisBasic
public import CFSG.LinearAlgebra.LinearGroups.QuadraticActions
import CFSG.GroupTheory.CoprimeActionSupport.FaithfulIrreduciblePCoreTrivial
import CFSG.RankThree.PartTwo.J2Residue.LinAlg
import CFSG.Quasithin.Vol2.Ch11SecO6E

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631

open Subgroup
open CFSG.LinearGroups
open scoped MatrixGroups commutatorElement

section Fixed

variable {p : ℕ} [Fact p.Prime]

private theorem exists_fixed_of_orderOf_eq_prime {U : Type}
    [AddCommGroup U] [Module (ZMod p) U] [Module.Finite (ZMod p) U] [Nontrivial U]
    (u : (Module.End (ZMod p) U)ˣ) (hu : orderOf u = p) :
    ∃ v : U, v ≠ 0 ∧ (u : Module.End (ZMod p) U) v = v := by
  have hP : IsPGroup p ↥(Subgroup.zpowers u) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hu, pow_one]
  let ρ : ↥(Subgroup.zpowers u) →* (U ≃ₗ[ZMod p] U) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) U).toMonoidHom.comp
      (Subgroup.subtype (Subgroup.zpowers u))
  letI : DistribMulAction ↥(Subgroup.zpowers u) U := DistribMulAction.compHom U ρ
  obtain ⟨v, hv0, hvfix⟩ := CFSG.Quasithin.SmithCurtis.exists_fixed_ne_of_zmod
    (M := U) (S := ↥(Subgroup.zpowers u)) hP
  refine ⟨v, hv0, ?_⟩
  let g : ↥(Subgroup.zpowers u) := ⟨u, Subgroup.mem_zpowers_iff.mpr ⟨1, pow_one u⟩⟩
  have h := hvfix g
  change (ρ g) v = v at h
  simpa [ρ] using h

end Fixed

variable {p : ℕ} [Fact p.Prime]

section NegOne

variable {F : Type*} [Field F] [NeZero (2 : F)] {V : Type*} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]

private theorem mapsTo_ker_of_comm (k q : Module.End F V) (h : k * q = q * k) :
    ∀ v ∈ LinearMap.ker q, k v ∈ LinearMap.ker q := by
  intro v hv
  rw [LinearMap.mem_ker] at hv ⊢
  rw [← Module.End.mul_apply, ← h, Module.End.mul_apply, hv, map_zero]

theorem eq_neg_one_of_involution_of_no_invariant_line (hV : Module.finrank F V = 2)
    (σ : (Module.End F V)ˣ) (hσ : σ ^ 2 = 1) (hσne : σ ≠ 1)
    (K : Subgroup (Module.End F V)ˣ) (hcomm : ∀ k ∈ K, σ * k = k * σ)
    (hinv : ∀ T : Submodule F V, (∀ k ∈ K, ∀ v ∈ T, (k : Module.End F V) v ∈ T) →
      T = ⊥ ∨ T = ⊤) :
    σ = -1 := by
  have hcommEnd : ∀ k ∈ K, (k : Module.End F V) * (σ : Module.End F V) =
      (σ : Module.End F V) * k := by
    intro k hk
    have h := congrArg (fun u : (Module.End F V)ˣ => (u : Module.End F V)) (hcomm k hk)
    rw [Units.val_mul, Units.val_mul] at h
    exact h.symm
  have hinv1 : ∀ k ∈ K, ∀ v ∈ LinearMap.ker ((σ : Module.End F V) - 1),
      (k : Module.End F V) v ∈ LinearMap.ker ((σ : Module.End F V) - 1) :=
    fun k hk => mapsTo_ker_of_comm (k : Module.End F V) ((σ : Module.End F V) - 1)
      ((Commute.sub_right ((commute_iff_eq _ _).mpr (hcommEnd k hk))
        (Commute.one_right _))).eq
  have hinv2 : ∀ k ∈ K, ∀ v ∈ LinearMap.ker ((σ : Module.End F V) + 1),
      (k : Module.End F V) v ∈ LinearMap.ker ((σ : Module.End F V) + 1) :=
    fun k hk => mapsTo_ker_of_comm (k : Module.End F V) ((σ : Module.End F V) + 1)
      ((Commute.add_right ((commute_iff_eq _ _).mpr (hcommEnd k hk))
        (Commute.one_right _))).eq
  have hcompl := CFSG.RankThree.PartTwo.J2Residue.isCompl_ker_sub_one_ker_add_one
    (NeZero.ne (2 : F)) (σ : Module.End F V) (by
      rw [← Units.val_mul, ← pow_two, hσ, Units.val_one])
  rcases hinv _ hinv1 with h1 | h1
  · have htop : LinearMap.ker ((σ : Module.End F V) + 1) = ⊤ := by
      have := hcompl.sup_eq_top
      rwa [h1, bot_sup_eq] at this
    have hzero : (σ : Module.End F V) + 1 = 0 := LinearMap.ker_eq_top.mp htop
    have hσeq : (σ : Module.End F V) = -1 := by
      rw [add_eq_zero_iff_eq_neg] at hzero
      exact hzero
    exact Units.ext (by simpa using hσeq)
  · exfalso
    apply hσne
    have hzero : (σ : Module.End F V) - 1 = 0 := LinearMap.ker_eq_top.mp h1
    exact Units.ext (by rw [sub_eq_zero.mp hzero, Units.val_one])
end NegOne

section NoInvariantLine
variable {W : Type} [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W]
theorem forall_invariant_eq_top_of_no_isotropic {B : LinearMap.BilinForm (ZMod p) W}
    (hBalt : ∀ w : W, B w w = 0) {H : Subgroup (Module.End (ZMod p) W)ˣ}
    {U : Submodule (ZMod p) W} (hHU : ∀ x ∈ H, ∀ u ∈ U,
      (x : Module.End (ZMod p) W) u ∈ U) (hU : Module.finrank (ZMod p) U = 2)
    (hno : ∀ T : Submodule (ZMod p) W, T ≠ ⊥ → (∀ u ∈ T, ∀ v ∈ T, B u v = 0) →
      ¬ ∀ x ∈ H, ∀ u ∈ T, (x : Module.End (ZMod p) W) u ∈ T) :
    ∀ T : Submodule (ZMod p) U, T ≠ ⊥ →
      (∀ k ∈ (invariantRestrict H U hHU).range, ∀ v ∈ T,
        (k : Module.End (ZMod p) U) v ∈ T) → T = ⊤ := by
  intro T hTne hTinv
  by_contra hTtop
  have hpos : 0 < Module.finrank (ZMod p) T :=
    Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hTne)
  have hlt : Module.finrank (ZMod p) T < 2 := by
    have := Submodule.finrank_lt hTtop
    rwa [hU] at this
  have hT1 : Module.finrank (ZMod p) T = 1 := by omega
  let T' : Submodule (ZMod p) W := T.map U.subtype
  have hT'1 : Module.finrank (ZMod p) T' = 1 := by
    dsimp only [T']
    rw [Submodule.finrank_map_subtype_eq, hT1]
  have hT'ne : T' ≠ ⊥ := by
    intro hbot
    apply hTne
    have h := congrArg (Submodule.comap U.subtype) hbot
    rw [Submodule.comap_map_eq_of_injective U.subtype_injective,
      Submodule.comap_bot, LinearMap.ker_eq_bot.mpr U.subtype_injective] at h
    exact h
  have hT'iso : ∀ u ∈ T', ∀ v ∈ T', B u v = 0 := by
    intro x hx y hy
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff T').mp hT'ne
    have hspan' : ZMod p ∙ v = T' := by
      refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
      · rw [Submodule.span_singleton_le_iff_mem]
        exact hv
      · rw [finrank_span_singleton hv0, hT'1]
    have hspan : T' = ZMod p ∙ v := hspan'.symm
    rw [hspan] at hx hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
    have h2 : B (a • v) (b • v) = b • B (a • v) v := LinearMap.map_smul (B (a • v)) b v
    have h1 : B (a • v) v = 0 := by
      rw [LinearMap.map_smul B a v, LinearMap.smul_apply, hBalt v, smul_zero]
    rw [h2, h1, smul_zero]
  have hT'inv : ∀ x ∈ H, ∀ u ∈ T', (x : Module.End (ZMod p) W) u ∈ T' := by
    intro x hx u hu
    rw [Submodule.mem_map] at hu ⊢
    obtain ⟨a, ha, rfl⟩ := hu
    refine ⟨((invariantRestrict H U hHU ⟨x, hx⟩ : (Module.End (ZMod p) U)ˣ) :
        Module.End (ZMod p) U) a, ?_, ?_⟩
    · exact hTinv _ (MonoidHom.mem_range.mpr ⟨⟨x, hx⟩, rfl⟩) a ha
    · exact (coe_invariantRestrict_apply H U hHU ⟨x, hx⟩ a).symm
  exact hno T' hT'ne hT'iso hT'inv
end NoInvariantLine
theorem exists_mulEquiv_sl2_of_no_invariant_line {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] [Module.Finite (ZMod p) V] {K : Subgroup (Module.End (ZMod p) V)ˣ}
    (hKgen : oPPrimeHull p K = K) (hV2 : Module.finrank (ZMod p) V = 2)
    (hnoK : ∀ T : Submodule (ZMod p) V, T ≠ ⊥ →
      (∀ k ∈ K, ∀ v ∈ T, (k : Module.End (ZMod p) V) v ∈ T) → T = ⊤) :
    Nonempty (↥K ≃* SL(2, ZMod p)) := by
  classical
  haveI : Finite V := Module.finite_of_finite (ZMod p)
  have hVpos : 0 < Module.finrank (ZMod p) V := by omega
  have hpCore : CFSG.pCore p ↥K = ⊥ := by
    let ρ : ↥K →* (V ≃ₗ[ZMod p] V) :=
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) V).toMonoidHom.comp
        (Subgroup.subtype K)
    refine CFSG.GroupTheory.CoprimeActionSupport.FaithfulIrreduciblePCoreTrivial.pCore_eq_bot
      (p := p) ρ ?_ ?_
    · exact (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) V).injective.comp
        K.subtype_injective
    · intro W hW
      by_cases h : W = ⊥
      · exact Or.inl h
      · exact Or.inr (hnoK W h fun k hk v hv => hW ⟨k, hk⟩ v hv)
  have hD := sLTwoOrTrivial_of_finrank_eq_two (p := p) (U := V) (H := K)
    (sLTwoOrTrivialAt p) hV2 hKgen
  rcases hD with h | hcard
  · obtain ⟨e⟩ := h
    exact ⟨((QuotientGroup.quotientMulEquivOfEq hpCore).trans
      QuotientGroup.quotientBot).symm.trans e⟩
  · exfalso
    have hcardK : Nat.card ↥K = 1 := by
      have e : (↥K ⧸ CFSG.pCore p ↥K) ≃* ↥K :=
        (QuotientGroup.quotientMulEquivOfEq hpCore).trans QuotientGroup.quotientBot
      rw [← Nat.card_congr e.toEquiv]
      exact hcard
    have hKbot : K = ⊥ := Subgroup.card_eq_one.mp hcardK
    have hVnt : Nontrivial V := Module.finrank_pos_iff.mp hVpos
    obtain ⟨v, hv0⟩ := exists_ne (0 : V)
    let T : Submodule (ZMod p) V := ZMod p ∙ v
    have hTne : T ≠ ⊥ := by
      intro h
      exact hv0 (Submodule.span_singleton_eq_bot.mp h)
    have hT1 : Module.finrank (ZMod p) T = 1 := finrank_span_singleton hv0
    have hTtop : T ≠ ⊤ := by
      intro h
      rw [h, finrank_top, hV2] at hT1
      omega
    have hTinv : ∀ k ∈ K, ∀ w ∈ T, (k : Module.End (ZMod p) V) w ∈ T := by
      intro k hk w hw
      rw [hKbot, Subgroup.mem_bot] at hk
      rw [show (k : Module.End (ZMod p) V) = 1 by rw [hk]; rfl]
      exact hw
    exact hTtop (hnoK T hTne hTinv)
private theorem sq_eq_one_quotient_commutator_of_sup {G : Type*} [Group G] [Finite G]
    {N : Subgroup G} [N.Normal] (hNexp : ∀ n ∈ N, n * n = 1)
    (hsup : commutator G ⊔ N = ⊤) (g : G) :
    (QuotientGroup.mk' (commutator G) g) ^ 2 = 1 := by
  have hg : g ∈ commutator G ⊔ N := by rw [hsup]; trivial
  obtain ⟨k, hk, n, hn, hkn⟩ := (Subgroup.mem_sup_of_normal_right).mp hg
  have hkK : QuotientGroup.mk' (commutator G) k = 1 := by
    change (QuotientGroup.mk k : G ⧸ commutator G) = 1
    rw [QuotientGroup.eq_one_iff]
    exact hk
  rw [← hkn, map_mul, hkK, one_mul, ← map_pow, pow_two, hNexp n hn, map_one]

private theorem oPPrimeHull_le_commutator_of_sq_eq_one {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hsq : ∀ g : G, (QuotientGroup.mk' (commutator G) g) ^ 2 = 1) :
    oPPrimeHull p (⊤ : Subgroup G) ≤ commutator G := by
  refine Subgroup.closure_le _ |>.mpr ?_
  rintro x ⟨-, k, hk⟩
  have hdvd2 : orderOf (QuotientGroup.mk' (commutator G) x) ∣ 2 :=
    orderOf_dvd_iff_pow_eq_one.mpr (hsq x)
  have hdvdp : orderOf (QuotientGroup.mk' (commutator G) x) ∣ p ^ k := by
    rw [← hk]
    exact orderOf_map_dvd (QuotientGroup.mk' (commutator G)) x
  have hcop : Nat.Coprime 2 (p ^ k) := by
    have hcop2 : Nat.Coprime 2 p := by
      rw [Nat.coprime_comm]
      refine (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr ?_
      intro hdvd
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact (Fact.out : p.Prime).one_lt.ne' h
      · exact hp2 h
    exact Nat.Coprime.pow_right k hcop2
  have hd1 : orderOf (QuotientGroup.mk' (commutator G) x) ∣ 1 := by
    have hg1 : Nat.gcd 2 (p ^ k) = 1 := hcop
    rw [← hg1]
    exact Nat.dvd_gcd hdvd2 hdvdp
  have hx1 : QuotientGroup.mk' (commutator G) x = 1 :=
    orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd1)
  change (QuotientGroup.mk x : G ⧸ commutator G) = 1 at hx1
  rwa [QuotientGroup.eq_one_iff] at hx1

theorem isPerfect_of_isPerfect_quotient_of_central_exponent_two {G : Type*} [Group G]
    [Finite G] {N : Subgroup G} [N.Normal] (hN : N ≤ Subgroup.center G)
    (hNexp : ∀ n ∈ N, n * n = 1) (hquot : Group.IsPerfect (G ⧸ N))
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hgen : oPPrimeHull p (⊤ : Subgroup G) = ⊤) :
    Group.IsPerfect G := by
  classical
  let K : Subgroup G := commutator G
  let π : G →* G ⧸ N := QuotientGroup.mk' N
  have hmap : K.map π = ⊤ := by
    have h := Group.IsPerfect.commutator_eq_top (G := G ⧸ N)
    rw [show K.map π = commutator (G ⧸ N) from ?_]
    · exact h
    · dsimp only [K, π]
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N),
        commutator_def]
  have hsup : K ⊔ N = ⊤ := by
    rw [eq_top_iff]
    intro g hg
    have hgmap : π g ∈ K.map π := by rw [hmap]; trivial
    obtain ⟨k, hk, hkg⟩ := Subgroup.mem_map.mp hgmap
    have hmem : k⁻¹ * g ∈ N := by
      rw [← QuotientGroup.eq_one_iff (N := N)]
      change π (k⁻¹ * g) = 1
      rw [map_mul, map_inv, hkg, inv_mul_cancel]
    have hgk : g = k * (k⁻¹ * g) := by group
    rw [hgk]
    exact Subgroup.mul_mem_sup hk hmem
  have hsq : ∀ g : G, (QuotientGroup.mk' K g) ^ 2 = 1 :=
    sq_eq_one_quotient_commutator_of_sup hNexp (by simpa [K] using hsup)
  have hcomm : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = (⊤ : Subgroup G) := by
    have hle := oPPrimeHull_le_commutator_of_sq_eq_one hp2 (by simpa [K] using hsq)
    rw [hgen] at hle
    rw [← _root_.commutator_def]
    exact top_le_iff.mp hle
  haveI : Group.IsPerfect ↥(⊤ : Subgroup G) := Subgroup.isPerfect_iff.mpr hcomm
  refine Group.IsPerfect.ofSurjective (f := Subgroup.topEquiv.toMonoidHom) ?_
  simpa using Subgroup.topEquiv.surjective
private theorem split_ker_inf_eq_bot {p : ℕ} [Fact p.Prime] {W : Type} [AddCommGroup W]
    [Module (ZMod p) W] {H : Subgroup (Module.End (ZMod p) W)ˣ}
    {U₁ U₂ : Submodule (ZMod p) W} (hU : IsCompl U₁ U₂)
    (hH₁ : ∀ x ∈ H, ∀ u ∈ U₁, (x : Module.End (ZMod p) W) u ∈ U₁)
    (hH₂ : ∀ x ∈ H, ∀ u ∈ U₂, (x : Module.End (ZMod p) W) u ∈ U₂) :
    (invariantRestrict H U₁ hH₁).ker ⊓ (invariantRestrict H U₂ hH₂).ker = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hx
  apply Subtype.ext
  apply Units.ext
  apply LinearMap.ext
  intro w
  have hw : w ∈ U₁ ⊔ U₂ := by rw [hU.sup_eq_top]; trivial
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hw
  have hu' : ((x : (Module.End (ZMod p) W)ˣ) : Module.End (ZMod p) W) u = u := by
    have h := congrArg (fun e : (Module.End (ZMod p) U₁)ˣ =>
      (e : Module.End (ZMod p) U₁) ⟨u, hu⟩) hx.1
    simp only [Units.val_one, Module.End.one_apply] at h
    exact (coe_invariantRestrict_apply H U₁ hH₁ x ⟨u, hu⟩).symm.trans (congrArg Subtype.val h)
  have hv' : ((x : (Module.End (ZMod p) W)ˣ) : Module.End (ZMod p) W) v = v := by
    have h := congrArg (fun e : (Module.End (ZMod p) U₂)ˣ =>
      (e : Module.End (ZMod p) U₂) ⟨v, hv⟩) hx.2
    simp only [Units.val_one, Module.End.one_apply] at h
    exact (coe_invariantRestrict_apply H U₂ hH₂ x ⟨v, hv⟩).symm.trans (congrArg Subtype.val h)
  rw [map_add, hu', hv']
  simpa using (Module.End.one_apply (u + v)).symm

private theorem split_psi_ker {G K L : Type*} [Group G] [Group K]
    [Group L] (r : G →* K) (e : r.range ≃* L) :
    (e.toMonoidHom.comp r.rangeRestrict).ker = r.ker := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  constructor
  · intro h
    have h' : e (r.rangeRestrict x) = e (1 : ↥r.range) := by rw [map_one]; exact h
    have h2 : r.rangeRestrict x = 1 := e.injective h'
    exact congrArg Subtype.val h2
  · intro h
    have h2 : r.rangeRestrict x = 1 := Subtype.ext h
    show e (r.rangeRestrict x) = 1
    rw [h2, map_one]

private theorem split_psi_surj {G K L : Type*} [Group G] [Group K]
    [Group L] (r : G →* K) (e : r.range ≃* L) :
    Function.Surjective (e.toMonoidHom.comp r.rangeRestrict) := by
  intro y
  obtain ⟨k, hk⟩ := e.surjective y
  obtain ⟨x, hx⟩ := k.2
  refine ⟨x, ?_⟩
  show e (r.rangeRestrict x) = y
  have hk' : r.rangeRestrict x = k := Subtype.ext hx
  rw [hk', hk]

private theorem map_ker_eq_top_symm {G L₁ L₂ : Type*} [Group G] [Group L₁] [Group L₂]
    {ψ₁ : G →* L₁} {ψ₂ : G →* L₂} (hψ₂ : Function.Surjective ψ₂)
    (htop : ψ₂.ker.map ψ₁ = ⊤) : ψ₁.ker.map ψ₂ = ⊤ := by
  rw [eq_top_iff]
  rintro y -
  obtain ⟨x, rfl⟩ := hψ₂ y
  have hx : ψ₁ x ∈ ψ₂.ker.map ψ₁ := by rw [htop]; trivial
  obtain ⟨n, hn, hnx⟩ := Subgroup.mem_map.mp hx
  refine ⟨x * n⁻¹, ?_, ?_⟩
  · change ψ₁ (x * n⁻¹) = 1
    rw [map_mul, map_inv, hnx, mul_inv_cancel]
  · rw [map_mul, map_inv, MonoidHom.mem_ker.mp hn, inv_one, mul_one]

private theorem apply_eq_self_of_mem_ker {W : Type} [AddCommGroup W] [Module (ZMod p) W]
    {H : Subgroup (Module.End (ZMod p) W)ˣ} {T : Submodule (ZMod p) W}
    (hHT : ∀ x ∈ H, ∀ u ∈ T, (x : Module.End (ZMod p) W) u ∈ T)
    {x : ↥H} (hx : x ∈ (invariantRestrict H T hHT).ker) {v : W} (hv : v ∈ T) :
    ((x : (Module.End (ZMod p) W)ˣ) : Module.End (ZMod p) W) v = v := by
  have hx1 : invariantRestrict H T hHT x = 1 := MonoidHom.mem_ker.mp hx
  have h : ((invariantRestrict H T hHT x : (Module.End (ZMod p) T)ˣ) :
      Module.End (ZMod p) T) ⟨v, hv⟩ = ⟨v, hv⟩ := by
    have h1 := congrArg (fun e : (Module.End (ZMod p) T)ˣ =>
      (e : Module.End (ZMod p) T) ⟨v, hv⟩) hx1
    simpa using h1
  have h2 := coe_invariantRestrict_apply H T hHT x ⟨v, hv⟩
  rw [h] at h2
  exact h2.symm

private theorem exists_restrict_eq_neg_one {W : Type} [AddCommGroup W] [Module (ZMod p) W]
    [Module.Finite (ZMod p) W] (hp2 : p ≠ 2) {H : Subgroup (Module.End (ZMod p) W)ˣ}
    {U T : Submodule (ZMod p) W} (hU2 : Module.finrank (ZMod p) U = 2)
    (hHU : ∀ x ∈ H, ∀ u ∈ U, (x : Module.End (ZMod p) W) u ∈ U)
    (hHT : ∀ x ∈ H, ∀ u ∈ T, (x : Module.End (ZMod p) W) u ∈ T)
    (hinv : ∀ S : Submodule (ZMod p) U, (∀ k ∈ (invariantRestrict H U hHU).range, ∀ v ∈ S,
      (k : Module.End (ZMod p) U) v ∈ S) → S = ⊥ ∨ S = ⊤)
    (e : ↥(invariantRestrict H U hHU).range ≃* SL(2, ZMod p))
    (htop : (invariantRestrict H T hHT).ker.map
      (e.toMonoidHom.comp (invariantRestrict H U hHU).rangeRestrict) = ⊤) :
    ∃ n ∈ (invariantRestrict H T hHT).ker, invariantRestrict H U hHU n = -1 := by
  let rU := invariantRestrict H U hHU
  have hmem : CFSG.Quasithin.A1c.sl2NegOne p ∈
      (invariantRestrict H T hHT).ker.map (e.toMonoidHom.comp rU.rangeRestrict) := by
    rw [htop]; trivial
  obtain ⟨n, hn, hψ⟩ := Subgroup.mem_map.mp hmem
  let k : ↥rU.range := rU.rangeRestrict n
  have hψn : e k = CFSG.Quasithin.A1c.sl2NegOne p := hψ
  have hk2 : k * k = 1 := by
    apply e.injective
    rw [map_mul, hψn, CFSG.Quasithin.A1c.sl2NegOne_mul_self, map_one]
  have hσ2 : (rU n) ^ 2 = 1 := by
    have h := congrArg Subtype.val hk2
    rw [pow_two]
    simpa [k] using h
  have hσne : rU n ≠ 1 := by
    intro h1
    have hk1 : k = 1 := Subtype.ext h1
    have h : e k = 1 := by rw [hk1, map_one]
    rw [hψn] at h
    exact CFSG.Quasithin.A1c.sl2NegOne_ne_one hp2 h
  have hσcomm : ∀ k' ∈ rU.range, rU n * k' = k' * rU n := by
    intro k' hk'
    obtain ⟨m, rfl⟩ := hk'
    have hm : rU.rangeRestrict n * rU.rangeRestrict m =
        rU.rangeRestrict m * rU.rangeRestrict n := by
      apply e.injective
      rw [map_mul, map_mul, hψn]
      exact (CFSG.Quasithin.A1c.sl2NegOne_comm (e (rU.rangeRestrict m))).symm
    have h := congrArg Subtype.val hm
    simpa [k] using h
  haveI : NeZero (2 : ZMod p) := ⟨by
    intro h
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hp2le : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega⟩
  exact ⟨n, hn, eq_neg_one_of_involution_of_no_invariant_line hU2 (rU n) hσ2 hσne
    rU.range hσcomm hinv⟩

private theorem exists_orderOf_restrict_eq {W : Type} [AddCommGroup W] [Module (ZMod p) W]
    [Module.Finite (ZMod p) W] {H : Subgroup (Module.End (ZMod p) W)ˣ}
    {U T : Submodule (ZMod p) W}
    (hHU : ∀ x ∈ H, ∀ u ∈ U, (x : Module.End (ZMod p) W) u ∈ U)
    (hHT : ∀ x ∈ H, ∀ u ∈ T, (x : Module.End (ZMod p) W) u ∈ T)
    (e : ↥(invariantRestrict H U hHU).range ≃* SL(2, ZMod p))
    (htop : (invariantRestrict H T hHT).ker.map
      (e.toMonoidHom.comp (invariantRestrict H U hHU).rangeRestrict) = ⊤) :
    ∃ t ∈ (invariantRestrict H T hHT).ker,
      orderOf (invariantRestrict H U hHU t) = p := by
  let rU := invariantRestrict H U hHU
  have hmem : CFSG.Quasithin.A1c.sl2U p ∈
      (invariantRestrict H T hHT).ker.map (e.toMonoidHom.comp rU.rangeRestrict) := by
    rw [htop]; trivial
  obtain ⟨t, ht, hψ⟩ := Subgroup.mem_map.mp hmem
  refine ⟨t, ht, ?_⟩
  let k : ↥rU.range := rU.rangeRestrict t
  have hk : e k = CFSG.Quasithin.A1c.sl2U p := hψ
  have hordk : orderOf k = p := by
    have h1 : orderOf (e k) = orderOf k := MulEquiv.orderOf_eq e k
    rw [hk, CFSG.Quasithin.A1c.orderOf_sl2U (p := p)] at h1
    exact h1.symm
  have h := Subgroup.orderOf_coe k
  rw [hordk] at h
  simpa [k] using h

private theorem orderOf_eq_of_restrict {W : Type} [AddCommGroup W] [Module (ZMod p) W]
    {H : Subgroup (Module.End (ZMod p) W)ˣ} {U T : Submodule (ZMod p) W}
    (hUT : IsCompl U T)
    (hHU : ∀ x ∈ H, ∀ u ∈ U, (x : Module.End (ZMod p) W) u ∈ U)
    (hHT : ∀ x ∈ H, ∀ u ∈ T, (x : Module.End (ZMod p) W) u ∈ T) {t : ↥H}
    (ht : t ∈ (invariantRestrict H T hHT).ker)
    (hto : orderOf (invariantRestrict H U hHU t) = p) :
    orderOf (t : (Module.End (ZMod p) W)ˣ) = p := by
  have hpowT : (t : ↥H) ^ p ∈ (invariantRestrict H T hHT).ker := by
    rw [MonoidHom.mem_ker, map_pow, MonoidHom.mem_ker.mp ht, one_pow]
  have hpowU : (t : ↥H) ^ p ∈ (invariantRestrict H U hHU).ker := by
    rw [MonoidHom.mem_ker, map_pow]
    have hdvd : orderOf ((invariantRestrict H U hHU) t) ∣ p := by
      rw [hto]
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hmem : (t : ↥H) ^ p ∈
      (invariantRestrict H U hHU).ker ⊓ (invariantRestrict H T hHT).ker :=
    Subgroup.mem_inf.mpr ⟨hpowU, hpowT⟩
  rw [split_ker_inf_eq_bot hUT hHU hHT] at hmem
  have hpow1 : (t : ↥H) ^ p = 1 := by simpa using hmem
  have hne : (t : ↥H) ≠ 1 := by
    intro h1
    rw [h1, map_one, orderOf_one] at hto
    exact (Fact.out : p.Prime).one_lt.ne' hto.symm
  have hordH : orderOf (t : ↥H) = p := orderOf_eq_prime hpow1 hne
  have h := Subgroup.orderOf_coe t
  rw [hordH] at h
  exact h

private theorem neg_one_mem_of_restrict {W : Type} [AddCommGroup W] [Module (ZMod p) W]
    {H : Subgroup (Module.End (ZMod p) W)ˣ} {U T : Submodule (ZMod p) W} (hUT : IsCompl U T)
    (hHU : ∀ x ∈ H, ∀ u ∈ U, (x : Module.End (ZMod p) W) u ∈ U)
    (hHT : ∀ x ∈ H, ∀ u ∈ T, (x : Module.End (ZMod p) W) u ∈ T) {n₁ n₂ : ↥H}
    (hn₁ : n₁ ∈ (invariantRestrict H T hHT).ker)
    (hr₁ : invariantRestrict H U hHU n₁ = -1)
    (hn₂ : n₂ ∈ (invariantRestrict H U hHU).ker)
    (hr₂ : invariantRestrict H T hHT n₂ = -1) :
    (-1 : (Module.End (ZMod p) W)ˣ) ∈ H := by
  have hAct : (((n₁ * n₂ : ↥H) : (Module.End (ZMod p) W)ˣ) :
      Module.End (ZMod p) W) = -1 := by
    apply LinearMap.ext_on_codisjoint hUT.codisjoint
    · intro u hu
      rw [Subgroup.coe_mul, Units.val_mul, Module.End.mul_apply]
      have h₂ : ((n₂ : (Module.End (ZMod p) W)ˣ) : Module.End (ZMod p) W) u = u :=
        apply_eq_self_of_mem_ker hHU hn₂ hu
      have h₁ : ((n₁ : (Module.End (ZMod p) W)ˣ) : Module.End (ZMod p) W) u = -u := by
        have h := congrArg (fun e : (Module.End (ZMod p) U)ˣ =>
          (e : Module.End (ZMod p) U) ⟨u, hu⟩) hr₁
        simpa using (coe_invariantRestrict_apply H U hHU n₁ ⟨u, hu⟩).symm.trans
          (congrArg Subtype.val h)
      rw [h₂, h₁]
      simp
    · intro v hv
      rw [Subgroup.coe_mul, Units.val_mul, Module.End.mul_apply]
      have h₁ : ((n₁ : (Module.End (ZMod p) W)ˣ) : Module.End (ZMod p) W) v = v :=
        apply_eq_self_of_mem_ker hHT hn₁ hv
      have h₂ : ((n₂ : (Module.End (ZMod p) W)ˣ) : Module.End (ZMod p) W) v = -v := by
        have h := congrArg (fun e : (Module.End (ZMod p) T)ˣ =>
          (e : Module.End (ZMod p) T) ⟨v, hv⟩) hr₂
        simpa using (coe_invariantRestrict_apply H T hHT n₂ ⟨v, hv⟩).symm.trans
          (congrArg Subtype.val h)
      rw [h₂, map_neg, h₁]
      simp
  have hzUnit : ((n₁ * n₂ : ↥H) : (Module.End (ZMod p) W)ˣ) = -1 := Units.ext hAct
  rw [← hzUnit]
  exact (n₁ * n₂).2

private theorem finrank_eq_two_and_isotropic_of_mem {W : Type} [AddCommGroup W]
    [Module (ZMod p) W] {B : LinearMap.BilinForm (ZMod p) W}
    (hBalt : ∀ w : W, B w w = 0) {U T : Submodule (ZMod p) W} (hUT : U ⊓ T = ⊥)
    (hBUT : ∀ u ∈ U, ∀ v ∈ T, B u v = 0) {v₁ v₂ : W} (hv₁ : v₁ ∈ U) (hv₂ : v₂ ∈ T)
    (hv₁0 : v₁ ≠ 0) (hv₂0 : v₂ ≠ 0) :
    Module.finrank (ZMod p) ↥((ZMod p ∙ v₁) ⊔ (ZMod p ∙ v₂)) = 2 ∧
      ∀ u ∈ (ZMod p ∙ v₁) ⊔ (ZMod p ∙ v₂),
        ∀ v ∈ (ZMod p ∙ v₁) ⊔ (ZMod p ∙ v₂), B u v = 0 := by
  have hinf : (ZMod p ∙ v₁) ⊓ (ZMod p ∙ v₂) = ⊥ := by
    rw [eq_bot_iff]
    calc (ZMod p ∙ v₁) ⊓ (ZMod p ∙ v₂) ≤ U ⊓ T :=
          inf_le_inf ((Submodule.span_singleton_le_iff_mem v₁ U).mpr hv₁)
            ((Submodule.span_singleton_le_iff_mem v₂ T).mpr hv₂)
      _ = ⊥ := hUT
  have hfin : Module.finrank (ZMod p) ↥((ZMod p ∙ v₁) ⊔ (ZMod p ∙ v₂)) = 2 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (ZMod p ∙ v₁) (ZMod p ∙ v₂)
    rw [hinf, finrank_span_singleton hv₁0, finrank_span_singleton hv₂0] at h
    have hbot : Module.finrank (ZMod p) (⊥ : Submodule (ZMod p) W) = 0 :=
      (Submodule.finrank_eq_zero (R := ZMod p)).mpr rfl
    rw [hbot] at h
    omega
  have hBskew : ∀ u v : W, B u v = -B v u := by
    intro u v
    have h := hBalt (u + v)
    simp only [map_add, LinearMap.add_apply, hBalt, zero_add, add_zero] at h
    exact eq_neg_of_add_eq_zero_right h
  refine ⟨hfin, ?_⟩
  intro x hx y hy
  rw [Submodule.mem_sup] at hx hy
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := hx
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := hy
  rw [Submodule.mem_span_singleton] at hx₁ hx₂ hy₁ hy₂
  obtain ⟨a, rfl⟩ := hx₁
  obtain ⟨b, rfl⟩ := hx₂
  obtain ⟨c, rfl⟩ := hy₁
  obtain ⟨d, rfl⟩ := hy₂
  have h11 : B v₁ v₁ = 0 := hBalt _
  have h12 : B v₁ v₂ = 0 := hBUT v₁ hv₁ v₂ hv₂
  have h21 : B v₂ v₁ = 0 := by rw [hBskew, h12]; exact neg_zero
  have h22 : B v₂ v₂ = 0 := hBalt _
  simp only [map_add, LinearMap.map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, h11, h12, h21, h22, mul_zero, add_zero]

private theorem isElemAbelian_and_card_sup_zpowers {G : Type*} [Group G] {a b : G}
    (hab : a * b = b * a) (ha : orderOf a = p) (hb : orderOf b = p)
    (hdisj : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥) :
    CFSG.Open.IsElemAbelian p (Subgroup.zpowers a ⊔ Subgroup.zpowers b) ∧
      Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b) = p ^ 2 := by
  have hap : a ^ p = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have hbp : b ^ p = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
  have hcomm : ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ Subgroup.zpowers b, x * y = y * x := by
    intro x hx y hy
    rw [Subgroup.mem_zpowers_iff] at hx hy
    obtain ⟨m, rfl⟩ := hx
    obtain ⟨n, rfl⟩ := hy
    exact (Commute.zpow_zpow ((commute_iff_eq _ _).mpr hab) m n).eq
  have hEa : CFSG.Open.IsElemAbelian p (Subgroup.zpowers a) :=
    CFSG.Open.isElemAbelian_zpowers hap
  have hEb : CFSG.Open.IsElemAbelian p (Subgroup.zpowers b) :=
    CFSG.Open.isElemAbelian_zpowers hbp
  have hnorm : Subgroup.zpowers b ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer (Subgroup.zpowers a : Set G))
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hcomm y hy x hx
  refine ⟨CFSG.Open.IsElemAbelian.sup_of_commute hEa hEb hcomm, ?_⟩
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnorm
    (disjoint_iff.mpr hdisj), Nat.card_zpowers, Nat.card_zpowers, ha, hb, pow_two]

private theorem fixes_sup_span {W : Type} [AddCommGroup W] [Module (ZMod p) W]
    {g : Module.End (ZMod p) W} {v₁ v₂ : W} (h₁ : g v₁ = v₁) (h₂ : g v₂ = v₂) :
    ∀ u ∈ (ZMod p ∙ v₁) ⊔ (ZMod p ∙ v₂), g u = u := by
  have hle : (ZMod p ∙ v₁) ⊔ (ZMod p ∙ v₂) ≤ LinearMap.ker (g - 1) := by
    refine sup_le ?_ ?_
    · rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker, LinearMap.sub_apply,
        Module.End.one_apply, h₁, sub_self]
    · rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker, LinearMap.sub_apply,
        Module.End.one_apply, h₂, sub_self]
  intro u hu
  have h := hle hu
  rwa [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h

private theorem hasIsotropicPlaneGroup_of_elements {W : Type} [AddCommGroup W]
    [Module (ZMod p) W] [Module.Finite (ZMod p) W]
    {B : LinearMap.BilinForm (ZMod p) W} (hBalt : ∀ w : W, B w w = 0)
    {H : Subgroup (Module.End (ZMod p) W)ˣ} {U₁ U₂ : Submodule (ZMod p) W}
    (hU : IsCompl U₁ U₂) (hB12 : ∀ u ∈ U₁, ∀ v ∈ U₂, B u v = 0)
    {t₁ t₂ : ↥H} {v₁ v₂ : W}
    (hv₁ : v₁ ∈ U₁) (hv₂ : v₂ ∈ U₂) (hv₁0 : v₁ ≠ 0) (hv₂0 : v₂ ≠ 0)
    (ht₁ord : orderOf ((t₁ : ↥H) : (Module.End (ZMod p) W)ˣ) = p)
    (ht₂ord : orderOf ((t₂ : ↥H) : (Module.End (ZMod p) W)ˣ) = p)
    (hcommH : (t₁ : ↥H) * t₂ = t₂ * t₁)
    (hdisjH : Subgroup.zpowers t₁ ⊓ Subgroup.zpowers t₂ = ⊥)
    (hfix₁ : ((t₁ : (Module.End (ZMod p) W)ˣ) : Module.End (ZMod p) W) v₁ = v₁)
    (hfix₂ : ((t₂ : (Module.End (ZMod p) W)ˣ) : Module.End (ZMod p) W) v₂ = v₂)
    (hfix₁₂ : ∀ v ∈ U₂, ((t₁ : (Module.End (ZMod p) W)ˣ) : Module.End (ZMod p) W) v = v)
    (hfix₂₁ : ∀ v ∈ U₁, ((t₂ : (Module.End (ZMod p) W)ˣ) : Module.End (ZMod p) W) v = v)
    (hnegOne : (-1 : (Module.End (ZMod p) W)ˣ) ∈ H) :
    HasIsotropicPlaneGroup p B H := by
  let E : Subgroup (Module.End (ZMod p) W)ˣ :=
    Subgroup.zpowers ((t₁ : (Module.End (ZMod p) W)ˣ)) ⊔
      Subgroup.zpowers ((t₂ : (Module.End (ZMod p) W)ˣ))
  let π : Submodule (ZMod p) W := (ZMod p ∙ v₁) ⊔ (ZMod p ∙ v₂)
  have hcomm : ((t₁ : (Module.End (ZMod p) W)ˣ)) * ((t₂ : (Module.End (ZMod p) W)ˣ)) =
      ((t₂ : (Module.End (ZMod p) W)ˣ)) * ((t₁ : (Module.End (ZMod p) W)ˣ)) :=
    congrArg (fun z : ↥H => (z : (Module.End (ZMod p) W)ˣ)) hcommH
  have hdisj : Subgroup.zpowers ((t₁ : (Module.End (ZMod p) W)ˣ)) ⊓
      Subgroup.zpowers ((t₂ : (Module.End (ZMod p) W)ˣ)) = ⊥ := by
    change Subgroup.zpowers ((Subgroup.subtype H) t₁) ⊓
      Subgroup.zpowers ((Subgroup.subtype H) t₂) = ⊥
    rw [← MonoidHom.map_zpowers (Subgroup.subtype H) t₁,
      ← MonoidHom.map_zpowers (Subgroup.subtype H) t₂,
      ← Subgroup.map_inf _ _ (Subgroup.subtype H) (Subgroup.subtype_injective H),
      hdisjH, Subgroup.map_bot]
  have hE_le : E ≤ H := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]; exact t₁.2
    · rw [Subgroup.zpowers_le]; exact t₂.2
  obtain ⟨hEea, hEcard⟩ :=
    isElemAbelian_and_card_sup_zpowers hcomm ht₁ord ht₂ord hdisj
  obtain ⟨hπfin, hπiso⟩ := finrank_eq_two_and_isotropic_of_mem hBalt hU.inf_eq_bot hB12
    hv₁ hv₂ hv₁0 hv₂0
  have hfix₁' : ∀ u ∈ π,
      ((t₁ : (Module.End (ZMod p) W)ˣ) : Module.End (ZMod p) W) u = u :=
    fixes_sup_span hfix₁ (hfix₁₂ v₂ hv₂)
  have hfix₂' : ∀ u ∈ π,
      ((t₂ : (Module.End (ZMod p) W)ˣ) : Module.End (ZMod p) W) u = u :=
    fixes_sup_span (hfix₂₁ v₁ hv₁) hfix₂
  let Fix : Subgroup (Module.End (ZMod p) W)ˣ :=
    { carrier := {g | ∀ u ∈ π, (g : Module.End (ZMod p) W) u = u}
      one_mem' := fun u _ => Module.End.one_apply u
      mul_mem' := fun {g h} hg hh u hu => by
        rw [Units.val_mul, Module.End.mul_apply, hh u hu, hg u hu]
      inv_mem' := fun {g} hg u hu => by
        have h1 : (g⁻¹ * g : (Module.End (ZMod p) W)ˣ) = 1 := inv_mul_cancel g
        have h2 : ((g⁻¹ : (Module.End (ZMod p) W)ˣ) : Module.End (ZMod p) W)
            ((g : Module.End (ZMod p) W) u) = u := by
          rw [← Module.End.mul_apply, ← Units.val_mul, h1, Units.val_one,
            Module.End.one_apply]
        rwa [hg u hu] at h2 }
  have hEfix : E ≤ Fix :=
    sup_le (Subgroup.zpowers_le.mpr hfix₁') (Subgroup.zpowers_le.mpr hfix₂')
  exact ⟨hnegOne, E, hE_le, hEea, hEcard, π, hπfin, hπiso,
    fun e he u hu => hEfix he u hu⟩

private theorem zpowers_inf_zpowers_eq_bot_of_mem {G : Type*} [Group G]
    {N₁ N₂ : Subgroup G} (hN₁ : N₁.Normal) (hN₂ : N₂.Normal)
    (hdisj : N₁ ⊓ N₂ = ⊥) {a b : G} (ha : a ∈ N₁) (hb : b ∈ N₂) :
    Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  have hx₁ : x ∈ N₁ := Subgroup.zpowers_le.mpr ha hx.1
  have hx₂ : x ∈ N₂ := Subgroup.zpowers_le.mpr hb hx.2
  have hmem : x ∈ N₁ ⊓ N₂ := Subgroup.mem_inf.mpr ⟨hx₁, hx₂⟩
  rw [hdisj] at hmem
  simpa using hmem

private theorem eq_bot_or_top_of_invariant_of_no_isotropic {W : Type} [AddCommGroup W]
    [Module (ZMod p) W] [Module.Finite (ZMod p) W] {B : LinearMap.BilinForm (ZMod p) W}
    (hBalt : ∀ w : W, B w w = 0) {H : Subgroup (Module.End (ZMod p) W)ˣ}
    {U : Submodule (ZMod p) W}
    (hHU : ∀ x ∈ H, ∀ u ∈ U, (x : Module.End (ZMod p) W) u ∈ U)
    (hU : Module.finrank (ZMod p) U = 2)
    (hno : ∀ T : Submodule (ZMod p) W, T ≠ ⊥ → (∀ u ∈ T, ∀ v ∈ T, B u v = 0) →
      ¬ ∀ x ∈ H, ∀ u ∈ T, (x : Module.End (ZMod p) W) u ∈ T) :
    ∀ S : Submodule (ZMod p) U, (∀ k ∈ (invariantRestrict H U hHU).range, ∀ v ∈ S,
      (k : Module.End (ZMod p) U) v ∈ S) → S = ⊥ ∨ S = ⊤ := by
  intro S hS
  by_cases h : S = ⊥
  · exact Or.inl h
  · exact Or.inr (forall_invariant_eq_top_of_no_isotropic hBalt hHU hU hno S h hS)

private theorem le_center_and_mul_self_of_map_le_center {G : Type*} [Group G]
    {p : ℕ} [Fact p.Prime] {N : Subgroup G} [N.Normal] {ψ : G →* SL(2, ZMod p)}
    (hdisj : N ⊓ ψ.ker = ⊥)
    (hZ : N.map ψ ≤ Subgroup.center (SL(2, ZMod p))) :
    N ≤ Subgroup.center G ∧ ∀ n ∈ N, n * n = 1 := by
  constructor
  · intro n hn
    rw [Subgroup.mem_center_iff]
    intro x
    have hcomm₁ : ⁅n, x⁆ ∈ N := by
      rw [commutatorElement_def,
        show n * x * n⁻¹ * x⁻¹ = n * (x * n⁻¹ * x⁻¹) by group]
      exact N.mul_mem hn ((inferInstance : N.Normal).conj_mem n⁻¹ (N.inv_mem hn) x)
    have hψ : ψ ⁅n, x⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.mp (hZ (Subgroup.mem_map_of_mem ψ hn)) (ψ x)).symm
    have hcomm₂ : ⁅n, x⁆ ∈ ψ.ker := MonoidHom.mem_ker.mpr hψ
    have h1 : ⁅n, x⁆ = 1 := by
      have hmem : ⁅n, x⁆ ∈ N ⊓ ψ.ker := Subgroup.mem_inf.mpr ⟨hcomm₁, hcomm₂⟩
      rw [hdisj] at hmem
      simpa using hmem
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  · intro n hn
    have hmem₁ : n * n ∈ N := N.mul_mem hn hn
    have hψsq : ψ (n * n) = 1 := by
      rw [map_mul]
      rcases CFSG.Quasithin.A1c.eq_one_or_eq_sl2NegOne_of_mem_center
        (hZ (Subgroup.mem_map_of_mem ψ hn)) with h | h
      · rw [h, one_mul]
      · rw [h, CFSG.Quasithin.A1c.sl2NegOne_mul_self]
    have hmem₂ : n * n ∈ ψ.ker := MonoidHom.mem_ker.mpr hψsq
    have hmem : n * n ∈ N ⊓ ψ.ker := Subgroup.mem_inf.mpr ⟨hmem₁, hmem₂⟩
    rw [hdisj] at hmem
    simpa using hmem

private theorem eq_bot_of_isPerfect_of_le_center {G : Type} [Group G] [Finite G]
    {N : Subgroup G} [N.Normal] (hperf : Group.IsPerfect G)
    (hNcenter : N ≤ Subgroup.center G)
    {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {ψ : G →* SL(2, ZMod p)}
    (hψsurj : Function.Surjective ψ) (hψker : ψ.ker = N) : N = ⊥ := by
  haveI := hperf
  have hPKQ : ⁅N, (⊤ : Subgroup G)⁆ ≤ ⊥ := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp (hNcenter ha) b).symm
  have hmap : ∃ φ : ↥(⊤ : Subgroup G) →* SL(2, ZMod p),
      Function.Surjective φ ∧ φ.ker = N.subgroupOf ⊤ := by
    refine ⟨ψ.comp (⊤ : Subgroup G).subtype, ?_, ?_⟩
    · intro y
      obtain ⟨x, hx⟩ := hψsurj y
      exact ⟨⟨x, trivial⟩, hx⟩
    · ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.comp_apply]
      show ψ (x : G) = 1 ↔ (x : G) ∈ N
      rw [← hψker]
      exact MonoidHom.mem_ker
  obtain ⟨φ, hφsurj, hφker⟩ := hmap
  exact CFSG.Quasithin.Vol2.Ch11.SecD.sl2pMultFact_holds G (⊤ : Subgroup G) N ⊥ p
    (Fact.out) hp5 Group.IsPerfect.commutator_eq_top bot_le le_top
    (by rw [Subgroup.normalizer_eq_top]) (by rw [Subgroup.normalizer_eq_top])
    (by simpa using hPKQ) ⟨φ, hφsurj, hφker⟩

private theorem caseA {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {W : Type} [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W]
    {B : LinearMap.BilinForm (ZMod p) W} {H : Subgroup (Module.End (ZMod p) W)ˣ}
    {U₁ U₂ : Submodule (ZMod p) W}
    (hBalt : ∀ w : W, B w w = 0) (hH : oPPrimeHull p H = H)
    (hU : IsCompl U₁ U₂) (hU₁ : Module.finrank (ZMod p) U₁ = 2)
    (hU₂ : Module.finrank (ZMod p) U₂ = 2) (hB12 : ∀ u ∈ U₁, ∀ v ∈ U₂, B u v = 0)
    (hH₁ : ∀ x ∈ H, ∀ u ∈ U₁, (x : Module.End (ZMod p) W) u ∈ U₁)
    (hH₂ : ∀ x ∈ H, ∀ u ∈ U₂, (x : Module.End (ZMod p) W) u ∈ U₂)
    (hno : ∀ T : Submodule (ZMod p) W, T ≠ ⊥ → (∀ u ∈ T, ∀ v ∈ T, B u v = 0) →
      ¬ ∀ x ∈ H, ∀ u ∈ T, (x : Module.End (ZMod p) W) u ∈ T)
    {e₁ : ↥(invariantRestrict H U₁ hH₁).range ≃* SL(2, ZMod p)}
    {e₂ : ↥(invariantRestrict H U₂ hH₂).range ≃* SL(2, ZMod p)}
    (hψ₁ker : (e₁.toMonoidHom.comp (invariantRestrict H U₁ hH₁).rangeRestrict).ker =
      (invariantRestrict H U₁ hH₁).ker)
    (hψ₂ker : (e₂.toMonoidHom.comp (invariantRestrict H U₂ hH₂).rangeRestrict).ker =
      (invariantRestrict H U₂ hH₂).ker)
    (hψ₁surj : Function.Surjective (e₁.toMonoidHom.comp
      (invariantRestrict H U₁ hH₁).rangeRestrict))
    (hψ₂surj : Function.Surjective (e₂.toMonoidHom.comp
      (invariantRestrict H U₂ hH₂).rangeRestrict))
    (hdisj : (invariantRestrict H U₂ hH₂).ker ⊓ (invariantRestrict H U₁ hH₁).ker = ⊥)
    (hZ : (invariantRestrict H U₂ hH₂).ker.map
      (e₁.toMonoidHom.comp (invariantRestrict H U₁ hH₁).rangeRestrict) ≤
      Subgroup.center (SL(2, ZMod p))) :
    SixThreeOneList p (↥H ⧸ CFSG.pCore p ↥H) := by
  let r₁ : ↥H →* (Module.End (ZMod p) U₁)ˣ := invariantRestrict H U₁ hH₁
  let r₂ : ↥H →* (Module.End (ZMod p) U₂)ˣ := invariantRestrict H U₂ hH₂
  let N₁ : Subgroup ↥H := r₂.ker
  let N₂ : Subgroup ↥H := r₁.ker
  let ψ₁ : ↥H →* SL(2, ZMod p) := e₁.toMonoidHom.comp r₁.rangeRestrict
  let ψ₂ : ↥H →* SL(2, ZMod p) := e₂.toMonoidHom.comp r₂.rangeRestrict
  haveI : N₁.Normal := MonoidHom.normal_ker r₂
  have hp2 : p ≠ 2 := by omega
  have hψ₁ker : ψ₁.ker = N₂ := hψ₁ker
  have hψ₂ker : ψ₂.ker = N₁ := hψ₂ker
  have hdisj : N₁ ⊓ N₂ = ⊥ := hdisj
  have hZ : N₁.map ψ₁ ≤ Subgroup.center (SL(2, ZMod p)) := hZ
  obtain ⟨hN₁center, hN₁exp⟩ := le_center_and_mul_self_of_map_le_center (ψ := ψ₁)
    (by rw [hψ₁ker]; exact hdisj) hZ
  have hquotPerfect : Group.IsPerfect (↥H ⧸ N₁) := by
    haveI : Group.IsPerfect (SL(2, ZMod p)) := CFSG.Quasithin.A1c.sl2_isPerfect hp5
    have hq : ↥H ⧸ N₁ ≃* SL(2, ZMod p) :=
      (QuotientGroup.quotientMulEquivOfEq hψ₂ker).symm.trans
        (QuotientGroup.quotientKerEquivOfSurjective ψ₂ hψ₂surj)
    exact Group.IsPerfect.ofSurjective (f := hq.symm.toMonoidHom) hq.symm.surjective
  have hHperfect : Group.IsPerfect ↥H :=
    isPerfect_of_isPerfect_quotient_of_central_exponent_two (p := p) hN₁center hN₁exp
      hquotPerfect hp2 (oPPrimeHull_top_of_eq hH)
  have hN₁bot : N₁ = ⊥ :=
    eq_bot_of_isPerfect_of_le_center hHperfect hN₁center hp5 hψ₂surj hψ₂ker
  have hψ₂inj : Function.Injective ψ₂ := by
    rw [← MonoidHom.ker_eq_bot_iff, hψ₂ker, hN₁bot]
  let e₂' : ↥H ≃* SL(2, ZMod p) := MulEquiv.ofBijective ψ₂ ⟨hψ₂inj, hψ₂surj⟩
  have hpcoreSL : CFSG.pCore p (SL(2, ZMod p)) = ⊥ := CFSG.Glauberman.qdSL_pCore_eq_bot p hp2
  obtain ⟨E⟩ := nonempty_quot_pCore_mulEquiv_of_mulEquiv (p := p) e₂'
  have hSL : IsSLType 2 (ZMod p) (↥H ⧸ CFSG.pCore p ↥H) :=
    ⟨E.trans ((QuotientGroup.quotientMulEquivOfEq hpcoreSL).trans
      QuotientGroup.quotientBot)⟩
  exact Or.inl (Or.inl hSL)

private theorem caseB {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {W : Type} [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W]
    {B : LinearMap.BilinForm (ZMod p) W} {H : Subgroup (Module.End (ZMod p) W)ˣ}
    {U₁ U₂ : Submodule (ZMod p) W}
    (hBalt : ∀ w : W, B w w = 0) (hH : oPPrimeHull p H = H)
    (hU : IsCompl U₁ U₂) (hU₁ : Module.finrank (ZMod p) U₁ = 2)
    (hU₂ : Module.finrank (ZMod p) U₂ = 2) (hB12 : ∀ u ∈ U₁, ∀ v ∈ U₂, B u v = 0)
    (hH₁ : ∀ x ∈ H, ∀ u ∈ U₁, (x : Module.End (ZMod p) W) u ∈ U₁)
    (hH₂ : ∀ x ∈ H, ∀ u ∈ U₂, (x : Module.End (ZMod p) W) u ∈ U₂)
    (hno : ∀ T : Submodule (ZMod p) W, T ≠ ⊥ → (∀ u ∈ T, ∀ v ∈ T, B u v = 0) →
      ¬ ∀ x ∈ H, ∀ u ∈ T, (x : Module.End (ZMod p) W) u ∈ T)
    {e₁ : ↥(invariantRestrict H U₁ hH₁).range ≃* SL(2, ZMod p)}
    {e₂ : ↥(invariantRestrict H U₂ hH₂).range ≃* SL(2, ZMod p)}
    (hψ₁ker : (e₁.toMonoidHom.comp (invariantRestrict H U₁ hH₁).rangeRestrict).ker =
      (invariantRestrict H U₁ hH₁).ker)
    (hψ₂ker : (e₂.toMonoidHom.comp (invariantRestrict H U₂ hH₂).rangeRestrict).ker =
      (invariantRestrict H U₂ hH₂).ker)
    (hψ₁surj : Function.Surjective (e₁.toMonoidHom.comp
      (invariantRestrict H U₁ hH₁).rangeRestrict))
    (hψ₂surj : Function.Surjective (e₂.toMonoidHom.comp
      (invariantRestrict H U₂ hH₂).rangeRestrict))
    (hdisj : (invariantRestrict H U₂ hH₂).ker ⊓ (invariantRestrict H U₁ hH₁).ker = ⊥)
    (htop : (invariantRestrict H U₂ hH₂).ker.map
      (e₁.toMonoidHom.comp (invariantRestrict H U₁ hH₁).rangeRestrict) = ⊤) :
    HasIsotropicPlaneGroup p B H := by
  let r₁ : ↥H →* (Module.End (ZMod p) U₁)ˣ := invariantRestrict H U₁ hH₁
  let r₂ : ↥H →* (Module.End (ZMod p) U₂)ˣ := invariantRestrict H U₂ hH₂
  let N₁ : Subgroup ↥H := r₂.ker
  let N₂ : Subgroup ↥H := r₁.ker
  have hp2 : p ≠ 2 := by omega
  have htop₂ : (invariantRestrict H U₁ hH₁).ker.map
      (e₂.toMonoidHom.comp (invariantRestrict H U₂ hH₂).rangeRestrict) = ⊤ := by
    rw [← split_psi_ker r₁ e₁]
    exact map_ker_eq_top_symm hψ₂surj (by rw [hψ₂ker]; exact htop)
  have hinvK₁ := eq_bot_or_top_of_invariant_of_no_isotropic (U := U₁) hBalt hH₁ hU₁ hno
  have hinvK₂ := eq_bot_or_top_of_invariant_of_no_isotropic (U := U₂) hBalt hH₂ hU₂ hno
  obtain ⟨n₁, hn₁, hr₁⟩ := exists_restrict_eq_neg_one hp2 hU₁ hH₁ hH₂ hinvK₁ e₁ htop
  obtain ⟨n₂, hn₂, hr₂⟩ := exists_restrict_eq_neg_one hp2 hU₂ hH₂ hH₁ hinvK₂ e₂ htop₂
  have hnegOne := neg_one_mem_of_restrict hU hH₁ hH₂ hn₁ hr₁ hn₂ hr₂
  obtain ⟨t₁, ht₁, hto₁⟩ := exists_orderOf_restrict_eq hH₁ hH₂ e₁ htop
  obtain ⟨t₂, ht₂, hto₂⟩ := exists_orderOf_restrict_eq hH₂ hH₁ e₂ htop₂
  have ht₁ord : orderOf ((t₁ : ↥H) : (Module.End (ZMod p) W)ˣ) = p :=
    orderOf_eq_of_restrict hU hH₁ hH₂ ht₁ hto₁
  have ht₂ord : orderOf ((t₂ : ↥H) : (Module.End (ZMod p) W)ˣ) = p :=
    orderOf_eq_of_restrict hU.symm hH₂ hH₁ ht₂ hto₂
  have hcommH : (t₁ : ↥H) * t₂ = t₂ * t₁ :=
    (Subgroup.commute_of_normal_of_disjoint N₁ N₂ (MonoidHom.normal_ker r₂)
      (MonoidHom.normal_ker r₁) (disjoint_iff.mpr hdisj) t₁ t₂ ht₁ ht₂).eq
  have hzdisjH : Subgroup.zpowers t₁ ⊓ Subgroup.zpowers t₂ = ⊥ :=
    zpowers_inf_zpowers_eq_bot_of_mem (MonoidHom.normal_ker r₂) (MonoidHom.normal_ker r₁)
      hdisj ht₁ ht₂
  have hpos₁ : 0 < Module.finrank (ZMod p) U₁ := by omega
  have hpos₂ : 0 < Module.finrank (ZMod p) U₂ := by omega
  haveI : Nontrivial U₁ := Module.finrank_pos_iff.mp hpos₁
  haveI : Nontrivial U₂ := Module.finrank_pos_iff.mp hpos₂
  obtain ⟨v₁, hv₁0, hv₁fix⟩ := exists_fixed_of_orderOf_eq_prime (p := p) (r₁ t₁) hto₁
  obtain ⟨v₂, hv₂0, hv₂fix⟩ := exists_fixed_of_orderOf_eq_prime (p := p) (r₂ t₂) hto₂
  have hv₁W : ((t₁ : (Module.End (ZMod p) W)ˣ) : Module.End (ZMod p) W) (v₁ : W) = v₁ := by
    rw [← coe_invariantRestrict_apply H U₁ hH₁ (t₁ : ↥H) v₁]
    exact congrArg Subtype.val hv₁fix
  have hv₂W : ((t₂ : (Module.End (ZMod p) W)ˣ) : Module.End (ZMod p) W) (v₂ : W) = v₂ := by
    rw [← coe_invariantRestrict_apply H U₂ hH₂ (t₂ : ↥H) v₂]
    exact congrArg Subtype.val hv₂fix
  have ht₁U₂ : ∀ v ∈ U₂, ((t₁ : (Module.End (ZMod p) W)ˣ) : Module.End (ZMod p) W) v = v :=
    fun v hv => apply_eq_self_of_mem_ker hH₂ ht₁ hv
  have ht₂U₁ : ∀ v ∈ U₁, ((t₂ : (Module.End (ZMod p) W)ˣ) : Module.End (ZMod p) W) v = v :=
    fun v hv => apply_eq_self_of_mem_ker hH₁ ht₂ hv
  exact hasIsotropicPlaneGroup_of_elements hBalt hU hB12 v₁.2 v₂.2
    (fun h => hv₁0 (Subtype.ext h)) (fun h => hv₂0 (Subtype.ext h))
    ht₁ord ht₂ord hcommH hzdisjH hv₁W hv₂W ht₁U₂ ht₂U₁ hnegOne

theorem sixThreeOneList_or_hasIsotropicPlaneGroup_of_planes {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {W : Type} [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W]
    (B : LinearMap.BilinForm (ZMod p) W) (hBalt : ∀ w : W, B w w = 0)
    {H : Subgroup (Module.End (ZMod p) W)ˣ} (hH : oPPrimeHull p H = H)
    {U₁ U₂ : Submodule (ZMod p) W} (hU : IsCompl U₁ U₂) (hU₁ : Module.finrank (ZMod p) U₁ = 2)
    (hU₂ : Module.finrank (ZMod p) U₂ = 2) (hB12 : ∀ u ∈ U₁, ∀ v ∈ U₂, B u v = 0)
    (hH₁ : ∀ x ∈ H, ∀ u ∈ U₁, (x : Module.End (ZMod p) W) u ∈ U₁)
    (hH₂ : ∀ x ∈ H, ∀ u ∈ U₂, (x : Module.End (ZMod p) W) u ∈ U₂)
    (hno : ∀ T : Submodule (ZMod p) W, T ≠ ⊥ → (∀ u ∈ T, ∀ v ∈ T, B u v = 0) →
      ¬ ∀ x ∈ H, ∀ u ∈ T, (x : Module.End (ZMod p) W) u ∈ T) :
    SixThreeOneList p (↥H ⧸ CFSG.pCore p ↥H) ∨ HasIsotropicPlaneGroup p B H := by
  classical
  haveI : Finite W := Module.finite_of_finite (ZMod p)
  have hp2 : p ≠ 2 := by omega
  let r₁ : ↥H →* (Module.End (ZMod p) U₁)ˣ := invariantRestrict H U₁ hH₁
  let r₂ : ↥H →* (Module.End (ZMod p) U₂)ˣ := invariantRestrict H U₂ hH₂
  let K₁ : Subgroup (Module.End (ZMod p) U₁)ˣ := r₁.range
  let K₂ : Subgroup (Module.End (ZMod p) U₂)ˣ := r₂.range
  let N₁ : Subgroup ↥H := r₂.ker
  let N₂ : Subgroup ↥H := r₁.ker
  have hK₁gen : oPPrimeHull p K₁ = K₁ := by
    have h := oPPrimeHull_map_eq (p := p) (H := (⊤ : Subgroup ↥H)) r₁
      (oPPrimeHull_top_of_eq hH)
    simpa [K₁, MonoidHom.range_eq_map] using h
  have hK₂gen : oPPrimeHull p K₂ = K₂ := by
    have h := oPPrimeHull_map_eq (p := p) (H := (⊤ : Subgroup ↥H)) r₂
      (oPPrimeHull_top_of_eq hH)
    simpa [K₂, MonoidHom.range_eq_map] using h
  have hnoK₁ : ∀ T : Submodule (ZMod p) U₁, T ≠ ⊥ →
      (∀ k ∈ K₁, ∀ v ∈ T, (k : Module.End (ZMod p) U₁) v ∈ T) → T = ⊤ :=
    forall_invariant_eq_top_of_no_isotropic (p := p) (H := H) (U := U₁) hBalt hH₁ hU₁ hno
  have hnoK₂ : ∀ T : Submodule (ZMod p) U₂, T ≠ ⊥ →
      (∀ k ∈ K₂, ∀ v ∈ T, (k : Module.End (ZMod p) U₂) v ∈ T) → T = ⊤ :=
    forall_invariant_eq_top_of_no_isotropic (p := p) (H := H) (U := U₂) hBalt hH₂ hU₂ hno
  obtain ⟨e₁⟩ := exists_mulEquiv_sl2_of_no_invariant_line (p := p) hK₁gen hU₁ hnoK₁
  obtain ⟨e₂⟩ := exists_mulEquiv_sl2_of_no_invariant_line (p := p) hK₂gen hU₂ hnoK₂
  let ψ₁ : ↥H →* SL(2, ZMod p) := e₁.toMonoidHom.comp r₁.rangeRestrict
  let ψ₂ : ↥H →* SL(2, ZMod p) := e₂.toMonoidHom.comp r₂.rangeRestrict
  have hψ₁ker : ψ₁.ker = N₂ := split_psi_ker r₁ e₁
  have hψ₂ker : ψ₂.ker = N₁ := split_psi_ker r₂ e₂
  have hψ₁surj : Function.Surjective ψ₁ := split_psi_surj r₁ e₁
  have hψ₂surj : Function.Surjective ψ₂ := split_psi_surj r₂ e₂
  have hdisj : N₁ ⊓ N₂ = ⊥ := by
    dsimp only [N₁, N₂]
    rw [inf_comm]
    exact split_ker_inf_eq_bot hU hH₁ hH₂
  have hmapNormal : (N₁.map ψ₁).Normal :=
    (MonoidHom.normal_ker r₂).map ψ₁ hψ₁surj
  rcases CFSG.Quasithin.A1c.normal_le_center_or_eq_top hp5 (N₁.map ψ₁) with hZ | htop
  · exact Or.inl (caseA hp5 hBalt hH hU hU₁ hU₂ hB12 hH₁ hH₂ hno (e₁ := e₁) (e₂ := e₂)
      hψ₁ker hψ₂ker hψ₁surj hψ₂surj hdisj hZ)
  · exact Or.inr (caseB hp5 hBalt hH hU hU₁ hU₂ hB12 hH₁ hH₂ hno (e₁ := e₁) (e₂ := e₂)
      hψ₁ker hψ₂ker hψ₁surj hψ₂surj hdisj htop)
end CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631
