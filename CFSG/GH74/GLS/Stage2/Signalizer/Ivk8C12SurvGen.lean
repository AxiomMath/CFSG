module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8YCfg
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87NatMod
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8C12Mono
public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Defs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup Matrix CFSG CFSG.Open CFSG.ABGLocalTools CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

section Stated

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

@[expose] noncomputable def statedRho (H : Subgroup (GL ι K)) :
    ↥H →* ((ι → K) ≃ₗ[K] (ι → K)) :=
  ((LinearMap.GeneralLinearGroup.generalLinearEquiv K (ι → K)).toMonoidHom.comp
    (Matrix.GeneralLinearGroup.toLin (n := ι) (R := K)).toMonoidHom).comp H.subtype

theorem statedRho_apply (H : Subgroup (GL ι K)) (g : ↥H) (v : ι → K) :
    statedRho H g v = ((g : GL ι K) : Matrix ι ι K) *ᵥ v :=
  rfl

theorem statedRho_injective (H : Subgroup (GL ι K)) : Function.Injective (statedRho H) := by
  intro a b hab
  apply Subtype.ext
  have h1 : (LinearMap.GeneralLinearGroup.generalLinearEquiv K (ι → K)).toMonoidHom
      (Matrix.GeneralLinearGroup.toLin (n := ι) (R := K) (a : GL ι K)) =
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (ι → K)).toMonoidHom
      (Matrix.GeneralLinearGroup.toLin (n := ι) (R := K) (b : GL ι K)) :=
    hab
  exact Matrix.GeneralLinearGroup.toLin.injective
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv K (ι → K)).injective h1)

theorem exists_proper_invariant_subspace_stated [Finite K] {r : ℕ} [Fact r.Prime] [CharP K r]
    (H : Subgroup (GL ι K)) {X : Subgroup (StatedProj H)} (hX : IsPGroup r ↥X) (hX1 : X ≠ ⊥)
    {C : Subgroup (StatedProj H)} (hC : C ≤ normalizer (X : Set (StatedProj H))) :
    ∃ W : Submodule K (ι → K), W ≠ ⊥ ∧ W ≠ ⊤ ∧ ∀ g : ↥H,
      (QuotientGroup.mk g : StatedProj H) ∈ C → ∀ w ∈ W,
        ((g : GL ι K) : Matrix ι ι K) *ᵥ w ∈ W := by
  set N : Subgroup ↥H := (StatedScalars ι K).subgroupOf H with hN
  have hker : (QuotientGroup.mk' N).ker ≤ center ↥H := by
    intro z hz
    rw [QuotientGroup.ker_mk'] at hz
    rw [Subgroup.mem_center_iff]
    intro g
    have hz' : (z : GL ι K) ∈ StatedScalars ι K := hz
    rw [StatedScalars, ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz'
    exact Subtype.ext (Subgroup.mem_center_iff.1 hz' g)
  have hcop : Nat.Coprime r (Nat.card (QuotientGroup.mk' N).ker) := by
    refine NatMod.coprime_card_of_scalars (statedRho H) (statedRho_injective H) fun z hz => ?_
    rw [QuotientGroup.ker_mk'] at hz
    have hz' : (z : GL ι K) ∈ StatedScalars ι K := hz
    obtain ⟨c, hc⟩ := hz'
    refine ⟨(c : K), fun v => ?_⟩
    rw [statedRho_apply, ← hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    ext i
    rw [Matrix.mulVec_diagonal]
    rfl
  obtain ⟨W, hW0, hWt, hW⟩ := exists_proper_invariant_subspace (statedRho H)
    (statedRho_injective H) (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) hker hcop hX
    hX1 hC
  exact ⟨W, hW0, hWt, fun g hg w hw => hW g hg w hw⟩

end Stated

section Outer

theorem isPGroup_outer_of_card_dvd {Y : Type} [Group Y] {k : ℕ}
    (h : Nat.card (Outer Y) ∣ 2 ^ k) : IsPGroup 2 (Outer Y) := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h
  exact IsPGroup.of_card hj

theorem le_innSub_of_isPGroup_outer {Y : Type} [Group Y] (hout : IsPGroup 2 (Outer Y))
    {W : Subgroup (MulAut Y)} (hW : IsPGroup 3 ↥W) : W ≤ innSub Y := by
  intro w hw
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hW) ⟨w, hw⟩
  have hj' : orderOf w = 3 ^ j := by rwa [Subgroup.orderOf_mk] at hj
  let q : MulAut Y →* Outer Y := QuotientGroup.mk' (inner Y)
  obtain ⟨i, hi⟩ := (IsPGroup.iff_orderOf.mp hout) (q w)
  have h1 : orderOf (q w) ∣ 3 ^ j := hj' ▸ orderOf_map_dvd q w
  have h2 : orderOf (q w) ∣ 2 ^ i := hi ▸ dvd_rfl
  have hcop : Nat.gcd (3 ^ j) (2 ^ i) = 1 := Nat.Coprime.pow j i (by norm_num : Nat.Coprime 3 2)
  have h3 : orderOf (q w) = 1 := Nat.dvd_one.1 (hcop ▸ Nat.dvd_gcd h1 h2)
  exact (QuotientGroup.eq_one_iff (N := inner Y) w).1 (orderOf_eq_one_iff.1 h3)

theorem finite_mulAut_surv (Y : Type) [Group Y] [Finite Y] : Finite (MulAut Y) :=
  Finite.of_injective (fun f : MulAut Y => (f : Y → Y)) fun _ _ h => MulEquiv.ext (congrFun h)

theorem conj_injective_surv {Y : Type} [Group Y] (hc : center Y = ⊥) :
    Function.Injective (MulAut.conj : Y →* MulAut Y) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have : g ∈ center Y := by
    rw [Subgroup.mem_center_iff]
    intro z
    have hz := congrArg (fun φ : MulAut Y => φ z) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at hz
    calc z * g = g * z * g⁻¹ * g := by rw [hz]
      _ = g * z := by group
  rw [hc] at this
  exact this

theorem isSylowOf_of_map {K G : Type*} [Group K] [Group G] [Finite K] [Finite G] {p : ℕ}
    [Fact p.Prime] (f : K →* G) (hf : Function.Injective f) {P X : Subgroup K}
    (h : IsSylowOf p (P.map f) (X.map f)) : IsSylowOf p P X := by
  rw [isSylowOf_iff] at h ⊢
  obtain ⟨h1, h2, h3⟩ := h
  rw [Subgroup.relIndex_map_map_of_injective _ _ hf] at h3
  exact ⟨(Subgroup.map_le_map_iff_of_injective hf).1 h1,
    h2.of_equiv (P.equivMapOfInjective f hf).symm, h3⟩

theorem exists_sylow_three_of_sylCfgOf_outer {Y G : Type} [Group Y] [Finite Y] [Group G]
    [Finite G] (hc : center Y = ⊥) (hout : IsPGroup 2 (Outer Y)) (e : Y ≃* G)
    (h : SylCfgOf Y) :
    ∃ P W : Subgroup G, IsSylowOf 2 P ⊤ ∧ IsPGroup 3 ↥W ∧ W ≠ ⊥ ∧
      P ≤ normalizer (W : Set G) := by
  obtain ⟨T, W, hcfg⟩ := h
  obtain ⟨P, hPT, hPinn, hPsyl⟩ := hcfg.syl
  have hfin : Finite (MulAut Y) := finite_mulAut_surv Y
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set c : G →* MulAut Y := (MulAut.conj : Y →* MulAut Y).comp e.symm.toMonoidHom with hcdef
  have hinj : Function.Injective c := (conj_injective_surv hc).comp e.symm.injective
  have hrange : c.range = innSub Y := by
    ext a
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨e.symm x, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨e y, by simp [c]⟩
  have hWI : W ≤ innSub Y := le_innSub_of_isPGroup_outer hout hcfg.w3
  have hPc : P ≤ c.range := hrange ▸ hPinn
  have hWc : W ≤ c.range := hrange ▸ hWI
  refine ⟨P.comap c, W.comap c, ?_, ?_, ?_, ?_⟩
  · have h1 : (P.comap c).map c = P := Subgroup.map_comap_eq_self hPc
    have h2 : (⊤ : Subgroup G).map c = innSub Y := by
      rw [← hrange]
      exact (MonoidHom.range_eq_map c).symm
    have h3 : IsSylowOf 2 ((P.comap c).map c) ((⊤ : Subgroup G).map c) := by
      rw [h1, h2]
      exact hPsyl
    exact isSylowOf_of_map c hinj h3
  · refine IsPGroup.comap_of_ker_isPGroup hcfg.w3 c ?_
    rw [(MonoidHom.ker_eq_bot_iff c).2 hinj]
    exact IsPGroup.of_card (by simp : Nat.card ↥(⊥ : Subgroup G) = 3 ^ 0)
  · intro hb
    apply hcfg.w_ne
    rw [← Subgroup.map_comap_eq_self hWc, hb, Subgroup.map_bot]
  · intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have hyT : c y ∈ T := hPT hy
    have := Subgroup.mem_normalizer_iff.mp (hcfg.t_norm hyT) (c z)
    simpa [Subgroup.mem_comap, map_mul, map_inv] using this

theorem exists_three_normalized_of_sylow {G : Type*} [Group G] [Finite G] {P W : Subgroup G}
    (hP : IsSylowOf 2 P ⊤) (hW3 : IsPGroup 3 ↥W) (hWne : W ≠ ⊥)
    (hPW : P ≤ normalizer (W : Set G)) {M : Subgroup G} (hM : IsPGroup 2 ↥M) :
    ∃ X : Subgroup G, IsPGroup 3 ↥X ∧ X ≠ ⊥ ∧ M ≤ normalizer (X : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS, hMS⟩ : ∃ S : Subgroup G, IsSylowOf 2 S ⊤ ∧ M ≤ S := by
    have hM' : IsPGroup 2 ↥(M.subgroupOf ⊤) := hM.comap_subtype
    obtain ⟨Q, hQ⟩ := hM'.exists_le_sylow
    refine ⟨(Q : Subgroup (⊤ : Subgroup G)).map (⊤ : Subgroup G).subtype, ⟨Q, rfl⟩,
      fun m hm => ?_⟩
    exact ⟨⟨m, trivial⟩, hQ (show (⟨m, trivial⟩ : (⊤ : Subgroup G)) ∈ M.subgroupOf ⊤ from hm),
      rfl⟩
  obtain ⟨κ, -, hκ⟩ := hS.exists_mem_conj hP
  have hcomap : ∀ x : G, x ∈ W.comap (MulAut.conj κ).toMonoidHom ↔ κ * x * κ⁻¹ ∈ W := fun x => by
    simp [Subgroup.mem_comap, MulAut.conj_apply]
  refine ⟨W.comap (MulAut.conj κ).toMonoidHom, ?_, ?_, ?_⟩
  · refine IsPGroup.comap_of_ker_isPGroup hW3 (MulAut.conj κ).toMonoidHom ?_
    rw [(MonoidHom.ker_eq_bot_iff _).2 (MulAut.conj κ).injective]
    exact IsPGroup.of_card (by simp : Nat.card ↥(⊥ : Subgroup G) = 3 ^ 0)
  · intro hb
    apply hWne
    rw [eq_bot_iff]
    intro x hx
    have : κ⁻¹ * x * κ⁻¹⁻¹ ∈ W.comap (MulAut.conj κ).toMonoidHom := by
      rw [hcomap]
      simpa [mul_assoc] using hx
    rw [hb] at this
    have h1 : κ⁻¹ * x * κ⁻¹⁻¹ = 1 := this
    rw [Subgroup.mem_bot]
    calc x = κ * (κ⁻¹ * x * κ⁻¹⁻¹) * κ⁻¹ := by group
      _ = 1 := by rw [h1]; group
  · intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hp : κ * m * κ⁻¹ ∈ P := (hκ _).2 (by simpa [mul_assoc] using hMS hm)
    have hn := Subgroup.mem_normalizer_iff.1 (hPW hp) (κ * x * κ⁻¹)
    rw [hcomap, hcomap]
    have e : κ * (m * x * m⁻¹) * κ⁻¹ = (κ * m * κ⁻¹) * (κ * x * κ⁻¹) * (κ * m * κ⁻¹)⁻¹ := by
      group
    rw [e]
    exact hn

end Outer

section Main

theorem not_sylCfgOf_of_irreducible {Y : Type} [Group Y] [Finite Y] (hc : center Y = ⊥)
    (hout : IsPGroup 2 (Outer Y)) {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] [CharP K 3] (H : Subgroup (GL ι K)) (e : Y ≃* StatedProj H)
    (T : Subgroup (GL ι K)) (hT : IsPGroup 2 ↥T)
    (hirr : ∀ W : Submodule K (ι → K),
      (∀ g ∈ T ⊓ H, ∀ w ∈ W, ((g : GL ι K) : Matrix ι ι K) *ᵥ w ∈ W) → W = ⊥ ∨ W = ⊤) :
    ¬ SylCfgOf Y := by
  intro hcfg
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, W₀, hP, hW3, hWne, hPW⟩ := exists_sylow_three_of_sylCfgOf_outer hc hout e hcfg
  let T' : Subgroup ↥H := (T ⊓ H).comap H.subtype
  have hT2 : IsPGroup 2 ↥T' := by
    refine IsPGroup.comap_of_ker_isPGroup (hT.to_le inf_le_left) H.subtype ?_
    rw [(MonoidHom.ker_eq_bot_iff _).2 H.subtype_injective]
    exact IsPGroup.of_card (by simp : Nat.card ↥(⊥ : Subgroup ↥H) = 2 ^ 0)
  let M : Subgroup (StatedProj H) :=
    T'.map (QuotientGroup.mk' ((StatedScalars ι K).subgroupOf H))
  have hM : IsPGroup 2 ↥M := hT2.map _
  obtain ⟨X, hX3, hXne, hMX⟩ := exists_three_normalized_of_sylow hP hW3 hWne hPW hM
  obtain ⟨W, hW0, hWt, hW⟩ := exists_proper_invariant_subspace_stated H hX3 hXne hMX
  have hinv : ∀ g ∈ T ⊓ H, ∀ w ∈ W, ((g : GL ι K) : Matrix ι ι K) *ᵥ w ∈ W := fun g hg w hw =>
    hW ⟨g, hg.2⟩ (Subgroup.mem_map_of_mem _ (show (⟨g, hg.2⟩ : ↥H) ∈ T' from hg)) w hw
  rcases hirr W hinv with h | h
  · exact hW0 h
  · exact hWt h

variable {K : Type} [Field K]

theorem not_sylCfgOf_of_stated {Y : Type} [Group Y] [Finite Y] (hc : center Y = ⊥) {k : ℕ}
    (hout : Nat.card (Outer Y) ∣ 2 ^ k) [Finite K] [CharP K 3] (H : Subgroup (GL (Fin 4) K))
    (e : Y ≃* StatedProj H)
    (hH : ∀ (g : Fin 4) (ε : Fin 4 → K) (hε : ∀ i, ε i = 1 ∨ ε i = -1),
      ε 0 * ε 1 * ε 2 * ε 3 = 1 → monoGL g ε hε ∈ H) : ¬ SylCfgOf Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have h3 : (3 : ℕ) ∣ 2 := (CharP.cast_eq_zero_iff K 3 2).1 (by exact_mod_cast h)
    omega
  refine not_sylCfgOf_of_irreducible hc (isPGroup_outer_of_card_dvd hout) H e (sgnGroup K)
    isPGroup_sgnGroup fun W hW => ?_
  exact eq_bot_or_top_of_sgn_invariant h2 W fun g ε hε hdet w hw =>
    hW (monoGL g ε hε) ⟨monoGL_mem_sgnGroup g ε hε, hH g ε hε hdet⟩ w hw

end Main

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
