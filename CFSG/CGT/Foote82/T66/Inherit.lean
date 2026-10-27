module

public import CFSG.CGT.Foote82.T66.Basic
public import CFSG.CGT.Foote82.Lemma63
import CFSG.Quasithin.Background.G11Basic
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

private instance instFiniteGLVInherit : Finite (GLV V) :=
  Finite.of_injective (fun f : GLV V => (f : V → V)) fun _ _ h => LinearEquiv.ext (congrFun h)

private theorem nontrivial_of_isQuasisimple_inh {Q : Type*} [Group Q]
    (hQ : CFSG.Open.IsQuasisimple Q) : Nontrivial Q := by
  have hsimple : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2
  obtain ⟨x, y, hxy⟩ := hsimple.exists_pair_ne
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  exact ⟨a, b, fun hab => hxy (by rw [hab])⟩

private theorem perfect_ne_bot_inh {L : Subgroup (GLV V)} (hq : CFSG.Open.IsQuasisimple ↥L) :
    ⁅L, L⁆ = L ∧ L ≠ ⊥ := by
  haveI : Nontrivial ↥L := nontrivial_of_isQuasisimple_inh hq
  haveI : Group.IsPerfect ↥L := Group.isPerfect_def.2 hq.1
  exact ⟨Subgroup.isPerfect_iff.1 inferInstance, (Subgroup.nontrivial_iff_ne_bot L).1 inferInstance⟩

section Sections

variable {H : Subgroup (GLV V)} {W₀ W₁ : Submodule (ZMod 2) V}

private theorem mk_eq_mk_iff_inh {v v' : V} (hv : v ∈ W₁) (hv' : v' ∈ W₁) :
    (Submodule.Quotient.mk ⟨v, hv⟩ : Sect W₀ W₁) = Submodule.Quotient.mk ⟨v', hv'⟩ ↔
      v - v' ∈ W₀ := by
  rw [Submodule.Quotient.eq]
  rfl

private theorem sectHom_eq_one_iff_inh (h₀ : Invariant H W₀) (h₁ : Invariant H W₁) (y : ↥H) :
    sectHom H h₀ h₁ y = 1 ↔ ∀ w ∈ W₁, (y : GLV V) w - w ∈ W₀ := by
  constructor
  · intro h w hw
    have h' := congrArg (fun f : GLV (Sect W₀ W₁) => f (Submodule.Quotient.mk ⟨w, hw⟩)) h
    simp only [sectHom_mk] at h'
    exact (mk_eq_mk_iff_inh (h₁ y y.2 w hw) hw).1 h'
  · intro h
    ext q
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    simp only [sectHom_mk]
    exact (mk_eq_mk_iff_inh (h₁ y y.2 w w.2) w.2).2 (h w w.2)

end Sections

private theorem invariant_commSpace_top_inh (L : Subgroup (GLV V)) :
    Invariant L (commSpace L ⊤) :=
  invariant_commSpace (fun k' hk' k hk => L.mul_mem (L.mul_mem hk' hk) (L.inv_mem hk'))
    (invariant_top L)

private theorem apply_mem_commSpace_inh {L : Subgroup (GLV V)} (ℓ : ↥L)
    (w : ↥(commSpace L ⊤)) : (ℓ : GLV V) (w : V) ∈ commSpace L ⊤ :=
  invariant_commSpace_top_inh L ℓ ℓ.2 w w.2

private theorem commSpace_commSpace_of_perfect_inh {L : Subgroup (GLV V)} (hperf : ⁅L, L⁆ = L)
    {X : Submodule (ZMod 2) V} (hX : Invariant L X) :
    commSpace L (commSpace L X) = commSpace L X := by
  have hconj : ∀ k' ∈ L, ∀ k ∈ L, k' * k * k'⁻¹ ∈ L := fun k' hk' k hk =>
    L.mul_mem (L.mul_mem hk' hk) (L.inv_mem hk')
  refine le_antisymm (commSpace_le_of_invariant (invariant_commSpace hconj hX)) ?_
  set M : Submodule (ZMod 2) V := commSpace L (commSpace L X) with hM
  let K : Subgroup (GLV V) :=
    { carrier := {k | k ∈ L ∧ ∀ v ∈ X, k v - v ∈ M}
      mul_mem' := fun {a b} ha hb => by
        refine ⟨L.mul_mem ha.1 hb.1, fun v hv => ?_⟩
        have h := M.add_mem (ha.2 (b v) (hX b hb.1 v hv)) (hb.2 v hv)
        rwa [sub_add_sub_cancel] at h
      one_mem' := ⟨L.one_mem, fun v _ => by simp⟩
      inv_mem' := fun {a} ha => by
        refine ⟨L.inv_mem ha.1, fun v hv => ?_⟩
        have h := M.neg_mem (ha.2 (a⁻¹ v) (hX a⁻¹ (L.inv_mem ha.1) v hv))
        simpa using h }
  have hcomm : ⁅L, L⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro g hg h hh
    refine ⟨L.mul_mem (L.mul_mem (L.mul_mem hg hh) (L.inv_mem hg)) (L.inv_mem hh),
      fun v hv => ?_⟩
    have key : ∀ u ∈ X, (g * h * g⁻¹ * h⁻¹) (h (g u)) - h (g u) ∈ M := by
      intro u hu
      have e1 : (g * h * g⁻¹ * h⁻¹) (h (g u)) = g (h u) := by simp
      have e2 : g (h u) - h (g u) = (g (h u - u) - (h u - u)) - (h (g u - u) - (g u - u)) := by
        simp only [map_sub]
        abel
      rw [e1, e2]
      exact M.sub_mem (sub_mem_commSpace hg (sub_mem_commSpace hh hu))
        (sub_mem_commSpace hh (sub_mem_commSpace hg hu))
    have hu : g⁻¹ (h⁻¹ v) ∈ X := hX g⁻¹ (L.inv_mem hg) _ (hX h⁻¹ (L.inv_mem hh) v hv)
    have e : h (g (g⁻¹ (h⁻¹ v))) = v := by simp
    have := key _ hu
    rw [e] at this
    exact this
  rw [hperf] at hcomm
  exact commSpace_le_iff.2 fun l hl v hv => (hcomm hl).2 v hv

private theorem trivial_of_commSpace_le_fixedSpace_inh {L : Subgroup (GLV V)}
    (hperf : ⁅L, L⁆ = L) {X : Submodule (ZMod 2) V} (hX : Invariant L X)
    (h : commSpace L X ≤ fixedSpace L) : ∀ l ∈ L, ∀ x ∈ X, l x = x := by
  have h0 : commSpace L (commSpace L X) = ⊥ :=
    commSpace_eq_bot_iff.2 fun l hl w hw => h hw l hl
  rw [commSpace_commSpace_of_perfect_inh hperf hX] at h0
  exact commSpace_eq_bot_iff.1 h0

private theorem trivial_or_commSpace_le_inh {L : Subgroup (GLV V)} (hperf : ⁅L, L⁆ = L)
    (hirr : HasIrrTildeV L) {U : Submodule (ZMod 2) V} (hU : Invariant L U) :
    (∀ l ∈ L, ∀ u ∈ U, l u = u) ∨ commSpace L ⊤ ≤ U := by
  obtain ⟨-, hmin⟩ : IrrSec L (fixedSpace L ⊓ commSpace L ⊤) (commSpace L ⊤) := hirr
  have hAinv : Invariant L (commSpace L ⊤) := invariant_commSpace_top_inh L
  have hCinv : Invariant L (fixedSpace L ⊓ commSpace L ⊤) := fun l hl u hu => by
    rw [hu.1 l hl]
    exact hu
  have hJinv : Invariant L (U ⊓ commSpace L ⊤ ⊔ fixedSpace L ⊓ commSpace L ⊤) :=
    (hU.inf hAinv).sup hCinv
  rcases hmin _ hJinv le_sup_right (sup_le inf_le_right inf_le_right) with hJ | hJ
  · left
    refine trivial_of_commSpace_le_fixedSpace_inh hperf hU fun w hw => ?_
    have hwJ : w ∈ U ⊓ commSpace L ⊤ ⊔ fixedSpace L ⊓ commSpace L ⊤ :=
      Submodule.mem_sup_left ⟨commSpace_le_of_invariant hU hw, commSpace_mono le_rfl le_top hw⟩
    rw [hJ] at hwJ
    exact hwJ.1
  · right
    rw [← commSpace_commSpace_top_of_perfect hperf]
    refine commSpace_le_iff.2 fun l hl a ha => ?_
    have haJ : a ∈ U ⊓ commSpace L ⊤ ⊔ fixedSpace L ⊓ commSpace L ⊤ := by
      rw [hJ]
      exact ha
    obtain ⟨u, hu, c, hc, rfl⟩ := Submodule.mem_sup.1 haJ
    have e : l (u + c) - (u + c) = l u - u := by
      rw [map_add, hc.1 l hl]
      abel
    rw [e]
    exact U.sub_mem (hU l hl u hu.1) hu.1

private theorem sub_one_pow_two_pow_inh {R : Type*} [Ring R] (h2 : (2 : R) = 0) (x : R) (k : ℕ) :
    (x - 1) ^ 2 ^ k = x ^ 2 ^ k - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hsq : ∀ y : R, (y - 1) ^ 2 = y ^ 2 - 1 := fun y => by
      have : (y - 1) ^ 2 = y ^ 2 - 1 - 2 * (y - 1) := by noncomm_ring
      rw [this, h2, zero_mul, sub_zero]
    rw [pow_succ, pow_mul, pow_mul, ih, hsq]

private theorem exists_pow_sub_one_eq_zero_inh {H : Subgroup (GLV V)}
    (htriv : ∀ W₀ W₁ : Submodule (ZMod 2) V, Invariant H W₀ → Invariant H W₁ → IrrSec H W₀ W₁ →
      ∀ x ∈ H, ∀ w ∈ W₁, x w - w ∈ W₀) (U : Submodule (ZMod 2) V) (hU : Invariant H U) :
    ∃ k : ℕ, ∀ x ∈ H, ∀ u ∈ U, (((x : Module.End (ZMod 2) V) - 1) ^ k) u = 0 := by
  suffices key : ∀ n : ℕ, ∀ U : Submodule (ZMod 2) V, Module.finrank (ZMod 2) U = n →
      Invariant H U → ∃ k : ℕ, ∀ x ∈ H, ∀ u ∈ U, (((x : Module.End (ZMod 2) V) - 1) ^ k) u = 0 from
    key _ U rfl hU
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro U hn hU
  by_cases hbot : U = ⊥
  · refine ⟨0, fun x _ u hu => ?_⟩
    rw [hbot, Submodule.mem_bot] at hu
    simp [hu]
  · classical
    let S : Set ℕ := {m | ∃ J : Submodule (ZMod 2) V, Invariant H J ∧ J < U ∧
      Module.finrank (ZMod 2) J = m}
    have hS : S.Nonempty := ⟨0, ⊥, invariant_bot H, bot_lt_iff_ne_bot.2 hbot, by simp⟩
    have hbdd : BddAbove S := ⟨Module.finrank (ZMod 2) U, by
      rintro m ⟨J, -, hJ, rfl⟩
      exact Submodule.finrank_mono hJ.le⟩
    obtain ⟨U', hU'inv, hU'lt, hU'n⟩ := Nat.sSup_mem hS hbdd
    have hirr : IrrSec H U' U := by
      refine ⟨hU'lt, fun J hJ hU'J hJU => ?_⟩
      by_cases hJeq : J = U
      · exact Or.inr hJeq
      · left
        have hJlt : J < U := lt_of_le_of_ne hJU hJeq
        have hle : Module.finrank (ZMod 2) J ≤ Module.finrank (ZMod 2) U' := by
          rw [hU'n]
          exact le_csSup hbdd ⟨J, hJ, hJlt, rfl⟩
        exact (Submodule.eq_of_le_of_finrank_le hU'J hle).symm
    have hlt : Module.finrank (ZMod 2) U' < n := hn ▸ Submodule.finrank_lt_finrank_of_lt hU'lt
    obtain ⟨k, hk⟩ := ih _ hlt U' rfl hU'inv
    refine ⟨k + 1, fun x hx u hu => ?_⟩
    rw [pow_succ, Module.End.mul_apply]
    have e : ((x : Module.End (ZMod 2) V) - 1) u = x u - u := by simp
    rw [e]
    exact hk x hx _ (htriv U' U hU'inv hU hirr x hx u hu)

theorem exists_irrSec_nontrivial_of_not_isPGroup {H : Subgroup (GLV V)}
    (hH : ¬ IsPGroup 2 ↥H) :
    ∃ W₀ W₁ : Submodule (ZMod 2) V, ∃ (h₀ : Invariant H W₀) (h₁ : Invariant H W₁),
      IrrSec H W₀ W₁ ∧ ¬ ∀ x ∈ H, ∀ w ∈ W₁, x w - w ∈ W₀ := by
  by_contra hcon
  have htriv : ∀ W₀ W₁ : Submodule (ZMod 2) V, Invariant H W₀ → Invariant H W₁ →
      IrrSec H W₀ W₁ → ∀ x ∈ H, ∀ w ∈ W₁, x w - w ∈ W₀ := by
    intro W₀ W₁ h₀ h₁ hirr
    by_contra hnt
    exact hcon ⟨W₀, W₁, h₀, h₁, hirr, hnt⟩
  obtain ⟨k, hk⟩ := exists_pow_sub_one_eq_zero_inh htriv ⊤ (invariant_top H)
  have hvv : ∀ v : V, v + v = 0 := fun v => by
    have h2v : (2 : ZMod 2) • v = 0 := by
      have : (2 : ZMod 2) = 0 := rfl
      rw [this, zero_smul]
    rwa [two_smul] at h2v
  have h2 : (2 : Module.End (ZMod 2) V) = 0 := by
    ext v
    simp [two_nsmul, hvv]
  refine hH fun y => ⟨k, Subtype.ext ?_⟩
  have h0 : (((y : GLV V) : Module.End (ZMod 2) V) - 1) ^ 2 ^ k = 0 := by
    have hk' : (((y : GLV V) : Module.End (ZMod 2) V) - 1) ^ k = 0 :=
      LinearMap.ext fun v => hk y y.2 v Submodule.mem_top
    exact pow_eq_zero_of_le (Nat.lt_two_pow_self).le hk'
  rw [sub_one_pow_two_pow_inh h2, sub_eq_zero] at h0
  have hpow := map_pow
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := ZMod 2) (M := V)) (y : GLV V) (2 ^ k)
  have hy : (y : GLV V) ^ 2 ^ k = 1 :=
    LinearEquiv.toLinearMap_injective (hpow.trans h0)
  exact hy

theorem exists_irrSec_nontrivial_of_perfect {H L : Subgroup (GLV V)} (hLH : L ≤ H)
    (hperf : ⁅L, L⁆ = L) (hL : L ≠ ⊥) :
    ∃ W₀ W₁ : Submodule (ZMod 2) V, ∃ (h₀ : Invariant H W₀) (h₁ : Invariant H W₁),
      IrrSec H W₀ W₁ ∧ ¬ ∀ x ∈ H, ∀ w ∈ W₁, x w - w ∈ W₀ := by
  refine exists_irrSec_nontrivial_of_not_isPGroup fun hH => ?_
  have hL2 : IsPGroup 2 ↥L := hH.to_le hLH
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hL2.isNilpotent
  haveI : Nontrivial ↥L := (Subgroup.nontrivial_iff_ne_bot L).2 hL
  haveI : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.2 hperf
  exact Group.IsPerfect.not_isSolvable ↥L inferInstance

theorem layerIn_eq_normalClosure {G R L H₀ H : Subgroup (GLV V)} (h : Setup6 G R L)
    (hH₀ : H₀ ≤ G) (hLR : L ⊔ R ≤ H₀) (hH : H = normalClosure (layerIn H₀) L ⊔ R) :
    layerIn H = normalClosure (layerIn H₀) L := by
  obtain ⟨K, hO⟩ := Lemma63.exists_orbitData (Lemma63.setup6_of_le h hH₀ hLR) hH
  have hAH : normalClosure (layerIn H₀) L ≤ H := by
    rw [hH]
    exact le_sup_left
  show (CFSG.layer ↥H).map H.subtype = _
  rw [hO.layer_eq, Subgroup.map_subgroupOf_eq_of_le hAH]

section Transfer

variable {V' : Type} [AddCommGroup V'] [Module (ZMod 2) V']

private structure TildeVIso (L : Subgroup (GLV V)) (L' : Subgroup (GLV V')) where
  ι : ↥L ≃* ↥L'
  π : ↥(commSpace L ⊤) →ₗ[ZMod 2] ↥(commSpace L' ⊤)
  π_surj : Function.Surjective π
  mem_fixedSpace_iff : ∀ w : ↥(commSpace L ⊤),
    ((π w : ↥(commSpace L' ⊤)) : V') ∈ fixedSpace L' ↔ (w : V) ∈ fixedSpace L
  map_act : ∀ (ℓ : ↥L) (w w' : ↥(commSpace L ⊤)), (w' : V) = (ℓ : GLV V) (w : V) →
    ((π w' : ↥(commSpace L' ⊤)) : V') = (ι ℓ : GLV V') ((π w : ↥(commSpace L' ⊤)) : V')

namespace TildeVIso

variable {L : Subgroup (GLV V)} {L' : Subgroup (GLV V')}

private theorem tildeVWitness (D : TildeVIso L L') {X M : Type} [Group X] [AddGroup M]
    {R : X → M → M → Prop} (h : TildeVWitness L X M R) : TildeVWitness L' X M R := by
  obtain ⟨α, hα, β, hβ, hβk, hR⟩ := h
  have hker : D.π.toAddMonoidHom.ker ≤ β.ker := by
    intro w hw
    rw [hβk, Submodule.mem_toAddSubgroup, Submodule.mem_comap, Submodule.subtype_apply]
    refine (D.mem_fixedSpace_iff w).1 ?_
    have hw0 : D.π w = 0 := hw
    rw [hw0]
    exact Submodule.zero_mem _
  obtain ⟨β', hβ'⟩ : ∃ β' : ↥(commSpace L' ⊤) →+ M, ∀ w, β' (D.π w) = β w :=
    ⟨D.π.toAddMonoidHom.liftOfSurjective D.π_surj ⟨β, hker⟩,
      fun w => AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ _ w⟩
  refine ⟨α.comp D.ι.symm.toMonoidHom, hα.comp D.ι.symm.surjective, β', ?_, ?_, ?_⟩
  · intro m
    obtain ⟨w, rfl⟩ := hβ m
    exact ⟨D.π w, hβ' w⟩
  · ext w'
    obtain ⟨w, rfl⟩ := D.π_surj w'
    rw [AddMonoidHom.mem_ker, hβ', ← AddMonoidHom.mem_ker, hβk]
    simp only [Submodule.mem_toAddSubgroup, Submodule.mem_comap, Submodule.subtype_apply]
    exact (D.mem_fixedSpace_iff w).symm
  · intro ℓ' w₁ w₂ hw
    obtain ⟨ℓ, rfl⟩ := D.ι.surjective ℓ'
    obtain ⟨w, rfl⟩ := D.π_surj w₁
    let v : ↥(commSpace L ⊤) := ⟨(ℓ : GLV V) (w : V), apply_mem_commSpace_inh ℓ w⟩
    have hv : D.π v = w₂ := Subtype.ext ((D.map_act ℓ w v rfl).trans hw.symm)
    rw [← hv, hβ', hβ']
    have e : (α.comp D.ι.symm.toMonoidHom) (D.ι ℓ) = α ℓ := by
      simp
    rw [e]
    exact hR ℓ w v rfl

private theorem finrank_tildeV_eq (D : TildeVIso L L') :
    Module.finrank (ZMod 2) (TildeV L') = Module.finrank (ZMod 2) (TildeV L) := by
  let q' : Submodule (ZMod 2) ↥(commSpace L' ⊤) := (fixedSpace L').comap (commSpace L' ⊤).subtype
  let f : ↥(commSpace L ⊤) →ₗ[ZMod 2] TildeV L' := q'.mkQ ∘ₗ D.π
  have hf : Function.Surjective f := (Submodule.mkQ_surjective q').comp D.π_surj
  have hker : (fixedSpace L).comap (commSpace L ⊤).subtype = LinearMap.ker f := by
    ext w
    simp only [Submodule.mem_comap, Submodule.subtype_apply, LinearMap.mem_ker, f,
      LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, q']
    exact (D.mem_fixedSpace_iff w).symm
  exact ((Submodule.quotEquivOfEq _ _ hker).trans (f.quotKerEquivOfSurjective hf)).finrank_eq.symm

private theorem isFPrimeModule (D : TildeVIso L L') (h : IsFPrimeModule L) :
    IsFPrimeModule L' := by
  have hα : ∀ {T : Type} [Group T] (α : ↥L →* T), Function.Surjective α →
      ∃ α' : ↥L' →* T, Function.Surjective α' :=
    fun α hα => ⟨α.comp D.ι.symm.toMonoidHom, hα.comp D.ι.symm.surjective⟩
  rcases h with ⟨n, hn, hw⟩ | ⟨⟨α, hα'⟩, hr⟩ | hw | hw | hw | ⟨⟨α, hα'⟩, hr⟩
  · exact Or.inl ⟨n, hn, D.tildeVWitness hw⟩
  · exact Or.inr (Or.inl ⟨hα α hα', D.finrank_tildeV_eq.trans hr⟩)
  · exact Or.inr (Or.inr (Or.inl (D.tildeVWitness hw)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (D.tildeVWitness hw))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (D.tildeVWitness hw)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hα α hα', D.finrank_tildeV_eq.trans hr⟩))))

private theorem faithful (D : TildeVIso L L') (h : FaithfulTildeV L) : FaithfulTildeV L' := by
  intro ℓ' hℓ' hfix
  obtain ⟨ℓ, hℓ⟩ := D.ι.surjective ⟨ℓ', hℓ'⟩
  have hℓ1 : (ℓ : GLV V) = 1 := by
    refine h ℓ ℓ.2 fun w hw => ?_
    let w₁ : ↥(commSpace L ⊤) := ⟨w, hw⟩
    let w₂ : ↥(commSpace L ⊤) := ⟨(ℓ : GLV V) w, apply_mem_commSpace_inh ℓ w₁⟩
    have h2 : ((D.π w₂ : ↥(commSpace L' ⊤)) : V') = ℓ' ((D.π w₁ : ↥(commSpace L' ⊤)) : V') := by
      rw [D.map_act ℓ w₁ w₂ rfl, hℓ]
    have h3 : ((D.π (w₂ - w₁) : ↥(commSpace L' ⊤)) : V') ∈ fixedSpace L' := by
      rw [map_sub, Submodule.coe_sub, h2]
      exact hfix _ (D.π w₁).2
    exact (D.mem_fixedSpace_iff (w₂ - w₁)).1 h3
  have hℓe : ℓ = 1 := Subtype.ext hℓ1
  rw [hℓe, map_one] at hℓ
  exact (congrArg Subtype.val hℓ).symm

end TildeVIso

end Transfer

private def relFixed (L : Subgroup (GLV V)) (W₀ : Submodule (ZMod 2) V) :
    Submodule (ZMod 2) V where
  carrier := {v | ∀ l ∈ L, l v - v ∈ W₀}
  add_mem' := fun {a b} ha hb l hl => by
    have e : l (a + b) - (a + b) = (l a - a) + (l b - b) := by
      rw [map_add]
      abel
    rw [e]
    exact W₀.add_mem (ha l hl) (hb l hl)
  zero_mem' := fun l _ => by
    rw [map_zero, sub_zero]
    exact W₀.zero_mem
  smul_mem' := fun c v hv l hl => by
    rw [map_smul, ← smul_sub]
    exact W₀.smul_mem c (hv l hl)

private theorem sect_tildeVIso {H L : Subgroup (GLV V)} {W₀ W₁ : Submodule (ZMod 2) V}
    (h₀ : Invariant H W₀) (h₁ : Invariant H W₁) (hLH : L ≤ H) (hperf : ⁅L, L⁆ = L)
    (hirr : HasIrrTildeV L) (hA : commSpace L ⊤ ≤ W₁) (hA₀ : ¬ commSpace L ⊤ ≤ W₀)
    (hinj : ∀ x : ↥H, (x : GLV V) ∈ L → sectHom H h₀ h₁ x = 1 → x = 1) :
    Nonempty (TildeVIso L ((L.subgroupOf H).map (sectHom H h₀ h₁))) := by
  set φ := sectHom H h₀ h₁ with hφ
  set Lb := (L.subgroupOf H).map φ with hLb
  have hAinv : Invariant L (commSpace L ⊤) := invariant_commSpace_top_inh L
  let f : ↥L →* ↥Lb := (φ.comp (Subgroup.inclusion hLH)).codRestrict Lb fun l =>
    ⟨Subgroup.inclusion hLH l, l.2, rfl⟩
  have hf_inj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro l hl
    have h1 : φ (Subgroup.inclusion hLH l) = 1 := congrArg Subtype.val hl
    have h2 := congrArg (fun z : ↥H => (z : GLV V)) (hinj (Subgroup.inclusion hLH l) l.2 h1)
    exact Subtype.ext h2
  have hf_surj : Function.Surjective f := by
    rintro ⟨_, y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩
  let ι : ↥L ≃* ↥Lb := MulEquiv.ofBijective f ⟨hf_inj, hf_surj⟩
  have hι : ∀ l : ↥L, (ι l : GLV (Sect W₀ W₁)) = φ (Subgroup.inclusion hLH l) := fun l => rfl
  let g : ↥(commSpace L ⊤) →ₗ[ZMod 2] Sect W₀ W₁ :=
    (W₀.comap W₁.subtype).mkQ ∘ₗ Submodule.inclusion hA
  have hg : ∀ w, g w = Submodule.Quotient.mk ⟨(w : V), hA w.2⟩ := fun w => rfl
  have hmem : ∀ w : ↥(commSpace L ⊤), g w ∈ commSpace Lb ⊤ := by
    let P : Submodule (ZMod 2) V :=
      ((commSpace Lb ⊤).comap (W₀.comap W₁.subtype).mkQ).map W₁.subtype
    have hP : commSpace L (commSpace L ⊤) ≤ P := by
      refine commSpace_le_iff.2 fun l hl u hu => ?_
      have hu₁ : u ∈ W₁ := hA hu
      have hlu : (l : GLV V) u ∈ W₁ := h₁ l (hLH hl) u hu₁
      refine ⟨⟨(l : GLV V) u - u, W₁.sub_mem hlu hu₁⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      have e : (W₀.comap W₁.subtype).mkQ ⟨(l : GLV V) u - u, W₁.sub_mem hlu hu₁⟩ =
          φ ⟨l, hLH hl⟩ (Submodule.Quotient.mk ⟨u, hu₁⟩) - Submodule.Quotient.mk ⟨u, hu₁⟩ := by
        rw [hφ, sectHom_mk, ← Submodule.Quotient.mk_sub]
        rfl
      rw [e]
      exact sub_mem_commSpace (show φ ⟨l, hLH hl⟩ ∈ Lb from ⟨⟨l, hLH hl⟩, hl, rfl⟩)
        Submodule.mem_top
    intro w
    have hw : (w : V) ∈ commSpace L (commSpace L ⊤) := by
      rw [commSpace_commSpace_top_of_perfect hperf]
      exact w.2
    obtain ⟨x, hx, hxw⟩ := hP hw
    have hxe : x = ⟨(w : V), hA w.2⟩ := Subtype.ext hxw
    rw [hg, ← hxe]
    exact hx
  have hsurj : commSpace Lb ⊤ ≤ LinearMap.range g := by
    refine commSpace_le_iff.2 fun k hk q _ => ?_
    obtain ⟨y, hy, rfl⟩ := hk
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have hv : (y : GLV V) v - v ∈ commSpace L ⊤ :=
      sub_mem_commSpace (Subgroup.mem_subgroupOf.1 hy) Submodule.mem_top
    refine ⟨⟨_, hv⟩, ?_⟩
    rw [hg, hφ, sectHom_mk, ← Submodule.Quotient.mk_sub]
    rfl
  let π : ↥(commSpace L ⊤) →ₗ[ZMod 2] ↥(commSpace Lb ⊤) := g.codRestrict (commSpace Lb ⊤) hmem
  have hπ : ∀ w, ((π w : ↥(commSpace Lb ⊤)) : Sect W₀ W₁) = g w := fun w => rfl
  have hπs : Function.Surjective π := by
    intro q
    obtain ⟨w, hw⟩ := hsurj q.2
    exact ⟨w, Subtype.ext hw⟩
  have hfix : ∀ w : ↥(commSpace L ⊤),
      ((π w : ↥(commSpace Lb ⊤)) : Sect W₀ W₁) ∈ fixedSpace Lb ↔ (w : V) ∈ fixedSpace L := by
    intro w
    rw [hπ]
    constructor
    · intro hw
      have hrel : (w : V) ∈ relFixed L W₀ := by
        intro l hl
        have h1 := hw (φ ⟨l, hLH hl⟩) ⟨⟨l, hLH hl⟩, hl, rfl⟩
        rw [hg, hφ, sectHom_mk] at h1
        exact (mk_eq_mk_iff_inh _ _).1 h1
      obtain ⟨-, hmin⟩ : IrrSec L (fixedSpace L ⊓ commSpace L ⊤) (commSpace L ⊤) := hirr
      have hYinv : Invariant L (relFixed L W₀ ⊓ commSpace L ⊤) := by
        intro l hl y hy
        refine ⟨fun l' hl' => ?_, hAinv l hl y hy.2⟩
        have e : l' (l y) - l y = ((l' * l) y - y) - (l y - y) := by
          rw [LinearEquiv.mul_apply]
          abel
        rw [e]
        exact W₀.sub_mem (hy.1 _ (L.mul_mem hl' hl)) (hy.1 l hl)
      have hCY : fixedSpace L ⊓ commSpace L ⊤ ≤ relFixed L W₀ ⊓ commSpace L ⊤ :=
        fun c hc => ⟨fun l hl => by rw [hc.1 l hl, sub_self]; exact W₀.zero_mem, hc.2⟩
      rcases hmin _ hYinv hCY inf_le_right with hY | hY
      · have hwY : (w : V) ∈ relFixed L W₀ ⊓ commSpace L ⊤ := ⟨hrel, w.2⟩
        rw [hY] at hwY
        exact hwY.1
      · exfalso
        apply hA₀
        rw [← commSpace_commSpace_top_of_perfect hperf]
        refine commSpace_le_iff.2 fun l hl u hu => ?_
        have huY : u ∈ relFixed L W₀ ⊓ commSpace L ⊤ := by
          rw [hY]
          exact hu
        exact huY.1 l hl
    · intro hw k hk
      obtain ⟨y, hy, rfl⟩ := hk
      rw [hg, hφ, sectHom_mk]
      congr 1
      exact Subtype.ext (hw _ (Subgroup.mem_subgroupOf.1 hy))
  have hact : ∀ (ℓ : ↥L) (w w' : ↥(commSpace L ⊤)), (w' : V) = (ℓ : GLV V) (w : V) →
      ((π w' : ↥(commSpace Lb ⊤)) : Sect W₀ W₁) =
        (ι ℓ : GLV (Sect W₀ W₁)) ((π w : ↥(commSpace Lb ⊤)) : Sect W₀ W₁) := by
    intro ℓ w w' hww'
    rw [hπ, hπ, hι, hg, hg, hφ]
    show _ = sectHom H h₀ h₁ ⟨(ℓ : GLV V), hLH ℓ.2⟩ _
    rw [sectHom_mk]
    congr 1
    exact Subtype.ext hww'
  exact ⟨⟨ι, π, hπs, hfix, hact⟩⟩

theorem Conf66.conf66_sect {G S L R H₀ H : Subgroup (GLV V)} (hc : Conf66 G S L)
    (hf : FaithfulTildeV L) (hR : Setup6 G R L) (hH₀ : H₀ ≤ G) (hLR : L ⊔ R ≤ H₀)
    (hH : H = normalClosure (layerIn H₀) L ⊔ R) {W₀ W₁ : Submodule (ZMod 2) V}
    (h₀ : Invariant H W₀) (h₁ : Invariant H W₁) (hirr : IrrSec H W₀ W₁)
    (hnt : ¬ ∀ x ∈ H, ∀ w ∈ W₁, x w - w ∈ W₀) :
    Conf66 (sectHom H h₀ h₁).range ((R.subgroupOf H).map (sectHom H h₀ h₁))
        ((L.subgroupOf H).map (sectHom H h₀ h₁)) ∧
      FaithfulTildeV ((L.subgroupOf H).map (sectHom H h₀ h₁)) ∧
      ∀ x : ↥H, (x : GLV V) ∈ L → sectHom H h₀ h₁ x = 1 → x = 1 := by
  have hAH : normalClosure (layerIn H₀) L ≤ H := by
    rw [hH]
    exact le_sup_left
  have hLH : L ≤ H := (le_normalClosure _ L).trans hAH
  have hHH₀ : H ≤ H₀ := by
    rw [hH]
    refine sup_le ?_ (le_sup_right.trans hLR)
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨x, hx, l, hl, rfl⟩
    have hxH₀ : x ∈ H₀ := Subgroup.map_subtype_le _ hx
    have hlH₀ : l ∈ H₀ := hLR (Subgroup.mem_sup_left hl)
    exact H₀.mul_mem (H₀.mul_mem hxH₀ hlH₀) (H₀.inv_mem hxH₀)
  have hHG : H ≤ G := hHH₀.trans hH₀
  obtain ⟨hs, -, -⟩ := lemma63 hR hH₀ hLR hH h₀ h₁ hirr hnt
  set φ := sectHom H h₀ h₁ with hφ
  obtain ⟨hperf, -⟩ := perfect_ne_bot_inh hR.component.2.2
  have hirrL : HasIrrTildeV L := hR.irrTilde
  have hntL : ¬ ∀ l ∈ L, ∀ w ∈ W₁, (l : GLV V) w - w ∈ W₀ := by
    intro hcon
    have h0 : commSpace ((L.subgroupOf H).map φ) ⊤ = ⊥ := by
      refine commSpace_eq_bot_iff.2 fun k hk u _ => ?_
      obtain ⟨y, hy, rfl⟩ := hk
      rw [(sectHom_eq_one_iff_inh h₀ h₁ y).2 fun w hw =>
        hcon _ (Subgroup.mem_subgroupOf.1 hy) w hw]
      rfl
    have hlt := hs.irrTilde.1
    rw [h0] at hlt
    exact not_lt_bot hlt
  have hW₁L : Invariant L W₁ := h₁.mono hLH
  have hW₀L : Invariant L W₀ := h₀.mono hLH
  have hA₁ : commSpace L ⊤ ≤ W₁ := by
    rcases trivial_or_commSpace_le_inh hperf hirrL hW₁L with h1 | h1
    · exact absurd (fun l hl w hw => by rw [h1 l hl w hw, sub_self]; exact W₀.zero_mem) hntL
    · exact h1
  have hA₀ : ¬ commSpace L ⊤ ≤ W₀ := fun h0 =>
    hntL fun l hl w _ => h0 (sub_mem_commSpace hl Submodule.mem_top)
  have hW₀fix : W₀ ≤ fixedSpace L := by
    rcases trivial_or_commSpace_le_inh hperf hirrL hW₀L with h1 | h1
    · exact fun w hw l hl => h1 l hl w hw
    · exact absurd h1 hA₀
  have hinj : ∀ x : ↥H, (x : GLV V) ∈ L → φ x = 1 → x = 1 := by
    intro x hxL hx
    have hx' := (sectHom_eq_one_iff_inh h₀ h₁ x).1 hx
    exact Subtype.ext (hf _ hxL fun w hw => hW₀fix (hx' w (hA₁ hw)))
  obtain ⟨D⟩ := sect_tildeVIso h₀ h₁ hLH hperf hirrL hA₁ hA₀ hinj
  refine ⟨⟨?_, hs, D.isFPrimeModule hc.fmod⟩, D.faithful hf, hinj⟩
  exact CFSG.ComponentClassification.CatalogueKProper.of_surjective
    (CFSG.ComponentClassification.CatalogueKProper.of_injective hc.kProper
      (Subgroup.inclusion hHG) (Subgroup.inclusion_injective hHG))
    φ.rangeRestrict φ.rangeRestrict_surjective

theorem isComponentOf_normalClosure {G R L H₀ H : Subgroup (GLV V)} (h : Setup6 G R L)
    (hH₀ : H₀ ≤ G) (hLR : L ⊔ R ≤ H₀) (hH : H = normalClosure (layerIn H₀) L ⊔ R)
    {W₀ W₁ : Submodule (ZMod 2) V} (h₀ : Invariant H W₀) (h₁ : Invariant H W₁)
    (hirr : IrrSec H W₀ W₁) (hnt : ¬ ∀ x ∈ H, ∀ w ∈ W₁, x w - w ∈ W₀)
    (hq : IsQuasisimple ↥(layerIn (sectHom H h₀ h₁).range)) :
    IsComponentOf (normalClosure (layerIn H₀) L) H₀ := by
  set A := normalClosure (layerIn H₀) L with hA
  have h0 : Setup6 H₀ R L := Lemma63.setup6_of_le h hH₀ hLR
  obtain ⟨K, hO⟩ := Lemma63.exists_orbitData h0 hH
  obtain ⟨-, hlay, hcen⟩ := lemma63 h hH₀ hLR hH h₀ h₁ hirr hnt
  set φ := sectHom H h₀ h₁ with hφ
  have hAH : A ≤ H := by
    rw [hH]
    exact le_sup_left
  have hAE : A ≤ layerIn H₀ := normalClosure_le h0.le_layerIn
  have hEH₀ : layerIn H₀ ≤ H₀ := Subgroup.map_subtype_le _
  have h1 : (layerIn H).subgroupOf H = CFSG.layer ↥H :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hQ : (CFSG.layer ↥H).map φ = layerIn φ.range := by
    rw [← h1]
    exact hlay
  have hmapQ : ∀ C : Subgroup ↥H, CFSG.IsComponent C → layerIn φ.range ≤ C.map φ := by
    intro C hC
    have hCE : C ≤ CFSG.layer ↥H := CFSG.LocalCores.component_le_layer hC
    have hCQ : C.map φ ≤ layerIn φ.range := (Subgroup.map_mono hCE).trans hQ.le
    have hN : ((C.map φ).subgroupOf (layerIn φ.range)).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hCQ]
      intro a b ha hb
      rw [← hQ] at hb
      obtain ⟨c, hc, rfl⟩ := ha
      obtain ⟨e, he, rfl⟩ := hb
      refine ⟨e * c * e⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
      exact (Subgroup.mem_normalizer_iff.1 (CFSG.LocalCores.layer_le_normalizer hC he) c).1 hc
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hN with htop | hcenter
    · exact Subgroup.subgroupOf_eq_top.1 htop
    · exfalso
      have hcomm : ⁅C.map φ, C.map φ⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hxc := hcenter (show (⟨x, hCQ hx⟩ : ↥(layerIn φ.range)) ∈
          (C.map φ).subgroupOf (layerIn φ.range) from hx)
        exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hxc ⟨y, hCQ hy⟩)
      have hCperf : ⁅C, C⁆ = C := Subgroup.isPerfect_iff.1 hC.1.1
      have hmapbot : C.map φ = ⊥ := by
        calc C.map φ = (⁅C, C⁆).map φ := by rw [hCperf]
          _ = ⁅C.map φ, C.map φ⁆ := Subgroup.map_commutator _ _ _
          _ = ⊥ := hcomm
      have hCker : C ≤ φ.ker := (Subgroup.map_eq_bot_iff C).1 hmapbot
      have hCc : C ≤ Subgroup.centralizer (C : Set ↥H) := by
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hxl : (x : GLV V) ∈ layerIn H := ⟨x, hCE hx, rfl⟩
        have hyl : (y : GLV V) ∈ layerIn H := ⟨y, hCE hy, rfl⟩
        exact Subtype.ext (Subgroup.mem_centralizer_iff.1
          (hcen x hxl (MonoidHom.mem_ker.1 (hCker hx))) _ hyl)
      have hCC : ⁅C, C⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hCc
      rw [hCperf] at hCC
      haveI := CFSG.LocalCores.isQuasisimple_nontrivial hC.1
      exact (Subgroup.nontrivial_iff_ne_bot C).1 inferInstance hCC
  have hconjK : ∀ s ∈ R.subgroupOf H,
      CFSG.conjugate (K.subgroupOf H) s = K.subgroupOf H := by
    intro s _
    by_contra hne
    have hC₂ : CFSG.IsComponent (CFSG.conjugate (K.subgroupOf H) s) :=
      CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj s⁻¹) hO.comp
    have hcomm : ⁅CFSG.conjugate (K.subgroupOf H) s, K.subgroupOf H⁆ = ⊥ :=
      (CFSG.LocalCores.distinct_components_commute hC₂ hO.comp).resolve_left hne
    have hmapc : ⁅(CFSG.conjugate (K.subgroupOf H) s).map φ, (K.subgroupOf H).map φ⁆ = ⊥ := by
      rw [← Subgroup.map_commutator, hcomm, Subgroup.map_bot]
    have hQc : ⁅layerIn φ.range, layerIn φ.range⁆ = ⊥ :=
      eq_bot_iff.2 ((Subgroup.commutator_mono (hmapQ _ hC₂) (hmapQ _ hO.comp)).trans hmapc.le)
    have hQperf : ⁅layerIn φ.range, layerIn φ.range⁆ = layerIn φ.range :=
      Subgroup.isPerfect_iff.1 hq.1
    haveI := CFSG.LocalCores.isQuasisimple_nontrivial hq
    exact (Subgroup.nontrivial_iff_ne_bot _).1 inferInstance (hQperf.symm.trans hQc)
  have hAK : A.subgroupOf H = K.subgroupOf H :=
    le_antisymm (hO.A_le.trans (iSup₂_le fun s hs => (hconjK s hs).le)) hO.K_le
  have hqA : CFSG.IsQuasisimple ↥(A.subgroupOf H) := by
    rw [hAK]
    exact hO.comp.1
  have hqA' : CFSG.IsQuasisimple ↥A :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAH) hqA
  have hn₁ : (A.subgroupOf (layerIn H₀)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hAE]
    intro a e ha he
    exact normalClosure_conj he ha
  have hn₂ : ((layerIn H₀).subgroupOf H₀).Normal := by
    have h2 : (layerIn H₀).subgroupOf H₀ = CFSG.layer ↥H₀ :=
      Subgroup.comap_map_eq_self_of_injective H₀.subtype_injective _
    rw [h2]
    infer_instance
  exact ⟨hAE.trans hEH₀, CFSG.Open.IsSubnormal.step hAE hn₁
      (CFSG.Open.IsSubnormal.step hEH₀ hn₂ (CFSG.Open.IsSubnormal.refl H₀)),
    hqA'.1.commutator_eq_top, hqA'.2.1⟩

end CFSG.CGT.Foote82
