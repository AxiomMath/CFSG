module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.Context
import all CFSG.LocalAnalysis.RankThreeUC.Section5.Context
public import CFSG.LocalAnalysis.RankThreeUC.Section5.ActorInfCentralizerEqBot
public import CFSG.LocalAnalysis.RankThreeUC.Section5.OpenPCoreEq
public import CFSG.GroupTheory.AutomorphismAction.CommutingPGroup
public import CFSG.LocalAnalysis.RankThreeUC.ConstrainedNormalCoreNontrivial.ConstrainedNormalCoreNontrivial

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace Section5

open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

def maxInvariantOdd (X A : Subgroup G) : Set (Subgroup G) :=
  {R | Maximal (fun R : Subgroup G => R ≤ X ∧ Odd (Nat.card R) ∧
    A ≤ Subgroup.normalizer (R : Set G)) R}

section Aux

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

private theorem finite_of_irred (ρ : Representation (ZMod 2) G V) (h : ρ.IsIrreducible) :
    Finite V := by
  have := (Representation.irreducible_iff_isSimpleModule_asModule ρ).1 h
  haveI : Nontrivial ρ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra (ZMod 2) G) _
  obtain ⟨v, hv⟩ := exists_ne (0 : ρ.asModule)
  have htop := IsSimpleModule.span_singleton_eq_top (R := MonoidAlgebra (ZMod 2) G) hv
  have hsurj : Function.Surjective (fun r : MonoidAlgebra (ZMod 2) G => r • v) := by
    intro x
    have : x ∈ Submodule.span (MonoidAlgebra (ZMod 2) G) {v} := by rw [htop]; trivial
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 this
    exact ⟨r, hr⟩
  haveI : Finite (MonoidAlgebra (ZMod 2) G) :=
    Finite.of_equiv (G → ZMod 2)
      ((Finsupp.equivFunOnFinite (α := G) (M := ZMod 2)).symm.trans MonoidAlgebra.coeffEquiv.symm)
  have : Finite ρ.asModule := Finite.of_surjective _ hsurj
  exact Finite.of_equiv ρ.asModule (Representation.asModuleEquiv ρ).toEquiv

private noncomputable def toLE (ρ : Representation (ZMod 2) G V) : G →* (V ≃ₗ[ZMod 2] V) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _).toMonoidHom.comp
    (Representation.asGroupHom ρ)

private theorem toLE_apply (ρ : Representation (ZMod 2) G V) (g : G) (v : V) :
    toLE ρ g v = ρ g v := rfl

private theorem toLE_injective (ρ : Representation (ZMod 2) G V)
    (hρ : Function.Injective ρ) : Function.Injective (toLE ρ) := by
  intro a b hab
  apply hρ
  ext v
  have := LinearEquiv.congr_fun hab v
  simpa [toLE_apply] using this

private theorem mem_fix {ρ : Representation (ZMod 2) G V} {S : Subgroup G} {u : V} :
    u ∈ fixedSubmodule ρ S ↔ ∀ s ∈ S, ρ s u = u := by
  unfold fixedSubmodule
  rw [Representation.mem_invariants]
  exact ⟨fun h s hs => h ⟨s, hs⟩, fun h s => h s s.2⟩

private theorem thompson_aux [Finite V] {ρ : Representation (ZMod 2) G V}
    (hρ : Function.Injective ρ) {S : Subgroup G} (hS : IsPGroup 2 S) {k : G}
    (hk : Odd (orderOf k)) (hkS : ∀ s ∈ S, s * k = k * s)
    (hfix : ∀ u ∈ fixedSubmodule ρ S, ρ k u = u) : k = 1 := by
  let σ : S →* (V ≃ₗ[ZMod 2] V) := (toLE ρ).comp S.subtype
  let C := Subgroup.centralizer (S : Set G)
  let ρ' : C →* (V ≃ₗ[ZMod 2] V) := (toLE ρ).comp C.subtype
  have hkC : k ∈ C := Subgroup.mem_centralizer_iff.2 hkS
  have hcomm : ∀ (g : C) (x : S) (u : V), ρ' g (σ x u) = σ x (ρ' g u) := by
    intro g x u
    have h1 : (x : G) * g = g * x := Subgroup.mem_centralizer_iff.1 g.2 x x.2
    simp only [ρ', σ, MonoidHom.comp_apply, Subgroup.coe_subtype, toLE_apply]
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, h1.symm]
  have hker : (⟨k, hkC⟩ : C) ∈ CFSG.GroupTheory.AutomorphismAction.CommutingPGroup.fixedKernel ρ' σ := by
    rw [CFSG.GroupTheory.AutomorphismAction.CommutingPGroup.mem_fixedKernel]
    intro u hu
    apply hfix
    rw [mem_fix]
    intro s hs
    have := hu ⟨s, hs⟩
    simpa [σ, toLE_apply] using this
  have hcop : Nat.Coprime (orderOf (ρ' ⟨k, hkC⟩)) 2 := by
    have : orderOf (ρ' ⟨k, hkC⟩) = orderOf k := by
      have h1 : ρ' ⟨k, hkC⟩ = toLE ρ k := rfl
      rw [h1, orderOf_injective _ (toLE_injective ρ hρ)]
    rw [this]
    exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2
      (by rintro ⟨c, hc⟩; obtain ⟨m, hm⟩ := hk; omega))
  have h1 : ∀ u, ρ k u = u := fun u => by
    have := CFSG.GroupTheory.AutomorphismAction.CommutingPGroup.eq_of_coprime_of_mem_fixedKernel (p := 2) hS hcomm hker hcop u
    simpa [ρ', toLE_apply] using this
  apply hρ
  ext u
  simpa using h1 u

private theorem fixed_inter_comm_eq_zero (ρ : Representation (ZMod 2) G V) {A : Subgroup G}
    (hA : Odd (Nat.card A)) {w : V} (hfix : ∀ a ∈ A, ρ a w = w)
    (hw : w ∈ Submodule.span (ZMod 2) {x | ∃ a ∈ A, ∃ v, x = ρ a v - v}) : w = 0 := by
  classical
  haveI : Fintype A := Fintype.ofFinite A
  let e : Module.End (ZMod 2) V := ∑ a : A, ρ a
  have he : ∀ v, e v = ∑ a : A, ρ a v := fun v => by simp [e, LinearMap.sum_apply]
  have hker : ∀ x ∈ Submodule.span (ZMod 2) {x | ∃ a ∈ A, ∃ v, x = ρ a v - v}, e x = 0 := by
    intro x hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨b, hb, v, rfl⟩
      rw [map_sub, he, he]
      have : ∑ a : A, ρ a (ρ b v) = ∑ a : A, ρ a v := by
        rw [← Equiv.sum_comp (Equiv.mulRight (⟨b, hb⟩ : A)) (fun a : A => ρ a v)]
        refine Finset.sum_congr rfl fun a _ => ?_
        show ρ (a : G) (ρ b v) = ρ ((a : G) * b) v
        rw [map_mul]; rfl
      rw [this, sub_self]
    · simp
    · intro x y _ _ hx hy
      rw [map_add, hx, hy, add_zero]
    · intro c x _ hx
      rw [map_smul, hx, smul_zero]
  have h0 := hker w hw
  rw [he] at h0
  have : ∑ a : A, ρ a w = (Nat.card A) • w := by
    rw [Finset.sum_congr rfl (fun (a : A) _ => hfix (a : G) a.2), Finset.sum_const, Finset.card_univ,
      Nat.card_eq_fintype_card]
  rw [this, ← Nat.cast_smul_eq_nsmul (ZMod 2), ZMod.natCast_eq_one_iff_odd.2 hA, one_smul] at h0
  exact h0

private theorem conj_mem_commutator {R A : Subgroup G} {n : G}
    (hR : n ∈ Subgroup.normalizer (R : Set G)) (hA : n ∈ Subgroup.normalizer (A : Set G))
    {s : G} (hs : s ∈ ⁅R, A⁆) : n * s * n⁻¹ ∈ ⁅R, A⁆ := by
  have h1 : Subgroup.map (MulAut.conj n).toMonoidHom R ≤ R := by
    rintro _ ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 hR y).1 hy
  have h2 : Subgroup.map (MulAut.conj n).toMonoidHom A ≤ A := by
    rintro _ ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 hA y).1 hy
  have := Subgroup.commutator_mono h1 h2
  rw [← Subgroup.map_commutator] at this
  exact this ⟨s, hs, rfl⟩

end Aux
theorem characteristic_actor_fixes_commutator_fixedSpace_and_centralizes_odd_invariants {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (h51 : OddPrimeClassTwoAction G p P T B e) (h53 : FaithfulBinaryIrreducibleAction G p P T B ρ)
    (A : Subgroup G) (hAB : A ≤ B)
    (hchar : ∀ φ : ↥B ≃* ↥B, Subgroup.map φ.toMonoidHom (A.subgroupOf B) = A.subgroupOf B) :
    (∀ a ∈ A, ∀ u ∈ fixedSubmodule ρ ⁅CFSG.Open.pCoreOf 2 (B ⊔ T), A⁆, ρ a u = u) ∧
    (∀ R ∈ maxInvariantOdd
        (Subgroup.centralizer ((⁅CFSG.Open.pCoreOf 2 (B ⊔ T), A⁆ : Subgroup G) : Set G)) A,
      R ≤ Subgroup.centralizer (A : Set G)) ∧
    (A ≠ ⊥ → ⁅P, ⁅CFSG.Open.pCoreOf 2 (B ⊔ T), A⁆⁆ ≠ ⊥) := by
  classical
  have hfinV : Finite V := finite_of_irred ρ h53.irreducible
  have hR2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 (B ⊔ T)) := by
    have h : CFSG.Open.pCore 2 ↥(B ⊔ T) = CFSG.pCore 2 ↥(B ⊔ T) :=
      rfl
    unfold CFSG.Open.pCoreOf
    rw [h]
    exact (CFSG.pCore_isPGroup (p := 2) (G := ↥(B ⊔ T))).map (B ⊔ T).subtype
  set R : Subgroup G := CFSG.Open.pCoreOf 2 (B ⊔ T) with hRdef
  set S : Subgroup G := ⁅R, A⁆ with hSdef
  have hRle : R ≤ B ⊔ T := ConstrainedNormalCoreNontrivial.pCoreOf_le
  have hRnorm : ∀ x ∈ B ⊔ T, x ∈ Subgroup.normalizer (R : Set G) := fun x hx =>
    ConstrainedNormalCoreNontrivial.normalizer_le_normalizer_pCoreOf (B ⊔ T)
      (Subgroup.le_normalizer hx)
  have hAnormR : ∀ a ∈ A, a ∈ Subgroup.normalizer (R : Set G) := fun a ha =>
    hRnorm a (Subgroup.mem_sup_left (hAB ha))
  have hSR : S ≤ R := by
    rw [hSdef, Subgroup.commutator_le]
    intro r hr a ha
    have h1 : a * r⁻¹ * a⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.1 (hAnormR a ha) r⁻¹).1
      (R.inv_mem hr)
    have : ⁅r, a⁆ = r * (a * r⁻¹ * a⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact R.mul_mem hr h1
  have hS2 : IsPGroup 2 S := hR2.of_injective (Subgroup.inclusion hSR)
    (Subgroup.inclusion_injective hSR)
  have hOddA : Odd (Nat.card A) :=
    Odd.of_dvd_nat h51.setting.oddOrder (Subgroup.card_dvd_of_le hAB)
  have hUinv : ∀ n ∈ Subgroup.normalizer (R : Set G) ⊓ Subgroup.normalizer (A : Set G),
      ∀ u ∈ fixedSubmodule ρ S, ρ n u ∈ fixedSubmodule ρ S := by
    intro n hn u hu
    rw [mem_fix] at hu ⊢
    intro s hs
    have hn' : n⁻¹ ∈ Subgroup.normalizer (R : Set G) ⊓ Subgroup.normalizer (A : Set G) :=
      Subgroup.inv_mem _ hn
    have h1 : n⁻¹ * s * n⁻¹⁻¹ ∈ S := conj_mem_commutator hn'.1 hn'.2 hs
    have h2 := hu _ h1
    calc ρ s (ρ n u) = ρ n (ρ (n⁻¹ * s * n⁻¹⁻¹ ) u) := by
          rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
          simp [mul_assoc]
      _ = ρ n u := by rw [h2]
  have hcentU : ∀ y ∈ Subgroup.centralizer (S : Set G), ∀ u ∈ fixedSubmodule ρ S,
      ρ y u ∈ fixedSubmodule ρ S := by
    intro y hy u hu
    rw [mem_fix] at hu ⊢
    intro s hs
    have h1 : s * y = y * s := Subgroup.mem_centralizer_iff.1 hy s hs
    rw [← Module.End.mul_apply, ← map_mul, h1, map_mul, Module.End.mul_apply, hu s hs]
  have fixes_fixedSubmodule : ∀ a ∈ A, ∀ u ∈ fixedSubmodule ρ S, ρ a u = u := by
    set U := fixedSubmodule ρ S with hU
    set W : Submodule (ZMod 2) V :=
      Submodule.span (ZMod 2) {x | ∃ a ∈ A, ∃ u ∈ U, x = ρ a u - u} with hW
    have hAn : ∀ a ∈ A, a ∈ Subgroup.normalizer (R : Set G) ⊓ Subgroup.normalizer (A : Set G) :=
      fun a ha => ⟨hAnormR a ha, Subgroup.le_normalizer ha⟩
    have hWU : W ≤ U := by
      rw [hW, Submodule.span_le]
      rintro _ ⟨a, ha, u, hu, rfl⟩
      exact U.sub_mem (hUinv a (hAn a ha) u hu) hu
    suffices hWbot : W = ⊥ by
      intro a ha u hu
      have : ρ a u - u ∈ W := Submodule.subset_span ⟨a, ha, u, hu, rfl⟩
      rw [hWbot, Submodule.mem_bot, sub_eq_zero] at this
      exact this
    by_contra hne
    have hTn : ∀ n ∈ T ⊓ Subgroup.normalizer (A : Set G), ∀ w ∈ W, ρ n w ∈ W := by
      intro n hn w hw
      have hnn : n ∈ Subgroup.normalizer (R : Set G) ⊓ Subgroup.normalizer (A : Set G) :=
        ⟨hRnorm n (Subgroup.mem_sup_right hn.1), hn.2⟩
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
      · rintro _ ⟨a, ha, u, hu, rfl⟩
        have h1 : n * a * n⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 hn.2 a).1 ha
        have : ρ n (ρ a u - u) = ρ (n * a * n⁻¹) (ρ n u) - ρ n u := by
          rw [map_sub, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
            ← Module.End.mul_apply (ρ n⁻¹), ← map_mul, inv_mul_cancel, map_one]
          rfl
        rw [this]
        exact Submodule.subset_span ⟨_, h1, _, hUinv n hnn u hu, rfl⟩
      · simp
      · intro x y _ _ hx hy
        rw [map_add]; exact W.add_mem hx hy
      · intro c x _ hx
        rw [map_smul]; exact W.smul_mem c hx
    have hWT : ∀ t ∈ T, ∀ w ∈ W, ρ t w ∈ W := by
      intro t ht w hw
      have h56 := (actor_le_twoFitting_preimage_and_sylow_factorization h51 h53).2 A hAB hchar
      have : t ∈ (T : Set G) := ht
      rw [h56] at this
      obtain ⟨s, hs, n, hn, rfl⟩ := this
      have h1 : ρ n w ∈ W := hTn n hn w hw
      have h2 : ρ s (ρ n w) = ρ n w := (mem_fix.1 (hWU h1)) s hs
      rw [map_mul, Module.End.mul_apply, h2]
      exact h1
    have hT2 : IsPGroup 2 T := h51.setting.twoGroup
    obtain ⟨w, hwW, hw0, hwfix⟩ := CFSG.GroupTheory.AutomorphismAction.CommutingPGroup.exists_fixed_of_invariant (p := 2) hT2
      ((toLE ρ).comp T.subtype) W (fun x u hu => hWT x x.2 u hu) hne
    have hwZ : w ∈ sylowFixedSubmodule ρ T := by
      show w ∈ CFSG.LocalAnalysis.RankThreeUC.fixedSubmodule ρ T
      rw [mem_fix]
      intro t ht
      simpa [toLE_apply] using hwfix ⟨t, ht⟩
    have hwA : ∀ a ∈ A, ρ a w = w := fun a ha => h53.comm_Z_B w hwZ a (hAB ha)
    refine hw0 (fixed_inter_comm_eq_zero ρ hOddA hwA ?_)
    refine Submodule.span_mono ?_ hwW
    rintro _ ⟨a, ha, u, _, rfl⟩
    exact ⟨a, ha, u, rfl⟩
  have part2 : ∀ X ∈ maxInvariantOdd (Subgroup.centralizer (S : Set G)) A,
      X ≤ Subgroup.centralizer (A : Set G) := by
    intro X hX x hx
    obtain ⟨hXc, hXodd, hXA⟩ := hX.1
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    set k : G := a * x * a⁻¹ * x⁻¹ with hk
    have hkX : k ∈ X := by
      have h1 : a * x * a⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.1 (hXA ha) x).1 hx
      exact X.mul_mem h1 (X.inv_mem hx)
    have hkodd : Odd (orderOf k) :=
      Odd.of_dvd_nat hXodd (by simpa using Subgroup.orderOf_dvd_natCard X hkX)
    have hkS : ∀ s ∈ S, s * k = k * s := fun s hs =>
      Subgroup.mem_centralizer_iff.1 (hXc hkX) s hs
    have hkfix : ∀ u ∈ fixedSubmodule ρ S, ρ k u = u := by
      intro u hu
      have h1 : ρ x⁻¹ u ∈ fixedSubmodule ρ S := hcentU _ (hXc (X.inv_mem hx)) u hu
      have h2 : ρ a⁻¹ (ρ x⁻¹ u) = ρ x⁻¹ u := fixes_fixedSubmodule a⁻¹ (A.inv_mem ha) _ h1
      have h3 : ρ x (ρ x⁻¹ u) = u := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
      calc ρ k u = ρ a (ρ x (ρ a⁻¹ (ρ x⁻¹ u))) := by
            simp [hk, map_mul, Module.End.mul_apply]
        _ = u := by rw [h2, h3]; exact fixes_fixedSubmodule a ha u hu
    have := thompson_aux h53.faithful hS2 hkodd hkS hkfix
    have h4 : a * x * a⁻¹ = x := by
      have := mul_inv_eq_one.1 (hk ▸ this)
      exact this
    calc a * x = a * x * a⁻¹ * a := by group
      _ = x * a := by rw [h4]
  refine ⟨fixes_fixedSubmodule, part2, ?_⟩
  intro hA hPS
  have hPC : P ≤ Subgroup.centralizer (S : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have h1 : ⁅y, s⁆ ∈ ⁅P, S⁆ := Subgroup.commutator_mem_commutator hy hs
    rw [hPS, Subgroup.mem_bot] at h1
    have h2 : y * s * y⁻¹ * s⁻¹ = 1 := by simpa [commutatorElement_def] using h1
    have h3 : y * s * y⁻¹ = s := mul_inv_eq_one.1 h2
    calc s * y = (y * s * y⁻¹) * y := by rw [h3]
      _ = y * s := by group
  have hPodd : Odd (Nat.card P) := by
    haveI : Fact p.Prime := ⟨h51.setting.prime⟩
    obtain ⟨n, hn⟩ := h51.setting.pGroup.exists_card_eq
    rw [hn]; exact h51.setting.odd.pow
  have hPA : A ≤ Subgroup.normalizer (P : Set G) := fun a ha => h51.setting.normB (hAB ha)
  have hmem : P ∈ {R : Subgroup G | R ≤ Subgroup.centralizer (S : Set G) ∧ Odd (Nat.card R) ∧
      A ≤ Subgroup.normalizer (R : Set G)} := ⟨hPC, hPodd, hPA⟩
  obtain ⟨X, hPX, hXmax⟩ := Set.Finite.exists_le_maximal (Set.toFinite _) hmem
  have hXA := part2 X hXmax
  have hAcP : A ≤ B ⊓ Subgroup.centralizer (P : Set G) := by
    refine le_inf hAB ?_
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.1 (hXA (hPX hy)) a ha).symm
  rw [actor_inf_centralizer_eq_bot h51 h53] at hAcP
  exact hA (le_bot_iff.1 hAcP)

end Section5
end CFSG.LocalAnalysis.RankThreeUC
