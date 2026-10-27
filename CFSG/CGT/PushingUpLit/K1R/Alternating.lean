module

public import CFSG.CGT.PushingUpLit.K1R.Defs
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatAlternating

public section

namespace CFSG.CGT.PushingUpLit.K1R

open Equiv Subgroup CFSG.LocalAnalysis.EvenBN.GMSK CFSG.LocalAnalysis.EvenBN.GMSK.Alternating
open CFSG.LocalAnalysis.SteinbergBT (swap_mul_swap_comm_of_ne mul_comm_of_conj_eq)

open CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification in
theorem alternating_inner_noFour_false {n m : ℕ} (hn : 2 ≤ n) (K : Type*) [Field K]
    (hK : Nat.card K = 2 ^ n) (hm : 5 ≤ m) (hm6 : m ≠ 6) {D : Type*} [Group D] [Finite D]
    (η : D ≃* alternatingGroup (Fin m)) (α : MulAut D) (hα : orderOf α = 2)
    (hin : α ∈ (MulAut.conj : D →* MulAut D).range) (S : Subgroup D)
    (hSα : S ≤ α.toMonoidHom.eqLocus (MonoidHom.id D))
    (hSn : (S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D))).Normal)
    (φ : S ≃* Matrix.SpecialLinearGroup (Fin 2) K)
    (hnf : NoFour (α.toMonoidHom.eqLocus (MonoidHom.id D) ⊓ centralizer (S : Set D))) : False := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  have hSs : IsSimpleGroup S := by
    have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
    have := Fintype.ofFinite K
    have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) := sl2_isSimpleGroup h2K (by
      rw [← Nat.card_eq_fintype_card, hK]
      calc 4 = 2 ^ 2 := rfl
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn)
    exact φ.isSimpleGroup
  have hSnab : ∃ a b : S, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := sl2_exists_mul_ne (K := K)
    exact ⟨φ.symm a, φ.symm b, fun h => hab (by
      have h1 := congrArg φ h
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h1)⟩
  have hm' : m = 5 ∨ 7 ≤ m := by omega
  have hmemC : ∀ d, d ∈ α.toMonoidHom.eqLocus (MonoidHom.id D) ↔ α d = d := fun d => Iff.rfl
  let β : MulAut (alternatingGroup (Fin m)) := η.symm.trans (α.trans η)
  have hβ : ∀ g, β g = η (α (η.symm g)) := fun g => rfl
  obtain ⟨σ, hσ⟩ := CFSG.Milestones.alternating_automorphism_permutation hm' β
  have hσ' : ∀ g : alternatingGroup (Fin m), (η (α (η.symm g)) : Perm (Fin m)) = σ * g * σ⁻¹ :=
    fun g => hσ g
  have hinj := Quasithin.SteinbergCB.conjPerm_injective (n := m) (by omega)
  have hconj : ∀ τ : Perm (Fin m),
      (∀ g : alternatingGroup (Fin m), (η (α (η.symm g)) : Perm (Fin m)) = τ * g * τ⁻¹) →
        Quasithin.SteinbergCB.conjPerm m τ = β := fun τ hτ =>
    MulEquiv.ext fun g => Subtype.ext (by rw [Quasithin.SteinbergCB.conjPerm_apply, hβ, hτ])
  have huniq : ∀ τ : Perm (Fin m),
      (∀ g : alternatingGroup (Fin m), (η (α (η.symm g)) : Perm (Fin m)) = τ * g * τ⁻¹) →
        τ = σ := fun τ hτ => hinj ((hconj τ hτ).trans (hconj σ hσ').symm)
  have hα2 : ∀ d, α (α d) = d := by
    have h : α ^ 2 = 1 := by rw [← hα]; exact pow_orderOf_eq_one α
    intro d
    have := congrArg (fun γ : MulAut D => γ d) h
    simpa [sq] using this
  have hσσ : σ * σ = 1 := by
    apply hinj
    rw [map_mul, hconj σ hσ', map_one]
    refine MulEquiv.ext fun g => ?_
    rw [MulAut.mul_apply, hβ, hβ, MulEquiv.symm_apply_apply, hα2, MulEquiv.apply_symm_apply,
      MulAut.one_apply]
  have hσ1 : σ ≠ 1 := by
    intro h1
    have hβ1 : β = 1 := by rw [← hconj σ hσ', h1, map_one]
    have hα1 : α ≠ 1 := fun h => by
      rw [h, orderOf_one] at hα
      omega
    apply hα1
    refine MulEquiv.ext fun d => ?_
    have := congrArg (fun γ : MulAut (alternatingGroup (Fin m)) => γ (η d)) hβ1
    simp only [hβ, MulEquiv.symm_apply_apply, MulAut.one_apply] at this
    exact η.injective this
  have hσ2 : orderOf σ = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [sq, hσσ]) hσ1
  have hσinv : ∀ x, σ (σ x) = x := fun x => by rw [← Perm.mul_apply, hσσ, Perm.one_apply]
  let ι : D →* Perm (Fin m) :=
    (alternatingGroup (Fin m)).subtype.comp (η : D →* alternatingGroup (Fin m))
  have hι : Function.Injective ι := (alternatingGroup (Fin m)).subtype_injective.comp η.injective
  have hιA : ∀ d, ι d ∈ alternatingGroup (Fin m) := fun d => (η d).2
  have hfix : ∀ d, d ∈ α.toMonoidHom.eqLocus (MonoidHom.id D) ↔ σ * ι d = ι d * σ := by
    intro d
    rw [hmemC]
    have h := hσ' (η d)
    rw [MulEquiv.symm_apply_apply] at h
    constructor
    · intro hd
      rw [hd] at h
      exact (mul_comm_of_conj_eq h.symm)
    · intro hd
      apply η.injective
      apply Subtype.ext
      rw [h]
      change σ * ι d * σ⁻¹ = ι d
      rw [hd, mul_inv_cancel_right]
  set S' := S.map ι with hS'def
  set M := alternatingGroup (Fin m) ⊓ centralizer ({σ} : Set (Perm (Fin m))) with hMdef
  have hS'M : S' ≤ M := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨hιA s, mem_centralizer_singleton_iff.2 ((hfix s).1 (hSα hs)).symm⟩
  have hS'n : (S'.subgroupOf M).Normal := by
    constructor
    intro x hx g
    rw [mem_subgroupOf] at hx ⊢
    obtain ⟨s, hs, hsx⟩ := hx
    have hgA : (g : Perm (Fin m)) ∈ alternatingGroup (Fin m) := (mem_inf.1 g.2).1
    have hgC : (g : Perm (Fin m)) ∈ centralizer ({σ} : Set (Perm (Fin m))) := (mem_inf.1 g.2).2
    have hcg : ι (η.symm ⟨g, hgA⟩) = g := by
      change ((η (η.symm ⟨g, hgA⟩) : alternatingGroup (Fin m)) : Perm (Fin m)) = g
      rw [MulEquiv.apply_symm_apply]
    have hcC : η.symm ⟨g, hgA⟩ ∈ α.toMonoidHom.eqLocus (MonoidHom.id D) :=
      (hfix _).2 (by rw [hcg]; exact (mem_centralizer_singleton_iff.1 hgC).symm)
    have hmem := hSn.conj_mem ⟨s, hSα hs⟩ (mem_subgroupOf.2 hs) ⟨_, hcC⟩
    rw [mem_subgroupOf] at hmem
    refine ⟨_, hmem, ?_⟩
    change ι (η.symm ⟨g, hgA⟩ * s * (η.symm ⟨g, hgA⟩)⁻¹) =
      (g : Perm (Fin m)) * x * (g : Perm (Fin m))⁻¹
    rw [map_mul, map_mul, map_inv, hcg, hsx]
  have hMN : (M.subgroupOf (centralizer ({σ} : Set (Perm (Fin m))))).Normal := by
    constructor
    intro x hx g
    rw [mem_subgroupOf] at hx ⊢
    obtain ⟨hxA, hxC⟩ := mem_inf.1 hx
    refine mem_inf.2 ⟨?_, ?_⟩
    · exact (inferInstance : (alternatingGroup (Fin m)).Normal).conj_mem _ hxA _
    · exact mul_mem (mul_mem g.2 hxC) (inv_mem g.2)
  have hS'q : CFSG.Assembly.IsQuasisimple S' := by
    have : IsSimpleGroup S := hSs
    have hSq := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hSnab).1
    rw [AssemblyBPredicates.isQuasisimple_iff_native]
    exact (isQuasisimple_congr (S.equivMapOfInjective ι hι)).1 hSq
  have hcomp : CFSG.Assembly.IsComponentOf S'
      (⊤ ⊓ normalizer ((zpowers σ : Subgroup (Perm (Fin m))) : Set (Perm (Fin m)))) := by
    rw [top_inf_eq, ← centralizer_singleton_eq_normalizer_zpowers hσ2]
    exact ⟨hS'M.trans inf_le_right, CFSG.Assembly.IsSubnormal.step hS'M hS'n
      (CFSG.Assembly.IsSubnormal.step inf_le_right hMN (CFSG.Assembly.IsSubnormal.refl _)),
      hS'q⟩
  obtain ⟨-, hS'eq⟩ := ordinary_permutation_local_component_fixed_support (T := ⊤) le_top
    Nat.prime_two le_top (isPGroup_zpowers_of_orderOf_eq_two hσ2) hcomp
  have hS'mem : ∀ g, g ∈ S' ↔ (∀ x, ¬ σ x = x → g x = x) ∧ Perm.sign g = 1 := by
    intro g
    classical
    rw [hS'eq, SymmetricLocal.mem_map_ofSubtype_alternatingGroup_iff]
    simp only [mem_fixedPoints_zpowers_iff]
  obtain ⟨a, ha⟩ : ∃ a, σ a ≠ a := by
    by_contra h
    push Not at h
    exact hσ1 (Equiv.ext h)
  have hab : a ≠ σ a := fun h => ha h.symm
  have hrest : ∀ c, c ≠ a → c ≠ σ a → σ c = c := by
    intro c hca hcb
    by_contra hc
    have hda : σ c ≠ a := fun h => hcb (by rw [← h, hσinv])
    have hdb : σ c ≠ σ a := fun h => hca (σ.injective h)
    have hdc : σ c ≠ c := hc
    have hxA : swap a (σ a) * swap c (σ c) ∈ alternatingGroup (Fin m) := by
      rw [Perm.mem_alternatingGroup, map_mul, Perm.sign_swap hab, Perm.sign_swap hdc.symm]
      decide
    have hyA : swap a c * swap (σ a) (σ c) ∈ alternatingGroup (Fin m) := by
      rw [Perm.mem_alternatingGroup, map_mul, Perm.sign_swap hca.symm, Perm.sign_swap hdb.symm]
      decide
    have hxσ : σ * (swap a (σ a) * swap c (σ c)) = swap a (σ a) * swap c (σ c) * σ := by
      refine mul_comm_of_conj_eq ?_
      rw [show σ * (swap a (σ a) * swap c (σ c)) * σ⁻¹ =
          (σ * swap a (σ a) * σ⁻¹) * (σ * swap c (σ c) * σ⁻¹) by group,
        ← swap_apply_apply, ← swap_apply_apply, hσinv, hσinv, swap_comm (σ a), swap_comm (σ c)]
    have hyσ : σ * (swap a c * swap (σ a) (σ c)) = swap a c * swap (σ a) (σ c) * σ := by
      refine mul_comm_of_conj_eq ?_
      rw [show σ * (swap a c * swap (σ a) (σ c)) * σ⁻¹ =
          (σ * swap a c * σ⁻¹) * (σ * swap (σ a) (σ c) * σ⁻¹) by group,
        ← swap_apply_apply, ← swap_apply_apply, hσinv, hσinv]
      exact swap_mul_swap_comm_of_ne ha hcb.symm hda hdc
    have hfixF : ∀ z, σ z = z → z ≠ a ∧ z ≠ σ a ∧ z ≠ c ∧ z ≠ σ c := by
      intro z hz
      refine ⟨fun h => ha (h ▸ hz), fun h => ?_, fun h => hc (h ▸ hz), fun h => ?_⟩
      · rw [h, hσinv] at hz
        exact hab hz
      · rw [h, hσinv] at hz
        exact hdc hz.symm
    have hcent : ∀ w : Perm (Fin m), (∀ z, σ z = z → w z = z) → ∀ t ∈ S', t * w = w * t := by
      intro w hw t ht
      refine (Perm.Disjoint.commute fun z => ?_).eq
      by_cases hz : σ z = z
      · exact Or.inr (hw z hz)
      · exact Or.inl ((hS'mem t).1 ht |>.1 z hz)
    have hxF : ∀ z, σ z = z → (swap a (σ a) * swap c (σ c)) z = z := by
      intro z hz
      obtain ⟨h1, h2, h3, h4⟩ := hfixF z hz
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne h3 h4, swap_apply_of_ne_of_ne h1 h2]
    have hyF : ∀ z, σ z = z → (swap a c * swap (σ a) (σ c)) z = z := by
      intro z hz
      obtain ⟨h1, h2, h3, h4⟩ := hfixF z hz
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne h2 h4, swap_apply_of_ne_of_ne h1 h3]
    have hpre : ∀ w (hw : w ∈ alternatingGroup (Fin m)), σ * w = w * σ →
        (∀ z, σ z = z → w z = z) →
        η.symm ⟨w, hw⟩ ∈ α.toMonoidHom.eqLocus (MonoidHom.id D) ⊓ centralizer (S : Set D) := by
      intro w hw hwσ hwF
      have hιw : ι (η.symm ⟨w, hw⟩) = w := by
        change ((η (η.symm ⟨w, hw⟩) : alternatingGroup (Fin m)) : Perm (Fin m)) = w
        rw [MulEquiv.apply_symm_apply]
      refine mem_inf.2 ⟨(hfix _).2 (by rw [hιw]; exact hwσ), mem_centralizer_iff.2 fun t ht => ?_⟩
      apply hι
      rw [map_mul, map_mul, hιw]
      exact hcent w hwF (ι t) ⟨t, ht, rfl⟩
    have hx1 : swap a (σ a) * swap c (σ c) ≠ 1 := by
      intro h
      have h1 := congrArg (fun w : Perm (Fin m) => w a) h
      simp only [Perm.mul_apply, Perm.one_apply] at h1
      rw [swap_apply_of_ne_of_ne hca.symm hda.symm, swap_apply_left] at h1
      exact hab h1.symm
    have hy1 : swap a c * swap (σ a) (σ c) ≠ 1 := by
      intro h
      have h1 := congrArg (fun w : Perm (Fin m) => w a) h
      simp only [Perm.mul_apply, Perm.one_apply] at h1
      rw [swap_apply_of_ne_of_ne hab hda.symm, swap_apply_left] at h1
      exact hca h1
    have hxy : swap a (σ a) * swap c (σ c) ≠ swap a c * swap (σ a) (σ c) := by
      intro h
      have h1 := congrArg (fun w : Perm (Fin m) => w a) h
      simp only [Perm.mul_apply] at h1
      rw [swap_apply_of_ne_of_ne hca.symm hda.symm, swap_apply_left,
        swap_apply_of_ne_of_ne hab hda.symm, swap_apply_left] at h1
      exact hcb h1.symm
    have hxx : (swap a (σ a) * swap c (σ c)) * (swap a (σ a) * swap c (σ c)) = 1 :=
      mul_mul_self_of_commute (swap_mul_swap_comm_of_ne hca.symm hda.symm hcb.symm hdb.symm)
        (swap_mul_self _ _) (swap_mul_self _ _)
    have hyy : (swap a c * swap (σ a) (σ c)) * (swap a c * swap (σ a) (σ c)) = 1 :=
      mul_mul_self_of_commute (swap_mul_swap_comm_of_ne hab hda.symm hcb hdc.symm)
        (swap_mul_self _ _) (swap_mul_self _ _)
    have hxa : (swap a (σ a) * swap c (σ c)) a = σ a := by
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne hca.symm hda.symm, swap_apply_left]
    have hxb : (swap a (σ a) * swap c (σ c)) (σ a) = a := by
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne hcb.symm hdb.symm, swap_apply_right]
    have hxc : (swap a (σ a) * swap c (σ c)) c = σ c := by
      rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hda hdb]
    have hxd : (swap a (σ a) * swap c (σ c)) (σ c) = c := by
      rw [Perm.mul_apply, swap_apply_right, swap_apply_of_ne_of_ne hca hcb]
    have hxyc : (swap a (σ a) * swap c (σ c)) * (swap a c * swap (σ a) (σ c)) =
        (swap a c * swap (σ a) (σ c)) * (swap a (σ a) * swap c (σ c)) := by
      refine mul_comm_of_conj_eq ?_
      rw [show (swap a (σ a) * swap c (σ c)) * (swap a c * swap (σ a) (σ c)) *
          (swap a (σ a) * swap c (σ c))⁻¹ =
          ((swap a (σ a) * swap c (σ c)) * swap a c * (swap a (σ a) * swap c (σ c))⁻¹) *
          ((swap a (σ a) * swap c (σ c)) * swap (σ a) (σ c) * (swap a (σ a) * swap c (σ c))⁻¹)
          by group, ← swap_apply_apply, ← swap_apply_apply, hxa, hxc, hxb, hxd]
      exact swap_mul_swap_comm_of_ne ha hcb.symm hda hdc
    have hιpre : ∀ w (hw : w ∈ alternatingGroup (Fin m)), ι (η.symm ⟨w, hw⟩) = w := fun w hw => by
      change ((η (η.symm ⟨w, hw⟩) : alternatingGroup (Fin m)) : Perm (Fin m)) = w
      rw [MulEquiv.apply_symm_apply]
    rcases hnf _ (hpre _ hxA hxσ hxF) _ (hpre _ hyA hyσ hyF)
        (hι (by rw [map_mul, hιpre, map_one, hxx]))
        (hι (by rw [map_mul, hιpre, map_one, hyy]))
        (hι (by rw [map_mul, map_mul, hιpre, hιpre, hxyc])) with h | h | h
    · exact hx1 (by
        have := congrArg (fun d => ι d) h
        simpa [ι] using this)
    · exact hy1 (by
        have := congrArg (fun d => ι d) h
        simpa [ι] using this)
    · exact hxy (by
        have := congrArg (fun d => ι d) h
        simpa [ι] using this)
  have hσswap : σ = swap a (σ a) := by
    ext z
    by_cases hza : z = a
    · rw [hza, swap_apply_left]
    by_cases hzb : z = σ a
    · rw [hzb, swap_apply_right, hσinv]
    · rw [swap_apply_of_ne_of_ne hza hzb, hrest z hza hzb]
  have hout : α ∉ (MulAut.conj : D →* MulAut D).range := by
    rintro ⟨d, hd⟩
    have hτ : ∀ g : alternatingGroup (Fin m),
        (η (α (η.symm g)) : Perm (Fin m)) = ι d * g * (ι d)⁻¹ := by
      intro g
      rw [← hd, MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      rfl
    have hsign : Perm.sign σ = 1 := by
      rw [← huniq (ι d) hτ]
      exact hιA d
    rw [hσswap, Perm.sign_swap hab] at hsign
    exact absurd hsign (by decide)
  exact hout hin

theorem innerKernelSelector_alternating :
    InnerKernelSelector fun D _ => ∃ m : ℕ, 5 ≤ m ∧ Nonempty (D ≃* alternatingGroup (Fin m)) := by
  refine InnerKernelSelector.of_false ?_
  intro D _ _ _ ⟨m, hm, ⟨η⟩⟩ n hn K _ _ hK α hα hin S hSα hSn ⟨φ⟩ hnf
  have hK' : Nat.card K = 2 ^ n := by rw [Nat.card_eq_fintype_card, hK]
  by_cases hm6 : m = 6
  · subst hm6
    exact alternating_six_fixed_SL2_false hn K hK' η α hα S hSα φ
  · exact alternating_inner_noFour_false hn K hK' hm hm6 η α hα hin S hSα hSn φ hnf

end CFSG.CGT.PushingUpLit.K1R
