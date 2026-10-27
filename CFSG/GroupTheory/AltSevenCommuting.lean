module

public import CFSG.Quasithin.Background.Module
import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4FusionTwo
import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ModuleChief
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin (fixV commV)

private noncomputable def restrictHom_a7c {X : Type*} [Group X] (E : Subgroup X)
    (A : Subgroup (MulAut X)) (hA : ∀ β ∈ A, ∀ x ∈ E, β x ∈ E) : A →* MulAut E where
  toFun β :=
    { toFun := fun x => ⟨(β : MulAut X) x, hA β β.2 x x.2⟩
      invFun := fun x => ⟨(β : MulAut X)⁻¹ x, hA _ (A.inv_mem β.2) x x.2⟩
      left_inv := fun x => Subtype.ext (MulAut.inv_apply_self _ _ _)
      right_inv := fun x => Subtype.ext (MulAut.apply_inv_self _ _ _)
      map_mul' := fun x y => Subtype.ext (map_mul (β : MulAut X) (x : X) (y : X)) }
  map_one' := by ext x; rfl
  map_mul' β γ := by ext x; rfl

@[simp] private theorem restrictHom_a7c_apply {X : Type*} [Group X] (E : Subgroup X)
    (A : Subgroup (MulAut X)) (hA : ∀ β ∈ A, ∀ x ∈ E, β x ∈ E) (β : A) (x : E) :
    ((restrictHom_a7c E A hA β x : E) : X) = (β : MulAut X) x := rfl

private theorem isPerfect_of_iso_a7c {G : Type*} [Group G]
    (e : G ≃* alternatingGroup (Fin 7)) : commutator G = ⊤ := by
  have : Group.IsPerfect (alternatingGroup (Fin 7)) :=
    Group.isPerfect_def.mpr (commutator_alternatingGroup_eq_top (by
      rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num))
  exact (Group.IsPerfect.ofSurjective (f := (e.symm : alternatingGroup (Fin 7) →* G))
    e.symm.surjective).commutator_eq_top

private theorem center_eq_bot_of_iso_a7c {G : Type*} [Group G]
    (e : G ≃* alternatingGroup (Fin 7)) : Subgroup.center G = ⊥ := by
  have h : Subgroup.map (e : G →* alternatingGroup (Fin 7)) (Subgroup.center G) = ⊥ := by
    rw [Subgroup.map_center_eq e, alternatingGroup.center_eq_bot (by
      rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)]
  exact Subgroup.map_injective e.injective (h.trans (Subgroup.map_bot _).symm)

private theorem restrictHom_injective_of_ker_ne_top_a7c {G E : Type*} [Group G] [Group E]
    [IsSimpleGroup G] (f : G →* MulAut E) (hker : f.ker ≠ ⊤) : Function.Injective f := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h | h
  · exact (MonoidHom.ker_eq_bot_iff f).1 h
  · exact absurd h hker

private theorem restrictHomK_ker_ne_top_a7c {W : Type*} [CommGroup W]
    {K : Subgroup (MulAut W)} (eK : ↥K ≃* alternatingGroup (Fin 7))
    (hcard : Nat.card (commV K) = 16) :
    (restrictHom_a7c (commV K) K
      (fun _ hβ _ hx => CFSG.Quasithin.commV_apply_mem_of_mem hβ hx)).ker ≠ ⊤ := by
  intro hker
  have hcent : ∀ l ∈ K, ∀ t ∈ commV K, l t = t := by
    intro l hl t ht
    have h1 : (restrictHom_a7c (commV K) K
        (fun _ hβ _ hx => CFSG.Quasithin.commV_apply_mem_of_mem hβ hx)) ⟨l, hl⟩ = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      exact Subgroup.mem_top _
    have h2 := congrArg (fun φ : MulAut ↥(commV K) => ((φ ⟨t, ht⟩ : ↥(commV K)) : W)) h1
    simpa [restrictHom_a7c_apply, MulAut.one_apply] using h2
  have htriv : ∀ l ∈ K, ∀ s ∈ (Set.univ : Set W), l s * s⁻¹ ∈ (⊥ : Subgroup W) := by
    apply CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.mul_inv_mem_of_perfect
      (isPerfect_of_iso_a7c eK) (S := Set.univ) (T := commV K) (Z := ⊥)
    · intro l hl s _
      exact Subgroup.subset_closure ⟨l, hl, s, rfl⟩
    · intro l hl t ht
      rw [hcent l hl t ht, mul_inv_cancel]
      exact Subgroup.mem_bot.mpr rfl
  have hEbot : commV K ≤ ⊥ := by
    rw [commV, Subgroup.closure_le]
    rintro _ ⟨l, hl, s, rfl⟩
    exact htriv l hl s (Set.mem_univ s)
  have h1 : Nat.card (commV K) = 1 := by
    rw [le_bot_iff.mp hEbot, Subgroup.card_bot]
  omega

private theorem restrictHomL_ker_ne_top_a7c {W : Type*} [CommGroup W]
    {K L : Subgroup (MulAut W)} (hKL : ∀ k ∈ K, ∀ l ∈ L, k * l = l * k)
    (hgoal : ¬ commV K ≤ fixV L) :
    (restrictHom_a7c (commV K) L
      (fun _ hβ _ hx => CFSG.Quasithin.commV_apply_mem_of_commute hKL hβ hx)).ker ≠ ⊤ := by
  intro hker
  apply hgoal
  intro e he
  rw [CFSG.Quasithin.mem_fixV]
  intro l hl
  have h1 : (restrictHom_a7c (commV K) L
      (fun _ hβ _ hx => CFSG.Quasithin.commV_apply_mem_of_commute hKL hβ hx)) ⟨l, hl⟩ = 1 := by
    rw [← MonoidHom.mem_ker, hker]
    exact Subgroup.mem_top _
  have h2 := congrArg (fun φ : MulAut ↥(commV K) => ((φ ⟨e, he⟩ : ↥(commV K)) : W)) h1
  simpa [restrictHom_a7c_apply, MulAut.one_apply] using h2

private theorem restrictHom_mul_comm_a7c {X : Type*} [Group X] {E : Subgroup X}
    {K L : Subgroup (MulAut X)} (hKE : ∀ β ∈ K, ∀ x ∈ E, β x ∈ E)
    (hLE : ∀ β ∈ L, ∀ x ∈ E, β x ∈ E) (hKL : ∀ k ∈ K, ∀ l ∈ L, k * l = l * k)
    (k : ↥K) (l : ↥L) : restrictHom_a7c E K hKE k * restrictHom_a7c E L hLE l =
      restrictHom_a7c E L hLE l * restrictHom_a7c E K hKE k := by
  ext e
  simp only [MulAut.mul_apply, restrictHom_a7c_apply]
  exact congrArg (fun φ : MulAut X => φ (e : X)) (hKL k k.2 l l.2)

private theorem range_inf_eq_bot_of_commute_a7c {E G H : Type*} [Group E] [Group G] [Group H]
    [IsSimpleGroup G] (f : G →* MulAut E) (g : H →* MulAut E) (hf : Function.Injective f)
    (hcenter : Subgroup.center G = ⊥)
    (hcomm : ∀ a : G, ∀ b : H, f a * g b = g b * f a) : f.range ⊓ g.range = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxK, hxL⟩
  obtain ⟨k, rfl⟩ := hxK
  obtain ⟨b, hb⟩ := hxL
  have hcent : k ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro k'
    exact hf (by
      rw [map_mul, map_mul]
      calc f k' * f k = f k' * g b := by rw [hb]
        _ = g b * f k' := hcomm k' b
        _ = f k * f k' := by rw [hb])
  have hk1 : k = 1 := by
    rw [hcenter] at hcent
    exact Subgroup.mem_bot.mp hcent
  rw [hk1, map_one]
  exact Subgroup.mem_bot.mpr rfl

private theorem false_of_two_a7_hom_inj_a7c {E K L : Type*} [Group E] [Finite E]
    [Group K] [Group L] (hEc : ∀ a b : E, a * b = b * a) (hEsq : ∀ a : E, a * a = 1)
    (hEcard : Nat.card E = 16) (hKcard : Nat.card K = 2520) (hLcard : Nat.card L = 2520)
    (f : K →* MulAut E) (g : L →* MulAut E) (hf : Function.Injective f)
    (hg : Function.Injective g) (hdisj : f.range ⊓ g.range = ⊥) : False := by
  let Φ : K × L → MulAut E := fun p => f p.1 * g p.2
  have hinjΦ : Function.Injective Φ := by
    rintro ⟨k1, l1⟩ ⟨k2, l2⟩ h
    have h' : f k1 * g l1 = f k2 * g l2 := h
    have key : g l1 * (g l2)⁻¹ = (f k1)⁻¹ * f k2 := by
      have := congrArg (fun x => (f k1)⁻¹ * x * (g l2)⁻¹) h'
      simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one] using this
    have hmemK : (f k1)⁻¹ * f k2 ∈ f.range := ⟨k1⁻¹ * k2, by rw [map_mul, map_inv]⟩
    have hmemL : (f k1)⁻¹ * f k2 ∈ g.range := by
      rw [← key]
      exact ⟨l1 * l2⁻¹, by rw [map_mul, map_inv]⟩
    have hone : (f k1)⁻¹ * f k2 = 1 := by
      have hmem : (f k1)⁻¹ * f k2 ∈ f.range ⊓ g.range := Subgroup.mem_inf.mpr ⟨hmemK, hmemL⟩
      rw [hdisj] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hk : k1 = k2 := hf (inv_mul_eq_one.mp hone)
    have hl : l1 = l2 := by
      rw [hk] at h'
      exact hg (mul_left_cancel h')
    exact Prod.ext hk hl
  have hle := Nat.card_le_card_of_injective Φ hinjΦ
  have hAut : Nat.card (MulAut E) = 20160 :=
    CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.card_mulAut_of_elemAb_sixteen hEc hEsq hEcard
  rw [Nat.card_prod, hKcard, hLcard, hAut] at hle
  norm_num at hle

theorem commV_le_fixV_of_commute {W : Type} [CommGroup W] (hW : ∀ w : W, w ^ 2 = 1)
    {K L : Subgroup (MulAut W)} (hK : Nonempty (↥K ≃* alternatingGroup (Fin 7)))
    (hL : Nonempty (↥L ≃* alternatingGroup (Fin 7))) (hcard : Nat.card (commV K) = 16)
    (hKL : ∀ k ∈ K, ∀ l ∈ L, k * l = l * k) : commV K ≤ fixV L := by
  classical
  obtain ⟨eK⟩ := hK
  obtain ⟨eL⟩ := hL
  let E : Subgroup W := commV K
  have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  have hsimpleK : IsSimpleGroup ↥K := eK.isSimpleGroup
  have hsimpleL : IsSimpleGroup ↥L := eL.isSimpleGroup
  have hcenterK : Subgroup.center ↥K = ⊥ := center_eq_bot_of_iso_a7c eK
  let ρK : ↥K →* MulAut E :=
    restrictHom_a7c E K (fun _ hβ _ hx => CFSG.Quasithin.commV_apply_mem_of_mem hβ hx)
  let ρL : ↥L →* MulAut E :=
    restrictHom_a7c E L (fun _ hβ _ hx => CFSG.Quasithin.commV_apply_mem_of_commute hKL hβ hx)
  have hkerK : ρK.ker ≠ ⊤ := restrictHomK_ker_ne_top_a7c eK hcard
  have hinjK : Function.Injective ρK :=
    restrictHom_injective_of_ker_ne_top_a7c ρK hkerK
  by_contra hgoal
  have hkerL : ρL.ker ≠ ⊤ := restrictHomL_ker_ne_top_a7c hKL hgoal
  have hinjL : Function.Injective ρL :=
    restrictHom_injective_of_ker_ne_top_a7c ρL hkerL
  have hcomm : ∀ a : ↥K, ∀ b : ↥L, ρK a * ρL b = ρL b * ρK a := fun a b =>
    restrictHom_mul_comm_a7c
      (fun _ hβ _ hx => CFSG.Quasithin.commV_apply_mem_of_mem hβ hx)
      (fun _ hβ _ hx => CFSG.Quasithin.commV_apply_mem_of_commute hKL hβ hx) hKL a b
  have hdisj : ρK.range ⊓ ρL.range = ⊥ :=
    range_inf_eq_bot_of_commute_a7c ρK ρL hinjK hcenterK hcomm
  have hcardK : Nat.card ↥K = 2520 := by
    rw [Nat.card_congr eK.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  have hcardL : Nat.card ↥L = 2520 := by
    rw [Nat.card_congr eL.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  have hfiniteE : Finite ↥(commV K) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  exact false_of_two_a7_hom_inj_a7c (fun a b => mul_comm a b)
    (fun a => Subtype.ext (by
      change (a : W) * (a : W) = 1
      simpa only [pow_two] using hW (a : W)))
    hcard hcardK hcardL ρK ρL hinjK hinjL hdisj

end CFSG.GroupTheory
