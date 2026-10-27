module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailRootGen
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailWittFlags
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitGeometryWeylLift

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.LieType.Universal.SpecialLinear SymplecticTorusWeyl
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open scoped Pointwise

variable {K : Type*} [Field K] {A : Type*} [AddCommGroup A] [Module K A] {r : ℕ}
  {qA : QuadraticForm K A}

section Block

variable (r qA) in
@[expose] def blockHom : (monoAut r K × TauCeti.QuadraticMap.orthogonalGroup qA) →*
    (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) where
  toFun p := (p.1 : (Fin r ⊕ Fin r → K) ≃ₗ[K] _).prodCongr (p.2 : A ≃ₗ[K] A)
  map_one' := LinearEquiv.ext fun _ => rfl
  map_mul' _ _ := LinearEquiv.ext fun _ => rfl

theorem blockHom_apply (p : monoAut r K × TauCeti.QuadraticMap.orthogonalGroup qA)
    (v : (Fin r ⊕ Fin r → K) × A) :
    blockHom r qA p v = ((p.1 : (Fin r ⊕ Fin r → K) ≃ₗ[K] _) v.1, (p.2 : A ≃ₗ[K] A) v.2) :=
  rfl

theorem blockHom_injective : Function.Injective (blockHom r qA) := by
  intro p q h
  have h1 : ∀ v, (p.1 : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) v =
      (q.1 : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) v := fun v => by
    have := congrArg Prod.fst (LinearEquiv.congr_fun h (v, 0))
    exact this
  have h2 : ∀ a, (p.2 : A ≃ₗ[K] A) a = (q.2 : A ≃ₗ[K] A) a := fun a => by
    have := congrArg Prod.snd (LinearEquiv.congr_fun h (0, a))
    exact this
  exact Prod.ext (Subtype.ext (LinearEquiv.ext h1)) (Subtype.ext (LinearEquiv.ext h2))

variable (r qA) in
@[expose] def tailMono : Subgroup (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) :=
  (blockHom r qA).range

variable (r qA) in
@[expose] noncomputable def tailNu : tailMono r qA →* ((Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) :=
  (nuMono r K).comp ((MonoidHom.fst _ _).comp
    (MonoidHom.ofInjective (blockHom_injective (r := r) (qA := qA))).symm.toMonoidHom)

theorem ofInjective_symm_blockHom (p : monoAut r K × TauCeti.QuadraticMap.orthogonalGroup qA) :
    (MonoidHom.ofInjective (blockHom_injective (r := r) (qA := qA))).symm
      ⟨blockHom r qA p, ⟨p, rfl⟩⟩ = p := by
  rw [MulEquiv.symm_apply_eq]
  exact Subtype.ext (MonoidHom.ofInjective_apply _).symm

theorem tailNu_blockHom (p : monoAut r K × TauCeti.QuadraticMap.orthogonalGroup qA) :
    tailNu r qA ⟨blockHom r qA p, ⟨p, rfl⟩⟩ = nuMono r K p.1 := by
  change nuMono r K ((MonoidHom.ofInjective (blockHom_injective (r := r) (qA := qA))).symm
    ⟨blockHom r qA p, ⟨p, rfl⟩⟩).1 = _
  rw [ofInjective_symm_blockHom]

theorem tailNu_eq {g : tailMono r qA} {p : monoAut r K × TauCeti.QuadraticMap.orthogonalGroup qA}
    (hp : blockHom r qA p = g) : tailNu r qA g = nuMono r K p.1 := by
  obtain ⟨g, hg⟩ := g
  change blockHom r qA p = g at hp
  subst hp
  exact tailNu_blockHom p

theorem autMat_eq_signedPerm_of_apply {g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)}
    {σ : Equiv.Perm (Fin r ⊕ Fin r)} {μ : Fin r ⊕ Fin r → K}
    (h : ∀ c, g (Pi.single c 1) = μ c • Pi.single (σ c) 1) : autMat g = signedPerm σ μ := by
  ext i j
  rw [autMat_apply, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe, h, signedPerm_apply]
  by_cases hij : i = σ j <;> simp [hij]

theorem tailTorus_le_tailMono : tailTorus r qA ≤ tailMono r qA := by
  rintro g ⟨-, t, h, hh, rfl⟩
  exact ⟨(⟨torusElt r K t, torusElt_mem_monoAut t⟩, ⟨h, hh⟩), rfl⟩

end Block

section Last

variable (d : K) (l : Fin r)

@[expose] def lastLin : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K) where
  toFun v c := if c = .inl l then -d * v (.inr l) else if c = .inr l then -d⁻¹ * v (.inl l)
    else v c
  map_add' v w := by
    funext c
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' t v := by
    funext c
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

theorem lastLin_apply (v : Fin r ⊕ Fin r → K) (c : Fin r ⊕ Fin r) :
    lastLin d l v c = if c = .inl l then -d * v (.inr l) else if c = .inr l then -d⁻¹ * v (.inl l)
      else v c :=
  rfl

variable {d} (hd : d ≠ 0)
include hd

theorem lastLin_involutive : Function.Involutive (lastLin d l) := by
  intro v
  funext c
  rw [lastLin_apply]
  split_ifs with h1 h2
  · subst h1
    rw [lastLin_apply, ite_eq_right (by simp), ite_eq_left rfl]
    field_simp
  · subst h2
    rw [lastLin_apply, ite_eq_left rfl]
    field_simp
  · rw [lastLin_apply, ite_eq_right h1, ite_eq_right h2]

@[expose] noncomputable def lastMono : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K) :=
  LinearEquiv.ofInvolutive (lastLin d l) (lastLin_involutive l hd)

theorem lastMono_apply (v : Fin r ⊕ Fin r → K) : lastMono l hd v = lastLin d l v :=
  rfl

@[expose] noncomputable def lastUnits : Fin r ⊕ Fin r → Kˣ :=
  fun c => if c = .inl l then -(Units.mk0 d hd)⁻¹ else if c = .inr l then -(Units.mk0 d hd) else 1

theorem lastMono_single (c : Fin r ⊕ Fin r) :
    lastMono l hd (Pi.single c 1) =
      ((lastUnits l hd c : Kˣ) : K) • Pi.single (Equiv.swap (.inl l) (.inr l) c) 1 := by
  funext x
  rw [lastMono_apply, lastLin_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hc1 : c = .inl l
  · subst hc1
    rw [Equiv.swap_apply_left]
    by_cases hx1 : x = .inl l
    · subst hx1
      simp [lastUnits]
    · by_cases hx2 : x = .inr l
      · subst hx2
        simp [lastUnits]
      · simp [lastUnits, hx1, hx2]
  · by_cases hc2 : c = .inr l
    · subst hc2
      rw [Equiv.swap_apply_right]
      by_cases hx1 : x = .inl l
      · subst hx1
        simp [lastUnits]
      · by_cases hx2 : x = .inr l
        · subst hx2
          simp [lastUnits]
        · simp [lastUnits, hx1, hx2]
    · rw [Equiv.swap_apply_of_ne_of_ne hc1 hc2]
      by_cases hx1 : x = .inl l
      · subst hx1
        simp [lastUnits, hc1, hc2, Ne.symm hc1]
      · by_cases hx2 : x = .inr l
        · subst hx2
          simp [lastUnits, hc1, hc2, Ne.symm hc2]
        · simp [lastUnits, hc1, hc2, hx1, hx2]

omit hd in
theorem swap_last_mem_signedPermGroup :
    Equiv.swap (Sum.inl l : Fin r ⊕ Fin r) (.inr l) ∈ signedPermGroup r := by
  intro x
  by_cases hi : Sum.elim id id x = l
  · rcases x with i | i <;> simp only [Sum.elim_inl, Sum.elim_inr, id_eq] at hi <;> subst hi <;>
      simp
  · have h1 : x ≠ .inl l := fun h => hi (by rw [h]; rfl)
    have h2 : x ≠ .inr l := fun h => hi (by rw [h]; rfl)
    have h3 : x.swap ≠ .inl l := fun h => h2 (by rw [← Sum.swap_swap x, h]; rfl)
    have h4 : x.swap ≠ .inr l := fun h => h1 (by rw [← Sum.swap_swap x, h]; rfl)
    change Equiv.swap _ _ x.swap = (Equiv.swap _ _ x).swap
    rw [Equiv.swap_apply_of_ne_of_ne h3 h4, Equiv.swap_apply_of_ne_of_ne h1 h2]

theorem lastUnits_swap (c : Fin r ⊕ Fin r) : lastUnits l hd c.swap = (lastUnits l hd c)⁻¹ := by
  rcases c with i | i <;> by_cases hi : i = l
  · subst hi
    simp [lastUnits]
  · simp [lastUnits, hi]
  · subst hi
    simp [lastUnits]
  · simp [lastUnits, hi]

theorem autMat_lastMono :
    autMat (lastMono l hd) = signedPerm (Equiv.swap (.inl l) (.inr l))
      fun c => ((lastUnits l hd c : Kˣ) : K) :=
  autMat_eq_signedPerm_of_apply (lastMono_single l hd)

theorem lastMono_mem : lastMono l hd ∈ monoAut r K :=
  ⟨_, swap_last_mem_signedPermGroup l, lastUnits l hd, lastUnits_swap l hd, autMat_lastMono l hd⟩

theorem nuMono_lastMono :
    nuMono r K ⟨lastMono l hd, lastMono_mem l hd⟩ = signedPermAut r 1 (signAt r l) := by
  have hσ := monoPermFun_eq (g := ⟨lastMono l hd, lastMono_mem l hd⟩) (autMat_lastMono l hd)
  refine LinearEquiv.toLinearMap_injective (linearMap_ext_eps fun j => ?_)
  rw [LinearEquiv.coe_coe, LinearEquiv.coe_coe, ← coordWt_inl, nuMono_coordWt, hσ,
    coordWt_inl, signedPermAut_eps, Equiv.Perm.coe_one, id_eq]
  by_cases hj : j = l
  · subst hj
    rw [Equiv.swap_apply_left, coordWt_inr, signAt_self, neg_one_smul]
  · rw [Equiv.swap_apply_of_ne_of_ne (by simp [hj]) (by simp), coordWt_inl, signAt_of_ne hj,
      one_smul]

end Last

section Generators

variable (hani : qA.Anisotropic) {a₀ : A} (ha₀ : a₀ ≠ 0)
include hani ha₀

theorem tailWeylElt_last_eq_blockHom {i : Fin r} (h : ¬i.val + 1 < r) :
    tailWeylElt r qA a₀ i = blockHom r qA (⟨lastMono i (qA_ne_zero hani ha₀),
      lastMono_mem i (qA_ne_zero hani ha₀)⟩,
        ⟨reflect qA a₀, reflect_mem_orthogonalGroup qA a₀⟩) := by
  have hd := qA_ne_zero hani ha₀
  have hQa : quadTail r qA ((0, a₀) : (Fin r ⊕ Fin r → K) × A) ≠ 0 := by rwa [quadTail_tail]
  have ha := tail_mem_perp_hypPairT (r := r) (qA := qA) i a₀
  rw [tailWeylElt_of_not_lt a₀ h]
  refine LinearEquiv.toLinearMap_injective (LinearMap.prod_ext ?_ ?_)
  · refine LinearMap.pi_ext fun c x => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.inl_apply]
    rw [blockHom_apply]
    simp only
    have hsx : ((Pi.single c x, 0) : (Fin r ⊕ Fin r → K) × A) = x • hypVec K A c := by
      rw [hypVec_smul, ← Pi.single_smul, smul_eq_mul, mul_one]
    rw [hsx, map_smul, show (Pi.single c x : Fin r ⊕ Fin r → K) = x • Pi.single c 1 by
      rw [← Pi.single_smul, smul_eq_mul, mul_one], map_smul, lastMono_single]
    by_cases hc1 : c = .inl i
    · subst hc1
      rw [← hypPairT_e (qA := qA), shortWeyl_e _ ha hQa, hypPairT_f, quadTail_tail, hypVec_smul,
        Equiv.swap_apply_left]
      simp [lastUnits]
    · by_cases hc2 : c = .inr i
      · subst hc2
        rw [← hypPairT_f (qA := qA), shortWeyl_f _ ha hQa, hypPairT_e, quadTail_tail, hypVec_smul,
          Equiv.swap_apply_right]
        simp [lastUnits]
      ·
        have hperp : hypVec K A c ∈ (hypPairT r qA i).perp := by
          rw [HypPair.mem_perp, hypPairT_e, hypPairT_f, polar_hypVec_hypVec,
            polar_hypVec_hypVec, ite_eq_right, ite_eq_right]
          · exact ⟨rfl, rfl⟩
          · rintro rfl; exact hc1 rfl
          · rintro rfl; exact hc2 rfl
        have h0 : polar (quadTail r qA) (hypVec K A c) ((0, a₀) : (Fin r ⊕ Fin r → K) × A) = 0 :=
          polar_hypVec_tail c a₀
        rw [shortWeyl_perp _ ha hQa hperp, h0, zero_mul, zero_smul, sub_zero,
          Equiv.swap_apply_of_ne_of_ne hc1 hc2, hypVec]
        simp [lastUnits, hc1, hc2]
  · refine LinearMap.ext fun b => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.inr_apply]
    rw [blockHom_apply, shortWeyl_perp _ ha hQa (tail_mem_perp_hypPairT i b), polar_tail_tail,
      quadTail_tail]
    simp only [map_zero]
    rw [reflect_apply hd, polar_comm, div_eq_mul_inv, Prod.smul_mk, smul_zero, Prod.mk_sub_mk,
      sub_zero]

theorem tailTorusWeyl_le_tailMono : tailTorusWeyl r qA a₀ ≤ tailMono r qA := by
  rw [tailTorusWeyl, Subgroup.closure_le]
  rintro _ (hx | ⟨i, rfl⟩)
  · exact tailTorus_le_tailMono hx
  · by_cases h : i.val + 1 < r
    · exact ⟨(⟨weylElt r K i, weylElt_mem_monoAut (by omega) i⟩, 1), by
        rw [tailWeylElt_eq_prodCongr a₀ h]
        exact LinearEquiv.ext fun _ => rfl⟩
    · exact ⟨_, (tailWeylElt_last_eq_blockHom hani ha₀ h).symm⟩

omit hani ha₀ in
theorem tailNu_tailTorus {g} (hg : g ∈ tailTorus r qA) :
    tailNu r qA ⟨g, tailTorus_le_tailMono hg⟩ = 1 := by
  obtain ⟨-, t, h, hh, rfl⟩ := hg
  rw [tailNu_eq (p := (⟨torusElt r K t, torusElt_mem_monoAut t⟩, ⟨h, hh⟩)) rfl]
  exact nuMono_torusElt t

theorem tailNu_tailWeylElt (i : Fin r) :
    tailNu r qA ⟨tailWeylElt r qA a₀ i,
      tailTorusWeyl_le_tailMono hani ha₀ (tailWeylElt_mem_tailTorusWeyl a₀ i)⟩ =
      simpleReflB r i := by
  by_cases h : i.val + 1 < r
  · rw [tailNu_eq (p := (⟨weylElt r K i, weylElt_mem_monoAut (by omega) i⟩, 1)) (by
      show _ = tailWeylElt r qA a₀ i
      rw [tailWeylElt_eq_prodCongr a₀ h]
      exact LinearEquiv.ext fun _ => rfl), simpleReflB_eq_simpleRefl h]
    exact nuMono_weylElt (by omega) i
  · rw [tailNu_eq (tailWeylElt_last_eq_blockHom hani ha₀ h).symm, simpleReflB_of_not_lt h]
    exact nuMono_lastMono i _

theorem tailNu_mem_weylGroupB {g} (hg : g ∈ tailTorusWeyl r qA a₀) :
    tailNu r qA ⟨g, tailTorusWeyl_le_tailMono hani ha₀ hg⟩ ∈ weylGroupB r := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | ⟨i, rfl⟩
    · rw [tailNu_tailTorus hx]
      exact one_mem _
    · rw [tailNu_tailWeylElt hani ha₀ i]
      exact simpleReflB_mem i
  | one =>
    have : (⟨1, tailTorusWeyl_le_tailMono hani ha₀ (one_mem _)⟩ : tailMono r qA) = 1 := rfl
    rw [this, map_one]
    exact one_mem _
  | mul x y hx hy ihx ihy =>
    have : (⟨x * y, tailTorusWeyl_le_tailMono hani ha₀ (mul_mem hx hy)⟩ : tailMono r qA) =
        ⟨x, tailTorusWeyl_le_tailMono hani ha₀ hx⟩ * ⟨y, tailTorusWeyl_le_tailMono hani ha₀ hy⟩ :=
      rfl
    rw [this, map_mul]
    exact mul_mem ihx ihy
  | inv x hx ihx =>
    have : (⟨x⁻¹, tailTorusWeyl_le_tailMono hani ha₀ (inv_mem hx)⟩ : tailMono r qA) =
        (⟨x, tailTorusWeyl_le_tailMono hani ha₀ hx⟩)⁻¹ := rfl
    rw [this, map_inv]
    exact inv_mem ihx

end Generators

section Nu

variable (hani : qA.Anisotropic) {a₀ : A} (ha₀ : a₀ ≠ 0)

variable (r qA) in
@[expose] noncomputable def tailTorusWeylNu : tailTorusWeyl r qA a₀ →* weylGroupB r :=
  ((tailNu r qA).comp (Subgroup.inclusion (tailTorusWeyl_le_tailMono hani ha₀))).codRestrict
    (weylGroupB r) fun n => tailNu_mem_weylGroupB hani ha₀ n.2

include hani ha₀

theorem coe_tailTorusWeylNu (n : tailTorusWeyl r qA a₀) :
    ((tailTorusWeylNu r qA hani ha₀ n : weylGroupB r) : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) =
      tailNu r qA ⟨n, tailTorusWeyl_le_tailMono hani ha₀ n.2⟩ :=
  rfl

theorem tailTorusWeylNu_tailWeylElt (i : Fin r) :
    tailTorusWeylNu r qA hani ha₀ ⟨tailWeylElt r qA a₀ i, tailWeylElt_mem_tailTorusWeyl a₀ i⟩ =
      ⟨simpleReflB r i, simpleReflB_mem i⟩ :=
  Subtype.ext (tailNu_tailWeylElt hani ha₀ i)

theorem exists_blockHom_eq (n : tailTorusWeyl r qA a₀) :
    ∃ p : monoAut r K × TauCeti.QuadraticMap.orthogonalGroup qA, blockHom r qA p = n ∧
      ((tailTorusWeylNu r qA hani ha₀ n : weylGroupB r) : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) =
        nuMono r K p.1 := by
  obtain ⟨p, hp⟩ := tailTorusWeyl_le_tailMono hani ha₀ n.2
  exact ⟨p, hp, by rw [coe_tailTorusWeylNu]; exact tailNu_eq hp⟩

theorem apply_tail_tailTorusWeyl (n : tailTorusWeyl r qA a₀) (a : A) :
    ∃ b : A, (n : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A))
      ((0 : Fin r ⊕ Fin r → K), a) = (0, b) := by
  obtain ⟨p, hp, -⟩ := exists_blockHom_eq hani ha₀ n
  refine ⟨(p.2 : A ≃ₗ[K] A) a, ?_⟩
  rw [← hp, blockHom_apply, map_zero]

theorem apply_hypVec_tailTorusWeylNu (n : tailTorusWeyl r qA a₀) (c : Fin r ⊕ Fin r) :
    ∃ (μ : Kˣ) (c' : Fin r ⊕ Fin r),
      (n : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _) (hypVec K A c) = (μ : K) • hypVec K A c' ∧
        coordWt c' =
          ((tailTorusWeylNu r qA hani ha₀ n : weylGroupB r) : (Fin r → ℤ) ≃ₗ[ℤ] _) (coordWt c) := by
  obtain ⟨p, hp, hν⟩ := exists_blockHom_eq hani ha₀ n
  obtain ⟨μ, -, hμ⟩ := exists_autMat_eq_monoPermFun p.1
  refine ⟨μ c, monoPermFun p.1 c, ?_, by rw [hν, nuMono_coordWt]⟩
  rw [← hp, blockHom_apply, hypVec, map_zero, apply_single_of_autMat hμ, hypVec_smul]

theorem tailTorusWeylNu_surjective : Function.Surjective (tailTorusWeylNu r qA hani ha₀) := by
  have key : ∀ w ∈ Subgroup.closure (Set.range (simpleReflB r)), ∃ n : tailTorusWeyl r qA a₀,
      ((tailTorusWeylNu r qA hani ha₀ n : weylGroupB r) : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) = w := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨_, congrArg Subtype.val (tailTorusWeylNu_tailWeylElt hani ha₀ i)⟩
    | one => exact ⟨1, by rw [map_one]; rfl⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨n, hn⟩ := ihx
      obtain ⟨m, hm⟩ := ihy
      exact ⟨n * m, by rw [map_mul, Subgroup.coe_mul, hn, hm]⟩
    | inv x _ ihx =>
      obtain ⟨n, hn⟩ := ihx
      exact ⟨n⁻¹, by rw [map_inv, Subgroup.coe_inv, hn]⟩
  rintro ⟨w, hw⟩
  obtain ⟨n, hn⟩ := key w (by rwa [closure_simpleReflB])
  exact ⟨n, Subtype.ext hn⟩

theorem tailTorusWeylNu_ker :
    (tailTorusWeylNu r qA hani ha₀).ker = (tailTorus r qA).subgroupOf (tailTorusWeyl r qA a₀) := by
  ext n
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h1
    obtain ⟨p, hp, hν⟩ := exists_blockHom_eq hani ha₀ n
    have h2 : nuMono r K p.1 = 1 := by rw [← hν, h1]; rfl
    rw [nuMono, MonoidHom.comp_apply, ← map_one wtHom] at h2
    have h3 := congrArg Subtype.val (wtHom_injective h2)
    rw [coe_monoPerm, OneMemClass.coe_one] at h3
    obtain ⟨μ, hμ, hmat⟩ := exists_autMat_eq_monoPermFun p.1
    rw [h3, signedPerm_one] at hmat
    have htor : (p.1 : (Fin r ⊕ Fin r → K) ≃ₗ[K] _) = torusElt r K fun i => μ (Sum.inl i) := by
      refine autMat_injective ?_
      rw [autMat_torusElt, hmat]
      congr 1
      funext x
      rcases x with i | i
      · rfl
      · change (μ (Sum.inr i) : K) = (((μ (Sum.inl i))⁻¹ : Kˣ) : K)
        rw [← hμ (Sum.inl i)]
        rfl
    refine ⟨tailTorusWeyl_le a₀ n.2, fun i => μ (Sum.inl i), p.2, p.2.2, ?_⟩
    rw [← hp, tailDiag]
    exact LinearEquiv.ext fun v => by rw [blockHom_apply, ← htor]; rfl
  · intro hn
    exact Subtype.ext (tailNu_tailTorus hn)

theorem tailWeylElt_sq_mem_tailTorus (i : Fin r) : tailWeylElt r qA a₀ i ^ 2 ∈ tailTorus r qA := by
  have hmem : (⟨tailWeylElt r qA a₀ i, tailWeylElt_mem_tailTorusWeyl a₀ i⟩ :
      tailTorusWeyl r qA a₀) ^ 2 ∈ (tailTorusWeylNu r qA hani ha₀).ker := by
    rw [MonoidHom.mem_ker, map_pow, tailTorusWeylNu_tailWeylElt hani ha₀ i]
    exact Subtype.ext (by rw [Subgroup.coe_pow, pow_two]; exact simpleReflB_mul_self i)
  rw [tailTorusWeylNu_ker hani ha₀, Subgroup.mem_subgroupOf] at hmem
  exact hmem

end Nu

section Conj

theorem tailLongGroup_eq_map (α : Fin r → ℤ) :
    tailLongGroup r qA α = (rootSubgroup r K α).map (prodHom A) := by
  ext g
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨rootElt r K α t, ⟨t, rfl⟩, (tailLongElt_eq_prodCongr α t).symm⟩
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    exact ⟨t, tailLongElt_eq_prodCongr α t⟩

theorem conj_blockHom_prodHom (p : monoAut r K × TauCeti.QuadraticMap.orthogonalGroup qA)
    (x : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :
    MulAut.conj (blockHom r qA p) (prodHom A x) =
      prodHom A (MulAut.conj (p.1 : (Fin r ⊕ Fin r → K) ≃ₗ[K] _) x) := by
  rw [MulAut.conj_apply, MulAut.conj_apply, ← map_inv (blockHom r qA)]
  refine LinearEquiv.ext fun v => ?_
  simp only [LinearEquiv.mul_apply, blockHom_apply, prodHom_apply, LinearEquiv.prodCongr_apply,
    LinearEquiv.refl_apply, Prod.fst_inv, Prod.snd_inv, Subgroup.coe_inv]
  rw [LinearEquiv.apply_inv_apply']

theorem mem_tailRootGroup_coordWt (c : Fin r ⊕ Fin r)
    {g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)} :
    g ∈ tailRootGroup r qA (coordWt c) ↔
      ∃ a : A, eichler (quadTail r qA) (hypVec K A c) (0, a) = g := by
  rcases c with i | i
  · rw [coordWt_inl]
    exact mem_tailRootGroup_eps
  · rw [coordWt_inr]
    exact mem_tailRootGroup_neg_eps

variable (hani : qA.Anisotropic) {a₀ : A} (ha₀ : a₀ ≠ 0)
include hani ha₀

theorem map_conj_tailRootGroup_short (n : tailTorusWeyl r qA a₀) (c : Fin r ⊕ Fin r) :
    (tailRootGroup r qA (coordWt c)).map
        (MulAut.conj (n : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _)).toMonoidHom =
      tailRootGroup r qA (((tailTorusWeylNu r qA hani ha₀ n : weylGroupB r) :
        (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) (coordWt c)) := by
  obtain ⟨p, hp, hν⟩ := exists_blockHom_eq hani ha₀ n
  obtain ⟨μ, -, hμ⟩ := exists_autMat_eq_monoPermFun p.1
  have hnO : (n : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _) ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadTail r qA) :=
    orthElementaryGroup_le _ (tailTorusWeyl_le a₀ n.2)
  have hnc : (n : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _) (hypVec K A c) =
      (μ c : K) • hypVec K A (monoPermFun p.1 c) := by
    rw [← hp, blockHom_apply, hypVec, map_zero, apply_single_of_autMat hμ, hypVec_smul]
  have hna : ∀ a : A, (n : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A))
      ((0 : Fin r ⊕ Fin r → K), a) = (0, (p.2 : A ≃ₗ[K] A) a) := fun a => by
    rw [← hp, blockHom_apply, map_zero]
  have hconj : ∀ a : A, MulAut.conj (n : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K]
      ((Fin r ⊕ Fin r → K) × A)) (eichler (quadTail r qA) (hypVec K A c) (0, a)) =
        eichler (quadTail r qA) (hypVec K A (monoPermFun p.1 c))
          (0, (μ c : K) • (p.2 : A ≃ₗ[K] A) a) := by
    intro a
    rw [MulAut.conj_apply, eichler_conj hnO, hnc, hna, eichler_smul_left, Prod.smul_mk,
      smul_zero]
  rw [hν, nuMono_coordWt]
  ext g
  rw [Subgroup.mem_map, mem_tailRootGroup_coordWt]
  constructor
  · rintro ⟨_, h, rfl⟩
    obtain ⟨a, rfl⟩ := (mem_tailRootGroup_coordWt c).1 h
    exact ⟨_, (hconj a).symm⟩
  · rintro ⟨b, rfl⟩
    refine ⟨eichler (quadTail r qA) (hypVec K A c)
      (0, (p.2 : A ≃ₗ[K] A).symm ((μ c : K)⁻¹ • b)), (mem_tailRootGroup_coordWt c).2 ⟨_, rfl⟩,
      ?_⟩
    change MulAut.conj _ _ = _
    rw [hconj, LinearEquiv.apply_symm_apply, smul_smul, mul_inv_cancel₀ (μ c).ne_zero, one_smul]

theorem map_conj_tailRootGroup_long (n : tailTorusWeyl r qA a₀) {α : Fin r → ℤ}
    (hlong : α ∈ roots r) :
    (tailRootGroup r qA α).map
        (MulAut.conj (n : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _)).toMonoidHom =
      tailRootGroup r qA (((tailTorusWeylNu r qA hani ha₀ n : weylGroupB r) :
        (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) α) := by
  obtain ⟨p, hp, hν⟩ := exists_blockHom_eq hani ha₀ n
  have hνα : ((tailTorusWeylNu r qA hani ha₀ n : weylGroupB r) :
      (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) α ∈ roots r := by
    obtain ⟨σ, δ, h⟩ := (tailTorusWeylNu r qA hani ha₀ n).2
    rw [h]
    exact signedPermAut_mem_roots σ δ hlong
  rw [tailRootGroup_of_mem_roots hlong, tailRootGroup_of_mem_roots hνα, tailLongGroup_eq_map,
    tailLongGroup_eq_map, hν, ← map_conj_rootSubgroup p.1 hlong, Subgroup.map_map,
    Subgroup.map_map]
  congr 1
  refine MonoidHom.ext fun x => ?_
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [← hp]
  exact conj_blockHom_prodHom p x

theorem map_conj_tailRootGroup (n : tailTorusWeyl r qA a₀) {α : Fin r → ℤ} (hα : α ∈ rootsB r) :
    (tailRootGroup r qA α).map
        (MulAut.conj (n : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _)).toMonoidHom =
      tailRootGroup r qA (((tailTorusWeylNu r qA hani ha₀ n : weylGroupB r) :
        (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) α) := by
  rcases hα with ⟨i, rfl | rfl⟩ | hlong
  · rw [← coordWt_inl]
    exact map_conj_tailRootGroup_short hani ha₀ n _
  · rw [← coordWt_inr]
    exact map_conj_tailRootGroup_short hani ha₀ n _
  · exact map_conj_tailRootGroup_long hani ha₀ n hlong

end Conj

section Flags

theorem blockHom_smul_tailFlag_eq_iff (p : monoAut r K × TauCeti.QuadraticMap.orthogonalGroup qA)
    (k : ℕ) :
    blockHom r qA p • tailFlag K A r k = tailFlag K A r k ↔
      (p.1 : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) • flag r K k = flag r K k := by
  have hcomm : ((blockHom r qA p : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) :
      ((Fin r ⊕ Fin r → K) × A) →ₗ[K] ((Fin r ⊕ Fin r → K) × A)).comp
        (LinearMap.inl K (Fin r ⊕ Fin r → K) A) =
      (LinearMap.inl K (Fin r ⊕ Fin r → K) A).comp
        ((p.1 : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :
          (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) :=
    LinearMap.ext fun v => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.inl_apply, blockHom_apply,
        map_zero]
  have h1 : blockHom r qA p • tailFlag K A r k =
      ((flag r K k).map ((p.1 : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :
        (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K))).map
          (LinearMap.inl K (Fin r ⊕ Fin r → K) A) := by
    rw [tailFlag_eq_map]
    change Submodule.map ((blockHom r qA p : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K]
        ((Fin r ⊕ Fin r → K) × A)) : ((Fin r ⊕ Fin r → K) × A) →ₗ[K] ((Fin r ⊕ Fin r → K) × A))
        (Submodule.map (LinearMap.inl K (Fin r ⊕ Fin r → K) A) (flag r K k)) = _
    rw [← Submodule.map_comp, hcomm, Submodule.map_comp]
  have h2 : (p.1 : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) • flag r K k =
      (flag r K k).map ((p.1 : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :
        (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) := rfl
  rw [h1, h2, tailFlag_eq_map]
  exact (Submodule.map_injective_of_injective LinearMap.inl_injective).eq_iff

theorem mem_flagCoords {k : ℕ} {c : Fin r ⊕ Fin r} :
    c ∈ (Sum.inl '' {j : Fin r | (j : ℕ) < k} : Set (Fin r ⊕ Fin r)) ↔
      ∃ j : Fin r, (j : ℕ) < k ∧ c = Sum.inl j := by
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, rfl⟩

variable (hani : qA.Anisotropic) {a₀ : A} (ha₀ : a₀ ≠ 0)
include hani ha₀

theorem tailWeylElt_smul_tailFlag (i j : Fin r) :
    (tailWeylElt r qA a₀ j • tailFlag K A r (i + 1) = tailFlag K A r (i + 1) ↔ j ≠ i) := by
  set S : Set (Fin r ⊕ Fin r) := Sum.inl '' {k : Fin r | (k : ℕ) < i + 1} with hS
  have hmemS : ∀ k : Fin r, Sum.inl k ∈ S ↔ (k : ℕ) < i + 1 := fun k =>
    ⟨fun ⟨k', hk', hkk'⟩ => by rw [← Sum.inl_injective hkk']; exact hk', fun hk => ⟨k, hk, rfl⟩⟩
  have hinr : ∀ k : Fin r, Sum.inr k ∉ S := fun k ⟨_, _, h⟩ => Sum.inl_ne_inr h
  by_cases hj : j.val + 1 < r
  ·
    have hr2 : 2 ≤ r := by omega
    rw [show tailWeylElt r qA a₀ j = blockHom r qA (⟨weylElt r K j, weylElt_mem_monoAut hr2 j⟩, 1)
        by rw [tailWeylElt_eq_prodCongr a₀ hj]; exact LinearEquiv.ext fun _ => rfl,
      blockHom_smul_tailFlag_eq_iff, flag_eq_coordSpan]
    change weylElt r K j • coordSpan K S = coordSpan K S ↔ _
    rw [weylElt_smul_coordSpan_eq_iff hr2]
    constructor
    · rintro h rfl
      refine image_ne_self_of_mem (S := S) (c := Sum.inl j) ((hmemS j).2 (by omega)) ?_ h
      rw [weylPerm_inl_of_lt hr2 hj, Equiv.swap_apply_left, hmemS]
      simp only
      omega
    · intro hji
      refine image_eq_self_of_mapsTo (weylPerm_mul_self hr2 j) fun c hc => ?_
      obtain ⟨k, hk, rfl⟩ := hc
      have hk' : (k : ℕ) < i + 1 := hk
      rw [weylPerm_inl_of_lt hr2 hj, hmemS]
      have hji' : j.val ≠ i.val := fun h => hji (Fin.ext h)
      rw [Equiv.swap_apply_def]
      split_ifs with h1 h2
      · subst h1
        simp only
        omega
      · subst h2
        simp only at hk' ⊢
        omega
      · exact hk'
  ·
    have hd := qA_ne_zero hani ha₀
    rw [tailWeylElt_last_eq_blockHom hani ha₀ hj, blockHom_smul_tailFlag_eq_iff,
      flag_eq_coordSpan]
    change lastMono j hd • coordSpan K S = coordSpan K S ↔ _
    rw [smul_coordSpan_eq_iff (fun c => (lastUnits j hd c).ne_zero) (autMat_lastMono j hd)]
    constructor
    · rintro h rfl
      refine image_ne_self_of_mem (S := S) (c := Sum.inl j) ((hmemS j).2 (by omega)) ?_ h
      rw [Equiv.swap_apply_left]
      exact hinr j
    · intro hji
      refine image_eq_self_of_mapsTo (Equiv.swap_mul_self _ _) fun c hc => ?_
      obtain ⟨k, hk, rfl⟩ := hc
      have hk' : (k : ℕ) < i + 1 := hk
      have hkj : k ≠ j := by
        rintro rfl
        have := i.isLt
        exact hji (Fin.ext (by omega))
      rw [Equiv.swap_apply_of_ne_of_ne (by simp [hkj]) (by simp)]
      exact (hmemS k).2 hk'

end Flags


theorem orthogonal_geometry_tail_Weyl_lifts {K : Type*} [Field K] {A : Type*} [AddCommGroup A]
    [Module K A] {r : ℕ} {qA : QuadraticForm K A} (hani : qA.Anisotropic) {a₀ : A}
    (ha₀ : a₀ ≠ 0) :
    (∀ n : tailTorusWeyl r qA a₀,
      (∀ a : A, ∃ b : A, (n : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A))
        ((0 : Fin r ⊕ Fin r → K), a) = (0, b)) ∧
      ∀ c : Fin r ⊕ Fin r, ∃ (μ : Kˣ) (c' : Fin r ⊕ Fin r),
        (n : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) (hypVec K A c) =
          (μ : K) • hypVec K A c' ∧
        coordWt c' = ((tailTorusWeylNu r qA hani ha₀ n : weylGroupB r) :
          (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) (coordWt c)) ∧
    Function.Surjective (tailTorusWeylNu r qA hani ha₀) ∧
    (tailTorusWeylNu r qA hani ha₀).ker = (tailTorus r qA).subgroupOf (tailTorusWeyl r qA a₀) ∧
    (∀ i, tailTorusWeylNu r qA hani ha₀
        ⟨tailWeylElt r qA a₀ i, tailWeylElt_mem_tailTorusWeyl a₀ i⟩ =
      ⟨simpleReflB r i, simpleReflB_mem i⟩) ∧
    (∀ (n : tailTorusWeyl r qA a₀) (α : Fin r → ℤ), α ∈ rootsB r →
      (tailRootGroup r qA α).map (MulAut.conj
          (n : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A))).toMonoidHom =
        tailRootGroup r qA (((tailTorusWeylNu r qA hani ha₀ n : weylGroupB r) :
          (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) α)) ∧
    (∀ i, tailWeylElt r qA a₀ i ^ 2 ∈ tailTorus r qA) ∧
    ∀ i j : Fin r,
      (tailWeylElt r qA a₀ j • tailFlag K A r (i + 1) = tailFlag K A r (i + 1) ↔ j ≠ i) :=
  ⟨fun n => ⟨apply_tail_tailTorusWeyl hani ha₀ n, apply_hypVec_tailTorusWeylNu hani ha₀ n⟩,
    tailTorusWeylNu_surjective hani ha₀, tailTorusWeylNu_ker hani ha₀,
    tailTorusWeylNu_tailWeylElt hani ha₀, fun n _ hα => map_conj_tailRootGroup hani ha₀ n hα,
    tailWeylElt_sq_mem_tailTorus hani ha₀, tailWeylElt_smul_tailFlag hani ha₀⟩

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
