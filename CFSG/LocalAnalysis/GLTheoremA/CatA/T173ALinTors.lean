module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ALinDefs
import CFSG.Assembly.GL83StatedBridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open scoped MatrixGroups

private def diagHom (d : ℕ) (F : Type) [Field F] : (Fin d → Fˣ) →* GL (Fin d) F where
  toFun f :=
    ⟨Matrix.diagonal fun i => (f i : F), Matrix.diagonal fun i => ((f i)⁻¹ : F),
      by
        rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one,
          Matrix.diagonal_injective.eq_iff]
        funext i
        simpa using (f i).mul_inv,
      by
        rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one,
          Matrix.diagonal_injective.eq_iff]
        funext i
        simpa using (f i).inv_mul⟩
  map_one' := by
    apply Units.ext
    simp
  map_mul' f g := by
    apply Units.ext
    simp [Matrix.diagonal_mul_diagonal]

@[simp] private theorem coe_diagHom {d : ℕ} {F : Type} [Field F] (f : Fin d → Fˣ) :
    ((diagHom d F f : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
      Matrix.diagonal fun i => (f i : F) := rfl

private theorem diagHom_injective (d : ℕ) (F : Type) [Field F] :
    Function.Injective (diagHom d F) := by
  intro f g h
  funext i
  have h' := congrArg (fun A : GL (Fin d) F => (A : Matrix (Fin d) (Fin d) F) i i) h
  rw [coe_diagHom, coe_diagHom, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq] at h'
  exact Units.ext h'

private def rootsPi (d p : ℕ) (F : Type) [Field F] :
    (Fin d → rootsOfUnity p F) →* (Fin d → Fˣ) :=
  MonoidHom.pi fun i =>
    (Subgroup.subtype (rootsOfUnity p F)).comp
      (Pi.evalMonoidHom (fun _ => rootsOfUnity p F) i)

@[simp] private theorem rootsPi_apply {d p : ℕ} {F : Type} [Field F]
    (f : Fin d → rootsOfUnity p F) (i : Fin d) :
    (rootsPi d p F f) i = (f i : Fˣ) := rfl

private theorem rootsPi_injective (d p : ℕ) (F : Type) [Field F] :
    Function.Injective (rootsPi d p F) := by
  intro f g h
  funext i
  have h' := congrFun h i
  simpa using h'

private def prodRoots (d p : ℕ) (F : Type) [Field F] :
    (Fin d → rootsOfUnity p F) →* rootsOfUnity p F where
  toFun f := ⟨∏ i, (f i : Fˣ), by
    rw [mem_rootsOfUnity, ← Finset.prod_pow]
    exact Finset.prod_eq_one fun i _ =>
      (mem_rootsOfUnity p (f i : Fˣ)).mp (f i).2⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' f g := by
    apply Subtype.ext
    show (∏ i, ((f * g) i : Fˣ)) = (∏ i, (f i : Fˣ)) * (∏ i, (g i : Fˣ))
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => rfl

@[simp] private theorem prodRoots_apply {d p : ℕ} {F : Type} [Field F]
    (f : Fin d → rootsOfUnity p F) :
    ((prodRoots d p F f : rootsOfUnity p F) : Fˣ) = ∏ i, (f i : Fˣ) := rfl

private def diagP (p d : ℕ) (F : Type) [Field F] : Subgroup (GL (Fin d) F) :=
  (prodRoots d p F).ker.map ((diagHom d F).comp (rootsPi d p F))

private theorem diagP_pow {p d : ℕ} {F : Type} [Field F] {x : GL (Fin d) F}
    (hx : x ∈ diagP p d F) : x ^ p = 1 := by
  rw [diagP] at hx
  obtain ⟨f, _, rfl⟩ := Subgroup.mem_map.mp hx
  rw [MonoidHom.comp_apply, ← map_pow,
    (map_pow (rootsPi d p F) f p).symm]
  have hfp : f ^ p = 1 := by
    funext i
    exact Subtype.ext ((mem_rootsOfUnity p (f i : Fˣ)).mp (f i).2)
  rw [hfp, map_one, map_one]

private theorem diagP_diag {p d : ℕ} {F : Type} [Field F] {x : GL (Fin d) F}
    (hx : x ∈ diagP p d F) {i j : Fin d} (hij : i ≠ j) :
    (x : Matrix (Fin d) (Fin d) F) i j = 0 := by
  rw [diagP] at hx
  obtain ⟨f, _, rfl⟩ := Subgroup.mem_map.mp hx
  rw [MonoidHom.comp_apply, coe_diagHom, Matrix.diagonal_apply_ne _ hij]

private theorem diagP_mem_of {p d : ℕ} {F : Type} [Field F] {a : GL (Fin d) F}
    (haSL : a ∈ LinSL d F) (hap : a ^ p = 1)
    (hadiag : ∀ i j : Fin d, i ≠ j → (a : Matrix (Fin d) (Fin d) F) i j = 0) :
    a ∈ diagP p d F := by
  have hdiag : (a : Matrix (Fin d) (Fin d) F) =
      Matrix.diagonal (fun i => (a : Matrix (Fin d) (Fin d) F) i i) := by
    ext i j
    by_cases hij : i = j
    · subst hij; rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ hij]; exact hadiag i j hij
  have hdet_ne : (a : Matrix (Fin d) (Fin d) F).det ≠ 0 := by
    simpa using (Matrix.GeneralLinearGroup.det a).ne_zero
  have hne : ∀ i, (a : Matrix (Fin d) (Fin d) F) i i ≠ 0 := by
    intro i hi0
    apply hdet_ne
    rw [hdiag, Matrix.det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi0
  have hpow : (a : Matrix (Fin d) (Fin d) F) ^ p = 1 := by
    have h := congrArg (fun g : GL (Fin d) F => (g : Matrix (Fin d) (Fin d) F)) hap
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at h
  have hdiag_pow : ∀ i, (a : Matrix (Fin d) (Fin d) F) i i ^ p = 1 := by
    intro i
    have h := congrArg (fun M : Matrix (Fin d) (Fin d) F => M i i) hpow
    rw [hdiag, Matrix.diagonal_pow, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h
    simpa only [Pi.pow_apply] using h
  have hdet_a : (a : Matrix (Fin d) (Fin d) F).det = 1 := by
    have hmem : a ∈ LargeEvenSLGroup (Fin d) F := haSL
    rw [CFSG.Assembly.largeEvenSLGroup_eq_statedSL] at hmem
    exact CFSG.Open.StatedAPI.mem_statedSL_iff.mp hmem
  let f : Fin d → rootsOfUnity p F := fun i =>
    ⟨Units.mk0 ((a : Matrix (Fin d) (Fin d) F) i i) (hne i), by
      rw [mem_rootsOfUnity]
      exact Units.ext (by simpa using hdiag_pow i)⟩
  have hf_eq : (diagHom d F) ((rootsPi d p F) f) = a := by
    apply Units.ext
    rw [coe_diagHom, hdiag]
    rfl
  have hfun : (fun i => ((f i : Fˣ) : F)) =
      (fun i => (a : Matrix (Fin d) (Fin d) F) i i) := by
    funext i
    rfl
  have hprodF : ∏ i, ((f i : Fˣ) : F) = 1 := by
    rw [hfun, ← Matrix.det_diagonal, ← hdiag]
    exact hdet_a
  have hprod_unit : ∏ i, (f i : Fˣ) = 1 := by
    apply Units.ext
    rw [Units.coe_prod]
    simpa using hprodF
  have hfker : f ∈ (prodRoots d p F).ker := by
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    rw [prodRoots_apply]
    simpa using hprod_unit
  rw [diagP]
  exact Subgroup.mem_map.mpr ⟨f, hfker, hf_eq⟩

private theorem diagP_le_linSL {p d : ℕ} {F : Type} [Field F] :
    diagP p d F ≤ LinSL d F := by
  intro x hx
  obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.mp hx
  rw [MonoidHom.comp_apply]
  change (diagHom d F) ((rootsPi d p F) f) ∈ LargeEvenSLGroup (Fin d) F
  rw [CFSG.Assembly.largeEvenSLGroup_eq_statedSL, CFSG.Open.StatedAPI.mem_statedSL_iff]
  have hprod : ∏ i, ((rootsPi d p F) f i : F) = 1 := by
    have hker : (prodRoots d p F) f = 1 := MonoidHom.mem_ker.mp hf
    have hcoe : ∏ i, ((rootsPi d p F) f i : F) =
        ((((prodRoots d p F) f : rootsOfUnity p F) : Fˣ) : F) := by
      rw [prodRoots_apply, Units.coe_prod]
      rfl
    rw [hcoe, hker]
    rfl
  rw [coe_diagHom, Matrix.det_diagonal]
  exact hprod

private theorem isElemAbelian_diagP {p d : ℕ} {F : Type} [Field F] :
    IsElemAbelian p (diagP p d F) := by
  refine ⟨⟨⟨?_⟩⟩, ?_⟩
  · rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
    apply Subtype.ext
    change ((diagHom d F).comp (rootsPi d p F)) a * ((diagHom d F).comp (rootsPi d p F)) b =
      ((diagHom d F).comp (rootsPi d p F)) b * ((diagHom d F).comp (rootsPi d p F)) a
    rw [(map_mul ((diagHom d F).comp (rootsPi d p F)) a b).symm,
      (map_mul ((diagHom d F).comp (rootsPi d p F)) b a).symm, mul_comm a b]
  · rintro _ ⟨a, ha, rfl⟩
    rw [MonoidHom.comp_apply, ← map_pow, (map_pow (rootsPi d p F) a p).symm]
    have hap : a ^ p = 1 := by
      funext i
      exact Subtype.ext ((mem_rootsOfUnity p (a i : Fˣ)).mp (a i).2)
    rw [hap, map_one, map_one]

private theorem card_rootsOfUnity_prime {p : ℕ} {F : Type} [Field F] [Finite F]
    (hp : p.Prime) (hdvd : p ∣ Nat.card F - 1) :
    Nat.card (rootsOfUnity p F) = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hdvd' : p ∣ Nat.card Fˣ := by rwa [Nat.card_units F]
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd'
  have hxroot : x ∈ rootsOfUnity p F := by
    rw [mem_rootsOfUnity, ← hx]
    exact pow_orderOf_eq_one x
  have hle : Subgroup.zpowers x ≤ rootsOfUnity p F := Subgroup.zpowers_le.mpr hxroot
  have hge : Nat.card (rootsOfUnity p F) ≤ Nat.card (Subgroup.zpowers x) := by
    rw [Nat.card_zpowers, hx]
    exact card_rootsOfUnity F p
  have heq : Subgroup.zpowers x = rootsOfUnity p F := Subgroup.eq_of_le_of_card_ge hle hge
  rw [← heq, Nat.card_zpowers, hx]

private theorem card_diagP {p d : ℕ} {F : Type} [Field F] [Finite F]
    (hp : p.Prime) (hdvd : p ∣ Nat.card F - 1) (hd : 1 ≤ d) :
    Nat.card (diagP p d F) = p ^ (d - 1) := by
  have hinj : Function.Injective ((diagHom d F).comp (rootsPi d p F)) :=
    (diagHom_injective d F).comp (rootsPi_injective d p F)
  rw [diagP, Subgroup.card_map_of_injective (K := (prodRoots d p F).ker)
    (f := (diagHom d F).comp (rootsPi d p F)) hinj]
  have hsurj : Function.Surjective (prodRoots d p F) := by
    intro ζ
    refine ⟨Pi.mulSingle ⟨0, hd⟩ ζ, ?_⟩
    apply Subtype.ext
    rw [prodRoots_apply]
    exact Finset.prod_eq_single (⟨0, hd⟩ : Fin d)
      (fun b _ hb => by rw [Pi.mulSingle_eq_of_ne hb]; rfl)
      (fun h => absurd (Finset.mem_univ _) h)
  have hcard := Subgroup.card_ker_mul_card_of_surjective (f := prodRoots d p F) hsurj
  rw [Nat.card_fun, Nat.card_fin, card_rootsOfUnity_prime hp hdvd] at hcard
  have hle : p ^ (d - 1) * p = Nat.card (prodRoots d p F).ker * p := by
    rw [← pow_succ, Nat.sub_add_cancel hd, hcard]
  exact Nat.eq_of_mul_eq_mul_right hp.pos hle.symm

private theorem scalar_eq_one_of_mem_diagP {p d : ℕ} {F : Type} [Field F]
    (hp : p.Prime) (hpd : ¬ p ∣ d) (hd : 1 ≤ d) {z : GL (Fin d) F}
    (hz : z ∈ diagP p d F) (hzsc : z ∈ LargeEvenScalars (Fin d) F) : z = 1 := by
  obtain ⟨f, hf, hfz⟩ := Subgroup.mem_map.mp hz
  rw [CFSG.Assembly.largeEvenScalars_def] at hzsc
  obtain ⟨c, hc⟩ := hzsc
  have hzSL : z ∈ LinSL d F := diagP_le_linSL hz
  have hdet_z : (z : Matrix (Fin d) (Fin d) F).det = 1 := by
    have hmem : z ∈ LargeEvenSLGroup (Fin d) F := hzSL
    rw [CFSG.Assembly.largeEvenSLGroup_eq_statedSL] at hmem
    exact CFSG.Open.StatedAPI.mem_statedSL_iff.mp hmem
  have hval : (c : F) = ((f ⟨0, hd⟩ : Fˣ) : F) := by
    have hEq : Matrix.GeneralLinearGroup.scalar (Fin d) c =
        diagHom d F (rootsPi d p F f) := by
      rw [hc, ← hfz, MonoidHom.comp_apply]
    have h' := congrArg (fun A : GL (Fin d) F =>
      (A : Matrix (Fin d) (Fin d) F) ⟨0, hd⟩ ⟨0, hd⟩) hEq
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, coe_diagHom,
      Matrix.diagonal_apply_eq] at h'
    exact h'
  have hcp : c ^ p = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hval, ← Units.val_pow_eq_pow_val,
      (mem_rootsOfUnity p (f ⟨0, hd⟩ : Fˣ)).mp (f ⟨0, hd⟩).2,
      Units.val_one]
  have hdet_scalar : ((Matrix.GeneralLinearGroup.scalar (Fin d) c : GL (Fin d) F) :
      Matrix (Fin d) (Fin d) F).det = ((c ^ d : Fˣ) : F) := by
    have h := Matrix.GeneralLinearGroup.det_scalar (n := Fin d) c
    rw [Fintype.card_fin] at h
    exact congrArg (fun u : Fˣ => (u : F)) h
  have hcd : c ^ d = 1 := by
    apply Units.ext
    rw [← hdet_scalar, hc]
    simpa using hdet_z
  have hcop : Nat.Coprime p d := hp.coprime_iff_not_dvd.mpr hpd
  have hc1 : c = 1 := by
    have h := pow_gcd_eq_one.2 ⟨hcp, hcd⟩
    rwa [hcop.gcd_eq_one, pow_one] at h
  rw [← hc, hc1, map_one]

theorem lin_diagTorsion_data {p n d : ℕ} {F : Type} [Field F] [Finite F] (h : LinArith p n d F) :
    LinDiagTorsion p d F ≤ LinSL d F ∧ IsElemAbelian p (LinDiagTorsion p d F) ∧
      Nat.card (LinDiagTorsion p d F) = p ^ (d - 1) ∧
      ∀ z ∈ LinDiagTorsion p d F, z ∈ LargeEvenScalars (Fin d) F → z = 1 := by
  obtain ⟨hp, hp2, hpdvd, hpd, hcard, hn, hd⟩ := h
  have hdvd : p ∣ Nat.card F - 1 := by rw [hcard]; exact hpdvd
  have hd' : 1 ≤ d := by omega
  have heq : LinDiagTorsion p d F = diagP p d F := by
    apply le_antisymm
    · rw [LinDiagTorsion, Subgroup.closure_le]
      intro a ha
      exact diagP_mem_of ha.1 ha.2.1 ha.2.2
    · intro x hx
      rw [LinDiagTorsion]
      exact Subgroup.subset_closure
        ⟨diagP_le_linSL hx, diagP_pow hx, fun i j hij => diagP_diag hx hij⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [heq]; exact diagP_le_linSL
  · rw [heq]; exact isElemAbelian_diagP
  · rw [heq]; exact card_diagP hp hdvd hd'
  · intro z hz hzsc
    rw [heq] at hz
    exact scalar_eq_one_of_mem_diagP hp hpd hd' hz hzsc

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
