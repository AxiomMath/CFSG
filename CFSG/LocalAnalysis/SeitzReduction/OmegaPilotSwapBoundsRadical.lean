module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogOmegaFlagRadical
public import CFSG.RankThree.OrthogonalInvolutions.Basic
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal

section Counting

variable {G : Type*} [Group G]

theorem card_mul_card_le_card_of_inf_eq_bot {H A B : Subgroup G} [Finite H] (hA : A ≤ H)
    (hB : B ≤ H) (hAB : A ⊓ B = ⊥) : Nat.card A * Nat.card B ≤ Nat.card H := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun p : A × B => (⟨p.1.1 * p.2.1, H.mul_mem (hA p.1.2) (hB p.2.2)⟩ : H)) ?_
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  have h1 : (a : G) * b = a' * b' := congrArg Subtype.val h
  set x : G := ↑a
  set y : G := ↑b
  set x' : G := ↑a'
  set y' : G := ↑b'
  have h2 : x'⁻¹ * x = y' * y⁻¹ := by
    calc x'⁻¹ * x = x'⁻¹ * (x * y) * y⁻¹ := by group
      _ = x'⁻¹ * (x' * y') * y⁻¹ := by rw [h1]
      _ = y' * y⁻¹ := by group
  have hmem : x'⁻¹ * x ∈ A ⊓ B :=
    ⟨A.mul_mem (A.inv_mem a'.2) a.2, h2 ▸ B.mul_mem b'.2 (B.inv_mem b.2)⟩
  rw [hAB, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  have hb : y = y' := by
    rw [← hmem] at h1
    exact mul_left_cancel h1
  exact Prod.ext (Subtype.ext hmem.symm) (Subtype.ext hb)

theorem prod_card_le_card_of_chain [Finite G] (R A : ℕ → Subgroup G)
    (hR : ∀ i, R (i + 1) ≤ R i) :
    ∀ m : ℕ, (∀ i < m, A i ≤ R i) → (∀ i < m, A i ⊓ R (i + 1) = ⊥) →
      (∏ i ∈ Finset.range m, Nat.card (A i)) * Nat.card (R m) ≤ Nat.card (R 0) := by
  intro m
  induction m with
  | zero => intro _ _; simp
  | succ m ih =>
    intro hA hAR
    have h1 := card_mul_card_le_card_of_inf_eq_bot (hA m (by omega)) (hR m) (hAR m (by omega))
    have h2 := ih (fun i hi => hA i (by omega)) (fun i hi => hAR i (by omega))
    rw [Finset.prod_range_succ, mul_assoc]
    exact le_trans (Nat.mul_le_mul_left _ h1) h2

end Counting

section Commute

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem eichler_commute_of_apply_eq {t : V ≃ₗ[K] V}
    (ht : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {u w : V} (htu : t u = u) (htw : t w = w) :
    t * eichler Q u w = eichler Q u w * t := by
  have h := eichler_conj ht u w
  rw [htu, htw] at h
  calc t * eichler Q u w = t * eichler Q u w * t⁻¹ * t := by group
    _ = eichler Q u w * t := by rw [h]

end Commute

section Data

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

variable {K : Type} [Field K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))

@[expose] def fixFamily {m : ℕ} (f : Fin m → (Fin d → K)) (i : ℕ) : Subgroup (GL (Fin d) K) where
  carrier := {g | ∀ j : Fin m, j.val < i → matrixLinearIso g (f j) = f j}
  one_mem' := fun j _ => by rw [map_one]; rfl
  mul_mem' := fun {g h} hg hh j hj => by
    rw [map_mul, LinearEquiv.mul_apply, hh j hj, hg j hj]
  inv_mem' := fun {g} hg j hj => by
    have h1 := hg j hj
    calc matrixLinearIso g⁻¹ (f j) = matrixLinearIso g⁻¹ (matrixLinearIso g (f j)) := by rw [h1]
      _ = f j := by rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl

theorem fixFamily_antitone {m : ℕ} (f : Fin m → (Fin d → K)) (i : ℕ) :
    fixFamily f (i + 1) ≤ fixFamily f i := fun _ hg j hj => hg j (by omega)

@[expose] def radicalKer {m : ℕ} (e f : Fin m → (Fin d → K)) (a : Fin d → K) :
    Submodule K (Fin d → K) :=
  LinearMap.ker (LinearMap.prod (LinearMap.pi fun i => polarBilin Q (e i))
    (LinearMap.prod (LinearMap.pi fun j => polarBilin Q (f j)) (polarBilin Q a)))

variable {Q}

theorem mem_radicalKer {m : ℕ} {e f : Fin m → (Fin d → K)} {a v : Fin d → K} :
    v ∈ radicalKer Q e f a ↔
      (∀ i, polar Q (e i) v = 0) ∧ (∀ j, polar Q (f j) v = 0) ∧ polar Q a v = 0 := by
  simp only [radicalKer, LinearMap.mem_ker, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero, funext_iff,
    Pi.zero_apply]
  rfl

variable (Q) in
theorem finrank_radicalKer_ge {m : ℕ} (e f : Fin m → (Fin d → K)) (a : Fin d → K) :
    d - (2 * m + 1) ≤ Module.finrank K (radicalKer Q e f a) := by
  set L := LinearMap.prod (LinearMap.pi fun i => polarBilin Q (e i))
    (LinearMap.prod (LinearMap.pi fun j => polarBilin Q (f j)) (polarBilin Q a))
  have h1 := LinearMap.finrank_range_add_finrank_ker L
  have h2 : Module.finrank K (LinearMap.range L) ≤ 2 * m + 1 := by
    refine (Submodule.finrank_le _).trans ?_
    simp only [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_self]
    omega
  rw [Module.finrank_fin_fun] at h1
  change d - (2 * m + 1) ≤ Module.finrank K (LinearMap.ker L)
  omega

variable (Q) in
@[expose] def rootParams {m : ℕ} (e f : Fin m → (Fin d → K)) (a : Fin d → K) (i : ℕ) :
    Submodule K (Fin d → K) :=
  radicalKer Q e f a ⊔ Submodule.span K (Set.range fun k : {k : Fin m // i < k.val} => e k)

end Data

section Root

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {m : ℕ}
  {e f : Fin m → (Fin d → K)} {a : Fin d → K}

theorem polar_f_eq_zero_of_mem_rootParams
    (hef : ∀ i j, polar Q (e i) (f j) = if i = j then 1 else 0) {i : ℕ} {u : Fin d → K}
    (hu : u ∈ rootParams Q e f a i) (j : Fin m) (hj : j.val ≤ i) : polar Q (f j) u = 0 := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hu
  rw [polar_add_right, (mem_radicalKer.mp hy).2.1 j, zero_add]
  refine Submodule.span_induction (p := fun z _ => polar Q (f j) z = 0) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨k, rfl⟩
    rw [polar_comm, hef]
    have hne : (k : Fin m) ≠ j := by
      intro h
      have := k.2
      rw [h] at this
      omega
    simp [hne]
  · exact polar_zero_right Q _
  · intro x y _ _ hx hy
    rw [polar_add_right, hx, hy, add_zero]
  · intro c x _ hx
    rw [polar_smul_right, hx, smul_zero]

theorem polar_e_eq_zero_of_mem_rootParams (hee : ∀ i j, polar Q (e i) (e j) = 0) {i : ℕ}
    {u : Fin d → K} (hu : u ∈ rootParams Q e f a i) (j : Fin m) : polar Q (e j) u = 0 := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hu
  rw [polar_add_right, (mem_radicalKer.mp hy).1 j, zero_add]
  refine Submodule.span_induction (p := fun z _ => polar Q (e j) z = 0) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨k, rfl⟩
    exact hee j k
  · exact polar_zero_right Q _
  · intro x y _ _ hx hy
    rw [polar_add_right, hx, hy, add_zero]
  · intro c x _ hx
    rw [polar_smul_right, hx, smul_zero]

theorem eichler_apply_f (he : ∀ i, Q (e i) = 0) (hee : ∀ i j, polar Q (e i) (e j) = 0)
    (hef : ∀ i j, polar Q (e i) (f j) = if i = j then 1 else 0) (i : Fin m)
    {u : Fin d → K} (hu : u ∈ rootParams Q e f a i.val) (j : Fin m) (hj : j.val ≤ i.val) :
    eichler Q (e i) u (f j) = if j = i then f i + u - Q u • e i else f j := by
  have hiu : polar Q (e i) u = 0 := polar_e_eq_zero_of_mem_rootParams hee hu i
  rw [eichler_apply (he i) hiu, polar_f_eq_zero_of_mem_rootParams hef hu j hj, polar_comm, hef]
  split_ifs with h1 h2 h2
  · subst h2
    simp
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · simp

theorem card_fin_gt (m i : ℕ) : Fintype.card {k : Fin m // i < k.val} = m - 1 - i := by
  rw [← Fintype.card_fin (m - 1 - i)]
  refine Fintype.card_congr
    { toFun := fun k => ⟨k.1.val - i - 1, by have := k.1.2; have := k.2; omega⟩
      invFun := fun j => ⟨⟨j.val + i + 1, by have := j.2; omega⟩, by simp⟩
      left_inv := fun k => by
        apply Subtype.ext; apply Fin.ext
        simp only
        have := k.2
        omega
      right_inv := fun j => by
        apply Fin.ext
        simp only
        omega }

theorem eq_zero_of_mem_span_of_polar_f
    (hef : ∀ i j, polar Q (e i) (f j) = if i = j then 1 else 0) {v : Fin d → K}
    (hv : v ∈ Submodule.span K (Set.range e)) (hvf : ∀ j, polar Q (f j) v = 0) : v = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hv
  have hc : ∀ j, c j = 0 := fun j => by
    have h := hvf j
    have h2 : polar Q (f j) (∑ k, c k • e k) = ∑ k, c k * polar Q (f j) (e k) := by
      rw [← polarBilin_apply_apply, map_sum]
      simp only [map_smul, smul_eq_mul, polarBilin_apply_apply]
    rw [h2] at h
    simp only [polar_comm Q (f j), hef, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true] at h
    exact h
  simp [hc]

theorem finrank_rootParams_ge (hind : LinearIndependent K e)
    (hef : ∀ i j, polar Q (e i) (f j) = if i = j then 1 else 0) (i : ℕ) :
    Module.finrank K (radicalKer Q e f a) + (m - 1 - i) ≤
      Module.finrank K (rootParams Q e f a i) := by
  set S := Submodule.span K (Set.range fun k : {k : Fin m // i < k.val} => e k) with hSdef
  have hS : Module.finrank K S = m - 1 - i := by
    have h := finrank_span_eq_card (hind.comp _ Subtype.val_injective :
      LinearIndependent K (e ∘ (Subtype.val : {k : Fin m // i < k.val} → Fin m)))
    rw [card_fin_gt] at h
    exact h
  have hSe : S ≤ Submodule.span K (Set.range e) :=
    Submodule.span_mono (Set.range_comp_subset_range _ _)
  have hdisj : radicalKer Q e f a ⊓ S = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot]
    exact eq_zero_of_mem_span_of_polar_f hef (hSe hv.2) (mem_radicalKer.mp hv.1).2.1
  have h := Submodule.finrank_sup_add_finrank_inf_eq (radicalKer Q e f a) S
  rw [hdisj, finrank_bot, add_zero] at h
  change _ ≤ Module.finrank K ↥(radicalKer Q e f a ⊔ S)
  omega

theorem finrank_radicalKer_ge_of_mem_span (ha : a ∈ Submodule.span K (Set.range e)) :
    d - 2 * m ≤ Module.finrank K (radicalKer Q e f a) := by
  set L := LinearMap.prod (LinearMap.pi fun i => polarBilin Q (e i))
    (LinearMap.pi fun j => polarBilin Q (f j))
  have h1 := LinearMap.finrank_range_add_finrank_ker L
  have h2 : Module.finrank K (LinearMap.range L) ≤ 2 * m := by
    refine (Submodule.finrank_le _).trans ?_
    simp only [Module.finrank_prod, Module.finrank_fin_fun]
    omega
  rw [Module.finrank_fin_fun] at h1
  have hle : LinearMap.ker L ≤ radicalKer Q e f a := by
    intro v hv
    have hv' : L v = 0 := hv
    simp only [L, LinearMap.prod_apply, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero, funext_iff,
      Pi.zero_apply] at hv'
    refine mem_radicalKer.mpr ⟨fun i => hv'.1 i, fun j => hv'.2 j, ?_⟩
    rw [polar_comm]
    have hspan : Submodule.span K (Set.range e) ≤ LinearMap.ker (polarBilin Q v) :=
      Submodule.span_le.mpr (by
        rintro _ ⟨i, rfl⟩
        change polarBilin Q v (e i) = 0
        rw [polarBilin_apply_apply, polar_comm]
        exact hv'.1 i)
    have := hspan ha
    rwa [LinearMap.mem_ker, polarBilin_apply_apply] at this
  have h3 := Submodule.finrank_mono hle
  omega

end Root

section Chain

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical
open CFSG.RankThree.OrthogonalInvolutions (fixSpace commSpace mem_fixSpace mem_commSpace
  fixSpace_eq_orthogonal_commSpace)

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {m : ℕ}
  {e f : Fin m → (Fin d → K)} {a : Fin d → K}

theorem polar_eq_zero_of_mem_span {v w : Fin d → K} (hv : ∀ i, polar Q (e i) v = 0)
    (hw : w ∈ Submodule.span K (Set.range e)) : polar Q w v = 0 := by
  have hle : Submodule.span K (Set.range e) ≤ LinearMap.ker (polarBilin Q v) :=
    Submodule.span_le.mpr (by
      rintro _ ⟨i, rfl⟩
      change polarBilin Q v (e i) = 0
      rw [polarBilin_apply_apply, polar_comm, hv i])
  have h := hle hw
  rw [LinearMap.mem_ker, polarBilin_apply_apply, polar_comm] at h
  exact h

theorem apply_eq_of_mem_radicalKer (hQ : (polarBilin Q).Nondegenerate)
    {t : (Fin d → K) ≃ₗ[K] (Fin d → K)}
    (ht : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (htt : t * t = 1)
    (hW : ∀ v, t v - v ∈ Submodule.span K (Set.range e) ⊔ K ∙ a) {v : Fin d → K}
    (hv : v ∈ radicalKer Q e f a) : t v = v := by
  obtain ⟨hve, -, hva⟩ := mem_radicalKer.mp hv
  have hmem : v ∈ fixSpace t := by
    rw [fixSpace_eq_orthogonal_commSpace hQ ht htt, LinearMap.BilinForm.mem_orthogonal_iff]
    intro x hx
    obtain ⟨u, rfl⟩ := mem_commSpace.mp hx
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp (hW u)
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
    change polarBilin Q (t u - u) v = 0
    rw [polarBilin_apply_apply, ← hyz, polar_add_left, polar_smul_left, hva, smul_zero, add_zero]
    exact polar_eq_zero_of_mem_span hve hy
  exact mem_fixSpace.mp hmem

theorem sum_range_add_sub (m c : ℕ) :
    ∑ i ∈ Finset.range m, (c + (m - 1 - i)) = m * c + m * (m - 1) / 2 := by
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
  congr 1
  have h1 := Finset.sum_range_reflect (fun i => i) m
  have h2 := Finset.sum_range_id_mul_two m
  omega

variable [Finite K] [CharP K 2]

theorem exists_twoSubgroup_centralizer_of_setup (hQ : (polarBilin Q).Nondegenerate)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    {s : GL (Fin d) K} (hs : s ∈ matrixIsometries Q) (hss : s * s = 1)
    (hind : LinearIndependent K e) (he : ∀ i, Q (e i) = 0)
    (hee : ∀ i j, polar Q (e i) (e j) = 0)
    (hef : ∀ i j, polar Q (e i) (f j) = if i = j then 1 else 0)
    (hfix : ∀ i, matrixLinearIso s (e i) = e i)
    (hW : ∀ v, matrixLinearIso s v - v ∈ Submodule.span K (Set.range e) ⊔ K ∙ a) :
    ∃ R : Subgroup (GL (Fin d) K), IsPGroup 2 R ∧
      R ≤ matrixDerived Q ⊓ Subgroup.centralizer {s} ∧
      R ≤ (flagRadical Q (Submodule.span K (Set.range e))).map (matrixDerived Q).subtype ∧
      Nat.card K ^ (m * Module.finrank K (radicalKer Q e f a) + m * (m - 1) / 2) ≤
        Nat.card R := by
  set t := matrixLinearIso s with htdef
  have ht : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q := hs
  have htt : t * t = 1 := by rw [htdef, ← map_mul, hss, map_one]
  set T := Submodule.span K (Set.range e) with hTdef
  have hT : ∀ x ∈ T, ∀ y ∈ T, polar Q x y = 0 := fun x hx y hy => by
    have h1 : ∀ i, polar Q (e i) y = 0 := fun i => by
      rw [polar_comm]
      exact polar_eq_zero_of_mem_span (fun j => hee j i) hy
    exact polar_eq_zero_of_mem_span h1 hx
  have hDfix : ∀ (i : ℕ) {u : Fin d → K}, u ∈ rootParams Q e f a i → t u = u := by
    intro i u hu
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hu
    have hz' : z ∈ fixSpace t := by
      refine (Submodule.span_le.mpr ?_) hz
      rintro _ ⟨k, rfl⟩
      exact mem_fixSpace.mpr (hfix k)
    rw [map_add, apply_eq_of_mem_radicalKer hQ ht htt hW hy, mem_fixSpace.mp hz']
  have hDorth : ∀ (i : ℕ) {u : Fin d → K}, u ∈ rootParams Q e f a i →
      u ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) T := by
    intro i u hu
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    rw [polarBilin_apply_apply]
    exact polar_eq_zero_of_mem_span (polar_e_eq_zero_of_mem_rootParams hee hu) hw
  set R : Subgroup (GL (Fin d) K) :=
    (flagRadical Q T).map (matrixDerived Q).subtype ⊓ Subgroup.centralizer {s} with hRdef
  have hR2 : IsPGroup 2 R := by
    intro g
    obtain ⟨⟨h, hh, hgh⟩, -⟩ := g.2
    refine ⟨2, Subtype.ext ?_⟩
    have h4 := pow_four_eq_one_of_mem hT hh
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← hgh]
    change ((matrixDerived Q).subtype h) ^ 4 = 1
    rw [← map_pow, h4, map_one]
  have hRle : R ≤ matrixDerived Q ⊓ Subgroup.centralizer {s} := by
    refine inf_le_inf_right _ ?_
    rintro _ ⟨h, -, rfl⟩
    exact h.2
  let φ : ∀ i : Fin m, Multiplicative (rootParams Q e f a i.val) →* GL (Fin d) K := fun i =>
    { toFun := fun u => matrixLinearIso.symm (eichler Q (e i)
        ((Multiplicative.toAdd u : rootParams Q e f a i.val) : Fin d → K))
      map_one' := by
        rw [toAdd_one, Submodule.coe_zero, eichler_zero_right, map_one]
      map_mul' := fun u v => by
        rw [← map_mul, eichler_mul
          (polar_e_eq_zero_of_mem_rootParams hee (Multiplicative.toAdd u).2 i)
          (polar_e_eq_zero_of_mem_rootParams hee (Multiplicative.toAdd v).2 i), toAdd_mul,
          Submodule.coe_add] }
  have hφapp : ∀ (i : Fin m) (u : rootParams Q e f a i.val),
      matrixLinearIso (φ i (Multiplicative.ofAdd u)) = eichler Q (e i) u := fun i u =>
    MulEquiv.apply_symm_apply _ _
  have hφR : ∀ (i : Fin m) (u : rootParams Q e f a i.val), φ i (Multiplicative.ofAdd u) ∈ R := by
    intro i u
    obtain ⟨g, hg, hgv⟩ := eichler_mem_flagRadical hE hT (Submodule.subset_span ⟨i, rfl⟩) (he i)
      (hDorth i.val u.2)
    have hgval : g.val = φ i (Multiplicative.ofAdd u) := by
      apply matrixLinearIso.injective
      rw [hφapp]
      exact LinearEquiv.ext hgv
    refine ⟨⟨g, hg, hgval⟩, ?_⟩
    show _ ∈ Subgroup.centralizer {s}
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply matrixLinearIso.injective
    rw [map_mul, map_mul, hφapp]
    exact (eichler_commute_of_apply_eq ht (hfix i) (hDfix i.val u.2)).symm
  have hφfix : ∀ (i : Fin m) (u : rootParams Q e f a i.val) (j : Fin m), j.val < i.val →
      matrixLinearIso (φ i (Multiplicative.ofAdd u)) (f j) = f j := by
    intro i u j hj
    rw [hφapp, eichler_apply_f he hee hef i u.2 j hj.le, ite_eq_right (fun h => by
      rw [h] at hj; exact lt_irrefl _ hj)]
  have hφfi : ∀ (i : Fin m) (u : rootParams Q e f a i.val),
      matrixLinearIso (φ i (Multiplicative.ofAdd u)) (f i) = f i → u = 0 := by
    intro i u h
    rw [hφapp, eichler_apply_f he hee hef i u.2 i le_rfl, ite_eq_left rfl] at h
    have h1 : (u : Fin d → K) = Q u • e i := by
      have h2 : (u : Fin d → K) - Q u • e i = (f i + u - Q u • e i) - f i := by abel
      rw [h, sub_self] at h2
      exact sub_eq_zero.mp h2
    have h2 := polar_f_eq_zero_of_mem_rootParams hef u.2 i le_rfl
    rw [h1, polar_smul_right, polar_comm, hef, ite_eq_left rfl, smul_eq_mul, mul_one] at h2
    apply Subtype.ext
    rw [h1, h2, zero_smul, Submodule.coe_zero]
  have hφinj : ∀ i : Fin m, Function.Injective (φ i) := by
    intro i
    rw [injective_iff_map_eq_one]
    intro u hu
    have h := hφfi i (Multiplicative.toAdd u) (by
      change matrixLinearIso (φ i u) (f i) = f i
      rw [hu, map_one]
      rfl)
    exact toAdd_eq_zero.mp h
  set Rch : ℕ → Subgroup (GL (Fin d) K) := fun i => R ⊓ fixFamily f i with hRch
  set A : ℕ → Subgroup (GL (Fin d) K) := fun i =>
    if h : i < m then (φ ⟨i, h⟩).range else ⊥ with hAdef
  have hRmono : ∀ i, Rch (i + 1) ≤ Rch i := fun i => inf_le_inf_left _ (fixFamily_antitone f i)
  have hAle : ∀ i < m, A i ≤ Rch i := by
    intro i hi
    simp only [hAdef, hi, dite_true]
    rintro _ ⟨u, rfl⟩
    exact ⟨hφR ⟨i, hi⟩ (Multiplicative.toAdd u),
      fun j hj => hφfix ⟨i, hi⟩ (Multiplicative.toAdd u) j hj⟩
  have hAR : ∀ i < m, A i ⊓ Rch (i + 1) = ⊥ := by
    intro i hi
    rw [eq_bot_iff]
    rintro g ⟨hgA, -, hgfix⟩
    simp only [hAdef, hi, dite_true] at hgA
    obtain ⟨u, rfl⟩ := hgA
    have h := hφfi ⟨i, hi⟩ (Multiplicative.toAdd u)
      (hgfix ⟨i, hi⟩ (by simp))
    rw [Subgroup.mem_bot, toAdd_eq_zero.mp h, map_one]
  have hchain := prod_card_le_card_of_chain Rch A hRmono m hAle hAR
  have hcardA : ∀ i < m, Nat.card K ^ (Module.finrank K (radicalKer Q e f a) + (m - 1 - i)) ≤
      Nat.card (A i) := by
    intro i hi
    simp only [hAdef, hi, dite_true]
    rw [← Nat.card_congr (MonoidHom.ofInjective (hφinj ⟨i, hi⟩)).toEquiv,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (rootParams Q e f a i) ≃ _),
      Module.natCard_eq_pow_finrank (K := K) (V := rootParams Q e f a i)]
    exact Nat.pow_le_pow_right Nat.card_pos (finrank_rootParams_ge hind hef i)
  refine ⟨R, hR2, hRle, inf_le_left, ?_⟩
  have hprod : Nat.card K ^ (m * Module.finrank K (radicalKer Q e f a) + m * (m - 1) / 2) ≤
      ∏ i ∈ Finset.range m, Nat.card (A i) := by
    rw [← sum_range_add_sub, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod fun i hi => hcardA i (Finset.mem_range.mp hi)
  have hR0 : Nat.card (Rch 0) ≤ Nat.card R := Subgroup.card_le_of_le inf_le_left
  have hRm : 0 < Nat.card (Rch m) := Nat.card_pos
  calc _ ≤ ∏ i ∈ Finset.range m, Nat.card (A i) := hprod
    _ ≤ (∏ i ∈ Finset.range m, Nat.card (A i)) * Nat.card (Rch m) :=
        Nat.le_mul_of_pos_right _ hRm
    _ ≤ Nat.card (Rch 0) := hchain
    _ ≤ Nat.card R := hR0

end Chain

end CFSG.SeitzReduction.OmegaPilot
