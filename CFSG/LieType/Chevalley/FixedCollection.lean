module

public import CFSG.LieType.Chevalley.Refined
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.RootSystem

variable {τ : Tag}

section Weyl

theorem length_simple_mul_eq_add_one_iff (w : WeylGroup τ) (i : Fin τ.rank) :
    (coxeterSystem τ).length (simple τ i * w) = (coxeterSystem τ).length w + 1 ↔
      0 < height (w⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ)) := by
  rw [← (coxeterSystem τ).not_isLeftDescent_iff, ← (coxeterSystem τ).isRightDescent_inv_iff,
    ← nonneg_iff_not_isRightDescent, IsRoot.height_pos_iff (IsRoot.smul (isRoot_single τ i) w⁻¹)]
  rfl

theorem height_simple_mul_smul_neg {w : WeylGroup τ} {i : Fin τ.rank}
    (h : (coxeterSystem τ).length (simple τ i * w) = (coxeterSystem τ).length w + 1)
    {α : Root τ} (hα : 0 < height α.1) (hw : height (w • α).1 < 0) :
    height ((simple τ i * w) • α).1 < 0 := by
  have hpos := (length_simple_mul_eq_add_one_iff w i).1 h
  have hne : -(w • α) ≠ simpleRoot τ i := by
    intro he
    have e : α = -(w⁻¹ • simpleRoot τ i) := by
      rw [← smul_neg_root, ← he, neg_neg, inv_smul_smul]
    rw [e, coe_neg_root, height_neg, coe_smul_root] at hα
    change 0 < -height (w⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ)) at hα
    omega
  have h1 : 0 < height (-(w • α)).1 := by
    rw [coe_neg_root, height_neg]
    omega
  have h2 := (rootCombinatorics τ).pos_refl i _ h1 hne
  change 0 < height (simple τ i • -(w • α)).1 at h2
  rw [smul_neg_root, coe_neg_root, height_neg] at h2
  rw [mul_smul]
  omega

theorem height_wordProd_append_smul_neg {ω ω' : List (Fin τ.rank)}
    (hred : (coxeterSystem τ).IsReduced (ω ++ ω')) {α : Root τ} (hα : 0 < height α.1)
    (h : height ((coxeterSystem τ).wordProd ω' • α).1 < 0) :
    height ((coxeterSystem τ).wordProd (ω ++ ω') • α).1 < 0 := by
  induction ω with
  | nil => simpa using h
  | cons i ω ih =>
    have hred' : (coxeterSystem τ).IsReduced (ω ++ ω') := by
      simpa using hred.drop 1
    have hlen : (coxeterSystem τ).length (simple τ i * (coxeterSystem τ).wordProd (ω ++ ω')) =
        (coxeterSystem τ).length ((coxeterSystem τ).wordProd (ω ++ ω')) + 1 := by
      have e := hred.eq
      rw [List.cons_append, CoxeterSystem.wordProd_cons, List.length_cons] at e
      rw [e, hred'.eq]
    rw [List.cons_append, CoxeterSystem.wordProd_cons]
    exact height_simple_mul_smul_neg hlen hα (ih hred')

theorem isReduced_append_of_length_mul {ω ω' : List (Fin τ.rank)}
    (hω : (coxeterSystem τ).IsReduced ω) (hω' : (coxeterSystem τ).IsReduced ω')
    (hlen : (coxeterSystem τ).length
        ((coxeterSystem τ).wordProd ω * (coxeterSystem τ).wordProd ω') =
      (coxeterSystem τ).length ((coxeterSystem τ).wordProd ω) +
        (coxeterSystem τ).length ((coxeterSystem τ).wordProd ω')) :
    (coxeterSystem τ).IsReduced (ω ++ ω') := by
  rw [CoxeterSystem.IsReduced, CoxeterSystem.wordProd_append, hlen, hω.eq, hω'.eq,
    List.length_append]

theorem isReduced_left_right_of_append {ω ω' : List (Fin τ.rank)}
    (hred : (coxeterSystem τ).IsReduced (ω ++ ω')) :
    (coxeterSystem τ).IsReduced ω ∧ (coxeterSystem τ).IsReduced ω' :=
  ⟨by simpa using hred.take ω.length, by simpa using hred.drop ω.length⟩

theorem length_mul_of_isReduced_append {ω ω' : List (Fin τ.rank)}
    (hred : (coxeterSystem τ).IsReduced (ω ++ ω')) :
    (coxeterSystem τ).length ((coxeterSystem τ).wordProd ω * (coxeterSystem τ).wordProd ω') =
      (coxeterSystem τ).length ((coxeterSystem τ).wordProd ω) +
        (coxeterSystem τ).length ((coxeterSystem τ).wordProd ω') := by
  obtain ⟨h1, h2⟩ := isReduced_left_right_of_append hred
  rw [← CoxeterSystem.wordProd_append, hred.eq, h1.eq, h2.eq, List.length_append]

theorem height_mul_smul_neg {v v' : WeylGroup τ}
    (hlen : (coxeterSystem τ).length (v * v') =
      (coxeterSystem τ).length v + (coxeterSystem τ).length v')
    {α : Root τ} (hα : 0 < height α.1) (h : height (v' • α).1 < 0) :
    height ((v * v') • α).1 < 0 := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem τ).exists_isReduced v
  obtain ⟨ω', hω', rfl⟩ := (coxeterSystem τ).exists_isReduced v'
  have := height_wordProd_append_smul_neg (isReduced_append_of_length_mul hω hω' hlen) hα h
  rwa [CoxeterSystem.wordProd_append] at this

theorem map_wordProd_flatten (δ : WeylGroup τ ≃* WeylGroup τ) {L : List (List (Fin τ.rank))}
    (h : ∀ ω ∈ L, δ ((coxeterSystem τ).wordProd ω) = (coxeterSystem τ).wordProd ω) :
    δ ((coxeterSystem τ).wordProd L.flatten) = (coxeterSystem τ).wordProd L.flatten := by
  induction L with
  | nil => simp
  | cons ω L ih =>
    rw [List.flatten_cons, CoxeterSystem.wordProd_append, map_mul, h ω List.mem_cons_self,
      ih fun ω' hω' => h ω' (List.mem_cons_of_mem _ hω')]

end Weyl

section Reduced

variable (τ) in
@[expose] def reflectWord (ω : List (Fin τ.rank)) (v : Fin τ.rank → ℤ) : Fin τ.rank → ℤ :=
  ω.foldl (fun v j => reflect τ j v) v

theorem reflectWord_eq (ω : List (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    reflectWord τ ω v = ((coxeterSystem τ).wordProd ω)⁻¹ • v := by
  induction ω generalizing v with
  | nil => simp [reflectWord]
  | cons j ω ih =>
    rw [reflectWord, List.foldl_cons, ← reflectWord, ih, CoxeterSystem.wordProd_cons, mul_inv_rev,
      CoxeterSystem.inv_simple, mul_smul, simple_smul]

theorem isReduced_cons_iff (i : Fin τ.rank) (ω : List (Fin τ.rank)) :
    (coxeterSystem τ).IsReduced (i :: ω) ↔ (coxeterSystem τ).IsReduced ω ∧
      0 < height (((coxeterSystem τ).wordProd ω)⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ)) := by
  rw [← length_simple_mul_eq_add_one_iff]
  constructor
  · intro h
    have hω : (coxeterSystem τ).IsReduced ω := by simpa using h.drop 1
    refine ⟨hω, ?_⟩
    have e := h.eq
    rw [CoxeterSystem.wordProd_cons, List.length_cons] at e
    rw [e, hω.eq]
  · rintro ⟨hω, h⟩
    rw [CoxeterSystem.IsReduced, CoxeterSystem.wordProd_cons, h, hω.eq, List.length_cons]

variable (τ) in
@[expose] def reducedCheck : List (Fin τ.rank) → Bool
  | [] => true
  | i :: ω => decide (0 < height (reflectWord τ ω (Pi.single i 1))) && reducedCheck ω

theorem reducedCheck_iff (ω : List (Fin τ.rank)) :
    reducedCheck τ ω = true ↔ (coxeterSystem τ).IsReduced ω := by
  induction ω with
  | nil => simp [reducedCheck, CoxeterSystem.IsReduced]
  | cons i ω ih =>
    rw [reducedCheck, Bool.and_eq_true, decide_eq_true_iff, ih, isReduced_cons_iff, reflectWord_eq,
      and_comm]

theorem isReduced_of_reducedCheck {ω : List (Fin τ.rank)} (h : reducedCheck τ ω = true) :
    (coxeterSystem τ).IsReduced ω :=
  (reducedCheck_iff ω).1 h

theorem isReduced_G2_alternating :
    (coxeterSystem .G2).IsReduced ([0, 1, 0, 1, 0, 1] : List (Fin 2)) :=
  isReduced_of_reducedCheck (by decide +kernel)

theorem not_isReduced_G2_square : ¬(coxeterSystem .G2).IsReduced ([0, 0] : List (Fin 2)) :=
  fun h => absurd ((reducedCheck_iff _).2 h) (by decide +kernel)

end Reduced

section AllNegative

open RootWalk

variable (τ) in
@[expose] def walkPos (ω : List (Fin τ.rank)) (k : ℕ) : ℕ :=
  ω.foldr (fun i k => τ.rootCertificate.image k i) k

theorem walkPos_spec (ω : List (Fin τ.rank)) {k : ℕ} (hk : k < τ.rootCertificate.roots.length) :
    walkPos τ ω k < τ.rootCertificate.roots.length ∧
      τ.rootCertificate.root (walkPos τ ω k) =
        (coxeterSystem τ).wordProd ω • τ.rootCertificate.root k := by
  induction ω with
  | nil => simpa [walkPos] using hk
  | cons i ω ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨rootCertificate_image_lt h1 i, ?_⟩
    change τ.rootCertificate.root (τ.rootCertificate.image (walkPos τ ω k) i) = _
    rw [rootCertificate_root_image h1, h2, CoxeterSystem.wordProd_cons, mul_smul, simple_smul]

variable (τ) in
@[expose] def negCheck (ω : List (Fin τ.rank)) : Bool :=
  (List.range τ.rootCertificate.roots.length).all fun k =>
    decide (height (τ.rootCertificate.root k) < 0) ||
      decide (height (τ.rootCertificate.root (walkPos τ ω k)) < 0)

theorem height_wordProd_smul_neg_of_negCheck {ω : List (Fin τ.rank)} (h : negCheck τ ω = true)
    (α : Root τ) (hα : 0 < height α.1) : height ((coxeterSystem τ).wordProd ω • α).1 < 0 := by
  obtain ⟨k, hk, hkα⟩ := RootCertificate.exists_root_eq τ.rootCertificate_check α.2
  simp only [negCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h k hk with h' | h'
  · rw [hkα] at h'
    omega
  · rwa [(walkPos_spec ω hk).2, hkα] at h'

theorem negCheck_G2_alternating : negCheck .G2 ([0, 1, 0, 1, 0, 1] : List (Fin 2)) = true := by
  decide +kernel

end AllNegative

section Subgroups

variable {K : Type} [Field K]

variable (K) in
theorem nrep_mul_of_isReduced_append {ω ω' : List (Fin τ.rank)}
    (hred : (coxeterSystem τ).IsReduced (ω ++ ω')) :
    nrep τ K ((coxeterSystem τ).wordProd ω * (coxeterSystem τ).wordProd ω') =
      nrep τ K ((coxeterSystem τ).wordProd ω) * nrep τ K ((coxeterSystem τ).wordProd ω') := by
  obtain ⟨h1, h2⟩ := isReduced_left_right_of_append hred
  rw [← CoxeterSystem.wordProd_append, nrep_eq_prod τ K hred, nrep_eq_prod τ K h1,
    nrep_eq_prod τ K h2, List.map_append, List.prod_append]

variable (K) in
theorem nrep_mul {v v' : WeylGroup τ}
    (hlen : (coxeterSystem τ).length (v * v') =
      (coxeterSystem τ).length v + (coxeterSystem τ).length v') :
    nrep τ K (v * v') = nrep τ K v * nrep τ K v' := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem τ).exists_isReduced v
  obtain ⟨ω', hω', rfl⟩ := (coxeterSystem τ).exists_isReduced v'
  exact nrep_mul_of_isReduced_append K (isReduced_append_of_length_mul hω hω' hlen)

variable (τ K) in
theorem Uminus_one : Uminus τ K 1 = ⊥ := by
  refine le_bot_iff.mp (iSup₂_le fun α hα => ?_)
  rw [one_smul] at hα
  omega

theorem Uminus_le_Uminus_mul {v v' : WeylGroup τ}
    (hlen : (coxeterSystem τ).length (v * v') =
      (coxeterSystem τ).length v + (coxeterSystem τ).length v') :
    Uminus τ K v' ≤ Uminus τ K (v * v') :=
  biSup_mono fun _ hα => ⟨hα.1, height_mul_smul_neg hlen hα.1 hα.2⟩

variable [Finite K]

variable (τ K) in
theorem Uminus_le_U (w : WeylGroup τ) : Uminus τ K w ≤ (nativeData τ K).U :=
  biSup_mono fun _ hα => hα.1

theorem Uminus_eq_U_of_forall {w : WeylGroup τ}
    (h : ∀ α : Root τ, 0 < height α.1 → height (w • α).1 < 0) :
    Uminus τ K w = (nativeData τ K).U :=
  le_antisymm (Uminus_le_U τ K w) (biSup_mono fun α hα => ⟨hα, h α hα⟩)

theorem Uminus_eq_U_of_negCheck {ω : List (Fin τ.rank)} (h : negCheck τ ω = true) :
    Uminus τ K ((coxeterSystem τ).wordProd ω) = (nativeData τ K).U :=
  Uminus_eq_U_of_forall (height_wordProd_smul_neg_of_negCheck h)

private theorem eq_one_of_conj_mem_B_inf_Uneg {g x : adjointGroup τ K}
    (h : g * x * g⁻¹ ∈ (nativeData τ K).B ⊓ Uneg τ K) : x = 1 := by
  rw [nativeData_B_inf_Uneg, Subgroup.mem_bot] at h
  have := congrArg (fun y => g⁻¹ * y * g) h
  simpa [mul_assoc] using this

theorem exists_mem_Uminus_mul_conj_mem_Uminus {v v' : WeylGroup τ}
    (hlen : (coxeterSystem τ).length (v * v') =
      (coxeterSystem τ).length v + (coxeterSystem τ).length v')
    {u : adjointGroup τ K} (hu : u ∈ Uminus τ K (v * v')) :
    ∃ z ∈ Uminus τ K v', ∃ y ∈ Uplus τ K v',
      nrep τ K v' * y * (nrep τ K v')⁻¹ ∈ Uminus τ K v ∧ u = z * y := by
  obtain ⟨p, hp, q, hq, hpq⟩ := exists_mem_Uplus_mem_Uminus v' (inv_mem (Uminus_le_U τ K _ hu))
  have hu' : u = q⁻¹ * p⁻¹ := by rw [← mul_inv_rev, ← hpq, inv_inv]
  have hneg : nrep τ K v * (nrep τ K v' * p⁻¹ * (nrep τ K v')⁻¹) * (nrep τ K v)⁻¹ ∈ Uneg τ K := by
    have e : nrep τ K v * (nrep τ K v' * p⁻¹ * (nrep τ K v')⁻¹) * (nrep τ K v)⁻¹ =
        nrep τ K (v * v') * (q * u) * (nrep τ K (v * v'))⁻¹ := by
      rw [nrep_mul K hlen, hu']
      group
    rw [e]
    exact nrep_conj_mem_Uneg (mul_mem (Uminus_le_Uminus_mul hlen hq) hu)
  obtain ⟨a, ha, b, hb, hab⟩ := exists_mem_Uplus_mem_Uminus v (nrep_conj_mem_U (inv_mem hp))
  have ha1 : a = 1 := by
    refine eq_one_of_conj_mem_B_inf_Uneg (g := nrep τ K v)
      (Subgroup.mem_inf.mpr ⟨(nativeData τ K).U_le_B (nrep_conj_mem_U ha), ?_⟩)
    have e : nrep τ K v * a * (nrep τ K v)⁻¹ =
        (nrep τ K v * (nrep τ K v' * p⁻¹ * (nrep τ K v')⁻¹) * (nrep τ K v)⁻¹) *
          (nrep τ K v * b * (nrep τ K v)⁻¹)⁻¹ := by
      rw [hab]
      group
    rw [e]
    exact mul_mem hneg (inv_mem (nrep_conj_mem_Uneg hb))
  refine ⟨q⁻¹, inv_mem hq, p⁻¹, inv_mem hp, ?_, hu'⟩
  rw [hab, ha1, one_mul]
  exact hb

theorem eq_of_mul_eq_of_mem_Uminus {v' : WeylGroup τ} {z z₁ y y₁ : adjointGroup τ K}
    (hz : z ∈ Uminus τ K v') (hz₁ : z₁ ∈ Uminus τ K v')
    (hy : nrep τ K v' * y * (nrep τ K v')⁻¹ ∈ (nativeData τ K).U)
    (hy₁ : nrep τ K v' * y₁ * (nrep τ K v')⁻¹ ∈ (nativeData τ K).U)
    (h : z * y = z₁ * y₁) : z = z₁ ∧ y = y₁ := by
  have h1 : z₁⁻¹ * z = 1 := by
    refine eq_one_of_conj_mem_B_inf_Uneg (g := nrep τ K v')
      (Subgroup.mem_inf.mpr ⟨?_, nrep_conj_mem_Uneg (mul_mem (inv_mem hz₁) hz)⟩)
    have e : nrep τ K v' * (z₁⁻¹ * z) * (nrep τ K v')⁻¹ =
        (nrep τ K v' * y₁ * (nrep τ K v')⁻¹) * (nrep τ K v' * y * (nrep τ K v')⁻¹)⁻¹ := by
      have e' : z₁⁻¹ * z = y₁ * y⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h]
        group
      rw [e']
      group
    rw [e]
    exact (nativeData τ K).U_le_B (mul_mem hy₁ (inv_mem hy))
  rw [inv_mul_eq_one] at h1
  subst h1
  exact ⟨rfl, mul_left_cancel h⟩

theorem existsUnique_Uminus_mul {v v' : WeylGroup τ}
    (hlen : (coxeterSystem τ).length (v * v') =
      (coxeterSystem τ).length v + (coxeterSystem τ).length v')
    {u : adjointGroup τ K} (hu : u ∈ Uminus τ K (v * v')) :
    ∃! p : adjointGroup τ K × adjointGroup τ K, p.1 ∈ Uminus τ K v' ∧
      nrep τ K v' * p.2 * (nrep τ K v')⁻¹ ∈ Uminus τ K v ∧ u = p.1 * p.2 := by
  obtain ⟨z, hz, y, -, hy, rfl⟩ := exists_mem_Uminus_mul_conj_mem_Uminus hlen hu
  refine ⟨(z, y), ⟨hz, hy, rfl⟩, fun p hp => ?_⟩
  obtain ⟨h1, h2⟩ := eq_of_mul_eq_of_mem_Uminus hp.1 hz (Uminus_le_U τ K _ hp.2.1)
    (Uminus_le_U τ K _ hy) hp.2.2.symm
  exact Prod.ext h1 h2

theorem fixed_mem_of_reduced_blocks (F : adjointGroup τ K ≃* adjointGroup τ K)
    (δ : WeylGroup τ ≃* WeylGroup τ)
    (hFU0 : ∀ u ∈ (nativeData τ K).U, F u ∈ (nativeData τ K).U)
    (hFU : ∀ w, ∀ u ∈ Uminus τ K w, F u ∈ Uminus τ K (δ w))
    (hFn : ∀ w, δ w = w → F (nrep τ K w) = nrep τ K w)
    (L : List (List (Fin τ.rank)))
    (hδL : ∀ ω ∈ L, δ ((coxeterSystem τ).wordProd ω) = (coxeterSystem τ).wordProd ω)
    (hred : (coxeterSystem τ).IsReduced L.flatten) (Q : Subgroup (adjointGroup τ K))
    (hQ : ∀ g, F g = g → ∀ x ∈ Q, g * x * g⁻¹ ∈ Q)
    (hQL : ∀ ω ∈ L, ∀ y ∈ Uminus τ K ((coxeterSystem τ).wordProd ω), F y = y → y ∈ Q) :
    ∀ u ∈ Uminus τ K ((coxeterSystem τ).wordProd L.flatten), F u = u → u ∈ Q := by
  induction L with
  | nil =>
    intro u hu _
    rw [List.flatten_nil, CoxeterSystem.wordProd_nil, Uminus_one, Subgroup.mem_bot] at hu
    rw [hu]
    exact one_mem Q
  | cons ω L ih =>
    intro u hu hFu
    rw [List.flatten_cons] at hred hu
    have hlen := length_mul_of_isReduced_append hred
    rw [CoxeterSystem.wordProd_append] at hu
    obtain ⟨z, hz, y, hy, hy', rfl⟩ := exists_mem_Uminus_mul_conj_mem_Uminus hlen hu
    have hδ' := map_wordProd_flatten δ fun ω' hω' => hδL ω' (List.mem_cons_of_mem _ hω')
    have hFn' := hFn _ hδ'
    have hFz : F z ∈ Uminus τ K ((coxeterSystem τ).wordProd L.flatten) := by
      have := hFU _ z hz
      rwa [hδ'] at this
    have hconj : ∀ x, F (nrep τ K ((coxeterSystem τ).wordProd L.flatten) * x *
        (nrep τ K ((coxeterSystem τ).wordProd L.flatten))⁻¹) =
        nrep τ K ((coxeterSystem τ).wordProd L.flatten) * F x *
          (nrep τ K ((coxeterSystem τ).wordProd L.flatten))⁻¹ := fun x => by
      rw [map_mul, map_mul, map_inv, hFn']
    have hFy : nrep τ K ((coxeterSystem τ).wordProd L.flatten) * F y *
        (nrep τ K ((coxeterSystem τ).wordProd L.flatten))⁻¹ ∈ (nativeData τ K).U := by
      rw [← hconj]
      exact hFU0 _ (nrep_conj_mem_U hy)
    obtain ⟨hz1, hy1⟩ := eq_of_mul_eq_of_mem_Uminus hFz hz hFy (nrep_conj_mem_U hy)
      (by rw [← map_mul, hFu])
    have hzQ : z ∈ Q :=
      ih (fun ω' hω' => hδL ω' (List.mem_cons_of_mem _ hω'))
        (isReduced_left_right_of_append hred).2
        (fun ω' hω' => hQL ω' (List.mem_cons_of_mem _ hω')) z hz hz1
    have hy'Q := hQL ω List.mem_cons_self _ hy' (by rw [hconj, hy1])
    have hyQ : y ∈ Q := by
      have := hQ _ (by rw [map_inv, hFn']) _ hy'Q
      simpa [mul_assoc] using this
    exact mul_mem hzQ hyQ

theorem fixed_mem_U_of_reduced_blocks (F : adjointGroup τ K ≃* adjointGroup τ K)
    (δ : WeylGroup τ ≃* WeylGroup τ)
    (hFU0 : ∀ u ∈ (nativeData τ K).U, F u ∈ (nativeData τ K).U)
    (hFU : ∀ w, ∀ u ∈ Uminus τ K w, F u ∈ Uminus τ K (δ w))
    (hFn : ∀ w, δ w = w → F (nrep τ K w) = nrep τ K w)
    (L : List (List (Fin τ.rank)))
    (hδL : ∀ ω ∈ L, δ ((coxeterSystem τ).wordProd ω) = (coxeterSystem τ).wordProd ω)
    (hred : (coxeterSystem τ).IsReduced L.flatten)
    (hneg : ∀ α : Root τ, 0 < height α.1 →
      height ((coxeterSystem τ).wordProd L.flatten • α).1 < 0)
    (Q : Subgroup (adjointGroup τ K)) (hQ : ∀ g, F g = g → ∀ x ∈ Q, g * x * g⁻¹ ∈ Q)
    (hQL : ∀ ω ∈ L, ∀ y ∈ Uminus τ K ((coxeterSystem τ).wordProd ω), F y = y → y ∈ Q) :
    ∀ u ∈ (nativeData τ K).U, F u = u → u ∈ Q := by
  rw [← Uminus_eq_U_of_forall hneg]
  exact fixed_mem_of_reduced_blocks F δ hFU0 hFU hFn L hδL hred Q hQ hQL

end Subgroups

end CFSG.LieType.Chevalley
