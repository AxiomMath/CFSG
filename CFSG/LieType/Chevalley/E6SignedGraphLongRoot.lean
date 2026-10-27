module

public import CFSG.LieType.Chevalley.E6SignedGraphFixed
public import CFSG.LieType.Chevalley.E6SignedGraphRoots

public noncomputable section

namespace CFSG.LieType.Chevalley.E6SignedGraph

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement

variable (K : Type) [Field K]

@[expose] def longY
    (c : K) : ModGL TwistTag.E6.tag K :=
  weylElt TwistTag.E6.tag K ⟨3, by decide⟩ 1 *
      (xUnit TwistTag.E6.tag K ⟨2, by decide⟩ c * xUnit TwistTag.E6.tag K ⟨4, by decide⟩ c) *
    (weylElt TwistTag.E6.tag K ⟨3, by decide⟩ 1)⁻¹

@[expose] def longZ
    (d : K) : ModGL TwistTag.E6.tag K :=
  yUnit TwistTag.E6.tag K ⟨2, by decide⟩ d * yUnit TwistTag.E6.tag K ⟨4, by decide⟩ d

theorem weylElt_conj_pinnedX_int
    {τ : Tag} (i : Fin τ.rank) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ (R : Type) [CommRing R] (c : R),
      weylElt τ R i 1 * pinnedX τ R α c * (weylElt τ R i 1)⁻¹ =
        pinnedX τ R (reflect τ i α) ((ε : R) * c) := by
  set F := rootOperatorFamily τ
  have hα' : IsRoot τ (reflect τ i α) := IsRoot.reflect i hα
  refine ⟨F.pinnedFamilySign (reflect τ i α) * F.sign i ⟨α, hα⟩ * F.pinnedFamilySign α, ?_,
    fun R _ c => ?_⟩
  · rcases F.pinnedFamilySign_eq (reflect τ i α) with h1 | h1 <;>
      rcases F.sign_eq i ⟨α, hα⟩ with h2 | h2 <;>
      rcases F.pinnedFamilySign_eq α with h3 | h3 <;> simp [h1, h2, h3]
  · have hsm : simple τ i • (⟨α, hα⟩ : Root τ) = ⟨reflect τ i α, hα'⟩ :=
      Subtype.ext (simple_smul i α)
    rw [F.pinnedX_eq_eltUnit R hα, F.weylElt_mul_eltUnit_mul_inv, F.pinnedX_eq_eltUnit R hα', hsm]
    congr 1
    have h2 := F.pinnedFamilySign_mul_self R (reflect τ i α)
    push_cast
    linear_combination (-((F.sign i ⟨α, hα⟩ : R) * (F.pinnedFamilySign α : R) * c)) * h2

theorem commutatorElement_mul_mul_of_commute {G : Type*} [Group G] {a b y z u v : G}
    (hu : ⁅a, y⁆ = u) (hv : ⁅b, z⁆ = v) (hby : b * y = y * b) (haz : a * z = z * a)
    (hva : v * a = a * v) (hvy : v * y = y * v) : ⁅a * b, y * z⁆ = u * v := by
  have hay : a * y = u * y * a := by rw [← hu, commutatorElement_def]; group
  have hbz : b * z = v * z * b := by rw [← hv, commutatorElement_def]; group
  have key : a * b * (y * z) = u * v * (y * z) * (a * b) :=
    calc a * b * (y * z) = a * (b * y) * z := by group
      _ = a * y * (b * z) := by rw [hby]; group
      _ = u * y * (a * v) * z * b := by rw [hay, hbz]; group
      _ = u * (y * v) * (a * z) * b := by rw [← hva]; group
      _ = u * v * (y * z) * (a * b) := by rw [← hvy, haz]; group
  rw [commutatorElement_def, key]
  group

theorem not_isRoot_of_check
    {v : E6Vec} (h : ∀ k < cert.roots.length, cert.root k ≠ v) :
    ¬IsRoot TwistTag.E6.tag v := fun hv => by
  obtain ⟨k, hk, e⟩ := isRoot_iff_cert.1 hv
  exact h k hk e

theorem simplyLaced_E6 :
    TwistTag.E6.tag = .D4 ∨ TwistTag.E6.tag = .E6 ∨ TwistTag.E6.tag = .E7 ∨ TwistTag.E6.tag = .E8 :=
  Or.inr (Or.inl rfl)

variable {K}

theorem commute_pinnedX_of_not_isRoot
    {α β : E6Vec} (hα : IsRoot TwistTag.E6.tag α)
    (hβ : IsRoot TwistTag.E6.tag β) (hne : α ≠ β) (hne' : α ≠ -β)
    (h : ¬IsRoot TwistTag.E6.tag (α + β)) (c d : K) :
    pinnedX TwistTag.E6.tag K α c * pinnedX TwistTag.E6.tag K β d =
      pinnedX TwistTag.E6.tag K β d * pinnedX TwistTag.E6.tag K α c :=
  (simply_laced_root_commutator_unit TwistTag.E6.tag simplyLaced_E6 hα hβ hne hne').2 h K _
    (Subgroup.subset_closure ⟨c, rfl⟩) _ (Subgroup.subset_closure ⟨d, rfl⟩)

theorem conj_commutatorElement {G : Type*} [Group G] (p g h : G) :
    p * ⁅g, h⁆ * p⁻¹ = ⁅p * g * p⁻¹, p * h * p⁻¹⁆ := by
  simp only [commutatorElement_def]
  group

theorem conj_eq_of_mul_eq {G : Type*} [Group G] {p g h : G} (e : g * h = h * g) :
    p * g * p⁻¹ * (p * h * p⁻¹) = p * h * p⁻¹ * (p * g * p⁻¹) := by
  calc p * g * p⁻¹ * (p * h * p⁻¹) = p * (g * h) * p⁻¹ := by group
    _ = p * (h * g) * p⁻¹ := by rw [e]
    _ = p * h * p⁻¹ * (p * g * p⁻¹) := by group

end CFSG.LieType.Chevalley.E6SignedGraph

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley E6SignedGraph
open scoped commutatorElement

theorem E6_signed_graph_long_root_two_commutator :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ (K : Type) [Field K],
      (∀ c : K, longY K c * twistA K = twistA K * longY K c) ∧
      (∀ d : K, longZ K d * twistA K = twistA K * longZ K d) ∧
      (∀ c : K, xUnit TwistTag.E6.tag K ⟨3, by decide⟩ c * twistA K =
        twistA K * xUnit TwistTag.E6.tag K ⟨3, by decide⟩ c) ∧
      (∀ c d : K, ⁅longY K c, longZ K d⁆ =
        xUnit TwistTag.E6.tag K ⟨3, by decide⟩ (2 * ε * c * d)) ∧
      (ringChar K ≠ 2 → ∀ t : K, ∃ g ∈ fixedGroup K, ∃ h ∈ fixedGroup K,
        ⁅g, h⁆ = xUnit TwistTag.E6.tag K ⟨3, by decide⟩ t) := by
  set e2 : E6Vec := Pi.single ⟨2, by decide⟩ 1 with he2
  set e3 : E6Vec := Pi.single ⟨3, by decide⟩ 1 with he3
  set e4 : E6Vec := Pi.single ⟨4, by decide⟩ 1 with he4
  have hr : reflect TwistTag.E6.tag ⟨3, by decide⟩ e2 = e2 + e3 := by decide +kernel
  have hγ : IsRoot TwistTag.E6.tag (e2 + e3) := hr ▸ IsRoot.reflect _ (isRoot_single _ _)
  have hsum : e2 + e3 + -e2 = e3 := by abel
  obtain ⟨η, hη, hW⟩ :=
    weylElt_conj_pinnedX_int (τ := TwistTag.E6.tag) ⟨3, by decide⟩ (isRoot_single _ ⟨2, by decide⟩)
  obtain ⟨hκ, hF⟩ := (simply_laced_root_commutator_unit TwistTag.E6.tag simplyLaced_E6 hγ
    (isRoot_neg_single _ ⟨2, by decide⟩) (by decide +kernel) (by decide +kernel)).1
    (by rw [hsum]; exact isRoot_single _ _)
  set κ := commConst TwistTag.E6.tag (e2 + e3) (-e2) (1, 1)
  refine ⟨κ * η, ?_, fun K _ => ?_⟩
  · rcases hκ with h | h <;> rcases hη with h' | h' <;> simp [h, h']
  set P := diagramMap TwistTag.E6 K
  set D := rootDiagUnit TwistTag.E6.tag (signTuple K)
  set n := weylElt TwistTag.E6.tag K ⟨3, by decide⟩ 1
  have hp2 : TwistTag.E6.perm ⟨2, by decide⟩ = ⟨4, by decide⟩ := by decide
  have hp3 : TwistTag.E6.perm ⟨3, by decide⟩ = ⟨3, by decide⟩ := by decide
  have hp4 : TwistTag.E6.perm ⟨4, by decide⟩ = ⟨2, by decide⟩ := by decide
  have hPn : P * n * P⁻¹ = n := by rw [conjP_weylElt, hp3]
  have hDn : D * n * D⁻¹ = n := conjD_weylElt_of_ne (by decide)
  have ha : ∀ c : K, n * xUnit TwistTag.E6.tag K ⟨2, by decide⟩ c * n⁻¹ =
      pinnedX TwistTag.E6.tag K (e2 + e3) ((η : K) * c) := fun c => by
    rw [← pinnedX_single, hW K c, hr]
  have hPa : ∀ c : K, P * (n * xUnit TwistTag.E6.tag K ⟨2, by decide⟩ c * n⁻¹) * P⁻¹ =
      n * xUnit TwistTag.E6.tag K ⟨4, by decide⟩ c * n⁻¹ := fun c => by
    rw [conj_mul_mul, hPn, conjP_xUnit, hp2, show P * n⁻¹ * P⁻¹ = (P * n * P⁻¹)⁻¹ by group, hPn]
  have hay : ∀ c d : K, ⁅n * xUnit TwistTag.E6.tag K ⟨2, by decide⟩ c * n⁻¹,
      yUnit TwistTag.E6.tag K ⟨2, by decide⟩ d⁆ =
        xUnit TwistTag.E6.tag K ⟨3, by decide⟩ (((κ * η : ℤ) : K) * c * d) := fun c d => by
    rw [ha, ← pinnedX_neg_single, hF K, hsum, pinnedX_single]
    congr 1
    push_cast
    ring
  have hbz : ∀ c d : K, ⁅n * xUnit TwistTag.E6.tag K ⟨4, by decide⟩ c * n⁻¹,
      yUnit TwistTag.E6.tag K ⟨4, by decide⟩ d⁆ =
        xUnit TwistTag.E6.tag K ⟨3, by decide⟩ (((κ * η : ℤ) : K) * c * d) := fun c d => by
    have h := congrArg (fun g => P * g * P⁻¹) (hay c d)
    rwa [conj_commutatorElement, hPa, conjP_yUnit, hp2, conjP_xUnit, hp3] at h
  have haz : ∀ c d : K, n * xUnit TwistTag.E6.tag K ⟨2, by decide⟩ c * n⁻¹ *
      yUnit TwistTag.E6.tag K ⟨4, by decide⟩ d =
        yUnit TwistTag.E6.tag K ⟨4, by decide⟩ d *
          (n * xUnit TwistTag.E6.tag K ⟨2, by decide⟩ c * n⁻¹) := fun c d => by
    rw [ha, ← pinnedX_neg_single]
    exact commute_pinnedX_of_not_isRoot hγ (isRoot_neg_single _ _) (by decide +kernel)
      (by decide +kernel) (not_isRoot_of_check (by decide +kernel)) _ _
  have hby : ∀ c d : K, n * xUnit TwistTag.E6.tag K ⟨4, by decide⟩ c * n⁻¹ *
      yUnit TwistTag.E6.tag K ⟨2, by decide⟩ d =
        yUnit TwistTag.E6.tag K ⟨2, by decide⟩ d *
          (n * xUnit TwistTag.E6.tag K ⟨4, by decide⟩ c * n⁻¹) := fun c d => by
    have h := conj_eq_of_mul_eq (p := P) (haz c d)
    rwa [hPa, conjP_yUnit, hp4] at h
  have hva : ∀ c t : K, xUnit TwistTag.E6.tag K ⟨3, by decide⟩ t *
      (n * xUnit TwistTag.E6.tag K ⟨2, by decide⟩ c * n⁻¹) =
        n * xUnit TwistTag.E6.tag K ⟨2, by decide⟩ c * n⁻¹ *
          xUnit TwistTag.E6.tag K ⟨3, by decide⟩ t := fun c t => by
    rw [ha, ← pinnedX_single]
    exact commute_pinnedX_of_not_isRoot (isRoot_single _ _) hγ (by decide +kernel)
      (by decide +kernel) (not_isRoot_of_check (by decide +kernel)) _ _
  have hvy : ∀ d t : K, xUnit TwistTag.E6.tag K ⟨3, by decide⟩ t *
      yUnit TwistTag.E6.tag K ⟨2, by decide⟩ d =
        yUnit TwistTag.E6.tag K ⟨2, by decide⟩ d * xUnit TwistTag.E6.tag K ⟨3, by decide⟩ t :=
    fun d t => by
    rw [← pinnedX_single, ← pinnedX_neg_single]
    exact commute_pinnedX_of_not_isRoot (isRoot_single _ _) (isRoot_neg_single _ _)
      (by decide +kernel) (by decide +kernel) (not_isRoot_of_check (by decide +kernel)) _ _
  have hxx : ∀ c : K, xUnit TwistTag.E6.tag K ⟨2, by decide⟩ c *
      xUnit TwistTag.E6.tag K ⟨4, by decide⟩ c =
        xUnit TwistTag.E6.tag K ⟨4, by decide⟩ c * xUnit TwistTag.E6.tag K ⟨2, by decide⟩ c :=
    fun c => by
    rw [← pinnedX_single, ← pinnedX_single]
    exact commute_pinnedX_of_not_isRoot (isRoot_single _ _) (isRoot_single _ _)
      (by decide +kernel) (by decide +kernel) (not_isRoot_of_check (by decide +kernel)) _ _
  have hyy : ∀ d : K, yUnit TwistTag.E6.tag K ⟨2, by decide⟩ d *
      yUnit TwistTag.E6.tag K ⟨4, by decide⟩ d =
        yUnit TwistTag.E6.tag K ⟨4, by decide⟩ d * yUnit TwistTag.E6.tag K ⟨2, by decide⟩ d :=
    fun d => by
    rw [← pinnedX_neg_single, ← pinnedX_neg_single]
    exact commute_pinnedX_of_not_isRoot (isRoot_neg_single _ _) (isRoot_neg_single _ _)
      (by decide +kernel) (by decide +kernel) (not_isRoot_of_check (by decide +kernel)) _ _
  have hcomm : ∀ c d : K, ⁅longY K c, longZ K d⁆ =
      xUnit TwistTag.E6.tag K ⟨3, by decide⟩ (2 * ((κ * η : ℤ) : K) * c * d) := fun c d => by
    have hY : longY K c = n * xUnit TwistTag.E6.tag K ⟨2, by decide⟩ c * n⁻¹ *
        (n * xUnit TwistTag.E6.tag K ⟨4, by decide⟩ c * n⁻¹) := by
      show n * (xUnit TwistTag.E6.tag K ⟨2, by decide⟩ c *
        xUnit TwistTag.E6.tag K ⟨4, by decide⟩ c) * n⁻¹ = _
      group
    rw [hY, longZ, commutatorElement_mul_mul_of_commute (hay c d) (hbz c d) (hby c d)
      (haz c d) (hva c _) (hvy d _), ← xUnit_add]
    congr 1
    ring
  have hPY : ∀ c : K, P * longY K c * P⁻¹ = longY K c := fun c => by
    show P * (n * (xUnit TwistTag.E6.tag K ⟨2, by decide⟩ c *
      xUnit TwistTag.E6.tag K ⟨4, by decide⟩ c) * n⁻¹) * P⁻¹ =
        n * (xUnit TwistTag.E6.tag K ⟨2, by decide⟩ c * xUnit TwistTag.E6.tag K ⟨4, by decide⟩ c) *
          n⁻¹
    rw [conj_mul_mul, hPn, show P * n⁻¹ * P⁻¹ = (P * n * P⁻¹)⁻¹ by group, hPn,
      show P * (xUnit TwistTag.E6.tag K ⟨2, by decide⟩ c * xUnit TwistTag.E6.tag K ⟨4, by decide⟩ c)
        * P⁻¹ = (P * xUnit TwistTag.E6.tag K ⟨2, by decide⟩ c * P⁻¹) *
          (P * xUnit TwistTag.E6.tag K ⟨4, by decide⟩ c * P⁻¹) by group,
      conjP_xUnit, conjP_xUnit, hp2, hp4, hxx]
  have hDY : ∀ c : K, D * longY K c * D⁻¹ = longY K c := fun c => by
    show D * (n * (xUnit TwistTag.E6.tag K ⟨2, by decide⟩ c *
      xUnit TwistTag.E6.tag K ⟨4, by decide⟩ c) * n⁻¹) * D⁻¹ =
        n * (xUnit TwistTag.E6.tag K ⟨2, by decide⟩ c * xUnit TwistTag.E6.tag K ⟨4, by decide⟩ c) *
          n⁻¹
    rw [conj_mul_mul, hDn, show D * n⁻¹ * D⁻¹ = (D * n * D⁻¹)⁻¹ by group, hDn,
      show D * (xUnit TwistTag.E6.tag K ⟨2, by decide⟩ c * xUnit TwistTag.E6.tag K ⟨4, by decide⟩ c)
        * D⁻¹ = (D * xUnit TwistTag.E6.tag K ⟨2, by decide⟩ c * D⁻¹) *
          (D * xUnit TwistTag.E6.tag K ⟨4, by decide⟩ c * D⁻¹) by group,
      conjD_xUnit_of_ne (by decide), conjD_xUnit_of_ne (by decide)]
  have hPZ : ∀ d : K, P * longZ K d * P⁻¹ = longZ K d := fun d => by
    rw [longZ, show P * (yUnit TwistTag.E6.tag K ⟨2, by decide⟩ d *
        yUnit TwistTag.E6.tag K ⟨4, by decide⟩ d) * P⁻¹ =
          (P * yUnit TwistTag.E6.tag K ⟨2, by decide⟩ d * P⁻¹) *
            (P * yUnit TwistTag.E6.tag K ⟨4, by decide⟩ d * P⁻¹) by group,
      conjP_yUnit, conjP_yUnit, hp2, hp4, hyy]
  have hDZ : ∀ d : K, D * longZ K d * D⁻¹ = longZ K d := fun d => by
    rw [longZ, show D * (yUnit TwistTag.E6.tag K ⟨2, by decide⟩ d *
        yUnit TwistTag.E6.tag K ⟨4, by decide⟩ d) * D⁻¹ =
          (D * yUnit TwistTag.E6.tag K ⟨2, by decide⟩ d * D⁻¹) *
            (D * yUnit TwistTag.E6.tag K ⟨4, by decide⟩ d * D⁻¹) by group,
      conjD_yUnit_of_ne (by decide), conjD_yUnit_of_ne (by decide)]
  have hAY : ∀ c : K, longY K c * twistA K = twistA K * longY K c := fun c =>
    commute_twistA_of_conj (hPY c) (hDY c)
  have hAZ : ∀ d : K, longZ K d * twistA K = twistA K * longZ K d := fun d =>
    commute_twistA_of_conj (hPZ d) (hDZ d)
  refine ⟨hAY, hAZ, fun c => commute_twistA_of_conj (by rw [conjP_xUnit, hp3])
    (conjD_xUnit_of_ne (by decide) c), hcomm, fun h2 t => ?_⟩
  have hY1 : longY K 1 ∈ adjointGroup TwistTag.E6.tag K :=
    mul_mem (mul_mem (weylElt_mem_adjointGroup _ _) (mul_mem (xUnit_mem_adjointGroup _ _)
      (xUnit_mem_adjointGroup _ _))) (inv_mem (weylElt_mem_adjointGroup _ _))
  have hZ : ∀ d : K, longZ K d ∈ adjointGroup TwistTag.E6.tag K := fun d =>
    mul_mem (yUnit_mem_adjointGroup _ _) (yUnit_mem_adjointGroup _ _)
  have hε : ((κ * η : ℤ) : K) ≠ 0 := by
    rcases hκ with h | h <;> rcases hη with h' | h' <;> simp [h, h']
  have h2' : (2 : K) ≠ 0 := Ring.two_ne_zero h2
  refine ⟨longY K 1, mem_fixedGroup.2 ⟨hY1, hAY 1⟩, longZ K (t / (2 * ((κ * η : ℤ) : K))),
    mem_fixedGroup.2 ⟨hZ _, hAZ _⟩, ?_⟩
  rw [hcomm]
  congr 1
  field_simp

end CFSG.LieType.Chevalley
