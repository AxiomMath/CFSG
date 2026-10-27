module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.Weyl
public import CFSG.Quasithin.Background.SmithCurtisChev

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.Quasithin.SmithCurtis.Chev
open scoped Pointwise


variable {t : TwistTag} {K : Type} [Field K]

namespace LongestData

theorem perm_perm (D : LongestData t) (i : Fin t.tag.rank) : t.perm (t.perm i) = i := by
  have h : t.perm.symm = t.perm := D.perm_symm
  calc t.perm (t.perm i) = t.perm (t.perm.symm i) := by rw [h]
    _ = i := t.perm.apply_symm_apply i

theorem smul_single_perm (D : LongestData t) (i : Fin t.tag.rank) :
    D.w • (Pi.single (t.perm i) 1 : Fin t.tag.rank → ℤ) = -Pi.single i 1 := by
  rw [D.smul, permLattice_single, D.perm_perm]

theorem image_smul_posComplement (D : LongestData t) (i : Fin t.tag.rank) :
    (fun α => D.w • α) '' {α | IsRoot t.tag α ∧ 0 < height α ∧
        α ≠ (Pi.single (t.perm i) 1 : Fin t.tag.rank → ℤ)} =
      {γ | IsRoot t.tag γ ∧ height γ < 0 ∧ γ ≠ -(Pi.single i 1 : Fin t.tag.rank → ℤ)} := by
  ext γ
  constructor
  · rintro ⟨α, ⟨hr, hp, hne⟩, rfl⟩
    show D.w • α ∈ _
    rw [D.smul]
    refine ⟨CFSG.LieType.Chevalley.IsRoot.neg (hr.permLattice t.cartan_perm), ?_, fun h => hne ?_⟩
    · rw [height_neg, height_permLattice]
      omega
    · have h1 : permLattice t.perm α = Pi.single i 1 := neg_inj.1 h
      have h2 := congrArg (permLattice t.perm) h1
      rw [permLattice_permLattice D, permLattice_single] at h2
      exact h2
  · rintro ⟨hγ, hn, hne⟩
    have hr : IsRoot t.tag (permLattice t.perm (-γ)) :=
      (CFSG.LieType.Chevalley.IsRoot.neg hγ).permLattice t.cartan_perm
    refine ⟨permLattice t.perm (-γ), ⟨hr, ?_, fun h => hne ?_⟩, ?_⟩
    · rw [height_permLattice, height_neg]
      omega
    · have h2 := congrArg (permLattice t.perm) h
      rw [permLattice_permLattice D, permLattice_single, D.perm_perm] at h2
      rw [← neg_neg γ, h2]
    · simp only [D.smul, permLattice_neg, permLattice_permLattice D, neg_neg]

end LongestData

section Opposite

variable (D : LongestData t)
include D

theorem map_conj_posUnipotent_LD :
    (posUnipotent t.tag K).map (MulAut.conj (canonicalRep (coxeterSystem t.tag) K D.w)).toMonoidHom =
      negUnipotent t.tag K := by
  unfold posUnipotent negUnipotent
  rw [(canonical_weyl_root_transport t.tag K).1 D.w _ (fun α h => h.1), D.image_smul_posRoots]

theorem map_conj_posComplement_LD (i : Fin t.tag.rank) :
    (posComplement t.tag K (t.perm i)).map
        (MulAut.conj (canonicalRep (coxeterSystem t.tag) K D.w)).toMonoidHom =
      negComplement t.tag K i := by
  rw [posComplement, (canonical_weyl_root_transport t.tag K).1 D.w _ (fun α h => h.1),
    D.image_smul_posComplement i]
  rfl

theorem map_conj_rootSubgroup_single_LD (i : Fin t.tag.rank) :
    (rootSubgroup t.tag K (Pi.single (t.perm i) 1)).map
        (MulAut.conj (canonicalRep (coxeterSystem t.tag) K D.w)).toMonoidHom =
      rootSubgroup t.tag K (-Pi.single i 1) := by
  rw [(canonical_weyl_root_transport t.tag K).2.1 D.w _ (isRoot_single t.tag _),
    D.smul_single_perm i]

theorem negUnipotent_eq_mul_LD (i : Fin t.tag.rank) {l : ModGL t.tag K}
    (hl : l ∈ negUnipotent t.tag K) : ∃ y ∈ rootSubgroup t.tag K (-Pi.single i 1),
      ∃ q ∈ negComplement t.tag K i, l = y * q := by
  rw [← map_conj_posUnipotent_LD D] at hl
  obtain ⟨u, hu, rfl⟩ := hl
  have hU := (simple_positive_root_complement t.tag K (t.perm i)).2.2.1
  have hu' : u ∈ (rootSubgroup t.tag K (Pi.single (t.perm i) 1) : Set (ModGL t.tag K)) *
      (posComplement t.tag K (t.perm i) : Set (ModGL t.tag K)) := by
    rw [posComplement, ← hU]
    exact hu
  obtain ⟨x, hx, v, hv, rfl⟩ := hu'
  refine ⟨MulAut.conj (canonicalRep (coxeterSystem t.tag) K D.w) x, ?_,
    MulAut.conj (canonicalRep (coxeterSystem t.tag) K D.w) v, ?_, map_mul _ x v⟩
  · rw [← map_conj_rootSubgroup_single_LD D i]
    exact ⟨x, hx, rfl⟩
  · rw [← map_conj_posComplement_LD D i]
    exact ⟨v, hv, rfl⟩

theorem negComplement_normal_LD (i : Fin t.tag.rank) {y q : ModGL t.tag K}
    (hy : y ∈ rootSubgroup t.tag K (-Pi.single i 1)) (hq : q ∈ negComplement t.tag K i) :
    y * q * y⁻¹ ∈ negComplement t.tag K i := by
  rw [← map_conj_rootSubgroup_single_LD D i] at hy
  rw [← map_conj_posComplement_LD D i] at hq ⊢
  obtain ⟨x, hx, rfl⟩ := hy
  obtain ⟨v, hv, rfl⟩ := hq
  have hnorm := (simple_positive_root_complement t.tag K (t.perm i)).2.1
  have hxv : x * v * x⁻¹ ∈ posComplement t.tag K (t.perm i) := by
    have hn := (Subgroup.normal_subgroupOf_iff (posComplement_le (K := K) (t.perm i))).1 hnorm
    exact hn v x hv (rootSubgroup_single_le (t.perm i) hx)
  exact ⟨x * v * x⁻¹, hxv, by simp only [map_mul, map_inv]⟩

theorem xUnit_conj_negComplement_LD (i : Fin t.tag.rank) {x q : ModGL t.tag K}
    (hx : x ∈ rootSubgroup t.tag K (Pi.single i 1)) (hq : q ∈ negComplement t.tag K i) :
    x * q * x⁻¹ ∈ negComplement t.tag K i := by
  obtain ⟨c, rfl⟩ := mem_rootSubgroup_single.mp hx
  set n := weylElt t.tag K i 1
  have hy : n⁻¹ * xUnit t.tag K i c * n ∈ rootSubgroup t.tag K (-Pi.single i 1) := by
    rw [weylElt_inv_conj_xUnit]
    exact yUnit_mem_rootSubgroup i _
  have e : xUnit t.tag K i c * q * (xUnit t.tag K i c)⁻¹ =
      n * ((n⁻¹ * xUnit t.tag K i c * n) * (n⁻¹ * q * n) *
        (n⁻¹ * xUnit t.tag K i c * n)⁻¹) * n⁻¹ := by
    group
  rw [e]
  exact weylElt_conj_negComplement i (negComplement_normal_LD D i hy
    (weylElt_inv_conj_negComplement i hq))

theorem cover_LD {g : ModGL t.tag K} (hg : g ∈ adjointGroup t.tag K) :
    ∃ l ∈ negUnipotent t.tag K, ∃ w : WeylGroup t.tag, ∃ h ∈ torusGroup t.tag K,
      ∃ u ∈ posUnipotent t.tag K,
        g = l * canonicalRep (coxeterSystem t.tag) K w * (h * u) := by
  set n₁ := canonicalRep (coxeterSystem t.tag) K D.w
  have hn₁ : n₁ ∈ adjointGroup t.tag K := canonicalRep_mem_adjointGroup _ K D.w
  have hg' : n₁⁻¹ * g ∈ (adjointGroup t.tag K : Set (ModGL t.tag K)) := mul_mem (inv_mem hn₁) hg
  rw [adjointGroup_eq_iUnion_bruhatCell] at hg'
  obtain ⟨v, hv⟩ := Set.mem_iUnion.1 hg'
  obtain ⟨b, hb, b', hb', hbb⟩ := mem_bruhatCell.1 hv
  obtain ⟨-, -, hHnorm, -, hHU, -⟩ := triangular_borel_structure.{0, 0} t.tag K
  have hb2 : b ∈ (torusGroup t.tag K : Set (ModGL t.tag K)) *
      (posUnipotent t.tag K : Set (ModGL t.tag K)) := by
    rw [← hHU]
    exact hb
  have hb'2 : b' ∈ (torusGroup t.tag K : Set (ModGL t.tag K)) *
      (posUnipotent t.tag K : Set (ModGL t.tag K)) := by
    rw [← hHU]
    exact hb'
  obtain ⟨h₀, hh₀, u₀, hu₀, rfl⟩ := hb2
  obtain ⟨h₁, hh₁, u₁, hu₁, rfl⟩ := hb'2
  obtain ⟨k, hk, hkn⟩ := canonicalRep_mul_mem (R := K) D.w v
  have hnorm := (canonical_weyl_root_transport t.tag K).2.2
  set H₀ := n₁ * h₀ * n₁⁻¹
  have hH₀ : H₀ ∈ torusGroup t.tag K := (Subgroup.mem_normalizer_iff.mp (hnorm D.w) h₀).mp hh₀
  set L₀ := n₁ * u₀ * n₁⁻¹
  have hL₀ : L₀ ∈ negUnipotent t.tag K := by
    rw [← map_conj_posUnipotent_LD D]
    exact ⟨u₀, hu₀, rfl⟩
  set n' := canonicalRep (coxeterSystem t.tag) K (D.w * v)
  have hHk : n'⁻¹ * (H₀ * k) * n' ∈ torusGroup t.tag K := by
    have e : n'⁻¹ * (H₀ * k) * n' = n'⁻¹ * (H₀ * k) * n'⁻¹⁻¹ := by rw [inv_inv]
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (inv_mem (hnorm (D.w * v))) (H₀ * k)).mp
      (mul_mem hH₀ hk)
  have hl : H₀ * L₀ * H₀⁻¹ ∈ negUnipotent t.tag K :=
    (Subgroup.mem_normalizer_iff.mp (torusGroup_le_normalizer_negUnipotent hH₀) L₀).mp hL₀
  refine ⟨H₀ * L₀ * H₀⁻¹, hl, D.w * v, n'⁻¹ * (H₀ * k) * n' * h₁, mul_mem hHk hh₁, u₁, hu₁, ?_⟩
  have hg2 : g = n₁ * (h₀ * u₀ * canonicalRep (coxeterSystem t.tag) K v * (h₁ * u₁)) := by
    rw [hbb]
    group
  have e1 : n₁ * canonicalRep (coxeterSystem t.tag) K v = k * n' := hkn
  rw [hg2]
  have e2 : n₁ * (h₀ * u₀ * canonicalRep (coxeterSystem t.tag) K v * (h₁ * u₁)) =
      H₀ * L₀ * (n₁ * canonicalRep (coxeterSystem t.tag) K v) * (h₁ * u₁) := by
    simp only [H₀, L₀]
    group
  rw [e2, e1, show canonicalRep (coxeterSystem t.tag) K (D.w * v) = n' from rfl]
  group

end Opposite

variable (t K) in
@[expose] def chevDatumLD
    [Finite K] (p : ℕ) [CharP K p]
    (D : LongestData t) :
    CurtisDatum (adjointGroup t.tag K) (coxeterSystem t.tag) p where
  U := (posUnipotent t.tag K).subgroupOf (adjointGroup t.tag K)
  L := (negUnipotent t.tag K).subgroupOf (adjointGroup t.tag K)
  H := (torusGroup t.tag K).subgroupOf (adjointGroup t.tag K)
  X i := (rootSubgroup t.tag K (Pi.single i 1)).subgroupOf (adjointGroup t.tag K)
  Y i := (rootSubgroup t.tag K (-Pi.single i 1)).subgroupOf (adjointGroup t.tag K)
  Us i := (posComplement t.tag K i).subgroupOf (adjointGroup t.tag K)
  Q i := (negComplement t.tag K i).subgroupOf (adjointGroup t.tag K)
  n i := nC t.tag K i
  nW w := nWC t.tag K w
  phi i := torusPart t.tag K i
  psi i := torusPart t.tag K i
  isPGroup_U := ((positive_root_triangularity.{0, 0} t.tag).2 K p).2.1.of_equiv
    (Subgroup.subgroupOfEquivOfLe posUnipotent_le_adjointGroup).symm
  isPGroup_L := ((positive_root_triangularity.{0, 0} t.tag).2 K p).2.2.2.of_equiv
    (Subgroup.subgroupOfEquivOfLe negUnipotent_le_adjointGroup').symm
  U_inf_L := by
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hx
    have h : (x : ModGL t.tag K) ∈ posUnipotent t.tag K ⊓ negUnipotent t.tag K := Subgroup.mem_inf.2 ⟨h1, h2⟩
    rw [posUnipotent_inf_negUnipotent, Subgroup.mem_bot] at h
    exact Subgroup.mem_bot.2 (Subtype.ext h)
  H_comm a ha b hb := Subtype.ext ((triangular_borel_structure.{0, 0} t.tag K).1 _ ha _ hb)
  H_normU h hh u hu := conj_mem_subgroupOf
    ((Subgroup.mem_normalizer_iff.mp ((triangular_borel_structure.{0, 0} t.tag K).2.2.1 hh) u).mp hu)
  H_normU' h hh u hu := conj_inv_mem_subgroupOf
    (torus_inv_conj_mem ((triangular_borel_structure.{0, 0} t.tag K).2.2.1 hh) hu)
  H_normL h hh l hl := conj_mem_subgroupOf
    ((Subgroup.mem_normalizer_iff.mp (torusGroup_le_normalizer_negUnipotent hh) l).mp hl)
  H_normX i h hh x hx := conj_mem_subgroupOf (torus_conj_mem_rootSubgroup (isRoot_single t.tag i) hh hx)
  H_normQ i h hh q hq := conj_mem_subgroupOf (torus_conj_mem_rootSpan (fun γ hγ => hγ.1) hh hq)
  X_le i x hx := rootSubgroup_single_le i hx
  X_ne_bot i := by
    intro h
    have hx : xC t.tag K i 1 ∈ (rootSubgroup t.tag K (Pi.single i 1)).subgroupOf (adjointGroup t.tag K) :=
      xUnit_mem_rootSubgroup i 1
    rw [h, Subgroup.mem_bot] at hx
    have h1 : xUnit t.tag K i (1 : K) = xUnit t.tag K i 0 := by
      rw [xUnit_zero]
      exact congrArg Subtype.val hx
    exact one_ne_zero (xUnit_injective i h1)
  U_eq i u hu := by
    have hU := (simple_positive_root_complement t.tag K i).2.2.1
    have hu' : (u : ModGL t.tag K) ∈ (rootSubgroup t.tag K (Pi.single i 1) : Set (ModGL t.tag K)) *
        (posComplement t.tag K i : Set (ModGL t.tag K)) := by
      rw [posComplement, ← hU]
      exact hu
    obtain ⟨x, hx, v, hv, e⟩ := hu'
    exact ⟨⟨x, rootSubgroup_le_adjointGroup _ hx⟩, hx,
      ⟨v, posUnipotent_le_adjointGroup (posComplement_le i hv)⟩, hv, Subtype.ext e.symm⟩
  Us_le i v hv := posComplement_le i hv
  X_normUs i x hx v hv := by
    have hn := (Subgroup.normal_subgroupOf_iff (posComplement_le (K := K) i)).1
      (simple_positive_root_complement t.tag K i).2.1
    exact conj_mem_subgroupOf (hn _ _ hv (rootSubgroup_single_le i hx))
  n_normUs i v hv := by
    have h := (simple_Weyl_positive_complement t.tag K i 1).1
    refine conj_mem_subgroupOf ?_
    rw [← h]
    exact ⟨v, hv, rfl⟩
  n_normUs' i v hv := by
    have h := (simple_Weyl_positive_complement t.tag K i 1).1
    refine conj_inv_mem_subgroupOf ?_
    have hv' : (v : ModGL t.tag K) ∈ (posComplement t.tag K i).map
        (MulAut.conj (weylElt t.tag K i 1)).toMonoidHom := by
      rw [h]
      exact hv
    obtain ⟨v', hv', e⟩ := hv'
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at e
    show (weylElt t.tag K i 1)⁻¹ * v * weylElt t.tag K i 1 ∈ posComplement t.tag K i
    rw [← e]
    group
    exact hv'
  Y_le i y hy := rootSubgroup_neg_single_le i hy
  Q_le i q hq := negComplement_le i hq
  L_le i l hl := by
    obtain ⟨y, hy, q, hq, e⟩ := negUnipotent_eq_mul_LD D i hl
    have hl' : l = ⟨y, rootSubgroup_le_adjointGroup _ hy⟩ *
        ⟨q, negUnipotent_le_adjointGroup' (negComplement_le i hq)⟩ := Subtype.ext e
    rw [hl']
    exact mul_mem (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right hq)
  X_normQ i x hx q hq := by
    exact conj_mem_subgroupOf (xUnit_conj_negComplement_LD D i hx hq)
  Y_normQ i y hy q hq := by
    exact conj_mem_subgroupOf (negComplement_normal_LD D i hy hq)
  n_normQ i q hq := conj_mem_subgroupOf (weylElt_conj_negComplement i hq)
  n_conjX i x hx := by
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨c, hc⟩ := mem_rootSubgroup_single.mp hx
    refine conj_mem_subgroupOf ?_
    change weylElt t.tag K i 1 * (x : ModGL t.tag K) * (weylElt t.tag K i 1)⁻¹ ∈ _
    rw [← hc, weylElt_conj_xUnit]
    exact yUnit_mem_rootSubgroup i _
  n_conjY i y hy := by
    rw [Subgroup.mem_subgroupOf] at hy
    obtain ⟨c, hc⟩ := mem_rootSubgroup_neg_single.mp hy
    refine conj_mem_subgroupOf ?_
    change weylElt t.tag K i 1 * (y : ModGL t.tag K) * (weylElt t.tag K i 1)⁻¹ ∈ _
    rw [← hc, weylElt_conj_yUnit]
    exact xUnit_mem_rootSubgroup i _
  n_sq i := weylElt_sq_mem_torus i
  n_normH i h hh := conj_mem_subgroupOf (weylElt_mem_normalizer_torus' i hh)
  phi_mem i x hx hx1 := by
    obtain ⟨c, hc⟩ := exists_unit_of_mem hx hx1
    rw [torusPart_eq hc]
    exact torusElt_mem_torusGroup i _
  psi_mem i x hx hx1 := by
    obtain ⟨c, hc⟩ := exists_unit_of_mem hx hx1
    rw [torusPart_eq hc]
    exact torusElt_mem_torusGroup i _
  phi_spec i x hx hx1 := by
    obtain ⟨c, hc⟩ := exists_unit_of_mem hx hx1
    rw [torusPart_eq hc]
    refine ⟨yC t.tag K i ((c⁻¹ : Kˣ) : K), rootSubgroup_neg_single_le i (yUnit_mem_rootSubgroup i _),
      xC t.tag K i (-((c⁻¹ : Kˣ) : K)), rootSubgroup_single_le i (xUnit_mem_rootSubgroup i _), ?_⟩
    refine Subtype.ext ?_
    change (x : ModGL t.tag K) * weylElt t.tag K i 1 = yUnit t.tag K i ((c⁻¹ : Kˣ) : K) *
      torusElt t.tag K i (-c) * xUnit t.tag K i (-((c⁻¹ : Kˣ) : K))
    rw [hc, xUnit_mul_weylElt, weylElt_inv_conj_yUnit, weylElt_one_mul_self, ← torusElt_mul,
      mul_neg_one]
  psi_spec i x hx hx1 := by
    obtain ⟨c, hc⟩ := exists_unit_of_mem hx hx1
    rw [torusPart_eq hc]
    refine ⟨xC t.tag K i (-((c⁻¹ : Kˣ) : K)), xUnit_mem_rootSubgroup i _,
      xC t.tag K i (-((c⁻¹ : Kˣ) : K)), rootSubgroup_single_le i (xUnit_mem_rootSubgroup i _), ?_⟩
    refine Subtype.ext ?_
    change weylElt t.tag K i 1 * (x : ModGL t.tag K) * weylElt t.tag K i 1 =
      xUnit t.tag K i (-((c⁻¹ : Kˣ) : K)) * weylElt t.tag K i 1 * torusElt t.tag K i (-c) *
        xUnit t.tag K i (-((c⁻¹ : Kˣ) : K))
    rw [hc, CFSG.Quasithin.SmithCurtis.Chev.weylElt_mul_xUnit_mul_weylElt, weylElt_inv_conj_torusElt, weylElt_inv_conj_yUnit,
      inv_neg, inv_inv]
  bruhatY i y hy hy1 := by
    rw [Subgroup.mem_subgroupOf] at hy
    obtain ⟨c, hc⟩ := mem_rootSubgroup_neg_single.mp hy
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply hy1
      refine Subtype.ext ?_
      rw [← hc, yUnit_zero]
      rfl
    obtain ⟨h, hh, a, ha, b, hb, e⟩ := yUnit_eq (K := K) i (Units.mk0 c hc0)
    refine ⟨⟨h, (triangular_borel_structure.{0, 0} t.tag K).2.2.2.2.2.2.2.2.2.2.2 K |>.1
      (Subgroup.mem_sup_left hh)⟩, hh, ⟨a, rootSubgroup_le_adjointGroup _ ha⟩, ha,
      ⟨b, rootSubgroup_le_adjointGroup _ hb⟩, hb, Subtype.ext ?_⟩
    change (y : ModGL t.tag K) = a * (h * weylElt t.tag K i 1) * b
    rw [← hc, ← e, Units.val_mk0]
  nW_one := Subtype.ext (canonicalRep_one _ K)
  nW_simple_mul w i h := Subtype.ext (weylElt_mul_canonicalRep_of_length_eq h).symm
  nW_conj w i h x hx := canonicalRep_inv_conj_mem h hx
  heckeDeg_mul w i h := by
    rw [heckeDeg_subgroupOf posUnipotent_le_adjointGroup,
      heckeDeg_subgroupOf posUnipotent_le_adjointGroup,
      heckeDeg_subgroupOf posUnipotent_le_adjointGroup]
    change heckeDeg _ (weylElt t.tag K i 1) * heckeDeg _ (canonicalRep (coxeterSystem t.tag) K w) =
      heckeDeg _ (canonicalRep (coxeterSystem t.tag) K ((coxeterSystem t.tag).simple i * w))
    rw [← canonicalRep_simple (coxeterSystem t.tag) K i, heckeDeg_canonicalRep,
      heckeDeg_canonicalRep, heckeDeg_canonicalRep, h, (coxeterSystem t.tag).length_simple,
      ← pow_add, add_comm]
  cover g := by
    obtain ⟨l, hl, w, h, hh, u, hu, e⟩ := cover_LD D g.2
    refine ⟨⟨l, negUnipotent_le_adjointGroup' hl⟩, hl, w,
      ⟨h, (triangular_borel_structure.{0, 0} t.tag K).2.2.2.2.2.2.2.2.2.2.2 K |>.1
        (Subgroup.mem_sup_left hh)⟩, hh, ⟨u, posUnipotent_le_adjointGroup hu⟩, hu,
      Subtype.ext e⟩


end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
