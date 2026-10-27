module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTPFieldGraph

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical (matrixIsometryGroup
  mem_matrixIsometryGroup)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (blockSwapJ)
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect)
open CFSG.ComponentClassification.OutcomeLocal (blockSwapIsometryEquivStatedSp oneRestrictEquiv
  nonempty_altIsometry_mulEquiv_statedSp dotForm_restrict_isAlt dotForm_restrict_nondegenerate
  finrank_dotForm_ker)
open CFSG.ComponentClassification.UnbalancedCatalog
  (even_linear_canonical_graph_symplectic_centralizers det_eq_one_of_mem_matrixIsometryGroup)
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.ComponentClassification.UnbalancedCatalog.NonalternatingRadical (radicalGroup
  radicalGroup_comm radicalImage_le_centralizer radicalImage_le_inner radicalImage_normal
  sq_eq_one_of_mem_centralizer_radicalImage)

variable {n : ℕ} {K : Type} [Field K] [Finite K]

variable (n K) in
@[expose] def HasSylowCard (X : Subgroup (projectiveSL n K)) (c : ℕ) : Prop :=
  ∀ S : Sylow 2 X, Nat.card S = c ^ (n * (n - 1) / 2)

theorem map_ne_of_lt_card_of_sylow {X Y T : Subgroup (projectiveSL n K)} {m : ℕ}
    (hX : ∀ S : Sylow 2 X, Nat.card S = m) {Γ : Type*} [Group Γ]
    {φ₁ φ₂ : projectiveSL n K →* Γ} (hφ₁ : Function.Injective φ₁)
    (hφ₂ : Function.Injective φ₂) (hTY : T ≤ Y) (hT : IsPGroup 2 T) (hlt : m < Nat.card T) :
    X.map φ₁ ≠ Y.map φ₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hXY
  have hcard := card_eq_of_map_eq hφ₁ hφ₂ hXY
  have hT' : IsPGroup 2 (T.subgroupOf Y) := hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTY).symm
  obtain ⟨Q, hQ⟩ := hT'.exists_le_sylow
  have h1 : Nat.card T ≤ Nat.card Q := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTY).toEquiv]
    exact Subgroup.card_le_of_le hQ
  obtain ⟨S⟩ : Nonempty (Sylow 2 X) := inferInstance
  have h2 : Nat.card Q = m := by
    rw [Sylow.card_eq_multiplicity, ← hcard, ← Sylow.card_eq_multiplicity S, hX S]
  omega

omit [Finite K] in
theorem map_ne_of_not_dvd_of_sylow {X Y Z : Subgroup (projectiveSL n K)} {m : ℕ}
    (hX : ∀ S : Sylow 2 X, Nat.card S = m) {Γ : Type*} [Group Γ]
    {φ₁ φ₂ : projectiveSL n K →* Γ} (hφ₁ : Function.Injective φ₁)
    (hφ₂ : Function.Injective φ₂) (hYZ : Y ≤ Z) (hdvd : ¬ m ∣ Nat.card Z) :
    X.map φ₁ ≠ Y.map φ₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hXY
  apply hdvd
  obtain ⟨S⟩ : Nonempty (Sylow 2 X) := inferInstance
  have h1 : m ∣ Nat.card X := by
    rw [← hX S]
    exact Subgroup.card_subgroup_dvd_card _
  rw [card_eq_of_map_eq hφ₁ hφ₂ hXY] at h1
  exact h1.trans (Subgroup.card_dvd_of_le hYZ)

theorem map_ne_perfectCore_blockSwap_of_sylow {f r c : ℕ} (hK : Nat.card K = 2 ^ f)
    (hn : 4 ≤ n) (hr : n = 2 * r) (hc2 : c ^ 2 = Nat.card K) (hc1 : 1 < c)
    {X : Subgroup (projectiveSL n K)} (hX : HasSylowCard n K X c) (C : GL (Fin n) K)
    (hC : (C : Matrix (Fin n) (Fin n) K) = blockSwapJ n r) {Γ : Type*} [Group Γ]
    {φ₁ φ₂ : projectiveSL n K →* Γ} (hφ₁ : Function.Injective φ₁)
    (hφ₂ : Function.Injective φ₂) :
    X.map φ₁ ≠ (perfectCore (autFixSubgroup (conjAut n K C * dualAut n K))).map φ₂ := by
  have : CharP K 2 := charP_two_of_card_eq_two_pow hK
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h1
    · have h1 := Finite.one_lt_card (α := K)
      rw [hK, h0, pow_zero] at h1
      exact absurd h1 (lt_irrefl 1)
    · exact h1
  have hn3 : 3 ≤ n := by omega
  have hrr : r + r = n := by omega
  have hf2 : 2 ≤ f := by
    by_contra h
    have h1 : 2 ^ f ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 : 4 ≤ c ^ 2 := by nlinarith
    omega
  obtain ⟨hinj, hNinn, -, -, hNC, -, -⟩ :=
    even_linear_canonical_graph_symplectic_centralizers hf hK hn3 C (Or.inr ⟨r, hr, hC⟩)
  set β := conjAut n K C * dualAut n K with hβ
  set N := (matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K)).map (conjAut n K) with hN
  have hconj := CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.conj_injective_projectiveSL
    (F := K) hn3
  set Y' := N.comap (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)) with hY'
  have hY'fix : Y' ≤ autFixSubgroup β := fun x hx =>
    (mem_autFixSubgroup_iff_conj_mem_centralizer hn3 β x).2 (hNC hx)
  have hmap : Y'.map (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)) = N :=
    Subgroup.map_comap_eq_self hNinn
  let eY : Y' ≃* N := (Y'.equivMapOfInjective _ hconj).trans (MulEquiv.subgroupCongr hmap)
  let eN : N ≃* matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K) :=
    (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, range_subtype])).trans
      (MonoidHom.ofInjective hinj).symm
  let eSp : matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K) ≃* StatedSp r K :=
    (MulEquiv.subgroupCongr (congrArg matrixIsometryGroup hC)).trans
      (blockSwapIsometryEquivStatedSp hrr)
  let E : StatedSp r K ≃* Y' := (eY.trans (eN.trans eSp)).symm
  have := LinearOuter.isPerfect_statedSp_of_card (r := r) hf hK (Or.inl hf2)
  have hY'perf : Group.IsPerfect Y' :=
    Group.IsPerfect.ofSurjective (f := E.toMonoidHom) E.surjective
  have hY'core : Y' ≤ perfectCore (autFixSubgroup β) :=
    le_perfectCore_of_perfect hY'fix (Subgroup.isPerfect_iff.mp hY'perf)
  set ι : StatedSp r K →* projectiveSL n K := Y'.subtype.comp E.toMonoidHom with hι
  have hιinj : Function.Injective ι := Y'.subtype_injective.comp E.injective
  set T := (SymplecticFlag.unipotent r K).map ι with hT
  have hTcard : Nat.card T = Nat.card K ^ (r ^ 2) := by
    rw [hT, Subgroup.card_map_of_injective hιinj, SymplecticFlag.card_unipotent]
  have hTp : IsPGroup 2 T := IsPGroup.of_card (n := f * r ^ 2) (by rw [hTcard, hK, ← pow_mul])
  have hTY : T ≤ perfectCore (autFixSubgroup β) := by
    rintro _ ⟨u, -, rfl⟩
    exact hY'core (E u).2
  refine map_ne_of_lt_card_of_sylow hX hφ₁ hφ₂ hTY hTp ?_
  rw [hTcard, ← hc2, ← pow_mul]
  apply Nat.pow_lt_pow_right hc1
  rw [Nat.div_lt_iff_lt_mul (by norm_num), hr]
  have h1 : 2 * r - 1 < 2 * r := by omega
  calc 2 * r * (2 * r - 1) < 2 * r * (2 * r) := Nat.mul_lt_mul_of_pos_left h1 (by omega)
    _ = 2 * r ^ 2 * 2 := by ring

theorem map_ne_perfectCore_dualAut_of_odd_of_sylow {f r c : ℕ} (hK : Nat.card K = 2 ^ f)
    (hr : n = 2 * r + 1) (hr1 : 1 ≤ r) (hc2 : c ^ 2 = Nat.card K)
    {X : Subgroup (projectiveSL n K)} (hX : HasSylowCard n K X c) {Γ : Type*} [Group Γ]
    {φ₁ φ₂ : projectiveSL n K →* Γ} (hφ₁ : Function.Injective φ₁)
    (hφ₂ : Function.Injective φ₂) :
    X.map φ₁ ≠ (perfectCore (autFixSubgroup (dualAut n K))).map φ₂ := by
  have : CharP K 2 := charP_two_of_card_eq_two_pow hK
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h1
    · have h1 := Finite.one_lt_card (α := K)
      rw [hK, h0, pow_zero] at h1
      exact absurd h1 (lt_irrefl 1)
    · exact h1
  set O := matrixIsometryGroup ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hO
  let ρ₀ : O →* SpecialLinearGroup (Fin n) K :=
    { toFun := fun g => ⟨((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
        det_eq_one_of_mem_matrixIsometryGroup g.2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl }
  set ρ := (proj n K).comp ρ₀ with hρ
  have hfix : autFixSubgroup (dualAut n K) ≤ ρ.range := by
    intro x hx
    obtain ⟨g, hgx, hg⟩ := exists_isometry_of_mem_autFixSubgroup_dualAut hx
    have hgO : Matrix.SpecialLinearGroup.toGL g ∈ O := by
      rw [hO, mem_matrixIsometryGroup, Units.val_one, Matrix.mul_one]
      exact hg
    refine ⟨⟨Matrix.SpecialLinearGroup.toGL g, hgO⟩, ?_⟩
    have h1 : ρ₀ ⟨Matrix.SpecialLinearGroup.toGL g, hgO⟩ = g := Subtype.ext rfl
    rw [hρ, MonoidHom.comp_apply, h1, hgx]
  have hOcard : Nat.card O =
      Nat.card K ^ (r ^ 2) * ∏ j ∈ Finset.Icc 1 r, (Nat.card K ^ (2 * j) - 1) := by
    obtain ⟨e⟩ := nonempty_altIsometry_mulEquiv_statedSp _
      (dotForm_restrict_isAlt (k := K) (n := n)) (dotForm_restrict_nondegenerate hr)
      (finrank_dotForm_ker hr)
    rw [Nat.card_congr (oneRestrictEquiv hr).toEquiv, Nat.card_congr e.toEquiv,
      SymplecticFlag.card_statedSp]
  have hc0 : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · rw [h0] at hc2
      have := Nat.card_pos (α := K)
      omega
    · exact h0
  have hc_even : 2 ∣ c := by
    have h1 : 2 ∣ c ^ 2 := by
      rw [hc2, hK]
      exact dvd_pow_self 2 (by omega)
    exact Nat.prime_two.dvd_of_dvd_pow h1
  have hndvd : ¬ c ^ (n * (n - 1) / 2) ∣ Nat.card ρ.range := by
    intro h
    have h1 := h.trans (Subgroup.card_range_dvd ρ)
    have hexp : n * (n - 1) / 2 = 2 * r ^ 2 + r := by
      rw [hr]
      refine Nat.div_eq_of_eq_mul_left (by norm_num) ?_
      rw [Nat.add_sub_cancel]
      ring
    have hK2 : Nat.card K ^ (r ^ 2) = c ^ (2 * r ^ 2) := by rw [← hc2, ← pow_mul]
    rw [hOcard, hexp, pow_add, hK2] at h1
    have h2 := Nat.dvd_of_mul_dvd_mul_left (pow_pos hc0 _) h1
    have h3 : 2 ∣ ∏ j ∈ Finset.Icc 1 r, (Nat.card K ^ (2 * j) - 1) :=
      (dvd_pow hc_even (by omega : r ≠ 0)).trans h2
    exact SymplecticFlag.not_dvd_prod_pow_two_mul_sub_one Nat.prime_two
      (by rw [hK]; exact dvd_pow_self 2 (by omega)) Nat.card_pos r h3
  exact map_ne_of_not_dvd_of_sylow hX hφ₁ hφ₂ ((perfectCore_le _).trans hfix) hndvd

theorem map_ne_perfectCore_dualAut_of_even_of_isSimpleGroup {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hn : 4 ≤ n) (he : Even n) {X : Subgroup (projectiveSL n K)} (hX : IsSimpleGroup X)
    (hXnc : ¬ ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) {Γ : Type*} [Group Γ]
    {φ₁ φ₂ : projectiveSL n K →* Γ} (hφ₁ : Function.Injective φ₁)
    (hφ₂ : Function.Injective φ₂) :
    X.map φ₁ ≠ (perfectCore (autFixSubgroup (dualAut n K))).map φ₂ := by
  have : CharP K 2 := charP_two_of_card_eq_two_pow hK
  have hn3 : 3 ≤ n := by omega
  have hconj := CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.conj_injective_projectiveSL
    (F := K) hn3
  intro hXY
  set i : Fin n := ⟨0, by omega⟩
  set R := (radicalGroup (K := K) i).map (conjAut n K) with hR
  set R' := R.comap (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)) with hR'
  set Cδ := autFixSubgroup (dualAut n K) with hCδ
  set Y := perfectCore Cδ with hY
  have hRM : R ≤ centralizer {dualAut n K} :=
    radicalImage_le_centralizer he hn3 i
  have hRinn := radicalImage_le_inner (K := K) he i
  have hR'C : R' ≤ Cδ := fun x hx =>
    (mem_autFixSubgroup_iff_conj_mem_centralizer hn3 _ x).2 (hRM hx)
  have hF2 : ∀ c ∈ Cδ, ∀ r ∈ R', c * r * c⁻¹ ∈ R' := by
    intro c hc r hr
    have hcM := (mem_autFixSubgroup_iff_conj_mem_centralizer hn3 _ c).1 hc
    have h1 := (radicalImage_normal (K := K) he hn3 i).conj_mem
      ⟨MulAut.conj r, hRM hr⟩ (mem_subgroupOf.2 hr) ⟨MulAut.conj c, hcM⟩
    rw [mem_subgroupOf] at h1
    change MulAut.conj (c * r * c⁻¹) ∈ R
    rw [map_mul, map_mul, map_inv]
    exact h1
  have hF3 : ∀ a ∈ R', ∀ b ∈ R', a * b = b * a := by
    intro a ha b hb
    obtain ⟨g, hg, hga⟩ := mem_map.1 (show MulAut.conj a ∈ R from ha)
    obtain ⟨h, hh, hhb⟩ := mem_map.1 (show MulAut.conj b ∈ R from hb)
    apply hconj
    rw [map_mul, map_mul, ← hga, ← hhb, ← map_mul, ← map_mul,
      radicalGroup_comm he hg hh]
  have hF4 : ∀ y ∈ Cδ, (∀ r ∈ R', y * r = r * y) → y ^ 2 = 1 := by
    intro y hy hyR
    have hyM := (mem_autFixSubgroup_iff_conj_mem_centralizer hn3 _ y).1 hy
    have hmem : MulAut.conj y ∈ centralizer {dualAut n K} ⊓ centralizer
        ((R : Subgroup (MulAut (projectiveSL n K))) : Set (MulAut (projectiveSL n K))) := by
      refine mem_inf.2 ⟨hyM, ?_⟩
      rw [mem_centralizer_iff]
      intro α hα
      obtain ⟨r, hr⟩ := hRinn hα
      have hrR' : r ∈ R' := by
        change MulAut.conj r ∈ R
        rw [hr]
        exact hα
      rw [← hr, ← map_mul, ← map_mul, hyR r hrR']
    have h1 := sq_eq_one_of_mem_centralizer_radicalImage he hn3 i hmem
    apply hconj
    rw [map_pow, h1, map_one]
  have hF5 : Cδ ≤ normalizer (Y : Set (projectiveSL n K)) :=
    le_normalizer.trans (CFSG.Quasithin.normalizer_le_normalizer_perfectCore Cδ)
  have hYC : Y ≤ Cδ := perfectCore_le Cδ
  have hYnc : ¬ ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a := fun h =>
    hXnc (forall_mul_comm_of_map_eq hφ₁ hXY h)
  set Q := Y ⊓ R' with hQ
  have hQY : Q ≤ Y := inf_le_left
  have hYQ : Y ≤ normalizer (Q : Set (projectiveSL n K)) := by
    intro y hy
    have hQconj : ∀ z ∈ Y, ∀ q ∈ Q, z * q * z⁻¹ ∈ Q := fun z hz q hq =>
      mem_inf.2 ⟨mul_mem (mul_mem hz (mem_inf.1 hq).1) (inv_mem hz),
        hF2 z (hYC hz) q (mem_inf.1 hq).2⟩
    rw [mem_normalizer_iff]
    intro q
    refine ⟨fun hq => hQconj y hy q hq, fun hq => ?_⟩
    have h1 := hQconj y⁻¹ (inv_mem hy) _ hq
    rwa [inv_inv, show y⁻¹ * (y * q * y⁻¹) * y = q by group] at h1
  have hQ1 : Q ≠ ⊥ := by
    intro hQbot
    apply hYnc
    have hsq : ∀ y ∈ Y, y ^ 2 = 1 := by
      intro y hy
      refine hF4 y (hYC hy) fun r hr => ?_
      have hcomm : y * r * y⁻¹ * r⁻¹ ∈ Q := by
        refine mem_inf.2 ⟨?_, mul_mem (hF2 y (hYC hy) r hr) (inv_mem hr)⟩
        have h1 : r * y⁻¹ * r⁻¹ ∈ Y := ((mem_normalizer_iff.1 (hF5 (hR'C hr))) _).1 (inv_mem hy)
        have h2 : y * r * y⁻¹ * r⁻¹ = y * (r * y⁻¹ * r⁻¹) := by group
        rw [h2]
        exact mul_mem hy h1
      rw [hQbot, mem_bot] at hcomm
      calc y * r = y * r * y⁻¹ * r⁻¹ * (r * y) := by group
        _ = r * y := by rw [hcomm, one_mul]
    intro a ha b hb
    have ha2 := hsq a ha
    have hb2 := hsq b hb
    calc a * b = a * b * (b * a) * (b * a)⁻¹ := by group
      _ = (b * a)⁻¹ := by
        rw [show a * b * (b * a) = a * (b ^ 2) * a by rw [sq]; group, hb2, mul_one, ← sq, ha2,
          one_mul]
      _ = b * a := by
        rw [inv_eq_of_mul_eq_one_right (show (b * a) * (b * a) = 1 by
          rw [← sq]; exact hsq (b * a) (mul_mem hb ha))]
  have hQY' : Q ≠ Y := by
    intro hQeq
    apply hYnc
    intro a ha b hb
    have ha' : a ∈ R' := (mem_inf.1 (hQeq ▸ ha : a ∈ Q)).2
    have hb' : b ∈ R' := (mem_inf.1 (hQeq ▸ hb : b ∈ Q)).2
    exact hF3 a ha' b hb'
  exact false_of_map_eq_of_isSimpleGroup hφ₁ hφ₂ hX hXY hQY hYQ hQ1 hQY'

theorem map_ne_perfectCore_graph_of_sylow {f c : ℕ} (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n)
    (hc2 : c ^ 2 = Nat.card K) (hc1 : 1 < c) {X : Subgroup (projectiveSL n K)}
    (hX : HasSylowCard n K X c) (hXs : IsSimpleGroup X)
    (hXnc : ¬ ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) (A : GL (Fin n) K)
    (hβ : (conjAut n K A * dualAut n K) ^ 2 = 1) {Γ : Type*} [Group Γ]
    {φ₁ φ₂ : projectiveSL n K →* Γ} (hφ₁ : Function.Injective φ₁)
    (hφ₂ : Function.Injective φ₂) :
    X.map φ₁ ≠ (perfectCore (autFixSubgroup (conjAut n K A * dualAut n K))).map φ₂ := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h1
    · have h1 := Finite.one_lt_card (α := K)
      rw [hK, h0, pow_zero] at h1
      exact absurd h1 (lt_irrefl 1)
    · exact h1
  have hn3 : 3 ≤ n := by omega
  obtain ⟨-, ⟨H, C, -, hconj, hC⟩, -⟩ :=
    UnitaryHigher.even_linear_pure_graph_involution_normal_forms hf hK hn3 A hβ
  rw [hconj, perfectCore_autFixSubgroup_conj, Subgroup.map_map]
  have hi₂ : Function.Injective (φ₂.comp (conjAut n K H).toMonoidHom) :=
    hφ₂.comp (conjAut n K H).injective
  rcases hC with ⟨hC1, -⟩ | ⟨r, hr, hJ, -⟩
  · have hC1' : C = 1 := Units.ext (by rw [hC1, Units.val_one])
    rw [hC1', map_one, one_mul]
    rcases Nat.even_or_odd n with he | ⟨r, hr⟩
    · exact map_ne_perfectCore_dualAut_of_even_of_isSimpleGroup hK hn he hXs hXnc hφ₁ hi₂
    · exact map_ne_perfectCore_dualAut_of_odd_of_sylow hK hr (by omega) hc2 hX hφ₁ hi₂
  · exact map_ne_perfectCore_blockSwap_of_sylow hK hn hr hc2 hc1 hX C hJ hφ₁ hi₂

end CFSG.SeitzReduction.LinearPilot
