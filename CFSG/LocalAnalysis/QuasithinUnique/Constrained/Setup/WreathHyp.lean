module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellElem
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathBase
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Quasithin.Background.B2Thompson

public section

namespace CFSG.QuasithinUnique.Setup.Wreath

open scoped Pointwise commutatorElement
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell

structure WreathHyp {H : Type*} [Group H] (R M V W F : Subgroup H) {r : ℕ}
    (I : Fin r → Subgroup H) (Pm : Subgroup (Equiv.Perm (Fin r))) : Prop where
  sylow : IsSylowTwoOf R (⊤ : Subgroup H)
  nonnormal : ¬ R.Normal
  le_M : R ≤ M
  M_lt : M < ⊤
  M_max : ∀ Y : Subgroup H, R ≤ Y → Y < ⊤ → Y ≤ M
  J_not_le_centralizer : ¬ thompsonJ R ≤ Subgroup.centralizer (V : Set H)
  reduced : IsTwoReducedIn (⊤ : Subgroup H) V
  W_le : W ≤ V
  F_le : F ≤ V
  W_normal : W.Normal
  F_normal : F.Normal
  W_sup_F : W ⊔ F = V
  W_inf_F : W ⊓ F = ⊥
  r_pos : 1 ≤ r
  I_le : ∀ i, I i ≤ W
  I_card : ∀ i, Nat.card ↥(I i) = 4
  I_indep : iSupIndep I
  I_sup : ⨆ i, I i = W
  Pm_two : IsPGroup 2 ↥Pm
  Pm_trans : ∀ i j, ∃ σ ∈ Pm, σ i = j
  image_le : ∀ x : H, ∃ σ ∈ Pm, ∀ i, (I i).map (MulAut.conj x).toMonoidHom = I (σ i)
  image_ge : ∀ (g : ↥W ≃* ↥W) (σ : Equiv.Perm (Fin r)), σ ∈ Pm →
    (∀ i, ∀ w : ↥W, ((g w : ↥W) : H) ∈ I (σ i) ↔ (w : H) ∈ I i) →
    ∃ x : H, ∀ w : ↥W, ((g w : ↥W) : H) = x * w * x⁻¹
  centralizes : ∀ x : H, (∀ i, (I i).map (MulAut.conj x).toMonoidHom = I i) →
    ∀ f ∈ F, x * f = f * x

@[expose] def planesIn {H : Type*} [Group H] (W : Subgroup H) {r : ℕ} (I : Fin r → Subgroup H)
    (i : Fin r) : Subgroup ↥W := (I i).subgroupOf W

theorem mem_planesIn_iff {H : Type*} [Group H] {W : Subgroup H} {r : ℕ} {I : Fin r → Subgroup H}
    {i : Fin r} {w : ↥W} : w ∈ planesIn W I i ↔ (w : H) ∈ I i := Iff.rfl

namespace WreathHyp

variable {H : Type*} [Group H] {R M V W F : Subgroup H} {r : ℕ} {I : Fin r → Subgroup H}
  {Pm : Subgroup (Equiv.Perm (Fin r))} (h : WreathHyp R M V W F I Pm)

include h

theorem V_elem : CFSG.Open.IsElemAbelian 2 V := h.reduced.2.2.1

theorem W_elem : CFSG.Open.IsElemAbelian 2 W := isElemAbelian_mono h.V_elem h.W_le

theorem V_normal : V.Normal :=
  Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp h.reduced.2.1)

@[expose, reducible] def cg : CommGroup ↥W := commGroupOfElemAbelian h.W_elem

theorem map_planes (i : Fin r) : (planesIn W I i).map W.subtype = I i :=
  Subgroup.map_subgroupOf_eq_of_le (h.I_le i)

theorem card_planes (i : Fin r) : Nat.card ↥(planesIn W I i) = 4 := by
  rw [← h.I_card i]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (h.I_le i)).toEquiv

theorem isKleinFour_planes (i : Fin r) : IsKleinFour ↥(planesIn W I i) := by
  refine ⟨h.card_planes i, ?_⟩
  have hfin : Finite ↥(planesIn W I i) :=
    Nat.finite_of_card_ne_zero (by rw [h.card_planes i]; norm_num)
  have hnt : Nontrivial ↥(planesIn W I i) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [h.card_planes i]; norm_num)
  rw [Monoid.exponent_eq_prime_iff Nat.prime_two]
  intro g hg
  refine orderOf_eq_prime ?_ hg
  apply Subtype.ext
  apply Subtype.ext
  simpa using h.W_elem.2 (((g : ↥W) : H)) (g : ↥W).2

theorem planeFamily : @PlaneFamily ↥W h.cg (Fin r) (planesIn W I) :=
  letI := h.cg
  { exp_two := fun w => by
      apply Subtype.ext
      have := h.W_elem.2 w w.2
      simpa [pow_two] using this
    klein := fun i => h.isKleinFour_planes i
    indep := by
      intro i
      rw [disjoint_iff, eq_bot_iff]
      intro x hx
      obtain ⟨hx1, hx2⟩ := hx
      have h1 : (x : H) ∈ I i := hx1
      have h2 : (x : H) ∈ ⨆ j, ⨆ (_ : j ≠ i), I j := by
        have : (x : H) ∈ (⨆ j, ⨆ (_ : j ≠ i), planesIn W I j).map W.subtype := ⟨x, hx2, rfl⟩
        rw [Subgroup.map_iSup] at this
        simp only [Subgroup.map_iSup, h.map_planes] at this
        exact this
      have h3 : (x : H) ∈ I i ⊓ ⨆ j, ⨆ (_ : j ≠ i), I j := ⟨h1, h2⟩
      have h4 := (disjoint_iff.mp (h.I_indep i)) ▸ h3
      have : (x : H) = 1 := (Subgroup.mem_bot.mp h4)
      exact Subgroup.mem_bot.mpr (Subtype.ext this)
    sup_eq_top := by
      apply Subgroup.map_injective W.subtype_injective
      rw [Subgroup.map_iSup, Subgroup.map_top, Subgroup.range_subtype]
      simp only [h.map_planes]
      exact h.I_sup }

@[expose] def rho : H →* MulAut ↥W :=
  have := h.W_normal
  MulAut.conjNormal

theorem rho_apply (x : H) (w : ↥W) : ((h.rho x w : ↥W) : H) = x * w * x⁻¹ := by
  have := h.W_normal
  exact MulAut.conjNormal_apply x w

omit h in
theorem smul_planes_iff {W : Subgroup H} {I : Fin r → Subgroup H} (g : MulAut ↥W) (i j : Fin r) :
    g • planesIn W I i = planesIn W I j ↔
      ∀ w : ↥W, ((g w : ↥W) : H) ∈ I j ↔ (w : H) ∈ I i := by
  constructor
  · intro hg w
    constructor
    · intro hw
      have hw' : g w ∈ g • planesIn W I i := by rw [hg]; exact hw
      obtain ⟨b, hb, hbw⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp hw'
      have : b = w := g.injective hbw
      rw [this] at hb
      exact hb
    · intro hw
      have : g w ∈ g • planesIn W I i :=
        (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨w, hw, rfl⟩
      rw [hg] at this
      exact this
  · intro hcond
    ext z
    rw [Subgroup.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact (hcond b).mpr hb
    · intro hz
      refine ⟨g⁻¹ z, ?_, by simp⟩
      have hz' : ((g (g⁻¹ z) : ↥W) : H) ∈ I j := by simpa [mem_planesIn_iff] using hz
      exact (hcond (g⁻¹ z)).mp hz'

omit h in
theorem mem_map_conj_iff {K : Subgroup H} {x y : H} :
    x * y * x⁻¹ ∈ K.map (MulAut.conj x).toMonoidHom ↔ y ∈ K :=
  Subgroup.mem_map_iff_mem (f := (MulAut.conj x).toMonoidHom) (MulAut.conj x).injective

theorem image_le' (x : H) : ∃ σ ∈ Pm, ∀ i, h.rho x • planesIn W I i = planesIn W I (σ i) := by
  obtain ⟨σ, hσ, hx⟩ := h.image_le x
  refine ⟨σ, hσ, fun i => (smul_planes_iff (h.rho x) i (σ i)).mpr fun w => ?_⟩
  rw [h.rho_apply, ← hx i]
  exact mem_map_conj_iff

theorem rho_range : h.rho.range = @wreathAut ↥W h.cg (Fin r) (planesIn W I) _ h.planeFamily Pm := by
  let _ := h.cg
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨σ, hσ, hx⟩ := h.image_le' x
    exact (mem_wreathAut_iff h.planeFamily).mpr ⟨σ, hσ, hx⟩
  · intro hg
    obtain ⟨σ, hσ, hg'⟩ := (mem_wreathAut_iff h.planeFamily).mp hg
    obtain ⟨x, hx⟩ := h.image_ge g σ hσ fun i w => (smul_planes_iff g i (σ i)).mp (hg' i) w
    exact ⟨x, MulEquiv.ext fun w => Subtype.ext (by rw [h.rho_apply, ← hx w])⟩

end WreathHyp

end CFSG.QuasithinUnique.Setup.Wreath
