module

public import CFSG.CGT.PushingUpLit.CGT6.EmbDictBase
public import CFSG.CGT.PushingUpLit.CGT6.EmbDictXfer

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

theorem mult_trivial_of_perfect {Γ : Type*} [Group Γ] [Group.IsPerfect Γ] {M : Type*}
    [Group M] [IsMulCommutative M] (χ : Γ → M) (hχ : ∀ g h, χ (g * h) = χ g * χ h) :
    ∀ g, χ g = 1 := by
  let f : Γ →* M := MonoidHom.mk' χ hχ
  have : Group.IsPerfect f.range := Group.IsPerfect.range f
  have : Subsingleton f.range := inferInstance
  intro s
  have h : (⟨f s, s, rfl⟩ : f.range) = 1 := Subsingleton.elim _ _
  exact congrArg Subtype.val h

theorem trivial_of_unipotent {V : Type*} [CommGroup V] {Γ : Type*} [Group Γ] [Group.IsPerfect Γ]
    (ρ : Γ →* MulAut V) (A : Subgroup V) (hA : ∀ g, ∀ a ∈ A, ρ g a = a)
    (hU : ∀ g v, ρ g v * v⁻¹ ∈ A) : ∀ g v, ρ g v = v := by
  intro g v
  have key := mult_trivial_of_perfect (fun g => ρ g v * v⁻¹) (fun g h => by
    have h1 : ρ (g * h) v = ρ g (ρ h v) := by rw [map_mul]; rfl
    have h2 : ρ h v = (ρ h v * v⁻¹) * v := by group
    show ρ (g * h) v * v⁻¹ = (ρ g v * v⁻¹) * (ρ h v * v⁻¹)
    rw [h1]
    conv_lhs => rw [h2]
    rw [map_mul, hA g _ (hU h v)]
    ac_rfl) g
  exact mul_inv_eq_one.mp key

section Yu

variable {V : Type} [CommGroup V] (Y : Subgroup (MulAut V))

theorem commV_mem_of_apply (g : ↥Y) (v : V) : (g : MulAut V) v * v⁻¹ ∈ commV Y :=
  Subgroup.subset_closure ⟨g, g.2, v, rfl⟩

theorem yuInc_range_le_pCore (hV : ∀ v : V, v ^ 2 = 1) :
    (yuInc Y).range ≤ pCore 2 ↥(yuHol Y) := by
  apply le_sSup
  refine ⟨?_, ?_⟩
  · rw [← ker_yuProj]; infer_instance
  · intro x
    obtain ⟨u, hu⟩ := x.2
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hu]
    simpa using yuInc_sq Y hV u

theorem commV_le_of_perfect [Group.IsPerfect ↥Y] (N₁ : Subgroup V)
    (hN : ∀ (g : ↥Y) (u : ↥(commV Y)), (g : MulAut V) (u : V) * (u : V)⁻¹ ∈ N₁) :
    commV Y ≤ N₁ := by
  classical
  let N₀ : Subgroup ↥(commV Y) := N₁.subgroupOf (commV Y)
  have hgen : ∀ (g : ↥Y) (v : V),
      (⟨(g : MulAut V) v * v⁻¹, commV_mem_of_apply Y g v⟩ : ↥(commV Y)) ∈ N₀ := by
    intro g v
    let f : ↥Y → ↥(commV Y) ⧸ N₀ := fun g =>
      QuotientGroup.mk ⟨(g : MulAut V) v * v⁻¹, commV_mem_of_apply Y g v⟩
    have hf : ∀ g h, f (g * h) = f g * f h := by
      intro g h
      let w : ↥(commV Y) := ⟨(h : MulAut V) v * v⁻¹, commV_mem_of_apply Y h v⟩
      let u₁ : ↥(commV Y) := ⟨(g : MulAut V) (w : V) * (w : V)⁻¹, commV_mem_of_apply Y g (w : V)⟩
      have hu₁ : u₁ ∈ N₀ := hN g w
      have hprod : (⟨((g * h : ↥Y) : MulAut V) v * v⁻¹, commV_mem_of_apply Y (g * h) v⟩ :
          ↥(commV Y)) = u₁ * w * ⟨(g : MulAut V) v * v⁻¹, commV_mem_of_apply Y g v⟩ := by
        apply Subtype.ext
        show ((g * h : ↥Y) : MulAut V) v * v⁻¹ = ((g : MulAut V) ((h : MulAut V) v * v⁻¹) *
          ((h : MulAut V) v * v⁻¹)⁻¹) * ((h : MulAut V) v * v⁻¹) * ((g : MulAut V) v * v⁻¹)
        rw [Subgroup.coe_mul, MulAut.mul_apply, map_mul, map_inv]
        group
      show QuotientGroup.mk _ = QuotientGroup.mk _ * QuotientGroup.mk _
      rw [hprod, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        (QuotientGroup.eq_one_iff u₁).mpr hu₁, one_mul]
      exact mul_comm _ _
    have := mult_trivial_of_perfect f hf g
    exact (QuotientGroup.eq_one_iff _).mp this
  unfold commV
  rw [Subgroup.closure_le]
  rintro _ ⟨g, hg, v, rfl⟩
  exact hgen ⟨g, hg⟩ v

theorem yuInc_mem_shortU [Finite V] [Group.IsPerfect ↥Y] (hV : ∀ v : V, v ^ 2 = 1)
    (u : ↥(commV Y)) : yuInc Y u ∈ shortU ↥(yuHol Y) := by
  let N₁ : Subgroup V := ((shortU ↥(yuHol Y)).comap (yuInc Y)).map (commV Y).subtype
  have hN : ∀ (g : ↥Y) (w : ↥(commV Y)), (g : MulAut V) (w : V) * (w : V)⁻¹ ∈ N₁ := by
    intro g w
    refine ⟨⟨(g : MulAut V) (w : V) * (w : V)⁻¹, commV_mem_of_apply Y g (w : V)⟩, ?_, rfl⟩
    have hc := comm_yuInc_yuSec Y g w⁻¹
    have hmem : ⁅yuInc Y w⁻¹, yuSec Y g⁆ ∈ shortU ↥(yuHol Y) :=
      Subgroup.commutator_mem_commutator (yuInc_range_le_pCore Y hV ⟨w⁻¹, rfl⟩)
        (Subgroup.mem_top _)
    rw [hc] at hmem
    have : (⟨((w⁻¹ : ↥(commV Y)) : V) * (g : MulAut V) (((w⁻¹ : ↥(commV Y)) : V))⁻¹,
        mul_mem (w⁻¹).2 (apply_mem_commV_self Y g.2 (inv_mem (w⁻¹).2))⟩ : ↥(commV Y)) =
        ⟨(g : MulAut V) (w : V) * (w : V)⁻¹, commV_mem_of_apply Y g (w : V)⟩ := by
      apply Subtype.ext
      show (w : V)⁻¹ * (g : MulAut V) (w : V)⁻¹⁻¹ = (g : MulAut V) (w : V) * (w : V)⁻¹
      rw [inv_inv, mul_comm]
    rw [this] at hmem
    exact hmem
  obtain ⟨u', hu', hu'u⟩ := commV_le_of_perfect Y N₁ hN u.2
  have : u' = u := Subtype.ext hu'u
  rw [← this]
  exact hu'

theorem apply_eq_of_yuInc_mem_center {g : ↥Y} {u : ↥(commV Y)}
    (h : yuInc Y u ∈ Subgroup.center ↥(yuHol Y)) : (g : MulAut V) (u : V) = u := by
  have h1 := conj_yuInc Y (yuSec Y g) u
  rw [Subgroup.mem_center_iff.mp h (yuSec Y g)] at h1
  rw [mul_assoc, mul_inv_cancel, mul_one] at h1
  exact (congrArg Subtype.val (yuInc_injective Y h1)).symm


theorem shortU_eq_sup [Finite V] [Group.IsPerfect ↥Y] (hV : ∀ v : V, v ^ 2 = 1)
    (hX : IsShortGroup ↥(yuHol Y)) :
    shortU ↥(yuHol Y) = (yuInc Y).range ⊔ shortC ↥(yuHol Y) := by
  have hUL : (yuInc Y).range ≤ shortU ↥(yuHol Y) := fun x ⟨u, hu⟩ => hu ▸ yuInc_mem_shortU Y hV u
  have hN : ((yuInc Y).range ⊔ shortC ↥(yuHol Y)).Normal := by
    have h1 : (yuInc Y).range.Normal := by rw [← ker_yuProj]; infer_instance
    have h2 : (shortC ↥(yuHol Y)).Normal :=
      inferInstanceAs (shortU ↥(yuHol Y) ⊓ Subgroup.center ↥(yuHol Y)).Normal
    infer_instance
  rcases hX.irreducible _ hN (sup_le hUL shortC_le_shortU) le_sup_right with h | h
  · exfalso
    have hUc : (yuInc Y).range ≤ shortC ↥(yuHol Y) := le_sup_left.trans h.le
    have hcent : ∀ u : ↥(commV Y), yuInc Y u ∈ Subgroup.center ↥(yuHol Y) := fun u =>
      (hUc ⟨u, rfl⟩).2
    have hfix : ∀ (g : ↥Y) (v : V), (g : MulAut V) v = v := by
      refine trivial_of_unipotent Y.subtype (commV Y) (fun g a ha => ?_)
        (fun g v => commV_mem_of_apply Y g v)
      exact apply_eq_of_yuInc_mem_center Y (hcent ⟨a, ha⟩)
    have hY1 : ∀ g : ↥Y, (g : MulAut V) = 1 := fun g => MulEquiv.ext (hfix g)
    have htop : (⊤ : Subgroup ↥(yuHol Y)) ≤ (yuInc Y).range := by
      intro x _
      rw [← ker_yuProj, mem_ker_yuProj]
      exact hY1 ⟨x.1.right, x.2.2⟩
    exact absurd (lt_of_lt_of_le hX.nonzero ((le_top.trans htop).trans hUc)) (lt_irrefl _)
  · exact h.symm


section Theta


variable {A : Type*} [Group A]
  (φ : (↥(yuHol Y) ⧸ pCore 2 ↥(yuHol Y)) ≃* A)

@[expose] def yuTheta : ↥Y →* A :=
  φ.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 ↥(yuHol Y))).comp (yuSec Y))

theorem yuTheta_apply (y : ↥Y) :
    yuTheta Y φ y = φ (QuotientGroup.mk (yuSec Y y)) := rfl

theorem yuTheta_eq_one_iff (y : ↥Y) : yuTheta Y φ y = 1 ↔ yuSec Y y ∈ pCore 2 ↥(yuHol Y) := by
  rw [yuTheta_apply, ← map_one φ, φ.injective.eq_iff, QuotientGroup.eq_one_iff]

theorem yuTheta_surjective (hV : ∀ v : V, v ^ 2 = 1) : Function.Surjective (yuTheta Y φ) := by
  intro a
  obtain ⟨q, hq⟩ := φ.surjective a
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨yuProj Y x, ?_⟩
  rw [yuTheta_apply, ← hq]
  congr 1
  rw [QuotientGroup.eq]
  have h1 := yu_eq_inc_mul_sec Y x
  have h2 : yuSec Y (yuProj Y x) = (yuInc Y ⟨x.1.left, x.2.1⟩)⁻¹ * x := by
    rw [eq_inv_mul_iff_mul_eq]
    exact h1.symm
  rw [h2]
  have ha := yuInc_range_le_pCore Y hV (⟨⟨x.1.left, x.2.1⟩, rfl⟩ : _ ∈ (yuInc Y).range)
  have hc := (pCore_normal (p := 2) (G := ↥(yuHol Y))).conj_mem _ ha x⁻¹
  simpa [mul_assoc] using hc

theorem yuTheta_ker_eq : (yuTheta Y φ).ker = (pCore 2 ↥(yuHol Y)).comap (yuSec Y) := by
  ext y
  rw [MonoidHom.mem_ker, yuTheta_eq_one_iff, Subgroup.mem_comap]

theorem yuTheta_ker_isPGroup : IsPGroup 2 ↥(yuTheta Y φ).ker := by
  rw [yuTheta_ker_eq]
  exact pCore_isPGroup.comap_of_injective (yuSec Y) (yuSec_injective Y)

theorem yuTheta_ker_le_center [Finite V] [Group.IsPerfect ↥Y] (hV : ∀ v : V, v ^ 2 = 1)
    (hX : IsShortGroup ↥(yuHol Y)) : (yuTheta Y φ).ker ≤ Subgroup.center ↥Y := by
  intro r hr
  have hrp : yuSec Y r ∈ pCore 2 ↥(yuHol Y) := (yuTheta_eq_one_iff Y φ r).mp hr
  have ha : ∀ y : ↥Y, ⁅r, y⁆ ∈ Subgroup.center ↥Y := by
    intro y
    have h1 : ⁅yuSec Y r, yuSec Y y⁆ ∈ shortU ↥(yuHol Y) :=
      Subgroup.commutator_mem_commutator hrp (Subgroup.mem_top _)
    rw [shortU_eq_sup Y hV hX] at h1
    have h2 : yuProj Y ⁅yuSec Y r, yuSec Y y⁆ ∈
        ((yuInc Y).range ⊔ shortC ↥(yuHol Y)).map (yuProj Y) := Subgroup.mem_map_of_mem _ h1
    have h3 : ((yuInc Y).range ⊔ shortC ↥(yuHol Y)).map (yuProj Y) ≤ Subgroup.center ↥Y := by
      rw [Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨x, ⟨u, rfl⟩, rfl⟩
        simp
      · rintro _ ⟨c, hc, rfl⟩
        rw [Subgroup.mem_center_iff]
        intro y
        obtain ⟨x, rfl⟩ := yuProj_surjective Y y
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hc.2 x]
    have h4 := h3 h2
    rwa [map_commutatorElement, yuProj_sec, yuProj_sec] at h4
  have key := mult_trivial_of_perfect (M := ↥(Subgroup.center ↥Y))
    (fun y : ↥Y => (⟨⁅r, y⁆, ha y⟩ : ↥(Subgroup.center ↥Y))) (fun y y' => by
      apply Subtype.ext
      rw [Subgroup.coe_mul]
      show ⁅r, y * y'⁆ = ⁅r, y⁆ * ⁅r, y'⁆
      have hc := Subgroup.mem_center_iff.mp (ha y') y
      simp only [commutatorElement_def] at hc ⊢
      calc r * (y * y') * r⁻¹ * (y * y')⁻¹
          = (r * y * r⁻¹ * y⁻¹) * (y * (r * y' * r⁻¹ * y'⁻¹) * y⁻¹) := by group
        _ = (r * y * r⁻¹ * y⁻¹) * (r * y' * r⁻¹ * y'⁻¹) := by
          rw [hc]
          group)
  rw [Subgroup.mem_center_iff]
  intro y
  have := congrArg Subtype.val (key y)
  have h5 : ⁅r, y⁆ = 1 := this
  rw [commutatorElement_def, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h5
  exact h5.symm

theorem yuTheta_ker_fixes [Finite V] [Group.IsPerfect ↥Y] (hV : ∀ v : V, v ^ 2 = 1)
    (hX : IsShortGroup ↥(yuHol Y)) {r : ↥Y} (hr : r ∈ (yuTheta Y φ).ker) (u : ↥(commV Y)) :
    (r : MulAut V) (u : V) = u := by
  have hrp : yuSec Y r ∈ pCore 2 ↥(yuHol Y) := (yuTheta_eq_one_iff Y φ r).mp hr
  have hu : yuInc Y u ∈ shortU ↥(yuHol Y) := yuInc_mem_shortU Y hV u
  obtain ⟨c, hc, hcu⟩ := hX.U_le_center hu
  have h1 := Subgroup.mem_center_iff.mp hc ⟨yuSec Y r, hrp⟩
  have h2 : yuSec Y r * yuInc Y u = yuInc Y u * yuSec Y r := by
    have := congrArg Subtype.val h1
    simpa [← hcu] using this
  have h3 := conj_yuInc Y (yuSec Y r) u
  rw [h2, mul_assoc, mul_inv_cancel, mul_one] at h3
  exact (congrArg Subtype.val (yuInc_injective Y h3)).symm

include φ in
theorem shortU_eq_range [Finite V] [Group.IsPerfect ↥Y] (hV : ∀ v : V, v ^ 2 = 1)
    (hX : IsShortGroup ↥(yuHol Y)) : shortU ↥(yuHol Y) = (yuInc Y).range := by
  refine le_antisymm ?_ (fun x ⟨u, hu⟩ => hu ▸ yuInc_mem_shortU Y hV u)
  have hRc := yuTheta_ker_le_center Y φ hV hX
  have : ((yuInc Y).range).Normal := by rw [← ker_yuProj]; infer_instance
  unfold shortU
  rw [Subgroup.commutator_le]
  intro q hq x _
  have hyq : yuProj Y q ∈ (yuTheta Y φ).ker := by
    rw [MonoidHom.mem_ker, yuTheta_eq_one_iff]
    have h1 := yu_eq_inc_mul_sec Y q
    have h2 : yuSec Y (yuProj Y q) = (yuInc Y ⟨q.1.left, q.2.1⟩)⁻¹ * q := by
      rw [eq_inv_mul_iff_mul_eq]
      exact h1.symm
    rw [h2]
    exact mul_mem (inv_mem (yuInc_range_le_pCore Y hV ⟨_, rfl⟩)) hq
  rw [← ker_yuProj] at *
  rw [MonoidHom.mem_ker, map_commutatorElement]
  have := Subgroup.mem_center_iff.mp (hRc hyq) (yuProj Y x)
  rw [commutatorElement_def]
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
  exact this.symm

theorem yuTheta_center_le_ker (hV : ∀ v : V, v ^ 2 = 1) (hA : Subgroup.center A = ⊥) :
    Subgroup.center ↥Y ≤ (yuTheta Y φ).ker := by
  intro z hz
  rw [MonoidHom.mem_ker]
  have : yuTheta Y φ z ∈ Subgroup.center A := by
    rw [Subgroup.mem_center_iff]
    intro a
    obtain ⟨y, rfl⟩ := yuTheta_surjective Y φ hV a
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz y]
  rw [hA] at this
  exact this

end Theta

end Yu

end CFSG.CGT.PushingUpLit.CGT6
