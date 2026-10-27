module

public import CFSG.CGT.PushingUpLit.BHS5.AmbientFamily

public section

namespace CFSG.CGT.PushingUpLit.BHS5

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.Open
  CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {Γ : Type} [Group Γ] {V : Subgroup Γ}

theorem mem_liftSub_iff {A : Subgroup Γ} {Y : Subgroup (MulAut ↥V)} {g : Γ} :
    g ∈ liftSub V A Y ↔ g ∈ A ∧ ∃ hg : g ∈ Subgroup.normalizer (V : Set Γ),
      conjAct V ⟨g, hg⟩ ∈ Y := by
  constructor
  · rintro ⟨hgA, x, hxY, rfl⟩
    exact ⟨hgA, x.2, hxY⟩
  · rintro ⟨hgA, hg, hY⟩
    exact ⟨hgA, ⟨g, hg⟩, hY, rfl⟩

theorem autOn_conjSub {t : Γ} (ht : t ∈ Subgroup.normalizer (V : Set Γ)) {X : Subgroup Γ} :
    autOn (conjSub t X) V = conjSub (conjAct V ⟨t, ht⟩) (autOn X V) := by
  ext y
  rw [mem_autOn_iff, mem_conjSub_iff, mem_autOn_iff]
  constructor
  · rintro ⟨a, haX, rfl⟩
    refine ⟨⟨t⁻¹ * a * t, Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ ht) a.2) ht⟩,
      mem_conjSub_iff.1 haX, ?_⟩
    rw [show (⟨t⁻¹ * (a : Γ) * t, _⟩ : ↥(Subgroup.normalizer (V : Set Γ))) =
      ⟨t, ht⟩⁻¹ * a * ⟨t, ht⟩ from rfl, map_mul, map_mul, map_inv]
  · rintro ⟨b, hbX, hb⟩
    refine ⟨⟨t * b * t⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ ht b.2)
      (Subgroup.inv_mem _ ht)⟩, mem_conjSub_of_mem hbX, ?_⟩
    have : conjAct V b = (conjAct V ⟨t, ht⟩)⁻¹ * y * conjAct V ⟨t, ht⟩ := hb
    rw [show (⟨t * (b : Γ) * t⁻¹, _⟩ : ↥(Subgroup.normalizer (V : Set Γ))) =
      ⟨t, ht⟩ * b * ⟨t, ht⟩⁻¹ from rfl, map_mul, map_mul, map_inv, this]
    group

theorem liftSub_conjSub {t : Γ} (ht : t ∈ Subgroup.normalizer (V : Set Γ)) {A : Subgroup Γ}
    (htA : t ∈ A) (Y : Subgroup (MulAut ↥V)) :
    conjSub t (liftSub V A Y) = liftSub V A (conjSub (conjAct V ⟨t, ht⟩) Y) := by
  ext g
  rw [mem_conjSub_iff, mem_liftSub_iff, mem_liftSub_iff]
  constructor
  · rintro ⟨hgA, hg, hY⟩
    have hgA' : g ∈ A := by
      have := A.mul_mem (A.mul_mem htA hgA) (A.inv_mem htA)
      simpa [mul_assoc] using this
    have hgN : g ∈ Subgroup.normalizer (V : Set Γ) := by
      have := Subgroup.mul_mem _ (Subgroup.mul_mem _ ht hg) (Subgroup.inv_mem _ ht)
      simpa [mul_assoc] using this
    refine ⟨hgA', hgN, mem_conjSub_iff.2 ?_⟩
    have h1 : conjAct V ⟨t⁻¹ * g * t, hg⟩ =
        (conjAct V ⟨t, ht⟩)⁻¹ * conjAct V ⟨g, hgN⟩ * conjAct V ⟨t, ht⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [← h1]
    exact hY
  · rintro ⟨hgA, hgN, hY⟩
    have hg : t⁻¹ * g * t ∈ Subgroup.normalizer (V : Set Γ) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ ht) hgN) ht
    refine ⟨A.mul_mem (A.mul_mem (A.inv_mem htA) hgA) htA, hg, ?_⟩
    have h1 : conjAct V ⟨t⁻¹ * g * t, hg⟩ =
        (conjAct V ⟨t, ht⟩)⁻¹ * conjAct V ⟨g, hgN⟩ * conjAct V ⟨t, ht⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [h1]
    exact mem_conjSub_iff.1 hY

theorem mem_fixV_autOn_iff (hV : IsElemAbelian 2 V) {E : Subgroup Γ}
    (hE : E ≤ Subgroup.normalizer (V : Set Γ)) (u : ↥V) :
    u ∈ @fixV ↥V (commGroupOfElemAbelian hV) (autOn E V) ↔
      (u : Γ) ∈ Subgroup.centralizer (E : Set Γ) := by
  constructor
  · intro h
    refine Subgroup.mem_centralizer_iff.2 fun g hg => ?_
    have h1 := congrArg (fun w : ↥V => (w : Γ)) (h (conjAct V ⟨g, hE hg⟩)
      (mem_autOn_iff.2 ⟨⟨g, hE hg⟩, hg, rfl⟩))
    simp only [conjAct_apply'] at h1
    calc g * u = (g * u * g⁻¹) * g := by group
      _ = u * g := by rw [h1]
  · intro h σ hσ
    obtain ⟨a, haE, rfl⟩ := mem_autOn_iff.1 hσ
    apply Subtype.ext
    rw [conjAct_apply']
    have := Subgroup.mem_centralizer_iff.1 h a haE
    calc (a : Γ) * u * (a : Γ)⁻¹ = u * (a : Γ) * (a : Γ)⁻¹ := by rw [this]
      _ = u := by group

theorem map_commV_autOn (hV : IsElemAbelian 2 V) {E : Subgroup Γ}
    (hE : E ≤ Subgroup.normalizer (V : Set Γ)) :
    (@commV ↥V (commGroupOfElemAbelian hV) (autOn E V)).map V.subtype = ⁅V, E⁆ := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hV
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap, commV, Subgroup.closure_le]
    rintro _ ⟨σ, hσ, v, rfl⟩
    obtain ⟨g, hgL, rfl⟩ := mem_autOn_iff.1 hσ
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    show ((conjAct V g v * v⁻¹ : ↥V) : Γ) ∈ ⁅V, E⁆
    rw [Subgroup.coe_mul, conjAct_apply', Subgroup.coe_inv]
    have e : (g : Γ) * v * (g : Γ)⁻¹ * (v : Γ)⁻¹ = ⁅(v : Γ), (g : Γ)⁆⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact (⁅V, E⁆).inv_mem (Subgroup.commutator_mem_commutator v.2 hgL)
  · rw [Subgroup.commutator_le]
    intro w hw l hl
    have hmem : conjAct V ⟨l, hE hl⟩ ⟨w, hw⟩ * (⟨w, hw⟩ : ↥V)⁻¹ ∈
        @commV ↥V (commGroupOfElemAbelian hV) (autOn E V) :=
      Subgroup.subset_closure ⟨_, mem_autOn_iff.2 ⟨⟨l, hE hl⟩, hl, rfl⟩, ⟨w, hw⟩, rfl⟩
    refine ⟨(conjAct V ⟨l, hE hl⟩ ⟨w, hw⟩ * (⟨w, hw⟩ : ↥V)⁻¹)⁻¹,
      Subgroup.inv_mem _ hmem, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_inv, Subgroup.coe_mul, conjAct_apply']
    rw [commutatorElement_def]
    group

end CFSG.CGT.PushingUpLit.BHS5
