module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalURigidStab

public section

namespace CFSG.ComponentClassification.RankTwoClassical.URigid

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

variable {K : Type} [Field K] [CharP K 2] {ε f : ℕ} (h : UnitaryFieldData 2 f K)

@[expose] def avecPre (S : AddSubgroup (Fin ε → K)) : Subgroup (stabE (ε := ε) h) where
  carrier := {x | x ∈ (zBlockHom h).ker ∧ avec h x ∈ S}
  mul_mem' := by
    rintro x y ⟨hx, hxS⟩ ⟨hy, hyS⟩
    exact ⟨mul_mem hx hy, by rw [avec_mul_of_mem_ker h hx]; exact add_mem hxS hyS⟩
  one_mem' := ⟨one_mem _, by rw [avec_one]; exact zero_mem _⟩
  inv_mem' := by
    rintro x ⟨hx, hxS⟩
    refine ⟨inv_mem hx, ?_⟩
    have hx1 : rmat h x⁻¹ = 1 := by
      rw [rmat, MonoidHom.mem_ker.mp (inv_mem hx)]
      rfl
    rw [avec_inv, hx1, one_mulVec]
    exact neg_mem hxS

theorem mem_avecPre {S : AddSubgroup (Fin ε → K)} {x : stabE (ε := ε) h} :
    x ∈ avecPre h S ↔ x ∈ (zBlockHom h).ker ∧ avec h x ∈ S := Iff.rfl

theorem tvSub_le_avecPre (S : AddSubgroup (Fin ε → K)) : tvSub (ε := ε) h ≤ avecPre h S := by
  rintro x ⟨hx, hx0⟩
  exact ⟨hx, by rw [hx0]; exact zero_mem _⟩

@[expose] def commSpace (H : Subgroup (stabE (ε := ε) h)) : AddSubgroup (Fin ε → K) :=
  AddSubgroup.closure {w | ∃ g ∈ H, ∃ v : Fin ε → K, w = v - rmat h g *ᵥ v}

theorem avec_commutatorElement {x : stabE (ε := ε) h} (hx : x ∈ (zBlockHom h).ker)
    (g : stabE (ε := ε) h) : avec h ⁅x, g⁆ = avec h x - rmat h g *ᵥ avec h x := by
  have hxi : x⁻¹ ∈ (zBlockHom h).ker := inv_mem hx
  have hconj : g * x⁻¹ * g⁻¹ ∈ (zBlockHom h).ker :=
    (zBlockHom h).normal_ker.conj_mem _ hxi g
  have hx1 : rmat h x⁻¹ = 1 := by
    rw [rmat, MonoidHom.mem_ker.mp hxi]
    rfl
  rw [commutatorElement_def, mul_assoc, mul_assoc, avec_mul_of_mem_ker h hx, ← mul_assoc,
    avec_conj h hxi, avec_inv, hx1, one_mulVec, mulVec_neg, sub_eq_add_neg]

theorem commutator_sup_tvSub_eq (H : Subgroup (stabE (ε := ε) h)) :
    ⁅(zBlockHom (ε := ε) h).ker, H⁆ ⊔ tvSub h = avecPre h (commSpace h H) := by
  apply le_antisymm
  · refine sup_le ?_ (tvSub_le_avecPre h _)
    rw [Subgroup.commutator_le]
    intro x hx g hg
    refine ⟨MonoidHom.mem_ker.mpr (by rw [map_commutatorElement, MonoidHom.mem_ker.mp hx,
      commutatorElement_one_left]), ?_⟩
    rw [avec_commutatorElement h hx]
    exact AddSubgroup.subset_closure ⟨g, hg, avec h x, rfl⟩
  · rintro x ⟨hx, hxS⟩
    obtain ⟨y, hy, hyx⟩ : ∃ y ∈ ⁅(zBlockHom (ε := ε) h).ker, H⁆, avec h y = avec h x := by
      have hle : ⁅(zBlockHom (ε := ε) h).ker, H⁆ ≤ (zBlockHom h).ker := by
        rw [Subgroup.commutator_le]
        intro x hx g _
        exact MonoidHom.mem_ker.mpr (by rw [map_commutatorElement, MonoidHom.mem_ker.mp hx,
          commutatorElement_one_left])
      refine AddSubgroup.closure_induction (p := fun w _ => ∃ y ∈ ⁅(zBlockHom (ε := ε) h).ker, H⁆,
        avec h y = w) ?_ ?_ ?_ ?_ hxS
      · rintro _ ⟨g, hg, v, rfl⟩
        obtain ⟨z, hz, hzv⟩ := exists_mem_ker_avec_eq h v
        exact ⟨⁅z, g⁆, Subgroup.commutator_mem_commutator hz hg,
          by rw [avec_commutatorElement h hz, hzv]⟩
      · exact ⟨1, one_mem _, avec_one h⟩
      · rintro _ _ _ _ ⟨y₁, hy₁, rfl⟩ ⟨y₂, hy₂, rfl⟩
        exact ⟨y₁ * y₂, mul_mem hy₁ hy₂, avec_mul_of_mem_ker h (hle hy₁) _⟩
      · rintro _ _ ⟨y₁, hy₁, rfl⟩
        refine ⟨y₁⁻¹, inv_mem hy₁, ?_⟩
        have hy1 : rmat h y₁⁻¹ = 1 := by
          rw [rmat, MonoidHom.mem_ker.mp (inv_mem (hle hy₁))]
          rfl
        rw [avec_inv, hy1, one_mulVec]
    have hyker : y ∈ (zBlockHom h).ker := by
      have hle : ⁅(zBlockHom (ε := ε) h).ker, H⁆ ≤ (zBlockHom h).ker := by
        rw [Subgroup.commutator_le]
        intro x hx g _
        exact MonoidHom.mem_ker.mpr (by rw [map_commutatorElement, MonoidHom.mem_ker.mp hx,
          commutatorElement_one_left])
      exact hle hy
    have ht : y⁻¹ * x ∈ tvSub h := by
      refine ⟨mul_mem (inv_mem hyker) hx, ?_⟩
      have hy1 : rmat h y⁻¹ = 1 := by
        rw [rmat, MonoidHom.mem_ker.mp (inv_mem hyker)]
        rfl
      rw [avec_mul_of_mem_ker h (inv_mem hyker), avec_inv, hy1, one_mulVec, hyx, neg_add_cancel]
    have := mul_mem (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right ht :
      y⁻¹ * x ∈ ⁅(zBlockHom (ε := ε) h).ker, H⁆ ⊔ tvSub h)
    rwa [mul_inv_cancel_left] at this

@[expose] def fixSpace (H : Subgroup (stabE (ε := ε) h)) : AddSubgroup (Fin ε → K) where
  carrier := {v | ∀ g ∈ H, rmat h g *ᵥ v = v}
  add_mem' := by
    intro v w hv hw g hg
    rw [mulVec_add, hv g hg, hw g hg]
  zero_mem' := by
    intro g _
    rw [mulVec_zero]
  neg_mem' := by
    intro v hv g hg
    rw [mulVec_neg, hv g hg]

theorem exists_tvSub_conj {x : stabE (ε := ε) h} (hx : x ∈ (zBlockHom h).ker)
    {g : stabE (ε := ε) h} (hg : rmat h g *ᵥ avec h x = avec h x) :
    ∃ t ∈ tvSub h, g * x * g⁻¹ = t * x := by
  have hc : g * x * g⁻¹ ∈ (zBlockHom h).ker := (zBlockHom h).normal_ker.conj_mem _ hx g
  refine ⟨g * x * g⁻¹ * x⁻¹, ⟨mul_mem hc (inv_mem hx), ?_⟩, by rw [inv_mul_cancel_right]⟩
  have hx1 : rmat h x⁻¹ = 1 := by
    rw [rmat, MonoidHom.mem_ker.mp (inv_mem hx)]
    rfl
  rw [avec_mul_of_mem_ker h hc, avec_conj h hx, hg, avec_inv, hx1, one_mulVec, add_neg_cancel]

theorem le_centralizer_of_perfect {H : Subgroup (stabE (ε := ε) h)} (hH : ⁅H, H⁆ = H)
    {x : stabE (ε := ε) h} (hx : x ∈ (zBlockHom h).ker)
    (hxf : ∀ g ∈ H, rmat h g *ᵥ avec h x = avec h x) :
    H ≤ centralizer ({x} : Set (stabE (ε := ε) h)) := by
  have hT : ∀ g ∈ H, g * x * g⁻¹ * x⁻¹ ∈ tvSub h := fun g hg => by
    obtain ⟨t, ht, hgt⟩ := exists_tvSub_conj h hx (hxf g hg)
    rwa [hgt, mul_inv_cancel_right]
  let F : H →* stabE (ε := ε) h :=
    { toFun := fun g => (g : stabE (ε := ε) h) * x * (g : stabE (ε := ε) h)⁻¹ * x⁻¹
      map_one' := by simp
      map_mul' := fun g g' => by
        obtain ⟨G, hG⟩ := g
        obtain ⟨G', hG'⟩ := g'
        have ht' := hT G' hG'
        have hc := commute_of_avec_eq_zero h ht'.1 ht'.2
        show G * G' * x * (G * G')⁻¹ * x⁻¹ = (G * x * G⁻¹ * x⁻¹) * (G' * x * G'⁻¹ * x⁻¹)
        calc G * G' * x * (G * G')⁻¹ * x⁻¹ = G * (G' * x * G'⁻¹ * x⁻¹) * (x * G⁻¹ * x⁻¹) := by
              group
          _ = (G' * x * G'⁻¹ * x⁻¹) * G * (x * G⁻¹ * x⁻¹) := by rw [← hc G]
          _ = (G' * x * G'⁻¹ * x⁻¹) * (G * x * G⁻¹ * x⁻¹) := by group
          _ = (G * x * G⁻¹ * x⁻¹) * (G' * x * G'⁻¹ * x⁻¹) := hc _ }
  rw [← hH, Subgroup.commutator_le]
  intro a ha b hb
  have h1 : F ⁅(⟨a, ha⟩ : H), ⟨b, hb⟩⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    have hta := hT a ha
    exact commute_of_avec_eq_zero h hta.1 hta.2 _
  have h2 : F ⁅(⟨a, ha⟩ : H), ⟨b, hb⟩⁆ = ⁅a, b⁆ * x * ⁅a, b⁆⁻¹ * x⁻¹ := rfl
  rw [h2, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
  exact mem_centralizer_singleton_iff.mpr h1

theorem centralizer_inf_avecPre_eq {H : Subgroup (stabE (ε := ε) h)} (hH : ⁅H, H⁆ = H)
    (S : AddSubgroup (Fin ε → K)) :
    centralizer (H : Set (stabE (ε := ε) h)) ⊓ avecPre h S = avecPre h (S ⊓ fixSpace h H) := by
  apply le_antisymm
  · rintro x ⟨hxc, hx, hxS⟩
    refine ⟨hx, hxS, fun g hg => ?_⟩
    have := (mem_centralizer_iff.mp hxc) g hg
    rw [← avec_conj h hx g, this, mul_inv_cancel_right]
  · rintro x ⟨hx, hxS, hxf⟩
    refine ⟨?_, hx, hxS⟩
    have key := le_centralizer_of_perfect h hH hx hxf
    exact mem_centralizer_iff.mpr fun g hg => mem_centralizer_singleton_iff.mp (key hg)

theorem mul_self_eq_one_of_mem_tvSub {t : stabE (ε := ε) h} (ht : t ∈ tvSub h) : t * t = 1 := by
  obtain ⟨c, hc⟩ := exists_eichM_zero_of_avec h ht.1 ht.2
  refine Subtype.ext (Subtype.ext (Units.ext ?_))
  change smat h t * smat h t = 1
  rw [hc, eichM_mul]
  simp only [add_zero, Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero,
    CharTwo.add_self_eq_zero]
  exact eichM_zero _

@[expose] def fixOne (z : stabE (ε := ε) h) : AddSubgroup (Fin ε → K) where
  carrier := {v | rmat h z *ᵥ v = v}
  add_mem' := by
    intro v w hv hw
    simp only [Set.mem_ofPred_eq] at hv hw ⊢
    rw [mulVec_add, hv, hw]
  zero_mem' := by simp
  neg_mem' := by
    intro v hv
    simp only [Set.mem_ofPred_eq] at hv ⊢
    rw [mulVec_neg, hv]

theorem centralizer_singleton_inf_avecPre_eq {z : stabE (ε := ε) h} {m : ℕ} (hm : Odd m)
    (hz : z ^ m = 1) (S : AddSubgroup (Fin ε → K)) :
    centralizer ({z} : Set (stabE (ε := ε) h)) ⊓ avecPre h S = avecPre h (S ⊓ fixOne h z) := by
  apply le_antisymm
  · rintro x ⟨hxc, hx, hxS⟩
    refine ⟨hx, hxS, ?_⟩
    have := mem_centralizer_singleton_iff.mp hxc
    show rmat h z *ᵥ avec h x = avec h x
    rw [← avec_conj h hx z, ← this, mul_inv_cancel_right]
  · rintro x ⟨hx, hxS, hxf⟩
    refine ⟨?_, hx, hxS⟩
    obtain ⟨t, ht, hzt⟩ := exists_tvSub_conj h hx hxf
    have hc := commute_of_avec_eq_zero h ht.1 ht.2
    have hj : ∀ j : ℕ, z ^ j * x * (z ^ j)⁻¹ = t ^ j * x := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        calc z ^ (j + 1) * x * (z ^ (j + 1))⁻¹ = z * (z ^ j * x * (z ^ j)⁻¹) * z⁻¹ := by group
          _ = z * (t ^ j * x) * z⁻¹ := by rw [ih]
          _ = t ^ j * (z * x * z⁻¹) := by
              rw [show z * (t ^ j * x) * z⁻¹ = (z * t ^ j) * x * z⁻¹ by group,
                ← (Commute.pow_left (hc z) j).eq]
              group
          _ = t ^ (j + 1) * x := by rw [hzt, pow_succ, mul_assoc]
    have h1 := hj m
    rw [hz, one_mul, inv_one, mul_one] at h1
    have htm : t ^ m = 1 := by
      have := congrArg (· * x⁻¹) h1
      simpa using this.symm
    have ht1 : t = 1 := by
      obtain ⟨k, rfl⟩ := hm
      have hsq : t ^ 2 = 1 := by rw [sq]; exact mul_self_eq_one_of_mem_tvSub h ht
      rw [pow_succ, pow_mul, hsq, one_pow, one_mul] at htm
      exact htm
    rw [ht1, one_mul] at hzt
    exact mem_centralizer_singleton_iff.mpr (by
      rw [mul_inv_eq_iff_eq_mul] at hzt
      exact hzt.symm)

theorem card_avecPre (S : AddSubgroup (Fin ε → K)) :
    Nat.card (avecPre (ε := ε) h S) = Nat.card S * Nat.card (tvSub (ε := ε) h) := by
  choose sec hsec hsecv using exists_mem_ker_avec_eq (ε := ε) h
  have hinv : ∀ v, rmat h (sec v)⁻¹ = 1 := fun v => by
    rw [rmat, MonoidHom.mem_ker.mp (inv_mem (hsec v))]
    rfl
  have hT : ∀ x : avecPre (ε := ε) h S, (sec (avec h x))⁻¹ * x ∈ tvSub (ε := ε) h := by
    rintro ⟨x, hx, hxS⟩
    refine ⟨mul_mem (inv_mem (hsec _)) hx, ?_⟩
    rw [avec_mul_of_mem_ker h (inv_mem (hsec _)), avec_inv, hinv, one_mulVec, hsecv,
      neg_add_cancel]
  let e : avecPre (ε := ε) h S ≃ S × tvSub (ε := ε) h :=
    { toFun := fun x => (⟨avec h x, x.2.2⟩, ⟨_, hT x⟩)
      invFun := fun p => ⟨sec p.1 * p.2, mul_mem (hsec _) p.2.2.1, by
        rw [avec_mul_of_mem_ker h (hsec _), hsecv, p.2.2.2, add_zero]
        exact p.1.2⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun p => by
        obtain ⟨⟨v, hv⟩, ⟨t, ht⟩⟩ := p
        have hv' : avec h (sec v * t) = v := by
          rw [avec_mul_of_mem_ker h (hsec _), hsecv, ht.2, add_zero]
        refine Prod.ext (Subtype.ext hv') (Subtype.ext ?_)
        change (sec (avec h (sec v * t)))⁻¹ * (sec v * t) = t
        rw [hv', inv_mul_cancel_left] }
  rw [Nat.card_congr e, Nat.card_prod]

@[expose] def commSub (H : Subgroup (stabE (ε := ε) h)) : Submodule K (Fin ε → K) where
  toAddSubmonoid := (commSpace h H).toAddSubmonoid
  smul_mem' := by
    intro t w hw
    refine AddSubgroup.closure_induction (p := fun w _ => t • w ∈ commSpace h H) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨g, hg, v, rfl⟩
      exact AddSubgroup.subset_closure ⟨g, hg, t • v, by rw [smul_sub, mulVec_smul]⟩
    · rw [smul_zero]
      exact zero_mem _
    · intro a b _ _ ha hb
      rw [smul_add]
      exact add_mem ha hb
    · intro a _ ha
      rw [smul_neg]
      exact neg_mem ha

theorem mem_commSub {H : Subgroup (stabE (ε := ε) h)} {v : Fin ε → K} :
    v ∈ commSub h H ↔ v ∈ commSpace h H := Iff.rfl

@[expose] def fixSub (H : Subgroup (stabE (ε := ε) h)) : Submodule K (Fin ε → K) where
  toAddSubmonoid := (fixSpace h H).toAddSubmonoid
  smul_mem' := by
    intro t v hv g hg
    rw [mulVec_smul, hv g hg]

theorem mem_fixSub {H : Subgroup (stabE (ε := ε) h)} {v : Fin ε → K} :
    v ∈ fixSub h H ↔ ∀ g ∈ H, rmat h g *ᵥ v = v := Iff.rfl

@[expose] def fixOneSub (z : stabE (ε := ε) h) : Submodule K (Fin ε → K) where
  toAddSubmonoid := (fixOne h z).toAddSubmonoid
  smul_mem' := by
    intro t v hv
    show rmat h z *ᵥ (t • v) = t • v
    rw [mulVec_smul, show rmat h z *ᵥ v = v from hv]

end CFSG.ComponentClassification.RankTwoClassical.URigid
