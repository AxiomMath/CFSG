module

public import CFSG.LieType.Ree.FixedWeylStructure
public import CFSG.LieType.Ree.RootBruhatEquivariance
public import CFSG.LieType.Ree.RelationGraph
public import CFSG.LieType.Chevalley.RootCommutatorReduction

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Commute

variable {τ : Tag}

theorem commute_pinnedX_of_not_isRoot
    (R : Type) [CommRing R] {α β : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (hβ : IsRoot τ β) (hαp : 0 < height α) (hβp : 0 < height β)
    (hne : α ≠ β) (h : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → ¬ IsRoot τ (a • α + b • β)) (c d : R) :
    Commute (pinnedX τ R α c) (pinnedX τ R β d) := by
  have hle := commutator_rootSubgroup_le R hα hβ hαp hβp hne
  have hbot : (⨆ (γ : Fin τ.rank → ℤ) (_ : IsRoot τ γ ∧
      ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ γ = a • α + b • β), rootSubgroup τ R γ) = ⊥ :=
    iSup₂_eq_bot.2 fun γ ⟨hγ, a, b, ha, hb, hγe⟩ => absurd (hγe ▸ hγ) (h a b ha hb)
  rw [hbot] at hle
  have hmem := hle (Subgroup.commutator_mem_commutator (Subgroup.subset_closure ⟨c, rfl⟩)
    (Subgroup.subset_closure ⟨d, rfl⟩))
  exact commutatorElement_eq_one_iff_commute.1 ((Subgroup.mem_bot).1 hmem)

theorem forall_not_isRoot_of_check
    {α β : Fin τ.rank → ℤ} (hα : ∀ j, 0 ≤ α j)
    (hβ : ∀ j, 0 ≤ β j) {k l : Fin τ.rank} (hk : 1 ≤ α k) (hl : 1 ≤ β l)
    (h : ∀ a < 8, ∀ b < 8, 1 ≤ a → 1 ≤ b → RootOps.isRootB τ (a • α + b • β) = false) :
    ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → ¬ IsRoot τ (a • α + b • β) := by
  intro a b ha hb hr
  obtain ⟨ha7, hb7⟩ := RootOps.le_seven_of_isRoot_nsmul_add_nsmul hα hβ hk hl hr
  have h1 := h a (by omega) b (by omega) ha hb
  rw [← RootOps.isRootB_iff, h1] at hr
  exact Bool.false_ne_true hr

theorem pinnedX_mul_pinnedX_ne_one
    (R : Type) [CommRing R] [Nontrivial R]
    {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β) (hαp : 0 < height α)
    (hβp : 0 < height β) (hne : α ≠ β) :
    pinnedX τ R α 1 * pinnedX τ R β 1 ≠ 1 := by
  intro h1
  have h := pinnedX_list_prod_injective (R := R) [α, β] (by simp [hne])
    (by simp [hα, hβ, hαp, hβp]) (fun _ => 1) (fun _ => 0)
    (by simp [pinnedX_zero, h1])
  exact one_ne_zero (h α List.mem_cons_self)

end Commute

namespace ReeTag

@[expose] def g2Root11 : Fin G2.tag.rank → ℤ := ![1, 1]

@[expose] def g2Root13 : Fin G2.tag.rank → ℤ := ![1, 3]

@[expose] def f4Root0110 : Fin F4.tag.rank → ℤ := ![0, 1, 1, 0]

@[expose] def f4Root0120 : Fin F4.tag.rank → ℤ := ![0, 1, 2, 0]

theorem pinnedData_g2Root11
    : pinnedData G2.tag g2Root11 = (⟨1, by decide⟩, [0], 1) := by
  have h1 : ¬∃ j, g2Root11 = Pi.single j 1 := by decide
  have h2 : ¬∃ j, g2Root11 = -Pi.single j 1 := by decide
  rw [pinnedData, dite_eq_right h1, dite_eq_right h2]
  decide

theorem pinnedData_g2Root13
    : pinnedData G2.tag g2Root13 = (⟨0, by decide⟩, [1], 1) := by
  have h1 : ¬∃ j, g2Root13 = Pi.single j 1 := by decide
  have h2 : ¬∃ j, g2Root13 = -Pi.single j 1 := by decide
  rw [pinnedData, dite_eq_right h1, dite_eq_right h2]
  decide

theorem pinnedData_f4Root0110
    : pinnedData F4.tag f4Root0110 = (⟨2, by decide⟩, [1], 1) := by
  have h1 : ¬∃ j, f4Root0110 = Pi.single j 1 := by decide
  have h2 : ¬∃ j, f4Root0110 = -Pi.single j 1 := by decide
  rw [pinnedData, dite_eq_right h1, dite_eq_right h2]
  decide

theorem pinnedData_f4Root0120
    : pinnedData F4.tag f4Root0120 = (⟨1, by decide⟩, [2], 1) := by
  have h1 : ¬∃ j, f4Root0120 = Pi.single j 1 := by decide
  have h2 : ¬∃ j, f4Root0120 = -Pi.single j 1 := by decide
  rw [pinnedData, dite_eq_right h1, dite_eq_right h2]
  decide

theorem pinnedX_eq_of_pinnedData
    {τ : Tag} {R : Type} [CommRing R] {α : Fin τ.rank → ℤ}
    {j : Fin τ.rank} {i : ℕ} (h : pinnedData τ α = (j, [i], 1)) (c : R) :
    pinnedX τ R α c = weylElt τ R (τ.idx i) 1 * xUnit τ R j c * (weylElt τ R (τ.idx i) 1)⁻¹ := by
  simp only [pinnedX, pinnedWeyl, h, List.map_cons, List.map_nil, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.prod_cons, List.prod_nil, mul_one, one_smul]

variable {t : ReeTag} {K : Type} [Field K] [Finite K] [CharP K t.prime] {a : ℕ}

theorem finiteReeAut_weylElement
    (i : Fin t.tag.rank) :
    t.finiteReeAut K a (weylElement t.tag K i) = weylElement t.tag K (t.perm i) := by
  rw [finiteReeAut_eq_reeAut]
  exact reeAut_weylElement a i

theorem finiteReeAut_conj_one
    (i j : Fin t.tag.rank) :
    t.finiteReeAut K a (weylElement t.tag K i * xElement j 1 * (weylElement t.tag K i)⁻¹) =
      weylElement t.tag K (t.perm i) * xElement (t.perm j) 1 *
        (weylElement t.tag K (t.perm i))⁻¹ := by
  rw [map_mul, map_mul, map_inv, finiteReeAut_weylElement, finiteReeAut_xElement, one_pow]

theorem finiteReeAut_mul_eq_self
    {x y : adjointGroup t.tag K} (hx : t.finiteReeAut K a x = y)
    (hy : t.finiteReeAut K a y = x) (hc : Commute x y) : t.finiteReeAut K a (x * y) = x * y := by
  rw [map_mul, hx, hy]
  exact hc.eq.symm

theorem mem_reeGamma_mul
    {x y : adjointGroup t.tag K} (hx : t.finiteReeAut K a x = y)
    (hy : t.finiteReeAut K a y = x) (hc : Commute (x : ModGL t.tag K) (y : ModGL t.tag K)) :
    (x : ModGL t.tag K) * y ∈ t.reeGamma K a :=
  mem_reeGamma.2 ⟨(x * y).2, finiteReeAut_mul_eq_self hx hy (Subtype.ext hc.eq)⟩

theorem mem_reeFixedOrbitUnipotent_of_conj
    {k : Fin t.fixedOrbitCount} {α β : Fin t.tag.rank → ℤ}
    (hαE : α ∈ t.fixedOrbitRoots k) (hβE : β ∈ t.fixedOrbitRoots k) (i j : Fin t.tag.rank)
    (hα : pinnedX t.tag K α 1 =
      weylElt t.tag K i 1 * xUnit t.tag K j 1 * (weylElt t.tag K i 1)⁻¹)
    (hβ : pinnedX t.tag K β 1 = weylElt t.tag K (t.perm i) 1 * xUnit t.tag K (t.perm j) 1 *
      (weylElt t.tag K (t.perm i) 1)⁻¹)
    (hc : Commute (pinnedX t.tag K α 1) (pinnedX t.tag K β 1)) :
    pinnedX t.tag K α 1 * pinnedX t.tag K β 1 ∈ t.reeFixedOrbitUnipotent K a k := by
  refine ⟨mul_mem (pinnedX_mem_rootSpan hαE 1) (pinnedX_mem_rootSpan hβE 1), ?_⟩
  have hFy := finiteReeAut_conj_one (K := K) (a := a) (t.perm i) (t.perm j)
  rw [perm_perm, perm_perm] at hFy
  rw [hα, hβ] at hc ⊢
  exact mem_reeGamma_mul (finiteReeAut_conj_one i j) hFy hc

theorem fixedBlockRoots_check :
    g2Root11 ∈ G2.fixedOrbitRootList ⟨0, by decide⟩ ∧
      g2Root13 ∈ G2.fixedOrbitRootList ⟨0, by decide⟩ ∧
      f4Root0110 ∈ F4.fixedOrbitRootList ⟨1, by decide⟩ ∧
      f4Root0120 ∈ F4.fixedOrbitRootList ⟨1, by decide⟩ ∧
      (Pi.single ⟨0, by decide⟩ 1 : Fin F4.tag.rank → ℤ) ∈ F4.fixedOrbitRootList ⟨0, by decide⟩ ∧
      (Pi.single ⟨3, by decide⟩ 1 : Fin F4.tag.rank → ℤ) ∈
        F4.fixedOrbitRootList ⟨0, by decide⟩ := by
  decide

theorem g2Root_not_isRoot : ∀ a < 8, ∀ b < 8, 1 ≤ a → 1 ≤ b →
    RootOps.isRootB G2.tag (a • g2Root11 + b • g2Root13) = false := by
  decide +kernel

theorem f4Root_not_isRoot : ∀ a < 8, ∀ b < 8, 1 ≤ a → 1 ≤ b →
    RootOps.isRootB F4.tag (a • f4Root0110 + b • f4Root0120) = false := by
  decide +kernel

theorem f4Single_not_isRoot : ∀ a < 8, ∀ b < 8, 1 ≤ a → 1 ≤ b →
    RootOps.isRootB F4.tag (a • (Pi.single ⟨0, by decide⟩ 1 : Fin F4.tag.rank → ℤ) +
      b • (Pi.single ⟨3, by decide⟩ 1 : Fin F4.tag.rank → ℤ)) = false := by
  decide +kernel

theorem mem_fixedOrbitRoots_of_mem_list {t : ReeTag}
    {j : Fin t.fixedOrbitCount}
    {α : Fin t.tag.rank → ℤ} (h : α ∈ t.fixedOrbitRootList j) :
    α ∈ t.fixedOrbitRoots j := by
  rw [fixedOrbitRoots_eq_list]
  exact h

theorem fixedOrbitRoots_data
    {t : ReeTag} {j : Fin t.fixedOrbitCount}
    {α : Fin t.tag.rank → ℤ} (h : α ∈ t.fixedOrbitRoots j) :
    IsRoot t.tag α ∧ 0 < height α ∧ ∀ l, 0 ≤ α l :=
  ⟨(mem_fixedOrbitRoots_iff.1 h).1, (mem_fixedOrbitRoots_iff.1 h).2.1,
    (IsRoot.height_pos_iff (mem_fixedOrbitRoots_iff.1 h).1).1 (mem_fixedOrbitRoots_iff.1 h).2.1⟩

theorem g2_fixedBlock
    (K : Type) [Field K] [Finite K] [CharP K G2.prime] (a : ℕ) :
    pinnedX G2.tag K g2Root11 1 * pinnedX G2.tag K g2Root13 1 ∈
        G2.reeFixedOrbitUnipotent K a ⟨0, by decide⟩ ∧
      pinnedX G2.tag K g2Root11 1 * pinnedX G2.tag K g2Root13 1 ≠ 1 := by
  obtain ⟨h1, h2, -⟩ := fixedBlockRoots_check
  have hE1 := mem_fixedOrbitRoots_of_mem_list h1
  have hE2 := mem_fixedOrbitRoots_of_mem_list h2
  obtain ⟨r1, p1, n1⟩ := fixedOrbitRoots_data hE1
  obtain ⟨r2, p2, n2⟩ := fixedOrbitRoots_data hE2
  have hne : g2Root11 ≠ g2Root13 := by decide
  have hnr := forall_not_isRoot_of_check n1 n2 (k := ⟨0, by decide⟩) (l := ⟨0, by decide⟩)
    (by decide) (by decide) g2Root_not_isRoot
  refine ⟨mem_reeFixedOrbitUnipotent_of_conj hE1 hE2 ⟨0, by decide⟩ ⟨1, by decide⟩
    (pinnedX_eq_of_pinnedData pinnedData_g2Root11 1)
    (pinnedX_eq_of_pinnedData pinnedData_g2Root13 1)
    (commute_pinnedX_of_not_isRoot K r1 r2 p1 p2 hne hnr 1 1),
    pinnedX_mul_pinnedX_ne_one K r1 r2 p1 p2 hne⟩

theorem f4_fixedBlock_two
    (K : Type) [Field K] [Finite K] [CharP K F4.prime] (a : ℕ) :
    pinnedX F4.tag K f4Root0110 1 * pinnedX F4.tag K f4Root0120 1 ∈
        F4.reeFixedOrbitUnipotent K a ⟨1, by decide⟩ ∧
      pinnedX F4.tag K f4Root0110 1 * pinnedX F4.tag K f4Root0120 1 ≠ 1 := by
  obtain ⟨-, -, h1, h2, -⟩ := fixedBlockRoots_check
  have hE1 := mem_fixedOrbitRoots_of_mem_list h1
  have hE2 := mem_fixedOrbitRoots_of_mem_list h2
  obtain ⟨r1, p1, n1⟩ := fixedOrbitRoots_data hE1
  obtain ⟨r2, p2, n2⟩ := fixedOrbitRoots_data hE2
  have hne : f4Root0110 ≠ f4Root0120 := by decide
  have hnr := forall_not_isRoot_of_check n1 n2 (k := ⟨1, by decide⟩) (l := ⟨1, by decide⟩)
    (by decide) (by decide) f4Root_not_isRoot
  refine ⟨mem_reeFixedOrbitUnipotent_of_conj hE1 hE2 ⟨1, by decide⟩ ⟨2, by decide⟩
    (pinnedX_eq_of_pinnedData pinnedData_f4Root0110 1)
    (pinnedX_eq_of_pinnedData pinnedData_f4Root0120 1)
    (commute_pinnedX_of_not_isRoot K r1 r2 p1 p2 hne hnr 1 1),
    pinnedX_mul_pinnedX_ne_one K r1 r2 p1 p2 hne⟩

theorem f4_fixedBlock_one
    (K : Type) [Field K] [Finite K] [CharP K F4.prime] (a : ℕ) :
    xUnit F4.tag K ⟨0, by decide⟩ 1 * xUnit F4.tag K ⟨3, by decide⟩ 1 ∈
        F4.reeFixedOrbitUnipotent K a ⟨0, by decide⟩ ∧
      xUnit F4.tag K ⟨0, by decide⟩ 1 * xUnit F4.tag K ⟨3, by decide⟩ 1 ≠ 1 := by
  obtain ⟨-, -, -, -, h1, h2⟩ := fixedBlockRoots_check
  have hE1 := mem_fixedOrbitRoots_of_mem_list h1
  have hE2 := mem_fixedOrbitRoots_of_mem_list h2
  obtain ⟨r1, p1, n1⟩ := fixedOrbitRoots_data hE1
  obtain ⟨r2, p2, n2⟩ := fixedOrbitRoots_data hE2
  have hne : (Pi.single ⟨0, by decide⟩ 1 : Fin F4.tag.rank → ℤ) ≠ Pi.single ⟨3, by decide⟩ 1 := by
    decide
  have hnr := forall_not_isRoot_of_check n1 n2 (k := ⟨0, by decide⟩) (l := ⟨3, by decide⟩)
    (by decide) (by decide) f4Single_not_isRoot
  have hc := commute_pinnedX_of_not_isRoot K r1 r2 p1 p2 hne hnr 1 1
  rw [pinnedX_single, pinnedX_single] at hc
  refine ⟨⟨mul_mem ?_ ?_, ?_⟩, ?_⟩
  · rw [← pinnedX_single]
    exact pinnedX_mem_rootSpan hE1 1
  · rw [← pinnedX_single]
    exact pinnedX_mem_rootSpan hE2 1
  · refine mem_reeGamma_mul (x := xElement ⟨0, by decide⟩ 1) (y := xElement ⟨3, by decide⟩ 1)
      ?_ ?_ hc
    · rw [finiteReeAut_xElement, one_pow]
      rfl
    · rw [finiteReeAut_xElement, one_pow]
      rfl
  · have h := pinnedX_mul_pinnedX_ne_one K r1 r2 p1 p2 hne
    rwa [pinnedX_single, pinnedX_single] at h

theorem ree_nontrivial_fixed_positive_blocks :
    (∀ (K : Type) [Field K] [Finite K] [CharP K G2.prime] (a : ℕ),
      pinnedX G2.tag K ![1, 1] 1 * pinnedX G2.tag K ![1, 3] 1 ∈
          G2.reeFixedOrbitUnipotent K a (0 : Fin 1) ∧
        pinnedX G2.tag K ![1, 1] 1 * pinnedX G2.tag K ![1, 3] 1 ≠ 1) ∧
    ∀ (K : Type) [Field K] [Finite K] [CharP K F4.prime] (a : ℕ),
      (xUnit F4.tag K (0 : Fin 4) 1 * xUnit F4.tag K (3 : Fin 4) 1 ∈
          F4.reeFixedOrbitUnipotent K a (0 : Fin 2) ∧
        xUnit F4.tag K (0 : Fin 4) 1 * xUnit F4.tag K (3 : Fin 4) 1 ≠ 1) ∧
      pinnedX F4.tag K ![0, 1, 1, 0] 1 * pinnedX F4.tag K ![0, 1, 2, 0] 1 ∈
          F4.reeFixedOrbitUnipotent K a (1 : Fin 2) ∧
        pinnedX F4.tag K ![0, 1, 1, 0] 1 * pinnedX F4.tag K ![0, 1, 2, 0] 1 ≠ 1 :=
  ⟨fun K _ _ _ a => g2_fixedBlock K a,
    fun K _ _ _ a => ⟨f4_fixedBlock_one K a, f4_fixedBlock_two K a⟩⟩

end ReeTag

end CFSG.LieType.Ree
