module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerS3A

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.QuasithinUnique.Setup.Offender CFSG.Quasithin.B6
open scoped commutatorElement

universe v

variable {k : Type*} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

structure NaturalS3Factors (G N A : Subgroup (V ≃ₗ[k] V)) {ι : Type*}
    (g : ι → V ≃ₗ[k] V) : Prop where
  card_k : Nat.card k = 2
  card_L : ∀ i, Nat.card (natL N A g i) = 3
  card_A : ∀ i, Nat.card (natA A g i) = 2
  finrank_I : ∀ i, Module.finrank k (natI N A g i) = 2
  L_comm : ∀ i j, i ≠ j → ∀ x ∈ natL N A g i, ∀ y ∈ natL N A g j, x * y = y * x
  L_indep : iSupIndep (natL N A g)
  D_le_N : natD N A g ≤ N
  D_normal : ((natD N A g).subgroupOf G).Normal
  D_elem : CFSG.IsElementaryAbelian 3 (natD N A g)
  card_D : Nat.card (natD N A g) = 3 ^ Nat.card ι
  I_indep : iSupIndep (natI N A g)
  W_eq : natW N A g = ⨆ i, natI N A g i
  V_compl : IsCompl (natW N A g) (fixGL (natD N A g))
  S_comm : ∀ i j, i ≠ j → ∀ x ∈ natS N A g i, ∀ y ∈ natS N A g j, x * y = y * x
  S_indep : iSupIndep (natS N A g)
  B_eq : natB G N A = ⨆ i, natS N A g i
  B_le : natB G N A ≤ G
  B_normal : ((natB G N A).subgroupOf G).Normal
  LA_le_B : ⁅N, A⁆ ⊔ A ≤ natB G N A
  S_action : ∀ i,
    ∃ hW : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[k] V)) (natS N A g i) (natI N A g i),
    Function.Bijective
      (resSub (MonoidHom.id (V ≃ₗ[k] V)) (natS N A g i) (natI N A g i) hW)
  S_fix_I : ∀ i j, i ≠ j → natI N A g j ≤ fixGL (natS N A g i)
  S_fix_C : ∀ i, fixGL (natD N A g) ≤ fixGL (natS N A g i)
  S_choice : ∀ x ∈ G, ∀ i, conjR x ⁅N, A⁆ = natL N A g i →
    conjR x (⁅N, A⁆ ⊔ A) = natS N A g i
  S_perm : ∀ x ∈ G, ∀ i, ∃ j, conjSub x (natS N A g i) = natS N A g j ∧
    conjSub x (natL N A g i) = natL N A g j ∧
    (natI N A g i).map (x : V →ₗ[k] V) = natI N A g j
  S_trans : ∀ i j, ∃ x ∈ G, conjSub x (natS N A g i) = natS N A g j ∧
    conjSub x (natL N A g i) = natL N A g j ∧
    (natI N A g i).map (x : V →ₗ[k] V) = natI N A g j
  B_derived : ⁅natB G N A, natB G N A⁆ = natD N A g
  S_le_B : ∀ i, natS N A g i ≤ natB G N A
  S_normal_B : ∀ i, ((natS N A g i).subgroupOf (natB G N A)).Normal
  N_eq : natD N A g ⊔ (N ⊓ centSub (MonoidHom.id (V ≃ₗ[k] V)) (natW N A g)) = N
  N_disjoint : Disjoint (natD N A g) (N ⊓ centSub (MonoidHom.id (V ≃ₗ[k] V)) (natW N A g))
  C_eq : N ⊓ centSub (MonoidHom.id (V ≃ₗ[k] V)) (natW N A g) =
    N ⊓ Subgroup.centralizer (natB G N A : Set (V ≃ₗ[k] V))

namespace OddAbelianSetting

variable [CharP k 2] [Finite V] {G N A : Subgroup (V ≃ₗ[k] V)} {ι : Type*}
  {g : ι → V ≃ₗ[k] V} [Fintype ι] (h : OddAbelianSetting G N A) (F : ConjFamily G N A g)

include h F

omit [Fintype ι] in
theorem S_action (i : ι) :
    ∃ hW : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[k] V)) (natS N A g i) (natI N A g i),
      Function.Bijective
        (resSub (MonoidHom.id (V ≃ₗ[k] V)) (natS N A g i) (natI N A g i) hW) :=
  (h.planeData_family F i).action

theorem S_fix_I {i j : ι} (hij : i ≠ j) : natI N A g j ≤ fixGL (natS N A g i) :=
  fun w hw x hx => (h.famData F).fix_sup_I (h.planeData_family F i) (Ne.symm hij) x hx w hw

theorem S_fix_C (i : ι) : fixGL (natD N A g) ≤ fixGL (natS N A g i) :=
  fun c hc x hx => (h.famData F).fix_sup_C (h.planeData_family F i) x hx c hc

theorem S_comm {i j : ι} (hij : i ≠ j) :
    ∀ x ∈ natS N A g i, ∀ y ∈ natS N A g j, x * y = y * x := by
  intro x hx y hy
  obtain ⟨hWi, -⟩ := h.S_action F i
  obtain ⟨hWj, -⟩ := h.S_action F j
  exact (h.famData F).mul_comm_of_supports hij (fun w hw => hWi x hx w hw)
    (fun w hw => hWj y hy w hw)
    (fun l hli w hw => h.S_fix_I F (Ne.symm hli) hw x hx)
    (fun l hlj w hw => h.S_fix_I F (Ne.symm hlj) hw y hy)
    (fun c hc => h.S_fix_C F i hc x hx) (fun c hc => h.S_fix_C F j hc y hy)

theorem S_indep : iSupIndep (natS N A g) := by
  intro i
  rw [Subgroup.disjoint_def]
  intro x hxi hxj
  have hle : (⨆ (j : ι) (_ : j ≠ i), natS N A g j) ≤
      centSub (MonoidHom.id (V ≃ₗ[k] V)) (natI N A g i) := by
    refine iSup₂_le fun j hj => ?_
    intro y hy u hu
    exact h.S_fix_I F hj hu y hy
  have hfix : ∀ u ∈ natI N A g i, x u = u := fun u hu => hle hxj u hu
  obtain ⟨hW, hbij⟩ := h.S_action F i
  have h1 : resSub (MonoidHom.id (V ≃ₗ[k] V)) (natS N A g i) (natI N A g i) hW ⟨x, hxi⟩ = 1 := by
    apply LinearEquiv.ext
    intro w
    apply Subtype.ext
    rw [resSub_apply]
    exact hfix w w.2
  have h2 : (⟨x, hxi⟩ : ↥(natS N A g i)) = 1 := hbij.1 (by rw [h1, map_one])
  exact congrArg Subtype.val h2

theorem S_le_B (i : ι) : natS N A g i ≤ natB G N A := by
  rw [h.B_eq F]
  exact le_iSup (natS N A g) i

theorem S_normal_B (i : ι) : ((natS N A g i).subgroupOf (natB G N A)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (h.S_le_B F i)]
  intro s b hs hb
  rw [h.B_eq F] at hb
  refine Subgroup.iSup_induction (natS N A g) hb
    (C := fun b => ∀ s ∈ natS N A g i, b * s * b⁻¹ ∈ natS N A g i) ?_ ?_ ?_ s hs
  · intro j b' hb' s' hs'
    by_cases hji : j = i
    · subst hji
      exact (natS N A g j).mul_mem ((natS N A g j).mul_mem hb' hs') ((natS N A g j).inv_mem hb')
    · have e : b' * s' * b'⁻¹ = s' := by
        rw [h.S_comm F hji b' hb' s' hs']
        group
      rw [e]
      exact hs'
  · intro s' hs'
    simpa using hs'
  · intro x y hx hy s' hs'
    have e : x * y * s' * (x * y)⁻¹ = x * (y * s' * y⁻¹) * x⁻¹ := by group
    rw [e]
    exact hx _ (hy s' hs')

theorem D_le_N : natD N A g ≤ N := iSup_le (h.famData F).L_le

theorem D_normal : ((natD N A g).subgroupOf G).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (h.D_le_N F |>.trans h.N_le)]
  intro y hy
  exact mem_normalizer_of_conjSub_le (h.D_normal_aux F hy) (h.D_normal_aux F (G.inv_mem hy))

theorem D_elem : CFSG.IsElementaryAbelian 3 (natD N A g) := by
  have fd := h.famData F
  exact
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext
        (fd.N_comm a (h.D_le_N F a.2) b (h.D_le_N F b.2))⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x =>
        Subtype.ext (fd.D_exp x x.2) }

theorem card_D : Nat.card (natD N A g) = 3 ^ Nat.card ι := by
  classical
  have fd := h.famData F
  have hcomm : Pairwise fun i j => ∀ x y : V ≃ₗ[k] V, x ∈ natL N A g i → y ∈ natL N A g j →
      Commute x y := fun i j hij x y hx hy => fd.L_comm i j hij x hx y hy
  have hinj := Subgroup.injective_noncommPiCoprod_of_iSupIndep (H := natL N A g)
    (hcomm := hcomm) fd.L_indep
  have hrange := Subgroup.noncommPiCoprod_range (H := natL N A g) (hcomm := hcomm)
  have e1 : Nat.card (natD N A g) = Nat.card (∀ i, natL N A g i) := by
    have : Nat.card (Subgroup.noncommPiCoprod hcomm).range = Nat.card (∀ i, natL N A g i) :=
      Nat.card_congr (Equiv.ofInjective _ hinj).symm
    rw [← this, hrange]
    rfl
  rw [e1, Nat.card_pi]
  rw [Finset.prod_congr rfl (fun i _ => (h.planeData_family F i).card_L)]
  simp [Nat.card_eq_fintype_card]

end OddAbelianSetting

end CFSG.QuasithinUnique.Setup.Layer
