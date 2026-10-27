module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HNSideFacts.F4Setup
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HNSideFacts.F4FamilyHom
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HNSideFacts.F4Wreath
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HNSideFacts.F4Radical

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.HNRecog.SideF4

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.Sporadic.HNOddCore
  CFSG.Sporadic.HNOddCore.Native CFSG.ONSchreier CFSG.ONSchreier.Native Equiv

section Quotient


theorem closure_gJ : Subgroup.closure (Set.range gJ) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : (x : JH) ∈ S4 := by rw [CJ_t4_eq]; exact x.2
  have key : ∀ y ∈ S4, y ∈ (Subgroup.closure (Set.range gJ)).map CJ.subtype := by
    intro y hy
    refine Subgroup.closure_induction
      (p := fun y _ => y ∈ (Subgroup.closure (Set.range gJ)).map CJ.subtype) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨s, rfl⟩
      have hs : (s : ℕ) < 10 := by
        have h1 := s.2
        have h2 := s4J_size
        omega
      exact Subgroup.mem_map.2 ⟨gJ ⟨s, hs⟩, Subgroup.subset_closure ⟨_, rfl⟩, rfl⟩
    · exact Subgroup.one_mem _
    · exact fun _ _ _ _ hx hy => Subgroup.mul_mem _ hx hy
    · exact fun _ _ hx => Subgroup.inv_mem _ hx
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 (key _ hx)
  have : y = x := Subtype.ext hyx
  rw [← this]
  exact hy

@[expose] def actQ : CJ →* Perm (Perm (Fin 800)) :=
  (MulAut.toPerm (Perm (Fin 800))).comp
    ((MulAut.conj : Perm (Fin 800) →* MulAut (Perm (Fin 800))).comp rhoJ)

theorem actQ_apply (x : CJ) (y : Perm (Fin 800)) : actQ x y = rhoJ x * y * (rhoJ x)⁻¹ :=
  MulAut.conj_apply (rhoJ x) y

theorem conjQ_mem {x : CJ} {y : Perm (Fin 800)} (hy : y ∈ Qbar) :
    rhoJ x * y * (rhoJ x)⁻¹ ∈ Qbar := by
  obtain ⟨z, hz⟩ := Qbar_le_rhoJ_range hy
  have hzQ : z ∈ QJ := by rw [mem_QJ, hz]; exact hy
  have h2 : rhoJ (x * z * x⁻¹) ∈ Qbar := QJ_normal.conj_mem z hzQ x
  rw [map_mul, map_mul, map_inv, hz] at h2
  exact h2

theorem conjQ_iff (x : CJ) (y : Perm (Fin 800)) :
    rhoJ x * y * (rhoJ x)⁻¹ ∈ Qbar ↔ y ∈ Qbar := by
  refine ⟨fun h => ?_, conjQ_mem⟩
  have h2 := conjQ_mem (x := x⁻¹) h
  have e : rhoJ x⁻¹ * (rhoJ x * y * (rhoJ x)⁻¹) * (rhoJ x⁻¹)⁻¹ = y := by
    rw [map_inv]
    group
  rw [e] at h2
  exact h2

theorem actQ_of_mem_QJ {x : CJ} (hx : x ∈ QJ) {y : Perm (Fin 800)} (hy : y ∈ Qbar) :
    actQ x y = y := by
  rw [actQ_apply, Qbar_comm (mem_QJ.1 hx) hy]
  group

@[expose] def Vfam (i : Fin 10) : Set (Perm (Fin 800)) :=
  {y | ∃ m, m < 256 ∧ inV (i : ℕ) m = true ∧ qb m = y}

theorem mem_Vfam_qb {i : Fin 10} {m : ℕ} (hm : m < 256) : qb m ∈ Vfam i ↔ inV (i : ℕ) m = true := by
  constructor
  · rintro ⟨m', hm', hin, he⟩
    rw [qb_inj hm' hm he] at hin
    exact hin
  · intro h
    exact ⟨m, hm, h, rfl⟩

theorem Vfam_subset_Qbar (i : Fin 10) : Vfam i ⊆ Qbar := by
  rintro _ ⟨m, hm, -, rfl⟩
  exact (qb_spec hm).1

@[expose] def sigPerm (k : ℕ) : Perm (Fin 10) := CFSG.ONSchreier.permOfArr 10 sigArrs[k]!

theorem prep_sigPerm {k : ℕ} (hk : k < 10) : PRep 10 sigArrs[k]! (sigPerm k) :=
  (prep_permOfArr ((sideF4FamOK_parts sideF4FamOK_true).2.2.2.2.1 k hk)).1

theorem Vfam_action (s : Fin 10) (i : Fin 10) (y : Perm (Fin 800)) :
    actQ (gJ s) y ∈ Vfam (sigPerm s i) ↔ y ∈ Vfam i := by
  have hdata := (sideF4FamOK_parts sideF4FamOK_true).2.2.1
  have hr : rhoJ (gJ s) = rhoGen s := rhoJ_gJ s
  rw [actQ_apply, hr]
  by_cases hy : y ∈ Qbar
  · obtain ⟨m1, hm1⟩ := Qbar_subset hy
    have hm1' : qb m1 = y := hm1
    have h2 : rhoGen s * y * (rhoGen s)⁻¹ ∈ Qbar := by
      have := conjQ_mem (x := gJ s) hy
      rwa [hr] at this
    obtain ⟨m2, hm2⟩ := Qbar_subset h2
    have hm2' : qb m2 = rhoGen s * y * (rhoGen s)⁻¹ := hm2
    have hspec := colPerm_spec (g := (s : ℕ)) (by omega) (m := (m2 : ℕ)) m2.2
    have hback : y = qb ((colPerms[(s : ℕ)]!)[(m2 : ℕ)]!) := by
      rw [← hspec, hm2']
      group
    have hm1eq : (m1 : ℕ) = (colPerms[(s : ℕ)]!)[(m2 : ℕ)]! :=
      qb_inj m1.2 (colPerm_lt (by omega) m2.2) (by rw [hm1', hback])
    have hd := hdata (s : ℕ) s.2 (i : ℕ) i.2 (m2 : ℕ) m2.2
    rw [(prep_sigPerm s.2) i] at hd
    rw [← hm2', ← hm1', mem_Vfam_qb m2.2, mem_Vfam_qb m1.2, hd, hm1eq]
  · have h2 : ¬ (rhoGen s * y * (rhoGen s)⁻¹ ∈ Qbar) := fun h =>
      hy ((conjQ_iff (gJ s) y).1 (by rwa [hr]))
    exact ⟨fun h => absurd (Vfam_subset_Qbar _ h) h2, fun h => absurd (Vfam_subset_Qbar _ h) hy⟩

theorem Vfam_injective : Function.Injective Vfam := by
  have hdist := (sideF4FamOK_parts sideF4FamOK_true).2.2.2.1
  have key : ∀ i j : Fin 10, i ≠ j → Vfam i ≠ Vfam j := by
    intro i j hij hV
    have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    have hex : ∃ m < 256, inV (i : ℕ) m ≠ inV (j : ℕ) m := by
      rcases lt_or_gt_of_ne hne with h | h
      · rcases hdist i i.2 j j.2 with h' | h'
        · omega
        · exact h'
      · rcases hdist j j.2 i i.2 with h' | h'
        · omega
        · obtain ⟨m, hm, hne'⟩ := h'
          exact ⟨m, hm, Ne.symm hne'⟩
    obtain ⟨m, hm, hne'⟩ := hex
    apply hne'
    have h1 := mem_Vfam_qb (i := i) hm
    have h2 := mem_Vfam_qb (i := j) hm
    rw [hV] at h1
    exact Bool.eq_iff_iff.2 (h1.symm.trans h2)
  intro i j h
  by_contra hij
  exact key i j hij h

theorem exists_phi : ∃ φ : CJ →* Perm (Fin 10), (∀ s : Fin 10, φ (gJ s) = sigPerm s) ∧
    ∀ (x : CJ) (i : Fin 10) (y : Perm (Fin 800)), actQ x y ∈ Vfam (φ x i) ↔ y ∈ Vfam i :=
  exists_hom_of_permuted_family gJ closure_gJ actQ Vfam Vfam_injective (fun s => sigPerm s)
    Vfam_action

@[expose] def phiQ : CJ →* Perm (Fin 10) := Classical.choose exists_phi

theorem phiQ_gJ (s : Fin 10) : phiQ (gJ s) = sigPerm s :=
  (Classical.choose_spec exists_phi).1 s

theorem phiQ_action (x : CJ) (i : Fin 10) (y : Perm (Fin 800)) :
    actQ x y ∈ Vfam (phiQ x i) ↔ y ∈ Vfam i :=
  (Classical.choose_spec exists_phi).2 x i y

theorem QJ_le_ker_phi : QJ ≤ phiQ.ker := by
  intro x hx
  rw [MonoidHom.mem_ker]
  apply Equiv.ext
  intro i
  apply Vfam_injective
  ext y
  by_cases hy : y ∈ Qbar
  · have h := phiQ_action x i y
    rw [actQ_of_mem_QJ hx hy] at h
    exact h.trans (by rfl)
  · exact ⟨fun h => absurd (Vfam_subset_Qbar _ h) hy, fun h => absurd (Vfam_subset_Qbar _ h) hy⟩

theorem range_phi_eq : phiQ.range = Subgroup.closure (Set.range fun s : Fin 10 => sigPerm s) := by
  have e : (phiQ ∘ gJ) = fun s : Fin 10 => sigPerm s := funext phiQ_gJ
  rw [MonoidHom.range_eq_map, ← closure_gJ, MonoidHom.map_closure, ← Set.range_comp, e]

theorem range_phi_le : phiQ.range ≤ a5WrTwoImage := by
  rw [range_phi_eq, Subgroup.closure_le]
  rintro _ ⟨s, rfl⟩
  exact mem_a5WrTwoImage_of_prep_sigArrs s.2 (prep_sigPerm s.2)

theorem card_range_phi : Nat.card phiQ.range = 7200 := by
  have hsz : sigArrs.size = 10 := (sideF4FamOK_parts sideF4FamOK_true).2.1
  have hO : ∀ k < sigArrs.size, PRep 10 sigArrs[k]! (sigPerm k) := fun k hk =>
    prep_sigPerm (by omega)
  have hset : (Set.range fun s : Fin 10 => sigPerm s) =
      Set.range fun k : Fin sigArrs.size => sigPerm k := by
    ext σ
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨⟨s, by rw [hsz]; exact s.2⟩, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨⟨k, by rw [← hsz]; exact k.2⟩, rfl⟩
  have hcard := card_arrGen_of_chainCheck (n := 10) (by norm_num) (O := sigArrs) (W := sigWords)
    (base := sigBase) (sizes := sigSizes) (by decide)
    (sideF4FamOK_parts sideF4FamOK_true).2.2.2.2.2
  rw [range_phi_eq, hset, ← arrGen_eq hO, hcard]
  decide

theorem ker_phi_eq : phiQ.ker = QJ := by
  have hle := QJ_le_ker_phi
  have hk := Subgroup.card_ker_mul_card_range phiQ
  rw [card_CJ_t4, card_range_phi] at hk
  have hker : Nat.card phiQ.ker = 512 := Nat.eq_of_mul_eq_mul_right (by norm_num) (hk.trans (by norm_num))
  haveI : Finite phiQ.ker := Nat.finite_of_card_ne_zero (by rw [hker]; norm_num)
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hker, card_QJ])).symm

theorem nonempty_quotient_QJ : Nonempty (CJ ⧸ QJ ≃* A5WrTwo) :=
  nonempty_quotient_mulEquiv_a5WrTwo QJ phiQ ker_phi_eq range_phi_le card_range_phi

end Quotient

end CFSG.EvenSporadicStandard.HNRecog.SideF4
