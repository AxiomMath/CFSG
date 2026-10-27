module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentAdapt
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentFrame

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

open Polynomial Module QuadraticMap CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.K159 CFSG.Open CFSG.GroupTheory.WeirSylow

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ} {Bb : Subgroup ↥(orthDerived Q)}

structure IsPlaneDecomp (Q : QuadraticForm F V) (Bb : Subgroup ↥(orthDerived Q)) (N : Submodule F V)
    {r : ℕ} (U : Fin r → Submodule F V) : Prop extends IsPlaneSystem Q U where
  le : ∀ j, U j ≤ N
  maps_to : ∀ b ∈ Bb, ∀ j, ∀ x ∈ U j, (b : V ≃ₗ[F] V) x ∈ U j
  exists_gen : ∀ j, ∃ g ∈ Bb, (∀ x ∈ U j, (g : V ≃ₗ[F] V) x = x → x = 0) ∧
    ∀ b ∈ Bb, ∃ m : ℕ, ∀ x ∈ U j, (b : V ≃ₗ[F] V) x = ((g : V ≃ₗ[F] V) ^ m) x
  apply_of_perp : ∀ b ∈ Bb, ∀ x ∈ N, x ∈ polarPerp Q (⨆ j, U j) → (b : V ≃ₗ[F] V) x = x

theorem IsPlaneDecomp.nil {N : Submodule F V} (h : ∀ b ∈ Bb, ∀ x ∈ N, (b : V ≃ₗ[F] V) x = x) :
    IsPlaneDecomp Q Bb N (Fin.elim0 : Fin 0 → Submodule F V) where
  finrank_eq j := j.elim0
  nondeg j := j.elim0
  not_isPlusType j := j.elim0
  perp i := i.elim0
  le j := j.elim0
  maps_to _ _ j := j.elim0
  exists_gen j := j.elim0
  apply_of_perp b hb x hx _ := h b hb x hx

theorem regOn_inf_polarPerp {N P : Submodule F V} (hN : RegOn Q N) (hP : RegOn Q P) (hPN : P ≤ N) :
    RegOn Q (N ⊓ polarPerp Q P) := by
  intro u hu h
  have hcompl := isCompl_polarPerp (nondegenerate_of_regOn hP)
  refine hN u hu.1 fun w hw => ?_
  have hw' : w ∈ P ⊔ polarPerp Q P := by
    rw [hcompl.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hw'
  have hbN : b ∈ N := by
    have : b = (a + b) - a := by abel
    rw [this]
    exact Submodule.sub_mem _ hw (hPN ha)
  rw [QuadraticMap.polar_add_right, h b ⟨hbN, hb⟩, add_zero, QuadraticMap.polar_comm]
  exact mem_polarPerp_iff.1 hu.2 a ha

theorem finrank_add_finrank_inf_polarPerp {N P : Submodule F V} (hP : RegOn Q P) (hPN : P ≤ N) :
    Module.finrank F P + Module.finrank F ↥(N ⊓ polarPerp Q P) = Module.finrank F N := by
  have hcompl := isCompl_polarPerp (nondegenerate_of_regOn hP)
  have h1 : P ⊔ (N ⊓ polarPerp Q P) = N := by
    rw [inf_comm, ← sup_inf_assoc_of_le _ hPN, hcompl.sup_eq_top, top_inf_eq]
  have h2 : P ⊓ (N ⊓ polarPerp Q P) = ⊥ := by
    rw [← inf_assoc, inf_eq_left.2 hPN]
    exact hcompl.inf_eq_bot
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq P (N ⊓ polarPerp Q P)
  rw [h1, h2, finrank_bot, add_zero] at h3
  omega

theorem apply_mem_polarPerp {P : Submodule F V}
    (hP : ∀ b ∈ Bb, ∀ y ∈ P, (b : V ≃ₗ[F] V) y ∈ P) {b : ↥(orthDerived Q)} (hb : b ∈ Bb) {x : V}
    (hx : x ∈ polarPerp Q P) : (b : V ≃ₗ[F] V) x ∈ polarPerp Q P := by
  rw [mem_polarPerp_iff] at hx ⊢
  intro y hy
  have hb' : b⁻¹ ∈ Bb := Bb.inv_mem hb
  have h1 : (b : V ≃ₗ[F] V) (((b⁻¹ : ↥(orthDerived Q)) : V ≃ₗ[F] V) y) = y := by
    have := congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V) y) (mul_inv_cancel b)
    simpa using this
  rw [← h1, TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup
    (orthDerived_le_orthogonalGroup b.2)]
  exact hx _ (hP _ hb' y hy)

private theorem IsPlaneDecomp.cons_aux1 {N P : Submodule F V} {r : ℕ} {U' : Fin r → Submodule F V}
    (hU' : IsPlaneDecomp Q Bb (N ⊓ polarPerp Q P) U') :
    ∀ i j, i ≠ j → ∀ x ∈ (Fin.cons P U' : Fin (r + 1) → Submodule F V) i,
      ∀ y ∈ (Fin.cons P U' : Fin (r + 1) → Submodule F V) j, QuadraticMap.polar Q x y = 0 := by
  intro i j hij x hx y hy
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => exact absurd rfl hij
    | succ k =>
      simp only [Fin.cons_zero, Fin.cons_succ] at hx hy
      exact mem_polarPerp_iff.1 (hU'.le k hy).2 x hx
  | succ k =>
    induction j using Fin.cases with
    | zero =>
      simp only [Fin.cons_zero, Fin.cons_succ] at hx hy
      rw [QuadraticMap.polar_comm]
      exact mem_polarPerp_iff.1 (hU'.le k hx).2 y hy
    | succ l =>
      simp only [Fin.cons_succ] at hx hy
      exact hU'.perp k l (fun h => hij (by rw [h])) x hx y hy

private theorem IsPlaneDecomp.cons_aux2 {P : Submodule F V} {r : ℕ} {U' : Fin r → Submodule F V} :
    (⨆ j : Fin (r + 1), (Fin.cons P U' : Fin (r + 1) → Submodule F V) j) = P ⊔ ⨆ j, U' j := by
  apply le_antisymm
  · refine iSup_le fun j => ?_
    induction j using Fin.cases with
    | zero => simp
    | succ i => simpa using le_sup_of_le_right (le_iSup U' i)
  · refine sup_le ?_ (iSup_le fun i => ?_)
    · simpa using le_iSup (Fin.cons P U' : Fin (r + 1) → Submodule F V) 0
    · simpa using le_iSup (Fin.cons P U' : Fin (r + 1) → Submodule F V) i.succ

private theorem IsPlaneDecomp.cons_aux3 {N P : Submodule F V} {r : ℕ} {U' : Fin r → Submodule F V}
    (hP2 : Module.finrank F P = 2) (hU' : IsPlaneDecomp Q Bb (N ⊓ polarPerp Q P) U') :
    ∀ j, Module.finrank F ((Fin.cons P U' : Fin (r + 1) → Submodule F V) j) = 2 := by
  intro j
  induction j using Fin.cases with
  | zero => rw [Fin.cons_zero]; exact hP2
  | succ i => rw [Fin.cons_succ]; exact hU'.finrank_eq i

private theorem IsPlaneDecomp.cons_aux4 {N P : Submodule F V} {r : ℕ} {U' : Fin r → Submodule F V}
    (hPreg : RegOn Q P) (hU' : IsPlaneDecomp Q Bb (N ⊓ polarPerp Q P) U') :
    ∀ j, (QuadraticMap.polarBilin (Q.comp ((Fin.cons P U' : Fin (r + 1) → Submodule F V) j).subtype)).Nondegenerate := by
  intro j
  induction j using Fin.cases with
  | zero => rw [Fin.cons_zero]; exact nondegenerate_of_regOn hPreg
  | succ i => rw [Fin.cons_succ]; exact hU'.nondeg i

private theorem IsPlaneDecomp.cons_aux5 {N P : Submodule F V} {r : ℕ} {U' : Fin r → Submodule F V}
    (hPm : ¬ IsPlusType (Q.comp P.subtype)) (hU' : IsPlaneDecomp Q Bb (N ⊓ polarPerp Q P) U') :
    ∀ j, ¬ IsPlusType (Q.comp ((Fin.cons P U' : Fin (r + 1) → Submodule F V) j).subtype) := by
  intro j
  induction j using Fin.cases with
  | zero => rw [Fin.cons_zero]; exact hPm
  | succ i => rw [Fin.cons_succ]; exact hU'.not_isPlusType i

theorem IsPlaneDecomp.cons {N P : Submodule F V} {r : ℕ} {U' : Fin r → Submodule F V}
    (hU' : IsPlaneDecomp Q Bb (N ⊓ polarPerp Q P) U') (hPN : P ≤ N) (hP2 : Module.finrank F P = 2)
    (hPreg : RegOn Q P) (hPm : ¬ IsPlusType (Q.comp P.subtype))
    (hPinv : ∀ b ∈ Bb, ∀ y ∈ P, (b : V ≃ₗ[F] V) y ∈ P)
    (hPgen : ∃ g ∈ Bb, (∀ y ∈ P, (g : V ≃ₗ[F] V) y = y → y = 0) ∧
      ∀ b ∈ Bb, ∃ m : ℕ, ∀ y ∈ P, (b : V ≃ₗ[F] V) y = ((g : V ≃ₗ[F] V) ^ m) y) :
    IsPlaneDecomp Q Bb N (Fin.cons P U' : Fin (r + 1) → Submodule F V) where
  finrank_eq := IsPlaneDecomp.cons_aux3 hP2 hU'
  nondeg := IsPlaneDecomp.cons_aux4 hPreg hU'
  not_isPlusType := IsPlaneDecomp.cons_aux5 hPm hU'
  perp := IsPlaneDecomp.cons_aux1 hU'
  le j := by
    induction j using Fin.cases with
    | zero => simpa using hPN
    | succ i => simpa using (hU'.le i).trans inf_le_left
  maps_to b hb j x hx := by
    induction j using Fin.cases with
    | zero =>
      simp only [Fin.cons_zero] at hx ⊢
      exact hPinv b hb x hx
    | succ i =>
      simp only [Fin.cons_succ] at hx ⊢
      exact hU'.maps_to b hb i x hx
  exists_gen j := by
    induction j using Fin.cases with
    | zero => simpa using hPgen
    | succ i => simpa using hU'.exists_gen i
  apply_of_perp b hb x hxN hx := by
    rw [IsPlaneDecomp.cons_aux2, mem_polarPerp_iff] at hx
    exact hU'.apply_of_perp b hb x
      ⟨hxN, mem_polarPerp_iff.2 fun y hy => hx y (Submodule.mem_sup_left hy)⟩
      (mem_polarPerp_iff.2 fun y hy => hx y (Submodule.mem_sup_right hy))

theorem exists_planeDecomp (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) (hBb : IsElemAbelian p Bb) :
    ∀ (N : Submodule F V), RegOn Q N → (∀ b ∈ Bb, ∀ y ∈ N, (b : V ≃ₗ[F] V) y ∈ N) →
      ∃ (r : ℕ) (U : Fin r → Submodule F V), IsPlaneDecomp Q Bb N U := by
  suffices h : ∀ d : ℕ, ∀ N : Submodule F V, Module.finrank F N = d → RegOn Q N →
      (∀ b ∈ Bb, ∀ y ∈ N, (b : V ≃ₗ[F] V) y ∈ N) →
      ∃ (r : ℕ) (U : Fin r → Submodule F V), IsPlaneDecomp Q Bb N U from fun N => h _ N rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro N hd hN hinv
    by_cases hmov : ∃ b ∈ Bb, ∃ y ∈ N, (b : V ≃ₗ[F] V) y ≠ y
    · obtain ⟨P, g, hgB, hPN, hP2, hPreg, hPm, hPinv, hPfix, hPgen⟩ :=
        exists_adapted_plane hQ hp hp2 hpq hBb hN hinv hmov
      have hN' : RegOn Q (N ⊓ polarPerp Q P) := regOn_inf_polarPerp hN hPreg hPN
      have hinv' : ∀ b ∈ Bb, ∀ y ∈ N ⊓ polarPerp Q P, (b : V ≃ₗ[F] V) y ∈ N ⊓ polarPerp Q P :=
        fun b hb y hy => ⟨hinv b hb y hy.1, apply_mem_polarPerp hPinv hb hy.2⟩
      have hdim := finrank_add_finrank_inf_polarPerp hPreg hPN
      obtain ⟨r, U', hU'⟩ := ih _ (by omega) (N ⊓ polarPerp Q P) rfl hN' hinv'
      exact ⟨r + 1, Fin.cons P U', hU'.cons hPN hP2 hPreg hPm hPinv ⟨g, hgB, hPfix, hPgen⟩⟩
    · push Not at hmov
      exact ⟨0, Fin.elim0, IsPlaneDecomp.nil fun b hb x hx => hmov b hb x hx⟩

end CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

end
