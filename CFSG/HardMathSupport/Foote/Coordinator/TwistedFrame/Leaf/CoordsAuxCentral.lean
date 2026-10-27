module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.CoordsAuxData
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.CoordsAuxComm
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.CoordsAuxDescent

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open scoped commutatorElement

set_option linter.unusedSectionVars false


namespace CoordsAux

section Class

variable (c : TwClass) {K : Type} [Field K] [Finite K] (D : LangLevi c.tag K c.w)

private theorem exists_list_of_subset_roots (S : Set (Fin c.tag.rank → ℤ))
    (hS : ∀ β ∈ S, IsRoot c.tag β) :
    ∃ l : List (Fin c.tag.rank → ℤ), l.Nodup ∧ ∀ β, β ∈ l ↔ β ∈ S :=
  exists_list_of_finite ((finite_setOf_isRoot c.tag).subset fun β hβ => hS β hβ)

private theorem Bset_isRoot {β : Fin c.tag.rank → ℤ} (h : β ∈ Bset c) : IsRoot c.tag β :=
  (CoordAux.mem_Deg1.1 h.1).1

private theorem Uθ_mul_comm {u u' : ModGL c.tag D.L} (hu : u ∈ Uθ c.tag D.L)
    (hu' : u' ∈ Uθ c.tag D.L) : u * u' = u' * u := by
  obtain ⟨a, rfl⟩ := mem_rootSubgroup.1 hu
  obtain ⟨b, rfl⟩ := mem_rootSubgroup.1 hu'
  rw [← pinnedX_add, ← pinnedX_add, add_comm]

private theorem Uθ_mem_posUnipotent {u : ModGL c.tag D.L} (hu : u ∈ Uθ c.tag D.L) :
    u ∈ posUnipotent c.tag D.L := by
  obtain ⟨a, rfl⟩ := mem_rootSubgroup.1 hu
  exact pinnedX_mem_rootSpan (S := {α | IsRoot c.tag α ∧ 0 < height α})
    ⟨isRoot_highRoot _, height_highRoot_pos _⟩ a

theorem commute_of_disjoint_support {q q' : ModGL c.tag K} (hq : q ∈ Qθ c.tag K)
    (hq' : q' ∈ Qθ c.tag K) (hs : ∀ β, κ D q β ≠ 0 → β ∈ Bset c)
    (hs' : ∀ β, κ D q' β ≠ 0 → β ∉ Bset c) : q * q' = q' * q := by
  classical
  obtain ⟨lB, hndB, hlB⟩ := exists_list_of_subset_roots c (Bset c) fun β hβ => Bset_isRoot c hβ
  obtain ⟨lM, hndM, hlM⟩ := exists_list_of_subset_roots c {β | β ∈ Deg1 c.tag ∧ β ∉ Bset c}
    fun β hβ => (CoordAux.mem_Deg1.1 hβ.1).1
  obtain ⟨u, hu, he⟩ := exists_prodX_of_support (K := D.L) hndB
    (fun β hβ => ((hlB β).1 hβ).1) (Ψ_Qθ D hq) (fun ν hν => by
      by_contra h
      exact hν ((hlB ν).2 (hs ν h)))
  obtain ⟨u', hu', he'⟩ := exists_prodX_of_support (K := D.L) hndM
    (fun β hβ => ((hlM β).1 hβ).1) (Ψ_Qθ D hq') (fun ν hν => by
      by_contra h
      refine hν ((hlM ν).2 ⟨?_, hs' ν h⟩)
      by_contra hD
      exact h (κ_support D hq' hD))
  set P := CoordAux.prodX lB (heisCoord c.tag D.L (Ψ D q)) with hP
  set P' := CoordAux.prodX lM (heisCoord c.tag D.L (Ψ D q')) with hP'
  have hnot : ∀ β ∈ lB, ∀ γ ∈ lM, β + γ ∉ rootFinset c.tag := by
    intro β hβ γ hγ hr
    have hdeg : (β + γ) (iθ c.tag) = 2 := by
      rw [Pi.add_apply, (CoordAux.mem_Deg1.1 ((hlB β).1 hβ).1).2,
        (CoordAux.mem_Deg1.1 ((hlM γ).1 hγ).1).2]
      norm_num
    have hθ : β + γ = highRoot c.tag :=
      CoordAux.eq_highRoot_of_two_le (mem_rootFinset.1 hr) (by omega)
    have hγ' : γ = highRoot c.tag - β := by rw [← hθ]; abel
    obtain ⟨hd, hS₁⟩ := partner_mem c ((hlB β).1 hβ).1 ((hlB β).1 hβ).2
    exact ((hlM γ).1 hγ).2 ⟨by rw [hγ']; exact hd, by rw [hγ']; exact hS₁⟩
  have hPP' : P * P' = P' * P := by
    refine Commute.eq ?_
    have key : ∀ l : List (Fin c.tag.rank → ℤ), (∀ γ ∈ l, γ ∈ lM) →
        Commute P (CoordAux.prodX l (heisCoord c.tag D.L (Ψ D q'))) := by
      intro l
      induction l with
      | nil => intro _; rw [CoordAux.prodX_nil]; exact Commute.one_right _
      | cons γ l ih =>
        intro hl
        rw [CoordAux.prodX_cons]
        refine Commute.mul_right ?_ (ih fun α hα => hl α (List.mem_cons_of_mem _ hα))
        exact CoordAux.commute_prodX fun β hβ _ => CoordAux.commute_pinnedX_of_not_isRoot_add
          ((hlB β).1 hβ).1 ((hlM γ).1 (hl γ List.mem_cons_self)).1
          (hnot β hβ γ (hl γ List.mem_cons_self)) _ _
    exact key lM fun γ hγ => hγ
  have hPpos : P ∈ posUnipotent c.tag D.L :=
    CoordAux.prodX_mem_pos (fun β hβ => ((hlB β).1 hβ).1) _
  have hP'pos : P' ∈ posUnipotent c.tag D.L :=
    CoordAux.prodX_mem_pos (fun β hβ => ((hlM β).1 hβ).1) _
  have hcomm : Ψ D q * Ψ D q' = Ψ D q' * Ψ D q := by
    rw [he, he']
    change u * P * (u' * P') = u' * P' * (u * P)
    calc u * P * (u' * P') = u * (P * u') * P' := by simp only [mul_assoc]
      _ = u * (u' * P) * P' := by rw [CoordAux.Uθ_comm hu' hPpos]
      _ = (u * u') * (P * P') := by simp only [mul_assoc]
      _ = (u' * u) * (P' * P) := by rw [Uθ_mul_comm c D hu hu', hPP']
      _ = u' * (u * P') * P := by simp only [mul_assoc]
      _ = u' * (P' * u) * P := by rw [CoordAux.Uθ_comm hu hP'pos]
      _ = u' * P' * (u * P) := by simp only [mul_assoc]
  have h2 : Ψ D (q * q') = Ψ D (q' * q) := by rw [Ψ_mul, Ψ_mul, hcomm]
  have h3 : bc D (q * q') = bc D (q' * q) := by
    unfold Ψ at h2
    simpa using h2
  exact baseChangeGL_injective (algebraMap K D.L) h3

private theorem smul_mem_Bset_iff {β : Fin c.tag.rank → ℤ} (hβ : β ∈ Deg1 c.tag) :
    c.w • β ∈ Bset c ↔ β ∈ Bset c := by
  have hw := w_smul_highRoot c
  have hβr : IsRoot c.tag β := (CoordAux.mem_Deg1.1 hβ).1
  have hwβ : c.w • β ∈ Deg1 c.tag :=
    CoordAux.mem_Deg1.2 ⟨IsRoot.smul hβr c.w, by
      rw [degθ_smul_of_fix hw]
      exact (CoordAux.mem_Deg1.1 hβ).2⟩
  unfold Bset
  simp only [Set.mem_setOf_eq]
  rw [w_smul_mem_S₁_iff c hβr]
  exact ⟨fun h => ⟨hβ, h.2⟩, fun h => ⟨hwβ, h.2⟩⟩

open Classical in
private theorem isSig_pB {ε : (Fin c.tag.rank → ℤ) → D.L} {v : (Fin c.tag.rank → ℤ) → D.L}
    (hv : IsSig D ε v) :
    IsSig D ε (fun β => if β ∈ Bset c then v β else 0) := by
  refine ⟨fun β hβ => ?_, fun β hβ => ?_⟩
  · dsimp only
    rw [if_neg (fun h => hβ h.1)]
  · dsimp only
    by_cases hB : β ∈ Bset c
    · rw [if_pos hB, if_pos ((smul_mem_Bset_iff c hβ).2 hB), hv.2 β hβ]
    · rw [if_neg hB, if_neg (fun h => hB ((smul_mem_Bset_iff c hβ).1 h)), map_zero, mul_zero]

theorem eq_zero_of_central {ε : (Fin c.tag.rank → ℤ) → D.L} (hε : MonomialProp c.w ε)
    {q : ModGL c.tag K} (hq : q ∈ Qθ c.tag K) (hs : ∀ β, κ D q β ≠ 0 → β ∈ Bset c)
    (hc : ∀ r ∈ Qθ c.tag K, (∀ β, κ D r β ≠ 0 → β ∈ Bset c) → q * r = r * q) :
    κ D q = 0 := by
  classical
  have hw := w_smul_highRoot c
  obtain ⟨lB, hndB, hlB⟩ := exists_list_of_subset_roots c (Bset c) fun β hβ => Bset_isRoot c hβ
  have hNex : ∀ β : Fin c.tag.rank → ℤ, ∃ N : D.L, β ∈ Bset c → (N * N = 1 ∧
      ∀ a b : D.L, ⁅pinnedX c.tag D.L β a, pinnedX c.tag D.L (highRoot c.tag - β) b⁆ =
        pinnedX c.tag D.L (highRoot c.tag) (N * a * b)) := by
    intro β
    by_cases hβ : β ∈ Bset c
    · obtain ⟨N, hN1, hN2⟩ := exists_pair_comm c hβ.1 hβ.2 D.L
      exact ⟨N, fun _ => ⟨hN1, hN2⟩⟩
    · exact ⟨0, fun h => absurd h hβ⟩
  choose N hN using hNex
  set R : Set (ModGL c.tag K) := {r | r ∈ Qθ c.tag K ∧ ∀ β, κ D r β ≠ 0 → β ∈ Bset c} with hR
  set 𝒮 := Submodule.span D.L (κ D '' R) with h𝒮
  have hproj : ∀ v ∈ Submodule.span D.L (κ D '' (Qθ c.tag K : Set (ModGL c.tag K))),
      (fun β => if β ∈ Bset c then v β else 0) ∈ 𝒮 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨r, hr, rfl⟩ := hx
      obtain ⟨r', hr'Q, hr'⟩ := exists_lift D hw hε (isSig_pB c D (κ_isSig D hw hε hr))
      refine Submodule.subset_span ⟨r', ⟨hr'Q, fun β hβ => ?_⟩, hr'⟩
      by_contra hB
      apply hβ
      rw [hr']
      simp [hB]
    | zero =>
      convert zero_mem 𝒮 using 1
      funext β
      simp
    | add x y _ _ hx hy =>
      convert add_mem hx hy using 1
      funext β
      by_cases h : β ∈ Bset c <;> simp [h]
    | smul a x _ hx =>
      convert Submodule.smul_mem 𝒮 a hx using 1
      funext β
      by_cases h : β ∈ Bset c <;> simp [h]
  have hunit : ∀ γ ∈ Bset c, (Pi.single γ (1 : D.L) : (Fin c.tag.rank → ℤ) → D.L) ∈ 𝒮 := by
    intro γ hγ
    have hx : D.g * pinnedX c.tag D.L γ 1 * D.g⁻¹ ∈ Qθ c.tag D.L :=
      Lθ_conj_mem_Qθ D.g_mem (pinnedX_mem_Qθ_of_mem_Deg1 hγ.1 1)
    have hd := desc D hx
    have e : D.g⁻¹ * (D.g * pinnedX c.tag D.L γ 1 * D.g⁻¹) * D.g = pinnedX c.tag D.L γ 1 := by
      group
    rw [e, (heisCoord_spec c.tag D.L).pinnedX_deg1 γ hγ.1] at hd
    have := hproj _ hd
    convert this using 1
    funext β
    by_cases hβ : β = γ
    · subst hβ
      simp [hγ]
    · rw [Pi.single_eq_of_ne hβ]
      by_cases hB : β ∈ Bset c <;> simp [hB]
  let φ : ((Fin c.tag.rank → ℤ) → D.L) → D.L := fun v =>
    ∑ β ∈ lB.toFinset, if highRoot c.tag - β ∈ lB then
      N β * κ D q β * v (highRoot c.tag - β) else 0
  have hφr : ∀ r ∈ R, φ (κ D r) = 0 := by
    intro r hr
    obtain ⟨hrQ, hrs⟩ := hr
    have hcomm : Ψ D q * Ψ D r = Ψ D r * Ψ D q := by rw [← Ψ_mul, ← Ψ_mul, hc r hrQ hrs]
    obtain ⟨u, hu, he⟩ := exists_prodX_of_support (K := D.L) hndB
      (fun β hβ => ((hlB β).1 hβ).1) (Ψ_Qθ D hq) (fun ν hν => by
        by_contra h
        exact hν ((hlB ν).2 (hs ν h)))
    obtain ⟨u', hu', he'⟩ := exists_prodX_of_support (K := D.L) hndB
      (fun β hβ => ((hlB β).1 hβ).1) (Ψ_Qθ D hrQ) (fun ν hν => by
        by_contra h
        exact hν ((hlB ν).2 (hrs ν h)))
    set P := CoordAux.prodX lB (heisCoord c.tag D.L (Ψ D q)) with hP
    set P' := CoordAux.prodX lB (heisCoord c.tag D.L (Ψ D r)) with hP'
    have hPpos : P ∈ posUnipotent c.tag D.L :=
      CoordAux.prodX_mem_pos (fun β hβ => ((hlB β).1 hβ).1) _
    have hP'pos : P' ∈ posUnipotent c.tag D.L :=
      CoordAux.prodX_mem_pos (fun β hβ => ((hlB β).1 hβ).1) _
    have hL : Ψ D q * Ψ D r = (u * u') * (P * P') := by
      rw [he, he']
      change u * P * (u' * P') = _
      calc u * P * (u' * P') = u * (P * u') * P' := by simp only [mul_assoc]
        _ = u * (u' * P) * P' := by rw [CoordAux.Uθ_comm hu' hPpos]
        _ = (u * u') * (P * P') := by simp only [mul_assoc]
    have hR' : Ψ D r * Ψ D q = (u * u') * (P' * P) := by
      rw [he, he']
      change u' * P' * (u * P) = _
      calc u' * P' * (u * P) = u' * (P' * u) * P := by simp only [mul_assoc]
        _ = u' * (u * P') * P := by rw [CoordAux.Uθ_comm hu hP'pos]
        _ = (u' * u) * (P' * P) := by simp only [mul_assoc]
        _ = (u * u') * (P' * P) := by rw [Uθ_mul_comm c D hu' hu]
    have hPP' : P * P' = P' * P := mul_left_cancel (a := u * u') (by rw [← hL, ← hR', hcomm])
    have hcm : ⁅P, P'⁆ = 1 := commutatorElement_eq_one_iff_commute.2 hPP'
    have hpair : ∀ β ∈ lB, ∀ γ ∈ lB, β + γ = highRoot c.tag → ∀ a b : D.L,
        ⁅pinnedX c.tag D.L β a, pinnedX c.tag D.L γ b⁆ =
          pinnedX c.tag D.L (highRoot c.tag) (N β * a * b) := by
      intro β hβ γ _ hβγ a b
      have hγ : γ = highRoot c.tag - β := by rw [← hβγ]; abel
      subst hγ
      exact ((hN β ((hlB β).1 hβ)).2 a b)
    have hform := comm_prodX_prodX hndB hndB (fun β hβ => ((hlB β).1 hβ).1)
      (fun β hβ => ((hlB β).1 hβ).1) N hpair (heisCoord c.tag D.L (Ψ D q))
      (heisCoord c.tag D.L (Ψ D r))
    rw [← hP, ← hP', hcm] at hform
    have hz : pinnedX c.tag D.L (highRoot c.tag) (φ (κ D r)) =
        pinnedX c.tag D.L (highRoot c.tag) 0 := by
      rw [pinnedX_zero, hform]
      rfl
    exact pinnedX_injective c.tag D.L (highRoot c.tag) hz
  have hφ𝒮 : ∀ v ∈ 𝒮, φ v = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨r, hr, rfl⟩ := hx
      exact hφr r hr
    | zero => simp [φ]
    | add x y _ _ hx hy =>
      have : φ (x + y) = φ x + φ y := by
        simp only [φ, Pi.add_apply, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun β _ => ?_
        split_ifs <;> ring
      rw [this, hx, hy, add_zero]
    | smul a x _ hx =>
      have : φ (a • x) = a * φ x := by
        simp only [φ, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun β _ => ?_
        split_ifs <;> ring
      rw [this, hx, mul_zero]
  have hcoord : ∀ γ ∈ Bset c, κ D q (highRoot c.tag - γ) = 0 := by
    intro γ hγ
    obtain ⟨hdeg, hS⟩ := partner_mem c hγ.1 hγ.2
    have hθγ : highRoot c.tag - γ ∈ Bset c := ⟨hdeg, hS⟩
    have h0 := hφ𝒮 _ (hunit γ hγ)
    simp only [φ] at h0
    rw [Finset.sum_eq_single (highRoot c.tag - γ)] at h0
    · rw [if_pos (by rw [hlB]; simpa using hγ), sub_sub_cancel, Pi.single_eq_same, mul_one] at h0
      have hNN := (hN _ hθγ).1
      have hne : N (highRoot c.tag - γ) ≠ 0 := by
        intro h
        rw [h, zero_mul] at hNN
        exact zero_ne_one hNN
      exact (mul_eq_zero.1 h0).resolve_left hne
    · intro β _ hβ
      have hne : highRoot c.tag - β ≠ γ := fun h => hβ (by rw [← h]; abel)
      split_ifs
      · rw [Pi.single_eq_of_ne hne, mul_zero]
      · rfl
    · intro h
      exact absurd ((List.mem_toFinset).2 ((hlB _).2 hθγ)) h
  funext β
  by_cases hβ : β ∈ Bset c
  · obtain ⟨hdeg, hS⟩ := partner_mem c hβ.1 hβ.2
    have := hcoord (highRoot c.tag - β) ⟨hdeg, hS⟩
    rwa [sub_sub_cancel] at this
  · by_contra h
    exact hβ (hs β h)

end Class

end CoordsAux

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
