module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.A5Pair
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.CliqueIso
public import CFSG.HardMathSupport.RichardWeiss.Proving.ThreeCycleTransport
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.Closure

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation

open CFSG.CGT.PushingUpLit.CGT6

variable {S : Type} [Group S]

theorem exists_noncommuting_outside (hS : IsSimpleGroup S) {Y : Subgroup S}
    (hY : Nat.card Y = 3) {F : Finset S} (hFD : ∀ p ∈ F, IsDGen Y p) (hne : F.Nonempty)
    (htop : Subgroup.closure (F : Set S) ≠ ⊤) :
    ∃ y p : S, IsDGen Y y ∧ y ∉ Subgroup.closure (F : Set S) ∧ p ∈ F ∧ p * y ≠ y * p := by
  by_contra hcon
  push Not at hcon
  set M := Subgroup.closure (F : Set S) with hM
  set N := Subgroup.closure {y : S | IsDGen Y y} with hN
  have hNnormal : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    induction hn using Subgroup.closure_induction with
    | mem y hy =>
      refine Subgroup.subset_closure ?_
      have := (show IsDGen Y y from hy).conj g⁻¹
      simpa using this
    | one => simp
    | mul a b _ _ ha hb =>
      have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      rw [this]; exact Subgroup.mul_mem _ ha hb
    | inv a _ ha =>
      have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
      rw [this]; exact Subgroup.inv_mem _ ha
  obtain ⟨a, ha3, hag⟩ := CFSG.HardMathSupport.RichardWeiss.Proving.exists_gen_map_conj hY 1
  have hDa : IsDGen Y a := ⟨1, hag.symm⟩
  have hNtop : N = ⊤ := by
    rcases hS.eq_bot_or_eq_top_of_normal N with h | h
    · exfalso
      have : a ∈ N := Subgroup.subset_closure hDa
      rw [h, Subgroup.mem_bot] at this
      exact hDa.ne_one hY this
    · exact h
  have hnorm : ∀ y, IsDGen Y y → y ∈ Subgroup.normalizer (M : Set S) := by
    intro y hy
    by_cases hyM : y ∈ M
    · exact Subgroup.le_normalizer hyM
    · have hcomm : M ≤ Subgroup.centralizer ({y} : Set S) := by
        rw [hM, Subgroup.closure_le]
        intro p hp
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        rw [hz]; exact (hcon y p hy hyM hp).symm
      have hyc : ∀ m ∈ M, y * m * y⁻¹ = m := by
        intro m hm
        have := Subgroup.mem_centralizer_iff.1 (hcomm hm) y rfl
        rw [this]; group
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh; rw [hyc h hh]; exact hh
      · intro hh
        have h2 := hyc _ hh
        have : y * h * y⁻¹ = h := by
          have := congrArg (fun x => y⁻¹ * x * y) h2
          simpa [mul_assoc] using this
        rw [← this]; exact hh
  have hle : N ≤ Subgroup.normalizer (M : Set S) := by
    rw [hN, Subgroup.closure_le]
    intro y hy
    exact hnorm y hy
  have hMnormal : M.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hNtop]
    exact hle
  rcases hS.eq_bot_or_eq_top_of_normal M with h | h
  · obtain ⟨p, hp⟩ := hne
    have : p ∈ M := Subgroup.subset_closure hp
    rw [h, Subgroup.mem_bot] at this
    exact (hFD p hp).ne_one hY this
  · exact htop h

theorem stellmacherSixOneThree_of_A5Pair
    [Finite S]
    (hS : IsSimpleGroup S) {Y : Subgroup S}
    (hY : Nat.card Y = 3) (hpair : ∀ g h : S, IsZ3E9A4A5 ↥(pairGen Y g h))
    (hA5 : ∃ g h : S, Nonempty (↥(pairGen Y g h) ≃* alternatingGroup (Fin 5))) :
    ∃ n : ℕ, 5 ≤ n ∧ ∃ e : S ≃* alternatingGroup (Fin n), ∃ c : alternatingGroup (Fin n),
      (c : Equiv.Perm (Fin n)).IsThreeCycle ∧ Y.map e.toMonoidHom = Subgroup.zpowers c := by
  classical
  have hD := orderThreeClass_isDGen hY hpair
  obtain ⟨g, h, ⟨e⟩⟩ := hA5
  obtain ⟨F0, hF0, hcard0⟩ := exists_clique_three_of_pairGen_iso hY hpair e
  have : Fintype S := Fintype.ofFinite S
  let 𝒞 : Finset (Finset S) := Finset.univ.filter (IsClique (IsDGen Y))
  obtain ⟨F, hF𝒞, hFmax⟩ := Finset.exists_max_image 𝒞 Finset.card ⟨F0, by simp [𝒞, hF0]⟩
  have hFcl : IsClique (IsDGen Y) F := (Finset.mem_filter.1 hF𝒞).2
  have hMax : IsMaxClique (IsDGen Y) F := ⟨hFcl, fun F' hF' => hFmax F' (by simp [𝒞, hF'])⟩
  have hcard : 3 ≤ F.card := hcard0.trans (hFmax F0 (by simp [𝒞, hF0]))
  have hne : F.Nonempty := Finset.card_pos.1 (by omega)
  have htop := hMax.closure_eq_top hD hcard
    (fun hne' => exists_noncommuting_outside hS hY hFcl.mem hne hne')
  obtain ⟨n, hn, e', h3⟩ := exists_alt_iso_of_clique hD hFcl hcard htop
  obtain ⟨p, hp⟩ := hne
  obtain ⟨g', hg'⟩ := hFcl.mem p hp
  have hYeq : Y = Subgroup.zpowers (g'⁻¹ * p * g') := by
    have hcomp : (MulAut.conj g'⁻¹).toMonoidHom.comp (MulAut.conj g').toMonoidHom =
        MonoidHom.id S := by
      ext x; simp [MulAut.conj_apply, mul_assoc]
    have : (Subgroup.zpowers p).map (MulAut.conj g'⁻¹).toMonoidHom = Y := by
      rw [hg', Subgroup.map_map, hcomp, Subgroup.map_id]
    rw [← this, MonoidHom.map_zpowers]
    simp
  refine ⟨n, hn, e', e' (g'⁻¹ * p * g'), ?_, ?_⟩
  · have key := Equiv.Perm.cycleType_conj (σ := ((e' p : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)))
      (τ := ((e' g'⁻¹ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)))
    have hcoe : ((e' (g'⁻¹ * p * g') : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) =
        ((e' g'⁻¹ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) *
          ((e' p : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) *
            ((e' g'⁻¹ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n))⁻¹ := by
      simp [map_mul, map_inv]
    show _ = _
    rw [hcoe, key]
    exact h3 p hp
  · refine CFSG.HardMathSupport.RichardWeiss.Proving.map_eq_zpowers_of_isThreeCycle e' hY ?_ ?_
    · have key := Equiv.Perm.cycleType_conj
        (σ := ((e' p : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)))
        (τ := ((e' g'⁻¹ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)))
      have hcoe : ((e' (g'⁻¹ * p * g') : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) =
          ((e' g'⁻¹ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) *
            ((e' p : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) *
              ((e' g'⁻¹ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n))⁻¹ := by
        simp [map_mul, map_inv]
      show _ = _
      rw [hcoe, key]
      exact h3 p hp
    · refine ⟨g'⁻¹ * p * g', ?_, rfl⟩
      rw [hYeq]
      exact Subgroup.mem_zpowers _

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation

end
