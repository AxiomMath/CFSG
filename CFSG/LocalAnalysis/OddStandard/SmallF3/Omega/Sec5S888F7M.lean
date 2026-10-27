module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Cov3Frame
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5AbsQuot
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5FrameType
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFClassModelAux1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup Equiv

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {c : ZMod 3}

private lemma f7_twoRes_mono {G : Type} [Group G] {K₁ K₂ : Subgroup G} (h : K₁ ≤ K₂) :
    twoRes K₁ ≤ twoRes K₂ := by
  unfold twoRes
  exact Subgroup.closure_mono fun g hg => ⟨h hg.1, hg.2⟩

private lemma f7_cycle_pow3 :
    ∀ x y w : Fin 6, x ≠ y → x ≠ w → y ≠ w → (swap x y * swap x w) ^ 3 = 1 := by
  decide +kernel

private lemma f7_cycle_sign :
    ∀ x y w : Fin 6, x ≠ y → x ≠ w → y ≠ w → Equiv.Perm.sign (swap x y * swap x w) = 1 := by
  decide +kernel

private lemma f7_cycle_symmDiff :
    ∀ x y w : Fin 6, x ≠ y → x ≠ w → y ≠ w →
      symmDiff ({x, y} : Finset (Fin 6))
          (({x, y} : Finset (Fin 6)).map (swap x y * swap x w).toEmbedding) =
        (({x, y} : Finset (Fin 6)).map (swap x y * swap x w).toEmbedding).map
          (swap x y * swap x w).toEmbedding := by
  decide +kernel

private lemma f7_cycle_in :
    ∀ x y w i : Fin 6, x ≠ y → x ≠ w → y ≠ w → (i = x ∨ i = y ∨ i = w) →
      ((swap x y * swap x w) i = x ∨ (swap x y * swap x w) i = y ∨
        (swap x y * swap x w) i = w) := by
  decide +kernel

private lemma f7_cycle_out :
    ∀ x y w i : Fin 6, x ≠ y → x ≠ w → y ≠ w → i ≠ x → i ≠ y → i ≠ w →
      (swap x y * swap x w) i = i := by
  decide +kernel

private lemma f7_map_cycle_eq {x y w : Fin 6} (hxy : x ≠ y) (hxw : x ≠ w) (hyw : y ≠ w)
    {J : Finset (Fin 6)} (hx : x ∈ J) (hy : y ∈ J) (hw : w ∈ J) :
    J.map (swap x y * swap x w).toEmbedding = J := by
  apply Finset.map_eq_of_subset
  intro i hi
  obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
  by_cases hjx : j = x ∨ j = y ∨ j = w
  · rcases f7_cycle_in x y w j hxy hxw hyw hjx with h | h | h <;>
      (rw [Equiv.coe_toEmbedding, h]; assumption)
  · simp only [not_or] at hjx
    rw [Equiv.coe_toEmbedding, f7_cycle_out x y w j hxy hxw hyw hjx.1 hjx.2.1 hjx.2.2]
    exact hj

private lemma f7_pair_mem_twoRes (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c)
    {J : Finset (Fin 6)} {x y w : Fin 6} (hxy : x ≠ y) (hxw : x ≠ w) (hyw : y ≠ w)
    (hx : x ∈ J) (hy : y ∈ J) (hw : w ∈ J) :
    fr.signChange {x, y} ∈
      twoRes (omegaGroup hQ ⊓ centralizer ({fr.signChange J} : Set (OGroup Q))) := by
  have hσalt : (swap x y * swap x w) ∈ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    exact f7_cycle_sign x y w hxy hxw hyw
  have hp : fr.permOrth (swap x y * swap x w) ∈
      omegaGroup hQ ⊓ centralizer ({fr.signChange J} : Set (OGroup Q)) :=
    ⟨fr.permOrth_mem_omegaGroup hQ hσalt, Subgroup.mem_centralizer_singleton_iff.mpr
      (fr.permOrth_comm_signChange (f7_map_cycle_eq hxy hxw hyw hx hy hw))⟩
  have hpair : Even ({x, y} : Finset (Fin 6)).card := by
    rw [Finset.card_pair hxy]
    exact even_two
  have ht : fr.signChange ({x, y} : Finset (Fin 6)) ∈
      omegaGroup hQ ⊓ centralizer ({fr.signChange J} : Set (OGroup Q)) :=
    ⟨fr.signChange_mem_omegaGroup hQ {x, y} hpair,
      Subgroup.mem_centralizer_singleton_iff.mpr (fr.signChange_comm {x, y} J)⟩
  exact fr.signChange_mem_twoRes (f7_cycle_pow3 x y w hxy hxw hyw) hp ht
    (f7_cycle_symmDiff x y w hxy hxw hyw)

private lemma f7_even_mem_twoRes (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c)
    {J J₄ : Finset (Fin 6)} (hJ₄ : J₄ ⊆ J) (hc4 : J₄.card = 4) {A : Finset (Fin 6)}
    (hA : A ⊆ J₄) (hAe : Even A.card) :
    fr.signChange A ∈
      twoRes (omegaGroup hQ ⊓ centralizer ({fr.signChange J} : Set (OGroup Q))) := by
  have hpair : ∀ P : Finset (Fin 6), P ⊆ J₄ → P.card = 2 →
      fr.signChange P ∈
        twoRes (omegaGroup hQ ⊓ centralizer ({fr.signChange J} : Set (OGroup Q))) := by
    intro P hP hP2
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hP2
    obtain ⟨w, hw, hwn⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := ({x, y} : Finset (Fin 6)))
      (t := J₄) (by rw [Finset.card_pair hxy, hc4]; omega)
    have hwx : x ≠ w := fun h => hwn (by simp [h])
    have hwy : y ≠ w := fun h => hwn (by simp [h])
    exact f7_pair_mem_twoRes hQ fr hxy hwx hwy (hJ₄ (hP (by simp))) (hJ₄ (hP (by simp)))
      (hJ₄ hw)
  have hle : A.card ≤ 4 := hc4 ▸ Finset.card_le_card hA
  obtain ⟨m, hm⟩ := hAe
  have hm3 : m = 0 ∨ m = 1 ∨ m = 2 := by omega
  rcases hm3 with rfl | rfl | rfl
  · have h0 : A = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [h0, fr.signChange_empty]
    exact (twoRes _).one_mem
  · exact hpair A hA (by omega)
  · have hAeq : A = J₄ := Finset.eq_of_subset_of_card_le hA (by omega)
    subst hAeq
    obtain ⟨P, hPA, hPc⟩ := Finset.exists_subset_card_eq (show 2 ≤ A.card by omega)
    have hdc : (A \ P).card = 2 := by
      rw [Finset.card_sdiff_of_subset hPA]
      omega
    have hsd : symmDiff P (A \ P) = A := by
      ext i
      simp only [Finset.mem_symmDiff, Finset.mem_sdiff]
      constructor
      · rintro (⟨h1, _⟩ | ⟨⟨h1, _⟩, _⟩)
        · exact hPA h1
        · exact h1
      · intro h
        by_cases hi : i ∈ P
        · exact Or.inl ⟨hi, fun h' => h'.2 hi⟩
        · exact Or.inr ⟨⟨h, hi⟩, hi⟩
    have h1 := hpair P hPA hPc
    have h2 := hpair (A \ P) Finset.sdiff_subset hdc
    rw [← hsd, ← fr.signChange_mul]
    exact (twoRes _).mul_mem h1 h2

private lemma f7_toProj_mem_twoRes (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c)
    {J J₄ : Finset (Fin 6)} (hJ₄ : J₄ ⊆ J) (hc4 : J₄.card = 4) {A : Finset (Fin 6)}
    (hA : A ⊆ J₄) (hAe : Even A.card) :
    toProj Q (fr.signChange A) ∈
      twoRes (omegaProj hQ ⊓ centralizer ({toProj Q (fr.signChange J)} : Set (ProjOrth Q))) := by
  have h := f7_even_mem_twoRes hQ fr hJ₄ hc4 hA hAe
  have hker2 : ∀ k ∈ (toProj Q).ker, k * k = 1 := by
    intro k hk
    rw [QuotientGroup.ker_mk'] at hk
    rcases mem_piGroup_iff.mp hk with rfl | rfl
    · simp
    · exact piOrth_mul_self
  have hmem : toProj Q (fr.signChange A) ∈
      (twoRes (omegaGroup hQ ⊓ centralizer ({fr.signChange J} : Set (OGroup Q)))).map
        (toProj Q) := Subgroup.mem_map_of_mem _ h
  rw [map_twoRes (toProj Q) hker2] at hmem
  refine f7_twoRes_mono ?_ hmem
  rintro _ ⟨h', hmem', rfl⟩
  obtain ⟨hΩ, hc⟩ := Subgroup.mem_inf.mp hmem'
  refine ⟨(mem_omegaProj_iff hQ).mpr ⟨h', hΩ, rfl⟩, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff] at hc
  show toProj Q h' ∈ centralizer ({toProj Q (fr.signChange J)} : Set (ProjOrth Q))
  rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hc]

private lemma f7_toProj_inj (fr : NFrame Q (Fin 6) c) {J₄ : Finset (Fin 6)} (hc4 : J₄.card = 4)
    {A B : Finset (Fin 6)} (hA : A ⊆ J₄) (hB : B ⊆ J₄)
    (h : toProj Q (fr.signChange A) = toProj Q (fr.signChange B)) : A = B := by
  rcases toProj_eq_or_eq_piOrth h with h1 | h1
  · exact fr.signChange_injective h1
  · exfalso
    rw [← fr.signChange_univ, fr.signChange_mul] at h1
    have hAeq : A = symmDiff Finset.univ B := fr.signChange_injective h1
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := J₄)
      (t := (Finset.univ : Finset (Fin 6))) (by rw [hc4, Finset.card_univ, Fintype.card_fin]; omega)
    have hiB : i ∉ B := fun hb => hi (hB hb)
    have hiA : i ∈ A := by
      rw [hAeq, Finset.mem_symmDiff]
      exact Or.inl ⟨Finset.mem_univ i, hiB⟩
    exact hi (hA hiA)

private lemma f7_card_even_subsets :
    ∀ J₄ : Finset (Fin 6), J₄.card = 4 →
      8 ≤ (J₄.powerset.filter (fun A => Even A.card)).card := by
  decide +kernel

theorem f7_exists_big (fr : NFrame Q (Fin 6) c) {J : Finset (Fin 6)} (hJe : Even J.card) :
    ∃ J' : Finset (Fin 6), 4 ≤ J'.card ∧
      toProj Q (fr.signChange J') = toProj Q (fr.signChange J) := by
  by_cases h : 4 ≤ J.card
  · exact ⟨J, h, rfl⟩
  · refine ⟨Jᶜ, ?_, ?_⟩
    · obtain ⟨m, hm⟩ := hJe
      have h6 : Jᶜ.card = 6 - J.card := by rw [Finset.card_compl, Fintype.card_fin]
      omega
    · have hc : fr.signChange Jᶜ = piOrth Q * fr.signChange J := by
        rw [← fr.signChange_univ, fr.signChange_mul]
        congr 1
        ext i
        simp [Finset.mem_symmDiff]
      rw [hc, map_mul, toProj_piOrth, one_mul]

theorem f7_model (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c) {J : Finset (Fin 6)}
    (hJ4 : 4 ≤ J.card) :
    ∃ P : Finset (Finset (Fin 6)), 8 ≤ P.card ∧
      (∀ A ∈ P, Even A.card ∧ toProj Q (fr.signChange A) ∈
        twoRes (omegaProj hQ ⊓ centralizer ({toProj Q (fr.signChange J)} : Set (ProjOrth Q)))) ∧
      ∀ A ∈ P, ∀ B ∈ P, toProj Q (fr.signChange A) = toProj Q (fr.signChange B) → A = B := by
  obtain ⟨J₄, hJ₄, hc4⟩ := Finset.exists_subset_card_eq hJ4
  refine ⟨J₄.powerset.filter (fun A => Even A.card), f7_card_even_subsets J₄ hc4, ?_, ?_⟩
  · intro A hA
    rw [Finset.mem_filter, Finset.mem_powerset] at hA
    exact ⟨hA.2, f7_toProj_mem_twoRes hQ fr hJ₄ hc4 hA.1 hA.2⟩
  · intro A hA B hB h
    rw [Finset.mem_filter, Finset.mem_powerset] at hA hB
    exact f7_toProj_inj fr hc4 hA.1 hB.1 h

end CFSG.OddStandard.SmallF3.Omega
