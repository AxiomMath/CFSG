module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FSmallRed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS07I67

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.ComponentClassification.PerfectAutomorphisms
  (centerQuotientHom centerQuotientHom_injective)
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut)

section Glue

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem i141f_isPerfect_pQuot {p : ℕ} {A L : Subgroup Γ} (h : S10.InnDiagOn p A L) :
    Group.IsPerfect (PQuot p L) :=
  ⟨h.2.1⟩

theorem i141f_chevAut_eq_one_iff {p : ℕ} {L : Subgroup Γ} (hP : Group.IsPerfect (PQuot p L))
    {a : Γ} (ha : a ∈ Subgroup.normalizer (L : Set Γ)) :
    chevAut p L ⟨a, ha⟩ = 1 ↔ CentMod p L a := by
  haveI := hP
  rw [← chev_barAut_eq_one_iff_centMod ha]
  show centerQuotientHom (PQuot p L) (barAut p L ⟨a, ha⟩) = 1 ↔ _
  rw [← map_one (centerQuotientHom (PQuot p L))]
  exact (centerQuotientHom_injective (PQuot p L)).eq_iff

theorem i141f_center_pSimple {p : ℕ} {L : Subgroup Γ} (hP : Group.IsPerfect (PQuot p L)) :
    Subgroup.center (PSimple p L) = ⊥ := by
  haveI := hP
  exact Group.IsPerfect.center_quotient_center_eq_bot (PQuot p L)

theorem i141f_exists_elemAb {p : ℕ} (hp : p.Prime) {L A : Subgroup Γ} (hA : IsElemAbelian p A)
    (hInn : S10.InnDiagOn p A L)
    (hcard : p ^ 3 * Nat.card ↥(A ⊓ centModSubgroup p L) ≤ Nat.card A) :
    ∃ E : Subgroup (MulAut (PSimple p L)), IsElemAbelian p E ∧ p ^ 3 ≤ Nat.card E ∧
      ∀ ε ∈ E, ∃ (a : Γ) (ha : a ∈ Subgroup.normalizer (L : Set Γ)), a ∈ A ∧
        chevAut p L ⟨a, ha⟩ = ε := by
  have hBN : A ≤ Subgroup.normalizer (L : Set Γ) := hInn.1
  have hP := i141f_isPerfect_pQuot hInn
  let ψ : ↥A →* MulAut (PSimple p L) := (chevAut p L).comp (Subgroup.inclusion hBN)
  refine ⟨ψ.range, ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩, ?_, ?_⟩
  · rcases a with ⟨a, x, rfl⟩
    rcases b with ⟨b, y, rfl⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul, ← map_mul]
    rw [hA.1.is_comm.comm x y]
  · rintro _ ⟨x, rfl⟩
    have hxp : x ^ p = 1 := Subtype.ext (by simpa using hA.2 (x : Γ) x.2)
    rw [← map_pow, hxp, map_one]
  · have hkerle : Nat.card ψ.ker ≤ Nat.card ↥(A ⊓ centModSubgroup p L) := by
      have hsub : ψ.ker.map A.subtype ≤ A ⊓ centModSubgroup p L := by
        rintro _ ⟨b, hb, rfl⟩
        have h1 : chevAut p L ⟨(b : Γ), hBN b.2⟩ = 1 := hb
        exact Subgroup.mem_inf.2
          ⟨b.2, centMod_iff.1 ((i141f_chevAut_eq_one_iff hP (hBN b.2)).1 h1)⟩
      rw [← Subgroup.card_map_of_injective (f := A.subtype) Subtype.val_injective]
      exact Subgroup.card_le_of_le hsub
    have hlag := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
    have hquot : Nat.card (↥A ⧸ ψ.ker) = Nat.card ψ.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv
    have hpos : 0 < Nat.card ↥(A ⊓ centModSubgroup p L) := Nat.card_pos
    rw [hlag, hquot] at hcard
    have h2 := le_trans hcard (Nat.mul_le_mul_left _ hkerle)
    exact Nat.le_of_mul_le_mul_right h2 hpos
  · rintro _ ⟨x, rfl⟩
    exact ⟨(x : Γ), hBN x.2, x.2, rfl⟩

theorem i141RankFamily_of_autRank (F : TauCeti.CFSGIndex → Prop)
    (h : ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (S : Type) [Group S] [Finite S], catalogIs S F →
      ∀ E : Subgroup (MulAut S), IsElemAbelian p E → p ^ 3 ≤ Nat.card E → False) :
    I141RankFamily F := by
  intro p hp hp2 Γ _ _ L A hcat hA hInn hcard
  obtain ⟨E, hE, hE3, -⟩ := i141f_exists_elemAb hp hA hInn hcard
  exact h p hp hp2 (PSimple p L) hcat E hE hE3

end Glue

theorem i141f_elemAb_of_le_inn {S : Type} [Group S] [Finite S] {p : ℕ}
    (hZ : Subgroup.center S = ⊥) {E : Subgroup (MulAut S)} (hE : IsElemAbelian p E)
    (hin : E ≤ (MulAut.conj : S →* MulAut S).range) :
    ∃ P : Subgroup S, IsElemAbelian p P ∧ Nat.card P = Nat.card E := by
  have hinj : Function.Injective (MulAut.conj : S →* MulAut S) := conj_inj_of_center_bot hZ
  let P : Subgroup S := E.comap (MulAut.conj : S →* MulAut S)
  have hPmap : P.map (MulAut.conj : S →* MulAut S) = E := by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.2 hin
  have hPcard : Nat.card P = Nat.card E := by
    rw [← hPmap, Subgroup.card_map_of_injective hinj]
  have hPel : IsElemAbelian p P := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
    · apply Subtype.ext
      apply hinj
      simp only [Subgroup.coe_mul]
      rw [map_mul, map_mul]
      have := congrArg Subtype.val
        (hE.1.is_comm.comm (⟨MulAut.conj a.1, a.2⟩ : E) ⟨MulAut.conj b.1, b.2⟩)
      simpa only [Subgroup.coe_mul] using this
    · apply hinj
      rw [map_pow, map_one]
      exact hE.2 (MulAut.conj a) ha
  exact ⟨P, hPel, hPcard⟩

theorem i141f_exists_cube {M : Type} [Group M] [Finite M] {p : ℕ} (hp : p.Prime) {E : Subgroup M}
    (hE : IsElemAbelian p E) (h3 : p ^ 3 ≤ Nat.card E) :
    ∃ E₀ : Subgroup M, E₀ ≤ E ∧ IsElemAbelian p E₀ ∧ Nat.card E₀ = p ^ 3 := by
  have hdvd : p ^ 3 ∣ Nat.card E := cube_dvd_of_elemAb hp hE h3
  obtain ⟨K, hK, -, hKE⟩ := Sylow.exists_subgroup_card_pow_prime_le_le hp (H := ⊥) (L := E)
    (by simp) hdvd bot_le
  refine ⟨K, hKE, ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => hE.2 a (hKE ha)⟩, hK⟩
  apply Subtype.ext
  have := congrArg Subtype.val
    (hE.1.is_comm.comm (⟨a.1, hKE a.2⟩ : E) (⟨b.1, hKE b.2⟩ : E))
  simpa using this

end CFSG.LocalAnalysis.GLTheoremA.I141F
