module

public import CFSG.ClassicalInvolution.Asc77.AscB3C4
public import CFSG.ClassicalInvolution.Asc77.AscB3CG

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace B3C

set_option linter.unusedSectionVars false

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open scoped commutatorElement MatrixGroups

section Core

variable {G : Type} [Group G]

theorem ySide_core_tw {F : Type} [Field F] [Finite F] (h2 : (2 : F) ≠ 0) (hF4 : 4 ≤ Nat.card F)
    (ψ : StatedSp 2 F →* G) (hker : ψ.ker ≤ Subgroup.center (StatedSp 2 F)) {c : StatedSp 2 F}
    {Rp : Subgroup (StatedSp 2 F)}
    (hpl : Rp = (longBlock F 2 1).range.map (MulAut.conj c⁻¹).toMonoidHom)
    (hinj : ∀ y ∈ Rp, ψ y = 1 → y = 1) {e : StatedSp 2 F}
    (hS : (twShort h2).range.map (MulAut.conj c⁻¹).toMonoidHom ≤
      Subgroup.centralizer ({e} : Set (StatedSp 2 F))) :
    SymplecticPhanPair F h2 ψ.range (Rp.map ψ)
      (((twShort h2).range.map (MulAut.conj c⁻¹).toMonoidHom).map ψ) ∧
    ((twShort h2).range.map (MulAut.conj c⁻¹).toMonoidHom).map ψ ≤
      Subgroup.centralizer ({ψ e} : Set G) ∧
    ((twShort h2).range.map (MulAut.conj c⁻¹).toMonoidHom).map ψ ≤
      ⁅((twShort h2).range.map (MulAut.conj c⁻¹).toMonoidHom).map ψ,
        ((twShort h2).range.map (MulAut.conj c⁻¹).toMonoidHom).map ψ⁆ ∧
    ψ.range ≤ Rp.map ψ ⊔ ((twShort h2).range.map (MulAut.conj c⁻¹).toMonoidHom).map ψ := by
  have hmem : ∀ A : SL(2, F), c⁻¹ * longBlock F 2 1 A * c ∈ Rp := by
    intro A
    rw [hpl]
    exact ⟨longBlock F 2 1 A, ⟨A, rfl⟩, by simp⟩
  refine ⟨⟨ψ, c, rfl, hker, ?_, ?_, rfl⟩, ?_, ?_, ?_⟩
  · intro A B hAB
    have h1 : ψ ((c⁻¹ * longBlock F 2 1 A * c)⁻¹ * (c⁻¹ * longBlock F 2 1 B * c)) = 1 := by
      rw [map_mul, map_inv]
      have : ψ (c⁻¹ * longBlock F 2 1 A * c) = ψ (c⁻¹ * longBlock F 2 1 B * c) := by
        simpa [MonoidHom.comp_apply] using hAB
      rw [this, inv_mul_cancel]
    have h2' := hinj _ (Rp.mul_mem (Rp.inv_mem (hmem A)) (hmem B)) h1
    have h3 : c⁻¹ * longBlock F 2 1 A * c = c⁻¹ * longBlock F 2 1 B * c := inv_mul_eq_one.mp h2'
    exact longBlock_injective (1 : Fin 2) (by simpa using h3)
  · exact congrArg (Subgroup.map ψ) hpl.symm
  · rintro _ ⟨s, hs, rfl⟩
    have h := Subgroup.mem_centralizer_singleton_iff.mp (hS hs)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h' := congrArg ψ h
    simpa only [map_mul] using h'
  · have hperf2 : Group.IsPerfect SL(2, F) :=
      CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card _ hF4
    have hφ : ((twShort h2).range.map (MulAut.conj c⁻¹).toMonoidHom).map ψ =
        (ψ.comp ((MulAut.conj c⁻¹).toMonoidHom.comp (twShort h2))).range := by
      rw [MonoidHom.range_comp, MonoidHom.range_comp]
    rw [hφ]
    have := Group.IsPerfect.range (ψ.comp ((MulAut.conj c⁻¹).toMonoidHom.comp (twShort h2)))
    exact (Subgroup.isPerfect_iff.mp this).ge
  · have htop : ((twShort h2).range.map (MulAut.conj c⁻¹).toMonoidHom) ⊔ Rp = ⊤ := by
      rw [hpl, ← Subgroup.map_sup, twShort_sup_longBlock h2, Subgroup.map_top]
      exact MonoidHom.range_eq_top.mpr (MulAut.conj c⁻¹).surjective
    rw [MonoidHom.range_eq_map, ← htop, Subgroup.map_sup, sup_comm]

end Core

section Model

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]


theorem ySide_model_tw (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {Φ : Set (Subgroup G)}
    (P : T7Z.ModelLayer .PSp 2 p f Φ) {J J' : Subgroup G} {t a b : G}
    (hJ : J ∈ Φ) (hJ' : J' ∈ Φ) (eJ : Nonempty (↥J ≃* SL(2, GaloisField p f)))
    (eJ' : Nonempty (↥J' ≃* SL(2, GaloisField p f))) (hne : J ≠ J')
    (hcomm : Commutes J J') (htJ : IsUniqueInvolution J t) (htJ' : IsUniqueInvolution J' t)
    (ha : a ∈ J) (hb : b ∈ J') (haa : a * a = t) (hbb : b * b = t) :
    ∃ J₁ K₃ : Subgroup G, (J₁ = J ∨ J₁ = J') ∧
      SymplecticPhanPair (GaloisField p f) (ModelFacts.two_ne_zero_galoisField f hp2)
        (omegaGen Φ) J₁ K₃ ∧
      K₃ ≤ Subgroup.centralizer ({a * b} : Set G) ∧ K₃ ≤ ⁅K₃, K₃⁆ ∧ omegaGen Φ ≤ J₁ ⊔ K₃ ∧
      K₃ ≤ omegaGen Φ := by
  classical
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at hq
  have : NeZero f := ⟨hf0⟩
  have hadm : StatedLieAdmissible .PSp 2 p f := by
    refine ⟨Fact.out, Nat.one_le_iff_ne_zero.mpr hf0, le_rfl, ?_⟩
    intro h
    have := congrArg Prod.snd h
    simp at this
    omega
  have h2 : (2 : GaloisField p f) ≠ 0 := ModelFacts.two_ne_zero_galoisField f hp2
  have hfin : Finite (modelUniv .PSp 2 p f Fact.out).K :=
    ModelFacts.finite_modelUniv hp2 Fact.out (by trivial) hadm
  obtain ⟨RJ, hRJ, hJR⟩ := P.fund J hJ
  obtain ⟨RJ', hRJ', hJ'R⟩ := P.fund J' hJ'
  have hi₁ := P.injOn_fund hp2 hadm (by trivial) (by decide) (by decide) hRJ hJR eJ
  have hi₂ := P.injOn_fund hp2 hadm (by trivial) (by decide) (by decide) hRJ' hJ'R eJ'
  have hperf : RJ ≤ ⁅RJ, RJ⁆ :=
    RouteD.Gaps.fundPerfect_modelUniv hp2 (by trivial) hadm (by omega) RJ hRJ
  obtain ⟨a₀, ha₀, hψa⟩ := (hJR ▸ ha : a ∈ RJ.map P.ψ)
  obtain ⟨b₀, hb₀, hψb⟩ := (hJ'R ▸ hb : b ∈ RJ'.map P.ψ)
  have hcomm' : Commutes RJ RJ' := by
    refine T7Z.commutes_of_map_commutes P.ψ P.ker_le hperf ?_
    rw [← hJR, ← hJ'R]
    exact hcomm
  have hxR : a₀ * a₀ ∈ RJ := RJ.mul_mem ha₀ ha₀
  have hx'R : b₀ * b₀ ∈ RJ' := RJ'.mul_mem hb₀ hb₀
  have hψx : P.ψ (a₀ * a₀) = t := by rw [map_mul, hψa, haa]
  have hψx' : P.ψ (b₀ * b₀) = t := by rw [map_mul, hψb, hbb]
  have hx2 : (a₀ * a₀) * (a₀ * a₀) = 1 := hi₁ _ (RJ.mul_mem hxR hxR) (by
    rw [map_mul, hψx, htJ.sq])
  have hx'2 : (b₀ * b₀) * (b₀ * b₀) = 1 := hi₂ _ (RJ'.mul_mem hx'R hx'R) (by
    rw [map_mul, hψx', htJ'.sq])
  have hx1 : a₀ * a₀ ≠ 1 := fun h => htJ.ne_one (by rw [← hψx, h, map_one])
  have hx'1 : b₀ * b₀ ≠ 1 := fun h => htJ'.ne_one (by rw [← hψx', h, map_one])
  have hc : (b₀ * b₀) * (a₀ * a₀)⁻¹ ∈ Subgroup.center (StatedSp 2 (GaloisField p f)) := by
    refine P.ker_le ?_
    rw [MonoidHom.mem_ker, map_mul, map_inv, hψx, hψx', mul_inv_cancel]
  have hne' : RJ ≠ RJ' := by
    intro h
    apply hne
    rw [hJR, hJ'R, h]
  have hlong : ∀ R : Subgroup (modelUniv .PSp 2 p f Fact.out).K,
      R ∈ fundamentalSubgroups .PSp (modelUniv .PSp 2 p f Fact.out).D →
        ∃ i, IsLongRootSp2 (K := GaloisField p f) (n := 2) R i :=
    fun R hR => (ModelFacts.fund_iff_isLongRootSp2 hadm h2 R).1 hR
  obtain ⟨c, Rp, hRp, hpl, hS⟩ := sp4_adapted_tw h2 (hlong RJ hRJ) (hlong RJ' hRJ') hne' hxR hx2
    hx1 hx'R hx'2 hx'1 hc ha₀ rfl hb₀ rfl (hcomm' a₀ ha₀ b₀ hb₀)
  have hF4 : 4 ≤ Nat.card (GaloisField p f) := by
    rw [GaloisField.card p f hf0]
    omega
  have hinj : ∀ y ∈ Rp, P.ψ y = 1 → y = 1 := by
    rcases hRp with h | h
    · rw [h]
      exact hi₁
    · rw [h]
      exact hi₂
  obtain ⟨hpair, hcent, hperfK, hgen⟩ := ySide_core_tw h2 hF4 P.ψ P.ker_le hpl hinj hS
  refine ⟨Rp.map P.ψ, _, ?_, ?_, ?_, hperfK, ?_, ?_⟩
  · rcases hRp with h | h
    · left
      rw [h, hJR]
    · right
      rw [h, hJ'R]
  · rw [← P.range_eq]
    exact hpair
  · have hψe : P.ψ (a₀ * b₀) = a * b := by rw [map_mul, hψa, hψb]
    rw [← hψe]
    exact hcent
  · rw [← P.range_eq]
    exact hgen
  · rw [← P.range_eq]
    exact Subgroup.map_le_range _ _

end Model

end B3C

end CFSG.ClassicalInvolution.Asc77
