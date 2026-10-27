module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossExcUWin

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

namespace CrossExcU

open CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LinearGroups Subgroup

section Odd

variable {ℓ f : ℕ} {K : Type} [Field K] [Finite K]

theorem unitaryRankAt_of_odd (h : UnitaryFieldData ℓ f K) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpℓ : ¬ p ∣ ℓ) (hodd : Odd (unitaryOrder ℓ f p)) (n : ℕ) :
    UnitaryRankAt ℓ f K n p (unitaryOrder ℓ f p) := by
  intro h4 Y hY
  haveI : Fact p.Prime := ⟨hp⟩
  set B : (Fin n → K) →ₛₗ[h.bar] (Fin n → K) →ₗ[K] K := gramForm h (1 : Matrix (Fin n) (Fin n) K)
    with hBdef
  have hB : B.IsSymm := by
    rw [hBdef, ← stdHermForm_eq_gramForm]
    exact stdHermForm_isSymm h n
  have hBl : B.SeparatingLeft := by
    rw [hBdef, ← stdHermForm_eq_gramForm]
    exact stdHermForm_separatingLeft h n
  let T : GL (Fin n) K ≃* (Module.End K (Fin n → K))ˣ := Matrix.GeneralLinearGroup.toLin
  let uV : (Module.End K (Fin n → K))ˣ := T (Y : GL (Fin n) K)
  have hYsu : (Y : GL (Fin n) K) ∈ gramSU h (1 : Matrix (Fin n) (Fin n) K) := by
    rw [← unitarySU_eq_gramSU h n]
    exact Y.2
  have huSU : uV ∈ sesqSpecialUnitaryGroup B :=
    (toLin_mem_sesqSpecialUnitaryGroup_iff h 1 _).2 hYsu
  have huU : uV ∈ sesqUnitaryGroup B := sesqSpecialUnitaryGroup_le B huSU
  have hup : uV ^ p = 1 := by
    rw [← map_pow]
    have : ((Y : GL (Fin n) K)) ^ p = 1 := by
      have := congrArg Subtype.val hY
      simpa using this
    rw [this, map_one]
  have hdim : 4 * unitaryOrder ℓ f p ≤ Module.finrank K (Fin n → K) := by
    rw [Module.finrank_fin_fun]
    exact h4
  have h4r := crossExcU_rank_GU h hp hp5 hpℓ hodd hB hBl uV huU hup hdim
  have hdet := pRank_le_pRank_inf_ker_add_one (p := p)
    (Units.map (LinearMap.det : Module.End K (Fin n → K) →* K))
    (centralizer ({uV} : Set (Module.End K (Fin n → K))ˣ) ⊓ sesqUnitaryGroup B)
  have h3 : 3 ≤ CFSG.Open.pRank p
      (centralizer ({uV} : Set (Module.End K (Fin n → K))ˣ) ⊓ sesqSpecialUnitaryGroup B) := by
    have hassoc : centralizer ({uV} : Set (Module.End K (Fin n → K))ˣ) ⊓ sesqUnitaryGroup B ⊓
        (Units.map (LinearMap.det : Module.End K (Fin n → K) →* K)).ker =
        centralizer ({uV} : Set (Module.End K (Fin n → K))ˣ) ⊓ sesqSpecialUnitaryGroup B :=
      inf_assoc _ _ _
    rw [hassoc] at hdet
    omega
  obtain ⟨E, hEle, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt
    (centralizer ({uV} : Set (Module.End K (Fin n → K))ˣ) ⊓ sesqSpecialUnitaryGroup B)
  haveI := hE.1
  have hmem : ∀ x : E, T.symm (x : (Module.End K (Fin n → K))ˣ) ∈ unitarySU ℓ f K n := by
    intro x
    rw [unitarySU_eq_gramSU h n]
    refine (toLin_mem_sesqSpecialUnitaryGroup_iff h 1 _).1 ?_
    rw [MulEquiv.apply_symm_apply]
    exact (hEle x.2).2
  let φ : E →* unitarySU ℓ f K n :=
    { toFun := fun x => ⟨T.symm (x : (Module.End K (Fin n → K))ˣ), hmem x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp) }
  have hφ : Function.Injective φ := fun x y hxy => by
    apply Subtype.ext
    exact T.symm.injective (congrArg Subtype.val hxy)
  have hrange : φ.range ≤ centralizer ({Y} : Set (unitarySU ℓ f K n)) := by
    rintro _ ⟨x, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxc : (x : (Module.End K (Fin n → K))ˣ) ∈ centralizer ({uV} : Set _) := (hEle x.2).1
    have hxc' := Subgroup.mem_centralizer_singleton_iff.1 hxc
    apply Subtype.ext
    have := congrArg T.symm hxc'
    simp only [map_mul, MulEquiv.symm_apply_apply, uV] at this
    exact this
  have hle := CFSG.SectionRank.le_pRank_of_injective (A := E) hp.one_lt
    (fun a b => Subtype.ext (setLike_mul_comm a.2 b.2)) (fun a => Subtype.ext (hE.2 a a.2))
    hEcard φ hφ hrange
  omega

end Odd

end CrossExcU

end CFSG.LocalAnalysis.RankFourTheoremC
