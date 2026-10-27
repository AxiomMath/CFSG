module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K292NIndex
public import CFSG.RankThree.PartTwo.Sec15.KSL3TwoProofDiag

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614

namespace P614K292N

open CFSG.Open Subgroup Matrix
open CFSG.RankThree.PartTwo.Sec4 hiding diagHom coe_diagHom diagHom_injective
open CFSG.RankThree.PartTwo.Sec15.KSL3Two
open CFSG.SectionRank.OddCover
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
open CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K292

variable {K : Type} [Field K]

section Perm

variable {τ : K}

theorem exists_isMonomialWith (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (P : GL (Fin 3) K)
    {x : GL (Fin 3) K}
    (hx : x ∈ normalizer (conjTorus 3 P : Set (GL (Fin 3) K))) :
    ∃ σ : Fin 3 → Fin 3,
      IsMonomialWith ((P⁻¹ * x * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) σ := by
  rw [mem_normalizer_conjTorus] at hx
  refine exists_monomial_of_normalizes (H := torus3 (rootsOfUnity 3 K))
    (fun u hu => isDiag_of_mem_torus3 hu) (exists_sep_torus3_three hτ hτ1) fun u hu => ?_
  exact (mem_normalizer_iff''.1 hx u).1 hu

noncomputable def monoFun (M : Matrix (Fin 3) (Fin 3) K) : Fin 3 → Fin 3 := by
  classical
  exact if h : ∃ σ, IsMonomialWith M σ then Classical.choose h else id

theorem isMonomialWith_monoFun {M : Matrix (Fin 3) (Fin 3) K} (h : ∃ σ, IsMonomialWith M σ) :
    IsMonomialWith M (monoFun M) := by
  classical
  rw [monoFun, dif_pos h]
  exact Classical.choose_spec h

theorem monoFun_mul (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (P : GL (Fin 3) K) {x y : GL (Fin 3) K}
    (hx : x ∈ normalizer (conjTorus 3 P : Set (GL (Fin 3) K)))
    (hy : y ∈ normalizer (conjTorus 3 P : Set (GL (Fin 3) K))) :
    monoFun ((P⁻¹ * (x * y) * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      monoFun ((P⁻¹ * x * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ∘
        monoFun ((P⁻¹ * y * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  have hx' := isMonomialWith_monoFun (exists_isMonomialWith hτ hτ1 P hx)
  have hy' := isMonomialWith_monoFun (exists_isMonomialWith hτ hτ1 P hy)
  have hxy := isMonomialWith_monoFun (exists_isMonomialWith hτ hτ1 P (mul_mem hx hy))
  have e : ((P⁻¹ * (x * y) * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((P⁻¹ * x * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((P⁻¹ * y * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [← Units.val_mul]
    congr 1
    group
  rw [e] at hxy ⊢
  exact hxy.unique (hx'.mul hy')

theorem monoFun_one (P : GL (Fin 3) K) :
    monoFun ((P⁻¹ * 1 * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = id := by
  have e : ((P⁻¹ * 1 * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (1 : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by
    rw [mul_one, inv_mul_cancel, Units.val_one, one_smul]
  have h1 : IsMonomialWith ((P⁻¹ * 1 * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) id := by
    rw [e]
    exact isMonomialWith_smul_one one_ne_zero
  exact (isMonomialWith_monoFun ⟨id, h1⟩).unique h1

noncomputable def framePerm (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (P : GL (Fin 3) K) :
    ↥(normalizer (conjTorus 3 P : Set (GL (Fin 3) K))) →* Equiv.Perm (Fin 3) where
  toFun x :=
    { toFun := monoFun ((P⁻¹ * (x : GL (Fin 3) K) * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
      invFun :=
        monoFun ((P⁻¹ * (x : GL (Fin 3) K)⁻¹ * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
      left_inv := fun i => by
        have h := monoFun_mul hτ hτ1 P (inv_mem x.2) x.2
        rw [inv_mul_cancel, monoFun_one] at h
        exact (congrFun h i).symm
      right_inv := fun i => by
        have h := monoFun_mul hτ hτ1 P x.2 (inv_mem x.2)
        rw [mul_inv_cancel, monoFun_one] at h
        exact (congrFun h i).symm }
  map_one' := Equiv.ext fun i => congrFun (monoFun_one P) i
  map_mul' x y := Equiv.ext fun i => congrFun (monoFun_mul hτ hτ1 P x.2 y.2) i

theorem isDiag_of_mem_ker_framePerm (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (P : GL (Fin 3) K)
    {x : ↥(normalizer (conjTorus 3 P : Set (GL (Fin 3) K)))}
    (hx : x ∈ (framePerm hτ hτ1 P).ker) :
    ((P⁻¹ * (x : GL (Fin 3) K) * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag := by
  have h1 : monoFun ((P⁻¹ * (x : GL (Fin 3) K) * P : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = id :=
    congrArg (fun σ : Equiv.Perm (Fin 3) => (σ : Fin 3 → Fin 3)) (MonoidHom.mem_ker.1 hx)
  have h2 := isMonomialWith_monoFun (exists_isMonomialWith hτ hτ1 P x.2)
  rw [h1] at h2
  exact h2.isDiag

theorem ker_framePerm_comm (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (P : GL (Fin 3) K)
    (x y : ↥(framePerm hτ hτ1 P).ker) : x * y = y * x := by
  have hx := isDiag_of_mem_ker_framePerm hτ hτ1 P x.2
  have hy := isDiag_of_mem_ker_framePerm hτ hτ1 P y.2
  have hc : (P⁻¹ * ((x : ↥(normalizer (conjTorus 3 P : Set (GL (Fin 3) K)))) : GL (Fin 3) K) * P) *
      (P⁻¹ * ((y : ↥(normalizer (conjTorus 3 P : Set (GL (Fin 3) K)))) : GL (Fin 3) K) * P) =
      (P⁻¹ * ((y : ↥(normalizer (conjTorus 3 P : Set (GL (Fin 3) K)))) : GL (Fin 3) K) * P) *
        (P⁻¹ * ((x : ↥(normalizer (conjTorus 3 P : Set (GL (Fin 3) K)))) : GL (Fin 3) K) * P) :=
    Units.ext (commute_of_isDiag hx hy)
  refine Subtype.ext (Subtype.ext ?_)
  simp only [Subgroup.coe_mul]
  calc ((x : ↥(normalizer (conjTorus 3 P : Set (GL (Fin 3) K)))) : GL (Fin 3) K) *
        ((y : ↥(normalizer (conjTorus 3 P : Set (GL (Fin 3) K)))) : GL (Fin 3) K) =
      P * ((P⁻¹ * ((x : ↥(normalizer (conjTorus 3 P : Set (GL (Fin 3) K)))) : GL (Fin 3) K) * P) *
        (P⁻¹ * ((y : ↥(normalizer (conjTorus 3 P : Set (GL (Fin 3) K)))) : GL (Fin 3) K) * P)) *
          P⁻¹ := by group
    _ = P * ((P⁻¹ * ((y : ↥(normalizer (conjTorus 3 P : Set (GL (Fin 3) K)))) : GL (Fin 3) K) * P) *
        (P⁻¹ * ((x : ↥(normalizer (conjTorus 3 P : Set (GL (Fin 3) K)))) : GL (Fin 3) K) * P)) *
          P⁻¹ := by rw [hc]
    _ = ((y : ↥(normalizer (conjTorus 3 P : Set (GL (Fin 3) K)))) : GL (Fin 3) K) *
        ((x : ↥(normalizer (conjTorus 3 P : Set (GL (Fin 3) K)))) : GL (Fin 3) K) := by group

theorem isSolvable_normalizer_conjTorus (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (P : GL (Fin 3) K) :
    Group.IsSolvable ↥(normalizer (conjTorus 3 P : Set (GL (Fin 3) K))) := by
  have : Group.IsSolvable ↥(framePerm hτ hτ1 P).ker :=
    Group.isSolvable_of_comm (ker_framePerm_comm hτ hτ1 P)
  have : Group.IsSolvable (Equiv.Perm (Fin 3)) := Equiv.Perm.isSolvable (by simp)
  exact Group.isSolvable_of_ker_le_range (framePerm hτ hτ1 P).ker.subtype (framePerm hτ hτ1 P)
    fun x hx => ⟨⟨x, hx⟩, rfl⟩

end Perm

section Conjuncts

variable {π : Bool} {p f : ℕ}

theorem isSolvable_slPi_inf_normalizer (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {y : GL (Fin 3) K} (hT : IsTypeThree π (p ^ f) K y) {v : Fin 3 → K} (hv : v ≠ 0)
    (horth : π = false → YFrameOrth (p ^ f) y v) :
    Group.IsSolvable
      ↥(slPi π 3 (p ^ f) K ⊓ normalizer (threeFrame y v : Set (GL (Fin 3) K))) := by
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨P, -, hPn⟩ := exists_glPi_frame hK hq hT hv horth
  have h3 : threeFrame y v = conjTorus 3 P := hPn 3 (by norm_num)
  have := isSolvable_normalizer_conjTorus hτ hτ1 P
  have hle : slPi π 3 (p ^ f) K ⊓ normalizer (threeFrame y v : Set (GL (Fin 3) K)) ≤
      normalizer (conjTorus 3 P : Set (GL (Fin 3) K)) := by
    rw [h3]
    exact inf_le_right
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)

theorem mem_threeFrame_iff (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {y : GL (Fin 3) K} (hT : IsTypeThree π (p ^ f) K y) {v : Fin 3 → K} (hv : v ≠ 0)
    (horth : π = false → YFrameOrth (p ^ f) y v) (h2 : (2 : K) ≠ 0) (g : GL (Fin 3) K) :
    g ∈ threeFrame y v ↔
      g ∈ slPi π 3 (p ^ f) K ∧ (∀ r ∈ twoFrame y v, g * r = r * g) ∧ g ^ 3 = 1 := by
  obtain ⟨P, hP, hPn⟩ := exists_glPi_frame hK hq hT hv horth
  have h3 : threeFrame y v = conjTorus 3 P := hPn 3 (by norm_num)
  have h2' : twoFrame y v = conjTorus 2 P := hPn 2 (by norm_num)
  rw [h3, h2']
  constructor
  · intro hg
    refine ⟨conjTorus_le_slPi hK hq hP hg, fun r hr => ?_, pow_eq_one_of_mem_conjTorus hg⟩
    have hgd := isDiag_of_mem_torus3 (mem_conjTorus.1 hg)
    have hrd := isDiag_of_mem_torus3 (mem_conjTorus.1 hr)
    have hc : (P⁻¹ * g * P) * (P⁻¹ * r * P) = (P⁻¹ * r * P) * (P⁻¹ * g * P) :=
      Units.ext (commute_of_isDiag hgd hrd)
    calc g * r = P * ((P⁻¹ * g * P) * (P⁻¹ * r * P)) * P⁻¹ := by group
      _ = P * ((P⁻¹ * r * P) * (P⁻¹ * g * P)) * P⁻¹ := by rw [hc]
      _ = r * g := by group
  · rintro ⟨hgL, hgr, hg3⟩
    rw [mem_conjTorus]
    refine mem_torus3_of_isDiag (by norm_num) ?_ ?_ ?_
    · refine isDiag_of_commute (H := torus3 (rootsOfUnity 2 K))
        (fun u hu => isDiag_of_mem_torus3 hu) (exists_sep_torus3_two h2) fun u hu => ?_
      have hr : P * u * P⁻¹ ∈ conjTorus 2 P := by
        rw [mem_conjTorus, show P⁻¹ * (P * u * P⁻¹) * P = u by group]
        exact hu
      have hcomm := hgr _ hr
      have e : u * (P⁻¹ * g * P) = (P⁻¹ * g * P) * u := by
        calc u * (P⁻¹ * g * P) = P⁻¹ * ((P * u * P⁻¹) * g) * P := by group
          _ = P⁻¹ * (g * (P * u * P⁻¹)) * P := by rw [hcomm]
          _ = (P⁻¹ * g * P) * u := by group
      rw [← Units.val_mul, ← Units.val_mul, e]
    · rw [← GeneralLinearGroup.val_det_apply, det_conj_inv, det_eq_one_of_mem_slPi hK hgL,
        Units.val_one]
    · rw [conj_inv_pow, hg3, mul_one, inv_mul_cancel]

end Conjuncts

end P614K292N

open P614K292N

theorem kD292ThreeFrameNorm3_holds : KD292ThreeFrameNorm3 := by
  intro π p f K _ y hK hq _ hT v hv horth
  exact ⟨threeFrame_mem_frameCands hK hq hT hv horth,
    fun E hEs hEa hE9 _ => exists_slPi_map_eq_threeFrame hK hq hT hv horth hEs hEa hE9,
    not_three_dvd_relIndex_normalizer hK hq hT hv horth,
    isSolvable_slPi_inf_normalizer hK hq hT hv horth,
    fun h2 g => mem_threeFrame_iff hK hq hT hv horth h2 g⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614
