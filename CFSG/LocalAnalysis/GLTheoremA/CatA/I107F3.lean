module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107F2

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

@[expose] def TwoRankLowS : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (lab : GLALabel), IsSimpleGroup S → Rk2IsLabel S lab → GLAInLambda2 lab →
    ¬ exempt107 lab → twoRankLow107 lab ≤ CFSG.Open.pRank 2 (⊤ : Subgroup S)

@[expose] def CoverEvenAt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (X L : Subgroup G) (lab : GLALabel), p.Prime → p ≠ 2 →
    CFSG.Open.IsKGroup ↥X → GLAPComponent p X L → Rk2IsLabel (PSimple p L) lab → GLAInLambda2 lab →
    ¬ exempt107 lab → 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (MulAut (PSimple p L))) →
    Even (Nat.card ↥(Subgroup.center (LTilde p L))) →
    twoRankLow107 lab + CFSG.Open.pRank 2 (Subgroup.center (LTilde p L)) ≤
      CFSG.Open.pRank 2 (⊤ : Subgroup (LTilde p L))

theorem central_of_image_central {T Q : Type} [Group T] [Group Q] (π : T →* Q)
    (hker : ∀ k ∈ π.ker, k ∈ Subgroup.center T) (hperf : commutator T = ⊤) (t : T)
    (ht : π t ∈ Subgroup.center Q) : t ∈ Subgroup.center T := by
  have hc : ∀ s : T, t * s * t⁻¹ * s⁻¹ ∈ Subgroup.center T := by
    intro s
    apply hker
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    have h1 : π s * π t = π t * π s := Subgroup.mem_center_iff.1 ht (π s)
    rw [← h1]
    group
  let c : T →* T :=
    { toFun := fun s => t * s * t⁻¹ * s⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        have hb : a * (t * b * t⁻¹ * b⁻¹) = (t * b * t⁻¹ * b⁻¹) * a :=
          Subgroup.mem_center_iff.1 (hc b) a
        calc t * (a * b) * t⁻¹ * (a * b)⁻¹
            = (t * a * t⁻¹ * a⁻¹) * (a * (t * b * t⁻¹ * b⁻¹) * a⁻¹) := by group
          _ = (t * a * t⁻¹ * a⁻¹) * (t * b * t⁻¹ * b⁻¹) := by rw [hb]; group }
  have hcc : ∀ s : T, c s ∈ Subgroup.center T := hc
  have hker2 : commutator T ≤ c.ker := by
    apply Subgroup.commutator_le.2
    intro g₁ _ g₂ _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.1 (hcc g₁) (c g₂)).symm
  have hall : ∀ s : T, c s = 1 := by
    intro s
    have hs : s ∈ commutator T := by
      rw [hperf]
      exact Subgroup.mem_top s
    exact MonoidHom.mem_ker.1 (hker2 hs)
  refine Subgroup.mem_center_iff.2 (fun g => ?_)
  have h1 : ⁅t, g⁆ = 1 := hall g
  exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm

variable {G : Type} [Group G] [Finite G]

theorem commutator_top_le_glaPPrimeCore (p : ℕ) (L : Subgroup G) :
    ⁅(⊤ : Subgroup ↥L), GLAPPrimeCore p ↥L⁆ ≤ GLAPPrimeCore p ↥L :=
  Subgroup.commutator_le_right _ _

noncomputable def ltildeToPQuot (p : ℕ) (L : Subgroup G) : LTilde p L →* PQuot p L :=
  QuotientGroup.map _ (GLAPPrimeCore p ↥L) (MonoidHom.id ↥L)
    (fun x hx => commutator_top_le_glaPPrimeCore p L hx)

theorem ltildeToPQuot_surjective (p : ℕ) (L : Subgroup G) : Function.Surjective (ltildeToPQuot p L) := by
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨(QuotientGroup.mk x : LTilde p L), rfl⟩

theorem ltilde_perfect {p : ℕ} {X L : Subgroup G} (hL : GLAPComponent p X L) :
    commutator (LTilde p L) = ⊤ := by
  have hLL : commutator ↥L = ⊤ := by
    apply Subgroup.map_injective (f := L.subtype) Subtype.val_injective
    rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype,
      glaPComponent_perfect hL]
  have hsurj : Function.Surjective (QuotientGroup.mk' (⁅(⊤ : Subgroup ↥L), GLAPPrimeCore p ↥L⁆) : ↥L →* LTilde p L) :=
    QuotientGroup.mk'_surjective _
  rw [eq_top_iff]
  intro t _
  obtain ⟨x, rfl⟩ := hsurj t
  have hx : x ∈ commutator ↥L := by
    rw [hLL]
    exact Subgroup.mem_top x
  have hmem := Subgroup.mem_map_of_mem (QuotientGroup.mk' (⁅(⊤ : Subgroup ↥L), GLAPPrimeCore p ↥L⁆)) hx
  rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ hsurj] at hmem
  rw [_root_.commutator_def]
  exact hmem

theorem ltilde_ker_le_center (p : ℕ) (L : Subgroup G) :
    ∀ k ∈ (ltildeToPQuot p L).ker, k ∈ Subgroup.center (LTilde p L) := by
  intro k hk
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective k
  have hxO : x ∈ GLAPPrimeCore p ↥L := by
    rw [MonoidHom.mem_ker] at hk
    exact (QuotientGroup.eq_one_iff x).1 hk
  refine Subgroup.mem_center_iff.2 (fun g => ?_)
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective g
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  apply QuotientGroup.eq.2
  have hmem : ⁅l⁻¹, x⁻¹⁆ ∈ ⁅(⊤ : Subgroup ↥L), GLAPPrimeCore p ↥L⁆ :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.inv_mem _ hxO)
  have key : (l * x)⁻¹ * (x * l) = (⁅l⁻¹, x⁻¹⁆)⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [key]
  exact Subgroup.inv_mem _ hmem

theorem ltilde_centre_equiv {p : ℕ} {X L : Subgroup G} (hL : GLAPComponent p X L) :
    Nonempty (LTilde p L ⧸ Subgroup.center (LTilde p L) ≃* PSimple p L) := by
  let f : LTilde p L →* PSimple p L :=
    (QuotientGroup.mk' (Subgroup.center (PQuot p L))).comp (ltildeToPQuot p L)
  have hf : Function.Surjective f := by
    intro s
    obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (PQuot p L)) s
    obtain ⟨t, rfl⟩ := ltildeToPQuot_surjective p L q
    exact ⟨t, rfl⟩
  have hkerf : Subgroup.center (LTilde p L) = f.ker := by
    apply le_antisymm
    · intro z hz
      rw [MonoidHom.mem_ker]
      have hzq : ltildeToPQuot p L z ∈ Subgroup.center (PQuot p L) := by
        refine Subgroup.mem_center_iff.2 (fun w => ?_)
        obtain ⟨s, hs⟩ := ltildeToPQuot_surjective p L w
        rw [← hs, ← map_mul, ← map_mul]
        exact congrArg (ltildeToPQuot p L) (Subgroup.mem_center_iff.1 hz s)
      show (QuotientGroup.mk' (Subgroup.center (PQuot p L)) (ltildeToPQuot p L z) : PSimple p L) = 1
      exact (QuotientGroup.eq_one_iff _).2 hzq
    · intro z hz
      have hz' : (QuotientGroup.mk' (Subgroup.center (PQuot p L)) (ltildeToPQuot p L z) : PSimple p L) = 1 := hz
      have hzq : ltildeToPQuot p L z ∈ Subgroup.center (PQuot p L) := (QuotientGroup.eq_one_iff _).1 hz'
      exact central_of_image_central (ltildeToPQuot p L) (ltilde_ker_le_center p L) (ltilde_perfect hL) z hzq
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hkerf).trans (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩

theorem pRank_two_eq_zero_of_odd_subgroup {H : Subgroup G} (hH : Odd (Nat.card H)) :
    CFSG.Open.pRank 2 H = 0 := by
  refine le_antisymm ?_ (Nat.zero_le _)
  apply pRank_le_of_card_le le_rfl
  intro E hEH hE
  obtain ⟨k, hk⟩ := exists_card_eq_pow_of_isElemAbelian Nat.prime_two hE
  have hdvd : Nat.card E ∣ Nat.card H := Subgroup.card_dvd_of_le hEH
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · simp [hk, h0]
  · exfalso
    have h2 : 2 ∣ Nat.card H := by
      rw [hk] at hdvd
      exact dvd_trans (dvd_pow_self 2 hpos.ne') hdvd
    exact Odd.not_two_dvd_nat hH h2

theorem pRank_ltilde_eq_of_odd_centre {p : ℕ} {X L : Subgroup G} (hL : GLAPComponent p X L)
    (hodd : Odd (Nat.card ↥(Subgroup.center (LTilde p L)))) :
    CFSG.Open.pRank 2 (⊤ : Subgroup (LTilde p L)) = CFSG.Open.pRank 2 (⊤ : Subgroup (PSimple p L)) := by
  obtain ⟨e⟩ := ltilde_centre_equiv hL
  have hn : ¬ 2 ∣ Nat.card ↥(Subgroup.center (LTilde p L)) := Odd.not_two_dvd_nat hodd
  have h1 := CFSG.SectionRank.pRank_quotient_eq (p := 2) (Subgroup.center (LTilde p L)) hn
  have h2 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 2) e
  rw [← h1]
  exact h2

theorem i107CoverAt_of_residuals (hS : TwoRankLowS) (hE : CoverEvenAt) : I107CoverAt := by
  intro G _ _ p X L lab hp hp2 hX hL hrk hlab hex hr
  by_cases hodd : Odd (Nat.card ↥(Subgroup.center (LTilde p L)))
  · have hsimple : IsSimpleGroup (PSimple p L) := (isQuasisimple_pQuot_of_glaPComponent hp hL).2
    have hS' := hS (PSimple p L) lab hsimple hrk hlab hex
    rw [pRank_two_eq_zero_of_odd_subgroup hodd, add_zero, pRank_ltilde_eq_of_odd_centre hL hodd]
    exact hS'
  · have hev : Even (Nat.card ↥(Subgroup.center (LTilde p L))) := Nat.not_odd_iff_even.1 hodd
    exact hE G p X L lab hp hp2 hX hL hrk hlab hex hr hev

end CFSG.LocalAnalysis.GLTheoremA

end
