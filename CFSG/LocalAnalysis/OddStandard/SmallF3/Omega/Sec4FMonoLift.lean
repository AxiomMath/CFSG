module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IDict
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4MPts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IBLift
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IBTrans
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IBType

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

private lemma sec4F_permVec_add {n : ℕ} (σ : Equiv.Perm (Fin n)) (v w : Fin n → ZMod 2) :
    permVec σ (v + w) = permVec σ v + permVec σ w := by
  funext k
  simp only [permVec, Function.comp_apply, Pi.add_apply]

private lemma sec4F_permVec_zero (σ : Equiv.Perm (Fin 7)) :
    permVec σ (0 : Fin 7 → ZMod 2) = 0 := by
  funext k
  rfl

private lemma sec4F_sec4MV_some (i : Fin 7) : sec4MV (some i) = sec4MW i := rfl

private lemma sec4F_sec4MW_injective : Function.Injective sec4MW := by
  intro i j hij
  by_contra hne
  have h1 : sec4MW j i = 0 := by
    have h := congr_fun hij i
    simpa [sec4MW] using h.symm
  have h2 : sec4MW j i = 1 := by simp [sec4MW, hne]
  rw [h2] at h1
  exact one_ne_zero h1

theorem sec4F_mono_frame {G : Type} [Group G] [Finite G] {L P B : Subgroup G}
    {φ : (Fin 7 → ZMod 2) → G} (hL : IsOmega7Group L) (hB : Sec4BData L P B φ) :
    ∃ (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega) (fr : Sec4IFrame Sec4IQ)
      (σ : Equiv.Perm (Fin 7)), ∀ v, IsEvenVec v →
        ∃ hφ : φ v ∈ L, sec4IRho e ⟨φ v, hφ⟩ = sec4IPsi fr (permVec σ v) := by
  classical
  have hBL : B ≤ L := (le_sup_left.trans hB.cent.symm.le).trans inf_le_right
  have hB2 : IsPGroup 2 B := IsPGroup.of_card hB.card
  have hBsub2 : IsPGroup 2 ↥(B.subgroupOf L) :=
    hB2.of_equiv (Subgroup.subgroupOfEquivOfLe hBL).symm
  obtain ⟨P₁, hP₁⟩ := IsPGroup.exists_le_sylow hBsub2
  let P₀ : Subgroup G := (P₁ : Subgroup ↥L).map L.subtype
  have hP₀ : IsSylow2Of P₀ L := isSylow2Of_map_sylow P₁
  have hBP₀ : B ≤ P₀ := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hBL]
    exact Subgroup.map_mono hP₁
  obtain ⟨e⟩ := sec4I_exists_model hL
  obtain ⟨fr, hfr⟩ := sec4I_exists_frame_good (sec4IRho_isSylow2Of hL e hP₀)
  have hmapB : (B.subgroupOf L).map (sec4IRho e) = sec4IB0 fr :=
    (sec4ILift_card_le hL e hP₀ hfr hBP₀ hB.isMax.2.1).2 hB.card
  have hφB : ∀ (v : Fin 7 → ZMod 2), IsEvenVec v → φ v ∈ B :=
    fun v hv => (hB.perm.2.2.1 (φ v)).mpr ⟨v, hv, rfl⟩
  have hφL : ∀ (v : Fin 7 → ZMod 2), IsEvenVec v → φ v ∈ L :=
    fun v hv => hBL (hφB v hv)
  have hex : ∀ (v : Fin 7 → ZMod 2) (hv : IsEvenVec v),
      ∃ w : Fin 7 → ZMod 2, IsEvenVec w ∧
        sec4IPsi fr w = sec4IRho e ⟨φ v, hφL v hv⟩ := by
    intro v hv
    have hmem : sec4IRho e ⟨φ v, hφL v hv⟩ ∈ sec4IB0 fr := by
      rw [← hmapB]
      exact Subgroup.mem_map.mpr
        ⟨⟨φ v, hφL v hv⟩, Subgroup.mem_subgroupOf.mpr (hφB v hv), rfl⟩
    obtain ⟨w, hw, hwψ⟩ := (mem_sec4IB0_iff fr).mp hmem
    exact ⟨w, hw, hwψ⟩
  let T : (Fin 7 → ZMod 2) → (Fin 7 → ZMod 2) := fun v =>
    if hv : IsEvenVec v then Classical.choose (hex v hv) else 0
  have hT_even : ∀ (v : Fin 7 → ZMod 2) (hv : IsEvenVec v), IsEvenVec (T v) := by
    intro v hv
    dsimp only [T]
    rw [dif_pos hv]
    exact (Classical.choose_spec (hex v hv)).1
  have hT_psi : ∀ (v : Fin 7 → ZMod 2) (hv : IsEvenVec v),
      sec4IPsi fr (T v) = sec4IRho e ⟨φ v, hφL v hv⟩ := by
    intro v hv
    dsimp only [T]
    rw [dif_pos hv]
    exact (Classical.choose_spec (hex v hv)).2
  have hT_add : ∀ v w, IsEvenVec v → IsEvenVec w → T (v + w) = T v + T w := by
    intro v w hv hw
    apply sec4IPsi_injOn fr (hT_even (v + w) (isEvenVec_add hv hw))
      (isEvenVec_add (hT_even v hv) (hT_even w hw))
    rw [hT_psi (v + w) (isEvenVec_add hv hw), sec4IPsi_add, hT_psi v hv, hT_psi w hw,
      ← map_mul]
    congr 1
    exact Subtype.ext (hB.perm.1 v w hv hw)
  have hT_zero : T 0 = 0 := by
    apply sec4IPsi_injOn fr (hT_even 0 sec4I_isEvenVec_zero) sec4I_isEvenVec_zero
    rw [hT_psi 0 sec4I_isEvenVec_zero, sec4IPsi_zero]
    have h1 : (⟨φ 0, hφL 0 sec4I_isEvenVec_zero⟩ : ↥L) = 1 :=
      Subtype.ext (IsPermModuleVia.map_zero hB.perm)
    rw [h1, map_one]
  have hT_inj : ∀ v w, IsEvenVec v → IsEvenVec w → T v = T w → v = w := by
    intro v w hv hw h
    have hP₀sub : IsPGroup 2 ↥(P₀.subgroupOf L) :=
      hP₀.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hP₀.1).symm
    have hρ : sec4IRho e ⟨φ v, hφL v hv⟩ = sec4IRho e ⟨φ w, hφL w hw⟩ := by
      rw [← hT_psi v hv, ← hT_psi w hw, h]
    have hφeq : φ v = φ w := by
      have hinj := sec4IRho_injOn hL e hP₀sub
      have hvP : (⟨φ v, hφL v hv⟩ : ↥L) ∈ P₀.subgroupOf L :=
        Subgroup.mem_subgroupOf.mpr (hBP₀ (hφB v hv))
      have hwP : (⟨φ w, hφL w hw⟩ : ↥L) ∈ P₀.subgroupOf L :=
        Subgroup.mem_subgroupOf.mpr (hBP₀ (hφB w hw))
      exact congrArg Subtype.val (hinj hvP hwP hρ)
    exact hB.perm.2.1 v w hv hw hφeq
  have hT_weight6 : ∀ v, IsEvenVec v → vecWeight v = 6 → vecWeight (T v) = 6 := by
    intro v hv h6
    have hv0 : v ≠ 0 := by
      intro h0
      rw [h0] at h6
      have h0w : vecWeight (0 : Fin 7 → ZMod 2) = 0 := by simp [vecWeight]
      omega
    have hind : InducesTypeSome L (φ v) 7 1 6 (-1) := (hB.type6 v hv hv0).mp h6
    have htype : HasType
        ((e (QuotientGroup.mk (⟨φ v, hφL v hv⟩ : ↥L)) : Sec4IOmega) : ProjOrth Sec4IQ)
        6 (-1) :=
      (sec4I_inducesTypeSome_mem_iff e (hφL v hv) (Or.inr (Or.inr rfl))).mp hind
    have htype' : HasType (sec4IPsi fr (T v)) 6 (-1) := by
      rw [hT_psi v hv, sec4IRho_apply]
      exact htype
    have hTv0 : T v ≠ 0 := by
      intro h0
      exact htype'.1 (by rw [h0, sec4IPsi_zero])
    exact (sec4IPsi_hasType_six sec4IQ_nondegenerate fr (hT_even v hv) hTv0).mpr htype'
  have hσ₀ : ∀ p : Fin 7, ∃ i : Fin 7, T (sec4MW p) = sec4MW i :=
    fun p => exists_sec4MW_of_weight_six (hT_even (sec4MW p) (sec4MW_even p))
      (hT_weight6 (sec4MW p) (sec4MW_even p) (sec4MW_weight p))
  let σ₀ : Fin 7 → Fin 7 := fun p => Classical.choose (hσ₀ p)
  have hσ₀spec : ∀ p, T (sec4MW p) = sec4MW (σ₀ p) := fun p => Classical.choose_spec (hσ₀ p)
  have hσ₀inj : Function.Injective σ₀ := by
    intro p q hpq
    exact sec4F_sec4MW_injective
      (hT_inj (sec4MW p) (sec4MW q) (sec4MW_even p) (sec4MW_even q)
        (by rw [hσ₀spec p, hσ₀spec q, hpq]))
  let σ : Equiv.Perm (Fin 7) :=
    Equiv.ofBijective σ₀ (Finite.injective_iff_bijective.mp hσ₀inj)
  have hT_MW : ∀ p, T (sec4MW p) = permVec σ (sec4MW p) := by
    intro p
    rw [hσ₀spec p]
    have hp : σ p = σ₀ p := by
      dsimp only [σ]
      rw [Equiv.coe_ofBijective]
    rw [← hp]
    simpa [Equiv.optionCongr_apply, sec4F_sec4MV_some] using
      (permVec_sec4MV σ (some p)).symm
  have hUeven : ∀ v : Fin 7 → ZMod 2,
      v ∈ AddSubgroup.closure {u : Fin 7 → ZMod 2 | IsEvenVec u ∧ vecWeight u = 6} →
        IsEvenVec v := by
    intro v hv
    refine AddSubgroup.closure_induction (p := fun v _ => IsEvenVec v) ?_ ?_ ?_ ?_ hv
    · rintro x ⟨hx, -⟩
      exact hx
    · unfold IsEvenVec
      simp
    · intro x y _ _ hx hy
      exact isEvenVec_add hx hy
    · intro x _ hx
      rwa [CharTwo.neg_eq x]
  have hPadd : ∀ v w, IsEvenVec v → IsEvenVec w → T v = permVec σ v →
      T w = permVec σ w → T (v + w) = permVec σ (v + w) := by
    intro v w hv hw hPv hPw
    rw [hT_add v w hv hw, hPv, hPw, sec4F_permVec_add]
  have hPU : ∀ v : Fin 7 → ZMod 2,
      v ∈ AddSubgroup.closure {u : Fin 7 → ZMod 2 | IsEvenVec u ∧ vecWeight u = 6} →
        T v = permVec σ v := by
    intro v hv
    refine AddSubgroup.closure_induction (p := fun v _ => T v = permVec σ v) ?_ ?_ ?_ ?_ hv
    · rintro x ⟨hx, hx6⟩
      obtain ⟨i, rfl⟩ := exists_sec4MW_of_weight_six hx hx6
      exact hT_MW i
    · rw [hT_zero, sec4F_permVec_zero]
    · intro x y hx hy hPx hPy
      exact hPadd x y (hUeven x hx) (hUeven y hy) hPx hPy
    · intro x _ hPx
      rwa [CharTwo.neg_eq x]
  have hT_perm : ∀ v, IsEvenVec v → T v = permVec σ v :=
    fun v hv => hPU v (isEvenVec_mem_closure_weight (k := 6) (Or.inr (Or.inr rfl)) hv)
  refine ⟨e, fr, σ, ?_⟩
  intro v hv
  refine ⟨hφL v hv, ?_⟩
  rw [← hT_psi v hv, hT_perm v hv]

end CFSG.OddStandard.SmallF3.Omega
