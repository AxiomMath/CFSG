module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173SplitCent
public import CFSG.Yardstones.Md0ec50421ce4.Definitions
public import CFSG.RankThree.PartTwo.Sec15.F153L3C2Quot
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightSwapGen
import CFSG.LieType.SeitzGeneration.OrthRelRoot
import CFSG.RankThree.PartOne.KC.OrthogonalNormPlaneInvolution
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CRankWitt
import CFSG.RankThree.PartOne.KC.LinearPlaneBlocks
import CFSG.RankThree.PartOne.KC.OrthogonalKernelSectorRigidityTransvection
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173SplitBorelTits

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.T173S

open Polynomial Module QuadraticMap CFSG.Open CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
  CFSG.StandardType.TableBOrth
  CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal CFSG.StandardType.TableBOrth
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.Yardstones.Md0ec50421ce4 (closureIn)
open scoped commutatorElement

section Vanish

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V}

theorem le_closureIn_self {G : Type} [Group G] (K H : Subgroup G) : K ≤ closureIn K H := by
  intro k hk
  have hk' : k ∈ K.map (MulAut.conj (1 : G)).toMonoidHom := ⟨k, hk, by simp⟩
  exact le_iSup₂ (f := fun (a : G) (_ : a ∈ H) => K.map (MulAut.conj a).toMonoidHom) 1 H.one_mem hk'

theorem conj_mem_closureIn {G : Type} [Group G] {K H : Subgroup G} {n k : G} (hn : n ∈ H)
    (hk : k ∈ K) : n * k * n⁻¹ ∈ closureIn K H := by
  have hk' : n * k * n⁻¹ ∈ K.map (MulAut.conj n).toMonoidHom := ⟨k, hk, by simp [MulAut.conj_apply]⟩
  exact le_iSup₂ (f := fun (a : G) (_ : a ∈ H) => K.map (MulAut.conj a).toMonoidHom) n hn hk'

theorem eq_bot_of_top_le_normalizer (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {l : ℕ}
    (hdim : finrank F V = 2 * l) (hl : 4 ≤ l) {T : Subgroup ↥(orthDerived Q)} (hT2 : IsPGroup 2 T)
    (hT : (⊤ : Subgroup ↥(orthDerived Q)) ≤ Subgroup.normalizer (T : Set ↥(orthDerived Q))) :
    T = ⊥ := by
  obtain ⟨T3, hT3, hTs⟩ := exists_finrank_three_singular hQ hdim hl
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hnormal : T.Normal := Subgroup.normalizer_eq_top_iff.1 (top_le_iff.1 hT)
  have hq := isQuasisimple_orthDerived hQ ⟨T3, hT3, hTs⟩
  have hne : ∃ v, Q v ≠ 0 := by
    obtain ⟨e, f, hef⟩ := exists_isHypFamily_wittRank hQ hdim
    have hm : 0 < wittRank Q l := by
      unfold wittRank
      split_ifs <;> omega
    refine ⟨e ⟨0, hm⟩ + f ⟨0, hm⟩, ?_⟩
    rw [QuadraticMap.map_add (⇑Q) _ _, hef.map_e, hef.map_f, hef.polar_ef]
    simp
  have hcen : Subgroup.center ↥(orthDerived Q) = ⊥ :=
    CFSG.SeitzReduction.OmegaPilot.center_orthDerived_eq_bot' hQ ⟨T3, hT3, hTs⟩ hne
  rcases CFSG.RankThree.PartTwo.Sec15.F153L3C2.quasi_normal_le_center_or_eq_top hq T with h | h
  · rw [hcen] at h
    exact le_bot_iff.1 h
  · exfalso
    have hP : IsPGroup 2 ↥(orthDerived Q) := by
      have h1 : IsPGroup 2 ↥(⊤ : Subgroup ↥(orthDerived Q)) := h ▸ hT2
      exact h1.of_equiv Subgroup.topEquiv
    haveI : Nontrivial (↥(orthDerived Q) ⧸ Subgroup.center ↥(orthDerived Q)) := hq.2.1.toNontrivial
    haveI : Nontrivial ↥(orthDerived Q) :=
      (QuotientGroup.mk'_surjective (Subgroup.center ↥(orthDerived Q))).nontrivial
    have hcn := hP.center_nontrivial
    rw [hcen] at hcn
    exact not_nontrivial_iff_subsingleton.mpr inferInstance hcn

private theorem exists_mem_normalizer_swap_aux1 {m : ℕ} {e f : Fin m → V}
    (hef : IsHypFamily Q e f) {j k : Fin m} (hjk : j ≠ k) :
    Q (e j + e k) = 0 ∧ polar Q (e j + e k) (f j + f k) = 0 := by
  constructor
  · rw [QuadraticMap.map_add (⇑Q), hef.map_e j, hef.map_e k, hef.polar_ee j k, add_zero, add_zero]
  · rw [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
      QuadraticMap.polar_add_right, hef.polar_ef j j, hef.polar_ef j k, hef.polar_ef k j,
      hef.polar_ef k k, if_pos rfl, if_neg hjk, if_neg (Ne.symm hjk), if_pos rfl]
    simp only [add_zero, zero_add]
    exact CharTwo.add_self_eq_zero (1 : F)

private theorem exists_mem_normalizer_swap_aux2 {m : ℕ} {e f : Fin m → V}
    (hef : IsHypFamily Q e f) {j k : Fin m} (hjk : j ≠ k) :
    ∀ i, eichler Q (e j + e k) (f j + f k) (e i) = e (Equiv.swap j k i) := by
  intro i
  have h := exists_mem_normalizer_swap_aux1 hef hjk
  have hnegv : ∀ x : V, -x = x := fun x => by
    have hneg : (-1 : F) = 1 := by simpa using CharTwo.neg_eq (1 : F)
    rw [← neg_one_smul F x, hneg, one_smul]
  rw [eichler_apply h.1 h.2, QuadraticMap.map_add (⇑Q), hef.map_f j, hef.map_f k,
    hef.polar_ff j k, add_zero, add_zero, zero_mul, add_zero,
    QuadraticMap.polar_add_right, QuadraticMap.polar_add_right, hef.polar_ee i j, hef.polar_ee i k,
    hef.polar_ef i j, hef.polar_ef i k, add_zero]
  rw [Equiv.swap_apply_def]
  by_cases hij : i = j
  · subst i
    rw [if_pos rfl, if_neg hjk, if_pos rfl]
    simp only [one_smul, zero_smul, add_zero, sub_zero]
    rw [show e j - (e j + e k) = -e k by abel, hnegv]
  · by_cases hik : i = k
    · subst i
      rw [if_neg (Ne.symm hjk), if_pos rfl, if_neg (Ne.symm hjk), if_pos rfl]
      simp only [one_smul, zero_smul, zero_add, add_zero, sub_zero]
      rw [show e k - (e j + e k) = -e j by abel, hnegv]
    · rw [if_neg hij, if_neg hik, if_neg hij, if_neg hik]
      simp only [add_zero, zero_smul, sub_zero]

private theorem exists_mem_normalizer_swap_aux3 {m : ℕ} {e f : Fin m → V}
    (hef : IsHypFamily Q e f) {j k : Fin m} (hjk : j ≠ k) :
    ∀ i, eichler Q (e j + e k) (f j + f k) (f i) = f (Equiv.swap j k i) := by
  intro i
  have h := exists_mem_normalizer_swap_aux1 hef hjk
  have hnegv : ∀ x : V, -x = x := fun x => by
    have hneg : (-1 : F) = 1 := by simpa using CharTwo.neg_eq (1 : F)
    rw [← neg_one_smul F x, hneg, one_smul]
  rw [eichler_apply h.1 h.2, QuadraticMap.map_add (⇑Q), hef.map_f j, hef.map_f k,
    hef.polar_ff j k, add_zero, add_zero, zero_mul, add_zero,
    QuadraticMap.polar_add_right, QuadraticMap.polar_add_right,
    QuadraticMap.polar_comm (⇑Q) (f i) (e j), QuadraticMap.polar_comm (⇑Q) (f i) (e k),
    hef.polar_ef j i, hef.polar_ef k i, hef.polar_ff i j, hef.polar_ff i k, add_zero]
  rw [Equiv.swap_apply_def]
  by_cases hij : i = j
  · subst i
    rw [if_pos rfl, if_neg (Ne.symm hjk), if_pos rfl]
    simp only [add_zero, one_smul, zero_smul, sub_zero]
    rw [show f j + (f j + f k) = f k + (f j + f j) by abel,
      show f j + f j = 0 by rw [← two_smul F (f j), CharTwo.two_eq_zero, zero_smul], add_zero]
  · by_cases hik : i = k
    · subst i
      rw [if_neg hjk, if_pos rfl, if_neg (Ne.symm hjk), if_pos rfl]
      simp only [zero_add, one_smul, zero_smul, sub_zero]
      rw [show f k + (f j + f k) = f j + (f k + f k) by abel,
        show f k + f k = 0 by rw [← two_smul F (f k), CharTwo.two_eq_zero, zero_smul], add_zero]
    · rw [if_neg (Ne.symm hij), if_neg (Ne.symm hik), if_neg hij, if_neg hik]
      simp only [add_zero, zero_add, zero_smul, sub_zero]

private theorem exists_mem_normalizer_swap_aux4 {m : ℕ} {e f : Fin m → V} {j k : Fin m}
    {n0 : V ≃ₗ[F] V} (hn0O : n0 ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hn0inv : n0⁻¹ = n0)
    (he : ∀ i, n0 (e i) = e (Equiv.swap j k i))
    (hf : ∀ i, n0 (f i) = f (Equiv.swap j k i))
    {c : Fin m → Fˣ} {a : V ≃ₗ[F] V} (hdiag : IsHypDiag Q e f c a) :
    IsHypDiag Q e f (fun i => c (Equiv.swap j k i)) (n0 * a * n0⁻¹) := by
  refine ⟨fun i => ?_, fun i => ?_, fun v hv1 hv2 => ?_⟩
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      show n0⁻¹ (e i) = e (Equiv.swap j k i) by rw [hn0inv]; exact he i,
      hdiag.1 (Equiv.swap j k i), map_smul, he (Equiv.swap j k i), Equiv.swap_apply_self]
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      show n0⁻¹ (f i) = f (Equiv.swap j k i) by rw [hn0inv]; exact hf i,
      hdiag.2.1 (Equiv.swap j k i), map_smul, hf (Equiv.swap j k i), Equiv.swap_apply_self]
  · have h1 : ∀ i, polar Q (e i) (n0⁻¹ v) = 0 := by
      intro i
      have hpol := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hn0O (e i) (n0⁻¹ v)
      rw [show n0 (n0⁻¹ v) = v from LinearEquiv.apply_symm_apply n0 v, he i] at hpol
      rw [← hpol]; exact hv1 (Equiv.swap j k i)
    have h2 : ∀ i, polar Q (f i) (n0⁻¹ v) = 0 := by
      intro i
      have hpol := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hn0O (f i) (n0⁻¹ v)
      rw [show n0 (n0⁻¹ v) = v from LinearEquiv.apply_symm_apply n0 v, hf i] at hpol
      rw [← hpol]; exact hv2 (Equiv.swap j k i)
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hdiag.2.2 (n0⁻¹ v) h1 h2]
    exact LinearEquiv.apply_symm_apply n0 v

private theorem exists_mem_normalizer_swap_aux5 {m : ℕ} {e f : Fin m → V} {j k : Fin m}
    {p : ℕ} {A : Subgroup ↥(orthDerived Q)}
    (hAeq : ∀ g : ↥(orthDerived Q), g ∈ A ↔ InTorsionTorus Q p e f (g : V ≃ₗ[F] V))
    {n0 : V ≃ₗ[F] V} (hn0mem : n0 ∈ orthDerived Q)
    (hn0O : n0 ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hn0inv : n0⁻¹ = n0)
    (he : ∀ i, n0 (e i) = e (Equiv.swap j k i))
    (hf : ∀ i, n0 (f i) = f (Equiv.swap j k i)) :
    (⟨n0, hn0mem⟩ : ↥(orthDerived Q)) ∈ Subgroup.normalizer (A : Set ↥(orthDerived Q)) := by
  have hn0sq : n0 * n0 = 1 := by
    nth_rewrite 2 [← hn0inv]
    rw [mul_inv_cancel]
  have hmem : ∀ a : ↥(orthDerived Q), a ∈ A → ⟨n0, hn0mem⟩ * a * ⟨n0, hn0mem⟩⁻¹ ∈ A := by
    intro a ha
    rw [hAeq] at ha ⊢
    obtain ⟨c, hcp, hdiag⟩ := ha
    refine ⟨fun i => c (Equiv.swap j k i), fun i => hcp _, ?_⟩
    rw [show ((⟨n0, hn0mem⟩ * a * ⟨n0, hn0mem⟩⁻¹ : ↥(orthDerived Q)) : V ≃ₗ[F] V)
        = n0 * (a : V ≃ₗ[F] V) * n0⁻¹ from rfl]
    exact exists_mem_normalizer_swap_aux4 hn0O hn0inv he hf hdiag
  have hnsq : (⟨n0, hn0mem⟩ : ↥(orthDerived Q)) * ⟨n0, hn0mem⟩ = 1 :=
    Subtype.ext (by simpa using hn0sq)
  have hninv : (⟨n0, hn0mem⟩ : ↥(orthDerived Q))⁻¹ = ⟨n0, hn0mem⟩ := Subtype.ext hn0inv
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · exact hmem a
  · intro hb
    have h2 := hmem (⟨n0, hn0mem⟩ * a * ⟨n0, hn0mem⟩⁻¹) hb
    rwa [show (⟨n0, hn0mem⟩ : ↥(orthDerived Q)) *
        (⟨n0, hn0mem⟩ * a * ⟨n0, hn0mem⟩⁻¹) * ⟨n0, hn0mem⟩⁻¹ = a by
      calc (⟨n0, hn0mem⟩ : ↥(orthDerived Q)) * (⟨n0, hn0mem⟩ * a * ⟨n0, hn0mem⟩⁻¹) *
            ⟨n0, hn0mem⟩⁻¹
          = (⟨n0, hn0mem⟩ * ⟨n0, hn0mem⟩) * a * (⟨n0, hn0mem⟩⁻¹ * ⟨n0, hn0mem⟩⁻¹) := by group
        _ = a := by rw [hnsq, hninv, hnsq, one_mul, mul_one]] at h2

theorem exists_mem_normalizer_swap (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F - 1) {m : ℕ} {e f : Fin m → V}
    (hef : IsHypFamily Q e f) {A : Subgroup ↥(orthDerived Q)}
    (hAeq : ∀ g : ↥(orthDerived Q), g ∈ A ↔ InTorsionTorus Q p e f (g : V ≃ₗ[F] V))
    {j k : Fin m} (hjk : j ≠ k) :
    ∃ n : ↥(orthDerived Q), n ∈ Subgroup.normalizer (A : Set ↥(orthDerived Q)) ∧
      (n : V ≃ₗ[F] V) (e j) = e k ∧ (n : V ≃ₗ[F] V) (f j) = f k := by
  classical
  have huw := exists_mem_normalizer_swap_aux1 hef hjk
  have he_img := exists_mem_normalizer_swap_aux2 hef hjk
  have hf_img := exists_mem_normalizer_swap_aux3 hef hjk
  have hnegv : ∀ x : V, -x = x := fun x => by
    have hneg : (-1 : F) = 1 := by simpa using CharTwo.neg_eq (1 : F)
    rw [← neg_one_smul F x, hneg, one_smul]
  let n0 : V ≃ₗ[F] V := eichler Q (e j + e k) (f j + f k)
  have hn0O : n0 ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    eichler_mem_orthogonalGroup Q _ _
  have hn0inv : n0⁻¹ = n0 := by
    dsimp only [n0]
    rw [eichler_inv huw.2]
    congr 1
    exact hnegv (f j + f k)
  have hn0mem : n0 ∈ orthDerived Q := by
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p (by rwa [Nat.card_units])
    refine CFSG.SeitzReduction.OmegaPilot.eichler_mem_orthDerived_of_ne_zero_ne_one hQ
      (Units.ne_zero ζ) ?_ (e j + e k) (f j + f k)
    intro h
    have h1 : ζ = 1 := Units.ext h
    have : orderOf ζ = 1 := by rw [h1]; exact orderOf_one
    rw [hζ] at this
    exact hp.ne_one this
  refine ⟨⟨n0, hn0mem⟩, ?_, ?_, ?_⟩
  · exact exists_mem_normalizer_swap_aux5 hAeq hn0mem hn0O hn0inv he_img hf_img
  · show n0 (e j) = e k
    rw [he_img j, Equiv.swap_apply_left]
  · show n0 (f j) = f k
    rw [hf_img j, Equiv.swap_apply_left]

private theorem exists_mem_normalizer_flip_aux1 {m : ℕ} {e f : Fin m → V} (hef : IsHypFamily Q e f) (i : Fin m) :
    Q (e i + f i) = 1 := by
  rw [QuadraticMap.map_add (⇑Q), hef.map_e i, hef.map_f i, hef.polar_ef i i, if_pos rfl]
  simp only [add_zero, zero_add]

private theorem exists_mem_normalizer_flip_aux2 {m : ℕ} {e f : Fin m → V} (hef : IsHypFamily Q e f) {i j : Fin m}
    (h : j ≠ i) : reflect Q (e i + f i) (e j) = e j ∧ reflect Q (e i + f i) (f j) = f j := by
  have hQ := exists_mem_normalizer_flip_aux1 hef i
  have hpj : polar Q (e i + f i) (e j) = 0 := by
    rw [QuadraticMap.polar_add_left, hef.polar_ee i j, QuadraticMap.polar_comm,
      hef.polar_ef j i, if_neg h, zero_add]
  have hqj : polar Q (e i + f i) (f j) = 0 := by
    rw [QuadraticMap.polar_add_left, hef.polar_ef i j, hef.polar_ff i j, if_neg (Ne.symm h),
      add_zero]
  exact ⟨reflect_apply_of_polar_eq_zero hpj, reflect_apply_of_polar_eq_zero hqj⟩

private theorem exists_mem_normalizer_flip_aux3 {m : ℕ} {e f : Fin m → V} (hef : IsHypFamily Q e f) (i : Fin m) :
    reflect Q (e i + f i) (e i) = f i ∧ reflect Q (e i + f i) (f i) = e i := by
  have hQ := exists_mem_normalizer_flip_aux1 hef i
  have hQ0 : Q (e i + f i) ≠ 0 := by rw [hQ]; exact one_ne_zero
  have hnegv : ∀ x : V, -x = x := fun x => by
    have hneg : (-1 : F) = 1 := by simpa using CharTwo.neg_eq (1 : F)
    rw [← neg_one_smul F x, hneg, one_smul]
  constructor
  · rw [reflect_apply hQ0, QuadraticMap.polar_add_left, hef.polar_ee i i,
      QuadraticMap.polar_comm, hef.polar_ef i i, if_pos rfl, zero_add, hQ, div_one, one_smul,
      show e i - (e i + f i) = -f i by abel, hnegv]
  · rw [reflect_apply hQ0, QuadraticMap.polar_add_left, hef.polar_ef i i, hef.polar_ff i i,
      if_pos rfl, add_zero, hQ, div_one, one_smul,
      show f i - (e i + f i) = -e i by abel, hnegv]

private theorem exists_mem_normalizer_flip_aux4 {m : ℕ} {e f : Fin m → V} (hef : IsHypFamily Q e f) {i j : Fin m}
    (hij : i ≠ j) : polar Q (e i + f i) (e j + f j) = 0 := by
  rw [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right, QuadraticMap.polar_add_right,
    hef.polar_ee i j, hef.polar_ef i j, QuadraticMap.polar_comm, hef.polar_ef j i,
    hef.polar_ff i j, if_neg hij, if_neg (Ne.symm hij)]
  simp only [add_zero, zero_add]

private def exists_mem_normalizer_flip_aux5 {m : ℕ} {e f : Fin m → V} (hef : IsHypFamily Q e f) (S : Finset (Fin m)) :
    (S : Set (Fin m)).Pairwise (Function.onFun Commute (fun k => reflect Q (e k + f k))) :=
  fun i _ j _ hij => CFSG.RankThree.PartOne.KCOrthogonal.reflectPair_comm (exists_mem_normalizer_flip_aux1 hef i) (exists_mem_normalizer_flip_aux1 hef j)
    (exists_mem_normalizer_flip_aux4 hef hij)

private theorem exists_mem_normalizer_flip_aux6 {m : ℕ} {e f : Fin m → V} (hef : IsHypFamily Q e f) :
    ∀ S : Finset (Fin m), ∀ i,
      (S.noncommProd (fun k => reflect Q (e k + f k)) (exists_mem_normalizer_flip_aux5 hef S)) (e i) =
      if i ∈ S then f i else e i := by
  intro S
  induction S using Finset.induction with
  | empty => intro i; rw [Finset.noncommProd_empty]; simp
  | insert k S hk ih =>
      intro i
      rw [Finset.noncommProd_insert_of_notMem S k _ (exists_mem_normalizer_flip_aux5 hef (insert k S)) hk,
        show S.noncommProd (fun k => reflect Q (e k + f k)) _ =
          S.noncommProd (fun k => reflect Q (e k + f k)) (exists_mem_normalizer_flip_aux5 hef S) from
          congrArg (fun c => S.noncommProd (fun k => reflect Q (e k + f k)) c)
            (Subsingleton.elim _ _),
        LinearEquiv.mul_apply]
      by_cases hik : i = k
      · subst i
        rw [ih k, if_neg hk, (exists_mem_normalizer_flip_aux3 hef k).1, if_pos (Finset.mem_insert_self k S)]
      · rw [ih i]
        by_cases his : i ∈ S
        · rw [if_pos his, (exists_mem_normalizer_flip_aux2 hef (i := k) (j := i) hik).2,
            if_pos (Finset.mem_insert_of_mem his)]
        · rw [if_neg his, (exists_mem_normalizer_flip_aux2 hef (i := k) (j := i) hik).1,
            if_neg (by simp [hik, his])]

private theorem exists_mem_normalizer_flip_aux7 {m : ℕ} {e f : Fin m → V} (hef : IsHypFamily Q e f) :
    ∀ S : Finset (Fin m), ∀ i,
      (S.noncommProd (fun k => reflect Q (e k + f k)) (exists_mem_normalizer_flip_aux5 hef S)) (f i) =
      if i ∈ S then e i else f i := by
  intro S
  induction S using Finset.induction with
  | empty => intro i; rw [Finset.noncommProd_empty]; simp
  | insert k S hk ih =>
      intro i
      rw [Finset.noncommProd_insert_of_notMem S k _ (exists_mem_normalizer_flip_aux5 hef (insert k S)) hk,
        show S.noncommProd (fun k => reflect Q (e k + f k)) _ =
          S.noncommProd (fun k => reflect Q (e k + f k)) (exists_mem_normalizer_flip_aux5 hef S) from
          congrArg (fun c => S.noncommProd (fun k => reflect Q (e k + f k)) c)
            (Subsingleton.elim _ _),
        LinearEquiv.mul_apply]
      by_cases hik : i = k
      · subst i
        rw [ih k, if_neg hk, (exists_mem_normalizer_flip_aux3 hef k).2, if_pos (Finset.mem_insert_self k S)]
      · rw [ih i]
        by_cases his : i ∈ S
        · rw [if_pos his, (exists_mem_normalizer_flip_aux2 hef (i := k) (j := i) hik).1,
            if_pos (Finset.mem_insert_of_mem his)]
        · rw [if_neg his, (exists_mem_normalizer_flip_aux2 hef (i := k) (j := i) hik).2,
            if_neg (by simp [hik, his])]

private theorem exists_mem_normalizer_flip_aux8b {m : ℕ} {e f : Fin m → V} {S : Finset (Fin m)}
    (hEven : Even S.card) (hne : S.Nonempty) :
    ∃ x y : Fin m, ∃ S' : Finset (Fin m), S = insert x (insert y S') ∧
      x ∉ insert y S' ∧ y ∉ S' ∧ S' ⊂ S ∧ S'.card = S.card - 2 := by
  obtain ⟨x, hx⟩ := hne
  have hneer : (S.erase x).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h0
    have h1 : (S.erase x).card = 0 := by rw [h0]; simp
    rw [Finset.card_erase_of_mem hx] at h1
    have hc1 : 1 ≤ S.card := Finset.card_pos.mpr ⟨x, hx⟩
    obtain ⟨t, ht⟩ := hEven
    omega
  obtain ⟨y, hy⟩ := hneer
  have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
  refine ⟨x, y, (S.erase x).erase y, ?_, ?_, ?_, ?_, ?_⟩
  · ext z
    simp only [Finset.mem_insert, Finset.mem_erase]
    constructor
    · intro hz
      by_cases hzx : z = x
      · exact Or.inl hzx
      · right
        by_cases hzy : z = y
        · exact Or.inl hzy
        · exact Or.inr ⟨hzy, hzx, hz⟩
    · rintro (rfl | rfl | ⟨-, -, hz⟩)
      · exact hx
      · exact Finset.mem_of_mem_erase hy
      · exact hz
  · rw [Finset.mem_insert]; push Not
    exact ⟨Ne.symm hyx, fun h => (Finset.mem_erase.mp (Finset.mem_of_mem_erase h)).1 rfl⟩
  · simp
  · rw [Finset.ssubset_iff_subset_ne]
    refine ⟨?_, ?_⟩
    · intro z hz; exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hz)
    · intro heq
      have hxS' : x ∈ (S.erase x).erase y := by rw [heq]; exact hx
      exact (Finset.mem_erase.mp (Finset.mem_of_mem_erase hxS')).1 rfl
  · rw [Finset.card_erase_of_mem hy, Finset.card_erase_of_mem hx, Nat.sub_sub]

private theorem exists_mem_normalizer_flip_aux8a {m : ℕ} {e f : Fin m → V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hef : IsHypFamily Q e f)
    {S : Finset (Fin m)} (hEven : Even S.card) (hne : S.Nonempty)
    (ih : ∀ T, T ⊂ S → Even T.card →
      (T.noncommProd (fun k => reflect Q (e k + f k)) (exists_mem_normalizer_flip_aux5 hef T)) ∈
        orthDerived Q) :
    (S.noncommProd (fun k => reflect Q (e k + f k)) (exists_mem_normalizer_flip_aux5 hef S)) ∈
      orthDerived Q := by
  obtain ⟨x, y, S', hsplit, hnot1, hnot2, hsub, hcardS'⟩ :=
    exists_mem_normalizer_flip_aux8b (V := V) (e := e) (f := f) hEven hne
  obtain ⟨t, ht⟩ := hEven
  have hevenS' : Even S'.card := by
    rw [hcardS']
    exact ⟨t - 1, by omega⟩
  rw [hsplit,
    Finset.noncommProd_insert_of_notMem (insert y S') x (fun k => reflect Q (e k + f k))
      (exists_mem_normalizer_flip_aux5 hef (insert x (insert y S'))) hnot1,
    Finset.noncommProd_insert_of_notMem S' y (fun k => reflect Q (e k + f k))
      (exists_mem_normalizer_flip_aux5 hef (insert y S')) hnot2, ← mul_assoc]
  refine Subgroup.mul_mem _ ?_ ?_
  · exact CFSG.LocalAnalysis.GLTheoremA.S172C.Rank.reflect_mul_reflect_mem_orthDerived hQ
      (by rw [exists_mem_normalizer_flip_aux1 hef x]; exact one_ne_zero)
      (by rw [exists_mem_normalizer_flip_aux1 hef y]; exact one_ne_zero)
  · rw [show S'.noncommProd (fun k => reflect Q (e k + f k)) _ =
        S'.noncommProd (fun k => reflect Q (e k + f k))
          (exists_mem_normalizer_flip_aux5 hef S') from
        congrArg (fun c => S'.noncommProd (fun k => reflect Q (e k + f k)) c)
          (Subsingleton.elim _ _)]
    exact ih S' hsub hevenS'

private theorem exists_mem_normalizer_flip_aux8 {m : ℕ} {e f : Fin m → V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hef : IsHypFamily Q e f) :
    ∀ S : Finset (Fin m), Even S.card →
      (S.noncommProd (fun k => reflect Q (e k + f k)) (exists_mem_normalizer_flip_aux5 hef S)) ∈
        orthDerived Q := by
  intro S
  refine Finset.strongInductionOn S ?_
  intro S ih hEven
  rcases S.eq_empty_or_nonempty with rfl | hne
  · rw [Finset.noncommProd_empty]; exact Subgroup.one_mem _
  · exact exists_mem_normalizer_flip_aux8a hQ hef hEven hne ih

private theorem exists_mem_normalizer_flip_aux9 {m : ℕ} {e f : Fin m → V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hef : IsHypFamily Q e f) {w : V}
    (hw : Q w ≠ 0) :
    ∀ S : Finset (Fin m), Odd S.card →
      (reflect Q w * S.noncommProd (fun k => reflect Q (e k + f k)) (exists_mem_normalizer_flip_aux5 hef S)) ∈
        orthDerived Q := by
  intro S hOdd
  have hne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h0
    rw [Finset.card_eq_zero.mpr h0] at hOdd
    obtain ⟨k, hk⟩ := hOdd; omega
  obtain ⟨x, hx⟩ := hne
  have hnot : x ∉ S.erase x := by simp
  rw [← Finset.insert_erase hx,
    Finset.noncommProd_insert_of_notMem (S.erase x) x (fun k => reflect Q (e k + f k))
      (exists_mem_normalizer_flip_aux5 hef (insert x (S.erase x))) hnot, ← mul_assoc]
  refine Subgroup.mul_mem _ ?_ ?_
  · exact CFSG.LocalAnalysis.GLTheoremA.S172C.Rank.reflect_mul_reflect_mem_orthDerived hQ hw
      (by rw [exists_mem_normalizer_flip_aux1 hef x]; exact one_ne_zero)
  · refine exists_mem_normalizer_flip_aux8 hQ hef (S.erase x) ?_
    rw [Finset.card_erase_of_mem hx]
    exact Nat.Odd.sub_odd hOdd odd_one

private theorem exists_mem_normalizer_flip_aux10 (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {l : ℕ}
    (hdim : finrank F V = 2 * l) {e f : Fin (wittRank Q l) → V} (hef : IsHypFamily Q e f)
    (hm : 1 ≤ wittRank Q l) (hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q) :
    ∃ w : V, Q w ≠ 0 ∧ (∀ i, polar Q (e i) w = 0) ∧ (∀ i, polar Q (f i) w = 0) := by
  let H : Submodule F V := Submodule.span F (Set.range (Sum.elim e f))
  have hmrank : Module.finrank F H < Module.finrank F V := by
    have hfin : Module.finrank F H = 2 * wittRank Q l := by
      rw [show H = Submodule.span F (Set.range (Sum.elim e f)) from rfl,
        finrank_span_eq_card hef.linearIndependent]
      simp only [Fintype.card_sum, Fintype.card_fin]
      ring
    have hwr : wittRank Q l = l - 1 := by unfold wittRank; rw [if_neg hminus]
    rw [hfin, hdim, hwr]
    omega
  have hHtop : H ≠ ⊤ := fun htop => by
    rw [htop, finrank_top] at hmrank; exact lt_irrefl _ hmrank
  obtain ⟨u, hu⟩ : ∃ u, u ∉ H := by
    by_contra h; push Not at h
    exact hHtop (Submodule.ext fun x => ⟨fun _ => Submodule.mem_top, fun _ => h x⟩)
  obtain ⟨w, hw1, hw2, hueq⟩ := exists_decomp_of_isHypFamily hef u
  refine ⟨w, fun hw0 => hu ?_, hw1, hw2⟩
  have hwzero : w = 0 := eq_zero_of_isHypFamily_wittRank hQ hdim hef hw1 hw2 hw0
  rw [hueq, hwzero, add_zero]
  exact Submodule.sum_mem _ fun i _ => Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl i, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr i, rfl⟩))

private theorem exists_mem_normalizer_flip_aux11 {m : ℕ} {e f : Fin m → V} (hef : IsHypFamily Q e f)
    (S : Finset (Fin m)) :
    S.noncommProd (fun k => reflect Q (e k + f k)) (exists_mem_normalizer_flip_aux5 hef S) ∈
      TauCeti.QuadraticMap.orthogonalGroup Q :=
  Finset.noncommProd_induction S _ (exists_mem_normalizer_flip_aux5 hef S) _
    (fun a b ha hb => mul_mem ha hb) (one_mem _)
    (fun k _ => reflect_mem_orthogonalGroup Q _)

private theorem exists_mem_normalizer_flip_aux12 {m : ℕ} {e f : Fin m → V} {S : Finset (Fin m)}
    {g : V ≃ₗ[F] V} (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hge : ∀ i, g (e i) = if i ∈ S then f i else e i)
    (hgf : ∀ i, g (f i) = if i ∈ S then e i else f i)
    (hginve : ∀ i, g⁻¹ (e i) = if i ∈ S then f i else e i)
    (hginvf : ∀ i, g⁻¹ (f i) = if i ∈ S then e i else f i)
    {c : Fin m → Fˣ} {a : V ≃ₗ[F] V} (hdiag : IsHypDiag Q e f c a) :
    IsHypDiag Q e f (fun i => if i ∈ S then (c i)⁻¹ else c i) (g * a * g⁻¹) := by
  refine ⟨fun i => ?_, fun i => ?_, fun v hv1 hv2 => ?_⟩
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hginve i]
    by_cases his : i ∈ S
    · rw [if_pos his, hdiag.2.1 i, map_smul, hgf i]
      simp only [his, if_true, inv_inv]
    · rw [if_neg his, hdiag.1 i, map_smul, hge i]
      simp only [his, if_false, inv_inv]
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hginvf i]
    by_cases his : i ∈ S
    · rw [if_pos his, hdiag.1 i, map_smul, hge i]
      simp only [his, if_true, inv_inv]
    · rw [if_neg his, hdiag.2.1 i, map_smul, hgf i]
      simp only [his, if_false, inv_inv]
  · have h1 : ∀ i, polar Q (e i) (g⁻¹ v) = 0 := by
      intro i
      have hpol := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgO (e i) (g⁻¹ v)
      rw [show g (g⁻¹ v) = v from LinearEquiv.apply_symm_apply g v, hge i] at hpol
      rw [← hpol]
      by_cases his : i ∈ S <;> simp [his, hv1, hv2]
    have h2 : ∀ i, polar Q (f i) (g⁻¹ v) = 0 := by
      intro i
      have hpol := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgO (f i) (g⁻¹ v)
      rw [show g (g⁻¹ v) = v from LinearEquiv.apply_symm_apply g v, hgf i] at hpol
      rw [← hpol]
      by_cases his : i ∈ S <;> simp [his, hv1, hv2]
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hdiag.2.2 (g⁻¹ v) h1 h2]
    exact LinearEquiv.apply_symm_apply g v

private theorem exists_mem_normalizer_flip_aux13 {m : ℕ} {e f : Fin m → V} {S : Finset (Fin m)}
    {p : ℕ} {A : Subgroup ↥(orthDerived Q)}
    (hAeq : ∀ g : ↥(orthDerived Q), g ∈ A ↔ InTorsionTorus Q p e f (g : V ≃ₗ[F] V))
    {n0 : V ≃ₗ[F] V} (hn0mem : n0 ∈ orthDerived Q)
    (hn0O : n0 ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (h0e : ∀ i, n0 (e i) = if i ∈ S then f i else e i)
    (h0f : ∀ i, n0 (f i) = if i ∈ S then e i else f i)
    (hinve : ∀ i, n0⁻¹ (e i) = if i ∈ S then f i else e i)
    (hinvf : ∀ i, n0⁻¹ (f i) = if i ∈ S then e i else f i) :
    (⟨n0, hn0mem⟩ : ↥(orthDerived Q)) ∈ Subgroup.normalizer (A : Set ↥(orthDerived Q)) := by
  have hmem : ∀ a : ↥(orthDerived Q), a ∈ A → ⟨n0, hn0mem⟩ * a * ⟨n0, hn0mem⟩⁻¹ ∈ A := by
    intro a ha
    rw [hAeq] at ha ⊢
    obtain ⟨c, hcp, hdiag⟩ := ha
    refine ⟨fun i => if i ∈ S then (c i)⁻¹ else c i, fun i => ?_, ?_⟩
    · by_cases his : i ∈ S <;> simp [his, hcp i]
    · rw [show ((⟨n0, hn0mem⟩ * a * ⟨n0, hn0mem⟩⁻¹ : ↥(orthDerived Q)) : V ≃ₗ[F] V)
          = n0 * (a : V ≃ₗ[F] V) * n0⁻¹ from rfl]
      exact exists_mem_normalizer_flip_aux12 hn0O h0e h0f hinve hinvf hdiag
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · exact hmem a
  · intro hb
    rw [hAeq] at hb ⊢
    obtain ⟨c, hcp, hdiag⟩ := hb
    have hdiag' := exists_mem_normalizer_flip_aux12 (g := n0⁻¹) (inv_mem hn0O) hinve hinvf h0e h0f hdiag
    have hdiag'' : IsHypDiag Q e f (fun i => if i ∈ S then (c i)⁻¹ else c i) (a : V ≃ₗ[F] V) := by
      have h := hdiag'
      rw [show n0⁻¹ * ((⟨n0, hn0mem⟩ * a * ⟨n0, hn0mem⟩⁻¹ : ↥(orthDerived Q)) : V ≃ₗ[F] V)
          * (n0⁻¹)⁻¹ = (a : V ≃ₗ[F] V) by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group] at h
      exact h
    refine ⟨fun i => if i ∈ S then (c i)⁻¹ else c i, fun i => ?_, hdiag''⟩
    by_cases his : i ∈ S <;> simp [his, hcp i]

private theorem exists_mem_normalizer_flip_aux17 {m : ℕ} {e f : Fin m → V} {S : Finset (Fin m)}
    {n0 : V ≃ₗ[F] V} (h0e : ∀ i, n0 (e i) = if i ∈ S then f i else e i)
    (h0f : ∀ i, n0 (f i) = if i ∈ S then e i else f i) :
    (∀ i ∈ S, n0 (e i) = f i ∧ n0 (f i) = e i) ∧
      ∀ i, i ∉ S → n0 (e i) = e i ∧ n0 (f i) = f i := by
  constructor
  · intro i hi
    exact ⟨by rw [h0e i, if_pos hi], by rw [h0f i, if_pos hi]⟩
  · intro i hi
    exact ⟨by rw [h0e i, if_neg hi], by rw [h0f i, if_neg hi]⟩

private theorem exists_mem_normalizer_flip_aux16 {m : ℕ} {e f : Fin m → V} {S : Finset (Fin m)}
    {p : ℕ} {A : Subgroup ↥(orthDerived Q)}
    (hAeq : ∀ g : ↥(orthDerived Q), g ∈ A ↔ InTorsionTorus Q p e f (g : V ≃ₗ[F] V))
    {n0 : V ≃ₗ[F] V} (hn0mem : n0 ∈ orthDerived Q)
    (hn0O : n0 ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (h0e : ∀ i, n0 (e i) = if i ∈ S then f i else e i)
    (h0f : ∀ i, n0 (f i) = if i ∈ S then e i else f i) :
    ∃ n : ↥(orthDerived Q), n ∈ Subgroup.normalizer (A : Set ↥(orthDerived Q)) ∧
      (∀ i ∈ S, (n : V ≃ₗ[F] V) (e i) = f i ∧ (n : V ≃ₗ[F] V) (f i) = e i) ∧
      ∀ i, i ∉ S → (n : V ≃ₗ[F] V) (e i) = e i ∧ (n : V ≃ₗ[F] V) (f i) = f i := by
  have h0e2 : ∀ i, n0 (n0 (e i)) = e i := by
    intro i
    rw [h0e i]
    by_cases his : i ∈ S
    · rw [if_pos his, h0f i, if_pos his]
    · rw [if_neg his, h0e i, if_neg his]
  have h0f2 : ∀ i, n0 (n0 (f i)) = f i := by
    intro i
    rw [h0f i]
    by_cases his : i ∈ S
    · rw [if_pos his, h0e i, if_pos his]
    · rw [if_neg his, h0f i, if_neg his]
  have hinve : ∀ i, n0⁻¹ (e i) = if i ∈ S then f i else e i := by
    intro i
    rw [show n0⁻¹ (e i) = n0 (e i) from by
      apply n0.injective
      rw [show n0 (n0⁻¹ (e i)) = e i from LinearEquiv.apply_symm_apply n0 (e i), h0e2 i]]
    exact h0e i
  have hinvf : ∀ i, n0⁻¹ (f i) = if i ∈ S then e i else f i := by
    intro i
    rw [show n0⁻¹ (f i) = n0 (f i) from by
      apply n0.injective
      rw [show n0 (n0⁻¹ (f i)) = f i from LinearEquiv.apply_symm_apply n0 (f i), h0f2 i]]
    exact h0f i
  refine ⟨⟨n0, hn0mem⟩, exists_mem_normalizer_flip_aux13 hAeq hn0mem hn0O h0e h0f hinve hinvf,
    ?_⟩
  exact exists_mem_normalizer_flip_aux17 h0e h0f

private theorem exists_mem_normalizer_flip_aux14 {m : ℕ} {e f : Fin m → V} {S : Finset (Fin m)}
    {p : ℕ} {A : Subgroup ↥(orthDerived Q)}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hef : IsHypFamily Q e f)
    (hAeq : ∀ g : ↥(orthDerived Q), g ∈ A ↔ InTorsionTorus Q p e f (g : V ≃ₗ[F] V))
    (hEven : Even S.card) :
    ∃ n : ↥(orthDerived Q), n ∈ Subgroup.normalizer (A : Set ↥(orthDerived Q)) ∧
      (∀ i ∈ S, (n : V ≃ₗ[F] V) (e i) = f i ∧ (n : V ≃ₗ[F] V) (f i) = e i) ∧
      ∀ i, i ∉ S → (n : V ≃ₗ[F] V) (e i) = e i ∧ (n : V ≃ₗ[F] V) (f i) = f i := by
  let n0 : V ≃ₗ[F] V := S.noncommProd (fun k => reflect Q (e k + f k))
    (exists_mem_normalizer_flip_aux5 hef S)
  exact exists_mem_normalizer_flip_aux16 hAeq (exists_mem_normalizer_flip_aux8 hQ hef S hEven)
    (exists_mem_normalizer_flip_aux11 hef S) (exists_mem_normalizer_flip_aux6 hef S)
    (exists_mem_normalizer_flip_aux7 hef S)

private theorem exists_mem_normalizer_flip_aux15 {l : ℕ}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hdim : finrank F V = 2 * l) {p : ℕ}
    {e f : Fin (wittRank Q l) → V} (hef : IsHypFamily Q e f)
    {A : Subgroup ↥(orthDerived Q)}
    (hAeq : ∀ g : ↥(orthDerived Q), g ∈ A ↔ InTorsionTorus Q p e f (g : V ≃ₗ[F] V))
    (S : Finset (Fin (wittRank Q l))) (hOdd : Odd S.card)
    (hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q) :
    ∃ n : ↥(orthDerived Q), n ∈ Subgroup.normalizer (A : Set ↥(orthDerived Q)) ∧
      (∀ i ∈ S, (n : V ≃ₗ[F] V) (e i) = f i ∧ (n : V ≃ₗ[F] V) (f i) = e i) ∧
      ∀ i, i ∉ S → (n : V ≃ₗ[F] V) (e i) = e i ∧ (n : V ≃ₗ[F] V) (f i) = f i := by
  have hne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro h0
    rw [Finset.card_eq_zero.mpr h0] at hOdd
    obtain ⟨k, hk⟩ := hOdd; omega
  have hm : 1 ≤ wittRank Q l := by
    have hc := Finset.card_pos.mpr hne
    have hle := Finset.card_le_univ S
    simp only [Fintype.card_fin] at hle
    omega
  obtain ⟨w, hw, hw1, hw2⟩ := exists_mem_normalizer_flip_aux10 hQ hdim hef hm hminus
  let P : V ≃ₗ[F] V := S.noncommProd (fun k => reflect Q (e k + f k))
    (exists_mem_normalizer_flip_aux5 hef S)
  let n0 : V ≃ₗ[F] V := reflect Q w * P
  have hn0mem : n0 ∈ orthDerived Q := exists_mem_normalizer_flip_aux9 hQ hef hw S hOdd
  have hPO : P ∈ TauCeti.QuadraticMap.orthogonalGroup Q := exists_mem_normalizer_flip_aux11 hef S
  have hn0O : n0 ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    mul_mem (reflect_mem_orthogonalGroup Q w) hPO
  have hPe : ∀ i, P (e i) = if i ∈ S then f i else e i := exists_mem_normalizer_flip_aux6 hef S
  have hPf : ∀ i, P (f i) = if i ∈ S then e i else f i := exists_mem_normalizer_flip_aux7 hef S
  have hwfixe : ∀ i, reflect Q w (e i) = e i := fun i =>
    reflect_apply_of_polar_eq_zero (by rw [QuadraticMap.polar_comm]; exact hw1 i)
  have hwfixf : ∀ i, reflect Q w (f i) = f i := fun i =>
    reflect_apply_of_polar_eq_zero (by rw [QuadraticMap.polar_comm]; exact hw2 i)
  have h0e : ∀ i, n0 (e i) = if i ∈ S then f i else e i := by
    intro i
    show reflect Q w (P (e i)) = _
    rw [hPe i]
    by_cases his : i ∈ S
    · rw [if_pos his, hwfixf i]
    · rw [if_neg his, hwfixe i]
  have h0f : ∀ i, n0 (f i) = if i ∈ S then e i else f i := by
    intro i
    show reflect Q w (P (f i)) = _
    rw [hPf i]
    by_cases his : i ∈ S
    · rw [if_pos his, hwfixe i]
    · rw [if_neg his, hwfixf i]
  exact exists_mem_normalizer_flip_aux16 hAeq hn0mem hn0O h0e h0f

theorem exists_mem_normalizer_flip (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {l : ℕ}
    (hdim : finrank F V = 2 * l) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F - 1) {e f : Fin (wittRank Q l) → V} (hef : IsHypFamily Q e f)
    {A : Subgroup ↥(orthDerived Q)}
    (hAeq : ∀ g : ↥(orthDerived Q), g ∈ A ↔ InTorsionTorus Q p e f (g : V ≃ₗ[F] V))
    (S : Finset (Fin (wittRank Q l)))
    (hS : Even S.card ∨ ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q) :
    ∃ n : ↥(orthDerived Q), n ∈ Subgroup.normalizer (A : Set ↥(orthDerived Q)) ∧
      (∀ i ∈ S, (n : V ≃ₗ[F] V) (e i) = f i ∧ (n : V ≃ₗ[F] V) (f i) = e i) ∧
      ∀ i, i ∉ S → (n : V ≃ₗ[F] V) (e i) = e i ∧ (n : V ≃ₗ[F] V) (f i) = f i := by
  by_cases hEven : Even S.card
  · exact exists_mem_normalizer_flip_aux14 hQ hef hAeq hEven
  · exact exists_mem_normalizer_flip_aux15 hQ hdim hef hAeq S (Nat.not_even_iff_odd.mp hEven)
      (hS.resolve_left hEven)

private theorem eichler_mem_supportedFixedDerived_of_weightOne_aux1 {m : ℕ} {e f : Fin m → V}
    (hef : IsHypFamily Q e f) {c : Fin m → Fˣ} {d : V ≃ₗ[F] V}
    (hd : IsHypDiag Q e f c d) {j : Fin m} (hcj : c j ≠ 1) (hc1 : ∀ i, i ≠ j → c i = 1)
    {a : V} (ha1 : QuadraticMap.polar Q (e j) a = 0) (ha2 : QuadraticMap.polar Q (f j) a = 0) :
    d a = a := by
  obtain ⟨w, hw1, hw2, hv⟩ := exists_decomp_of_isHypFamily hef a
  have hdw : d w = w := hd.2.2 w hw1 hw2
  have hsum : d (∑ i, (QuadraticMap.polar Q a (f i) • e i +
      QuadraticMap.polar Q a (e i) • f i)) =
      ∑ i, (QuadraticMap.polar Q a (f i) • e i + QuadraticMap.polar Q a (e i) • f i) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_add, map_smul, map_smul, hd.1 i, hd.2.1 i]
    by_cases hij : i = j
    · subst hij
      have h1 : QuadraticMap.polar Q a (f i) = 0 := by
        rw [QuadraticMap.polar_comm]; exact ha2
      have h2 : QuadraticMap.polar Q a (e i) = 0 := by
        rw [QuadraticMap.polar_comm]; exact ha1
      rw [h1, h2]; simp
    · rw [hc1 i hij]; simp
  rw [hv, map_add, hdw, hsum]

private theorem eichler_mem_supportedFixedDerived_of_weightOne_aux2 {m : ℕ} {e f : Fin m → V}
    (hef : IsHypFamily Q e f) {c : Fin m → Fˣ} {d : V ≃ₗ[F] V}
    (hd : IsHypDiag Q e f c d) {j : Fin m} (hcj : c j ≠ 1) (hc1 : ∀ i, i ≠ j → c i = 1)
    (hdO : d ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    fixedSpace d = LinearMap.ker (polarBilin Q (e j)) ⊓ LinearMap.ker (polarBilin Q (f j)) := by
  ext x
  rw [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker, QuadraticMap.polarBilin_apply_apply,
    QuadraticMap.polarBilin_apply_apply, mem_fixedSpace]
  constructor
  · intro hx
    constructor
    · have h := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hdO (e j) x
      rw [hx, hd.1 j] at h
      have h2 : ((c j : Fˣ) : F) * QuadraticMap.polar Q (e j) x =
          QuadraticMap.polar Q (e j) x := by
        rw [← polar_smul_left_eq, h]
      have h3 : (((c j : Fˣ) : F) - 1) * QuadraticMap.polar Q (e j) x = 0 := by
        rw [sub_mul, one_mul, h2, sub_self]
      rcases mul_eq_zero.mp h3 with h4 | h4
      · exact absurd (Units.ext (sub_eq_zero.mp h4)) hcj
      · exact h4
    · have h := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hdO (f j) x
      rw [hx, hd.2.1 j] at h
      have h2 : (((c j)⁻¹ : Fˣ) : F) * QuadraticMap.polar Q (f j) x =
          QuadraticMap.polar Q (f j) x := by
        rw [← polar_smul_left_eq, h]
      have h3 : ((((c j)⁻¹ : Fˣ) : F) - 1) * QuadraticMap.polar Q (f j) x = 0 := by
        rw [sub_mul, one_mul, h2, sub_self]
      rcases mul_eq_zero.mp h3 with h4 | h4
      · exact absurd (inv_eq_one.mp (Units.ext (sub_eq_zero.mp h4))) hcj
      · exact h4
  · rintro ⟨h1, h2⟩
    exact eichler_mem_supportedFixedDerived_of_weightOne_aux1 hef hd hcj hc1 h1 h2

private theorem eichler_mem_supportedFixedDerived_of_weightOne_aux4 {d : V ≃ₗ[F] V} {a b : V}
    (hEsub : ∀ x : V, eichler Q a b x - x ∈ fixedSpace d)
    (hEcent : eichler Q a b ∈ Subgroup.centralizer ({d} : Set (V ≃ₗ[F] V))) :
    ∀ v ∈ othersSpace d.toLinearMap (X - 1), eichler Q a b v = v := by
  rw [fixes_othersSpace_iff]
  intro k hk hk1 hk1' v hv
  have hEdiff := hEsub v
  have hEv : eichler Q a b v ∈ primaryComponent d.toLinearMap k :=
    apply_mem_primaryComponent (commute_toLinearMap_of_mem_centralizer d hEcent) hv
  have hdiffk : eichler Q a b v - v ∈ primaryComponent d.toLinearMap k :=
    Submodule.sub_mem _ hEv hv
  by_cases hmem : (X - 1 : F[X]) ∈ primaryFactors d.toLinearMap
  · rw [fixedSpace_eq_primaryComponent] at hEdiff
    have h0 : eichler Q a b v - v = 0 := by
      obtain ⟨u, v', huv⟩ := isCoprime_of_mem_primaryFactors hmem hk (Ne.symm hk1)
      have h1 := congrArg (fun f : F[X] => aeval d.toLinearMap f (eichler Q a b v - v)) huv
      simp only [map_add, map_mul, map_one, LinearMap.add_apply, Module.End.mul_apply,
        Module.End.one_apply, mem_primaryComponent.mp hEdiff, mem_primaryComponent.mp hdiffk,
        map_zero, add_zero] at h1
      exact h1.symm
    exact sub_eq_zero.mp h0
  · rw [fixedSpace_eq_bot_of_not_mem hmem, Submodule.mem_bot] at hEdiff
    exact sub_eq_zero.mp hEdiff

private theorem eichler_mem_supportedFixedDerived_of_weightOne_aux3 {m : ℕ} {e f : Fin m → V}
    (hef : IsHypFamily Q e f) {c : Fin m → Fˣ} {d : V ≃ₗ[F] V}
    (hd : IsHypDiag Q e f c d) {j : Fin m} (hcj : c j ≠ 1) (hc1 : ∀ i, i ≠ j → c i = 1)
    (hdO : d ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {a b : V}
    (ha1 : QuadraticMap.polar Q (e j) a = 0) (ha2 : QuadraticMap.polar Q (f j) a = 0)
    (hb1 : QuadraticMap.polar Q (e j) b = 0) (hb2 : QuadraticMap.polar Q (f j) b = 0) :
    eichler Q a b ∈ supportedBlock Q d (X - 1) := by
  have haW : a ∈ fixedSpace d :=
    mem_fixedSpace.mpr (eichler_mem_supportedFixedDerived_of_weightOne_aux1 hef hd hcj hc1 ha1 ha2)
  have hbW : b ∈ fixedSpace d :=
    mem_fixedSpace.mpr (eichler_mem_supportedFixedDerived_of_weightOne_aux1 hef hd hcj hc1 hb1 hb2)
  have hda : d a = a := eichler_mem_supportedFixedDerived_of_weightOne_aux1 hef hd hcj hc1 ha1 ha2
  have hdb : d b = b := eichler_mem_supportedFixedDerived_of_weightOne_aux1 hef hd hcj hc1 hb1 hb2
  have hEorth : eichler Q a b ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    eichler_mem_orthogonalGroup Q a b
  have hEcomm : eichler Q a b * d = d * eichler Q a b := by
    have h1 : d * eichler Q a b * d⁻¹ = eichler Q a b := by
      rw [eichler_conj hdO a b, hda, hdb]
    calc eichler Q a b * d = (d * eichler Q a b * d⁻¹) * d := by rw [h1]
      _ = d * eichler Q a b := by group
  have hEcent : eichler Q a b ∈ Subgroup.centralizer ({d} : Set (V ≃ₗ[F] V)) :=
    (mem_centralizer_iff d).mpr fun v => by
      have := congrArg (fun g : V ≃ₗ[F] V => g v) hEcomm
      simpa using this
  have hEsub : ∀ x : V, eichler Q a b x - x ∈ fixedSpace d := by
    intro x
    by_cases hg : Q a = 0 ∧ QuadraticMap.polar Q a b = 0
    · have h1 : eichler Q a b x - x =
          QuadraticMap.polar Q x a • b -
            (QuadraticMap.polar Q x b + Q b * QuadraticMap.polar Q x a) • a := by
        rw [eichler_apply hg.1 hg.2]; abel
      rw [h1]
      exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hbW) (Submodule.smul_mem _ _ haW)
    · rw [eichler_of_not hg]
      simp
  exact mem_supportedBlock.mpr ⟨Subgroup.mem_inf.mpr ⟨hEorth, hEcent⟩,
    eichler_mem_supportedFixedDerived_of_weightOne_aux4 hEsub hEcent⟩

private theorem eichler_mem_supportedFixedDerived_of_weightOne_aux5 {d : ↥(orthDerived Q)} {a b : V}
    (haW : a ∈ fixedSpace (d : V ≃ₗ[F] V)) (hbW : b ∈ fixedSpace (d : V ≃ₗ[F] V))
    (hg : eichler Q a b ∈ supportedBlock Q (d : V ≃ₗ[F] V) (X - 1)) :
    restrictFixed Q (d : V ≃ₗ[F] V) ⟨eichler Q a b, hg⟩ =
      eichler (Q.comp (fixedSpace (d : V ≃ₗ[F] V)).subtype) ⟨a, haW⟩ ⟨b, hbW⟩ := by
  refine LinearEquiv.ext fun w => Subtype.ext ?_
  rw [coe_restrictFixed]
  change eichler Q a b (w : V) =
    ((eichler (Q.comp (fixedSpace (d : V ≃ₗ[F] V)).subtype) ⟨a, haW⟩ ⟨b, hbW⟩) w : V)
  by_cases hgen : Q a = 0 ∧ QuadraticMap.polar Q a b = 0
  · rw [eichler_apply hgen.1 hgen.2]
    have hgen' : (Q.comp (fixedSpace (d : V ≃ₗ[F] V)).subtype) ⟨a, haW⟩ = 0 ∧
        QuadraticMap.polar (Q.comp (fixedSpace (d : V ≃ₗ[F] V)).subtype)
          ⟨a, haW⟩ ⟨b, hbW⟩ = 0 := by
      refine ⟨?_, ?_⟩
      · simpa using hgen.1
      · rw [polar_comp_subtype]; exact hgen.2
    rw [eichler_apply hgen'.1 hgen'.2]
    simp only [QuadraticMap.comp_apply, Submodule.coe_add, Submodule.coe_sub,
      Submodule.coe_smul, polar_comp_subtype, Submodule.coe_subtype]
  · rw [eichler_of_not hgen]
    have hgen' : ¬((Q.comp (fixedSpace (d : V ≃ₗ[F] V)).subtype) ⟨a, haW⟩ = 0 ∧
        QuadraticMap.polar (Q.comp (fixedSpace (d : V ≃ₗ[F] V)).subtype)
          ⟨a, haW⟩ ⟨b, hbW⟩ = 0) := by
      rintro ⟨h1, h2⟩
      exact hgen ⟨by simpa using h1, (polar_comp_subtype _ _ _).symm.trans h2⟩
    rw [eichler_of_not hgen']
    rfl

theorem eichler_mem_supportedFixedDerived_of_weightOne
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {m : ℕ} {e f : Fin m → V}
    (hef : IsHypFamily Q e f) {c : Fin m → Fˣ} {d : ↥(orthDerived Q)}
    (hd : IsHypDiag Q e f c (d : V ≃ₗ[F] V)) {j : Fin m} (hcj : c j ≠ 1)
    (hc1 : ∀ i, i ≠ j → c i = 1) {a b : V} (ha1 : QuadraticMap.polar Q (e j) a = 0)
    (ha2 : QuadraticMap.polar Q (f j) a = 0) (hb1 : QuadraticMap.polar Q (e j) b = 0)
    (hb2 : QuadraticMap.polar Q (f j) b = 0) :
    eichler Q a b ∈ supportedFixedDerived Q (d : V ≃ₗ[F] V) := by
  have hdO : (d : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthDerived_le_orthogonalGroup d.2
  have haW : a ∈ fixedSpace (d : V ≃ₗ[F] V) :=
    mem_fixedSpace.mpr (eichler_mem_supportedFixedDerived_of_weightOne_aux1 hef hd hcj hc1 ha1 ha2)
  have hbW : b ∈ fixedSpace (d : V ≃ₗ[F] V) :=
    mem_fixedSpace.mpr (eichler_mem_supportedFixedDerived_of_weightOne_aux1 hef hd hcj hc1 hb1 hb2)
  have hg := eichler_mem_supportedFixedDerived_of_weightOne_aux3 hef hd hcj hc1 hdO ha1 ha2 hb1 hb2
  refine mem_supportedFixedDerived.mpr ⟨hg, ?_⟩
  have hres := eichler_mem_supportedFixedDerived_of_weightOne_aux5 haW hbW hg
  rw [hres]
  let P : HypPair Q := ⟨e j, f j, hef.map_e j, hef.map_f j, by simpa using hef.polar_ef j j⟩
  have hPperp : P.perp = fixedSpace (d : V ≃ₗ[F] V) := by
    rw [eichler_mem_supportedFixedDerived_of_weightOne_aux2 hef hd hcj hc1 hdO]
    rfl
  have hWnd : PolarNondegOn Q (fixedSpace (d : V ≃ₗ[F] V)) := by
    rw [← hPperp]
    exact P.polarNondegOn_perp hQ
  refine CFSG.SeitzReduction.OmegaPilot.eichler_mem_orthDerived_of_ne_zero_ne_one
    (nondegenerate_polarBilin_restrict hWnd) (Units.ne_zero (c j)) ?_ _ _
  exact fun h => hcj (Units.ext h)

private theorem eichler_mem_specialBlock_aux6 (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {d : ↥(orthDerived Q)} (hdp : (d : V ≃ₗ[F] V) ^ p = 1) :
    OddOrderIsometry Q p (d : V ≃ₗ[F] V) := by
  refine ⟨orthDerived_le_orthogonalGroup d.2, hdp, ?_, fun v hv => hQ.1 v fun w => by simpa using hv w⟩
  intro h0
  have h1 := (ringChar.spec F p).mp h0
  have hℓ : (ringChar F).Prime := by
    rw [ringChar.eq F 2]
    exact CharP.char_is_prime F 2
  rcases (Nat.dvd_prime hp).mp h1 with h2 | h2
  · exact hℓ.one_lt.ne' h2
  · exact hp2 (by rw [← h2]; exact ringChar.eq F 2)

private theorem eichler_mem_specialBlock_aux1 {u : Fˣ} (hu : u ≠ 1) {d : ↥(orthDerived Q)}
    (hdO : (d : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {x y : V} (hx : x ∈ primaryComponent (d : V ≃ₗ[F] V).toLinearMap (X - C (u : F)))
    (hy : y ∈ primaryComponent (d : V ≃ₗ[F] V).toLinearMap (X - C (u : F))) :
    QuadraticMap.polar Q x y = 0 := by
  have hdx : (d : V ≃ₗ[F] V) x = (u : F) • x := by
    have h := mem_primaryComponent.mp hx
    rw [map_sub, aeval_X, aeval_C] at h
    simpa [Algebra.algebraMap_eq_smul_one, Module.End.mul_apply, sub_eq_zero] using h
  have hdy : (d : V ≃ₗ[F] V) y = (u : F) • y := by
    have h := mem_primaryComponent.mp hy
    rw [map_sub, aeval_X, aeval_C] at h
    simpa [Algebra.algebraMap_eq_smul_one, Module.End.mul_apply, sub_eq_zero] using h
  have hu2 : (u : F) * (u : F) ≠ 1 := by
    intro h
    have h' : (u : F) ^ 2 = 1 := by rwa [pow_two]
    rcases sq_eq_one_iff.mp h' with h1 | h1
    · exact hu (Units.ext h1)
    · rw [CharTwo.neg_eq] at h1
      exact hu (Units.ext h1)
  have h1 : QuadraticMap.polar Q ((d : V ≃ₗ[F] V) x) ((d : V ≃ₗ[F] V) y) =
      QuadraticMap.polar Q x y :=
    TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hdO x y
  rw [hdx, hdy, polar_smul_left_eq, polar_smul_right_eq] at h1
  have h2 : ((u : F) * (u : F) - 1) * QuadraticMap.polar Q x y = 0 := by
    rw [sub_mul, one_mul, mul_assoc, h1, sub_self]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (sub_eq_zero.mp h3) hu2
  · exact h3

private theorem eichler_mem_specialBlock_aux2 {u : Fˣ} {d : ↥(orthDerived Q)} {a b : V}
    (hdO : (d : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (ha : (d : V ≃ₗ[F] V) a = ((u : Fˣ) : F) • a)
    (hb : (d : V ≃ₗ[F] V) b = (((u⁻¹ : Fˣ)) : F) • b) :
    eichler Q a b ∈ Subgroup.centralizer ({(d : V ≃ₗ[F] V)} : Set (V ≃ₗ[F] V)) := by
  have hconj : (d : V ≃ₗ[F] V) * eichler Q a b * (d : V ≃ₗ[F] V)⁻¹ = eichler Q a b := by
    rw [eichler_conj hdO a b, ha, hb, eichler_smul_left, smul_smul]
    congr 1
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]
  have hcomm : eichler Q a b * (d : V ≃ₗ[F] V) = (d : V ≃ₗ[F] V) * eichler Q a b := by
    calc eichler Q a b * (d : V ≃ₗ[F] V) =
        ((d : V ≃ₗ[F] V) * eichler Q a b * (d : V ≃ₗ[F] V)⁻¹) * (d : V ≃ₗ[F] V) := by
          rw [hconj]
      _ = (d : V ≃ₗ[F] V) * eichler Q a b := by group
  exact (mem_centralizer_iff _).mpr fun v => by
    have := congrArg (fun g : V ≃ₗ[F] V => g v) hcomm
    simpa using this

private theorem eichler_mem_specialBlock_aux3 (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {d : ↥(orthDerived Q)} (hdp : (d : V ≃ₗ[F] V) ^ p = 1)
    {u : Fˣ} (hu : u ≠ 1) {a b : V} (ha : (d : V ≃ₗ[F] V) a = ((u : Fˣ) : F) • a)
    (hb : (d : V ≃ₗ[F] V) b = (((u⁻¹ : Fˣ)) : F) • b)
    (hgen : Q a = 0 ∧ QuadraticMap.polar Q a b = 0) (ha0 : a ≠ 0) :
    eichler Q a b ∈ supportedBlock Q (d : V ≃ₗ[F] V) (X - C (u : F)) := by
  have hx := eichler_mem_specialBlock_aux6 hQ hp hp2 hdp
  have ha_comp : a ∈ primaryComponent (d : V ≃ₗ[F] V).toLinearMap (X - C (u : F)) := by
    rw [mem_primaryComponent, map_sub, aeval_X, aeval_C]
    have h : (↑↑d : V →ₗ[F] V) a = (u : F) • a := ha
    rw [LinearMap.sub_apply, h]
    simp [Algebra.algebraMap_eq_smul_one]
  have hh : (X - C (u : F)) ∈ primaryFactors (d : V ≃ₗ[F] V).toLinearMap :=
    CFSG.RankThree.PartOne.KCLinPlane.mem_primaryFactors_of_ne_zero
      (irreducible_X_sub_C (u : F)) (monic_X_sub_C (u : F)) ha0 ha_comp
  have hT := eichler_mem_specialBlock_aux2 hx.mem ha hb
  have hb_comp : b ∈ primaryComponent (d : V ≃ₗ[F] V).toLinearMap
      (X - C (((u⁻¹ : Fˣ) : F))) := by
    rw [mem_primaryComponent, map_sub, aeval_X, aeval_C]
    have h : (↑↑d : V →ₗ[F] V) b = (((u⁻¹ : Fˣ) : F)) • b := hb
    rw [LinearMap.sub_apply, h]
    simp [Algebra.algebraMap_eq_smul_one]
  have hdb' : (d : V ≃ₗ[F] V).symm b = (u : F) • b := by
    rw [LinearEquiv.symm_apply_eq, map_smul, hb, smul_smul, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, one_smul]
  have hb_orbit : b ∈ orbitSpace (d : V ≃ₗ[F] V).toLinearMap (X - C (u : F)) := by
    rw [orbitSpace]
    refine Submodule.mem_sup_right ?_
    rw [mem_primaryComponent_reciprocalPolynomial (by
      rw [coeff_sub, coeff_X, coeff_C]; simp [Units.ne_zero u])]
    rw [map_sub, aeval_X, aeval_C]
    have h : (↑(d : V ≃ₗ[F] V).symm : V →ₗ[F] V) b = (u : F) • b := hdb'
    rw [LinearMap.sub_apply, h]
    simp [Algebra.algebraMap_eq_smul_one]
  have ha_orbit : a ∈ orbitSpace (d : V ≃ₗ[F] V).toLinearMap (X - C (u : F)) :=
    Submodule.mem_sup_left ha_comp
  have hfix : ∀ v ∈ othersSpace (d : V ≃ₗ[F] V).toLinearMap (X - C (u : F)),
      eichler Q a b v = v := by
    intro v hv
    rw [eichler_apply hgen.1 hgen.2]
    rw [QuadraticMap.polar_comm Q v a, QuadraticMap.polar_comm Q v b,
      hx.polar_orbit_others hh ha_orbit hv, hx.polar_orbit_others hh hb_orbit hv]
    simp
  have hQpres : ∀ v ∈ orbitSpace (d : V ≃ₗ[F] V).toLinearMap (X - C (u : F)),
      Q (eichler Q a b v) = Q v := fun v _ =>
    TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (eichler_mem_orthogonalGroup Q a b) v
  exact hx.mem_supportedBlock_of_block hh hT hfix hQpres

private theorem eichler_mem_specialBlock_aux5 {u : Fˣ} (hu : u ≠ 1) {d : ↥(orthDerived Q)} {a b : V}
    (ha : (d : V ≃ₗ[F] V) a = ((u : Fˣ) : F) • a)
    (hb : (d : V ≃ₗ[F] V) b = (((u⁻¹ : Fˣ)) : F) • b)
    (hgen : Q a = 0 ∧ QuadraticMap.polar Q a b = 0)
    (hdO : (d : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (ha_comp : a ∈ primaryComponent (d : V ≃ₗ[F] V).toLinearMap (X - C (u : F)))
    (f : Module.End (AdjoinRoot (X - C (u : F)))
      (primaryComponent (d : V ≃ₗ[F] V).toLinearMap (X - C (u : F))))
    (hfapp : ∀ w, (f w : V) = eichler Q a b (w : V)) :
    LinearMap.det f = 1 := by
  haveI : Fact (Irreducible (X - C (u : F))) := ⟨irreducible_X_sub_C (u : F)⟩
  refine CFSG.RankThree.PartOne.KCLinPlane.det_eq_one_of_restrictScalars
    (natDegree_X_sub_C (u : F)) f ?_
  let a' : primaryComponent (d : V ≃ₗ[F] V).toLinearMap (X - C (u : F)) := ⟨a, ha_comp⟩
  let φ : primaryComponent (d : V ≃ₗ[F] V).toLinearMap (X - C (u : F)) →ₗ[F] F :=
    { toFun := fun w => -QuadraticMap.polar Q (w : V) b
      map_add' := by intro w w'; rw [Submodule.coe_add, QuadraticMap.polar_add_left, neg_add]
      map_smul' := by
        intro c w
        rw [Submodule.coe_smul, polar_smul_left_eq, smul_eq_mul, mul_neg]
        rfl }
  have hf_eq : f.restrictScalars F = 1 + LinearMap.smulRight φ a' := by
    refine LinearMap.ext fun w => Subtype.ext ?_
    rw [LinearMap.add_apply, Module.End.one_apply, LinearMap.smulRight_apply]
    show ((f.restrictScalars F) w : V) = (w : V) + (φ w • a' : _)
    rw [show ((f.restrictScalars F) w : V) = eichler Q a b (w : V) from hfapp w]
    rw [eichler_apply hgen.1 hgen.2,
      eichler_mem_specialBlock_aux1 hu hdO w.2 ha_comp]
    simp only [zero_smul, add_zero, mul_zero]
    rw [sub_eq_add_neg]
    show (w : V) + -(QuadraticMap.polar Q (w : V) b • a) =
      (w : V) + (-QuadraticMap.polar Q (w : V) b) • a
    rw [neg_smul]
  rw [hf_eq]
  refine det_one_add_of_range_le_ker (LinearMap.smulRight φ a') (Submodule.span F {a'})
    (fun w => Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a')) ?_
  intro u hu'
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu'
  simp [LinearMap.smulRight_apply, φ, a', hgen.2]

private theorem eichler_mem_specialBlock_aux4 {u : Fˣ} (hu : u ≠ 1) {d : ↥(orthDerived Q)} {a b : V}
    (ha : (d : V ≃ₗ[F] V) a = ((u : Fˣ) : F) • a)
    (hb : (d : V ≃ₗ[F] V) b = (((u⁻¹ : Fˣ)) : F) • b)
    (hgen : Q a = 0 ∧ QuadraticMap.polar Q a b = 0)
    (hg : eichler Q a b ∈ supportedBlock Q (d : V ≃ₗ[F] V) (X - C (u : F))) :
    blockDet Q (d : V ≃ₗ[F] V) (X - C (u : F)) ⟨eichler Q a b, hg⟩ = 1 := by
  have hdO : (d : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthDerived_le_orthogonalGroup d.2
  have ha_comp : a ∈ primaryComponent (d : V ≃ₗ[F] V).toLinearMap (X - C (u : F)) := by
    rw [mem_primaryComponent, map_sub, aeval_X, aeval_C]
    have h : (↑↑d : V →ₗ[F] V) a = (u : F) • a := ha
    rw [LinearMap.sub_apply, h]
    simp [Algebra.algebraMap_eq_smul_one]
  rw [blockDet_apply]
  set f : Module.End (AdjoinRoot (X - C (u : F)))
      (primaryComponent (d : V ≃ₗ[F] V).toLinearMap (X - C (u : F))) :=
    ((blockGL Q (d : V ≃ₗ[F] V) (X - C (u : F)) ⟨eichler Q a b, hg⟩ :
      BlockGL (d : V ≃ₗ[F] V) (X - C (u : F))) :
      Module.End (AdjoinRoot (X - C (u : F)))
        (primaryComponent (d : V ≃ₗ[F] V).toLinearMap (X - C (u : F)))) with hf
  change LinearMap.det f = 1
  exact eichler_mem_specialBlock_aux5 hu ha hb hgen hdO ha_comp f (fun w => by
    rw [hf]
    exact coe_blockGL (X - C (u : F)) ⟨eichler Q a b, hg⟩ w)

theorem eichler_mem_specialBlock (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {d : ↥(orthDerived Q)} (hdp : (d : V ≃ₗ[F] V) ^ p = 1) {u : Fˣ}
    (hu : u ≠ 1) {a b : V} (ha : (d : V ≃ₗ[F] V) a = ((u : Fˣ) : F) • a)
    (hb : (d : V ≃ₗ[F] V) b = (((u⁻¹ : Fˣ)) : F) • b) :
    eichler Q a b ∈ specialBlock Q (d : V ≃ₗ[F] V) (X - C (u : F)) := by
  by_cases hgen : Q a = 0 ∧ QuadraticMap.polar Q a b = 0
  · by_cases ha0 : a = 0
    · rw [ha0, eichler_zero_left]; exact one_mem _
    · have hg := eichler_mem_specialBlock_aux3 hQ hp hp2 hdp hu ha hb hgen ha0
      exact mem_specialBlock.mpr ⟨hg, eichler_mem_specialBlock_aux4 hu ha hb hgen hg⟩
  · rw [eichler_of_not hgen]; exact one_mem _

private theorem closureIn_eq_top_of_weightOne_aux1 {l : ℕ} {j : Fin (wittRank Q l)} (hm3 : 3 ≤ wittRank Q l) :
    ∃ k i : Fin (wittRank Q l), k ≠ j ∧ i ≠ j ∧ i ≠ k := by
  obtain ⟨k, hkj⟩ : ∃ k : Fin (wittRank Q l), k ≠ j :=
    Fintype.exists_ne_of_one_lt_card (α := Fin (wittRank Q l))
      (by rw [Fintype.card_fin]; omega) j
  obtain ⟨i, -, hi⟩ : ∃ i : Fin (wittRank Q l),
      i ∈ (Finset.univ : Finset (Fin (wittRank Q l))) ∧
      i ∉ ({j, k} : Finset (Fin (wittRank Q l))) := by
    refine Finset.exists_of_ssubset ?_
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.subset_univ _, ?_⟩
    intro hc
    have h1 : ({j, k} : Finset (Fin (wittRank Q l))).card =
        (Finset.univ : Finset (Fin (wittRank Q l))).card := congrArg Finset.card hc
    rw [Finset.card_univ, Fintype.card_fin] at h1
    have h2 : ({j, k} : Finset (Fin (wittRank Q l))).card ≤ 2 := Finset.card_le_two
    omega
  exact ⟨k, i, hkj, fun h => hi (by simp [h]), fun h => hi (by simp [h])⟩

private theorem closureIn_eq_top_of_weightOne_aux2 {Pj Pk : HypPair Q} (hek : Pk.e ∈ Pj.perp) (hfk : Pk.f ∈ Pj.perp) :
    CFSG.LieType.SeitzGeneration.OrthBlk.perp Q Pj.perp ≤ Pk.perp := by
  intro x hx
  exact HypPair.mem_perp.mpr
    ⟨CFSG.LieType.SeitzGeneration.OrthBlk.mem_perp.mp hx Pk.e hek,
     CFSG.LieType.SeitzGeneration.OrthBlk.mem_perp.mp hx Pk.f hfk⟩

private theorem closureIn_eq_top_of_weightOne_aux3 {m : ℕ} {e f : Fin m → V} {j k : Fin m}
    {K N : Subgroup ↥(orthDerived Q)}
    {Pj Pk : HypPair Q} (hPje : Pj.e = e j) (hPjf : Pj.f = f j)
    (hPke : Pk.e = e k) (hPkf : Pk.f = f k)
    {n : ↥(orthDerived Q)} (hnN : n ∈ N)
    (hne : (n : V ≃ₗ[F] V) (e j) = e k) (hnf : (n : V ≃ₗ[F] V) (f j) = f k)
    (h1K : ∀ a ∈ Pj.perp, ∀ b ∈ Pj.perp, ∃ g ∈ K, (g : V ≃ₗ[F] V) = eichler Q a b) :
    ∀ c ∈ Pk.perp, ∀ d ∈ Pk.perp, eichler Q c d ∈ (closureIn K N).map (orthDerived Q).subtype := by
  intro c hc d hd
  let n0 : V ≃ₗ[F] V := (n : V ≃ₗ[F] V)
  have hn0O : n0 ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    CFSG.RankThree.Classical.orthDerived_le_orthogonalGroup Q n.2
  have hmem : ∀ x ∈ Pk.perp, n0.symm x ∈ Pj.perp := by
    intro x hx
    refine HypPair.mem_perp.mpr ⟨?_, ?_⟩
    · rw [hPje]
      have hpol := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hn0O (e j) (n0.symm x)
      rw [show n0 (n0.symm x) = x from LinearEquiv.apply_symm_apply n0 x, hne] at hpol
      rw [← hpol]; simpa [hPke] using (HypPair.mem_perp.mp hx).1
    · rw [hPjf]
      have hpol := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hn0O (f j) (n0.symm x)
      rw [show n0 (n0.symm x) = x from LinearEquiv.apply_symm_apply n0 x, hnf] at hpol
      rw [← hpol]; simpa [hPkf] using (HypPair.mem_perp.mp hx).2
  obtain ⟨g, hgK, hgval⟩ := h1K _ (hmem c hc) _ (hmem d hd)
  have hconj := eichler_conj hn0O (n0.symm c) (n0.symm d)
  rw [LinearEquiv.apply_symm_apply n0 c, LinearEquiv.apply_symm_apply n0 d] at hconj
  refine Subgroup.mem_map.mpr ⟨n * g * n⁻¹, ?_, ?_⟩
  · exact conj_mem_closureIn hnN hgK
  · change n0 * (g : V ≃ₗ[F] V) * n0.symm = eichler Q c d
    rw [hgval]; exact hconj

private theorem closureIn_eq_top_of_weightOne_aux5 {K N : Subgroup ↥(orthDerived Q)}
    (hEq : orthDerived Q = elementaryGroup Q)
    (hle : elementaryGroup Q ≤ (closureIn K N).map (orthDerived Q).subtype) :
    closureIn K N = ⊤ := by
  refine eq_top_iff.mpr ?_
  intro g _
  have hgE : (g : V ≃ₗ[F] V) ∈ elementaryGroup Q := by rw [← hEq]; exact g.2
  have hgH : (g : V ≃ₗ[F] V) ∈ (closureIn K N).map (orthDerived Q).subtype := hle hgE
  obtain ⟨x, hx, hxval⟩ := Subgroup.mem_map.mp hgH
  have hxg : x = g := Subtype.ext hxval
  rwa [hxg] at hx

private theorem closureIn_eq_top_of_weightOne_aux4 {m : ℕ} {e f : Fin m → V} {j : Fin m}
    {K N : Subgroup ↥(orthDerived Q)} (hEq : orthDerived Q = elementaryGroup Q)
    {Pj : HypPair Q} (hPje : Pj.e = e j) (hPjf : Pj.f = f j)
    (hK : ∀ a b : V, QuadraticMap.polar Q (e j) a = 0 → QuadraticMap.polar Q (f j) a = 0 →
      QuadraticMap.polar Q (e j) b = 0 → QuadraticMap.polar Q (f j) b = 0 →
      ∀ g : ↥(orthDerived Q), (g : V ≃ₗ[F] V) = eichler Q a b → g ∈ K) :
    (∀ a ∈ Pj.perp, ∀ b ∈ Pj.perp, eichler Q a b ∈ (closureIn K N).map (orthDerived Q).subtype) ∧
      (∀ a ∈ Pj.perp, ∀ b ∈ Pj.perp, ∃ g ∈ K, (g : V ≃ₗ[F] V) = eichler Q a b) := by
  have h1K : ∀ a ∈ Pj.perp, ∀ b ∈ Pj.perp, ∃ g ∈ K, (g : V ≃ₗ[F] V) = eichler Q a b := by
    intro a ha b hb
    have ha' := HypPair.mem_perp.mp ha
    have hb' := HypPair.mem_perp.mp hb
    rw [hPje, hPjf] at ha' hb'
    have hΩ : eichler Q a b ∈ orthDerived Q := by
      rw [hEq]; exact eichler_mem_elementaryGroup Q a b
    exact ⟨⟨eichler Q a b, hΩ⟩, hK a b ha'.1 ha'.2 hb'.1 hb'.2 _ rfl, rfl⟩
  refine ⟨fun a ha b hb => ?_, h1K⟩
  obtain ⟨g, hgK, hgval⟩ := h1K a ha b hb
  exact Subgroup.mem_map.mpr ⟨g, le_closureIn_self K N hgK, hgval⟩

theorem closureIn_eq_top_of_weightOne (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {l : ℕ}
    (hdim : finrank F V = 2 * l) (hl : 4 ≤ l) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F - 1) {e f : Fin (wittRank Q l) → V} (hef : IsHypFamily Q e f)
    {A : Subgroup ↥(orthDerived Q)}
    (hAeq : ∀ g : ↥(orthDerived Q), g ∈ A ↔ InTorsionTorus Q p e f (g : V ≃ₗ[F] V))
    {j : Fin (wittRank Q l)} {K : Subgroup ↥(orthDerived Q)}
    (hK : ∀ a b : V, QuadraticMap.polar Q (e j) a = 0 → QuadraticMap.polar Q (f j) a = 0 →
      QuadraticMap.polar Q (e j) b = 0 → QuadraticMap.polar Q (f j) b = 0 →
      ∀ g : ↥(orthDerived Q), (g : V ≃ₗ[F] V) = eichler Q a b → g ∈ K) :
    closureIn K (Subgroup.normalizer (A : Set ↥(orthDerived Q))) = ⊤ := by
  classical
  set N : Subgroup ↥(orthDerived Q) := Subgroup.normalizer (A : Set ↥(orthDerived Q)) with hN
  have hT3 := exists_finrank_three_singular hQ hdim hl
  have hEq : orthDerived Q = elementaryGroup Q :=
    (CFSG.RankThree.Classical.orthDerived_eq_and_le_closure hQ hT3).1
  have hm3 : 3 ≤ wittRank Q l := by unfold wittRank; split_ifs <;> omega
  obtain ⟨k, i, hkj, hij, hik⟩ := closureIn_eq_top_of_weightOne_aux1 (Q := Q) (j := j) hm3
  have hjk : j ≠ k := Ne.symm hkj
  let Pj : HypPair Q := ⟨e j, f j, hef.map_e j, hef.map_f j, by simpa using hef.polar_ef j j⟩
  let Pk : HypPair Q := ⟨e k, f k, hef.map_e k, hef.map_f k, by simpa using hef.polar_ef k k⟩
  let Pi : HypPair Q := ⟨e i, f i, hef.map_e i, hef.map_f i, by simpa using hef.polar_ef i i⟩
  have hek : Pk.e ∈ Pj.perp := HypPair.mem_perp.mpr ⟨hef.polar_ee j k, by
    rw [QuadraticMap.polar_comm, hef.polar_ef k j, if_neg hkj]⟩
  have hfk : Pk.f ∈ Pj.perp := HypPair.mem_perp.mpr ⟨by rw [hef.polar_ef j k, if_neg hjk],
    hef.polar_ff j k⟩
  have hperp := closureIn_eq_top_of_weightOne_aux2 hek hfk
  have hW1 : PolarNondegOn Q Pj.perp := Pj.polarNondegOn_perp hQ
  have hH : ((closureIn K N).map (orthDerived Q).subtype) ≤
      TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro g ⟨x, hx, rfl⟩
    exact CFSG.RankThree.Classical.orthDerived_le_orthogonalGroup Q x.2
  obtain ⟨n, hnN, hne, hnf⟩ := exists_mem_normalizer_swap hQ hp hp2 hpq hef hAeq hjk
  obtain ⟨h1mem, h1K⟩ := closureIn_eq_top_of_weightOne_aux4 (Pj := Pj) (N := N) hEq
    (rfl : Pj.e = e j) (rfl : Pj.f = f j) hK
  have h2mem := closureIn_eq_top_of_weightOne_aux3 (N := N) (rfl : Pj.e = e j)
    (rfl : Pj.f = f j) (rfl : Pk.e = e k) (rfl : Pk.f = f k) hnN hne hnf h1K
  have hPe : Pi.e ∈ Pj.perp ⊓ Pk.perp := Submodule.mem_inf.mpr
    ⟨HypPair.mem_perp.mpr ⟨hef.polar_ee j i, by rw [QuadraticMap.polar_comm, hef.polar_ef i j,
      if_neg hij]⟩,
     HypPair.mem_perp.mpr ⟨hef.polar_ee k i, by rw [QuadraticMap.polar_comm, hef.polar_ef i k,
      if_neg hik]⟩⟩
  have hPf : Pi.f ∈ Pj.perp ⊓ Pk.perp := Submodule.mem_inf.mpr
    ⟨HypPair.mem_perp.mpr ⟨by rw [hef.polar_ef j i, if_neg (Ne.symm hij)], hef.polar_ff j i⟩,
     HypPair.mem_perp.mpr ⟨by rw [hef.polar_ef k i, if_neg (Ne.symm hik)], hef.polar_ff k i⟩⟩
  have hle := CFSG.LieType.SeitzGeneration.elementaryGroup_le_of_two hH hQ hW1 hperp h1mem h2mem
    Pi hPe hPf
  exact closureIn_eq_top_of_weightOne_aux5 hEq hle

private theorem closureIn_eq_top_of_plus_aux1 {m : ℕ} {e f : Fin m → V} (hef : IsHypFamily Q e f) :
    IsHypFamily Q f e where
  map_e := hef.map_f
  map_f := hef.map_e
  polar_ee := hef.polar_ff
  polar_ff := hef.polar_ee
  polar_ef i j := by
    rw [polar_comm, hef.polar_ef]
    by_cases h : i = j
    · rw [if_pos h.symm, if_pos h]
    · rw [if_neg (Ne.symm h), if_neg h]

private theorem closureIn_eq_top_of_plus_aux2 {A K : Subgroup ↥(orthDerived Q)} {n : ↥(orthDerived Q)}
    (hn : n ∈ Subgroup.normalizer (A : Set ↥(orthDerived Q))) {a b a' b' : V}
    (ha : (n : V ≃ₗ[F] V) a = a') (hb : (n : V ≃ₗ[F] V) b = b')
    {g : ↥(orthDerived Q)} (hg : g ∈ K) (hg' : (g : V ≃ₗ[F] V) = eichler Q a b) :
    eichler Q a' b' ∈ (closureIn K (Subgroup.normalizer (A : Set ↥(orthDerived Q)))).map
      (orthDerived Q).subtype := by
  have hmem : n * g * n⁻¹ ∈ closureIn K (Subgroup.normalizer (A : Set ↥(orthDerived Q))) :=
    conj_mem_closureIn hn hg
  refine Subgroup.mem_map.mpr ⟨_, hmem, ?_⟩
  change ((n * g * n⁻¹ : ↥(orthDerived Q)) : V ≃ₗ[F] V) = eichler Q a' b'
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hg',
    eichler_conj (orthDerived_le_orthogonalGroup n.2) a b, ha, hb]

private theorem closureIn_eq_top_of_plus_aux3 {M : Subgroup (V ≃ₗ[F] V)} {u : V} (hu : Q u = 0) (S : Set V)
    (hS : ∀ x ∈ S, polar Q u x = 0 ∧ eichler Q u x ∈ M) :
    ∀ w ∈ AddSubgroup.closure S, polar Q u w = 0 ∧ eichler Q u w ∈ M := by
  intro w hw
  induction hw using AddSubgroup.closure_induction with
  | mem x hx => exact hS x hx
  | zero => exact ⟨polar_zero_right Q u, by rw [eichler_zero_right]; exact M.one_mem⟩
  | add x y _ _ hx hy =>
      exact ⟨by rw [polar_add_right, hx.1, hy.1, add_zero],
        by rw [← eichler_mul hx.1 hy.1]; exact M.mul_mem hx.2 hy.2⟩
  | neg x _ hx =>
      exact ⟨by rw [polar_neg_right, hx.1, neg_zero],
        by rw [← eichler_inv hx.1]; exact M.inv_mem hx.2⟩

private theorem closureIn_eq_top_of_plus_aux4 (S : Set V) (hS : ∀ c : F, ∀ x ∈ S, c • x ∈ S) :
    ∀ w ∈ Submodule.span F S, w ∈ AddSubgroup.closure S := by
  have hcl : ∀ c : F, ∀ x ∈ AddSubgroup.closure S, c • x ∈ AddSubgroup.closure S := by
    intro c x hx
    induction hx using AddSubgroup.closure_induction with
    | mem y hy => exact AddSubgroup.subset_closure (hS c y hy)
    | zero => rw [smul_zero]; exact AddSubgroup.zero_mem _
    | add y z _ _ hy hz => rw [smul_add]; exact AddSubgroup.add_mem _ hy hz
    | neg y _ hy => rw [smul_neg]; exact AddSubgroup.neg_mem _ hy
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx => exact AddSubgroup.subset_closure hx
  | zero => exact AddSubgroup.zero_mem _
  | add x y _ _ hx hy => exact AddSubgroup.add_mem _ hx hy
  | smul c x _ hx => exact hcl c x hx

private theorem closureIn_eq_top_of_plus_aux11 (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {l : ℕ}
    (hdim : finrank F V = 2 * l) (hl : 4 ≤ l) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F - 1) {e f : Fin (wittRank Q l) → V} (hef : IsHypFamily Q e f)
    {A : Subgroup ↥(orthDerived Q)}
    (hAeq : ∀ g : ↥(orthDerived Q), g ∈ A ↔ InTorsionTorus Q p e f (g : V ≃ₗ[F] V))
    (i k : Fin (wittRank Q l)) (hik : i ≠ k) :
    ∃ (r : Fin (wittRank Q l)) (ni nk : ↥(orthDerived Q)),
      r ∉ ({i, k} : Finset (Fin (wittRank Q l))) ∧
      ni ∈ Subgroup.normalizer (A : Set ↥(orthDerived Q)) ∧
      nk ∈ Subgroup.normalizer (A : Set ↥(orthDerived Q)) ∧
      (∀ x ∈ ({i, r} : Finset (Fin (wittRank Q l))),
        (ni : V ≃ₗ[F] V) (e x) = f x ∧ (ni : V ≃ₗ[F] V) (f x) = e x) ∧
      (∀ x, x ∉ ({i, r} : Finset (Fin (wittRank Q l))) →
        (ni : V ≃ₗ[F] V) (e x) = e x ∧ (ni : V ≃ₗ[F] V) (f x) = f x) ∧
      (∀ x ∈ ({k, r} : Finset (Fin (wittRank Q l))),
        (nk : V ≃ₗ[F] V) (e x) = f x ∧ (nk : V ≃ₗ[F] V) (f x) = e x) ∧
      (∀ x, x ∉ ({k, r} : Finset (Fin (wittRank Q l))) →
        (nk : V ≃ₗ[F] V) (e x) = e x ∧ (nk : V ≃ₗ[F] V) (f x) = f x) := by
  classical
  have hm3 : 3 ≤ wittRank Q l := by unfold wittRank; split_ifs <;> omega
  obtain ⟨r, -, hr⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({i, k} : Finset (Fin (wittRank Q l)))) (t := Finset.univ)
    (by rw [Finset.card_univ, Fintype.card_fin]
        exact lt_of_le_of_lt Finset.card_le_two (by omega))
  have hri : r ≠ i := fun h => hr (Finset.mem_insert.mpr (Or.inl h))
  have hrk : r ≠ k := fun h => hr (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h)))
  have hcardi : Even ({i, r} : Finset (Fin (wittRank Q l))).card := by
    rw [Finset.card_pair (Ne.symm hri)]; decide
  have hcardk : Even ({k, r} : Finset (Fin (wittRank Q l))).card := by
    rw [Finset.card_pair (Ne.symm hrk)]; decide
  obtain ⟨ni, hniN, hniS, hniNot⟩ :=
    exists_mem_normalizer_flip hQ hdim hp hp2 hpq hef hAeq {i, r} (Or.inl hcardi)
  obtain ⟨nk, hnkN, hnkS, hnkNot⟩ :=
    exists_mem_normalizer_flip hQ hdim hp hp2 hpq hef hAeq {k, r} (Or.inl hcardk)
  exact ⟨r, ni, nk, hr, hniN, hnkN, hniS, hniNot, hnkS, hnkNot⟩

private theorem closureIn_eq_top_of_plus_aux12 {l : ℕ} {e f : Fin (wittRank Q l) → V}
    {a b : Fin (wittRank Q l) → V} {ni nk : ↥(orthDerived Q)} {i k r : Fin (wittRank Q l)}
    (hpair : ∀ j, (a j = e j ∧ b j = f j) ∨ (a j = f j ∧ b j = e j))
    (hik : i ≠ k) (hr : r ∉ ({i, k} : Finset (Fin (wittRank Q l))))
    (hniS : ∀ x ∈ ({i, r} : Finset (Fin (wittRank Q l))),
      (ni : V ≃ₗ[F] V) (e x) = f x ∧ (ni : V ≃ₗ[F] V) (f x) = e x)
    (hniNot : ∀ x, x ∉ ({i, r} : Finset (Fin (wittRank Q l))) →
      (ni : V ≃ₗ[F] V) (e x) = e x ∧ (ni : V ≃ₗ[F] V) (f x) = f x)
    (hnkS : ∀ x ∈ ({k, r} : Finset (Fin (wittRank Q l))),
      (nk : V ≃ₗ[F] V) (e x) = f x ∧ (nk : V ≃ₗ[F] V) (f x) = e x)
    (hnkNot : ∀ x, x ∉ ({k, r} : Finset (Fin (wittRank Q l))) →
      (nk : V ≃ₗ[F] V) (e x) = e x ∧ (nk : V ≃ₗ[F] V) (f x) = f x) :
    (ni : V ≃ₗ[F] V) (a i) = b i ∧ (ni : V ≃ₗ[F] V) (b i) = a i ∧
    (ni : V ≃ₗ[F] V) (b k) = b k ∧ (nk : V ≃ₗ[F] V) (a i) = a i ∧
    (nk : V ≃ₗ[F] V) (b k) = a k ∧ (nk : V ≃ₗ[F] V) (b i) = b i := by
  have hri : r ≠ i := fun h => hr (Finset.mem_insert.mpr (Or.inl h))
  have hrk : r ≠ k := fun h => hr (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h)))
  have hkS : k ∉ ({i, r} : Finset (Fin (wittRank Q l))) := by
    rw [Finset.mem_insert, Finset.mem_singleton]; push Not; exact ⟨hik.symm, Ne.symm hrk⟩
  have hiS : i ∉ ({k, r} : Finset (Fin (wittRank Q l))) := by
    rw [Finset.mem_insert, Finset.mem_singleton]; push Not; exact ⟨hik, fun h => hri h.symm⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases hpair i with ⟨ha1, hb1⟩ | ⟨ha1, hb1⟩
    · rw [ha1, hb1]; exact (hniS i (by simp)).1
    · rw [ha1, hb1]; exact (hniS i (by simp)).2
  · rcases hpair i with ⟨ha1, hb1⟩ | ⟨ha1, hb1⟩
    · rw [hb1, ha1]; exact (hniS i (by simp)).2
    · rw [hb1, ha1]; exact (hniS i (by simp)).1
  · rcases hpair k with ⟨ha1, hb1⟩ | ⟨ha1, hb1⟩
    · rw [hb1]; exact (hniNot k hkS).2
    · rw [hb1]; exact (hniNot k hkS).1
  · rcases hpair i with ⟨ha1, hb1⟩ | ⟨ha1, hb1⟩
    · rw [ha1]; exact (hnkNot i hiS).1
    · rw [ha1]; exact (hnkNot i hiS).2
  · rcases hpair k with ⟨ha1, hb1⟩ | ⟨ha1, hb1⟩
    · rw [hb1, ha1]; exact (hnkS k (by simp)).2
    · rw [hb1, ha1]; exact (hnkS k (by simp)).1
  · rcases hpair i with ⟨ha1, hb1⟩ | ⟨ha1, hb1⟩
    · rw [hb1]; exact (hnkNot i hiS).2
    · rw [hb1]; exact (hnkNot i hiS).1

private theorem closureIn_eq_top_of_plus_aux13 {l : ℕ}
    {a b : Fin (wittRank Q l) → V} {d : ↥(orthDerived Q)} {u : Fˣ}
    {K : Subgroup ↥(orthDerived Q)} (hΩE : orthDerived Q = elementaryGroup Q)
    (ha : ∀ j, (d : V ≃ₗ[F] V) (a j) = ((u : Fˣ) : F) • a j)
    (hb : ∀ j, (d : V ≃ₗ[F] V) (b j) = (((u⁻¹ : Fˣ)) : F) • b j)
    (hK : ∀ a b : V, (d : V ≃ₗ[F] V) a = ((u : Fˣ) : F) • a →
      (d : V ≃ₗ[F] V) b = (((u⁻¹ : Fˣ)) : F) • b →
      ∀ g : ↥(orthDerived Q), (g : V ≃ₗ[F] V) = eichler Q a b → g ∈ K)
    (i k : Fin (wittRank Q l)) :
    ∀ α : F, (⟨eichler Q (a i) (α • b k),
      (by rw [hΩE]; exact eichler_mem_elementaryGroup Q _ _)⟩ : ↥(orthDerived Q)) ∈ K := by
  intro α
  have hcond : (d : V ≃ₗ[F] V) (α • b k) = (((u⁻¹ : Fˣ)) : F) • (α • b k) := by
    rw [map_smul, hb k, smul_comm]
  exact hK (a i) (α • b k) (ha i) hcond _ rfl

private theorem closureIn_eq_top_of_plus_aux5 (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {l : ℕ}
    (hdim : finrank F V = 2 * l) (hl : 4 ≤ l) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F - 1) {e f : Fin (wittRank Q l) → V} (hef : IsHypFamily Q e f)
    {A : Subgroup ↥(orthDerived Q)}
    (hAeq : ∀ g : ↥(orthDerived Q), g ∈ A ↔ InTorsionTorus Q p e f (g : V ≃ₗ[F] V))
    {c : Fin (wittRank Q l) → Fˣ} {d : ↥(orthDerived Q)}
    (hd : IsHypDiag Q e f c (d : V ≃ₗ[F] V)) {u : Fˣ} (hu : u ≠ 1)
    (hcu : ∀ i, c i = u ∨ c i = u⁻¹) {K : Subgroup ↥(orthDerived Q)}
    (hK : ∀ a b : V, (d : V ≃ₗ[F] V) a = ((u : Fˣ) : F) • a →
      (d : V ≃ₗ[F] V) b = (((u⁻¹ : Fˣ)) : F) • b →
      ∀ g : ↥(orthDerived Q), (g : V ≃ₗ[F] V) = eichler Q a b → g ∈ K)
    {a b : Fin (wittRank Q l) → V}
    (ha : ∀ j, (d : V ≃ₗ[F] V) (a j) = ((u : Fˣ) : F) • a j)
    (hb : ∀ j, (d : V ≃ₗ[F] V) (b j) = (((u⁻¹ : Fˣ)) : F) • b j)
    (hpair : ∀ j, (a j = e j ∧ b j = f j) ∨ (a j = f j ∧ b j = e j))
    (i k : Fin (wittRank Q l)) (hik : i ≠ k) :
    ∀ α : F,
      eichler Q (a i) (α • b k) ∈ (closureIn K
        (Subgroup.normalizer (A : Set ↥(orthDerived Q)))).map (orthDerived Q).subtype ∧
      eichler Q (b i) (α • b k) ∈ (closureIn K
        (Subgroup.normalizer (A : Set ↥(orthDerived Q)))).map (orthDerived Q).subtype ∧
      eichler Q (a i) (α • a k) ∈ (closureIn K
        (Subgroup.normalizer (A : Set ↥(orthDerived Q)))).map (orthDerived Q).subtype ∧
      eichler Q (b i) (α • a k) ∈ (closureIn K
        (Subgroup.normalizer (A : Set ↥(orthDerived Q)))).map (orthDerived Q).subtype := by
  classical
  have hΩE : orthDerived Q = elementaryGroup Q :=
    (CFSG.RankThree.Classical.orthDerived_eq_and_le_closure hQ
      (exists_finrank_three_singular hQ hdim hl)).1
  set NN := Subgroup.normalizer (A : Set ↥(orthDerived Q)) with hNN
  set IMG := (closureIn K NN).map (orthDerived Q).subtype with hIMG
  obtain ⟨r, ni, nk, hr, hniN, hnkN, hniS, hniNot, hnkS, hnkNot⟩ :=
    closureIn_eq_top_of_plus_aux11 hQ hdim hl hp hp2 hpq hef hAeq i k hik
  obtain ⟨hni_a, hni_b, hni_bk, hnk_a, hnk_b, hnk_bi⟩ :=
    closureIn_eq_top_of_plus_aux12 (e := e) (f := f) (a := a) (b := b)
      hpair hik hr hniS hniNot hnkS hnkNot
  have hbaseK := closureIn_eq_top_of_plus_aux13 hΩE ha hb hK i k
  have hbase : ∀ α : F, eichler Q (a i) (α • b k) ∈ IMG := fun α =>
    Subgroup.mem_map.mpr ⟨_, le_closureIn_self K NN (hbaseK α), rfl⟩
  have h1 : ∀ α : F, eichler Q (b i) (α • b k) ∈ IMG := fun α =>
    closureIn_eq_top_of_plus_aux2 hniN hni_a (by rw [map_smul, hni_bk]) (hbaseK α) rfl
  have h2 : ∀ α : F, eichler Q (a i) (α • a k) ∈ IMG := fun α =>
    closureIn_eq_top_of_plus_aux2 hnkN hnk_a (by rw [map_smul, hnk_b]) (hbaseK α) rfl
  have h3 : ∀ α : F, eichler Q (b i) (α • a k) ∈ IMG := fun α =>
    closureIn_eq_top_of_plus_aux2 (NN.mul_mem hnkN hniN)
      (by simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, hni_a, hnk_bi])
      (by simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, map_smul, hni_bk, hnk_b])
      (hbaseK α) rfl
  intro α
  exact ⟨hbase α, h1 α, h2 α, h3 α⟩

private theorem closureIn_eq_top_of_plus_aux6 (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {l : ℕ}
    (hdim : finrank F V = 2 * l) (hl : 4 ≤ l) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F - 1) {e f : Fin (wittRank Q l) → V} (hef : IsHypFamily Q e f)
    {A : Subgroup ↥(orthDerived Q)}
    (hAeq : ∀ g : ↥(orthDerived Q), g ∈ A ↔ InTorsionTorus Q p e f (g : V ≃ₗ[F] V))
    {c : Fin (wittRank Q l) → Fˣ} {d : ↥(orthDerived Q)}
    (hd : IsHypDiag Q e f c (d : V ≃ₗ[F] V)) {u : Fˣ} (hu : u ≠ 1)
    (hcu : ∀ i, c i = u ∨ c i = u⁻¹) {K : Subgroup ↥(orthDerived Q)}
    (hK : ∀ a b : V, (d : V ≃ₗ[F] V) a = ((u : Fˣ) : F) • a →
      (d : V ≃ₗ[F] V) b = (((u⁻¹ : Fˣ)) : F) • b →
      ∀ g : ↥(orthDerived Q), (g : V ≃ₗ[F] V) = eichler Q a b → g ∈ K)
    {a b : Fin (wittRank Q l) → V}
    (ha : ∀ j, (d : V ≃ₗ[F] V) (a j) = ((u : Fˣ) : F) • a j)
    (hb : ∀ j, (d : V ≃ₗ[F] V) (b j) = (((u⁻¹ : Fˣ)) : F) • b j)
    (hpair : ∀ j, (a j = e j ∧ b j = f j) ∨ (a j = f j ∧ b j = e j))
    (i k : Fin (wittRank Q l)) (hik : i ≠ k) :
    ∀ y ∈ ({e i, f i} : Set V), ∀ y' ∈ ({e k, f k} : Set V), ∀ α : F,
      eichler Q y (α • y') ∈ (closureIn K
        (Subgroup.normalizer (A : Set ↥(orthDerived Q)))).map (orthDerived Q).subtype := by
  have h4 := closureIn_eq_top_of_plus_aux5 hQ hdim hl hp hp2 hpq hef hAeq hd hu hcu hK ha hb hpair i k hik
  have hseti : ({e i, f i} : Set V) = {a i, b i} := by
    rcases hpair i with ⟨ha1, hb1⟩ | ⟨ha1, hb1⟩
    · rw [ha1, hb1]
    · rw [ha1, hb1, Set.pair_comm]
  have hsetk : ({e k, f k} : Set V) = {a k, b k} := by
    rcases hpair k with ⟨ha1, hb1⟩ | ⟨ha1, hb1⟩
    · rw [ha1, hb1]
    · rw [ha1, hb1, Set.pair_comm]
  intro y hy y' hy' α
  rw [hseti] at hy
  rw [hsetk] at hy'
  rcases hy with rfl | rfl <;> rcases hy' with rfl | rfl
  · exact (h4 α).2.2.1
  · exact (h4 α).1
  · exact (h4 α).2.2.2
  · exact (h4 α).2.1

private theorem closureIn_eq_top_of_plus_aux7 {m : ℕ} {e f : Fin m → V} (hef : IsHypFamily Q e f)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) :
    PolarNondegOn Q (Submodule.span F (Set.range e ∪ Set.range f)) := by
  let P : Fin m → HypPair Q := fun i =>
    ⟨e i, f i, hef.map_e i, hef.map_f i, by simpa using hef.polar_ef i i⟩
  have hPo : ∀ i j, i ≠ j → (P i).Orth (P j) := by
    intro i j hij
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact hef.polar_ee i j
    · rw [hef.polar_ef, if_neg hij]
    · rw [polar_comm, hef.polar_ef, if_neg (Ne.symm hij)]
    · exact hef.polar_ff i j
  intro x hx hxorth
  have hxP : x ∈ pairsPerp P := by
    refine (mem_pairsPerp P).2 fun i => ?_
    rw [HypPair.mem_perp]
    exact ⟨by rw [polar_comm]; exact hxorth (P i).e (Submodule.subset_span (Or.inl ⟨i, rfl⟩)),
      by rw [polar_comm]; exact hxorth (P i).f (Submodule.subset_span (Or.inr ⟨i, rfl⟩))⟩
  have hinf : x ∈ pairsSpan P ⊓ pairsPerp P := ⟨hx, hxP⟩
  rw [pairsSpan_inf_pairsPerp hPo hQ] at hinf
  simpa using hinf

private theorem closureIn_eq_top_of_plus_aux8 {l : ℕ} {e f : Fin (wittRank Q l) → V} (hef : IsHypFamily Q e f)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (i : Fin (wittRank Q l)) :
    ∀ w ∈ Submodule.span F (Set.range e ∪ Set.range f), polar Q (e i) w = 0 →
      w ∈ Submodule.span F ({x : V | (∃ j, j ≠ i ∧ ∃ t : F, x = t • e j) ∨
        (∃ j, j ≠ i ∧ ∃ t : F, x = t • f j)} ∪ {x : V | ∃ t : F, x = t • e i}) := by
  let H : Submodule F V := Submodule.span F (Set.range e ∪ Set.range f)
  intro w hwH hw
  obtain ⟨w0, hw1, hw2, hwdec⟩ := exists_decomp_of_isHypFamily hef w
  have hs_mem : (∑ j, (polar Q w (f j) • e j + polar Q w (e j) • f j)) ∈ H :=
    Submodule.sum_mem _ fun j _ => Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl ⟨j, rfl⟩)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨j, rfl⟩)))
  have hw0H : w0 ∈ H := by
    have h1 : w - (∑ j, (polar Q w (f j) • e j + polar Q w (e j) • f j)) = w0 := by
      nth_rewrite 1 [hwdec]; abel
    rw [← h1]
    exact Submodule.sub_mem _ hwH hs_mem
  have hw0orth : ∀ y ∈ H, polar Q w0 y = 0 := by
    intro y hy
    rw [polar_comm]
    refine polar_eq_zero_of_mem_span_left ?_ hy
    rintro s (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · exact hw1 j
    · exact hw2 j
  have hw0 : w0 = 0 := closureIn_eq_top_of_plus_aux7 hef hQ w0 hw0H hw0orth
  rw [hwdec, hw0, add_zero]
  refine Submodule.sum_mem _ fun j _ => Submodule.add_mem _ ?_ ?_
  · by_cases hji : j = i
    · rw [hji]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨1, by simp⟩))
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl (Or.inl ⟨j, hji, 1, by simp⟩)))
  · by_cases hji : j = i
    · rw [hji, show polar Q w (e i) = 0 by rw [polar_comm]; exact hw, zero_smul]
      exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl (Or.inr ⟨j, hji, 1, by simp⟩)))

private theorem closureIn_eq_top_of_plus_aux9 {l : ℕ} {e f : Fin (wittRank Q l) → V} (hef : IsHypFamily Q e f)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {M : Subgroup (V ≃ₗ[F] V)}
    (hshared : ∀ (i k : Fin (wittRank Q l)), i ≠ k →
      ∀ y ∈ ({e i, f i} : Set V), ∀ y' ∈ ({e k, f k} : Set V), ∀ α : F,
        eichler Q y (α • y') ∈ M)
    (i : Fin (wittRank Q l)) :
    ∀ w ∈ Submodule.span F (Set.range e ∪ Set.range f), polar Q (e i) w = 0 →
      eichler Q (e i) w ∈ M := by
  let S : Set V := {x : V | (∃ j, j ≠ i ∧ ∃ t : F, x = t • e j) ∨
    (∃ j, j ≠ i ∧ ∃ t : F, x = t • f j)} ∪ {x : V | ∃ t : F, x = t • e i}
  have hSsmul : ∀ c : F, ∀ x ∈ S, c • x ∈ S := by
    rintro c x hx
    rcases hx with (⟨j, hj, t, hx⟩ | ⟨j, hj, t, hx⟩) | ⟨t, hx⟩
    · rw [hx]; exact Or.inl (Or.inl ⟨j, hj, c * t, by rw [smul_smul]⟩)
    · rw [hx]; exact Or.inl (Or.inr ⟨j, hj, c * t, by rw [smul_smul]⟩)
    · rw [hx]; exact Or.inr ⟨c * t, by rw [smul_smul]⟩
  have hS : ∀ x ∈ S, polar Q (e i) x = 0 ∧ eichler Q (e i) x ∈ M := by
    rintro x hx
    rcases hx with (⟨j, hj, t, hx⟩ | ⟨j, hj, t, hx⟩) | ⟨t, hx⟩
    · rw [hx]; exact ⟨by rw [polar_smul_right_eq, hef.polar_ee i j, mul_zero],
        hshared i j (Ne.symm hj) (e i) (by simp) (e j) (by simp) t⟩
    · rw [hx]; exact ⟨by rw [polar_smul_right_eq, hef.polar_ef i j, if_neg (Ne.symm hj), mul_zero],
        hshared i j (Ne.symm hj) (e i) (by simp) (f j) (by simp) t⟩
    · rw [hx]; refine ⟨by rw [polar_smul_right_eq, hef.polar_ee i i, mul_zero], ?_⟩
      have h1 := eichler_add_smul_self (hef.map_e i) 0 t
      rw [zero_add, eichler_zero_right] at h1
      rw [h1]; exact M.one_mem
  intro w hwH hw
  exact (closureIn_eq_top_of_plus_aux3 (hef.map_e i) S hS w (closureIn_eq_top_of_plus_aux4 S hSsmul w (closureIn_eq_top_of_plus_aux8 hef hQ i w hwH hw))).2

private theorem closureIn_eq_top_of_plus_aux10 {l : ℕ} {e f : Fin (wittRank Q l) → V} (hef : IsHypFamily Q e f)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {M : Subgroup (V ≃ₗ[F] V)}
    (hshared : ∀ (i k : Fin (wittRank Q l)), i ≠ k →
      ∀ y ∈ ({e i, f i} : Set V), ∀ y' ∈ ({e k, f k} : Set V), ∀ α : F,
        eichler Q y (α • y') ∈ M)
    (i : Fin (wittRank Q l)) :
    ∀ w ∈ Submodule.span F (Set.range e ∪ Set.range f), polar Q (f i) w = 0 →
      eichler Q (f i) w ∈ M := by
  let S : Set V := {x : V | (∃ j, j ≠ i ∧ ∃ t : F, x = t • f j) ∨
    (∃ j, j ≠ i ∧ ∃ t : F, x = t • e j)} ∪ {x : V | ∃ t : F, x = t • f i}
  have hSsmul : ∀ c : F, ∀ x ∈ S, c • x ∈ S := by
    rintro c x hx
    rcases hx with (⟨j, hj, t, hx⟩ | ⟨j, hj, t, hx⟩) | ⟨t, hx⟩
    · rw [hx]; exact Or.inl (Or.inl ⟨j, hj, c * t, by rw [smul_smul]⟩)
    · rw [hx]; exact Or.inl (Or.inr ⟨j, hj, c * t, by rw [smul_smul]⟩)
    · rw [hx]; exact Or.inr ⟨c * t, by rw [smul_smul]⟩
  have hS : ∀ x ∈ S, polar Q (f i) x = 0 ∧ eichler Q (f i) x ∈ M := by
    rintro x hx
    rcases hx with (⟨j, hj, t, hx⟩ | ⟨j, hj, t, hx⟩) | ⟨t, hx⟩
    · rw [hx]; exact ⟨by rw [polar_smul_right_eq, hef.polar_ff i j, mul_zero],
        hshared i j (Ne.symm hj) (f i) (by simp) (f j) (by simp) t⟩
    · rw [hx]; exact ⟨by rw [polar_smul_right_eq, polar_comm, hef.polar_ef, if_neg hj, mul_zero],
        hshared i j (Ne.symm hj) (f i) (by simp) (e j) (by simp) t⟩
    · rw [hx]; refine ⟨by rw [polar_smul_right_eq, hef.polar_ff i i, mul_zero], ?_⟩
      have h1 := eichler_add_smul_self (hef.map_f i) 0 t
      rw [zero_add, eichler_zero_right] at h1
      rw [h1]; exact M.one_mem
  intro w hwH hw
  have hwH' : w ∈ Submodule.span F (Set.range f ∪ Set.range e) := by
    rw [Set.union_comm]; exact hwH
  exact (closureIn_eq_top_of_plus_aux3 (hef.map_f i) S hS w
    (closureIn_eq_top_of_plus_aux4 S hSsmul w (closureIn_eq_top_of_plus_aux8 (e := f) (f := e) (closureIn_eq_top_of_plus_aux1 hef) hQ i w hwH' hw))).2

private theorem closureIn_eq_top_of_plus_aux14 {l : ℕ} {e f : Fin (wittRank Q l) → V}
    {c : Fin (wittRank Q l) → Fˣ} {d : ↥(orthDerived Q)}
    (hd : IsHypDiag Q e f c (d : V ≃ₗ[F] V)) {u : Fˣ}
    (hcu : ∀ i, c i = u ∨ c i = u⁻¹) :
    ∃ a b : Fin (wittRank Q l) → V,
      (∀ j, (d : V ≃ₗ[F] V) (a j) = ((u : Fˣ) : F) • a j) ∧
      (∀ j, (d : V ≃ₗ[F] V) (b j) = (((u⁻¹ : Fˣ)) : F) • b j) ∧
      (∀ j, (a j = e j ∧ b j = f j) ∨ (a j = f j ∧ b j = e j)) := by
  classical
  let a : Fin (wittRank Q l) → V := fun j => if c j = u then e j else f j
  let b : Fin (wittRank Q l) → V := fun j => if c j = u then f j else e j
  have ha : ∀ j, (d : V ≃ₗ[F] V) (a j) = ((u : Fˣ) : F) • a j := by
    intro j
    by_cases h : c j = u
    · simp only [show a j = e j by simp [a, h], hd.1 j, h]
    · have haj : a j = f j := by simp [a, h]
      have h' : c j = u⁻¹ := (hcu j).resolve_left h
      simp only [haj, hd.2.1 j, h', inv_inv]
  have hb : ∀ j, (d : V ≃ₗ[F] V) (b j) = (((u⁻¹ : Fˣ)) : F) • b j := by
    intro j
    by_cases h : c j = u
    · simp only [show b j = f j by simp [b, h], hd.2.1 j, h, Units.val_inv_eq_inv_val]
    · have hbj : b j = e j := by simp [b, h]
      have h' : c j = u⁻¹ := (hcu j).resolve_left h
      simp only [hbj, hd.1 j, h']
  have hpair : ∀ j, (a j = e j ∧ b j = f j) ∨ (a j = f j ∧ b j = e j) := by
    intro j; by_cases h : c j = u
    · exact Or.inl ⟨by simp [a, h], by simp [b, h]⟩
    · exact Or.inr ⟨by simp [a, h], by simp [b, h]⟩
  exact ⟨a, b, ha, hb, hpair⟩

private theorem closureIn_eq_top_of_plus_aux15 {l : ℕ} (hdim : finrank F V = 2 * l)
    (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q) {e f : Fin (wittRank Q l) → V}
    (hef : IsHypFamily Q e f) :
    Submodule.span F (Set.range e ∪ Set.range f) = ⊤ := by
  have hplus_m : wittRank Q l = l := by simp [wittRank, hplus]
  rw [← Set.Sum.elim_range e f]
  apply Submodule.eq_top_of_finrank_eq
  rw [finrank_span_eq_card hef.linearIndependent]
  simp only [Fintype.card_sum, Fintype.card_fin]
  rw [hplus_m, hdim]
  ring

private theorem closureIn_eq_top_of_plus_aux16 {l : ℕ} {e f : Fin (wittRank Q l) → V}
    (hef : IsHypFamily Q e f) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {M : Subgroup (V ≃ₗ[F] V)}
    (hshared : ∀ (i k : Fin (wittRank Q l)), i ≠ k →
      ∀ y ∈ ({e i, f i} : Set V), ∀ y' ∈ ({e k, f k} : Set V), ∀ α : F,
        eichler Q y (α • y') ∈ M)
    (hspan_top : Submodule.span F (Set.range e ∪ Set.range f) = ⊤) (i : Fin (wittRank Q l)) :
    IsRootCenter Q M (e i) ∧ IsRootCenter Q M (f i) := by
  have hei0 : e i ≠ 0 := by simpa using hef.linearIndependent.ne_zero (Sum.inl i)
  have hfi0 : f i ≠ 0 := by simpa using hef.linearIndependent.ne_zero (Sum.inr i)
  have hmem : ∀ w ∈ Submodule.span F (Set.range e ∪ Set.range f),
      polar Q (e i) w = 0 → eichler Q (e i) w ∈ M :=
    closureIn_eq_top_of_plus_aux9 hef hQ hshared i
  have hmem' : ∀ w ∈ Submodule.span F (Set.range e ∪ Set.range f),
      polar Q (f i) w = 0 → eichler Q (f i) w ∈ M :=
    closureIn_eq_top_of_plus_aux10 hef hQ hshared i
  refine ⟨⟨hei0, hef.map_e i, fun w hw => hmem w ?_ hw⟩,
    ⟨hfi0, hef.map_f i, fun w hw => hmem' w ?_ hw⟩⟩
  · rw [hspan_top]; exact Submodule.mem_top
  · rw [hspan_top]; exact Submodule.mem_top

theorem closureIn_eq_top_of_plus (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {l : ℕ}
    (hdim : finrank F V = 2 * l) (hl : 4 ≤ l) (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F - 1)
    {e f : Fin (wittRank Q l) → V} (hef : IsHypFamily Q e f) {A : Subgroup ↥(orthDerived Q)}
    (hAeq : ∀ g : ↥(orthDerived Q), g ∈ A ↔ InTorsionTorus Q p e f (g : V ≃ₗ[F] V))
    {c : Fin (wittRank Q l) → Fˣ} {d : ↥(orthDerived Q)}
    (hd : IsHypDiag Q e f c (d : V ≃ₗ[F] V)) {u : Fˣ} (hu : u ≠ 1)
    (hcu : ∀ i, c i = u ∨ c i = u⁻¹) {K : Subgroup ↥(orthDerived Q)}
    (hK : ∀ a b : V, (d : V ≃ₗ[F] V) a = ((u : Fˣ) : F) • a →
      (d : V ≃ₗ[F] V) b = (((u⁻¹ : Fˣ)) : F) • b →
      ∀ g : ↥(orthDerived Q), (g : V ≃ₗ[F] V) = eichler Q a b → g ∈ K) :
    closureIn K (Subgroup.normalizer (A : Set ↥(orthDerived Q))) = ⊤ := by
  classical
  set NN := Subgroup.normalizer (A : Set ↥(orthDerived Q)) with hNN
  set II := closureIn K NN with hII
  set M := II.map (orthDerived Q).subtype with hM
  have hMO : M ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    intro g hg
    obtain ⟨h, -, rfl⟩ := Subgroup.mem_map.mp hg
    exact orthDerived_le_orthogonalGroup h.2
  obtain ⟨a, b, ha, hb, hpair⟩ := closureIn_eq_top_of_plus_aux14 hd hcu
  have hshared : ∀ (i k : Fin (wittRank Q l)), i ≠ k →
      ∀ y ∈ ({e i, f i} : Set V), ∀ y' ∈ ({e k, f k} : Set V), ∀ α : F,
        eichler Q y (α • y') ∈ M := fun i k hik =>
    closureIn_eq_top_of_plus_aux6 hQ hdim hl hp hp2 hpq hef hAeq hd hu hcu hK ha hb hpair i k hik
  have hm3 : 3 ≤ wittRank Q l := by unfold wittRank; split_ifs <;> omega
  let i : Fin (wittRank Q l) := ⟨0, by omega⟩
  have hspan_top := closureIn_eq_top_of_plus_aux15 hdim hplus hef
  obtain ⟨he, hf⟩ := closureIn_eq_top_of_plus_aux16 hef hQ hshared hspan_top i
  let P : HypPair Q := ⟨e i, f i, hef.map_e i, hef.map_f i, by simpa using hef.polar_ef i i⟩
  have hgen := elementaryGroup_le_of_hypPair hQ hMO P he hf
  have hΩE : orthDerived Q = elementaryGroup Q :=
    (CFSG.RankThree.Classical.orthDerived_eq_and_le_closure hQ
      (exists_finrank_three_singular hQ hdim hl)).1
  rw [← hΩE] at hgen
  apply eq_top_iff.mpr
  intro x _
  obtain ⟨h, hh, hx⟩ := Subgroup.mem_map.mp (hgen x.2)
  have : h = x := Subtype.ext hx
  simpa [this] using hh

theorem eichler_mem_closureIn_of_minus (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {l : ℕ}
    (hdim : finrank F V = 2 * l) (hl : 4 ≤ l) (hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F - 1)
    {e f : Fin (wittRank Q l) → V} (hef : IsHypFamily Q e f) {A : Subgroup ↥(orthDerived Q)}
    (hAeq : ∀ g : ↥(orthDerived Q), g ∈ A ↔ InTorsionTorus Q p e f (g : V ≃ₗ[F] V))
    {c : Fin (wittRank Q l) → Fˣ} {d : ↥(orthDerived Q)}
    (hd : IsHypDiag Q e f c (d : V ≃ₗ[F] V)) {u : Fˣ} (hu : u ≠ 1)
    (hcu : ∀ i, c i = u ∨ c i = u⁻¹) {K : Subgroup ↥(orthDerived Q)}
    (hK : ∀ a b : V, (d : V ≃ₗ[F] V) a = ((u : Fˣ) : F) • a →
      (d : V ≃ₗ[F] V) b = (((u⁻¹ : Fˣ)) : F) • b →
      ∀ g : ↥(orthDerived Q), (g : V ≃ₗ[F] V) = eichler Q a b → g ∈ K) :
    ∀ a b : V, a ∈ Submodule.span F (Set.range e ∪ Set.range f) →
      b ∈ Submodule.span F (Set.range e ∪ Set.range f) →
      ∀ g : ↥(orthDerived Q), (g : V ≃ₗ[F] V) = eichler Q a b →
        g ∈ closureIn K (Subgroup.normalizer (A : Set ↥(orthDerived Q))) := by
  classical
  set NN := Subgroup.normalizer (A : Set ↥(orthDerived Q)) with hNN
  set II := closureIn K NN with hII
  set M := II.map (orthDerived Q).subtype with hM
  have hMO : M ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    intro g hg
    obtain ⟨h, -, rfl⟩ := Subgroup.mem_map.mp hg
    exact orthDerived_le_orthogonalGroup h.2
  obtain ⟨av, bv, ha, hb, hpair⟩ := closureIn_eq_top_of_plus_aux14 hd hcu
  have hshared : ∀ (i k : Fin (wittRank Q l)), i ≠ k →
      ∀ y ∈ ({e i, f i} : Set V), ∀ y' ∈ ({e k, f k} : Set V), ∀ α : F,
        eichler Q y (α • y') ∈ M := fun i k hik =>
    closureIn_eq_top_of_plus_aux6 hQ hdim hl hp hp2 hpq hef hAeq hd hu hcu hK ha hb hpair i k hik
  have hm3 : 3 ≤ wittRank Q l := by unfold wittRank; split_ifs <;> omega
  let i0 : Fin (wittRank Q l) := ⟨0, by omega⟩
  have hU : PolarNondegOn Q (Submodule.span F (Set.range e ∪ Set.range f)) :=
    closureIn_eq_top_of_plus_aux7 hef hQ
  have hr := closureIn_eq_top_of_plus_aux9 hef hQ hshared i0
  have hr' := closureIn_eq_top_of_plus_aux10 hef hQ hshared i0
  have hpol : polar Q (e i0) (f i0) ≠ 0 := by rw [hef.polar_ef]; simp
  have hall := CFSG.LieType.SeitzGeneration.eichler_mem_of_relRoot hMO hU
    (Submodule.subset_span (Or.inl ⟨i0, rfl⟩))
    (Submodule.subset_span (Or.inr ⟨i0, rfl⟩)) (hef.map_e i0) (hef.map_f i0) hpol hr hr'
  intro a b ha_mem hb_mem g hg
  have hmem : eichler Q a b ∈ M := hall a ha_mem b hb_mem
  obtain ⟨h, hh, hx⟩ := Subgroup.mem_map.mp hmem
  have : g = h := Subtype.ext (hg.trans hx.symm)
  simpa [this] using hh

private theorem eq_bot_of_invariant_totallySingular_aux1
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {l : ℕ} (hdim : finrank F V = 2 * l)
    (hl : 4 ≤ l) {e f : Fin (wittRank Q l) → V} (hef : IsHypFamily Q e f)
    {X : Subgroup ↥(orthDerived Q)}
    (hX : ∀ a b : V, a ∈ Submodule.span F (Set.range e ∪ Set.range f) →
      b ∈ Submodule.span F (Set.range e ∪ Set.range f) →
      ∀ g : ↥(orthDerived Q), (g : V ≃ₗ[F] V) = eichler Q a b → g ∈ X)
    {W : Submodule F V}
    (hWi : ∀ g ∈ X, ∀ w ∈ W, (g : V ≃ₗ[F] V) w ∈ W)
    {w : V} (hwW : w ∈ W) {a : V}
    (haH : a ∈ Submodule.span F (Set.range e ∪ Set.range f)) (haQ : Q a = 0)
    {k : Fin (wittRank Q l)} (hak : polar Q a (e k + f k) = 0) :
    ∃ g : ↥(orthDerived Q), g ∈ X ∧ (g : V ≃ₗ[F] V) w - w ∈ W ∧
      Q ((g : V ≃ₗ[F] V) w - w) = (polar Q w a) ^ 2 * Q (e k + f k) := by
  classical
  have hT3 := exists_finrank_three_singular hQ hdim hl
  have hΩE : orthDerived Q = elementaryGroup Q :=
    (CFSG.RankThree.Classical.orthDerived_eq_and_le_closure hQ hT3).1
  have hbH : e k + f k ∈ Submodule.span F (Set.range e ∪ Set.range f) :=
    Submodule.add_mem _ (Submodule.subset_span (Or.inl ⟨k, rfl⟩))
      (Submodule.subset_span (Or.inr ⟨k, rfl⟩))
  have hmem : eichler Q a (e k + f k) ∈ orthDerived Q := by
    rw [hΩE]; exact eichler_mem_elementaryGroup Q a (e k + f k)
  let g : ↥(orthDerived Q) := ⟨eichler Q a (e k + f k), hmem⟩
  have hgval : (g : V ≃ₗ[F] V) = eichler Q a (e k + f k) := rfl
  have hgX : g ∈ X := hX a (e k + f k) haH hbH g hgval
  have hdiffW : (g : V ≃ₗ[F] V) w - w ∈ W := W.sub_mem (hWi g hgX w hwW) hwW
  have hQsub : ∀ x y : V, Q (x - y) = Q x + Q y - polar Q x y := by
    intro x y
    rw [sub_eq_add_neg, QuadraticMap.map_add (⇑Q) x (-y), QuadraticMap.map_neg,
      QuadraticMap.polar_neg_right]
    abel
  have hD : (g : V ≃ₗ[F] V) w - w
      = (polar Q w a) • (e k + f k)
        - (polar Q w (e k + f k) + Q (e k + f k) * polar Q w a) • a := by
    rw [hgval, eichler_apply haQ hak]
    abel
  have hQba : polar Q (e k + f k) a = 0 := by
    rw [QuadraticMap.polar_comm Q (e k + f k) a]; exact hak
  have hQval : Q ((g : V ≃ₗ[F] V) w - w) = (polar Q w a) ^ 2 * Q (e k + f k) := by
    rw [hD, hQsub, QuadraticMap.map_smul, QuadraticMap.map_smul,
      QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, haQ, hQba]
    simp only [smul_zero, mul_zero, sub_zero, add_zero, smul_eq_mul]
    ring
  exact ⟨g, hgX, hdiffW, hQval⟩

private theorem eq_bot_of_invariant_totallySingular_aux2
    {l : ℕ} {e f : Fin (wittRank Q l) → V} (hef : IsHypFamily Q e f)
    {X : Subgroup ↥(orthDerived Q)} {W : Submodule F V}
    (hWs : ∀ w ∈ W, Q w = 0) {w : V} {a : V} (haB : polar Q w a ≠ 0)
    {k : Fin (wittRank Q l)}
    (hres : ∃ g : ↥(orthDerived Q), g ∈ X ∧ (g : V ≃ₗ[F] V) w - w ∈ W ∧
      Q ((g : V ≃ₗ[F] V) w - w) = (polar Q w a) ^ 2 * Q (e k + f k)) :
    False := by
  obtain ⟨g, -, hdiffW, hQval⟩ := hres
  have hQb : Q (e k + f k) = 1 := by
    rw [QuadraticMap.map_add (⇑Q) (e k) (f k), hef.map_e, hef.map_f, hef.polar_ef,
      if_pos rfl]
    ring
  have hQzero : Q ((g : V ≃ₗ[F] V) w - w) = 0 := hWs _ hdiffW
  have hprod : (polar Q w a) ^ 2 * Q (e k + f k) = 0 := by rw [← hQval, hQzero]
  rw [hQb, mul_one] at hprod
  have hsq : (polar Q w a) * (polar Q w a) = 0 := by simpa [pow_two] using hprod
  exact haB (mul_self_eq_zero.mp hsq)

private theorem eq_bot_of_invariant_totallySingular_aux3
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {l : ℕ} (hdim : finrank F V = 2 * l)
    (hl : 4 ≤ l) {e f : Fin (wittRank Q l) → V} (hef : IsHypFamily Q e f)
    {X : Subgroup ↥(orthDerived Q)}
    (hX : ∀ a b : V, a ∈ Submodule.span F (Set.range e ∪ Set.range f) →
      b ∈ Submodule.span F (Set.range e ∪ Set.range f) →
      ∀ g : ↥(orthDerived Q), (g : V ≃ₗ[F] V) = eichler Q a b → g ∈ X)
    {W : Submodule F V} (hWs : ∀ w ∈ W, Q w = 0)
    (hWi : ∀ g ∈ X, ∀ w ∈ W, (g : V ≃ₗ[F] V) w ∈ W)
    {w : V} (hwW : w ∈ W) (s : V)
    (hsdef : s = ∑ i, (polar Q w (f i) • e i + polar Q w (e i) • f i)) : s = 0 := by
  by_contra hs
  have hcard : 1 < Fintype.card (Fin (wittRank Q l)) := by
    rw [Fintype.card_fin]; unfold wittRank; split_ifs <;> omega
  have hcoef : ∃ i : Fin (wittRank Q l), polar Q w (f i) ≠ 0 ∨ polar Q w (e i) ≠ 0 := by
    by_contra h
    simp only [not_exists, not_or, not_ne_iff] at h
    exact hs (by
      rw [hsdef]
      apply Finset.sum_eq_zero
      intro i _
      rw [(h i).1, (h i).2]
      simp)
  obtain ⟨i, hi | hi⟩ := hcoef
  · obtain ⟨k, hki⟩ := Fintype.exists_ne_of_one_lt_card hcard i
    have hak : polar Q (f i) (e k + f k) = 0 := by
      rw [QuadraticMap.polar_add_right, QuadraticMap.polar_comm Q (f i) (e k),
        hef.polar_ef, hef.polar_ff]
      simp [hki]
    exact eq_bot_of_invariant_totallySingular_aux2 hef hWs hi
      (eq_bot_of_invariant_totallySingular_aux1 hQ hdim hl hef hX hWi hwW
        (Submodule.subset_span (Or.inr ⟨i, rfl⟩)) (hef.map_f i) hak)
  · obtain ⟨k, hki⟩ := Fintype.exists_ne_of_one_lt_card hcard i
    have hak : polar Q (e i) (e k + f k) = 0 := by
      rw [QuadraticMap.polar_add_right, hef.polar_ee, hef.polar_ef]
      simp [Ne.symm hki]
    exact eq_bot_of_invariant_totallySingular_aux2 hef hWs hi
      (eq_bot_of_invariant_totallySingular_aux1 hQ hdim hl hef hX hWi hwW
        (Submodule.subset_span (Or.inl ⟨i, rfl⟩)) (hef.map_e i) hak)

theorem eq_bot_of_invariant_totallySingular (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {l : ℕ} (hdim : finrank F V = 2 * l) (hl : 4 ≤ l) {e f : Fin (wittRank Q l) → V}
    (hef : IsHypFamily Q e f) {X : Subgroup ↥(orthDerived Q)}
    (hX : ∀ a b : V, a ∈ Submodule.span F (Set.range e ∪ Set.range f) →
      b ∈ Submodule.span F (Set.range e ∪ Set.range f) →
      ∀ g : ↥(orthDerived Q), (g : V ≃ₗ[F] V) = eichler Q a b → g ∈ X)
    {W : Submodule F V} (hWs : ∀ w ∈ W, Q w = 0)
    (hWi : ∀ g ∈ X, ∀ w ∈ W, (g : V ≃ₗ[F] V) w ∈ W) : W = ⊥ := by
  classical
  refine le_antisymm ?_ bot_le
  intro w hwW
  rw [Submodule.mem_bot]
  obtain ⟨t, ht1, ht2, hw⟩ := exists_decomp_of_isHypFamily hef w
  set s : V := ∑ i, (polar Q w (f i) • e i + polar Q w (e i) • f i) with hsdef
  have hs0 : s = 0 :=
    eq_bot_of_invariant_totallySingular_aux3 hQ hdim hl hef hX hWs hWi hwW s hsdef
  have hws : w = s + t := hw
  rw [hs0, zero_add] at hws
  have hQt : Q t = 0 := by rw [← hws]; exact hWs w hwW
  have ht0 : t = 0 := eq_zero_of_isHypFamily_wittRank hQ hdim hef ht1 ht2 hQt
  rw [hws, ht0]

theorem eq_bot_of_closureIn_le_normalizer (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {l : ℕ}
    (hdim : finrank F V = 2 * l) (hl : 4 ≤ l) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F - 1) {A : Subgroup ↥(orthDerived Q)} (hA : GLAIsBmax p A)
    {d : ↥(orthDerived Q)} (hdA : d ∈ A)
    (hK : IsComponentOf (GLALayer (Subgroup.centralizer ({d} : Set ↥(orthDerived Q))))
      (Subgroup.centralizer ({d} : Set ↥(orthDerived Q))))
    (hCA : A ⊓ Subgroup.centralizer
      (GLALayer (Subgroup.centralizer ({d} : Set ↥(orthDerived Q))) : Set ↥(orthDerived Q)) =
        Subgroup.zpowers d)
    {T : Subgroup ↥(orthDerived Q)} (hT2 : IsPGroup 2 T)
    (hT : closureIn (GLALayer (Subgroup.centralizer ({d} : Set ↥(orthDerived Q))))
      (Subgroup.normalizer (A : Set ↥(orthDerived Q))) ≤ Subgroup.normalizer (T : Set ↥(orthDerived Q))) :
    T = ⊥ := by
  classical
  obtain ⟨e, f, c, hef, hAeq, hcp, hd, hcases⟩ :=
    standard_classification hQ hdim hl hp hp2 hpq hA hdA hK hCA
  have hdp : d ^ p = 1 := hA.1.2 d hdA
  have hdp' : (d : V ≃ₗ[F] V) ^ p = 1 := by
    simpa using congrArg (fun x : ↥(orthDerived Q) => (x : V ≃ₗ[F] V)) hdp
  rcases hcases with ⟨-, hK1⟩ | ⟨j, hcj, hc1, hKj⟩ | ⟨u, hu, hcu, hKu⟩
  · exact eq_bot_of_top_le_normalizer hQ hdim hl hT2
      (hK1.symm.le.trans ((le_closureIn_self _ _).trans hT))
  · have htop := closureIn_eq_top_of_weightOne hQ hdim hl hp hp2 hpq hef hAeq (j := j)
      (K := GLALayer (Subgroup.centralizer ({d} : Set ↥(orthDerived Q))))
      (fun a b ha1 ha2 hb1 hb2 g hg => by
        rw [hKj, Subgroup.mem_subgroupOf, hg]
        exact eichler_mem_supportedFixedDerived_of_weightOne hQ hef hd hcj hc1 ha1 ha2 hb1 hb2)
    exact eq_bot_of_top_le_normalizer hQ hdim hl hT2 (htop.ge.trans hT)
  · have hKu' : ∀ a b : V, (d : V ≃ₗ[F] V) a = ((u : Fˣ) : F) • a →
        (d : V ≃ₗ[F] V) b = (((u⁻¹ : Fˣ)) : F) • b → ∀ g : ↥(orthDerived Q),
        (g : V ≃ₗ[F] V) = eichler Q a b →
          g ∈ GLALayer (Subgroup.centralizer ({d} : Set ↥(orthDerived Q))) := by
      intro a b ha hb g hg
      rw [hKu, Subgroup.mem_subgroupOf, hg]
      exact eichler_mem_specialBlock hQ hp hp2 hdp' hu ha hb
    by_cases hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q
    · have htop := closureIn_eq_top_of_plus hQ hdim hl hplus hp hp2 hpq hef hAeq hd hu hcu hKu'
      exact eq_bot_of_top_le_normalizer hQ hdim hl hT2 (htop.ge.trans hT)
    · by_contra hT0
      have hX := eichler_mem_closureIn_of_minus hQ hdim hl hplus hp hp2 hpq hef hAeq hd hu hcu hKu'
      obtain ⟨W, hW0, hWs, hWi⟩ :=
        exists_invariant_totallySingular_of_normalizes hQ hdim hl hT2 hT0 hT
      exact hW0 (eq_bot_of_invariant_totallySingular hQ hdim hl hef hX hWs hWi)

end Vanish

end CFSG.LocalAnalysis.GLTheoremA.T173S

end

