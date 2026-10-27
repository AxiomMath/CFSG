module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420Facts2
public import CFSG.LocalAnalysis.GLTheoremA.CatC.ChevQ

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420.ClsRed

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup LieOrderBridge)
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut)
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom centerQuotientHom_injective)

@[expose] def I1432SporD4S : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (s : TauCeti.SporadicName),
    Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    ∀ β : MulAut S, β ^ 3 = 1 → β ≠ 1 → ∀ J : Subgroup S, GLAPComponent 3 (fixSubgroup β) J →
      catalogIs (PSimple 3 J) (S8.isD4of 3) → s = .Fi24Prime

@[expose] def I1432SporG2S : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (s : TauCeti.SporadicName),
    Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    ∀ β : MulAut S, β ^ 3 = 1 → β ≠ 1 → ∀ J : Subgroup S, GLAPComponent 3 (fixSubgroup β) J →
      catalogIs (PSimple 3 J) (S8.isG2of 3) → s = .Th ∨ s = .Fi24Prime

@[expose] def I1432ClsD4Lie : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (K I : Subgroup Q) (y : Q), I1432Model K I y →
    S8.IsTypeWithCenter 3 I (S8.isD4of 3) 1 →
    ∀ d : TauCeti.ValidLieTypeIndex, Nonempty (PSimple 3 K ≃* (TauCeti.CFSGIndex.lie d).Group) →
      catalogIs (PSimple 3 K) (S8.sporIs .Fi24Prime) ∨ catalogIs (PSimple 3 K) (S8.isD4of 27)

@[expose] def I1432ClsG2Lie : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (K I : Subgroup Q) (y : Q), I1432Model K I y →
    S8.IsTypeWithCenter 3 I (S8.isG2of 3) 1 →
    ∀ d : TauCeti.ValidLieTypeIndex, Nonempty (PSimple 3 K ≃* (TauCeti.CFSGIndex.lie d).Group) →
      catalogIs (PSimple 3 K) (S8.sporIs .Th) ∨ catalogIs (PSimple 3 K) (S8.sporIs .Fi24Prime) ∨
        catalogIs (PSimple 3 K) (S8.isG2of 27) ∨ catalogIs (PSimple 3 K) (S8.isD4of 3) ∨
        catalogIs (PSimple 3 K) (isTD4of 3) ∨ catalogIs (PSimple 3 K) (S8.isD4of 27)

variable {Q : Type} [Group Q] [Finite Q]

theorem isPGroup_zpowers_three {y : Q} (hy : y ^ 3 = 1) : IsPGroup 3 (Subgroup.zpowers y) := by
  intro g
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 g.2
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, Subgroup.coe_pow, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
    hy, one_zpow, Subgroup.coe_one]

theorem le_sup_of_centMod {K I : Subgroup Q} {y : Q} (hq : CFSG.Open.IsQuasisimple (PQuot 3 K))
    (hy : IsPGroup 3 (Subgroup.zpowers y)) (hCM : CentMod 3 K y)
    (hI : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set Q)) I) :
    K ≤ I ⊔ GLAPPrimeCoreOf 3 K := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  set C : Subgroup Q := K ⊓ Subgroup.centralizer ({y} : Set Q) with hCdef
  have hCK : C ⊔ GLAPPrimeCoreOf 3 K = K := inf_centralizer_sup_eq_of_centMod hp hy hCM
  obtain ⟨hcov, ⟨eC⟩⟩ := cover_facts hp (inf_le_left : C ≤ K) hCK
  have hqC : CFSG.Open.IsQuasisimple (PQuot 3 C) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv eC.symm hq
  obtain ⟨-, hlay, hbar⟩ := glaPLayer_of_isQuasisimple hqC
  have hIeq : I = GLAPLayer 3 C := hlay I hI
  have hbarI : barX 3 C I = ⊤ := hIeq ▸ hbar
  have hIcov : I ⊔ GLAPPrimeCoreOf 3 C = C := sup_glaPPrimeCoreOf_eq_of_barX_eq_top hI.1 hbarI
  have hOC : GLAPPrimeCoreOf 3 C ≤ GLAPPrimeCoreOf 3 K := by
    rw [hcov]
    exact inf_le_right
  calc K = C ⊔ GLAPPrimeCoreOf 3 K := hCK.symm
    _ ≤ I ⊔ GLAPPrimeCoreOf 3 K := by
      apply sup_le _ le_sup_right
      calc C = I ⊔ GLAPPrimeCoreOf 3 C := hIcov.symm
        _ ≤ I ⊔ GLAPPrimeCoreOf 3 K := sup_le_sup_left hOC I

theorem chevAut_eq_one_iff' {K : Subgroup Q} (hq : CFSG.Open.IsQuasisimple (PQuot 3 K)) {a : Q}
    (ha : a ∈ Subgroup.normalizer (K : Set Q)) :
    chevAut 3 K ⟨a, ha⟩ = 1 ↔ CentMod 3 K a := by
  haveI : Group.IsPerfect (PQuot 3 K) := ⟨hq.1⟩
  rw [← chev_barAut_eq_one_iff_centMod ha]
  show centerQuotientHom (PQuot 3 K) (barAut 3 K ⟨a, ha⟩) = 1 ↔ _
  rw [← map_one (centerQuotientHom (PQuot 3 K))]
  exact (centerQuotientHom_injective (PQuot 3 K)).eq_iff

theorem model_chevAut_ne_one {K I : Subgroup Q} {y : Q} (hM : I1432Model K I y) :
    chevAut 3 K ⟨y, hM.2.2.1⟩ ≠ 1 := by
  obtain ⟨hq, -, hyN, hy3, hI, hnot⟩ := hM
  intro h
  exact hnot (le_sup_of_centMod hq (isPGroup_zpowers_three hy3)
    ((chevAut_eq_one_iff' hq hyN).1 h) hI)

theorem model_alt {K I : Subgroup Q} {y : Q} (hM : I1432Model K I y) {n : ℕ} (hn : 5 ≤ n)
    (e : PSimple 3 K ≃* alternatingGroup (Fin n)) :
    ∃ m : ℕ, 5 ≤ m ∧ Nonempty (PSimple 3 I ≃* alternatingGroup (Fin m)) := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  obtain ⟨-, -, hyN, hy3, hI, -⟩ := id hM
  have hα1 : chevAut 3 K ⟨y, hyN⟩ ≠ 1 := model_chevAut_ne_one hM
  have hyp := isPGroup_zpowers_three hy3
  have hI' := glaPComponent_chevTransfer hp hyN hyp hI
  have hα : chevAut 3 K ⟨y, hyN⟩ ^ 3 = 1 := chevAut_pow_eq_one 3 K hyN hy3
  obtain ⟨hβI, ⟨e₁⟩⟩ := chevQ_transport hp e hI'
  have hβ : MulAut.congr e (chevAut 3 K ⟨y, hyN⟩) ^ 3 = 1 := by
    rw [← map_pow, hα, map_one]
  have hβ1 : MulAut.congr e (chevAut 3 K ⟨y, hyN⟩) ≠ 1 := fun h =>
    hα1 ((MulAut.congr e).injective (h.trans (map_one _).symm))
  obtain ⟨m, hm, -, ⟨f⟩⟩ := kdAltDown_holds n 3 hn hp (by norm_num) _ hβ hβ1 _ hβI
  obtain ⟨g₁⟩ := nonempty_pSimple_equiv_chevTransfer hp hyN hyp hI
  exact ⟨m, (le_max_left 5 3).trans hm, ⟨g₁.trans (e₁.trans f)⟩⟩

theorem model_spor {K I : Subgroup Q} {y : Q} (hM : I1432Model K I y) {s : TauCeti.SporadicName}
    (e : PSimple 3 K ≃* (TauCeti.CFSGIndex.sporadic s).Group) {P : TauCeti.CFSGIndex → Prop}
    (hT : catalogIs (PSimple 3 I) P) :
    ∃ β : MulAut (PSimple 3 K), β ^ 3 = 1 ∧ β ≠ 1 ∧ ∃ J : Subgroup (PSimple 3 K),
      GLAPComponent 3 (fixSubgroup β) J ∧ catalogIs (PSimple 3 J) P := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  obtain ⟨-, -, hyN, hy3, hI, -⟩ := id hM
  have hα1 : chevAut 3 K ⟨y, hyN⟩ ≠ 1 := model_chevAut_ne_one hM
  have hyp := isPGroup_zpowers_three hy3
  obtain ⟨g⟩ := nonempty_pSimple_equiv_chevTransfer hp hyN hyp hI
  obtain ⟨i, hi, ⟨f⟩⟩ := hT
  exact ⟨chevAut 3 K ⟨y, hyN⟩, chevAut_pow_eq_one 3 K hyN hy3, hα1, chevTransfer 3 K I,
    glaPComponent_chevTransfer hp hyN hyp hI, ⟨i, hi, ⟨g.symm.trans f⟩⟩⟩

theorem card_alt_ne {m N : ℕ} (k : ℕ) (hm : 5 ≤ m) (h1 : k.factorial < 2 * N)
    (h2 : 2 * N < (k + 1).factorial) : Nat.card (alternatingGroup (Fin m)) ≠ N := by
  haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 (by omega)
  rw [nat_card_alternatingGroup, Nat.card_fin]
  intro h
  have h2m : 2 ∣ m.factorial := Nat.dvd_factorial (by norm_num) (by omega)
  have hmN : m.factorial = 2 * N := by rw [← h]; exact (Nat.mul_div_cancel' h2m).symm
  rcases le_or_gt m k with hk | hk
  · have := Nat.factorial_le hk
    omega
  · have := Nat.factorial_le (show k + 1 ≤ m by omega)
    omega

theorem card_d4three (hB : LieOrderBridge) {T : Type} [Group T] [Finite T] (h : catalogIs T (S8.isD4of 3)) :
    Nat.card T = 4952179814400 := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  cases i with
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d with
    | D n q =>
      rcases n with _ | _ | _ | _ | _ | n
      · exact False.elim hi
      · exact False.elim hi
      · exact False.elim hi
      · exact False.elim hi
      · have hq : q.card = 3 := hi
        rw [hB ⟨_, hv⟩ T ⟨f⟩]
        show orderD 4 q.card = 4952179814400
        rw [hq]
        decide
      · exact False.elim hi
    | _ => exact False.elim hi
  | _ => exact False.elim hi

theorem card_g2three (hB : LieOrderBridge) {T : Type} [Group T] [Finite T] (h : catalogIs T (S8.isG2of 3)) :
    Nat.card T = 4245696 := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  cases i with
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d with
    | G2 q =>
      have hq : q.card = 3 := hi
      rw [hB ⟨_, hv⟩ T ⟨f⟩]
      show orderG2 q.card = 4245696
      rw [hq]
      decide
    | _ => exact False.elim hi
  | _ => exact False.elim hi

theorem model_not_cyclic {K I : Subgroup Q} {y : Q} (hM : I1432Model K I y) {r : ℕ} {hr : r.Prime}
    (e : PSimple 3 K ≃* (TauCeti.CFSGIndex.cyclic r hr).Group) : False := by
  obtain ⟨a', b', hab⟩ :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hM.1
  apply hab
  apply e.injective
  simp only [map_mul]
  exact mul_comm _ _

theorem i1432ClsD4_of_parts (hB : LieOrderBridge) (hSpor : I1432SporD4S) (hLie : I1432ClsD4Lie) :
    I1432ClsD4 := by
  intro Q _ _ K I y hM hI
  obtain ⟨i, ⟨e⟩⟩ := hM.2.1
  cases i with
  | cyclic r hr => exact (model_not_cyclic hM e).elim
  | alternating n hn =>
    exfalso
    obtain ⟨m, hm, ⟨f⟩⟩ := model_alt hM hn e
    have h1 := card_d4three hB hI.1
    rw [Nat.card_congr f.toEquiv] at h1
    exact card_alt_ne 15 hm (by decide) (by decide) h1
  | sporadic s =>
    obtain ⟨β, hβ, hβ1, J, hJ, hT⟩ := model_spor hM e hI.1
    have hs := hSpor _ s ⟨e⟩ β hβ hβ1 J hJ hT
    subst hs
    exact Or.inl ⟨_, rfl, ⟨e⟩⟩
  | lie d => exact hLie Q K I y hM hI d ⟨e⟩

theorem i1432ClsG2_of_parts (hB : LieOrderBridge) (hSpor : I1432SporG2S) (hLie : I1432ClsG2Lie) :
    I1432ClsG2 := by
  intro Q _ _ K I y hM hI
  obtain ⟨i, ⟨e⟩⟩ := hM.2.1
  cases i with
  | cyclic r hr => exact (model_not_cyclic hM e).elim
  | alternating n hn =>
    exfalso
    obtain ⟨m, hm, ⟨f⟩⟩ := model_alt hM hn e
    have h1 := card_g2three hB hI.1
    rw [Nat.card_congr f.toEquiv] at h1
    exact card_alt_ne 10 hm (by decide) (by decide) h1
  | sporadic s =>
    obtain ⟨β, hβ, hβ1, J, hJ, hT⟩ := model_spor hM e hI.1
    rcases hSpor _ s ⟨e⟩ β hβ hβ1 J hJ hT with rfl | rfl
    · exact Or.inl ⟨_, rfl, ⟨e⟩⟩
    · exact Or.inr (Or.inl ⟨_, rfl, ⟨e⟩⟩)
  | lie d => exact hLie Q K I y hM hI d ⟨e⟩

end CFSG.LocalAnalysis.GLTheoremA.H1420.ClsRed

end
