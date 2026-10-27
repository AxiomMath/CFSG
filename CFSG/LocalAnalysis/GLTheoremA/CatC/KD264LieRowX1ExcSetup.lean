module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.AlgSetupUntw
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFivePairRigid
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Exc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE

section Algebra

theorem le_of_isPGroup_of_not_dvd_index {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    [H.Normal] {p : ℕ} [Fact p.Prime] (hidx : ¬ p ∣ H.index) {P : Subgroup G} (hP : IsPGroup p P) :
    P ≤ H := by
  have h1 : H.relIndex P ∣ H.index := Subgroup.relIndex_dvd_index_of_normal H P
  have h2 : H.relIndex P ∣ Nat.card P := by
    unfold Subgroup.relIndex
    exact Subgroup.index_dvd_card _
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  rw [hk] at h2
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).1 h2
  have hj0 : j = 0 := by
    by_contra hne
    apply hidx
    rw [hj] at h1
    exact (dvd_pow_self p hne).trans h1
  rw [hj0, pow_zero] at hj
  exact Subgroup.relIndex_eq_one.1 hj

theorem le_of_isPGroup_of_relIndex {G : Type*} [Group G] {H X P : Subgroup G} [Finite X]
    (hHX : H ≤ X) (hn : (H.subgroupOf X).Normal) {p : ℕ} [Fact p.Prime]
    (hidx : ¬ p ∣ H.relIndex X) (hPX : P ≤ X) (hP : IsPGroup p P) : P ≤ H := by
  have hP' : IsPGroup p (P.subgroupOf X) := by
    have := hP.comap_subtype (K := X)
    exact this
  have := le_of_isPGroup_of_not_dvd_index (H := H.subgroupOf X) hidx hP'
  intro x hx
  have hxX : x ∈ X := hPX hx
  have := this (show (⟨x, hxX⟩ : X) ∈ P.subgroupOf X from hx)
  exact this

end Algebra

section Setup


theorem exists_exc_setup {τ : Tag} (d : ℕ) (hτ : (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1))
    (w : WeylGroup τ) (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2)
    (hperf : Group.IsPerfect ↥(adjointGroup τ K)) :
    ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (_ : Algebra K L) (_ : IsAlgClosure K L)
      (S : LangSetup τ L 5) (Fr : L →+* L),
      (∀ c, Fr c = c ^ 2) ∧ S.D.q = 2 ∧ S.D.Φ = Units.map (entrywiseHom Fr) ∧
      S.D.n = canonicalRep (coxeterSystem τ) L w ∧ S.IsAlgebraic ∧
      (∀ γ, IsRoot τ γ → S.ρ γ = w • γ) ∧ Nonempty (adjointGroup τ K ≃* S.Γ) ∧
      (∀ P : Subgroup (ModGL τ L), P ≤ S.D.model → IsPGroup 3 P → P ≤ S.Γ) := by
  classical
  have hτ' : (τ = .E6 ∧ d = 3) ∨ (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1) :=
    hτ.elim (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr h))
  have hperf' : commutator ↥(adjointGroup τ K) = ⊤ := hperf.commutator_eq_top
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Finite (ModGL τ K) := finite_modGL
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hq : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  haveI : CharP K (ringChar K) := ringChar.charP K
  let L := AlgebraicClosure K
  haveI : CharP L (ringChar K) := charP_of_injective_algebraMap (algebraMap K L).injective _
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  let Fr : L →+* L := iterateFrobenius L (ringChar K) (f : ℕ)
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hq]
    exact iterateFrobenius_def (ringChar K) (f : ℕ) c
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator τ K (ℓ := ringChar K) (f := (f : ℕ)) f.pos L w
  have hp5 : Nat.Prime 5 := by norm_num
  have hpq : ¬ 5 ∣ Nat.card K := by rw [hK]; norm_num
  obtain ⟨S, hSD, hd⟩ := exists_langSetup_untw_of_datum frobeniusOnRoots_proved d hτ' (K := K)
    (L := L) hp5 (by norm_num) hpq hperf hFr w hg0C hg0
  set D : LangDatum τ L := LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0 with hDdef
  have hD : D.Φ = Units.map (entrywiseHom Fr) := rfl
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, S, Fr,
    fun c => by rw [hFr c, hK], ?_, ?_, ?_, S.isAlgebraic_of_isAlgClosure K 1 ?_, ?_, ?_, ?_⟩
  · rw [hSD]; exact hK
  · rw [hSD]; exact hD
  · rw [hSD]; rfl
  · rw [pow_one, hSD]; rfl
  · intro γ hγ
    have hFD : FrobRootMap (LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0) S.ρ := by
      have := S.frob
      rw [hSD] at this
      exact this
    exact frobRootMap_ofFrobenius_apply Nat.card_pos hFr hg0C hg0 hFD hγ
  · exact ⟨hd.descentEquiv ((baseChangeGL_injective _).comp (Subgroup.subtype_injective _))⟩
  ·
    intro P hP hP3
    have hd' : LangDescent D 5 ((baseChangeGL (algebraMap K L)).comp
        (adjointGroup τ K).subtype) := hSD ▸ hd
    have hP : P ≤ D.model := by rw [← hSD]; exact hP
    haveI : Finite D.fix := hd'.finite_fix
    set ι : adjointGroup τ K →* ModGL τ L :=
      (baseChangeGL (algebraMap K L)).comp (adjointGroup τ K).subtype with hι
    have hrange : ι.range = (adjointGroup τ K).map (baseChangeGL (algebraMap K L)) := by
      rw [hι, MonoidHom.range_comp, Subgroup.range_subtype]
    have hrel := (finite_fixed_subgroup_rational d hτ' Fr hFr D.fix
      (fun x hx => ((LangDatum.mem_fix D).1 hx).1)
      (fun x hx => by have := ((LangDatum.mem_fix D).1 hx).2; rwa [hD] at this)).1
    have hdd : d ≤ 2 := by rcases hτ with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
    have hn3 : ¬ 3 ∣ ι.range.relIndex D.fix := by
      intro h3
      have := (h3.trans (hrange ▸ hrel))
      have := Nat.le_of_dvd (by omega) this
      omega
    have hnorm : (ι.range.subgroupOf D.fix).Normal := by
      have hder : ⁅D.fix, D.fix⁆ = ι.range := hd'.derived
      rw [← hder]
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer (commutator_le_self_of_subgroup D.fix)]
      exact Subgroup.normalizer_commutator_ge_left (H₁ := D.fix) (H₂ := D.fix)
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hPfix : P.map (MulAut.conj D.g0).toMonoidHom ≤ D.fix := by
      rw [← LangDatum.map_conj_model]
      exact Subgroup.map_mono hP
    have h1 := le_of_isPGroup_of_relIndex hd'.range_le hnorm hn3 hPfix (hP3.map _)
    have hΓ := hd'.Γ_eq
    show P ≤ S.D.Γ
    rw [hSD]
    rw [hΓ]
    intro x hx
    have hxr : (MulAut.conj D.g0 : MulAut (ModGL τ L)) x ∈ ι.range :=
      h1 (Subgroup.mem_map_of_mem _ hx)
    refine Subgroup.mem_map.2 ⟨_, hxr, ?_⟩
    show D.g0⁻¹ * (D.g0 * x * D.g0⁻¹) * D.g0⁻¹⁻¹ = x
    group

end Setup

section Torus

variable {τ : Tag} {L : Type} [Field L]

theorem rootChar_neg_eq_inv' (a : Fin τ.rank → Lˣ) (v : Fin τ.rank → ℤ) :
    rootChar a (-v) = (rootChar a v)⁻¹ := by
  have := rootChar_sub a 0 v
  rwa [zero_sub, rootChar_zero, one_mul] at this

theorem rootChar_pow_two' (a : Fin τ.rank → Lˣ) (v : Fin τ.rank → ℤ) :
    rootChar (fun i => a i ^ 2) v = rootChar a v ^ 2 := by
  unfold rootChar
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]

theorem rootChar_pow_three_eq_one' {a : Fin τ.rank → Lˣ} (ha : ∀ i, a i ^ 3 = 1)
    (v : Fin τ.rank → ℤ) : rootChar a v ^ 3 = 1 := by
  unfold rootChar
  rw [← Finset.prod_pow]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha i, one_zpow]

variable [IsAlgClosed L]

theorem rootDiagUnit_mem_langTorus {p : ℕ} (S : LangSetup τ L p) (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ 2) (w : WeylGroup τ) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
    (hn : S.D.n = canonicalRep (coxeterSystem τ) L w)
    (hw : ∀ x : Fin τ.rank → ℤ, w • x = -x)
    {a : Fin τ.rank → Lˣ} (ha : ∀ i, a i ^ 3 = 1) : rootDiagUnit τ a ∈ S.D.torus := by
  refine mem_twistedTorusOf.2 ⟨rootDiagUnit_mem_torusGroup a, ?_⟩
  rw [hn, hΦ, units_map_entrywiseHom_rootDiagUnit Fr a]
  have hsq : (fun i => Units.map Fr.toMonoidHom (a i)) = fun i => a i ^ 2 := by
    funext i
    exact Units.ext (by simp [hFr])
  rw [hsq]
  refine ((rootDiagUnit_eq_conj_canonicalRep_iff a (fun i => a i ^ 2) w).2 fun v => ?_).symm
  rw [hw, rootChar_neg_eq_inv', rootChar_pow_two']
  have h3 := rootChar_pow_three_eq_one' ha v
  rw [pow_succ, pow_two] at h3
  rw [inv_eq_iff_eq_inv]
  exact (eq_inv_of_mul_eq_one_right (by simpa [pow_succ, mul_assoc] using h3))

end Torus


end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Exc

end
