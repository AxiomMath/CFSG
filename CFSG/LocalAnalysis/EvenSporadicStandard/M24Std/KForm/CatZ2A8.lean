module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.CatZ2A8Alt
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.CatZ2A8Red
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpArmsHolds
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpEvenTypedHolds
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.ResidualA8Proof
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.McLLyInnerCenter
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpClause1
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.HSInvolutions
public import CFSG.GH74.KGroups.PSLN

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped MatrixGroups

@[expose] def CatZ2A8 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (S : Subgroup K), S.Normal → IsSimpleGroup ↥S →
    Catalog ↥S → centralizer (S : Set K) = ⊥ → ∀ z : K, orderOf z = 2 →
    Nonempty (↥(centralizer ({z} : Set K)) ≃* Multiplicative (ZMod 2) × alternatingGroup (Fin 8)) →
    Nonempty (↥S ≃* PSL(4, GaloisField 2 2))

namespace KForm

open CFSG.ComponentClassification.CatFC
open CFSG.ComponentClassification.CatLeaf (mulAut_conj_injective_of_simple)
open CFSG.EvenSporadicStandard.HSStd.Zassenhaus (card_centralizer_of_involution_hs)
open CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore

theorem isQuasisimple_of_simple_nonab {N : Type*} [Group N] (hs : IsSimpleGroup N)
    (hna : ∃ a b : N, a * b ≠ b * a) : CFSG.IsQuasisimple N := by
  have hc : center N = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center N) with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨a, b, hab⟩ := hna
      exact hab (mem_center_iff.1 (h1 ▸ mem_top b) a)
  have hperf : Group.IsPerfect N := by
    rw [Group.isPerfect_def, _root_.commutator_def]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ⁅(⊤ : Subgroup N), (⊤ : Subgroup N)⁆ with
        h1 | h1
    · exfalso
      obtain ⟨a, b, hab⟩ := hna
      have hcen := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h1
      exact hab (mem_centralizer_iff.1 (hcen (mem_top a)) b (mem_top b)).symm
    · exact h1
  let e : (N ⧸ center N) ≃* N :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  refine ⟨hperf, MulEquiv.isSimpleGroup e, ?_⟩
  obtain ⟨a, b, hab⟩ := hna
  refine ⟨QuotientGroup.mk a, QuotientGroup.mk b, fun h => hab ?_⟩
  have h1 := congrArg e h
  have he : ∀ x : N, e (QuotientGroup.mk x) = x := fun x => rfl
  rwa [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, he, he] at h1

theorem alt8_simple : IsSimpleGroup (alternatingGroup (Fin 8)) :=
  alternatingGroup.isSimpleGroup (by simp)

theorem alt8_nonab : ∃ a b : alternatingGroup (Fin 8), a * b ≠ b * a := by
  by_contra hcon
  have hcom : ∀ a b : alternatingGroup (Fin 8), a * b = b * a := by
    intro a b
    by_contra h
    exact hcon ⟨a, b, h⟩
  have hnc : ¬ IsMulCommutative (alternatingGroup (Fin 8)) := by
    rw [alternatingGroup.isMulCommutative_iff_card_le_three]
    simp
  exact hnc ⟨⟨hcom⟩⟩

section Generic

variable {A : Type} [Group A] [IsSimpleGroup A]

theorem center_eq_bot_of_simple_iso (hA : ∃ a b : A, a * b ≠ b * a) {X : Type} [Group X]
    (e : X ≃* A) : center X = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have h1 : e x = 1 := by
    apply eq_one_of_central_of_simple hA
    intro b
    obtain ⟨y, rfl⟩ := e.surjective b
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx y]
  exact e.injective (h1.trans e.map_one.symm)

theorem quotient_center_iso_of_simple_iso (hA : ∃ a b : A, a * b ≠ b * a) {X : Type} [Group X]
    (e : X ≃* A) : Nonempty (X ⧸ center X ≃* A) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq (center_eq_bot_of_simple_iso hA e)).trans
    ((QuotientGroup.quotientBot : X ⧸ (⊥ : Subgroup X) ≃* X).trans e)⟩

theorem isComponent_of_simple_iso (hA : ∃ a b : A, a * b ≠ b * a) {G : Type} [Group G]
    (D : Subgroup G) [D.Normal] (e : ↥D ≃* A) : CFSG.IsComponent D := by
  have hs : IsSimpleGroup ↥D := e.isSimpleGroup
  have hna : ∃ a b : ↥D, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hA
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  exact ⟨isQuasisimple_of_simple_nonab hs hna, Subgroup.Normal.isSubnormal inferInstance⟩

theorem exists_normal_of_prod {G : Type} [Group G]
    (ψ : G ≃* Multiplicative (ZMod 2) × A) :
    ∃ D : Subgroup G, D.Normal ∧ Nonempty (↥D ≃* A) := by
  let M : Subgroup (Multiplicative (ZMod 2) × A) :=
    (MonoidHom.inr (Multiplicative (ZMod 2)) A).range
  have hMn : M.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hn
    refine MonoidHom.mem_range.mpr ⟨g.2 * a * g.2⁻¹, ?_⟩
    ext <;> simp
  have hinj : Function.Injective (MonoidHom.inr (Multiplicative (ZMod 2)) A) :=
    fun a b h => congrArg Prod.snd h
  have hmap : (M.comap ψ.toMonoidHom).map ψ.toMonoidHom = M :=
    Subgroup.map_comap_eq_self_of_surjective (f := ψ.toMonoidHom) ψ.surjective M
  refine ⟨M.comap ψ.toMonoidHom, Subgroup.Normal.comap hMn ψ.toMonoidHom, ⟨?_⟩⟩
  exact (Subgroup.equivMapOfInjective (M.comap ψ.toMonoidHom) ψ.toMonoidHom ψ.injective).trans
    ((MulEquiv.subgroupCongr hmap).trans (MonoidHom.ofInjective hinj).symm)

end Generic

section HSOuter


theorem hs_outer_card_fixedSubgroup {S : Type} [Group S] (e : S ≃* NativeSporadic.HS)
    {σ : MulAut S} (hσ : orderOf σ = 2) (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) :
    Nat.card (fixedSubgroup σ) = 40320 ∨ Nat.card (fixedSubgroup σ) = 1920 := by
  obtain ⟨r, hr, hrout, ⟨φ⟩⟩ := hs_fixedSubgroup_rows_outer e hσ hout
  obtain ⟨-, -, -, hrows, -, -, hmap, -⟩ := hs_involution_centralizers
  have hcardC := (hrows r hr).2.2.2.2.1
  have hmem : (r.outer, r.classSize, r.centOrder) ∈
      [(false, 5775, 7680), (false, 15400, 2880), (true, 1100, 40320), (true, 23100, 1920)] := by
    rw [← hmap]
    exact List.mem_map_of_mem
      (f := fun r : ClassRow => (r.outer, r.classSize, r.centOrder)) hr
  have hc : r.centOrder = 40320 ∨ r.centOrder = 1920 := by
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
    rcases hmem with ⟨h1, -, -⟩ | ⟨h1, -, -⟩ | ⟨-, -, h3⟩ | ⟨-, -, h3⟩
    · exact absurd (h1.symm.trans hrout) (by decide)
    · exact absurd (h1.symm.trans hrout) (by decide)
    · exact Or.inl h3
    · exact Or.inr h3
  rw [Nat.card_congr φ.toEquiv, hcardC]
  exact hc

end HSOuter

end KForm

section Assembly


namespace KForm

open CFSG.ComponentClassification.CatFC
open CFSG.ComponentClassification.CatLeaf (mulAut_conj_injective_of_simple)
open CFSG.EvenSporadicStandard.HSStd.Zassenhaus (card_centralizer_of_involution_hs)

theorem alt8_outcome {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) (hcat : Catalog S) {σ : MulAut S} (hσ : orderOf σ = 2)
    {D : Subgroup ↥(fixedSubgroup σ)} [D.Normal] (e : ↥D ≃* alternatingGroup (Fin 8)) :
    (∃ m : ℕ, 5 ≤ m ∧ Nonempty (S ≃* alternatingGroup (Fin (2 * m)))) ∨ IsSporadic S .HS ∨
      LieModel S .PSL 4 2 2 := by
  haveI := alt8_simple
  have hD : CFSG.IsComponent D := isComponent_of_simple_iso alt8_nonab D e
  obtain ⟨eQ⟩ := quotient_center_iso_of_simple_iso alt8_nonab e
  rcases clause1_of_inputs armInputs_holds evenOuterTypedInput_holds heSuzONNoAltEight_proved
      mcl_inner_component_center hna hcat hσ hD ⟨eQ⟩ with h | h | h | ⟨-, hc⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exfalso
    rw [center_eq_bot_of_simple_iso alt8_nonab e, Subgroup.card_bot] at hc
    omega

theorem inner_alt8 {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) (hcat : Catalog S) (z : S) (hz : orderOf z = 2)
    (e : ↥(centralizer ({z} : Set S)) ≃* Multiplicative (ZMod 2) × alternatingGroup (Fin 8)) :
    LieModel S .PSL 4 2 2 := by
  haveI := alt8_simple
  have hI : Function.Injective (MulAut.conj : S →* MulAut S) :=
    mulAut_conj_injective_of_simple hna
  have hσ : orderOf (MulAut.conj z : MulAut S) = 2 :=
    (orderOf_injective (MulAut.conj : S →* MulAut S) hI z).trans hz
  have hfix : fixedSubgroup (MulAut.conj z : MulAut S) = centralizer ({z} : Set S) := by
    ext x
    rw [mem_centralizer_singleton_iff]
    change z * x * z⁻¹ = x ↔ x * z = z * x
    rw [mul_inv_eq_iff_eq_mul]
    exact eq_comm
  obtain ⟨D, hDn, ⟨eD⟩⟩ := exists_normal_of_prod ((MulEquiv.subgroupCongr hfix).trans e)
  haveI := hDn
  rcases alt8_outcome hna hcat hσ eD with ⟨m, hm5, ⟨θ⟩⟩ | hHS | hL
  · exact absurd ⟨e⟩ (alt_not_centralizer_Z2_alt8 (by omega) θ z hz)
  · exfalso
    have hC : Nat.card (centralizer ({z} : Set S)) = 2 * 20160 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_prod, card_alternatingGroup_fin_eight,
        natCard_multiplicative_zmod_two]
    rcases card_centralizer_of_involution_hs hHS z hz with h | h <;> omega
  · exact hL

theorem outer_alt8 {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) (hcat : Catalog S) {σ : MulAut S} (hσ : orderOf σ = 2)
    (hout : σ ∉ (MulAut.conj : S →* MulAut S).range)
    (e : ↥(fixedSubgroup σ) ≃* alternatingGroup (Fin 8)) : LieModel S .PSL 4 2 2 := by
  have eD : ↥(⊤ : Subgroup ↥(fixedSubgroup σ)) ≃* alternatingGroup (Fin 8) :=
    Subgroup.topEquiv.trans e
  rcases alt8_outcome hna hcat hσ eD with ⟨m, hm5, ⟨θ⟩⟩ | hHS | hL
  · exact absurd ⟨e⟩ (alt_not_fixedSubgroup_alt8 (by omega) (by omega) θ hσ)
  · exfalso
    obtain ⟨eHS⟩ := hHS
    have h := hs_outer_card_fixedSubgroup eHS hσ hout
    rw [Nat.card_congr e.toEquiv, card_alternatingGroup_fin_eight] at h
    omega
  · exact hL

end KForm

theorem catZ2A8_holds : CatZ2A8 := by
  intro K _ _ S hSn hSs hcat hcent z hz hne
  obtain ⟨φ⟩ := hne
  haveI := KForm.alt8_simple
  have hSna : ∃ a b : ↥S, a * b ≠ b * a := KForm.nonabelian_of_centralizer_eq_bot S hcent
  have hL : LieModel ↥S .PSL 4 2 2 := by
    rcases KForm.z2_reduction KForm.alt8_nonab S hcent hz φ with
      ⟨w, hw, ⟨e⟩⟩ | ⟨σ, hσ, hout, ⟨e⟩⟩
    · exact KForm.inner_alt8 hSna hcat w hw e
    · exact KForm.outer_alt8 hSna hcat hσ hout e
  exact CFSG.GH74.KGroups.PSLN.psl_equiv_of_lieModel (F := GaloisField 2 2) 4 2 2
    (by norm_num) (GaloisField.card 2 2 (by norm_num)) hL

end Assembly

end CFSG.EvenSporadicStandard.M24Std
