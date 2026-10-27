module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommUniTransferAut
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommUniTransferLevi
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommLinTransferCrt
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommLinTransferS3
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommLinTransferNormFix
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommUniModel
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockLinData
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniBlocks
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommGeneric
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommUniModelCut

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Uni

open CFSG.Open CFSG.AGLEmbedding CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.AGLEmbedding.LeviBlock
open scoped commutatorElement

section Scalars

variable {p f r ε : ℕ} {K : Type} [Field K]

theorem pow_card_units_eq_one_of_mem_hypScalars [Finite K] {h : UnitaryFieldData p f K}
    {z : hypSU h r ε}
    (hz : z ∈ hypScalars h r ε) : z ^ Nat.card Kˣ = 1 := by
  obtain ⟨c, -, -, hc⟩ := hz
  apply Subtype.ext
  change ((z ^ Nat.card Kˣ : hypSU h r ε) : GL (HypIndex r ε) K) = 1
  rw [Subgroup.coe_pow, hc, ← map_pow, pow_card_eq_one', map_one]

theorem gl_mul_comm_of_subsingleton {ι : Type} [Fintype ι] [DecidableEq ι] [Subsingleton ι]
    (a b : GL ι K) : a * b = b * a := by
  ext i j
  simp only [Units.val_mul, Matrix.mul_apply, Fintype.sum_subsingleton _ i]
  rw [Subsingleton.elim j i]
  exact mul_comm _ _

end Scalars

section Cover

variable {A : Type} [Group A] [Finite A] {Y P : Subgroup A} {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {t s ε : ℕ} {I : Finset ℕ} (C : UniCover Y P h (t + s) ε ↑I)

@[expose] noncomputable def UniCover.toP : ↥(flagStabilizer h (t + s) ε ↑I) →* ↥P :=
  (((Y.subtype).comp C.σ).comp (flagStabilizer h (t + s) ε ↑I).subtype).codRestrict P
    fun q => (C.mem_flag_iff q.1).mp q.2

@[simp] theorem UniCover.coe_toP (x : ↥(flagStabilizer h (t + s) ε ↑I)) :
    ((C.toP x : ↥P) : A) = ((C.σ x : ↥Y) : A) := rfl

theorem UniCover.toP_surjective (hPY : P ≤ Y) : Function.Surjective C.toP := by
  rintro ⟨w, hw⟩
  obtain ⟨g, hg⟩ := C.surjective ⟨w, hPY hw⟩
  have hgQ : g ∈ flagStabilizer h (t + s) ε ↑I := by
    rw [C.mem_flag_iff, hg]
    exact hw
  exact ⟨⟨g, hgQ⟩, Subtype.ext (by rw [C.coe_toP, hg])⟩

@[expose] noncomputable def UniCover.toHat :
    ↥(flagStabilizer h (t + s) ε ↑I) →* ↥P ⧸ CFSG.pCore 2 ↥P :=
  (QuotientGroup.mk' (CFSG.pCore 2 ↥P)).comp C.toP

theorem UniCover.toHat_surjective (hPY : P ≤ Y) : Function.Surjective C.toHat :=
  (QuotientGroup.mk'_surjective _).comp (C.toP_surjective hPY)

theorem UniCover.toP_mem_pCore_of_mem_ker (hε : ε ≤ 1) (hI : IsTopCut I t) (hPY : P ≤ Y)
    {u : ↥(flagStabilizer h (t + s) ε ↑I)} (hu : u ∈ (uniLeviHom (s := s) h hε hI).ker) :
    C.toP u ∈ CFSG.pCore 2 ↥P := by
  have hs := C.toP_surjective hPY
  have hmap : ((uniLeviHom (s := s) h hε hI).ker.map C.toP) ≤ CFSG.pCore 2 ↥P := by
    have hnorm : ((uniLeviHom (s := s) h hε hI).ker.map C.toP).Normal :=
      (MonoidHom.normal_ker _).map _ hs
    have hp : IsPGroup 2 ((uniLeviHom (s := s) h hε hI).ker.map C.toP) :=
      (isPGroup_ker_uniLeviHom h hε hI).map _
    exact le_sSup ⟨hnorm, hp⟩
  exact hmap (Subgroup.mem_map_of_mem _ hu)

include C in
theorem UniCover.exists_big_block (hε : ε ≤ 1) (hI : IsTopCut I t) (hPY : P ≤ Y)
    (hna : ∃ x ∈ P, ∃ y ∈ P, x * y * x⁻¹ * y⁻¹ ∉ pCoreOf 2 P) : ∃ j, IsBigBlock s ε I j := by
  by_contra hno
  push Not at hno
  obtain ⟨x, hx, y, hy, hxy⟩ := hna
  apply hxy
  obtain ⟨x', hx'⟩ := C.toP_surjective hPY ⟨x, hx⟩
  obtain ⟨y', hy'⟩ := C.toP_surjective hPY ⟨y, hy⟩
  have hU : ⁅x', y'⁆ ∈ (uniLeviHom (s := s) h hε hI).ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    funext j
    rcases j with _ | b
    · have hj := hno none
      simp only [IsBigBlock, not_le] at hj
      haveI := subsingleton_hypIndex (s := s) (ε := ε) (by omega)
      exact gl_mul_comm_of_subsingleton _ _
    · have hj := hno (some b)
      simp only [IsBigBlock, not_le] at hj
      exact Lin.commute_of_lt_two hj _ _
  have h3 := C.toP_mem_pCore_of_mem_ker hε hI hPY hU
  rw [map_commutatorElement, hx', hy'] at h3
  exact ⟨_, h3, rfl⟩

theorem UniCover.mem_hypScalars_of_toP_eq_one {z : ↥(flagStabilizer h (t + s) ε ↑I)}
    (hz : C.toP z = 1) : (z : hypSU h (t + s) ε) ∈ hypScalars h (t + s) ε := by
  apply C.ker_le
  rw [MonoidHom.mem_ker]
  have h1 : ((C.σ (z : hypSU h (t + s) ε) : ↥Y) : A) = 1 := congrArg (fun w : ↥P => (w : A)) hz
  exact Subtype.ext h1

theorem UniCover.exists_mul_of_toP_mem_pCore (hε : ε ≤ 1) (hI : IsTopCut I t)
    (q : ↥(flagStabilizer h (t + s) ε ↑I)) (hq : C.toP q ∈ CFSG.pCore 2 ↥P) :
    ∃ s' ∈ (uniLeviHom (s := s) h hε hI).ker, ∃ z : ↥(flagStabilizer h (t + s) ε ↑I),
      C.toP z = 1 ∧ q = s' * z := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite K := h.finite
  haveI : CharP K 2 := h.charP
  have hker : C.toP.ker ≤ Subgroup.center ↥(flagStabilizer h (t + s) ε ↑I) := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro g
    have hc := Subgroup.mem_center_iff.mp
      (normOneScalars_le_center h _ _ (C.mem_hypScalars_of_toP_eq_one hz)) (g : hypSU h (t + s) ε)
    exact Subtype.ext hc
  obtain ⟨s', hs', z, hz, hsz⟩ := Lin.exists_mul_of_comap_isPGroup C.toP hker
    (Lin.odd_card_units K)
    (fun z hz => Subtype.ext (by
      have := pow_card_units_eq_one_of_mem_hypScalars (C.mem_hypScalars_of_toP_eq_one hz)
      simpa using this))
    (CFSG.pCore_isPGroup (p := 2) (G := ↥P)) hq
  exact ⟨s', le_ker_uniLeviHom_of_normal_isPGroup h hε hI (CFSG.pCore 2 _)
    (CFSG.pCore_isPGroup (p := 2) (G := ↥(flagStabilizer h (t + s) ε ↑I))) hs', z,
    MonoidHom.mem_ker.mp hz, hsz⟩

theorem UniCover.proj_mem_projUni (hε : ε ≤ 1) (hI : IsTopCut I t)
    (q : ↥(flagStabilizer h (t + s) ε ↑I)) (hq : C.toP q ∈ CFSG.pCore 2 ↥P) :
    hypProj h (t + s) ε (q : hypSU h (t + s) ε) ∈ projUni h hε hI := by
  obtain ⟨s', hs', z, hz, hsz⟩ := C.exists_mul_of_toP_mem_pCore hε hI q hq
  have hzs := C.mem_hypScalars_of_toP_eq_one hz
  rw [← ker_hypProj] at hzs
  rw [hsz, Subgroup.coe_mul, map_mul, MonoidHom.mem_ker.mp hzs, mul_one]
  exact ⟨(s' : hypSU h (t + s) ε), ⟨s', hs', rfl⟩, rfl⟩

end Cover

section Types

variable {f : ℕ} {K : Type} [Field K] {s ε : ℕ} {I : Finset ℕ}

theorem nonempty_mulEquiv_perm_three_hypSU (h : UnitaryFieldData 2 1 K) :
    Nonempty (↥(hypSU h 1 0) ≃* Equiv.Perm (Fin 3)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := h.charP
  obtain ⟨F, hF, hFfin, hcard, ⟨e⟩⟩ := exists_hypSU_one_zero_mulEquiv h
  rw [pow_one] at hcard
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (f := 1) (by
    rw [← Nat.card_eq_fintype_card, hcard, pow_one])
  obtain ⟨e'⟩ := Lin.nonempty_mulEquiv_perm_three_of_card_two (K := F) hcard
  exact ⟨e.trans e'⟩

theorem hypSU_type (h : UnitaryFieldData 2 f K) (hε : ε ≤ 1) (hres : 2 ≤ 2 * s + ε) :
    (CFSG.Open.IsQuasisimple ↥(hypSU h s ε) ∨ Nonempty (↥(hypSU h s ε) ≃* Equiv.Perm (Fin 3))) ∨
      ∃ (K' : Type) (_ : Field K') (_ : Finite K'), Nat.card K' = 4 ∧
        Nonempty (↥(hypSU h s ε) ≃* ↥(StatedSU 3 2 K')) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases h3 : 3 ≤ 2 * s + ε
  · by_cases hmq : (2 * s + ε, 2 ^ f) = (3, 2)
    · rw [Prod.mk.injEq] at hmq
      obtain ⟨rfl, rfl⟩ : s = 1 ∧ ε = 1 := by omega
      obtain rfl : f = 1 := Nat.pow_right_injective le_rfl (hmq.2.trans (pow_one 2).symm)
      obtain ⟨R, hR⟩ := exists_isHypTransport h (r := 1) (ε := 1)
      refine Or.inr ⟨K, inferInstance, h.finite, ?_, ⟨hypTransport h hR⟩⟩
      rw [h.card]
      norm_num
    · exact Or.inl (Or.inl (hypSU_facts_of_three_le h h3 hmq).1)
  · obtain ⟨rfl, rfl⟩ : s = 1 ∧ ε = 0 := by omega
    by_cases hf2 : 2 ≤ f
    · exact Or.inl (Or.inl (hypSU_facts_two h hf2).1)
    · obtain rfl : f = 1 := by
        have := h.one_le
        omega
      exact Or.inl (Or.inr (nonempty_mulEquiv_perm_three_hypSU h))

theorem blockSub_type [Finite K] [CharP K 2] (h : UnitaryFieldData 2 f K) (hε : ε ≤ 1)
    (j : Option ↥I) (hj : IsBigBlock s ε I j) :
    (CFSG.Open.IsQuasisimple ↥(uniBlockSub (s := s) (ε := ε) h I j) ∨
      Nonempty (↥(uniBlockSub (s := s) (ε := ε) h I j) ≃* Equiv.Perm (Fin 3))) ∨
    (j = none ∧ ∃ (K' : Type) (_ : Field K') (_ : Finite K'), Nat.card K' = 4 ∧
      Nonempty (↥(uniBlockSub (s := s) (ε := ε) h I j) ≃* ↥(StatedSU 3 2 K'))) := by
  rcases j with _ | b
  · rcases hypSU_type h hε hj with hq | hsu
    · exact Or.inl hq
    · exact Or.inr ⟨rfl, hsu⟩
  · exact Or.inl (Lin.isQuasisimple_or_perm_three (K := K) hj
      (slEquivToGLRange (K := K) (b.1 - predCut I b.1)))

end Types

section WSup

theorem range_le_wSup_of_ker_eq {G : Type} [Group G] {D S : Type} [Group D] [Group S]
    (ℓ : D →* S) (hℓ : Function.Surjective ℓ) (φ : D →* G) (hker : ℓ.ker ≤ φ.ker)
    (hker' : φ.ker ≤ ℓ.ker) (hnormal : φ.range.Normal) (hS : IsSymThreeOrSUThreeTwo S) :
    φ.range ≤ CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.wSup G := by
  obtain ⟨ψ, hψ⟩ : ∃ ψ : S →* G, ψ.comp ℓ = φ :=
    ⟨ℓ.liftOfSurjective hℓ ⟨φ, hker⟩, MonoidHom.liftOfRightInverse_comp _ _ _ _⟩
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨d, rfl⟩ := hℓ x
    have : φ d = 1 := by rw [← hψ]; exact hx
    exact MonoidHom.mem_ker.mp (hker' this)
  have hrange : φ.range = ψ.range := by
    rw [← hψ, MonoidHom.range_comp, MonoidHom.range_eq_top.2 hℓ, Subgroup.map_top]
  rw [hrange] at hnormal ⊢
  refine Lin.le_wSup_of_normal hnormal (Or.inr (Or.inr ?_))
  let e : S ≃* ψ.range := MonoidHom.ofInjective hinj
  rcases hS with ⟨e'⟩ | ⟨K', hK', hfin, hc, ⟨e'⟩⟩
  · exact Or.inl ⟨e.symm.trans e'.some⟩
  · exact Or.inr ⟨K', hK', hfin, hc, ⟨e.symm.trans e'⟩⟩

end WSup

section BlockSubgroup

variable {f : ℕ} {K : Type} [Field K] {t s ε : ℕ} {I : Finset ℕ}

@[expose] def blockSubgroup (h : UnitaryFieldData 2 f K) (hε : ε ≤ 1) (hI : IsTopCut I t)
    (j : Option ↥I) : Subgroup ↥(flagStabilizer h (t + s) ε ↑I) where
  carrier := {y | (∀ k, k ≠ j → uniLeviHom (s := s) h hε hI y k = 1) ∧
    uniLeviHom (s := s) h hε hI y j ∈ uniBlockSub (s := s) (ε := ε) h I j}
  mul_mem' := fun {a b} ha hb => ⟨fun k hk => by
      rw [map_mul, Pi.mul_apply, ha.1 k hk, hb.1 k hk, one_mul], by
      rw [map_mul, Pi.mul_apply]
      exact mul_mem ha.2 hb.2⟩
  one_mem' := ⟨fun k _ => by rw [map_one]; rfl, by rw [map_one]; exact one_mem _⟩
  inv_mem' := fun {a} ha => ⟨fun k hk => by
      rw [map_inv, Pi.inv_apply, ha.1 k hk, inv_one], by
      rw [map_inv, Pi.inv_apply]
      exact inv_mem ha.2⟩

instance blockSubgroup_normal (h : UnitaryFieldData 2 f K) (hε : ε ≤ 1) (hI : IsTopCut I t)
    (j : Option ↥I) : (blockSubgroup (s := s) h hε hI j).Normal where
  conj_mem y hy q := by
    refine ⟨fun k hk => ?_, ?_⟩
    · rw [map_mul, map_mul, map_inv, Pi.mul_apply, Pi.mul_apply, Pi.inv_apply, hy.1 k hk,
        mul_one, mul_inv_cancel]
    · have hc : ⁅uniLeviHom (s := s) h hε hI q, uniLeviHom (s := s) h hε hI y⁆ ∈
          Subgroup.pi Set.univ (uniBlockSub (s := s) (ε := ε) h I) :=
        commutator_range_le_pi h hε hI
          (Subgroup.commutator_mem_commutator ⟨q, rfl⟩ ⟨y, rfl⟩)
      have e : uniLeviHom (s := s) h hε hI (q * y * q⁻¹) =
          ⁅uniLeviHom (s := s) h hε hI q, uniLeviHom (s := s) h hε hI y⁆ *
            uniLeviHom (s := s) h hε hI y := by
        rw [map_mul, map_mul, map_inv, commutatorElement_def]
        group
      rw [e, Pi.mul_apply]
      exact mul_mem ((Subgroup.mem_pi _).mp hc j trivial) hy.2

end BlockSubgroup

section Block

variable {A : Type} [Group A] [Finite A] {Y P : Subgroup A} {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {t s ε : ℕ} {I : Finset ℕ} (C : UniCover Y P h (t + s) ε ↑I)

theorem UniCover.toHat_mem_wSup (hε : ε ≤ 1) (hI : IsTopCut I t) (hPY : P ≤ Y)
    (j : Option ↥I) (hj : IsBigBlock s ε I j) (x : ↥(flagStabilizer h (t + s) ε ↑I))
    (hx1 : ∀ k, k ≠ j → uniLeviHom (s := s) h hε hI x k = 1)
    (hx2 : uniLeviHom (s := s) h hε hI x j ∈ uniBlockSub (s := s) (ε := ε) h I j) :
    C.toHat x ∈ CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.wSup
      (↥P ⧸ CFSG.pCore 2 ↥P) := by
  classical
  haveI : Finite K := h.finite
  haveI : CharP K 2 := h.charP
  set D := blockSubgroup (s := s) h hε hI j with hD
  have hxD : x ∈ D := ⟨hx1, hx2⟩
  let ℓ : ↥D →* ↥(uniBlockSub (s := s) (ε := ε) h I j) :=
    ((Pi.evalMonoidHom (uniBlockGroup K s ε I) j).comp
      ((uniLeviHom (s := s) h hε hI).comp D.subtype)).codRestrict _ fun y => y.2.2
  have hℓs : Function.Surjective ℓ := by
    rintro ⟨b, hb⟩
    have hmem : (Pi.mulSingle j b : ∀ k, uniBlockGroup K s ε I k) ∈
        (uniLeviHom (s := s) h hε hI).range := by
      refine pi_uniBlockSub_le_range h hε hI ((Subgroup.mem_pi _).mpr fun k _ => ?_)
      by_cases hk : k = j
      · subst hk
        rw [Pi.mulSingle_eq_same]
        exact hb
      · rw [Pi.mulSingle_eq_of_ne hk]
        exact one_mem _
    obtain ⟨y, hy⟩ := hmem
    have hyD : y ∈ D := ⟨fun k hk => by rw [hy, Pi.mulSingle_eq_of_ne hk], by
      rw [hy, Pi.mulSingle_eq_same]
      exact hb⟩
    refine ⟨⟨y, hyD⟩, Subtype.ext ?_⟩
    change uniLeviHom (s := s) h hε hI y j = b
    rw [hy, Pi.mulSingle_eq_same]
  let φ : ↥D →* ↥P ⧸ CFSG.pCore 2 ↥P := C.toHat.comp D.subtype
  have hker : ℓ.ker ≤ φ.ker := by
    intro y hy
    have h1 : uniLeviHom (s := s) h hε hI y.1 j = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp hy)
    have hyU : y.1 ∈ (uniLeviHom (s := s) h hε hI).ker := by
      rw [MonoidHom.mem_ker]
      funext k
      by_cases hk : k = j
      · subst hk
        exact h1
      · exact y.2.1 k hk
    rw [MonoidHom.mem_ker]
    show C.toHat y.1 = 1
    rw [UniCover.toHat, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact C.toP_mem_pCore_of_mem_ker hε hI hPY hyU
  have hrange : φ.range = D.map C.toHat := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hnormal : φ.range.Normal := by
    rw [hrange]
    exact (blockSubgroup_normal h hε hI j).map _ (C.toHat_surjective hPY)
  have hG : CFSG.pCore 2 (↥P ⧸ CFSG.pCore 2 ↥P) = ⊥ :=
    CFSG.AGLEmbedding.pCore_quotient_pCore_eq_bot' (X := ↥P) 2
  have hle : φ.range ≤ CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.wSup
      (↥P ⧸ CFSG.pCore 2 ↥P) := by
    rcases blockSub_type h hε j hj with hS | ⟨hjn, hsu⟩
    · exact Lin.range_le_wSup hG ℓ hℓs φ hker hnormal hS
    · refine range_le_wSup_of_ker_eq ℓ hℓs φ hker ?_ hnormal (Or.inr hsu)
      subst hjn
      intro y hy
      have hy1 : C.toHat y.1 = 1 := hy
      rw [UniCover.toHat, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hy1
      obtain ⟨s', hs', z, hz, hsz⟩ := C.exists_mul_of_toP_mem_pCore hε hI y.1 hy1
      obtain ⟨c, -, -, hc⟩ := C.mem_hypScalars_of_toP_eq_one hz
      set b₀ : ↥I := ⟨t, hI.mem⟩ with hb₀
      have hk₀ : uniLeviHom (s := s) h hε hI y.1 (some b₀) = 1 :=
        y.2.1 _ (Option.some_ne_none _)
      have hs'1 : uniLeviHom (s := s) h hε hI s' = 1 := MonoidHom.mem_ker.mp hs'
      have hlz : uniLeviHom (s := s) h hε hI z (some b₀) = 1 := by
        rw [hsz, map_mul, hs'1, one_mul] at hk₀
        exact hk₀
      have ht1 : 1 ≤ t := (hI.le t hI.mem).1
      have hm : 0 < t - predCut I t := Nat.sub_pos_of_lt (predCut_lt ht1)
      have hbr : t ≤ t + s := Nat.le_add_right t s
      have hentry := congrArg (fun g : GL (Fin (t - predCut I t)) K =>
        (g : Matrix (Fin (t - predCut I t)) (Fin (t - predCut I t)) K) ⟨0, hm⟩ ⟨0, hm⟩) hlz
      have hc1 : (c : K) = 1 := by
        have h2 : (eBlockHom h hε hI.mem ht1 hbr z : GL (Fin (t - predCut I t)) K) =
            1 := hlz
        have h3 := congrArg (fun g : GL (Fin (t - predCut I t)) K =>
          (g : Matrix (Fin (t - predCut I t)) (Fin (t - predCut I t)) K) ⟨0, hm⟩ ⟨0, hm⟩) h2
        simp only [coe_eBlockHom, Matrix.submatrix_apply, Units.val_one, Matrix.one_apply_eq]
          at h3
        have h4 : ((z : hypSU h (t + s) ε) : GL (HypIndex (t + s) ε) K) =
            Matrix.GeneralLinearGroup.scalar (HypIndex (t + s) ε) c := hc
        rw [h4, coe_scalar_eq_smul_one] at h3
        simpa using h3
      have hz1 : z = 1 := by
        apply Subtype.ext
        apply Subtype.ext
        have h4 : ((z : hypSU h (t + s) ε) : GL (HypIndex (t + s) ε) K) =
            Matrix.GeneralLinearGroup.scalar (HypIndex (t + s) ε) c := hc
        rw [h4]
        have : c = 1 := Units.ext hc1
        rw [this, map_one]
        rfl
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      change uniLeviHom (s := s) h hε hI y.1 none = 1
      rw [hsz, map_mul, hs'1, hz1, map_one, one_mul]
      rfl
  exact hle ⟨⟨x, hxD⟩, rfl⟩

theorem UniCover.normFix_autHom (hε : ε ≤ 1) (hI : IsTopCut I t) (hPY : P ≤ Y)
    (b : ↥(Subgroup.normalizer (Y : Set A))) (hbP : (b : A) ∈ Subgroup.normalizer (P : Set A))
    (hW : WCent P (b : A)) : UniNormFix h hε hI (C.autHom b) := by
  refine ⟨C.map_projFlag b hbP, fun j hj x hx1 hx2 => ?_⟩
  have hmem := C.toHat_mem_wSup hε hI hPY j hj x hx1 hx2
  have hc : (b : A) * ((C.toP x : ↥P) : A) * (b : A)⁻¹ * ((C.toP x : ↥P) : A)⁻¹ ∈
      pCoreOf 2 P := hW _ (C.toP x).2 hmem
  obtain ⟨c₀, hc₀, hc₀eq⟩ := hc
  obtain ⟨q, hq⟩ := C.toP_surjective hPY c₀
  have hσq : C.σ (q : hypSU h (t + s) ε) =
      Y.normalizerMonoidHom b (C.σ (x : hypSU h (t + s) ε)) *
        (C.σ (x : hypSU h (t + s) ε))⁻¹ := by
    apply Subtype.ext
    have h1 : ((C.σ (q : hypSU h (t + s) ε) : ↥Y) : A) = (c₀ : A) := by
      rw [← hq]
      rfl
    rw [h1, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.normalizerMonoidHom_apply_apply_coe]
    exact hc₀eq
  have hprojq : hypProj h (t + s) ε (q : hypSU h (t + s) ε) =
      C.autHom b (hypProj h (t + s) ε (x : hypSU h (t + s) ε)) *
        (hypProj h (t + s) ε (x : hypSU h (t + s) ε))⁻¹ := by
    rw [← C.compat (q : hypSU h (t + s) ε), hσq, C.autHom_apply_proj,
      ← C.compat (x : hypSU h (t + s) ε), QuotientGroup.mk_mul, map_mul,
      QuotientGroup.mk_inv, map_inv]
  rw [← hprojq]
  exact C.proj_mem_projUni hε hI q (hq ▸ hc₀)

end Block

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Uni
