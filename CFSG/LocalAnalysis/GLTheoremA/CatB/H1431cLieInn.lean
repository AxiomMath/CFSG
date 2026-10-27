module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieOrdExc
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoInn

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)
open CFSG.HardMathSupport.Solomon.LocalBalance

theorem lieSInn_component_index (hL : LieSemisimpleCent) {S : Type} [Group S] [Finite S]
    (hS : IsSimpleGroup S) (hnc : ∃ a b : S, a * b ≠ b * a)
    (d : TauCeti.ValidLieTypeIndex) (hd : d.1.characteristic = 2)
    (e : S ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hI : CompIdxAt 3 d.1 (TauCeti.CFSGIndex.lie d).Group)
    {α : MulAut S} (hα : α ∈ innAutDerived S) (hα3 : α ^ 3 = 1) (hα1 : α ≠ 1)
    {T : TauCeti.CFSGIndex → Prop} (hC : CompOfType S α T) :
    ∃ (i : TauCeti.CFSGIndex) (J : Subgroup S), compRelC d.1 i ∧
      Nonempty (↥J ⧸ Subgroup.center ↥J ≃* i.Group) ∧ catalogIs (↥J ⧸ Subgroup.center ↥J) T := by
  obtain ⟨J, hJ, hT⟩ := hC
  have hpil : PerfectInLayer α :=
    hL S hS hnc d ⟨e⟩ 3 Nat.prime_three (by norm_num) (by rw [hd]; norm_num) α hα3 hα1
  have hJle := hpil J hJ.1 (glaPComponent_perfect hJ)
  have hJcomp := (glaPComponent_isComponent_of_le_layer hJ hJle).1
  obtain ⟨i, ⟨φ⟩, hrel⟩ := (compIdxAt_of_mulEquiv e.symm hI) α hα hα3 hα1 J hJcomp
  refine ⟨i, J, hrel, ⟨φ⟩, ?_⟩
  have hq : CFSG.Open.IsQuasisimple (PQuot 3 J) := isQuasisimple_quotient_of_glaPComponent hJ
  haveI : Nontrivial (PQuot 3 J) := by
    have := hq.2.toNontrivial
    obtain ⟨a, b, hab⟩ := exists_pair_ne (PQuot 3 J ⧸ Subgroup.center (PQuot 3 J))
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨⟨a, b, fun h => hab (by rw [h])⟩⟩
  have hne : GLAPPrimeCore 3 ↥J ≠ ⊤ := by
    intro htop
    obtain ⟨a, b, hab⟩ := exists_pair_ne (PQuot 3 J)
    apply hab
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    rw [QuotientGroup.eq, htop]
    exact Subgroup.mem_top _
  have hker : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J)).ker ≤ Subgroup.center ↥J := by
    rw [QuotientGroup.ker_mk']
    exact le_center_of_normal_of_isQuasisimple hJcomp.2.2 (GLAPPrimeCore.normal 3 ↥J) hne
  obtain ⟨ψ⟩ := psimple_equiv_of_central_surj hJcomp.2.2
    (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J)) (QuotientGroup.mk'_surjective _) hker
  obtain ⟨i', hi', ⟨f⟩⟩ := hT
  exact ⟨i', hi', ⟨ψ.trans f⟩⟩

theorem lieSInn_of_isSp6two {j : TauCeti.ValidLieTypeIndex} (h : S9.isSp6two (.lie j)) :
    ∃ q : TauCeti.PrimePower, j.1 = .B 3 q ∧ q.card = 2 := by
  obtain ⟨e, hv⟩ := j
  cases e with
  | B n q =>
    rcases n with _ | _ | _ | _ | n
    · exact h.elim
    · exact h.elim
    · exact h.elim
    · exact ⟨q, rfl, h⟩
    · exact h.elim
  | _ => exact h.elim

theorem lieSInn_of_isSp48 {j : TauCeti.ValidLieTypeIndex} (h : S8.L84.isSp48 (.lie j)) :
    ∃ q : TauCeti.PrimePower, j.1 = .B 2 q ∧ q.card = 8 := by
  obtain ⟨e, hv⟩ := j
  cases e with
  | B n q =>
    rcases n with _ | _ | _ | n
    · exact h.elim
    · exact h.elim
    · exact ⟨q, rfl, h⟩
    · exact h.elim
  | _ => exact h.elim

theorem lieSInn_card_sp6 (hB : LieOrderBridge) {T : Type} [Group T] [Finite T]
    (h : catalogIs T S9.isSp6two) : Nat.card T = 1451520 := by
  obtain ⟨i, hi, ⟨φ⟩⟩ := h
  cases i with
  | lie j =>
    obtain ⟨q, hj, hq⟩ := lieSInn_of_isSp6two hi
    rw [hB j T ⟨φ⟩, hj]
    show orderBC 3 q.card = 1451520
    rw [hq]
    decide +kernel
  | _ => exact hi.elim

theorem lieSInn_card_sp48 (hB : LieOrderBridge) {T : Type} [Group T] [Finite T]
    (h : catalogIs T S8.L84.isSp48) : Nat.card T = 1056706560 := by
  obtain ⟨i, hi, ⟨φ⟩⟩ := h
  cases i with
  | lie j =>
    obtain ⟨q, hj, hq⟩ := lieSInn_of_isSp48 hi
    rw [hB j T ⟨φ⟩, hj]
    show orderBC 2 q.card = 1056706560
    rw [hq]
    decide +kernel
  | _ => exact hi.elim

theorem lieSInn_exp_of_compRel {d e : TauCeti.LieTypeIndex} (hd : d.characteristic = 2) {m : ℕ}
    (hm : fieldSize e = 2 ^ m) (hrel : compRel d e) :
    ∃ k : ℕ, 1 ≤ k ∧ k ∣ m ∧ fieldSize d = 2 ^ k := by
  obtain ⟨k0, hk0, hkd⟩ := I1431C2.exists_fieldSize_two_pow hd
  rcases hrel with ⟨-, ⟨j, hj, hf⟩, -⟩ | ⟨hf2, -⟩ | ⟨hf3, -⟩
  · rw [hm, hkd, ← pow_mul] at hf
    exact ⟨k0, hk0, ⟨j, Nat.pow_right_injective le_rfl hf⟩, hkd⟩
  · exact ⟨1, le_rfl, one_dvd m, by rw [hf2]; rfl⟩
  · exfalso
    have h2 : 2 ∣ 2 ^ k0 := dvd_pow_self 2 (by omega)
    rw [← hkd, hf3] at h2
    omega

theorem lieSInn_fieldSize (hB : LieOrderBridge) {T : Type} [Group T] [Finite T]
    (d : TauCeti.ValidLieTypeIndex) (hd : d.1.characteristic = 2) (i : TauCeti.CFSGIndex)
    (hrel : compRelC d.1 i) (φ : T ≃* i.Group) {N : ℕ} (hNT : Nat.card T = N)
    (hN : N = 1451520 ∨ N = 1056706560) :
    (N = 1451520 → fieldSize d.1 = 2) ∧
      (N = 1056706560 → fieldSize d.1 = 2 ∨ fieldSize d.1 = 8) := by
  have hNm : Nat.card T ∈ lieSOrdN := by
    rw [hNT]
    exact lieSOrd_mem_of_eq (by omega)
  cases i with
  | cyclic _ _ => exact hrel.elim
  | sporadic _ => exact hrel.elim
  | alternating n hn =>
    exfalso
    rcases hrel with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
      exact lieSOrd_not_alt φ.toEquiv hNm (by omega)
  | lie e =>
    have hcard : Nat.card T = lieOrderFormula e.1 := hB e T ⟨φ⟩
    rw [hcard] at hNm
    rcases lieSOrd_cases e.2 hNm with ⟨q, hq, hq2, hv⟩ | ⟨q, hq, hq729, hv⟩ | ⟨q, hq, hq8, hv⟩
    · have hfe : fieldSize e.1 = 2 ^ 1 := by rw [hq]; simpa [fieldSize] using hq2
      obtain ⟨k, -, hk, hfd⟩ := lieSInn_exp_of_compRel hd hfe hrel
      have hk1 : k = 1 := Nat.dvd_one.1 hk
      exact ⟨fun _ => by rw [hfd, hk1]; rfl, fun h => by omega⟩
    · exfalso
      omega
    · have hfe : fieldSize e.1 = 2 ^ 3 := by rw [hq]; simpa [fieldSize] using hq8
      obtain ⟨k, -, hk, hfd⟩ := lieSInn_exp_of_compRel hd hfe hrel
      refine ⟨fun h => by omega, fun _ => ?_⟩
      rcases (Nat.dvd_prime Nat.prime_three).1 hk with rfl | rfl
      · exact Or.inl (by rw [hfd]; rfl)
      · exact Or.inr (by rw [hfd]; rfl)

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
