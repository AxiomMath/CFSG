module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsAutFieldOrth
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsTriRank
import CFSG.HardMathSupport.Lang.Proving.OrthogonalFieldDescentOdd
import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.OrthOdd

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

open CFSG.Open QuadraticMap CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.RankThree.PartOne.OutStructure (Inn)
open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.ComponentInitial
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData

section Split

variable {p : ℕ} {Ω : Type} [Group Ω] {S B : Subgroup Ω} [S.Normal]

theorem inner_split_of_chain (hp : p.Prime) {X : Type*} [Group X] (e : X ≃* ↥S)
    (hB : IsElemAbelian p B) {D E : Subgroup (MulAut X)} (hID : Inn X ≤ D)
    (hD2 : ∀ δ ∈ D, δ ^ p ∈ Inn X → δ ∈ Inn X) (hBE : ∀ x ∈ B, transAut e x ∈ E)
    (hcomp : ∀ α ∈ E, ∀ β ∈ E, α ^ p ∈ D → β ^ p ∈ D →
      (∃ m : ℤ, α * β ^ m ∈ D) ∨ ∃ m : ℤ, β * α ^ m ∈ D) :
    B ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω)) = B ∨
      ∃ b ∈ B, b ∉ S ⊔ Subgroup.centralizer (S : Set Ω) ∧
        B = B ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω)) ⊔ Subgroup.zpowers b ∧
        Subgroup.zpowers b ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω)) = ⊥ := by
  set N := S ⊔ Subgroup.centralizer (S : Set Ω) with hN
  have hα : ∀ x y : Ω, transAut e (x * y) = transAut e x * transAut e y := fun x y => by
    rw [transAut_eq_congr, transAut_eq_congr, transAut_eq_congr, map_mul, map_mul]
  have hαz : ∀ (x : Ω) (m : ℤ), transAut e (x ^ m) = transAut e x ^ m := fun x m => by
    rw [transAut_eq_congr, transAut_eq_congr, map_zpow, map_zpow]
  have hαp : ∀ x ∈ B, transAut e x ^ p = 1 := fun x hx => by
    rw [transAut_eq_congr, ← map_pow, ← map_pow, hB.2 x hx, map_one, map_one]
  have hcompB : ∀ x ∈ B, ∀ y ∈ B, (∃ m : ℤ, x * y ^ m ∈ N) ∨ ∃ m : ℤ, y * x ^ m ∈ N := by
    intro x hx y hy
    have hxy : Commute (transAut e x) (transAut e y) := by
      rw [Commute, SemiconjBy, ← hα, ← hα, hB.comm hx hy]
    have hinn : ∀ (u v : Ω), u ∈ B → v ∈ B → ∀ m : ℤ, transAut e u * transAut e v ^ m ∈ D →
        u * v ^ m ∈ N := by
      intro u v hu hv m hm
      have huv : Commute (transAut e u) (transAut e v) := by
        rw [Commute, SemiconjBy, ← hα, ← hα, hB.comm hu hv]
      have hpow : (transAut e u * transAut e v ^ m) ^ p ∈ Inn X := by
        rw [(huv.zpow_right m).mul_pow, hαp u hu, one_mul, ← zpow_natCast, ← zpow_mul,
          mul_comm, zpow_mul, zpow_natCast, hαp v hv, one_zpow]
        exact one_mem _
      rw [← transAut_mem_inner_iff e, hα, hαz]
      exact hD2 _ hm hpow
    have hpD : ∀ u ∈ B, transAut e u ^ p ∈ D := fun u hu => by
      rw [hαp u hu]
      exact one_mem _
    rcases hcomp _ (hBE x hx) _ (hBE y hy) (hpD x hx) (hpD y hy) with ⟨m, hm⟩ | ⟨m, hm⟩
    · exact Or.inl ⟨m, hinn x y hx hy m hm⟩
    · exact Or.inr ⟨m, hinn y x hy hx m hm⟩
  by_cases h : B ≤ N
  · exact Or.inl (inf_eq_left.2 h)
  right
  obtain ⟨b, hbB, hbN⟩ := Set.not_subset.1 h
  have hbot : Subgroup.zpowers b ⊓ N = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hz, hzN⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    rw [Subgroup.mem_bot]
    have hbp : b ^ p = 1 := hB.2 b hbB
    by_cases hpm : (p : ℤ) ∣ m
    · obtain ⟨k, rfl⟩ := hpm
      rw [zpow_mul, zpow_natCast, hbp, one_zpow]
    · exfalso
      obtain ⟨u, v, huv⟩ := ((Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd.2 hpm)
      apply hbN
      have h1 : b = b ^ (u * (p : ℤ) + v * m) := by rw [huv, zpow_one]
      rw [zpow_add, mul_comm u (p : ℤ), zpow_mul, zpow_natCast, hbp, one_zpow, one_mul,
        mul_comm v m, zpow_mul] at h1
      rw [h1]
      exact N.zpow_mem hzN v
  refine ⟨b, hbB, hbN, le_antisymm (fun x hx => ?_) (sup_le inf_le_left
    (Subgroup.zpowers_le.2 hbB)), hbot⟩
  rcases hcompB x hx b hbB with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hx' : x = x * b ^ m * b ^ (-m) := by group
    rw [hx']
    exact Subgroup.mul_mem_sup ⟨B.mul_mem hx (B.zpow_mem hbB m), hm⟩
      (Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) _)
  · have hxp : x ^ p = 1 := hB.2 x hx
    have hpm : ¬ (p : ℤ) ∣ m := by
      rintro ⟨k, rfl⟩
      apply hbN
      have h1 : x ^ ((p : ℤ) * k) = 1 := by rw [zpow_mul, zpow_natCast, hxp, one_zpow]
      rw [h1, mul_one] at hm
      exact hm
    obtain ⟨u, v, huv⟩ := ((Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd.2 hpm)
    have hbx : b * x = x * b := hB.comm hbB hx
    have hcomm' : Commute b (x ^ m) := Commute.zpow_right hbx m
    have hxv : x = (x ^ m) ^ v := by
      have h1 : x = x ^ (u * (p : ℤ) + v * m) := by rw [huv, zpow_one]
      rw [zpow_add, mul_comm u (p : ℤ), zpow_mul, zpow_natCast, hxp, one_zpow, one_mul,
        mul_comm v m, zpow_mul] at h1
      exact h1
    have hxv' : x = (b * x ^ m) ^ v * b ^ (-v) := by
      rw [hcomm'.mul_zpow, (hcomm'.zpow_zpow v v).eq, mul_assoc, ← zpow_add, add_neg_cancel,
        zpow_zero, mul_one]
      exact hxv
    rw [hxv']
    exact Subgroup.mul_mem_sup ⟨B.zpow_mem (B.mul_mem hbB (B.zpow_mem hx m)) v,
      N.zpow_mem hm v⟩ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) _)

end Split

section Count

variable {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω} [S.Normal]
variable {K : Type} [Field K] [Finite K] {d : ℕ}

theorem card_dvd_three_of_isCyclic {C : Type*} [Group C] [Finite C] [IsCyclic C]
    (h : ∀ x : C, x ^ 3 = 1) : Nat.card C ∣ 3 := by
  rw [← IsCyclic.exponent_eq_card]
  exact Monoid.exponent_dvd_of_forall_pow_eq_one h

open CFSG.RankThree.Classical.SteinbergBY in
open scoped Pointwise in
theorem card_le_of_triality (hZ : Subgroup.center ↥S = ⊥) {f : ℕ}
    (hAut : Nat.card (K ≃+* K) ∣ f) (Q : QuadraticForm K (Fin d → K))
    (hgates : OrthogonalGates Q f)
    (hrank : ∀ y : MulAut (matrixProjectiveDerived Q), y ^ 3 = 1 → y ∉ matrixProjectiveImage Q →
      ∀ E : Subgroup (matrixProjectiveDerived Q), E ≤ fixSubgroup y → IsElemAbelian 3 E →
        Nat.card E ≤ 3 ^ 2)
    (e : matrixProjectiveDerived Q ≃* ↥S) (hB : IsElemAbelian 3 B)
    (hB0 : Nat.card ↥(B ⊓ Subgroup.centralizer (S : Set Ω)) = 3) {y : Ω} (hy : y ∈ B)
    (hyE : transAut e y ∉ matrixProjectiveImage Q) :
    Nat.card B ≤ 3 ^ 5 ∧ (¬ 3 ∣ f → Nat.card B ≤ 3 ^ 4) := by
  classical
  haveI : Finite (K ≃+* K) :=
    Finite.of_injective (fun σ : K ≃+* K => (σ : K → K)) DFunLike.coe_injective
  set T := matrixProjectiveDerived Q with hTdef
  obtain ⟨-, ⟨ψ, -, hψker, hψcyc⟩, ⟨-, k, hk⟩, horb, -, hEA, -⟩ := hgates
  have hZT : ∀ t : T, (∀ u : T, u * t = t * u) → t = 1 := by
    intro t ht
    have h1 : e t ∈ Subgroup.center ↥S := Subgroup.mem_center_iff.2 fun s => by
      obtain ⟨u, rfl⟩ := e.surjective s
      rw [← map_mul, ← map_mul, ht u]
    rw [hZ, Subgroup.mem_bot] at h1
    exact (map_eq_one_iff e e.injective).1 h1
  have hconj_inj : Function.Injective (MulAut.conj : T →* MulAut T) := by
    rw [injective_iff_map_eq_one]
    intro t ht
    refine hZT t fun u => ?_
    have := congrArg (fun α : MulAut T => α u) ht
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc u * t = t * u * t⁻¹ * t := by rw [this]
      _ = t * u := by group
  set α : Ω →* MulAut T := (MulAut.congr e.symm).toMonoidHom.comp MulAut.conjNormal with hαdef
  have hαt : ∀ x, transAut e x = α x := fun x => rfl
  set Bb := B.map α with hBb
  have hBbel : IsElemAbelian 3 Bb := CFSG.SectionRank.isElemAbelian_map hB α
  have hcardB : Nat.card B = 3 * Nat.card Bb := by
    set α' := α.comp B.subtype with hα'
    have h1 := Subgroup.card_ker_mul_card_range α'
    have hr : α'.range = Bb := by rw [hα', MonoidHom.range_comp, Subgroup.range_subtype]
    have hkr : α'.ker = (B ⊓ Subgroup.centralizer (S : Set Ω)).subgroupOf B := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro hx
        refine ⟨x.2, Subgroup.mem_centralizer_iff.2 fun s hs => ?_⟩
        change (MulAut.congr e.symm) (MulAut.conjNormal (x : Ω)) = 1 at hx
        have h2 : MulAut.conjNormal (x : Ω) = (1 : MulAut ↥S) :=
          (MulAut.congr e.symm).injective (hx.trans (map_one _).symm)
        have h3 := congrArg (fun β : MulAut ↥S => ((β ⟨s, hs⟩ : ↥S) : Ω)) h2
        simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h3
        calc s * x = (x : Ω) * s * (x : Ω)⁻¹ * x := by rw [h3]
          _ = x * s := by group
      · rintro ⟨-, hx⟩
        have h2 : MulAut.conjNormal (x : Ω) = (1 : MulAut ↥S) := by
          ext s
          simp only [MulAut.conjNormal_apply, MulAut.one_apply]
          rw [← (Subgroup.mem_centralizer_iff.1 hx) s s.2, mul_inv_cancel_right]
        change (MulAut.congr e.symm) (MulAut.conjNormal (x : Ω)) = 1
        rw [h2, map_one]
    rw [hr, hkr] at h1
    rw [← h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv, hB0]
  have hidx : (matrixProjectiveImage Q).index ≤ 3 := by
    have hst : (projectivePointFamilyAut Q).index =
        (MulAction.orbit (MulAut T) (projectivePointFamily Q)).ncard :=
      MulAction.index_stabilizer _ _
    rw [← hEA, hst]
    exact horb
  have hEidx0 : (matrixProjectiveImage Q).relIndex ⊤ ≠ 0 := by
    rw [Subgroup.relIndex_top_right]
    exact Subgroup.index_ne_zero_of_finite
  have ha : Nat.card Bb ≤ 3 * Nat.card ↥((matrixProjectiveImage Q) ⊓ Bb) := by
    have h1 := Subgroup.relIndex_mul_card (H := (matrixProjectiveImage Q)) (K := Bb)
    have h2 : (matrixProjectiveImage Q).relIndex Bb ≤ 3 :=
      (Subgroup.relIndex_le_of_le_right le_top hEidx0).trans
      (by rw [Subgroup.relIndex_top_right]; exact hidx)
    rw [← h1]
    exact Nat.mul_le_mul_right _ h2
  set yb := α y with hyb
  have hyb3 : yb ^ 3 = 1 := hBbel.2 yb ⟨y, hy, rfl⟩
  set Inn' := (MulAut.conj : T →* MulAut T).range with hInn'
  set Et := (Bb ⊓ Inn').comap (MulAut.conj : T →* MulAut T) with hEt
  have hEtcard : Nat.card Et = Nat.card ↥(Bb ⊓ Inn') := by
    have h1 : Et.map (MulAut.conj : T →* MulAut T) = Bb ⊓ Inn' :=
      Subgroup.map_comap_eq_self (inf_le_right)
    rw [← h1, Subgroup.card_map_of_injective hconj_inj]
  have hEtfix : Et ≤ fixSubgroup yb := by
    intro t ht
    rw [mem_fixSubgroup]
    have hc : yb * MulAut.conj t = MulAut.conj t * yb := hBbel.comm ⟨y, hy, rfl⟩ ht.1
    have h1 : MulAut.conj (yb t) = MulAut.conj t := by
      rw [show MulAut.conj (yb t) = yb * MulAut.conj t * yb⁻¹ by
        ext u
        simp [MulAut.conj_apply, MulAut.mul_apply], hc, mul_inv_cancel_right]
    exact hconj_inj h1
  have hEtel : IsElemAbelian 3 Et := (hBbel.mono inf_le_left).comap hconj_inj
  have hc : Nat.card ↥(Bb ⊓ Inn') ≤ 3 ^ 2 := by
    rw [← hEtcard]
    exact hrank yb hyb3 (by rw [hyb, ← hαt]; exact hyE) Et hEtfix hEtel
  set W := ((matrixProjectiveImage Q) ⊓ Bb).subgroupOf (matrixProjectiveImage Q) with hW
  have hWcard : Nat.card W = Nat.card ↥((matrixProjectiveImage Q) ⊓ Bb) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  set ψW := ψ.comp W.subtype with hψW
  have h1 := Subgroup.card_ker_mul_card_range ψW
  have hrange : Nat.card ψW.range ∣ 3 ∧ Nat.card ψW.range ∣ f := by
    have hle : ψW.range ≤ ψ.range := by
      rw [hψW, MonoidHom.range_comp]
      exact Subgroup.map_le_range _ _
    haveI : IsCyclic ψ.range := hψcyc
    haveI : IsCyclic ψW.range := Subgroup.isCyclic_of_le hle
    refine ⟨card_dvd_three_of_isCyclic fun x => ?_, (Subgroup.card_subgroup_dvd_card _).trans hAut⟩
    obtain ⟨w, hw⟩ := x.2
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hw, ← map_pow, Subgroup.coe_one]
    have hw3 : w ^ 3 = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_pow]
      exact hBbel.2 _ (Subgroup.mem_subgroupOf.1 w.2).2
    rw [hw3, map_one]
  have hker : Nat.card ψW.ker ≤ Nat.card ↥(Bb ⊓ Inn') := by
    refine Nat.card_le_card_of_injective
      (fun w => ⟨((w : W) : (matrixProjectiveImage Q)), ?_⟩) ?_
    · have hwW := Subgroup.mem_subgroupOf.1 (w : W).2
      have hwD : ((((w : W) : (matrixProjectiveImage Q))) : MulAut T) ∈
          (linearConjugationHom Q).range := by
        have h2 : ((w : W) : (matrixProjectiveImage Q)) ∈ ψ.ker :=
          MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 w.2)
        rw [hψker, Subgroup.mem_subgroupOf] at h2
        exact h2
      refine ⟨hwW.2, ?_⟩
      have hcop : Nat.Coprime ((CFSG.ComponentClassification.OuterAutomorphisms.inner T).relIndex
          (linearConjugationHom Q).range) 3 := by
        rw [hk]
        exact Nat.Coprime.pow_left k (by norm_num)
      exact mem_of_pow_mem_of_coprime (CFSG.ComponentClassification.OuterAutomorphisms.inner T)
        hwD (by rw [hBbel.2 _ hwW.2]; exact one_mem _) hcop
    · intro w w' h
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : ↥(Bb ⊓ Inn') => (z : MulAut T)) h
  have hb : Nat.card ↥((matrixProjectiveImage Q) ⊓ Bb) ≤
      Nat.card ↥(Bb ⊓ Inn') * Nat.card ψW.range := by
    rw [← hWcard, ← h1]
    exact Nat.mul_le_mul_right _ hker
  have hr3 : Nat.card ψW.range ≤ 3 := Nat.le_of_dvd (by norm_num) hrange.1
  refine ⟨?_, fun hf3 => ?_⟩
  · calc Nat.card B = 3 * Nat.card Bb := hcardB
      _ ≤ 3 * (3 * Nat.card ↥((matrixProjectiveImage Q) ⊓ Bb)) := Nat.mul_le_mul_left _ ha
      _ ≤ 3 * (3 * (Nat.card ↥(Bb ⊓ Inn') * Nat.card ψW.range)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hb)
      _ ≤ 3 * (3 * (3 ^ 2 * 3)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul hc hr3))
      _ = 3 ^ 5 := by norm_num
  · have hr1 : Nat.card ψW.range = 1 := by
      have h2 := Nat.dvd_gcd hrange.1 hrange.2
      have h3 : Nat.gcd 3 f = 1 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hf3
      rw [h3] at h2
      exact Nat.dvd_one.1 h2
    calc Nat.card B = 3 * Nat.card Bb := hcardB
      _ ≤ 3 * (3 * Nat.card ↥((matrixProjectiveImage Q) ⊓ Bb)) := Nat.mul_le_mul_left _ ha
      _ ≤ 3 * (3 * (Nat.card ↥(Bb ⊓ Inn') * Nat.card ψW.range)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hb)
      _ ≤ 3 * (3 * (3 ^ 2 * 1)) := by
          rw [hr1]
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul hc le_rfl))
      _ = 3 ^ 4 := by norm_num

end Count

section Three

variable {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω} [S.Normal]

open CFSG.RankThree.Classical.SteinbergBY CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.PartOne.KCOrthogonalDescent in
theorem exists_clsData_orthPlusFour_three (hcore : GLAPPrimeCore 3 ↥S = ⊥)
    (hZ : Subgroup.center ↥S = ⊥) {ℓ f : ℕ}
    (hmodel : StatedClassicalModel (PSimple 3 S) .POmegaPlus 4 ℓ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = ℓ ^ f)
    (e : PSimple 3 S ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K))) {B : Subgroup Ω}
    (hB : IsElemAbelian 3 B)
    (hBE : ∀ e₃ : matrixProjectiveDerived (coordinateQuadPlus 4 K) ≃* ↥S, ∀ x ∈ B,
      transAut e₃ x ∈ matrixProjectiveImage (coordinateQuadPlus 4 K)) :
    ∃ φ : ↥(matrixDerived (coordinateQuadPlus 4 K)) →* Ω, φ.range = S ∧
      φ.ker = (StatedScalars (Fin (2 * 4)) K).subgroupOf
        (matrixDerived (coordinateQuadPlus 4 K)) ∧
      ¬ 3 ∣ Nat.card φ.ker ∧
      ∃ θ : ↥(B ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω))) →*
          ↥(matrixDerived (coordinateQuadPlus 4 K)),
        (∀ x, (φ (θ x))⁻¹ * (x : Ω) ∈ Subgroup.centralizer (S : Set Ω)) ∧
        IsElemAbelian 3 θ.range ∧ θ.range ⊓ φ.ker = ⊥ ∧
        (∀ x, θ x = 1 ↔ (x : Ω) ∈ Subgroup.centralizer (S : Set Ω)) ∧
        (B ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω)) = B ∨
          ∃ b ∈ B, b ∉ S ⊔ Subgroup.centralizer (S : Set Ω) ∧
            B = B ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω)) ⊔ Subgroup.zpowers b ∧
            Subgroup.zpowers b ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω)) = ⊥ ∧
            ∃ (A : GL (Fin (2 * 4)) K) (σ : K ≃+* K), FieldAct 3 φ b A σ ∧
              FormRel (polarBilin (coordinateQuadPlus 4 K)) A σ ∧
              ∀ x, semiConj A σ ((θ x : ↥(matrixDerived (coordinateQuadPlus 4 K))) :
                GL (Fin (2 * 4)) K) = θ x) := by
  set Q := coordinateQuadPlus 4 K with hQ
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨-, hnd, hT3, -⟩ := coordinate_model_witness_plus hmodel K hK e
  have hQ0 : ∃ v, Q v ≠ 0 :=
    CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT3
  have hab := orthogonal_model_isometry_abelianization_order_bound _ .POmegaPlus
    (.inr (.inl rfl)) 4 ℓ f hmodel K hK (quadPlus 4 K) (coe_quadPlus 4 K) e
  have hab' := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.card_abelianization_two_pow_of_bound
    (plusIndexEquiv 4) (quadPlus 4 K) hab
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates _ .POmegaPlus
    (Or.inr (Or.inl rfl)) 4 ℓ f hmodel K hK e
  obtain ⟨-, ⟨ψ, -, hψker, hψcyc⟩, ⟨hInnD, k, hk⟩, -⟩ := hgates
  obtain ⟨φ, hφS, hφk⟩ := exists_cover_of_center_eq_bot hcore hZ
    ((coordinatePlusWitnessEquiv K e).trans (statedProjMatrixDerivedEquiv Q).symm)
  have hker : φ.ker ≤ Subgroup.center ↥(matrixDerived Q) :=
    hφk ▸ CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _
  have hC : ¬ 3 ∣ Nat.card φ.ker := hφk ▸ not_dvd_card_orthScalars Q hQ0 Nat.prime_three
    (by norm_num)
  obtain ⟨θ, hθ, hθel, hθk, hθ1⟩ := exists_inner_lift Nat.prime_three hB hZ φ hφS hker hC
  set e₃ : matrixProjectiveDerived Q ≃* ↥S :=
    (statedProjMatrixDerivedEquiv Q).symm.trans (coverProjEquiv φ hφS hφk) with he₃
  refine ⟨φ, hφS, hφk, hC, θ, hθ, hθel, hθk, hθ1, ?_⟩
  have hD2 : ∀ δ ∈ (linearConjugationHom Q).range, δ ^ 3 ∈ Inn (matrixProjectiveDerived Q) →
      δ ∈ Inn (matrixProjectiveDerived Q) := fun δ hδ h3 =>
    mem_of_pow_mem_of_coprime (CFSG.ComponentClassification.OuterAutomorphisms.inner _) hδ h3
      (by rw [hk]; exact Nat.Coprime.pow_left k (by norm_num))
  have hcomp : ∀ α ∈ matrixProjectiveImage Q, ∀ β ∈ matrixProjectiveImage Q,
      α ^ 3 ∈ (linearConjugationHom Q).range → β ^ 3 ∈ (linearConjugationHom Q).range →
      (∃ m : ℤ, α * β ^ m ∈ (linearConjugationHom Q).range) ∨
        ∃ m : ℤ, β * α ^ m ∈ (linearConjugationHom Q).range := by
    intro α hα β hβ hα3 hβ3
    obtain ⟨γ, hγ⟩ := hψcyc.exists_generator
    obtain ⟨g, hg⟩ := γ.2
    have hgen : ∀ x : matrixProjectiveImage Q, ∃ m : ℤ, g ^ m * x ∈ ψ.ker := by
      intro x
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (hγ ⟨ψ x, x, rfl⟩)
      refine ⟨-m, ?_⟩
      rw [MonoidHom.mem_ker, map_mul, map_zpow, hg]
      have hm' : (γ : K ≃+* K) ^ m = ψ x := congrArg Subtype.val hm
      rw [zpow_neg, hm', inv_mul_cancel]
    have hmemK : ∀ z : matrixProjectiveImage Q,
        z ∈ ψ.ker ↔ (z : MulAut (matrixProjectiveDerived Q)) ∈ (linearConjugationHom Q).range :=
      fun z => by rw [hψker, Subgroup.mem_subgroupOf]
    rcases CFSG.RankThree.PartOne.OutStructure.chain_of_cyclic_quotient Nat.prime_three g hgen
      ⟨α, hα⟩ ⟨β, hβ⟩ ⟨1, (hmemK _).2 (by rw [pow_one]; exact hα3)⟩
      ⟨1, (hmemK _).2 (by rw [pow_one]; exact hβ3)⟩ with ⟨m, hm⟩ | ⟨m, hm⟩
    · exact Or.inl ⟨m, (hmemK _).1 hm⟩
    · exact Or.inr ⟨m, (hmemK _).1 hm⟩
  rcases inner_split_of_chain Nat.prime_three e₃ hB hInnD hD2 (hBE e₃) hcomp with
    h | ⟨b, hb, hbN, hBb, hbinf⟩
  · exact Or.inl h
  · right
    set γ := transAut e₃ b with hγ
    have hγo : orderOf γ = 3 := orderOf_transAut_eq e₃ Nat.prime_three (hB.2 b hb) hbN
    have hγp : γ ^ 3 = 1 := by rw [← hγo]; exact pow_orderOf_eq_one γ
    have hγD : γ ∉ (linearConjugationHom Q).range := fun hD =>
      hbN ((transAut_mem_inner_iff e₃ b).1 (hD2 γ hD (by rw [hγp]; exact one_mem _)))
    have hγE : γ ∈ matrixProjectiveImage Q := hBE e₃ b hb
    obtain ⟨σ, U, Q', T, ν, hσo, hcard, hUγ, hUσ, hQ'σ, hT, hTU⟩ := orthDesc_of hγE
      (CFSG.HardMathSupport.Lang.Proving.orthogonal_prime_semilinear_actual_fixed_form_descent'
        (PSimple 3 S) .POmegaPlus (.inr (.inl rfl)) 4 ℓ f 3 hmodel Nat.prime_three (by norm_num)
        K hK e γ hγE hγD hγo) hK (by
          rintro U Q₀ ⟨-, -, -, -, T, ν, hT, -, hTU, -⟩
          exact ⟨coordinateQuadPlus 4 K, T, ν, coordinateQuadPlus_field 4 U.val.right, hT, hTU⟩)
    obtain ⟨hact, hform⟩ := fieldAct_of_transport hQ'σ U hUσ T ν hT hTU φ hφS hφk hUγ.symm hσo
      hcard
    exact ⟨b, hb, hbN, hBb, hbinf, T⁻¹, σ, hact, hform, semiConj_eq_of_fieldAct Nat.prime_three
      hZ φ hφS hker hC hB inf_le_left θ hθ (fun x => hθel.2 _ ⟨x, rfl⟩) hb hact⟩

open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin in
theorem isPlus_coordinateQuadPlus_four {K : Type} [Field K] [Finite K]
    (hnd : (polarBilin (coordinateQuadPlus 4 K)).Nondegenerate) :
    IsPlus (coordinateQuadPlus 4 K) 4 := by
  set ε := plusIndexEquiv 4 with hε
  have hQ : ∀ v : Fin 4 ⊕ Fin 4 → K,
      coordinateQuadPlus 4 K (fun j => v (ε.symm j)) = quadPlus 4 K v := fun v => by
    rw [coordinateQuadPlus, reindexQuadraticForm_apply]
    exact congrArg (quadPlus 4 K) (funext fun i => by rw [Equiv.symm_apply_apply])
  have hpol : ∀ v w : Fin 4 ⊕ Fin 4 → K,
      polar (coordinateQuadPlus 4 K) (fun j => v (ε.symm j)) (fun j => w (ε.symm j)) =
        polar (quadPlus 4 K) v w := fun v w => by
    rw [polar, polar, ← hQ v, ← hQ w, ← hQ (v + w)]
    rfl
  refine ⟨hnd, by rw [Module.finrank_fin_fun], ⟨fun i =>
    { e := fun j => (plusPair K i).e (ε.symm j)
      f := fun j => (plusPair K i).f (ε.symm j)
      Q_e := by rw [hQ]; exact (plusPair K i).Q_e
      Q_f := by rw [hQ]; exact (plusPair K i).Q_f
      polar_ef := by rw [hpol]; exact (plusPair K i).polar_ef }, fun i j hij => ?_⟩⟩
  have h := plusPair_orth (K := K) hij
  exact ⟨by rw [hpol]; exact h.ee, by rw [hpol]; exact h.ef, by rw [hpol]; exact h.fe,
    by rw [hpol]; exact h.ff⟩

open CFSG.RankThree.Classical.SteinbergBY CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal in
theorem forall_transAut_mem_image (hTri : CFSG.LocalAnalysis.GLTheoremA.S267.Cls.D4TriRank)
    (hZ : Subgroup.center ↥S = ⊥) {ℓ f : ℕ} (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3)
    (hmodel : StatedClassicalModel (PSimple 3 S) .POmegaPlus 4 ℓ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = ℓ ^ f)
    (e : PSimple 3 S ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K))) {B : Subgroup Ω}
    (hB : IsElemAbelian 3 B) (hB0 : Nat.card ↥(B ⊓ Subgroup.centralizer (S : Set Ω)) = 3)
    (hcard : 3 ^ 5 ≤ Nat.card B) (hnot : ¬ (3 ∣ f ∧ Nat.card B = 3 ^ 5))
    (e₃ : matrixProjectiveDerived (coordinateQuadPlus 4 K) ≃* ↥S) :
    ∀ x ∈ B, transAut e₃ x ∈ matrixProjectiveImage (coordinateQuadPlus 4 K) := by
  intro x hx
  by_contra hxE
  obtain ⟨hℓ, hf, -⟩ := hmodel.1
  obtain ⟨-, hnd, -, -⟩ := coordinate_model_witness_plus hmodel K hK e
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates _ .POmegaPlus
    (Or.inr (Or.inl rfl)) 4 ℓ f hmodel K hK e
  obtain ⟨-, -, -, -, hAutf, -⟩ := finite_field_automorphism_fixed_field_cardinality hℓ hf hK
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hℓ.odd_of_ne_two hℓ2).pow
  have h3K : ¬ 3 ∣ Nat.card K := by
    rw [hK]
    intro h3
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1
      (Nat.prime_three.dvd_of_dvd_pow h3)).symm
  have hplus := isPlus_coordinateQuadPlus_four hnd
  obtain ⟨h5, h4⟩ := card_le_of_triality hZ (by rw [hAutf]) _ hgates
    (fun y hy3 hyE E hE hEel => hTri K _ hodd h3K hplus y hy3 hyE E hE hEel) e₃ hB hB0 hx hxE
  by_cases h3f : 3 ∣ f
  · exact hnot ⟨h3f, le_antisymm h5 hcard⟩
  · have := h4 h3f
    have : 3 ^ 4 < 3 ^ 5 := by norm_num
    omega

end Three

end CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

end
