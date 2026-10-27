module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T2021LayerExc
import CFSG.LocalAnalysis.GLTheoremA.CatA.FRLift
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs196
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.LocalAnalysis.GL83PartI.I_27_9_3.Component
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRMat
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bTools

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.MI
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs196 (ambiguousChev_lie_odd)
open scoped commutatorElement

section Lift


theorem t263CI_layer_ne_bot_of_core {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Ω : Type} [Group Ω] [Finite Ω]
    {S : Subgroup Ω} (hSp : GLAPPrimeCore p ↥S = ⊥) {b : Ω} (hb : b ∈ Subgroup.normalizer (S : Set Ω))
    (hbp : b ^ p = 1) {E : Subgroup (PSimple p S)} [IsSimpleGroup ↥E] (hEn : ∃ x y : ↥E, x * y ≠ y * x)
    (hEC : E ≤ FP.fixSub (indAut p S b hb))
    (hEnorm : ∀ c ∈ FP.fixSub (indAut p S b hb), ∀ x ∈ E, c * x * c⁻¹ ∈ E) (hpE : p ∣ Nat.card ↥E) :
    GLAPLayer p (S ⊓ Subgroup.centralizer ({b} : Set Ω)) ≠ ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set Xs : Subgroup ↥S := (S ⊓ Subgroup.centralizer ({b} : Set Ω)).subgroupOf S with hXs
  set Xb : Subgroup (PSimple p S) := Xs.map (chevQuotHom p S) with hXb
  have hX : FR.SubfieldGrp (indAut p S b hb) Xb := FR.fieldOn_lift hp hp2 hb hbp
  have hperfE : Group.IsPerfect ↥E :=
    Group.isPerfect_def.mpr (GL83.PiGen.isQuasisimple_of_simple_nonabelian hEn).1
  have hEperf : ⁅E, E⁆ = E := Subgroup.isPerfect_iff.1 hperfE
  have hEXb : E ≤ Xb :=
    calc E = ⁅E, E⁆ := hEperf.symm
      _ ≤ ⁅FP.fixSub (indAut p S b hb), FP.fixSub (indAut p S b hb)⁆ :=
        Subgroup.commutator_mono hEC hEC
      _ ≤ Xb := hX.2.1
  have hnormal : (E.subgroupOf Xb).Normal := by
    refine ⟨fun d hd x => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hd ⊢
    have hxC : (x : PSimple p S) ∈ FP.fixSub (indAut p S b hb) := hX.1 x.2
    simpa using hEnorm (x : PSimple p S) hxC (d : PSimple p S) hd
  have hcomp : GLAPComponent p Xb E := GL83.PiGen.glaPComponent_of_normal_simple hp hEXb hnormal hEn hpE
  have hlayer : GLAPLayer p Xb ≠ ⊥ := by
    intro h
    have hle : E ≤ GLAPLayer p Xb := by
      unfold GLAPLayer
      exact le_sSup hcomp
    rw [h, le_bot_iff] at hle
    obtain ⟨x, y, hxy⟩ := hEn
    have hx : x = 1 := Subtype.ext (by simpa using (hle ▸ x.2 : (x : PSimple p S) ∈ (⊥ : Subgroup _)))
    exact hxy (by rw [hx, one_mul, mul_one])
  have hcenter : ∀ y ∈ Xs ⊓ (chevQuotHom p S).ker, ∀ x ∈ Xs, x * y = y * x := by
    intro y hy x _
    have h1 : QuotientGroup.mk y = (1 : ↥S ⧸ Subgroup.center ↥S) := by
      rw [← pSimpleEquiv_chevQuotHom hSp y, MonoidHom.mem_ker.1 hy.2, map_one]
    exact (Subgroup.mem_center_iff.1 ((QuotientGroup.eq_one_iff y).1 h1) x)
  have hS : GLAPLayer p Xs ≠ ⊥ :=
    (CFSG.glaPLayer_ne_bot_iff_map_ne_bot hp (chevQuotHom p S) hcenter).2 hlayer
  have hinj : ∀ y ∈ Xs ⊓ S.subtype.ker, ∀ x ∈ Xs, x * y = y * x := by
    intro y hy x _
    have : y = 1 :=
      (MonoidHom.ker_eq_bot_iff _ |>.2 S.subtype_injective ▸ hy.2 : y ∈ (⊥ : Subgroup ↥S)) |> Subgroup.mem_bot.1
    rw [this, one_mul, mul_one]
  have hmap : Xs.map S.subtype = S ⊓ Subgroup.centralizer ({b} : Set Ω) :=
    Subgroup.map_subgroupOf_eq_of_le inf_le_left
  have := (CFSG.glaPLayer_ne_bot_iff_map_ne_bot hp S.subtype hinj).1 hS
  rwa [hmap] at this

theorem t263CI_layer_ne_bot_of_perfect_core {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Ω : Type} [Group Ω]
    [Finite Ω] {S : Subgroup Ω} (hSp : GLAPPrimeCore p ↥S = ⊥) {b : Ω}
    (hb : b ∈ Subgroup.normalizer (S : Set Ω)) (hbp : b ^ p = 1) {E : Subgroup (PSimple p S)}
    [IsSimpleGroup ↥E] (hEn : ∃ x y : ↥E, x * y ≠ y * x) (hEC : E ≤ FP.fixSub (indAut p S b hb))
    (hperf : ∀ T : Subgroup (PSimple p S), T ≤ FP.fixSub (indAut p S b hb) → ⁅T, T⁆ = T → T ≤ E)
    (hpE : p ∣ Nat.card ↥E) : GLAPLayer p (S ⊓ Subgroup.centralizer ({b} : Set Ω)) ≠ ⊥ := by
  have hEperf : ⁅E, E⁆ = E :=
    Subgroup.isPerfect_iff.1
      (Group.isPerfect_def.mpr (GL83.PiGen.isQuasisimple_of_simple_nonabelian hEn).1)
  refine t263CI_layer_ne_bot_of_core hp hp2 hSp hb hbp hEn hEC (fun c hc y hy => ?_) hpE
  have hle : E.map (MulAut.conj c).toMonoidHom ≤ E := by
    refine hperf _ ?_ (by rw [← Subgroup.map_commutator, hEperf])
    rintro _ ⟨z, hz, rfl⟩
    exact (FP.fixSub (indAut p S b hb)).mul_mem
      ((FP.fixSub (indAut p S b hb)).mul_mem hc (hEC hz)) ((FP.fixSub (indAut p S b hb)).inv_mem hc)
  exact hle ⟨y, hy, rfl⟩

end Lift

section NotChev


theorem t263CI_not_chev {S : Type} [Group S] [Finite S] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {α : MulAut S} (hαp : α ^ p = 1) (hαi : α ∉ (MulAut.conj : S →* MulAut S).range)
    (hchev : IsChevSimple 2 S)
    (hL8 : ∀ (q : TauCeti.PrimePower) (hd' : (TauCeti.LieTypeIndex.A 1 q).Valid), q.card = 8 →
      ¬ (p = 3 ∧ Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.A 1 q, hd'⟩).Group))) :
    ¬ IsChevSimple p S := by
  rintro (⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩)
  ·
    obtain ⟨d, hd, hd2, ⟨eS⟩⟩ := T2021.t2021Layer_exists_index hp hp2 hαp hαi hchev
    rcases i with ⟨_, _⟩ | ⟨_, _⟩ | ⟨d', hd'⟩ | _
    · exact hi.elim
    · exact hi.elim
    · exact hαi (T2021.t2021Layer_inner_of_crossChar hp hp2 hd2 eS hi e hαp)
    · exact hi.elim
  ·
    rcases i with ⟨_, _⟩ | ⟨n, hn⟩ | ⟨d', hd'⟩ | _
    · exact hi.elim
    · exact hαi (T2021.t2021Layer_inner_alt hp hp2 hn e hαp)
    · obtain ⟨rfl, ⟨q, hq, hq8⟩ | ⟨q, hq, hq2⟩⟩ := ambiguousChev_lie_odd hp2 hi
      · obtain rfl : d' = .A 1 q := hq
        exact hL8 q hd' hq8 ⟨rfl, ⟨e⟩⟩
      · obtain rfl : d' = .twistedA 3 q := hq
        exact hαi (T2021.t2021Layer_inner_u42 hp hp2 hq2 e hαp)
    · exact hi.elim

end NotChev

end CFSG.LocalAnalysis.GLTheoremA.T263

end
