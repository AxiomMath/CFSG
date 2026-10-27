module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceCommon
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.QuasithinUnique.Setup.Lift.PieceDel

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
open scoped commutatorElement

section ModComm

variable {G : Type} [Group G]

theorem modComm_le_V (V : Subgroup G) (A : Subgroup (MulAut V)) : modComm V A ≤ V := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g ⟨a, -, v, rfl⟩
  exact V.mul_mem (a v).2 (V.inv_mem v.2)

theorem modComm_eq_commutator {B V : Subgroup G} {Fs : Subgroup (MulAut V)}
    (hB : B ≤ Subgroup.normalizer (V : Set G)) (himg : autOn B V = Fs) :
    modComm V Fs = ⁅B, V⁆ := by
  rw [← himg]
  exact Piece.modComm_autOn hB

end ModComm

section ElemAbelian

variable {G : Type} [Group G]

theorem isElemAbelian_of_le {E V : Subgroup G} (hE : E ≤ V) (hV : IsElemAbelian 2 V) :
    IsElemAbelian 2 E := CFSG.Open.IsElemAbelian.mono hV hE

theorem le_omegaOneCenterOf_of_le {V Q : Subgroup G} (hVQ : V ≤ Q)
    (hQC : Q ≤ Subgroup.centralizer (V : Set G)) (hV2 : ∀ v ∈ V, v ^ 2 = 1) :
    V ≤ omegaOneCenterOf Q := by
  intro v hv
  refine Subgroup.subset_closure ⟨⟨hVQ hv, Subgroup.mem_centralizer_iff.2 fun q hq => ?_⟩, hV2 v hv⟩
  exact (Subgroup.mem_centralizer_iff.1 (hQC hq) v hv).symm

end ElemAbelian

section Closure

variable {G : Type} [Group G]

theorem self_le_conjJoin (R B : Subgroup G) : B ≤ conjJoin R B := fun y hy =>
  Subgroup.mem_iSup_of_mem (⟨1, R.one_mem⟩ : R) ⟨y, hy, by simp⟩

theorem le_normalizer_conjJoin_self (R B : Subgroup G) :
    R ≤ Subgroup.normalizer (conjJoin R B : Set G) := by
  have key : ∀ s ∈ R, ∀ y ∈ conjJoin R B, s * y * s⁻¹ ∈ conjJoin R B := by
    intro s hs y hy
    refine Subgroup.iSup_induction (fun s' : R => B.map (MulAut.conj (s' : G)).toMonoidHom)
      (C := fun y => s * y * s⁻¹ ∈ conjJoin R B) hy ?_ ?_ ?_
    · rintro ⟨s', hs'⟩ y ⟨x, hx, rfl⟩
      have e : s * ((MulAut.conj s').toMonoidHom x) * s⁻¹ =
          (MulAut.conj (s * s')).toMonoidHom x := by
        simp [MulAut.conj_apply, mul_assoc]
      rw [e]
      exact Subgroup.mem_iSup_of_mem (⟨s * s', R.mul_mem hs hs'⟩ : R) ⟨x, hx, rfl⟩
    · simp
    · intro a b ha hb
      have e : s * (a * b) * s⁻¹ = (s * a * s⁻¹) * (s * b * s⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ ha hb
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro y
  exact ⟨fun h => key s hs y h, fun h => by simpa [mul_assoc] using key s⁻¹ (R.inv_mem hs) _ h⟩

theorem commutator_le_of_le_conjJoin {Q N B R L : Subgroup G} [hQ : Q.Normal] [hN : N.Normal]
    (hB : ⁅Q, B⁆ ≤ N) (hL : L ≤ conjJoin R B) : ⁅Q, L⁆ ≤ N := by
  classical
  let π : G →* G ⧸ N := QuotientGroup.mk' N
  have hQmap : (Q.map π).Normal := hQ.map π (QuotientGroup.mk'_surjective N)
  let Y : Subgroup G :=
    (Subgroup.centralizer ((Q.map π : Subgroup (G ⧸ N)) : Set (G ⧸ N))).comap π
  have hYn : Y.Normal := Subgroup.Normal.comap Subgroup.normal_centralizer π
  have hcomm (q h : G) : ⁅q, h⁆ ∈ N ↔ π q * π h = π h * π q := by
    rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).symm
  have hmem (h : G) : h ∈ Y ↔ ∀ q ∈ Q, ⁅q, h⁆ ∈ N := by
    change π h ∈ Subgroup.centralizer _ ↔ _
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro hh q hq
      exact (hcomm q h).mpr (hh (π q) ⟨q, hq, rfl⟩)
    · rintro hh _ ⟨q, hq, rfl⟩
      exact (hcomm q h).mp (hh q hq)
  have hBY : B ≤ Y := fun b hb =>
    (hmem b).2 fun q hq => hB (Subgroup.commutator_mem_commutator hq hb)
  have hconj : conjJoin R B ≤ Y := iSup_le fun s => by
    rintro _ ⟨b, hb, rfl⟩
    exact hYn.conj_mem b (hBY hb) (s : G)
  rw [Subgroup.commutator_le]
  intro q hq l hl
  exact (hmem l).1 (hconj (hL hl)) q hq

end Closure

section Seed

open scoped Pointwise

variable {A : Type} [Group A]

theorem pow_mem_of_eq_mul_mem {Y N : Subgroup A} (hN : (N.subgroupOf Y).Normal) {x z f : A}
    (hx : x ∈ Y) (hz : z ∈ Y) (hf : f ∈ N) (hxzf : x = z * f) {k : ℕ} (hzk : z ^ k = 1) :
    x ^ k ∈ N := by
  have hfY : f ∈ Y := by
    have : f = z⁻¹ * x := by rw [hxzf]; group
    rw [this]
    exact Y.mul_mem (Y.inv_mem hz) hx
  have h1 : (QuotientGroup.mk (⟨f, hfY⟩ : Y) : Y ⧸ N.subgroupOf Y) = 1 :=
    (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hf)
  have hmul : (⟨x, hx⟩ : Y) = ⟨z, hz⟩ * ⟨f, hfY⟩ := Subtype.ext hxzf
  have hz1 : (⟨z, hz⟩ : Y) ^ k = 1 := Subtype.ext (by simpa using hzk)
  have h2 : (QuotientGroup.mk (⟨x, hx⟩ : Y) : Y ⧸ N.subgroupOf Y) ^ k = 1 := by
    rw [hmul, QuotientGroup.mk_mul, h1, mul_one, ← QuotientGroup.mk_pow, hz1]
    rfl
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h2
  simpa using Subgroup.mem_subgroupOf.1 h2

theorem oddOrderSubgroup_sup_seed {Fs D : Subgroup A} (hF3 : Nat.card Fs = 3)
    (hD : IsPGroup 2 D) (hn : D ≤ Subgroup.normalizer (Fs : Set A)) :
    oddOrderSubgroup (Fs ⊔ D) = Fs := by
  classical
  have hnF : Fs ⊔ D ≤ Subgroup.normalizer (Fs : Set A) := sup_le Subgroup.le_normalizer hn
  have hnorm : (Fs.subgroupOf (Fs ⊔ D)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 hnF
  apply le_antisymm
  · refine oddOrderSubgroup_le_of_pow_mem fun h hh => ?_
    have hset : ((D ⊔ Fs : Subgroup A) : Set A) = (D : Set A) * (Fs : Set A) :=
      Subgroup.coe_mul_of_left_le_normalizer_right D Fs hn
    have hh' : h ∈ ((D ⊔ Fs : Subgroup A) : Set A) := by
      rw [SetLike.mem_coe, sup_comm]
      exact hh
    rw [hset] at hh'
    obtain ⟨d, hd, f, hf, rfl⟩ := hh'
    obtain ⟨k, hk⟩ := hD ⟨d, hd⟩
    have hdk : d ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    exact ⟨k, pow_mem_of_eq_mul_mem hnorm hh (Subgroup.mem_sup_right hd) hf rfl hdk⟩
  · intro x hx
    refine Subgroup.subset_closure ⟨Subgroup.mem_sup_left hx, ?_⟩
    have h3 : orderOf x ∣ 3 := hF3 ▸ Subgroup.orderOf_dvd_natCard Fs hx
    exact Odd.of_dvd_nat (⟨1, by norm_num⟩ : Odd 3) h3

end Seed

section Fixed

variable {G : Type} [Group G]

theorem eq_one_of_mem_modComm_of_fixed {V : Subgroup G}
    (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hV2 : ∀ a ∈ V, a ^ 2 = 1)
    {Fs : Subgroup (MulAut V)} (hF3 : Nat.card Fs = 3) {w : G} (hw : w ∈ modComm V Fs)
    (hwV : w ∈ V) (hfix : ∀ a ∈ Fs, ((a ⟨w, hwV⟩ : V) : G) = w) : w = 1 := by
  classical
  have hfin : Finite Fs := Nat.finite_of_card_ne_zero (by rw [hF3]; norm_num)
  let _ : Fintype Fs := Fintype.ofFinite Fs
  let _instCG : CommGroup V :=
    { (inferInstance : Group V) with mul_comm := fun a b => Subtype.ext (hVc a a.2 b b.2) }
  let N : V →* V :=
    { toFun := fun x => ∏ a : Fs, (a : MulAut V) x
      map_one' := by simp
      map_mul' := fun x y => by simp [Finset.prod_mul_distrib] }
  have hNa : ∀ a : Fs, ∀ x : V, N ((a : MulAut V) x) = N x := by
    intro a x
    show ∏ b : Fs, (b : MulAut V) ((a : MulAut V) x) = ∏ b : Fs, (b : MulAut V) x
    exact Fintype.prod_equiv (Equiv.mulRight a) _ _ fun b => rfl
  have hker : modComm V Fs ≤ (N.ker).map V.subtype := by
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨a, ha, v, rfl⟩
    refine ⟨(a : MulAut V) v * v⁻¹, ?_, by simp⟩
    show N ((a : MulAut V) v * v⁻¹) = 1
    rw [map_mul, map_inv, hNa ⟨a, ha⟩ v, mul_inv_cancel]
  obtain ⟨wt, hwt, hwtw⟩ := hker hw
  have hwt' : wt = ⟨w, hwV⟩ := Subtype.ext hwtw
  have hN1 : N wt = 1 := hwt
  have hNw : N wt = wt ^ 3 := by
    show ∏ a : Fs, (a : MulAut V) wt = wt ^ 3
    have : ∀ a : Fs, (a : MulAut V) wt = wt := fun a =>
      Subtype.ext (by rw [hwt']; exact hfix a a.2)
    rw [Finset.prod_congr rfl (fun a _ => this a), Finset.prod_const, Finset.card_univ,
      Fintype.card_eq_nat_card, hF3]
  have hwt2 : wt ^ 2 = 1 := Subtype.ext (by simpa [hwt'] using hV2 w hwV)
  have h3 : wt ^ 3 = wt := by rw [pow_succ, hwt2, one_mul]
  have : wt = 1 := by rw [← h3, ← hNw, hN1]
  rw [← hwtw, this]
  rfl

end Fixed

section Normal

variable {G : Type} [Group G]

theorem normal_Q {R : Subgroup G}
    (hLS : (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R).Normal) :
    (pCoreOf 2 (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R)).Normal := by
  have h1 := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2
    (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R)
  rw [Subgroup.normalizer_eq_top_iff.mpr hLS] at h1
  exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp h1)

end Normal

end CFSG.QuasithinUnique.Setup.Lift.PieceDel
