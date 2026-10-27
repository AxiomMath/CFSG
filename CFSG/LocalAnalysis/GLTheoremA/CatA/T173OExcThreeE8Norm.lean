module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OExcThreeE8Data
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OExcThreeE8Frame
public import CFSG.LocalAnalysis.ComponentClassification.GS82HConfigNorm
import all CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBTorus

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType
open CFSG.StandardType.TableBExcTwo CFSG.StandardType.TableBExcTwoTB
open CFSG.SeitzReduction.E8Pilot CFSG.SeitzReduction.EPilot CFSG.SeitzReduction
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.ComponentClassification.GSThmB.HConfig

section FrameNorm


variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem frameE8Root_succ_highNode :
    ∀ i : Fin 7, frameE8Root i.succ (highNode .E8) = 0 := by
  decide +kernel

private theorem nW_mem_subsystemGroup_of_le (w : List (Fin Tag.E8.rank))
    (hw : ∀ i ∈ w, i.val ≤ 6) : nW .E8 K w ∈ subsystemGroup .E8 K (perpNodes .E8) := by
  induction w with
  | nil => simp [nW]
  | cons i w ih =>
      rw [nW_cons]
      refine mul_mem (weylElt_mem_subsystemGroup ?_ (1 : Kˣ)) (ih ?_)
      · simp only [perpNodes, Set.mem_setOf_eq, highNode]
        intro h
        have hle := hw i (by simp)
        rw [h] at hle
        norm_num at hle
      · intro j hj
        exact hw j (by simp [hj])

private theorem e8SingerPerm_bijective : Function.Bijective e8SingerPerm := by
  have hleft : ∀ j, e8SingerPerm^[6] (e8SingerPerm j) = j := by
    intro j
    have h := e8SingerPerm_iterate_seven j
    rwa [show (7 : ℕ) = 6 + 1 from rfl, Function.iterate_succ_apply] at h
  have hright : ∀ j, e8SingerPerm (e8SingerPerm^[6] j) = j := by
    intro j
    have h := e8SingerPerm_iterate_seven j
    rwa [show (7 : ℕ) = 6 + 1 from rfl, Function.iterate_succ_apply'] at h
  refine ⟨fun a b h => ?_, fun j => ⟨e8SingerPerm^[6] j, hright j⟩⟩
  have := congrArg (e8SingerPerm^[6]) h
  rwa [hleft, hleft] at this

private noncomputable def e8SingerPermEquiv : Fin 8 ≃ Fin 8 :=
  Equiv.ofBijective e8SingerPerm e8SingerPerm_bijective

theorem nGen_succ_mem_e7Levi (i : Fin 7) : nGen K frameE8 i.succ ∈ e7Levi K := by
  rw [mem_e7Levi_iff]
  have hpos : frameE8Root i.succ ∈ perpRoots .E8 :=
    ⟨frameE8.isRoot i.succ, frameE8Root_succ_highNode i⟩
  have hneg : -frameE8Root i.succ ∈ perpRoots .E8 :=
    ⟨IsRoot.neg hpos.1, by simp [hpos.2]⟩
  have hsub : ({frameE8Root i.succ, -frameE8Root i.succ} : Set (Fin Tag.E8.rank → ℤ)) ⊆
      perpRoots .E8 := by
    intro α hα
    rcases hα with rfl | rfl
    · exact hpos
    · exact hneg
  have h := rootSpan_mono hsub
    (rootSL2_mem_rootSpan_pair (τ := .E8) (L := K) (frameE8.isRoot i.succ) WSL)
  change ((rho K frameE8 i.succ WSL : adjointGroup .E8 K) : ModGL .E8 K) ∈
    rootSpan .E8 K (perpRoots .E8)
  rwa [coe_rho]

theorem nWA_e8SingerWord_mem_e7Levi : nWA .E8 K e8SingerWord ∈ e7Levi K := by
  rw [mem_e7Levi_iff,
    ← parabolicRoots_perpNodes (τ := .E8),
    ← subsystemGroup_eq_rootSpan (τ := .E8) (K := K) (J := perpNodes .E8)]
  change nW .E8 K e8SingerWord ∈ subsystemGroup .E8 K (perpNodes .E8)
  exact nW_mem_subsystemGroup_of_le (K := K) e8SingerWord e8SingerWord_le

theorem map_conj_nGen_succ_e8FrameV (i : Fin 7) :
    (e8FrameV K).map (MulAut.conj (nGen K frameE8 i.succ)).toMonoidHom = e8FrameV K := by
  haveI : Finite ↥(adjointGroup .E8 K) := generated_group_finite .E8 K
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [mem_e8FrameV_iff] at hy
    obtain ⟨v, hv0, rfl⟩ := hy
    rw [mem_e8FrameV_iff]
    refine ⟨v - reflCoeff i.succ v • Pi.single i.succ 1, ?_, ?_⟩
    · rw [reflVec_apply_of_ne (Fin.succ_ne_zero i).symm, hv0]
    · show (MulAut.conj (nGen K frameE8 i.succ))
          (tE K frameE8 (Multiplicative.ofAdd v)) = _
      rw [MulAut.conj_apply]
      exact nGen_conj_tE frameE8 i.succ v
  · rw [Subgroup.card_map_of_injective
      (f := (MulAut.conj (nGen K frameE8 i.succ)).toMonoidHom)
      (MulAut.conj (nGen K frameE8 i.succ)).injective, card_e8FrameV]


private theorem tC_commute_singer (v k : Fin 8 → ZMod 3) :
    ((Finset.univ : Finset (Fin 8)) : Set (Fin 8)).Pairwise
      (Function.onFun Commute fun a =>
        tC K frameE8 (e8SingerPerm a) (Multiplicative.ofAdd (v a * k a))) :=
  fun a _ b _ hab =>
    tC_commute frameE8 (fun h => hab (e8SingerPerm_bijective.injective h)) _ _

private theorem tC_commute_singerEquiv (u : Fin 8 → ZMod 3) :
    ((Finset.univ : Finset (Fin 8)) : Set (Fin 8)).Pairwise
      (Function.onFun Commute fun a =>
        tC K frameE8 (e8SingerPermEquiv a) (Multiplicative.ofAdd (u (e8SingerPermEquiv a)))) :=
  fun a _ b _ hab =>
    tC_commute frameE8 (fun h => hab (e8SingerPermEquiv.injective h)) _ _

private theorem exists_conj_tE_of_coordAction (n : adjointGroup .E8 K) (v : Fin 8 → ZMod 3)
    (k : Fin 8 → ZMod 3) (hk0 : ∀ a, k a ≠ 0)
    (hk : ∀ a, n * tC K frameE8 a (Multiplicative.ofAdd (v a)) * n⁻¹ =
      tC K frameE8 (e8SingerPerm a) (Multiplicative.ofAdd (v a * k a))) :
    (∀ j, k j * v j ≠ 0 ↔ v j ≠ 0) ∧
      n * tE K frameE8 (Multiplicative.ofAdd v) * n⁻¹ =
        tE K frameE8 (Multiplicative.ofAdd fun j =>
          k (e8SingerPermEquiv.symm j) * v (e8SingerPermEquiv.symm j)) := by
  classical
  let σ : Fin 8 ≃ Fin 8 := e8SingerPermEquiv
  let u : Fin 8 → ZMod 3 := fun j => k (σ.symm j) * v (σ.symm j)
  have hu : ∀ j, u (e8SingerPerm j) = k j * v j := by
    intro j
    change k (σ.symm (σ j)) * v (σ.symm (σ j)) = k j * v j
    rw [Equiv.symm_apply_apply]
  refine ⟨?_, ?_⟩
  · intro j
    exact mul_ne_zero_iff.trans (and_iff_right (hk0 j))
  · change n * tE K frameE8 (Multiplicative.ofAdd v) * n⁻¹ =
      tE K frameE8 (Multiplicative.ofAdd u)
    rw [tE_apply, tE_apply, ← MulAut.conj_apply]
    unfold tD
    rw [MonoidHom.noncommPiCoprod_apply, MonoidHom.noncommPiCoprod_apply,
      Finset.map_noncommProd]
    have hcomm₁ : ((Finset.univ : Finset (Fin 8)) : Set (Fin 8)).Pairwise
        (Function.onFun Commute fun a =>
          (MulAut.conj n) (tC K frameE8 a (Multiplicative.ofAdd (v a)))) :=
      fun a _ b _ hab => (tC_commute frameE8 hab _ _).map (MulAut.conj n).toMonoidHom
    have hcomm₂ := tC_commute_singer (K := K) v k
    have hcomm₃ : ((Finset.univ : Finset (Fin 8)) : Set (Fin 8)).Pairwise
        (Function.onFun Commute fun j => tC K frameE8 j (Multiplicative.ofAdd (u j))) :=
      fun a _ b _ hab => tC_commute frameE8 hab _ _
    have h1 : Finset.univ.noncommProd
          (fun a => (MulAut.conj n) (tC K frameE8 a (Multiplicative.ofAdd (v a)))) hcomm₁ =
        Finset.univ.noncommProd
          (fun a => tC K frameE8 (e8SingerPerm a) (Multiplicative.ofAdd (v a * k a))) hcomm₂ := by
      refine Finset.noncommProd_congr rfl (fun a _ => ?_) hcomm₁
      rw [MulAut.conj_apply]
      exact hk a
    have hcomm₂' := tC_commute_singerEquiv (K := K) u
    have h2a : Finset.univ.noncommProd
          (fun a => tC K frameE8 (e8SingerPerm a) (Multiplicative.ofAdd (v a * k a))) hcomm₂ =
        Finset.univ.noncommProd
          (fun a => tC K frameE8 (σ a) (Multiplicative.ofAdd (u (σ a)))) hcomm₂' := by
      refine Finset.noncommProd_congr rfl (fun a _ => ?_) hcomm₂
      congr 2
      simp only [u, σ, Equiv.symm_apply_apply, mul_comm]
    have h2b : Finset.univ.noncommProd
          (fun a => tC K frameE8 (σ a) (Multiplicative.ofAdd (u (σ a)))) hcomm₂' =
        Finset.univ.noncommProd
          (fun j => tC K frameE8 j (Multiplicative.ofAdd (u j))) hcomm₃ :=
      noncommProd_univ_comp_equiv σ
        (fun j => tC K frameE8 j (Multiplicative.ofAdd (u j))) hcomm₃ hcomm₂'
    rw [h1, h2a, h2b]

theorem exists_conj_tE_support_e8SingerPerm (hK : Nat.card K = 2) (v : Fin 8 → ZMod 3) :
    ∃ u : Fin 8 → ZMod 3, (∀ j, (u (e8SingerPerm j) ≠ 0 ↔ v j ≠ 0)) ∧
      nWA .E8 K e8SingerWord * tE K frameE8 (Multiplicative.ofAdd v) *
          (nWA .E8 K e8SingerWord)⁻¹ = tE K frameE8 (Multiplicative.ofAdd u) := by
  classical
  let n : adjointGroup .E8 K := nWA .E8 K e8SingerWord
  have hperm : PermutesFrame frameE8 e8SingerWord e8SingerPerm := fun a => e8SingerPerm_root a
  choose k hk0 hk using fun a => conj_nWA_tC hK frameE8 hperm a
  have hk' : ∀ a, n * tC K frameE8 a (Multiplicative.ofAdd (v a)) * n⁻¹ =
      tC K frameE8 (e8SingerPerm a) (Multiplicative.ofAdd (v a * k a)) := fun a => hk a _
  obtain ⟨hsupp, hconj⟩ := exists_conj_tE_of_coordAction n v k hk0 hk'
  refine ⟨_, ?_, hconj⟩
  intro j
  have hsymm : e8SingerPermEquiv.symm (e8SingerPerm j) = j := by
    change e8SingerPermEquiv.symm (e8SingerPermEquiv j) = j
    exact Equiv.symm_apply_apply _ _
  change k (e8SingerPermEquiv.symm (e8SingerPerm j)) *
    v (e8SingerPermEquiv.symm (e8SingerPerm j)) ≠ 0 ↔ v j ≠ 0
  rw [hsymm]
  exact hsupp j

theorem map_conj_nWA_e8SingerWord_e8FrameV (hK : Nat.card K = 2) :
    (e8FrameV K).map (MulAut.conj (nWA .E8 K e8SingerWord)).toMonoidHom = e8FrameV K := by
  haveI : Finite ↥(adjointGroup .E8 K) := generated_group_finite .E8 K
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [mem_e8FrameV_iff] at hy
    obtain ⟨v, hv0, rfl⟩ := hy
    obtain ⟨u, hu, hconj⟩ := exists_conj_tE_support_e8SingerPerm hK v
    rw [mem_e8FrameV_iff]
    refine ⟨u, ?_, ?_⟩
    · have hπ0 : e8SingerPerm 0 = 0 := rfl
      have h0 : ¬ u 0 ≠ 0 := by
        rw [← hπ0]
        exact fun h => (hu 0).mp h hv0
      simpa using h0
    · show (MulAut.conj (nWA .E8 K e8SingerWord)) (tE K frameE8 (Multiplicative.ofAdd v)) = _
      rw [MulAut.conj_apply]
      exact hconj
  · rw [Subgroup.card_map_of_injective
      (f := (MulAut.conj (nWA .E8 K e8SingerWord)).toMonoidHom)
      (MulAut.conj (nWA .E8 K e8SingerWord)).injective, card_e8FrameV]


private theorem zmod3_eq_zero_or_one_or_two (a : ZMod 3) : a = 0 ∨ a = 1 ∨ a = 2 := by
  have h : ∀ b : ZMod 3, b = 0 ∨ b = 1 ∨ b = 2 := by decide +kernel
  exact h a

private theorem nGenProd_comm (S : Finset (Fin 8)) :
    (S : Set (Fin 8)).Pairwise (Function.onFun Commute fun i => rho K frameE8 i WSL) :=
  fun i _ j _ hij => commute_rho frameE8 hij WSL WSL

private noncomputable def nGenProd (S : Finset (Fin 8)) : adjointGroup .E8 K :=
  S.noncommProd (fun i => rho K frameE8 i WSL) (nGenProd_comm S)

private theorem nGenProd_empty : nGenProd (K := K) ∅ = 1 := by
  rw [nGenProd, Finset.noncommProd_empty]

private theorem nGenProd_insert {a : Fin 8} {S : Finset (Fin 8)} (ha : a ∉ S) :
    nGenProd (K := K) (insert a S) = nGen K frameE8 a * nGenProd (K := K) S := by
  rw [nGenProd, Finset.noncommProd_insert_of_notMem _ _ _ _ ha]
  rfl

private theorem nGen_conj_tE_of_ne_zero {a : Fin 8} (ha : a ≠ 0) (v : Fin 8 → ZMod 3) :
    nGen K frameE8 a * tE K frameE8 (Multiplicative.ofAdd v) * (nGen K frameE8 a)⁻¹ =
      tE K frameE8 (Multiplicative.ofAdd fun j => if j = a then -v j else v j) := by
  obtain ⟨i, rfl⟩ := Fin.exists_succ_eq_of_ne_zero ha
  rw [nGen_conj_tE]
  congr 2
  funext j
  by_cases hj : j = i.succ
  · subst hj
    rw [reflVec_apply_self, if_pos rfl]
    rfl
  · rw [reflVec_apply_of_ne hj, if_neg hj]

private theorem conj_nGenProd_tE (S : Finset (Fin 8)) :
    ∀ v : Fin 8 → ZMod 3, (0 : Fin 8) ∉ S →
      nGenProd (K := K) S * tE K frameE8 (Multiplicative.ofAdd v) *
          (nGenProd (K := K) S)⁻¹ =
        tE K frameE8 (Multiplicative.ofAdd fun j => if j ∈ S then -v j else v j) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      intro v _
      rw [nGenProd_empty, one_mul, inv_one, mul_one]
      refine congrArg (tE K frameE8) ?_
      refine congrArg Multiplicative.ofAdd ?_
      funext j
      simp
  | insert a S ha ih =>
      intro v h0
      have h0S : (0 : Fin 8) ∉ S := fun h => h0 (Finset.mem_insert_of_mem h)
      have ha0 : a ≠ 0 := fun h => h0 (h ▸ Finset.mem_insert_self a S)
      rw [nGenProd_insert ha]
      calc (nGen K frameE8 a * nGenProd (K := K) S) *
            tE K frameE8 (Multiplicative.ofAdd v) *
            (nGen K frameE8 a * nGenProd (K := K) S)⁻¹
          = nGen K frameE8 a *
              (nGenProd (K := K) S * tE K frameE8 (Multiplicative.ofAdd v) *
                (nGenProd (K := K) S)⁻¹) * (nGen K frameE8 a)⁻¹ := by group
        _ = nGen K frameE8 a *
              tE K frameE8 (Multiplicative.ofAdd fun j => if j ∈ S then -v j else v j) *
              (nGen K frameE8 a)⁻¹ := by rw [ih v h0S]
        _ = tE K frameE8 (Multiplicative.ofAdd fun j =>
              if j = a then -(if j ∈ S then -v j else v j)
                else (if j ∈ S then -v j else v j)) :=
              nGen_conj_tE_of_ne_zero ha0 _
        _ = tE K frameE8 (Multiplicative.ofAdd fun j =>
              if j ∈ insert a S then -v j else v j) := by
              refine congrArg (tE K frameE8) ?_
              refine congrArg Multiplicative.ofAdd ?_
              funext j
              by_cases hja : j = a
              · subst hja
                simp [ha]
              · simp [hja, Finset.mem_insert, hja]

private theorem map_conj_nGenProd_e8FrameV (S : Finset (Fin 8))
    (hS : ∀ i ∈ S, i ≠ 0) :
    (e8FrameV K).map (MulAut.conj (nGenProd (K := K) S)).toMonoidHom = e8FrameV K := by
  classical
  rw [nGenProd]
  refine Finset.noncommProd_induction S (fun i => rho K frameE8 i WSL) _
    (fun x => (e8FrameV K).map (MulAut.conj x).toMonoidHom = e8FrameV K)
    (fun a b ha hb => ?_) ?_ ?_
  · rw [map_conj_mul, hb, ha]
  · have h : (MulAut.conj (1 : adjointGroup .E8 K)).toMonoidHom = MonoidHom.id _ := by
      ext x
      simp [MulAut.conj_apply]
    rw [h, Subgroup.map_id]
  · intro i hi
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq_of_ne_zero (hS i hi)
    exact map_conj_nGen_succ_e8FrameV j

private theorem nGenProd_mem_e7Levi (S : Finset (Fin 8)) (hS : ∀ i ∈ S, i ≠ 0) :
    nGenProd (K := K) S ∈ e7Levi K := by
  classical
  rw [nGenProd]
  refine Finset.noncommProd_induction S (fun i => rho K frameE8 i WSL) _
    (fun x => x ∈ e7Levi K)
    (fun a b ha hb => mul_mem ha hb) (one_mem _) (fun i hi => ?_)
  obtain ⟨j, rfl⟩ := Fin.exists_succ_eq_of_ne_zero (hS i hi)
  exact nGen_succ_mem_e7Levi j

theorem exists_conj_tE_eq_indicator {v : Fin 8 → ZMod 3} (hv0 : v 0 = 0) :
    ∃ n ∈ e7Levi K, (e8FrameV K).map (MulAut.conj n).toMonoidHom = e8FrameV K ∧
      n * tE K frameE8 (Multiplicative.ofAdd v) * n⁻¹ =
        tE K frameE8 (Multiplicative.ofAdd fun i => if v i = 0 then 0 else 1) := by
  classical
  let S : Finset (Fin 8) := (Finset.univ.filter (fun i => v i = 2)).erase 0
  have h0 : (0 : Fin 8) ∉ S := Finset.notMem_erase 0 _
  have hS : ∀ i ∈ S, i ≠ 0 := fun _ hi => Finset.ne_of_mem_erase hi
  refine ⟨nGenProd (K := K) S, nGenProd_mem_e7Levi S hS,
    map_conj_nGenProd_e8FrameV S hS, ?_⟩
  have hconj := conj_nGenProd_tE (K := K) S v h0
  rw [hconj]
  refine congrArg (tE K frameE8) ?_
  refine congrArg Multiplicative.ofAdd ?_
  funext j
  by_cases hj : j ∈ S
  · have hv2 : v j = 2 := by
      have hmem := Finset.mem_of_mem_erase hj
      simpa using hmem
    rw [if_pos hj, hv2]
    decide
  · by_cases hj0 : j = 0
    · subst hj0
      simp [S, hv0]
    · have hmem : j ∉ Finset.univ.filter (fun i => v i = 2) := by
        intro h
        exact hj (Finset.mem_erase.mpr ⟨hj0, h⟩)
      have hv2 : v j ≠ 2 := by simpa using hmem
      rw [if_neg hj]
      rcases zmod3_eq_zero_or_one_or_two (v j) with h | h | h
      · simp [h]
      · simp [h]
      · exact absurd h hv2

private theorem exists_conj_tE_support_iterate (hK : Nat.card K = 2) (v : Fin 8 → ZMod 3) :
    ∀ k : ℕ, ∃ u : Fin 8 → ZMod 3,
      (∀ j, u (e8SingerPerm^[k] j) ≠ 0 ↔ v j ≠ 0) ∧
      (nWA .E8 K e8SingerWord) ^ k * tE K frameE8 (Multiplicative.ofAdd v) *
          ((nWA .E8 K e8SingerWord) ^ k)⁻¹ =
        tE K frameE8 (Multiplicative.ofAdd u) := by
  intro k
  induction k with
  | zero =>
      refine ⟨v, ?_, ?_⟩
      · intro j
        rw [Function.iterate_zero_apply]
      · rw [pow_zero, one_mul, inv_one, mul_one]
  | succ k ih =>
      obtain ⟨u, hu, hconj⟩ := ih
      obtain ⟨u', hu', hconj'⟩ := exists_conj_tE_support_e8SingerPerm hK u
      refine ⟨u', ?_, ?_⟩
      · intro j
        rw [Function.iterate_succ_apply']
        exact (hu' (e8SingerPerm^[k] j)).trans (hu j)
      · calc (nWA .E8 K e8SingerWord) ^ (k + 1) *
              tE K frameE8 (Multiplicative.ofAdd v) *
              ((nWA .E8 K e8SingerWord) ^ (k + 1))⁻¹
            = nWA .E8 K e8SingerWord *
                ((nWA .E8 K e8SingerWord) ^ k * tE K frameE8 (Multiplicative.ofAdd v) *
                  ((nWA .E8 K e8SingerWord) ^ k)⁻¹) *
                (nWA .E8 K e8SingerWord)⁻¹ := by
                rw [pow_succ']; group
          _ = nWA .E8 K e8SingerWord * tE K frameE8 (Multiplicative.ofAdd u) *
                (nWA .E8 K e8SingerWord)⁻¹ := by rw [hconj]
          _ = tE K frameE8 (Multiplicative.ofAdd u') := hconj'

private theorem map_conj_pow_nWA_e8FrameV (hK : Nat.card K = 2) (k : ℕ) :
    (e8FrameV K).map (MulAut.conj ((nWA .E8 K e8SingerWord) ^ k)).toMonoidHom =
      e8FrameV K := by
  induction k with
  | zero =>
      rw [pow_zero]
      have h : (MulAut.conj (1 : adjointGroup .E8 K)).toMonoidHom = MonoidHom.id _ := by
        ext x
        simp [MulAut.conj_apply]
      rw [h, Subgroup.map_id]
  | succ k ih =>
      rw [pow_succ, map_conj_mul, map_conj_nWA_e8SingerWord_e8FrameV hK, ih]

theorem exists_conj_tE_mem_e8FrameReps (hK : Nat.card K = 2) {v : Fin 8 → ZMod 3}
    (hv0 : v 0 = 0) (hv : v ≠ 0) :
    ∃ n ∈ e7Levi K, (e8FrameV K).map (MulAut.conj n).toMonoidHom = e8FrameV K ∧
      ∃ r ∈ e8FrameReps, n * tE K frameE8 (Multiplicative.ofAdd v) * n⁻¹ =
        tE K frameE8 (Multiplicative.ofAdd r) := by
  classical
  let u : Fin 8 → Bool := fun j => decide (v j ≠ 0)
  have hu0 : u 0 = false := by simp [u, hv0]
  have hune : u ≠ (fun _ => false) := by
    intro h
    apply hv
    funext j
    have hj : u j = false := congrFun h j
    simpa [u] using hj
  obtain ⟨k, -, r, hr, -, hr01, hsupp⟩ := exists_e8SingerPerm_iterate_reps u hu0 hune
  obtain ⟨u', hu', hconj'⟩ := exists_conj_tE_support_iterate hK v k
  have hbij : Function.Bijective (e8SingerPerm^[k]) := e8SingerPerm_bijective.iterate k
  have hsupp' : ∀ y, u' y ≠ 0 ↔ r y ≠ 0 := by
    intro y
    obtain ⟨j, rfl⟩ := hbij.surjective y
    have huj : u j = true ↔ v j ≠ 0 := by simp [u]
    exact (hu' j).trans (huj.symm.trans (hsupp j))
  have hind : (fun i => if u' i = 0 then 0 else 1) = r := by
    funext y
    by_cases hy : u' y = 0
    · have hry : r y = 0 := by
        by_contra hne
        exact (hsupp' y).mpr hne hy
      simp [hy, hry]
    · have hry : r y ≠ 0 := (hsupp' y).mp hy
      have hr1 : r y = 1 := by
        rcases hr01 y with h | h
        · exact absurd h hry
        · exact h
      simp [hy, hr1]
  have hπ0 : e8SingerPerm^[k] 0 = 0 := Function.iterate_fixed (by rfl) k
  have hu'0 : u' 0 = 0 := by
    have h0 : ¬ u' 0 ≠ 0 := by
      rw [← hπ0]
      exact fun h => (hu' 0).mp h hv0
    simpa using h0
  obtain ⟨n6, hn6D, hn6V, hn6conj⟩ := exists_conj_tE_eq_indicator (K := K) hu'0
  refine ⟨n6 * (nWA .E8 K e8SingerWord) ^ k, ?_, ?_, ⟨r, hr, ?_⟩⟩
  · exact mul_mem hn6D (pow_mem nWA_e8SingerWord_mem_e7Levi k)
  · rw [map_conj_mul, map_conj_pow_nWA_e8FrameV hK, hn6V]
  · calc (n6 * (nWA .E8 K e8SingerWord) ^ k) * tE K frameE8 (Multiplicative.ofAdd v) *
          (n6 * (nWA .E8 K e8SingerWord) ^ k)⁻¹
        = n6 * ((nWA .E8 K e8SingerWord) ^ k * tE K frameE8 (Multiplicative.ofAdd v) *
            ((nWA .E8 K e8SingerWord) ^ k)⁻¹) * n6⁻¹ := by group
      _ = n6 * tE K frameE8 (Multiplicative.ofAdd u') * n6⁻¹ := by rw [hconj']
      _ = tE K frameE8 (Multiplicative.ofAdd fun i => if u' i = 0 then 0 else 1) := hn6conj
      _ = tE K frameE8 (Multiplicative.ofAdd r) := by rw [hind]

end FrameNorm

end CFSG.LocalAnalysis.GLTheoremA.T173O

end