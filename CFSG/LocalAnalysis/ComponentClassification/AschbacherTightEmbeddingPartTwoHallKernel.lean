module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoHallNormalizer
public import CFSG.Adapters.QiuzhenLegacy.FeitThompson.GroupAction.Quotient

public section

namespace CFSG.ComponentClassification.AschbacherTightEmbedding

open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

theorem hall_conjugacy_by_normal_kernel (K : Subgroup G) [K.Normal]
    (hsolv : Group.IsSolvable G) (π : Set Nat.Primes) (D : Subgroup G)
    (hHall : CFSG.IsHallSubgroup π D) (e : MulAut G)
    (hkernel : ∀ d ∈ D, e d * d⁻¹ ∈ K) :
    ∃ k ∈ K, D.map e.toMonoidHom = D.map (MulAut.conj k).toMonoidHom := by
  let W := K ⊔ D
  let E := D.map e.toMonoidHom
  have hDW : D ≤ W := le_sup_right
  have hEW : E ≤ W := by
    rintro x ⟨d, hd, rfl⟩
    have hc : e d * d⁻¹ ∈ W := (show K ≤ W from le_sup_left) (hkernel d hd)
    have hdc : (e d * d⁻¹) * d = e d := by group
    exact hdc ▸ W.mul_mem hc (hDW hd)
  let : Group.IsSolvable G := hsolv
  have hsolvW : Group.IsSolvable W := subgroup_solvable_of_solvable W
  obtain ⟨w, hw⟩ := CFSG.exists_conj_eq_of_isHallSubgroup_of_solvable hsolvW
    (hHall.subgroupOf hDW) ((hHall.map_mulAut e).subgroupOf hEW)
  have hmaps : E = D.map (MulAut.conj (w : G)).toMonoidHom := by
    have h := congrArg (fun U : Subgroup W => U.map W.subtype) hw
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hEW,
      CFSG.map_subgroupOf_map_conj_eq hDW w] at h
    exact h
  have hwproduct : (w : G) ∈ (K : Set G) * (D : Set G) := by
    rw [← Subgroup.normal_mul K D]
    exact w.property
  obtain ⟨k, hk, d, hd, hkd⟩ := Set.mem_mul.mp hwproduct
  refine ⟨k, hk, ?_⟩
  change E = D.map (MulAut.conj k).toMonoidHom
  rw [hmaps, ← hkd]
  exact CFSG.map_conj_mul_right_eq_of_mem_normalizer k
    ⟨d, Subgroup.le_normalizer hd⟩

theorem normal_subgroup_hall_normalizer_factorization
    (M Q : Subgroup G) [M.Normal] [Q.Normal] (hsolv : Group.IsSolvable M)
    (π : Set Nat.Primes) (D : Subgroup M) (hHall : CFSG.IsHallSubgroup π D)
    (g : G) (hg : g ∈ Q) :
    ∃ m : M, (m : G) ∈ Q ∧
      ∃ n ∈ Subgroup.normalizer (D.map M.subtype : Set G),
        n ∈ Q ∧ g = (m : G) * n := by
  let K := Q.subgroupOf M
  let e : MulAut M := MulAut.conjNormal g
  have hkernel : ∀ d ∈ D, e d * d⁻¹ ∈ K := by
    intro d _hd
    change ((e d : M) : G) * (d : G)⁻¹ ∈ Q
    rw [MulAut.conjNormal_apply]
    have hc : (d : G) * g⁻¹ * (d : G)⁻¹ ∈ Q :=
      (inferInstance : Q.Normal).conj_mem g⁻¹ (Q.inv_mem hg) d
    simpa only [mul_assoc] using Q.mul_mem hg hc
  obtain ⟨m, hm, heq⟩ := hall_conjugacy_by_normal_kernel K hsolv π D hHall e hkernel
  have hmaps : (D.map M.subtype).map (MulAut.conj g).toMonoidHom =
      (D.map M.subtype).map (MulAut.conj (m : G)).toMonoidHom := by
    have h := congrArg (fun U : Subgroup M => U.map M.subtype) heq
    rw [show e = MulAut.conjNormal g from rfl,
      normal_subgroup_conjugate_map_subtype,
      ← MulAut.conjNormal_val (h := m),
      normal_subgroup_conjugate_map_subtype] at h
    exact h
  let n := (m : G)⁻¹ * g
  have hn : n ∈ Subgroup.normalizer (D.map M.subtype : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change (D.map M.subtype).map (MulAut.conj n).toMonoidHom = D.map M.subtype
    have hcomp : (MulAut.conj n).toMonoidHom =
        (MulAut.conj (m : G)⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom := by
      ext x
      simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      dsimp only [n]
      group
    rw [hcomp, ← Subgroup.map_map, hmaps, Subgroup.map_map]
    have hcancel : (MulAut.conj (m : G)⁻¹).toMonoidHom.comp
        (MulAut.conj (m : G)).toMonoidHom = MonoidHom.id G := by
      ext x
      simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, MonoidHom.id_apply]
      group
    rw [hcancel, Subgroup.map_id]
  have hmQ : (m : G) ∈ Q := hm
  have hnQ : n ∈ Q := Q.mul_mem (Q.inv_mem hmQ) hg
  exact ⟨m, hmQ, n, hn, hnQ, by dsimp only [n]; group⟩

theorem odd_relative_index_of_normal_subgroup_hall_normalizer
    (M Q L R : Subgroup G) [M.Normal] [Q.Normal]
    (hsolv : Group.IsSolvable M) (hML : M ≤ L)
    (π : Set Nat.Primes) (D : Subgroup M) (hHall : CFSG.IsHallSubgroup π D)
    (hcontain : ∀ x ∈ Q, orderOf x = 2 → x ∈ R)
    (hdisjoint : Disjoint R (Subgroup.normalizer (D.map M.subtype : Set G))) :
    Odd (L.subgroupOf Q).index := by
  let A := M.subgroupOf Q
  let B := (Subgroup.normalizer (D.map M.subtype : Set G)).subgroupOf Q
  have hsup : A ⊔ B = ⊤ := by
    apply top_unique
    intro x _hx
    obtain ⟨m, hmQ, n, hn, hnQ, hmn⟩ :=
      normal_subgroup_hall_normalizer_factorization M Q hsolv π D hHall x x.property
    let mQ : Q := ⟨m, hmQ⟩
    let nQ : Q := ⟨n, hnQ⟩
    have hmA : mQ ∈ A := m.property
    have hnB : nQ ∈ B := hn
    have hval : x = mQ * nQ := Subtype.ext hmn
    rw [hval]
    exact (A ⊔ B).mul_mem
      ((show A ≤ A ⊔ B from le_sup_left) hmA)
      ((show B ≤ A ⊔ B from le_sup_right) hnB)
  have hBodd : Odd (Nat.card B) := by
    have hcard : Nat.card B =
        Nat.card (Q ⊓ Subgroup.normalizer (D.map M.subtype : Set G) : Subgroup G) := by
      calc
        _ = Nat.card (B.map Q.subtype) := (Subgroup.card_subtype _ _).symm
        _ = _ := by rw [Subgroup.subgroupOf_map_subtype, inf_comm]
    rw [hcard]
    exact hall_normalizer_intersection_odd Q R (D.map M.subtype) hcontain hdisjoint
  have hAodd : Odd A.index := by
    have hdiv : A.index ∣ Nat.card B := by
      rw [← Subgroup.relIndex_top_right A, ← hsup, Subgroup.relIndex_sup_left]
      exact Subgroup.relIndex_dvd_card A B
    exact hBodd.of_dvd_nat hdiv
  exact hAodd.of_dvd_nat (Subgroup.index_dvd_of_le
    (show A ≤ L.subgroupOf Q from fun _ hx => hML hx))

end CFSG.ComponentClassification.AschbacherTightEmbedding
