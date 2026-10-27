module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.CfgIMain
public import CFSG.RankThree.PartTwo.Census.TripleCoverLift
public import CFSG.GH74.GLS.C3.Layer1.Th2HYGrp

public section

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.RankThree.PartTwo.Sec4.Census

namespace CFSG.LocalAnalysis.GLTheoremA.S8.CfgI.Triangular

variable {Q X : Type} [Group Q] [Group X] {π : Q →* X}

theorem exists_elemAbelian_of_lifts [Finite Q] (A : Subgroup X)
    (hcomm : ∀ x ∈ A.comap π, ∀ y ∈ A.comap π, x * y = y * x)
    (hlift : ∀ e ∈ A, ∃ y : Q, π y = e ∧ y ^ 3 = 1) :
    ∃ U : Subgroup Q, IsElemAbelian 3 U ∧ Nat.card A * Nat.card ↥(U ⊓ π.ker) ≤ Nat.card U := by
  classical
  set U := TripleCoverLift.powOneSubgroup π A 3 hcomm with hUdef
  have hUab : IsElemAbelian 3 U :=
    ⟨⟨⟨fun a b => Subtype.ext (hcomm _ (TripleCoverLift.mem_powOneSubgroup.mp a.2).1 _
      (TripleCoverLift.mem_powOneSubgroup.mp b.2).1)⟩⟩,
      fun x hx => (TripleCoverLift.mem_powOneSubgroup.mp hx).2⟩
  refine ⟨U, hUab, ?_⟩
  set ψ : ↥U →* X := π.comp U.subtype with hψ
  have hψr : ψ.range = A := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (TripleCoverLift.mem_powOneSubgroup.mp y.2).1
    · intro hx
      obtain ⟨y, hy, hyp⟩ := hlift x hx
      exact ⟨⟨y, TripleCoverLift.mem_powOneSubgroup.mpr ⟨hy ▸ hx, hyp⟩⟩, hy⟩
  have hkerψ : Nat.card ψ.ker = Nat.card ↥(U ⊓ π.ker) := by
    rw [hψ, ← MonoidHom.comap_ker, ← Subgroup.card_map_of_injective U.subtype_injective]
    change Nat.card ((π.ker.subgroupOf U).map U.subtype) = _
    rw [Subgroup.subgroupOf_map_subtype, inf_comm]
  have hmul := Subgroup.card_ker_mul_card_range ψ
  rw [hkerψ, hψr] at hmul
  rw [← hmul, mul_comm]

theorem exists_elemAbelian_of_triangular [Finite Q] (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center Q) {m : ℕ} (x n : Fin m → X) (hx3 : ∀ i, x i ^ 3 = 1)
    (hcomm : ∀ i j, x i * x j = x j * x i) (hinv : ∀ j, n j * x j * (n j)⁻¹ = (x j)⁻¹)
    (hfix : ∀ i j, i < j → n j * x i * (n j)⁻¹ = x i) :
    ∃ U : Subgroup Q, IsElemAbelian 3 U ∧
      Nat.card (Subgroup.closure (Set.range x)) * Nat.card ↥(U ⊓ π.ker) ≤ Nat.card U := by
  have hodd : Odd 3 := by decide
  have hS : ∀ a b : Q, π a ∈ Set.range x → π b ∈ Set.range x → π a ≠ π b → a * b = b * a := by
    rintro a b ⟨i, hi⟩ ⟨j, hj⟩ hab
    have hij : i ≠ j := fun h => hab (by rw [← hi, ← hj, h])
    rcases lt_or_gt_of_ne hij with h | h
    · refine TripleCoverLift.commute_of_conj hπ hker hodd (n := n j) ?_ ?_ (Or.inl ⟨?_, ?_⟩)
      · rw [← hi, ← hj]; exact hcomm i j
      · rw [← hj]; exact hx3 j
      · rw [← hi]; exact hfix i j h
      · rw [← hj]; exact hinv j
    · refine (TripleCoverLift.commute_of_conj hπ hker hodd (n := n i) ?_ ?_
        (Or.inl ⟨?_, ?_⟩)).symm
      · rw [← hi, ← hj]; exact hcomm j i
      · rw [← hi]; exact hx3 i
      · rw [← hj]; exact hfix j i h
      · rw [← hi]; exact hinv i
  have hc : ∀ a ∈ (Subgroup.closure (Set.range x)).comap π,
      ∀ b ∈ (Subgroup.closure (Set.range x)).comap π, a * b = b * a :=
    fun a ha b hb => TripleCoverLift.commute_of_mem_closure hπ hker hS ha hb
  refine exists_elemAbelian_of_lifts _ hc fun e he => ?_
  refine TripleCoverLift.exists_lift_pow_eq_one_of_mem_closure hc Subgroup.subset_closure ?_ he
  rintro _ ⟨j, rfl⟩
  exact TripleCoverLift.exists_lift_pow_eq_one_of_conj_eq_inv hπ hker hodd (hx3 j) (hinv j)

theorem cfgIRankRow_of_triangular {row : S8.Row} {M : Type} [Group M]
    (hbr : ∀ i : TauCeti.CFSGIndex, row.Iq i → Nonempty (i.Group ≃* M)) {m : ℕ}
    (hm : row.rank - 1 = m) (x n : Fin m → M) (hx3 : ∀ i, x i ^ 3 = 1)
    (hcomm : ∀ i j, x i * x j = x j * x i) (hinv : ∀ j, n j * x j * (n j)⁻¹ = (x j)⁻¹)
    (hfix : ∀ i j, i < j → n j * x i * (n j)⁻¹ = x i)
    (hcard : 3 ^ m ≤ Nat.card (Subgroup.closure (Set.range x))) :
    CfgIRankRow 3 row := by
  intro Q _ _ hcat _
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  obtain ⟨b⟩ := hbr i hi
  let π : Q →* M := (e.trans b).toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Q))
  have hπ : Function.Surjective π :=
    (e.trans b).surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerZ : π.ker = Subgroup.center Q := by
    ext q
    simp only [π, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨U, hU, hUc⟩ := exists_elemAbelian_of_triangular hπ hkerZ.le x n hx3 hcomm hinv hfix
  refine ⟨U, hU, ?_⟩
  rw [hm, ← hkerZ]
  exact le_trans (Nat.mul_le_mul_right _ hcard) hUc

section Card

variable {M : Type} [Group M] [Finite M] {m : ℕ} {x n : Fin m → M}

@[expose] def lowerClosure (x : Fin m → M) (k : ℕ) : Subgroup M :=
  Subgroup.closure (x '' {i | i.val < k})

theorem lowerClosure_succ (x : Fin m → M) {k : ℕ} (hk : k < m) :
    lowerClosure x (k + 1) = lowerClosure x k ⊔ Subgroup.zpowers (x ⟨k, hk⟩) := by
  unfold lowerClosure
  rw [Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
    · exact Or.inl ⟨i, h, rfl⟩
    · exact Or.inr (by congr 1; exact Fin.ext h)
  · rintro (⟨i, hi, rfl⟩ | rfl)
    · exact ⟨i, Nat.lt_succ_of_lt hi, rfl⟩
    · exact ⟨⟨k, hk⟩, Nat.lt_succ_self k, rfl⟩

theorem lowerClosure_eq (x : Fin m → M) : lowerClosure x m = Subgroup.closure (Set.range x) := by
  unfold lowerClosure
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_range]
  exact ⟨fun ⟨i, _, h⟩ => ⟨i, h⟩, fun ⟨i, h⟩ => ⟨i, i.2, h⟩⟩

theorem card_closure_of_triangular (hx3 : ∀ i, x i ^ 3 = 1) (hx1 : ∀ i, x i ≠ 1)
    (hcomm : ∀ i j, x i * x j = x j * x i) (hinv : ∀ j, n j * x j * (n j)⁻¹ = (x j)⁻¹)
    (hfix : ∀ i j, i < j → n j * x i * (n j)⁻¹ = x i) :
    3 ^ m ≤ Nat.card (Subgroup.closure (Set.range x)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [← lowerClosure_eq]
  suffices h : ∀ k ≤ m, 3 ^ k ≤ Nat.card (lowerClosure x k) from h m le_rfl
  intro k
  induction k with
  | zero => intro _; simpa using Nat.one_le_iff_ne_zero.2 Nat.card_pos.ne'
  | succ k ih =>
    intro hk
    have hkm : k < m := hk
    set y := x ⟨k, hkm⟩ with hy
    set H := lowerClosure x k with hH
    have hnH : ∀ h ∈ H, n ⟨k, hkm⟩ * h * (n ⟨k, hkm⟩)⁻¹ = h := by
      intro h hh
      have hle : H ≤ Subgroup.centralizer ({n ⟨k, hkm⟩} : Set M) := by
        rw [hH, lowerClosure, Subgroup.closure_le]
        rintro _ ⟨i, hi, rfl⟩
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        have := hfix i ⟨k, hkm⟩ (Fin.lt_def.2 hi)
        symm
        calc n ⟨k, hkm⟩ * x i = n ⟨k, hkm⟩ * x i * (n ⟨k, hkm⟩)⁻¹ * n ⟨k, hkm⟩ := by group
          _ = x i * n ⟨k, hkm⟩ := by rw [this]
      have := Subgroup.mem_centralizer_singleton_iff.1 (hle hh)
      rw [← this, mul_inv_cancel_right]
    have hyH : y ∉ H := by
      intro hm
      have h1 := hnH y hm
      rw [hy, hinv] at h1
      have h2 : y ^ 2 = 1 := by
        rw [sq]
        calc y * y = y * y⁻¹ := by rw [← hy] at h1; rw [h1]
          _ = 1 := mul_inv_cancel y
      apply hx1 ⟨k, hkm⟩
      rw [← hy]
      calc y = y ^ 3 * (y ^ 2)⁻¹ := by group
        _ = 1 := by rw [hx3, h2]; group
    have hyN : Subgroup.zpowers y ≤ Subgroup.normalizer (H : Set M) := by
      have hc : ∀ h ∈ H, y * h = h * y := by
        intro h hh
        have hle : H ≤ Subgroup.centralizer ({y} : Set M) := by
          rw [hH, lowerClosure, Subgroup.closure_le]
          rintro _ ⟨i, -, rfl⟩
          rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, hy]
          exact hcomm _ _
        exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hh)).symm
      refine Subgroup.zpowers_le.2 ?_
      rw [Subgroup.mem_normalizer_iff]
      intro h
      have hyh : ∀ g ∈ H, y * g * y⁻¹ = g := fun g hg => by rw [hc g hg, mul_inv_cancel_right]
      constructor
      · intro hh; rw [hyh h hh]; exact hh
      · intro hh
        have hk := hc _ hh
        have e2 : (y * h * y⁻¹) * y⁻¹ = h * y⁻¹ := by
          calc (y * h * y⁻¹) * y⁻¹ = y⁻¹ * (y * (y * h * y⁻¹)) * y⁻¹ := by group
            _ = y⁻¹ * ((y * h * y⁻¹) * y) * y⁻¹ := by rw [hk]
            _ = h * y⁻¹ := by group
        have e : h = y * h * y⁻¹ := (mul_right_cancel e2).symm
        rw [e]; exact hh
    have hprod := CFSG.GH74.GLS.Th2.HY.card_sup_mul_card_inf_of_le_normalizer hyN
    have hcy : Nat.card (Subgroup.zpowers y) = 3 := by
      rw [Nat.card_zpowers, orderOf_eq_prime (hx3 _) (hx1 _)]
    have hinf : Nat.card ↥(Subgroup.zpowers y ⊓ H) = 1 := by
      have hd : Nat.card ↥(Subgroup.zpowers y ⊓ H) ∣ 3 := by
        rw [← hcy]; exact Subgroup.card_dvd_of_le inf_le_left
      rcases (Nat.dvd_prime Nat.prime_three).1 hd with h1 | h3
      · exact h1
      · exfalso
        have heq : Subgroup.zpowers y ⊓ H = Subgroup.zpowers y :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, hcy])
        have : y ∈ Subgroup.zpowers y ⊓ H := by rw [heq]; exact Subgroup.mem_zpowers y
        exact hyH (Subgroup.mem_inf.1 this).2
    rw [hinf, mul_one, hcy] at hprod
    rw [lowerClosure_succ x hkm, ← hy, sup_comm, hprod, pow_succ, mul_comm]
    exact Nat.mul_le_mul_left 3 (ih hkm.le)

end Card

theorem cfgIRankRow_of_triangular' {row : S8.Row} {M : Type} [Group M] [Finite M]
    (hbr : ∀ i : TauCeti.CFSGIndex, row.Iq i → Nonempty (i.Group ≃* M)) {m : ℕ}
    (hm : row.rank - 1 = m) (x n : Fin m → M) (hx3 : ∀ i, x i ^ 3 = 1) (hx1 : ∀ i, x i ≠ 1)
    (hcomm : ∀ i j, x i * x j = x j * x i) (hinv : ∀ j, n j * x j * (n j)⁻¹ = (x j)⁻¹)
    (hfix : ∀ i j, i < j → n j * x i * (n j)⁻¹ = x i) :
    CfgIRankRow 3 row :=
  cfgIRankRow_of_triangular hbr hm x n hx3 hcomm hinv hfix
    (card_closure_of_triangular hx3 hx1 hcomm hinv hfix)

end CFSG.LocalAnalysis.GLTheoremA.S8.CfgI.Triangular
