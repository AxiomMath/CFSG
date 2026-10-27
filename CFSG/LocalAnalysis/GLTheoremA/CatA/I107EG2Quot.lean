module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47fTable
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107ETwB2
public import CFSG.LocalAnalysis.StandardType.MarkingChevalley

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I107E

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.GH74.GLS.IVK.Proofs2.Ivk47 CFSG.LieType.Chevalley RootOps
open CFSG.Assembly
open scoped commutatorElement

abbrev i0G2 : Fin (Tag.rank Tag.G2) := ⟨0, by decide⟩

abbrev rA : Fin (Tag.rank Tag.G2) → ℤ := ![1, 0]
abbrev rR : Fin (Tag.rank Tag.G2) → ℤ := ![0, 1]
abbrev rV : Fin (Tag.rank Tag.G2) → ℤ := ![1, 2]
abbrev rB : Fin (Tag.rank Tag.G2) → ℤ := ![1, 3]
abbrev rC : Fin (Tag.rank Tag.G2) → ℤ := ![2, 3]

section Commutators

variable (K : Type) [Field K]

theorem g2_comm_rc (x y : K) : Commute (pinnedX Tag.G2 K rR x) (pinnedX Tag.G2 K rC y) :=
  (g2_commute_table (R := K) x y).2.2.2.2.1

theorem g2_comm_rb (x y : K) : Commute (pinnedX Tag.G2 K rR x) (pinnedX Tag.G2 K rB y) :=
  (g2_commute_table (R := K) x y).2.2.2.1

theorem g2_comm_bc (x y : K) : Commute (pinnedX Tag.G2 K rB x) (pinnedX Tag.G2 K rC y) :=
  (g2_commute_table (R := K) x y).2.2.2.2.2.2.2.2.2

theorem g2_comm_vb (x y : K) : Commute (pinnedX Tag.G2 K rV x) (pinnedX Tag.G2 K rB y) :=
  (g2_commute_table (R := K) x y).2.2.2.2.2.2.2.1

theorem g2_comm_vc (x y : K) : Commute (pinnedX Tag.G2 K rV x) (pinnedX Tag.G2 K rC y) :=
  (g2_commute_table (R := K) x y).2.2.2.2.2.2.2.2.1

theorem g2_comm_ac (x y : K) : Commute (pinnedX Tag.G2 K rA x) (pinnedX Tag.G2 K rC y) :=
  (g2_commute_table (R := K) x y).2.2.1

theorem g2_rel_ab_K : ∃ e : K, (e = 1 ∨ e = -1) ∧ ∀ x y : K,
    ⁅pinnedX Tag.G2 K rA x, pinnedX Tag.G2 K rB y⁆ = pinnedX Tag.G2 K rC (e * (x * y)) :=
  g2_rel_ab (R := K)

theorem g2_rel_rv (h2 : (2 : K) = 0) :
    ∃ e : K, (e = 1 ∨ e = -1) ∧ ∀ x y : K,
      ⁅pinnedX Tag.G2 K rR x, pinnedX Tag.G2 K rV y⁆ = pinnedX Tag.G2 K rB (e * (x * y)) := by
  have e6 : orbitCertRoot Tag.G2 6 = rR := List.ofFn_injective (by decide +kernel)
  have e9 : orbitCertRoot Tag.G2 9 = rV := List.ofFn_injective (by decide +kernel)
  have e10 : orbitCertRoot Tag.G2 10 = rB := List.ofFn_injective (by decide +kernel)
  rw [← e6, ← e9, ← e10]
  have r9 : ((6, 9, 12, [(1, 1, 10, 3)]) : PairRow) ∈ pairTable Tag.G2 := by decide +kernel
  have one : ∀ k, (1 : WeylGroup Tag.G2) • orbitCertRoot Tag.G2 k = orbitCertRoot Tag.G2 k :=
    fun _ => one_smul _ _
  have h3 : (3 : K) = 1 := by linear_combination h2
  obtain ⟨σ, hσ, h⟩ := commutatorElement_pinnedX_signs (R := K) r9 1 (one 6) (one 9)
  refine ⟨σ (1, 1, 10, 3), hσ _, fun x y => ?_⟩
  rw [h x y]
  simp [one, h3]

end Commutators

theorem exists_unit_ne_one (K : Type) [Field K] [Finite K] (hK : 2 < Nat.card K) :
    ∃ τ0 : Kˣ, (τ0 : K) ≠ 1 := by
  classical
  by_contra h
  replace h : ∀ τ0 : Kˣ, (τ0 : K) = 1 := fun τ0 => by
    by_contra hc
    exact h ⟨τ0, hc⟩
  have key : ∀ x : K, x ≠ 0 → x = 1 := fun x hx => by
    simpa using h (Units.mk0 x hx)
  let f : K → Bool := fun x => decide (x ≠ 0)
  have hinj : Function.Injective f := by
    intro x y hxy
    by_cases hx : x = 0
    · by_cases hy : y = 0
      · rw [hx, hy]
      · exfalso
        simp [f, hx, hy] at hxy
    · by_cases hy : y = 0
      · exfalso
        simp [f, hx, hy] at hxy
      · rw [key x hx, key y hy]
  have hle := Nat.card_le_card_of_injective f hinj
  simp at hle
  omega

section Triple

variable {K : Type} [Field K]

@[expose] noncomputable def g2Prod (K : Type) [Field K] (s t u : K) : (Module.End K (RootModule Tag.G2 K))ˣ :=
  pinnedX Tag.G2 K rR s * pinnedX Tag.G2 K rB t * pinnedX Tag.G2 K rC u

theorem g2Prod_mem (s t u : K) : g2Prod K s t u ∈ adjointGroup Tag.G2 K :=
  mul_mem (mul_mem (pinnedX_mem_adjointGroup rR s) (pinnedX_mem_adjointGroup rB t))
    (pinnedX_mem_adjointGroup rC u)

theorem comm_reorder {G : Type*} [Group G] {R B C R' B' C' : G} (e1 : C * R' = R' * C)
    (e2 : B * R' = R' * B) (e3 : C * B' = B' * C) :
    R * B * C * (R' * B' * C') = R * R' * (B * B') * (C * C') := by
  have L1 : B * C * R' = R' * B * C := by rw [mul_assoc, e1, ← mul_assoc, e2]
  calc R * B * C * (R' * B' * C') = R * (B * C * R') * B' * C' := by simp only [mul_assoc]
    _ = R * (R' * B * C) * B' * C' := by rw [L1]
    _ = R * R' * B * (C * B') * C' := by simp only [mul_assoc]
    _ = R * R' * B * (B' * C) * C' := by rw [e3]
    _ = R * R' * (B * B') * (C * C') := by simp only [mul_assoc]

theorem g2Prod_add (s s' t t' u u' : K) :
    g2Prod K (s + s') (t + t') (u + u') = g2Prod K s t u * g2Prod K s' t' u' := by
  have e1 := (g2_comm_rc K s' u).eq.symm
  have e2 := (g2_comm_rb K s' t).eq.symm
  have e3 := (g2_comm_bc K t' u).eq.symm
  unfold g2Prod
  rw [pinnedX_add Tag.G2 K rR s s', pinnedX_add Tag.G2 K rB t t', pinnedX_add Tag.G2 K rC u u']
  exact (comm_reorder e1 e2 e3).symm

theorem isRoot_rC : IsRoot Tag.G2 rC := by
  have h := IsRoot.reflect (τ := Tag.G2) ⟨0, by decide⟩
    (IsRoot.reflect (τ := Tag.G2) ⟨1, by decide⟩ (IsRoot.basis (τ := Tag.G2) ⟨0, by decide⟩))
  have key : reflect Tag.G2 ⟨0, by decide⟩ (reflect Tag.G2 ⟨1, by decide⟩ (Pi.single ⟨0, by decide⟩ 1)) = rC := by
    decide
  rw [← key]
  exact h

theorem g2Prod_eq_zero_of_mem_center (h2 : (2 : K) = 0) (hτ : ∃ τ0 : Kˣ, (τ0 : K) ≠ 1) (s t u : K)
    (hz : (⟨g2Prod K s t u, g2Prod_mem s t u⟩ : ↥(adjointGroup Tag.G2 K)) ∈
      Subgroup.center ↥(adjointGroup Tag.G2 K)) : s = 0 ∧ t = 0 ∧ u = 0 := by
  rw [Subgroup.mem_center_iff] at hz
  have hcen : ∀ g : (Module.End K (RootModule Tag.G2 K))ˣ, g ∈ adjointGroup Tag.G2 K →
      g * g2Prod K s t u = g2Prod K s t u * g := fun g hg => congrArg Subtype.val (hz ⟨g, hg⟩)
  obtain ⟨e, he, hrel⟩ := g2_rel_rv K h2
  obtain ⟨e', he', hrel'⟩ := g2_rel_ab_K K
  have hV := hcen (pinnedX Tag.G2 K rV 1) (pinnedX_mem_adjointGroup rV 1)
  have hCV : pinnedX Tag.G2 K rC u * pinnedX Tag.G2 K rV 1 =
      pinnedX Tag.G2 K rV 1 * pinnedX Tag.G2 K rC u := (g2_comm_vc K 1 u).eq.symm
  have hBV : pinnedX Tag.G2 K rB t * pinnedX Tag.G2 K rV 1 =
      pinnedX Tag.G2 K rV 1 * pinnedX Tag.G2 K rB t := (g2_comm_vb K 1 t).eq.symm
  have hVR : pinnedX Tag.G2 K rV 1 * pinnedX Tag.G2 K rR s =
      pinnedX Tag.G2 K rR s * pinnedX Tag.G2 K rV 1 := by
    apply mul_right_cancel (b := pinnedX Tag.G2 K rB t * pinnedX Tag.G2 K rC u)
    unfold g2Prod at hV
    calc pinnedX Tag.G2 K rV 1 * pinnedX Tag.G2 K rR s * (pinnedX Tag.G2 K rB t * pinnedX Tag.G2 K rC u)
        = pinnedX Tag.G2 K rV 1 * (pinnedX Tag.G2 K rR s * pinnedX Tag.G2 K rB t * pinnedX Tag.G2 K rC u) := by
          simp only [mul_assoc]
      _ = pinnedX Tag.G2 K rR s * pinnedX Tag.G2 K rB t * pinnedX Tag.G2 K rC u * pinnedX Tag.G2 K rV 1 := hV
      _ = pinnedX Tag.G2 K rR s * (pinnedX Tag.G2 K rB t * (pinnedX Tag.G2 K rC u * pinnedX Tag.G2 K rV 1)) := by
          simp only [mul_assoc]
      _ = pinnedX Tag.G2 K rR s * (pinnedX Tag.G2 K rB t * (pinnedX Tag.G2 K rV 1 * pinnedX Tag.G2 K rC u)) := by
          rw [hCV]
      _ = pinnedX Tag.G2 K rR s * ((pinnedX Tag.G2 K rB t * pinnedX Tag.G2 K rV 1) * pinnedX Tag.G2 K rC u) := by
          simp only [mul_assoc]
      _ = pinnedX Tag.G2 K rR s * ((pinnedX Tag.G2 K rV 1 * pinnedX Tag.G2 K rB t) * pinnedX Tag.G2 K rC u) := by
          rw [hBV]
      _ = pinnedX Tag.G2 K rR s * pinnedX Tag.G2 K rV 1 * (pinnedX Tag.G2 K rB t * pinnedX Tag.G2 K rC u) := by
          simp only [mul_assoc]
  have hs : s = 0 := by
    have hcomm : Commute (pinnedX Tag.G2 K rR s) (pinnedX Tag.G2 K rV 1) := hVR.symm
    have hb : pinnedX Tag.G2 K rB (e * (s * 1)) = pinnedX Tag.G2 K rB 0 := by
      rw [pinnedX_zero, ← hrel s 1, commutatorElement_eq_one_iff_commute.2 hcomm]
    have hw := pinnedX_injective Tag.G2 K rB hb
    rcases he with rfl | rfl
    · simpa using hw
    · simpa using hw
  subst hs
  have hA := hcen (pinnedX Tag.G2 K rA 1) (pinnedX_mem_adjointGroup rA 1)
  unfold g2Prod at hA
  rw [pinnedX_zero, one_mul] at hA
  have hAC : pinnedX Tag.G2 K rA 1 * pinnedX Tag.G2 K rC u =
      pinnedX Tag.G2 K rC u * pinnedX Tag.G2 K rA 1 := (g2_comm_ac K 1 u).eq
  have hAB : pinnedX Tag.G2 K rA 1 * pinnedX Tag.G2 K rB t =
      pinnedX Tag.G2 K rB t * pinnedX Tag.G2 K rA 1 := by
    apply mul_right_cancel (b := pinnedX Tag.G2 K rC u)
    calc pinnedX Tag.G2 K rA 1 * pinnedX Tag.G2 K rB t * pinnedX Tag.G2 K rC u
        = pinnedX Tag.G2 K rA 1 * (pinnedX Tag.G2 K rB t * pinnedX Tag.G2 K rC u) := by simp only [mul_assoc]
      _ = pinnedX Tag.G2 K rB t * pinnedX Tag.G2 K rC u * pinnedX Tag.G2 K rA 1 := hA
      _ = pinnedX Tag.G2 K rB t * (pinnedX Tag.G2 K rC u * pinnedX Tag.G2 K rA 1) := by simp only [mul_assoc]
      _ = pinnedX Tag.G2 K rB t * (pinnedX Tag.G2 K rA 1 * pinnedX Tag.G2 K rC u) := by rw [hAC]
      _ = pinnedX Tag.G2 K rB t * pinnedX Tag.G2 K rA 1 * pinnedX Tag.G2 K rC u := by simp only [mul_assoc]
  have ht : t = 0 := by
    have hb : pinnedX Tag.G2 K rC (e' * (1 * t)) = pinnedX Tag.G2 K rC 0 := by
      rw [pinnedX_zero, ← hrel' 1 t, commutatorElement_eq_one_iff_commute.2 hAB]
    have hw := pinnedX_injective Tag.G2 K rC hb
    rcases he' with rfl | rfl
    · simpa using hw
    · simpa using hw
  subst ht
  obtain ⟨τ0, hτ0⟩ := hτ
  have hd := hcen (torusElt Tag.G2 K i0G2 τ0) (torusElt_mem_adjointGroup i0G2 τ0)
  unfold g2Prod at hd
  simp only [pinnedX_zero, one_mul, mul_one] at hd
  have hconj := root_torus_conjugation i0G2 isRoot_rC τ0 u
  have hexp : (∑ j, Tag.cartan Tag.G2 i0G2 j * rC j) = 1 := by
    decide
  rw [hexp, zpow_one] at hconj
  have hC : torusElt Tag.G2 K i0G2 τ0 * pinnedX Tag.G2 K rC u * (torusElt Tag.G2 K i0G2 τ0)⁻¹ =
      pinnedX Tag.G2 K rC u := by
    rw [hd, mul_assoc, mul_inv_cancel, mul_one]
  rw [hC] at hconj
  have hw := pinnedX_injective Tag.G2 K rC hconj.symm
  have hu : ((τ0 : K) - 1) * u = 0 := by linear_combination hw
  rcases mul_eq_zero.1 hu with h | h
  · exact absurd (sub_eq_zero.1 h) hτ0
  · exact ⟨rfl, rfl, h⟩

theorem g2Quot_pRank {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    [Finite (AdjointQuotient Tag.G2 K)] :
    3 * n ≤ CFSG.Open.pRank 2 (⊤ : Subgroup (AdjointQuotient Tag.G2 K)) := by
  have h2 : (2 : K) = 0 := CFSG.LocalAnalysis.GLTheoremA.I107G.two_eq_zero_of_card (by omega) hK
  have hτ : ∃ τ0 : Kˣ, (τ0 : K) ≠ 1 := exists_unit_ne_one K (by
    rw [hK]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn)
  let G : K × K × K → ↥(adjointGroup Tag.G2 K) := fun p => ⟨g2Prod K p.1 p.2.1 p.2.2, g2Prod_mem _ _ _⟩
  have hG : ∀ p q : K × K × K, G (p + q) = G p * G q := fun p q => Subtype.ext (g2Prod_add _ _ _ _ _ _)
  let F : Multiplicative (K × K × K) →* ↥(adjointGroup Tag.G2 K) :=
    MonoidHom.mk' (fun x => G (Multiplicative.toAdd x)) (fun x y => by rw [toAdd_mul]; exact hG _ _)
  let Fq : Multiplicative (K × K × K) →* AdjointQuotient Tag.G2 K :=
    (QuotientGroup.mk' (Subgroup.center ↥(adjointGroup Tag.G2 K))).comp F
  have hinj : Function.Injective Fq := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : (QuotientGroup.mk (G (Multiplicative.toAdd x)) :
        ↥(adjointGroup Tag.G2 K) ⧸ Subgroup.center ↥(adjointGroup Tag.G2 K)) = 1 := hx
    have hz : G (Multiplicative.toAdd x) ∈ Subgroup.center ↥(adjointGroup Tag.G2 K) :=
      (QuotientGroup.eq_one_iff _).1 hx'
    obtain ⟨hs, ht, hu⟩ := g2Prod_eq_zero_of_mem_center h2 hτ (Multiplicative.toAdd x).1
      (Multiplicative.toAdd x).2.1 (Multiplicative.toAdd x).2.2 hz
    have h0 : Multiplicative.toAdd x = 0 := Prod.ext hs (Prod.ext ht hu)
    exact Multiplicative.toAdd.injective (by rw [h0, toAdd_one])
  have hcard : Nat.card Fq.range = 2 ^ (3 * n) := by
    have e1 := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    rw [← e1, Nat.card_congr Multiplicative.toAdd, Nat.card_prod, Nat.card_prod, hK]
    ring
  have hE : IsElemAbelian 2 Fq.range := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨p, hp⟩ := MonoidHom.mem_range.1 x.2
      obtain ⟨q, hq⟩ := MonoidHom.mem_range.1 y.2
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← hp, ← hq, ← map_mul, ← map_mul, mul_comm]
    · obtain ⟨p, rfl⟩ := MonoidHom.mem_range.1 hx
      have hA : ∀ x : K × K × K, x + x = 0 := fun x => by simp [Prod.ext_iff, ← two_mul, h2]
      have hsq : p ^ 2 = 1 := by
        apply Multiplicative.toAdd.injective
        rw [toAdd_pow, toAdd_one, two_nsmul, hA]
      rw [← map_pow, hsq, map_one]
  exact pRank_two_ge Fq.range hE hcard

theorem twoRankLow_G2_holds (S : Type) [Group S] [Finite S] (lab : GLALabel) (hS : IsSimpleGroup S)
    (hrk : Rk2IsLabel S lab) (ht : lab.tag = .G2) :
    twoRankLow107 lab ≤ CFSG.Open.pRank 2 (⊤ : Subgroup S) := by
  have hlab := rk2IsLabel_inLambda2 hrk
  have hraw := rk2IsLabel_rawDatum hrk
  obtain ⟨tag, rank, n⟩ := lab
  obtain rfl : tag = .G2 := ht
  have hn : 2 ≤ n := by
    have h := hlab.2
    dsimp only at h
    exact h.2
  dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum, CFSG.Assembly.LargeEvenRecipeChevalley] at hraw
  obtain ⟨K, hf, hfin, hK, hQ⟩ := hraw
  obtain ⟨hsR, hna, ⟨θ⟩⟩ := hQ
  have e0 : LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K false) ≃*
      AdjointQuotient Tag.G2 K :=
    (CFSG.StandardType.centerQuot_chevGroup_equiv K Tag.G2).some
  haveI : Finite (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K false)) :=
    Finite.of_equiv _ θ.toEquiv
  haveI : Finite (AdjointQuotient Tag.G2 K) := Finite.of_equiv _ e0.toEquiv
  rw [CFSG.LocalAnalysis.GLTheoremA.I107L.pRank_eq_of_quotient θ hna,
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 2) e0]
  exact g2Quot_pRank hn hK

end Triple

end CFSG.LocalAnalysis.GLTheoremA.I107E

end
