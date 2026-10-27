module

public import CFSG.RankThree.GF2n.Tim78S31Model
public import CFSG.RankThree.GF2n.Tim78S31Split
import CFSG.Fischer.Classification.Recognition.PSU6

public section

namespace CFSG.CGT.PushingUpLit.SolKR2

open CFSG.GroupTheory.ComplementLifting (out_inv_mul_mem commGroupOf)
open CFSG CFSG.Open CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78
open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup IsTI BenderCenterInput
  UnitaryTwoGenerationInput pslMulEquivSL center_sl2_eq_bot)
open scoped MatrixGroups
open CFSG.RankThree.PartTwo (omegaOneSub omegaOneSub_le)

theorem exists_coboundary {Γ : Type*} [Group Γ] [Finite Γ] (N Λ : Subgroup Γ) [N.Normal]
    (hNc : ∀ m ∈ N, ∀ n ∈ N, m * n = n * m) (hN2 : ∀ n ∈ N, n * n = 1) (hodd : Odd Λ.index)
    (δ : Γ → Γ) (hδN : ∀ z, δ z ∈ N) (hδmul : ∀ z z', δ (z * z') = δ z * (z * δ z' * z⁻¹))
    (hδΛ : ∀ s ∈ Λ, δ s = 1) : ∃ m ∈ N, ∀ z, δ z = m * (z * m⁻¹ * z⁻¹) := by
  classical
  have hcomm : IsMulCommutative N := ⟨⟨fun a b => Subtype.ext (hNc a a.2 b b.2)⟩⟩
  let _ : Fintype (Γ ⧸ Λ) := Fintype.ofFinite _
  let _ : CommGroup N := commGroupOf N
  let δ' : Γ → N := fun z => ⟨δ z, hδN z⟩
  have hδ'mul : ∀ z z', δ' (z * z') = δ' z * MulAut.conjNormal z (δ' z') := fun z z' =>
    Subtype.ext (by
      show δ (z * z') = δ z * (z * δ z' * z⁻¹)
      exact hδmul z z')
  have hδ'Λ : ∀ s ∈ Λ, δ' s = 1 := fun s hs => Subtype.ext (hδΛ s hs)
  have key1 : ∀ (g : Γ) (x : Γ ⧸ Λ),
      δ' (g • x).out = δ' g * MulAut.conjNormal g (δ' x.out) := by
    intro g x
    have hs : (g • x).out⁻¹ * g * x.out ∈ Λ := out_inv_mul_mem g x
    have e : g * x.out = (g • x).out * ((g • x).out⁻¹ * g * x.out) := by group
    have h1 : δ' (g * x.out) = δ' (g • x).out := by
      rw [e, hδ'mul, hδ'Λ _ hs, map_one, mul_one]
    rw [← h1, hδ'mul]
  let m : N := ∏ x : Γ ⧸ Λ, δ' x.out
  have key2 : ∀ g : Γ, m = δ' g ^ Fintype.card (Γ ⧸ Λ) * MulAut.conjNormal g m := by
    intro g
    calc m = ∏ x : Γ ⧸ Λ, δ' (g • x).out :=
          (Equiv.prod_comp (MulAction.toPerm g) (fun y : Γ ⧸ Λ => δ' y.out)).symm
      _ = ∏ x : Γ ⧸ Λ, (δ' g * MulAut.conjNormal g (δ' x.out)) :=
          Finset.prod_congr rfl fun x _ => key1 g x
      _ = δ' g ^ Fintype.card (Γ ⧸ Λ) * MulAut.conjNormal g m := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, map_prod]
  have hk : Odd (Fintype.card (Γ ⧸ Λ)) := by
    rw [Fintype.card_eq_nat_card, ← Subgroup.index_eq_card]
    exact hodd
  refine ⟨m, m.2, fun z => ?_⟩
  have hsq : δ' z ^ 2 = 1 := by
    rw [pow_two]
    exact Subtype.ext (hN2 _ (hδN z))
  obtain ⟨j, hj⟩ := hk
  have hpow : δ' z ^ Fintype.card (Γ ⧸ Λ) = δ' z := by
    rw [hj, pow_succ, pow_mul, hsq, one_pow, one_mul]
  have h2 := key2 z
  rw [hpow] at h2
  have h3 : δ' z = m * (MulAut.conjNormal z m)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    exact h2.symm
  have h4 := congrArg Subtype.val h3
  rw [Subgroup.coe_mul, ← map_inv, MulAut.conjNormal_apply] at h4
  exact h4


section InnerAction

variable {G : Type} [Group G]

theorem exists_inner_of_trivial_action [Finite G] {X N S₂ : Subgroup G} {y : G} (hNX : N ≤ X)
    (hXn : ∀ z ∈ X, ∀ n ∈ N, z * n * z⁻¹ ∈ N) (hNc : ∀ m ∈ N, ∀ n ∈ N, m * n = n * m)
    (hN2 : ∀ n ∈ N, n * n = 1) (hodd : Odd (S₂.subgroupOf X).index)
    (hδ : ∀ z ∈ X, y * z * y⁻¹ * z⁻¹ ∈ N) (hS : ∀ s ∈ S₂, y * s * y⁻¹ = s) :
    ∃ m ∈ N, ∀ z ∈ X, y * z * y⁻¹ = m * z * m⁻¹ := by
  have hnorm : (N.subgroupOf X).Normal := ⟨fun n hn z => Subgroup.mem_subgroupOf.mpr (by
    simpa using hXn z z.2 n (Subgroup.mem_subgroupOf.mp hn))⟩
  let δ : ↥X → ↥X := fun z => ⟨y * z * y⁻¹ * z⁻¹, hNX (hδ z z.2)⟩
  have hδN : ∀ z, δ z ∈ N.subgroupOf X := fun z => Subgroup.mem_subgroupOf.mpr (hδ z z.2)
  have hδmul : ∀ z z', δ (z * z') = δ z * (z * δ z' * z⁻¹) := fun z z' => Subtype.ext (by
    show y * (z * z' : ↥X) * y⁻¹ * (z * z' : ↥X)⁻¹ =
      (y * z * y⁻¹ * z⁻¹) * ((z : G) * (y * z' * y⁻¹ * z'⁻¹) * (z : G)⁻¹)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group)
  have hδΛ : ∀ s ∈ S₂.subgroupOf X, δ s = 1 := fun s hs => Subtype.ext (by
    have := hS s (Subgroup.mem_subgroupOf.mp hs)
    show y * (s : G) * y⁻¹ * (s : G)⁻¹ = 1
    rw [this]
    group)
  have hNc' : ∀ m ∈ N.subgroupOf X, ∀ n ∈ N.subgroupOf X, m * n = n * m := fun m hm n hn =>
    Subtype.ext (hNc m (Subgroup.mem_subgroupOf.mp hm) n (Subgroup.mem_subgroupOf.mp hn))
  have hN2' : ∀ n ∈ N.subgroupOf X, n * n = 1 := fun n hn =>
    Subtype.ext (hN2 n (Subgroup.mem_subgroupOf.mp hn))
  have : Finite ↥X := inferInstance
  obtain ⟨m, hm, hmδ⟩ := exists_coboundary (N.subgroupOf X) (S₂.subgroupOf X) hNc' hN2' hodd δ
    hδN hδmul hδΛ
  refine ⟨m, Subgroup.mem_subgroupOf.mp hm, fun z hz => ?_⟩
  have h1 := congrArg Subtype.val (hmδ ⟨z, hz⟩)
  simp only [δ, Subgroup.coe_mul, Subgroup.coe_inv] at h1
  show y * z * y⁻¹ = (m : G) * z * (m : G)⁻¹
  calc y * z * y⁻¹ = (y * z * y⁻¹ * z⁻¹) * z := by group
    _ = ((m : G) * (z * (m : G)⁻¹ * z⁻¹)) * z := by rw [h1]
    _ = (m : G) * z * (m : G)⁻¹ := by group

end InnerAction

section Data31Level

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
abbrev dN (U : Subgroup G) (x : G) : Subgroup G := omegaOneSub U ⊔ omegaOneSub (conjSubgroup x U)

abbrev dX (U : Subgroup G) (x : G) : Subgroup G := U ⊔ conjSubgroup x U

abbrev dS2 (U : Subgroup G) (x : G) : Subgroup G := dN U x ⊔ conjSubgroup x U

abbrev dS (U : Subgroup G) (g x : G) : Subgroup G :=
  dS2 U x ⊓ Subgroup.centralizer (omegaOneSub (conjSubgroup g U) : Set G)

omit [Finite G] in
theorem dN_le_dS2 (U : Subgroup G) (x : G) : dN U x ≤ dS2 U x := le_sup_left

omit [Finite G] in
theorem C_le_dS2 (U : Subgroup G) (x : G) : conjSubgroup x U ≤ dS2 U x := le_sup_right

omit [Finite G] in
theorem dS2_le_dX (U : Subgroup G) (x : G) : dS2 U x ≤ dX U x :=
  sup_le (sup_le_sup (omegaOneSub_le U) (omegaOneSub_le _)) le_sup_right

omit [Finite G] in
theorem dN_le_dX (U : Subgroup G) (x : G) : dN U x ≤ dX U x :=
  (dN_le_dS2 U x).trans (dS2_le_dX U x)

omit [Finite G] in
theorem dS_le_dS2 (U : Subgroup G) (g x : G) : dS U g x ≤ dS2 U x := inf_le_left

omit [Finite G] in
theorem U_le_dX (U : Subgroup G) (x : G) : U ≤ dX U x := le_sup_left

omit [Finite G] in
theorem C_le_dX (U : Subgroup G) (x : G) : conjSubgroup x U ≤ dX U x := le_sup_right

omit [Finite G] in
theorem exists_C_not_C0 {U : Subgroup G} {g α x : G} (D : Data31 U g α x) :
    ∃ c ∈ conjSubgroup x U, c ∉ omegaOneSub (conjSubgroup x U) := by
  obtain ⟨y, hy, hy2⟩ := D.core.exp_ne_conj x
  refine ⟨y, hy, fun h => hy2 ?_⟩
  rw [sq]
  exact ((mem_omegaOneSub_iff (D.core.comm_conj' x)).mp h).2

omit [Finite G] in
theorem exists_U_not_U0 {U : Subgroup G} {g α x : G} (D : Data31 U g α x) :
    ∃ u ∈ U, u ∉ omegaOneSub U := by
  obtain ⟨y, hy, hy2⟩ := D.core.exp_ne
  refine ⟨y, hy, fun h => hy2 ?_⟩
  rw [sq]
  exact ((mem_omegaOneSub_iff D.core.comm).mp h).2

section Certificates34


namespace Inner

variable {U : Subgroup G} {g α x : G} (D : Data31 U g α x) (hCen : BenderCenterInput)
  (hU : UnitaryTwoGenerationInput)
include D hCen hU

theorem odd_index :
    Odd ((dS2 U x).subgroupOf (U ⊔ conjSubgroup α U)).index := by
  classical
  have K := D.core
  have hXe := D.sup_eq hCen hU D.mem D.ne_one
  have hNe := D.N_eq hCen hU D.mem D.ne_one
  have hce := D.card_eq hCen hU
  obtain ⟨f, hf, hrel, hNn, ⟨e⟩⟩ := D.linear hCen hU
  set N := omegaOneSub U ⊔ omegaOneSub (conjSubgroup x U) with hNdef
  set S := N ⊔ conjSubgroup x U with hSdef
  have hCX : conjSubgroup x U ≤ U ⊔ conjSubgroup α U := by
    rw [hXe]
    exact le_sup_right
  have hπ : Function.Surjective (QuotientGroup.mk' ((omegaOneSub U ⊔
      omegaOneSub (conjSubgroup α U)).subgroupOf (U ⊔ conjSubgroup α U))) :=
    QuotientGroup.mk'_surjective _
  have hker : (QuotientGroup.mk' ((omegaOneSub U ⊔
      omegaOneSub (conjSubgroup α U)).subgroupOf (U ⊔ conjSubgroup α U))).ker ≤
        S.subgroupOf (U ⊔ conjSubgroup α U) := by
    rw [QuotientGroup.ker_mk']
    intro z hz
    have h1 : (z : G) ∈ omegaOneSub U ⊔ omegaOneSub (conjSubgroup α U) :=
      Subgroup.mem_subgroupOf.mp hz
    rw [hNe] at h1
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left h1)
  have hidx := Subgroup.index_map_eq (S.subgroupOf (U ⊔ conjSubgroup α U)) hπ hker
  have hCS : ((conjSubgroup x U).subgroupOf (U ⊔ conjSubgroup α U)).map
      (QuotientGroup.mk' ((omegaOneSub U ⊔
        omegaOneSub (conjSubgroup α U)).subgroupOf (U ⊔ conjSubgroup α U))) ≤
          (S.subgroupOf (U ⊔ conjSubgroup α U)).map (QuotientGroup.mk' ((omegaOneSub U ⊔
            omegaOneSub (conjSubgroup α U)).subgroupOf (U ⊔ conjSubgroup α U))) :=
    Subgroup.map_mono fun z hz =>
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hz))
  have hdvd := Subgroup.index_dvd_of_le hCS
  have hcard1 := card_map_mk_mul
    (N := omegaOneSub U ⊔ omegaOneSub (conjSubgroup α U)) hCX
  have hinf : conjSubgroup x U ⊓ (omegaOneSub U ⊔
      omegaOneSub (conjSubgroup α U)) = omegaOneSub (conjSubgroup x U) := by
    rw [hNe]
    exact D.inf_N hCen hU
  rw [hinf] at hcard1
  have hC₀card : Nat.card ↥(omegaOneSub (conjSubgroup x U)) = 2 ^ f := by
    rw [omegaOneSub_conj K.comm x, card_conjSubgroup, hce, hrel]
  have hCcard : Nat.card ↥(conjSubgroup x U) = 2 ^ f * 2 ^ f := by
    have h1 := Subgroup.relIndex_mul_card (omegaOneSub U) U
    rw [inf_of_le_left (omegaOneSub_le U), hrel, hce, hrel] at h1
    rw [card_conjSubgroup, ← h1]
  rw [hC₀card, hCcard] at hcard1
  have hCbar := Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 2 ^ f) hcard1
  have hXbar : Nat.card (↥(U ⊔ conjSubgroup α U) ⧸ (omegaOneSub U ⊔
      omegaOneSub (conjSubgroup α U)).subgroupOf (U ⊔ conjSubgroup α U)) =
        2 ^ f * ((2 ^ f) ^ 2 - 1) := by
    rw [Nat.card_congr (e.trans pslMulEquivSL).toEquiv, card_SL_two_galoisField (by omega)]
  have hCidx : (((conjSubgroup x U).subgroupOf (U ⊔ conjSubgroup α U)).map
      (QuotientGroup.mk' ((omegaOneSub U ⊔
        omegaOneSub (conjSubgroup α U)).subgroupOf (U ⊔ conjSubgroup α U)))).index =
          (2 ^ f) ^ 2 - 1 := by
    have h1 := Subgroup.card_mul_index (((conjSubgroup x U).subgroupOf (U ⊔ conjSubgroup α U)).map
      (QuotientGroup.mk' ((omegaOneSub U ⊔
        omegaOneSub (conjSubgroup α U)).subgroupOf (U ⊔ conjSubgroup α U))))
    rw [hCbar, hXbar] at h1
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
  have hodd : Odd ((2 ^ f) ^ 2 - 1) := by
    have h4 : Even ((2 ^ f) ^ 2) :=
      Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, by omega⟩, two_ne_zero⟩
    have h1 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    obtain ⟨k, hk⟩ := h4
    exact ⟨k - 1, by omega⟩
  have hoddS : Odd (S.subgroupOf (U ⊔ conjSubgroup α U)).index := by
    rw [← hidx]
    rw [hCidx] at hdvd
    exact Odd.of_dvd_nat hodd hdvd
  exact hoddS

theorem S_sq {s : G} (hs : s ∈ dS U g x) : s * s = 1 := D.sq_eq_one_of_mem_S₁ hCen hU hs

theorem S_comm {s t : G} (hs : s ∈ dS U g x) (ht : t ∈ dS U g x) : s * t = t * s := by
  have hst := S_sq D hCen hU (Subgroup.mul_mem _ hs ht)
  have hss := S_sq D hCen hU hs
  have htt := S_sq D hCen hU ht
  calc s * t = (s * t) * (s * (t * t) * s) := by rw [htt, mul_one, hss, mul_one]
    _ = ((s * t) * (s * t)) * (t * s) := by group
    _ = t * s := by rw [hst, one_mul]

theorem X_normalizes_N {z n : G} (hz : z ∈ dX U x) (hn : n ∈ dN U x) : z * n * z⁻¹ ∈ dN U x :=
  D.conj_mem_N hCen hU hz hn

theorem N_comm {m n : G} (hm : m ∈ dN U x) (hn : n ∈ dN U x) : m * n = n * m :=
  D.comm_N hCen hU hm hn

theorem N_sq {n : G} (hn : n ∈ dN U x) : n * n = 1 := D.sq_N hCen hU hn

theorem cent_C {c n : G} (hc : c ∈ conjSubgroup x U) (hc0 : c ∉ omegaOneSub (conjSubgroup x U))
    (hn : n ∈ dN U x) (hcn : c * n = n * c) : n ∈ omegaOneSub (conjSubgroup x U) := by
  have hn' : n ∈ omegaOneSub U ⊔ omegaOneSub (conjSubgroup α U) := by
    rw [D.N_eq hCen hU D.mem D.ne_one]
    exact hn
  exact D.pair.cent_conj hCen hU D.memX hc hc0 hn' hcn

theorem cent_U {u n : G} (hu : u ∈ U) (hu0 : u ∉ omegaOneSub U) (hn : n ∈ dN U x)
    (hun : u * n = n * u) : n ∈ omegaOneSub U := by
  have hn' : n ∈ omegaOneSub U ⊔ omegaOneSub (conjSubgroup α U) := by
    rw [D.N_eq hCen hU D.mem D.ne_one]
    exact hn
  exact D.pair.cent hCen hU hu hu0 hn' hun

theorem exists_S_not_N : ∃ t ∈ dS U g x, t ∉ dN U x := by
  by_contra hcon
  push Not at hcon
  obtain ⟨c, hc, hc0⟩ := exists_C_not_C0 D
  apply hc0
  have hcS2 : c ∈ dS2 U x := Subgroup.mem_sup_right hc
  obtain ⟨n, hn, s, hs, hcns⟩ := D.exists_eq_mul hCen hU hcS2
  have hcN : c ∈ dN U x := by
    rw [hcns]
    exact Subgroup.mul_mem _ hn (hcon s hs)
  have := D.inf_N hCen hU
  have hmem : c ∈ conjSubgroup x U ⊓ dN U x := Subgroup.mem_inf.mpr ⟨hc, hcN⟩
  rwa [this] at hmem

theorem cent_S2_S {z : G} (hz : z ∈ dS2 U x) (hzS : ∀ t ∈ dS U g x, z * t = t * z) :
    z ∈ dS U g x := by
  obtain ⟨n, hn, s', hs', rfl⟩ := D.exists_eq_mul hCen hU hz
  have hnS : ∀ t ∈ dS U g x, n * t = t * n := by
    intro t ht
    have h1 := hzS t ht
    have h2 := S_comm D hCen hU hs' ht
    calc n * t = n * s' * t * s'⁻¹ := by
          rw [mul_assoc n s' t, h2]
          group
      _ = t * (n * s') * s'⁻¹ := by rw [h1]
      _ = t * n := by group
  obtain ⟨t, htS, htN⟩ := exists_S_not_N D hCen hU
  have htS2 : t ∈ dS2 U x := (Subgroup.mem_inf.mp htS).1
  obtain ⟨nt, hnt, c, hc, hteq⟩ := exists_mul_of_mem_sup
    (le_trans le_sup_right (D.le_normalizer hCen hU)) htS2
  have hc0 : c ∉ omegaOneSub (conjSubgroup x U) := fun h0 => htN (by
    rw [hteq]
    exact Subgroup.mul_mem _ hnt
      ((show omegaOneSub (conjSubgroup x U) ≤ dN U x from le_sup_right) h0))
  have hnc : c * n = n * c := by
    have h1 := hnS t htS
    rw [hteq] at h1
    have h3 := N_comm D hCen hU hn hnt
    have h4 : nt * (n * c) = nt * (c * n) := by
      calc nt * (n * c) = (nt * n) * c := by group
        _ = (n * nt) * c := by rw [h3]
        _ = n * (nt * c) := by group
        _ = (nt * c) * n := h1
        _ = nt * (c * n) := by group
    exact (mul_left_cancel h4).symm
  have hnC0 := cent_C D hCen hU hc hc0 hn hnc
  have hnS' : n ∈ dS U g x := by
    refine Subgroup.mem_inf.mpr ⟨dN_le_dS2 U x hn, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
    exact (D.comm_C₀_A₀ hCen hU ha hnC0)
  exact Subgroup.mul_mem _ hnS' hs'

theorem inner {a : G} (ha : a ∈ omegaOneSub (conjSubgroup g U)) :
    ∃ s ∈ dS U g x, ∃ m ∈ dN U x, ∀ z ∈ dX U x, a * z * a⁻¹ = (s * m) * z * (s * m)⁻¹ := by
  classical
  by_cases ha1 : a = 1
  · subst ha1
    exact ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, fun z _ => by simp⟩
  have hodd : Odd ((dS2 U x).subgroupOf (dX U x)).index := by
    have h := odd_index D hCen hU
    have hXe := D.sup_eq hCen hU D.mem D.ne_one
    rw [hXe] at h
    exact h
  obtain ⟨c, hcC, hcn, hcz⟩ := D.act hCen hU ha
  obtain ⟨n1, hn1, s1, hs1, hc⟩ := D.exists_eq_mul hCen hU
    (Subgroup.mem_sup_right hcC : c ∈ dS2 U x)
  have hs1X : s1 ∈ dX U x := dS2_le_dX U x (dS_le_dS2 U g x hs1)
  have hs1a : a * s1 = s1 * a :=
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hs1).2 a ha
  have hyN : ∀ n ∈ dN U x, s1⁻¹ * a * n * (s1⁻¹ * a)⁻¹ = n := by
    intro n hn
    have h1 := hcn n hn
    have h2 : s1 * n * s1⁻¹ ∈ dN U x := X_normalizes_N D hCen hU hs1X hn
    have h3 : n1 * (s1 * n * s1⁻¹) * n1⁻¹ = s1 * n * s1⁻¹ := by
      have := N_comm D hCen hU hn1 h2
      calc n1 * (s1 * n * s1⁻¹) * n1⁻¹ = ((s1 * n * s1⁻¹) * n1) * n1⁻¹ := by rw [this]
        _ = s1 * n * s1⁻¹ := by group
    calc s1⁻¹ * a * n * (s1⁻¹ * a)⁻¹ = s1⁻¹ * (a * n * a⁻¹) * s1 := by group
      _ = s1⁻¹ * (c * n * c⁻¹) * s1 := by rw [h1]
      _ = s1⁻¹ * (n1 * (s1 * n * s1⁻¹) * n1⁻¹) * s1 := by rw [hc]; group
      _ = s1⁻¹ * (s1 * n * s1⁻¹) * s1 := by rw [h3]
      _ = n := by group
  have hyX : ∀ z ∈ dX U x, s1⁻¹ * a * z * (s1⁻¹ * a)⁻¹ * z⁻¹ ∈ dN U x := by
    intro z hz
    have hw := hcz z hz
    have e : s1⁻¹ * a * z * (s1⁻¹ * a)⁻¹ * z⁻¹ =
        (s1⁻¹ * n1 * s1) * (z * (s1⁻¹ * n1⁻¹ * ((c * z * c⁻¹)⁻¹ * (a * z * a⁻¹)) * s1) * z⁻¹) := by
      rw [hc]
      group
    rw [e]
    have hn' : s1⁻¹ * n1 * s1 ∈ dN U x := by
      have := X_normalizes_N D hCen hU ((dX U x).inv_mem hs1X) hn1
      simpa using this
    have hn'' : s1⁻¹ * n1⁻¹ * ((c * z * c⁻¹)⁻¹ * (a * z * a⁻¹)) * s1 ∈ dN U x := by
      have h1 : s1⁻¹ * (n1⁻¹ * ((c * z * c⁻¹)⁻¹ * (a * z * a⁻¹))) * s1⁻¹⁻¹ ∈ dN U x :=
        X_normalizes_N D hCen hU ((dX U x).inv_mem hs1X)
          (Subgroup.mul_mem _ ((dN U x).inv_mem hn1) hw)
      simpa [mul_assoc] using h1
    exact Subgroup.mul_mem _ hn' (X_normalizes_N D hCen hU hz hn'')
  have hyS : ∀ s ∈ dS2 U x, s1⁻¹ * a * s * (s1⁻¹ * a)⁻¹ = s := by
    intro s hs
    obtain ⟨n, hn, s', hs', rfl⟩ := D.exists_eq_mul hCen hU hs
    have has' : a * s' = s' * a :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hs').2 a ha
    have hss' : s1 * s' = s' * s1 := S_comm D hCen hU hs1 hs'
    have h1 : s1⁻¹ * a * s' * (s1⁻¹ * a)⁻¹ = s' := by
      calc s1⁻¹ * a * s' * (s1⁻¹ * a)⁻¹ = s1⁻¹ * (a * s') * a⁻¹ * s1 := by group
        _ = s1⁻¹ * (s' * a) * a⁻¹ * s1 := by rw [has']
        _ = s1⁻¹ * s' * s1 := by group
        _ = s' := by
          calc s1⁻¹ * s' * s1 = s1⁻¹ * (s' * s1) := by group
            _ = s1⁻¹ * (s1 * s') := by rw [hss']
            _ = s' := by group
    calc s1⁻¹ * a * (n * s') * (s1⁻¹ * a)⁻¹
        = (s1⁻¹ * a * n * (s1⁻¹ * a)⁻¹) * (s1⁻¹ * a * s' * (s1⁻¹ * a)⁻¹) := by group
      _ = n * s' := by rw [hyN n hn, h1]
  obtain ⟨m, hm, hmz⟩ := exists_inner_of_trivial_action (X := dX U x) (N := dN U x)
    (S₂ := dS2 U x) (y := s1⁻¹ * a) (dN_le_dX U x)
    (fun z hz n hn => X_normalizes_N D hCen hU hz hn)
    (fun m hm n hn => N_comm D hCen hU hm hn) (fun n hn => N_sq D hCen hU hn) hodd hyX hyS
  refine ⟨s1, hs1, m, hm, fun z hz => ?_⟩
  calc a * z * a⁻¹ = s1 * ((s1⁻¹ * a) * z * (s1⁻¹ * a)⁻¹) * s1⁻¹ := by group
    _ = s1 * (m * z * m⁻¹) * s1⁻¹ := by rw [hmz z hz]
    _ = (s1 * m) * z * (s1 * m)⁻¹ := by group

theorem inner_mem_S {a : G} (ha : a ∈ omegaOneSub (conjSubgroup g U)) :
    ∃ y ∈ dS U g x, ∀ z ∈ dX U x, a * z * a⁻¹ = y * z * y⁻¹ := by
  obtain ⟨s, hs, m, hm, h⟩ := inner D hCen hU ha
  have hyS2 : s * m ∈ dS2 U x := Subgroup.mul_mem _ (dS_le_dS2 U g x hs) (dN_le_dS2 U x hm)
  have hcent : ∀ t ∈ dS U g x, (s * m) * t = t * (s * m) := by
    intro t ht
    have htX : t ∈ dX U x := dS2_le_dX U x (dS_le_dS2 U g x ht)
    have h1 := h t htX
    have h2 : a * t * a⁻¹ = t := by
      have := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp ht).2 a ha
      rw [this]
      group
    rw [h2] at h1
    calc (s * m) * t = (s * m) * t * (s * m)⁻¹ * (s * m) := by group
      _ = t * (s * m) := by rw [← h1]
  exact ⟨s * m, cent_S2_S D hCen hU hyS2 hcent, h⟩

theorem center_X {z : G} (hz : z ∈ dX U x) (hzc : ∀ w ∈ dX U x, z * w = w * z) : z = 1 := by
  classical
  obtain ⟨f, hf, hrel, hNn, ⟨e⟩⟩ := D.linear hCen hU
  have hXe := D.sup_eq hCen hU D.mem D.ne_one
  have hNe := D.N_eq hCen hU D.mem D.ne_one
  have hzα : z ∈ U ⊔ conjSubgroup α U := by
    rw [hXe]
    exact hz
  let φ := e.trans pslMulEquivSL
  let π := QuotientGroup.mk' ((omegaOneSub U ⊔ omegaOneSub (conjSubgroup α U)).subgroupOf
    (U ⊔ conjSubgroup α U))
  have hcen : φ (π ⟨z, hzα⟩) ∈ Subgroup.center SL(2, GaloisField 2 f) := by
    rw [Subgroup.mem_center_iff]
    intro B
    obtain ⟨w, hw⟩ := (QuotientGroup.mk'_surjective _) (φ.symm B)
    have hwX : (w : G) ∈ U ⊔ conjSubgroup x U := by
      rw [← hXe]
      exact w.2
    have hcomm : (⟨z, hzα⟩ : ↥(U ⊔ conjSubgroup α U)) * w = w * ⟨z, hzα⟩ :=
      Subtype.ext (hzc w hwX)
    have hB : φ (π w) = B := by
      show φ ((QuotientGroup.mk' _) w) = B
      rw [hw, MulEquiv.apply_symm_apply]
    calc B * φ (π ⟨z, hzα⟩) = φ (π w) * φ (π ⟨z, hzα⟩) := by rw [hB]
      _ = φ (π (w * ⟨z, hzα⟩)) := by simp only [map_mul]
      _ = φ (π (⟨z, hzα⟩ * w)) := by rw [hcomm]
      _ = φ (π ⟨z, hzα⟩) * φ (π w) := by simp only [map_mul]
      _ = φ (π ⟨z, hzα⟩) * B := by rw [hB]
  rw [center_sl2_eq_bot, Subgroup.mem_bot] at hcen
  have h1 : π ⟨z, hzα⟩ = 1 := φ.injective (by rw [hcen, map_one])
  have hzN : z ∈ dN U x := by
    have h2 := (QuotientGroup.eq_one_iff _).mp h1
    rw [Subgroup.mem_subgroupOf, hNe] at h2
    exact h2
  obtain ⟨c, hc, hc0⟩ := exists_C_not_C0 D
  have hzC := cent_C D hCen hU hc hc0 hzN (hzc c (C_le_dX U x hc)).symm
  obtain ⟨u, hu, hu0⟩ := exists_U_not_U0 D
  have hzU := cent_U D hCen hU hu hu0 hzN (hzc u (U_le_dX U x hu)).symm
  have hmem : z ∈ U ⊓ conjSubgroup x U :=
    Subgroup.mem_inf.mpr ⟨omegaOneSub_le U hzU, omegaOneSub_le _ hzC⟩
  rwa [D.inf_UC, Subgroup.mem_bot] at hmem

theorem A0_le_normalizer_X :
    omegaOneSub (conjSubgroup g U) ≤ Subgroup.normalizer (dX U x : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro z
  obtain ⟨y, hyS, hy⟩ := inner_mem_S D hCen hU ha
  have hyX : y ∈ dX U x := dS2_le_dX U x (dS_le_dS2 U g x hyS)
  have haa : a * a = 1 := D.core.sq_omega ha
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  constructor
  · intro hz
    rw [hy z hz]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hyX hz) ((dX U x).inv_mem hyX)
  · intro hz
    have h1 := hy _ hz
    have h2 : a * (a * z * a⁻¹) * a⁻¹ = z := by
      rw [hai]
      calc a * (a * z * a) * a = (a * a) * z * (a * a) := by group
        _ = z := by rw [haa]; group
    rw [h2] at h1
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hyX hz) ((dX U x).inv_mem hyX)

end Inner

end Certificates34

end Data31Level

end CFSG.CGT.PushingUpLit.SolKR2
