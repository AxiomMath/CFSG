module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiComponents
public import CFSG.Quasithin.Background.B6Defs
import CFSG.GroupTheory.PermSylowTwo.Alt
import CFSG.GroupTheory.SylowInfNormal
import CFSG.LocalAnalysis.PreuniquenessRankFour.Helpers

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.SignalizerFunctorTheorem.McBride

variable {G : Type} [Group G]

theorem isPGroup_of_isPGroup_inf {p : ℕ} {N X : Subgroup G} [N.Normal]
    (hQ : IsPGroup p (G ⧸ N)) (hXN : IsPGroup p (X ⊓ N : Subgroup G)) : IsPGroup p X := by
  intro x
  obtain ⟨k, hk⟩ := hQ (x : G)
  have hmem : (x : G) ^ p ^ k ∈ X ⊓ N :=
    ⟨pow_mem x.2 _, (QuotientGroup.eq_one_iff _).mp (by rw [QuotientGroup.mk_pow, hk])⟩
  obtain ⟨j, hj⟩ := hXN ⟨_, hmem⟩
  refine ⟨k + j, Subtype.ext ?_⟩
  have h := congrArg Subtype.val hj
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h ⊢
  rw [pow_add, pow_mul, h]

theorem twoResidual_eq_bot_of_isPGroup {X : Subgroup G} (hX : IsPGroup 2 X) :
    twoResidual X = ⊥ := by
  refine eq_bot_iff.mpr (iInf₂_le ⊥ ⟨bot_le, le_normalizer_of_normal, fun x hx => ?_⟩)
  obtain ⟨k, hk⟩ := hX ⟨x, hx⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem two_dvd_card_alternatingGroup {n : ℕ} (hn : 4 ≤ n) :
    2 ∣ Nat.card (alternatingGroup (Fin n)) := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have h := two_mul_nat_card_alternatingGroup (α := Fin n)
  rw [Nat.card_perm, Nat.card_fin] at h
  refine Nat.dvd_of_mul_dvd_mul_left zero_lt_two ?_
  rw [h]
  exact Nat.dvd_factorial (by norm_num) hn

theorem not_isPGroup_two_of_mulEquiv_alt {A : Subgroup G} {n : ℕ} (hn : 3 ≤ n)
    (e : A ≃* alternatingGroup (Fin n)) : ¬ IsPGroup 2 A := by
  intro hA
  set f : Fin 3 ↪ Fin n := Fin.castLEEmb hn
  have h3 : (Equiv.swap (f 0) (f 1) * Equiv.swap (f 0) (f 2)).IsThreeCycle :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same (f.injective.ne (by decide))
      (f.injective.ne (by decide)) (f.injective.ne (by decide))
  set c : alternatingGroup (Fin n) := ⟨_, h3.mem_alternatingGroup⟩
  obtain ⟨k, hk⟩ := hA (e.symm c)
  have hc : c ^ 2 ^ k = 1 := by simpa using congrArg e hk
  have h3d : 3 ∣ 2 ^ k := by
    rw [← h3.orderOf, show Equiv.swap (f 0) (f 1) * Equiv.swap (f 0) (f 2) = (c : Equiv.Perm _)
      from rfl, orderOf_submonoid]
    exact orderOf_dvd_of_pow_eq_one hc
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3d) (by decide)

theorem normalizer_le_normalizer_inf_of_normal {H N : Subgroup G} [N.Normal] :
    normalizer (H : Set G) ≤ normalizer ((H ⊓ N : Subgroup G) : Set G) := fun x hx =>
  inf_normalizer_le_normalizer_inf ⟨hx, le_normalizer_of_normal (H := N) (K := ⊤) (mem_top x)⟩

private theorem normalizer_le_normalizer_centralizer (J : Subgroup G) :
    normalizer (J : Set G) ≤ normalizer (centralizer (J : Set G) : Set G) :=
  le_normalizer_iff.mpr fun m hm c hc => mem_centralizer_iff.mpr fun j hj => by
    have h1 : m⁻¹ * j * m ∈ J := by
      simpa [mul_assoc] using (mem_normalizer_iff.mp (inv_mem hm) j).mp hj
    have h2 := mem_centralizer_iff.mp hc _ h1
    calc j * (m * c * m⁻¹) = m * ((m⁻¹ * j * m) * c) * m⁻¹ := by group
      _ = m * (c * (m⁻¹ * j * m)) * m⁻¹ := by rw [h2]
      _ = m * c * m⁻¹ * j := by group

theorem charTwo_normalizer_of_isSylowTwoOf {N J : Subgroup G} [N.Normal]
    (hGN : IsPGroup 2 (G ⧸ N)) (hJ : IsSylowTwoOf J N) (hNJ : N ⊓ centralizer (J : Set G) ≤ J) :
    CharTwo (normalizer (J : Set G)) ∧
      IsPGroup 2 (normalizer (J : Set G) ⊓
        centralizer (pCoreOf 2 (normalizer (J : Set G)) : Set G) : Subgroup G) := by
  set M := normalizer (J : Set G)
  have hJM : J ≤ pCoreOf 2 M := PreuniquenessRankFour.Helpers.normal_pSubgroup_le_pCoreOf 2
    le_normalizer ((normal_subgroupOf_iff_le_normalizer le_normalizer).mpr le_rfl) hJ.2.1
  have hX : IsPGroup 2 (M ⊓ centralizer (J : Set G) : Subgroup G) :=
    isPGroup_of_isPGroup_inf hGN (hJ.2.1.to_le fun x hx => hNJ ⟨hx.2, hx.1.2⟩)
  have hXn : ((M ⊓ centralizer (J : Set G)).subgroupOf M).Normal :=
    (normal_subgroupOf_iff_le_normalizer inf_le_left).mpr fun m hm =>
      inf_normalizer_le_normalizer_inf ⟨le_normalizer hm, normalizer_le_normalizer_centralizer J hm⟩
  have hC : M ⊓ centralizer (pCoreOf 2 M : Set G) ≤ M ⊓ centralizer (J : Set G) :=
    inf_le_inf_left M (centralizer_le hJM)
  exact ⟨hC.trans (PreuniquenessRankFour.Helpers.normal_pSubgroup_le_pCoreOf 2 inf_le_left hXn hX),
    hX.to_le hC⟩

variable [Finite G]

theorem odd_index_normalizer_of_isSylowTwoOf {N J : Subgroup G} [hN : N.Normal]
    (hJ : IsSylowTwoOf J N) : Odd (normalizer (J : Set G)).index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hJT⟩ := hJ.2.1.exists_le_sylow
  set T' : Subgroup G := (T : Subgroup G)
  have hTN : T' ⊓ N ≤ J := PermSylowTwo.le_of_isSylowTwoOf_of_isPGroup hJ
    (le_inf hJT hJ.1) inf_le_right (T.isPGroup'.to_le inf_le_left)
  have hT : T' ≤ normalizer (J : Set G) := by
    intro t ht
    refine mem_normalizer_iff.mpr fun x =>
      ⟨fun hx => hTN (mem_inf.mpr ⟨?_, hN.conj_mem x (hJ.1 hx) t⟩),
        fun hx => hTN (mem_inf.mpr ⟨?_, ?_⟩)⟩
    · exact mul_mem (mul_mem ht (hJT hx)) (inv_mem ht)
    · simpa [mul_assoc] using mul_mem (mul_mem (inv_mem ht) (hJT hx)) ht
    · simpa [mul_assoc] using hN.conj_mem _ (hJ.1 hx) t⁻¹
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h =>
    T.not_dvd_index (h.trans (index_dvd_of_le hT)))

theorem normalizer_ne_top_of_isSylowTwoOf {S : Set (Subgroup G)} {N J A : Subgroup G} {n : ℕ}
    (hn : 5 ≤ n) (hN : IsDirectProduct S N) (hAS : A ∈ S) (e : A ≃* alternatingGroup (Fin n))
    (hJ : IsSylowTwoOf J N) : normalizer (J : Set G) ≠ ⊤ := by
  intro htop
  have hJA : IsSylowTwoOf (A ⊓ J) A :=
    isSylowTwoOf_inf_of_normal hJ (hN.le hAS) (hN.le_normalizer hAS)
  have hnorm : ((A ⊓ J).subgroupOf A).Normal :=
    (normal_subgroupOf_iff_le_normalizer inf_le_left).mpr fun a ha =>
      inf_normalizer_le_normalizer_inf ⟨le_normalizer ha, htop ▸ mem_top a⟩
  have : IsSimpleGroup A := (MulEquiv.isSimpleGroup_congr e).mpr
    (alternatingGroup.isSimpleGroup (by simpa using hn))
  rcases hnorm.eq_bot_or_eq_top with h | h
  · apply hJA.2.2
    rw [h, index_bot, Nat.card_congr e.toEquiv]
    exact two_dvd_card_alternatingGroup (by omega)
  · refine not_isPGroup_two_of_mulEquiv_alt (by omega) e (hJ.2.1.to_le fun a ha => ?_)
    have : (⟨a, ha⟩ : A) ∈ (A ⊓ J).subgroupOf A := h ▸ mem_top _
    exact this.2

theorem inf_centralizer_le_of_isSylowTwoOf {S : Set (Subgroup G)} {N J : Subgroup G} {n : ℕ}
    (hn : 6 ≤ n) (hN : IsDirectProduct S N)
    (hA : ∀ A ∈ S, Nonempty (A ≃* alternatingGroup (Fin n))) (hJ : IsSylowTwoOf J N) :
    N ⊓ centralizer (J : Set G) ≤ J :=
  inf_centralizer_le hN fun A hAS x hx => by
    obtain ⟨e⟩ := hA A hAS
    have hJA : IsSylowTwoOf (A ⊓ J) A :=
      isSylowTwoOf_inf_of_normal hJ (hN.le hAS) (hN.le_normalizer hAS)
    refine (PermSylowTwo.inf_normalizer_le_of_mulEquiv_alt hn e hJA
      ⟨hx.1, centralizer_le_normalizer _ ?_⟩).2
    rw [inf_comm A J]
    exact hx.2

end CFSG.GroupTheory
