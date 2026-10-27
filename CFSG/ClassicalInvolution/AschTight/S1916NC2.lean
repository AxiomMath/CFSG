module

public import CFSG.ClassicalInvolution.AschTight.S1916SCStmt
public import CFSG.ClassicalInvolution.AschTight.S1916WrAut2
public import CFSG.ClassicalInvolution.AschTight.S1911Case2a
public import CFSG.ClassicalInvolution.AschTight.S1916Sec

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1916

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G]

theorem exists_pow_mem_centralizer_of_isWreathed {A : Subgroup G} (hA : IsWreathed A)
    (hA2 : IsPGroup 2 A) {n : G} (hn : n ∈ Subgroup.normalizer (A : Set G)) :
    ∃ k : ℕ, n ^ (2 ^ k) ∈ Subgroup.centralizer (A : Set G) := by
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos n).ne'
  refine ⟨k, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
  have hdvd : 2 ^ k ∣ orderOf n := ⟨m, hkm⟩
  have hord : orderOf (n ^ (2 ^ k)) = m := by
    rw [orderOf_pow_of_dvd (by positivity) hdvd, hkm, Nat.mul_div_cancel_left _ (by positivity)]
  have hnA : conjSub (n ^ (2 ^ k)) A = A :=
    mem_normalizer_iff_conjSub_eq.mp (Subgroup.pow_mem _ hn _)
  have h1 := centralizes_of_isWreathed_of_odd hA hA2 hnA (hord ▸ hm) x hx
  calc x * n ^ 2 ^ k = n ^ 2 ^ k * x * (n ^ 2 ^ k)⁻¹ * n ^ 2 ^ k := by rw [h1]
    _ = n ^ 2 ^ k * x := by group

omit [Finite G] in
theorem isElemAbelian_conjSub {E : Subgroup G} (hE : IsElemAbelian 2 E) (g : G) :
    IsElemAbelian 2 (conjSub g E) := by
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy⟩ := y
    rw [mem_conjSub_iff] at hx hy
    have h1 := congrArg Subtype.val (hE.1.is_comm.comm ⟨_, hx⟩ ⟨_, hy⟩)
    simp only [Subgroup.coe_mul] at h1 ⊢
    calc x * y = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
      _ = y * x := by group
  · rw [mem_conjSub_iff] at hx
    have h1 := hE.2 _ hx
    calc x ^ 2 = g * (g⁻¹ * x * g) ^ 2 * g⁻¹ := by rw [_root_.sq, _root_.sq]; group
      _ = 1 := by rw [h1]; group

variable {p f : ℕ} [Fact p.Prime]

variable (p f) in
theorem not_case2_of (hSC : C19_14SCTmp p f) (hB3 : GoldschmidtB3Tmp) :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G)
      (S : Sylow 2 G) (W : Subgroup G), Sec19Data p f K z S W →
        W ⊔ sec19Y K z ≠ oddCoreOf (sec19Y K z) ⊔ W := by
  intro G _ _ _ K z S W hd h1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨L, t, V, hDT⟩ := exists_sec19DataT hd
  have hwr : IsWreathed ((S : Subgroup G) ⊓ sec19X K z) :=
    S1911.isWreathed_inf_sec19X_of_case2 hDT h1
  have hA2 : IsPGroup 2 ↥((S : Subgroup G) ⊓ sec19X K z) := S.isPGroup'.to_le inf_le_left
  have hsc : fusionStronglyClosed (((S : Subgroup G) ⊓ sec19X K z : Subgroup G) : Set G) S := by
    intro x hx g hg
    refine ⟨hg, ?_⟩
    have := hSC G K z S W hd h1 x hx g⁻¹ (by simpa using hg)
    simpa using this
  have hSyl := hB3 G S _ inf_le_left hsc fun n hn =>
    exists_pow_mem_centralizer_of_isWreathed hwr hA2 hn
  have hzK := isUniqueInvolution_of_tight hd.tight.toTightBranch
  have hzA : z ∈ (S : Subgroup G) ⊓ sec19X K z :=
    ⟨sd_mem_S hd, le_sec19X hd.tight.branch.member hzK.mem⟩
  have htop : Subgroup.normalClosure
      (((S : Subgroup G) ⊓ sec19X K z : Subgroup G) : Set G) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.normalClosure
      (((S : Subgroup G) ⊓ sec19X K z : Subgroup G) : Set G)) with h | h
    · exfalso
      have h2 : z ∈ Subgroup.normalClosure
          (((S : Subgroup G) ⊓ sec19X K z : Subgroup G) : Set G) :=
        Subgroup.subset_normalClosure hzA
      rw [h, Subgroup.mem_bot] at h2
      exact hzK.ne_one h2
    · exact h
  rw [htop] at hSyl
  have hSS : IsSylow2In (S : Subgroup G) ⊤ :=
    ⟨le_top, S.isPGroup', fun V' _ hV' hle => S.is_maximal' hV' hle⟩
  have hSX : (S : Subgroup G) ≤ sec19X K z := by
    have hcard := hSyl.natCard_eq hSS
    have heq := Subgroup.eq_of_le_of_card_ge (inf_le_left :
      (S : Subgroup G) ⊓ sec19X K z ≤ S) (by rw [hcard])
    rw [← heq]
    exact inf_le_right
  have hSRV : (S : Subgroup G) ≤ (S : Subgroup G) ⊓ K ⊔ V := by
    rw [← S1911.inf_sec19X_eq_of_case2 hDT h1]
    exact le_inf le_rfl hSX
  have hrank : twoRank G ≤ 2 := by
    refine csSup_le' fun k hk => ?_
    obtain ⟨E, -, hE, hEk⟩ := hk
    have hE2 : IsPGroup 2 E := fun x => ⟨1, by
      have := hE.2 x x.2
      exact Subtype.ext (by simpa using this)⟩
    obtain ⟨c, -, hc⟩ := exists_conj_le_of_sylow_le S le_top le_top hE2
    have h4 := S1911.card_le_four_of_le_inf_sup hDT (hc.trans hSRV) (isElemAbelian_conjSub hE c)
    rw [AscL62.natCard_conjSub, hEk] at h4
    by_contra hk
    have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have := hd.tight.branch.rank
  omega

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1916
