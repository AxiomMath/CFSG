module

public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.GroupTheory.SteinbergBSFixedPointFree
public import CFSG.LocalAnalysis.RankThreeTheoremC.FPFSFitting
public import CFSG.LocalAnalysis.RankThreeTheoremC.FPFSModuleAction

public section

universe u

namespace CFSG.LocalAnalysis.RankThreeTheoremC.FPFS

open CFSG.OrderReductions.FrattiniAutomorphisms

noncomputable def frattiniAction {N : Type u} [Group N] (T : Subgroup N) [T.Normal] :
    N →* MulAut (↥T ⧸ frattini ↥T) :=
  quotientAction (frattini ↥T) (MulAut.conjNormal : N →* MulAut ↥T)

theorem frattiniAction_apply {N : Type u} [Group N] (T : Subgroup N) [T.Normal] (n : N) (t : ↥T) :
    frattiniAction T n (QuotientGroup.mk' (frattini ↥T) t) =
      QuotientGroup.mk' (frattini ↥T) (MulAut.conjNormal n t) :=
  quotientAction_apply _ _ _ _

theorem frattini_quot_comm {N : Type u} [Group N] [Finite N] (T : Subgroup N)
    (hT : IsPGroup 2 T) :
    (∀ a b : ↥T ⧸ frattini ↥T, a * b = b * a) ∧ (∀ v : ↥T ⧸ frattini ↥T, v * v = 1) := by
  obtain ⟨-, hcomm, hpow, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hT
  exact ⟨fun a b => mul_comm' a b, fun v => by rw [← sq]; exact hpow v⟩

theorem frattiniAction_eq_one_of_mem {N : Type u} [Group N] (T : Subgroup N) [T.Normal]
    (hcomm : ∀ a b : ↥T ⧸ frattini ↥T, a * b = b * a) {t : N} (ht : t ∈ T) :
    frattiniAction T t = 1 := by
  ext v
  obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective (frattini ↥T) v
  rw [frattiniAction_apply, MulAut.one_apply]
  have e : MulAut.conjNormal t s = (⟨t, ht⟩ : ↥T) * s * (⟨t, ht⟩ : ↥T)⁻¹ := Subtype.ext rfl
  rw [e, map_mul, map_mul, map_inv, mul_inv_eq_iff_eq_mul]
  exact hcomm _ _

theorem exists_pow_eq_one_of_mem_ker {N : Type u} [Group N] [Finite N] (T : Subgroup N)
    [T.Normal] (hT : IsPGroup 2 T) (hC : Subgroup.centralizer (T : Set N) ≤ T) {k : N}
    (hk : k ∈ (frattiniAction T).ker) : ∃ n : ℕ, k ^ (2 ^ n) = 1 := by
  have hker : (MulAut.conjNormal k : MulAut ↥T) ∈ (quotientAutomorphism (frattini ↥T)).ker := hk
  obtain ⟨a, ha⟩ := (CFSG.GroupTheory.frattini_automorphism_kernel hT).2 ⟨_, hker⟩
  have h1 : (MulAut.conjNormal k : MulAut ↥T) ^ (2 ^ a) = 1 := by
    simpa using congrArg Subtype.val ha
  have h2 : k ^ (2 ^ a) ∈ Subgroup.centralizer (T : Set N) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have h3 : (MulAut.conjNormal (k ^ (2 ^ a)) : MulAut ↥T) ⟨t, ht⟩ = ⟨t, ht⟩ := by
      rw [map_pow, h1]
      rfl
    have h4 := congrArg Subtype.val h3
    rw [MulAut.conjNormal_apply] at h4
    exact (mul_inv_eq_iff_eq_mul.mp h4).symm
  obtain ⟨b, hb⟩ := hT ⟨_, hC h2⟩
  refine ⟨a + b, ?_⟩
  rw [pow_add, pow_mul]
  simpa using congrArg Subtype.val hb

theorem frattiniAction_ker {N : Type u} [Group N] [Finite N] (T : Subgroup N) [T.Normal]
    (hT : IsPGroup 2 T)
    (hC : Subgroup.centralizer (T : Set N) ≤ T)
    (hO2 : ∀ W : Subgroup N, W.Normal → IsPGroup 2 W → W ≤ T) : (frattiniAction T).ker = T := by
  refine le_antisymm ?_ ?_
  · refine hO2 _ (MonoidHom.normal_ker _) ?_
    intro k
    obtain ⟨n, hn⟩ := exists_pow_eq_one_of_mem_ker T hT hC k.2
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  · intro t ht
    exact frattiniAction_eq_one_of_mem T (frattini_quot_comm T hT).1 ht

theorem frattiniAction_alpha_eq {N : Type u} [Group N] [Finite N] {V : Type u} [Group V] [Finite V]
    (hcomm : ∀ a b : V, a * b = b * a) (hexp : ∀ v : V, v * v = 1) (ρ : N →* MulAut V)
    (T : Subgroup N) (hT : IsPGroup 2 T) (hker : ρ.ker = T) (hsolv : Group.IsSolvable N)
    (hO2 : ∀ W : Subgroup N, W.Normal → IsPGroup 2 W → W ≤ T) (α : MulAut N) (β : MulAut V)
    (hcompat : ∀ n : N, β * ρ n = ρ (α n) * β) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hp : ¬ p ∣ Nat.card N) (hβp : β ^ p = 1) (hfix : ∀ v : V, β v = v → v = 1) :
    ∀ n : N, ρ (α n) = ρ n := by
  have hsurj : Function.Surjective ρ.rangeRestrict := MonoidHom.rangeRestrict_surjective ρ
  have := hsolv
  have hΓsolv : Group.IsSolvable ρ.range := Group.isSolvable_of_surjective hsurj
  have hO2Γ : CFSG.pCore 2 ρ.range = ⊥ := by
    have hWn : ((CFSG.pCore 2 ρ.range).comap ρ.rangeRestrict).Normal :=
      CFSG.pCore_normal.comap _
    have hWp : IsPGroup 2 ((CFSG.pCore 2 ρ.range).comap ρ.rangeRestrict) := by
      refine CFSG.pCore_isPGroup.comap_of_ker_isPGroup ρ.rangeRestrict ?_
      rw [MonoidHom.ker_rangeRestrict, hker]
      exact hT
    have hWT := hO2 _ hWn hWp
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨n, rfl⟩ := hsurj g
    have hnT : n ∈ ρ.ker := by rw [hker]; exact hWT hg
    have h1 : ρ.rangeRestrict n = 1 := Subtype.ext (MonoidHom.mem_ker.mp hnT)
    rw [h1]
    exact Subgroup.one_mem _
  have hpΓ : ¬ p ∣ Nat.card ρ.range := by
    intro hd
    refine hp (hd.trans ?_)
    have e : Nat.card (N ⧸ ρ.ker) = Nat.card ρ.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker
    rw [e] at h
    exact Dvd.intro _ h.symm
  have hconj : ∀ n : N, β * ρ n * β⁻¹ = ρ (α n) := fun n =>
    mul_inv_eq_iff_eq_mul.mpr (hcompat n)
  have hx : β ∈ Subgroup.normalizer (ρ.range : Set (MulAut V)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨α n, (hconj n).symm⟩
    · rintro ⟨m, hm⟩
      obtain ⟨n, rfl⟩ := α.surjective m
      refine ⟨n, ?_⟩
      have h2 : β * ρ n * β⁻¹ = β * h * β⁻¹ := (hconj n).trans hm
      exact mul_left_cancel (mul_right_cancel h2)
  have hKL : ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ p → ∀ S : Subgroup (MulAut V), S ≤ ρ.range →
      IsPGroup q S → β ∈ Subgroup.normalizer (S : Set (MulAut V)) →
        ∀ s ∈ S, β * s = s * β := by
    intro q hq hq2 hqp S _ hS hβS
    have : Fact q.Prime := ⟨hq⟩
    exact kl_mulAut hcomm hexp hp2 hq2 hqp S hS β hβS hβp hfix
  have hcent := centralizes_of_pCores hΓsolv hO2Γ hx hβp hpΓ hKL
  intro n
  have h3 : β * ρ n = ρ n * β := hcent (ρ n) ⟨n, rfl⟩
  exact mul_right_cancel ((hcompat n).symm.trans h3)

theorem map_eq_self_of_forall_mem {N : Type u} [Group N] [Finite N] (T : Subgroup N)
    (α : MulAut N) (hαT : ∀ t ∈ T, α t ∈ T) : T.map α.toMonoidHom = T := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨t, ht, rfl⟩
    exact hαT t ht
  · rw [Subgroup.card_map_of_injective α.injective]

theorem fpfs_abstract {N : Type u} [Group N] [Finite N] (T : Subgroup N) [T.Normal]
    (hT : IsPGroup 2 T) (hsolv : Group.IsSolvable N)
    (hC : Subgroup.centralizer (T : Set N) ≤ T)
    (hO2 : ∀ W : Subgroup N, W.Normal → IsPGroup 2 W → W ≤ T) (α : MulAut N)
    (hαT : ∀ t ∈ T, α t ∈ T) {p : ℕ} [Fact p.Prime] (hp : ¬ p ∣ Nat.card N) (hαp : α ^ p = 1)
    (hfpf : ∀ t ∈ T, α t = t → t = 1) : ∀ n : N, n⁻¹ * α n ∈ T := by
  by_cases hp2 : p = 2
  · subst hp2
    have hT1 : T = ⊥ := by
      refine Subgroup.eq_bot_of_card_eq _ ?_
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT
      have hk0 : k = 0 := by
        by_contra hk0
        refine hp ?_
        have h1 : 2 ∣ Nat.card T := hk ▸ dvd_pow_self 2 hk0
        exact h1.trans (Subgroup.card_subgroup_dvd_card T)
      rw [hk, hk0, pow_zero]
    intro n
    have hn : n ∈ T := by
      refine hC ?_
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have hh' : h ∈ T := hh
      rw [hT1, Subgroup.mem_bot] at hh'
      rw [hh', one_mul, mul_one]
    exact mul_mem (inv_mem hn) (hαT n hn)
  · obtain ⟨hcomm, hexp⟩ := frattini_quot_comm T hT
    have hker := frattiniAction_ker T hT hC hO2
    have hTα := map_eq_self_of_forall_mem T α hαT
    set αT : MulAut ↥T := CFSG.GroupTheory.SteinbergBS.invariantRestrict α T hTα
    have hαTapply : ∀ t : ↥T, ((αT t : ↥T) : N) = α t := fun t => rfl
    have hαTfpf : MonoidHom.FixedPointFree ⇑αT := by
      intro t ht
      have h1 : α (t : N) = t := by rw [← hαTapply t, ht]
      exact Subtype.ext (hfpf t t.2 h1)
    have hfix : ∀ v : ↥T ⧸ frattini ↥T, quotientAutomorphism (frattini ↥T) αT v = v →
        v = 1 :=
      CFSG.GroupTheory.SteinbergBS.fixedPointFree_quotientCongr hαTfpf (frattini ↥T)
        (Subgroup.characteristic_iff_map_eq.mp inferInstance αT)
    have hαTp : αT ^ p = 1 := by
      refine MulEquiv.ext fun t => Subtype.ext ?_
      rw [CFSG.GroupTheory.SteinbergBS.coe_invariantRestrict_pow, hαp]
      rfl
    have hβp : quotientAutomorphism (frattini ↥T) αT ^ p = 1 := by
      rw [← map_pow, hαTp, map_one]
    have hcompat : ∀ n : N, quotientAutomorphism (frattini ↥T) αT * frattiniAction T n =
        frattiniAction T (α n) * quotientAutomorphism (frattini ↥T) αT := by
      intro n
      ext v
      obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective (frattini ↥T) v
      simp only [MulAut.mul_apply, frattiniAction_apply, quotientAutomorphism_apply]
      congr 1
      refine Subtype.ext ?_
      rw [hαTapply, MulAut.conjNormal_apply, MulAut.conjNormal_apply, hαTapply, map_mul, map_mul,
        map_inv]
    have hres := frattiniAction_alpha_eq hcomm hexp (frattiniAction T) T hT hker hsolv hO2 α _
      hcompat hp2 hp hβp hfix
    intro n
    have h1 : n⁻¹ * α n ∈ (frattiniAction T).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hres n]
      exact inv_mul_cancel _
    rwa [hker] at h1


theorem fpfs_subgroup {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (T N : Subgroup G)
    (x : G) (hT : IsPGroup 2 T) (hTN : T ≤ N) (hsolv : Group.IsSolvable N)
    (hNT : N ≤ Subgroup.normalizer (T : Set G)) (hC : N ⊓ Subgroup.centralizer (T : Set G) ≤ T)
    (hO2 : ∀ W : Subgroup G, W ≤ N → IsPGroup 2 W →
      N ≤ Subgroup.normalizer (W : Set G) → W ≤ T)
    (hp : ¬ p ∣ Nat.card N) (hxp : x ^ p = 1) (hxN : x ∈ Subgroup.normalizer (N : Set G))
    (hxT : x ∈ Subgroup.normalizer (T : Set G)) (hfpf : ∀ t ∈ T, x * t = t * x → t = 1) :
    ∀ n ∈ N, n⁻¹ * x⁻¹ * n * x ∈ T := by
  classical
  have hTn : (T.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTN).2 hNT
  have hT' : IsPGroup 2 (T.subgroupOf N) := hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTN).symm
  have hC' : Subgroup.centralizer ((T.subgroupOf N : Subgroup N) : Set N) ≤ T.subgroupOf N := by
    intro n hn
    rw [Subgroup.mem_subgroupOf]
    refine hC ⟨n.2, ?_⟩
    show (n : G) ∈ Subgroup.centralizer (T : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have h1 := Subgroup.mem_centralizer_iff.1 hn ⟨t, hTN ht⟩
      (by rwa [SetLike.mem_coe, Subgroup.mem_subgroupOf])
    exact congrArg Subtype.val h1
  have hO2' : ∀ W : Subgroup N, W.Normal → IsPGroup 2 W → W ≤ T.subgroupOf N := by
    intro W hW hW2
    have hWG : W.map N.subtype ≤ T := by
      refine hO2 _ ?_ (hW2.map N.subtype) ?_
      · rintro _ ⟨w, -, rfl⟩
        exact w.2
      · intro n hn
        rw [Subgroup.mem_normalizer_iff]
        intro h
        constructor
        · rintro ⟨w, hw, rfl⟩
          exact ⟨⟨n, hn⟩ * w * ⟨n, hn⟩⁻¹, hW.conj_mem w hw ⟨n, hn⟩, rfl⟩
        · rintro ⟨w, hw, hwh⟩
          refine ⟨⟨n, hn⟩⁻¹ * w * ⟨n, hn⟩, hW.conj_mem w hw ⟨n, hn⟩⁻¹ |> fun h' => ?_, ?_⟩
          · simpa using h'
          · show (n⁻¹ * (w : G) * n) = h
            rw [show (w : G) = n * h * n⁻¹ from hwh]
            group
    intro w hw
    rw [Subgroup.mem_subgroupOf]
    exact hWG ⟨w, hw, rfl⟩
  have hxinvN : x⁻¹ ∈ Subgroup.normalizer (N : Set G) := inv_mem hxN
  have hxp' : x⁻¹ ^ p = 1 := by rw [inv_pow, hxp, inv_one]
  set α : MulAut N := conjAut N x⁻¹ hxinvN with hα
  have hαT : ∀ t ∈ T.subgroupOf N, α t ∈ T.subgroupOf N := by
    intro t ht
    rw [Subgroup.mem_subgroupOf] at ht ⊢
    have : ((α t : N) : G) = x⁻¹ * (t : G) * x := by
      rw [hα, coe_conjAut, inv_inv]
    rw [this]
    have h2 := (Subgroup.mem_normalizer_iff.1 (inv_mem hxT) (t : G)).1 ht
    simpa using h2
  have hαp : α ^ p = 1 := conjAut_pow_eq_one N x⁻¹ hxinvN hxp'
  have hfpf' : ∀ t ∈ T.subgroupOf N, α t = t → t = 1 := by
    intro t ht h
    have ht' : (t : G) ∈ T := ht
    have h1 : x⁻¹ * (t : G) * x = t := by
      have := congrArg Subtype.val h
      rwa [hα, coe_conjAut, inv_inv] at this
    have h2 : x * (t : G) = (t : G) * x := by
      calc x * (t : G) = x * (x⁻¹ * (t : G) * x) := by rw [h1]
        _ = (t : G) * x := by group
    exact Subtype.ext (hfpf (t : G) ht' h2)
  have key := fpfs_abstract (T.subgroupOf N) hT' hsolv hC' hO2' α hαT hp hαp hfpf'
  intro n hn
  have h := key ⟨n, hn⟩
  rw [Subgroup.mem_subgroupOf] at h
  have : (((⟨n, hn⟩ : N)⁻¹ * α ⟨n, hn⟩ : N) : G) = n⁻¹ * x⁻¹ * n * x := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hα, coe_conjAut, inv_inv]
    simp [mul_assoc]
  rwa [this] at h

end CFSG.LocalAnalysis.RankThreeTheoremC.FPFS
