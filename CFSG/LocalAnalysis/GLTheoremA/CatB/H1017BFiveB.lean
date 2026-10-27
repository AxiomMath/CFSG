module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017BFiveDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017BFiveA
public import CFSG.RankThree.Native.FiveLocalForms

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Blueprint CFSG.Monster.B.Pinned Subgroup
open scoped Pointwise

section Generic

variable {G : Type*} [Group G]

private theorem map_conj_le_centralizer (g : G) {F W : Subgroup G}
    (hFW : F ≤ centralizer (W : Set G)) :
    F.map (MulAut.conj g).toMonoidHom ≤
      centralizer ((W.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨y, hy, rfl⟩
  rw [← map_mul, ← map_mul, mem_centralizer_iff.1 (hFW hx) y hy]

private theorem card_map_conj (g : G) (H : Subgroup G) :
    Nat.card (H.map (MulAut.conj g).toMonoidHom) = Nat.card H :=
  card_map_of_injective (MulAut.conj g).injective

private theorem pure_map_conj (g : G) {z : G} {F : Subgroup G}
    (h : ∀ f ∈ F, f ≠ 1 → ∃ (c : ℕ) (k : G), k * z ^ c * k⁻¹ = f) :
    ∀ f ∈ F.map (MulAut.conj g).toMonoidHom, f ≠ 1 → ∃ (c : ℕ) (k : G), k * z ^ c * k⁻¹ = f := by
  rintro _ ⟨f, hf, rfl⟩ hf1
  have hf1' : f ≠ 1 := fun h1 => hf1 (by rw [h1, map_one])
  obtain ⟨c, k, hk⟩ := h f hf hf1'
  refine ⟨c, g * k, ?_⟩
  rw [← hk]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev, mul_assoc]

private theorem mem_map_conj_inv {g y f : G} {F : Subgroup G} (hf : f ∈ F)
    (hg : g * y * g⁻¹ = f) : y ∈ F.map (MulAut.conj g⁻¹).toMonoidHom :=
  ⟨f, hf, by
    rw [← hg]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group⟩

private theorem false_of_z_mem [Finite G] {z : G} {P : Subgroup G}
    (hP : ∃ S : Sylow 5 G, (S : Subgroup G) = P) (hPz : ∀ y ∈ P, y * z = z * y)
    (hB : ∀ F : Subgroup G, F ≤ P → z ∈ F → IsElemAbelian 5 F → Nat.card F = 5 ^ 2 →
      (∀ f ∈ F, f ≠ 1 → ∃ (c : ℕ) (g : G), g * z ^ c * g⁻¹ = f) →
      ∀ W : Subgroup G, IsElemAbelian 2 W → Nat.card W = 2 ^ 4 →
        F ≤ centralizer (W : Set G) → False)
    {F W : Subgroup G} (hF : IsElemAbelian 5 F) (hFc : Nat.card F = 5 ^ 2) (hzF : z ∈ F)
    (hpure : ∀ f ∈ F, f ≠ 1 → ∃ (c : ℕ) (g : G), g * z ^ c * g⁻¹ = f)
    (hW : IsElemAbelian 2 W) (hWc : Nat.card W = 2 ^ 4) (hFW : F ≤ centralizer (W : Set G)) :
    False := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hFC : F ≤ centralizer ({z} : Set G) := fun f hf => by
    have := hF.1
    exact mem_centralizer_singleton_iff.2
      (congrArg Subtype.val (mul_comm' (⟨f, hf⟩ : F) ⟨z, hzF⟩))
  obtain ⟨S, hS⟩ := hP
  have hSC : (S : Subgroup G) ≤ centralizer ({z} : Set G) := by
    rw [hS]
    exact fun y hy => mem_centralizer_singleton_iff.2 (hPz y hy)
  have hF1 : IsPGroup 5 ↥(F.subgroupOf (centralizer ({z} : Set G))) :=
    hF.isPGroup.of_equiv (subgroupOfEquivOfLe hFC).symm
  obtain ⟨Q', hQ'⟩ := hF1.exists_le_sylow
  obtain ⟨d, hd⟩ := MulAction.exists_smul_eq (centralizer ({z} : Set G)) Q' (S.subtype hSC)
  have hdP : ∀ y ∈ F, (d : G) * y * (d : G)⁻¹ ∈ P := by
    intro y hy
    have hy' : (⟨y, hFC hy⟩ : centralizer ({z} : Set G)) ∈
        (Q' : Subgroup (centralizer ({z} : Set G))) :=
      hQ' (mem_subgroupOf.2 hy)
    have := Subgroup.smul_mem_pointwise_smul _ (MulAut.conj d) _ hy'
    rw [← Sylow.coe_subgroup_smul, hd] at this
    rw [← hS]
    exact this
  have hdz : (d : G) * z = z * d := mem_centralizer_singleton_iff.1 d.2
  refine hB (F.map (MulAut.conj (d : G)).toMonoidHom) ?_ ⟨z, hzF, ?_⟩ (hF.map _)
    ((card_map_conj _ F).trans hFc) (pure_map_conj _ hpure)
    (W.map (MulAut.conj (d : G)).toMonoidHom) (hW.map _) ((card_map_conj _ W).trans hWc)
    (map_conj_le_centralizer _ hFW)
  · rintro _ ⟨y, hy, rfl⟩
    exact hdP y hy
  · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hdz, mul_inv_cancel_right]

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance (zpowers_pow_eq_of_five) in
private theorem false_of_card_eq [Finite G] {z s : G} (hz5 : orderOf z = 5)
    (hs5 : orderOf s = 5) {P : Subgroup G} (hP : ∃ S : Sylow 5 G, (S : Subgroup G) = P)
    (hPz : ∀ y ∈ P, y * z = z * y)
    (hconj : ∀ y : G, orderOf y = 5 → ∃ c : ℕ, ¬ 5 ∣ c ∧ ∃ g : G,
      g * z ^ c * g⁻¹ = y ∨ g * s ^ c * g⁻¹ = y)
    (hA : ∀ F W : Subgroup G, IsElemAbelian 5 F → Nat.card F = 5 ^ 2 → s ∈ F →
      IsElemAbelian 2 W → Nat.card W = 2 ^ 4 → F ≤ centralizer (W : Set G) → False)
    (hB : ∀ F : Subgroup G, F ≤ P → z ∈ F → IsElemAbelian 5 F → Nat.card F = 5 ^ 2 →
      (∀ f ∈ F, f ≠ 1 → ∃ (c : ℕ) (g : G), g * z ^ c * g⁻¹ = f) →
      ∀ W : Subgroup G, IsElemAbelian 2 W → Nat.card W = 2 ^ 4 →
        F ≤ centralizer (W : Set G) → False)
    {F W : Subgroup G} (hF : IsElemAbelian 5 F) (hFc : Nat.card F = 5 ^ 2)
    (hW : IsElemAbelian 2 W) (hWc : Nat.card W = 2 ^ 4) (hFW : F ≤ centralizer (W : Set G)) :
    False := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hord : ∀ f ∈ F, f ≠ 1 → orderOf f = 5 := fun f hf hf1 =>
    orderOf_eq_prime (hF.2 f hf) hf1
  by_cases hAs : ∃ f ∈ F, f ≠ 1 ∧ ∃ c : ℕ, ¬ 5 ∣ c ∧ ∃ g : G, g * s ^ c * g⁻¹ = f
  ·
    obtain ⟨f, hf, -, c, hc, g, hg⟩ := hAs
    have hs : s ∈ zpowers (s ^ c) := by
      rw [zpowers_pow_eq_of_five hs5 hc]
      exact mem_zpowers _
    exact hA _ _ (hF.map _) ((card_map_conj _ F).trans hFc)
      (zpowers_le.2 (mem_map_conj_inv hf hg) hs) (hW.map _) ((card_map_conj _ W).trans hWc)
      (map_conj_le_centralizer _ hFW)
  ·
    push Not at hAs
    have hpure : ∀ f ∈ F, f ≠ 1 → ∃ (c : ℕ) (g : G), g * z ^ c * g⁻¹ = f := by
      intro f hf hf1
      obtain ⟨c, hc, g, hg | hg⟩ := hconj f (hord f hf hf1)
      · exact ⟨c, g, hg⟩
      · exact absurd hg (hAs f hf hf1 c hc g)
    obtain ⟨⟨f, hf⟩, hf1⟩ := ne_bot_iff_exists_ne_one.1 fun hb : F = ⊥ => by
      rw [hb, card_bot] at hFc
      norm_num at hFc
    have hf1' : f ≠ 1 := fun h1 => hf1 (Subtype.ext h1)
    obtain ⟨c, hc, g, hg | hg⟩ := hconj f (hord f hf hf1')
    · have hz : z ∈ zpowers (z ^ c) := by
        rw [zpowers_pow_eq_of_five hz5 hc]
        exact mem_zpowers _
      exact false_of_z_mem hP hPz hB (hF.map _) ((card_map_conj _ F).trans hFc)
        (zpowers_le.2 (mem_map_conj_inv hf hg) hz) (pure_map_conj _ hpure) (hW.map _)
        ((card_map_conj _ W).trans hWc) (map_conj_le_centralizer _ hFW)
    · exact hAs f hf hf1' c hc g hg

end Generic

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance (sFiveA orderOf_sFiveA)


theorem false_of_five_two_four_B
    (h : BabyFiveBPureFact) (F W : Subgroup NativeSporadic.B)
    (hF : IsElemAbelian 5 F) (hFc : Nat.card F = 5 ^ 2) (hW : IsElemAbelian 2 W)
    (hWc : 2 ^ 4 ≤ Nat.card W) (hFW : F ≤ centralizer (W : Set NativeSporadic.B)) : False := by
  haveI : Finite NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  obtain ⟨W', hW'⟩ :=
    Sylow.exists_subgroup_card_pow_prime_of_le_card Nat.prime_two hW.isPGroup hWc
  have hW0W : W'.map W.subtype ≤ W := map_subtype_le W'
  refine false_of_card_eq (P := PFive) CFSG.RankThree.Native.bFiveRel.orderOf_z orderOf_sFiveA
    (CFSG.RankThree.Native.bFiveRel.P_sylow CFSG.RankThree.Native.factorization_card_B_five)
    (fun y hy => (CFSG.RankThree.Native.bFiveRel.mem_H0.1
      (CFSG.RankThree.Native.bFiveRel.P_le_H0 hy)).2)
    CFSG.HardMathSupport.Dickson.I271.tabBFive_hconj
    (fun _ _ hF hFc hsF hW hWc hFW => false_of_fiveA_B hF hFc hsF hW hWc hFW) h hF hFc
    (hW.mono hW0W) ?_ (hFW.trans (centralizer_le hW0W))
  rw [card_map_of_injective W.subtype_injective, hW']

end CFSG.LocalAnalysis.GLTheoremA.H1017
