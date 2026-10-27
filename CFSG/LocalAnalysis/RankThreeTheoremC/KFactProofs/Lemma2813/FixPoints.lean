module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813.Transv
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813.CountDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813

open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family

section CT

variable {M : Type} [AddCommGroup M] [Finite M] [DistribMulAction GL32 M]

theorem fix_mem_fixSub_map_conj (g : GL32) (H : Subgroup GL32) (m : M) :
    m ∈ fixSub M (H.map (MulAut.conj g).toMonoidHom) ↔ g⁻¹ • m ∈ fixSub M H := by
  rw [mem_fixSub, mem_fixSub]
  constructor
  · intro hm h hh
    have h1 := hm (g * h * g⁻¹) ⟨h, hh, by simp⟩
    calc h • g⁻¹ • m = g⁻¹ • (g * h * g⁻¹) • m := by simp [smul_smul, mul_assoc]
      _ = g⁻¹ • m := by rw [h1]
  · intro hm k hk
    obtain ⟨h, hh, rfl⟩ := hk
    have h1 := hm h hh
    calc (MulAut.conj g).toMonoidHom h • m = g • h • g⁻¹ • m := by simp [smul_smul, mul_assoc]
      _ = g • g⁻¹ • m := by rw [h1]
      _ = m := by simp [smul_smul]

theorem card_fixSub_conj (g : GL32) (H : Subgroup GL32) :
    Nat.card (fixSub M (H.map (MulAut.conj g).toMonoidHom)) = Nat.card (fixSub M H) := by
  refine Nat.card_congr ?_
  refine
    { toFun := fun m => ⟨g⁻¹ • m.1, (fix_mem_fixSub_map_conj g H m.1).1 m.2⟩
      invFun := fun m => ⟨g • m.1, ?_⟩
      left_inv := fun m => ?_
      right_inv := fun m => ?_ }
  · rw [fix_mem_fixSub_map_conj, inv_smul_smul]
    exact m.2
  · ext
    simp
  · ext
    simp

theorem card_fixSub_Spt {p q : V3} (hp : p ≠ 0) (hq : q ≠ 0) :
    Nat.card (fixSub M (Spt p)) = Nat.card (fixSub M (Spt q)) := by
  obtain ⟨g, hg⟩ := exists_act hp hq
  rw [← card_fixSub_conj (M := M) g (Spt p), Spt_conj, hg]

theorem card_fixSub_pair {p q p' q' : V3} (hp : p ≠ 0) (hq : q ≠ 0) (hp' : p' ≠ 0) (hq' : q' ≠ 0)
    (hpq : p ≠ q) (hpq' : p' ≠ q') :
    Nat.card (fixSub M (Spt p ⊔ Spt q)) = Nat.card (fixSub M (Spt p' ⊔ Spt q')) := by
  obtain ⟨g, hg1, hg2⟩ := exists_act_pair hp hq hp' hq' hpq hpq'
  rw [← card_fixSub_conj (M := M) g (Spt p ⊔ Spt q), Subgroup.map_sup, Spt_conj, Spt_conj, hg1, hg2]

theorem fixSub_sup (H K : Subgroup GL32) :
    fixSub M (H ⊔ K) = fixSub M H ⊓ fixSub M K := by
  ext m
  rw [AddSubgroup.mem_inf]
  have key : ∀ L : Subgroup GL32, m ∈ fixSub M L ↔ L ≤ MulAction.stabilizer GL32 m := by
    intro L
    rw [mem_fixSub]
    constructor
    · intro h g hg
      exact MulAction.mem_stabilizer_iff.2 (h g hg)
    · intro h g hg
      exact MulAction.mem_stabilizer_iff.1 (h hg)
  rw [key, key, key, sup_le_iff]

theorem fixSub_mono {H K : Subgroup GL32} (h : H ≤ K) : fixSub M K ≤ fixSub M H := by
  intro m hm
  rw [mem_fixSub] at hm ⊢
  intro g hg
  exact hm g (h hg)

theorem card_addSubgroup_pow_two (h2 : ∀ m : M, m + m = 0) (B : AddSubgroup M) :
    ∃ k : ℕ, Nat.card B = 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx : ∀ x : B, x + x = 0 := fun x => Subtype.ext (h2 x.1)
  have hB : IsPGroup 2 (Multiplicative B) := by
    intro g
    refine ⟨1, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, pow_one, two_nsmul]
    exact hx _
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hB
  exact ⟨k, (Nat.card_congr (Multiplicative.toAdd : Multiplicative B ≃ B)).symm.trans hk⟩

theorem two_dvd_card_fixSub (h2 : ∀ m : M, m + m = 0) (hne : ∃ m : M, m ≠ 0) {H : Subgroup GL32}
    (hH : IsPGroup 2 H) : 2 ∣ Nat.card (fixSub M H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := hH.card_modEq_card_fixedPoints M
  have hfix : Nat.card (MulAction.fixedPoints H M) = Nat.card (fixSub M H) := by
    refine Nat.card_congr (Equiv.subtypeEquivRight ?_)
    intro m
    rw [mem_fixSub, MulAction.mem_fixedPoints]
    constructor
    · intro hm g hg
      exact hm ⟨g, hg⟩
    · intro hm g
      exact hm g g.2
  have hMeven : 2 ∣ Nat.card M := by
    obtain ⟨k, hk⟩ := card_addSubgroup_pow_two (M := M) h2 ⊤
    have hk' : Nat.card M = 2 ^ k := by
      rw [← hk]
      exact (Nat.card_congr (AddSubgroup.topEquiv).toEquiv).symm
    obtain ⟨m, hm⟩ := hne
    have hk0 : k ≠ 0 := by
      rintro rfl
      have h1 : Nat.card M = 1 := by simpa using hk'
      obtain ⟨hu⟩ := Nat.card_eq_one_iff_unique.1 h1
      exact hm (Subsingleton.elim m 0)
    rw [hk']
    exact dvd_pow_self 2 hk0
  rw [← hfix]
  exact (hmod.dvd_iff dvd_rfl).1 hMeven

theorem fix_card_sup_mul_card_inf (A B : AddSubgroup M) :
    Nat.card (A ⊔ B : AddSubgroup M) * Nat.card (A ⊓ B : AddSubgroup M) =
      Nat.card A * Nat.card B := by
  have h1 := AddSubgroup.relIndex_mul_card B (A ⊔ B)
  have h2 := AddSubgroup.relIndex_mul_card B A
  rw [inf_eq_left.2 le_sup_right, AddSubgroup.relIndex_sup_right] at h1
  rw [inf_comm] at h2
  rw [← h1, ← h2]
  ring

theorem card_inf_ge (A B : AddSubgroup M) :
    Nat.card A * Nat.card B ≤ Nat.card M * Nat.card (A ⊓ B : AddSubgroup M) := by
  rw [← fix_card_sup_mul_card_inf]
  exact Nat.mul_le_mul_right _ (Nat.card_le_card_of_injective _ Subtype.val_injective)

theorem mem_fixSub_zpowers {d : GL32} {m : M} : m ∈ fixSub M (zpowers d) ↔ d • m = m := by
  constructor
  · intro h
    exact h d (mem_zpowers d)
  · intro h
    have hle : zpowers d ≤ MulAction.stabilizer GL32 m := by
      rw [zpowers_le]
      exact MulAction.mem_stabilizer_iff.2 h
    intro g hg
    exact MulAction.mem_stabilizer_iff.1 (hle hg)

theorem smul_mem_fixSub_Spt {d : GL32} {p : V3} (hdp : act d p = p) {m : M}
    (hm : m ∈ fixSub M (Spt p)) : d • m ∈ fixSub M (Spt p) := by
  have hdp' : act d⁻¹ p = p := by
    have := congrArg (act d⁻¹) hdp
    rw [act_inv_act] at this
    exact this.symm
  rw [mem_fixSub] at hm ⊢
  intro s hs
  have hs' : d⁻¹ * s * d ∈ Spt p := by
    rw [mem_Spt]
    intro x
    rw [act_mul, act_mul]
    rcases (mem_Spt.1 hs) (act d x) with h | h
    · left
      rw [h, act_inv_act]
    · right
      rw [h, act_add, hdp', act_inv_act]
  calc s • d • m = d • (d⁻¹ * s * d) • m := by simp [smul_smul, mul_assoc]
    _ = d • m := by rw [hm _ hs']

theorem Pset_smul (g : GL32) (w : M) (x : V3) : x ∈ Pset M (g • w) ↔ act g⁻¹ x ∈ Pset M w := by
  rw [mem_Pset, mem_Pset]
  have h0 : x ≠ 0 ↔ act g⁻¹ x ≠ 0 := by
    rw [Ne, Ne, act_eq_zero_iff]
  have h1 : g • w ∈ fixSub M (Spt x) ↔ w ∈ fixSub M (Spt (act g⁻¹ x)) := by
    rw [← Spt_conj, fix_mem_fixSub_map_conj, inv_inv]
  exact and_congr h0 h1

theorem fix_smul_cube {d : GL32} (hd : orderOf d = 3) (m : M) : d • d • d • m = m := by
  have hd3 : d ^ 3 = 1 := by
    have := pow_orderOf_eq_one d
    rwa [hd] at this
  rw [← mul_smul, ← mul_smul]
  have : d * d * d = 1 := by
    rw [← pow_three']
    exact hd3
  rw [this, one_smul]

theorem fix_commSub_eq_range {d : GL32} (hd : orderOf d = 3) :
    ∃ f : M →+ M, (∀ m, f m = d • m - m) ∧ commSub M (zpowers d) = f.range := by
  obtain ⟨f, hf⟩ : ∃ f : M →+ M, ∀ m, f m = d • m - m :=
    ⟨DistribSMul.toAddMonoidHom M d - AddMonoidHom.id M, fun m => by simp⟩
  refine ⟨f, hf, ?_⟩
  have hnat : ∀ n : ℕ, ∀ m : M, d ^ n • m - m ∈ f.range := by
    intro n
    induction n with
    | zero =>
      intro m
      simp
    | succ n ih =>
      intro m
      have : d ^ (n + 1) • m - m = (d ^ n • (d • m) - d • m) + f m := by
        rw [hf, pow_succ, mul_smul]
        abel
      rw [this]
      exact AddSubgroup.add_mem _ (ih (d • m)) ⟨m, rfl⟩
  apply le_antisymm
  · apply (AddSubgroup.closure_le _).2
    rintro x ⟨g, hg, m, rfl⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hg
    have hk : d ^ k = d ^ (k % 3).toNat := by
      have h := zpow_mod_orderOf d k
      rw [hd] at h
      rw [← zpow_natCast, Int.toNat_of_nonneg (by omega)]
      simpa using h.symm
    rw [hk]
    exact hnat _ m
  · rintro x ⟨m, rfl⟩
    rw [hf]
    exact AddSubgroup.subset_closure ⟨d, mem_zpowers d, m, rfl⟩

theorem commSub_inf_fixSub (h2 : ∀ m : M, m + m = 0) {d : GL32} (hd : orderOf d = 3) :
    commSub M (zpowers d) ⊓ fixSub M (zpowers d) = ⊥ := by
  obtain ⟨f, hf, hRc⟩ := fix_commSub_eq_range (M := M) hd
  have hneg : ∀ m : M, -m = m := fun m => neg_eq_of_add_eq_zero_left (h2 m)
  have hsub : ∀ a b : M, a - b = a + b := fun a b => by rw [sub_eq_add_neg, hneg]
  rw [hRc, eq_bot_iff]
  rintro x ⟨⟨m, rfl⟩, hxE⟩
  rw [AddSubgroup.mem_bot]
  have hxE' : d • f m = f m := mem_fixSub_zpowers.1 hxE
  rw [hf, smul_sub, hsub, hsub] at hxE'
  rw [hf]
  have h1 : d • d • m = m := by
    have : d • d • m + d • m = m + d • m := by rw [hxE', add_comm]
    exact add_right_cancel this
  have h2' : d • m = m := by
    have : d • d • d • m = d • m := congrArg (fun y => d • y) h1
    rw [fix_smul_cube hd] at this
    exact this.symm
  rw [h2', sub_self]

theorem commSub_card_mul (h2 : ∀ m : M, m + m = 0) {d : GL32} (hd : orderOf d = 3) :
    Nat.card (commSub M (zpowers d)) * Nat.card (fixSub M (zpowers d)) = Nat.card M := by
  obtain ⟨f, hf, hRc⟩ := fix_commSub_eq_range (M := M) hd
  have hneg : ∀ m : M, -m = m := fun m => neg_eq_of_add_eq_zero_left (h2 m)
  have hsub : ∀ a b : M, a - b = a + b := fun a b => by rw [sub_eq_add_neg, hneg]
  have hinf := commSub_inf_fixSub h2 hd
  have hsup : commSub M (zpowers d) ⊔ fixSub M (zpowers d) = ⊤ := by
    rw [eq_top_iff]
    intro m _
    have hn : m + d • m + d • d • m ∈ fixSub M (zpowers d) := by
      rw [mem_fixSub_zpowers, smul_add, smul_add, fix_smul_cube hd]
      abel
    have hm : m = f (d • m) + (m + d • m + d • d • m) := by
      rw [hf, hsub]
      calc m = m + (d • m + d • m) + (d • d • m + d • d • m) := by
            rw [h2, h2, add_zero, add_zero]
        _ = _ := by abel
    have hmem : f (d • m) ∈ commSub M (zpowers d) := by
      rw [hRc]
      exact ⟨d • m, rfl⟩
    rw [hm]
    exact AddSubgroup.add_mem_sup hmem hn
  have hcard := fix_card_sup_mul_card_inf (commSub M (zpowers d)) (fixSub M (zpowers d))
  rw [hsup, hinf, AddSubgroup.card_top, AddSubgroup.card_bot, mul_one] at hcard
  exact hcard.symm

end CT

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813
