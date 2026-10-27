module

public import CFSG.Quasithin.Background.B2FactorizationBridge
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a
import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open Subgroup CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

private theorem isCyclic_sylow_three_of_pRank_le_one {N : Subgroup G}
    (hrank : CFSG.Open.pRank 3 N ≤ 1) (S₁ : Sylow 3 N) : IsCyclic (S₁ : Subgroup N) := by
  by_contra hnc
  have : Fact (IsPGroup 3 (S₁ : Subgroup N)) := ⟨S₁.isPGroup'⟩
  obtain ⟨T, -, hTcard, hTel⟩ :=
    CFSG.lemma_4_5_a (R := (S₁ : Subgroup N)) (p := 3) (by norm_num) hnc
  let f : (S₁ : Subgroup N) →* G := N.subtype.comp (S₁ : Subgroup N).subtype
  have hf : Function.Injective f := N.subtype_injective.comp (S₁ : Subgroup N).subtype_injective
  have hEl : CFSG.IsElementaryAbelian 3 (T.map f) := hTel.map f
  have hEN : T.map f ≤ N := by
    rintro _ ⟨t, -, rfl⟩
    exact (t : N).2
  have hcard : Nat.card (T.map f) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective hf, hTcard]
  have hElem : CFSG.Open.IsElemAbelian 3 (T.map f) :=
    ⟨hEl.toIsMulCommutative, fun x hx => CFSG.elemPow_eq_one_of_isElementaryAbelian x hx⟩
  have := CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) hEN hElem hcard
  omega

private theorem pow_three_eq_one_of_mem_closure_pair {Ω : Type*} [Group Ω] {c₁ c₂ : Ω}
    (h12 : c₁ * c₂ = c₂ * c₁) (h1 : c₁ ^ 3 = 1) (h2 : c₂ ^ 3 = 1) {x : Ω}
    (hx : x ∈ Subgroup.closure {c₁, c₂}) : x ^ 3 = 1 := by
  have hpair : ({c₁, c₂} : Set Ω).Pairwise Commute := by
    intro x hx y hy hxy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · exact h12
    · exact h12.symm
    · exact absurd rfl hxy
  have : IsMulCommutative (Subgroup.closure {c₁, c₂}) := Subgroup.isMulCommutative_closure hpair
  induction hx using Subgroup.closure_induction with
  | mem y hy => rcases hy with rfl | rfl <;> assumption
  | one => simp
  | mul y z hy hz ihy ihz =>
    have hyz : Commute y z :=
      congrArg Subtype.val (mul_comm' (⟨y, hy⟩ : Subgroup.closure {c₁, c₂}) ⟨z, hz⟩)
    rw [hyz.mul_pow, ihy, ihz, one_mul]
  | inv y hy ihy => rw [inv_pow, ihy, inv_one]

private theorem false_of_four_cubes {B : Type*} [Group B] [Finite B] [IsCyclic B]
    {a b c d : B} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hc : c ^ 3 = 1) (hd : d ^ 3 = 1)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    False := by
  classical
  have : Fintype B := Fintype.ofFinite B
  have hle := IsCyclic.card_pow_eq_one_le (α := B) (n := 3) (by norm_num)
  have hsub : ({a, b, c, d} : Finset B) ⊆ Finset.univ.filter fun x : B => x ^ 3 = 1 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp [*]
  have h4 : ({a, b, c, d} : Finset B).card = 4 := by
    have h1 : a ∉ ({b, c, d} : Finset B) := by simp [hab, hac, had]
    have h2 : b ∉ ({c, d} : Finset B) := by simp [hbc, hbd]
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2, Finset.card_pair hcd]
  have := Finset.card_le_card hsub
  omega

theorem two_le_pRank_of_range_eq_closure {H : Subgroup G} {Ω : Type*} [Group Ω] (f : H →* Ω)
    {c₁ c₂ : Ω} (hc : f.range = Subgroup.closure {c₁, c₂}) (h12 : c₁ * c₂ = c₂ * c₁)
    (h1 : c₁ ^ 3 = 1) (h2 : c₂ ^ 3 = 1) (h1' : c₁ ≠ 1) (h2' : c₂ ≠ 1) (h12' : c₂ ≠ c₁)
    (h12'' : c₂ ≠ c₁⁻¹) : 2 ≤ CFSG.Open.pRank 3 H := by
  by_contra hlt
  have hrank : CFSG.Open.pRank 3 H ≤ 1 := by omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcube : ∀ x ∈ f.range, x ^ 3 = 1 := fun x hx =>
    pow_three_eq_one_of_mem_closure_pair h12 h1 h2 (hc ▸ hx)
  have hsurj : Function.Surjective f.rangeRestrict := f.rangeRestrict_surjective
  have : Finite f.range := Finite.of_surjective _ hsurj
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 3 H))
  have hScyc : IsCyclic (S : Subgroup H) := isCyclic_sylow_three_of_pRank_le_one hrank S
  have htop : (S : Subgroup H).map f.rangeRestrict = ⊤ := by
    have hpg : IsPGroup 3 (⊤ : Subgroup f.range) := fun g =>
      ⟨1, Subtype.ext (Subtype.ext (by simpa using hcube _ (g : f.range).2))⟩
    exact ((S.mapSurjective hsurj).is_maximal' hpg le_top).symm
  have hcyc : IsCyclic f.range := by
    refine isCyclic_of_surjective (f.rangeRestrict.comp (S : Subgroup H).subtype) (fun y => ?_)
    obtain ⟨s, hs, rfl⟩ : y ∈ (S : Subgroup H).map f.rangeRestrict := htop ▸ Subgroup.mem_top y
    exact ⟨⟨s, hs⟩, rfl⟩
  have hm1 : c₁ ∈ f.range := by rw [hc]; exact Subgroup.subset_closure (by simp)
  have hm2 : c₂ ∈ f.range := by rw [hc]; exact Subgroup.subset_closure (by simp)
  have hne : c₁ ≠ c₁⁻¹ := by
    intro h
    apply h1'
    have hsq : c₁ * c₁ = 1 := mul_eq_one_iff_eq_inv.2 h
    calc c₁ = c₁ * c₁ * c₁ := by rw [hsq, one_mul]
      _ = c₁ ^ 3 := (pow_three' c₁).symm
      _ = 1 := h1
  refine false_of_four_cubes (B := f.range) (a := 1) (b := ⟨c₁, hm1⟩)
    (c := ⟨c₁⁻¹, f.range.inv_mem hm1⟩) (d := ⟨c₂, hm2⟩) (one_pow 3)
    (Subtype.ext h1) (Subtype.ext (by simp [inv_pow, h1])) (Subtype.ext h2)
    (fun h => h1' (congrArg Subtype.val h).symm)
    (fun h => h1' (inv_eq_one.1 (congrArg Subtype.val h).symm))
    (fun h => h2' (congrArg Subtype.val h).symm)
    (fun h => hne (congrArg Subtype.val h))
    (fun h => h12' (congrArg Subtype.val h).symm)
    (fun h => h12'' (congrArg Subtype.val h).symm)

theorem two_le_pRank_inf_centralizer_of_few_images {M E U : Subgroup G} (hEM : E ≤ M)
    (hE : IsElemAbelian 3 E) (hEcard : Nat.card E = 27) (hU : IsElemAbelian 2 U)
    (hEN : E ≤ normalizer (U : Set G)) (u : IntMod U hU)
    (hfew : {v : IntMod U hU | ∃ x : E, convHom hU E hEN x u = v}.ncard ≤ 3) :
    2 ≤ CFSG.Open.pRank 3 (M ⊓ centralizer ({u.val} : Set G)) := by
  let _ : MulAction E (IntMod U hU) := MulAction.compHom _ (convHom hU E hEN)
  have horb : Nat.card (MulAction.orbit E u) * Nat.card (MulAction.stabilizer E u) =
      Nat.card E := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup E u)
  have hcard_orb : Nat.card (MulAction.orbit E u) ≤ 3 := by
    rw [Nat.card_coe_set_eq]
    exact hfew
  let E' : Subgroup G := (MulAction.stabilizer E u).map E.subtype
  have hE'E : E' ≤ E := Subgroup.map_subtype_le _
  have hE'card : Nat.card E' = Nat.card (MulAction.stabilizer E u) :=
    Subgroup.card_map_of_injective E.subtype_injective
  have hE'le : E' ≤ M ⊓ centralizer ({u.val} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨hEM x.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have h1 : convHom hU E hEN x u = u := hx
    have h2 : (x : G) * u.val * (x : G)⁻¹ = u.val :=
      (convI_apply_val hU ⟨x, hEN x.2⟩ u).symm.trans (congrArg IntMod.val h1)
    show (x : G) * u.val = u.val * (x : G)
    calc (x : G) * u.val = (x : G) * u.val * (x : G)⁻¹ * (x : G) :=
          (inv_mul_cancel_right _ _).symm
      _ = u.val * (x : G) := by rw [h2]
  have hE'el : IsElemAbelian 3 E' := by
    have := hE.1
    exact ⟨⟨⟨fun a b => Subtype.ext (setLike_mul_comm (hE'E a.2) (hE'E b.2))⟩⟩,
      fun x hx => hE.2 x (hE'E hx)⟩
  have hdvd : Nat.card E' ∣ 3 ^ 3 := by
    have h := Subgroup.card_dvd_of_le hE'E
    rw [hEcard] at h
    simpa using h
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have h27 : 27 ≤ 3 * Nat.card (MulAction.stabilizer E u) :=
    calc 27 = Nat.card E := hEcard.symm
      _ = Nat.card (MulAction.orbit E u) * Nat.card (MulAction.stabilizer E u) := horb.symm
      _ ≤ 3 * Nat.card (MulAction.stabilizer E u) := Nat.mul_le_mul_right _ hcard_orb
  have hm2 : 2 ≤ m := by
    by_contra h
    have : 3 ^ m ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact hm2.trans (CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) hE'le hE'el hm)

end CFSG.LocalAnalysis.RankThreeUC
