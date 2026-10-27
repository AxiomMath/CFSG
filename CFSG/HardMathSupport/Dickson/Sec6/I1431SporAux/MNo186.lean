module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.BMGeom
public import CFSG.LargeExtraspecial.A2ModOrdCard
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.Sylow
public import CFSG.Milestones.CL_LIT_Monster_existence_Griess_Conway
public import CFSG.Sporadic.Bridge.MonsterModelsGriess
public import CFSG.RankThree.OddKernel.SporadicKernelRestrictionB

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open Subgroup CFSG.Blueprint CFSG.Monster.Existence CFSG.Open

section Pure

variable {G : Type} [Group G]

theorem orderOf_eq_of_isConj'' {u v : G} (h : IsConj u v) : orderOf u = orderOf v := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  exact SemiconjBy.orderOf_eq c (show c * u = v * c by rw [← hc]; group)

theorem not_dvd_twoBCentralizerOrder : ¬ 31 ∣ twoBCentralizerOrder := by
  unfold twoBCentralizerOrder
  norm_num

theorem isConj_of_commute_thirtyOne {a z x f : G}
    (hinv : ∀ t : G, orderOf t = 2 → IsConj a t ∨ IsConj z t)
    (hBz : ∀ ζ : G, IsConj z ζ → IsTwoBCentralizer ζ) (hx : orderOf x = 31)
    (hf : orderOf f = 2) (hfx : f * x = x * f) : IsConj a f := by
  rcases hinv f hf with h | h
  · exact h
  · exfalso
    have hcard := (hBz f h).2.2.2.2.1
    have hxmem : x ∈ cent f := mem_centralizer_singleton_iff.2 hfx.symm
    have := Subgroup.orderOf_dvd_natCard (cent f) hxmem
    rw [hx, hcard] at this
    exact not_dvd_twoBCentralizerOrder this

theorem card_cent_of_isTwoACentralizer {a : G} (ha : orderOf a = 2) (h : IsTwoACentralizer a)
    (hB : Nat.card NativeSporadic.B = monsterBabyOrder) :
    Nat.card ↥(cent a) = 2 * monsterBabyOrder := by
  obtain ⟨-, hz, ⟨e⟩⟩ := h
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥(cent a))
  have hc : Nat.card ↥(center ↥(cent a)) = 2 := by
    rw [← Subgroup.card_map_of_injective (cent a).subtype_injective, hz, Nat.card_zpowers, ha]
  rw [Nat.card_congr e.toEquiv, hB, hc] at h1
  omega

theorem exists_orderOf_mul_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {x w : X}
    (hxw : Commute x w) {m n : ℕ} (hx : orderOf x = m) (hw : orderOf w = n)
    (hmn : Nat.Coprime m n) : ∃ y : Y, orderOf y = m * n := by
  refine ⟨e (x * w), ?_⟩
  rw [MulEquiv.orderOf_eq, hxw.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hx, hw]; exact hmn),
    hx, hw]

end Pure

section Certified


variable {G : Type} [Group G]

theorem not_dvd_of_twoPointShape {H : Subgroup G} {i : Fin 9}
    (hi0 : i ≠ 0) (hi4 : i ≠ 4) (h : TwoPointShape H i) : ¬ 31 ∣ Nat.card H := by
  fin_cases i
  · exact absurd rfl hi0
  · simp only [TwoPointShape] at h
    obtain ⟨N, hN, -, hN4, hX⟩ := h
    have h1 : Nat.card H = Nat.card (H ⧸ N) * Nat.card N :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [h1, CFSG.LargeExtraspecial.A2Mod.Ord.card_of_lieModel_twistedE6 hX, hN4]
    norm_num [ordTwistedE6]
  · simp only [TwoPointShape, HasLayeredTwoShape] at h
    obtain ⟨N, hN, N₀, hN₀, -, -, -, -, hNc, ⟨e⟩⟩ := h
    have h1 : Nat.card H = Nat.card (H ⧸ N) * Nat.card N :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [h1, Nat.card_congr e.toEquiv, CFSG.Sporadic.Co2.card_Co2, hNc]
    norm_num
  · simp only [TwoPointShape] at h
    obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Fi23.card_Fi23]
    norm_num
  · exact absurd rfl hi4
  · simp only [TwoPointShape] at h
    obtain ⟨N, hN, -, hN23, ⟨e⟩⟩ := h
    have h1 : Nat.card H = Nat.card (H ⧸ N) * Nat.card N :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [h1, Nat.card_congr e.toEquiv, CFSG.Sporadic.McL.card_McL, hN23]
    norm_num
  · simp only [TwoPointShape, HasTwoShape] at h
    obtain ⟨N, hN, hN2, hX⟩ := h
    have h1 : Nat.card H = Nat.card (H ⧸ N) * Nat.card N :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [h1, CFSG.LargeExtraspecial.A2Mod.Ord.card_of_lieModel_F4 hX, hN2]
    norm_num [ordF4]
  · simp only [TwoPointShape] at h
    obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.HN.card_HN]
    norm_num
  · simp only [TwoPointShape, HasTwoShape] at h
    obtain ⟨N, hN, hN2, ⟨e⟩⟩ := h
    have h1 : Nat.card H = Nat.card (H ⧸ N) * Nat.card N :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [h1, Nat.card_congr e.toEquiv, CFSG.Sporadic.Fi22.card_Fi22, hN2]
    norm_num

theorem isThShape_of_commute {a : G} {c : Fin 9 → G}
    (hord : ∀ i, orderOf (c i) = suborbitClassOrder i)
    (hcov : ∀ α β : G, IsConj a α → IsConj a β → ∃ i, IsConj (α * β) (c i))
    (hshape : ∀ (α β : G) (i : Fin 9), IsConj a α → IsConj a β → IsConj (α * β) (c i) →
      TwoPointShape (cent2 α β) i)
    {x f f' : G} (hx : orderOf x = 31) (hf : IsConj a f) (hf' : IsConj a f') (hff : f ≠ f')
    (hf2 : f * f = 1) (hfx : f * x = x * f) (hf'x : f' * x = x * f') :
    orderOf (f * f') = 3 ∧ Nonempty (↥(cent2 f f') ≃* NativeSporadic.Th) := by
  obtain ⟨i, hi⟩ := hcov f f' hf hf'
  have hsh := hshape f f' i hf hf' hi
  have hordi : orderOf (f * f') = suborbitClassOrder i := by
    rw [orderOf_eq_of_isConj'' hi, hord i]
  have hxmem : x ∈ cent2 f f' :=
    ⟨mem_centralizer_singleton_iff.2 hfx.symm, mem_centralizer_singleton_iff.2 hf'x.symm⟩
  have h31 : 31 ∣ Nat.card (cent2 f f') := hx ▸ Subgroup.orderOf_dvd_natCard _ hxmem
  by_cases h0 : i = 0
  · exfalso
    subst h0
    have h1 : f * f' = 1 := by
      rw [← orderOf_eq_one_iff, hordi]
      simp [suborbitClassOrder]
    have h2 : f' = f⁻¹ := eq_inv_of_mul_eq_one_right h1
    have h3 : f⁻¹ = f := inv_eq_of_mul_eq_one_right hf2
    exact hff (h2.trans h3).symm
  by_cases h4 : i = 4
  · subst h4
    exact ⟨hordi, hsh⟩
  · exact absurd h31 (not_dvd_of_twoPointShape h0 h4 hsh)

theorem exists_second_involution [Finite G] {a : G} {c : Fin 9 → G} (ha : orderOf a = 2)
    (h3i : ∀ α β β' : G, IsConj a α → IsConj a β → IsConj a β' →
      IsConj (α * β) (α * β') → ∃ g ∈ cent α, g * β * g⁻¹ = β')
    (hord : ∀ i, orderOf (c i) = suborbitClassOrder i)
    (hocc : ∀ i, ∃ α β : G, IsConj a α ∧ IsConj a β ∧ IsConj (α * β) (c i))
    (hshape : ∀ (α β : G) (i : Fin 9), IsConj a α → IsConj a β → IsConj (α * β) (c i) →
      TwoPointShape (cent2 α β) i)
    (hAcard : ∀ α : G, IsConj a α → Nat.card ↥(cent α) = 2 * monsterBabyOrder)
    (hTh : Nat.card NativeSporadic.Th = 90745943887872000)
    {x t : G} (hx : orderOf x = 31) (ht : IsConj a t) (htx : t * x = x * t) :
    ∃ f : G, IsConj a f ∧ f ≠ t ∧ f * x = x * f := by
  obtain ⟨α, β, hα, hβ, hαβ⟩ := hocc 4
  obtain ⟨k, hk⟩ := isConj_iff.1 (hα.symm.trans ht)
  have hβ₀ : IsConj a (k * β * k⁻¹) := hβ.trans (isConj_iff.2 ⟨k, rfl⟩)
  have hαβ₀ : IsConj (t * (k * β * k⁻¹)) (c 4) := by
    have e : t * (k * β * k⁻¹) = k * (α * β) * k⁻¹ := by rw [← hk]; group
    rw [e]
    exact (isConj_iff.2 ⟨k, rfl⟩ : IsConj (α * β) (k * (α * β) * k⁻¹)).symm.trans hαβ
  generalize k * β * k⁻¹ = β₀ at hβ₀ hαβ₀
  set S : Set G := {s | IsConj a s ∧ IsConj (t * s) (c 4)} with hSdef
  have hS0 : β₀ ∈ S := ⟨hβ₀, hαβ₀⟩
  have hSclosed : ∀ g ∈ cent t, ∀ s ∈ S, g * s * g⁻¹ ∈ S := by
    intro g hg s hs
    have hgt : g * t = t * g := mem_centralizer_singleton_iff.1 hg
    refine ⟨hs.1.trans (isConj_iff.2 ⟨g, rfl⟩), ?_⟩
    have e : t * (g * s * g⁻¹) = g * (t * s) * g⁻¹ := by
      calc t * (g * s * g⁻¹) = (t * g) * s * g⁻¹ := by simp only [mul_assoc]
        _ = (g * t) * s * g⁻¹ := by rw [hgt]
        _ = g * (t * s) * g⁻¹ := by simp only [mul_assoc]
    rw [e]
    exact (isConj_iff.2 ⟨g, rfl⟩ : IsConj (t * s) (g * (t * s) * g⁻¹)).symm.trans hs.2
  have hStrans : ∀ s ∈ S, ∃ g ∈ cent t, g * β₀ * g⁻¹ = s := fun s hs =>
    h3i t β₀ s ht hβ₀ hs.1 (hαβ₀.trans hs.2.symm)
  letI : MulAction (cent t) S := conjSMulOn (cent t) S hSclosed
  let s₀ : S := ⟨β₀, hS0⟩
  have horbit : MulAction.orbit (cent t) s₀ = Set.univ := by
    ext s
    simp only [Set.mem_univ, iff_true]
    obtain ⟨g, hg, hgs⟩ := hStrans s.1 s.2
    exact ⟨⟨g, hg⟩, Subtype.ext hgs⟩
  have hcard : Nat.card (MulAction.stabilizer (cent t) s₀) * S.ncard = Nat.card (cent t) := by
    have h := Subgroup.card_mul_index (MulAction.stabilizer (cent t) s₀)
    rwa [MulAction.index_stabilizer, horbit, Set.ncard_univ, Nat.card_coe_set_eq] at h
  have hstab : Nat.card (MulAction.stabilizer (cent t) s₀) = Nat.card (cent2 t β₀) := by
    apply Nat.card_congr
    exact
      { toFun := fun g => ⟨(g.1 : G), g.1.2, mem_centralizer_singleton_iff.2 (by
          have h1 := congrArg Subtype.val (MulAction.mem_stabilizer_iff.1 g.2)
          have h2 : (g.1 : G) * β₀ * (g.1 : G)⁻¹ = β₀ := h1
          rw [mul_inv_eq_iff_eq_mul] at h2
          exact h2)⟩
        invFun := fun h => ⟨⟨(h : G), h.2.1⟩, MulAction.mem_stabilizer_iff.2 (Subtype.ext (by
          show (h : G) * β₀ * (h : G)⁻¹ = β₀
          rw [mul_inv_eq_iff_eq_mul]
          exact mem_centralizer_singleton_iff.1 h.2.2))⟩
        left_inv := fun g => rfl
        right_inv := fun h => rfl }
  have hThc : Nat.card (cent2 t β₀) = 90745943887872000 := by
    obtain ⟨e⟩ := hshape t β₀ 4 ht hβ₀ hαβ₀
    rw [Nat.card_congr e.toEquiv, hTh]
  have hmain : 90745943887872000 * S.ncard = 2 * monsterBabyOrder := by
    have h := hcard
    rwa [hstab, hThc, hAcard t ht] at h
  have hn31 : ¬ 31 ∣ S.ncard := by
    rintro ⟨m, hm⟩
    rw [hm] at hmain
    norm_num [monsterBabyOrder] at hmain
    omega
  have hmod := ncard_modEq_fixed (p := 31) (by norm_num) hx (F := S) (by
    intro g hg s hs
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hg
    exact hSclosed _ (mem_centralizer_singleton_iff.2
      (Commute.zpow_left (show Commute x t from htx.symm) n).eq) s hs)
  have hne : {s | s ∈ S ∧ x * s = s * x}.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, Set.ncard_empty] at hmod
    exact hn31 ((Nat.modEq_zero_iff_dvd).1 hmod)
  obtain ⟨β', hβ'S, hxβ'⟩ := hne
  refine ⟨β', hβ'S.1, ?_, hxβ'.symm⟩
  rintro rfl
  have ht2 : orderOf β' = 2 := (orderOf_eq_of_isConj'' ht).symm.trans ha
  have htt : β' * β' = 1 := by
    have := pow_orderOf_eq_one β'
    rwa [ht2, pow_two] at this
  have h4 := hβ'S.2
  rw [htt] at h4
  have : c 4 = 1 := isConj_one_right.1 h4
  have h3 := hord 4
  rw [this, orderOf_one] at h3
  simp [suborbitClassOrder] at h3

theorem noOrder186_of_noOrder93_Th
    (hE : MonsterExistenceStatement G)
    (hB : Nat.card NativeSporadic.B = monsterBabyOrder) (hTh93 : NoOrder 93 NativeSporadic.Th) :
    NoOrder 186 G := by
  obtain ⟨⟨hfin, -, -, -⟩, a, z, ha, hz, hnc, hinv, hA, hBz, hgraph⟩ := hE
  obtain ⟨h3i, c, -, -, -, -, hord, hcov, hocc, hshape, -⟩ := hgraph
  haveI := hfin
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro g hg
  have hAcard : ∀ α : G, IsConj a α → Nat.card ↥(cent α) = 2 * monsterBabyOrder := fun α hα =>
    card_cent_of_isTwoACentralizer ((orderOf_eq_of_isConj'' hα).symm.trans ha) (hA α hα) hB
  have hg0 : g ≠ 1 := by
    rintro rfl
    simp at hg
  have hord_pow : ∀ n : ℕ, n ≠ 0 → orderOf (g ^ n) = 186 / Nat.gcd 186 n := fun n hn => by
    rw [orderOf_pow' _ hn, hg]
  have hx : orderOf (g ^ 6) = 31 := by rw [hord_pow 6 (by norm_num)]; norm_num
  have ht : orderOf (g ^ 93) = 2 := by rw [hord_pow 93 (by norm_num)]; norm_num
  have hw : orderOf (g ^ 62) = 3 := by rw [hord_pow 62 (by norm_num)]; norm_num
  set x := g ^ 6 with hxdef
  set t := g ^ 93 with htdef
  set w := g ^ 62 with hwdef
  have htx : t * x = x * t := (Commute.pow_pow_self g 93 6).eq
  have hwx : w * x = x * w := (Commute.pow_pow_self g 62 6).eq
  have hwt : w * t = t * w := (Commute.pow_pow_self g 62 93).eq
  have hinvol : ∀ f : G, f ∈ invComm x → orderOf f = 2 := fun f hf =>
    orderOf_eq_prime (by rw [pow_two]; exact hf.1) hf.2.1
  have hFconj : ∀ f ∈ invComm x, IsConj a f := fun f hf =>
    isConj_of_commute_thirtyOne hinv hBz hx (hinvol f hf) hf.2.2
  have htF : t ∈ invComm x := by
    refine ⟨?_, ?_, htx⟩
    · have := pow_orderOf_eq_one t
      rwa [ht, pow_two] at this
    · intro h1
      rw [h1, orderOf_one] at ht
      omega
  have h3 : ∀ u ∈ invComm x, ∀ v ∈ invComm x, u ≠ v → orderOf (u * v) = 3 :=
    fun u hu v hv hne =>
      (isThShape_of_commute hord hcov hshape hx (hFconj u hu) (hFconj v hv) hne hu.1 hu.2.2
        hv.2.2).1
  obtain ⟨f₀, hf₀A, hf₀t, hf₀x⟩ := exists_second_involution ha h3i hord hocc hshape hAcard
    (CFSG.RankThree.OddKernel.card_Th_eq) hx (hFconj t htF) htx
  have hf₀o : orderOf f₀ = 2 := (orderOf_eq_of_isConj'' hf₀A).symm.trans ha
  have hf₀F : f₀ ∈ invComm x := by
    refine ⟨?_, ?_, hf₀x⟩
    · have := pow_orderOf_eq_one f₀
      rwa [hf₀o, pow_two] at this
    · intro h1
      rw [h1, orderOf_one] at hf₀o
      omega
  obtain ⟨f, hfF, hft, hwf⟩ := exists_fixed_ne htF hf₀F hf₀t h3 hw hwx hwt
  obtain ⟨-, ⟨e⟩⟩ := isThShape_of_commute hord hcov hshape hx (hFconj t htF) (hFconj f hfF)
    (Ne.symm hft) htF.1 htx hfF.2.2
  have hxm : x ∈ cent2 t f :=
    ⟨mem_centralizer_singleton_iff.2 htx.symm, mem_centralizer_singleton_iff.2 hfF.2.2.symm⟩
  have hwm : w ∈ cent2 t f :=
    ⟨mem_centralizer_singleton_iff.2 hwt, mem_centralizer_singleton_iff.2 hwf⟩
  have hXo : orderOf (⟨x, hxm⟩ : cent2 t f) = 31 := by rw [Subgroup.orderOf_mk]; exact hx
  have hWo : orderOf (⟨w, hwm⟩ : cent2 t f) = 3 := by rw [Subgroup.orderOf_mk]; exact hw
  have hXW : Commute (⟨x, hxm⟩ : cent2 t f) ⟨w, hwm⟩ :=
    Subtype.ext (Commute.pow_pow_self g 6 62).eq
  obtain ⟨y, hy⟩ := @exists_orderOf_mul_of_mulEquiv (↥(cent2 t f)) NativeSporadic.Th _ Units.instGroup
    e _ _ hXW 31 3 hXo hWo (by norm_num)
  exact hTh93 y (hy.trans (by norm_num))

end Certified

section Native



theorem noOrder186_M_of_noOrder93_Th (hTh93 : NoOrder 93 NativeSporadic.Th) :
    NoOrder 186 NativeSporadic.M := by
  have hB : Nat.card NativeSporadic.B = monsterBabyOrder := by
    rw [CFSG.RankThree.OddKernel.card_B_eq]
    norm_num [monsterBabyOrder]
  have h := noOrder186_of_noOrder93_Th CFSG.Milestones.cl_lit_monster_existence_griess_conway
    hB hTh93
  obtain ⟨e⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_griess_y443Derived
  exact noOrder_of_mulEquiv e.symm h

end Native

end CFSG.HardMathSupport.Dickson.Sec6.I1431
