module

public import CFSG.CGT.Timmesfeld75.SimpleCase
public import CFSG.CGT.Timmesfeld75.Reduction
public import CFSG.CGT.Timmesfeld75.OddCenter
public import CFSG.CGT.Timmesfeld75.Lemma25
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.CGT.Timmesfeld75.CentralQuotient

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

theorem eq_of_card_two {G : Type*} [Group G] {T : Subgroup G} (hT : IsElemAbelian 2 T)
    (h2 : Nat.card T = 2) {x y : G} (hx : x ∈ T) (hx1 : x ≠ 1) (hy : y ∈ T) (hy1 : y ≠ 1) :
    x = y := by
  have hord : orderOf x = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using elemAbelian_mul_self hT hx) hx1
  have hTfin : Finite T := Nat.finite_of_card_ne_zero (by omega)
  have hTeq : T = Subgroup.zpowers x := by
    symm
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.zpowers_le]; exact hx
    · rw [Nat.card_zpowers, hord, h2]
  rw [hTeq] at hy
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hy
  have hsq : x ^ 2 = 1 := by rw [← hord]; exact pow_orderOf_eq_one x
  have hk2 : x ^ k = x ^ (k % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 2]
    rw [zpow_add, zpow_mul, zpow_ofNat, hsq, one_zpow, mul_one]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · rw [h] at hk2
    exact absurd (hk.symm.trans (by rw [hk2]; simp)) hy1
  · rw [h] at hk2
    rw [← hk, hk2]; simp

theorem eq_one_of_mul_self_of_odd {G : Type*} [Group G] {Z : Subgroup G}
    (hZodd : Odd (Nat.card Z)) {z : G} (hz : z ∈ Z) (hzz : z * z = 1) : z = 1 := by
  have h1 : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hzz)
  have h2 : orderOf z ∣ Nat.card Z := by
    have := orderOf_dvd_natCard (⟨z, hz⟩ : Z)
    rwa [Subgroup.orderOf_mk] at this
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.2 hZodd) h1 h2)

theorem lift_normalizer_of_central_odd {K : Type*} [Group K] [Finite K] {T : Subgroup K}
    (hT : IsElemAbelian 2 T) (Z : Subgroup K) [Z.Normal] (hZc : Z ≤ Subgroup.center K)
    (hZodd : Odd (Nat.card Z)) {g : K}
    (hg : QuotientGroup.mk' Z g ∈
      Subgroup.normalizer ((T.map (QuotientGroup.mk' Z) : Subgroup (K ⧸ Z)) : Set (K ⧸ Z))) :
    g ∈ Subgroup.normalizer (T : Set K) := by
  have key : ∀ t ∈ T, g * t * g⁻¹ ∈ T := by
    intro t ht
    have ht2 : t * t = 1 := elemAbelian_mul_self hT ht
    have hmem : QuotientGroup.mk' Z t ∈ (T.map (QuotientGroup.mk' Z) : Subgroup (K ⧸ Z)) :=
      Subgroup.mem_map_of_mem _ ht
    have h1 := (Subgroup.mem_normalizer_iff.1 hg _).1 hmem
    obtain ⟨t', ht', ht'eq⟩ := h1
    set w := g * t * g⁻¹ with hwdef
    have hz : t'⁻¹ * w ∈ Z := by
      refine (QuotientGroup.eq (a := t') (b := w)).1 ?_
      rw [← QuotientGroup.mk'_apply, ht'eq]
      simp [w]
    set z := t'⁻¹ * w with hzdef
    have hww : w * w = 1 := by
      calc w * w = g * (t * t) * g⁻¹ := by simp only [hwdef]; group
        _ = 1 := by rw [ht2]; group
    have ht'2 : t' * t' = 1 := elemAbelian_mul_self hT ht'
    have hzc : z * t' = t' * z := (Subgroup.mem_center_iff.1 (hZc hz) t').symm
    have hwe : w = t' * z := by rw [hzdef]; group
    have hzz : z * z = 1 := by
      have : (t' * z) * (t' * z) = z * z := by
        calc (t' * z) * (t' * z) = t' * (z * t') * z := by simp only [mul_assoc]
          _ = t' * (t' * z) * z := by rw [hzc]
          _ = (t' * t') * (z * z) := by simp only [mul_assoc]
          _ = z * z := by rw [ht'2, one_mul]
      rw [← this, ← hwe]; exact hww
    have hz1 : z = 1 := eq_one_of_mul_self_of_odd hZodd hz hzz
    rw [hwe, hz1, mul_one]
    exact ht'
  have hle : conjSubgroup g T ≤ T := by
    intro w hw
    have h1 : g⁻¹ * w * g ∈ T := mem_conjSubgroup.1 hw
    have := key _ h1
    simpa [mul_assoc] using this
  exact mem_normalizer_iff_conjSubgroup_eq.2 (conjSubgroup_eq_of_le hle)

theorem four_le_card_map_central_odd {K : Type*} [Group K] [Finite K] {T : Subgroup K}
    (hT : IsElemAbelian 2 T) (Z : Subgroup K) [Z.Normal] (hZodd : Odd (Nat.card Z))
    (h4 : 4 ≤ Nat.card T) : 4 ≤ Nat.card (T.map (QuotientGroup.mk' Z)) := by
  refine h4.trans (Nat.card_le_card_of_injective
    (fun t : T => (⟨QuotientGroup.mk' Z t, Subgroup.mem_map_of_mem _ t.2⟩ :
      T.map (QuotientGroup.mk' Z))) ?_)
  intro a b hab
  have h1 : QuotientGroup.mk' Z (a : K) = QuotientGroup.mk' Z (b : K) := congrArg Subtype.val hab
  have h2 : (a : K)⁻¹ * b ∈ Z := (QuotientGroup.eq).1 h1
  have h3 : (a : K)⁻¹ * b ∈ T := T.mul_mem (T.inv_mem a.2) b.2
  have h5 : (a : K)⁻¹ * b = 1 := eq_one_of_mem_of_odd_card hT hZodd h3 h2
  exact Subtype.ext (inv_mul_eq_one.1 h5)

theorem conclusion_of_simpleCase (hS : SimpleCaseStmt) (h215 : Lemma215Stmt)
    {K : Type} [Group K] [Finite K] {T : Subgroup K} (hT : IsWC T)
    (hK : Subgroup.normalClosure (T : Set K) = ⊤)
    (hO2 : ∀ N : Subgroup K, N.Normal → IsPGroup 2 N → N = ⊥) :
    ((ZStarCase K ∧ Nat.card T ≤ 2) ∨ (4 ≤ Nat.card T ∧ IsCoveringOfList K)) ∧
      ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 →
        ∃ g ∈ Subgroup.normalizer (T : Set K), g * x * g⁻¹ = y := by
  by_cases hTbot : T = ⊥
  · subst hTbot
    refine ⟨Or.inl ⟨?_, by rw [Subgroup.card_bot]; omega⟩,
      fun x hx hx1 => absurd ((Subgroup.mem_bot).1 hx) hx1⟩
    have hK1 : (⊤ : Subgroup K) = ⊥ := by
      rw [← hK]; exact (Subgroup.normalClosure_eq_self (⊥ : Subgroup K))
    refine zStarCase_of_commutative fun a b => ?_
    have ha : a = 1 := (Subgroup.mem_bot).1 (hK1 ▸ Subgroup.mem_top a)
    have hb : b = 1 := (Subgroup.mem_bot).1 (hK1 ▸ Subgroup.mem_top b)
    rw [ha, hb]
  by_cases h2 : Nat.card T = 2
  · refine ⟨Or.inl ⟨?_, h2.le⟩, fun x hx hx1 y hy hy1 => ⟨1, Subgroup.one_mem _, ?_⟩⟩
    · have h := zStarCase_normalClosure_of_card_two hT h2
      rw [hK] at h
      exact zStarCase_of_mulEquiv Subgroup.topEquiv h
    · rw [eq_of_card_two hT.1 h2 hx hx1 hy hy1]; simp
  have h4 : 4 ≤ Nat.card T := four_le_card_of_isElemAbelian hT.1 hTbot h2
  have hZodd := odd_card_center hO2
  have hrad := solvable_radical_bot_quotient hT h4 hK hO2
  set Z : Subgroup K := Subgroup.center K with hZdef
  have hWCb : IsWC (T.map (QuotientGroup.mk' Z)) := hT.map_quotient_central_odd Z le_rfl hZodd
  have hKb : Subgroup.normalClosure
      ((T.map (QuotientGroup.mk' Z) : Subgroup (K ⧸ Z)) : Set (K ⧸ Z)) = ⊤ := by
    rw [Subgroup.coe_map, ← Subgroup.map_normalClosure _ _ (QuotientGroup.mk'_surjective _), hK,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have h4b := four_le_card_map_central_odd hT.1 Z hZodd h4
  have hsimple : IsSimpleGroup (K ⧸ Z) := h215 (K ⧸ Z) _ hWCb h4b hKb hrad
  have hnab : ∃ a b : K ⧸ Z, a * b ≠ b * a := by
    by_contra hcomm
    push Not at hcomm
    have hsolv : Group.IsSolvable (⊤ : Subgroup (K ⧸ Z)) :=
      Group.isSolvable_of_comm fun a b => Subtype.ext (hcomm a b)
    have htop := hrad ⊤ inferInstance hsolv
    have hbot : T.map (QuotientGroup.mk' Z) = ⊥ := by
      rw [eq_bot_iff]
      intro x _
      rw [← htop]
      exact Subgroup.mem_top x
    rw [hbot, Subgroup.card_bot] at h4b
    omega
  obtain ⟨hlist, htrans⟩ := hS (K ⧸ Z) hnab _ hWCb h4b
  have hcomm_top : commutator K = ⊤ :=
    commutator_eq_top_of_odd_center hT.1 hK hZodd (center_sup_commutator_eq_top hsimple hnab)
  refine ⟨Or.inr ⟨h4, hcomm_top, Z, le_rfl, inferInstance, hlist⟩, fun x hx hx1 y hy hy1 => ?_⟩
  have hxb : QuotientGroup.mk' Z x ∈ T.map (QuotientGroup.mk' Z) := Subgroup.mem_map_of_mem _ hx
  have hyb : QuotientGroup.mk' Z y ∈ T.map (QuotientGroup.mk' Z) := Subgroup.mem_map_of_mem _ hy
  have hx1b : QuotientGroup.mk' Z x ≠ 1 := fun h =>
    hx1 (eq_one_of_mem_of_odd_card hT.1 hZodd hx ((QuotientGroup.eq_one_iff x).1 h))
  have hy1b : QuotientGroup.mk' Z y ≠ 1 := fun h =>
    hy1 (eq_one_of_mem_of_odd_card hT.1 hZodd hy ((QuotientGroup.eq_one_iff y).1 h))
  obtain ⟨gb, hgb, hgbxy⟩ := htrans _ hxb hx1b _ hyb hy1b
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gb
  have hgT := lift_normalizer_of_central_odd hT.1 Z le_rfl hZodd hgb
  refine ⟨g, hgT, ?_⟩
  have hmem : g * x * g⁻¹ ∈ T := conj_mem_of_mem_normalizer hgT hx
  have h5 : (QuotientGroup.mk (g * x * g⁻¹) : K ⧸ Z) = QuotientGroup.mk y := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact hgbxy
  have h6 : (g * x * g⁻¹)⁻¹ * y ∈ Z := (QuotientGroup.eq).1 h5
  have h7 : (g * x * g⁻¹)⁻¹ * y ∈ T := T.mul_mem (T.inv_mem hmem) hy
  exact inv_mul_eq_one.1 (eq_one_of_mem_of_odd_card hT.1 hZodd h7 h6)

theorem isElemAbelian_bot {G : Type*} [Group G] (p : ℕ) : IsElemAbelian p (⊥ : Subgroup G) := by
  exact CFSG.Open.isElemAbelian_bot _

theorem eq_bot_of_normal_isPGroup_of_normal {X : Type*} [Group X] (K : Subgroup X) [K.Normal]
    (hO2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥) (P : Subgroup K) (hP : P.Normal)
    (hP2 : IsPGroup 2 P) : P = ⊥ := by
  have hle : P ≤ CFSG.pCore 2 K := le_sSup ⟨hP, hP2⟩
  have hQn : ((CFSG.pCore 2 K).map K.subtype).Normal := by
    refine ⟨fun n hn x => ?_⟩
    obtain ⟨q, hq, rfl⟩ := hn
    have hqk : MulAut.conjNormal (H := K) x q ∈ CFSG.pCore 2 K := by
      have h := (CFSG.pCore_characteristic (p := 2) (G := K)).fixed (MulAut.conjNormal x)
      have : q ∈ (CFSG.pCore 2 K).comap (MulAut.conjNormal (H := K) x).toMonoidHom := by
        rw [h]; exact hq
      exact this
    exact ⟨_, hqk, by simp [MulAut.conjNormal_apply]⟩
  have hQp : IsPGroup 2 ((CFSG.pCore 2 K).map K.subtype) :=
    CFSG.pCore_isPGroup.map K.subtype
  have hQ := hO2 _ hQn hQp
  have hQ' : CFSG.pCore 2 K = ⊥ := (Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).1 hQ
  exact le_bot_iff.1 (hQ' ▸ hle)

theorem theoremA1_of_simpleCase (hS : SimpleCaseStmt) (h215 : Lemma215Stmt)
    {X : Type} [Group X] [Finite X] {L : Subgroup X} (hL : IsWC L)
    (hO2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥) :
    ThmAConclusion L ∧
      ∀ x ∈ L, x ≠ 1 → ∀ y ∈ L, y ≠ 1 →
        ∃ g ∈ Subgroup.normalizer (L : Set X), g * x * g⁻¹ = y := by
  set K := Subgroup.normalClosure (L : Set X) with hKdef
  have hTWC : IsWC (L.subgroupOf K) := isWC_subgroupOf_normalClosure hL
  have hKtop := normalClosure_subgroupOf_eq_top hL
  have hO2K := eq_bot_of_normal_isPGroup_of_normal K hO2
  obtain ⟨hc, htrans⟩ := conclusion_of_simpleCase hS h215 hTWC hKtop hO2K
  refine ⟨⟨⊥, inferInstance, isElemAbelian_bot 2, ?_⟩, fun x hx hx1 y hy hy1 => ?_⟩
  · rcases hc with ⟨hz, -⟩ | ⟨-, hcov⟩
    · exact Or.inl (zStarCase_of_mulEquiv QuotientGroup.quotientBot.symm hz)
    · exact Or.inr (isCoveringOfList_of_mulEquiv QuotientGroup.quotientBot.symm hcov)
  · have hxK : x ∈ K := Subgroup.le_normalClosure hx
    have hyK : y ∈ K := Subgroup.le_normalClosure hy
    obtain ⟨g, hg, hgxy⟩ := htrans ⟨x, hxK⟩ (Subgroup.mem_subgroupOf.2 hx)
      (fun h => hx1 (congrArg Subtype.val h)) ⟨y, hyK⟩ (Subgroup.mem_subgroupOf.2 hy)
      (fun h => hy1 (congrArg Subtype.val h))
    refine ⟨(g : X), ?_, congrArg Subtype.val hgxy⟩
    have hle : conjSubgroup (g : X) L ≤ L := by
      intro w hw
      have h1 : (g : X)⁻¹ * w * g ∈ L := mem_conjSubgroup.1 hw
      have h1K : (g : X)⁻¹ * w * g ∈ K := Subgroup.le_normalClosure h1
      have h2 : (⟨(g : X)⁻¹ * w * g, h1K⟩ : K) ∈ L.subgroupOf K := Subgroup.mem_subgroupOf.2 h1
      have h3 := conj_mem_of_mem_normalizer hg h2
      have h4 : (g : X) * ((g : X)⁻¹ * w * g) * (g : X)⁻¹ ∈ L := Subgroup.mem_subgroupOf.1 h3
      simpa [mul_assoc] using h4
    exact mem_normalizer_iff_conjSubgroup_eq.2 (conjSubgroup_eq_of_le hle)

end CFSG.CGT.Timmesfeld75
