module

public import CFSG.LocalAnalysis.RankThreeUC.GL33.Classes
public import CFSG.LocalAnalysis.AGL81I.Section3.Sp43.Gen

public section

namespace CFSG.KC.GL33K

open CFSG.GL33 CFSG.GL33.Native Subgroup
open scoped Matrix

@[expose] def fam (mem : ℕ → Subgroup G) : Set (Subgroup G) :=
  {K | ∃ j < 13, ∃ g : G, K = (mem j).map (MulAut.conj g).toMonoidHom}

structure GFacts (mem : ℕ → Subgroup G) : Prop where
  zero : mem 0 = ⊥
  ne_bot : ∀ j < 13, j ≠ 0 → mem j ≠ ⊥
  join_closed : ∀ K ∈ fam mem, ∀ σ : G, (∃ k, orderOf σ = 3 ^ k) → K ⊔ zpowers σ ∈ fam mem
  kind1 : ∀ j ∈ [1, 2, 3, 4, 5, 7, 8, 11], ∃ v : V, v ≠ 0 ∧ mem j ≤ fixer v
  kind2 : ∃ f : V, f ≠ 0 ∧ mem 10 ≤ cofixer f
  a4 : ∃ M : Subgroup G, Nat.card M = 48 ∧
    (∀ x ∈ M, ∀ j : Fin 3, ∃ i : Fin 3, act x (Pi.single j 1) ∈
      AddSubgroup.zmultiples (Pi.single i 1 : V)) ∧ normalizer (mem 6 : Set G) ≤ M
  c13 : ∃ u ∈ mem 9, orderOf u = 13 ∧ ∀ n ∈ normalizer (mem 9 : Set G), n * u * n⁻¹ ∈ zpowers u
  sl : Nonempty (mem 12 ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 3))
  syl : ∃ T : Subgroup G, Nat.card T = 16 ∧ ofCode minusOneC ∉ T ∧ T ≤ lineStab (toV 9)

variable {mem : ℕ → Subgroup G}

theorem conj_mem_map' {M : Subgroup G} {g x : G} (hx : x ∈ M) :
    g * x * g⁻¹ ∈ M.map (MulAut.conj g).toMonoidHom :=
  ⟨x, hx, by simp⟩

theorem mem_map_conj' {M : Subgroup G} {g y : G}
    (hy : y ∈ M.map (MulAut.conj g).toMonoidHom) : g⁻¹ * y * g ∈ M := by
  obtain ⟨x, hx, rfl⟩ := hy
  simpa [mul_assoc] using hx

theorem map_conj_ne_bot {M : Subgroup G} (hM : M ≠ ⊥) (g : G) :
    M.map (MulAut.conj g).toMonoidHom ≠ ⊥ := by
  intro h
  apply hM
  rw [eq_bot_iff]
  intro x hx
  have := conj_mem_map' (g := g) hx
  rw [h, Subgroup.mem_bot] at this
  rw [Subgroup.mem_bot]
  have e : x = g⁻¹ * (g * x * g⁻¹) * g := by group
  rw [e, this]
  group

theorem GFacts.false_of_fix {M : Subgroup G} {v : V} (hv0 : v ≠ 0) (hle : M ≤ fixer v)
    (hM : M ≠ ⊥) {W : Subgroup G} (hW : Irr W) {g : G}
    (hN : Normalizes W (M.map (MulAut.conj g).toMonoidHom)) : False := by
  have hfix := (fixA_comA_of_irr hW hN (map_conj_ne_bot hM g)).1
  have hmem : act g v ∈ fixA (M.map (MulAut.conj g).toMonoidHom) := by
    intro y hy
    have hy' := hle (mem_map_conj' hy)
    change act _ _ = _ at hy'
    have e : y * g = g * (g⁻¹ * y * g) := by group
    rw [← act_mul, e, act_mul, hy']
  rw [hfix, AddSubgroup.mem_bot] at hmem
  exact hv0 (act_injective g (by rw [hmem, act_zero]))

theorem GFacts.false_of_cofix {M : Subgroup G} {f : V} (hf0 : f ≠ 0) (hle : M ≤ cofixer f)
    (hM : M ≠ ⊥) {W : Subgroup G} (hW : Irr W) {g : G}
    (hN : Normalizes W (M.map (MulAut.conj g).toMonoidHom)) : False := by
  have hcom := (fixA_comA_of_irr hW hN (map_conj_ne_bot hM g)).2
  let φ : V →+ ZMod 3 :=
    { toFun := fun u => f ⬝ᵥ act g⁻¹ u
      map_zero' := by simp [act_zero]
      map_add' := fun u w => by simp [act_add, dotProduct_add] }
  have hker : comA (M.map (MulAut.conj g).toMonoidHom) ≤ φ.ker := by
    rw [comA, AddSubgroup.closure_le]
    rintro _ ⟨y, hy, v, rfl⟩
    have hy' := hle (mem_map_conj' hy)
    change f ᵥ* _ = f at hy'
    simp only [SetLike.mem_coe, AddMonoidHom.mem_ker]
    change f ⬝ᵥ act g⁻¹ (act y v - v) = 0
    have e : act g⁻¹ (act y v) = act (g⁻¹ * y * g) (act g⁻¹ v) := by
      rw [← act_mul, ← act_mul, show g⁻¹ * y * g * g⁻¹ = g⁻¹ * y by group]
    rw [act_sub, e, act, dotProduct_sub, Matrix.dotProduct_mulVec, hy', sub_self]
  obtain ⟨i, hi⟩ : ∃ i, f i ≠ 0 := by
    by_contra hall
    exact hf0 (funext fun i => by_contra fun h => hall ⟨i, h⟩)
  have hφ : φ (act g (Pi.single i 1)) ≠ 0 := by
    change f ⬝ᵥ act g⁻¹ (act g (Pi.single i 1)) ≠ 0
    rw [act_inv_act, dotProduct_single, mul_one]
    exact hi
  exact hφ (hker (hcom ▸ AddSubgroup.mem_top (act g (Pi.single i 1))))

theorem GFacts.case_A4 (F : GFacts mem) {W : Subgroup G} {g : G}
    (hN : Normalizes W ((mem 6).map (MulAut.conj g).toMonoidHom)) :
    ∃ Bi : Fin 3 → AddSubgroup V, (∀ i, Nat.card (Bi i) = 3) ∧ (⨆ i, Bi i) = ⊤ ∧
      (∀ w ∈ W, ∀ i, ∃ j, ∀ v ∈ Bi i, act w v ∈ Bi j) ∧ Nat.card W ∣ 48 := by
  obtain ⟨Mon, hcard, hmonoE, hnorm⟩ := F.a4
  have hmon : ∀ w ∈ W, g⁻¹ * w * g ∈ Mon := fun w hw => hnorm (conj_mem_normalizer hN hw)
  refine ⟨fun i => AddSubgroup.zmultiples (act g (Pi.single i 1)), fun i => ?_, ?_, ?_, ?_⟩
  · rw [Nat.card_zmultiples]
    apply addOrderOf_eq_prime
    · exact three_nsmul_V _
    · intro h0
      have : (Pi.single i 1 : V) = 0 := act_injective g (by rw [h0, act_zero])
      have := congrFun this i
      simp at this
  · rw [eq_top_iff]
    intro v _
    have hv : v = act g (act g⁻¹ v) := (act_act_inv g v).symm
    rw [hv, pi_eq_sum_univ' (act g⁻¹ v)]
    have hsum : ∀ (s : Finset (Fin 3)), act g (∑ i ∈ s, (act g⁻¹ v) i • Pi.single i 1) ∈
        ⨆ i, AddSubgroup.zmultiples (act g (Pi.single i 1)) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp [act_zero]
      | insert a s ha ih =>
        rw [Finset.sum_insert ha, act_add]
        refine AddSubgroup.add_mem _ ?_ ih
        refine AddSubgroup.mem_iSup_of_mem a ?_
        rw [act_smul]
        have e : ((act g⁻¹ v) a) • act g (Pi.single a 1) =
            ((((act g⁻¹ v) a).val : ℤ)) • act g (Pi.single a 1) := by
          rw [← Int.cast_smul_eq_zsmul (ZMod 3)]
          simp
        rw [e]
        exact AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples _) _
    exact hsum Finset.univ
  · intro w hw i
    obtain ⟨j, hj⟩ := hmonoE _ (hmon w hw) i
    refine ⟨j, fun v hv => ?_⟩
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hv
    obtain ⟨k', hk'⟩ := AddSubgroup.mem_zmultiples_iff.1 hj
    have e : act w (act g (Pi.single i 1)) = act g (act (g⁻¹ * w * g) (Pi.single i 1)) := by
      rw [← act_mul, ← act_mul, show g * (g⁻¹ * w * g) = w * g by group]
    rw [AddSubgroup.mem_zmultiples_iff]
    refine ⟨k * k', ?_⟩
    have hz : ∀ (z : ℤ) (u : V), act w (z • u) = z • act w u := fun z u =>
      map_zsmul (actHom w) z u
    have hz' : ∀ (z : ℤ) (u : V), act g (z • u) = z • act g u := fun z u =>
      map_zsmul (actHom g) z u
    rw [hz, e, ← hk', hz', mul_smul]
  · have hle : W ≤ Mon.map (MulAut.conj g).toMonoidHom := by
      intro w hw
      refine ⟨g⁻¹ * w * g, hmon w hw, ?_⟩
      simp [mul_assoc]
    have hc := Subgroup.card_dvd_of_le hle
    rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard] at hc

theorem GFacts.case_13 (F : GFacts mem) {W : Subgroup G} {g : G}
    (hN : Normalizes W ((mem 9).map (MulAut.conj g).toMonoidHom))
    (hXW : (mem 9).map (MulAut.conj g).toMonoidHom ≤ W) :
    ∃ U : Subgroup G, U ≤ W ∧ (U.subgroupOf W).Normal ∧ Nat.card U = 13 := by
  obtain ⟨u, huM, hord, hnorm⟩ := F.c13
  set z := g * u * g⁻¹
  have hzw : ∀ w ∈ W, w * z * w⁻¹ ∈ zpowers z := by
    intro w hw
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hnorm _ (conj_mem_normalizer hN hw))
    refine ⟨k, ?_⟩
    have e : w * z * w⁻¹ = g * ((g⁻¹ * w * g) * u * (g⁻¹ * w * g)⁻¹) * g⁻¹ := by
      simp only [z]
      group
    rw [e, ← hk]
    simp only [z, ← conj_zpow]
  refine ⟨zpowers z, ?_, ?_, ?_⟩
  · rw [Subgroup.zpowers_le]
    exact hXW (conj_mem_map' huM)
  · constructor
    intro x hx w
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hx
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hm, ← conj_zpow]
    exact Subgroup.zpow_mem _ (hzw w w.2) m
  · rw [Nat.card_zpowers]
    simp only [z]
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hord]

theorem GFacts.case_SL (F : GFacts mem) {W : Subgroup G} {g : G}
    (hN : Normalizes W ((mem 12).map (MulAut.conj g).toMonoidHom))
    (hXW : (mem 12).map (MulAut.conj g).toMonoidHom ≤ W) :
    ∃ U : Subgroup G, U ≤ W ∧ (U.subgroupOf W).Normal ∧
      Nonempty (U ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)) := by
  obtain ⟨e⟩ := F.sl
  refine ⟨(mem 12).map (MulAut.conj g).toMonoidHom, hXW, ?_, ⟨?_⟩⟩
  · constructor
    intro x hx w
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have := hN w⁻¹ (W.inv_mem w.2) _ hx
    simpa using this
  · exact ((mem 12).equivMapOfInjective _ (MulAut.conj g).injective).symm.trans e

private theorem act_minusOne' (v : V) : act (ofCode minusOneC) v = -v := by
  rw [act, coe_ofCode good_minusOneC, toM_minusOneC, Matrix.neg_mulVec, Matrix.one_mulVec]

private theorem minusOne_comm' (x : G) : x * ofCode minusOneC = ofCode minusOneC * x := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_ofCode good_minusOneC, toM_minusOneC, mul_neg_one,
    neg_one_mul]

theorem GFacts.line_of_two_group (F : GFacts mem) {W : Subgroup G} (hp : IsPGroup 2 W) :
    ∃ v : V, v ≠ 0 ∧ ∀ w ∈ W, act w v = v ∨ act w v = -v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hcard, hzT, hline0⟩ := F.syl
  set z := ofCode minusOneC
  set S := T ⊔ zpowers z
  have he : toV 9 ≠ 0 := toV_ne_zero (by norm_num) (by norm_num)
  have hline : S ≤ lineStab (toV 9) := by
    refine sup_le hline0 ?_
    rw [Subgroup.zpowers_le]
    exact Or.inr (act_minusOne' _)
  have hz2 : z ^ 2 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, coe_ofCode good_minusOneC, toM_minusOneC, Units.val_one]
    simp
  have hz1 : z ≠ 1 := by
    intro h
    have := congrArg (fun x : G => (x : Matrix (Fin 3) (Fin 3) (ZMod 3)) 0 0) h
    simp only [z, coe_ofCode good_minusOneC, toM_minusOneC, Units.val_one] at this
    revert this
    decide
  have hTp : IsPGroup 2 T := IsPGroup.of_card (n := 4) (by rw [hcard]; norm_num)
  have hZp : IsPGroup 2 (zpowers z) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, orderOf_eq_prime hz2 hz1]; norm_num)
  have hZn : (zpowers z).Normal := by
    constructor
    intro x hx g
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have : g * z ^ m * g⁻¹ = z ^ m := by
      rw [← conj_zpow, show g * z * g⁻¹ = z by rw [minusOne_comm' g, mul_assoc, mul_inv_cancel,
        mul_one]]
    rw [this]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) m
  have hSp : IsPGroup 2 S := hTp.to_sup_of_normal_right hZp
  obtain ⟨m, hm⟩ := hSp.exists_card_eq
  have h16 : 16 ∣ Nat.card S := hcard ▸ Subgroup.card_dvd_of_le le_sup_left
  have hne : Nat.card S ≠ 16 := by
    intro h
    apply hzT
    have heq : T = S := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h, hcard])
    rw [heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have hS32 : Nat.card S = 32 := by
    have hdvd : 2 ^ m ∣ 2 ^ 5 * 351 := by
      rw [← hm, show 2 ^ 5 * 351 = 11232 by norm_num, ← card_G]
      exact Subgroup.card_subgroup_dvd_card S
    have hm5 : m ≤ 5 := by
      by_contra hm5
      have : 2 ^ 6 ∣ 2 ^ 5 * 351 := (Nat.pow_dvd_pow 2 (by omega : 6 ≤ m)).trans hdvd
      norm_num at this
    rw [hm] at h16 hne ⊢
    interval_cases m <;> simp_all
  have hidx : ¬ 2 ∣ S.index := by
    have := Subgroup.card_mul_index S
    rw [hS32, card_G] at this
    have h351 : S.index = 351 := by omega
    rw [h351]
    norm_num
  set S₀ : Sylow 2 G := hSp.toSylow hidx
  obtain ⟨P, hWP⟩ := hp.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G S₀ P
  refine ⟨act h (toV 9), fun h0 => he (act_injective h (by rw [h0, act_zero])), ?_⟩
  intro w hw
  have hwP : w ∈ ((h • S₀ : Sylow 2 G) : Subgroup G) := by rw [hh]; exact hWP hw
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
    MulAut.smul_def, MulAut.conj_apply, inv_inv] at hwP
  have hS : h⁻¹ * w * h ∈ S := hwP
  have e : act w (act h (toV 9)) = act h (act (h⁻¹ * w * h) (toV 9)) := by
    rw [← act_mul, ← act_mul, show h * (h⁻¹ * w * h) = w * h by group]
  rcases hline hS with h1 | h1
  · left
    rw [e, h1]
  · right
    rw [e, h1, act_neg]

theorem GFacts.case_bot (F : GFacts mem) {W : Subgroup G} (hW : Irr W)
    (h3 : ∀ x ∈ W, ∀ k, orderOf x = 3 ^ k → x = 1) :
    ∃ U : Subgroup G, U ≤ W ∧ (U.subgroupOf W).Normal ∧ Nat.card U = 13 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 13) := ⟨by decide⟩
  have h3W : ¬ 3 ∣ Nat.card W := by
    intro hd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 hd
    have hx1 := h3 x x.2 1 (by rw [Subgroup.orderOf_coe, hx, pow_one])
    have : orderOf (x : G) = 1 := by rw [hx1, orderOf_one]
    rw [Subgroup.orderOf_coe, hx] at this
    omega
  have hW416 : Nat.card W ∣ 2 ^ 5 * 13 := by
    have h1 : Nat.card W ∣ 3 ^ 3 * (2 ^ 5 * 13) := by
      rw [show 3 ^ 3 * (2 ^ 5 * 13) = 11232 by norm_num, ← card_G]
      exact Subgroup.card_subgroup_dvd_card W
    have hcop : Nat.Coprime (Nat.card W) (3 ^ 3) :=
      Nat.Coprime.pow_right 3 (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd
        Nat.prime_three).2 h3W))
    exact hcop.dvd_of_dvd_mul_left h1
  by_cases h13 : 13 ∣ Nat.card W
  · obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 13 W))
    have hidx : ¬ 13 ∣ (S : Subgroup W).index := S.not_dvd_index
    have hcm := Subgroup.card_mul_index (S : Subgroup W)
    have hidx32 : (S : Subgroup W).index ∣ 2 ^ 5 := by
      have h1 : (S : Subgroup W).index ∣ 13 * 2 ^ 5 := by
        rw [mul_comm]
        exact (Dvd.intro_left _ hcm).trans hW416
      exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (by decide)).2 hidx)).dvd_of_dvd_mul_left
        h1
    have hn1 : Nat.card (Sylow 13 W) = 1 := by
      have hdvd := (Sylow.card_dvd_index S).trans hidx32
      obtain ⟨a, ha, hna⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
      have hmod := card_sylow_modEq_one 13 W
      rw [hna] at hmod ⊢
      interval_cases a <;> simp_all [Nat.ModEq]
    have : Subsingleton (Sylow 13 W) := (Nat.card_eq_one_iff_unique.1 hn1).1
    have hSn := Sylow.normal_of_subsingleton S
    have hScard : Nat.card S = 13 := by
      obtain ⟨b, hb⟩ := S.isPGroup'.exists_card_eq
      have hb1 : b ≤ 1 := by
        by_contra hb1
        have : 13 ^ 2 ∣ 2 ^ 5 * 13 := (Nat.pow_dvd_pow 13 (by omega : 2 ≤ b)).trans
          (hb ▸ (Dvd.intro _ hcm).trans hW416)
        norm_num at this
      have hb0 : b ≠ 0 := by
        rintro rfl
        rw [hb, pow_zero, one_mul] at hcm
        exact hidx (by rw [hcm]; exact h13)
      have : b = 1 := by omega
      rw [hb, this, pow_one]
    refine ⟨(S : Subgroup W).map W.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
    · rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective W.subtype_injective]
      exact hSn
    · rw [Subgroup.card_map_of_injective W.subtype_injective, hScard]
  · exfalso
    have h2 : Nat.card W ∣ 2 ^ 5 := (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd
      (by decide)).2 h13)).dvd_of_dvd_mul_right hW416
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
    obtain ⟨v, hv, hvW⟩ := F.line_of_two_group (IsPGroup.of_card hm)
    have hinv : ∀ w ∈ W, ∀ b ∈ AddSubgroup.zmultiples v, act w b ∈ AddSubgroup.zmultiples v := by
      intro w hw b hb
      obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hb
      rw [show act w (k • v) = k • act w v from map_zsmul (actHom w) k v]
      rcases hvW w hw with h | h <;> rw [h]
      · exact AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples v) k
      · rw [smul_neg]
        exact AddSubgroup.neg_mem _ (AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples v) k)
    rcases hW _ hinv with h | h
    · have := AddSubgroup.mem_zmultiples v
      rw [h, AddSubgroup.mem_bot] at this
      exact hv this
    · have := card_zmultiples_V hv
      rw [h, card_top_V] at this
      omega

private theorem false_k1 (F : GFacts mem) {j : ℕ} (hj : j ∈ [1, 2, 3, 4, 5, 7, 8, 11])
    {W : Subgroup G} (hW : Irr W) {g : G}
    (hN : Normalizes W ((mem j).map (MulAut.conj g).toMonoidHom)) {P : Prop} : P := by
  obtain ⟨v, hv, hle⟩ := F.kind1 j hj
  have hj13 : j < 13 := by simp at hj; omega
  have hj0 : j ≠ 0 := by simp at hj; omega
  exact (GFacts.false_of_fix hv hle (F.ne_bot j hj13 hj0) hW hN).elim

theorem GFacts.sixSevenGL (F : GFacts mem) {W : Subgroup G} (hW : Irr W) :
    (∃ Bi : Fin 3 → AddSubgroup V, (∀ i, Nat.card (Bi i) = 3) ∧ (⨆ i, Bi i) = ⊤ ∧
        (∀ w ∈ W, ∀ i, ∃ j, ∀ v ∈ Bi i, act w v ∈ Bi j) ∧ Nat.card W ∣ 48) ∨
      (∃ U : Subgroup G, U ≤ W ∧ (U.subgroupOf W).Normal ∧ Nat.card U = 13) ∨
      (∃ U : Subgroup G, U ≤ W ∧ (U.subgroupOf W).Normal ∧
        Nonempty (U ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 3))) := by
  obtain ⟨X, hX⟩ : ∃ X : Subgroup G,
      X = Subgroup.closure {x | x ∈ W ∧ ∃ k, orderOf x = 3 ^ k} := ⟨_, rfl⟩
  have hXW : X ≤ W := by
    rw [hX]
    exact (Subgroup.closure_le W).2 fun x hx => hx.1
  have hsub : ∀ x ∈ W, (∃ k, orderOf x = 3 ^ k) → x ∈ X := fun x hx hk => by
    rw [hX]
    exact Subgroup.subset_closure ⟨hx, hk⟩
  have hgen : Subgroup.closure {x : G | x ∈ X ∧ ∃ k, orderOf x = 3 ^ k} = X := by
    apply le_antisymm
    · exact (Subgroup.closure_le X).2 fun x hx => hx.1
    · rw [hX]
      exact Subgroup.closure_mono fun x hx => ⟨Subgroup.subset_closure hx, hx.2⟩
  have hN : Normalizes W X := by
    intro w hw x hx
    rw [hX] at hx ⊢
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨hxW, k, hk⟩ := hx
      apply Subgroup.subset_closure
      refine ⟨W.mul_mem (W.mul_mem (W.inv_mem hw) hxW) hw, k, ?_⟩
      have e : w⁻¹ * x * w = MulAut.conj w⁻¹ x := by rw [MulAut.conj_apply, inv_inv]
      rw [e, MulEquiv.orderOf_eq, hk]
    | one =>
      rw [mul_one, inv_mul_cancel]
      exact Subgroup.one_mem _
    | mul x y _ _ hx hy =>
      have e : w⁻¹ * (x * y) * w = (w⁻¹ * x * w) * (w⁻¹ * y * w) := by group
      rw [e]
      exact Subgroup.mul_mem _ hx hy
    | inv x _ hx =>
      have e : w⁻¹ * x⁻¹ * w = (w⁻¹ * x * w)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ hx
  have hbot : (⊥ : Subgroup G) ∈ fam mem :=
    ⟨0, by norm_num, 1, by rw [F.zero, Subgroup.map_bot]⟩
  obtain ⟨j, hj, g, hjg⟩ :=
    CFSG.Sp43.mem_of_join_closed_pElt (fam mem) F.join_closed hgen hbot bot_le
  rw [hjg] at hN hXW
  interval_cases j
  · refine Or.inr (Or.inl (F.case_bot hW fun x hx k hk => ?_))
    have hxX := hsub x hx ⟨k, hk⟩
    rw [hjg, F.zero, Subgroup.map_bot, Subgroup.mem_bot] at hxX
    exact hxX
  · exact false_k1 F (by decide) hW hN
  · exact false_k1 F (by decide) hW hN
  · exact false_k1 F (by decide) hW hN
  · exact false_k1 F (by decide) hW hN
  · exact false_k1 F (by decide) hW hN
  · exact Or.inl (F.case_A4 hN)
  · exact false_k1 F (by decide) hW hN
  · exact false_k1 F (by decide) hW hN
  · exact Or.inr (Or.inl (F.case_13 hN hXW))
  · obtain ⟨f, hf, hle⟩ := F.kind2
    exact (GFacts.false_of_cofix hf hle (F.ne_bot 10 (by norm_num) (by norm_num)) hW hN).elim
  · exact false_k1 F (by decide) hW hN
  · exact Or.inr (Or.inr (F.case_SL hN hXW))

end CFSG.KC.GL33K

end
