module

public import CFSG.GH74.GLS.LU.Local.FiveStdSetting

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.GLS.LU.Local

open scoped Pointwise

namespace CFSG.GH74.GLS.LU.Local.Five

open CFSG.GH74.GLS.LU.Local.FiveStd

namespace FiveStdBase

theorem natCard_S {G : Type} [Group G] {ι : E → G} (hM : Model ι) {L : List E} (hL : V L) (hnd : L.Nodup) :
    Nat.card ↥(S ι L) = L.length := by
  have hinj : Set.InjOn ι {x | x ∈ L} := fun x hx y hy h => hM.inj x y (hL x hx) (hL y hy) h
  have hS : S ι L = ι '' {x | x ∈ L} := Set.ext fun g => mem_S
  rw [hS, Nat.card_image_of_injOn hinj, Nat.card_coe_set_eq]
  have : {x | x ∈ L} = (↑L.toFinset : Set E) := by ext x; simp
  rw [this, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]

theorem natCard_eq_of_coe {G : Type} [Group G] (H : Subgroup G) {ι : E → G} {L : List E}
    (h : (H : Set G) = S ι L) : Nat.card ↥H = Nat.card ↥(S ι L) :=
  Nat.card_congr (Equiv.subtypeEquivRight fun g => by rw [← SetLike.mem_coe, h])

theorem nodup_Cs (hb : baseCheck = true) : Cs.Nodup := by
  obtain ⟨-, -, -, -, h5, -⟩ := baseCheck_spec hb
  have h5' : ((Cs.map codeE).mergeSort (· ≤ ·)).Nodup := h5.imp (fun h => ne_of_lt h)
  have h6 := (List.mergeSort_perm (Cs.map codeE) (fun a b => decide (a ≤ b))).nodup_iff.1 h5'
  exact h6.of_map _

theorem sylCover_unfold (h : sylCover = true) :
    FiveStd.R1.Nodup ∧ (∀ q ∈ Syl36, q.2.2.Nodup) ∧
      ∀ c ∈ Cs, ∃ q ∈ Syl36, inL (conjI c (invE c) FiveStd.x1) q.2.2 = true ∧
        inL (conjI c (invE c) FiveStd.y1) q.2.2 = true := by
  unfold sylCover at h
  simp only [Bool.and_eq_true, nodupL_iff, List.all_eq_true, List.any_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1, h2, h3⟩

theorem mem_Syl36 {q : E × E × List E} :
    q ∈ Syl36 ↔ ∃ gx ∈ X1cands, ∃ gy ∈ Y1cands, (gx, gy, ppE gx gy 5 5) = q := by
  simp [Syl36, List.mem_flatMap, List.mem_map]

theorem X1cands_spec {g : E} (h : g ∈ X1cands) : g ∈ K1l ∧ ordE g = 5 := by
  simp only [X1cands, List.mem_filter, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2⟩

theorem Y1cands_spec {g : E} (h : g ∈ Y1cands) : g ∈ K2l ∧ ordE g = 5 := by
  simp only [Y1cands, List.mem_filter, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2⟩

theorem x1_cases : (FiveStd.x1 ∈ K1l ∧ ordE FiveStd.x1 = 5) ∨ FiveStd.x1 = oneE := by
  unfold FiveStd.x1
  rcases h : K1l.filter (fun x => ordE x == 5) with _ | ⟨g, l⟩
  · right; rfl
  · left
    have hg : g ∈ K1l.filter (fun x => ordE x == 5) := by rw [h]; exact List.mem_cons_self
    simp only [List.mem_filter, beq_iff_eq] at hg
    exact hg

theorem y1_cases : (FiveStd.y1 ∈ K2l ∧ ordE FiveStd.y1 = 5) ∨ FiveStd.y1 = oneE := by
  unfold FiveStd.y1
  rcases h : K2l.filter (fun x => ordE x == 5) with _ | ⟨g, l⟩
  · right; rfl
  · left
    have hg : g ∈ K2l.filter (fun x => ordE x == 5) := by rw [h]; exact List.mem_cons_self
    simp only [List.mem_filter, beq_iff_eq] at hg
    exact hg

theorem length_ppE (a b : E) : (ppE a b 5 5).length = 25 := by
  simp [ppE, mulLL, powers, Function.comp_def]

theorem pp_mul_formula {G : Type} [Group G] {x y : G} (hxy : x * y = y * x) (i j k l : ℕ) :
    (x ^ i * y ^ j) * (x ^ k * y ^ l) = x ^ (i + k) * y ^ (j + l) := by
  have hc : y ^ j * x ^ k = x ^ k * y ^ j := ((Commute.pow_pow hxy k j).eq).symm
  calc (x ^ i * y ^ j) * (x ^ k * y ^ l) = x ^ i * (y ^ j * x ^ k) * y ^ l := by simp only [mul_assoc]
    _ = x ^ i * (x ^ k * y ^ j) * y ^ l := by rw [hc]
    _ = x ^ (i + k) * y ^ (j + l) := by rw [pow_add, pow_add]; simp only [mul_assoc]

theorem exists_pp_sub {G : Type} [Group G] {x y : G} (hxy : x * y = y * x) (hx : x ^ 5 = 1) (hy : y ^ 5 = 1) :
    ∃ P : Subgroup G, ∀ h, h ∈ P ↔ ∃ i j : ℕ, h = x ^ i * y ^ j := by
  refine ⟨{ carrier := {h | ∃ i j : ℕ, h = x ^ i * y ^ j}, mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ },
    fun h => Iff.rfl⟩
  · rintro a b ⟨i, j, rfl⟩ ⟨k, l, rfl⟩
    exact ⟨i + k, j + l, pp_mul_formula hxy i j k l⟩
  · exact ⟨0, 0, by simp⟩
  · rintro a ⟨i, j, rfl⟩
    refine ⟨4 * i, 4 * j, ?_⟩
    apply inv_eq_of_mul_eq_one_right
    rw [pp_mul_formula hxy, show i + 4 * i = 5 * i by omega, show j + 4 * j = 5 * j by omega, pow_mul, pow_mul, hx,
      hy]
    simp

end FiveStdBase

namespace FiveStdSetting

open FiveStdBase

variable {G : Type} [Group G] [Finite G] (st : FiveStdSetting G)

omit [Finite G] in
theorem card_Cz (hb : baseCheck = true) : Nat.card ↥(Cz st.z) = 28800 := by
  obtain ⟨h1, -⟩ := baseCheck_spec hb
  rw [natCard_eq_of_coe _ st.hC, natCard_S st.model V_Cs (nodup_Cs hb), h1]

omit [Finite G] in
private theorem K1_pow5 (hb : baseCheck = true) {a : E} (ha : a ∈ K1l) (h5 : ordE a = 5) :
    validE a = true ∧ st.ι a ∈ st.K₁ ∧ st.ι a ^ 5 = 1 := by
  obtain ⟨-, hV1, -⟩ := baseCheck_spec hb
  have hv : validE a = true := hV1 a ha
  refine ⟨hv, ?_, ?_⟩
  · have : st.ι a ∈ ((st.K₁ : Subgroup G) : Set G) := by rw [st.hK₁]; exact mem_S.2 ⟨a, ha, rfl⟩
    exact this
  · have := st.model.orderOf_of_ordE hv h5 (by norm_num)
    rw [← this]
    exact pow_orderOf_eq_one _

omit [Finite G] in
private theorem K2_pow5 (hb : baseCheck = true) {a : E} (ha : a ∈ K2l) (h5 : ordE a = 5) :
    validE a = true ∧ st.ι a ∈ st.K₂ ∧ st.ι a ^ 5 = 1 := by
  obtain ⟨-, -, hV2, -⟩ := baseCheck_spec hb
  have hv : validE a = true := hV2 a ha
  refine ⟨hv, ?_, ?_⟩
  · have : st.ι a ∈ ((st.K₂ : Subgroup G) : Set G) := by rw [st.hK₂]; exact mem_S.2 ⟨a, ha, rfl⟩
    exact this
  · have := st.model.orderOf_of_ordE hv h5 (by norm_num)
    rw [← this]
    exact pow_orderOf_eq_one _

omit [Finite G] in
private theorem x1_facts (hb : baseCheck = true) :
    validE FiveStd.x1 = true ∧ st.ι FiveStd.x1 ∈ st.K₁ ∧ st.ι FiveStd.x1 ^ 5 = 1 := by
  rcases x1_cases with ⟨h1, h2⟩ | h
  · exact st.K1_pow5 hb h1 h2
  · rw [h]
    refine ⟨st.model.valid_one, ?_, ?_⟩ <;> simp [st.model.map_one]

omit [Finite G] in
private theorem y1_facts (hb : baseCheck = true) :
    validE FiveStd.y1 = true ∧ st.ι FiveStd.y1 ∈ st.K₂ ∧ st.ι FiveStd.y1 ^ 5 = 1 := by
  rcases y1_cases with ⟨h1, h2⟩ | h
  · exact st.K2_pow5 hb h1 h2
  · rw [h]
    refine ⟨st.model.valid_one, ?_, ?_⟩ <;> simp [st.model.map_one]

omit [Finite G] in
private theorem pp_sub {a b : E} (hav : validE a = true) (hbv : validE b = true)
    (haK : st.ι a ∈ st.K₁) (hbK : st.ι b ∈ st.K₂)
    (ha5 : st.ι a ^ 5 = 1) (hb5 : st.ι b ^ 5 = 1) (hnd : (ppE a b 5 5).Nodup) :
    ∃ P : Subgroup G, (P : Set G) = S st.ι (ppE a b 5 5) ∧ P ≤ Cz st.z ∧ Nat.card ↥P = 25 ∧
      ∀ h, h ∈ P ↔ ∃ i j : ℕ, h = st.ι a ^ i * st.ι b ^ j := by
  obtain ⟨P, hP⟩ := exists_pp_sub (st.hcomm _ haK _ hbK) ha5 hb5
  have hS : (P : Set G) = S st.ι (ppE a b 5 5) := by
    ext h
    rw [SetLike.mem_coe, hP, st.model.S_ppE hav hbv, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨i, j, rfl⟩
      refine ⟨i % 5, Nat.mod_lt _ (by norm_num), j % 5, Nat.mod_lt _ (by norm_num), ?_⟩
      rw [← pow_eq_pow_mod i ha5, ← pow_eq_pow_mod j hb5]
    · rintro ⟨i, -, j, -, rfl⟩
      exact ⟨i, j, rfl⟩
  refine ⟨P, hS, ?_, ?_, hP⟩
  · intro h hh
    obtain ⟨i, j, rfl⟩ := (hP h).1 hh
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (st.ι_mem_C hav) i) (Subgroup.pow_mem _ (st.ι_mem_C hbv) j)
  · rw [natCard_eq_of_coe P hS, natCard_S st.model (st.model.V_ppE hav hbv 5 5) hnd, length_ppE]

private theorem sylow_conj (R : Subgroup G) (hR : IsSylowIn 5 R (Cz st.z)) (P1 : Subgroup G)
    (hP1M : P1 ≤ Cz st.z) (hP1c : Nat.card ↥P1 = 25) (hMc : Nat.card ↥(Cz st.z) = 28800) :
    Nat.card ↥R = 25 ∧ ∃ c : Cz st.z, ∀ r ∈ R, ∃ s ∈ P1, r = (c : G) * s * (c : G)⁻¹ := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hRM : R ≤ Cz st.z := hR.1
  have hRp : IsPGroup 5 ↥(R.subgroupOf (Cz st.z)) :=
    IsPGroup.of_equiv hR.2.1 (R.subgroupOfEquivOfLe hRM).symm
  let PR : Sylow 5 ↥(Cz st.z) := hRp.toSylow hR.2.2
  have hcardP1 : Nat.card ↥(P1.subgroupOf (Cz st.z)) = 25 := by
    rw [Nat.card_congr (P1.subgroupOfEquivOfLe hP1M).toEquiv, hP1c]
  have hP1p : IsPGroup 5 ↥(P1.subgroupOf (Cz st.z)) := IsPGroup.of_card (n := 2) (by rw [hcardP1]; norm_num)
  have hP1idx : ¬ 5 ∣ (P1.subgroupOf (Cz st.z)).index := by
    have := Subgroup.card_mul_index (P1.subgroupOf (Cz st.z))
    rw [hcardP1, hMc] at this
    omega
  let PA : Sylow 5 ↥(Cz st.z) := hP1p.toSylow hP1idx
  have : Finite (Subgroup ↥(Cz st.z)) :=
    Finite.of_injective (fun H : Subgroup ↥(Cz st.z) => (H : Set ↥(Cz st.z))) SetLike.coe_injective
  refine ⟨?_, ?_⟩
  · have h1 := Sylow.card_eq_multiplicity PR
    have h2 := Sylow.card_eq_multiplicity PA
    have h3 : Nat.card ↥(R.subgroupOf (Cz st.z)) = Nat.card ↥(P1.subgroupOf (Cz st.z)) := by
      simpa [PA, PR] using h1.trans h2.symm
    rw [← hcardP1, ← h3]
    exact Nat.card_congr (R.subgroupOfEquivOfLe hRM).toEquiv.symm
  · obtain ⟨c, hc⟩ := MulAction.exists_smul_eq ↥(Cz st.z) PA PR
    refine ⟨c, fun r hr => ?_⟩
    have hc' : (MulAut.conj c • (P1.subgroupOf (Cz st.z)) : Subgroup ↥(Cz st.z)) = R.subgroupOf (Cz st.z) := by
      have := congrArg (fun P : Sylow 5 ↥(Cz st.z) => (P : Subgroup ↥(Cz st.z))) hc
      simpa [PA, PR, Sylow.coe_subgroup_smul] using this
    have hmem : (⟨r, hRM hr⟩ : ↥(Cz st.z)) ∈ MulAut.conj c • (P1.subgroupOf (Cz st.z)) := by
      rw [hc']
      exact Subgroup.mem_subgroupOf.2 hr
    obtain ⟨s, hs, hsr⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hmem
    refine ⟨(s : G), Subgroup.mem_subgroupOf.1 hs, ?_⟩
    have := congrArg Subtype.val hsr
    simpa using this.symm

theorem sylow_cover (hb : baseCheck = true) (hs : sylCover = true) :
    ∀ R : Subgroup G, IsSylowIn 5 R (Cz st.z) → ∃ q ∈ Syl36, (R : Set G) = S st.ι q.2.2 := by
  intro R hR
  obtain ⟨hnd1, hnd2, hcov⟩ := sylCover_unfold hs
  obtain ⟨hx1v, hx1K, hx15⟩ := st.x1_facts hb
  obtain ⟨hy1v, hy1K, hy15⟩ := st.y1_facts hb
  obtain ⟨P1, hP1S, hP1M, hP1c, hP1mem⟩ := st.pp_sub hx1v hy1v hx1K hy1K hx15 hy15 hnd1
  obtain ⟨hRc, c, hc⟩ := st.sylow_conj R hR P1 hP1M hP1c (st.card_Cz hb)
  obtain ⟨cE, hcEv, hcE⟩ := st.mem_C_iff.1 c.2
  obtain ⟨q, hq, hqx, hqy⟩ := hcov cE ((mem_Cs_iff cE).2 hcEv)
  obtain ⟨gx, hgx, gy, hgy, rfl⟩ := mem_Syl36.1 hq
  obtain ⟨hgxK, hgx5⟩ := X1cands_spec hgx
  obtain ⟨hgyK, hgy5⟩ := Y1cands_spec hgy
  obtain ⟨hgxv, hgxK', hgx5'⟩ := st.K1_pow5 hb hgxK hgx5
  obtain ⟨hgyv, hgyK', hgy5'⟩ := st.K2_pow5 hb hgyK hgy5
  obtain ⟨Pq, hPqS, hPqM, hPqc, hPqmem⟩ := st.pp_sub hgxv hgyv hgxK' hgyK' hgx5' hgy5' (hnd2 _ hq)
  refine ⟨(gx, gy, ppE gx gy 5 5), hq, ?_⟩
  have hVq : V (ppE gx gy 5 5) := st.model.V_ppE hgxv hgyv 5 5
  have hcx : (c : G) * st.ι FiveStd.x1 * (c : G)⁻¹ ∈ Pq := by
    have h1 := (st.model.inL_iff hVq (st.model.valid_conjI hcEv hx1v)).1 hqx
    rw [st.model.map_conjI hcEv hx1v, hcE] at h1
    rw [← SetLike.mem_coe, hPqS]
    exact h1
  have hcy : (c : G) * st.ι FiveStd.y1 * (c : G)⁻¹ ∈ Pq := by
    have h1 := (st.model.inL_iff hVq (st.model.valid_conjI hcEv hy1v)).1 hqy
    rw [st.model.map_conjI hcEv hy1v, hcE] at h1
    rw [← SetLike.mem_coe, hPqS]
    exact h1
  have hle : R ≤ Pq := by
    intro r hr
    obtain ⟨s, hsP, rfl⟩ := hc r hr
    obtain ⟨i, j, rfl⟩ := (hP1mem s).1 hsP
    have : (c : G) * (st.ι FiveStd.x1 ^ i * st.ι FiveStd.y1 ^ j) * (c : G)⁻¹ =
        ((c : G) * st.ι FiveStd.x1 * (c : G)⁻¹) ^ i * ((c : G) * st.ι FiveStd.y1 * (c : G)⁻¹) ^ j := by
      rw [conj_pow, conj_pow]
      group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hcx i) (Subgroup.pow_mem _ hcy j)
  have heq : R = Pq := Subgroup.eq_of_le_of_card_ge hle (by rw [hPqc, hRc])
  rw [heq, hPqS]

end FiveStdSetting

end CFSG.GH74.GLS.LU.Local.Five
