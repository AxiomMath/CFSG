module

public import CFSG.GH74.GLS.LU.Local.FiveStdRepA
public import CFSG.GH74.GLS.LU.Local.FiveStdSetting

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.GLS.LU.Local

open scoped Pointwise

namespace CFSG.GH74.GLS.LU.Local.Five

open CFSG.GH74.GLS.LU.Local.FiveStd

namespace FiveStdRep

theorem ncard_S_eq {G : Type} [Group G] {ι : E → G} (hM : Model ι) {L : List E} (hL : V L) :
    Set.ncard (S ι L) = L.toFinset.card := by
  have hS : S ι L = ι '' {x | x ∈ L} := by
    ext g
    rw [mem_S]
    exact Iff.rfl
  have hfin : ({x | x ∈ L} : Set E).Finite := L.finite_toSet
  have hinj : Set.InjOn ι {x | x ∈ L} := fun x hx y hy h => hM.inj x y (hL x hx) (hL y hy) h
  rw [hS, (Set.ncard_image_iff hfin).2 hinj, ← List.coe_toFinset, Set.ncard_coe_finset]

theorem nodup_iff_ncard_S {G : Type} [Group G] {ι : E → G} (hM : Model ι) {L : List E} (hL : V L) :
    L.Nodup ↔ Set.ncard (S ι L) = L.length := by
  rw [ncard_S_eq hM hL, List.card_toFinset, List.nodup_iff_length_dedup_eq]

theorem length_ppE_mul (a b : E) (m n : ℕ) : (ppE a b m n).length = m * n := by
  simp [ppE, mulLL, powers, List.length_flatMap, Function.comp_def, List.map_const', List.sum_replicate]

variable {G : Type} [Group G] [Finite G] (st : FiveStdSetting G)

theorem validE_zE (hb : baseCheck = true) : validE zE = true := by
  obtain ⟨-, -, -, hS, -, -, -, -, hz, -⟩ := baseCheck_spec hb
  exact hS _ hz

theorem Cs_nodup (hb : baseCheck = true) : Cs.Nodup := by
  obtain ⟨-, -, -, -, hsort, -⟩ := baseCheck_spec hb
  have h1 : ((Cs.map codeE).mergeSort (· ≤ ·)).Nodup := hsort.imp (fun h => ne_of_lt h)
  have h2 : (Cs.map codeE).Nodup := (List.mergeSort_perm _ _).nodup_iff.1 h1
  exact List.Nodup.of_map _ h2

omit [Finite G] in
theorem torus_inj_iff {a b : E} (ha : validE a = true) (hb : validE b = true) (ha4 : st.ι a ^ 4 = 1)
    (hb4 : st.ι b ^ 4 = 1) (hab : st.ι a * st.ι b = st.ι b * st.ι a) :
    nodupL (ppE a b 4 4) = true ↔ Function.Injective (z4Hom (st.ι a) (st.ι b) ha4 hb4 hab) := by
  rw [nodupL_iff, z4Hom_injective_iff, nodup_iff_ncard_S st.model (st.model.V_ppE ha hb 4 4),
    st.model.S_ppE ha hb, length_ppE_mul]


omit [Finite G] in
theorem S_z4Sub {a b : E} (ha : validE a = true) (hb : validE b = true) (ha4 : st.ι a ^ 4 = 1)
    (hb4 : st.ι b ^ 4 = 1) (hab : st.ι a * st.ι b = st.ι b * st.ι a) :
    ((z4Sub (st.ι a) (st.ι b) ha4 hb4 hab : Subgroup G) : Set G) = S st.ι (ppE a b 4 4) := by
  ext g
  rw [SetLike.mem_coe, mem_z4Sub, st.model.S_ppE ha hb]
  rfl

omit [Finite G] in
theorem pow4_of_ordE {a : E} (ha : validE a = true) (h : ordE a = 4) : st.ι a ^ 4 = 1 := by
  have := st.model.orderOf_of_ordE ha h (by norm_num)
  rw [← this]
  exact pow_orderOf_eq_one _

omit [Finite G] in
theorem V_PlOf (u : E) : V (PlOf u) := fun x hx => (mem_Cs_iff x).1 (List.mem_of_mem_filter hx)

omit [Finite G] in
theorem mem_PlOf_iff {u : E} (hz : validE zE = true) (hu : validE u = true) {x : E} :
    x ∈ PlOf u ↔ validE x = true ∧ st.ι x * st.z = st.z * st.ι x ∧ st.ι x * st.ι u = st.ι u * st.ι x := by
  unfold PlOf
  rw [List.mem_filter, mem_Cs_iff, Bool.and_eq_true]
  constructor
  · rintro ⟨hx, h1, h2⟩
    exact ⟨hx, (st.model.commE_iff hx hz).1 h1, (st.model.commE_iff hx hu).1 h2⟩
  · rintro ⟨hx, h1, h2⟩
    exact ⟨hx, (st.model.commE_iff hx hz).2 h1, (st.model.commE_iff hx hu).2 h2⟩

omit [Finite G] in
theorem P_eq {u : E} (hz : validE zE = true) (hu : validE u = true) :
    ((centralizer ((UU st.z (st.ι u) : Subgroup G) : Set G) : Subgroup G) : Set G) = S st.ι (PlOf u) := by
  ext g
  rw [SetLike.mem_coe, mem_P_iff, mem_S]
  constructor
  · rintro ⟨h1, h2⟩
    have hg : g ∈ Cz st.z := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      rw [Set.mem_singleton_iff.1 hk]
      exact h1.symm
    obtain ⟨x, hx, rfl⟩ := st.mem_C_iff.1 hg
    exact ⟨x, (mem_PlOf_iff st hz hu).2 ⟨hx, h1, h2⟩, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨-, h1, h2⟩ := (mem_PlOf_iff st hz hu).1 hx
    exact ⟨h1, h2⟩

omit [Finite G] in
theorem card_P (hb : baseCheck = true) {u : E} (hu : validE u = true) :
    Nat.card ↥(centralizer ((UU st.z (st.ι u) : Subgroup G) : Set G)) = (PlOf u).length := by
  have h1 := Nat.card_coe_set_eq ((centralizer ((UU st.z (st.ι u) : Subgroup G) : Set G) : Subgroup G) : Set G)
  rw [SetLike.coe_sort_coe] at h1
  rw [h1, P_eq st (validE_zE hb) hu,
    (nodup_iff_ncard_S st.model (V_PlOf u)).1 ((Cs_nodup hb).filter _)]

theorem normK_iff (hb : baseCheck = true) {g : E} (hg : validE g = true) :
    normK g = true ↔ cjL (st.ι g) st.K₁ = st.K₁ ∧ cjL (st.ι g) st.K₂ = st.K₂ := by
  obtain ⟨-, hK1, hK2, -⟩ := baseCheck_spec hb
  have key : ∀ (K : Subgroup G) (L : List E), V L → (K : Set G) = S st.ι L →
      ((L.all fun x => inL (conjI g (invE g) x) L) = true ↔ cjL (st.ι g) K = K) := by
    intro K L hL hKL
    rw [List.all_eq_true]
    constructor
    · intro h
      apply repCj_eq_of_le
      intro y hy
      have hy' : y ∈ S st.ι L := by rw [← hKL]; exact hy
      obtain ⟨x, hx, rfl⟩ := mem_S.1 hy'
      have := (st.model.inL_iff hL (st.model.valid_conjI hg (hL x hx))).1 (h x hx)
      rw [st.model.map_conjI hg (hL x hx), ← hKL] at this
      exact this
    · intro h x hx
      have hxK : st.ι x ∈ K := by
        rw [← SetLike.mem_coe, hKL]
        exact mem_S.2 ⟨x, hx, rfl⟩
      have h2 := repCj_mem_self (g := st.ι g) hxK
      rw [h] at h2
      rw [st.model.inL_iff hL (st.model.valid_conjI hg (hL x hx)), st.model.map_conjI hg (hL x hx), ← hKL]
      exact h2
  unfold normK
  rw [Bool.and_eq_true, key st.K₁ K1l hK1 st.hK₁, key st.K₂ K2l hK2 st.hK₂]

theorem mem_els4Of_iff {u x : E} : x ∈ els4Of u ↔ x ∈ PlOf u ∧ ordE x = 4 ∧ normK x = true := by
  unfold els4Of
  simp only [List.mem_filter, beq_iff_eq, and_assoc]

theorem isTorusPair_iff {a b : E} : isTorusPair a b = true ↔ ordE a = 4 ∧ ordE b = 4 ∧ commE a b = true ∧
    nodupL (ppE a b 4 4) = true ∧ normK a = true ∧ normK b = true := by
  unfold isTorusPair
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc]

theorem mem_tpOf_iff {u a b : E} : (a, b) ∈ tpOf u ↔ a ∈ PlOf u ∧ b ∈ PlOf u ∧ ordE a = 4 ∧ ordE b = 4 ∧
    commE a b = true ∧ nodupL (ppE a b 4 4) = true ∧ normK a = true ∧ normK b = true := by
  unfold tpOf
  simp only [List.mem_flatMap, List.mem_filterMap]
  constructor
  · rintro ⟨a', ha', b', hb', h⟩
    by_cases hT : isTorusPair a' b' = true
    · simp only [hT, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := isTorusPair_iff.1 hT
      exact ⟨(mem_els4Of_iff.1 ha').1, (mem_els4Of_iff.1 hb').1, h1, h2, h3, h4, h5, h6⟩
    · simp [hT] at h
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    refine ⟨a, mem_els4Of_iff.2 ⟨h1, h3, h7⟩, b, mem_els4Of_iff.2 ⟨h2, h4, h8⟩, ?_⟩
    have hT : isTorusPair a b = true := isTorusPair_iff.2 ⟨h3, h4, h5, h6, h7, h8⟩
    simp [hT]

theorem mem_WlOf_iff {u w : E} : w ∈ WlOf u ↔ w ∈ K1l ∧ mulE w w = zE ∧ conjE w u = mulE u zE := by
  unfold WlOf
  simp only [List.mem_filter, Bool.and_eq_true, beq_iff_eq]

theorem checkP_spec {t u a b : E} (h : checkP t u a b = true) :
    (PlOf u).length = 64 ∧
    (∀ p ∈ tpOf u, inL p.1 (ppE a b 4 4) = true ∧ inL p.2 (ppE a b 4 4) = true) ∧
    inL zE (ppE a b 4 4) = true ∧ inL u (ppE a b 4 4) = true ∧
    (∀ p ∈ PlOf u, normG p [a, b] (ppE a b 4 4) = true) ∧
    (∀ p ∈ PlOf u, inL (mulE p p) (ppE a b 4 4) = true) ∧
    (∃ w ∈ K1l, mulE w w = zE ∧ conjE w u = mulE u zE) ∧
    (∃ p ∈ PlOf u, conjE p t = mulE zE t) := by
  unfold checkP at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.any_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, ?_, h8⟩
  obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ (List.isEmpty_eq_false_iff.1 h7)
  exact ⟨w, (mem_WlOf_iff.1 hw).1, (mem_WlOf_iff.1 hw).2⟩

theorem isTorus_of_mem_tpOf (hb : baseCheck = true) {u a b : E} (hu : validE u = true)
    (h : (a, b) ∈ tpOf u) :
    ∃ H' : Subgroup G, IsTorus st.z (st.ι u) st.K₁ st.K₂ H' ∧ (H' : Set G) = S st.ι (ppE a b 4 4) := by
  have hz := validE_zE hb
  obtain ⟨haP, hbP, h4a, h4b, hc, hn, hna, hnb⟩ := mem_tpOf_iff.1 h
  have hva : validE a = true := V_PlOf u a haP
  have hvb : validE b = true := V_PlOf u b hbP
  have ha4 := pow4_of_ordE st hva h4a
  have hb4 := pow4_of_ordE st hvb h4b
  have hab := (st.model.commE_iff hva hvb).1 hc
  have hinj := (torus_inj_iff st hva hvb ha4 hb4 hab).1 hn
  refine ⟨z4Sub (st.ι a) (st.ι b) ha4 hb4 hab, ?_, S_z4Sub st hva hvb ha4 hb4 hab⟩
  unfold IsTorus
  refine ⟨?_, z4Sub_equiv hinj, ?_⟩
  · obtain ⟨-, h1, h2⟩ := (mem_PlOf_iff st hz hu).1 haP
    obtain ⟨-, h3, h4⟩ := (mem_PlOf_iff st hz hu).1 hbP
    exact z4Sub_le (mem_P_iff.2 ⟨h1, h2⟩) (mem_P_iff.2 ⟨h3, h4⟩)
  · intro h hh
    have hle : z4Sub (st.ι a) (st.ι b) ha4 hb4 hab ≤
        normalizer (st.K₁ : Set G) ⊓ normalizer (st.K₂ : Set G) :=
      z4Sub_le (mem_inf_normalizer.2 ((normK_iff st hb hva).1 hna))
        (mem_inf_normalizer.2 ((normK_iff st hb hvb).1 hnb))
    exact mem_inf_normalizer.1 (hle hh)

omit [Finite G] in
theorem mem_Cz_of_comm {g : G} (h : g * st.z = st.z * g) : g ∈ Cz st.z := by
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  rw [Set.mem_singleton_iff.1 hk]
  exact h.symm

omit [Finite G] in
theorem exists_pair_of_torus (hb : baseCheck = true) {u : E} (hu : validE u = true) {A : Subgroup G}
    (hA : ∀ h ∈ A, h * st.z = st.z * h ∧ h * st.ι u = st.ι u * h) (f : ↥A ≃* Z4Z4) :
    ∃ a b : E, validE a = true ∧ validE b = true ∧ a ∈ PlOf u ∧ b ∈ PlOf u ∧ ordE a = 4 ∧ ordE b = 4 ∧
      commE a b = true ∧ nodupL (ppE a b 4 4) = true ∧ st.ι a ∈ A ∧ st.ι b ∈ A ∧
      (A : Set G) = S st.ι (ppE a b 4 4) := by
  have hz := validE_zE hb
  obtain ⟨a', b', ha4, hb4, hab, hinj, hsub⟩ := exists_z4_of_equiv f
  have ha'A : a' ∈ A := by rw [← hsub]; exact left_mem_z4Sub
  have hb'A : b' ∈ A := by rw [← hsub]; exact right_mem_z4Sub
  have hord := orderOf_eq_four_of_inj hinj
  obtain ⟨a, hva, rfl⟩ := st.mem_C_iff.1 (mem_Cz_of_comm st (hA a' ha'A).1)
  obtain ⟨b, hvb, rfl⟩ := st.mem_C_iff.1 (mem_Cz_of_comm st (hA b' hb'A).1)
  refine ⟨a, b, hva, hvb, (mem_PlOf_iff st hz hu).2 ⟨hva, (hA _ ha'A).1, (hA _ ha'A).2⟩,
    (mem_PlOf_iff st hz hu).2 ⟨hvb, (hA _ hb'A).1, (hA _ hb'A).2⟩,
    st.model.ordE_of_orderOf hva hord.1 (by norm_num) (by norm_num),
    st.model.ordE_of_orderOf hvb hord.2 (by norm_num) (by norm_num),
    (st.model.commE_iff hva hvb).2 hab, (torus_inj_iff st hva hvb ha4 hb4 hab).2 hinj, ha'A, hb'A, ?_⟩
  rw [← hsub, S_z4Sub st hva hvb ha4 hb4 hab]

theorem torus_set_eq (hb : baseCheck = true) {t u a b : E} (hu : validE u = true)
    (hab : (a, b) ∈ tpOf u) (hP : checkP t u a b = true) {A : Subgroup G}
    (hA : IsTorus st.z (st.ι u) st.K₁ st.K₂ A) : (A : Set G) = S st.ι (ppE a b 4 4) := by
  obtain ⟨H', hH', hH'S⟩ := isTorus_of_mem_tpOf st hb hu hab
  obtain ⟨haP0, hbP0, -⟩ := mem_tpOf_iff.1 hab
  have hva0 : validE a = true := V_PlOf u a haP0
  have hvb0 : validE b = true := V_PlOf u b hbP0
  unfold IsTorus at hA hH'
  obtain ⟨hAP, ⟨f⟩, hAN⟩ := hA
  have hAc : ∀ h ∈ A, h * st.z = st.z * h ∧ h * st.ι u = st.ι u * h :=
    fun h hh => mem_P_iff.1 (hAP hh)
  obtain ⟨a', b', hva, hvb, haP, hbP, h4a, h4b, hc, hn, haA, hbA, hAS⟩ :=
    exists_pair_of_torus st hb hu hAc f
  have hna : normK a' = true := (normK_iff st hb hva).2 (hAN _ haA)
  have hnb : normK b' = true := (normK_iff st hb hvb).2 (hAN _ hbA)
  have hmem : (a', b') ∈ tpOf u := mem_tpOf_iff.2 ⟨haP, hbP, h4a, h4b, hc, hn, hna, hnb⟩
  obtain ⟨hin1, hin2⟩ := (checkP_spec hP).2.1 (a', b') hmem
  have hHa : st.ι a' ∈ H' := by
    have : st.ι a' ∈ S st.ι (ppE a b 4 4) := (st.model.inL_iff (st.model.V_ppE hva0 hvb0 4 4) hva).1 hin1
    rw [← hH'S] at this
    exact this
  have hHb : st.ι b' ∈ H' := by
    have : st.ι b' ∈ S st.ι (ppE a b 4 4) := (st.model.inL_iff (st.model.V_ppE hva0 hvb0 4 4) hvb).1 hin2
    rw [← hH'S] at this
    exact this
  have hAle : A ≤ H' := by
    intro x hx
    have hx' : x ∈ S st.ι (ppE a' b' 4 4) := by rw [← hAS]; exact hx
    rw [st.model.S_ppE hva hvb] at hx'
    obtain ⟨i, -, j, -, rfl⟩ := hx'
    exact H'.mul_mem (H'.pow_mem hHa i) (H'.pow_mem hHb j)
  have hcardA : Nat.card ↥A = 16 := (Nat.card_congr f.toEquiv).trans card_z4z4
  have hcardH : Nat.card ↥H' = 16 := (Nat.card_congr hH'.2.1.some.toEquiv).trans card_z4z4
  have hAH : A = H' := Subgroup.eq_of_le_of_card_ge hAle (by omega)
  rw [hAH, hH'S]

omit [Finite G] in
theorem pairCond_valid (hb : baseCheck = true) {t u : E} (hp : pairCond t u = true) :
    validE t = true ∧ validE u = true := by
  obtain ⟨-, -, -, hS0, -⟩ := baseCheck_spec hb
  unfold pairCond at hp
  simp only [Bool.and_eq_true, inL, List.contains_iff_mem] at hp
  obtain ⟨⟨⟨⟨⟨hA, hB⟩, -⟩, -⟩, -⟩, -⟩ := hp
  exact ⟨hS0 t (List.mem_filter.1 hA).1, hS0 u (List.mem_filter.1 hB).1⟩

end FiveStdRep

end CFSG.GH74.GLS.LU.Local.Five
