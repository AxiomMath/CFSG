module

public import CFSG.LargeExtraspecial.S3Thompson
public import CFSG.LargeExtraspecial.Transport

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup

section Generic

variable {G : Type*} [Group G]

private theorem exists_mem_normalizer_not_mem_of_lt [Finite G] {P S₀ : Subgroup G}
    (hP : IsPGroup 2 P) (hlt : S₀ < P) :
    ∃ x ∈ P, x ∉ S₀ ∧ x ∈ normalizer (S₀ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent P := hP.isNilpotent
  have hlt' : S₀.subgroupOf P < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hlt.not_ge fun x hx => ?_
    have hx' : (⟨x, hx⟩ : P) ∈ S₀.subgroupOf P := by
      rw [htop]
      trivial
    exact mem_subgroupOf.mp hx'
  obtain ⟨y, hyN, hyP⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent (G := P) _ hlt')
  refine ⟨y, y.2, fun h => hyP (mem_subgroupOf.mpr h), ?_⟩
  have hy : y ∈ (normalizer (S₀ : Set G)).subgroupOf P := by
    rw [subgroupOf_normalizer_eq hlt.le]
    exact hyN
  exact mem_subgroupOf.mp hy

private theorem map_conj_eq_of_mem_normalizer {H : Subgroup G} {g : G}
    (hg : g ∈ normalizer (H : Set G)) : H.map (MulAut.conj g).toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_normalizer_iff.mp hg y).mp hy
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by simp [mul_assoc]⟩
    change g⁻¹ * x * g ∈ H
    rw [mem_normalizer_iff.mp hg]
    convert hx using 1
    group

private theorem conj_mul_conj (u a b : G) : u * (a * b) * u⁻¹ = u * a * u⁻¹ * (u * b * u⁻¹) := by
  group

private theorem conj_conj (u v a : G) : u * v * a * (u * v)⁻¹ = u * (v * a * v⁻¹) * u⁻¹ := by
  group

theorem sigma3_of_transvections {H : Subgroup G} {z t u₁ u₂ : G} (hzz : z * z = 1)
    (htt : t * t = 1) (hzt : z * t = t * z) (hu₁ : u₁ ∈ H) (hu₂ : u₂ ∈ H)
    (h1z : u₁ * z * u₁⁻¹ = z) (h1t : u₁ * t * u₁⁻¹ = t * z) (h2z : u₂ * z * u₂⁻¹ = t * z)
    (h2t : u₂ * t * u₂⁻¹ = t) :
    ∀ a ∈ ({z, t, t * z} : Set G), ∀ b ∈ ({z, t, t * z} : Set G), a ≠ b →
      ∃ u ∈ H, u * z * u⁻¹ = a ∧ u * t * u⁻¹ = b := by
  have h1tz : u₁ * (t * z) * u₁⁻¹ = t := by
    rw [conj_mul_conj, h1t, h1z, mul_assoc, hzz, mul_one]
  have h2tz : u₂ * (t * z) * u₂⁻¹ = z := by
    rw [conj_mul_conj, h2t, h2z, ← mul_assoc, htt, one_mul]
  intro a ha b hb hab
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · exact absurd rfl hab
  · exact ⟨1, H.one_mem, by group, by group⟩
  · exact ⟨u₁, hu₁, h1z, h1t⟩
  · refine ⟨u₁ * u₂ * u₁, H.mul_mem (H.mul_mem hu₁ hu₂) hu₁, ?_, ?_⟩
    · rw [conj_conj, conj_conj, h1z, h2z, h1tz]
    · rw [conj_conj, conj_conj, h1t, h2tz, h1z]
  · exact absurd rfl hab
  · refine ⟨u₁ * u₂, H.mul_mem hu₁ hu₂, ?_, ?_⟩
    · rw [conj_conj, h2z, h1tz]
    · rw [conj_conj, h2t, h1t]
  · refine ⟨u₂ * u₁, H.mul_mem hu₂ hu₁, ?_, ?_⟩
    · rw [conj_conj, h1z, h2z]
    · rw [conj_conj, h1t, h2tz]
  · exact ⟨u₂, hu₂, h2z, h2t⟩
  · exact absurd rfl hab

theorem mem_normalizer_closure_pair {a b x : G}
    (hxa : x * a * x⁻¹ ∈ closure ({a, b} : Set G)) (hxb : x * b * x⁻¹ ∈ closure ({a, b} : Set G))
    (hxa' : x⁻¹ * a * x ∈ closure ({a, b} : Set G))
    (hxb' : x⁻¹ * b * x ∈ closure ({a, b} : Set G)) :
    x ∈ normalizer (closure ({a, b} : Set G) : Set G) := by
  have key : ∀ y : G, y * a * y⁻¹ ∈ closure ({a, b} : Set G) →
      y * b * y⁻¹ ∈ closure ({a, b} : Set G) →
      ∀ v ∈ closure ({a, b} : Set G), y * v * y⁻¹ ∈ closure ({a, b} : Set G) := by
    intro y hya hyb v hv
    have hle : (closure ({a, b} : Set G)).map (MulAut.conj y).toMonoidHom ≤
        closure ({a, b} : Set G) := by
      rw [MonoidHom.map_closure, closure_le]
      rintro _ ⟨w, hw, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · exact hya
      · exact hyb
    exact hle ⟨v, hv, rfl⟩
  rw [mem_normalizer_iff]
  intro v
  constructor
  · exact key x hxa hxb v
  · intro hv
    have := key x⁻¹ (by simpa using hxa') (by simpa using hxb') _ hv
    simpa [mul_assoc] using this

theorem mem_closure_pair_iff {a b x : G} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    x ∈ closure ({a, b} : Set G) ↔ x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  have ha' : ∀ y, a * (a * y) = y := fun y => by rw [← mul_assoc, ha, one_mul]
  have hba : ∀ y, b * (a * y) = a * (b * y) := fun y => by rw [← mul_assoc, ← hab, mul_assoc]
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  constructor
  · intro hx
    induction hx using closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    | one => exact Or.inl rfl
    | mul x y _ _ hx hy =>
      rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
        simp only [mul_assoc, ha, hb, ha', hba, hab.symm, mul_one, one_mul, true_or, or_true]
    | inv x _ hx =>
      rcases hx with rfl | rfl | rfl | rfl <;>
        simp only [inv_one, hai, hbi, mul_inv_rev, hab.symm, true_or, or_true]
  · rintro (rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
    · exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))

end Generic

namespace Setting

variable {G : Type*} [Group G] [Finite G] (S : Setting G)

omit [Finite G] in
theorem M_le_normalizer_QG : S.M ≤ normalizer (S.QG : Set G) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro h
  constructor
  · exact S.conj_mem_QG hg
  · intro h'
    have := S.conj_mem_QG (S.M.inv_mem hg) h'
    simpa [mul_assoc] using this

theorem z_mem_Qa_of_mem_QG {g t : G} (hgt : g * S.z * g⁻¹ = t) (htQ : t ∈ S.QG)
    (hne : t ≠ S.z) : S.z ∈ S.Qa g := by
  classical
  set T := S.conjBy g with hT
  have hTz : T.z = t := hgt
  have ht1 : t ≠ 1 := by
    rw [← hTz]
    exact T.z_ne_one
  have htt : t * t = 1 := by
    rw [← hTz]
    exact T.z_mul_z
  have htM : t ∈ S.M := S.QG_le_M htQ
  have htz : t * S.z = S.z * t := S.mem_M_iff.mp htM
  have hzTM : S.z ∈ T.M := by
    rw [T.mem_M_iff, hTz]
    exact htz.symm
  set F := S.QG ⊓ centralizer ({t} : Set G) with hF
  have hFQ : F ≤ S.QG := inf_le_left
  have hFi : F.relIndex S.QG = 2 := S.relIndex_centralizer_eq_two htQ ht1 hne
  have hzF : S.z ∈ F := ⟨S.z_mem_QG, mem_centralizer_singleton_iff.mpr htz.symm⟩
  have htF : t ∈ F := ⟨htQ, mem_centralizer_singleton_iff.mpr rfl⟩
  set C := S.M ⊓ T.M with hC
  have hFC : F ≤ C := fun x hx => ⟨S.QG_le_M hx.1, show x ∈ T.M by
    rw [T.mem_M_iff, hTz]
    exact mem_centralizer_singleton_iff.mp hx.2⟩
  have hfin : {P : Subgroup G | F ≤ P ∧ P ≤ C ∧ IsPGroup 2 P}.Finite := Set.toFinite _
  obtain ⟨S₀, hFS₀, hS₀max⟩ :=
    hfin.exists_le_maximal (a := F) ⟨le_rfl, hFC, S.isPGroup_QG.to_le hFQ⟩
  have hS₀C : S₀ ≤ C := hS₀max.prop.2.1
  have hS₀2 : IsPGroup 2 S₀ := hS₀max.prop.2.2
  have hmax : ∀ P : Subgroup G, S₀ ≤ P → P ≤ C → IsPGroup 2 P → P = S₀ := fun P h1 h2 h3 =>
    (hS₀max.eq_of_le ⟨hFS₀.trans h1, h2, h3⟩ h1).symm
  have hzS₀ : S.z ∈ S₀ := hFS₀ hzF
  have htS₀ : t ∈ S₀ := hFS₀ htF
  have hzc : ∀ s ∈ S₀, S.z * s = s * S.z := fun s hs => (S.mem_M_iff.mp (hS₀C hs).1).symm
  have htc : ∀ s ∈ S₀, t * s = s * t := fun s hs => by
    have := T.mem_M_iff.mp (hS₀C hs).2
    rw [hTz] at this
    exact this.symm
  have hZ : ∀ x ∈ S₀, (∀ s ∈ S₀, x * s = s * x) → x ^ 2 = 1 →
      x = 1 ∨ x = S.z ∨ x = t ∨ x = t * S.z := by
    intro x _ hxc hx2
    have hxQ : x ∈ S.QG :=
      S.mem_QG_of_sq_eq_one_of_commute hFQ hFi hx2 fun f hf => hxc f (hFS₀ hf)
    exact (S.mem_centralizer_centralizer_iff htQ).mp
      ⟨hxQ, mem_centralizer_iff.mpr fun f hf => (hxc f (hFS₀ hf)).symm⟩
  have hnorm : ∀ n ∈ normalizer (S₀ : Set G), ∀ a ∈ S₀, (∀ s ∈ S₀, a * s = s * a) →
      a * a = 1 → a ≠ 1 →
      n * a * n⁻¹ = S.z ∨ n * a * n⁻¹ = t ∨ n * a * n⁻¹ = t * S.z := by
    intro n hn a haS hac ha2 ha1
    have h1 : n * a * n⁻¹ ∈ S₀ := (mem_normalizer_iff.mp hn a).mp haS
    have h2 : ∀ s ∈ S₀, n * a * n⁻¹ * s = s * (n * a * n⁻¹) := by
      intro s hs
      have hs' : n⁻¹ * s * n ∈ S₀ := by
        rw [mem_normalizer_iff.mp hn]
        convert hs using 1
        group
      calc n * a * n⁻¹ * s = n * (a * (n⁻¹ * s * n)) * n⁻¹ := by group
        _ = n * ((n⁻¹ * s * n) * a) * n⁻¹ := by rw [hac _ hs']
        _ = s * (n * a * n⁻¹) := by group
    have h3 : (n * a * n⁻¹) ^ 2 = 1 := by rw [conj_pow, pow_two, ha2]; group
    have h4 : n * a * n⁻¹ ≠ 1 := fun h => ha1 (by
      calc a = n⁻¹ * (n * a * n⁻¹) * n := by group
        _ = 1 := by rw [h]; group)
    rcases hZ _ h1 h2 h3 with h | h | h | h
    · exact absurd h h4
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  obtain ⟨v, hvN, hvz, hvt⟩ : ∃ v ∈ normalizer (S₀ : Set G),
      v * S.z * v⁻¹ = S.z ∧ v * t * v⁻¹ = t * S.z := by
    have hS₀M : S₀ ≤ S.M := fun s hs => (hS₀C hs).1
    have hP : IsPGroup 2 (S₀ ⊔ S.QG : Subgroup G) :=
      hS₀2.to_sup_of_normal_right' S.isPGroup_QG (hS₀M.trans S.M_le_normalizer_QG)
    have hlt : S₀ < S₀ ⊔ S.QG := by
      refine lt_of_le_of_ne le_sup_left fun h => ?_
      have hcomm : ∀ y ∈ S.QG, t * y = y * t := fun y hy => by
        have hy' : y ∈ S₀ ⊔ S.QG := mem_sup_right hy
        rw [← h] at hy'
        exact htc y hy'
      rcases S.eq_one_or_z_of_commute htQ hcomm with h' | h'
      · exact ht1 h'
      · exact hne h'
    obtain ⟨v, hvP, hvS, hvN⟩ := exists_mem_normalizer_not_mem_of_lt hP hlt
    have hvM : v ∈ S.M := sup_le hS₀M S.QG_le_M hvP
    have hvz : v * S.z * v⁻¹ = S.z := by rw [S.z_comm hvM]; group
    refine ⟨v, hvN, hvz, ?_⟩
    rcases hnorm v hvN t htS₀ htc htt ht1 with h | h | h
    · exact absurd (by
        calc t = v⁻¹ * (v * t * v⁻¹) * v := by group
          _ = v⁻¹ * (v * S.z * v⁻¹) * v := by rw [h, hvz]
          _ = S.z := by group) hne
    · exfalso
      have hvC : v ∈ C := by
        refine ⟨hvM, show v ∈ T.M from ?_⟩
        rw [T.mem_M_iff, hTz]
        calc v * t = v * t * v⁻¹ * v := by group
          _ = t * v := by rw [h]
      have hle : S₀ ⊔ zpowers v ≤ S₀ ⊔ S.QG := sup_le le_sup_left (zpowers_le.mpr hvP)
      have heq := hmax (S₀ ⊔ zpowers v) le_sup_left (sup_le hS₀C (zpowers_le.mpr hvC))
        (hP.to_le hle)
      exact hvS (heq ▸ (le_sup_right : zpowers v ≤ S₀ ⊔ zpowers v) (mem_zpowers v))
    · exact h
  by_contra hzQt
  obtain ⟨u, huN, hut, huz⟩ : ∃ u ∈ normalizer (S₀ : Set G),
      u * t * u⁻¹ = t ∧ u * S.z * u⁻¹ = t * S.z := by
    have hS₀M : S₀ ≤ T.M := fun s hs => (hS₀C hs).2
    have hP : IsPGroup 2 (S₀ ⊔ T.QG : Subgroup G) :=
      hS₀2.to_sup_of_normal_right' T.isPGroup_QG (hS₀M.trans T.M_le_normalizer_QG)
    have hlt : S₀ < S₀ ⊔ T.QG := by
      refine lt_of_le_of_ne le_sup_left fun h => hzQt ?_
      refine T.mem_QG_of_commute hzTM fun y hy => ?_
      have hy' : y ∈ S₀ ⊔ T.QG := mem_sup_right hy
      rw [← h] at hy'
      exact hzc y hy'
    obtain ⟨u, huP, huS, huN⟩ := exists_mem_normalizer_not_mem_of_lt hP hlt
    have huM : u ∈ T.M := sup_le hS₀M T.QG_le_M huP
    have hut : u * t * u⁻¹ = t := by
      rw [← hTz, T.z_comm huM]
      group
    refine ⟨u, huN, hut, ?_⟩
    rcases hnorm u huN S.z hzS₀ hzc S.z_mul_z S.z_ne_one with h | h | h
    · exfalso
      have huC : u ∈ C := by
        refine ⟨show u ∈ S.M from ?_, huM⟩
        rw [S.mem_M_iff]
        calc u * S.z = u * S.z * u⁻¹ * u := by group
          _ = S.z * u := by rw [h]
      have hle : S₀ ⊔ zpowers u ≤ S₀ ⊔ T.QG := sup_le le_sup_left (zpowers_le.mpr huP)
      have heq := hmax (S₀ ⊔ zpowers u) le_sup_left (sup_le hS₀C (zpowers_le.mpr huC))
        (hP.to_le hle)
      exact huS (heq ▸ (le_sup_right : zpowers u ≤ S₀ ⊔ zpowers u) (mem_zpowers u))
    · exact absurd (by
        calc t = u⁻¹ * (u * t * u⁻¹) * u := by group
          _ = u⁻¹ * (u * S.z * u⁻¹) * u := by rw [h, hut]
          _ = S.z := by group) hne
    · exact h
  have hg'N : v * u ∈ normalizer (S₀ : Set G) := mul_mem hvN huN
  have hg'z : (v * u) * S.z * (v * u)⁻¹ = t := by
    calc (v * u) * S.z * (v * u)⁻¹ = v * (u * S.z * u⁻¹) * v⁻¹ := by group
      _ = v * t * v⁻¹ * (v * S.z * v⁻¹) := by rw [huz]; group
      _ = t := by rw [hvt, hvz, mul_assoc, S.z_mul_z, mul_one]
  have hQa : S.Qa (v * u) = S.Qa g := S.Qa_eq_of_conj_eq (hg'z.trans hgt.symm)
  have hQS : S.QG ⊓ S₀ = F :=
    le_antisymm (fun x hx => ⟨hx.1, mem_centralizer_singleton_iff.mpr (htc x hx.2).symm⟩)
      (le_inf hFQ hFS₀)
  have hinj : Function.Injective (MulAut.conj (v * u)).toMonoidHom :=
    (MulAut.conj (v * u)).injective
  have hidx : (S.Qa g ⊓ S₀).relIndex (S.Qa g) = 2 := by
    rw [← hQa, S.Qa_eq_map, ← map_conj_eq_of_mem_normalizer hg'N, ← map_inf_eq _ _ _ hinj,
      relIndex_map_map_of_injective _ _ hinj, hQS]
    exact hFi
  exact hzQt (T.mem_QG_of_sq_eq_one_of_commute inf_le_left hidx S.z_sq fun f hf => hzc f hf.2)

theorem exists_polar_eq_zero_eq_one {u v : S.Qt} (hv : v ≠ 0) (huv : v ≠ u) :
    ∃ w, QuadraticMap.polar S.q w u = 0 ∧ QuadraticMap.polar S.q w v = 1 := by
  by_contra h
  push Not at h
  have h' : ∀ w, QuadraticMap.polar S.q w u = 0 → QuadraticMap.polar S.q w v = 0 := fun w hw =>
    (CFSG.RankThree.Literature.FSmith.zmod2_cases _).resolve_right (h w hw)
  obtain ⟨w₀, hw₀⟩ : ∃ w₀, QuadraticMap.polar S.q w₀ v = 1 := by
    by_contra h0
    push Not at h0
    apply hv
    refine S.q_nondegenerate.1 v fun w => ?_
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]
    exact (CFSG.RankThree.Literature.FSmith.zmod2_cases _).resolve_right (h0 w)
  have hw₀u : QuadraticMap.polar S.q w₀ u = 1 := by
    rcases CFSG.RankThree.Literature.FSmith.zmod2_cases (QuadraticMap.polar S.q w₀ u) with h1 | h1
    · rw [h' w₀ h1] at hw₀
      exact absurd hw₀ (by decide)
    · exact h1
  have heq : ∀ w, QuadraticMap.polar S.q w v = QuadraticMap.polar S.q w u := by
    intro w
    rcases CFSG.RankThree.Literature.FSmith.zmod2_cases (QuadraticMap.polar S.q w u) with h1 | h1
    · rw [h1, h' w h1]
    · have h2 : QuadraticMap.polar S.q (w + w₀) u = 0 := by
        rw [QuadraticMap.polar_add_left, h1, hw₀u]
        decide
      have h3 := h' _ h2
      rw [QuadraticMap.polar_add_left, hw₀] at h3
      rw [h1]
      calc QuadraticMap.polar S.q w v = QuadraticMap.polar S.q w v + 1 + 1 := by
            rw [add_assoc, show (1 : ZMod 2) + 1 = 0 from rfl, add_zero]
        _ = 1 := by rw [h3, zero_add]
  apply huv
  rw [← sub_eq_zero]
  refine S.q_nondegenerate.1 _ fun w => ?_
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm, QuadraticMap.polar_sub_right,
    heq, sub_self]

omit [Finite G] in
theorem exists_conj_eq_mul_z {t : G} (htQ : t ∈ S.QG) (ht1 : t ≠ 1) (htz : t ≠ S.z) :
    ∃ u ∈ S.QG, u * t * u⁻¹ = t * S.z := by
  obtain ⟨u, hu, hut⟩ : ∃ u ∈ S.QG, u * t ≠ t * u := by
    by_contra h
    push Not at h
    rcases S.eq_one_or_z_of_commute htQ (fun y hy => (h y hy).symm) with h' | h'
    · exact ht1 h'
    · exact htz h'
  refine ⟨u, hu, ?_⟩
  rcases S.mul_comm_or hu htQ with h | h
  · exact absurd h hut
  · calc u * t * u⁻¹ = S.z * (t * u) * u⁻¹ := by rw [h]
      _ = S.z * t := by group
      _ = t * S.z := (S.z_comm (S.QG_le_M htQ)).symm

theorem exists_conj_eq_mul_z_of_commute {t e : G} (htQ : t ∈ S.QG) (heQ : e ∈ S.QG)
    (ht1 : t ≠ 1) (htz : t ≠ S.z) (het : e ≠ t) (hetz : e ≠ t * S.z) :
    ∃ u ∈ S.QG, u * e = e * u ∧ u * t * u⁻¹ = t * S.z := by
  have hv : S.cl t ≠ 0 := fun h => by
    rcases (S.cl_eq_zero_iff htQ).mp h with h' | h'
    · exact ht1 h'
    · exact htz h'
  have huv : S.cl t ≠ S.cl e := fun h => by
    rcases (S.cl_eq_cl_iff htQ heQ).mp h with h' | h'
    · exact het h'
    · exact hetz h'
  obtain ⟨w, hw0, hw1⟩ := S.exists_polar_eq_zero_eq_one hv huv
  obtain ⟨u, hu, rfl⟩ := S.exists_cl w
  refine ⟨u, hu, (S.polar_cl_eq_zero_iff hu heQ).mp hw0, ?_⟩
  rcases S.mul_comm_or hu htQ with h | h
  · exact absurd h ((S.polar_cl_eq_one_iff hu htQ).mp hw1)
  · calc u * t * u⁻¹ = S.z * (t * u) * u⁻¹ := by rw [h]
      _ = S.z * t := by group
      _ = t * S.z := (S.z_comm (S.QG_le_M htQ)).symm

omit [Finite G] in
theorem QG_le_normalizer_pair {t : G} (htQ : t ∈ S.QG) :
    S.QG ≤ normalizer (closure ({S.z, t} : Set G) : Set G) := by
  have hz : S.z ∈ closure ({S.z, t} : Set G) := subset_closure (by simp)
  have ht : t ∈ closure ({S.z, t} : Set G) := subset_closure (by simp)
  have key : ∀ x ∈ S.QG, x * S.z * x⁻¹ ∈ closure ({S.z, t} : Set G) ∧
      x * t * x⁻¹ ∈ closure ({S.z, t} : Set G) := by
    intro x hx
    refine ⟨by rw [S.z_comm (S.QG_le_M hx)]; group; exact hz, ?_⟩
    rcases S.mul_comm_or hx htQ with h | h
    · rw [h]
      group
      exact ht
    · rw [h, show S.z * (t * x) * x⁻¹ = S.z * t by group]
      exact mul_mem hz ht
  intro x hx
  have h1 := key x hx
  have h2 := key x⁻¹ (S.QG.inv_mem hx)
  rw [inv_inv] at h2
  exact mem_normalizer_closure_pair h1.1 h1.2 h2.1 h2.2

theorem lemma_3_8_1 {g t : G} (hgt : g * S.z * g⁻¹ = t) (htQ : t ∈ S.QG) (hne : t ≠ S.z) :
    S.QG ⊔ S.Qa g ≤ normalizer (closure ({S.z, t} : Set G) : Set G) ∧
    ∀ a ∈ ({S.z, t, t * S.z} : Set G), ∀ b ∈ ({S.z, t, t * S.z} : Set G), a ≠ b →
      ∃ u ∈ S.QG ⊔ S.Qa g, u * S.z * u⁻¹ = a ∧ u * t * u⁻¹ = b := by
  set T := S.conjBy g with hT
  have hTz : T.z = t := hgt
  have hzQt : S.z ∈ T.QG := S.z_mem_Qa_of_mem_QG hgt htQ hne
  have ht1 : t ≠ 1 := by
    rw [← hTz]
    exact T.z_ne_one
  have htz : t * S.z = S.z * t := S.mem_M_iff.mp (S.QG_le_M htQ)
  refine ⟨sup_le (S.QG_le_normalizer_pair htQ) ?_, ?_⟩
  · have h := T.QG_le_normalizer_pair hzQt
    rw [hTz, Set.pair_comm] at h
    exact h
  · obtain ⟨u₁, hu₁, h1t⟩ := S.exists_conj_eq_mul_z htQ ht1 hne
    obtain ⟨u₂, hu₂, h2z⟩ := T.exists_conj_eq_mul_z hzQt S.z_ne_one (by rw [hTz]; exact hne.symm)
    rw [hTz, ← htz] at h2z
    refine sigma3_of_transvections S.z_mul_z (by rw [← hTz]; exact T.z_mul_z) htz.symm
      (mem_sup_left hu₁) (mem_sup_right hu₂) ?_ h1t h2z ?_
    · rw [S.z_comm (S.QG_le_M hu₁)]
      group
    · rw [← hTz, T.z_comm (T.QG_le_M hu₂)]
      group

theorem lemma_3_8_2 {g t e : G} (hgt : g * S.z * g⁻¹ = t) (htQ : t ∈ S.QG) (hne : t ≠ S.z)
    (heQ : e ∈ S.QG) (heQt : e ∈ S.Qa g) (he : e ∉ closure ({t, S.z} : Set G)) :
    ∀ a ∈ ({S.z, t, t * S.z} : Set G), ∀ b ∈ ({S.z, t, t * S.z} : Set G), a ≠ b →
      ∃ u ∈ (S.QG ⊔ S.Qa g) ⊓ centralizer ({e} : Set G),
        u * S.z * u⁻¹ = a ∧ u * t * u⁻¹ = b := by
  set T := S.conjBy g with hT
  have hTz : T.z = t := hgt
  have hzQt : S.z ∈ T.QG := S.z_mem_Qa_of_mem_QG hgt htQ hne
  have ht1 : t ≠ 1 := by
    rw [← hTz]
    exact T.z_ne_one
  have htz : t * S.z = S.z * t := S.mem_M_iff.mp (S.QG_le_M htQ)
  have hz : S.z ∈ closure ({t, S.z} : Set G) := subset_closure (by simp)
  have ht : t ∈ closure ({t, S.z} : Set G) := subset_closure (by simp)
  have het : e ≠ t := fun h => he (h ▸ ht)
  have hetz : e ≠ t * S.z := fun h => he (h ▸ mul_mem ht hz)
  have hez : e ≠ S.z := fun h => he (h ▸ hz)
  have hezt : e ≠ S.z * t := fun h => he (h ▸ mul_mem hz ht)
  obtain ⟨u₁, hu₁, h1e, h1t⟩ := S.exists_conj_eq_mul_z_of_commute htQ heQ ht1 hne het hetz
  obtain ⟨u₂, hu₂, h2e, h2z⟩ := T.exists_conj_eq_mul_z_of_commute hzQt heQt S.z_ne_one
    (by rw [hTz]; exact hne.symm) hez (by rw [hTz]; exact hezt)
  rw [hTz, ← htz] at h2z
  refine sigma3_of_transvections S.z_mul_z (by rw [← hTz]; exact T.z_mul_z) htz.symm
    ⟨mem_sup_left hu₁, mem_centralizer_singleton_iff.mpr h1e⟩
    ⟨mem_sup_right hu₂, mem_centralizer_singleton_iff.mpr h2e⟩ ?_ h1t h2z ?_
  · rw [S.z_comm (S.QG_le_M hu₁)]
    group
  · rw [← hTz, T.z_comm (T.QG_le_M hu₂)]
    group

theorem exists_swap {g t : G} (hgt : g * S.z * g⁻¹ = t) (htQ : t ∈ S.QG) (hne : t ≠ S.z) :
    ∃ u ∈ S.QG ⊔ S.Qa g, u * S.z * u⁻¹ = t ∧ u * t * u⁻¹ = S.z :=
  (S.lemma_3_8_1 hgt htQ hne).2 t (by simp) S.z (by simp) hne

theorem lemma_3_8_1_mulAut {g t : G} (hgt : g * S.z * g⁻¹ = t) (htQ : t ∈ S.QG)
    (hne : t ≠ S.z) (σ : closure ({S.z, t} : Set G) ≃* closure ({S.z, t} : Set G)) :
    ∃ u ∈ S.QG ⊔ S.Qa g, ∀ v (hv : v ∈ closure ({S.z, t} : Set G)),
      u * v * u⁻¹ = (σ ⟨v, hv⟩ : G) := by
  set T := S.conjBy g
  have hTz : T.z = t := hgt
  have htt : t * t = 1 := by
    rw [← hTz]
    exact T.z_mul_z
  have ht1 : t ≠ 1 := by
    rw [← hTz]
    exact T.z_ne_one
  have hzt : S.z * t = t * S.z := (S.mem_M_iff.mp (S.QG_le_M htQ)).symm
  have hzV : S.z ∈ closure ({S.z, t} : Set G) := subset_closure (by simp)
  have htV : t ∈ closure ({S.z, t} : Set G) := subset_closure (by simp)
  have himg : ∀ (w : closure ({S.z, t} : Set G)), (w : G) ≠ 1 →
      (w : G) ∈ ({S.z, t, t * S.z} : Set G) := by
    intro w hw
    rcases (mem_closure_pair_iff S.z_mul_z htt hzt).mp w.2 with h | h | h | h
    · exact absurd h hw
    · simp [h]
    · simp [h]
    · simp [h, hzt]
  have hne1 : ∀ v (hv : v ∈ closure ({S.z, t} : Set G)), v ≠ 1 → (σ ⟨v, hv⟩ : G) ≠ 1 := by
    intro v hv hv1 h
    apply hv1
    have : σ ⟨v, hv⟩ = 1 := Subtype.ext h
    rw [← map_one σ] at this
    exact congrArg Subtype.val (σ.injective this)
  have hσzt : (σ ⟨S.z, hzV⟩ : G) ≠ σ ⟨t, htV⟩ := by
    intro h
    exact hne (congrArg Subtype.val (σ.injective (Subtype.ext h))).symm
  obtain ⟨u, hu, huz, hut⟩ := (S.lemma_3_8_1 hgt htQ hne).2 _
    (himg _ (hne1 _ hzV S.z_ne_one)) _ (himg _ (hne1 _ htV ht1)) hσzt
  refine ⟨u, hu, fun v hv => ?_⟩
  induction hv using closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact huz
    · exact hut
  | one =>
    rw [mul_one, mul_inv_cancel]
    exact (congrArg Subtype.val (map_one σ)).symm
  | mul x y hx hy ihx ihy =>
    have : σ ⟨x * y, mul_mem hx hy⟩ = σ ⟨x, hx⟩ * σ ⟨y, hy⟩ := by
      rw [← map_mul]
      rfl
    rw [this, Subgroup.coe_mul, ← ihx, ← ihy]
    group
  | inv x hx ihx =>
    have : σ ⟨x⁻¹, inv_mem hx⟩ = (σ ⟨x, hx⟩)⁻¹ := by
      rw [← map_inv]
      rfl
    rw [this, Subgroup.coe_inv, ← ihx]
    group

end Setting

end CFSG.LargeExtraspecial
