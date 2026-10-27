module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622K3Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622K3Aux
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622K3Psl2Overgroup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
open CFSG.Open Subgroup
open scoped MatrixGroups
open CFSG.Yardstones.Md0ec50421ce4 (catalogIs onLie)

theorem overgroup_eq_top_of_equiv_psl2 {Kg : Type} [Group Kg]
    {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hq : 11 ≤ p ^ f)
    (ε : Kg ≃* PSL(2, GaloisField p f)) {z : Kg} (hz : orderOf z = 3) (R J : Subgroup Kg)
    (hR : IsPGroup 2 R) (hzR : z ∈ normalizer (R : Set Kg)) (hnc : ∃ y ∈ R, z * y ≠ y * z)
    (hRJ : R ≤ J) (hNJ : normalizer (zpowers z : Set Kg) ≤ J) : J = ⊤ := by
  have hz' : orderOf (ε z) = 3 := (MulEquiv.orderOf_eq ε z).trans hz
  have hR' : IsPGroup 2 (R.map ε.toMonoidHom) := hR.map ε.toMonoidHom
  have hzR' : ε z ∈ normalizer ((R.map ε.toMonoidHom : Subgroup PSL(2, GaloisField p f)) :
      Set PSL(2, GaloisField p f)) := by
    have h := Subgroup.mem_map_of_mem ε.toMonoidHom hzR
    rw [Subgroup.map_equiv_normalizer_eq] at h
    exact h
  have hnc' : ∃ y ∈ R.map ε.toMonoidHom, ε z * y ≠ y * ε z := by
    obtain ⟨y, hy, hyz⟩ := hnc
    refine ⟨ε y, Subgroup.mem_map_of_mem _ hy, ?_⟩
    intro h
    exact hyz (ε.injective (by rw [map_mul, map_mul]; exact h))
  have hRJ' : R.map ε.toMonoidHom ≤ J.map ε.toMonoidHom := Subgroup.map_mono hRJ
  have hzp : (zpowers z).map ε.toMonoidHom = zpowers (ε z) :=
    MonoidHom.map_zpowers ε.toMonoidHom z
  have hNJ' : normalizer (zpowers (ε z) : Set PSL(2, GaloisField p f)) ≤ J.map ε.toMonoidHom := by
    have key := Subgroup.map_equiv_normalizer_eq (zpowers z) ε
    rw [hzp] at key
    rw [← key]
    exact Subgroup.map_mono hNJ
  have htop : J.map ε.toMonoidHom = ⊤ :=
    psl2_overgroup_eq_top hp2 hp3 hq (ε z) hz' (R.map ε.toMonoidHom) (J.map ε.toMonoidHom)
      hR' hzR' hnc' hRJ' hNJ'
  rw [eq_top_iff]
  intro g _
  have hg : ε g ∈ J.map ε.toMonoidHom := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨j, hj, hjg⟩ := Subgroup.mem_map.mp hg
  have hjg2 : ε j = ε g := hjg
  have hjg' : j = g := ε.injective hjg2
  rw [hjg'] at hj
  exact hj

theorem isLTwoIndex_cases (dd : TauCeti.LieTypeIndex) (h : IsLTwoIndex dd) :
    ∃ q : TauCeti.PrimePower, dd = .A 1 q ∧ q.p ≠ 2 := by
  rcases dd with ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | q | q | q |
    q | q | q | q | m | m | m | _
  · by_cases hn : n = 1
    · subst hn
      exact ⟨q, rfl, h⟩
    · exfalso
      simp [IsLTwoIndex, hn] at h
  all_goals (exfalso; simp [IsLTwoIndex] at h)

theorem prime_pow_seven_or_eleven_le (p e : ℕ) (hp : p.Prime) (he : 0 < e) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) (hne5 : p ^ e ≠ 5) : p ^ e = 7 ∨ 11 ≤ p ^ e := by
  have hp5 : 5 ≤ p := by
    have h2 : 2 ≤ p := hp.two_le
    have hne4 : p ≠ 4 := by
      rintro rfl
      norm_num at hp
    omega
  rcases Nat.lt_or_ge e 2 with he1 | he2
  · have he1' : e = 1 := by omega
    subst he1'
    simp only [pow_one] at hne5 ⊢
    by_cases h11 : 11 ≤ p
    · exact Or.inr h11
    · have hp10 : p ≤ 10 := by omega
      have hp57 : p = 5 ∨ p = 7 := by
        interval_cases p <;> first | (left; rfl) | (right; rfl) | (exfalso; norm_num at hp)
      rcases hp57 with rfl | rfl
      · exact absurd rfl hne5
      · exact Or.inl rfl
  · right
    calc (11 : ℕ) ≤ 5 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left hp5 2
      _ ≤ p ^ e := Nat.pow_le_pow_right hp.pos he2

theorem eleven_le_of_valid_A_one (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A 1 q).Valid) (hq2 : q.p ≠ 2) (hq3 : q.p ≠ 3) :
    q.p ^ q.exponent = 7 ∨ 11 ≤ q.p ^ q.exponent := by
  have hdup : ¬ (TauCeti.LieTypeIndex.A 1 q).IsDuplicateRepresentative :=
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).2
  have hne5 : q.p ^ q.exponent ≠ 5 := by
    intro h5
    apply hdup
    have hcard5 : q.card = 5 := (TauCeti.PrimePower.card_def q).trans h5
    exact (TauCeti.LieTypeIndex.isDuplicateRepresentative_iff
      (TauCeti.LieTypeIndex.A 1 q)).mpr (Or.inl ⟨rfl, Or.inr (Or.inl hcard5)⟩)
  exact prime_pow_seven_or_eleven_le q.p q.exponent q.prime_p q.exponent_pos hq2 hq3 hne5

theorem kFact2713Three_holds : KFact2713Three := by
  intro A _ _ L R z hcat hzL hz3 hRL hR hzN hnc
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  cases i with
  | lie d =>
    obtain ⟨dd, hv⟩ := d
    obtain ⟨hidx, hchar⟩ := hi
    obtain ⟨q, rfl, hq2⟩ := isLTwoIndex_cases dd hidx
    have hq3 : q.p ≠ 3 := by simpa using hchar
    haveI : Fact q.p.Prime := ⟨q.prime_p⟩
    have hK : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
      GaloisField.card _ _ q.exponent_pos.ne'
    let e' : ↥L ≃* PSL(2, GaloisField q.p q.exponent) :=
      e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv)
    rcases eleven_le_of_valid_A_one q hv hq2 hq3 with h7 | h11
    · left
      obtain ⟨e''⟩ := nonempty_psl_two_seven_equiv_psl_three_two (hK.trans h7)
      exact ⟨e'.trans e''⟩
    · right
      intro J hNJ hRJ
      have hz0 : orderOf (⟨z, hzL⟩ : ↥L) = 3 := (Subgroup.orderOf_mk z hzL).trans hz3
      have hR0 : IsPGroup 2 (R.subgroupOf L) := hR.comap_subtype (K := L)
      have hzR0 : (⟨z, hzL⟩ : ↥L) ∈ normalizer ((R.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
        rw [← Subgroup.subgroupOf_normalizer_eq hRL]
        exact Subgroup.mem_subgroupOf.mpr hzN
      have hnc0 : ∃ y ∈ R.subgroupOf L, (⟨z, hzL⟩ : ↥L) * y ≠ y * (⟨z, hzL⟩ : ↥L) := by
        obtain ⟨y, hy, hyz⟩ := hnc
        refine ⟨⟨y, hRL hy⟩, Subgroup.mem_subgroupOf.mpr hy, ?_⟩
        intro h
        exact hyz (congrArg Subtype.val h)
      have hRJ0 : R.subgroupOf L ≤ J.subgroupOf L := Subgroup.subgroupOf_mono L hRJ
      have hNJ0 : normalizer ((zpowers (⟨z, hzL⟩ : ↥L) : Subgroup ↥L) : Set ↥L) ≤
          J.subgroupOf L := by
        intro x hx
        have h1 : (normalizer ((zpowers (⟨z, hzL⟩ : ↥L) : Subgroup ↥L) : Set ↥L)).map L.subtype ≤
            normalizer (((zpowers (⟨z, hzL⟩ : ↥L)).map L.subtype : Subgroup A) : Set A) :=
          Subgroup.le_normalizer_map L.subtype
        have h2 : (zpowers (⟨z, hzL⟩ : ↥L)).map L.subtype = zpowers z :=
          MonoidHom.map_zpowers L.subtype ⟨z, hzL⟩
        rw [h2] at h1
        have h3 : (x : A) ∈ (normalizer ((zpowers (⟨z, hzL⟩ : ↥L) : Subgroup ↥L) :
            Set ↥L)).map L.subtype :=
          Subgroup.mem_map_of_mem L.subtype hx
        have hxN : (x : A) ∈ normalizer (zpowers z : Set A) ⊓ L :=
          Subgroup.mem_inf.mpr ⟨h1 h3, x.2⟩
        exact Subgroup.mem_subgroupOf.mpr (hNJ hxN)
      have htop := overgroup_eq_top_of_equiv_psl2 hq2 hq3 h11 e' hz0 (R.subgroupOf L)
        (J.subgroupOf L) hR0 hzR0 hnc0 hRJ0 hNJ0
      exact Subgroup.subgroupOf_eq_top.mp htop
  | _ => exact absurd hi (by simp [onLie])

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
