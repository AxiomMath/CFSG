module

public import CFSG.ClassicalInvolution.Phan.Parabolic.Decomp
public import CFSG.ClassicalInvolution.Phan.Parabolic.Generation

public section

namespace CFSG.ClassicalInvolution.Phan

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {Y : Type} [Group Y] {n : ℕ}

@[expose] noncomputable def PhanFamily.rangeHom (F : PhanFamily K p f Y n) (j : Fin n) :
    (blockEmb2 K p f n j).range →* Y :=
  (F.ι j).comp (MonoidHom.ofInjective (blockEmb2_injective n j)).symm.toMonoidHom

theorem PhanFamily.rangeHom_blockEmb2 (F : PhanFamily K p f Y n) (j : Fin n) (A : Su K p f 2)
    (h : blockEmb2 K p f n j A ∈ (blockEmb2 K p f n j).range) :
    F.rangeHom j ⟨blockEmb2 K p f n j A, h⟩ = F.ι j A := by
  simp only [PhanFamily.rangeHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    ofInjective_symm_apply_self]

@[expose] def PhanFamily.IsBlockHom (F : PhanFamily K p f Y n) (J : Set (Fin n))
    (φ : blockSup K p f n J →* Y) : Prop :=
  ∀ (j : Fin n) (hj : j ∈ J) (A : Su K p f 2),
    φ ⟨blockEmb2 K p f n j A, blockEmb2_mem_blockSup hj A⟩ = F.ι j A

theorem PhanFamily.conj_relation (hK : Nat.card K = (p ^ f) ^ 2) (F : PhanFamily K p f Y n)
    {J : Set (Fin n)} {φN : blockSup K p f n J →* Y} (hφN : F.IsBlockHom J φN)
    (t : torus (unitaryInvolution K p f) (n + 1)) (x : blockSup K p f n J) :
    F.torusHom t * φN x * (F.torusHom t)⁻¹ =
      φN (conjAutOfNormalizer (torus_le_normalizer_blockSup hK J) t x) := by
  let S : Set (Su K p f (n + 1)) := ⋃ j ∈ J, ((blockEmb2 K p f n j).range : Set (Su K p f (n + 1)))
  have hSH : S ⊆ blockSup K p f n J := fun y hy => by
    obtain ⟨j, hj, hy'⟩ := Set.mem_iUnion₂.1 hy
    exact range_blockEmb2_le_blockSup hj hy'
  have hSN : Subgroup.closure {x : blockSup K p f n J | (x : Su K p f (n + 1)) ∈ S} = ⊤ :=
    closure_eq_top_of_le_closure hSH (iSup₂_le fun j hj y hy =>
      Subgroup.subset_closure (Set.mem_iUnion₂.2 ⟨j, hj, hy⟩))
  let ST : Set (torus (unitaryInvolution K p f) (n + 1)) :=
    Set.range fun q : Fin n × normOne (unitaryInvolution K p f) =>
      torusEquiv (unitaryInvolution K p f) n (Pi.mulSingle q.1 q.2)
  have hST : Subgroup.closure ST = ⊤ := by
    rw [eq_top_iff]
    intro t _
    obtain ⟨s, rfl⟩ := (torusEquiv (unitaryInvolution K p f) n).surjective t
    have hmem : s ∈ (Subgroup.closure ST).comap
        (torusEquiv (unitaryInvolution K p f) n).toMonoidHom := by
      rw [← Finset.univ_prod_mulSingle s]
      refine Subgroup.prod_mem _ fun k _ => ?_
      exact Subgroup.subset_closure ⟨(k, s k), rfl⟩
    exact hmem
  refine forall_conj_of_gens (torus_le_normalizer_blockSup hK J) φN F.torusHom hSN hST ?_ t x
  rintro _ ⟨⟨k, u⟩, rfl⟩ y hy
  have hy' : ∃ j ∈ J, ∃ A, blockEmb2 K p f n j A = (y : Su K p f (n + 1)) := by
    obtain ⟨j, hj, A, hA⟩ := Set.mem_iUnion₂.1 hy
    exact ⟨j, hj, A, hA⟩
  obtain ⟨j, hj, A, hA⟩ := hy'
  have hy1 : y = ⟨blockEmb2 K p f n j A, blockEmb2_mem_blockSup hj A⟩ := Subtype.ext hA.symm
  have hconj : conjAutOfNormalizer (torus_le_normalizer_blockSup hK J)
      (torusEquiv (unitaryInvolution K p f) n (Pi.mulSingle k u)) y =
      ⟨blockEmb2 K p f n j (conjDiag hK (blockTuple k j u) A),
        blockEmb2_mem_blockSup hj _⟩ := by
    refine Subtype.ext ?_
    rw [coe_conjAutOfNormalizer, hy1]
    change ((torusEquiv (unitaryInvolution K p f) n (Pi.mulSingle k u) :
        torus (unitaryInvolution K p f) (n + 1)) : Su K p f (n + 1)) *
          blockEmb2 K p f n j A *
        ((torusEquiv (unitaryInvolution K p f) n (Pi.mulSingle k u) :
          torus (unitaryInvolution K p f) (n + 1)) : Su K p f (n + 1))⁻¹ = _
    rw [coe_torusEquiv_mulSingle]
    exact blockEmb2_torusTwo_mul_blockEmb2_mul_inv hK k j u A
  rw [hconj, hy1, hφN j hj A, hφN j hj, F.torusHom_torusEquiv_mulSingle]
  exact F.conj_torusFactor hK k j u A

section BlockHom

theorem PhanFamily.exists_blockHom_empty (F : PhanFamily K p f Y n) :
    ∃ φN : blockSup K p f n (∅ : Set (Fin n)) →* Y, F.IsBlockHom ∅ φN :=
  ⟨1, fun _ hj => absurd hj (by simp)⟩

theorem PhanFamily.exists_blockHom_singleton (F : PhanFamily K p f Y n) (i : Fin n) :
    ∃ φN : blockSup K p f n {i} →* Y, F.IsBlockHom {i} φN := by
  refine ⟨(F.rangeHom i).comp (MulEquiv.subgroupCongr (blockSup_singleton i)).toMonoidHom, ?_⟩
  intro j hj A
  obtain rfl : j = i := hj
  exact F.rangeHom_blockEmb2 j A _

theorem PhanFamily.exists_blockHom_pair_far (F : PhanFamily K p f Y n) {a b : Fin n}
    (hab : (a : ℕ) + 1 < b) :
    ∃ φN : blockSup K p f n {a, b} →* Y, F.IsBlockHom {a, b} φN := by
  have hNT := range_blockEmb2_le_normalizer_far (K := K) (p := p) (f := f) hab
  obtain ⟨φ, h1, h2⟩ := exists_hom_sup_of_normalizes hNT (F.rangeHom a) (F.rangeHom b)
    (fun g hN hT => by
      have hg : g = 1 := Subgroup.mem_bot.1 (range_blockEmb2_inf_far (K := K) (p := p) (f := f)
        hab ▸ ⟨hN, hT⟩)
      rw [show (⟨g, hN⟩ : (blockEmb2 K p f n a).range) = 1 from Subtype.ext hg,
        show (⟨g, hT⟩ : (blockEmb2 K p f n b).range) = 1 from Subtype.ext hg, map_one, map_one])
    (fun t m => by
      obtain ⟨B, hB⟩ := t.2
      obtain ⟨A, hA⟩ := m.2
      have ht : t = ⟨blockEmb2 K p f n b B, B, rfl⟩ := Subtype.ext hB.symm
      have hm : m = ⟨blockEmb2 K p f n a A, A, rfl⟩ := Subtype.ext hA.symm
      have hc : conjAutOfNormalizer hNT t m = m := by
        refine Subtype.ext ?_
        rw [coe_conjAutOfNormalizer, ht, hm]
        exact mul_inv_eq_iff_eq_mul.2 (blockEmb2_comm n a b hab A B).symm
      have e1 : F.rangeHom b t = F.ι b B := by
        rw [ht]
        exact F.rangeHom_blockEmb2 b B _
      have e2 : F.rangeHom a m = F.ι a A := by
        rw [hm]
        exact F.rangeHom_blockEmb2 a A _
      rw [hc, e1, e2]
      exact mul_inv_eq_iff_eq_mul.2 (F.comm a b hab A B).symm)
  refine ⟨φ.comp (MulEquiv.subgroupCongr (blockSup_pair a b)).toMonoidHom, ?_⟩
  intro j hj A
  rcases hj with rfl | hj
  · exact (h1 ⟨blockEmb2 K p f n j A, A, rfl⟩).trans (F.rangeHom_blockEmb2 j A _)
  · obtain rfl : j = b := hj
    exact (h2 ⟨blockEmb2 K p f n j A, A, rfl⟩).trans (F.rangeHom_blockEmb2 j A _)

theorem PhanFamily.exists_blockHom_pair_succ (F : PhanFamily K p f Y n) (i : Fin n)
    (h : (i : ℕ) + 1 < n) (J : Set (Fin n)) (hJ : J = {i, ⟨i + 1, h⟩}) :
    ∃ φN : blockSup K p f n J →* Y, F.IsBlockHom J φN := by
  have hle : blockSup K p f n J ≤ (blockEmb3 K p f n i h).range := by
    rw [hJ, blockSup_pair]
    exact sup_le (range_blockEmb2_le_range_blockEmb3 n i h)
      (range_blockEmb2_succ_le_range_blockEmb3 n i h)
  let ψ : blockSup K p f n J →* Y :=
    ((F.θ i).comp (MonoidHom.ofInjective (blockEmb3_injective n i h)).symm.toMonoidHom).comp
      (Subgroup.inclusion hle)
  have hψ : ∀ (x : blockSup K p f n J) (A : Su K p f 3),
      (x : Su K p f (n + 1)) = blockEmb3 K p f n i h A → ψ x = F.θ i A := by
    intro x A hxA
    obtain ⟨x, hx⟩ := x
    subst hxA
    exact congrArg (F.θ i) (ofInjective_symm_apply_self (blockEmb3_injective n i h) A _)
  refine ⟨ψ, ?_⟩
  intro j hj A
  rw [hJ] at hj
  rcases hj with hji | hji
  · subst hji
    refine (hψ _ (embSUid (unitaryInvolution K p f) 2 A)
      (DFunLike.congr_fun (blockEmb3_comp_embSUid_two n j h) A).symm).trans ?_
    exact F.θ_embSUid_two j h A
  · have hj' : j = ⟨i + 1, h⟩ := hji
    subst hj'
    refine (hψ _ (embSUid (unitaryInvolution K p f) 0 A)
      (DFunLike.congr_fun (blockEmb3_comp_embSUid_zero n i h) A).symm).trans ?_
    exact F.θ_embSUid_zero i h A

theorem PhanFamily.exists_blockHom (F : PhanFamily K p f Y n) {J : Set (Fin n)}
    (hJ : J.encard ≤ 2) : ∃ φN : blockSup K p f n J →* Y, F.IsBlockHom J φN := by
  rcases hJ.lt_or_eq with h | h
  · have h1 : J.encard ≤ 1 := by
      have : (2 : ℕ∞) = 1 + 1 := by norm_num
      rw [this] at h
      exact (ENat.lt_add_one_iff (by simp)).1 h
    rcases Set.encard_le_one_iff_eq.1 h1 with rfl | ⟨a, rfl⟩
    · exact F.exists_blockHom_empty
    · exact F.exists_blockHom_singleton a
  · obtain ⟨a, b, hab, rfl⟩ := Set.encard_eq_two.1 h
    have key : ∀ a b : Fin n, a < b → ∃ φN : blockSup K p f n {a, b} →* Y,
        F.IsBlockHom {a, b} φN := by
      intro a b hlt
      by_cases hfar : (a : ℕ) + 1 < b
      · exact F.exists_blockHom_pair_far hfar
      · have hb : (b : ℕ) = a + 1 := by omega
        have hai : (a : ℕ) + 1 < n := by omega
        obtain rfl : b = ⟨a + 1, hai⟩ := Fin.ext hb
        exact F.exists_blockHom_pair_succ a hai _ rfl
    rcases lt_or_gt_of_ne hab with hlt | hlt
    · exact key a b hlt
    · obtain ⟨φN, hφN⟩ := key b a hlt
      refine ⟨φN.comp (MulEquiv.subgroupCongr (by rw [Set.pair_comm])).toMonoidHom, ?_⟩
      intro j hj A
      exact hφN j (by rwa [Set.pair_comm]) A

end BlockHom

theorem PhanFamily.blockHom_agree (F : PhanFamily K p f Y n) {J : Set (Fin n)}
    (hJ : J.encard ≤ 2) {φN : blockSup K p f n J →* Y} (hφN : F.IsBlockHom J φN)
    (g : Su K p f (n + 1)) (hN : g ∈ blockSup K p f n J)
    (hT : g ∈ torus (unitaryInvolution K p f) (n + 1)) :
    φN ⟨g, hN⟩ = F.torusHom ⟨g, hT⟩ := by
  rcases torus_inf_blockSup hJ hN hT with rfl | ⟨a, ha, b, hb, u, v, rfl⟩
  · exact (map_one φN).trans (map_one F.torusHom).symm
  · have hxN := blockEmb2_mem_blockSup ha (torusTwo (unitaryInvolution K p f) u)
    have hyN := blockEmb2_mem_blockSup hb (torusTwo (unitaryInvolution K p f) v)
    have hxT := blockEmb2_torusTwo_mem_torus (K := K) (p := p) (f := f) a u
    have hyT := blockEmb2_torusTwo_mem_torus (K := K) (p := p) (f := f) b v
    have e1 : φN ⟨_, hN⟩ = φN ⟨_, hxN⟩ * φN ⟨_, hyN⟩ := by
      rw [← map_mul]
      rfl
    have e2 : F.torusHom ⟨_, hT⟩ = F.torusHom ⟨_, hxT⟩ * F.torusHom ⟨_, hyT⟩ := by
      rw [← map_mul]
      rfl
    rw [e1, e2, F.torusHom_blockEmb2 a u hxT, F.torusHom_blockEmb2 b v hyT]
    exact congrArg₂ _ (hφN a ha _) (hφN b hb _)

@[expose] def PhanFamily.IsParabolicHom (F : PhanFamily K p f Y n) (J : Set (Fin n))
    (φ : parabolic K p f n J →* Y) : Prop :=
  (∀ (t : Su K p f (n + 1)) (ht : t ∈ torus (unitaryInvolution K p f) (n + 1)),
      φ ⟨t, torus_le_parabolic J ht⟩ = F.torusHom ⟨t, ht⟩) ∧
    ∀ (j : Fin n) (hj : j ∈ J) (A : Su K p f 2),
      φ ⟨blockEmb2 K p f n j A, blockEmb2_mem_parabolic hj A⟩ = F.ι j A

theorem PhanFamily.exists_isParabolicHom (hK : Nat.card K = (p ^ f) ^ 2)
    (F : PhanFamily K p f Y n) {J : Set (Fin n)} (hJ : J.encard ≤ 2) :
    ∃ φ : parabolic K p f n J →* Y, F.IsParabolicHom J φ := by
  obtain ⟨φN, hφN⟩ := F.exists_blockHom hJ
  obtain ⟨φ, h1, h2⟩ := exists_hom_sup_of_normalizes' (torus_le_normalizer_blockSup hK J) φN
    F.torusHom (fun g hN hT => F.blockHom_agree hJ hφN g hN hT)
    (fun t x => F.conj_relation hK hφN t x)
  exact ⟨φ, fun t ht => h2 ⟨t, ht⟩, fun j hj A =>
    (h1 ⟨blockEmb2 K p f n j A, blockEmb2_mem_blockSup hj A⟩).trans (hφN j hj A)⟩

theorem PhanFamily.isParabolicHom_unique (F : PhanFamily K p f Y n) {J : Set (Fin n)}
    {φ₁ φ₂ : parabolic K p f n J →* Y} (h₁ : F.IsParabolicHom J φ₁)
    (h₂ : F.IsParabolicHom J φ₂) : φ₁ = φ₂ := by
  refine hom_ext_of_le_closure φ₁ φ₂ (S := (torus (unitaryInvolution K p f) (n + 1) :
      Set (Su K p f (n + 1))) ∪ ⋃ j ∈ J, ((blockEmb2 K p f n j).range : Set (Su K p f (n + 1))))
    ?_ (parabolic_le_closure J) ?_
  · rintro x (hx | hx)
    · exact torus_le_parabolic J hx
    · obtain ⟨j, hj, hx'⟩ := Set.mem_iUnion₂.1 hx
      exact range_blockEmb2_le_parabolic hj hx'
  · rintro x (hx | hx)
    · exact (h₁.1 x hx).trans (h₂.1 x hx).symm
    · obtain ⟨j, hj, A, rfl⟩ := Set.mem_iUnion₂.1 hx
      exact (h₁.2 j hj A).trans (h₂.2 j hj A).symm

noncomputable def PhanFamily.parabolicHom (hK : Nat.card K = (p ^ f) ^ 2)
    (F : PhanFamily K p f Y n) (J : Set (Fin n)) (hJ : J.encard ≤ 2) :
    parabolic K p f n J →* Y :=
  Classical.choose (F.exists_isParabolicHom hK hJ)

theorem PhanFamily.isParabolicHom_parabolicHom (hK : Nat.card K = (p ^ f) ^ 2)
    (F : PhanFamily K p f Y n) {J : Set (Fin n)} (hJ : J.encard ≤ 2) :
    F.IsParabolicHom J (F.parabolicHom hK J hJ) :=
  Classical.choose_spec (F.exists_isParabolicHom hK hJ)

theorem PhanFamily.parabolicHom_torus (hK : Nat.card K = (p ^ f) ^ 2) (F : PhanFamily K p f Y n)
    {J : Set (Fin n)} (hJ : J.encard ≤ 2) (t : Su K p f (n + 1))
    (ht : t ∈ torus (unitaryInvolution K p f) (n + 1)) :
    F.parabolicHom hK J hJ ⟨t, torus_le_parabolic J ht⟩ = F.torusHom ⟨t, ht⟩ :=
  (F.isParabolicHom_parabolicHom hK hJ).1 t ht

theorem PhanFamily.parabolicHom_blockEmb2 (hK : Nat.card K = (p ^ f) ^ 2)
    (F : PhanFamily K p f Y n) {J : Set (Fin n)} (hJ : J.encard ≤ 2) {j : Fin n} (hj : j ∈ J)
    (A : Su K p f 2) :
    F.parabolicHom hK J hJ ⟨blockEmb2 K p f n j A, blockEmb2_mem_parabolic hj A⟩ = F.ι j A :=
  (F.isParabolicHom_parabolicHom hK hJ).2 j hj A

theorem PhanFamily.parabolicHom_compat (hK : Nat.card K = (p ^ f) ^ 2)
    (F : PhanFamily K p f Y n) {J J' : Set (Fin n)} (hJ : J.encard ≤ 2) (hJ' : J'.encard ≤ 2)
    (hJJ' : J' ⊆ J) (g : Su K p f (n + 1)) (hgJ' : g ∈ parabolic K p f n J')
    (hgJ : g ∈ parabolic K p f n J) :
    F.parabolicHom hK J' hJ' ⟨g, hgJ'⟩ = F.parabolicHom hK J hJ ⟨g, hgJ⟩ := by
  have hψ : F.IsParabolicHom J' ((F.parabolicHom hK J hJ).comp
      (Subgroup.inclusion (parabolic_mono hJJ'))) := by
    refine ⟨fun t ht => ?_, fun j hj A => ?_⟩
    · exact F.parabolicHom_torus hK hJ t ht
    · exact F.parabolicHom_blockEmb2 hK hJ (hJJ' hj) A
  have := F.isParabolicHom_unique (F.isParabolicHom_parabolicHom hK hJ') hψ
  exact DFunLike.congr_fun this ⟨g, hgJ'⟩

theorem range_blockEmb3_eq (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f ≠ 2) (i : Fin n)
    (h : (i : ℕ) + 1 < n) :
    (blockEmb3 K p f n i h).range =
      (blockEmb2 K p f n i).range ⊔ (blockEmb2 K p f n ⟨i + 1, h⟩).range := by
  rw [MonoidHom.range_eq_map, ← B12_sup_B23_eq_top hK hq, Subgroup.map_sup]
  congr 1
  · rw [B12, ← MonoidHom.range_comp, blockEmb3_comp_embSUid_two]
  · rw [B23, ← MonoidHom.range_comp, blockEmb3_comp_embSUid_zero]

theorem blockEmb3_mem_parabolic (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f ≠ 2) (i : Fin n)
    (h : (i : ℕ) + 1 < n) (J : Set (Fin n)) (hJ : J = {i, ⟨i + 1, h⟩}) (A : Su K p f 3) :
    blockEmb3 K p f n i h A ∈ parabolic K p f n J := by
  have hle : (blockEmb3 K p f n i h).range ≤ parabolic K p f n J := by
    rw [range_blockEmb3_eq hK hq i h]
    exact sup_le (range_blockEmb2_le_parabolic (by rw [hJ]; exact Set.mem_insert _ _))
      (range_blockEmb2_le_parabolic (by rw [hJ]; exact Set.mem_insert_of_mem _ rfl))
  exact hle ⟨A, rfl⟩

theorem parabolic_pair_succ (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f ≠ 2) (i : Fin n)
    (h : (i : ℕ) + 1 < n) (J : Set (Fin n)) (hJ : J = {i, ⟨i + 1, h⟩}) :
    parabolic K p f n J =
      torus (unitaryInvolution K p f) (n + 1) ⊔ (blockEmb3 K p f n i h).range := by
  rw [parabolic, hJ, blockSup_pair, range_blockEmb3_eq hK hq i h]

theorem PhanFamily.parabolicHom_blockEmb3 (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f ≠ 2)
    (F : PhanFamily K p f Y n) (i : Fin n) (h : (i : ℕ) + 1 < n) (J : Set (Fin n))
    (hJ : J = {i, ⟨i + 1, h⟩}) (hJ2 : J.encard ≤ 2) (A : Su K p f 3) :
    F.parabolicHom hK J hJ2 ⟨blockEmb3 K p f n i h A, blockEmb3_mem_parabolic hK hq i h J hJ A⟩ =
      F.θ i A := by
  have hi : i ∈ J := by rw [hJ]; exact Set.mem_insert _ _
  have hi1 : (⟨i + 1, h⟩ : Fin n) ∈ J := by rw [hJ]; exact Set.mem_insert_of_mem _ rfl
  let ψ₁ : Su K p f 3 →* Y := (F.parabolicHom hK J hJ2).comp
    ((blockEmb3 K p f n i h).codRestrict (parabolic K p f n J)
      (blockEmb3_mem_parabolic hK hq i h J hJ))
  have hψ₁ : ∀ A, ψ₁ A = F.parabolicHom hK J hJ2
      ⟨blockEmb3 K p f n i h A, blockEmb3_mem_parabolic hK hq i h J hJ A⟩ := fun A => rfl
  have hle : B12 K p f ⊔ B23 K p f ≤ MonoidHom.eqLocus ψ₁ (F.θ i) := by
    refine sup_le ?_ ?_
    · rintro _ ⟨B, rfl⟩
      show ψ₁ (embSUid (unitaryInvolution K p f) 2 B) =
        F.θ i (embSUid (unitaryInvolution K p f) 2 B)
      rw [hψ₁, F.θ_embSUid_two i h B, ← F.parabolicHom_blockEmb2 hK hJ2 hi B]
      congr 1
      exact Subtype.ext (DFunLike.congr_fun (blockEmb3_comp_embSUid_two n i h) B)
    · rintro _ ⟨B, rfl⟩
      show ψ₁ (embSUid (unitaryInvolution K p f) 0 B) =
        F.θ i (embSUid (unitaryInvolution K p f) 0 B)
      rw [hψ₁, F.θ_embSUid_zero i h B, ← F.parabolicHom_blockEmb2 hK hJ2 hi1 B]
      congr 1
      exact Subtype.ext (DFunLike.congr_fun (blockEmb3_comp_embSUid_zero n i h) B)
  rw [B12_sup_B23_eq_top hK hq] at hle
  exact hle (Subgroup.mem_top A)

theorem PhanFamily.comp_blockEmb_of_parabolicHom (hK : Nat.card K = (p ^ f) ^ 2)
    (hq : p ^ f ≠ 2) (F : PhanFamily K p f Y n) (ψ : Su K p f (n + 1) →* Y)
    (hψ : ∀ (J : Set (Fin n)) (hJ : J.encard ≤ 2) (g : parabolic K p f n J),
      ψ g = F.parabolicHom hK J hJ g) :
    (∀ i : Fin n, ψ.comp (blockEmb2 K p f n i) = F.ι i) ∧
      ∀ (i : Fin n) (h : (i : ℕ) + 1 < n), ψ.comp (blockEmb3 K p f n i h) = F.θ i := by
  refine ⟨fun i => MonoidHom.ext fun A => ?_, fun i h => MonoidHom.ext fun A => ?_⟩
  · have hJ2 : ({i} : Set (Fin n)).encard ≤ 2 := by simp
    have hi : i ∈ ({i} : Set (Fin n)) := rfl
    exact (hψ {i} hJ2 ⟨blockEmb2 K p f n i A, blockEmb2_mem_parabolic hi A⟩).trans
      (F.parabolicHom_blockEmb2 hK hJ2 hi A)
  · have hJ2 : ({i, ⟨i + 1, h⟩} : Set (Fin n)).encard ≤ 2 := by
      refine (Set.encard_insert_le _ _).trans ?_
      rw [Set.encard_singleton]
      norm_num
    exact (hψ _ hJ2 ⟨blockEmb3 K p f n i h A, blockEmb3_mem_parabolic hK hq i h _ rfl A⟩).trans
      (F.parabolicHom_blockEmb3 hK hq i h _ rfl hJ2 A)

end CFSG.ClassicalInvolution.Phan
