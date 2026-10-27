module

public import CFSG.GH74.BNPair.Parabolic

public section

namespace CFSG.GroupTheory.TitsSystem

open CFSG.GH74.BNPair
open scoped Pointwise

variable {G : Type*} [Group G]

structure IsBNPair (B N : Subgroup G) [(cartan B N).Normal] (S : Set (WeylGroup B N)) : Prop where
  gen : B ⊔ N = ⊤
  orderOf_eq_two : ∀ s ∈ S, orderOf s = 2
  closure_eq : Subgroup.closure S = ⊤
  mul_subset : ∀ n m : N, (n : WeylGroup B N) ∈ S →
    ({(n : G)} : Set G) * (B : Set G) * {(m : G)} ⊆
      dc B N (m : WeylGroup B N) ∪ dc B N ((n : WeylGroup B N) * (m : WeylGroup B N))
  ne : ∀ n : N, (n : WeylGroup B N) ∈ S →
    ({(n : G)} : Set G) * (B : Set G) * {(n : G)} ≠ (B : Set G)

namespace IsBNPair

variable {B N : Subgroup G} [(cartan B N).Normal] {S : Set (WeylGroup B N)}

theorem mul_self_eq_one (h : IsBNPair B N S) {s : WeylGroup B N} (hs : s ∈ S) : s * s = 1 := by
  have h2 := h.orderOf_eq_two s hs
  have := pow_orderOf_eq_one s
  rwa [h2, sq] at this

theorem bnCore (h : IsBNPair B N S) : BNCore B N S where
  mul_self_eq_one s hs := h.mul_self_eq_one hs
  ne_one s hs h1 := by
    have h2 := h.orderOf_eq_two s hs
    simp [h1] at h2
  mul_subset s hs w := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_mul.1 hx
    obtain ⟨n, hn, b₁, hb₁, b₂, hb₂, rfl⟩ := mem_dc_iff.1 hy
    obtain ⟨m, hm, b₃, hb₃, b₄, hb₄, rfl⟩ := mem_dc_iff.1 hz
    have hsub := h.mul_subset n m (by simpa [hn] using hs)
    have hmem : (n : G) * (b₂ * b₃) * (m : G) ∈
        ({(n : G)} : Set G) * (B : Set G) * {(m : G)} :=
      Set.mem_mul.2 ⟨(n : G) * (b₂ * b₃), Set.mem_mul.2 ⟨n, rfl, b₂ * b₃, B.mul_mem hb₂ hb₃, rfl⟩,
        m, rfl, rfl⟩
    have key : b₁ * (n : G) * b₂ * (b₃ * (m : G) * b₄) =
        b₁ * ((n : G) * (b₂ * b₃) * (m : G)) * b₄ := by simp only [mul_assoc]
    rw [key]
    rw [hn, hm] at hsub
    rcases hsub hmem with h1 | h1
    · exact Or.inr (mul_mem_dc h1 hb₁ hb₄)
    · exact Or.inl (mul_mem_dc h1 hb₁ hb₄)
  not_subset s hs hss := by
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective s
    have h1 : (n : WeylGroup B N) * n = 1 := h.mul_self_eq_one hs
    have hnn : (n : G) * n ∈ B := by
      have : ((n * n : N) : WeylGroup B N) = 1 := by rw [QuotientGroup.mk_mul]; exact h1
      simpa using mk_eq_one_iff.1 this
    have hmem : ∀ c ∈ B, (n : G) * c * n ∈ (B : Set G) := by
      intro c hc
      refine hss (Set.mem_mul.2 ⟨n, coe_mem_dc n, c * n, ?_, by simp [mul_assoc]⟩)
      exact mem_dc_of_mem (coe_mem_dc n) hc B.one_mem (by simp)
    refine h.ne n hs (Set.Subset.antisymm ?_ ?_)
    · rintro _ ⟨_, ⟨_, rfl, c, hc, rfl⟩, _, rfl, rfl⟩
      exact hmem c hc
    · intro b hb
      have hc : (n : G)⁻¹ * b * (n : G)⁻¹ ∈ B := by
        have h' : (n : G)⁻¹ * b * (n : G)⁻¹ =
            ((n : G) * (((n : G) * n)⁻¹ * b) * n) * ((n : G) * n)⁻¹ := by group
        rw [h']
        exact B.mul_mem (hmem _ (B.mul_mem (B.inv_mem hnn) hb)) (B.inv_mem hnn)
      exact Set.mem_mul.2 ⟨n * ((n : G)⁻¹ * b * (n : G)⁻¹),
        Set.mem_mul.2 ⟨n, rfl, _, hc, rfl⟩, n, rfl, by group⟩

theorem mem_closure (h : IsBNPair B N S) (w : WeylGroup B N) : w ∈ Subgroup.closure S := by
  rw [h.closure_eq]
  trivial

theorem ne_one (h : IsBNPair B N S) {s : WeylGroup B N} (hs : s ∈ S) : s ≠ 1 :=
  h.bnCore.ne_one s hs

theorem parabolicSubgroup_eq_top (h : IsBNPair B N S) : h.bnCore.parabolicSubgroup = ⊤ := by
  have hB : B ≤ h.bnCore.parabolicSubgroup := fun x hx => le_parabolic_one _ hx
  have hN : N ≤ h.bnCore.parabolicSubgroup := fun x hx =>
    mem_parabolicSet_iff.2 ⟨_, h.mem_closure _, coe_mem_dc (⟨x, hx⟩ : N)⟩
  rw [eq_top_iff, ← h.gen]
  exact sup_le hB hN

theorem parabolic_univ (h : IsBNPair B N S) : parabolic B N S = ⊤ := by
  rw [h.bnCore.parabolic_eq]
  exact h.parabolicSubgroup_eq_top

theorem iUnion_dc (h : IsBNPair B N S) : (⋃ w, dc B N w) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  have hx : x ∈ h.bnCore.parabolicSubgroup := by
    rw [h.parabolicSubgroup_eq_top]
    trivial
  obtain ⟨w, _, hw⟩ := mem_parabolicSet_iff.1 hx
  exact ⟨w, hw⟩

theorem exists_mem_dc (h : IsBNPair B N S) (x : G) : ∃ w, x ∈ dc B N w :=
  Set.mem_iUnion.1 (h.iUnion_dc ▸ Set.mem_univ x)

theorem dc_injective (h : IsBNPair B N S) : Function.Injective (dc B N) :=
  fun w _ hww' => h.bnCore.dc_inj (h.mem_closure w) hww'

theorem pairwise_disjoint_dc (h : IsBNPair B N S) :
    Pairwise (Function.onFun Disjoint (dc B N)) := by
  intro w w' hne
  rw [Function.onFun, Set.disjoint_left]
  intro x hx hx'
  exact hne (h.dc_injective (dc_eq_of_mem hx hx'))

theorem eq_of_mem_dc (h : IsBNPair B N S) {w w' : WeylGroup B N} {x : G} (hx : x ∈ dc B N w)
    (hx' : x ∈ dc B N w') : w = w' :=
  h.dc_injective (dc_eq_of_mem hx hx')

theorem bnCore_of_subset (h : IsBNPair B N S) {J : Set (WeylGroup B N)} (hJ : J ⊆ S) :
    BNCore B N J :=
  h.bnCore.mono hJ

theorem coe_parabolic (h : IsBNPair B N S) {J : Set (WeylGroup B N)} (hJ : J ⊆ S) :
    (parabolic B N J : Set G) = parabolicSet B N J :=
  (h.bnCore_of_subset hJ).coe_parabolic

theorem le_parabolic (h : IsBNPair B N S) {J : Set (WeylGroup B N)} (hJ : J ⊆ S) :
    B ≤ parabolic B N J :=
  (h.bnCore_of_subset hJ).le_parabolic

theorem mem_parabolic_iff (h : IsBNPair B N S) {J : Set (WeylGroup B N)} (hJ : J ⊆ S) {x : G} :
    x ∈ parabolic B N J ↔ ∃ w ∈ Subgroup.closure J, x ∈ dc B N w :=
  (h.bnCore_of_subset hJ).mem_parabolic_iff

theorem mem_parabolic_iff_of_mem_dc (h : IsBNPair B N S) {J : Set (WeylGroup B N)} (hJ : J ⊆ S)
    {w : WeylGroup B N} {x : G} (hx : x ∈ dc B N w) :
    x ∈ parabolic B N J ↔ w ∈ Subgroup.closure J := by
  rw [h.mem_parabolic_iff hJ]
  constructor
  · rintro ⟨w', hw', hxw'⟩
    rwa [h.eq_of_mem_dc hx hxw']
  · intro hw
    exact ⟨w, hw, hx⟩

theorem dc_subset_parabolic (h : IsBNPair B N S) {J : Set (WeylGroup B N)} (hJ : J ⊆ S)
    {w : WeylGroup B N} (hw : w ∈ Subgroup.closure J) : dc B N w ⊆ parabolic B N J :=
  fun _ hx => (h.mem_parabolic_iff_of_mem_dc hJ hx).2 hw

theorem mem_of_mem_closure (h : IsBNPair B N S) {K : Set (WeylGroup B N)} (hKS : K ⊆ S)
    {s : WeylGroup B N} (hs : s ∈ S) (hsK : s ∈ Subgroup.closure K) : s ∈ K := by
  by_contra hsK'
  have hcore := h.bnCore
  have hK : BNCore B N K := hcore.mono hKS
  have hs1 : BNCore B N ({s} : Set (WeylGroup B N)) :=
    hcore.mono (Set.singleton_subset_iff.2 hs)
  have hs1' := hs1.mul_self_eq_one s rfl
  set P := hs1.parabolicSubgroup with hP
  have hBP : B ≤ P := fun x hx => le_parabolic_one _ hx
  have hsP : s ∈ weylSubgroup B N P := by
    obtain ⟨n, hn⟩ := QuotientGroup.mk_surjective s
    refine mem_weylSubgroup_iff.2 ⟨n, ?_, hn⟩
    exact mem_parabolicSet_iff.2 ⟨s, Subgroup.subset_closure rfl, hn ▸ coe_mem_dc n⟩
  have hWP : ∀ t ∈ weylSubgroup B N P, t = 1 ∨ t = s := by
    intro t ht
    obtain ⟨n, hnP, rfl⟩ := mem_weylSubgroup_iff.1 ht
    obtain ⟨w', hw', hnw'⟩ := mem_parabolicSet_iff.1 hnP
    have := hs1.dc_inj hw' (dc_eq_of_mem hnw' (coe_mem_dc n))
    rw [← this]
    exact eq_one_or_eq_of_mem_closure_singleton hs1' hw'
  have h1 := hK.mem_closure_inter_weylSubgroup hBP _ s hsK rfl hsP
  have hempty : K ∩ (weylSubgroup B N P : Set (WeylGroup B N)) ⊆ (∅ : Set (WeylGroup B N)) := by
    intro t ht
    rcases hWP t ht.2 with rfl | rfl
    · exact absurd rfl (hcore.ne_one _ (hKS ht.1))
    · exact absurd ht.1 hsK'
  have h2 := Subgroup.closure_mono hempty h1
  rw [Subgroup.closure_empty] at h2
  exact hcore.ne_one s hs ((Subgroup.mem_bot).1 h2)

theorem parabolic_le_iff (h : IsBNPair B N S) {J K : Set (WeylGroup B N)} (hJ : J ⊆ S)
    (hK : K ⊆ S) : parabolic B N J ≤ parabolic B N K ↔ J ⊆ K := by
  constructor
  · intro hle s hs
    obtain ⟨n, hn⟩ := QuotientGroup.mk_surjective s
    have hnJ : (n : G) ∈ parabolic B N J :=
      (h.mem_parabolic_iff_of_mem_dc hJ (hn ▸ coe_mem_dc n)).2 (Subgroup.subset_closure hs)
    have hsK := (h.mem_parabolic_iff_of_mem_dc hK (hn ▸ coe_mem_dc n)).1 (hle hnJ)
    exact h.mem_of_mem_closure hK (hJ hs) hsK
  · intro hJK
    refine Subgroup.closure_mono ?_
    intro x hx
    obtain ⟨w, hw, hxw⟩ := mem_parabolicSet_iff.1 hx
    exact mem_parabolicSet_iff.2 ⟨w, Subgroup.closure_mono hJK hw, hxw⟩

theorem parabolic_injOn (h : IsBNPair B N S) {J K : Set (WeylGroup B N)} (hJ : J ⊆ S)
    (hK : K ⊆ S) (hJK : parabolic B N J = parabolic B N K) : J = K :=
  Set.Subset.antisymm ((h.parabolic_le_iff hJ hK).1 hJK.le)
    ((h.parabolic_le_iff hK hJ).1 hJK.ge)

theorem exists_parabolic (h : IsBNPair B N S) {P : Subgroup G} (hBP : B ≤ P) :
    ∃ J ⊆ S, P = parabolic B N J := by
  set T := weylSubgroup B N P with hT
  refine ⟨S ∩ (T : Set (WeylGroup B N)), Set.inter_subset_left, ?_⟩
  have hclosure : Subgroup.closure (S ∩ (T : Set (WeylGroup B N))) = T := by
    apply le_antisymm
    · exact (Subgroup.closure_le _).2 fun x hx => hx.2
    · intro w hw
      exact h.bnCore.mem_closure_inter_weylSubgroup hBP _ w (h.mem_closure w) rfl hw
  have hset : (P : Set G) = parabolicSet B N (S ∩ (T : Set (WeylGroup B N))) := by
    ext x
    constructor
    · intro hx
      obtain ⟨w, hw⟩ := h.exists_mem_dc x
      refine mem_parabolicSet_iff.2 ⟨w, ?_, hw⟩
      rw [hclosure]
      exact mem_weylSubgroup_of_mem_dc hBP hw hx
    · intro hx
      obtain ⟨w, hw, hxw⟩ := mem_parabolicSet_iff.1 hx
      rw [hclosure] at hw
      exact dc_subset_of_mem_weylSubgroup hBP hw hxw
  unfold parabolic
  rw [← hset]
  exact (Subgroup.closure_eq P).symm

theorem existsUnique_parabolic (h : IsBNPair B N S) {P : Subgroup G} (hBP : B ≤ P) :
    ∃! J : Set (WeylGroup B N), J ⊆ S ∧ P = parabolic B N J := by
  obtain ⟨J, hJ, hPJ⟩ := h.exists_parabolic hBP
  exact ⟨J, ⟨hJ, hPJ⟩, fun K ⟨hK, hPK⟩ => h.parabolic_injOn hK hJ (hPK.symm.trans hPJ)⟩

end IsBNPair

end CFSG.GroupTheory.TitsSystem
