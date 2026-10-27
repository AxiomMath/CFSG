module

public import CFSG.GroupTheory.TitsSystem.Exchange

public section

namespace CFSG.GroupTheory.TitsSystem

open CFSG.GH74.BNPair
open scoped Pointwise

variable {G : Type*} [Group G] {B N : Subgroup G} [(cartan B N).Normal] {S : Set (WeylGroup B N)}

namespace IsBNPair

theorem parabolic_inf (h : IsBNPair B N S) {J K : Set (WeylGroup B N)} (hJ : J ⊆ S)
    (hK : K ⊆ S) : parabolic B N J ⊓ parabolic B N K = parabolic B N (J ∩ K) := by
  obtain ⟨L, hL, hPL⟩ := h.exists_parabolic (le_inf (h.le_parabolic hJ) (h.le_parabolic hK))
  have hLJ : L ⊆ J := (h.parabolic_le_iff hL hJ).1 (hPL ▸ inf_le_left)
  have hLK : L ⊆ K := (h.parabolic_le_iff hL hK).1 (hPL ▸ inf_le_right)
  have hJK : J ∩ K ⊆ S := fun x hx => hJ hx.1
  refine le_antisymm ?_ (le_inf ((h.parabolic_le_iff hJK hJ).2 Set.inter_subset_left)
    ((h.parabolic_le_iff hJK hK).2 Set.inter_subset_right))
  rw [hPL]
  exact (h.parabolic_le_iff hL hJK).2 (Set.subset_inter hLJ hLK)

theorem parabolic_sup (h : IsBNPair B N S) {J K : Set (WeylGroup B N)} (hJ : J ⊆ S)
    (hK : K ⊆ S) : parabolic B N J ⊔ parabolic B N K = parabolic B N (J ∪ K) := by
  have hJK : J ∪ K ⊆ S := Set.union_subset hJ hK
  obtain ⟨L, hL, hPL⟩ := h.exists_parabolic (P := parabolic B N J ⊔ parabolic B N K)
    ((h.le_parabolic hJ).trans le_sup_left)
  have hJL : J ⊆ L := (h.parabolic_le_iff hJ hL).1 (hPL ▸ le_sup_left)
  have hKL : K ⊆ L := (h.parabolic_le_iff hK hL).1 (hPL ▸ le_sup_right)
  have hle : parabolic B N J ⊔ parabolic B N K ≤ parabolic B N (J ∪ K) :=
    sup_le ((h.parabolic_le_iff hJ hJK).2 Set.subset_union_left)
      ((h.parabolic_le_iff hK hJK).2 Set.subset_union_right)
  have hLJK : L ⊆ J ∪ K := (h.parabolic_le_iff hL hJK).1 (hPL ▸ hle)
  rw [hPL, Set.Subset.antisymm hLJK (Set.union_subset hJL hKL)]

theorem closure_inf (h : IsBNPair B N S) {J K : Set (WeylGroup B N)} (hJ : J ⊆ S)
    (hK : K ⊆ S) :
    Subgroup.closure J ⊓ Subgroup.closure K = Subgroup.closure (J ∩ K) := by
  have hJK : J ∩ K ⊆ S := fun x hx => hJ hx.1
  refine le_antisymm ?_ (le_inf (Subgroup.closure_mono Set.inter_subset_left)
    (Subgroup.closure_mono Set.inter_subset_right))
  intro w hw
  obtain ⟨n, hn⟩ := QuotientGroup.mk_surjective w
  have hnw : (n : G) ∈ dc B N w := hn ▸ coe_mem_dc n
  have hnJ := (h.mem_parabolic_iff_of_mem_dc hJ hnw).2 (Subgroup.mem_inf.1 hw).1
  have hnK := (h.mem_parabolic_iff_of_mem_dc hK hnw).2 (Subgroup.mem_inf.1 hw).2
  have hnJK : (n : G) ∈ parabolic B N (J ∩ K) := by
    rw [← h.parabolic_inf hJ hK]
    exact Subgroup.mem_inf.2 ⟨hnJ, hnK⟩
  exact (h.mem_parabolic_iff_of_mem_dc hJK hnw).1 hnJK

theorem mem_closure_of_conj_le (h : IsBNPair B N S) {K : Set (WeylGroup B N)} (hK : K ⊆ S) :
    ∀ (k : ℕ) (n : N), wordLength S (n : WeylGroup B N) = k →
      (∀ b ∈ B, (n : G) * b * (n : G)⁻¹ ∈ parabolic B N K) →
        (n : WeylGroup B N) ∈ Subgroup.closure K := by
  have hcore := h.bnCore
  have hBP : B ≤ parabolic B N K := h.le_parabolic hK
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro n hlen hn
    by_cases hw1 : (n : WeylGroup B N) = 1
    · rw [hw1]
      exact Subgroup.one_mem _
    obtain ⟨s, hs, hdesc⟩ := exists_left_descent hcore.mul_self_eq_one
      (h.mem_closure (n : WeylGroup B N)) hw1
    obtain ⟨ns, hns⟩ := QuotientGroup.mk_surjective s
    have hdc : ∀ x ∈ dc B N s, x ∈ parabolic B N K := by
      intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hcore.dc_subset_mul_inv hs
        (h.mem_closure (n : WeylGroup B N)) hdesc x hx
      obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := (mem_dc_of_lift rfl).1 ha
      obtain ⟨b₃, hb₃, b₄, hb₄, rfl⟩ := (mem_dc_of_lift rfl).1 hb
      have hc : (n : G) * (b₂ * b₄⁻¹) * (n : G)⁻¹ ∈ parabolic B N K :=
        hn _ (B.mul_mem hb₂ (B.inv_mem hb₄))
      have e : b₁ * (n : G) * b₂ * (b₃ * (n : G) * b₄)⁻¹ =
          b₁ * ((n : G) * (b₂ * b₄⁻¹) * (n : G)⁻¹) * b₃⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hBP hb₁) hc) (Subgroup.inv_mem _ (hBP hb₃))
    have hnsP : (ns : G) ∈ parabolic B N K := hdc _ (hns ▸ coe_mem_dc ns)
    have hsK : s ∈ K := h.mem_of_mem_closure hK hs
      ((h.mem_parabolic_iff_of_mem_dc hK (hns ▸ coe_mem_dc ns)).1 hnsP)
    have hn' : ∀ b ∈ B, ((ns * n : N) : G) * b * ((ns * n : N) : G)⁻¹ ∈ parabolic B N K := by
      intro b hb
      have e : ((ns * n : N) : G) * b * ((ns * n : N) : G)⁻¹ =
          (ns : G) * ((n : G) * b * (n : G)⁻¹) * (ns : G)⁻¹ := by
        rw [Subgroup.coe_mul]
        group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hnsP (hn b hb)) (Subgroup.inv_mem _ hnsP)
    have hmk : ((ns * n : N) : WeylGroup B N) = s * (n : WeylGroup B N) := by
      rw [QuotientGroup.mk_mul, hns]
    have hrec := ih (wordLength S (s * (n : WeylGroup B N))) (by omega) (ns * n)
      (by rw [hmk]) hn'
    rw [hmk] at hrec
    have e : (n : WeylGroup B N) = s * (s * (n : WeylGroup B N)) := by
      rw [← mul_assoc, h.mul_self_eq_one hs, one_mul]
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure hsK) hrec

theorem mem_and_subset_of_conj_le (h : IsBNPair B N S) {J K : Set (WeylGroup B N)} (hJ : J ⊆ S)
    (hK : K ⊆ S) {g : G} (hg : ∀ x ∈ parabolic B N J, g * x * g⁻¹ ∈ parabolic B N K) :
    g ∈ parabolic B N K ∧ J ⊆ K := by
  have hBJ := h.le_parabolic hJ
  have hBK := h.le_parabolic hK
  obtain ⟨w, hw⟩ := h.exists_mem_dc g
  obtain ⟨n, hn, b, hb, b', hb', rfl⟩ := mem_dc_iff.1 hw
  have hnB : ∀ c ∈ B, (n : G) * c * (n : G)⁻¹ ∈ parabolic B N K := by
    intro c hc
    have hx : b'⁻¹ * c * b' ∈ parabolic B N J :=
      hBJ (B.mul_mem (B.mul_mem (B.inv_mem hb') hc) hb')
    have e : (n : G) * c * (n : G)⁻¹ =
        b⁻¹ * (b * (n : G) * b' * (b'⁻¹ * c * b') * (b * (n : G) * b')⁻¹) * b := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hBK hb)) (hg _ hx)) (hBK hb)
  have hwK : w ∈ Subgroup.closure K := by
    rw [← hn]
    exact h.mem_closure_of_conj_le hK _ n rfl hnB
  have hgK : b * (n : G) * b' ∈ parabolic B N K :=
    (h.mem_parabolic_iff_of_mem_dc hK hw).2 hwK
  refine ⟨hgK, (h.parabolic_le_iff hJ hK).1 fun x hx => ?_⟩
  have e : x = (b * (n : G) * b')⁻¹ * ((b * (n : G) * b') * x * (b * (n : G) * b')⁻¹) *
      (b * (n : G) * b') := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hgK) (hg x hx)) hgK

theorem normalizer_parabolic (h : IsBNPair B N S) {J : Set (WeylGroup B N)} (hJ : J ⊆ S) :
    Subgroup.normalizer (parabolic B N J : Set G) = parabolic B N J := by
  refine le_antisymm (fun g hg => ?_) Subgroup.le_normalizer
  exact (h.mem_and_subset_of_conj_le hJ hJ fun x hx =>
    (Subgroup.mem_normalizer_iff.1 hg x).1 hx).1

theorem eq_of_conj_eq (h : IsBNPair B N S) {J K : Set (WeylGroup B N)} (hJ : J ⊆ S) (hK : K ⊆ S)
    {g : G} (hg : (parabolic B N J).map (MulAut.conj g).toMonoidHom = parabolic B N K) :
    J = K := by
  have h1 : ∀ x ∈ parabolic B N J, g * x * g⁻¹ ∈ parabolic B N K := fun x hx => by
    rw [← hg]
    exact ⟨x, hx, rfl⟩
  have h2 : ∀ y ∈ parabolic B N K, g⁻¹ * y * g⁻¹⁻¹ ∈ parabolic B N J := fun y hy => by
    rw [← hg] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [inv_inv]
    change g⁻¹ * (g * x * g⁻¹) * g ∈ parabolic B N J
    rw [show g⁻¹ * (g * x * g⁻¹) * g = x by group]
    exact hx
  exact Set.Subset.antisymm (h.mem_and_subset_of_conj_le hJ hK h1).2
    (h.mem_and_subset_of_conj_le hK hJ h2).2

end IsBNPair

theorem bourbaki_tits_standard_parabolics {B N : Subgroup G} [(cartan B N).Normal]
    {S : Set (WeylGroup B N)} (h : IsBNPair B N S) :
    ((⋃ w : WeylGroup B N, dc B N w) = Set.univ ∧ Pairwise (Function.onFun Disjoint (dc B N)) ∧
      ∃ cs : CoxeterSystem (orderMatrix h.orderOf_eq_two) (WeylGroup B N),
        ∀ s : S, cs.simple s = s) ∧
    (∀ J ⊆ S, (parabolic B N J : Set G) = parabolicSet B N J ∧ B ≤ parabolic B N J) ∧
    (∀ P : Subgroup G, B ≤ P → ∃! J : Set (WeylGroup B N), J ⊆ S ∧ P = parabolic B N J) ∧
    (∀ J ⊆ S, ∀ K ⊆ S, J ≠ K → parabolic B N J ≠ parabolic B N K) ∧
    (∀ J ⊆ S, ∀ K ⊆ S, Subgroup.closure J ⊓ Subgroup.closure K = Subgroup.closure (J ∩ K) ∧
      parabolic B N J ⊓ parabolic B N K = parabolic B N (J ∩ K) ∧
      parabolic B N J ⊔ parabolic B N K = parabolic B N (J ∪ K)) ∧
    (∀ J ⊆ S, ∀ K ⊆ S, ∀ g : G, (∀ x ∈ parabolic B N J, g * x * g⁻¹ ∈ parabolic B N K) →
      g ∈ parabolic B N K ∧ J ⊆ K) ∧
    (∀ J ⊆ S, Subgroup.normalizer (parabolic B N J : Set G) = parabolic B N J) ∧
    (∀ J ⊆ S, ∀ K ⊆ S, ∀ g : G,
      (parabolic B N J).map (MulAut.conj g).toMonoidHom = parabolic B N K → J = K) :=
  ⟨⟨h.iUnion_dc, h.pairwise_disjoint_dc, h.exists_coxeterSystem⟩,
    fun _ hJ => ⟨h.coe_parabolic hJ, h.le_parabolic hJ⟩,
    fun _ hBP => h.existsUnique_parabolic hBP,
    fun _ hJ _ hK hne heq => hne (h.parabolic_injOn hJ hK heq),
    fun _ hJ _ hK => ⟨h.closure_inf hJ hK, h.parabolic_inf hJ hK, h.parabolic_sup hJ hK⟩,
    fun _ hJ _ hK _ hg => h.mem_and_subset_of_conj_le hJ hK hg,
    fun _ hJ => h.normalizer_parabolic hJ,
    fun _ hJ _ hK _ hg => h.eq_of_conj_eq hJ hK hg⟩

end CFSG.GroupTheory.TitsSystem
