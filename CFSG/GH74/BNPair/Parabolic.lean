module

public import CFSG.GH74.BNPair.Bruhat

public section

namespace CFSG.GH74.BNPair

open scoped Pointwise

variable {X : Type*} [Group X] {B N : Subgroup X} [(cartan B N).Normal]

@[expose] def weylSubgroup (B N : Subgroup X) [(cartan B N).Normal] (P : Subgroup X) :
    Subgroup (WeylGroup B N) :=
  ((P ⊓ N).subgroupOf N).map (QuotientGroup.mk' (cartan B N))

theorem mem_weylSubgroup_iff {P : Subgroup X} {w : WeylGroup B N} :
    w ∈ weylSubgroup B N P ↔ ∃ n : N, (n : X) ∈ P ∧ (n : WeylGroup B N) = w := by
  simp only [weylSubgroup, Subgroup.mem_map, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · rintro ⟨n, ⟨hn, _⟩, rfl⟩
    exact ⟨n, hn, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, ⟨hn, n.2⟩, rfl⟩

theorem dc_subset_of_mem_weylSubgroup {P : Subgroup X} (hBP : B ≤ P) {w : WeylGroup B N}
    (hw : w ∈ weylSubgroup B N P) : dc B N w ⊆ P := by
  obtain ⟨n, hnP, rfl⟩ := mem_weylSubgroup_iff.1 hw
  exact dc_subset_of_biinv (T := (P : Set X))
    (fun _ hb _ hx _ hb' => P.mul_mem (P.mul_mem (hBP hb) hx) (hBP hb')) (coe_mem_dc n) hnP

theorem mem_weylSubgroup_of_mem_dc {P : Subgroup X} (hBP : B ≤ P) {w : WeylGroup B N} {x : X}
    (hx : x ∈ dc B N w) (hxP : x ∈ P) : w ∈ weylSubgroup B N P := by
  obtain ⟨n, hn, b, hb, b', hb', rfl⟩ := mem_dc_iff.1 hx
  refine mem_weylSubgroup_iff.2 ⟨n, ?_, hn⟩
  have : (n : X) = b⁻¹ * (b * n * b') * b'⁻¹ := by group
  rw [this]
  exact P.mul_mem (P.mul_mem (P.inv_mem (hBP hb)) hxP) (P.inv_mem (hBP hb'))

theorem BNCore.mono {J K : Set (WeylGroup B N)} (hJ : BNCore B N J) (hK : K ⊆ J) :
    BNCore B N K where
  mul_self_eq_one s hs := hJ.mul_self_eq_one s (hK hs)
  ne_one s hs := hJ.ne_one s (hK hs)
  mul_subset s hs := hJ.mul_subset s (hK hs)
  not_subset s hs := hJ.not_subset s (hK hs)

section Descent

variable {J : Set (WeylGroup B N)}

theorem BNCore.dc_subset_mul_inv (hJ : BNCore B N J) {s w : WeylGroup B N} (hs : s ∈ J)
    (hw : w ∈ Subgroup.closure J) (hdesc : wordLength J (s * w) + 1 = wordLength J w) :
    ∀ x ∈ dc B N s, ∃ a ∈ dc B N w, ∃ b ∈ dc B N w, x = a * b⁻¹ := by
  intro x hx
  have hu : s * w ∈ Subgroup.closure J := mem_closure_mul_gen hs hw
  have hsu : s * (s * w) = w := by rw [← mul_assoc, hJ.mul_self_eq_one s hs, one_mul]
  have hlt : wordLength J (s * w) < wordLength J (s * (s * w)) := by rw [hsu]; omega
  have hQ := hJ.mul_subset_of_lt hs hu hlt
  rw [hsu] at hQ
  obtain ⟨n, hn⟩ := QuotientGroup.mk_surjective (s * w)
  have hy : (n : X) ∈ dc B N (s * w) := by rw [← hn]; exact coe_mem_dc n
  obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := Set.mem_mul.1 (hJ.subset_mul_self hs (Or.inr hx))
  have hs₂' : s₂⁻¹ ∈ dc B N s := by
    simpa [hJ.inv_eq hs] using inv_mem_dc hs₂
  refine ⟨s₁ * n, hQ (Set.mem_mul.2 ⟨s₁, hs₁, n, hy, rfl⟩), s₂⁻¹ * n,
    hQ (Set.mem_mul.2 ⟨_, hs₂', n, hy, rfl⟩), by group⟩

theorem BNCore.mem_weylSubgroup_of_descent (hJ : BNCore B N J) {P : Subgroup X} (hBP : B ≤ P)
    {s w : WeylGroup B N} (hs : s ∈ J) (hw : w ∈ Subgroup.closure J)
    (hdesc : wordLength J (s * w) + 1 = wordLength J w) (hwP : w ∈ weylSubgroup B N P) :
    s ∈ weylSubgroup B N P := by
  obtain ⟨n, hn⟩ := QuotientGroup.mk_surjective s
  have hsP : ∀ x ∈ dc B N s, x ∈ P := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hJ.dc_subset_mul_inv hs hw hdesc x hx
    exact P.mul_mem (dc_subset_of_mem_weylSubgroup hBP hwP ha)
      (P.inv_mem (dc_subset_of_mem_weylSubgroup hBP hwP hb))
  exact mem_weylSubgroup_of_mem_dc hBP (coe_mem_dc n |> fun h => hn ▸ h) (hsP _ (hn ▸ coe_mem_dc n))

theorem BNCore.mem_closure_inter_weylSubgroup (hJ : BNCore B N J) {P : Subgroup X}
    (hBP : B ≤ P) :
    ∀ k : ℕ, ∀ w ∈ Subgroup.closure J, wordLength J w = k → w ∈ weylSubgroup B N P →
      w ∈ Subgroup.closure (J ∩ (weylSubgroup B N P : Set (WeylGroup B N))) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro w hw hlen hwP
    by_cases hw1 : w = 1
    · rw [hw1]
      exact Subgroup.one_mem _
    · obtain ⟨s, hs, hdesc⟩ := exists_left_descent hJ.mul_self_eq_one hw hw1
      have hsP := hJ.mem_weylSubgroup_of_descent hBP hs hw hdesc hwP
      have hsm : s ∈ Subgroup.closure (J ∩ (weylSubgroup B N P : Set (WeylGroup B N))) :=
        Subgroup.subset_closure ⟨hs, hsP⟩
      have hu : s * w ∈ weylSubgroup B N P := Subgroup.mul_mem _ hsP hwP
      have hu' := ih (wordLength J (s * w)) (by omega) (s * w)
        (mem_closure_mul_gen hs hw) rfl hu
      have : w = s * (s * w) := by rw [← mul_assoc, hJ.mul_self_eq_one s hs, one_mul]
      rw [this]
      exact Subgroup.mul_mem _ hsm hu'

end Descent

theorem eq_one_or_eq_of_mem_closure_singleton {W : Type*} [Group W] {s t : W} (hs : s * s = 1)
    (ht : t ∈ Subgroup.closure ({s} : Set W)) : t = 1 ∨ t = s := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_closure_singleton.1 ht
  rcases Int.even_or_odd' n with ⟨k, rfl | rfl⟩
  · left
    rw [zpow_mul]
    have : s ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hs
    rw [this, one_zpow]
  · right
    rw [zpow_add, zpow_mul]
    have : s ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hs
    rw [this, one_zpow, one_mul, zpow_one]

section TitsSystem

variable {S : Finset (WeylGroup B N)} {J : Set (WeylGroup B N)}

theorem IsTitsSystem.mem_closure (h : IsTitsSystem B N S) (w : WeylGroup B N) :
    w ∈ Subgroup.closure (S : Set (WeylGroup B N)) := by
  rw [h.closure_eq]
  trivial

theorem le_parabolic_one (J : Set (WeylGroup B N)) {x : X} (hx : x ∈ B) : x ∈ parabolicSet B N J :=
  mem_parabolicSet_iff.2 ⟨1, Subgroup.one_mem _, mem_dc_one.2 hx⟩

theorem BNCore.le_parabolic (hJ : BNCore B N J) : B ≤ parabolic B N J := by
  rw [hJ.parabolic_eq]
  exact fun x hx => le_parabolic_one J hx

theorem BNCore.mem_parabolic_of_mem_dc (hJ : BNCore B N J) {w : WeylGroup B N}
    (hw : w ∈ Subgroup.closure J) {x : X} (hx : x ∈ dc B N w) : x ∈ parabolic B N J :=
  hJ.mem_parabolic_iff.2 ⟨w, hw, hx⟩

theorem IsTitsSystem.mem_of_mem_closure (h : IsTitsSystem B N S)
    {K : Set (WeylGroup B N)} (hKS : K ⊆ (S : Set (WeylGroup B N))) {s : WeylGroup B N}
    (hs : s ∈ S) (hsK : s ∈ Subgroup.closure K) : s ∈ K := by
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

theorem IsTitsSystem.parabolicSubgroup_eq_top (h : IsTitsSystem B N S) :
    h.bnCore.parabolicSubgroup = ⊤ := by
  have hB : B ≤ h.bnCore.parabolicSubgroup := fun x hx => le_parabolic_one _ hx
  have hN : N ≤ h.bnCore.parabolicSubgroup := fun x hx =>
    mem_parabolicSet_iff.2 ⟨_, h.mem_closure _, coe_mem_dc (⟨x, hx⟩ : N)⟩
  rw [eq_top_iff, ← h.gen]
  exact sup_le hB hN

theorem IsTitsSystem.parabolic_univ (h : IsTitsSystem B N S) :
    parabolic B N (S : Set (WeylGroup B N)) = ⊤ := by
  rw [h.bnCore.parabolic_eq]
  exact h.parabolicSubgroup_eq_top

theorem IsTitsSystem.iUnion_dc (h : IsTitsSystem B N S) : (⋃ w, dc B N w) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  have hx : x ∈ h.bnCore.parabolicSubgroup := by
    rw [h.parabolicSubgroup_eq_top]
    trivial
  obtain ⟨w, _, hw⟩ := mem_parabolicSet_iff.1 hx
  exact ⟨w, hw⟩

theorem IsTitsSystem.dc_injective (h : IsTitsSystem B N S) : Function.Injective (dc B N) :=
  fun w _ hww' => h.bnCore.dc_inj (h.mem_closure w) hww'

theorem IsTitsSystem.pairwise_disjoint_dc (h : IsTitsSystem B N S) :
    Pairwise (Function.onFun Disjoint (dc B N)) := by
  intro w w' hne
  rw [Function.onFun, Set.disjoint_left]
  intro x hx hx'
  exact hne (h.dc_injective (dc_eq_of_mem hx hx'))

theorem IsTitsSystem.refined (h : IsTitsSystem B N S) {n m : N}
    (hn : (n : WeylGroup B N) ∈ S)
    (hlt : wordLength (S : Set (WeylGroup B N)) ((n : WeylGroup B N) * (m : WeylGroup B N)) >
      wordLength (S : Set (WeylGroup B N)) (m : WeylGroup B N)) :
    ({(n : X)} : Set X) * (B : Set X) * {(m : X)} ⊆
      dc B N ((n : WeylGroup B N) * (m : WeylGroup B N)) := by
  have h1 := h.bnCore.mul_subset_of_lt hn (h.mem_closure _) hlt
  rintro _ ⟨_, ⟨_, rfl, b, hb, rfl⟩, _, rfl, rfl⟩
  exact h1 (Set.mem_mul.2 ⟨n, coe_mem_dc n, b * m,
    mem_dc_of_mem (coe_mem_dc m) hb B.one_mem (by simp), by simp [mul_assoc]⟩)

theorem IsTitsSystem.coe_parabolic (h : IsTitsSystem B N S) {J : Finset (WeylGroup B N)}
    (hJ : J ⊆ S) :
    (parabolic B N (J : Set (WeylGroup B N)) : Set X) = parabolicSet B N (J : Set (WeylGroup B N)) :=
  (h.bnCore.mono (by exact_mod_cast hJ)).coe_parabolic

theorem IsTitsSystem.le_parabolic (h : IsTitsSystem B N S) {J : Finset (WeylGroup B N)}
    (hJ : J ⊆ S) : B ≤ parabolic B N (J : Set (WeylGroup B N)) :=
  (h.bnCore.mono (by exact_mod_cast hJ)).le_parabolic

theorem IsTitsSystem.normalizer_parabolic (h : IsTitsSystem B N S) {J : Finset (WeylGroup B N)}
    (hJ : J ⊆ S) :
    Subgroup.normalizer ((parabolic B N (J : Set (WeylGroup B N)) : Subgroup X) : Set X) =
      parabolic B N (J : Set (WeylGroup B N)) := by
  have hSJ : (J : Set (WeylGroup B N)) ⊆ (S : Set (WeylGroup B N)) := by exact_mod_cast hJ
  have hcore := h.bnCore
  have hK : BNCore B N (J : Set (WeylGroup B N)) := hcore.mono hSJ
  set P := parabolic B N (J : Set (WeylGroup B N)) with hP
  have hBP : B ≤ P := hK.le_parabolic
  refine le_antisymm ?_ Subgroup.le_normalizer
  have key : ∀ k : ℕ, ∀ n : N, wordLength (S : Set (WeylGroup B N)) (n : WeylGroup B N) = k →
      (n : X) ∈ Subgroup.normalizer (P : Set X) → (n : WeylGroup B N) ∈ Subgroup.closure
        (J : Set (WeylGroup B N)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro n hlen hn
      by_cases hw1 : (n : WeylGroup B N) = 1
      · rw [hw1]
        exact Subgroup.one_mem _
      · obtain ⟨s, hs, hdesc⟩ := exists_left_descent hcore.mul_self_eq_one
          (h.mem_closure (n : WeylGroup B N)) hw1
        obtain ⟨ns, hns⟩ := QuotientGroup.mk_surjective s
        by_cases hsJ : s ∈ (J : Set (WeylGroup B N))
        · have hnsP : (ns : X) ∈ P :=
            hK.mem_parabolic_of_mem_dc (Subgroup.subset_closure hsJ) (hns ▸ coe_mem_dc ns)
          have hn' : ((ns * n : N) : X) ∈ Subgroup.normalizer (P : Set X) := by
            rw [Subgroup.coe_mul]
            exact Subgroup.mul_mem _ (Subgroup.le_normalizer hnsP) hn
          have hmk : ((ns * n : N) : WeylGroup B N) = s * (n : WeylGroup B N) := by
            rw [QuotientGroup.mk_mul, hns]
          have := ih (wordLength (S : Set (WeylGroup B N)) (s * (n : WeylGroup B N))) (by omega)
            (ns * n) (by rw [hmk]) hn'
          rw [hmk] at this
          have e : (n : WeylGroup B N) = s * (s * (n : WeylGroup B N)) := by
            rw [← mul_assoc, hcore.mul_self_eq_one s hs, one_mul]
          rw [e]
          exact Subgroup.mul_mem _ (Subgroup.subset_closure hsJ) this
        · exfalso
          have hdc : ∀ x ∈ dc B N s, x ∈ P := by
            intro x hx
            obtain ⟨a, ha, b, hb, rfl⟩ := hcore.dc_subset_mul_inv hs
              (h.mem_closure (n : WeylGroup B N)) hdesc x hx
            obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := (mem_dc_of_lift rfl).1 ha
            obtain ⟨b₃, hb₃, b₄, hb₄, rfl⟩ := (mem_dc_of_lift rfl).1 hb
            have hc : (n : X) * (b₂ * b₄⁻¹) * (n : X)⁻¹ ∈ P :=
              (Subgroup.mem_normalizer_iff.1 hn _).1 (P.mul_mem (hBP hb₂) (P.inv_mem (hBP hb₄)))
            have e : b₁ * (n : X) * b₂ * (b₃ * (n : X) * b₄)⁻¹ =
                b₁ * ((n : X) * (b₂ * b₄⁻¹) * (n : X)⁻¹) * b₃⁻¹ := by group
            rw [e]
            exact P.mul_mem (P.mul_mem (hBP hb₁) hc) (P.inv_mem (hBP hb₃))
          have hnsP : (ns : X) ∈ P := hdc _ (hns ▸ coe_mem_dc ns)
          obtain ⟨w', hw', hnsw'⟩ := hK.mem_parabolic_iff.1 hnsP
          have hs' : s ∈ Subgroup.closure (J : Set (WeylGroup B N)) := by
            have := hK.dc_inj hw' (dc_eq_of_mem hnsw' (hns ▸ coe_mem_dc ns))
            rw [← this]
            exact hw'
          exact hsJ (h.mem_of_mem_closure hSJ hs hs')
  intro x hx
  obtain ⟨w, hw⟩ := Set.mem_iUnion.1 (h.iUnion_dc ▸ Set.mem_univ x)
  obtain ⟨n, hn⟩ := QuotientGroup.mk_surjective w
  obtain ⟨b, hb, b', hb', hxb⟩ := (mem_dc_of_lift hn).1 hw
  have hnN : (n : X) ∈ Subgroup.normalizer (P : Set X) := by
    have e : (n : X) = b⁻¹ * x * b'⁻¹ := by rw [hxb]; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer (hBP hb)))
      hx) (Subgroup.inv_mem _ (Subgroup.le_normalizer (hBP hb')))
  have hwJ := key _ n rfl hnN
  rw [hn] at hwJ
  exact hK.mem_parabolic_of_mem_dc hwJ hw

theorem IsTitsSystem.parabolic_le_iff (h : IsTitsSystem B N S) {J K : Finset (WeylGroup B N)}
    (hJ : J ⊆ S) (hK : K ⊆ S) :
    parabolic B N (J : Set (WeylGroup B N)) ≤ parabolic B N (K : Set (WeylGroup B N)) ↔ J ⊆ K := by
  have hJS : (J : Set (WeylGroup B N)) ⊆ (S : Set (WeylGroup B N)) := by exact_mod_cast hJ
  have hKS : (K : Set (WeylGroup B N)) ⊆ (S : Set (WeylGroup B N)) := by exact_mod_cast hK
  have hJcore : BNCore B N (J : Set (WeylGroup B N)) := h.bnCore.mono hJS
  have hKcore : BNCore B N (K : Set (WeylGroup B N)) := h.bnCore.mono hKS
  constructor
  · intro hle s hs
    have hsS : s ∈ S := hJ hs
    obtain ⟨n, hn⟩ := QuotientGroup.mk_surjective s
    have hnJ : (n : X) ∈ parabolic B N (J : Set (WeylGroup B N)) :=
      hJcore.mem_parabolic_of_mem_dc (Subgroup.subset_closure (Finset.mem_coe.2 hs))
        (hn ▸ coe_mem_dc n)
    obtain ⟨w', hw', hnw'⟩ := hKcore.mem_parabolic_iff.1 (hle hnJ)
    have hw's : w' = s := hKcore.dc_inj hw' (dc_eq_of_mem hnw' (hn ▸ coe_mem_dc n))
    have hsK : s ∈ Subgroup.closure (K : Set (WeylGroup B N)) := hw's ▸ hw'
    exact Finset.mem_coe.1 (h.mem_of_mem_closure hKS hsS hsK)
  · intro hJK
    refine Subgroup.closure_mono ?_
    intro x hx
    obtain ⟨w, hw, hxw⟩ := mem_parabolicSet_iff.1 hx
    exact mem_parabolicSet_iff.2 ⟨w, Subgroup.closure_mono (by exact_mod_cast hJK) hw, hxw⟩

theorem IsTitsSystem.exists_parabolic (h : IsTitsSystem B N S) {P : Subgroup X} (hBP : B ≤ P) :
    ∃ J : Finset (WeylGroup B N), J ⊆ S ∧ P = parabolic B N (J : Set (WeylGroup B N)) := by
  classical
  set T := weylSubgroup B N P with hT
  refine ⟨S.filter (· ∈ T), Finset.filter_subset _ _, ?_⟩
  have hclosure : Subgroup.closure ((S.filter (· ∈ T) : Finset (WeylGroup B N)) :
      Set (WeylGroup B N)) = T := by
    apply le_antisymm
    · exact (Subgroup.closure_le _).2 fun x hx => (Finset.mem_filter.1 (Finset.mem_coe.1 hx)).2
    · intro w hw
      have h1 := h.bnCore.mem_closure_inter_weylSubgroup hBP _ w (h.mem_closure w) rfl hw
      refine Subgroup.closure_mono ?_ h1
      intro t ht
      exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨ht.1, ht.2⟩)
  have hset : (P : Set X) = parabolicSet B N ((S.filter (· ∈ T) : Finset (WeylGroup B N)) :
      Set (WeylGroup B N)) := by
    ext x
    constructor
    · intro hx
      obtain ⟨w, hw⟩ := Set.mem_iUnion.1 (h.iUnion_dc ▸ Set.mem_univ x)
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

theorem parabolicSet_empty : parabolicSet B N (∅ : Set (WeylGroup B N)) = (B : Set X) := by
  ext x
  rw [mem_parabolicSet_iff]
  simp only [Subgroup.closure_empty, Subgroup.mem_bot]
  constructor
  · rintro ⟨w, rfl, hx⟩
    exact mem_dc_one.1 hx
  · intro hx
    exact ⟨1, rfl, mem_dc_one.2 hx⟩

theorem parabolic_empty : parabolic B N (∅ : Set (WeylGroup B N)) = B := by
  unfold parabolic
  rw [parabolicSet_empty]
  exact Subgroup.closure_eq B

end TitsSystem

end CFSG.GH74.BNPair
