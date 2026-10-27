module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallKCInGen

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers

@[expose] def KGenTwoModAbFix (p : ℕ) (K : Type) [Group K] : Prop :=
  ∀ E : Subgroup (MulAut K), IsElemAbelian p E → Nat.card E = p ^ 2 →
    (∀ k l : K, MulAut.conj k ∈ E → MulAut.conj l ∈ E → k * l = l * k) →
    (∀ e ∈ E, ∀ k : K, k ^ p = 1 → MulAut.conj k ∈ E → e k = k) →
    Subgroup.closure {k : K | ∃ e ∈ E, e ≠ 1 ∧ e k * k⁻¹ ∈ Subgroup.center K} = ⊤

theorem kGenTwoModAbFix_of_kGenTwoModAb {p : ℕ} {K : Type} [Group K] (h : KGenTwoModAb p K) :
    KGenTwoModAbFix p K :=
  fun E hE hEcard hcomm _ => h E hE hEcard hcomm

namespace ReducedNongeneration

variable {p : ℕ} {X : Type} [Group X] [Finite X] {R : Sylow p X} {X₀ : Subgroup X}

omit [Finite X] in
theorem inv_mul_mem_centralizer_of_conjNormal_eq_conj {K : Subgroup X} [K.Normal] {x : X}
    {m : K} (hxm : MulAut.conjNormal (H := K) x = MulAut.conj m) :
    (m : X)⁻¹ * x ∈ Subgroup.centralizer (K : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h1 : x * y * x⁻¹ = (m : X) * y * (m : X)⁻¹ := by
    have h2 := congrArg (fun φ : MulAut K => ((φ ⟨y, hy⟩ : K) : X)) hxm
    simpa [MulAut.conjNormal_apply, MulAut.conj_apply, Subgroup.coe_inv] using h2
  calc y * ((m : X)⁻¹ * x) = (m : X)⁻¹ * ((m : X) * y * (m : X)⁻¹) * x := by group
    _ = (m : X)⁻¹ * (x * y * x⁻¹) * x := by rw [h1]
    _ = (m : X)⁻¹ * x * y := by group

theorem mem_center_of_mem_centralizer_of_pow_eq_one (h : ReducedNongeneration p X R X₀)
    {z : X} (hz : z ∈ Subgroup.center X) (hzp : orderOf z = p) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hKn : K.Normal) (hzK : z ∈ K)
    (hZK : Nat.card (Subgroup.center K) = p) {c : X}
    (hc : c ∈ Subgroup.centralizer (K : Set X)) (hcp : c ^ p = 1) :
    c ∈ Subgroup.center X := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  rcases eq_or_ne c 1 with rfl | hc1
  · exact Subgroup.one_mem _
  have hcK : c ∈ K := mem_of_mem_centralizer_of_orderOf_eq R hKn (fun c hc hcp =>
    Subgroup.zpowers_le.mpr hzK (h.mem_zpowers_of_mem_inf_centralizer hz hzp hK hKn hzK c hc hcp))
    hc (orderOf_eq_prime hcp hc1)
  have hcZ : (⟨c, hcK⟩ : K) ∈ Subgroup.center K :=
    Subgroup.mem_center_iff.mpr fun k => Subtype.ext (Subgroup.mem_centralizer_iff.mp hc k k.2)
  exact Subgroup.zpowers_le.mpr hz (mem_zpowers_of_mem_center_of_card hz hzp hzK hZK _ hcZ)

theorem conjNormal_apply_eq_self_of_conjNormal_eq_conj (h : ReducedNongeneration p X R X₀)
    {z : X} (hz : z ∈ Subgroup.center X) (hzp : orderOf z = p) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hKn : K.Normal) (hzK : z ∈ K)
    (hZK : Nat.card (Subgroup.center K) = p) {A : Subgroup X} (hA : IsElemAbelian p A)
    {a a' : X} (haA : a ∈ A) (ha'A : a' ∈ A) {k : K} (hkp : k ^ p = 1)
    (hak : MulAut.conjNormal (H := K) a = MulAut.conj k) :
    MulAut.conjNormal (H := K) a' k = k := by
  have hc := inv_mul_mem_centralizer_of_conjNormal_eq_conj hak
  have hka : Commute (k : X) a := by
    have h1 := Subgroup.mem_centralizer_iff.mp hc k k.2
    calc (k : X) * a = k * (k * ((k : X)⁻¹ * a)) := by group
      _ = k * ((k : X)⁻¹ * a * k) := by rw [h1]
      _ = a * k := by group
  have hkX : (k : X) ^ p = 1 := by rw [← Subgroup.coe_pow, hkp, Subgroup.coe_one]
  have hcp : ((k : X)⁻¹ * a) ^ p = 1 := by
    rw [hka.inv_left.mul_pow, inv_pow, hkX, hA.2 a haA, inv_one, one_mul]
  have hca := Subgroup.mem_center_iff.mp
    (h.mem_center_of_mem_centralizer_of_pow_eq_one hz hzp hK hKn hzK hZK hc hcp) a'
  have haa : a' * a = a * a' := congrArg Subtype.val (hA.1.is_comm.comm ⟨a', ha'A⟩ ⟨a, haA⟩)
  have h1 : a' * (k : X)⁻¹ * a = (k : X)⁻¹ * a' * a := by
    calc a' * (k : X)⁻¹ * a = a' * ((k : X)⁻¹ * a) := by group
      _ = (k : X)⁻¹ * a * a' := hca
      _ = (k : X)⁻¹ * a' * a := by rw [mul_assoc, ← haa, ← mul_assoc]
  have h2 : a' * (k : X)⁻¹ = (k : X)⁻¹ * a' := mul_right_cancel h1
  apply Subtype.ext
  rw [MulAut.conjNormal_apply]
  calc a' * (k : X) * a'⁻¹ = (k : X) * ((k : X)⁻¹ * a') * (k : X) * a'⁻¹ := by group
    _ = (k : X) * (a' * (k : X)⁻¹) * (k : X) * a'⁻¹ := by rw [h2]
    _ = (k : X) := by group

theorem le_of_kGenTwoModAbFix (h : ReducedNongeneration p X R X₀) {z : X}
    (hz : z ∈ Subgroup.center X) (hzp : orderOf z = p) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hKn : K.Normal) (hzK : z ∈ K)
    (hZK : Nat.card (Subgroup.center K) = p) (hgen : KGenTwoModAbFix p K) : K ≤ X₀ := by
  have hp := h.prime
  obtain ⟨A, hAR, hA, hAcard⟩ := pRank_attained p hp (R : Subgroup X)
  have hA3 : 3 ≤ Open.pRank p A :=
    h.three_le_pRank.trans (le_csSup (pRank_bddAbove p hp A) ⟨A, le_rfl, hA, hAcard⟩)
  have hineq := pRank_le_pRank_inf_centralizer_add_pRank_map_conjNormal hp K A
  have hAC : Open.pRank p (A ⊓ Subgroup.centralizer (K : Set X)) ≤ 1 :=
    (PreuniquenessRankFour.Helpers.pRank_mono p hp (inf_le_inf_right _ hAR)).trans
      (h.pRank_inf_centralizer_le_one hz hzp hK hKn hzK)
  have h2 : 2 ≤ Open.pRank p (A.map (MulAut.conjNormal (H := K))) := by omega
  obtain ⟨E, hEA, hE, hEcard⟩ := exists_isElemAbelian_card_sq_of_two_le_pRank hp h2
  have hcomm : ∀ k l : K, MulAut.conj k ∈ E → MulAut.conj l ∈ E → k * l = l * k := by
    intro k l hk hl
    obtain ⟨a, haA, hak⟩ := hEA hk
    obtain ⟨b, hbA, hbl⟩ := hEA hl
    exact h.commute_of_conjNormal_eq_conj hz hzp hK hKn hzK
      (congrArg Subtype.val (hA.1.is_comm.comm ⟨a, haA⟩ ⟨b, hbA⟩)) hak hbl
  have hfix : ∀ e ∈ E, ∀ k : K, k ^ p = 1 → MulAut.conj k ∈ E → e k = k := by
    intro e he k hkp hk
    obtain ⟨a', ha'A, rfl⟩ := hEA he
    obtain ⟨a, haA, hak⟩ := hEA hk
    exact h.conjNormal_apply_eq_self_of_conjNormal_eq_conj hz hzp hK hKn hzK hZK hA haA ha'A hkp
      hak
  have hZ := mem_zpowers_of_mem_center_of_card hz hzp hzK hZK
  intro x hx
  have hxmem : (⟨x, hx⟩ : K) ∈ Subgroup.closure
      {k : K | ∃ e ∈ E, e ≠ 1 ∧ e k * k⁻¹ ∈ Subgroup.center K} :=
    hgen E hE hEcard hcomm hfix ▸ Subgroup.mem_top _
  refine (Subgroup.closure_le (X₀.comap K.subtype)).mpr ?_ hxmem
  rintro k ⟨e, heE, he1, hk⟩
  obtain ⟨f, hfA, rfl⟩ := hEA heE
  exact h.mem_of_conjNormal_mul_inv_mem hz hzp hZ hAR hA hA3 hfA he1 hk

end ReducedNongeneration

@[expose] def KFactCoverThreeFix : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Open.IsQuasisimple K →
    IsCatalogGroup (K ⧸ Subgroup.center K) →
    Subgroup.center K ≠ ⊥ → IsPGroup 3 (Subgroup.center K) → IsCyclic (Subgroup.center K) →
    Open.pRank 3 (⊤ : Subgroup K) ≤ 3 → ∀ T : Sylow 3 K,
      (KGenTwoModAbFix 3 K ∧ Nat.card (Subgroup.center K) = 3 ∧ KOutNormalSylow 3 K) ∨
        (GLBWeakCore 3 (T : Subgroup K) = ⊤ ∧ 3 ≤ Open.pRank 3 (⊤ : Subgroup K))

end CFSG.AGLEmbedding
