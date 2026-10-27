module

public import CFSG.GroupTheory.Frattini.PSubgroupLift
public import CFSG.GroupTheory.CardMapInfKer
public import CFSG.GroupTheory.PerfectLeOfPGroupQuotient
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs

public section

open scoped Pointwise

namespace CFSG.GroupTheory

variable {X M : Type*} [Group X] [Group M]

private theorem smul_fixedPoints_subset_of_mem_normalizer [MulDistribMulAction X M]
    {S : Subgroup X} {k : X} (hk : k ∈ Subgroup.normalizer (S : Set X)) :
    k • (FixedPoints.subgroup S M : Set M) ⊆ (FixedPoints.subgroup S M : Set M) := by
  intro v hv
  rw [Set.mem_smul_set] at hv
  obtain ⟨w, hw, rfl⟩ := hv
  change w ∈ FixedPoints.subgroup (↥S) M at hw
  change k • w ∈ FixedPoints.subgroup (↥S) M
  rw [FixedPoints.mem_subgroup] at hw ⊢
  intro s
  have hks : k⁻¹ * (s : X) * k ∈ S := by
    simpa using
      (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (S : Set X)).inv_mem hk) (s : X)).mp
        s.2
  calc s • (k • w) = ((s : X) * k) • w := (mul_smul (s : X) k w).symm
    _ = (k * (k⁻¹ * (s : X) * k)) • w := by
        rw [show (s : X) * k = k * (k⁻¹ * (s : X) * k) from by group]
    _ = k • ((k⁻¹ * (s : X) * k) • w) := mul_smul k _ w
    _ = k • w := by
        rw [show ((k⁻¹ * (s : X) * k) • w) = w from hw ⟨k⁻¹ * (s : X) * k, hks⟩]

theorem le_stabilizer_fixedPointSubgroup_of_le_normalizer [MulDistribMulAction X M]
    {S K : Subgroup X} (hK : K ≤ Subgroup.normalizer (S : Set X)) :
    K ≤ MulAction.stabilizer X ((FixedPoints.subgroup S M : Subgroup M) : Set M) := by
  intro k hk
  rw [MulAction.mem_stabilizer_iff]
  have hsub := smul_fixedPoints_subset_of_mem_normalizer (M := M) (S := S) (k := k) (hK hk)
  have hinv := smul_fixedPoints_subset_of_mem_normalizer (M := M) (S := S) (k := k⁻¹)
    ((Subgroup.normalizer (S : Set X)).inv_mem (hK hk))
  refine Set.eq_of_subset_of_subset hsub ?_
  calc (FixedPoints.subgroup S M : Set M)
      = k • (k⁻¹ • (FixedPoints.subgroup S M : Set M)) := by rw [smul_inv_smul]
    _ ⊆ k • (FixedPoints.subgroup S M : Set M) := Set.smul_set_mono hinv

theorem isSylowOf_comap_of_map_eq_of_coprime_ker {L H : Type*} [Group L] [Finite L]
    [Group H] [Finite H] {p : ℕ} [Fact p.Prime] (f : L →* H)
    (hf : Function.Surjective f) (hker : ¬ p ∣ Nat.card f.ker)
    {A : Subgroup L} {Astar : Subgroup H} (hAle : A ≤ Astar.comap f)
    (hmap : A.map f = Astar)
    (hdisj : A ⊓ f.ker = ⊥) (hAp : IsPGroup p A) :
    CFSG.ABGLocalTools.IsSylowOf p A (Astar.comap f) := by
  let N : Subgroup L := Astar.comap f
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨hAle, hAp, ?_⟩
  have hcardA : Nat.card A = Nat.card Astar := by
    rw [← hmap, card_map_eq_card_of_inf_ker_eq_bot (f := f) (J := A) hdisj]
  have hcardN := card_comap_eq_card_ker_mul_card f hf Astar
  have hmul := Subgroup.relIndex_mul_card (H := A) (K := N)
  rw [inf_of_le_left hAle] at hmul
  have hmul' : A.relIndex N * Nat.card A = Nat.card f.ker * Nat.card A := by
    rw [hmul, hcardN, hcardA]
  have hrel : A.relIndex N = Nat.card f.ker :=
    Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := A)) hmul'
  rw [hrel]
  exact hker

theorem le_of_commutator_eq_self_of_le_sup_of_isPGroup {X : Type*} [Group X] [Finite X]
    {K N P : Subgroup X} [N.Normal] (hP : IsPGroup 2 P) (hK : ⁅K, K⁆ = K)
    (hKN : K ≤ N ⊔ P) : K ≤ N := by
  haveI : ((K ⊓ N).subgroupOf K).Normal := by
    rw [Subgroup.inf_subgroupOf_left]
    exact Subgroup.normal_subgroupOf
  let D : Subgroup ↥K := (K ⊓ N).subgroupOf K
  let f : ↥K →* X ⧸ N := (QuotientGroup.mk' N).comp K.subtype
  have hker : f.ker = D := by
    dsimp only [f, D]
    rw [← MonoidHom.comap_ker (QuotientGroup.mk' N) K.subtype, QuotientGroup.ker_mk']
    ext x
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  have hrange_le : f.range ≤ (N ⊔ P).map (QuotientGroup.mk' N) := by
    rintro _ ⟨k, rfl⟩
    exact Subgroup.mem_map.mpr ⟨(k : X), hKN k.2, rfl⟩
  have hPquot : IsPGroup 2 ((N ⊔ P).map (QuotientGroup.mk' N)) := by
    rw [Subgroup.map_sup]
    have hbot : N.map (QuotientGroup.mk' N) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rw [hbot, bot_sup_eq]
    exact hP.map (QuotientGroup.mk' N)
  have hrangeP : IsPGroup 2 f.range := hPquot.to_le hrange_le
  have hpquot : IsPGroup 2 (↥K ⧸ D) := by
    let e : (↥K ⧸ D) ≃* ↥f.range :=
      (QuotientGroup.quotientMulEquivOfEq hker).symm.trans
        (QuotientGroup.quotientKerEquivRange f)
    exact hrangeP.of_equiv e.symm
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hpquot
  have hidx : D.relIndex ⊤ = 2 ^ m := by
    rw [Subgroup.relIndex_top_right, Subgroup.index_eq_card]
    exact hm
  have htop : ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = ⊤ := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_top]
    rw [Subgroup.range_subtype]
    exact hK
  have hDnorm : (⊤ : Subgroup ↥K) ≤ Subgroup.normalizer (D : Set ↥K) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr this]
  have htopD := Subgroup.le_of_commutator_eq_self_of_relIndex_eq_prime_pow
    (G := ↥K) (D := D) (C := ⊤) (H := ⊤) (p := 2) (k := m)
    Nat.prime_two le_top hDnorm hidx le_top htop
  intro x hx
  exact (Subgroup.mem_subgroupOf.mp (htopD (Subgroup.mem_top ⟨x, hx⟩))).2

theorem mem_normalizer_of_conj_eq_inv {G : Type*} [Group G] {E : Subgroup G} {w : G}
    (h : ∀ e ∈ E, w * e * w⁻¹ = e⁻¹) : w ∈ Subgroup.normalizer (E : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [h x hx]
    exact E.inv_mem hx
  · intro hx
    have hw : ∀ e ∈ E, w⁻¹ * e * (w⁻¹)⁻¹ = e⁻¹ := by
      intro e he
      have h' := h (e⁻¹) (E.inv_mem he)
      have hc := congrArg (fun z => w⁻¹ * z * w) h'
      simpa [mul_assoc] using hc.symm
    have hxin : w⁻¹ * (w * x * w⁻¹) * (w⁻¹)⁻¹ = (w * x * w⁻¹)⁻¹ := hw _ hx
    have hxin' : w⁻¹ * (w * x * w⁻¹) * w = (w * x * w⁻¹)⁻¹ := by
      simpa only [inv_inv] using hxin
    have hxeq : x = (w * x * w⁻¹)⁻¹ := by
      calc x = w⁻¹ * (w * x * w⁻¹) * w := by group
        _ = (w * x * w⁻¹)⁻¹ := hxin'
    rw [hxeq]
    exact E.inv_mem hx

theorem fixV_eq_top_iff_le_ker {G V : Type} [Group G] [Finite G] {p : ℕ}
    [AddCommGroup V] [Module (ZMod p) V] (ρ : Representation (ZMod p) G V)
    (X : Subgroup G) :
    CFSG.LocalAnalysis.UniquenessCase.UCK.fixV ρ X = ⊤ ↔ X ≤ ρ.ker := by
  constructor
  · intro h x hx
    rw [MonoidHom.mem_ker]
    ext v
    have hv : v ∈ CFSG.LocalAnalysis.UniquenessCase.UCK.fixV ρ X := by
      rw [h]
      exact Submodule.mem_top
    exact hv x hx
  · intro h
    rw [eq_top_iff]
    intro v _
    intro a ha
    have ha1 : ρ a = 1 := by
      rw [← MonoidHom.mem_ker]
      exact h ha
    rw [ha1]
    simp

end CFSG.GroupTheory
