module

public import CFSG.Goldschmidt75.TheoremBcBasic
public import CFSG.Goldschmidt75.Quotient

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup
open scoped commutatorElement

universe u

variable {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem inf_centralizer_ne_bot {S S₀ : Subgroup G} (hSp : IsPGroup p S) (hS₀S : S₀ ≤ S)
    (hn : S ≤ normalizer (S₀ : Set G)) (hS₀1 : S₀ ≠ ⊥) :
    S₀ ⊓ centralizer (S : Set G) ≠ ⊥ := by
  have : Group.IsNilpotent S := hSp.isNilpotent
  have hN : (S₀.subgroupOf S).Normal := by
    refine ⟨fun x hx g => ?_⟩
    have := (mem_normalizer_iff.mp (hn g.2) x).mp hx
    simpa [mem_subgroupOf] using this
  have hne : S₀.subgroupOf S ≠ ⊥ := by
    intro h
    apply hS₀1
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hS₀S hx⟩ : S) ∈ S₀.subgroupOf S := hx
    rw [h, mem_bot] at this
    simpa using congrArg Subtype.val this
  obtain ⟨z, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  intro hbot
  apply hz1
  have hzS₀ : ((z : S) : G) ∈ S₀ := (mem_inf.1 z.2).1
  have hzc : ((z : S) : G) ∈ centralizer (S : Set G) := by
    rw [mem_centralizer_iff]
    intro y hy
    have := mem_center_iff.mp (mem_inf.1 z.2).2 ⟨y, hy⟩
    exact congrArg Subtype.val this
  have : ((z : S) : G) ∈ S₀ ⊓ centralizer (S : Set G) := ⟨hzS₀, hzc⟩
  rw [hbot, mem_bot] at this
  exact Subtype.ext (Subtype.ext this)

theorem map_centralizer_le_centralizer {K : Type*} [Group K] {Q : Type*} [Group Q] (ψ : K →* Q)
    (S C : Subgroup K) (hC : C ≤ centralizer (S : Set K)) :
    C.map ψ ≤ centralizer ((S.map ψ : Subgroup Q) : Set Q) := by
  rintro _ ⟨c, hc, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨s, hs, rfl⟩
  rw [← map_mul, ← map_mul, mem_centralizer_iff.mp (hC hc) s hs]

theorem commutator_le_centralizer_of_le {K : Type*} [Group K] {S H Z : Subgroup K}
    (hSH : ⁅S, H⁆ ≤ Z) (hZ : Z ≤ centralizer (H : Set K)) :
    ⁅H, H⁆ ≤ centralizer (S : Set K) := by
  have h1 : ⁅⁅S, H⁆, H⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (hSH.trans hZ)
  have h2 : ⁅⁅H, S⁆, H⁆ = ⊥ := by rw [commutator_comm H S]; exact h1
  have h3 : ⁅⁅H, H⁆, S⁆ = ⊥ := commutator_commutator_eq_bot_of_rotate h2 h1
  exact commutator_eq_bot_iff_le_centralizer.mp h3

theorem rcSet_stronglyClosed_K₁ (P : Sylow p G) {S S₀ : Subgroup G} (hSP : S ≤ P)
    (hS : fusionStronglyClosed (S : Set G) P) (hS₀S : S₀ ≤ S) [S₀.Normal] (hS₀1 : S₀ ≠ ⊥)
    (IH : ∀ (H : Type u) [Group H] [Finite H], Nat.card H < Nat.card G → RcFor p H) :
    ∀ x ∈ rcSet S P, ∀ k ∈ S ⊔ centralizer (S₀ : Set G), k⁻¹ * x * k ∈ P →
      k⁻¹ * x * k ∈ rcSet S P := by
  intro x hx k hk hxk
  set K := centralizer (S₀ : Set G)
  set K₁ := S ⊔ K
  set Z₀ := S₀ ⊓ centralizer (S : Set G)
  have hZ₀1 : Z₀ ≠ ⊥ := inf_centralizer_ne_bot (P.isPGroup'.to_le hSP) hS₀S
    (fun s _ => by rw [normalizer_eq_top_iff.mpr inferInstance]; exact mem_top s) hS₀1
  have hZ₀K : Z₀ ≤ centralizer (K₁ : Set G) := by
    have hle : K₁ ≤ centralizer (Z₀ : Set G) := by
      refine sup_le (fun s hs => ?_) (fun c hc => ?_)
      · rw [mem_centralizer_iff]; intro z hz
        exact (mem_centralizer_iff.mp hz.2 s hs).symm
      · rw [mem_centralizer_iff]; intro z hz
        exact mem_centralizer_iff.mp hc z hz.1
    intro z hz
    rw [mem_centralizer_iff]
    intro y hy
    exact (mem_centralizer_iff.mp (hle hy) z hz).symm
  have hZ₀K₁ : Z₀ ≤ K₁ := inf_le_left.trans (hS₀S.trans le_sup_left)
  set Z' := Z₀.subgroupOf K₁
  have hZ'c : Z' ≤ center K₁ := by
    intro z hz
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (mem_centralizer_iff.mp (hZ₀K hz) y y.2)
  have : Z'.Normal := normal_of_le_center hZ'c
  obtain ⟨T₁, hT₁⟩ :=
    ((P.isPGroup'.to_inf_left (K := K₁)).comap_subtype (K := K₁)).exists_le_sylow
  have hST : S.subgroupOf K₁ ≤ T₁ := fun y hy => hT₁ (show (y : G) ∈ (P : Subgroup G) ⊓ K₁
    from ⟨hSP hy, y.2⟩)
  have hSc := stronglyClosed_subgroupOf P hS (le_sup_left : S ≤ K₁) T₁ hST
  set ψ := QuotientGroup.mk' Z'
  have hcard : Nat.card (K₁ ⧸ Z') < Nat.card G := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup Z'
    have h2 : 1 < Nat.card Z' := by
      rw [Subgroup.one_lt_card_iff_ne_bot]
      intro h
      apply hZ₀1
      rw [eq_bot_iff]
      intro z hz
      have : (⟨z, hZ₀K₁ hz⟩ : K₁) ∈ Z' := hz
      rw [h, mem_bot] at this
      simpa using congrArg Subtype.val this
    have h3 : 0 < Nat.card (K₁ ⧸ Z') := Nat.card_pos
    have h4 : Nat.card K₁ ≤ Nat.card G := Subgroup.card_le_card_group K₁
    nlinarith
  have hSbar := stronglyClosed_map Z' T₁ hST hSc
  have hSbarT : (S.subgroupOf K₁).map ψ ≤ (sylowMap Z' T₁ : Subgroup (K₁ ⧸ Z')) := by
    rw [coe_sylowMap]; exact map_mono hST
  have hR := IH (K₁ ⧸ Z') hcard (sylowMap Z' T₁) _ hSbarT hSbar
  have hCK : centralizer (S : Set G) ≤ K := Subgroup.centralizer_le hS₀S
  have hCK₁ : centralizer (S : Set G) ≤ K₁ := hCK.trans le_sup_right
  have hxK₁ : x ∈ K₁ := hCK₁ (rcSet_le_centralizer S P hx)
  set x' : K₁ := ⟨x, hxK₁⟩
  set k' : K₁ := ⟨k, hk⟩
  set Sb := (S.subgroupOf K₁).map ψ
  have h1 : ψ x' ∈ rcSet Sb (sylowMap Z' T₁) := by
    refine ⟨?_, ?_⟩
    · have hx1 := mem_commutator_subgroupOf hCK₁ hx.1 hxK₁
      have hle : ((centralizer (S : Set G)).subgroupOf K₁).map ψ ≤
          centralizer (Sb : Set (K₁ ⧸ Z')) :=
        map_centralizer_le_centralizer ψ _ _ (subgroupOf_centralizer_le le_sup_left)
      have := Subgroup.mem_map_of_mem ψ hx1
      rw [Subgroup.map_commutator] at this
      exact Subgroup.commutator_mono hle hle this
    · rw [coe_sylowMap]
      exact Subgroup.mem_map_of_mem ψ (hT₁ (show (x' : G) ∈ (P : Subgroup G) ⊓ K₁ from
        ⟨rcSet_le S P hx, hxK₁⟩))
  have h2 : (ψ k')⁻¹ * ψ x' * ψ k' ∈ (sylowMap Z' T₁ : Subgroup (K₁ ⧸ Z')) := by
    rw [coe_sylowMap, ← map_inv, ← map_mul, ← map_mul]
    refine Subgroup.mem_map_of_mem ψ (hT₁ ?_)
    show ((k'⁻¹ * x' * k' : K₁) : G) ∈ (P : Subgroup G) ⊓ K₁
    exact ⟨by simpa [x', k'] using hxk, (k'⁻¹ * x' * k').2⟩
  have h3 := hR _ h1 (ψ k') h2
  set H' := (centralizer (Sb : Set (K₁ ⧸ Z'))).comap ψ
  have hSH : ⁅S.subgroupOf K₁, H'⁆ ≤ Z' := by
    rw [commutator_le]
    intro s hs h hh
    have h5 : ψ ⁅s, h⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mem_centralizer_iff.mp hh (ψ s) ⟨s, hs, rfl⟩
    rwa [← QuotientGroup.ker_mk' Z', MonoidHom.mem_ker]
  have hZH : Z' ≤ centralizer (H' : Set K₁) := fun z hz =>
    mem_centralizer_iff.mpr fun y _ => mem_center_iff.mp (hZ'c hz) y
  have hZC : Z' ≤ centralizer ((S.subgroupOf K₁ : Subgroup K₁) : Set K₁) := fun z hz =>
    mem_centralizer_iff.mpr fun y _ => mem_center_iff.mp (hZ'c hz) y
  have hH'C := commutator_le_centralizer_of_le hSH hZH
  have hmem : k'⁻¹ * x' * k' ∈ ⁅H', H'⁆ ⊔ Z' := by
    have h4 : ψ (k'⁻¹ * x' * k') ∈ ⁅H', H'⁆.map ψ := by
      rw [Subgroup.map_commutator,
        map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
      simpa [map_mul, map_inv] using h3.1
    have := Subgroup.mem_comap.mpr h4
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at this
  have hC' : k'⁻¹ * x' * k' ∈ centralizer ((S.subgroupOf K₁ : Subgroup K₁) : Set K₁) :=
    (sup_le hH'C hZC) hmem
  have hCG : k⁻¹ * x * k ∈ centralizer (S : Set G) := by
    have := (mem_centralizer_subgroupOf_iff le_sup_left).1 hC'
    rwa [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at this
  obtain ⟨m, hm, hmeq⟩ := exists_normalizer_conj_of_le T₁ le_sup_left hST hSc hxK₁ hk
    (rcSet_le_centralizer S P hx) hCG
  rw [← hmeq]
  exact conj_mem_rcSet hm.2 hx (by rw [hmeq]; exact hxk)

end CFSG.Goldschmidt75
