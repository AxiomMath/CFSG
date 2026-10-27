module

public import CFSG.CGT.Timmesfeld75.Sec4CaseIGDich
public import CFSG.LargeExtraspecial.S111SHCor3

public section

namespace CFSG.CGT.T75F

open CFSG CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.LargeExtraspecial Subgroup

variable {G : Type} [Group G] [Finite G]

theorem mem_wcl_of_involution (hG : Goldschmidt1974) [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (S : Sylow 2 G) {τ : G} (hτ1 : τ ≠ 1) (hτ2 : τ * τ = 1)
    (hτS : τ ∈ (S : Subgroup G)) (hτc : ∀ x ∈ (S : Subgroup G), x * τ = τ * x)
    (hab : IsMulCommutative (S11.wcl τ)) {u : G} (hu : u ∈ (S : Subgroup G)) (hu2 : u * u = 1) :
    u ∈ S11.wcl τ := by
  obtain ⟨hWS, hcl⟩ := S11.wcl_stronglyClosed S hτS hτc hab
  obtain ⟨ha, hb, -⟩ := hG G S (S11.wcl τ) hWS hab hcl
  set A : Subgroup G := S11.wcl τ with hA
  set M : Subgroup G := Subgroup.normalClosure (A : Set G) with hM
  have hMn : M.Normal := Subgroup.normalClosure_normal
  have hτM : τ ∈ M := Subgroup.subset_normalClosure (S11.self_mem_wcl τ)
  have hMtop : M = ⊤ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top M with h | h
    · exact absurd (by simpa [h] using hτM) hτ1
    · exact h
  have : IsSimpleGroup ↥M :=
    ((MulEquiv.subgroupCongr hMtop).trans Subgroup.topEquiv).isSimpleGroup
  set N : Subgroup ↥M := goldschmidtOddCore ↥M with hN
  have hNn : N.Normal := goldschmidtOddCore_normal ↥M
  have hN0 : N = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top N with h | h
    · exact h
    · exfalso
      have hodd : Odd (Nat.card ↥N) := odd_card_goldschmidtOddCore ↥M
      rw [h, Subgroup.card_top] at hodd
      have hτ2' : (⟨τ, hτM⟩ : ↥M) ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using hτ2)
      have hτ1' : (⟨τ, hτM⟩ : ↥M) ≠ 1 := fun h' => hτ1 (congrArg Subtype.val h')
      have h2 : 2 ∣ Nat.card ↥M := by
        have := orderOf_dvd_natCard (⟨τ, hτM⟩ : ↥M)
        rwa [orderOf_eq_prime hτ2' hτ1'] at this
      obtain ⟨k, hk⟩ := hodd
      omega
  set π : ↥M →* ↥M ⧸ N := QuotientGroup.mk' N with hπ
  have hπinj : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, hπ, QuotientGroup.ker_mk', hN0]
  have : Nontrivial (↥M ⧸ N) := hπinj.nontrivial
  have : IsSimpleGroup (↥M ⧸ N) :=
    IsSimpleGroup.isSimpleGroup_of_surjective π (QuotientGroup.mk'_surjective N)
  have hp0 : CFSG.pCore 2 (↥M ⧸ N) = ⊥ := by
    have : (CFSG.pCore 2 (↥M ⧸ N)).Normal := CFSG.pCore_normal
    rcases Subgroup.Normal.eq_bot_or_eq_top (CFSG.pCore 2 (↥M ⧸ N)) with h | h
    · exact h
    · exfalso
      have h2 : IsPGroup 2 ↥(CFSG.pCore 2 (↥M ⧸ N)) := CFSG.pCore_isPGroup
      rw [h] at h2
      have h3 : IsPGroup 2 (↥M ⧸ N) :=
        h2.of_surjective (Subgroup.topEquiv (G := ↥M ⧸ N)).toMonoidHom
          (Subgroup.topEquiv (G := ↥M ⧸ N)).surjective
      have : Group.IsNilpotent (↥M ⧸ N) := h3.isNilpotent
      have hcomm : ∀ a b : ↥M ⧸ N, a * b = b * a :=
        IsSimpleGroup.comm_iff_isSolvable.2 inferInstance
      obtain ⟨g1, g2, hg⟩ := hnab
      apply hg
      have hg1 : g1 ∈ M := hMtop ▸ Subgroup.mem_top g1
      have hg2 : g2 ∈ M := hMtop ▸ Subgroup.mem_top g2
      have := hcomm (π ⟨g1, hg1⟩) (π ⟨g2, hg2⟩)
      rw [← map_mul, ← map_mul] at this
      exact congrArg Subtype.val (hπinj this)
  have hlayer : goldschmidtLayer (↥M ⧸ N) = ⊤ := by
    rw [hp0, bot_sup_eq] at ha
    exact ha
  have huM : u ∈ M := hMtop ▸ Subgroup.mem_top u
  have hm2 : (⟨u, huM⟩ : ↥M) ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using hu2)
  have hmem : π ⟨u, huM⟩ ∈ (A.subgroupOf M).map π := by
    rw [hb]
    refine Subgroup.mem_sup_right (Subgroup.subset_closure ⟨⟨?_, ?_⟩, ?_⟩)
    · exact ⟨⟨u, huM⟩, Subgroup.mem_subgroupOf.2 hu, rfl⟩
    · rw [hlayer]
      exact Subgroup.mem_top _
    · rw [← map_pow, hm2, map_one]
  obtain ⟨w, hw, hwm⟩ := Subgroup.mem_map.1 hmem
  have hwu : w = ⟨u, huM⟩ := hπinj hwm
  rw [hwu] at hw
  exact Subgroup.mem_subgroupOf.1 hw

theorem involutions_commute_of_wcl_abelian (hG : Goldschmidt1974) [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (S : Sylow 2 G) {τ : G} (hτ1 : τ ≠ 1) (hτ2 : τ * τ = 1)
    (hτS : τ ∈ (S : Subgroup G)) (hτc : ∀ x ∈ (S : Subgroup G), x * τ = τ * x)
    (hab : IsMulCommutative (S11.wcl τ)) :
    ∀ a ∈ (S : Subgroup G), ∀ b ∈ (S : Subgroup G), a * a = 1 → b * b = 1 → a * b = b * a := by
  intro a ha b hb ha2 hb2
  have h1 := mem_wcl_of_involution hG hnab S hτ1 hτ2 hτS hτc hab ha ha2
  have h2 := mem_wcl_of_involution hG hnab S hτ1 hτ2 hτS hτc hab hb hb2
  exact congrArg Subtype.val (hab.is_comm.comm ⟨a, h1⟩ ⟨b, h2⟩)

end CFSG.CGT.T75F
