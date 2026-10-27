module

public import CFSG.ClassicalInvolution.Q3.Q3T6OpenSDMuC
public import CFSG.ClassicalInvolution.AschTight.T6ASD
public import CFSG.ClassicalInvolution.AschTight.MuZ2Final

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T6.SD

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

theorem twoSubgroupsFourGenerated_of_allTypeTwo (hB3 : GoldschmidtB3Tmp) [IsSimpleGroup G]
    (ht : Setup194Three K z) (hA : AllTypeTwo K z) : TwoSubgroupsFourGenerated G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hI := ht.isUniqueInvolution
  obtain ⟨Q₀⟩ : Nonempty (Sylow 2 K) := inferInstance
  set R : Subgroup G := (Q₀ : Subgroup K).map K.subtype with hRdef
  have hR : R ∈ RSet (CoreAssembly.conjClass K) :=
    ⟨K, CoreAssembly.mem_conjClass_self K, Q₀, rfl⟩
  have hRK : R ≤ K := Subgroup.map_subtype_le _
  have hzR : IsUniqueInvolution R z := ht.isUniqueInvolution_of_mem_rSet_of_le hR hRK
  obtain ⟨S, hRS⟩ := (Q₀.isPGroup'.map K.subtype).exists_le_sylow
  have hSN : (S : Subgroup G) ≤ Subgroup.normalizer (R : Set G) := by
    intro s hs
    have hle : conjSubgroup s R ≤ (S : Subgroup G) := by
      intro x hx
      have hx' := mem_conjSubgroup_iff.mp hx
      have e : x = s * (s⁻¹ * x * s) * s⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hs (hRS hx')) (Subgroup.inv_mem _ hs)
    exact conjSubgroup_eq_self_iff.mp
      (ht.sylow_eq Q₀ S.isPGroup' hRS hle)
  have hSz : (S : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := by
    intro s hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hzR.conj_eq (conjSub_eq_of_mem_normalizer (hSN hs))
    calc s * z = s * z * s⁻¹ * s := by group
      _ = z * s := by rw [h1]
  have hSKR : (S : Subgroup G) ⊓ K ≤ R := by
    have h2 : IsPGroup 2 (((S : Subgroup G) ⊓ K).subgroupOf K) :=
      (S.isPGroup'.to_le inf_le_left).comap_subtype
    have hle : (Q₀ : Subgroup K) ≤ ((S : Subgroup G) ⊓ K).subgroupOf K := by
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr ⟨hRS ⟨x, hx, rfl⟩, x.2⟩
    have heq := Q₀.3 h2 hle
    intro x hx
    have hxK : x ∈ K := hx.2
    have : (⟨x, hxK⟩ : K) ∈ ((S : Subgroup G) ⊓ K).subgroupOf K := Subgroup.mem_subgroupOf.mpr hx
    rw [heq] at this
    exact ⟨⟨x, hxK⟩, this, rfl⟩
  obtain ⟨g, htS, htz⟩ := exists_conj_mem_sylow_ne ht S hSz
  set t := g * z * g⁻¹ with htdef
  set P := R ⊔ Subgroup.zpowers t with hPdef
  have hPS : P ≤ (S : Subgroup G) := sup_le hRS (Subgroup.zpowers_le.mpr htS)
  have htzc : t * z = z * t := Subgroup.mem_centralizer_singleton_iff.mp (hSz htS)
  have hsd := isSemidihedral_sup_of_allTypeTwo ht hA hR hRK (hSN htS) htzc htz
  obtain ⟨a, b, M, hsdd⟩ := exists_sdData (S.isPGroup'.to_le hPS) hsd
  have hcl : fusionStronglyClosed (P : Set G) S := by
    intro x hx y hy
    have := mem_sup_of_conj_mem ht hA hR hRK hRS hSKR hSN hSz htS htz hx (y := y⁻¹)
      (by rwa [inv_inv])
    rwa [inv_inv] at this
  have hNC : ∀ n ∈ Subgroup.normalizer (P : Set G), ∃ k : ℕ,
      n ^ (2 ^ k) ∈ Subgroup.centralizer (P : Set G) := by
    intro n hn
    obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos n).ne'
    refine ⟨k, hsdd.mem_centralizer_of_odd (Subgroup.pow_mem _ hn _) ?_⟩
    rw [orderOf_pow' n (pow_ne_zero _ two_ne_zero), hkm,
      Nat.gcd_mul_right_left, Nat.mul_div_cancel_left _ (by positivity)]
    exact hm
  have hB := hB3 G S P hPS hcl hNC
  have hncl : Subgroup.normalClosure (P : Set G) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.normalClosure (P : Set G)) with
      h0 | h0
    · exfalso
      have : z ∈ Subgroup.normalClosure (P : Set G) :=
        Subgroup.le_normalClosure (Subgroup.mem_sup_left hzR.mem)
      rw [h0, Subgroup.mem_bot] at this
      exact hI.ne_one this
    · exact h0
  have hPeq : (S : Subgroup G) = P := hB.2.2 _ (hncl ▸ le_top) S.isPGroup' hPS
  have hsdS : SDData (S : Subgroup G) a b M := by rw [hPeq]; exact hsdd
  exact T6A.twoSubgroupsFourGenerated_of_sdData S hsdS

end CFSG.ClassicalInvolution.Q3.Q3T6.SD
