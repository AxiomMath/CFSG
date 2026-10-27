module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.InvariantComplement

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

theorem exists_proj_of_odd {G : Type*} [Group G] [Finite G] {R A : Subgroup G} (hAR : A ≤ R)
    (hRc : ∀ r ∈ R, ∀ r' ∈ R, r * r' = r' * r) (hR2 : ∀ r ∈ R, r ^ 2 = 1) {d : G}
    (hd : Odd (orderOf d)) (hdR : d ∈ normalizer (R : Set G))
    (hdA : d ∈ normalizer (A : Set G)) :
    ∃ π : G → G, (∀ r ∈ R, π r ∈ A) ∧ (∀ a ∈ A, π a = a) ∧
      (∀ r ∈ R, ∀ r' ∈ R, π (r * r') = π r * π r') ∧
      (∀ r ∈ R, π (d * r * d⁻¹) = d * π r * d⁻¹) := by
  classical
  obtain ⟨C, hCR, hdC, hAC, hcov⟩ : ∃ C : Subgroup G, C ≤ R ∧ (∀ c ∈ C, d * c * d⁻¹ ∈ C) ∧
      (∀ x ∈ A, x ∈ C → x = 1) ∧ (∀ r ∈ R, ∃ a ∈ A, ∃ c ∈ C, a * c = r) := by
    have hRle : zpowers d ≤ normalizer (R : Set G) := zpowers_le.mpr hdR
    have hAle : zpowers d ≤ normalizer (A : Set G) := zpowers_le.mpr hdA
    have hconj : ∀ x : zpowers d, ∀ r : R, (x : G) * r * (x : G)⁻¹ ∈ R := fun x r =>
      (mem_normalizer_iff.mp (hRle x.2) r).mp r.2
    let cf : zpowers d → R → R := fun x r => ⟨(x : G) * r * (x : G)⁻¹, hconj x r⟩
    have hcf : ∀ x r, ((cf x r : R) : G) = (x : G) * r * (x : G)⁻¹ := fun _ _ => rfl
    let act : MulDistribMulAction (zpowers d) R :=
      { smul := cf
        one_smul := fun r => Subtype.ext (by
          show ((cf 1 r : R) : G) = r
          rw [hcf]
          simp)
        mul_smul := fun x y r => Subtype.ext (by
          show ((cf (x * y) r : R) : G) = (cf x (cf y r) : G)
          rw [hcf, hcf, hcf, Subgroup.coe_mul]
          group)
        smul_one := fun x => Subtype.ext (by
          show ((cf x 1 : R) : G) = 1
          rw [hcf]
          simp)
        smul_mul := fun x r r' => Subtype.ext (by
          show ((cf x (r * r') : R) : G) = (cf x r : G) * (cf x r' : G)
          rw [hcf, hcf, hcf, Subgroup.coe_mul]
          group) }
    have hsmul : ∀ (x : zpowers d) (r : R), ((x • r : R) : G) = (x : G) * r * (x : G)⁻¹ :=
      fun _ _ => rfl
    let : Fintype (zpowers d) := Fintype.ofFinite _
    have hodd : Odd (Fintype.card (zpowers d)) := by
      rw [← Nat.card_eq_fintype_card, Nat.card_zpowers]
      exact hd
    have : IsElementaryAbelian 2 R :=
      { is_comm := ⟨fun a b => Subtype.ext (hRc a a.2 b b.2)⟩
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
          Subtype.ext (by simpa using hR2 g g.2) }
    obtain ⟨W, hW, hWinv⟩ :=
      CFSG.BenderSuzuki.External.Higman.exists_isCompl_invariant_subgroup_of_odd_group
        (A := zpowers d) (G := R) hodd (A.subgroupOf R) (fun x g hg => by
          rw [mem_subgroupOf] at hg ⊢
          rw [hsmul]
          exact (mem_normalizer_iff.mp (hAle x.2) _).mp hg)
    have hWn : W.Normal := ⟨fun n _ g => by
      have e : g * n * g⁻¹ = n := by
        rw [Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_mul,
          hRc _ g.2 _ n.2, Subgroup.coe_inv, mul_inv_cancel_right]
      rwa [e]⟩
    refine ⟨W.map R.subtype, map_subtype_le W, ?_, ?_, ?_⟩
    · rintro _ ⟨w, hw, rfl⟩
      exact ⟨⟨d, mem_zpowers d⟩ • w, hWinv _ w hw, hsmul _ w⟩
    · rintro x hxA ⟨w, hw, rfl⟩
      have hwA : w ∈ A.subgroupOf R := by
        rw [mem_subgroupOf]
        exact hxA
      have := Subgroup.disjoint_def.mp hW.disjoint hwA hw
      rw [this]
      rfl
    · intro r hr
      have hmem : (⟨r, hr⟩ : R) ∈ A.subgroupOf R ⊔ W := by
        rw [hW.sup_eq_top]
        exact mem_top _
      obtain ⟨y, hy, z, hz, hyz⟩ := mem_sup_of_normal_right.mp hmem
      refine ⟨y, (mem_subgroupOf.mp hy), z, ⟨z, hz, rfl⟩, ?_⟩
      have := congrArg Subtype.val hyz
      rw [Subgroup.coe_mul] at this
      exact this
  have huniq : ∀ a ∈ A, ∀ c ∈ C, ∀ a' ∈ A, ∀ c' ∈ C, a * c = a' * c' → a = a' := by
    intro a ha c hc a' ha' c' hc' h
    have h1 : a'⁻¹ * a = c' * c⁻¹ := by
      calc a'⁻¹ * a = a'⁻¹ * (a * c) * c⁻¹ := by group
        _ = a'⁻¹ * (a' * c') * c⁻¹ := by rw [h]
        _ = c' * c⁻¹ := by group
    have h2 := hAC _ (mul_mem (inv_mem ha') ha) (h1 ▸ mul_mem hc' (inv_mem hc))
    rw [inv_mul_eq_one] at h2
    exact h2.symm
  choose! πa hπA πc hπC hπ using hcov
  refine ⟨πa, hπA, fun a ha => ?_, fun r hr r' hr' => ?_, fun r hr => ?_⟩
  · exact huniq _ (hπA a (hAR ha)) _ (hπC a (hAR ha)) a ha 1 (one_mem _)
      (by rw [hπ a (hAR ha), mul_one])
  · have hrr' : r * r' ∈ R := mul_mem hr hr'
    refine huniq _ (hπA _ hrr') _ (hπC _ hrr') _ (mul_mem (hπA r hr) (hπA r' hr')) _
      (mul_mem (hπC r hr) (hπC r' hr')) ?_
    rw [hπ _ hrr']
    have hcomm : πc r * πa r' = πa r' * πc r := hRc _ (hCR (hπC r hr)) _ (hAR (hπA r' hr'))
    calc r * r' = πa r * πc r * (πa r' * πc r') := by rw [hπ r hr, hπ r' hr']
      _ = πa r * (πc r * πa r') * πc r' := by group
      _ = πa r * (πa r' * πc r) * πc r' := by rw [hcomm]
      _ = πa r * πa r' * (πc r * πc r') := by group
  · have hdr : d * r * d⁻¹ ∈ R := (mem_normalizer_iff.mp hdR r).mp hr
    refine huniq _ (hπA _ hdr) _ (hπC _ hdr) _ ((mem_normalizer_iff.mp hdA _).mp (hπA r hr)) _
      (hdC _ (hπC r hr)) ?_
    rw [hπ _ hdr]
    calc d * r * d⁻¹ = d * (πa r * πc r) * d⁻¹ := by rw [hπ r hr]
      _ = d * πa r * d⁻¹ * (d * πc r * d⁻¹) := by group

end CFSG.SeitzReduction.RankOne
