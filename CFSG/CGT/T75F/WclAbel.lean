module

public import CFSG.CGT.Timmesfeld75.Sec5FiveEngHelp
public import CFSG.LargeExtraspecial.S111SHCor3

public section

namespace CFSG.CGT.T75F

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.LargeExtraspecial

variable {G : Type} [Group G] [Finite G] {T T₁ : Subgroup G}

theorem exists_central_of_secA (hy : StepHyp T T₁) (hA : secA T T₁ ≠ ⊥) :
    ∃ (S : Sylow 2 G) (τ : G), T ≤ (S : Subgroup G) ∧ τ ∈ secA T T₁ ∧ τ ≠ 1 ∧ τ * τ = 1 ∧
      τ ∈ (S : Subgroup G) ∧ ∀ x ∈ (S : Subgroup G), x * τ = τ * x := by
  obtain ⟨S, hTS⟩ := (isPGroup_two_of_isElemAbelian hy.pair.wc.1).exists_le_sylow
  have hSN : (S : Subgroup G) ≤ Subgroup.normalizer (T : Set G) := fun s hs =>
    mem_normalizer_of_conjSubgroup_eq
      (eq_of_conj_le_pGroup hy.pair.wc S.isPGroup' hTS (conjSubgroup_le_of_le_of_mem hTS hs))
  have hAS : secA T T₁ ≤ (S : Subgroup G) := secA_le_left.trans hTS
  have hAn : ((secA T T₁).subgroupOf (S : Subgroup G)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h : (g : G) * (n : G) * (g : G)⁻¹ ∈ conjSubgroup (g : G) (secA T T₁) :=
      ⟨n, hn, by simp [MulAut.conj_apply]⟩
    rwa [conjSubgroup_secA (hSN g.2)] at h
  have hnil : Group.IsNilpotent ↥(S : Subgroup G) := S.isPGroup'.isNilpotent
  obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA
  have hbot : (secA T T₁).subgroupOf (S : Subgroup G) ≠ ⊥ :=
    Subgroup.ne_bot_iff_exists_ne_one.2
      ⟨⟨⟨a, hAS ha⟩, Subgroup.mem_subgroupOf.2 ha⟩, fun h => ha1 (Subtype.ext (by
        have := congrArg (fun x : ↥((secA T T₁).subgroupOf (S : Subgroup G)) => ((x : ↥S) : G)) h
        simpa using this))⟩
  have hne := @Group.IsNilpotent.inf_center_ne_bot_of_normal ↥(S : Subgroup G) _ hnil
    ((secA T T₁).subgroupOf (S : Subgroup G)) hAn hbot
  obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hxA : (x : G) ∈ secA T T₁ := Subgroup.mem_subgroupOf.1 hx.1
  refine ⟨S, (x : G), hTS, hxA, fun h => hx1 (Subtype.ext (Subtype.ext h)),
    elemAbelian_mul_self hy.pair.wc.1 (secA_le_left hxA), x.2, fun y hy' => ?_⟩
  exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hx.2 ⟨y, hy'⟩)

theorem wclSet_subset_sup (hy : StepHyp T T₁) (hS : Sec3Global T)
    (hcase : ∀ g : G, conjSubgroup g (secA T T₁) ≤ Subgroup.normalizer (T : Set G) →
      conjSubgroup g T ≠ T → conjSubgroup g (secA T T₁) ≤ secR₁ T T₁)
    {τ : G} (hτA : τ ∈ secA T T₁) (hτ1 : τ ≠ 1) :
    S11.wclSet τ ⊆ ((secA T T₁ ⊔ secR₁ T T₁ : Subgroup G) : Set G) := by
  rintro e ⟨m, rfl, hcomm⟩
  have hτT : τ ∈ T := secA_le_left hτA
  have hτD : τ ∈ classD T := mem_classD_of_mem hτT hτ1
  have he1 : m * τ * m⁻¹ ≠ 1 := fun h => hτ1 (by
    calc τ = m⁻¹ * (m * τ * m⁻¹) * m := by group
      _ = 1 := by rw [h]; group)
  have heT : m * τ * m⁻¹ ∈ conjSubgroup m T := ⟨τ, hτT, by simp [MulAut.conj_apply]⟩
  have hτN : τ ∈ Subgroup.normalizer ((conjSubgroup m T : Subgroup G) : Set G) :=
    (hy.pair.wc.conj m).centralizer_le_normalizer heT he1
      (Subgroup.mem_centralizer_singleton_iff.2 hcomm.symm)
  have hcommA : ∀ a ∈ conjSubgroup m (secA T T₁), a * τ = τ * a :=
    conjSubgroup_secA_comm_of_mem_normalizer hy.pair hS hτD hτN
  have hAmN : conjSubgroup m (secA T T₁) ≤ Subgroup.normalizer (T : Set G) := fun a ha =>
    hy.pair.wc.centralizer_le_normalizer hτT hτ1
      (Subgroup.mem_centralizer_singleton_iff.2 (hcommA a ha))
  have heA : m * τ * m⁻¹ ∈ conjSubgroup m (secA T T₁) := ⟨τ, hτA, by simp [MulAut.conj_apply]⟩
  by_cases hmT : conjSubgroup m T = T
  · rw [conjSubgroup_secA (mem_normalizer_of_conjSubgroup_eq hmT)] at heA
    exact Subgroup.mem_sup_left heA
  · exact Subgroup.mem_sup_right (hcase m hAmN hmT heA)

theorem secA_comm_secR₁ (hy : StepHyp T T₁) (hS : Sec3Global T) :
    ∀ a ∈ secA T T₁, ∀ x ∈ secR₁ T T₁, a * x = x * a := by
  have h : secR₁ T T₁ ≤ Subgroup.centralizer (secA T T₁ : Set G) := by
    refine iSup₂_le fun h hu => ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    by_cases hx1 : x = 1
    · simp [hx1]
    have hxN : x ∈ Subgroup.normalizer (T : Set G) := hu.conj_secA_le_normalizer hy.pair hS hx
    have hxT : x ∈ conjSubgroup h T := conjSubgroup_mono secA_le_left hx
    have hxD : x ∈ normD T := ⟨mem_classD_of_mem_conjSubgroup hxT hx1, hxN⟩
    exact (Subgroup.mem_centralizer_iff.1 (secA_le_centralizer_normD hy.pair hS ha) x hxD).symm
  intro a ha x hx
  exact Subgroup.mem_centralizer_iff.1 (h hx) a ha

theorem comm_secA_sup_secR₁ (hy : StepHyp T T₁) (hS : Sec3Global T)
    (hab : ∀ x ∈ secR₁ T T₁, ∀ y ∈ secR₁ T T₁, x * y = y * x) :
    ∀ u ∈ (secA T T₁ ⊔ secR₁ T T₁ : Subgroup G), ∀ v ∈ (secA T T₁ ⊔ secR₁ T T₁ : Subgroup G),
      u * v = v * u := by
  have hAA : ∀ a ∈ secA T T₁, ∀ b ∈ secA T T₁, a * b = b * a := fun a ha b hb =>
    elemAbelian_mul_comm hy.pair.wc.1 (secA_le_left ha) (secA_le_left hb)
  have hAR := secA_comm_secR₁ hy hS
  have hK1 : secA T T₁ ⊔ secR₁ T T₁ ≤ Subgroup.centralizer (secA T T₁ : Set G) :=
    sup_le (fun a ha => Subgroup.mem_centralizer_iff.2 fun b hb => hAA b hb a ha)
      (fun x hx => Subgroup.mem_centralizer_iff.2 fun b hb => hAR b hb x hx)
  have hK2 : secA T T₁ ⊔ secR₁ T T₁ ≤ Subgroup.centralizer (secR₁ T T₁ : Set G) :=
    sup_le (fun a ha => Subgroup.mem_centralizer_iff.2 fun x hx => (hAR a ha x hx).symm)
      (fun x hx => Subgroup.mem_centralizer_iff.2 fun y hy' => hab y hy' x hx)
  have hAK : secA T T₁ ≤ Subgroup.centralizer ((secA T T₁ ⊔ secR₁ T T₁ : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.2 hK1
  have hRK : secR₁ T T₁ ≤ Subgroup.centralizer ((secA T T₁ ⊔ secR₁ T T₁ : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.2 hK2
  have hKK := sup_le hAK hRK
  intro u hu v hv
  exact (Subgroup.mem_centralizer_iff.1 (hKK hu) v hv).symm

theorem isMulCommutative_wcl (hy : StepHyp T T₁) (hS : Sec3Global T)
    (hab : ∀ x ∈ secR₁ T T₁, ∀ y ∈ secR₁ T T₁, x * y = y * x)
    (hcase : ∀ g : G, conjSubgroup g (secA T T₁) ≤ Subgroup.normalizer (T : Set G) →
      conjSubgroup g T ≠ T → conjSubgroup g (secA T T₁) ≤ secR₁ T T₁)
    {τ : G} (hτA : τ ∈ secA T T₁) (hτ1 : τ ≠ 1) : IsMulCommutative (S11.wcl τ) := by
  have hle : S11.wcl τ ≤ secA T T₁ ⊔ secR₁ T T₁ :=
    (Subgroup.closure_le _).2 (wclSet_subset_sup hy hS hcase hτA hτ1)
  exact ⟨⟨fun a b => Subtype.ext (comm_secA_sup_secR₁ hy hS hab a.1 (hle a.2) b.1 (hle b.2))⟩⟩

end CFSG.CGT.T75F
