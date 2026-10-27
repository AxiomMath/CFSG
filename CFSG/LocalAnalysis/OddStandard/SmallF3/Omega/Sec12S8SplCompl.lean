module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8SplLift
public import CFSG.CGT.T75P.Split

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

private lemma s8_compl_alpha_V1 {P : Type} [Group P] {V1 : Subgroup P}
    {φ : (Fin 5 → ZMod 2) → P} (hφ : Sec128Coord V1 φ) (α : P →* S8A5)
    (hact : ∀ (g : P) (v : Fin 5 → ZMod 2), IsEvenVec v →
      g * φ v * g⁻¹ = φ (permVec ((α g : S8A5) : Equiv.Perm (Fin 5)) v)) :
    ∀ x ∈ V1, α x = 1 := by
  intro x hx
  apply s8_fin_faithful
  intro v hv
  apply hφ.eq_of_eq' (s8_isEvenVec_permVec _ hv) hv
  rw [← hact x v hv]
  rw [hφ.comm_mem hx (hφ.mem v hv)]
  group

private lemma s8_compl_K0 {P : Type} [Group P] {H V1 : Subgroup P}
    {φ : (Fin 5 → ZMod 2) → P} (hφ : Sec128Coord V1 φ) (hVH : V1 ≤ H) (hn : V1.Normal)
    (α : P →* S8A5) (hα : ∀ a : S8A5, ∃ h ∈ H, α h = a)
    (hker : ∀ h ∈ H, α h = 1 → h ∈ V1)
    (hact : ∀ (g : P) (v : Fin 5 → ZMod 2), IsEvenVec v →
      g * φ v * g⁻¹ = φ (permVec ((α g : S8A5) : Equiv.Perm (Fin 5)) v)) :
    ∃ K0 : Subgroup P, K0 ≤ H ∧ V1 ⊓ K0 = ⊥ ∧ V1 ⊔ K0 = H ⊓ s8K4.comap α := by
  have hkerV1 : ∀ x ∈ V1, α x = 1 := s8_compl_alpha_V1 hφ α hact
  obtain ⟨a0, ha0H, ha0⟩ := hα s8PaA
  obtain ⟨b0, hb0H, hb0⟩ := hα s8PbA
  have hcoe_a : ((α a0 : S8A5) : Equiv.Perm (Fin 5)) = s8Pa := by rw [ha0]; rfl
  have hcoe_b : ((α b0 : S8A5) : Equiv.Perm (Fin 5)) = s8Pb := by rw [hb0]; rfl
  have ha : ∀ v : Fin 5 → ZMod 2, IsEvenVec v →
      a0 * φ v * a0⁻¹ = φ (permVec s8Pa v) := by
    intro v hv
    simpa only [hcoe_a] using hact a0 v hv
  have hb : ∀ v : Fin 5 → ZMod 2, IsEvenVec v →
      b0 * φ v * b0⁻¹ = φ (permVec s8Pb v) := by
    intro v hv
    simpa only [hcoe_b] using hact b0 v hv
  have haa : a0 * a0 ∈ V1 := by
    refine hker _ (H.mul_mem ha0H ha0H) ?_
    rw [map_mul, ha0, s8K4_facts.1]
  have hbb : b0 * b0 ∈ V1 := by
    refine hker _ (H.mul_mem hb0H hb0H) ?_
    rw [map_mul, hb0, s8K4_facts.2.1]
  have hcommP : s8PaA * s8PbA * s8PaA⁻¹ * s8PbA⁻¹ = 1 := by
    rw [inv_eq_of_mul_eq_one_right s8K4_facts.1,
      inv_eq_of_mul_eq_one_right s8K4_facts.2.1]
    calc s8PaA * s8PbA * s8PaA * s8PbA
        = s8PaA * (s8PbA * s8PaA) * s8PbA := by group
      _ = s8PaA * (s8PaA * s8PbA) * s8PbA := by rw [← s8K4_facts.2.2.1]
      _ = (s8PaA * s8PaA) * (s8PbA * s8PbA) := by group
      _ = 1 := by rw [s8K4_facts.1, s8K4_facts.2.1, mul_one]
  have hab : a0 * b0 * a0⁻¹ * b0⁻¹ ∈ V1 := by
    refine hker _ ?_ ?_
    · exact H.mul_mem (H.mul_mem (H.mul_mem ha0H hb0H) (H.inv_mem ha0H)) (H.inv_mem hb0H)
    · simpa only [map_mul, map_inv, ha0, hb0] using hcommP
  obtain ⟨a', b', ha'mem, hb'mem, ha'sq, hb'sq, hab'comm⟩ :=
    s8_k4_lift hn hφ ha hb haa hbb hab
  have ha'_eq : a' = a0 * (a'⁻¹ * a0)⁻¹ := by group
  have ha'H : a' ∈ H := by
    rw [ha'_eq]
    exact H.mul_mem ha0H (H.inv_mem (hVH ha'mem))
  have ha'alpha : α a' = s8PaA := by
    rw [ha'_eq, map_mul, map_inv, ha0, hkerV1 (a'⁻¹ * a0) ha'mem]
    simp
  have hb'_eq : b' = b0 * (b'⁻¹ * b0)⁻¹ := by group
  have hb'H : b' ∈ H := by
    rw [hb'_eq]
    exact H.mul_mem hb0H (H.inv_mem (hVH hb'mem))
  have hb'alpha : α b' = s8PbA := by
    rw [hb'_eq, map_mul, map_inv, hb0, hkerV1 (b'⁻¹ * b0) hb'mem]
    simp
  let K0 : Subgroup P := s8Klein a' b' ha'sq hb'sq hab'comm
  have hK0mem : ∀ x : P, x ∈ K0 ↔ x = 1 ∨ x = a' ∨ x = b' ∨ x = a' * b' :=
    fun x => mem_s8Klein_iff a' b' ha'sq hb'sq hab'comm x
  have hK0H : K0 ≤ H := by
    intro x hx
    rcases (hK0mem x).1 hx with rfl | rfl | rfl | rfl
    · exact H.one_mem
    · exact ha'H
    · exact hb'H
    · exact H.mul_mem ha'H hb'H
  have hmemK4 : ∀ y : S8A5,
      y ∈ s8K4 ↔ y = 1 ∨ y = s8PaA ∨ y = s8PbA ∨ y = s8PaA * s8PbA := by
    intro y
    exact mem_s8Klein_iff s8PaA s8PbA s8K4_facts.1 s8K4_facts.2.1 s8K4_facts.2.2.1 y
  have hV1T : V1 ≤ H ⊓ s8K4.comap α := by
    intro x hx
    refine Subgroup.mem_inf.2 ⟨hVH hx, ?_⟩
    show α x ∈ s8K4
    rw [hkerV1 x hx]
    exact s8K4.one_mem
  have hK0T : K0 ≤ H ⊓ s8K4.comap α := by
    intro x hx
    refine Subgroup.mem_inf.2 ⟨hK0H hx, ?_⟩
    show α x ∈ s8K4
    rcases (hK0mem x).1 hx with rfl | rfl | rfl | rfl
    · rw [map_one]
      exact s8K4.one_mem
    · rw [ha'alpha]
      exact (hmemK4 s8PaA).2 (Or.inr (Or.inl rfl))
    · rw [hb'alpha]
      exact (hmemK4 s8PbA).2 (Or.inr (Or.inr (Or.inl rfl)))
    · rw [map_mul, ha'alpha, hb'alpha]
      exact (hmemK4 (s8PaA * s8PbA)).2 (Or.inr (Or.inr (Or.inr rfl)))
  have hTle : H ⊓ s8K4.comap α ≤ V1 ⊔ K0 := by
    intro x hx
    obtain ⟨hxH, hxK4⟩ := Subgroup.mem_inf.1 hx
    have hxK4' := (hmemK4 (α x)).1 hxK4
    rcases hxK4' with h0 | h0 | h0 | h0
    · exact Subgroup.mem_sup_left (hker x hxH h0)
    · have hy : a' ∈ K0 := (hK0mem a').2 (Or.inr (Or.inl rfl))
      have hz : a'⁻¹ * x ∈ V1 := by
        refine hker _ (H.mul_mem (H.inv_mem ha'H) hxH) ?_
        rw [map_mul, map_inv, ha'alpha, h0]
        simp
      have hxeq : x = a' * (a'⁻¹ * x) := by group
      rw [hxeq, sup_comm]
      exact Subgroup.mul_mem_sup hy hz
    · have hy : b' ∈ K0 := (hK0mem b').2 (Or.inr (Or.inr (Or.inl rfl)))
      have hz : b'⁻¹ * x ∈ V1 := by
        refine hker _ (H.mul_mem (H.inv_mem hb'H) hxH) ?_
        rw [map_mul, map_inv, hb'alpha, h0]
        simp
      have hxeq : x = b' * (b'⁻¹ * x) := by group
      rw [hxeq, sup_comm]
      exact Subgroup.mul_mem_sup hy hz
    · have hy : a' * b' ∈ K0 := (hK0mem (a' * b')).2 (Or.inr (Or.inr (Or.inr rfl)))
      have hz : (a' * b')⁻¹ * x ∈ V1 := by
        refine hker _ (H.mul_mem (H.inv_mem (H.mul_mem ha'H hb'H)) hxH) ?_
        rw [map_mul, map_inv, map_mul, ha'alpha, hb'alpha, h0]
        simp
      have hxeq : x = (a' * b') * ((a' * b')⁻¹ * x) := by group
      rw [hxeq, sup_comm]
      exact Subgroup.mul_mem_sup hy hz
  have hV1K0bot : V1 ⊓ K0 = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxV1, hxK0⟩ := Subgroup.mem_inf.1 hx
    have hxK0' := (hK0mem x).1 hxK0
    have hxα : α x = 1 := hkerV1 x hxV1
    rw [Subgroup.mem_bot]
    rcases hxK0' with rfl | rfl | rfl | rfl
    · rfl
    · exact absurd (by rw [← ha'alpha, hxα] : s8PaA = 1) s8K4_facts.2.2.2.1
    · exact absurd (by rw [← hb'alpha, hxα] : s8PbA = 1) s8K4_facts.2.2.2.2.1
    · exact absurd (by rw [← ha'alpha, ← hb'alpha, ← map_mul, hxα] : s8PaA * s8PbA = 1)
        s8K4_facts.2.2.2.2.2.1
  exact ⟨K0, hK0H, hV1K0bot, le_antisymm (sup_le hV1T hK0T) hTle⟩

theorem s8_complement {P : Type} [Group P] [Finite P] {H V1 : Subgroup P}
    {φ : (Fin 5 → ZMod 2) → P} (hφ : Sec128Coord V1 φ) (hVH : V1 ≤ H) (hn : V1.Normal)
    (α : P →* S8A5) (hα : ∀ a : S8A5, ∃ h ∈ H, α h = a) (hker : ∀ h ∈ H, α h = 1 → h ∈ V1)
    (hact : ∀ (g : P) (v : Fin 5 → ZMod 2), IsEvenVec v →
      g * φ v * g⁻¹ = φ (permVec ((α g : S8A5) : Equiv.Perm (Fin 5)) v)) :
    ∃ C : Subgroup P, C ≤ H ∧ V1 ⊓ C = ⊥ ∧ V1 ⊔ C = H := by
  obtain ⟨K0, hK0H, hV1K0bot, hsup⟩ := s8_compl_K0 hφ hVH hn α hα hker hact
  have hmap : H.map α = ⊤ := by
    apply eq_top_iff.2
    intro a _
    obtain ⟨h, hhH, hha⟩ := hα a
    exact ⟨h, hhH, hha⟩
  have hindex : (V1 ⊔ K0).relIndex H = 15 := by
    rw [hsup, Subgroup.inf_relIndex_left, Subgroup.relIndex_comap]
    rw [hmap, Subgroup.relIndex_top_right, s8K4_index]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : ∃ n : ℕ, Nat.card V1 = 2 ^ n := by
    have hpgrp : IsPGroup 2 ↥V1 := by
      intro g
      refine ⟨1, ?_⟩
      rw [pow_one, pow_two]
      exact Subtype.ext (hφ.mul_self_mem g.2)
    exact IsPGroup.iff_card.mp hpgrp
  have hcop : Nat.Coprime ((V1 ⊔ K0).relIndex H) (Nat.card V1) := by
    obtain ⟨n, hn⟩ := hcard
    rw [hindex, hn]
    exact Nat.Coprime.pow_right n (by decide)
  exact CFSG.CGT.T75P.exists_complement_of_coprime_index hVH hK0H (hn.subgroupOf H)
    (fun a ha b hb => hφ.comm_mem ha hb) hV1K0bot hcop

end CFSG.OddStandard.SmallF3.Omega
