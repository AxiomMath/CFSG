module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec79B

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem aSub_le_S (S B : Subgroup G) : ASub S B ≤ S := by
  change omega1 (S ⊓ centralizer (B : Set G)) ≤ S
  rw [omega1]
  exact (Subgroup.closure_le S).mpr fun x hx => hx.1.1

theorem sec710_A_inf_L [Finite G] (hP : Asc82Tab6P) (h78 : Asc82Lemma78) {t : G}
    {L S : Subgroup G} {z g : G} {B : Subgroup G} (hc : Sec7Choice G t L S z g B) :
    ASub S B ⊓ L = B := by
  have hcomm : ∀ b ∈ B, Commute b t := fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.mp
      (hc.ctx.sylow.1 (hc.normalE16.1 hb).1)
  let K : Subgroup G :=
    { carrier := {x : G | ∃ k : ℤ, ∃ b ∈ B, x = t ^ k * b}
      one_mem' := ⟨0, 1, B.one_mem, by simp⟩
      mul_mem' := by
        rintro x y ⟨k, b, hb, rfl⟩ ⟨l, c, hcB, rfl⟩
        refine ⟨k + l, b * c, B.mul_mem hb hcB, ?_⟩
        have hbcomm : Commute b (t ^ l) := (hcomm b hb).zpow_right l
        calc (t ^ k * b) * (t ^ l * c) = t ^ k * (b * t ^ l) * c := by group
          _ = t ^ k * (t ^ l * b) * c := by rw [hbcomm.eq]
          _ = (t ^ k * t ^ l) * (b * c) := by group
          _ = t ^ (k + l) * (b * c) := by rw [← zpow_add t k l]
      inv_mem' := by
        rintro x ⟨k, b, hb, rfl⟩
        refine ⟨-k, b⁻¹, B.inv_mem hb, ?_⟩
        have hbcomm : Commute b⁻¹ (t ^ (-k)) := (hcomm b hb).inv_left.zpow_right (-k)
        calc (t ^ k * b)⁻¹ = b⁻¹ * t ^ (-k) := by rw [mul_inv_rev, zpow_neg]
          _ = t ^ (-k) * b⁻¹ := hbcomm.eq }
  have hztK : Subgroup.zpowers t ≤ K := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ⟨k, 1, B.one_mem, by simp⟩
  have hBK : B ≤ K := fun b hb => ⟨0, b, hb, by simp⟩
  have hsupK : Subgroup.zpowers t ⊔ B ≤ K := sup_le hztK hBK
  apply le_antisymm
  · intro a ha
    obtain ⟨haA, haL⟩ := ha
    rw [h78 G t L S z g B hc] at haA
    obtain ⟨k, b, hb, rfl⟩ := hsupK haA
    have hbL : b ∈ L := (hc.normalE16.1 hb).2
    have htkL : t ^ k ∈ L := by
      have h := L.mul_mem haL (L.inv_mem hbL)
      rwa [show (t ^ k * b) * b⁻¹ = t ^ k from by group] at h
    have htkC : t ^ k ∈ centralizer (L : Set G) :=
      (centralizer (L : Set G)).zpow_mem hc.ctx.t_mem_centralizer k
    have htkZ : t ^ k ∈ centerIn L := by
      refine Subgroup.mem_map.mpr ⟨⟨t ^ k, htkL⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp htkC (y : G) y.2)
    have htk1 : t ^ k = 1 :=
      Subgroup.mem_bot.mp (hP.center_triv G L hc.ctx.isOm6P ▸ htkZ)
    rw [htk1, one_mul]
    exact hb
  · intro b hb
    exact ⟨sec79_B_le_A hc hb, (hc.normalE16.1 hb).2⟩

theorem sec710_B_eq_closure [Finite G] (h36 : Asc82Lemma36) (hP : Asc82Tab6P)
    (h75b : Asc82Lemma75b) (h78 : Asc82Lemma78) (h710b : Asc82Lemma710b) {t : G}
    {L S : Subgroup G} {z g : G} {B : Subgroup G} (hc : Sec7Choice G t L S z g B) :
    B = Subgroup.closure ({x : G | IsConj z x} ∩ (ASub S B : Set G)) := by
  have hcl : B = Subgroup.closure (conjClassIn (L ⊓ normalizer (B : Set G)) z) :=
    (h75b G t L S z hc.ctx B hc.normalE16).2.2.2
  have hzB : z ∈ B := by
    rw [hcl]
    exact Subgroup.subset_closure
      ⟨1, ⟨L.one_mem, (normalizer (B : Set G)).one_mem⟩, by simp⟩
  apply le_antisymm
  · conv_lhs => rw [hcl]
    apply Subgroup.closure_mono
    rintro x ⟨h, hh, rfl⟩
    exact ⟨isConj_iff.mpr ⟨h, rfl⟩,
      sec79_B_le_A hc ((Subgroup.mem_normalizer_iff.mp hh.2 z).mp hzB)⟩
  · rw [Subgroup.closure_le]
    rintro x ⟨hxz, hxA⟩
    have hxC : x ∈ centralizer ({t} : Set G) := hc.ctx.sylow.1 (aSub_le_S S B hxA)
    have hxcl : x ∈ conjClassIn L z := by
      rw [← h710b G t L S z g B hc]
      exact ⟨hxz, hxC⟩
    obtain ⟨h, hhL, rfl⟩ := hxcl
    have hxL : h * z * h⁻¹ ∈ L :=
      L.mul_mem (L.mul_mem hhL hc.ctx.z_mem_L) (L.inv_mem hhL)
    have hmem : h * z * h⁻¹ ∈ ASub S B ⊓ L := ⟨hxA, hxL⟩
    rwa [sec710_A_inf_L hP h78 hc] at hmem

theorem sec710_B_normal_M [Finite G] (h36 : Asc82Lemma36) (hP : Asc82Tab6P)
    (h75b : Asc82Lemma75b) (h78 : Asc82Lemma78) (h710b : Asc82Lemma710b) {t : G}
    {L S : Subgroup G} {z g : G} {B : Subgroup G} (hc : Sec7Choice G t L S z g B) :
    (B.subgroupOf (MSub S B)).Normal := by
  have hB : B = Subgroup.closure
      ({x : G | IsConj z x} ∩ (ASub S B : Set G)) :=
    sec710_B_eq_closure h36 hP h75b h78 h710b hc
  have key : ∀ m ∈ MSub S B,
      ∀ b ∈ Subgroup.closure ({x : G | IsConj z x} ∩ (ASub S B : Set G)),
      m * b * m⁻¹ ∈ Subgroup.closure ({x : G | IsConj z x} ∩ (ASub S B : Set G)) := by
    intro m hm b hb
    have hmN : m ∈ normalizer ((ASub S B : Subgroup G) : Set G) := hm
    refine Subgroup.closure_induction (p := fun b _ =>
      m * b * m⁻¹ ∈ Subgroup.closure ({x : G | IsConj z x} ∩ (ASub S B : Set G)))
      ?mem ?one ?mul ?inv hb
    · intro x hx
      exact Subgroup.subset_closure
        ⟨hx.1.trans (isConj_iff.mpr ⟨m, rfl⟩),
          (Subgroup.mem_normalizer_iff.mp hmN x).mp hx.2⟩
    · simp
    · intro y w hy hw ihy ihw
      have heq : m * (y * w) * m⁻¹ = (m * y * m⁻¹) * (m * w * m⁻¹) := by group
      rw [heq]
      exact Subgroup.mul_mem _ ihy ihw
    · intro y hy ihy
      have heq : m * y⁻¹ * m⁻¹ = (m * y * m⁻¹)⁻¹ := by group
      rw [heq]
      exact Subgroup.inv_mem _ ihy
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn
  have hmemcl : ∀ y : G, y ∈ B ↔
      y ∈ Subgroup.closure ({x : G | IsConj z x} ∩ (ASub S B : Set G)) := by
    intro y
    conv_lhs => rw [hB]
  have hn' : (n : G) ∈ Subgroup.closure
      ({x : G | IsConj z x} ∩ (ASub S B : Set G)) := (hmemcl (n : G)).mp hn
  have h := key (g : G) g.2 (n : G) hn'
  rw [Subgroup.mem_subgroupOf]
  exact (hmemcl _).mpr h

theorem asc82Lemma710c_of (h36 : Asc82Lemma36) (hP : Asc82Tab6P) (h75b : Asc82Lemma75b)
    (h78 : Asc82Lemma78) (h710b : Asc82Lemma710b) : Asc82Lemma710c := by
  intro G _ _ t L S z g B hc
  exact ⟨(sec710_A_inf_L hP h78 hc).symm,
    sec710_B_eq_closure h36 hP h75b h78 h710b hc,
    sec710_B_normal_M h36 hP h75b h78 h710b hc⟩

end CFSG.OddStandard.SmallF3.Omega
