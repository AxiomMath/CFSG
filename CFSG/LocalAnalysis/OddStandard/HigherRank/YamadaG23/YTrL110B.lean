module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrL18Def
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrImg
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrSigA
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YAFacts

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma commutator_mul_right_of_commute {H : Type*} [Group H] {a b c : H}
    (hbc : Commute b c) (hac : Commute a c) : ⁅a, c * b⁆ = ⁅a, b⁆ := by
  rw [← hbc.eq, commutatorElement_mul_right_eq_mul_conj, Commute.commutator_eq hac, mul_one,
    mul_inv_cancel_right]

private theorem mem_sup_zL_A (s : Setting3 G L) {x : G}
    (hx : x ∈ (zL L : Subgroup G) ⊔ s.fr.A) :
    ∃ c ∈ zL L, ∃ b ∈ s.fr.A, x = c * b := by
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction (p := fun x _ => ∃ c ∈ zL L, ∃ b ∈ s.fr.A, x = c * b)
    ?_ ?_ ?_ ?_ hx
  · rintro x (hx | hx)
    · exact ⟨x, hx, 1, one_mem _, by simp⟩
    · exact ⟨1, one_mem _, x, hx, by simp⟩
  · exact ⟨1, one_mem _, 1, one_mem _, by simp⟩
  · rintro x y _ _ ⟨c₁, hc₁, b₁, hb₁, rfl⟩ ⟨c₂, hc₂, b₂, hb₂, rfl⟩
    have hb₁L : b₁ ∈ L := s3_S_le_L s (s3_A_le_S s hb₁)
    have hcz : c₂ ∈ centralizer (L : Set G) := (mem_zL_iff.mp hc₂).2
    have hbc : Commute b₁ c₂ := Subgroup.mem_centralizer_iff.mp hcz b₁ hb₁L
    exact ⟨c₁ * c₂, mul_mem hc₁ hc₂, b₁ * b₂, mul_mem hb₁ hb₂,
      hbc.mul_mul_mul_comm c₁ b₂⟩
  · rintro x _ ⟨c, hc, b, hb, rfl⟩
    have hbL : b ∈ L := s3_S_le_L s (s3_A_le_S s hb)
    have hcz : c ∈ centralizer (L : Set G) := (mem_zL_iff.mp hc).2
    have hbc : Commute b c := Subgroup.mem_centralizer_iff.mp hcz b hbL
    exact ⟨c⁻¹, inv_mem hc, b⁻¹, inv_mem hb, by rw [mul_inv_rev, hbc.inv_inv.eq]⟩

private theorem commutator_mem_Z_of_mem_A (hS : HRSetting G L)
    (hZ : Odd (Nat.card ↥(center ↥L))) (s : Setting3 G L) (h14 : s.fr'.Fact14) {a b : G}
    (ha : a ∈ s.fr.A) (hb : b ∈ s.fr.A) : ⁅a, b⁆ ∈ s.fr.Z := by
  haveI : Group.IsPerfect ↥L := isPerfect_of_hrSetting hS
  have hcab : ⁅a, b⁆ ∈ s.fr.A := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have haN : a ∈ normalizer (L : Set G) := s3_A_le_N s ha
  have hbN : b ∈ normalizer (L : Set G) := s3_A_le_N s hb
  have hα : jHom L ⟨a, haN⟩ ∈ s.fr'.A := by
    rw [← s3_jSub_A s]
    exact (mem_jSub (L := L)).mpr ⟨a, ha, jHom_actsAs L ⟨a, haN⟩⟩
  have hβ : jHom L ⟨b, hbN⟩ ∈ s.fr'.A := by
    rw [← s3_jSub_A s]
    exact (mem_jSub (L := L)).mpr ⟨b, hb, jHom_actsAs L ⟨b, hbN⟩⟩
  have hZ' : ⁅jHom L ⟨a, haN⟩, jHom L ⟨b, hbN⟩⁆ ∈ s.fr'.Z :=
    (A_facts s.fr' h14).2.1 _ hα _ hβ
  have hact : ActsAs L ⁅a, b⁆ ⁅jHom L ⟨a, haN⟩, jHom L ⟨b, hbN⟩⁆ := by
    have h := actsAs_mul L
      (actsAs_mul L (actsAs_mul L (jHom_actsAs L ⟨a, haN⟩) (jHom_actsAs L ⟨b, hbN⟩))
        (actsAs_inv L (jHom_actsAs L ⟨a, haN⟩)))
      (actsAs_inv L (jHom_actsAs L ⟨b, hbN⟩))
    simpa only [commutatorElement_def] using h
  have hZL : ⁅jHom L ⟨a, haN⟩, jHom L ⟨b, hbN⟩⁆ ∈ jSub L s.fr.Z := by
    rw [s3_jSub_Z s]
    exact hZ'
  have hx2 : IsPGroup 2 ↥(zpowers ⁅a, b⁆) := s3_isPGroup_zpowers s (s3_A_le_S s hcab)
  exact (mem_jSub_iff_mem (L := L) hZ
    (s3_Z_le_A s |>.trans (s3_A_le_S s) |>.trans (s3_S_le_L s))
    (s3_isPGroup_of_le s (s3_Z_le_A s |>.trans (s3_A_le_S s)))
    (s3_S_le_L s (s3_A_le_S s hcab)) hx2 hact).mp hZL

private theorem subset_lf110 (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (s : Setting3 G L) {g : G} (hg2 : g ^ 2 = 1) (hg : ActsAs L g s.fr'.σ)
    {V : Subgroup G} (hVA : V ≤ s.fr.A) :
    ((zL L ⊔ s.fr.A : Subgroup G) : Set G) ⊆
      {x : G | x ∈ L ⊔ closure {g} ∧ ∀ v ∈ V, ⁅v, x⁆ ∈ s.fr.Z} := by
  haveI : Group.IsPerfect ↥L := isPerfect_of_hrSetting hS
  have h14 : s.fr'.Fact14 := s.facts.2.2.2.1
  intro x hx
  obtain ⟨c, hc, b, hb, rfl⟩ := mem_sup_zL_A s hx
  refine ⟨?_, ?_⟩
  · exact Subgroup.mem_sup_left (L.mul_mem (zL_le hc) (s3_S_le_L s (s3_A_le_S s hb)))
  · intro v hv
    have hbL : b ∈ L := s3_S_le_L s (s3_A_le_S s hb)
    have hcz : c ∈ centralizer (L : Set G) := (mem_zL_iff.mp hc).2
    have hvc : Commute v c :=
      Subgroup.mem_centralizer_iff.mp hcz v (s3_S_le_L s (s3_A_le_S s (hVA hv)))
    have hbc : Commute b c := Subgroup.mem_centralizer_iff.mp hcz b hbL
    rw [commutator_mul_right_of_commute hbc hvc]
    exact commutator_mem_Z_of_mem_A hS hZ s h14 (hVA hv) hb

private theorem lf110_forward (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (hOut : (innerAut (L ⧸ center L)).index = 2) (s : Setting3 G L) {g : G} (hg2 : g ^ 2 = 1)
    (hg : ActsAs L g s.fr'.σ) {V : Subgroup G} (hVA : V ≤ s.fr.A)
    {V' : Subgroup (MulAut (L ⧸ center L))} (hV_eq : jSub L V = V')
    (hclause : ∀ x : MulAut (L ⧸ center L),
      x ∈ innerAut (L ⧸ center L) ⊔ closure {s.fr'.σ} →
      (∀ a ∈ V', ⁅a, x⁆ ∈ s.fr'.Z) → x ∈ s.fr'.A) :
    ∀ x : G, x ∈ L ⊔ closure {g} → (∀ v ∈ V, ⁅v, x⁆ ∈ s.fr.Z) → x ∈ zL L ⊔ s.fr.A := by
  haveI : Group.IsPerfect ↥L := isPerfect_of_hrSetting hS
  intro x hx hxcomm
  have hgn : g ∈ normalizer (L : Set G) := mem_normalizer_of_actsAs L hg
  have hN : L ⊔ closure {g} ≤ normalizer (L : Set G) := s3_Vg_le_normalizer (L := L) hgn
  have hxN : x ∈ normalizer (L : Set G) := hN hx
  let ξ : MulAut (L ⧸ center L) := jHom L ⟨x, hxN⟩
  have hxξ : ActsAs L x ξ := jHom_actsAs L ⟨x, hxN⟩
  have hgN : closure ({g} : Set G) ≤ normalizer (L : Set G) := by
    rw [Subgroup.closure_le]
    rintro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact hgn
  have hjcl : jSub L (closure ({g} : Set G)) = closure {s.fr'.σ} := by
    rw [jSub_closure_of_actsAs (L := L) ({g} : Set G)
      (fun y hy => by rw [Set.mem_singleton_iff] at hy; rw [hy]; exact hgn) (fun _ => s.fr'.σ)
      (fun y hy => by rw [Set.mem_singleton_iff] at hy; rw [hy]; exact hg)]
    simp
  have hξsup : ξ ∈ innerAut (L ⧸ center L) ⊔ closure {s.fr'.σ} := by
    have hmem : ξ ∈ jSub L (L ⊔ closure ({g} : Set G)) := (mem_jSub (L := L)).mpr ⟨x, hx, hxξ⟩
    rwa [jSub_sup (L := L) Subgroup.le_normalizer hgN, jSub_self L, hjcl] at hmem
  have hξA : ξ ∈ s.fr'.A := by
    refine hclause ξ hξsup ?_
    intro a ha
    have ha' : a ∈ jSub L V := by rw [hV_eq]; exact ha
    obtain ⟨a₀, ha₀V, ha₀a⟩ := (mem_jSub (L := L)).mp ha'
    have hact : ActsAs L ⁅a₀, x⁆ ⁅a, ξ⁆ := by
      have h := actsAs_mul L (actsAs_mul L (actsAs_mul L ha₀a hxξ) (actsAs_inv L ha₀a))
        (actsAs_inv L hxξ)
      simpa only [commutatorElement_def] using h
    rw [← s3_jSub_Z s]
    exact (mem_jSub (L := L)).mpr ⟨⁅a₀, x⁆, hxcomm a₀ ha₀V, hact⟩
  have hξA' : ξ ∈ jSub L s.fr.A := by rw [s3_jSub_A s]; exact hξA
  obtain ⟨a₁, ha₁A, ha₁ξ⟩ := (mem_jSub (L := L)).mp hξA'
  have hact1 : ActsAs L (a₁⁻¹ * x) 1 := by
    have h := actsAs_mul L (actsAs_inv L ha₁ξ) hxξ
    simpa using h
  have hcx : a₁⁻¹ * x ∈ centralizer (L : Set G) := (actsAs_one_iff L).mp hact1
  have hxsup : a₁⁻¹ * x ∈ L ⊔ closure {g} :=
    mul_mem (Subgroup.mem_sup_left (L.inv_mem (s3_S_le_L s (s3_A_le_S s ha₁A)))) hx
  have hz : a₁⁻¹ * x ∈ zL L := s3_kernel_Vg hS hOut s hg2 hg hxsup hcx
  have hx_eq : x = a₁ * (a₁⁻¹ * x) := by group
  rw [hx_eq]
  exact mul_mem (Subgroup.mem_sup_right ha₁A) (Subgroup.mem_sup_left hz)

theorem lf110_2_of (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (hOut : (innerAut (L ⧸ center L)).index = 2) (s : Setting3 G L) {g : G} (hg2 : g ^ 2 = 1)
    (hg : ActsAs L g s.fr'.σ) : LF110_2 s g := by
  obtain ⟨_, _, _, _, _, _, _, _, _, h110⟩ := s.facts
  unfold LF110_2
  apply Set.Subset.antisymm
  · rintro x ⟨hx, hxcomm⟩
    exact lf110_forward hS hZ hOut s hg2 hg (V := s.fr.A) (le_refl s.fr.A)
      (V' := s.fr'.A) (s3_jSub_A s)
      (fun y hy hc => by
        change y ∈ (s.fr'.A : Set (MulAut (L ⧸ center L)))
        rw [← h110.1.2.1]
        exact ⟨hy, hc⟩)
      x hx hxcomm
  · exact subset_lf110 hS hZ s hg2 hg (V := s.fr.A) (le_refl s.fr.A)

theorem lf110_3_of (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (hOut : (innerAut (L ⧸ center L)).index = 2) (s : Setting3 G L) {g : G} (hg2 : g ^ 2 = 1)
    (hg : ActsAs L g s.fr'.σ) : LF110_3 s g := by
  obtain ⟨_, _, _, _, _, _, _, _, _, h110⟩ := s.facts
  unfold LF110_3
  apply Set.Subset.antisymm
  · rintro x ⟨hx, hxcomm⟩
    exact lf110_forward hS hZ hOut s hg2 hg (V := s.fr.E ⊔ s.fr.F)
      (sup_le (s3_E_le_A s) (s3_F_le_A s)) (V' := s.fr'.E ⊔ s.fr'.F) (s3_jSub_EF hS hZ s)
      (fun y hy hc => by
        change y ∈ (s.fr'.A : Set (MulAut (L ⧸ center L)))
        rw [← h110.1.2.2]
        exact ⟨hy, hc⟩)
      x hx hxcomm
  · exact subset_lf110 hS hZ s hg2 hg (V := s.fr.E ⊔ s.fr.F)
      (sup_le (s3_E_le_A s) (s3_F_le_A s))

end CFSG.OddStandard.HigherRank.YamadaG23
