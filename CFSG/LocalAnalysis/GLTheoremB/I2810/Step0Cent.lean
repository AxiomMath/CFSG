module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.Step0Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.ThreeSubgroups

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810

section Cent

theorem s0_quasisimple_normal_dichotomy {Q : Type*} [Group Q] (h : CFSG.IsQuasisimple Q)
    (M : Subgroup Q) [M.Normal] : M ≤ Subgroup.center Q ∨ M = ⊤ := by
  obtain ⟨hperf, hsimple, -⟩ := h
  rcases hsimple.eq_bot_or_eq_top_of_normal (M.map (QuotientGroup.mk' (Subgroup.center Q))) with h0 | h1
  · left
    intro x hx
    have : QuotientGroup.mk' (Subgroup.center Q) x ∈ (⊥ : Subgroup (Q ⧸ Subgroup.center Q)) :=
      h0 ▸ ⟨x, hx, rfl⟩
    exact (QuotientGroup.eq_one_iff x).mp (Subgroup.mem_bot.mp this)
  · right
    have hMZ : M ⊔ Subgroup.center Q = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center Q)) M
      rw [h1, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hle : commutator Q ≤ M := by
      have e : commutator Q = ⁅M ⊔ Subgroup.center Q, M ⊔ Subgroup.center Q⁆ := by rw [hMZ]; rfl
      rw [e]
      have hn : (M ⊔ Subgroup.center Q).Normal := by rw [hMZ]; infer_instance
      rw [Subgroup.commutator_sup_right, Subgroup.commutator_center_left, sup_bot_eq,
        Subgroup.commutator_sup_left, Subgroup.commutator_center_right, sup_bot_eq]
      exact Subgroup.commutator_le_left M M
    rw [hperf.commutator_eq_top] at hle
    exact top_le_iff.mp hle

end Cent

section Main
variable {X : Type} [Group X] {W K S : Subgroup X} [W.Normal]

theorem s0_N_le_normalizer_K (h : Setup28 W K S) : K ⊔ S ≤ Subgroup.normalizer (K : Set X) :=
  sup_le Subgroup.le_normalizer h.hN

abbrev s0CentN (W K S : Subgroup X) [W.Normal] : Subgroup X :=
  Subgroup.centralizer (vOf W K S : Set X) ⊓ (K ⊔ S)

theorem s0_conj_mem_centN (h : Setup28 W K S) {n c : X} (hn : n ∈ K ⊔ S) (hc : c ∈ s0CentN W K S) :
    n * c * n⁻¹ ∈ s0CentN W K S := by
  refine ⟨Subgroup.mem_centralizer_iff.2 fun v hv => ?_,
    (K ⊔ S).mul_mem ((K ⊔ S).mul_mem hn hc.2) ((K ⊔ S).inv_mem hn)⟩
  have hv' := (s0_v_props_aux h).2.2 n⁻¹ ((K ⊔ S).inv_mem hn) v hv
  rw [inv_inv] at hv'
  have hcv := Subgroup.mem_centralizer_iff.1 hc.1 _ hv'
  calc v * (n * c * n⁻¹) = n * ((n⁻¹ * v * n) * c) * n⁻¹ := by group
    _ = n * (c * (n⁻¹ * v * n)) * n⁻¹ := by rw [hcv]
    _ = n * c * n⁻¹ * v := by group

theorem s0_comm_mem_K_centN (h : Setup28 W K S) {c k : X} (hc : c ∈ s0CentN W K S) (hk : k ∈ K) :
    ⁅c, k⁆ ∈ K ⊓ s0CentN W K S := by
  refine ⟨?_, ?_⟩
  · have h1 : ⁅c, k⁆ = (c * k * c⁻¹) * k⁻¹ := by simp only [commutatorElement_def]
    rw [h1]
    exact K.mul_mem ((Subgroup.mem_normalizer_iff.1 (s0_N_le_normalizer_K h hc.2) k).1 hk)
      (K.inv_mem hk)
  · have h1 : ⁅c, k⁆ = c * (k * c⁻¹ * k⁻¹) := by simp only [commutatorElement_def]; group
    rw [h1]
    exact (s0CentN W K S).mul_mem hc
      (s0_conj_mem_centN h (Subgroup.mem_sup_left hk) ((s0CentN W K S).inv_mem hc))

theorem s0_inf_centN_comm_le_W (h : Setup28 W K S) (hq : IsQuasisimple ↥(bar W K))
    (hnt : ¬ K ≤ Subgroup.centralizer (vOf W K S : Set X)) :
    ∀ x ∈ K ⊓ s0CentN W K S, ∀ k' ∈ K, ⁅x, k'⁆ ∈ W := by
  obtain ⟨hsurj, hker⟩ := toBar_props W K
  set M : Subgroup ↥(bar W K) := ((K ⊓ s0CentN W K S).subgroupOf K).map (toBar W K) with hM
  have hMn : M.Normal := by
    refine ⟨fun y hy g => ?_⟩
    obtain ⟨m, hm, rfl⟩ := hy
    obtain ⟨k₀, rfl⟩ := hsurj g
    refine ⟨k₀ * m * k₀⁻¹, ?_, by simp [map_mul, map_inv]⟩
    have hm' : (m : X) ∈ K ⊓ s0CentN W K S := hm
    show ((k₀ * m * k₀⁻¹ : ↥K) : X) ∈ K ⊓ s0CentN W K S
    refine ⟨(k₀ * m * k₀⁻¹ : ↥K).2, ?_⟩
    exact s0_conj_mem_centN h (Subgroup.mem_sup_left k₀.2) hm'.2
  rcases s0_quasisimple_normal_dichotomy hq M with hc | htop
  · intro x hx k' hk'
    have hmem : toBar W K ⟨x, hx.1⟩ ∈ M := ⟨⟨x, hx.1⟩, hx, rfl⟩
    exact ((zPre_iff_center ⟨x, hx.1⟩).2 (hc hmem)).2 k' hk'
  · exfalso
    apply hnt
    intro k hk
    have hkM : toBar W K ⟨k, hk⟩ ∈ M := htop ▸ Subgroup.mem_top _
    obtain ⟨m, hm, hmk⟩ := hkM
    have hm' : (m : X) ∈ K ⊓ s0CentN W K S := hm
    have h1 : toBar W K (⟨k, hk⟩ * m⁻¹) = 1 := by
      rw [map_mul, map_inv, ← hmk]; simp
    have hW : k * (m : X)⁻¹ ∈ W := (hker _).1 h1
    have hWc : k * (m : X)⁻¹ ∈ Subgroup.centralizer (vOf W K S : Set X) :=
      s0_kerAct_le_centralizer_V (s0_w_le_kerAct h hW)
    have : k = (k * (m : X)⁻¹) * m := by group
    rw [this]
    exact (Subgroup.centralizer (vOf W K S : Set X)).mul_mem hWc hm'.2.1

theorem s0_cent_comm_aux (h : Setup28 W K S) (hq : IsQuasisimple ↥(bar W K))
    (hnt : ¬ K ≤ Subgroup.centralizer (vOf W K S : Set X)) :
    ∀ c ∈ K ⊔ S, (∀ v ∈ vOf W K S, c * v = v * c) → ∀ k ∈ K, ⁅c, k⁆ ∈ W := by
  intro c hc hcv k hk
  have hcC : c ∈ s0CentN W K S := ⟨Subgroup.mem_centralizer_iff.2 fun v hv => (hcv v hv).symm, hc⟩
  have hA := s0_inf_centN_comm_le_W h hq hnt
  have hB : ⁅⁅s0CentN W K S, K⁆, K⁆ ≤ W := by
    rw [Subgroup.commutator_le]
    intro g hg k' hk'
    refine hA g ?_ k' hk'
    exact (Subgroup.commutator_le.2 fun c' hc' k'' hk'' => s0_comm_mem_K_centN h hc' hk'') hg
  have hC : ⁅⁅K, s0CentN W K S⁆, K⁆ ≤ W := by
    rw [Subgroup.commutator_comm K]; exact hB
  have h3 := CFSG.SignalizerFunctorTheorem.McBride.three_subgroups_lemma_normal
    (X := K) (Y := s0CentN W K S) (Z := K) (N := W) hC hB
  rw [h.hK.2.1, Subgroup.commutator_comm] at h3
  exact h3 (Subgroup.commutator_mem_commutator hcC hk)

end Main

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810
