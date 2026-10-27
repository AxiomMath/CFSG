module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.Api

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810

section Basic
variable {X : Type} [Group X] {W K S : Subgroup X} [W.Normal]

theorem s0_le_pCore_of_normal {G : Type*} [Group G] {p : ℕ} (N : Subgroup G) [N.Normal]
    (hN : IsPGroup p N) : N ≤ CFSG.pCore p G :=
  le_sSup ⟨inferInstance, hN⟩

theorem s0_w_le_kerAct (h : Setup28 W K S) : W ≤ kerAct W K S := fun w hw =>
  ⟨h.hWS hw, fun k _ => by
    have h1 : ⁅w, k⁆ = w * (k * w⁻¹ * k⁻¹) := by simp only [commutatorElement_def]; group
    rw [h1]
    exact W.mul_mem hw (Subgroup.Normal.conj_mem inferInstance _ (W.inv_mem hw) k)⟩

theorem s0_kerAct_le_S : kerAct W K S ≤ S := fun s hs => hs.1

theorem s0_o2K_aux (h : Setup28 W K S) : pCoreOf 2 K = K ⊓ W := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    have hnorm : ((CFSG.pCore 2 ↥K).map (toBar W K)).Normal :=
      (CFSG.pCore_normal).map _ (toBar_props W K).1
    have hP : IsPGroup 2 ↥((CFSG.pCore 2 ↥K).map (toBar W K)) := CFSG.pCore_isPGroup.map _
    have hle : (CFSG.pCore 2 ↥K).map (toBar W K) ≤ CFSG.pCore 2 ↥(bar W K) :=
      s0_le_pCore_of_normal _ hP
    rw [h.hO] at hle
    have : toBar W K y ∈ (⊥ : Subgroup _) := hle ⟨y, hy, rfl⟩
    exact ((toBar_props W K).2 y).1 (Subgroup.mem_bot.1 this)
  · intro x hx
    have hP : IsPGroup 2 ↥(W.subgroupOf K) := h.hW.comap_of_injective K.subtype K.subtype_injective
    have hle : W.subgroupOf K ≤ CFSG.pCore 2 ↥K := s0_le_pCore_of_normal _ hP
    exact ⟨⟨x, hx.1⟩, hle hx.2, rfl⟩

theorem s0_kerAct_conj_of_mem {n w : X} (hn : n ∈ Subgroup.normalizer (K : Set X))
    (hw : w ∈ kerAct W K S) (hnwS : n * w * n⁻¹ ∈ S) : n * w * n⁻¹ ∈ kerAct W K S := by
  refine ⟨hnwS, fun k hk => ?_⟩
  have hk' : n⁻¹ * k * n ∈ K := (Subgroup.mem_normalizer_iff''.1 hn k).1 hk
  have h1 : ⁅n * w * n⁻¹, k⁆ = n * ⁅w, n⁻¹ * k * n⁆ * n⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [h1]
  exact Subgroup.Normal.conj_mem inferInstance _ (hw.2 _ hk') n

theorem s0_w1_nrm_aux (h : Setup28 W K S) :
    ∀ n ∈ K ⊔ S, ∀ w ∈ kerAct W K S, n * w * n⁻¹ ∈ kerAct W K S := by
  have hKn : K ≤ Subgroup.normalizer (K : Set X) := Subgroup.le_normalizer
  have hK : ∀ n ∈ K, ∀ w ∈ kerAct W K S, n * w * n⁻¹ ∈ kerAct W K S := by
    intro n hn w hw
    refine s0_kerAct_conj_of_mem (hKn hn) hw ?_
    have h1 : n * w * n⁻¹ = (⁅w, n⁆)⁻¹ * w := by
      rw [commutatorElement_inv]
      simp only [commutatorElement_def]; group
    rw [h1]
    exact S.mul_mem (h.hWS (W.inv_mem (hw.2 n hn))) hw.1
  have hS : ∀ n ∈ S, ∀ w ∈ kerAct W K S, n * w * n⁻¹ ∈ kerAct W K S := by
    intro n hn w hw
    exact s0_kerAct_conj_of_mem (h.hN hn) hw (S.mul_mem (S.mul_mem hn hw.1) (S.inv_mem hn))
  have hnorm : K ⊔ S ≤ Subgroup.normalizer (kerAct W K S : Set X) := by
    refine sup_le (fun n hn => ?_) (fun n hn => ?_)
    · rw [Subgroup.mem_normalizer_iff]
      intro w
      exact ⟨fun hw => hK n hn w hw, fun hw => by
        have := hK n⁻¹ (K.inv_mem hn) _ hw
        have e : n⁻¹ * (n * w * n⁻¹) * n⁻¹⁻¹ = w := by group
        rwa [e] at this⟩
    · rw [Subgroup.mem_normalizer_iff]
      intro w
      exact ⟨fun hw => hS n hn w hw, fun hw => by
        have := hS n⁻¹ (S.inv_mem hn) _ hw
        have e : n⁻¹ * (n * w * n⁻¹) * n⁻¹⁻¹ = w := by group
        rwa [e] at this⟩
  intro n hn w hw
  exact (Subgroup.mem_normalizer_iff.1 (hnorm hn) w).1 hw

theorem s0_k_w1_aux (h : Setup28 W K S) : K ⊓ kerAct W K S = K ⊓ W := by
  apply le_antisymm
  · intro x hx
    have hnrm : ((kerAct W K S).subgroupOf K).Normal := by
      refine ⟨fun m hm k => ?_⟩
      have hm' : (m : X) ∈ kerAct W K S := hm
      show ((k * m * k⁻¹ : ↥K) : X) ∈ kerAct W K S
      exact s0_w1_nrm_aux h _ (Subgroup.mem_sup_left k.2) _ hm'
    have hP : IsPGroup 2 ↥((kerAct W K S).subgroupOf K) :=
      (h.hS.to_le (s0_kerAct_le_S (W := W) (K := K) (S := S))).comap_of_injective K.subtype K.subtype_injective
    have hle : (kerAct W K S).subgroupOf K ≤ CFSG.pCore 2 ↥K := s0_le_pCore_of_normal _ hP
    have : x ∈ pCoreOf 2 K := ⟨⟨x, hx.1⟩, hle hx.2, rfl⟩
    rwa [s0_o2K_aux h] at this
  · exact inf_le_inf_left K (s0_w_le_kerAct h)

theorem s0_v_props_aux (h : Setup28 W K S) :
    IsElemAbelian 2 (vOf W K S) ∧ vOf W K S ≤ kerAct W K S ∧
      ∀ n ∈ K ⊔ S, ∀ v ∈ vOf W K S, n * v * n⁻¹ ∈ vOf W K S := by
  refine ⟨⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩, fun v hv => hv.1, fun n hn v hv => ?_⟩
  · exact Subtype.ext (x.2.2.1 _ y.2.1)
  · exact hx.2.2
  · have hn' : n⁻¹ ∈ K ⊔ S := (K ⊔ S).inv_mem hn
    refine ⟨s0_w1_nrm_aux h n hn v hv.1, fun w hw => ?_, ?_⟩
    · have hw' := s0_w1_nrm_aux h n⁻¹ hn' w hw
      rw [inv_inv] at hw'
      have hc := hv.2.1 _ hw'
      calc n * v * n⁻¹ * w = n * (v * (n⁻¹ * w * n)) * n⁻¹ := by group
        _ = n * ((n⁻¹ * w * n) * v) * n⁻¹ := by rw [hc]
        _ = w * (n * v * n⁻¹) := by group
    · have h2 := hv.2.2
      calc (n * v * n⁻¹) ^ 2 = n * v ^ 2 * n⁻¹ := by simp only [pow_two]; group
        _ = 1 := by rw [h2]; group

theorem s0_K_ne_bot (h : Setup28 W K S) : K ≠ ⊥ := by
  intro hK
  have hq := h.hK.2.2.2.2
  rw [hK, Subgroup.map_bot] at hq
  haveI := hq.2.toNontrivial
  obtain ⟨a, b, hab⟩ := exists_pair_ne (↥(⊥ : Subgroup (X ⧸ CFSG.pCore 2 X)) ⧸
    Subgroup.center ↥(⊥ : Subgroup (X ⧸ CFSG.pCore 2 X)))
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  exact hab (by rw [Subsingleton.elim x y])

theorem s0_S_ne_bot (h : Setup28 W K S) : S ≠ ⊥ := by
  intro hS
  apply s0_K_ne_bot h
  have hW : W = ⊥ := le_bot_iff.1 (hS ▸ h.hWS)
  have hX : ∀ x : X, x = 1 := fun x => by
    have hx : x ∈ Subgroup.centralizer (W : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have hg' : g ∈ W := hg
      rw [hW, Subgroup.mem_bot] at hg'
      rw [hg']; simp
    have := h.hC hx
    rw [hW] at this
    exact Subgroup.mem_bot.1 this
  exact eq_bot_iff.2 fun x _ => Subgroup.mem_bot.2 (hX x)

theorem s0_vOf_le_S (h : Setup28 W K S) : vOf W K S ≤ S := fun v hv => hv.1.1

theorem s0_kerAct_le_centralizer_V : kerAct W K S ≤ Subgroup.centralizer (vOf W K S : Set X) := by
  intro w hw
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact hv.2.1 w hw

theorem s0_omegaZ_eq_quasithin (T : Subgroup X) : omegaZ T = quasithinOmegaOneCenter T := by
  apply le_antisymm
  · intro v hv
    exact Subgroup.subset_closure ⟨Subgroup.mem_inf.2 ⟨hv.1, Subgroup.mem_centralizer_iff.2
      fun w hw => (hv.2.1 w hw).symm⟩, hv.2.2⟩
  · refine (Subgroup.closure_le _).2 fun z hz => ?_
    obtain ⟨hzI, hz2⟩ := hz
    exact ⟨(Subgroup.mem_inf.1 hzI).1, fun w hw =>
      (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hzI).2 w hw).symm, hz2⟩

end Basic

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810
