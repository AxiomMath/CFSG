module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppDK6
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppC56A5
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L2_4_27
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.GammaLemmas
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.SetupAt
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraConfining
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Basic

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.AppD Equiv

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {s : G}

@[expose] noncomputable def gcfgOf (h : A3A3 T M H S L s) (sp : A3x.Spec h) : GCfg T M H S L :=
  { hcs := h.cs
    U := blockU L ⊔ blockU2 L s
    hUdef := (A3x.hUeq h).symm
    P := A3x.piS sp
    hB := A3x.piS_im_B sp
    hS := A3x.piS_im_S sp
    hUQ := A3x.U_le_Q (h := h)
    hQ := A3x.hQ_cent h
    hUD := A3x.U_inf_D h
    hQeq := A3x.Q_eq sp
    hU1 := le_sup_left }

section Normalizer

variable (h : A3A3 T M H S L s)
include h

theorem conjR_le_H : conjR L s ≤ H := by
  have h1 : conjR L s ≤ conjJoin S L := by rw [h.join]; exact le_sup_right
  have h2 : conjJoin S L ≤ H := by rw [h.cs.eq_join]; exact le_sup_left
  exact h1.trans h2

theorem Ls_comm_L {l a : G} (hl : l ∈ conjR L s) (ha : a ∈ L) : l * a = a * l := by
  have h1 : ⁅L, conjR L s⁆ = ⊥ := h.comm
  have h2 : L ≤ Subgroup.centralizer ((conjR L s : Subgroup G) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1
  exact (Subgroup.mem_centralizer_iff.mp (h2 ha) l hl)

theorem Ls_comm_U₁ {l u : G} (hl : l ∈ conjR L s) (hu : u ∈ blockU L) : l * u = u * l :=
  Ls_comm_L h hl ((IsA4Block.of_alt3 h.cs.block.1.1 h.a3).le hu)

end Normalizer

omit [Finite G] in
theorem Ls_le_normalizer_U₂ : conjR L s ≤ Subgroup.normalizer (blockU2 L s : Set G) := by
  intro l hl
  refine mem_normalizer_conj_of ?_
  have hmem : s * l * s⁻¹ ∈ L := mem_conjR.mp hl
  exact C1.mem_normalizer_blockU (Subgroup.le_normalizer hmem)

section Generic

variable {C : GCfg T M H S L} {x : G} {M₀ : Subgroup G} (m : GMate S T M₀ x) (F : GFour C x)

omit m in
theorem v_sq : F.v * F.v = 1 := by
  have := GMate.V_sq (x := x) C F.hv
  simpa [pow_two] using this

omit m in
theorem v_inv : F.v⁻¹ = F.v := inv_eq_of_mul_eq_one_right (v_sq F)

include m

theorem W_eq : F.Y ⊔ pCoreOf 2 H = pCoreOf 2 H ⊔ Subgroup.zpowers F.v := by
  have hvY : F.v ∈ F.Y := by
    show F.v ∈ GYv C.U (blockD S L) F.v
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers F.v)
  apply le_antisymm
  · refine sup_le ?_ le_sup_left
    intro y hy
    obtain ⟨a, haQ, hya⟩ := m.Yv_decomp C F.hv hy
    rcases hya with rfl | rfl
    · exact Subgroup.mem_sup_left haQ
    · exact mul_mem (Subgroup.mem_sup_left haQ) (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  · refine sup_le le_sup_right ?_
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_sup_left hvY

theorem v_mem_W : F.v ∈ F.Y ⊔ pCoreOf 2 H := by
  rw [W_eq m F]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers F.v)

omit m in
theorem v_not_mem_Q : F.v ∉ pCoreOf 2 H := by
  intro hv
  have h1 := C.pf_eq_one_of_mem_Q hv
  rw [F.hπ] at h1
  exact absurd h1 (by decide)

theorem card_Q_lt_W : Nat.card ↥(pCoreOf 2 H) < Nat.card ↥(F.Y ⊔ pCoreOf 2 H) := by
  have hle : pCoreOf 2 H ≤ F.Y ⊔ pCoreOf 2 H := le_sup_right
  refine lt_of_le_of_ne (Subgroup.card_le_of_le hle) fun heq => ?_
  have := Subgroup.eq_of_le_of_card_ge hle heq.ge
  exact v_not_mem_Q F (this ▸ v_mem_W m F)

theorem W_le_S : F.Y ⊔ pCoreOf 2 H ≤ S :=
  sup_le (m.Yv_isMax C F.hv F.hπ).1.1 C.hQS

theorem mem_normalizer_W {l : G} (hlH : l ∈ H) (h1 : l * F.v * l⁻¹ * F.v⁻¹ ∈ pCoreOf 2 H)
    (h2 : l⁻¹ * F.v * l * F.v⁻¹ ∈ pCoreOf 2 H) :
    l ∈ Subgroup.normalizer ((F.Y ⊔ pCoreOf 2 H : Subgroup G) : Set G) := by
  have hWeq := W_eq m F
  have key : ∀ l ∈ H, l * F.v * l⁻¹ * F.v⁻¹ ∈ pCoreOf 2 H →
      ∀ w ∈ F.Y ⊔ pCoreOf 2 H, l * w * l⁻¹ ∈ F.Y ⊔ pCoreOf 2 H := by
    intro l hl hc
    have hNQ : l ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
      CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H hl
    let K' : Subgroup G := (F.Y ⊔ pCoreOf 2 H).comap (MulAut.conj l).toMonoidHom
    have hQK : pCoreOf 2 H ≤ K' := by
      intro q hq
      show l * q * l⁻¹ ∈ F.Y ⊔ pCoreOf 2 H
      have : l * q * l⁻¹ ∈ pCoreOf 2 H := (Subgroup.mem_normalizer_iff.mp hNQ q).mp hq
      exact Subgroup.mem_sup_right this
    have hvK : Subgroup.zpowers F.v ≤ K' := by
      rw [Subgroup.zpowers_le]
      show l * F.v * l⁻¹ ∈ F.Y ⊔ pCoreOf 2 H
      have e : l * F.v * l⁻¹ = (l * F.v * l⁻¹ * F.v⁻¹) * F.v := by group
      rw [e]
      exact mul_mem (Subgroup.mem_sup_right hc) (v_mem_W m F)
    have hW : F.Y ⊔ pCoreOf 2 H ≤ K' := by
      rw [hWeq]
      exact sup_le hQK hvK
    exact fun w hw => hW hw
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · exact key l hlH h1 w
  · intro hw
    have h2' : l⁻¹ * F.v * l⁻¹⁻¹ * F.v⁻¹ ∈ pCoreOf 2 H := by rwa [inv_inv]
    have := key l⁻¹ (inv_mem hlH) h2' _ hw
    have e : l⁻¹ * (l * w * l⁻¹) * l⁻¹⁻¹ = w := by group
    rwa [e] at this

end Generic

section Ws

variable (h : A3A3 T M H S L s) (sp : A3x.Spec h) {x : G} {M₀ : Subgroup G} (m : GMate S T M₀ x)
  (F : GFour (gcfgOf h sp) x)
include h sp m F

theorem v_lab (i : Fin 5) : F.v * A3x.lab sp i * F.v⁻¹ = A3x.lab sp (swap 0 1 i) := by
  have hvS : F.v ∈ S := m.V_le_S (gcfgOf h sp) F.hv
  have h1 := A3x.piS_spec sp ⟨F.v, hvS⟩ i
  have h0 : (A3x.piS sp).pf F.v = swap 0 1 := F.hπ
  rw [(A3x.piS sp).pf_eq hvS] at h0
  rw [h0] at h1
  exact h1

theorem v_comm_U₂ {u : G} (hu : u ∈ blockU2 L s) : F.v * u = u * F.v := by
  have hy2 : F.v * sp.y₂ * F.v⁻¹ = sp.y₂ := by
    have := v_lab h sp m F 2
    rw [A3x.lab_two] at this
    rw [this]
    have e : (swap (0 : Fin 5) 1) 2 = 2 := by decide
    rw [e, A3x.lab_two]
  have hy2z : F.v * (sp.y₂ * sp.z₂) * F.v⁻¹ = sp.y₂ * sp.z₂ := by
    have := v_lab h sp m F 3
    rw [A3x.lab_three] at this
    rw [this]
    have e : (swap (0 : Fin 5) 1) 3 = 3 := by decide
    rw [e, A3x.lab_three]
  have hz2 : F.v * sp.z₂ * F.v⁻¹ = sp.z₂ := by
    have e : F.v * sp.z₂ * F.v⁻¹ =
        (F.v * sp.y₂ * F.v⁻¹)⁻¹ * (F.v * (sp.y₂ * sp.z₂) * F.v⁻¹) := by group
    rw [e, hy2, hy2z]
    group
  have hc : F.v * u * F.v⁻¹ = u := by
    rcases sp.kp.elems₂ u hu with rfl | rfl | rfl | rfl
    · group
    · exact hz2
    · exact hy2
    · exact hy2z
  calc F.v * u = (F.v * u * F.v⁻¹) * F.v := by group
    _ = u * F.v := by rw [hc]

theorem v_conj_U₁ {u : G} (hu : u ∈ blockU L) : F.v * u * F.v⁻¹ ∈ blockU L := by
  have hy1 : F.v * sp.y₁ * F.v⁻¹ = sp.y₁ * sp.z₁ := by
    have := v_lab h sp m F 0
    rw [A3x.lab_zero] at this
    rw [this]
    have e : (swap (0 : Fin 5) 1) 0 = 1 := by decide
    rw [e, A3x.lab_one]
  have hy1z : F.v * (sp.y₁ * sp.z₁) * F.v⁻¹ = sp.y₁ := by
    have := v_lab h sp m F 1
    rw [A3x.lab_one] at this
    rw [this]
    have e : (swap (0 : Fin 5) 1) 1 = 0 := by decide
    rw [e, A3x.lab_zero]
  have hy1m : sp.y₁ ∈ blockU L := sp.kp.hy₁
  have hz1m : sp.z₁ ∈ blockU L := sp.kp.hz₁
  rcases sp.kp.elems₁ u hu with rfl | rfl | rfl | rfl
  · simp
  · have e : F.v * sp.z₁ * F.v⁻¹ =
        (F.v * sp.y₁ * F.v⁻¹)⁻¹ * (F.v * (sp.y₁ * sp.z₁) * F.v⁻¹) := by group
    rw [e, hy1, hy1z]
    exact mul_mem (inv_mem (mul_mem hy1m hz1m)) hy1m
  · rw [hy1]; exact mul_mem hy1m hz1m
  · rw [hy1z]; exact hy1m

theorem comm_mem_Q {l : G} (hl : l ∈ conjR L s) :
    l * F.v * l⁻¹ * F.v⁻¹ ∈ pCoreOf 2 H := by
  have hlH : l ∈ H := conjR_le_H h hl
  have hvS : F.v ∈ S := m.V_le_S (gcfgOf h sp) F.hv
  have hvH : F.v ∈ H := (gcfgOf h sp).hSH hvS
  have hcH : l * F.v * l⁻¹ * F.v⁻¹ ∈ H :=
    mul_mem (mul_mem (mul_mem hlH hvH) (inv_mem hlH)) (inv_mem hvH)
  have hvinv := v_inv F
  have hv2 := v_sq F
  have hl₂ : l⁻¹ ∈ conjR L s := inv_mem hl
  have h1 : blockU L ≤ Subgroup.centralizer {l * F.v * l⁻¹ * F.v⁻¹} := by
    intro u hu
    rw [Subgroup.mem_centralizer_singleton_iff]
    symm
    have hu' : F.v * u * F.v⁻¹ ∈ blockU L := v_conj_U₁ h sp m F hu
    set u' := F.v * u * F.v⁻¹ with hu'def
    have hvu : F.v * u = u' * F.v := by rw [hu'def]; group
    have hvu' : F.v * u' = u * F.v := by
      rw [hu'def, hvinv]
      calc F.v * (F.v * u * F.v) = (F.v * F.v) * u * F.v := by group
        _ = u * F.v := by rw [hv2]; group
    have hl1 : l⁻¹ * u' = u' * l⁻¹ := Ls_comm_U₁ h hl₂ hu'
    have hl2 : l * u = u * l := Ls_comm_U₁ h hl hu
    rw [hvinv]
    calc l * F.v * l⁻¹ * F.v * u = l * F.v * l⁻¹ * (F.v * u) := by group
      _ = l * F.v * l⁻¹ * (u' * F.v) := by rw [hvu]
      _ = l * F.v * (l⁻¹ * u') * F.v := by group
      _ = l * F.v * (u' * l⁻¹) * F.v := by rw [hl1]
      _ = l * (F.v * u') * l⁻¹ * F.v := by group
      _ = l * (u * F.v) * l⁻¹ * F.v := by rw [hvu']
      _ = (l * u) * F.v * l⁻¹ * F.v := by group
      _ = (u * l) * F.v * l⁻¹ * F.v := by rw [hl2]
      _ = u * (l * F.v * l⁻¹ * F.v) := by group
  have h2 : blockU2 L s ≤ Subgroup.centralizer {l * F.v * l⁻¹ * F.v⁻¹} := by
    intro u hu
    rw [Subgroup.mem_centralizer_singleton_iff]
    symm
    have hu'' : l⁻¹ * u * l ∈ blockU2 L s := by
      have := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (blockU2 L s : Set G)).inv_mem (Ls_le_normalizer_U₂ hl)) u).mp hu
      simpa using this
    set u'' := l⁻¹ * u * l with hu''def
    have hvu : F.v * u = u * F.v := v_comm_U₂ h sp m F hu
    have hvu'' : F.v * u'' = u'' * F.v := v_comm_U₂ h sp m F hu''
    have hlu : l⁻¹ * u = u'' * l⁻¹ := by rw [hu''def]; group
    rw [hvinv]
    calc l * F.v * l⁻¹ * F.v * u = l * F.v * l⁻¹ * (F.v * u) := by group
      _ = l * F.v * l⁻¹ * (u * F.v) := by rw [hvu]
      _ = l * F.v * (l⁻¹ * u) * F.v := by group
      _ = l * F.v * (u'' * l⁻¹) * F.v := by rw [hlu]
      _ = l * (F.v * u'') * l⁻¹ * F.v := by group
      _ = l * (u'' * F.v) * l⁻¹ * F.v := by rw [hvu'']
      _ = (l * u'') * F.v * l⁻¹ * F.v := by group
      _ = (u * l) * F.v * l⁻¹ * F.v := by rw [hu''def]; group
      _ = u * (l * F.v * l⁻¹ * F.v) := by group
  have hcU : l * F.v * l⁻¹ * F.v⁻¹ ∈ Subgroup.centralizer ((gcfgOf h sp).U : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hu' : u ∈ blockU L ⊔ blockU2 L s := hu
    have : u ∈ Subgroup.centralizer {l * F.v * l⁻¹ * F.v⁻¹} :=
      (sup_le h1 h2 : blockU L ⊔ blockU2 L s ≤ _) hu'
    exact Subgroup.mem_centralizer_singleton_iff.mp this
  rw [← (gcfgOf h sp).hQ]
  exact ⟨hcH, hcU⟩

theorem Ls_le_normalizer_W :
    conjR L s ≤ Subgroup.normalizer ((F.Y ⊔ pCoreOf 2 H : Subgroup G) : Set G) := fun l hl =>
  mem_normalizer_W m F (conjR_le_H h hl) (comm_mem_Q h sp m F hl)
    (by simpa using comm_mem_Q h sp m F (inv_mem hl))

end Ws

section Core

variable {T M H S L : Subgroup G} {s : G}

@[expose, reducible] def Wgrp {C : GCfg T M H S L} {x : G} (F : GFour C x) : Subgroup G :=
  F.Y ⊔ pCoreOf 2 H

@[expose, reducible] def Ggrp {C : GCfg T M H S L} {x : G} (F : GFour C x) : Subgroup G :=
  Subgroup.normalizer (Wgrp F : Set G)

theorem A3A3.not_Ls_le_M (h : A3A3 T M H S L s) : ¬ conjR L s ≤ M := by
  intro hle
  apply h.cs.not_le
  have h1 : conjSubgroup (conjSubgroup L s) s⁻¹ ≤ conjSubgroup M s⁻¹ :=
    C5.conjSubgroup_mono hle s⁻¹
  have e : conjSubgroup (conjSubgroup L s) s⁻¹ = L := C5.conjSubgroup_conjSubgroup_inv L s
  have hsM : s ∈ Subgroup.normalizer (M : Set G) :=
    Subgroup.le_normalizer (h.cs.setting.le (h.cs.le_T h.s_mem))
  rw [e, C5.conjSubgroup_eq_self (inv_mem hsM)] at h1
  exact h1

@[expose] def A5BlockS1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), ConstrainedSetting G T M H S L →
    IsAltType L 5 → conjJoin S L = L

theorem isMaxElemAbelian_pCoreOf {T M H S L : Subgroup G} (hcs : ConstrainedSetting G T M H S L)
    (hcase : (IsAltType L 5 ∧ conjJoin S L = L) ∨ (IsAltType L 3 ∧ conjJoin S L ≠ L)) :
    IsMaxElemAbelian S (pCoreOf 2 H) := by
  obtain ⟨M₀, hSM, hMT, h2⟩ := C56.exists_index_two hcs
  rcases hcase with ⟨h5, hj⟩ | ⟨h3, hne⟩
  · obtain ⟨-, -, -, -, hmax, -, -⟩ := AppC.c56A5Case G T M H S L hcs h5 hj M₀ hSM hMT h2
    exact hmax
  · obtain ⟨-, -, -, -, hmax, -, -⟩ := AppD.c56DoubleA3 G T M H S L hcs h3 hne M₀ hSM hMT h2
    exact hmax

variable (hSA : ConstrainedSetupAt) (hlin : Lin2BlockExcluded) (ha3 : SingleA3Excluded)
  (h25 : A5BlockS1)
include hSA hlin ha3 h25

theorem false_of_ne_normT
    {C : GCfg T M H S L} {x : G} {M₀ : Subgroup G} (m : GMate S T M₀ x)
    (hne : M₀ ≠ T) (F : GFour C x) (hXM : ¬ Ggrp F ≤ M) : False := by
  have hcs := C.hcs
  have hT2 : IsPGroup 2 ↥T := hcs.setting.isPGroup
  have hcardN : Nat.card S ≤ Nat.card ↥(T ⊓ Ggrp F) :=
    m.card_normalizer_pair C F hT2 hne (i := 2) (by decide)
  have hWS : Wgrp F ≤ S := W_le_S m F
  have hWT : Wgrp F ≤ T := hWS.trans hcs.le_T
  have hW2 : IsPGroup 2 ↥(Wgrp F) := hT2.to_le hWT
  have hvW : F.v ∈ Wgrp F := v_mem_W m F
  have hv1 : F.v ≠ 1 := fun h1 => v_not_mem_Q F (h1 ▸ one_mem _)
  have hWne : Wgrp F ≠ ⊥ := fun hb => hv1 (Subgroup.mem_bot.mp (hb ▸ hvW))
  have hTbot : T ≠ ⊥ := fun hb => hcs.ne_T (le_antisymm (hb ▸ hcs.le_T) (hb ▸ bot_le))
  obtain ⟨z, hzT, hz1, hzc⟩ := exists_central_of_normal hTbot le_rfl Subgroup.le_normalizer hT2
  have hzcent : z ∈ Subgroup.centralizer (T : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun t ht => hzc t ht
  have hzQ : z ∈ pCoreOf 2 H := by
    have hzS : z ∈ S := hcs.center_le ⟨hzT, hzcent⟩
    refine hcs.charTwo ⟨hcs.sylow.le hzS, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
    exact hzc q (hcs.le_T (C.hQS hq))
  have hWZ : Wgrp F ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) ≠ ⊥ := by
    intro hbot
    have hzmem : z ∈ Wgrp F ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) :=
      ⟨Subgroup.mem_sup_right hzQ, hzT, hzcent⟩
    rw [hbot] at hzmem
    exact hz1 (Subgroup.mem_bot.mp hzmem)
  have hct : CharTwo (Ggrp F) :=
    charTwo_normalizer_of_inf_center hcs.setting.qtke.2.1 hcs.setting.sylow hW2 hWZ
  have hWcore : Wgrp F ≤ pCoreOf 2 (Ggrp F) :=
    le_pCoreOf_of_normalizes Subgroup.le_normalizer le_rfl hW2
  have hpc : pCoreOf 2 (Ggrp F) ≠ ⊥ := fun hb => hWne (le_bot_iff.mp (hb ▸ hWcore))
  have hRX : baum S ≤ Ggrp F := fun b hb =>
    mem_normalizer_sup_of (m.B_le_normalizer_Y C F.hv F.hπ hb) (C.S_le_normalizer_Q hb.1)
  have hbJ : baum S = thompsonJ S := (m.J_eq_B C).symm
  have hRS : baum S ≤ S := inf_le_left
  have hSidx : (baum S).relIndex S = 2 := by
    have h1 := C5.card_eq_card_mul_relIndex hRS
    have h2 := m.card_S_eq C
    have hpos : 0 < Nat.card ↥(baum S) := Nat.card_pos
    have h3 : Nat.card ↥(baum S) * 2 = Nat.card ↥(baum S) * (baum S).relIndex S := by
      rw [← h1, h2]; ring
    exact (Nat.eq_of_mul_eq_mul_left hpos h3).symm
  have hC : pCoreOf 2 M ⊓ Subgroup.centralizer (baum S : Set G) ≤ baum S :=
    hcs.gamma0.pCore_centralizer_le_of_charTwo hcs.setting hcs.sylow_inf hcs.charTwo (m.Q_le_B C)
  have hconf : IsConfining M (baum S) :=
    hcs.gamma0.isConfining_of_relIndex_two hcs.setting hcs.sylow_inf hbJ.ge hRS hSidx hC
  have hpair : IsWitnessPair M (baum S) (Ggrp F) := ⟨hconf, hRX, hpc, hct, hXM⟩
  have hTX2 : IsPGroup 2 ↥(T ⊓ Ggrp F) := hT2.to_le inf_le_left
  have hle : twoPart H ≤ twoPart (Ggrp F) := by
    calc twoPart H = Nat.card S := hcs.sylow.card_eq.symm
      _ ≤ Nat.card ↥(T ⊓ Ggrp F) := hcardN
      _ ≤ twoPart (Ggrp F) := card_le_twoPart inf_le_right hTX2
  obtain ⟨heq, hΓ0, -, -⟩ :=
    IsGamma0.of_isWitnessPair_of_twoPart_le hcs.setting hcs.gamma0 hpair hle
  have hcardTX : Nat.card ↥(T ⊓ Ggrp F) = twoPart (Ggrp F) := by
    have h1 := card_le_twoPart (inf_le_right : T ⊓ Ggrp F ≤ Ggrp F) hTX2
    have h2 : Nat.card S = twoPart H := hcs.sylow.card_eq
    omega
  have hSylXM : IsSylowTwoOf (T ⊓ Ggrp F) (Ggrp F ⊓ M) := by
    have hle1 : T ⊓ Ggrp F ≤ Ggrp F ⊓ M :=
      le_inf inf_le_right (inf_le_left.trans hcs.setting.le)
    have h1 : twoPart (Ggrp F ⊓ M) ≤ twoPart (Ggrp F) := twoPart_mono inf_le_left
    have h2 : Nat.card ↥(T ⊓ Ggrp F) ≤ twoPart (Ggrp F ⊓ M) := card_le_twoPart hle1 hTX2
    exact isSylowTwoOf_of_card_eq hle1 hTX2 (by omega)
  obtain ⟨P, L', hPX, hcs'⟩ := hSA G T M (Ggrp F) (T ⊓ Ggrp F) hcs.setting hcs.notBender
    hcs.notSmall hΓ0 hct hSylXM inf_le_left
  have hcase : (IsAltType L' 5 ∧ conjJoin (T ⊓ Ggrp F) L' = L') ∨
      (IsAltType L' 3 ∧ conjJoin (T ⊓ Ggrp F) L' ≠ L') := by
    rcases hcs'.block.2 with ⟨n, hn, hlin2⟩ | h3 | h5
    · exact (hlin G T M P _ L' hcs' n hn hlin2).elim
    · by_cases hj : conjJoin (T ⊓ Ggrp F) L' = L'
      · exact (ha3 G T M P _ L' hcs' h3 hj).elim
      · exact Or.inr ⟨h3, hj⟩
    · exact Or.inl ⟨h5, h25 G T M P _ L' hcs' h5⟩
  have hmax := isMaxElemAbelian_pCoreOf hcs' hcase
  have hWP : Wgrp F ≤ P :=
    (le_inf hWT Subgroup.le_normalizer : Wgrp F ≤ T ⊓ Ggrp F).trans hcs'.sylow.le
  have hWcoreP : Wgrp F ≤ pCoreOf 2 P := le_pCoreOf_of_normalizes hWP hPX hW2
  have hWe : IsElemAbelian 2 (Wgrp F) := B2F.isElemAbelian_mono hWcoreP hmax.2.1
  have hQmax := m.Q_isMax C
  have h1 := hQmax.2.2 (Wgrp F) hWS hWe
  have h2 : Nat.card ↥(pCoreOf 2 H) < Nat.card ↥(Wgrp F) := card_Q_lt_W m F
  omega

end Core

section A3Main

variable (hSA : ConstrainedSetupAt) (hlin : Lin2BlockExcluded) (ha3 : SingleA3Excluded)
  (h25 : A5BlockS1)
include hSA hlin ha3 h25

theorem lemma2_4_27_1A3_of : Lemma2_4_27_1A3 := by
  intro G _ _ T M H S L hcs h3 hne
  obtain ⟨s, h⟩ := exists_A3A3 hcs h3 hne
  obtain ⟨sp⟩ := A3x.exists_spec h
  obtain ⟨M₀, hSM, hMT, h2⟩ := C56.exists_index_two hcs
  have hne' : S ≠ M₀ := by
    intro hh
    rw [← hh] at h2
    simp at h2
  obtain ⟨x₀, hx₀, hx₀S⟩ : ∃ x ∈ M₀, x ∉ S := by
    by_contra hcon
    push Not at hcon
    exact hne' (le_antisymm hSM hcon)
  have m : GMate S T M₀ x₀ := ⟨hSM, hMT, h2, hx₀, hx₀S⟩
  by_cases hTM : M₀ = T
  · refine ⟨?_, ?_, ?_⟩
    · rw [← hTM]; exact h2
    · exact (m.J_eq_B (gcfgOf h sp)).symm
    · rw [← hTM]; exact (thompsonJ_M₀_eq (gcfgOf h sp) hSM hMT h2).symm
  · obtain ⟨F⟩ := m.nonempty_four (gcfgOf h sp)
    exact (false_of_ne_normT hSA hlin ha3 h25 m hTM F fun hXM =>
      A3A3.not_Ls_le_M h ((Ls_le_normalizer_W h sp m F).trans hXM)).elim

end A3Main

end CFSG.QuasithinUnique.DoubleA3
