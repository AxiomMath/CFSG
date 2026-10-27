module

public import CFSG.GH74.GLS.C3.Layer1.Thm1P33f
public import CFSG.GH74.GLS.C3.Layer1.Th2T1RelBase
public import CFSG.GH74.GLS.C3.Layer1.Th2T1RelLeaves

public section

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.GLS.C3.Layer1.Thm1 CFSG.GH74.GLS.C3.Layer1.Thm1G33

namespace CFSG.GH74.GLS

theorem env33_of_rel
    (h2hb : IVK.IVK_1_2h_b) (h102 : B_ivk_10_2) (hL34 : B_gen4_noL34_elem)
    (hP31s : B_thm1_P31s_rel) (hP31c : B_thm1_P31c_rel) (hL32 : B_thm1_L32'_rel)
    {G : Type} [Group G] [Finite G] (hG : C3Hyp G) (hNo : NoV2Fine G)
    {x y : G} {K T V W : Subgroup G} {f z : G} (hyp : Hyp33 x y K T V W f z)
    (h5 : ¬ HasL2Model (kBar K) (fun q => q = 5)) :
    Env33 x y K T V W f z := by
  obtain ⟨cfg, hsup⟩ := hyp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hJc, hJn, r, hrodd, hr5, hI, hKshape, -, -⟩ := hL32 G hG hNo x y K f cfg.fmax h5
  have hshape := Thm1.kBar_model_of_U2 hG h102 hL34 cfg.hu2
  obtain ⟨hKN, hKuniq, -, hTdata⟩ := hP31s G hG hNo x y K cfg.hu2 hshape h5
  obtain ⟨-, ⟨n, hn3, hdih⟩, z₁, hz₁P, hz₁2, hz₁c, hz₁u⟩ := hTdata T cfg.setup
  have hz2 : orderOf z = 2 := cfg.z_mem.2.1
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz2; omega
  have hzu : ∀ w ∈ T ⊓ K, (∀ p ∈ T ⊓ K, w * p = p * w) → w = 1 ∨ w = z := by
    have hzz₁ : z = z₁ := by
      rcases hz₁u z cfg.z_mem.1 (fun p hp => (cfg.z_mem.2.2 p hp.1).symm) with h | h
      · exact absurd h hz1
      · exact h
    intro w hw hwc
    rcases hz₁u w hw hwc with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans hzz₁.symm)
  have hfC : f ∈ centralizer ({x} : Set G) := cfg.setup.sylowT.le cfg.mem.1
  have hfFaut : P34.IsFAutL2A7 (kBar K) (Back.actHom hKN ⟨f, hfC⟩) := by
    obtain ⟨hfN, hF⟩ := thm1_FmemberF_of_rel h2hb G hG hNo x y K cfg.hu2 hshape hKN T cfg.setup f
      cfg.mem h5
    exact hF
  obtain ⟨hcen, hAut⟩ := kBar_autData_rel h2hb hNo cfg.hu2 hshape h5
  exact ⟨cfg, hsup, hKN, hKuniq, cfg.setup.sylowT.inf_of_le_normalizer cfg.hKx
    (fun c hc => U1a.mem_normalizer_of_norm hKN hc), ⟨n, hn3, hdih⟩, hzu, hfC, hfFaut, hcen,
    hAut, card_le_two_of_noV2Fine hNo cfg.hu2 h5,
    autLevelC_of_shape hshape, hP31c G hG hNo x y K cfg.hu2 h5, hJc, hJn,
    ⟨r, hrodd, hr5, hI, hKshape⟩, hshape⟩


theorem b_thm1_L33c'_rel_proved
    (h2hb : IVK.IVK_1_2h_b) (h102 : B_ivk_10_2) (hL34 : B_gen4_noL34_elem)
    (hP31s : B_thm1_P31s_rel) (hP31c : B_thm1_P31c_rel) (hL32 : B_thm1_L32'_rel) : B_thm1_L33c'_rel := by
  intro G _ _ hG hNo x y K T V W f z hyp h8 hVW h5
  have E := env33_of_rel h2hb h102 hL34 hP31s hP31c hL32 hG hNo hyp h5
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b₀, hb₀W, hb₀N, hb₀V⟩ := exists_mem_normalizer_not_mem E.cfg.V_le_W hVW
    E.cfg.sylowW.isPGroup
  have hb₀2 : ∃ k : ℕ, b₀ ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := E.cfg.sylowW.isPGroup ⟨b₀, hb₀W⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  obtain ⟨c, hc, hcV, hc2⟩ := exists_pow_not_mem_sq_mem hb₀2 hb₀V
  have hcW : c ∈ W := (zpowers_le).2 hb₀W hc
  have hcN : c ∈ normalizer (V : Set G) := (zpowers_le).2 hb₀N hc
  obtain ⟨-, hcz, -, -⟩ := E.key_c h8 hcW hcN hcV hc2
  refine ⟨isConj_iff.2 ⟨c, hcz⟩, fun b hbW hbN hbV hb2 => ?_⟩
  obtain ⟨-, -, hDD', hcomm⟩ := E.key_c h8 hbW hbN hbV hb2
  exact ⟨E.zCenter_sup_zpowers h8 hbW hbN hbV hb2, hDD', hcomm⟩


theorem b_thm1_L33d_rel_proved
    (h2hb : IVK.IVK_1_2h_b) (h102 : B_ivk_10_2) (hL34 : B_gen4_noL34_elem)
    (hP31s : B_thm1_P31s_rel) (hP31c : B_thm1_P31c_rel) (hL32 : B_thm1_L32'_rel) : B_thm1_L33d_rel := by
  intro G _ _ hG hNo x y K T V W f z hyp hD4 hcond h5
  have E := env33_of_rel h2hb h102 hL34 hP31s hP31c hL32 hG hNo hyp h5
  have hxZ : x ∈ zCenter V := by
    by_contra hx
    rcases hcond with hVW | ⟨g, hgN, hg⟩
    · exact E.false_of_VW hD4 hx hVW
    · exact hx (E.key_d hD4 hgN hg)
  refine ⟨hxZ, ?_, E.hPD, E.hPcD4 hD4⟩
  apply le_antisymm
  · unfold omega1
    refine (Subgroup.closure_le _).2 ?_
    rintro u ⟨huV, huu⟩
    have hux : u * x = x * u := hxZ.2 u huV
    have := E.hOmega1S u huV hux huu
    show u ∈ (T ⊓ K) ⊔ secD K f V
    rwa [E.hDeq4 hD4]
  · refine sup_le ?_ ?_
    · intro p hp
      obtain ⟨n, -, hdih⟩ := E.hdih
      obtain ⟨u, hu, w, hw, huu, hww, hpuw⟩ := Thm1.exists_mul_involutions_of_dihedral hdih p hp
      rw [hpuw]
      exact (omega1 V).mul_mem (Subgroup.subset_closure ⟨E.hPV hu, huu⟩)
        (Subgroup.subset_closure ⟨E.hPV hw, hww⟩)
    · rw [E.hDeq4 hD4]
      exact sup_le ((zpowers_le).2 (Subgroup.subset_closure ⟨E.cfg.x_mem_V, E.hx2⟩))
        ((zpowers_le).2 (Subgroup.subset_closure ⟨E.cfg.f_mem_V, E.hf2'⟩))


theorem b_thm1_L33f_rel_proved
    (h2hb : IVK.IVK_1_2h_b) (h102 : B_ivk_10_2) (hL34 : B_gen4_noL34_elem)
    (hP31s : B_thm1_P31s_rel) (hP31c : B_thm1_P31c_rel) (hL32 : B_thm1_L32'_rel) : B_thm1_L33f_rel := by
  intro G _ _ hG hNo x y K T V W f z hyp hconj h5
  have E := env33_of_rel h2hb h102 hL34 hP31s hP31c hL32 hG hNo hyp h5
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hgN, hgf⟩ := E.exists_g hconj
  have h8 : 8 ≤ Nat.card ↥(secD K f V) := by
    rcases E.card_secD_cases with h4 | h8
    · exact (E.false_f_card4 h4 hgN hgf).elim
    · exact h8
  have hVW : V ≠ W := fun hVW => E.false_f_V_eq_W hG h8 hVW hgN hgf
  refine ⟨hVW, ?_⟩
  by_contra hA7
  obtain ⟨b₀, hb₀W, hb₀N, hb₀V⟩ := exists_mem_normalizer_not_mem E.cfg.V_le_W hVW
    E.cfg.sylowW.isPGroup
  have hb₀2 : ∃ k : ℕ, b₀ ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := E.cfg.sylowW.isPGroup ⟨b₀, hb₀W⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  obtain ⟨b, hb, hbV, hb2⟩ := exists_pow_not_mem_sq_mem hb₀2 hb₀V
  have hbW : b ∈ W := (zpowers_le).2 hb₀W hb
  have hbN : b ∈ normalizer (V : Set G) := (zpowers_le).2 hb₀N hb
  have hb2el : ∃ k : ℕ, b ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := E.cfg.sylowW.isPGroup ⟨b, hbW⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  obtain ⟨hbf, hbz, -, -⟩ := E.key_c h8 hbW hbN hbV hb2
  have hzf_comm : z * f = f * z := (E.hfP z E.hzP).symm
  have hX2 : IsPGroup 2 ↥(V ⊔ zpowers b) :=
    E.hV2.to_sup_of_normal_left' (C3.Layer1.Thm1.isPGroup_zpowers_of_pow_eq_one hb2el)
      ((zpowers_le).2 hbN)
  have hXC : V ⊔ zpowers b ≤ centralizer ({f * z} : Set G) := by
    refine sup_le ?_ ?_
    · intro v hv
      refine mem_centralizer_singleton_iff.2 ?_
      have h1 := E.hVf v hv
      have h2 : v * z = z * v := E.hzZ.2 v hv
      calc v * (f * z) = (v * f) * z := by group
        _ = (f * v) * z := by rw [h1]
        _ = f * (v * z) := by group
        _ = f * (z * v) := by rw [h2]
        _ = (f * z) * v := by group
    · rw [zpowers_le]
      refine mem_centralizer_singleton_iff.2 ?_
      calc b * (f * z) = (b * f * b⁻¹) * (b * z * b⁻¹) * b := by group
        _ = z * f * b := by rw [hbf, hbz]
        _ = f * z * b := by rw [hzf_comm]
  have hcardlt : Nat.card ↥V < Nat.card ↥(V ⊔ zpowers b) := by
    by_contra hnot
    push Not at hnot
    have heq := Subgroup.eq_of_le_of_card_ge (le_sup_left : V ≤ V ⊔ zpowers b) hnot
    exact hbV (heq ▸ Subgroup.mem_sup_right (mem_zpowers b))
  obtain ⟨S, hS⟩ := exists_isSylowOf 2 (centralizer ({f * z} : Set G))
  have hXS : Nat.card ↥(V ⊔ zpowers b) ≤ Nat.card ↥S :=
    Thm1L3.card_le_of_isPGroup_of_isSylowOf hX2 hXC hS
  have hFM3 := E.cfg.fmax
  have hFM2 : FMax2 x y K f := hFM3.1
  have hFM1 : FMax1 x y K f := hFM2.1
  obtain ⟨hfzT, hfz2, hfzc, hfzx⟩ := E.fz_basic
  have hlay := E.layer_fz_ne_bot hG hA7
  have hmem : IsFMember x K T (f * z) := ⟨hfzT, hfz2, hfzc, hfzx, hlay⟩
  have hFU2 : IsFU2 x y K (f * z) := ⟨E.cfg.hu2, T, E.cfg.setup, hmem⟩
  have hFM2' : FMax2 x y K (f * z) := ⟨⟨hFU2, hFM1.2⟩, hFM2.2⟩
  have hle := hFM3.2 x y K (f * z) hFM2'
  have hV_eq : twoPartCard (centralizer ({f} : Set G)) = Nat.card ↥V := by
    unfold twoPartCard
    exact E.cfg.sylowV.card_eq.symm
  have hS_eq : twoPartCard (centralizer ({f * z} : Set G)) = Nat.card ↥S := by
    unfold twoPartCard
    exact hS.card_eq.symm
  rw [hV_eq, hS_eq] at hle
  omega


end CFSG.GH74.GLS
