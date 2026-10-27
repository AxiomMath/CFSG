module

public import CFSG.GH74.Generic.S45.LVert
public import CFSG.GH74.Generic.S45.LPumpG
public import CFSG.GH74.Generic.S45.PumpC2

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.Blueprint Subgroup

theorem b_S45_pumpup_of_leaves_g4_vert (hK : B_S45_KFacts) (hS : B_S45_pumpStructV) (h13 : B_III11_13_10_g4)
    (h63 : B_III8_6_3) (h21 : B_III11_2_1) (hJ2 : B_IA_5_3g) : B_S45_pumpup := by
  intro G _ _ hs hn hgen hKGH x hx K hKc hj hnot T hT
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨v, hvR, hv1⟩ : ∃ v ∈ T ⊓ Pre x K, v ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have h8 := hT.R_card
    have : T ⊓ Pre x K = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hcon
    rw [this, Subgroup.card_bot] at h8
    omega
  have hvT : v ∈ T := hvR.1
  have hvK : v ∈ Pre x K := hvR.2
  have hv2 : v * v = 1 := hT.sq v hvT
  have hvord : orderOf v = 2 := orderOf_eq_prime (by rw [pow_two]; exact hv2) hv1
  have hTv : T ≤ centralizer ({v} : Set G) := fun t ht => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hT.comm t ht v hvT
  have hxv : x ∈ centralizer ({v} : Set G) := hTv hT.x_mem
  obtain ⟨W, hWY, hWn, hWs, hWnab, hWL, Jb, hJb0, hWJb⟩ :=
    hS G hs hn hgen hKGH x hx K hKc hj hnot T hT v hvT hvK hv1
  obtain ⟨hE4, c, hcW, hcN, hc1⟩ := hT.exists_normalizing_in_W hvT hvK hv1 W hWY hWn hWs hWnab
  obtain ⟨e, heE, he1⟩ : ∃ e ∈ T ⊓ W, e ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have h1 : T ⊓ W = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hcon
    rw [h1, Subgroup.card_bot] at hE4
    omega
  have he2 : e * e = 1 := hT.sq e heE.1
  have hWH : W ≤ centralizer ({v} : Set G) := fun w hw => (Subgroup.mem_inf.1 (hWY hw)).2
  obtain ⟨J, hWJ, hJH, hbJ⟩ := exists_J_of_vertical hWH hWJb
  have hJb : IsComponent (barSub v J) := by rw [hbJ]; exact hJb0
  obtain ⟨φ, hφ⟩ := barSub_mulEquiv hWH hWs heE.2 he2 he1
  have hWbs : IsSimpleGroup ↥(barSub v W) := @MulEquiv.isSimpleGroup _ _ _ _ hWs φ.symm
  have hWbnab : ∃ a b : ↥(barSub v W), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hWnab
    exact ⟨φ a, φ b, fun h1 => hab (φ.injective (by rw [map_mul, map_mul]; exact h1))⟩
  have hWbL : HasL2Model ↥(barSub v W) Odd :=
    CFSG.GH74.GLS.TwoThin.hasL2Model_of_mulEquiv φ hWL
  have hcent := hT.exists_two_central hvT hvK hv1
  have hnoRee : ¬ IsJ1OrRee ↥(barSub v J) := fun hj' =>
    not_isJ1OrRee_of_central hK hs hn hgen hvord hcent hJb hj'
  obtain ⟨hxv', hxcomm⟩ := h63 G hs hn x hx T hT.sylow v hvT (fun p hp => hT.comm p hp v hvT) hvord
    hcent (fun g hg _ => hT.controls_fusion hvT hvK hv1 g hg)
  have hxc : proj v ⟨x, hxv⟩ ∈ commutator (CentralizerBar v) := by
    have h1 : proj v ⟨x, hxv⟩ ∈ (commutator ↥(centralizer ({v} : Set G))).map (proj v) :=
      ⟨⟨x, hxv⟩, hxcomm, rfl⟩
    have h2 : (commutator ↥(centralizer ({v} : Set G))).map (proj v) ≤
        commutator (CentralizerBar v) := by
      rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator]
      exact Subgroup.commutator_mono le_top le_top
    exact h2 h1
  have hx2' : proj v ⟨x, hxv⟩ * proj v ⟨x, hxv⟩ = 1 := by
    rw [← map_mul]
    have h1 : (⟨x, hxv⟩ * ⟨x, hxv⟩ : ↥(centralizer ({v} : Set G))) = 1 :=
      Subtype.ext (hT.sq x hT.x_mem)
    rw [h1, map_one]
  have hWx : barSub v W ≤ centralizer ({proj v ⟨x, hxv⟩} : Set (CentralizerBar v)) := by
    intro w hw
    obtain ⟨w₀, hw₀, hw₀W, rfl⟩ := mem_barSub.1 hw
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hWY hw₀W)).1
  have hWbn : ((barSub v W).subgroupOf
      (centralizer ({proj v ⟨x, hxv⟩} : Set (CentralizerBar v)))).Normal := by
    constructor
    intro n hn g
    have hn' : (n : CentralizerBar v) ∈ barSub v W := hn
    obtain ⟨n₀, hn₀, hn₀W, hnn⟩ := mem_barSub.1 hn'
    have hgc : (g : CentralizerBar v) * proj v ⟨x, hxv⟩ =
        proj v ⟨x, hxv⟩ * (g : CentralizerBar v) :=
      Subgroup.mem_centralizer_singleton_iff.1 g.2
    obtain ⟨g₁, hg₁, hg₁p⟩ := proj_cent v (u := ⟨x, hxv⟩)
      (by apply Subtype.ext; exact hT.sq x hT.x_mem) (g : CentralizerBar v) hgc
    have hg₁x : (g₁ : G) ∈ centralizer ({x} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val hg₁
    have hg₁Y : (g₁ : G) ∈ centralizer ({x} : Set G) ⊓ centralizer ({v} : Set G) :=
      Subgroup.mem_inf.2 ⟨hg₁x, g₁.2⟩
    have hn₀Y : n₀ ∈ centralizer ({x} : Set G) ⊓ centralizer ({v} : Set G) := hWY hn₀W
    have hconj := hWn.conj_mem
      (⟨n₀, hn₀Y⟩ : ↥(centralizer ({x} : Set G) ⊓ centralizer ({v} : Set G))) hn₀W
      ⟨(g₁ : G), hg₁Y⟩
    have hgnW : (g₁ : G) * n₀ * (g₁ : G)⁻¹ ∈ W := hconj
    have hmem : (g₁ : G) * n₀ * (g₁ : G)⁻¹ ∈ centralizer ({v} : Set G) :=
      mul_mem (mul_mem g₁.2 hn₀) (inv_mem g₁.2)
    have heq : (g : CentralizerBar v) * (n : CentralizerBar v) * (g : CentralizerBar v)⁻¹ =
        proj v ⟨(g₁ : G) * n₀ * (g₁ : G)⁻¹, hmem⟩ := by
      rw [← hg₁p, ← hnn]
      have h1 : (⟨(g₁ : G) * n₀ * (g₁ : G)⁻¹, hmem⟩ : ↥(centralizer ({v} : Set G))) =
          g₁ * ⟨n₀, hn₀⟩ * g₁⁻¹ := rfl
      rw [h1, map_mul, map_mul, map_inv]
    show (g : CentralizerBar v) * (n : CentralizerBar v) * (g : CentralizerBar v)⁻¹ ∈ barSub v W
    rw [heq]
    exact proj_mem_barSub hmem hgnW
  have hEcomm : ∀ a ∈ barSub v (T ⊓ W), ∀ b ∈ barSub v (T ⊓ W), a * b = b * a := by
    intro a ha b hb
    obtain ⟨a₀, ha₀, ha₀E, rfl⟩ := mem_barSub.1 ha
    obtain ⟨b₀, hb₀, hb₀E, rfl⟩ := mem_barSub.1 hb
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hT.comm a₀ ha₀E.1 b₀ hb₀E.1
  have hEsq : ∀ a ∈ barSub v (T ⊓ W), a * a = 1 := by
    intro a ha
    obtain ⟨a₀, ha₀, ha₀E, rfl⟩ := mem_barSub.1 ha
    rw [← map_mul]
    have h1 : (⟨a₀, ha₀⟩ * ⟨a₀, ha₀⟩ : ↥(centralizer ({v} : Set G))) = 1 :=
      Subtype.ext (hT.sq a₀ ha₀E.1)
    rw [h1, map_one]
  have hEcard : 4 ≤ Nat.card ↥(barSub v (T ⊓ W)) := by
    refine hE4.trans (Nat.card_le_card_of_injective
      (fun a : ↥(T ⊓ W) => (⟨proj v ⟨(a : G), hTv a.2.1⟩,
        proj_mem_barSub (hTv a.2.1) a.2⟩ : ↥(barSub v (T ⊓ W)))) ?_)
    intro a b hab
    exact Subtype.ext (hT.eq_of_proj_eq a.2.1 b.2.1 (hTv a.2.1) (hTv b.2.1)
      (congrArg Subtype.val hab))
  have hKP : IsKProperSimple G := ⟨hs, hn, kProper_of_kgh hKGH⟩
  have hJK2 : InCalK2 ↥(barSub v J) := CFSG.GH74.GLS.inCalK2_of_isComponent hKP hvord hJb
  exact pump_tail_g4 (gen4_centralizerBar hgen v) h13 h21 hJ2 (z := xbar v)
    (x' := proj v ⟨x, hxv⟩) (xbar_comm v) (xbar_mul_self hvord) (xbar_ne_one hvord) hx2' hxc
    (fun P hP hPc => hT.two_subgroup_elementary hvT hxv P hP hPc)
    hJb hJK2 (barSub_mono hWJ) (barSub_mono inf_le_right) hWbs hWbnab hWbL hWx hWbn hEcomm hEsq
    hEcard hnoRee (hT.not_barSub_le_centralizer hvT hvK hv1 hxv hWJ hJH hJb.2 hcW hcN hc1)

theorem s_shapeCase_S4_of_pumpLeaves_g4_vert
    (hS : B_S45_pumpStructV) (h13 : B_III11_13_10_g4)
    (h63 : B_III8_6_3) (h21 : B_III11_2_1) (hJ2 : B_IA_5_3g) : S_shapeCaseMaxNT @ShapeS4 :=
  s_shapeCase_S4_of_pumpup (b_S45_pumpup_of_leaves_g4_vert b_S45_KFacts hS h13 h63 h21 hJ2)

theorem s_shapeCase_S5_of_pumpLeaves_g4_vert
    (hS : B_S45_pumpStructV) (h13 : B_III11_13_10_g4)
    (h63 : B_III8_6_3) (h21 : B_III11_2_1) (hJ2 : B_IA_5_3g) : S_shapeCaseMaxNT @ShapeS5 :=
  s_shapeCase_S5_of_pumpup (b_S45_pumpup_of_leaves_g4_vert b_S45_KFacts hS h13 h63 h21 hJ2)

end CFSG.GH74.Generic.S45
