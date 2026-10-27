module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixTransport
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixClosure

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.SignalizerFunctor.Helpers
open CFSG.Open
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem normal_sup_of_frame {G T : Subgroup X} (hF : Frame G T) (htop : G ⊔ T = ⊤)
    (hT : IsMulCommutative T) (K : Subgroup X) : (G ⊔ K).Normal :=
  ⟨fun n hn x => by
    have h := commutator_mem_of_frame hF htop hT x n
    have : x * n * x⁻¹ = (x * n * x⁻¹ * n⁻¹) * n := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h) hn⟩

omit [Finite X] in
theorem inf_sup_eq_of_le {G T T₁ : Subgroup X} (hF : Frame G T) (hT₁ : T₁ ≤ T) :
    T ⊓ (G ⊔ T₁) = T₁ := by
  apply le_antisymm _ (le_inf hT₁ le_sup_right)
  rintro t ⟨ht, htG⟩
  have hT₁G : T₁ ≤ Subgroup.normalizer (G : Set X) := hT₁.trans hF.le_normalizer
  have hm : t ∈ (G : Set X) * (T₁ : Set X) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left G T₁ hT₁G]
    exact htG
  obtain ⟨h, hh, t₁, ht₁, rfl⟩ := Set.mem_mul.mp hm
  have hhT : h ∈ T := by simpa using T.mul_mem ht (T.inv_mem (hT₁ ht₁))
  have hh1 : h ∈ T ⊓ G := ⟨hhT, hh⟩
  rw [hF.inf_eq_bot, Subgroup.mem_bot] at hh1
  rw [hh1, one_mul]
  exact ht₁

theorem pRank_omegaOne (T : Subgroup X) : pRank 2 (omegaOne T) = pRank 2 T := by
  apply le_antisymm (CFSG.SectionRank.pRank_mono one_lt_two (omegaOne_le T))
  obtain ⟨E, hET, hE, hcard⟩ := CFSG.SectionRank.exists_pRank one_lt_two T
  exact CFSG.SectionRank.le_pRank one_lt_two
    ((le_omegaOne fun x hx => hE.2 x hx).trans (omegaOne_mono hET)) hE hcard

namespace Conf46

variable {G T S Q H : Subgroup X} {g : X}

theorem isSylowOf_omegaOne (c : Conf46 G T S Q H g) (htop : G ⊔ T = ⊤) :
    IsSylowOf 2 (omegaOne T) (Q ⊓ (G ⊔ omegaOne T)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn := normal_sup_of_frame c.frame htop c.isMulCommutative (omegaOne T)
  have h := c.hyp43.sylow.inf_of_le_normalizer (inf_le_left : Q ⊓ (G ⊔ omegaOne T) ≤ Q)
    (fun x _ => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer (by assumption), by
        rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top x⟩)
  rwa [← inf_assoc, inf_eq_left.mpr c.hyp43.le_Q,
    inf_sup_eq_of_le c.frame (omegaOne_le T)] at h

theorem hyp43_omegaOne (c : Conf46 G T S Q H g) (htop : G ⊔ T = ⊤) {G₁ : Subgroup X}
    (hG₁ : G₁ ≤ G) :
    Hyp43 G₁ (omegaOne T) (Q ⊓ (G₁ ⊔ omegaOne T)) (H ⊓ (G₁ ⊔ omegaOne T)) where
  le := inf_le_inf_right _ c.hyp43.le
  le_normalizer := fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
    ⟨c.hyp43.le_normalizer hx.1, Subgroup.le_normalizer hx.2⟩
  le_sup := inf_le_right
  sylow := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact (c.isSylowOf_omegaOne htop).of_le
      (le_inf ((omegaOne_le T).trans c.hyp43.le_Q) le_sup_right)
      (inf_le_inf_left _ (sup_le_sup_right hG₁ _))
  inf_eq_bot := fun n hn hnH => by
    have hnH' : n ∉ H := fun h => hnH ⟨h, Subgroup.mem_sup_left hn⟩
    rw [eq_bot_iff, ← c.hyp43.inf_eq_bot n (hG₁ hn) hnH']
    exact inf_le_inf (omegaOne_le T) (rightConjugate_le_rightConjugate (omegaOne_le T) n)

theorem omegaOne_Z_ne_bot (c : Conf46 G T S Q H g) :
    omegaOne ((T ⊔ rightConjugate T g) ⊓ G) ≠ ⊥ := by
  have hZ2 : IsPGroup 2 ((T ⊔ rightConjugate T g) ⊓ G : Subgroup X) :=
    c.isPGroup_S.to_le (inf_le_left.trans c.W_le_S)
  obtain ⟨z, hz, hz2, -⟩ := exists_center_involution hZ2 c.hyp45.W_inf_G_ne_bot
  intro hbot
  have hzO : z ∈ omegaOne ((T ⊔ rightConjugate T g) ⊓ G) :=
    mem_omegaOne hz (by rw [← hz2, pow_orderOf_eq_one])
  rw [hbot, Subgroup.mem_bot] at hzO
  rw [hzO, orderOf_one] at hz2
  omega

theorem exists_conf_omegaOne (c : Conf46 G T S Q H g) (htop : G ⊔ T = ⊤) {G₁ S₀ : Subgroup X}
    (hG₁ : G₁ ≤ G) (hUN : omegaOne T ≤ Subgroup.normalizer (G₁ : Set X))
    (hS₀ : IsSylowOf 2 S₀ (G₁ ⊔ omegaOne T)) (hS₀S : S₀ ≤ S) :
    ∃ S₁ : Subgroup X, SylowFrame G₁ (omegaOne T) S₁ ∧ ∃ y ∈ G₁ ⊔ omegaOne T, ∃ n ∈ G₁,
      relativeWeakClosure G₁ (omegaOne T) S₁ = omegaOne T ⊔ rightConjugate (omegaOne T) n ∧
      rightConjugate (omegaOne T) n ≤ Subgroup.normalizer (omegaOne T : Set X) ∧
      (relativeWeakClosure G₁ (omegaOne T) S₁ = omegaOne T ∨
        relativeWeakClosure G₁ (omegaOne T) S₁ =
          rightConjugate (omegaOne (T ⊔ rightConjugate T g)) y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := omegaOne T with hUdef
  set V := omegaOne (T ⊔ rightConjugate T g) with hVdef
  have hUT : U ≤ T := omegaOne_le T
  have hVab : IsMulCommutative V := isMulCommutative_of_le (omegaOne_le _) c.isMulCommutative_W
  have hWU : relativeWeakClosure G U S = V := c.weakClosure_omegaOne
  have hF₁ : Frame G₁ U := ⟨hUN, by
    rw [eq_bot_iff, ← c.frame.inf_eq_bot]; exact inf_le_inf hUT hG₁,
    c.frame.isPGroup.to_le hUT⟩
  obtain ⟨S₁, hS₁⟩ := hF₁.exists_sylowFrame
  have hUS₁ : U ≤ S₁ := hS₁.le
  obtain ⟨y, hyL, hy⟩ := exists_rightConjugate_eq_of_isSylowOf hS₁.sylow hS₀
  refine ⟨S₁, hS₁, y, hyL, ?_⟩
  have hkey : ∀ x ∈ G₁ ⊔ U, rightConjugate U x ≤ S₁ → rightConjugate U x ≤ rightConjugate V y := by
    intro x hx hle
    have hxy : x * y⁻¹ ∈ G₁ ⊔ U := (G₁ ⊔ U).mul_mem hx ((G₁ ⊔ U).inv_mem hyL)
    obtain ⟨t, ht, h, hh, -, hrc⟩ := hF₁.exists_rightConjugate_eq hxy
    have hS₀eq : rightConjugate S₁ y⁻¹ = S₀ := by
      rw [← hy, rightConjugate_mul, mul_inv_cancel, rightConjugate_one]
    have h1 : rightConjugate U (x * y⁻¹) ≤ S₀ := by
      rw [← rightConjugate_mul, ← hS₀eq]
      exact rightConjugate_le_rightConjugate hle y⁻¹
    rw [hrc] at h1
    have h3 : rightConjugate U h ≤ V := by
      rw [← hWU]
      exact rightConjugate_le_relativeWeakClosure (hG₁ hh) (h1.trans hS₀S)
    rw [← hrc] at h3
    have h4 := rightConjugate_le_rightConjugate h3 y
    rwa [rightConjugate_mul, inv_mul_cancel_right] at h4
  have hW₁V : relativeWeakClosure G₁ U S₁ ≤ rightConjugate V y := by
    rw [relativeWeakClosure_le_iff]
    exact fun x hx hle => hkey x (Subgroup.mem_sup_left hx) hle
  by_cases hall : ∀ n ∈ G₁, rightConjugate U n ≤ S₁ → rightConjugate U n = U
  · have hW₁ : relativeWeakClosure G₁ U S₁ = U := by
      apply le_antisymm _ (subgroup_le_relative_weak_closure _ _ _ hUS₁)
      rw [relativeWeakClosure_le_iff]
      exact fun x hx hle => (hall x hx hle).le
    refine ⟨1, G₁.one_mem, ?_, ?_, Or.inl hW₁⟩
    · rw [rightConjugate_one, sup_idem, hW₁]
    · rw [rightConjugate_one]
      exact Subgroup.le_normalizer
  · push Not at hall
    obtain ⟨n, hn, hle, hne⟩ := hall
    have hUV : U ≤ rightConjugate V y := hkey 1 (Subgroup.one_mem _) (by
      rw [rightConjugate_one]; exact hUS₁) |>.trans' (by rw [rightConjugate_one])
    have hUnV : rightConjugate U n ≤ rightConjugate V y := hkey n (Subgroup.mem_sup_left hn) hle
    have hVyab : IsMulCommutative (rightConjugate V y) := isMulCommutative_rightConjugate hVab y
    have hUnN : rightConjugate U n ≤ Subgroup.normalizer (U : Set X) := by
      refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
      intro x hx
      exact Subgroup.mem_centralizer_iff.mpr fun u hu => congrArg Subtype.val
        (hVyab.is_comm.comm ⟨u, hUV hu⟩ ⟨x, hUnV hx⟩)
    have hinf : U ⊓ rightConjugate U n = ⊥ := by
      by_contra hne'
      have hnH : n ∈ H := c.hyp43.mem_of_inf_ne_bot (hG₁ hn) fun hbot => hne' (by
        rw [eq_bot_iff, ← hbot]
        exact inf_le_inf hUT (rightConjugate_le_rightConjugate hUT n))
      have hGU := normal_sup_of_frame c.frame htop c.isMulCommutative U
      have hle₂ : U ⊔ rightConjugate U n ≤ Q ⊓ (G ⊔ U) := by
        refine sup_le (le_inf (hUT.trans c.hyp43.le_Q) le_sup_right) (le_inf ?_ ?_)
        · have h1 := rightConjugate_le_rightConjugate (hUT.trans c.hyp43.le_Q) n
          rwa [(rightConjugate_eq_self_iff Q n).mpr (c.hyp43.le_normalizer hnH)] at h1
        · have hnN : n ∈ Subgroup.normalizer ((G ⊔ U : Subgroup X) : Set X) := by
            rw [Subgroup.normalizer_eq_top_iff.mpr hGU]; exact Subgroup.mem_top n
          have h1 := rightConjugate_le_rightConjugate (le_sup_right : U ≤ G ⊔ U) n
          rwa [(rightConjugate_eq_self_iff (G ⊔ U) n).mpr hnN] at h1
      have h2 : IsPGroup 2 (U ⊔ rightConjugate U n : Subgroup X) :=
        (c.frame.isPGroup.to_le hUT).to_sup_of_normal_left'
          (isPGroup_rightConjugate (c.frame.isPGroup.to_le hUT) n) hUnN
      have hcard := card_le_of_isSylowOf (c.isSylowOf_omegaOne htop) h2 hle₂
      have heq : U ⊔ rightConjugate U n = rightConjugate U n :=
        (Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [rightConjugate_card]; exact hcard)).symm
      apply hne
      exact (Subgroup.eq_of_le_of_card_ge (heq ▸ le_sup_left) (by rw [rightConjugate_card])).symm
    have hcardUU : Nat.card (U ⊔ rightConjugate U n : Subgroup X) = Nat.card U * Nat.card U := by
      rw [card_sup_of_le_normalizer hUnN hinf, rightConjugate_card]
    have hW₁ : relativeWeakClosure G₁ U S₁ = rightConjugate V y := by
      apply le_antisymm hW₁V
      calc rightConjugate V y = U ⊔ rightConjugate U n := by
            refine (Subgroup.eq_of_le_of_card_ge (sup_le hUV hUnV) ?_).symm
            rw [rightConjugate_card, hcardUU, c.card_omegaOne_W]
        _ ≤ relativeWeakClosure G₁ U S₁ :=
            sup_le (subgroup_le_relative_weak_closure _ _ _ hUS₁)
              (rightConjugate_le_relativeWeakClosure hn hle)
    refine ⟨n, hn, ?_, hUnN, Or.inr hW₁⟩
    rw [hW₁]
    exact (Subgroup.eq_of_le_of_card_ge (sup_le hUV hUnV)
      (by rw [rightConjugate_card, hcardUU, c.card_omegaOne_W])).symm

theorem exists_odd_conj_of_le_sup {P O : Subgroup X} (hP : IsPGroup 2 P)
    (hO : Odd (Nat.card O)) (hPO : P ≤ Subgroup.normalizer (O : Set X)) {m : X}
    (hm : rightConjugate P m ≤ P ⊔ O) : ∃ o ∈ O, rightConjugate P m = rightConjugate P o := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinf : P ⊓ O = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨k, hk⟩ := hP ⟨x, hx.1⟩
    exact Subgroup.mem_bot.mpr (eq_one_of_two_pow_of_odd hx.2 hO (congrArg Subtype.val hk))
  have hsyl := isSylowOf_sup_odd' hP hO hPO hinf
  have hsyl' : IsSylowOf 2 (rightConjugate P m) (P ⊔ O) :=
    isSylowOf_of_card hm (by rw [rightConjugate_card, hsyl.card_eq])
  obtain ⟨c, hc, hceq⟩ := exists_rightConjugate_eq_of_isSylowOf hsyl' hsyl
  have hcm : c ∈ (P : Set X) * (O : Set X) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right P O hPO]
    exact hc
  obtain ⟨p, hp, o, ho, rfl⟩ := Set.mem_mul.mp hcm
  refine ⟨o, ho, ?_⟩
  rw [← hceq, ← rightConjugate_mul, rightConjugate_eq_of_mem hp]

theorem sub_omegaOne (c : Conf46 G T S Q H g) (htop : G ⊔ T = ⊤)
    (IH : IH46 (Nat.card (G ⊔ T : Subgroup X))) {G₁ S₀ : Subgroup X} (hG₁ : G₁ ≤ G)
    (hUN : omegaOne T ≤ Subgroup.normalizer (G₁ : Set X))
    (hZG₁ : omegaOne ((T ⊔ rightConjugate T g) ⊓ G) ≤ G₁)
    (hS₀ : IsSylowOf 2 S₀ (G₁ ⊔ omegaOne T)) (hS₀S : S₀ ≤ S)
    (hcard : Nat.card (G₁ ⊔ omegaOne T : Subgroup X) < Nat.card (G ⊔ T : Subgroup X)) :
    ⁅G₁, omegaOne T⁆ ≤ (CFSG.oddCore G₁).map G₁.subtype ∨
    G₁ ≤ Subgroup.normalizer ((omegaOne (T ⊔ rightConjugate T g) ⊔
      (CFSG.oddCore G₁).map G₁.subtype : Subgroup X) : Set X) ∨
    ∃ y ∈ G₁ ⊔ omegaOne T, ∃ B : Subgroup X, B ≤ G₁ ∧ G₁ ≤ Subgroup.normalizer (B : Set X) ∧
      rightConjugate (omegaOne ((T ⊔ rightConjugate T g) ⊓ G)) y ≤ B ∧
      ∀ N : Subgroup X, IsPGroup 2 N → N ≤ B → G₁ ≤ Subgroup.normalizer (N : Set X) →
        N = ⊥ := by
  obtain ⟨S₁, hS₁, y, hyL, n₁, hn₁, hW₁eq, hn₁N, hcases⟩ :=
    c.exists_conf_omegaOne htop hG₁ hUN hS₀ hS₀S
  have h43₁ := c.hyp43_omegaOne htop hG₁
  set U := omegaOne T with hUdef
  set Z₁ := omegaOne ((T ⊔ rightConjugate T g) ⊓ G) with hZ₁def
  set V := omegaOne (T ⊔ rightConjugate T g) with hVdef
  set O₁ := (CFSG.oddCore G₁).map G₁.subtype with hO₁
  rcases hcases with hW₁U | hW₁V
  ·
    left
    have hW₁U' : relativeWeakClosure G₁ U S₁ = U := hW₁U
    exact lemma_4_2_oddCore ⟨hS₁.toFrame, hS₁.sylow, hS₁.le, fun x hx hle =>
      Subgroup.eq_of_le_of_card_ge
        ((rightConjugate_le_relativeWeakClosure hx hle).trans hW₁U'.le)
        (by rw [rightConjugate_card])⟩
  · have hW₁V' : relativeWeakClosure G₁ U S₁ = rightConjugate V y := hW₁V
    have hyN : y ∈ Subgroup.normalizer (G₁ : Set X) :=
      (sup_le Subgroup.le_normalizer hUN) hyL
    have hG₁y : rightConjugate G₁ y = G₁ := (rightConjugate_eq_self_iff G₁ y).mpr hyN
    have hO₁N : ∀ x ∈ Subgroup.normalizer (G₁ : Set X),
        x ∈ Subgroup.normalizer (O₁ : Set X) := fun x hx => by
      have : (CFSG.oddCore G₁).Characteristic := OddCore.characteristic _
      exact mem_normalizer_map_of_characteristic _ hx
    have hO₁y : rightConjugate O₁ y = O₁ :=
      (rightConjugate_eq_self_iff O₁ y).mpr (hO₁N y hyN)
    have hZV : Z₁ ≤ V := by
      have hVeq : V = U ⊔ Z₁ := c.omegaOne_W
      rw [hVeq]
      exact le_sup_right
    rcases IH46.apply_mod_odd IH hcard hS₁ h43₁ c.omegaOne_ne_bot hn₁ hW₁eq hn₁N with
      hm | hN | ⟨B, hBG, hG₁B, hWB, hfree⟩
    · exfalso
      rw [pRank_omegaOne] at hm
      have := c.pRank_lt
      omega
    · right; left
      rw [hW₁V'] at hN
      have hNy : rightConjugate V y ⊔ O₁ = rightConjugate (V ⊔ O₁) y := by
        unfold rightConjugate
        rw [Subgroup.map_sup]
        change rightConjugate V y ⊔ O₁ = rightConjugate V y ⊔ rightConjugate O₁ y
        rw [hO₁y]
      rw [hNy, ← rightConjugate_normalizer] at hN
      intro m hm
      have hx : y⁻¹ * m * y ∈ G₁ := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyN) m).mp hm
        simpa using this
      have h1 := hN hx
      rw [mem_rightConjugate_iff] at h1
      simpa [mul_assoc] using h1
    · right; right
      refine ⟨y, hyL, B, hBG, hG₁B, le_trans (le_inf ?_ ?_) hWB, hfree⟩
      · rw [hW₁V']
        exact rightConjugate_le_rightConjugate hZV y
      · rw [← hG₁y]
        exact rightConjugate_le_rightConjugate hZG₁ y

theorem local_step (c : Conf46 G T S Q H g) (htop : G ⊔ T = ⊤)
    (IH : IH46 (Nat.card (G ⊔ T : Subgroup X))) {D : Subgroup X} (hDS : D ≤ S ⊓ G)
    (hZD : omegaOne ((T ⊔ rightConjugate T g) ⊓ G) ≤ D)
    (hsyl : IsSylowOf 2 ((S ⊓ G) ⊓ Subgroup.normalizer (D : Set X))
      (G ⊓ Subgroup.normalizer (D : Set X)))
    (hlt : G ⊓ Subgroup.normalizer (D : Set X) < G) :
    ∀ n ∈ G ⊓ Subgroup.normalizer (D : Set X),
      rightConjugate (omegaOne ((T ⊔ rightConjugate T g) ⊓ G)) n =
        omegaOne ((T ⊔ rightConjugate T g) ⊓ G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := omegaOne T with hUdef
  set Z₁ := omegaOne ((T ⊔ rightConjugate T g) ⊓ G) with hZ₁def
  set V := omegaOne (T ⊔ rightConjugate T g) with hVdef
  set G₁ := G ⊓ Subgroup.normalizer (D : Set X) with hG₁def
  have hUT : U ≤ T := omegaOne_le T
  have hU2 : IsPGroup 2 U := c.frame.isPGroup.to_le hUT
  have hDG : D ≤ G := hDS.trans inf_le_right
  have hDG₁ : D ≤ G₁ := le_inf hDG Subgroup.le_normalizer
  have hZG₁ : Z₁ ≤ G₁ := hZD.trans hDG₁
  have hD2 : IsPGroup 2 D := c.isPGroup_S.to_le (hDS.trans inf_le_left)
  have hUD : U ≤ Subgroup.normalizer (D : Set X) := by
    have hconj : ∀ u ∈ U, ∀ d ∈ D, u * d * u⁻¹ ∈ D := by
      intro u hu d hd
      have hk := hZD (c.commutator_mem_omegaOne (hDS hd).1 hu)
      have : u * d * u⁻¹ = (d⁻¹ * (d * u * d⁻¹ * u⁻¹))⁻¹ := by group
      rw [this]
      exact D.inv_mem (D.mul_mem (D.inv_mem hd) hk)
    intro u hu
    exact mem_normalizer_of_conj_le (hconj u hu) (by
      simpa using hconj u⁻¹ (U.inv_mem hu))
  have hUG₁ : U ≤ Subgroup.normalizer (G₁ : Set X) := fun u hu =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨c.frame.le_normalizer (hUT hu), Subgroup.le_normalizer (hUD hu)⟩
  have hUG₁inf : G₁ ⊓ U = ⊥ := by
    rw [eq_bot_iff, ← c.frame.inf_eq_bot, inf_comm]
    exact inf_le_inf hUT inf_le_left
  have hUP : U ≤ Subgroup.normalizer (((S ⊓ G) ⊓ Subgroup.normalizer (D : Set X) :
      Subgroup X) : Set X) := fun u hu =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer (c.le_S (hUT hu)), c.frame.le_normalizer (hUT hu)⟩,
      Subgroup.le_normalizer (hUD hu)⟩
  have hS₀ := isSylowOf_sup_of_isSylowOf hsyl hU2 hUG₁ hUP hUG₁inf
  have hS₀S : (S ⊓ G) ⊓ Subgroup.normalizer (D : Set X) ⊔ U ≤ S :=
    sup_le (inf_le_left.trans inf_le_left) (hUT.trans c.le_S)
  have hcard : Nat.card (G₁ ⊔ U : Subgroup X) < Nat.card (G ⊔ T : Subgroup X) := by
    rw [card_sup_of_le_normalizer hUG₁ hUG₁inf, card_sup_of_le_normalizer
      c.frame.le_normalizer (by rw [inf_comm]; exact c.frame.inf_eq_bot)]
    exact Nat.mul_lt_mul_of_lt_of_le (Subgroup.card_lt_of_lt hlt)
      (Subgroup.card_le_of_le hUT) Nat.card_pos
  set O₁ := (CFSG.oddCore G₁).map G₁.subtype with hO₁
  have hO₁odd : Odd (Nat.card O₁) := by
    rw [hO₁, Subgroup.card_map_of_injective G₁.subtype_injective]
    exact odd_card_oddCore _
  have hO₁G₁ : O₁ ≤ G₁ := Subgroup.map_subtype_le _
  have hO₁N : ∀ x ∈ Subgroup.normalizer (G₁ : Set X), x ∈ Subgroup.normalizer (O₁ : Set X) :=
    fun x hx => by
      have : (CFSG.oddCore G₁).Characteristic := OddCore.characteristic _
      exact mem_normalizer_map_of_characteristic _ hx
  have hOD : ∀ o ∈ O₁, ∀ z ∈ D, o * z * o⁻¹ = z := by
    intro o ho z hz
    have h1 : o * z * o⁻¹ * z⁻¹ ∈ O₁ := by
      have := (Subgroup.mem_normalizer_iff.mp (hO₁N z (Subgroup.le_normalizer (hDG₁ hz)))
        o⁻¹).mp (O₁.inv_mem ho)
      have h2 : o * z * o⁻¹ * z⁻¹ = o * (z * o⁻¹ * z⁻¹) := by group
      rw [h2]
      exact O₁.mul_mem ho this
    have h2 : o * z * o⁻¹ * z⁻¹ ∈ D := by
      have := (Subgroup.mem_normalizer_iff.mp (hO₁G₁ ho).2 z).mp hz
      exact D.mul_mem this (D.inv_mem hz)
    obtain ⟨k, hk⟩ := hD2 ⟨_, h2⟩
    have h3 := eq_one_of_two_pow_of_odd h1 hO₁odd (congrArg Subtype.val hk)
    calc o * z * o⁻¹ = (o * z * o⁻¹ * z⁻¹) * z := by group
      _ = z := by rw [h3, one_mul]
  have hZo : ∀ o ∈ O₁, rightConjugate Z₁ o = Z₁ := by
    intro o ho
    apply (rightConjugate_eq_self_iff Z₁ o).mpr
    exact mem_normalizer_of_conj_le (fun z hz => by rw [hOD o ho z (hZD hz)]; exact hz)
      (fun z hz => by
        have h := hOD o⁻¹ (O₁.inv_mem ho) z (hZD hz)
        simp only [inv_inv] at h ⊢
        rw [h]
        exact hz)
  have hUO₁ : U ≤ Subgroup.normalizer (O₁ : Set X) := fun u hu => hO₁N u (hUG₁ hu)
  intro n hn
  rcases c.sub_omegaOne htop IH inf_le_left hUG₁ hZG₁ hS₀ hS₀S hcard with
    hcomm | hN | ⟨y, hyL, B, -, hG₁B, hZB, hfree⟩
  ·
    have hle : rightConjugate U n ≤ U ⊔ O₁ := by
      intro w hw
      rw [mem_rightConjugate_iff] at hw
      have hk : (n * w * n⁻¹)⁻¹ * n⁻¹ * (n * w * n⁻¹) * n ∈ O₁ := by
        apply hcomm
        rw [Subgroup.commutator_comm]
        have := Subgroup.commutator_mem_commutator (U.inv_mem hw) (G₁.inv_mem hn)
        simpa [commutatorElement_def] using this
      have : w = (n * w * n⁻¹) * ((n * w * n⁻¹)⁻¹ * n⁻¹ * (n * w * n⁻¹) * n) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hw) (Subgroup.mem_sup_right hk)
    obtain ⟨o, ho, hno⟩ := exists_odd_conj_of_le_sup hU2 hO₁odd hUO₁ hle
    have hmG₁ : n * o⁻¹ ∈ G₁ := G₁.mul_mem hn (G₁.inv_mem (hO₁G₁ ho))
    have hmU : n * o⁻¹ ∈ Subgroup.normalizer (U : Set X) := by
      rw [← rightConjugate_eq_self_iff, ← rightConjugate_mul, hno, rightConjugate_mul,
        mul_inv_cancel, rightConjugate_one]
    have hmS : rightConjugate Z₁ (n * o⁻¹) ≤ S := by
      have h1 := rightConjugate_le_rightConjugate hZD (n * o⁻¹)
      rw [(rightConjugate_eq_self_iff D _).mpr hmG₁.2] at h1
      exact h1.trans (hDS.trans inf_le_left)
    have hZm := c.conj_omegaOne_eq hmG₁.1 hmU hmS
    have hn' : n = n * o⁻¹ * o := by group
    rw [hn', ← rightConjugate_mul, hZm, hZo o ho]
  ·
    have hV2 : IsPGroup 2 V := c.isPGroup_S.to_le ((omegaOne_le _).trans c.W_le_S)
    have hVO₁ : V ≤ Subgroup.normalizer (O₁ : Set X) := by
      have hVeq : V = U ⊔ Z₁ := c.omegaOne_W
      rw [hVeq]
      exact sup_le hUO₁ (fun z hz => hO₁N z (Subgroup.le_normalizer (hZG₁ hz)))
    have hVG : V ⊓ G = Z₁ := c.omegaOne_W_inf
    have hle : rightConjugate V n ≤ V ⊔ O₁ := by
      have h1 := rightConjugate_le_rightConjugate (le_sup_left : V ≤ V ⊔ O₁) n
      rwa [(rightConjugate_eq_self_iff _ n).mpr (hN hn)] at h1
    obtain ⟨o, ho, hno⟩ := exists_odd_conj_of_le_sup hV2 hO₁odd hVO₁ hle
    calc rightConjugate Z₁ n = rightConjugate (V ⊓ G) n := by rw [hVG]
      _ = rightConjugate V o ⊓ G := by
          rw [rightConjugate_inf, hno, rightConjugate_eq_of_mem hn.1]
      _ = rightConjugate (V ⊓ G) o := by
          rw [rightConjugate_inf, rightConjugate_eq_of_mem (hO₁G₁ ho).1]
      _ = Z₁ := by rw [hVG, hZo o ho]
  ·
    exfalso
    have hyN : y ∈ Subgroup.normalizer (G₁ : Set X) :=
      (sup_le Subgroup.le_normalizer hUG₁) hyL
    have hG₁y : rightConjugate G₁ y = G₁ := (rightConjugate_eq_self_iff G₁ y).mpr hyN
    have hNN : G₁ ≤ Subgroup.normalizer
        ((rightConjugate D y ⊓ B : Subgroup X) : Set X) := by
      intro x hx
      refine Subgroup.inf_normalizer_le_normalizer_inf ⟨?_, hG₁B hx⟩
      rw [← rightConjugate_normalizer]
      have h1 := rightConjugate_le_rightConjugate (inf_le_right : G₁ ≤ _) y
      rw [hG₁y] at h1
      exact h1 hx
    have hbot := hfree _ ((isPGroup_rightConjugate hD2 y).to_le inf_le_left) inf_le_right hNN
    have hZy : rightConjugate Z₁ y ≤ rightConjugate D y ⊓ B :=
      le_inf (rightConjugate_le_rightConjugate hZD y) hZB
    rw [hbot, le_bot_iff, rightConjugate_eq_bot_iff] at hZy
    exact c.omegaOne_Z_ne_bot hZy

theorem isSylowOf_inf (c : Conf46 G T S Q H g) : IsSylowOf 2 (S ⊓ G) G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact c.sylowFrame.sylow.inf_of_le_normalizer le_sup_left
    (sup_le Subgroup.le_normalizer c.frame.le_normalizer)

theorem weaklyClosed_omegaOne (c : Conf46 G T S Q H g) (htop : G ⊔ T = ⊤)
    (IH : IH46 (Nat.card (G ⊔ T : Subgroup X)))
    (hnn : ∀ D : Subgroup X, omegaOne ((T ⊔ rightConjugate T g) ⊓ G) ≤ D → D ≤ S ⊓ G →
      G ≤ Subgroup.normalizer (D : Set X) → False) :
    ∀ x ∈ G, rightConjugate (omegaOne ((T ⊔ rightConjugate T g) ⊓ G)) x ≤ S ⊓ G →
      rightConjugate (omegaOne ((T ⊔ rightConjugate T g) ⊓ G)) x =
        omegaOne ((T ⊔ rightConjugate T g) ⊓ G) := by
  have hZS : omegaOne ((T ⊔ rightConjugate T g) ⊓ G) ≤ S ⊓ G :=
    le_inf ((omegaOne_le _).trans (inf_le_left.trans c.W_le_S))
      ((omegaOne_le _).trans inf_le_right)
  intro x hx hle
  apply rightConjugate_eq_of_alperin c.isSylowOf_inf hZS _ hx hle
  intro D hDS hZD hsyl _ n hn
  by_cases hlt : G ⊓ Subgroup.normalizer (D : Set X) < G
  · exact c.local_step htop IH hDS hZD hsyl hlt n hn
  · exfalso
    apply hnn D hZD hDS
    have heq : G ⊓ Subgroup.normalizer (D : Set X) = G :=
      (eq_or_lt_of_le inf_le_left).resolve_right hlt
    rw [← heq]
    exact inf_le_right

theorem stronglyClosed_omegaOne (c : Conf46 G T S Q H g) (htop : G ⊔ T = ⊤)
    (IH : IH46 (Nat.card (G ⊔ T : Subgroup X)))
    (hnn : ∀ D : Subgroup X, omegaOne ((T ⊔ rightConjugate T g) ⊓ G) ≤ D → D ≤ S ⊓ G →
      G ≤ Subgroup.normalizer (D : Set X) → False)
    {z x : X} (hz : z ∈ omegaOne ((T ⊔ rightConjugate T g) ⊓ G)) (hx : x ∈ G)
    (hS : x⁻¹ * z * x ∈ S) : x⁻¹ * z * x ∈ omegaOne ((T ⊔ rightConjugate T g) ⊓ G) := by
  set Z₁ := omegaOne ((T ⊔ rightConjugate T g) ⊓ G) with hZ₁def
  have hZab : IsMulCommutative Z₁ :=
    isMulCommutative_of_le ((omegaOne_le _).trans inf_le_left) c.isMulCommutative_W
  have hZS : Z₁ ≤ S ⊓ G :=
    le_inf ((omegaOne_le _).trans (inf_le_left.trans c.W_le_S))
      ((omegaOne_le _).trans inf_le_right)
  have hz2 : z ^ 2 = 1 :=
    ((mem_omegaOne_iff (isMulCommutative_of_le inf_le_left c.isMulCommutative_W)).mp hz).2
  have hzx2 : (x⁻¹ * z * x) ^ 2 = 1 := by
    rw [pow_two, show x⁻¹ * z * x * (x⁻¹ * z * x) = x⁻¹ * (z * z) * x by group, ← pow_two, hz2,
      mul_one, inv_mul_cancel]
  have hcomm : x⁻¹ * z * x ∈ Subgroup.centralizer (Z₁ : Set X) := by
    have h1 : x⁻¹ * z * x ∈ omegaOne S := mem_omegaOne hS hzx2
    exact Subgroup.mem_centralizer_iff.mpr fun w hw =>
      (Subgroup.mem_centralizer_iff.mp (c.omegaOne_Z_le hw).2 _ h1).symm
  exact mem_of_weaklyClosed c.isSylowOf_inf hZS hZab (c.weaklyClosed_omegaOne htop IH hnn)
    hz hx hcomm

end Conf46

end CFSG.ComponentClassification.AschbacherTheorem3
