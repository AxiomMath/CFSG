module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixLocal
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.SignalizerFunctor.Helpers
open CFSG.Open
open scoped Pointwise commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem inf_centralizer_le_of_odd {G K N : Subgroup X} (hNn : N.Normal) (hKn : K.Normal)
    (hKG : K ≤ G) (hO : CFSG.oddCore G = ⊥) (hN2 : IsPGroup 2 N)
    (hodd : ∀ C ≤ K, ¬ 2 ∣ N.relIndex C) : K ⊓ Subgroup.centralizer (N : Set X) ≤ N := by
  set C := K ⊓ Subgroup.centralizer (N : Set X) with hCdef
  have hCn : C.Normal := by
    have : (Subgroup.centralizer (N : Set X)).Normal := inferInstance
    exact Subgroup.normal_inf_normal _ _
  have heq : N ⊓ C = C := by
    apply eq_of_central_sylow inf_le_right
      ((inf_le_right : C ≤ _).trans (Subgroup.centralizer_le
        (SetLike.coe_subset_coe.mpr inf_le_left)))
      (hN2.to_le inf_le_left)
    · rw [Subgroup.inf_relIndex_right]
      exact hodd C inf_le_left
    · exact oddCore_eq_bot_of_le (inf_le_left.trans hKG)
        (by rw [Subgroup.normalizer_eq_top]; exact le_top) hO
  rw [← heq]
  exact inf_le_left

theorem oddCore_eq_bot_of_le_of_centralizer {G G₁ N : Subgroup X} (hNG₁ : N ≤ G₁)
    (hG₁G : G₁ ≤ G) (hN2 : IsPGroup 2 N) (hG₁N : G₁ ≤ Subgroup.normalizer (N : Set X))
    (hC : G ⊓ Subgroup.centralizer (N : Set X) ≤ N) : CFSG.oddCore G₁ = ⊥ := by
  set O₁ := (CFSG.oddCore G₁).map G₁.subtype with hO₁
  have hO₁odd : Odd (Nat.card O₁) := by
    rw [hO₁, Subgroup.card_map_of_injective G₁.subtype_injective]
    exact odd_card_oddCore _
  have hO₁G₁ : O₁ ≤ G₁ := Subgroup.map_subtype_le _
  have hO₁N : G₁ ≤ Subgroup.normalizer (O₁ : Set X) := fun x hx => by
    have : (CFSG.oddCore G₁).Characteristic := OddCore.characteristic _
    exact mem_normalizer_map_of_characteristic _ (Subgroup.le_normalizer hx)
  have hcent : O₁ ≤ Subgroup.centralizer (N : Set X) := by
    intro o ho
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have h1 : o * z * o⁻¹ * z⁻¹ ∈ O₁ := by
      have := (Subgroup.mem_normalizer_iff.mp (hO₁N (hNG₁ hz)) o⁻¹).mp (O₁.inv_mem ho)
      have h2 : o * z * o⁻¹ * z⁻¹ = o * (z * o⁻¹ * z⁻¹) := by group
      rw [h2]
      exact O₁.mul_mem ho this
    have h2 : o * z * o⁻¹ * z⁻¹ ∈ N := by
      have := (Subgroup.mem_normalizer_iff.mp (hG₁N (hO₁G₁ ho)) z).mp hz
      exact N.mul_mem this (N.inv_mem hz)
    obtain ⟨k, hk⟩ := hN2 ⟨_, h2⟩
    have h3 := eq_one_of_two_pow_of_odd h1 hO₁odd (congrArg Subtype.val hk)
    calc z * o = (o * z * o⁻¹ * z⁻¹)⁻¹ * (o * z) := by group
      _ = o * z := by rw [h3, inv_one, one_mul]
  have hle : O₁ ≤ N := fun o ho => hC ⟨hG₁G (hO₁G₁ ho), hcent ho⟩
  have hbot : O₁ = ⊥ := by
    rw [eq_bot_iff]
    intro o ho
    obtain ⟨k, hk⟩ := hN2 ⟨o, hle ho⟩
    exact Subgroup.mem_bot.mpr (eq_one_of_two_pow_of_odd ho hO₁odd (congrArg Subtype.val hk))
  exact (Subgroup.map_eq_bot_iff_of_injective _ G₁.subtype_injective).mp hbot

omit [Finite X] in
theorem conj_mem_sup {A B : Subgroup X} {x : X} (hA : ∀ a ∈ A, x * a * x⁻¹ ∈ A ⊔ B)
    (hB : ∀ b ∈ B, x * b * x⁻¹ ∈ A ⊔ B) : ∀ y ∈ A ⊔ B, x * y * x⁻¹ ∈ A ⊔ B := by
  have hle : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj x).toMonoidHom :=
    sup_le (fun a ha => hA a ha) (fun b hb => hB b hb)
  exact fun y hy => hle hy

omit [Finite X] in
theorem le_normalizer_sup_of_commutator_le {G K U : Subgroup X}
    (hK : G ≤ Subgroup.normalizer (K : Set X)) (hGU : ⁅G, U⁆ ≤ K) :
    G ≤ Subgroup.normalizer ((K ⊔ U : Subgroup X) : Set X) := by
  have hconj : ∀ x ∈ G, ∀ y ∈ K ⊔ U, x * y * x⁻¹ ∈ K ⊔ U := by
    intro x hx
    apply conj_mem_sup
    · intro k hk
      exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hK hx) k).mp hk)
    · intro u hu
      have h1 : x * u * x⁻¹ * u⁻¹ ∈ K := hGU (Subgroup.commutator_mem_commutator hx hu)
      have : x * u * x⁻¹ = (x * u * x⁻¹ * u⁻¹) * u := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right hu)
  intro x hx
  exact mem_normalizer_of_conj_le (hconj x hx) (by simpa using hconj x⁻¹ (G.inv_mem hx))

namespace Conf46

variable {G T S Q H : Subgroup X} {g : X}

theorem W_inf_le_commutator (c : Conf46 G T S Q H g) :
    (T ⊔ rightConjugate T g) ⊓ G ≤ ⁅T, G⁆ := by
  rintro w ⟨hw, hwG⟩
  have hwm : w ∈ (T : Set X) * (rightConjugate T g : Set X) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left T _ c.le_normalizer]
    exact hw
  obtain ⟨t, ht, k, hk, rfl⟩ := Set.mem_mul.mp hwm
  have hk' : g * k * g⁻¹ ∈ T := (mem_rightConjugate_iff T g k).mp hk
  set t' := g * k * g⁻¹ with ht'
  have hcomm : t'⁻¹ * g⁻¹ * t' * g ∈ ⁅T, G⁆ := by
    have := Subgroup.commutator_mem_commutator (T.inv_mem hk') (G.inv_mem c.mem)
    simpa [commutatorElement_def] using this
  have hTG : ⁅T, G⁆ ≤ G := by
    rw [Subgroup.commutator_comm]
    exact c.frame.commutator_le
  have hkeq : k = t' * (t'⁻¹ * g⁻¹ * t' * g) := by rw [ht']; group
  have htt : t * t' ∈ T ⊓ G := by
    refine ⟨T.mul_mem ht hk', ?_⟩
    have h1 : t * k ∈ G := hwG
    rw [hkeq, ← mul_assoc] at h1
    have h2 := G.mul_mem h1 (G.inv_mem (hTG hcomm))
    rwa [mul_inv_cancel_right] at h2
  rw [c.frame.inf_eq_bot, Subgroup.mem_bot] at htt
  rw [hkeq, ← mul_assoc, htt, one_mul]
  exact hcomm

theorem normal_sup_omegaOne (c : Conf46 G T S Q H g) (htop : G ⊔ T = ⊤) {K : Subgroup X}
    (hKn : K.Normal) (hGU : ⁅G, omegaOne T⁆ ≤ K) : (K ⊔ omegaOne T).Normal := by
  have hUT : omegaOne T ≤ T := omegaOne_le T
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← htop]
  refine sup_le (le_normalizer_sup_of_commutator_le
    (by rw [Subgroup.normalizer_eq_top]; exact le_top) hGU) ?_
  intro t ht
  have hconj : ∀ s ∈ T, ∀ y ∈ K ⊔ omegaOne T, s * y * s⁻¹ ∈ K ⊔ omegaOne T := by
    intro s hs
    apply conj_mem_sup
    · intro k hk
      exact Subgroup.mem_sup_left (hKn.conj_mem k hk s)
    · intro u hu
      have h := congrArg Subtype.val (c.isMulCommutative.is_comm.comm ⟨s, hs⟩ ⟨u, hUT hu⟩)
      have : s * u * s⁻¹ = u := by
        rw [show s * u = u * s from h, mul_inv_cancel_right]
      rw [this]
      exact Subgroup.mem_sup_right hu
  exact mem_normalizer_of_conj_le (hconj t ht) (by simpa using hconj t⁻¹ (T.inv_mem ht))

theorem le_normalizer_of_normal_sup (c : Conf46 G T S Q H g) (htop : G ⊔ T = ⊤)
    {G₁ : Subgroup X} (hZG₁ : omegaOne ((T ⊔ rightConjugate T g) ⊓ G) ≤ G₁)
    (hn : (G₁ ⊔ omegaOne T).Normal)
    (hV : G₁ ⊔ omegaOne T ≤
      Subgroup.normalizer ((omegaOne (T ⊔ rightConjugate T g) : Subgroup X) : Set X)) :
    G ≤ Subgroup.normalizer ((omegaOne (T ⊔ rightConjugate T g) : Subgroup X) : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := G₁ ⊔ omegaOne T with hL
  set V := omegaOne (T ⊔ rightConjugate T g) with hVdef
  have hV2 : IsPGroup 2 V := c.isPGroup_S.to_le ((omegaOne_le _).trans c.W_le_S)
  have hVL : V ≤ L := by
    have hVeq : V = omegaOne T ⊔ omegaOne ((T ⊔ rightConjugate T g) ⊓ G) := c.omegaOne_W
    rw [hVeq]
    exact sup_le le_sup_right (hZG₁.trans le_sup_left)
  have hSL : IsSylowOf 2 (S ⊓ L) L := c.sylowFrame.sylow.inf_of_le_normalizer
    (by rw [htop]; exact le_top) (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  apply c.le_normalizer_omegaOne_of_forall
  intro x _
  have hLx : rightConjugate L x = L := (rightConjugate_eq_self_iff L x).mpr
    (by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top x)
  have hVx : rightConjugate V x ≤ S ⊓ L := by
    apply le_of_isSylowOf_of_le_normalizer hSL (isPGroup_rightConjugate hV2 x)
    · have h1 := rightConjugate_le_rightConjugate hVL x
      rwa [hLx] at h1
    · intro y hy
      rw [← rightConjugate_normalizer]
      have h1 := rightConjugate_le_rightConjugate hV x
      rw [hLx] at h1
      exact h1 hy
  exact (rightConjugate_le_rightConjugate (omegaOne_mono le_sup_left) x).trans
    (hVx.trans inf_le_left)

theorem not_free (c : Conf46 G T S Q H g) {P B L : Subgroup X} (hPn : P.Normal)
    (hP2 : IsPGroup 2 P) (hZP : omegaOne ((T ⊔ rightConjugate T g) ⊓ G) ≤ P)
    (hLB : L ≤ Subgroup.normalizer (B : Set X)) {y : X}
    (hZB : rightConjugate (omegaOne ((T ⊔ rightConjugate T g) ⊓ G)) y ≤ B)
    (hfree : ∀ N : Subgroup X, IsPGroup 2 N → N ≤ B → L ≤ Subgroup.normalizer (N : Set X) →
      N = ⊥) : False := by
  have hPN : ∀ x : X, x ∈ Subgroup.normalizer (P : Set X) := fun x => by
    rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top x
  have hNN : L ≤ Subgroup.normalizer ((P ⊓ B : Subgroup X) : Set X) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hPN x, hLB hx⟩
  have hbot := hfree _ (hP2.to_le inf_le_left) inf_le_right hNN
  have hZy : rightConjugate (omegaOne ((T ⊔ rightConjugate T g) ⊓ G)) y ≤ P ⊓ B := by
    refine le_inf ?_ hZB
    have h1 := rightConjugate_le_rightConjugate hZP y
    rwa [(rightConjugate_eq_self_iff P y).mpr (hPN y)] at h1
  rw [hbot, le_bot_iff, rightConjugate_eq_bot_iff] at hZy
  exact c.omegaOne_Z_ne_bot hZy

theorem caseOne_central (c : Conf46 G T S Q H g) (htop : G ⊔ T = ⊤) (hO : CFSG.oddCore G = ⊥)
    (IH : IH46 (Nat.card (G ⊔ T : Subgroup X))) {P : Subgroup X} (hPn : P.Normal)
    (hPS : P ≤ S) (hZP : omegaOne ((T ⊔ rightConjugate T g) ⊓ G) ≤ P)
    (hT : omegaOne T = T) {e : X} (heT : e ∈ T) (he1 : e ≠ 1)
    (he : ∀ x ∈ G, x * e * x⁻¹ * e⁻¹ ∈ P) :
    G ≤ Subgroup.normalizer ((omegaOne (T ⊔ rightConjugate T g) : Subgroup X) : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := omegaOne T with hUdef
  set Z₁ := omegaOne ((T ⊔ rightConjugate T g) ⊓ G) with hZ₁def
  set V := omegaOne (T ⊔ rightConjugate T g) with hVdef
  have hP2 : IsPGroup 2 P := c.isPGroup_S.to_le hPS
  have he2 : e ^ 2 = 1 := by
    have : e ∈ U := hT ▸ heT
    exact ((mem_omegaOne_iff c.isMulCommutative).mp this).2
  have hZT : ∀ x ∈ G, rightConjugate T x ≤ Subgroup.centralizer (Z₁ : Set X) := by
    intro x hx t' ht' z hz
    rw [mem_rightConjugate_iff] at ht'
    have hzx : x * z * x⁻¹ ∈ H ⊓ S := by
      have hzP : x * z * x⁻¹ ∈ P := hPn.conj_mem z (hZP hz) x
      refine ⟨?_, hPS hzP⟩
      apply c.hyp43.centralizer_le c.frame heT he1
      refine ⟨htop ▸ Subgroup.mem_top _, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have hex : x⁻¹ * e * x ∈ S := by
        have h1 := he x⁻¹ (G.inv_mem hx)
        have : x⁻¹ * e * x = (x⁻¹ * e * x⁻¹⁻¹ * e⁻¹) * e := by group
        rw [this]
        exact S.mul_mem (hPS h1) (c.le_S heT)
      have hex2 : (x⁻¹ * e * x) ^ 2 = 1 := by
        rw [pow_two, show x⁻¹ * e * x * (x⁻¹ * e * x) = x⁻¹ * (e * e) * x by group, ← pow_two,
          he2, mul_one, inv_mul_cancel]
      have hc := Subgroup.mem_centralizer_iff.mp (c.omegaOne_Z_le hz).2 _ (mem_omegaOne hex hex2)
      calc x * z * x⁻¹ * e = x * (z * (x⁻¹ * e * x)) * x⁻¹ := by group
        _ = x * ((x⁻¹ * e * x) * z) * x⁻¹ := by rw [hc]
        _ = e * (x * z * x⁻¹) := by group
    have h1 := Subgroup.mem_centralizer_iff.mp (c.hyp45.le_centralizer hzx) _ ht'
    calc z * t' = x⁻¹ * ((x * z * x⁻¹) * (x * t' * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * t' * x⁻¹) * (x * z * x⁻¹)) * x := by rw [h1]
      _ = t' * z := by group
  set G₂ := ⁅T, G⁆ with hG₂def
  have hG₂n : G₂.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← htop, sup_comm]
    exact sup_le (Subgroup.normalizer_commutator_ge_left T G)
      (Subgroup.normalizer_commutator_ge_right T G)
  have hG₂G : G₂ ≤ G := by
    rw [hG₂def, Subgroup.commutator_comm]
    exact c.frame.commutator_le
  have hZG₂ : Z₁ ≤ G₂ := (omegaOne_le _).trans c.W_inf_le_commutator
  have hG₂C : G₂ ≤ Subgroup.centralizer (Z₁ : Set X) := by
    rw [hG₂def, Subgroup.commutator_le]
    intro t ht x hx
    have h1 : t ∈ Subgroup.centralizer (Z₁ : Set X) := by
      have := hZT 1 G.one_mem
      rw [rightConjugate_one] at this
      exact this ht
    have h2 : x * t⁻¹ * x⁻¹ ∈ Subgroup.centralizer (Z₁ : Set X) := by
      apply hZT x⁻¹ (G.inv_mem hx)
      rw [mem_rightConjugate_iff]
      simpa [mul_assoc] using T.inv_mem ht
    have : ⁅t, x⁆ = t * (x * t⁻¹ * x⁻¹) := by rw [commutatorElement_def]; group
    rw [this]
    exact Subgroup.mul_mem _ h1 h2
  by_cases hlt : G₂ < G
  ·
    have hUT : U ≤ T := omegaOne_le T
    have hGUc : ⁅G, U⁆ ≤ G₂ := by
      rw [hG₂def, Subgroup.commutator_comm T G]
      exact Subgroup.commutator_mono le_rfl hUT
    have hLn : (G₂ ⊔ U).Normal := c.normal_sup_omegaOne htop hG₂n hGUc
    have hSL : IsSylowOf 2 (S ⊓ (G₂ ⊔ U)) (G₂ ⊔ U) := c.sylowFrame.sylow.inf_of_le_normalizer
      (by rw [htop]; exact le_top) (by rw [Subgroup.normalizer_eq_top]; exact le_top)
    have hcard : Nat.card (G₂ ⊔ U : Subgroup X) < Nat.card (G ⊔ T : Subgroup X) :=
      (Subgroup.card_le_of_le (sup_le_sup_left hUT G₂)).trans_lt (card_sup_lt c.frame hlt
        (by rw [Subgroup.normalizer_eq_top]; exact le_top))
    have hO₂ : CFSG.oddCore G₂ = ⊥ :=
      oddCore_eq_bot_of_le hG₂G (by rw [Subgroup.normalizer_eq_top]; exact le_top) hO
    rcases c.sub_omegaOne htop IH hG₂G (by rw [Subgroup.normalizer_eq_top]; exact le_top) hZG₂
      hSL inf_le_left hcard with hcomm | hN | ⟨y, -, B, -, hG₂B, hZB, hfree⟩
    ·
      rw [hO₂, Subgroup.map_bot, le_bot_iff] at hcomm
      have hU2 : IsPGroup 2 U := c.frame.isPGroup.to_le hUT
      have hUN : G₂ ⊔ U ≤ Subgroup.normalizer (U : Set X) := by
        refine sup_le ?_ Subgroup.le_normalizer
        exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm).trans
          (Subgroup.centralizer_le_normalizer _)
      apply c.le_normalizer_omegaOne_of_forall
      intro x _
      have hLx : rightConjugate (G₂ ⊔ U) x = G₂ ⊔ U := (rightConjugate_eq_self_iff _ x).mpr
        (by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top x)
      have hUx : rightConjugate U x ≤ S ⊓ (G₂ ⊔ U) := by
        apply le_of_isSylowOf_of_le_normalizer hSL (isPGroup_rightConjugate hU2 x)
        · have h1 := rightConjugate_le_rightConjugate (le_sup_right : U ≤ G₂ ⊔ U) x
          rwa [hLx] at h1
        · intro w hw
          rw [← rightConjugate_normalizer]
          have h1 := rightConjugate_le_rightConjugate hUN x
          rw [hLx] at h1
          exact h1 hw
      exact hUx.trans inf_le_left
    ·
      rw [hO₂, Subgroup.map_bot, sup_bot_eq] at hN
      exact c.le_normalizer_of_normal_sup htop hZG₂ hLn
        (sup_le hN (fun u hu => Subgroup.le_normalizer (omegaOne_mono le_sup_left hu)))
    ·
      exact (c.not_free hPn hP2 hZP hG₂B hZB hfree).elim
  ·
    have heq : G₂ = G := (eq_or_lt_of_le hG₂G).resolve_right hlt
    apply c.omegaOne_W_normal htop hO
    intro x hx
    have hx' : x ∈ G₂ := heq ▸ hx
    exact (hG₂C.trans (Subgroup.centralizer_le_normalizer _)) hx'

theorem caseOne_odd (c : Conf46 G T S Q H g) (htop : G ⊔ T = ⊤) (hO : CFSG.oddCore G = ⊥)
    (IH : IH46 (Nat.card (G ⊔ T : Subgroup X))) {P : Subgroup X} (hPn : P.Normal)
    (hPG : P ≤ G) (hPS : P ≤ S) (hZP : omegaOne ((T ⊔ rightConjugate T g) ⊓ G) ≤ P)
    (hT : omegaOne T = T) (hodd : ∀ C ≤ G, ¬ 2 ∣ P.relIndex C) :
    G ≤ Subgroup.normalizer ((omegaOne (T ⊔ rightConjugate T g) : Subgroup X) : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := omegaOne T with hUdef
  set Z₁ := omegaOne ((T ⊔ rightConjugate T g) ⊓ G) with hZ₁def
  set V := omegaOne (T ⊔ rightConjugate T g) with hVdef
  have hP2 : IsPGroup 2 P := c.isPGroup_S.to_le hPS
  have hGn : G.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← htop]
    exact sup_le Subgroup.le_normalizer c.frame.le_normalizer
  have hPN : ∀ x : X, x ∈ Subgroup.normalizer (P : Set X) := fun x => by
    rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top x
  by_cases hcen : U ≤ Subgroup.centralizer (P : Set X)
  · exact c.normalizer_omegaOne_of_central htop hO hPn hPG hPS hZP hcen
  by_contra hne
  have hCP : G ⊓ Subgroup.centralizer (P : Set X) ≤ P :=
    inf_centralizer_le_of_odd hPn hGn le_rfl hO hP2 hodd
  obtain ⟨E, hET, hE4, hEel⟩ := exists_four_le c.pRank_lt
  set π := QuotientGroup.mk' P with hπ
  have hkerπ : π.ker = P := QuotientGroup.ker_mk' P
  have hPGe : ∀ e : X, P ≤ G ⊓ (Subgroup.centralizer {π e}).comap π := fun e x hx => by
    refine ⟨hPG hx, ?_⟩
    have h1 : π x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    show π x ∈ Subgroup.centralizer {π e}
    rw [h1]
    exact Subgroup.one_mem _
  have hGe : ∀ e ∈ E, e ≠ 1 →
      G ⊓ (Subgroup.centralizer {π e}).comap π ≤ Subgroup.normalizer (V : Set X) := by
    intro e heE he1
    have heT : e ∈ T := hET heE
    set Ge := G ⊓ (Subgroup.centralizer {π e}).comap π with hGedef
    have hGeG : Ge ≤ G := inf_le_left
    have hUGe : U ≤ Subgroup.normalizer (Ge : Set X) := by
      intro u hu
      have huT : u ∈ T := omegaOne_le T hu
      apply Subgroup.inf_normalizer_le_normalizer_inf
      refine ⟨c.frame.le_normalizer huT, ?_⟩
      rw [← Subgroup.comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective P)]
      apply Subgroup.le_normalizer
      show π u ∈ Subgroup.centralizer {π e}
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      exact congrArg π (congrArg Subtype.val
        (c.isMulCommutative.is_comm.comm ⟨u, huT⟩ ⟨e, heT⟩))
    by_cases hlt : Ge < G
    · have hO₁ : CFSG.oddCore Ge = ⊥ :=
        oddCore_eq_bot_of_le_of_centralizer (hPGe e) hGeG hP2 (fun x _ => hPN x) hCP
      have hPsyl : IsSylowOf 2 P Ge := by
        rw [isSylowOf_iff]
        exact ⟨hPGe e, hP2, hodd Ge hGeG⟩
      have hU2 : IsPGroup 2 U := c.frame.isPGroup.to_le (omegaOne_le T)
      have hinf : Ge ⊓ U = ⊥ := by
        rw [eq_bot_iff, ← c.frame.inf_eq_bot, inf_comm]
        exact inf_le_inf (omegaOne_le T) hGeG
      have hS₀ := isSylowOf_sup_of_isSylowOf hPsyl hU2 hUGe (fun u _ => hPN u) hinf
      have hS₀S : P ⊔ U ≤ S := sup_le hPS ((omegaOne_le T).trans c.le_S)
      have hTGe : T ≤ Subgroup.normalizer (Ge : Set X) := by
        rw [← hT]; exact hUGe
      have hcard : Nat.card (Ge ⊔ U : Subgroup X) < Nat.card (G ⊔ T : Subgroup X) :=
        calc Nat.card (Ge ⊔ U : Subgroup X) = Nat.card (Ge ⊔ T : Subgroup X) := by rw [hT]
          _ < Nat.card (G ⊔ T : Subgroup X) := card_sup_lt c.frame hlt hTGe
      rcases c.sub_omegaOne htop IH hGeG hUGe ((hZP.trans (hPGe e)).trans le_rfl) hS₀ hS₀S
        hcard with hcomm | hN | ⟨y, -, B, -, hGeB, hZB, hfree⟩
      · exfalso
        rw [hO₁, Subgroup.map_bot, le_bot_iff,
          Subgroup.commutator_eq_bot_iff_le_centralizer] at hcomm
        exact hcen (Subgroup.le_centralizer_iff.mp ((hPGe e).trans hcomm))
      · rw [hO₁, Subgroup.map_bot, sup_bot_eq] at hN
        exact hN
      · exact (c.not_free hPn hP2 hZP hGeB hZB hfree).elim
    ·
      exfalso
      have heq : Ge = G := (eq_or_lt_of_le hGeG).resolve_right hlt
      apply hne
      apply c.caseOne_central htop hO IH hPn hPS hZP hT heT he1
      intro x hx
      have hx' : x ∈ Ge := heq ▸ hx
      have hc : π x * π e = π e * π x := Subgroup.mem_centralizer_singleton_iff.mp hx'.2
      apply (QuotientGroup.eq_one_iff _).mp
      show π (x * e * x⁻¹ * e⁻¹) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc, mul_inv_cancel_right,
        mul_inv_cancel]
  have hEne : ∃ e ∈ E, e ≠ 1 := by
    by_contra h
    push Not at h
    have hEbot : E = ⊥ := eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (h x hx)
    rw [hEbot, Subgroup.card_bot] at hE4
    norm_num at hE4
  obtain ⟨e₀, he₀E, he₀1⟩ := hEne
  have hPV : P ≤ G ⊓ Subgroup.normalizer (V : Set X) :=
    le_inf hPG ((hPGe e₀).trans (hGe e₀ he₀E he₀1))
  have hEb4 : Nat.card (E.map π) = 4 := by
    rw [card_map_eq_of_ker π fun x hx h1 => ?_, hE4]
    have hxP : x ∈ P := (QuotientGroup.eq_one_iff x).mp h1
    have hx' : x ∈ T ⊓ G := ⟨hET hx, hPG hxP⟩
    rw [c.frame.inf_eq_bot] at hx'
    exact hx'
  have hEbel : Open.IsElemAbelian 2 (E.map π) := by
    have : IsMulCommutative E := hEel.1
    refine ⟨inferInstance, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hEel.2 x hx, map_one]
  have hEbN : E.map π ≤ Subgroup.normalizer ((G.map π : Subgroup (X ⧸ P)) : Set (X ⧸ P)) :=
    (Subgroup.map_mono (hET.trans c.frame.le_normalizer)).trans (Subgroup.le_normalizer_map _)
  have hGbodd : Odd (Nat.card (G.map π)) := by
    have hrel := Subgroup.relIndex_ker (K := G) π
    rw [hkerπ] at hrel
    rw [← hrel]
    exact Nat.not_even_iff_odd.mp fun h => hodd G le_rfl (even_iff_two_dvd.mp h)
  have hgen : G.map π ≤ (G ⊓ Subgroup.normalizer (V : Set X)).map π := by
    apply le_of_centralizers_le hEb4 hEbel hEbN hGbodd
    rintro _ ⟨e, heE, rfl⟩ he1
    have he1' : e ≠ 1 := fun h => he1 (by rw [h, map_one])
    rintro _ ⟨⟨x, hxG, rfl⟩, hxc⟩
    exact Subgroup.mem_map_of_mem π ⟨hxG, hGe e heE he1' ⟨hxG, hxc⟩⟩
  apply hne
  have h1 : G ≤ ((G ⊓ Subgroup.normalizer (V : Set X)).map π).comap π := fun x hx =>
    hgen (Subgroup.mem_map_of_mem π hx)
  rw [Subgroup.comap_map_eq, hkerπ, sup_eq_left.mpr hPV] at h1
  exact h1.trans inf_le_right

theorem caseOne (c : Conf46 G T S Q H g) (htop : G ⊔ T = ⊤) (hO : CFSG.oddCore G = ⊥)
    (IH : IH46 (Nat.card (G ⊔ T : Subgroup X))) {D : Subgroup X}
    (hZD : omegaOne ((T ⊔ rightConjugate T g) ⊓ G) ≤ D) (hDS : D ≤ S ⊓ G)
    (hDN : G ≤ Subgroup.normalizer (D : Set X)) :
    G ⊔ T ≤ Subgroup.normalizer ((T ⊔ rightConjugate T g : Subgroup X) : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply c.normalizer_W_of_omegaOne htop hO IH
  set U := omegaOne T with hUdef
  set Z₁ := omegaOne ((T ⊔ rightConjugate T g) ⊓ G) with hZ₁def
  have hUT : U ≤ T := omegaOne_le T
  have hGn : G.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← htop]
    exact sup_le Subgroup.le_normalizer c.frame.le_normalizer
  set P := pCoreOf 2 G with hPdef
  have hPG : P ≤ G := CFSG.LieType.BorelTits.pCoreOf_le 2 G
  have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G
  have hPn : P.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
    exact (Subgroup.normalizer_eq_top_iff.mpr hGn).symm.le.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 G)
  have hPN : ∀ x : X, x ∈ Subgroup.normalizer (P : Set X) := fun x => by
    rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top x
  have hPS : P ≤ S := le_of_isSylowOf_of_le_normalizer c.sylowFrame.sylow hP2
    (hPG.trans le_sup_left) (fun x _ => hPN x)
  have hZP : Z₁ ≤ P := hZD.trans (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (hDS.trans inf_le_right) hDN (c.isPGroup_S.to_le (hDS.trans inf_le_left)))
  by_cases hcen : U ≤ Subgroup.centralizer (P : Set X)
  · exact c.normalizer_omegaOne_of_central htop hO hPn hPG hPS hZP hcen
  obtain ⟨K, hPK, hKG, hKn, hGUK, hKodd, -⟩ := c.exists_odd_extension htop hPn hPG hPS hZP
  have hKN : ∀ x : X, x ∈ Subgroup.normalizer (K : Set X) := fun x => by
    rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top x
  have hCK : K ⊓ Subgroup.centralizer (P : Set X) ≤ P :=
    inf_centralizer_le_of_odd hPn hKn hKG hO hP2 hKodd
  have hOK : CFSG.oddCore K = ⊥ :=
    oddCore_eq_bot_of_le_of_centralizer hPK le_rfl hP2 (fun x _ => hPN x) hCK
  have hLn : (K ⊔ U).Normal := c.normal_sup_omegaOne htop hKn hGUK
  have hinfKU : K ⊓ U = ⊥ := by
    rw [eq_bot_iff, ← c.frame.inf_eq_bot, inf_comm]
    exact inf_le_inf hUT hKG
  have hinfGT : G ⊓ T = ⊥ := by rw [inf_comm]; exact c.frame.inf_eq_bot
  have hcases : (K = G ∧ U = T) ∨
      Nat.card (K ⊔ U : Subgroup X) < Nat.card (G ⊔ T : Subgroup X) := by
    by_cases hKG' : K = G
    · by_cases hUT' : U = T
      · exact Or.inl ⟨hKG', hUT'⟩
      · right
        have hlt : Nat.card U < Nat.card T := Subgroup.card_lt_of_lt (lt_of_le_of_ne hUT hUT')
        rw [card_sup_of_le_normalizer (fun u _ => hKN u) hinfKU,
          card_sup_of_le_normalizer c.frame.le_normalizer hinfGT]
        calc Nat.card K * Nat.card U ≤ Nat.card G * Nat.card U :=
              Nat.mul_le_mul_right _ (Subgroup.card_le_of_le hKG)
          _ < Nat.card G * Nat.card T := Nat.mul_lt_mul_of_pos_left hlt Nat.card_pos
    · right
      calc Nat.card (K ⊔ U : Subgroup X) ≤ Nat.card (K ⊔ T : Subgroup X) :=
            Subgroup.card_le_of_le (sup_le_sup_left hUT K)
        _ < Nat.card (G ⊔ T : Subgroup X) :=
            card_sup_lt c.frame (lt_of_le_of_ne hKG hKG') (fun t _ => hKN t)
  rcases hcases with ⟨hKG', hUT'⟩ | hcard
  ·
    exact c.caseOne_odd htop hO IH hPn hPG hPS hZP hUT' (by rw [← hKG']; exact hKodd)
  ·
    have hSL : IsSylowOf 2 (S ⊓ (K ⊔ U)) (K ⊔ U) := c.sylowFrame.sylow.inf_of_le_normalizer
      (by rw [htop]; exact le_top) (by rw [Subgroup.normalizer_eq_top]; exact le_top)
    rcases c.sub_omegaOne htop IH hKG (fun u _ => hKN u) (hZP.trans hPK) hSL inf_le_left hcard
      with hcomm | hN | ⟨y, -, B, -, hKB, hZB, hfree⟩
    · exfalso
      rw [hOK, Subgroup.map_bot, le_bot_iff,
        Subgroup.commutator_eq_bot_iff_le_centralizer] at hcomm
      exact hcen (Subgroup.le_centralizer_iff.mp (hPK.trans hcomm))
    · rw [hOK, Subgroup.map_bot, sup_bot_eq] at hN
      exact c.le_normalizer_of_normal_sup htop (hZP.trans hPK) hLn
        (sup_le hN (fun u hu => Subgroup.le_normalizer (omegaOne_mono le_sup_left hu)))
    · exact (c.not_free hPn hP2 hZP hKB hZB hfree).elim

end Conf46

end CFSG.ComponentClassification.AschbacherTheorem3
