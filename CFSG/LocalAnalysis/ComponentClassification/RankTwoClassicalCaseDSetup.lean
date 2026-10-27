module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalDiag
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAlpha
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalChoice
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalVData

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G]

namespace ClassicalModel

variable {A : Subgroup G}

theorem mem_of_suzukiType (D : ClassicalModel A) {x : G} {L : Letter} {ℓ : ℕ}
    (h : D.SuzukiType x L ℓ) : x ∈ A ∧ orderOf x = 2 := by
  cases D with
  | linear => exact h.elim
  | unitary => exact h.elim
  | symplectic =>
    obtain ⟨h2, M, hM, -⟩ := h
    exact ⟨hM.1, h2⟩
  | orthPlus =>
    obtain ⟨h2, M, hM, -⟩ := h
    exact ⟨hM.1, h2⟩
  | orthMinus =>
    obtain ⟨h2, M, hM, -⟩ := h
    exact ⟨hM.1, h2⟩

theorem isPrimary_of_suzukiType_b_one (D : ClassicalModel A) (hfam : D.family = .symplectic)
    {x : G} (h : D.SuzukiType x .b 1) : D.IsPrimary x := by
  cases D with
  | linear => exact h.elim
  | unitary => exact h.elim
  | symplectic =>
    obtain ⟨h2, M, hM, hM2, hr, -⟩ := h
    exact ⟨h2, M, hM, hM2, hr⟩
  | orthPlus => simp [family] at hfam
  | orthMinus => simp [family] at hfam

theorem suzukiType_conj_iff (D : ClassicalModel A) {x b : G} {L : Letter} {ℓ : ℕ} (hb : b ∈ A) :
    D.SuzukiType (b * x * b⁻¹) L ℓ ↔ D.SuzukiType x L ℓ := by
  refine ⟨fun h => ?_, fun h => D.suzukiType_conj h hb⟩
  have h1 := D.suzukiType_conj h (inv_mem hb)
  rwa [show b⁻¹ * (b * x * b⁻¹) * b⁻¹⁻¹ = x by group] at h1

theorem alpha_eq_of_mem [Finite G] (D : ClassicalModel A) (hfam : D.family = .symplectic)
    (hZ : Odd (Nat.card (center ↥A))) {x : G} (hx : x ∈ A) (hx2 : orderOf x = 2) {y : G}
    (hy : y ∈ D.alpha x) (hy1 : y ≠ 1) : D.alpha y = D.alpha x := by
  have hxZ := not_mem_center_of_orderOf_eq_two hZ hx hx2
  have hx2' : x ^ 2 = 1 := by rw [← hx2]; exact pow_orderOf_eq_one x
  obtain ⟨hle, hyA, hy2⟩ : D.alpha y ≤ D.alpha x ∧ y ∈ A ∧ orderOf y = 2 := by
    cases D with
    | linear => simp [family] at hfam
    | unitary => simp [family] at hfam
    | orthPlus => simp [family] at hfam
    | orthMinus => simp [family] at hfam
    | symplectic n m hn hm hnm K hK e =>
      have := charP_two_of_card hK
      obtain ⟨M, hxM, hM2⟩ := exists_represents_orderOf_eq_two e hx hx2' hxZ
      have hMsq : M ^ 2 = 1 := by rw [← hM2]; exact pow_orderOf_eq_one M
      have hE := sub_one_mul_self hMsq
      have hH : ∀ a : K, unipGL ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) hE a ∈
          StatedSp n K := fun a => unipGL_mem_statedSp hxM.2.1 hMsq hE a
      obtain ⟨a, ha, hy2, hyN⟩ := exists_of_mem_alphaGroup hZ hxM hM2 hE hH hy hy1
      refine ⟨?_, hyN.1, orderOf_eq_prime hy2 hy1⟩
      have hM1 : M ≠ 1 := by
        intro h
        rw [h, orderOf_one] at hM2
        omega
      have hN2 : orderOf (unipGL ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) hE a) =
          2 := orderOf_unipGL hE ha (sub_one_ne_zero hM1)
      show alphaGroup e y ≤ alphaGroup e x
      rw [alphaGroup, alphaGroup, closure_le]
      rintro y' ⟨hk, M', N', hM', hM'2, hy'N', c, hc⟩
      obtain rfl := hyN.eq_of_orderOf_eq_two hM' hN2 hM'2
      apply Subgroup.subset_closure
      refine ⟨hk, M, N', hxM, hM2, hy'N', c * a, ?_⟩
      rw [hc, coe_unipGL, add_sub_cancel_left, smul_smul]
  exact eq_of_le_of_card_ge hle (by
    rw [D.card_alpha_symplectic hfam hZ hx hx2, D.card_alpha_symplectic hfam hZ hyA hy2])

end ClassicalModel

variable {A : Subgroup G}

structure Case23Setup (D : ClassicalModel A) (R T : Subgroup G) (p : G) (U W : Subgroup G)
    (y₁ y₂ : G) (ℓ : ℕ) : Prop where
  diag : DiagData A (jGroup A p) U W p y₁ y₂
  vdata : VData A R T p (jGroup A p) (diagSet (jGroup A p) U W)
  oddCenter : Odd (Nat.card (center ↥A))
  fused : ∀ t ∈ T, t ≠ 1 → ∀ t' ∈ T, t' ≠ 1 → ∀ p₁ ∈ A, t⁻¹ * p₁ ∈ R → ∀ p₂ ∈ A,
    t'⁻¹ * p₂ ∈ R → ∃ a ∈ A, a * p₁ * a⁻¹ = p₂
  card_U : Nat.card U = D.q
  card_W : Nat.card W = D.q
  prim_W : ∀ w ∈ W, w ≠ 1 → D.IsPrimary w
  types : (1 < ℓ ∧ D.SuzukiType p .b ℓ ∧ ∀ u ∈ U, u ≠ 1 → D.SuzukiType u .a (ℓ - 1)) ∨
    (D.SuzukiType p .c ℓ ∧ ∀ u ∈ U, u ≠ 1 → D.SuzukiType u .a ℓ)
  alpha_U : ∀ u ∈ U, u ≠ 1 → D.alpha u = U
  alpha_W : ∀ w ∈ W, w ≠ 1 → D.alpha w = W
  four_le : 4 ≤ D.q

variable [Finite G]

namespace Sec3

variable {R T : Subgroup G} {g : G} (hc : Sec3 A R T g)
include hc

theorem exists_case23Setup (I : Inputs74) (hTy : RankTwoClassicalEvenType (rankTwoQuot A))
    (D : ClassicalModel A) (hfam : D.family = .symplectic) (hq : 4 ≤ D.q) {t p : G}
    (ht : t ∈ T) (ht1 : t ≠ 1) (hp : p ∈ A) (hρ : t⁻¹ * p ∈ R) (h23 : Case23 D p) :
    ∃ (U W : Subgroup G) (y₁ y₂ : G) (ℓ : ℕ), Case23Setup D R T p U W y₁ y₂ ℓ := by
  have hOut := I.hOut ↥A hc.hyp.standard.1.1 hTy
  have hH := hc.hyp221 I.h32 I.h4 I.h34 I.h2 hOut I.hF hTy
  obtain ⟨hZ, hfus, -⟩ := I.h222.conclusion D hq hH
  have hle : ∀ t' ∈ T, ∀ p' ∈ A, t'⁻¹ * p' ∈ R → p' ∈ jGroup A p := by
    rcases hc.case222 I.h32 I.h4 I.h34 I.h2 hOut I.hF hTy I.h222 D hq ht ht1 hp hρ with
      ⟨h, -⟩ | hII
    · exact h
    · exfalso
      have := hII.2.2
      omega
  obtain ⟨ℓ, a, b, hcase, hb, hJ, hpa, hpb, hreg, hdiag⟩ := h23
  obtain ⟨-, y₁, hy₁, y₂, hy₂, hy₁U, hy₂W, hgen⟩ := hdiag
  have hWb : ∀ w ∈ D.alpha b, w ≠ 1 → D.SuzukiType w .b 1 := fun w hw hw1 =>
    D.suzukiType_of_mem_alpha hfam hZ hb hw hw1
  obtain ⟨ℓa, hℓa, hUa⟩ : ∃ ℓa, D.SuzukiType a .a ℓa ∧
      ∀ u ∈ D.alpha a, u ≠ 1 → D.SuzukiType u .a ℓa := by
    rcases hcase with ⟨-, -, ha⟩ | ⟨-, ha⟩
    · exact ⟨_, ha, fun u hu hu1 => D.suzukiType_of_mem_alpha hfam hZ ha hu hu1⟩
    · exact ⟨_, ha, fun u hu hu1 => D.suzukiType_of_mem_alpha hfam hZ ha hu hu1⟩
  obtain ⟨Lp, hLp, hpL⟩ : ∃ Lp : Letter, (Lp = .b ∧ 1 < ℓ ∨ Lp = .c) ∧ D.SuzukiType p Lp ℓ := by
    rcases hcase with ⟨hℓ, hpb', -⟩ | ⟨hpc, -⟩
    · exact ⟨.b, Or.inl ⟨rfl, hℓ⟩, hpb'⟩
    · exact ⟨.c, Or.inr rfl, hpc⟩
  have hpJ : p ∈ jGroup A p := hle t ht p hp hρ
  have hpΓ : p ∈ diagSet (jGroup A p) (D.alpha a) (D.alpha b) := ⟨hpJ, hpa, hpb⟩
  have hΓ : ∀ j ∈ diagSet (jGroup A p) (D.alpha a) (D.alpha b), D.SuzukiType j Lp ℓ := by
    intro j hj
    obtain ⟨c, hc', rfl⟩ := hreg.1 p hpΓ j hj
    exact D.suzukiType_conj hpL (mem_inf.mp hc').1
  have hUiff : ∀ x ∈ jGroup A p, x ≠ 1 → (x ∈ D.alpha a ↔ D.SuzukiType x .a ℓa) := by
    intro x hx hx1
    refine ⟨fun hxU => hUa x hxU hx1, fun hxa => ?_⟩
    by_contra hxU
    by_cases hxW : x ∈ D.alpha b
    · have h := (D.suzukiType_unique hxa (hWb x hxW hx1)).1
      cases h
    · have h := (D.suzukiType_unique hxa (hΓ x ⟨hx, hxU, hxW⟩)).1
      rcases hLp with ⟨rfl, -⟩ | rfl <;> cases h
  have hWiff : ∀ x ∈ jGroup A p, x ≠ 1 → (x ∈ D.alpha b ↔ D.SuzukiType x .b 1) := by
    intro x hx hx1
    refine ⟨fun hxW => hWb x hxW hx1, fun hxb => ?_⟩
    by_contra hxW
    by_cases hxU : x ∈ D.alpha a
    · have h := (D.suzukiType_unique (hUa x hxU hx1) hxb).1
      cases h
    · have h := D.suzukiType_unique hxb (hΓ x ⟨hx, hxU, hxW⟩)
      rcases hLp with ⟨rfl, hℓ⟩ | rfl
      · omega
      · have h1 := h.1
        cases h1
  have hinf : D.alpha a ⊓ D.alpha b = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [mem_bot]
    by_contra hx1
    obtain ⟨hxU, hxW⟩ := mem_inf.mp hx
    have h := (D.suzukiType_unique (hUa x hxU hx1) (hWb x hxW hx1)).1
    cases h
  have hcardU : Nat.card (D.alpha a) = D.q := by
    obtain ⟨haA, ha2⟩ := D.mem_of_suzukiType hℓa
    exact D.card_alpha_symplectic hfam hZ haA ha2
  have hcardW : Nat.card (D.alpha b) = D.q := by
    obtain ⟨hbA, hb2⟩ := D.mem_of_suzukiType hb
    exact D.card_alpha_symplectic hfam hZ hbA hb2
  have hdd : DiagData A (jGroup A p) (D.alpha a) (D.alpha b) p y₁ y₂ :=
    { J_eq := hJ
      inf_eq := hinf
      three_le_U := by omega
      three_le_W := by omega
      p_mem := hpΓ
      trans := fun j hj => hreg.1 p hpΓ j hj
      free := hreg.2
      y₁_mem := hy₁
      y₂_mem := hy₂
      y₁_cent := hy₁U
      y₂_cent := hy₂W
      gen := hgen
      sep := fun c hc' x hx hx1 hcx => by
        have hcx1 : c * x * c⁻¹ ≠ 1 := fun h => hx1 (by
          have := congrArg (fun z => c⁻¹ * z * c) h
          simpa [mul_assoc] using this)
        rw [hUiff x hx hx1, hUiff _ hcx hcx1, hWiff x hx hx1, hWiff _ hcx hcx1,
          D.suzukiType_conj_iff hc', D.suzukiType_conj_iff hc']
        exact ⟨Iff.rfl, Iff.rfl⟩ }
  have hsyl := I.hJS.jSylowAt D hc.hyp.standard.1 hZ hq hp (hc.orderOf_aPart I.h32 ht ht1 hρ)
  have hvd : VData A R T p (jGroup A p) (diagSet (jGroup A p) (D.alpha a) (D.alpha b)) :=
    { le := (jGroup_le A p).trans inf_le_left
      mem := hpJ
      ne_one := hc.aPart_ne_one ht ht1 hρ
      aPart_mem := ⟨t, ht, hρ⟩
      aPart_le := hle
      le_centralizer := fun b hb hbp =>
        inf_le_right.trans (centralizer_le (Set.singleton_subset_iff.mpr ⟨b, hb, rfl, hbp⟩))
      le_normalizer := le_normalizer_jGroup A p
      trans := hdd.trans
      free := fun a ha hap => hreg.2 a ha p hpΓ hap
      gen := hdd.le_closure
      sylow := fun x hx hxc hx2 => by
        have hx' : x ∈ centralizer (conjCommuting A p) := by
          rw [mem_centralizer_iff]
          rintro _ ⟨b, hb, rfl, hbp⟩
          exact (mem_centralizer_singleton_iff.mp (hxc b hb hbp)).symm
        exact mem_inf.mpr ⟨hsyl x hx hx' hx2, hx'⟩ }
  obtain ⟨haA, ha2⟩ := D.mem_of_suzukiType hℓa
  obtain ⟨hbA, hb2⟩ := D.mem_of_suzukiType hb
  refine ⟨D.alpha a, D.alpha b, y₁, y₂, ℓ, hdd, hvd, hZ, ?_, hcardU, hcardW,
    fun w hw hw1 => D.isPrimary_of_suzukiType_b_one hfam (hWb w hw hw1), ?_,
    fun u hu hu1 => D.alpha_eq_of_mem hfam hZ haA ha2 hu hu1,
    fun w hw hw1 => D.alpha_eq_of_mem hfam hZ hbA hb2 hw hw1, hq⟩
  · intro t₁ ht₁ ht₁1 t₂ ht₂ ht₂1 p₁ hp₁ hρ₁ p₂ hp₂ hρ₂
    exact hfus t₁ ht₁ ht₁1 t₂ ht₂ ht₂1 p₁ p₂ (hc.isAPart I.h32 ht₁ hp₁ hρ₁)
      (hc.isAPart I.h32 ht₂ hp₂ hρ₂)
  · rcases hcase with ⟨hℓ, hpb', ha⟩ | ⟨hpc, ha⟩
    · exact Or.inl ⟨hℓ, hpb', fun u hu hu1 => D.suzukiType_of_mem_alpha hfam hZ ha hu hu1⟩
    · exact Or.inr ⟨hpc, fun u hu hu1 => D.suzukiType_of_mem_alpha hfam hZ ha hu hu1⟩

theorem card_sec3V_eq (h32 : Lemma32) (h4 : Asc75Theorem4) (h34 : Asc08Lemma34)
    (hZ : Odd (Nat.card (center ↥A))) :
    Nat.card (sec3V R T) = Nat.card R * Nat.card ↥(sec3V R T ⊓ A) := by
  have h := (lemma35 h32 (lemma33Two_of h32 h4 h34) hc.hyp hc.sylowR hc.sylowT
    hc.le_centralizer).2.1
  have hle : sec3V R T ⊓ A ≤ normalizer (R : Set G) := by
    intro x hx
    refine centralizer_le_normalizer _ ?_
    rw [mem_centralizer_iff]
    intro r hr
    exact (hc.commute_of_mem (mem_inf.mp hx).2 hr).eq.symm
  have hbot : R ⊓ (sec3V R T ⊓ A) = ⊥ := by
    rw [eq_bot_iff, ← hc.R_inf_A hZ]
    exact inf_le_inf_left R inf_le_right
  conv_lhs => rw [h]
  exact card_sup_eq_mul hle hbot

theorem card_sec3V_eq' (h32 : Lemma32) (h4 : Asc75Theorem4) (h34 : Asc08Lemma34)
    (hZ : Odd (Nat.card (center ↥A))) :
    Nat.card (sec3V R T) = Nat.card T * Nat.card ↥(sec3V R T ⊓ rightConjugate A g) := by
  have h := (lemma35 h32 (lemma33Two_of h32 h4 h34) hc.hyp hc.sylowR hc.sylowT
    hc.le_centralizer).2.2
  have hle : sec3V R T ⊓ rightConjugate A g ≤ normalizer (T : Set G) := by
    intro x hx
    refine centralizer_le_normalizer _ ?_
    rw [mem_centralizer_iff]
    intro t ht
    have htK := hc.sylowT.le ht
    rw [← centralizer_rightConjugate] at htK
    exact (mem_centralizer_iff.mp htK x (mem_inf.mp hx).2).symm
  have hbot : T ⊓ (sec3V R T ⊓ rightConjugate A g) = ⊥ := by
    rw [eq_bot_iff, ← hc.T_inf_conj hZ]
    exact inf_le_inf_left T inf_le_right
  conv_lhs => rw [h]
  exact card_sup_eq_mul hle hbot

theorem card_inf_sec3V_swap (h32 : Lemma32) (h4 : Asc75Theorem4) (h34 : Asc08Lemma34)
    (hZ : Odd (Nat.card (center ↥A))) :
    Nat.card ↥(sec3V (rightConjugate T g⁻¹) (rightConjugate R g⁻¹) ⊓ A) =
      Nat.card ↥(sec3V R T ⊓ A) := by
  obtain ⟨w, hw⟩ := hc.exists_conj
  have h1 := hc.card_sec3V_eq h32 h4 h34 hZ
  have h2 := hc.card_sec3V_eq' h32 h4 h34 hZ
  rw [hc.card_eq] at h2
  have hpos : 0 < Nat.card R := Nat.card_pos
  have h3 : Nat.card ↥(sec3V R T ⊓ A) = Nat.card ↥(sec3V R T ⊓ rightConjugate A g) :=
    Nat.eq_of_mul_eq_mul_left hpos (h1.symm.trans h2)
  have hV : sec3V (rightConjugate T g⁻¹) (rightConjugate R g⁻¹) ⊓ A =
      rightConjugate (sec3V R T ⊓ rightConjugate A g) g⁻¹ := by
    rw [sec3V_rightConjugate, sec3V_symm hw, rightConjugate_inf,
      rightConjugate_rightConjugate_inv]
  rw [hV, rightConjugate_card, h3]

theorem card_inf_of_case14 (h32 : Lemma32) (h4 : Asc75Theorem4) (h34 : Asc08Lemma34)
    (D : ClassicalModel A) (hq : 4 ≤ D.q) {t p : G} (ht : t ∈ T) (ht1 : t ≠ 1) (hp : p ∈ A)
    (hρ : t⁻¹ * p ∈ R) (hle : ∀ t' ∈ T, ∀ p' ∈ A, t'⁻¹ * p' ∈ R → p' ∈ jGroup A p)
    (hI : Case1 D p ∨ Case4 D p) (hsyl : JSylowAt A p) :
    Nat.card ↥(sec3V R T ⊓ A) = D.q := by
  have hpJ := hle t ht p hp hρ
  have hp1 := hc.aPart_ne_one ht ht1 hρ
  obtain ⟨hreg, hcyc⟩ : RegularOn A (jGroup A p) (nonidentity (jGroup A p)) ∧
      AutCyclic A (jGroup A p) (D.q - 1) := by
    rcases hI with ⟨-, hreg, hcyc⟩ | ⟨-, hreg, hcyc⟩
    · exact ⟨hreg, hcyc⟩
    · exact ⟨hreg, hcyc⟩
  obtain ⟨y, hJ⟩ := hc.jData_of ht ht1 hp hρ hle hreg hcyc hsyl
  rw [hc.inf_sec3V_eq h32 h4 h34 hJ, card_eq_of_regularOn hreg hcyc hpJ hp1]
  omega

end Sec3

namespace Case23Setup

variable {D : ClassicalModel A} {R T : Subgroup G} {p : G} {U W : Subgroup G} {y₁ y₂ : G}
  {ℓ : ℕ} (hS : Case23Setup D R T p U W y₁ y₂ ℓ) {g : G} (hc : Sec3 A R T g)
  (h32 : Lemma32) (h4 : Asc75Theorem4) (h34 : Asc08Lemma34)
include hS hc h32 h4 h34

theorem inf_sec3V_eq : sec3V R T ⊓ A = jGroup A p :=
  hS.vdata.inf_sec3V_eq hc h32 h4 h34

theorem sec3V_eq_sup : sec3V R T = R ⊔ jGroup A p :=
  hS.vdata.sec3V_eq_sup hc h32 h4 h34

theorem jGroup_le_sec3V : jGroup A p ≤ sec3V R T := by
  rw [← hS.inf_sec3V_eq hc h32 h4 h34]
  exact inf_le_left

omit hS h4 h34 in
theorem isElemAbelian : IsElemAbelian 2 (sec3V R T) := by
  obtain ⟨w, hw⟩ := hc.exists_conj
  exact isElemAbelian_sec3V (hc.elemR h32) hc.le_centralizer ⟨w, hw⟩

omit hS h4 h34 in
theorem commute_of_mem_sec3V {x y : G} (hx : x ∈ sec3V R T) (hy : y ∈ sec3V R T) :
    x * y = y * x :=
  congrArg Subtype.val ((isElemAbelian hc h32).1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem commute_U_W {u w : G} (hu : u ∈ U) (hw : w ∈ W) : u * w = w * u :=
  commute_of_mem_sec3V hc h32 (hS.jGroup_le_sec3V hc h32 h4 h34 (hS.diag.U_le hu))
    (hS.jGroup_le_sec3V hc h32 h4 h34 (hS.diag.W_le hw))

theorem card_jGroup : Nat.card (jGroup A p) = D.q * D.q := by
  have hle : W ≤ normalizer (U : Set G) := by
    intro w hw
    refine centralizer_le_normalizer _ ?_
    rw [mem_centralizer_iff]
    intro u hu
    exact hS.commute_U_W hc h32 h4 h34 hu hw
  rw [hS.diag.J_eq, card_sup_eq_mul hle hS.diag.inf_eq, hS.card_U, hS.card_W]

theorem card_inf_sec3V : Nat.card ↥(sec3V R T ⊓ A) = D.q * D.q := by
  rw [hS.inf_sec3V_eq hc h32 h4 h34, hS.card_jGroup hc h32 h4 h34]

omit h32 h4 h34 in
theorem aPart_mem_diagSet {t' p' : G} (ht' : t' ∈ T) (ht'1 : t' ≠ 1) (hp' : p' ∈ A)
    (hρ' : t'⁻¹ * p' ∈ R) : p' ∈ diagSet (jGroup A p) U W := by
  obtain ⟨t, ht, hρ⟩ := hS.vdata.aPart_mem
  have ht1 : t ≠ 1 := by
    rintro rfl
    apply hS.vdata.ne_one
    have hpR : p ∈ R := by simpa using hρ
    have h1 : p ∈ R ⊓ A := mem_inf.mpr ⟨hpR, hS.vdata.le hS.vdata.mem⟩
    rwa [hc.R_inf_A hS.oddCenter, mem_bot] at h1
  obtain ⟨a, ha, hap⟩ :=
    hS.fused t ht ht1 t' ht' ht'1 p (hS.vdata.le hS.vdata.mem) hρ p' hp' hρ'
  have hp'J : p' ∈ jGroup A p := hS.vdata.aPart_le t' ht' p' hp' hρ'
  obtain ⟨hpJ, hpU, hpW⟩ := hS.diag.p_mem
  have hsep := hS.diag.sep a ha p hpJ hS.vdata.ne_one (by rw [hap]; exact hp'J)
  rw [hap] at hsep
  exact ⟨hp'J, fun h => hpU (hsep.1.mpr h), fun h => hpW (hsep.2.mpr h)⟩

end Case23Setup

end CFSG.ComponentClassification.RankTwoClassical
