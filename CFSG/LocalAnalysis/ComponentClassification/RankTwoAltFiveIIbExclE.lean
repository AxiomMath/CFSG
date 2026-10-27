module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIbExclL
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIbCent

public section

open Subgroup CFSG.Open CFSG.Blueprint CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped commutatorElement

namespace CFSG.ComponentClassification.RankTwoAltFive

namespace Setting310

variable {G : Type} [Group G] [Finite G] {A R T V₀ : Subgroup G} {g : G}
  (h : Setting310 A R g T V₀)
include h

theorem exists_conj_mem_R_of_isRootInv {d : G} (hd : IsRootInv A d) (hd1 : d ≠ 1)
    (hd2 : d * d = 1) : ∃ y : G, y * d * y⁻¹ ∈ R ∧ y * d * y⁻¹ ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := hd
  rw [mem_rightConjugate_iff] at hc
  have hp : IsPGroup 2 (zpowers (c * d * c⁻¹)) := by
    apply isPGroup_zpowers_of_pow_eq_one (n := 1)
    rw [pow_one, sq]
    calc c * d * c⁻¹ * (c * d * c⁻¹) = c * (d * d) * c⁻¹ := by group
      _ = 1 := by rw [hd2]; group
  obtain ⟨Q, hQ, hdQ⟩ := exists_isSylowOf_le (zpowers_le.mpr hc) hp
  obtain ⟨k, -, hQk⟩ := Lemma22.exists_conj_eq_of_isSylowOf h.sylowR hQ
  have h1 : c * d * c⁻¹ ∈ Lemma34.conj R k := hQk ▸ hdQ (mem_zpowers _)
  rw [Lemma34.mem_conj_iff] at h1
  refine ⟨k⁻¹ * c, by rwa [show k⁻¹ * c * d * (k⁻¹ * c)⁻¹ = k⁻¹ * (c * d * c⁻¹) * k by group],
    fun he => hd1 ?_⟩
  calc d = (k⁻¹ * c)⁻¹ * (k⁻¹ * c * d * (k⁻¹ * c)⁻¹) * (k⁻¹ * c) := by group
    _ = 1 := by rw [he]; group

section PStructure

variable {P : Subgroup G} (hP : IsSylowOf 2 P (transvGroup (R ⊔ T) V₀))
  (hPC : P ⊓ centralizer ((R ⊔ T : Subgroup G) : Set G) = R ⊔ T)
include hP hPC

omit h hPC in
theorem isSylowOf_top_of_eps_one (hε : EpsOne (R ⊔ T) P)
    (hNP : ∀ n : G, n ∈ normalizer (P : Set G) → n ∈ normalizer ((R ⊔ T : Subgroup G) : Set G)) :
    IsSylowOf 2 P ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hε' : IsSylowOf 2 P (normalizer ((R ⊔ T : Subgroup G) : Set G)) := hε
  obtain ⟨S, hS, hPS⟩ := exists_isSylowOf_le le_top hP.isPGroup
  by_contra hne
  have hlt : P < S := lt_of_le_of_ne hPS fun he => hne (he ▸ hS)
  obtain ⟨n, hn, hnP⟩ := IsConcreteLE.exists_of_lt (lt_inf_normalizer hS.isPGroup hlt)
  obtain ⟨hnS, hnN⟩ := mem_inf.mp hn
  have hT2 : IsPGroup 2 (P ⊔ zpowers n : Subgroup G) :=
    hS.isPGroup.to_le (sup_le hPS (zpowers_le.mpr hnS))
  have heq := hε'.eq_of_le le_sup_left (sup_le hε'.le (zpowers_le.mpr (hNP n hnN))) hT2
  exact hnP (heq ▸ mem_sup_right (mem_zpowers n))

theorem false_of_V_closed (hGold : Asc76X.GoldschmidtTheoremA)
    (hP64 : Nat.card P = 64) (hS : IsSylowOf 2 P ⊤)
    (hcl : ∀ a ∈ R ⊔ T, ∀ y : G, y⁻¹ * a * y ∈ P → y⁻¹ * a * y ∈ R ⊔ T) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hSS⟩ : ∃ S : Sylow 2 G, (S : Subgroup G) = P := by
    have hc := hS.card_eq
    rw [Subgroup.card_top] at hc
    exact ⟨Sylow.ofCard _ hc, Sylow.coe_ofCard _ _⟩
  have hVP : R ⊔ T ≤ P := hPC ▸ inf_le_left
  have hV1 : R ⊔ T ≠ ⊥ := fun he => by
    have := h.loc.card
    rw [he, card_bot] at this
    omega
  obtain ⟨hVX, hinv⟩ := h.goldschmidt_X hGold S (hSS ▸ hVP) h.loc.elem.1
    (fun a ha y hy => hcl a ha y (hSS ▸ hy)) hV1
  have hXtop : rankTwoX A = ⊤ := by
    rw [← h.sup_top]
    exact (sup_eq_left.mpr (le_sup_left.trans hVX)).symm
  obtain ⟨p, hp, hpV⟩ : ∃ p ∈ P, p ∉ R ⊔ T := by
    by_contra hcon
    push Not at hcon
    have := card_le_of_le (show P ≤ R ⊔ T from hcon)
    rw [hP64, h.loc.card] at this
    omega
  obtain ⟨v, hv, hpv⟩ := h.P_exists_invol hP hPC hp hpV
  have hpvV : p * v ∉ R ⊔ T := fun he => hpV (by
    have := mul_mem he (inv_mem hv)
    rwa [mul_inv_cancel_right] at this)
  exact hpvV (hinv _ (hSS ▸ mul_mem hp (hVP hv)) (hXtop ▸ mem_top _) (by rw [sq]; exact hpv))

variable (hIIb : centralizer (A : Set G) ⊓ normalizer (R : Set G) ≤ centralizer (R : Set G))
  (hNA : normalizer (A : Set G) ≤ A ⊔ centralizer (A : Set G))

omit hP hPC in
include hIIb hNA in
theorem isSylowOf_centralizer_of_eps_one {r : G} (hr : r ∈ R) (hr1 : r ≠ 1) :
    IsSylowOf 2 (R ⊔ T) (centralizer ({r} : Set G)) := by
  have hrK : r ∈ centralizer (A : Set G) := h.sylowR.le hr
  have hr2 : r * r = 1 := h.mul_self (mem_sup_left hr)
  have hCN : centralizer ({r} : Set G) ≤ normalizer (A : Set G) := by
    have := centralizer_le_normalizer_conj h.hyp.standard 1
      (by rw [rightConjugate_one]; exact hrK) hr1 hr2
    rwa [rightConjugate_one] at this
  have hVC : R ⊔ T ≤ centralizer ({r} : Set G) := fun v hv =>
    mem_centralizer_singleton_iff.mpr (h.comm hv (mem_sup_left hr))
  have hV2 : IsPGroup 2 (R ⊔ T : Subgroup G) := IsPGroup.of_card (n := 4) (by rw [h.loc.card]; rfl)
  obtain ⟨S, hS, hVS⟩ := exists_isSylowOf_le hVC hV2
  have heq : S = R ⊔ T := by
    rw [← h.inf_sup_eq_of_le_centralizer hIIb hr hr1 hS.isPGroup hS.le hVS]
    exact (inf_eq_left.mpr (hS.le.trans (hCN.trans hNA))).symm
  rwa [← heq]

omit hP hPC in
include hIIb hNA in
theorem mul_self_eq_one_of_isRootInv {d : G} (hd : IsRootInv A d) (hd1 : d ≠ 1)
    (hd2 : d * d = 1) {u : G} (hu : u * d = d * u) (hu2 : IsPGroup 2 (zpowers u)) :
    u * u = 1 := by
  obtain ⟨y, hyR, hy1⟩ := h.exists_conj_mem_R_of_isRootInv hd hd1 hd2
  obtain ⟨n, hn⟩ := hu2 ⟨u, mem_zpowers u⟩
  have hn' : u ^ 2 ^ n = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  have hu' : y * u * y⁻¹ ∈ centralizer ({y * d * y⁻¹} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc y * u * y⁻¹ * (y * d * y⁻¹) = y * (u * d) * y⁻¹ := by group
      _ = y * (d * u) * y⁻¹ := by rw [hu]
      _ = y * d * y⁻¹ * (y * u * y⁻¹) := by group
  have hu'2 : IsPGroup 2 (zpowers (y * u * y⁻¹)) := by
    apply isPGroup_zpowers_of_pow_eq_one (n := n)
    rw [conj_pow, hn']
    group
  have h1 := mul_self_eq_one_of_isSylowOf (h.isSylowOf_centralizer_of_eps_one hIIb hNA hyR hy1)
    (fun e he => h.mul_self he) hu' hu'2
  calc u * u = y⁻¹ * (y * u * y⁻¹ * (y * u * y⁻¹)) * y := by group
    _ = 1 := by rw [h1]; group

omit h hPC in
theorem mem_centralizer_V₀_of_isPGroup (hS : IsSylowOf 2 P ⊤) {u : G}
    (huN : u ∈ normalizer (V₀ : Set G)) (hu2 : IsPGroup 2 (zpowers u)) :
    u ∈ centralizer (V₀ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPC₀ : P ≤ centralizer (V₀ : Set G) := fun p hp => (mem_transvGroup.mp (hP.le hp)).2.1
  have hPN : IsSylowOf 2 P (normalizer (V₀ : Set G)) :=
    hS.of_le (hPC₀.trans (centralizer_le_normalizer _)) le_top
  obtain ⟨Q, hQ, huQ⟩ := exists_isSylowOf_le (zpowers_le.mpr huN) hu2
  obtain ⟨c, hc, hQc⟩ := Lemma22.exists_conj_eq_of_isSylowOf hPN hQ
  have h1 : u ∈ Lemma34.conj P c := hQc ▸ huQ (mem_zpowers u)
  rw [Lemma34.mem_conj_iff] at h1
  have h2 := hPC₀ h1
  rw [mem_centralizer_iff] at h2 ⊢
  intro w hw
  have hw' : c⁻¹ * w * c ∈ V₀ := by
    have := (mem_normalizer_iff.mp (inv_mem hc) w).mp hw
    rwa [inv_inv] at this
  have h3 := h2 _ hw'
  calc w * u = c * (c⁻¹ * w * c * (c⁻¹ * u * c)) * c⁻¹ := by group
    _ = c * (c⁻¹ * u * c * (c⁻¹ * w * c)) * c⁻¹ := by rw [h3]
    _ = u * w := by group

theorem exists_mem_centralizer_sq_ne_one (hm : MType (R ⊔ T) P) {c : G} (hc : c ∈ P)
    (hcV : c ∉ R ⊔ T) (hc2 : c * c = 1) :
    ∃ y ∈ P, y ∉ R ⊔ T ∧ c⁻¹ * y ∉ R ⊔ T ∧ y * c = c * y ∧ y * y ≠ 1 := by
  have hVP : R ⊔ T ≤ P := hPC ▸ inf_le_left
  obtain ⟨b₀, b, hb₀N, hb₀3, hb₀tr, hbP, hbV, -, hbc⟩ := h.exists_b hP hPC
  have hc₂P : b * c * b⁻¹ ∈ P := (mem_normalizer_iff.mp hbP c).mp hc
  have hc₂V : b * c * b⁻¹ ∉ R ⊔ T := fun he => hcV ((mem_normalizer_iff.mp hbV c).mpr he)
  have hcc₂ : c⁻¹ * (b * c * b⁻¹) ∉ R ⊔ T :=
    h.inv_mul_b_conj_not_mem hP hPC hb₀N hb₀3 hb₀tr hbP hbc hc hcV
  have hc₂2 : b * c * b⁻¹ * (b * c * b⁻¹) = 1 := by
    calc b * c * b⁻¹ * (b * c * b⁻¹) = b * (c * c) * b⁻¹ := by group
      _ = 1 := by rw [hc2]; group
  set c₂ := b * c * b⁻¹ with hc₂def
  have hw := h.commP_mem hP hPC hc hc₂P
  have hw1 : ⁅c, c₂⁆ ≠ 1 := fun he =>
    hm c hc c₂ hc₂P hcV hc₂V hc2 hc₂2 hcc₂ (commutatorElement_eq_one_iff_mul_comm.mp he)
  obtain ⟨r, hr, hcr⟩ := h.exists_commP_eq hP hPC hc hcV hw
  have hrP : r ∈ P := hVP (mem_sup_left hr)
  have hw2 : ⁅c, c₂⁆ * ⁅c, c₂⁆ = 1 := h.commP_mul_self hP hPC hc hc₂P
  have hyP : c₂ * r ∈ P := mul_mem hc₂P hrP
  have hyV : c₂ * r ∉ R ⊔ T := fun he => hc₂V (by
    have := mul_mem he (inv_mem (mem_sup_left hr))
    rwa [mul_inv_cancel_right] at this)
  have hcy : c⁻¹ * (c₂ * r) ∉ R ⊔ T := fun he => hcc₂ (by
    have := mul_mem he (inv_mem (mem_sup_left hr))
    rwa [← mul_assoc, mul_inv_cancel_right] at this)
  have hcomm : ⁅c, c₂ * r⁆ = 1 := by
    rw [h.commP_mul_right hP hPC hc hc₂P hrP, hcr, hw2]
  have hyc : c₂ * r * c = c * (c₂ * r) :=
    (commutatorElement_eq_one_iff_mul_comm.mp hcomm).symm
  refine ⟨c₂ * r, hyP, hyV, hcy, hyc, fun hy2 => ?_⟩
  exact hm c hc (c₂ * r) hyP hcV hyV hc2 hy2 hcy hyc.symm

include hIIb hNA in
theorem not_isRootInv_of_mType (hm : MType (R ⊔ T) P) {c : G} (hc : c ∈ P) (hcV : c ∉ R ⊔ T)
    (hc2 : c * c = 1) : ¬ IsRootInv A c := by
  intro hroot
  obtain ⟨y, hyP, -, -, hyc, hy2⟩ := h.exists_mem_centralizer_sq_ne_one hP hPC hm hc hcV hc2
  have hc1 : c ≠ 1 := fun he => hcV (he ▸ one_mem _)
  exact hy2 (h.mul_self_eq_one_of_isRootInv hIIb hNA hroot hc1 hc2 hyc
    (hP.isPGroup.to_le (zpowers_le.mpr hyP)))

theorem not_isConj_of_mType (hm : MType (R ⊔ T) P) (hS : IsSylowOf 2 P ⊤) {w₀ c : G}
    (hw₀ : w₀ ∈ V₀) (hc : c ∈ P) (hcV : c ∉ R ⊔ T) (hc2 : c * c = 1) :
    ¬ IsConj w₀ c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hconj
  obtain ⟨g₀, hg₀⟩ := isConj_iff.mp hconj
  have hVP : R ⊔ T ≤ P := hPC ▸ inf_le_left
  have hPC₀ : P ≤ centralizer (V₀ : Set G) := fun p hp => (mem_transvGroup.mp (hP.le hp)).2.1
  have hPz : IsSylowOf 2 P (centralizer ({w₀} : Set G)) :=
    hS.of_le (fun p hp => mem_centralizer_singleton_iff.mpr
      ((mem_centralizer_iff.mp (hPC₀ hp) w₀ hw₀).symm)) le_top
  set Q := rightConjugate (P ⊓ centralizer ({c} : Set G)) g₀ with hQdef
  have hQz : Q ≤ centralizer ({w₀} : Set G) := by
    intro x hx
    rw [hQdef, mem_rightConjugate_iff] at hx
    obtain ⟨-, hxc⟩ := mem_inf.mp hx
    rw [mem_centralizer_singleton_iff] at hxc ⊢
    rw [← hg₀] at hxc
    calc x * w₀ = g₀⁻¹ * (g₀ * x * g₀⁻¹ * (g₀ * w₀ * g₀⁻¹)) * g₀ := by group
      _ = g₀⁻¹ * (g₀ * w₀ * g₀⁻¹ * (g₀ * x * g₀⁻¹)) * g₀ := by rw [hxc]
      _ = w₀ * x := by group
  have hQ2 : IsPGroup 2 Q := by
    rw [hQdef]
    exact (hP.isPGroup.to_le inf_le_left).map _
  obtain ⟨Q', hQ', hQQ'⟩ := exists_isSylowOf_le hQz hQ2
  obtain ⟨k, hk, hQ'k⟩ := Lemma22.exists_conj_eq_of_isSylowOf hPz hQ'
  obtain ⟨m, hmdef⟩ : ∃ m : G, m = g₀ * k := ⟨_, rfl⟩
  have hkw : k * w₀ * k⁻¹ = w₀ := by
    rw [mem_centralizer_singleton_iff.mp hk]
    group
  have hmw : m * w₀ * m⁻¹ = c := by
    rw [hmdef, ← hg₀]
    calc g₀ * k * w₀ * (g₀ * k)⁻¹ = g₀ * (k * w₀ * k⁻¹) * g₀⁻¹ := by group
      _ = g₀ * w₀ * g₀⁻¹ := by rw [hkw]
  have hCP : ∀ y ∈ P, y * c = c * y → m⁻¹ * y * m ∈ P := by
    intro y hy hyc
    have h1 : g₀⁻¹ * y * g₀ ∈ Q := by
      rw [hQdef, mem_rightConjugate_iff]
      rw [show g₀ * (g₀⁻¹ * y * g₀) * g₀⁻¹ = y by group]
      exact mem_inf.mpr ⟨hy, mem_centralizer_singleton_iff.mpr hyc⟩
    have h2 := hQQ' h1
    rw [hQ'k, Lemma34.mem_conj_iff] at h2
    rw [hmdef]
    simpa [mul_assoc] using h2
  obtain ⟨y, hyP, hyV, -, hyc, hy2⟩ := h.exists_mem_centralizer_sq_ne_one hP hPC hm hc hcV hc2
  have hwV₀ : y * y ∈ V₀ := h.P_mul_self_mem_V₀ hP hPC hyP
  have hmy := hCP y hyP hyc
  have hmwV₀ : m⁻¹ * (y * y) * m ∈ V₀ := by
    have := h.P_mul_self_mem_V₀ hP hPC hmy
    rwa [show m⁻¹ * y * m * (m⁻¹ * y * m) = m⁻¹ * (y * y) * m by group] at this
  obtain ⟨r, hr, hcr⟩ := h.exists_commP_eq hP hPC hc hcV hwV₀
  have hrP : r ∈ P := hVP (mem_sup_left hr)
  have hr2 : r * r = 1 := h.mul_self (mem_sup_left hr)
  have hrc : r * c * r⁻¹ = c * (y * y) := by
    rw [commutatorElement_def] at hcr
    have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
    calc r * c * r⁻¹ = (c * c) * r * c * r⁻¹ := by rw [hc2, one_mul]
      _ = c * (c * r * c⁻¹ * r⁻¹) := by rw [hci]; group
      _ = c * (y * y) := by rw [hcr]
  have hrw : r * (y * y) * r⁻¹ = y * y := by
    rw [P_comm_V₀ hP hwV₀ hrP]
    group
  set W := rightConjugate V₀ m⁻¹ with hWdef
  have hmemW : ∀ x : G, x ∈ W ↔ m⁻¹ * x * m ∈ V₀ := fun x => by
    rw [hWdef, mem_rightConjugate_iff, inv_inv]
  have hW4 : Nat.card W = 4 := by rw [hWdef, rightConjugate_card, h.card_V₀]
  have hW2 : ∀ x ∈ W, x * x = 1 := by
    intro x hx
    have h1 := h.mul_self (h.V₀_le ((hmemW x).mp hx))
    calc x * x = m * (m⁻¹ * x * m * (m⁻¹ * x * m)) * m⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hcW : c ∈ W := by
    rw [hmemW, ← hmw]
    rw [show m⁻¹ * (m * w₀ * m⁻¹) * m = w₀ by group]
    exact hw₀
  have hwW : y * y ∈ W := (hmemW _).mpr hmwV₀
  have hc1 : c ≠ 1 := fun he => hcV (he ▸ one_mem _)
  have hcw : c ≠ y * y := fun he => hcV (he ▸ h.V₀_le hwV₀)
  have hrW : ∀ x ∈ W, r * x * r⁻¹ ∈ W := by
    intro x hx
    rcases mem_four hW4 hW2 hcW hwW hc1 hy2 hcw hx with rfl | rfl | rfl | rfl
    · rw [mul_one, mul_inv_cancel]
      exact one_mem W
    · rw [hrc]
      exact mul_mem hcW hwW
    · rw [hrw]
      exact hwW
    · rw [show r * (c * (y * y)) * r⁻¹ = r * c * r⁻¹ * (r * (y * y) * r⁻¹) by group, hrc, hrw,
        mul_assoc, hW2 _ hwW, mul_one]
      exact hcW
  have huN : m⁻¹ * r * m ∈ normalizer (V₀ : Set G) := by
    have key : ∀ v ∈ V₀, m⁻¹ * r * m * v * (m⁻¹ * r * m)⁻¹ ∈ V₀ := by
      intro v hv
      have hvW : m * v * m⁻¹ ∈ W := by
        rw [hmemW, show m⁻¹ * (m * v * m⁻¹) * m = v by group]
        exact hv
      have := (hmemW _).mp (hrW _ hvW)
      rwa [show m⁻¹ * (r * (m * v * m⁻¹) * r⁻¹) * m = m⁻¹ * r * m * v * (m⁻¹ * r * m)⁻¹ by
        group] at this
    rw [mem_normalizer_iff]
    intro v
    refine ⟨key v, fun hv => ?_⟩
    have := key _ hv
    have hu1 : m⁻¹ * r * m * (m⁻¹ * r * m) = 1 := by
      calc m⁻¹ * r * m * (m⁻¹ * r * m) = m⁻¹ * (r * r) * m := by group
        _ = 1 := by rw [hr2]; group
    have e : m⁻¹ * r * m * (m⁻¹ * r * m * v * (m⁻¹ * r * m)⁻¹) * (m⁻¹ * r * m)⁻¹ = v := by
      rw [inv_eq_of_mul_eq_one_right hu1]
      calc m⁻¹ * r * m * (m⁻¹ * r * m * v * (m⁻¹ * r * m)) * (m⁻¹ * r * m) =
          (m⁻¹ * r * m * (m⁻¹ * r * m)) * v * (m⁻¹ * r * m * (m⁻¹ * r * m)) := by group
        _ = v := by rw [hu1]; group
    rwa [e] at this
  have hu2 : IsPGroup 2 (zpowers (m⁻¹ * r * m)) := by
    apply isPGroup_zpowers_of_pow_eq_one (n := 1)
    rw [pow_one, sq]
    calc m⁻¹ * r * m * (m⁻¹ * r * m) = m⁻¹ * (r * r) * m := by group
      _ = 1 := by rw [hr2]; group
  have huC := mem_centralizer_V₀_of_isPGroup hP hS huN hu2
  have h1 := mem_centralizer_iff.mp huC w₀ hw₀
  have h2 : r * c = c * r := by
    rw [← hmw]
    calc r * (m * w₀ * m⁻¹) = m * (m⁻¹ * r * m * w₀) * m⁻¹ := by group
      _ = m * (w₀ * (m⁻¹ * r * m)) * m⁻¹ := by rw [h1]
      _ = m * w₀ * m⁻¹ * r := by group
  apply hy2
  rw [← hcr, commutatorElement_def, ← h2]
  group

include hIIb in
theorem false_of_eps_one_mType (hGold : Asc76X.GoldschmidtTheoremA)
    (hP64 : Nat.card P = 64) (hε : EpsOne (R ⊔ T) P) (hm : MType (R ⊔ T) P) : False := by
  have hNA' := h.normalizer_le_sup_of_eps_one hP hε
  have hPV : R ⊔ T ≤ P := hPC ▸ inf_le_left
  have hS : IsSylowOf 2 P ⊤ := by
    refine isSylowOf_top_of_eps_one hP hε fun n hnN => ?_
    have hPn : rightConjugate P n = P := (rightConjugate_eq_self_iff _ n).mpr hnN
    have hVn : rightConjugate (R ⊔ T) n ≤ P := by
      rw [← hPn]
      exact map_mono hPV
    exact (rightConjugate_eq_self_iff _ n).mp (h.eq_of_elemAbelian_P_of_mType hP hPC hm hVn
      (isElemAbelian_rightConjugate h.loc.elem n) (by rw [rightConjugate_card, h.loc.card]))
  refine h.false_of_V_closed hP hPC hGold hP64 hS fun a ha y hy => ?_
  by_contra hyV
  have ha2 : y⁻¹ * a * y * (y⁻¹ * a * y) = 1 := by
    calc y⁻¹ * a * y * (y⁻¹ * a * y) = y⁻¹ * (a * a) * y := by group
      _ = 1 := by rw [h.mul_self ha]; group
  by_cases ha0 : a ∈ V₀
  · exact h.not_isConj_of_mType hP hPC hm hS ha0 hy hyV ha2
      (isConj_iff.mpr ⟨y⁻¹, by rw [inv_inv]⟩)
  · exact h.not_isRootInv_of_mType hP hPC hIIb hNA' hm hy hyV ha2
      ((h.isRootInv_of_mem_V ha ha0).conj y)

include hIIb hNA in
theorem not_isRootInv_of_mem_Vprime (hP64 : Nat.card P = 64) {V' : Subgroup G}
    (hV' : IsVprime (R ⊔ T) V₀ P V') {c : G} (hcV' : c ∈ V') (hcV₀ : c ∉ V₀) :
    ¬ IsRootInv A c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hroot
  have hV₀V' : V₀ ≤ V' := hV'.inf ▸ inf_le_right
  have hc1 : c ≠ 1 := fun he => hcV₀ (he ▸ one_mem _)
  have hc2 : c * c = 1 := by rw [← sq]; exact hV'.elem.2 c hcV'
  obtain ⟨y, hyR, hy1⟩ := h.exists_conj_mem_R_of_isRootInv hroot hc1 hc2
  have hSyl := h.isSylowOf_centralizer_of_eps_one hIIb hNA hyR hy1
  set Q := rightConjugate V' y⁻¹ with hQdef
  have hmemQ : ∀ x : G, x ∈ Q ↔ y⁻¹ * x * y ∈ V' := fun x => by
    rw [hQdef, mem_rightConjugate_iff, inv_inv]
  have hQC : Q ≤ centralizer ({y * c * y⁻¹} : Set G) := by
    intro x hx
    rw [hmemQ] at hx
    rw [mem_centralizer_singleton_iff]
    have h1 := congrArg Subtype.val (hV'.elem.1.is_comm.comm ⟨_, hx⟩ ⟨c, hcV'⟩)
    simp only [coe_mul] at h1
    calc x * (y * c * y⁻¹) = y * (y⁻¹ * x * y * c) * y⁻¹ := by group
      _ = y * (c * (y⁻¹ * x * y)) * y⁻¹ := by rw [h1]
      _ = y * c * y⁻¹ * x := by group
  have hQ16 : Nat.card Q = 16 := by rw [hQdef, rightConjugate_card, hV'.card]
  have hQ2 : IsPGroup 2 Q := IsPGroup.of_card (n := 4) (by rw [hQ16]; rfl)
  obtain ⟨Q', hQ', hQQ'⟩ := exists_isSylowOf_le hQC hQ2
  have hQ'16 : Nat.card Q' = 16 := by rw [hQ'.card_eq, ← hSyl.card_eq, h.loc.card]
  have hQeq : Q = Q' := eq_of_le_of_card_ge hQQ' (by rw [hQ16, hQ'16])
  obtain ⟨k, -, hk⟩ := Lemma22.exists_conj_eq_of_isSylowOf hSyl hQ'
  apply h.not_conj_Vprime hP hPC hIIb hP64 hV' (k⁻¹ * y)
  ext v
  have e1 : v ∈ V' ↔ y * v * y⁻¹ ∈ Q := by
    rw [hmemQ, show y⁻¹ * (y * v * y⁻¹) * y = v by group]
  rw [mem_rightConjugate_iff, e1, hQeq, hk, Lemma34.mem_conj_iff,
    show k⁻¹ * y * v * (k⁻¹ * y)⁻¹ = k⁻¹ * (y * v * y⁻¹) * k by group]

include hIIb in
theorem isSylowOf_top_of_eps_one_isVprime (hP64 : Nat.card P = 64) (hε : EpsOne (R ⊔ T) P)
    {V' : Subgroup G} (hV' : IsVprime (R ⊔ T) V₀ P V') : IsSylowOf 2 P ⊤ := by
  have hPV : R ⊔ T ≤ P := hPC ▸ inf_le_left
  have hV₀V' : V₀ ≤ V' := hV'.inf ▸ inf_le_right
  refine isSylowOf_top_of_eps_one hP hε fun n hnN => ?_
  have hPn : rightConjugate P n = P := (rightConjugate_eq_self_iff _ n).mpr hnN
  have hVn : rightConjugate (R ⊔ T) n ≤ P := by
    rw [← hPn]
    exact map_mono hPV
  rcases h.eq_or_eq_of_elemAbelian hP hPC hV'.inv hV₀V' hV'.card hVn
    (isElemAbelian_rightConjugate h.loc.elem n) (by rw [rightConjugate_card, h.loc.card])
    with h1 | h1
  · exact (rightConjugate_eq_self_iff _ n).mp h1
  · exact absurd h1 (h.not_conj_Vprime hP hPC hIIb hP64 hV' n)

include hIIb in
theorem false_of_eps_one_isVprime_of_not_conj
    (hGold : Asc76X.GoldschmidtTheoremA) (hP64 : Nat.card P = 64) (hε : EpsOne (R ⊔ T) P)
    {V' : Subgroup G} (hV' : IsVprime (R ⊔ T) V₀ P V')
    (hcase : ∀ c ∈ V', c ∉ V₀ → ∀ w ∈ V₀, w ≠ 1 → ¬ IsConj w c) : False := by
  have hNA' := h.normalizer_le_sup_of_eps_one hP hε
  have hS := h.isSylowOf_top_of_eps_one_isVprime hP hPC hIIb hP64 hε hV'
  refine h.false_of_V_closed hP hPC hGold hP64 hS fun a ha y hy => ?_
  by_contra hyV
  have ha2 : y⁻¹ * a * y * (y⁻¹ * a * y) = 1 := by
    calc y⁻¹ * a * y * (y⁻¹ * a * y) = y⁻¹ * (a * a) * y := by group
      _ = 1 := by rw [h.mul_self ha]; group
  have hcV' : y⁻¹ * a * y ∈ V' := hV'.inv _ hy ha2 hyV
  have hcV₀ : y⁻¹ * a * y ∉ V₀ := fun h0 => hyV (h.V₀_le h0)
  by_cases ha0 : a ∈ V₀
  · have ha1 : a ≠ 1 := fun he => hyV (by rw [he]; group; exact one_mem _)
    exact hcase _ hcV' hcV₀ a ha0 ha1 (isConj_iff.mpr ⟨y⁻¹, by rw [inv_inv]⟩)
  · exact h.not_isRootInv_of_mem_Vprime hP hPC hIIb hNA' hP64 hV' hcV' hcV₀
      ((h.isRootInv_of_mem_V ha ha0).conj y)

end PStructure

end Setting310

end CFSG.ComponentClassification.RankTwoAltFive
