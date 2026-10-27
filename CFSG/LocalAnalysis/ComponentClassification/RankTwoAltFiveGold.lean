module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveUT
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XFinal

public section

open Subgroup Equiv CFSG.Open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoClassical

namespace CFSG.ComponentClassification.RankTwoAltFive

variable {G : Type} [Group G] [Finite G]


theorem mem_of_goldschmidt (hGold : Asc76X.GoldschmidtTheoremA) (hGs : IsSimpleGroup G)
    (hO : standardComponentOddCore G = ⊥) (hnot2 : ¬ IsPGroup 2 G) (S : Sylow 2 G)
    {W : Subgroup G} (hWS : W ≤ S) (hWab : IsMulCommutative W)
    (hWcl : ∀ a ∈ W, ∀ x : G, x⁻¹ * a * x ∈ (S : Subgroup G) → x⁻¹ * a * x ∈ W)
    (hW1 : W ≠ ⊥) {v : G} (hvS : v ∈ (S : Subgroup G)) (hv2 : v ^ 2 = 1) : v ∈ W := by
  have := hGs
  have hG := hGold G S W hWS hWab hWcl
  simp only at hG
  obtain ⟨ha, hb, -⟩ := hG
  have hWM : W ≤ normalClosure (W : Set G) := le_normalClosure
  have hMtop : normalClosure (W : Set G) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (normalClosure (W : Set G)) with h1 | h1
    · exact absurd (le_bot_iff.mp (h1 ▸ hWM)) hW1
    · exact h1
  have hOM : goldschmidtOddCore ↥(normalClosure (W : Set G)) = ⊥ := by
    rw [goldschmidtOddCore, sSup_eq_bot]
    rintro N ⟨hN, hodd⟩
    have hsurj : Function.Surjective (normalClosure (W : Set G)).subtype :=
      fun x => ⟨⟨x, hMtop ▸ mem_top x⟩, rfl⟩
    have hNn : (N.map (normalClosure (W : Set G)).subtype).Normal := hN.map _ hsurj
    have hNo : Odd (Nat.card (N.map (normalClosure (W : Set G)).subtype)) := by
      rwa [card_map_of_injective (Subgroup.subtype_injective _)]
    have h1 := RankTwoSporadic.le_standardComponentOddCore hNn hNo
    rw [hO, le_bot_iff] at h1
    exact (map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp h1
  have e : ↥(normalClosure (W : Set G)) ⧸ goldschmidtOddCore ↥(normalClosure (W : Set G)) ≃* G :=
    ((QuotientGroup.quotientMulEquivOfEq hOM).trans QuotientGroup.quotientBot).trans
      ((MulEquiv.subgroupCongr hMtop).trans Subgroup.topEquiv)
  have hQs : IsSimpleGroup (↥(normalClosure (W : Set G)) ⧸
      goldschmidtOddCore ↥(normalClosure (W : Set G))) := MulEquiv.isSimpleGroup e
  have hO2 : CFSG.Open.pCore 2 (↥(normalClosure (W : Set G)) ⧸
      goldschmidtOddCore ↥(normalClosure (W : Set G))) = ⊥ := by
    simp only [CFSG.pCore_eq_iSup, iSup_eq_bot]
    intro N hN hNp
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h1 | h1
    · exact h1
    · exfalso
      apply hnot2
      rw [h1] at hNp
      exact (hNp.of_equiv Subgroup.topEquiv).of_equiv e
  rw [hO2, bot_sup_eq] at ha
  rw [hO2, bot_sup_eq, ha] at hb
  have hvM : v ∈ normalClosure (W : Set G) := hMtop ▸ mem_top v
  have h1 : QuotientGroup.mk' (goldschmidtOddCore ↥(normalClosure (W : Set G))) ⟨v, hvM⟩ ∈
      map (QuotientGroup.mk' (goldschmidtOddCore ↥(normalClosure (W : Set G))))
        (W.subgroupOf (normalClosure (W : Set G))) := by
    rw [hb]
    refine Subgroup.subset_closure ⟨mem_inf.mpr ⟨⟨⟨v, hvM⟩, mem_subgroupOf.mpr hvS, rfl⟩,
      mem_top _⟩, ?_⟩
    rw [← map_pow]
    have : (⟨v, hvM⟩ : ↥(normalClosure (W : Set G))) ^ 2 = 1 := Subtype.ext (by simpa using hv2)
    rw [this, map_one]
  obtain ⟨w, hw, hwv⟩ := h1
  have h2 : w⁻¹ * ⟨v, hvM⟩ ∈ goldschmidtOddCore ↥(normalClosure (W : Set G)) := by
    rw [← QuotientGroup.eq]
    exact hwv
  rw [hOM, mem_bot, inv_mul_eq_one] at h2
  have h3 : (w : G) = v := congrArg Subtype.val h2
  rw [← h3]
  exact mem_subgroupOf.mp hw

namespace Setting310

variable {A R T V₀ : Subgroup G} {g : G} (h : Setting310 A R g T V₀)
include h

theorem conj_V₀_ne {z v : G} (hz : z ∈ V₀) (hz1 : z ≠ 1) (hv : v ∈ R ⊔ T) (hv0 : v ∉ V₀)
    (x : G) : x⁻¹ * z * x ≠ v := by
  intro he
  obtain ⟨y, -, hvy⟩ := h.loc.cover v hv hv0
  have h1 : z ∈ V₀ ⊓ rightConjugate (centralizer (A : Set G)) (y * x⁻¹) := by
    refine mem_inf.mpr ⟨hz, ?_⟩
    rw [← rightConjugate_mul]
    have h2 : z ∈ rightConjugate (rightConjugate R y) x⁻¹ := by
      rw [mem_rightConjugate_iff, inv_inv, he]
      exact hvy
    exact (map_mono (map_mono h.sylowR.le)) h2
  rw [h.loc.noRoot, mem_bot] at h1
  exact hz1 h1

section PStructure

variable {P : Subgroup G} (hP : IsSylowOf 2 P (transvGroup (R ⊔ T) V₀))
  (hPC : P ⊓ centralizer ((R ⊔ T : Subgroup G) : Set G) = R ⊔ T)
include hP hPC

theorem P_phi_surj {x : G} (hx : x ∈ P) (hxV : x ∉ R ⊔ T) {w : G} (hw : w ∈ V₀) :
    ∃ v ∈ R ⊔ T, v⁻¹ * (x * v * x⁻¹) = w := by
  let φ : ↥(R ⊔ T) →* ↥V₀ :=
    { toFun := fun v => ⟨(v : G)⁻¹ * (x * v * x⁻¹), P_mod hP hx v.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => by
        apply Subtype.ext
        have ha := P_mod hP hx a.2
        have hcomm := h.comm (h.V₀_le ha) (inv_mem b.2)
        simp only [coe_mul]
        calc ((a : G) * b)⁻¹ * (x * (a * b) * x⁻¹) =
            (b : G)⁻¹ * ((a : G)⁻¹ * (x * a * x⁻¹)) * (x * b * x⁻¹) := by group
          _ = ((a : G)⁻¹ * (x * a * x⁻¹)) * (b : G)⁻¹ * (x * b * x⁻¹) := by rw [← hcomm]
          _ = ((a : G)⁻¹ * (x * a * x⁻¹)) * ((b : G)⁻¹ * (x * b * x⁻¹)) := by group }
  have hker : Nat.card φ.ker = 4 := by
    have h1 : φ.ker = V₀.subgroupOf (R ⊔ T) := by
      ext v
      rw [MonoidHom.mem_ker, mem_subgroupOf]
      constructor
      · intro hv
        have h2 : (v : G)⁻¹ * (x * v * x⁻¹) = 1 := congrArg Subtype.val hv
        refine h.P_fixed hP hPC hx hxV v.2 ?_
        calc x * v * x⁻¹ = v * ((v : G)⁻¹ * (x * v * x⁻¹)) := by group
          _ = v := by rw [h2, mul_one]
      · intro hv
        apply Subtype.ext
        change (v : G)⁻¹ * (x * v * x⁻¹) = 1
        rw [P_comm_V₀ hP hv hx]
        group
    rw [h1, ← h.card_V₀]
    exact Nat.card_congr (subgroupOfEquivOfLe h.V₀_le).toEquiv
  have hsurj : Function.Surjective φ := by
    have h1 := Subgroup.card_ker_mul_card_range φ
    rw [hker, h.loc.card] at h1
    have h2 : Nat.card φ.range = 4 := by omega
    have htop : φ.range = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [h2, h.card_V₀])
    exact MonoidHom.range_eq_top.mp htop
  obtain ⟨v, hv⟩ := hsurj ⟨w, hw⟩
  exact ⟨v, v.2, congrArg Subtype.val hv⟩

theorem P_conj_coset {x : G} (hx : x ∈ P) (hxV : x ∉ R ⊔ T) {w : G} (hw : w ∈ V₀) :
    ∃ v ∈ R ⊔ T, v⁻¹ * x * v = x * w := by
  obtain ⟨v, hv, hvw⟩ := h.P_phi_surj hP hPC hx hxV hw
  refine ⟨v, hv, ?_⟩
  have h1 : x * v * x⁻¹ = v * w := by
    rw [← hvw]; group
  calc v⁻¹ * x * v = v⁻¹ * (x * v * x⁻¹) * x := by group
    _ = w * x := by rw [h1]; group
    _ = x * w := (P_comm_V₀ hP hw hx).symm

theorem P_invol_conj {c c' : G} (hc : c ∈ P) (hcV : c ∉ R ⊔ T) (hc2 : c * c = 1)
    (hc' : c' ∈ P) (hc'V : c' ∉ R ⊔ T) (hc'2 : c' * c' = 1) : ∃ x : G, x⁻¹ * c * x = c' := by
  obtain ⟨eA⟩ := h.equiv
  have hR2 : ∀ x ∈ R, x * x = 1 := fun x hx => h.mul_self (mem_sup_left hx)
  obtain ⟨b₀, hb₀A, hb₀N, -, hb₀tr, -⟩ := exists_klein_three eA h.V₀_le_A h.card_V₀
  have hb₀R : b₀ ∈ centralizer (R : Set G) := le_centralizer_iff.mp h.sylowR.le hb₀A
  have hb₀V := h.mem_normalizer_V (centralizer_le_normalizer _ hb₀R) hb₀N
  obtain ⟨p, hp, hpb⟩ := exists_mul_mem_normalizer hP (h.le_normalizer_transvGroup hb₀V)
  set b := p * b₀ with hbdef
  obtain ⟨r₀, hr₀, hr₀1, -⟩ := exists_ne_one_ne h.cardR hR2 (one_mem R)
  set f := transvHom (T := T) (V₀ := V₀) hr₀ with hf
  have hfeq := h.transvHom_eq_iff hr₀ hr₀1
  have hPP₀ : P ≤ transvGroup (R ⊔ T) V₀ := hP.le
  have hbP : ∀ y ∈ P, b⁻¹ * y * b ∈ P := fun y hy => by
    have := (mem_normalizer_iff.mp (inv_mem hpb) y).mp hy
    simpa using this
  have hb₀r : b₀⁻¹ * r₀ = r₀ * b₀⁻¹ := (mem_centralizer_iff.mp (inv_mem hb₀R) r₀ hr₀).symm
  have hfb : ∀ y (hy : y ∈ P), ((f ⟨b⁻¹ * y * b, hPP₀ (hbP y hy)⟩ : ↥V₀) : G) =
      b₀⁻¹ * ((f ⟨y, hPP₀ hy⟩ : ↥V₀) : G) * b₀ := by
    intro y hy
    have hm : p⁻¹ * y * p ∈ transvGroup (R ⊔ T) V₀ :=
      mul_mem (mul_mem (inv_mem hp) (hPP₀ hy)) hp
    have hm' : b₀⁻¹ * (p⁻¹ * y * p) * b₀⁻¹⁻¹ ∈ transvGroup (R ⊔ T) V₀ := by
      have := hPP₀ (hbP y hy)
      simpa [hbdef, mul_assoc] using this
    have h1 := transvHom_conj hr₀ hb₀r hm hm'
    have h2 : f ⟨p⁻¹ * y * p, hm⟩ = f ⟨y, hPP₀ hy⟩ := by
      have : (⟨p⁻¹ * y * p, hm⟩ : ↥(transvGroup (R ⊔ T) V₀)) =
          ⟨p, hp⟩⁻¹ * ⟨y, hPP₀ hy⟩ * ⟨p, hp⟩ := Subtype.ext (by simp)
      rw [this, map_mul, map_mul, map_inv]
      apply Subtype.ext
      have hcomm := h.comm (h.V₀_le (f ⟨y, hPP₀ hy⟩).2) (h.V₀_le (f ⟨p, hp⟩).2)
      simp only [coe_mul, InvMemClass.coe_inv]
      calc ((f ⟨p, hp⟩ : ↥V₀) : G)⁻¹ * ((f ⟨y, hPP₀ hy⟩ : ↥V₀) : G) * ((f ⟨p, hp⟩ : ↥V₀) : G) =
          ((f ⟨p, hp⟩ : ↥V₀) : G)⁻¹ * (((f ⟨y, hPP₀ hy⟩ : ↥V₀) : G) *
            ((f ⟨p, hp⟩ : ↥V₀) : G)) := by group
        _ = ((f ⟨y, hPP₀ hy⟩ : ↥V₀) : G) := by rw [hcomm]; group
    have h3 : (⟨b⁻¹ * y * b, hPP₀ (hbP y hy)⟩ : ↥(transvGroup (R ⊔ T) V₀)) =
        ⟨b₀⁻¹ * (p⁻¹ * y * p) * b₀⁻¹⁻¹, hm'⟩ := Subtype.ext (by simp [hbdef, mul_assoc])
    rw [h3, hf, h1, ← hf, h2, inv_inv]
  have hbkP : ∀ (k : ℕ) {y : G}, y ∈ P → (b ^ k)⁻¹ * y * b ^ k ∈ P := by
    intro k
    induction k with
    | zero => intro y hy; simpa using hy
    | succ k ih =>
      intro y hy
      have := hbP _ (ih hy)
      simpa [pow_succ, mul_assoc] using this
  have hfbk : ∀ (k : ℕ) (y : G) (hy : y ∈ P),
      ((f ⟨(b ^ k)⁻¹ * y * b ^ k, hPP₀ (hbkP k hy)⟩ : ↥V₀) : G) =
        (b₀ ^ k)⁻¹ * ((f ⟨y, hPP₀ hy⟩ : ↥V₀) : G) * b₀ ^ k := by
    intro k
    induction k with
    | zero => intro y hy; simp
    | succ k ih =>
      intro y hy
      have e : (⟨(b ^ (k + 1))⁻¹ * y * b ^ (k + 1), hPP₀ (hbkP (k + 1) hy)⟩ :
          ↥(transvGroup (R ⊔ T) V₀)) =
          ⟨b⁻¹ * ((b ^ k)⁻¹ * y * b ^ k) * b, hPP₀ (hbP _ (hbkP k hy))⟩ :=
        Subtype.ext (by simp [pow_succ, mul_assoc])
      rw [e, hfb _ (hbkP k hy), ih y hy, pow_succ]
      group
  have hne : ∀ y (hy : y ∈ P), y ∉ R ⊔ T → (f ⟨y, hPP₀ hy⟩ : ↥V₀) ≠ 1 := by
    intro y hy hyV he
    apply hyV
    rw [← hPC]
    refine mem_inf.mpr ⟨hy, ?_⟩
    have := (hfeq ⟨y, hPP₀ hy⟩ 1).mp (by rw [he, map_one])
    simpa using this
  obtain ⟨k, hk⟩ := hb₀tr _ (f ⟨c, hPP₀ hc⟩).2 _ (f ⟨c', hPP₀ hc'⟩).2
    (fun he => hne c hc hcV (Subtype.ext he)) (fun he => hne c' hc' hc'V (Subtype.ext he))
  set y := (b ^ k)⁻¹ * c * b ^ k with hy
  have hyP : y ∈ P := hbkP k hc
  have hfy : f ⟨y, hPP₀ hyP⟩ = f ⟨c', hPP₀ hc'⟩ := by
    apply Subtype.ext
    rw [hfbk k c hc]
    exact hk
  have hyc' : y⁻¹ * c' ∈ R ⊔ T := by
    rw [← hPC]
    refine mem_inf.mpr ⟨mul_mem (inv_mem hyP) hc', ?_⟩
    have := (hfeq _ _).mp hfy
    simpa using this
  have hyV : y ∉ R ⊔ T := fun hyV => by
    have h1 := hne c' hc' hc'V
    rw [← hfy] at h1
    apply h1
    have h2 : y ∈ centralizer ((R ⊔ T : Subgroup G) : Set G) := by
      rw [← hPC] at hyV
      exact (mem_inf.mp hyV).2
    exact (hfeq _ 1).mpr (by simpa using h2) |>.trans (map_one f)
  have hy2 : y * y = 1 := by
    rw [hy]
    calc (b ^ k)⁻¹ * c * b ^ k * ((b ^ k)⁻¹ * c * b ^ k) = (b ^ k)⁻¹ * (c * c) * b ^ k := by
          group
      _ = 1 := by rw [hc2]; group
  have hv0 : y⁻¹ * c' ∈ V₀ := by
    refine h.P_invol_coset hP hPC hyP hyV hy2 hyc' ?_
    calc y * (y⁻¹ * c') * (y * (y⁻¹ * c')) = c' * c' := by group
      _ = 1 := hc'2
  obtain ⟨u, -, hu⟩ := h.P_conj_coset hP hPC hyP hyV hv0
  refine ⟨b ^ k * u, ?_⟩
  calc (b ^ k * u)⁻¹ * c * (b ^ k * u) = u⁻¹ * y * u := by rw [hy]; group
    _ = y * (y⁻¹ * c') := hu
    _ = c' := by group

theorem P_not_sylow (hGold : Asc76X.GoldschmidtTheoremA) (hGs : IsSimpleGroup G)
    (hIIa : ¬ centralizer (A : Set G) ⊓ normalizer (R : Set G) ≤ centralizer (R : Set G))
    (hP64 : Nat.card P = 64) (hVP : R ⊔ T ≤ P) (S : Sylow 2 G) : (S : Subgroup G) ≠ P := by
  intro hSP
  obtain ⟨V', hV'P, hV'e, hV'16, hinf, -, hV'inv, hV'mem⟩ :=
    h.exists_Vprime hP hPC hIIa hP64 hVP
  have hV₀V' : V₀ ≤ V' := hinf ▸ inf_le_right
  have hnot2 : ¬ IsPGroup 2 G := by
    intro h2
    obtain ⟨eA⟩ := h.equiv
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (h2.to_subgroup A)
    rw [Nat.card_congr eA.toEquiv, card_A5] at hk
    have h4 : ¬ (3 : ℕ) ∣ 2 ^ k := fun h5 =>
      absurd ((Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3) h5)) (by norm_num)
    exact h4 (hk ▸ (by norm_num : (3 : ℕ) ∣ 60))
  have hV₀1 : V₀ ≠ ⊥ := fun he => by
    have := h.card_V₀
    rw [he, card_bot] at this
    omega
  have hinvol : ∀ v ∈ R ⊔ T, v ^ 2 = 1 := fun v hv => by rw [sq]; exact h.mul_self hv
  have hsq : ∀ {x : G}, x * x = 1 → x ^ 2 = 1 := fun hx => by rw [sq]; exact hx
  by_cases hcase : ∃ c ∈ P, c ∉ R ⊔ T ∧ c * c = 1 ∧ ∃ z ∈ V₀, z ≠ 1 ∧ ∃ x : G, x⁻¹ * z * x = c
  ·
    obtain ⟨c, hcP, hcV, hc2, z, hz, hz1, x₀, hx₀⟩ := hcase
    have hcl : ∀ a ∈ V', ∀ x : G, x⁻¹ * a * x ∈ (S : Subgroup G) → x⁻¹ * a * x ∈ V' := by
      intro a ha x hx
      by_cases ha1 : a = 1
      · rw [ha1]; simp
      obtain ⟨ha2, haV⟩ := hV'mem a ha
      obtain ⟨z', hz', hz'1, y, hy⟩ : ∃ z' ∈ V₀, z' ≠ 1 ∧ ∃ y : G, y⁻¹ * z' * y = a := by
        by_cases haV' : a ∈ R ⊔ T
        · exact ⟨a, haV haV', ha1, 1, by group⟩
        · obtain ⟨u, hu⟩ := h.P_invol_conj hP hPC hcP hcV hc2 (hV'P ha) haV' ha2
          exact ⟨z, hz, hz1, x₀ * u, by rw [← hu, ← hx₀]; group⟩
      have hb : x⁻¹ * a * x = (y * x)⁻¹ * z' * (y * x) := by rw [← hy]; group
      rw [hSP] at hx
      by_cases hbV : x⁻¹ * a * x ∈ R ⊔ T
      · by_cases hb0 : x⁻¹ * a * x ∈ V₀
        · exact hV₀V' hb0
        · exact absurd hb (fun he => h.conj_V₀_ne hz' hz'1 hbV hb0 (y * x) he.symm)
      · refine hV'inv _ hx ?_ hbV
        calc x⁻¹ * a * x * (x⁻¹ * a * x) = x⁻¹ * (a * a) * x := by group
          _ = 1 := by rw [ha2]; group
    have hall : ∀ v ∈ R ⊔ T, v ∈ V' := fun v hv =>
      mem_of_goldschmidt hGold hGs h.oddCore hnot2 S (hSP ▸ hV'P) hV'e.1 hcl
        (fun he => hV₀1 (le_bot_iff.mp (he ▸ hV₀V'))) (hSP ▸ hVP hv) (hinvol v hv)
    have hVV₀ : R ⊔ T ≤ V₀ := fun v hv => hinf ▸ mem_inf.mpr ⟨hv, hall v hv⟩
    have := Subgroup.card_le_of_le hVV₀
    rw [h.loc.card, h.card_V₀] at this
    omega
  ·
    push Not at hcase
    have hcl : ∀ a ∈ V₀, ∀ x : G, x⁻¹ * a * x ∈ (S : Subgroup G) → x⁻¹ * a * x ∈ V₀ := by
      intro a ha x hx
      by_cases ha1 : a = 1
      · rw [ha1]; simp
      rw [hSP] at hx
      by_cases hbV : x⁻¹ * a * x ∈ R ⊔ T
      · by_contra hb0
        exact h.conj_V₀_ne ha ha1 hbV hb0 x rfl
      · exfalso
        refine hcase _ hx hbV ?_ a ha ha1 x rfl
        have ha2 := h.mul_self (h.V₀_le ha)
        calc x⁻¹ * a * x * (x⁻¹ * a * x) = x⁻¹ * (a * a) * x := by group
          _ = 1 := by rw [ha2]; group
    have hab : IsMulCommutative V₀ :=
      ⟨⟨fun a b => Subtype.ext (h.comm (h.V₀_le a.2) (h.V₀_le b.2))⟩⟩
    have hall : ∀ v ∈ R ⊔ T, v ∈ V₀ := fun v hv =>
      mem_of_goldschmidt hGold hGs h.oddCore hnot2 S (hSP ▸ (h.V₀_le.trans hVP)) hab hcl hV₀1
        (hSP ▸ hVP hv) (hinvol v hv)
    have := Subgroup.card_le_of_le (show R ⊔ T ≤ V₀ from hall)
    rw [h.loc.card, h.card_V₀] at this
    omega

end PStructure

end Setting310

end CFSG.ComponentClassification.RankTwoAltFive
