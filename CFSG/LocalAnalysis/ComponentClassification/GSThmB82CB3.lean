module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81Fus2
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7S4f
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer Seven

namespace Eight2

variable {X : Type} [Group X] [Finite X]

theorem eight_dvd_ordL2_sq {q : ℕ} (hq : Odd q) : 8 ∣ Cat8.ordL2 (q ^ 2) := by
  have key : ∀ r : ℕ, r < 16 → r % 2 = 1 → r ^ 4 % 16 = 1 := by decide
  have hm : (q ^ 2) ^ 2 % 16 = 1 := by
    rw [← pow_mul, Nat.pow_mod]
    exact key _ (Nat.mod_lt _ (by norm_num)) (by have := Nat.odd_iff.mp hq; omega)
  have h16 : 16 ∣ (q ^ 2) ^ 2 - 1 := by
    have := Nat.dvd_sub_mod (n := 16) ((q ^ 2) ^ 2)
    rwa [hm] at this
  obtain ⟨j, hj⟩ := h16
  show 8 ∣ q ^ 2 * ((q ^ 2) ^ 2 - 1) / 2
  rw [hj, show q ^ 2 * (16 * j) = 2 * (8 * (q ^ 2 * j)) by ring,
    Nat.mul_div_cancel_left _ (by norm_num)]
  exact dvd_mul_right 8 _

theorem card_D_ge_eight (hJo : CFSec8JOrder) {h : Hyp52 X} (hc : h.Sec8Case) :
    8 ≤ Nat.card h.D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, p, f, hp, hp2, hf, -, hJ⟩ := Hyp52.Sec8Case.exists_params h hc
  have h8 : 2 ^ 3 ∣ Nat.card h.J := by
    refine dvd_trans ?_ h.card_Jbar_dvd
    rw [hJo _ p f hp hp2 hf hJ]
    exact eight_dvd_ordL2_sq (hp.odd_of_ne_two hp2).pow
  obtain ⟨T, hT⟩ := h.sec8_D_sylow
  have h2 := T.pow_dvd_card_of_pow_dvd_card h8
  rw [hT] at h2
  have h3 : Nat.card (h.D.subgroupOf h.J) = Nat.card h.D := by
    rw [← card_map_of_injective h.J.subtype_injective, subgroupOf_map_subtype,
      inf_eq_left.mpr inf_le_right]
  rw [h3] at h2
  exact Nat.le_of_dvd Nat.card_pos h2

theorem exists_central_inv_D {h : Hyp52 X} (h8 : 8 ≤ Nat.card h.D) :
    ∃ z ∈ h.D, z * z = 1 ∧ z ≠ 1 ∧ ∀ d ∈ h.D, z * d = d * z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD2 : IsPGroup 2 h.D := (Six.isPGroup_S h).to_le inf_le_left
  have hnt : Nontrivial h.D := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    omega
  have hZ := hD2.center_nontrivial
  have h2 : 2 ∣ Nat.card (center h.D) := by
    obtain ⟨k, hk⟩ := (hD2.to_subgroup (center h.D)).exists_card_eq
    have h1 : 1 < Nat.card (center h.D) := Finite.one_lt_card_iff_nontrivial.mpr hZ
    rw [hk] at h1 ⊢
    rcases k with _ | k
    · simp at h1
    · exact dvd_pow_self 2 (Nat.succ_ne_zero k)
  obtain ⟨⟨⟨z, hzD⟩, hzc⟩, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
  refine ⟨z, hzD, ?_, ?_, ?_⟩
  · have := pow_orderOf_eq_one (⟨⟨z, hzD⟩, hzc⟩ : center h.D)
    rw [hz, pow_two] at this
    exact congrArg (fun t : center h.D => ((t : h.D) : X)) this
  · intro h1
    have : (⟨⟨z, hzD⟩, hzc⟩ : center h.D) = 1 := Subtype.ext (Subtype.ext h1)
    rw [this, orderOf_one] at hz
    norm_num at hz
  · intro d hd
    have := Subgroup.mem_center_iff.mp hzc ⟨d, hd⟩
    exact (congrArg Subtype.val this).symm

structure ZData (h : Hyp52 X) where
  z : X
  hzD : z ∈ h.D
  hzz : z * z = 1
  hz1 : z ≠ 1
  hzP : z ∉ h.P
  hzS : ∀ t ∈ h.S, t * z = z * t
  hZDz : ∀ w ∈ h.D, (∀ d ∈ h.D, w * d = d * w) → w = 1 ∨ w = z
  h8 : 8 ≤ Nat.card (Dbar h)
  sylow : ∃ T : Sylow 2 (Jbar h), (T : Subgroup (Jbar h)) = Dbar h
  lie : ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ Blueprint.LieModel (Jbar h) .PSL 2 p f
  hZD : ∀ t ∈ Dbar h, t ∈ centralizer (Dbar h : Set (Jbar h)) →
    MulAut.conj t = 1 ∨ MulAut.conj t = rhoE h.J z
  hsq : ∃ t ∈ Dbar h, t * t ≠ 1 ∧ t * t ∈ centralizer (Dbar h : Set (Jbar h))
  hprod : ∀ t ∈ Dbar h, ∃ i ∈ Dbar h, ∃ j ∈ Dbar h, i * i = 1 ∧ j * j = 1 ∧ t = i * j
  hC4 : ∀ R : Subgroup (MulAut (Jbar h)), IsPGroup 2 R →
    R ≤ centralizer (innOf (Dbar h) : Set (MulAut (Jbar h))) → Nat.card R ≤ 4
  hJ8 : ∀ R : Subgroup (MulAut (Jbar h)), IsPGroup 2 R → innOf (Dbar h) ≤ R →
    ∀ E : Subgroup (MulAut (Jbar h)), E ≤ R → (∀ e ∈ E, e * e = 1) → Nat.card E = 8 →
      E ≤ innOf (Dbar h) ⊔ (R ⊓ centralizer (innOf (Dbar h) : Set (MulAut (Jbar h))))
  hRk : ∀ E : Subgroup (MulAut (Jbar h)), (∀ e ∈ E, e * e = 1) → Nat.card E ≤ 8

theorem exists_zData (hSy : CFL2Sylow) (hC : CFL2C) (hJ : CFL2J) (hRank : CFL2Rank)
    (hJo : CFSec8JOrder) {h : Hyp52 X} (hc : h.Sec8Case)
    (hZJ : center (h.J ⧸ pPrimeCore 2 h.J) = ⊥) : Nonempty (ZData h) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h8 := card_D_ge_eight hJo hc
  obtain ⟨T₀, hT₀, hT₀c⟩ := h.sec8_exists_sylow_Dbar
  obtain ⟨-, p, f, hp, hp2, hf, -, hJt⟩ := Hyp52.Sec8Case.exists_params h hc
  obtain ⟨p', f', hp', hp2', hf', hJL⟩ := lieModel_of_isSec8JType hp hp2 hf hJt
  have hT8 : 8 ≤ Nat.card T₀ := by
    have : Nat.card T₀ = Nat.card h.D := hT₀c
    omega
  obtain ⟨hZ2, hsq, hprod⟩ := hSy _ p' f' hp' hp2' hf' hJL T₀ hT8
  rw [hT₀] at hZ2 hsq hprod
  have hC4 := hC _ p' f' hp' hp2' hf' hJL T₀ hT8
  rw [hT₀] at hC4
  have hJ8 := hJ _ p' f' hp' hp2' hf' hJL T₀ hT8
  rw [hT₀] at hJ8
  have hRk := hRank _ p' f' hp' hp2' hf' hJL
  obtain ⟨z, hzD, hzz, hz1, hzc⟩ := exists_central_inv_D h8
  have hker : ¬ 2 ∣ Nat.card (QuotientGroup.mk' (pPrimeCore 2 ↥h.J)).ker := by
    rw [QuotientGroup.ker_mk']
    exact (Nat.prime_two.coprime_iff_not_dvd).mp (pPrimeCore_coprime_card (p := 2) (G := ↥h.J))
  have hinjOn := Eight.injOn_of_isPGroup hker
    ((h.isPGroup_S.to_le (inf_le_left : h.D ≤ h.S)).comap_subtype)
  have hinj : ∀ d₁ d₂ : X, ∀ (hd₁ : d₁ ∈ h.D) (hd₂ : d₂ ∈ h.D),
      QuotientGroup.mk' (pPrimeCore 2 ↥h.J) ⟨d₁, h.D_le_J hd₁⟩ =
        QuotientGroup.mk' (pPrimeCore 2 ↥h.J) ⟨d₂, h.D_le_J hd₂⟩ → d₁ = d₂ :=
    fun d₁ d₂ hd₁ hd₂ he => congrArg Subtype.val
      (hinjOn (mem_subgroupOf.mpr hd₁) (mem_subgroupOf.mpr hd₂) he)
  set zbar : Jbar h := ((⟨z, h.D_le_J hzD⟩ : ↥h.J) : Jbar h) with hzbar
  have hrz : rhoE h.J z = MulAut.conj zbar := rhoE_of_mem_J _
  have hcent : ∀ w (hw : w ∈ h.D), (∀ d ∈ h.D, w * d = d * w) →
      ((⟨w, h.D_le_J hw⟩ : ↥h.J) : Jbar h) ∈ Dbar h ⊓ centralizer (Dbar h : Set (Jbar h)) := by
    intro w hw hwc
    refine mem_inf.mpr ⟨mem_map_of_mem _ (mem_subgroupOf.mpr hw), ?_⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨⟨t, htJ⟩, ht, rfl⟩
    change QuotientGroup.mk' (pPrimeCore 2 ↥h.J) ⟨t, htJ⟩ *
        QuotientGroup.mk' (pPrimeCore 2 ↥h.J) ⟨w, h.D_le_J hw⟩ =
      QuotientGroup.mk' (pPrimeCore 2 ↥h.J) ⟨w, h.D_le_J hw⟩ *
        QuotientGroup.mk' (pPrimeCore 2 ↥h.J) ⟨t, htJ⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hwc t (mem_subgroupOf.mp ht)).symm
  have hzbarZ := hcent z hzD hzc
  have hzbar1 : zbar ≠ 1 := by
    intro h1
    apply hz1
    apply hinj z 1 hzD (one_mem _)
    rw [show (⟨(1 : X), h.D_le_J (one_mem _)⟩ : ↥h.J) = 1 from rfl, map_one]
    exact h1
  have hZDz : ∀ w ∈ h.D, (∀ d ∈ h.D, w * d = d * w) → w = 1 ∨ w = z := by
    intro w hw hwc
    rcases eq_one_or_of_card_two hZ2 hzbarZ (hcent w hw hwc) hzbar1 with h1 | h1
    · left
      apply hinj w 1 hw (one_mem _)
      rw [show (⟨(1 : X), h.D_le_J (one_mem _)⟩ : ↥h.J) = 1 from rfl, map_one]
      exact h1
    · exact Or.inr (hinj w z hw hzD h1)
  have hzS : ∀ t ∈ h.S, t * z = z * t := by
    intro t ht
    have hw : t * z * t⁻¹ ∈ h.D := h.sec8_conj_mem_D ht hzD
    have hwc : ∀ d ∈ h.D, t * z * t⁻¹ * d = d * (t * z * t⁻¹) := by
      intro d hd
      have hd' : t⁻¹ * d * t ∈ h.D := by
        have := h.sec8_conj_mem_D (inv_mem ht) hd
        rwa [inv_inv] at this
      have h1 := hzc _ hd'
      calc t * z * t⁻¹ * d = t * (z * (t⁻¹ * d * t)) * t⁻¹ := by group
        _ = t * ((t⁻¹ * d * t) * z) * t⁻¹ := by rw [h1]
        _ = d * (t * z * t⁻¹) := by group
    rcases hZDz _ hw hwc with h1 | h1
    · exfalso
      apply hz1
      calc z = t⁻¹ * (t * z * t⁻¹) * t := by group
        _ = 1 := by rw [h1]; group
    · calc t * z = t * z * t⁻¹ * t := by group
        _ = z * t := by rw [h1]
  have hzP : z ∉ h.P := fun hzP => hz1 (by
    have := h.D_inf_P_eq_bot hZJ ▸ mem_inf.mpr ⟨hzD, hzP⟩
    exact mem_bot.mp this)
  have hZD : ∀ t ∈ Dbar h, t ∈ centralizer (Dbar h : Set (Jbar h)) →
      MulAut.conj t = 1 ∨ MulAut.conj t = rhoE h.J z := by
    intro t ht htC
    rcases eq_one_or_of_card_two hZ2 hzbarZ (mem_inf.mpr ⟨ht, htC⟩) hzbar1 with h1 | h1
    · left
      rw [h1, map_one]
    · right
      rw [h1, hrz]
  exact ⟨{
    z := z
    hzD := hzD
    hzz := hzz
    hz1 := hz1
    hzP := hzP
    hzS := hzS
    hZDz := hZDz
    h8 := by
      have h8' := hT8
      rwa [hT₀] at h8'
    sylow := ⟨T₀, hT₀⟩
    lie := ⟨p', f', hp', hp2', hf', hJL⟩
    hZD := hZD
    hsq := hsq
    hprod := hprod
    hC4 := hC4
    hJ8 := hJ8
    hRk := hRk }⟩

end Eight2

end CFSG.ComponentClassification.GSThmB
