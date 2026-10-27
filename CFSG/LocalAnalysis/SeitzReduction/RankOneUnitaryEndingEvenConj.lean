module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingEvenCount
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingEven

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace U3EndingData

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T R₂ U₁ : Subgroup G}
  {s : G}

theorem map_conj_eq_of_le (hD : U3EndingData G L f t T R₂ U₁ s)
    {v : G} (hvT : v ∈ T) (hv2 : v ^ 2 = 1) (hvS : v ∉ szT₁ L T ⊔ zpowers t)
    {Y₁ Y₂ : Subgroup G} (hY : Y₁ ⊔ Y₂ = U₁) (hinf : Y₁ ⊓ Y₂ = ⊥)
    (hcomm : ∀ a ∈ Y₁, ∀ b ∈ Y₂, a * b = b * a)
    (ht₁ : ∀ a ∈ Y₁, t * a * t⁻¹ ∈ Y₂) (ht₂ : ∀ b ∈ Y₂, t * b * t⁻¹ ∈ Y₁) {P : Subgroup G}
    (hP2 : IsPGroup 2 P) (hUP : U₁ ≤ P) (hTP : T ≤ P) (hPN : P ≤ normalizer (U₁ : Set G))
    {g : G} (hle : U₁.map (MulAut.conj g).toMonoidHom ≤ P)
    (hnorm : P ≤ normalizer ((U₁.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) :
    U₁.map (MulAut.conj g).toMonoidHom = U₁ := by
  classical
  have h := hD.start
  have hS2 := hD.card_sylow
  have hR := hD.r2
  have hU := hD.u1
  set U' := U₁.map (MulAut.conj g).toMonoidHom with hU'def
  have htt : t * t = 1 := by rw [← sq]; exact hR.t_sq
  have htinv : t⁻¹ = t := hR.t_inv
  obtain ⟨htT, -⟩ := h.start_of_card_sylow hS2
  have htU : t ∈ normalizer (U₁ : Set G) := hPN (hTP htT)
  obtain ⟨E, _, _, _, σ, hEcard, hσq, hFcard, u, vc, hc, -⟩ :=
    h.exists_rootCoords_of_card_sylow hS2
  have hCt : ∀ y ∈ U₁, y * t = t * y → y ∈ szT₁ L T :=
    fun y hy hyt => hU.mem_szT₁_of_commute hR hy hyt
  have hT₁ : ∀ y ∈ szT₁ L T, y ∈ U₁ ∧ y * t = t * y :=
    fun y hy => ⟨hU.le (mem_sup_left hy), hR.t_comm y hy⟩
  have hY' : Y₂ ⊔ Y₁ = U₁ := by rw [sup_comm]; exact hY
  have hinf' : Y₂ ⊓ Y₁ = ⊥ := by rw [inf_comm]; exact hinf
  have hcomm' : ∀ a ∈ Y₂, ∀ b ∈ Y₁, a * b = b * a := fun a ha b hb => (hcomm b hb a ha).symm
  have hc₁ := hc.of_partner htt hY hinf hcomm ht₁ ht₂ hCt hT₁
  have hc₂ := hc.of_partner htt hY' hinf' hcomm' ht₂ ht₁ hCt hT₁
  have hq4 : 4 ≤ 2 ^ f :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.two_le
  have hY₁U : Y₁ ≤ U₁ := hY ▸ le_sup_left
  have hY₂U : Y₂ ≤ U₁ := hY ▸ le_sup_right
  have hU'U : U' ≤ normalizer (U₁ : Set G) := hle.trans hPN
  have hUU' : U₁ ≤ normalizer (U' : Set G) := hUP.trans hnorm
  have hinv : ∀ x ∈ U₁, x * x = 1 → x ∈ centralizer (U₁ : Set G) := fun x hx hxx =>
    mem_centralizer_of_mul_self_eq_one hc₁ hc₂ hY hinf hcomm hx hxx
  have hsq : ∀ x ∈ U₁, x * x ∈ centralizer (U₁ : Set G) := by
    intro x hx
    have hx2 : x * x ∈ R₂ := by rw [← sq]; exact hU.sq_mem x hx
    exact mem_centralizer_iff.mpr fun w hw =>
      (mem_centralizer_iff.mp (hU.le_centralizer hw) _ hx2).symm
  have hU'c : ∀ a ∈ U', ∀ b ∈ U', a * b * a⁻¹ * b⁻¹ * (a * b * a⁻¹ * b⁻¹) = 1 := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hr2 : (a * b * a⁻¹ * b⁻¹) * (a * b * a⁻¹ * b⁻¹) = 1 := by
      rw [← sq]
      exact hU.sq_R₂ _ (hU.comm_mem a ha b hb)
    calc g * a * g⁻¹ * (g * b * g⁻¹) * (g * a * g⁻¹)⁻¹ * (g * b * g⁻¹)⁻¹ *
          (g * a * g⁻¹ * (g * b * g⁻¹) * (g * a * g⁻¹)⁻¹ * (g * b * g⁻¹)⁻¹) =
          g * ((a * b * a⁻¹ * b⁻¹) * (a * b * a⁻¹ * b⁻¹)) * g⁻¹ := by group
      _ = 1 := by rw [hr2]; group
  have hcardU' : Nat.card U' = Nat.card U₁ :=
    card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
  obtain ⟨hCA₁, hCA₂, hna₁, hna₂⟩ :=
    hU.product_facts_of_card_sylow h hS2 hR hY hinf hcomm ht₁ ht₂
  obtain ⟨hne, -, hdich⟩ := map_conj_eq_or_eq hY hinf hcomm hCA₁ hCA₂ hna₁ hna₂ htt htU ht₁ ht₂
  set M₁ := U₁ ⊓ centralizer (Y₂ : Set G) with hM₁
  set M₂ := U₁ ⊓ centralizer (Y₁ : Set G) with hM₂
  have hN₂ : ∀ y ∈ normalizer (U₁ : Set G), y ∈ normalizer (M₁ : Set G) →
      y ∈ normalizer (M₂ : Set G) := by
    intro y hy hy₁
    rcases hdich y hy with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact mem_normalizer_iff_map_conj_eq'.mpr h2
    · exact absurd ((mem_normalizer_iff_map_conj_eq'.mp hy₁).symm.trans h1) hne
  have hswap : ∀ y ∈ normalizer (U₁ : Set G), y ∉ normalizer (M₁ : Set G) →
      M₁.map (MulAut.conj y).toMonoidHom = M₂ := by
    intro y hy hy₁
    rcases hdich y hy with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact absurd (mem_normalizer_iff_map_conj_eq'.mpr h1) hy₁
    · exact h1
  set D := U₁ ⊓ U' with hDdef
  have hfaith : ∀ y ∈ U', y ∈ centralizerModCenter U₁ → y ∈ U₁ := fun y hy hyK =>
    hD.mem_of_mem_centralizerModCenter hvT hv2 hvS hY hinf hcomm ht₁ ht₂ hP2 hUP hTP hPN
      (hle hy) hyK
  have hDC : ∀ y ∈ U', D ≤ commCenterSubgroup U₁ y := fun y hy d hd =>
    ⟨(mem_inf.mp hd).1, comm_mem_center_of_mem_inf hU'U hinv hU'c hy hd⟩
  have hyy : ∀ y ∈ U', ∀ w ∈ U₁, y * y * w * (y * y)⁻¹ * w⁻¹ ∈ U₁ ⊓ centralizer (U₁ : Set G) :=
    fun y hy w hw => sq_comm_mem_center hU'U hUU' hinv hsq hU'c hy hw
  have hUcard : Nat.card U₁ = (2 ^ f) ^ 6 := hU.card
  have hY₁₂ : Nat.card Y₁ = Nat.card Y₂ := by
    have hmap : Y₁.map (MulAut.conj t).toMonoidHom = Y₂ := by
      apply le_antisymm
      · rintro _ ⟨a, ha, rfl⟩
        simpa [MulAut.conj_apply] using ht₁ a ha
      · intro b hb
        refine ⟨t⁻¹ * b * t, ?_, by simp [MulAut.conj_apply]; group⟩
        have := ht₂ b hb
        rw [htinv] at this ⊢
        exact this
    rw [← hmap]
    exact (card_map_of_injective (f := (MulAut.conj t).toMonoidHom)
      (MulAut.conj t).injective).symm
  have hUle : Nat.card U₁ ≤ Nat.card Y₁ * Nat.card Y₂ :=
    card_le_card_mul_card_of_forall_eq_mul (A := (Y₁ : Set G)) (B := (Y₂ : Set G))
      (C := (U₁ : Set G)) fun w hw => by
        obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_eq_of_mem_sup_of_commute hcomm (hY ▸ hw)
        exact ⟨a, ha, b, hb, rfl⟩
  have hY₁card : (2 ^ f) ^ 3 ≤ Nat.card Y₁ := by
    have h1 : ((2 ^ f) ^ 3) ^ 2 ≤ Nat.card Y₁ ^ 2 := by
      rw [← pow_mul, sq, ← hUcard]
      calc Nat.card U₁ ≤ Nat.card Y₁ * Nat.card Y₂ := hUle
        _ = Nat.card Y₁ * Nat.card Y₁ := by rw [hY₁₂]
    exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h1
  have hY₂card : (2 ^ f) ^ 3 ≤ Nat.card Y₂ := hY₁₂ ▸ hY₁card
  have hprod₁ : ∀ y, Nat.card (commCenterSubgroup U₁ y) * Nat.card Y₁ ≤
      Nat.card U₁ * Nat.card (Y₁ ⊓ commCenterSubgroup U₁ y : Subgroup G) := fun y =>
    card_mul_card_le_card_mul_card_inf (commCenterSubgroup_le U₁ y) hY₁U
  have hprod₂ : ∀ y, Nat.card (commCenterSubgroup U₁ y) * Nat.card Y₂ ≤
      Nat.card U₁ * Nat.card (Y₂ ⊓ commCenterSubgroup U₁ y : Subgroup G) := fun y =>
    card_mul_card_le_card_mul_card_inf (commCenterSubgroup_le U₁ y) hY₂U
  have hK1 : ∀ y ∈ U', (∀ a ∈ Y₁, y * a * y⁻¹ * a⁻¹ ∈ U₁ ⊓ centralizer (U₁ : Set G)) →
      (∀ b ∈ Y₂, y * b * y⁻¹ * b⁻¹ ∈ U₁ ⊓ centralizer (U₁ : Set G)) → y ∈ D :=
    fun y hy h₁ h₂ => mem_inf.mpr
      ⟨hfaith y hy (mem_centralizerModCenter_of_forall hY hcomm (hU'U hy) h₁ h₂), hy⟩
  have hsame₁ : ∀ y ∈ U', ∀ y' ∈ U', y ∈ normalizer (M₁ : Set G) →
      y' ∈ normalizer (M₁ : Set G) →
      ((∀ a ∈ Y₁, y * a * y⁻¹ * a⁻¹ ∈ U₁ ⊓ centralizer (U₁ : Set G)) ↔
        (∀ a ∈ Y₁, y' * a * y'⁻¹ * a⁻¹ ∈ U₁ ⊓ centralizer (U₁ : Set G))) →
      ∀ a ∈ Y₁, y⁻¹ * y' * a * (y⁻¹ * y')⁻¹ * a⁻¹ ∈ U₁ ⊓ centralizer (U₁ : Set G) := by
    intro y hy y' hy' hyM hy'M hiff
    by_cases h1 : ∀ a ∈ Y₁, y * a * y⁻¹ * a⁻¹ ∈ U₁ ⊓ centralizer (U₁ : Set G)
    · exact forall_comm_mem_center_of_mul_right (hU'U hy)
        (fun a ha => by rw [mul_inv_cancel_left]; exact hiff.mp h1 a ha) h1
    · exact forall_comm_mem_center_inv_mul_of_not hσq hEcard hFcard hc₁ hY hinf hcomm hU'U hUU'
        hinv hsq hU'c hy hy' hyM hy'M h1 (fun h2 => h1 (hiff.mpr h2))
  have hsame₂ : ∀ y ∈ U', ∀ y' ∈ U', y ∈ normalizer (M₂ : Set G) →
      y' ∈ normalizer (M₂ : Set G) →
      ((∀ b ∈ Y₂, y * b * y⁻¹ * b⁻¹ ∈ U₁ ⊓ centralizer (U₁ : Set G)) ↔
        (∀ b ∈ Y₂, y' * b * y'⁻¹ * b⁻¹ ∈ U₁ ⊓ centralizer (U₁ : Set G))) →
      ∀ b ∈ Y₂, y⁻¹ * y' * b * (y⁻¹ * y')⁻¹ * b⁻¹ ∈ U₁ ⊓ centralizer (U₁ : Set G) := by
    intro y hy y' hy' hyM hy'M hiff
    by_cases h1 : ∀ b ∈ Y₂, y * b * y⁻¹ * b⁻¹ ∈ U₁ ⊓ centralizer (U₁ : Set G)
    · exact forall_comm_mem_center_of_mul_right (hU'U hy)
        (fun b hb => by rw [mul_inv_cancel_left]; exact hiff.mp h1 b hb) h1
    · exact forall_comm_mem_center_inv_mul_of_not hσq hEcard hFcard hc₂ hY' hinf' hcomm' hU'U
        hUU' hinv hsq hU'c hy hy' hyM hy'M h1 (fun h2 => h1 (hiff.mpr h2))
  have hfour : ∀ K : Subgroup G, K ≤ U' → K ≤ normalizer (M₁ : Set G) →
      Nat.card K ≤ 4 * Nat.card D := by
    intro K hKU hKM
    have h1 := card_le_card_mul_card_of_fiber (S := (K : Set G)) (D := D)
      (fun z => (decide (∀ a ∈ Y₁, z * a * z⁻¹ * a⁻¹ ∈ U₁ ⊓ centralizer (U₁ : Set G)),
        decide (∀ b ∈ Y₂, z * b * z⁻¹ * b⁻¹ ∈ U₁ ⊓ centralizer (U₁ : Set G))))
      (fun z hz z' hz' he => by
        simp only [Prod.mk.injEq, decide_eq_decide] at he
        have hzU := hKU hz
        have hz'U := hKU hz'
        exact hK1 _ (mul_mem (inv_mem hzU) hz'U)
          (hsame₁ z hzU z' hz'U (hKM hz) (hKM hz') he.1)
          (hsame₂ z hzU z' hz'U (hN₂ z (hU'U hzU) (hKM hz)) (hN₂ z' (hU'U hz'U) (hKM hz'))
            he.2))
    have h4 : Nat.card (Bool × Bool) = 4 := by simp [Nat.card_eq_fintype_card]
    rw [h4] at h1
    exact h1
  refine eq_of_le_of_card_ge (fun y₀ hy₀ => ?_) hcardU'.symm.le
  by_contra hy₀U
  have hpos : 0 < Nat.card U₁ := Nat.card_pos
  have hQ : 0 < 2 ^ f := by positivity
  by_cases hA : ∃ y ∈ U', y ∉ normalizer (M₁ : Set G)
  · obtain ⟨y, hy, hyM⟩ := hA
    have hsw := hswap y (hU'U hy) hyM
    have hb1 := card_inf_commCenterSubgroup_le_of_swap hEcard hFcard hc₁ hY hcomm hsw
    have hUH : Nat.card U' ≤ 2 * Nat.card (U' ⊓ normalizer (M₁ : Set G) : Subgroup G) := by
      have h1 := card_le_card_mul_card_of_fiber (S := (U' : Set G))
        (D := U' ⊓ normalizer (M₁ : Set G)) (fun z => decide (z ∈ normalizer (M₁ : Set G)))
        (fun z hz z' hz' he => by
          simp only [decide_eq_decide] at he
          refine mem_inf.mpr ⟨mul_mem (inv_mem hz) hz', ?_⟩
          by_cases hzM : z ∈ normalizer (M₁ : Set G)
          · exact mul_mem (inv_mem hzM) (he.mp hzM)
          · have hz'M : z' ∉ normalizer (M₁ : Set G) := fun h' => hzM (he.mpr h')
            have e1 := hswap z (hU'U hz) hzM
            have e2 := hswap z' (hU'U hz') hz'M
            refine mem_normalizer_iff_map_conj_eq'.mpr ?_
            rw [map_conj_mul_eq, e2, ← e1, ← map_conj_mul_eq, inv_mul_cancel]
            exact mem_normalizer_iff_map_conj_eq'.mp (one_mem _))
      have h2 : Nat.card Bool = 2 := by simp [Nat.card_eq_fintype_card]
      rw [h2] at h1
      exact h1
    have hHD := hfour _ inf_le_left inf_le_right
    have hDC' := card_le_of_le (hDC y hy)
    have hp := hprod₁ y
    have e0 : Nat.card U₁ ≤ 8 * Nat.card (commCenterSubgroup U₁ y) := by omega
    have e1 : Nat.card (commCenterSubgroup U₁ y) * (2 ^ f) ^ 3 ≤ Nat.card U₁ * 2 ^ f :=
      (Nat.mul_le_mul_left _ hY₁card).trans (hp.trans (Nat.mul_le_mul_left _ hb1))
    have e2 : Nat.card U₁ * 2 ^ f * (2 ^ f) ^ 2 ≤ Nat.card U₁ * 2 ^ f * 8 :=
      calc Nat.card U₁ * 2 ^ f * (2 ^ f) ^ 2 = Nat.card U₁ * (2 ^ f) ^ 3 := by ring
        _ ≤ 8 * Nat.card (commCenterSubgroup U₁ y) * (2 ^ f) ^ 3 := Nat.mul_le_mul_right _ e0
        _ = 8 * (Nat.card (commCenterSubgroup U₁ y) * (2 ^ f) ^ 3) := by ring
        _ ≤ 8 * (Nat.card U₁ * 2 ^ f) := Nat.mul_le_mul_left 8 e1
        _ = Nat.card U₁ * 2 ^ f * 8 := by ring
    have e3 := Nat.le_of_mul_le_mul_left e2 (Nat.mul_pos hpos hQ)
    nlinarith
  · push Not at hA
    have hU'D4 : Nat.card U' ≤ 4 * Nat.card D := hfour U' le_rfl fun y hy => hA y hy
    by_cases hB1 : ∃ y ∈ U', (¬ ∀ a ∈ Y₁, y * a * y⁻¹ * a⁻¹ ∈ U₁ ⊓ centralizer (U₁ : Set G)) ∧
        ¬ ∀ b ∈ Y₂, y * b * y⁻¹ * b⁻¹ ∈ U₁ ⊓ centralizer (U₁ : Set G)
    · obtain ⟨y, hy, hn1, hn2⟩ := hB1
      have hyM := hA y hy
      have hyM₂ := hN₂ y (hU'U hy) hyM
      have hb1 := card_inf_commCenterSubgroup_le_of_not hσq hEcard hFcard hc₁ hY hinf hcomm
        (hU'U hy) hyM (hyy y hy) hn1
      have hb2 := card_inf_commCenterSubgroup_le_of_not hσq hEcard hFcard hc₂ hY' hinf' hcomm'
        (hU'U hy) hyM₂ (hyy y hy) hn2
      have hCy : Nat.card (commCenterSubgroup U₁ y) ≤
          Nat.card (Y₁ ⊓ commCenterSubgroup U₁ y : Subgroup G) *
            Nat.card (Y₂ ⊓ commCenterSubgroup U₁ y : Subgroup G) :=
        card_le_card_mul_card_of_forall_eq_mul (A := ((Y₁ ⊓ commCenterSubgroup U₁ y :
          Subgroup G) : Set G)) (B := ((Y₂ ⊓ commCenterSubgroup U₁ y : Subgroup G) : Set G))
          (C := (commCenterSubgroup U₁ y : Set G)) fun w hw => by
            obtain ⟨a, ha, b, hb, rfl, h1, h2⟩ :=
              exists_mul_of_comm_mem_center hY hcomm hyM hyM₂ hw.1 hw.2
            exact ⟨a, mem_inf.mpr ⟨ha, hY₁U ha, h1⟩, b, mem_inf.mpr ⟨hb, hY₂U hb, h2⟩, rfl⟩
      have hDC' := card_le_of_le (hDC y hy)
      have e0 : (2 ^ f) ^ 6 ≤ 4 * ((2 ^ f * 2 ^ f) * (2 ^ f * 2 ^ f)) := by
        have := Nat.mul_le_mul hb1 hb2
        rw [← hUcard]
        omega
      have hq16 : 16 ≤ 2 ^ f * 2 ^ f := by nlinarith
      have hq4' : 0 < (2 ^ f * 2 ^ f) * (2 ^ f * 2 ^ f) := by positivity
      have e1 : (2 ^ f) ^ 6 = (2 ^ f * 2 ^ f) * ((2 ^ f * 2 ^ f) * (2 ^ f * 2 ^ f)) := by ring
      rw [e1] at e0
      nlinarith
    · have hB1' : ∀ y ∈ U', (¬ ∀ a ∈ Y₁, y * a * y⁻¹ * a⁻¹ ∈ U₁ ⊓ centralizer (U₁ : Set G)) →
          ∀ b ∈ Y₂, y * b * y⁻¹ * b⁻¹ ∈ U₁ ⊓ centralizer (U₁ : Set G) := fun y hy hn => by
        by_contra hn2
        exact hB1 ⟨y, hy, hn, hn2⟩
      have hnot : ¬ ((∀ a ∈ Y₁, y₀ * a * y₀⁻¹ * a⁻¹ ∈ U₁ ⊓ centralizer (U₁ : Set G)) ∧
          ∀ b ∈ Y₂, y₀ * b * y₀⁻¹ * b⁻¹ ∈ U₁ ⊓ centralizer (U₁ : Set G)) :=
        fun ⟨h1, h2⟩ => hy₀U (mem_inf.mp (hK1 y₀ hy₀ h1 h2)).1
      have hy₀M := hA y₀ hy₀
      have hy₀M₂ := hN₂ y₀ (hU'U hy₀) hy₀M
      have hfin : ∀ (i y₂ : ℕ), Nat.card U' ≤ 2 * Nat.card D → i ≤ 2 ^ f * 2 ^ f →
          (2 ^ f) ^ 3 ≤ y₂ →
          Nat.card (commCenterSubgroup U₁ y₀) * y₂ ≤ Nat.card U₁ * i → False := by
        intro i y₂ hU'D hi hy₂ hp
        have hDC' := card_le_of_le (hDC y₀ hy₀)
        have e0 : Nat.card U₁ ≤ 2 * Nat.card (commCenterSubgroup U₁ y₀) := by omega
        have e1 : Nat.card (commCenterSubgroup U₁ y₀) * (2 ^ f) ^ 3 ≤
            Nat.card U₁ * (2 ^ f * 2 ^ f) :=
          (Nat.mul_le_mul_left _ hy₂).trans (hp.trans (Nat.mul_le_mul_left _ hi))
        have e2 : Nat.card U₁ * (2 ^ f * 2 ^ f) * 2 ^ f ≤ Nat.card U₁ * (2 ^ f * 2 ^ f) * 2 :=
          calc Nat.card U₁ * (2 ^ f * 2 ^ f) * 2 ^ f = Nat.card U₁ * (2 ^ f) ^ 3 := by ring
            _ ≤ 2 * Nat.card (commCenterSubgroup U₁ y₀) * (2 ^ f) ^ 3 :=
                Nat.mul_le_mul_right _ e0
            _ = 2 * (Nat.card (commCenterSubgroup U₁ y₀) * (2 ^ f) ^ 3) := by ring
            _ ≤ 2 * (Nat.card U₁ * (2 ^ f * 2 ^ f)) := Nat.mul_le_mul_left 2 e1
            _ = Nat.card U₁ * (2 ^ f * 2 ^ f) * 2 := by ring
        have e3 := Nat.le_of_mul_le_mul_left e2 (Nat.mul_pos hpos (Nat.mul_pos hQ hQ))
        omega
      have h2el : Nat.card Bool = 2 := by simp [Nat.card_eq_fintype_card]
      by_cases h₀₁ : ∀ a ∈ Y₁, y₀ * a * y₀⁻¹ * a⁻¹ ∈ U₁ ⊓ centralizer (U₁ : Set G)
      · have hn₂ : ¬ ∀ b ∈ Y₂, y₀ * b * y₀⁻¹ * b⁻¹ ∈ U₁ ⊓ centralizer (U₁ : Set G) :=
          fun h2 => hnot ⟨h₀₁, h2⟩
        have hall : ∀ y ∈ U', ∀ a ∈ Y₁, y * a * y⁻¹ * a⁻¹ ∈ U₁ ⊓ centralizer (U₁ : Set G) := by
          intro y hy
          by_contra hn1
          have h2 := hB1' y hy hn1
          have hn1' : ¬ ∀ a ∈ Y₁, y₀ * y * a * (y₀ * y)⁻¹ * a⁻¹ ∈
              U₁ ⊓ centralizer (U₁ : Set G) := fun h' =>
            hn1 (forall_comm_mem_center_of_mul_right (hU'U hy₀) h' h₀₁)
          have hn2' : ¬ ∀ b ∈ Y₂, y₀ * y * b * (y₀ * y)⁻¹ * b⁻¹ ∈
              U₁ ⊓ centralizer (U₁ : Set G) := fun h' =>
            hn₂ (forall_comm_mem_center_of_mul_left (hU'U hy₀) h' h2)
          exact hn2' (hB1' _ (mul_mem hy₀ hy) hn1')
        have hU'D : Nat.card U' ≤ 2 * Nat.card D := by
          have h1 := card_le_card_mul_card_of_fiber (S := (U' : Set G)) (D := D)
            (fun z => decide (∀ b ∈ Y₂, z * b * z⁻¹ * b⁻¹ ∈ U₁ ⊓ centralizer (U₁ : Set G)))
            (fun z hz z' hz' he => by
              simp only [decide_eq_decide] at he
              exact hK1 _ (mul_mem (inv_mem hz) hz')
                (hsame₁ z hz z' hz' (hA z hz) (hA z' hz') (iff_of_true (hall z hz) (hall z' hz')))
                (hsame₂ z hz z' hz' (hN₂ z (hU'U hz) (hA z hz)) (hN₂ z' (hU'U hz') (hA z' hz'))
                  he))
          rw [h2el] at h1
          exact h1
        exact hfin _ _ hU'D (card_inf_commCenterSubgroup_le_of_not hσq hEcard hFcard hc₂ hY'
          hinf' hcomm' (hU'U hy₀) hy₀M₂ (hyy y₀ hy₀) hn₂) hY₂card (hprod₂ y₀)
      · have h₀₂ := hB1' y₀ hy₀ h₀₁
        have hall : ∀ y ∈ U', ∀ b ∈ Y₂, y * b * y⁻¹ * b⁻¹ ∈ U₁ ⊓ centralizer (U₁ : Set G) := by
          intro y hy
          by_contra hn2
          have h1 : ∀ a ∈ Y₁, y * a * y⁻¹ * a⁻¹ ∈ U₁ ⊓ centralizer (U₁ : Set G) := by
            by_contra hn1
            exact hn2 (hB1' y hy hn1)
          have hn1' : ¬ ∀ a ∈ Y₁, y₀ * y * a * (y₀ * y)⁻¹ * a⁻¹ ∈
              U₁ ⊓ centralizer (U₁ : Set G) := fun h' =>
            h₀₁ (forall_comm_mem_center_of_mul_left (hU'U hy₀) h' h1)
          have hn2' : ¬ ∀ b ∈ Y₂, y₀ * y * b * (y₀ * y)⁻¹ * b⁻¹ ∈
              U₁ ⊓ centralizer (U₁ : Set G) := fun h' =>
            hn2 (forall_comm_mem_center_of_mul_right (hU'U hy₀) h' h₀₂)
          exact hn2' (hB1' _ (mul_mem hy₀ hy) hn1')
        have hU'D : Nat.card U' ≤ 2 * Nat.card D := by
          have h1 := card_le_card_mul_card_of_fiber (S := (U' : Set G)) (D := D)
            (fun z => decide (∀ a ∈ Y₁, z * a * z⁻¹ * a⁻¹ ∈ U₁ ⊓ centralizer (U₁ : Set G)))
            (fun z hz z' hz' he => by
              simp only [decide_eq_decide] at he
              exact hK1 _ (mul_mem (inv_mem hz) hz')
                (hsame₁ z hz z' hz' (hA z hz) (hA z' hz') he)
                (hsame₂ z hz z' hz' (hN₂ z (hU'U hz) (hA z hz)) (hN₂ z' (hU'U hz') (hA z' hz'))
                  (iff_of_true (hall z hz) (hall z' hz'))))
          rw [h2el] at h1
          exact h1
        exact hfin _ _ hU'D (card_inf_commCenterSubgroup_le_of_not hσq hEcard hFcard hc₁ hY hinf
          hcomm (hU'U hy₀) hy₀M (hyy y₀ hy₀) h₀₁) hY₁card (hprod₁ y₀)

end U3EndingData

section Certificates

theorem u3EndingNormalConjInput_holds : U3EndingNormalConjInput := by
  intro G _ _ L f t T R₂ U₁ s v Y₁ Y₂ hD hvT hv2 hvS _ hY hinf hcomm ht₁ ht₂ P hP2 hQP hPN g hle
    hnorm
  have hTN : T ≤ normalizer (U₁ : Set G) := hD.u1.le_normalizer hD.start hD.card_sylow hD.r2
  have hTP : T ≤ P := fun x hx => hQP (mem_sup_right (mem_inf.mpr ⟨hx, hTN hx⟩))
  exact hD.map_conj_eq_of_le hvT hv2 hvS hY hinf hcomm ht₁ ht₂ hP2 (le_sup_left.trans hQP) hTP
    hPN hle hnorm

theorem u3EndingSylowInput_holds : U3EndingSylowInput :=
  u3EndingSylowInput_of_normalConj u3EndingNormalConjInput_holds

end Certificates

end CFSG.SeitzReduction.RankOne
