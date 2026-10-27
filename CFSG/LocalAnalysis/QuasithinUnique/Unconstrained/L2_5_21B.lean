module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21A

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

section Generic

variable {G : Type} [Group G] [Finite G]

theorem card_mul_le_card_sup {X Y : Subgroup G} (h : X ⊓ Y = ⊥) :
    Nat.card X * Nat.card Y ≤ Nat.card ↥(X ⊔ Y) := by
  have hinj : Function.Injective (fun p : X × Y =>
      (⟨(p.1 : G) * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩ : ↥(X ⊔ Y))) := by
    intro p q hpq
    have h1 : (p.1 : G) * p.2 = q.1 * q.2 := congrArg Subtype.val hpq
    have h2 : (q.1 : G)⁻¹ * p.1 = q.2 * (p.2 : G)⁻¹ := by
      calc (q.1 : G)⁻¹ * p.1 = (q.1 : G)⁻¹ * (p.1 * p.2) * (p.2 : G)⁻¹ := by group
        _ = (q.1 : G)⁻¹ * (q.1 * q.2) * (p.2 : G)⁻¹ := by rw [h1]
        _ = q.2 * (p.2 : G)⁻¹ := by group
    have h3 : (q.1 : G)⁻¹ * p.1 ∈ X ⊓ Y :=
      ⟨X.mul_mem (X.inv_mem q.1.2) p.1.2, h2 ▸ Y.mul_mem q.2.2 (Y.inv_mem p.2.2)⟩
    rw [h, Subgroup.mem_bot] at h3
    have h4 : p.1 = q.1 := Subtype.ext (inv_mul_eq_one.mp h3).symm
    have h5 : (p.2 : G) = q.2 := by
      have : (p.1 : G) * p.2 = (p.1 : G) * q.2 := by rw [h1, ← h4]
      exact mul_left_cancel this
    exact Prod.ext h4 (Subtype.ext h5)
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_prod] at this

theorem relIndex_le_two_of_card {X S : Subgroup G} (hXS : X ≤ S)
    (h : Nat.card S ≤ 2 * Nat.card X) : X.relIndex S ≤ 2 := by
  have h1 := Subgroup.card_mul_index (X.subgroupOf S)
  have h2 : Nat.card (X.subgroupOf S) = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXS).toEquiv
  rw [h2] at h1
  have hpos : 0 < Nat.card X := Nat.card_pos
  by_contra hgt
  push Not at hgt
  have : Nat.card X * 3 ≤ Nat.card X * X.relIndex S := Nat.mul_le_mul_left _ hgt
  have h3 : Nat.card X * (X.subgroupOf S).index = Nat.card S := h1
  have h4 : (X.subgroupOf S).index = X.relIndex S := rfl
  rw [h4] at h3
  omega

theorem two_mul_card_le_of_lt {X S : Subgroup G} (h : X < S) : 2 * Nat.card X ≤ Nat.card S := by
  have h1 := Subgroup.card_mul_index (X.subgroupOf S)
  have h2 : Nat.card (X.subgroupOf S) = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.le).toEquiv
  rw [h2] at h1
  have h3 : (X.subgroupOf S).index ≠ 1 := fun h' =>
    absurd (Subgroup.relIndex_eq_one.mp h') (not_le_of_gt h)
  have h4 : (X.subgroupOf S).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h5 : 2 ≤ (X.subgroupOf S).index := by omega
  calc 2 * Nat.card X ≤ (X.subgroupOf S).index * Nat.card X := Nat.mul_le_mul_right _ h5
    _ = Nat.card X * (X.subgroupOf S).index := mul_comm _ _
    _ = Nat.card S := h1

theorem eq_of_card_le_two_mul {S X Q : Subgroup G} (hQX : Q ≤ X) (hXS : X < S)
    (h : Nat.card S ≤ 2 * Nat.card Q) : Q = X ∧ Nat.card S = 2 * Nat.card X := by
  have h1 := two_mul_card_le_of_lt hXS
  have h2 := Subgroup.card_le_of_le hQX
  exact ⟨Subgroup.eq_of_le_of_card_ge hQX (by omega), by omega⟩

end Generic

section SBarRt

variable {G : Type} [Group G] {S A : Subgroup G} {P : Type} [Group P] [Finite P]
  {π : G → P} {R : Subgroup P}

theorem SBar.card_Rt [Finite G] (h : SBar S A π R) : Nat.card h.Rt * R.index = Nat.card S := by
  have h1 : Nat.card h.Rt = Nat.card (R.comap h.hom) :=
    Subgroup.card_map_of_injective S.subtype_injective
  have h2 := Subgroup.card_mul_index (R.comap h.hom)
  rw [Subgroup.index_comap_of_surjective R h.hom_surjective] at h2
  rw [h1]
  exact h2

theorem SBar.not_img_le_of_not_le_Rt (h : SBar S A π R) {Q : Subgroup G} (hQS : Q ≤ S)
    (hQR : ¬ Q ≤ h.Rt) : ¬ h.img Q ≤ R := by
  intro hle
  apply hQR
  intro q hq
  rw [h.mem_Rt]
  exact ⟨hQS hq, hle (h.pi_mem_img hq (hQS hq))⟩

theorem SBar.pow_half_eq_one_of (h : SBar S A π R) {Q Y : Subgroup G} (hY : Y ≤ S)
    (hYA : Y ⊓ A = ⊥) (hQi : (h.img Q).index = 2) (hQR : ¬ h.img Q ≤ R) (h8 : 8 ≤ Nat.card R)
    {y : G} (hy : y ∈ Y) (hyQ : π y ∈ h.img Q) : y ^ (Nat.card R / 2) = 1 := by
  have h1 := h.ds.pow_half_eq_one hQi hQR h8 hyQ
  have hyS : y ∈ S := hY hy
  rw [← h.pi_pow hyS] at h1
  have h2 : y ^ (Nat.card R / 2) ∈ A := (h.ker _ (S.pow_mem hyS _)).mp h1
  have h3 : y ^ (Nat.card R / 2) ∈ Y ⊓ A := ⟨Y.pow_mem hy _, h2⟩
  rw [hYA, Subgroup.mem_bot] at h3
  exact h3

end SBarRt

section CaseB

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  {N : Notation25 hs} {t zK : G}

theorem Lv2520.caseB_not_le_centralizer (h : Lv2520 N t zK) (hA4 : 4 ≤ Nat.card ↥N.SC) :
    ¬ N.S ≤ Subgroup.centralizer (N.SC : Set G) := by
  intro hle
  have hf := h.facts2511
  have hle' : N.SC ≤ centerOf N.S := fun a ha =>
    ⟨N.SC_le_S ha, Subgroup.mem_centralizer_iff.mpr fun s hs' =>
      (Subgroup.mem_centralizer_iff.mp (hle hs') a ha).symm⟩
  have hlt : N.SC < centerOf N.S := lt_of_le_of_ne hle' fun heq =>
    h.zK_not_mem_SC (by rw [heq]; exact hf.zK_mem_center)
  have h1 := Subgroup.card_lt_of_lt hlt
  have h4 := hf.centerS_E4.2
  omega

theorem Lv2520.caseB_out (h : Lv2520 N t zK) (hAab : ∀ a ∈ N.SC, ∀ b ∈ N.SC, a * b = b * a)
    (hA4 : 4 ≤ Nat.card ↥N.SC) : ¬ N.S ≤ N.K ⊔ N.SC := by
  intro hin
  apply h.caseB_not_le_centralizer hA4
  intro s hs'
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  obtain ⟨k, hk, c, hc, hkc⟩ := mem_sup_of_commute (A := N.K) (B := N.SC)
    (fun k hk a ha => (h.SC_commutes ha k hk).symm) (hin hs')
  have h1 : a * k = k * a := h.SC_commutes ha k hk
  have h2 : a * c = c * a := hAab a ha c hc
  rw [← hkc]
  calc a * (k * c) = (a * k) * c := by group
    _ = (k * a) * c := by rw [h1]
    _ = k * (a * c) := by group
    _ = k * (c * a) := by rw [h2]
    _ = (k * c) * a := by group

theorem Lv2520.caseB_centralizer (h : Lv2520 N t zK)
    (hidx : Nat.card ↥N.S ≤ 2 * (Nat.card ↥N.SK * Nat.card ↥N.SC))
    (hAab : ∀ a ∈ N.SC, ∀ b ∈ N.SC, a * b = b * a) (hA4 : 4 ≤ Nat.card ↥N.SC) :
    N.SK ⊔ N.SC = N.S ⊓ Subgroup.centralizer (N.SC : Set G) ∧
      Nat.card ↥N.S = 2 * Nat.card ↥(N.S ⊓ Subgroup.centralizer (N.SC : Set G)) := by
  have hQX : N.SK ⊔ N.SC ≤ N.S ⊓ Subgroup.centralizer (N.SC : Set G) := by
    refine sup_le (fun q hq => ⟨hq.1, ?_⟩) (fun a ha => ⟨N.SC_le_S ha, ?_⟩)
    · exact Subgroup.mem_centralizer_iff.mpr fun a ha => h.SC_commutes ha q hq.2
    · exact Subgroup.mem_centralizer_iff.mpr fun b hb => hAab b hb a ha
  have hXS : N.S ⊓ Subgroup.centralizer (N.SC : Set G) < N.S :=
    lt_of_le_of_ne inf_le_left fun heq => h.caseB_not_le_centralizer hA4 fun s hs' => by
      have : s ∈ N.S ⊓ Subgroup.centralizer (N.SC : Set G) := by rw [heq]; exact hs'
      exact this.2
  have hS2 : Nat.card ↥N.S ≤ 2 * Nat.card ↥(N.SK ⊔ N.SC) :=
    hidx.trans (Nat.mul_le_mul_left 2 (card_mul_le_card_sup h.SK_inf_SC))
  exact eq_of_card_le_two_mul hQX hXS hS2

theorem Lv2520.caseB_false {R : Subgroup ↥(autOn N.S N.K)} (h : Lv2520 N t zK)
    (hR : DS.DSData R) (hidx : Nat.card ↥N.S ≤ 2 * (Nat.card ↥N.SK * Nat.card ↥N.SC))
    (hAab : ∀ a ∈ N.SC, ∀ b ∈ N.SC, a * b = b * a) (hA4 : 4 ≤ Nat.card ↥N.SC) : False := by
  have hSB := h.sBar hR
  have h258 := h.facts258
  have h255 := h.concl255
  have hQi := h.index_img_SK hR hidx (h.caseB_out hAab hA4)
  obtain ⟨hXeq, hcardX⟩ := h.caseB_centralizer hidx hAab hA4
  obtain ⟨X, hXdef⟩ : ∃ X : Subgroup G, X = N.S ⊓ Subgroup.centralizer (N.SC : Set G) :=
    ⟨_, rfl⟩
  rw [← hXdef] at hXeq hcardX
  have hQR : ¬ hSB.img N.SK ≤ R := hSB.not_img_le_of_not_le_Rt N.SK_le_S (h.not_SK_le_Rt hR)
  have hR8 : 8 ≤ Nat.card R := by
    have h1 := hSB.index_img_mul N.SK_le_S h.SK_inf_SC
    rw [hQi] at h1
    have h2 := Subgroup.card_mul_index R
    rw [hR.index_two] at h2
    have h3 := h258.eight_le_card_SK
    omega
  obtain ⟨B, hBdef⟩ : ∃ B : Subgroup G, B = CFSG.conjugate N.SC N.x := ⟨_, rfl⟩
  have hBS : B ≤ N.S := by rw [hBdef]; exact h255.2.1
  have hBA : B ⊓ N.SC = ⊥ := by rw [hBdef, inf_comm]; exact h255.1
  have hBcomm : ∀ a ∈ N.SC, ∀ b ∈ B, a * b = b * a := by rw [hBdef]; exact h255.2.2
  have hB4 : 4 ≤ Nat.card ↥B := by rw [hBdef, BenderBranch.card_conjugate]; exact hA4
  have hSx : CFSG.conjugate N.S N.x = N.S :=
    BenderBranch.conjugate_eq_iff_mem_normalizer.mpr N.x_mem.2
  have hCB : N.S ⊓ Subgroup.centralizer (B : Set G) = CFSG.conjugate X N.x := by
    rw [hXdef, BenderBranch.conjugate_inf, BenderBranch.conjugate_centralizer, hSx, hBdef]
  have hCBcard : Nat.card ↥(N.S ⊓ Subgroup.centralizer (B : Set G)) = Nat.card ↥X := by
    rw [hCB, BenderBranch.card_conjugate]
  have hidxB : (N.S ⊓ Subgroup.centralizer (B : Set G)).relIndex N.S ≤ 2 :=
    relIndex_le_two_of_card inf_le_left (by rw [hCBcard]; exact hcardX.le)
  obtain ⟨-, hcen⟩ := hSB.abelian_centralizer hR8 hBS hBA hB4 hidxB
  have hYRt : N.S ⊓ Subgroup.centralizer (B : Set G) ≤ hSB.Rt := by
    intro c hc
    refine hcen c hc.1 fun b hb => ?_
    exact (Subgroup.mem_centralizer_iff.mp hc.2 b hb).symm
  have hRtcard := hSB.card_Rt
  rw [hR.index_two] at hRtcard
  have hYeq : N.S ⊓ Subgroup.centralizer (B : Set G) = hSB.Rt :=
    Subgroup.eq_of_le_of_card_ge hYRt (by omega)
  obtain ⟨g, hg⟩ := hR.cyclic.exists_generator
  have hord : orderOf (g : ↥(autOn N.S N.K)) = Nat.card R := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_card_of_forall_mem_zpowers hg
  have hgne : (g : ↥(autOn N.S N.K)) ^ (Nat.card R / 2) ≠ 1 :=
    pow_ne_one_of_lt_orderOf (by omega) (by rw [hord]; omega)
  obtain ⟨y, hyS, hyπ⟩ := hSB.surj (g : ↥(autOn N.S N.K))
  have hyRt : y ∈ hSB.Rt := hSB.mem_Rt.mpr ⟨hyS, by rw [hyπ]; exact g.2⟩
  have hyY : y ∈ N.S ⊓ Subgroup.centralizer (B : Set G) := by rw [hYeq]; exact hyRt
  have hyX : N.x * y * N.x⁻¹ ∈ X := by
    have : y ∈ CFSG.conjugate X N.x := by rw [← hCB]; exact hyY
    exact BenderBranch.mem_conjugate_iff.mp this
  have hq : N.x * y * N.x⁻¹ ∈ N.SK ⊔ N.SC := by rw [hXeq]; exact hyX
  obtain ⟨s, hsSK, a, haSC, hsa⟩ := mem_sup_of_commute (A := N.SK) (B := N.SC)
    (fun s hs' a ha => (h.SC_commutes ha s hs'.2).symm) hq
  have hsm : s ^ (Nat.card R / 2) = 1 :=
    hSB.pow_half_eq_one_of (Q := N.SK) (Y := N.SK) N.SK_le_S h.SK_inf_SC hQi hQR hR8 hsSK
      (hSB.pi_mem_img hsSK (N.SK_le_S hsSK))
  obtain ⟨b, hb⟩ : ∃ b : G, b = N.x⁻¹ * a * N.x := ⟨_, rfl⟩
  have hbB : b ∈ B := by
    rw [hBdef, BenderBranch.mem_conjugate_iff, hb]
    have : N.x * (N.x⁻¹ * a * N.x) * N.x⁻¹ = a := by group
    rw [this]; exact haSC
  have hbX : b ∈ N.SK ⊔ N.SC := by
    rw [hXeq, hXdef]
    exact ⟨hBS hbB, Subgroup.mem_centralizer_iff.mpr fun a' ha' => hBcomm a' ha' b hbB⟩
  obtain ⟨s', hs'SK, a', ha'SC, hsa'⟩ := mem_sup_of_commute (A := N.SK) (B := N.SC)
    (fun s'' hs'' a'' ha'' => (h.SC_commutes ha'' s'' hs''.2).symm) hbX
  have hπa' : actS N.K N.S h.S_le_normalizer a' = 1 :=
    (hSB.ker a' (N.SC_le_S ha'SC)).mpr ha'SC
  have hπb : actS N.K N.S h.S_le_normalizer b ∈ hSB.img N.SK := by
    have : actS N.K N.S h.S_le_normalizer b = actS N.K N.S h.S_le_normalizer s' := by
      rw [← hsa', hSB.mul s' (N.SK_le_S hs'SK) a' (N.SC_le_S ha'SC), hπa', mul_one]
    rw [this]
    exact hSB.pi_mem_img hs'SK (N.SK_le_S hs'SK)
  have hbm : b ^ (Nat.card R / 2) = 1 :=
    hSB.pow_half_eq_one_of (Q := N.SK) (Y := B) hBS hBA hQi hQR hR8 hbB hπb
  have ham : a ^ (Nat.card R / 2) = 1 := by
    have h1 : a = N.x * b * N.x⁻¹ := by rw [hb]; group
    have h2 : (N.x * b * N.x⁻¹) ^ (Nat.card R / 2) = N.x * b ^ (Nat.card R / 2) * N.x⁻¹ :=
      conj_pow
    rw [h1, h2, hbm]; group
  have hcomm_sa : Commute s a := (h.SC_commutes haSC s hsSK.2).symm
  have hqm : (N.x * y * N.x⁻¹) ^ (Nat.card R / 2) = 1 := by
    rw [← hsa, hcomm_sa.mul_pow, hsm, ham, mul_one]
  have hym : y ^ (Nat.card R / 2) = 1 := by
    have h2 : (N.x * y * N.x⁻¹) ^ (Nat.card R / 2) = N.x * y ^ (Nat.card R / 2) * N.x⁻¹ :=
      conj_pow
    rw [h2] at hqm
    calc y ^ (Nat.card R / 2) = N.x⁻¹ * (N.x * y ^ (Nat.card R / 2) * N.x⁻¹) * N.x := by group
      _ = 1 := by rw [hqm]; group
  apply hgne
  rw [← hyπ, ← hSB.pi_pow hyS, hym, hSB.pi_one]

end CaseB

end CFSG.QuasithinUnique
