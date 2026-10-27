module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bNotFused
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bSmallInv

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped Pointwise

theorem card_mul_le_card_sup {G : Type*} [Group G] [Finite G] {X Y : Subgroup G}
    (hXY : X ⊓ Y = ⊥) : Nat.card X * Nat.card Y ≤ Nat.card ↥(X ⊔ Y) := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun p => (⟨(p.1 : G) * p.2, mul_mem (mem_sup_left p.1.2) (mem_sup_right p.2.2)⟩ :
      ↥(X ⊔ Y))) ?_
  rintro ⟨u, v⟩ ⟨u', v'⟩ huv
  have h1 : (u : G) * v = u' * v' := congrArg Subtype.val huv
  have h2 : (u' : G)⁻¹ * u ∈ X ⊓ Y := by
    refine mem_inf.mpr ⟨mul_mem (inv_mem u'.2) u.2, ?_⟩
    have : (u' : G)⁻¹ * u = v' * (v : G)⁻¹ := by
      calc (u' : G)⁻¹ * u = (u' : G)⁻¹ * (u * v) * (v : G)⁻¹ := by group
        _ = (u' : G)⁻¹ * (u' * v') * (v : G)⁻¹ := by rw [h1]
        _ = v' * (v : G)⁻¹ := by group
    rw [this]
    exact mul_mem v'.2 (inv_mem v.2)
  rw [hXY, mem_bot] at h2
  have hu : (u : G) = u' := by
    calc (u : G) = u' * ((u' : G)⁻¹ * u) := by group
      _ = u' := by rw [h2, mul_one]
  have hv : (v : G) = v' := by
    rw [hu] at h1
    exact mul_left_cancel h1
  rw [Subtype.ext hu, Subtype.ext hv]

namespace Hyp52

variable {H : Type} [Group H] [Finite H] (h : Hyp52 H)

theorem two_element_mem_centralizer_B (hB6 : SylowKernelStatement)
    (hKa : conjugate h.K h.a = h.K) (hW : h.W ≤ h.K ⊔ coreActionKernel h.K)
    (hBab : ∀ u ∈ h.B, ∀ v ∈ h.B, u * v = v * u)
    {m : H} (hmW : m ∈ h.W) {k : ℕ} (hm : m ^ 2 ^ k = 1) :
    m ∈ centralizer (h.B : Set H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := coreActionKernel h.K with hC
  have h6 := hB6 H h
  rw [h.V_eq_K hKa] at h6
  obtain ⟨hBC, R₀, hR₀⟩ := h6
  have hKW : h.K ≤ h.W := h.isPComponent_K.1
  have hKB : h.K ≤ centralizer (h.B : Set H) := h.K_le_layer_W.trans h.V_le_centralizer_B
  have hCN : C ≤ normalizer (h.K : Set H) := fun c hc => (mem_coreActionKernel.mp hc).1
  have hmKC : m ∈ (h.K : Set H) * (C : Set H) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hCN]
    exact hW hmW
  obtain ⟨k₀, hk₀, c, hc, rfl⟩ := Set.mem_mul.mp hmKC
  have hcW : c ∈ h.W := by
    have := mul_mem (inv_mem (hKW hk₀)) hmW
    rwa [inv_mul_cancel_left] at this
  set ρ := h.B.normalizerMonoidHom with hρ
  have hρk : ρ ⟨k₀, hKW hk₀⟩ = 1 := by
    rw [← MonoidHom.mem_ker, normalizerMonoidHom_ker, mem_subgroupOf]
    exact hKB hk₀
  have hρm : ρ ⟨k₀ * c, hmW⟩ = ρ ⟨c, hcW⟩ := by
    have : (⟨k₀ * c, hmW⟩ : ↥h.W) = ⟨k₀, hKW hk₀⟩ * ⟨c, hcW⟩ := rfl
    rw [this, map_mul, hρk, one_mul]
  set D₀ : Subgroup H := C ⊓ h.W with hD₀
  have hBD : h.B ≤ D₀ := le_inf hBC le_normalizer
  have hodd : ¬ 2 ∣ h.B.relIndex D₀ := by
    have h1 : ¬ 2 ∣ (R₀ : Subgroup ↥C).index := Sylow.not_dvd_index R₀
    rw [hR₀] at h1
    have h2 : h.B.relIndex D₀ ∣ h.B.relIndex C :=
      ⟨_, (relIndex_mul_relIndex _ _ _ hBD inf_le_left).symm⟩
    exact fun hd => h1 (hd.trans h2)
  set ρ' : ↥D₀ →* MulAut ↥h.B := ρ.comp (inclusion (inf_le_right : D₀ ≤ h.W)) with hρ'
  have hker : h.B.subgroupOf D₀ ≤ ρ'.ker := by
    intro y hy
    rw [MonoidHom.mem_ker, hρ', MonoidHom.comp_apply, ← MonoidHom.mem_ker,
      normalizerMonoidHom_ker, mem_subgroupOf]
    rw [mem_subgroupOf] at hy
    rw [mem_centralizer_iff]
    intro b hb
    exact hBab b hb _ hy
  have hrange : Nat.card ρ'.range ∣ h.B.relIndex D₀ := by
    rw [← Subgroup.index_ker]
    exact Subgroup.index_dvd_of_le hker
  have hcD : c ∈ D₀ := mem_inf.mpr ⟨hc, hcW⟩
  have hord1 : ¬ 2 ∣ orderOf (ρ' ⟨c, hcD⟩) := by
    have h1 : orderOf (ρ' ⟨c, hcD⟩) ∣ Nat.card ρ'.range := by
      have := orderOf_dvd_natCard (⟨ρ' ⟨c, hcD⟩, ⟨_, rfl⟩⟩ : ρ'.range)
      rw [← Subgroup.orderOf_coe] at this
      exact this
    exact fun hd => hodd (hd.trans (h1.trans hrange))
  have hρ'c : ρ' ⟨c, hcD⟩ = ρ ⟨c, hcW⟩ := rfl
  have hord2 : orderOf (ρ ⟨c, hcW⟩) ∣ 2 ^ k := by
    rw [← hρm]
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow]
    have : (⟨k₀ * c, hmW⟩ : ↥h.W) ^ 2 ^ k = 1 := Subtype.ext (by
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one]; exact hm)
    rw [this, map_one]
  have hρc1 : ρ ⟨c, hcW⟩ = 1 := by
    rw [hρ'c] at hord1
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord2
    rcases j with _ | j
    · rw [pow_zero] at hj
      exact orderOf_eq_one_iff.mp hj
    · exact absurd (hj ▸ dvd_pow_self 2 (Nat.succ_ne_zero j)) hord1
  have hm1 : ρ ⟨k₀ * c, hmW⟩ = 1 := by rw [hρm, hρc1]
  rw [← MonoidHom.mem_ker, normalizerMonoidHom_ker, mem_subgroupOf] at hm1
  exact hm1

end Hyp52

namespace Hyp59

variable {H : Type} [Group H] [Finite H] (h : Hyp59 H)

theorem false_of_row515 (hB1 : ConjFixStatement) (hB6 : SylowKernelStatement)
    (hB7 : EmbedsTQuotStatement) (hCF23 : CFProp23Fusion) (hCF24 : CFProp24c)
    (hCFc : CFProp23Center) (hP21 : CFProp21A10) (hLoc : CFA10Local) (hNO : CFA10NoOuter)
    (hrow : h.Row515) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnf' := h.not_fused_of_row515 hB1 hCF23 hCF24 hCFc hP21 hrow
  obtain ⟨hTB4, hTB2⟩ := hP21 H h.toHyp52 hrow
  obtain ⟨hA4, hA2, ⟨N₀, hN₀K, hN₀T, hN₀B, hN₀tr, n₂, hn₂, ⟨k₂, hk₂⟩, u₂, hu₂, hn₂u⟩, haA⟩ :=
    hLoc H h.toHyp52 hrow
  have hW := hNO H h.toHyp52 hrow
  obtain ⟨⟨eJ⟩, hKa, ⟨eK⟩⟩ := hrow
  set A := h.T ⊓ h.K with hAdef
  set B' := conjugate h.B h.x with hB'def
  have hxT := h.x_mem_normalizer_T
  have hconjT : ∀ {y : H}, y ∈ h.T → h.x * y * h.x⁻¹ ∈ h.T := fun hy =>
    (mem_normalizer_iff.mp hxT _).mp hy
  have hconjT' : ∀ {y : H}, y ∈ h.T → h.x⁻¹ * y * h.x ∈ h.T := fun hy => by
    have := (mem_normalizer_iff.mp (inv_mem hxT) _).mp hy
    rwa [inv_inv] at this
  have hT2 : ∀ t ∈ h.T, t ^ 2 = 1 := by
    intro t ht
    have h1 := hTB2 t ht
    have h2 : t ^ 2 ∈ B' := by
      rw [hB'def, mem_conjugate_iff, ← conj_pow]
      exact hTB2 _ (hconjT ht)
    have := h.inf_conjugate_x ▸ mem_inf.mpr ⟨h1, h2⟩
    exact mem_bot.mp this
  have hTab : ∀ s ∈ h.T, ∀ t ∈ h.T, s * t = t * s := by
    intro s hs t ht
    have h1 := hT2 _ (mul_mem hs ht)
    have hs1 := hT2 s hs
    have ht1 := hT2 t ht
    rw [pow_two] at h1 hs1 ht1
    calc s * t = (s * t)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
      _ = t⁻¹ * s⁻¹ := mul_inv_rev s t
      _ = t * s := by rw [inv_eq_of_mul_eq_one_right hs1, inv_eq_of_mul_eq_one_right ht1]
  have hsq : ∀ {t : H}, t ∈ h.T → t * t = 1 := fun ht => by rw [← pow_two]; exact hT2 _ ht
  have hBT := h.toHyp52.B_le_T
  have hcardT : Nat.card h.T = 4 * Nat.card h.B := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (h.B.subgroupOf h.T)
    have h2 : Nat.card (h.B.subgroupOf h.T) = Nat.card h.B := by
      rw [← Subgroup.card_map_of_injective h.T.subtype_injective, subgroupOf_map_subtype,
        inf_of_le_left hBT]
    rw [h1, hTB4, h2]
  have hB4 : Nat.card h.B ≤ 4 := by
    obtain ⟨f, hf⟩ := hB7 H h
    exact hTB4 ▸ Nat.card_le_card_of_injective f hf
  have hcardB' : Nat.card B' = Nat.card h.B :=
    card_map_of_injective (MulAut.conj h.x⁻¹).injective
  have hB'T : B' ≤ h.T := by
    intro y hy
    rw [hB'def, mem_conjugate_iff] at hy
    have := hconjT' (hBT hy)
    rwa [show h.x⁻¹ * (h.x * y * h.x⁻¹) * h.x = y by group] at this
  have hBB' : h.B ⊓ B' = ⊥ := h.inf_conjugate_x
  have hKB : ∀ {k : H}, k ∈ h.K → ∀ {b : H}, b ∈ h.B → k * b = b * k := fun hk b hb =>
    (mem_centralizer_iff.mp ((h.toHyp52.K_le_layer_W.trans h.toHyp52.V_le_centralizer_B) hk)
      b hb).symm
  have hZK : center (OddBar h.K) = ⊥ := center_eq_bot_of_mulEquiv_alternating (by norm_num) eK
  have hAB : A ⊓ h.B = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨⟨hyT, hyK⟩, hyB⟩ := mem_inf.mp hy |>.imp_left mem_inf.mp
    have h6 := hB6 H h.toHyp52
    rw [h.toHyp52.V_eq_K hKa] at h6
    have hyC : y ∈ h.K ⊓ coreActionKernel h.K := mem_inf.mpr ⟨hyK, h6.1 hyB⟩
    rw [← map_fusionZStar_eq, fusionZStar_eq_of_center_eq_bot hZK] at hyC
    obtain ⟨w, hw, rfl⟩ := mem_map.mp hyC
    have hodd := CFSG.pPrimeCore_coprime_card (p := 2) (G := h.K)
    have hdvd : orderOf (⟨w, hw⟩ : pPrimeCore 2 h.K) ∣ Nat.card (pPrimeCore 2 h.K) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at hdvd
    have h2 : orderOf (w : H) ∣ 2 := orderOf_dvd_of_pow_eq_one (hT2 _ hyT)
    rw [Subgroup.orderOf_coe] at h2
    have h3 : Nat.Coprime 2 (orderOf w) := Nat.Coprime.coprime_dvd_right hdvd hodd
    have h4 : orderOf w = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h5 | h5
      · exact h5
      · rw [h5] at h3; exact absurd h3 (by norm_num)
    rw [orderOf_eq_one_iff] at h4
    rw [mem_bot, subtype_apply, h4, OneMemClass.coe_one]
  have hAT : A ≤ h.T := inf_le_left
  have hTAB : h.T = A ⊔ h.B := by
    symm
    apply Subgroup.eq_of_le_of_card_ge (sup_le hAT hBT)
    rw [hcardT, ← hA4]
    exact card_mul_le_card_sup hAB
  have hANB : ∀ X : Subgroup H, X ≤ h.T → A ≤ normalizer (X : Set H) := by
    intro X hX u hu
    apply mem_normalizer_of_conj_mem
    · intro y hy
      rw [hTab u (hAT hu) y (hX hy), mul_inv_cancel_right]
      exact hy
    · intro y hy
      rw [mul_assoc, hTab y (hX hy) u (hAT hu), ← mul_assoc, inv_mul_cancel, one_mul]
      exact hy
  have hdecomp : ∀ {X : Subgroup H}, X ≤ h.T → ∀ {t : H}, t ∈ A ⊔ X → ∃ α ∈ A, ∃ β ∈ X,
      α * β = t := by
    intro X hX t ht
    have hm : t ∈ (A : Set H) * (X : Set H) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hANB X hX)]
      exact ht
    exact Set.mem_mul.mp hm
  have hN₀A : ∀ {n : H}, n ∈ N₀ → ∀ {u : H}, u ∈ A → n * u * n⁻¹ ∈ A := by
    intro n hn u hu
    exact mem_inf.mpr ⟨(mem_normalizer_iff.mp (hN₀T hn) u).mp (hAT hu),
      mul_mem (mul_mem (hN₀K hn) (mem_inf.mp hu).2) (inv_mem (hN₀K hn))⟩
  have hN₀b : ∀ {n : H}, n ∈ N₀ → ∀ {b : H}, b ∈ h.B → n * b * n⁻¹ = b := by
    intro n hn b hb
    rw [(mem_centralizer_iff.mp (hN₀B hn) b hb).symm, mul_inv_cancel_right]
  have haT : h.a ∈ h.T :=
    mem_inf.mpr ⟨mem_inf.mpr ⟨h.toHyp52.a_mem_S, h.a_mem_normalizer⟩, h.toHyp52.a_mem_P⟩
  have haB : h.a ∉ h.B := h.toHyp52.a_not_mem_B
  have hZJ : center (OddBar h.J) = ⊥ := center_eq_bot_of_mulEquiv_alternating (by norm_num) eJ
  have hDP := h.toHyp52.D_inf_P_eq_bot hZJ
  have haA : h.a ∉ A := by
    intro ha
    obtain ⟨g, hgK, hgD⟩ := haA ha
    have hmem : g⁻¹ * h.a * g ∈ h.J ⊔ zpowers h.a := mem_sup_left (h.toHyp52.D_le_J hgD)
    have hnot : g⁻¹ * h.a * g ∉ zpowers h.a := by
      intro hm
      have h1 : g⁻¹ * h.a * g ∈ h.D ⊓ h.P :=
        mem_inf.mpr ⟨hgD, zpowers_le.mpr h.toHyp52.a_mem_P hm⟩
      rw [hDP, mem_bot] at h1
      have : h.a = 1 := by
        calc h.a = g * (g⁻¹ * h.a * g) * g⁻¹ := by group
          _ = 1 := by rw [h1]; group
      have h2 := h.orderOf_a
      rw [this, orderOf_one] at h2
      exact absurd h2 (by norm_num)
    have hPP := h.toHyp52.inf_conjugate_P_eq_bot hB1 hB6 hCF23 hCF24 hCFc cfSmallInv hmem hnot
    apply h.B_ne_bot
    rw [eq_bot_iff]
    intro b hb
    have hbg : b ∈ conjugate h.P g := by
      rw [mem_conjugate_iff, hKB hgK hb, mul_inv_cancel_right]
      exact h.toHyp52.B_le_P hb
    exact hPP ▸ mem_inf.mpr ⟨h.toHyp52.B_le_P hb, hbg⟩
  obtain ⟨a₀, ha₀, b₁, hb₁, hab⟩ := hdecomp hBT (hTAB ▸ haT)
  have ha₀1 : a₀ ≠ 1 := by
    rintro rfl
    rw [one_mul] at hab
    exact haB (hab ▸ hb₁)
  have hb₁1 : b₁ ≠ 1 := by
    rintro rfl
    rw [mul_one] at hab
    exact haA (hab ▸ ha₀)
  have hBab : ∀ u ∈ h.B, ∀ v ∈ h.B, u * v = v * u := fun u hu v hv =>
    hTab u (hBT hu) v (hBT hv)
  have hx2 : h.x ^ 2 ∈ h.T := by
    obtain ⟨⟨h1, h2⟩, h3⟩ := mem_inf.mp h.x_sq_mem |>.imp_left mem_inf.mp
    exact mem_inf.mpr ⟨mem_inf.mpr ⟨h1, h3⟩, mem_inf.mpr ⟨h1, h2⟩⟩
  have hx2c : ∀ {t : H}, t ∈ h.T → h.x * (h.x * t * h.x⁻¹) * h.x⁻¹ = t := by
    intro t ht
    have h1 := hTab _ hx2 t ht
    calc h.x * (h.x * t * h.x⁻¹) * h.x⁻¹ = (h.x * h.x * t) * (h.x * h.x)⁻¹ := by group
      _ = t := by rw [← pow_two, h1, mul_inv_cancel_right]
  have hAB' : A ≠ B' := by
    intro hAeq
    have hc4 : Nat.card h.B = 4 := by rw [← hcardB', ← hAeq, hA4]
    set m := h.x * n₂ * h.x⁻¹ with hm
    have hconjB : ∀ {c : H}, (∀ y ∈ A, c * y * c⁻¹ ∈ A) →
        ∀ β ∈ h.B, h.x * c * h.x⁻¹ * β * (h.x * c * h.x⁻¹)⁻¹ ∈ h.B := by
      intro c hc β hβ
      have h1 : h.x⁻¹ * β * h.x ∈ A := by
        rw [hAeq, hB'def, mem_conjugate_iff, show h.x * (h.x⁻¹ * β * h.x) * h.x⁻¹ = β by group]
        exact hβ
      have h2 := hc _ h1
      rw [hAeq, hB'def, mem_conjugate_iff] at h2
      rwa [show h.x * (c * (h.x⁻¹ * β * h.x) * c⁻¹) * h.x⁻¹ =
        h.x * c * h.x⁻¹ * β * (h.x * c * h.x⁻¹)⁻¹ by group] at h2
    have hmW : m ∈ h.W := by
      apply mem_normalizer_of_conj_mem
      · exact hconjB (fun y hy => hN₀A hn₂ hy)
      · intro β hβ
        have := hconjB (c := n₂⁻¹) (fun y hy => hN₀A (inv_mem hn₂) hy) β hβ
        rwa [show h.x * n₂⁻¹ * h.x⁻¹ = m⁻¹ by rw [hm]; group, inv_inv] at this
    have hm2 : m ^ 2 ^ k₂ = 1 := by
      rw [hm, conj_pow, hk₂, mul_one, mul_inv_cancel]
    have hmC := h.toHyp52.two_element_mem_centralizer_B hB6 hKa hW hBab hmW hm2
    apply hn₂u
    have hu₂B : h.x * u₂ * h.x⁻¹ ∈ h.B := by
      have := hu₂
      rw [hAeq, hB'def, mem_conjugate_iff] at this
      exact this
    have h1 := mem_centralizer_iff.mp hmC _ hu₂B
    have h2 : h.x * (n₂ * u₂ * n₂⁻¹) * h.x⁻¹ = h.x * u₂ * h.x⁻¹ := by
      calc h.x * (n₂ * u₂ * n₂⁻¹) * h.x⁻¹
          = m * (h.x * u₂ * h.x⁻¹) * m⁻¹ := by rw [hm]; group
        _ = h.x * u₂ * h.x⁻¹ := by rw [← h1, mul_inv_cancel_right]
    have h3 := congrArg (fun y => h.x⁻¹ * y * h.x) h2
    simpa [mul_assoc] using h3
  set M := A ⊔ B' with hMdef
  have hMT : M ≤ h.T := sup_le hAT hB'T
  have hmemB' : ∀ {y : H}, y ∈ B' → h.x * y * h.x⁻¹ ∈ h.B := fun hy => by
    rw [hB'def, mem_conjugate_iff] at hy
    exact hy
  have hcrit : ∀ {t : H}, t ∈ M → t ∉ h.B → (∃ g : H, g * h.a * g⁻¹ = t) →
      ((∃ κ ∈ A ⊓ B', κ ≠ 1) ∨ t ∉ A) → False := by
    intro t htM htB ⟨g, hg⟩ hκ
    obtain ⟨α, hα, β, hβ, hαβ⟩ := hdecomp hBT (hTAB ▸ hMT htM)
    have hα1 : α ≠ 1 := by
      rintro rfl
      rw [one_mul] at hαβ
      exact htB (hαβ ▸ hβ)
    have hβM : β ∈ M := by
      have := mul_mem (inv_mem (mem_sup_left hα : α ∈ M)) htM
      rwa [← hαβ, inv_mul_cancel_left] at this
    obtain ⟨α₂, hα₂, β₂, hβ₂, hαβ₂⟩ := hdecomp hB'T hβM
    obtain ⟨α', hα', hα'1, hα'β⟩ : ∃ α' ∈ A, α' ≠ 1 ∧ α' * β ∈ B' := by
      by_cases h₂ : α₂ = 1
      · rw [h₂, one_mul] at hαβ₂
        have hβ1 : β = 1 := by
          have : β ∈ h.B ⊓ B' := mem_inf.mpr ⟨hβ, hαβ₂ ▸ hβ₂⟩
          rw [hBB', mem_bot] at this
          exact this
        rcases hκ with ⟨κ, hκm, hκ1⟩ | htA
        · refine ⟨κ, (mem_inf.mp hκm).1, hκ1, ?_⟩
          rw [hβ1, mul_one]
          exact (mem_inf.mp hκm).2
        · exfalso
          apply htA
          rw [← hαβ, hβ1, mul_one]
          exact hα
      · refine ⟨α₂, hα₂, h₂, ?_⟩
        rw [← hαβ₂, ← mul_assoc, hsq (hAT hα₂), one_mul]
        exact hβ₂
    obtain ⟨n, hn, hnα⟩ := hN₀tr α hα α' hα' hα1 hα'1
    have hnt : n * t * n⁻¹ = α' * β := by
      rw [← hαβ, show n * (α * β) * n⁻¹ = (n * α * n⁻¹) * (n * β * n⁻¹) by group, hnα,
        hN₀b hn hβ]
    have hne : α' * β ≠ 1 := by
      intro h1
      apply hα'1
      have : α' ∈ A ⊓ h.B := by
        refine mem_inf.mpr ⟨hα', ?_⟩
        rw [eq_inv_of_mul_eq_one_left h1]
        exact inv_mem hβ
      rw [hAB, mem_bot] at this
      exact this
    apply hnf' (h.x * n * g)
    have : h.x * n * g * h.a * (h.x * n * g)⁻¹ = h.x * (n * (g * h.a * g⁻¹) * n⁻¹) * h.x⁻¹ := by
      group
    rw [this, hg, hnt]
    exact hmemB' hα'β
  have haM : ∀ {y : H}, y ∈ A → y * b₁ ∈ M → b₁ ∈ M := by
    intro y hy hyM
    have := mul_mem (inv_mem (mem_sup_left hy : y ∈ M)) hyM
    rwa [inv_mul_cancel_left] at this
  by_cases hb₁M : b₁ ∈ M
  ·
    have haMem : h.a ∈ M := hab ▸ mul_mem (mem_sup_left ha₀) hb₁M
    exact hcrit haMem haB ⟨1, by group⟩ (Or.inr haA)
  ·
    have hκ : ∃ κ ∈ A ⊓ B', κ ≠ 1 := by
      by_contra hne
      push Not at hne
      have hbot : A ⊓ B' = ⊥ := by
        rw [eq_bot_iff]
        intro y hy
        exact mem_bot.mpr (hne y hy)
      have hMeq : M = h.T := by
        apply Subgroup.eq_of_le_of_card_ge hMT
        rw [hcardT, ← hA4, ← hcardB']
        exact card_mul_le_card_sup hbot
      exact hb₁M (hMeq ▸ hBT hb₁)
    set M' := conjugate M h.x with hM'def
    have hBM' : h.B ≤ M' := by
      intro β hβ
      rw [hM'def, mem_conjugate_iff]
      apply mem_sup_right
      rw [hB'def, mem_conjugate_iff, hx2c (hBT hβ)]
      exact hβ
    have hM'T : M' ≤ h.T := by
      intro y hy
      rw [hM'def, mem_conjugate_iff] at hy
      have := hconjT' (hMT hy)
      rwa [show h.x⁻¹ * (h.x * y * h.x⁻¹) * h.x = y by group] at this
    have hcardM' : Nat.card M' = Nat.card M := card_map_of_injective (MulAut.conj h.x⁻¹).injective
    have hBltM : Nat.card h.B < Nat.card M := by
      rw [← hcardB']
      apply Subgroup.card_lt_of_lt
      refine lt_of_le_of_ne le_sup_right fun heq => hAB' ?_
      have hAle : A ≤ B' := by
        rw [heq]
        exact le_sup_left
      apply Subgroup.eq_of_le_of_card_ge hAle
      rw [hA4, hcardB']
      exact hB4
    obtain ⟨a', ha'm, ha'1⟩ : ∃ a' ∈ A ⊓ M', a' ≠ 1 := by
      by_contra hne
      push Not at hne
      have hbot : A ⊓ M' = ⊥ := by
        rw [eq_bot_iff]
        intro y hy
        exact mem_bot.mpr (hne y hy)
      have h1 := card_mul_le_card_sup hbot
      have h2 : Nat.card ↥(A ⊔ M') ≤ Nat.card h.T := Subgroup.card_le_of_le (sup_le hAT hM'T)
      rw [hA4, hcardM', hcardT] at *
      omega
    obtain ⟨ha'A, ha'M'⟩ := mem_inf.mp ha'm
    obtain ⟨n, hn, hna⟩ := hN₀tr a₀ ha₀ a' ha'A ha₀1 ha'1
    have hna' : n * h.a * n⁻¹ = a' * b₁ := by
      rw [← hab, show n * (a₀ * b₁) * n⁻¹ = (n * a₀ * n⁻¹) * (n * b₁ * n⁻¹) by group, hna,
        hN₀b hn hb₁]
    have ht₀ : a' * b₁ ∈ M' := mul_mem ha'M' (hBM' hb₁)
    have ht₁M : h.x * (a' * b₁) * h.x⁻¹ ∈ M := by
      have := ht₀
      rw [hM'def, mem_conjugate_iff] at this
      exact this
    have ht₁B : h.x * (a' * b₁) * h.x⁻¹ ∉ h.B := by
      intro hB
      apply hb₁M
      have h1 : a' * b₁ ∈ B' := by
        rw [hB'def, mem_conjugate_iff]
        exact hB
      apply haM ha'A
      exact mem_sup_right h1
    exact hcrit ht₁M ht₁B ⟨h.x * n, by rw [← hna']; group⟩ (Or.inl hκ)

end Hyp59

namespace Hyp52

variable {H : Type} [Group H] [Finite H] (h : Hyp52 H)

theorem not_row515 (hB1 : ConjFixStatement) (hB6 : SylowKernelStatement)
    (hB7 : EmbedsTQuotStatement) (hCF23 : CFProp23Fusion) (hCF24 : CFProp24c)
    (hCFc : CFProp23Center) (hP21 : CFProp21A10) (hLoc : CFA10Local) (hNO : CFA10NoOuter)
    (hsec : h.SectionData) : ¬ h.Row515 := by
  intro hrow
  obtain ⟨⟨eJ⟩, hKa, ⟨eK⟩⟩ := hrow
  obtain ⟨H', _, _, h', -, -, -, hK', hJ', hKa', -, -⟩ := hsec
  obtain ⟨eK'⟩ := hK' (center_eq_bot_of_mulEquiv_alternating (by norm_num) eK)
  obtain ⟨eJ'⟩ := hJ' (center_eq_bot_of_mulEquiv_alternating (by norm_num) eJ)
  exact h'.false_of_row515 hB1 hB6 hB7 hCF23 hCF24 hCFc hP21 hLoc hNO
    ⟨⟨eJ'.trans eJ⟩, hKa'.mpr hKa, ⟨eK'.trans eK⟩⟩

end Hyp52

end CFSG.ComponentClassification.GSThmB
