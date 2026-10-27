module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415KA

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ABGLocalTools HarrisEnd

namespace L415

theorem false_of_B {X : Type} [Group X] [Finite X] {β t z₁ z : X}
    {Kb₁ Kb₂ : Subgroup (MBar β)} (htM : t ∈ centralizer ({β} : Set X)) (ht2 : t * t = 1)
    (hprod : IsProd (layer (MBar β)) Kb₁ Kb₂ (QuotientGroup.mk ⟨t, htM⟩))
    {W : Subgroup X} (hW : IsSylowOf 2 W (centralizer {β})) (htW : t ∈ W) (hz₁W : z₁ ∈ W)
    (hzz : z = z₁ * (t * z₁ * t⁻¹)) (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1)
    (hmk : ∀ hz₁ : z₁ ∈ centralizer ({β} : Set X),
      (QuotientGroup.mk ⟨z₁, hz₁⟩ : MBar β) ∈ Kb₁)
    (hnab : ∃ a ∈ barOf (centralizer {β}) W ⊓ Kb₁, ∃ b ∈ barOf (centralizer {β}) W ⊓ Kb₁,
      a * b ≠ b * a)
    (hcen : ∀ c ∈ barOf (centralizer {β}) W ⊓ Kb₁,
      (∀ d ∈ barOf (centralizer {β}) W ⊓ Kb₁, c * d = d * c) →
        c = 1 ∨ c = QuotientGroup.mk ⟨z₁, hW.le hz₁W⟩)
    (hA : AutPSL2RCentralizerInput) {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hlie : Blueprint.LieModel ↥Kb₁ .PSL 2 p n)
    (h8 : 8 ≤ Nat.card ↥(barOf (centralizer {β}) W ⊓ Kb₁))
    (hQ : pCore 2 (MBar β) =
      centralizer ((layer (MBar β) : Subgroup (MBar β)) : Set (MBar β)))
    (hQ4 : Nat.card ↥(pCore 2 (MBar β)) ≤ 4)
    (hQt : pCore 2 (MBar β) ⊓ centralizer {(QuotientGroup.mk ⟨t, htM⟩ : MBar β)} =
      zpowers (betaBar β))
    (hβW : β ∈ W) (hβ1 : β ≠ 1) (hβ2 : β * β = 1)
    (h42h : ∀ E : Subgroup X, E ≤ W ⊓ centralizer {t} →
      (∀ g ∈ W ⊓ centralizer {t}, ∀ e ∈ E, g * e * g⁻¹ ∈ E) → z ∉ E → ∀ e ∈ E, e ^ 2 = 1)
    {B Y : Subgroup X} (hBW : B ≤ W) (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hBn : ∀ g ∈ W, ∀ b ∈ B, g * b * g⁻¹ ∈ B) (hYB : Y ≤ B) (hY4 : Nat.card Y = 4)
    (hY2 : ∀ b ∈ B, b ^ 2 = 1 ↔ b ∈ Y) (hYsq : ∀ y ∈ Y, ∃ b ∈ B, b ^ 2 = y)
    (hz₁B : z₁ ∉ B) (hz₂B : t * z₁ * t⁻¹ ∉ B) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := centralizer ({β} : Set X) with hMdef
  have hWM : W ≤ M := hW.le
  have hWp := hW.isPGroup
  have hE : (layer (MBar β)).Normal := by
    have := LocalCores.layer_characteristic (G := MBar β)
    infer_instance
  set s : MBar β := QuotientGroup.mk ⟨t, htM⟩ with hsdef
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hs2 : s * s = 1 := by
    rw [hsdef, ← QuotientGroup.mk_mul]
    have : (⟨t, htM⟩ : ↥M) * ⟨t, htM⟩ = 1 := Subtype.ext ht2
    rw [this, QuotientGroup.mk_one]
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  set P := barOf M W with hPdef
  have hP : IsSylowOf 2 P ⊤ := isSylowOf_barOf hW
  have hsP : s ∈ P := mk_mem_barOf htM htW
  have htβ : t * β = β * t := mem_centralizer_singleton_iff.mp htM
  set Bb := barOf M B with hBb
  have hBbc : ∀ a ∈ Bb, ∀ b ∈ Bb, a * b = b * a := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hBc x hx y hy)
  have hBbn : ∀ d ∈ P, ∀ b ∈ Bb, d * b * d⁻¹ ∈ Bb := by
    rintro _ ⟨g, hg, rfl⟩ _ ⟨y, hy, rfl⟩
    exact ⟨g * y * g⁻¹, hBn g hg y hy, by simp only [map_mul, map_inv]⟩
  have hBbP : Bb ≤ P := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨y, hBW hy, rfl⟩
  have hz₁M : z₁ ∈ M := hWM hz₁W
  set zb₁ : MBar β := QuotientGroup.mk ⟨z₁, hz₁M⟩ with hzb₁
  have hzb₁B : zb₁ ∉ Bb := by
    rintro ⟨y, hy, hyz⟩
    apply hz₁B
    have : (y : X) = z₁ := mk_injOn hWM hWp (hBW hy) hz₁W hyz
    rw [← this]
    exact hy
  have hz₂W : t * z₁ * t⁻¹ ∈ W := mul_mem (mul_mem htW hz₁W) (inv_mem htW)
  have hz₂M : t * z₁ * t⁻¹ ∈ M := hWM hz₂W
  have hzb₂ : (QuotientGroup.mk ⟨t * z₁ * t⁻¹, hz₂M⟩ : MBar β) = s⁻¹ * zb₁ * s := by
    rw [hsi]
    have : (⟨t * z₁ * t⁻¹, hz₂M⟩ : ↥M) = ⟨t, htM⟩ * ⟨z₁, hz₁M⟩ * ⟨t, htM⟩ :=
      Subtype.ext (by show t * z₁ * t⁻¹ = t * z₁ * t; rw [hti])
    rw [this]
    simp only [QuotientGroup.mk_mul]
    rfl
  have hzb₂B : s⁻¹ * zb₁ * s ∉ Bb := by
    rw [← hzb₂]
    rintro ⟨y, hy, hyz⟩
    apply hz₂B
    have : (y : X) = t * z₁ * t⁻¹ := mk_injOn hWM hWp (hBW hy) hz₂W hyz
    rw [← this]
    exact hy
  have hPK₁ : ∀ d ∈ P ⊓ Kb₁, ∀ b ∈ Bb, d * b * d⁻¹ ∈ Bb := fun d hd b hb =>
    hBbn d (mem_inf.mp hd).1 b hb
  have hmapK : ∀ b ∈ Bb, Kb₁.map (MulAut.conj b).toMonoidHom = Kb₁ := fun b hb =>
    hprod.map_K₁_of_abelian hE hBbc hPK₁ hnab hb
  have hcomm₁ : ∀ b ∈ Bb, ∀ d ∈ P ⊓ Kb₁, d * b = b * d := by
    intro b hb
    refine comm_of_inf_eq (hP.isPGroup.to_le inf_le_left) hcen hzb₁B hPK₁ hb ?_
    intro d hd
    refine mem_inf.mpr ⟨mul_mem (mul_mem (hBbP hb) (mem_inf.mp hd).1) (inv_mem (hBbP hb)), ?_⟩
    rw [← hmapK b hb]
    exact ⟨d, (mem_inf.mp hd).2, rfl⟩
  have hcen₂ : ∀ c ∈ P ⊓ Kb₂, (∀ d ∈ P ⊓ Kb₂, c * d = d * c) →
      c = 1 ∨ c = s⁻¹ * zb₁ * s := by
    intro c hc hcc
    have h1 : s * c * s⁻¹ ∈ P ⊓ Kb₁ := mem_inf.mpr ⟨mul_mem (mul_mem hsP (mem_inf.mp hc).1)
      (inv_mem hsP), hprod.mem_K₂_iff.mp (mem_inf.mp hc).2⟩
    have h2 : ∀ d ∈ P ⊓ Kb₁, s * c * s⁻¹ * d = d * (s * c * s⁻¹) := by
      intro d hd
      have h3 : s⁻¹ * d * s ∈ P ⊓ Kb₂ := mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hsP)
        (mem_inf.mp hd).1) hsP, hprod.conj_mem_K₂ (mem_inf.mp hd).2⟩
      have h4 := hcc _ h3
      calc s * c * s⁻¹ * d = s * (c * (s⁻¹ * d * s)) * s⁻¹ := by group
        _ = s * ((s⁻¹ * d * s) * c) * s⁻¹ := by rw [h4]
        _ = d * (s * c * s⁻¹) := by group
    rcases hcen _ h1 h2 with h5 | h5
    · left
      calc c = s⁻¹ * (s * c * s⁻¹) * s := by group
        _ = 1 := by rw [h5]; group
    · right
      calc c = s⁻¹ * (s * c * s⁻¹) * s := by group
        _ = s⁻¹ * zb₁ * s := by rw [h5]
  have hPK₂ : ∀ d ∈ P ⊓ Kb₂, ∀ b ∈ Bb, d * b * d⁻¹ ∈ Bb := fun d hd b hb =>
    hBbn d (mem_inf.mp hd).1 b hb
  have hcomm₂ : ∀ b ∈ Bb, ∀ d ∈ P ⊓ Kb₂, d * b = b * d := by
    intro b hb
    refine comm_of_inf_eq (hP.isPGroup.to_le inf_le_left) hcen₂ hzb₂B hPK₂ hb ?_
    intro d hd
    refine mem_inf.mpr ⟨mul_mem (mul_mem (hBbP hb) (mem_inf.mp hd).1) (inv_mem (hBbP hb)), ?_⟩
    rw [← hprod.map_K₂_of_map_K₁ hE (hmapK b hb)]
    exact ⟨d, (mem_inf.mp hd).2, rfl⟩
  have hS₁ := hprod.isSylowOf_inf_K₁ hE hP
  have hS₂ := hprod.isSylowOf_inf_K₂ hE hP
  have hcard₂ : Nat.card ↥(P ⊓ Kb₂) = Nat.card ↥(P ⊓ Kb₁) := by
    rw [hS₁.card_eq, hS₂.card_eq, ← Nat.card_congr hprod.equivK₂.toEquiv]
  have hlie₂ := GSThmB.OddQuot.lieModel_of_equiv hprod.equivK₂ hlie
  have h2el : ∀ b ∈ Bb, ∃ k : ℕ, orderOf b = 2 ^ k := by
    intro b hb
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP.isPGroup) ⟨b, hBbP hb⟩
    rw [Subgroup.orderOf_mk] at hk
    exact ⟨k, hk⟩
  have hsqQ : ∀ b ∈ Bb, b ^ 2 ∈ pCore 2 (MBar β) := by
    intro b hb
    have hN₁ : b ∈ normalizer (Kb₁ : Set (MBar β)) :=
      (IsProd.mem_normalizer_iff_map _ _).mpr (hmapK b hb)
    have hN₂ : b ∈ normalizer (Kb₂ : Set (MBar β)) :=
      (IsProd.mem_normalizer_iff_map _ _).mpr (hprod.map_K₂_of_map_K₁ hE (hmapK b hb))
    have h1 := IsProd.sq_comm_of_fix' hA hp hp2 hlie hS₁ h8 (h2el b hb) hN₁
      (fun d hd => hcomm₁ b hb d hd)
    have h2 := IsProd.sq_comm_of_fix' hA hp hp2 hlie₂ hS₂ (hcard₂ ▸ h8) (h2el b hb) hN₂
      (fun d hd => hcomm₂ b hb d hd)
    rw [hQ, Subgroup.mem_centralizer_iff]
    intro e he
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := hprod.exists_mul he
    calc k₁ * k₂ * b ^ 2 = k₁ * (k₂ * b ^ 2) := by group
      _ = k₁ * (b ^ 2 * k₂) := by rw [← h2 k₂ hk₂]
      _ = (k₁ * b ^ 2) * k₂ := by group
      _ = (b ^ 2 * k₁) * k₂ := by rw [← h1 k₁ hk₁]
      _ = b ^ 2 * (k₁ * k₂) := by group
  have hYW : Y ≤ W := hYB.trans hBW
  have hYbQ : barOf M Y ≤ pCore 2 (MBar β) := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨b, hbB, hby⟩ := hYsq y hy
    have h1 := hsqQ (QuotientGroup.mk ⟨b, hWM (hBW hbB)⟩) ⟨⟨b, hWM (hBW hbB)⟩, hbB, rfl⟩
    rw [← QuotientGroup.mk_pow] at h1
    have h2 : (⟨b, hWM (hBW hbB)⟩ : ↥M) ^ 2 = y :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hby)
    rw [h2] at h1
    exact h1
  have hYcard : Nat.card ↥(barOf M Y) = 4 := by
    rw [card_barOf (hYW.trans hWM) (hWp.to_le hYW), hY4]
  have hYQ : barOf M Y = pCore 2 (MBar β) :=
    eq_of_le_of_card_ge hYbQ (by rw [hYcard]; exact hQ4)
  have hβY : β ∈ Y := by
    have h1 : betaBar β ∈ pCore 2 (MBar β) := by
      have : betaBar β ∈ pCore 2 (MBar β) ⊓ centralizer {s} := hQt ▸ mem_zpowers _
      exact (mem_inf.mp this).1
    rw [← hYQ] at h1
    obtain ⟨y, hy, hyb⟩ := mem_barOf.mp h1
    have : (y : X) = β := mk_injOn hWM hWp (hYW hy) hβW hyb
    rw [← this]
    exact hy
  have hβb2 : betaBar β * betaBar β = 1 := by
    rw [betaBar, ← QuotientGroup.mk_mul]
    have : (⟨β, mem_centralizer_singleton_iff.mpr rfl⟩ : ↥M) *
        ⟨β, mem_centralizer_singleton_iff.mpr rfl⟩ = 1 := Subtype.ext hβ2
    rw [this, QuotientGroup.mk_one]
  have hYt : ∀ y ∈ Y, y * t = t * y → y = 1 ∨ y = β := by
    intro y hy hyt
    have h1 : (QuotientGroup.mk ⟨y, hWM (hYW hy)⟩ : MBar β) ∈
        pCore 2 (MBar β) ⊓ centralizer {s} := by
      refine mem_inf.mpr ⟨hYQ ▸ mk_mem_barOf _ hy, mem_centralizer_singleton_iff.mpr ?_⟩
      rw [hsdef, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext hyt
    rw [hQt] at h1
    rcases mem_zpowers_two hβb2 h1 with h2 | h2
    · left
      exact mk_injOn hWM hWp (hYW hy) (one_mem W) (by rw [h2]; rfl)
    · right
      exact mk_injOn hWM hWp (hYW hy) hβW h2
  have hYn : ∀ y ∈ Y, t * y * t⁻¹ ∈ Y := by
    intro y hy
    have h1 : t * y * t⁻¹ ∈ B := hBn t htW y (hYB hy)
    rw [← hY2 _ h1, conj_pow, (hY2 y (hYB hy)).mpr hy]
    group
  have hYncard : (Y : Set X).ncard = 4 := by
    rw [← hY4, ← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
  obtain ⟨q₀, hq₀Y, hq₀1, hq₀β⟩ : ∃ q₀ ∈ Y, q₀ ≠ 1 ∧ q₀ ≠ β := by
    by_contra hno
    push Not at hno
    have hsub : (Y : Set X) ⊆ {1, β} := fun y hy => by
      by_cases h1 : y = 1
      · exact Or.inl h1
      · exact Or.inr (hno y hy h1)
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [hYncard, Set.ncard_pair (Ne.symm hβ1)] at h1
    omega
  have hq₀2 : q₀ ^ 2 = 1 := (hY2 q₀ (hYB hq₀Y)).mpr hq₀Y
  have hq₀βY : q₀ * β ∈ Y := mul_mem hq₀Y hβY
  have hq₀β2 : (q₀ * β) ^ 2 = 1 := (hY2 _ (hYB hq₀βY)).mpr hq₀βY
  have hYeq : (Y : Set X) = {1, β, q₀, q₀ * β} := by
    symm
    apply Set.eq_of_subset_of_ncard_le
    · intro y hy
      rcases hy with rfl | rfl | rfl | rfl
      · exact one_mem Y
      · exact hβY
      · exact hq₀Y
      · exact hq₀βY
    · rw [hYncard]
      have h1 : (1 : X) ≠ q₀ * β := fun h => hq₀β (by
        calc q₀ = q₀ * β * β := by rw [mul_assoc, hβ2, mul_one]
          _ = β := by rw [← h, one_mul])
      have h2 : β ≠ q₀ * β := fun h => hq₀1 (by
        calc q₀ = q₀ * β * β⁻¹ := by group
          _ = 1 := by rw [← h, mul_inv_cancel])
      have h3 : q₀ ≠ q₀ * β := fun h => hβ1 (by
        calc β = q₀⁻¹ * (q₀ * β) := by group
          _ = 1 := by rw [← h, inv_mul_cancel])
      rw [Set.ncard_insert_of_notMem (by simp [Ne.symm hβ1, Ne.symm hq₀1, h1]),
        Set.ncard_insert_of_notMem (by simp [hq₀β.symm, h2]), Set.ncard_pair h3]
    · exact Set.toFinite _
  have htq₀ : t * q₀ * t⁻¹ = q₀ * β := by
    have hmem : t * q₀ * t⁻¹ ∈ (Y : Set X) := hYn q₀ hq₀Y
    rw [hYeq] at hmem
    rcases hmem with h1 | h1 | h1 | h1
    · exfalso
      apply hq₀1
      calc q₀ = t⁻¹ * (t * q₀ * t⁻¹) * t := by group
        _ = 1 := by rw [h1]; group
    · exfalso
      apply hq₀β
      calc q₀ = t⁻¹ * (t * q₀ * t⁻¹) * t := by group
        _ = t⁻¹ * (β * t) := by rw [h1, mul_assoc]
        _ = t⁻¹ * (t * β) := by rw [htβ]
        _ = β := by group
    · exfalso
      rcases hYt q₀ hq₀Y (by
          calc q₀ * t = (t * q₀ * t⁻¹) * t := by rw [h1]
            _ = t * q₀ := by group) with h2 | h2
      · exact hq₀1 h2
      · exact hq₀β h2
    · exact h1
  obtain ⟨b₀, hb₀B, hb₀2⟩ := hYsq β hβY
  have htb₀ : t * b₀ * t⁻¹ ∈ B := hBn t htW b₀ hb₀B
  have htβ' : t * β * t⁻¹ = β := by rw [htβ]; group
  set c := b₀⁻¹ * (t * b₀ * t⁻¹) with hc
  have hcB : c ∈ B := mul_mem (inv_mem hb₀B) htb₀
  have hc2 : c ^ 2 = 1 := by
    have hcomm := hBc _ (inv_mem hb₀B) _ htb₀
    calc c ^ 2 = b₀⁻¹ * ((t * b₀ * t⁻¹) * b₀⁻¹) * (t * b₀ * t⁻¹) := by rw [hc, sq]; group
      _ = b₀⁻¹ * (b₀⁻¹ * (t * b₀ * t⁻¹)) * (t * b₀ * t⁻¹) := by rw [← hcomm]
      _ = (b₀ ^ 2)⁻¹ * (t * b₀ ^ 2 * t⁻¹) := by rw [sq]; group
      _ = 1 := by rw [hb₀2, htβ', inv_mul_cancel]
  have hcY : c ∈ Y := (hY2 c hcB).mp hc2
  have htc : t * b₀ * t⁻¹ = b₀ * c := by rw [hc]; group
  have htt : ∀ y : X, t * (t * y * t⁻¹) * t⁻¹ = y := fun y => by
    rw [show t * (t * y * t⁻¹) * t⁻¹ = (t * t) * y * (t * t)⁻¹ by group, ht2]
    group
  obtain ⟨b', hb'B, hb't, hb'2⟩ : ∃ b' ∈ B, b' * t = t * b' ∧ b' ^ 2 = β := by
    have hmem : c ∈ (Y : Set X) := hcY
    rw [hYeq] at hmem
    rcases hmem with h1 | h1 | h1 | h1
    · refine ⟨b₀, hb₀B, ?_, hb₀2⟩
      have h2 : t * b₀ * t⁻¹ = b₀ := by rw [htc, h1, mul_one]
      calc b₀ * t = (t * b₀ * t⁻¹) * t := by rw [h2]
        _ = t * b₀ := by group
    · refine ⟨b₀ * q₀, mul_mem hb₀B (hYB hq₀Y), ?_, ?_⟩
      · have hcomm := hBc _ (hYB hβY) _ (hYB hq₀Y)
        have h2 : t * (b₀ * q₀) * t⁻¹ = b₀ * q₀ := by
          calc t * (b₀ * q₀) * t⁻¹ = (t * b₀ * t⁻¹) * (t * q₀ * t⁻¹) := by group
            _ = b₀ * (β * q₀) * β := by rw [htc, h1, htq₀]; group
            _ = b₀ * (q₀ * β) * β := by rw [hcomm]
            _ = b₀ * q₀ * (β * β) := by group
            _ = b₀ * q₀ := by rw [hβ2, mul_one]
        calc b₀ * q₀ * t = (t * (b₀ * q₀) * t⁻¹) * t := by rw [h2]
          _ = t * (b₀ * q₀) := by group
      · have hcomm := hBc _ hb₀B _ (hYB hq₀Y)
        calc (b₀ * q₀) ^ 2 = b₀ * (q₀ * b₀) * q₀ := by rw [sq]; group
          _ = b₀ * (b₀ * q₀) * q₀ := by rw [hcomm]
          _ = b₀ ^ 2 * q₀ ^ 2 := by rw [sq, sq]; group
          _ = β := by rw [hb₀2, hq₀2, mul_one]
    · exfalso
      have h2 : t * (t * b₀ * t⁻¹) * t⁻¹ = b₀ * β := by
        calc t * (t * b₀ * t⁻¹) * t⁻¹ = t * (b₀ * q₀) * t⁻¹ := by rw [htc, h1]
          _ = (t * b₀ * t⁻¹) * (t * q₀ * t⁻¹) := by group
          _ = b₀ * (q₀ * q₀) * β := by rw [htc, h1, htq₀]; group
          _ = b₀ * β := by rw [← sq, hq₀2, mul_one]
      apply hβ1
      calc β = b₀⁻¹ * (b₀ * β) := by group
        _ = 1 := by rw [← h2, htt, inv_mul_cancel]
    · exfalso
      have h2 : t * (t * b₀ * t⁻¹) * t⁻¹ = b₀ * β := by
        calc t * (t * b₀ * t⁻¹) * t⁻¹ = t * (b₀ * (q₀ * β)) * t⁻¹ := by rw [htc, h1]
          _ = (t * b₀ * t⁻¹) * (t * q₀ * t⁻¹) * (t * β * t⁻¹) := by group
          _ = b₀ * ((q₀ * β) * (q₀ * β)) * β := by rw [htc, h1, htq₀, htβ']; group
          _ = b₀ * β := by rw [← sq, hq₀β2, mul_one]
      apply hβ1
      calc β = b₀⁻¹ * (b₀ * β) := by group
        _ = 1 := by rw [← h2, htt, inv_mul_cancel]
  have hzE : z ∉ B ⊓ centralizer {t} := by
    intro hz
    have hzY : z ∈ Y := (hY2 z (mem_inf.mp hz).1).mp hz2
    have hzQ : (QuotientGroup.mk ⟨z, hWM (hYW hzY)⟩ : MBar β) ∈ pCore 2 (MBar β) :=
      hYQ ▸ mk_mem_barOf _ hzY
    rw [hQ] at hzQ
    have hzE' : (QuotientGroup.mk ⟨z, hWM (hYW hzY)⟩ : MBar β) ∈ layer (MBar β) := by
      have : (⟨z, hWM (hYW hzY)⟩ : ↥M) = ⟨z₁, hz₁M⟩ * ⟨t * z₁ * t⁻¹, hz₂M⟩ := Subtype.ext hzz
      rw [this, QuotientGroup.mk_mul]
      refine mul_mem (hprod.K₁_le (hmk hz₁M)) (hprod.K₂_le ?_)
      rw [hzb₂]
      exact hprod.conj_mem_K₂ (hmk hz₁M)
    have h1 := hprod.eq_one_of_mem_centralizer hzE' hzQ
    exact hz1 (mk_injOn hWM hWp (hYW hzY) (one_mem W) (by rw [h1]; rfl))
  have hEle : B ⊓ centralizer {t} ≤ W ⊓ centralizer {t} := inf_le_inf_right _ hBW
  have hEn : ∀ g ∈ W ⊓ centralizer {t}, ∀ e ∈ B ⊓ centralizer {t},
      g * e * g⁻¹ ∈ B ⊓ centralizer {t} := by
    intro g hg e he
    refine mem_inf.mpr ⟨hBn g (mem_inf.mp hg).1 e (mem_inf.mp he).1, ?_⟩
    have h1 : g * t = t * g := mem_centralizer_singleton_iff.mp (mem_inf.mp hg).2
    have h2 : e * t = t * e := mem_centralizer_singleton_iff.mp (mem_inf.mp he).2
    have hginv : g⁻¹ * t = t * g⁻¹ := by
      calc g⁻¹ * t = g⁻¹ * (t * g) * g⁻¹ := by group
        _ = g⁻¹ * (g * t) * g⁻¹ := by rw [h1]
        _ = t * g⁻¹ := by group
    rw [mem_centralizer_singleton_iff]
    calc g * e * g⁻¹ * t = g * e * (g⁻¹ * t) := by group
      _ = g * e * (t * g⁻¹) := by rw [hginv]
      _ = g * (e * t) * g⁻¹ := by group
      _ = g * (t * e) * g⁻¹ := by rw [h2]
      _ = (g * t) * e * g⁻¹ := by group
      _ = (t * g) * e * g⁻¹ := by rw [h1]
      _ = t * (g * e * g⁻¹) := by group
  have h1 := h42h _ hEle hEn hzE b' (mem_inf.mpr ⟨hb'B, mem_centralizer_singleton_iff.mpr hb't⟩)
  exact hβ1 (hb'2.symm.trans h1)

end L415

end CFSG.ComponentClassification.HarrisLit
