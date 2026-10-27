module

public import CFSG.CGT.T75R.Cases

public section

namespace CFSG.CGT.T75R

open CFSG.Open CFSG.CGT.Timmesfeld75
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T T₁ L S V Tx : Subgroup G} {x : G}

theorem Nbr.ne_left (hV : Nbr T L S V) (hq : Nat.card T = 2 * Nat.card L) : V ≠ T := by
  intro h
  have hL : L = T := by
    rw [← hV.hL, h]
    unfold normIn
    exact inf_eq_left.2 Subgroup.le_normalizer
  rw [hL] at hq
  have : 0 < Nat.card T := Nat.card_pos
  omega

theorem Nbr.dichotomy [IsSimpleGroup G] (h214 : Lemma214) (hInv : InvolutionClassInput)
    (hSz : Section3SzInput) (hnab : ∃ a b : G, a * b ≠ b * a) (htri : TriA)
    (hStep : StepHyp T T₁) (hglob : Sec3Global T) (hiso : Sec3IsoGlobal T)
    (hq : Nat.card T = 2 * Nat.card (normIn T T₁)) (hT8 : Nat.card T = 8)
    (hLT₁ : normIn T T₁ = L) (hV : Nbr T L S V) (hS2 : IsPGroup 2 S)
    (hSN : S ≤ Subgroup.normalizer (T : Set G)) (hSL : S ≤ Subgroup.normalizer (L : Set G))
    (hxS : x ∈ S) (hX : XData T L Tx x) :
    (∃ t ∈ T, conjSubgroup x V = conjSubgroup t V) ∨
      (conjSubgroup x V ≠ V ∧ normIn (conjSubgroup x V) T ⊓ cfgM T V = ⊥) := by
  by_cases hVx : conjSubgroup x V = V
  · left
    exact ⟨1, T.one_mem, by rw [hVx, conjSubgroup_one]⟩
  · have hV' := hV.conj_x hX.hxT hX.hxL hxS
    have hq' : Nat.card T = 2 * Nat.card L := by rw [hq, hLT₁]
    have hcomm := hV.comm_conj_x h214 hInv hSz hnab hS2 hSN hSL hxS
    rcases htri G T T₁ hStep hglob hiso hq hT8 V (conjSubgroup x V) hV.conj hV'.conj
      (hV.ne_left hq') (hV'.ne_left hq') hVx (hV.hL.trans hLT₁.symm) (hV'.hL.trans hLT₁.symm)
      hcomm with h | ⟨t, ht, -, htV⟩
    · right
      exact ⟨hVx, h⟩
    · left
      exact ⟨t, ht, htV⟩

omit [Finite G] in
theorem Nbr.inf_eq_bot (hV : Nbr T L S V) : L ⊓ normIn V T = ⊥ := by
  rw [← hV.hL]
  refine eq_bot_iff.2 fun z hz => ?_
  have h1 : z ∈ T ⊓ V := ⟨(normIn_le _ _) hz.1, (normIn_le _ _) hz.2⟩
  rw [hV.sec3.cfg.inf, Subgroup.mem_bot] at h1
  rw [h1]
  exact Subgroup.one_mem _

omit [Finite G] in
theorem Nbr.conj_x_le (hV : Nbr T L S V) (hX : XData T L Tx x) {t : G} (ht : t ∈ T)
    (htV : conjSubgroup x V = conjSubgroup t V) :
    conjSubgroup x (normIn V T) ≤ cfgM T V := by
  have hA : conjSubgroup x (normIn V T) = conjSubgroup t (normIn V T) := by
    rw [← normIn_conj_right_of_mem_normalizer hX.hxT, htV,
      normIn_conj_right_of_mem_normalizer (Subgroup.le_normalizer ht)]
  rw [hA]
  intro z hz
  obtain ⟨e, he, rfl⟩ := mem_conjSubgroup_iff_exists.1 hz
  have h1 : t * e * t⁻¹ ∈ cfgM T V :=
    hV.sec3.cfg.conj_mem_cfgM (Subgroup.mem_sup_left ht) (Cfg.normIn_le_cfgM_right T V he)
  exact h1

theorem Nbr.caseA_data (hV : Nbr T L S V) (hX : XData T L Tx x) {t : G} (ht : t ∈ T)
    (htV : conjSubgroup x V = conjSubgroup t V) :
    ∃ e ∈ normIn V T, ⁅x, e⁆ ∈ cfgM T V ∧ ⁅x, e⁆ ∉ L := by
  have hwc := hV.sec3.cfg.wc
  have hLT : L ≤ T := hV.hL ▸ normIn_le T V
  have hcfg : cfgM T V = L ⊔ normIn V T := by rw [cfgM, hV.hL]
  have hLA := hV.inf_eq_bot
  set y := t⁻¹ * x with hy
  have hxT := hX.hxT
  have hyT : y ∈ Subgroup.normalizer (T : Set G) :=
    (Subgroup.normalizer (T : Set G)).mul_mem
      ((Subgroup.normalizer (T : Set G)).inv_mem (Subgroup.le_normalizer ht)) hxT
  have hyV : conjSubgroup y V = V := by
    rw [hy, ← conjSubgroup_conjSubgroup, htV, conjSubgroup_conjSubgroup, inv_mul_cancel,
      conjSubgroup_one]
  have hyA : conjSubgroup y (normIn V T) = normIn V T := by
    have h := normIn_conj y V T
    rw [hyV, mem_normalizer_iff_conjSubgroup_eq.1 hyT] at h
    exact h.symm
  have hact : ∀ r ∈ T, y * r * y⁻¹ * r⁻¹ ∈ L := by
    intro r hr
    have hw : x * r * x⁻¹ ∈ T := conj_mem_of_mem_normalizer hxT hr
    have hcomm := elemAbelian_mul_comm hwc.1 (T.inv_mem ht) hw
    have : y * r * y⁻¹ * r⁻¹ = x * r * x⁻¹ * r⁻¹ := by
      calc y * r * y⁻¹ * r⁻¹ = (t⁻¹ * (x * r * x⁻¹)) * t * r⁻¹ := by rw [hy]; group
        _ = ((x * r * x⁻¹) * t⁻¹) * t * r⁻¹ := by rw [hcomm]
        _ = x * r * x⁻¹ * r⁻¹ := by group
    rw [this]
    exact hX.hxact r hr
  obtain ⟨l₀, hl₀, hl₀x⟩ := hX.hxl
  have hyl₀ : y * l₀ ≠ l₀ * y := by
    intro h
    apply hl₀x
    have hc := elemAbelian_mul_comm hwc.1 (T.inv_mem ht) (hLT hl₀)
    have : t⁻¹ * (x * l₀) = t⁻¹ * (l₀ * x) := by
      calc t⁻¹ * (x * l₀) = y * l₀ := by rw [hy]; group
        _ = l₀ * y := h
        _ = (l₀ * t⁻¹) * x := by rw [hy]; group
        _ = (t⁻¹ * l₀) * x := by rw [← hc]
        _ = t⁻¹ * (l₀ * x) := by group
    exact mul_left_cancel this
  obtain ⟨t₀, ht₀T, ht₀M⟩ := IsConcreteLE.not_le_iff_exists.1 hV.sec3.not_le_cfgM
  obtain ⟨e, he, hee⟩ :=
    hV.sec3.exists_mem_normIn₁_conj_eq ht₀T ht₀M (hV.hL ▸ hl₀ : l₀ ∈ normIn T V)
  have hye : y * e ≠ e * y := by
    intro hye
    set u' := y * t₀ * y⁻¹ * t₀⁻¹ with hu'
    have hu'L : u' ∈ L := hact t₀ ht₀T
    have hyey : y * e * y⁻¹ = e := by rw [hye]; group
    have hyt : y * t₀ * y⁻¹ = u' * t₀ := by rw [hu']; group
    have heu' : e * u' * e⁻¹ = u' := by
      have : u' * e = e * u' := hV.sec3.cfg.comm_L_L₁ (hV.hL ▸ hu'L) he
      rw [← this]; group
    have h1 : y * (e * t₀ * e⁻¹) * y⁻¹ = u' * (t₀ * l₀) := by
      calc y * (e * t₀ * e⁻¹) * y⁻¹ = (y * e * y⁻¹) * (y * t₀ * y⁻¹) * (y * e * y⁻¹)⁻¹ := by group
        _ = e * (u' * t₀) * e⁻¹ := by rw [hyey, hyt]
        _ = (e * u' * e⁻¹) * (e * t₀ * e⁻¹) := by group
        _ = u' * (t₀ * l₀) := by rw [heu', hee]
    have h2 : y * (e * t₀ * e⁻¹) * y⁻¹ = u' * t₀ * (y * l₀ * y⁻¹) := by
      rw [hee]
      calc y * (t₀ * l₀) * y⁻¹ = (y * t₀ * y⁻¹) * (y * l₀ * y⁻¹) := by group
        _ = u' * t₀ * (y * l₀ * y⁻¹) := by rw [hyt]
    have h3 : u' * (t₀ * l₀) = u' * t₀ * (y * l₀ * y⁻¹) := h1.symm.trans h2
    have h4 : l₀ = y * l₀ * y⁻¹ := by
      have : u' * t₀ * l₀ = u' * t₀ * (y * l₀ * y⁻¹) := by rw [mul_assoc]; exact h3
      exact mul_left_cancel this
    apply hyl₀
    calc y * l₀ = (y * l₀ * y⁻¹) * y := by group
      _ = l₀ * y := by rw [← h4]
  set e' := y * e * y⁻¹ with he'
  have he'A : e' ∈ normIn V T := by
    have := conj_mem_conjSubgroup y he
    rwa [hyA] at this
  have hxy : x = t * y := by rw [hy]; group
  have hcomm : ⁅x, e⁆ = ⁅t, e'⁆ * (e' * e⁻¹) := by
    rw [hxy]
    simp only [commutatorElement_def, he']
    group
  have htL : ⁅t, e'⁆ ∈ L := hV.hL ▸ hV.sec3.cfg.comm_mem_normIn ht he'A
  refine ⟨e, he, ?_, ?_⟩
  · rw [hcomm, hcfg]
    exact (L ⊔ normIn V T).mul_mem (Subgroup.mem_sup_left htL)
      (Subgroup.mem_sup_right ((normIn V T).mul_mem he'A ((normIn V T).inv_mem he)))
  · intro hκ
    have h1 : e' * e⁻¹ ∈ L := by
      have : e' * e⁻¹ = (⁅t, e'⁆)⁻¹ * ⁅x, e⁆ := by rw [hcomm]; group
      rw [this]
      exact L.mul_mem (L.inv_mem htL) hκ
    have h2 : e' * e⁻¹ ∈ L ⊓ normIn V T :=
      ⟨h1, (normIn V T).mul_mem he'A ((normIn V T).inv_mem he)⟩
    rw [hLA, Subgroup.mem_bot, mul_inv_eq_one] at h2
    apply hye
    have : y * e * y⁻¹ = e := h2
    calc y * e = (y * e * y⁻¹) * y := by group
      _ = e * y := by rw [this]

end CFSG.CGT.T75R
