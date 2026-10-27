module

public import CFSG.Quasithin.EmptyFaithful.S1421QA17Surv10
public import CFSG.GH74.QTGen4.DSGen4.OpenLeaves

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement Pointwise

private theorem m5_centralizer_three :
    ∀ g h : alternatingGroup (Fin 5), (g ^ 3 = 1 ∧ g ≠ 1 ∧ g * h = h * g) → h ^ 3 = 1 := by
  decide +kernel

private theorem m5_card_A5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup]
  simp [Nat.factorial]

private def m5a : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩

private def m5b : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 2 * Equiv.swap 1 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩

private def m5c : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩

private theorem m5c_pow : m5c ^ 3 = 1 := by decide +kernel

private theorem m5c_ne : m5c ≠ 1 := by decide +kernel

private def m5V0 : Subgroup (alternatingGroup (Fin 5)) where
  carrier := {x | x = 1 ∨ x = m5a ∨ x = m5b ∨ x = m5a * m5b}
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;> decide +kernel
  one_mem' := Or.inl rfl
  inv_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel

private theorem m5V0_mem (x : alternatingGroup (Fin 5)) :
    x ∈ m5V0 ↔ (x = 1 ∨ x = m5a ∨ x = m5b ∨ x = m5a * m5b) := Iff.rfl

private theorem m5V0_card : Nat.card m5V0 = 4 := by
  have hset : (m5V0 : Set (alternatingGroup (Fin 5))) =
      ↑({1, m5a, m5b, m5a * m5b} : Finset (alternatingGroup (Fin 5))) := by
    ext x
    simp [m5V0_mem]
  have h4 : ({1, m5a, m5b, m5a * m5b} : Finset (alternatingGroup (Fin 5))).card = 4 := by
    decide +kernel
  show Nat.card (m5V0 : Set (alternatingGroup (Fin 5))) = 4
  rw [Nat.card_coe_set_eq, hset, Set.ncard_coe_finset, h4]

private theorem m5c_normalizes : ∀ v ∈ m5V0, m5c * v * m5c⁻¹ ∈ m5V0 := by
  intro v hv
  rw [m5V0_mem] at hv ⊢
  rcases hv with rfl | rfl | rfl | rfl <;> decide +kernel

private theorem m5_index_odd (W : Subgroup (alternatingGroup (Fin 5)))
    (hW : Nat.card W = 4) : ¬ 2 ∣ W.index := by
  have h := Subgroup.card_mul_index W
  rw [hW, m5_card_A5] at h
  omega

private def m5_sylow (W : Subgroup (alternatingGroup (Fin 5))) (hW : Nat.card W = 4) :
    Sylow 2 (alternatingGroup (Fin 5)) :=
  (IsPGroup.of_card (n := 2) (by rw [hW]; norm_num)).toSylow (m5_index_odd W hW)

private theorem m5_sylow_coe (W : Subgroup (alternatingGroup (Fin 5))) (hW : Nat.card W = 4) :
    (m5_sylow W hW : Subgroup (alternatingGroup (Fin 5))) = W :=
  IsPGroup.toSylow_coe _ _

private theorem m5_exists_three_normalizer (V : Subgroup (alternatingGroup (Fin 5)))
    (hV : Nat.card V = 4) :
    ∃ g : alternatingGroup (Fin 5), g ^ 3 = 1 ∧ g ≠ 1 ∧ ∀ v ∈ V, g * v * g⁻¹ ∈ V := by
  have hV0 : Nat.card m5V0 = 4 := m5V0_card
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 5))
    (m5_sylow m5V0 hV0) (m5_sylow V hV)
  have hcoe : MulAut.conj c • m5V0 = V := by
    have h := congrArg
      (fun P : Sylow 2 (alternatingGroup (Fin 5)) => (P : Subgroup (alternatingGroup (Fin 5)))) hc
    simpa only [Sylow.coe_subgroup_smul, m5_sylow_coe m5V0 hV0, m5_sylow_coe V hV] using h
  have hcV : ∀ v, v ∈ V ↔ c⁻¹ * v * c ∈ m5V0 := by
    intro v
    rw [← hcoe, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.smul_def, MulAut.conj_inv_apply]
  refine ⟨c * m5c * c⁻¹, ?_, ?_, ?_⟩
  · rw [conj_pow, m5c_pow]
    simp
  · intro h
    apply m5c_ne
    have e1 : m5c = c⁻¹ * (c * m5c * c⁻¹) * c := by group
    rw [e1, h]
    group
  · intro v hv
    have hv' := (hcV v).mp hv
    rw [hcV]
    convert m5c_normalizes _ hv' using 1
    group


private theorem m5_eq_one_of_pow {M : Type*} [Group M] {x : M} {k : ℕ}
    (h3 : x ^ 3 = 1) (hk : x ^ (2 ^ k) = 1) : x = 1 := by
  have h1 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have h2 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have h4 : orderOf x ∣ 1 := by
    have := Nat.dvd_gcd h1 h2
    rwa [hcop.gcd_eq_one] at this
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h4)

private theorem m5_isPGroup_of_pow {M : Type*} [Group M] (H : Subgroup M)
    (h : ∀ x ∈ H, ∃ k : ℕ, x ^ (2 ^ k) = 1) : IsPGroup 2 H := by
  intro x
  obtain ⟨k, hk⟩ := h x.1 x.2
  exact ⟨k, Subtype.ext (by simpa using hk)⟩

private theorem m5_inv_normalizes {g : alternatingGroup (Fin 5)} (hg3 : g ^ 3 = 1)
    {V : Subgroup (alternatingGroup (Fin 5))} (hV : ∀ v ∈ V, g * v * g⁻¹ ∈ V) :
    ∀ v ∈ V, g⁻¹ * v * g ∈ V := by
  intro v hv
  have h2 : g * g ^ 2 = 1 := by
    rw [← pow_succ']
    exact hg3
  have h2' : g ^ 2 = g⁻¹ := eq_inv_of_mul_eq_one_right h2
  have e : g⁻¹ * v * g = g * (g * v * g⁻¹) * g⁻¹ := by
    calc g⁻¹ * v * g = g ^ 2 * v * (g ^ 2)⁻¹ := by rw [h2', inv_inv]
      _ = g * (g * v * g⁻¹) * g⁻¹ := by simp only [pow_two, mul_inv_rev, mul_assoc]
  rw [e]
  exact hV _ (hV v hv)

private theorem m5_fixed_or_full {V W : Subgroup (alternatingGroup (Fin 5))}
    (hV : Nat.card V = 4) (hWV : W ≤ V) {g : alternatingGroup (Fin 5)}
    (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) (hgW : ∀ x ∈ W, g * x * g⁻¹ ∈ W) :
    W = ⊥ ∨ W = V := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hWbot, hWV'⟩ := hcon
  obtain ⟨w, hwW, hw1⟩ : ∃ w ∈ W, w ≠ 1 := by
    by_contra h
    refine hWbot (eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr ?_)
    by_contra hx1
    exact h ⟨x, hx, hx1⟩
  have hg3' : g * (g * g) = 1 := by simpa [pow_succ, mul_assoc] using hg3
  have hσ3 : ∀ x : alternatingGroup (Fin 5), g * (g * (g * x * g⁻¹) * g⁻¹) * g⁻¹ = x := by
    intro x
    calc g * (g * (g * x * g⁻¹) * g⁻¹) * g⁻¹ = (g * (g * g)) * x * (g * (g * g))⁻¹ := by group
      _ = x := by rw [hg3']; simp
  have hσinj : ∀ x y : alternatingGroup (Fin 5), g * x * g⁻¹ = g * y * g⁻¹ → x = y := by
    intro x y h
    have := congrArg (fun z => g⁻¹ * z * g) h
    simpa [mul_assoc] using this
  have hσ1 : ∀ x : alternatingGroup (Fin 5), g * x * g⁻¹ = 1 → x = 1 := by
    intro x h
    apply hσinj x 1
    rw [h]
    group
  have hwV : w ∈ V := hWV hwW
  set w₁ := g * w * g⁻¹ with hw₁def
  set w₂ := g * w₁ * g⁻¹ with hw₂def
  have hw₁W : w₁ ∈ W := hgW w hwW
  have hw₂W : w₂ ∈ W := hgW w₁ hw₁W
  by_cases hfix : w₁ = w
  ·
    have hcomm : g * w = w * g := by
      calc g * w = g * w * g⁻¹ * g := by group
        _ = w * g := by rw [← hw₁def, hfix]
    have hw3 : w ^ 3 = 1 := m5_centralizer_three g w ⟨hg3, hg1, hcomm⟩
    have hw4 : w ^ 4 = 1 := by
      have h := Subgroup.orderOf_dvd_natCard V hwV
      rw [hV] at h
      exact orderOf_dvd_iff_pow_eq_one.mp h
    apply hw1
    calc w = w ^ 4 := by
          rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, hw3, one_mul]
      _ = 1 := hw4
  ·
    have hw₁1 : w₁ ≠ 1 := fun h => hw1 (hσ1 w h)
    have hw₂1 : w₂ ≠ 1 := fun h => hw₁1 (hσ1 w₁ h)
    have hww₂ : w ≠ w₂ := by
      intro h
      apply hfix
      have h1 : g * w₂ * g⁻¹ = w := hσ3 w
      rw [← h] at h1
      exact h1
    have hw₁w₂ : w₁ ≠ w₂ := by
      intro h
      apply hfix
      apply hσinj w₁ w
      exact h.symm
    have hfour : 4 ≤ Nat.card W := by
      let f : Fin 4 → W := fun i =>
        ⟨![1, w, w₁, w₂] i, by fin_cases i <;> simp [hwW, hw₁W, hw₂W]⟩
      have hf : Function.Injective f := by
        intro i j hij
        have hij' := congrArg Subtype.val hij
        fin_cases i <;> fin_cases j <;> first
          | rfl
          | simp [f, Ne.symm hw1, Ne.symm hw₁1, Ne.symm hw₂1, Ne.symm hfix, Ne.symm hww₂,
              Ne.symm hw₁w₂, hw1, hw₁1, hw₂1, hfix, hww₂, hw₁w₂] at hij'
      have := Nat.card_le_card_of_injective f hf
      simpa using this
    have hdvd : Nat.card W ∣ Nat.card V := Subgroup.card_dvd_of_le hWV
    rw [hV] at hdvd
    have hle : Nat.card W ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    exact hWV' (Subgroup.eq_of_le_of_card_ge hWV (by omega))


theorem leafM5 : LeafM5 := by
  intro G _ _ L T hq hT
  obtain ⟨φ⟩ := CFSG.Quasithin.S1421QA17.nonempty_mulEquiv_alt5_of_isL2Quot_two hq
  let ρ : ↥L →* alternatingGroup (Fin 5) := φ.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 ↥L))
  have hρsurj : Function.Surjective ρ := by
    intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (pCore 2 ↥L) (φ.symm y)
    exact ⟨x, by show φ (QuotientGroup.mk' (pCore 2 ↥L) x) = y; rw [hx, MulEquiv.apply_symm_apply]⟩
  have hρker : ∀ x : ↥L, ρ x = 1 ↔ x ∈ pCore 2 ↥L := by
    intro x
    simp [ρ, QuotientGroup.eq_one_iff]
  have hO : ∀ z : ↥L, (z : G) ∈ pCoreOf 2 L ↔ ρ z = 1 := by
    intro z
    rw [hρker, CFSG.Quasithin.F1.mem_pCore_iff_coe]
  have hTL : T ≤ L := hT.1
  have hOT : pCoreOf 2 L ≤ T := CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le hT
  set T₁ : Subgroup ↥L := T.subgroupOf L with hT₁def
  have hT₁mem : ∀ y : ↥L, y ∈ T₁ ↔ (y : G) ∈ T := fun y => Subgroup.mem_subgroupOf
  set V : Subgroup (alternatingGroup (Fin 5)) := T₁.map ρ with hVdef
  have hker_le : ρ.ker ≤ T₁ := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    exact (hT₁mem x).mpr (hOT ((hO x).mpr hx))
  have hcomap : V.comap ρ = T₁ := by
    rw [hVdef, Subgroup.comap_map_eq, sup_eq_left.mpr hker_le]
  have hVmem : ∀ y : ↥L, ρ y ∈ V ↔ y ∈ T₁ := fun y => by
    rw [← Subgroup.mem_comap, hcomap]
  have hT2 : ∀ y : ↥L, (y : G) ∈ T → ∃ k : ℕ, y ^ (2 ^ k) = 1 := by
    intro y hy
    obtain ⟨k, hk⟩ := hT.2.1 ⟨(y : G), hy⟩
    refine ⟨k, Subtype.ext ?_⟩
    simpa using congrArg Subtype.val hk
  have hVpow : ∀ v ∈ V, ∃ k : ℕ, v ^ (2 ^ k) = 1 := by
    intro v hv
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hv
    obtain ⟨k, hk⟩ := hT2 y ((hT₁mem y).mp hy)
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  have hVcard : Nat.card V = 4 := by
    have hpg : IsPGroup 2 V := m5_isPGroup_of_pow V hVpow
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hpg
    have hidx : V.index = (T.subgroupOf L).index := Subgroup.index_map_eq T₁ hρsurj hker_le
    have hodd : ¬ 2 ∣ V.index := by
      rw [hidx]
      exact hT.2.2
    have hprod : Nat.card V * V.index = 60 := by
      rw [Subgroup.card_mul_index, m5_card_A5]
    rw [hn] at hprod
    have hdvd : 2 ^ n ∣ 60 := Dvd.intro _ hprod
    have hn6 : n < 6 := by
      by_contra hc
      have h1 : 2 ^ 6 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : 2 ^ n ≤ 60 := Nat.le_of_dvd (by norm_num) hdvd
      norm_num at h1
      omega
    interval_cases n <;> norm_num at hn hprod hodd ⊢ <;> omega
  obtain ⟨g₀, hg₀3, hg₀1, hg₀V⟩ := m5_exists_three_normalizer V hVcard
  have hg₀conj : ∀ v, v ∈ V ↔ g₀ * v * g₀⁻¹ ∈ V := by
    intro v
    refine ⟨hg₀V v, fun h => ?_⟩
    have := m5_inv_normalizes hg₀3 hg₀V _ h
    simpa [mul_assoc] using this
  obtain ⟨d₁, hd₁⟩ := hρsurj g₀
  have hd₁T : ∀ y : ↥L, y ∈ T₁ ↔ d₁ * y * d₁⁻¹ ∈ T₁ := by
    intro y
    rw [← hVmem, ← hVmem, map_mul, map_mul, map_inv, hd₁]
    exact hg₀conj (ρ y)
  have hdL : (d₁ : G) ∈ L := d₁.2
  have hdN : (d₁ : G) ∈ Subgroup.normalizer (T : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    by_cases hhL : h ∈ L
    · have := hd₁T ⟨h, hhL⟩
      simpa [hT₁mem] using this
    · have hTn : h ∉ T := fun hh => hhL (hTL hh)
      have hdh : (d₁ : G) * h * (d₁ : G)⁻¹ ∉ T := fun hh => hhL (by
        have := L.mul_mem (L.mul_mem (L.inv_mem hdL) (hTL hh)) hdL
        simpa [mul_assoc] using this)
      exact ⟨fun hh => absurd hh hTn, fun hh => absurd hh hdh⟩
  refine ⟨?_, ?_⟩
  ·
    intro X hOX hXT hN
    have hXL : X ≤ L := hXT.trans hTL
    set X₁ : Subgroup ↥L := X.subgroupOf L with hX₁def
    have hX₁mem : ∀ y : ↥L, y ∈ X₁ ↔ (y : G) ∈ X := fun y => Subgroup.mem_subgroupOf
    set W : Subgroup (alternatingGroup (Fin 5)) := X₁.map ρ with hWdef
    have hWV : W ≤ V := by
      apply Subgroup.map_mono
      intro y hy
      exact (hT₁mem y).mpr (hXT ((hX₁mem y).mp hy))
    have hdX : (d₁ : G) ∈ Subgroup.normalizer (X : Set G) := hN ⟨hdL, hdN⟩
    have hgW : ∀ x ∈ W, g₀ * x * g₀⁻¹ ∈ W := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      have hconj : g₀ * ρ y * g₀⁻¹ = ρ (d₁ * y * d₁⁻¹) := by
        rw [map_mul, map_mul, map_inv, hd₁]
      rw [hconj]
      apply Subgroup.mem_map_of_mem
      rw [hX₁mem]
      have hyX : (y : G) ∈ X := (hX₁mem y).mp hy
      have := (Subgroup.mem_normalizer_iff.mp hdX (y : G)).mp hyX
      simpa using this
    rcases m5_fixed_or_full hVcard hWV hg₀3 hg₀1 hgW with hWbot | hWtop
    · left
      apply le_antisymm
      · intro x hx
        have hxL : x ∈ L := hXL hx
        have hmem : ρ ⟨x, hxL⟩ ∈ W := Subgroup.mem_map_of_mem ρ ((hX₁mem ⟨x, hxL⟩).mpr hx)
        rw [hWbot, Subgroup.mem_bot] at hmem
        exact (hO ⟨x, hxL⟩).mpr hmem
      · exact hOX
    · right
      apply le_antisymm hXT
      intro t ht
      have htL : t ∈ L := hTL ht
      have htW : ρ ⟨t, htL⟩ ∈ W := by
        rw [hWtop]
        exact (hVmem _).mpr ((hT₁mem _).mpr ht)
      obtain ⟨y, hy, hyt⟩ := Subgroup.mem_map.mp htW
      have hk : ρ ((⟨t, htL⟩ : ↥L)⁻¹ * y) = 1 := by
        rw [map_mul, map_inv, hyt, inv_mul_cancel]
      have hkX : (((⟨t, htL⟩ : ↥L)⁻¹ * y : ↥L) : G) ∈ X := hOX ((hO _).mpr hk)
      have hyX : (y : G) ∈ X := (hX₁mem y).mp hy
      have hteq : t = (y : G) * (((⟨t, htL⟩ : ↥L)⁻¹ * y : ↥L) : G)⁻¹ := by
        simp
      rw [hteq]
      exact X.mul_mem hyX (X.inv_mem hkX)
  ·
    intro d hdN3 hd3
    have hdL' : d ∈ L := hdN3.1
    have hd3' : d ^ 3 = 1 := by
      rw [← hd3]
      exact pow_orderOf_eq_one d
    have hdne : d ≠ 1 := by
      rintro rfl
      simp at hd3
    intro e he hcomm
    have heL : e ∈ L := hTL he
    have hd₁' : ∃ d' : ↥L, (d' : G) = d := ⟨⟨d, hdL'⟩, rfl⟩
    obtain ⟨δ, rfl⟩ := hd₁'
    obtain ⟨ε, rfl⟩ : ∃ ε : ↥L, (ε : G) = e := ⟨⟨e, heL⟩, rfl⟩
    have hδ3 : δ ^ 3 = 1 := Subtype.ext (by simpa using hd3')
    have hδne : ρ δ ≠ 1 := by
      intro h1
      have hpc : IsPGroup 2 (pCore 2 ↥L) := CFSG.pCore_isPGroup
      obtain ⟨k, hk⟩ := hpc ⟨δ, (hρker δ).mp h1⟩
      have hk' : δ ^ (2 ^ k) = 1 := by
        have := congrArg Subtype.val hk
        simpa using this
      exact hdne (congrArg Subtype.val (m5_eq_one_of_pow hδ3 hk'))
    have hcomm' : ((⁅ε, δ⁆ : ↥L) : G) ∈ pCoreOf 2 L := by
      simpa [commutatorElement_def] using hcomm
    have h2 : ρ ⁅ε, δ⁆ = 1 := (hO _).mp hcomm'
    have h3 : ⁅ρ ε, ρ δ⁆ = 1 := by
      rw [← map_commutatorElement]
      exact h2
    have hcomm2 : ρ ε * ρ δ = ρ δ * ρ ε := commutatorElement_eq_one_iff_mul_comm.mp h3
    have hρδ3 : ρ δ ^ 3 = 1 := by
      rw [← map_pow, hδ3, map_one]
    have hρε3 : ρ ε ^ 3 = 1 := m5_centralizer_three (ρ δ) (ρ ε) ⟨hρδ3, hδne, hcomm2.symm⟩
    obtain ⟨k, hk⟩ := hT2 ε he
    have hρεk : ρ ε ^ (2 ^ k) = 1 := by
      rw [← map_pow, hk, map_one]
    have hρε : ρ ε = 1 := m5_eq_one_of_pow hρε3 hρεk
    exact (hO ε).mpr hρε

end CFSG.GH74.QTGen4.DSGen4
