module

public import CFSG.CGT.T75R.Tri2
public import CFSG.CGT.T75R.Cases

public section

namespace CFSG.CGT.T75R

open CFSG.Open CFSG.CGT.Timmesfeld75
open scoped commutatorElement

variable {G : Type} [Group G]

theorem exists_mem_not_mem_of_card_two [Finite G] {K L : Subgroup G}
    (hcard : Nat.card K = Nat.card L * 2) : ∃ t ∈ K, t ∉ L := by
  by_contra hcon
  push Not at hcon
  have hle : K ≤ L := hcon
  have h1 : Nat.card K ≤ Nat.card L := Subgroup.card_le_of_le hle
  have : 0 < Nat.card L := Nat.card_pos
  omega

theorem mem_normalizer_sup' {A B : Subgroup G} {t : G} (hA : t ∈ Subgroup.normalizer (A : Set G))
    (hB : t ∈ Subgroup.normalizer (B : Set G)) :
    t ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  apply mem_normalizer_of_conjSubgroup_eq
  rw [conjSubgroup_sup_eq_sup, mem_normalizer_iff_conjSubgroup_eq.1 hA,
    mem_normalizer_iff_conjSubgroup_eq.1 hB]

theorem triA : TriA := by
  intro G _ T T₁ hy hglob hiso hq hT8 V V' hV hV' hVT hV'T hne hLV hLV' hcomm
  have hfin : Finite G := hy.finite
  have hwc : IsWC T := hy.pair.wc
  have hT1 : ∃ u : G, T = conjSubgroup u T := ⟨1, (conjSubgroup_one T).symm⟩
  have hL4 : Nat.card (normIn T T₁) = 4 := by omega
  have hLne : normIn T T₁ ≠ ⊥ := by
    intro h
    rw [h] at hL4
    simp at hL4
  have hSV : Sec3 T V := sec3_of_conj_conj hglob hT1 hV hVT (by rw [hLV]; exact hLne)
  have hSV' : Sec3 T V' := sec3_of_conj_conj hglob hT1 hV' hV'T (by rw [hLV']; exact hLne)
  have hIV : Sec3Iso T V := sec3Iso_of_conj_conj hiso hT1 hV hVT (by rw [hLV]; exact hLne)
  have hIV' : Sec3Iso T V' := sec3Iso_of_conj_conj hiso hT1 hV' hV'T (by rw [hLV']; exact hLne)
  have hVne : V ≠ V' := fun h => hne h.symm
  have hTVne : T ≠ V := fun h => hVT h.symm
  have hTV'ne : T ≠ V' := fun h => hV'T h.symm
  have hAne : normIn V T ≠ ⊥ := hSV.cfg.ne₁
  have hBne : normIn V' T ≠ ⊥ := hSV'.cfg.ne₁
  have hAcard : Nat.card (normIn V T) = 4 := by
    rw [hSV.card_normIn_swap, hLV, hL4]
  have hBcard : Nat.card (normIn V' T) = 4 := by
    rw [hSV'.card_normIn_swap, hLV', hL4]
  have hVc : Nat.card V = 8 := by
    obtain ⟨v, hv⟩ := hV
    rw [hv, card_conjSubgroup, hT8]
  have hV'c : Nat.card V' = 8 := by
    obtain ⟨v, hv⟩ := hV'
    rw [hv, card_conjSubgroup, hT8]
  have hwcV : IsWC V := hSV.cfg.wc₁
  have hwcV' : IsWC V' := hSV'.cfg.wc₁
  obtain ⟨⟨y, hyA⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hAne
  have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
  obtain ⟨⟨z, hzB⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hBne
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hBle : normIn V' T ≤ normIn V' V := fun b hb => mem_normIn.2 ⟨normIn_le _ _ hb,
    hwcV.centralizer_le_normalizer (normIn_le _ _ hyA) hy1'
      (Subgroup.mem_centralizer_iff.2 fun h hh => by
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        exact hcomm y hyA b hb)⟩
  have hAle : normIn V T ≤ normIn V V' := fun a ha => mem_normIn.2 ⟨normIn_le _ _ ha,
    hwcV'.centralizer_le_normalizer (normIn_le _ _ hzB) hz1'
      (Subgroup.mem_centralizer_iff.2 fun h hh => by
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        exact (hcomm a ha z hzB).symm)⟩
  have hBeq : normIn V' T = normIn V' V :=
    Subgroup.eq_of_le_of_card_ge hBle (by
      have := hy.pair.card_normIn_le hV' hV hVne
      omega)
  have hAeq : normIn V T = normIn V V' :=
    Subgroup.eq_of_le_of_card_ge hAle (by
      have := hy.pair.card_normIn_le hV hV' hne
      omega)
  have hSV'V : Sec3 V' V := sec3_of_conj_conj hglob hV' hV hVne (by rw [← hBeq]; exact hBne)
  have hIV'V : Sec3Iso V' V := sec3Iso_of_conj_conj hiso hV' hV hVne (by rw [← hBeq]; exact hBne)
  have hSVV' : Sec3 V V' := sec3_of_conj_conj hglob hV hV' hne (by rw [← hAeq]; exact hAne)
  have hIVV' : Sec3Iso V V' := sec3Iso_of_conj_conj hiso hV hV' hne (by rw [← hAeq]; exact hAne)
  have hSVT : Sec3 V T := sec3_of_conj_conj hglob hV hT1 hTVne hAne
  have hIVT : Sec3Iso V T := sec3Iso_of_conj_conj hiso hV hT1 hTVne hAne
  obtain ⟨t₀, ht₀V', ht₀B⟩ := exists_mem_not_mem_of_card_two
    (K := V') (L := normIn V' T) (by rw [hV'c, hBcard])
  obtain ⟨t₁, ht₁V, ht₁A⟩ := exists_mem_not_mem_of_card_two
    (K := V) (L := normIn V T) (by rw [hVc, hAcard])
  obtain ⟨t₂, ht₂T, ht₂L⟩ := exists_mem_not_mem_of_card_two
    (K := T) (L := normIn T T₁) (by rw [hT8, hL4])
  have hAel : IsElemAbelian 2 (normIn V T) := isElemAbelian_of_le hwcV.1 (normIn_le V T)
  have hBel : IsElemAbelian 2 (normIn V' T) := isElemAbelian_of_le hwcV'.1 (normIn_le V' T)
  have hLel : IsElemAbelian 2 (normIn T T₁) := isElemAbelian_of_le hwc.1 (normIn_le T T₁)
  have hBA : ∀ x ∈ normIn V' T, ∀ y ∈ normIn V T, x * y = y * x := fun x hx y hy =>
    (hcomm y hy x hx).symm
  have hLA : ∀ x ∈ normIn T T₁, ∀ y ∈ normIn V T, x * y = y * x := fun x hx y hy =>
    hSV.cfg.comm_L_L₁ (by rw [hLV]; exact hx) hy
  have hLB : ∀ x ∈ normIn T T₁, ∀ y ∈ normIn V' T, x * y = y * x := fun x hx y hy =>
    hSV'.cfg.comm_L_L₁ (by rw [hLV']; exact hx) hy
  have hBAel : IsElemAbelian 2 (normIn V' T ⊔ normIn V T) := isElemAbelian_sup_of_comm hBel hAel hBA
  have hNel : IsElemAbelian 2 (normIn V' T ⊔ normIn V T ⊔ normIn T T₁) := by
    refine isElemAbelian_sup_of_comm hBAel hLel fun x hx y hy => ?_
    obtain ⟨b, hb, a, ha, rfl⟩ := (mem_sup_iff_of_comm hBA).1 hx
    calc b * a * y = b * (a * y) := by rw [mul_assoc]
      _ = b * (y * a) := by rw [(hLA y hy a ha).symm]
      _ = (b * y) * a := by rw [mul_assoc]
      _ = (y * b) * a := by rw [(hLB y hy b hb).symm]
      _ = y * (b * a) := by rw [mul_assoc]
  have hcfg₀₁ : cfgM V' V = normIn V' T ⊔ normIn V T := by rw [cfgM, ← hBeq, ← hAeq]
  have hcfg₀₂ : cfgM V' T = normIn V' T ⊔ normIn T T₁ := by rw [cfgM, hLV']
  have hcfg₁₀ : cfgM V V' = normIn V T ⊔ normIn V' T := by rw [cfgM, ← hBeq, ← hAeq]
  have hcfg₁₂ : cfgM V T = normIn V T ⊔ normIn T T₁ := by rw [cfgM, hLV]
  have hcfg₂₁ : cfgM T V = normIn T T₁ ⊔ normIn V T := by rw [cfgM, hLV]
  have hcfg₂₀ : cfgM T V' = normIn T T₁ ⊔ normIn V' T := by rw [cfgM, hLV']
  have htN₀ : t₀ ∈ Subgroup.normalizer
      ((normIn V' T ⊔ normIn V T ⊔ normIn T T₁ : Subgroup G) : Set G) := by
    have h := mem_normalizer_sup' (hSV'V.cfg.le_normalizer_cfgM (Subgroup.mem_sup_left ht₀V'))
      (hSV'.cfg.symm.le_normalizer_cfgM (Subgroup.mem_sup_left ht₀V'))
    rw [hcfg₀₁, hcfg₀₂] at h
    have e : normIn V' T ⊔ normIn V T ⊔ normIn T T₁ =
        (normIn V' T ⊔ normIn V T) ⊔ (normIn V' T ⊔ normIn T T₁) := by
      generalize normIn V' T = B
      generalize normIn V T = A
      generalize normIn T T₁ = L
      simp [sup_comm, sup_left_comm]
    rw [e]
    exact h
  have htN₁ : t₁ ∈ Subgroup.normalizer
      ((normIn V' T ⊔ normIn V T ⊔ normIn T T₁ : Subgroup G) : Set G) := by
    have h := mem_normalizer_sup' (hSVV'.cfg.le_normalizer_cfgM (Subgroup.mem_sup_left ht₁V))
      (hSVT.cfg.le_normalizer_cfgM (Subgroup.mem_sup_left ht₁V))
    rw [hcfg₁₀, hcfg₁₂] at h
    have e : normIn V' T ⊔ normIn V T ⊔ normIn T T₁ =
        (normIn V T ⊔ normIn V' T) ⊔ (normIn V T ⊔ normIn T T₁) := by
      generalize normIn V' T = B
      generalize normIn V T = A
      generalize normIn T T₁ = L
      simp [sup_comm, sup_left_comm]
    rw [e]
    exact h
  have htN₂ : t₂ ∈ Subgroup.normalizer
      ((normIn V' T ⊔ normIn V T ⊔ normIn T T₁ : Subgroup G) : Set G) := by
    have h := mem_normalizer_sup' (hSV.cfg.le_normalizer_cfgM (Subgroup.mem_sup_left ht₂T))
      (hSV'.cfg.le_normalizer_cfgM (Subgroup.mem_sup_left ht₂T))
    rw [hcfg₂₁, hcfg₂₀] at h
    have e : normIn V' T ⊔ normIn V T ⊔ normIn T T₁ =
        (normIn T T₁ ⊔ normIn V T) ⊔ (normIn T T₁ ⊔ normIn V' T) := by
      generalize normIn V' T = B
      generalize normIn V T = A
      generalize normIn T T₁ = L
      simp [sup_comm, sup_left_comm]
    rw [e]
    exact h
  by_cases hdir : normIn V' T ⊓ cfgM T V = ⊥
  · exact Or.inl hdir
  right
  obtain ⟨⟨c, hcmem⟩, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hdir
  have hc1' : c ≠ 1 := fun h => hc1 (Subtype.ext h)
  obtain ⟨l, hl, e, he, hce⟩ := (hSV.cfg.mem_cfgM_iff).1 hcmem.2
  have hlL : l ∈ normIn T T₁ := by rw [← hLV]; exact hl
  have he1 : e ≠ 1 := by
    intro h1
    apply hc1'
    have hcl : c = l := by rw [hce, h1, mul_one]
    have hlT : l ∈ T := normIn_le _ _ hl
    have hcV' : c ∈ V' := normIn_le _ _ hcmem.1
    have h2 : c ∈ T ⊓ V' := ⟨hcl ▸ hlT, hcV'⟩
    rw [inf_eq_bot_of_conj_ne hwc hT1 hV' hV'T, Subgroup.mem_bot] at h2
    exact h2
  have hprod : c * e⁻¹ * l⁻¹ = 1 := by rw [hce]; group
  have hT₁ : ∃ w : G, V = conjSubgroup w V' := by
    obtain ⟨v, hv⟩ := hV
    obtain ⟨v', hv'⟩ := hV'
    refine ⟨v * v'⁻¹, ?_⟩
    rw [hv, hv', conjSubgroup_conjSubgroup]
    congr 1
    group
  have hCV'V : Cfg V' V := cfg_of_conj_conj hwc hV' hV hVne (by rw [← hBeq]; exact hBne)
  have hconj : conjSubgroup t₂ V = V' :=
    tri_conj_eq (T₀ := V') (T₁ := V) (T₂ := T) (L₀ := normIn V' T) (L₁ := normIn V T)
      (L₂ := normIn T T₁) (N := normIn V' T ⊔ normIn V T ⊔ normIn T T₁) hT₁ hCV'V hSV'.cfg.symm
      hSV.cfg.symm hBeq.symm hAeq.symm rfl hLV' rfl hLV (by rw [hVc, hAcard]) ht₀V' ht₀B ht₁V
      ht₁A ht₂T hNel (le_sup_left.trans le_sup_left) (le_sup_right.trans le_sup_left) le_sup_right
      htN₀ htN₁ htN₂
      (fun e he => s3_relation hSV'V hIV'V (by rw [hVc, ← hAeq, hAcard]) ht₀V'
        (by rw [← hBeq]; exact ht₀B) ht₁V (by rw [← hAeq]; exact ht₁A) (by rw [← hBeq]; exact he))
      (fun e he => s3_relation hSVV' hIVV' (by rw [hV'c, ← hBeq, hBcard]) ht₁V
        (by rw [← hAeq]; exact ht₁A) ht₀V' (by rw [← hBeq]; exact ht₀B) (by rw [← hAeq]; exact he))
      (fun e he => s3_relation hSV' hIV' (by rw [hV'c, hBcard]) ht₂T
        (by rw [hLV']; exact ht₂L) ht₀V' ht₀B (by rw [hLV']; exact he))
      (fun e he => s3_relation hSVT hIVT (by rw [hT8, hLV, hL4]) ht₁V ht₁A ht₂T
        (by rw [hLV]; exact ht₂L) he)
      hcmem.1 ((normIn V T).inv_mem he) ((normIn T T₁).inv_mem hlL)
      (fun h => he1 (inv_eq_one.1 h)) hprod
  exact ⟨t₂, ht₂T, ht₂L, hconj.symm⟩

end CFSG.CGT.T75R
