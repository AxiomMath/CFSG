module

public import CFSG.CGT.Timmesfeld75.Sec3TwelveRho

public section

namespace CFSG.CGT.Timmesfeld75

open scoped MatrixGroups
open CFSG.Open

section Case1

variable {G : Type} [Group G] [Finite G] {T T₁ X M : Subgroup G} [hN : (M.subgroupOf X).Normal]
  {F : Type} [Field F] [Finite F] [CharP F 2] {a : G}

theorem Data312.false_of_trivial (D : Data312 T T₁ X M F a) {T₂ : Subgroup G} (hS₂ : Sec3 T T₂)
    [hN₂ : ((cfgM T T₂).subgroupOf (T ⊔ T₂)).Normal] (haT₂ : a ∈ T₂) (ha1 : a ≠ 1) {b : G}
    (hbL₁ : b ∈ normIn T₁ T) (hb1 : b ≠ 1) {f' : ℕ} (hf' : 0 < f')
    (hpair₂ : IsL2Pair (↥(T ⊔ T₂) ⧸ (cfgM T T₂).subgroupOf (T ⊔ T₂))
      ((T.subgroupOf (T ⊔ T₂)).map (QuotientGroup.mk' ((cfgM T T₂).subgroupOf (T ⊔ T₂))))
      (2 ^ f'))
    (hc : Nat.card ↥(T ⊓ Subgroup.centralizer ({a} : Set G)) = 2 ^ f')
    (hid : ∀ y ∈ T ⊔ T₂, y⁻¹ * (b * y * b⁻¹) ∈ cfgM T T₂) : False := by
  have hS := D.sec3
  have haTn : a ∈ normIn T₂ T := mem_normIn.2 ⟨haT₂, mem_normalizer_iff_conjSubgroup_eq.2 D.aT⟩
  have hTCa : T ⊓ Subgroup.centralizer ({a} : Set G) = normIn T T₂ :=
    hS₂.cfg.inf_centralizer_eq_normIn haTn ha1
  have hTCb : T ⊓ Subgroup.centralizer ({b} : Set G) = normIn T T₁ :=
    hS.cfg.inf_centralizer_eq_normIn hbL₁ hb1
  have hP := D.card_centralizer_sq.1
  have hL1 : 1 < Nat.card (normIn T T₁) :=
    (Subgroup.one_lt_card_iff_ne_bot (H := normIn T T₁)).2 hS.cfg.ne
  have hPpos : 0 < Nat.card ↥(normIn T T₁ ⊓ Subgroup.centralizer ({a} : Set G)) := Nat.card_pos
  have hP1 : 1 < Nat.card ↥(normIn T T₁ ⊓ Subgroup.centralizer ({a} : Set G)) := by
    by_contra h
    have h1 : Nat.card ↥(normIn T T₁ ⊓ Subgroup.centralizer ({a} : Set G)) = 1 := by omega
    rw [h1, one_pow] at hP
    omega
  obtain ⟨⟨p, hp⟩, hp1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.1
      ((Subgroup.one_lt_card_iff_ne_bot (H := normIn T T₁ ⊓ Subgroup.centralizer ({a} : Set G))).1
        hP1)
  have hp1' : p ≠ 1 := fun h => hp1 (Subtype.ext h)
  have hpN : p ∈ cfgM T T₂ ⊓ Subgroup.centralizer ({b} : Set G) := by
    refine ⟨?_, Subgroup.mem_centralizer_singleton_iff.2 (hS.cfg.comm_L_L₁ hp.1 hbL₁)⟩
    have h : p ∈ T ⊓ Subgroup.centralizer ({a} : Set G) := ⟨normIn_le _ _ hp.1, hp.2⟩
    rw [hTCa] at h
    exact Cfg.normIn_le_cfgM_left T T₂ h
  have hne : cfgM T T₂ ⊓ Subgroup.centralizer ({b} : Set G) ≠ ⊥ := fun h => by
    rw [h, Subgroup.mem_bot] at hpN
    exact hp1' hpN
  have hnorm : ∀ x ∈ T ⊔ T₂, ∀ n ∈ cfgM T T₂ ⊓ Subgroup.centralizer ({b} : Set G),
      x * n * x⁻¹ ∈ cfgM T T₂ ⊓ Subgroup.centralizer ({b} : Set G) := fun x hx n hn =>
    inf_centralizer_conj_mem hS₂.cfg.isElemAbelian_cfgM
      (fun y hy m hm => hS₂.cfg.conj_mem_cfgM hy hm) hid hx hn
  have hle : 2 ^ (2 * f') ≤ Nat.card ↥(cfgM T T₂ ⊓ Subgroup.centralizer ({b} : Set G)) :=
    Sec3.two_pow_le_card_of_normal hS₂ rfl rfl hf' hpair₂ inf_le_left hnorm hne
  have hNcard : Nat.card (cfgM T T₂) = 2 ^ (2 * f') := by
    rw [hS₂.card_cfgM_eq_sq, ← hTCa, hc, ← pow_mul, mul_comm]
  have heq : cfgM T T₂ ⊓ Subgroup.centralizer ({b} : Set G) = cfgM T T₂ :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hNcard]; exact hle)
  have hNb : cfgM T T₂ ≤ Subgroup.centralizer ({b} : Set G) := fun x hx => by
    have h : x ∈ cfgM T T₂ ⊓ Subgroup.centralizer ({b} : Set G) := by rw [heq]; exact hx
    exact h.2
  obtain ⟨x, hxT, hxa, hxM⟩ := D.exists_centralizer_not_mem_M
  have hxC : x ∈ T ⊓ Subgroup.centralizer ({a} : Set G) :=
    ⟨hxT, Subgroup.mem_centralizer_singleton_iff.2 (by
      calc x * a = (a * x * a⁻¹) * a := by rw [hxa]
        _ = a * x := by group)⟩
  have hxN : x ∈ cfgM T T₂ := by
    rw [hTCa] at hxC
    exact Cfg.normIn_le_cfgM_left T T₂ hxC
  have hxb : x ∈ T ⊓ Subgroup.centralizer ({b} : Set G) := ⟨hxT, hNb hxN⟩
  rw [hTCb] at hxb
  exact hxM (by rw [← D.hM]; exact Cfg.normIn_le_cfgM_left T T₁ hxb)

end Case1

section Case2

variable {G : Type} [Group G] [Finite G] {T T₁ X M : Subgroup G} [hN : (M.subgroupOf X).Normal]
  {F : Type} [Field F] [Finite F] [CharP F 2] {a : G}

theorem Data312.card_le_four (D : Data312 T T₁ X M F a) {T₂ : Subgroup G} (hS₂ : Sec3 T T₂)
    (haT₂ : a ∈ T₂) (ha1 : a ≠ 1) {b : G} (hbL₁ : b ∈ normIn T₁ T) (hb1 : b ≠ 1)
    {F' : Type} [Field F'] [Finite F'] [CharP F' 2]
    [hN₂ : ((cfgM T T₂).subgroupOf (T ⊔ T₂)).Normal]
    (D₂ : Data312 T T₂ (T ⊔ T₂) (cfgM T T₂) F' b) :
    Nat.card (normIn T T₁) = Nat.card F ∧
      Nat.card ↥(T ⊓ Subgroup.centralizer ({a} : Set G)) ≤ 4 := by
  have hS := D.sec3
  have haTn : a ∈ normIn T₂ T := mem_normIn.2 ⟨haT₂, mem_normalizer_iff_conjSubgroup_eq.2 D.aT⟩
  have hTCa : T ⊓ Subgroup.centralizer ({a} : Set G) = normIn T T₂ :=
    hS₂.cfg.inf_centralizer_eq_normIn haTn ha1
  have hTCb : T ⊓ Subgroup.centralizer ({b} : Set G) = normIn T T₁ :=
    hS.cfg.inf_centralizer_eq_normIn hbL₁ hb1
  have hbT₁ : b ∈ T₁ := normIn_le _ _ hbL₁
  have hTb := D₂.card_T_eq_sq
  rw [hTCb] at hTb
  have hTF := D.card_T_eq
  have hLF : Nat.card (normIn T T₁) = Nat.card F := by
    have hL0 : 0 < Nat.card (normIn T T₁) := Nat.card_pos
    rw [hTF, sq] at hTb
    exact (Nat.eq_of_mul_eq_mul_left hL0 hTb).symm
  refine ⟨hLF, ?_⟩
  by_contra hgt
  push Not at hgt
  have hFb : Nat.card ↥(normIn T₂ T ⊓ Subgroup.centralizer ({b} : Set G)) ^ 2 =
      Nat.card ↥(T ⊓ Subgroup.centralizer ({a} : Set G)) := by
    rw [D₂.card_centralizer_sq.2, hS₂.card_normIn_swap, hTCa]
  have hFb2 : 2 < Nat.card ↥(normIn T₂ T ⊓ Subgroup.centralizer ({b} : Set G)) := by
    by_contra h
    push Not at h
    nlinarith [hFb, hgt]
  obtain ⟨f₁, hf₁, hf₁1, f₂, hf₂, hf₂1, hf₁₂⟩ := exists_ne_one_ne_of_two_lt_natCard hFb2
  have hT₂ab : IsElemAbelian 2 T₂ := hS₂.cfg.wc₁.1
  have hprop : ∀ f ∈ normIn T₂ T ⊓ Subgroup.centralizer ({b} : Set G),
      conjSubgroup f T = T ∧ conjSubgroup f T₁ = T₁ ∧ f * f = 1 := fun f hf =>
    ⟨mem_normalizer_iff_conjSubgroup_eq.1 (mem_normIn.1 hf.1).2,
      mem_normalizer_iff_conjSubgroup_eq.1
        (hS.cfg.wc₁.centralizer_le_normalizer hbT₁ hb1 hf.2),
      elemAbelian_mul_self hT₂ab (normIn_le _ _ hf.1)⟩
  obtain ⟨hf₁T, hf₁T₁, hf₁f₁⟩ := hprop f₁ hf₁
  obtain ⟨hf₂T, hf₂T₁, hf₂f₂⟩ := hprop f₂ hf₂
  have hcomm : f₁ * f₂ = f₂ * f₁ :=
    elemAbelian_mul_comm hT₂ab (normIn_le _ _ hf₁.1) (normIn_le _ _ hf₂.1)
  obtain ⟨e', he'F, he'1, htriv⟩ : ∃ e' ∈ normIn T₂ T ⊓ Subgroup.centralizer ({b} : Set G),
      e' ≠ 1 ∧ ∀ y ∈ X, y⁻¹ * (e' * y * e'⁻¹) ∈ M := by
    rcases eq_or_eq_one_of_commute_involutions (D.rho hf₁T hf₁T₁) (D.rho hf₂T hf₂T₁)
      (D.rho_mem_utri_iff hf₁T hf₁T₁) (D.rho_mem_ltri_iff hf₁T hf₁T₁)
      (D.rho_mem_utri_iff hf₂T hf₂T₁) (D.rho_mem_ltri_iff hf₂T hf₂T₁)
      (D.rho_rho hf₁T hf₁T₁ hf₁f₁) (D.rho_rho hf₂T hf₂T₁ hf₂f₂)
      (D.rho_comm hf₁T hf₁T₁ hf₂T hf₂T₁ hcomm) with h | h | h
    · exact ⟨f₁, hf₁, hf₁1, D.triv_of_rho_eq_self hf₁T hf₁T₁ h⟩
    · exact ⟨f₂, hf₂, hf₂1, D.triv_of_rho_eq_self hf₂T hf₂T₁ h⟩
    · refine ⟨f₁ * f₂, Subgroup.mul_mem _ hf₁ hf₂, fun h1 => hf₁₂ ?_,
        D.triv_mul_of_rho_eq hf₁T hf₁T₁ hf₂T hf₂T₁ hf₁f₁ h⟩
      have h2 : f₂ = f₁⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [h2, inv_eq_of_mul_eq_one_right hf₁f₁]
  obtain ⟨n, hn, hFn⟩ := exists_natCard_eq_two_pow (F := F)
  have hpairD : IsL2Pair (↥X ⧸ M.subgroupOf X)
      ((T.subgroupOf X).map (QuotientGroup.mk' (M.subgroupOf X))) (2 ^ n) :=
    ⟨F, inferInstance, inferInstance, inferInstance, D.e, hFn, D.eT⟩
  have hMab : IsElemAbelian 2 M := by
    rw [← D.hM]
    exact hS.cfg.isElemAbelian_cfgM
  have hXM : ∀ x ∈ X, ∀ m ∈ M, x * m * x⁻¹ ∈ M := fun x hx m hm => by
    rw [← D.hX] at hx
    rw [← D.hM] at hm ⊢
    exact hS.cfg.conj_mem_cfgM hx hm
  have hbM : b ∈ M := by
    rw [← D.hM]
    exact Cfg.normIn_le_cfgM_right T T₁ hbL₁
  have hbe : b ∈ M ⊓ Subgroup.centralizer ({e'} : Set G) :=
    ⟨hbM, Subgroup.mem_centralizer_singleton_iff.2
      (Subgroup.mem_centralizer_singleton_iff.1 he'F.2).symm⟩
  have hne : M ⊓ Subgroup.centralizer ({e'} : Set G) ≠ ⊥ := fun h => by
    rw [h, Subgroup.mem_bot] at hbe
    exact hb1 hbe
  have hnorm : ∀ x ∈ X, ∀ m ∈ M ⊓ Subgroup.centralizer ({e'} : Set G),
      x * m * x⁻¹ ∈ M ⊓ Subgroup.centralizer ({e'} : Set G) := fun x hx m hm =>
    inf_centralizer_conj_mem hMab hXM htriv hx hm
  have hle : 2 ^ (2 * n) ≤ Nat.card ↥(M ⊓ Subgroup.centralizer ({e'} : Set G)) :=
    Sec3.two_pow_le_card_of_normal hS D.hX D.hM hn hpairD inf_le_left hnorm hne
  have hMcard : Nat.card M = 2 ^ (2 * n) := by
    rw [← D.hM, hS.card_cfgM_eq_sq, hLF, hFn, ← pow_mul, mul_comm]
  have heq : M ⊓ Subgroup.centralizer ({e'} : Set G) = M :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hMcard]; exact hle)
  have hMe : M ≤ Subgroup.centralizer ({e'} : Set G) := fun x hx => by
    have h : x ∈ M ⊓ Subgroup.centralizer ({e'} : Set G) := by rw [heq]; exact hx
    exact h.2
  have hTCe : T ⊓ Subgroup.centralizer ({e'} : Set G) = normIn T T₂ :=
    hS₂.cfg.inf_centralizer_eq_normIn (mem_normIn.2 ⟨normIn_le _ _ he'F.1,
      (mem_normIn.1 he'F.1).2⟩) he'1
  have hLM : normIn T T₁ ≤ M := by
    rw [← D.hM]
    exact Cfg.normIn_le_cfgM_left T T₁
  have hLCa : normIn T T₁ ≤ Subgroup.centralizer ({a} : Set G) := fun x hx => by
    have h : x ∈ T ⊓ Subgroup.centralizer ({e'} : Set G) := ⟨normIn_le _ _ hx, hMe (hLM hx)⟩
    rw [hTCe, ← hTCa] at h
    exact h.2
  have hLP : normIn T T₁ ⊓ Subgroup.centralizer ({a} : Set G) = normIn T T₁ :=
    inf_eq_left.2 hLCa
  have hP := D.card_centralizer_sq.1
  rw [hLP] at hP
  have hL1 : 1 < Nat.card (normIn T T₁) :=
    (Subgroup.one_lt_card_iff_ne_bot (H := normIn T T₁)).2 hS.cfg.ne
  nlinarith

end Case2

section Main

variable {G : Type} [Group G] [Finite G] {T T₁ X M : Subgroup G} [hN : (M.subgroupOf X).Normal]
  {F : Type} [Field F] [Finite F] [CharP F 2] {a : G}

theorem Data312.core (D : Data312 T T₁ X M F a) (haD : a ∈ classD T) (hglob : Sec3Global T)
    (hiso : Sec3IsoGlobal T) : Nat.card T = 16 ∧ Nat.card F = 4 := by
  have hS := D.sec3
  have hWC := hS.cfg.wc
  obtain ⟨g, t, htT, ht1, hat⟩ := haD
  have ha1 : a ≠ 1 := fun h => D.not_mem_T (h ▸ T.one_mem)
  obtain ⟨T₂, hT₂⟩ : ∃ T₂ : Subgroup G, T₂ = conjSubgroup g⁻¹ T := ⟨_, rfl⟩
  have haT₂ : a ∈ T₂ := by
    rw [hT₂, mem_conjSubgroup, inv_inv]
    have : g * a * g⁻¹ = t := by rw [hat]; group
    rw [this]
    exact htT
  have hT₂wc : IsWC T₂ := by
    rw [hT₂]
    exact hWC.conj g⁻¹
  have hT₂ne : conjSubgroup g⁻¹ T ≠ T := fun h => D.not_mem_T (by rw [← h, ← hT₂]; exact haT₂)
  obtain ⟨x, hxT, hxa, hxM⟩ := D.exists_centralizer_not_mem_M
  have hxC : x ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 (by
      calc x * a = (a * x * a⁻¹) * a := by rw [hxa]
        _ = a * x := by group)
  have hx1 : x ≠ 1 := fun h => hxM (h ▸ M.one_mem)
  have hLne : normIn T (conjSubgroup g⁻¹ T) ≠ ⊥ := by
    intro h
    have hxn : x ∈ normIn T (conjSubgroup g⁻¹ T) :=
      mem_normIn.2 ⟨hxT, by
        rw [← hT₂]
        exact hT₂wc.centralizer_le_normalizer haT₂ ha1 hxC⟩
    rw [h, Subgroup.mem_bot] at hxn
    exact hx1 hxn
  have hS₂ : Sec3 T T₂ := by
    rw [hT₂]
    exact hglob g⁻¹ hT₂ne hLne
  have hiso₂ : Sec3Iso T T₂ := by
    rw [hT₂]
    exact hiso g⁻¹ hT₂ne hLne
  obtain ⟨hN₂, f', hf', hpsl⟩ := hiso₂
  have hpair₂ := hS₂.isL2Pair_quotient hf' hpsl
  have haTn : a ∈ normIn T₂ T := mem_normIn.2 ⟨haT₂, mem_normalizer_iff_conjSubgroup_eq.2 D.aT⟩
  have hTCa : T ⊓ Subgroup.centralizer ({a} : Set G) = normIn T T₂ :=
    hS₂.cfg.inf_centralizer_eq_normIn haTn ha1
  have hc : Nat.card ↥(T ⊓ Subgroup.centralizer ({a} : Set G)) = 2 ^ f' := by
    have h1 := hS₂.card_eq_mul hf' hpsl
    have h2 := D.card_T_eq_sq
    rw [hTCa] at h2
    rw [h2, sq] at h1
    have hpos : 0 < Nat.card (normIn T T₂) := Nat.card_pos
    rw [hTCa]
    exact Nat.eq_of_mul_eq_mul_left hpos h1
  have hQ := D.card_centralizer_sq.2
  have hL₁1 : 1 < Nat.card (normIn T₁ T) :=
    (Subgroup.one_lt_card_iff_ne_bot (H := normIn T₁ T)).2 hS.cfg.ne₁
  have hQpos : 0 < Nat.card ↥(normIn T₁ T ⊓ Subgroup.centralizer ({a} : Set G)) := Nat.card_pos
  have hQ1 : 1 < Nat.card ↥(normIn T₁ T ⊓ Subgroup.centralizer ({a} : Set G)) := by
    by_contra h
    have h1 : Nat.card ↥(normIn T₁ T ⊓ Subgroup.centralizer ({a} : Set G)) = 1 := by omega
    rw [h1, one_pow] at hQ
    omega
  obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
    ((Subgroup.one_lt_card_iff_ne_bot (H := normIn T₁ T ⊓ Subgroup.centralizer ({a} : Set G))).1
      hQ1)
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hbL₁ : b ∈ normIn T₁ T := hb.1
  have hbC : b ∈ Subgroup.centralizer ({a} : Set G) := hb.2
  have hbT₁ : b ∈ T₁ := normIn_le _ _ hbL₁
  have hbb : b * b = 1 := elemAbelian_mul_self hS.cfg.wc₁.1 hbT₁
  have hbT : conjSubgroup b T = T := mem_normalizer_iff_conjSubgroup_eq.1 (mem_normIn.1 hbL₁).2
  have hbT₂ : conjSubgroup b T₂ = T₂ :=
    mem_normalizer_iff_conjSubgroup_eq.1 (hT₂wc.centralizer_le_normalizer haT₂ ha1 hbC)
  have hbY : conjSubgroup b (T ⊔ T₂) = T ⊔ T₂ := by
    rw [conjSubgroup_sup_eq_sup, hbT, hbT₂]
  have hbN : conjSubgroup b (cfgM T T₂) = cfgM T T₂ := by
    have h := cfgM_conj b T T₂
    rw [hbT, hbT₂] at h
    exact h.symm
  obtain ⟨x₂, hx₂, hT₂x⟩ := hS₂.conj
  have hconj : ∃ q : ↥(T ⊔ T₂) ⧸ (cfgM T T₂).subgroupOf (T ⊔ T₂),
      (T₂.subgroupOf (T ⊔ T₂)).map (QuotientGroup.mk' ((cfgM T T₂).subgroupOf (T ⊔ T₂))) =
        conjSubgroup q ((T.subgroupOf (T ⊔ T₂)).map
          (QuotientGroup.mk' ((cfgM T T₂).subgroupOf (T ⊔ T₂)))) := by
    refine ⟨QuotientGroup.mk' ((cfgM T T₂).subgroupOf (T ⊔ T₂)) ⟨x₂, hx₂⟩, ?_⟩
    rw [← map_subgroupOf_conjSubgroup_of_mem (T ⊔ T₂) (cfgM T T₂) T hx₂, ← hT₂x]
  have hdich := autInvolDichotomy _ _ _ _ hpair₂ hconj hS₂.map_ne_map
    (quotConjAut (T ⊔ T₂) (cfgM T T₂) b hbY hbN)
    (quotConjAut_quotConjAut_of_mul_self (T ⊔ T₂) (cfgM T T₂) b hbY hbN hbb)
    (map_subgroupOf_conjSubgroup_eq (T ⊔ T₂) (cfgM T T₂) b hbY hbN T ▸ by rw [hbT])
    (map_subgroupOf_conjSubgroup_eq (T ⊔ T₂) (cfgM T T₂) b hbY hbN T₂ ▸ by rw [hbT₂])
  rcases hdich with hid | ⟨F', i1, i2, i3, e', σ', hσ', hSe, hS'e, hφe⟩
  · exact (D.false_of_trivial hS₂ haT₂ ha1 hbL₁ hb1' (Nat.pos_of_ne_zero hf') hpair₂ hc
      (fun y hy => mem_of_quotConjAut_mk_eq (T ⊔ T₂) (cfgM T T₂) b hbY hbN ⟨y, hy⟩
        (hid _))).elim
  · have hD₂ : Data312 T T₂ (T ⊔ T₂) (cfgM T T₂) F' b :=
      { e := e'
        σ := σ'
        hX := rfl
        hM := rfl
        sec3 := hS₂
        aa := hbb
        aT := hbT
        aT₁ := hbT₂
        eT := hSe
        eT₁ := hS'e
        ind := ⟨fun x hx => by
          have h := conj_mem_conjSubgroup b hx
          rwa [hbY] at h, fun x => hφe (QuotientGroup.mk x)⟩
        σ_ne := hσ' }
    obtain ⟨hLF, hc4⟩ := D.card_le_four hS₂ haT₂ ha1 hbL₁ hb1' hD₂
    have hP := D.card_centralizer_sq.1
    have hFf := natCard_eq_sq_of_orderOf_eq_two D.orderOf_σ
    have hcc := D.card_centralizer_T
    have hTF := D.card_T_eq
    have h4 := D.four_le_card
    have hpf : Nat.card ↥(normIn T T₁ ⊓ Subgroup.centralizer ({a} : Set G)) =
        Nat.card (autFixedSubfield D.σ) := by
      have h1 : Nat.card ↥(normIn T T₁ ⊓ Subgroup.centralizer ({a} : Set G)) ^ 2 =
          Nat.card (autFixedSubfield D.σ) ^ 2 := by rw [hP, hLF, hFf]
      exact Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) h1
    have hc' : Nat.card ↥(T ⊓ Subgroup.centralizer ({a} : Set G)) = Nat.card F := by
      rw [hcc, hpf, hFf, sq]
    have hF4 : Nat.card F = 4 := le_antisymm (hc' ▸ hc4) h4
    refine ⟨?_, hF4⟩
    rw [hTF, hLF, hF4]

end Main

end CFSG.CGT.Timmesfeld75
