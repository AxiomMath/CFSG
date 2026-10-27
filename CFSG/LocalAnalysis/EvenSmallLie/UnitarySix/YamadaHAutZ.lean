module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.Child5HAutTransfer
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaHAutL1
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaHAutType

public noncomputable section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaHAut

open CFSG.Fischer Subgroup CFSG.EvenSmallLie.UnitarySix.YamadaSec3
open CFSG.EvenSmallLie.UnitarySix.YamadaD


theorem K1A1_comm_z {l : Equiv.Perm (Fin 693)} (hl : l ∈ chK1A1.grp) : l * gP 14 = gP 14 * l := by
  have hz : gP 14 ∈ chZ.grp := by
    rw [← wP_single]
    exact wP_mem_grp (by decide)
  have hle : chK1A1.grp ≤ centralizer (chZ.grp : Set (Equiv.Perm (Fin 693))) := by
    rw [chK1A1_eq]
    exact sup_le xComm_spec.2.2.2.2.2.1 xComm_spec.2.2.2.2.2.2.2
  exact ((mem_centralizer_iff.1 (hle hl)) _ hz).symm

theorem normalizer_A1_of_comm_z {x : Equiv.Perm (Fin 693)} (hx : x ∈ autT)
    (hz : x * gP 14 = gP 14 * x) : x ∈ normalizer (chA1.grp : Set (Equiv.Perm (Fin 693))) := by
  obtain ⟨l, hl, i, -, j, -, rfl⟩ := mem_autT_iff.1 hx
  have hd : Commute (dP ^ i) (gP 14) := Commute.pow_left (letter_spec.1 14 (by decide)) i
  have hs : Commute (sP ^ j) (gP 14) := Commute.pow_left (letter_spec.2.1 14 (by decide)) j
  have hc : Commute (dP ^ i * sP ^ j) (gP 14) := hd.mul_left hs
  have hx' : Commute (l * dP ^ i * sP ^ j) (gP 14) := hz
  have hlz : l * gP 14 = gP 14 * l := by
    have e1 : l = (l * dP ^ i * sP ^ j) * (dP ^ i * sP ^ j)⁻¹ := by group
    rw [e1]
    exact (hx'.mul_left hc.inv_left).eq
  have hlK : l ∈ chK1A1.grp := centralizer_gP14_le hl hlz
  have hlN : l ∈ normalizer (chA1.grp : Set (Equiv.Perm (Fin 693))) := by
    rw [chK1A1_eq] at hlK
    exact (sup_le chK1_le_normalizer_A1 le_normalizer) hlK
  exact mul_mem (mul_mem hlN (pow_mem norm_chA1.1 i)) (pow_mem norm_chA1.2 j)

theorem card_centralizer_z_autT :
    Nat.card (centralizer ({gP 14} : Set (Equiv.Perm (Fin 693))) ⊓ autT :
      Subgroup (Equiv.Perm (Fin 693))) = 6 * 13271040 := by
  have hcomm : ∀ (l : chK1A1.grp) (i j : ℕ), l * dP ^ i * sP ^ j * gP 14 =
      gP 14 * (l * dP ^ i * sP ^ j) := by
    intro l i j
    have h1 : Commute (l : Equiv.Perm (Fin 693)) (gP 14) := K1A1_comm_z l.2
    have hd : Commute (dP ^ i) (gP 14) := Commute.pow_left (letter_spec.1 14 (by decide)) i
    have hs : Commute (sP ^ j) (gP 14) := Commute.pow_left (letter_spec.2.1 14 (by decide)) j
    exact ((h1.mul_left hd).mul_left hs).eq
  let f : chK1A1.grp × Fin 3 × Fin 2 → (centralizer ({gP 14} : Set (Equiv.Perm (Fin 693))) ⊓
      autT : Subgroup (Equiv.Perm (Fin 693))) := fun p =>
    ⟨p.1 * dP ^ (p.2.1 : ℕ) * sP ^ (p.2.2 : ℕ), mem_inf.2 ⟨mem_centralizer_singleton_iff.2
      (hcomm p.1 _ _), mem_autT_of (grp_le_T46 gensOK_chK1A1 p.1.2) _ _⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨l, i, j⟩ ⟨l', i', j'⟩ h
      have h' := congrArg Subtype.val h
      obtain ⟨e1, e2, e3⟩ := mul_pow_inj (grp_le_T46 gensOK_chK1A1 l.2)
        (grp_le_T46 gensOK_chK1A1 l'.2) i.2 i'.2 j.2 j'.2 h'
      exact Prod.ext (Subtype.ext e1) (Prod.ext (Fin.ext e2) (Fin.ext e3))
    · rintro ⟨x, hx⟩
      obtain ⟨hxz, hxA⟩ := mem_inf.1 hx
      obtain ⟨l, hl, i, hi, j, hj, rfl⟩ := mem_autT_iff.1 hxA
      have hd : Commute (dP ^ i) (gP 14) := Commute.pow_left (letter_spec.1 14 (by decide)) i
      have hs : Commute (sP ^ j) (gP 14) := Commute.pow_left (letter_spec.2.1 14 (by decide)) j
      have hx' : Commute (l * dP ^ i * sP ^ j) (gP 14) := mem_centralizer_singleton_iff.1 hxz
      have hlz : l * gP 14 = gP 14 * l := by
        have e1 : l = (l * dP ^ i * sP ^ j) * (dP ^ i * sP ^ j)⁻¹ := by group
        rw [e1]
        exact (hx'.mul_left (hd.mul_left hs).inv_left).eq
      exact ⟨(⟨l, centralizer_gP14_le hl hlz⟩, ⟨i, hi⟩, ⟨j, hj⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, Nat.card_prod, card_chK1A1,
    Nat.card_fin, Nat.card_fin]

theorem chS_le_chK1A1 : chS.grp ≤ chK1A1.grp := grp_le_of_subset (by decide)

theorem le_chS_of_normal {N : Subgroup (Equiv.Perm (Fin 693))} (hN : N ≤ chK1A1.grp)
    (hnorm : ∀ k ∈ chK1A1.grp, ∀ n ∈ N, k * n * k⁻¹ ∈ N) (h2 : IsPGroup 2 N) : N ≤ chS.grp := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := chK1A1.grp
  set N' := N.subgroupOf K
  set S' := chS.grp.subgroupOf K
  have hN' : N'.Normal := ⟨fun n hn k => by
    rw [mem_subgroupOf] at hn ⊢
    simpa using hnorm k k.2 n hn⟩
  have hcS : Nat.card S' = 2 ^ 15 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe chS_le_chK1A1).toEquiv, card_chS]
    norm_num
  have hS2 : IsPGroup 2 S' := IsPGroup.of_card hcS
  have hidx : ¬ 2 ∣ S'.index := by
    have h := S'.card_mul_index
    rw [hcS, show Nat.card K = 13271040 from card_chK1A1] at h
    have h405 : S'.index = 405 := by omega
    rw [h405]
    decide
  have h2' : IsPGroup 2 N' := h2.of_equiv (subgroupOfEquivOfLe hN).symm
  have hle := h2'.le_sylow_of_normal (hS2.toSylow hidx)
  intro n hn
  have := hle (show (⟨n, hN hn⟩ : K) ∈ N' from mem_subgroupOf.2 hn)
  exact mem_subgroupOf.1 this

theorem mem_chZ_cases' {c : Equiv.Perm (Fin 693)} (hc : c ∈ chZ.grp) : c = 1 ∨ c = gP 14 := by
  have h1 : chZ.grp = zpowers (gP 14) := by
    rw [ChainData.grp, zpowers_eq_closure]
    congr 1
    ext x
    simp [chZ, wP_single]
  rw [h1] at hc
  have hsq : gP 14 ^ 2 = 1 := by rw [pow_two]; exact gP_mul_self (by norm_num)
  exact Yamada.eq_one_or_eq_of_mem_zpowers hsq hc

theorem comm_z_of_normalizer_A1 {x : Equiv.Perm (Fin 693)}
    (hN : x ∈ normalizer (chA1.grp : Set (Equiv.Perm (Fin 693)))) : x * gP 14 = gP 14 * x := by
  have hz : gP 14 ∈ chA1.grp := by
    rw [← wP_single]
    exact wP_mem_grp (by decide)
  have hz14 : gP 14 ∈ chZ.grp := by
    rw [← wP_single]
    exact wP_mem_grp (by decide)
  have hzc : ∀ b ∈ chA1.grp, gP 14 * b = b * gP 14 := fun b hb =>
    mem_centralizer_iff.1 (xComm_spec.2.2.2.2.2.2.2 hb) (gP 14) hz14
  set c := x * gP 14 * x⁻¹ with hcdef
  have hcA : c ∈ chA1.grp := (mem_normalizer_iff.1 hN _).1 hz
  have hcZ : c ∈ chZ.grp := (a1_spec c hcA).1 fun w hw => by
    have hb : x⁻¹ * wP w * x ∈ chA1.grp := by
      have := (mem_normalizer_iff.1 (inv_mem hN) (wP w)).1 (wP_mem_grp hw)
      simpa using this
    have h1 := hzc _ hb
    calc c * wP w = x * (gP 14 * (x⁻¹ * wP w * x)) * x⁻¹ := by rw [hcdef]; group
      _ = x * ((x⁻¹ * wP w * x) * gP 14) * x⁻¹ := by rw [h1]
      _ = wP w * c := by rw [hcdef]; group
  rcases mem_chZ_cases' hcZ with h1 | h1
  · exfalso
    apply gP14_ne_one
    calc gP 14 = x⁻¹ * c * x := by rw [hcdef]; group
      _ = 1 := by rw [h1]; group
  · calc x * gP 14 = c * x := by rw [hcdef]; group
      _ = gP 14 * x := by rw [h1]

theorem mem_K1A1_of_comm_z {l : Equiv.Perm (Fin 693)} (hl : l ∈ T46) (i j : ℕ)
    (hz : l * dP ^ i * sP ^ j * gP 14 = gP 14 * (l * dP ^ i * sP ^ j)) : l ∈ chK1A1.grp := by
  have hd : Commute (dP ^ i) (gP 14) := Commute.pow_left (letter_spec.1 14 (by decide)) i
  have hs : Commute (sP ^ j) (gP 14) := Commute.pow_left (letter_spec.2.1 14 (by decide)) j
  have hx' : Commute (l * dP ^ i * sP ^ j) (gP 14) := hz
  have hlz : l * gP 14 = gP 14 * l := by
    have e1 : l = (l * dP ^ i * sP ^ j) * (dP ^ i * sP ^ j)⁻¹ := by group
    rw [e1]
    exact (hx'.mul_left (hd.mul_left hs).inv_left).eq
  exact centralizer_gP14_le hl hlz

theorem mem_chA1_of_mod
    (c10 : ∀ {k : Equiv.Perm (Fin 693)} {i j : ℕ}, k ∈ chK1.grp → i < 3 → j < 2 →
      (∀ w ∈ chA1.gens, k * (dP ^ i * sP ^ j) * wP w * (k * (dP ^ i * sP ^ j))⁻¹ * (wP w)⁻¹ ∈
        chZ.grp) → k = 1 ∧ i = 0 ∧ j = 0)
    {x : Equiv.Perm (Fin 693)} (hx : x ∈ autT)
    (hN : x ∈ normalizer (chA1.grp : Set (Equiv.Perm (Fin 693))))
    (hc : ∀ b ∈ chA1.grp, x * b * x⁻¹ * b⁻¹ ∈ chZ.grp) : x ∈ chA1.grp := by
  have hxz := comm_z_of_normalizer_A1 hN
  obtain ⟨l, hl, i, hi, j, hj, rfl⟩ := mem_autT_iff.1 hx
  have hlK := mem_K1A1_of_comm_z hl i j hxz
  rw [chK1A1_eq] at hlK
  have hx2 : l ∈ ((chK1.grp ⊔ chA1.grp : Subgroup _) : Set (Equiv.Perm (Fin 693))) := hlK
  rw [coe_mul_of_left_le_normalizer_right _ _ chK1_le_normalizer_A1] at hx2
  obtain ⟨k, hk, a, ha, hka⟩ := hx2
  replace hka : k * a = l := hka
  set y := dP ^ i * sP ^ j with hy
  have hyN : y ∈ normalizer (chA1.grp : Set (Equiv.Perm (Fin 693))) :=
    mul_mem (pow_mem norm_chA1.1 i) (pow_mem norm_chA1.2 j)
  set a' := y⁻¹ * a * y with ha'
  have ha'A : a' ∈ chA1.grp := by
    have := (mem_normalizer_iff.1 (inv_mem hyN) a).1 ha
    simpa [ha'] using this
  have hxe : l * dP ^ i * sP ^ j = k * y * a' := by
    rw [ha', hy, ← hka]
    group
  have hz14 : ∀ c ∈ chZ.grp, (l * dP ^ i * sP ^ j) * c = c * (l * dP ^ i * sP ^ j) := by
    intro c hcz
    rcases mem_chZ_cases' hcz with rfl | rfl
    · group
    · exact hxz
  have hkey : ∀ w ∈ chA1.gens, k * y * wP w * (k * y)⁻¹ * (wP w)⁻¹ ∈ chZ.grp := by
    intro w hw
    have hcomm := (a1_spec _ (inv_mem ha'A)).2.2.1 w hw
    rw [commutatorElement_def] at hcomm
    set c := a'⁻¹ * wP w * a'⁻¹⁻¹ * (wP w)⁻¹ with hc'
    have hb := hc (wP w) (wP_mem_grp hw)
    have e1 : k * y * wP w * (k * y)⁻¹ * (wP w)⁻¹ =
        (l * dP ^ i * sP ^ j) * c * (l * dP ^ i * sP ^ j)⁻¹ *
          ((l * dP ^ i * sP ^ j) * wP w * (l * dP ^ i * sP ^ j)⁻¹ * (wP w)⁻¹) := by
      rw [hxe, hc']
      group
    rw [e1]
    have e2 : (l * dP ^ i * sP ^ j) * c * (l * dP ^ i * sP ^ j)⁻¹ = c := by
      rw [hz14 c hcomm]
      group
    rw [e2]
    exact mul_mem hcomm hb
  obtain ⟨rfl, rfl, rfl⟩ := c10 hk hi hj hkey
  rw [← hka]
  simpa using ha

theorem le_chA1_of_normal
    (c8 : ∀ {k : Equiv.Perm (Fin 693)} {i j : ℕ}, k ∈ chK1.grp → i < 3 → j < 2 → (i = 0 ∨ j = 1) →
      (∀ w ∈ chK1.gens, k * (dP ^ i * sP ^ j) * wP w * (k * (dP ^ i * sP ^ j))⁻¹ * (wP w)⁻¹ ∈
        chA1.grp) → k = 1 ∧ i = 0 ∧ j = 0)
    (i5 : ∀ {s : Equiv.Perm (Fin 693)}, s ∈ chS.grp →
      (wP [16, 17, 16, 17])⁻¹ * s * wP [16, 17, 16, 17] ∈ chS.grp → s ∈ chA1.grp)
    {C P : Subgroup (Equiv.Perm (Fin 693))}
    (hCz : C ≤ centralizer ({gP 14} : Set (Equiv.Perm (Fin 693))) ⊓ autT)
    (hKC : chK1A1.grp ≤ C) (hPC : P ≤ C) (hPn : C ≤ normalizer (P : Set (Equiv.Perm (Fin 693))))
    (h2 : IsPGroup 2 P) : P ≤ chA1.grp := by
  have hzP : ∀ p ∈ P, p * gP 14 = gP 14 * p := fun p hp =>
    mem_centralizer_singleton_iff.1 (mem_inf.1 (hCz (hPC hp))).1
  have hAP : ∀ p ∈ P, p ∈ autT := fun p hp => (mem_inf.1 (hCz (hPC hp))).2
  have hP0 : ∀ p ∈ P, p ∈ T46 → p ∈ chA1.grp := by
    set P₀ := P ⊓ T46 with hP₀
    have hP₀K : P₀ ≤ chK1A1.grp := fun p hp =>
      centralizer_gP14_le (mem_inf.1 hp).2 (hzP p (mem_inf.1 hp).1)
    have hnorm : ∀ k ∈ chK1A1.grp, ∀ n ∈ P₀, k * n * k⁻¹ ∈ P₀ := by
      intro k hk n hn
      refine mem_inf.2 ⟨(mem_normalizer_iff.1 (hPn (hKC hk)) n).1 (mem_inf.1 hn).1, ?_⟩
      have hkT : k ∈ T46 := grp_le_T46 gensOK_chK1A1 hk
      exact mul_mem (mul_mem hkT (mem_inf.1 hn).2) (inv_mem hkT)
    have hS := le_chS_of_normal hP₀K hnorm (h2.to_le inf_le_left)
    have hg : (wP [16, 17, 16, 17])⁻¹ ∈ chK1A1.grp :=
      inv_mem (wP_mem_of_letters _ (by decide))
    intro p hp hpT
    have hp0 : p ∈ P₀ := mem_inf.2 ⟨hp, hpT⟩
    refine i5 (hS hp0) (hS ?_)
    simpa using hnorm _ hg p hp0
  intro p hp
  by_contra hpA
  have hpT : p ∉ T46 := fun h => hpA (hP0 p hp h)
  obtain ⟨k₁, hk₁⟩ := h2 ⟨p, hp⟩
  have hk₁' : p ^ 2 ^ k₁ = 1 := by simpa using congrArg Subtype.val hk₁
  obtain ⟨l, hl, a, ha, rfl⟩ := field_of_pow_two_pow (hAP _ hp) hk₁' hpT
  have hlK := mem_K1A1_of_comm_z hl a 1 (by rw [pow_one]; exact hzP _ hp)
  rw [chK1A1_eq] at hlK
  have hx2 : l ∈ ((chK1.grp ⊔ chA1.grp : Subgroup _) : Set (Equiv.Perm (Fin 693))) := hlK
  rw [coe_mul_of_left_le_normalizer_right _ _ chK1_le_normalizer_A1] at hx2
  obtain ⟨k, hk, a₀, ha₀, hka⟩ := hx2
  replace hka : k * a₀ = l := hka
  set q := l * dP ^ a * sP with hq
  set y := dP ^ a * sP ^ 1 with hy
  have hyN : y ∈ normalizer (chA1.grp : Set (Equiv.Perm (Fin 693))) :=
    mul_mem (pow_mem norm_chA1.1 a) (pow_mem norm_chA1.2 1)
  set a' := y⁻¹ * a₀ * y with ha'
  have ha'A : a' ∈ chA1.grp := by
    have := (mem_normalizer_iff.1 (inv_mem hyN) a₀).1 ha₀
    simpa [ha'] using this
  have hqe : q = k * y * a' := by
    rw [hq, ha', hy, ← hka, pow_one]
    group
  have hqN : q ∈ normalizer (chA1.grp : Set (Equiv.Perm (Fin 693))) :=
    normalizer_A1_of_comm_z (hAP _ hp) (hzP _ hp)
  have hkey : ∀ w ∈ chK1.gens, k * y * wP w * (k * y)⁻¹ * (wP w)⁻¹ ∈ chA1.grp := by
    intro w hw
    have hbK : wP w ∈ chK1.grp := wP_mem_grp hw
    have hbN := chK1_le_normalizer_A1 hbK
    have hbC : wP w ∈ C := hKC (by rw [chK1A1_eq]; exact mem_sup_left hbK)
    have hbT : wP w ∈ T46 := grp_le_T46 gensOK_chK1 hbK
    have hqb : q * wP w * q⁻¹ * (wP w)⁻¹ ∈ chA1.grp := by
      refine hP0 _ ?_ ?_
      · have h1 : wP w * q⁻¹ * (wP w)⁻¹ ∈ P :=
          (mem_normalizer_iff.1 (hPn hbC) q⁻¹).1 (inv_mem hp)
        have := mul_mem hp h1
        simpa [mul_assoc] using this
      · have h1 : q * wP w * q⁻¹ ∈ T46 := (conj_mem_T46_iff (hAP _ hp)).2 hbT
        exact mul_mem h1 (inv_mem hbT)
    set a'' := (wP w)⁻¹ * a'⁻¹ * wP w * a' with ha''
    have ha''A : a'' ∈ chA1.grp := by
      refine mul_mem ?_ ha'A
      have := (mem_normalizer_iff.1 (inv_mem hbN) a'⁻¹).1 (inv_mem ha'A)
      simpa [mul_assoc] using this
    have e1 : k * y * wP w * (k * y)⁻¹ * (wP w)⁻¹ =
        (q * wP w * q⁻¹ * (wP w)⁻¹) * (wP w * (q * a'' * q⁻¹) * (wP w)⁻¹) := by
      rw [hqe, ha'']
      group
    rw [e1]
    refine mul_mem hqb ?_
    have h1 : q * a'' * q⁻¹ ∈ chA1.grp := (mem_normalizer_iff.1 hqN a'').1 ha''A
    exact (mem_normalizer_iff.1 hbN _).1 h1
  have := (c8 hk ha (by norm_num) (Or.inr rfl) hkey).2.2
  exact absurd this (by norm_num)

variable {G : Type} [Group G] {L : Subgroup G} {t : G} {e : L ≃* T46}
  {Θ : centralizer ({t} : Set G) →* Equiv.Perm (Fin 693)}

theorem card_eq_mul_map (hΘ : ThetaSpec t e Θ) {P : Subgroup G}
    (hP : P ≤ centralizer ({t} : Set G)) :
    Nat.card P = Nat.card (P ⊓ zpowers t : Subgroup G) *
      Nat.card ((P.subgroupOf (centralizer ({t} : Set G))).map Θ) := by
  set P' := P.subgroupOf (centralizer ({t} : Set G)) with hP'
  set f : P' →* Equiv.Perm (Fin 693) := Θ.comp P'.subtype with hf
  have h1 : Nat.card P' = Nat.card f.ker * Nat.card f.range := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, mul_comm]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  have h2 : f.range = P'.map Θ := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : ∀ p : P', p ∈ f.ker ↔ ((p : centralizer ({t} : Set G)) : G) ∈ zpowers t := by
    intro p
    rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, Subgroup.coe_subtype]
    exact hΘ.eq_one_iff _
  have h3 : Nat.card f.ker = Nat.card (P ⊓ zpowers t : Subgroup G) := by
    refine Nat.card_congr
      { toFun := fun p => ⟨((p : P') : centralizer ({t} : Set G)),
          mem_inf.2 ⟨mem_subgroupOf.1 (p : P').2, (hker p).1 p.2⟩⟩
        invFun := fun g => ⟨⟨⟨g, hP (mem_inf.1 g.2).1⟩, mem_subgroupOf.2 (mem_inf.1 g.2).1⟩,
          (hker _).2 (mem_inf.1 g.2).2⟩
        left_inv := fun p => rfl
        right_inv := fun g => rfl }
  have h4 : Nat.card P' = Nat.card P := Nat.card_congr (subgroupOfEquivOfLe hP).toEquiv
  rw [← h4, h1, h2, h3]


theorem comm_z_iff (hΘ : ThetaSpec t e Θ) (x : centralizer ({t} : Set G)) :
    (x : G) ∈ centralizer ({(sec3DData e t).z} : Set G) ↔ Θ x * gP 14 = gP 14 * Θ x := by
  rw [mem_centralizer_singleton_iff, show (sec3DData e t).z = gw e [14] from rfl,
    gw_eq [14] (by decide), hΘ.comm_iotaG_iff x _]
  change Θ x * wP [14] = wP [14] * Θ x ↔ _
  rw [wP_single]

theorem CHz_le' (hΘ : ThetaSpec t e Θ) :
    centralizer ({(sec3DData e t).z} : Set G) ⊓ (sec3DData e t).H ≤
      normalizer ((sec3DData e t).A₁ : Set G) := by
  rintro x ⟨hxz, hxH⟩
  have hz := (comm_z_iff hΘ ⟨x, hxH⟩).1 hxz
  exact (hΘ.mem_normalizer_toG_iff (grp_le_T46 gensOK_chA1) ⟨x, hxH⟩).2
    (normalizer_A1_of_comm_z (hΘ.mem_autT _) hz)

theorem card_CHz' (hΘ : ThetaSpec t e Θ) (ht : orderOf t = 2) :
    Nat.card (centralizer ({(sec3DData e t).z} : Set G) ⊓ (sec3DData e t).H : Subgroup G) ∣
      2 ^ 17 * 3 ^ 5 * 5 := by
  set P := centralizer ({(sec3DData e t).z} : Set G) ⊓ (sec3DData e t).H with hPdef
  have hPC : P ≤ centralizer ({t} : Set G) := inf_le_right
  have htP : t ∈ P := by
    refine mem_inf.2 ⟨mem_centralizer_singleton_iff.2 ?_, mem_centralizer_singleton_iff.2 rfl⟩
    exact ((mem_centralizer_iff.1 hΘ.t_mem_centralizer) _ (gw_mem_L [14])).symm
  have hinf : P ⊓ zpowers t = zpowers t := inf_eq_right.2 (zpowers_le.2 htP)
  have h1 := card_eq_mul_map hΘ hPC
  rw [hinf, Nat.card_zpowers, ht] at h1
  have h2 : (P.subgroupOf (centralizer ({t} : Set G))).map Θ ≤
      centralizer ({gP 14} : Set (Equiv.Perm (Fin 693))) ⊓ autT := by
    rintro _ ⟨x, hx, rfl⟩
    have hxP : (x : G) ∈ P := mem_subgroupOf.1 hx
    exact mem_inf.2 ⟨mem_centralizer_singleton_iff.2 ((comm_z_iff hΘ x).1 (mem_inf.1 hxP).1),
      hΘ.mem_autT x⟩
  have h3 := Subgroup.card_dvd_of_le h2
  rw [card_centralizer_z_autT] at h3
  rw [h1]
  calc 2 * Nat.card ((P.subgroupOf (centralizer ({t} : Set G))).map Θ) ∣ 2 * (6 * 13271040) :=
        Nat.mul_dvd_mul_left 2 h3
    _ = 2 ^ 17 * 3 ^ 5 * 5 := by norm_num

theorem comm_chZ_of (hΘ : ThetaSpec t e Θ) (x : centralizer ({t} : Set G))
    (hc : ∀ a ∈ (sec3DData e t).A₁, (x : G) * a * (x : G)⁻¹ * a⁻¹ ∈ zpowers (sec3DData e t).z) :
    ∀ b ∈ chA1.grp, Θ x * b * (Θ x)⁻¹ * b⁻¹ ∈ chZ.grp := by
  intro b hb
  have hbT : b ∈ T46 := grp_le_T46 gensOK_chA1 hb
  have h1 := hc (iotaG e ⟨b, hbT⟩) (iotaG_mem_toG.2 hb)
  rw [hΘ.conj_iotaG x ⟨b, hbT⟩, show (sec3DData e t).z = gw e [14] from rfl, ← toG_chZ] at h1
  have h2 : iotaG e (⟨Θ x * b * (Θ x)⁻¹, hΘ.conj_mem x ⟨b, hbT⟩⟩ * (⟨b, hbT⟩ : T46)⁻¹) ∈
      toG e chZ.grp := by
    rw [map_mul, map_inv]
    exact h1
  exact iotaG_mem_toG.1 h2

theorem CH_A₁_mod_of (hΘ : ThetaSpec t e Θ)
    (c10 : ∀ {k : Equiv.Perm (Fin 693)} {i j : ℕ}, k ∈ chK1.grp → i < 3 → j < 2 →
      (∀ w ∈ chA1.gens, k * (dP ^ i * sP ^ j) * wP w * (k * (dP ^ i * sP ^ j))⁻¹ * (wP w)⁻¹ ∈
        chZ.grp) → k = 1 ∧ i = 0 ∧ j = 0) :
    ∀ n ∈ (sec3DData e t).H, n ∈ normalizer ((sec3DData e t).A₁ : Set G) →
      (∀ a ∈ (sec3DData e t).A₁, n * a * n⁻¹ * a⁻¹ ∈ zpowers (sec3DData e t).z) →
      n ∈ (sec3DData e t).withT (sec3DData e t).A₁ := by
  intro n hn hN hc
  set x : centralizer ({t} : Set G) := ⟨n, hn⟩
  have hxN := (hΘ.mem_normalizer_toG_iff (grp_le_T46 gensOK_chA1) x).1 hN
  have hx := mem_chA1_of_mod c10 (hΘ.mem_autT x) hxN (comm_chZ_of hΘ x hc)
  exact (hΘ.mem_toG_sup_iff (grp_le_T46 gensOK_chA1) x).2 hx

theorem CH_A₁_of (hΘ : ThetaSpec t e Θ)
    (c10 : ∀ {k : Equiv.Perm (Fin 693)} {i j : ℕ}, k ∈ chK1.grp → i < 3 → j < 2 →
      (∀ w ∈ chA1.gens, k * (dP ^ i * sP ^ j) * wP w * (k * (dP ^ i * sP ^ j))⁻¹ * (wP w)⁻¹ ∈
        chZ.grp) → k = 1 ∧ i = 0 ∧ j = 0) :
    centralizer ((sec3DData e t).A₁ : Set G) ⊓ (sec3DData e t).H ≤ (sec3DData e t).ZR := by
  rintro n ⟨hC, hn⟩
  set x : centralizer ({t} : Set G) := ⟨n, hn⟩
  have hxC := (hΘ.mem_centralizer_toG_iff (grp_le_T46 gensOK_chA1) x).1 hC
  have hxA : Θ x ∈ chA1.grp := by
    refine mem_chA1_of_mod c10 (hΘ.mem_autT x) (centralizer_le_normalizer _ hxC) fun b hb => ?_
    rw [(mem_centralizer_iff.1 hxC b hb).symm]
    simp [one_mem]
  have hxZ : Θ x ∈ chZ.grp := (a1_spec _ hxA).1 fun w hw =>
    ((mem_centralizer_iff.1 hxC) _ (wP_mem_grp hw)).symm
  have h := (hΘ.mem_toG_sup_iff (grp_le_T46 gensOK_chZ) x).2 hxZ
  rw [toG_chZ] at h
  exact h

theorem oTwo_CHz_of (hΘ : ThetaSpec t e Θ)
    (c8 : ∀ {k : Equiv.Perm (Fin 693)} {i j : ℕ}, k ∈ chK1.grp → i < 3 → j < 2 → (i = 0 ∨ j = 1) →
      (∀ w ∈ chK1.gens, k * (dP ^ i * sP ^ j) * wP w * (k * (dP ^ i * sP ^ j))⁻¹ * (wP w)⁻¹ ∈
        chA1.grp) → k = 1 ∧ i = 0 ∧ j = 0)
    (i5 : ∀ {s : Equiv.Perm (Fin 693)}, s ∈ chS.grp →
      (wP [16, 17, 16, 17])⁻¹ * s * wP [16, 17, 16, 17] ∈ chS.grp → s ∈ chA1.grp) :
    ∀ P : Subgroup G, P ≤ centralizer ({(sec3DData e t).z} : Set G) ⊓ (sec3DData e t).H →
      centralizer ({(sec3DData e t).z} : Set G) ⊓ (sec3DData e t).H ≤ normalizer (P : Set G) →
      IsPGroup 2 P → P ≤ (sec3DData e t).withT (sec3DData e t).A₁ := by
  intro P hP hnorm h2
  have hPC : P ≤ centralizer ({t} : Set G) := hP.trans inf_le_right
  refine (hΘ.le_toG_sup_iff (grp_le_T46 gensOK_chA1) hPC).2 ?_
  refine le_chA1_of_normal c8 i5 (C := ((centralizer ({(sec3DData e t).z} : Set G) ⊓
    (sec3DData e t).H).subgroupOf (centralizer ({t} : Set G))).map Θ) ?_ ?_ ?_
    (ThetaSpec.map_le_normalizer hnorm) (ThetaSpec.isPGroup_map h2)
  · rintro _ ⟨x, hx, rfl⟩
    have hx' := mem_subgroupOf.1 hx
    exact mem_inf.2 ⟨mem_centralizer_singleton_iff.2 ((comm_z_iff hΘ x).1 (mem_inf.1 hx').1),
      hΘ.mem_autT x⟩
  · intro l hl
    have hlT := grp_le_T46 gensOK_chK1A1 hl
    refine ⟨⟨iotaG e ⟨l, hlT⟩, hΘ.L_le_centralizer (iotaG_mem _)⟩, mem_subgroupOf.2 ?_,
      hΘ.apply_iotaG _⟩
    refine mem_inf.2 ⟨(comm_z_iff hΘ _).2 ?_, hΘ.L_le_centralizer (iotaG_mem _)⟩
    rw [hΘ.apply_iotaG]
    exact K1A1_comm_z hl
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, mem_subgroupOf.2 (hP (mem_subgroupOf.1 hx)), rfl⟩

end CFSG.EvenSmallLie.UnitarySix.YamadaHAut
