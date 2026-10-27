module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisE16c
public import CFSG.Goldschmidt.Steps.GoldType

public noncomputable section

namespace CFSG.ComponentClassification.GHarris.E16

open CFSG Subgroup ThmC CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23

variable {X : Type} [Group X] [Finite X] {D : ThmC.UTSylow X}

namespace CaseB

theorem eq_one_of_mem (hB : CaseB D) {K₁ K₂ : Subgroup X} (h₁ : gComp D.E K₁)
    (h₂ : gComp D.E K₂) (hne : K₁ ≠ K₂) {x : X} (hx₁ : x ∈ K₁) (hx₂ : x ∈ K₂) : x = 1 :=
  hB.eq_one K₁ h₁ x hx₁ fun k' hk' => (gComp_comm h₁ h₂ hne k' hk' x hx₂).symm

omit [Finite X] in
theorem isSimpleGroup (hB : CaseB D) {K : Subgroup X} (hK : gComp D.E K) : IsSimpleGroup K := by
  have hZ : center K = ⊥ := eq_bot_iff.mpr fun z hz => mem_bot.mpr (Subtype.ext
    (hB.eq_one K hK z z.2 fun k' hk' =>
      (congrArg Subtype.val (mem_center_iff.mp hz ⟨k', hk'⟩)).symm))
  have : IsSimpleGroup (K ⧸ center K) := (gComp_quasisimple hK).2
  exact (QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hZ.symm)).isSimpleGroup

omit [Finite X] in
theorem toX_not_mem_E {u : UT3 F4c} (hu : u.b ≠ 0) : D.toX u ∉ D.E :=
  fun h => hu (D.toX_mem_E_iff.mp h)

omit [Finite X] in
theorem toX_ne_one {u : UT3 F4c} (hu : u ≠ 1) : D.toX u ≠ 1 :=
  fun h => hu (D.toX_injective (h.trans (map_one D.toX).symm))

omit [Finite X] in
theorem conj_mem_E {t e : X} (ht : t ∈ (D.T : Subgroup X)) (he : e ∈ D.E) :
    t * e * t⁻¹ ∈ D.E := by
  obtain ⟨u, rfl⟩ := D.exists_toX ht
  obtain ⟨w, hw, rfl⟩ := he
  rw [← map_inv, ← map_mul, ← map_mul, ut_conj]
  exact D.toX_mem_E_iff.mpr (mem_Eu.mp hw)

theorem false_of_three (hB : CaseB D) (h4 : ∀ K, gComp D.E K → 4 ≤ Nat.card (D.E ⊓ K : Subgroup X))
    {K₁ K₂ K₃ : Subgroup X} (h₁ : gComp D.E K₁) (h₂ : gComp D.E K₂) (h₃ : gComp D.E K₃)
    (h12 : K₁ ≠ K₂) (h13 : K₁ ≠ K₃) (h23 : K₂ ≠ K₃) : False := by
  let f : (D.E ⊓ K₁ : Subgroup X) × (D.E ⊓ K₂ : Subgroup X) × (D.E ⊓ K₃ : Subgroup X) → D.E :=
    fun p => ⟨p.1 * p.2.1 * p.2.2, mul_mem (mul_mem p.1.2.1 p.2.1.2.1) p.2.2.2.1⟩
  have hC : ∀ {K : Subgroup X}, gComp D.E K → K ≠ K₁ → ∀ y ∈ K,
      y ∈ centralizer (K₁ : Set X) := fun hK hne y hy =>
    mem_centralizer_iff.mpr fun k hk => gComp_comm h₁ hK hne.symm k hk y hy
  have hf : Function.Injective f := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
    have h' : (a : X) * b * c = a' * b' * c' := congrArg Subtype.val h
    have ha : a = a' := by
      have hx : (a' : X)⁻¹ * a = b' * c' * (c : X)⁻¹ * (b : X)⁻¹ := by
        calc (a' : X)⁻¹ * a = (a' : X)⁻¹ * (a * b * c) * (c : X)⁻¹ * (b : X)⁻¹ := by group
          _ = (a' : X)⁻¹ * (a' * b' * c') * (c : X)⁻¹ * (b : X)⁻¹ := by rw [h']
          _ = b' * c' * (c : X)⁻¹ * (b : X)⁻¹ := by group
      have hxC : (a' : X)⁻¹ * a ∈ centralizer (K₁ : Set X) := by
        rw [hx]
        exact mul_mem (mul_mem (mul_mem (hC h₂ h12.symm _ b'.2.2) (hC h₃ h13.symm _ c'.2.2))
          (inv_mem (hC h₃ h13.symm _ c.2.2))) (inv_mem (hC h₂ h12.symm _ b.2.2))
      have h1 := hB.eq_one K₁ h₁ _ (mul_mem (inv_mem a'.2.2) a.2.2) fun k hk =>
        (mem_centralizer_iff.mp hxC k hk).symm
      exact Subtype.ext (inv_mul_eq_one.mp h1).symm
    subst ha
    have h'' : (b : X) * c = b' * c' := by
      rw [mul_assoc, mul_assoc] at h'
      exact mul_left_cancel h'
    have hb : b = b' := by
      have hy : (b' : X)⁻¹ * b = c' * (c : X)⁻¹ := by
        calc (b' : X)⁻¹ * b = (b' : X)⁻¹ * (b * c) * (c : X)⁻¹ := by group
          _ = (b' : X)⁻¹ * (b' * c') * (c : X)⁻¹ := by rw [h'']
          _ = c' * (c : X)⁻¹ := by group
      have hy3 : (b' : X)⁻¹ * b ∈ K₃ := by
        rw [hy]
        exact mul_mem c'.2.2 (inv_mem c.2.2)
      have h1 := hB.eq_one_of_mem h₂ h₃ h23 (mul_mem (inv_mem b'.2.2) b.2.2) hy3
      exact Subtype.ext (inv_mul_eq_one.mp h1).symm
    subst hb
    have hc : c = c' := Subtype.ext (mul_left_cancel h'')
    subst hc
    rfl
  have hcard := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, Nat.card_prod, D.card_E] at hcard
  have h64 : 4 * (4 * 4) ≤ Nat.card (D.E ⊓ K₁ : Subgroup X) *
      (Nat.card (D.E ⊓ K₂ : Subgroup X) * Nat.card (D.E ⊓ K₃ : Subgroup X)) :=
    Nat.mul_le_mul (h4 _ h₁) (Nat.mul_le_mul (h4 _ h₂) (h4 _ h₃))
  exact absurd (h64.trans hcard) (by norm_num)


theorem comp_facts (hB : CaseB D) {K : Subgroup X} (hK : gComp D.E K) :
    4 ≤ Nat.card (D.E ⊓ K : Subgroup X) ∧
      (D.E ≤ K → (∀ x ∈ D.E, ∀ y ∈ D.E, x ≠ 1 → y ≠ 1 →
          ∃ n ∈ K, n ∈ normalizer (D.E : Set X) ∧ n⁻¹ * x * n = y) ∧
        ∀ R : Subgroup X, IsPGroup 2 R → D.E ≤ R → R ≤ K → R = D.E) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup K := hB.isSimpleGroup hK
  obtain ⟨Q, hQ⟩ := gComp_sylow hK D.T
  have hTK : (D.T : Subgroup X) ⊓ K = D.E ⊓ K :=
    le_antisymm (le_inf ((inf_le_inf_left _ (gComp_le hK)).trans hB.T_inf_le) inf_le_right)
      (inf_le_inf_right _ D.E_le_T)
  rw [hTK] at hQ
  have hQE : ∀ q : K, q ∈ (Q : Subgroup K) → (q : X) ∈ D.E := fun q hq => by
    have h := mem_map_of_mem K.subtype hq
    rw [hQ] at h
    exact h.1
  have hQ2 : ∀ q ∈ (Q : Subgroup K), q ^ 2 = 1 := fun q hq => Subtype.ext (by
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one, sq]
    exact D.E_mul_self (hQE q hq))
  have hΩ := CFSG.Goldschmidt.GoldType.omega1_eq_self hQ2
  have hab : IsMulCommutative (CFSG.Goldschmidt.Omega1 (Q : Subgroup K)) := by
    rw [hΩ]
    exact ⟨⟨fun a b => Subtype.ext (Subtype.ext (D.E_comm (hQE _ a.2) (hQE _ b.2)))⟩⟩
  obtain ⟨h4, htr⟩ := CFSG.Goldschmidt.N11b K (hB.type K hK) Q hab
  rw [hΩ] at h4 htr
  have hcard : Nat.card (Q : Subgroup K) = Nat.card (D.E ⊓ K : Subgroup X) := by
    rw [← hQ, card_map_of_injective (subtype_injective _)]
  refine ⟨h4.trans_eq hcard, fun hEK => ⟨?_, ?_⟩⟩
  ·
    have hQE' : (Q : Subgroup K).map K.subtype = D.E := by rw [hQ, inf_eq_left.mpr hEK]
    intro x hx y hy hx1 hy1
    obtain ⟨x', hx'Q, rfl⟩ := hQE'.ge hx
    obtain ⟨y', hy'Q, rfl⟩ := hQE'.ge hy
    obtain ⟨n, hn, hnxy⟩ := htr x' hx'Q y' hy'Q (fun h => hx1 (by rw [h, map_one]))
      (fun h => hy1 (by rw [h, map_one]))
    refine ⟨n, n.2, mem_normalizer_fintype fun e he => ?_, by simpa using congrArg K.subtype hnxy⟩
    obtain ⟨e', he'Q, rfl⟩ := hQE'.ge he
    have h2 := mem_map_of_mem K.subtype ((mem_normalizer_iff.mp hn e').mp he'Q)
    rw [hQE'] at h2
    simpa using h2
  ·
    intro R hR hER hRK
    have hRK' : IsPGroup 2 (R.subgroupOf K) := hR.comap_of_injective K.subtype (subtype_injective _)
    have hQR : (Q : Subgroup K) ≤ R.subgroupOf K := fun q hq => mem_subgroupOf.mpr (hER (hQE q hq))
    have h := Q.is_maximal' hRK' hQR
    calc R = (R.subgroupOf K).map K.subtype := (map_subgroupOf_eq_of_le hRK).symm
      _ = (Q : Subgroup K).map K.subtype := by rw [h]
      _ = D.E := by rw [hQ, inf_eq_left.mpr hEK]

theorem E_le_of_normalized (hB : CaseB D) {K : Subgroup X} (hK : gComp D.E K)
    (hTK : ∀ t ∈ (D.T : Subgroup X), ∀ k ∈ K, t * k * t⁻¹ ∈ K) : D.E ≤ K := by
  have hNT : ∀ t ∈ (D.T : Subgroup X), ∀ n ∈ D.E ⊓ K, t * n * t⁻¹ ∈ D.E ⊓ K :=
    fun t ht n hn => mem_inf.mpr ⟨conj_mem_E ht hn.1, hTK t ht n hn.2⟩
  have hZK : D.Z ≤ K := by
    rcases D.le_Z_or_Z_le inf_le_left hNT with h | h
    · have hEq : D.E ⊓ K = D.Z := Subgroup.eq_of_le_of_card_ge h
        (by rw [D.card_Z]; exact (hB.comp_facts hK).1)
      exact hEq.ge.trans inf_le_right
    · exact h.trans inf_le_right
  by_contra hEK
  obtain ⟨K₂, hK₂, hne⟩ : ∃ K₂, gComp D.E K₂ ∧ K₂ ≠ K := by
    by_contra h
    push Not at h
    apply hEK
    refine hB.E_le.trans ?_
    rw [gL_eq_sSup]
    exact sSup_le fun K₂ hK₂ => (h K₂ hK₂).le
  obtain ⟨e, he, he1⟩ : ∃ e ∈ D.E ⊓ K₂, e ≠ 1 := by
    by_contra h
    push Not at h
    have h1 : D.E ⊓ K₂ = ⊥ := eq_bot_iff.mpr fun e he => mem_bot.mpr (h e he)
    have h2 := (hB.comp_facts hK₂).1
    rw [h1, card_bot] at h2
    omega
  have htT : D.toX ⟨0, 1, 0⟩ ∈ (D.T : Subgroup X) := D.toX_mem _
  have htE : D.toX ⟨0, 1, 0⟩ ∉ D.E := toX_not_mem_E (by decide)
  set t := D.toX ⟨0, 1, 0⟩
  have hcZ : e⁻¹ * t * e * t⁻¹ ∈ D.Z := by
    have h := D.comm_mem_Z (D.E_le_T he.1) (inv_mem htT)
    rwa [inv_inv] at h
  have hcc : ∀ k ∈ K, (e⁻¹ * t * e * t⁻¹) * k = k * (e⁻¹ * t * e * t⁻¹) := by
    intro k hk
    have h1 : e⁻¹ * k = k * e⁻¹ := gComp_comm hK₂ hK hne _ (inv_mem he.2) k hk
    have h2 : e * (t⁻¹ * k * t⁻¹⁻¹) = (t⁻¹ * k * t⁻¹⁻¹) * e :=
      gComp_comm hK₂ hK hne e he.2 _ (hTK _ (inv_mem htT) k hk)
    have h3 : t * e * t⁻¹ * k = k * (t * e * t⁻¹) := by
      calc t * e * t⁻¹ * k = t * (e * (t⁻¹ * k * t⁻¹⁻¹)) * t⁻¹ := by group
        _ = t * ((t⁻¹ * k * t⁻¹⁻¹) * e) * t⁻¹ := by rw [h2]
        _ = k * (t * e * t⁻¹) := by group
    calc e⁻¹ * t * e * t⁻¹ * k = e⁻¹ * (t * e * t⁻¹ * k) := by group
      _ = e⁻¹ * (k * (t * e * t⁻¹)) := by rw [h3]
      _ = (e⁻¹ * k) * (t * e * t⁻¹) := by group
      _ = (k * e⁻¹) * (t * e * t⁻¹) := by rw [h1]
      _ = k * (e⁻¹ * t * e * t⁻¹) := by group
  have hc1 := hB.eq_one K hK _ (hZK hcZ) hcc
  have het : e * t = t * e := by
    have h : t * e * t⁻¹ = e := by
      calc t * e * t⁻¹ = e * (e⁻¹ * t * e * t⁻¹) := by group
        _ = e := by rw [hc1, mul_one]
    calc e * t = (t * e * t⁻¹) * t := by rw [h]
      _ = t * e := by group
  exact he1 (hB.eq_one_of_mem hK hK₂ hne.symm
    (hZK (D.mem_Z_of_comm_of_not_mem he.1 htT htE het)) he.2)

theorem exists_normalized (hB : CaseB D) :
    ∃ K, gComp D.E K ∧ ∀ t ∈ (D.T : Subgroup X), ∀ k ∈ K, t * k * t⁻¹ ∈ K := by
  obtain ⟨K₁, h₁⟩ : ∃ K, gComp D.E K := by
    by_contra h
    push Not at h
    have hL : gL D.E = ⊥ := by
      rw [gL_eq_sSup]
      exact sSup_eq_bot.mpr fun K hK => absurd hK (h K)
    have h1 := hB.E_le (D.toX_mem_E_iff.mpr rfl : D.toX ⟨1, 0, 0⟩ ∈ D.E)
    rw [hL, mem_bot] at h1
    exact toX_ne_one (by decide) h1
  by_contra hcon
  push Not at hcon
  obtain ⟨t₀, ht₀, k₀, hk₀, hk₀'⟩ := hcon K₁ h₁
  have hne₀ : K₁.map (MulAut.conj t₀).toMonoidHom ≠ K₁ := fun h =>
    hk₀' (h ▸ ⟨k₀, hk₀, rfl⟩)
  have hZ1 : ∀ z ∈ D.Z, z ∈ K₁ → z = 1 := fun z hz hzK => by
    refine hB.eq_one_of_mem h₁ (gComp_conj h₁ t₀) hne₀.symm hzK ?_
    rw [mem_conj_iff, mul_assoc, D.Z_comm hz ht₀, inv_mul_cancel_left]
    exact hzK
  have hno : ∀ s ∈ (D.T : Subgroup X), s ∉ D.E → ¬ ∀ k ∈ K₁, s * k * s⁻¹ ∈ K₁ := by
    intro s hs hsE hsK
    have h1 : D.E ⊓ K₁ = ⊥ := eq_bot_iff.mpr fun e he => mem_bot.mpr (by
      have hc : e⁻¹ * s * e * s⁻¹ ∈ D.Z := by
        have h := D.comm_mem_Z (D.E_le_T he.1) (inv_mem hs)
        rwa [inv_inv] at h
      have hcK : e⁻¹ * s * e * s⁻¹ ∈ K₁ := by
        rw [show e⁻¹ * s * e * s⁻¹ = e⁻¹ * (s * e * s⁻¹) by group]
        exact mul_mem (inv_mem he.2) (hsK e he.2)
      have hc1 := hZ1 _ hc hcK
      have hes : e * s = s * e := by
        have h : s * e * s⁻¹ = e := by
          calc s * e * s⁻¹ = e * (e⁻¹ * s * e * s⁻¹) := by group
            _ = e := by rw [hc1, mul_one]
        calc e * s = (s * e * s⁻¹) * s := by rw [h]
          _ = s * e := by group
      exact hZ1 e (D.mem_Z_of_comm_of_not_mem he.1 hs hsE hes) he.2)
    have h2 := (hB.comp_facts h₁).1
    rw [h1, card_bot] at h2
    omega
  have hs₁ : D.toX ⟨0, 1, 0⟩ ∈ (D.T : Subgroup X) := D.toX_mem _
  have hs₂ : D.toX ⟨0, ⟨0, 1⟩, 0⟩ ∈ (D.T : Subgroup X) := D.toX_mem _
  have hs₁E : D.toX ⟨0, 1, 0⟩ ∉ D.E := toX_not_mem_E (by decide)
  have hs₂E : D.toX ⟨0, ⟨0, 1⟩, 0⟩ ∉ D.E := toX_not_mem_E (by decide)
  have hs₂₁E : (D.toX ⟨0, ⟨0, 1⟩, 0⟩)⁻¹ * D.toX ⟨0, 1, 0⟩ ∉ D.E := by
    rw [← map_inv, ← map_mul]
    exact toX_not_mem_E (by decide)
  have hconj : ∀ {s : X}, s ∈ (D.T : Subgroup X) → s ∉ D.E →
      K₁.map (MulAut.conj s).toMonoidHom ≠ K₁ := fun {s} hs hsE h => hno s hs hsE fun k hk => by
    have h0 : s * k * s⁻¹ ∈ K₁.map (MulAut.conj s).toMonoidHom := ⟨k, hk, rfl⟩
    rwa [h] at h0
  have h23 : K₁.map (MulAut.conj (D.toX ⟨0, 1, 0⟩)).toMonoidHom ≠
      K₁.map (MulAut.conj (D.toX ⟨0, ⟨0, 1⟩, 0⟩)).toMonoidHom := fun h =>
    hno _ (mul_mem (inv_mem hs₂) hs₁) hs₂₁E fun k hk => by
      have h0 : D.toX ⟨0, 1, 0⟩ * k * (D.toX ⟨0, 1, 0⟩)⁻¹ ∈
          K₁.map (MulAut.conj (D.toX ⟨0, 1, 0⟩)).toMonoidHom := ⟨k, hk, rfl⟩
      rw [h, mem_conj_iff] at h0
      rw [show (D.toX ⟨0, ⟨0, 1⟩, 0⟩)⁻¹ * D.toX ⟨0, 1, 0⟩ * k *
          ((D.toX ⟨0, ⟨0, 1⟩, 0⟩)⁻¹ * D.toX ⟨0, 1, 0⟩)⁻¹ =
        (D.toX ⟨0, ⟨0, 1⟩, 0⟩)⁻¹ * (D.toX ⟨0, 1, 0⟩ * k * (D.toX ⟨0, 1, 0⟩)⁻¹) *
          D.toX ⟨0, ⟨0, 1⟩, 0⟩ by group]
      exact h0
  exact hB.false_of_three (fun K hK => (hB.comp_facts hK).1) h₁ (gComp_conj h₁ _)
    (gComp_conj h₁ _) (hconj hs₁ hs₁E).symm (hconj hs₂ hs₂E).symm h23

end CaseB

end CFSG.ComponentClassification.GHarris.E16
