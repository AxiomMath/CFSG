module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74XSylow
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74OIBar
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74QDefs

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open CFSG Subgroup CFSG.LieType.Universal.Spin
open scoped commutatorElement

section Sylow

variable {K : Type} [Field K] [Finite K] {p f : ℕ} {i : spinGroup (quadOdd 3 K)}
  {P₂ : Subgroup (spinGroup (quadOdd 3 K))}

theorem pThree_le_odd (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    (hP : P₂ ≤ spinJ₂ K) : pThree i P₂ ≤ spinJ₃ K :=
  (map_mono hP).trans (hI.map_spinJ₂_odd hp hp2 hK).le

theorem commute_P₂_pThree_odd (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (hP : P₂ ≤ spinJ₂ K) :
    ∀ b ∈ P₂, ∀ c ∈ pThree i P₂, b * c = c * b := fun _ hb _ hc =>
  commute_spinJ₂_spinJ₃_odd (odd_card_spin hp hp2 hK) (hP hb) (pThree_le_odd hI hp hp2 hK hP hc)

theorem exists_mul_of_mem_bSyl_odd (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (hP : P₂ ≤ spinJ₂ K)
    {x : spinGroup (quadOdd 3 K)} (hx : x ∈ bSyl i P₂) :
    ∃ b ∈ P₂, ∃ c ∈ pThree i P₂, x = b * c :=
  exists_mul_of_mem_sup (commute_P₂_pThree_odd hI hp hp2 hK hP) hx

theorem bSyl_le_ct_odd (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    (hP : P₂ ≤ spinJ₂ K) :
    bSyl i P₂ ≤ centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))) ⊓
      centralizer ({qThree K} : Set (spinGroup (quadOdd 3 K))) :=
  (sup_le_sup hP (pThree_le_odd hI hp hp2 hK hP)).trans (sup_le_centralizer_inf hp hp2 hK)

theorem conj_mem_bSyl_odd (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    (hP : P₂ ≤ spinJ₂ K) {x : spinGroup (quadOdd 3 K)} (hx : x ∈ bSyl i P₂) :
    i * x * i⁻¹ ∈ bSyl i P₂ := by
  obtain ⟨b, hb, c, hc, rfl⟩ := exists_mul_of_mem_bSyl_odd hI hp hp2 hK hP hx
  have e : i * (b * c) * i⁻¹ = (i * c * i⁻¹) * (i * b * i⁻¹) := by
    rw [commute_P₂_pThree_odd hI hp hp2 hK hP b hb c hc]
    group
  rw [e]
  exact mul_mem (mem_sup_left (conj_mem_of_mem_pThree hI hc)) (mem_sup_right (conj_mem_pThree hb))

theorem mem_normalizer_bSyl_odd (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (hP : P₂ ≤ spinJ₂ K) :
    i ∈ normalizer (bSyl i P₂ : Set (spinGroup (quadOdd 3 K))) :=
  mem_normalizer_of_involution hI.mul_self fun _ hx => conj_mem_bSyl_odd hI hp hp2 hK hP hx

theorem bSyl_inf_zpowers_odd (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (hP : P₂ ≤ spinJ₂ K) :
    bSyl i P₂ ⊓ zpowers i = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hx1, hx2⟩ := mem_inf.mp hx
  rcases eq_one_or_eq_of_mem_zpowers_of_mul_self hI.mul_self hx2 with h | h
  · exact (mem_bot).mpr h
  · exact absurd (h ▸ (mem_inf.mp (bSyl_le_ct_odd hI hp hp2 hK hP hx1)).1)
      (hI.not_mem_centralizer_t hp hp2 hK)

theorem card_sSyl_odd (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    (hP : P₂ ≤ spinJ₂ K) :
    Nat.card ↥(sSyl i P₂) = Nat.card ↥(bSyl i P₂) * 2 := by
  have h := card_sup_mul_card_inf_of_le_normalizer'
    (zpowers_le.mpr (mem_normalizer_bSyl_odd hI hp hp2 hK hP))
  rw [bSyl_inf_zpowers_odd hI hp hp2 hK hP, card_bot, mul_one, Nat.card_zpowers,
    hI.orderOf_eq hp hp2 hK] at h
  exact h

theorem relIndex_bSyl_odd (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    (hP : P₂ ≤ spinJ₂ K) : (bSyl i P₂).relIndex (sSyl i P₂) = 2 := by
  have := finite_spinSeven (two_ne_zero_spin hp hp2 hK)
  have h := Subgroup.relIndex_mul_card (H := bSyl i P₂) (K := sSyl i P₂)
  rw [inf_of_le_left le_sup_left, card_sSyl_odd hI hp hp2 hK hP] at h
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h.trans (mul_comm _ _))

theorem mem_sSyl_odd (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    (hP : P₂ ≤ spinJ₂ K) {x : spinGroup (quadOdd 3 K)} (hx : x ∈ sSyl i P₂) :
    ∃ b ∈ bSyl i P₂, x = b ∨ x = b * i := by
  have hx' : x ∈ ((bSyl i P₂ ⊔ zpowers i : Subgroup (spinGroup (quadOdd 3 K))) :
      Set (spinGroup (quadOdd 3 K))) := hx
  rw [coe_mul_of_right_le_normalizer_left _ _
    (zpowers_le.mpr (mem_normalizer_bSyl_odd hI hp hp2 hK hP))] at hx'
  obtain ⟨b, hb, y, hy, rfl⟩ := hx'
  rcases eq_one_or_eq_of_mem_zpowers_of_mul_self hI.mul_self hy with rfl | rfl
  · exact ⟨b, hb, Or.inl (mul_one b)⟩
  · exact ⟨b, hb, Or.inr rfl⟩

theorem mul_self_mem_bSyl_odd (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (hP : P₂ ≤ spinJ₂ K)
    {x : spinGroup (quadOdd 3 K)} (hx : x ∈ sSyl i P₂) : x * x ∈ bSyl i P₂ := by
  obtain ⟨b, hb, rfl | rfl⟩ := mem_sSyl_odd hI hp hp2 hK hP hx
  · exact mul_mem hb hb
  · have e : b * i * (b * i) = b * (i * b * i⁻¹) := by
      rw [hI.inv_eq]
      group
    rw [e]
    exact mul_mem hb (conj_mem_bSyl_odd hI hp hp2 hK hP hb)

theorem card_bSyl_odd (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    (hP : P₂ ≤ spinJ₂ K) :
    Nat.card ↥(bSyl i P₂) = Nat.card P₂ * Nat.card P₂ := by
  rw [card_sup_of_commute (commute_P₂_pThree_odd hI hp hp2 hK hP),
    card_map_of_injective (f := (MulAut.conj i).toMonoidHom) (MulAut.conj i).injective]
  rw [eq_bot_iff]
  intro x hx
  exact (mem_bot).mpr ((spinJ_inf_eq_one_odd hp hp2 hK).2.2 (hP (mem_inf.mp hx).1)
    (pThree_le_odd hI hp hp2 hK hP (mem_inf.mp hx).2))

section A4

theorem eq_of_commute_pThree_odd (hA4 : A4) (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (hP : P₂ ≤ spinJ₂ K) (hP2 : IsPGroup 2 P₂)
    (hPi : ¬ 2 ∣ P₂.relIndex (spinJ₂ K)) {c : spinGroup (quadOdd 3 K)} (hc : c ∈ spinJ₃ K)
    (hcP : ∀ y ∈ pThree i P₂, c * y = y * c) : c = 1 ∨ c = spinZ K * tSeven K := by
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  obtain ⟨-, hcent⟩ := (hA4 K hodd).2 P₂ hP hP2 hPi
  have hcomm : ∀ y ∈ P₂, (i * c * i⁻¹) * y = y * (i * c * i⁻¹) := by
    intro y hy
    have h := hcP _ (conj_mem_pThree hy)
    have hy' : y = i * (i * y * i⁻¹) * i⁻¹ := (hI.conj_conj y).symm
    rw [hy']
    exact conj_mul_conj_comm i h
  rcases hcent _ (hI.conj_mem_spinJ₂_odd hp hp2 hK hc) hcomm with h | h
  · left
    calc c = i⁻¹ * (i * c * i⁻¹) * i := by group
      _ = 1 := by rw [h]; group
  · right
    calc c = i * (i * c * i⁻¹) * i⁻¹ := (hI.conj_conj c).symm
      _ = spinZ K * tSeven K := by rw [h, hI.conj_t]

theorem involutions_bSyl_odd (hA4 : A4) (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (hP : P₂ ≤ spinJ₂ K)
    {x : spinGroup (quadOdd 3 K)} (hx : x ∈ bSyl i P₂) (hxx : x * x = 1) :
    x = 1 ∨ x = spinZ K ∨ x = tSeven K ∨ x = spinZ K * tSeven K := by
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  obtain ⟨b, hb, c, hc, rfl⟩ := exists_mul_of_mem_bSyl_odd hI hp hp2 hK hP hx
  have hc3 := pThree_le_odd hI hp hp2 hK hP hc
  have e : b * b * (c * c) = 1 * 1 := by
    rw [← mul_mul_self_of_commute (commute_P₂_pThree_odd hI hp hp2 hK hP b hb c hc), hxx,
      one_mul]
  obtain ⟨hb1, hc1⟩ := eq_of_mul_eq_mul_J₂J₃_odd hp hp2 hK (mul_mem (hP hb) (hP hb)) (one_mem _)
    (mul_mem hc3 hc3) (one_mem _) e
  rcases (hA4 K hodd).1 b (hP hb) hb1 with rfl | rfl <;>
    rcases hI.eq_of_mem_spinJ₃_of_mul_self_odd hA4 hp hp2 hK hc3 hc1 with rfl | rfl
  · exact Or.inl (one_mul 1)
  · exact Or.inr (Or.inr (Or.inr (one_mul _)))
  · exact Or.inr (Or.inr (Or.inl (mul_one _)))
  · exact Or.inr (Or.inl (tSeven_mul_zt hp hp2 hK))

theorem center_sSyl_odd (hA4 : A4) (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (hP : P₂ ≤ spinJ₂ K) (hP2 : IsPGroup 2 P₂)
    (hPi : ¬ 2 ∣ P₂.relIndex (spinJ₂ K)) {x : spinGroup (quadOdd 3 K)} (hx : x ∈ sSyl i P₂)
    (hcent : ∀ y ∈ sSyl i P₂, x * y = y * x) : x = 1 ∨ x = spinZ K := by
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  obtain ⟨-, hz1, hzc, -⟩ := spinZ_facts hp hp2 hK
  obtain ⟨-, hcentP⟩ := (hA4 K hodd).2 P₂ hP hP2 hPi
  have hiS : i ∈ sSyl i P₂ := mem_sup_right (mem_zpowers i)
  obtain ⟨b, hb, rfl | rfl⟩ := mem_sSyl_odd hI hp hp2 hK hP hx
  · obtain ⟨b₂, hb₂, b₃, hb₃, rfl⟩ := exists_mul_of_mem_bSyl_odd hI hp hp2 hK hP hb
    have h2 : ∀ y ∈ P₂, b₂ * y = y * b₂ := by
      intro y hy
      have h := hcent y (mem_sup_left (mem_sup_left hy))
      have hy3 : b₃ * y = y * b₃ := (commute_P₂_pThree_odd hI hp hp2 hK hP y hy b₃ hb₃).symm
      have e : b₂ * y * b₃ = y * b₂ * b₃ := by
        calc b₂ * y * b₃ = b₂ * (b₃ * y) := by rw [hy3]; group
          _ = b₂ * b₃ * y := by group
          _ = y * (b₂ * b₃) := h
          _ = y * b₂ * b₃ := by group
      exact mul_right_cancel e
    have h3 : ∀ y ∈ pThree i P₂, b₃ * y = y * b₃ := by
      intro y hy
      have h := hcent y (mem_sup_left (mem_sup_right hy))
      have hy2 : b₂ * y = y * b₂ := commute_P₂_pThree_odd hI hp hp2 hK hP b₂ hb₂ y hy
      have e : b₂ * (b₃ * y) = b₂ * (y * b₃) := by
        calc b₂ * (b₃ * y) = b₂ * b₃ * y := by group
          _ = y * (b₂ * b₃) := h
          _ = (y * b₂) * b₃ := by group
          _ = (b₂ * y) * b₃ := by rw [hy2]
          _ = b₂ * (y * b₃) := by group
      exact mul_left_cancel e
    have hxi := hcent i hiS
    rcases hcentP b₂ (hP hb₂) h2 with rfl | rfl <;>
      rcases eq_of_commute_pThree_odd hA4 hI hp hp2 hK hP hP2 hPi
        (pThree_le_odd hI hp hp2 hK hP hb₃) h3 with rfl | rfl
    · exact Or.inl (one_mul 1)
    · exfalso
      rw [one_mul] at hxi
      have h' : i * (spinZ K * tSeven K) * i⁻¹ = spinZ K * tSeven K := by
        rw [← hxi, mul_inv_cancel_right]
      rw [hI.conj_zt hp hp2 hK] at h'
      apply hz1
      calc spinZ K = spinZ K * tSeven K * (tSeven K)⁻¹ := by group
        _ = 1 := by rw [← h']; group
    · exfalso
      rw [mul_one] at hxi
      exact hI.not_commute_t hp hp2 hK hxi.symm
    · exact Or.inr (tSeven_mul_zt hp hp2 hK)
  · exfalso
    have ht : tSeven K ∈ sSyl i P₂ :=
      mem_sup_left (mem_sup_left (tSeven_mem_P₂ hA4 hp hp2 hK hP hP2 hPi))
    have h := hcent _ ht
    have hbt : b * tSeven K = tSeven K * b :=
      mem_centralizer_singleton_iff.mp (mem_inf.mp (bSyl_le_ct_odd hI hp hp2 hK hP hb)).1
    have hbz' : b * spinZ K * b⁻¹ = spinZ K := by
      rw [mem_center_iff.mp hzc b, mul_inv_cancel_right]
    have hbt' : b * tSeven K * b⁻¹ = tSeven K := by rw [hbt, mul_inv_cancel_right]
    have e : spinZ K * tSeven K = tSeven K := by
      calc spinZ K * tSeven K = (b * spinZ K * b⁻¹) * (b * tSeven K * b⁻¹) := by rw [hbz', hbt']
        _ = b * (spinZ K * tSeven K) * b⁻¹ := by group
        _ = b * (i * tSeven K * i⁻¹) * b⁻¹ := by rw [hI.conj_t]
        _ = (b * i) * tSeven K * (b * i)⁻¹ := by group
        _ = tSeven K := by rw [h, mul_inv_cancel_right]
    exact hz1 (mul_right_cancel (e.trans (one_mul _).symm))

theorem conj_i_sSyl_odd (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (hP : P₂ ≤ spinJ₂ K)
    {w : spinGroup (quadOdd 3 K)} (hw : w ∈ sSyl i P₂) (hwB : w ∉ bSyl i P₂)
    (hww : w * w = 1) : ∃ s ∈ sSyl i P₂, s * i * s⁻¹ = w := by
  have hodd' := odd_card_spin hp hp2 hK
  obtain ⟨b, hb, rfl | rfl⟩ := mem_sSyl_odd hI hp hp2 hK hP hw
  · exact absurd hb hwB
  obtain ⟨b₂, hb₂, b₃, hb₃, rfl⟩ := exists_mul_of_mem_bSyl_odd hI hp hp2 hK hP hb
  have hb₂J := hP hb₂
  have hb₃J := pThree_le_odd hI hp hp2 hK hP hb₃
  have hinv : i * (b₂ * b₃) * i⁻¹ = (b₂ * b₃)⁻¹ := by
    have e : (b₂ * b₃) * i * ((b₂ * b₃) * i) = 1 := hww
    rw [hI.inv_eq]
    calc i * (b₂ * b₃) * i = (b₂ * b₃)⁻¹ * ((b₂ * b₃) * i * ((b₂ * b₃) * i)) := by group
      _ = (b₂ * b₃)⁻¹ := by rw [e, mul_one]
  have h23 : i * b₂ * i⁻¹ ∈ spinJ₃ K := hI.conj_mem_spinJ₃_odd hp hp2 hK hb₂J
  have h32 : i * b₃ * i⁻¹ ∈ spinJ₂ K := hI.conj_mem_spinJ₂_odd hp hp2 hK hb₃J
  have e3 : (i * b₃ * i⁻¹) * (i * b₂ * i⁻¹) = b₂⁻¹ * b₃⁻¹ := by
    calc (i * b₃ * i⁻¹) * (i * b₂ * i⁻¹) = (i * b₂ * i⁻¹) * (i * b₃ * i⁻¹) :=
          commute_spinJ₂_spinJ₃_odd hodd' h32 h23
      _ = i * (b₂ * b₃) * i⁻¹ := by group
      _ = (b₂ * b₃)⁻¹ := hinv
      _ = b₃⁻¹ * b₂⁻¹ := mul_inv_rev _ _
      _ = b₂⁻¹ * b₃⁻¹ := (commute_spinJ₂_spinJ₃_odd hodd' (inv_mem hb₂J) (inv_mem hb₃J)).symm
  obtain ⟨-, h3⟩ := eq_of_mul_eq_mul_J₂J₃_odd hp hp2 hK h32 (inv_mem hb₂J) h23 (inv_mem hb₃J) e3
  refine ⟨b₂, mem_sup_left (mem_sup_left hb₂), ?_⟩
  have hb₃' : b₃ = (i * b₂ * i⁻¹)⁻¹ := by rw [h3, inv_inv]
  rw [hb₃']
  group

theorem sqrt_bSyl_odd (hA4 : A4) (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (hP : P₂ ≤ spinJ₂ K) (hP2 : IsPGroup 2 P₂)
    (hPi : ¬ 2 ∣ P₂.relIndex (spinJ₂ K)) :
    (sqrtSet (bSyl i P₂) (spinZ K)).ncard ≠ (sqrtSet (bSyl i P₂) (spinZ K * tSeven K)).ncard := by
  have := finite_spinSeven (two_ne_zero_spin hp hp2 hK)
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  obtain ⟨-, -, hzc, htt, ht1, -, -, ht2J, hzt3J, -⟩ := spinZ_facts hp hp2 hK
  obtain ⟨⟨a, ha, b, hb, haa, hbb, hab⟩, -⟩ := (hA4 K hodd).2 P₂ hP hP2 hPi
  have htP := tSeven_mem_P₂ hA4 hp hp2 hK hP hP2 hPi
  have hinj : Set.InjOn (fun pr : spinGroup (quadOdd 3 K) × spinGroup (quadOdd 3 K) =>
      pr.1 * pr.2) ((P₂ : Set (spinGroup (quadOdd 3 K))) ×ˢ (pThree i P₂ : Set _)) := by
    rintro ⟨b₁, c₁⟩ ⟨hb₁, hc₁⟩ ⟨b₂, c₂⟩ ⟨hb₂, hc₂⟩ h
    obtain ⟨e1, e2⟩ := eq_of_mul_eq_mul_J₂J₃_odd hp hp2 hK (hP hb₁) (hP hb₂)
      (pThree_le_odd hI hp hp2 hK hP hc₁) (pThree_le_odd hI hp hp2 hK hP hc₂) h
    exact Prod.ext e1 e2
  have hsq : ∀ {x c' d' : spinGroup (quadOdd 3 K)}, x ∈ bSyl i P₂ → c' ∈ spinJ₂ K →
      d' ∈ spinJ₃ K → x * x = c' * d' →
      ∃ b₂ ∈ P₂, ∃ b₃ ∈ pThree i P₂, x = b₂ * b₃ ∧ b₂ * b₂ = c' ∧ b₃ * b₃ = d' := by
    intro x c' d' hx hc' hd' hxx
    obtain ⟨b₂, hb₂, b₃, hb₃, rfl⟩ := exists_mul_of_mem_bSyl_odd hI hp hp2 hK hP hx
    have hb₃J := pThree_le_odd hI hp hp2 hK hP hb₃
    have e : b₂ * b₂ * (b₃ * b₃) = c' * d' := by
      rw [← mul_mul_self_of_commute (commute_P₂_pThree_odd hI hp hp2 hK hP b₂ hb₂ b₃ hb₃), hxx]
    obtain ⟨e1, e2⟩ := eq_of_mul_eq_mul_J₂J₃_odd hp hp2 hK (mul_mem (hP hb₂) (hP hb₂)) hc'
      (mul_mem hb₃J hb₃J) hd' e
    exact ⟨b₂, hb₂, b₃, hb₃, rfl, e1, e2⟩
  have hprod : ∀ {b₂ b₃ : spinGroup (quadOdd 3 K)}, b₂ ∈ P₂ → b₃ ∈ pThree i P₂ →
      b₂ * b₃ * (b₂ * b₃) = b₂ * b₂ * (b₃ * b₃) := fun hb₂ hb₃ =>
    mul_mul_self_of_commute (commute_P₂_pThree_odd hI hp hp2 hK hP _ hb₂ _ hb₃)
  have hz : sqrtSet (bSyl i P₂) (spinZ K) =
      (fun pr : spinGroup (quadOdd 3 K) × spinGroup (quadOdd 3 K) => pr.1 * pr.2) ''
        (sqrtSet P₂ (tSeven K) ×ˢ sqrtSet (pThree i P₂) (spinZ K * tSeven K)) := by
    ext x
    constructor
    · rintro ⟨hx, hxx⟩
      rw [← tSeven_mul_zt hp hp2 hK] at hxx
      obtain ⟨b₂, hb₂, b₃, hb₃, rfl, e1, e2⟩ := hsq hx ht2J hzt3J hxx
      exact ⟨(b₂, b₃), ⟨⟨hb₂, e1⟩, ⟨hb₃, e2⟩⟩, rfl⟩
    · rintro ⟨⟨b₂, b₃⟩, ⟨⟨hb₂, e1⟩, ⟨hb₃, e2⟩⟩, rfl⟩
      refine ⟨mul_mem (mem_sup_left hb₂) (mem_sup_right hb₃), ?_⟩
      show b₂ * b₃ * (b₂ * b₃) = spinZ K
      rw [hprod hb₂ hb₃, e1, e2, tSeven_mul_zt hp hp2 hK]
  have hzt : sqrtSet (bSyl i P₂) (spinZ K * tSeven K) =
      (fun pr : spinGroup (quadOdd 3 K) × spinGroup (quadOdd 3 K) => pr.1 * pr.2) ''
        (sqrtSet P₂ 1 ×ˢ sqrtSet (pThree i P₂) (spinZ K * tSeven K)) := by
    ext x
    constructor
    · rintro ⟨hx, hxx⟩
      rw [← one_mul (spinZ K * tSeven K)] at hxx
      obtain ⟨b₂, hb₂, b₃, hb₃, rfl, e1, e2⟩ := hsq hx (one_mem _) hzt3J hxx
      exact ⟨(b₂, b₃), ⟨⟨hb₂, e1⟩, ⟨hb₃, e2⟩⟩, rfl⟩
    · rintro ⟨⟨b₂, b₃⟩, ⟨⟨hb₂, e1⟩, ⟨hb₃, e2⟩⟩, rfl⟩
      refine ⟨mul_mem (mem_sup_left hb₂) (mem_sup_right hb₃), ?_⟩
      show b₂ * b₃ * (b₂ * b₃) = spinZ K * tSeven K
      rw [hprod hb₂ hb₃, e1, e2, one_mul]
  have hA₂ : sqrtSet P₂ (tSeven K) ⊆ (P₂ : Set (spinGroup (quadOdd 3 K))) := fun _ h => h.1
  have hA₃ : sqrtSet (pThree i P₂) (spinZ K * tSeven K) ⊆
      (pThree i P₂ : Set (spinGroup (quadOdd 3 K))) := fun _ h => h.1
  have hT₂ : sqrtSet P₂ 1 ⊆ (P₂ : Set (spinGroup (quadOdd 3 K))) := fun _ h => h.1
  rw [hz, hzt, (hinj.mono (Set.prod_mono hA₂ hA₃)).ncard_image,
    (hinj.mono (Set.prod_mono hT₂ hA₃)).ncard_image, Set.ncard_prod, Set.ncard_prod]
  have hT₂eq : sqrtSet P₂ 1 = {1, tSeven K} := by
    ext x
    constructor
    · rintro ⟨hx, hxx⟩
      rcases (hA4 K hodd).1 x (hP hx) hxx with h | h
      · exact Or.inl h
      · exact Or.inr h
    · rintro (rfl | rfl)
      · exact ⟨one_mem _, one_mul 1⟩
      · exact ⟨htP, htt⟩
  have hT₂c : (sqrtSet P₂ 1).ncard = 2 := by
    rw [hT₂eq]
    exact Set.ncard_pair (Ne.symm ht1)
  have ha1 : a ≠ a⁻¹ := by
    intro h
    apply ht1
    rw [← haa]
    calc a * a = a * a⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel a
  have hab' : a ≠ b := fun h => hab (by rw [h])
  have hab'' : a⁻¹ ≠ b := by
    intro h
    apply hab
    rw [← h, mul_inv_cancel, inv_mul_cancel]
  have hA₂c : 3 ≤ (sqrtSet P₂ (tSeven K)).ncard := by
    have hsub : ({a, a⁻¹, b} : Set (spinGroup (quadOdd 3 K))) ⊆ sqrtSet P₂ (tSeven K) := by
      rintro _ (rfl | rfl | rfl)
      · exact ⟨ha, haa⟩
      · refine ⟨inv_mem ha, ?_⟩
        rw [← mul_inv_rev, haa]
        exact inv_eq_of_mul_eq_one_right htt
      · exact ⟨hb, hbb⟩
    calc 3 = ({a, a⁻¹, b} : Set (spinGroup (quadOdd 3 K))).ncard :=
          (Set.ncard_eq_three.mpr ⟨a, a⁻¹, b, ha1, hab', hab'', rfl⟩).symm
      _ ≤ _ := Set.ncard_le_ncard hsub
  have hA₃c : 0 < (sqrtSet (pThree i P₂) (spinZ K * tSeven K)).ncard := by
    refine (Set.ncard_pos (Set.toFinite _)).mpr ⟨i * a * i⁻¹, conj_mem_pThree ha, ?_⟩
    calc i * a * i⁻¹ * (i * a * i⁻¹) = i * (a * a) * i⁻¹ := by group
      _ = spinZ K * tSeven K := by rw [haa, hI.conj_t]
  rw [hT₂c]
  intro h
  have h' : (sqrtSet P₂ (tSeven K)).ncard * (sqrtSet (pThree i P₂) (spinZ K * tSeven K)).ncard ≤
      2 * (sqrtSet (pThree i P₂) (spinZ K * tSeven K)).ncard := h.le
  have := Nat.le_of_mul_le_mul_right h' hA₃c
  omega

abbrev dP_odd (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    (P₂ : Subgroup (spinGroup (quadOdd 3 K))) :
    Subgroup (spinGroup (quadOdd 3 K)) :=
  (P₂.subgroupOf (spinJ₂ K)).map (hI.diagOdd hp hp2 hK)

theorem dP_le_bSyl_odd (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) : dP_odd hI hp hp2 hK P₂ ≤ bSyl i P₂ := by
  rintro _ ⟨b, hb, rfl⟩
  rw [IsIBar.diagOdd_apply]
  exact mul_mem (mem_sup_left (mem_subgroupOf.mp hb)) (mem_sup_right (conj_mem_pThree
    (mem_subgroupOf.mp hb)))

theorem card_dP_odd (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (hP : P₂ ≤ spinJ₂ K) :
    Nat.card ↥(dP_odd hI hp hp2 hK P₂) = Nat.card P₂ := by
  rw [card_map_of_injective (hI.injective_diagOdd hp hp2 hK)]
  exact Nat.card_congr (subgroupOfEquivOfLe hP).toEquiv

theorem bSyl_inf_le_dP_odd (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (hP : P₂ ≤ spinJ₂ K) :
    bSyl i P₂ ⊓ centralizer ({i} : Set (spinGroup (quadOdd 3 K))) ≤
    dP_odd hI hp hp2 hK P₂ := by
  have hodd' := odd_card_spin hp hp2 hK
  intro x hx
  obtain ⟨hxB, hxi⟩ := mem_inf.mp hx
  obtain ⟨b₂, hb₂, b₃, hb₃, rfl⟩ := exists_mul_of_mem_bSyl_odd hI hp hp2 hK hP hxB
  have hb₂J := hP hb₂
  have hb₃J := pThree_le_odd hI hp hp2 hK hP hb₃
  have hfix : i * (b₂ * b₃) * i⁻¹ = b₂ * b₃ := by
    rw [← mem_centralizer_singleton_iff.mp hxi, mul_inv_cancel_right]
  have h23 : i * b₂ * i⁻¹ ∈ spinJ₃ K := hI.conj_mem_spinJ₃_odd hp hp2 hK hb₂J
  have h32 : i * b₃ * i⁻¹ ∈ spinJ₂ K := hI.conj_mem_spinJ₂_odd hp hp2 hK hb₃J
  have e : (i * b₃ * i⁻¹) * (i * b₂ * i⁻¹) = b₂ * b₃ := by
    calc (i * b₃ * i⁻¹) * (i * b₂ * i⁻¹) = (i * b₂ * i⁻¹) * (i * b₃ * i⁻¹) :=
          commute_spinJ₂_spinJ₃_odd hodd' h32 h23
      _ = i * (b₂ * b₃) * i⁻¹ := by group
      _ = b₂ * b₃ := hfix
  obtain ⟨-, h3⟩ := eq_of_mul_eq_mul_J₂J₃_odd hp hp2 hK h32 hb₂J h23 hb₃J e
  refine ⟨⟨b₂, hb₂J⟩, mem_subgroupOf.mpr hb₂, ?_⟩
  rw [IsIBar.diagOdd_apply]
  show b₂ * (i * b₂ * i⁻¹) = b₂ * b₃
  rw [h3]

theorem card_inf_ne_odd (hA4 : A4) (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (hP : P₂ ≤ spinJ₂ K) (hP2 : IsPGroup 2 P₂)
    (hPi : ¬ 2 ∣ P₂.relIndex (spinJ₂ K)) :
    Nat.card ↥(sSyl i P₂ ⊓ centralizer ({i} : Set (spinGroup (quadOdd 3 K)))) ≠
    Nat.card ↥(bSyl i P₂) := by
  have := finite_spinSeven (two_ne_zero_spin hp hp2 hK)
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  obtain ⟨-, -, -, -, ht1, -⟩ := spinZ_facts hp hp2 hK
  obtain ⟨⟨a, ha, b, hb, haa, -, hab⟩, -⟩ := (hA4 K hodd).2 P₂ hP hP2 hPi
  have h1 : (bSyl i P₂).relIndex (sSyl i P₂ ⊓ centralizer ({i} : Set (spinGroup (quadOdd 3 K))))
      ≤ 2 := by
    calc (bSyl i P₂).relIndex (sSyl i P₂ ⊓ centralizer ({i} : Set (spinGroup (quadOdd 3 K))))
        ≤ (bSyl i P₂).relIndex (sSyl i P₂) := relIndex_le_of_le_right inf_le_left
          (by rw [relIndex_bSyl_odd hI hp hp2 hK hP]; norm_num)
      _ = 2 := relIndex_bSyl_odd hI hp hp2 hK hP
  have h2 := Subgroup.relIndex_mul_card (H := bSyl i P₂)
    (K := sSyl i P₂ ⊓ centralizer ({i} : Set (spinGroup (quadOdd 3 K))))
  have hBC : bSyl i P₂ ⊓ (sSyl i P₂ ⊓ centralizer ({i} : Set (spinGroup (quadOdd 3 K)))) ≤
      dP_odd hI hp hp2 hK P₂ := by
    intro x hx
    obtain ⟨hxB, hxC⟩ := mem_inf.mp hx
    exact bSyl_inf_le_dP_odd hI hp hp2 hK hP (mem_inf.mpr ⟨hxB, (mem_inf.mp hxC).2⟩)
  have h3 : Nat.card ↥(bSyl i P₂ ⊓ (sSyl i P₂ ⊓ centralizer ({i} :
      Set (spinGroup (quadOdd 3 K))))) ≤ Nat.card P₂ :=
    (card_le_of_le hBC).trans (card_dP_odd hI hp hp2 hK hP).le
  have hP3 : 3 ≤ Nat.card P₂ := by
    have ha1 : (1 : spinGroup (quadOdd 3 K)) ≠ a := by
      intro h
      apply ht1
      rw [← haa, ← h, one_mul]
    have hb1 : (1 : spinGroup (quadOdd 3 K)) ≠ b := by
      intro h
      apply hab
      rw [← h, one_mul, mul_one]
    have hab' : a ≠ b := fun h => hab (by rw [h])
    have hsub : ({1, a, b} : Set (spinGroup (quadOdd 3 K))) ⊆ (P₂ : Set _) := by
      rintro _ (rfl | rfl | rfl)
      · exact one_mem _
      · exact ha
      · exact hb
    calc 3 = ({1, a, b} : Set (spinGroup (quadOdd 3 K))).ncard :=
          (Set.ncard_eq_three.mpr ⟨1, a, b, ha1, hb1, hab', rfl⟩).symm
      _ ≤ (P₂ : Set (spinGroup (quadOdd 3 K))).ncard := Set.ncard_le_ncard hsub
      _ = Nat.card P₂ := (Nat.card_coe_set_eq _).symm
  rw [card_bSyl_odd hI hp hp2 hK hP]
  intro h
  have key : Nat.card P₂ * Nat.card P₂ ≤ 2 * Nat.card P₂ := by
    calc Nat.card P₂ * Nat.card P₂ =
        Nat.card ↥(sSyl i P₂ ⊓ centralizer ({i} : Set (spinGroup (quadOdd 3 K)))) := h.symm
      _ = _ := h2.symm
      _ ≤ 2 * Nat.card P₂ := Nat.mul_le_mul h1 h3
  have := Nat.le_of_mul_le_mul_right key (by omega)
  omega

theorem spinZ_mem_commutator_dP_odd (hA4 : A4) (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (hP : P₂ ≤ spinJ₂ K) (hP2 : IsPGroup 2 P₂)
    (hPi : ¬ 2 ∣ P₂.relIndex (spinJ₂ K)) :
    spinZ K ∈ ⁅dP_odd hI hp hp2 hK P₂, dP_odd hI hp hp2 hK P₂⁆ := by
  have := finite_spinSeven (two_ne_zero_spin hp hp2 hK)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  obtain ⟨-, -, hzc, htt, -, -, -, ht2J, -⟩ := spinZ_facts hp hp2 hK
  obtain ⟨⟨a, ha, b, hb, -, -, hab⟩, -⟩ := (hA4 K hodd).2 P₂ hP hP2 hPi
  have hCle : ⁅P₂, P₂⁆ ≤ P₂ := commutator_le.mpr fun g₁ h₁ g₂ h₂ => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)
  have hCp : IsPGroup 2 ↥⁅P₂, P₂⁆ := hP2.to_le hCle
  have hab1 : ⁅a, b⁆ ≠ 1 := fun h => hab (commutatorElement_eq_one_iff_mul_comm.mp h)
  have hC1 : Nat.card ↥⁅P₂, P₂⁆ ≠ 1 := by
    rw [Ne, Subgroup.card_eq_one]
    intro h
    have hm := commutator_mem_commutator ha hb
    rw [h, mem_bot] at hm
    exact hab1 hm
  have hC2 : 2 ∣ Nat.card ↥⁅P₂, P₂⁆ := hCp.card_eq_or_dvd.resolve_left hC1
  have : Fintype ↥⁅P₂, P₂⁆ := Fintype.ofFinite _
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card (G := ↥⁅P₂, P₂⁆) 2
    (by rwa [← Nat.card_eq_fintype_card])
  have hy' : orderOf (y : spinGroup (quadOdd 3 K)) = 2 := by rw [Subgroup.orderOf_coe, hy]
  have hyy : (y : spinGroup (quadOdd 3 K)) * y = 1 := by
    have h := pow_orderOf_eq_one (y : spinGroup (quadOdd 3 K))
    rwa [hy', pow_two] at h
  have hy1 : (y : spinGroup (quadOdd 3 K)) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hy'
    exact absurd hy' (by norm_num)
  have hyt : (y : spinGroup (quadOdd 3 K)) = tSeven K :=
    ((hA4 K hodd).1 _ (hP (hCle y.2)) hyy).resolve_left hy1
  have htC : tSeven K ∈ ⁅P₂, P₂⁆ := hyt ▸ y.2
  have hP'map : (P₂.subgroupOf (spinJ₂ K)).map (spinJ₂ K).subtype = P₂ := by
    rw [subgroupOf_map_subtype, inf_of_le_left hP]
  have htC' : (⟨tSeven K, ht2J⟩ : ↥(spinJ₂ K)) ∈
      ⁅P₂.subgroupOf (spinJ₂ K), P₂.subgroupOf (spinJ₂ K)⁆ := by
    have h : tSeven K ∈ (⁅P₂.subgroupOf (spinJ₂ K), P₂.subgroupOf (spinJ₂ K)⁆).map
        (spinJ₂ K).subtype := by
      rw [Subgroup.map_commutator, hP'map]
      exact htC
    obtain ⟨y', hy', hy't⟩ := h
    have : y' = ⟨tSeven K, ht2J⟩ := Subtype.ext hy't
    rw [← this]
    exact hy'
  have hz : spinZ K = hI.diagOdd hp hp2 hK ⟨tSeven K, ht2J⟩ := by
    rw [IsIBar.diagOdd_apply]
    show spinZ K = tSeven K * (i * tSeven K * i⁻¹)
    rw [hI.conj_t, tSeven_mul_zt hp hp2 hK]
  rw [hz]
  show hI.diagOdd hp hp2 hK ⟨tSeven K, ht2J⟩ ∈
    ⁅(P₂.subgroupOf (spinJ₂ K)).map (hI.diagOdd hp hp2 hK),
      (P₂.subgroupOf (spinJ₂ K)).map (hI.diagOdd hp hp2 hK)⁆
  rw [← Subgroup.map_commutator]
  exact ⟨_, htC', rfl⟩

theorem dP_le_centralizer_odd (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) : dP_odd hI hp hp2 hK P₂ ≤
    centralizer ({i} : Set (spinGroup (quadOdd 3 K))) :=
  (map_le_range _ _).trans (hI.dTwoThreeOdd_le_centralizer_i hp hp2 hK)

end A4

theorem sSyl_le_mX_odd (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    (hP : P₂ ≤ spinJ₂ K) : sSyl i P₂ ≤ mX K :=
  sup_le ((bSyl_le_ct_odd hI hp hp2 hK hP).trans (centralizer_inf_le_mX hp hp2 hK))
    (zpowers_le.mpr (hI.mem_mX hp hp2 hK))

theorem odd_relIndex_mX_odd (hF1 : F1Odd) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) : Odd ((mX K).relIndex (centQThree K)) := by
  have := finite_spinSeven (two_ne_zero_spin hp hp2 hK)
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  obtain ⟨-, hle⟩ := hF1 K hodd
  have hKn : ∀ y ∈ centQThree K, ∀ k ∈ oddQThree K, y * k * y⁻¹ ∈ oddQThree K :=
    fun _ hy _ hk => CFSG.Walter.conj_mem_map_of_characteristic (le_normalizer hy) hk
  have hMN : mX K ≤ normalizer (oddQThree K : Set (spinGroup (quadOdd 3 K))) :=
    le_normalizer_of_conj_mem hKn inf_le_left
  have hcard := card_sup_mul_card_inf_of_le_normalizer' hMN
  have hsup : oddQThree K ⊔ mX K = centQThree K :=
    le_antisymm (sup_le (map_subtype_le _) inf_le_left) hle
  rw [hsup] at hcard
  have hidx := Subgroup.relIndex_mul_card (H := mX K) (K := centQThree K)
  rw [inf_of_le_left (inf_le_left : mX K ≤ centQThree K)] at hidx
  have hK₃ : Odd (Nat.card ↥(oddQThree K)) := by
    rw [card_map_of_injective (subtype_injective _)]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hdvd : (mX K).relIndex (centQThree K) ∣ Nat.card ↥(oddQThree K) := by
    refine ⟨Nat.card ↥(oddQThree K ⊓ mX K), ?_⟩
    have hpos : 0 < Nat.card ↥(mX K) := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc Nat.card ↥(oddQThree K) * Nat.card ↥(mX K) =
        Nat.card ↥(centQThree K) * Nat.card ↥(oddQThree K ⊓ mX K) := hcard.symm
      _ = (mX K).relIndex (centQThree K) * Nat.card ↥(mX K) *
          Nat.card ↥(oddQThree K ⊓ mX K) := by rw [hidx]
      _ = (mX K).relIndex (centQThree K) * Nat.card ↥(oddQThree K ⊓ mX K) *
          Nat.card ↥(mX K) := by ring
  exact Odd.of_dvd_nat hK₃ hdvd

theorem odd_relIndex_sSyl_odd (hA2 : A2) (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (hP : P₂ ≤ spinJ₂ K)
    (hPi : ¬ 2 ∣ P₂.relIndex (spinJ₂ K)) : Odd ((sSyl i P₂).relIndex (mX K)) := by
  have := finite_spinSeven (two_ne_zero_spin hp hp2 hK)
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  have hm : Odd (P₂.relIndex (spinJ₂ K)) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hPi)
  have h1 := Subgroup.relIndex_mul_card (H := sSyl i P₂) (K := mX K)
  rw [inf_of_le_left (sSyl_le_mX_odd hI hp hp2 hK hP), card_sSyl_odd hI hp hp2 hK hP,
    card_bSyl_odd hI hp hp2 hK hP, hI.card_mX hp hp2 hK, card_centralizer_inf_odd hA2 hp hp2 hK]
    at h1
  have h2 := Subgroup.relIndex_mul_card (H := P₂) (K := spinJ₂ K)
  rw [inf_of_le_left hP] at h2
  have hJ23 : Nat.card ↥(spinJ₃ K) = Nat.card ↥(spinJ₂ K) := by rw [card_spinJ₂, card_spinJ₃]
  rw [hJ23, ← h2] at h1
  have hn : 0 < Nat.card P₂ := Nat.card_pos
  have key : (sSyl i P₂).relIndex (mX K) * (Nat.card P₂ * Nat.card P₂ * 2) =
      (P₂.relIndex (spinJ₂ K) * P₂.relIndex (spinJ₂ K) * Nat.card K) *
        (Nat.card P₂ * Nat.card P₂ * 2) := by
    rw [h1]
    ring
  have hr := Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (Nat.mul_pos hn hn) (by norm_num)) key
  rw [hr]
  exact (hm.mul hm).mul hodd

theorem sylowFacts_of_odd (hF1 : F1Odd) (hA2 : A2) (hA4 : A4) (hI : IsIBar K i) (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (hP : P₂ ≤ spinJ₂ K)
    (hP2 : IsPGroup 2 P₂) (hPi : ¬ 2 ∣ P₂.relIndex (spinJ₂ K)) :
    SylowFacts K i (sSyl i P₂) (bSyl i P₂) := by
  have := finite_spinSeven (two_ne_zero_spin hp hp2 hK)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htP := tSeven_mem_P₂ hA4 hp hp2 hK hP hP2 hPi
  have hiZ : IsPGroup 2 ↥(zpowers i) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hI.orderOf_eq hp hp2 hK, pow_one])
  have hB2 : IsPGroup 2 ↥(bSyl i P₂) := hP2.to_sup_of_normal_right' (hP2.map _)
    (le_normalizer_of_conj_mem (fun b hb c hc => by
      rw [commute_P₂_pThree_odd hI hp hp2 hK hP b hb c hc, mul_inv_cancel_right]
      exact hc) le_rfl)
  refine ⟨?_, ?_, ?_, le_sup_left, relIndex_bSyl_odd hI hp hp2 hK hP,
    mem_sup_right (mem_zpowers i), mem_sup_left htP, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    exact hB2.to_sup_of_normal_left' hiZ (zpowers_le.mpr (mem_normalizer_bSyl_odd hI hp hp2 hK hP))
  ·
    exact (sSyl_le_mX_odd hI hp hp2 hK hP).trans inf_le_left
  ·
    rw [← Subgroup.relIndex_mul_relIndex _ _ _ (sSyl_le_mX_odd hI hp hp2 hK hP) inf_le_left]
    exact Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp ((odd_relIndex_sSyl_odd hA2 hI hp hp2 hK hP
      hPi).mul (odd_relIndex_mX_odd hF1 hp hp2 hK)))
  ·
    rw [← tSeven_mul_zt hp hp2 hK, ← hI.conj_t]
    exact mul_mem (mem_sup_left htP) (mem_sup_right (conj_mem_pThree htP))
  ·
    intro x hx
    exact (mem_centralizer_singleton_iff.mp (mem_inf.mp (bSyl_le_ct_odd hI hp hp2 hK hP hx)).1).symm
  · exact fun x hx hcent => center_sSyl_odd hA4 hI hp hp2 hK hP hP2 hPi hx hcent
  · exact fun x hx hxx => involutions_bSyl_odd hA4 hI hp hp2 hK hP hx hxx
  · exact sqrt_bSyl_odd hA4 hI hp hp2 hK hP hP2 hPi
  · exact fun w hw hwB hww => conj_i_sSyl_odd hI hp hp2 hK hP hw hwB hww
  ·
    rw [commutator_le]
    intro g₁ h₁ g₂ h₂
    have e : ⁅g₁, g₂⁆ = (g₁ * g₁) * ((g₁⁻¹ * g₂) * (g₁⁻¹ * g₂)) * (g₂⁻¹ * g₂⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact mul_mem (mul_mem (mul_self_mem_bSyl_odd hI hp hp2 hK hP h₁)
      (mul_self_mem_bSyl_odd hI hp hp2 hK hP (mul_mem (inv_mem h₁) h₂)))
      (mul_self_mem_bSyl_odd hI hp hp2 hK hP (inv_mem h₂))
  ·
    exact ⟨dP_odd hI hp hp2 hK P₂, le_inf ((dP_le_bSyl_odd hI hp hp2 hK).trans le_sup_left)
      (dP_le_centralizer_odd hI hp hp2 hK), spinZ_mem_commutator_dP_odd hA4 hI hp hp2 hK hP hP2 hPi⟩
  · exact card_inf_ne_odd hA4 hI hp hp2 hK hP hP2 hPi

theorem exists_sylowFacts_odd (hF1 : F1Odd) (hA2 : A2) (hA4 : A4) (hI : IsIBar K i) (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) :
    ∃ S₀ B : Subgroup (spinGroup (quadOdd 3 K)), SylowFacts K i S₀ B := by
  have := finite_spinSeven (two_ne_zero_spin hp hp2 hK)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥(spinJ₂ K)) := inferInstance
  have hPi : ¬ 2 ∣ ((P : Subgroup ↥(spinJ₂ K)).map (spinJ₂ K).subtype).relIndex (spinJ₂ K) := by
    have e : ((P : Subgroup ↥(spinJ₂ K)).map (spinJ₂ K).subtype).subgroupOf (spinJ₂ K) =
        (P : Subgroup ↥(spinJ₂ K)) :=
      comap_map_eq_self_of_injective (spinJ₂ K).subtype_injective _
    show ¬ 2 ∣ (((P : Subgroup ↥(spinJ₂ K)).map (spinJ₂ K).subtype).subgroupOf (spinJ₂ K)).index
    rw [e]
    exact P.not_dvd_index
  exact ⟨_, _, sylowFacts_of_odd hF1 hA2 hA4 hI hp hp2 hK (map_subtype_le _) (P.isPGroup'.map _)
    hPi⟩

end Sylow

end CFSG.ComponentClassification.HarrisLit.T1.S74
