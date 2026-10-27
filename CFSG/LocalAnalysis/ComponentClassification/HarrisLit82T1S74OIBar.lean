module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74OBasic
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74XIBar
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74ThreeComp

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open CFSG Subgroup CFSG.LieType.Universal.Spin
open scoped MatrixGroups

section Model

variable {K : Type} [Field K] [Finite K] {p f : ℕ}

theorem map_conj_spinJ_odd (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    {g : spinGroup (quadOdd 3 K)}
    (hg : g ∈ normalizer (centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))) :
      Set (spinGroup (quadOdd 3 K))))
    {J : Subgroup (spinGroup (quadOdd 3 K))} (hJ : J = spinJ₁ K ∨ J = spinJ₂ K ∨ J = spinJ₃ K) :
    ∃ J' : Subgroup (spinGroup (quadOdd 3 K)), (J' = spinJ₁ K ∨ J' = spinJ₂ K ∨ J' = spinJ₃ K) ∧
      J.map (MulAut.conj g).toMonoidHom = J' := by
  have := finite_spinSeven (two_ne_zero_spin hp hp2 hK)
  obtain ⟨J', hJ', h⟩ := map_conj_spinJ hp hp2 hK (φ := MonoidHom.id (spinGroup (quadOdd 3 K)))
    (D := centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K)))) (fun _ _ h => h)
    (Subgroup.map_id _).le
    (fun d hd x hx => by
      rw [Subgroup.map_id] at hx ⊢
      exact mul_mem (mul_mem hd hx) (inv_mem hd))
    (by rw [Subgroup.map_id, Subgroup.relIndex_self]; exact odd_one) hg hJ
  simp only [Subgroup.map_id] at h
  exact ⟨J', hJ', h⟩

end Model

namespace IsIBar

variable {K : Type} [Field K] [Finite K] {p f : ℕ} {i : spinGroup (quadOdd 3 K)}

theorem mem_normalizer_centralizer_t (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    i ∈ normalizer (centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))) :
      Set (spinGroup (quadOdd 3 K))) :=
  mem_normalizer_of_involution hI.mul_self fun _ hx => hI.conj_mem_centralizer_t hp hp2 hK hx

theorem map_spinJ₂_odd (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) : (spinJ₂ K).map (MulAut.conj i).toMonoidHom = spinJ₃ K := by
  obtain ⟨hzz, -, hzc, -, -, htc, -, ht2J, hzt3J, -⟩ := spinZ_facts hp hp2 hK
  have hzt1 : spinZ K * tSeven K ≠ 1 := fun h => htc (by
    have e : tSeven K = spinZ K := by
      calc tSeven K = (spinZ K)⁻¹ := eq_inv_of_mul_eq_one_right h
        _ = spinZ K := inv_eq_of_mul_eq_one_right hzz
    rw [e]
    exact hzc)
  have hmem : spinZ K * tSeven K ∈ (spinJ₂ K).map (MulAut.conj i).toMonoidHom :=
    ⟨tSeven K, ht2J, hI.conj_t⟩
  obtain ⟨J', hJ', h⟩ := map_conj_spinJ_odd hp hp2 hK (hI.mem_normalizer_centralizer_t hp hp2 hK)
    (Or.inr (Or.inl rfl))
  rw [h] at hmem ⊢
  rcases hJ' with rfl | rfl | rfl
  · exact absurd ((spinJ_inf_eq_one_odd hp hp2 hK).2.1 hmem hzt3J) hzt1
  · exact absurd ((spinJ_inf_eq_one_odd hp hp2 hK).2.2 hmem hzt3J) hzt1
  · rfl

theorem map_spinJ₃_odd (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) : (spinJ₃ K).map (MulAut.conj i).toMonoidHom = spinJ₂ K := by
  obtain ⟨-, -, -, -, ht1, -, -, ht2J, hzt3J, -⟩ := spinZ_facts hp hp2 hK
  have hmem : tSeven K ∈ (spinJ₃ K).map (MulAut.conj i).toMonoidHom :=
    ⟨spinZ K * tSeven K, hzt3J, hI.conj_zt hp hp2 hK⟩
  obtain ⟨J', hJ', h⟩ := map_conj_spinJ_odd hp hp2 hK (hI.mem_normalizer_centralizer_t hp hp2 hK)
    (Or.inr (Or.inr rfl))
  rw [h] at hmem ⊢
  rcases hJ' with rfl | rfl | rfl
  · exact absurd ((spinJ_inf_eq_one_odd hp hp2 hK).1 hmem ht2J) ht1
  · rfl
  · exact absurd ((spinJ_inf_eq_one_odd hp hp2 hK).2.2 ht2J hmem) ht1

theorem conj_mem_spinJ₃_odd (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) {b : spinGroup (quadOdd 3 K)} (hb : b ∈ spinJ₂ K) :
    i * b * i⁻¹ ∈ spinJ₃ K := by
  rw [← hI.map_spinJ₂_odd hp hp2 hK]
  exact ⟨b, hb, rfl⟩

theorem conj_mem_spinJ₂_odd (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) {c : spinGroup (quadOdd 3 K)} (hc : c ∈ spinJ₃ K) :
    i * c * i⁻¹ ∈ spinJ₂ K := by
  rw [← hI.map_spinJ₃_odd hp hp2 hK]
  exact ⟨c, hc, rfl⟩

theorem conj_mem_sup_odd (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) {x : spinGroup (quadOdd 3 K)} (hx : x ∈ spinJ₂ K ⊔ spinJ₃ K) :
    i * x * i⁻¹ ∈ spinJ₂ K ⊔ spinJ₃ K := by
  have h : (spinJ₂ K ⊔ spinJ₃ K).map (MulAut.conj i).toMonoidHom = spinJ₂ K ⊔ spinJ₃ K := by
    rw [Subgroup.map_sup, hI.map_spinJ₂_odd hp hp2 hK, hI.map_spinJ₃_odd hp hp2 hK, sup_comm]
  rw [← h]
  exact ⟨x, hx, rfl⟩

theorem eq_of_mem_spinJ₃_of_mul_self_odd (hA4 : A4) (hI : IsIBar K i) (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) {x : spinGroup (quadOdd 3 K)} (hx : x ∈ spinJ₃ K)
    (hxx : x * x = 1) : x = 1 ∨ x = spinZ K * tSeven K := by
  have hodd := odd_card_spin hp hp2 hK
  have h2 : i * x * i⁻¹ * (i * x * i⁻¹) = 1 := by
    calc i * x * i⁻¹ * (i * x * i⁻¹) = i * (x * x) * i⁻¹ := by group
      _ = 1 := by rw [hxx]; group
  rcases (hA4 K hodd).1 _ (hI.conj_mem_spinJ₂_odd hp hp2 hK hx) h2 with h | h
  · left
    calc x = i⁻¹ * (i * x * i⁻¹) * i := by group
      _ = 1 := by rw [h]; group
  · right
    calc x = i * (i * x * i⁻¹) * i⁻¹ := (hI.conj_conj x).symm
      _ = spinZ K * tSeven K := by rw [h, hI.conj_t]

theorem commute_of_mem_spinJ₃_odd (hA3 : A3) (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) {x : spinGroup (quadOdd 3 K)} (hx : x ∈ spinJ₃ K) (hx1 : x ≠ 1)
    (hxp : x ^ p = 1) {a b : spinGroup (quadOdd 3 K)} (ha : a ∈ spinJ₃ K) (hb : b ∈ spinJ₃ K)
    (hax : a * x = x * a) (hbx : b * x = x * b) : a * b = b * a := by
  have hx1' : i * x * i⁻¹ ≠ 1 := fun h => hx1 (by
    calc x = i⁻¹ * (i * x * i⁻¹) * i := by group
      _ = 1 := by rw [h]; group)
  have hxp' : (i * x * i⁻¹) ^ p = 1 := by
    rw [← MulAut.conj_apply, ← map_pow, hxp, map_one]
  have h := commute_of_mem_spinJ₂ hA3 hp hp2 hK (hI.conj_mem_spinJ₂_odd hp hp2 hK hx) hx1' hxp'
    (hI.conj_mem_spinJ₂_odd hp hp2 hK ha) (hI.conj_mem_spinJ₂_odd hp hp2 hK hb)
    (conj_mul_conj_comm i hax) (conj_mul_conj_comm i hbx)
  apply (MulAut.conj i).injective
  simp only [MulAut.conj_apply]
  calc i * (a * b) * i⁻¹ = i * a * i⁻¹ * (i * b * i⁻¹) := by group
    _ = i * b * i⁻¹ * (i * a * i⁻¹) := h
    _ = i * (b * a) * i⁻¹ := by group

theorem commute_conj_odd (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (b b' : ↥(spinJ₂ K)) :
    Commute (b : spinGroup (quadOdd 3 K)) (i * b' * i⁻¹) :=
  commute_spinJ₂_spinJ₃_odd (odd_card_spin hp hp2 hK) b.2 (hI.conj_mem_spinJ₃_odd hp hp2 hK b'.2)

@[expose] def diagOdd (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) : ↥(spinJ₂ K) →* spinGroup (quadOdd 3 K) :=
  (MonoidHom.noncommCoprod (spinJ₂ K).subtype
    ((MulAut.conj i).toMonoidHom.comp (spinJ₂ K).subtype)
    (hI.commute_conj_odd hp hp2 hK)).comp ((MonoidHom.id _).prod (MonoidHom.id _))

theorem diagOdd_apply (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    (b : ↥(spinJ₂ K)) : hI.diagOdd hp hp2 hK b = b * (i * b * i⁻¹) := rfl

abbrev dTwoThreeOdd (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) :
    Subgroup (spinGroup (quadOdd 3 K)) :=
  (hI.diagOdd hp hp2 hK).range

theorem injective_diagOdd (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) : Function.Injective (hI.diagOdd hp hp2 hK) := by
  rw [injective_iff_map_eq_one]
  intro b hb
  rw [diagOdd_apply] at hb
  have h3 : (b : spinGroup (quadOdd 3 K)) ∈ spinJ₃ K := by
    rw [eq_inv_of_mul_eq_one_left hb]
    exact inv_mem (hI.conj_mem_spinJ₃_odd hp hp2 hK b.2)
  exact Subtype.ext ((spinJ_inf_eq_one_odd hp hp2 hK).2.2 b.2 h3)

theorem card_dTwoThreeOdd (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    Nat.card ↥(hI.dTwoThreeOdd hp hp2 hK) = Nat.card ↥(spinJ₂ K) :=
  (Nat.card_congr (MonoidHom.ofInjective (hI.injective_diagOdd hp hp2 hK)).toEquiv).symm

theorem dTwoThreeOdd_le_sup (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) : hI.dTwoThreeOdd hp hp2 hK ≤ spinJ₂ K ⊔ spinJ₃ K := by
  rintro _ ⟨b, rfl⟩
  rw [diagOdd_apply]
  exact mul_mem (mem_sup_left b.2) (mem_sup_right (hI.conj_mem_spinJ₃_odd hp hp2 hK b.2))

theorem dTwoThreeOdd_le_centralizer_i (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    hI.dTwoThreeOdd hp hp2 hK ≤ centralizer ({i} : Set (spinGroup (quadOdd 3 K))) := by
  rintro _ ⟨b, rfl⟩
  rw [mem_centralizer_singleton_iff, diagOdd_apply]
  have hc : (b : spinGroup (quadOdd 3 K)) * (i * b * i⁻¹) = (i * b * i⁻¹) * b :=
    hI.commute_conj_odd hp hp2 hK b b
  calc (b : spinGroup (quadOdd 3 K)) * (i * b * i⁻¹) * i = (i * b * i⁻¹) * b * i := by rw [hc]
    _ = i * (b * (i * b * i⁻¹)) := by
        rw [hI.inv_eq]
        simp only [mul_assoc]

theorem spinZ_eq_diagOdd (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (ht2J : tSeven K ∈ spinJ₂ K) :
    spinZ K = hI.diagOdd hp hp2 hK ⟨tSeven K, ht2J⟩ := by
  obtain ⟨-, -, hzc, htt, -⟩ := spinZ_facts hp hp2 hK
  rw [diagOdd_apply]
  show spinZ K = tSeven K * (i * tSeven K * i⁻¹)
  rw [hI.conj_t, ← mul_assoc, mem_center_iff.mp hzc (tSeven K), mul_assoc, htt, mul_one]

theorem card_M_odd (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) :
    2 * Nat.card K ^ 2 * (Nat.card K ^ 2 - 1) ≤
      Nat.card ↥(mX K ⊓ centralizer ({i} : Set (spinGroup (quadOdd 3 K)))) := by
  have := finite_spinSeven (two_ne_zero_spin hp hp2 hK)
  have hDS := hI.dTwoThreeOdd_le_sup hp hp2 hK
  have hUD : Nat.card ↥(uThree K ⊔ hI.dTwoThreeOdd hp hp2 hK) =
      Nat.card K * Nat.card ↥(spinJ₂ K) := by
    rw [card_sup_of_commute (fun u hu d hd => commute_spinJ₁_sup (uThree_le_spinJ₁ hu) (hDS hd)),
      card_uThree, hI.card_dTwoThreeOdd hp hp2 hK]
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxu, hxd⟩ := mem_inf.mp hx
    have h := mem_inf.mpr ⟨hDS hxd, hxu⟩
    rwa [sup_inf_uThree_odd hp hp2 hK] at h
  have hUDi : uThree K ⊔ hI.dTwoThreeOdd hp hp2 hK ≤
      centralizer ({i} : Set (spinGroup (quadOdd 3 K))) :=
    sup_le (fun u hu => mem_centralizer_singleton_iff.mpr (hI.commute_J₁ u
      (uThree_le_spinJ₁ hu)).symm) (hI.dTwoThreeOdd_le_centralizer_i hp hp2 hK)
  have hUDt : uThree K ⊔ hI.dTwoThreeOdd hp hp2 hK ≤
      centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))) ⊓
        centralizer ({qThree K} : Set (spinGroup (quadOdd 3 K))) :=
    sup_le (uThree_le_centralizer_inf hp hp2 hK) (hDS.trans (sup_le_centralizer_inf hp hp2 hK))
  have hQ : Nat.card ↥((uThree K ⊔ hI.dTwoThreeOdd hp hp2 hK) ⊔ zpowers i) =
      Nat.card K * Nat.card ↥(spinJ₂ K) * 2 := by
    rw [card_sup_of_commute, hUD, Nat.card_zpowers, hI.orderOf_eq hp hp2 hK]
    · intro a ha y hy
      have hya : y ∈ centralizer ({a} : Set (spinGroup (quadOdd 3 K))) :=
        zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
          (mem_centralizer_singleton_iff.mp (hUDi ha)).symm) hy
      exact (mem_centralizer_singleton_iff.mp hya).symm
    · rw [eq_bot_iff]
      intro x hx
      obtain ⟨hx1, hx2⟩ := mem_inf.mp hx
      rcases eq_one_or_eq_of_mem_zpowers_of_mul_self hI.mul_self hx2 with h | h
      · exact (mem_bot).mpr h
      · exact absurd (h ▸ (mem_inf.mp (hUDt hx1)).1) (hI.not_mem_centralizer_t hp hp2 hK)
  have hle : (uThree K ⊔ hI.dTwoThreeOdd hp hp2 hK) ⊔ zpowers i ≤
      mX K ⊓ centralizer ({i} : Set (spinGroup (quadOdd 3 K))) :=
    sup_le (le_inf (hUDt.trans (centralizer_inf_le_mX hp hp2 hK)) hUDi)
      (zpowers_le.mpr (mem_inf.mpr ⟨hI.mem_mX hp hp2 hK,
        mem_centralizer_singleton_iff.mpr rfl⟩))
  calc 2 * Nat.card K ^ 2 * (Nat.card K ^ 2 - 1) =
      Nat.card K * Nat.card ↥(spinJ₂ K) * 2 := by rw [card_spinJ₂]; ring
    _ = Nat.card ↥((uThree K ⊔ hI.dTwoThreeOdd hp hp2 hK) ⊔ zpowers i) := hQ.symm
    _ ≤ _ := card_le_of_le hle

theorem conj_M_odd (hA2 : A2) (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) {w : spinGroup (quadOdd 3 K)} (hw : w ∈ mX K)
    (hww : w * w = 1) (hwt : w * tSeven K ≠ tSeven K * w) : ∃ m ∈ mX K, m * i * m⁻¹ = w := by
  have hodd := odd_card_spin hp hp2 hK
  have hc := hI.mul_mem_of_not_commute hp hp2 hK hw hwt
  rw [centralizer_inf_eq_odd hA2 hp hp2 hK] at hc
  obtain ⟨x, hx, u, hu, hxu⟩ := exists_mul_of_mem_sup
    (fun x hx u hu => (commute_spinJ₁_sup (uThree_le_spinJ₁ hu) hx).symm) hc
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
  have hinv : i * (w * i) * i⁻¹ = (w * i)⁻¹ := by
    rw [mul_inv_rev, hwinv]
    calc i * (w * i) * i⁻¹ = i * w := by group
      _ = i⁻¹ * w := by rw [hI.inv_eq]
  rw [hxu] at hinv
  have hiu : i * u * i⁻¹ = u := by
    rw [hI.commute_J₁ u (uThree_le_spinJ₁ hu), mul_inv_cancel_right]
  have hxu' : x * u = u * x := (commute_spinJ₁_sup (uThree_le_spinJ₁ hu) hx).symm
  have hx'S : i * x * i⁻¹ ∈ spinJ₂ K ⊔ spinJ₃ K := hI.conj_mem_sup_odd hp hp2 hK hx
  have e1 : (i * x * i⁻¹) * u = x⁻¹ * u⁻¹ := by
    calc (i * x * i⁻¹) * u = (i * x * i⁻¹) * (i * u * i⁻¹) := by rw [hiu]
      _ = i * (x * u) * i⁻¹ := by group
      _ = (x * u)⁻¹ := hinv
      _ = x⁻¹ * u⁻¹ := by rw [hxu', mul_inv_rev]
  have e2 : u * u = (i * x * i⁻¹)⁻¹ * x⁻¹ := by
    calc u * u = (i * x * i⁻¹)⁻¹ * ((i * x * i⁻¹) * u) * u := by group
      _ = (i * x * i⁻¹)⁻¹ * (x⁻¹ * u⁻¹) * u := by rw [e1]
      _ = (i * x * i⁻¹)⁻¹ * x⁻¹ := by group
  have huu : u * u = 1 := by
    have h1 : u * u ∈ (spinJ₂ K ⊔ spinJ₃ K) ⊓ uThree K := by
      refine mem_inf.mpr ⟨?_, mul_mem hu hu⟩
      rw [e2]
      exact mul_mem (inv_mem hx'S) (inv_mem hx)
    rw [sup_inf_uThree_odd hp hp2 hK] at h1
    exact (mem_bot).mp h1
  have hu1 : u = 1 := eq_one_of_mem_uThree_of_mul_self hp hp2 hK hu huu
  subst hu1
  obtain ⟨b, hb, d, hd, rfl⟩ := exists_mul_of_mem_sup (commute_spinJ₂_spinJ₃_odd' hp hp2 hK) hx
  have hbd3 : i * b * i⁻¹ ∈ spinJ₃ K := hI.conj_mem_spinJ₃_odd hp hp2 hK hb
  have hdb2 : i * d * i⁻¹ ∈ spinJ₂ K := hI.conj_mem_spinJ₂_odd hp hp2 hK hd
  have e3 : (i * d * i⁻¹) * (i * b * i⁻¹) = b⁻¹ * d⁻¹ := by
    calc (i * d * i⁻¹) * (i * b * i⁻¹) = (i * b * i⁻¹) * (i * d * i⁻¹) :=
          commute_spinJ₂_spinJ₃_odd hodd hdb2 hbd3
      _ = i * (b * d) * i⁻¹ * 1 := by group
      _ = (b * d)⁻¹ * 1⁻¹ := e1
      _ = d⁻¹ * b⁻¹ := by rw [inv_one, mul_one, mul_inv_rev]
      _ = b⁻¹ * d⁻¹ := (commute_spinJ₂_spinJ₃_odd hodd (inv_mem hb) (inv_mem hd)).symm
  obtain ⟨-, h3⟩ := eq_of_mul_eq_mul_J₂J₃_odd hp hp2 hK hdb2 (inv_mem hb) hbd3 (inv_mem hd) e3
  refine ⟨b, centralizer_inf_le_mX hp hp2 hK (spinJ₂_le_centralizer_inf hp hp2 hK hb), ?_⟩
  have hd' : d = (i * b * i⁻¹)⁻¹ := by rw [h3, inv_inv]
  have hw' : w = b * d * i⁻¹ := by
    calc w = w * i * i⁻¹ := by group
      _ = b * d * 1 * i⁻¹ := by rw [hxu]
      _ = b * d * i⁻¹ := by rw [mul_one]
  rw [hw', hd']
  calc b * i * b⁻¹ = b * (i * b * i⁻¹)⁻¹ * i⁻¹ * (i * i) := by group
    _ = b * (i * b * i⁻¹)⁻¹ * i⁻¹ := by rw [hI.mul_self, mul_one]

end IsIBar

end CFSG.ComponentClassification.HarrisLit.T1.S74
