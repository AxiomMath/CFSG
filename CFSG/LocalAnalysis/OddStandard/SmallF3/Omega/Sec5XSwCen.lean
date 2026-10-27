module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5XSwList
public import Certificates.Kernel.ThCent.Leaves

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.LieType.Multipliers.U43 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Quasithin.H13.U43 CFSG.KGroups.U43 Certificates.Asc82Swap

private lemma natAny_eq_true (n : ℕ) (f : (i : ℕ) → i < n → Bool) :
    Nat.any n f = true ↔ ∃ i, ∃ h : i < n, f i h = true := by
  rw [Nat.any_eq_finRange_any, List.any_eq_true]
  constructor
  · rintro ⟨x, -, hx⟩; exact ⟨x.1, x.2, hx⟩
  · rintro ⟨i, hi, hf⟩; exact ⟨⟨i, hi⟩, List.mem_finRange _, hf⟩

private lemma commB_eq_true {n : ℕ} {t u : Array ℕ} {g h : Equiv.Perm (Fin n)}
    (ht : Rep n t g) (hu : Rep n u h) : commB n t u = true ↔ g * h = h * g := by
  rw [commB, eqA_iff (rep_compA ht hu) (rep_compA hu ht)]

private lemma conjArr_getElem {O Oi : Array (Array ℕ)} {ga : Array ℕ} {k : ℕ}
    (hk : k < O.size) :
    (conjArr 820 O Oi ga)[k]! = compA 820 O[k]! (compA 820 ga Oi[k]!) := by
  unfold conjArr
  rw [getElem!_pos _ k (by simpa using hk), Array.getElem_map, Array.getElem_range]

private lemma rep_inv_of_invsOK {L Li : Array (Array ℕ)} (h : invsOK 820 L Li = true)
    {i : ℕ} (hi : i < L.size) {s : X₀} (hs : Rep 820 L[i]! (psi s)) :
    Rep 820 Li[i]! (psi (s⁻¹)) := by
  have := rep_inv_of_isInvA hs (invsOK_spec h i hi)
  rwa [← map_inv] at this

private lemma conjArr_rep {O Oi : Array (Array ℕ)} {ga : Array ℕ} {g : X₀}
    (hg : Rep 820 ga (psi g)) (hOi : invsOK 820 O Oi = true) {k : ℕ} (hk : k < O.size)
    {o : X₀} (ho : Rep 820 O[k]! (psi o)) :
    Rep 820 (conjArr 820 O Oi ga)[k]! (psi (o * g * o⁻¹)) := by
  have hOi' : Rep 820 Oi[k]! (psi (o⁻¹)) := rep_inv_of_invsOK hOi hk ho
  rw [conjArr_getElem hk]
  have h1 : Rep 820 (compA 820 ga Oi[k]!) (psi g * psi (o⁻¹)) := rep_compA hg hOi'
  have h2 : Rep 820 (compA 820 O[k]! (compA 820 ga Oi[k]!))
      (psi o * (psi g * psi (o⁻¹))) := rep_compA ho h1
  have heq : psi o * (psi g * psi (o⁻¹)) = psi (o * g * o⁻¹) := by
    rw [map_mul, map_mul, map_inv, mul_assoc]
  rwa [heq] at h2

theorem sw_cenB_iff {O Oi : Array (Array ℕ)} (hO : SwCover O {o | o ∈ SwC ∧ Odd (orderOf o)})
    (hOi : invsOK 820 O Oi = true) {g h : X₀} {ga ha : Array ℕ} (hg : Rep 820 ga (psi g))
    (hh : Rep 820 ha (psi h)) :
    cenB 820 (conjArr 820 O Oi ga) ha = true ↔
      ∀ o ∈ SwC, Odd (orderOf o) → h * (o * g * o⁻¹) = o * g * o⁻¹ * h := by
  constructor
  · intro hcen o hoC hoOdd
    obtain ⟨k, hk, hkrep⟩ := hO.2 o ⟨hoC, hoOdd⟩
    rw [cenB, Array.all_eq_true] at hcen
    have hcomm : commB 820 ha (conjArr 820 O Oi ga)[k]! = true := by
      have h' := hcen k (by simpa [conjArr] using hk)
      rwa [← getElem!_pos (conjArr 820 O Oi ga) k (by simpa [conjArr] using hk)] at h'
    have hrep := conjArr_rep hg hOi hk hkrep
    have hEq := (commB_eq_true hh hrep).1 hcomm
    have hcalc : psi (h * (o * g * o⁻¹)) = psi ((o * g * o⁻¹) * h) := by
      calc psi (h * (o * g * o⁻¹))
          = psi h * psi (o * g * o⁻¹) := map_mul psi h _
        _ = psi (o * g * o⁻¹) * psi h := hEq
        _ = psi ((o * g * o⁻¹) * h) := (map_mul psi _ h).symm
    exact psi_inj hcalc
  · intro hmain
    rw [cenB, Array.all_eq_true]
    intro k hk
    have hkO : k < O.size := by simpa [conjArr] using hk
    obtain ⟨o, ho, hkrep⟩ := hO.1 k hkO
    have hrep := conjArr_rep hg hOi hkO hkrep
    rw [← getElem!_pos (conjArr 820 O Oi ga) k hk, commB_eq_true hh hrep]
    rw [← map_mul, ← map_mul, hmain o ho.1 ho.2]

theorem sw_t1_sound {L O Oi : Array (Array ℕ)} (hL : SwCover L (SwC : Set X₀))
    (hO : SwCover O {o | o ∈ SwC ∧ Odd (orderOf o)}) (hOi : invsOK 820 O Oi = true)
    {g₁ g₂ : X₀} {ga₁ ga₂ one xA : Array ℕ} (hg₁ : Rep 820 ga₁ (psi g₁))
    (hg₂ : Rep 820 ga₂ (psi g₂)) (hone : Rep 820 one (psi 1)) (hxA : Rep 820 xA (psi xElt))
    (hT : t1Check 820 L (conjArr 820 O Oi ga₁) (conjArr 820 O Oi ga₂) one xA = true) :
    ∀ h ∈ SwCen g₁, h ∈ SwCen g₂ → h = 1 ∨ h = xElt := by
  intro h h1 h2
  have hhC : h ∈ SwC := h1.1
  obtain ⟨j, hj, hjrep⟩ := hL.2 h hhC
  have hcen1 : cenB 820 (conjArr 820 O Oi ga₁) L[j]! = true :=
    (sw_cenB_iff hO hOi hg₁ hjrep).2 (fun o ho hodd => h1.2 o ho hodd)
  have hcen2 : cenB 820 (conjArr 820 O Oi ga₂) L[j]! = true :=
    (sw_cenB_iff hO hOi hg₂ hjrep).2 (fun o ho hodd => h2.2 o ho hodd)
  have ht1 := allLt_spec hT hj
  simp only [hcen1, hcen2, Bool.or_eq_true_iff] at ht1
  rcases ht1 with h | h
  · rcases h with h | h
    · simp at h
    · exact Or.inl (psi_inj ((eqA_iff hjrep hone).1 h))
  · exact Or.inr (psi_inj ((eqA_iff hjrep hxA).1 h))

theorem sw_t2_sound {L Li O Oi : Array (Array ℕ)} (hL : SwCover L (SwC : Set X₀))
    (hLi : invsOK 820 L Li = true) (hO : SwCover O {o | o ∈ SwC ∧ Odd (orderOf o)})
    (hOi : invsOK 820 O Oi = true) {g₁ g₂ : X₀} {ga₁ ga₂ : Array ℕ}
    (hg₁ : Rep 820 ga₁ (psi g₁)) (hg₂ : Rep 820 ga₂ (psi g₂))
    (hT : t2Check 820 L Li (O.filter (cenB 820 (conjArr 820 O Oi ga₂)))
      (O.filter (cenB 820 (conjArr 820 O Oi ga₁))) (conjArr 820 O Oi ga₁)
      (conjArr 820 O Oi ga₂) = true) :
    ∃ c ∈ SwC, (∀ o ∈ SwC, Odd (orderOf o) → o ∈ SwCen g₂ → c⁻¹ * o * c ∈ SwCen g₁) ∧
      (∀ o ∈ SwC, Odd (orderOf o) → o ∈ SwCen g₁ → c * o * c⁻¹ ∈ SwCen g₂) := by
  unfold t2Check at hT
  obtain ⟨kc, hkc, hval⟩ := (natAny_eq_true L.size _).mp hT
  rw [Bool.and_eq_true_iff] at hval
  obtain ⟨hX1, hX2⟩ := hval
  obtain ⟨c, hc, hLc⟩ := hL.1 kc hkc
  have hLic : Rep 820 Li[kc]! (psi (c⁻¹)) := rep_inv_of_invsOK hLi hkc hLc
  refine ⟨c, hc, ?_, ?_⟩
  · intro o hoC hoOdd hoCen
    obtain ⟨k, hk, hkrep⟩ := hO.2 o ⟨hoC, hoOdd⟩
    have hcen2 : cenB 820 (conjArr 820 O Oi ga₂) O[k]! = true :=
      (sw_cenB_iff hO hOi hg₂ hkrep).2 (fun o' ho' hodd => hoCen.2 o' ho' hodd)
    have hk_mem : O[k]! ∈ O := by
      rw [getElem!_pos O k hk]
      exact Array.getElem_mem hk
    have hX1' : cenB 820 (conjArr 820 O Oi ga₁)
        (compA 820 Li[kc]! (compA 820 O[k]! L[kc]!)) = true :=
      (Array.all_eq_true'.1 hX1) (O[k]!) (Array.mem_filter.mpr ⟨hk_mem, hcen2⟩)
    have hrep1 : Rep 820 (compA 820 O[k]! L[kc]!) (psi (o * c)) := by
      have h := rep_compA hkrep hLc
      rwa [← map_mul] at h
    have harg : Rep 820 (compA 820 Li[kc]! (compA 820 O[k]! L[kc]!))
        (psi (c⁻¹ * o * c)) := by
      have h := rep_compA hLic hrep1
      rwa [← map_mul, ← mul_assoc] at h
    refine ⟨?_, ?_⟩
    · exact SwC.mul_mem (SwC.mul_mem (SwC.inv_mem hc) hoC) hc
    · intro o' ho' hodd
      exact (sw_cenB_iff hO hOi hg₁ harg).1 hX1' o' ho' hodd
  · intro o hoC hoOdd hoCen
    obtain ⟨k, hk, hkrep⟩ := hO.2 o ⟨hoC, hoOdd⟩
    have hcen1 : cenB 820 (conjArr 820 O Oi ga₁) O[k]! = true :=
      (sw_cenB_iff hO hOi hg₁ hkrep).2 (fun o' ho' hodd => hoCen.2 o' ho' hodd)
    have hk_mem : O[k]! ∈ O := by
      rw [getElem!_pos O k hk]
      exact Array.getElem_mem hk
    have hX2' : cenB 820 (conjArr 820 O Oi ga₂)
        (compA 820 L[kc]! (compA 820 O[k]! Li[kc]!)) = true :=
      (Array.all_eq_true'.1 hX2) (O[k]!) (Array.mem_filter.mpr ⟨hk_mem, hcen1⟩)
    have hrep1 : Rep 820 (compA 820 O[k]! Li[kc]!) (psi (o * c⁻¹)) := by
      have h := rep_compA hkrep hLic
      rwa [← map_mul] at h
    have harg : Rep 820 (compA 820 L[kc]! (compA 820 O[k]! Li[kc]!))
        (psi (c * o * c⁻¹)) := by
      have h := rep_compA hLc hrep1
      rwa [← map_mul, ← mul_assoc] at h
    refine ⟨?_, ?_⟩
    · exact SwC.mul_mem (SwC.mul_mem hc hoC) (SwC.inv_mem hc)
    · intro o' ho' hodd
      exact (sw_cenB_iff hO hOi hg₂ harg).1 hX2' o' ho' hodd

end CFSG.OddStandard.SmallF3.Omega
