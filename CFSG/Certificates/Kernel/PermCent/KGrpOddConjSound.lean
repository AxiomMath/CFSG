module

public import CFSG.Certificates.Kernel.PermCent.KGrpCSound
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import Certificates.Data.Kernel.PermCent.KGrpC2

public section

namespace CFSG.Certificates.Kernel.PkCV.KGrp

open CFSG.Certificates CFSG.Sporadic.Schreier

variable {n : Nat} [Small n]

@[expose] noncomputable def invOC (τ : CV n) : Bool := powOneC τ 2 && !decide (τ = 1)

theorem invOC_conj (g x : CV n) : invOC (g * x * g⁻¹) = invOC x := by
  have h : ∀ y : CV n, g * y * g⁻¹ = 1 ↔ y = 1 := fun y =>
    ⟨fun h => by simpa [mul_assoc] using congrArg (fun z => g⁻¹ * z * g) h, fun h => by simp [h]⟩
  unfold invOC
  simp only [← powOneC_eq', conj_pow, h]

theorem one_memC (Q : RawSchreierDatum n) (hQ : ValidSchreier Q) : (1 : CV n) ∈ elemsC Q := by
  rw [mem_elemsC Q hQ, ev_one]
  exact Q.originalSubgroup.one_mem

theorem mul_memC (Q : RawSchreierDatum n) (hQ : ValidSchreier Q) {g h : CV n}
    (hg : g ∈ elemsC Q) (hh : h ∈ elemsC Q) : g * h ∈ elemsC Q := by
  rw [mem_elemsC Q hQ] at hg hh ⊢
  rw [ev_mul]
  exact Q.originalSubgroup.mul_mem hg hh

theorem inv_memC (Q : RawSchreierDatum n) (hQ : ValidSchreier Q) {g : CV n}
    (hg : g ∈ elemsC Q) : g⁻¹ ∈ elemsC Q := by
  rw [mem_elemsC Q hQ] at hg ⊢
  rw [ev_inv]
  exact Q.originalSubgroup.inv_mem hg

theorem mem_centL (L : List (CV n)) (r g : CV n) : g ∈ centL L r ↔ g ∈ L ∧ g * r = r * g := by
  unfold centL
  rw [List.mem_filter, eq22C_eq, decide_eq_true_iff]

theorem card_conj_mul (Q : RawSchreierDatum n) (hQ : ValidSchreier Q) (r : CV n) :
    ((elemsC Q).map fun g => g * r * g⁻¹).toFinset.card * (centL (elemsC Q) r).length =
      (elemsC Q).length := by
  set L := elemsC Q with hL
  have hnd : L.Nodup := nodup_elemsC Q hQ
  set f : CV n → CV n := fun g => g * r * g⁻¹ with hf
  have himg : (L.map f).toFinset = L.toFinset.image f := by
    ext y
    simp only [List.mem_toFinset, List.mem_map, Finset.mem_image]
  have hC : (centL L r).length = (centL L r).toFinset.card :=
    (List.toFinset_card_of_nodup (hnd.filter _)).symm
  have fib : ∀ y ∈ L.toFinset.image f,
      (L.toFinset.filter fun g => f g = y).card = (centL L r).toFinset.card := by
    intro y hy
    obtain ⟨g0, hg0, rfl⟩ := Finset.mem_image.1 hy
    rw [List.mem_toFinset] at hg0
    have e : (L.toFinset.filter fun g => f g = f g0) = (centL L r).toFinset.image (g0 * ·) := by
      ext g
      simp only [Finset.mem_filter, List.mem_toFinset, Finset.mem_image, mem_centL, hf]
      constructor
      · rintro ⟨hg, he⟩
        refine ⟨g0⁻¹ * g, ⟨mul_memC Q hQ (inv_memC Q hQ hg0) hg, ?_⟩, by group⟩
        calc g0⁻¹ * g * r = g0⁻¹ * (g * r * g⁻¹) * g := by group
          _ = g0⁻¹ * (g0 * r * g0⁻¹) * g := by rw [he]
          _ = r * (g0⁻¹ * g) := by group
      · rintro ⟨h, ⟨hh, hc⟩, rfl⟩
        refine ⟨mul_memC Q hQ hg0 hh, ?_⟩
        calc g0 * h * r * (g0 * h)⁻¹ = g0 * (h * r) * h⁻¹ * g0⁻¹ := by group
          _ = g0 * (r * h) * h⁻¹ * g0⁻¹ := by rw [hc]
          _ = g0 * r * g0⁻¹ := by group
    rw [e, Finset.card_image_of_injective _ (mul_right_injective g0)]
  rw [← List.toFinset_card_of_nodup hnd, Finset.card_eq_sum_card_image f L.toFinset,
    Finset.sum_congr rfl fib, Finset.sum_const, smul_eq_mul, himg, hC]

theorem conj_of_count (QA QP : RawSchreierDatum n) (hA : ValidSchreier QA)
    (hP : ValidSchreier QP) (hle : QP.originalSubgroup ≤ QA.originalSubgroup) (a b : CV n)
    (ka kb : Nat) (hka : (elemsC QP).length = ka * (centL (elemsC QP) a).length)
    (hkb : (elemsC QP).length = kb * (centL (elemsC QP) b).length)
    (hI : ((elemsC QA).filter invOC).length = ka + kb) (haA : a ∈ elemsC QA)
    (hbA : b ∈ elemsC QA) (hai : invOC a = true) (hbi : invOC b = true) (haP : a ∈ elemsC QP)
    (hbP : b ∉ elemsC QP) :
    ∀ τ ∈ (elemsC QA).filter invOC, ∃ r ∈ [a, b], ∃ g ∈ elemsC QP, τ = g * r * g⁻¹ := by
  have hPA : ∀ g, g ∈ elemsC QP → g ∈ elemsC QA := fun g hg =>
    (mem_elemsC QA hA g).2 (hle ((mem_elemsC QP hP g).1 hg))
  set I := (elemsC QA).filter invOC with hIdef
  have hInd : I.Nodup := (nodup_elemsC QA hA).filter _
  set Ca := ((elemsC QP).map fun g => g * a * g⁻¹).toFinset with hCa
  set Cb := ((elemsC QP).map fun g => g * b * g⁻¹).toFinset with hCb
  have hpos : ∀ r, 0 < (centL (elemsC QP) r).length := fun r =>
    List.length_pos_of_mem ((mem_centL _ r 1).2 ⟨one_memC QP hP, by group⟩)
  have hcard : ∀ (r : CV n) (k : Nat), (elemsC QP).length = k * (centL (elemsC QP) r).length →
      ((elemsC QP).map fun g => g * r * g⁻¹).toFinset.card = k := fun r k hk =>
    Nat.eq_of_mul_eq_mul_right (hpos r) ((card_conj_mul QP hP r).trans hk)
  have hsub : ∀ r, r ∈ elemsC QA → invOC r = true →
      ((elemsC QP).map fun g => g * r * g⁻¹).toFinset ⊆ I.toFinset := by
    intro r hr hri y hy
    rw [List.mem_toFinset, List.mem_map] at hy
    obtain ⟨g, hg, rfl⟩ := hy
    rw [List.mem_toFinset, hIdef, List.mem_filter, invOC_conj]
    exact ⟨conj_mem_elemsC QA hA (hPA g hg) hr, hri⟩
  have hdisj : Disjoint Ca Cb := by
    rw [Finset.disjoint_left]
    intro y hya hyb
    rw [hCa, List.mem_toFinset, List.mem_map] at hya
    rw [hCb, List.mem_toFinset, List.mem_map] at hyb
    obtain ⟨g, hg, rfl⟩ := hya
    obtain ⟨h, hh, e⟩ := hyb
    apply hbP
    have hb : b = (h⁻¹ * g) * a * (h⁻¹ * g)⁻¹ := by
      calc b = h⁻¹ * (h * b * h⁻¹) * h := by group
        _ = h⁻¹ * (g * a * g⁻¹) * h := by rw [e]
        _ = (h⁻¹ * g) * a * (h⁻¹ * g)⁻¹ := by group
    rw [hb]
    exact conj_mem_elemsC QP hP (mul_memC QP hP (inv_memC QP hP hh) hg) haP
  have hU : Ca ∪ Cb = I.toFinset := by
    apply Finset.eq_of_subset_of_card_le (Finset.union_subset (hsub a haA hai) (hsub b hbA hbi))
    rw [List.toFinset_card_of_nodup hInd, hI, Finset.card_union_of_disjoint hdisj, hCa, hCb,
      hcard a ka hka, hcard b kb hkb]
  intro τ hτ
  have hτ' : τ ∈ Ca ∪ Cb := by rw [hU, List.mem_toFinset]; exact hτ
  rcases Finset.mem_union.1 hτ' with h | h
  · rw [hCa, List.mem_toFinset, List.mem_map] at h
    obtain ⟨g, hg, e⟩ := h
    exact ⟨a, by simp, g, hg, e.symm⟩
  · rw [hCb, List.mem_toFinset, List.mem_map] at h
    obtain ⟨g, hg, e⟩ := h
    exact ⟨b, by simp, g, hg, e.symm⟩

theorem oddCoreAtC_iff (m : Nat) (CA CP : List (CV n)) :
    oddCoreAtC m CA CP = true ↔
      ∀ x ∈ CA, x ≠ 1 → x ^ m = 1 → ∃ c ∈ CP, (x * c * x⁻¹ * c⁻¹) ^ m ≠ 1 := by
  unfold oddCoreAtC
  rw [List.all_eq_true]
  refine forall_congr' fun x => forall_congr' fun _ => ?_
  by_cases h1 : x = 1
  · simp [h1]
  · by_cases h2 : x ^ m = 1
    · simp [h1, h2, List.any_eq_true]
    · simp [h1, h2]

theorem oddCoreAtC_conj (QA QP : RawSchreierDatum n) (hA : ValidSchreier QA)
    (hP : ValidSchreier QP) {g : CV n} (hgA : g ∈ elemsC QA) (hgP : g ∈ elemsC QP) (m : Nat)
    (r : CV n) (h : oddCoreAtC m (centL (elemsC QA) r) (centL (elemsC QP) r) = true) :
    oddCoreAtC m (centL (elemsC QA) (g * r * g⁻¹)) (centL (elemsC QP) (g * r * g⁻¹)) = true := by
  rw [oddCoreAtC_iff] at h ⊢
  intro x hx hx1 hxm
  rw [mem_centL] at hx
  obtain ⟨hxA, hxc⟩ := hx
  have hyc : g⁻¹ * x * g⁻¹⁻¹ * r = r * (g⁻¹ * x * g⁻¹⁻¹) := by
    calc g⁻¹ * x * g⁻¹⁻¹ * r = g⁻¹ * (x * (g * r * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * r * g⁻¹) * x) * g := by rw [hxc]
      _ = r * (g⁻¹ * x * g⁻¹⁻¹) := by group
  have hy1 : g⁻¹ * x * g⁻¹⁻¹ ≠ 1 := fun e => hx1 (by
    calc x = g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ := by group
      _ = 1 := by rw [e]; group)
  have hym : (g⁻¹ * x * g⁻¹⁻¹) ^ m = 1 := by rw [conj_pow, hxm]; group
  have hy : g⁻¹ * x * g⁻¹⁻¹ ∈ centL (elemsC QA) r :=
    (mem_centL _ r _).2 ⟨conj_mem_elemsC QA hA (inv_memC QA hA hgA) hxA, hyc⟩
  obtain ⟨c, hc, hcm⟩ := h _ hy hy1 hym
  rw [mem_centL] at hc
  obtain ⟨hcP, hcc⟩ := hc
  refine ⟨g * c * g⁻¹, (mem_centL _ _ _).2 ⟨conj_mem_elemsC QP hP hgP hcP, ?_⟩, ?_⟩
  · calc g * c * g⁻¹ * (g * r * g⁻¹) = g * (c * r) * g⁻¹ := by group
      _ = g * (r * c) * g⁻¹ := by rw [hcc]
      _ = g * r * g⁻¹ * (g * c * g⁻¹) := by group
  · intro e
    apply hcm
    have e2 : x * (g * c * g⁻¹) * x⁻¹ * (g * c * g⁻¹)⁻¹ =
        g * (g⁻¹ * x * g⁻¹⁻¹ * c * (g⁻¹ * x * g⁻¹⁻¹)⁻¹ * c⁻¹) * g⁻¹ := by group
    rw [e2, conj_pow] at e
    calc (g⁻¹ * x * g⁻¹⁻¹ * c * (g⁻¹ * x * g⁻¹⁻¹)⁻¹ * c⁻¹) ^ m
        = g⁻¹ * (g * (g⁻¹ * x * g⁻¹⁻¹ * c * (g⁻¹ * x * g⁻¹⁻¹)⁻¹ * c⁻¹) ^ m * g⁻¹) * g := by
          group
      _ = 1 := by rw [e]; group

theorem oddCoreCheckC_of_reps (QA QP : RawSchreierDatum n) (hA : ValidSchreier QA)
    (hP : ValidSchreier QP) (hle : QP.originalSubgroup ≤ QA.originalSubgroup) (m : Nat)
    (R : List (CV n))
    (hcl : ∀ τ ∈ (elemsC QA).filter invOC, ∃ r ∈ R, ∃ g ∈ elemsC QP, τ = g * r * g⁻¹)
    (hR : ∀ r ∈ R, oddCoreAtC m (centL (elemsC QA) r) (centL (elemsC QP) r) = true) :
    oddCoreCheckC m (elemsC QA) (elemsC QP) = true := by
  unfold oddCoreCheckC
  rw [List.all_eq_true]
  intro τ hτ
  cases hb : (powOneC τ 2 && !decide (τ = 1))
  · rfl
  · rw [cond_true]
    obtain ⟨r, hr, g, hgP, rfl⟩ := hcl τ (List.mem_filter.2 ⟨hτ, hb⟩)
    exact oddCoreAtC_conj QA QP hA hP ((mem_elemsC QA hA g).2 (hle ((mem_elemsC QP hP g).1 hgP)))
      hgP m r (hR r hr)

end CFSG.Certificates.Kernel.PkCV.KGrp

end
