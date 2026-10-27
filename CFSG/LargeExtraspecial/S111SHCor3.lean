module

public import CFSG.ClassicalInvolution.AschTight.S1916Alp
public import CFSG.Walter.Cited.HuppertAlperin
public import CFSG.LargeExtraspecial.S111CBasic

public section

namespace CFSG.LargeExtraspecial.S11

open Subgroup CFSG.RankTwoShapes

section Basic

variable {X : Type*} [Group X]

@[expose] def wclSet (t : X) : Set X := {y | ∃ m : X, y = m * t * m⁻¹ ∧ y * t = t * y}

@[expose] def wcl (t : X) : Subgroup X := closure (wclSet t)

theorem subset_wcl (t : X) : wclSet t ⊆ wcl t := subset_closure

theorem self_mem_wclSet (t : X) : t ∈ wclSet t := ⟨1, by group, rfl⟩

theorem self_mem_wcl (t : X) : t ∈ wcl t := subset_wcl t (self_mem_wclSet t)

theorem conj_mem_wcl_of_forall {t c : X} (hc : ∀ y ∈ wclSet t, c * y * c⁻¹ ∈ wclSet t)
    {x : X} (hx : x ∈ wcl t) : c * x * c⁻¹ ∈ wcl t := by
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact subset_wcl t (hc y hy)
  | one => simp [one_mem]
  | mul a b _ _ ha hb =>
    have e : c * (a * b) * c⁻¹ = (c * a * c⁻¹) * (c * b * c⁻¹) := by group
    rw [e]
    exact mul_mem ha hb
  | inv a _ ha =>
    have e : c * a⁻¹ * c⁻¹ = (c * a * c⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem ha

theorem conj_mem_wclSet {t c y : X} (hc : c * t = t * c) (hy : y ∈ wclSet t) :
    c * y * c⁻¹ ∈ wclSet t := by
  obtain ⟨m, rfl, hm⟩ := hy
  refine ⟨c * m, by group, ?_⟩
  have hct : c⁻¹ * t = t * c⁻¹ := by
    calc c⁻¹ * t = c⁻¹ * (t * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * t) * c⁻¹ := by rw [hc]
      _ = t * c⁻¹ := by group
  calc c * (m * t * m⁻¹) * c⁻¹ * t = c * ((m * t * m⁻¹) * (c⁻¹ * t)) := by group
    _ = c * ((m * t * m⁻¹) * t) * c⁻¹ := by rw [hct]; group
    _ = c * (t * (m * t * m⁻¹)) * c⁻¹ := by rw [hm]
    _ = (c * t) * (m * t * m⁻¹) * c⁻¹ := by group
    _ = t * (c * (m * t * m⁻¹) * c⁻¹) := by rw [hc]; group

theorem mem_normalizer_wcl {t c : X} (hc : c * t = t * c) :
    c ∈ normalizer (wcl t : Set X) := by
  have hci : c⁻¹ * t = t * c⁻¹ := by
    calc c⁻¹ * t = c⁻¹ * (t * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * t) * c⁻¹ := by rw [hc]
      _ = t * c⁻¹ := by group
  rw [mem_normalizer_iff]
  intro h
  refine ⟨fun hh => conj_mem_wcl_of_forall (fun y hy => conj_mem_wclSet hc hy) hh, fun hh => ?_⟩
  have := conj_mem_wcl_of_forall (fun y hy => conj_mem_wclSet hci hy) hh
  simpa [mul_assoc] using this

theorem isPGroup_wcl {p : ℕ} {t : X} (ht : ∃ k : ℕ, t ^ p ^ k = 1)
    (hab : IsMulCommutative (wcl t)) : IsPGroup p (wcl t) := by
  have hcomm : ∀ a ∈ wcl t, ∀ b ∈ wcl t, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨k, hk⟩ := ht
  suffices h : ∀ x ∈ wcl t, ∃ e : ℕ, x ^ p ^ e = 1 by
    intro x
    obtain ⟨e, he⟩ := h x x.2
    exact ⟨e, Subtype.ext (by simpa using he)⟩
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨m, rfl, -⟩ := hy
    exact ⟨k, by rw [conj_pow, hk]; group⟩
  | one => exact ⟨0, one_pow _⟩
  | mul a b ha hb iha ihb =>
    obtain ⟨e₁, he₁⟩ := iha
    obtain ⟨e₂, he₂⟩ := ihb
    refine ⟨e₁ + e₂, ?_⟩
    have hc : Commute a b := hcomm a ha b hb
    rw [hc.mul_pow, pow_add, pow_mul, he₁, one_pow, one_mul, mul_comm (p ^ e₁), pow_mul, he₂,
      one_pow]
  | inv a _ iha =>
    obtain ⟨e, he⟩ := iha
    exact ⟨e, by rw [inv_pow, he, inv_one]⟩

end Basic

section Normalizer

variable {X : Type*} [Group X]

theorem mem_map_conj_iff' {H : Subgroup X} {g y : X} :
    y ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ H := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [mul_assoc] using hx
  · intro hy
    exact ⟨g⁻¹ * y * g, hy, by simp [mul_assoc]⟩

theorem centralizer_le_normalizer' (Q : Subgroup X) :
    centralizer (Q : Set X) ≤ normalizer (Q : Set X) := by
  intro c hc
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have e : c * h * c⁻¹ = h := by
      rw [← mem_centralizer_iff.mp hc h hh]
      group
    rwa [e]
  · intro hh
    have e : c * h * c⁻¹ * c = c * (c * h * c⁻¹) := mem_centralizer_iff.mp hc _ hh
    have e' : h = c * h * c⁻¹ := by
      simp only [mul_assoc, inv_mul_cancel, mul_one] at e
      simpa [mul_assoc] using mul_left_cancel e
    rw [e']
    exact hh

theorem inv_pow_mul_mul_pow_mem {K : Subgroup X} {d k : X} (hd : d ∈ normalizer (K : Set X))
    (hk : k ∈ K) : ∀ m : ℕ, (d ^ m)⁻¹ * (d * k) ^ m ∈ K
  | 0 => by simp [one_mem]
  | m + 1 => by
    have ih := inv_pow_mul_mul_pow_mem hd hk m
    have e : (d ^ (m + 1))⁻¹ * (d * k) ^ (m + 1) =
        d⁻¹ * ((d ^ m)⁻¹ * (d * k) ^ m) * d * k := by
      rw [pow_succ, pow_succ, mul_inv_rev]
      simp only [mul_assoc]
    rw [e]
    refine mul_mem ?_ hk
    have := (mem_normalizer_iff.mp (inv_mem hd) _).mp ih
    simpa [mul_assoc] using this

end Normalizer

section Sylow

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem exists_pow_eq_one_of_mem_sylow (P : Sylow 2 X) {t : X} (htP : t ∈ (P : Subgroup X)) :
    ∃ k : ℕ, t ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := P.isPGroup' ⟨t, htP⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

omit [Finite X] in
theorem wcl_le_sylow (P : Sylow 2 X) {t : X} (htP : t ∈ (P : Subgroup X))
    (htc : ∀ x ∈ (P : Subgroup X), x * t = t * x) (hab : IsMulCommutative (wcl t)) :
    wcl t ≤ P := by
  have hW := isPGroup_wcl (exists_pow_eq_one_of_mem_sylow P htP) hab
  have hPN : (P : Subgroup X) ≤ normalizer (wcl t : Set X) := fun x hx =>
    mem_normalizer_wcl (htc x hx)
  have hmax := P.is_maximal' (P.isPGroup'.to_sup_of_normal_right' hW hPN) le_sup_left
  calc wcl t ≤ (P : Subgroup X) ⊔ wcl t := le_sup_right
    _ = P := hmax

theorem wcl_le_of_isAlperinSubgroup (P : Sylow 2 X) {t : X} (htP : t ∈ (P : Subgroup X))
    (htc : ∀ x ∈ (P : Subgroup X), x * t = t * x) (hab : IsMulCommutative (wcl t))
    {Q : Subgroup X} (hQ : IsAlperinSubgroup 2 (P : Subgroup X) Q) : wcl t ≤ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := wcl t with hWdef
  set N := normalizer (Q : Set X) with hNdef
  have hWP : W ≤ P := wcl_le_sylow P htP htc hab
  have hW2 : IsPGroup 2 W := isPGroup_wcl (exists_pow_eq_one_of_mem_sylow P htP) hab
  have hcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have htQ : t ∈ Q :=
    CFSG.ClassicalInvolution.Disconnected.AschTight.S1916.mem_of_isAlperinSubgroup hQ htP htc
  set S0 : Set X := {y | ∃ n ∈ N, y = n * t * n⁻¹} with hS0
  have hS0Q : ∀ y ∈ S0, y ∈ Q := by
    rintro _ ⟨n, hn, rfl⟩
    exact (mem_normalizer_iff.mp hn t).mp htQ
  have hS0W : ∀ y ∈ S0, y ∈ W := by
    intro y hy
    have hyQ := hS0Q y hy
    obtain ⟨n, -, rfl⟩ := hy
    exact subset_wcl t ⟨n, rfl, htc _ (hQ.1 hyQ)⟩
  set C0 : Subgroup X := N ⊓ centralizer S0 with hC0
  set A1 : Subgroup X := W ⊓ N with hA1
  have hA1C0 : A1 ≤ C0 := fun x hx =>
    ⟨hx.2, mem_centralizer_iff.mpr fun y hy => hcomm y (hS0W y hy) x hx.1⟩
  have hC0t : ∀ c ∈ C0, c * t = t * c := fun c hc =>
    (mem_centralizer_iff.mp hc.2 t ⟨1, one_mem _, by group⟩).symm
  have hC0A1 : C0 ≤ normalizer (A1 : Set X) := fun c hc =>
    mem_normalizer_inf (mem_normalizer_wcl (hC0t c hc)) (le_normalizer hc.1)
  have hNC0 : ∀ n ∈ N, ∀ c ∈ C0, n * c * n⁻¹ ∈ C0 := by
    intro n hn c hc
    refine Subgroup.mem_inf.mpr ⟨N.mul_mem (N.mul_mem hn (Subgroup.mem_inf.mp hc).1)
      (N.inv_mem hn), mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨m, hm, rfl⟩
    have h1 := mem_centralizer_iff.mp hc.2 ((n⁻¹ * m) * t * (n⁻¹ * m)⁻¹)
      ⟨n⁻¹ * m, mul_mem (inv_mem hn) hm, rfl⟩
    calc m * t * m⁻¹ * (n * c * n⁻¹)
        = n * ((n⁻¹ * m) * t * (n⁻¹ * m)⁻¹ * c) * n⁻¹ := by group
      _ = n * (c * ((n⁻¹ * m) * t * (n⁻¹ * m)⁻¹)) * n⁻¹ := by rw [h1]
      _ = n * c * n⁻¹ * (m * t * m⁻¹) := by group
  set 𝒦 : Set (Subgroup X) := {B | ∃ n ∈ N, B = A1.map (MulAut.conj n).toMonoidHom} with h𝒦
  have h𝒦2 : ∀ B ∈ 𝒦, IsPGroup 2 B := by
    rintro _ ⟨n, -, rfl⟩
    exact (hW2.to_le inf_le_left).map _
  have h𝒦C0 : ∀ B ∈ 𝒦, B ≤ C0 := by
    rintro _ ⟨n, hn, rfl⟩ _ ⟨a, ha, rfl⟩
    exact hNC0 n hn a (hA1C0 ha)
  have hC0𝒦 : ∀ B ∈ 𝒦, C0 ≤ normalizer (B : Set X) := by
    rintro _ ⟨n, hn, rfl⟩ c hc
    rw [mem_normalizer_iff]
    intro h
    have hc' : n⁻¹ * c * n⁻¹⁻¹ ∈ C0 := hNC0 n⁻¹ (inv_mem hn) c hc
    rw [mem_map_conj_iff', mem_map_conj_iff', mem_normalizer_iff.mp (hC0A1 hc') (n⁻¹ * h * n)]
    constructor <;> intro hh <;> convert hh using 1 <;> group
  set D : Subgroup X := sSup 𝒦 with hD
  have hD2 : IsPGroup 2 D :=
    isPGroup_sSup_of_le_normalizer h𝒦2 fun B hB B' hB' => (h𝒦C0 B hB).trans (hC0𝒦 B' hB')
  have hA1D : A1 ≤ D := by
    intro x hx
    have hle : A1.map (MulAut.conj (1 : X)).toMonoidHom ≤ D := le_sSup ⟨1, one_mem _, rfl⟩
    exact hle (Subgroup.mem_map.mpr ⟨x, hx, by simp⟩)
  have hDN : D ≤ N := sSup_le fun B hB => (h𝒦C0 B hB).trans inf_le_left
  have hconjD : ∀ n ∈ N, ∀ h ∈ D, n * h * n⁻¹ ∈ D := by
    intro n hn h hh
    have hle : D ≤ D.comap (MulAut.conj n).toMonoidHom := by
      refine sSup_le fun B hB => ?_
      obtain ⟨n', hn', rfl⟩ := hB
      rintro _ ⟨a, ha, rfl⟩
      have hle : A1.map (MulAut.conj (n * n')).toMonoidHom ≤ D :=
        le_sSup ⟨n * n', N.mul_mem hn hn', rfl⟩
      refine Subgroup.mem_comap.mpr (hle (Subgroup.mem_map.mpr ⟨a, ha, ?_⟩))
      simp [mul_assoc]
    exact hle hh
  have hND : N ≤ normalizer (D : Set X) := by
    intro n hn
    rw [mem_normalizer_iff]
    intro h
    refine ⟨hconjD n hn h, fun hh => ?_⟩
    have := hconjD n⁻¹ (inv_mem hn) _ hh
    simpa [mul_assoc] using this
  set K : Subgroup X := Q ⊔ centralizer (Q : Set X) with hK
  have hKN : N ≤ normalizer (K : Set X) := fun n hn =>
    CFSG.Walter.Huppert.mem_normalizer_sup hn
      (CFSG.Walter.Huppert.normalizer_le_normalizer_centralizer Q hn)
  have hDK : D ≤ normalizer (K : Set X) := hDN.trans hKN
  have hRN : K ⊔ D ≤ N := sup_le (sup_le le_normalizer (centralizer_le_normalizer' Q)) hDN
  have hNR : N ≤ normalizer ((K ⊔ D : Subgroup X) : Set X) := fun n hn =>
    CFSG.Walter.Huppert.mem_normalizer_sup (hKN hn) (hND hn)
  have hpow : ∀ r ∈ K ⊔ D, ∃ e : ℕ, r ^ 2 ^ e ∈ K := by
    intro r hr
    have hr' : r ∈ ((D ⊔ K : Subgroup X) : Set X) := by rw [sup_comm]; exact hr
    rw [coe_mul_of_left_le_normalizer_right D K hDK] at hr'
    obtain ⟨d, hd, k, hk, rfl⟩ := hr'
    obtain ⟨e, he⟩ := hD2 ⟨d, hd⟩
    have hde : d ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
    refine ⟨e, ?_⟩
    have := inv_pow_mul_mul_pow_mem (hDK hd) hk (2 ^ e)
    rwa [hde, inv_one, one_mul] at this
  have hRK : K ⊔ D = K :=
    CFSG.Walter.Huppert.eq_sup_of_radical hQ.2.2.2 le_sup_left hRN hNR hpow
  have hA1Q : A1 ≤ Q := by
    intro x hx
    have hxK : x ∈ K := hRK ▸ (le_sup_right : D ≤ K ⊔ D) (hA1D hx)
    exact CFSG.Walter.Huppert.mem_of_mem_sup_centralizer hQ.1 hQ.2.2.1 (hWP hx.1) hxK
  by_contra hWQ
  have hQW : Q ≤ normalizer (W : Set X) := fun q hq => mem_normalizer_wcl (htc q (hQ.1 hq))
  have hQW2 : IsPGroup 2 (Q ⊔ W : Subgroup X) :=
    (P.isPGroup'.to_le hQ.1).to_sup_of_normal_right' hW2 hQW
  have hne : Q ≠ Q ⊔ W := fun h => hWQ (le_sup_right.trans h.symm.le)
  obtain ⟨x, hxQW, hxN, hxQ⟩ :=
    CFSG.Walter.Huppert.exists_mem_normalizer_not_mem hQW2 le_sup_left hne
  have hx' : x ∈ ((Q ⊔ W : Subgroup X) : Set X) := hxQW
  rw [coe_mul_of_left_le_normalizer_right Q W hQW] at hx'
  obtain ⟨q, hq, w, hw, rfl⟩ := hx'
  have hwN : w ∈ N := by
    have e : w = q⁻¹ * (q * w) := by group
    rw [e]
    exact mul_mem (inv_mem (le_normalizer hq)) hxN
  exact hxQ (mul_mem hq (hA1Q ⟨hw, hwN⟩))

theorem conj_mem_wcl_of_isAlperinSubgroup (P : Sylow 2 X) {t : X}
    (htP : t ∈ (P : Subgroup X)) (htc : ∀ x ∈ (P : Subgroup X), x * t = t * x)
    (hab : IsMulCommutative (wcl t)) {Q : Subgroup X}
    (hQ : IsAlperinSubgroup 2 (P : Subgroup X) Q) {n : X} (hn : n ∈ normalizer (Q : Set X))
    {x : X} (hx : x ∈ wcl t) : n⁻¹ * x * n ∈ wcl t := by
  have hWQ := wcl_le_of_isAlperinSubgroup P htP htc hab hQ
  have h := conj_mem_wcl_of_forall (c := n⁻¹) (fun y hy => by
    have hyQ := hWQ (subset_wcl t hy)
    have hyQ' : n⁻¹ * y * n⁻¹⁻¹ ∈ Q := (mem_normalizer_iff.mp (inv_mem hn) y).mp hyQ
    obtain ⟨m, rfl, -⟩ := hy
    exact ⟨n⁻¹ * m, by group, htc _ (hQ.1 hyQ')⟩) hx
  simpa using h

theorem wcl_stronglyClosed (P : Sylow 2 X) {t : X} (htP : t ∈ (P : Subgroup X))
    (htc : ∀ x ∈ (P : Subgroup X), x * t = t * x) (hab : IsMulCommutative (wcl t)) :
    wcl t ≤ P ∧ ∀ a ∈ wcl t, ∀ g : X, g⁻¹ * a * g ∈ (P : Subgroup X) → g⁻¹ * a * g ∈ wcl t :=
  ⟨wcl_le_sylow P htP htc hab,
    CFSG.ClassicalInvolution.Disconnected.AschTight.S1916.stronglyClosed_of_alperin P
      (wcl_le_sylow P htP htc hab) fun _ hQ _ hn _ hx =>
        conj_mem_wcl_of_isAlperinSubgroup P htP htc hab hQ hn hx.1⟩

end Sylow

end CFSG.LargeExtraspecial.S11
