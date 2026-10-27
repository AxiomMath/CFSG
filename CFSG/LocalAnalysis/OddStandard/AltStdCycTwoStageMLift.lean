module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecGenLiftB
public import CFSG.LocalAnalysis.SignalizerFunctor.Maximality

public section

namespace CFSG.OddStandard.AltStdCycTwo.StageM

open Subgroup AltStdSec

section Conj

variable {N : Type*} [Group N]

private theorem exists_conj_of_involutions {P : Subgroup N} (hP : ∀ x ∈ P, Odd (orderOf x))
    {u v : N} (hu : u * u = 1) (hv : v * v = 1) (huv : v * u ∈ P) :
    ∃ r ∈ P, r * u * r⁻¹ = v := by
  have hv1 : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  have hu1 : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hvvu : v * (v * u) = u := by rw [← mul_assoc, hv, one_mul]
  have hinv : v * (v * u) * v⁻¹ = (v * u)⁻¹ := by
    rw [hvvu, mul_inv_rev, hu1, hv1]
  obtain ⟨r, hr, hrr, hvr⟩ := exists_sq_root_inverted (hP _ huv) hinv
  have hrP : r ∈ P := (zpowers_le.2 huv) hr
  have hvr' : v * r = r⁻¹ * v := mul_inv_eq_iff_eq_mul.1 hvr
  refine ⟨r, hrP, ?_⟩
  calc r * u * r⁻¹ = r * (v * (v * u)) * r⁻¹ := by rw [hvvu]
    _ = r * (v * (r * r)) * r⁻¹ := by rw [hrr]
    _ = r * ((v * r) * r) * r⁻¹ := by group
    _ = r * ((r⁻¹ * v) * r) * r⁻¹ := by rw [hvr']
    _ = v := by group

private theorem comm_mul_of_commute {w₁ w₂ a c : N} (h1c : Commute w₁ c) (h12 : Commute w₁ w₂)
    (h2a : Commute w₂ a) :
    (a * w₁) * (c * w₂) * (a * w₁)⁻¹ * (c * w₂)⁻¹ = a * c * a⁻¹ * c⁻¹ := by
  calc (a * w₁) * (c * w₂) * (a * w₁)⁻¹ * (c * w₂)⁻¹
      = a * (w₁ * c) * w₂ * w₁⁻¹ * a⁻¹ * w₂⁻¹ * c⁻¹ := by group
    _ = a * (c * w₁) * w₂ * w₁⁻¹ * a⁻¹ * w₂⁻¹ * c⁻¹ := by rw [h1c.eq]
    _ = a * c * (w₁ * w₂) * w₁⁻¹ * a⁻¹ * w₂⁻¹ * c⁻¹ := by group
    _ = a * c * (w₂ * w₁) * w₁⁻¹ * a⁻¹ * w₂⁻¹ * c⁻¹ := by rw [h12.eq]
    _ = a * c * (w₂ * a⁻¹) * w₂⁻¹ * c⁻¹ := by group
    _ = a * c * (a⁻¹ * w₂) * w₂⁻¹ * c⁻¹ := by rw [h2a.inv_right.eq]
    _ = a * c * a⁻¹ * c⁻¹ := by group

theorem sq_eq_one_and_exists_conj {O : Subgroup N} [O.Normal]
    (hO : ∀ x ∈ O, Odd (orderOf x)) {z b : N} (hz : z * z = 1) (hb : b * b = 1)
    (hzb : z * b = b * z) {m : ℕ} (hm : 4 ≤ m) {K : Subgroup (N ⧸ O)}
    (eK : K ≃* alternatingGroup (Fin m))
    (hKK : ∀ a ∈ K, ∀ c ∈ K, a * ((z : N ⧸ O) * c * (z : N ⧸ O)⁻¹) =
      ((z : N ⧸ O) * c * (z : N ⧸ O)⁻¹) * a) {a : N ⧸ O} (ha : a ∈ K)
    (hab : (b : N ⧸ O) = a * ((z : N ⧸ O) * a * (z : N ⧸ O)⁻¹)) :
    a * a = 1 ∧ ∃ g : N, g * b = b * g ∧ g * z * g⁻¹ = z * b := by
  obtain ⟨zq, hzq⟩ : ∃ zq : N ⧸ O, (z : N ⧸ O) = zq := ⟨_, rfl⟩
  rw [hzq] at hKK hab
  have hbq2 : (b : N ⧸ O) * (b : N ⧸ O) = 1 := by
    rw [← QuotientGroup.mk_mul, hb, QuotientGroup.mk_one]
  have haa' : a * (zq * a * zq⁻¹) = (zq * a * zq⁻¹) * a := hKK a ha a ha
  have ha2 : a * a = 1 := by
    have h1 : (a * a) * (zq * (a * a) * zq⁻¹) = 1 := by
      calc (a * a) * (zq * (a * a) * zq⁻¹)
          = a * (a * (zq * a * zq⁻¹)) * (zq * a * zq⁻¹) := by group
        _ = a * ((zq * a * zq⁻¹) * a) * (zq * a * zq⁻¹) := by rw [haa']
        _ = (a * (zq * a * zq⁻¹)) * (a * (zq * a * zq⁻¹)) := by group
        _ = 1 := by rw [← hab]; exact hbq2
    have h2 : zq * (a * a) * zq⁻¹ = (a * a)⁻¹ := eq_inv_of_mul_eq_one_right h1
    have hcen : (⟨a * a, mul_mem ha ha⟩ : K) ∈ center K := by
      rw [Subgroup.mem_center_iff]
      intro c
      apply Subtype.ext
      have h3 := hKK c c.2 (a * a) (mul_mem ha ha)
      rw [h2] at h3
      show (c : N ⧸ O) * (a * a) = (a * a) * c
      calc (c : N ⧸ O) * (a * a) = (a * a) * ((a * a)⁻¹ * c) * (a * a) := by group
        _ = (a * a) * ((c : N ⧸ O) * (a * a)⁻¹) * (a * a) := by rw [← h3]
        _ = (a * a) * c := by group
    rw [center_eq_bot_of_alt hm eK] at hcen
    exact congrArg Subtype.val (Subgroup.mem_bot.1 hcen)
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  obtain ⟨g₀, hg₀⟩ := QuotientGroup.mk_surjective a
  have hab' : a * (b : N ⧸ O) = (b : N ⧸ O) * a := by
    rw [hab]
    calc a * (a * (zq * a * zq⁻¹)) = a * ((zq * a * zq⁻¹) * a) := by rw [haa']
      _ = (a * (zq * a * zq⁻¹)) * a := by group
  have hmem : g₀ * b * g₀⁻¹ * b⁻¹ ∈ O := by
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hg₀, hab']
    group
  obtain ⟨g₁, hg₁b, hg₁q⟩ : ∃ g₁ : N, g₁ * b = b * g₁ ∧ (g₁ : N ⧸ O) = a := by
    obtain ⟨p, hpO, hpc⟩ := exists_mul_mem_centralizer hO hb hmem
    refine ⟨p * g₀, mem_centralizer_singleton_iff.1 hpc, ?_⟩
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff p).2 hpO, one_mul, hg₀]
  have hu2 : (g₁ * z * g₁⁻¹) * (g₁ * z * g₁⁻¹) = 1 := by
    calc (g₁ * z * g₁⁻¹) * (g₁ * z * g₁⁻¹) = g₁ * (z * z) * g₁⁻¹ := by group
      _ = 1 := by rw [hz]; group
  have hv2 : (b * z) * (b * z) = 1 := by
    calc (b * z) * (b * z) = b * (z * b) * z := by group
      _ = b * (b * z) * z := by rw [hzb]
      _ = (b * b) * (z * z) := by group
      _ = 1 := by rw [hb, hz, one_mul]
  have huq : ((g₁ * z * g₁⁻¹ : N) : N ⧸ O) = ((b * z : N) : N ⧸ O) := by
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hg₁q, hab, hzq, hai]
    group
  have hg₁b' : g₁⁻¹ * b = b * g₁⁻¹ := by
    calc g₁⁻¹ * b = g₁⁻¹ * (b * g₁) * g₁⁻¹ := by group
      _ = g₁⁻¹ * (g₁ * b) * g₁⁻¹ := by rw [← hg₁b]
      _ = b * g₁⁻¹ := by group
  have hub : (g₁ * z * g₁⁻¹) * b = b * (g₁ * z * g₁⁻¹) := by
    calc (g₁ * z * g₁⁻¹) * b = g₁ * z * (g₁⁻¹ * b) := by group
      _ = g₁ * z * (b * g₁⁻¹) := by rw [hg₁b']
      _ = g₁ * (z * b) * g₁⁻¹ := by group
      _ = g₁ * (b * z) * g₁⁻¹ := by rw [hzb]
      _ = (g₁ * b) * z * g₁⁻¹ := by group
      _ = (b * g₁) * z * g₁⁻¹ := by rw [hg₁b]
      _ = b * (g₁ * z * g₁⁻¹) := by group
  have hvu : (b * z) * (g₁ * z * g₁⁻¹) ∈ O ⊓ centralizer ({b} : Set N) := by
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, huq, ← QuotientGroup.mk_mul, hv2,
        QuotientGroup.mk_one]
    · rw [mem_centralizer_singleton_iff]
      calc (b * z) * (g₁ * z * g₁⁻¹) * b = b * z * ((g₁ * z * g₁⁻¹) * b) := by group
        _ = b * z * (b * (g₁ * z * g₁⁻¹)) := by rw [hub]
        _ = b * (z * b) * (g₁ * z * g₁⁻¹) := by group
        _ = b * (b * z) * (g₁ * z * g₁⁻¹) := by rw [hzb]
        _ = b * ((b * z) * (g₁ * z * g₁⁻¹)) := by group
  obtain ⟨r, hrP, hr⟩ := exists_conj_of_involutions (P := O ⊓ centralizer ({b} : Set N))
    (fun x hx => hO x (Subgroup.mem_inf.1 hx).1) hu2 hv2 hvu
  have hrb : r * b = b * r := mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hrP).2
  refine ⟨ha2, r * g₁, ?_, ?_⟩
  · calc r * g₁ * b = r * (g₁ * b) := by group
      _ = r * (b * g₁) := by rw [hg₁b]
      _ = (r * b) * g₁ := by group
      _ = (b * r) * g₁ := by rw [hrb]
      _ = b * (r * g₁) := by group
  · calc r * g₁ * z * (r * g₁)⁻¹ = r * (g₁ * z * g₁⁻¹) * r⁻¹ := by group
      _ = b * z := hr
      _ = z * b := hzb.symm

end Conj

section Four

variable {N : Type*} [Group N] [Finite N]

theorem commute_of_conj_four {O : Subgroup N} [O.Normal] (hOodd : Odd (Nat.card O))
    {z b g : N} (hz : z * z = 1) (hb : b * b = 1) (hzb : z * b = b * z) (hz1 : z ≠ 1)
    (hb1 : b ≠ 1) (hbz : b ≠ z) (hgb : g * b = b * g) (hgz : g * z * g⁻¹ = z * b)
    (hCz : ∀ u ∈ O, z * u * z⁻¹ = u → u * b = b * u) : ∀ u ∈ O, u * b = b * u := by
  classical
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have e1 : z * (z * b) = b := by rw [← mul_assoc, hz, one_mul]
  have e2 : b * (z * b) = z := by rw [hzb, ← mul_assoc, hb, one_mul]
  have e3 : z * b * z = b := by rw [hzb, mul_assoc, hz, mul_one]
  have e4 : z * b * b = z := by rw [mul_assoc, hb, mul_one]
  have e5 : z * b * (z * b) = 1 := by rw [← mul_assoc, e3, hb]
  have e6 : b * z = z * b := hzb.symm
  have hV4 : ∀ x ∈ closure ({z, b} : Set N), x = 1 ∨ x = z ∨ x = b ∨ x = z * b := by
    intro x hx
    induction hx using closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx
      · exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr (Or.inl hx))
    | one => exact Or.inl rfl
    | mul x y _ _ hx hy =>
      rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy <;> rw [hx, hy] <;>
        simp only [one_mul, mul_one, hz, hb, e1, e2, e3, e4, e5, e6, eq_self_iff_true, true_or,
          or_true]
    | inv x _ hx =>
      rcases hx with hx | hx | hx | hx <;> rw [hx] <;>
        simp only [inv_one, hzi, hbi, mul_inv_rev, e6, eq_self_iff_true, true_or, or_true]
  have hsq : ∀ x ∈ closure ({z, b} : Set N), x ^ 2 = 1 := by
    intro x hx
    rw [sq]
    rcases hV4 x hx with h | h | h | h <;> rw [h]
    · exact mul_one 1
    · exact hz
    · exact hb
    · exact e5
  have hinv : ∀ x ∈ closure ({z, b} : Set N), x⁻¹ = x := fun x hx =>
    inv_eq_of_mul_eq_one_left (by rw [← sq]; exact hsq x hx)
  have hcomm : ∀ x ∈ closure ({z, b} : Set N), ∀ y ∈ closure ({z, b} : Set N),
      x * y = y * x := by
    intro x hx y hy
    have h := hinv _ (mul_mem hx hy)
    rw [mul_inv_rev, hinv x hx, hinv y hy] at h
    exact h.symm
  have hzb1 : z * b ≠ 1 := fun h => hbz ((eq_inv_of_mul_eq_one_right h).trans hzi)
  have hzbz : z * b ≠ z := fun h => hb1 (by simpa using h)
  have hzbb : z * b ≠ b := fun h => hz1 (by simpa using h)
  have hcard : 2 ^ (1 + 1) ≤ Nat.card (closure ({z, b} : Set N)) := by
    have hsub : ({1, z, b, z * b} : Set N) ⊆ (closure ({z, b} : Set N) : Set N) := by
      intro x hx
      rw [SetLike.mem_coe]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with h | h | h | h <;> rw [h]
      · exact one_mem _
      · exact subset_closure (by simp)
      · exact subset_closure (by simp)
      · exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
    have hn1 : (1 : N) ∉ ({z, b, z * b} : Set N) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hz1.symm, hb1.symm, hzb1.symm⟩
    have hn2 : z ∉ ({b, z * b} : Set N) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hbz.symm, hzbz.symm⟩
    have h4 : ({1, z, b, z * b} : Set N).ncard = 2 + 1 + 1 := by
      rw [Set.ncard_insert_of_notMem hn1 (Set.toFinite _),
        Set.ncard_insert_of_notMem hn2 (Set.toFinite _), Set.ncard_pair hzbb.symm]
    calc 2 ^ (1 + 1) = 2 + 1 + 1 := by norm_num
      _ = ({1, z, b, z * b} : Set N).ncard := h4.symm
      _ ≤ ((closure ({z, b} : Set N) : Subgroup N) : Set N).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = Nat.card (closure ({z, b} : Set N)) := (Nat.card_coe_set_eq _).symm
  have hnorm : closure ({z, b} : Set N) ≤ normalizer (O : Set N) := by
    rw [normalizer_eq_top_iff.2 ‹O.Normal›]
    exact le_top
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 1
    Nat.prime_two (closure ({z, b} : Set N)) O
    ⟨⟨⟨fun x y => Subtype.ext (hcomm x x.2 y y.2)⟩⟩, hsq⟩ hcard hnorm
    (Nat.coprime_two_left.2 hOodd)
  have hOle : O ≤ centralizer ({b} : Set N) := by
    rw [← hgen]
    refine iSup₂_le fun S hS => ?_
    obtain ⟨hSV, hScard⟩ := hS
    have hSne : S ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hScard
      norm_num at hScard
    obtain ⟨⟨s, hsS⟩, hs1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hSne
    have hs1' : s ≠ 1 := fun h => hs1 (Subtype.ext h)
    intro x hx
    obtain ⟨hxO, hxS⟩ := Subgroup.mem_inf.1 hx
    have hsx : s * x = x * s := mem_centralizer_iff.1 hxS s hsS
    rw [mem_centralizer_singleton_iff]
    rcases hV4 s (hSV hsS) with h | h | h | h
    · exact absurd h hs1'
    · rw [h] at hsx
      exact hCz x hxO (by rw [hsx]; group)
    · rw [h] at hsx
      exact hsx.symm
    · rw [h] at hsx
      have hzg : z * g⁻¹ = g⁻¹ * (z * b) := by
        calc z * g⁻¹ = g⁻¹ * (g * z * g⁻¹) := by group
          _ = g⁻¹ * (z * b) := by rw [hgz]
      have hgz' : (z * b) * g = g * z := by
        calc (z * b) * g = (g * z * g⁻¹) * g := by rw [hgz]
          _ = g * z := by group
      have hyO : g⁻¹ * x * g ∈ O := by
        have := (inferInstance : O.Normal).conj_mem x hxO g⁻¹
        simpa using this
      have hyz : z * (g⁻¹ * x * g) * z⁻¹ = g⁻¹ * x * g := by
        have h1 : z * (g⁻¹ * x * g) = (g⁻¹ * x * g) * z := by
          calc z * (g⁻¹ * x * g) = (z * g⁻¹) * x * g := by group
            _ = g⁻¹ * ((z * b) * x) * g := by rw [hzg]; group
            _ = g⁻¹ * (x * (z * b)) * g := by rw [hsx]
            _ = g⁻¹ * x * ((z * b) * g) := by group
            _ = g⁻¹ * x * (g * z) := by rw [hgz']
            _ = (g⁻¹ * x * g) * z := by group
        rw [h1]; group
      have hyb := hCz _ hyO hyz
      have hgb' : g⁻¹ * b = b * g⁻¹ := by
        calc g⁻¹ * b = g⁻¹ * (b * g) * g⁻¹ := by group
          _ = g⁻¹ * (g * b) * g⁻¹ := by rw [← hgb]
          _ = b * g⁻¹ := by group
      calc x * b = g * ((g⁻¹ * x * g) * (g⁻¹ * b * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * x * g) * b) * g⁻¹ := by rw [hgb']; group
        _ = g * (b * (g⁻¹ * x * g)) * g⁻¹ := by rw [hyb]
        _ = (g * b) * g⁻¹ * x := by group
        _ = (b * g) * g⁻¹ * x := by rw [hgb]
        _ = b * x := by group
  intro u hu
  exact mem_centralizer_singleton_iff.1 (hOle hu)

theorem diag_centralizes_oddCore {O B : Subgroup N} [O.Normal] (hOodd : Odd (Nat.card O))
    {z : N} (hz : z * z = 1) (hCzB : ∀ u ∈ O, z * u * z⁻¹ = u → ∀ b ∈ B, u * b = b * u)
    {m : ℕ} (hm : 4 ≤ m) {K : Subgroup (N ⧸ O)} (eK : K ≃* alternatingGroup (Fin m))
    (hKK : ∀ a ∈ K, ∀ c ∈ K, a * ((z : N ⧸ O) * c * (z : N ⧸ O)⁻¹) =
      ((z : N ⧸ O) * c * (z : N ⧸ O)⁻¹) * a)
    {l : ℕ} (hl : 5 ≤ l) (eB : B ≃* alternatingGroup (Fin l)) (hBz : ∀ b ∈ B, z * b * z⁻¹ = b)
    (hB : ∀ g : N ⧸ O, g ∈ B.map (QuotientGroup.mk' O) ↔
      ∃ k ∈ K, g = k * ((z : N ⧸ O) * k * (z : N ⧸ O)⁻¹)) :
    ∀ b ∈ B, ∀ u ∈ O, b * u = u * b := by
  have hOodd' : ∀ x ∈ O, Odd (orderOf x) := fun x hx =>
    hOodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hx)
  obtain ⟨b₀, hb₀B, hb₀2, hb₀1⟩ : ∃ b₀ ∈ B, b₀ * b₀ = 1 ∧ b₀ ≠ 1 := by
    obtain ⟨x₀, -, -, -, hx₀, -⟩ := exists_two_involutions_of_alt (by omega) eB
    refine ⟨x₀, x₀.2, ?_, ?_⟩
    · have := pow_orderOf_eq_one x₀
      rw [hx₀, pow_two] at this
      exact congrArg Subtype.val this
    · intro h
      have : x₀ = 1 := Subtype.ext h
      rw [this, orderOf_one] at hx₀
      omega
  have hzb₀ : z * b₀ = b₀ * z := by
    calc z * b₀ = (z * b₀ * z⁻¹) * z := by group
      _ = b₀ * z := by rw [hBz b₀ hb₀B]
  have hb₀O : ∀ u ∈ O, u * b₀ = b₀ * u := by
    by_cases hz1 : z = 1
    · intro u hu
      exact hCzB u hu (by rw [hz1]; group) b₀ hb₀B
    obtain ⟨a, ha, hab⟩ := (hB (b₀ : N ⧸ O)).1 ⟨b₀, hb₀B, rfl⟩
    obtain ⟨ha2, g, hgb, hgz⟩ := sq_eq_one_and_exists_conj hOodd' hz hb₀2 hzb₀ hm eK hKK ha hab
    have hbz : b₀ ≠ z := by
      intro hbz
      rw [hbz] at hab
      have h3 : a * (z : N ⧸ O) * a = 1 := by
        calc a * (z : N ⧸ O) * a = (a * ((z : N ⧸ O) * a * (z : N ⧸ O)⁻¹)) * (z : N ⧸ O) := by
              group
          _ = (z : N ⧸ O) * (z : N ⧸ O) := by rw [← hab]
          _ = 1 := by rw [← QuotientGroup.mk_mul, hz, QuotientGroup.mk_one]
      have h2 : (z : N ⧸ O) = 1 := by
        calc (z : N ⧸ O) = a⁻¹ * (a * (z : N ⧸ O) * a) * a⁻¹ := by group
          _ = (a * a)⁻¹ := by rw [h3]; group
          _ = 1 := by rw [ha2, inv_one]
      have hzO : z ∈ O := (QuotientGroup.eq_one_iff z).1 h2
      have hzo : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz) hz1
      have h4 := hOodd' z hzO
      rw [hzo] at h4
      exact (Nat.not_odd_iff_even.2 even_two) h4
    exact commute_of_conj_four hOodd hz hb₀2 hzb₀ hz1 hb₀1 hbz hgb hgz
      (fun u hu hzu => hCzB u hu hzu b₀ hb₀B)
  have hsimple : IsSimpleGroup B := isSimpleGroup_of_alt hl eB
  have hb₀C : (⟨b₀, hb₀B⟩ : B) ∈ (centralizer (O : Set N)).subgroupOf B := by
    rw [Subgroup.mem_subgroupOf, mem_centralizer_iff]
    exact hb₀O
  rcases hsimple.eq_bot_or_eq_top_of_normal ((centralizer (O : Set N)).subgroupOf B) with h | h
  · exfalso
    rw [h] at hb₀C
    exact hb₀1 (congrArg Subtype.val (Subgroup.mem_bot.1 hb₀C))
  · intro b hb u hu
    have hbC : (⟨b, hb⟩ : B) ∈ (centralizer (O : Set N)).subgroupOf B := by
      rw [h]; exact Subgroup.mem_top _
    rw [Subgroup.mem_subgroupOf, mem_centralizer_iff] at hbC
    exact (hbC u hu).symm

theorem exists_wreath_lift_weak {O B : Subgroup N} [O.Normal] (hOodd : Odd (Nat.card O))
    {z : N} (hz : z * z = 1) (hCzB : ∀ u ∈ O, z * u * z⁻¹ = u → ∀ b ∈ B, u * b = b * u)
    {m : ℕ} (hm : 8 ≤ m) {K : Subgroup (N ⧸ O)} (eK : K ≃* alternatingGroup (Fin m))
    (hKK : ∀ a ∈ K, ∀ c ∈ K, a * ((z : N ⧸ O) * c * (z : N ⧸ O)⁻¹) =
      ((z : N ⧸ O) * c * (z : N ⧸ O)⁻¹) * a)
    {l : ℕ} (hl : 5 ≤ l) (eB : B ≃* alternatingGroup (Fin l)) (hBz : ∀ b ∈ B, z * b * z⁻¹ = b)
    (hB : ∀ g : N ⧸ O, g ∈ B.map (QuotientGroup.mk' O) ↔
      ∃ k ∈ K, g = k * ((z : N ⧸ O) * k * (z : N ⧸ O)⁻¹)) :
    ∃ (Q : Subgroup N) (ψ : B →* N), Q.map (QuotientGroup.mk' O) = K ∧ ⁅Q, Q⁆ = Q ∧
      Q ⊓ O = ⊥ ∧ (∀ q ∈ Q, ∀ u ∈ O, q * u = u * q) ∧
      (∀ a ∈ Q, ∀ x ∈ zConjSub z Q, a * x = x * a) ∧ Q ⊓ zConjSub z Q = ⊥ ∧ (∀ b, ψ b ∈ Q) ∧
      Function.Injective ψ ∧ (∀ b, ψ b * (z * ψ b * z⁻¹) = b) := by
  classical
  have hBO : ∀ b ∈ B, ∀ u ∈ O, b * u = u * b :=
    diag_centralizes_oddCore hOodd hz hCzB (by omega) eK hKK hl eB hBz hB
  set π : N →* N ⧸ O := QuotientGroup.mk' O with hπ
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective O
  have hKperf : ⁅K, K⁆ = K := by
    have hc := (isQuasisimple_of_alt (by omega : 5 ≤ m) eK).1
    exact Subgroup.isPerfect_iff.1 ⟨hc⟩
  have hBperf : ⁅B, B⁆ = B := Subgroup.isPerfect_iff.1 ⟨(isQuasisimple_of_alt hl eB).1⟩
  have hDbar : ((centralizer (O : Set N)).map π).Normal :=
    (inferInstance : (centralizer (O : Set N)).Normal).map π hπsurj
  have hBD : B.map π ≤ (centralizer (O : Set N)).map π :=
    Subgroup.map_mono fun b hb => mem_centralizer_iff.2 fun u hu => (hBO b hb u hu).symm
  have hKD : K ≤ (centralizer (O : Set N)).map π := by
    refine le_of_comm_mem hKperf fun k₁ hk₁ k₂ hk₂ => ?_
    have hd : k₂ * ((z : N ⧸ O) * k₂ * (z : N ⧸ O)⁻¹) ∈ (centralizer (O : Set N)).map π :=
      hBD ((hB _).2 ⟨k₂, hk₂, rfl⟩)
    have hc := hKK k₁ hk₁ k₂ hk₂
    have h1 : k₁ * k₂ * k₁⁻¹ * k₂⁻¹ =
        (k₁ * (k₂ * ((z : N ⧸ O) * k₂ * (z : N ⧸ O)⁻¹)) * k₁⁻¹) *
          (k₂ * ((z : N ⧸ O) * k₂ * (z : N ⧸ O)⁻¹))⁻¹ := by
      calc k₁ * k₂ * k₁⁻¹ * k₂⁻¹
          = k₁ * k₂ * (k₁⁻¹ * (((z : N ⧸ O) * k₂ * (z : N ⧸ O)⁻¹) * k₁)) * k₁⁻¹ *
              ((z : N ⧸ O) * k₂ * (z : N ⧸ O)⁻¹)⁻¹ * k₂⁻¹ := by group
        _ = k₁ * k₂ * (k₁⁻¹ * (k₁ * ((z : N ⧸ O) * k₂ * (z : N ⧸ O)⁻¹))) * k₁⁻¹ *
              ((z : N ⧸ O) * k₂ * (z : N ⧸ O)⁻¹)⁻¹ * k₂⁻¹ := by rw [← hc]
        _ = _ := by group
    rw [h1]
    exact mul_mem (hDbar.conj_mem _ hd k₁) (inv_mem hd)
  obtain ⟨Q₀, hQ₀map, hQ₀perf⟩ := exists_perfect_lift
    (π.comp (centralizer (O : Set N)).subtype) K hKperf
    (by rw [MonoidHom.range_comp, Subgroup.range_subtype]; exact hKD)
  obtain ⟨Q, hQdef⟩ : ∃ Q : Subgroup N, Q = Q₀.map (centralizer (O : Set N)).subtype :=
    ⟨_, rfl⟩
  have hQmap : Q.map π = K := by rw [hQdef, Subgroup.map_map]; exact hQ₀map
  have hQperf : ⁅Q, Q⁆ = Q := by rw [hQdef, ← Subgroup.map_commutator, hQ₀perf]
  have hQO : ∀ q ∈ Q, ∀ u ∈ O, q * u = u * q := by
    intro q hq u hu
    rw [hQdef] at hq
    obtain ⟨q', -, rfl⟩ := hq
    exact (mem_centralizer_iff.1 q'.2 u hu).symm
  have hQz : ∀ a ∈ Q, ∀ b ∈ Q, a * (z * b * z⁻¹) * a⁻¹ * (z * b * z⁻¹)⁻¹ ∈ O := by
    intro a ha b hb
    have haK : π a ∈ K := hQmap ▸ ⟨a, ha, rfl⟩
    have hbK : π b ∈ K := hQmap ▸ ⟨b, hb, rfl⟩
    rw [← QuotientGroup.eq_one_iff]
    show π (a * (z * b * z⁻¹) * a⁻¹ * (z * b * z⁻¹)⁻¹) = 1
    have := hKK _ haK _ hbK
    simp only [map_mul, map_inv]
    rw [show π z = (z : N ⧸ O) from rfl]
    rw [this]; group
  have hQQz := perfect_commute_zConjSub hQperf hQO hQz
  have hQbot : Q ⊓ O = ⊥ := by
    let πQ : ↥Q →* ↥K := (π.comp Q.subtype).codRestrict K (fun q => by
      rw [← hQmap]; exact ⟨q, q.2, rfl⟩)
    let π' : ↥Q →* alternatingGroup (Fin m) := eK.toMonoidHom.comp πQ
    have hπ' : Function.Surjective π' := by
      intro a
      have h1 : (eK.symm a : N ⧸ O) ∈ Q.map π := by rw [hQmap]; exact (eK.symm a).2
      obtain ⟨q, hq, hqe⟩ := h1
      refine ⟨⟨q, hq⟩, ?_⟩
      apply eK.symm.injective
      apply Subtype.ext
      simpa [π', πQ] using hqe
    have hker_le : ∀ q : ↥Q, q ∈ π'.ker → (q : N) ∈ O := by
      intro q hq
      have h1 : eK (πQ q) = 1 := hq
      have h2 : πQ q = 1 := by simpa using h1
      have h3 : π q = 1 := congrArg Subtype.val h2
      exact (QuotientGroup.eq_one_iff (q : N)).1 h3
    have hZc : π'.ker ≤ Subgroup.center ↥Q := by
      intro q hq
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact hQO g g.2 q (hker_le q hq)
    have hodd' : Odd (Nat.card π'.ker) := by
      let ι : π'.ker →* O := MonoidHom.codRestrict ((Q.subtype).comp π'.ker.subtype) O
        (fun q => hker_le q.1 q.2)
      have hι : Function.Injective ι := by
        intro a b hab
        have h1 : ((ι a : O) : N) = ((ι b : O) : N) := congrArg Subtype.val hab
        exact Subtype.ext (Subtype.ext h1)
      exact hOodd.of_dvd_nat (Subgroup.card_dvd_of_injective ι hι)
    have : Group.IsPerfect ↥Q := Subgroup.isPerfect_iff.2 hQperf
    have hbot := ker_eq_bot_of_perfect_odd_central_cover hm π' hπ' hZc hodd'
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxQ, hxO⟩ := hx
    have hxk : (⟨x, hxQ⟩ : ↥Q) ∈ π'.ker := by
      show eK (πQ ⟨x, hxQ⟩) = 1
      have : πQ ⟨x, hxQ⟩ = 1 := Subtype.ext ((QuotientGroup.eq_one_iff x).2 hxO)
      rw [this, map_one]
    rw [hbot] at hxk
    have := congrArg Subtype.val (Subgroup.mem_bot.1 hxk)
    exact Subgroup.mem_bot.2 this
  have hQQzbot : Q ⊓ zConjSub z Q = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨hgQ, hgz⟩ := hg
    have hπg : π g ∈ K := hQmap ▸ ⟨g, hgQ, rfl⟩
    have hcen : (⟨π g, hπg⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro k
      obtain ⟨q, hq, hqk⟩ : (k : N ⧸ O) ∈ Q.map π := by rw [hQmap]; exact k.2
      apply Subtype.ext
      show (k : N ⧸ O) * π g = π g * k
      rw [← hqk, ← map_mul, ← map_mul, hQQz q hq g hgz]
    rw [center_eq_bot_of_alt (by omega : 4 ≤ m) eK] at hcen
    have h1 : π g = 1 := congrArg Subtype.val (Subgroup.mem_bot.1 hcen)
    have hgO : g ∈ O := (QuotientGroup.eq_one_iff g).1 h1
    have : g ∈ Q ⊓ O := ⟨hgQ, hgO⟩
    rwa [hQbot] at this
  let πQ : ↥Q →* ↥K := (π.comp Q.subtype).codRestrict K (fun q => by
    rw [← hQmap]; exact ⟨q, q.2, rfl⟩)
  have hπQbij : Function.Bijective πQ := by
    constructor
    · intro a b hab
      have h1 : π (a : N) = π (b : N) := congrArg Subtype.val hab
      have h2 : ((a : N)⁻¹ * (b : N)) ∈ O := by
        rw [← QuotientGroup.eq_one_iff]
        show π ((a : N)⁻¹ * (b : N)) = 1
        rw [map_mul, map_inv, h1]; group
      have h3 : ((a : N)⁻¹ * (b : N)) ∈ Q ⊓ O := ⟨Q.mul_mem (Q.inv_mem a.2) b.2, h2⟩
      rw [hQbot] at h3
      have h4 : (a : N)⁻¹ * (b : N) = 1 := h3
      exact Subtype.ext (inv_mul_eq_one.1 h4)
    · intro k
      have h1 : (k : N ⧸ O) ∈ Q.map π := by rw [hQmap]; exact k.2
      obtain ⟨q, hq, hqk⟩ := h1
      exact ⟨⟨q, hq⟩, Subtype.ext hqk⟩
  let eQ : ↥Q ≃* ↥K := MulEquiv.ofBijective πQ hπQbij
  set zq : N ⧸ O := (z : N ⧸ O) with hzq
  let δ : ↥K →* N ⧸ O := MonoidHom.mk' (fun k => (k : N ⧸ O) * (zq * k * zq⁻¹)) (fun a b => by
    have hc : (b : N ⧸ O) * (zq * (a : N ⧸ O) * zq⁻¹) = (zq * (a : N ⧸ O) * zq⁻¹) * b :=
      hKK b b.2 a a.2
    show ((a * b : ↥K) : N ⧸ O) * (zq * ((a * b : ↥K) : N ⧸ O) * zq⁻¹) =
      ((a : N ⧸ O) * (zq * a * zq⁻¹)) * ((b : N ⧸ O) * (zq * b * zq⁻¹))
    rw [Subgroup.coe_mul]
    calc ((a : N ⧸ O) * b) * (zq * ((a : N ⧸ O) * b) * zq⁻¹)
        = (a : N ⧸ O) * ((b : N ⧸ O) * (zq * a * zq⁻¹)) * (zq * b * zq⁻¹) := by group
      _ = (a : N ⧸ O) * ((zq * a * zq⁻¹) * b) * (zq * b * zq⁻¹) := by rw [hc]
      _ = ((a : N ⧸ O) * (zq * a * zq⁻¹)) * ((b : N ⧸ O) * (zq * b * zq⁻¹)) := by group)
  have hδinj : Function.Injective δ := by
    intro a b hab
    have hker : ∀ k : ↥K, δ k = 1 → k = 1 := by
      intro k hk
      have h1 : (k : N ⧸ O) * (zq * k * zq⁻¹) = 1 := hk
      have h2 : zq * (k : N ⧸ O) * zq⁻¹ = (k : N ⧸ O)⁻¹ := eq_inv_of_mul_eq_one_right h1
      have hcen : k ∈ Subgroup.center ↥K := by
        rw [Subgroup.mem_center_iff]
        intro g
        apply Subtype.ext
        have := hKK g g.2 k k.2
        rw [h2] at this
        show (g : N ⧸ O) * k = k * g
        have h3 : (g : N ⧸ O) * (k : N ⧸ O)⁻¹ = (k : N ⧸ O)⁻¹ * g := this
        calc (g : N ⧸ O) * k = k * ((k : N ⧸ O)⁻¹ * g) * k := by group
          _ = k * ((g : N ⧸ O) * (k : N ⧸ O)⁻¹) * k := by rw [← h3]
          _ = k * g := by group
      rw [center_eq_bot_of_alt (by omega : 4 ≤ m) eK] at hcen
      exact hcen
    have : δ (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, hab, inv_mul_cancel]
    exact inv_mul_eq_one.1 (hker _ this)
  have hδrange : δ.range = B.map π := by
    ext g
    rw [hB]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, k.2, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
  let eδ : ↥K ≃* ↥δ.range := MonoidHom.ofInjective hδinj
  let πB : ↥B →* ↥δ.range := (π.comp B.subtype).codRestrict δ.range (fun b => by
    rw [hδrange]; exact ⟨b, b.2, rfl⟩)
  let κ : ↥B →* ↥K := eδ.symm.toMonoidHom.comp πB
  let ψ : ↥B →* N := Q.subtype.comp (eQ.symm.toMonoidHom.comp κ)
  have hπψ : ∀ b : ↥B, π (ψ b) = (κ b : N ⧸ O) := by
    intro b
    have h1 : πQ (eQ.symm (κ b)) = κ b := eQ.apply_symm_apply (κ b)
    exact congrArg Subtype.val h1
  have hδκ : ∀ b : ↥B, δ (κ b) = π b := by
    intro b
    have h1 : eδ (κ b) = πB b := eδ.apply_symm_apply (πB b)
    exact congrArg Subtype.val h1
  have hψQ : ∀ b : ↥B, ψ b ∈ Q := fun b => (eQ.symm (κ b)).2
  have hcomm : ∀ a b : ↥B, ψ a * (z * ψ b * z⁻¹) = (z * ψ b * z⁻¹) * ψ a := fun a b =>
    hQQz _ (hψQ a) _ (mem_zConjSub.2 ⟨ψ b, hψQ b, rfl⟩)
  have hconjconj : ∀ g : N, z * (z * g * z⁻¹) * z⁻¹ = g := fun g => by
    calc z * (z * g * z⁻¹) * z⁻¹ = (z * z) * g * (z * z)⁻¹ := by group
      _ = g := by rw [hz]; group
  let xh : ↥B →* N := MonoidHom.mk' (fun b => ψ b * (z * ψ b * z⁻¹)) (fun a b => by
    have hc := hcomm b a
    show ψ (a * b) * (z * ψ (a * b) * z⁻¹) =
      (ψ a * (z * ψ a * z⁻¹)) * (ψ b * (z * ψ b * z⁻¹))
    rw [map_mul]
    calc ψ a * ψ b * (z * (ψ a * ψ b) * z⁻¹)
        = ψ a * (ψ b * (z * ψ a * z⁻¹)) * (z * ψ b * z⁻¹) := by group
      _ = ψ a * ((z * ψ a * z⁻¹) * ψ b) * (z * ψ b * z⁻¹) := by rw [hc]
      _ = (ψ a * (z * ψ a * z⁻¹)) * (ψ b * (z * ψ b * z⁻¹)) := by group)
  have hxπ : ∀ b : ↥B, π (xh b) = π b := by
    intro b
    show π (ψ b * (z * ψ b * z⁻¹)) = π b
    rw [map_mul, map_mul, map_mul, map_inv, hπψ]
    exact hδκ b
  have hxO : ∀ b : ↥B, ∀ u ∈ O, Commute (xh b) u := by
    intro b u hu
    have h1 : Commute (ψ b) u := hQO (ψ b) (hψQ b) u hu
    have h2 : Commute (z * ψ b * z⁻¹) u :=
      zConjSub_centralizes (z := z) hQO _ (mem_zConjSub.2 ⟨ψ b, hψQ b, rfl⟩) u hu
    exact h1.mul_left h2
  have hdef : ∀ b : ↥B, ∃ w ∈ O, (∀ u ∈ O, Commute w u) ∧ xh b = (b : N) * w := by
    intro b
    refine ⟨(b : N)⁻¹ * xh b, ?_, fun u hu => ?_, by group⟩
    · rw [← QuotientGroup.eq_one_iff]
      show π ((b : N)⁻¹ * xh b) = 1
      rw [map_mul, map_inv, hxπ]; group
    · exact (Commute.inv_left (show Commute (b : N) u from hBO b b.2 u hu)).mul_left (hxO b u hu)
  have hT : B ≤ (MonoidHom.eqLocus xh B.subtype).map B.subtype := by
    refine le_of_comm_mem hBperf (fun a ha c hc => ?_)
    refine ⟨⟨a, ha⟩ * ⟨c, hc⟩ * ⟨a, ha⟩⁻¹ * ⟨c, hc⟩⁻¹, ?_, rfl⟩
    show xh (⟨a, ha⟩ * ⟨c, hc⟩ * ⟨a, ha⟩⁻¹ * ⟨c, hc⟩⁻¹) = a * c * a⁻¹ * c⁻¹
    obtain ⟨wa, hwaO, hwac, hwa⟩ : ∃ w ∈ O, (∀ u ∈ O, Commute w u) ∧ xh ⟨a, ha⟩ = a * w :=
      hdef ⟨a, ha⟩
    obtain ⟨wc, hwcO, -, hwc⟩ : ∃ w ∈ O, (∀ u ∈ O, Commute w u) ∧ xh ⟨c, hc⟩ = c * w :=
      hdef ⟨c, hc⟩
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hwa, hwc]
    exact comm_mul_of_commute (hBO c hc wa hwaO).symm (hwac wc hwcO) (hBO a ha wc hwcO).symm
  have hxeq : ∀ b : ↥B, xh b = (b : N) := by
    intro b
    obtain ⟨b', hb', hbb⟩ := hT b.2
    have : b' = b := Subtype.ext hbb
    rw [← this]; exact hb'
  refine ⟨Q, ψ, hQmap, hQperf, hQbot, hQO, hQQz, hQQzbot, hψQ, ?_, ?_⟩
  · intro a b hab
    have h1 : xh a = xh b := by
      show ψ a * (z * ψ a * z⁻¹) = ψ b * (z * ψ b * z⁻¹)
      rw [hab]
    rw [hxeq a, hxeq b] at h1
    exact Subtype.ext h1
  · intro b
    exact hxeq b

end Four

end CFSG.OddStandard.AltStdCycTwo.StageM
