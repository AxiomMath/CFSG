module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldModel
public import CFSG.LocalAnalysis.OddStandard.ChengHeldChartShape

public section

namespace CFSG.OddStandard.ChengHeld

open Subgroup CFSG.OddStandard.ChengHeldData CFSG.OddStandard.ChengHeld.Model
open CFSG.OddStandard.ChengHeld.ChartShape
  (cm_eq_one_iff cj_mul cj_of_commute cj_mem_of_closure cj_mem_of_closure_left)
open scoped commutatorElement

section Generic

variable {G : Type*} [Group G]

theorem mem_closure_triple_invol {a b c : G} (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1)
    (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b) {v : G}
    (hv : v ∈ closure ({a, b, c} : Set G)) :
    v = 1 ∨ v = a ∨ v = b ∨ v = a * b ∨ v = c ∨ v = a * c ∨ v = b * c ∨ v = a * b * c := by
  have ha' : ∀ x : G, a * (a * x) = x := fun x => by rw [← mul_assoc, ha, one_mul]
  have hb' : ∀ x : G, b * (b * x) = x := fun x => by rw [← mul_assoc, hb, one_mul]
  have hc' : ∀ x : G, c * (c * x) = x := fun x => by rw [← mul_assoc, hc, one_mul]
  have hba : b * a = a * b := hab.symm
  have hca : c * a = a * c := hac.symm
  have hcb : c * b = b * c := hbc.symm
  have hba' : ∀ x : G, b * (a * x) = a * (b * x) := fun x => by
    rw [← mul_assoc, hba, mul_assoc]
  have hca' : ∀ x : G, c * (a * x) = a * (c * x) := fun x => by
    rw [← mul_assoc, hca, mul_assoc]
  have hcb' : ∀ x : G, c * (b * x) = b * (c * x) := fun x => by
    rw [← mul_assoc, hcb, mul_assoc]
  have hinv : ∀ x : G, x * x = 1 → x⁻¹ = x := fun x hx => inv_eq_of_mul_eq_one_right hx
  induction hv using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> simp
  | one => exact Or.inl rfl
  | mul x y _ _ hx hy =>
    rcases hx with hx | hx | hx | hx | hx | hx | hx | hx <;>
    rcases hy with hy | hy | hy | hy | hy | hy | hy | hy <;>
    subst x <;> subst y <;>
    simp only [mul_assoc, ha, hb, hc, ha', hb', hba, hca, hcb, hba', hca', hcb', mul_one,
      one_mul, true_or, or_true]
  | inv x _ hx =>
    rcases hx with hx | hx | hx | hx | hx | hx | hx | hx <;> subst x <;>
    simp only [mul_inv_rev, hinv a ha, hinv b hb, hinv c hc, inv_one, mul_assoc, hba, hca, hcb,
      hba', true_or, or_true]

@[expose] def twc (z s : G) : G := s⁻¹ * (z⁻¹ * s * z)

theorem twc_mul (z s1 s2 : G) : twc z (s1 * s2) = s2⁻¹ * twc z s1 * s2 * twc z s2 := by
  unfold twc; group

theorem cj_eq_twc_mul {z : G} (hz2 : z * z = 1) (s : G) : cj z s = twc z s * z := by
  have hinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  unfold cj twc
  rw [hinv]
  simp only [mul_assoc, hz2, mul_one]

theorem graph_coset_conj {t p u m l w x z : G} (fr : Frame4 0 t p u m l w x)
    (ht : ∀ s ∈ closure ({t, p, u, m, l, w, x} : Set G), s * t = t * s)
    (hz : Kind.graph.Act 0 t p u m l w x z) (hz2 : z * z = 1)
    {v : G} (hv : v ∈ closure ({t ^ 2, p, t * u} : Set G)) :
    ∃ s ∈ closure ({t, p, u, m, l, w, x} : Set G), cj z s = v * z := by
  set S0 : Subgroup G := closure ({t, p, u, m, l, w, x} : Set G) with hS0
  have mt : t ∈ S0 := subset_closure (by simp)
  have mp : p ∈ S0 := subset_closure (by simp)
  have mu : u ∈ S0 := subset_closure (by simp)
  have mm : m ∈ S0 := subset_closure (by simp)
  have ml : l ∈ S0 := subset_closure (by simp)
  have mw : w ∈ S0 := subset_closure (by simp)
  have mx : x ∈ S0 := subset_closure (by simp)
  unfold Kind.Act at hz
  simp only [↓reduceIte, cj] at hz
  obtain ⟨hzt, hzp, hzu, hzm, hzl, hzw, hzx⟩ := hz
  have ht4 : t ^ 4 = 1 := fr.t4
  have hq2 : t ^ 2 * t ^ 2 = 1 := by rw [← pow_add]; exact ht4
  have hp2 : p * p = 1 := by rw [← pow_two]; exact fr.pi2
  have hm2 : m * m = 1 := by rw [← pow_two]; exact fr.mu2
  have hl2 : l * l = 1 := by rw [← pow_two]; exact fr.lam2
  have hw2 : w * w = 1 := by rw [← pow_two]; exact fr.ze2
  have hx2 : x * x = 1 := by rw [← pow_two]; exact fr.xi2
  have hu2 : u * u = t ^ 2 := by rw [← pow_two]; exact fr.tau_sq
  have hmi : m⁻¹ = m := inv_eq_of_mul_eq_one_right hm2
  have hli : l⁻¹ = l := inv_eq_of_mul_eq_one_right hl2
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have cpu : p * u = u * p := (cm_eq_one_iff.1 fr.pi_tau).eq
  have cum : u * m = m * u := (cm_eq_one_iff.1 fr.tau_mu).eq
  have cwx : w * x = x * w := (cm_eq_one_iff.1 fr.ze_xi).eq
  have hcp : p * t = t * p := ht p mp
  have hcu : u * t = t * u := ht u mu
  have hq : ∀ s ∈ S0, s * t ^ 2 = t ^ 2 * s := fun s hs => (Commute.pow_right (ht s hs) 2).eq
  have hqc : ∀ s ∈ S0, s⁻¹ * t ^ 2 * s = t ^ 2 := fun s hs => by
    rw [mul_assoc, ← hq s hs, ← mul_assoc, inv_mul_cancel, one_mul]
  have hpm : m * p * m = t ^ 2 * p := by
    have := fr.pi_mu; unfold cj at this; rwa [hmi] at this
  have hpl : l * p * l = t ^ 2 * p := by
    have := fr.pi_lam; unfold cj at this; rwa [hli] at this
  have hpw : w * p * w = t ^ 2 * p := by
    have := fr.pi_ze; unfold cj at this; rwa [hwi] at this
  have hxl : x⁻¹ * l * x = l * u := by
    have := fr.lam_xi; unfold cm at this
    calc x⁻¹ * l * x = l * (l⁻¹ * x⁻¹ * l * x) := by group
      _ = l * u := by rw [this]
  have hxm : x⁻¹ * m * x = m * (p * u) := by
    have := fr.mu_xi; unfold cm at this
    calc x⁻¹ * m * x = m * (m⁻¹ * x⁻¹ * m * x) := by group
      _ = m * (p * u) := by rw [this]
  have hB1 : twc z t = t ^ 2 := by
    unfold twc
    rw [hzt]
    have ht3 : t⁻¹ = t ^ 3 := by
      rw [inv_eq_iff_mul_eq_one]
      calc t * t ^ 3 = t ^ 4 := by rw [← pow_succ']
        _ = 1 := ht4
    rw [ht3, ← pow_add]
    calc t ^ (3 + 3) = t ^ 2 * t ^ 4 := by rw [← pow_add]
      _ = t ^ 2 := by rw [ht4, mul_one]
  have hc1 : Commute t p := hcp.symm
  have hc2 : Commute t u := hcu.symm
  have hc3 : Commute p u := cpu
  have hB2 : twc z (l * w) = t * p * u := by
    have e1 : twc z (l * w) = (cm l w)⁻¹ := by
      unfold twc cm
      have : z⁻¹ * (l * w) * z = (z⁻¹ * l * z) * (z⁻¹ * w * z) := by group
      rw [this, hzl, hzw]; group
    rw [e1, fr.lam_ze]
    have h2 : (t * p * u) ^ 2 = 1 := by
      rw [Commute.mul_pow (Commute.mul_left hc2 hc3), Commute.mul_pow hc1, fr.pi2, fr.tau_sq,
        mul_one]
      exact hq2
    simp only [mul_zero, pow_zero, mul_one]
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact h2)
  have hB3 : twc z (m * l * x) = t ^ 2 * p := by
    unfold twc
    have e : z⁻¹ * (m * l * x) * z = (z⁻¹ * m * z) * (z⁻¹ * l * z) * (z⁻¹ * x * z) := by group
    rw [e, hzm, hzl, hzx]
    have s1 : (m * l * x)⁻¹ = x⁻¹ * l * m := by
      simp only [mul_inv_rev, hmi, hli, mul_assoc]
    have hwxw : w * x * w = x := by
      calc w * x * w = x * w * w := by rw [cwx]
        _ = x := by rw [mul_assoc, hw2, mul_one]
    have s2 : t ^ 2 * w * x * w * (t ^ 2 * m * l) = x * (m * l) := by
      have hmem : w * x * w ∈ S0 := mul_mem (mul_mem mw mx) mw
      calc t ^ 2 * w * x * w * (t ^ 2 * m * l)
          = t ^ 2 * ((w * x * w) * t ^ 2) * (m * l) := by simp only [mul_assoc]
        _ = t ^ 2 * (t ^ 2 * (w * x * w)) * (m * l) := by rw [hq _ hmem]
        _ = (t ^ 2 * t ^ 2) * ((w * x * w) * (m * l)) := by simp only [mul_assoc]
        _ = x * (m * l) := by rw [hq2, one_mul, hwxw]
    rw [s1, s2]
    have hlmp : l * m * p ∈ S0 := mul_mem (mul_mem ml mm) mp
    have cum' : ∀ X : G, u * (m * X) = m * (u * X) := fun X => by
      rw [← mul_assoc, cum, mul_assoc]
    calc x⁻¹ * l * m * (x * (m * l))
        = (x⁻¹ * l * x) * (x⁻¹ * m * x) * (m * l) := by group
      _ = (l * u) * (m * (p * u)) * (m * l) := by rw [hxl, hxm]
      _ = l * m * (u * p) * u * m * l := by simp only [mul_assoc, cum']
      _ = l * m * p * (u * u) * m * l := by rw [← cpu]; simp only [mul_assoc]
      _ = (l * m * p * t ^ 2) * m * l := by rw [hu2]
      _ = (t ^ 2 * (l * m * p)) * m * l := by rw [hq _ hlmp]
      _ = t ^ 2 * (l * (m * p * m) * l) := by simp only [mul_assoc]
      _ = t ^ 2 * (l * (t ^ 2 * p) * l) := by rw [hpm]
      _ = t ^ 2 * ((l * t ^ 2) * p * l) := by simp only [mul_assoc]
      _ = t ^ 2 * ((t ^ 2 * l) * p * l) := by rw [hq l ml]
      _ = t ^ 2 * (t ^ 2 * (l * p * l)) := by simp only [mul_assoc]
      _ = t ^ 2 * (t ^ 2 * (t ^ 2 * p)) := by rw [hpl]
      _ = t ^ 2 * p := by rw [← mul_assoc (t ^ 2), hq2, one_mul]
  have hC2 : (l * w)⁻¹ * p * (l * w) = p := by
    calc (l * w)⁻¹ * p * (l * w) = w⁻¹ * (l⁻¹ * p * l) * w := by group
      _ = w * (l * p * l) * w := by rw [hwi, hli]
      _ = w * (t ^ 2 * p) * w := by rw [hpl]
      _ = (w * t ^ 2) * p * w := by simp only [mul_assoc]
      _ = (t ^ 2 * w) * p * w := by rw [hq w mw]
      _ = t ^ 2 * (w * p * w) := by simp only [mul_assoc]
      _ = t ^ 2 * (t ^ 2 * p) := by rw [hpw]
      _ = p := by rw [← mul_assoc, hq2, one_mul]
  have hwl : l * w ∈ S0 := mul_mem ml mw
  have hmlx : m * l * x ∈ S0 := mul_mem (mul_mem mm ml) mx
  have hTt : ∀ s ∈ S0, twc z (t * s) = t ^ 2 * twc z s := fun s hs => by
    rw [twc_mul, hB1, hqc s hs]
  have hB4 : twc z ((m * l * x) * (l * w)) = t ^ 2 * (t * u) := by
    rw [twc_mul, hB3, hB2]
    have : (l * w)⁻¹ * (t ^ 2 * p) * (l * w) = t ^ 2 * p := by
      calc (l * w)⁻¹ * (t ^ 2 * p) * (l * w)
          = ((l * w)⁻¹ * t ^ 2 * (l * w)) * ((l * w)⁻¹ * p * (l * w)) := by group
        _ = t ^ 2 * p := by rw [hqc _ hwl, hC2]
    rw [this]
    calc t ^ 2 * p * (t * p * u) = t ^ 2 * (p * t) * p * u := by simp only [mul_assoc]
      _ = t ^ 2 * (t * p) * p * u := by rw [hcp]
      _ = t ^ 2 * t * (p * p) * u := by simp only [mul_assoc]
      _ = t ^ 2 * (t * u) := by rw [hp2, mul_one, mul_assoc]
  have key : ∀ s ∈ S0, ∀ v', twc z s = v' → ∃ s ∈ S0, cj z s = v' * z := fun s hs v' h =>
    ⟨s, hs, by rw [cj_eq_twc_mul hz2, h]⟩
  have hc : t * u * (t * u) = 1 := by
    rw [← pow_two, Commute.mul_pow hc2, fr.tau_sq]
    exact hq2
  have hab : t ^ 2 * p = p * t ^ 2 := (hq p mp).symm
  have hac : t ^ 2 * (t * u) = (t * u) * t ^ 2 := (hq (t * u) (mul_mem mt mu)).symm
  have hbc : p * (t * u) = (t * u) * p := by
    calc p * (t * u) = (p * t) * u := by rw [mul_assoc]
      _ = (t * p) * u := by rw [hcp]
      _ = t * (p * u) := by rw [mul_assoc]
      _ = t * (u * p) := by rw [cpu]
      _ = (t * u) * p := by rw [mul_assoc]
  rcases mem_closure_triple_invol hq2 hp2 hc hab hac hbc hv with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact key 1 (one_mem _) 1 (by simp [twc])
  · exact key t mt _ hB1
  · refine key (t * (m * l * x)) (mul_mem mt hmlx) _ ?_
    rw [hTt _ hmlx, hB3, ← mul_assoc, hq2, one_mul]
  · exact key (m * l * x) hmlx _ hB3
  · refine key (t * ((m * l * x) * (l * w))) (mul_mem mt (mul_mem hmlx hwl)) _ ?_
    rw [hTt _ (mul_mem hmlx hwl), hB4, ← mul_assoc, hq2, one_mul]
  · exact key ((m * l * x) * (l * w)) (mul_mem hmlx hwl) _ hB4
  · refine key (l * w) hwl _ ?_
    rw [hB2]
    calc t * p * u = (t * p) * u := rfl
      _ = (p * t) * u := by rw [hcp]
      _ = p * (t * u) := by rw [mul_assoc]
  · refine key (t * (l * w)) (mul_mem mt hwl) _ ?_
    rw [hTt _ hwl, hB2]
    calc t ^ 2 * (t * p * u) = t ^ 2 * (t * p) * u := by simp only [mul_assoc]
      _ = t ^ 2 * (p * t) * u := by rw [hcp]
      _ = t ^ 2 * p * (t * u) := by simp only [mul_assoc]

end Generic

section Classes

variable {G : Type} [Group G]

@[expose] def IsSConj (S : Subgroup G) (a b : G) : Prop := ∃ s ∈ S, b = s⁻¹ * a * s

theorem IsSConj.symm {S : Subgroup G} {a b : G} (h : IsSConj S a b) : IsSConj S b a := by
  obtain ⟨s, hs, rfl⟩ := h
  exact ⟨s⁻¹, inv_mem hs, by group⟩

theorem IsSConj.trans {S : Subgroup G} {a b c : G} (h : IsSConj S a b) (h' : IsSConj S b c) :
    IsSConj S a c := by
  obtain ⟨s, hs, rfl⟩ := h
  obtain ⟨s', hs', rfl⟩ := h'
  exact ⟨s * s', mul_mem hs hs', by group⟩

theorem ClassSizes.isSConj_of_single {S : Subgroup G} {y : G} {n : ℕ} (h : ClassSizes S y [n])
    {a b : G} (ha : ∃ s ∈ S, a = s * y) (ha2 : a * a = 1) (hb : ∃ s ∈ S, b = s * y)
    (hb2 : b * b = 1) : IsSConj S a b := by
  obtain ⟨reps, -, hsz, -, hcov⟩ := h
  obtain ⟨r, rfl⟩ : ∃ r, reps = [r] :=
    List.length_eq_one_iff.1 (by simpa using congrArg List.length hsz)
  obtain ⟨ra, hra, hAa⟩ := hcov a ha ha2
  obtain ⟨rb, hrb, hBb⟩ := hcov b hb hb2
  simp only [List.mem_singleton] at hra hrb
  rw [hra] at hAa
  rw [hrb] at hBb
  exact (show IsSConj S r a from hAa).symm.trans (show IsSConj S r b from hBb)

theorem ClassSizes.isSConj_of_two {S : Subgroup G} {y : G} {n₁ n₂ : ℕ}
    (h : ClassSizes S y [n₁, n₂]) {a b : G} (ha : ∃ s ∈ S, a = s * y) (ha2 : a * a = 1)
    (hb : ∃ s ∈ S, b = s * y) (hb2 : b * b = 1) (hab : ¬ IsSConj S a b) {z : G}
    (hz : ∃ s ∈ S, z = s * y) (hz2 : z * z = 1) : IsSConj S a z ∨ IsSConj S b z := by
  obtain ⟨reps, -, hsz, -, hcov⟩ := h
  obtain ⟨r₁, r₂, rfl⟩ : ∃ r₁ r₂, reps = [r₁, r₂] := by
    have : reps.length = 2 := by simpa using congrArg List.length hsz
    match reps, this with
    | [r₁, r₂], _ => exact ⟨r₁, r₂, rfl⟩
  obtain ⟨ra, hra, hAa⟩ := hcov a ha ha2
  obtain ⟨rb, hrb, hBb⟩ := hcov b hb hb2
  obtain ⟨rz, hrz, hZz⟩ := hcov z hz hz2
  have hA : IsSConj S ra a := hAa
  have hB : IsSConj S rb b := hBb
  have hZ : IsSConj S rz z := hZz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hra hrb hrz
  rcases hra with rfl | rfl <;> rcases hrb with rfl | rfl <;> rcases hrz with rfl | rfl <;>
  first
    | exact absurd (hA.symm.trans hB) hab
    | exact Or.inl (hA.symm.trans hZ)
    | exact Or.inr (hB.symm.trans hZ)

end Classes

section Commutators

variable {H : Type*} [Group H]

theorem commutatorElement_mul_left' (a b c : H) :
    ⁅a * b, c⁆ = a * ⁅b, c⁆ * a⁻¹ * ⁅a, c⁆ := by
  simp only [commutatorElement_def]; group

end Commutators

section Charts

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A}

theorem Chart2.coset_classes_S (c : Chart2 d) (h : Hyp G A) (hP : chPresOK = true)
    (hQ : chPropsOK = true) (k : Kind) {y : G} (hy : y ∈ d.X)
    (hact : k.Act2 d.q c.pi c.tau c.mu c.lam c.ze c.xi y) (hy2 : y * y = 1) {z : G}
    (hz : ∃ s ∈ d.S, z = s * y) (hz2 : z * z = 1) :
    ∃ s ∈ d.S, cj z s = y ∨ cj z s = d.q * y := by
  have hA := c.autFactsG h hP hQ k hy hact
  have hcl := hA.coset_classes hy2
  have hfl := hA.flag hy2
  have hq : qOfG 2 c.famG = d.q := by simp [qOfG, Chart2.famG]
  rw [hq] at hfl
  have hyS : ∃ s ∈ d.S, y = s * y := ⟨1, one_mem _, (one_mul y).symm⟩
  have hqS : d.q ∈ d.S := c.mem.2.2.2.2.2.2
  have hcq : cj d.q y = d.q := by cases k <;> exact hact.1
  have hqy : y * d.q = d.q * y := by
    unfold cj at hcq
    calc y * d.q = y * (y⁻¹ * d.q * y) := by rw [hcq]
      _ = d.q * y := by group
  have hq2 : d.q * d.q = 1 := by
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.1 (by simp [d.q_ord])
  have hqy2 : (d.q * y) * (d.q * y) = 1 := by
    calc d.q * y * (d.q * y) = d.q * (y * d.q) * y := by simp only [mul_assoc]
      _ = d.q * (d.q * y) * y := by rw [hqy]
      _ = (d.q * d.q) * (y * y) := by simp only [mul_assoc]
      _ = 1 := by rw [hq2, hy2, mul_one]
  have hqyS : ∃ s ∈ d.S, d.q * y = s * y := ⟨d.q, hqS, rfl⟩
  cases k with
  | unitary =>
    have h1 : (autData 2 (kind0 Kind.unitary)).2.2.1 = [16] := by decide
    rw [h1] at hcl
    obtain ⟨s, hs, e⟩ := hcl.isSConj_of_single hyS hy2 hz hz2
    exact ⟨s⁻¹, inv_mem hs, Or.inl (by rw [e]; unfold cj; group)⟩
  | field =>
    have h1 : (autData 2 (kind0 Kind.field)).2.2.1 = [8, 8] := by decide
    have h2 : (autData 2 (kind0 Kind.field)).2.2.2 = false := by decide
    rw [h1] at hcl
    rw [h2] at hfl
    have hab : ¬ IsSConj d.S y (d.q * y) := fun ⟨s, hs, e⟩ =>
      absurd (hfl.1 ⟨s, hs, e.symm⟩) (by simp)
    rcases hcl.isSConj_of_two hyS hy2 hqyS hqy2 hab hz hz2 with ⟨s, hs, e⟩ | ⟨s, hs, e⟩
    · exact ⟨s⁻¹, inv_mem hs, Or.inl (by rw [e]; unfold cj; group)⟩
    · exact ⟨s⁻¹, inv_mem hs, Or.inr (by rw [e]; unfold cj; group)⟩
  | graph =>
    have h1 : (autData 2 (kind0 Kind.graph)).2.2.1 = [16, 16] := by decide
    have h2 : (autData 2 (kind0 Kind.graph)).2.2.2 = false := by decide
    rw [h1] at hcl
    rw [h2] at hfl
    have hab : ¬ IsSConj d.S y (d.q * y) := fun ⟨s, hs, e⟩ =>
      absurd (hfl.1 ⟨s, hs, e.symm⟩) (by simp)
    rcases hcl.isSConj_of_two hyS hy2 hqyS hqy2 hab hz hz2 with ⟨s, hs, e⟩ | ⟨s, hs, e⟩
    · exact ⟨s⁻¹, inv_mem hs, Or.inl (by rw [e]; unfold cj; group)⟩
    · exact ⟨s⁻¹, inv_mem hs, Or.inr (by rw [e]; unfold cj; group)⟩

theorem Chart4.coset_conj_unitary {α : ℕ} (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A)
    (hP : chPresOK = true) (hQ : chPropsOK = true) {y : G} (hy : y ∈ d.X)
    (hact : Kind.unitary.Act α c.t c.pi c.tau c.mu c.lam c.ze c.xi y) (hy2 : y * y = 1)
    {a b : G} (ha : ∃ s ∈ d.S, a = s * y) (ha2 : a * a = 1) (hb : ∃ s ∈ d.S, b = s * y)
    (hb2 : b * b = 1) : ∃ s ∈ d.S, cj a s = b := by
  have hcl := (c.autFactsG hα h hP hQ Kind.unitary hy hact).coset_classes hy2
  have h1 : (autData α (kind0 Kind.unitary)).2.2.1 = [32] := by
    interval_cases α <;> decide
  rw [h1] at hcl
  obtain ⟨s, hs, e⟩ := hcl.isSConj_of_single ha ha2 hb hb2
  exact ⟨s, hs, e.symm⟩

theorem Chart4.t_comm {α : ℕ} (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A)
    (hP : chPresOK = true) (hQ : chPropsOK = true) : ∀ s ∈ d.S, s * c.t = c.t * s := fun s hs => by
  have ht : c.t ∈ d.S ⊓ centralizer (d.S : Set G) := by
    rw [(c.sFacts hα h hP hQ).center]; exact mem_zpowers _
  exact mem_centralizer_iff.1 ht.2 s hs

theorem Chart4.alpha_eq_zero_of_graph {α : ℕ} (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A)
    (hP : chPresOK = true) (hQ : chPropsOK = true) {z : G}
    (hz : Kind.graph.Act α c.t c.pi c.tau c.mu c.lam c.ze c.xi z) (hzt : cj c.t z = c.t⁻¹) :
    α = 0 := by
  have hS := c.sFacts hα h hP hQ
  by_contra hne
  have h1 : α = 1 := by omega
  subst h1
  have h2 : cj c.t z = c.t := by
    simp [Kind.Act] at hz
    exact hz.1
  rw [h2] at hzt
  have h3 : c.t ^ 2 = 1 := by rw [pow_two]; exact mul_eq_one_iff_eq_inv.2 hzt
  have h4 : orderOf c.t ∣ 2 := orderOf_dvd_of_pow_eq_one h3
  rw [hS.ord_t] at h4
  omega

theorem Chart4.coset_conj_graph {α : ℕ} (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A)
    (hP : chPresOK = true) (hQ : chPropsOK = true) {z : G}
    (hz : Kind.graph.Act α c.t c.pi c.tau c.mu c.lam c.ze c.xi z) (hz2 : z * z = 1)
    (hzt : cj c.t z = c.t⁻¹) : ∀ v ∈ c.V, ∃ s ∈ d.S, cj z s = v * z := by
  have hS := c.sFacts hα h hP hQ
  have hα0 := c.alpha_eq_zero_of_graph hα h hP hQ hz hzt
  subst hα0
  have hcen : ∀ s ∈ d.S, s * c.t = c.t * s := fun s hs => by
    have ht : c.t ∈ d.S ⊓ centralizer (d.S : Set G) := by
      rw [hS.center]; exact mem_zpowers _
    exact mem_centralizer_iff.1 ht.2 s hs
  intro v hv
  have hv' : v ∈ closure ({c.t ^ 2, c.pi, c.t * c.tau} : Set G) := by
    unfold Chart4.V at hv; rwa [c.q_eq] at hv
  have hcen' : ∀ s ∈ closure ({c.t, c.pi, c.tau, c.mu, c.lam, c.ze, c.xi} : Set G),
      s * c.t = c.t * s := by
    rw [c.gen]; exact hcen
  obtain ⟨s, hs, hsz⟩ := graph_coset_conj c.frame hcen' hz hz2 hv'
  exact ⟨s, by rwa [c.gen] at hs, hsz⟩

theorem Chart4.graph_fixes_V {α : ℕ} (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A)
    (hP : chPresOK = true) (hQ : chPropsOK = true) {z : G}
    (hz : Kind.graph.Act α c.t c.pi c.tau c.mu c.lam c.ze c.xi z) :
    ∀ v ∈ c.V, z⁻¹ * v * z = v := by
  have hcen := c.t_comm hα h hP hQ
  have ht4 : c.t ^ 4 = 1 := c.frame.t4
  have hu2 : c.tau ^ 2 = c.t ^ 2 := c.frame.tau_sq
  have hcut : c.tau * c.t = c.t * c.tau := hcen c.tau c.mem.2.1
  have hq2 : c.t ^ 2 * c.t ^ 2 = 1 := by rw [← pow_add]; exact ht4
  have htu : (c.t * c.tau) * (c.t * c.tau) = 1 := by
    calc c.t * c.tau * (c.t * c.tau) = c.t * (c.tau * c.t) * c.tau := by simp only [mul_assoc]
      _ = c.t * (c.t * c.tau) * c.tau := by rw [hcut]
      _ = c.t ^ 2 * c.tau ^ 2 := by simp only [pow_two, mul_assoc]
      _ = 1 := by rw [hu2, ← pow_add]; exact ht4
  have e : z⁻¹ * (c.t * c.tau) * z = (z⁻¹ * c.t * z) * (z⁻¹ * c.tau * z) := by group
  have e2 : z⁻¹ * c.t ^ 2 * z = (z⁻¹ * c.t * z) ^ 2 := by rw [pow_two, pow_two]; group
  have key : z⁻¹ * c.t ^ 2 * z = c.t ^ 2 ∧ z⁻¹ * c.pi * z = c.pi ∧
      z⁻¹ * (c.t * c.tau) * z = c.t * c.tau := by
    interval_cases α
    · unfold Kind.Act at hz
      simp only [↓reduceIte, cj] at hz
      obtain ⟨hzt', hzp, hzu, -⟩ := hz
      refine ⟨?_, hzp, ?_⟩
      · rw [e2, hzt', inv_pow, inv_eq_of_mul_eq_one_right hq2]
      · rw [e, hzt', hzu, ← mul_inv_rev, hcut, inv_eq_of_mul_eq_one_right htu]
    · have hz1 : cj c.t z = c.t ∧ cj c.pi z = c.pi ∧ cj c.tau z = c.tau := by
        simp [Kind.Act] at hz
        exact ⟨hz.1, hz.2.1, hz.2.2.1⟩
      obtain ⟨hzt', hzp, hzu⟩ := hz1
      refine ⟨?_, hzp, ?_⟩
      · rw [e2]; exact congrArg (· ^ 2) hzt'
      · rw [e]; exact congrArg₂ (· * ·) hzt' hzu
  intro v hv
  unfold Chart4.V at hv
  induction hv using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · rw [c.q_eq]; exact key.1
    · exact key.2.1
    · exact key.2.2
  | one => simp
  | mul a b _ _ ha hb =>
    calc z⁻¹ * (a * b) * z = (z⁻¹ * a * z) * (z⁻¹ * b * z) := by group
      _ = a * b := by rw [ha, hb]
  | inv a _ ha =>
    calc z⁻¹ * a⁻¹ * z = (z⁻¹ * a * z)⁻¹ := by group
      _ = a⁻¹ := by rw [ha]

theorem Chart4.centralizer_graph_eq_V {α : ℕ} (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A)
    (hP : chPresOK = true) (hQ : chPropsOK = true) {z : G} (hzX : z ∈ d.X)
    (hz : Kind.graph.Act α c.t c.pi c.tau c.mu c.lam c.ze c.xi z) (hzt : cj c.t z = c.t⁻¹) :
    ∀ s ∈ d.S, (cj s z = s ↔ s ∈ c.V) := by
  have hS := c.sFacts hα h hP hQ
  have hα0 := c.alpha_eq_zero_of_graph hα h hP hQ hz hzt
  have hA := c.autFactsG hα h hP hQ Kind.graph hzX hz
  have hVfix := c.graph_fixes_V hα h hP hQ hz
  subst hα0
  have hVS : c.V ≤ d.S := by
    unfold Chart4.V
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact d.q_mem_S h
    · exact c.mem.1
    · exact d.S.mul_mem c.t_mem.2 c.mem.2.1
  intro s hs
  constructor
  · intro hcs
    have hF : {x : G | x ∈ d.S ∧ z⁻¹ * x * z = x}.ncard = 8 := by
      rw [hA.fixed_card]; decide
    have hVF : (c.V : Set G) ⊆ {x : G | x ∈ d.S ∧ z⁻¹ * x * z = x} := fun v hv =>
      ⟨hVS hv, hVfix v hv⟩
    have hVcard : (c.V : Set G).ncard = 8 := by
      rw [← Nat.card_coe_set_eq]; exact hS.card_V
    have heq := Set.eq_of_subset_of_ncard_le hVF (by rw [hF, hVcard])
    have hmem : s ∈ {x : G | x ∈ d.S ∧ z⁻¹ * x * z = x} := ⟨hs, hcs⟩
    rw [← heq] at hmem
    exact hmem
  · intro hv
    exact hVfix s hv

theorem Chart4.W_pow_four {α : ℕ} (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A)
    (hP : chPresOK = true) (hQ : chPropsOK = true) : ∀ a ∈ c.W, a ^ 4 = 1 := by
  have hS := c.sFacts hα h hP hQ
  intro a ha
  have hdvd : orderOf a ∣ 2 ^ 6 := by
    have h1 : orderOf (⟨a, ha⟩ : c.W) ∣ Nat.card c.W := orderOf_dvd_natCard _
    rw [hS.card_W] at h1
    have h2 : orderOf (⟨a, ha⟩ : c.W) = orderOf a := Subgroup.orderOf_mk a ha
    rw [h2] at h1
    exact h1
  obtain ⟨k, hk, hka⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  by_contra hne
  have hk3 : 3 ≤ k := by
    by_contra hlt
    have : orderOf a ∣ 4 := by
      rw [hka]
      exact (Nat.pow_dvd_pow 2 (by omega : k ≤ 2) : 2 ^ k ∣ 2 ^ 2)
    exact hne (orderOf_dvd_iff_pow_eq_one.1 this)
  have hb : a ^ (2 ^ (k - 3)) ∈ c.W := pow_mem ha _
  have hdv : 2 ^ (k - 3) ∣ orderOf a := by
    rw [hka]; exact Nat.pow_dvd_pow 2 (by omega)
  have hord : orderOf (a ^ (2 ^ (k - 3))) = 8 := by
    rw [orderOf_pow_of_dvd (by positivity) hdv, hka, Nat.pow_div (by omega) (by norm_num)]
    have : k - (k - 3) = 3 := by omega
    rw [this]
  exact hS.W_ord8 _ hb hord

theorem Chart2.sq_mlxt (c : Chart2 d) (h : Hyp G A) (hP : chPresOK = true)
    (hQ : chPropsOK = true) : (c.mu * c.lam * c.xi * c.tau) ^ 2 = c.pi := by
  have hS := c.sFacts h hP hQ
  have htau : c.tau ∈ d.S ⊓ centralizer (d.S : Set G) := by
    rw [hS.center]
    unfold Chart2.D
    exact subset_closure (by simp)
  have hmlx : c.mu * c.lam * c.xi ∈ d.S :=
    mul_mem (mul_mem c.mem.2.2.1 c.mem.2.2.2.1) c.mem.2.2.2.2.2.1
  have hcomm : Commute (c.mu * c.lam * c.xi) c.tau := mem_centralizer_iff.1 htau.2 _ hmlx
  rw [hcomm.mul_pow, hS.sq_mlx, c.frame.ord.2.2.1, mul_one]

theorem Chart4.cj_V_mem {α : ℕ} (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A)
    (hP : chPresOK = true) (hQ : chPropsOK = true) : ∀ s ∈ d.S, ∀ v ∈ c.V, cj v s ∈ c.V := by
  have hcen := c.t_comm hα h hP hQ
  have fr := c.frame
  have mq : c.t ^ 2 ∈ c.V := by
    rw [← c.q_eq]; exact subset_closure (by simp)
  have mp : c.pi ∈ c.V := subset_closure (by simp)
  have mtu : c.t * c.tau ∈ c.V := subset_closure (by simp)
  have hq' : ∀ s ∈ d.S, Commute (c.t ^ 2) s := fun s hs =>
    (Commute.pow_left (hcen s hs).symm 2)
  have hgS : ∀ g ∈ ({c.t, c.pi, c.tau, c.mu, c.lam, c.ze, c.xi} : Set G), g ∈ d.S := by
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact c.t_mem.2
    · exact c.mem.1
    · exact c.mem.2.1
    · exact c.mem.2.2.1
    · exact c.mem.2.2.2.1
    · exact c.mem.2.2.2.2.1
    · exact c.mem.2.2.2.2.2
  have cPT : Commute c.pi c.tau := cm_eq_one_iff.1 fr.pi_tau
  have cTM : Commute c.tau c.mu := cm_eq_one_iff.1 fr.tau_mu
  have hpi : ∀ g ∈ ({c.t, c.pi, c.tau, c.mu, c.lam, c.ze, c.xi} : Set G), cj c.pi g ∈ c.V := by
    intro g hg
    have hg' := hgS g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [cj_of_commute (hcen _ c.mem.1)]; exact mp
    · rw [cj_of_commute (Commute.refl _)]; exact mp
    · rw [cj_of_commute cPT]; exact mp
    · rw [fr.pi_mu]; exact mul_mem mq mp
    · rw [fr.pi_lam]; exact mul_mem mq mp
    · rw [fr.pi_ze]; exact mul_mem mq mp
    · rw [fr.pi_xi]; exact mp
  have htu : ∀ g ∈ ({c.t, c.pi, c.tau, c.mu, c.lam, c.ze, c.xi} : Set G),
      cj (c.t * c.tau) g ∈ c.V := by
    intro g hg
    have hg' := hgS g hg
    have ht : cj c.t g = c.t := cj_of_commute (hcen g hg').symm
    rw [cj_mul, ht]
    have e : ∀ x : G, c.t * (c.t ^ 2 * x) = c.t ^ 2 * (c.t * x) := fun x => by
      simp only [← mul_assoc, ← pow_succ, ← pow_succ']
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [cj_of_commute (hcen _ c.mem.2.1)]; exact mtu
    · rw [cj_of_commute cPT.symm]; exact mtu
    · rw [cj_of_commute (Commute.refl _)]; exact mtu
    · rw [cj_of_commute cTM]; exact mtu
    · rw [fr.tau_lam, e]; exact mul_mem mq mtu
    · rw [fr.tau_ze, e]; exact mul_mem mq mtu
    · rw [fr.tau_xi, e]; exact mul_mem mq mtu
  have key : ∀ g ∈ ({c.t, c.pi, c.tau, c.mu, c.lam, c.ze, c.xi} : Set G), ∀ v ∈ c.V,
      cj v g ∈ c.V := by
    intro g hg
    refine cj_mem_of_closure_left g ?_
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · rw [c.q_eq, cj_of_commute (hq' g (hgS g hg))]; exact mq
    · exact hpi g hg
    · exact htu g hg
  intro s hs v hv
  rw [← c.gen] at hs
  exact cj_mem_of_closure key s hs v hv

end Charts

end CFSG.OddStandard.ChengHeld
