module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3FourEightElation
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3FourEightInputs

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3.FourEight

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.Open
open CFSG.SignalizerFunctor.Helpers
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]
variable {G T S Q H : Subgroup X} {g y : X}

omit [Finite X] in
theorem isSylowOf_rightConjugate' [Finite X] {p : ℕ} [Fact p.Prime] {P K : Subgroup X}
    (hP : IsSylowOf p P K) (x : X) :
    IsSylowOf p (rightConjugate P x) (rightConjugate K x) := by
  apply isSylowOf_of_card (rightConjugate_le_rightConjugate hP.le x)
  rw [rightConjugate_card, rightConjugate_card, CFSG.ABGLocalTools.IsSylowOf.card_eq hP]

omit [Finite X] in
theorem rightConjugate_inf_centralizer {G : Subgroup X} {x z w : X} (hx : x ∈ G)
    (hxw : x⁻¹ * w * x = z) :
    rightConjugate (G ⊓ Subgroup.centralizer {z}) x⁻¹ = G ⊓ Subgroup.centralizer {w} := by
  ext u
  rw [mem_rightConjugate_iff, inv_inv, Subgroup.mem_inf, Subgroup.mem_inf,
    Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff, ← hxw]
  constructor
  · rintro ⟨hu, hc⟩
    refine ⟨?_, ?_⟩
    · have := G.mul_mem (G.mul_mem hx hu) (G.inv_mem hx)
      simpa [mul_assoc] using this
    · have h1 : x⁻¹ * (u * w) * x = x⁻¹ * (w * u) * x := by
        calc x⁻¹ * (u * w) * x = (x⁻¹ * u * x) * (x⁻¹ * w * x) := by group
          _ = (x⁻¹ * w * x) * (x⁻¹ * u * x) := hc
          _ = x⁻¹ * (w * u) * x := by group
      exact mul_left_cancel (mul_right_cancel h1)
  · rintro ⟨hu, hc⟩
    refine ⟨G.mul_mem (G.mul_mem (G.inv_mem hx) hu) hx, ?_⟩
    calc (x⁻¹ * u * x) * (x⁻¹ * w * x) = x⁻¹ * (u * w) * x := by group
      _ = x⁻¹ * (w * u) * x := by rw [hc]
      _ = (x⁻¹ * w * x) * (x⁻¹ * u * x) := by group

namespace ElemCtx

theorem Z_le_P (c : ElemCtx G T S Q H g y) : (T ⊔ rightConjugate T g) ⊓ G ≤ S ⊓ G :=
  inf_le_inf_right G c.elem.M_le_S

theorem cosetSub_facts (c : ElemCtx G T S Q H g y) {w : X} (hwS : w ∈ S) (hwG : w ∈ G)
    (hwW : w ∉ rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) (hw2 : w ^ 2 = 1)
    (hwA : ∀ a ∈ (T ⊔ rightConjugate T g) ⊓ G ⊓ Subgroup.centralizer (S : Set X), a * w = w * a) :
    cosetSub ((T ⊔ rightConjugate T g) ⊓ G ⊓ Subgroup.centralizer (S : Set X)) w hw2 hwA ≤
        S ⊓ G ∧
      cosetSub ((T ⊔ rightConjugate T g) ⊓ G ⊓ Subgroup.centralizer (S : Set X)) w hw2 hwA ≤
        G ⊓ Subgroup.centralizer {w} ∧
      (∀ x ∈ cosetSub ((T ⊔ rightConjugate T g) ⊓ G ⊓ Subgroup.centralizer (S : Set X)) w hw2
        hwA, x ^ 2 = 1) ∧
      Nat.card (cosetSub ((T ⊔ rightConjugate T g) ⊓ G ⊓ Subgroup.centralizer (S : Set X)) w hw2
        hwA) = 2 * Nat.card ((T ⊔ rightConjugate T g) ⊓ G ⊓
          Subgroup.centralizer (S : Set X) : Subgroup X) := by
  have e := c.elem
  set A := (T ⊔ rightConjugate T g) ⊓ G ⊓ Subgroup.centralizer (S : Set X) with hAdef
  have hww : w * w = 1 := by rw [← pow_two, hw2]
  have hAP : A ≤ S ⊓ G := inf_le_left.trans c.Z_le_P
  have hEab := cosetSub_comm hw2 hwA c.A_comm'
  have hwE := mem_cosetSub_self hw2 hwA
  have hwA' : w ∉ A := fun h => hwW (Subgroup.mem_sup_right h.1.1)
  refine ⟨?_, ?_, ?_, card_cosetSub hw2 hwA hwA'⟩
  · intro x hx
    rcases hx with hx | hx
    · exact hAP hx
    · have := Subgroup.mul_mem _ (⟨hwS, hwG⟩ : w ∈ S ⊓ G) (hAP hx)
      simpa using this
  · intro x hx
    have hxP : x ∈ S ⊓ G := by
      rcases hx with hx' | hx'
      · exact hAP hx'
      · have := Subgroup.mul_mem _ (⟨hwS, hwG⟩ : w ∈ S ⊓ G) (hAP hx')
        simpa using this
    exact ⟨hxP.2, Subgroup.mem_centralizer_singleton_iff.mpr (hEab x hx w hwE)⟩
  · intro x hx
    rcases hx with hx | hx
    · exact sq_Z e hx.1
    · obtain ⟨a, ha, rfl⟩ : ∃ a ∈ A, x = w * a := ⟨w⁻¹ * x, hx, by group⟩
      calc (w * a) ^ 2 = w * (a * w) * a := by rw [pow_two]; group
        _ = (w * w) * a ^ 2 := by rw [hwA a ha, pow_two]; group
        _ = 1 := by rw [hww, sq_Z e ha.1, one_mul]

theorem exists_normalizer_conj_mem_A (c : ElemCtx G T S Q H g y) {w : X} (hwS : w ∈ S)
    (hwG : w ∈ G) (hwW : w ∉ rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) (hw2 : w ^ 2 = 1)
    (hwA : ∀ a ∈ (T ⊔ rightConjugate T g) ⊓ G ⊓ Subgroup.centralizer (S : Set X), a * w = w * a)
    (hk : Nat.card ((T ⊔ rightConjugate T g) ⊓ G : Subgroup X) ≤
      2 * Nat.card ((T ⊔ rightConjugate T g) ⊓ G ⊓ Subgroup.centralizer (S : Set X) :
        Subgroup X))
    {x z₀ : X} (hx : x ∈ G)
    (hz₀ : z₀ ∈ (T ⊔ rightConjugate T g) ⊓ G ⊓ Subgroup.centralizer (S : Set X))
    (hxw : x⁻¹ * w * x = z₀) :
    ∃ y' ∈ G, y' ∈ Subgroup.normalizer
        (cosetSub ((T ⊔ rightConjugate T g) ⊓ G ⊓ Subgroup.centralizer (S : Set X)) w hw2 hwA :
          Set X) ∧
      y'⁻¹ * w * y' ∈ (T ⊔ rightConjugate T g) ⊓ G ⊓ Subgroup.centralizer (S : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e := c.elem
  have hP := c.isSylowOf_P
  have hNZ := c.normalizer_P_le
  have hE := c.le_normalizer_cosetSub hwS hwG hwW hw2 hwA
  obtain ⟨hEP, hEK, hE2, hEcard⟩ := c.cosetSub_facts hwS hwG hwW hw2 hwA
  have hPC : S ⊓ G ≤ G ⊓ Subgroup.centralizer {z₀} := fun p hp =>
    ⟨hp.2, Subgroup.mem_centralizer_singleton_iff.mpr (A_comm hz₀ hp.1).symm⟩
  have hPC' : IsSylowOf 2 (S ⊓ G) (G ⊓ Subgroup.centralizer {z₀}) := hP.of_le hPC inf_le_left
  have hP' := isSylowOf_rightConjugate' hPC' x⁻¹
  rw [rightConjugate_inf_centralizer hx hxw] at hP'
  obtain ⟨k, hkK, hkey⟩ := isSylowOf_exists_conj_mem hP' hEK
    (c.sylowFrame.sylow.isPGroup.to_le (hEP.trans inf_le_left))
  set x' := k * x with hx'def
  have hx' : x' ∈ G := G.mul_mem hkK.1 hx
  have hkw : k * w = w * k := Subgroup.mem_centralizer_singleton_iff.mp hkK.2
  have hx'w : x'⁻¹ * w * x' = z₀ := by
    rw [hx'def, ← hxw]
    calc (k * x)⁻¹ * w * (k * x) = x⁻¹ * (k⁻¹ * (w * k)) * x := by group
      _ = x⁻¹ * (k⁻¹ * (k * w)) * x := by rw [hkw]
      _ = x⁻¹ * w * x := by group
  set E := cosetSub ((T ⊔ rightConjugate T g) ⊓ G ⊓ Subgroup.centralizer (S : Set X)) w hw2 hwA
    with hEdef
  set U := rightConjugate E x' with hUdef
  have hUP : U ≤ S ⊓ G := by
    intro u hu
    rw [hUdef, mem_rightConjugate_iff] at hu
    have h1 := hkey _ hu
    rw [mem_rightConjugate_iff, inv_inv] at h1
    have h2 : x⁻¹ * (k⁻¹ * (x' * u * x'⁻¹) * k) * x = u := by rw [hx'def]; group
    rwa [h2] at h1
  have hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := by
    intro a ha b hb
    rw [hUdef, mem_rightConjugate_iff] at ha hb
    have h1 := cosetSub_comm hw2 hwA c.A_comm' _ ha _ hb
    have h2 : x' * (a * b) * x'⁻¹ = x' * (b * a) * x'⁻¹ := by
      calc x' * (a * b) * x'⁻¹ = (x' * a * x'⁻¹) * (x' * b * x'⁻¹) := by group
        _ = (x' * b * x'⁻¹) * (x' * a * x'⁻¹) := h1
        _ = x' * (b * a) * x'⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  have hU2 : ∀ u ∈ U, u ^ 2 = 1 := fun u hu => sq_eq_one_of_mem_rightConjugate hE2 hu
  have hUcard : 2 * Nat.card ((T ⊔ rightConjugate T g) ⊓ G ⊓ Subgroup.centralizer (S : Set X) :
      Subgroup X) ≤ Nat.card U := by
    rw [hUdef, rightConjugate_card, hEcard]
  have hPU := c.le_normalizer_of_elem hk hUP hUab hU2 hUcard
  obtain ⟨n, hn, hnE⟩ := exists_normalizer_eq_rightConjugate hP hE hx' hPU
  refine ⟨x' * n⁻¹, G.mul_mem hx' (G.inv_mem hn.1), ?_, ?_⟩
  · rw [← rightConjugate_eq_self_iff, ← rightConjugate_mul, hnE, rightConjugate_mul,
      mul_inv_cancel, rightConjugate_one]
  · have h1 : (x' * n⁻¹)⁻¹ * w * (x' * n⁻¹) = n * (x'⁻¹ * w * x') * n⁻¹ := by group
    rw [h1, hx'w]
    have hnZ : n * z₀ * n⁻¹ ∈ (T ⊔ rightConjugate T g) ⊓ G :=
      (Subgroup.mem_normalizer_iff.mp (hNZ hn) z₀).mp hz₀.1
    refine c.mem_A_of_comm hwS hwW hnZ ?_
    have hnw : n⁻¹ * w * n ∈ S ⊓ G := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn.2) w).mp ⟨hwS, hwG⟩
      simpa using this
    have h2 := A_comm hz₀ hnw.1
    calc n * z₀ * n⁻¹ * w = n * (z₀ * (n⁻¹ * w * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * w * n) * z₀) * n⁻¹ := by rw [h2]
      _ = w * (n * z₀ * n⁻¹) := by group

theorem exists_conj_mem_A (c : ElemCtx G T S Q H g y) {w : X} (hwS : w ∈ S) (hwG : w ∈ G)
    (hwW : w ∉ rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) (hw2 : w ^ 2 = 1)
    (hwA : ∀ a ∈ (T ⊔ rightConjugate T g) ⊓ G ⊓ Subgroup.centralizer (S : Set X), a * w = w * a)
    (hk : Nat.card ((T ⊔ rightConjugate T g) ⊓ G : Subgroup X) ≤
      2 * Nat.card ((T ⊔ rightConjugate T g) ⊓ G ⊓ Subgroup.centralizer (S : Set X) :
        Subgroup X))
    {x z : X} (hx : x ∈ G) (hz : z ∈ (T ⊔ rightConjugate T g) ⊓ G) (hxw : x⁻¹ * w * x = z) :
    ∃ x' ∈ G, x'⁻¹ * w * x' ∈
      (T ⊔ rightConjugate T g) ⊓ G ⊓ Subgroup.centralizer (S : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e := c.elem
  have hP := c.isSylowOf_P
  have hNZ := c.normalizer_P_le
  by_cases hzA : z ∈ (T ⊔ rightConjugate T g) ⊓ G ⊓ Subgroup.centralizer (S : Set X)
  · exact ⟨x, hx, hxw ▸ hzA⟩
  set R := (rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G with hRdef
  set C₁ := G ⊓ Subgroup.centralizer {z} with hC₁def
  have hRC : R ≤ C₁ := fun r hr =>
    ⟨hr.2, Subgroup.mem_centralizer_singleton_iff.mpr (e.Z_comm hz hr.1).symm⟩
  have hR2 : IsPGroup 2 R :=
    c.sylowFrame.sylow.isPGroup.to_le (inf_le_inf_right G e.A_le_S |>.trans inf_le_left)
  obtain ⟨D₀, hD₀⟩ := exists_isSylowOf 2 C₁
  obtain ⟨k, hkC, hkey⟩ := isSylowOf_exists_conj_mem hD₀ hRC hR2
  set D := rightConjugate D₀ k⁻¹ with hDdef
  have hD : IsSylowOf 2 D C₁ := isSylowOf_rightConjugate hD₀ (C₁.inv_mem hkC)
  have hRD : R ≤ D := by
    intro r hr
    rw [hDdef, mem_rightConjugate_iff, inv_inv]
    exact hkey r hr
  by_cases hDR : D ≤ R
  ·
    exfalso
    have hRS : IsSylowOf 2 R C₁ := by
      rw [← le_antisymm hDR hRD]
      exact hD
    have hR' := isSylowOf_rightConjugate' hRS x⁻¹
    rw [hC₁def, rightConjugate_inf_centralizer hx hxw] at hR'
    obtain ⟨hEP, hEK, hE2, hEcard⟩ := c.cosetSub_facts hwS hwG hwW hw2 hwA
    obtain ⟨k', hk', hkey'⟩ := isSylowOf_exists_conj_mem hR' hEK
      (c.sylowFrame.sylow.isPGroup.to_le (hEP.trans inf_le_left))
    set E := cosetSub ((T ⊔ rightConjugate T g) ⊓ G ⊓ Subgroup.centralizer (S : Set X)) w hw2
      hwA with hEdef
    have hEZ : E ≤ rightConjugate ((T ⊔ rightConjugate T g) ⊓ G) (k' * x)⁻¹ := by
      intro h hh
      have h1 := hkey' h hh
      rw [mem_rightConjugate_iff, inv_inv] at h1
      rw [mem_rightConjugate_iff, inv_inv]
      have h2 : (k' * x)⁻¹ * h * (k' * x) = x⁻¹ * (k'⁻¹ * h * k') * x := by group
      rw [h2]
      refine mem_Z_of_sq e h1.1 h1.2 ?_
      have h3 : (x⁻¹ * (k'⁻¹ * h * k') * x) ^ 2 = (k' * x)⁻¹ * h ^ 2 * (k' * x) := by
        rw [pow_two, pow_two]; group
      rw [h3, hE2 h hh]
      group
    have hEeq : E = rightConjugate ((T ⊔ rightConjugate T g) ⊓ G) (k' * x)⁻¹ :=
      Subgroup.eq_of_le_of_card_ge hEZ (by rw [rightConjugate_card, hEcard]; exact hk)
    have hE := c.le_normalizer_cosetSub hwS hwG hwW hw2 hwA
    rw [← hEdef, hEeq] at hE
    obtain ⟨n, hn, hnZ⟩ := exists_normalizer_eq_rightConjugate hP
      (inf_le_left.trans (S_le_normalizer_Z e)) (G.inv_mem (G.mul_mem hk'.1 hx)) hE
    rw [(rightConjugate_eq_self_iff _ _).mpr (hNZ hn), ← hEeq] at hnZ
    have hwE : w ∈ E := mem_cosetSub_self hw2 hwA
    rw [hnZ] at hwE
    exact hwW (Subgroup.mem_sup_right hwE.1)
  ·
    obtain ⟨d, hdD, hdR, hdN⟩ := exists_mem_normalizer_not_mem hD.isPGroup hRD hDR
    have hdC := hD.le hdD
    have hPN : S ⊓ G ≤ G ⊓ Subgroup.normalizer (R : Set X) :=
      le_inf inf_le_right (inf_le_left.trans (c.S_le_normalizer_R))
    have hPN' : IsSylowOf 2 (S ⊓ G) (G ⊓ Subgroup.normalizer (R : Set X)) :=
      hP.of_le hPN inf_le_left
    obtain ⟨m, hm, hmkey⟩ := isSylowOf_exists_conj_mem hPN'
      (Subgroup.zpowers_le.mpr ⟨hdC.1, hdN⟩) (hD.isPGroup.to_le (Subgroup.zpowers_le.mpr hdD))
    have hd' := hmkey d (Subgroup.mem_zpowers d)
    have hd'W : m⁻¹ * d * m ∉ rightConjugate T y ⊔ (T ⊔ rightConjugate T g) := by
      intro h
      apply hdR
      have h1 : m⁻¹ * d * m ∈ R := ⟨h, hd'.2⟩
      have := (Subgroup.mem_normalizer_iff.mp hm.2 _).mp h1
      simpa [mul_assoc] using this
    have hz' : m⁻¹ * z * m ∈ (T ⊔ rightConjugate T g) ⊓ G := by
      have := (Subgroup.mem_normalizer_iff.mp
        (c.normalizer_R_le (Subgroup.inv_mem _ hm.2)) z).mp hz
      simpa using this
    have hdz : d * z = z * d := Subgroup.mem_centralizer_singleton_iff.mp hdC.2
    have hcomm : m⁻¹ * z * m * (m⁻¹ * d * m) = m⁻¹ * d * m * (m⁻¹ * z * m) := by
      calc m⁻¹ * z * m * (m⁻¹ * d * m) = m⁻¹ * (z * d) * m := by group
        _ = m⁻¹ * (d * z) * m := by rw [hdz]
        _ = m⁻¹ * d * m * (m⁻¹ * z * m) := by group
    refine ⟨x * m, G.mul_mem hx hm.1, ?_⟩
    have h1 : (x * m)⁻¹ * w * (x * m) = m⁻¹ * (x⁻¹ * w * x) * m := by group
    rw [h1, hxw]
    exact c.mem_A_of_comm hd'.1 hd'W hz' hcomm

theorem exists_involution_of_not_weaklyClosed (c : ElemCtx G T S Q H g y) {h : X} (hh : h ∈ G)
    (hle : rightConjugate ((T ⊔ rightConjugate T g) ⊓ G) h ≤ S ⊓ G)
    (hne : rightConjugate ((T ⊔ rightConjugate T g) ⊓ G) h ≠ (T ⊔ rightConjugate T g) ⊓ G) :
    ∃ w ∈ S ⊓ G, w ∉ rightConjugate T y ⊔ (T ⊔ rightConjugate T g) ∧ w ^ 2 = 1 ∧
      Nat.card ((T ⊔ rightConjugate T g) ⊓ G : Subgroup X) ≤
        2 * Nat.card ((T ⊔ rightConjugate T g) ⊓ G ⊓ Subgroup.centralizer (S : Set X) :
          Subgroup X) ∧
      ∃ x ∈ G, x⁻¹ * w * x ∈ (T ⊔ rightConjugate T g) ⊓ G := by
  have e := c.elem
  have hZ2 : ∀ u ∈ rightConjugate ((T ⊔ rightConjugate T g) ⊓ G) h, u ^ 2 = 1 :=
    fun u hu => sq_eq_one_of_mem_rightConjugate (fun z hz => sq_Z e hz) hu
  have hZW : ∀ u ∈ rightConjugate ((T ⊔ rightConjugate T g) ⊓ G) h,
      u ∈ rightConjugate T y ⊔ (T ⊔ rightConjugate T g) → u ∈ (T ⊔ rightConjugate T g) ⊓ G :=
    fun u hu huW => mem_Z_of_sq e huW (hle hu).2 (hZ2 u hu)
  have hnW : ¬ rightConjugate ((T ⊔ rightConjugate T g) ⊓ G) h ≤
      rightConjugate T y ⊔ (T ⊔ rightConjugate T g) := by
    intro hW
    exact hne (Subgroup.eq_of_le_of_card_ge (fun u hu => hZW u hu (hW hu))
      (by rw [rightConjugate_card]))
  obtain ⟨w, hwZh, hwW⟩ := Set.not_subset.mp hnW
  have hwP := hle hwZh
  have hw2 := hZ2 w hwZh
  have hcomm : ∀ u ∈ rightConjugate ((T ⊔ rightConjugate T g) ⊓ G) h, u * w = w * u := by
    intro u hu
    have hu' := (mem_rightConjugate_iff _ _ _).mp hu
    have hw' := (mem_rightConjugate_iff _ _ _).mp hwZh
    have h1 := M_comm' e hu'.1 hw'.1
    have h2 : h * (u * w) * h⁻¹ = h * (w * u) * h⁻¹ := by
      calc h * (u * w) * h⁻¹ = (h * u * h⁻¹) * (h * w * h⁻¹) := by group
        _ = (h * w * h⁻¹) * (h * u * h⁻¹) := h1
        _ = h * (w * u) * h⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  have hint : (rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓
      rightConjugate ((T ⊔ rightConjugate T g) ⊓ G) h ≤
      (T ⊔ rightConjugate T g) ⊓ G ⊓ Subgroup.centralizer (S : Set X) := fun u hu =>
    c.mem_A_of_comm hwP.1 hwW (hZW u hu.2 hu.1) (hcomm u hu.2)
  have hrel : (rightConjugate T y ⊔ (T ⊔ rightConjugate T g)).relIndex
      (rightConjugate ((T ⊔ rightConjugate T g) ⊓ G) h) ≤ 2 := by
    have := Subgroup.relIndex_le_of_le_right (hle.trans inf_le_left)
      (Elem47.relIndex_ne_zero_of_finite (rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) S)
    rwa [e.index_eq] at this
  have hcard := Subgroup.relIndex_mul_card (rightConjugate T y ⊔ (T ⊔ rightConjugate T g))
    (rightConjugate ((T ⊔ rightConjugate T g) ⊓ G) h)
  rw [rightConjugate_card] at hcard
  have hA := Subgroup.card_le_of_le hint
  refine ⟨w, hwP, hwW, hw2, ?_, h⁻¹, G.inv_mem hh, ?_⟩
  · rw [← hcard]
    exact Nat.mul_le_mul hrel hA
  · rw [inv_inv]
    exact (mem_rightConjugate_iff _ _ _).mp hwZh

theorem exists_involution_of_weaklyClosed (c : ElemCtx G T S Q H g y) (hin : Theorem48Inputs)
    (hwc : ∀ h ∈ G, rightConjugate ((T ⊔ rightConjugate T g) ⊓ G) h ≤ S ⊓ G →
      rightConjugate ((T ⊔ rightConjugate T g) ⊓ G) h = (T ⊔ rightConjugate T g) ⊓ G)
    (hns : ∃ z ∈ (T ⊔ rightConjugate T g) ⊓ G, ∃ x ∈ G, x⁻¹ * z * x ∈ S ⊓ G ∧
      x⁻¹ * z * x ∉ (T ⊔ rightConjugate T g) ⊓ G) :
    ∃ w ∈ S ⊓ G, w ∉ rightConjugate T y ⊔ (T ⊔ rightConjugate T g) ∧ w ^ 2 = 1 ∧
      Nat.card ((T ⊔ rightConjugate T g) ⊓ G : Subgroup X) ≤
        2 * Nat.card ((T ⊔ rightConjugate T g) ⊓ G ⊓ Subgroup.centralizer (S : Set X) :
          Subgroup X) ∧
      ∃ x ∈ G, x⁻¹ * w * x ∈ (T ⊔ rightConjugate T g) ⊓ G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e := c.elem
  obtain ⟨Q₀, hQ₀⟩ := c.isSylowOf_P
  have hQeq : (Q₀ : Subgroup G) = (S ⊓ G).subgroupOf G := by
    apply Subgroup.map_injective G.subtype_injective
    rw [hQ₀, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (inf_le_right : S ⊓ G ≤ G)]
  have hmemQ : ∀ v : G, v ∈ (Q₀ : Subgroup G) ↔ (v : X) ∈ S ⊓ G := by
    intro v
    rw [hQeq, Subgroup.mem_subgroupOf]
  have hZP := c.Z_le_P
  have hVQ : ((T ⊔ rightConjugate T g) ⊓ G).subgroupOf G ≤ (Q₀ : Subgroup G) := fun v hv =>
    (hmemQ v).mpr (hZP (Subgroup.mem_subgroupOf.mp hv))
  have hVel : IsElemAbelian 2 (((T ⊔ rightConjugate T g) ⊓ G).subgroupOf G) := by
    refine ⟨?_, fun v hv => Subtype.ext (by simpa using sq_Z e (Subgroup.mem_subgroupOf.mp hv))⟩
    exact CFSG.Goldschmidt.isMulCommutative_subgroupOf
      (isMulCommutative_of_le inf_le_left e.hyp45.facts.2.2.2) G
  have hmemRC : ∀ (U : Subgroup X) (v h : G), v ∈ rightConjugate (U.subgroupOf G) h ↔
      (v : X) ∈ rightConjugate U (h : X) := by
    intro U v h
    rw [mem_rightConjugate_iff, mem_rightConjugate_iff, Subgroup.mem_subgroupOf]
    simp
  have hVwc : ∀ h : G, rightConjugate (((T ⊔ rightConjugate T g) ⊓ G).subgroupOf G) h ≤
      (Q₀ : Subgroup G) → rightConjugate (((T ⊔ rightConjugate T g) ⊓ G).subgroupOf G) h =
        ((T ⊔ rightConjugate T g) ⊓ G).subgroupOf G := by
    intro h hle
    have hle' : rightConjugate ((T ⊔ rightConjugate T g) ⊓ G) (h : X) ≤ S ⊓ G := by
      intro u hu
      have huG : u ∈ G := by
        have hu' := (mem_rightConjugate_iff _ _ _).mp hu
        have := G.mul_mem (G.mul_mem (G.inv_mem h.2) hu'.2) h.2
        simpa [mul_assoc] using this
      exact (hmemQ _).mp (hle ((hmemRC _ ⟨u, huG⟩ h).mpr hu))
    have heq := hwc h h.2 hle'
    ext v
    rw [hmemRC, heq, Subgroup.mem_subgroupOf]
  obtain ⟨v₀, hv₀, x₀, hx₀, hx₀P, hx₀Z⟩ := hns
  obtain ⟨U, hUV, h, hUhQ, hUhV, hcard⟩ := hin.goldschmidt_theorem_four G Q₀
    (((T ⊔ rightConjugate T g) ⊓ G).subgroupOf G) hVQ hVel hVwc
    ⟨⟨v₀, hv₀.2⟩, Subgroup.mem_subgroupOf.mpr hv₀, ⟨x₀, hx₀⟩, (hmemQ _).mpr (by simpa using hx₀P),
      fun h => hx₀Z (by simpa using Subgroup.mem_subgroupOf.mp h)⟩
  obtain ⟨w', hw'U, hw'V⟩ := Set.not_subset.mp hUhV
  have hU2 : ∀ u ∈ U, u ^ 2 = 1 := fun u hu => hVel.2 u (hUV hu)
  have hw'2 : w' ^ 2 = 1 := sq_eq_one_of_mem_rightConjugate hU2 hw'U
  have hwP : (w' : X) ∈ S ⊓ G := (hmemQ w').mp (hUhQ hw'U)
  have hw2 : (w' : X) ^ 2 = 1 := by simpa using congrArg Subtype.val hw'2
  have hwZ : (w' : X) ∉ (T ⊔ rightConjugate T g) ⊓ G :=
    fun h => hw'V (Subgroup.mem_subgroupOf.mpr h)
  have hwW : (w' : X) ∉ rightConjugate T y ⊔ (T ⊔ rightConjugate T g) :=
    fun h => hwZ (mem_Z_of_sq e h hwP.2 hw2)
  refine ⟨w', hwP, hwW, hw2, ?_, (h : X)⁻¹, G.inv_mem h.2, ?_⟩
  ·
    have hrel : (((T ⊔ rightConjugate T g) ⊓ G).subgroupOf G).relIndex (rightConjugate U h) ≤
        2 := by
      have hRU : ((rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G).subgroupOf G ⊓
          rightConjugate U h ≤ ((T ⊔ rightConjugate T g) ⊓ G).subgroupOf G := by
        intro v hv
        obtain ⟨hvR, hvU⟩ := Subgroup.mem_inf.mp hv
        rw [Subgroup.mem_subgroupOf] at hvR ⊢
        exact mem_Z_of_sq e hvR.1 hvR.2
          (by simpa using congrArg Subtype.val (sq_eq_one_of_mem_rightConjugate hU2 hvU))
      have h1 := Subgroup.relIndex_le_of_le_left (L := rightConjugate U h) hRU
        (Elem47.relIndex_ne_zero_of_finite _ _)
      rw [Subgroup.inf_relIndex_right] at h1
      have h2 := Subgroup.relIndex_le_of_le_right hUhQ (Elem47.relIndex_ne_zero_of_finite
        (((rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G).subgroupOf G) _)
      have h3 : (((rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G).subgroupOf G).relIndex
          (Q₀ : Subgroup G) = 2 := by
        rw [hQeq, Subgroup.relIndex_subgroupOf inf_le_right]
        exact c.relIndex_R_P
      omega
    have hwC := hcard w' hw'U
    have hZR : ∀ z ∈ (T ⊔ rightConjugate T g) ⊓ G,
        z ∈ (rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G :=
      fun z hz => ⟨Subgroup.mem_sup_right hz.1, hz.2⟩
    let φ : ((T ⊔ rightConjugate T g) ⊓ G : Subgroup X) →* X :=
      { toFun := fun z => (z : X)⁻¹ * ((w' : X)⁻¹ * z * w')
        map_one' := by simp
        map_mul' := fun a b => by
          simp only [Subgroup.coe_mul]
          exact comm_mul e hwP.1 hwP.2 hwW (hZR a a.2) (hZR b b.2) }
    have hrange : φ.range ≤ (⁅((T ⊔ rightConjugate T g) ⊓ G).subgroupOf G,
        Subgroup.zpowers w'⁆ : Subgroup G).map G.subtype := by
      rintro _ ⟨z, rfl⟩
      refine ⟨⁅(⟨z, z.2.2⟩ : G)⁻¹, w'⁻¹⁆, Subgroup.commutator_mem_commutator
        (Subgroup.inv_mem _ (Subgroup.mem_subgroupOf.mpr z.2))
        (Subgroup.inv_mem _ (Subgroup.mem_zpowers w')), ?_⟩
      simp [φ, commutatorElement_def, mul_assoc]
    have hker : ∀ z ∈ φ.ker, (z : X) ∈ (T ⊔ rightConjugate T g) ⊓ G ⊓
        Subgroup.centralizer (S : Set X) := by
      intro z hz
      have h1 : (z : X)⁻¹ * ((w' : X)⁻¹ * z * w') = 1 := hz
      refine c.mem_A_of_comm hwP.1 hwW z.2 ?_
      have h2 : (w' : X)⁻¹ * z * w' = z := by
        calc (w' : X)⁻¹ * z * w' = z * ((z : X)⁻¹ * ((w' : X)⁻¹ * z * w')) := by group
          _ = z := by rw [h1, mul_one]
      calc (z : X) * w' = w' * ((w' : X)⁻¹ * z * w') := by group
        _ = w' * z := by rw [h2]
    let f : φ.ker → ↥((T ⊔ rightConjugate T g) ⊓ G ⊓ Subgroup.centralizer (S : Set X)) :=
      fun z => ⟨((z : ↥((T ⊔ rightConjugate T g) ⊓ G)) : X), hker z z.2⟩
    have hf : Function.Injective f := by
      intro a b hab
      have h1 := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h1)
    have hkerA := Nat.card_le_card_of_injective f hf
    have hidx := Subgroup.card_mul_index φ.ker
    rw [Subgroup.index_ker] at hidx
    have hrange' := Subgroup.card_le_of_le hrange
    rw [Subgroup.card_map_of_injective G.subtype_injective] at hrange'
    rw [← hidx]
    calc Nat.card φ.ker * Nat.card φ.range ≤ Nat.card ((T ⊔ rightConjugate T g) ⊓ G ⊓
          Subgroup.centralizer (S : Set X) : Subgroup X) * 2 :=
        Nat.mul_le_mul hkerA (hrange'.trans (hwC.trans hrel))
      _ = 2 * _ := mul_comm _ _
  · have h1 : h * w' * h⁻¹ ∈ U := (mem_rightConjugate_iff _ _ _).mp hw'U
    have h2 := Subgroup.mem_subgroupOf.mp (hUV h1)
    simpa [mul_assoc] using h2

theorem stronglyClosed_Z (c : ElemCtx G T S Q H g y) (hin : Theorem48Inputs) :
    ∀ z ∈ (T ⊔ rightConjugate T g) ⊓ G, ∀ x ∈ G, x⁻¹ * z * x ∈ S ⊓ G →
      x⁻¹ * z * x ∈ (T ⊔ rightConjugate T g) ⊓ G := by
  by_contra hcon
  simp only [not_forall, exists_prop] at hcon
  obtain ⟨z, hz, x, hx, hxP, hxZ⟩ := hcon
  obtain ⟨w, hwP, hwW, hw2, hk, x₀, hx₀, hx₀w⟩ :
      ∃ w ∈ S ⊓ G, w ∉ rightConjugate T y ⊔ (T ⊔ rightConjugate T g) ∧ w ^ 2 = 1 ∧
        Nat.card ((T ⊔ rightConjugate T g) ⊓ G : Subgroup X) ≤
          2 * Nat.card ((T ⊔ rightConjugate T g) ⊓ G ⊓ Subgroup.centralizer (S : Set X) :
            Subgroup X) ∧
        ∃ x ∈ G, x⁻¹ * w * x ∈ (T ⊔ rightConjugate T g) ⊓ G := by
    by_cases hwc : ∀ h ∈ G, rightConjugate ((T ⊔ rightConjugate T g) ⊓ G) h ≤ S ⊓ G →
        rightConjugate ((T ⊔ rightConjugate T g) ⊓ G) h = (T ⊔ rightConjugate T g) ⊓ G
    · exact c.exists_involution_of_weaklyClosed hin hwc ⟨z, hz, x, hx, hxP, hxZ⟩
    · simp only [not_forall, exists_prop] at hwc
      obtain ⟨h, hh, hle, hne⟩ := hwc
      exact c.exists_involution_of_not_weaklyClosed hh hle hne
  have hwA : ∀ a ∈ (T ⊔ rightConjugate T g) ⊓ G ⊓ Subgroup.centralizer (S : Set X),
      a * w = w * a := fun a ha => A_comm ha hwP.1
  obtain ⟨x', hx', hx'A⟩ := c.exists_conj_mem_A hwP.1 hwP.2 hwW hw2 hwA hk hx₀ hx₀w rfl
  obtain ⟨y', hy', hyE, hyw⟩ :=
    c.exists_normalizer_conj_mem_A hwP.1 hwP.2 hwW hw2 hwA hk hx' hx'A rfl
  exact c.false_of_normalizer hwP.1 hwP.2 hwW hw2 hwA hk hy' hyE hyw

end ElemCtx

end CFSG.ComponentClassification.AschbacherTheorem3.FourEight
