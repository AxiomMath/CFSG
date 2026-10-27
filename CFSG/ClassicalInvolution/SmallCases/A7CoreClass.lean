module

public import CFSG.ClassicalInvolution.SmallCases.A7CoreQuasi
public import CFSG.ClassicalInvolution.SmallCases.A7CoreConj

public section

namespace CFSG.ClassicalInvolution.A7Core

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Hat2A7
  CFSG.ClassicalInvolution.Hat2A7R CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

variable {F : Type} [Group F] [Finite F]

theorem exists_classical_of_twin_pairs {K K' : Subgroup F} {z : F} (hK : IsClassical2A7 ⊤ K z)
    (hK' : IsClassical2A7 ⊤ K' z) (hne : K ≠ K') {a κ b κ' : F} (ha : a ∈ K) (hκ : κ ∈ K)
    (hb : b ∈ K') (hκ' : κ' ∈ K') (ha2 : a * a = z) (hb2 : b * b = z) (hab : a * b = b * a)
    (hκ2 : κ * κ = z) (hκ'2 : κ' * κ' = z) (hκκ' : κ * κ' = κ' * κ) {J : Subgroup F}
    (hJ : IsClassical2A7 ⊤ J (a * b)) : ∃ I : Subgroup F, IsClassical2A7 ⊤ I (κ * κ') := by
  classical
  obtain ⟨g, hgK, hg⟩ := exists_conj_in_member hK hκ ha hκ2 ha2
  obtain ⟨g', hg'K', hg'⟩ := exists_conj_in_member hK' hκ' hb hκ'2 hb2
  obtain ⟨hK'N, hKN', -⟩ := twin_facts hK hK' hne
  set M : Subgroup F := K ⊔ K' with hM
  have hKM : K ≤ M := le_sup_left
  have hK'M : K' ≤ M := le_sup_right
  set N : Subgroup F := oddCoreOf M with hN
  have hMN : ∀ m ∈ M, m ∈ Subgroup.normalizer (N : Set F) := fun m hm =>
    AscFusion.mem_normalizer_oddCoreOf_of_mem_normalizer' (Subgroup.le_normalizer hm)
  have hOK : oddCoreOf K ≤ N := by
    refine AscFusion.le_oddCoreOf_of_normal_odd ((oddCoreOf_le_self K).trans hKM) ?_
      (oddCoreOf_odd_natCard K)
    refine sup_le ?_ ?_
    · exact fun m hm =>
        AscFusion.mem_normalizer_oddCoreOf_of_mem_normalizer' (Subgroup.le_normalizer hm)
    · exact fun m hm => AscFusion.mem_normalizer_oddCoreOf_of_mem_normalizer' (hK'N hm)
  have hcN : ∀ u ∈ K, ∀ w ∈ K', ⁅u, w⁆ ∈ N := fun u hu w hw => by
    rw [← commutatorElement_inv]
    exact N.inv_mem (hOK (commutator_mem_of_twin hK hK' hne hw u hu))
  have hcN' : ∀ w ∈ K', ∀ u ∈ K, ⁅w, u⁆ ∈ N := fun w hw u hu =>
    hOK (commutator_mem_of_twin hK hK' hne hw u hu)
  set x : F := g * g' with hx
  set y : F := x * (κ * κ') * x⁻¹ with hy
  set c₁ : F := g' * κ * g'⁻¹ * κ⁻¹ with hc₁
  set c₂ : F := g * b * g⁻¹ * b⁻¹ with hc₂
  have hc₁N : c₁ ∈ N := by
    have : c₁ = ⁅g', κ⁆ := by rw [hc₁, commutatorElement_def]
    rw [this]
    exact hcN' g' hg'K' κ hκ
  have hc₂N : c₂ ∈ N := by
    have : c₂ = ⁅g, b⁆ := by rw [hc₂, commutatorElement_def]
    rw [this]
    exact hcN g hgK b hb
  have hgM : g ∈ M := hKM hgK
  have haM : a ∈ M := hKM ha
  have hbM : b ∈ M := hK'M hb
  have hy' : y = (g * c₁ * g⁻¹) * a * c₂ * b := by
    have e1 : g' * κ' * g'⁻¹ = b := hg'
    have e2 : g * κ * g⁻¹ = a := hg
    calc y = g * (g' * κ * g'⁻¹) * (g' * κ' * g'⁻¹) * g⁻¹ := by rw [hy, hx]; group
      _ = g * (c₁ * κ) * b * g⁻¹ := by
        rw [e1]
        congr 3
        rw [hc₁]
        group
      _ = (g * c₁ * g⁻¹) * (g * κ * g⁻¹) * (g * b * g⁻¹) := by group
      _ = (g * c₁ * g⁻¹) * a * c₂ * b := by
        rw [e2]
        have : g * b * g⁻¹ = c₂ * b := by rw [hc₂]; group
        rw [this]
        group
  have hn1 : g * c₁ * g⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hMN g hgM) c₁).mp hc₁N
  have hn2 : a⁻¹ * (g * c₁ * g⁻¹) * a ∈ N := by
    have := (Subgroup.mem_normalizer_iff.mp (hMN a⁻¹ (M.inv_mem haM)) (g * c₁ * g⁻¹)).mp hn1
    simpa using this
  have hn3 : b⁻¹ * ((a⁻¹ * (g * c₁ * g⁻¹) * a) * c₂) * b ∈ N := by
    have := (Subgroup.mem_normalizer_iff.mp (hMN b⁻¹ (M.inv_mem hbM)) _).mp
      (N.mul_mem hn2 hc₂N)
    simpa using this
  have hxy : (a * b)⁻¹ * y ∈ N := by
    have : (a * b)⁻¹ * y = b⁻¹ * ((a⁻¹ * (g * c₁ * g⁻¹) * a) * c₂) * b := by
      rw [hy']
      group
    rw [this]
    exact hn3
  have hab2 : (a * b) * (a * b) = 1 := by
    calc (a * b) * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha2, hb2]; exact hK.mul_self
  have hδ2 : (κ * κ') * (κ * κ') = 1 := by
    calc (κ * κ') * (κ * κ') = κ * (κ' * κ) * κ' := by group
      _ = κ * (κ * κ') * κ' := by rw [← hκκ']
      _ = (κ * κ) * (κ' * κ') := by group
      _ = 1 := by rw [hκ2, hκ'2]; exact hK.mul_self
  have hy2 : y * y = 1 := by
    calc y * y = x * ((κ * κ') * (κ * κ')) * x⁻¹ := by rw [hy]; group
      _ = 1 := by rw [hδ2]; group
  have hxt : IsPGroup 2 (Subgroup.zpowers (a * b)) :=
    AscFusion.isPGroup_zpowers_of_sq_sq (by rw [hab2]; group)
  have hyt : IsPGroup 2 (Subgroup.zpowers y) :=
    AscFusion.isPGroup_zpowers_of_sq_sq (by rw [hy2]; group)
  obtain ⟨h, -, hh⟩ := AscFusion.exists_conj_of_odd_coset (oddCoreOf_odd_natCard M) hxt hyt
    (hMN (a * b) (M.mul_mem haM hbM)) hxy
  refine ⟨conjSub (x⁻¹ * h) J, ?_⟩
  have := classical_conjSub hJ (x⁻¹ * h)
  have e : (x⁻¹ * h) * (a * b) * (x⁻¹ * h)⁻¹ = κ * κ' := by
    calc (x⁻¹ * h) * (a * b) * (x⁻¹ * h)⁻¹ = x⁻¹ * (h * (a * b) * h⁻¹) * x := by group
      _ = x⁻¹ * y * x := by rw [hh]
      _ = κ * κ' := by rw [hy]; group
  rwa [e] at this

theorem exists_twin_product {K : Subgroup F} {z : F} (hK : IsClassical2A7 ⊤ K z)
    {J : Subgroup F} {t : F} (hJ : IsClassical2A7 ⊤ J t) (hne : t ≠ z) {v : F} (hvJ : v ∈ J)
    (hv4 : orderOf v = 4) (hvz : v * z = z * v) (hvK : v * v ∈ Subgroup.normalizer (K : Set F))
    (hv : v ∉ Subgroup.normalizer (K : Set F)) :
    ∃ a ∈ K, ∃ b ∈ conjSub v⁻¹ K, a * a = z ∧ b * b = z ∧ a * b = b * a ∧ a * b = t := by
  classical
  have hKz : IsUniqueInvolution K z := isUniqueInvolution hK
  have hJt : IsUniqueInvolution J t := isUniqueInvolution hJ
  have hz2 : z * z = 1 := hKz.sq
  have ht2 : t * t = 1 := hJt.sq
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hv2 : IsPGroup 2 (Subgroup.zpowers v) := isPGroup_zpowers_of_orderOf_four hv4
  have hvv : v * v = t := mul_self_eq_of_orderOf_four hJt hvJ hv4
  have htK : t ∈ Subgroup.normalizer (K : Set F) := hvv ▸ hvK
  have htz : t * z = z * t := by
    rw [← hvv]
    calc v * v * z = v * (v * z) := by group
      _ = v * (z * v) := by rw [hvz]
      _ = (v * z) * v := by group
      _ = (z * v) * v := by rw [hvz]
      _ = z * (v * v) := by group
  have hvK'' : conjSub v⁻¹ K ≠ K := conjSub_inv_ne hv
  obtain ⟨hK'mem, -, -, -⟩ := twin_facts_a7 hK (inv_comm_of_comm hvz) hvK''.symm
  set K' : Subgroup F := conjSub v⁻¹ K with hK'
  have hKK' : K ≠ K' := hvK''.symm
  obtain ⟨R, hR2, hvR, -, hRK, -, hRcomm, hRinv⟩ := exists_twin_sylow hK hv2 hvz hvK'' hvK
  have htR : t ∈ R := hvv ▸ R.mul_mem hvR hvR
  have hnt : ¬ ∀ k ∈ K, ⁅t, k⁆ ∈ oddCoreOf K := by
    have := nontrivAction hK hJ hne hvJ hv4 hvz hvK hv
    rwa [hvv] at this
  obtain ⟨k, hkK, -, hkact⟩ := typeI hK hJ hne hvJ hv4 hvz hvK hv
  have hnc : ¬ ∀ y ∈ K, ⁅k, y⁆ ∈ oddCoreOf K := by
    intro hc
    apply hnt
    intro y hy
    have e1 : ⁅t, y⁆ = (t * y * t⁻¹ * (k * y * k⁻¹)⁻¹) * ⁅k, y⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e1]
    exact (oddCoreOf K).mul_mem (hkact y hy) (hc y hy)
  obtain ⟨a₀, ⟨ha₀R, ha₀K⟩, ha₀2, hta₀⟩ :=
    exists_fixed_of_inner hK hR2 hRK htR ht2 htK hkK hkact hnc
  have ha₀pg : IsPGroup 2 (Subgroup.zpowers a₀) := AscFusion.isPGroup_zpowers_of_sq_eq hz2 ha₀2
  have ha₀ord : orderOf a₀ = 4 := AscFusion.orderOf_eq_four_of_sq_eq hz2 hKz.ne_one ha₀2
  have hzv : v⁻¹ * z * v = z := conj_eq_of_comm hvz
  set a₀' : F := v⁻¹ * a₀ * v with ha₀'
  obtain ⟨ha₀'R, ha₀'K'⟩ := hRinv a₀ ⟨ha₀R, ha₀K⟩
  have ha₀cm : a₀ * a₀' = a₀' * a₀ := hRcomm a₀ ⟨ha₀R, ha₀K⟩ a₀' ⟨ha₀'R, ha₀'K'⟩
  have ha₀'2 : a₀' * a₀' = z := by
    calc a₀' * a₀' = v⁻¹ * (a₀ * a₀) * v := by rw [ha₀']; group
      _ = z := by rw [ha₀2, hzv]
  have hta₀i : t * a₀⁻¹ = a₀⁻¹ * t := by
    calc t * a₀⁻¹ = a₀⁻¹ * (a₀ * t) * a₀⁻¹ := by group
      _ = a₀⁻¹ * (t * a₀) * a₀⁻¹ := by rw [hta₀]
      _ = a₀⁻¹ * t := by group
  by_cases hJa : a₀ ∈ Subgroup.normalizer (J : Set F)
  ·
    have hc : a₀ * a₀'⁻¹ = a₀'⁻¹ * a₀ := (Commute.inv_right (show Commute a₀ a₀' from ha₀cm)).eq
    have hσJ : a₀'⁻¹ * a₀ ∈ J := by
      have h1 : a₀⁻¹ * v * a₀ ∈ J := by
        have := (Subgroup.mem_normalizer_iff.mp
          ((Subgroup.normalizer (J : Set F)).inv_mem hJa) v).mp hvJ
        simpa using this
      have : a₀'⁻¹ * a₀ = v⁻¹ * (a₀⁻¹ * v * a₀) := by rw [ha₀']; group
      rw [this]
      exact J.mul_mem (J.inv_mem hvJ) h1
    have hσ2 : (a₀'⁻¹ * a₀) * (a₀'⁻¹ * a₀) = 1 := by
      calc (a₀'⁻¹ * a₀) * (a₀'⁻¹ * a₀) = a₀'⁻¹ * (a₀ * a₀'⁻¹) * a₀ := by group
        _ = a₀'⁻¹ * (a₀'⁻¹ * a₀) * a₀ := by rw [hc]
        _ = (a₀' * a₀')⁻¹ * (a₀ * a₀) := by group
        _ = 1 := by rw [ha₀'2, ha₀2]; exact inv_mul_cancel z
    have hσt : a₀'⁻¹ * a₀ = t := by
      rcases hJt.unique _ hσJ hσ2 with h | h
      · exfalso
        have hee : a₀' = a₀ := inv_mul_eq_one.mp h
        exact hKK' (eq_of_mem_of_mem hK hK'mem ha₀K (hee ▸ ha₀'K') ha₀pg (by omega))
      · exact h
    refine ⟨a₀, ha₀K, a₀'⁻¹, K'.inv_mem ha₀'K', ha₀2, ?_, hc, ?_⟩
    · calc a₀'⁻¹ * a₀'⁻¹ = (a₀' * a₀')⁻¹ := by group
        _ = z := by rw [ha₀'2, hzi]
    · rw [hc]
      exact hσt
  ·
    have hv3 : 3 ≤ Nat.card (Subgroup.zpowers v) := by rw [Nat.card_zpowers, hv4]; omega
    have hzJ : z ∈ Subgroup.normalizer (J : Set F) :=
      mem_normalizer_of_commute_of_mem_noncentral hJ htz.symm hvJ hv2 hv3 hvz.symm
    have hnt_d := nontrivAction hJ hK hne.symm ha₀K ha₀ord hta₀.symm
      (by rw [ha₀2]; exact hzJ) hJa
    obtain ⟨κ, hκJ, hκ2, hκn, hκc⟩ :=
      exists_kappa hJ ha₀ord hta₀.symm hJa (by rw [ha₀2]; exact hzJ) hnt_d
    obtain ⟨δ, hδ2, hzδ, hδa⟩ := AscFusion.dual_delta_facts hz2 ht2 ha₀2 hta₀ hκ2 hκn hκc
    have hδi : δ⁻¹ = δ := inv_eq_of_mul_eq_one_right hδ2
    have hzδ' : δ⁻¹ * z = z * δ⁻¹ := by rw [hδi]; exact hzδ.symm
    set K₃ : Subgroup F := conjSub δ⁻¹ K with hK₃
    have hK₃z : IsClassical2A7 ⊤ K₃ z := classical_conjSub_of_commute hK hzδ'
    have hb₃ : a₀ * t ∈ K₃ := by
      have := conj_mem_conjSub (n := δ⁻¹) ha₀K
      rw [inv_inv] at this
      rwa [hδa] at this
    have hK₃K : K₃ ≠ K := by
      intro h
      have htK' : t ∈ K := by
        have h1 : a₀ * t ∈ K := h ▸ hb₃
        have := K.mul_mem (K.inv_mem ha₀K) h1
        simpa using this
      rcases hKz.unique t htK' ht2 with h1 | h1
      · exact hJt.ne_one h1
      · exact hne h1
    have hK₃K' : K₃ = K' := by
      by_contra hK₃K'
      have htK'N : t ∈ Subgroup.normalizer (K' : Set F) := mem_normalizer_symm hK'mem hJ hzJ
      have hvK'₂ : v ∉ Subgroup.normalizer (K' : Set F) := by
        intro h
        have h1 : conjSub v K' = K' := conjSub_eq_of_mem_normalizer h
        have h2 : conjSub v K' = K := by
          rw [hK', ← conjSub_mul, mul_inv_cancel, conjSub_one]
        exact hKK' (h2.symm.trans h1)
      apply nontrivAction hK'mem hJ hne hvJ hv4 hvz (hvv ▸ htK'N) hvK'₂
      intro k' hk'
      rw [hvv]
      have e : a₀⁻¹ * (a₀ * t) = t := by group
      have := commutator_mem_of_product hK hK₃z hK'mem hKK' hK₃K' (K.inv_mem ha₀K) hb₃ k' hk'
      rwa [e] at this
    have hb₃' : a₀ * t ∈ K' := hK₃K' ▸ hb₃
    refine ⟨a₀⁻¹, K.inv_mem ha₀K, a₀ * t, hb₃', ?_, ?_, ?_, ?_⟩
    · calc a₀⁻¹ * a₀⁻¹ = (a₀ * a₀)⁻¹ := by group
        _ = z := by rw [ha₀2, hzi]
    · calc a₀ * t * (a₀ * t) = a₀ * (t * a₀) * t := by group
        _ = a₀ * (a₀ * t) * t := by rw [hta₀]
        _ = (a₀ * a₀) * (t * t) := by group
        _ = z := by rw [ha₀2, ht2, mul_one]
    · calc a₀⁻¹ * (a₀ * t) = t := by group
        _ = a₀ * (a₀⁻¹ * t) := by group
        _ = a₀ * (t * a₀⁻¹) := by rw [hta₀i]
        _ = a₀ * t * a₀⁻¹ := by group
    · group

theorem deltaClassical {K : Subgroup F} {z : F} (hK : IsClassical2A7 ⊤ K z) {J : Subgroup F}
    {t : F} (hJ : IsClassical2A7 ⊤ J t) (hne : t ≠ z) {v : F} (hvJ : v ∈ J)
    (hv4 : orderOf v = 4) (hvz : v * z = z * v) (hvK : v * v ∈ Subgroup.normalizer (K : Set F))
    (hv : v ∉ Subgroup.normalizer (K : Set F)) {κ : F} (hκK : κ ∈ K) (hκ2 : κ * κ = z)
    (hcomm : κ * (v⁻¹ * κ * v) = (v⁻¹ * κ * v) * κ) :
    ∃ I : Subgroup F, IsClassical2A7 ⊤ I (κ * (v⁻¹ * κ * v)) := by
  obtain ⟨a, haK, b, hbK', ha2, hb2, hab, hat⟩ :=
    exists_twin_product hK hJ hne hvJ hv4 hvz hvK hv
  have hvK'' : conjSub v⁻¹ K ≠ K := conjSub_inv_ne hv
  obtain ⟨hK'mem, -, -, -⟩ := twin_facts_a7 hK (inv_comm_of_comm hvz) hvK''.symm
  have hκ'K' : v⁻¹ * κ * v ∈ conjSub v⁻¹ K := by
    have := conj_mem_conjSub (n := v⁻¹) hκK
    rwa [inv_inv] at this
  have hκ'2 : (v⁻¹ * κ * v) * (v⁻¹ * κ * v) = z := by
    calc (v⁻¹ * κ * v) * (v⁻¹ * κ * v) = v⁻¹ * (κ * κ) * v := by group
      _ = z := by rw [hκ2, conj_eq_of_comm hvz]
  have hJab : IsClassical2A7 ⊤ J (a * b) := by rw [hat]; exact hJ
  exact exists_classical_of_twin_pairs hK hK'mem hvK''.symm haK hκK hbK' hκ'K' ha2 hb2 hab hκ2
    hκ'2 hcomm hJab

end CFSG.ClassicalInvolution.A7Core
