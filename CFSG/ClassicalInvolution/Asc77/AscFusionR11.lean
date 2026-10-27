module

public import CFSG.ClassicalInvolution.Asc77.AscFusionR10
public import CFSG.ClassicalInvolution.Asc77.AscFusionR7

public section

namespace CFSG.ClassicalInvolution.Asc77.AscFusion

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscHypOmega
  CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

variable {p f : ℕ} [Fact p.Prime]


@[expose] def TypeI (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) →
      ∀ J ∈ CoreAssembly.conjClass K, ∀ t : G, IsUniqueInvolution J t → t ≠ z →
        (∀ Q ∈ CoreAssembly.conjClass K, IsUniqueInvolution Q z →
          t ∈ Subgroup.normalizer (Q : Set G)) →
        ∀ v ∈ J, IsPGroup 2 (Subgroup.zpowers v) → orderOf v = 4 → v * z = z * v →
          v ^ 2 ∈ Subgroup.normalizer (K : Set G) → v ∉ Subgroup.normalizer (K : Set G) →
            ∃ k ∈ K, ∀ x ∈ K, t * x * t⁻¹ * (k * x * k⁻¹)⁻¹ ∈ oddCoreOf K


variable {G : Type} [Group G] [Finite G]

theorem exists_twin_product (hC : Prop370 p f) (hA : NontrivAction p f) (hI : TypeI p f)
    [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {K : Subgroup G} {z : G} (hz : IsClassicalMember p f K z)
    (hbelow : CITBelowU p f (Nat.card G)) {J : Subgroup G}
    (hJ : J ∈ CoreAssembly.conjClass K) {t : G} (ht : IsUniqueInvolution J t) (hne : t ≠ z)
    (hH : ∀ Q ∈ CoreAssembly.conjClass K, IsUniqueInvolution Q z →
      t ∈ Subgroup.normalizer (Q : Set G))
    {v : G} (hvJ : v ∈ J) (hv2 : IsPGroup 2 (Subgroup.zpowers v)) (hv4 : orderOf v = 4)
    (hvz : v * z = z * v) (hvK : v ^ 2 ∈ Subgroup.normalizer (K : Set G))
    (hv : v ∉ Subgroup.normalizer (K : Set G)) :
    ∃ a ∈ K, ∃ b ∈ conjSub v⁻¹ K, a * a = z ∧ b * b = z ∧ a * b = b * a ∧ a * b = t := by
  classical
  have hKc : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hKz : IsUniqueInvolution K z :=
    ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hz
  have hz2 : z * z = 1 := hKz.sq
  have ht2 : t * t = 1 := ht.sq
  have hJt : IsClassicalMember p f J t := isClassicalMember_of_mem_conjClass hp2 hq hz hJ ht
  have hvv : v * v = t := by
    have hv22 : (v * v) * (v * v) = 1 := by
      have : v ^ 4 = 1 := by rw [← hv4]; exact pow_orderOf_eq_one v
      simpa [pow_succ, mul_assoc] using this
    rcases ht.unique (v * v) (J.mul_mem hvJ hvJ) hv22 with h | h
    · exfalso
      have : orderOf v ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
      rw [hv4] at this
      omega
    · exact h
  have hvK' : v * v ∈ Subgroup.normalizer (K : Set G) := by simpa [pow_two] using hvK
  have htK : t ∈ Subgroup.normalizer (K : Set G) := hvv ▸ hvK'
  have htz : t * z = z * t := by
    rw [← hvv]
    calc v * v * z = v * (v * z) := by group
      _ = v * (z * v) := by rw [hvz]
      _ = (v * z) * v := by group
      _ = (z * v) * v := by rw [hvz]
      _ = z * (v * v) := by group
  have hvz' : v⁻¹ * z = z * v⁻¹ := by
    calc v⁻¹ * z = v⁻¹ * z * v * v⁻¹ := by group
      _ = z * v⁻¹ := by
        have : v⁻¹ * z * v = z := by
          calc v⁻¹ * z * v = v⁻¹ * (z * v) := by rw [mul_assoc]
            _ = v⁻¹ * (v * z) := by rw [hvz]
            _ = z := by group
        rw [this]
  have hvK'' : conjSub v⁻¹ K ≠ K := fun h =>
    hv (by
      have := (Subgroup.normalizer (K : Set G)).inv_mem
        (AscHypOmega.mem_normalizer_of_conjSub_eq h)
      simpa using this)
  obtain ⟨hK'mem, hK'z, hK'N, hKN', hcomm'⟩ :=
    twin_facts_conj hp2 hq hz hKc hKz hvz' hvK''.symm
  set K' : Subgroup G := conjSub v⁻¹ K with hK'
  have hKK' : K ≠ K' := hvK''.symm
  have hK'K : K' ∈ CoreAssembly.conjClass K := hK'mem
  have hK'class : IsClassicalMember p f K' z :=
    isClassicalMember_of_mem_conjClass hp2 hq hz hK'mem hK'z
  obtain ⟨R, hR2, hvR, -, hRK, -, hRcomm, hRinv⟩ :=
    exists_twin_sylow hp2 hq hz hKc hKz hv2 hvz hvK'' hvK'
  have htR : t ∈ R := hvv ▸ R.mul_mem hvR hvR
  have hnt : ¬ ∀ k ∈ K, ⁅t, k⁆ ∈ oddCoreOf K := by
    have := hA G hnab hp2 hq K z hz hbelow J hJ t ht hne hH v hvJ hv2 hv4 hvz hvK hv
    rwa [hvv] at this
  have hin := hI G hnab hp2 hq K z hz hbelow J hJ t ht hne hH v hvJ hv2 hv4 hvz hvK hv
  obtain ⟨a₀, ⟨ha₀R, ha₀K⟩, ha₀2, hta₀⟩ :=
    exists_order_four_comm hp2 hq hz hR2 hRK htR htK ht2 hnt hin
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have ha₀4' : (a₀ * a₀) * (a₀ * a₀) = 1 := by rw [ha₀2]; exact hz2
  have ha₀pg : IsPGroup 2 (Subgroup.zpowers a₀) := isPGroup_zpowers_of_sq_sq ha₀4'
  have ha₀ord : orderOf a₀ = 4 := by
    have h4 : a₀ ^ 2 ^ (1 + 1) = 1 := by simpa [pow_succ, mul_assoc] using ha₀4'
    have hn2 : ¬ a₀ ^ 2 ^ 1 = 1 := by
      intro h
      apply hKz.ne_one
      rw [← ha₀2]
      simpa [pow_two] using h
    have := orderOf_eq_prime_pow hn2 h4
    simpa using this
  have hzv : v⁻¹ * z * v = z := by
    calc v⁻¹ * z * v = v⁻¹ * (z * v) := by rw [mul_assoc]
      _ = v⁻¹ * (v * z) := by rw [hvz]
      _ = z := by group
  set a₀' : G := v⁻¹ * a₀ * v with ha₀'
  obtain ⟨ha₀'R, ha₀'K'⟩ := hRinv a₀ ⟨ha₀R, ha₀K⟩
  have ha₀cm : a₀ * a₀' = a₀' * a₀ := hRcomm a₀ ⟨ha₀R, ha₀K⟩ a₀' ⟨ha₀'R, ha₀'K'⟩
  have ha₀'2 : a₀' * a₀' = z := by
    calc a₀' * a₀' = v⁻¹ * (a₀ * a₀) * v := by rw [ha₀']; group
      _ = z := by rw [ha₀2, hzv]
  have hta₀i : t * a₀⁻¹ = a₀⁻¹ * t := by
    calc t * a₀⁻¹ = a₀⁻¹ * (a₀ * t) * a₀⁻¹ := by group
      _ = a₀⁻¹ * (t * a₀) * a₀⁻¹ := by rw [hta₀]
      _ = a₀⁻¹ * t := by group
  by_cases hJa : a₀ ∈ Subgroup.normalizer (J : Set G)
  ·
    have hc : a₀ * a₀'⁻¹ = a₀'⁻¹ * a₀ := (Commute.inv_right (show Commute a₀ a₀' from ha₀cm)).eq
    have hσJ : a₀'⁻¹ * a₀ ∈ J := by
      have h1 : a₀⁻¹ * v * a₀ ∈ J := by
        have := (Subgroup.mem_normalizer_iff.mp
          ((Subgroup.normalizer (J : Set G)).inv_mem hJa) v).mp hvJ
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
      rcases ht.unique _ hσJ hσ2 with h | h
      · exfalso
        have hee : a₀' = a₀ := inv_mul_eq_one.mp h
        have hK'eq := eq_of_mem_of_mem hp2 hq hz hKc hK'mem ha₀K (hee ▸ ha₀'K') ha₀pg
          (by omega)
        exact hKK' hK'eq
      · exact h
    refine ⟨a₀, ha₀K, a₀'⁻¹, K'.inv_mem ha₀'K', ha₀2, ?_, hc, ?_⟩
    · calc a₀'⁻¹ * a₀'⁻¹ = (a₀' * a₀')⁻¹ := by group
        _ = z := by rw [ha₀'2, hzi]
    · rw [hc]
      exact hσt
  ·
    have hKJ : K ∈ CoreAssembly.conjClass J := conjClass_symm hJ
    have hzJ : z ∈ Subgroup.normalizer (J : Set G) := by
      have := centralizer_le_normalizer_of_mem hp2 hq hz hJ hvJ hv2 (by omega : 4 ≤ orderOf v)
      exact this (Subgroup.mem_centralizer_singleton_iff.mpr hvz.symm)
    have hH_d : ∀ Q ∈ CoreAssembly.conjClass J, IsUniqueInvolution Q t →
        z ∈ Subgroup.normalizer (Q : Set G) := by
      intro Q hQ hQt
      have hQK : Q ∈ CoreAssembly.conjClass K := conjClass_trans hJ hQ
      exact hC G hnab hp2 hq K z hz hbelow Q hQK t hQt K hKc z hKz hne.symm htz htK
    have hnt_d := hA G hnab hp2 hq J t hJt hbelow K hKJ z hKz hne.symm hH_d a₀ ha₀K ha₀pg
      ha₀ord hta₀.symm (by rw [pow_two, ha₀2]; exact hzJ) hJa
    obtain ⟨κ, hκJ, hκ2, hκn, hκc⟩ :=
      exists_kappa hp2 hq hz hJ ht ha₀ord hta₀.symm hJa (by rw [ha₀2]; exact hzJ) hnt_d
    obtain ⟨δ, hδ2, hzδ, hδa⟩ := dual_delta_facts hz2 ht2 ha₀2 hta₀ hκ2 hκn hκc
    have hδi : δ⁻¹ = δ := inv_eq_of_mul_eq_one_right hδ2
    have hzδ' : δ⁻¹ * z * δ⁻¹⁻¹ = z := by
      rw [inv_inv, hδi]
      calc δ * z * δ = (z * δ) * δ := by rw [← hzδ]
        _ = z := by rw [mul_assoc, hδ2, mul_one]
    set K₃ : Subgroup G := conjSub δ⁻¹ K with hK₃
    have hK₃mem : K₃ ∈ CoreAssembly.conjClass K := conjSub_mem_conjClass hKc δ⁻¹
    have hK₃z : IsUniqueInvolution K₃ z := by
      have := hKz.conj δ⁻¹
      rwa [hzδ'] at this
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
      · exact ht.ne_one h1
      · exact hne h1
    have hK₃K' : K₃ = K' := by
      by_contra hK₃K'
      have hcomm₃ := commutator_mem_oddCoreOf_of_product hp2 hq hz hKc hK₃mem hK'mem hKz hK₃z hK'z
        hKK' hK₃K' (K.inv_mem ha₀K) hb₃
      have hJ' : J ∈ CoreAssembly.conjClass K' := conjClass_trans (conjClass_symm hK'K) hJ
      have hH' : ∀ Q ∈ CoreAssembly.conjClass K', IsUniqueInvolution Q z →
          t ∈ Subgroup.normalizer (Q : Set G) := fun Q hQ hQz =>
        hH Q (conjClass_trans hK'K hQ) hQz
      have hvK'₁ : v ^ 2 ∈ Subgroup.normalizer (K' : Set G) := by
        rw [pow_two, hvv]
        exact hH K' hK'K hK'z
      have hvK'₂ : v ∉ Subgroup.normalizer (K' : Set G) := by
        intro h
        have h1 : conjSub v K' = K' := mem_normalizer_iff_conjSub_eq.mp h
        have h2 : conjSub v K' = K := by
          rw [hK', ← conjSub_mul, mul_inv_cancel, conjSub_one]
        exact hKK' (h2.symm.trans h1)
      have := hA G hnab hp2 hq K' z hK'class hbelow J hJ' t ht hne hH' v hvJ hv2 hv4 hvz hvK'₁
        hvK'₂
      apply this
      intro k hk
      rw [hvv]
      have e : a₀⁻¹ * (a₀ * t) = t := by group
      have := hcomm₃ k hk
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


theorem deltaClassical_of_typeI (hC : Prop370 p f) (hA : NontrivAction p f) (hI : TypeI p f) :
    DeltaClassical p f := by
  intro G _ _ _ hnab hp2 hq K z hz hbelow J hJ t ht hne hH v hvJ hv2 hv4 hvz hvK hv κ hκK hκ2 hκn
    hcomm
  obtain ⟨a, haK, b, hbK', ha2, hb2, hab, hat⟩ :=
    exists_twin_product hC hA hI hnab hp2 hq hz hbelow hJ ht hne hH hvJ hv2 hv4 hvz hvK hv
  have hKc : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hKz : IsUniqueInvolution K z :=
    ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hz
  have hz2 : z * z = 1 := hKz.sq
  have hvz' : v⁻¹ * z = z * v⁻¹ := by
    calc v⁻¹ * z = v⁻¹ * z * v * v⁻¹ := by group
      _ = z * v⁻¹ := by
        have : v⁻¹ * z * v = z := by
          calc v⁻¹ * z * v = v⁻¹ * (z * v) := by rw [mul_assoc]
            _ = v⁻¹ * (v * z) := by rw [hvz]
            _ = z := by group
        rw [this]
  have hvK'' : conjSub v⁻¹ K ≠ K := fun h =>
    hv (by
      have := (Subgroup.normalizer (K : Set G)).inv_mem
        (AscHypOmega.mem_normalizer_of_conjSub_eq h)
      simpa using this)
  obtain ⟨hK'mem, hK'z, -, -, -⟩ := twin_facts_conj hp2 hq hz hKc hKz hvz' hvK''.symm
  have hzv : v⁻¹ * z * v = z := by
    calc v⁻¹ * z * v = v⁻¹ * (z * v) := by rw [mul_assoc]
      _ = v⁻¹ * (v * z) := by rw [hvz]
      _ = z := by group
  have hκ'K' : v⁻¹ * κ * v ∈ conjSub v⁻¹ K := by
    have := conj_mem_conjSub (n := v⁻¹) hκK
    rwa [inv_inv] at this
  have hκ'2 : (v⁻¹ * κ * v) * (v⁻¹ * κ * v) = z := by
    calc (v⁻¹ * κ * v) * (v⁻¹ * κ * v) = v⁻¹ * (κ * κ) * v := by group
      _ = z := by rw [hκ2, hzv]
  have hJt : IsUniqueInvolution J (a * b) := by rw [hat]; exact ht
  exact exists_classical_of_twin_pairs hp2 hq hz hKc hK'mem hKz hK'z hvK''.symm haK hκK hbK'
    hκ'K' ha2 hb2 hab hκ2 hκ'2 hcomm hJ hJt

theorem fusionCore_of_residuals' (hC : Prop370 p f) (hA : NontrivAction p f) (hI : TypeI p f)
    (h8 : BigOrder p f) : FusionCoreStmt p f :=
  fusionCore_of_residuals hC hA (deltaClassical_of_typeI hC hA hI) h8

end CFSG.ClassicalInvolution.Asc77.AscFusion
