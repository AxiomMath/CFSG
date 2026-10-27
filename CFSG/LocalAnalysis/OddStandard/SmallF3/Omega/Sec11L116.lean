module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10K0Aux
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11Statements

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec11_eq_one_or_of_mem_zpowers {x a : G} (hx : x * x = 1) (ha : a ∈ zpowers x) :
    a = 1 ∨ a = x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  have hx2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hx
  obtain ⟨n, hn | hn⟩ := Int.even_or_odd' k
  · left
    rw [hn, zpow_mul, hx2, one_zpow]
  · right
    rw [hn, zpow_add, zpow_mul, hx2, one_zpow, one_mul, zpow_one]

private theorem sec11_zpowers_comm {t z : G} (htz : t * z = z * t) :
    ∀ a ∈ zpowers t, ∀ b ∈ zpowers z, a * b = b * a := by
  intro a ha b hb
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  exact (Commute.zpow_zpow (show Commute t z from htz) m n).eq

theorem sec11_hatCent_conj {t z : G} (ht2 : t * t = 1) (hz2 : z * z = 1) (htz : t * z = z * t)
    (ht1 : t ≠ 1) (hne : t ≠ z) {p : G} (hp : p ∈ hatCent t z) :
    p * t * p⁻¹ = t ∨ p * t * p⁻¹ = t * z := by
  obtain ⟨hpc, hpn⟩ := Subgroup.mem_inf.mp hp
  have hpz : p * z * p⁻¹ = z := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hpc, mul_assoc, mul_inv_cancel, mul_one]
  have hmem : p * t * p⁻¹ ∈ zpowers t ⊔ zpowers z :=
    ((Subgroup.mem_normalizer_iff.mp hpn) t).mp (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
  obtain ⟨a, ha, b, hb, hab⟩ :=
    exists_mul_of_mem_sup_of_commute (sec11_zpowers_comm htz) hmem
  rcases sec11_eq_one_or_of_mem_zpowers ht2 ha with ha' | ha' <;>
    rcases sec11_eq_one_or_of_mem_zpowers hz2 hb with hb' | hb' <;> rw [ha', hb'] at hab
  · exact absurd (conj_eq_one_iff.mp (by rw [hab, one_mul])) ht1
  · refine absurd ?_ hne
    exact mul_left_cancel (mul_right_cancel (by rw [hab, one_mul, hpz]))
  · left
    rw [hab, mul_one]
  · right
    exact hab

theorem sec11_klein_mul {t z : G} (ht2 : t * t = 1) (hz2 : z * z = 1) (htz : t * z = z * t) :
    t * (t * z) = z ∧ (t * z) * t = z ∧ (t * z) * (t * z) = 1 := by
  refine ⟨by rw [← mul_assoc, ht2, one_mul], ?_, ?_⟩
  · rw [mul_assoc, ← htz, ← mul_assoc, ht2, one_mul]
  · calc t * z * (t * z) = t * (z * t) * z := by simp only [mul_assoc]
      _ = t * (t * z) * z := by rw [← htz]
      _ = (t * t) * (z * z) := by simp only [mul_assoc]
      _ = 1 := by rw [ht2, hz2, one_mul]

theorem sec11_conj_cases {t z : G} {T : Subgroup G} (hclass : conjClassIn T t = {t, t * z}) :
    (∀ σ ∈ T, σ * t * σ⁻¹ = t ∨ σ * t * σ⁻¹ = t * z) ∧
      ∀ σ ∈ T, σ * (t * z) * σ⁻¹ = t ∨ σ * (t * z) * σ⁻¹ = t * z := by
  have hmem_tz : t * z ∈ conjClassIn T t := by
    rw [hclass]
    exact Set.mem_insert_of_mem _ rfl
  obtain ⟨τ, hτT, hτ⟩ := hmem_tz
  refine ⟨fun σ hσ => ?_, fun σ hσ => ?_⟩
  · have hm : σ * t * σ⁻¹ ∈ conjClassIn T t := ⟨σ, hσ, rfl⟩
    rw [hclass] at hm
    rcases hm with h | h
    · exact Or.inl h
    · exact Or.inr h
  · have hm : σ * (t * z) * σ⁻¹ ∈ conjClassIn T t := by
      refine ⟨σ * τ, T.mul_mem hσ hτT, ?_⟩
      rw [hτ]
      group
    rw [hclass] at hm
    rcases hm with h | h
    · exact Or.inl h
    · exact Or.inr h

theorem sec11_fix_z_of_class {t z : G} {T : Subgroup G} (ht2 : t * t = 1) (hz2 : z * z = 1)
    (htz : t * z = z * t) (hz1 : z ≠ 1) (hclass : conjClassIn T t = {t, t * z}) :
    ∀ σ ∈ T, σ * z * σ⁻¹ = z := by
  obtain ⟨hk1, hk2, hk3⟩ := sec11_klein_mul ht2 hz2 htz
  obtain ⟨hconjT, hconjTz⟩ := sec11_conj_cases hclass
  intro σ hσ
  have hdec : σ * z * σ⁻¹ = (σ * t * σ⁻¹) * (σ * (t * z) * σ⁻¹) := by
    calc σ * z * σ⁻¹ = σ * (t * (t * z)) * σ⁻¹ := by rw [hk1]
      _ = (σ * t * σ⁻¹) * (σ * (t * z) * σ⁻¹) := by group
  rw [hdec]
  rcases hconjT σ hσ with h1 | h1 <;> rcases hconjTz σ hσ with h2 | h2 <;> rw [h1, h2]
  · exfalso
    have h5 : σ * z * σ⁻¹ = 1 := by rw [hdec, h1, h2, ht2]
    exact hz1 (conj_eq_one_iff.mp h5)
  · exact hk1
  · exact hk2
  · exfalso
    have h5 : σ * z * σ⁻¹ = 1 := by rw [hdec, h1, h2, hk3]
    exact hz1 (conj_eq_one_iff.mp h5)

theorem asc82Lemma116_of (h111N : Asc82Lemma111N) : Asc82Lemma116 := by
  intro G _ _ t L S z K1 K2 T R hctx
  obtain ⟨hidx, hclass, -, -⟩ := h111N G t L S z K1 K2 T R hctx
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [hctx.involution, pow_two] at h
    exact h
  have hz2 : z * z = 1 := by
    have h := pow_orderOf_eq_one z
    rw [hctx.toSec10Z.pocket.1, pow_two] at h
    exact h
  have htz : t * z = z * t :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hctx.sylow.1 hctx.mem_S)).symm
  have ht1 : t ≠ 1 := by
    intro h
    have h2 := hctx.involution
    rw [h, orderOf_one] at h2
    omega
  have hz1 : z ≠ 1 := by
    intro h
    have h2 := hctx.toSec10Z.pocket.1
    rw [h, orderOf_one] at h2
    omega
  have hmem_tz : t * z ∈ conjClassIn T t := by
    rw [hclass]
    exact Set.mem_insert_of_mem _ rfl
  obtain ⟨τ, hτT, hτ⟩ := hmem_tz
  have hne : t ≠ z := by
    intro h
    apply ht1
    have h1 : τ * t * τ⁻¹ = 1 := by
      rw [← hτ, ← h]
      exact ht2
    exact conj_eq_one_iff.mp h1
  obtain ⟨hconjT, -⟩ := sec11_conj_cases hclass
  have hTz := sec11_fix_z_of_class ht2 hz2 htz hz1 hclass
  have hcomm := sec11_zpowers_comm htz
  have hconjV : ∀ ρ ∈ T, ∀ h ∈ zpowers t ⊔ zpowers z, ρ * h * ρ⁻¹ ∈ zpowers t ⊔ zpowers z := by
    intro ρ hρ h hh
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm hh
    have e : ρ * (a * b) * ρ⁻¹ = (ρ * a * ρ⁻¹) * (ρ * b * ρ⁻¹) := by group
    rw [e]
    refine Subgroup.mul_mem _ ?_ ?_
    · rcases sec11_eq_one_or_of_mem_zpowers ht2 ha with h1 | h1
      · rw [h1]
        simp
      · rw [h1]
        rcases hconjT ρ hρ with h2 | h2 <;> rw [h2]
        · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
        · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
            (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
    · rcases sec11_eq_one_or_of_mem_zpowers hz2 hb with h1 | h1
      · rw [h1]
        simp
      · rw [h1, hTz ρ hρ]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have hTP : T ≤ hatCent t z := by
    intro σ hσ
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, ?_⟩
    · exact mul_inv_eq_iff_eq_mul.mp (hTz σ hσ)
    · refine Subgroup.mem_normalizer_iff.mpr fun h => ⟨hconjV σ hσ h, fun hh => ?_⟩
      have h' := hconjV σ⁻¹ (T.inv_mem hσ) _ hh
      have e : σ⁻¹ * (σ * h * σ⁻¹) * σ⁻¹⁻¹ = h := by group
      rwa [e] at h'
  set P : Subgroup G := hatCent t z with hP
  set C : Subgroup G := P ⊓ centralizer ({t} : Set G) with hC
  have hCP : C ≤ P := inf_le_left
  have hCZ : C ≤ centralizer ({t} : Set G) := inf_le_right
  have hSP : S ≤ P := hctx.S_le.trans hTP
  have hSC : S ≤ C := le_inf hSP hctx.sylow.1
  have hmemC : ∀ x ∈ P, x ∈ C ↔ x * t * x⁻¹ = t := by
    intro x hx
    rw [hC, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
    exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩
  have htzt : t * z ≠ t := by
    intro h
    exact hz1 (mul_left_cancel (h.trans (mul_one t).symm))
  have hCindex : C.relIndex P = 2 := by
    show (C.subgroupOf P).index = 2
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨τ, hTP hτT⟩, fun b => ?_⟩
    have hbP : (b : G) ∈ hatCent t z := b.2
    have hbt := sec11_hatCent_conj ht2 hz2 htz ht1 hne hbP
    have hbz : (b : G) * z * (b : G)⁻¹ = z := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hbP).1, mul_assoc,
        mul_inv_cancel, mul_one]
    have hbτP : (b : G) * τ ∈ P := P.mul_mem b.2 (hTP hτT)
    have hbτ : (b : G) * τ * t * ((b : G) * τ)⁻¹ = (b : G) * (t * z) * (b : G)⁻¹ := by
      rw [hτ]
      group
    have hbtz : (b : G) * (t * z) * (b : G)⁻¹ =
        ((b : G) * t * (b : G)⁻¹) * ((b : G) * z * (b : G)⁻¹) := by
      group
    show Xor ((b : G) * τ ∈ C) ((b : G) ∈ C)
    rw [hmemC _ hbτP, hmemC _ b.2]
    rcases hbt with h | h
    · refine Or.inr ⟨h, fun h' => htzt ?_⟩
      rw [hbτ, hbtz, h, hbz] at h'
      exact h'
    · refine Or.inl ⟨?_, fun h' => htzt (h.symm.trans h')⟩
      rw [hbτ, hbtz, h, hbz, mul_assoc, hz2, mul_one]
  have hSC' : ¬ 2 ∣ S.relIndex C := by
    intro hd
    apply hctx.sylow.2.2
    rw [← Subgroup.relIndex_mul_relIndex S C (centralizer ({t} : Set G)) hSC hCZ]
    exact Dvd.dvd.mul_right hd _
  have h1 := Subgroup.relIndex_mul_relIndex S T P hctx.S_le hTP
  have h2 := Subgroup.relIndex_mul_relIndex S C P hSC hCP
  rw [hidx] at h1
  rw [hCindex] at h2
  have h3 : T.relIndex P = S.relIndex C := by omega
  refine ⟨hTP, hctx.sylowT.2.1, ?_⟩
  rw [h3]
  exact hSC'

end CFSG.OddStandard.SmallF3.Omega
