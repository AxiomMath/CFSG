module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.MultA2

variable {J : Type} [Group J]

theorem mem_of_pow_mem {H : Subgroup J} {k : J} {m : ℕ} (hm : Nat.Coprime m (orderOf k))
    (hkm : k ^ m ∈ H) : k ∈ H := by
  have hgab := Nat.gcd_eq_gcd_ab m (orderOf k)
  rw [Nat.Coprime.gcd_eq_one hm] at hgab
  set u := Nat.gcdA m (orderOf k)
  set v := Nat.gcdB m (orderOf k)
  have hd : k ^ (orderOf k : ℤ) = 1 := by rw [zpow_natCast, pow_orderOf_eq_one]
  have hexp : (m : ℤ) * u + (orderOf k : ℤ) * v = 1 := hgab.symm
  have e1 : k ^ ((m : ℤ) * u + (orderOf k : ℤ) * v) = k := by rw [hexp, zpow_one]
  rw [zpow_add, zpow_mul, zpow_mul, hd, one_zpow, mul_one, zpow_natCast] at e1
  rw [← e1]
  exact H.zpow_mem hkm u

theorem key_center {S : Type} [Group S] [Finite J] (ψ : J →* S) (R : Subgroup J) [hRn : R.Normal]
    (hR3 : Nat.Coprime 3 (Nat.card R))
    (hQs : IsSimpleGroup (J ⧸ R))
    (hQz : Subgroup.center (J ⧸ R) = ⊥)
    (hrange : IsSimpleGroup ↥ψ.range)
    (hN : ∀ k : J, ψ k = 1 → ∃ a : ℕ, k ^ (3 ^ a) ∈ R)
    (hZ : ∀ k : J, ψ k = 1 → ∃ a : ℕ, k ^ (3 ^ a) ∈ Subgroup.center J) :
    ψ.ker = R ∧ Subgroup.center J = R := by
  classical
  haveI : Nontrivial (J ⧸ R) := hQs.toNontrivial
  have hRord : ∀ r ∈ R, Nat.Coprime 3 (orderOf r) := by
    intro r hr
    have hd : orderOf (⟨r, hr⟩ : R) ∣ Nat.card R := orderOf_dvd_natCard _
    rw [← Subgroup.orderOf_mk r hr]
    exact Nat.Coprime.coprime_dvd_right hd hR3
  have hKR : ψ.ker ≤ R := by
    let π : J →* J ⧸ R := QuotientGroup.mk' R
    have hKb : (ψ.ker.map π).Normal :=
      Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective R)
    rcases hQs.eq_bot_or_eq_top_of_normal (ψ.ker.map π) with h | h
    · intro k hk
      have hmem : π k ∈ ψ.ker.map π := Subgroup.mem_map_of_mem π hk
      rw [h, Subgroup.mem_bot] at hmem
      exact (QuotientGroup.eq_one_iff k).1 hmem
    · exfalso
      have hPG : IsPGroup 3 (J ⧸ R) := by
        intro y
        have hy : y ∈ ψ.ker.map π := by rw [h]; exact Subgroup.mem_top y
        obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hy
        obtain ⟨a, ha⟩ := hN k (MonoidHom.mem_ker.1 hk)
        refine ⟨a, ?_⟩
        rw [← map_pow]
        exact (QuotientGroup.eq_one_iff _).2 ha
      have hc := IsPGroup.center_nontrivial hPG
      rw [hQz] at hc
      exact not_nontrivial_iff_subsingleton.2 inferInstance hc
  have hRK : R ≤ ψ.ker := by
    let Tr : Subgroup ↥ψ.range := (R.map ψ).subgroupOf ψ.range
    have hTr : Tr.Normal := by
      refine ⟨fun n hn g => ?_⟩
      obtain ⟨j, hj⟩ := MonoidHom.mem_range.1 g.2
      obtain ⟨r, hr, hrn⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hn)
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      refine ⟨j * r * j⁻¹, hRn.conj_mem r hr j, ?_⟩
      simp [map_mul, map_inv, hj, hrn]
    rcases hrange.eq_bot_or_eq_top_of_normal Tr with h | h
    · intro r hr
      have hmem : (⟨ψ r, MonoidHom.mem_range.2 ⟨r, rfl⟩⟩ : ↥ψ.range) ∈ Tr := by
        rw [Subgroup.mem_subgroupOf]
        exact Subgroup.mem_map_of_mem ψ hr
      rw [h, Subgroup.mem_bot] at hmem
      exact MonoidHom.mem_ker.2 (congrArg Subtype.val hmem)
    · exfalso
      apply not_subsingleton_iff_nontrivial.2 (inferInstance : Nontrivial (J ⧸ R))
      rw [QuotientGroup.subsingleton_iff, eq_top_iff]
      intro j _
      have hmem : (⟨ψ j, MonoidHom.mem_range.2 ⟨j, rfl⟩⟩ : ↥ψ.range) ∈ Tr := by
        rw [h]; exact Subgroup.mem_top _
      obtain ⟨r, hr, hrj⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hmem)
      have hrj' : ψ r = ψ j := hrj
      have hk : r⁻¹ * j ∈ ψ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hrj', inv_mul_cancel]
      have hkR := hKR hk
      have hj : j = r * (r⁻¹ * j) := by group
      rw [hj]
      exact R.mul_mem hr hkR
  have hKeq : ψ.ker = R := le_antisymm hKR hRK
  have hZR : Subgroup.center J ≤ R := by
    intro z hz
    have hcentr : (⟨ψ z, MonoidHom.mem_range.2 ⟨z, rfl⟩⟩ : ↥ψ.range) ∈
        Subgroup.center ↥ψ.range := by
      rw [Subgroup.mem_center_iff]
      rintro ⟨g, hg⟩
      obtain ⟨j, rfl⟩ := MonoidHom.mem_range.1 hg
      apply Subtype.ext
      show ψ j * ψ z = ψ z * ψ j
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz j]
    rcases hrange.eq_bot_or_eq_top_of_normal (Subgroup.center ↥ψ.range) with hc | hc
    · have h1 : (⟨ψ z, MonoidHom.mem_range.2 ⟨z, rfl⟩⟩ : ↥ψ.range) = 1 := by
        rw [hc] at hcentr
        exact Subgroup.mem_bot.1 hcentr
      have hk : z ∈ ψ.ker := MonoidHom.mem_ker.2 (congrArg Subtype.val h1)
      rw [hKeq] at hk
      exact hk
    · exfalso
      have hcomm : ∀ x y : ↥ψ.range, x * y = y * x := by
        intro x y
        have hx : x ∈ Subgroup.center ↥ψ.range := by rw [hc]; exact Subgroup.mem_top x
        exact (Subgroup.mem_center_iff.1 hx y).symm
      have hQc : Subgroup.center (J ⧸ R) = ⊤ := by
        rw [eq_top_iff]
        intro x _
        rw [Subgroup.mem_center_iff]
        intro y
        obtain ⟨j1, rfl⟩ := QuotientGroup.mk_surjective x
        obtain ⟨j2, rfl⟩ := QuotientGroup.mk_surjective y
        have hc2 := hcomm ⟨ψ j1, MonoidHom.mem_range.2 ⟨j1, rfl⟩⟩
          ⟨ψ j2, MonoidHom.mem_range.2 ⟨j2, rfl⟩⟩
        have hc2' : ψ j1 * ψ j2 = ψ j2 * ψ j1 := congrArg Subtype.val hc2
        have hin : (j1 * j2)⁻¹ * (j2 * j1) ∈ R := by
          rw [← hKeq, MonoidHom.mem_ker]
          simp only [map_mul, map_inv]
          rw [← hc2']
          group
        have hQeq : ((j1 * j2 : J) : J ⧸ R) = ((j2 * j1 : J) : J ⧸ R) := QuotientGroup.eq.2 hin
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul] at hQeq
        exact hQeq.symm
      have htb : (⊤ : Subgroup (J ⧸ R)) = ⊥ := hQc.symm.trans hQz
      apply not_subsingleton_iff_nontrivial.2 (inferInstance : Nontrivial (J ⧸ R))
      refine ⟨fun a b => ?_⟩
      have ha : a ∈ (⊥ : Subgroup (J ⧸ R)) := htb ▸ Subgroup.mem_top a
      have hb : b ∈ (⊥ : Subgroup (J ⧸ R)) := htb ▸ Subgroup.mem_top b
      rw [Subgroup.mem_bot] at ha hb
      rw [ha, hb]
  have hRZ : R ≤ Subgroup.center J := by
    intro r hr
    have hkr : ψ r = 1 := by
      have : r ∈ ψ.ker := by rw [hKeq]; exact hr
      exact MonoidHom.mem_ker.1 this
    obtain ⟨a, ha⟩ := hZ r hkr
    have hcop : Nat.Coprime (3 ^ a) (orderOf r) := Nat.Coprime.pow_left a (hRord r hr)
    exact mem_of_pow_mem hcop ha
  exact ⟨hKeq, le_antisymm hZR hRZ⟩

end CFSG.LocalAnalysis.GLTheoremA.CatB.MultA2

end
