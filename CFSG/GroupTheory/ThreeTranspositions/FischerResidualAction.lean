module

public import CFSG.GroupTheory.ThreeTranspositions.FischerResidual
public import TauCeti.GroupTheory.QuotientGroup.MulAut

import CFSG.GroupTheory.PermFiveNormalElemAbelian

public section

namespace CFSG.GroupTheory.ThreeTranspositions

open CFSG.Blueprint.Fischer CFSG.Fischer.Classification CFSG.Fischer

variable {X : Type} [Group X]

theorem exists_normal_le_threeResidualQuot {E : Set X} (hP : Pair X E)
    (h2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥)
    (h3 : ∀ N : Subgroup X, N.Normal → IsPGroup 3 N → N ≤ Subgroup.center X)
    {d : X} (hd : d ∈ E) :
    ∃ N : Subgroup (X ⧸ Subgroup.center X), N.Normal ∧
      Subgroup.centralizer (N : Set (X ⧸ Subgroup.center X)) = ⊥ ∧
      N ≤ threeResidualQuot d := by
  have : Finite X := Pair.finite hP
  obtain ⟨N, hNn, hNbot, hNs, hNsol, hcent⟩ :=
    exists_minimalNormal_quotient_center hP h2 h3
  have hPq : Pair (X ⧸ Subgroup.center X) ((QuotientGroup.mk' (Subgroup.center X)) '' E) :=
    pair_quot_center hP h2
  have hZ : Subgroup.center (X ⧸ Subgroup.center X) = ⊥ :=
    Pair.center_quotient_center_eq_bot hP
  have hNle : N ≤ commutator (X ⧸ Subgroup.center X) :=
    le_commutator_of_isSimpleGroup_of_not_isSolvable hNs hNsol
  have hOeq : CFSG.Quasithin.pResidualOf 3 (commutator (X ⧸ Subgroup.center X)) = N :=
    pResidualOf_three_commutator_eq hPq hZ hNn hNbot hNs hNsol hNle
  have hquot := threeResidualQuot_eq_Kgrp hPq hZ hNn hNs hNbot hOeq hd
  refine ⟨N, hNn, hcent, ?_⟩
  rw [hquot]
  exact CFSG.RankThree.PartOne.FIS.normal_le_closure_conjOrbit hPq hZ hNn hNs hNbot
    ⟨d, hd, rfl⟩

theorem mapQuotient_conjNormal_eq_self_of_fixes_normal {G : Type*} [Group G] [Finite G]
    {N : Subgroup G} [N.Normal] [hC : (Subgroup.center N).Characteristic]
    {K : Subgroup (N ⧸ Subgroup.center N)} (hK : K.Normal)
    (hKc : Subgroup.centralizer (K : Set (N ⧸ Subgroup.center N)) = ⊥) {g : G}
    (hg : ∀ n : N, (QuotientGroup.mk n : N ⧸ Subgroup.center N) ∈ K →
      (MulAut.conjNormal (H := N) g) n / n ∈ Subgroup.center N) :
    ∀ x : N ⧸ Subgroup.center N,
      (MulAut.mapQuotient (Subgroup.center N)) (MulAut.conjNormal (H := N) g) x = x := by
  classical
  let σ : MulAut (N ⧸ Subgroup.center N) :=
    (MulAut.mapQuotient (Subgroup.center N)) (MulAut.conjNormal (H := N) g)
  have hσ_mk : ∀ n : N, σ (QuotientGroup.mk n) =
      QuotientGroup.mk ((MulAut.conjNormal (H := N) g) n) := by
    intro n
    simp [σ, MulAut.mapQuotient_mk]
  have hfixK : ∀ k : N, (QuotientGroup.mk k : N ⧸ Subgroup.center N) ∈ K →
      σ (QuotientGroup.mk k) = QuotientGroup.mk k := by
    intro k hk
    rw [hσ_mk, QuotientGroup.eq_iff_div_mem]
    exact hg k hk
  intro x
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective x
  have hc : (QuotientGroup.mk n)⁻¹ * σ (QuotientGroup.mk n) ∈
      Subgroup.centralizer (K : Set (N ⧸ Subgroup.center N)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    obtain ⟨k', rfl⟩ := QuotientGroup.mk_surjective k
    have hk' : (QuotientGroup.mk k' : N ⧸ Subgroup.center N) ∈ K := hk
    have hfix := hfixK k' hk'
    have hnk : (QuotientGroup.mk n) * (QuotientGroup.mk k') * (QuotientGroup.mk n)⁻¹ ∈ K :=
      hK.conj_mem _ hk' _
    have hfix2 := hfixK _ hnk
    have h3 : σ (QuotientGroup.mk n) * (QuotientGroup.mk k') *
        (σ (QuotientGroup.mk n))⁻¹ =
          (QuotientGroup.mk n) * (QuotientGroup.mk k') * (QuotientGroup.mk n)⁻¹ := by
      calc
        σ (QuotientGroup.mk n) * (QuotientGroup.mk k') * (σ (QuotientGroup.mk n))⁻¹
            = σ ((QuotientGroup.mk n) * (QuotientGroup.mk k') *
                (QuotientGroup.mk n)⁻¹) := by
              rw [map_mul, map_mul, map_inv, hfix]
        _ = (QuotientGroup.mk n) * (QuotientGroup.mk k') * (QuotientGroup.mk n)⁻¹ := hfix2
    have hceq : ((QuotientGroup.mk n)⁻¹ * σ (QuotientGroup.mk n)) *
        (QuotientGroup.mk k') * ((QuotientGroup.mk n)⁻¹ * σ (QuotientGroup.mk n))⁻¹ =
          (QuotientGroup.mk k') := by
      calc
        ((QuotientGroup.mk n)⁻¹ * σ (QuotientGroup.mk n)) * (QuotientGroup.mk k') *
            ((QuotientGroup.mk n)⁻¹ * σ (QuotientGroup.mk n))⁻¹
            = (QuotientGroup.mk n)⁻¹ *
                (σ (QuotientGroup.mk n) * (QuotientGroup.mk k') *
                  (σ (QuotientGroup.mk n))⁻¹) * (QuotientGroup.mk n) := by group
        _ = (QuotientGroup.mk n)⁻¹ *
              ((QuotientGroup.mk n) * (QuotientGroup.mk k') * (QuotientGroup.mk n)⁻¹) *
              (QuotientGroup.mk n) := by rw [h3]
        _ = (QuotientGroup.mk k') := by group
    have hck : ((QuotientGroup.mk n)⁻¹ * σ (QuotientGroup.mk n)) * (QuotientGroup.mk k') =
        (QuotientGroup.mk k') * ((QuotientGroup.mk n)⁻¹ * σ (QuotientGroup.mk n)) := by
      calc
        ((QuotientGroup.mk n)⁻¹ * σ (QuotientGroup.mk n)) * (QuotientGroup.mk k')
            = (((QuotientGroup.mk n)⁻¹ * σ (QuotientGroup.mk n)) * (QuotientGroup.mk k') *
                ((QuotientGroup.mk n)⁻¹ * σ (QuotientGroup.mk n))⁻¹) *
                ((QuotientGroup.mk n)⁻¹ * σ (QuotientGroup.mk n)) := by group
        _ = (QuotientGroup.mk k') * ((QuotientGroup.mk n)⁻¹ * σ (QuotientGroup.mk n)) := by
              rw [hceq]
    exact hck.symm
  rw [hKc, Subgroup.mem_bot] at hc
  have h := congrArg (fun t => (QuotientGroup.mk n) * t) hc
  simpa [σ, MulAut.mapQuotient_mk, mul_assoc] using h

theorem mem_centralizer_of_trivial_on_normal {G : Type*} [Group G] [Finite G]
    {N : Subgroup G} [N.Normal]
    (hgen : Subgroup.closure {x : N | x ^ 2 = 1} = ⊤)
    (hZodd : Odd (Nat.card (Subgroup.center N)))
    {K : Subgroup (N ⧸ Subgroup.center N)} (hK : K.Normal)
    (hKc : Subgroup.centralizer (K : Set (N ⧸ Subgroup.center N)) = ⊥) {g : G}
    (hg : ∀ n : N, (QuotientGroup.mk n : N ⧸ Subgroup.center N) ∈ K →
      (MulAut.conjNormal (H := N) g) n / n ∈ Subgroup.center N) :
    g ∈ Subgroup.centralizer (N : Set G) := by
  classical
  have hfixAll := mapQuotient_conjNormal_eq_self_of_fixes_normal hK hKc hg
  refine mem_centralizer_of_conjNormal_div_mem_center hgen hZodd ?_
  intro n
  have hmkeq :
      (QuotientGroup.mk' (Subgroup.center N)) ((MulAut.conjNormal (H := N) g) n) =
        (QuotientGroup.mk' (Subgroup.center N)) n := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      ← MulAut.mapQuotient_mk (N := Subgroup.center N)
        (MulAut.conjNormal (H := N) g) n, hfixAll]
  exact QuotientGroup.eq_iff_div_mem.mp hmkeq

theorem map_centralizer_eq_of_odd_ker {W K : Type*} [Group W] [Group K]
    (π : W →* K) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center W)
    (hodd : Odd (Nat.card π.ker)) {d : W} (hd : d ^ 2 = 1) :
    (Subgroup.centralizer ({d} : Set W)).map π =
      Subgroup.centralizer ({π d} : Set K) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨w, hw, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hwd : w * d = d * w := by
      have hw' : w ∈ Subgroup.centralizer ({d} : Set W) := hw
      exact Subgroup.mem_centralizer_singleton_iff.mp hw'
    rw [← map_mul, ← map_mul, hwd]
  · intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff] at hk
    obtain ⟨w, rfl⟩ := hπ k
    set c : W := w * d * w⁻¹ * d⁻¹ with hc
    have hc_ker : c ∈ π.ker := by
      rw [MonoidHom.mem_ker, hc, map_mul, map_mul, map_inv, map_mul, map_inv]
      rw [hk]
      group
    have hc_center : c ∈ Subgroup.center W := hker hc_ker
    have hc_comm : Commute c d := (Subgroup.mem_center_iff.mp hc_center d).symm
    have hcd : c * d = w * d * w⁻¹ := by
      rw [hc]
      group
    have hsq : (c * d) ^ 2 = 1 := by
      rw [hcd]
      rw [show w * d * w⁻¹ = (MulAut.conj w) d from rfl, ← map_pow, hd, map_one]
    have hc2 : c ^ 2 = 1 := by
      have hpow := hc_comm.mul_pow 2
      rw [hsq, hd, mul_one] at hpow
      exact hpow.symm
    have hc1 : c = 1 := by
      have hcop : Nat.Coprime (orderOf c) (Nat.card π.ker) :=
        (Nat.coprime_two_left.2 hodd).coprime_dvd_left (orderOf_dvd_of_pow_eq_one hc2)
      have hdvd : orderOf c ∣ Nat.card π.ker :=
        Subgroup.orderOf_dvd_natCard π.ker hc_ker
      exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hdvd)
    refine Subgroup.mem_map.mpr ⟨w, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hwd : w * d * w⁻¹ = d := by
      have h : c * d = d := by rw [hc1, one_mul]
      rwa [hcd] at h
    calc
      w * d = (w * d * w⁻¹) * w := by group
      _ = d * w := by rw [hwd]

end CFSG.GroupTheory.ThreeTranspositions
