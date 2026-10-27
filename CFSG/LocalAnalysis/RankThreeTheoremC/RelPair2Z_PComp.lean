module

import CFSG.Walter.AStar.Subnormal
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Struct
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem zjc_sylow_le {p : ℕ} [Fact p.Prime] {J : Type} [Group J] [Finite J] {H : Subgroup J}
    (hH : H.IsSubnormal) (hidx : ¬ p ∣ H.index) (S : Sylow p J) : (S : Subgroup J) ≤ H := by
  obtain ⟨P, hP⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal S hH
  have h1 : Nat.card (S ⊓ H : Subgroup J) = Nat.card P := by
    rw [← hP, Subgroup.card_map_of_injective H.subtype_injective]
  have hcard : Nat.card J = H.index * Nat.card H := by
    rw [mul_comm]; exact (Subgroup.card_mul_index H).symm
  have hH0 : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have hi0 : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hfac : (Nat.card J).factorization p = (Nat.card H).factorization p := by
    rw [hcard, Nat.factorization_mul hi0 hH0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hidx, zero_add]
  have h2 : Nat.card P = Nat.card S := by
    rw [Sylow.card_eq_multiplicity P, Sylow.card_eq_multiplicity S, hfac]
  have h3 : (S ⊓ H : Subgroup J) = S := by
    refine Subgroup.eq_of_le_of_card_ge inf_le_left ?_
    rw [h1, h2]
  exact h3 ▸ inf_le_right

theorem isPComponent_of_normal {p : ℕ} (hp : p.Prime) {X : Type} [Group X] [Finite X]
    {J : Subgroup X} (hJn : J.Normal) (hJp : pElementSubgroup p J = J)
    {L : Subgroup (X ⧸ CFSG.pPrimeCore p X)} (hL : CFSG.IsComponent L)
    (hJL : J.map (QuotientGroup.mk' (CFSG.pPrimeCore p X)) = L) : CFSG.IsPComponent p J := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨L, hL, hJn.isSubnormal, hJL, ?_⟩
  intro J' hlt hJ'sub hJ'L
  have hJ'le : J' ≤ J := hlt.le
  set K₀ := CFSG.pPrimeCore p X with hK₀
  have hsup : J ≤ (J ⊓ K₀) ⊔ J' := by
    intro x hx
    have hmem : QuotientGroup.mk' K₀ x ∈ J'.map (QuotientGroup.mk' K₀) := by
      rw [hJ'L, ← hJL]
      exact ⟨x, hx, rfl⟩
    obtain ⟨j, hj, hjx⟩ := hmem
    have hxj : x * j⁻¹ ∈ J ⊓ K₀ := by
      refine ⟨J.mul_mem hx (J.inv_mem (hJ'le hj)), ?_⟩
      show x * j⁻¹ ∈ K₀
      rw [← QuotientGroup.eq_one_iff]
      change QuotientGroup.mk' K₀ (x * j⁻¹) = 1
      rw [map_mul, map_inv, ← hjx, mul_inv_cancel]
    have : x = (x * j⁻¹) * j := by group
    rw [this]
    exact Subgroup.mul_mem_sup hxj hj
  have hNJ : (J ⊓ K₀) ⊔ J' = J := le_antisymm (sup_le inf_le_left hJ'le) hsup
  have hidx : ¬ p ∣ (J'.subgroupOf J).index := by
    have h1 := CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal (J ⊓ K₀) J'
    rw [hNJ] at h1
    have h2 : (J'.subgroupOf J).index ∣ Nat.card (J ⊓ K₀ : Subgroup X) := by
      have := Subgroup.relIndex_dvd_card (H := J') (K := J ⊓ K₀)
      rw [← h1] at this
      exact this
    have h3 : Nat.card (J ⊓ K₀ : Subgroup X) ∣ Nat.card K₀ := Subgroup.card_dvd_of_le inf_le_right
    have h4 : p.Coprime (Nat.card K₀) := CFSG.pPrimeCore_coprime_card
    intro hd
    exact hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes h4 (dvd_refl p) (hd.trans (h2.trans h3)))
  have hall : ∀ x ∈ J, (∃ k : ℕ, orderOf x = p ^ k) → x ∈ J' := by
    rintro x hxJ ⟨k, hk⟩
    have hx'p : IsPGroup p (Subgroup.zpowers (⟨x, hxJ⟩ : ↥J)) := by
      refine IsPGroup.of_card (n := k) ?_
      rw [Nat.card_zpowers, Subgroup.orderOf_mk, hk]
    obtain ⟨S, hS⟩ := hx'p.exists_le_sylow
    have hSH := zjc_sylow_le (Subgroup.IsSubnormal.subgroupOf (K := J) hJ'sub) hidx S
    exact hSH (hS (Subgroup.mem_zpowers _))
  apply hlt.not_ge
  conv_lhs => rw [← hJp]
  exact (Subgroup.closure_le _).mpr fun x hx => hall x hx.1 hx.2

theorem zjc_exists_pElement_lift {p : ℕ} (hp : p.Prime) {A B : Type} [Group A] [Finite A]
    [Group B] (f : A →* B) {a : A} {k : ℕ} (hk : orderOf (f a) = p ^ k) :
    ∃ a' : A, a' ∈ Subgroup.zpowers a ∧ f a' = f a ∧ ∃ j : ℕ, orderOf a' = p ^ j := by
  have hn0 : orderOf a ≠ 0 := (orderOf_pos a).ne'
  obtain ⟨α, m, hm, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 p hp.ne_one
  have hcop2 : Nat.Coprime (p ^ α) m :=
    Nat.Coprime.pow_left α ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm)
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop2
  have hcn : a ^ orderOf a = 1 := pow_orderOf_eq_one a
  have hc1 : a ^ (v * (m : ℤ)) * a ^ (u * ((p ^ α : ℕ) : ℤ)) = a := by
    rw [← zpow_add]
    have : v * (m : ℤ) + u * ((p ^ α : ℕ) : ℤ) = 1 := by linarith
    rw [this, zpow_one]
  have hord1 : ∃ j : ℕ, orderOf (a ^ (v * (m : ℤ))) = p ^ j := by
    have h1 : (a ^ (v * (m : ℤ))) ^ (p ^ α) = 1 := by
      rw [← zpow_natCast, ← zpow_mul]
      have : v * (m : ℤ) * ((p ^ α : ℕ) : ℤ) = (orderOf a : ℤ) * v := by
        rw [hn]; push_cast; ring
      rw [this, zpow_mul, zpow_natCast, hcn, one_zpow]
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one h1)
    exact ⟨j, hj⟩
  have hf2 : f (a ^ (u * ((p ^ α : ℕ) : ℤ))) = 1 := by
    have h2 : (f (a ^ (u * ((p ^ α : ℕ) : ℤ)))) ^ (p ^ k) = 1 := by
      rw [map_zpow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hk,
        pow_orderOf_eq_one, one_zpow]
    have h3 : (f (a ^ (u * ((p ^ α : ℕ) : ℤ)))) ^ m = 1 := by
      rw [← map_pow, ← zpow_natCast, ← zpow_mul]
      have : u * ((p ^ α : ℕ) : ℤ) * (m : ℤ) = (orderOf a : ℤ) * u := by
        rw [hn]; push_cast; ring
      rw [this, zpow_mul, zpow_natCast, hcn, one_zpow, map_one]
    have hcop3 : Nat.Coprime (p ^ k) m :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm)
    exact orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes hcop3 (orderOf_dvd_of_pow_eq_one h2)
        (orderOf_dvd_of_pow_eq_one h3))
  refine ⟨a ^ (v * (m : ℤ)), Subgroup.zpow_mem_zpowers _ _, ?_, hord1⟩
  conv_rhs => rw [← hc1]
  rw [map_mul, hf2, mul_one]

theorem exists_pComponent_normal {p : ℕ} (hp : p.Prime) {Y : Type} [Group Y] [Finite Y]
    {L : Subgroup (Y ⧸ CFSG.pPrimeCore p Y)} (hL : CFSG.IsComponent L) (hLn : L.Normal)
    (hLz : center L = ⊥) (hpL : p ∣ Nat.card L) :
    ∃ J : Subgroup Y, J.Normal ∧ CFSG.IsPComponent p J ∧
      J.map (QuotientGroup.mk' (CFSG.pPrimeCore p Y)) = L ∧ pElementSubgroup p J = J ∧
      ⁅J, J⁆ = J ∧ (CFSG.pPrimeCore p ↥J).map J.subtype = J ⊓ CFSG.pPrimeCore p Y := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set K₀ := CFSG.pPrimeCore p Y with hK₀
  set π : Y →* Y ⧸ K₀ := QuotientGroup.mk' K₀ with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective K₀
  set A : Subgroup Y := L.comap π with hA
  have hAn : A.Normal := Subgroup.Normal.comap hLn π
  set S : Set Y := {x | x ∈ A ∧ ∃ k : ℕ, orderOf x = p ^ k} with hS
  set J : Subgroup Y := pElementSubgroup p A with hJ
  have hJA : J ≤ A := pElementSubgroup_le A
  have hJn : J.Normal := by
    refine ⟨fun n hn g => ?_⟩
    induction hn using Subgroup.closure_induction with
    | mem x hx =>
      refine Subgroup.subset_closure ⟨?_, ?_⟩
      · exact hAn.conj_mem x hx.1 g
      · obtain ⟨k, hk⟩ := hx.2
        refine ⟨k, ?_⟩
        have h := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
        simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply] at h
        rw [h, hk]
    | one => simp
    | mul x y _ _ hx hy =>
      have := J.mul_mem hx hy
      simpa [mul_assoc] using this
    | inv x _ hx =>
      have := J.inv_mem hx
      simpa [mul_assoc] using this
  have hJpel : pElementSubgroup p J = J := by
    refine le_antisymm (pElementSubgroup_le J) ?_
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    exact Subgroup.subset_closure ⟨Subgroup.subset_closure hx, hx.2⟩
  have hLs : IsSimpleGroup L := by
    obtain ⟨-, hS1, -⟩ := hL.1
    let q1 : ↥L ⧸ Subgroup.center ↥L ≃* ↥L :=
      (QuotientGroup.quotientMulEquivOfEq hLz).trans QuotientGroup.quotientBot
    have : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hS1
    exact q1.symm.isSimpleGroup
  have hJL : J.map π = L := by
    refine le_antisymm (fun y ⟨x, hx, hxy⟩ => hxy ▸ hJA hx) ?_
    have hMn : (J.map π).Normal := Subgroup.Normal.map hJn π hπs
    obtain ⟨l, hl⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) p hpL
    obtain ⟨a, ha⟩ := hπs (l : Y ⧸ K₀)
    have haA : a ∈ A := by
      show π a ∈ L
      rw [ha]
      exact l.2
    have hord : orderOf (π a) = p ^ 1 := by
      rw [ha, Subgroup.orderOf_coe, hl, pow_one]
    obtain ⟨a', ha'z, ha'π, hj⟩ := zjc_exists_pElement_lift hp π hord
    have ha'A : a' ∈ A := (Subgroup.zpowers_le.mpr haA) ha'z
    have hl1 : (l : Y ⧸ K₀) ∈ J.map π := ⟨a', Subgroup.subset_closure ⟨ha'A, hj⟩, by
      rw [ha'π, ha]⟩
    have hne : (J.map π).subgroupOf L ≠ ⊥ := by
      intro hbot
      have : l ∈ (J.map π).subgroupOf L := hl1
      rw [hbot, Subgroup.mem_bot] at this
      rw [this, orderOf_one] at hl
      exact hp.one_lt.ne hl
    have := (hMn.subgroupOf L)
    have htop := (IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((J.map π).subgroupOf L)).resolve_left hne
    intro x hx
    have : (⟨x, hx⟩ : ↥L) ∈ (J.map π).subgroupOf L := by rw [htop]; trivial
    exact this
  have hpc : CFSG.IsPComponent p J := isPComponent_of_normal hp hJn hJpel hL hJL
  refine ⟨J, hJn, hpc, hJL, hJpel, ?_, ?_⟩
  ·
    obtain ⟨K', hK', -, hmapK', hmin⟩ := hpc
    have hK'L : K' = L := hmapK'.symm.trans hJL
    have hcn : (⁅J, J⁆ : Subgroup Y).Normal := inferInstance
    have hle : ⁅J, J⁆ ≤ J := Subgroup.commutator_le_left J J
    by_contra hne
    have hlt : ⁅J, J⁆ < J := lt_of_le_of_ne hle hne
    refine hmin _ hlt hcn.isSubnormal ?_
    rw [hK'L, Subgroup.map_commutator, hJL]
    have hperf : ⁅(⊤ : Subgroup ↥L), ⊤⁆ = ⊤ := hL.1.1.commutator_eq_top
    have := congrArg (Subgroup.map L.subtype) hperf
    rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype] at this
    exact this
  ·
    set Sc : Subgroup Y := (CFSG.pPrimeCore p ↥J).map J.subtype with hSc
    have hSn : Sc.Normal := by
      have : (CFSG.pPrimeCore p ↥J).Characteristic := inferInstance
      rw [hSc]
      infer_instance
    have hScJ : Sc ≤ J := Subgroup.map_subtype_le _
    have hcopSc : p.Coprime (Nat.card Sc) := by
      rw [hSc, Subgroup.card_map_of_injective J.subtype_injective]
      exact CFSG.pPrimeCore_coprime_card
    refine le_antisymm (le_inf hScJ (ths_le_pPrimeCore_of_isSubnormal hSn.isSubnormal hcopSc)) ?_
    intro y hy
    have hM0 : ((J ⊓ K₀).subgroupOf J) ≤ CFSG.pPrimeCore p ↥J := by
      refine le_sSup ⟨?_, ?_⟩
      · exact Subgroup.Normal.subgroupOf inferInstance J
      · have h1 : Nat.card ((J ⊓ K₀).subgroupOf J) ∣ Nat.card K₀ := by
          rw [← Subgroup.card_map_of_injective J.subtype_injective,
            Subgroup.map_subgroupOf_eq_of_le inf_le_left]
          exact Subgroup.card_dvd_of_le inf_le_right
        exact Nat.Coprime.coprime_dvd_right h1 CFSG.pPrimeCore_coprime_card
    have : (⟨y, hy.1⟩ : ↥J) ∈ CFSG.pPrimeCore p ↥J := hM0 (Subgroup.mem_subgroupOf.mpr hy)
    exact ⟨⟨y, hy.1⟩, this, rfl⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
