module

public import CFSG.ClassicalInvolution.Q3.TL4MFMuZ2Syl
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenSDMuC
public import CFSG.ClassicalInvolution.Q3.TA3SmallCriteria
public import CFSG.ClassicalInvolution.Q3.TL3S8Setup

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.MFMuZ2

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.Q3T6

variable {X : Type} [Group X] [Finite X] {R : Subgroup X} {S : Sylow 2 R} {z : X}

theorem card_sylow_eq_sixteen (hB3 : GoldschmidtB3Tmp) (hd : TightDatum R S z)
    (hq : Nonempty ((S : Subgroup R) ≃* QuaternionGroup 2)) (hgen : TightSelfGen R)
    (hodd : classicalInvolutionOddCore X = ⊥) (hnc : z ∉ Subgroup.center X)
    (he : TightEdgeless R) (hA : AllTypeTwo (tightCore R) z) (T : Sylow 2 X)
    (hST : (S : Subgroup R).map R.subtype ≤ (T : Subgroup X))
    (hTt : (T : Subgroup X) ≤ Subgroup.centralizer ({z} : Set X)) :
    Nat.card (T : Subgroup X) = 16 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht := hd.setup194 he
  have hS2 : IsSylow2Of ((S : Subgroup R).map R.subtype) (tightCore R) := hd.sylow_core
  obtain ⟨Q₀, hQ₀⟩ := hS2.exists_sylow
  set R0 : Subgroup X := (Q₀ : Subgroup (tightCore R)).map (tightCore R).subtype with hR0
  have hR : R0 ∈ RSet (CoreAssembly.conjClass (tightCore R)) :=
    ⟨tightCore R, CoreAssembly.mem_conjClass_self _, Q₀, rfl⟩
  have hRK : R0 ≤ tightCore R := Subgroup.map_subtype_le _
  have hzR : IsUniqueInvolution R0 z := ht.isUniqueInvolution_of_mem_rSet_of_le hR hRK
  have hRT : R0 ≤ (T : Subgroup X) := by
    rw [hQ₀]
    exact hST
  have hSN : (T : Subgroup X) ≤ Subgroup.normalizer (R0 : Set X) := by
    intro s hs
    have hle : conjSubgroup s R0 ≤ (T : Subgroup X) := by
      intro x hx
      have hx' := mem_conjSubgroup_iff.mp hx
      have e : x = s * (s⁻¹ * x * s) * s⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hs (hRT hx')) (Subgroup.inv_mem _ hs)
    exact conjSubgroup_eq_self_iff.mp (ht.sylow_eq Q₀ T.isPGroup' hRT hle)
  have hSKR : (T : Subgroup X) ⊓ tightCore R ≤ R0 := by
    have h2 : IsPGroup 2 (((T : Subgroup X) ⊓ tightCore R).subgroupOf (tightCore R)) :=
      (T.isPGroup'.to_le inf_le_left).comap_subtype
    have hle : (Q₀ : Subgroup (tightCore R)) ≤
        ((T : Subgroup X) ⊓ tightCore R).subgroupOf (tightCore R) := by
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr ⟨hRT ⟨x, hx, rfl⟩, x.2⟩
    have heq := Q₀.3 h2 hle
    intro x hx
    have hxK : x ∈ tightCore R := hx.2
    have : (⟨x, hxK⟩ : tightCore R) ∈ ((T : Subgroup X) ⊓ tightCore R).subgroupOf (tightCore R) :=
      Subgroup.mem_subgroupOf.mpr hx
    rw [heq] at this
    exact ⟨⟨x, hxK⟩, this, rfl⟩
  obtain ⟨g, htS, htz⟩ : ∃ g : X, g * z * g⁻¹ ∈ (T : Subgroup X) ∧ g * z * g⁻¹ ≠ z := by
    have hzT : z ∈ (T : Subgroup X) := hST hd.mem
    have hzZ : (⟨z, hzT⟩ : (T : Subgroup X)) ∈ Subgroup.center (T : Subgroup X) := by
      rw [Subgroup.mem_center_iff]
      intro s
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp (hTt s.2)
    exact CFSG.ClassicalInvolution.exists_conj_mem_sylow_ne hodd T ⟨z, hzT⟩ hzZ
      (by rw [Subgroup.orderOf_mk]; exact hd.order) hnc
  set t' := g * z * g⁻¹ with ht'def
  set P := R0 ⊔ Subgroup.zpowers t' with hPdef
  have hPS : P ≤ (T : Subgroup X) := sup_le hRT (Subgroup.zpowers_le.mpr htS)
  have htzc : t' * z = z * t' := Subgroup.mem_centralizer_singleton_iff.mp (hTt htS)
  have hsd := SD.isSemidihedral_sup_of_allTypeTwo ht hA hR hRK (hSN htS) htzc htz
  obtain ⟨a, b, M, hsdd⟩ := exists_sdData (T.isPGroup'.to_le hPS) hsd
  have hcl : fusionStronglyClosed (P : Set X) T := by
    intro x hx y hy
    have := SD.mem_sup_of_conj_mem ht hA hR hRK hRT hSKR hSN hTt htS htz hx (y := y⁻¹)
      (by rwa [inv_inv])
    rwa [inv_inv] at this
  have hNC : ∀ n ∈ Subgroup.normalizer (P : Set X), ∃ k : ℕ,
      n ^ (2 ^ k) ∈ Subgroup.centralizer (P : Set X) := by
    intro n hn
    obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos n).ne'
    refine ⟨k, hsdd.mem_centralizer_of_odd (Subgroup.pow_mem _ hn _) ?_⟩
    rw [orderOf_pow' n (pow_ne_zero _ two_ne_zero), hkm,
      Nat.gcd_mul_right_left, Nat.mul_div_cancel_left _ (by positivity)]
    exact hm
  have hB := hB3 X T P hPS hcl hNC
  have hN : Subgroup.normalClosure (P : Set X) = ⊤ := by
    refine TA3.TightDatum.eq_top_of_normal_le hd hgen Subgroup.normalClosure_normal ?_
    rw [← hQ₀]
    exact le_sup_left.trans Subgroup.le_normalClosure
  have hTP : (T : Subgroup X) = P := hB.2.2 _ (hN ▸ le_top) T.isPGroup' hPS
  have ht2 : t' * t' = 1 := by
    calc t' * t' = g * (z * z) * g⁻¹ := by rw [ht'def]; group
      _ = 1 := by rw [hzR.sq]; group
  have hR8 : Nat.card R0 = 8 := by
    obtain ⟨e⟩ := hq
    rw [hQ₀, Subgroup.card_map_of_injective R.subtype_injective, Nat.card_congr e.toEquiv,
      Nat.card_eq_fintype_card, QuaternionGroup.card]
  have ht'2 : Nat.card (Subgroup.zpowers t') = 2 := by
    rw [Nat.card_zpowers]
    have := (MulAut.conj g).orderOf_eq z
    rwa [MulAut.conj_apply, hd.order] at this
  have hdisj : Disjoint R0 (Subgroup.zpowers t') := by
    rw [Subgroup.disjoint_def]
    intro x hxR hxt
    rcases eq_one_or_eq_of_mem_zpowers_of_mul_self ht2 hxt with h | h
    · exact h
    · subst h
      exact ((hzR.unique _ hxR ht2).resolve_right htz)
  rw [hTP, hPdef, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer R0 _
    (Subgroup.zpowers_le.mpr (hSN htS)) hdisj, hR8, ht'2]

theorem not_thirtyTwo_dvd_card (hB3 : GoldschmidtB3Tmp) (hm : TL4.EdgelessMember3 R S z)
    (hmu : TL4.MuZ2Member R) (hnc : z ∉ Subgroup.center X) : ¬ 32 ∣ Nat.card X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hST, hTt⟩ := exists_sylow_le_centralizer hm.datum hm.edgeless
  have h16 := card_sylow_eq_sixteen hB3 hm.datum hm.cls.1 hm.cls.2.1 hm.cls.2.2 hnc
    hm.edgeless (allTypeTwo_of_muZ2Member hm.datum hm.edgeless hmu) T hST hTt
  rw [T.card_eq_multiplicity] at h16
  have hv : (Nat.card X).factorization 2 = 4 :=
    Nat.pow_right_injective le_rfl (h16.trans (by norm_num : (16 : ℕ) = 2 ^ 4))
  intro h32
  have h5 := (Nat.Prime.pow_dvd_iff_le_factorization (k := 5) Nat.prime_two
    Nat.card_pos.ne').mp (by norm_num; exact h32)
  omega

end CFSG.ClassicalInvolution.Q3.TL4.MFMuZ2
