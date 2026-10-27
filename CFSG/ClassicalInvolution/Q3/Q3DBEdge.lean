module

public import CFSG.ClassicalInvolution.Q3.Q3DBSetup
public import CFSG.ClassicalInvolution.Q3.Generation
public import CFSG.ClassicalInvolution.Q3.Q3T6CoreFld
public import CFSG.ClassicalInvolution.Uniform.UOmega4
public import CFSG.ClassicalInvolution.Uniform.UFacade

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3DB

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem mem_of_isSylow2In_of_isUniqueInvolution {M P : Subgroup G} {y : G}
    (hy : IsUniqueInvolution M y) (hP : IsSylow2In P M) : y ∈ P := by
  have hc : ∀ m ∈ M, m * y = y * m := by
    intro m hm
    have hmy : m * y * m⁻¹ ∈ M := M.mul_mem (M.mul_mem hm hy.mem) (M.inv_mem hm)
    have hsq : (m * y * m⁻¹) * (m * y * m⁻¹) = 1 := by
      calc (m * y * m⁻¹) * (m * y * m⁻¹) = m * (y * y) * m⁻¹ := by group
        _ = 1 := by rw [hy.sq]; group
    rcases hy.unique _ hmy hsq with h1 | h1
    · exfalso
      apply hy.ne_one
      have : y = m⁻¹ * (m * y * m⁻¹) * m := by group
      rw [this, h1]
      group
    · calc m * y = (m * y * m⁻¹) * m := by group
        _ = y * m := by rw [h1]
  have h2 : IsPGroup 2 (Subgroup.zpowers y) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hy.sq) hy.ne_one]
    norm_num
  have hyc : y ∈ Subgroup.centralizer (P : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun h hh => hc h (hP.1 hh)
  have hnorm : Subgroup.zpowers y ≤ Subgroup.normalizer (P : Set G) :=
    (Subgroup.zpowers_le.mpr hyc).trans (Subgroup.centralizer_le_normalizer _)
  have hsup : IsPGroup 2 ↥(Subgroup.zpowers y ⊔ P) := h2.to_sup_of_normal_right' hP.2.1 hnorm
  have hle : Subgroup.zpowers y ⊔ P ≤ M := sup_le (Subgroup.zpowers_le.mpr hy.mem) hP.1
  have heq := hP.2.2 (Subgroup.zpowers y ⊔ P) hle hsup le_sup_right
  exact heq ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers y)

section Edge

variable {K : Subgroup G} {z : G}

theorem exists_involution_of_mem_class (hK : IsClassicalMember3 K z)
    {L : Subgroup G} (hL : L ∈ CoreAssembly.conjClass K) :
    ∃ w : G, IsClassicalMember3 L w := by
  obtain ⟨g, rfl⟩ := hL
  exact ⟨g * z * g⁻¹, hK.conj g⟩

theorem conjInvariant_class (K : Subgroup G) : ConjInvariant (CoreAssembly.conjClass K) := by
  rintro n _ ⟨g, rfl⟩
  exact ⟨n * g, conjSub_mul n g K⟩

theorem exists_sylow_of_mem_omegaNbr (hK : IsClassicalMember3 K z)
    {M N : Subgroup G} (hN : N ∈ omegaNbr (CoreAssembly.conjClass K) M) :
    ∃ R : Subgroup G, IsSylow2In R N ∧ Nat.card R = 8 ∧ R ≤ Subgroup.normalizer (M : Set G) := by
  obtain ⟨hNΩ, -, R, hR, hRN, hRM⟩ := hN
  obtain ⟨J, hJΩ, hRJ, hR2, hRmax⟩ := mem_RSet_iff.mp hR
  obtain ⟨wJ, hwJ⟩ := exists_involution_of_mem_class hK hJΩ
  obtain ⟨wN, hwN⟩ := exists_involution_of_mem_class hK hNΩ
  obtain ⟨eJ⟩ := hwJ.nonempty_equiv
  obtain ⟨eN⟩ := hwN.nonempty_equiv
  have hR8 : Nat.card R = 8 := Q3T6.natCard_sylow_eq_eight eJ ⟨hRJ, hR2, hRmax⟩
  obtain ⟨V, hV, hRV⟩ := IsSylow2In.exists_ge hR2 hRN
  have hV8 : Nat.card V = 8 := Q3T6.natCard_sylow_eq_eight eN hV
  exact ⟨R, hV.of_natCard_le hR2 hRN (le_of_eq (hV8.trans hR8.symm)), hR8, hRM⟩

theorem fuzzy_of_mem_omegaNbr (hK : IsClassicalMember3 K z)
    (hint : IsIntrinsicU (.sl2 3 1) K z) {M N : Subgroup G}
    (hN : N ∈ omegaNbr (CoreAssembly.conjClass K) M) {a : G} (ha : IsClassicalMember3 M a) :
    conjSub a N = N ∧ ∀ x ∈ N, ⁅a, x⁆ ∈ oddCoreOf N := by
  have hNΩ : N ∈ CoreAssembly.conjClass K := hN.1
  obtain ⟨R, hRsyl, hR8, hRM⟩ := exists_sylow_of_mem_omegaNbr hK hN
  have hUM : IsUniqueInvolution M a :=
    (IsClassicalMemberU.ofQ3 ha).isUniqueInvolution (MemberType.cert_sl2 3 1)
  have haR : ∀ r ∈ R, a * r = r * a := by
    intro r hr
    have h1 := hUM.conj_eq (n := r) (mem_normalizer_iff_conjSub_eq.mp (hRM hr))
    calc a * r = (r * a * r⁻¹) * r := by rw [h1]
      _ = r * a := by group
  have hconj : conjSub a N = N := by
    by_contra hne
    have hNa : conjSub a N ∈ CoreAssembly.conjClass K := conjInvariant_class K a N hNΩ
    obtain ⟨h1, -⟩ := omega4_of_memberU (MemberType.cert_sl2 3 1) (IsClassicalMemberU.ofQ3 hK)
      hint hNΩ hNa (Ne.symm hne)
    have hRle : R ≤ N ⊓ conjSub a N := by
      intro r hr
      refine Subgroup.mem_inf.mpr ⟨hRsyl.1 hr, ?_⟩
      rw [mem_conjSub_iff]
      have : a⁻¹ * r * a = r := by
        rw [mul_assoc, ← haR r hr]
        group
      rw [this]
      exact hRsyl.1 hr
    have h8 : 2 ^ 3 ∣ Nat.card ↥(N ⊓ conjSub a N) := by
      have := Subgroup.card_dvd_of_le hRle
      rwa [hR8] at this
    have h3 : 3 ≤ padicValNat 2 (Nat.card ↥(N ⊓ conjSub a N)) :=
      (padicValNat_dvd_iff_le Nat.card_pos.ne').mp h8
    omega
  refine ⟨hconj, ?_⟩
  have haN : ∀ y ∈ Subgroup.zpowers a, conjSub y N = N := by
    intro y hy
    have ha' : a ∈ Subgroup.normalizer (N : Set G) := mem_normalizer_iff_conjSub_eq.mpr hconj
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact mem_normalizer_iff_conjSub_eq.mp (Subgroup.zpow_mem _ ha' k)
  have hV2 : IsPGroup 2 ↥(Subgroup.zpowers a) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, ha.orderOf_eq_two]
    norm_num
  have hcomm : ∀ r ∈ R, ∀ v ∈ Subgroup.zpowers a, r * v = v * r := by
    intro r hr v hv
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact ((Commute.zpow_right (show Commute r a from (haR r hr).symm) k)).eq
  have hex : ∀ L ∈ CoreAssembly.conjClass K,
      Nonempty (L ⧸ classicalInvolutionOddCore L ≃* SL(2, ZMod 3)) := fun L hL => by
    obtain ⟨w, hw⟩ := exists_involution_of_mem_class hK hL
    exact hw.nonempty_equiv
  have key := Q3T6.centSylow_three hex hNΩ hRsyl hV2 haN hcomm
  intro x hx
  exact key x hx a (Subgroup.mem_zpowers a)

theorem centralizes_of_mem_omegaNbr (hK : IsClassicalMember3 K z)
    (hW : Balance.oddCoreIn (Subgroup.centralizer ({z} : Set G)) = ⊥)
    {M N : Subgroup G} (hN : N ∈ omegaNbr (CoreAssembly.conjClass K) M) {a : G}
    (ha : IsClassicalMember3 M a) : ∀ x ∈ N, a * x = x * a := by
  have hint : IsIntrinsicU (.sl2 3 1) K z := fun _ => by rw [hW]; exact bot_le
  obtain ⟨-, hfz⟩ := fuzzy_of_mem_omegaNbr hK hint hN ha
  obtain ⟨wN, hwN⟩ := exists_involution_of_mem_class hK hN.1
  obtain ⟨g, hg⟩ := id hN.1
  have hWN : Balance.oddCoreIn (Subgroup.centralizer ({wN} : Set G)) = ⊥ := by
    have hwg : wN = g * z * g⁻¹ := involution_unique3 hwN (hg ▸ hK.conj g)
    rw [hwg]
    exact oddCoreIn_centralizer_conj g hW
  have h2 : oddCoreOf N = ⊥ :=
    le_bot_iff.mp ((Balance.oddCoreIn_le_of_isSubnormal hwN.subnormal).trans hWN.le)
  intro x hx
  have h1 := hfz x hx
  rw [h2, Subgroup.mem_bot] at h1
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

end Edge

end CFSG.ClassicalInvolution.Q3.Q3DB
