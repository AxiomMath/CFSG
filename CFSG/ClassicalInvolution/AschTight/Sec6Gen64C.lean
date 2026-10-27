module

public import CFSG.GroupTheory.CyclicSylowNormalOddComplement
public import CFSG.ClassicalInvolution.AschTight.Sec6GenAPI

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem exists_mem_centralizer_of_odd {V : Subgroup G} (hV : IsPGroup 2 ↥V) {C : Set G}
    (hC : ∀ v ∈ V, ∀ c ∈ C, v * c * v⁻¹ ∈ C) (hodd : Odd (Nat.card C)) :
    ∃ c ∈ C, ∀ v ∈ V, v * c * v⁻¹ = c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulAction ↥V ↥C :=
    { smul := fun v c => ⟨(v : G) * c * (v : G)⁻¹, hC v v.2 c c.2⟩
      one_smul := fun c => Subtype.ext (by
        show ((1 : ↥V) : G) * c * ((1 : ↥V) : G)⁻¹ = c
        simp)
      mul_smul := fun v w c => Subtype.ext (by
        show ((v * w : ↥V) : G) * c * ((v * w : ↥V) : G)⁻¹ =
          (v : G) * ((w : G) * c * (w : G)⁻¹) * (v : G)⁻¹
        simp only [Subgroup.coe_mul]
        group) }
  have hnd : ¬ 2 ∣ Nat.card ↥C := fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
  obtain ⟨c, hc⟩ := hV.nonempty_fixed_point_of_prime_not_dvd_card ↥C hnd
  refine ⟨c, c.2, fun v hv => ?_⟩
  have h1 : (⟨v, hv⟩ : ↥V) • c = c := hc ⟨v, hv⟩
  exact congrArg Subtype.val h1

theorem exists_odd_complement {H U : Subgroup G} (hU : IsSylow2In U H) (hUc : IsCyclic ↥U) :
    ∃ N₀ : Subgroup G, N₀ ≤ H ∧ Odd (Nat.card N₀) ∧
      (∀ h ∈ H, ∃ n ∈ N₀, ∃ u ∈ U, h = n * u) ∧
      ∀ x ∈ H, Odd (orderOf x) → x ∈ N₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S : Sylow 2 ↥H := AscL62.sylowOfIsSylow2In'' hU with hS
  have hSU : ∀ b : ↥H, b ∈ (S : Subgroup ↥H) ↔ (b : G) ∈ U := fun b => Iff.rfl
  have hScyc : IsCyclic ↥(S : Subgroup ↥H) :=
    (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hU.1)).mpr hUc
  obtain ⟨-, hmul, hinf, ⟨hNn, hNodd, -, -⟩, -⟩ := CFSG.cyclic_sylow_normal_odd_complement S hScyc
  set N : Subgroup ↥H := pPrimeCore 2 ↥H with hN
  refine ⟨N.map H.subtype, Subgroup.map_subtype_le N, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact hNodd
  · intro h hh
    have hmem : (⟨h, hh⟩ : ↥H) ∈ (N : Set ↥H) * (S : Set ↥H) := by rw [hmul]; trivial
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hmem
    refine ⟨a, ⟨a, ha, rfl⟩, b, (hSU b).mp hb, ?_⟩
    have := congrArg Subtype.val hab
    simpa using this.symm
  · intro x hx hodd
    have hmem : (⟨x, hx⟩ : ↥H) ∈ (N : Set ↥H) * (S : Set ↥H) := by rw [hmul]; trivial
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hmem
    have hNn' : N.Normal := hNn
    have hb1 : b = 1 := by
      have hmk : (QuotientGroup.mk' N) (⟨x, hx⟩ : ↥H) = (QuotientGroup.mk' N) b := by
        rw [← hab, map_mul,
          show (QuotientGroup.mk' N) a = 1 from (QuotientGroup.eq_one_iff a).mpr ha, one_mul]
      have h1 : orderOf ((QuotientGroup.mk' N) b) ∣ orderOf (⟨x, hx⟩ : ↥H) := by
        rw [← hmk]
        exact orderOf_map_dvd _ _
      rw [Subgroup.orderOf_mk] at h1
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp S.isPGroup') ⟨b, hb⟩
      have h2 : orderOf ((QuotientGroup.mk' N) b) ∣ 2 ^ k := by
        rw [← hk, Subgroup.orderOf_mk]
        exact orderOf_map_dvd _ _
      have hcop : Nat.Coprime (2 ^ k) (orderOf x) :=
        Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
      have h3 := Nat.eq_one_of_dvd_coprimes hcop h2 h1
      have h4 : (QuotientGroup.mk' N) b = 1 := orderOf_eq_one_iff.mp h3
      have hbN : b ∈ N := (QuotientGroup.eq_one_iff b).mp h4
      have hbinf : b ∈ N ⊓ (S : Subgroup ↥H) := ⟨hbN, hb⟩
      rw [hinf] at hbinf
      exact Subgroup.mem_bot.mp hbinf
    rw [hb1, mul_one] at hab
    exact ⟨a, ha, by rw [hab]; rfl⟩

theorem inf_centralizer_le_normalizer (hΩ : HypOmegaGen Ω) {K J : Subgroup G} (hK : K ∈ Ω)
    (hJ : J ∈ Ω) (hKJ : K ≠ J) {j : G} (hj : IsUniqueInvolution J j) {U V : Subgroup G}
    (hU : IsSylow2In U (K ⊓ Subgroup.centralizer ({j} : Set G))) (hUc : IsCyclic ↥U)
    (hU4 : 4 ≤ Nat.card U) (hVJ : V ≤ J) (hV2 : IsPGroup 2 ↥V) (hV4 : 4 ≤ Nat.card V)
    (hVK : V ≤ Subgroup.normalizer (K : Set G)) (hVj : V ≤ Subgroup.centralizer ({j} : Set G)) :
    K ⊓ Subgroup.centralizer ({j} : Set G) ≤ Subgroup.normalizer (J : Set G) := by
  set H := K ⊓ Subgroup.centralizer ({j} : Set G) with hH
  obtain ⟨N₀, hN₀H, hN₀odd, hdec, hoddmem⟩ := exists_odd_complement hU hUc
  have hconjj : ∀ h ∈ H, IsUniqueInvolution (conjSub h J) j := by
    intro h hh
    have h1 := hj.conj h
    have e : h * j * h⁻¹ = j := by
      have h2 : h * j = j * h := Subgroup.mem_centralizer_singleton_iff.mp hh.2
      calc h * j * h⁻¹ = j * h * h⁻¹ := by rw [h2]
        _ = j := by group
    rwa [e] at h1
  have hU2 : IsPGroup 2 ↥U := hU.2.1
  have hUK : U ≤ K := hU.1.trans inf_le_left
  have hUj : U ≤ Subgroup.centralizer ({j} : Set G) := hU.1.trans inf_le_right
  have hUN : U ≤ Subgroup.normalizer (J : Set G) :=
    le_normalizer_of_le_centralizer hΩ hJ hK hKJ.symm hj hUK hU2 (by omega) hUj
  have hVconj : ∀ h ∈ H, V ≤ Subgroup.normalizer ((conjSub h J : Subgroup G) : Set G) := by
    intro h hh
    by_cases he : conjSub h J = J
    · rw [he]
      exact hVJ.trans Subgroup.le_normalizer
    · exact le_normalizer_of_le_centralizer hΩ (hΩ.conjInvariant h J hJ) hJ he (hconjj h hh) hVJ
        hV2 (by omega) hVj
  have hVN₀ : ∀ v ∈ V, ∀ n ∈ N₀, v * n * v⁻¹ ∈ N₀ := by
    intro v hv n hn
    have hnH := hN₀H hn
    have hmemH : v * n * v⁻¹ ∈ H :=
      ⟨(Subgroup.mem_normalizer_iff.mp (hVK hv) n).mp hnH.1,
        (Subgroup.centralizer _).mul_mem ((Subgroup.centralizer _).mul_mem (hVj hv) hnH.2)
          ((Subgroup.centralizer _).inv_mem (hVj hv))⟩
    have hodd : Odd (orderOf (v * n * v⁻¹)) := by
      have e : orderOf (v * n * v⁻¹) = orderOf n := by
        simpa [MulAut.conj_apply] using (MulAut.conj v).orderOf_eq n
      rw [e]
      exact hN₀odd.of_dvd_nat (Subgroup.orderOf_dvd_natCard N₀ hn)
    exact hoddmem _ hmemH hodd
  have hN₀N : ∀ w ∈ N₀, w ∈ Subgroup.normalizer (J : Set G) := by
    intro w hw
    set N₁ : Subgroup G := N₀ ⊓ Subgroup.normalizer (J : Set G) with hN₁
    set C : Set G := {c | w⁻¹ * c ∈ N₁} with hC
    have hwconj : ∀ v ∈ V, w⁻¹ * v * w ∈ Subgroup.normalizer (J : Set G) := by
      intro v hv
      have := hVconj w (hN₀H hw) hv
      rwa [mem_normalizer_conjSub_iff] at this
    have hVJN : ∀ v ∈ V, v ∈ Subgroup.normalizer (J : Set G) := fun v hv =>
      Subgroup.le_normalizer (hVJ hv)
    have hCstable : ∀ v ∈ V, ∀ c ∈ C, v * c * v⁻¹ ∈ C := by
      intro v hv c hc
      have e : w⁻¹ * (v * c * v⁻¹) = (w⁻¹ * (v * w * v⁻¹)) * (v * (w⁻¹ * c) * v⁻¹) := by group
      show w⁻¹ * (v * c * v⁻¹) ∈ N₁
      rw [e]
      refine N₁.mul_mem ⟨N₀.mul_mem (N₀.inv_mem hw) (hVN₀ v hv w hw), ?_⟩
        ⟨hVN₀ v hv _ hc.1, ?_⟩
      · have e2 : w⁻¹ * (v * w * v⁻¹) = (w⁻¹ * v * w) * v⁻¹ := by group
        rw [e2]
        exact (Subgroup.normalizer _).mul_mem (hwconj v hv)
          ((Subgroup.normalizer _).inv_mem (hVJN v hv))
      · exact (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).mul_mem (hVJN v hv) hc.2)
          ((Subgroup.normalizer _).inv_mem (hVJN v hv))
    have hCcard : Nat.card C = Nat.card N₁ := by
      refine Nat.card_congr ⟨fun c => ⟨w⁻¹ * c, c.2⟩, fun n => ⟨w * n, ?_⟩, ?_, ?_⟩
      · show w⁻¹ * (w * n) ∈ N₁
        simp
      · intro c
        apply Subtype.ext
        show w * (w⁻¹ * c) = c
        group
      · intro n
        apply Subtype.ext
        show w⁻¹ * (w * n) = n
        group
    have hCodd : Odd (Nat.card C) := by
      rw [hCcard]
      exact hN₀odd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
    obtain ⟨c, hcC, hcfix⟩ := exists_mem_centralizer_of_odd hV2 hCstable hCodd
    have hVc : V ≤ conjSub c J := by
      intro v hv
      have h1 := hcfix v hv
      rw [mem_conjSub_iff]
      have hvc : v * c = c * v := by
        calc v * c = v * c * v⁻¹ * v := by group
          _ = c * v := by rw [h1]
      have e : c⁻¹ * v * c = v := by
        calc c⁻¹ * v * c = c⁻¹ * (v * c) := by group
          _ = c⁻¹ * (c * v) := by rw [hvc]
          _ = v := by group
      rw [e]
      exact hVJ hv
    have hJc : conjSub c J = J :=
      eq_of_le_of_le hΩ (hΩ.conjInvariant c J hJ) hJ hV2 hV4 hVc hVJ
    have hcN : c ∈ Subgroup.normalizer (J : Set G) := mem_normalizer_iff_conjSub_eq.mpr hJc
    have hwc : w⁻¹ * c ∈ Subgroup.normalizer (J : Set G) := hcC.2
    have hwinv : w⁻¹ ∈ Subgroup.normalizer (J : Set G) := by
      have := (Subgroup.normalizer _).mul_mem hwc ((Subgroup.normalizer _).inv_mem hcN)
      simpa using this
    simpa using (Subgroup.normalizer _).inv_mem hwinv
  intro h hh
  obtain ⟨n, hn, u, hu, rfl⟩ := hdec h hh
  exact (Subgroup.normalizer _).mul_mem (hN₀N n hn) (hUN hu)

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
