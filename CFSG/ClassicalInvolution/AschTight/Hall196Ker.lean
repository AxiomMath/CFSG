module

public import CFSG.ClassicalInvolution.AschTight.Hall196QD
public import CFSG.ClassicalInvolution.AschTight.Hall196XG

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Hall196

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}
  {S : Sylow 2 G} {W : Subgroup G}

theorem eq_one_or_eq_of_mem_inter (hd : Sec19Data p f K z S W)
    (hQ : IsQuaternionSub ((S : Subgroup G) ⊓ sec19Y K z)) {b : G} (hbK : b ∈ K)
    (hbY : b ∈ sec19Y K z) (hb2 : IsPGroup 2 (Subgroup.zpowers b)) : b = 1 ∨ b = z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hI := isUniqueInvolution_of_tight hd.tight.toTightBranch
  have hNC := normalizer_eq_centralizer_of_tight hd.tight.toTightBranch
  have hR := isSylow2In_inf_of_le_normalizer S (hd.hSz.trans hNC.ge)
  obtain ⟨R₁, hR₁, hbR₁⟩ := IsSylow2In.exists_ge hb2 (Subgroup.zpowers_le.mpr hbK)
  obtain ⟨k, hk, hkR⟩ := exists_conjSub_eq_of_isSylow2In hR hR₁
  have hb' : b ∈ conjSub k ((S : Subgroup G) ⊓ K) := hkR ▸ hbR₁ (Subgroup.mem_zpowers b)
  rw [mem_conjSub_iff] at hb'
  have hkz : k⁻¹ ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.inv_mem _ (Subgroup.mem_centralizer_singleton_iff.mpr (hI.commute_of_mem hk).symm)
  have hkY : k⁻¹ * b * k ∈ sec19Y K z := by
    have h1 := conj_mem_conjSub (n := k⁻¹) hbY
    rwa [inv_inv, conjSub_sec19Y hd.tight hkz] at h1
  rcases eq_one_or_eq_of_mem_inf hd hQ hb' hkY with h | h
  · left
    calc b = k * (k⁻¹ * b * k) * k⁻¹ := by group
      _ = 1 := by rw [h]; group
  · right
    calc b = k * (k⁻¹ * b * k) * k⁻¹ := by group
      _ = k * z * k⁻¹ := by rw [h]
      _ = z := by rw [← hI.commute_of_mem hk]; group

theorem ker_sec19Y_quot [IsSimpleGroup G] (hd : Sec19Data p f K z S W)
    (hQ : IsQuaternionSub ((S : Subgroup G) ⊓ sec19Y K z)) [(K.subgroupOf (sec19X K z)).Normal]
    (y : ↥(sec19Y K z)) :
    QuotientGroup.mk' (pPrimeCore 2 (↥(sec19X K z) ⧸ K.subgroupOf (sec19X K z)))
        (QuotientGroup.mk' (K.subgroupOf (sec19X K z))
          (Subgroup.inclusion (sec19Y_le_sec19X K z) y)) = 1 ↔
      (y : G) ∈ oddCoreOf (sec19Y K z) ⊔ Subgroup.zpowers z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hI := isUniqueInvolution_of_tight hd.tight.toTightBranch
  have hYX : sec19Y K z ≤ sec19X K z := sec19Y_le_sec19X K z
  have hzY : z ∈ sec19Y K z := S1916.sd_mem_Y hd
  set Q := ↥(sec19X K z) ⧸ K.subgroupOf (sec19X K z) with hQdef
  set π := QuotientGroup.mk' (K.subgroupOf (sec19X K z)) with hπ
  have : (pPrimeCore 2 Q).Normal := pPrimeCore_normal
  set ρ₀ : ↥(sec19Y K z) →* Q ⧸ pPrimeCore 2 Q :=
    (QuotientGroup.mk' (pPrimeCore 2 Q)).comp (π.comp (Subgroup.inclusion hYX)) with hρ₀
  have hρ₀y : ∀ y : ↥(sec19Y K z), ρ₀ y = QuotientGroup.mk' (pPrimeCore 2 Q)
      (π (Subgroup.inclusion hYX y)) := fun _ => rfl
  rw [← hρ₀y]
  have hOker : ∀ x : ↥(sec19Y K z), (x : G) ∈ oddCoreOf (sec19Y K z) → ρ₀ x = 1 := by
    intro x hx
    have hXN : sec19X K z ≤ Subgroup.normalizer (oddCoreOf (sec19Y K z) : Set G) := fun g hg =>
      AschTight.mem_normalizer_oddCoreOf_of_mem_normalizer
        (centralizer_le_normalizer_sec19Y hd.tight (gammaGen_le_centralizer _ z hg))
    have hOX : oddCoreOf (sec19Y K z) ≤ sec19X K z := (oddCoreOf_le_self _).trans hYX
    have hO1 : ((oddCoreOf (sec19Y K z)).subgroupOf (sec19X K z)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hOX).mpr hXN
    have hO2 : (((oddCoreOf (sec19Y K z)).subgroupOf (sec19X K z)).map π).Normal :=
      Subgroup.Normal.map hO1 π (QuotientGroup.mk'_surjective _)
    have hO3 : Nat.Coprime 2 (Nat.card ↥(((oddCoreOf (sec19Y K z)).subgroupOf
        (sec19X K z)).map π)) := by
      refine Nat.coprime_two_left.mpr (Odd.of_dvd_nat ?_ (Subgroup.card_map_dvd _ _))
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOX).toEquiv]
      exact oddCoreOf_odd_natCard _
    have hle : ((oddCoreOf (sec19Y K z)).subgroupOf (sec19X K z)).map π ≤ pPrimeCore 2 Q :=
      le_sSup ⟨hO2, hO3⟩
    rw [hρ₀y, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hle ⟨Subgroup.inclusion hYX x, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have hzker : ρ₀ ⟨z, hzY⟩ = 1 := by
    have h1 : π (Subgroup.inclusion hYX ⟨z, hzY⟩) = 1 := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hI.mem
    rw [hρ₀y, h1, map_one]
  constructor
  · intro hy
    have hB2 : ∀ b : ↥(sec19Y K z), ρ₀ b = 1 → IsPGroup 2 (Subgroup.zpowers (b : G)) →
        (b : G) = 1 ∨ (b : G) = z := by
      intro b hb hb2
      have hx : π (Subgroup.inclusion hYX b) ∈ pPrimeCore 2 Q := by
        rw [hρ₀y, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hb
        exact hb
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hb2) ⟨b, Subgroup.mem_zpowers _⟩
      have hko : orderOf (Subgroup.inclusion hYX b) = 2 ^ k := by
        rw [← Subgroup.orderOf_coe, Subgroup.coe_inclusion, ← hk, Subgroup.orderOf_mk]
      have h1 : orderOf (π (Subgroup.inclusion hYX b)) ∣ 2 ^ k :=
        hko ▸ orderOf_map_dvd π _
      have h2 := Subgroup.orderOf_dvd_natCard _ hx
      have h3 : Nat.Coprime (2 ^ k) (Nat.card ↥(pPrimeCore 2 Q)) :=
        Nat.Coprime.pow_left k pPrimeCore_coprime_card
      have h4 := (Nat.Coprime.coprime_dvd_left h1 h3).eq_one_of_dvd h2
      rw [orderOf_eq_one_iff, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        Subgroup.mem_subgroupOf, Subgroup.coe_inclusion] at h4
      exact eq_one_or_eq_of_mem_inter hd hQ h4 b.2 hb2
    set B : Subgroup G := ρ₀.ker.map (sec19Y K z).subtype with hB
    have hBY : B ≤ sec19Y K z := Subgroup.map_subtype_le _
    have hYB : sec19Y K z ≤ Subgroup.normalizer (B : Set G) := by
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer hBY).mp ?_
      rw [show B.subgroupOf (sec19Y K z) = ρ₀.ker from
        Subgroup.comap_map_eq_self_of_injective (sec19Y K z).subtype_injective _]
      exact ρ₀.normal_ker
    have hbot : IsPGroup 2 ↥(⊥ : Subgroup G) :=
      IsPGroup.of_card (n := 0) (by rw [Subgroup.card_bot, pow_zero])
    obtain ⟨PB, hPB, -⟩ := IsSylow2In.exists_ge hbot (bot_le : ⊥ ≤ B)
    have hPBz : PB ≤ Subgroup.zpowers z := by
      intro x hx
      obtain ⟨b, hb, rfl⟩ := hPB.1 hx
      have hb2 : IsPGroup 2 (Subgroup.zpowers ((sec19Y K z).subtype b)) :=
        hPB.2.1.to_le (Subgroup.zpowers_le.mpr hx)
      rcases hB2 b hb hb2 with h | h
      · rw [show (sec19Y K z).subtype b = (b : G) from rfl, h]
        exact Subgroup.one_mem _
      · rw [show (sec19Y K z).subtype b = (b : G) from rfl, h]
        exact Subgroup.mem_zpowers z
    have hPBc : IsCyclic PB := Subgroup.isCyclic_of_le hPBz
    have hsup := sup_eq_oddCoreOf_sup_of_isCyclic hPB hPBc hPBz
    have hOB := oddCoreOf_le_of_le_normalizer hBY hYB
    have hyB : (y : G) ∈ Subgroup.zpowers z ⊔ B := Subgroup.mem_sup_right ⟨y, hy, rfl⟩
    rw [hsup] at hyB
    exact (sup_le_sup_right hOB _) hyB
  · intro hy
    have hle : (oddCoreOf (sec19Y K z) ⊔ Subgroup.zpowers z).subgroupOf (sec19Y K z) ≤
        ρ₀.ker := by
      rw [Subgroup.subgroupOf_sup (oddCoreOf_le_self _) (Subgroup.zpowers_le.mpr hzY)]
      refine sup_le (fun x hx => hOker x (Subgroup.mem_subgroupOf.mp hx)) ?_
      intro x hx
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hx)
      have hx' : x = (⟨z, hzY⟩ : ↥(sec19Y K z)) ^ i :=
        Subtype.ext (by rw [Subgroup.coe_zpow, Subgroup.coe_mk]; exact hi.symm)
      rw [MonoidHom.mem_ker, hx', map_zpow, hzker, one_zpow]
    exact hle (Subgroup.mem_subgroupOf.mpr hy)

end CFSG.ClassicalInvolution.Disconnected.AschTight.Hall196
