module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuCentA

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.BenderSuzuki.PFAppendixIII

theorem conj_eq_inv_of_fixedPointFree {H : Type*} [Group H] [Finite H] {D : Subgroup H}
    [D.Normal] {e : H} (he : e * e = 1) (hfix : ∀ x ∈ D, e * x = x * e → x = 1) {x : H}
    (hx : x ∈ D) : e * x * e⁻¹ = x⁻¹ := by
  have heinv : e⁻¹ = e := inv_eq_of_mul_eq_one_right he
  set φ : D →* D := (MulAut.conjNormal e : MulAut D).toMonoidHom with hφdef
  have hφ : ∀ z : D, ((φ z : D) : H) = e * z * e⁻¹ := fun z => MulAut.conjNormal_apply e z
  have hfpf : MonoidHom.FixedPointFree φ := by
    intro z hz
    apply Subtype.ext
    refine hfix z z.2 ?_
    have h1 := congrArg Subtype.val hz
    rw [hφ] at h1
    calc e * z = e * z * e⁻¹ * e := by group
      _ = z * e := by rw [h1]
  have hinv : Function.Involutive φ := by
    intro z
    apply Subtype.ext
    rw [hφ, hφ, heinv]
    calc e * (e * z * e) * e = e * e * z * (e * e) := by group
      _ = z := by rw [he]; group
  have h1 := congrArg Subtype.val (congrFun (hfpf.coe_eq_inv_of_involutive hinv) ⟨x, hx⟩)
  rw [hφ] at h1
  simpa using h1

theorem eq_bot_of_fixedPointFree_of_four {H : Type*} [Group H] [Finite H] {D : Subgroup H}
    [D.Normal] {u v : H} (hu : u * u = 1) (hv : v * v = 1)
    (hfu : ∀ x ∈ D, u * x = x * u → x = 1) (hfv : ∀ x ∈ D, v * x = x * v → x = 1)
    (hfuv : ∀ x ∈ D, (u * v) * x = x * (u * v) → x = 1) : D = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [mem_bot]
  refine hfuv x hx ?_
  have h1 := conj_eq_inv_of_fixedPointFree hu hfu hx
  have h2 := conj_eq_inv_of_fixedPointFree hv hfv hx
  calc u * v * x = u * (v * x * v⁻¹) * v := by group
    _ = u * x⁻¹ * u⁻¹ * (u * v) := by rw [h2]; group
    _ = (u * x * u⁻¹)⁻¹ * (u * v) := by group
    _ = x * (u * v) := by rw [h1, inv_inv]

namespace Sec3.SzR

variable {G : Type} [Group G] [Finite G] {L T R R₂ : Subgroup G} {y d : G}

theorem centralizer_inf_le_T
    (hS : SzR G L T R 1 y d)
    (hCe : ∀ e ∈ T ⊓ centralizer (L : Set G), e ≠ 1 →
      centralizer ({e} : Set G) = (T ⊓ centralizer (L : Set G)) ⊔ L)
    (hCL : ∀ a ∈ L, a ≠ 1 → a ^ 2 = 1 →
      IsPGroup 2 (L ⊓ centralizer ({a} : Set G) : Subgroup G))
    {e : G} (he : e ∈ T ⊓ centralizer (L : Set G)) (he1 : e ≠ 1) :
    centralizer ({e} : Set G) ⊓ centralizer (gmsA L T : Set G) ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx
  obtain ⟨hxe, hxA⟩ := mem_inf.mp hx
  rw [hCe e he he1] at hxe
  obtain ⟨t, ht, l, hl, rfl⟩ := CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer
    (inf_le_right.trans hS.sec3.centralizer_le_normalizer) hxe
  obtain ⟨hA₁card, hA2, -⟩ := hS.facts.sylow hS.sec3
  have hA₁1 : gmsA L T ≠ ⊥ := by
    intro hb
    rw [hb, card_bot] at hA₁card
    norm_num at hA₁card
  obtain ⟨⟨a, ha⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA₁1
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have haL : a ∈ L := ha.1.2
  have hla : l * a = a * l := by
    have h1 : (t * l) * a = a * (t * l) := (mem_centralizer_iff.mp hxA a ha).symm
    have h2 : t * a = a * t := (mem_centralizer_iff.mp ht.2 a haL).symm
    calc l * a = t⁻¹ * ((t * l) * a) := by group
      _ = t⁻¹ * (a * (t * l)) := by rw [h1]
      _ = t⁻¹ * (a * t) * l := by group
      _ = t⁻¹ * (t * a) * l := by rw [h2]
      _ = a * l := by group
  have hCa : L ⊓ centralizer ({a} : Set G) = T ⊓ L :=
    hS.sec3.isSylowOf_T₁.eq_of_le (fun z hz => ⟨hz.2, mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp ha.2 z hz)⟩) inf_le_left (hCL a haL ha1' (hA2 a ha))
  have hlT₁ : l ∈ T ⊓ L := by
    rw [← hCa]
    exact ⟨hl, mem_centralizer_singleton_iff.mpr hla⟩
  exact mul_mem ht.1 hlT₁.1

theorem exists_two_ne_one_of_four_le_card {H : Subgroup G} (h : 4 ≤ Nat.card H) :
    ∃ s₁ ∈ H, ∃ s₂ ∈ H, s₁ ≠ 1 ∧ s₂ ≠ 1 ∧ s₁ ≠ s₂ := by
  classical
  have : Fintype G := Fintype.ofFinite G
  set S := ((H : Set G).toFinset).erase 1 with hS
  have hc : 1 < S.card := by
    rw [show Nat.card H = Nat.card (H : Set G) from rfl, Nat.card_eq_card_toFinset] at h
    rw [hS, Finset.card_erase_of_mem (by simp)]
    omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hc
  simp only [hS, Finset.mem_erase, Set.mem_toFinset, SetLike.mem_coe] at hx hy
  exact ⟨x, hx.2, y, hy.2, hx.1, hy.1, hxy⟩

theorem eq_one_of_mem_T_of_odd (hS : SzR G L T R 1 y d) {x : G}
    (hxT : x ∈ T) (hx : Odd (orderOf x)) : x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (hS.isR.isPGroup.to_le hS.T_le) ⟨x, hxT⟩
  have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk')
  rcases j with _ | j
  · rw [pow_zero] at hj
    exact orderOf_eq_one_iff.mp hj
  · rw [hj, pow_succ] at hx
    exact absurd hx (Nat.not_odd_iff_even.mpr (even_two.mul_left _))

theorem centralizer_gmsA_eq
    (hS : SzR G L T R 1 y d) (h34 : NoStronglyClosedAbelian G)
    (hR₂ : IsR₂ L T R R₂ d) (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4)
    (hCV : centralizer (gmsV L T : Set G) = T)
    (hCe : ∀ e ∈ T ⊓ centralizer (L : Set G), e ≠ 1 →
      centralizer ({e} : Set G) = (T ⊓ centralizer (L : Set G)) ⊔ L)
    (hCL : ∀ a ∈ L, a ≠ 1 → a ^ 2 = 1 →
      IsPGroup 2 (L ⊓ centralizer ({a} : Set G) : Subgroup G)) :
    centralizer (gmsA L T : Set G) = R := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨X, hX⟩ := hS.exists_isX h34
  set C := centralizer (gmsA L T : Set G) with hCdef
  have hRC : R ≤ C := fun r hr =>
    mem_centralizer_iff.mpr fun b hb => (hS.commute_gmsA hr hb).symm
  have hAR : gmsA L T ≤ R := gmsA_le_T.trans hS.T_le
  have hNC : normalizer (R : Set G) ⊓ C = R := hS.normalizer_inf_centralizer_eq h34 hR₂ h4 hCV
  refine le_antisymm ?_ hRC
  set R' : Subgroup C := R.subgroupOf C with hR'
  set A' : Subgroup C := (gmsA L T).subgroupOf C with hA'
  have hA'R' : A' ≤ R' := fun x hx => hAR hx
  have hA'cent : ∀ a ∈ A', ∀ c : C, c * a = a * c := fun a ha c =>
    Subtype.ext (mem_centralizer_iff.mp c.2 a ha).symm
  have : A'.Normal := ⟨fun a ha c => by
    have h1 : c * a * c⁻¹ = a := by rw [hA'cent a ha c]; group
    rw [h1]
    exact ha⟩
  have hR'2 : IsPGroup 2 R' := hS.isR.isPGroup.comap_subtype
  have hR'idx : ¬ 2 ∣ R'.index := by
    intro hdvd
    have hnS : ¬ IsSylowOf 2 R' ⊤ := fun h =>
      (isSylowOf_iff.mp h).2.2 (by rwa [relIndex_top_right])
    obtain ⟨-, -, z, -, hzN, hzR⟩ := exists_mem_normalizer_of_not_isSylowOf hR'2 hnS
    apply hzR
    have hz : (z : G) ∈ normalizer (R : Set G) ⊓ C := by
      refine mem_inf.mpr ⟨mem_normalizer_of_conj_mem_of_finite fun x hx => ?_, z.2⟩
      exact (mem_normalizer_iff.mp hzN ⟨x, hRC hx⟩).mp hx
    rw [hNC] at hz
    exact hz
  set PR : Sylow 2 C := hR'2.toSylow hR'idx with hPR
  have hPRc : (PR : Subgroup C) = R' := IsPGroup.toSylow_coe hR'2 hR'idx
  set π := QuotientGroup.mk' A' with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective A'
  set S : Sylow 2 (C ⧸ A') := PR.mapSurjective hπs with hSdef
  have hSc : (S : Subgroup (C ⧸ A')) = R'.map π := by
    rw [hSdef, Sylow.coe_mapSurjective, hPRc]
  have hNS : normalizer (S : Set (C ⧸ A')) ≤ centralizer (S : Set (C ⧸ A')) := by
    intro q hq
    obtain ⟨c, rfl⟩ := hπs q
    have hcN : (c : G) ∈ normalizer (R : Set G) := by
      refine mem_normalizer_of_conj_mem_of_finite fun x hx => ?_
      have hxC := hRC hx
      have h1 : π (c * ⟨x, hxC⟩ * c⁻¹) ∈ (S : Subgroup (C ⧸ A')) := by
        rw [map_mul, map_mul, map_inv]
        refine (mem_normalizer_iff.mp hq _).mp ?_
        rw [hSc]
        exact ⟨⟨x, hxC⟩, hx, rfl⟩
      rw [hSc] at h1
      obtain ⟨r, hr, hrπ⟩ := h1
      have h2 : r⁻¹ * (c * ⟨x, hxC⟩ * c⁻¹) ∈ A' := QuotientGroup.eq.mp hrπ
      have h3 : c * ⟨x, hxC⟩ * c⁻¹ ∈ R' := by
        have e1 : c * ⟨x, hxC⟩ * c⁻¹ = r * (r⁻¹ * (c * ⟨x, hxC⟩ * c⁻¹)) := by group
        rw [e1]
        exact mul_mem hr (hA'R' h2)
      exact h3
    have hcR : (c : G) ∈ R := by
      have h1 : (c : G) ∈ normalizer (R : Set G) ⊓ C := mem_inf.mpr ⟨hcN, c.2⟩
      rwa [hNC] at h1
    rw [mem_centralizer_iff]
    intro s hs
    have hs' : s ∈ (S : Subgroup (C ⧸ A')) := hs
    rw [hSc] at hs'
    obtain ⟨r, hr, rfl⟩ := hs'
    rw [← map_mul, ← map_mul]
    refine QuotientGroup.eq.mpr ?_
    have hrR : (r : G) ∈ R := hr
    have h1 := hS.commutator_mem_gmsA_of_isX h34 hX (inv_mem hcR) (inv_mem hrR)
    have e1 : (((r * c)⁻¹ * (c * r) : C) : G) =
        (c : G)⁻¹ * (r : G)⁻¹ * (c : G)⁻¹⁻¹ * (r : G)⁻¹⁻¹ := by
      simp only [coe_mul, coe_inv]
      group
    show (((r * c)⁻¹ * (c * r) : C) : G) ∈ gmsA L T
    rw [e1]
    exact h1
  obtain ⟨K, hKn, hK2, -, -, -, -, hKS, -, -, -⟩ :=
    CFSG.GroupTheory.burnside_normal_complement S hNS
  set Kt := K.comap π with hKt
  have : Kt.Normal := hKn.comap π
  set φ : Kt →* K := (π.comp Kt.subtype).codRestrict K fun x => x.2 with hφ
  have hφker : φ.ker = A'.subgroupOf Kt := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    constructor
    · intro h
      have h1 : π (x : C) = 1 := congrArg Subtype.val h
      exact (QuotientGroup.eq_one_iff _).mp h1
    · intro h
      exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr h)
  have hφs : Function.Surjective φ := by
    rintro ⟨k, hk⟩
    obtain ⟨c, rfl⟩ := hπs k
    exact ⟨⟨c, hk⟩, rfl⟩
  have hA''idx : (A'.subgroupOf Kt).index = Nat.card K := by
    rw [← hφker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hφs, card_top]
  have hA''2 : IsPGroup 2 (A'.subgroupOf Kt) :=
    (hS.isR.isPGroup.to_le hAR).comap_subtype.comap_subtype
  have hA''nd : ¬ 2 ∣ (A'.subgroupOf Kt).index := by rw [hA''idx]; exact hK2
  set PA : Sylow 2 Kt := hA''2.toSylow hA''nd with hPA
  have hPAc : (PA : Subgroup Kt) = A'.subgroupOf Kt := IsPGroup.toSylow_coe hA''2 hA''nd
  have hNA : normalizer (PA : Set Kt) ≤ centralizer (PA : Set Kt) := by
    intro k _
    rw [mem_centralizer_iff]
    intro a ha
    have ha' : a ∈ (PA : Subgroup Kt) := ha
    rw [hPAc] at ha'
    exact Subtype.ext (hA'cent (a : C) ha' (k : C)).symm
  obtain ⟨D, -, hD2, -, -, hDchar, -, hDA, -, -, -⟩ :=
    CFSG.GroupTheory.burnside_normal_complement PA hNA
  have := hDchar
  set D' := D.map Kt.subtype with hD'
  have hD'2 : ¬ 2 ∣ Nat.card D' := by
    rw [hD', card_map_of_injective Kt.subtype_injective]
    exact hD2
  have hT₀C : ∀ e ∈ T ⊓ centralizer (L : Set G), e ∈ C := fun e he =>
    mem_centralizer_iff.mpr fun b hb => mem_centralizer_iff.mp (mem_inf.mp he).2 b hb.1.2
  have hfix : ∀ e (he : e ∈ T ⊓ centralizer (L : Set G)), e ≠ 1 →
      ∀ x ∈ D', (⟨e, hT₀C e he⟩ : C) * x = x * ⟨e, hT₀C e he⟩ → x = 1 := by
    intro e he he1 x hx hxe
    apply Subtype.ext
    have hxe' : (x : G) ∈ centralizer ({e} : Set G) ⊓ C := mem_inf.mpr
      ⟨mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hxe).symm, x.2⟩
    have hxT := hS.centralizer_inf_le_T hCe hCL he he1 hxe'
    have hodd : Odd (orderOf (x : G)) := by
      rw [Subgroup.orderOf_coe]
      have h1 : orderOf x ∣ Nat.card D' := Subgroup.orderOf_dvd_natCard D' hx
      by_contra hev
      rw [Nat.not_odd_iff_even] at hev
      exact hD'2 ((even_iff_two_dvd.mp hev).trans h1)
    exact hS.eq_one_of_mem_T_of_odd hxT hodd
  have hT₀el := hS.sec3.isElemAbelian_T₀ hS.foundation
  obtain ⟨u, hu, w, hw, hu1, hw1, huw⟩ := exists_two_ne_one_of_four_le_card h4.ge
  have huw' : u * w ∈ T ⊓ centralizer (L : Set G) := mul_mem hu hw
  have huw1 : u * w ≠ 1 := by
    intro h
    apply huw
    have hw2 : w * w = 1 := by rw [← sq]; exact hT₀el.2 w hw
    calc u = u * w * w := by rw [mul_assoc, hw2, mul_one]
      _ = w := by rw [h, one_mul]
  have hinv : ∀ e (he : e ∈ T ⊓ centralizer (L : Set G)),
      (⟨e, hT₀C e he⟩ : C) * ⟨e, hT₀C e he⟩ = 1 := fun e he =>
    Subtype.ext (by rw [coe_mul, ← sq]; exact hT₀el.2 e he)
  have hD'bot : D' = ⊥ :=
    eq_bot_of_fixedPointFree_of_four (hinv u hu) (hinv w hw)
      (hfix u hu hu1) (hfix w hw hw1) (hfix (u * w) huw' huw1)
  have hDbot : D = ⊥ := (map_eq_bot_iff_of_injective D Kt.subtype_injective).mp hD'bot
  have hKtA : ∀ x : Kt, (x : C) ∈ A' := by
    intro x
    have hPA : (PA : Subgroup Kt) = ⊤ := by rw [← hDA, hDbot, bot_sup_eq]
    have hx : x ∈ (PA : Subgroup Kt) := by rw [hPA]; exact mem_top x
    rw [hPAc] at hx
    exact hx
  have hKbot : K = ⊥ := by
    rw [eq_bot_iff]
    intro k hk
    obtain ⟨c, rfl⟩ := hπs k
    rw [mem_bot]
    exact (QuotientGroup.eq_one_iff c).mpr (hKtA ⟨c, hk⟩)
  have hStop : (S : Subgroup (C ⧸ A')) = ⊤ := by rw [← hKS, hKbot, bot_sup_eq]
  intro x hx
  have h1 : π ⟨x, hx⟩ ∈ (S : Subgroup (C ⧸ A')) := by rw [hStop]; exact mem_top _
  rw [hSc] at h1
  obtain ⟨r, hr, hrπ⟩ := h1
  have h2 : r⁻¹ * ⟨x, hx⟩ ∈ A' := QuotientGroup.eq.mp hrπ
  have h3 : (⟨x, hx⟩ : C) ∈ R' := by
    have e1 : (⟨x, hx⟩ : C) = r * (r⁻¹ * ⟨x, hx⟩) := by group
    rw [e1]
    exact mul_mem hr (hA'R' h2)
  exact h3

end Sec3.SzR

end CFSG.ComponentClassification.GMS78
