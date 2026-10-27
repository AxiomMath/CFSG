module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Basic

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_isElemTwo_card_eq_pRank (H : Subgroup G) :
    ∃ F : Subgroup G, F ≤ H ∧ IsElemTwo F ∧ Nat.card F = 2 ^ pRank 2 ↥H := by
  set s := {r : ℕ | ∃ B : Subgroup ↥H, IsElementaryAbelian 2 ↥B ∧ Nat.card B = 2 ^ r} with hs
  have hne : s.Nonempty := by
    refine ⟨0, ⊥, ?_, by simp⟩
    exact { is_comm := ⟨fun x y => Subsingleton.elim _ _⟩
            exponent_dvd_p := by simp }
  have hbdd : BddAbove s := by
    refine ⟨Nat.card H, ?_⟩
    rintro k ⟨B, -, hB⟩
    calc k ≤ 2 ^ k := (Nat.lt_two_pow_self).le
      _ = Nat.card B := hB.symm
      _ ≤ Nat.card H := card_le_card_group B
  obtain ⟨B, hBe, hBc⟩ := Nat.sSup_mem hne hbdd
  refine ⟨B.map H.subtype, map_subtype_le _, ⟨?_, ?_⟩, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have hc := hBe.toIsMulCommutative.is_comm.comm (⟨x, hx⟩ : B) ⟨y, hy⟩
    exact congrArg (fun w : B => ((w : ↥H) : G)) hc
  · rintro _ ⟨x, hx, rfl⟩
    have h2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := B) x hx
    have h2' := congrArg Subtype.val h2
    rw [← pow_two]
    exact h2'
  · rw [card_map_of_injective H.subtype_injective, hBc]
    rfl

omit [Finite G] in
theorem commute_of_mem_coreActionKernel_of_central {K : Subgroup G} (hperf : ⁅K, K⁆ = K)
    (hO : ∀ x ∈ oddIn K, ∀ k ∈ K, x * k = k * x) {b : G} (hb : b ∈ coreActionKernel K) :
    ∀ k ∈ K, b * k = k * b := by
  set B := zpowers b with hB
  have hBK : B ≤ coreActionKernel K := zpowers_le.mpr hb
  have h1 : ⁅K, B⁆ ≤ oddIn K := by
    rw [commutator_le]
    intro k hk y hy
    have h := (mem_coreActionKernel.mp (inv_mem (hBK hy))).2 k⁻¹ (inv_mem hk)
    rw [inv_inv, inv_inv] at h
    rwa [commutatorElement_def]
  have h2 : ⁅⁅K, B⁆, K⁆ = ⊥ := by
    rw [eq_bot_iff, commutator_le]
    intro x hx k hk
    rw [mem_bot, commutatorElement_def, hO x (h1 hx) k hk]
    group
  have h3 : ⁅⁅B, K⁆, K⁆ = ⊥ := by rw [commutator_comm B K, h2]
  have h4 : ⁅⁅K, K⁆, B⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := K) (H₂ := K) (H₃ := B) h2 h3
  rw [hperf] at h4
  intro k hk
  have h5 : ⁅k, b⁆ ∈ ⁅K, B⁆ := commutator_mem_commutator hk (mem_zpowers b)
  rw [h4, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h5
  exact h5.symm

omit [Finite G] in
theorem le_of_conj_eq_inv {K D : Subgroup G} {z : G} (hz : z ∈ K)
    (hDK : D ≤ normalizer (K : Set G)) (hD : ∀ d ∈ D, z * d * z⁻¹ = d⁻¹)
    (hodd : Odd (Nat.card D)) : D ≤ K := by
  intro d hd
  have h1 : d * z * d⁻¹ ∈ K := (mem_normalizer_iff.mp (hDK hd) z).mp hz
  have h2 : d * d ∈ K := by
    have h3 : d * d = (d * z * d⁻¹) * z⁻¹ := by
      calc d * d = d * (z * d * z⁻¹)⁻¹ := by rw [hD d hd, inv_inv]
        _ = (d * z * d⁻¹) * z⁻¹ := by group
    rw [h3]
    exact mul_mem h1 (inv_mem hz)
  have hdo : Odd (orderOf d) := by
    have h4 := orderOf_dvd_natCard (⟨d, hd⟩ : D)
    rw [Subgroup.orderOf_mk] at h4
    exact Odd.of_dvd_nat hodd h4
  obtain ⟨k, hk⟩ := hdo
  have h5 : d = (d * d) ^ (k + 1) := by
    rw [← pow_two, ← pow_mul, show 2 * (k + 1) = orderOf d + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  rw [h5]
  exact pow_mem h2 _

omit [Finite G] in
theorem normal_le_center_or_eq_top_of_isQuasisimple {Q : Type*} [Group Q] (hQ : IsQuasisimple Q)
    (N : Subgroup Q) [N.Normal] : N ≤ center Q ∨ N = ⊤ := by
  let π := QuotientGroup.mk' (center Q)
  have : IsSimpleGroup (Q ⧸ center Q) := hQ.2.1
  have hnormal : (N.map π).Normal :=
    Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective _)
  rcases hnormal.eq_bot_or_eq_top with hbot | htop
  · left
    have hker : N ≤ π.ker := N.map_eq_bot_iff.mp hbot
    simpa only [π, QuotientGroup.ker_mk'] using hker
  · right
    have hsup : N ⊔ center Q = ⊤ := by
      have hcomap := Subgroup.comap_map_eq π N
      rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at hcomap
      exact hcomap.symm
    have hderived : commutator Q ≤ N :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
    rw [hQ.1.commutator_eq_top] at hderived
    exact top_unique hderived

omit [Finite G] in
theorem le_sup_oddIn_of_normal {L N : Subgroup G} (hq : IsQuasisimple (L ⧸ pPrimeCore 2 L))
    (hNL : N ≤ L) (hLN : L ≤ normalizer (N : Set G)) (hNZ : ¬ N ≤ zStarIn L) :
    L ≤ N ⊔ oddIn L := by
  have hNn : (N.subgroupOf L).Normal := (normal_subgroupOf_iff_le_normalizer hNL).mpr hLN
  set M := (N.subgroupOf L).map (QuotientGroup.mk' (pPrimeCore 2 L)) with hM
  have hMn : M.Normal := hNn.map _ (QuotientGroup.mk'_surjective _)
  rcases normal_le_center_or_eq_top_of_isQuasisimple hq M with h | h
  · exfalso
    apply hNZ
    intro n hn
    have h1 : QuotientGroup.mk' (pPrimeCore 2 L) (⟨n, hNL hn⟩ : L) ∈ M :=
      mem_map_of_mem _ (mem_subgroupOf.mpr hn)
    refine ⟨⟨n, hNL hn⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Sol78.fusionZStar_eq_comap, mem_comap]
    exact h h1
  · intro l hl
    have h1 : QuotientGroup.mk' (pPrimeCore 2 L) (⟨l, hl⟩ : L) ∈ M := h ▸ mem_top _
    obtain ⟨n', hn', hn'l⟩ := h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hn'l
    have h2 : (l : G) = (n' : G) * ((n'⁻¹ * ⟨l, hl⟩ : L) : G) := by simp
    rw [h2]
    exact mul_mem (mem_sup_left (mem_subgroupOf.mp hn')) (mem_sup_right ⟨_, hn'l, rfl⟩)

theorem oddIn_le_center_of_le_sup {L : Subgroup G} (hperf : ⁅L, L⁆ = L)
    (hle : L ≤ (L ⊓ centralizer (oddIn L : Set G)) ⊔ oddIn L) :
    oddIn L ≤ (center ↥L).map L.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup ↥L := (L ⊓ centralizer (oddIn L : Set G)).subgroupOf L with hN
  set X : Subgroup ↥L := (oddIn L).subgroupOf L with hX
  have hXchar : (pPrimeCore 2 ↥L).Characteristic := pPrimeCore_characteristic
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    obtain ⟨hnL, hnC⟩ := mem_inf.mp hn
    refine mem_inf.mpr ⟨mul_mem (mul_mem g.2 hnL) (inv_mem g.2),
      mem_centralizer_iff.mpr fun x hx => ?_⟩
    have hx' : (g : G)⁻¹ * x * (g : G) ∈ oddIn L := by
      have h := CFSG.Walter.conj_mem_map_of_characteristic (inv_mem (le_normalizer g.2)) hx
      rwa [inv_inv] at h
    have h1 := mem_centralizer_iff.mp hnC _ hx'
    simp only [coe_mul, coe_inv]
    calc x * ((g : G) * (n : G) * (g : G)⁻¹) =
        (g : G) * (((g : G)⁻¹ * x * (g : G)) * (n : G)) * (g : G)⁻¹ := by group
      _ = (g : G) * ((n : G) * ((g : G)⁻¹ * x * (g : G))) * (g : G)⁻¹ := by rw [h1]
      _ = (g : G) * (n : G) * (g : G)⁻¹ * x := by group
  have hXsolv : Group.IsSolvable X := by
    have hXc : Nat.card X = Nat.card (oddIn L) :=
      Nat.card_congr (subgroupOfEquivOfLe (map_subtype_le _)).toEquiv
    have hodd : Odd (Nat.card X) := by
      rw [hXc, oddIn, card_map_of_injective (subtype_injective _)]
      exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
    exact CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hLperf : Group.IsPerfect (⊤ : Subgroup ↥L) := by
    have h : Group.IsPerfect ↥L := (Subgroup.isPerfect_iff (H := L)).mpr hperf
    exact Group.IsPerfect.ofSurjective (f := (Subgroup.topEquiv (G := ↥L)).symm.toMonoidHom)
      (Subgroup.topEquiv (G := ↥L)).symm.surjective
  have htop : (⊤ : Subgroup ↥L) ≤ N ⊔ X := by
    intro l _
    have hl := hle l.2
    obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ L ⊓ centralizer (oddIn L : Set G), ∃ b ∈ oddIn L,
        a * b = (l : G) := by
      have hn : oddIn L ≤ normalizer ((L ⊓ centralizer (oddIn L : Set G) : Subgroup G) : Set G) :=
        fun x hx => by
          have hxL : x ∈ L := map_subtype_le _ hx
          refine mem_normalizer_iff.mpr fun h => ⟨fun hh => ?_, fun hh => ?_⟩
          · obtain ⟨hhL, hhC⟩ := mem_inf.mp hh
            refine mem_inf.mpr ⟨mul_mem (mul_mem hxL hhL) (inv_mem hxL), ?_⟩
            rw [mem_centralizer_iff.mp hhC x hx, mul_inv_cancel_right]
            exact hhC
          · obtain ⟨hhL, hhC⟩ := mem_inf.mp hh
            have hh' : h ∈ L := by
              have := mul_mem (mul_mem (inv_mem hxL) hhL) hxL
              rwa [show x⁻¹ * (x * h * x⁻¹) * x = h by group] at this
            refine mem_inf.mpr ⟨hh', ?_⟩
            have h1 := mem_centralizer_iff.mp hhC x hx
            have h2 : h = x * h * x⁻¹ := by
              calc h = x⁻¹ * (x * h * x⁻¹) * x := by group
                _ = x⁻¹ * (x * (x * h * x⁻¹)) * x⁻¹ * x * x⁻¹ * x := by rw [h1]; group
                _ = x * h * x⁻¹ := by group
            rw [h2]
            exact hhC
      have hs := (coe_mul_of_right_le_normalizer_left _ _ hn).symm ▸ (show (l : G) ∈
        (((L ⊓ centralizer (oddIn L : Set G)) ⊔ oddIn L : Subgroup G) : Set G) from hl)
      obtain ⟨a, ha, b, hb, hab⟩ := hs
      exact ⟨a, ha, b, hb, hab⟩
    have haL : a ∈ L := (mem_inf.mp ha).1
    have hbL : b ∈ L := map_subtype_le _ hb
    have hl' : l = ⟨a, haL⟩ * ⟨b, hbL⟩ := Subtype.ext hab.symm
    rw [hl']
    exact mul_mem (mem_sup_left (mem_subgroupOf.mpr ha)) (mem_sup_right (mem_subgroupOf.mpr hb))
  have hLN := ClassicalInvolution.LBalanceProof.perfect_le_of_le_sup_solvable ⊤ N X htop
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨x, mem_center_iff.mpr fun g => Subtype.ext ?_, rfl⟩
  have hg := hLN (mem_top g)
  rw [hN, mem_subgroupOf] at hg
  rw [coe_mul, coe_mul]
  exact (mem_centralizer_iff.mp (mem_inf.mp hg).2 _ ⟨x, hx, rfl⟩).symm

end CFSG.ComponentClassification.GrSLit.GrS5
