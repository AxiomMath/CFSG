module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.SubnormalPrimeCores
public import CFSG.Assembly.Defs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

theorem exists_pow_mem_of_mem_sup_of_isPGroup {G : Type*} [Group G] {p : ℕ} {R L : Subgroup G}
    (hR : IsPGroup p R) (hRL : R ≤ Subgroup.normalizer (L : Set G)) {u : G} (hu : u ∈ R ⊔ L) :
    ∃ e : ℕ, u ^ p ^ e ∈ L := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right R L hRL] at hu
  obtain ⟨v, hv, c, hc, rfl⟩ := hu
  obtain ⟨e, he⟩ := hR ⟨v, hv⟩
  have hve : v ^ p ^ e = 1 := by simpa using congrArg Subtype.val he
  have key : ∀ n : ℕ, ∃ c' ∈ L, (v * c) ^ n = v ^ n * c' := by
    intro n
    induction n with
    | zero => exact ⟨1, L.one_mem, by simp⟩
    | succ n ih =>
      obtain ⟨c', hc', hn⟩ := ih
      refine ⟨v⁻¹ * c' * v * c, L.mul_mem ?_ hc, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (hRL (R.inv_mem hv)) c').mp hc'
        simpa using this
      · rw [pow_succ, hn, pow_succ]
        group
  obtain ⟨c', hc', hn⟩ := key (p ^ e)
  exact ⟨e, by rw [hn, hve, one_mul]; exact hc'⟩

theorem exists_normal_isPGroup_sup_eq_top {W : Type*} [Group W] [Finite W] {r : ℕ}
    [Fact r.Prime] {N : Subgroup W} (hN : N ≤ Subgroup.center W)
    (hq : ∀ w : W, ∃ k : ℕ, w ^ r ^ k ∈ N) :
    ∃ T : Subgroup W, T.Normal ∧ IsPGroup r T ∧ N ⊔ T = ⊤ := by
  have hNn : N.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_center_iff.mp (hN hn) g, mul_inv_cancel_right]
    exact hn⟩
  let f := QuotientGroup.mk' N
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective N
  have hK : IsPGroup r (W ⧸ N) := by
    intro q
    obtain ⟨w, rfl⟩ := hf q
    obtain ⟨k, hk⟩ := hq w
    exact ⟨k, by rw [← map_pow]; exact (QuotientGroup.eq_one_iff _).mpr hk⟩
  obtain ⟨P0⟩ : Nonempty (Sylow r W) := inferInstance
  have hTK : (P0 : Subgroup W).map f = ⊤ :=
    ((P0.mapSurjective hf).is_maximal' (hK.to_subgroup ⊤) le_top).symm
  have hsup : N ⊔ (P0 : Subgroup W) = ⊤ := by
    refine eq_top_iff.mpr fun w _ => ?_
    have hw : f w ∈ (P0 : Subgroup W).map f := hTK ▸ Subgroup.mem_top _
    obtain ⟨t, ht, hft⟩ := hw
    have hk : w * t⁻¹ ∈ N := by
      rw [← QuotientGroup.eq_one_iff]
      change f (w * t⁻¹) = 1
      rw [map_mul, map_inv, hft, mul_inv_cancel]
    have := Subgroup.mul_mem_sup hk ht
    rwa [inv_mul_cancel_right] at this
  have hnormal : (P0 : Subgroup W).Normal := ⟨fun n hn g => by
    have hg : g ∈ N ⊔ (P0 : Subgroup W) := hsup ▸ Subgroup.mem_top g
    rw [← SetLike.mem_coe, Subgroup.normal_mul] at hg
    obtain ⟨k, hk, t, ht, rfl⟩ := hg
    have hkc := Subgroup.mem_center_iff.mp (hN hk)
    have hconj : ∀ x : W, k * x * k⁻¹ = x := fun x => by
      rw [← hkc x]
      group
    have e : k * t * n * (k * t)⁻¹ = k * (t * n * t⁻¹) * k⁻¹ := by group
    rw [e, hconj]
    exact P0.1.mul_mem (P0.1.mul_mem ht hn) (P0.1.inv_mem ht)⟩
  exact ⟨P0, hnormal, P0.isPGroup', hsup⟩

theorem exists_mul_of_pow_mem_of_commute {X : Type*} [Group X] [Finite X] {D Z : Subgroup X}
    (hc : ∀ d ∈ D, ∀ z ∈ Z, d * z = z * d) (h2 : ∀ d ∈ D, ∃ k : ℕ, d ^ 2 ^ k ∈ Z)
    {d : X} (hd : d ∈ D) : ∃ c ∈ pCoreOf 2 D, ∃ z ∈ Z, d = c * z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNc : Z.subgroupOf D ≤ Subgroup.center D := fun z hz =>
    Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hc g g.2 z hz)
  have hNn : (Z.subgroupOf D).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_center_iff.mp (hNc hn) g, mul_inv_cancel_right]
    exact hn⟩
  obtain ⟨T, hTn, hT2, hsup⟩ := exists_normal_isPGroup_sup_eq_top hNc fun w => by
    obtain ⟨k, hk⟩ := h2 w w.2
    exact ⟨k, by rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]; exact hk⟩
  have hTle : T.map D.subtype ≤ pCoreOf 2 D := by
    refine normal_pGroup_le_pCoreOf 2 _ D (Subgroup.map_subtype_le T) ?_ (hT2.map _)
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective D.subtype_injective]
    exact hTn
  have hmem : (⟨d, hd⟩ : D) ∈ ((Z.subgroupOf D ⊔ T : Subgroup D) : Set D) := by
    rw [hsup]
    trivial
  rw [Subgroup.normal_mul] at hmem
  obtain ⟨z, hz, t, ht, he⟩ := hmem
  refine ⟨t, hTle ⟨t, ht, rfl⟩, z, hz, ?_⟩
  have he' : (z : X) * t = d := congrArg Subtype.val he
  rw [← he']
  exact (hc t t.2 z hz).symm

section Centre

variable {Y : Type*} [Group Y] [Finite Y]

omit [Finite Y] in
theorem isSubnormal_of_le_inf_centralizer {K W : Subgroup Y} (hK : IsSubnormal K ⊤)
    (hW : W ≤ K ⊓ Subgroup.centralizer (K : Set Y)) : IsSubnormal W ⊤ := by
  refine IsSubnormal.step (hW.trans inf_le_left) ⟨fun n hn g => ?_⟩ hK
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hc := Subgroup.mem_centralizer_iff.mp (hW hn).2 g g.2
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hc, mul_inv_cancel_right]
  exact hn

omit [Finite Y] in
theorem eq_bot_of_isSubnormal_of_isPGroup (hY : CFSG.pCore 2 Y = ⊥) {W : Subgroup Y}
    (hW : IsSubnormal W ⊤) (h2 : IsPGroup 2 W) : W = ⊥ := by
  have h1 := cfsg_subnormal_pCoreOf_le 2 hW
  rw [pCoreOf_top_eq_pCore, hY] at h1
  have h3 : W ≤ pCoreOf 2 W := normal_pGroup_le_pCoreOf 2 W W le_rfl
    (by rw [Subgroup.subgroupOf_self]; infer_instance) h2
  exact le_bot_iff.mp (h3.trans h1)

theorem coprime_two_card_inf_centralizer (hY : CFSG.pCore 2 Y = ⊥) {K : Subgroup Y}
    (hK : IsSubnormal K ⊤) :
    Nat.Coprime 2 (Nat.card (K ⊓ Subgroup.centralizer (K : Set Y) : Subgroup Y)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
  intro hdvd
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hzo : orderOf (z : Y) = 2 := by rw [Subgroup.orderOf_coe, hz]
  have hW : IsSubnormal (Subgroup.zpowers (z : Y)) ⊤ :=
    isSubnormal_of_le_inf_centralizer hK ((Subgroup.zpowers_le).mpr z.2)
  have h2 : IsPGroup 2 (Subgroup.zpowers (z : Y)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hzo, pow_one]
  have hbot := eq_bot_of_isSubnormal_of_isPGroup hY hW h2
  have hz1 : (z : Y) = 1 := by
    have : (z : Y) ∈ Subgroup.zpowers (z : Y) := Subgroup.mem_zpowers _
    rwa [hbot, Subgroup.mem_bot] at this
  rw [hz1, orderOf_one] at hzo
  exact absurd hzo (by norm_num)

theorem inf_centralizer_le_pPrimeCore (hY : CFSG.pCore 2 Y = ⊥) {K : Subgroup Y}
    (hK : IsSubnormal K ⊤) :
    K ⊓ Subgroup.centralizer (K : Set Y) ≤ CFSG.pPrimeCore 2 Y := by
  set Z := K ⊓ Subgroup.centralizer (K : Set Y) with hZ
  have hZs : IsSubnormal Z ⊤ := isSubnormal_of_le_inf_centralizer hK le_rfl
  have hcop := coprime_two_card_inf_centralizer hY hK
  have h1 := cfsg_subnormal_primeComplementCoreOf_le 2 hZs
  rw [primeComplementCoreOf_top_eq_primeComplementCore] at h1
  have htop : primeComplementCore (G := Z) 2 = ⊤ :=
    eq_top_iff.mpr (normal_coprime_le_primeComplementCore 2 ⊤ inferInstance
      (by rw [Subgroup.card_top]; exact hcop))
  have h2 : Z ≤ primeComplementCoreOf 2 Z := by
    rw [primeComplementCoreOf, htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  exact (h2.trans h1).trans (sSup_le fun N hN => le_sSup hN)

end Centre

end CFSG.AGLEmbedding
