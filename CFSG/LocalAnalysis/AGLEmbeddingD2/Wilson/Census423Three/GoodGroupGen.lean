module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census423Three.GoodGroup

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census423Three

open CFSG
open scoped commutatorElement

theorem rad_of_isQuasisimple {S : Type} [Group S] [Finite S] (hq : CFSG.IsQuasisimple S)
    {N : Subgroup S} (hN : N.Normal) (hs : Group.IsSolvable N) :
    ∀ n ∈ N, ∀ y : S, n * y = y * n := by
  obtain ⟨-, hsimple, a, b, hab⟩ := hq
  set π := QuotientGroup.mk' (Subgroup.center S) with hπ
  have hNm : (N.map π).Normal := hN.map π (QuotientGroup.mk'_surjective _)
  have hsm : Group.IsSolvable (N.map π) :=
    Group.isSolvable_of_surjective (f := π.subgroupMap N) (π.subgroupMap_surjective N)
  have := hsimple
  have hNmn := hNm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map π) with h | h
  · intro n hn y
    have h1 : π n = 1 := by
      have := Subgroup.mem_map_of_mem π hn
      rw [h] at this
      simpa using this
    have h2 : n ∈ Subgroup.center S := (QuotientGroup.eq_one_iff n).mp h1
    exact (Subgroup.mem_center_iff.mp h2 y).symm
  · exfalso
    have hsolv : Group.IsSolvable (S ⧸ Subgroup.center S) := by
      have h3 : Group.IsSolvable ↥(⊤ : Subgroup (S ⧸ Subgroup.center S)) := by
        rw [← h]; exact hsm
      exact Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.topEquiv (G := S ⧸ Subgroup.center S)).symm.toMonoidHom)
        (Subgroup.topEquiv (G := S ⧸ Subgroup.center S)).symm.injective
    exact hab ((IsSimpleGroup.comm_iff_isSolvable).mpr hsolv a b)

theorem center_quotient_eq_bot {S : Type} [Group S] (hq : CFSG.IsQuasisimple S) :
    Subgroup.center (S ⧸ Subgroup.center S) = ⊥ := by
  obtain ⟨-, hsimple, a, b, hab⟩ := hq
  have := hsimple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (S ⧸ Subgroup.center S)) with
    h | h
  · exact h
  · exfalso
    have : a ∈ Subgroup.center (S ⧸ Subgroup.center S) := by rw [h]; trivial
    exact hab (Subgroup.mem_center_iff.mp this b).symm

theorem noCentral3_of_card {S : Type} [Group S] [Finite S]
    (h : ¬ 3 ∣ Nat.card (Subgroup.center S)) :
    ∀ z : S, (∀ y, z * y = y * z) → z ^ 3 = 1 → z = 1 := by
  intro z hz hz3
  have hzc : z ∈ Subgroup.center S := Subgroup.mem_center_iff.mpr fun y => (hz y).symm
  have h1 : orderOf (⟨z, hzc⟩ : Subgroup.center S) ∣ Nat.card (Subgroup.center S) :=
    orderOf_dvd_natCard _
  have h2 : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one hz3
  have h3 : orderOf z ∣ Nat.card (Subgroup.center S) := by
    rwa [← Subgroup.orderOf_coe (⟨z, hzc⟩ : Subgroup.center S)] at h1
  have h4 : orderOf z = 1 ∨ orderOf z = 3 := (Nat.dvd_prime Nat.prime_three).mp h2
  rcases h4 with h4 | h4
  · exact orderOf_eq_one_iff.mp h4
  · exact absurd (h4 ▸ h3) h

theorem conj3_of_cyclic_sylow {S : Type} [Group S] [Finite S] (hc : ∀ P : Sylow 3 S, IsCyclic P) :
    ∀ x y : S, x ≠ 1 → x ^ 3 = 1 → y ≠ 1 → y ^ 3 = 1 →
      ∃ g : S, Subgroup.zpowers (g * x * g⁻¹) = Subgroup.zpowers y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro x y hx1 hx3 hy1 hy3
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hyo : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hpx : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxo]; norm_num)
  have hpy : IsPGroup 3 (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyo]; norm_num)
  obtain ⟨Px, hPx⟩ := IsPGroup.exists_le_sylow hpx
  obtain ⟨Py, hPy⟩ := IsPGroup.exists_le_sylow hpy
  obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq (M := S) Py Px
  have hgy : g * y * g⁻¹ ∈ (Px : Subgroup S) := by
    rw [← hg]
    have hyP : y ∈ (Py : Subgroup S) := hPy (Subgroup.mem_zpowers y)
    exact (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨y, hyP, by simp⟩
  have hyo' : orderOf (g * y * g⁻¹) = 3 := by
    have h3 : (g * y * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hy3, mul_one, mul_inv_cancel]
    have h1 : g * y * g⁻¹ ≠ 1 := by
      intro h
      apply hy1
      have : g * y * g⁻¹ = 1 := h
      simpa [mul_inv_eq_one] using this
    exact orderOf_eq_prime h3 h1
  set P : Subgroup S := (Px : Subgroup S) with hP
  have := hc Px
  set a : P := ⟨x, hPx (Subgroup.mem_zpowers x)⟩ with ha
  set b : P := ⟨g * y * g⁻¹, hgy⟩ with hb
  have hcard : Nat.card (Subgroup.zpowers a) = Nat.card (Subgroup.zpowers b) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, ← Subgroup.orderOf_coe a, ← Subgroup.orderOf_coe b]
    simp only [ha, hb]
    rw [hxo, hyo']
  have heq : Subgroup.zpowers a = Subgroup.zpowers b := IsCyclic.subgroup_eq_iff_card_eq.mpr hcard
  have hmap := congrArg (Subgroup.map P.subtype) heq
  rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at hmap
  change Subgroup.zpowers x = Subgroup.zpowers (g * y * g⁻¹) at hmap
  refine ⟨g⁻¹, ?_⟩
  have h2 := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hmap
  rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at h2
  simpa [MulAut.conj_apply, mul_assoc] using h2

theorem GoodGroup.of_central_quotient {S : Type} [Group S] [Finite S]
    (hq : CFSG.IsQuasisimple S) (h3 : ¬ 3 ∣ Nat.card (Subgroup.center S))
    (helt : ∃ s : S, s ≠ 1 ∧ s ^ 3 = 1) (hG : GoodGroup (S ⧸ Subgroup.center S)) :
    GoodGroup S where
  rad N hN hs n hn y := rad_of_isQuasisimple hq hN hs n hn y
  elt3 := helt
  noCentral3 := noCentral3_of_card h3
  conj3 x y hx1 hx3 hy1 hy3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hnc := noCentral3_of_card h3
    set π := QuotientGroup.mk' (Subgroup.center S) with hπ
    have hne : ∀ t : S, t ≠ 1 → t ^ 3 = 1 → π t ≠ 1 := by
      intro t ht1 ht3 h
      have hc : t ∈ Subgroup.center S := (QuotientGroup.eq_one_iff t).mp h
      exact ht1 (hnc t (fun y => (Subgroup.mem_center_iff.mp hc y).symm) ht3)
    obtain ⟨gbar, hgbar⟩ := hG.conj3 (π x) (π y) (hne x hx1 hx3) (by rw [← map_pow, hx3, map_one])
      (hne y hy1 hy3) (by rw [← map_pow, hy3, map_one])
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gbar
    have hmem : π (g * x * g⁻¹) ∈ Subgroup.zpowers (π y) := by
      rw [← hgbar]
      have : π (g * x * g⁻¹) = (QuotientGroup.mk g) * π x * (QuotientGroup.mk g)⁻¹ := by
        simp [hπ]
      rw [this]
      exact Subgroup.mem_zpowers _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hz : (y ^ k)⁻¹ * (g * x * g⁻¹) ∈ Subgroup.center S := by
      rw [← QuotientGroup.eq]
      change π (y ^ k) = π (g * x * g⁻¹)
      rw [map_zpow]
      exact hk
    set z := (y ^ k)⁻¹ * (g * x * g⁻¹) with hzdef
    have hgx : g * x * g⁻¹ = y ^ k * z := by rw [hzdef]; group
    have hzc : Commute (y ^ k) z := Subgroup.mem_center_iff.mp hz (y ^ k)
    have hz3 : z ^ 3 = 1 := by
      have h1 : (g * x * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hx3, mul_one, mul_inv_cancel]
      rw [hgx, hzc.mul_pow] at h1
      have h2 : (y ^ k) ^ 3 = 1 := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy3, one_zpow]
      rwa [h2, one_mul] at h1
    have hz1 : z = 1 := hnc z (fun t => (Subgroup.mem_center_iff.mp hz t).symm) hz3
    have hgxy : g * x * g⁻¹ = y ^ k := by rw [hgx, hz1, mul_one]
    refine ⟨g, ?_⟩
    have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
    have hyo : orderOf y = 3 := orderOf_eq_prime hy3 hy1
    have hgo : orderOf (g * x * g⁻¹) = 3 := by
      have h3' : (g * x * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hx3, mul_one, mul_inv_cancel]
      have h1' : g * x * g⁻¹ ≠ 1 := by
        intro h
        apply hx1
        have : g * x * g⁻¹ = 1 := h
        simpa [mul_inv_eq_one] using this
      exact orderOf_eq_prime h3' h1'
    have hle : Subgroup.zpowers (g * x * g⁻¹) ≤ Subgroup.zpowers y := by
      rw [Subgroup.zpowers_le, hgxy]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers y) k
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hgo, hyo]
  inner3 α hα := by
    have hcen : (Subgroup.center S).map α.toMonoidHom = Subgroup.center S := by
      ext z
      constructor
      · rintro ⟨c, hc, rfl⟩
        rw [SetLike.mem_coe, Subgroup.mem_center_iff] at hc
        rw [Subgroup.mem_center_iff]
        intro t
        have := hc (α.symm t)
        have h2 := congrArg α this
        simpa using h2
      · intro hz
        refine ⟨α.symm z, ?_, by simp⟩
        change α.symm z ∈ Subgroup.center S
        rw [Subgroup.mem_center_iff] at hz ⊢
        intro t
        apply α.injective
        simpa using hz (α t)
    set abar : MulAut (S ⧸ Subgroup.center S) :=
      QuotientGroup.congr (Subgroup.center S) (Subgroup.center S) α hcen with habardef
    have hmk : ∀ y : S, abar (QuotientGroup.mk y) = QuotientGroup.mk (α y) := fun y => rfl
    have hpow : ∀ (n : ℕ) (y : S), (abar ^ n) (QuotientGroup.mk y) =
        QuotientGroup.mk ((α ^ n) y) := by
      intro n
      induction n with
      | zero => intro y; simp
      | succ n ih =>
        intro y
        rw [pow_succ, MulAut.mul_apply, pow_succ, MulAut.mul_apply, hmk, ih]
    have habar3 : abar ^ 3 = 1 := by
      ext t
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective t
      rw [hpow, hα]
      rfl
    obtain ⟨sbar, hsbar⟩ := hG.inner3 abar habar3
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective sbar
    refine ⟨s, fun y => ?_⟩
    have h1 := hsbar (QuotientGroup.mk y)
    rw [center_quotient_eq_bot hq, Subgroup.mem_bot, hmk] at h1
    rw [← QuotientGroup.eq_one_iff]
    rw [← h1]
    simp

end CFSG.AGLEmbeddingD2.Wilson.Census423Three
