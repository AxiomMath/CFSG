module

public import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.GNLift

open CFSG.Open

theorem isElemAbelian_of_le {p : ℕ} {W : Type} [Group W] {E F : Subgroup W}
    (hE : IsElemAbelian p E) (hF : F ≤ E) : IsElemAbelian p F := CFSG.Open.IsElemAbelian.mono hE hF

theorem not_isCyclic_of_isElemAbelian {p : ℕ} [hp : Fact p.Prime] {W : Type} [Group W]
    {E : Subgroup W} (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 2) :
    ¬ IsCyclic E := by
  intro hcyc
  have hfin : Finite E :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ hp.out.ne_zero)
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := E)
  have hgp : (g : W) ^ p = 1 := hE.2 _ g.2
  have hdvd : orderOf (g : W) ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hgp
  rw [Subgroup.orderOf_coe, hg, hc] at hdvd
  have h1 : p ^ 2 ≤ p := Nat.le_of_dvd hp.out.pos hdvd
  have h2 := hp.out.two_le
  nlinarith

theorem exists_elemAbelian_card_sq {p : ℕ} [hp : Fact p.Prime] {W : Type} [Group W] [Finite W]
    {H : Subgroup W} (h : 1 < pRank p H) :
    ∃ E : Subgroup W, E ≤ H ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  obtain ⟨E, hEH, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp.out.one_lt H
  have hfin : Finite E :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.out.ne_zero)
  have hpg : IsPGroup p E := IsPGroup.iff_card.mpr ⟨_, hcard⟩
  have hle : p ^ 2 ≤ Nat.card E := by
    rw [hcard]
    exact Nat.pow_le_pow_right hp.out.pos (by omega)
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card hp.out hpg hle
  refine ⟨K.map E.subtype, ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨k, -, rfl⟩ := Subgroup.mem_map.mp hw
    exact hEH k.2
  · refine isElemAbelian_of_le hE ?_
    intro w hw
    obtain ⟨k, -, rfl⟩ := Subgroup.mem_map.mp hw
    exact k.2
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective E), hK]

theorem exists_isPGroup_map_eq {p : ℕ} [Fact p.Prime] {X W : Type} [Group X] [Group W]
    [Finite X] {f : X →* W} {Y : Subgroup X} {E : Subgroup W} (hE : IsPGroup p E)
    (hEY : E ≤ Y.map f) : ∃ U : Subgroup X, U ≤ Y ∧ IsPGroup p U ∧ U.map f = E := by
  let V : Subgroup X := Y ⊓ E.comap f
  let ψ : V →* E := (f.comp V.subtype).codRestrict E (fun v => (Subgroup.mem_inf.mp v.2).2)
  have hψ : Function.Surjective ψ := by
    intro e
    obtain ⟨y, hy, hfy⟩ := Subgroup.mem_map.mp (hEY e.2)
    refine ⟨⟨y, Subgroup.mem_inf.mpr ⟨hy, ?_⟩⟩, ?_⟩
    · show f y ∈ E
      rw [hfy]
      exact e.2
    · apply Subtype.ext
      exact hfy
  obtain ⟨P⟩ : Nonempty (Sylow p V) := inferInstance
  have hQtop : (⊤ : Subgroup E) = (Sylow.mapSurjective hψ P).toSubgroup :=
    (Sylow.mapSurjective hψ P).is_maximal' (hE.to_subgroup ⊤) le_top
  refine ⟨P.toSubgroup.map V.subtype, ?_, P.isPGroup'.map V.subtype, ?_⟩
  · intro u hu
    obtain ⟨v, -, rfl⟩ := Subgroup.mem_map.mp hu
    exact (Subgroup.mem_inf.mp v.2).1
  · apply le_antisymm
    · intro w hw
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hw
      obtain ⟨v, -, rfl⟩ := Subgroup.mem_map.mp hu
      exact (Subgroup.mem_inf.mp v.2).2
    · intro e he
      have hmem : (⟨e, he⟩ : E) ∈ P.toSubgroup.map ψ := by
        change (⟨e, he⟩ : E) ∈ (Sylow.mapSurjective hψ P).toSubgroup
        rw [← hQtop]
        exact Subgroup.mem_top _
      obtain ⟨v, hv, hvE⟩ := Subgroup.mem_map.mp hmem
      refine Subgroup.mem_map.mpr ⟨v.1, Subgroup.mem_map.mpr ⟨v, hv, rfl⟩, ?_⟩
      exact congrArg Subtype.val hvE

theorem mem_zpowers_or_mem_zpowers {p : ℕ} [Fact p.Prime] {W : Type} [Group W] [Finite W]
    {x y : W} (hx : ∃ k : ℕ, orderOf x = p ^ k) (hy : ∃ k : ℕ, orderOf y = p ^ k)
    (hc : IsCyclic ↥(Subgroup.closure ({x, y} : Set W))) :
    x ∈ Subgroup.zpowers y ∨ y ∈ Subgroup.zpowers x := by
  set C := Subgroup.closure ({x, y} : Set W) with hC
  have hxC : x ∈ C := Subgroup.subset_closure (by simp)
  have hyC : y ∈ C := Subgroup.subset_closure (by simp)
  let x' : C := ⟨x, hxC⟩
  let y' : C := ⟨y, hyC⟩
  have hox : orderOf x' = orderOf x := (Subgroup.orderOf_coe x').symm
  have hoy : orderOf y' = orderOf y := (Subgroup.orderOf_coe y').symm
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  rcases le_total a b with hab | hab
  · have hdvd : orderOf x' ∣ orderOf y' := by
      rw [hox, hoy, ha, hb]
      exact pow_dvd_pow p hab
    have hle : Subgroup.zpowers x' ≤ Subgroup.zpowers y' := by
      rw [IsCyclic.subgroup_le_iff_card_dvd, Nat.card_zpowers, Nat.card_zpowers]
      exact hdvd
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hle (Subgroup.mem_zpowers x'))
    left
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have := congrArg Subtype.val hk
    simpa using this
  · have hdvd : orderOf y' ∣ orderOf x' := by
      rw [hox, hoy, ha, hb]
      exact pow_dvd_pow p hab
    have hle : Subgroup.zpowers y' ≤ Subgroup.zpowers x' := by
      rw [IsCyclic.subgroup_le_iff_card_dvd, Nat.card_zpowers, Nat.card_zpowers]
      exact hdvd
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hle (Subgroup.mem_zpowers y'))
    right
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have := congrArg Subtype.val hk
    simpa using this

theorem isPGroup_closure_pair {p : ℕ} [Fact p.Prime] {W : Type} [Group W] [Finite W] {x y : W}
    (hxy : Commute x y) (hx : ∃ k : ℕ, orderOf x = p ^ k) (hy : ∃ k : ℕ, orderOf y = p ^ k) :
    IsPGroup p ↥(Subgroup.closure ({x, y} : Set W)) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  have hpow : ∀ (g : W) (m : ℤ) (N : ℕ), (g ^ m) ^ N = (g ^ N) ^ m := by
    intro g m N
    rw [← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul, mul_comm]
  have hdecomp : ∀ z ∈ Subgroup.closure ({x, y} : Set W),
      ∃ m n : ℤ, x ^ m * y ^ n = z := by
    intro z hz
    induction hz using Subgroup.closure_induction with
    | mem g hg =>
      rcases hg with rfl | rfl
      · exact ⟨1, 0, by simp⟩
      · exact ⟨0, 1, by simp⟩
    | one => exact ⟨0, 0, by simp⟩
    | mul g h _ _ ihg ihh =>
      obtain ⟨m, n, rfl⟩ := ihg
      obtain ⟨m', n', rfl⟩ := ihh
      refine ⟨m + m', n + n', ?_⟩
      have hc : Commute (y ^ n) (x ^ m') := (hxy.zpow_zpow m' n).symm
      have key : y ^ n * (x ^ m' * y ^ n') = x ^ m' * (y ^ n * y ^ n') := by
        rw [← mul_assoc, hc.eq, mul_assoc]
      rw [zpow_add, zpow_add, mul_assoc (x ^ m) (y ^ n), key, mul_assoc]
    | inv g _ ihg =>
      obtain ⟨m, n, rfl⟩ := ihg
      refine ⟨-m, -n, ?_⟩
      have hc : Commute (x ^ (-m)) (y ^ (-n)) := hxy.zpow_zpow (-m) (-n)
      rw [mul_inv_rev, ← zpow_neg, ← zpow_neg]
      exact hc.eq
  intro g
  obtain ⟨z, hz⟩ := g
  obtain ⟨m, n, rfl⟩ := hdecomp z hz
  refine ⟨a + b, ?_⟩
  have hxN : x ^ (p ^ (a + b)) = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (by rw [ha]; exact pow_dvd_pow p (Nat.le_add_right a b))
  have hyN : y ^ (p ^ (a + b)) = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (by rw [hb]; exact pow_dvd_pow p (Nat.le_add_left b a))
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  show (x ^ m * y ^ n) ^ (p ^ (a + b)) = 1
  rw [(hxy.zpow_zpow m n).mul_pow, hpow x m, hpow y n, hxN, hyN, one_zpow, one_zpow, one_mul]
