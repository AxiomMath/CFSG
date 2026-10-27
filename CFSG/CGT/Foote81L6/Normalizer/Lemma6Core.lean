module

public import CFSG.CGT.Foote81L6.Normalizer.GroupAux
public import CFSG.Quasithin.Background.B19Block
public import CFSG.Adapters.Involutions
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.CGT.Foote81L6.Normalizer

open CFSG.Quasithin

structure IsTransvectionBlockAt {V X : Type*} [CommGroup V] [Group X] (ρ : X →* MulAut V)
    (d : X) (w : V) (y : X) : Prop where
  orderOf_eq : orderOf y = 3
  mem_pPrimeCore : y ∈ pPrimeCore 2 X
  conj_eq_inv : d * y * d⁻¹ = y⁻¹
  normal : (Subgroup.zpowers y).Normal
  card_comm : Nat.card (commV (Subgroup.zpowers (ρ y))) = 4
  centre_mem : w ∈ commV (Subgroup.zpowers (ρ y))
  mem_comm : ∀ v ∈ commV (Subgroup.zpowers (ρ y)),
    v = 1 ∨ v = w ∨ v = ρ y w ∨ v = ρ y (ρ y w)
  comm_invariant : ∀ g : X, ∀ v ∈ commV (Subgroup.zpowers (ρ y)),
    ρ g v ∈ commV (Subgroup.zpowers (ρ y))
  fix_invariant : ∀ g : X, ∀ v ∈ fixV (Subgroup.zpowers (ρ y)),
    ρ g v ∈ fixV (Subgroup.zpowers (ρ y))
  fix_of_mem : ∀ v ∈ fixV (Subgroup.zpowers (ρ y)), ρ d v = v
  inf_eq : commV (Subgroup.zpowers (ρ y)) ⊓ fixV (Subgroup.zpowers (ρ y)) = ⊥
  sup_eq : commV (Subgroup.zpowers (ρ y)) ⊔ fixV (Subgroup.zpowers (ρ y)) = ⊤

theorem exists_isolatedTransvectionBlock {V X : Type} [CommGroup V] [Finite V] [Group X]
    [Finite X] (hV : ∀ v : V, v * v = 1) {ρ : X →* MulAut V} (hρ : Function.Injective ρ)
    (D : Sylow 2 X) {d : X} (hdD : d ∈ (D : Subgroup X)) {w : V}
    (hdw : IsTransvectionWith (ρ d) w) (hd1 : ρ d ≠ 1)
    (hfus : ∀ y ∈ (D : Subgroup X), IsConj d y → y = d) (hmove : ∃ g : X, ρ g w ≠ w) :
    ∃ y : X, IsTransvectionBlockAt ρ d w y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV' : ∀ v : V, v ^ 2 = 1 := fun v => by rw [pow_two]; exact hV v
  have hd2 : d * d = 1 := hρ (by rw [map_mul, B1.tv_sq hV' hdw hd1, map_one])
  have hd1' : d ≠ 1 := fun h => hd1 (by rw [h, map_one])
  have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd2
  have hzZ : (⟨d, hdD⟩ : (D : Subgroup X)) ∈ Subgroup.center (D : Subgroup X) := by
    rw [Subgroup.mem_center_iff]
    intro c
    apply Subtype.ext
    have h1 := hfus _ ((D : Subgroup X).mul_mem ((D : Subgroup X).mul_mem c.2 hdD)
      ((D : Subgroup X).inv_mem c.2)) (isConj_iff.mpr ⟨c, rfl⟩)
    show (c : X) * d = d * c
    calc (c : X) * d = (c : X) * d * (c : X)⁻¹ * c := by group
      _ = d * c := by rw [h1]
  have hz2 : orderOf (⟨d, hdD⟩ : (D : Subgroup X)) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [pow_two]; exact hd2) hd1'
  have hwc : ∀ g : X, g⁻¹ * d * g ∈ (D : Subgroup X) → g⁻¹ * d * g = d := fun g hg =>
    hfus _ hg (isConj_iff.mpr ⟨g⁻¹, by rw [inv_inv]⟩)
  obtain ⟨hfrat, -⟩ := CFSG.Adapters.glauberman_zStar D ⟨d, hdD⟩ hzZ hz2 hwc
  set O := pPrimeCore 2 X with hO
  have hfrat' : ∀ g : X, ∃ c, c * d = d * c ∧ ∃ k ∈ O, g = c * k := by
    intro g
    obtain ⟨c, hc, k, hk, rfl⟩ := hfrat g
    rw [oddCore_eq_pPrimeCore_two] at hk
    exact ⟨c, (Subgroup.mem_centralizer_singleton_iff.mp hc), k, hk, rfl⟩
  have hnt : ∃ k ∈ O, k * d ≠ d * k := by
    by_contra hall
    push Not at hall
    obtain ⟨g, hg⟩ := hmove
    obtain ⟨c, hc, k, hk, rfl⟩ := hfrat' g
    have hgd : c * k * d = d * (c * k) := by
      rw [mul_assoc, hall k hk, ← mul_assoc, hc, mul_assoc]
    apply hg
    refine B1.tv_comm_centre hdw hd1 ?_
    rw [← map_mul, ← map_mul, hgd]
  set Φ : Subgroup (MulAut V) := O.map ρ with hΦ
  have hΦodd : Odd (Nat.card Φ) := by
    rw [hΦ, Subgroup.card_map_of_injective hρ]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  haveI : Group.IsSolvable Φ := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hΦodd
  have htΦ : ∀ f ∈ Φ, ρ d * f * (ρ d)⁻¹ ∈ Φ := by
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨d * k * d⁻¹, (inferInstance : O.Normal).conj_mem k hk d, by simp [map_mul, map_inv]⟩
  have hntΦ : ∃ f ∈ Φ, f * ρ d ≠ ρ d * f := by
    obtain ⟨k, hk, hkd⟩ := hnt
    exact ⟨ρ k, ⟨k, hk, rfl⟩, fun h => hkd (hρ (by rw [map_mul, map_mul]; exact h))⟩
  obtain ⟨x', hB⟩ := B19.exists_tvBlock hV' hΦodd hdw hd1 htΦ hntΦ
  obtain ⟨y, hyO, rfl⟩ := hB.mem
  have hy3 : y ^ 3 = 1 := hρ (by rw [map_pow, hB.x3, map_one])
  have hy1 : y ≠ 1 := fun h => hB.x1 (by rw [h, map_one])
  have hord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hyinv : d * y * d⁻¹ = y⁻¹ := hρ (by rw [map_mul, map_mul, map_inv, map_inv, hB.inv])
  have hcentral : ∀ k ∈ O, k * y = y * k := fun k hk =>
    hρ (by rw [map_mul, map_mul]; exact hB.central (ρ k) ⟨k, hk, rfl⟩)
  have hinverted : ∀ z ∈ O, d * z * d⁻¹ = z⁻¹ → z ∈ Subgroup.zpowers y := by
    intro z hz hzd
    have h1 : ρ z ∈ Subgroup.zpowers (ρ y) := hB.inverted (ρ z) ⟨z, hz, rfl⟩ (by
      rw [← map_inv, ← map_mul, ← map_mul, hzd, map_inv])
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h1
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, hρ (by rw [map_zpow, hn])⟩
  have hconj : ∀ g : X, g * y * g⁻¹ ∈ Subgroup.zpowers y := by
    intro g
    obtain ⟨c, hc, k, hk, rfl⟩ := hfrat' g
    have e : c * k * y * (c * k)⁻¹ = c * y * c⁻¹ := by
      calc c * k * y * (c * k)⁻¹ = c * (k * y) * k⁻¹ * c⁻¹ := by group
        _ = c * (y * k) * k⁻¹ * c⁻¹ := by rw [hcentral k hk]
        _ = c * y * c⁻¹ := by group
    rw [e]
    apply hinverted _ ((inferInstance : O.Normal).conj_mem y hyO c)
    have hc' : c⁻¹ * d = d * c⁻¹ := by
      calc c⁻¹ * d = c⁻¹ * (d * c) * c⁻¹ := by group
        _ = c⁻¹ * (c * d) * c⁻¹ := by rw [hc]
        _ = d * c⁻¹ := by group
    calc d * (c * y * c⁻¹) * d⁻¹ = c * (d * y * d⁻¹) * c⁻¹ := by
          calc d * (c * y * c⁻¹) * d⁻¹ = (d * c) * y * (c⁻¹ * d⁻¹) := by group
            _ = (c * d) * y * (c⁻¹ * d⁻¹) := by rw [hc]
            _ = (c * d) * y * (c⁻¹ * d) := by rw [hdinv]
            _ = (c * d) * y * (d * c⁻¹) := by rw [hc']
            _ = c * (d * y * d⁻¹) * c⁻¹ := by rw [hdinv]; group
      _ = (c * y * c⁻¹)⁻¹ := by rw [hyinv]; group
  have hnormal : (Subgroup.zpowers y).Normal := by
    refine ⟨fun z hz g => ?_⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have e : g * y ^ n * g⁻¹ = (g * y * g⁻¹) ^ n := by
      rw [← MulAut.conj_apply, ← MulAut.conj_apply, map_zpow]
    rw [e]
    exact Subgroup.zpow_mem _ (hconj g) n
  have hρconj : ∀ g : X, ∀ z ∈ Subgroup.zpowers (ρ y), ρ g * z * (ρ g)⁻¹ ∈ Subgroup.zpowers (ρ y) := by
    intro g z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hconj g)
    have e : ρ g * ρ y ^ n * (ρ g)⁻¹ = (ρ (g * y * g⁻¹)) ^ n := by
      rw [map_mul, map_mul, map_inv, ← MulAut.conj_apply, ← MulAut.conj_apply, map_zpow]
    rw [e, ← hm, map_zpow, ← zpow_mul]
    exact Subgroup.zpow_mem_zpowers _ _
  set Y := Subgroup.zpowers (ρ y) with hYdef
  have hYodd : Odd (Nat.card Y) := by
    rw [hYdef, Nat.card_zpowers, orderOf_injective ρ hρ y, hord]
    decide
  obtain ⟨hsup, hinf⟩ := B1.coprime_decomp hV' hYodd (M := ⊤) (fun _ _ _ _ => trivial)
  rw [top_inf_eq, ← commV_eq_commSub] at hsup hinf
  have hcomm_inv : ∀ g : X, ∀ v ∈ commV Y, ρ g v ∈ commV Y := by
    intro g v hv
    rw [commV_eq_commSub] at hv ⊢
    exact B1.commSub_smul_mem (M := ⊤) (M' := ⊤) (ρ g) (hρconj g)
      (fun _ _ => Subgroup.mem_top _) v hv
  have hfix_inv : ∀ g : X, ∀ v ∈ fixV Y, ρ g v ∈ fixV Y := by
    intro g v hv
    refine B1.fixV_smul_mem (ρ g) (fun z hz => ?_) hv
    have := hρconj g⁻¹ z hz
    rwa [map_inv, inv_inv] at this
  have hcY : Nat.card (commV Y) = 4 := hB.card_comm
  have hwY : w ∈ commV Y := hB.w_mem
  have hw1 : w ≠ 1 := hdw.1
  set x := ρ y with hx
  have hx3 : ∀ v : V, x (x (x v)) = v := by
    intro v
    have h3 : x ^ 3 = 1 := by rw [hx, ← map_pow, hy3, map_one]
    have := congrArg (fun f : MulAut V => f v) h3
    simpa [pow_succ, MulAut.mul_apply] using this
  have hfixY : ∀ v ∈ commV Y, x v = v → v = 1 := by
    intro v hv hxv
    have hvfix : v ∈ fixV Y := fun z hz => B1.zpowers_fix hxv z hz
    have : v ∈ commV Y ⊓ fixV Y := ⟨hv, hvfix⟩
    rw [inf_comm, hinf, Subgroup.mem_bot] at this
    exact this
  have hxw : x w ≠ w := fun h => hw1 (hfixY w hwY h)
  have hxxw : x (x w) ≠ w := fun h => hxw (by
    have := hx3 w
    rw [h] at this
    exact this)
  have hxxw' : x (x w) ≠ x w := fun h => hxw (x.injective h)
  have hxw1 : x w ≠ 1 := fun h => hw1 (by rwa [map_eq_one_iff _ x.injective] at h)
  have hxxw1 : x (x w) ≠ 1 := fun h => hxw1 (by rwa [map_eq_one_iff _ x.injective] at h)
  have hmem_comm : ∀ v ∈ commV Y, v = 1 ∨ v = w ∨ v = x w ∨ v = x (x w) := by
    have hsub : ({1, w, x w, x (x w)} : Set V) ⊆ (commV Y : Set V) := by
      intro v hv
      rcases hv with rfl | rfl | rfl | rfl
      · exact (commV Y).one_mem
      · exact hwY
      · exact hcomm_inv y _ hwY
      · exact hcomm_inv y _ (hcomm_inv y _ hwY)
    have hnc : ({1, w, x w, x (x w)} : Set V).ncard = 4 := by
      rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair hxxw'.symm]
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨hxw.symm, hxxw.symm⟩
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨hw1.symm, hxw1.symm, hxxw1.symm⟩
    have hcY' : (commV Y : Set V).ncard = 4 := by
      rw [← Nat.card_coe_set_eq]
      exact hcY
    have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [hnc, hcY'])
    intro v hv
    have hv' : v ∈ ({1, w, x w, x (x w)} : Set V) := by
      rw [heq]
      exact hv
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hv'
  exact ⟨y, hord, hyO, hyinv, hnormal, hcY, hwY, hmem_comm, hcomm_inv, hfix_inv, hB.fix,
    by rw [inf_comm]; exact hinf, by rw [sup_comm]; exact hsup⟩

end CFSG.CGT.Foote81L6.Normalizer
