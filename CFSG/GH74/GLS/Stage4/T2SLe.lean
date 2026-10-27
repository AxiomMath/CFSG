module

public import CFSG.GH74.GLS.Stage4.T2Ctx
public import CFSG.GH74.GLS.Stage4.T2Omega1
public import CFSG.GH74.GLS.Stage4.T2Steps

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2
  CFSG.GH74.BNPair

section Core

variable {A : Type*} [CommGroup A]

theorem t2SLe_prod_mem {H' : Subgroup A} (hidx : H'.index = 2) {x y : A} (hx : x ∉ H')
    (hy : y ∉ H') : x * y ∈ H' := by
  obtain ⟨c, hc⟩ := Subgroup.index_eq_two_iff.1 hidx
  have hc1 : c ∉ H' := by
    rcases hc 1 with h | h
    · exact absurd H'.one_mem h.2
    · simpa using h.2
  have hxc : x * c ∈ H' := by
    rcases hc x with h | h
    · exact h.1
    · exact absurd h.1 hx
  have hyc : y * c ∈ H' := by
    rcases hc y with h | h
    · exact h.1
    · exact absurd h.1 hy
  have hcc : c * c ∈ H' := by
    rcases hc c with h | h
    · exact h.1
    · exact absurd h.1 hc1
  have : x * y = (x * c) * (y * c) * (c * c)⁻¹ := by
    rw [mul_mul_mul_comm, mul_inv_cancel_right]
  rw [this]
  exact H'.mul_mem (H'.mul_mem hxc hyc) (H'.inv_mem hcc)

variable [Finite A]

theorem t2SLe_core (φ : A ≃* A) {z u : A} (H' : Subgroup A)
    (hz1 : z ≠ 1) (hu1 : u ≠ 1) (hzu : z ≠ u)
    (hΩ : ∀ x : A, x * x = 1 → x = 1 ∨ x = z ∨ x = u ∨ x = z * u)
    (hφ3 : ∀ x, φ (φ (φ x)) = x) (hφz : φ z = z * u) (hφu : φ u = z)
    (hidx : H'.index = 2) (h1 : ∀ x ∈ H', φ x ∈ H') (h2 : ∀ x, φ x ∈ H' → x ∈ H') : False := by
  have hsq : ∀ x : A, x * x ∈ H' := by
    intro x
    by_cases hx : x ∈ H'
    · exact H'.mul_mem hx hx
    · exact t2SLe_prod_mem hidx hx hx
  have hφ1 : ∀ x : A, x⁻¹ * φ x ∈ H' := by
    intro x
    by_cases hx : x ∈ H'
    · exact H'.mul_mem (H'.inv_mem hx) (h1 x hx)
    · have hφx : φ x ∉ H' := fun h => hx (h2 x h)
      exact t2SLe_prod_mem hidx (fun h => hx (by simpa using H'.inv_mem h)) hφx
  have hφ2 : ∀ x : A, x⁻¹ * φ (φ x) ∈ H' := by
    intro x
    have : x⁻¹ * φ (φ x) = (x⁻¹ * φ x) * ((φ x)⁻¹ * φ (φ x)) := by group
    rw [this]
    exact H'.mul_mem (hφ1 x) (hφ1 (φ x))
  have hfix : ∀ x : A, φ (x * φ x * φ (φ x)) = x * φ x * φ (φ x) := by
    intro x
    rw [map_mul, map_mul, hφ3 x, mul_comm (φ x * φ (φ x)) x, mul_assoc]
  have hzφ : φ z ≠ z := by
    intro h
    rw [hφz] at h
    exact hu1 (mul_eq_left.1 h)
  have huφ : φ u ≠ u := by
    intro h
    rw [hφu] at h
    exact hzu h
  have hzuφ : φ (z * u) ≠ z * u := by
    intro h
    rw [map_mul, hφz, hφu] at h
    have h' : z * u * z = z * u * 1 := by rw [mul_one]; exact h
    exact hz1 (mul_left_cancel h')
  have hodd : ∀ x : A, Odd (orderOf (x * φ x * φ (φ x))) := by
    intro x
    set y := x * φ x * φ (φ x) with hy
    by_contra hnodd
    have hev : Even (orderOf y) := Nat.not_odd_iff_even.1 hnodd
    obtain ⟨k, hk⟩ := hev
    have hpos : 0 < orderOf y := orderOf_pos y
    have hk0 : k ≠ 0 := by omega
    have hklt : k < orderOf y := by omega
    have hw1 : y ^ k ≠ 1 := pow_ne_one_of_lt_orderOf hk0 hklt
    have hw2 : y ^ k * y ^ k = 1 := by
      rw [← pow_add, ← hk]
      exact pow_orderOf_eq_one y
    have hφw : φ (y ^ k) = y ^ k := by rw [map_pow, hfix x]
    rcases hΩ _ hw2 with h | h | h | h
    · exact hw1 h
    · rw [h] at hφw; exact hzφ hφw
    · rw [h] at hφw; exact huφ hφw
    · rw [h] at hφw; exact hzuφ hφw
  have hNmem : ∀ x : A, x * φ x * φ (φ x) ∈ H' := by
    intro x
    obtain ⟨j, hj⟩ := hodd x
    set y := x * φ x * φ (φ x) with hy
    have hyj : y ^ (2 * j + 1) = 1 := by rw [← hj]; exact pow_orderOf_eq_one y
    have : y = y ^ (j + 1) * y ^ (j + 1) := by
      rw [← pow_add]
      have h3 : j + 1 + (j + 1) = (2 * j + 1) + 1 := by ring
      rw [h3, pow_succ, hyj, one_mul]
    rw [this]
    exact hsq _
  have hall : ∀ x : A, x ∈ H' := by
    intro x
    obtain ⟨c₁, hc₁⟩ : ∃ c₁ ∈ H', φ x = x * c₁ := ⟨x⁻¹ * φ x, hφ1 x, by simp⟩
    obtain ⟨c₂, hc₂⟩ : ∃ c₂ ∈ H', φ (φ x) = x * c₂ := ⟨x⁻¹ * φ (φ x), hφ2 x, by simp⟩
    have hN := hNmem x
    rw [hc₂.2, hc₁.2] at hN
    have hxe : x = (x * (x * c₁) * (x * c₂)) * (x * x * c₁ * c₂)⁻¹ := by
      refine eq_mul_inv_of_mul_eq ?_
      ac_rfl
    rw [hxe]
    exact H'.mul_mem hN (H'.inv_mem (H'.mul_mem (H'.mul_mem (hsq x) hc₁.1) hc₂.1))
  have : H' = ⊤ := eq_top_iff.2 fun x _ => hall x
  rw [this, Subgroup.index_top] at hidx
  omega

end Core

section InG

variable {G : Type} [Group G] [Finite G]

theorem t2SLe_noInvIdx {H H' : Subgroup G} {z u a : G}
    (hHc : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) (hzH : z ∈ H) (huH : u ∈ H)
    (hz1 : z ≠ 1) (hu1 : u ≠ 1) (hzu : z ≠ u)
    (hΩ : ∀ x ∈ H, x * x = 1 → x = 1 ∨ x = z ∨ x = u ∨ x = z * u)
    (haH : ∀ h ∈ H, a * h * a⁻¹ ∈ H) (haH' : ∀ h ∈ H, a⁻¹ * h * a ∈ H) (ha3 : a ^ 3 ∈ H)
    (haz : a * z * a⁻¹ = z * u) (hau : a * u * a⁻¹ = z)
    (hidx : H'.relIndex H = 2)
    (h1 : ∀ h ∈ H', a * h * a⁻¹ ∈ H') (h2 : ∀ h ∈ H, a * h * a⁻¹ ∈ H' → h ∈ H') : False := by
  let _ : CommGroup ↥H :=
    { (inferInstance : Group ↥H) with mul_comm := fun x y => Subtype.ext (hHc x x.2 y y.2) }
  let φ : ↥H ≃* ↥H :=
    { toFun := fun x => ⟨a * x * a⁻¹, haH x x.2⟩
      invFun := fun x => ⟨a⁻¹ * x * a, haH' x x.2⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hφ3 : ∀ x : ↥H, φ (φ (φ x)) = x := by
    intro x
    apply Subtype.ext
    have ha3' : a * (a * a) ∈ H := by
      have : a * (a * a) = a ^ 3 := by simp [pow_succ, mul_assoc]
      rw [this]; exact ha3
    have hc : a * (a * a) * (x : G) = (x : G) * (a * (a * a)) := hHc _ ha3' _ x.2
    calc a * (a * (a * (x : G) * a⁻¹) * a⁻¹) * a⁻¹
        = a * (a * a) * (x : G) * (a * (a * a))⁻¹ := by group
      _ = (x : G) * (a * (a * a)) * (a * (a * a))⁻¹ := by rw [hc]
      _ = x := by group
  refine t2SLe_core φ (H'.subgroupOf H) (z := ⟨z, hzH⟩) (u := ⟨u, huH⟩)
    (fun h => hz1 (congrArg Subtype.val h)) (fun h => hu1 (congrArg Subtype.val h))
    (fun h => hzu (congrArg Subtype.val h)) ?_ hφ3 (Subtype.ext haz) (Subtype.ext hau) hidx ?_ ?_
  · intro x hx
    have hx' : (x : G) * x = 1 := by simpa using congrArg Subtype.val hx
    rcases hΩ x x.2 hx' with h | h | h | h
    · left; exact Subtype.ext h
    · right; left; exact Subtype.ext h
    · right; right; left; exact Subtype.ext h
    · right; right; right; exact Subtype.ext h
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact h1 _ hx
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact h2 _ x.2 hx

end InG

section Main

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem t2SLe_relIndex_two {K L M : Subgroup G} (hKL : K ≤ L) (hLM : L ≤ M)
    (h2 : K.relIndex M = 2) (hne : ¬ M ≤ L) : L.relIndex M = 2 := by
  have hmul := Subgroup.relIndex_mul_relIndex K L M hKL hLM
  have h1 : L.relIndex M ≠ 1 := fun h => hne (Subgroup.relIndex_eq_one.1 h)
  have hdvd : L.relIndex M ∣ 2 := by rw [← h2, ← hmul]; exact Dvd.intro_left _ rfl
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
  · exact absurd h h1
  · exact h

omit [Finite G] in
theorem t2SLe_M_conj {Nsub K : Subgroup G} {m : G} (hm : m ∈ Nsub) {x : G}
    (hx : x ∈ ⨆ n ∈ Nsub, conjBy n K) : m * x * m⁻¹ ∈ ⨆ n ∈ Nsub, conjBy n K := by
  have key : (⨆ n ∈ Nsub, conjBy n K) ≤
      (⨆ n ∈ Nsub, conjBy n K).comap (MulAut.conj m).toMonoidHom := by
    refine iSup₂_le fun n hn y hy => ?_
    rw [mem_conjBy_iff] at hy
    have h : m * y * m⁻¹ ∈ conjBy (n * m⁻¹) K := by
      rw [mem_conjBy_iff]
      have : n * m⁻¹ * (m * y * m⁻¹) * (n * m⁻¹)⁻¹ = n * y * n⁻¹ := by group
      rw [this]; exact hy
    exact le_iSup₂ (f := fun (n : G) (_ : n ∈ Nsub) => conjBy n K) (n * m⁻¹)
      (Nsub.mul_mem hn (Nsub.inv_mem hm)) h
  have := key hx
  simpa using this

omit [Finite G] in
theorem t2SLe_le_M {Nsub K : Subgroup G} : K ≤ ⨆ n ∈ Nsub, conjBy n K :=
  le_iSup₂_of_le (f := fun (n : G) (_ : n ∈ Nsub) => conjBy n K) (1 : G) Nsub.one_mem
    (BNPair.conjBy_one K).symm.le

end Main

theorem ch6T2SLe : Ch6T2SLe := by
  intro G _ _ hr Gs _ q₁ q₂ z K₁ K₂ F₁ F₂ _ _ t hSet hRem N u hz hK₁ hK₂ hq₁ hq₂ hLoc hCoord hF hW
  have ctx := t2Ctx_of hSet hRem hLoc hz hK₁ hK₂ hq₁ hq₂
  obtain ⟨hw₀sq, hw₀H, -⟩ := t2Ctx_Y1 hSet hRem hLoc hz hK₁ hK₂ hq₁ hq₂
  have hindex := hSet.index_two
  subst hz hK₁ hK₂ hq₁ hq₂
  have hz2 : N.z * N.z = 1 := ctx.zz
  have hz : N.z⁻¹ = N.z := inv_eq_of_mul_eq_one_right hz2
  have haH : ∀ h ∈ N.H, N.a * h * N.a⁻¹ ∈ N.H := fun h hh =>
    (Subgroup.mem_normalizer_iff.1 hW.a_normH h).1 hh
  have haH' : ∀ h ∈ N.H, N.a⁻¹ * h * N.a ∈ N.H := fun h hh => by
    simpa using (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hW.a_normH) h).1 hh
  obtain ⟨u', hu'⟩ : ∃ u' : G, u' = N.a⁻¹ * N.z * N.a := ⟨_, rfl⟩
  have hcyc : N.a⁻¹ * u' * N.a = N.z * u' := by rw [hu']; exact hW.a_cycle
  have hu'H : u' ∈ N.H := by rw [hu']; exact haH' N.z hLoc.z_mem_H
  have hu'2 : u' * u' = 1 := by
    calc u' * u' = N.a⁻¹ * (N.z * N.z) * N.a := by rw [hu']; group
      _ = 1 := by rw [hz2]; group
  have hu'1 : u' ≠ 1 := by
    intro h
    apply ctx.z_ne
    calc N.z = N.a * (N.a⁻¹ * N.z * N.a) * N.a⁻¹ := by group
      _ = 1 := by rw [← hu', h]; group
  have hzu'ne : N.z ≠ u' := by
    intro h
    apply ctx.z_ne
    have e1 : N.a⁻¹ * N.z * N.a = N.z := by rw [← hu']; exact h.symm
    rw [← h] at hcyc
    calc N.z = N.a⁻¹ * N.z * N.a := e1.symm
      _ = N.z * N.z := hcyc
      _ = 1 := hz2
  have hau' : N.a * u' * N.a⁻¹ = N.z := by rw [hu']; group
  have haz' : N.a * N.z * N.a⁻¹ = N.z * u' := by
    have e : (N.a * N.z * N.a⁻¹) * N.z = u' := by
      calc (N.a * N.z * N.a⁻¹) * N.z = (N.a * N.z * N.a⁻¹) * (N.a * u' * N.a⁻¹) := by rw [hau']
        _ = N.a * (N.z * u') * N.a⁻¹ := by group
        _ = N.a * (N.a⁻¹ * u' * N.a) * N.a⁻¹ := by rw [hcyc]
        _ = u' := by group
    calc N.a * N.z * N.a⁻¹ = ((N.a * N.z * N.a⁻¹) * N.z) * N.z⁻¹ := by group
      _ = u' * N.z := by rw [e, hz]
      _ = N.z * u' := hLoc.H_comm u' hu'H N.z hLoc.z_mem_H
  have hΩ := t2_omega1_zu hr hLoc.H_comm hLoc.z_mem_H hu'H hz2 hu'2 ctx.z_ne hu'1 hzu'ne hw₀sq hw₀H
    hLoc.w₀_inv
  set M : Subgroup G := ⨆ n ∈ N.Nsub, conjBy n (N.K₁ ⊔ N.K₂) with hM
  have hKM : N.K₁ ⊔ N.K₂ ≤ M := t2SLe_le_M
  have hHM : N.H ≤ M := by
    by_contra hnot
    have hHt : (N.H ⊓ N.K₁) ⊔ (N.H ⊓ N.K₂) ≤ N.H ⊓ M :=
      sup_le (le_inf inf_le_left (inf_le_right.trans (le_sup_left.trans hKM)))
        (le_inf inf_le_left (inf_le_right.trans (le_sup_right.trans hKM)))
    have hidx' : (N.H ⊓ M).relIndex N.H = 2 :=
      t2SLe_relIndex_two hHt inf_le_left hLoc.H_idx (fun h => hnot (h.trans inf_le_right))
    refine t2SLe_noInvIdx hLoc.H_comm hLoc.z_mem_H hu'H ctx.z_ne hu'1 hzu'ne hΩ haH haH' hW.a_cube
      haz' hau' hidx' (fun h hh => ⟨haH h hh.1, t2SLe_M_conj hW.a_mem_N hh.2⟩)
      (fun h hh hmem => ⟨hh, ?_⟩)
    have := t2SLe_M_conj (N.Nsub.inv_mem hW.a_mem_N) hmem.2
    simpa [mul_assoc] using this
  have hKS : (N.K₁ ⊔ N.K₂).relIndex (N.K₁ ⊔ N.K₂ ⊔ N.S) = 2 := by
    rw [ctx.KS]; exact hindex
  have hEq : N.K₁ ⊔ N.K₂ ⊔ N.H = N.K₁ ⊔ N.K₂ ⊔ N.S :=
    sup_eq_of_relIndex_two le_sup_left (sup_le le_sup_left hLoc.H_le) hKS
      (fun h => hLoc.H_not_le_K (le_sup_right.trans h))
  calc N.S ≤ N.K₁ ⊔ N.K₂ ⊔ N.S := le_sup_right
    _ = N.K₁ ⊔ N.K₂ ⊔ N.H := hEq.symm
    _ ≤ M := sup_le hKM hHM

end CFSG.GH74.GLS.Stage4.Rest
