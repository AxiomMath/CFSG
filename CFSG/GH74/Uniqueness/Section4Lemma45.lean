module

public import CFSG.GH74.Uniqueness.Section4Basic
public import CFSG.GH74.Uniqueness.Section4Data
public import CFSG.GH74.Uniqueness.Section4Lift
public import CFSG.GH74.Uniqueness.Section4Bender

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

section Quotient

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

omit [Finite X] in
theorem mem_map_mk'_iff {N : Subgroup X} [N.Normal] (hNM : N ≤ M) {x : X} :
    QuotientGroup.mk' N x ∈ M.map (QuotientGroup.mk' N) ↔ x ∈ M := by
  constructor
  · rintro ⟨m, hm, hmx⟩
    have : m⁻¹ * x ∈ N := by
      have h := (QuotientGroup.eq (a := m) (b := x)).mp hmx
      exact h
    have h2 : x = m * (m⁻¹ * x) := by group
    rw [h2]
    exact M.mul_mem hm (hNM this)
  · intro hx
    exact ⟨x, hx, rfl⟩

omit [Finite X] in
theorem IsInvariantInvolutionSet.map_mk' (hZ : IsInvariantInvolutionSet Z) (N : Subgroup X)
    [N.Normal] (hZN : ∀ z ∈ Z, z ∉ N) :
    IsInvariantInvolutionSet ((QuotientGroup.mk' N) '' Z) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    have hz2 : z * z = 1 := hZ.mul_self_eq_one hz
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two, ← map_mul, hz2, map_one]
    · intro h1
      exact hZN z hz ((QuotientGroup.eq_one_iff z).mp h1)
  · rintro _ ⟨z, hz, rfl⟩ g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N g
    exact ⟨g⁻¹ * z * g, hZ.2 z hz g, by simp⟩

omit [Finite X] in
theorem closure_image_mk' (N : Subgroup X) [N.Normal] (hgen : Subgroup.closure Z = ⊤) :
    Subgroup.closure ((QuotientGroup.mk' N) '' Z) = ⊤ := by
  rw [← MonoidHom.map_closure, hgen, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]

end Quotient


section QuotientPD

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.isProductDisconnected_quot (S : ZDSetup X Z M) {N : Subgroup X} [N.Normal]
    (hNM : N ≤ M)
    (hlift : ∀ x ∈ Z, ∀ y ∈ Z, x * y * x⁻¹ * y⁻¹ ∈ N →
      ∃ x' ∈ Z, ∃ y' ∈ Z, x'⁻¹ * x ∈ N ∧ y'⁻¹ * y ∈ N ∧ x' * y' = y' * x') :
    IsProductDisconnected ((QuotientGroup.mk' N) '' Z) (M.map (QuotientGroup.mk' N)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro htop
    apply S.prodDisc.ne_top
    rw [eq_top_iff]
    intro x _
    have : QuotientGroup.mk' N x ∈ M.map (QuotientGroup.mk' N) := htop ▸ Subgroup.mem_top _
    exact (mem_map_mk'_iff hNM).mp this
  · obtain ⟨z, hz, hzM⟩ := S.exists_mem_inter
    exact ⟨QuotientGroup.mk' N z, ⟨z, hz, rfl⟩, Subgroup.mem_map_of_mem _ hzM⟩
  · rintro _ ⟨z, hz, rfl⟩ hzM gb
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N gb
    have hzM' := (mem_map_mk'_iff hNM).mp hzM
    have e : (QuotientGroup.mk' N g)⁻¹ * QuotientGroup.mk' N z * QuotientGroup.mk' N g =
        QuotientGroup.mk' N (g⁻¹ * z * g) := by simp
    rw [e, mem_map_mk'_iff hNM, mem_map_mk'_iff hNM]
    exact S.prodDisc.2.2.1 z hz hzM' g
  · rintro _ hub hubM tb htb
    obtain ⟨hord, _, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, hxy, rfl⟩ := hub
    obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective N tb
    have hcomm : x * y * x⁻¹ * y⁻¹ ∈ N := by
      have h1 : QuotientGroup.mk' N (x * y * x⁻¹ * y⁻¹) = 1 := by
        simp only [map_mul, map_inv]
        rw [hxy]
        group
      exact (QuotientGroup.eq_one_iff _).mp h1
    obtain ⟨x', hx', y', hy', hxx, hyy, hx'y'⟩ := hlift x hx y hy hcomm
    have hmx : QuotientGroup.mk' N x' = QuotientGroup.mk' N x := (QuotientGroup.eq).mpr hxx
    have hmy : QuotientGroup.mk' N y' = QuotientGroup.mk' N y := (QuotientGroup.eq).mpr hyy
    have hmu : QuotientGroup.mk' N (x' * y') = QuotientGroup.mk' N x * QuotientGroup.mk' N y := by
      rw [map_mul, hmx, hmy]
    have hx2 := S.invariant.mul_self_eq_one hx'
    have hy2 := S.invariant.mul_self_eq_one hy'
    have hu2 : (x' * y') * (x' * y') = 1 := by
      calc (x' * y') * (x' * y') = x' * (y' * x') * y' := by group
        _ = x' * (x' * y') * y' := by rw [hx'y']
        _ = (x' * x') * (y' * y') := by group
        _ = 1 := by rw [hx2, hy2, one_mul]
    have hu1 : x' * y' ≠ 1 := by
      intro h1
      rw [h1, map_one] at hmu
      rw [← hmu] at hord
      simp at hord
    have hordu : orderOf (x' * y') = 2 := orderOf_eq_prime (by rwa [pow_two]) hu1
    have huM : x' * y' ∈ M := by
      have : QuotientGroup.mk' N (x' * y') ∈ M.map (QuotientGroup.mk' N) := by
        rw [hmu]; exact hubM
      exact (mem_map_mk'_iff hNM).mp this
    have hu𝒱 : x' * y' ∈ productInvolutions Z := ⟨hordu, x', hx', y', hy', hx'y', rfl⟩
    have hU := (mem_uniqU_iff 2).mp (S.mem_uniqU_of_mem_productInvolutions hu𝒱 huM)
    rw [Subgroup.mem_centralizer_singleton_iff] at htb
    rw [← hmu] at htb
    have hN : (x' * y')⁻¹ * t⁻¹ * (x' * y') * t ∈ N := by
      apply (QuotientGroup.eq_one_iff _).mp
      show QuotientGroup.mk' N ((x' * y')⁻¹ * t⁻¹ * (x' * y') * t) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      generalize QuotientGroup.mk' N (x' * y') = a at htb ⊢
      generalize QuotientGroup.mk' N t = b at htb ⊢
      calc a⁻¹ * b⁻¹ * a * b = a⁻¹ * b⁻¹ * (a * b) := by group
        _ = a⁻¹ * b⁻¹ * (b * a) := by rw [htb]
        _ = 1 := by group
    have hconj : t⁻¹ * (x' * y') * t ∈ M := by
      have e : t⁻¹ * (x' * y') * t = (x' * y') * ((x' * y')⁻¹ * t⁻¹ * (x' * y') * t) := by group
      rw [e]
      exact M.mul_mem huM (hNM hN)
    exact (mem_map_mk'_iff hNM).mpr (hU.2.2 t hconj) |> fun h => by simpa using h
    
end QuotientPD


section Lift

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

omit [Finite X] in
theorem map_commutator_of_surjective {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (hf : Function.Surjective f) : (commutator G).map f = commutator G' := by
  rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective f hf,
    ← commutator_def]

theorem ZDSetup.hlift_odd (S : ZDSetup X Z M) {N : Subgroup X} [N.Normal] (hN : Odd (Nat.card N)) :
    ∀ x ∈ Z, ∀ y ∈ Z, x * y * x⁻¹ * y⁻¹ ∈ N →
      ∃ x' ∈ Z, ∃ y' ∈ Z, x'⁻¹ * x ∈ N ∧ y'⁻¹ * y ∈ N ∧ x' * y' = y' * x' := by
  intro x hx y hy hxy
  have hnorm : ∀ g : X, g ∈ normalizer (N : Set X) := fun g => by
    rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top g
  obtain ⟨b, hb, hcomm⟩ := exists_commuting_involution_conj hN (S.invariant.mul_self_eq_one hx)
    (S.invariant.1 y hy) (hnorm x) (hnorm y) hxy
  refine ⟨x, hx, b⁻¹ * y * b, S.invariant.2 y hy b, by simp [N.one_mem], ?_, hcomm⟩
  have e : (b⁻¹ * y * b)⁻¹ * y = b⁻¹ * (y⁻¹ * b * y) := by group
  rw [e]
  exact N.mul_mem (N.inv_mem hb) (by simpa using (Subgroup.Normal.conj_mem inferInstance b hb y⁻¹))

theorem exists_involution_lift {N : Subgroup X} [N.Normal] (hN : Odd (Nat.card N))
    {ub : X ⧸ N} (hu : ub * ub = 1) : ∃ u : X, u * u = 1 ∧ QuotientGroup.mk' N u = ub := by
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective N ub
  by_cases hc : c ∈ N
  · refine ⟨1, mul_one 1, ?_⟩
    rw [map_one]
    exact ((QuotientGroup.eq_one_iff c).mpr hc).symm
  · have hc2 : c * c ∈ N := by
      apply (QuotientGroup.eq_one_iff _).mp
      show QuotientGroup.mk' N (c * c) = 1
      rw [map_mul]; exact hu
    obtain ⟨y, hy, hyord, hyc⟩ := exists_involution_mem_zpowers_coset hN hc2 hc
    refine ⟨y, ?_, ?_⟩
    · have := pow_orderOf_eq_one y
      rwa [hyord, pow_two] at this
    · have : QuotientGroup.mk' N (y * c⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr hyc
      rw [map_mul, map_inv] at this
      exact mul_inv_eq_one.mp this

end Lift


section LiftData

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

omit [Finite X] in
theorem mem_of_sq_eq_one_of_mul {N T : Subgroup X} [T.Normal] (hN : Odd (Nat.card N)) {z : X}
    (hz : z * z = 1) {t n : X} (ht : t ∈ T) (hn : n ∈ N) (hzt : z = t * n) : z ∈ T := by
  have hfin : Finite N := Nat.finite_of_card_ne_zero (by rintro h; rw [h] at hN; exact absurd hN (by decide))
  have hg : QuotientGroup.mk' T z = QuotientGroup.mk' T n := by
    have h1t : QuotientGroup.mk' T t = 1 := (QuotientGroup.eq_one_iff t).mpr ht
    rw [hzt, map_mul, h1t, one_mul]
  have h2 : QuotientGroup.mk' T n * QuotientGroup.mk' T n = 1 := by
    rw [← hg, ← map_mul, hz, map_one]
  have hodd : Odd (orderOf (QuotientGroup.mk' T n)) := by
    refine Odd.of_dvd_nat hN ?_
    refine (orderOf_map_dvd (QuotientGroup.mk' T) n).trans ?_
    have := orderOf_dvd_natCard (⟨n, hn⟩ : N)
    rwa [Subgroup.orderOf_mk] at this
  have h1 : QuotientGroup.mk' T n = 1 := by
    have hd : orderOf (QuotientGroup.mk' T n) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at hodd; exact absurd hodd (by decide)
  exact (QuotientGroup.eq_one_iff z).mp (hg.trans h1)

end LiftData


section FD

variable {X : Type} [Group X]

@[expose] def commutatorQuotHom (N : Subgroup X) [N.Normal] :
    ↥(commutator X) →* ↥(commutator (X ⧸ N)) :=
  ((QuotientGroup.mk' N).comp (commutator X).subtype).codRestrict (commutator (X ⧸ N))
    (fun d => by
      rw [← map_commutator_of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)]
      exact Subgroup.mem_map_of_mem _ d.2)

theorem commutatorQuotHom_apply (N : Subgroup X) [N.Normal] (d : ↥(commutator X)) :
    ((commutatorQuotHom N d : ↥(commutator (X ⧸ N))) : X ⧸ N) = QuotientGroup.mk' N d := rfl

theorem commutatorQuotHom_surjective (N : Subgroup X) [N.Normal] :
    Function.Surjective (commutatorQuotHom N) := by
  rintro ⟨x, hx⟩
  rw [← map_commutator_of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)] at hx
  obtain ⟨d, hd, rfl⟩ := hx
  exact ⟨⟨d, hd⟩, rfl⟩

theorem ker_commutatorQuotHom (N : Subgroup X) [N.Normal] :
    (commutatorQuotHom N).ker = N.subgroupOf (commutator X) := by
  ext d
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    have h1 : QuotientGroup.mk' N (d : X) = 1 := by
      have := congrArg (fun y : ↥(commutator (X ⧸ N)) => (y : X ⧸ N)) h
      simpa [commutatorQuotHom_apply] using this
    exact (QuotientGroup.eq_one_iff _).mp h1
  · intro h
    apply Subtype.ext
    rw [commutatorQuotHom_apply]
    exact (QuotientGroup.eq_one_iff _).mpr h

theorem map_subgroupOf_commutatorQuotHom {M : Subgroup X} {N : Subgroup X} [N.Normal] (hNM : N ≤ M) :
    (M.subgroupOf (commutator X)).map (commutatorQuotHom N) =
      (M.map (QuotientGroup.mk' N)).subgroupOf (commutator (X ⧸ N)) := by
  ext xb
  constructor
  · rintro ⟨d, hd, rfl⟩
    rw [Subgroup.mem_subgroupOf, commutatorQuotHom_apply]
    exact Subgroup.mem_map_of_mem _ hd
  · intro hx
    obtain ⟨d, hd⟩ := commutatorQuotHom_surjective N xb
    refine ⟨d, ?_, hd⟩
    show (d : X) ∈ M
    have hx' : ((commutatorQuotHom N d : ↥(commutator (X ⧸ N))) : X ⧸ N) ∈
        M.map (QuotientGroup.mk' N) := by rw [hd]; exact hx
    rw [commutatorQuotHom_apply] at hx'
    exact (mem_map_mk'_iff hNM).mp hx'

theorem exists_hom_comp_quot {M N : Subgroup X} [N.Normal] (hNM : N ≤ M) {K : Type} [Group K]
    (φ' : ↥(commutator (X ⧸ N)) →* K) (hs : Function.Surjective φ') (hk : φ'.ker = ⊥)
    {S' : Subgroup K} (hS' : ((M.map (QuotientGroup.mk' N)).subgroupOf (commutator (X ⧸ N))).map φ' = S') :
    ∃ φ : ↥(commutator X) →* K, Function.Surjective φ ∧ φ.ker = N.subgroupOf (commutator X) ∧
      (M.subgroupOf (commutator X)).map φ = S' := by
  refine ⟨φ'.comp (commutatorQuotHom N), hs.comp (commutatorQuotHom_surjective N), ?_, ?_⟩
  · rw [← MonoidHom.comap_ker, hk, MonoidHom.comap_bot, ker_commutatorQuotHom]
  · rw [← Subgroup.map_map, map_subgroupOf_commutatorQuotHom hNM, hS']

end FD


section LiftData2

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

omit [Finite X] in
theorem eq_one_of_mem_of_sq_eq_one {N : Subgroup X} (hN : Odd (Nat.card N)) {y : X} (hy : y ∈ N)
    (hy2 : y * y = 1) : y = 1 := by
  have hfin : Finite N := Nat.finite_of_card_ne_zero
    (by rintro h; rw [h] at hN; exact absurd hN (by decide))
  have hodd : Odd (orderOf y) := by
    refine Odd.of_dvd_nat hN ?_
    have := orderOf_dvd_natCard (⟨y, hy⟩ : N)
    rwa [Subgroup.orderOf_mk] at this
  have hd : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hy2)
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at hodd; exact absurd hodd (by decide)

omit [Finite X] in
theorem zpow_involution_mul_self {u : X} (hu : u * u = 1) (k : ℤ) : u ^ k * u ^ k = 1 := by
  rw [← zpow_add, ← two_mul, zpow_mul]
  have : u ^ (2 : ℤ) = 1 := by rw [zpow_two, hu]
  rw [this, one_zpow]

theorem ZDSetup.zdData_of_quot (S : ZDSetup X Z M) {N : Subgroup X} [N.Normal]
    (hkerO : N = pPrimeCore 2 X) (hNM : N ≤ M) {ub : X ⧸ N}
    (h : ZDData (X ⧸ N) ((QuotientGroup.mk' N) '' Z) (M.map (QuotientGroup.mk' N)) ub) :
    ∃ u, ZDData X Z M u := by
  have hNodd : Odd (Nat.card N) := by
    rw [hkerO]
    exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := X))
  have hbot : pPrimeCore 2 (X ⧸ N) = ⊥ := by
    subst hkerO
    exact pPrimeCore_quotient_pPrimeCore X
  have hub2 : ub * ub = 1 := by have := h.sq; rwa [pow_two] at this
  obtain ⟨u, hu2, hfu⟩ := exists_involution_lift hNodd hub2
  have huM : u ∈ M := (mem_map_mk'_iff hNM).mp (hfu ▸ h.mem)
  have hDmap : (commutator X).map (QuotientGroup.mk' N) = commutator (X ⧸ N) :=
    map_commutator_of_surjective _ (QuotientGroup.mk'_surjective N)
  have hzdec : ∀ z ∈ Z, ∃ d ∈ commutator X, ∃ n ∈ N, z = u * d * n := by
    intro z hz
    obtain ⟨⟨db, hdb, hzd⟩, -⟩ := h.zset (QuotientGroup.mk' N z) ⟨z, hz, rfl⟩
    rw [← hDmap] at hdb
    obtain ⟨d, hd, rfl⟩ := hdb
    refine ⟨d, hd, (u * d)⁻¹ * z, ?_, by group⟩
    apply (QuotientGroup.eq_one_iff _).mp
    show QuotientGroup.mk' N ((u * d)⁻¹ * z) = 1
    rw [map_mul, map_inv, map_mul, hfu, ← hzd]
    group
  have hTnormal : (commutator X ⊔ zpowers u).Normal :=
    Subgroup.Normal.of_commutator_le X le_sup_left
  have hsup : commutator X ⊔ zpowers u = ⊤ := by
    rw [eq_top_iff, ← S.gen, Subgroup.closure_le]
    intro z hz
    obtain ⟨d, hd, n, hn, hzn⟩ := hzdec z hz
    have hud : u * d ∈ commutator X ⊔ zpowers u :=
      (commutator X ⊔ zpowers u).mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers u))
        (Subgroup.mem_sup_left hd)
    exact mem_of_sq_eq_one_of_mul hNodd (S.invariant.mul_self_eq_one hz) hud hn hzn
  have hkey : ∀ k : ℤ, QuotientGroup.mk' N (u ^ k) ∈ commutator (X ⧸ N) → u ^ k = 1 := by
    intro k hk
    have h2 : QuotientGroup.mk' N (u ^ k) ∈ commutator (X ⧸ N) ⊓ zpowers ub :=
      ⟨hk, by rw [map_zpow, hfu]; exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers ub) _⟩
    rw [h.inf, Subgroup.mem_bot] at h2
    exact eq_one_of_mem_of_sq_eq_one hNodd ((QuotientGroup.eq_one_iff _).mp h2)
      (zpow_involution_mul_self hu2 k)
  have hND : N ≤ commutator X := by
    intro n hn
    have hn' : n ∈ commutator X ⊔ zpowers u := hsup ▸ Subgroup.mem_top n
    obtain ⟨d, hd, w, hw, hdw⟩ := Subgroup.mem_sup_of_normal_left.mp hn'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have h1 : QuotientGroup.mk' N (u ^ k) = (QuotientGroup.mk' N d)⁻¹ := by
      have : QuotientGroup.mk' N d * QuotientGroup.mk' N (u ^ k) = 1 := by
        rw [← map_mul, hdw]
        exact (QuotientGroup.eq_one_iff n).mpr hn
      exact eq_inv_of_mul_eq_one_right this
    have h4 : u ^ k = 1 := hkey k (by
      rw [h1]
      exact (commutator (X ⧸ N)).inv_mem (hDmap ▸ Subgroup.mem_map_of_mem _ hd))
    rw [h4, mul_one] at hdw
    rw [← hdw]
    exact hd
  have hinf : commutator X ⊓ zpowers u = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyD, hyu⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hyu
    rw [hkey k (hDmap ▸ Subgroup.mem_map_of_mem _ hyD)]
    exact Subgroup.one_mem _
  have hcomm : ⁅zpowers u, commutator X⁆ ≤ N := by
    have h1 : (⁅zpowers u, commutator X⁆).map (QuotientGroup.mk' N) ≤ ⊥ := by
      rw [Subgroup.map_commutator, MonoidHom.map_zpowers, hDmap, hfu]
      exact h.comm.trans hbot.le
    intro x hx
    have := h1 (Subgroup.mem_map_of_mem _ hx)
    rw [Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff x).mp this
  obtain ⟨K, _, φ', hφ's, hφ'k, hKB, S', hS'⟩ := h.bar
  have hk' : φ'.ker = ⊥ := by rw [hφ'k, hbot, Subgroup.bot_subgroupOf]
  obtain ⟨φ, hφs, hφk, hφS⟩ := exists_hom_comp_quot hNM φ' hφ's hk' hS'
  refine ⟨u, ⟨huM, by rw [pow_two]; exact hu2, hsup, hinf, hkerO ▸ hcomm, hkerO ▸ hND,
    hkerO ▸ hNM, ⟨K, inferInstance, φ, hφs, hkerO ▸ hφk, hKB, S', hφS⟩, ?_⟩⟩
  intro z hz
  obtain ⟨d, hd, n, hn, hzn⟩ := hzdec z hz
  refine ⟨⟨d * n, (commutator X).mul_mem hd (hND hn), by rw [hzn]; group⟩, fun o ho hzo => ?_⟩
  obtain ⟨-, hne⟩ := h.zset (QuotientGroup.mk' N z) ⟨z, hz, rfl⟩
  apply hne 1 (by rw [hbot]; exact Subgroup.one_mem _)
  have ho1 : QuotientGroup.mk' N o = 1 := (QuotientGroup.eq_one_iff o).mpr (hkerO ▸ ho)
  rw [hzo, map_mul, hfu, ho1]

end LiftData2


section Central

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

omit [Finite X] in
theorem commutator_self_eq_of_central {A D : Subgroup X} [D.Normal] (hAc : A ≤ center X)
    (hDc : D = commutator X) {w : X} (hw : D ⊔ zpowers w = ⊤) (hperf : D ≤ ⁅D, D⁆ ⊔ A) :
    ⁅D, D⁆ = D := by
  have hD'D : ⁅D, D⁆ ≤ D := Subgroup.commutator_le_right D D
  apply le_antisymm hD'D
  suffices hcomm : commutator X ≤ ⁅D, D⁆ by rwa [← hDc] at hcomm
  set D' := ⁅D, D⁆ with hD'
  have : D'.Normal := inferInstance
  rw [← Subgroup.Normal.quotient_commutative_iff_commutator_le]
  refine ⟨⟨fun a b => ?_⟩⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  have hdec : ∀ x : X, ∃ a ∈ A, ∃ k : ℤ, (QuotientGroup.mk x : X ⧸ D') =
      QuotientGroup.mk a * (QuotientGroup.mk w) ^ k := by
    intro x
    have hx : x ∈ D ⊔ zpowers w := hw ▸ Subgroup.mem_top x
    obtain ⟨d, hd, wk, hwk, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hwk
    obtain ⟨d', hd', a, ha, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp (hperf hd)
    refine ⟨a, ha, k, ?_⟩
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_zpow,
      (QuotientGroup.eq_one_iff d').mpr hd', one_mul]
  obtain ⟨a₁, ha₁, k₁, h₁⟩ := hdec x
  obtain ⟨a₂, ha₂, k₂, h₂⟩ := hdec y
  rw [h₁, h₂]
  have hc₁ : Commute (QuotientGroup.mk a₁ : X ⧸ D') (QuotientGroup.mk a₂) := by
    show _ = _
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact (Subgroup.mem_center_iff.mp (hAc ha₂) a₁)
  have hc₂ : Commute (QuotientGroup.mk a₁ : X ⧸ D') ((QuotientGroup.mk w) ^ k₂) := by
    show _ = _
    rw [← QuotientGroup.mk_zpow, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact (Subgroup.mem_center_iff.mp (hAc ha₁) (w ^ k₂)).symm
  have hc₃ : Commute ((QuotientGroup.mk w : X ⧸ D') ^ k₁) (QuotientGroup.mk a₂) := by
    show _ = _
    rw [← QuotientGroup.mk_zpow, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact (Subgroup.mem_center_iff.mp (hAc ha₂) (w ^ k₁))
  have hc₄ : Commute ((QuotientGroup.mk w : X ⧸ D') ^ k₁) ((QuotientGroup.mk w) ^ k₂) :=
    (Commute.refl _).zpow_zpow k₁ k₂
  exact ((hc₁.mul_right hc₂).mul_left (hc₃.mul_right hc₄)).eq

theorem ZDSetup.exists_conj_mem_of_isPGroup (S : ZDSetup X Z M) {x : X}
    (hx : IsPGroup 2 (zpowers x)) : ∃ g : X, g⁻¹ * x * g ∈ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz, hzM⟩ := S.exists_mem_inter
  obtain ⟨T, hTM, -, -⟩ := S.exists_sylow_central hz hzM
  obtain ⟨Q, hQ⟩ := hx.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Q T
  refine ⟨g⁻¹, ?_⟩
  have hxQ : x ∈ (Q : Subgroup X) := hQ (Subgroup.mem_zpowers x)
  have : g * x * g⁻¹ ∈ ((g • Q : Sylow 2 X) : Subgroup X) :=
    (mem_smul_sylow_iff Q g _).mpr ⟨x, hxQ, rfl⟩
  rw [hg] at this
  simpa using hTM this

end Central


section PartI

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.two_le_pRank_zHull_top (S : ZDSetup X Z M) :
    2 ≤ Open.pRank 2 (zHull Z (⊤ : Subgroup X)) := by
  have : zHull Z (⊤ : Subgroup X) = ⊤ := by
    unfold zHull
    rw [Subgroup.coe_top, Set.inter_univ]
    exact S.gen
  rw [this]
  exact S.two_le_twoRank

theorem odd_card_pPrimeCore (X : Type*) [Group X] [Finite X] : Odd (Nat.card (pPrimeCore 2 X)) :=
  Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := X))

theorem ZDSetup.pPrimeCore_le (S : ZDSetup X Z M) : pPrimeCore 2 X ≤ M := by
  obtain ⟨z, hz, hzM⟩ := S.exists_mem_inter
  have hnorm : normalizer ((pPrimeCore 2 X : Subgroup X) : Set X) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr inferInstance
  have hrank : 2 ≤ Open.pRank 2 (zHull Z (normalizer ((pPrimeCore 2 X : Subgroup X) : Set X))) := by
    rw [hnorm]
    exact S.two_le_pRank_zHull_top
  exact S.lemma313 (odd_card_pPrimeCore X) hrank hz (by rw [hnorm]; exact Subgroup.mem_top z)
    (self_mem_omega M) ((S.prodDisc.conjugate_eq_iff_mem (self_mem_omega M)).mpr hzM)

theorem ZDSetup.pPrimeCore_eq_bot (S : ZDSetup X Z M) : pPrimeCore 2 X = ⊥ := by
  by_contra hne
  have hNM := S.pPrimeCore_le
  have hNodd := odd_card_pPrimeCore X
  have hZN : ∀ z ∈ Z, z ∉ pPrimeCore 2 X := by
    intro z hz hzN
    have := S.prodDisc.zN_eq_empty inferInstance hNM
    exact (Set.eq_empty_iff_forall_notMem.mp this) z ⟨hz, hzN⟩
  have hpd := S.isProductDisconnected_quot hNM (S.hlift_odd hNodd)
  have hinv := S.invariant.map_mk' (pPrimeCore 2 X) hZN
  have hgen := closure_image_mk' (pPrimeCore 2 X) S.gen
  have hlt : Nat.card (X ⧸ pPrimeCore 2 X) < Nat.card X := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 X)
    have h2 : 1 < Nat.card (pPrimeCore 2 X) := (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
    have h3 : 0 < Nat.card (X ⧸ pPrimeCore 2 X) := Nat.card_pos
    nlinarith
  have hIH := S.ih (X ⧸ pPrimeCore 2 X) hlt _ _ hinv hgen hpd
  rw [zdConclusion_iff] at hIH
  rcases hIH with hrank | ⟨ub, hub⟩
  · apply S.counterexample
    refine Or.inl ?_
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hq := CFSG.SectionRank.pRank_quotient_eq (p := 2) (pPrimeCore 2 X)
      (fun h2 => (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr h2))
    unfold Open.twoRank at hrank ⊢
    rw [← hq]
    exact hrank
  · obtain ⟨u, hu⟩ := S.zdData_of_quot rfl hNM hub
    exact S.counterexample ((zdConclusion_iff _ _).mpr (Or.inr ⟨u, hu⟩))

end PartI


section PartIIIAux

variable {X : Type} [Group X]

theorem mem_zpowers_involution {v w : X} (hv : v * v = 1) (hw : w ∈ zpowers v) :
    w = 1 ∨ w = v := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left
    rw [zpow_mul]
    have : v ^ (2 : ℤ) = 1 := by rw [zpow_two, hv]
    rw [this, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_one]
    have : v ^ (2 : ℤ) = 1 := by rw [zpow_two, hv]
    rw [this, one_zpow, one_mul]

theorem normal_of_le_center' {A : Subgroup X} (hAc : A ≤ center X) : A.Normal := by
  refine ⟨fun n hn g => ?_⟩
  have := Subgroup.mem_center_iff.mp (hAc hn) g
  rw [this]
  simpa using hn

theorem map_subtype_commutator' (D : Subgroup X) : (commutator ↥D).map D.subtype = ⁅D, D⁆ := by
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

end PartIIIAux


section PartIII

open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem commutator_eq_top_of_isBenderGroup
    {K : Type} [Group K] [Finite K]
    (h : CFSG.BenderSuzuki.IsBenderGroup K) : commutator K = ⊤ := by
  have hsimple := isSimpleGroup_of_isBenderGroup h
  rcases hsimple.eq_bot_or_eq_top_of_normal (commutator K) with hb | ht
  · exfalso
    obtain ⟨a, b, hab⟩ := exists_not_commute_of_isBenderGroup h
    apply hab
    have hmem : ⁅a, b⁆ ∈ commutator K :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [hb, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem
  · exact ht

theorem ZDSetup.central_facts (S : ZDSetup X Z M) {v : X} (hv : v ∈ center X) (hv2 : orderOf v = 2) :
    v ∈ M ∧ v ∉ Z ∧ v ∉ productInvolutions Z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hvv : v * v = 1 := by
    have := pow_orderOf_eq_one v
    rwa [hv2, pow_two] at this
  have hApGroup : IsPGroup 2 (zpowers v) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hv2, pow_one])
  have hvM : v ∈ M := by
    obtain ⟨g, hg⟩ := S.exists_conj_mem_of_isPGroup hApGroup
    have : g⁻¹ * v * g = v := by
      have := Subgroup.mem_center_iff.mp hv g⁻¹
      rw [this]; group
    rwa [this] at hg
  have hC : centralizer ({v} : Set X) = ⊤ :=
    Subgroup.centralizer_eq_top_iff_subset.mpr (by simpa using hv)
  refine ⟨hvM, ?_, ?_⟩
  · intro hvZ
    exact S.prodDisc.ne_top (top_le_iff.mp (hC ▸ S.prodDisc.centralizer_le_of_mem hvZ hvM))
  · intro hvP
    exact S.prodDisc.ne_top (top_le_iff.mp (hC ▸ (S.prodDisc.mem_uniqC hvP hvM).2.2))

end PartIII


section PartIII2

open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.false_of_central_involution
    (hB : BenderCoverRigid) (S : ZDSetup X Z M)
    (hO : pPrimeCore 2 X = ⊥) {v : X} (hv : v ∈ center X) (hv2 : orderOf v = 2) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hvM, hvZ, hvP⟩ := S.central_facts hv hv2
  have hvv : v * v = 1 := by
    have := pow_orderOf_eq_one v
    rwa [hv2, pow_two] at this
  set A := zpowers v with hA
  have hAc : A ≤ center X := (Subgroup.zpowers_le).mpr hv
  have : A.Normal := normal_of_le_center' hAc
  have hA2 : Nat.card A = 2 := by rw [hA, Nat.card_zpowers, hv2]
  have hAM : A ≤ M := (Subgroup.zpowers_le).mpr hvM
  have hZA : ∀ z ∈ Z, z ∉ A := by
    intro z hz hzA
    rcases mem_zpowers_involution hvv hzA with h1 | h1
    · have := S.invariant.1 z hz
      rw [h1, orderOf_one] at this
      exact absurd this (by norm_num)
    · exact hvZ (h1 ▸ hz)
  have hvzZ : ∀ z ∈ Z, v * z ∉ Z := by
    intro z hz hvz
    apply hvP
    have hzv : z * v = v * z := Subgroup.mem_center_iff.mp hv z
    refine ⟨hv2, v * z, hvz, z, hz, ?_, ?_⟩
    · calc v * z * z = z * v * z := by rw [hzv]
        _ = z * (v * z) := by rw [mul_assoc]
    · rw [mul_assoc, S.invariant.mul_self_eq_one hz, mul_one]
  have hlift : ∀ x ∈ Z, ∀ y ∈ Z, x * y * x⁻¹ * y⁻¹ ∈ A →
      ∃ x' ∈ Z, ∃ y' ∈ Z, x'⁻¹ * x ∈ A ∧ y'⁻¹ * y ∈ A ∧ x' * y' = y' * x' := by
    intro x hx y hy hxy
    refine ⟨x, hx, y, hy, by simp, by simp, ?_⟩
    rcases mem_zpowers_involution hvv hxy with h1 | h1
    · calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
        _ = y * x := by rw [h1, one_mul]
    · exfalso
      have hxyx : x * y * x⁻¹ = v * y := by
        calc x * y * x⁻¹ = (x * y * x⁻¹ * y⁻¹) * y := by group
          _ = v * y := by rw [h1]
      have : x * y * x⁻¹ ∈ Z := by
        have := S.invariant.2 y hy x⁻¹
        simpa using this
      exact hvzZ y hy (hxyx ▸ this)
  have hpd := S.isProductDisconnected_quot hAM hlift
  have hinv := S.invariant.map_mk' A hZA
  have hgen := closure_image_mk' A S.gen
  have hlt : Nat.card (X ⧸ A) < Nat.card X := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup A
    have h3 : 0 < Nat.card (X ⧸ A) := Nat.card_pos
    rw [hA2] at h1
    omega
  have hIH := S.ih (X ⧸ A) hlt _ _ hinv hgen hpd
  rw [zdConclusion_iff] at hIH
  have hbot : pPrimeCore 2 (X ⧸ A) = ⊥ := pPrimeCore_quotient_central_two hAc hA2 hO
  obtain ⟨z₀, hz₀, hz₀M⟩ := S.exists_mem_inter
  have hz₀2 := S.invariant.mul_self_eq_one hz₀
  have hZD : ∀ z ∈ Z, z * z₀⁻¹ ∈ commutator X := by
    intro z hz
    obtain ⟨g, hg⟩ := isConj_iff.mp (S.prodDisc.isConj_of_mem S.invariant hz₀ hz)
    rw [← hg]
    have hmem : ⁅g, z₀⁆ ∈ commutator X :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top z₀)
    rw [commutatorElement_def] at hmem
    exact hmem
  have hXD : commutator X ⊔ zpowers z₀ = ⊤ := by
    rw [eq_top_iff, ← S.gen, Subgroup.closure_le]
    intro z hz
    have : z = (z * z₀⁻¹) * z₀ := by group
    rw [this]
    exact (commutator X ⊔ zpowers z₀).mul_mem (Subgroup.mem_sup_left (hZD z hz))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  rcases hIH with hrank | ⟨ub, hub⟩
  ·
    exfalso
    have hz1 : QuotientGroup.mk' A z₀ ≠ 1 := fun h =>
      hZA z₀ hz₀ ((QuotientGroup.eq_one_iff z₀).mp h)
    have hz2 : QuotientGroup.mk' A z₀ * QuotientGroup.mk' A z₀ = 1 := by
      rw [← map_mul, hz₀2, map_one]
    have : Fintype (X ⧸ A) := Fintype.ofFinite _
    obtain ⟨N, hNn, hNodd, hN⟩ := CFSG.ZStar.glauberman_zStar (X ⧸ A) (QuotientGroup.mk' A z₀)
      hz1 hz2 (by
        intro g hg
        by_contra hne
        have hmem : g * QuotientGroup.mk' A z₀ * g⁻¹ ∈ (QuotientGroup.mk' A) '' Z := by
          have := hinv.2 _ ⟨z₀, hz₀, rfl⟩ g⁻¹
          simpa using this
        obtain ⟨y, hy, hyeq⟩ := hmem
        have hy2 : orderOf (g * QuotientGroup.mk' A z₀ * g⁻¹) = 2 := by
          rw [← hyeq]; exact hinv.1 _ ⟨y, hy, rfl⟩
        have h2 := CFSG.TwoRankLowerBound.Helpers.two_le_twoRank_of_commuting_involutions (X ⧸ A)
          _ _ hy2 (hinv.1 _ ⟨z₀, hz₀, rfl⟩) hne hg
        omega)
    have hNle : N ≤ pPrimeCore 2 (X ⧸ A) :=
      le_sSup ⟨hNn, Nat.coprime_two_left.mpr hNodd⟩
    rw [hbot] at hNle
    have hcen : ∀ g : X, g * z₀ * g⁻¹ * z₀⁻¹ ∈ A := by
      intro g
      have h1 := hN (QuotientGroup.mk' A g)
      have h2 := hNle h1
      rw [Subgroup.mem_bot] at h2
      apply (QuotientGroup.eq_one_iff _).mp
      show QuotientGroup.mk' A (g * z₀ * g⁻¹ * z₀⁻¹) = 1
      simpa using h2
    have hcomm : ∀ g : X, g * z₀ * g⁻¹ = z₀ := by
      intro g
      rcases mem_zpowers_involution hvv (hcen g) with h1 | h1
      · calc g * z₀ * g⁻¹ = (g * z₀ * g⁻¹ * z₀⁻¹) * z₀ := by group
          _ = z₀ := by rw [h1, one_mul]
      · exfalso
        have hg : g * z₀ * g⁻¹ = v * z₀ := by
          calc g * z₀ * g⁻¹ = (g * z₀ * g⁻¹ * z₀⁻¹) * z₀ := by group
            _ = v * z₀ := by rw [h1]
        have : g * z₀ * g⁻¹ ∈ Z := by
          have := S.invariant.2 z₀ hz₀ g⁻¹
          simpa using this
        exact hvzZ z₀ hz₀ (hg ▸ this)
    have hC : centralizer ({z₀} : Set X) = ⊤ := by
      rw [eq_top_iff]
      intro g _
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := hcomm g
      calc g * z₀ = (g * z₀ * g⁻¹) * g := by group
        _ = z₀ * g := by rw [this]
    exact S.prodDisc.ne_top (top_le_iff.mp (hC ▸ S.prodDisc.centralizer_le_of_mem hz₀ hz₀M))
  · obtain ⟨K, _, φ', hφ's, hφ'k, hKB, S', hS'⟩ := hub.bar
    have : Finite K := Finite.of_surjective φ' (by simpa using hφ's)
    have hk' : φ'.ker = ⊥ := by rw [hφ'k, hbot, Subgroup.bot_subgroupOf]
    obtain ⟨φ, hφs, hφk, hφS⟩ := exists_hom_comp_quot hAM φ' hφ's hk' hS'
    by_cases hvD : v ∈ commutator X
    ·
      exfalso
      have hKperf : commutator K = ⊤ := commutator_eq_top_of_isBenderGroup hKB
      have hperf : commutator X ≤ ⁅commutator X, commutator X⁆ ⊔ A := by
        intro d hd
        have hmapc : (commutator ↥(commutator X)).map φ = ⊤ := by
          rw [map_commutator_of_surjective φ hφs, hKperf]
        have hmem : φ ⟨d, hd⟩ ∈ (commutator ↥(commutator X)).map φ := hmapc ▸ Subgroup.mem_top _
        obtain ⟨e, he, hed⟩ := hmem
        have hker : (⟨d, hd⟩ : ↥(commutator X)) * e⁻¹ ∈ φ.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, ← hed, mul_inv_cancel]
        rw [hφk, Subgroup.mem_subgroupOf] at hker
        have he' : (e : X) ∈ ⁅commutator X, commutator X⁆ := by
          rw [← map_subtype_commutator']
          exact Subgroup.mem_map_of_mem _ he
        have hd' : d = ((d : X) * (e : X)⁻¹) * (e : X) := by group
        rw [hd']
        exact (⁅commutator X, commutator X⁆ ⊔ A).mul_mem
          (Subgroup.mem_sup_right (by simpa using hker)) (Subgroup.mem_sup_left he')
      have hDD : ⁅commutator X, commutator X⁆ = commutator X :=
        commutator_self_eq_of_central hAc rfl hXD hperf
      have hAD : A ≤ commutator X := (Subgroup.zpowers_le).mpr hvD
      have : (commutator X).Normal := inferInstance
      have : ((A).subgroupOf (commutator X)).Normal := inferInstance
      have hBender : CFSG.BenderSuzuki.IsBenderGroup (↥(commutator X) ⧸ A.subgroupOf (commutator X)) := by
        let e : (↥(commutator X) ⧸ A.subgroupOf (commutator X)) ≃* K :=
          (QuotientGroup.quotientMulEquivOfEq hφk.symm).trans
            (QuotientGroup.quotientKerEquivOfSurjective φ hφs)
        exact isBenderGroup_of_mulEquiv e hKB
      obtain ⟨T, hTM, hzT, hcomm⟩ := S.exists_sylow_central hz₀ hz₀M
      obtain ⟨P, hP⟩ := exists_sylow_map_subtype_eq_inf (inferInstance : (commutator X).Normal) T
      have hcentD : ∀ k ∈ commutator X, z₀ * k * z₀⁻¹ = k := by
        apply hB X (commutator X) A hAD (fun a ha k _ => (Subgroup.mem_center_iff.mp (hAc ha) k).symm)
          hA2 hDD hBender P z₀
        intro s hs
        have hs' : (s : X) ∈ (T : Subgroup X) ⊓ commutator X := by
          rw [← hP]; exact Subgroup.mem_map_of_mem _ hs
        have := hcomm (s : X) hs'.1
        calc z₀ * (s : X) * z₀⁻¹ = (z₀ * (s : X)) * z₀⁻¹ := rfl
          _ = ((s : X) * z₀) * z₀⁻¹ := by rw [this]
          _ = (s : X) := by group
      have hDcenter : commutator X ≤ center X := by
        intro k hk
        rw [Subgroup.mem_center_iff]
        have hsub : Z ⊆ (centralizer ({k} : Set X) : Set X) := by
          intro z hz
          obtain ⟨c, hc⟩ := isConj_iff.mp (S.prodDisc.isConj_of_mem S.invariant hz₀ hz)
          rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, ← hc]
          have hk' : c⁻¹ * k * c ∈ commutator X := by
            have := (inferInstance : (commutator X).Normal).conj_mem k hk c⁻¹
            simpa using this
          have h1 := hcentD _ hk'
          calc c * z₀ * c⁻¹ * k = c * (z₀ * (c⁻¹ * k * c) * z₀⁻¹) * z₀ * c⁻¹ := by group
            _ = c * (c⁻¹ * k * c) * z₀ * c⁻¹ := by rw [h1]
            _ = k * (c * z₀ * c⁻¹) := by group
        have hcl : Subgroup.closure Z ≤ centralizer ({k} : Set X) := (Subgroup.closure_le _).mpr hsub
        rw [S.gen] at hcl
        intro g
        have := hcl (Subgroup.mem_top g)
        rw [Subgroup.mem_centralizer_singleton_iff] at this
        exact this
      have hbot2 : ⁅commutator X, commutator X⁆ = ⊥ :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
          (hDcenter.trans (Subgroup.center_le_centralizer _))
      have : commutator X = ⊥ := by rw [← hDD, hbot2]
      have hv1 : v = 1 := by
        have := hvD
        rw [‹commutator X = ⊥›, Subgroup.mem_bot] at this
        exact this
      rw [hv1, orderOf_one] at hv2
      exact absurd hv2 (by norm_num)
    ·
      have hAD : ∀ w ∈ A, w ∈ commutator X → w = 1 := by
        intro w hwA hwD
        rcases mem_zpowers_involution hvv hwA with h1 | h1
        · exact h1
        · exact absurd (h1 ▸ hwD) hvD
      have hz₀dec : ∃ d ∈ commutator X, z₀ = d * v := by
        have hvX : v ∈ commutator X ⊔ zpowers z₀ := hXD ▸ Subgroup.mem_top v
        obtain ⟨d, hd, w, hw, hdw⟩ := Subgroup.mem_sup_of_normal_left.mp hvX
        rcases mem_zpowers_involution hz₀2 hw with h1 | h1
        · exfalso
          rw [h1, mul_one] at hdw
          exact hvD (hdw ▸ hd)
        · rw [h1] at hdw
          exact ⟨d⁻¹, (commutator X).inv_mem hd, by rw [← hdw]; group⟩
      obtain ⟨d₀, hd₀, hz₀d⟩ := hz₀dec
      have hZv : ∀ z ∈ Z, ∃ e ∈ commutator X, z = v * e := by
        intro z hz
        refine ⟨(z * z₀⁻¹) * d₀, (commutator X).mul_mem (hZD z hz) hd₀, ?_⟩
        have hzv : z₀ * v = v * z₀ := Subgroup.mem_center_iff.mp hv z₀
        calc z = (z * z₀⁻¹) * z₀ := by group
          _ = (z * z₀⁻¹) * (d₀ * v) := by rw [← hz₀d]
          _ = v * ((z * z₀⁻¹) * d₀) := by
            have hcv := Subgroup.mem_center_iff.mp hv
            calc (z * z₀⁻¹) * (d₀ * v) = ((z * z₀⁻¹) * d₀) * v := by group
              _ = v * ((z * z₀⁻¹) * d₀) := hcv _
      have hsup : commutator X ⊔ zpowers v = ⊤ := by
        rw [eq_top_iff, ← S.gen, Subgroup.closure_le]
        intro z hz
        obtain ⟨e, he, rfl⟩ := hZv z hz
        have hcv := Subgroup.mem_center_iff.mp hv e
        show v * e ∈ commutator X ⊔ zpowers v
        rw [← hcv]
        exact (commutator X ⊔ zpowers v).mul_mem (Subgroup.mem_sup_left he)
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers v))
      have hinf : commutator X ⊓ zpowers v = ⊥ := by
        rw [eq_bot_iff]
        rintro y ⟨hyD, hyv⟩
        rw [Subgroup.mem_bot]
        exact hAD y hyv hyD
      have hcomm' : ⁅zpowers v, commutator X⁆ ≤ pPrimeCore 2 X := by
        have : ⁅zpowers v, commutator X⁆ = ⊥ :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
            (hAc.trans (Subgroup.center_le_centralizer _))
        rw [this]
        exact bot_le
      have hker : φ.ker = (pPrimeCore 2 X).subgroupOf (commutator X) := by
        rw [hφk, hO, Subgroup.bot_subgroupOf]
        ext w
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_bot]
        constructor
        · intro hw
          exact Subtype.ext (hAD w hw w.2)
        · intro hw
          rw [hw]
          exact A.one_mem
      refine S.counterexample ((zdConclusion_iff _ _).mpr (Or.inr ⟨v, ⟨hvM, by rw [pow_two]; exact hvv,
        hsup, hinf, hcomm', by rw [hO]; exact bot_le, by rw [hO]; exact bot_le,
        ⟨K, inferInstance, φ, hφs, hker, hKB, S', hφS⟩, ?_⟩⟩))
      intro z hz
      obtain ⟨e, he, hze⟩ := hZv z hz
      refine ⟨⟨e, he, hze⟩, fun o ho hzo => ?_⟩
      rw [hO, Subgroup.mem_bot] at ho
      rw [ho, mul_one] at hzo
      exact hvZ (hzo ▸ hz)

end PartIII2


section Lemma45

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.no_solvable_normal
    (hB : BenderFacts) (S : ZDSetup X Z M) :
    ∀ N : Subgroup X, N.Normal → Group.IsSolvable ↥N → N = ⊥ := by
  intro N hN hsol
  by_contra hne
  obtain ⟨p, hp, B, hBn, hBne, hBN, hBp, hBcomm⟩ :=
    exists_abelian_elemental_normal_of_solvable hN hsol hne
  have hO := S.pPrimeCore_eq_bot
  have : Fact p.Prime := ⟨hp⟩
  have hBpG : IsPGroup p ↥B := fun g => ⟨1, by
    apply Subtype.ext
    simpa using hBp g g.2⟩
  by_cases hp2 : p = 2
  · subst hp2
    obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hBne
    have hb1 : (a : X) ≠ 1 := fun h => ha (Subtype.ext h)
    have hb2 : orderOf (a : X) = 2 := orderOf_eq_prime (hBp a a.2) hb1
    have hcent : (a : X) ∈ center X := by
      have hsub : Z ⊆ (centralizer ({(a : X)} : Set X) : Set X) := by
        intro z hz
        obtain ⟨-, T, hzT, hcomm⟩ := S.isCentralInvolution hz
        have haT : (a : X) ∈ (T : Subgroup X) := hBpG.le_sylow_of_normal T a.2 |> fun h => h
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        exact (hcomm _ haT).symm
      have hcl : Subgroup.closure Z ≤ centralizer ({(a : X)} : Set X) :=
        (Subgroup.closure_le _).mpr hsub
      rw [S.gen] at hcl
      rw [Subgroup.mem_center_iff]
      intro g
      have := hcl (Subgroup.mem_top g)
      rw [Subgroup.mem_centralizer_singleton_iff] at this
      exact this
    exact S.false_of_central_involution hB.coverRigid hO hcent hb2
  · have hcard : ∃ n, Nat.card B = p ^ n := IsPGroup.iff_card.mp hBpG
    obtain ⟨n, hn⟩ := hcard
    have hcop : Nat.Coprime 2 (Nat.card B) := by
      rw [hn]
      exact Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
    have hle : B ≤ pPrimeCore 2 X := le_sSup ⟨hBn, hcop⟩
    rw [hO] at hle
    exact hBne (le_bot_iff.mp hle)

end Lemma45


end CFSG.GH74.Uniqueness
