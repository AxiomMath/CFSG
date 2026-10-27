module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBMSuzukiEightCover
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergCBShearAxis
public import CFSG.LocalAnalysis.EvenSmallLie.Setup
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.SuzukiOuterOdd

public section

namespace CFSG.LocalAnalysis.ComponentInitial.SuzukiEightZStar

open Subgroup

theorem eq_of_orderOf_eq_two_of_isCyclic {X : Type*} [Group X] [Finite X] [IsCyclic X]
    {x y : X} (hx : orderOf x = 2) (hy : orderOf y = 2) : x = y := by
  have := Fintype.ofFinite X
  have hd : 2 ∣ Fintype.card X := hx ▸ orderOf_dvd_card
  have h := IsCyclic.card_orderOf_eq_totient hd
  rw [Nat.totient_two] at h
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
  have hxa : x ∈ ({a} : Finset X) := ha ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
  have hya : y ∈ ({a} : Finset X) := ha ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩
  rw [Finset.mem_singleton] at hxa hya
  rw [hxa, hya]

section Automorphisms

open CFSG.ComponentClassification.OuterAutomorphisms (inner congr_conj)
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom onCenterQuotient
  onCenterQuotient_apply_mk centerQuotientHom_injective)

theorem onCenterQuotient_conj {X : Type*} [Group X] (x : X) :
    onCenterQuotient (MulAut.conj x) = MulAut.conj (QuotientGroup.mk' (center X) x) := by
  ext q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center X) q
  rw [onCenterQuotient_apply_mk]
  simp only [MulAut.conj_apply, map_mul, map_inv]

theorem exists_inv_mul_mem_centralizer {G : Type*} [Group G] {L : Subgroup G}
    [Group.IsPerfect L] {Q : Type*} [Group Q] (φ : L ⧸ center L ≃* Q)
    (hQ : ∀ P : Subgroup (MulAut Q), IsPGroup 2 P → P ≤ inner Q)
    {n : G} (hn : n ∈ normalizer (L : Set G)) {k : ℕ} (hk : n ^ 2 ^ k = 1) :
    ∃ l ∈ L, l⁻¹ * n ∈ centralizer (L : Set G) := by
  set ρ : normalizer (L : Set G) →* MulAut Q :=
    (MulAut.congr φ).toMonoidHom.comp ((centerQuotientHom L).comp L.normalizerMonoidHom)
  set n' : normalizer (L : Set G) := ⟨n, hn⟩
  have hn' : n' ^ 2 ^ k = 1 := Subtype.ext (by simpa [n'] using hk)
  have hP : IsPGroup 2 (zpowers (ρ n')) := by
    rintro ⟨_, m, rfl⟩
    refine ⟨k, Subtype.ext ?_⟩
    change (ρ n' ^ m) ^ 2 ^ k = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← map_pow, hn', map_one,
      one_zpow]
  obtain ⟨g, hg⟩ := hQ _ hP (mem_zpowers _)
  obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (center L) (φ.symm g)
  have h1 : centerQuotientHom L (L.normalizerMonoidHom n') =
      centerQuotientHom L (MulAut.conj l) := by
    apply (MulAut.congr φ).injective
    change ρ n' = _
    rw [← hg]
    change MulAut.conj g = MulAut.congr φ (onCenterQuotient (MulAut.conj l))
    rw [onCenterQuotient_conj, congr_conj, hl, MulEquiv.apply_symm_apply]
  have h2 := centerQuotientHom_injective L h1
  refine ⟨l, l.2, mem_centralizer_iff.2 fun x hx => ?_⟩
  have h3 : n * x * n⁻¹ = l * x * (l : G)⁻¹ := by
    have := congrArg (fun α : MulAut L => (α ⟨x, hx⟩ : G)) h2
    simpa [n'] using this
  calc x * ((l : G)⁻¹ * n) = (l : G)⁻¹ * ((l : G) * x * (l : G)⁻¹) * n := by group
    _ = (l : G)⁻¹ * (n * x * n⁻¹) * n := by rw [h3]
    _ = (l : G)⁻¹ * n * x := by group

theorem exists_mulEquiv_suzukiGroup {X : Type} [Group X]
    (h : CFSG.Blueprint.LieModel X .twistedB2 0 2 3) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 8 ∧
      Nonempty (X ≃* CFSG.Blueprint.suzukiGroup 1 K) := by
  rcases h with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, -, a, ha, K, hF, hfin, ha3, hK, hφ⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · obtain rfl : a = 1 := by omega
    exact ⟨K, hF, hfin, by rw [hK]; norm_num, hφ⟩

end Automorphisms

section Product

variable {G : Type*} [Group G] {L : Subgroup G}

theorem le_normalizer_centralizer :
    L ≤ normalizer (centralizer (L : Set G) : Set G) :=
  le_trans (le_centralizer_iff.2 le_rfl) (centralizer_le_normalizer _)

theorem mem_sup_centralizer_iff {P : Subgroup G} (hP : P ≤ L) {x : G} :
    x ∈ P ⊔ centralizer (L : Set G) ↔ ∃ p ∈ P, ∃ c ∈ centralizer (L : Set G), p * c = x := by
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _
    (le_trans hP le_normalizer_centralizer), Set.mem_mul]
  simp only [SetLike.mem_coe]

theorem mem_center_of_mem_centralizer {x : G} (hxL : x ∈ L)
    (hxC : x ∈ centralizer (L : Set G)) : (⟨x, hxL⟩ : L) ∈ center L :=
  mem_center_iff.2 fun y => Subtype.ext (mem_centralizer_iff.1 hxC y y.2)

theorem mem_centralizer_of_forall_commute {P : Subgroup G} (hP : P ≤ L)
    (hZP : ∀ p ∈ P, (∀ q ∈ P, p * q = q * p) → p ∈ centralizer (L : Set G))
    {y : G} (hy : y ∈ P ⊔ centralizer (L : Set G)) (hyc : ∀ q ∈ P, y * q = q * y) :
    y ∈ centralizer (L : Set G) := by
  obtain ⟨p, hp, c, hc, rfl⟩ := (mem_sup_centralizer_iff hP).1 hy
  refine mul_mem (hZP p hp fun q hq => ?_) hc
  have h1 := hyc q hq
  have h2 : q * c = c * q := mem_centralizer_iff.1 hc q (hP hq)
  have h3 : p * q * c = q * p * c := by
    calc p * q * c = p * (q * c) := mul_assoc _ _ _
      _ = p * (c * q) := by rw [h2]
      _ = q * (p * c) := by rw [← mul_assoc, h1]
      _ = q * p * c := (mul_assoc _ _ _).symm
  exact mul_right_cancel h3

theorem conj_eq_of_normalizes [Finite G] {P : Subgroup G} (hP : P ≤ L)
    (hZP : ∀ p ∈ P, (∀ q ∈ P, p * q = q * p) → p ∈ centralizer (L : Set G))
    (hCcyc : IsCyclic (centralizer (L : Set G))) {z : G} (hzL : z ∈ L)
    (hzC : z ∈ centralizer (L : Set G)) (hz2 : orderOf z = 2) {n : G}
    (hnz : n * z * n⁻¹ ∈ P ⊔ centralizer (L : Set G))
    (hn : ∀ r ∈ P ⊔ centralizer (L : Set G), n⁻¹ * r * n ∈ P ⊔ centralizer (L : Set G)) :
    n * z * n⁻¹ = z := by
  have hzR : ∀ r ∈ P ⊔ centralizer (L : Set G), z * r = r * z := by
    intro r hr
    obtain ⟨p, hp, c, hc, rfl⟩ := (mem_sup_centralizer_iff hP).1 hr
    have h1 : z * p = p * z := ((mem_centralizer_iff.1 hzC) p (hP hp)).symm
    have h2 : z * c = c * z := mem_centralizer_iff.1 hc z hzL
    calc z * (p * c) = p * (z * c) := by rw [← mul_assoc, h1, mul_assoc]
      _ = p * c * z := by rw [h2, mul_assoc]
  have hyR : ∀ q ∈ P, n * z * n⁻¹ * q = q * (n * z * n⁻¹) := by
    intro q hq
    have h := hzR _ (hn q (mem_sup_left hq))
    calc n * z * n⁻¹ * q = n * (z * (n⁻¹ * q * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * q * n) * z) * n⁻¹ := by rw [h]
      _ = q * (n * z * n⁻¹) := by group
  have hyC : n * z * n⁻¹ ∈ centralizer (L : Set G) :=
    mem_centralizer_of_forall_commute hP hZP hnz hyR
  have hy2 : orderOf (n * z * n⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hz2]
  exact congrArg Subtype.val (eq_of_orderOf_eq_two_of_isCyclic (X := centralizer (L : Set G))
    (x := ⟨_, hyC⟩) (y := ⟨z, hzC⟩) (by rwa [orderOf_mk]) (by rwa [orderOf_mk]))

theorem sup_centralizer_eq_sylow [Finite G] (P : Sylow 2 L) {z : G}
    (hzR : z ∈ (P : Subgroup L).map L.subtype ⊔ centralizer (L : Set G))
    (hfix : ∀ n : G, n * z * n⁻¹ ∈ (P : Subgroup L).map L.subtype ⊔ centralizer (L : Set G) →
      (∀ r ∈ (P : Subgroup L).map L.subtype ⊔ centralizer (L : Set G),
        n⁻¹ * r * n ∈ (P : Subgroup L).map L.subtype ⊔ centralizer (L : Set G)) →
      n * z * n⁻¹ = z)
    (hinner : ∀ n ∈ centralizer ({z} : Set G), ∀ k : ℕ, n ^ 2 ^ k = 1 →
      ∃ l ∈ L, l⁻¹ * n ∈ centralizer (L : Set G))
    (T : Sylow 2 G) (hRT : (P : Subgroup L).map L.subtype ⊔ centralizer (L : Set G) ≤ T) :
    (P : Subgroup L).map L.subtype ⊔ centralizer (L : Set G) = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := (P : Subgroup L).map L.subtype ⊔ centralizer (L : Set G)
  by_contra hne
  have hlt : R.subgroupOf T < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hne
    refine le_antisymm hRT fun x hx => ?_
    have : (⟨x, hx⟩ : (T : Subgroup G)) ∈ R.subgroupOf T := htop ▸ mem_top _
    exact this
  obtain ⟨n, hn, hnU⟩ := IsConcreteLE.exists_of_lt
    (p_group_normalizer_condition T.isPGroup' hlt)
  have hnz : (n : G) * z * (n : G)⁻¹ ∈ R := by
    have := (mem_normalizer_iff.1 hn ⟨z, hRT hzR⟩).1 (mem_subgroupOf.2 hzR)
    rwa [mem_subgroupOf] at this
  have hnR : ∀ r ∈ R, (n : G)⁻¹ * r * n ∈ R := by
    intro r hr
    have := (mem_normalizer_iff.1 (inv_mem hn) ⟨r, hRT hr⟩).1 (mem_subgroupOf.2 hr)
    rw [mem_subgroupOf] at this
    simpa using this
  have hnH : (n : G) ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have h := hfix n hnz hnR
    calc (n : G) * z = (n : G) * z * (n : G)⁻¹ * n := by group
      _ = z * n := by rw [h]
  obtain ⟨k, hk⟩ := T.isPGroup' n
  obtain ⟨l, hlL, hlC⟩ := hinner n hnH k (by simpa using congrArg Subtype.val hk)
  have hCT : centralizer (L : Set G) ≤ T := le_trans le_sup_right hRT
  have hlT : l ∈ (T : Subgroup G) := by
    have h : l = n * (l⁻¹ * n)⁻¹ := by group
    rw [h]
    exact mul_mem n.2 (inv_mem (hCT hlC))
  have hTL : (T : Subgroup G).subgroupOf L = P :=
    P.is_maximal' T.isPGroup'.comap_subtype
      (fun x hx => mem_subgroupOf.2 (hRT (mem_sup_left ⟨x, hx, rfl⟩)))
  have hlP : (⟨l, hlL⟩ : L) ∈ (P : Subgroup L) := hTL ▸ mem_subgroupOf.2 hlT
  apply hnU
  rw [mem_subgroupOf]
  have h : (n : G) = l * (l⁻¹ * n) := by group
  rw [h]
  exact mul_mem (mem_sup_left ⟨_, hlP, rfl⟩) (mem_sup_right hlC)

theorem closure_involutions_eq [Finite G] (P : Sylow 2 L) {A : Subgroup L}
    (hAP : A ≤ (P : Subgroup L)) (hA2 : ∀ a ∈ A, a ^ 2 = 1)
    (hsq : ∀ x ∈ (P : Subgroup L), x ^ 2 ∈ center L → x ∈ A)
    (hCcyc : IsCyclic (centralizer (L : Set G))) {z : L} (hzA : z ∈ A)
    (hzC : (z : G) ∈ centralizer (L : Set G)) (hz2 : orderOf (z : G) = 2) :
    closure {x : G | x ∈ (P : Subgroup L).map L.subtype ⊔ centralizer (L : Set G) ∧
      orderOf x = 2} = A.map L.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPL : (P : Subgroup L).map L.subtype ≤ L := map_subtype_le _
  apply le_antisymm
  · rw [closure_le]
    rintro x ⟨hx, hx2⟩
    obtain ⟨_, ⟨p, hp, rfl⟩, c, hc, rfl⟩ := (mem_sup_centralizer_iff hPL).1 hx
    have hpc : (p : G) * c = c * p := mem_centralizer_iff.1 hc p p.2
    have hsq1 : ((p : G) * c) ^ 2 = (p : G) ^ 2 * c ^ 2 := by
      rw [sq, sq, sq]
      calc (p : G) * c * ((p : G) * c) = (p : G) * (c * p) * c := by group
        _ = (p : G) * ((p : G) * c) * c := by rw [hpc]
        _ = (p : G) * p * (c * c) := by group
    have hx1 : ((p : G) * c) ^ 2 = 1 := by
      rw [← hx2]
      exact pow_orderOf_eq_one _
    rw [hsq1] at hx1
    have hp2C : (p : G) ^ 2 ∈ centralizer (L : Set G) := by
      rw [eq_inv_of_mul_eq_one_left hx1]
      exact inv_mem (pow_mem hc 2)
    have hp2Z : p ^ 2 ∈ center L := mem_center_of_mem_centralizer (pow_mem p.2 2) hp2C
    have hpA : p ∈ A := hsq p hp hp2Z
    have hp1 : (p : G) ^ 2 = 1 := by
      have := congrArg Subtype.val (hA2 p hpA)
      simpa using this
    rw [hp1, one_mul] at hx1
    have hcA : c ∈ A.map L.subtype := by
      by_cases hc1 : c = 1
      · rw [hc1]
        exact one_mem _
      · have hcz := congrArg Subtype.val (eq_of_orderOf_eq_two_of_isCyclic
          (X := centralizer (L : Set G)) (x := ⟨c, hc⟩) (y := ⟨z, hzC⟩)
          (by rw [orderOf_mk]; exact orderOf_eq_prime hx1 hc1) (by rwa [orderOf_mk]))
        change c = (z : G) at hcz
        rw [hcz]
        exact ⟨z, hzA, rfl⟩
    exact mul_mem ⟨p, hpA, rfl⟩ hcA
  · rintro _ ⟨a, ha, rfl⟩
    by_cases h1 : (a : G) = 1
    · change (a : G) ∈ _
      rw [h1]
      exact one_mem _
    · refine subset_closure ⟨mem_sup_left ⟨a, hAP ha, rfl⟩, orderOf_eq_prime ?_ h1⟩
      have := congrArg Subtype.val (hA2 a ha)
      simpa using this

theorem shear_image_eq {P A : Subgroup L} {z : L}
    (hrange : Set.range (fun (p : P) (a : A) => (p : L) * a * (p : L)⁻¹) =
      {f | ∃ ℓ : Additive A →+ ZMod 2, (∀ a : A, (a : L) = z → ℓ (Additive.ofMul a) = 0) ∧
        f = fun a : A => (a : L) * z ^ (ℓ (Additive.ofMul a)).val})
    (hzA : (z : G) ∈ A.map L.subtype) :
    {f : A.map L.subtype → A.map L.subtype |
        ∃ s ∈ P.map L.subtype ⊔ centralizer (L : Set G), ∀ a, (f a : G) = s * a * s⁻¹} =
      {f | ∃ ℓ : Additive (A.map L.subtype) →+ ZMod 2, ℓ (Additive.ofMul ⟨z, hzA⟩) = 0 ∧
        ∀ a, (f a : G) = a * (z : G) ^ (ℓ (Additive.ofMul a)).val} := by
  set e : A ≃* A.map L.subtype := A.equivMapOfInjective L.subtype L.subtype_injective
  have he' : ∀ a : A, ((e a : A.map L.subtype) : G) = ((a : L) : G) := fun a => rfl
  have hes : ∀ b : A.map L.subtype, (((e.symm b : A) : L) : G) = (b : G) := fun b => by
    rw [← he', MulEquiv.apply_symm_apply]
  ext f
  constructor
  · rintro ⟨s, hs, hf⟩
    obtain ⟨_, ⟨p, hp, rfl⟩, c, hc, rfl⟩ := (mem_sup_centralizer_iff (map_subtype_le P)).1 hs
    have hmem : (fun a : A => (p : L) * a * (p : L)⁻¹) ∈
        Set.range (fun (p : P) (a : A) => (p : L) * a * (p : L)⁻¹) := ⟨⟨p, hp⟩, rfl⟩
    rw [hrange] at hmem
    obtain ⟨ℓ, hℓz, hℓ⟩ := hmem
    refine ⟨ℓ.comp (MulEquiv.toAdditive e.symm).toAddMonoidHom, ?_, fun b => ?_⟩
    · change ℓ (Additive.ofMul (e.symm ⟨z, hzA⟩)) = 0
      exact hℓz _ (Subtype.ext (hes _))
    · rw [hf b]
      have hcb : (b : G) * c = c * b := mem_centralizer_iff.1 hc b (map_subtype_le A b.2)
      have h1 : L.subtype p * c * b * (L.subtype p * c)⁻¹ = (p : G) * b * (p : G)⁻¹ := by
        calc L.subtype p * c * b * (L.subtype p * c)⁻¹ = (p : G) * (c * b) * c⁻¹ * (p : G)⁻¹ := by
              simp only [coe_subtype]
              group
          _ = (p : G) * (b * c) * c⁻¹ * (p : G)⁻¹ := by rw [hcb]
          _ = (p : G) * b * (p : G)⁻¹ := by group
      have h2 := congrArg (fun x : L => (x : G)) (congrFun hℓ (e.symm b))
      simp only [coe_mul, coe_inv, SubgroupClass.coe_pow, hes] at h2
      rw [h1, h2]
      rfl
  · rintro ⟨ℓ, hℓz, hf⟩
    have hmem : (fun a : A => (a : L) * z ^
        ((ℓ.comp (MulEquiv.toAdditive e).toAddMonoidHom) (Additive.ofMul a)).val) ∈
        Set.range (fun (p : P) (a : A) => (p : L) * a * (p : L)⁻¹) := by
      rw [hrange]
      refine ⟨ℓ.comp (MulEquiv.toAdditive e).toAddMonoidHom, fun a ha => ?_, rfl⟩
      change ℓ (Additive.ofMul (e a)) = 0
      have hea : e a = ⟨z, hzA⟩ := Subtype.ext (by rw [he', ha])
      rw [hea, hℓz]
    obtain ⟨p, hp⟩ := hmem
    refine ⟨(p : L), mem_sup_left ⟨p, p.2, rfl⟩, fun b => ?_⟩
    rw [hf b]
    have h2 := congrArg (fun x : L => (x : G)) (congrFun hp (e.symm b))
    simp only [coe_mul, coe_inv, SubgroupClass.coe_pow, hes] at h2
    rw [h2]
    change _ = _ * _ ^ (ℓ (Additive.ofMul (e (e.symm b)))).val
    rw [MulEquiv.apply_symm_apply]

end Product

theorem even_standard_Suzuki_eight_double_cover_Zstar
    {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : CFSG.Open.standardComponentIsStandard L)
    (S : Sylow 2 (centralizer (L : Set G)))
    (hS : IsCyclic (S : Subgroup (centralizer (L : Set G))))
    {z : L} (hz : zpowers z = center L) (hZ : Nat.card (center L) = 2)
    (hmod : CFSG.Blueprint.LieModel (L ⧸ center L) .twistedB2 0 2 3)
    (hcore : CFSG.Open.standardComponentOddCore (centralizer ({(z : G)} : Set G)) = ⊥) :
    (∀ T : Sylow 2 G, (z : G) ∈ (T : Subgroup G) →
        (z : G) ∈ (center (T : Subgroup G)).map (T : Subgroup G).subtype ∧
        Set.range (fun g : G => g⁻¹ * (z : G) * g) ∩ (T : Set G) = {(z : G)}) ∧
      (∀ g : G, ∃ c ∈ centralizer ({(z : G)} : Set G), ∃ k ∈ CFSG.oddCore G, g = c * k) ∧
      (QuotientGroup.mk (z : G) : G ⧸ CFSG.oddCore G) ∈ center (G ⧸ CFSG.oddCore G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect L := ⟨hL.1.1⟩
  have hzZ : z ∈ center L := hz ▸ mem_zpowers z
  have hzo : orderOf z = 2 := by rw [← Nat.card_zpowers, hz, hZ]
  have hz2 : orderOf (z : G) = 2 := by rw [orderOf_coe, hzo]
  have hz1 : (z : G) ≠ 1 := fun h => by
    rw [h, orderOf_one] at hz2
    exact absurd hz2 (by decide)
  have hzC : (z : G) ∈ centralizer (L : Set G) :=
    CFSG.EvenSmallLie.mem_centralizer_of_mem_center hzZ
  obtain ⟨hC2, hCcyc⟩ :=
    CFSG.EvenSmallLie.centralizer_isPGroup_isCyclic_of_center hL hzZ hz2 hcore S hS
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := exists_mulEquiv_suzukiGroup hmod
  have hK' : Nat.card K = 2 ^ (2 * 1 + 1) := hK
  set η : L →* CFSG.Blueprint.suzukiGroup 1 K :=
    φ.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hηs : Function.Surjective η := φ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : η.ker = center L := by
    ext x
    rw [MonoidHom.mem_ker]
    change φ (QuotientGroup.mk' (center L) x) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  let P : Sylow 2 L := default
  obtain ⟨hAe, hA16, hZP, -, -, hsq, hrange, -⟩ :=
    even_Suzuki_eight_double_cover_Sylow_involutions hK η hηs (hker ▸ le_rfl)
      (by rw [hker, hZ]) z (hz.trans hker.symm) P
  rw [hker] at hZP hsq
  set A := ⁅(P : Subgroup L), (P : Subgroup L)⁆
  have hA2 : ∀ a ∈ A, a ^ 2 = 1 := fun a ha => CFSG.elemPow_eq_one_of_isElementaryAbelian a ha
  have hzP : z ∈ (P : Subgroup L) := by
    rw [← hZP] at hzZ
    obtain ⟨w, -, rfl⟩ := hzZ
    exact w.2
  have hzA : z ∈ A := (hsq z hzP).1 (by rw [← hzo, pow_orderOf_eq_one]; exact one_mem _)
  set PG := (P : Subgroup L).map L.subtype with hPG
  have hPGL : PG ≤ L := map_subtype_le _
  have hZPG : ∀ p ∈ PG, (∀ q ∈ PG, p * q = q * p) → p ∈ centralizer (L : Set G) := by
    rintro _ ⟨p, hp, rfl⟩ hpc
    have hpZ : (⟨p, hp⟩ : (P : Subgroup L)) ∈ center (P : Subgroup L) :=
      mem_center_iff.2 fun q => Subtype.ext (Subtype.ext (hpc _ ⟨q, q.2, rfl⟩).symm)
    have hpZL : p ∈ center L := by
      rw [← hZP]
      exact ⟨⟨p, hp⟩, hpZ, rfl⟩
    exact CFSG.EvenSmallLie.mem_centralizer_of_mem_center hpZL
  set R := PG ⊔ centralizer (L : Set G) with hR
  have hRp : IsPGroup 2 R := (P.isPGroup'.map L.subtype).to_sup_of_normal_right' hC2
    (le_trans hPGL le_normalizer_centralizer)
  obtain ⟨T, hRT⟩ := hRp.exists_le_sylow
  have hRT' : R = T := sup_centralizer_eq_sylow P (mem_sup_right hzC)
    (fun n hnz hn => conj_eq_of_normalizes hPGL hZPG hCcyc z.2 hzC hz2 hnz hn)
    (fun n hn k hk => exists_inv_mul_mem_centralizer φ
      (CFSG.ProperTwoGeneratedCore.HighRankPair.suzuki_outer_automorphism_group_has_odd_order
        le_rfl hK').2
      (CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard hL hzC hz2 hn) hk)
    T hRT
  have hΩ := closure_involutions_eq P (commutator_le_self _) hA2
    (fun x hx hx2 => (hsq x hx).1 hx2) hCcyc hzA hzC hz2
  rw [← hPG, ← hR, hRT'] at hΩ
  have hzAG : (z : G) ∈ A.map L.subtype := ⟨z, hzA, rfl⟩
  have hshear := shear_image_eq (G := G) hrange hzAG
  rw [← hPG, ← hR, hRT'] at hshear
  have hAeG : CFSG.Assembly.IsElemAbelian 2 (A.map L.subtype) := by
    refine ⟨inferInstance, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hA2 a ha, map_one]
  obtain ⟨hzT, hiso⟩ := even_four_dimensional_involution_shears_isolate_axis T hΩ.symm hAeG
    (by rw [card_map_of_injective L.subtype_injective, hA16]) hzAG hz1 hshear
  have hzT' : (z : G) ∈ (T : Subgroup G) := hRT' ▸ mem_sup_right hzC
  obtain ⟨w, hw, hwz⟩ := hzT
  have hwz' : w = ⟨z, hzT'⟩ := Subtype.ext hwz
  have hwc : ∀ g : G, g⁻¹ * (z : G) * g ∈ (T : Subgroup G) → g⁻¹ * (z : G) * g = z := by
    intro g hg
    have h : g⁻¹ * (z : G) * g ∈ Set.range (fun g : G => g⁻¹ * (z : G) * g) ∩ (T : Set G) :=
      ⟨⟨g, rfl⟩, hg⟩
    rw [hiso] at h
    exact h
  obtain ⟨hfac, hcen⟩ := CFSG.Adapters.glauberman_zStar T ⟨z, hzT'⟩ (hwz' ▸ hw)
    (by rw [orderOf_mk, hz2]) hwc
  have hiso' : ∀ T' : Sylow 2 G, (z : G) ∈ (T' : Subgroup G) →
      ∀ g : G, g⁻¹ * (z : G) * g ∈ (T' : Subgroup G) → g⁻¹ * (z : G) * g = z := by
    intro T' hzT'' g hg
    obtain ⟨x, rfl⟩ := MulAction.exists_smul_eq G T T'
    have hmem : ∀ y : G, y ∈ ((x • T : Sylow 2 G) : Subgroup G) ↔
        x⁻¹ * y * x ∈ (T : Subgroup G) := by
      intro y
      rw [Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
        ← map_inv, MulAut.conj_apply, inv_inv]
    rw [hmem] at hzT'' hg
    have hxz := hwc x hzT''
    have hxz' : x * (z : G) * x⁻¹ = z := by
      calc x * (z : G) * x⁻¹ = x * (x⁻¹ * (z : G) * x) * x⁻¹ := by rw [hxz]
        _ = z := by group
    have h1 : (g * x)⁻¹ * (z : G) * (g * x) ∈ (T : Subgroup G) := by
      convert hg using 1
      group
    have h2 := hwc _ h1
    calc g⁻¹ * (z : G) * g = x * ((g * x)⁻¹ * (z : G) * (g * x)) * x⁻¹ := by group
      _ = z := by rw [h2, hxz']
  refine ⟨fun T' hzT'' => ⟨⟨⟨z, hzT''⟩, mem_center_iff.2 fun t => Subtype.ext ?_, rfl⟩, ?_⟩,
    hfac, hcen⟩
  · have h := hiso' T' hzT'' t (mul_mem (mul_mem (inv_mem t.2) hzT'') t.2)
    change (t : G) * z = z * t
    calc (t : G) * z = t * ((t : G)⁻¹ * z * t) := by rw [h]
      _ = z * t := by group
  · ext y
    constructor
    · rintro ⟨⟨g, rfl⟩, hg⟩
      exact hiso' T' hzT'' g hg
    · rintro rfl
      exact ⟨⟨1, by group⟩, hzT''⟩

theorem false_of_suzuki_eight_double_cover {G : Type} [Group G]
    [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {L : Subgroup G}
    (hL : CFSG.Open.standardComponentIsStandard L)
    (S : Sylow 2 (Subgroup.centralizer (L : Set G)))
    (hS : IsCyclic (S : Subgroup (Subgroup.centralizer (L : Set G))))
    (hcore : ∀ t : G, orderOf t = 2 →
      CFSG.Open.standardComponentOddCore (Subgroup.centralizer ({t} : Set G)) = ⊥)
    (hZ : Nat.card (Subgroup.center L) = 2)
    (hmod : CFSG.Blueprint.LieModel (L ⧸ Subgroup.center L) .twistedB2 0 2 3) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial (center L) := Finite.one_lt_card_iff_nontrivial.1 (by rw [hZ]; norm_num)
  obtain ⟨⟨z, hzZ⟩, hz1⟩ := exists_ne (1 : center L)
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hzo : orderOf z = 2 := by
    refine orderOf_eq_prime ?_ hz1'
    have h := pow_card_eq_one' (x := (⟨z, hzZ⟩ : center L))
    rw [hZ] at h
    exact congrArg Subtype.val h
  have hz : zpowers z = center L :=
    eq_of_le_of_card_ge (zpowers_le.2 hzZ) (by rw [hZ, Nat.card_zpowers, hzo])
  have hz2 : orderOf (z : G) = 2 := by rw [orderOf_coe, hzo]
  obtain ⟨-, hfac, -⟩ :=
    even_standard_Suzuki_eight_double_cover_Zstar hL S hS hz hZ hmod (hcore _ hz2)
  have hO : CFSG.oddCore G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.oddCore G) with h | h
    · exact h
    · exact absurd (h ▸ mem_top (z : G)) (CFSG.Adapters.not_mem_oddCore_of_orderOf_eq_two hz2)
  have hzcen : (z : G) ∈ center G := by
    rw [mem_center_iff]
    intro g
    obtain ⟨c, hc, k, hk, rfl⟩ := hfac g
    rw [hO, mem_bot] at hk
    rw [hk, mul_one]
    exact mem_centralizer_singleton_iff.1 hc
  have htop : center G = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h | h
    · rw [h, mem_bot] at hzcen
      exact absurd hzcen (by exact_mod_cast hz1')
    · exact h
  obtain ⟨a, b, hab⟩ := hnonab
  exact hab (mem_center_iff.1 (htop ▸ mem_top b) a)

end CFSG.LocalAnalysis.ComponentInitial.SuzukiEightZStar
