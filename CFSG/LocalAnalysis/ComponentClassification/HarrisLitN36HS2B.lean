module

import CFSG.Adapters.StatedPSLTwoNine
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLit39
public import CFSG.Sporadic.SmallOddCore.CentCoset
public import Certificates.Data.CFSGNative.PairSchreier.J2Data

public section

namespace CFSG.ComponentClassification.HarrisLit.N36

namespace HS2B

open CFSG Subgroup CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier

theorem eq_one_or_eq_of_mem_zpowers {G : Type*} [Group G] {t x : G} (htt : t * t = 1)
    (hx : x ∈ zpowers t) : x = 1 ∨ x = t := by
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hx
  have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two, htt]
  have hm : m = 2 * (m / 2) + m % 2 := (Int.mul_ediv_add_emod m 2).symm
  rcases Int.emod_two_eq_zero_or_one m with h | h
  · left
    rw [hm, h, add_zero, zpow_mul, h2, one_zpow]
  · right
    rw [hm, h, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem exists_mul_ne_mul {G : Type*} [Group G] (h : IsQuasisimple G) :
    ∃ a b : G, a * b ≠ b * a := by
  obtain ⟨-, -, a, b, hab⟩ := h
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  exact ⟨a, b, fun h => hab (by rw [← QuotientGroup.mk_mul, h, QuotientGroup.mk_mul])⟩

theorem eq_one_or_eq_of_card_eq_two {G : Type*} [Group G] {H : Subgroup G}
    (hH : Nat.card H = 2) {a : G} (ha : a ∈ H) (ha1 : a ≠ 1) {x : G} (hx : x ∈ H) :
    x = 1 ∨ x = a := by
  rw [Nat.card_eq_two_iff' (1 : H)] at hH
  obtain ⟨y, -, huniq⟩ := hH
  by_cases hx1 : x = 1
  · exact Or.inl hx1
  · right
    have h1 : (⟨x, hx⟩ : H) = y := huniq _ fun h => hx1 (congrArg Subtype.val h)
    have h2 : (⟨a, ha⟩ : H) = y := huniq _ fun h => ha1 (congrArg Subtype.val h)
    exact congrArg Subtype.val (h1.trans h2.symm)

theorem card_alternatingGroup_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card]
  have h := two_mul_card_alternatingGroup (α := Fin 6)
  rw [Fintype.card_perm, Fintype.card_fin] at h
  have h720 : Nat.factorial 6 = 720 := rfl
  omega

theorem nonempty_equiv_of_lieModel {X : Type} [Group X] (h : Blueprint.LieModel X .PSL 2 3 2) :
    Nonempty (X ≃* alternatingGroup (Fin 6)) :=
  CFSG.Blueprint.LieModel.nonempty_mulEquiv_alternating_six h

theorem card_eq_of_lieModel {X : Type} [Group X]
    (h : Blueprint.LieModel (X ⧸ pPrimeCore 2 X) .PSL 2 3 2) :
    Nat.card X = 360 * Nat.card ↥(pPrimeCore 2 X) := by
  obtain ⟨e⟩ := nonempty_equiv_of_lieModel h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 X), Nat.card_congr e.toEquiv,
    card_alternatingGroup_six]

theorem card_dvd_two_mul_of_map_le {Y Q : Type*} [Group Y] [Group Q] {t : Y}
    (ht2 : t * t = 1) (ρ : Y →* Q) (hker : ∀ y, ρ y = 1 → y = 1 ∨ y = t) {K : Subgroup Y}
    {M : Subgroup Q} (hKM : ∀ k ∈ K, ρ k ∈ M) : Nat.card K ∣ 2 * Nat.card M := by
  let f : ↥K →* Q := ρ.comp K.subtype
  have hr : f.range ≤ M := by
    rintro _ ⟨k, rfl⟩
    exact hKM k k.2
  have hk : Nat.card f.ker ∣ 2 := by
    have hle : f.ker.map K.subtype ≤ zpowers t := by
      rintro _ ⟨k, hk, rfl⟩
      show (k : Y) ∈ zpowers t
      rcases hker (k : Y) (MonoidHom.mem_ker.mp hk) with h | h
      · rw [h]
        exact one_mem _
      · rw [h]
        exact mem_zpowers t
    have h1 := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective K.subtype_injective, Nat.card_zpowers] at h1
    exact h1.trans (orderOf_dvd_of_pow_eq_one (by rw [sq]; exact ht2))
  rw [← Subgroup.card_ker_mul_card_range f]
  exact Nat.mul_dvd_mul hk (Subgroup.card_dvd_of_le hr)

theorem nonempty_generalizedFitting_equiv {Y Q : Type} [Group Y] [Finite Y] [Group Q] {t : Y}
    (ht : t ∈ center Y) (ht1 : t ≠ 1) (ht2 : t * t = 1) (ρ : Y →* Q)
    (hker : ∀ y, ρ y = 1 → y = 1 ∨ y = t) {W : Y} (hWW : W * W = t) {C₂ D : Subgroup Q}
    (hWC : ∀ c ∈ centralizer ({W} : Set Y), ρ c ∈ C₂) (hC₂ : Nat.card C₂ = 2880)
    [IsSimpleGroup D] (hD : Nat.card D = 360) (hDC : D ≤ C₂) (hCD : C₂ ≤ normalizer (D : Set Q))
    (hcent : Nat.card ↥(C₂ ⊓ centralizer (D : Set Q)) = 2) (hWD : ρ W ∈ centralizer (D : Set Q))
    {K : Subgroup Y} (hK : IsTwoComponentIn K (centralizer ({W} : Set Y)))
    (hKm : Blueprint.LieModel (↥K ⧸ pPrimeCore 2 ↥K) .PSL 2 3 2) :
    Nonempty (↥(generalizedFitting ↥(centralizer ({W} : Set Y))) ≃*
      Multiplicative (ZMod 4) × ↥(alternatingGroup (Fin 6))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite C₂ := Nat.finite_of_card_ne_zero (by rw [hC₂]; norm_num)
  set C := centralizer ({W} : Set Y) with hCdef
  have hKC : K ≤ C := hK.1
  have hKcard := card_eq_of_lieModel hKm
  have hO : pPrimeCore 2 ↥K = ⊥ := by
    have hKdvd : Nat.card K ∣ 2 * Nat.card C₂ :=
      card_dvd_two_mul_of_map_le ht2 ρ hker fun k hk => hWC k (hKC hk)
    rw [hKcard, hC₂, show (2 : ℕ) * 2880 = 360 * 2 ^ 4 by norm_num] at hKdvd
    have h16 := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 360) hKdvd
    have hcop : Nat.Coprime (Nat.card ↥(pPrimeCore 2 ↥K)) (2 ^ 4) :=
      (Nat.Coprime.pow_left 4 (pPrimeCore_coprime_card (p := 2) (G := ↥K))).symm
    exact Subgroup.eq_bot_of_card_eq _ (Nat.Coprime.eq_one_of_dvd hcop h16)
  have := isSimpleGroup_of_lieModel_psl2 hKm
  let eK : ↥K ≃* ↥K ⧸ pPrimeCore 2 ↥K :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hO.symm)
  have hKs : IsSimpleGroup ↥K := eK.isSimpleGroup
  have hKnab : ∃ a b : ↥K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := nonabelian_of_lieModel_psl2 hKm
    exact ⟨eK.symm a, eK.symm b, fun h => hab (by simpa using congrArg eK h)⟩
  have hK360 : Nat.card K = 360 := by rw [hKcard, hO, Subgroup.card_bot, mul_one]
  let f : ↥K →* Q := ρ.comp K.subtype
  have hfinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases hKs.eq_bot_or_eq_top_of_normal f.ker with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hKnab
      apply hab
      have ha : (a : Y) ∈ center Y := by
        have h1 : f a = 1 := MonoidHom.mem_ker.mp (h ▸ mem_top a)
        rcases hker (a : Y) h1 with h2 | h2
        · rw [h2]
          exact one_mem _
        · rw [h2]
          exact ht
      exact Subtype.ext (mem_center_iff.mp ha (b : Y)).symm
  have hRC : f.range ≤ C₂ := by
    rintro _ ⟨k, rfl⟩
    exact hWC k (hKC k.2)
  have hR : Nat.card f.range = 360 := by
    rw [← hK360]
    exact (Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv).symm
  have hRD : f.range = D := by
    have hRs : IsSimpleGroup f.range := (MonoidHom.ofInjective hfinj).symm.isSimpleGroup
    have hn : ((D ⊓ f.range).subgroupOf f.range).Normal := by
      rw [normal_subgroupOf_iff inf_le_right]
      intro x y hx hy
      exact ⟨(mem_normalizer_iff.mp (hCD (hRC hy)) x).mp hx.1,
        f.range.mul_mem (f.range.mul_mem hy hx.2) (f.range.inv_mem hy)⟩
    rcases hRs.eq_bot_or_eq_top_of_normal ((D ⊓ f.range).subgroupOf f.range) with h | h
    · exfalso
      have : (D.subgroupOf C₂).Normal := (normal_subgroupOf_iff_le_normalizer hDC).mpr hCD
      let φ : ↥f.range →* ↥C₂ ⧸ D.subgroupOf C₂ :=
        (QuotientGroup.mk' _).comp (Subgroup.inclusion hRC)
      have hφ : Function.Injective φ := by
        rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
        intro x hx
        have h1 : Subgroup.inclusion hRC x ∈ D.subgroupOf C₂ := by
          rw [← QuotientGroup.ker_mk' (D.subgroupOf C₂)]
          exact hx
        have h3 : x ∈ (D ⊓ f.range).subgroupOf f.range :=
          mem_subgroupOf.mpr ⟨mem_subgroupOf.mp h1, x.2⟩
        rw [h] at h3
        exact h3
      have hle := Nat.card_le_card_of_injective φ hφ
      have hq : Nat.card (↥C₂ ⧸ D.subgroupOf C₂) * 360 = 2880 := by
        rw [← hC₂, Subgroup.card_eq_card_quotient_mul_card_subgroup (D.subgroupOf C₂),
          Nat.card_congr (subgroupOfEquivOfLe hDC).toEquiv, hD]
      rw [hR] at hle
      omega
    · have hle : f.range ≤ D := by
        intro x hx
        have h1 : (⟨x, hx⟩ : f.range) ∈ (D ⊓ f.range).subgroupOf f.range := h ▸ mem_top _
        exact (mem_subgroupOf.mp h1).1
      have : Finite D := Nat.finite_of_card_ne_zero (by rw [hD]; norm_num)
      exact Subgroup.eq_of_le_of_card_ge hle (by rw [hD, hR])
  have hDK : ∀ d ∈ D, ∃ k ∈ K, ρ k = d := by
    intro d hd
    rw [← hRD] at hd
    obtain ⟨⟨k, hk⟩, rfl⟩ := hd
    exact ⟨k, hk, rfl⟩
  have hWz : t ∈ zpowers W := by
    rw [← hWW]
    exact mul_mem (mem_zpowers W) (mem_zpowers W)
  have hW1 : ρ W ≠ 1 := by
    intro h
    rcases hker W h with h' | h'
    · apply ht1
      rw [← hWW, h', one_mul]
    · apply ht1
      rw [h'] at hWW
      calc t = t * t := hWW.symm
        _ = 1 := ht2
  have hWmem : ρ W ∈ C₂ ⊓ centralizer (D : Set Q) :=
    ⟨hWC W (mem_centralizer_singleton_iff.mpr rfl), hWD⟩
  have hcomm_mem : ∀ y ∈ C, (∀ k ∈ K, y * k = k * y) → y ∈ zpowers W := by
    intro y hy hyK
    have hyD : ρ y ∈ centralizer (D : Set Q) := by
      rw [mem_centralizer_iff]
      intro d hd
      obtain ⟨k, hk, rfl⟩ := hDK d hd
      rw [← map_mul, ← map_mul, hyK k hk]
    rcases eq_one_or_eq_of_card_eq_two hcent hWmem hW1 ⟨hWC y hy, hyD⟩ with h | h
    · rcases hker y h with h' | h'
      · rw [h']
        exact one_mem _
      · rw [h']
        exact hWz
    · have h1 : ρ (y * W⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
      have h2 : y = y * W⁻¹ * W := by group
      rw [h2]
      refine mul_mem ?_ (mem_zpowers W)
      rcases hker _ h1 with h3 | h3
      · rw [h3]
        exact one_mem _
      · rw [h3]
        exact hWz
  have hKq : IsQuasisimple ↥(K.subgroupOf C) := by
    let e1 := subgroupOfEquivOfLe hKC
    have : IsSimpleGroup ↥(K.subgroupOf C) := e1.isSimpleGroup
    obtain ⟨a, b, hab⟩ := hKnab
    refine (LocalCores.isQuasisimple_of_isSimpleGroup ⟨e1.symm a, e1.symm b, fun h => hab ?_⟩).1
    simpa using congrArg e1 h
  have hKcomp : IsComponent (K.subgroupOf C) := ⟨hKq, hK.2.1⟩
  have hlayer : layer ↥C = K.subgroupOf C := by
    refine le_antisymm (sSup_le fun L hL => ?_) (le_sSup hKcomp)
    rcases LocalCores.distinct_components_commute hL hKcomp with h | h
    · exact h.le
    · exfalso
      have hLz : ∀ l ∈ L, ((l : C) : Y) ∈ zpowers W := by
        intro l hl
        refine hcomm_mem _ l.2 fun k hk => ?_
        have h1 := (commutator_eq_bot_iff_le_centralizer.mp h) hl
        rw [mem_centralizer_iff] at h1
        exact (congrArg Subtype.val (h1 ⟨k, hKC hk⟩ (mem_subgroupOf.mpr hk))).symm
      obtain ⟨a, b, hab⟩ := exists_mul_ne_mul hL.1
      apply hab
      obtain ⟨i, hi⟩ := mem_zpowers_iff.mp (hLz _ a.2)
      obtain ⟨j, hj⟩ := mem_zpowers_iff.mp (hLz _ b.2)
      apply Subtype.ext
      apply Subtype.ext
      change ((a : C) : Y) * ((b : C) : Y) = ((b : C) : Y) * ((a : C) : Y)
      rw [← hi, ← hj]
      exact (Commute.zpow_zpow_self W i j).eq
  have hzC : zpowers W ≤ C := by
    rw [zpowers_le]
    exact mem_centralizer_singleton_iff.mpr rfl
  have hZW : (zpowers W).subgroupOf C ≤ center ↥C := by
    intro x hx
    rw [mem_center_iff]
    intro g
    apply Subtype.ext
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp (mem_subgroupOf.mp hx)
    change (g : Y) * (x : Y) = (x : Y) * (g : Y)
    rw [← hi]
    exact (Commute.zpow_right (mem_centralizer_singleton_iff.mp g.2) i).eq
  have hfit : fittingSubgroup ↥C = (zpowers W).subgroupOf C := by
    apply le_antisymm
    · intro x hx
      have h1 : ⁅fittingSubgroup ↥C, layer ↥C⁆ = ⊥ := LocalCores.fitting_layer_commute
      rw [hlayer] at h1
      have h2 := (commutator_eq_bot_iff_le_centralizer.mp h1) hx
      rw [mem_centralizer_iff] at h2
      refine mem_subgroupOf.mpr (hcomm_mem _ x.2 fun k hk => ?_)
      exact (congrArg Subtype.val (h2 ⟨k, hKC hk⟩ (mem_subgroupOf.mpr hk))).symm
    · have : ((zpowers W).subgroupOf C).Normal := Subgroup.normal_of_le_center hZW
      have : IsMulCommutative ↥((zpowers W).subgroupOf C) :=
        ⟨⟨fun a b => Subtype.ext (mem_center_iff.mp (hZW a.2) b).symm⟩⟩
      exact le_sSup ⟨inferInstance, inferInstance⟩
  set A := (zpowers W).subgroupOf C with hA
  set B := K.subgroupOf C with hB
  have hgf : generalizedFitting ↥C = A ⊔ B := by
    rw [generalizedFitting, hfit, hlayer]
  have hcomm : ∀ (a : A) (b : B), Commute (A.subtype a) (B.subtype b) := fun a b =>
    (mem_center_iff.mp (hZW a.2) b).symm
  have hd : Disjoint A B := by
    rw [disjoint_iff, eq_bot_iff]
    rintro x ⟨hxA, hxB⟩
    have hxK : ((x : C) : Y) ∈ K := mem_subgroupOf.mp hxB
    have hxZ : (⟨(x : Y), hxK⟩ : K) ∈ center ↥K := by
      rw [mem_center_iff]
      intro k
      exact Subtype.ext (show (k : Y) * ((x : C) : Y) = ((x : C) : Y) * (k : Y) from
        congrArg Subtype.val (mem_center_iff.mp (hZW hxA) ⟨k, hKC k.2⟩))
    rw [(LocalCores.isQuasisimple_of_isSimpleGroup hKnab).2, mem_bot] at hxZ
    have h1 : ((x : C) : Y) = 1 := congrArg Subtype.val hxZ
    exact mem_bot.mpr (Subtype.ext h1)
  have hinj : Function.Injective (A.subtype.noncommCoprod B.subtype hcomm) := by
    rw [MonoidHom.noncommCoprod_injective]
    exact ⟨A.subtype_injective, B.subtype_injective, by simpa only [range_subtype] using hd⟩
  let ePS : A × B ≃* ↥(A ⊔ B) := (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr (by
    rw [MonoidHom.noncommCoprod_range, range_subtype, range_subtype]))
  have hW4 : orderOf W = 4 := by
    have h1 : ¬ W ^ 2 ^ 1 = 1 := by
      rw [pow_one, sq, hWW]
      exact ht1
    have h2 : W ^ 2 ^ (1 + 1) = 1 := by
      have h3 : W ^ 2 = t := by rw [sq, hWW]
      rw [show (2 : ℕ) ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, h3, sq, ht2]
    simpa using orderOf_eq_prime_pow h1 h2
  have key : Nonempty (Multiplicative (ZMod (Nat.card (zpowers W))) ≃* zpowers W) :=
    ⟨zmodCyclicMulEquiv inferInstance⟩
  rw [Nat.card_zpowers, hW4] at key
  obtain ⟨eZ⟩ := key
  obtain ⟨eA⟩ := nonempty_equiv_of_lieModel hKm
  rw [hgf]
  exact ⟨ePS.symm.trans (MulEquiv.prodCongr ((subgroupOfEquivOfLe hzC).trans eZ.symm)
    ((subgroupOfEquivOfLe hKC).trans (eK.trans eA)))⟩

end HS2B

end CFSG.ComponentClassification.HarrisLit.N36
