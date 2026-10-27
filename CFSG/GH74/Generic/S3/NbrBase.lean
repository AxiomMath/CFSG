module

public import CFSG.GH74.Generic.S3.PumpLift
public import CFSG.GH74.Generic.S3.PumpDiag
public import CFSG.GH74.Generic.S3.LeavesR
public import CFSG.GH74.Generic.S3.Conf
public import CFSG.GH74.Generic.S3.Nbhd
public import CFSG.GH74.Generic.S3.L3Sylow
public import CFSG.GH74.Generic.S3.Front
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalComponent
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.Generic.S3.Terminal

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.Blueprint CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank Subgroup
  CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

theorem normal_of_component_gen4 {X : Type} [Group X] [Finite X] (hX : Gen4 X) {c : X}
    (hc : ∀ g : X, g * c = c * g) (hc2 : c * c = 1) (hc1 : c ≠ 1) {K : Subgroup X}
    (hK : IsComponent K) (hKc : ∀ k : ↥K, (∀ k' : ↥K, k' * k = k * k') → k = 1)
    (hK1 : RankCertified ↥K 1) : K.Normal := by
  refine ⟨fun n hn g => ?_⟩
  by_contra hmem
  set K' : Subgroup X := conjSub g K with hK'
  have hK'c : IsComponent K' := isComponent_conjSub hK g
  have hgn : g * n * g⁻¹ ∈ K' := ⟨n, hn, by simp [MulAut.conj_apply]⟩
  have hne : K ≠ K' := fun h => hmem (h ▸ hgn)
  have hcomm : ⁅K, K'⁆ = ⊥ := (CFSG.LocalCores.distinct_components_commute hK hK'c).resolve_left hne
  have hKK' : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a := by
    intro a ha b hb
    have := Subgroup.commutator_mem_commutator ha hb
    rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  have hinf : ∀ a ∈ K, a ∈ K' → a = 1 := by
    intro a ha ha'
    have := hKc ⟨a, ha⟩ (fun k' => Subtype.ext (hKK' k' k'.2 a ha'))
    exact congrArg Subtype.val this
  have hK1' : RankCertified ↥K' 1 :=
    hK1.of_mulEquiv (K.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)
  let φ : ↥K × ↥K' →* X := MonoidHom.noncommCoprod K.subtype K'.subtype
    (fun a b => hKK' a a.2 b b.2)
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ hab
    have h1 : (a : X) * b = 1 := hab
    have ha' : (a : X) ∈ K' := by
      have : (a : X) = (b : X)⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]; exact K'.inv_mem b.2
    have ha1 := hinf a a.2 ha'
    have hb1 : (b : X) = 1 := by rw [ha1, one_mul] at h1; exact h1
    exact Prod.ext (Subtype.ext ha1) (Subtype.ext hb1)
  have hcert : RankCertified ↥φ.range 3 :=
    (hK1.prod hK1').of_mulEquiv (MonoidHom.ofInjective hφ)
  have hcB : c ∉ φ.range := by
    rintro ⟨⟨a, b⟩, hab⟩
    have h1 : (a : X) * b = c := hab
    have hb' : (b : X)⁻¹ ∈ K' := K'.inv_mem b.2
    have h2 : (a : X) = c * (b : X)⁻¹ := by rw [← h1]; group
    have ha1 : (a : X) = 1 := by
      have := hKc a (fun k' => by
        apply Subtype.ext
        change (k' : X) * a = a * k'
        calc (k' : X) * a = k' * (c * (b : X)⁻¹) := by rw [h2]
          _ = c * (k' * (b : X)⁻¹) := by rw [← mul_assoc, hc k', mul_assoc]
          _ = c * ((b : X)⁻¹ * k') := by rw [hKK' k' k'.2 _ hb']
          _ = (c * (b : X)⁻¹) * k' := by rw [mul_assoc]
          _ = a * k' := by rw [h2])
      exact congrArg Subtype.val this
    have hbc : (b : X) = c := by rw [ha1, one_mul] at h1; exact h1
    have hcK' : c ∈ K' := hbc ▸ b.2
    obtain ⟨k, hk, hkc⟩ := hcK'
    have hkc' : k = c := by
      have e1 : g * k * g⁻¹ = c := by simpa [MulAut.conj_apply] using hkc
      have e2 : g * c = c * g := hc g
      calc k = g⁻¹ * (g * k * g⁻¹) * g := by group
        _ = g⁻¹ * c * g := by rw [e1]
        _ = c := by rw [show g⁻¹ * c * g = g⁻¹ * (c * g) from mul_assoc _ _ _, ← e2]; group
    have hcK : c ∈ K := hkc' ▸ hk
    have := hKc ⟨c, hcK⟩ (fun k' => Subtype.ext (hc k'))
    exact hc1 (congrArg Subtype.val this)
  have := RankCertified.of_central_involution (K := φ.range) hc hc2 hcB hcert
  exact this.not_gen4 (by norm_num) hX


theorem odd_card_of_forall_odd_orderOf {A : Type*} [Group A] [Finite A]
    (h : ∀ a : A, Odd (orderOf a)) : Odd (Nat.card A) := by
  by_contra hev
  have h2 : 2 ∣ Nat.card A := by
    rcases Nat.even_or_odd (Nat.card A) with he | ho
    · exact even_iff_two_dvd.1 he
    · exact absurd ho hev
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := A) 2 h2
  have := h a
  rw [ha] at this
  exact absurd this (by decide)

theorem center_eq_bot_of_isSimpleGroup {K : Type*} [Group K] (hs : IsSimpleGroup K)
    (hn : ∃ a b : K, a * b ≠ b * a) : center K = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center K) with hb | ht
  · exact hb
  · exfalso
    obtain ⟨a, b, hab⟩ := hn
    apply hab
    have : a ∈ center K := by rw [ht]; exact Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.1 this b).symm

section Lift

variable {G : Type} [Group G] [Finite G] {z : G} {L : Subgroup (CentralizerBar z)}


theorem exists_centralQuot
    (hcentral : ∀ n ∈ S1.liftL z L, proj z n = 1 → ∀ l ∈ S1.liftL z L, n * l = l * n)
    (hL : ⁅L, L⁆ = L) (hLc : ∀ k : ↥L, (∀ k' : ↥L, k' * k = k * k') → k = 1) :
    ∃ ψ : ↥(liftSub z L) →* ↥L, Function.Surjective ψ ∧ ψ.ker = center ↥(liftSub z L) ∧
      ∀ m : ↥(liftSub z L), (ψ m : CentralizerBar z) = proj z ⟨(m : G), liftSub_le m.2⟩ := by
  have himg : imgBar z (liftSub z L) = L := imgBar_liftSub hL
  have hmem : ∀ m : ↥(liftSub z L), proj z ⟨(m : G), liftSub_le m.2⟩ ∈ L := by
    intro m
    have h := mem_imgBar.2 (show ∃ g : ↥(centralizer ({z} : Set G)), (g : G) ∈ liftSub z L ∧
      proj z g = proj z ⟨(m : G), liftSub_le m.2⟩ from ⟨⟨m, liftSub_le m.2⟩, m.2, rfl⟩)
    rwa [himg] at h
  let ψ : ↥(liftSub z L) →* ↥L :=
    ((proj z).comp (Subgroup.inclusion liftSub_le)).codRestrict L hmem
  have hψ : Function.Surjective ψ := by
    rintro ⟨k, hk⟩
    rw [← himg] at hk
    obtain ⟨g, hgM, rfl⟩ := mem_imgBar.1 hk
    exact ⟨⟨g, hgM⟩, rfl⟩
  refine ⟨ψ, hψ, ?_, fun m => rfl⟩
  ext m
  constructor
  · intro hm
    rw [Subgroup.mem_center_iff]
    intro n
    apply Subtype.ext
    have h1 : proj z ⟨(m : G), liftSub_le m.2⟩ = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hm)
    exact (liftSub_kernel_central hcentral m.2 (liftSub_le m.2) h1 n n.2).symm
  · intro hm
    rw [MonoidHom.mem_ker]
    apply hLc
    intro k'
    obtain ⟨n, rfl⟩ := hψ k'
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hm n]

theorem liftSub_center_odd
    (hcentral : ∀ n ∈ S1.liftL z L, proj z n = 1 → ∀ l ∈ S1.liftL z L, n * l = l * n)
    (hL : ⁅L, L⁆ = L) (hLc : ∀ k : ↥L, (∀ k' : ↥L, k' * k = k * k') → k = 1) :
    Odd (Nat.card ↥(center ↥(liftSub z L))) := by
  obtain ⟨ψ, hψ, hker, hψapp⟩ := exists_centralQuot hcentral hL hLc
  apply odd_card_of_forall_odd_orderOf
  intro c
  have hc : (c : ↥(liftSub z L)) ∈ ψ.ker := by rw [hker]; exact c.2
  have h1 : proj z ⟨((c : ↥(liftSub z L)) : G), liftSub_le (c : ↥(liftSub z L)).2⟩ = 1 := by
    have := congrArg Subtype.val (MonoidHom.mem_ker.1 hc)
    rw [hψapp] at this
    exact this
  have h2 := proj_odd z ⟨((c : ↥(liftSub z L)) : G), liftSub_le (c : ↥(liftSub z L)).2⟩ h1
  rw [← Subgroup.orderOf_coe c, ← Subgroup.orderOf_coe (c : ↥(liftSub z L))]
  rwa [← Subgroup.orderOf_mk _ (liftSub_le (c : ↥(liftSub z L)).2)]

theorem liftSub_model
    (hcentral : ∀ n ∈ S1.liftL z L, proj z n = 1 → ∀ l ∈ S1.liftL z L, n * l = l * n)
    (hL : ⁅L, L⁆ = L) (hLc : ∀ k : ↥L, (∀ k' : ↥L, k' * k = k * k') → k = 1)
    {t : StatedLieTag} {p f : ℕ} (hmodel : LieModel ↥L t 3 p f) :
    LieModel (↥(liftSub z L) ⧸ center ↥(liftSub z L)) t 3 p f := by
  obtain ⟨ψ, hψ, hker, -⟩ := exists_centralQuot hcentral hL hLc
  let e : ↥(liftSub z L) ⧸ center ↥(liftSub z L) ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
  exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm hmodel

theorem liftSub_isNormCompC
    (hcentral : ∀ n ∈ S1.liftL z L, proj z n = 1 → ∀ l ∈ S1.liftL z L, n * l = l * n)
    (hLc : IsComponent L) (hLs : IsSimpleGroup ↥L) (hLn : L.Normal) :
    IsNormCompC (liftSub z L) z := by
  have hKperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hLc.1.1
  have hKn : ∃ a b : ↥L, a * b ≠ b * a := S45.exists_noncomm_of_isQuasisimple hLc.1
  have hq : IsQuasisimple ↥(liftSub z L) := liftSub_isQuasisimple hcentral hLs hKn hKperf
  have hsub : ((liftSub z L).subgroupOf (centralizer ({z} : Set G))).IsSubnormal := by
    rw [liftSub_subgroupOf]
    exact liftL_isSubnormal hLc.2
  refine ⟨⟨liftSub_le, ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (subgroupOfEquivOfLe liftSub_le).symm hq, hsub⟩⟩, ?_⟩
  have := hLn
  rw [liftSub_subgroupOf]
  exact S1.liftL_normal

theorem noCommInv_of_onlyInv (hL : ⁅L, L⁆ = L) (honly : OnlyInvX z L) (hz : orderOf z = 2)
    {P : Subgroup G} (hPz : P ≤ centralizer ({z} : Set G))
    (hPL : P ≤ centralizer ((liftSub z L : Subgroup G) : Set G)) : NoCommInv P := by
  intro a ha b hb ha2 hb2 hab
  by_cases ha1 : a = 1
  · exact Or.inl ha1
  by_cases hb1 : b = 1
  · exact Or.inr (Or.inl hb1)
  right; right
  have himg : imgBar z (liftSub z L) = L := imgBar_liftSub hL
  have key : ∀ c (hc : c ∈ P), c * c = 1 → c ≠ 1 → proj z ⟨c, hPz hc⟩ = xbar z := by
    intro c hc hc2 hc1
    have hcz := hPz hc
    have hcb1 : proj z ⟨c, hcz⟩ ≠ 1 := fun h => hc1 (S45.eq_one_of_proj_eq_one_of_sq hcz h hc2)
    have hcb2 : proj z ⟨c, hcz⟩ * proj z ⟨c, hcz⟩ = 1 := by
      rw [← map_mul]
      have : (⟨c, hcz⟩ : ↥(centralizer ({z} : Set G))) * ⟨c, hcz⟩ = 1 := Subtype.ext hc2
      rw [this, map_one]
    have hord : orderOf (proj z ⟨c, hcz⟩) = 2 := orderOf_eq_prime (by rw [sq]; exact hcb2) hcb1
    have hcent : proj z ⟨c, hcz⟩ ∈ centralizer (L : Set (CentralizerBar z)) := by
      rw [mem_centralizer_iff]
      intro l hl
      have hl' : l ∈ imgBar z (liftSub z L) := by rw [himg]; exact hl
      obtain ⟨g, hg, rfl⟩ := mem_imgBar.1 hl'
      have h1 : (g : G) * c = c * (g : G) := mem_centralizer_iff.1 (hPL hc) (g : G) hg
      have h2 : g * ⟨c, hcz⟩ = ⟨c, hcz⟩ * g := Subtype.ext h1
      rw [← map_mul, ← map_mul, h2]
    exact honly _ hcent hord
  have h1 := key a ha ha2 ha1
  have h2 := key b hb hb2 hb1
  have habz : a * b ∈ centralizer ({z} : Set G) :=
    (centralizer ({z} : Set G)).mul_mem (hPz ha) (hPz hb)
  have hab2 : (a * b) * (a * b) = 1 := by
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha2, hb2, one_mul]
  have himgab : proj z ⟨a * b, habz⟩ = 1 := by
    have : (⟨a * b, habz⟩ : ↥(centralizer ({z} : Set G))) = ⟨a, hPz ha⟩ * ⟨b, hPz hb⟩ := rfl
    rw [this, map_mul, h1, h2]
    exact xbar_mul_self hz
  have h3 := S45.eq_one_of_proj_eq_one_of_sq habz himgab hab2
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  calc a = a * b * b⁻¹ := by group
    _ = b := by rw [h3, one_mul, hb']


end Lift

theorem exists_T_y {G : Type} [Group G] [Finite G] {t : StatedLieTag} {p f : ℕ} (ht : t = .PSL ∨ t = .PSU) (hp : p.Prime) (hp2 : p ≠ 2)
    (h5 : 5 ≤ p ^ f) {x : G} (hx : orderOf x = 2) {Iw : Subgroup G} (hIw : IsNormCompC Iw x)
    (hodd : Odd (Nat.card ↥(center ↥Iw))) (hmodel : LieModel (↥Iw ⧸ center ↥Iw) t 3 p f) :
    ∃ (T : Subgroup G) (y : G), IsSylowOf 2 T (centralizer ({x} : Set G)) ∧ x ∈ T ∧ y ∈ T ⊓ Iw ∧
      orderOf y = 2 ∧ (∀ r ∈ T ⊓ Iw, r * y = y * r) ∧
      (∀ z ∈ T ⊓ Iw, (∀ r ∈ T ⊓ Iw, r * z = z * r) → z * z = 1 → z = 1 ∨ z = y) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := exists_isSylowOf (G := G) 2 (centralizer ({x} : Set G))
  have hxT : x ∈ T := by
    obtain ⟨Q, hQ⟩ := hT
    have hxC : x ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
    set x' : ↥(centralizer ({x} : Set G)) := ⟨x, hxC⟩ with hx'
    have hx'2 : x' * x' = 1 := Subtype.ext (by
      change x * x = 1
      have := pow_orderOf_eq_one x
      rwa [hx, pow_two] at this)
    have hcen : ∀ g : ↥(centralizer ({x} : Set G)), g * x' = x' * g := fun g =>
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 g.2)
    have hN : (Subgroup.zpowers x').Normal := by
      refine ⟨fun n hn g => ?_⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
      have hc : g * x' * g⁻¹ = x' := by rw [hcen g]; group
      have : g * x' ^ k * g⁻¹ = x' ^ k := by
        rw [← conj_zpow]; simp [hc]
      rw [this]
      exact Subgroup.zpow_mem_zpowers x' k
    have hNp : IsPGroup 2 ↥(Subgroup.zpowers x') :=
      isPGroup_zpowers_of_pow_two_pow_eq_one (n := 1) (by simpa [pow_two] using hx'2)
    have hle := IsPGroup.le_sylow_of_normal hNp Q
    have hx'Q : x' ∈ (Q : Subgroup ↥(centralizer ({x} : Set G))) := hle (Subgroup.mem_zpowers x')
    rw [← hQ]
    exact ⟨x', hx'Q, rfl⟩
  have hnormalizer : centralizer ({x} : Set G) ≤ normalizer (Iw : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hIw.1.1).1 hIw.2
  have hR : IsSylowOf 2 (T ⊓ Iw) Iw := hT.inf_of_le_normalizer hIw.1.1 hnormalizer
  have hq : IsQuasisimple ↥Iw := hIw.1.isQuasisimple
  obtain ⟨hcyc, -⟩ := b_L3_sylow G t p f ht hp hp2 h5 Iw hq hodd hmodel (T ⊓ Iw) hR
  obtain ⟨e, heI, he2, he1⟩ := exists_involution_mem_of_quasisimple hq
  have hRp : IsPGroup 2 ↥(T ⊓ Iw) := hR.isPGroup
  have hRnt : Nontrivial ↥(T ⊓ Iw) := by
    have hcard := hR.card_eq
    have h2 : 2 ∣ Nat.card ↥Iw := by
      have hord : orderOf e = 2 := orderOf_eq_prime (by rw [sq]; exact he2) he1
      rw [← hord]
      exact Subgroup.orderOf_dvd_natCard Iw heI
    have hpos : 1 ≤ (Nat.card ↥Iw).factorization 2 := by
      have hne : Nat.card ↥Iw ≠ 0 := Nat.card_pos.ne'
      exact (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hne).1 h2
    have : 1 < Nat.card ↥(T ⊓ Iw) := by
      rw [hcard]
      calc 1 < 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (Nat.card ↥Iw).factorization 2 := Nat.pow_le_pow_right (by norm_num) hpos
    exact Finite.one_lt_card_iff_nontrivial.1 this
  have hZnt : Nontrivial ↥(center ↥(T ⊓ Iw)) := hRp.center_nontrivial
  have hZp : IsPGroup 2 ↥(center ↥(T ⊓ Iw)) := hRp.to_subgroup (center ↥(T ⊓ Iw))
  obtain ⟨n, hn⟩ := hZp.exists_card_eq
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h, pow_zero] at hn
      exact absurd (Nat.card_eq_one_iff_unique.1 hn).1 (not_subsingleton _)
    · exact h
  have h2Z : 2 ∣ Nat.card ↥(center ↥(T ⊓ Iw)) := by
    rw [hn]; exact dvd_pow_self 2 (by omega)
  obtain ⟨y₀, hy₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥(center ↥(T ⊓ Iw))) 2 h2Z
  set y : G := (((y₀ : ↥(center ↥(T ⊓ Iw))) : ↥(T ⊓ Iw)) : G) with hy
  have hyR : y ∈ T ⊓ Iw := ((y₀ : ↥(center ↥(T ⊓ Iw))) : ↥(T ⊓ Iw)).2
  have hyord : orderOf y = 2 := by
    rw [hy, Subgroup.orderOf_coe, Subgroup.orderOf_coe]; exact hy₀
  have hycen : ∀ r ∈ T ⊓ Iw, r * y = y * r := by
    intro r hr
    have := Subgroup.mem_center_iff.1 y₀.2 ⟨r, hr⟩
    exact congrArg Subtype.val this
  refine ⟨T, y, hT, hxT, hyR, hyord, hycen, ?_⟩
  intro z hz hzc hz2
  by_contra hne
  push Not at hne
  obtain ⟨hz1, hzy⟩ := hne
  have hZs : ∀ a ∈ T ⊓ Iw, (∀ r ∈ T ⊓ Iw, r * a = a * r) →
      a ∈ (T ⊓ Iw) ⊓ centralizer (((T ⊓ Iw : Subgroup G)) : Set G) := by
    intro a ha hac
    exact ⟨ha, Subgroup.mem_centralizer_iff.2 fun r hr => hac r hr⟩
  have hyZ := hZs y hyR (fun r hr => (hycen r hr))
  have hzZ := hZs z hz hzc
  have : Fintype ↥((T ⊓ Iw) ⊓ centralizer (((T ⊓ Iw : Subgroup G)) : Set G)) := Fintype.ofFinite _
  have hle := IsCyclic.card_pow_eq_one_le (α := ↥((T ⊓ Iw) ⊓ centralizer (((T ⊓ Iw : Subgroup G)) : Set G)))
    (n := 2) (by norm_num)
  have hy2' : y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hyord, pow_two] at this
  have hsub : ({1, ⟨y, hyZ⟩, ⟨z, hzZ⟩} :
      Finset ↥((T ⊓ Iw) ⊓ centralizer (((T ⊓ Iw : Subgroup G)) : Set G))) ⊆
      Finset.univ.filter (fun a => a ^ 2 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl
    · simp
    · ext; simpa [pow_two] using hy2'
    · ext; simpa [pow_two] using hz2
  have hcard : ({1, ⟨y, hyZ⟩, ⟨z, hzZ⟩} :
      Finset ↥((T ⊓ Iw) ⊓ centralizer (((T ⊓ Iw : Subgroup G)) : Set G))).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp only [Finset.mem_singleton]
      intro h'
      exact hzy (congrArg Subtype.val h').symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨fun h' => ?_, fun h' => hz1 (congrArg Subtype.val h').symm⟩
      have : y = 1 := congrArg Subtype.val h'.symm
      rw [this, orderOf_one] at hyord
      omega
  have := Finset.card_le_card hsub
  omega

theorem isSubnormal_of_normal_chain {G : Type} [Group G] {V B A : Subgroup G} (hAB : A ≤ B)
    (hA : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ ∈ A) (hB : ∀ v ∈ V, ∀ b ∈ B, v * b * v⁻¹ ∈ B) :
    (A.subgroupOf V).IsSubnormal := by
  have hBn : (B.subgroupOf V).Normal :=
    ⟨fun n hn g => Subgroup.mem_subgroupOf.2 (hB g.1 g.2 n.1 (Subgroup.mem_subgroupOf.1 hn))⟩
  have hAV : A.subgroupOf V ≤ B.subgroupOf V := fun a ha => hAB ha
  refine Subgroup.IsSubnormal.step (A.subgroupOf V) (B.subgroupOf V) hAV hBn.isSubnormal ?_
  refine ⟨fun n hn g => ?_⟩
  have hn' : (n : ↥V) ∈ A.subgroupOf V := hn
  exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2 (hA g.1.1 g.2 n.1.1 hn'))

section Models

variable {G : Type} [Group G] [Finite G]

theorem isSimple_of_model {K : Type} [Group K] {t : StatedLieTag} {p f : ℕ} (ht : t = .PSL ∨ t = .PSU)
    (h : LieModel K t 3 p f) : IsSimpleGroup K := by
  rcases ht with rfl | rfl
  · exact isSimpleGroup_of_lieModel_L3 (Or.inl h)
  · exact isSimpleGroup_of_lieModel_L3 (Or.inr h)

theorem rankCertified_one_of_model {K : Type} [Group K] [Finite K] {t : StatedLieTag} {p f : ℕ}
    (ht : t = .PSL ∨ t = .PSU) (hp2 : p ≠ 2) (h : LieModel K t 3 p f) : RankCertified K 1 := by
  rcases ht with rfl | rfl
  · exact rankCertified_one_of_l3 (Or.inl rfl) hp2 (stated_of_lieModel_PSL h)
  · exact rankCertified_one_of_l3 (Or.inr rfl) hp2 (stated_of_lieModel_PSU h)

theorem centerless_of_model {K : Type} [Group K] {t : StatedLieTag} {p f : ℕ} (ht : t = .PSL ∨ t = .PSU)
    (h : LieModel K t 3 p f) (hnab : ∃ a b : K, a * b ≠ b * a) :
    ∀ k : K, (∀ k' : K, k' * k = k * k') → k = 1 := by
  intro k hk
  have : k ∈ center K := Subgroup.mem_center_iff.2 hk
  rw [center_eq_bot_of_isSimpleGroup (isSimple_of_model ht h) hnab] at this
  exact Subgroup.mem_bot.1 this

end Models

end CFSG.GH74.Generic.S3
