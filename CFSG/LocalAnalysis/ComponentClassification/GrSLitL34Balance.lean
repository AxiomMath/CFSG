module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Cert
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourIndexTwoLocalB
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.InvolutionCountOfFusion
public import CFSG.Sporadic.HeldB.AlmostSimple

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

section Embedding

variable {X : Type} [Group X] [Finite X]

theorem exists_psl34Embedding (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a)
    (hmodel : Blueprint.LieModel (GeneralizedFitting.subgroup X) .PSL 3 2 2) :
    ∃ ψ : X →* Equiv.Perm (Fin 42), Function.Injective ψ ∧ (∀ x, ψ x ∈ R) ∧
      (∀ x : X, x ∈ GeneralizedFitting.subgroup X ↔ ψ x ∈ S) ∧
      ∀ s ∈ S, ∃ x ∈ GeneralizedFitting.subgroup X, ψ x = s := by
  set F := GeneralizedFitting.subgroup X
  have : F.Normal := GeneralizedFitting.normal X
  have hstated : Assembly.LowTwoRank.StatedClassicalModel F .PSL 3 2 2 := by
    rcases hmodel with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    all_goals exact absurd h (by norm_num)
  obtain ⟨θ⟩ := nonempty_equiv_of_stated F hstated
  obtain ⟨e, he, -⟩ := full_automorphism_action
  let ψ₀ : X →* R :=
    e.symm.toMonoidHom.comp ((MulAut.congr θ).toMonoidHom.comp MulAut.conjNormal)
  have hψ : ∀ (t : X) (n : F), (ψ₀ t : Equiv.Perm (Fin 42)) * (θ n : Equiv.Perm (Fin 42)) *
      (ψ₀ t : Equiv.Perm (Fin 42))⁻¹ = (θ (MulAut.conjNormal t n) : Equiv.Perm (Fin 42)) := by
    intro t n
    have h1 := he (ψ₀ t) (θ n)
    have h2 : e (ψ₀ t) = MulAut.congr θ (MulAut.conjNormal t) := e.apply_symm_apply _
    rw [h2] at h1
    rw [← Subgroup.coe_inv, ← h1]
    simp [MulAut.congr]
  have hψF : ∀ n : F, (ψ₀ n : Equiv.Perm (Fin 42)) = θ n := by
    intro n
    have hu : (θ n : Equiv.Perm (Fin 42))⁻¹ * ψ₀ n ∈
        Subgroup.centralizer (S : Set (Equiv.Perm (Fin 42))) ⊓ R := by
      refine ⟨Subgroup.mem_centralizer_iff.2 fun s hs => ?_,
        R.mul_mem (R.inv_mem (S_le_R (θ n).2)) (ψ₀ n).2⟩
      have h := hψ n (θ.symm ⟨s, hs⟩)
      rw [MulEquiv.apply_symm_apply] at h
      have hconj : MulAut.conjNormal (n : X) (θ.symm ⟨s, hs⟩) = n * θ.symm ⟨s, hs⟩ * n⁻¹ :=
        Subtype.ext (by rw [MulAut.conjNormal_apply]; rfl)
      rw [hconj, map_mul, map_mul, map_inv] at h
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulEquiv.apply_symm_apply] at h
      calc s * ((θ n : Equiv.Perm (Fin 42))⁻¹ * ψ₀ n) =
          (θ n : Equiv.Perm (Fin 42))⁻¹ * ((θ n : Equiv.Perm (Fin 42)) * s *
            (θ n : Equiv.Perm (Fin 42))⁻¹) * ψ₀ n := by group
        _ = (θ n : Equiv.Perm (Fin 42))⁻¹ * (ψ₀ n * s * (ψ₀ n : Equiv.Perm (Fin 42))⁻¹) *
            ψ₀ n := by rw [h]
        _ = (θ n : Equiv.Perm (Fin 42))⁻¹ * ψ₀ n * s := by group
    rw [centralizer_S_inf_R, Subgroup.mem_bot] at hu
    exact (inv_mul_eq_one.1 hu).symm
  have hinj : Function.Injective ψ₀ := by
    rw [injective_iff_map_eq_one]
    intro t ht
    have hC : t ∈ Subgroup.centralizer (F : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      have h := hψ t ⟨n, hn⟩
      rw [ht] at h
      simp only [Subgroup.coe_one, one_mul, inv_one, mul_one] at h
      have h' := θ.injective (Subtype.ext h)
      have h'' := congrArg Subtype.val h'
      rw [MulAut.conjNormal_apply] at h''
      calc n * t = t * n * t⁻¹ * t := by rw [← h'']
        _ = t * n := by group
    rw [Sporadic.HeldB.centralizer_generalizedFitting_eq_bot hsimple hnab, Subgroup.mem_bot]
      at hC
    exact hC
  refine ⟨R.subtype.comp ψ₀, (Subgroup.subtype_injective R).comp hinj, fun x => (ψ₀ x).2,
    fun x => ⟨fun hx => ?_, fun hx => ?_⟩, fun s hs => ?_⟩
  · change (ψ₀ x : Equiv.Perm (Fin 42)) ∈ S
    rw [show x = ((⟨x, hx⟩ : F) : X) from rfl, hψF]
    exact (θ ⟨x, hx⟩).2
  · set n := θ.symm ⟨_, hx⟩
    have hn : ψ₀ n = ψ₀ x := by
      apply Subtype.ext
      rw [hψF, MulEquiv.apply_symm_apply]
      rfl
    rw [← hinj hn]
    exact n.2
  · refine ⟨θ.symm ⟨s, hs⟩, (θ.symm ⟨s, hs⟩).2, ?_⟩
    change (ψ₀ (θ.symm ⟨s, hs⟩ : F) : Equiv.Perm (Fin 42)) = s
    rw [hψF, MulEquiv.apply_symm_apply]

end Embedding

theorem card_centralizer_R (x : R) :
    Nat.card (centralizer ({x} : Set R)) =
      Nat.card ↥(centralizer ({(x : Equiv.Perm (Fin 42))} : Set (Equiv.Perm (Fin 42))) ⊓ R) := by
  have hmap : (centralizer ({x} : Set R)).map R.subtype =
      centralizer ({(x : Equiv.Perm (Fin 42))} : Set (Equiv.Perm (Fin 42))) ⊓ R := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨mem_centralizer_singleton_iff.2 ?_, z.2⟩
      have := mem_centralizer_singleton_iff.1 hz
      exact congrArg Subtype.val this
    · rintro ⟨hy, hyR⟩
      refine ⟨⟨y, hyR⟩, mem_centralizer_singleton_iff.2 (Subtype.ext ?_), rfl⟩
      exact mem_centralizer_singleton_iff.1 hy
  rw [← hmap]
  exact (Nat.card_congr ((centralizer ({x} : Set R)).equivMapOfInjective R.subtype
    (Subgroup.subtype_injective R)).toEquiv)

theorem card_centralizer_mul_of_isConj {x r : R} (h : IsConj x r) {m : ℕ}
    (hm : Nat.card (ConjClasses.mk r).carrier = m) :
    Nat.card ↥(centralizer ({(x : Equiv.Perm (Fin 42))} : Set (Equiv.Perm (Fin 42))) ⊓ R) * m =
      241920 := by
  rw [← card_centralizer_R, ← hm, ← (ConjClasses.mk_eq_mk_iff_isConj.2 h),
    GorensteinWalter.card_conjClass_eq_centralizer_index_local x, Subgroup.card_mul_index,
    card_R]

theorem card_centralizer_S_of_isConj {x r : R} (h : IsConj x r) :
    Nat.card ↥(centralizer ({(x : Equiv.Perm (Fin 42))} : Set (Equiv.Perm (Fin 42))) ⊓ S) =
      Nat.card ↥(centralizer ({(r : Equiv.Perm (Fin 42))} : Set (Equiv.Perm (Fin 42))) ⊓ S) := by
  obtain ⟨e⟩ := fixed_of_isConj h
  exact Nat.card_congr e.toEquiv

section Core

variable {X : Type} [Group X] {ψ : X →* Equiv.Perm (Fin 42)}

theorem exists_preimage_of_mem_centralizer_S (hinj : Function.Injective ψ)
    (hS : ∀ s ∈ S, ∃ x ∈ GeneralizedFitting.subgroup X, ψ x = s) {t : X}
    {s : Equiv.Perm (Fin 42)}
    (hs : s ∈ centralizer ({ψ t} : Set (Equiv.Perm (Fin 42))) ⊓ S) :
    ∃ n ∈ GeneralizedFitting.subgroup X, n ∈ centralizer ({t} : Set X) ∧ ψ n = s := by
  obtain ⟨hs1, hs2⟩ := hs
  obtain ⟨n, hnF, rfl⟩ := hS s hs2
  refine ⟨n, hnF, mem_centralizer_singleton_iff.2 (hinj ?_), rfl⟩
  rw [map_mul, map_mul]
  exact mem_centralizer_singleton_iff.1 hs1

theorem coprime_orderOf_of_mem_oddCore [Finite X] {t : X} {d : X}
    (hd : d ∈ (pPrimeCore 2 (centralizer ({t} : Set X))).map
      (centralizer ({t} : Set X)).subtype) : Nat.Coprime 2 (orderOf d) := by
  obtain ⟨d, hd, rfl⟩ := hd
  have hcop := pPrimeCore_coprime_card (p := 2) (G := centralizer ({t} : Set X))
  have hdvd : orderOf d ∣ Nat.card (pPrimeCore 2 (centralizer ({t} : Set X))) := by
    rw [← Subgroup.orderOf_mk d hd]
    exact orderOf_dvd_natCard _
  rw [Subgroup.coe_subtype, Subgroup.orderOf_coe]
  exact hcop.coprime_dvd_right hdvd

theorem conj_mem_oddCore {t c d : X} (hc : c ∈ centralizer ({t} : Set X))
    (hd : d ∈ (pPrimeCore 2 (centralizer ({t} : Set X))).map
      (centralizer ({t} : Set X)).subtype) :
    c * d * c⁻¹ ∈ (pPrimeCore 2 (centralizer ({t} : Set X))).map
      (centralizer ({t} : Set X)).subtype := by
  obtain ⟨d, hd, rfl⟩ := hd
  have hn : (pPrimeCore 2 (centralizer ({t} : Set X))).Normal := inferInstance
  exact ⟨⟨c, hc⟩ * d * ⟨c, hc⟩⁻¹, hn.conj_mem d hd ⟨c, hc⟩, rfl⟩

theorem eq_one_of_coprime_of_pow {G : Type*} [Group G] {g : G} {k : ℕ}
    (hg : Nat.Coprime 2 (orderOf g)) (hpow : g ^ 2 ^ k = 1) : g = 1 := by
  have h := orderOf_dvd_of_pow_eq_one hpow
  have h1 : orderOf g = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left k hg).symm h
  exact orderOf_eq_one_iff.mp h1

theorem eq_one_of_simple_fixed [Finite X] (hinj : Function.Injective ψ) (hR : ∀ x, ψ x ∈ R)
    (hS : ∀ s ∈ S, ∃ x ∈ GeneralizedFitting.subgroup X, ψ x = s) {t : X}
    (hsimple : IsSimpleGroup ↥(centralizer ({ψ t} : Set (Equiv.Perm (Fin 42))) ⊓ S))
    (heven : Even (Nat.card ↥(centralizer ({ψ t} : Set (Equiv.Perm (Fin 42))) ⊓ S)))
    (hidx : Nat.card ↥(centralizer ({ψ t} : Set (Equiv.Perm (Fin 42))) ⊓ R) =
      4 * Nat.card ↥(centralizer ({ψ t} : Set (Equiv.Perm (Fin 42))) ⊓ S))
    {d : X} (hd : d ∈ (pPrimeCore 2 (centralizer ({t} : Set X))).map
      (centralizer ({t} : Set X)).subtype) : d = 1 := by
  set C := centralizer ({t} : Set X)
  set O := (pPrimeCore 2 C).map C.subtype
  set H := centralizer ({ψ t} : Set (Equiv.Perm (Fin 42))) ⊓ S
  set K := centralizer ({ψ t} : Set (Equiv.Perm (Fin 42))) ⊓ R
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hHK : H ≤ K := inf_le_inf_left _ S_le_R
  have hHn : (H.subgroupOf K).Normal := by
    constructor
    intro h hh k
    rw [mem_subgroupOf] at hh ⊢
    obtain ⟨hh1, hh2⟩ := Subgroup.mem_inf.1 hh
    obtain ⟨hk1, hk2⟩ := Subgroup.mem_inf.1 k.2
    rw [coe_mul, coe_mul, coe_inv]
    exact Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hk1 hh1) (inv_mem hk1), conj_mem_S hk2 hh2⟩
  have hp : IsPGroup 2 (K ⧸ H.subgroupOf K) := by
    have hc : Nat.card (H.subgroupOf K) = Nat.card H :=
      Nat.card_congr (subgroupOfEquivOfLe hHK).toEquiv
    have hmul := Subgroup.card_mul_index (H.subgroupOf K)
    rw [hc, hidx] at hmul
    have hpos : 0 < Nat.card H := Nat.card_pos
    have h4 : (H.subgroupOf K).index = 4 :=
      Nat.eq_of_mul_eq_mul_left hpos (hmul.trans (mul_comm _ _))
    exact IsPGroup.of_card (n := 2) (by rw [← Subgroup.index_eq_card, h4]; norm_num)
  have hmemH : ∀ d ∈ O, ψ d ∈ H := by
    intro d hd
    have hdC : d ∈ C := by
      obtain ⟨d', -, rfl⟩ := hd
      exact d'.2
    have hdK : ψ d ∈ K := by
      refine Subgroup.mem_inf.2 ⟨mem_centralizer_singleton_iff.2 ?_, hR d⟩
      rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.1 hdC]
    have hodd : Nat.Coprime 2 (orderOf (⟨ψ d, hdK⟩ : K)) := by
      rw [Subgroup.orderOf_mk, orderOf_injective ψ hinj]
      exact coprime_orderOf_of_mem_oddCore hd
    have hmem := LocalAnalysis.ComponentInitial.mem_of_coprime_orderOf hp hodd
    rwa [mem_subgroupOf] at hmem
  set D := (O.map ψ).subgroupOf H
  have hDn : D.Normal := by
    constructor
    intro y hy h
    rw [mem_subgroupOf] at hy ⊢
    obtain ⟨d₀, hd₀, hy'⟩ := hy
    obtain ⟨n, -, hnC, hn⟩ := exists_preimage_of_mem_centralizer_S hinj hS h.2
    refine ⟨n * d₀ * n⁻¹, conj_mem_oddCore hnC hd₀, ?_⟩
    rw [map_mul, map_mul, map_inv, hn, hy', coe_mul, coe_mul, coe_inv]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal D with hD | hD
  · have hmem : (⟨ψ d, hmemH d hd⟩ : H) ∈ D := by
      rw [mem_subgroupOf]
      exact ⟨d, hd, rfl⟩
    rw [hD, mem_bot] at hmem
    apply hinj
    rw [map_one]
    exact congrArg Subtype.val hmem
  ·
    exfalso
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.1 heven)
    have hgD : g ∈ D := by
      rw [hD]
      exact mem_top g
    rw [mem_subgroupOf] at hgD
    obtain ⟨d₀, hd₀, hg'⟩ := hgD
    have hodd := coprime_orderOf_of_mem_oddCore hd₀
    rw [← orderOf_injective ψ hinj, hg', Subgroup.orderOf_coe, hg] at hodd
    exact absurd hodd (by norm_num)

theorem eq_one_of_isConj_r₁ [Finite X] (hinj : Function.Injective ψ) (hR : ∀ x, ψ x ∈ R)
    (hF : ∀ x : X, x ∈ GeneralizedFitting.subgroup X ↔ ψ x ∈ S)
    (hS : ∀ s ∈ S, ∃ x ∈ GeneralizedFitting.subgroup X, ψ x = s) {t : X}
    (h : IsConj (⟨ψ t, hR t⟩ : R) r₁R)
    {d : X} (hd : d ∈ (pPrimeCore 2 (centralizer ({t} : Set X))).map
      (centralizer ({t} : Set X)).subtype) : d = 1 := by
  set C := centralizer ({t} : Set X)
  have hFn : (GeneralizedFitting.subgroup X).Normal := GeneralizedFitting.normal X
  have h64 : Nat.card ↥(centralizer ({ψ t} : Set (Equiv.Perm (Fin 42))) ⊓ S) = 2 ^ 6 :=
    (card_centralizer_S_of_isConj h).trans card_C₁
  have hcomm : ∀ s ∈ centralizer ({ψ t} : Set (Equiv.Perm (Fin 42))) ⊓ S,
      ψ d * s = s * ψ d := by
    intro s hs
    obtain ⟨n, hnF, hnC, rfl⟩ := exists_preimage_of_mem_centralizer_S hinj hS hs
    have hkO : n * d * n⁻¹ * d⁻¹ ∈ (pPrimeCore 2 C).map C.subtype :=
      mul_mem (conj_mem_oddCore hnC hd) (inv_mem hd)
    have hkF : n * d * n⁻¹ * d⁻¹ ∈ GeneralizedFitting.subgroup X := by
      have h1 := hFn.conj_mem _ (inv_mem hnF) d
      rw [show n * d * n⁻¹ * d⁻¹ = n * (d * n⁻¹ * d⁻¹) by group]
      exact mul_mem hnF h1
    have hkC : n * d * n⁻¹ * d⁻¹ ∈ C := by
      obtain ⟨k, -, hk⟩ := hkO
      rw [← hk]
      exact k.2
    have hkH : ψ (n * d * n⁻¹ * d⁻¹) ∈
        centralizer ({ψ t} : Set (Equiv.Perm (Fin 42))) ⊓ S := by
      refine Subgroup.mem_inf.2 ⟨mem_centralizer_singleton_iff.2 ?_, (hF _).1 hkF⟩
      rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.1 hkC]
    have hpow : ψ (n * d * n⁻¹ * d⁻¹) ^ 2 ^ 6 = 1 := by
      have h1 := pow_card_eq_one' (G := ↥(centralizer ({ψ t} : Set (Equiv.Perm (Fin 42))) ⊓ S))
        (x := ⟨_, hkH⟩)
      rw [h64] at h1
      have h2 := congrArg Subtype.val h1
      rwa [coe_pow, coe_one] at h2
    have hk1 : n * d * n⁻¹ * d⁻¹ = 1 := by
      apply hinj
      rw [map_one]
      refine eq_one_of_coprime_of_pow ?_ hpow
      rw [orderOf_injective ψ hinj]
      exact coprime_orderOf_of_mem_oddCore hkO
    have hnd : n * d = d * n := by
      calc n * d = (n * d * n⁻¹ * d⁻¹) * (d * n) := by group
        _ = d * n := by rw [hk1, one_mul]
    rw [← map_mul, ← map_mul, hnd]
  obtain ⟨c, hc, hce⟩ := eq_conj_of_isConj h
  have hce' : ψ t = c * r₁ * c⁻¹ := hce
  have hg : c⁻¹ * ψ d * c ∈ R := R.mul_mem (R.mul_mem (R.inv_mem hc) (hR d)) hc
  have hgc : ∀ y ∈ C₁, c⁻¹ * ψ d * c * y = y * (c⁻¹ * ψ d * c) := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.1 hy
    have hyr := mem_centralizer_singleton_iff.1 hy1
    have hy' : c * y * c⁻¹ ∈ centralizer ({ψ t} : Set (Equiv.Perm (Fin 42))) ⊓ S := by
      refine Subgroup.mem_inf.2 ⟨mem_centralizer_singleton_iff.2 ?_, conj_mem_S hc hy2⟩
      rw [hce']
      calc c * y * c⁻¹ * (c * r₁ * c⁻¹) = c * (y * r₁) * c⁻¹ := by group
        _ = c * (r₁ * y) * c⁻¹ := by rw [hyr]
        _ = c * r₁ * c⁻¹ * (c * y * c⁻¹) := by group
    have h1 := hcomm _ hy'
    calc c⁻¹ * ψ d * c * y = c⁻¹ * (ψ d * (c * y * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * y * c⁻¹) * ψ d) * c := by rw [h1]
      _ = y * (c⁻¹ * ψ d * c) := by group
  have hpow := pow_eq_one_of_commute_C₁ hg hgc
  have hdpow : ψ d ^ 2 ^ 8 = 1 := by
    have h' : ψ d = c * (c⁻¹ * ψ d * c) * c⁻¹ := by group
    rw [h', conj_pow, hpow, mul_one, mul_inv_cancel]
  have hψodd : Nat.Coprime 2 (orderOf (ψ d)) := by
    rw [orderOf_injective ψ hinj]
    exact coprime_orderOf_of_mem_oddCore hd
  apply hinj
  rw [map_one]
  exact eq_one_of_coprime_of_pow hψodd hdpow

theorem pPrimeCore_eq_bot_of_not_unitary [Finite X] (hinj : Function.Injective ψ)
    (hR : ∀ x, ψ x ∈ R) (hF : ∀ x : X, x ∈ GeneralizedFitting.subgroup X ↔ ψ x ∈ S)
    (hS : ∀ s ∈ S, ∃ x ∈ GeneralizedFitting.subgroup X, ψ x = s) {t : X} (ht : orderOf t = 2)
    (hu : ¬ IsConj (⟨ψ t, hR t⟩ : R) r₄R) :
    pPrimeCore 2 (centralizer ({t} : Set X)) = ⊥ := by
  suffices h : ∀ d ∈ (pPrimeCore 2 (centralizer ({t} : Set X))).map
      (centralizer ({t} : Set X)).subtype, d = 1 by
    rw [eq_bot_iff]
    intro d hd
    rw [mem_bot]
    exact Subtype.ext (h d ⟨d, hd, rfl⟩)
  intro d hd
  have hT2 : orderOf (⟨ψ t, hR t⟩ : R) = 2 := by
    rw [Subgroup.orderOf_mk, orderOf_injective ψ hinj, ht]
  rcases (orderOf_eq_two_iff _).1 hT2 with h | h | h | h
  · exact eq_one_of_isConj_r₁ hinj hR hF hS h hd
  · obtain ⟨e⟩ := fixed_of_isConj h
    have e' : ↥(centralizer ({ψ t} : Set (Equiv.Perm (Fin 42))) ⊓ S) ≃* C₂ := e
    have : IsSimpleGroup C₂ := isSimpleGroup_C₂
    have hH : Nat.card ↥(centralizer ({ψ t} : Set (Equiv.Perm (Fin 42))) ⊓ S) = 168 :=
      (card_centralizer_S_of_isConj h).trans card_C₂
    have hK : Nat.card ↥(centralizer ({ψ t} : Set (Equiv.Perm (Fin 42))) ⊓ R) * 360 = 241920 :=
      card_centralizer_mul_of_isConj h conjClass₂.2
    refine eq_one_of_simple_fixed hinj hR hS e'.isSimpleGroup ?_ ?_ hd
    · rw [hH]
      decide
    · rw [hH]
      omega
  · obtain ⟨e⟩ := fixed_of_isConj h
    have e' : ↥(centralizer ({ψ t} : Set (Equiv.Perm (Fin 42))) ⊓ S) ≃* C₃ := e
    have : IsSimpleGroup C₃ := isSimpleGroup_C₃
    have hH : Nat.card ↥(centralizer ({ψ t} : Set (Equiv.Perm (Fin 42))) ⊓ S) = 60 :=
      (card_centralizer_S_of_isConj h).trans card_C₃
    have hK : Nat.card ↥(centralizer ({ψ t} : Set (Equiv.Perm (Fin 42))) ⊓ R) * 1008 =
        241920 :=
      card_centralizer_mul_of_isConj h conjClass₃.2
    refine eq_one_of_simple_fixed hinj hR hS e'.isSimpleGroup ?_ ?_ hd
    · rw [hH]
      decide
    · rw [hH]
      omega
  · exact absurd h hu

end Core

theorem centralizer_r₄R_sup : centralizer ({r₄R} : Set R) ⊔ S.subgroupOf R = ⊤ := by
  have : (S.subgroupOf R).Normal := S_normal
  have h864 : Nat.card (centralizer ({r₄R} : Set R)) = 864 := by
    have h := card_centralizer_mul_of_isConj (IsConj.refl r₄R) conjClass₄.2
    rw [← card_centralizer_R] at h
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 280) (h.trans (by norm_num))
  have hmap : (S.subgroupOf R ⊓ centralizer ({r₄R} : Set R)).map R.subtype = C₄ := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨hz1, hz2⟩ := Subgroup.mem_inf.1 hz
      refine Subgroup.mem_inf.2 ⟨mem_centralizer_singleton_iff.2 ?_, mem_subgroupOf.1 hz1⟩
      exact congrArg Subtype.val (mem_centralizer_singleton_iff.1 hz2)
    · intro hy
      obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.1 hy
      refine ⟨⟨y, S_le_R hy2⟩, Subgroup.mem_inf.2 ⟨mem_subgroupOf.2 hy2,
        mem_centralizer_singleton_iff.2 (Subtype.ext ?_)⟩, rfl⟩
      exact mem_centralizer_singleton_iff.1 hy1
  have h72 : Nat.card ↥(S.subgroupOf R ⊓ centralizer ({r₄R} : Set R)) = 72 := by
    rw [← card_C₄, ← hmap]
    exact Nat.card_congr ((S.subgroupOf R ⊓ centralizer ({r₄R} : Set R)).equivMapOfInjective
      R.subtype (Subgroup.subtype_injective R)).toEquiv
  have hrel : (S.subgroupOf R).relIndex (centralizer ({r₄R} : Set R)) = 12 := by
    have h := Subgroup.relIndex_mul_card (H := S.subgroupOf R) (K := centralizer ({r₄R} : Set R))
    rw [h864, h72] at h
    omega
  have hcardS : Nat.card (S.subgroupOf R) = 20160 := by
    rw [← card_S]
    exact Nat.card_congr (subgroupOfEquivOfLe S_le_R).toEquiv
  have hidx : (S.subgroupOf R).index = 12 := by
    have h := Subgroup.card_mul_index (S.subgroupOf R)
    rw [hcardS, card_R] at h
    omega
  have h1 := Subgroup.relIndex_mul_index (H := S.subgroupOf R)
    (K := centralizer ({r₄R} : Set R) ⊔ S.subgroupOf R) le_sup_right
  rw [Subgroup.relIndex_sup_right, hrel, hidx] at h1
  exact Subgroup.index_eq_one.1 (by omega)

theorem mul_inv_mem_S_of_isConj₄ {x : R} (h : IsConj x r₄R) :
    (x : Equiv.Perm (Fin 42)) * r₄⁻¹ ∈ S := by
  rw [isConj_comm, isConj_iff] at h
  obtain ⟨c, rfl⟩ := h
  have : (S.subgroupOf R).Normal := S_normal
  have hc : c ∈ centralizer ({r₄R} : Set R) ⊔ S.subgroupOf R := by
    rw [centralizer_r₄R_sup]
    exact mem_top c
  obtain ⟨k, hk, s, hs, rfl⟩ := mem_sup_of_normal_right.1 hc
  have hk' : (k : Equiv.Perm (Fin 42)) * r₄ = r₄ * k :=
    congrArg Subtype.val (mem_centralizer_singleton_iff.1 hk)
  have hsS : (s : Equiv.Perm (Fin 42)) ∈ S := mem_subgroupOf.1 hs
  have hmem : (s : Equiv.Perm (Fin 42)) * (r₄ * (s : Equiv.Perm (Fin 42))⁻¹ * r₄⁻¹) ∈ S :=
    mul_mem hsS (conj_mem_S r₄_mem_R (inv_mem hsS))
  have hconj := conj_mem_S k.2 hmem
  have heq : ((k * s * r₄R * (k * s)⁻¹ : R) : Equiv.Perm (Fin 42)) * r₄⁻¹ =
      (k : Equiv.Perm (Fin 42)) *
        ((s : Equiv.Perm (Fin 42)) * (r₄ * (s : Equiv.Perm (Fin 42))⁻¹ * r₄⁻¹)) *
          (k : Equiv.Perm (Fin 42))⁻¹ := by
    rw [coe_mul, coe_mul, coe_inv, coe_mul, show ((r₄R : R) : Equiv.Perm (Fin 42)) = r₄ from rfl]
    calc (k : Equiv.Perm (Fin 42)) * s * r₄ * ((k : Equiv.Perm (Fin 42)) * s)⁻¹ * r₄⁻¹ =
        k * s * r₄ * (s : Equiv.Perm (Fin 42))⁻¹ * (r₄ * k)⁻¹ := by group
      _ = k * s * r₄ * (s : Equiv.Perm (Fin 42))⁻¹ * ((k : Equiv.Perm (Fin 42)) * r₄)⁻¹ := by
        rw [hk']
      _ = (k : Equiv.Perm (Fin 42)) *
          ((s : Equiv.Perm (Fin 42)) * (r₄ * (s : Equiv.Perm (Fin 42))⁻¹ * r₄⁻¹)) *
            (k : Equiv.Perm (Fin 42))⁻¹ := by group
  rw [heq]
  exact hconj

theorem orderOf_eq_two_of_four {X : Type*} [Group X] {A : Subgroup X}
    (e : A ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) {a : X} (ha : a ∈ A)
    (ha1 : a ≠ 1) : orderOf a = 2 := by
  have hm : ∀ y : Multiplicative (ZMod 2), y * y = 1 := by decide
  have hsq : (⟨a, ha⟩ : A) * ⟨a, ha⟩ = 1 := by
    apply e.injective
    rw [map_mul, map_one]
    exact Prod.ext (hm (e _).1) (hm (e _).2)
  exact orderOf_eq_prime (by rw [pow_two]; exact congrArg Subtype.val hsq) ha1

theorem deltaCore_eq_bot_of_psl34 {X : Type} [Group X] [Finite X]
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a)
    (hmodel : Blueprint.LieModel (GeneralizedFitting.subgroup X) .PSL 3 2 2)
    {A : Subgroup X} (hA : Nonempty (A ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) :
    (⨅ (a : X) (_ : a ∈ A) (_ : a ≠ 1),
      (pPrimeCore 2 (centralizer ({a} : Set X))).map (centralizer ({a} : Set X)).subtype) = ⊥ := by
  obtain ⟨ψ, hinj, hR, hF, hS⟩ := exists_psl34Embedding hsimple hnab hmodel
  obtain ⟨e⟩ := hA
  by_contra hne
  have hu : ∀ a ∈ A, a ≠ 1 → IsConj (⟨ψ a, hR a⟩ : R) r₄R := by
    intro a ha ha1
    by_contra hc
    apply hne
    rw [eq_bot_iff]
    intro g hg
    have hg' := mem_iInf.mp (mem_iInf.mp (mem_iInf.mp hg a) ha) ha1
    rw [pPrimeCore_eq_bot_of_not_unitary hinj hR hF hS (orderOf_eq_two_of_four e ha ha1) hc,
      Subgroup.map_bot] at hg'
    exact hg'
  set u : Multiplicative (ZMod 2) × Multiplicative (ZMod 2) := (Multiplicative.ofAdd 1, 1)
  set v : Multiplicative (ZMod 2) × Multiplicative (ZMod 2) := (1, Multiplicative.ofAdd 1)
  have hu1 : u ≠ 1 := by decide
  have hv1 : v ≠ 1 := by decide
  have huv : u * v ≠ 1 := by decide
  have hne1 : ∀ w, w ≠ 1 → ((e.symm w : A) : X) ≠ 1 := by
    intro w hw h1
    apply hw
    have h2 : e.symm w = 1 := Subtype.ext h1
    rw [← e.apply_symm_apply w, h2, map_one]
  have ha := hu _ (e.symm u).2 (hne1 u hu1)
  have hb := hu _ (e.symm v).2 (hne1 v hv1)
  have hab := hu _ (e.symm (u * v)).2 (hne1 _ huv)
  have hmem : ψ ((e.symm (u * v) : A) : X) ∈ S := by
    rw [map_mul, coe_mul, map_mul]
    have h1 := mul_inv_mem_S_of_isConj₄ ha
    have h2 := mul_inv_mem_S_of_isConj₄ hb
    have h3 := conj_mem_S r₄_mem_R h2
    have hr : r₄ * r₄ = 1 := by
      have h := pow_orderOf_eq_one r₄R
      rw [orderOf_r₄R, pow_two] at h
      exact congrArg Subtype.val h
    have heq : ψ ((e.symm u : A) : X) * ψ ((e.symm v : A) : X) =
        (ψ ((e.symm u : A) : X) * r₄⁻¹) * (r₄ * (ψ ((e.symm v : A) : X) * r₄⁻¹) * r₄⁻¹) *
          (r₄ * r₄) := by group
    rw [heq, hr, mul_one]
    exact mul_mem h1 h3
  exact not_mem_S_of_isConj hab not_mem_S_r₄ hmem

end CFSG.ComponentClassification.GrSLit
