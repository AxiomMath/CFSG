module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P85eBar
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P85eCfgMap
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P85eAltCon
public import CFSG.GH74.GLS.Stage2.Final.M12Odd

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87.P85

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

section Conj

theorem U34Cfg.conj {A : Type} [Group A] [Finite A] {P : Subgroup A} {w : A} (h : U34Cfg P w) (g : A) :
    U34Cfg (P.map (MulAut.conj g).toMonoidHom) (g * w * g⁻¹) :=
  h.map_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective

theorem exists_conj_le_sylow {G : Type} [Group G] [Finite G] {S P : Subgroup G}
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤) (hP : IsPGroup 2 P) :
    ∃ g : G, P.map (MulAut.conj g).toMonoidHom ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
  have hQ : CFSG.ABGLocalTools.IsSylowOf 2 (Q : Subgroup G) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_top, Q.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact Q.not_dvd_index
  obtain ⟨k, -, hk⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj hS hQ
  refine ⟨k⁻¹, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have := (hk x).mp (hPQ hx)
  simpa using this

theorem cfg_w_mem_cen {G : Type} [Group G] {z : G} {P : Subgroup G} {w : G} (h : U34Cfg P w)
    (hzP : z ∈ P) (hPC : P ≤ Cen z) : w ∈ Cen z := by
  have h1 := h.cen z hzP (fun y hy => by
    have := Subgroup.mem_centralizer_singleton_iff.mp (hPC hy)
    exact this.symm)
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h2 : w * z * w⁻¹ * w = z * w := by rw [h1]
  simpa [mul_assoc] using h2.symm.symm

theorem no_u34cfg_pair {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}
    (hz2 : orderOf z = 2) (hS : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤) (hSC : S ≤ Cen z)
    (hLP : LPairCtx G z S) {P : Subgroup G} {w : G} (h : U34Cfg P w) : False := by
  obtain ⟨g, hg⟩ := exists_conj_le_sylow hS h.two
  have h' := h.conj g
  have hz : z ∈ P.map (MulAut.conj g).toMonoidHom := lpair_z_mem hz2 hLP hSC hg h'.two h'.order
  have hPC : P.map (MulAut.conj g).toMonoidHom ≤ Cen z := hg.trans hSC
  have hwC : g * w * g⁻¹ ∈ Cen z := cfg_w_mem_cen h' hz hPC
  obtain ⟨a, ha⟩ := h'.five
  have h0 := lpair_comm_trivial hLP hSC hg h'.two hwC h'.norm ha
  have h64 := h'.comm_ge
  rw [h0, Subgroup.card_bot] at h64
  omega

end Conj

section M12

theorem card_le_sixtyfour_of_m12 {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}
    (hM : Stage1M12 G z S) (hSC : S ≤ Cen z) (hS2 : IsPGroup 2 S) : Nat.card S ≤ 64 := by
  obtain ⟨-, -, hC192, -⟩ := CFSG.GH74.GLS.Stage2.Final.m12_barFacts hM
  obtain ⟨ψ, hinj, -, hrange⟩ := exists_psi hS2 hSC
  have hcard : Nat.card S = Nat.card (barOf z S) := by
    rw [← hrange]
    exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  have hdvd : Nat.card (barOf z S) ∣ 192 := by
    have := Subgroup.card_subgroup_dvd_card (barOf z S)
    rwa [hC192] at this
  obtain ⟨k, hk⟩ := hS2.exists_card_eq
  rw [hcard] at hk
  by_contra hbig
  push Not at hbig
  rw [hcard] at hbig
  have h7 : 7 ≤ k := by
    by_contra hk7
    push Not at hk7
    have : 2 ^ k ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h128 : 2 ^ 7 ∣ Nat.card (barOf z S) := by
    rw [hk]
    exact pow_dvd_pow 2 h7
  have := h128.trans hdvd
  norm_num at this

theorem no_u34cfg_m12 {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}
    (hz : z ∈ S) (hS : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤) (hSC : S ≤ Cen z)
    (hM : Stage1M12 G z S) {P : Subgroup G} {w : G} (h : U34Cfg P w) : False := by
  obtain ⟨g, hg⟩ := exists_conj_le_sylow hS h.two
  have h' := h.conj g
  set P' := P.map (MulAut.conj g).toMonoidHom with hP'
  have hS64 := card_le_sixtyfour_of_m12 hM hSC hS.isPGroup
  have hPS : Nat.card P' ≤ Nat.card S := Subgroup.card_le_of_le hg
  have hbig := h'.big
  have hP64 : Nat.card P' = 64 := by omega
  have hPeq : P' = S := Subgroup.eq_of_le_of_card_ge hg (by omega)
  rcases h'.center_or with h1 | ⟨-, hZ4, hsq⟩
  · omega
  · have hsub : ((center ↥P' : Subgroup ↥P') : Set ↥P') ⊆ {1, ⟨z, hPeq ▸ hz⟩} := by
      intro x hx
      have hxc : ∀ y ∈ P', (x : G) * y = y * (x : G) := by
        intro y hy
        have := Subgroup.mem_center_iff.mp hx ⟨y, hy⟩
        exact congrArg Subtype.val this.symm
      have hx1 : (x : G) * x = 1 := hsq x x.2 hxc
      by_cases hx0 : (x : G) = 1
      · left
        exact Subtype.ext hx0
      · right
        have hord : orderOf (x : G) = 2 := by
          apply orderOf_eq_prime
          · rw [sq]; exact hx1
          · exact hx0
        have := hM.base.zcen (x : G) (hPeq ▸ x.2) (fun s hs => (hxc s (hPeq ▸ hs)).symm) hord
        exact Subtype.ext this
    have hle : Nat.card ↥(center ↥P') ≤ 2 := by
      have h2 : Set.ncard ((center ↥P' : Subgroup ↥P') : Set ↥P') ≤ Set.ncard ({1, ⟨z, hPeq ▸ hz⟩} : Set ↥P') :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
      have h3 : Set.ncard ({1, ⟨z, hPeq ▸ hz⟩} : Set ↥P') ≤ 2 := by
        refine (Set.ncard_insert_le _ _).trans ?_
        rw [Set.ncard_singleton]
      rw [← Nat.card_coe_set_eq] at h2
      exact h2.trans h3
    omega

end M12

section Sporadic

variable {G : Type} [Group G] [Finite G] {z : G}

theorem toBar_inj_on_pgroup {Q : Subgroup ↥(Cen z)} (hQ : IsPGroup 2 Q) {x y : ↥(Cen z)} (hx : x ∈ Q)
    (hy : y ∈ Q) (h : toBar z x = toBar z y) : x = y := by
  have hker : x⁻¹ * y ∈ (toBar z).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  have := eq_one_of_pgroup_of_odd hQ (odd_card_ker_toBar z) (Q.mul_mem (Q.inv_mem hx) hy) hker
  rwa [inv_mul_eq_one] at this

omit [Finite G] in
theorem exists_pi_alt {n : ℕ} (hcov : IsDoubleCoverOfAlt (CentralizerBar z) n) :
    ∃ π : ↥(Cen z) →* Equiv.Perm (Fin n), ∀ x, π x = 1 ↔ toBar z x ∈ center (CentralizerBar z) := by
  obtain ⟨-, -, ⟨e⟩⟩ := hcov
  refine ⟨(alternatingGroup (Fin n)).subtype.comp
    (e.toMonoidHom.comp ((QuotientGroup.mk' (center (CentralizerBar z))).comp (toBar z))), fun x => ?_⟩
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
    QuotientGroup.mk'_apply]
  rw [← Subgroup.coe_one (alternatingGroup (Fin n)), Subtype.coe_inj, ← e.map_one, e.injective.eq_iff,
    QuotientGroup.eq_one_iff]

theorem ker_card_le {n : ℕ} (hcov : IsDoubleCoverOfAlt (CentralizerBar z) n)
    {π : ↥(Cen z) →* Equiv.Perm (Fin n)}
    (hπ : ∀ x, π x = 1 ↔ toBar z x ∈ center (CentralizerBar z)) {Q : Subgroup ↥(Cen z)}
    (hQ : IsPGroup 2 Q) : Nat.card ↥(Q ⊓ π.ker) ≤ 2 := by
  have hc2 := hcov.2.1
  let f : ↥(Q ⊓ π.ker) → ↥(center (CentralizerBar z)) := fun x =>
    ⟨toBar z (x : ↥(Cen z)), (hπ x).mp x.2.2⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : toBar z (x : ↥(Cen z)) = toBar z (y : ↥(Cen z)) := congrArg Subtype.val hxy
    exact Subtype.ext (toBar_inj_on_pgroup hQ x.2.1 y.2.1 h1)
  have := Nat.card_le_card_of_injective f hf
  rwa [hc2] at this

theorem sporadic_core {n : ℕ} (hn : n ≤ 11) (hcov : IsDoubleCoverOfAlt (CentralizerBar z) n)
    {P : Subgroup G} {w : G} (hPC : P ≤ Cen z) (hwC : w ∈ Cen z) (h : U34Cfg P w) : False := by
  classical
  obtain ⟨π, hπ⟩ := exists_pi_alt hcov
  set Pc : Subgroup ↥(Cen z) := P.subgroupOf (Cen z) with hPc
  set wc : ↥(Cen z) := ⟨w, hwC⟩ with hwc
  have hPc2 : IsPGroup 2 Pc := h.two.comap_subtype
  obtain ⟨a, ha⟩ := h.five
  have hwc5 : wc ^ (5 ^ a) = 1 := Subtype.ext (by simpa [hwc] using ha)
  have hwcP : wc ∈ normalizer (Pc : Set ↥(Cen z)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have := Subgroup.mem_normalizer_iff.mp h.norm (x : G)
    simpa [hPc, Subgroup.mem_subgroupOf, hwc] using this
  set W : Subgroup ↥(Cen z) := zpowers wc with hW
  have hW5 : IsPGroup 5 ↥W := by
    intro g
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
    refine ⟨a, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hwc5, one_zpow]
  have hP5 : ¬ 5 ∣ Nat.card Pc := by
    obtain ⟨m, hm⟩ := hPc2.exists_card_eq
    rw [hm]
    intro hd
    have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) hd
    omega
  have hWP : W ≤ normalizer (Pc : Set ↥(Cen z)) := by
    rw [hW, Subgroup.zpowers_le]; exact hwcP
  set Q : Subgroup ↥(Cen z) := ⁅Pc, W⁆ with hQ
  have hidem : ⁅Q, W⁆ = Q :=
    CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 5 (by norm_num) W Pc hW5 hP5 hWP
  have hQle : Q ≤ Pc := by
    rw [hQ]
    refine Subgroup.commutator_le.mpr (fun x hx k hk => ?_)
    have h1 : k * x⁻¹ * k⁻¹ ∈ Pc := (Subgroup.mem_normalizer_iff.mp (hWP hk) x⁻¹).mp (Pc.inv_mem hx)
    rw [commutatorElement_def]
    have : x * k * x⁻¹ * k⁻¹ = x * (k * x⁻¹ * k⁻¹) := by group
    rw [this]
    exact Pc.mul_mem hx h1
  have hQ2 : IsPGroup 2 ↥Q := hPc2.to_le hQle
  have hwQ : wc ∈ normalizer (Q : Set ↥(Cen z)) :=
    Subgroup.normalizer_commutator_ge_right Pc W (Subgroup.mem_zpowers wc)
  have hmap : Q.map (Cen z).subtype = ⁅P, zpowers w⁆ := by
    rw [hQ, Subgroup.map_commutator, hPc, hW, Subgroup.map_subgroupOf_eq_of_le hPC,
      MonoidHom.map_zpowers]
    rfl
  have hcard : Nat.card Q = Nat.card ↥⁅P, zpowers w⁆ := by
    rw [← hmap]
    exact (Subgroup.card_map_of_injective (Cen z).subtype_injective).symm
  have h64 := h.comm_ge
  have := alt_contra hn π (fun Q' hQ' => ker_card_le hcov hπ hQ') hQ2 hwc5 hwQ hidem
  omega

theorem no_u34cfg_sporadic {n : ℕ} (hn : n ≤ 11) (hz2 : orderOf z = 2)
    (hcov : IsDoubleCoverOfAlt (CentralizerBar z) n)
    (hone : ∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v) {P : Subgroup G} {w : G}
    (h : U34Cfg P w) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt : Nontrivial ↥P := by
    have := h.big
    exact Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hZnt : Nontrivial ↥(center ↥P) := h.two.center_nontrivial
  have hZ2 : IsPGroup 2 ↥(center ↥P) := h.two.to_subgroup (center ↥P)
  have hdvd : 2 ∣ Nat.card ↥(center ↥P) := by
    obtain ⟨m, hm⟩ := hZ2.exists_card_eq
    have h1 : 1 < Nat.card ↥(center ↥P) := Finite.one_lt_card
    rw [hm] at h1 ⊢
    have : m ≠ 0 := by
      rintro rfl
      simp at h1
    exact dvd_pow_self 2 this
  obtain ⟨e, he⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have heP : ((e : ↥P) : G) ∈ P := (e : ↥P).2
  have he2 : orderOf ((e : ↥P) : G) = 2 := by
    rw [Subgroup.orderOf_coe (e : ↥P), Subgroup.orderOf_coe e]
    exact he
  have hec : ∀ y ∈ P, ((e : ↥P) : G) * y = y * ((e : ↥P) : G) := by
    intro y hy
    have := Subgroup.mem_center_iff.mp e.2 ⟨y, hy⟩
    exact congrArg Subtype.val this.symm
  obtain ⟨c, hc⟩ := isConj_iff.mp (hone _ z he2 hz2)
  have h' := h.conj c
  have hz : z ∈ P.map (MulAut.conj c).toMonoidHom :=
    ⟨_, heP, by simpa [MulAut.conj_apply] using hc⟩
  have hPC : P.map (MulAut.conj c).toMonoidHom ≤ Cen z := by
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← hc]
    have := hec y hy
    simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
    calc c * y * c⁻¹ * (c * (e : G) * c⁻¹) = c * (y * (e : G)) * c⁻¹ := by group
      _ = c * ((e : G) * y) * c⁻¹ := by rw [this]
      _ = c * (e : G) * c⁻¹ * (c * y * c⁻¹) := by group
  have hwC : c * w * c⁻¹ ∈ Cen z := cfg_w_mem_cen h' hz hPC
  exact sporadic_core hn hcov hPC hwC h'

end Sporadic

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87.P85

