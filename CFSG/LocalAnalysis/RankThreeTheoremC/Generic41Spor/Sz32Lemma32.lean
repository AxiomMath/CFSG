module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32SharedProp31
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32SharedLemma33
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupSz32
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.SecondPointSz32
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Lemmas
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericCaseSetup
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.PSU3.Aut

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3K0 x_mem_u3K0_gen
  fus_mem_zpowers_of_isCyclic_of_pow_prime u3_isSimple_quot)
open CFSG.LocalAnalysis.RankThreeTheoremC (u3main_center_bot odd_card_pPrimeCoreIn_of_not_le)

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}

private theorem sz32_l32_comm_ker {C' Q : Type} [Group C'] [Group Q] [Finite Q]
    (hSig : CFSG.LocalAnalysis.RankThreeTheoremC.SignalizerTwoGroupKFact)
    (hQ : IsSz32Type 5 Q) (hQs : IsSimpleGroup Q)
    (hZ : Subgroup.center Q = ⊥) (ρ : C' →* MulAut Q) {E F : Subgroup C'}
    (hE : IsElemAbelian 5 E) (hEcard : Nat.card E = 5 ^ 3)
    (hkcard : Nat.card (ρ.comp E.subtype).ker = 5) (hF2 : IsPGroup 2 F)
    (hEF : ∀ e ∈ E, ∀ f ∈ F, e * f * e⁻¹ ∈ F) :
    ∀ e ∈ E, ∀ f ∈ F, ρ (e * f * e⁻¹ * f⁻¹) = 1 := by
  haveI : Finite (MulAut Q) :=
    Finite.of_injective (fun f : MulAut Q => (f : Q → Q)) DFunLike.coe_injective
  let c : Q →* MulAut Q := MulAut.conj
  have hcinj : Function.Injective c := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have hkc : k ∈ Subgroup.center Q := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h1 := congrArg (fun φ : MulAut Q => φ y) hk
      simp only [c, MulAut.conj_apply, MulAut.one_apply] at h1
      calc y * k = (k * y * k⁻¹) * k := by rw [h1]
        _ = k * y := by group
    rw [hZ, Subgroup.mem_bot] at hkc
    exact hkc
  let Kin : Subgroup (MulAut Q) := c.range
  have hKinN : Kin.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := hn
    refine ⟨g k, ?_⟩
    ext y
    simp [c, MulAut.conj_apply]
  have hKinC : Subgroup.centralizer (Kin : Set (MulAut Q)) = ⊥ := by
    rw [eq_bot_iff]
    intro φ hφ
    rw [Subgroup.mem_centralizer_iff] at hφ
    rw [Subgroup.mem_bot]
    ext k
    have hcen : (φ k)⁻¹ * k ∈ Subgroup.center Q := by
      rw [Subgroup.mem_center_iff]
      intro z
      obtain ⟨y, rfl⟩ := φ.surjective z
      have h1 := congrArg (fun ψ : MulAut Q => ψ y) (hφ (MulAut.conj k) ⟨k, rfl⟩)
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv] at h1
      calc φ y * ((φ k)⁻¹ * k) = (φ k)⁻¹ * ((φ k * φ y * (φ k)⁻¹) * k) := by group
        _ = (φ k)⁻¹ * ((k * φ y * k⁻¹) * k) := by rw [← h1]
        _ = (φ k)⁻¹ * k * φ y := by group
    rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at hcen
    simpa using hcen
  let eK : Q ≃* Kin := MonoidHom.ofInjective hcinj
  haveI hKs : IsSimpleGroup Kin := eK.symm.isSimpleGroup
  have hQnonab : ∃ a b : Q, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    obtain ⟨l, hl⟩ := exists_ne (1 : Q)
    have : l ∈ Subgroup.center Q := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact hcon g l
    rw [hZ, Subgroup.mem_bot] at this
    exact hl this
  have hKnonab : ∃ a b : Kin, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hQnonab
    exact ⟨eK a, eK b, fun h => hab (eK.injective (by rw [map_mul, map_mul]; exact h))⟩
  obtain ⟨hv, ⟨eQ⟩⟩ := hQ.2
  have hKcat : IsCatalogGroup Kin :=
    ⟨TauCeti.CFSGIndex.lie ⟨.suzuki 2, hv⟩, ⟨eK.symm.trans eQ⟩⟩
  have hKiso : IsoLie ↥Kin (.suzuki 2) := ⟨hv, ⟨eK.symm.trans eQ⟩⟩
  let B : Subgroup (MulAut Q) := E.map ρ
  have hBel : IsElemAbelian 5 B := hE.map ρ
  have hBcard : Nat.card B = 5 ^ 2 := by
    show Nat.card (E.map ρ) = 5 ^ 2
    have h := Subgroup.card_ker_mul_card_range (ρ.comp E.subtype)
    rw [hkcard, MonoidHom.range_comp, Subgroup.range_subtype, hEcard] at h
    omega
  have hBZ : B ⊓ Subgroup.centralizer (Kin : Set (MulAut Q)) = ⊥ := by
    rw [hKinC]
    exact inf_bot_eq _
  let Fb : Subgroup (MulAut Q) := F.map ρ
  have hFbp : IsPGroup 2 Fb := hF2.map ρ
  have hBnorm : B ≤ Subgroup.normalizer (Fb : Set (MulAut Q)) := by
    rintro _ ⟨e, he, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact ⟨e * f * e⁻¹, hEF e he f hf, by simp [map_mul]⟩
    · rintro ⟨f, hf, hfeq⟩
      refine ⟨e⁻¹ * f * e, ?_, ?_⟩
      · have := hEF e⁻¹ (E.inv_mem he) f hf
        simpa using this
      · rw [map_mul, map_mul, map_inv, hfeq]
        group
  have hKey := hSig (MulAut Q) Kin hKinN hKs hKnonab hKcat 5 (by norm_num) (by norm_num) B hBel
    hBcard hBZ (Or.inr (Or.inr ⟨rfl, hKiso⟩)) Fb hFbp hBnorm
  intro e he f hf
  have h1 := hKey (Subgroup.commutator_mem_commutator (Subgroup.mem_map_of_mem ρ he)
    (Subgroup.mem_map_of_mem ρ hf))
  rw [hKinC, Subgroup.mem_bot, commutatorElement_def] at h1
  simpa [map_mul, map_inv] using h1

private theorem sz32_l32_zpow_mod5 {X : Type*} [Group X] {w : X} (hw : w ^ 5 = 1) {n : ℤ}
    (hn : n % 5 = 1) : w ^ n = w := by
  obtain ⟨q, rfl⟩ : ∃ q : ℤ, n = 5 * q + 1 := ⟨n / 5, by omega⟩
  have h5 : w ^ (5 : ℤ) = 1 := by exact_mod_cast hw
  rw [zpow_add, zpow_mul, h5, one_zpow, one_mul, zpow_one]

private theorem sz32_l32_comm_conj5 {X : Type*} [Group X] {g w : X} (hw : w ^ 5 = 1) {n : ℤ}
    (hn : n % 5 = 1) (h : g * w * g⁻¹ = w ^ n) : g * w = w * g := by
  have h1 : g * w * g⁻¹ = w := h.trans (sz32_l32_zpow_mod5 hw hn)
  rw [mul_inv_eq_iff_eq_mul] at h1
  exact h1

private theorem sz32_l32_plane {X : Type} [Group X] [Finite X] {Q : Subgroup X} {a c y x : X}
    (h : Sz32QPres Q a c y x) :
    ∃ A : Subgroup X, IsElemAbelian 5 A ∧ Nat.card A = 5 ^ 2 ∧ A ≤ Q ∧
      ∀ s ∈ Q, ∀ t ∈ A, s * t = t * s := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have ha25 : a ^ 25 = 1 := by rw [← h.ord_a]; exact pow_orderOf_eq_one a
  have he5 : (a ^ 5) ^ 5 = 1 := by rw [← pow_mul]; exact ha25
  have he1 : a ^ 5 ≠ 1 := by
    intro h1
    have := orderOf_dvd_of_pow_eq_one h1
    rw [h.ord_a] at this
    omega
  have hx5 : x ^ 5 = 1 := by rw [← h.x_ord]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    intro h1
    have := h.x_ord
    rw [h1, orderOf_one] at this
    omega
  have hac : Commute a c := h.ac
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h.x_mem
  have hcx : Commute c x := by rw [← hk]; exact (Commute.refl c).zpow_right k
  have hax : Commute a x := by rw [← hk]; exact hac.zpow_right k
  have hex : Commute (a ^ 5) x := hax.pow_left 5
  have hxe : x ∉ Subgroup.zpowers (a ^ 5) := by
    intro hx
    have h1 : x ∈ Subgroup.zpowers a :=
      Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers a) 5) hx
    have h2 : x ∈ Subgroup.zpowers a ⊓ Subgroup.zpowers c := ⟨h1, h.x_mem⟩
    rw [h.inf, Subgroup.mem_bot] at h2
    exact hx1 h2
  have hcomm : ∀ u ∈ Subgroup.zpowers (a ^ 5), ∀ v ∈ Subgroup.zpowers x, u * v = v * u := by
    intro u hu v hv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact ((hex.zpow_zpow i j)).eq
  have hel : IsElemAbelian 5 (Subgroup.zpowers (a ^ 5) ⊔ Subgroup.zpowers x) := by
    refine CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting 5
      (CFSG.Open.isElemAbelian_zpowers he5) (CFSG.Open.isElemAbelian_zpowers hx5) ?_
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (hcomm u hu v hv).symm
  refine ⟨Subgroup.zpowers (a ^ 5) ⊔ Subgroup.zpowers x, hel, ?_, ?_, ?_⟩
  · rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers (by norm_num) _ hx5 hxe
      (fun e he => (hcomm e he x (Subgroup.mem_zpowers x))), Nat.card_zpowers,
      orderOf_eq_prime he5 he1]
    norm_num
  · exact sup_le (Subgroup.zpowers_le.mpr (Q.pow_mem h.a_mem 5))
      (Subgroup.zpowers_le.mpr (Subgroup.zpowers_le.mpr h.c_mem h.x_mem))
  · have key : ∀ g : X, (a ^ 5) * g = g * (a ^ 5) → x * g = g * x →
        g ∈ Subgroup.centralizer ((Subgroup.zpowers (a ^ 5) ⊔ Subgroup.zpowers x : Subgroup X) : Set X) := by
      intro g heg hxg
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      have : Subgroup.zpowers (a ^ 5) ⊔ Subgroup.zpowers x ≤ Subgroup.centralizer ({g} : Set X) :=
        sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr heg))
          (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hxg))
      exact Subgroup.mem_centralizer_singleton_iff.mp (this ht)
    have hQle : Q ≤ Subgroup.centralizer
        ((Subgroup.zpowers (a ^ 5) ⊔ Subgroup.zpowers x : Subgroup X) : Set X) := by
      rw [h.gen]
      refine sup_le (sup_le ?_ ?_) ?_
      · rw [Subgroup.zpowers_le]
        exact key a (Commute.refl a |>.pow_left 5).eq hax.symm.eq
      · rw [Subgroup.zpowers_le]
        exact key c ((hac.pow_left 5).eq) hcx.symm.eq
      · rw [Subgroup.zpowers_le]
        obtain ⟨n, hn, hn5, -⟩ := h.ya
        obtain ⟨ν, hν, hν5⟩ := h.yc
        have hy1 : y * (a ^ 5) = (a ^ 5) * y := by
          refine sz32_l32_comm_conj5 he5 hn5 ?_
          rw [← conj_pow, hn]
          group
        have hy2 : y * x = x * y := by
          refine sz32_l32_comm_conj5 hx5 (n := ν) hν5 ?_
          rw [← hk, ← conj_zpow, hν]
          group
        exact key y hy1.symm hy2.symm
    intro s hs t ht
    exact ((Subgroup.mem_centralizer_iff.mp (hQle hs)) t ht).symm

private theorem sz32_l32_stepA (hc : PointConfig IsSz32Type G 5 P M x J) {E : Subgroup G}
    (hEQ : E ≤ u3S P x) (hE : IsElemAbelian 5 E) (hE3 : 5 ^ 3 ≤ Nat.card E) :
    x ∈ E ∧ Nat.card E = 5 ^ 3 := by
  have hp : (5 : ℕ).Prime := by norm_num
  haveI : Fact (Nat.Prime 5) := ⟨hp⟩
  have hxp : x ^ 5 = 1 := hc.generic.2.1.2.2.1
  have hrank3 : CFSG.Open.pRank 5 (u3S P x) = 3 := hc.generic.2.2.2
  have hSC : u3S P x ≤ Subgroup.centralizer ({x} : Set G) := inf_le_right
  have hxS : x ∈ u3S P x := ⟨hc.generic.1, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hSx : ∀ s ∈ u3S P x, s * x = x * s := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mp (hSC hs)
  have hcommEx : E ≤ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    intro e he
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hSx e (hEQ he))
  have hxel : IsElemAbelian 5 (Subgroup.zpowers x) := CFSG.Open.isElemAbelian_zpowers hxp
  have hE'el : IsElemAbelian 5 (E ⊔ Subgroup.zpowers x) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting 5 hE hxel hcommEx
  have hE'S : E ⊔ Subgroup.zpowers x ≤ u3S P x := sup_le hEQ (Subgroup.zpowers_le.mpr hxS)
  have hE'p : IsPGroup 5 ↥(E ⊔ Subgroup.zpowers x) :=
    CFSG.RankThreeCoreUniqueness.Helpers.elementary_isPGroup 5 _ hE'el
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hE'p
  have hk3 : k ≤ 3 := by
    have := CFSG.SectionRank.le_pRank hp.one_lt hE'S hE'el hk
    omega
  have hEeq : E = E ⊔ Subgroup.zpowers x := by
    refine Subgroup.eq_of_le_of_card_ge le_sup_left ?_
    rw [hk]
    exact (Nat.pow_le_pow_right hp.pos hk3).trans hE3
  refine ⟨?_, le_antisymm ?_ hE3⟩
  · rw [hEeq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  · have h1 : Nat.card E ≤ Nat.card ↥(E ⊔ Subgroup.zpowers x) :=
      Subgroup.card_le_of_le le_sup_left
    rw [hk] at h1
    exact h1.trans (Nat.pow_le_pow_right hp.pos hk3)

private theorem sz32_l32_rho_iff {p : ℕ}
    (hCN : Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (J : Set G))
    {Q : Type} [Group Q] (ψ : ↥J →* Q) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = (rankThreePrimeCore p J).subgroupOf J)
    (ρ : ↥(Subgroup.centralizer ({x} : Set G)) →* MulAut Q)
    (hρ : ∀ (c : ↥(Subgroup.centralizer ({x} : Set G))) (j : ↥J)
        (hj : (c : G) * (j : G) * (c : G)⁻¹ ∈ J),
        ρ c (ψ j) = ψ ⟨(c : G) * (j : G) * (c : G)⁻¹, hj⟩)
    (g : ↥(Subgroup.centralizer ({x} : Set G))) :
    ρ g = 1 ↔ (g : G) ∈ u3K0 p x J := by
  have hOker : ∀ j : J, ψ j = 1 ↔ (j : G) ∈ rankThreePrimeCore p J := by
    intro j
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  constructor
  · intro hg
    refine ⟨g.2, hCN g.2, fun j hj => ?_⟩
    have hjj : (g : G) * j * (g : G)⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp (hCN g.2) j).mp hj
    have h1 := hρ g ⟨j, hj⟩ hjj
    rw [hg, MulAut.one_apply] at h1
    have h2 : ψ (⟨(g : G) * j * (g : G)⁻¹, hjj⟩ * (⟨j, hj⟩ : J)⁻¹) = 1 := by
      rw [map_mul, map_inv, ← h1, mul_inv_cancel]
    have := (hOker _).mp h2
    simpa using this
  · rintro ⟨-, -, hgO⟩
    ext q
    obtain ⟨j, rfl⟩ := hψ q
    have hjj : (g : G) * (j : G) * (g : G)⁻¹ ∈ J :=
      (Subgroup.mem_normalizer_iff.mp (hCN g.2) j).mp j.2
    rw [hρ g j hjj, MulAut.one_apply]
    have h2 : ψ (⟨(g : G) * j * (g : G)⁻¹, hjj⟩ * j⁻¹) = 1 := by
      rw [hOker]
      exact hgO j j.2
    rwa [map_mul, map_inv, mul_inv_eq_one] at h2

private theorem sz32_l32_ker_E (hc : PointConfig IsSz32Type G 5 P M x J) {a c y : G}
    (hA : Sz32QDecomp P x J a c y) {E : Subgroup G} (hEQ : E ≤ u3S P x)
    (hE : IsElemAbelian 5 E) {g : G} (hg : g ∈ E) :
    g ∈ u3K0 5 x J ↔ g ∈ Subgroup.zpowers x := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  constructor
  · intro h
    have h1 : g ∈ Subgroup.zpowers c := hA.QC g (hEQ hg) h
    exact fus_mem_zpowers_of_isCyclic_of_pow_prime (Z := Subgroup.zpowers c) inferInstance
      hA.pres.x_mem h1 hc.generic.2.1.2.1 hc.generic.2.1.2.2.1 (hE.2 g hg)
  · intro h
    have : Subgroup.zpowers x ≤ u3K0 5 x J := Subgroup.zpowers_le.mpr (x_mem_u3K0_gen hc)
    exact this h

private theorem sz32_l32_two_elt_eq_one {X : Type*} [Group X] {N : Subgroup X} (hodd : ¬ 2 ∣ Nat.card N)
    {k : X} (hkN : k ∈ N) {m : ℕ} (hk : k ^ (2 ^ m) = 1) : k = 1 := by
  have h1 : orderOf k ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have h2 : orderOf k ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hkN
  by_cases hj0 : j = 0
  · rw [hj0, pow_zero, orderOf_eq_one_iff] at hj'
    exact hj'
  · exfalso
    apply hodd
    rw [hj'] at h2
    exact (dvd_pow_self 2 hj0).trans h2

theorem sz32_lemma32 (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    (hSig : SignalizerTwoGroupKFact) (hSz : Sz32Facts) (hdata : Sz32DataFacts)
    (hc : PointConfig IsSz32Type G 5 P M x J) {a c y : G} (hA : Sz32QDecomp P x J a c y) :
    Lemma32Data 5 P x := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine ⟨sz32_l32_plane hA.pres, ?_⟩
  intro E F hEQ hE hE3 hF2 hFC hEF a ha f hf
  obtain ⟨hxE, hEcard⟩ := sz32_l32_stepA hc hEQ hE hE3
  set C : Subgroup G := Subgroup.centralizer ({x} : Set G) with hC
  have hEC : E ≤ C := hEQ.trans inf_le_right
  obtain ⟨Q, hQg, ψ, hψ, hker, hQ⟩ := hc.typ
  haveI : Finite Q := Finite.of_surjective ψ hψ
  obtain ⟨ρ, hρ⟩ := sps_exists_action (p := 5) hc.cent_le ψ hψ hker
  have hiff := sz32_l32_rho_iff hc.cent_le ψ hψ hker ρ hρ
  have hOJ : rankThreePrimeCore 5 J ≤ J := CFSG.AGLEmbedding.glbPrimeCore_le 5 J
  have hQZ : Subgroup.center Q = ⊥ :=
    u3main_center_bot hOJ hc.perfect hc.lt hc.minimal ψ hψ hker
  haveI hQsimple : IsSimpleGroup Q := u3_isSimple_quot hOJ hc.lt hc.minimal ψ hψ hker
  let E' : Subgroup C := E.subgroupOf C
  let F' : Subgroup C := F.subgroupOf C
  have hE'el : IsElemAbelian 5 E' := hE.subgroupOf C
  have hE'card : Nat.card E' = 5 ^ 3 := by
    rw [← hEcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEC).toEquiv
  have hF'2 : IsPGroup 2 F' := hF2.of_equiv (Subgroup.subgroupOfEquivOfLe hFC).symm
  have hEF' : ∀ e ∈ E', ∀ f ∈ F', e * f * e⁻¹ ∈ F' := by
    intro e he f hf
    have h1 : ((e : C) : G) ∈ Subgroup.normalizer (F : Set G) := hEF he
    exact (Subgroup.mem_normalizer_iff.mp h1 (f : G)).mp hf
  have hkcard : Nat.card (ρ.comp E'.subtype).ker = 5 := by
    let Z : Subgroup C := (Subgroup.zpowers x).subgroupOf C
    have hxC : Subgroup.zpowers x ≤ C :=
      Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
    have hZE : Z ≤ E' := fun g hg => Subgroup.zpowers_le.mpr hxE hg
    have hkerE : (ρ.comp E'.subtype).ker = Z.subgroupOf E' := by
      ext ε
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      show ρ (ε : C) = 1 ↔ ((ε : C) : G) ∈ Subgroup.zpowers x
      rw [hiff]
      exact sz32_l32_ker_E hc hA hEQ hE ε.2
    rw [hkerE, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZE).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hxC).toEquiv, Nat.card_zpowers, hA.pres.x_ord]
  have hcomm := sz32_l32_comm_ker hSig hQ hQsimple hQZ ρ hE'el hE'card hkcard hF'2 hEF'
  have hk := hcomm ⟨a, hEC ha⟩ ha ⟨f, hFC hf⟩ hf
  rw [hiff] at hk
  have hk' : a * f * a⁻¹ * f⁻¹ ∈ u3K0 5 x J := hk
  have hkF : a * f * a⁻¹ * f⁻¹ ∈ F :=
    F.mul_mem ((Subgroup.mem_normalizer_iff.mp (hEF ha) f).mp hf) (F.inv_mem hf)
  obtain ⟨m, hm⟩ := hF2 ⟨_, hkF⟩
  have hm' : (a * f * a⁻¹ * f⁻¹) ^ (2 ^ m) = 1 := by
    simpa using congrArg Subtype.val hm
  have hcop : Nat.Coprime 5 (orderOf (a * f * a⁻¹ * f⁻¹)) :=
    (Nat.Coprime.pow_right m (by norm_num : Nat.Coprime 5 2)).coprime_dvd_right
      (orderOf_dvd_of_pow_eq_one hm')
  have hmem := (point_prop31_ii hS hD1 hU0 hc).2 _ hk' hcop
  have hodd := odd_card_pPrimeCoreIn_of_not_le hS hD1 hc.sigma hc.core hc.generic.2.2.2.ge
    hc.generic.2.1.2.2.2.2
  have h1 : a * f * a⁻¹ * f⁻¹ = 1 := sz32_l32_two_elt_eq_one hodd hmem hm'
  rw [mul_inv_eq_one] at h1
  exact mul_inv_eq_iff_eq_mul.mp h1

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
