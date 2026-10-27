module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporHull
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveThreeYTransportCore
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporOrder

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.LocalAnalysis.RankThreeUC.AGL81C (oPPrimeHull oPPrimeHull_top_normal
  map_subtype_oPPrimeHull_top)
open CFSG.LocalAnalysis.AGL81TheoremCD.Section12 (oPrimeModPrimeComplement modPrimeComplement)
open CFSG.RankThreeEvenClassification.Helpers (primeComplementCore primeComplementCore_properties
  primeComplementCore_characteristic le_primeComplementCore)

namespace SporCent

theorem oPPrimeHull_eq_of_normal {X : Type} [Group X] [Finite X] {d : ℕ} (hd : d.Prime)
    {X₁ T₀ : Subgroup X} (hT : T₀ ≤ X₁) (hn : (T₀.subgroupOf X₁).Normal)
    (hs : IsSimpleGroup ↥T₀) (hdT : d ∣ Nat.card ↥T₀) (hidx : ¬ d ∣ (T₀.subgroupOf X₁).index) :
    oPPrimeHull d X₁ = T₀ := by
  classical
  have : Fact d.Prime := ⟨hd⟩
  have : (T₀.subgroupOf X₁).Normal := hn
  have : IsSimpleGroup ↥T₀ := hs
  set N : Subgroup ↥X₁ := oPPrimeHull d (⊤ : Subgroup ↥X₁) with hN
  have hNnormal : N.Normal := oPPrimeHull_top_normal d
  have hNmap : N.map X₁.subtype = oPPrimeHull d X₁ := map_subtype_oPPrimeHull_top X₁ d
  have hNle : N ≤ T₀.subgroupOf X₁ :=
    oPPrimeHull_top_le_of_not_dvd_index hd (T₀.subgroupOf X₁) hidx
  have hHle : oPPrimeHull d X₁ ≤ T₀ := by
    rw [← hNmap]
    have h := Subgroup.map_mono (f := X₁.subtype) hNle
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hT] at h
  have hTsubSimple : IsSimpleGroup ↥(T₀.subgroupOf X₁) :=
    (Subgroup.subgroupOfEquivOfLe hT).isSimpleGroup
  have hNtop : N = T₀.subgroupOf X₁ := by
    have hNsubNormal : (N.subgroupOf (T₀.subgroupOf X₁)).Normal := hNnormal.subgroupOf _
    rcases hTsubSimple.eq_bot_or_eq_top_of_normal
      (N.subgroupOf (T₀.subgroupOf X₁)) with hbot | htop
    · exfalso
      have hdvd : d ∣ Nat.card ↥(T₀.subgroupOf X₁) := by
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT).toEquiv]
      obtain ⟨x, hxord⟩ :=
        exists_prime_orderOf_dvd_card' (G := ↥(T₀.subgroupOf X₁)) d hdvd
      have hxN : (x : ↥X₁) ∈ N := by
        rw [hN]
        exact Subgroup.subset_closure ⟨Subgroup.mem_top _, 1, by
          rw [pow_one, Subgroup.orderOf_coe]
          exact hxord⟩
      have hx1 : x ≠ 1 := by
        intro h
        rw [h, orderOf_one] at hxord
        exact hd.ne_one hxord.symm
      have hxbot : x ∈ (⊥ : Subgroup ↥(T₀.subgroupOf X₁)) := hbot ▸ hxN
      exact hx1 (Subgroup.mem_bot.mp hxbot)
    · exact le_antisymm hNle (Subgroup.subgroupOf_eq_top.mp htop)
  have hTleH : T₀ ≤ oPPrimeHull d X₁ := by
    rw [← hNmap]
    rw [show T₀ = (T₀.subgroupOf X₁).map X₁.subtype from by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hT]]
    rw [← hNtop]
  exact le_antisymm hHle hTleH

theorem exists_normal_of_mulEquiv {X M : Type} [Group X] [Group M] {X₁ : Subgroup X}
    (ψ : ↥X₁ ≃* M) (N : Subgroup M) (hn : N.Normal) (hs : IsSimpleGroup ↥N) :
    ∃ T₀ : Subgroup X, T₀ ≤ X₁ ∧ (T₀.subgroupOf X₁).Normal ∧ IsSimpleGroup ↥T₀ ∧
      Nonempty (↥T₀ ≃* ↥N) ∧ (T₀.subgroupOf X₁).index = N.index := by
  classical
  have : N.Normal := hn
  have : IsSimpleGroup ↥N := hs
  let N' : Subgroup ↥X₁ := N.map ψ.symm.toMonoidHom
  let T₀ : Subgroup X := N'.map X₁.subtype
  have hT : T₀ ≤ X₁ := Subgroup.map_subtype_le N'
  have hN'normal : N'.Normal := hn.map ψ.symm.toMonoidHom ψ.symm.surjective
  have hsub : T₀.subgroupOf X₁ = N' := by
    apply Subgroup.map_injective X₁.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hT]
  have hnormal : (T₀.subgroupOf X₁).Normal := hsub ▸ hN'normal
  let e₁ : ↥N ≃* ↥N' := Subgroup.equivMapOfInjective N ψ.symm.toMonoidHom
    ψ.symm.injective
  let e₂ : ↥N' ≃* ↥T₀ := Subgroup.equivMapOfInjective N' X₁.subtype
    X₁.subtype_injective
  let e : ↥T₀ ≃* ↥N := e₂.symm.trans e₁.symm
  have hsimple : IsSimpleGroup ↥T₀ := e.isSimpleGroup
  refine ⟨T₀, hT, hnormal, hsimple, ⟨e⟩, ?_⟩
  rw [hsub]
  exact Subgroup.index_map_equiv N ψ.symm

theorem centralizer_inf_eq_bot_of_index_two {X : Type} [Group X] [Finite X]
    {K X₁ T₀ : Subgroup X} (hX₁K : X₁ ≤ K) (hT : T₀ ≤ X₁) (hn : (T₀.subgroupOf X₁).Normal)
    (hs : IsSimpleGroup ↥T₀) (hp : ¬ (Nat.card ↥T₀).Prime) (hidx : (T₀.subgroupOf X₁).index = 2)
    (hC : Subgroup.centralizer (T₀ : Set X) ⊓ K ≤ X₁)
    (hinv : ∀ z : ↥K, orderOf z = 2 →
      ¬ Nat.card ↥T₀ ∣ Nat.card (Subgroup.centralizer ({z} : Set ↥K))) :
    Subgroup.centralizer (T₀ : Set X) ⊓ K = ⊥ := by
  classical
  have : IsSimpleGroup ↥T₀ := hs
  have : (T₀.subgroupOf X₁).Normal := hn
  have hTsubK : T₀ ≤ K := hT.trans hX₁K
  set C : Subgroup X := Subgroup.centralizer (T₀ : Set X) ⊓ K with hCdef
  have hCX₁ : C ≤ X₁ := hC
  have hZ : Subgroup.center ↥T₀ = ⊥ := center_eq_bot_of_not_prime hp
  have hCT : C ⊓ T₀ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxcenter : (⟨x, hx.2⟩ : ↥T₀) ∈ Subgroup.center ↥T₀ := by
      rw [Subgroup.mem_center_iff]
      intro t
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hx.1.1 t t.2
    rw [hZ, Subgroup.mem_bot] at hxcenter
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hxcenter)
  let f : ↥C →* ↥X₁ ⧸ (T₀.subgroupOf X₁) :=
    (QuotientGroup.mk' (T₀.subgroupOf X₁)).comp (Subgroup.inclusion hCX₁)
  have hfker : f.ker = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    rw [MonoidHom.mem_ker] at hc
    have hcT : (c : X) ∈ T₀ := by
      have h := (QuotientGroup.eq_one_iff (Subgroup.inclusion hCX₁ c)).mp hc
      exact Subgroup.mem_subgroupOf.mp h
    have hcbot : (c : X) ∈ C ⊓ T₀ := ⟨c.2, hcT⟩
    rw [hCT] at hcbot
    exact Subtype.ext (Subgroup.mem_bot.mp hcbot)
  have hf : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hfker
  have hdvd : Nat.card ↥C ∣ 2 := by
    have hcard : Nat.card ↥C = Nat.card ↥f.range :=
      Nat.card_congr (MonoidHom.ofInjective hf).toEquiv
    rw [hcard]
    have h := Subgroup.card_dvd_of_le (H := f.range) (K := ⊤) le_top
    rw [Subgroup.card_top, ← Subgroup.index_eq_card, hidx] at h
    exact h
  have hcardne : Nat.card ↥C ≠ 2 := by
    intro hC2
    obtain ⟨z, hzord⟩ :=
      exists_prime_orderOf_dvd_card' (G := ↥C) 2 (by rw [hC2])
    let zK : ↥K := ⟨(z : X), z.2.2⟩
    have hzX : orderOf (z : X) = 2 := by
      rw [Subgroup.orderOf_coe, hzord]
    have hzKord : orderOf zK = 2 := by
      rw [← Subgroup.orderOf_coe zK]
      exact hzX
    have hle : T₀.subgroupOf K ≤
        Subgroup.centralizer ({zK} : Set ↥K) := by
      intro t ht
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp z.2.1 t.val ht).symm
    have hdvdT : Nat.card ↥T₀ ∣
        Nat.card (Subgroup.centralizer ({zK} : Set ↥K)) := by
      have h := Subgroup.card_dvd_of_le hle
      rwa [Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe hTsubK).toEquiv] at h
    exact hinv zK hzKord hdvdT
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exact Subgroup.card_eq_one.mp h1
  · exact absurd h2 hcardne

end SporCent

namespace ThreeNineHyp

variable {X : Type} [Group X] [Finite X] {K E D X₁ : Subgroup X} {p d : ℕ}

theorem centralizer_oPPrimeHull_inf_le (h : ThreeNineHyp K E D X₁ p d) :
    Subgroup.centralizer (oPPrimeHull d X₁ : Set X) ⊓ K ≤ X₁ := by
  have : Fact d.Prime := ⟨h.d_prime⟩
  have hDle : D ≤ oPPrimeHull d X₁ := by
    intro g hgD
    obtain ⟨k, hk⟩ := h.isPGroup_D.exists_orderOf_dvd_pow (⟨g, hgD⟩ : D)
    have hk' : orderOf g ∣ d ^ k := by rwa [Subgroup.orderOf_mk] at hk
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow h.d_prime).mp hk'
    exact Subgroup.subset_closure ⟨h.D_le hgD, m, hm⟩
  obtain ⟨⟨g, hgD⟩, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.D_ne_bot
  have hg1' : g ≠ 1 := fun hg => hg1 (Subtype.ext hg)
  rintro x ⟨hxcent, hxK⟩
  exact h.mem_of_commute_D hgD hg1' ((le_sup_left : K ≤ K ⊔ D) hxK)
    (Subgroup.mem_centralizer_iff.mp hxcent g (hDle hgD))

theorem socle_of_index_two (h : ThreeNineHyp K E D X₁ p d) (hDK : D ≤ K) {T₀ : Subgroup X}
    (hT : T₀ ≤ X₁) (hn : (T₀.subgroupOf X₁).Normal) (hs : IsSimpleGroup ↥T₀)
    (hp : ¬ (Nat.card ↥T₀).Prime) (hdT : d ∣ Nat.card ↥T₀) (hidx : (T₀.subgroupOf X₁).index = 2)
    (hinv : ∀ z : ↥K, orderOf z = 2 →
      ¬ Nat.card ↥T₀ ∣ Nat.card (Subgroup.centralizer ({z} : Set ↥K))) :
    IsSimpleGroup ↥(oPPrimeHull d X₁) ∧
      Subgroup.centralizer (oPPrimeHull d X₁ : Set X) ⊓ K = ⊥ := by
  have hX₁K : X₁ ≤ K := h.lt.le.trans (sup_le le_rfl hDK)
  have hidx' : ¬ d ∣ (T₀.subgroupOf X₁).index := by
    intro hdvd
    exact h.d_ne_two ((Nat.prime_dvd_prime_iff_eq h.d_prime Nat.prime_two).mp
      (hidx ▸ hdvd))
  have hH : oPPrimeHull d X₁ = T₀ :=
    SporCent.oPPrimeHull_eq_of_normal h.d_prime hT hn hs hdT hidx'
  constructor
  · exact hH.symm ▸ hs
  · rw [hH]
    exact SporCent.centralizer_inf_eq_bot_of_index_two hX₁K hT hn hs hp hidx
      (by simpa [hH] using h.centralizer_oPPrimeHull_inf_le) hinv

theorem socle_of_centralizer_eq_bot (h : ThreeNineHyp K E D X₁ p d) {T₀ : Subgroup X}
    (hT : T₀ ≤ X₁) (hn : (T₀.subgroupOf X₁).Normal) (hs : IsSimpleGroup ↥T₀)
    (hdT : d ∣ Nat.card ↥T₀) (hidx : ¬ d ∣ (T₀.subgroupOf X₁).index)
    (hC : Subgroup.centralizer (T₀ : Set X) ⊓ K = ⊥) :
    IsSimpleGroup ↥(oPPrimeHull d X₁) ∧
      Subgroup.centralizer (oPPrimeHull d X₁ : Set X) ⊓ K = ⊥ := by
  have hH : oPPrimeHull d X₁ = T₀ :=
    SporCent.oPPrimeHull_eq_of_normal h.d_prime hT hn hs hdT hidx
  exact ⟨hH.symm ▸ hs, hH.symm ▸ hC⟩

theorem socle_of_primeComplementCore_eq_bot (h : ThreeNineHyp K E D X₁ p d) (hDK : D ≤ K)
    (hcore : primeComplementCore (↥X₁) d = ⊥)
    (hs : IsSimpleGroup (oPrimeModPrimeComplement d X₁))
    (hp : ¬ (Nat.card (oPrimeModPrimeComplement d X₁)).Prime) :
    IsSimpleGroup ↥(oPPrimeHull d X₁) ∧
      Subgroup.centralizer (oPPrimeHull d X₁ : Set X) ⊓ K = ⊥ := by
  classical
  have : Fact d.Prime := ⟨h.d_prime⟩
  have hX₁K : X₁ ≤ K := h.lt.le.trans (sup_le le_rfl hDK)
  let N : Subgroup ↥X₁ := oPPrimeHull d (⊤ : Subgroup ↥X₁)
  have hNnormal : N.Normal := oPPrimeHull_top_normal d
  have : N.Normal := hNnormal
  have hNmap : N.map X₁.subtype = oPPrimeHull d X₁ := map_subtype_oPPrimeHull_top X₁ d
  let O : Subgroup ↥N := primeComplementCore (G := ↥N) d
  have hOcop : ¬ d ∣ Nat.card O := (primeComplementCore_properties ↥N d h.d_prime).2
  have hOchar : O.Characteristic := primeComplementCore_characteristic ↥N d h.d_prime
  have : O.Characteristic := hOchar
  have hmapNormal : (O.map N.subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  have hmapcard : Nat.card (O.map N.subtype) = Nat.card O :=
    Subgroup.card_map_of_injective N.subtype_injective
  have hmapcop : ¬ d ∣ Nat.card (O.map N.subtype) := by rwa [hmapcard]
  have hOle : O.map N.subtype ≤ primeComplementCore (G := ↥X₁) d :=
    le_primeComplementCore d _ hmapNormal hmapcop
  rw [hcore] at hOle
  have hObot : O = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective O N.subtype_injective).mp
      (le_bot_iff.mp hOle)
  let e₁ : ↥N ≃* ↥(N.map X₁.subtype) :=
    Subgroup.equivMapOfInjective N X₁.subtype X₁.subtype_injective
  let eNH : ↥N ≃* ↥(oPPrimeHull d X₁) := e₁.trans (MulEquiv.subgroupCongr hNmap)
  have hHcore : primeComplementCore (G := ↥(oPPrimeHull d X₁)) d = ⊥ := by
    have hmap : O.map eNH.toMonoidHom =
        primeComplementCore (G := ↥(oPPrimeHull d X₁)) d :=
      CFSG.RankThreeEvenClassification.Helpers.primeComplementCore_map_equiv
        (G := ↥N) d h.d_prime eNH
    rw [hObot, Subgroup.map_bot] at hmap
    exact hmap.symm
  obtain ⟨eQ⟩ :=
    CFSG.LocalAnalysis.AGL81TheoremCD.Section12.nonempty_oPrimeModPrimeComplement_mulEquiv
      h.d_prime X₁
  let eH : modPrimeComplement d (oPPrimeHull d X₁) ≃* ↥(oPPrimeHull d X₁) :=
    (QuotientGroup.quotientMulEquivOfEq hHcore).trans QuotientGroup.quotientBot
  let eQH : oPrimeModPrimeComplement d X₁ ≃* ↥(oPPrimeHull d X₁) := eQ.trans eH
  have : IsSimpleGroup (oPrimeModPrimeComplement d X₁) := hs
  have hHsimple : IsSimpleGroup ↥(oPPrimeHull d X₁) := eQH.symm.isSimpleGroup
  have : IsSimpleGroup ↥(oPPrimeHull d X₁) := hHsimple
  have hHcardnp : ¬ (Nat.card ↥(oPPrimeHull d X₁)).Prime := by
    rw [← Nat.card_congr eQH.toEquiv]
    exact hp
  set C : Subgroup X :=
    Subgroup.centralizer (oPPrimeHull d X₁ : Set X) ⊓ K with hCdef
  have hCX₁ : C ≤ X₁ := h.centralizer_oPPrimeHull_inf_le
  have hHleX₁ : oPPrimeHull d X₁ ≤ X₁ := by
    rw [oPPrimeHull, Subgroup.closure_le]
    rintro x ⟨hx, -⟩
    exact hx
  have hHsubNormal : ((oPPrimeHull d X₁).subgroupOf X₁).Normal := by
    have hsub : (oPPrimeHull d X₁).subgroupOf X₁ = N := by
      apply Subgroup.map_injective X₁.subtype_injective
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hHleX₁]
      exact hNmap.symm
    rw [hsub]
    exact hNnormal
  have hCH : C ⊓ oPPrimeHull d X₁ = ⊥ := by
    have hZ : Subgroup.center ↥(oPPrimeHull d X₁) = ⊥ :=
      SporCent.center_eq_bot_of_not_prime hHcardnp
    rw [eq_bot_iff]
    intro x hx
    have hxcenter : (⟨x, hx.2⟩ : ↥(oPPrimeHull d X₁)) ∈
        Subgroup.center ↥(oPPrimeHull d X₁) := by
      rw [Subgroup.mem_center_iff]
      intro t
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hx.1.1 t t.2
    rw [hZ, Subgroup.mem_bot] at hxcenter
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hxcenter)
  have hno_d : ¬ d ∣ Nat.card ↥C := by
    intro hdvd
    obtain ⟨c, hcord⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) d hdvd
    have hcordX : orderOf (c : X) = d := by
      rw [Subgroup.orderOf_coe, hcord]
    have hmemH : (c : X) ∈ oPPrimeHull d X₁ :=
      Subgroup.subset_closure ⟨hCX₁ c.2, 1, by rw [pow_one, hcordX]⟩
    have hmemBot : (c : X) ∈ C ⊓ oPPrimeHull d X₁ := ⟨c.2, hmemH⟩
    rw [hCH] at hmemBot
    have hc1 : c = 1 := Subtype.ext (Subgroup.mem_bot.mp hmemBot)
    rw [hc1, orderOf_one] at hcord
    exact h.d_prime.ne_one hcord.symm
  have hCsubNormal : (C.subgroupOf X₁).Normal := by
    refine Subgroup.Normal.mk ?_
    intro c hc g
    rw [Subgroup.mem_subgroupOf] at hc ⊢
    rw [hCdef]
    constructor
    · refine Subgroup.mem_centralizer_iff.mpr ?_
      intro y hy
      have hyH : (g : X)⁻¹ * y * (g : X) ∈ oPPrimeHull d X₁ := by
        have hconj := hHsubNormal.conj_mem (⟨y, hHleX₁ hy⟩ : ↥X₁)
          (Subgroup.mem_subgroupOf.mpr hy) g⁻¹
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] using
          Subgroup.mem_subgroupOf.mp hconj
      have hcy := Subgroup.mem_centralizer_iff.mp hc.1
        ((g : X)⁻¹ * y * (g : X)) hyH
      calc y * ((g : X) * (c : X) * (g : X)⁻¹)
          = (g : X) * (((g : X)⁻¹ * y * (g : X)) * (c : X)) * (g : X)⁻¹ := by
            group
        _ = (g : X) * ((c : X) * ((g : X)⁻¹ * y * (g : X))) * (g : X)⁻¹ := by
            rw [hcy]
        _ = ((g : X) * (c : X) * (g : X)⁻¹) * y := by group
    · exact h.normal.conj_mem (c : X) hc.2 (g : X)
  have hCsubCop : ¬ d ∣ Nat.card (C.subgroupOf X₁) := by
    rwa [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCX₁).toEquiv] at hno_d
  have hCsubBot : C.subgroupOf X₁ = ⊥ := by
    have hle : C.subgroupOf X₁ ≤ primeComplementCore (G := ↥X₁) d :=
      le_primeComplementCore d _ hCsubNormal hCsubCop
    rw [hcore] at hle
    exact le_bot_iff.mp hle
  have hCbot : C = ⊥ :=
    (Subgroup.subgroupOf_eq_bot.mp hCsubBot).eq_bot_of_le hCX₁
  exact ⟨hHsimple, hCbot⟩

end ThreeNineHyp

end CFSG.LocalAnalysis.AGL81I.Section3
