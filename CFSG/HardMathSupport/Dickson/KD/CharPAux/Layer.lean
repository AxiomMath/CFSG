module

public import CFSG.GH74.GLS.Stage2.OddAut.PFix
public import CFSG.GH74.GLS.Stage2.OddAut.BTCanon
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.GLTheoremB.GammaStarConj

public section

namespace CFSG.HardMathSupport.Dickson.KD

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LieType.BorelTits
  CFSG.GH74.GLS.Stage2.OddAut
open scoped commutatorElement

section Elementary

variable {G : Type*} [Group G]

theorem eq_one_of_mem_pGroup_of_coprime {p : ℕ} [Fact p.Prime] {V : Subgroup G} (hV : IsPGroup p V)
    {c : G} (hc : c ∈ V) (hcop : (orderOf c).Coprime p) : c = 1 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hV) ⟨c, hc⟩
  rw [Subgroup.orderOf_mk] at hk
  rw [hk] at hcop
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [pow_zero] at hk
    exact orderOf_eq_one_iff.1 hk
  · exfalso
    have h2 := Nat.Coprime.eq_one_of_dvd hcop.symm (dvd_pow_self p hk0.ne')
    exact (Fact.out : p.Prime).ne_one h2

end Elementary

section Component

variable {G : Type*} [Group G] [Finite G]

theorem commutator_mem_pPrimeCoreOf_of_glaPComponent {p : ℕ} {X L N : Subgroup G}
    (hL : GLAPComponent p X L) (hNn : (N.subgroupOf X).Normal) (hNs : Group.IsSolvable N)
    {a b : G} (ha : a ∈ L) (hb : b ∈ N) (hNX : N ≤ X) :
    a * b * a⁻¹ * b⁻¹ ∈ GLAPPrimeCoreOf p X := by
  classical
  let π : ↥X →* (↥X ⧸ GLAPPrimeCore p ↥X) := QuotientGroup.mk' (GLAPPrimeCore p ↥X)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hLX : L ≤ X := hL.1
  have hbar : CFSG.Open.IsComponentOf (barX p X L) ⊤ := hL.2.2.1
  have hJc : CFSG.IsComponent (barX p X L) := (CFSG.isComponent_iff_open _).2 hbar
  have hNb : ((N.subgroupOf X).map π).Normal := hNn.map π hπ
  have hNsol : Group.IsSolvable ↥(N.subgroupOf X) := by
    haveI := hNs
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hNX).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hNX).injective
  have hNbsol : Group.IsSolvable ↥((N.subgroupOf X).map π) := by
    have : ((N.subgroupOf X).map π) = (π.domRestrict (N.subgroupOf X)).range :=
      (MonoidHom.domRestrict_range (N.subgroupOf X) π).symm
    rw [this]
    exact Group.isSolvable_of_surjective (π.domRestrict (N.subgroupOf X)).rangeRestrict_surjective
  have hcomm := (CFSG.LocalCores.component_solvable_centralizer hNbsol hNb.isSubnormal).1 _ hJc
  have haL : π ⟨a, hLX ha⟩ ∈ barX p X L := ⟨⟨a, hLX ha⟩, Subgroup.mem_subgroupOf.2 ha, rfl⟩
  have hbN : π ⟨b, hNX hb⟩ ∈ (N.subgroupOf X).map π :=
    ⟨⟨b, hNX hb⟩, Subgroup.mem_subgroupOf.2 hb, rfl⟩
  have h1 : ⁅π ⟨a, hLX ha⟩, π ⟨b, hNX hb⟩⁆ = 1 := by
    have := Subgroup.commutator_mem_commutator haL hbN
    rw [hcomm] at this
    exact this
  rw [← map_commutatorElement] at h1
  have h2 : (⁅(⟨a, hLX ha⟩ : ↥X), (⟨b, hNX hb⟩ : ↥X)⁆ : ↥X) ∈ GLAPPrimeCore p ↥X :=
    (QuotientGroup.eq_one_iff _).1 h1
  exact ⟨_, h2, rfl⟩

end Component

section Layer0

variable {G : Type*} [Group G] [Finite G]

theorem false_of_glaPComponent_of_solvable {p : ℕ} {X L : Subgroup G} (hL : GLAPComponent p X L)
    (hsolL : Group.IsSolvable ↥(L.subgroupOf X)) : False := by
  classical
  have hbar : CFSG.Open.IsComponentOf (barX p X L) ⊤ := hL.2.2.1
  have hJc : CFSG.IsComponent (barX p X L) := (CFSG.isComponent_iff_open _).2 hbar
  have hsolJ : Group.IsSolvable ↥(barX p X L) := by
    have : barX p X L = ((QuotientGroup.mk' (GLAPPrimeCore p ↥X)).domRestrict
        (L.subgroupOf X)).range :=
      (MonoidHom.domRestrict_range _ _).symm
    rw [this]
    exact Group.isSolvable_of_surjective
      ((QuotientGroup.mk' (GLAPPrimeCore p ↥X)).domRestrict
        (L.subgroupOf X)).rangeRestrict_surjective
  have : Nontrivial ↥(barX p X L) := CFSG.LocalCores.isQuasisimple_nontrivial hJc.1
  have : Group.IsPerfect ↥(barX p X L) := hJc.1.1
  exact Group.IsPerfect.not_isSolvable _ hsolJ

theorem false_of_glaPComponent_of_pPrime_eq_one {p : ℕ} [Fact p.Prime] {X L : Subgroup G}
    (hL : GLAPComponent p X L) (hid : ∀ s ∈ L, (orderOf s).Coprime p → s = 1) : False := by
  classical
  have hp : p.Prime := Fact.out
  have hLX : L ≤ X := hL.1
  have hLp : IsPGroup p L := by
    rw [IsPGroup.iff_card]
    refine ⟨(Nat.card L).primeFactorsList.length, ?_⟩
    refine Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {q} hq hqd => ?_
    by_contra hne
    have : Fact q.Prime := ⟨hq⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := L) q hqd
    have hxo : orderOf (x : G) = q := by rw [Subgroup.orderOf_coe]; exact hx
    have h1 : (x : G) = 1 := hid x x.2 (by rw [hxo]; exact (Nat.coprime_primes hq hp).2 hne)
    rw [h1, orderOf_one] at hxo
    exact hq.ne_one hxo.symm
  refine false_of_glaPComponent_of_solvable hL ?_
  have hpg : IsPGroup p ↥(L.subgroupOf X) := hLp.of_equiv (Subgroup.subgroupOfEquivOfLe hLX).symm
  haveI := hpg.isNilpotent
  infer_instance

theorem false_of_glaPComponent_of_comm {p : ℕ} {X L : Subgroup G}
    (hL : GLAPComponent p X L) (hc : ∀ a b : G, a * b = b * a) : False := by
  refine false_of_glaPComponent_of_solvable hL (isSolvable_of_comm fun a b => ?_)
  apply Subtype.ext
  apply Subtype.ext
  exact hc _ _

end Layer0

section Layer

variable {G : Type*} [Group G] [Finite G]

theorem gLAPLayer_centralizer_eq_bot {p : ℕ} [Fact p.Prime] {R : Subgroup G} (hRp : IsPGroup p R)
    {v : G} (hvR : v ∈ R)
    (hXN : Subgroup.centralizer ({v} : Set G) ≤ Subgroup.normalizer (R : Set G))
    (hC : Subgroup.centralizer (R : Set G) ≤ R) :
    GLAPLayer p (Subgroup.centralizer ({v} : Set G)) = ⊥ := by
  classical
  have hp : p.Prime := Fact.out
  set X : Subgroup G := Subgroup.centralizer ({v} : Set G) with hX
  refine le_bot_iff.1 (sSup_le fun L hL => ?_)
  exfalso
  have hLX : L ≤ X := hL.1
  set V : Subgroup G := R ⊓ X with hV
  have hVX : V ≤ X := inf_le_right
  have hVn : (V.subgroupOf X).Normal := by
    refine ⟨fun y hy x => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    refine ⟨?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.1 (hXN x.2) (y : G)).1 hy.1
      simpa using this
    · simpa using X.mul_mem (X.mul_mem x.2 hy.2) (X.inv_mem x.2)
  have hVp : IsPGroup p V := hRp.to_le inf_le_left
  have hVs : Group.IsSolvable V := by
    haveI := hVp.isNilpotent
    infer_instance
  have hcommV : ∀ a ∈ L, ∀ b ∈ V, a * b = b * a := by
    intro a ha b hb
    have h1 := commutator_mem_pPrimeCoreOf_of_glaPComponent hL hVn hVs ha hb hVX
    have h2 : a * b * a⁻¹ * b⁻¹ ∈ V := by
      have := hVn.conj_mem ⟨b, hVX hb⟩ (Subgroup.mem_subgroupOf.2 hb) ⟨a, hLX ha⟩
      have h' : (a * b * a⁻¹ : G) ∈ V := by simpa using Subgroup.mem_subgroupOf.1 this
      exact V.mul_mem h' (V.inv_mem hb)
    have h3 := CFSG.HardMathSupport.Timmesfeld.Proving.orderOf_coprime_of_mem_GLAPPrimeCoreOf hp h1
    have h4 := eq_one_of_mem_pGroup_of_coprime hVp h2 h3
    have h5 : a * b * a⁻¹ = b := by
      have := mul_inv_eq_one.1 h4
      exact this
    calc a * b = a * b * a⁻¹ * a := by group
      _ = b * a := by rw [h5]
  have hid : ∀ s ∈ L, (orderOf s).Coprime p → s = 1 := by
    intro s hs hcop
    have hsX : s ∈ X := hLX hs
    have hsN : s ∈ Subgroup.normalizer (R : Set G) := hXN hsX
    have hsv : s * v = v * s := Subgroup.mem_centralizer_singleton_iff.1 hsX
    let α : MulAut R := Subgroup.normalizerMonoidHom R ⟨s, hsN⟩
    have hα : ∀ r : R, ((α r : R) : G) = s * r * s⁻¹ := fun r => by
      simp [α, Subgroup.normalizerMonoidHom_apply_apply_coe]
    have hord : (orderOf α).Coprime p := by
      have h1 : orderOf α ∣ orderOf (⟨s, hsN⟩ : Subgroup.normalizer (R : Set G)) :=
        orderOf_map_dvd (Subgroup.normalizerMonoidHom R) _
      have h2 : orderOf (⟨s, hsN⟩ : Subgroup.normalizer (R : Set G)) = orderOf s :=
        Subgroup.orderOf_mk _ _
      rw [h2] at h1
      exact Nat.Coprime.coprime_dvd_left h1 hcop
    have hαv : α ⟨v, hvR⟩ = ⟨v, hvR⟩ := by
      apply Subtype.ext
      rw [hα]
      show s * v * s⁻¹ = v
      rw [hsv]
      group
    have hαC : ∀ u : R, u * (⟨v, hvR⟩ : R) = (⟨v, hvR⟩ : R) * u → α u = u := by
      intro u hu
      have huv : (u : G) * v = v * u := congrArg Subtype.val hu
      have huV : (u : G) ∈ V := ⟨u.2, Subgroup.mem_centralizer_singleton_iff.2 huv⟩
      apply Subtype.ext
      rw [hα]
      have := hcommV s hs u huV
      rw [this]
      group
    have hα1 : α = 1 := eq_one_of_fix_centralizer hRp α hord ⟨v, hvR⟩ hαv hαC
    have hsC : s ∈ Subgroup.centralizer (R : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      have h1 := congrArg (fun φ : MulAut R => ((φ ⟨r, hr⟩ : R) : G)) hα1
      simp only [hα, MulAut.one_apply] at h1
      calc r * s = (s * r * s⁻¹) * s := by rw [h1]
        _ = s * r := by group
    exact eq_one_of_mem_pGroup_of_coprime hRp (hC hsC) hcop
  exact false_of_glaPComponent_of_pPrime_eq_one hL hid

theorem gLAPLayer_centralizer_eq_bot_of_framework {p : ℕ} [Fact p.Prime]
    (hZ : Subgroup.center G = ⊥) (g : G) (Gen T : Set G)
    (h1 : ∀ q ∈ Gen ∪ T, g * q = q * g)
    (hT : ∀ s q, s * g = g * s → q ∈ T → s * q = q * s)
    (hGen : ∀ s q, s * g = g * s → q ∈ Gen → s * q * s⁻¹ ∈ Gen)
    (huniq : ∀ s : G, (orderOf s).Coprime p →
      (∀ q ∈ Gen ∪ T, (MulAut.conj s : MulAut G) q = q) → (MulAut.conj s : MulAut G) = 1)
    (hMp : IsPGroup p (Subgroup.closure (Gen ∪ T))) :
    GLAPLayer p (Subgroup.centralizer ({g} : Set G)) = ⊥ := by
  classical
  have hp : p.Prime := Fact.out
  set X : Subgroup G := Subgroup.centralizer ({g} : Set G) with hX
  set M : Subgroup G := Subgroup.closure (Gen ∪ T) with hM
  have hinj : Function.Injective (MulAut.conj : G →* MulAut G) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_bot]
    have : a ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro y
      have := congrArg (fun f : MulAut G => f y) (MonoidHom.mem_ker.1 ha)
      simp [MulAut.conj_apply] at this
      exact (by simpa [mul_inv_eq_iff_eq_mul] using this : a * y = y * a).symm
    rw [hZ] at this
    exact this
  have hMX : M ≤ X := by
    refine (Subgroup.closure_le _).2 fun q hq => ?_
    exact Subgroup.mem_centralizer_singleton_iff.2 (h1 q hq).symm
  have hMconj : ∀ s : G, s * g = g * s → ∀ m ∈ M, s * m * s⁻¹ ∈ M := by
    intro s hs m hm
    have : M ≤ M.comap (MulAut.conj s).toMonoidHom := by
      refine (Subgroup.closure_le _).2 fun q hq => ?_
      show s * q * s⁻¹ ∈ M
      rcases hq with hq | hq
      · exact Subgroup.subset_closure (Or.inl (hGen s q hs hq))
      · have : s * q * s⁻¹ = q := by rw [hT s q hs hq]; group
        rw [this]
        exact Subgroup.subset_closure (Or.inr hq)
    exact this hm
  have hMn : (M.subgroupOf X).Normal := by
    refine ⟨fun y hy x => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    have hxg : (x : G) * g = g * x := (Subgroup.mem_centralizer_singleton_iff.1 x.2)
    simpa using hMconj x hxg y hy
  have hMs : Group.IsSolvable M := by
    haveI := hMp.isNilpotent
    infer_instance
  refine le_bot_iff.1 (sSup_le fun L hL => ?_)
  exfalso
  have hLX : L ≤ X := hL.1
  have hcommM : ∀ a ∈ L, ∀ b ∈ M, a * b = b * a := by
    intro a ha b hb
    have h1' := commutator_mem_pPrimeCoreOf_of_glaPComponent hL hMn hMs ha hb hMX
    have h2 : a * b * a⁻¹ * b⁻¹ ∈ M := by
      have := hMn.conj_mem ⟨b, hMX hb⟩ (Subgroup.mem_subgroupOf.2 hb) ⟨a, hLX ha⟩
      have h' : (a * b * a⁻¹ : G) ∈ M := by simpa using Subgroup.mem_subgroupOf.1 this
      exact M.mul_mem h' (M.inv_mem hb)
    have h3 := CFSG.HardMathSupport.Timmesfeld.Proving.orderOf_coprime_of_mem_GLAPPrimeCoreOf hp h1'
    have h4 := eq_one_of_mem_pGroup_of_coprime hMp h2 h3
    have h5 : a * b * a⁻¹ = b := mul_inv_eq_one.1 h4
    calc a * b = a * b * a⁻¹ * a := by group
      _ = b * a := by rw [h5]
  have hid : ∀ s ∈ L, (orderOf s).Coprime p → s = 1 := by
    intro s hs hcop
    have h1 : (MulAut.conj s : MulAut G) = 1 := by
      refine huniq s hcop fun q hq => ?_
      have := hcommM s hs q (Subgroup.subset_closure hq)
      simp only [MulAut.conj_apply]
      rw [this]
      group
    exact hinj (by rw [h1, map_one])
  exact false_of_glaPComponent_of_pPrime_eq_one hL hid

end Layer

section RadCent

variable {S : Type*} [Group S]

variable (S) in
@[expose] def RadCent (p : ℕ) : Prop :=
  ∀ R : Subgroup S, R ≠ ⊥ → IsPGroup p R →
    pCoreOf p (Subgroup.normalizer (R : Set S)) = R → Subgroup.normalizer (R : Set S) ≠ ⊤ →
    (∃ Sy : Sylow p S, Subgroup.normalizer ((Sy : Subgroup S) : Set S) ≤
      Subgroup.normalizer (R : Set S)) →
    Subgroup.centralizer (R : Set S) ≤ R

theorem gLAPLayer_centralizer_eq_bot_of_holds [Finite S] {p : ℕ} [Fact p.Prime] (hBT : Holds S p)
    (hRC : RadCent S p) {u : S} (hu : orderOf u = p) :
    GLAPLayer p (Subgroup.centralizer ({u} : Set S)) = ⊥ := by
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hu
    exact (Fact.out : p.Prime).ne_one hu.symm
  have hR0p : IsPGroup p (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu, pow_one])
  have hR0 : Subgroup.zpowers u ≠ ⊥ := by
    intro h
    apply hu1
    have : u ∈ Subgroup.zpowers u := Subgroup.mem_zpowers u
    rw [h, Subgroup.mem_bot] at this
    exact this
  obtain ⟨hR0le, hRp, hN0, hNne, hcore, hSyl⟩ := canonical_parabolic hBT hR0 hR0p
  set R : Subgroup S := radInf p (Subgroup.zpowers u) with hR
  have hRne : R ≠ ⊥ := fun h => hR0 (le_bot_iff.1 (hR0le.trans h.le))
  have hCR : Subgroup.centralizer (R : Set S) ≤ R := hRC R hRne hRp hcore hNne hSyl
  have huR : u ∈ R := hR0le (Subgroup.mem_zpowers u)
  refine gLAPLayer_centralizer_eq_bot hRp huR (fun c hc => ?_) hCR
  have hc' : c * u = u * c := Subgroup.mem_centralizer_singleton_iff.1 hc
  have hcN : c ∈ Subgroup.normalizer ((Subgroup.zpowers u : Subgroup S) : Set S) := by
    have hcC : c ∈ Subgroup.centralizer ((Subgroup.zpowers u : Subgroup S) : Set S) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro h ⟨k, rfl⟩
      exact ((Commute.zpow_right (show Commute c u from hc') k).eq).symm
    exact Subgroup.centralizer_le_normalizer _ hcC
  exact hN0 hcN

end RadCent

end CFSG.HardMathSupport.Dickson.KD
