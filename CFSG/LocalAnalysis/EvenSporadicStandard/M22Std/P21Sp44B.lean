module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.P21Sp44A
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveSp4Out
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.P21Gl8
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResH2Sp44
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.EvenSporadicStandard.M24Std
  CFSG.EvenSporadicStandard.M24Std.CResH4

theorem isCyclic_outer_of_lieModel_sp44 {E : Type} [Group E] (h : LieModel E .PSp 2 2 2) :
    IsCyclic (CFSG.ComponentClassification.OuterAutomorphisms.Outer E) := by
  have hc := CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id hc
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 ^ 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  have := (CFSG.QuasithinUnique.Lin2.sp4OutCyclic K 2 hcard (by norm_num)).1
  exact isCyclic_of_surjective
    (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).symm.toMonoidHom
    (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).symm.surjective

variable {G : Type} [Group G] [Finite G] {z : G}

@[expose] noncomputable def outerHom (U : Subgroup G) [U.Normal] :
    G →* CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥U :=
  (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥U)).comp
    MulAut.conjNormal

omit [Finite G] in
theorem outerHom_eq_one_iff (U : Subgroup G) [U.Normal] (g : G) :
    outerHom U g = 1 ↔ ∃ u : U, ∀ x : U, g * x * g⁻¹ = (u : G) * x * (u : G)⁻¹ := by
  unfold outerHom
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u, fun x => ?_⟩
    have := congrArg (fun a : MulAut ↥U => ((a x : ↥U) : G)) hu
    simpa [MulAut.conj_apply, MulAut.conjNormal_apply] using this.symm
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_⟩
    ext x
    simp [MulAut.conj_apply, MulAut.conjNormal_apply, hu x]

omit [Finite G] in
theorem exists_decomp (U : Subgroup G) [U.Normal] {g : G} (h : outerHom U g = 1) :
    ∃ u ∈ U, ∃ k ∈ centralizer (U : Set G), g = u * k := by
  obtain ⟨u, hu⟩ := (outerHom_eq_one_iff U g).1 h
  refine ⟨u, u.2, (u : G)⁻¹ * g, ?_, by group⟩
  rw [mem_centralizer_iff]
  intro x hx
  have h1 := hu ⟨x, hx⟩
  have h2 : g * x = (u : G) * x * (u : G)⁻¹ * g := by
    simp only at h1
    rw [← h1]
    group
  calc x * ((u : G)⁻¹ * g) = (u : G)⁻¹ * ((u : G) * x * (u : G)⁻¹ * g) := by group
    _ = (u : G)⁻¹ * (g * x) := by rw [h2]
    _ = ((u : G)⁻¹ * g) * x := by group

omit [Finite G] in
theorem mem_sup_centralizer_of_outerHom_eq_one (U : Subgroup G) [U.Normal] {g : G}
    (h : outerHom U g = 1) : g ∈ U ⊔ centralizer (U : Set G) := by
  obtain ⟨u, hu, k, hk, rfl⟩ := exists_decomp U h
  exact mul_mem_sup hu hk

omit [Finite G] in
theorem outerHom_eq_one_of_mem (U : Subgroup G) [U.Normal] {x : G} (hx : x ∈ U) :
    outerHom U x = 1 :=
  (outerHom_eq_one_iff U x).2 ⟨⟨x, hx⟩, fun _ => rfl⟩

omit [Finite G] in
theorem outerHom_eq_one_of_mem_centralizer (U : Subgroup G) [U.Normal] {k : G}
    (hk : k ∈ centralizer (U : Set G)) : outerHom U k = 1 :=
  (outerHom_eq_one_iff U k).2 ⟨1, fun x => by
    have := mem_centralizer_iff.1 hk x x.2
    simp only [OneMemClass.coe_one, one_mul, inv_one, mul_one]
    rw [← this, mul_assoc, mul_inv_cancel, mul_one]⟩

omit [Finite G] in
theorem centralizer_normal (U : Subgroup G) [hU : U.Normal] :
    (centralizer (U : Set G)).Normal := by
  refine ⟨fun k hk g x hx => ?_⟩
  have hx' : g⁻¹ * x * g ∈ U := by
    have := hU.conj_mem x hx g⁻¹
    simpa using this
  have h := mem_centralizer_iff.1 hk _ hx'
  calc x * (g * k * g⁻¹) = g * ((g⁻¹ * x * g) * k) * g⁻¹ := by group
    _ = g * (k * (g⁻¹ * x * g)) * g⁻¹ := by rw [h]
    _ = (g * k * g⁻¹) * x := by group

omit [Finite G] in
theorem decomp_commutes (U : Subgroup G) [hU : U.Normal]
    (hZ : ∀ u : U, (∀ g : U, g * u = u * g) → u = 1) {g u k : G} (hu : u ∈ U)
    (hk : k ∈ centralizer (U : Set G)) (hg : g = u * k) (hzg : z * g = g * z) :
    z * k = k * z := by
  have hN := centralizer_normal U
  have hu' : z * u * z⁻¹ ∈ U := hU.conj_mem u hu z
  have hk' : z * k * z⁻¹ ∈ centralizer (U : Set G) := hN.conj_mem k hk z
  have h1 : u * k = (z * u * z⁻¹) * (z * k * z⁻¹) := by
    calc u * k = g := hg.symm
      _ = z * g * z⁻¹ := by rw [hzg]; group
      _ = (z * u * z⁻¹) * (z * k * z⁻¹) := by rw [hg]; group
  have hw : (z * u * z⁻¹)⁻¹ * u = (z * k * z⁻¹) * k⁻¹ := by
    calc (z * u * z⁻¹)⁻¹ * u = (z * u * z⁻¹)⁻¹ * (u * k) * k⁻¹ := by group
      _ = (z * u * z⁻¹)⁻¹ * ((z * u * z⁻¹) * (z * k * z⁻¹)) * k⁻¹ := by rw [h1]
      _ = (z * k * z⁻¹) * k⁻¹ := by group
  have hwK : (z * u * z⁻¹)⁻¹ * u ∈ centralizer (U : Set G) := by
    rw [hw]
    exact mul_mem hk' (inv_mem hk)
  have hwU : (z * u * z⁻¹)⁻¹ * u ∈ U := mul_mem (inv_mem hu') hu
  have hw1 : (⟨_, hwU⟩ : U) = 1 := hZ _ fun x => Subtype.ext (mem_centralizer_iff.1 hwK x x.2)
  have hw1' : (z * u * z⁻¹)⁻¹ * u = 1 := congrArg Subtype.val hw1
  have hu'u : z * u * z⁻¹ = u := inv_mul_eq_one.1 hw1'
  have hkk : z * k * z⁻¹ = k := by
    rw [hu'u] at h1
    exact (mul_left_cancel h1).symm
  exact mul_inv_eq_iff_eq_mul.1 hkk

theorem sp44_clause3
    (hG : Nat.card G ∣ gl8)
    (φ : ↥(centralizer ({z} : Set G)) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 6))
    (U : Subgroup G) [U.Normal] (hU : LieModel ↥U .PSp 2 2 2)
    (hzU : z ∉ U ⊔ centralizer (U : Set G)) :
    Nonempty (↥(U ⊓ centralizer ({z} : Set G)) ≃* Equiv.Perm (Fin 6)) := by
  have hE := eData_Sp44 hU
  have hZ : ∀ u : U, (∀ g : U, g * u = u * g) → u = 1 := fun u hu => hE.chief.center u hu
  have hc := CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hU
  have hUcard : Nat.card U = 979200 := card_of_statedClassicalModel_psp_two_two hc
  have hcyc : IsCyclic (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥U) :=
    isCyclic_outer_of_lieModel_sp44 hU
  set D := centralizer ({z} : Set G) with hD
  have hz1 : outerHom U z ≠ 1 := fun h => hzU (mem_sup_centralizer_of_outerHom_eq_one U h)
  obtain ⟨θ⟩ := nonempty_ker_equiv_perm_six (outerHom U) φ hz1
  set ψ := (outerHom U).comp D.subtype with hψ
  have hN : ∀ m : ψ.ker, ((m : D) : G) ∈ centralizer (U : Set G) → m = 1 := by
    intro m hm
    let ε : ψ.ker →* G := D.subtype.comp ψ.ker.subtype
    have hε : Function.Injective ε := D.subtype_injective.comp ψ.ker.subtype_injective
    let N : Subgroup ψ.ker := (centralizer (U : Set G)).comap ε
    have hNn : N.Normal := (centralizer_normal U).comap ε
    have hN' : (N.map θ.toMonoidHom).Normal := hNn.map _ θ.surjective
    rcases perm6_normal_bot_or_alt _ hN' with hbot | hA
    · have hmN : m ∈ N := hm
      have : θ m ∈ N.map θ.toMonoidHom := ⟨m, hmN, rfl⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact θ.injective (this.trans (map_one θ).symm)
    · exfalso
      have h360 : 360 ∣ Nat.card N := by
        have := Subgroup.card_dvd_of_le hA
        rwa [Subgroup.card_map_of_injective θ.injective, card_alternatingGroup_six] at this
      have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := N) 5
        (dvd_trans (by norm_num) h360)
      set κ : G := ε (y : ψ.ker) with hκ
      have hκord : orderOf κ = 5 := by
        rw [hκ, orderOf_injective ε hε, Subgroup.orderOf_coe, hy]
      have hκK : κ ∈ centralizer (U : Set G) := y.2
      have hcomm : ∀ (a : U) (b : zpowers κ),
          Commute (U.subtype a) ((zpowers κ).subtype b) := by
        intro a b
        obtain ⟨n, hn⟩ := b.2
        have hak : Commute (a : G) κ := (mem_centralizer_iff.1 hκK a a.2)
        have : Commute (a : G) (κ ^ n) := hak.zpow_right n
        simpa [← hn] using this
      let f : ↥U × ↥(zpowers κ) →* G :=
        MonoidHom.noncommCoprod U.subtype (zpowers κ).subtype hcomm
      have hf : Function.Injective f := by
        rw [injective_iff_map_eq_one]
        rintro ⟨a, b⟩ hab
        have hab' : (a : G) * (b : G) = 1 := by simpa [f] using hab
        have hbK : (b : G) ∈ centralizer (U : Set G) := Subgroup.zpowers_le.2 hκK b.2
        have haK : (a : G) ∈ centralizer (U : Set G) := by
          have : (a : G) = (b : G)⁻¹ := eq_inv_of_mul_eq_one_left hab'
          rw [this]
          exact inv_mem hbK
        have ha1 : a = 1 := hZ a fun g => Subtype.ext (mem_centralizer_iff.1 haK g g.2)
        have hb1 : (b : G) = 1 := by rw [ha1] at hab'; simpa using hab'
        exact Prod.ext ha1 (Subtype.ext hb1)
      have hdvd : Nat.card (↥U × ↥(zpowers κ)) ∣ Nat.card G :=
        Subgroup.card_dvd_of_injective f hf
      rw [Nat.card_prod, hUcard, Nat.card_zpowers, hκord] at hdvd
      have h2 := hdvd.trans hG
      revert h2
      unfold gl8
      norm_num
  have hkey : U ⊓ D = ψ.ker.map D.subtype := by
    ext g
    constructor
    · intro hg
      obtain ⟨hgU, hgD⟩ := mem_inf.1 hg
      exact ⟨⟨g, hgD⟩, outerHom_eq_one_of_mem U hgU, rfl⟩
    · rintro ⟨d, hd, rfl⟩
      refine mem_inf.2 ⟨?_, d.2⟩
      have hd1 : outerHom U (d : G) = 1 := hd
      obtain ⟨u, hu, k, hk, hdk⟩ := exists_decomp U hd1
      have hzd : z * (d : G) = (d : G) * z := (mem_centralizer_singleton_iff.1 d.2).symm
      have hzk : z * k = k * z := decomp_commutes U hZ hu hk hdk hzd
      have hkD : k ∈ D := mem_centralizer_singleton_iff.2 hzk.symm
      have hψk : ψ ⟨k, hkD⟩ = 1 := outerHom_eq_one_of_mem_centralizer U hk
      have h1 := hN ⟨⟨k, hkD⟩, hψk⟩ hk
      have hk1 : k = 1 := congrArg (fun m : ψ.ker => ((m : D) : G)) h1
      show (d : G) ∈ U
      rw [hdk, hk1, mul_one]
      exact hu
  exact ⟨(MulEquiv.subgroupCongr hkey).trans
    ((ψ.ker.equivMapOfInjective D.subtype D.subtype_injective).symm.trans θ)⟩

end CFSG.EvenSporadicStandard.M22Std
