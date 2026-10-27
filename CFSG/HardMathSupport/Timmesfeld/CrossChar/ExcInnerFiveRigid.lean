module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerF4Toral
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.Reduction
public import CFSG.LieType.SeitzGeneration.ExcParabolicReeF4Levi
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.Lattice.SteinbergBIQuotient
public import CFSG.RankThree.PartOne.KE.CTRational

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne.KE
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Lattice
open scoped Matrix

section Inner

variable {K : Type*} [Group K] [Finite K] {p : ℕ}

theorem le_fixSub_of_inner_component (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : K →* MulAut K))
    {H : Subgroup (MulAut K)} (hH : innerAut K ≤ H) {D₀ : Subgroup K} {g : MulAut K}
    (hg : g ∈ localDeltaIn p H (D₀.map (MulAut.conj : K →* MulAut K))) {d : K} (hd : d ∈ D₀)
    (hd1 : d ≠ 1) {L : Subgroup K} (hLC : L ≤ Subgroup.centralizer ({d} : Set K))
    (hLq : CFSG.IsQuasisimple L)
    (hLsn : (L.subgroupOf (Subgroup.centralizer ({d} : Set K))).IsSubnormal)
    (hLp : ¬ Nat.Coprime p (Nat.card L)) : L ≤ fixSub g := by
  set e : MulAut K := MulAut.conj d with hedef
  have he : e ∈ D₀.map (MulAut.conj : K →* MulAut K) := ⟨d, hd, rfl⟩
  have he1 : e ≠ 1 := fun h => hd1 (hinj (h.trans (map_one MulAut.conj).symm))
  set C : Subgroup (MulAut K) := H ⊓ Subgroup.centralizer ({e} : Set (MulAut K))
  have hcomm : ∀ x ∈ Subgroup.centralizer ({d} : Set K), MulAut.conj x * e = e * MulAut.conj x :=
    fun x hx => by
      have h1 : x * d = d * x := Subgroup.mem_centralizer_singleton_iff.1 hx
      rw [hedef, ← map_mul, ← map_mul, h1]
  have hXC : (Subgroup.centralizer ({d} : Set K)).map (MulAut.conj : K →* MulAut K) ≤ C := by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_inf.2 ⟨hH ⟨x, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 (hcomm x hx)⟩
  have hXn : (((Subgroup.centralizer ({d} : Set K)).map
      (MulAut.conj : K →* MulAut K)).subgroupOf C).IsSubnormal := by
    refine Subgroup.Normal.isSubnormal ⟨fun n hn y => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨x, hx, hxn⟩ := hn
    have hy := (Subgroup.mem_inf.1 y.2).2
    have hye : (y : MulAut K) * e = e * y := Subgroup.mem_centralizer_singleton_iff.1 hy
    refine ⟨(y : MulAut K) x, ?_, ?_⟩
    ·
      have hyd : (y : MulAut K) d = d := by
        apply hinj
        rw [← mul_conj_mul_inv, ← hedef, hye, mul_inv_cancel_right]
      have h1 : x * d = d * x := Subgroup.mem_centralizer_singleton_iff.1 hx
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      have h2 := congrArg (y : MulAut K) h1
      rwa [map_mul, map_mul, hyd] at h2
    · change MulAut.conj ((y : MulAut K) x) = (y : MulAut K) * (n : MulAut K) * (y : MulAut K)⁻¹
      rw [← mul_conj_mul_inv, ← hxn]
  have hTC : L.map (MulAut.conj : K →* MulAut K) ≤ C :=
    (Subgroup.map_mono hLC).trans hXC
  have hcompL : CFSG.IsComponent ((L.map (MulAut.conj : K →* MulAut K)).subgroupOf C) := by
    refine ⟨?_, isSubnormal_map_subgroupOf _ hLC hLsn hXC hXn⟩
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((L.equivMapOfInjective _ hinj).trans (Subgroup.subgroupOfEquivOfLe hTC).symm) hLq
  exact le_fixSub_of_component hp hinj hg he he1 hTC hcompL hLp

theorem mem_localDeltaIn_props (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : K →* MulAut K)) {H : Subgroup (MulAut K)}
    {D₀ : Subgroup K} (hD₀ : D₀ ≠ ⊥) {g : MulAut K}
    (hg : g ∈ localDeltaIn p H (D₀.map (MulAut.conj : K →* MulAut K))) :
    g ∈ H ∧ Nat.Coprime p (orderOf g) ∧ ∀ d ∈ D₀, g d = d := by
  obtain ⟨d, hd, hd1⟩ : ∃ d ∈ D₀, d ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hD₀ ((Subgroup.eq_bot_iff_forall D₀).2 hcon)
  have he : MulAut.conj d ∈ D₀.map (MulAut.conj : K →* MulAut K) := ⟨d, hd, rfl⟩
  have he1 : MulAut.conj d ≠ 1 := fun h => hd1 (hinj (h.trans (map_one MulAut.conj).symm))
  have : Finite (MulAut K) := Finite.of_injective (fun f : MulAut K => (f : K → K))
    fun f f' h => MulEquiv.ext (congrFun h)
  refine ⟨?_, coprime_orderOf_of_mem_localDeltaIn hp hg he he1, fun d' hd' => ?_⟩
  · have h1 := le_core_of_mem_localDeltaIn hg he he1
    exact (Subgroup.mem_inf.1 (Balance.gLAPPrimeCoreOf_le_self' _ h1)).1
  · have hc := commute_of_mem_localDeltaIn hg
      (⟨d', hd', rfl⟩ : MulAut.conj d' ∈ D₀.map (MulAut.conj : K →* MulAut K))
    exact mem_fixSub.1 (mem_fixSub_of_commute hinj hc)

end Inner

section Ambient

variable {G : Type*} [Group G] {A : Subgroup G} [Finite A] {p : ℕ}

theorem le_fixSub_of_inner_component_ambient (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : A →* MulAut A))
    {H : Subgroup (MulAut A)} (hH : innerAut A ≤ H) {D₀ : Subgroup A} {g : MulAut A}
    (hg : g ∈ localDeltaIn p H (D₀.map (MulAut.conj : A →* MulAut A))) {d : A} (hd : d ∈ D₀)
    (hd1 : d ≠ 1) {L : Subgroup G} (hLC : L ≤ A ⊓ Subgroup.centralizer {(d : G)})
    (hLq : CFSG.IsQuasisimple L)
    (hLsn : (L.subgroupOf (A ⊓ Subgroup.centralizer {(d : G)})).IsSubnormal)
    (hLp : ¬ Nat.Coprime p (Nat.card L)) {x : A} (hx : (x : G) ∈ L) : g x = x := by
  have hLA : L ≤ A := hLC.trans inf_le_left
  refine le_fixSub_of_inner_component hp hinj hH hg hd hd1 (L := L.subgroupOf A)
    (fun y hy => ?_) ?_ (isSubnormal_subgroupOf_centralizer d hLsn) ?_ hx
  · exact Subgroup.mem_centralizer_singleton_iff.2
      (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (hLC hy).2))
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLA).symm hLq
  · rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLA).toEquiv]

theorem localDeltaIn_eq_bot_of_inner_components_rigid_ambient (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : A →* MulAut A))
    {H : Subgroup (MulAut A)} (hH : innerAut A ≤ H) {D₀ : Subgroup A} (hD₀ : D₀ ≠ ⊥) {S : Set G}
    (hrig : ∀ δ ∈ H, Nat.Coprime p (orderOf δ) → (∀ d ∈ D₀, δ d = d) →
      (∀ x : A, (x : G) ∈ S → δ x = x) → δ = 1)
    (hcomp : ∀ x : A, (x : G) ∈ S → ∃ d ∈ D₀, d ≠ 1 ∧ ∃ L : Subgroup G, (x : G) ∈ L ∧
      L ≤ A ⊓ Subgroup.centralizer {(d : G)} ∧ CFSG.IsQuasisimple L ∧
      (L.subgroupOf (A ⊓ Subgroup.centralizer {(d : G)})).IsSubnormal ∧
      ¬ Nat.Coprime p (Nat.card L)) :
    localDeltaIn p H (D₀.map (MulAut.conj : A →* MulAut A)) = ⊥ := by
  refine eq_bot_iff.2 fun g hg => ?_
  obtain ⟨hgH, hcop, hfix⟩ := mem_localDeltaIn_props hp hinj hD₀ hg
  refine Subgroup.mem_bot.2 (hrig g hgH hcop hfix fun x hx => ?_)
  obtain ⟨d, hd, hd1, L, hxL, hLC, hLq, hLsn, hLp⟩ := hcomp x hx
  exact le_fixSub_of_inner_component_ambient hp hinj hH hg hd hd1 hLC hLq hLsn hLp hxL

end Ambient

@[expose] def FrameBalanced (p : ℕ) {M : Type*} [Group M] (Γ E : Subgroup M) : Prop :=
  ∀ D₁ : Subgroup ↥Γ, (∀ x ∈ D₁, (x : M) ∈ E) → (∀ x ∈ D₁, x ^ p = 1) → p < Nat.card D₁ →
    ∀ H : Subgroup (MulAut ↥Γ), innerAut ↥Γ ≤ H →
      localDeltaIn p H (D₁.map (MulAut.conj : ↥Γ →* MulAut ↥Γ)) = ⊥

theorem localDeltaIn_eq_bot_of_frameBalanced_mulEquiv {C M : Type*} [Group C] [Group M] {p : ℕ}
    {Γ E : Subgroup M} (hbal : FrameBalanced p Γ E) (φ : C ≃* ↥Γ) (D₀ : Subgroup C)
    (hpow : ∀ x ∈ D₀, x ^ p = 1) (hcard : p < Nat.card D₀)
    (hE : ∀ x ∈ D₀, ((φ x : ↥Γ) : M) ∈ E) {H : Subgroup (MulAut C)} (hH : innerAut C ≤ H) :
    localDeltaIn p H (D₀.map (MulAut.conj : C →* MulAut C)) = ⊥ := by
  set ψ : MulAut C →* MulAut ↥Γ := (MulAut.congr φ).toMonoidHom with hψ
  have hψinj : Function.Injective ψ := (MulAut.congr φ).injective
  have hψconj : ∀ g : C, ψ (MulAut.conj g) = MulAut.conj (φ g) := fun g => by
    ext z
    simp [hψ, MulAut.congr_apply, MulAut.conj_apply]
  have hinn : innerAut ↥Γ ≤ H.map ψ := by
    rintro _ ⟨y, rfl⟩
    refine ⟨MulAut.conj (φ.symm y), hH ⟨φ.symm y, rfl⟩, ?_⟩
    rw [hψconj]
    simp
  have hmap : (D₀.map (MulAut.conj : C →* MulAut C)).map ψ =
      (D₀.map φ.toMonoidHom).map (MulAut.conj : ↥Γ →* MulAut ↥Γ) := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext g z
    simp [hψ, MulAut.congr_apply, MulAut.conj_apply]
  have key := hbal (D₀.map φ.toMonoidHom)
    (by
      rintro _ ⟨x, hx, rfl⟩
      exact hE x hx)
    (by
      rintro _ ⟨x, hx, rfl⟩
      change φ x ^ p = 1
      rw [← map_pow, hpow x hx, map_one])
    (by rwa [Subgroup.card_map_of_injective φ.injective]) (H.map ψ) hinn
  have hle := map_localDeltaIn_le p ψ hψinj H (D₀.map (MulAut.conj : C →* MulAut C))
  rw [hmap, key, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ hψinj] at hle
  exact hle

variable {τ : Tag} {L : Type} [Field L]

end CFSG.HardMathSupport.Timmesfeld.CrossChar
