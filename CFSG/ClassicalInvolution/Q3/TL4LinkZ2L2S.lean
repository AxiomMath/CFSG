module

public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2L2DefsB
public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2L2A
public import CFSG.ClassicalInvolution.Q3.TL4ExitDichL2

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.Blueprint

namespace LinkZ2S

@[expose] def Concl163Q8 (A : Type) [Group A] : Prop :=
  ∀ (P : Subgroup A) (e : ↥P ≃* QuaternionGroup 2) (β : MulAut A), β * β = 1 →
    (∀ x ∈ P, β x = x) → β = 1 ∨ β = MulAut.conj ((e.symm (QuaternionGroup.a 2) : ↥P) : A)

theorem concl163_congr {A B : Type} [Group A] [Group B] (f : A ≃* B) (hB : Concl163Q8 B) :
    Concl163Q8 A := by
  intro P e β hβ hP
  have hc : ∀ m : A, MulAut.congr f (MulAut.conj m) = MulAut.conj (f m) := fun m => by
    ext x
    change f (m * f.symm x * m⁻¹) = f m * x * (f m)⁻¹
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  let fP : ↥P ≃* ↥(P.map f.toMonoidHom) := P.equivMapOfInjective f.toMonoidHom f.injective
  have hβ' : MulAut.congr f β * MulAut.congr f β = 1 := by rw [← map_mul, hβ, map_one]
  have hfix : ∀ x ∈ P.map f.toMonoidHom, MulAut.congr f β x = x := by
    rintro _ ⟨y, hy, rfl⟩
    change f (β (f.symm (f y))) = f y
    rw [MulEquiv.symm_apply_apply, hP y hy]
  rcases hB _ (fP.symm.trans e) _ hβ' hfix with h | h
  · left
    apply (MulAut.congr f).injective
    rw [h, map_one]
  · right
    apply (MulAut.congr f).injective
    rw [h, hc]
    rfl

theorem mul_inv_mem_oddCoreOf {G : Type} [Group G] {Λ : Subgroup G} {a b : G} (ha : a ∈ Λ)
    (hb : b ∈ Λ) (h : (QuotientGroup.mk ⟨a, ha⟩ : ↥Λ ⧸ classicalInvolutionOddCore ↥Λ) =
      QuotientGroup.mk ⟨b, hb⟩) : a * b⁻¹ ∈ oddCoreOf Λ := by
  rw [QuotientGroup.eq] at h
  have h1 := Subgroup.inv_mem _ h
  rw [mul_inv_rev, inv_inv] at h1
  have h2 := Subgroup.Normal.conj_mem inferInstance _ h1 ⟨b, hb⟩
  rw [show (⟨b, hb⟩ : ↥Λ) * ((⟨b, hb⟩ : ↥Λ)⁻¹ * ⟨a, ha⟩) * (⟨b, hb⟩ : ↥Λ)⁻¹ =
    ⟨a, ha⟩ * (⟨b, hb⟩ : ↥Λ)⁻¹ by group] at h2
  exact ⟨_, h2, rfl⟩

theorem triv_or_triv_mul {G : Type} [Group G] [Finite G] {Λ Q : Subgroup G} {w d : G}
    (hw2 : w * w = 1) (hwΛ : ∀ y ∈ Λ, w * y * w⁻¹ ∈ Λ) (hQΛ : Q ≤ Λ) (hQ2 : IsPGroup 2 Q)
    (e : ↥Q ≃* QuaternionGroup 2) (hd : ((e.symm (QuaternionGroup.a 2) : ↥Q) : G) = d)
    (hwQ : ∀ x ∈ Q, w * x = x * w)
    (h163 : Concl163Q8 (↥Λ ⧸ classicalInvolutionOddCore ↥Λ)) :
    (∀ y ∈ Λ, w * y * w⁻¹ * y⁻¹ ∈ oddCoreOf Λ) ∨
      (∀ y ∈ Λ, w * d * y * (w * d)⁻¹ * y⁻¹ ∈ oddCoreOf Λ) := by
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_left hw2
  let γ : MulAut ↥Λ :=
    { toFun := fun y => ⟨w * y * w⁻¹, hwΛ y y.2⟩
      invFun := fun y => ⟨w * y * w⁻¹, hwΛ y y.2⟩
      left_inv := fun y => Subtype.ext (by
        show w * (w * (y : G) * w⁻¹) * w⁻¹ = y
        rw [hwinv]
        calc w * (w * (y : G) * w) * w = w * w * y * (w * w) := by group
          _ = y := by rw [hw2, one_mul, mul_one])
      right_inv := fun y => Subtype.ext (by
        show w * (w * (y : G) * w⁻¹) * w⁻¹ = y
        rw [hwinv]
        calc w * (w * (y : G) * w) * w = w * w * y * (w * w) := by group
          _ = y := by rw [hw2, one_mul, mul_one])
      map_mul' := fun x y => Subtype.ext (by
        show w * ((x : G) * y) * w⁻¹ = w * x * w⁻¹ * (w * y * w⁻¹)
        group) }
  have hγ : ∀ y : ↥Λ, ((γ y : ↥Λ) : G) = w * y * w⁻¹ := fun _ => rfl
  have hO : (classicalInvolutionOddCore ↥Λ).map γ.toMonoidHom = classicalInvolutionOddCore ↥Λ :=
    CFSG.ComponentClassification.OddCore.char_invariant γ
  set O := classicalInvolutionOddCore ↥Λ with hOdef
  let β : MulAut (↥Λ ⧸ O) := QuotientGroup.congr O O γ hO
  have hβ : ∀ y : ↥Λ, β (QuotientGroup.mk y) = QuotientGroup.mk (γ y) := fun _ => rfl
  have hβ2 : β * β = 1 := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    rw [MulAut.mul_apply, hβ, hβ, MulAut.one_apply]
    congr 1
    exact γ.left_inv y
  let ι : ↥(Q.subgroupOf Λ) →* ↥Λ ⧸ O := (QuotientGroup.mk' O).comp (Q.subgroupOf Λ).subtype
  have hι : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxO : (x : ↥Λ) ∈ O := (QuotientGroup.eq_one_iff _).mp hx
    have hodd : Odd (orderOf (x : ↥Λ)) := by
      have h1 := orderOf_dvd_natCard (⟨_, hxO⟩ : ↥O)
      rw [Subgroup.orderOf_mk] at h1
      exact (CFSG.ComponentClassification.OddCore.odd_card ↥Λ).of_dvd_nat h1
    have hx2 : ∃ k : ℕ, orderOf (x : ↥Λ) = 2 ^ k := by
      obtain ⟨k, hk⟩ := hQ2 ⟨((x : ↥Λ) : G), Subgroup.mem_subgroupOf.mp x.2⟩
      have h1 : orderOf (⟨((x : ↥Λ) : G), Subgroup.mem_subgroupOf.mp x.2⟩ : ↥Q) ∣ 2 ^ k :=
        orderOf_dvd_of_pow_eq_one hk
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe] at h1
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
      exact ⟨j, hj⟩
    obtain ⟨k, hk⟩ := hx2
    have hk0 : k = 0 := by
      by_contra h
      rw [hk] at hodd
      exact Nat.not_even_iff_odd.2 hodd (Nat.even_pow.2 ⟨even_two, h⟩)
    rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
    exact Subtype.ext hk
  let eP : ↥ι.range ≃* QuaternionGroup 2 :=
    (MonoidHom.ofInjective hι).symm.trans ((Subgroup.subgroupOfEquivOfLe hQΛ).trans e)
  have hfix : ∀ x ∈ ι.range, β x = x := by
    rintro _ ⟨q, rfl⟩
    change β (QuotientGroup.mk (q : ↥Λ)) = QuotientGroup.mk (q : ↥Λ)
    rw [hβ]
    congr 1
    apply Subtype.ext
    rw [hγ]
    have hq : ((q : ↥Λ) : G) ∈ Q := Subgroup.mem_subgroupOf.mp q.2
    rw [hwQ _ hq, mul_inv_cancel_right]
  have hdΛ : d ∈ Λ := hd ▸ hQΛ (e.symm (QuaternionGroup.a 2)).2
  have hzP : ((eP.symm (QuaternionGroup.a 2) : ↥ι.range) : ↥Λ ⧸ O) =
      QuotientGroup.mk (⟨d, hdΛ⟩ : ↥Λ) := by
    change ι ((Subgroup.subgroupOfEquivOfLe hQΛ).symm (e.symm (QuaternionGroup.a 2))) = _
    change QuotientGroup.mk _ = _
    congr 1
    exact Subtype.ext hd
  have hd2 : d * d = 1 := by
    rw [← hd, ← Subgroup.coe_mul, ← map_mul, show QuaternionGroup.a 2 * QuaternionGroup.a 2 =
      (1 : QuaternionGroup 2) by decide, map_one, Subgroup.coe_one]
  rcases h163 _ eP β hβ2 hfix with h | h
  · left
    intro y hy
    have h1 : β (QuotientGroup.mk ⟨y, hy⟩) = QuotientGroup.mk ⟨y, hy⟩ := by rw [h]; rfl
    rw [hβ] at h1
    have e1 : γ ⟨y, hy⟩ = ⟨w * y * w⁻¹, hwΛ y hy⟩ := rfl
    rw [e1] at h1
    exact mul_inv_mem_oddCoreOf (hwΛ y hy) hy h1
  · right
    intro y hy
    have hdy : d * y * d⁻¹ ∈ Λ := Λ.mul_mem (Λ.mul_mem hdΛ hy) (Λ.inv_mem hdΛ)
    have h1 : β (QuotientGroup.mk ⟨d * y * d⁻¹, hdy⟩) =
        QuotientGroup.mk (⟨d, hdΛ⟩ : ↥Λ) * QuotientGroup.mk ⟨d * y * d⁻¹, hdy⟩ *
          (QuotientGroup.mk (⟨d, hdΛ⟩ : ↥Λ))⁻¹ := by
      rw [h, MulAut.conj_apply, hzP]
    rw [hβ, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul] at h1
    have hwdΛ : w * d * y * (w * d)⁻¹ ∈ Λ := by
      have := hwΛ _ hdy
      rwa [show w * (d * y * d⁻¹) * w⁻¹ = w * d * y * (w * d)⁻¹ by group] at this
    have e1 : γ ⟨d * y * d⁻¹, hdy⟩ = ⟨w * d * y * (w * d)⁻¹, hwdΛ⟩ :=
      Subtype.ext (by rw [hγ]; group)
    have e2 : (⟨d, hdΛ⟩ : ↥Λ) * ⟨d * y * d⁻¹, hdy⟩ * (⟨d, hdΛ⟩ : ↥Λ)⁻¹ = ⟨y, hy⟩ :=
      Subtype.ext (by
        show d * (d * y * d⁻¹) * d⁻¹ = y
        calc d * (d * y * d⁻¹) * d⁻¹ = (d * d) * y * (d * d)⁻¹ := by group
          _ = y := by rw [hd2]; group)
    rw [e1, e2] at h1
    exact mul_inv_mem_oddCoreOf hwdΛ hy h1

theorem e_symm_a_two_eq {G : Type} [Group G] {L P : Subgroup G} {z : G}
    (hz : IsUniqueInvolution L z) (hPL : P ≤ L) (e : ↥P ≃* QuaternionGroup 2) :
    ((e.symm (QuaternionGroup.a 2) : ↥P) : G) = z := by
  have hsq : ((e.symm (QuaternionGroup.a 2) : ↥P) : G) *
      (e.symm (QuaternionGroup.a 2) : G) = 1 := by
    rw [← Subgroup.coe_mul, ← map_mul, show QuaternionGroup.a 2 * QuaternionGroup.a 2 =
      (1 : QuaternionGroup 2) by decide, map_one, Subgroup.coe_one]
  rcases hz.unique _ (hPL (e.symm _).2) hsq with h | h
  · exfalso
    have h1 : e.symm (QuaternionGroup.a 2) = 1 := Subtype.ext h
    rw [map_eq_one_iff _ e.symm.injective] at h1
    exact absurd h1 (by decide)
  · exact h

theorem le_coreAt_of_isPGroup {G : Type} [Group G] {L Q : Subgroup G} {c : G} (hQL : Q ≤ L)
    (hQc : Q ≤ Subgroup.centralizer ({c} : Set G)) (hQ2 : IsPGroup 2 Q) : Q ≤ coreAt c L :=
  fun _ hx => Subgroup.subset_closure ⟨⟨hQL hx, hQc hx⟩, hQ2.to_le (Subgroup.zpowers_le.mpr hx)⟩

theorem mem_centralizer_mul {G : Type} [Group G] {x a b : G}
    (ha : x ∈ Subgroup.centralizer ({a} : Set G)) (hb : x ∈ Subgroup.centralizer ({b} : Set G)) :
    x ∈ Subgroup.centralizer ({a * b} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at ha hb ⊢
  calc x * (a * b) = x * a * b := by group
    _ = a * x * b := by rw [ha]
    _ = a * (x * b) := by group
    _ = a * (b * x) := by rw [hb]
    _ = a * b * x := by group

theorem caseA1_mul {G : Type} [Group G] {t u w c : G} {R₀ T₀ : Subgroup G} (hw2 : w * w = 1)
    (hwt : w * t = t * w) (hwu : w * u = u * w) (hwE : w ∉ Subgroup.closure ({t, u} : Set G))
    (hR₀w : R₀ ≤ Subgroup.centralizer ({w} : Set G))
    (hT₀w : T₀ ≤ Subgroup.centralizer ({w} : Set G)) (hc2 : c * c = 1) (hct : c * t = t * c)
    (hcu : c * u = u * c) (hcw : c * w = w * c) (hcE : c ∈ Subgroup.closure ({t, u} : Set G))
    (hR₀c : R₀ ≤ Subgroup.centralizer ({c} : Set G))
    (hT₀c : T₀ ≤ Subgroup.centralizer ({c} : Set G)) :
    w * c * (w * c) = 1 ∧ w * c * t = t * (w * c) ∧ w * c * u = u * (w * c) ∧
      w * c ∉ Subgroup.closure ({t, u} : Set G) ∧
      R₀ ≤ Subgroup.centralizer ({w * c} : Set G) ∧
      T₀ ≤ Subgroup.centralizer ({w * c} : Set G) := by
  refine ⟨?_, ?_, ?_, ?_, fun x hx => mem_centralizer_mul (hR₀w hx) (hR₀c hx),
    fun x hx => mem_centralizer_mul (hT₀w hx) (hT₀c hx)⟩
  · calc w * c * (w * c) = w * (c * w) * c := by group
      _ = w * (w * c) * c := by rw [hcw]
      _ = w * w * (c * c) := by group
      _ = 1 := by rw [hw2, hc2, one_mul]
  · calc w * c * t = w * (c * t) := by group
      _ = w * t * c := by rw [hct]; group
      _ = t * (w * c) := by rw [hwt]; group
  · calc w * c * u = w * (c * u) := by group
      _ = w * u * c := by rw [hcu]; group
      _ = u * (w * c) := by rw [hwu]; group
  · intro h
    apply hwE
    have e : w = w * c * c⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ h (Subgroup.inv_mem _ hcE)

theorem triv_mul_of_comm {G : Type} [Group G] {Λ : Subgroup G} {x c : G}
    (hc : ∀ y ∈ Λ, c * y = y * c) (h : ∀ y ∈ Λ, x * y * x⁻¹ * y⁻¹ ∈ oddCoreOf Λ) :
    ∀ y ∈ Λ, x * c * y * (x * c)⁻¹ * y⁻¹ ∈ oddCoreOf Λ := by
  intro y hy
  have e : x * c * y * (x * c)⁻¹ = x * y * x⁻¹ := by
    calc x * c * y * (x * c)⁻¹ = x * (c * y) * c⁻¹ * x⁻¹ := by group
      _ = x * (y * c) * c⁻¹ * x⁻¹ := by rw [hc y hy]
      _ = x * y * x⁻¹ := by group
  rw [e]
  exact h y hy

section Cit3


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem concl163_linkLayer (hL : TightLargeHypR 3 n Y R S t)
    (hsimp : IsSimpleGroup ↥(genFittingFStar ↥(linkGrp R t)))
    (hidx : (genFittingFStar ↥(linkGrp R t)).index ≤ 2) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : Even f) (h9 : p ^ f ≠ 9) (hk : LieModel (FStarQuot ↥(linkGrp R t)) .PSL 2 p f) :
    Concl163Q8 (↥(linkLayer R t) ⧸ classicalInvolutionOddCore ↥(linkLayer R t)) :=
  concl163_congr (linkLayerEquiv hL) fun P e β hβ hP =>
    model163L2Q8_proved _ hsimp hidx p f hp hp2 hf h9 hk P e β hβ hP

theorem triv_at_t (hL : TightLargeHypR 3 n Y R S t)
    (h163 : Concl163Q8 (↥(linkLayer R t) ⧸ classicalInvolutionOddCore ↥(linkLayer R t)))
    {J : Subgroup Y} (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    {u : Y} (hu : IsUniqueInvolution J u) {T₀ : Subgroup Y} (hT₀ : IsSylow2In T₀ J)
    (hT₀N : T₀ ≤ Subgroup.normalizer ((tightCore R : Subgroup Y) : Set Y)) {w : Y}
    (hw2 : w * w = 1) (hwt : w * t = t * w) (hT₀w : T₀ ≤ Subgroup.centralizer ({w} : Set Y)) :
    (∀ y ∈ linkLayer R t, w * y * w⁻¹ * y⁻¹ ∈ oddCoreOf (linkLayer R t)) ∨
      (∀ y ∈ linkLayer R t, w * u * y * (w * u)⁻¹ * y⁻¹ ∈ oddCoreOf (linkLayer R t)) := by
  have ht := hL.datum.isUniqueInvolution_core
  have hT₀t : T₀ ≤ Subgroup.centralizer ({t} : Set Y) := fun x hx =>
    S1916.normalizer_le_centralizer_of_isUniqueInvolution ht (hT₀N hx)
  obtain ⟨e⟩ := (TightLargeHypR.typeRFam hL).quat J hJ.1 T₀ hT₀
  exact triv_or_triv_mul hw2
    (fun y hy => conj_mem_linkLayer hL (Subgroup.mem_centralizer_singleton_iff.mpr hwt) hy)
    ((le_coreAt_of_isPGroup hT₀.1 hT₀t hT₀.2.1).trans (coreAt_le_linkLayerAt hJ)) hT₀.2.1 e
    (e_symm_a_two_eq hu hT₀.1 e)
    (fun x hx => (Subgroup.mem_centralizer_singleton_iff.mp (hT₀w hx)).symm) h163

theorem triv_at_u (hL : TightLargeHypR 3 n Y R S t)
    (h163 : Concl163Q8 (↥(linkLayer R t) ⧸ classicalInvolutionOddCore ↥(linkLayer R t)))
    {J : Subgroup Y} (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    {u : Y} (hu : IsUniqueInvolution J u) {R₀ : Subgroup Y} (hR₀ : IsSylow2In R₀ (tightCore R))
    (hR₀u : R₀ ≤ Subgroup.centralizer ({u} : Set Y)) {w : Y} (hw2 : w * w = 1)
    (hwu : w * u = u * w) (hR₀w : R₀ ≤ Subgroup.centralizer ({w} : Set Y)) :
    (∀ y ∈ linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u, w * y * w⁻¹ * y⁻¹ ∈
      oddCoreOf (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u)) ∨
    (∀ y ∈ linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u, w * t * y * (w * t)⁻¹ * y⁻¹ ∈
      oddCoreOf (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u)) := by
  have hΩ := hL.datum.hypOmegaGen
  have hcl : ConjInvariant (CoreAssembly.conjClass (tightCore R)) := hΩ.conjInvariant
  have ht := hL.datum.isUniqueInvolution_core
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) := ⟨1, conjSub_one _⟩
  obtain ⟨g, hg⟩ := hJ.1
  have hg' : conjSub g (tightCore R) = J := hg
  have hug : u = g * t * g⁻¹ := by
    have h1 := ht.conj g
    rw [hg'] at h1
    exact hu.eq h1
  have hKJ := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hK hJ.1 hJ
  have hM : conjSub g⁻¹ (tightCore R) ∈
      omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) := by
    have h1 := omegaNbr_conj hcl hKJ g⁻¹
    rwa [← hg', conjSub_inv_conjSub] at h1
  have hQt : conjSub g⁻¹ R₀ ≤ Subgroup.centralizer ({t} : Set Y) := by
    intro x hx
    rw [mem_conjSub_iff, inv_inv] at hx
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hR₀u hx)
    rw [hug] at h1
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 : g * (x * t) * g⁻¹ = g * (t * x) * g⁻¹ := by
      calc g * (x * t) * g⁻¹ = g * x * g⁻¹ * (g * t * g⁻¹) := by group
        _ = g * t * g⁻¹ * (g * x * g⁻¹) := h1
        _ = g * (t * x) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  have hQ2 : IsPGroup 2 ↥(conjSub g⁻¹ R₀) := hR₀.2.1.map _
  have hQΛ : conjSub g⁻¹ R₀ ≤ linkLayer R t :=
    (le_coreAt_of_isPGroup (conjSub_mono hR₀.1) hQt hQ2).trans (coreAt_le_linkLayerAt hM)
  obtain ⟨eR⟩ := (TightLargeHypR.typeRFam hL).quat (tightCore R) hK R₀ hR₀
  let cQ : ↥R₀ ≃* ↥(conjSub g⁻¹ R₀) :=
    R₀.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective
  have hdQ : (((cQ.symm.trans eR).symm (QuaternionGroup.a 2) : ↥(conjSub g⁻¹ R₀)) : Y) =
      g⁻¹ * t * g := by
    change g⁻¹ * ((eR.symm (QuaternionGroup.a 2) : ↥R₀) : Y) * g⁻¹⁻¹ = _
    rw [e_symm_a_two_eq ht hR₀.1 eR, inv_inv]
  have hw₁2 : g⁻¹ * w * g * (g⁻¹ * w * g) = 1 := by
    calc g⁻¹ * w * g * (g⁻¹ * w * g) = g⁻¹ * (w * w) * g := by group
      _ = 1 := by rw [hw2]; group
  have hw₁t : g⁻¹ * w * g * t = t * (g⁻¹ * w * g) := by
    rw [hug] at hwu
    calc g⁻¹ * w * g * t = g⁻¹ * (w * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * w) * g := by rw [hwu]
      _ = t * (g⁻¹ * w * g) := by group
  have hw₁Q : ∀ x ∈ conjSub g⁻¹ R₀, g⁻¹ * w * g * x = x * (g⁻¹ * w * g) := by
    intro x hx
    rw [mem_conjSub_iff, inv_inv] at hx
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hR₀w hx)
    calc g⁻¹ * w * g * x = g⁻¹ * (w * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * w) * g := by rw [h1]
      _ = x * (g⁻¹ * w * g) := by group
  have hV := triv_or_triv_mul hw₁2
    (fun y hy => conj_mem_linkLayer hL (Subgroup.mem_centralizer_singleton_iff.mpr hw₁t) hy)
    hQΛ hQ2 (cQ.symm.trans eR) hdQ hw₁Q h163
  have hΛ : linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u = conjSub g (linkLayer R t) := by
    show _ = conjSub g (linkLayerAt (CoreAssembly.conjClass (tightCore R)) (tightCore R) t)
    rw [conjSub_linkLayerAt hcl g, hg', ← hug]
  have hO : oddCoreOf (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) =
      conjSub g (oddCoreOf (linkLayer R t)) := by
    rw [hΛ, Thompson.oddCoreOf_conjSub_eq]
  rcases hV with h | h
  · left
    intro y hy
    rw [hΛ, mem_conjSub_iff] at hy
    rw [hO, mem_conjSub_iff]
    have h1 := h _ hy
    have e : g⁻¹ * (w * y * w⁻¹ * y⁻¹) * g = g⁻¹ * w * g * (g⁻¹ * y * g) *
        (g⁻¹ * w * g)⁻¹ * (g⁻¹ * y * g)⁻¹ := by group
    rw [e]
    exact h1
  · right
    intro y hy
    rw [hΛ, mem_conjSub_iff] at hy
    rw [hO, mem_conjSub_iff]
    have h1 := h _ hy
    have e : g⁻¹ * (w * t * y * (w * t)⁻¹ * y⁻¹) * g = g⁻¹ * w * g * (g⁻¹ * t * g) *
        (g⁻¹ * y * g) * (g⁻¹ * w * g * (g⁻¹ * t * g))⁻¹ * (g⁻¹ * y * g)⁻¹ := by group
    rw [e]
    exact h1

theorem exists_adapted (hL : TightLargeHypR 3 n Y R S t) {J : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) {u : Y}
    (hu : IsUniqueInvolution J u) :
    ∃ R₀ T₀ : Subgroup Y, IsSylow2In R₀ (tightCore R) ∧
      R₀ ≤ Subgroup.centralizer ({u} : Set Y) ∧ IsSylow2In T₀ J ∧
      T₀ ≤ Subgroup.normalizer ((tightCore R : Subgroup Y) : Set Y) := by
  have hΩ := hL.datum.hypOmegaGen
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) := ⟨1, conjSub_one _⟩
  obtain ⟨hJΩ, -, T, hT, hTJ, hTN⟩ := id hJ
  obtain ⟨-, -, T', hT', hT'K, hT'N⟩ := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hK hJ.1 hJ
  exact ⟨T', T, Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hK hT' hT'K,
    fun x hx => S1916.normalizer_le_centralizer_of_isUniqueInvolution hu (hT'N hx),
    Q3CL.Sec7.isSylow2In_of_mem_RSet_of_le hΩ hT hJΩ hTJ, hTN⟩

end Cit3

section Frame


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem false_of_caseA1 (h4 : Thm4RBelow 3 n) (h5 : Thm5RBelowF 3 n)
    (htw : PhilipHall.Frame.Thm1RTwinLiftSetEBelow n) (hE4 : E4AutOddFreeR)
    (hOm : OmegaAutOddFreeR) (hL : TightLargeHypR 3 n Y R S t)
    (hc : DConnected (CoreAssembly.conjClass (tightCore R))) (hα : LinkAlphaBad R t)
    (htr : LinkTrans R t)
    (h163 : Concl163Q8 (↥(linkLayer R t) ⧸ classicalInvolutionOddCore ↥(linkLayer R t)))
    {J : Subgroup Y} (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    {u : Y} (hu : IsUniqueInvolution J u) {R₀ : Subgroup Y} (hR₀ : IsSylow2In R₀ (tightCore R))
    (hR₀u : R₀ ≤ Subgroup.centralizer ({u} : Set Y)) {T₀ : Subgroup Y} (hT₀ : IsSylow2In T₀ J)
    (hT₀N : T₀ ≤ Subgroup.normalizer ((tightCore R : Subgroup Y) : Set Y)) {w : Y}
    (hw2 : w * w = 1) (hwt : w * t = t * w) (hwu : w * u = u * w)
    (hwE : w ∉ Subgroup.closure ({t, u} : Set Y))
    (hR₀w : R₀ ≤ Subgroup.centralizer ({w} : Set Y))
    (hT₀w : T₀ ≤ Subgroup.centralizer ({w} : Set Y)) : False := by
  have hΩ := hL.datum.hypOmegaGen
  have ht := hL.datum.isUniqueInvolution_core
  have ctu : t * u = u * t := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ ht hJ hu
  have hR₀t : R₀ ≤ Subgroup.centralizer ({t} : Set Y) :=
    hR₀.1.trans ((tightCore_le R).trans hL.datum.cent)
  have hT₀t : T₀ ≤ Subgroup.centralizer ({t} : Set Y) := fun x hx =>
    S1916.normalizer_le_centralizer_of_isUniqueInvolution ht (hT₀N hx)
  have hT₀u : T₀ ≤ Subgroup.centralizer ({u} : Set Y) := fun x hx =>
    S1916.normalizer_le_centralizer_of_isUniqueInvolution hu (Subgroup.le_normalizer (hT₀.1 hx))
  have hΛt : ∀ y ∈ linkLayer R t, t * y = y * t := fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff.mp (linkLayerAt_le_centralizer hy)).symm
  have hΛu : ∀ y ∈ linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u, u * y = y * u :=
    fun y hy => (Subgroup.mem_centralizer_singleton_iff.mp (linkLayerAt_le_centralizer hy)).symm
  have htE : t ∈ Subgroup.closure ({t, u} : Set Y) := Subgroup.subset_closure (by simp)
  have huE : u ∈ Subgroup.closure ({t, u} : Set Y) := Subgroup.subset_closure (by simp)
  have hut2 : u * t * (u * t) = 1 := by
    calc u * t * (u * t) = u * (t * u) * t := by group
      _ = u * (u * t) * t := by rw [ctu]
      _ = u * u * (t * t) := by group
      _ = 1 := by rw [hu.sq, ht.sq, one_mul]
  have frame : ∀ w' : Y, w' * w' = 1 → w' * t = t * w' → w' * u = u * w' →
      w' ∉ Subgroup.closure ({t, u} : Set Y) → R₀ ≤ Subgroup.centralizer ({w'} : Set Y) →
      T₀ ≤ Subgroup.centralizer ({w'} : Set Y) →
      (∀ y ∈ linkLayer R t, w' * y * w'⁻¹ * y⁻¹ ∈ oddCoreOf (linkLayer R t)) →
      (∀ y ∈ linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u, w' * y * w'⁻¹ * y⁻¹ ∈
        oddCoreOf (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u)) → False :=
    fun w' h1 h2 h3 h4' h5' h6 h7 h8 =>
      LinkZ2A.false_of_frameA1 h4 h5 htw hE4 hOm hL hc hα htr hJ hu h1 h2 h3 h4' hR₀ hR₀u h5'
        hT₀ hT₀N h6 h7 h8
  have vt := triv_at_t hL h163 hJ hu hT₀ hT₀N hw2 hwt hT₀w
  have vu := triv_at_u hL h163 hJ hu hR₀ hR₀u hw2 hwu hR₀w
  rcases vt with ht' | ht' <;> rcases vu with hu' | hu'
  · exact frame w hw2 hwt hwu hwE hR₀w hT₀w ht' hu'
  · obtain ⟨a1, a2, a3, a4, a5, a6⟩ := caseA1_mul hw2 hwt hwu hwE hR₀w hT₀w ht.sq rfl ctu
      hwt.symm htE hR₀t hT₀t
    exact frame _ a1 a2 a3 a4 a5 a6 (triv_mul_of_comm hΛt ht') hu'
  · obtain ⟨a1, a2, a3, a4, a5, a6⟩ := caseA1_mul hw2 hwt hwu hwE hR₀w hT₀w hu.sq ctu.symm rfl
      hwu.symm huE hR₀u hT₀u
    exact frame _ a1 a2 a3 a4 a5 a6 ht' (triv_mul_of_comm hΛu hu')
  · have hutt : u * t * t = t * (u * t) := by rw [← mul_assoc, ctu]
    have hutu : u * t * u = u * (u * t) := by rw [mul_assoc, ctu]
    have hutw : u * t * w = w * (u * t) := by
      calc u * t * w = u * (t * w) := by group
        _ = u * (w * t) := by rw [hwt]
        _ = (u * w) * t := by group
        _ = (w * u) * t := by rw [hwu]
        _ = w * (u * t) := by group
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := caseA1_mul hw2 hwt hwu hwE hR₀w hT₀w hut2 hutt hutu hutw
      (Subgroup.mul_mem _ huE htE) (fun x hx => mem_centralizer_mul (hR₀u hx) (hR₀t hx))
      (fun x hx => mem_centralizer_mul (hT₀u hx) (hT₀t hx))
    have e1 : w * (u * t) = w * u * t := by group
    have e2 : w * (u * t) = w * t * u := by rw [← ctu]; group
    refine frame _ a1 a2 a3 a4 a5 a6 ?_ ?_
    · rw [e1]
      exact triv_mul_of_comm hΛt ht'
    · rw [e2]
      exact triv_mul_of_comm hΛu hu'

end Frame

end LinkZ2S

section Frame


variable {n : ℕ}

theorem tightLinkZ2L2BigR_of (h4 : Thm4RBelow 3 n) (h5 : Thm5RBelowF 3 n)
    (htw : PhilipHall.Frame.Thm1RTwinLiftSetEBelow n) (hE4 : E4AutOddFreeR)
    (hOm : OmegaAutOddFreeR) (hout : TightLinkZ2L2OuterR 3 n) (hin : TightLinkZ2L2InnerR 3 n) :
    TightLinkZ2L2BigR 3 n := by
  intro Y _ _ R S t hL hc hT hbad hZ2 hsimp hidx ⟨p, f, hp, hp2, hf, h9, hk⟩
  obtain ⟨J, hJ, u, hu, hne⟩ := id hbad
  have h163 := LinkZ2S.concl163_linkLayer hL hsimp hidx hp hp2 hf h9 hk
  obtain ⟨R₀, T₀, hR₀, hR₀u, hT₀, hT₀N⟩ := LinkZ2S.exists_adapted hL hJ hu
  by_cases hD1 : ∃ R₁ T₁ : Subgroup Y, IsSylow2In R₁ (tightCore R) ∧
      R₁ ≤ Subgroup.centralizer ({u} : Set Y) ∧ IsSylow2In T₁ J ∧
      T₁ ≤ Subgroup.normalizer ((tightCore R : Subgroup Y) : Set Y) ∧
      ∃ w : Y, w * w = 1 ∧ w * t = t * w ∧ w * u = u * w ∧
        w ∉ Subgroup.closure ({t, u} : Set Y) ∧
        R₁ ≤ Subgroup.centralizer ({w} : Set Y) ∧ T₁ ≤ Subgroup.centralizer ({w} : Set Y)
  · obtain ⟨R₁, T₁, hR₁, hR₁u, hT₁, hT₁N, w, hw2, hwt, hwu, hwE, hR₁w, hT₁w⟩ := hD1
    exact LinkZ2S.false_of_caseA1 h4 h5 htw hE4 hOm hL hc hbad hZ2.1 h163 hJ hu hR₁ hR₁u hT₁
      hT₁N hw2 hwt hwu hwE hR₁w hT₁w
  · by_cases hx : ∃ x : Y, IsPGroup 2 ↥(Subgroup.zpowers x) ∧ x * t = t * x ∧ x * u = u * x ∧
        (¬ InnerModOdd (linkLayer R t) x ∨
          ¬ InnerModOdd (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) x)
    · exact hout Y R S t hL hc hT hZ2 hsimp hidx ⟨p, f, hp, hp2, hf, h9, hk⟩ J hJ u hu hne
        R₀ T₀ hR₀ hR₀u hT₀ hT₀N (fun hw => hD1 ⟨R₀, T₀, hR₀, hR₀u, hT₀, hT₀N, hw⟩) hx
    · refine hin Y R S t hL hc hT hZ2 hsimp hidx ⟨p, f, hp, hp2, hf, h9, hk⟩ J hJ u hu hne
        (fun R₁ T₁ h1 h2 h3 h4' hw => hD1 ⟨R₁, T₁, h1, h2, h3, h4', hw⟩) ?_
      intro x hx2 hxt hxu
      by_cases h1 : InnerModOdd (linkLayer R t) x
      · exact ⟨h1, by_contra fun h2 => hx ⟨x, hx2, hxt, hxu, Or.inr h2⟩⟩
      · exact absurd ⟨x, hx2, hxt, hxu, Or.inl h1⟩ hx

theorem outer_of_outerAll (h4 : Thm4RBelow 3 n) (h5 : Thm5RBelowF 3 n)
    (htw : PhilipHall.Frame.Thm1RTwinLiftSetEBelow n) (hE4 : E4AutOddFreeR)
    (hOm : OmegaAutOddFreeR) (hout : TightLinkZ2L2OuterAllR 3 n) :
    TightLinkZ2L2OuterR 3 n := by
  intro Y _ _ R S t hL hc hT hZ2 hsimp hidx hmodel J hJ u hu hne
    R₀ T₀ hR₀ hR₀u hT₀ hT₀N _ hx
  obtain ⟨p, f, hp, hp2, hf, h9, hk⟩ := hmodel
  have hbad : LinkAlphaBad R t := ⟨J, hJ, u, hu, hne⟩
  have h163 := LinkZ2S.concl163_linkLayer hL hsimp hidx hp hp2 hf h9 hk
  by_cases hD1 : ∃ R₁ T₁ : Subgroup Y, IsSylow2In R₁ (tightCore R) ∧
      R₁ ≤ Subgroup.centralizer ({u} : Set Y) ∧ IsSylow2In T₁ J ∧
      T₁ ≤ Subgroup.normalizer ((tightCore R : Subgroup Y) : Set Y) ∧
      ∃ w : Y, w * w = 1 ∧ w * t = t * w ∧ w * u = u * w ∧
        w ∉ Subgroup.closure ({t, u} : Set Y) ∧
        R₁ ≤ Subgroup.centralizer ({w} : Set Y) ∧ T₁ ≤ Subgroup.centralizer ({w} : Set Y)
  · obtain ⟨R₁, T₁, hR₁, hR₁u, hT₁, hT₁N, w, hw2, hwt, hwu, hwE, hR₁w, hT₁w⟩ := hD1
    exact LinkZ2S.false_of_caseA1 h4 h5 htw hE4 hOm hL hc hbad hZ2.1 h163 hJ hu hR₁ hR₁u hT₁
      hT₁N hw2 hwt hwu hwE hR₁w hT₁w
  · exact hout Y R S t hL hc hT hZ2 hsimp hidx ⟨p, f, hp, hp2, hf, h9, hk⟩ J hJ u hu hne
      (fun R₁ T₁ h1 h2 h3 h4' hw => hD1 ⟨R₁, T₁, h1, h2, h3, h4', hw⟩) hx

end Frame

end CFSG.ClassicalInvolution.Q3.TL4
