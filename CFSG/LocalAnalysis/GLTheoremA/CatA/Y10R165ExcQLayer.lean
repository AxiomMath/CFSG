module

public import CFSG.RankThree.PartOne.KE.SigmaUntwisted2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165LayerPullback

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE

variable {K M : Type} [Group K] [Group M] {x z : K}

@[expose] def comapCentralizer (ψ : ↥(Subgroup.centralizer ({x} : Set K)) →* M)
    (P : Subgroup M) : Subgroup K :=
  (P.comap ψ).map (Subgroup.centralizer ({x} : Set K)).subtype

theorem mem_comapCentralizer_iff {ψ : ↥(Subgroup.centralizer ({x} : Set K)) →* M}
    {P : Subgroup M} {g : K} :
    g ∈ comapCentralizer ψ P ↔
      ∃ hg : g ∈ Subgroup.centralizer ({x} : Set K), ψ ⟨g, hg⟩ ∈ P := by
  constructor
  · intro h
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp h
    exact ⟨y.2, hy⟩
  · rintro ⟨hg, hgP⟩
    exact Subgroup.mem_map_of_mem (f := (Subgroup.centralizer ({x} : Set K)).subtype)
      (show (⟨g, hg⟩ : ↥(Subgroup.centralizer ({x} : Set K))) ∈ P.comap ψ from hgP)

theorem comapCentralizer_mono {ψ : ↥(Subgroup.centralizer ({x} : Set K)) →* M}
    {P P' : Subgroup M} (h : P ≤ P') : comapCentralizer ψ P ≤ comapCentralizer ψ P' :=
  Subgroup.map_mono (Subgroup.comap_mono h)

theorem comapCentralizer_le_centralizer
    (ψ : ↥(Subgroup.centralizer ({x} : Set K)) →* M) (hψ : Function.Injective ψ)
    (hzC : z ∈ Subgroup.centralizer ({x} : Set K))
    {P : Subgroup M} (hPz : P ≤ Subgroup.centralizer ({ψ ⟨z, hzC⟩} : Set M)) :
    comapCentralizer ψ P ≤ Subgroup.centralizer ({z} : Set K) := by
  intro q hq
  obtain ⟨hqC, hqP⟩ := mem_comapCentralizer_iff.1 hq
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hcomm : (⟨q, hqC⟩ : ↥(Subgroup.centralizer ({x} : Set K))) *
      ⟨z, hzC⟩ = ⟨z, hzC⟩ * ⟨q, hqC⟩ := by
    apply hψ
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_singleton_iff.1 (hPz hqP)
  exact congrArg Subtype.val hcomm

theorem comapCentralizer_subgroupOf_normal
    (ψ : ↥(Subgroup.centralizer ({x} : Set K)) →* M) (hψ : Function.Injective ψ)
    {P QL : Subgroup M} (hQLP : QL ≤ P)
    (hzC : z ∈ Subgroup.centralizer ({x} : Set K))
    (hQLz : QL ≤ Subgroup.centralizer ({ψ ⟨z, hzC⟩} : Set M))
    (hN : ∀ y : ↥(Subgroup.centralizer ({x} : Set K)),
      (y : K) * z = z * (y : K) → ψ y ∈ Subgroup.normalizer (QL : Set M)) :
    ((comapCentralizer (x := x) ψ QL).subgroupOf
      (comapCentralizer (x := x) ψ P ⊓ Subgroup.centralizer ({z} : Set K))).Normal := by
  have hQJ : comapCentralizer ψ QL ≤ comapCentralizer ψ P :=
    comapCentralizer_mono hQLP
  have hQz : comapCentralizer ψ QL ≤ Subgroup.centralizer ({z} : Set K) :=
    comapCentralizer_le_centralizer ψ hψ hzC hQLz
  have hQle : comapCentralizer ψ QL ≤
      comapCentralizer ψ P ⊓ Subgroup.centralizer ({z} : Set K) :=
    le_inf hQJ hQz
  rw [Subgroup.normal_subgroupOf_iff hQle]
  intro q g hq hg
  obtain ⟨hqC, hqQL⟩ := mem_comapCentralizer_iff.1 hq
  obtain ⟨hgJ, hgz⟩ := Subgroup.mem_inf.mp hg
  obtain ⟨hgC, hgP⟩ := mem_comapCentralizer_iff.1 hgJ
  have hgN : ψ ⟨g, hgC⟩ ∈ Subgroup.normalizer (QL : Set M) :=
    hN ⟨g, hgC⟩ (Subgroup.mem_centralizer_singleton_iff.1 hgz)
  refine mem_comapCentralizer_iff.2 ⟨?_, ?_⟩
  · exact mul_mem (mul_mem hgC hqC) (inv_mem hgC)
  · have hsub : (⟨g * q * g⁻¹, mul_mem (mul_mem hgC hqC) (inv_mem hgC)⟩ :
        ↥(Subgroup.centralizer ({x} : Set K))) =
        ⟨g, hgC⟩ * ⟨q, hqC⟩ * ⟨g, hgC⟩⁻¹ := Subtype.ext rfl
    rw [hsub, map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.1 hgN (ψ ⟨q, hqC⟩)).1 hqQL

theorem exists_comapCentralizer_layer
    (ψ : ↥(Subgroup.centralizer ({x} : Set K)) →* M) (hψ : Function.Injective ψ)
    {P QL : Subgroup M} (hQLP : QL ≤ P) (hQLrange : QL ≤ ψ.range)
    (hzC : z ∈ Subgroup.centralizer ({x} : Set K))
    (hQLz : QL ≤ Subgroup.centralizer ({ψ ⟨z, hzC⟩} : Set M))
    (hN : ∀ y : ↥(Subgroup.centralizer ({x} : Set K)),
      (y : K) * z = z * (y : K) → ψ y ∈ Subgroup.normalizer (QL : Set M)) :
    ∃ J Q : Subgroup K, J = comapCentralizer ψ P ∧ Q = comapCentralizer ψ QL ∧
      Q ≤ J ∧ Q ≤ Subgroup.centralizer ({z} : Set K) ∧
      (Q.subgroupOf (J ⊓ Subgroup.centralizer ({z} : Set K))).Normal ∧
      Nonempty (Q ≃* QL) :=
  ⟨comapCentralizer ψ P, comapCentralizer ψ QL, rfl, rfl,
    comapCentralizer_mono hQLP, comapCentralizer_le_centralizer ψ hψ hzC hQLz,
    comapCentralizer_subgroupOf_normal ψ hψ hQLP hzC hQLz hN,
    ⟨comapMapMulEquiv hψ hQLrange⟩⟩

theorem exists_qLayer_of_quasisimple
    (ψ : ↥(Subgroup.centralizer ({x} : Set K)) →* M) (hψ : Function.Injective ψ)
    {P QL : Subgroup M} (hQLP : QL ≤ P) (hQLrange : QL ≤ ψ.range)
    (hzC : z ∈ Subgroup.centralizer ({x} : Set K))
    (hQLz : QL ≤ Subgroup.centralizer ({ψ ⟨z, hzC⟩} : Set M))
    (hN : ∀ y : ↥(Subgroup.centralizer ({x} : Set K)),
      (y : K) * z = z * (y : K) → ψ y ∈ Subgroup.normalizer (QL : Set M))
    {p : ℕ} (hQL : CFSG.Open.IsQuasisimple ↥QL) (hpQL : p ∣ Nat.card QL) :
    ∃ Q : Subgroup K, Q ≤ comapCentralizer ψ P ∧
      Q ≤ Subgroup.centralizer ({z} : Set K) ∧
      (Q.subgroupOf (comapCentralizer ψ P ⊓ Subgroup.centralizer ({z} : Set K))).Normal ∧
      CFSG.Open.IsQuasisimple ↥Q ∧ p ∣ Nat.card Q := by
  obtain ⟨J', Q', hJ', hQ', hQJ', hQz', hQn', ⟨e⟩⟩ :=
    exists_comapCentralizer_layer ψ hψ hQLP hQLrange hzC hQLz hN
  refine ⟨Q', ?_, hQz', ?_, ?_, ?_⟩
  · rwa [hJ'] at hQJ'
  · rwa [hJ'] at hQn'
  · exact CFSG.Open.IsQuasisimple.of_mulEquiv e hQL
  · rw [Nat.card_congr e.toEquiv]
    exact hpQL

section Bridge

variable
  {τ : Tag} {K : Type} [Field K] {L : Type} [Field L] [Algebra K L]
  {Fr : L →+* L} {n g0 : ModGL τ L} {c x : adjointGroup τ K}

@[expose] noncomputable def conjAdjEmbHom (τ : Tag) (K : Type) [Field K] (L : Type) [Field L]
    [Algebra K L] (g0 : ModGL τ L) (c x : adjointGroup τ K) :
    ↥(Subgroup.centralizer ({x} : Set (adjointGroup τ K))) →* ModGL τ L where
  toFun y := g0⁻¹ * adjEmb τ K L (c * (y : adjointGroup τ K) * c⁻¹) * g0
  map_one' := by simp
  map_mul' := by
    intro y y'
    simp only [Subgroup.coe_mul, map_mul, MulMemClass.coe_mul, map_inv]
    group

theorem le_range_conjAdjEmbHom_of_twistedFixed (hg0C : g0 ∈ adjointGroup τ L)
    (hg0 : Units.map (entrywiseHom Fr) g0 = g0 * n)
    {Q : Subgroup (ModGL τ L)} (hQfin : Finite Q) (hQperf : ⁅Q, Q⁆ = Q)
    (hQadj : Q ≤ adjointGroup τ L)
    (hQfix : Q ≤ twistedFixedPoints n (Units.map (entrywiseHom Fr)))
    (hQcent : ∀ q ∈ Q, Commute q
      (g0⁻¹ * adjEmb τ K L (c * x * c⁻¹) * g0))
    (hperf : ∀ P : Subgroup (ModGL τ L), Finite P → P ≤ adjointGroup τ L →
      (∀ y ∈ P, Units.map (entrywiseHom Fr) y = y) → ⁅P, P⁆ = P →
        P ≤ (adjEmb τ K L).range) :
    Q ≤ (conjAdjEmbHom τ K L g0 c x).range := by
  classical
  intro q hq
  set P' : Subgroup (ModGL τ L) := Q.map (MulAut.conj g0).toMonoidHom with hP'
  have hP'fin : Finite P' :=
    Finite.of_equiv ↥Q (Subgroup.equivMapOfInjective Q (MulAut.conj g0).toMonoidHom
      (MulAut.conj g0).injective).toEquiv
  have hP'adj : P' ≤ adjointGroup τ L := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
    have e : (MulAut.conj g0).toMonoidHom y = g0 * y * g0⁻¹ := by simp [MulAut.conj_apply]
    rw [e]
    exact mul_mem (mul_mem hg0C (hQadj hy)) (inv_mem hg0C)
  have hP'fix : ∀ z ∈ P', Units.map (entrywiseHom Fr) z = z := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
    have hyfix : n * Units.map (entrywiseHom Fr) y * n⁻¹ = y :=
      mem_twistedFixedPoints.1 (hQfix hy)
    have hyfix' : Units.map (entrywiseHom Fr) y = n⁻¹ * y * n := by
      calc Units.map (entrywiseHom Fr) y = n⁻¹ * (n * Units.map (entrywiseHom Fr) y * n⁻¹) * n := by
            group
        _ = n⁻¹ * y * n := by rw [hyfix]
    have e : (MulAut.conj g0).toMonoidHom y = g0 * y * g0⁻¹ := by simp [MulAut.conj_apply]
    rw [e, map_mul, map_mul, map_inv, hg0, hyfix']
    group
  have hP'perf : ⁅P', P'⁆ = P' := by
    rw [hP', ← Subgroup.map_commutator, hQperf]
  have hrange : P' ≤ (adjEmb τ K L).range := hperf P' hP'fin hP'adj hP'fix hP'perf
  have hq' : g0 * q * g0⁻¹ ∈ P' := by
    rw [hP']
    exact Subgroup.mem_map_of_mem _ hq
  obtain ⟨y₀, hy₀⟩ := hrange hq'
  have hιcomm : Commute (adjEmb τ K L (c * x * c⁻¹)) (adjEmb τ K L y₀) := by
    have h := congrArg (fun t => g0 * t * g0⁻¹) (hQcent q hq).eq
    have e1 : g0 * (q * (g0⁻¹ * adjEmb τ K L (c * x * c⁻¹) * g0)) * g0⁻¹ =
        (g0 * q * g0⁻¹) * adjEmb τ K L (c * x * c⁻¹) := by group
    have e2 : g0 * ((g0⁻¹ * adjEmb τ K L (c * x * c⁻¹) * g0) * q) * g0⁻¹ =
        adjEmb τ K L (c * x * c⁻¹) * (g0 * q * g0⁻¹) := by group
    rw [e1, e2, ← hy₀] at h
    exact h.symm
  have hy₀comm : (c * x * c⁻¹) * y₀ = y₀ * (c * x * c⁻¹) :=
    adjEmb_injective (by simpa only [map_mul] using hιcomm.eq)
  refine ⟨⟨c⁻¹ * y₀ * c, ?_⟩, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have h := congrArg (fun t => c⁻¹ * t * c) hy₀comm
    have e1 : c⁻¹ * ((c * x * c⁻¹) * y₀) * c = x * (c⁻¹ * y₀ * c) := by group
    have e2 : c⁻¹ * (y₀ * (c * x * c⁻¹)) * c = (c⁻¹ * y₀ * c) * x := by group
    rw [e1, e2] at h
    exact h.symm
  · show g0⁻¹ * adjEmb τ K L (c * (c⁻¹ * y₀ * c) * c⁻¹) * g0 = q
    have e : c * (c⁻¹ * y₀ * c) * c⁻¹ = y₀ := by group
    rw [e, hy₀]
    group

end Bridge

theorem commute_psi_of_commute {τ : Tag} {K : Type} [Field K] {L : Type} [Field L]
    {x z : adjointGroup τ K}
    {ψ : ↥(Subgroup.centralizer ({x} : Set (adjointGroup τ K))) →* ModGL τ L}
    {y : ↥(Subgroup.centralizer ({x} : Set (adjointGroup τ K)))}
    (hzC : z ∈ Subgroup.centralizer ({x} : Set (adjointGroup τ K)))
    (hyz : (y : adjointGroup τ K) * z = z * (y : adjointGroup τ K)) :
    Commute (ψ y) (ψ ⟨z, hzC⟩) := by
  show ψ y * ψ ⟨z, hzC⟩ = ψ ⟨z, hzC⟩ * ψ y
  calc ψ y * ψ ⟨z, hzC⟩ = ψ (y * ⟨z, hzC⟩) := (map_mul ψ y ⟨z, hzC⟩).symm
    _ = ψ ⟨(y : adjointGroup τ K) * z, mul_mem y.2 hzC⟩ := rfl
    _ = ψ ⟨z * (y : adjointGroup τ K), mul_mem hzC y.2⟩ := by
        congr 1
        exact Subtype.ext hyz
    _ = ψ (⟨z, hzC⟩ * y) := rfl
    _ = ψ ⟨z, hzC⟩ * ψ y := map_mul ψ ⟨z, hzC⟩ y

end CFSG.LocalAnalysis.GLTheoremA.Y10F

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint.Chevalley

theorem mul_mem_twistedFixedPoints_of_mem {τ : Tag} {L : Type} [Field L]
    {n g u : ModGL τ L} {Φ : ModGL τ L →* ModGL τ L}
    (hg : g ∈ twistedFixedPoints n Φ) (hu : u ∈ twistedFixedPoints n Φ) :
    g * u * g⁻¹ ∈ twistedFixedPoints n Φ := by
  rw [mem_twistedFixedPoints] at hg hu ⊢
  calc n * Φ (g * u * g⁻¹) * n⁻¹
      = (n * Φ g * n⁻¹) * (n * Φ u * n⁻¹) * (n * Φ g * n⁻¹)⁻¹ := by
        rw [map_mul, map_mul, map_inv]; group
    _ = g * u * g⁻¹ := by rw [hg, hu]

theorem mem_normalizer_inf_twistedFixedPoints {τ : Tag} {L : Type} [Field L]
    {n : ModGL τ L} {Φ : ModGL τ L →* ModGL τ L} {U : Subgroup (ModGL τ L)}
    {g : ModGL τ L}
    (hgN : g ∈ Subgroup.normalizer (U : Set (ModGL τ L)))
    (hg : g ∈ twistedFixedPoints n Φ) :
    g ∈ Subgroup.normalizer (U ⊓ twistedFixedPoints n Φ : Set (ModGL τ L)) := by
  change g ∈ Subgroup.normalizer ((U ⊓ twistedFixedPoints n Φ : Subgroup (ModGL τ L)) :
    Set (ModGL τ L))
  rw [Subgroup.mem_normalizer_iff] at hgN ⊢
  intro x
  constructor
  · rintro ⟨hxU, hxF⟩
    exact ⟨(hgN x).1 hxU, mul_mem_twistedFixedPoints_of_mem hg hxF⟩
  · rintro ⟨hxU, hxF⟩
    refine ⟨(hgN x).2 hxU, ?_⟩
    have hinv : g⁻¹ ∈ twistedFixedPoints n Φ := inv_mem hg
    have h := mul_mem_twistedFixedPoints_of_mem hinv hxF
    have h' : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rw [← h']
    exact h

end CFSG.RankThree.PartOne.KE
