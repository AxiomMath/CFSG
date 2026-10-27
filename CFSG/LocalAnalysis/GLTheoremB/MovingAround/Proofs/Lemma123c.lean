module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma123b
public import CFSG.LieType.ChevTwo.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut autBar barOf innerAut)
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple ambiguousChev onLie)
open CFSG.LieType.ChevTwo (Chev2KDOut Chev2CoreCent autCentralizer)
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevTwo IsChevIndexTwo)

namespace Lemma123

theorem isChevTwo_of_isChevSimple_two {S : Type} [Group S] (h : IsChevSimple 2 S) : IsChevTwo S := by
  rcases h with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  · cases i with
    | lie d =>
      obtain ⟨x, hx⟩ := d
      refine Or.inl ⟨⟨x, hx⟩, ?_, ⟨e⟩⟩
      have h2 : x.characteristic = 2 := hi
      cases x <;> simp_all [IsChevIndexTwo]
    | cyclic _ _ => exact absurd hi (by simp [onLie])
    | alternating _ _ => exact absurd hi (by simp [onLie])
    | sporadic _ => exact absurd hi (by simp [onLie])
  · cases i with
    | alternating n hn =>
      refine Or.inr (Or.inl ⟨n, ?_, ⟨e⟩⟩)
      simpa [ambiguousChev] using hi
    | lie d =>
      obtain ⟨x, hx⟩ := d
      refine Or.inr (Or.inr ⟨⟨x, hx⟩, ?_, ⟨e⟩⟩)
      have hi' : ambiguousChev 2 (TauCeti.CFSGIndex.lie ⟨x, hx⟩) := hi
      cases x with
      | A n q =>
        rcases n with _ | _ | n
        · simp [ambiguousChev] at hi'
        · simp [ambiguousChev] at hi'
          exact Or.inl ⟨q, by rw [TauCeti.PrimePower.card_def]; exact hi', rfl⟩
        · simp [ambiguousChev] at hi'
      | twistedA n q =>
        rcases n with _ | _ | _ | n
        · simp [ambiguousChev] at hi'
        · simp [ambiguousChev] at hi'
        · simp [ambiguousChev] at hi'
          exact Or.inr ⟨q, by rw [TauCeti.PrimePower.card_def]; exact hi', rfl⟩
        · rcases n with _ | n <;> simp [ambiguousChev] at hi'
      | _ => simp [ambiguousChev] at hi'
    | cyclic _ _ => exact absurd hi (by simp [ambiguousChev])
    | sporadic _ => exact absurd hi (by simp [ambiguousChev])

@[expose] noncomputable def autQ (Y : Type*) [Group Y] : MulAut Y →* MulAut (Y ⧸ Subgroup.center Y) where
  toFun β := QuotientGroup.congr (Subgroup.center Y) (Subgroup.center Y) β (Subgroup.map_center_eq β)
  map_one' := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H x => rfl
  map_mul' β γ := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H x => rfl

theorem autQ_mk {Y : Type*} [Group Y] (β : MulAut Y) (x : Y) :
    autQ Y β (x : Y ⧸ Subgroup.center Y) = (β x : Y ⧸ Subgroup.center Y) := rfl

theorem autQ_injective {Y : Type*} [Group Y] (hY : commutator Y = ⊤) : Function.Injective (autQ Y) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro β hβ
  rw [MonoidHom.mem_ker] at hβ
  have hβ' : ∀ x : Y, x⁻¹ * β x ∈ Subgroup.center Y := by
    intro x
    have h1 := congrArg (fun γ : MulAut (Y ⧸ Subgroup.center Y) => γ (x : Y ⧸ Subgroup.center Y)) hβ
    simp only [autQ_mk, MulAut.one_apply] at h1
    exact QuotientGroup.eq.1 h1.symm
  rw [Subgroup.mem_bot]
  let δ : Y →* Subgroup.center Y :=
    { toFun := fun x => ⟨x⁻¹ * β x, hβ' x⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        rw [map_mul]
        have hx := Subgroup.mem_center_iff.1 (hβ' x)
        calc (x * y)⁻¹ * (β x * β y) = y⁻¹ * (x⁻¹ * β x) * β y := by group
          _ = (x⁻¹ * β x) * (y⁻¹ * β y) := by rw [hx y⁻¹]; group }
  have hcomm : commutator Y ≤ δ.ker := by
    rw [commutator, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.1 (δ b).2 (δ a))
  ext x
  have hx : x ∈ δ.ker := hcomm (hY ▸ Subgroup.mem_top x)
  rw [MonoidHom.mem_ker] at hx
  have h1 : x⁻¹ * β x = 1 := congrArg Subtype.val hx
  rw [MulAut.one_apply]
  exact (inv_mul_eq_one.1 h1).symm

theorem autQ_conj {Y : Type*} [Group Y] (y : Y) :
    autQ Y (MulAut.conj y) = MulAut.conj (y : Y ⧸ Subgroup.center Y) := by
  ext z
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective z
  simp [autQ_mk, MulAut.conj_apply]

theorem conj_eq_one_of_mem_center {Y : Type*} [Group Y] {z : Y} (hz : z ∈ Subgroup.center Y) :
    (MulAut.conj z : MulAut Y) = 1 := by
  ext w
  simp only [MulAut.conj_apply, MulAut.one_apply]
  rw [← Subgroup.mem_center_iff.1 hz w]
  simp

theorem mem_center_of_conj_eq_one {Y : Type*} [Group Y] {z : Y} (h : (MulAut.conj z : MulAut Y) = 1) :
    z ∈ Subgroup.center Y := by
  rw [Subgroup.mem_center_iff]
  intro w
  have := congrArg (fun φ : MulAut Y => φ w) h
  simp only [MulAut.conj_apply, MulAut.one_apply] at this
  calc w * z = (z * w * z⁻¹) * z := by rw [this]
    _ = z * w := by group

theorem comm_conj_iff_fixed {Y : Type*} [Group Y] (y : Y) (r : MulAut Y) :
    r * MulAut.conj y = MulAut.conj y * r ↔
      autQ Y r (y : Y ⧸ Subgroup.center Y) = (y : Y ⧸ Subgroup.center Y) := by
  rw [autQ_mk, QuotientGroup.eq]
  constructor
  · intro h
    have hz : ∀ z : Y, r y * r z * (r y)⁻¹ = y * r z * y⁻¹ := fun z => by
      have := congrArg (fun φ : MulAut Y => φ z) h
      simpa [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv] using this
    rw [Subgroup.mem_center_iff]
    intro w
    have h2 := hz (r.symm w)
    rw [MulEquiv.apply_symm_apply] at h2
    calc w * ((r y)⁻¹ * y) = (r y)⁻¹ * ((r y * w * (r y)⁻¹) * y) := by group
      _ = (r y)⁻¹ * ((y * w * y⁻¹) * y) := by rw [h2]
      _ = ((r y)⁻¹ * y) * w := by group
  · intro h
    ext z
    have hc := Subgroup.mem_center_iff.1 h
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
    have h3 := hc (r z)
    calc r y * r z * (r y)⁻¹ = r y * (r z * ((r y)⁻¹ * y)) * y⁻¹ := by group
      _ = r y * (((r y)⁻¹ * y) * r z) * y⁻¹ := by rw [h3]
      _ = y * r z * y⁻¹ := by group

theorem map_le_normalizer_map {G H : Type*} [Group G] [Group H] (f : G →* H) {A B : Subgroup G}
    (h : A ≤ Subgroup.normalizer (B : Set G)) :
    A.map f ≤ Subgroup.normalizer ((B.map f : Subgroup H) : Set H) := by
  rintro _ ⟨b, hb, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨b * w * b⁻¹, (Subgroup.mem_normalizer_iff.1 (h hb) w).1 hw, by simp⟩
  · rintro ⟨w, hw, hwx⟩
    have hb' : b⁻¹ ∈ Subgroup.normalizer (B : Set G) := h (A.inv_mem hb)
    have hmem : b⁻¹ * w * b⁻¹⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.1 hb' w).1 hw
    refine ⟨b⁻¹ * w * b⁻¹⁻¹, hmem, ?_⟩
    calc f (b⁻¹ * w * b⁻¹⁻¹) = (f b)⁻¹ * f w * f b := by simp [map_mul, map_inv]
      _ = (f b)⁻¹ * (f b * x * (f b)⁻¹) * f b := by rw [hwx]
      _ = x := by group

theorem input7_12_2_of_chev2 (hKD : Chev2KDOut) : Input7_12_2 := by
  intro p hp hp2 Y _ _ hq hY W B' hW hB hN
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsSimpleGroup (Y ⧸ Subgroup.center Y) := hq.2
  have hnonab := Prop1116Design.not_isCommutative_barQuot Y hq
  have hperf : commutator Y = ⊤ := hq.1
  have hchev := isChevTwo_of_isChevSimple_two hY
  have hP : IsPGroup p ↥(B'.map (autQ Y)) := hB.map _
  have hT : IsPGroup 2 ↥(W.map (autQ Y)) := hW.map _
  have hPN : B'.map (autQ Y) ≤ Subgroup.normalizer ((W.map (autQ Y) : Subgroup _) : Set _) :=
    map_le_normalizer_map (autQ Y) hN
  have h1 := hKD (Y ⧸ Subgroup.center Y) hq.2 hnonab hchev p hp hp2 _ _ hP hT hPN
  intro φ hφ
  have hΦφ : autQ Y φ ∈ ⁅W.map (autQ Y), B'.map (autQ Y)⁆ := by
    rw [← Subgroup.map_commutator]
    exact Subgroup.mem_map_of_mem _ hφ
  obtain ⟨s, hs⟩ := h1 hΦφ
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective s
  have h2 : autQ Y φ = autQ Y (MulAut.conj y) := by rw [autQ_conj]; exact hs.symm
  exact ⟨y, (autQ_injective hperf h2).symm⟩

theorem input19_20_1_of_chev2 (hCore : Chev2CoreCent) : Input19_20_1 := by
  intro p hp hp2 Y _ _ hq hY R hR
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsSimpleGroup (Y ⧸ Subgroup.center Y) := hq.2
  have hnonab := Prop1116Design.not_isCommutative_barQuot Y hq
  have hperf : commutator Y = ⊤ := hq.1
  have hchev := isChevTwo_of_isChevSimple_two hY
  have hRq : IsPGroup p ↥(R.map (autQ Y)) := hR.map _
  have h0 := hCore (Y ⧸ Subgroup.center Y) hq.2 hnonab hchev p hp hp2 _ hRq
  set Q : Subgroup (MulAut Y) :=
    pCoreOf 2 (innerAut Y ⊓ Subgroup.centralizer (R : Set (MulAut Y))) with hQ
  set Q₀ : Subgroup Y := Q.comap (MulAut.conj : Y →* MulAut Y) with hQ₀
  set Q' : Subgroup (Y ⧸ Subgroup.center Y) := Q₀.map (QuotientGroup.mk' (Subgroup.center Y)) with hQ'
  have hQle : Q ≤ innerAut Y ⊓ Subgroup.centralizer (R : Set (MulAut Y)) :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hQ2 : IsPGroup 2 ↥Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hcenQ : ∀ z ∈ Subgroup.center Y, z ∈ Q₀ := fun z hz => by
    show MulAut.conj z ∈ Q
    rw [conj_eq_one_of_mem_center hz]
    exact Q.one_mem
  have hmemQ' : ∀ y : Y, (y : Y ⧸ Subgroup.center Y) ∈ Q' ↔ y ∈ Q₀ := by
    intro y
    constructor
    · rintro ⟨y₁, hy₁, hy⟩
      have hz : y₁⁻¹ * y ∈ Subgroup.center Y := QuotientGroup.eq.1 hy
      have : y = y₁ * (y₁⁻¹ * y) := by group
      rw [this]
      exact Q₀.mul_mem hy₁ (hcenQ _ hz)
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hfix : ∀ y : Y, MulAut.conj y ∈ Subgroup.centralizer (R : Set (MulAut Y)) →
      ∀ α ∈ R.map (autQ Y), α (y : Y ⧸ Subgroup.center Y) = (y : Y ⧸ Subgroup.center Y) := by
    intro y hy α hα
    obtain ⟨r, hr, rfl⟩ := hα
    exact (comm_conj_iff_fixed y r).1 (Subgroup.mem_centralizer_iff.1 hy r hr)
  have hcent : ∀ y : Y, (∀ α ∈ R.map (autQ Y), α (y : Y ⧸ Subgroup.center Y) = (y : Y ⧸ Subgroup.center Y)) →
      MulAut.conj y ∈ Subgroup.centralizer (R : Set (MulAut Y)) := by
    intro y hy
    refine Subgroup.mem_centralizer_iff.2 fun r hr => ?_
    exact (comm_conj_iff_fixed y r).2 (hy _ (Subgroup.mem_map_of_mem _ hr))
  have hQ'C : Q' ≤ autCentralizer (R.map (autQ Y)) := by
    rintro _ ⟨y, hy, rfl⟩ α hα
    exact hfix y (hQle hy).2 α hα
  have hnorm : autCentralizer (R.map (autQ Y)) ≤ Subgroup.normalizer (Q' : Set (Y ⧸ Subgroup.center Y)) := by
    intro s hs
    obtain ⟨y₁, rfl⟩ := QuotientGroup.mk_surjective s
    have hy₁ : MulAut.conj y₁ ∈ innerAut Y ⊓ Subgroup.centralizer (R : Set (MulAut Y)) :=
      Subgroup.mem_inf.2 ⟨⟨y₁, rfl⟩, hcent y₁ hs⟩
    have hN : MulAut.conj y₁ ∈ Subgroup.normalizer (Q : Set (MulAut Y)) :=
      CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ (Subgroup.le_normalizer hy₁)
    rw [Subgroup.mem_normalizer_iff]
    intro t
    obtain ⟨y₂, rfl⟩ := QuotientGroup.mk_surjective t
    have e : (y₁ : Y ⧸ Subgroup.center Y) * (y₂ : Y ⧸ Subgroup.center Y) * (y₁ : Y ⧸ Subgroup.center Y)⁻¹ =
        ((y₁ * y₂ * y₁⁻¹ : Y) : Y ⧸ Subgroup.center Y) := by simp
    rw [e, hmemQ', hmemQ']
    show MulAut.conj y₂ ∈ Q ↔ MulAut.conj (y₁ * y₂ * y₁⁻¹) ∈ Q
    have e2 : (MulAut.conj (y₁ * y₂ * y₁⁻¹) : MulAut Y) =
        MulAut.conj y₁ * MulAut.conj y₂ * (MulAut.conj y₁)⁻¹ := by simp [map_mul, map_inv]
    rw [e2]
    exact Subgroup.mem_normalizer_iff.1 hN _
  have hQ'2 : IsPGroup 2 ↥Q' := by
    intro g
    obtain ⟨y, hy, hgy⟩ := g.2
    obtain ⟨k, hk⟩ := hQ2 ⟨MulAut.conj y, hy⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : (MulAut.conj y : MulAut Y) ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    have h2 : y ^ (2 ^ k) ∈ Subgroup.center Y :=
      mem_center_of_conj_eq_one (by rw [map_pow]; exact h1)
    show (g : Y ⧸ Subgroup.center Y) ^ (2 ^ k) = 1
    rw [← hgy, ← map_pow]
    exact (QuotientGroup.eq_one_iff _).2 h2
  have hQ'le : Q' ≤ pCoreOf 2 (autCentralizer (R.map (autQ Y))) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQ'C hnorm hQ'2
  rw [h0] at hQ'le
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨⟨y, rfl⟩, -⟩ := Subgroup.mem_inf.1 (hQle hx)
  have hy0 : ((y : Y ⧸ Subgroup.center Y)) ∈ (⊥ : Subgroup (Y ⧸ Subgroup.center Y)) :=
    hQ'le ((hmemQ' y).2 hx)
  have hz : y ∈ Subgroup.center Y := (QuotientGroup.eq_one_iff y).1 (Subgroup.mem_bot.1 hy0)
  rw [Subgroup.mem_bot]
  exact conj_eq_one_of_mem_center hz

end Lemma123

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
