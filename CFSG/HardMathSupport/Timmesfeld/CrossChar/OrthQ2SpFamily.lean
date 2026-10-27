module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthQ2Cover
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthQ2SpComm
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SymplecticOrder
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SymplecticPlane
public import CFSG.RankThree.PartOne.KC.SymplecticIsotypicFixed
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SymplecticFamily

public section

open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.RankThree.PartOne.KCSpIsotypic
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
open Module CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCSpFull CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.Open (IsElemAbelian)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

section Group

theorem exists_mulEquiv_z3 {G : Type*} [CommGroup G] [Finite G] (h3 : ∀ g : G, g ^ 3 = 1)
    (hc : Nat.card G = 27) : Nonempty (G ≃* Multiplicative Z3) := by
  have : Fintype G := Fintype.ofFinite G
  have h : ∀ x : Additive G, (3 : ℕ) • x = 0 := fun x => h3 (Additive.toMul x)
  let _ : Module (ZMod 3) (Additive G) := AddCommGroup.zmodModule h
  have hcard : Fintype.card (Additive G) = Fintype.card (ZMod 3) ^ finrank (ZMod 3) (Additive G) :=
    Module.card_eq_pow_finrank
  have hfr : finrank (ZMod 3) (Additive G) = 3 := by
    rw [ZMod.card, Fintype.card_additive, ← Nat.card_eq_fintype_card, hc] at hcard
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3)
      (by rw [show (3 : ℕ) ^ 3 = 27 by norm_num]; exact hcard :
        3 ^ 3 = 3 ^ finrank (ZMod 3) (Additive G)) |>.symm
  let b := Module.finBasisOfFinrankEq (ZMod 3) (Additive G) hfr
  let e : Additive G ≃+ Z3 := b.equivFun.toAddEquiv
  exact ⟨{ toFun := fun g => Multiplicative.ofAdd (e (Additive.ofMul g))
           invFun := fun z => Additive.toMul (e.symm (Multiplicative.toAdd z))
           left_inv := fun g => by simp
           right_inv := fun z => by simp
           map_mul' := fun g h => by simp [ofAdd_add] }⟩

end Group

variable {r : ℕ} {K : Type} [Field K]

theorem exists_spInnerLift_eq (hK : Nat.card K = 2) (hr : 3 ≤ r)
    (α : MulAut (StatedProj (StatedSp r K))) : ∃ x : StatedSp r K, α = spInnerLift r K x := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : NeZero r := ⟨by omega⟩
  obtain ⟨A, σ, hα⟩ := (automorphism_generation (K := K) hr).2 α
  have hσ : σ = RingEquiv.refl K := ringEquiv_eq_refl_of_card_two hK σ
  have hμ : multiplier r K A = 1 := by
    have h0 : ((multiplier r K A : Kˣ) : K) ≠ 0 := Units.ne_zero _
    rcases eq_zero_or_one_of_card hK ((multiplier r K A : Kˣ) : K) with h | h
    · exact absurd h h0
    · exact Units.ext h
  have hAS : (A : GL (Fin r ⊕ Fin r) K) ∈ StatedSp r K := by
    have : A ∈ (multiplier r K).ker := hμ
    rw [ker_multiplier] at this
    exact this
  refine ⟨⟨A, hAS⟩, ?_⟩
  rw [hα, hσ]
  have h1 : fieldAut r K (RingEquiv.refl K) = 1 := map_one (fieldAut r K)
  rw [h1, mul_one]
  ext y
  obtain ⟨g, rfl⟩ := SymplecticHigher.proj_surjective (r := r) (K := K) y
  rw [conjAut_proj, spInnerLift_apply, MulAut.conj_apply]
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1

theorem commutator_normalized {G : Type*} [Group G] {F C : Subgroup G}
    (h : ∀ m ∈ C, ∀ g ∈ F, m * g * m⁻¹ ∈ F) :
    ∀ m ∈ C, ∀ g ∈ ⁅F, F⁆, m * g * m⁻¹ ∈ ⁅F, F⁆ := by
  intro m hm g hg
  have hle : F.map (MulAut.conj m).toMonoidHom ≤ F := by
    rintro _ ⟨a, ha, rfl⟩
    exact h m hm a ha
  have h2 : (MulAut.conj m).toMonoidHom g ∈ ⁅F, F⁆.map (MulAut.conj m).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hg
  rw [Subgroup.map_commutator] at h2
  exact Subgroup.commutator_mono hle hle h2

theorem spFixedLayer_facts {ℓ f p : ℕ} [Finite K] (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) {B : Subgroup (MulAut (StatedProj (StatedSp r K)))}
    (hB : (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))).range
      ≤ B)
    (hinj : Function.Injective (MulAut.conj : StatedProj (StatedSp r K) →*
      MulAut (StatedProj (StatedSp r K))))
    {x : StatedSp r K} (blocks : SpPrimaryBlocks ℓ f p x (proj r K x))
    (hl : SpFixedListed x) : SpListedFacts p B (proj r K x) (spFixedLayerImage x) := by
  have hcent := blocks.centralizer_eq
  by_cases h42 : spFixedDim x = 4 ∧ Nat.card K = 2
  · obtain ⟨hq, -⟩ := spFixed_four_two h42.2 blocks h42.1
    have himg : spFixedLayerImage x = (⁅spFixedFactor x, spFixedFactor x⁆).map (proj r K) := by
      unfold spFixedLayerImage
      simp only [hl, h42.1, h42.2, and_self, ↓reduceIte]
    rw [himg]
    exact spListed_facts hp hB hinj hcent
      ((commutator_le_self _).trans (spFixedFactor_le_centralizer x))
      (commutator_normalized (spFixedFactor_normalized x)) hq
  · have himg : spFixedLayerImage x = (spFixedFactor x).map (proj r K) := by
      unfold spFixedLayerImage
      simp only [hl, h42, ↓reduceIte]
    rw [himg]
    exact spListed_facts hp hB hinj hcent (spFixedFactor_le_centralizer x)
      (spFixedFactor_normalized x) (spFixedFactor_isQuasisimple hK hℓ hf blocks hl h42)

theorem proj_mem_spFixedLayerImage_of_commutator {x t : StatedSp r K} (hl : SpFixedListed x)
    (ht : t ∈ ⁅spFixedFactor x, spFixedFactor x⁆) : proj r K t ∈ spFixedLayerImage x := by
  rw [spFixedLayerImage_eq]
  refine Subgroup.mem_map_of_mem _ ?_
  unfold spFixedLayerS
  simp only [hl, ↓reduceIte]
  split_ifs
  · exact ht
  · exact commutator_le_self _ ht

theorem spBlocks_three_two [Finite K] (hK : Nat.card K = 2) (hr : 3 ≤ r) {x : StatedSp r K}
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) : SpPrimaryBlocks 2 1 3 x (proj r K x) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hK' : Nat.card K = 2 ^ 1 := by rw [hK]; norm_num
  have hℓ : Nat.Prime 2 := Nat.prime_two
  have ha1 : proj r K x ≠ 1 := fun h =>
    hx1 (KCSymplectic.eq_one_of_proj_eq_one_of_pow_eq_one (by omega) (by omega) hp h hx3)
  have ha : orderOf (proj r K x) = 3 := orderOf_eq_prime (by rw [← map_pow, hx3, map_one]) ha1
  have hxp : orderOf x = 3 := have : Fact (Nat.Prime 3) := ⟨hp⟩; orderOf_eq_prime hx3 hx1
  exact (symplectic_cross_prime_primary_centralizer_blocks hℓ le_rfl hK' hp (by omega)
    (by omega) (by omega) (proj r K x) ha).2 x rfl hxp

theorem commute_layer_of_good [Finite K] (hK : Nat.card K = 2) (hr : 3 ≤ r)
    {H : Subgroup (MulAut (StatedProj (StatedSp r K)))}
    (hH : innerAut (StatedProj (StatedSp r K)) ≤ H)
    {E : Subgroup (MulAut (StatedProj (StatedSp r K)))}
    {g : MulAut (StatedProj (StatedSp r K))} (hg : g ∈ localDeltaIn 3 H E)
    {x : StatedSp r K} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hxE : spInnerLift r K x ∈ E)
    (hdim : 4 ≤ spFixedDim x) {y : StatedSp r K} (hxy : y * x = x * y) (hy3 : y ^ 3 = 1)
    {u : Fin r ⊕ Fin r → K} (hu : spEnd x u = u) (hyu : spEnd y u ≠ u) :
    ∀ t ∈ ⁅spFixedFactor x, spFixedFactor x⁆,
      g * MulAut.conj (proj r K t) = MulAut.conj (proj r K t) * g := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hK' : Nat.card K = 2 ^ 1 := by rw [hK]; norm_num
  have hℓ : Nat.Prime 2 := Nat.prime_two
  have hrq : ¬ (r = 2 ∧ 2 ^ 1 = 2) := fun h => by omega
  obtain ⟨-, -, hinj⟩ := spProj_facts hℓ le_rfl hK' (by omega) hrq
  have ha1 : proj r K x ≠ 1 := fun h =>
    hx1 (KCSymplectic.eq_one_of_proj_eq_one_of_pow_eq_one (by omega) (by omega) hp h hx3)
  have blocks := spBlocks_three_two hK hr hx3 hx1
  have hl : SpFixedListed x := ⟨by omega, fun h => by omega⟩
  have hfacts := spFixedLayer_facts hℓ le_rfl hK' hp (B := H)
    (by rintro _ ⟨t, rfl⟩; exact hH ⟨t, rfl⟩) hinj blocks hl
  have hmem : u ∈ LinearMap.ker (spEnd x - 1) := mem_ker_sub_one_iff.2 hu
  have hdvd := dvd_card_spFixedLayerImage (by omega) hp (by omega) blocks hl hxy hy3 hmem hyu
  have hcomm := commute_of_spListedFacts hp hinj hH hg (a := proj r K x) hxE ha1 hfacts hdvd
  intro t ht
  exact hcomm _ (proj_mem_spFixedLayerImage_of_commutator hl ht)

section Parity

variable {V : Type} [AddCommGroup V] [Module K V]

theorem even_finrank_fixOf [CharP K 2] [FiniteDimensional K V] {B : LinearMap.BilinForm K V}
    (hB : B.IsAlt) (hnd : B.Nondegenerate) (ρ : Multiplicative Z3 →* Module.End K V)
    (hiso : ∀ x u v, B (act ρ x u) (act ρ x v) = B u v) (S : AddSubgroup Z3)
    (hodd : Odd (Nat.card S)) : Even (finrank K (fixOf ρ (S : Set Z3))) := by
  classical
  let T : Finset Z3 := Finset.univ.filter (· ∈ S)
  have hT : T.card = Nat.card S := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  let e : Module.End K V := ∑ s ∈ T, act ρ s
  have he : ∀ v, e v ∈ fixOf ρ (S : Set Z3) := fun v y hy => by
    simp only [e, LinearMap.sum_apply, map_sum]
    refine Finset.sum_equiv (Equiv.addLeft y) ?_ ?_
    · intro s
      simp [T, AddSubgroup.add_mem_cancel_left S hy]
    · intro s _
      simp [act_add]
  have hB' : ∀ u ∈ fixOf ρ (S : Set Z3), ∀ v, B u (e v) = B u v := fun u hu v => by
    simp only [e, LinearMap.sum_apply, map_sum]
    have : ∀ s ∈ T, B u (act ρ s v) = B u v := fun s hs => by
      have := hiso s u v
      rwa [hu s (by simpa [T] using hs)] at this
    rw [Finset.sum_congr rfl this, Finset.sum_const, hT]
    exact odd_nsmul_eq (K := K) _ hodd _
  set W := fixOf ρ (S : Set Z3) with hW
  have hrad : ∀ u ∈ W, (∀ w ∈ W, B u w = 0) → u = 0 := fun u hu h0 => by
    refine hnd.1 u fun v => ?_
    rw [← hB' u hu v]
    exact h0 _ (he v)
  have hBW : (B.restrict W).IsAlt := fun v => hB (v : V)
  have hndW : (B.restrict W).Nondegenerate := by
    refine ⟨fun u h0 => ?_, fun w h0 => ?_⟩
    · exact Subtype.ext (hrad u u.2 fun w hw => h0 ⟨w, hw⟩)
    · refine Subtype.ext (hrad w w.2 fun u hu => ?_)
      have h2 : B u w = 0 := h0 ⟨u, hu⟩
      have h3 := hB.neg_eq w u
      rw [h2] at h3
      exact neg_eq_zero.1 h3
  obtain ⟨s, hs, -⟩ := exists_mulEquiv_sesqUnitaryGroup_statedSp hBW hndW
  exact ⟨s, by omega⟩

@[expose] def dotHom (φ : Z3) : Z3 →+ ZMod 3 := AddMonoidHom.mk' (dot φ) (dot_add φ)

theorem even_finrank_fixOf_N [CharP K 2] [FiniteDimensional K V] {B : LinearMap.BilinForm K V}
    (hB : B.IsAlt) (hnd : B.Nondegenerate) (ρ : Multiplicative Z3 →* Module.End K V)
    (hiso : ∀ x u v, B (act ρ x u) (act ρ x v) = B u v) {φ : Z3} (hφ : φ ∈ Rset) :
    Even (finrank K (fixOf ρ {x | dot φ x = 0})) := by
  classical
  have h := even_finrank_fixOf hB hnd ρ hiso (AddMonoidHom.ker (dotHom φ)) (by
    have : Nat.card (AddMonoidHom.ker (dotHom φ)) = 9 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      exact card_N φ hφ
    rw [this]; decide)
  exact h

theorem even_finrank_fixOf_single [CharP K 2] [FiniteDimensional K V]
    {B : LinearMap.BilinForm K V} (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (ρ : Multiplicative Z3 →* Module.End K V)
    (hiso : ∀ x u v, B (act ρ x u) (act ρ x v) = B u v) {x : Z3} (hx : x ≠ 0) :
    Even (finrank K (fixOf ρ {x})) := by
  have hcard : Nat.card (AddSubgroup.closure ({x} : Set Z3)) = 3 := by
    have h3 : (3 : ℕ) • x = 0 := by
      have : ∀ a : ZMod 3, (3 : ℕ) • a = 0 := by decide
      ext i
      simp [this]
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [← AddSubgroup.zmultiples_eq_closure, Nat.card_zmultiples, addOrderOf_eq_prime h3 hx]
  have h := even_finrank_fixOf hB hnd ρ hiso (AddSubgroup.closure {x}) (by rw [hcard]; decide)
  have heq : fixOf ρ (AddSubgroup.closure ({x} : Set Z3) : Set Z3) = fixOf ρ {x} := by
    refine le_antisymm (fun v hv => ?_) fun v hv s hs => ?_
    · intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hv x (AddSubgroup.subset_closure rfl)
    · refine AddSubgroup.closure_induction (p := fun s _ => act ρ s v = v) ?_ ?_ ?_ ?_ hs
      · intro y hy
        exact hv y hy
      · rw [act_zero]; rfl
      · intro a b _ _ ha hb
        rw [act_add, Module.End.mul_apply, hb, ha]
      · intro a _ ha
        calc act ρ (-a) v = act ρ (-a) (act ρ a v) := by rw [ha]
          _ = v := by
            have h0 : -a + a = (0 : Z3) := by
              funext i
              exact neg_add_cancel (a i)
            rw [← Module.End.mul_apply, ← act_add, h0, act_zero]; rfl
  rw [← heq]
  exact h

end Parity

section Main

@[expose] noncomputable def spEndHom : StatedSp r K →* Module.End K (Fin r ⊕ Fin r → K) where
  toFun := spEnd
  map_one' := spEnd_one
  map_mul' := spEnd_mul

theorem spEnd_eq_one_iff {z : StatedSp r K} : spEnd z = 1 ↔ z = 1 := by
  constructor
  · intro h
    apply spLin_injective
    rw [map_one]
    exact Units.ext h
  · rintro rfl
    exact spEnd_one

theorem ker_spInnerLift_eq_bot [Finite K] (hK : Nat.card K = 2) (hr : 3 ≤ r)
    (hinj : Function.Injective (MulAut.conj : StatedProj (StatedSp r K) →*
      MulAut (StatedProj (StatedSp r K)))) : Function.Injective (spInnerLift r K) := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_spInnerLift hinj]
  have : Nat.card (proj r K).ker = 1 := by
    rw [SymplecticHigher.ker_proj, card_spScalars_eq_gcd K (by omega), hK]
    norm_num
  exact Subgroup.card_eq_one.1 this

theorem localDeltaIn_eq_bot_psp_three_two [Finite K] (hK : Nat.card K = 2) (hr : 3 ≤ r)
    {D : Subgroup (MulAut (StatedProj (StatedSp r K)))} (hD : IsElemAbelian 3 D)
    (hcard : Nat.card D = 3 ^ 3) {H : Subgroup (MulAut (StatedProj (StatedSp r K)))}
    (hH : innerAut (StatedProj (StatedSp r K)) ≤ H) : localDeltaIn 3 H D = ⊥ := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  have hK' : Nat.card K = 2 ^ 1 := by rw [hK]; norm_num
  have hrq : ¬ (r = 2 ∧ 2 ^ 1 = 2) := fun h => by omega
  obtain ⟨-, -, hinj⟩ := spProj_facts Nat.prime_two le_rfl hK' (by omega) hrq
  have hιinj := ker_spInnerLift_eq_bot hK hr hinj
  have hιsurj : Function.Surjective (spInnerLift r K) := fun α =>
    (exists_spInnerLift_eq hK hr α).imp fun x hx => hx.symm
  let e0 : StatedSp r K ≃* MulAut (StatedProj (StatedSp r K)) :=
    MulEquiv.ofBijective (spInnerLift r K) ⟨hιinj, hιsurj⟩
  set Dh : Subgroup (StatedSp r K) := D.comap (spInnerLift r K) with hDh
  have hmemDh : ∀ x, x ∈ Dh ↔ spInnerLift r K x ∈ D := fun x => Iff.rfl
  have hDhcard : Nat.card Dh = 27 := by
    have : Dh = D.map e0.symm.toMonoidHom := Subgroup.comap_equiv_eq_map_symm e0 D
    rw [this, Subgroup.card_map_of_injective e0.symm.injective, hcard]
    norm_num
  have hDh3 : ∀ x ∈ Dh, x ^ 3 = 1 := fun x hx => by
    apply hιinj
    rw [map_pow, map_one]
    exact hD.2 _ ((hmemDh x).1 hx)
  have hDhcomm : ∀ x ∈ Dh, ∀ y ∈ Dh, x * y = y * x := fun x hx y hy => by
    apply hιinj
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (hD.1.is_comm.comm ⟨_, (hmemDh x).1 hx⟩ ⟨_, (hmemDh y).1 hy⟩)
  let _ : CommGroup Dh := { (inferInstance : Group Dh) with
    mul_comm := fun a b => Subtype.ext (hDhcomm a a.2 b b.2) }
  obtain ⟨e⟩ := exists_mulEquiv_z3 (G := Dh) (fun g => Subtype.ext (hDh3 g g.2))
    (by rw [hDhcard])
  let ρ : Multiplicative Z3 →* Module.End K (Fin r ⊕ Fin r → K) :=
    spEndHom.comp (Dh.subtype.comp e.symm.toMonoidHom)
  have hact : ∀ x : Z3, act ρ x = spEnd ((e.symm (Multiplicative.ofAdd x) : Dh) : StatedSp r K) :=
    fun x => rfl
  have : CharP K 2 := charP_two_of_card hK
  have hfaith : ∀ x, act ρ x = 1 → x = 0 := fun x hx => by
    rw [hact, spEnd_eq_one_iff] at hx
    have h1 : e.symm (Multiplicative.ofAdd x) = 1 := Subtype.ext hx
    have h2 : Multiplicative.ofAdd x = 1 := by simpa using h1
    exact h2
  have hiso : ∀ x u v, spForm r K (act ρ x u) (act ρ x v) = spForm r K u v := fun x u v => by
    rw [hact]
    exact spForm_spEnd_spEnd' _ u v
  have hpN : ∀ φ ∈ Rset, Even (finrank K (fixOf ρ {x | dot φ x = 0})) := fun φ hφ =>
    even_finrank_fixOf_N spForm_isAlt spForm_nondegenerate ρ hiso hφ
  have hp1 : ∀ x : Z3, x ≠ 0 → Even (finrank K (fixOf ρ {x})) := fun x hx =>
    even_finrank_fixOf_single spForm_isAlt spForm_nondegenerate ρ hiso hx
  have hcov := cover ρ hfaith hpN hp1
  refine eq_bot_iff.2 fun g hg => ?_
  rw [Subgroup.mem_bot]
  obtain ⟨A, rfl⟩ := exists_spInnerLift_eq hK hr g
  have hgood : ∀ x' : Z3, GoodElt ρ x' → fixOf ρ {x'} ≤
      LinearMap.eqLocus (spEnd A) LinearMap.id := by
    intro x' hx'
    obtain ⟨hx0, hdim, y', u, hu, hyu⟩ := hx'
    set z : StatedSp r K := ((e.symm (Multiplicative.ofAdd x') : Dh) : StatedSp r K) with hz
    set y : StatedSp r K := ((e.symm (Multiplicative.ofAdd y') : Dh) : StatedSp r K) with hy
    have hzD : z ∈ Dh := (e.symm (Multiplicative.ofAdd x')).2
    have hyD : y ∈ Dh := (e.symm (Multiplicative.ofAdd y')).2
    have hz1 : z ≠ 1 := fun h => hx0 (hfaith x' (by rw [hact, ← hz, h, spEnd_one]))
    have hxu : spEnd z u = u := hu x' rfl
    have hyu' : spEnd y u ≠ u := hyu
    have hker : fixOf ρ {x'} = LinearMap.ker (spEnd z - 1) := by
      ext v
      rw [mem_fixOf, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
      exact ⟨fun h => h x' rfl, fun h x hx => by rw [Set.mem_singleton_iff] at hx; rw [hx]; exact h⟩
    have hdim' : 4 ≤ spFixedDim z := by
      rw [spFixedDim_eq_finrank_ker, ← hker]; exact hdim
    have blocks := spBlocks_three_two hK hr (hDh3 z hzD) hz1
    have hcomm := commute_layer_of_good hK hr hH hg (hDh3 z hzD) hz1 ((hmemDh z).1 hzD) hdim'
      (hDhcomm y hyD z hzD) (hDh3 y hyD) hxu hyu'
    have hAcomm : ∀ t ∈ ⁅spFixedFactor z, spFixedFactor z⁆, A * t = t * A := fun t ht => by
      apply hιinj
      rw [map_mul, map_mul]
      exact hcomm t ht
    have hW : ((spForm r K).restrict (LinearMap.ker (spEnd z - 1))).Nondegenerate := by
      have := blocks.fixed_nondegenerate
      rwa [blocks.fixed_eq] at this
    have h3 : 3 ≤ finrank K (LinearMap.ker (spEnd z - 1)) := by rw [← hker]; omega
    intro v hv
    rw [hker] at hv
    exact spEnd_eq_of_commute hK hAcomm hW h3 (mem_ker_sub_one_iff.1 hv)
  have hall : ∀ v, spEnd A v = v := fun v => by
    have : v ∈ ⨆ x ∈ {x | GoodElt ρ x}, fixOf ρ {x} := hcov Submodule.mem_top
    have hle : (⨆ x ∈ {x | GoodElt ρ x}, fixOf ρ {x}) ≤ LinearMap.eqLocus (spEnd A) LinearMap.id :=
      iSup₂_le fun x hx => hgood x hx
    exact hle this
  have hA1 : A = 1 := by
    rw [← spEnd_eq_one_iff]
    exact LinearMap.ext hall
  rw [hA1, map_one]

end Main

end CFSG.HardMathSupport.Timmesfeld.CrossChar
