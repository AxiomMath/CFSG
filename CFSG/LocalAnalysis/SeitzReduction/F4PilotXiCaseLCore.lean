module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiCaseLM2
public import CFSG.RankThree.Chevalley.EvenPinnedRootSL2
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiCaseLTorus

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Quasithin (perfectCore perfectCore_mono le_perfectCore_of_perfect perfectCore_le
  perfectCore_perfect)

local instance f4PilotXiCaseLCoreNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

local instance f4PilotXiCaseLCoreNeZeroE6 : NeZero Tag.E6.rank := ⟨by decide⟩

theorem odd_ordF4_oddPart {f : ℕ} (hf : 1 ≤ f) :
    Odd (((2 ^ f) ^ 12 - 1) * ((2 ^ f) ^ 8 - 1) * ((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1)) :=
  (((odd_two_pow_pow_sub_one hf (by norm_num)).mul (odd_two_pow_pow_sub_one hf (by norm_num))).mul
    (odd_two_pow_pow_sub_one hf (by norm_num))).mul (odd_two_pow_pow_sub_one hf (by norm_num))

section Sylow

variable {k : Type} [Field k]

theorem natCard_adjointGroup_F4_eq [Finite k] {f : ℕ} (hk : Nat.card k = 2 ^ f) :
    Nat.card (adjointGroup .F4 k) = 2 ^ (24 * f) *
      (((2 ^ f) ^ 12 - 1) * ((2 ^ f) ^ 8 - 1) * ((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1)) := by
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4, hk, CFSG.Open.ordF4, ← pow_mul,
    mul_comm f 24]
  ring

theorem factorization_natCard_adjointGroup_F4 [Finite k] {f : ℕ} (hf : 1 ≤ f)
    (hk : Nat.card k = 2 ^ f) : (Nat.card (adjointGroup .F4 k)).factorization 2 = 24 * f := by
  rw [natCard_adjointGroup_F4_eq hk]
  have hR := odd_ordF4_oddPart hf
  rw [Nat.factorization_mul (by positivity) hR.pos.ne', Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (fun h => by
      have := Nat.odd_iff.1 hR
      omega), add_zero]

@[expose] noncomputable def sylowOfCardF4 [Finite k] {f : ℕ} (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (P : Subgroup (adjointGroup .F4 k)) (hP : Nat.card P = 2 ^ (24 * f)) :
    Sylow 2 (adjointGroup .F4 k) :=
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (adjointGroup .F4 k) := Finite.of_injective _ Subtype.val_injective
  Sylow.ofCard P (by rw [hP, factorization_natCard_adjointGroup_F4 hf hk])

theorem coe_sylowOfCardF4 [Finite k] {f : ℕ} (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (P : Subgroup (adjointGroup .F4 k)) (hP : Nat.card P = 2 ^ (24 * f)) :
    (sylowOfCardF4 hf hk P hP : Subgroup (adjointGroup .F4 k)) = P :=
  rfl

end Sylow

section Transport

variable {k : Type} [Field k]

theorem exists_conj_leviTorus_of_injective {H : Type*} [Group H] [Finite k] [CharP k 2] {f : ℕ}
    (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f) {β : H →* adjointGroup .F4 k}
    (hβ : Function.Injective β) {U : Subgroup H} (hU : Nat.card U = 2 ^ (24 * f)) {w : H}
    (hwU : w ∈ centralizer (U : Set H)) (hw1 : w ≠ 1) {Λ : Subgroup H}
    (hΛ : Λ ≤ centralizer ({w} : Set H))
    (hdiv : (2 ^ f) ^ 24 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 4 - 1) * ((2 ^ f) ^ 6 - 1)) ∣
      Nat.card Λ)
    {T : Subgroup H} (hTU : T ≤ normalizer (U : Set H)) (hTw : T ≤ centralizer ({w} : Set H))
    (hT : Odd (Nat.card T)) :
    ∃ (c : adjointGroup .F4 k) (i : Fin (Tag.rank .F4)) (a : k), (i = 1 ∨ i = 2) ∧ a ≠ 0 ∧
      ((c * β w * c⁻¹ : adjointGroup .F4 k) : ModGL .F4 k) = pinnedX .F4 k (Pi.single i 1) a ∧
      (∀ s ∈ T, ((c * β s * c⁻¹ : adjointGroup .F4 k) : ModGL .F4 k) ∈ leviTorus k {i}) ∧
      ∀ d : adjointGroup .F4 k, (d : ModGL .F4 k) ∈ leviTorus k {i} →
        c⁻¹ * d * c ∈ normalizer ((U.map β : Subgroup (adjointGroup .F4 k)) :
          Set (adjointGroup .F4 k)) := by
  have hUβ : Nat.card (U.map β) = 2 ^ (24 * f) := by
    rw [card_map_of_injective hβ, hU]
  set P := sylowOfCardF4 hf hk (U.map β) hUβ with hP
  have hPcoe : (P : Subgroup (adjointGroup .F4 k)) = U.map β := rfl
  have hx : β w ∈ centralizer ((P : Subgroup (adjointGroup .F4 k)) : Set (adjointGroup .F4 k)) := by
    rw [hPcoe, mem_centralizer_iff]
    rintro _ ⟨u, hu, rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_iff.1 hwU u hu]
  have hx1 : β w ≠ 1 := fun h => hw1 (hβ (h.trans (map_one β).symm))
  have hΛC : Λ.map β ≤ centralizer ({β w} : Set (adjointGroup .F4 k)) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      mem_centralizer_singleton_iff.1 (hΛ hy)]
  have htu : ∀ c : adjointGroup .F4 k, c * β w * c⁻¹ ≠ yRep k .tu := by
    intro c hc
    have h1 : Nat.card Λ ∣ Nat.card (centralizer ({β w} : Set (adjointGroup .F4 k))) := by
      rw [← card_map_of_injective hβ]
      exact Subgroup.card_dvd_of_le hΛC
    rw [← natCard_centralizer_conj c (β w), hc] at h1
    apply not_dvd_natCard_centralizer_yRep_tu hf hk hk (κ := .t) (by decide)
    rw [natCard_centralizer_yRep_of_ne_tu hf hk (by decide)]
    exact hdiv.trans h1
  have hSU : T.map β ≤ normalizer ((P : Subgroup (adjointGroup .F4 k)) :
      Set (adjointGroup .F4 k)) := by
    rintro _ ⟨s, hs, rfl⟩
    rw [hPcoe, mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨s * u * s⁻¹, (mem_normalizer_iff.1 (hTU hs) u).1 hu, ?_⟩
      rw [map_mul, map_mul, map_inv]
    · rintro ⟨u, hu, hu'⟩
      refine ⟨s⁻¹ * u * s, ?_, ?_⟩
      · have := (mem_normalizer_iff.1 (hTU hs) (s⁻¹ * u * s)).2
        rw [show s * (s⁻¹ * u * s) * s⁻¹ = u by group] at this
        exact this hu
      · rw [map_mul, map_mul, map_inv, hu']
        group
  have hSx : T.map β ≤ centralizer ({β w} : Set (adjointGroup .F4 k)) := by
    rintro _ ⟨s, hs, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      mem_centralizer_singleton_iff.1 (hTw hs)]
  have hSodd : Odd (Nat.card (T.map β)) := by
    rw [card_map_of_injective hβ]
    exact hT
  obtain ⟨c, i, a, hi, ha, hcx, hcS, hcN⟩ :=
    exists_conj_leviTorus_of_mem_centralizer_sylow P hx hx1 htu hSU hSx hSodd
  exact ⟨c, i, a, hi, ha, hcx, fun s hs => hcS (β s) ⟨s, hs, rfl⟩, hcN⟩

end Transport

section RootSL2

variable {k : Type} [Field k]

theorem natCard_leviTorus_singleton
    [Finite k] (i : Fin (Tag.rank .F4)) :
    Nat.card (leviTorus k {i}) = (Nat.card k - 1) ^ 3 := by
  rw [leviTorus, card_map_of_injective (fun a b h => rootDiagUnit_injective h)]
  have e : (Subgroup.pi ((({i} : Finset (Fin (Tag.rank .F4))) : Set (Fin (Tag.rank .F4))))
      fun _ => (⊥ : Subgroup kˣ)) ≃ ({j : Fin (Tag.rank .F4) // j ≠ i} → kˣ) :=
    { toFun := fun b j => b.1 j.1
      invFun := fun g => ⟨fun j => if h : j = i then 1 else g ⟨j, h⟩, fun j hj => by
        rw [Finset.coe_singleton, Set.mem_singleton_iff] at hj
        subst hj
        simp⟩
      left_inv := fun b => by
        apply Subtype.ext
        funext j
        by_cases h : j = i
        · subst h
          have hb : b.1 j = 1 := b.2 j (by simp)
          simp [hb]
        · simp [h]
      right_inv := fun g => by
        funext j
        simp [j.2] }
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_units]
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]
  rfl

theorem natCard_SL2_eq (F : Type) [Field F] [Finite F] :
    Nat.card (SL2 F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  classical
  have := Fintype.ofFinite F
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  change Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = _
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    Nat.card_eq_fintype_card, show Fintype.card F ^ 2 - Fintype.card F =
      Fintype.card F * (Fintype.card F - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
    Nat.mul_div_cancel _ (by omega), mul_comm]

theorem natCard_rootSubgroup_sup_neg [Finite k] [CharP k 2] {τ : Tag}
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    Nat.card (rootSubgroup τ k α ⊔ rootSubgroup τ k (-α) : Subgroup (ModGL τ k)) =
      Nat.card k * (Nat.card k ^ 2 - 1) := by
  obtain ⟨-, -, ⟨e, -⟩, -⟩ := CFSG.RankThree.Chevalley.even_Chevalley_pinned_root_SL2_maps τ k hα
  rw [← Nat.card_congr e.toEquiv]
  exact natCard_SL2_eq k

theorem pinnedX_mul_pinnedX_neg_ne [CharP k 2] {τ : Tag} {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) {a : k} (ha : a ≠ 0) :
    pinnedX τ k α a * pinnedX τ k (-α) 1 ≠ pinnedX τ k (-α) 1 * pinnedX τ k α a := by
  obtain ⟨hinj, -, -, hρ, -⟩ := CFSG.RankThree.Chevalley.even_Chevalley_pinned_root_SL2_maps τ k hα
  intro h
  rw [← (hρ a).1, ← (hρ 1).2, ← map_mul, ← map_mul] at h
  have h1 := congrArg (fun A : SL2 k => (A : Matrix (Fin 2) (Fin 2) k) 0 0) (hinj h)
  have e1 : ((uSL a * vSL 1 : SL2 k) : Matrix (Fin 2) (Fin 2) k) =
      !![1, a; 0, 1] * !![1, 0; 1, 1] := rfl
  have e2 : ((vSL 1 * uSL a : SL2 k) : Matrix (Fin 2) (Fin 2) k) =
      !![1, 0; 1, 1] * !![1, a; 0, 1] := rfl
  simp only [e1, e2] at h1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h1
  exact ha h1

end RootSL2

section Bounds

open CFSG.SeitzReduction.E6Pilot (corootTuple)

theorem commutator_subgroupOf_eq {X : Type*} [Group X] {H J : Subgroup X} (hHJ : H ≤ J)
    (hH : ⁅H, H⁆ = H) : ⁅H.subgroupOf J, H.subgroupOf J⁆ = H.subgroupOf J := by
  apply map_injective J.subtype_injective
  rw [map_commutator, subgroupOf_map_subtype, inf_of_le_left hHJ, hH]

theorem commutator_map_eq {X Y : Type*} [Group X] [Group Y] (φ : X →* Y) {H : Subgroup X}
    (hH : ⁅H, H⁆ = H) : ⁅H.map φ, H.map φ⁆ = H.map φ := by
  rw [← map_commutator, hH]

variable {k : Type} [Field k] [Finite k] [CharP k 2] {KC : Type} [Field KC] [Finite KC]
  {C J : Subgroup (ModGL TwistTag.E6.tag KC)}

theorem natCard_SL2_le_perfectCore_of_le_leviTorus (hq : 4 ≤ Nat.card k) (hJC : J ≤ C)
    (eJ : J ≃* adjointGroup .F4 k) {S : Subgroup (ModGL TwistTag.E6.tag KC)} (hSJ : S ≤ J)
    (c : adjointGroup .F4 k) (i : Fin (Tag.rank .F4))
    (hS : ∀ (s : ModGL TwistTag.E6.tag KC) (hs : s ∈ S),
      ((c * eJ ⟨s, hSJ hs⟩ * c⁻¹ : adjointGroup .F4 k) : ModGL .F4 k) ∈ leviTorus k {i}) :
    Nat.card (SL2 k) ≤
      Nat.card (perfectCore (C ⊓ centralizer (S : Set (ModGL TwistTag.E6.tag KC)))) := by
  have : Finite (ModGL TwistTag.E6.tag KC) := finite_modGL
  have : Finite (ModGL .F4 k) := finite_modGL
  set R₀ : Subgroup (ModGL .F4 k) := rootSpan .F4 k (amalgamRoots {i}) with hR₀
  have hR₀core := perfectCore_inf_centralizer_leviTorus hq (J := {i}) (by simp)
  have hR₀C : R₀ ≤ adjointGroup .F4 k ⊓ centralizer (leviTorus k {i} : Set (ModGL .F4 k)) := by
    rw [hR₀, ← hR₀core]
    exact perfectCore_le _
  have hR₀perf : ⁅R₀, R₀⁆ = R₀ := by
    rw [hR₀, ← hR₀core]
    exact perfectCore_perfect _
  set R₁ : Subgroup (adjointGroup .F4 k) :=
    (R₀.subgroupOf (adjointGroup .F4 k)).map (MulAut.conj c⁻¹).toMonoidHom with hR₁
  set R : Subgroup (ModGL TwistTag.E6.tag KC) := (R₁.map eJ.symm.toMonoidHom).map J.subtype
    with hR
  have hRperf : ⁅R, R⁆ = R := by
    rw [hR, hR₁]
    exact commutator_map_eq _ (commutator_map_eq _ (commutator_map_eq _
      (commutator_subgroupOf_eq (fun x hx => (hR₀C hx).1) hR₀perf)))
  have hRle : R ≤ C ⊓ centralizer (S : Set (ModGL TwistTag.E6.tag KC)) := by
    rintro _ ⟨_, ⟨_, ⟨ρ, hρ, rfl⟩, rfl⟩, rfl⟩
    refine mem_inf.2 ⟨hJC (eJ.symm _).2, mem_centralizer_iff.2 fun s hs => ?_⟩
    have hd := hS s hs
    have hρd : (ρ : ModGL .F4 k) * ((c * eJ ⟨s, hSJ hs⟩ * c⁻¹ : adjointGroup .F4 k) :
        ModGL .F4 k) = ((c * eJ ⟨s, hSJ hs⟩ * c⁻¹ : adjointGroup .F4 k) : ModGL .F4 k) * ρ :=
      (mem_centralizer_iff.1 (hR₀C (mem_subgroupOf.1 hρ)).2 _ hd).symm
    have hρd' : ρ * (c * eJ ⟨s, hSJ hs⟩ * c⁻¹) = c * eJ ⟨s, hSJ hs⟩ * c⁻¹ * ρ :=
      Subtype.ext hρd
    have hcomm : MulAut.conj c⁻¹ ρ * eJ ⟨s, hSJ hs⟩ = eJ ⟨s, hSJ hs⟩ * MulAut.conj c⁻¹ ρ := by
      simp only [MulAut.conj_apply, inv_inv]
      calc c⁻¹ * ρ * c * eJ ⟨s, hSJ hs⟩ = c⁻¹ * (ρ * (c * eJ ⟨s, hSJ hs⟩ * c⁻¹)) * c := by group
        _ = c⁻¹ * (c * eJ ⟨s, hSJ hs⟩ * c⁻¹ * ρ) * c := by rw [hρd']
        _ = eJ ⟨s, hSJ hs⟩ * (c⁻¹ * ρ * c) := by group
    have h1 : eJ.symm (MulAut.conj c⁻¹ ρ) * ⟨s, hSJ hs⟩ = ⟨s, hSJ hs⟩ * eJ.symm (MulAut.conj c⁻¹ ρ) := by
      apply eJ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hcomm]
    have h2 := congrArg Subtype.val h1
    simp only [Subgroup.coe_mul] at h2
    exact h2.symm
  have hRcore := le_perfectCore_of_perfect hRle hRperf
  have hRcard : Nat.card R = Nat.card (SL2 k) := by
    rw [hR, card_map_of_injective J.subtype_injective, card_map_of_injective eJ.symm.injective,
      hR₁, card_map_of_injective (MulAut.conj c⁻¹).injective,
      card_subgroupOf_of_le (fun x hx => (hR₀C hx).1), hR₀, rootSpan_amalgamRoots_singleton_F4,
      natCard_rootSubgroup_sup_neg (isRoot_single .F4 i), natCard_SL2_eq]
  rw [← hRcard]
  exact Subgroup.card_le_of_le hRcore

theorem natCard_perfectCore_le_natCard_SL2 (hq : 4 ≤ Nat.card k) (hJC : J ≤ C)
    (hCad : C ≤ adjointGroup TwistTag.E6.tag KC) (h2 : (2 : KC) = 0)
    (hfix : ∀ g ∈ C, diagramMap TwistTag.E6 KC * g * (diagramMap TwistTag.E6 KC)⁻¹ = g → g ∈ J)
    (eJ : J ≃* adjointGroup .F4 k) {A : Subgroup KCˣ} (hA : 3 ≤ Nat.card A)
    (hd : ∀ δ ∈ xiLPerpRoots, ∀ c ∈ A, ∃ hd : rootDiagUnit TwistTag.E6.tag (corootTuple δ c) ∈ J,
      (eJ ⟨_, hd⟩ : ModGL .F4 k) ∈ leviTorus k {1})
    {S : Subgroup (ModGL TwistTag.E6.tag KC)} (hSJ : S ≤ J) (c : adjointGroup .F4 k)
    (hS : ∀ d : adjointGroup .F4 k, (d : ModGL .F4 k) ∈ leviTorus k {1} →
      ∃ (s : ModGL TwistTag.E6.tag KC) (hs : s ∈ S), c * eJ ⟨s, hSJ hs⟩ * c⁻¹ = d) :
    Nat.card (perfectCore (C ⊓ centralizer (S : Set (ModGL TwistTag.E6.tag KC)))) ≤
      Nat.card (SL2 k) := by
  have : Finite (ModGL TwistTag.E6.tag KC) := finite_modGL
  have : Finite (ModGL .F4 k) := finite_modGL
  set P₀ := perfectCore (C ⊓ centralizer (S : Set (ModGL TwistTag.E6.tag KC))) with hP₀
  have hP₀perf : ⁅P₀, P₀⁆ = P₀ := perfectCore_perfect _
  have hP₀le : P₀ ≤ C ⊓ centralizer (S : Set (ModGL TwistTag.E6.tag KC)) := perfectCore_le _
  set j : J := eJ.symm c⁻¹ with hj
  have hjd : ∀ δ ∈ xiLPerpRoots, ∀ c₀ ∈ A, (j : ModGL TwistTag.E6.tag KC) *
      rootDiagUnit TwistTag.E6.tag (corootTuple δ c₀) * (j : ModGL TwistTag.E6.tag KC)⁻¹ ∈ S := by
    intro δ hδ c₀ hc₀
    obtain ⟨hdJ, hdT⟩ := hd δ hδ c₀ hc₀
    obtain ⟨s, hs, hcs⟩ := hS _ hdT
    have hs' : (⟨s, hSJ hs⟩ : J) = j * ⟨_, hdJ⟩ * j⁻¹ := by
      apply eJ.injective
      rw [map_mul, map_mul, map_inv, hj, MulEquiv.apply_symm_apply, ← hcs]
      group
    have := congrArg Subtype.val hs'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
    rw [← this]
    exact hs
  set H : Subgroup (ModGL TwistTag.E6.tag KC) :=
    P₀.map (MulAut.conj ((j : ModGL TwistTag.E6.tag KC)⁻¹)).toMonoidHom with hH
  have hHperf : ⁅H, H⁆ = H := commutator_map_eq _ hP₀perf
  have hHR : H ≤ rootSpan TwistTag.E6.tag KC
      (signedSimpleRoots ({3} : Set (Fin (Tag.rank .E6)))) := by
    have h := perfectCore_le_rootSpan_alpha4_of_forall_conj_eq hA (H := H) (by
      rintro _ ⟨p, hp, rfl⟩
      have hpC := (hP₀le hp).1
      refine ⟨hCad ?_, fun δ hδ c₀ hc₀ => ?_⟩
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        exact mul_mem (mul_mem (inv_mem (hJC j.2)) hpC) (hJC j.2)
      · have hpS := mem_centralizer_iff.1 (hP₀le hp).2 _ (hjd δ hδ c₀ hc₀)
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        set d := rootDiagUnit TwistTag.E6.tag (corootTuple δ c₀)
        set jj := (j : ModGL TwistTag.E6.tag KC)
        calc d * (jj⁻¹ * p * jj) * d⁻¹ =
            jj⁻¹ * ((jj * d * jj⁻¹) * p) * (jj * d * jj⁻¹)⁻¹ * jj := by group
          _ = jj⁻¹ * (p * (jj * d * jj⁻¹)) * (jj * d * jj⁻¹)⁻¹ * jj := by rw [hpS]
          _ = jj⁻¹ * p * jj := by group)
    exact (CFSG.Quasithin.perfectCore_eq_self_of_perfect hHperf).ge.trans h
  have hP₀J : P₀ ≤ J := by
    intro p hp
    have hpC := (hP₀le hp).1
    have hR := hHR ⟨p, hp, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hR
    have hC' : (j : ModGL TwistTag.E6.tag KC)⁻¹ * p * j ∈ C :=
      mul_mem (mul_mem (inv_mem (hJC j.2)) hpC) (hJC j.2)
    have hJ' := hfix _ hC' (diagramMap_conj_eq_of_mem_rootSpan_alpha4 h2 hR)
    have e : p = (j : ModGL TwistTag.E6.tag KC) * ((j : ModGL TwistTag.E6.tag KC)⁻¹ * p * j) *
        (j : ModGL TwistTag.E6.tag KC)⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem j.2 hJ') (inv_mem j.2)
  set P₁ : Subgroup (adjointGroup .F4 k) :=
    ((P₀.subgroupOf J).map eJ.toMonoidHom).map (MulAut.conj c).toMonoidHom with hP₁
  set P₂ : Subgroup (ModGL .F4 k) := P₁.map (adjointGroup .F4 k).subtype with hP₂
  have hP₂perf : ⁅P₂, P₂⁆ = P₂ := by
    rw [hP₂, hP₁]
    exact commutator_map_eq _ (commutator_map_eq _ (commutator_map_eq _
      (commutator_subgroupOf_eq hP₀J hP₀perf)))
  have hP₂le : P₂ ≤ adjointGroup .F4 k ⊓ centralizer (leviTorus k {1} : Set (ModGL .F4 k)) := by
    rintro _ ⟨_, ⟨_, ⟨p, hp, rfl⟩, rfl⟩, rfl⟩
    refine mem_inf.2 ⟨Subtype.prop _, mem_centralizer_iff.2 fun d hd => ?_⟩
    have hdC : d ∈ adjointGroup .F4 k := leviTorus_le_adjointGroup _ hd
    obtain ⟨s, hs, hcs⟩ := hS ⟨d, hdC⟩ hd
    have hps : (p : ModGL TwistTag.E6.tag KC) * s = s * p :=
      (mem_centralizer_iff.1 (hP₀le (mem_subgroupOf.1 hp)).2 s hs).symm
    have hps' : p * ⟨s, hSJ hs⟩ = ⟨s, hSJ hs⟩ * p := Subtype.ext hps
    have h1 : eJ p * eJ ⟨s, hSJ hs⟩ = eJ ⟨s, hSJ hs⟩ * eJ p := by
      rw [← map_mul, ← map_mul, hps']
    have h2 : (c * eJ ⟨s, hSJ hs⟩ * c⁻¹) * (c * eJ p * c⁻¹) =
        (c * eJ p * c⁻¹) * (c * eJ ⟨s, hSJ hs⟩ * c⁻¹) := by
      calc (c * eJ ⟨s, hSJ hs⟩ * c⁻¹) * (c * eJ p * c⁻¹) =
          c * (eJ ⟨s, hSJ hs⟩ * eJ p) * c⁻¹ := by group
        _ = c * (eJ p * eJ ⟨s, hSJ hs⟩) * c⁻¹ := by rw [h1]
        _ = (c * eJ p * c⁻¹) * (c * eJ ⟨s, hSJ hs⟩ * c⁻¹) := by group
    rw [hcs] at h2
    have h3 := congrArg Subtype.val h2
    simp only [Subgroup.coe_mul] at h3
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, coe_subtype]
    exact h3
  have hP₂core := le_perfectCore_of_perfect hP₂le hP₂perf
  rw [perfectCore_inf_centralizer_leviTorus hq (J := {1}) (by simp),
    rootSpan_amalgamRoots_singleton_F4] at hP₂core
  have hcard : Nat.card P₂ = Nat.card P₀ := by
    rw [hP₂, card_map_of_injective (adjointGroup .F4 k).subtype_injective, hP₁,
      card_map_of_injective (MulAut.conj c).injective, card_map_of_injective eJ.injective,
      card_subgroupOf_of_le hP₀J]
  rw [← hcard, natCard_SL2_eq,
    ← natCard_rootSubgroup_sup_neg (isRoot_single .F4 (1 : Fin (Tag.rank .F4)))]
  exact Subgroup.card_le_of_le hP₂core

end Bounds

end CFSG.SeitzReduction.F4Pilot
