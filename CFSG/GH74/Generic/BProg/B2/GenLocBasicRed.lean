module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.Generic.BProg.B2.WeakSigGen
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 Subgroup

namespace GenLocBasic

section EA

variable {A : Type} [Group A]

theorem isEA_subgroup (hA : CFSG.IsElementaryAbelian 2 A) (E : Subgroup A) :
    CFSG.IsElementaryAbelian 2 ↥E := by
  have := hA
  refine WeakSigGen.isElementaryAbelian_of_forall (G := A) (fun u _ v _ => mul_comm' u v)
    (fun u _ => WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA u)

theorem isEA_of_surjective {B : Type} [Group B] (hA : CFSG.IsElementaryAbelian 2 A) (π : A →* B)
    (hπ : Function.Surjective π) : CFSG.IsElementaryAbelian 2 B := by
  have := hA
  have hcomm : ∀ a b : B, a * b = b * a := by
    intro a b
    obtain ⟨a', rfl⟩ := hπ a
    obtain ⟨b', rfl⟩ := hπ b
    rw [← map_mul, ← map_mul, mul_comm' a' b']
  have : IsMulCommutative B := ⟨⟨hcomm⟩⟩
  refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_of_forall_pow_eq_one fun b => ?_
  obtain ⟨b', rfl⟩ := hπ b
  rw [← map_pow, sq, WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA b', map_one]

theorem card_eq_two_pow_pRank_type {G : Type} [Group G] [Finite G]
    (hG : CFSG.IsElementaryAbelian 2 G) : Nat.card G = 2 ^ pRank 2 G := by
  have := hG
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 (CFSG.IsElementaryAbelian.isPGroup 2 G)
  rw [hk, CFSG.pRank_eq_of_card_eq_pow one_lt_two hk]

theorem adm_iff_index [Finite A] (hA : CFSG.IsElementaryAbelian 2 A) (E : Subgroup A) :
    pRank 2 A - 1 ≤ pRank 2 ↥E ↔ E.index ≤ 2 := by
  have hE := isEA_subgroup hA E
  have h1 := card_eq_two_pow_pRank_type hA
  have h2 := card_eq_two_pow_pRank_type hE
  have h3 := Subgroup.card_mul_index E
  rw [h1, h2] at h3
  have hpos : 0 < 2 ^ pRank 2 ↥E := by positivity
  constructor
  · intro h
    have h4 : 2 ^ pRank 2 A ≤ 2 ^ (pRank 2 ↥E + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_succ, ← h3] at h4
    exact Nat.le_of_mul_le_mul_left (by linarith) hpos
  · intro h
    have h4 : 2 ^ pRank 2 A ≤ 2 ^ (pRank 2 ↥E + 1) := by
      rw [pow_succ, ← h3]
      exact Nat.mul_le_mul_left _ h
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h4
    omega

end EA

section Fix

variable {J : Type} [Group J] {A : Type} [Group A]

theorem mem_fixedIn_map (α : A →* MulAut J) (E : Subgroup A) (x : J) :
    x ∈ fixedIn J (E.map α) ↔ ∀ a ∈ E, α a x = x := by
  constructor
  · intro h a ha
    exact h (α a) (mem_map_of_mem α ha)
  · intro h φ hφ
    obtain ⟨a, ha, rfl⟩ := mem_map.1 hφ
    exact h a ha

end Fix

end GenLocBasic

section G1

variable {J : Type} [Group J] {A : Type} [Group A]

theorem le_gammaAct (α : A →* MulAut J) {E : Subgroup A} (hE : pRank 2 A - 1 ≤ pRank 2 ↥E) :
    fixedIn J (E.map α) ≤ gammaAct α :=
  le_iSup₂_of_le E hE le_rfl

theorem gammaAct_eq_top_of_le_ker (α : A →* MulAut J) {E : Subgroup A}
    (hE : pRank 2 A - 1 ≤ pRank 2 ↥E) (hker : E ≤ α.ker) : gammaAct α = ⊤ := by
  refine eq_top_iff.2 (le_trans ?_ (le_gammaAct α hE))
  intro x _ φ hφ
  obtain ⟨a, ha, rfl⟩ := mem_map.1 hφ
  rw [MonoidHom.mem_ker.1 (hker ha)]
  rfl

end G1

namespace GenLocBasic

section Surj

variable {J : Type} [Group J] {A : Type} [Group A] {B : Type} [Group B]

theorem adm_map [Finite A] (hA : CFSG.IsElementaryAbelian 2 A) (π : A →* B)
    (hπ : Function.Surjective π) {E : Subgroup A} (hE : pRank 2 A - 1 ≤ pRank 2 ↥E) :
    pRank 2 B - 1 ≤ pRank 2 ↥(E.map π) := by
  have hB := isEA_of_surjective hA π hπ
  have : Finite B := Finite.of_surjective π hπ
  rw [adm_iff_index hA] at hE
  rw [adm_iff_index hB]
  have hne : E.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) (Subgroup.index_map_dvd E hπ)).trans hE

theorem adm_comap [Finite A] (hA : CFSG.IsElementaryAbelian 2 A) (π : A →* B)
    (hπ : Function.Surjective π) {E' : Subgroup B} (hE' : pRank 2 B - 1 ≤ pRank 2 ↥E') :
    pRank 2 A - 1 ≤ pRank 2 ↥(E'.comap π) := by
  have hB := isEA_of_surjective hA π hπ
  have : Finite B := Finite.of_surjective π hπ
  rw [adm_iff_index hB] at hE'
  rw [adm_iff_index hA, Subgroup.index_comap_of_surjective E' hπ]
  exact hE'

theorem gammaAct_comp_surj [Finite A] (hA : CFSG.IsElementaryAbelian 2 A) (β : B →* MulAut J)
    (π : A →* B) (hπ : Function.Surjective π) : gammaAct (β.comp π) = gammaAct β := by
  refine le_antisymm (iSup₂_le fun E hE => ?_) (iSup₂_le fun E' hE' => ?_)
  · rw [← Subgroup.map_map]
    exact le_gammaAct β (adm_map hA π hπ hE)
  · have := le_gammaAct (β.comp π) (adm_comap hA π hπ hE')
    rwa [← Subgroup.map_map, Subgroup.map_comap_eq_self_of_surjective hπ] at this

theorem locE1_comp_surj [Finite A] (hA : CFSG.IsElementaryAbelian 2 A) (β : B →* MulAut J)
    (π : A →* B) (hπ : Function.Surjective π) : LocE1 (β.comp π) ↔ LocE1 β := by
  constructor
  · intro h E' hE'
    have := h _ (adm_comap hA π hπ hE')
    rwa [← Subgroup.map_map, Subgroup.map_comap_eq_self_of_surjective hπ] at this
  · intro h E hE
    rw [← Subgroup.map_map]
    exact h _ (adm_map hA π hπ hE)

theorem locE2_comp_surj [Finite A] (hA : CFSG.IsElementaryAbelian 2 A) (β : B →* MulAut J)
    (π : A →* B) (hπ : Function.Surjective π) : LocE2 (β.comp π) ↔ LocE2 β := by
  unfold LocE2
  rw [gammaAct_comp_surj hA β π hπ]

theorem locE3_comp_surj [Finite A] (hA : CFSG.IsElementaryAbelian 2 A) (β : B →* MulAut J)
    (π : A →* B) (hπ : Function.Surjective π) : LocE3 (β.comp π) ↔ LocE3 β := by
  constructor
  · rintro ⟨E, hE, x, hx, h2, hc⟩
    refine ⟨E.map π, adm_map hA π hπ hE, x, ?_, h2, hc⟩
    rwa [← Subgroup.map_map] at hx
  · rintro ⟨E', hE', x, hx, h2, hc⟩
    refine ⟨E'.comap π, adm_comap hA π hπ hE', x, ?_, h2, hc⟩
    rwa [← Subgroup.map_map, Subgroup.map_comap_eq_self_of_surjective hπ]

end Surj

section Equiv

variable {J : Type} [Group J] {A' : Type} [Group A'] {A : Type} [Group A]

theorem pRank_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) : pRank 2 X = pRank 2 Y := by
  have key : ∀ {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (r : ℕ),
      (∃ B : Subgroup X, CFSG.IsElementaryAbelian 2 ↥B ∧ Nat.card ↥B = 2 ^ r) →
        ∃ B : Subgroup Y, CFSG.IsElementaryAbelian 2 ↥B ∧ Nat.card ↥B = 2 ^ r := by
    intro X Y _ _ e r ⟨B, hB, hc⟩
    refine ⟨B.map e.toMonoidHom, isEA_of_surjective hB (e.toMonoidHom.subgroupMap B)
      (MonoidHom.subgroupMap_surjective _ B), ?_⟩
    rw [Subgroup.card_map_of_injective e.injective, hc]
  unfold pRank
  congr 1
  ext r
  exact ⟨key e r, key e.symm r⟩

theorem pRank_map_equiv (ι : A' ≃* A) (E' : Subgroup A') :
    pRank 2 ↥(E'.map ι.toMonoidHom) = pRank 2 ↥E' :=
  (pRank_congr (ι.subgroupMap E')).symm

theorem adm_map_equiv (ι : A' ≃* A) (E' : Subgroup A') :
    pRank 2 A - 1 ≤ pRank 2 ↥(E'.map ι.toMonoidHom) ↔ pRank 2 A' - 1 ≤ pRank 2 ↥E' := by
  rw [pRank_map_equiv, pRank_congr ι]

theorem gammaAct_comp_equiv (β : A →* MulAut J) (ι : A' ≃* A) :
    gammaAct (β.comp ι.toMonoidHom) = gammaAct β := by
  refine le_antisymm (iSup₂_le fun E' hE' => ?_) (iSup₂_le fun E hE => ?_)
  · rw [← Subgroup.map_map]
    exact le_gammaAct β ((adm_map_equiv ι E').2 hE')
  · have hE' : pRank 2 A' - 1 ≤ pRank 2 ↥(E.comap ι.toMonoidHom) := by
      rw [← adm_map_equiv ι, Subgroup.map_comap_eq_self_of_surjective ι.surjective]
      exact hE
    have := le_gammaAct (β.comp ι.toMonoidHom) hE'
    rwa [← Subgroup.map_map, Subgroup.map_comap_eq_self_of_surjective ι.surjective] at this

theorem locE1_comp_equiv (β : A →* MulAut J) (ι : A' ≃* A) :
    LocE1 (β.comp ι.toMonoidHom) ↔ LocE1 β := by
  constructor
  · intro h E hE
    have hE' : pRank 2 A' - 1 ≤ pRank 2 ↥(E.comap ι.toMonoidHom) := by
      rw [← adm_map_equiv ι, Subgroup.map_comap_eq_self_of_surjective ι.surjective]
      exact hE
    have := h _ hE'
    rwa [← Subgroup.map_map, Subgroup.map_comap_eq_self_of_surjective ι.surjective] at this
  · intro h E' hE'
    rw [← Subgroup.map_map]
    exact h _ ((adm_map_equiv ι E').2 hE')

theorem locE2_comp_equiv (β : A →* MulAut J) (ι : A' ≃* A) :
    LocE2 (β.comp ι.toMonoidHom) ↔ LocE2 β := by
  unfold LocE2
  rw [gammaAct_comp_equiv β ι]

theorem locE3_comp_equiv (β : A →* MulAut J) (ι : A' ≃* A) :
    LocE3 (β.comp ι.toMonoidHom) ↔ LocE3 β := by
  constructor
  · rintro ⟨E', hE', x, hx, h2, hc⟩
    refine ⟨E'.map ι.toMonoidHom, (adm_map_equiv ι E').2 hE', x, ?_, h2, hc⟩
    rwa [← Subgroup.map_map] at hx
  · rintro ⟨E, hE, x, hx, h2, hc⟩
    have hE' : pRank 2 A' - 1 ≤ pRank 2 ↥(E.comap ι.toMonoidHom) := by
      rw [← adm_map_equiv ι, Subgroup.map_comap_eq_self_of_surjective ι.surjective]
      exact hE
    refine ⟨E.comap ι.toMonoidHom, hE', x, ?_, h2, hc⟩
    rwa [← Subgroup.map_map, Subgroup.map_comap_eq_self_of_surjective ι.surjective]

end Equiv

section Transport

variable {J J' : Type} [Group J] [Group J'] {A : Type} [Group A]

theorem noOddNormal_map (e : J ≃* J') {S : Subgroup J} (h : NoOddNormal S) :
    NoOddNormal (S.map e.toMonoidHom) := by
  intro N hN hodd hnorm
  have hN' : N.map e.symm.toMonoidHom ≤ S := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hN hy
    simpa using hx
  have hodd' : Odd (Nat.card ↥(N.map e.symm.toMonoidHom)) := by
    rwa [Subgroup.card_map_of_injective e.symm.injective]
  have hnorm' : ∀ x ∈ S, x ∈ normalizer ((N.map e.symm.toMonoidHom : Subgroup J) : Set J) := by
    intro x hx
    have h1 := hnorm (e x) (mem_map_of_mem _ hx)
    have h2 := Subgroup.map_equiv_normalizer_eq (N.map e.symm.toMonoidHom) e
    have h3 : (N.map e.symm.toMonoidHom).map e.toMonoidHom = N := by
      rw [Subgroup.map_map]
      convert Subgroup.map_id N
      ext y
      simp
    rw [h3] at h2
    have h4 : e x ∈ (normalizer ((N.map e.symm.toMonoidHom : Subgroup J) : Set J)).map e.toMonoidHom := by
      rw [h2]; exact h1
    obtain ⟨x', hx', hx''⟩ := h4
    have : x' = x := e.injective hx''
    rwa [← this]
  have h5 := h _ hN' hodd' hnorm'
  rw [eq_bot_iff]
  intro y hy
  have : e.symm y ∈ N.map e.symm.toMonoidHom := mem_map_of_mem _ hy
  rw [h5, mem_bot] at this
  have h6 : y = 1 := by simpa using congrArg e this
  rw [h6]
  exact one_mem _

theorem noOddNormal_map_equiv (e : J ≃* J') (S : Subgroup J) :
    NoOddNormal (S.map e.toMonoidHom) ↔ NoOddNormal S := by
  refine ⟨fun h => ?_, noOddNormal_map e⟩
  have := noOddNormal_map e.symm h
  convert this using 1
  rw [Subgroup.map_map]
  convert (Subgroup.map_id S).symm
  ext y
  simp

theorem fixedIn_map_equiv (e : J ≃* J') (α : A →* MulAut J) (α' : A →* MulAut J')
    (hc : ∀ a x, α' a (e x) = e (α a x)) (E : Subgroup A) :
    fixedIn J' (E.map α') = (fixedIn J (E.map α)).map e.toMonoidHom := by
  ext y
  rw [mem_map_equiv, mem_fixedIn_map, mem_fixedIn_map]
  refine forall_congr' fun a => forall_congr' fun _ => ?_
  have h1 : α' a y = e (α a (e.symm y)) := by simpa using hc a (e.symm y)
  rw [h1]
  constructor
  · intro h
    exact e.injective (by simpa using h)
  · intro h
    rw [h]
    simp

theorem gammaAct_map_equiv (e : J ≃* J') (α : A →* MulAut J) (α' : A →* MulAut J')
    (hc : ∀ a x, α' a (e x) = e (α a x)) :
    gammaAct α' = (gammaAct α).map e.toMonoidHom := by
  simp only [gammaAct, fixedIn_map_equiv e α α' hc, Subgroup.map_iSup]

theorem locE1_map_equiv (e : J ≃* J') (α : A →* MulAut J) (α' : A →* MulAut J')
    (hc : ∀ a x, α' a (e x) = e (α a x)) : LocE1 α' ↔ LocE1 α := by
  unfold LocE1
  refine forall_congr' fun E => forall_congr' fun _ => ?_
  rw [fixedIn_map_equiv e α α' hc E, noOddNormal_map_equiv]

theorem noOddFix_map_equiv (e : J ≃* J') (G0 : Subgroup J) :
    (∀ φ : MulAut J', Odd (orderOf φ) → (∀ x ∈ G0.map e.toMonoidHom, φ x = x) → φ = 1) ↔
      (∀ φ : MulAut J, Odd (orderOf φ) → (∀ x ∈ G0, φ x = x) → φ = 1) := by
  constructor
  · intro h φ hφ hfix
    have h1 := h (MulAut.congr e φ) (by rwa [MulEquiv.orderOf_eq]) (by
      rintro _ ⟨x, hx, rfl⟩
      have := hfix x hx
      simp [MulAut.congr_apply, this])
    exact (MulAut.congr e).injective (h1.trans (map_one _).symm)
  · intro h φ' hφ' hfix
    have h1 := h ((MulAut.congr e).symm φ') (by rwa [MulEquiv.orderOf_eq]) (by
      intro x hx
      have := hfix (e x) (mem_map_of_mem _ hx)
      simp [MulAut.congr_symm_apply, this])
    exact (MulAut.congr e).symm.injective (h1.trans (map_one _).symm)

theorem locE2_map_equiv (e : J ≃* J') (α : A →* MulAut J) (α' : A →* MulAut J')
    (hc : ∀ a x, α' a (e x) = e (α a x)) : LocE2 α' ↔ LocE2 α := by
  unfold LocE2
  rw [gammaAct_map_equiv e α α' hc]
  exact noOddFix_map_equiv e _

theorem locE3_map_equiv (e : J ≃* J') (α : A →* MulAut J) (α' : A →* MulAut J')
    (hc : ∀ a x, α' a (e x) = e (α a x)) : LocE3 α' ↔ LocE3 α := by
  have key : ∀ x : J, ((∃ n : ℕ, (e x) ^ (2 ^ n) = 1) ∧ ∃ y : J', y * e x ≠ e x * y) ↔
      ((∃ n : ℕ, x ^ (2 ^ n) = 1) ∧ ∃ y : J, y * x ≠ x * y) := by
    intro x
    constructor
    · rintro ⟨⟨n, hn⟩, y, hy⟩
      refine ⟨⟨n, e.injective (by rw [map_pow, hn, map_one])⟩, e.symm y, fun h => hy ?_⟩
      have := congrArg e h
      simpa using this
    · rintro ⟨⟨n, hn⟩, y, hy⟩
      refine ⟨⟨n, by rw [← map_pow, hn, map_one]⟩, e y, fun h => hy (e.injective ?_)⟩
      simpa using h
  constructor
  · rintro ⟨E, hE, x', hx', h2⟩
    rw [fixedIn_map_equiv e α α' hc E, mem_map_equiv] at hx'
    refine ⟨E, hE, e.symm x', hx', ?_⟩
    rw [← key]
    simpa using h2
  · rintro ⟨E, hE, x, hx, h2⟩
    refine ⟨E, hE, e x, ?_, (key x).2 h2⟩
    rw [fixedIn_map_equiv e α α' hc E]
    exact mem_map_of_mem _ hx

end Transport

end GenLocBasic

section G2

variable {J : Type} [Group J]

theorem GenLoc.of_mulEquiv {J' : Type} [Group J'] (e : J ≃* J') (h : GenLoc J) : GenLoc J' := by
  intro A _ _ α' hA
  let α : A →* MulAut J := (MulAut.congr e.symm).toMonoidHom.comp α'
  have hc : ∀ a x, α' a (e x) = e (α a x) := by
    intro a x
    simp [α, MulAut.congr_apply]
  rcases h A α hA with hg | ⟨h1, h2, h3⟩
  · left
    rw [GenLocBasic.gammaAct_map_equiv e α α' hc, hg, Subgroup.map_top_of_surjective _ e.surjective]
  · right
    exact ⟨(GenLocBasic.locE1_map_equiv e α α' hc).2 h1, (GenLocBasic.locE2_map_equiv e α α' hc).2 h2,
      (GenLocBasic.locE3_map_equiv e α α' hc).2 h3⟩

end G2

section G3

variable {J : Type} [Group J] {A : Type} [Group A]

@[expose] def GenLocSub (J : Type) [Group J] : Prop :=
  ∀ D : Subgroup (MulAut J), IsRank23 ↥D →
    gammaAct D.subtype = ⊤ ∨ (LocE1 D.subtype ∧ LocE2 D.subtype ∧ LocE3 D.subtype)

theorem range_reduction [Finite A] (α : A →* MulAut J) (hA : IsRank23 A)
    (hker : ∀ E : Subgroup A, pRank 2 A - 1 ≤ pRank 2 ↥E → ¬ E ≤ α.ker) :
    IsRank23 ↥α.range ∧ gammaAct α = gammaAct α.range.subtype ∧
      (LocE1 α ↔ LocE1 α.range.subtype) ∧ (LocE2 α ↔ LocE2 α.range.subtype) ∧
      (LocE3 α ↔ LocE3 α.range.subtype) := by
  have hsurj := α.rangeRestrict_surjective
  have hcomp : α.range.subtype.comp α.rangeRestrict = α := MonoidHom.ext fun _ => rfl
  have hEA := hA.1
  have hR : CFSG.IsElementaryAbelian 2 ↥α.range :=
    GenLocBasic.isEA_of_surjective hEA α.rangeRestrict hsurj
  have : Finite ↥α.range := Finite.of_surjective _ hsurj
  refine ⟨⟨hR, ?_⟩, ?_, ?_, ?_, ?_⟩
  · have h1 := GenLocBasic.card_eq_two_pow_pRank_type hR
    have h2 := GenLocBasic.card_eq_two_pow_pRank_type hEA
    have h3 : ¬ (pRank 2 A - 1 ≤ pRank 2 ↥α.ker) := fun h => hker α.ker h le_rfl
    rw [GenLocBasic.adm_iff_index hEA, Subgroup.index_ker, h1] at h3
    have h4 : Nat.card ↥α.range ≤ Nat.card A := Nat.card_le_card_of_surjective _ hsurj
    have hr2 : 2 ≤ pRank 2 ↥α.range := by
      by_contra hlt
      apply h3
      calc 2 ^ pRank 2 ↥α.range ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 := by norm_num
    have hr3 : pRank 2 ↥α.range ≤ pRank 2 A := by
      rw [h1, h2] at h4
      exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h4
    have := hA.2
    omega
  · have := GenLocBasic.gammaAct_comp_surj hEA α.range.subtype α.rangeRestrict hsurj
    rwa [hcomp] at this
  · have := GenLocBasic.locE1_comp_surj hEA α.range.subtype α.rangeRestrict hsurj
    rwa [hcomp] at this
  · have := GenLocBasic.locE2_comp_surj hEA α.range.subtype α.rangeRestrict hsurj
    rwa [hcomp] at this
  · have := GenLocBasic.locE3_comp_surj hEA α.range.subtype α.rangeRestrict hsurj
    rwa [hcomp] at this

namespace GenLocBasic

@[expose] def GenOrLocSub {J : Type} [Group J] (D : Subgroup (MulAut J)) : Prop :=
  gammaAct D.subtype = ⊤ ∨ (LocE1 D.subtype ∧ LocE2 D.subtype ∧ LocE3 D.subtype)

theorem genOrLocSub_of_conj {J : Type} [Group J] {D : Subgroup (MulAut J)} (β : MulAut J)
    (h : GenOrLocSub (D.map (MulAut.conj β).toMonoidHom)) : GenOrLocSub D := by
  let c : MulAut J →* MulAut J := (MulAut.conj β).toMonoidHom
  have hc_inj : Function.Injective c := (MulAut.conj β).injective
  let ι : ↥D ≃* ↥(D.map c) := D.equivMapOfInjective c hc_inj
  let α'' : ↥D →* MulAut J := (D.map c).subtype.comp ι.toMonoidHom
  have hc : ∀ (d : ↥D) (x : J), α'' d (β x) = β (D.subtype d x) := by
    intro d x
    change (β * (d : MulAut J) * β⁻¹) (β x) = β ((d : MulAut J) x)
    simp
  have hg := gammaAct_map_equiv β D.subtype α'' hc
  have hg' := gammaAct_comp_equiv (D.map c).subtype ι
  rcases h with h | ⟨h1, h2, h3⟩
  · left
    have h4 : (gammaAct D.subtype).map (β : J ≃* J).toMonoidHom = ⊤ := by
      rw [← hg]
      exact hg'.trans h
    have h5 := Subgroup.comap_map_eq_self_of_injective (f := (β : J ≃* J).toMonoidHom) (β : J ≃* J).injective
      (gammaAct D.subtype)
    rw [h4, Subgroup.comap_top] at h5
    exact h5.symm
  · right
    refine ⟨(locE1_map_equiv β D.subtype α'' hc).1 ((locE1_comp_equiv _ ι).2 h1),
      (locE2_map_equiv β D.subtype α'' hc).1 ((locE2_comp_equiv _ ι).2 h2),
      (locE3_map_equiv β D.subtype α'' hc).1 ((locE3_comp_equiv _ ι).2 h3)⟩

end GenLocBasic

theorem genLocSub_of_conj (h : ∀ D : Subgroup (MulAut J), IsRank23 ↥D → ∃ β : MulAut J,
    gammaAct (D.map (MulAut.conj β).toMonoidHom).subtype = ⊤ ∨
      (LocE1 (D.map (MulAut.conj β).toMonoidHom).subtype ∧
        LocE2 (D.map (MulAut.conj β).toMonoidHom).subtype ∧
        LocE3 (D.map (MulAut.conj β).toMonoidHom).subtype)) : GenLocSub J := by
  intro D hD
  obtain ⟨β, hβ⟩ := h D hD
  exact GenLocBasic.genOrLocSub_of_conj β hβ

theorem genLoc_of_genLocSub [Finite J] (h : GenLocSub J) : GenLoc J := by
  intro A _ _ α hA
  by_cases hex : ∃ E : Subgroup A, pRank 2 A - 1 ≤ pRank 2 ↥E ∧ E ≤ α.ker
  · obtain ⟨E, hE, hk⟩ := hex
    exact Or.inl (gammaAct_eq_top_of_le_ker α hE hk)
  · simp only [not_exists, not_and] at hex
    obtain ⟨hR, hg, h1, h2, h3⟩ := range_reduction α hA hex
    rcases h α.range hR with hgen | ⟨l1, l2, l3⟩
    · exact Or.inl (hg.trans hgen)
    · exact Or.inr ⟨h1.2 l1, h2.2 l2, h3.2 l3⟩

end G3

end CFSG.GH74.Generic.BProg.B2
