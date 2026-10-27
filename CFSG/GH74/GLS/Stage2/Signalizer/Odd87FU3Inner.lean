module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU3Def
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU3Card
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CrossL3
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Orth3Mod
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitL3U3
public import CFSG.GH74.Generic.S3.L3Class
public import CFSG.GH74.KGroups.L3EpsUniInv

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Matrix Subgroup CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.KGroups.L3Eps.Uni CFSG.GH74.Generic.S3
  CFSG.RankThree.SubgroupLists
open scoped MatrixGroups commutatorElement

section SL2Inv

variable {F : Type} [Field F]

theorem sl2_eq_neg_one_of_sq (h2 : (2 : F) ≠ 0) (x : SL(2, F)) (hx : x * x = 1) (hx1 : x ≠ 1) :
    x = -1 := by
  obtain ⟨a, b, c, d, hxe⟩ : ∃ a b c d : F, (x : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hxm : (x : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) = 1 := by
    have := congrArg (fun y : SL(2, F) => (y : Matrix (Fin 2) (Fin 2) F)) hx
    simpa using this
  have hdet : a * d - b * c = 1 := by
    have := x.2
    rw [hxe, Matrix.det_fin_two_of] at this
    exact this
  rw [hxe] at hxm
  have e00 := congrFun (congrFun hxm 0) 0
  have e01 := congrFun (congrFun hxm 0) 1
  have e10 := congrFun (congrFun hxm 1) 0
  have e11 := congrFun (congrFun hxm 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  by_cases hs : a + d = 0
  · exfalso
    apply h2
    linear_combination -e00 - hdet + a * hs
  · have hb : b = 0 := by
      have : b * (a + d) = 0 := by linear_combination e01
      exact (mul_eq_zero.mp this).resolve_right hs
    have hc : c = 0 := by
      have : c * (a + d) = 0 := by linear_combination e10
      exact (mul_eq_zero.mp this).resolve_right hs
    subst hb hc
    have ha1 : a * a = 1 := by linear_combination e00
    have hd1 : d * d = 1 := by linear_combination e11
    have had : a * d = 1 := by linear_combination hdet
    rcases mul_self_eq_one_iff.mp ha1 with ha | ha <;> rcases mul_self_eq_one_iff.mp hd1 with hd | hd
    · exfalso
      apply hx1
      apply Subtype.ext
      rw [hxe, ha, hd]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    · exfalso
      rw [ha, hd] at had
      apply h2
      linear_combination -had
    · exfalso
      rw [ha, hd] at had
      apply h2
      linear_combination -had
    · apply Subtype.ext
      rw [hxe, ha, hd]
      ext i j
      fin_cases i <;> fin_cases j <;> simp

end SL2Inv

theorem exists_sl2_block {A : Type} [Group A] {K : Subgroup A} {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hf : 1 ≤ f) {F : Type} [Field F] [Finite F] (hF : Nat.card F = (ℓ ^ f) ^ 2)
    (e : ↥K ≃* StatedProj (StatedSU 3 (ℓ ^ f) F)) {s : A} (hsK : s ∈ K) (hs2 : s * s = 1) (hs1 : s ≠ 1) :
    ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀) (ι : SL(2, F₀) →* A), Nat.card F₀ = ℓ ^ f ∧
      (∀ g, ι g ∈ K ∧ ι g * s = s * ι g) ∧ ι (-1) = s := by
  classical
  have hud : UnitaryFieldData ℓ f F := ⟨hℓ, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP F ℓ := hud.charP
  have : Finite F := hud.finite
  set w : StatedProj (StatedSU 3 (ℓ ^ f) F) := e ⟨s, hsK⟩ with hw
  have hww : w * w = 1 := by
    rw [hw, ← map_mul]
    have : (⟨s, hsK⟩ : ↥K) * ⟨s, hsK⟩ = 1 := Subtype.ext hs2
    rw [this, map_one]
  have hw1 : w ≠ 1 := by
    intro h
    apply hs1
    have : (⟨s, hsK⟩ : ↥K) = 1 := e.injective (by rw [← hw, h, map_one])
    exact congrArg Subtype.val this
  have hw2 : orderOf w = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hww) hw1
  obtain ⟨Y, hYC, -, ⟨eY⟩, hwY⟩ := CFSG.ComponentClassification.HarrisLit.L3U3.psu_case hud hℓ2 hF hw2
  refine ⟨↥(LieType.Steinberg.fixedSubfield F ℓ f), inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩
  · exact K.subtype.comp (e.symm.toMonoidHom.comp (Y.subtype.comp eY.symm.toMonoidHom))
  · exact LieType.Steinberg.card_fixedSubfield hF
  · intro g
    refine ⟨(e.symm (eY.symm g : Y)).2, ?_⟩
    have hy : (eY.symm g : Y).1 ∈ centralizer ({w} : Set _) := hYC (eY.symm g).2
    have hcomm : (eY.symm g : Y).1 * w = w * (eY.symm g : Y).1 :=
      Subgroup.mem_centralizer_singleton_iff.mp hy
    show ((e.symm (eY.symm g : Y).1 : ↥K) : A) * s = s * ((e.symm (eY.symm g : Y).1 : ↥K) : A)
    have h1 : e.symm (eY.symm g : Y).1 * (⟨s, hsK⟩ : ↥K) = ⟨s, hsK⟩ * e.symm (eY.symm g : Y).1 := by
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, ← hw]
      exact hcomm
    exact congrArg Subtype.val h1
  · have hodd : Odd (Nat.card ↥(LieType.Steinberg.fixedSubfield F ℓ f)) := by
      rw [LieType.Steinberg.card_fixedSubfield hF]
      exact (hℓ.odd_of_ne_two hℓ2).pow
    have h2 := two_ne_zero_of_odd_card hodd
    set x : SL(2, ↥(LieType.Steinberg.fixedSubfield F ℓ f)) := eY ⟨w, hwY⟩ with hx
    have hx2 : x * x = 1 := by
      rw [hx, ← map_mul]
      have : (⟨w, hwY⟩ : Y) * ⟨w, hwY⟩ = 1 := Subtype.ext hww
      rw [this, map_one]
    have hx1 : x ≠ 1 := by
      intro h
      apply hw1
      have : (⟨w, hwY⟩ : Y) = 1 := eY.injective (by rw [← hx, h, map_one])
      exact congrArg Subtype.val this
    have hxm := sl2_eq_neg_one_of_sq h2 x hx2 hx1
    show ((e.symm (eY.symm (-1) : Y).1 : ↥K) : A) = s
    rw [← hxm, hx, MulEquiv.symm_apply_apply]
    show ((e.symm w : ↥K) : A) = s
    rw [hw, MulEquiv.symm_apply_apply]

theorem fu3_inner_cross {A : Type} [Group A] [Finite A] {K : Subgroup A} {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (h5 : 5 ≤ ℓ ^ f) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (ℓ ^ f) ^ 2) (e : ↥K ≃* StatedProj (StatedSU 3 (ℓ ^ f) F)) {s : A}
    (hsK : s ∈ K) (hs2 : s * s = 1) (hs1 : s ≠ 1) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ)
    {X : Subgroup A} (hX : IsPGroup p ↥X) (hX1 : X ≠ ⊥) (hXK : X ≤ K)
    (hnorm : ∀ j ∈ K, j * s = s * j → j ∈ normalizer (X : Set A)) (hcomm : ⁅X, zpowers s⁆ = X) : False := by
  classical
  obtain ⟨F₀, _, _, ι, hcard, hι, hι1⟩ := exists_sl2_block hℓ hℓ2 hf hF e hsK hs2 hs1
  have hud : UnitaryFieldData ℓ f F := ⟨hℓ, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  have hK : Nat.card K = psu3Order (Nat.card F₀) := by
    rw [hcard]
    exact (Nat.card_congr e.toEquiv).trans (card_statedProj_su3 hud)
  have hodd : Odd (Nat.card F₀) := by rw [hcard]; exact (hℓ.odd_of_ne_two hℓ2).pow
  have hpq : ¬ p ∣ Nat.card F₀ := by
    intro hd
    rw [hcard] at hd
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hℓ).mp
      ((Fact.out : p.Prime).dvd_of_dvd_pow hd))
  exact false_of_sl2_psu3 hp2 hodd (by rw [hcard]; exact h5) hpq ι hXK hX hX1
    (fun g => hnorm (ι g) (hι g).1 (hι g).2) (by rw [hι1]; exact hcomm) hK


section Lift

theorem exists_pgroup_lift {G Q : Type} [Group G] [Finite G] [Group Q] (π : G →* Q)
    (hker : π.ker ≤ Subgroup.center G) {p : ℕ} [Fact p.Prime] (Y : Subgroup Q) (hY : IsPGroup p ↥Y)
    (hYr : Y ≤ π.range) :
    ∃ Yt : Subgroup G, IsPGroup p ↥Yt ∧ Yt.map π = Y ∧
      ∀ g : G, π g ∈ normalizer (Y : Set Q) → g ∈ normalizer (Yt : Set G) := by
  classical
  set N : Subgroup G := Y.comap π with hN
  let f : ↥N →* ↥Y := (π.comp N.subtype).codRestrict Y fun x => x.2
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ := hYr hy
    exact ⟨⟨x, show π x ∈ Y by rw [hx]; exact hy⟩, Subtype.ext hx⟩
  have hfker : f.ker ≤ Subgroup.center ↥N := by
    intro x hx
    have h1 : π (x : G) = 1 := congrArg Subtype.val hx
    have h2 : (x : G) ∈ Subgroup.center G := hker h1
    rw [Subgroup.mem_center_iff] at h2 ⊢
    intro g
    exact Subtype.ext (h2 g)
  have : Finite ↥Y := Finite.of_surjective f hf
  have : Group.IsNilpotent ↥Y := hY.isNilpotent
  have : Group.IsNilpotent ↥N := Subgroup.isNilpotent_of_ker_le_center f hfker
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p ↥N))
  have hPn : (P : Subgroup ↥N).Normal := inferInstance
  have hPc : (P : Subgroup ↥N).Characteristic := Sylow.characteristic_of_normal P hPn
  set Yt : Subgroup G := (P : Subgroup ↥N).map N.subtype with hYt
  have hYtp : IsPGroup p ↥Yt := P.isPGroup'.map _
  have htop : (P : Subgroup ↥N).map f = ⊤ := by
    have h := (Sylow.mapSurjective hf P).is_maximal' (hY.to_subgroup ⊤) le_top
    rw [Sylow.coe_mapSurjective] at h
    exact h.symm
  have hmap : Yt.map π = Y := by
    have hcomp : π.comp N.subtype = Y.subtype.comp f := MonoidHom.ext fun _ => rfl
    rw [hYt, Subgroup.map_map, hcomp, ← Subgroup.map_map, htop, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  refine ⟨Yt, hYtp, hmap, fun g hg => ?_⟩
  have key : ∀ g : G, π g ∈ normalizer (Y : Set Q) → ∀ x ∈ Yt, g * x * g⁻¹ ∈ Yt := by
    intro g hg x hx
    obtain ⟨x', hx', rfl⟩ := hx
    have hconj : ∀ n : ↥N, g * (n : G) * g⁻¹ ∈ N := by
      intro n
      show π (g * (n : G) * g⁻¹) ∈ Y
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hg _).mp n.2
    have hg' : π g⁻¹ ∈ normalizer (Y : Set Q) := by
      rw [map_inv]; exact (normalizer (Y : Set Q)).inv_mem hg
    have hconj' : ∀ n : ↥N, g⁻¹ * (n : G) * g ∈ N := by
      intro n
      show π (g⁻¹ * (n : G) * g) ∈ Y
      have := (Subgroup.mem_normalizer_iff.mp hg' (π (n : G))).mp n.2
      rw [map_inv] at this
      simpa [map_mul, map_inv, mul_assoc] using this
    let φ : ↥N ≃* ↥N :=
      { toFun := fun n => ⟨g * (n : G) * g⁻¹, hconj n⟩
        invFun := fun n => ⟨g⁻¹ * (n : G) * g, hconj' n⟩
        left_inv := fun n => Subtype.ext (by simp [mul_assoc])
        right_inv := fun n => Subtype.ext (by simp [mul_assoc])
        map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
    have h1 : φ x' ∈ (P : Subgroup ↥N) := by
      have := (Subgroup.characteristic_iff_map_le.mp hPc) φ
      exact this ⟨x', hx', rfl⟩
    exact ⟨φ x', h1, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have hg' : π g⁻¹ ∈ normalizer (Y : Set Q) := by
    rw [map_inv]; exact (normalizer (Y : Set Q)).inv_mem hg
  have := key g⁻¹ hg' _ hx
  simpa [mul_assoc] using this

end Lift

section InnerDef

theorem fu3_inner_def {A : Type} [Group A] [Finite A] {K : Subgroup A} {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (h3 : 3 ≤ ℓ ^ f) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (ℓ ^ f) ^ 2) (e : ↥K ≃* StatedProj (StatedSU 3 (ℓ ^ f) F)) {s : A}
    (hsK : s ∈ K) (hs2 : s * s = 1) (hs1 : s ≠ 1) {X : Subgroup A} (hX : IsPGroup ℓ ↥X) (hX1 : X ≠ ⊥)
    (hXK : X ≤ K) (hnorm : ∀ j ∈ K, j * s = s * j → j ∈ normalizer (X : Set A)) : False := by
  classical
  have hud : UnitaryFieldData ℓ f F := ⟨hℓ, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP F ℓ := hud.charP
  have hq : Odd (ℓ ^ f) := (hℓ.odd_of_ne_two hℓ2).pow
  have hq1 : 1 ≤ ℓ ^ f := by omega
  obtain ⟨θ₀, hθ₀⟩ := exists_cover_of_equiv hud e
  set w : ↥K := ⟨s, hsK⟩ with hw
  have hw2 : w * w = 1 := Subtype.ext hs2
  have hw1 : w ≠ 1 := fun h => hs1 (congrArg Subtype.val h)
  have hS : SingleInv ↥K := SingleInv.of_mulEquiv e.symm (singleInv_psu hud hℓ2)
  obtain ⟨g, hg⟩ := hS (θ₀ (dU hq)) w (theta_dU_sq hq θ₀) (theta_dU_ne_one hud hq hθ₀) hw2 hw1
  set θ : ↥(unitarySU ℓ f F 3) →* ↥K := (MulAut.conj g).toMonoidHom.comp θ₀ with hθdef
  have hθ : IsCover hud θ := hθ₀.comp_equiv (MulAut.conj g)
  have hθdU : θ (dU hq) = w := by
    simpa [hθdef, MulAut.conj_apply] using hg
  set Y : Subgroup ↥K := X.subgroupOf K with hY
  have hYp : IsPGroup ℓ ↥Y := hX.of_equiv (Subgroup.subgroupOfEquivOfLe hXK).symm
  have hY1 : Y ≠ ⊥ := by
    intro h
    apply hX1
    rw [eq_bot_iff]
    intro x hx
    have h1 : (⟨x, hXK hx⟩ : ↥K) ∈ Y := hx
    rw [h] at h1
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp h1))
  have hYn : ∀ j : ↥K, j * w = w * j → j ∈ normalizer (Y : Set ↥K) := by
    intro j hj
    have hjN : (j : A) ∈ normalizer (X : Set A) := hnorm j j.2 (by
      have := congrArg Subtype.val hj
      exact this)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have := Subgroup.mem_normalizer_iff.mp hjN (y : A)
    simpa [hY, Subgroup.mem_subgroupOf] using this
  obtain ⟨Yt, hYt, hmap, hnormYt⟩ := exists_pgroup_lift θ (by rw [hθ.ker]; exact unitaryScalars_le_center hud 3)
    Y hYp (by rw [MonoidHom.range_eq_top.mpr hθ.surj]; exact le_top)
  have hYt1 : Yt ≠ ⊥ := by
    intro h
    apply hY1
    rw [← hmap, h, Subgroup.map_bot]
  set Xt : Subgroup (GL (Fin 3) F) := Yt.map (unitarySU ℓ f F 3).subtype with hXt
  have hXtp : IsPGroup ℓ ↥Xt := hYt.map _
  have hXt1 : Xt ≠ ⊥ := by
    intro h
    apply hYt1
    rw [eq_bot_iff]
    intro y hy
    have : ((y : ↥(unitarySU ℓ f F 3)) : GL (Fin 3) F) ∈ Xt := ⟨y, hy, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext this)
  have hXtU : Xt ≤ unitarySU ℓ f F 3 := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  refine block_no_lgroup hud hq1 h3 Xt hXtU hXtp hXt1 fun B => ?_
  have hBn : (levU hq1 B : ↥(unitarySU ℓ f F 3)) ∈ normalizer (Yt : Set ↥(unitarySU ℓ f F 3)) := by
    apply hnormYt
    apply hYn
    have hc : levU hq1 B * dU hq = dU hq * levU hq1 B :=
      Subgroup.mem_centralizer_singleton_iff.mp (levU_mem_centralizer hq B)
    rw [← hθdU, ← map_mul, ← map_mul, hc]
  exact Subgroup.le_normalizer_map (unitarySU ℓ f F 3).subtype (Subgroup.mem_map_of_mem _ hBn)

end InnerDef

section Three

theorem commutator_mem_centralizer_of_cyclic {A : Type} [Group A] {X : Subgroup A} (hX : IsCyclic ↥X)
    {a b : A} (ha : a ∈ normalizer (X : Set A)) (hb : b ∈ normalizer (X : Set A)) :
    ⁅a, b⁆ ∈ centralizer (X : Set A) := by
  classical
  let φ : ↥(normalizer (X : Set A)) →* (ZMod (Nat.card ↥X))ˣ :=
    (IsCyclic.mulAutMulEquiv ↥X).toMonoidHom.comp X.normalizerMonoidHom
  have h1 : φ ⁅(⟨a, ha⟩ : ↥(normalizer (X : Set A))), ⟨b, hb⟩⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)
  have h2 : X.normalizerMonoidHom ⁅(⟨a, ha⟩ : ↥(normalizer (X : Set A))), ⟨b, hb⟩⁆ = 1 := by
    apply (IsCyclic.mulAutMulEquiv ↥X).injective
    rw [map_one]
    exact h1
  have h3 : ⁅(⟨a, ha⟩ : ↥(normalizer (X : Set A))), ⟨b, hb⟩⁆ ∈ X.normalizerMonoidHom.ker := h2
  rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at h3
  exact h3

theorem coe_uElt_SL {k : Type} [Field k] :
    ((uElt : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) = !![1, 1; 0, 1] := rfl

theorem coe_vElt_SL {k : Type} [Field k] :
    ((vElt : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) = !![1, 0; 1, 1] := rfl

theorem comm_uv_sq {F₀ : Type} [Field F₀] (h3 : (3 : F₀) = 0) :
    ⁅(uElt : SL(2, F₀)), (vElt : SL(2, F₀))⁆ * ⁅(uElt : SL(2, F₀)), (vElt : SL(2, F₀))⁆ = -1 := by
  let c : SL(2, F₀) := ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩
  have hc : ((c : SL(2, F₀)) : Matrix (Fin 2) (Fin 2) F₀) = !![0, -1; 1, 0] := rfl
  have hmat : (uElt : SL(2, F₀)) * (vElt : SL(2, F₀)) =
      c * ((vElt : SL(2, F₀)) * (uElt : SL(2, F₀))) := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, hc, coe_uElt_SL, coe_vElt_SL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> linear_combination h3
  have hcomm : ⁅(uElt : SL(2, F₀)), (vElt : SL(2, F₀))⁆ = c := by
    rw [commutatorElement_def, hmat]
    group
  rw [hcomm]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, hc, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem fu3_inner_three {A : Type} [Group A] [Finite A] {K : Subgroup A} {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (hq3 : ℓ ^ f = 3) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (ℓ ^ f) ^ 2) (e : ↥K ≃* StatedProj (StatedSU 3 (ℓ ^ f) F)) {s : A}
    (hsK : s ∈ K) (hs2 : s * s = 1) (hs1 : s ≠ 1) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ)
    {X : Subgroup A} (hX : IsPGroup p ↥X) (hX1 : X ≠ ⊥) (hXK : X ≤ K)
    (hnorm : ∀ j ∈ K, j * s = s * j → j ∈ normalizer (X : Set A)) (hcomm : ⁅X, zpowers s⁆ = X) :
    False := by
  classical
  obtain ⟨F₀, _, _, ι, hcard, hι, hι1⟩ := exists_sl2_block hℓ hℓ2 hf hF e hsK hs2 hs1
  have hud : UnitaryFieldData ℓ f F := ⟨hℓ, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  have hK : Nat.card K = 6048 := by
    have h1 : Nat.card K = psu3Order (ℓ ^ f) := (Nat.card_congr e.toEquiv).trans (card_statedProj_su3 hud)
    rw [h1, hq3]
    norm_num [psu3Order]
  have hℓ3 : ℓ = 3 := by
    have : ℓ ∣ 3 := hq3 ▸ dvd_pow_self ℓ (by omega)
    exact (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).mp this
  obtain ⟨a, ha⟩ := hX.exists_card_eq
  have hXdvd : Nat.card ↥X ∣ 6048 := hK ▸ Subgroup.card_dvd_of_le hXK
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hX1
    exact Subgroup.eq_bot_of_card_eq X (by simpa using ha)
  have hpp : p ∣ 6048 := (dvd_pow_self p ha0).trans (ha ▸ hXdvd)
  have hp7 : p = 7 := by
    have h6048 : (6048 : ℕ) = 2 ^ 5 * 3 ^ 3 * 7 := by norm_num
    rw [h6048] at hpp
    rcases (Fact.out : p.Prime).dvd_mul.mp hpp with h | h
    · rcases (Fact.out : p.Prime).dvd_mul.mp h with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp
          ((Fact.out : p.Prime).dvd_of_dvd_pow h)) hp2
      · have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).mp
          ((Fact.out : p.Prime).dvd_of_dvd_pow h)
        exact absurd (hp3.trans hℓ3.symm) hpℓ
    · exact (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (by norm_num)).mp h
  have ha1 : a = 1 := by
    by_contra hne
    have h2 : 2 ≤ a := by omega
    have h49 : 7 ^ 2 ∣ 6048 := by
      have := pow_dvd_pow 7 h2
      rw [hp7] at ha
      exact this.trans (ha ▸ hXdvd)
    norm_num at h49
  have hcardX : Nat.card ↥X = p := by rw [ha, ha1, pow_one]
  have hcyc : IsCyclic ↥X := isCyclic_of_prime_card hcardX
  have h3F : (3 : F₀) = 0 := by
    have : Fintype F₀ := Fintype.ofFinite F₀
    have h := Nat.cast_card_eq_zero F₀
    rw [← Nat.card_eq_fintype_card, hcard, hq3] at h
    exact_mod_cast h
  have hu : ι uElt ∈ normalizer (X : Set A) := hnorm _ (hι _).1 (hι _).2
  have hv : ι vElt ∈ normalizer (X : Set A) := hnorm _ (hι _).1 (hι _).2
  have hcc := commutator_mem_centralizer_of_cyclic hcyc hu hv
  rw [← map_commutatorElement] at hcc
  have hsq : s = ι ⁅(uElt : SL(2, F₀)), (vElt : SL(2, F₀))⁆ * ι ⁅(uElt : SL(2, F₀)), (vElt : SL(2, F₀))⁆ := by
    rw [← map_mul, comm_uv_sq h3F, hι1]
  have hs : s ∈ centralizer (X : Set A) := by
    rw [hsq]
    exact (centralizer (X : Set A)).mul_mem hcc hcc
  apply hX1
  rw [← hcomm, eq_bot_iff, Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hxs : Commute x s := Subgroup.mem_centralizer_iff.mp hs x hx
  rw [Subgroup.mem_bot]
  exact commutatorElement_eq_one_iff_commute.mpr (hxs.zpow_right n)

end Three


section All

theorem fu3_inner_false {A : Type} [Group A] [Finite A] {K : Subgroup A} {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (h3 : 3 ≤ ℓ ^ f) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (ℓ ^ f) ^ 2) (e : ↥K ≃* StatedProj (StatedSU 3 (ℓ ^ f) F)) {s : A}
    (hsK : s ∈ K) (hs2 : s * s = 1) (hs1 : s ≠ 1) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {X : Subgroup A} (hX : IsPGroup p ↥X) (hX1 : X ≠ ⊥) (hXK : X ≤ K)
    (hnorm : ∀ j ∈ K, j * s = s * j → j ∈ normalizer (X : Set A)) (hcomm : ⁅X, zpowers s⁆ = X) :
    False := by
  by_cases hpℓ : p = ℓ
  · subst hpℓ
    exact fu3_inner_def (Fact.out : p.Prime) hℓ2 hf h3 hF e hsK hs2 hs1 hX hX1 hXK hnorm
  · by_cases h5 : 5 ≤ ℓ ^ f
    · exact fu3_inner_cross hℓ hℓ2 hf h5 hF e hsK hs2 hs1 hp2 hpℓ hX hX1 hXK hnorm hcomm
    · have hq : Odd (ℓ ^ f) := (hℓ.odd_of_ne_two hℓ2).pow
      have hq3 : ℓ ^ f = 3 := by
        obtain ⟨m, hm⟩ := hq
        omega
      exact fu3_inner_three hℓ hℓ2 hf hq3 hF e hsK hs2 hs1 hp2 hpℓ hX hX1 hXK hnorm hcomm

end All

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
