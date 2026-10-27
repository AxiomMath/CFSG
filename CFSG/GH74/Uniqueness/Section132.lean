module

public import CFSG.GH74.Uniqueness.Section132W
public import CFSG.GH74.Uniqueness.Bender.UnitaryFixed

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem A6.L_le_LA (S : ZDSetup X Z M) (c : Ctx12 Z M) {A : Subgroup X}
    (hAL : ∀ a ∈ A, ∀ y ∈ c.L, a * y = y * a) : c.L ≤ zHull Z (centralizer (A : Set X)) := by
  have hLC : c.L ≤ centralizer (A : Set X) := fun y hy =>
    mem_centralizer_iff.mpr fun a ha => hAL a ha y hy
  calc c.L = zHull Z c.L := (IsProductDisconnected.zHull_lSubgroup S.invariant c.ht c.hz M).symm
    _ ≤ zHull Z (centralizer (A : Set X)) := closure_mono (Set.inter_subset_inter_right Z hLC)

theorem A6.ncard_Z_inter_L
    (S : ZDSetup X Z M) {c : Ctx12 Z M} {n : ℕ} (hL : LData c n 1) :
    (Z ∩ (c.L : Set X)).ncard = (2 ^ n - 1) * ((2 ^ n) ^ 1 + 1) := by
  have h1 := hL.bender.ncard_involutions
  have himage : (Subtype.val : ↥c.L → X) '' {a : ↥c.L | orderOf a = 2} = Z ∩ (c.L : Set X) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hL.invol y y.2 (by rw [Subgroup.orderOf_coe]; exact hy), y.2⟩
    · rintro ⟨hxZ, hxL⟩
      refine ⟨⟨x, hxL⟩, ?_, rfl⟩
      rw [Set.mem_ofPred_eq, Subgroup.orderOf_mk]
      exact S.invariant.1 x hxZ
  rw [← himage, Set.ncard_image_of_injective _ Subtype.val_injective, h1]

theorem A6.nonempty_L_equiv {c : Ctx12 Z M} {n : ℕ} (hL : LData c n 1) :
    Nonempty (↥c.L ≃* Theory.Comparator.PSL2Model n) := by
  have h := hL.bender
  cases h with
  | linear n hn e => exact ⟨e⟩

theorem A6.lemma132
    (S : ZDSetup X Z M) (h12 : Sec12Results Z M) {c : Ctx12 Z M} {n e : ℕ}
    (hL : LData c n 1) {u : X} (hu : u ∈ c.D) (hu2 : orderOf u = 2)
    (hBu : BenderSub Z M (cenHull Z u) n 3 e) {A : Subgroup X} (hAu : A ≤ cenHull Z u)
    (hAodd : Odd (Nat.card A)) (hAL : ∀ a ∈ A, ∀ y ∈ c.L, a * y = y * a)
    (hA0 : ∃ a ∈ A, ∃ y ∈ cenHull Z u, a * y ≠ y * a) :
    ∃ e', BenderSub Z M (zHull Z (centralizer (A : Set X))) n 3 e' ∧
      ¬ zHull Z (centralizer (A : Set X)) ≤ cenHull Z u ∧
      ∃ hun : u ∈ normalizer (zHull Z (centralizer (A : Set X)) : Set X),
        A6.barHom _ ⟨u, hun⟩ * A6.barHom _ ⟨u, hun⟩ = 1 ∧
        (¬ ∃ k, ∀ x, A6.barHom _ ⟨u, hun⟩ x = k * x * k⁻¹) ∧
        ∀ k ∈ Bender.autFixed (A6.barHom _ ⟨u, hun⟩),
          ∃ y, ∃ hy : y ∈ zHull Z (centralizer (A : Set X)), y ∈ c.L ∧
            QuotientGroup.mk' (center ↥(zHull Z (centralizer (A : Set X)))) ⟨y, hy⟩ = k := by
  set LA := zHull Z (centralizer (A : Set X)) with hLAdef
  have hZ := S.invariant
  have hLLA : c.L ≤ LA := A6.L_le_LA S c hAL
  have hLu : c.L ≤ cenHull Z u := (h12.l129 c n 1 hL u hu hu2).2
  obtain ⟨a₀, ha₀A, y₀, hy₀, ha₀y₀⟩ := hA0
  have hCne : centralizer (A : Set X) ≠ ⊤ := by
    intro htop
    apply ha₀y₀
    have hy : y₀ ∈ centralizer (A : Set X) := htop ▸ mem_top y₀
    exact mem_centralizer_iff.mp hy a₀ ha₀A
  have hCM : ¬ centralizer (A : Set X) ≤ M := fun h =>
    c.htM (h (mem_centralizer_iff.mpr fun a ha => hAL a ha _ c.t_mem_L))
  have hne : (Z ∩ ((centralizer (A : Set X) ⊓ M : Subgroup X) : Set X)).Nonempty :=
    ⟨c.z, c.hz, mem_inf.mpr ⟨mem_centralizer_iff.mpr fun a ha => hAL a ha _ c.z_mem_L, c.hzM⟩⟩
  have hLns : ¬ Group.IsSolvable ↥c.L := by
    intro hLsol
    have : IsSimpleGroup ↥c.L := hL.bender.isSimple
    exact hL.bender.isSimpleBenderGroup.not_commutative
      ((IsSimpleGroup.comm_iff_isSolvable (G := ↥c.L)).mpr hLsol)
  have hns : ¬ Group.IsSolvable ↥LA := by
    intro hsol
    exact hLns (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hLLA)
      (Subgroup.inclusion_injective hLLA))
  obtain ⟨n', j, e', hBA⟩ := S.benderSub_exists hCne hCM hne hns
  have hZM : Z ∩ ((LA ⊓ M : Subgroup X) : Set X) = Z ∩ (M : Set X) := by
    ext x
    constructor
    · rintro ⟨hxZ, hxLM⟩
      exact ⟨hxZ, (mem_inf.mp hxLM).2⟩
    · rintro ⟨hxZ, hxM⟩
      exact ⟨hxZ, mem_inf.mpr ⟨hLLA (IsProductDisconnected.inter_le_lSubgroup hZ S.prodDisc c.ht
        c.htM c.hz c.hzM ⟨hxZ, hxM⟩), hxM⟩⟩
  have hn' : n' = n := by
    have h1 := A2.ncard_inter_of_benderSub S hBA
    rw [hZM, A2.ncard_zM hL] at h1
    have h2 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have h3 : 1 ≤ 2 ^ n' := Nat.one_le_two_pow
    exact Nat.pow_right_injective le_rfl (by omega : 2 ^ n' = 2 ^ n)
  subst hn'
  set πA := QuotientGroup.mk' (center ↥LA) with hπA
  let ι : ↥c.L →* ↥LA ⧸ center ↥LA := πA.comp (Subgroup.inclusion hLLA)
  have hιinj : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro l hl
    have hmem : Subgroup.inclusion hLLA l ∈ center ↥LA := (QuotientGroup.eq_one_iff _).mp hl
    have hlc : l ∈ center ↥c.L := by
      rw [mem_center_iff]
      intro g
      apply Subtype.ext
      have h1 := mem_center_iff.mp hmem (Subgroup.inclusion hLLA g)
      have h2 := Subtype.ext_iff.mp h1
      exact h2
    rw [hL.center_eq_bot, mem_bot] at hlc
    exact hlc
  obtain ⟨φL⟩ := A6.nonempty_L_equiv hL
  rcases Bender.BenderType.embedding_index hL.bender hBA.bender ι hιinj with hj | ⟨-, hj⟩
  · exfalso
    subst hj
    have hLeq : c.L = LA := A6.eq_of_le_of_ncard_le
      (IsProductDisconnected.zHull_lSubgroup hZ c.ht c.hz M) hBA.zhull hLLA
      (le_of_eq (by rw [A6.ncard_Z_inter S hBA, A6.ncard_Z_inter_L S hL]))
    obtain ⟨W, hWLA, hWL, ⟨φW⟩⟩ := A6.exists_W S h12 hL hu hu2 hBu hAu hAodd hAL
    apply hWL
    have hWL' : W ≤ c.L := by rw [hLeq]; exact hWLA
    apply Subgroup.eq_of_le_of_card_ge hWL'
    exact le_of_eq ((Nat.card_congr φL.toEquiv).trans (Nat.card_congr φW.toEquiv).symm)
  subst hj
  have hnotle : ¬ LA ≤ cenHull Z u := by
    intro hle
    have heq : LA = cenHull Z u := A6.eq_of_le_of_ncard_le hBA.zhull hBu.zhull hle (le_of_eq (by
      rw [A6.ncard_Z_inter S hBu, A6.ncard_Z_inter S hBA]))
    apply ha₀y₀
    have hy₀LA : y₀ ∈ LA := by rw [heq]; exact hy₀
    have : y₀ ∈ centralizer (A : Set X) := Cor713.zHull_le _ hy₀LA
    exact mem_centralizer_iff.mp this a₀ ha₀A
  have huC : u ∈ centralizer (A : Set X) :=
    mem_centralizer_iff.mpr fun a ha => (mul_comm_of_mem_cenHull (hAu ha)).symm
  have hun : u ∈ normalizer (LA : Set X) := A6.mem_normalizer_zHull hZ (le_normalizer huC)
  set α := A6.barHom LA ⟨u, hun⟩ with hα
  have hα2 : α * α = 1 := by
    rw [hα, ← map_mul]
    have : (⟨u, hun⟩ : ↥(normalizer (LA : Set X))) * ⟨u, hun⟩ = 1 :=
      Subtype.ext (sec126_involution_mul_self hu2)
    rw [this, map_one]
  have hαL : ∀ y (hy : y ∈ LA), y ∈ c.L → α (πA ⟨y, hy⟩) = πA ⟨y, hy⟩ := by
    intro y hy hyL
    rw [hα, A6.barHom_mk' _ _ hy hy]
    have h1 : u * y = y * u := mul_comm_of_mem_cenHull (hLu hyL)
    rw [h1, mul_inv_cancel_right]
  have hnotinner : ¬ ∃ k, ∀ x, α x = k * x * k⁻¹ := by
    rintro ⟨k, hk⟩
    by_cases hk1 : k = 1
    · apply hnotle
      have hαfix : ∀ z ∈ Z, ∀ hzF : z ∈ LA, α (πA ⟨z, hzF⟩) = πA ⟨z, hzF⟩ := fun z _ hzF => by
        rw [hk, hk1]
        group
      have huLA := A6.mem_centralizer_of_barHom_eq_one LA (fun z hz => hZ.mul_self_eq_one hz)
        hBA.zhull (A2.odd_card_center_of_benderSub hBA) ⟨u, hun⟩ hαfix
      calc LA = zHull Z LA := hBA.zhull.symm
        _ ≤ cenHull Z u := closure_mono (Set.inter_subset_inter_right Z fun x hx =>
            mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp huLA x hx))
    · have hconj2 : ∀ x, (k * k) * x * (k * k)⁻¹ = x := by
        intro x
        have h1 : α (α x) = x := by rw [← MulAut.mul_apply, hα2, MulAut.one_apply]
        rw [hk, hk] at h1
        calc (k * k) * x * (k * k)⁻¹ = k * (k * x * k⁻¹) * k⁻¹ := by group
          _ = x := h1
      have hk2 : k * k = 1 := by
        have hcen : k * k ∈ center (↥LA ⧸ center ↥LA) := by
          rw [mem_center_iff]
          intro x
          calc x * (k * k) = ((k * k) * x * (k * k)⁻¹) * (k * k) := by rw [hconj2 x]
            _ = (k * k) * x := by group
        rw [Bender.BenderType.center_eq_bot hBA.bender, mem_bot] at hcen
        exact hcen
      have hk2' : orderOf k = 2 := orderOf_eq_prime (by rw [sq]; exact hk2) hk1
      obtain ⟨Q, hkQ⟩ := Sec128B.exists_sylow_mem_of_orderOf_eq_two hk2'
      obtain ⟨t', hct⟩ := hBA.bender.exists_benderCore Q
      obtain ⟨-, -, -, -, hsol, -⟩ :=
        hBA.bender.lemma_3_4_b Q hct.sq_eq_one hct.not_mem ⟨Bender.le_borel _ hkQ, hk2'⟩
      have hLk : ∀ l : ↥c.L, ι l ∈ centralizer ({k} : Set (↥LA ⧸ center ↥LA)) := by
        intro l
        rw [mem_centralizer_singleton_iff]
        have h1 := hαL l (hLLA l.2) l.2
        rw [hk] at h1
        change πA ⟨l, hLLA l.2⟩ * k = k * πA ⟨l, hLLA l.2⟩
        calc πA ⟨l, hLLA l.2⟩ * k = (k * πA ⟨l, hLLA l.2⟩ * k⁻¹) * k := by rw [h1]
          _ = k * πA ⟨l, hLLA l.2⟩ := by group
      let ι' : ↥c.L →* ↥(centralizer ({k} : Set (↥LA ⧸ center ↥LA))) := ι.codRestrict _ hLk
      have hι'inj : Function.Injective ι' := fun a b hab => hιinj (congrArg Subtype.val hab)
      exact hLns (Group.isSolvable_of_isSolvable_injective hι'inj)
  have hfixL : ∀ k ∈ Bender.autFixed α, ∃ y, ∃ hy : y ∈ LA, y ∈ c.L ∧ πA ⟨y, hy⟩ = k := by
    obtain ⟨φ⟩ := hBA.bender.fixed_unitary α hα2 hnotinner
    have hle : ι.range ≤ Bender.autFixed α := by
      rintro _ ⟨l, rfl⟩
      exact hαL l (hLLA l.2) l.2
    have hcard : Nat.card (Bender.autFixed α) ≤ Nat.card ι.range := le_of_eq (by
      rw [Nat.card_congr φ.toEquiv, ← Nat.card_congr (MonoidHom.ofInjective hιinj).toEquiv,
        Nat.card_congr φL.toEquiv])
    have heq := Subgroup.eq_of_le_of_card_ge hle hcard
    intro k hk
    rw [← heq] at hk
    obtain ⟨l, rfl⟩ := hk
    exact ⟨l, hLLA l.2, l.2, rfl⟩
  exact ⟨e', hBA, hnotle, hun, hα2, hnotinner, hfixL⟩

end CFSG.GH74.Uniqueness
