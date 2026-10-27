module

public import CFSG.Quasithin.Background.SmithB42G2FMain
public import CFSG.Quasithin.Vol2.Ch4Sec3L436InspFFG2
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15InnerStrict

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.B42G2 CFSG.Quasithin.B42G2F
open CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.JonesParshall
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.FFModules
open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF

@[expose] noncomputable def linearEquivToMulAut (Y : Type*) [AddCommGroup Y]
    [Module (ZMod 2) Y] : (Y ≃ₗ[ZMod 2] Y) →* MulAut (Multiplicative Y) where
  toFun e := AddEquiv.toMultiplicative e.toAddEquiv
  map_one' := by ext x; rfl
  map_mul' e f := by ext x; rfl

theorem linearEquivToMulAut_injective (Y : Type*) [AddCommGroup Y] [Module (ZMod 2) Y] :
    Function.Injective (linearEquivToMulAut Y) := by
  intro e f h
  apply LinearEquiv.ext
  intro y
  have h1 := congrArg (fun g : MulAut (Multiplicative Y) => g (Multiplicative.ofAdd y)) h
  simpa [linearEquivToMulAut] using h1

section IndexBound

variable {K : Type} [Group K] [Finite K] {L B : Subgroup K} (h : InnerCtx L B)
  {F : Type} [Field F] [Fintype F] {n : ℕ} (hn : 2 ≤ n) (hF : Fintype.card F = 2 ^ n)

theorem exists_g2AdjointEquiv (hn : 2 ≤ n) (hF : Fintype.card F = 2 ^ n)
    (e : ↥L ≃* ↥(quasithinG2 F)) :
    Nonempty (↥L ≃* ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 F)) := by
  classical
  have hNatF : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card]; exact hF
  haveI : CharP F 2 := CFSG.Quasithin.B42G2Id.charP_two_of_card hNatF
  obtain ⟨ψ, -, hsurj, hker⟩ :=
    CFSG.Quasithin.B42G2Id.exists_adjointGroup_hom_cayleyGroup (K := F) hNatF hn
  have hZadj : Subgroup.center ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 F) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, hker, hZadj]
  let ψe : ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 F) ≃* ↥(cayleyGroup F) :=
    MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩
  let eC : ↥L ≃* ↥(cayleyGroup F) :=
    e.trans (MulEquiv.subgroupCongr CFSG.Quasithin.G11.P3G2.quasithinG2_eq_cayleyGroup)
  exact ⟨eC.trans ψe.symm⟩

theorem g2_relIndex_innerPart_le_two (h : InnerCtx L B) (hn : 2 ≤ n)
    (hF : Fintype.card F = 2 ^ n) (e : ↥L ≃* ↥(quasithinG2 F)) :
    (innerPart L B).relIndex B ≤ 2 := by
  classical
  have hNatF : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card]; exact hF
  haveI : CharP F 2 := CFSG.Quasithin.B42G2Id.charP_two_of_card hNatF
  have hBN : B ≤ Subgroup.normalizer (L : Set K) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr h.normal_L]
    exact le_top
  obtain ⟨-, Θ, -, -, hΘker, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.even_G2_exact_automorphism_normal_form
      hn F hNatF
  have hinv : ∀ x y : F ≃+* F, x * x = 1 → y * y = 1 → x ≠ 1 → y ≠ 1 → x = y := by
    intro x y hx hy hx1 hy1
    have h1 : ∀ k, x (x k) = k := fun k => congrArg (fun σ : F ≃+* F => σ k) hx
    have h2 : ∀ k, y (y k) = k := fun k => congrArg (fun σ : F ≃+* F => σ k) hy
    have h1' : ∃ k, x k ≠ k := by
      by_contra hcon
      push Not at hcon
      exact hx1 (RingEquiv.ext hcon)
    have h2' : ∃ k, y k ≠ k := by
      by_contra hcon
      push Not at hcon
      exact hy1 (RingEquiv.ext hcon)
    exact CFSG.Quasithin.B42G2.ringEquiv_involution_unique hNatF hn h1 h2 h1' h2'
  obtain ⟨φ⟩ := exists_g2AdjointEquiv (L := L) hn hF e
  let cg : MulAut ↥L →* MulAut ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 F) :=
    (MulAut.congr φ).toMonoidHom
  let Φ : ↥B →* (F ≃+* F) := (Θ.comp cg).comp (CFSG.LocalAnalysis.RankThreeUC.S15.InnerOut.conjHom L B hBN)
  have hmap : (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L).map
      (MulAut.congr φ).toMonoidHom =
      CFSG.ComponentClassification.OuterAutomorphisms.inner
        ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 F) := inner_map_congr φ
  have hpre : cg ⁻¹'
      (CFSG.ComponentClassification.OuterAutomorphisms.inner
        ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 F)) =
      CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L := by
    ext x
    rw [Set.mem_preimage, ← hmap]
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      rwa [← (MulAut.congr φ).injective hyx]
    · intro hx
      exact Subgroup.mem_map_of_mem _ hx
  have hker : Φ.ker = (innerPart L B).subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply, Subgroup.mem_subgroupOf,
      mem_innerPart]
    constructor
    · intro hb
      have hb' : CFSG.LocalAnalysis.RankThreeUC.S15.InnerOut.conjHom L B hBN b ∈
          CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L := by
        have h1 : cg (CFSG.LocalAnalysis.RankThreeUC.S15.InnerOut.conjHom L B hBN b) ∈
            CFSG.ComponentClassification.OuterAutomorphisms.inner
              ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 F) := by
          rw [show CFSG.ComponentClassification.OuterAutomorphisms.inner
              ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 F) = Θ.ker from hΘker.symm]
          exact MonoidHom.mem_ker.mpr hb
        rw [← hmap] at h1
        obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp h1
        rw [← (MulAut.congr φ).injective hyx]
        exact hy
      obtain ⟨l, hl, hag⟩ :=
        CFSG.LocalAnalysis.RankThreeUC.S15.InnerOut.exists_conjAgree_of_mem_range L B hBN b hb'
      exact ⟨b.2, l, hl, hag⟩
    · rintro ⟨hbB, l, hl, hag⟩
      rw [← MonoidHom.mem_ker, hΘker]
      have hconj : CFSG.LocalAnalysis.RankThreeUC.S15.InnerOut.conjHom L B hBN b =
          MulAut.conj ⟨l, hl⟩ := by
        apply MulEquiv.ext
        intro k
        apply Subtype.ext
        exact hag (k : K) k.2
      rw [hconj]
      change MulAut.congr φ (MulAut.conj ⟨l, hl⟩) ∈ MulAut.conj.range
      rw [congr_conj]
      exact ⟨φ ⟨l, hl⟩, rfl⟩
  have hrange_sq : ∀ x ∈ Φ.range, x * x = 1 := by
    rintro _ ⟨b, rfl⟩
    rw [← map_mul, show ((b : ↥B) * b : ↥B) = 1 by
      exact Subtype.ext (by simpa using InnerCtx.sq h (b : K) b.2), map_one]
  have hrange_comm : ∀ x ∈ Φ.range, ∀ y ∈ Φ.range, x * y = y * x := by
    rintro _ ⟨b, rfl⟩ _ ⟨c, rfl⟩
    rw [← map_mul, ← map_mul, show ((b : ↥B) * c : ↥B) = (c : ↥B) * b by
      exact Subtype.ext (InnerCtx.comm h (b : K) b.2 (c : K) c.2)]
  have hrange_card : Nat.card Φ.range ≤ 2 := by
    by_cases htriv : ∀ y ∈ Φ.range, y = 1
    · have : Φ.range = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr htriv
      rw [this, Subgroup.card_bot]
      norm_num
    · push Not at htriv
      obtain ⟨y₀, hy₀, hy₀1⟩ := htriv
      have hsub : (Φ.range : Set (F ≃+* F)) ⊆ {1, y₀} := by
        intro y hy
        by_cases hy1 : y = 1
        · exact Or.inl hy1
        · exact Or.inr (hinv y y₀ (hrange_sq y hy) (hrange_sq y₀ hy₀) hy1 hy₀1)
      calc Nat.card Φ.range = Nat.card (Φ.range : Set (F ≃+* F)) := rfl
        _ ≤ Nat.card ({1, y₀} : Set (F ≃+* F)) := Nat.card_mono (Set.toFinite _) hsub
        _ ≤ 2 := by
            rw [Nat.card_coe_set_eq, Set.ncard_pair hy₀1.symm]
  have hBcard : Nat.card ↥B = Nat.card ↥(innerPart L B) * Nat.card Φ.range := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup Φ.ker
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (innerPart_le L B)).toEquiv] at h1
    have h2 : Nat.card (↥B ⧸ (innerPart L B).subgroupOf B) = Nat.card Φ.range := by
      rw [← hker]
      exact Nat.card_congr (QuotientGroup.quotientKerEquivRange Φ).toEquiv
    rw [h1, h2, mul_comm]
  have hrel : Nat.card ↥(innerPart L B) * (innerPart L B).relIndex B = Nat.card ↥B := by
    have h1 := Subgroup.card_mul_index ((innerPart L B).subgroupOf B)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (innerPart_le L B)).toEquiv] at h1
    exact h1
  have heq : (innerPart L B).relIndex B = Nat.card Φ.range := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥(innerPart L B)))
    rw [hrel, hBcard]
  rw [heq]
  exact hrange_card

end IndexBound

section NaturalOffender

variable {F : Type} [Field F] [Fintype F] [CharP F 2] {n : ℕ}
  {Y : Type} [AddCommGroup Y] [Module (ZMod 2) Y] [Finite Y]

theorem g2_offender_facts_of_natural (hn : 2 ≤ n) (hF : Fintype.card F = 2 ^ n)
    (π : ↥(cayleyGroup F) →* (Y ≃ₗ[ZMod 2] Y)) (hπ : Function.Injective π)
    (hnt : Nontrivial Y)
    (hirr : ∀ U : Submodule (ZMod 2) Y, (∀ g, ∀ u ∈ U, π g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (A : Subgroup (Y ≃ₗ[ZMod 2] Y))
    (hnorm : ∀ a ∈ A, ∀ x, ∃ y, a * π x * a⁻¹ = π y)
    (hAe : CFSG.IsElementaryAbelian 2 ↥A) (hA1 : A ≠ ⊥)
    (hoff : Nat.card Y ≤ Nat.card ↥A * Nat.card {y : Y // ∀ a ∈ A, a y = y}) :
    A ≤ π.range ∧
      Nat.card ↥A * Nat.card {y : Y // ∀ a ∈ A, a y = y} ≤ Nat.card Y := by
  classical
  have hNatF : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card]; exact hF
  have hFc : Fintype.card F = 2 ^ n := hF
  obtain ⟨φ, hφ⟩ :=
    B42G2F.exists_natural_of_offender (K := F) hFc hn π hπ hnt hirr A hnorm hAe hA1 hoff
  have h3 : 3 ≤ Nat.card F := by
    rw [hNatF]
    calc 3 ≤ 4 := by norm_num
      _ = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨c, hc0, hc1⟩ := CFSG.Quasithin.B42G2Id.exists_ne_zero_ne_one_of_three_le (K := F) h3
  let ε : ↥⁅quasithinG2 F, quasithinG2 F⁆ ≃* ↥(cayleyGroup F) :=
    MulEquiv.subgroupCongr (CFSG.Quasithin.Vol2.Ch11.G2Q8.g2Derived_eq hc0 hc1)
  let lm : (Y ≃ₗ[ZMod 2] Y) →* MulAut (Multiplicative Y) := linearEquivToMulAut Y
  let H : Subgroup (MulAut (Multiplicative Y)) := π.range.map lm
  let gamToSub : (FFModel.zornQ ⁅quasithinG2 F, quasithinG2 F⁆).Gam →
      ↥⁅quasithinG2 F, quasithinG2 F⁆ := fun γ => γ
  let π' : (FFModel.zornQ ⁅quasithinG2 F, quasithinG2 F⁆).Gam →* ↥H :=
    { toFun := fun γ => ⟨lm (π (ε (gamToSub γ))), Subgroup.mem_map_of_mem _ ⟨_, rfl⟩⟩
      map_one' := by
        apply Subtype.ext
        show lm (π (ε (gamToSub 1))) = (1 : MulAut (Multiplicative Y))
        rw [show gamToSub 1 = (1 : ↥⁅quasithinG2 F, quasithinG2 F⁆) from rfl]
        simp
      map_mul' := fun γ δ => by
        apply Subtype.ext
        show lm (π (ε (gamToSub (γ * δ)))) =
          lm (π (ε (gamToSub γ))) * lm (π (ε (gamToSub δ)))
        rw [show gamToSub (γ * δ) =
          gamToSub γ * gamToSub δ from rfl]
        rw [map_mul, map_mul, map_mul] }
  let f : Multiplicative Y → (Ix3 → F) := fun u => φ (Multiplicative.toAdd u)
  have hf : IsCoord (lmG F) H ⊥ π' f := by
    refine IsCoord.mk ?_ ?_ ?_ ?_ ?_
    · intro u u'
      change φ (Multiplicative.toAdd (u * u')) =
        φ (Multiplicative.toAdd u) + φ (Multiplicative.toAdd u')
      rw [show Multiplicative.toAdd (u * u') =
        Multiplicative.toAdd u + Multiplicative.toAdd u' from rfl, map_add]
    · intro u
      constructor
      · intro hu
        rw [Subgroup.mem_bot]
        have h1 : Multiplicative.toAdd u = 0 := by
          apply φ.injective
          simpa [f] using hu
        exact Multiplicative.toAdd.injective h1
      · intro hu
        rw [Subgroup.mem_bot] at hu
        rw [hu]
        simp [f]
    · intro v
      obtain ⟨y, rfl⟩ := φ.surjective v
      exact ⟨Multiplicative.ofAdd y, rfl⟩
    · intro γ u
      have hact : f (((π' γ : ↥H) : MulAut (Multiplicative Y)) u) =
          φ (π (ε (gamToSub γ)) (Multiplicative.toAdd u)) := by
        simp [f, π', lm, linearEquivToMulAut]
      have hlin : (lmG F).lin γ (f u) =
          JonesParshall.g2Act (ε (gamToSub γ)) (f u) := rfl
      rw [hact, hlin, hφ]
    · intro h
      obtain ⟨g, hgH, hg⟩ := Subgroup.mem_map.mp h.2
      obtain ⟨x, hx⟩ := hgH
      obtain ⟨γ, rfl⟩ := ε.surjective x
      refine ⟨γ, Subtype.ext ?_⟩
      rw [← hg]
      change lm (π (ε (gamToSub γ))) = lm g
      rw [show gamToSub γ = γ from rfl, hx]
  let A' : Subgroup (MulAut (Multiplicative Y)) := A.map lm
  have hcardA : Nat.card ↥A' = Nat.card ↥A :=
    Subgroup.card_map_of_injective (linearEquivToMulAut_injective Y)
  have hfix : Nat.card ↥(fixV A') = Nat.card {y : Y // ∀ a ∈ A, a y = y} := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun w => ⟨Multiplicative.toAdd w.1, fun a ha => ?_⟩
        invFun := fun y => ⟨Multiplicative.ofAdd y.1, fun a' ha' => ?_⟩
        left_inv := fun w => by ext; rfl
        right_inv := fun y => by ext; rfl }
    · have hw := w.2 (lm a) (Subgroup.mem_map_of_mem _ ha)
      simpa [lm, linearEquivToMulAut] using congrArg Multiplicative.toAdd hw
    · obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp ha'
      exact congrArg (fun x => Multiplicative.ofAdd x) (y.2 a ha)
  have hcardW : Nat.card (Multiplicative Y) = Nat.card Y := Nat.card_congr Multiplicative.toAdd
  haveI hAeI : CFSG.IsElementaryAbelian 2 ↥A := hAe
  have hA'e : IsElemAbelian2 A' := by
    constructor
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact congrArg Subtype.val (hAe.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow]
      have h2 : a ^ 2 = 1 := by
        rw [pow_two]
        exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) a ha
      rw [h2, map_one]
  have hAN : A' ≤ Subgroup.normalizer (H : Set (MulAut (Multiplicative Y))) := by
    rw [Subgroup.le_normalizer_iff]
    rintro _ ⟨a, ha, rfl⟩ x hx
    obtain ⟨g, hgH, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨xg, hxg⟩ := hgH
    rw [← hxg]
    obtain ⟨y, hy⟩ := hnorm a ha xg
    rw [← map_mul, ← map_inv, ← map_mul, hy]
    exact Subgroup.mem_map_of_mem _ ⟨y, rfl⟩
  have hA'1 : A' ≠ ⊥ := by
    intro hbot
    apply hA1
    rw [eq_bot_iff]
    intro a ha
    have hmem : lm a ∈ A' := Subgroup.mem_map_of_mem _ ha
    rw [hbot, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]
    exact (linearEquivToMulAut_injective Y) (by simpa [lm] using hmem)
  have hoff' : Nat.card (Multiplicative Y) ≤
      Nat.card ↥A' * Nat.card ↥(fixV A') := by
    rw [hcardW, hcardA, hfix]
    exact hoff
  have hfacts := B42G2.offender_facts (K := F) hNatF hn hf hAN hA'e
  have hineq' := hfacts.1
  rw [hcardW, hcardA, hfix] at hineq'
  refine ⟨?_, hineq'⟩
  have hle' : A' ≤ H := (hfacts.2 hA'1 hoff').1
  intro a ha
  have hmem : lm a ∈ H := hle' (Subgroup.mem_map_of_mem _ ha)
  obtain ⟨g, hg, hgg⟩ := Subgroup.mem_map.mp hmem
  obtain ⟨x, hx⟩ := hg
  refine ⟨x, ?_⟩
  have hga : g = a := (linearEquivToMulAut_injective Y) (by simpa [lm] using hgg)
  exact hx.trans hga

end NaturalOffender

section CoreInner

variable {K : Type} [Group K] [Finite K] {L B : Subgroup K} (h : InnerCtx L B)
  {F : Type} [Field F] [Fintype F] {n : ℕ} (hn : 2 ≤ n) (hF : Fintype.card F = 2 ^ n)
  (e : ↥L ≃* ↥(quasithinG2 F))
  {Z : Type} [AddCommGroup Z] [Module (ZMod 2) Z] [Finite Z]
  {κ : Representation (ZMod 2) K Z}

theorem core_inner_g2 (h : InnerCtx L B) (hn : 2 ≤ n) (hF : Fintype.card F = 2 ^ n)
    (e : ↥L ≃* ↥(quasithinG2 F)) (hd : ChiefData L B κ) :
    ∀ b ∈ B, ∃ l ∈ L, ConjAgree L b l := by
  classical
  haveI := hd.nontrivial
  have hNatF : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card]; exact hF
  haveI : CharP F 2 := CFSG.Quasithin.B42G2Id.charP_two_of_card hNatF
  have hperf : commutator ↥L = ⊤ := h.quasi.1
  have hZbot : Subgroup.center ↥L = ⊥ := by
    have hmap : (Subgroup.center ↥L).map (e : ↥L →* ↥(quasithinG2 F)) = ⊥ := by
      rw [Subgroup.map_center_eq (e : ↥L ≃* ↥(quasithinG2 F)),
        CFSG.Quasithin.H13.Ch4.FFG2.center_quasithinG2_eq_bot hn hNatF]
    exact (Subgroup.map_eq_bot_iff_of_injective
      (H := Subgroup.center ↥L) (f := (e : ↥L →* ↥(quasithinG2 F))) e.injective).mp hmap
  have hLsimple : IsSimpleGroup ↥L :=
    CFSG.Quasithin.H13.Ch4.FFG2.isSimpleGroup_of_quasisimple
      ((CFSG.Quasithin.A3.isQuasisimple_iff_open (Q := ↥L)).mpr h.quasi) hZbot
  obtain ⟨Y, hY⟩ := exists_lMin L κ
  haveI : Nontrivial ↥Y := (Submodule.nontrivial_iff_ne_bot).mpr hY.ne_bot
  have hnt := hY.nontriv h hd
  have hY4 : 4 < Nat.card ↥Y := inner_four_lt_card hperf hY.inv hnt
  have hBN : B ≤ Subgroup.normalizer (L : Set K) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr h.normal_L]
    exact le_top
  have hrel2 := g2_relIndex_innerPart_le_two h hn hF e
  have hcard_inner : Nat.card ↥(innerPart L B) * (innerPart L B).relIndex B = Nat.card ↥B := by
    have h1 := Subgroup.card_mul_index ((innerPart L B).subgroupOf B)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (innerPart_le L B)).toEquiv] at h1
    exact h1
  have hinner_le : Nat.card ↥(innerPart L B) ≤ Nat.card ↥(stabIn h κ Y) := by
    refine Nat.card_le_card_of_injective
      (Subgroup.inclusion (innerPart_le_stab h κ hd.irr hY.inv)) ?_
    exact Subgroup.inclusion_injective _
  have hB2 : Nat.card ↥B ≤ 2 * Nat.card ↥(stabIn h κ Y) := by
    rw [← hcard_inner]
    calc Nat.card ↥(innerPart L B) * (innerPart L B).relIndex B
        ≤ Nat.card ↥(stabIn h κ Y) * 2 := Nat.mul_le_mul hinner_le hrel2
      _ = 2 * Nat.card ↥(stabIn h κ Y) := by rw [mul_comm]
  let κY : Representation (ZMod 2) ↥L ↥Y :=
    (⟨Y, fun l _ hv => hY.inv l l.2 _ hv⟩ : Subrepresentation (κ.comp L.subtype)).toRepresentation
  let πL : ↥L →* (↥Y ≃ₗ[ZMod 2] ↥Y) := repGL κY
  let eC : ↥L ≃* ↥(cayleyGroup F) :=
    e.trans (MulEquiv.subgroupCongr CFSG.Quasithin.G11.P3G2.quasithinG2_eq_cayleyGroup)
  let πC : ↥(cayleyGroup F) →* (↥Y ≃ₗ[ZMod 2] ↥Y) := πL.comp eC.symm.toMonoidHom
  have hπL : Function.Injective πL := by
    rw [← MonoidHom.ker_eq_bot_iff]
    have hne : (repGL κY).ker ≠ ⊤ := by
      intro htop
      obtain ⟨l, hl, y, hy, hne⟩ := hnt
      have hmem : (⟨l, hl⟩ : ↥L) ∈ (repGL κY).ker := by rw [htop]; exact Subgroup.mem_top _
      rw [MonoidHom.mem_ker] at hmem
      have h1 := congrArg (fun f : ↥Y ≃ₗ[ZMod 2] ↥Y =>
        (((f ⟨y, hy⟩ : ↥Y) : Z))) hmem
      have hκ : (((κY ⟨l, hl⟩) ⟨y, hy⟩ : ↥Y) : Z) = κ l y := rfl
      exact hne (by simpa [repGL_apply, hκ] using h1)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (repGL κY).ker with hbot | htop
    · exact hbot
    · exact absurd htop hne
  have hπC : Function.Injective πC := by
    intro g g' hgg
    apply eC.symm.injective
    exact hπL hgg
  have hπCcoe : ∀ (g : ↥(cayleyGroup F)) (y : ↥Y),
      (((πC g) y : ↥Y) : Z) = κ ((eC.symm g : ↥L) : K) y := fun g y => rfl
  have hirrC : ∀ U : Submodule (ZMod 2) ↥Y,
      (∀ g, ∀ u ∈ U, πC g u ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    have hinv : ∀ l ∈ L, ∀ w ∈ U.map Y.subtype, κ l w ∈ U.map Y.subtype := by
      rintro l hl _ ⟨w, hw, rfl⟩
      refine ⟨πL ⟨l, hl⟩ w, ?_, rfl⟩
      have h1 : πC (eC ⟨l, hl⟩) = πL ⟨l, hl⟩ := by
        ext y
        simp [πC]
      rw [← h1]
      exact hU (eC ⟨l, hl⟩) w hw
    rcases hY.min _ (Submodule.map_subtype_le _ _) hinv with hbot | htop
    · left
      exact Submodule.map_injective_of_injective Y.injective_subtype (by rw [hbot, Submodule.map_bot])
    · right
      exact Submodule.map_injective_of_injective Y.injective_subtype
        (by rw [htop, Submodule.map_subtype_top])
  have hnormC : ∀ a ∈ stabImage h κ Y, ∀ g : ↥(cayleyGroup F),
      ∃ g' : ↥(cayleyGroup F), a * πC g * a⁻¹ = πC g' := by
    intro a ha g
    obtain ⟨b, hb, hab⟩ := (mem_stabImage h κ Y).mp ha
    have hbB : (b : K) ∈ B := hb.1
    let l : ↥L := eC.symm g
    have hconj : (b : K) * (l : K) * (b : K)⁻¹ ∈ L := h.normalizes b hbB l l.2
    refine ⟨eC ⟨(b : K) * (l : K) * (b : K)⁻¹, hconj⟩, ?_⟩
    have ha_inv : a⁻¹ = a := by
      have h2 : a * a = (1 : ↥Y ≃ₗ[ZMod 2] ↥Y) := stabImage_sq h κ Y a ha
      exact inv_eq_of_mul_eq_one_right h2
    ext w
    have h3 : ((a⁻¹ w : ↥Y) : Z) = κ (b : K)⁻¹ (w : Z) := by
      rw [ha_inv, hab w, InnerCtx.inv_eq h hbB]
    calc ((a * πC g * a⁻¹) w : Z)
        = κ (b : K) (((πC g) (a⁻¹ w) : ↥Y) : Z) := hab _
      _ = κ (b : K) (κ ((eC.symm g : ↥L) : K) (a⁻¹ w)) := by rw [hπCcoe]
      _ = κ (b : K) (κ ((eC.symm g : ↥L) : K) (κ (b : K)⁻¹ (w : Z))) := by rw [h3]
      _ = κ ((b : K) * (l : K) * (b : K)⁻¹) (w : Z) := by
          rw [show (b : K)⁻¹ = (b : K) from InnerCtx.inv_eq h hbB]
          rw [← repMulApply, ← repMulApply]
      _ = (((πC (eC ⟨(b : K) * (l : K) * (b : K)⁻¹, hconj⟩)) w : ↥Y) : Z) := by
          rw [hπCcoe]
          simp
  by_cases hall : ∀ b ∈ B, b ∈ stabIn h κ Y
  ·
    have hB1 : stabIn h κ Y = B := le_antisymm (stabIn_le h κ Y) hall
    have hYtop : Y = ⊤ := hY.eq_top_of_stab h hd hall
    have hzY : ∀ z : Z, z ∈ Y := fun z => by rw [hYtop]; exact Submodule.mem_top
    have hYZ : Nat.card ↥Y = Nat.card Z := by
      rw [hYtop]
      exact Nat.card_congr Submodule.topEquiv.toEquiv
    have hfixZ : Nat.card ↥(fixSub κ (stabIn h κ Y) ⊓ Y) =
        Nat.card {z : Z // ∀ b ∈ B, κ b z = z} := by
      refine Nat.card_congr ?_
      refine
        { toFun := fun w => ⟨w.1, fun b hb => ?_⟩
          invFun := fun z => ⟨z.1, mem_fixSub.mpr fun b hb => z.2 b hb.1, hzY z.1⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      exact mem_fixSub.mp w.2.1 b (hall b hb)
    have hNpos : 0 < Nat.card ↥(B ⊓ MonoidHom.ker κ) := Nat.card_pos
    have hcardA : Nat.card ↥(stabIn h κ Y) =
        Nat.card ↥(B ⊓ MonoidHom.ker κ) * Nat.card ↥(stabImage h κ Y) :=
      card_stabIn h hd hY hnt
    have hfixA : Nat.card {y : ↥Y // ∀ a ∈ stabImage h κ Y, a y = y} =
        Nat.card ↥(fixSub κ (stabIn h κ Y) ⊓ Y) := card_fix_stabImage h κ Y
    have he1 : Nat.card Z * Nat.card ↥(B ⊓ MonoidHom.ker κ) ≤
        (Nat.card ↥(B ⊓ MonoidHom.ker κ) * Nat.card ↥(stabImage h κ Y)) *
          Nat.card {y : ↥Y // ∀ a ∈ stabImage h κ Y, a y = y} := by
      calc Nat.card Z * Nat.card ↥(B ⊓ MonoidHom.ker κ)
          ≤ Nat.card ↥B * Nat.card {z : Z // ∀ b ∈ B, κ b z = z} := hd.budget
        _ = Nat.card ↥(stabIn h κ Y) * Nat.card {z : Z // ∀ b ∈ B, κ b z = z} := by
            rw [hB1]
        _ = Nat.card ↥(stabIn h κ Y) * Nat.card ↥(fixSub κ (stabIn h κ Y) ⊓ Y) := by
            rw [← hfixZ]
        _ = (Nat.card ↥(B ⊓ MonoidHom.ker κ) * Nat.card ↥(stabImage h κ Y)) *
              Nat.card {y : ↥Y // ∀ a ∈ stabImage h κ Y, a y = y} := by
            rw [hcardA, ← hfixA]
    have hoff : Nat.card ↥Y ≤ Nat.card ↥(stabImage h κ Y) *
        Nat.card {y : ↥Y // ∀ a ∈ stabImage h κ Y, a y = y} := by
      refine Nat.le_of_mul_le_mul_left ?_ hNpos
      calc Nat.card ↥(B ⊓ MonoidHom.ker κ) * Nat.card ↥Y
          = Nat.card Z * Nat.card ↥(B ⊓ MonoidHom.ker κ) := by rw [hYZ, mul_comm]
        _ ≤ (Nat.card ↥(B ⊓ MonoidHom.ker κ) * Nat.card ↥(stabImage h κ Y)) *
            Nat.card {y : ↥Y // ∀ a ∈ stabImage h κ Y, a y = y} := he1
        _ = Nat.card ↥(B ⊓ MonoidHom.ker κ) *
            (Nat.card ↥(stabImage h κ Y) *
              Nat.card {y : ↥Y // ∀ a ∈ stabImage h κ Y, a y = y}) := by ring
    have hAe : CFSG.IsElementaryAbelian 2 ↥(stabImage h κ Y) :=
      CFSG.IsElementaryAbelian.two_of_forall_mul_self (stabImage_comm h κ Y)
        (stabImage_sq h κ Y)
    by_cases hA0 : stabImage h κ Y = ⊥
    ·
      intro b hb
      refine ⟨1, L.one_mem, h.conjAgree_of_kappa_eq κ hd.hL fun z => ?_⟩
      have hmem : repGL (stabRep h κ Y) ⟨b, hall b hb⟩ ∈ stabImage h κ Y :=
        ⟨⟨b, hall b hb⟩, rfl⟩
      rw [hA0, Subgroup.mem_bot] at hmem
      have h1 := congrArg (fun a : ↥Y ≃ₗ[ZMod 2] ↥Y => (((a ⟨z, hzY z⟩ : ↥Y) : Z))) hmem
      simpa [repGL_apply, stabRep_coe] using h1
    ·
      obtain ⟨hAle, -⟩ := g2_offender_facts_of_natural hn hF πC hπC inferInstance hirrC
        (stabImage h κ Y) hnormC hAe hA0 hoff
      intro b hb
      have hmem : repGL (stabRep h κ Y) ⟨b, hall b hb⟩ ∈ stabImage h κ Y :=
        ⟨⟨b, hall b hb⟩, rfl⟩
      obtain ⟨g, hg⟩ := hAle hmem
      refine ⟨(eC.symm g : ↥L), (eC.symm g).2, h.conjAgree_of_kappa_eq κ hd.hL fun z => ?_⟩
      have h1 := congrArg (fun a : ↥Y ≃ₗ[ZMod 2] ↥Y => (((a ⟨z, hzY z⟩ : ↥Y) : Z))) hg
      simpa [hπCcoe, repGL_apply, stabRep_coe] using h1.symm
  ·
    push Not at hall
    obtain ⟨a, ha, hna⟩ := hall
    exfalso
    have hsq2 := card_inner_sq_le h hd hY ha hna
    have hmain : Nat.card ↥Y * Nat.card ↥Y ≤ 2 * (Nat.card ↥(stabImage h κ Y) *
        Nat.card {y : ↥Y // ∀ a ∈ stabImage h κ Y, a y = y}) := by
      refine Nat.le_of_mul_le_mul_left ?_ (Nat.card_pos (α := ↥(B ⊓ MonoidHom.ker κ)))
      calc Nat.card ↥(B ⊓ MonoidHom.ker κ) * (Nat.card ↥Y * Nat.card ↥Y)
          = Nat.card ↥(B ⊓ MonoidHom.ker κ) * Nat.card ↥Y ^ 2 := by ring
        _ ≤ Nat.card ↥B * Nat.card ↥(fixSub κ (stabIn h κ Y) ⊓ Y) := hsq2
        _ ≤ (2 * Nat.card ↥(stabIn h κ Y)) *
            Nat.card ↥(fixSub κ (stabIn h κ Y) ⊓ Y) := Nat.mul_le_mul_right _ hB2
        _ = Nat.card ↥(B ⊓ MonoidHom.ker κ) * (2 * (Nat.card ↥(stabImage h κ Y) *
            Nat.card {y : ↥Y // ∀ a ∈ stabImage h κ Y, a y = y})) := by
            rw [card_stabIn h hd hY hnt, ← card_fix_stabImage h κ Y]
            ring
    have hAe : CFSG.IsElementaryAbelian 2 ↥(stabImage h κ Y) :=
      CFSG.IsElementaryAbelian.two_of_forall_mul_self (stabImage_comm h κ Y)
        (stabImage_sq h κ Y)
    have hA1 : stabImage h κ Y ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hmain
      have h2 : Nat.card ↥Y * Nat.card ↥Y ≤ 2 * Nat.card ↥Y := by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hmain
      have hpos : 0 < Nat.card ↥Y := Nat.card_pos
      have h3 : Nat.card ↥Y ≤ 2 := by
        exact Nat.le_of_mul_le_mul_left (by simpa [pow_two, mul_comm, mul_left_comm] using h2) hpos
      omega
    have hoff : Nat.card ↥Y ≤ Nat.card ↥(stabImage h κ Y) *
        Nat.card {y : ↥Y // ∀ a ∈ stabImage h κ Y, a y = y} := by
      by_contra hlt
      push Not at hlt
      have h2 : Nat.card ↥Y * Nat.card ↥Y ≤ 2 * Nat.card ↥Y := by
        calc Nat.card ↥Y * Nat.card ↥Y
            ≤ 2 * (Nat.card ↥(stabImage h κ Y) *
                Nat.card {y : ↥Y // ∀ a ∈ stabImage h κ Y, a y = y}) := hmain
          _ ≤ 2 * Nat.card ↥Y := Nat.mul_le_mul_left 2 hlt.le
      have hpos : 0 < Nat.card ↥Y := Nat.card_pos
      have h3 : Nat.card ↥Y ≤ 2 :=
        Nat.le_of_mul_le_mul_left (by simpa [pow_two, mul_comm, mul_left_comm] using h2) hpos
      omega
    obtain ⟨-, hineq⟩ := g2_offender_facts_of_natural hn hF πC hπC inferInstance hirrC
      (stabImage h κ Y) hnormC hAe hA1 hoff
    have h2 : Nat.card ↥Y * Nat.card ↥Y ≤ 2 * Nat.card ↥Y := by
      calc Nat.card ↥Y * Nat.card ↥Y
          ≤ 2 * (Nat.card ↥(stabImage h κ Y) *
              Nat.card {y : ↥Y // ∀ a ∈ stabImage h κ Y, a y = y}) := hmain
        _ ≤ 2 * Nat.card ↥Y := Nat.mul_le_mul_left 2 hineq
    have hpos : 0 < Nat.card ↥Y := Nat.card_pos
    have h3 : Nat.card ↥Y ≤ 2 :=
      Nat.le_of_mul_le_mul_left (by simpa [pow_two, mul_comm, mul_left_comm] using h2) hpos
    omega

end CoreInner

theorem g2_center_eq_bot {L : Type*} [Group L] {F : Type} [Field F] [Fintype F] {n : ℕ}
    (hn : 2 ≤ n) (hF : Fintype.card F = 2 ^ n) (e : L ≃* ↥(quasithinG2 F)) :
    Subgroup.center L = ⊥ := by
  have hNatF : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card]; exact hF
  have hmap : (Subgroup.center L).map (e : L →* ↥(quasithinG2 F)) = ⊥ := by
    rw [Subgroup.map_center_eq e,
      CFSG.Quasithin.H13.Ch4.FFG2.center_quasithinG2_eq_bot hn hNatF]
  exact (Subgroup.map_eq_bot_iff_of_injective
    (H := Subgroup.center L) (f := (e : L →* ↥(quasithinG2 F))) e.injective).mp hmap

section StrictMin

variable {G : Type} [Group G] [Finite G] {V : Type} [AddCommGroup V]
  [Module (ZMod 2) V] [Finite V]
  {F : Type} [Field F] [Fintype F] {n : ℕ} (hn : 2 ≤ n) (hF : Fintype.card F = 2 ^ n)

theorem strictMin_inner_g2 (hn : 2 ≤ n) (hF : Fintype.card F = 2 ^ n)
    (ρ : Representation (ZMod 2) G V) (L B : Subgroup G)
    {U : Submodule (ZMod 2) V} (e : ↥L ≃* ↥(quasithinG2 F))
    (hquasi : CFSG.Open.IsQuasisimple ↥L)
    (hBN : ∀ b ∈ B, ∀ l ∈ L, b * l * b⁻¹ ∈ L) (hB2 : ∀ b ∈ B, b * b = 1)
    (hBc : ∀ b ∈ B, ∀ c ∈ B, b * c = c * b) (hinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) U)
    (hLnt : ¬ L ≤ cenOn ρ L U) (hbest : IsBestOffenderOn ρ B U)
    (hquad : IsQuadraticOn ρ B U)
    (hmove : ∀ b ∈ B, b ∉ cenOn ρ B U → ∃ k ∈ L, ∃ u ∈ U, ρ b (ρ k u) ≠ ρ k (ρ b u)) :
    ∀ b ∈ B, ∃ l ∈ L, ConjAgree L b l := by
  classical
  have hZbot : Subgroup.center ↥L = ⊥ := g2_center_eq_bot hn hF e
  have hZ' : ∀ z ∈ Subgroup.center ↥L, z ^ 3 = 1 := by
    intro z hz
    have hz1 : z = 1 := by
      rw [hZbot, Subgroup.mem_bot] at hz
      exact hz
    rw [hz1, one_pow]
  have hZ : ∀ z ∈ L, (∀ k ∈ L, k * z = z * k) → z ^ 3 = 1 := by
    intro z hz hzc
    have hmem : (⟨z, hz⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hzc g g.2)
    simpa using congrArg Subtype.val (hZ' _ hmem)
  have hctx := innerCtx_of_subgroups hBN hquasi hZ hB2 hBc
  obtain ⟨Z, iA, iM, iF, κ, hd⟩ :=
    exists_chief_factor (ρ := ρ) (L := L) (B := B) (U := U)
      hctx hinv hLnt hbest hquad (fun b hb hnb => hmove b hb hnb)
  have e' : ↥(L.subgroupOf (L ⊔ B)) ≃* ↥(quasithinG2 F) :=
    (Subgroup.subgroupOfEquivOfLe le_sup_left).trans e
  have hcore := core_inner_g2 hctx hn hF e' hd
  intro b hb
  obtain ⟨l, hl, hag⟩ := hcore ⟨b, Subgroup.mem_sup_right hb⟩ (Subgroup.mem_subgroupOf.mpr hb)
  refine ⟨(l : G), Subgroup.mem_subgroupOf.mp hl, fun k hk => ?_⟩
  have h1 := hag ⟨k, Subgroup.mem_sup_left hk⟩ (Subgroup.mem_subgroupOf.mpr hk)
  simpa using congrArg Subtype.val h1

end StrictMin

end CFSG.LocalAnalysis.RankThreeUC.S15

