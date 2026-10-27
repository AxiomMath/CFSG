module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256m2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Chev2SporCheck
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Chev2SporThreeSmall
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Chev2SporJ3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Chev2SporLarge
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Chev2SporHe3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Chev2SporRu3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Chev2SporSuz
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Chev2SporCo
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Chev2SporFi23
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Chev2SporHN3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Chev2SporLy
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Chev2SporTh
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporCo1ThreeTwo
public import CFSG.Adapters.LieModelSmallOrders
public import CFSG.HardMathSupport.Dickson.BMRows.CensusB3
public import CFSG.HardMathSupport.Dickson.BMRows.CensusM3

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256o

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple PSimple catalogIs onLie ambiguousChev)
open CFSG.LocalAnalysis.GLTheoremA (chev2Spor chev2L34 chev2Small)
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256m (IsGF4Type)

section Free

theorem isChevSimple_two_of_isGF4Type {X : Type} [Group X] (h : IsGF4Type X) : IsChevSimple 2 X := by
  obtain ⟨d', hd2, -, he⟩ := h
  exact Or.inl ⟨.lie d', hd2, he⟩

theorem card_psl_two_two_pow {n : ℕ} (hn : n ≠ 0) :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n hn
  rw [CFSG.OrderReductions.LinearOrders.card_projectiveSpecialLinear (GaloisField 2 n) 2 (by norm_num), hE]
  have hodd : Odd (2 ^ n - 1) := by
    have he : Even (2 ^ n) := (by decide : Even 2).pow_of_ne_zero hn
    exact Nat.Even.sub_odd (Nat.one_le_two_pow) he odd_one
  have hg : Nat.gcd 2 (2 ^ n - 1) = 1 := Nat.coprime_two_left.mpr hodd
  rw [hg, Nat.div_one, Finset.Icc_self, Finset.prod_singleton]
  norm_num

theorem not_isL2TwoPowOdd_of_card_20160 {X : Type} [Group X] (hX : Nat.card X = 20160) :
    ¬ CFSG.HardMathSupport.Timmesfeld.ComponentBalance.IsL2TwoPowOdd X := by
  rintro ⟨n, hn, hn1, ⟨f⟩⟩
  have hc := (Nat.card_congr f.toEquiv).symm.trans hX
  rw [card_psl_two_two_pow (by omega)] at hc
  have hodd : Odd ((2 ^ n) ^ 2 - 1) := by
    have he : Even ((2 ^ n) ^ 2) := ((by decide : Even 2).pow_of_ne_zero (by omega)).pow_of_ne_zero (by norm_num)
    exact Nat.Even.sub_odd (Nat.one_le_pow _ _ (Nat.two_pow_pos n)) he odd_one
  have h6 : n = 6 := CFSG.Timmesfeld.Orders.eq_of_two_pow_mul_odd (a := n) (b := 6) hodd
    (by decide : Odd 315) (hc.trans (by norm_num))
  rw [h6] at hn
  exact absurd hn (by decide)

theorem card_dvd_card_mulAut_of_trivial_center {X : Type} [Group X] (hZ : Subgroup.center X = ⊥) :
    Nat.card X ∣ Nat.card (MulAut X) := by
  refine Subgroup.card_dvd_of_injective (MulAut.conj : X →* MulAut X) fun a b hab => ?_
  have h : ∀ x : X, a * x * a⁻¹ = b * x * b⁻¹ := fun x => by
    have := congrArg (fun φ : MulAut X => φ x) hab
    simpa only [MulAut.conj_apply] using this
  have hc : b⁻¹ * a ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro g
    calc g * (b⁻¹ * a) = b⁻¹ * (b * g * b⁻¹) * a := by group
      _ = b⁻¹ * (a * g * a⁻¹) * a := by rw [← h g]
      _ = b⁻¹ * a * g := by group
  rw [hZ, Subgroup.mem_bot] at hc
  exact (inv_mul_eq_one.1 hc).symm

end Free

section TypeLevel


theorem not_isGF4Type_of_alt {X : Type} [Group X] {m : ℕ} (hm : 5 ≤ m)
    (e : X ≃* alternatingGroup (Fin m)) : ¬ IsGF4Type X := by
  rintro ⟨d', -, -, ⟨f⟩⟩
  exact (AltFacts4.inputAltNotLie_holds m d' hm).false (e.symm.trans f)

theorem not_isGF4Type_of_oddChar {X : Type} [Group X] {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {d : TauCeti.ValidLieTypeIndex} (hd : d.1.characteristic = r)
    (e : X ≃* (TauCeti.CFSGIndex.lie d).Group) : ¬ IsGF4Type X := by
  rintro ⟨d', hd2, hk, ⟨e'⟩⟩
  obtain ⟨t, n, f, hM, hf, h22⟩ := Inputs256m.exists_lieModel_two_even_of_gf4 d' hd2 hk e'
  have hodd := CFSG.LocalAnalysis.GLTheoremA.small_odd_lie hr hr2 hd e
  rcases CFSG.SeitzReduction.CrossChar.eq_of_lieModel_two_of_oddLieType' hM hodd with
    ⟨h1, h2, h3⟩ | ⟨-, -, h3⟩ | ⟨-, -, h3⟩
  · exact h22 ⟨h1, h2, h3⟩
  · exact absurd (h3 ▸ hf) (by decide)
  · exact absurd (h3 ▸ hf) (by decide)

theorem not_isGF4Type_of_isChevSimple_three {X : Type} [Group X] (h : IsChevSimple 3 X) :
    ¬ IsGF4Type X :=
  fun hX => Inputs256m.not_isChevSimple_three_of_isGF4Type hX h

theorem chev2L34_of_isGF4Type {X : Type} [Group X] (h : IsGF4Type X) (hc : catalogIs X chev2Spor) :
    catalogIs X chev2L34 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := hc
  rcases hi with hi | hi
  · exfalso
    cases i with
    | cyclic p hp => exact absurd hi (by simp [chev2Small])
    | sporadic s => exact absurd hi (by simp [chev2Small])
    | alternating n hn => exact not_isGF4Type_of_alt hn e h
    | lie d =>
      obtain ⟨d, hv⟩ := d
      cases d with
      | A r q =>
        cases r with
        | zero => exact absurd hi (by simp [chev2Small])
        | succ r =>
          cases r with
          | zero =>
            have hq : q.card = 7 ∨ q.card = 8 := hi
            rcases hq with hq | hq
            · obtain ⟨hp7, -⟩ := CFSG.LocalAnalysis.GLTheoremA.primePower_eq_of_card_eq (r := 7) (s := 1)
                (by norm_num) (by norm_num) (hq.trans (by norm_num))
              exact not_isGF4Type_of_oddChar (r := 7) (by norm_num) (by norm_num)
                (d := ⟨.A 1 q, hv⟩) (by simpa using hp7) e h
            · exact not_isGF4Type_of_isChevSimple_three
                (Or.inr ⟨.lie ⟨.A 1 q, hv⟩, Or.inr ⟨hq, rfl⟩, ⟨e⟩⟩) h
          | succ r => exact absurd hi (by simp [chev2Small])
      | twistedA r q =>
        rcases Nat.lt_or_ge r 4 with hr4 | hr4
        · interval_cases r
          · exact absurd hi (by simp [chev2Small])
          · exact absurd hi (by simp [chev2Small])
          · have hq : q.card = 3 := hi
            obtain ⟨hp3, -⟩ := CFSG.LocalAnalysis.GLTheoremA.primePower_eq_of_card_eq (r := 3) (s := 1)
              Nat.prime_three (by norm_num) (hq.trans (by norm_num))
            exact not_isGF4Type_of_isChevSimple_three (Or.inl ⟨.lie ⟨.twistedA 2 q, hv⟩, by simpa [onLie] using hp3, ⟨e⟩⟩) h
          · have hq : q.card = 2 := hi
            exact not_isGF4Type_of_isChevSimple_three
              (Or.inr ⟨.lie ⟨.twistedA 3 q, hv⟩, ⟨hq, rfl⟩, ⟨e⟩⟩) h
        · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 4 := ⟨r - 4, by omega⟩
          exact absurd hi (by simp [chev2Small])
      | _ => exact absurd hi (by simp [chev2Small])
  · exact ⟨i, hi, ⟨e⟩⟩

theorem false_of_chev2L34_of_typeOK {X : Type} [Group X] (hL : catalogIs X chev2L34)
    (hT : CFSG.LocalAnalysis.GLTheoremA.I1416Rows.TypeOK 3 X) : False := by
  obtain ⟨i, hi, ⟨e⟩⟩ := hL
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d with
    | A r q =>
      cases r with
      | zero => exact absurd hi (by simp [chev2L34])
      | succ r =>
        cases r with
        | zero => exact absurd hi (by simp [chev2L34])
        | succ r =>
          cases r with
          | succ r => exact absurd hi (by simp [chev2L34])
          | zero =>
            have hq : q.card = 4 := hi
            obtain ⟨hp2, he2⟩ := CFSG.LocalAnalysis.GLTheoremA.primePower_eq_of_card_eq (r := 2) (s := 2)
              Nat.prime_two (by norm_num) (hq.trans (by norm_num))
            have hGF4 : IsGF4Type X :=
              ⟨⟨.A 2 q, hv⟩, by simpa using hp2, ⟨1, le_rfl, by rw [pow_one]; exact hq⟩, ⟨e⟩⟩
            have hM := CFSG.Models.lieModel_A 2 q hv e
            rw [hp2, he2] at hM
            have hB := CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel
              (by simp [CFSG.Blueprint.classicalTags]) hM
            have hcard : Nat.card X = 20160 := CFSG.Blueprint.LieModel.card_psl_three_four hB
            haveI : Finite X := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
            haveI : IsSimpleGroup X :=
              (MulEquiv.isSimpleGroup_congr e).2 (CFSG.Assembly.lie_finite_simple ⟨.A 2 q, hv⟩).2
            have hnab : ∃ a b : X, a * b ≠ b * a := by
              by_contra hcon
              push Not at hcon
              letI : CommGroup X := { (inferInstance : Group X) with mul_comm := hcon }
              have hpr := IsSimpleGroup.prime_card (α := X)
              rw [hcard] at hpr
              norm_num at hpr
            have hZ : Subgroup.center X = ⊥ := by
              rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
              · exact h
              · exfalso
                obtain ⟨a, b, hab⟩ := hnab
                exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
            have h9 : 3 ^ 2 ∣ Nat.card (MulAut X) :=
              (show 3 ^ 2 ∣ Nat.card X by rw [hcard]; norm_num).trans
                (card_dvd_card_mulAut_of_trivial_center hZ)
            obtain ⟨-, j, hj, ⟨f⟩⟩ := hT (isChevSimple_two_of_isGF4Type hGF4) h9
              (fun h => not_isL2TwoPowOdd_of_card_20160 hcard h.2)
            rcases hj with hj | hj | hj | hj
            · cases j with
              | alternating m hm => exact not_isGF4Type_of_alt hm f hGF4
              | _ => exact hj.elim
            · cases j with
              | alternating m hm => exact not_isGF4Type_of_alt hm f hGF4
              | _ => exact hj.elim
            · cases j with
              | lie d' =>
                obtain ⟨d', hv'⟩ := d'
                cases d' with
                | twistedA r' q' =>
                  rcases Nat.lt_or_ge r' 3 with hr3 | hr3
                  · interval_cases r'
                    · exact absurd hj (by simp [CFSG.LocalAnalysis.GLTheoremA.isG2der, onLie])
                    · exact absurd hj (by simp [CFSG.LocalAnalysis.GLTheoremA.isG2der, onLie])
                    · have hq' : q'.card = 3 := hj
                      obtain ⟨hp3, -⟩ := CFSG.LocalAnalysis.GLTheoremA.primePower_eq_of_card_eq (r := 3) (s := 1)
                        Nat.prime_three (by norm_num) (hq'.trans (by norm_num))
                      exact not_isGF4Type_of_isChevSimple_three
                        (Or.inl ⟨.lie ⟨.twistedA 2 q', hv'⟩, by simpa [onLie] using hp3, ⟨f⟩⟩) hGF4
                  · obtain ⟨r'', rfl⟩ : ∃ r'', r' = r'' + 3 := ⟨r' - 3, by omega⟩
                    exact absurd hj (by simp [CFSG.LocalAnalysis.GLTheoremA.isG2der, onLie])
                | _ => exact absurd hj (by simp [CFSG.LocalAnalysis.GLTheoremA.isG2der, onLie])
              | _ => exact hj.elim
            · cases j with
              | lie d' =>
                obtain ⟨d', hv'⟩ := d'
                cases d' with
                | twistedA r' q' =>
                  rcases Nat.lt_or_ge r' 4 with hr4 | hr4
                  · interval_cases r'
                    · exact absurd hj (by simp [CFSG.LocalAnalysis.GLTheoremA.S9.isU4two, onLie])
                    · exact absurd hj (by simp [CFSG.LocalAnalysis.GLTheoremA.S9.isU4two, onLie])
                    · exact absurd hj (by simp [CFSG.LocalAnalysis.GLTheoremA.S9.isU4two, onLie])
                    · have hq' : q'.card = 2 := hj
                      exact not_isGF4Type_of_isChevSimple_three
                        (Or.inr ⟨.lie ⟨.twistedA 3 q', hv'⟩, ⟨hq', rfl⟩, ⟨f⟩⟩) hGF4
                  · obtain ⟨r'', rfl⟩ : ∃ r'', r' = r'' + 4 := ⟨r' - 4, by omega⟩
                    exact absurd hj (by simp [CFSG.LocalAnalysis.GLTheoremA.S9.isU4two, onLie])
                | _ => exact absurd hj (by simp [CFSG.LocalAnalysis.GLTheoremA.S9.isU4two, onLie])
              | _ => exact hj.elim
    | _ => exact absurd hi (by simp [chev2L34])

theorem not_isGF4Type_of_rows {s : TauCeti.SporadicName}
    (hC : CFSG.LocalAnalysis.GLTheoremA.Chev2Rows.CRow s 3)
    (hT : CFSG.LocalAnalysis.GLTheoremA.I1416Rows.I1416SporRow s 3)
    {S : Type} [Group S] [Finite S] (hs : Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    {α : MulAut S} (hα : α ^ 3 = 1) (hα1 : α ≠ 1) {I : Subgroup S}
    (hI : GLAPComponent 3 (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α) I) :
    ¬ IsGF4Type (PSimple 3 I) := by
  intro hG
  have hc := hC S hs Nat.prime_three (by norm_num) α hα hα1 I hI (isChevSimple_two_of_isGF4Type hG)
  exact false_of_chev2L34_of_typeOK (chev2L34_of_isGF4Type hG hc)
    (hT S hs Nat.prime_three (by norm_num) α hα hα1 I hI)

end TypeLevel


section Spor


theorem not_isGF4Type_of_sporadic {X : Type} [Group X] {s : TauCeti.SporadicName}
    (e : X ≃* (TauCeti.CFSGIndex.sporadic s).Group) : ¬ IsGF4Type X := by
  intro h
  have h2 := isChevSimple_two_of_isGF4Type h
  cases s
  case Co1 => exact CFSG.LocalAnalysis.GLTheoremA.No5.co1_not_chev2 e h2
  case J1 =>
    exact CFSG.LocalAnalysis.GLTheoremA.List93.not_chev2_spor (s := .J1) (a := 3) (m := 21945) (by decide)
      (by norm_num) (by decide) (by norm_num) (by decide +kernel) e h2
  case J2 =>
    exact CFSG.LocalAnalysis.GLTheoremA.List93.not_chev2_spor (s := .J2) (a := 7) (m := 4725) (by decide)
      (by norm_num) (by decide) (by norm_num) (by decide +kernel) e h2
  case M22 =>
    exact CFSG.LocalAnalysis.GLTheoremA.List93.not_chev2_spor (s := .M22) (a := 7) (m := 3465) (by decide)
      (by norm_num) (by decide) (by norm_num) (by decide +kernel) e h2
  case M23 =>
    exact CFSG.LocalAnalysis.GLTheoremA.List93.not_chev2_spor (s := .M23) (a := 7) (m := 79695) (by decide)
      (by norm_num) (by decide) (by norm_num) (by decide +kernel) e h2
  case M24 =>
    exact CFSG.LocalAnalysis.GLTheoremA.List93.not_chev2_spor (s := .M24) (a := 10) (m := 239085) (by decide)
      (by norm_num) (by decide) (by norm_num) (by decide +kernel) e h2
  case HN | HS | Ru =>
    exact CFSG.LocalAnalysis.GLTheoremA.List93.notChev2_holds X _
      (Or.inl ⟨_, rfl, 5, by simp [CFSG.Yardstones.Md0ec50421ce4.k2Spor]⟩) ⟨e⟩ h2
  case He =>
    exact CFSG.LocalAnalysis.GLTheoremA.List93.notChev2_holds X _
      (Or.inl ⟨_, rfl, 7, by simp [CFSG.Yardstones.Md0ec50421ce4.k2Spor]⟩) ⟨e⟩ h2
  case J4 | M12 =>
    exact CFSG.LocalAnalysis.GLTheoremA.List93.notChev2_holds X _
      (Or.inl ⟨_, rfl, 11, by simp [CFSG.Yardstones.Md0ec50421ce4.k2Spor]⟩) ⟨e⟩ h2
  all_goals
    exact CFSG.LocalAnalysis.GLTheoremA.List93.notChev2_holds X _
      (Or.inl ⟨_, rfl, 3, by simp [CFSG.Yardstones.Md0ec50421ce4.k2Spor]⟩) ⟨e⟩ h2

theorem not_isGF4Type_of_shapeM {G : Type} [Group G] {k : G}
    (h : CFSG.HardMathSupport.Dickson.I271.ShapeRkAt' 3
      (fun T _ => catalogIs T (fun i => i = .sporadic .Fi24Prime ∨ i = .sporadic .Th)) (fun _ _ => True) k)
    {J : Subgroup G} (hJ : GLAPComponent 3 (Subgroup.centralizer ({k} : Set G)) J) :
    ¬ IsGF4Type (PSimple 3 J) := by
  rcases h with hno | ⟨J0, -, huniq, hG, -⟩
  · exact (hno J hJ).elim
  · rw [huniq J hJ]
    obtain ⟨i, hi | hi, ⟨f⟩⟩ := hG <;> subst hi <;> exact not_isGF4Type_of_sporadic f

end Spor

section Framework

@[expose] def GF4FreeAtThree (Q : Type) [Group Q] : Prop :=
  ∀ x : Q, orderOf x = 3 → ∀ J : Subgroup Q,
    GLAPComponent 3 (Subgroup.centralizer ({x} : Set Q)) J → ¬ IsGF4Type (PSimple 3 J)

theorem GF4FreeAtThree.of_equiv {Q T : Type} [Group Q] [Group T] [Finite T] (e : T ≃* Q)
    (h : GF4FreeAtThree Q) : GF4FreeAtThree T := by
  intro s hs I hI hG
  have hs' : orderOf (e s) = 3 := by rw [MulEquiv.orderOf_eq, hs]
  obtain ⟨hI', ⟨f⟩⟩ := Inputs1415.comp_transport Nat.prime_three e hI
  exact h (e s) hs' _ hI' (hG.of_mulEquiv f.symm)

theorem gf4FreeAtThree_of_carrier (hBr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    {s : TauCeti.SporadicName} (h : GF4FreeAtThree (CFSG.Blueprint.NativeSporadic.Carrier s))
    {S : Type} [Group S] [Finite S] (hs : Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic s).Group)) :
    GF4FreeAtThree S :=
  h.of_equiv (hs.some.trans (hBr s).some.symm)

theorem not_isGF4Type_of_gf4FreeAtThree
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo) {S : Type} [Group S] [Finite S]
    (hS : IsSimpleGroup S) (hnc : ∃ a b : S, a * b ≠ b * a) {s : TauCeti.SporadicName} (hs : IsSporType s S)
    (h : GF4FreeAtThree S) {α : MulAut S} (hα : α ^ 3 = 1) (hα1 : α ≠ 1) {I : Subgroup S}
    (hI : GLAPComponent 3 (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α) I) :
    ¬ IsGF4Type (PSimple 3 I) := by
  haveI := hS
  have hcen : Subgroup.center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
  obtain ⟨x, rfl, hx3⟩ := CFSG.HardMathSupport.Solomon.Coordinator.exists_conj_of_pow Nat.prime_three
    (by norm_num) hcen (hOut S hS hnc s hs) α hα
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hα1 (map_one _)
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  rw [CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup_conj] at hI
  exact h x hxo I hI

theorem gf4FreeAtThree_of_not_sq_dvd {Q : Type} [Group Q] [Finite Q] (h : ¬ 3 ^ 2 ∣ Nat.card Q) :
    GF4FreeAtThree Q :=
  fun _ hx _ hJ => (CFSG.HardMathSupport.Solomon.Coordinator.no_glaPComponent_of_exact Nat.prime_three hx h hJ).elim

@[expose] def CentThreeBNoGF4 (G : Type) [Group G] : Prop :=
  ∀ k : G, orderOf k = 3 → ¬ CFSG.HardMathSupport.Timmesfeld.SporadicBalance.InvertedByTwoA k →
    ∀ J : Subgroup G, GLAPComponent 3 (Subgroup.centralizer ({k} : Set G)) J → ¬ IsGF4Type (PSimple 3 J)

theorem CentThreeBNoGF4.of_equiv {G G' : Type} [Group G] [Finite G] [Group G'] (e : G ≃* G')
    (h : CentThreeBNoGF4 G') : CentThreeBNoGF4 G := by
  intro k hk hinv J hJ hG
  have hinv' : ¬ CFSG.HardMathSupport.Timmesfeld.SporadicBalance.InvertedByTwoA (e k) := fun h' => hinv (by
    have := h'.map e.symm
    rwa [MulEquiv.symm_apply_apply] at this)
  obtain ⟨hJ', ⟨f⟩⟩ := Inputs1415.comp_transport Nat.prime_three e hJ
  exact h (e k) (by rw [MulEquiv.orderOf_eq]; exact hk) hinv' _ hJ' (hG.of_mulEquiv f.symm)

@[expose] def B3BNoGF4 : Prop :=
  ∀ s : CFSG.Blueprint.NativeSporadic.B, orderOf s = 3 →
    (∀ d : CFSG.Blueprint.NativeSporadic.B, CFSG.Monster.GMS.BabyInv 0 d → d * s * d⁻¹ ≠ s⁻¹) →
      ∀ J : Subgroup CFSG.Blueprint.NativeSporadic.B,
        GLAPComponent 3 (Subgroup.centralizer ({s} : Set CFSG.Blueprint.NativeSporadic.B)) J →
          ¬ IsGF4Type (PSimple 3 J)

end Framework

section Rows


theorem crow_three_of_ne (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) :
    ∀ s : TauCeti.SporadicName, s ≠ .B → s ≠ .M → s ≠ .J1 →
      CFSG.LocalAnalysis.GLTheoremA.Chev2Rows.CRow s 3 := by
  intro s hB hM hJ1
  cases s
  case B => exact absurd rfl hB
  case M => exact absurd rfl hM
  case J1 => exact absurd rfl hJ1
  case M11 => exact CFSG.LocalAnalysis.GLTheoremA.Chev2Rows.crow_M11_three hOut
  case M12 => exact CFSG.LocalAnalysis.GLTheoremA.Chev2Rows.crow_M12_three hOut
  case M22 => exact CFSG.LocalAnalysis.GLTheoremA.Chev2Rows.crow_M22_three hOut
  case M23 => exact CFSG.LocalAnalysis.GLTheoremA.Chev2Rows.crow_M23_three hOut hbr
  case M24 => exact CFSG.LocalAnalysis.GLTheoremA.Chev2Rows.crow_M24_three hOut hbr hb
  case J2 => exact CFSG.LocalAnalysis.GLTheoremA.Chev2Rows.crow_J2_three hOut hbr hb
  case J3 => exact CFSG.HardMathSupport.Dickson.I271.Chev2J3.crow_J3_three hOut hbr hb
  case J4 => exact CFSG.AGLEmbeddingD2.Wilson.NormalizerAction.crow_J4_three hOut hbr hb
  case HS => exact CFSG.LocalAnalysis.GLTheoremA.Chev2Rows.crow_HS_three hOut hbr
  case McL => exact CFSG.LocalAnalysis.GLTheoremA.Chev2Rows.crow_McL_three hOut hbr
  case He => exact CFSG.LocalAnalysis.GLTheoremA.Chev2Rows.crow_He_three hOut hbr hb
  case Ru => exact CFSG.LocalAnalysis.GLTheoremA.Chev2Rows.crow_Ru_three hOut hbr hb
  case Suz => exact CFSG.HardMathSupport.Dickson.I271.Chev2Suz.crow_Suz_three hOut hbr hb
  case ONan => exact CFSG.LocalAnalysis.GLTheoremA.Chev2Rows.crow_ON_three hOut hbr hb
  case Co1 => exact CFSG.HardMathSupport.Dickson.I271.TabCo1.crow_Co1_three hOut hbr hb
  case Co2 => exact CFSG.HardMathSupport.Dickson.I271.Chev2Co2.crow_Co2_three hOut hbr hb
  case Co3 => exact CFSG.HardMathSupport.Dickson.I271.Chev2Co3.crow_Co3_three hOut hbr hb
  case Fi22 => exact CFSG.HardMathSupport.Dickson.I271.Chev2Fi22.crow_Fi22_three hOut hbr hb
  case Fi23 => exact CFSG.HardMathSupport.Dickson.I271.Chev2Fi23.crow_Fi23_three hOut hbr hb
  case Fi24Prime => exact CFSG.HardMathSupport.Dickson.I271.TabFi24.crow_Fi24_three hOut hbr hb
  case HN => exact CFSG.HardMathSupport.Dickson.I271.Chev2HN3.crow_HN_three hOut hbr hb
  case Ly => exact CFSG.HardMathSupport.Dickson.I271.Chev2Ly.crow_Ly_three hOut hbr hb
  case Th => exact CFSG.HardMathSupport.Dickson.I271.Chev2Th.crow_Th_three hOut hbr hb

theorem typeRow_three_of_ne (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) :
    ∀ s : TauCeti.SporadicName, s ≠ .B → s ≠ .M → s ≠ .J1 →
      CFSG.LocalAnalysis.GLTheoremA.I1416Rows.I1416SporRow s 3 := by
  intro s hB hM hJ1
  cases s
  case B => exact absurd rfl hB
  case M => exact absurd rfl hM
  case J1 => exact absurd rfl hJ1
  case M11 => exact CFSG.LocalAnalysis.GLTheoremA.I1416Rows.row_M11_three hOut
  case M12 => exact CFSG.LocalAnalysis.GLTheoremA.I1416Rows.row_M12_three hOut
  case M22 => exact CFSG.LocalAnalysis.GLTheoremA.I1416Rows.row_M22_three hOut
  case M23 => exact CFSG.LocalAnalysis.GLTheoremA.I1416Rows.row_M23_three hOut hbr
  case M24 => exact CFSG.LocalAnalysis.GLTheoremA.I1416Rows.row_M24_three hOut hbr hb
  case J2 => exact CFSG.LocalAnalysis.GLTheoremA.I1416Rows.row_J2_three hOut hbr hb
  case J3 => exact CFSG.HardMathSupport.Dickson.I271.I1416J3.row_J3_three hOut hbr
  case J4 => exact CFSG.AGLEmbeddingD2.Wilson.NormalizerAction.row_J4_three hOut hbr hb
  case HS => exact CFSG.LocalAnalysis.GLTheoremA.I1416Rows.row_HS_three hOut hbr
  case McL => exact CFSG.LocalAnalysis.GLTheoremA.I1416Rows.row_McL_three hOut hbr
  case He => exact CFSG.LocalAnalysis.GLTheoremA.I1416Rows.row_He_three hOut hbr hb
  case Ru => exact CFSG.LocalAnalysis.GLTheoremA.I1416Rows.row_Ru_three hOut hbr hb
  case Suz => exact CFSG.HardMathSupport.Dickson.I271.I1416Suz.row_Suz_three hOut hbr hb
  case ONan => exact CFSG.LocalAnalysis.GLTheoremA.I1416Rows.row_ON_three hOut hbr
  case Co1 => exact CFSG.HardMathSupport.Dickson.I271.TabCo1.row_Co1_three hOut hbr hb
  case Co2 => exact CFSG.HardMathSupport.Dickson.I271.I1416Co2.row_Co2_three hOut hbr
  case Co3 => exact CFSG.HardMathSupport.Dickson.I271.I1416Co3.row_Co3_three hOut hbr
  case Fi22 => exact CFSG.HardMathSupport.Dickson.I271.I1416Fi22.row_Fi22_three hOut hbr hb
  case Fi23 => exact CFSG.HardMathSupport.Dickson.I271.I1416Fi23.row_Fi23_three hOut hbr hb
  case Fi24Prime => exact CFSG.HardMathSupport.Dickson.I271.TabFi24.row_Fi24_three hOut hbr hb
  case HN => exact CFSG.HardMathSupport.Dickson.I271.I1416HN3.row_HN_three hOut hbr hb
  case Ly => exact CFSG.HardMathSupport.Dickson.I271.I1416Ly.row_Ly_three hOut hbr hb
  case Th => exact CFSG.HardMathSupport.Dickson.I271.I1416Th.row_Th_three hOut hbr hb

end Rows

section Baby


theorem gf4FreeAtThree_B (h : B3BNoGF4) : GF4FreeAtThree (CFSG.Blueprint.NativeSporadic.Carrier .B) := by
  show GF4FreeAtThree CFSG.Blueprint.NativeSporadic.B
  intro x hx J hJ
  by_cases hinv : ∃ d : CFSG.Blueprint.NativeSporadic.B, CFSG.Monster.GMS.BabyInv 0 d ∧ d * x * d⁻¹ = x⁻¹
  · obtain ⟨d, hd, hdx⟩ := hinv
    rcases CFSG.HardMathSupport.Dickson.BMRows.CensusB3.shapeRkAt'_fi22_of_inverted
        CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv CFSG.HardMathSupport.Dickson.I271.tabBThreeACard_thm hx hd
        hdx with hno | ⟨J', -, hu, ⟨f⟩, -⟩
    · exact (hno J hJ).elim
    · rw [hu J hJ]
      exact not_isGF4Type_of_sporadic f
  · exact h x hx (fun d hd hdx => hinv ⟨d, hd, hdx⟩) J hJ

end Baby

section MonsterThreeB


theorem false_of_m3Beta1_of_lie {J : Subgroup CFSG.Monster.Generated.Gmat}
    (hJ : CFSG.HardMathSupport.Dickson.I271.M3Beta1 J) {d : TauCeti.ValidLieTypeIndex}
    (e : ↥J ⧸ Subgroup.center ↥J ≃* (TauCeti.CFSGIndex.lie d).Group) : False := by
  haveI : Finite CFSG.Monster.Generated.Gmat := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF.finite_Gmat
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have S := CFSG.HardMathSupport.Dickson.I271.m3Setup Certificates.certificate136201
    Certificates.certificate136207
  obtain ⟨hJc, -, hQN, hker, -⟩ := hJ
  have hQc : Nat.card CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF.QQ = 3 ^ (12 + 1) := by
    rw [CFSG.HardMathSupport.Dickson.I271.LargeExtraspecialAll.card_eq_pow_mul_of_relIndex S.order_w S.hwQ S.hrel]
    ring
  obtain ⟨D, hD, hDc, hDin⟩ := CFSG.HardMathSupport.Dickson.I271.ThreeOutRank.exists_elemAbelian_inner_trivial
    (p := 3) (k := 12) (m := 3) (by norm_num) S.order_w S.hQX hJc.1 S.hwX hJc.2.2.1 hQN hQc hker
    (fun a ha b hb => CFSG.HardMathSupport.Dickson.I271.MonsterThreeBRank.commutator_mem_zpowers ha hb)
    (fun a ha => CFSG.HardMathSupport.Dickson.I271.MonsterThreeBRank.pow_three_mem_zpowers ha)
  have hq := hJc.2.2
  have hnab := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian ↥J hq
  obtain ⟨x, hx, hx1⟩ := CFSG.HardMathSupport.Timmesfeld.DefChar.lieOuterRank_proved (↥J ⧸ Subgroup.center ↥J) hq.2
    hnab d ⟨e⟩ 3 Nat.prime_three (by norm_num) D hD hDc
  rw [hDin, Subgroup.mem_bot] at hx
  exact hx1 hx

theorem false_of_m3Beta2a_of_lie {J : Subgroup CFSG.Monster.Generated.Gmat}
    (hJ : CFSG.HardMathSupport.Dickson.I271.M3Beta2a J) {d : TauCeti.ValidLieTypeIndex}
    (e : ↥J ⧸ Subgroup.center ↥J ≃* (TauCeti.CFSGIndex.lie d).Group) : False := by
  haveI : Finite CFSG.Monster.Generated.Gmat := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF.finite_Gmat
  have S := CFSG.HardMathSupport.Dickson.I271.m3Setup Certificates.certificate136201
    Certificates.certificate136207
  obtain ⟨hJc, hQJ, -, -, -, hZ, -, -⟩ := hJ
  have hQc : Nat.card CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF.QQ = 3 ^ (12 + 1) := by
    rw [CFSG.HardMathSupport.Dickson.I271.LargeExtraspecialAll.card_eq_pow_mul_of_relIndex S.order_w S.hwQ S.hrel]
    ring
  have h13 : 3 ^ (12 + 1) ∣ Nat.card J := hQc ▸ Subgroup.card_dvd_of_le hQJ
  have h12 : 3 ^ 12 ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) :=
    CFSG.HardMathSupport.Dickson.I271.LargeExtraspecialOut.pow_dvd_card_quot (by norm_num) hZ h13
  have hq := hJc.2.2
  have hnab := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian ↥J hq
  have hq' : CFSG.IsQuasisimple ↥J := ⟨⟨hq.1⟩, hq.2, hnab⟩
  have hcardK : Nat.card ↥J = Nat.card (↥J ⧸ Subgroup.center ↥J) * Nat.card (Subgroup.center ↥J) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥J)
  have hdvd : Nat.card (↥J ⧸ Subgroup.center ↥J) ∣ CFSG.Open.monsterOrder :=
    (Dvd.intro _ hcardK.symm).trans (CFSG.HardMathSupport.Dickson.I271.MonsterThreeBRank.card_dvd_monsterOrder_gmat J)
  exact CFSG.HardMathSupport.Dickson.I271.ThreeCentralLeaf.lie_three_false
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
    CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds hq' d e (by rw [hZ]) h12 hdvd

theorem not_isGF4Type_of_comp_tbw
    (hM3 : CFSG.HardMathSupport.Timmesfeld.SporadicBalance.OPrimeCoreTrivialAt 3 CFSG.Monster.Generated.Gmat)
    {J : Subgroup CFSG.Monster.Generated.Gmat} (hJ : GLAPComponent 3 CFSG.HardMathSupport.Dickson.I271.M3X J) :
    ¬ IsGF4Type (PSimple 3 J) := by
  haveI : Finite CFSG.Monster.Generated.Gmat := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF.finite_Gmat
  rintro ⟨d, -, -, ⟨e⟩⟩
  have hX : GLAPPrimeCoreOf 3 CFSG.HardMathSupport.Dickson.I271.M3X = ⊥ :=
    hM3 _ CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF.orderOf_tbw
  have hJc := CFSG.HardMathSupport.Dickson.I271.isComponentOf_of_glaPComponent_of_core hX hJ
  have hcoreJ : GLAPPrimeCore 3 ↥J = ⊥ := by
    have h1 : GLAPPrimeCoreOf 3 J = ⊥ := le_bot_iff.1
      ((CFSG.HardMathSupport.Solomon.LocalBalance.glaPPrimeCoreOf_le_of_isSubnormal 3 hJc.2.1).trans hX.le)
    exact (Subgroup.map_eq_bot_iff_of_injective _ J.subtype_injective).1 h1
  have e' := (CFSG.HardMathSupport.Dickson.I271.pSimpleEquivCenterQuot J hcoreJ).symm.trans e
  rcases CFSG.HardMathSupport.Dickson.I271.m3_component_cases Certificates.certificate136201
      Certificates.certificate136207 hM3 hJc with h1 | h2
  · exact false_of_m3Beta1_of_lie h1 e'
  · exact false_of_m3Beta2a_of_lie h2 e'

theorem centThreeBNoGF4_gmat : CentThreeBNoGF4 CFSG.Monster.Generated.Gmat := by
  haveI : Finite CFSG.Monster.Generated.Gmat := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF.finite_Gmat
  have hB3 : CFSG.HardMathSupport.Timmesfeld.SporadicBalance.OPrimeCoreTrivialAt 3 CFSG.Blueprint.NativeSporadic.B :=
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23.oPrimeCoreTrivialAt_B_three
  have hM3 : CFSG.HardMathSupport.Timmesfeld.SporadicBalance.OPrimeCoreTrivialAt 3 CFSG.Monster.Generated.Gmat :=
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.oPrimeCoreTrivialAt_gmat_of_uninverted Nat.prime_three
      (by norm_num) (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.uninvertedOPrimeTrivial_gmat_of_twoAPureKlein
        Nat.prime_three (by norm_num) hB3
        CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF.twoAPureKlein_three_Gmat)
  intro x hx hinv J hJ hG
  obtain ⟨c, hc⟩ := isConj_iff.1 (CFSG.HardMathSupport.Dickson.Sec6.BM2.m3bClass_holds x hx hinv)
  have h1 := CFSG.HardMathSupport.Dickson.I271.glaPComponent_map_equiv Nat.prime_three (MulAut.conj c) hJ
  rw [CFSG.HardMathSupport.Dickson.I271.map_centralizer_singleton (MulAut.conj c) x] at h1
  have h4 : (MulAut.conj c) x = CFSG.AGLEmbedding.Norton.MON5_7.tbw := by
    simpa [MulAut.conj_apply] using hc
  rw [h4] at h1
  exact not_isGF4Type_of_comp_tbw hM3 h1
    (hG.of_mulEquiv (CFSG.HardMathSupport.Dickson.I271.pSimpleEquiv 3 ((MulAut.conj c).subgroupMap J)).symm)

end MonsterThreeB

section MonsterAll


theorem gf4FreeAtThree_M : GF4FreeAtThree (CFSG.Blueprint.NativeSporadic.Carrier .M) := by
  obtain ⟨e₀⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_griess_y443Derived
  let e : CFSG.Monster.Existence.MGriess ≃* CFSG.Blueprint.NativeSporadic.Carrier .M := e₀
  have hE : CFSG.Monster.Existence.MonsterExistenceStatement CFSG.Monster.Existence.MGriess :=
    CFSG.Milestones.cl_lit_monster_existence_griess_conway
  haveI : Finite CFSG.Monster.Existence.MGriess :=
    (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.twoA_data_of_existence hE).1
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .M) :=
    Finite.of_equiv CFSG.Monster.Existence.MGriess e.toEquiv
  have φ := CFSG.YGroups.Y443.griessEquivGmat CFSG.YGroups.Y443.Gmat_eq_AutO_of_stroth
  have hSpM := CFSG.HardMathSupport.Timmesfeld.Coordinator.sporadicMultipliers_of_census
    CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds
  have hBr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges :=
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
  have hA : CFSG.HardMathSupport.Dickson.I271.CentThreeA CFSG.Monster.Existence.MGriess :=
    CFSG.HardMathSupport.Dickson.I271.CentThreeA.of_equiv e
      (CFSG.HardMathSupport.Dickson.I271.centThreeA_M CFSG.HardMathSupport.Dickson.I271.tabBThreeACard_thm)
  have hC : CFSG.HardMathSupport.Dickson.I271.CentThreeC CFSG.Monster.Existence.MGriess :=
    CFSG.HardMathSupport.Dickson.I271.CentThreeC.of_equiv e CFSG.HardMathSupport.Dickson.I271.centThreeC_M
  have hB : CentThreeBNoGF4 CFSG.Monster.Existence.MGriess := CentThreeBNoGF4.of_equiv φ centThreeBNoGF4_gmat
  refine GF4FreeAtThree.of_equiv e.symm ?_
  intro k hk J hJ
  by_cases hinv : CFSG.HardMathSupport.Timmesfeld.SporadicBalance.InvertedByTwoA k
  · obtain ⟨α, hα2, hαc, hαk, i, hi, hsh⟩ :=
      CFSG.HardMathSupport.Dickson.I271.invertedByTwoA_data_twoA hE Nat.prime_three (by norm_num) hk hinv
    have hi34 : i = 3 ∨ i = 4 := by
      clear hsh
      revert i
      decide
    rcases hi34 with rfl | rfl
    · obtain ⟨hq, ⟨e'⟩⟩ := hA k α hk hα2 hαc hαk hsh
      exact not_isGF4Type_of_shapeM (CFSG.HardMathSupport.Dickson.BMRows.census_M_three_shape_of_cover hSpM hBr hk
        hq e') hJ
    · obtain ⟨e'⟩ := hsh
      exact not_isGF4Type_of_shapeM (CFSG.HardMathSupport.Dickson.BMRows.census_M_three_shape_of_th hBr hk hαk
        inf_le_left inf_le_right e' (hC k α hk hα2 hαc hαk ⟨e'⟩)) hJ
  · exact hB k hk hinv J hJ

end MonsterAll

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256o

end
