module

public import CFSG.LocalAnalysis.OddStandard.ONanDefs
public import CFSG.LocalAnalysis.OddStandard.ONanEndGpl
public import CFSG.LocalAnalysis.OddStandard.ONanEndLocal

public section

namespace CFSG.OddStandard.ONanRec

open Subgroup CFSG.Sporadic.Bridge

def centralizerConjEquiv {G : Type*} [Group G] (k x : G) :
    centralizer ({x} : Set G) ≃* centralizer ({k * x * k⁻¹} : Set G) where
  toFun g := ⟨k * g * k⁻¹, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.1 g.2
    calc k * (g : G) * k⁻¹ * (k * x * k⁻¹) = k * ((g : G) * x) * k⁻¹ := by group
      _ = k * (x * (g : G)) * k⁻¹ := by rw [this]
      _ = k * x * k⁻¹ * (k * (g : G) * k⁻¹) := by group⟩
  invFun g := ⟨k⁻¹ * g * k, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.1 g.2
    calc k⁻¹ * (g : G) * k * x = k⁻¹ * ((g : G) * (k * x * k⁻¹)) * k := by group
      _ = k⁻¹ * ((k * x * k⁻¹) * (g : G)) * k := by rw [this]
      _ = x * (k⁻¹ * (g : G) * k) := by group⟩
  left_inv g := by
    apply Subtype.ext
    show k⁻¹ * (k * (g : G) * k⁻¹) * k = g
    group
  right_inv g := by
    apply Subtype.ext
    show k * (k⁻¹ * (g : G) * k) * k⁻¹ = g
    group
  map_mul' g h := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    group

theorem card_centralizer_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) (u : A) :
    Nat.card (centralizer ({u} : Set A)) = Nat.card (centralizer ({e u} : Set B)) := by
  apply Nat.card_congr
  refine e.toEquiv.subtypeEquiv fun k => ?_
  simp only [Subgroup.mem_centralizer_singleton_iff, MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
  rw [← map_mul, ← map_mul]
  exact e.injective.eq_iff.symm


theorem stageB2_of_loc {N Cm : Type} [Group N] [Group Cm]
    (hN : OnNativeFacts N) (hC : CentFacts Cm) (hL : StageB2Loc Cm) : StageB2 N Cm := by
  intro G _ _ _ hna hone f hf he
  obtain ⟨x, hx, hx5⟩ := hL G hna hone f hf he
  obtain ⟨e⟩ := he
  have hcount : TauCeti.Sporadic.onanPresentation.generatorCount = 7 := by
    simp [TauCeti.GroupPresentation.generatorCount]
  set s : Set G := Set.range fun i : Fin 7 => x i with hs_def
  set H : Subgroup G := Subgroup.closure s with hH
  have hfH : f ∈ H := by
    rw [← hx5]
    exact Subgroup.subset_closure ⟨⟨5, by norm_num⟩, rfl⟩
  have hf1 : f ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hf
    exact absurd hf (by norm_num)
  have : Nontrivial H := ⟨⟨⟨f, hfH⟩, 1, fun h => hf1 (congrArg Subtype.val h)⟩⟩
  let y : ℕ → H := fun i =>
    if h : i < 7 then ⟨x i, Subgroup.subset_closure ⟨⟨i, h⟩, rfl⟩⟩ else 1
  have hyx : ∀ i, i < 7 → ((y i : H) : G) = x i := by
    intro i hi
    simp [y, hi]
  have hlet : ∀ v ∈ TauCeti.Sporadic.onanPresentation.relatorLetters, ∀ l ∈ v, l.1 < 7 := by
    intro v hv l hl
    rw [TauCeti.GroupPresentation.relatorLetters_def] at hv
    obtain ⟨r, -, rfl⟩ := List.mem_map.1 hv
    obtain ⟨letter, -, rfl⟩ := List.mem_map.1 hl
    have := letter.1.isLt
    simpa [hcount] using this
  have hy : ∀ v ∈ TauCeti.Sporadic.onanPresentation.relatorLetters, wordProd y v = 1 := by
    intro v hv
    apply Subtype.ext
    rw [coe_wordProd]
    have : wordProd (fun i => ((y i : H) : G)) v = wordProd x v := by
      unfold wordProd
      congr 1
      apply List.map_congr_left
      intro l hl
      show (if l.2 = true then ((y l.1 : H) : G) else ((y l.1 : H) : G)⁻¹) =
        (if l.2 = true then x l.1 else (x l.1)⁻¹)
      rw [hyx l.1 (hlet v hv l hl)]
    rw [this, hx v hv]
    rfl
  have hgen : Subgroup.closure (Set.range fun i : Fin 7 => y i) = ⊤ := by
    have h1 := Subgroup.closure_closure_coe_preimage (k := s)
    have h2 : (((↑) : Subgroup.closure s → G) ⁻¹' s) = Set.range fun i : Fin 7 => y i := by
      ext h
      constructor
      · rintro ⟨i, hi⟩
        refine ⟨i, Subtype.ext ?_⟩
        rw [hyx i i.2]
        exact hi
      · rintro ⟨i, rfl⟩
        exact ⟨i, (hyx i i.2).symm⟩
    rw [h2] at h1
    exact h1
  obtain ⟨φ⟩ := identify_of_gpl hN.simple hN.bridge y hy hgen
  have hone_H : ∀ u v : H, orderOf u = 2 → orderOf v = 2 → IsConj u v := by
    intro u v hu hv
    have hu' : orderOf (φ u) = 2 := by rw [MulEquiv.orderOf_eq]; exact hu
    have hv' : orderOf (φ v) = 2 := by rw [MulEquiv.orderOf_eq]; exact hv
    have := φ.symm.toMonoidHom.map_isConj (hN.oneClass _ _ hu' hv')
    simpa using this
  have hfo : orderOf (⟨f, hfH⟩ : H) = 2 := by rw [Subgroup.orderOf_mk]; exact hf
  have hev : Even (Nat.card H) := by
    have := orderOf_dvd_natCard (⟨f, hfH⟩ : H)
    rw [hfo] at this
    exact even_iff_two_dvd.mpr this
  have hcardG : Nat.card (centralizer ({f} : Set G)) = 161280 := by
    rw [Nat.card_congr e.toEquiv]
    exact hC.card
  have hcardH : Nat.card (centralizer ({(⟨f, hfH⟩ : H)} : Set H)) = 161280 := by
    rw [card_centralizer_equiv φ]
    exact hN.card_cent _ (by rw [MulEquiv.orderOf_eq]; exact hfo)
  have hNG : ∀ u : G, orderOf u = 2 → ∀ S : Subgroup G, IsPGroup 2 S →
      S ≤ centralizer ({u} : Set G) →
      (∀ k ∈ centralizer ({u} : Set G), k ∈ normalizer (S : Set G)) →
      Nat.card S ≤ 4 := by
    intro u hu S hS hSC hSn
    obtain ⟨c, rfl⟩ := isConj_iff.mp (hone f u hf hu)
    let ψ : centralizer ({c * f * c⁻¹} : Set G) ≃* Cm := (centralizerConjEquiv c f).symm.trans e
    set S' : Subgroup (centralizer ({c * f * c⁻¹} : Set G)) :=
      S.subgroupOf (centralizer ({c * f * c⁻¹} : Set G)) with hS'
    have hS'n : S'.Normal := by
      refine ⟨fun t ht k => ?_⟩
      rw [hS', Subgroup.mem_subgroupOf] at ht ⊢
      have := (Subgroup.mem_normalizer_iff.mp (hSn (k : G) k.2) (t : G)).mp ht
      simpa using this
    have hS'p : IsPGroup 2 S' := hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSC).symm
    have hS'c : Nat.card S' = Nat.card S :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSC).toEquiv
    have hT := hC.normal2 (S'.map ψ.toMonoidHom) (hS'p.map ψ.toMonoidHom)
      (hS'n.map ψ.toMonoidHom ψ.surjective)
    rwa [Subgroup.card_map_of_injective ψ.injective, hS'c] at hT
  have hfour : ∃ a b : G, orderOf a = 2 ∧ orderOf b = 2 ∧ a * b = b * a ∧ a ≠ b := by
    obtain ⟨w, hw2, hwc⟩ := hC.noncentral
    set w' : centralizer ({f} : Set G) := e.symm w with hw'
    have hw'o : orderOf (w' : G) = 2 := by
      rw [Subgroup.orderOf_coe, hw', MulEquiv.orderOf_eq]
      exact hw2
    have hcomm : (w' : G) * f = f * (w' : G) := Subgroup.mem_centralizer_singleton_iff.1 w'.2
    refine ⟨f, (w' : G), hf, hw'o, hcomm.symm, fun hfw => hwc ?_⟩
    rw [Subgroup.mem_center_iff]
    intro g
    have hw'c : w' = ⟨f, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ := Subtype.ext hfw.symm
    have hcen : ∀ k : centralizer ({f} : Set G), k * w' = w' * k := by
      intro k
      rw [hw'c]
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 k.2)
    have := hcen (e.symm g)
    have h2 := congrArg e this
    simpa [map_mul, hw'] using h2
  have h8 : 8 ≤ 2 ^ (Nat.card G).factorization 2 := by
    have h1 : Nat.card (centralizer ({f} : Set G)) ∣ Nat.card G := Subgroup.card_subgroup_dvd_card _
    rw [hcardG] at h1
    have h2 : 2 ^ 9 ∣ Nat.card G := (by norm_num : 2 ^ 9 ∣ 161280).trans h1
    have h3 : 9 ≤ (Nat.card G).factorization 2 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (Nat.card_pos (α := G)).ne').mp h2
    calc 8 ≤ 2 ^ 9 := by norm_num
      _ ≤ 2 ^ (Nat.card G).factorization 2 := Nat.pow_le_pow_right (by norm_num) h3
  have hcard : Nat.card (centralizer ({f} : Set G)) ≤
      Nat.card (centralizer ({(⟨f, hfH⟩ : H)} : Set H)) := by
    rw [hcardG, hcardH]
  have htop : H = ⊤ := eq_top_of_local inferInstance hNG hfour h8 H hev hone_H f hfH hf hcard
  exact ⟨((Subgroup.topEquiv (G := G)).symm.trans (MulEquiv.subgroupCongr htop.symm)).trans φ⟩

theorem onanSylowInputBal_of_everything {N Cm : Type} [Group N] [Group Cm]
    (h1 : StageB1 N Cm) (hLoc : StageB2Loc Cm)
    (hNat : OnNativeFacts N) (hC : CentFacts Cm) : SylowBal N :=
  onanSylowInputBal_of_stages h1 (stageB2_of_loc hNat hC hLoc)

theorem onanSylowInputBal_of_route {N : Type} [Group N]
    (hA : StageA5 N) (hL : StageB1Local) (hI : StageB1Ident)
    (hLoc : StageB2Loc CModel) (hNat : OnNativeFacts N) (hC : CentFacts CModel) : SylowBal N :=
  onanSylowInputBal_of_everything (stageB1_of_parts hA hL hI) hLoc hNat hC

end CFSG.OddStandard.ONanRec
