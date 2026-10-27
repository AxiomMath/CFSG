module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3M1Six
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3M1Eight
import CFSG.LocalAnalysis.EvenBN.Common.SL2Center

public section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.U5K.Hyp CFSG.LocalAnalysis.EvenBN.GMS
open scoped MatrixGroups

section NormalClosure

variable {H : Type} [Group H] [Finite H] {A : Subgroup H} {t : H} {U V D : Subgroup H}

theorem gms_linear_local_normal_closure_four
    (hL : GMSK.GMSLinearStandardLayerListKRankOneStatement) (hK : CFSG.SectionRank.IsKGroupCat H)
    (h : GMSLinearLocalApplication A t U V D 4) (hVA : V ≤ normalClosure (A : Set H)) :
    let R := CFSG.Open.standardComponentOddCore H
    let π : H →* H ⧸ R := QuotientGroup.mk' R
    let X := normalClosure (A : Set H)
    Set.InjOn π (A : Set H) ∧ Set.InjOn π (V : Set H) ∧ Set.InjOn π (zpowers t : Set H) ∧
      CFSG.Open.standardComponentIsStandard (A.map π) ∧ ¬ (A.map π).Normal ∧
      centralizer (X : Set H) = R ∧ Group.IsPerfect X ∧
      (center X).map X.subtype = X ⊓ R ∧
      (CFSG.Open.standardComponentOddCore X).map X.subtype = X ⊓ R ∧
      Xor
        (∃ (k : Type) (_ : Field k) (_ : Fintype k), Fintype.card k = 2 ^ 4 ∧
          ∃ (ψ : X ⧸ center X ≃* SL(2, k) × SL(2, k)) (α : A ≃* SL(2, k)),
            (∀ (a : A) (x : X), (x : H) = a → ψ (x : X ⧸ center X) = (α a, α a)) ∧
            ∀ (x y : X) (y₁ y₂ : SL(2, k)), (y : H) = t⁻¹ * x * t →
              ψ (x : X ⧸ center X) = (y₁, y₂) → ψ (y : X ⧸ center X) = (y₂, y₁))
        (∃ (k₂ : Type) (_ : Field k₂) (_ : Fintype k₂), Fintype.card k₂ = (2 ^ 4) ^ 2 ∧
          ∃ ψ : X ⧸ center X ≃* SL(2, k₂),
            (∀ x y : X, (y : H) = t⁻¹ * x * t →
              ((ψ (y : X ⧸ center X) : SL(2, k₂)) : Matrix (Fin 2) (Fin 2) k₂) =
                (ψ (x : X ⧸ center X) : Matrix (Fin 2) (Fin 2) k₂).map (fun c => c ^ 2 ^ 4)) ∧
            ∀ g : SL(2, k₂),
              g ∈ ((A.subgroupOf X).map (QuotientGroup.mk' (center X))).map ψ.toMonoidHom ↔
                ∀ i j, (g : Matrix (Fin 2) (Fin 2) k₂) i j ^ 2 ^ 4 =
                  (g : Matrix (Fin 2) (Fin 2) k₂) i j) ∧
      ∃ e : X ⧸ center X ≃* X.map π, ∀ x : X, (e (x : X ⧸ center X) : H ⧸ R) = π x := by
  intro R π X
  have hR : Odd (Nat.card R) := GMSK.odd_card_standardComponentOddCore H
  obtain ⟨hinjA, hinj2, -, -, -, -, hstdb, -⟩ := LinearApp.odd_quotient h R hR
  obtain ⟨hperf, -, hfin⟩ := LinearApp.elementary h
  have happ := LinearApp.map_quotient h R hR
  have hS : LocalSetting (A.map π) (π t) (U.map π) (V.map π) (D.map π) 4 :=
    ⟨GMSK.standardComponentOddCore_quotient_eq_bot H, happ⟩
  have hVA' : V.map π ≤ normalClosure ((A.map π : Subgroup (H ⧸ R)) : Set (H ⧸ R)) := by
    have h1 := map_mono (f := π) hVA
    rwa [map_normalClosure _ _ (QuotientGroup.mk'_surjective R), ← coe_map] at h1
  obtain ⟨hCE, -, hEA, -, hXor⟩ :=
    CFSG.LocalAnalysis.EvenBN.U5.LocalSetting.layer_selection_four hL (hK.quotient R) hS hVA'
  have hXE : X.map π = CFSG.layer (H ⧸ R) := by
    rw [hEA, map_normalClosure _ _ (QuotientGroup.mk'_surjective R), ← coe_map]
  obtain ⟨hCX, hZ, hO, e, he⟩ := hfin (by rw [hXE]; exact hCE)
  have hAX : A ≤ X := le_normalClosure
  have hV2 : IsPGroup 2 V := @IsElementaryAbelian.isPGroup 2 V _ h.2.2.2.2.1.2.2.1
  have hz : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.2.1, pow_one])
  refine ⟨hinjA, hinj2 V hV2, hinj2 _ hz, hstdb, happ.2.2.1.2.1, hCX, hperf, hZ.trans hO, hO, ?_,
    e, he⟩
  let e' : X ⧸ center X ≃* CFSG.layer (H ⧸ R) := e.trans (MulEquiv.subgroupCongr hXE)
  have he' : ∀ x : X, (e' (x : X ⧸ center X) : H ⧸ R) = π x := he
  have hconj : ∀ x y : X, (y : H) = t⁻¹ * x * t →
      ((e' (y : X ⧸ center X)) : H ⧸ R) = (π t)⁻¹ * (e' (x : X ⧸ center X)) * π t := by
    intro x y hyx
    rw [he', he', hyx, map_mul, map_mul, map_inv]
  let ιA : A ≃* A.map π := MulEquiv.ofBijective (π.subgroupMap A)
    ⟨fun x y hxy => Subtype.ext (hinjA x.2 y.2 (congrArg Subtype.val hxy)),
      π.subgroupMap_surjective A⟩
  have hexcl : ∀ (k : Type) (_ : Field k) (_ : Fintype k) (k₂ : Type) (_ : Field k₂)
      (_ : Fintype k₂), Fintype.card k₂ = (2 ^ 4) ^ 2 →
      (X ⧸ center X ≃* SL(2, k) × SL(2, k)) → (X ⧸ center X ≃* SL(2, k₂)) → False := by
    intro k _ _ k₂ _ _ hk₂ ψ₁ ψ₂
    have hk₂' : Nat.card k₂ = 2 ^ (2 * 4) := by
      rw [Nat.card_eq_fintype_card, hk₂]
      norm_num
    exact (isEmpty_mulEquiv_sl2_prod (k := k) (by norm_num) hk₂').false (ψ₂.symm.trans ψ₁)
  rcases hXor with ⟨⟨k, _, _, hk, ψ, α, hψA, hψt⟩, -⟩ | ⟨⟨k₂, _, _, hk₂, ψ, hψt, hψA⟩, -⟩
  · refine Or.inl ⟨⟨k, inferInstance, inferInstance, hk, e'.trans ψ, ιA.trans α,
      fun a x hxa => ?_, fun x y y₁ y₂ hyx hx => ?_⟩, ?_⟩
    · exact hψA (ιA a) (e' x) (by rw [he', hxa]; rfl)
    · exact hψt (e' x) (e' y) y₁ y₂ (hconj x y hyx) hx
    · rintro ⟨k₂, _, _, hk₂, ψ₂, -⟩
      exact hexcl k inferInstance inferInstance k₂ inferInstance inferInstance hk₂
        (e'.trans ψ) ψ₂
  · refine Or.inr ⟨⟨k₂, inferInstance, inferInstance, hk₂, e'.trans ψ,
      fun x y hyx => hψt (e' x) (e' y) (hconj x y hyx), fun g => ?_⟩, ?_⟩
    · rw [← hψA g, mem_map_equiv, mem_map_equiv, MulEquiv.symm_trans_apply]
      generalize ψ.symm g = z
      constructor
      · rintro ⟨x, hx, hxz⟩
        have hz' : z = e' (QuotientGroup.mk' (center X) x) := by
          rw [hxz, MulEquiv.apply_symm_apply]
        rw [mem_subgroupOf, hz', QuotientGroup.mk'_apply, he']
        exact mem_map_of_mem π (mem_subgroupOf.mp hx)
      · intro hzA
        obtain ⟨a, ha, haz⟩ := mem_subgroupOf.mp hzA
        refine ⟨⟨a, hAX ha⟩, mem_subgroupOf.mpr ha, ?_⟩
        rw [MulEquiv.eq_symm_apply, QuotientGroup.mk'_apply]
        exact Subtype.ext ((he' ⟨a, hAX ha⟩).trans haz)
    · rintro ⟨k, _, _, -, ψ₁, -⟩
      exact hexcl k inferInstance inferInstance k₂ inferInstance inferInstance hk₂ ψ₁
        (e'.trans ψ)

end NormalClosure

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem Hyp.centralizer_I₁_ne_top (hd : d.Hyp) : centralizer (d.I₁ : Set G) ≠ ⊤ := by
  intro htop
  have := finite_fixedField h
  have := charP_fixedField h
  have hK2 : 2 < Nat.card h.fixedField := by
    rw [h.card_fixedField]
    have := hd.four_le
    omega
  obtain ⟨b, hb0, hb1⟩ := Common.exists_ne_zero_ne_one hK2
  have hb0' : (b : K) ≠ 0 := fun e0 => hb0 (Subtype.ext e0)
  obtain ⟨j, hj, e1, -, -, e4, -⟩ := exists_I₁_block h hb0' (h.mem_fixedField.1 b.2)
  have hjI : d.η j ∈ d.I₁ := ⟨j, hj, rfl⟩
  have hz : (d.ιZp (Multiplicative.ofAdd 1) : G) ∈ centralizer (d.I₁ : Set G) :=
    htop ▸ mem_top _
  have hc := mem_centralizer_iff.1 hz _ hjI
  have e := d.conj_ιZp_torus (torusEq_le _ hj) e1 e4 1
  rw [hc, mul_inv_cancel_right] at e
  have e' := d.ιZp.injective (Subtype.ext e)
  have hbb : b * b * 1 = 1 := by simpa using (congrArg Multiplicative.toAdd e').symm
  have : (b - 1) * (b - 1) = 0 := by
    linear_combination hbb + (1 - b) * (CharTwo.two_eq_zero : (2 : h.fixedField) = 0)
  exact hb1 (sub_eq_zero.1 (mul_self_eq_zero.1 this))

theorem Hyp.V₁_le_normalClosure (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.V₁.subgroupOf (centralizer (d.I₁ : Set G)) ≤
      normalClosure ((d.N₁.subgroupOf (centralizer (d.I₁ : Set G)) :
        Subgroup (centralizer (d.I₁ : Set G))) : Set (centralizer (d.I₁ : Set G))) := by
  intro v hv
  obtain ⟨y, hy, hyv⟩ := hd.V₁_le_M₁ hGMS (mem_subgroupOf.1 hv)
  have hyv' : y = v := Subtype.ext hyv
  subst hyv'
  exact hy

theorem Hyp.sec3_5_three_four
    (hGMS : GMSK.GMSUnitarySharpKRankOneStatement)
    (hL : GMSK.GMSLinearStandardLayerListKRankOneStatement) (hd : d.Hyp) (hf : f = 2) :
    d.M₁ ≤ centralizer (d.I₁ : Set G) ∧
      centralizer (d.I₁ : Set G) ≤ normalizer (d.M₁ : Set G) ∧
      d.N₁ ≤ d.M₁ ∧ ⁅d.M₁, d.M₁⁆ = d.M₁ ∧
      Odd (Nat.card (center d.M₁)) ∧ center d.M₁ = ⊥ ∧
      Xor
        (∃ (k : Type) (_ : Field k) (_ : Fintype k), Fintype.card k = (2 ^ f) ^ 2 ∧
          ∃ (ψ : d.M₁ ⧸ center d.M₁ ≃* SL(2, k) × SL(2, k)) (α : d.N₁ ≃* SL(2, k)),
            (∀ (a : d.N₁) (x : d.M₁), (x : G) = a →
              ψ (x : d.M₁ ⧸ center d.M₁) = (α a, α a)) ∧
            ∀ (x y : d.M₁) (y₁ y₂ : SL(2, k)), (y : G) = d.t⁻¹ * x * d.t →
              ψ (x : d.M₁ ⧸ center d.M₁) = (y₁, y₂) → ψ (y : d.M₁ ⧸ center d.M₁) = (y₂, y₁))
        (∃ (k₂ : Type) (_ : Field k₂) (_ : Fintype k₂), Fintype.card k₂ = ((2 ^ f) ^ 2) ^ 2 ∧
          ∃ ψ : d.M₁ ⧸ center d.M₁ ≃* SL(2, k₂),
            (∀ x y : d.M₁, (y : G) = d.t⁻¹ * x * d.t →
              ((ψ (y : d.M₁ ⧸ center d.M₁) : SL(2, k₂)) : Matrix (Fin 2) (Fin 2) k₂) =
                (ψ (x : d.M₁ ⧸ center d.M₁) : Matrix (Fin 2) (Fin 2) k₂).map
                  (fun c => c ^ (2 ^ f) ^ 2)) ∧
            ∀ g : SL(2, k₂),
              g ∈ ((d.N₁.subgroupOf d.M₁).map (QuotientGroup.mk' (center d.M₁))).map
                  ψ.toMonoidHom ↔
                ∀ i j, (g : Matrix (Fin 2) (Fin 2) k₂) i j ^ (2 ^ f) ^ 2 =
                  (g : Matrix (Fin 2) (Fin 2) k₂) i j) ∧
      Odd (Nat.card (centralizer (d.I₁ : Set G) ⊓ centralizer (d.M₁ : Set G) : Subgroup G)) := by
  subst hf
  have : CharP K 2 := h.charP
  set Hs := centralizer (d.I₁ : Set G) with hHs
  have hNH : d.N₁ ≤ Hs := d.N₁_le_centralizer_I₁
  have hKH : CFSG.SectionRank.IsKGroupCat Hs :=
    CFSG.QuasithinUnique.isKGroupCat_of_kProper hd.setting.std.kProper hd.centralizer_I₁_ne_top
  have happ := hd.gmsLinearLocalApplication_one hGMS
  have key := gms_linear_local_normal_closure_four hL hKH happ (hd.V₁_le_normalClosure hGMS)
  obtain ⟨-, -, -, -, -, hCX, hperf, hZ, -, hXor, -⟩ := key
  set A : Subgroup Hs := d.N₁.subgroupOf Hs with hA
  set X : Subgroup Hs := normalClosure (A : Set Hs) with hX
  set R := CFSG.Open.standardComponentOddCore Hs with hR
  have hM : d.M₁ = X.map Hs.subtype := rfl
  have hRodd : Odd (Nat.card R) := GMSK.odd_card_standardComponentOddCore Hs
  have hMH : d.M₁ ≤ Hs := by
    rw [hM]
    exact map_subtype_le X
  have hHN : Hs ≤ normalizer (d.M₁ : Set G) := by
    intro g hg
    refine mem_normalizer_fintype fun m hm => ?_
    rw [SetLike.mem_coe, hM] at hm ⊢
    obtain ⟨x, hx, rfl⟩ := hm
    refine ⟨⟨g, hg⟩ * x * ⟨g, hg⟩⁻¹,
      (normalClosure_normal (s := (A : Set Hs))).conj_mem x hx ⟨g, hg⟩, ?_⟩
    simp
  have hNM : d.N₁ ≤ d.M₁ := by
    intro n hn
    rw [hM]
    exact ⟨⟨n, hNH hn⟩, subset_normalClosure (mem_subgroupOf.2 hn), rfl⟩
  have hXX : ⁅X, X⁆ = X := by
    have h1 : commutator X = ⊤ := hperf.commutator_eq_top
    have h2 := congrArg (Subgroup.map X.subtype) h1
    rwa [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype] at h2
  have hMM : ⁅d.M₁, d.M₁⁆ = d.M₁ := by
    rw [hM, ← map_commutator, hXX]
  let e₀ : X ≃* d.M₁ := Subgroup.equivMapOfInjective X Hs.subtype Hs.subtype_injective
  have : Group.IsPerfect d.M₁ :=
    Group.IsPerfect.ofSurjective (f := e₀.toMonoidHom) e₀.surjective
  have hZodd : Odd (Nat.card (center d.M₁)) := by
    rw [← Nat.card_congr (Subgroup.centerCongr e₀).toEquiv,
      ← card_map_of_injective X.subtype_injective, hZ]
    exact Odd.of_dvd_nat hRodd (card_dvd_of_le inf_le_right)
  have hXor' := U4.xor_map_subtype (X := X) hNH hd.t_mem_centralizer_I₁ (n := 4)
    (by norm_num) hXor.or
  rw [show (2 : ℕ) ^ 4 = (2 ^ 2) ^ 2 by norm_num] at hXor'
  have hcard : ∀ (k : Type) (_ : Field k) (_ : Fintype k), Fintype.card k = (2 ^ 2) ^ 2 ∨
      Fintype.card k = ((2 ^ 2) ^ 2) ^ 2 → 5 ≤ Nat.card k ∧ Nat.card k ≠ 9 := by
    intro k _ _ hk
    rw [Nat.card_eq_fintype_card]
    rcases hk with hk | hk <;> rw [hk] <;> norm_num
  have hZbot : center d.M₁ = ⊥ := by
    rcases hXor'.or with ⟨k, _, _, hk, ψ, -⟩ | ⟨k₂, _, _, hk₂, ψ, -⟩
    · obtain ⟨h5, h9⟩ := hcard k inferInstance inferInstance (Or.inl hk)
      exact Common.center_eq_bot_of_sl2_prod h5 h9 ψ
    · obtain ⟨h5, h9⟩ := hcard k₂ inferInstance inferInstance (Or.inr hk₂)
      exact Common.center_eq_bot_of_sl2 h5 h9 ψ
  have hCodd : Odd (Nat.card (Hs ⊓ centralizer (d.M₁ : Set G) : Subgroup G)) := by
    have hsub : d.M₁.subgroupOf Hs = X := by
      rw [hM]
      exact comap_map_eq_self_of_injective Hs.subtype_injective X
    rw [← U4.card_subgroupOf_of_le (inf_le_left : Hs ⊓ centralizer
      (d.M₁ : Set G) ≤ Hs), inf_subgroupOf_left, ← U4.centralizer_subgroupOf hMH, hsub, hCX]
    exact hRodd
  exact ⟨hMH, hHN, hNM, hMM, hZodd, hZbot, hXor', hCodd⟩

section Certified

theorem Hyp.sec3_5_three_all (hGMS : GMSK.GMSUnitarySharpKRankOneStatement)
    (hL : GMSK.GMSLinearStandardLayerListKRankOneStatement) (hd : d.Hyp) :
    d.M₁ ≤ centralizer (d.I₁ : Set G) ∧
      centralizer (d.I₁ : Set G) ≤ normalizer (d.M₁ : Set G) ∧
      d.N₁ ≤ d.M₁ ∧ ⁅d.M₁, d.M₁⁆ = d.M₁ ∧
      Odd (Nat.card (center d.M₁)) ∧ center d.M₁ = ⊥ ∧
      Xor
        (∃ (k : Type) (_ : Field k) (_ : Fintype k), Fintype.card k = (2 ^ f) ^ 2 ∧
          ∃ (ψ : d.M₁ ⧸ center d.M₁ ≃* SL(2, k) × SL(2, k)) (α : d.N₁ ≃* SL(2, k)),
            (∀ (a : d.N₁) (x : d.M₁), (x : G) = a →
              ψ (x : d.M₁ ⧸ center d.M₁) = (α a, α a)) ∧
            ∀ (x y : d.M₁) (y₁ y₂ : SL(2, k)), (y : G) = d.t⁻¹ * x * d.t →
              ψ (x : d.M₁ ⧸ center d.M₁) = (y₁, y₂) → ψ (y : d.M₁ ⧸ center d.M₁) = (y₂, y₁))
        (∃ (k₂ : Type) (_ : Field k₂) (_ : Fintype k₂), Fintype.card k₂ = ((2 ^ f) ^ 2) ^ 2 ∧
          ∃ ψ : d.M₁ ⧸ center d.M₁ ≃* SL(2, k₂),
            (∀ x y : d.M₁, (y : G) = d.t⁻¹ * x * d.t →
              ((ψ (y : d.M₁ ⧸ center d.M₁) : SL(2, k₂)) : Matrix (Fin 2) (Fin 2) k₂) =
                (ψ (x : d.M₁ ⧸ center d.M₁) : Matrix (Fin 2) (Fin 2) k₂).map
                  (fun c => c ^ (2 ^ f) ^ 2)) ∧
            ∀ g : SL(2, k₂),
              g ∈ ((d.N₁.subgroupOf d.M₁).map (QuotientGroup.mk' (center d.M₁))).map
                  ψ.toMonoidHom ↔
                ∀ i j, (g : Matrix (Fin 2) (Fin 2) k₂) i j ^ (2 ^ f) ^ 2 =
                  (g : Matrix (Fin 2) (Fin 2) k₂) i j) ∧
      Odd (Nat.card (centralizer (d.I₁ : Set G) ⊓ centralizer (d.M₁ : Set G) : Subgroup G)) := by
  rcases Nat.lt_or_ge f 3 with hf | hf
  · exact hd.sec3_5_three_four hGMS hL (by have := hd.two_le; omega)
  · exact hd.sec3_5_three hGMS hf

theorem Hyp.sec3_5_three_iso_all (hGMS : GMSK.GMSUnitarySharpKRankOneStatement)
    (hL : GMSK.GMSLinearStandardLayerListKRankOneStatement) (hd : d.Hyp) :
    Xor
      (∃ (k : Type) (_ : Field k) (_ : Fintype k), Fintype.card k = (2 ^ f) ^ 2 ∧
        ∃ (ψ : d.M₁ ≃* SL(2, k) × SL(2, k)) (α : d.N₁ ≃* SL(2, k)),
          (∀ (a : d.N₁) (x : d.M₁), (x : G) = a → ψ x = (α a, α a)) ∧
          ∀ (x y : d.M₁) (y₁ y₂ : SL(2, k)), (y : G) = d.t⁻¹ * x * d.t →
            ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
      (∃ (k₂ : Type) (_ : Field k₂) (_ : Fintype k₂), Fintype.card k₂ = ((2 ^ f) ^ 2) ^ 2 ∧
        ∃ ψ : d.M₁ ≃* SL(2, k₂),
          (∀ x y : d.M₁, (y : G) = d.t⁻¹ * x * d.t →
            ((ψ y : SL(2, k₂)) : Matrix (Fin 2) (Fin 2) k₂) =
              (ψ x : Matrix (Fin 2) (Fin 2) k₂).map (fun c => c ^ (2 ^ f) ^ 2)) ∧
          ∀ g : SL(2, k₂),
            g ∈ (d.N₁.subgroupOf d.M₁).map ψ.toMonoidHom ↔
              ∀ i j, (g : Matrix (Fin 2) (Fin 2) k₂) i j ^ (2 ^ f) ^ 2 =
                (g : Matrix (Fin 2) (Fin 2) k₂) i j) := by
  obtain ⟨-, -, -, -, -, hZ, hXor, -⟩ := hd.sec3_5_three_all hGMS hL
  set M := d.M₁ with hMdef
  let c : M ≃* M ⧸ center M :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  have hc : ∀ x : M, c x = (x : M ⧸ center M) := fun x =>
    (MulEquiv.symm_apply_eq _).2 rfl
  have hcm : c.toMonoidHom = QuotientGroup.mk' (center M) := MonoidHom.ext hc
  have hexcl : ∀ (k : Type) (_ : Field k) (_ : Fintype k) (k₂ : Type) (_ : Field k₂)
      (_ : Fintype k₂), Fintype.card k₂ = ((2 ^ f) ^ 2) ^ 2 →
      (M ⧸ center M ≃* SL(2, k) × SL(2, k)) → (M ≃* SL(2, k₂)) → False := by
    intro k _ _ k₂ _ _ hk₂ ψ₁ ψ₂
    have hk₂' : Nat.card k₂ = 2 ^ (4 * f) := by
      rw [Nat.card_eq_fintype_card, hk₂, ← pow_mul, ← pow_mul]
      ring_nf
    exact (GMS.isEmpty_mulEquiv_sl2_prod (k := k) (by have := hd.two_le; omega) hk₂').false
      ((ψ₂.symm.trans c).trans ψ₁)
  rcases hXor with ⟨⟨k, _, _, hk, ψ, α, hψA, hψt⟩, -⟩ | ⟨⟨k₂, _, _, hk₂, ψ, hψt, hψA⟩, -⟩
  · refine Or.inl ⟨⟨k, inferInstance, inferInstance, hk, c.trans ψ, α, fun a x hxa => ?_,
      fun x y y₁ y₂ hxy hx => ?_⟩, ?_⟩
    · rw [MulEquiv.trans_apply, hc]
      exact hψA a x hxa
    · rw [MulEquiv.trans_apply, hc] at hx ⊢
      exact hψt x y y₁ y₂ hxy hx
    · rintro ⟨k₂, _, _, hk₂, ψ₂, -⟩
      exact hexcl k inferInstance inferInstance k₂ inferInstance inferInstance hk₂ ψ ψ₂
  · refine Or.inr ⟨⟨k₂, inferInstance, inferInstance, hk₂, c.trans ψ, fun x y hxy => ?_,
      fun g => ?_⟩, ?_⟩
    · rw [MulEquiv.trans_apply, hc, MulEquiv.trans_apply, hc]
      exact hψt x y hxy
    · rw [← hψA g, ← hcm, map_map]
      rfl
    · rintro ⟨k, _, _, -, ψ₁, -⟩
      exact hexcl k inferInstance inferInstance k₂ inferInstance inferInstance hk₂
        (c.symm.trans ψ₁) (c.trans ψ)

end Certified

end Data

end CFSG.LocalAnalysis.EvenBN.U5
