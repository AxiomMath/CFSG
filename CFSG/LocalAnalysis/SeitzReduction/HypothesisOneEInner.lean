module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneEInnerBasic
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneF4Inner

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit rootChar)
open scoped commutatorElement

variable {τ : Tag} {K : Type} [Field K]

theorem mem_of_mem_posUnipotent_of_forall_pinnedX
    {H : Subgroup (adjointGroup τ K)}
    (h : ∀ γ, IsRoot τ γ → 0 < height γ → ∀ c : K,
      (⟨pinnedX τ K γ c, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup τ K) ∈ H)
    {u : adjointGroup τ K} (hu : (u : ModGL τ K) ∈ posUnipotent τ K) : u ∈ H := by
  have hle : posUnipotent τ K ≤ H.map (adjointGroup τ K).subtype := by
    rw [posUnipotent, rootSpan_eq_closure, Subgroup.closure_le]
    rintro _ ⟨β, hβ, d, rfl⟩
    exact ⟨_, h β hβ.1 hβ.2 d, rfl⟩
  obtain ⟨x, hx, hxu⟩ := hle hu
  rwa [show u = x from Subtype.ext hxu.symm]

theorem pinnedX_mem_closure_of_conj_tag
    {t h : adjointGroup τ K} (hh : h * t = t * h)
    (hho : Odd (orderOf h)) {γ : Fin τ.rank → ℤ} {l : K} (hl : l ≠ 1)
    (hconj : ∀ d : K, (h : ModGL τ K) * pinnedX τ K γ d * (h : ModGL τ K)⁻¹ =
      pinnedX τ K γ (l * d))
    (hγt : ∀ d : K, (⟨pinnedX τ K γ d, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup τ K) * t =
      t * ⟨pinnedX τ K γ d, pinnedX_mem_adjointGroup _ _⟩) (c : K) :
    (⟨pinnedX τ K γ c, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup τ K) ∈
      closure {x : adjointGroup τ K | x * t = t * x ∧ Odd (orderOf x)} := by
  have hl' : l - 1 ≠ 0 := sub_ne_zero.2 hl
  set d := c / (l - 1)
  set u : adjointGroup τ K := ⟨pinnedX τ K γ d, pinnedX_mem_adjointGroup _ _⟩
  have e : (⟨pinnedX τ K γ c, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup τ K) =
      h * (u * h⁻¹ * u⁻¹) := by
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, u]
    rw [← mul_assoc, ← mul_assoc, hconj, pinnedX_neg, ← pinnedX_add]
    congr 1
    simp only [d]
    field_simp
    ring
  rw [e]
  exact mul_mem (subset_closure ⟨hh, hho⟩)
    (subset_closure (conj_inv_mem_oddCentralizer hh hho (hγt d)))

theorem torusElt_conj_pinnedX_coPair
    (i : Fin τ.rank) (u : Kˣ) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) (c : K) :
    torusElt τ K i u * pinnedX τ K γ c * (torusElt τ K i u)⁻¹ =
      pinnedX τ K γ (((u ^ coPair τ i γ : Kˣ) : K) * c) := by
  rw [torusElt_eq_rootDiagUnit, rootDiagUnit_conj_pinnedX _ hγ]
  congr 3
  simp only [rootChar, coPair, ← zpow_mul]
  exact prod_zpow_eq_zpow_sum _ _ _

theorem odd_orderOf_torusElt
    {f : ℕ} (hf : 1 ≤ f) [Finite K] (hK : Nat.card K = 2 ^ f) (i : Fin τ.rank) (u : Kˣ) :
    Odd (orderOf (torusElt τ K i u)) := by
  let φ : Kˣ →* ModGL τ K :=
    (rootDiagUnitHom τ K).comp (MonoidHom.pi fun j => zpowGroupHom (τ.cartan i j))
  have hφ : φ u = torusElt τ K i u := (torusElt_eq_rootDiagUnit i u).symm
  have hodd : Odd (Nat.card Kˣ) := by
    rw [Nat.card_units, hK]
    have h2 : 2 ^ f = 2 * 2 ^ (f - 1) := by rw [← pow_succ']; congr 1; omega
    have h1 : 1 ≤ 2 ^ (f - 1) := Nat.one_le_two_pow
    exact ⟨2 ^ (f - 1) - 1, by omega⟩
  rw [← hφ]
  exact hodd.of_dvd_nat ((orderOf_map_dvd φ u).trans (orderOf_dvd_natCard u))

theorem mem_map_radicalIn_empty_iff_tag
    {u : (RootWeightDatum.ordinary (K := K) τ).group} :
    u ∈ ((RootWeightDatum.ordinary τ).radicalIn ∅).map
        (MulAut.conj (1 : (RootWeightDatum.ordinary (K := K) τ).group)).toMonoidHom ↔
      (u.1 : ModGL τ K) ∈ posUnipotent τ K := by
  rw [map_one, show (1 : MulAut (RootWeightDatum.ordinary (K := K) τ).group).toMonoidHom =
      MonoidHom.id _ from rfl, Subgroup.map_id, RootWeightDatum.radicalIn,
    Subgroup.mem_subgroupOf]
  change (u.1 : ModGL τ K) ∈ parabolicRadical τ K ∅ ↔ _
  rw [parabolicRadical_empty]


theorem pinnedX_mem_closure_odd_E (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {f : ℕ} (hf : 2 ≤ f)
    [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f) {t : adjointGroup τ K}
    (ht : (t : ModGL τ K) = pinnedX τ K (highRoot τ) 1) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hγp : 0 < height γ) (c : K) :
    (⟨pinnedX τ K γ c, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup τ K) ∈
      closure {x : adjointGroup τ K | x * t = t * x ∧ Odd (orderOf x)} := by
  set S := {x : adjointGroup τ K | x * t = t * x ∧ Odd (orderOf x)}
  obtain ⟨c₀, hc₀0, hc₀1⟩ : ∃ c₀ : K, c₀ ≠ 0 ∧ c₀ ≠ 1 := by
    by_contra hcon'
    have hcon : ∀ x : K, x ≠ 0 → x = 1 := fun x hx => by_contra fun h => hcon' ⟨x, hx, h⟩
    have hsurj : Function.Surjective (fun b : Bool => if b then (1 : K) else 0) := by
      intro x
      by_cases hx : x = 0
      · exact ⟨false, by simp [hx]⟩
      · exact ⟨true, by simp [hcon x hx]⟩
    have hle := Nat.card_le_card_of_surjective _ hsurj
    rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool, hK] at hle
    have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  set w : Kˣ := Units.mk0 c₀ hc₀0
  have hw : w ≠ 1 := fun h => hc₀1 (by simpa [w] using congrArg Units.val h)
  have hUt : ∀ β, IsRoot τ β → 0 < height β → ∀ d : K,
      (⟨pinnedX τ K β d, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup τ K) * t =
        t * ⟨pinnedX τ K β d, pinnedX_mem_adjointGroup _ _⟩ := fun β hβ hβp d => by
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul, ht]
    exact (commute_pinnedX_highRoot K hβ hβp d 1).eq
  have hgen : ∀ β, IsRoot τ β → 0 < height β → β ≠ highRoot τ → ∀ d : K,
      (⟨pinnedX τ K β d, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup τ K) ∈ closure S := by
    intro β hβ hβp hβr d
    obtain ⟨i, hi0, hi⟩ := exists_coPair_highRoot_eq_zero hτ hβ hβp hβr
    set h : adjointGroup τ K := ⟨torusElt τ K i w, torusElt_mem_adjointGroup i w⟩
    have hh : h * t = t * h := by
      refine Subtype.ext ?_
      simp only [Subgroup.coe_mul, ht, h]
      have e := torusElt_conj_pinnedX_coPair i w (isRoot_highRoot τ) 1
      rw [hi0, zpow_zero, Units.val_one, one_mul] at e
      exact mul_inv_eq_iff_eq_mul.1 e
    have hho : Odd (orderOf h) := by
      rw [← Subgroup.orderOf_coe]
      exact odd_orderOf_torusElt (by omega) hK i w
    have hl : ((w ^ coPair τ i β : Kˣ) : K) ≠ 1 := by
      rw [Ne, Units.val_eq_one]
      exact zpow_ne_one_of_charTwo hw (by simpa using hi)
    exact pinnedX_mem_closure_of_conj_tag hh hho hl
      (fun e => torusElt_conj_pinnedX_coPair i w hβ e) (hUt β hβ hβp) d
  by_cases hγr : γ = highRoot τ
  · subst hγr
    obtain ⟨hβ, hsum, hβp, hβr, hβe, hβe', her⟩ := highRoot_decomp hτ
    have hroot : IsRoot τ (highRoot τ - Pi.single (highNode τ) 1 + Pi.single (highNode τ) 1) :=
      hsum.symm ▸ isRoot_highRoot τ
    obtain ⟨hε, hcomm⟩ := (simply_laced_root_commutator_unit.{0} τ (Or.inr hτ) hβ
      (isRoot_single τ (highNode τ)) hβe hβe').1 hroot
    set ε : K := (commConst τ (highRoot τ - Pi.single (highNode τ) 1)
      (Pi.single (highNode τ) 1) (1, 1) : K) with hε_def
    have hεε : ε * ε = 1 := by
      rcases hε with h | h <;> simp [ε, h]
    have e1 : pinnedX τ K (highRoot τ) c = ⁅pinnedX τ K (highRoot τ - Pi.single (highNode τ) 1) 1,
        pinnedX τ K (Pi.single (highNode τ) 1) (ε * c)⁆ := by
      rw [hcomm K 1 (ε * c), hsum, mul_one, ← mul_assoc, hεε, one_mul]
    have hx := hgen _ hβ hβp hβr 1
    have hy := hgen _ (isRoot_single τ (highNode τ)) (by rw [height_single]; omega) her (ε * c)
    have e2 : (⟨pinnedX τ K (highRoot τ) c, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup τ K) =
        ⁅(⟨pinnedX τ K (highRoot τ - Pi.single (highNode τ) 1) 1, pinnedX_mem_adjointGroup _ _⟩ :
          adjointGroup τ K), ⟨pinnedX τ K (Pi.single (highNode τ) 1) (ε * c),
            pinnedX_mem_adjointGroup _ _⟩⁆ := by
      refine Subtype.ext ?_
      change pinnedX τ K (highRoot τ) c = _
      rw [e1, commutatorElement_def, commutatorElement_def]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e2, commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  · exact hgen γ hγ hγp hγr c

theorem mem_borelGroup_of_conj_inv_posUnipotent {g : adjointGroup τ K}
    (hconj : ∀ v : adjointGroup τ K, (v : ModGL τ K) ∈ posUnipotent τ K →
      ((g⁻¹ * v * g : adjointGroup τ K) : ModGL τ K) ∈ posUnipotent τ K) :
    (g : ModGL τ K) ∈ borelGroup τ K := by
  have hB := borel_self_normalizers τ K
  have hBN : borelGroup τ K ≤ Subgroup.normalizer (posUnipotent τ K : Set (ModGL τ K)) :=
    fun b hb => (Subgroup.mem_inf.1 (hB.1.symm ▸ hb : b ∈ _)).2
  have hUB : posUnipotent τ K ≤ borelGroup τ K := le_sup_right
  have hBC : borelGroup τ K ≤ adjointGroup τ K := borelGroup_le_adjointGroup_of_field
  have hgB : ((g⁻¹ : adjointGroup τ K) : ModGL τ K) ∈ borelGroup τ K := by
    refine mem_borelGroup_of_conj_posUnipotent_le (g⁻¹).2 fun b hb b' hb' w hw u hu => ?_
    have hn : canonicalRep (coxeterSystem τ) K w =
        b⁻¹ * ((g⁻¹ : adjointGroup τ K) : ModGL τ K) * b'⁻¹ := by
      rw [← hw]; group
    have hv : b'⁻¹ * u * b' ∈ posUnipotent τ K := by
      have := (Subgroup.mem_normalizer_iff.1 (hBN (inv_mem hb')) u).1 hu
      simpa using this
    have hw' := hconj ⟨b'⁻¹ * u * b', hBC (hUB hv)⟩ hv
    have hx := (Subgroup.mem_normalizer_iff.1 (hBN (inv_mem hb)) _).1 hw'
    rw [hn]
    refine hUB ?_
    convert hx using 1
  simpa using inv_mem hgB

theorem eq_zero_of_borel_conj_pinnedX_single [Finite K] {g : ModGL τ K}
    (hg : g ∈ borelGroup τ K) {i j : Fin τ.rank} (hij : i ≠ j) {c : K}
    (h : pinnedX τ K (Pi.single j 1) c = g⁻¹ * pinnedX τ K (Pi.single i 1) 1 * g) : c = 0 := by
  have hgHU : g ∈ (borelGroup τ K : Set (ModGL τ K)) := hg
  rw [(triangular_borel_structure.{0, 0} τ K).2.2.2.2.1] at hgHU
  obtain ⟨d, hd, u₀, hu₀, rfl⟩ := Set.mem_mul.1 hgHU
  rw [show (d * u₀)⁻¹ * pinnedX τ K (Pi.single i 1) 1 * (d * u₀) =
      u₀⁻¹ * (d⁻¹ * pinnedX τ K (Pi.single i 1) 1 * d⁻¹⁻¹) * u₀⁻¹⁻¹ by group,
    conj_pinnedX_of_mem_torusGroup (inv_mem hd) (isRoot_single τ i)] at h
  have hj : IsRoot τ (Pi.single j 1) ∧ 0 < height (Pi.single j 1 : Fin τ.rank → ℤ) :=
    ⟨isRoot_single τ j, by rw [height_single]; omega⟩
  have hmem : pinnedX τ K (Pi.single i 1) (torusRootChar d⁻¹ (Pi.single i 1) * 1) ∈
      heightSeries τ K (height (Pi.single j 1 : Fin τ.rank → ℤ)) := by
    rw [height_single, heightSeries_one]
    exact pinnedX_single_mem_posUnipotent i _
  have hc := congrArg (rootCoord hj) h
  rw [rootCoord_self, rootCoord_conj hj (inv_mem hu₀) hmem,
    rootCoord_pinnedX_of_ne hj ⟨isRoot_single τ i, by rw [height_single]; omega⟩
      (by rw [height_single, height_single])
      (fun e => hij (by
        have h1 := congrFun e i
        rw [Pi.single_eq_same, Pi.single_apply] at h1
        by_contra hne
        rw [ite_eq_right hne] at h1
        exact one_ne_zero h1))] at hc
  exact hc

theorem mem_diagonalFieldActors_E6_of_forall_posUnipotent [Finite K]
    (β : MulAut (adjointGroup .E6 K))
    (hβ : ∀ u : adjointGroup .E6 K, (u : ModGL .E6 K) ∈ posUnipotent .E6 K → β u = u) :
    β ∈ diagonalFieldActors .E6 K := by
  obtain ⟨g, a, σ, ⟨ε, hε⟩, hα⟩ :=
    (ordinary_E_exact_automorphism_normal_form .E6 (Or.inl rfl) K).2.2 β
  rcases ε with _ | _ | ε
  · refine (EvenExceptionalActorCoverage.mem_diagonalFieldActors_iff β).2
      ⟨g, g.2, a, σ, fun x => ?_⟩
    rw [hα x, show exactQ .E6 K ((⟨0, hε⟩ : Fin (exactE .E6)) : ℕ) = 1 from exactQ_zero .E6 K]
    group
  · exfalso
    let i₁ : Fin Tag.E6.rank := ⟨0, by decide⟩
    let i₆ : Fin Tag.E6.rank := ⟨5, by decide⟩
    set γ := exactNormalAut .E6 K a σ 1 with hγ_def
    have hβγ : ∀ x, β x = g * γ x * g⁻¹ := fun x => Subtype.ext (by
      rw [hα x, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hγ_def,
        coe_exactNormalAut]
      simp only [mul_assoc])
    have hγU : ∀ v : adjointGroup .E6 K, (v : ModGL .E6 K) ∈ posUnipotent .E6 K →
        ((γ v : adjointGroup .E6 K) : ModGL .E6 K) ∈ posUnipotent .E6 K := by
      intro v hv
      have hm := (exactNormalAut_mem a σ 1).1
      have h1 : γ v ∈ ((posUnipotent .E6 K).subgroupOf (adjointGroup .E6 K)).map
          γ.toMonoidHom := ⟨v, hv, rfl⟩
      rw [hm] at h1
      exact h1
    have hconj : ∀ v : adjointGroup .E6 K, (v : ModGL .E6 K) ∈ posUnipotent .E6 K →
        ((g⁻¹ * v * g : adjointGroup .E6 K) : ModGL .E6 K) ∈ posUnipotent .E6 K := by
      intro v hv
      have h := hβ v hv
      rw [hβγ] at h
      have e' := congrArg (fun x => g⁻¹ * x * g) h
      have e : g⁻¹ * v * g = γ v := by
        rw [← e']
        group
      rw [e]
      exact hγU v hv
    have hx1 : ((adjX .E6 K i₁ 1 : adjointGroup .E6 K) : ModGL .E6 K) ∈ posUnipotent .E6 K := by
      change xUnit .E6 K i₁ 1 ∈ _
      rw [← pinnedX_single]
      exact pinnedX_single_mem_posUnipotent i₁ 1
    have hfix := hβ _ hx1
    rw [hβγ, hγ_def, exactNormalAut_adjX, show exactPerm .E6 1 i₁ = i₆ by decide, map_one,
      mul_one] at hfix
    have e : (adjX .E6 K i₆ (a i₆) : adjointGroup .E6 K) = g⁻¹ * adjX .E6 K i₁ 1 * g := by
      rw [← hfix]
      group
    have e' := congrArg Subtype.val e
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e'
    change xUnit .E6 K i₆ (a i₆) = (g : ModGL .E6 K)⁻¹ * xUnit .E6 K i₁ 1 * g at e'
    rw [← pinnedX_single, ← pinnedX_single] at e'
    exact (a i₆).ne_zero (eq_zero_of_borel_conj_pinnedX_single
      (mem_borelGroup_of_conj_inv_posUnipotent hconj) (by decide) e')
  · simp [exactE] at hε

theorem mem_diagonalFieldActors_E_of_forall_posUnipotent (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {f : ℕ} (hf : 1 ≤ f) [Finite K] (hK : Nat.card K = 2 ^ f) (β : MulAut (adjointGroup τ K))
    (hβ : ∀ u : adjointGroup τ K, (u : ModGL τ K) ∈ posUnipotent τ K → β u = u) :
    β ∈ diagonalFieldActors τ K := by
  rcases hτ with rfl | hτ'
  · exact mem_diagonalFieldActors_E6_of_forall_posUnipotent β hβ
  · rw [EvenExceptionalActorCoverage.diagonalFieldActors_E7_E8_eq_top hf hK hτ']
    exact mem_top β

theorem innerCentralizerCriterion_E_of_posUnipotent_le (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {f : ℕ} (hf : 1 ≤ f) [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f)
    {t : adjointGroup τ K}
    (hodd : ∀ u : adjointGroup τ K, (u : ModGL τ K) ∈ posUnipotent τ K →
      u ∈ closure {c : adjointGroup τ K | c * t = t * c ∧ Odd (orderOf c)}) :
    InnerCentralizerCriterion t := by
  have hJ : (∅ : Set (Fin (RootWeightDatum.ordinary (K := K) τ).rank)) ≠ Set.univ := by
    intro h
    have := Set.mem_univ (⟨0, CFSG.Blueprint.Chevalley.Tag.rank_pos τ⟩ :
      Fin (RootWeightDatum.ordinary (K := K) τ).rank)
    rw [← h] at this
    exact this
  refine innerCentralizerCriterion_of_conj_radical (RootWeightDatum.ordinary τ) hJ 1 (t := t)
    (fun u hu => hodd u (mem_map_radicalIn_empty_iff_tag.1 hu)) (fun z hz hc _ => ?_)
    (fun β hβ => mem_diagonalFieldActors_E_of_forall_posUnipotent hτ hf hK β
      fun u hu => hβ u (mem_map_radicalIn_empty_iff_tag.2 hu))
  have hz' := mem_map_radicalIn_empty_iff_tag.1 hz
  refine Subtype.ext ?_
  rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
  exact sq_eq_one_of_commute_posUnipotent_E hτ hz' fun u hu => congrArg Subtype.val
    (hc (⟨u, posUnipotent_le_adjointGroup hu⟩ : (RootWeightDatum.ordinary τ).group)
      (mem_map_radicalIn_empty_iff_tag.2 hu))

theorem innerCentralizerCriterion_E_longRoot (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {f : ℕ}
    (hf : 2 ≤ f) [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f) :
    InnerCentralizerCriterion
      (⟨pinnedX τ K (highRoot τ) 1, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup τ K) :=
  innerCentralizerCriterion_E_of_posUnipotent_le hτ (by omega) hK fun _ hu =>
    mem_of_mem_posUnipotent_of_forall_pinnedX
      (fun _ hγ hγp c => pinnedX_mem_closure_odd_E hτ hf hK rfl hγ hγp c) hu

end CFSG.SeitzReduction
