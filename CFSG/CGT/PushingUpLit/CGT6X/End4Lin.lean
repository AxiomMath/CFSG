module

public import CFSG.CGT.PushingUpLit.CGT6X.End4Frame
public import CFSG.CGT.PushingUpLit.CGT6X.End4Cover
public import CFSG.CGT.PushingUpLit.CGT6X.End4Core
public import CFSG.CGT.PushingUpLit.CGT6X.End3Cfg
public import CFSG.LieType.Steinberg.CentralExt.SLCentrallyClosed

public section

namespace CFSG.CGT.PushingUpLit.CGT6X.End4

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.CGT.PushingUpLit.CGT6X.K7a CFSG.CGT.PushingUpLit.CGT6X.End3 CFSG.Quasithin
  CFSG.CGT.PushingUpLit.CGT6 CFSG.SL2MinimalFaithful CFSG.LocalAnalysis
  CFSG.LieType.Steinberg.CentralExt CFSG.ComponentClassification.CatalogueBGraphForm
open CFSG.Open (StatedClassicalModel)

section Elements

variable {K : Type} [Field K] [CharP K 2] (s : K)

@[expose] def kapSL (t : Kˣ × Kˣ × Kˣ) (ht : t.1 * t.2.1 * t.2.2 = 1) :
    SpecialLinearGroup (Fin 3) K :=
  ⟨tm s t.1 t.2.1 t.2.2, by rw [det_tm]; simpa using congrArg Units.val ht⟩

theorem toGL_kapSL (t : Kˣ × Kˣ × Kˣ) (ht : t.1 * t.2.1 * t.2.2 = 1) :
    SpecialLinearGroup.toGL (kapSL s t ht) = kap s t := Units.ext rfl

@[expose] def wSL : SpecialLinearGroup (Fin 3) K :=
  ⟨wm s, by
    have h := congrArg Matrix.det (wm_sq s)
    rw [det_mul, det_one] at h
    exact eq_one_of_sq_eq_one (by rw [pow_two]; exact h)⟩

theorem toGL_wSL : SpecialLinearGroup.toGL (wSL s) = wGL s := Units.ext rfl

end Elements

section Main

variable {V : Type} [CommGroup V] [Finite V]

theorem end411_linear (hV : ∀ v : V, v ^ 2 = 1) {L Y : Subgroup (MulAut V)} (hYL : Y ≤ L)
    [Group.IsPerfect ↥L] (hSQ : SimpleQuot Y) (hgen : CommGen Y) {t : MulAut V}
    (htN : t ∈ Subgroup.normalizer (L : Set (MulAut V))) (ht2 : t ^ 2 = 1)
    (htY : ∀ y ∈ Y, t * y = y * t)
    (hτout : ∀ x : ↥L ⧸ Subgroup.center ↥L,
      centerAutHom ↥L (conjOn L t htN) ≠ MulAut.conj x)
    {f : ℕ} (hf : 3 ≤ f) {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ f)
    (hYF : Nonempty (↥Y ≃* Matrix.SpecialLinearGroup (Fin 2) F))
    (hmod : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 3 2 f) : False := by
  set Y' : Subgroup ↥L := Y.subgroupOf L with hY'def
  obtain ⟨φ⟩ := hYF
  let φ' : ↥Y' ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (Subgroup.subgroupOfEquivOfLe hYL).trans φ
  have hτ2 : conjOn L t htN ^ 2 = 1 := conjOn_sq L t htN ht2
  have hYτ : ∀ y ∈ Y', conjOn L t htN y = y := fun y hy =>
    conjOn_fixes L t htN y (htY y hy)
  obtain ⟨K, _, _, hK, e, H, hHτ, hHY⟩ :=
    K7a_linear_model (L := ↥L) (by omega) hmod (conjOn L t htN) hτ2 hτout Y' hF ⟨φ'⟩ hYτ
  have hcharK : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK
  set cH : MulAut (projectiveSL 3 K) := conjAut 3 K H with hcH
  let e' : (↥L ⧸ Subgroup.center ↥L) ≃* projectiveSL 3 K := e.trans cH⁻¹
  have he'τ : ∀ y : ↥L, e' (QuotientGroup.mk (conjOn L t htN y)) =
      dualAut 3 K (e' (QuotientGroup.mk y)) := by
    intro y
    have h1 := hHτ (QuotientGroup.mk y)
    rw [centerAutHom_mk] at h1
    show cH⁻¹ (e (QuotientGroup.mk (conjOn L t htN y))) =
      dualAut 3 K (cH⁻¹ (e (QuotientGroup.mk y)))
    rw [h1]
    simp [MulAut.mul_apply]
  have hO : ∀ y ∈ Y', ∃ o ∈ orthSL K, e' (QuotientGroup.mk y) = proj 3 K o := by
    intro y hy
    have h1 : e (QuotientGroup.mk y) ∈
        (orthProj K).map (cH : MulAut (projectiveSL 3 K)).toMonoidHom := by
      rw [← hHY]
      exact ⟨QuotientGroup.mk y, ⟨y, hy, rfl⟩, rfl⟩
    obtain ⟨x, hx, hxy⟩ := h1
    obtain ⟨o, ho, rfl⟩ := mem_orthProj.mp hx
    refine ⟨o, ho, ?_⟩
    show cH⁻¹ (e (QuotientGroup.mk y)) = _
    rw [← hxy]
    simp
  have hK5 : 5 ≤ Nat.card K := by
    rw [hK]
    calc 5 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* SpecialLinearGroup (Fin 3) K),
      Function.Surjective π → π.ker ≤ Subgroup.center E →
        ∃ σ : SpecialLinearGroup (Fin 3) K →* E, ∀ g, π (σ g) = g := fun E _ _ π hπ hcen =>
    SLClosed.sl_exists_section_of_central (m := 2) (by norm_num) hK5 hπ hcen
  obtain ⟨ρ, hρ⟩ := exists_cover e' (proj 3 K) hsplit
  have hMperf : Group.IsPerfect (SpecialLinearGroup (Fin 3) K) :=
    LinearGroups.special_linear_isPerfect (by norm_num) (Or.inl le_rfl)
  have hint := cover_intertwine e' (proj 3 K) ρ hρ (conjOn L t htN).toMonoidHom
    (dualAut 3 K).toMonoidHom (slGraphAut 3 K).toMonoidHom he'τ
    (fun m => (dualAut_proj m).symm)
  have hF4 : ∃ s : Finset F, s.card = 4 := by
    have : Fintype F := Fintype.ofFinite F
    have h4 : 4 ≤ (Finset.univ : Finset F).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hF]
      calc 4 ≤ 2 ^ 3 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq h4
    exact ⟨s, hs⟩
  have hY'perf : Group.IsPerfect ↥Y' := by
    have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) :=
      LinearGroups.special_linear_dimension_two_perfect hF4
    exact Group.IsPerfect.ofSurjective (f := φ'.symm.toMonoidHom) φ'.symm.surjective
  have hcardY : Nat.card (orthSL K) ≤ Nat.card ↥Y' := by
    calc Nat.card (orthSL K) ≤ Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := card_orthSL_le
      _ = Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
          rw [card_specialLinearGroup_fin_two, card_specialLinearGroup_fin_two, hF, hK]
      _ = Nat.card ↥Y' := (Nat.card_congr φ'.toEquiv).symm
  have hYO' : Y' = (orthSL K).map ρ :=
    eq_map_of_perfect e' (proj 3 K) ρ hρ Y' Subgroup.commutator_eq_self (orthSL K) hO hcardY
  set ρ' : SpecialLinearGroup (Fin 3) K →* MulAut V := L.subtype.comp ρ with hρ'
  have hYO : Y = (orthSL K).map ρ' := by
    have h1 : Y'.map L.subtype = Y := Subgroup.map_subgroupOf_eq_of_le hYL
    rw [← h1, hYO', Subgroup.map_map]
  have hγ' : ∀ m, t * ρ' m * t⁻¹ = ρ' (slGraphAut 3 K m) := by
    intro m
    have h1 := congrArg (fun φ : SpecialLinearGroup (Fin 3) K →* ↥L => ((φ m : ↥L) : MulAut V))
      hint
    simpa [conjOn_apply, hρ'] using h1
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hordA : orderOf a = Nat.card Kˣ := orderOf_eq_card_of_forall_mem_zpowers ha
  have han : a ^ Nat.card Kˣ = 1 := pow_card_eq_one'
  have hnK : Nat.card Kˣ = 2 ^ f - 1 := by rw [Nat.card_units, hK]
  have hn7 : 7 ≤ Nat.card Kˣ := by
    rw [hnK]
    have : 2 ^ 3 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  have hnodd : Odd (Nat.card Kˣ) := by
    rw [hnK]
    have h2 : Even (2 ^ f) := (Nat.even_pow.2 ⟨even_two, by omega⟩)
    obtain ⟨k, hk⟩ := h2
    have : 8 ≤ 2 ^ f := by
      have : 2 ^ 3 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
      omega
    exact ⟨k - 1, by omega⟩
  have ha3 : a ^ 3 ≠ 1 := by
    intro h
    have h1 := orderOf_dvd_of_pow_eq_one h
    rw [hordA] at h1
    have := Nat.le_of_dvd (by norm_num) h1
    omega
  let α : SpecialLinearGroup (Fin 3) K := kapSL 0 (1, a, a⁻¹) (by simp)
  let δ : SpecialLinearGroup (Fin 3) K := kapSL 0 (a⁻¹ * a⁻¹, a, a) (by group)
  let ω : SpecialLinearGroup (Fin 3) K := wSL 0
  obtain ⟨hrel, hαn, hδn⟩ := torus_elements (0 : K) SpecialLinearGroup.toGL
    SpecialLinearGroup.toGL_injective a han (α := α) (δ := δ) (ω := ω) (toGL_kapSL 0 _ _)
    (toGL_kapSL 0 _ _) (toGL_wSL 0)
  have hαO : α ∈ orthSL K := by
    rw [mem_orthSL]
    have h1 : (α : Matrix (Fin 3) (Fin 3) K) = tm 0 ((1 : Kˣ) : K) (a : K) ((a⁻¹ : Kˣ) : K) := rfl
    rw [h1, tm_transpose, tm_mul]
    simpa using tm_one (0 : K)
  have hδC : ∀ o ∈ orthSL K, δ * o = o * δ := by
    intro o ho
    apply Subtype.ext
    have h1 : (δ : Matrix (Fin 3) (Fin 3) K) =
        tm 0 ((a⁻¹ * a⁻¹ : Kˣ) : K) (a : K) (a : K) := rfl
    show (δ : Matrix (Fin 3) (Fin 3) K) * (o : Matrix (Fin 3) (Fin 3) K) =
      (o : Matrix (Fin 3) (Fin 3) K) * δ
    rw [h1]
    exact (tm_comm 0 (row_sum_of_mem ho) (col_sum_of_mem ho) _ _).symm
  have hγδ : slGraphAut 3 K δ = δ⁻¹ := by
    apply SpecialLinearGroup.toGL_injective
    rw [toGL_slGraphAut, map_inv, toGL_kapSL]
    apply Units.ext
    rw [glGraphAut_matrix, ← map_inv, kap_coe, tm_transpose]
    rfl
  have hcore := end411_core hV hSQ hgen ht2 htY ρ' (fun m => slGraphAut 3 K m) (orthSL K) hYO hγ'
    hnodd hαO hδC hγδ hαn hδn hrel
  have h1 : ρ δ = 1 := Subtype.ext (by simpa [hρ'] using hcore)
  have h2 : proj 3 K δ = 1 := by
    rw [← hρ, h1]
    simp
  have h3 : δ ∈ scalars 3 K := by
    rw [← ker_proj]
    exact h2
  obtain ⟨c, -, hc⟩ := mem_scalars.mp h3
  have h4 : ((a⁻¹ * a⁻¹ : Kˣ) : K) = (a : K) := eq_of_tm_scalar 0 _ _ _ hc
  have h5 : a⁻¹ * a⁻¹ = a := Units.ext h4
  apply ha3
  calc a ^ 3 = a * a * a := pow_three' a
    _ = a * a * (a⁻¹ * a⁻¹) := by rw [h5]
    _ = 1 := by group

end Main

end CFSG.CGT.PushingUpLit.CGT6X.End4
