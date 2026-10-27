module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.Fusion
public import CFSG.LocalAnalysis.EvenBN.LinearThree.PlaneTranslations

public section

namespace CFSG.LocalAnalysis.EvenBN.LinearThree

open Matrix Subgroup CFSG.Open CFSG.LocalAnalysis.ComponentInitial LinearFlag FieldFourCover
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.OddStandard.Seitz77 (Datum)
open scoped commutatorElement MatrixGroups

structure IsRegularNormalQ {G : Type*} [Group G] (E : Subgroup G) (t : G) (X : Subgroup G)
    (q : ℕ) : Prop where
  le_normalizer : X ≤ normalizer (E : Set G)
  centralizer_le : centralizer (E : Set G) ≤ X
  normalizer_le : normalizer (E : Set G) ≤ normalizer (X : Set G)
  mul_self_mem : ∀ p ∈ X, p * p ∈ centralizer (E : Set G)
  commutator_mem : ∀ p ∈ X, ∀ r ∈ X, p * r * p⁻¹ * r⁻¹ ∈ centralizer (E : Set G)
  relIndex_eq : (X ⊓ centralizer (E : Set G)).relIndex X = q ^ 2
  exists_conj : ∀ x ∈ E, IsConj t x → ∃ p ∈ X, p * t * p⁻¹ = x

theorem IsRegularNormalQ.exists_sylow {G : Type*} [Group G] [Finite G] {E X : Subgroup G} {t : G}
    {f : ℕ} (hf : 1 ≤ f) (hX : IsRegularNormalQ E t X (2 ^ f)) (hE : IsPGroup 2 E)
    (hEC : E ≤ centralizer (E : Set G)) :
    ∃ Q : Subgroup G, IsSylowOf 2 Q X ∧ E < Q ∧ Q ⊔ centralizer (E : Set G) = X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer (E : Set G) with hC
  have hCX : C ≤ X := hX.centralizer_le
  have hEX : E ≤ X := hEC.trans hCX
  have hE' : IsPGroup 2 (E.subgroupOf X) := hE.comap_subtype
  obtain ⟨Q₀, hQ₀⟩ := hE'.exists_le_sylow
  set Q : Subgroup G := (Q₀ : Subgroup ↥X).map X.subtype with hQ
  have hQsyl : IsSylowOf 2 Q X := ⟨Q₀, rfl⟩
  have hEQ : E ≤ Q := fun x hx => ⟨⟨x, hEX hx⟩, hQ₀ (mem_subgroupOf.mpr hx), rfl⟩
  have hQX : Q ≤ X := hQsyl.le
  have hCidx : C.relIndex X = 2 ^ (2 * f) := by
    have := hX.relIndex_eq
    rwa [inf_eq_right.mpr hCX, ← pow_mul, mul_comm f 2] at this
  have hS : Q ⊔ C = X := by
    have hSX : Q ⊔ C ≤ X := sup_le hQX hCX
    have h1 : ¬ 2 ∣ Q.relIndex X := (CFSG.ABGLocalTools.isSylowOf_iff.mp hQsyl).2.2
    have h2 : (Q ⊔ C).relIndex X ∣ Q.relIndex X :=
      Dvd.intro_left _ (Subgroup.relIndex_mul_relIndex Q (Q ⊔ C) X le_sup_left hSX)
    have h3 : (Q ⊔ C).relIndex X ∣ 2 ^ (2 * f) := by
      have h := Subgroup.relIndex_mul_relIndex C (Q ⊔ C) X le_sup_right hSX
      rw [hCidx] at h
      exact Dvd.intro_left _ h
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h3
    have hi0 : i = 0 := by
      by_contra hne
      exact h1 ((hi ▸ dvd_pow_self 2 hne).trans h2)
    rw [hi0, pow_zero, Subgroup.relIndex_eq_one] at hi
    exact le_antisymm hSX hi
  refine ⟨Q, hQsyl, lt_of_le_of_ne hEQ fun hEQ' => ?_, hS⟩
  have hQC : Q ≤ C := hEQ' ▸ hEC
  rw [sup_eq_right.mpr hQC] at hS
  rw [hS, Subgroup.relIndex_self] at hCidx
  have : 1 < 2 ^ (2 * f) := Nat.one_lt_two_pow (by omega)
  omega

section Axis

variable {G : Type*} [Group G] {K : Type} [Field K]

theorem radCoord_axis (i : Fin 2) (a : K) :
    radCoord K i (Multiplicative.ofAdd ![a, 0]) = proj 3 K (unipU K 0 0 a) := by
  revert i
  rw [Fin.forall_fin_two]
  exact ⟨by simp [radCoord_zero_apply], by simp [radCoord_one_apply]⟩

theorem proj_unipU_mem_center [Finite K] [CharP K 2] (a : K) :
    proj 3 K (unipU K 0 0 a) ∈
      projUnip K ⊓ centralizer (projUnip K : Set (projectiveSL 3 K)) := by
  rw [← (radicals_projUnip (K := K)).inf_eq]
  exact ⟨mem_projRad_zero.2 ⟨0, a, rfl⟩, mem_projRad_one.2 ⟨0, a, rfl⟩⟩

theorem Frame.exists_leviData_axis [Finite K] [CharP K 2] {A V : Subgroup G} (F : Frame A V K)
    (i : Fin 2) : ∃ D : LeviData A ((projRad K i).map F.φ) K,
      ∀ a : K, D.ι (Multiplicative.ofAdd ![a, 0]) ∈ V ⊓ centralizer (V : Set G) := by
  let D : LeviData A ((projRad K i).map F.φ) K :=
    { ι := F.φ.comp (radCoord K i)
      ι_injective := F.injective.comp (radCoord_injective i)
      range_ι := by rw [MonoidHom.range_comp, range_radCoord]
      ι_mem := fun _ => F.mem_A _
      lev := F.φ.comp (leviProj K i)
      lev_injective := F.injective.comp (leviProj_injective i)
      lev_mem := fun _ => F.mem_A _
      lev_conj := fun B w => by
        simp only [MonoidHom.comp_apply]
        rw [← map_inv, ← map_mul, ← map_mul, leviProj_conj_radCoord]
      tor := F.φ.comp ((proj 3 K).comp (torSL K i))
      tor_mem := fun _ => F.mem_A _
      tor_conj := fun l w => by
        simp only [MonoidHom.comp_apply]
        rw [← map_inv, ← map_mul, ← map_mul, torSL_conj_radCoord]
      tor_comm := fun l B => by
        simp only [MonoidHom.comp_apply]
        rw [← map_mul, ← map_mul, leviProj, MonoidHom.comp_apply, ← map_mul, ← map_mul,
          torSL_mul_levi]
      mem_normalizer_iff := fun x hx => by
        obtain ⟨y, rfl⟩ := F.exists_eq hx
        rw [mem_normalizer_map_iff F.injective, mem_normalizer_projRad_iff]
        constructor
        · rintro ⟨w, l, B, rfl⟩
          exact ⟨w, l, B, by simp only [MonoidHom.comp_apply, map_mul]⟩
        · rintro ⟨w, l, B, h⟩
          refine ⟨w, l, B, F.injective ?_⟩
          simpa only [MonoidHom.comp_apply, map_mul] using h
      transitive := fun v hv w hw hv1 hw1 => by
        obtain ⟨r, hr, rfl⟩ := hv
        obtain ⟨s, hs, rfl⟩ := hw
        have hr1 : r ≠ 1 := fun h => hv1 (by rw [h, map_one])
        have hs1 : s ≠ 1 := fun h => hw1 (by rw [h, map_one])
        have key : ∃ B : CFSG.LieType.Chevalley.SL2 K,
            leviProj K i B * r * (leviProj K i B)⁻¹ = s := by
          fin_cases i
          · exact projRad_zero_transitive hr hs hr1 hs1
          · exact projRad_one_transitive hr hs hr1 hs1
        obtain ⟨B, hB⟩ := key
        refine ⟨B, ?_⟩
        simp only [MonoidHom.comp_apply]
        rw [← map_inv, ← map_mul, ← map_mul, hB] }
  refine ⟨D, fun a => ?_⟩
  have h : F.φ (proj 3 K (unipU K 0 0 a)) ∈
      (projUnip K ⊓ centralizer (projUnip K : Set (projectiveSL 3 K))).map F.φ :=
    ⟨_, proj_unipU_mem_center a, rfl⟩
  rw [map_inf_centralizer F.injective, F.map_projUnip] at h
  show F.φ (radCoord K i (Multiplicative.ofAdd ![a, 0])) ∈ _
  rw [radCoord_axis]
  exact h

theorem exists_leviData_axis [Finite G] [Finite K] [CharP K 2] {A V V₁ V₂ W : Subgroup G}
    (e : A ≃* projectiveSL 3 K) (hV : IsSylowOf 2 V A) (hR : Radicals V V₁ V₂ (Nat.card K))
    (hW : W = V₁ ∨ W = V₂) : ∃ D : LeviData A W K,
      ∀ a : K, D.ι (Multiplicative.ofAdd ![a, 0]) ∈ V ⊓ centralizer (V : Set G) := by
  obtain ⟨F⟩ := exists_frame e hV
  obtain ⟨i, rfl⟩ := F.exists_eq_radical hR hW
  exact F.exists_leviData_axis i

theorem LeviData.exists_axis_eq [Finite G] [Finite K] {A V V₁ V₂ W : Subgroup G}
    (D : LeviData A W K) (hR : Radicals V V₁ V₂ (Nat.card K))
    (hax : ∀ a : K, D.ι (Multiplicative.ofAdd ![a, 0]) ∈ V ⊓ centralizer (V : Set G)) {u : G}
    (hu : u ∈ V ⊓ centralizer (V : Set G)) : ∃ a : K, D.ι (Multiplicative.ofAdd ![a, 0]) = u := by
  let φ : K → ↥(V ⊓ centralizer (V : Set G)) := fun a => ⟨_, hax a⟩
  have hφ : Function.Injective φ := by
    intro a b hab
    have h := D.ι_injective (congrArg Subtype.val hab)
    simpa using congrFun (congrArg Multiplicative.toAdd h) 0
  obtain ⟨a, ha⟩ := (hφ.bijective_of_nat_card_le (by rw [hR.card_center])).2 ⟨u, hu⟩
  exact ⟨a, congrArg Subtype.val ha⟩

end Axis

section Acts

variable {G : Type*} [Group G] {K : Type} [Field K]

@[expose] def ActsBy (ι : Multiplicative (Fin 2 → K) →* G) (g : G) (c : Kˣ) (M : SL(2, K)) :
    Prop :=
  ∀ v : Fin 2 → K, g * ι (Multiplicative.ofAdd v) * g⁻¹ =
    ι (Multiplicative.ofAdd ((c : K) • (M • v)))

variable {ι : Multiplicative (Fin 2 → K) →* G}

theorem ActsBy.one : ActsBy ι 1 1 1 := fun v => by simp

theorem ActsBy.mul {g₁ g₂ : G} {c₁ c₂ : Kˣ} {M₁ M₂ : SL(2, K)} (h₁ : ActsBy ι g₁ c₁ M₁)
    (h₂ : ActsBy ι g₂ c₂ M₂) : ActsBy ι (g₁ * g₂) (c₁ * c₂) (M₁ * M₂) := fun v => by
  have e : g₁ * g₂ * ι (Multiplicative.ofAdd v) * (g₁ * g₂)⁻¹ =
      g₁ * (g₂ * ι (Multiplicative.ofAdd v) * g₂⁻¹) * g₁⁻¹ := by group
  rw [e, h₂, h₁, Plane.sl_smul_smul M₁ (c₂ : K) (M₂ • v), smul_smul (c₁ : K) (c₂ : K),
    mul_smul M₁ M₂ v, Units.val_mul]

theorem ActsBy.inv {g : G} {c : Kˣ} {M : SL(2, K)} (h : ActsBy ι g c M) :
    ActsBy ι g⁻¹ c⁻¹ M⁻¹ := fun v => by
  have h1 := h (((c⁻¹ : Kˣ) : K) • (M⁻¹ • v))
  have e : (c : K) • (M • (((c⁻¹ : Kˣ) : K) • (M⁻¹ • v))) = v := by
    rw [Plane.sl_smul_smul, smul_inv_smul, smul_smul, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, one_smul]
  rw [e] at h1
  rw [← h1]
  group

theorem ActsBy.commutatorElement {g₁ g₂ : G} {c₁ c₂ : Kˣ} {M₁ M₂ : SL(2, K)}
    (h₁ : ActsBy ι g₁ c₁ M₁) (h₂ : ActsBy ι g₂ c₂ M₂) : ActsBy ι ⁅g₁, g₂⁆ 1 ⁅M₁, M₂⁆ := by
  have h := ((h₁.mul h₂).mul h₁.inv).mul h₂.inv
  have hc : c₁ * c₂ * c₁⁻¹ * c₂⁻¹ = 1 := by
    rw [mul_comm c₁ c₂]
    group
  rw [hc] at h
  rwa [commutatorElement_def, commutatorElement_def]

theorem exists_SL_of_mem_commutator {N : Subgroup G}
    (hN : ∀ g ∈ N, ∃ (c : Kˣ) (M : SL(2, K)), ActsBy ι g c M) {g : G} (hg : g ∈ ⁅N, N⁆) :
    ∃ M : SL(2, K), ActsBy ι g 1 M := by
  let S : Subgroup G :=
    { carrier := {g | ∃ M : SL(2, K), ActsBy ι g 1 M}
      mul_mem' := by
        rintro a b ⟨M, hM⟩ ⟨M', hM'⟩
        have := hM.mul hM'
        rw [mul_one] at this
        exact ⟨M * M', this⟩
      one_mem' := ⟨1, ActsBy.one⟩
      inv_mem' := by
        rintro a ⟨M, hM⟩
        have := hM.inv
        rw [inv_one] at this
        exact ⟨M⁻¹, this⟩ }
  have hle : ⁅N, N⁆ ≤ S := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    obtain ⟨c₁, M₁, h₁⟩ := hN g₁ hg₁
    obtain ⟨c₂, M₂, h₂⟩ := hN g₂ hg₂
    exact ⟨_, h₁.commutatorElement h₂⟩
  exact hle hg

theorem LeviData.exists_actsBy {A W : Subgroup G} (D : LeviData A W K) {x : G}
    (hx : x ∈ A ⊓ normalizer (W : Set G)) : ∃ (c : Kˣ) (M : SL(2, K)), ActsBy D.ι x c M := by
  obtain ⟨w, l, B, rfl⟩ := (D.mem_normalizer_iff x hx.1).mp hx.2
  have hw : ActsBy D.ι (D.ι w) 1 1 := fun v => by
    rw [← map_inv, ← map_mul, ← map_mul, mul_comm w, mul_assoc, mul_inv_cancel, mul_one]
    simp
  have hl : ActsBy D.ι (D.tor l) (l ^ 3) 1 := fun v => by
    rw [D.tor_conj l, toAdd_ofAdd, one_smul, Units.val_pow_eq_pow_val]
  have hB : ActsBy D.ι (D.lev B) 1 B := fun v => by
    rw [D.lev_conj B, toAdd_ofAdd, Units.val_one, one_smul]
    rfl
  exact ⟨_, _, (hw.mul hl).mul hB⟩

end Acts

section Scaling

variable {G : Type*} [Group G] {K : Type} [Field K]

def diagSL (μ : Kˣ) : SL(2, K) :=
  ⟨!![(μ : K), 0; 0, ((μ⁻¹ : Kˣ) : K)], by simp [Matrix.det_fin_two]⟩

theorem diagSL_mulVec (μ : Kˣ) (a : K) :
    ((diagSL μ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *ᵥ ![a, 0] = ![(μ : K) * a, 0] := by
  ext i
  fin_cases i <;> simp [diagSL, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem LeviData.axis_mul {A W : Subgroup G} (D : LeviData A W K) (a b : K) :
    D.ι (Multiplicative.ofAdd ![a, 0]) * D.ι (Multiplicative.ofAdd ![b, 0]) =
      D.ι (Multiplicative.ofAdd ![a + b, 0]) := by
  rw [← map_mul, ← ofAdd_add]
  congr 2
  ext i
  fin_cases i <;> simp

theorem LeviData.axis_zero {A W : Subgroup G} (D : LeviData A W K) :
    D.ι (Multiplicative.ofAdd ![(0 : K), 0]) = 1 := by
  rw [← map_one D.ι]
  congr 1
  ext i
  fin_cases i <;> rfl

theorem LeviData.ι_mem_W {A W : Subgroup G} (D : LeviData A W K)
    (w : Multiplicative (Fin 2 → K)) : D.ι w ∈ W := by
  have h : D.ι w ∈ D.ι.range := ⟨w, rfl⟩
  rwa [D.range_ι] at h

theorem LeviData.lev_diag_axis {A W : Subgroup G} (D : LeviData A W K) (μ : Kˣ) (a : K) :
    D.lev (diagSL μ) * D.ι (Multiplicative.ofAdd ![a, 0]) * (D.lev (diagSL μ))⁻¹ =
      D.ι (Multiplicative.ofAdd ![(μ : K) * a, 0]) := by
  rw [D.lev_conj, toAdd_ofAdd, diagSL_mulVec]

theorem exists_unit_ne_one [Finite K] (hK : 3 ≤ Nat.card K) : ∃ μ : Kˣ, μ ≠ 1 := by
  classical
  have := Fintype.ofFinite K
  by_contra hcon
  push Not at hcon
  have hsub : (Set.univ : Set K) ⊆ (({0, 1} : Finset K) : Set K) := by
    intro a _
    by_cases ha : a = 0
    · simp [ha]
    · have := hcon (Units.mk0 a ha)
      have h1 : a = 1 := by simpa using congrArg Units.val this
      simp [h1]
  have hle := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_univ, Set.ncard_coe_finset] at hle
  have h2 : ({0, 1} : Finset K).card ≤ 2 := Finset.card_le_two
  omega

variable [Finite G] [Finite K] [CharP K 2]

theorem exists_scaling {A V V₁ V₂ W : Subgroup G} (e : A ≃* projectiveSL 3 K)
    (hV : IsSylowOf 2 V A) (hR : Radicals V V₁ V₂ (Nat.card K)) (hW : W = V₁ ∨ W = V₂)
    (hK : 4 ≤ Nat.card K) :
    ∃ y ∈ A ⊓ normalizer (W : Set G),
      y ∈ normalizer ((V ⊓ centralizer (V : Set G) : Subgroup G) : Set G) ∧
      ∀ u ∈ V ⊓ centralizer (V : Set G), y * u * y⁻¹ = u → u = 1 := by
  obtain ⟨D, hax⟩ := exists_leviData_axis e hV hR hW
  obtain ⟨μ, hμ⟩ := exists_unit_ne_one (K := K) (by omega)
  refine ⟨D.lev (diagSL μ), ⟨D.lev_mem _, D.lev_mem_normalizer _⟩,
    Subgroup.mem_normalizer_fintype fun u hu => ?_, fun u hu hfix => ?_⟩
  · obtain ⟨a, rfl⟩ := D.exists_axis_eq hR hax hu
    rw [D.lev_diag_axis]
    exact hax _
  · obtain ⟨a, rfl⟩ := D.exists_axis_eq hR hax hu
    rw [D.lev_diag_axis] at hfix
    have h1 := congrFun (congrArg Multiplicative.toAdd (D.ι_injective hfix)) 0
    simp only [toAdd_ofAdd, Matrix.cons_val_zero] at h1
    have ha : a = 0 := by
      by_contra ha
      apply hμ
      ext
      simpa [ha] using mul_right_cancel₀ ha (h1.trans (one_mul a).symm)
    rw [ha, D.axis_zero]

end Scaling

section Points

variable {G : Type*} [Group G] [Finite G] {A : Subgroup G} {W : Subgroup G}

theorem mem_normalizer_adj (d : Datum A) (hWV : W ≤ d.V) {y : G}
    (hyW : y ∈ normalizer (W : Set G)) (hyt : y * d.t * y⁻¹ ∈ W ⊔ zpowers d.t) :
    y ∈ normalizer ((W ⊔ zpowers d.t : Subgroup G) : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  rcases (d.mem_adj_iff hWV).mp hx with hxW | hxW
  · exact mem_sup_left ((mem_normalizer_iff.mp hyW x).mp hxW)
  · have e : y * x * y⁻¹ = (y * (x * d.t) * y⁻¹) * (y * d.t * y⁻¹) := by
      calc y * x * y⁻¹ = y * (x * d.t * d.t) * y⁻¹ := by
            rw [mul_assoc x d.t d.t, d.t_mul_self, mul_one]
        _ = (y * (x * d.t) * y⁻¹) * (y * d.t * y⁻¹) := by group
    rw [e]
    exact mul_mem (mem_sup_left ((mem_normalizer_iff.mp hyW _).mp hxW)) hyt

omit [Finite G] in
theorem mem_centralizer_adj_iff (d : Datum A) (hWV : W ≤ d.V) {x : G} :
    x ∈ centralizer ((W ⊔ zpowers d.t : Subgroup G) : Set G) ↔
      x ∈ centralizer (W : Set G) ∧ x * d.t = d.t * x := by
  constructor
  · intro hx
    exact ⟨mem_centralizer_iff.mpr fun w hw => mem_centralizer_iff.mp hx w (mem_sup_left hw),
      (mem_centralizer_iff.mp hx d.t (mem_sup_right (mem_zpowers _))).symm⟩
  · rintro ⟨hxW, hxt⟩
    refine mem_centralizer_iff.mpr fun y hy => ?_
    rcases (d.mem_adj_iff hWV).mp hy with hyW | hyW
    · exact mem_centralizer_iff.mp hxW y hyW
    · have hc1 : Commute (y * d.t) x := mem_centralizer_iff.mp hxW _ hyW
      have hc2 : Commute d.t x := hxt.symm
      have e : y = y * d.t * d.t := by rw [mul_assoc, d.t_mul_self, mul_one]
      rw [e]
      exact (hc1.mul_left hc2).eq

theorem mem_normalizer_adj_of_mem_A (d : Datum A) (hWV : W ≤ d.V) {a : G}
    (ha : a ∈ A ⊓ normalizer (W : Set G)) :
    a ∈ normalizer ((W ⊔ zpowers d.t : Subgroup G) : Set G) :=
  mem_normalizer_adj d hWV ha.2 (by
    rw [d.comm_t_of_mem ha.1, mul_inv_cancel_right]
    exact mem_sup_right (mem_zpowers _))

end Points

theorem exists_commMap {G : Type*} [Group G] {W T : Subgroup G} {t : G} (ht : t * t = 1)
    (hTW : T ≤ centralizer (W : Set G)) (hTt : ∀ x ∈ T, t * (x * t * x⁻¹) ∈ W) :
    ∃ φ : T →* W, ∀ x : T, ((φ x : W) : G) = t * ((x : G) * t * (x : G)⁻¹) := by
  have hconj : ∀ x : G, x * t * x⁻¹ = t * (t * (x * t * x⁻¹)) := fun x => by
    rw [← mul_assoc, ht, one_mul]
  have hmul : ∀ x y : G, x ∈ T → y ∈ T →
      t * (x * y * t * (x * y)⁻¹) = (t * (x * t * x⁻¹)) * (t * (y * t * y⁻¹)) := by
    intro x y hx hy
    have h1 : x * (t * (y * t * y⁻¹)) * x⁻¹ = t * (y * t * y⁻¹) := by
      rw [mul_inv_eq_iff_eq_mul]
      exact (mem_centralizer_iff.mp (hTW hx) _ (hTt y hy)).symm
    calc t * (x * y * t * (x * y)⁻¹) = t * (x * (y * t * y⁻¹) * x⁻¹) := by group
      _ = t * (x * (t * (t * (y * t * y⁻¹))) * x⁻¹) := by rw [← hconj y]
      _ = t * ((x * t * x⁻¹) * (x * (t * (y * t * y⁻¹)) * x⁻¹)) := by group
      _ = (t * (x * t * x⁻¹)) * (t * (y * t * y⁻¹)) := by rw [h1]; group
  exact ⟨MonoidHom.mk' (fun x : T => (⟨t * ((x : G) * t * (x : G)⁻¹), hTt x x.2⟩ : ↥W))
    (fun x y => Subtype.ext (hmul x y x.2 y.2)), fun x => rfl⟩

theorem sq_ne_one_of_charTwo {K : Type} [Field K] [CharP K 2] {μ : Kˣ} (hμ : μ ≠ 1) :
    (μ : K) ^ 2 ≠ 1 := by
  intro h2
  apply hμ
  have h22 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h3 : ((μ : K) + 1) ^ 2 = 0 := by linear_combination h2 + ((μ : K) + 1) * h22
  have h4 : (μ : K) + 1 = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp h3
  ext
  rw [Units.val_one, ← CharTwo.neg_eq (1 : K), ← sub_eq_zero, sub_neg_eq_add, h4]

namespace Hyp

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {f : ℕ}

theorem normalizer_adj_le (h : Hyp G A f) (d : Datum A) {V₁ V₂ W : Subgroup G}
    (hR : Radicals d.V V₁ V₂ (2 ^ f)) (hW : W = V₁ ∨ W = V₂) :
    normalizer ((W ⊔ zpowers d.t : Subgroup G) : Set G) ≤ normalizer (W : Set G) := by
  intro n hn
  refine Subgroup.mem_normalizer_fintype fun w hw => ?_
  have hnw : n * w * n⁻¹ ∈ W ⊔ zpowers d.t := (mem_normalizer_iff.mp hn w).mp (mem_sup_left hw)
  have hWA : w ∈ A := ((hR.property hW).1 hw).2
  have hnc : ¬ IsConj d.t (n * w * n⁻¹) := fun hc =>
    h.not_isConj_of_mem d hWA (hc.trans (isConj_iff.mpr ⟨n⁻¹, by group⟩))
  exact (h.not_isConj_iff_mem d hR hW hnw).mp hnc

theorem isConj_iff_mem_coset (h : Hyp G A f) (d : Datum A) {V₁ V₂ W : Subgroup G}
    (hR : Radicals d.V V₁ V₂ (2 ^ f)) (hW : W = V₁ ∨ W = V₂) {x : G}
    (hx : x ∈ W ⊔ zpowers d.t) : IsConj d.t x ↔ ∃ w ∈ W, x = d.t * w := by
  obtain ⟨hWV, -, -⟩ := hR.property hW
  constructor
  · intro hxc
    have hxW : x ∉ W := fun hxW => (h.not_isConj_iff_mem d hR hW hx).mpr hxW hxc
    have hxt : x * d.t ∈ W := ((d.mem_adj_iff hWV).mp hx).resolve_left hxW
    refine ⟨x * d.t, hxt, ?_⟩
    rw [← d.V_comm_t (hWV hxt), mul_assoc, d.t_mul_self, mul_one]
  · rintro ⟨w, hw, rfl⟩
    have hxE : d.t * w ∈ W ⊔ zpowers d.t :=
      mul_mem (mem_sup_right (mem_zpowers _)) (mem_sup_left hw)
    by_contra hnc
    have hmem := (h.not_isConj_iff_mem d hR hW hxE).mp hnc
    refine Facts.t_not_mem_A h.facts.toFusionFacts d ?_
    have := mul_mem (hWV hmem) (inv_mem (hWV hw))
    rw [mul_inv_cancel_right] at this
    exact this.2

theorem exists_moving (h : Hyp G A f) (d : Datum A) {V₁ V₂ W : Subgroup G}
    (hR : Radicals d.V V₁ V₂ (2 ^ f)) (hW : W = V₁ ∨ W = V₂) :
    ∃ y ∈ normalizer (W : Set G),
      y ∈ normalizer ((d.V ⊓ centralizer (d.V : Set G) : Subgroup G) : Set G) ∧
      ∃ u ∈ d.V ⊓ centralizer (d.V : Set G), u ≠ 1 ∧ y * d.t * y⁻¹ = d.t * u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u₀, hu₀U, hu₀P, hu₀1, hu₀2, hconj⟩ := h.exists_u₀ d
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  have hg : c⁻¹⁻¹ * d.t * c⁻¹ ∈ d.P ⊓ centralizer (d.P : Set G) := by
    rw [inv_inv, hc]
    exact ⟨mul_mem hu₀U.1.1 d.t_mem_P, mul_mem hu₀P d.t_mem_centralizer_P⟩
  have hVA' : d.V ≤ A.map (MulAut.conj c).toMonoidHom := fun v hv =>
    ⟨c⁻¹ * v * c⁻¹⁻¹, h.conj_V_le_A d hg hv, by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group⟩
  obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ := h.exists_model
  let e' : A.map (MulAut.conj c).toMonoidHom ≃* projectiveSL 3 K :=
    (A.equivMapOfInjective _ (MulAut.conj c).injective).symm.trans e
  have hV' : IsSylowOf 2 d.V (A.map (MulAut.conj c).toMonoidHom) :=
    CFSG.ABGLocalTools.isSylowOf_of_card hVA' (by
      rw [Subgroup.card_map_of_injective (MulAut.conj c).injective]
      exact d.V_isSylow.card_eq)
  have hR' : Radicals d.V V₁ V₂ (Nat.card K) := hK ▸ hR
  have hK4 : 4 ≤ Nat.card K := by have := h.four_lt; omega
  obtain ⟨y, ⟨hyA', hyW⟩, hyU, hfix⟩ := exists_scaling e' hV' hR' hW hK4
  have hyt' : y * (u₀ * d.t) * y⁻¹ = u₀ * d.t := by
    obtain ⟨a, haA, rfl⟩ := hyA'
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hc]
    have hat : a * d.t * a⁻¹ = d.t := by rw [d.comm_t_of_mem haA, mul_inv_cancel_right]
    calc c * a * c⁻¹ * (c * d.t * c⁻¹) * (c * a * c⁻¹)⁻¹ = c * (a * d.t * a⁻¹) * c⁻¹ := by
          group
      _ = c * d.t * c⁻¹ := by rw [hat]
  have hyu₀ : y * u₀ * y⁻¹ ∈ d.V ⊓ centralizer (d.V : Set G) :=
    (mem_normalizer_iff.mp hyU u₀).mp hu₀U
  have huU : (y * u₀ * y⁻¹) * u₀ ∈ d.V ⊓ centralizer (d.V : Set G) := mul_mem hyu₀ hu₀U
  refine ⟨y, hyW, hyU, (y * u₀ * y⁻¹) * u₀, huU, fun h1 => hu₀1 (hfix u₀ hu₀U ?_), ?_⟩
  · rw [eq_inv_of_mul_eq_one_left h1, inv_eq_of_mul_eq_one_right hu₀2]
  · calc y * d.t * y⁻¹ = (y * u₀ * y⁻¹) * (y * (u₀ * d.t) * y⁻¹) := by
          calc y * d.t * y⁻¹ = y * ((u₀ * u₀) * d.t) * y⁻¹ := by rw [hu₀2, one_mul]
            _ = (y * u₀ * y⁻¹) * (y * (u₀ * d.t) * y⁻¹) := by group
      _ = (y * u₀ * y⁻¹) * u₀ * d.t := by rw [hyt']; group
      _ = d.t * ((y * u₀ * y⁻¹) * u₀) := d.V_comm_t huU.1

theorem exists_line_stab (h : Hyp G A f) (d : Datum A) {V₁ V₂ W : Subgroup G}
    (hR : Radicals d.V V₁ V₂ (2 ^ f)) (hW : W = V₁ ∨ W = V₂) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ f) (D : LeviData A W K)
    (hax : ∀ a : K, D.ι (Multiplicative.ofAdd ![a, 0]) ∈ d.V ⊓ centralizer (d.V : Set G))
    (c : K) :
    ∃ x ∈ normalizer ((W ⊔ zpowers d.t : Subgroup G) : Set G),
      (∀ a : K, ∃ b : K, x * (d.t * D.ι (Multiplicative.ofAdd ![a, 0])) * x⁻¹ =
        d.t * D.ι (Multiplicative.ofAdd ![b, 0])) ∧
      x * d.t * x⁻¹ = d.t * D.ι (Multiplicative.ofAdd ![c, 0]) := by
  obtain ⟨hWV, -, -⟩ := hR.property hW
  have hR' : Radicals d.V V₁ V₂ (Nat.card K) := hK ▸ hR
  by_cases hc0 : c = 0
  · refine ⟨1, one_mem _, fun a => ⟨a, by group⟩, ?_⟩
    rw [hc0, D.axis_zero]
    group
  obtain ⟨y, hyW, hyU, u, hu, hu1, hyt⟩ := h.exists_moving d hR hW
  obtain ⟨c₀, rfl⟩ := D.exists_axis_eq hR' hax hu
  have hc₀ : c₀ ≠ 0 := fun h0 => hu1 (by rw [h0, D.axis_zero])
  have hyE : y ∈ normalizer ((W ⊔ zpowers d.t : Subgroup G) : Set G) :=
    mem_normalizer_adj d hWV hyW (by
      rw [hyt]
      exact mul_mem (mem_sup_right (mem_zpowers _)) (mem_sup_left (D.ι_mem_W _)))
  let μ : Kˣ := Units.mk0 (c / c₀) (div_ne_zero hc0 hc₀)
  have hμc : (μ : K) * c₀ = c := by
    rw [Units.val_mk0, div_mul_cancel₀ c hc₀]
  have hsA : D.lev (diagSL μ) ∈ A ⊓ normalizer (W : Set G) :=
    ⟨D.lev_mem _, D.lev_mem_normalizer _⟩
  have hst : D.lev (diagSL μ) * d.t * (D.lev (diagSL μ))⁻¹ = d.t := by
    rw [d.comm_t_of_mem hsA.1, mul_inv_cancel_right]
  have hs : ∀ b : K, D.lev (diagSL μ) * (d.t * D.ι (Multiplicative.ofAdd ![b, 0])) *
      (D.lev (diagSL μ))⁻¹ = d.t * D.ι (Multiplicative.ofAdd ![(μ : K) * b, 0]) := by
    intro b
    calc D.lev (diagSL μ) * (d.t * D.ι (Multiplicative.ofAdd ![b, 0])) * (D.lev (diagSL μ))⁻¹
        = (D.lev (diagSL μ) * d.t * (D.lev (diagSL μ))⁻¹) *
          (D.lev (diagSL μ) * D.ι (Multiplicative.ofAdd ![b, 0]) * (D.lev (diagSL μ))⁻¹) := by
          group
      _ = d.t * D.ι (Multiplicative.ofAdd ![(μ : K) * b, 0]) := by rw [hst, D.lev_diag_axis]
  refine ⟨D.lev (diagSL μ) * y, mul_mem (mem_normalizer_adj_of_mem_A d hWV hsA) hyE,
    fun a => ?_, ?_⟩
  · obtain ⟨a', ha'⟩ := D.exists_axis_eq hR' hax ((mem_normalizer_iff.mp hyU _).mp (hax a))
    refine ⟨(μ : K) * (c₀ + a'), ?_⟩
    calc D.lev (diagSL μ) * y * (d.t * D.ι (Multiplicative.ofAdd ![a, 0])) *
          (D.lev (diagSL μ) * y)⁻¹
        = D.lev (diagSL μ) * ((y * d.t * y⁻¹) * (y * D.ι (Multiplicative.ofAdd ![a, 0]) * y⁻¹)) *
          (D.lev (diagSL μ))⁻¹ := by group
      _ = D.lev (diagSL μ) * (d.t * D.ι (Multiplicative.ofAdd ![c₀ + a', 0])) *
          (D.lev (diagSL μ))⁻¹ := by
        rw [hyt, ← ha', mul_assoc d.t, D.axis_mul]
      _ = d.t * D.ι (Multiplicative.ofAdd ![(μ : K) * (c₀ + a'), 0]) := hs _
  · calc D.lev (diagSL μ) * y * d.t * (D.lev (diagSL μ) * y)⁻¹
        = D.lev (diagSL μ) * (y * d.t * y⁻¹) * (D.lev (diagSL μ))⁻¹ := by group
      _ = d.t * D.ι (Multiplicative.ofAdd ![c, 0]) := by rw [hyt, hs, hμc]

theorem exists_regularNormal (h : Hyp G A f) (d : Datum A) {V₁ V₂ W : Subgroup G}
    (hR : Radicals d.V V₁ V₂ (2 ^ f)) (hW : W = V₁ ∨ W = V₂) :
    ∃ X : Subgroup G, IsRegularNormalQ (W ⊔ zpowers d.t) d.t X (2 ^ f) ∧
      X = normalizer ((W ⊔ zpowers d.t : Subgroup G) : Set G) ⊓ centralizer (W : Set G) ∧
      (∃ Q : Subgroup G, IsSylowOf 2 Q X ∧ W ⊔ zpowers d.t < Q ∧
        Q ⊔ centralizer ((W ⊔ zpowers d.t : Subgroup G) : Set G) = X) ∧
      ∃ φ : X →* W, (∀ x : X, ((φ x : W) : G) = d.t * ((x : G) * d.t * (x : G)⁻¹)) ∧
        (∀ x : X, φ x = 1 ↔ (x : G) ∈ centralizer ((W ⊔ zpowers d.t : Subgroup G) : Set G)) ∧
        Function.Surjective φ ∧
        ∀ a ∈ A ⊓ normalizer (W : Set G), ∀ x : X, ∀ hx : a * x * a⁻¹ ∈ X,
          ((φ ⟨a * x * a⁻¹, hx⟩ : W) : G) = a * (φ x : G) * a⁻¹ := by
  obtain ⟨hWV, hWe, hWc⟩ := hR.property hW
  have ht2 := d.t_mul_self
  have hWt : W ≤ centralizer ({d.t} : Set G) := fun w hw =>
    mem_centralizer_singleton_iff.mpr (d.V_comm_t (hWV hw))
  have hNW := h.normalizer_adj_le d hR hW
  obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ := h.exists_model
  have := Fintype.ofFinite K
  have hR' : Radicals d.V V₁ V₂ (Nat.card K) := hK ▸ hR
  obtain ⟨D, hax⟩ := exists_leviData_axis e d.V_isSylow hR' hW
  let ι : Multiplicative (Fin 2 → K) ≃* W :=
    (MonoidHom.ofInjective D.ι_injective).trans (MulEquiv.subgroupCongr D.range_ι)
  have hι : ∀ x, (ι x : G) = D.ι x := fun x => by
    simp only [ι, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply, MonoidHom.ofInjective_apply]
  have hK₀M : ⁅A ⊓ normalizer (W : Set G), A ⊓ normalizer (W : Set G)⁆ ≤
      A ⊓ normalizer (W : Set G) := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg₁ hg₂) (inv_mem hg₁)) (inv_mem hg₂)
  have hKX : ⁅A ⊓ normalizer (W : Set G), A ⊓ normalizer (W : Set G)⁆ ≤
      normalizer ((W ⊔ zpowers d.t : Subgroup G) : Set G) ⊓ centralizer ({d.t} : Set G) :=
    le_inf (fun a ha => mem_normalizer_adj_of_mem_A d hWV (hK₀M ha))
      (fun a ha => mem_centralizer_singleton_iff.mpr (d.comm_t_of_mem (hK₀M ha).1))
  have hKn : ∀ x ∈ normalizer ((W ⊔ zpowers d.t : Subgroup G) : Set G) ⊓
      centralizer ({d.t} : Set G),
      ∀ g ∈ ⁅A ⊓ normalizer (W : Set G), A ⊓ normalizer (W : Set G)⁆,
      x * g * x⁻¹ ∈ ⁅A ⊓ normalizer (W : Set G), A ⊓ normalizer (W : Set G)⁆ := by
    intro x hx g hg
    have hxA : x ∈ normalizer (A : Set G) := (OddStandard.centralizer_t_facts d.sector).1 hx.2
    have hxW : x ∈ normalizer (W : Set G) := hNW hx.1
    refine OddStandard.Seitz77.conj_mem_commutator (fun y hy => Subgroup.mem_inf.mpr ⟨?_, ?_⟩) hg
    · exact (mem_normalizer_iff.mp hxA y).mp hy.1
    · exact mul_mem (mul_mem hxW hy.2) (inv_mem hxW)
  have hnat : ∀ g ∈ ⁅A ⊓ normalizer (W : Set G), A ⊓ normalizer (W : Set G)⁆,
      ∃ B : SL(2, K), ∀ v : Fin 2 → K, g * (ι (Multiplicative.ofAdd v) : G) * g⁻¹ =
        ι (Multiplicative.ofAdd ((B : Matrix (Fin 2) (Fin 2) K) *ᵥ v)) := by
    intro g hg
    obtain ⟨B, hB⟩ := exists_SL_of_mem_commutator (fun x hx => D.exists_actsBy hx) hg
    refine ⟨B, fun v => ?_⟩
    rw [hι, hι, hB v, Units.val_one, one_smul]
    rfl
  have hperf : commutator SL(2, K) = ⊤ := by
    obtain ⟨μ, hμ⟩ := exists_unit_ne_one (K := K) (by have := h.four_lt; omega)
    exact Matrix.SL2.commutator_eq_top μ.ne_zero (sq_ne_one_of_charTwo hμ)
  have hsurj : ∀ B : SL(2, K), ∃ g ∈ ⁅A ⊓ normalizer (W : Set G), A ⊓ normalizer (W : Set G)⁆,
      ∀ v : Fin 2 → K, g * (ι (Multiplicative.ofAdd v) : G) * g⁻¹ =
        ι (Multiplicative.ofAdd ((B : Matrix (Fin 2) (Fin 2) K) *ᵥ v)) := by
    intro B
    refine ⟨D.lev B, ?_, fun v => ?_⟩
    · have hB : B ∈ ⁅(⊤ : Subgroup SL(2, K)), (⊤ : Subgroup SL(2, K))⁆ := by
        rw [← _root_.commutator_def, hperf]
        trivial
      have h1 := Subgroup.mem_map_of_mem D.lev hB
      rw [Subgroup.map_commutator] at h1
      have h2 : (⊤ : Subgroup SL(2, K)).map D.lev ≤ A ⊓ normalizer (W : Set G) := by
        rintro _ ⟨B', -, rfl⟩
        exact ⟨D.lev_mem B', D.lev_mem_normalizer B'⟩
      exact Subgroup.commutator_mono h2 h2 h1
    · rw [hι, hι, D.lev_conj, toAdd_ofAdd]
  have hline : ∀ c : K, ∃ x ∈ normalizer ((W ⊔ zpowers d.t : Subgroup G) : Set G),
      (∀ a : K, ∃ b : K, x * (d.t * ι (Multiplicative.ofAdd ![a, 0])) * x⁻¹ =
        d.t * ι (Multiplicative.ofAdd ![b, 0])) ∧
      x * d.t * x⁻¹ = d.t * ι (Multiplicative.ofAdd ![c, 0]) := fun c => by
    simpa only [hι] using h.exists_line_stab d hR hW hK D hax c
  obtain ⟨T, hTX, hTn, hTW, hCT, htr⟩ := exists_regularNormal_of_natural ι ht2 hWt hNW le_rfl
    hKX hKn hnat hsurj hline
  have hTt : ∀ x ∈ T, d.t * (x * d.t * x⁻¹) ∈ W := fun x hx => by
    have := Plane.conj_mem_coset ht2 hWt (hNW (hTX hx)) (hTX hx)
    rwa [inv_eq_of_mul_eq_one_right ht2] at this
  obtain ⟨φ, hφ⟩ := exists_commMap ht2 hTW hTt
  have hker : ∀ x : T,
      φ x = 1 ↔ (x : G) ∈ centralizer ((W ⊔ zpowers d.t : Subgroup G) : Set G) := by
    intro x
    rw [Subtype.ext_iff, hφ, OneMemClass.coe_one, mem_centralizer_adj_iff d hWV]
    constructor
    · intro h1
      refine ⟨hTW x.2, mul_inv_eq_iff_eq_mul.mp ?_⟩
      calc (x : G) * d.t * (x : G)⁻¹ = d.t * (d.t * ((x : G) * d.t * (x : G)⁻¹)) := by
            rw [← mul_assoc, ht2, one_mul]
        _ = d.t := by rw [h1, mul_one]
    · rintro ⟨-, hxt⟩
      rw [mul_inv_eq_iff_eq_mul.mpr hxt, ht2]
  have hsurjφ : Function.Surjective φ := by
    intro w
    obtain ⟨x, hx, hxt⟩ := htr w w.2
    refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
    rw [hφ]
    show d.t * (x * d.t * x⁻¹) = w
    rw [hxt, ← mul_assoc, ht2, one_mul]
  have hW2 : ∀ w : W, w * w = 1 := fun w => Subtype.ext (by
    rw [Subgroup.coe_mul, OneMemClass.coe_one, ← sq]
    exact hWe.2 w w.2)
  have hreg : IsRegularNormalQ (W ⊔ zpowers d.t) d.t T (2 ^ f) := by
    refine ⟨hTX, fun c hc => hCT ⟨Subgroup.centralizer_le_normalizer _ hc, hc⟩,
      (Subgroup.normal_subgroupOf_iff_le_normalizer hTX).mp hTn, fun p hp => ?_,
      fun p hp r hr => ?_, ?_, ?_⟩
    · refine (hker ⟨p * p, mul_mem hp hp⟩).mp ?_
      have e : (⟨p * p, mul_mem hp hp⟩ : T) = ⟨p, hp⟩ * ⟨p, hp⟩ := rfl
      rw [e, map_mul, hW2]
    · refine (hker ⟨p * r * p⁻¹ * r⁻¹, mul_mem (mul_mem (mul_mem hp hr) (inv_mem hp))
        (inv_mem hr)⟩).mp ?_
      have e : (⟨p * r * p⁻¹ * r⁻¹, mul_mem (mul_mem (mul_mem hp hr) (inv_mem hp))
          (inv_mem hr)⟩ : T) = ⟨p, hp⟩ * ⟨r, hr⟩ * ⟨p, hp⟩⁻¹ * ⟨r, hr⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
      apply Subtype.ext
      have hc := comm_of_isElemAbelian hWe (φ ⟨p, hp⟩).2 (φ ⟨r, hr⟩).2
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one]
      rw [hc]
      group
    · have hk : φ.ker = (centralizer ((W ⊔ zpowers d.t : Subgroup G) : Set G)).subgroupOf T := by
        ext x
        rw [MonoidHom.mem_ker, mem_subgroupOf, hker]
      rw [inf_relIndex_left]
      show ((centralizer ((W ⊔ zpowers d.t : Subgroup G) : Set G)).subgroupOf T).index = _
      rw [← hk, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurjφ, Subgroup.card_top, hWc]
    · intro x hxE hxc
      obtain ⟨w, hw, rfl⟩ := (h.isConj_iff_mem_coset d hR hW hxE).mp hxc
      exact htr w hw
  have hTeq : T = normalizer ((W ⊔ zpowers d.t : Subgroup G) : Set G) ⊓
      centralizer (W : Set G) := by
    refine le_antisymm (le_inf hTX hTW) fun y hy => ?_
    have hyE : y * d.t * y⁻¹ ∈ W ⊔ zpowers d.t :=
      (mem_normalizer_iff.mp hy.1 d.t).mp (mem_sup_right (mem_zpowers _))
    obtain ⟨w, hw, hyw⟩ := (h.isConj_iff_mem_coset d hR hW hyE).mp (isConj_iff.mpr ⟨y, rfl⟩)
    obtain ⟨x, hx, hxt⟩ := htr w hw
    have hyx : y * d.t * y⁻¹ = x * d.t * x⁻¹ := by rw [hyw, hxt]
    have hxy : x⁻¹ * y ∈ normalizer ((W ⊔ zpowers d.t : Subgroup G) : Set G) ⊓
        centralizer ((W ⊔ zpowers d.t : Subgroup G) : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem (hTX hx)) hy.1,
        (mem_centralizer_adj_iff d hWV).mpr ⟨mul_mem (inv_mem (hTW hx)) hy.2, ?_⟩⟩
      calc x⁻¹ * y * d.t = x⁻¹ * (y * d.t * y⁻¹) * y := by group
        _ = x⁻¹ * (x * d.t * x⁻¹) * y := by rw [hyx]
        _ = d.t * (x⁻¹ * y) := by group
    have := mul_mem hx (hCT hxy)
    rwa [mul_inv_cancel_left] at this
  obtain ⟨hEP, hEe, -⟩ := (SylowSetting.of_datum d).adj_properties h.facts.toFusionFacts hR hW
  have hsyl := hreg.exists_sylow (by have := h.three_le; omega) (d.hP.isPGroup.to_le hEP)
    (fun x hx => mem_centralizer_iff.mpr fun y hy => comm_of_isElemAbelian hEe hy hx)
  refine ⟨T, hreg, hTeq, hsyl, φ, hφ, hker, hsurjφ, fun a ha x hx => ?_⟩
  have hc : a * d.t * a⁻¹ = d.t := by rw [d.comm_t_of_mem ha.1, mul_inv_cancel_right]
  rw [hφ, hφ]
  calc d.t * ((a * x * a⁻¹) * d.t * (a * x * a⁻¹)⁻¹)
      = (a * d.t * a⁻¹) * (a * x * a⁻¹) * (a * d.t * a⁻¹) * (a * x * a⁻¹)⁻¹ := by
        rw [hc]
        group
    _ = a * (d.t * ((x : G) * d.t * (x : G)⁻¹)) * a⁻¹ := by group

theorem isSylowOf_centralizer (h : Hyp G A f) (d : Datum A) {V₁ V₂ W : Subgroup G}
    (hR : Radicals d.V V₁ V₂ (2 ^ f)) (hW : W = V₁ ∨ W = V₂) :
    IsSylowOf 2 (W ⊔ zpowers d.t : Subgroup G)
      (centralizer ((W ⊔ zpowers d.t : Subgroup G) : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hWV, -, -⟩ := hR.property hW
  obtain ⟨hEP, hEe, -⟩ := (SylowSetting.of_datum d).adj_properties h.facts.toFusionFacts hR hW
  have hE2 : IsPGroup 2 (W ⊔ zpowers d.t : Subgroup G) := d.hP.isPGroup.to_le hEP
  have hEC : (W ⊔ zpowers d.t : Subgroup G) ≤
      centralizer ((W ⊔ zpowers d.t : Subgroup G) : Set G) := fun x hx =>
    mem_centralizer_iff.mpr fun y hy => comm_of_isElemAbelian hEe hy hx
  set C := centralizer ((W ⊔ zpowers d.t : Subgroup G) : Set G) with hC
  have hE' : IsPGroup 2 ((W ⊔ zpowers d.t : Subgroup G).subgroupOf C) := hE2.comap_subtype
  obtain ⟨D₀, hD₀⟩ := hE'.exists_le_sylow
  set D : Subgroup G := (D₀ : Subgroup ↥C).map C.subtype with hD
  have hDsyl : IsSylowOf 2 D C := ⟨D₀, rfl⟩
  have hED : (W ⊔ zpowers d.t : Subgroup G) ≤ D := fun x hx =>
    ⟨⟨x, hEC hx⟩, hD₀ (mem_subgroupOf.mpr hx), rfl⟩
  have htE : d.t ∈ (W ⊔ zpowers d.t : Subgroup G) := mem_sup_right (mem_zpowers _)
  have hsg := (h.seitz21 d).1
  have hDE : D ≤ (W ⊔ zpowers d.t : Subgroup G) := by
    intro x hx
    have hxC : x ∈ C := hDsyl.le hx
    have hxt : x * d.t = d.t * x := (mem_centralizer_iff.mp hxC d.t htE).symm
    have hxN : x ∈ normalizer (A : Set G) :=
      (OddStandard.centralizer_t_facts d.sector).1 (mem_centralizer_singleton_iff.mpr hxt)
    have hxW : x ∈ centralizer (W : Set G) :=
      mem_centralizer_iff.mpr fun w hw => mem_centralizer_iff.mp hxC w (mem_sup_left hw)
    obtain ⟨w, hw, k, hk, rfl⟩ := OddStandard.Seitz77.mem_sup_of_commute
      (fun a ha k hk => mem_centralizer_iff.mp hk a (hWV ha).2)
      (h.facts.cent_radical d.V V₁ V₂ d.V_isSylow hR W hW ⟨hxN, hxW⟩)
    have hkD : k ∈ D := by
      have := D.mul_mem (D.inv_mem (hED (mem_sup_left hw))) hx
      simpa using this
    have hDK : D ⊓ centralizer (A : Set G) = OddStandard.sg A d.R :=
      OddStandard.sg_maximal inf_le_right hDsyl.isPGroup.to_inf_left (by
        rw [hsg]
        exact (zpowers_le).mpr ⟨hED htE, d.t_mem_K⟩)
    have hkR : k ∈ OddStandard.sg A d.R := hDK ▸ ⟨hkD, hk⟩
    rw [hsg] at hkR
    exact mul_mem (mem_sup_left hw) ((zpowers_le.mpr htE) hkR)
  rw [show D = (W ⊔ zpowers d.t : Subgroup G) from le_antisymm hDE hED] at hDsyl
  exact hDsyl

end Hyp

end CFSG.LocalAnalysis.EvenBN.LinearThree
