module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34OutPerfect
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma514G

public section

namespace CFSG.ComponentClassification.GrSLit.HeInner

open CFSG Subgroup

variable {X : Type} [Group X] [Finite X]

theorem isSimpleGroup_of_l34 {Q : Type} [Group Q]
    (hQ : IsL34Type Q) : IsSimpleGroup Q := by
  obtain ⟨θQ⟩ := CatFactsSmall.nonempty_equiv_psl34_of_lieModel hQ
  obtain ⟨θ, -⟩ := PSL3Four.exact_model.2.1
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) PSL3Four.F4) :=
    BenderSuzuki.External.huppert_II_6_13 3 (by norm_num) (Or.inl (by norm_num))
      (Or.inl (by norm_num))
  exact (θQ.trans (θ.symm.trans (QuotientGroup.quotientMulEquivOfEq
    (LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 3 PSL3Four.F4)))).isSimpleGroup

theorem le_centralizer_or_mem_centralizer {K K₁ : Subgroup X}
    {v : X} (hKp : ⁅K, K⁆ = K) (hKt : IsL34Type (↥K ⧸ center ↥K)) (hK₁p : ⁅K₁, K₁⁆ = K₁)
    (hK₁t : IsL34Type (↥K₁ ⧸ center ↥K₁)) (hK₁N : K₁ ≤ normalizer (K : Set X))
    (hvN : v ∈ normalizer (K : Set X)) (hv : ∀ k ∈ K₁, v * k = k * v) :
    K₁ ≤ centralizer (K : Set X) ∨ v ∈ centralizer (K : Set X) := by
  classical
  by_cases hc : K₁ ≤ centralizer (K : Set X)
  · exact Or.inl hc
  right
  have hK₁perf : Group.IsPerfect ↥K₁ := isPerfect_iff.mpr hK₁p
  have hKperf : Group.IsPerfect ↥K := isPerfect_iff.mpr hKp
  have hK₁C := L34Out.le_sup_centralizer_of_perfect hKperf hKt hK₁p hK₁N
  let α : ↥K₁ →* MulAut ↥K := K.normalizerMonoidHom.comp (inclusion hK₁N)
  let ι : ↥K →* MulAut ↥K := MulAut.conj
  have hα : ∀ (k : ↥K₁) (y : ↥K), ((α k y : ↥K) : X) = (k : X) * y * (k : X)⁻¹ := fun _ _ => rfl
  have hι : ∀ (a y : ↥K), ((ι a y : ↥K) : X) = (a : X) * y * (a : X)⁻¹ := fun _ _ => rfl
  have hαι : α.range ≤ ι.range := by
    rintro _ ⟨k, rfl⟩
    have hk := hK₁C k.2
    rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left K (centralizer (K : Set X))
      (centralizer_le_normalizer _)] at hk
    obtain ⟨a, ha, c, hcK, hac⟩ := hk
    refine ⟨⟨a, ha⟩, ?_⟩
    ext y
    rw [hα, hι, ← hac]
    have hcy : (y : X) * c = c * y := mem_centralizer_iff.mp hcK y y.2
    calc (a : X) * y * a⁻¹ = a * (y * c) * c⁻¹ * a⁻¹ := by group
      _ = a * (c * y) * c⁻¹ * a⁻¹ := by rw [hcy]
      _ = a * c * y * (a * c)⁻¹ := by group
  have hker : α.ker ≤ center ↥K₁ := by
    rcases Quasisimple.normal_le_center_or_eq_top
        ⟨hK₁perf.commutator_eq_top, isSimpleGroup_of_l34 hK₁t⟩ α.ker with h | h
    · exact h
    · exfalso
      apply hc
      intro k hk
      have h1 : α ⟨k, hk⟩ = 1 := by
        have : (⟨k, hk⟩ : ↥K₁) ∈ α.ker := by rw [h]; exact mem_top _
        exact this
      rw [mem_centralizer_iff]
      intro y hy
      have h2 := congrArg (fun f : MulAut ↥K => ((f ⟨y, hy⟩ : ↥K) : X)) h1
      simp only [hα, MulAut.one_apply] at h2
      calc y * k = k * y * k⁻¹ * k := by rw [h2]
        _ = k * y := by group
  have hcardK₁ : Nat.card (↥K₁ ⧸ center ↥K₁) = 20160 := GSThmB.card_of_lieModel_L34 hK₁t
  have hcardK : Nat.card (↥K ⧸ center ↥K) = 20160 := GSThmB.card_of_lieModel_L34 hKt
  have hιker : ι.ker = center ↥K := by
    ext a
    rw [MonoidHom.mem_ker, mem_center_iff]
    constructor
    · intro h g
      have h2 := congrArg (fun f : MulAut ↥K => f g) h
      simp only [MulAut.one_apply] at h2
      apply Subtype.ext
      have h3 := congrArg Subtype.val h2
      rw [hι] at h3
      calc (g : X) * a = (a : X) * g * (a : X)⁻¹ * a := by rw [h3]
        _ = a * g := by group
    · intro h
      ext y
      rw [hι, MulAut.one_apply, ← coe_mul, ← h y, coe_mul, mul_inv_cancel_right]
  have hcardι : Nat.card ι.range = 20160 := by
    rw [← hcardK, ← hιker]
    exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange ι).toEquiv).symm
  have hcardα : 20160 ≤ Nat.card α.range := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange α).toEquiv]
    have e1 := card_eq_card_quotient_mul_card_subgroup α.ker
    have e2 := card_eq_card_quotient_mul_card_subgroup (center ↥K₁)
    have hle : Nat.card α.ker ≤ Nat.card (center ↥K₁) := card_le_of_le hker
    have hpos : 0 < Nat.card α.ker := Nat.card_pos
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc 20160 * Nat.card α.ker ≤ 20160 * Nat.card (center ↥K₁) := Nat.mul_le_mul_left _ hle
      _ = Nat.card (↥K₁ ⧸ α.ker) * Nat.card α.ker := by rw [← hcardK₁, ← e2, ← e1]
  have hEq : α.range = ι.range := eq_of_le_of_card_ge hαι (by rw [hcardι]; exact hcardα)
  let β : MulAut ↥K := K.normalizerMonoidHom ⟨v, hvN⟩
  have hβ : ∀ y : ↥K, ((β y : ↥K) : X) = v * y * v⁻¹ := fun _ => rfl
  have hβα : ∀ k : ↥K₁, β * α k = α k * β := by
    intro k
    ext y
    simp only [MulAut.mul_apply]
    rw [hβ, hα, hα, hβ]
    have hvk : v * (k : X) = k * v := hv k k.2
    calc v * (k * y * (k : X)⁻¹) * v⁻¹ = (v * k) * y * (v * k)⁻¹ := by group
      _ = (k * v) * y * (k * v)⁻¹ := by rw [hvk]
      _ = k * (v * y * v⁻¹) * (k : X)⁻¹ := by group
  have hβι : ∀ a : ↥K, β * ι a = ι a * β := by
    intro a
    obtain ⟨k, hk⟩ : ι a ∈ α.range := hEq ▸ ⟨a, rfl⟩
    rw [← hk]
    exact hβα k
  have hδ : ∀ a : ↥K, β a * a⁻¹ ∈ center ↥K := by
    intro a
    have hc' : ∀ g : ↥K, (a⁻¹ * β a) * g = g * (a⁻¹ * β a) := by
      intro g
      obtain ⟨y, rfl⟩ := β.surjective g
      have h1 := congrArg (fun f : MulAut ↥K => f y) (hβι a)
      simp only [MulAut.mul_apply] at h1
      have h2 : β (ι a y) = β a * β y * (β a)⁻¹ := by
        rw [show ι a y = a * y * a⁻¹ from rfl, map_mul, map_mul, map_inv]
      rw [h2, show ι a (β y) = a * β y * a⁻¹ from rfl] at h1
      calc a⁻¹ * β a * β y = a⁻¹ * (β a * β y * (β a)⁻¹) * β a := by group
        _ = a⁻¹ * (a * β y * a⁻¹) * β a := by rw [h1]
        _ = β y * (a⁻¹ * β a) := by group
    rw [mem_center_iff]
    intro g
    have h1 := hc' (a⁻¹ * g * a)
    calc g * (β a * a⁻¹) = a * ((a⁻¹ * g * a) * (a⁻¹ * β a)) * a⁻¹ := by group
      _ = a * ((a⁻¹ * β a) * (a⁻¹ * g * a)) * a⁻¹ := by rw [h1]
      _ = β a * a⁻¹ * g := by group
  let δ : ↥K →* ↥(center ↥K) :=
    { toFun := fun a => ⟨β a * a⁻¹, hδ a⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        simp only [map_mul, mul_inv_rev, coe_mul]
        have hb := mem_center_iff.mp (hδ b) a⁻¹
        calc β a * β b * (b⁻¹ * a⁻¹) = β a * (β b * b⁻¹ * a⁻¹) := by group
          _ = β a * (a⁻¹ * (β b * b⁻¹)) := by rw [hb]
          _ = β a * a⁻¹ * (β b * b⁻¹) := by group }
  have hδker : δ.ker = ⊤ := by
    rw [eq_top_iff, ← Group.isPerfect_def.mp hKperf]
    exact Abelianization.commutator_subset_ker δ
  rw [mem_centralizer_iff]
  intro y hy
  have h1 : δ ⟨y, hy⟩ = 1 := by
    have : (⟨y, hy⟩ : ↥K) ∈ δ.ker := by rw [hδker]; exact mem_top _
    exact this
  have h2 : ((β ⟨y, hy⟩ : ↥K) : X) * y⁻¹ = 1 := congrArg (fun z : ↥(center ↥K) => ((z : ↥K) : X)) h1
  rw [hβ] at h2
  calc y * v = v * y * v⁻¹ * y⁻¹ * y * v := by rw [h2, one_mul]
    _ = v * y := by group

end CFSG.ComponentClassification.GrSLit.HeInner
