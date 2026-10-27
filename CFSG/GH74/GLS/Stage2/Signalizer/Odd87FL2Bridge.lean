module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL2Char
public import CFSG.GH74.GLS.IVK.L2.Lemma12

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter
open scoped MatrixGroups commutatorElement

section OutAbelian

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem commutator_mem_innAut (hF : L2Field F) (e : K ≃* L2 F) (a b : MulAut K) :
    ⁅a, b⁆ ∈ innAut K := by
  classical
  have hNorm : (innAut K).Normal := innAut_normal
  have hDiagN : (innDiagSub e).Normal := innDiagSub_normal e
  let π : MulAut K →* MulAut K ⧸ innAut K := QuotientGroup.mk' (innAut K)
  have hπ : ∀ x : MulAut K, π x = 1 ↔ x ∈ innAut K := fun x => QuotientGroup.eq_one_iff x
  have hdec : ∀ x : MulAut K, ∃ u ∈ innDiagSub e, ∃ f ∈ fieldAutSub e, x = u * f := by
    intro x
    have hx : x ∈ innDiagSub e ⊔ fieldAutSub e := by
      rw [innDiagSub_sup_fieldAutSub e]; trivial
    rw [← SetLike.mem_coe, Subgroup.normal_mul] at hx
    obtain ⟨u, hu, f, hf, rfl⟩ := hx
    exact ⟨u, hu, f, hf, rfl⟩
  have hidx : ((innAut K).subgroupOf (innDiagSub e)).index = 2 := innAut_relIndex_two e hF
  have h1 : ∀ x y : ↥(innDiagSub e), x * y ∈ (innAut K).subgroupOf (innDiagSub e) ↔
      (x ∈ (innAut K).subgroupOf (innDiagSub e) ↔ y ∈ (innAut K).subgroupOf (innDiagSub e)) :=
    fun x y => Subgroup.mul_mem_iff_of_index_two hidx
  have hUU : ∀ u ∈ innDiagSub e, ∀ v ∈ innDiagSub e, Commute (π u) (π v) := by
    intro u hu v hv
    have hmem := commutator_mem_of_index_le_two ((innAut K).subgroupOf (innDiagSub e)) hidx.le
      ⟨u, hu⟩ ⟨v, hv⟩
    have hmem' : u * v * u⁻¹ * v⁻¹ ∈ innAut K := hmem
    have h2 : π (u * v * u⁻¹ * v⁻¹) = 1 := (hπ _).mpr hmem'
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h2
    exact (commutatorElement_eq_one_iff_commute.mp (by simpa [commutatorElement_def] using h2))
  have hFF : ∀ f ∈ fieldAutSub e, ∀ g ∈ fieldAutSub e, Commute (π f) (π g) := by
    intro f hf g hg
    have := isCyclic_fieldAutSub e
    have hc : (⟨f, hf⟩ : ↥(fieldAutSub e)) * ⟨g, hg⟩ = ⟨g, hg⟩ * ⟨f, hf⟩ :=
      IsMulCommutative.is_comm.comm _ _
    have hc' : f * g = g * f := congrArg Subtype.val hc
    show π f * π g = π g * π f
    rw [← map_mul, ← map_mul, hc']
  have hUF : ∀ u ∈ innDiagSub e, ∀ f ∈ fieldAutSub e, Commute (π u) (π f) := by
    intro u hu f hf
    have hz : f * u * f⁻¹ ∈ innDiagSub e := hDiagN.conj_mem u hu f
    let zΔ : ↥(innDiagSub e) := ⟨f * u * f⁻¹, hz⟩
    let uΔ : ↥(innDiagSub e) := ⟨u, hu⟩
    have hmem : zΔ * uΔ⁻¹ ∈ (innAut K).subgroupOf (innDiagSub e) := by
      rw [h1, inv_mem_iff]
      show f * u * f⁻¹ ∈ innAut K ↔ u ∈ innAut K
      constructor
      · intro h
        have := hNorm.conj_mem _ h f⁻¹
        simpa [mul_assoc] using this
      · intro h
        exact hNorm.conj_mem u h f
    have hmem' : f * u * f⁻¹ * u⁻¹ ∈ innAut K := hmem
    have h2 : π (f * u * f⁻¹ * u⁻¹) = 1 := (hπ _).mpr hmem'
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h2
    have h3 : Commute (π f) (π u) :=
      commutatorElement_eq_one_iff_commute.mp (by simpa [commutatorElement_def] using h2)
    exact h3.symm
  obtain ⟨u₁, hu₁, f₁, hf₁, rfl⟩ := hdec a
  obtain ⟨u₂, hu₂, f₂, hf₂, rfl⟩ := hdec b
  rw [← hπ]
  have hcomm : Commute (π (u₁ * f₁)) (π (u₂ * f₂)) := by
    rw [map_mul, map_mul]
    exact ((hUU u₁ hu₁ u₂ hu₂).mul_right (hUF u₁ hu₁ f₂ hf₂)).mul_left
      (((hUF u₂ hu₂ f₁ hf₁).symm).mul_right (hFF f₁ hf₁ f₂ hf₂))
  have := commutatorElement_eq_one_iff_commute.mpr hcomm
  rw [map_commutatorElement]
  exact this

end OutAbelian

section Quot

variable {A : Type} [Group A]

@[expose] noncomputable def actOnQuot (K : Subgroup A) [K.Normal] : A →* MulAut (↥K ⧸ center ↥K) where
  toFun a := QuotientGroup.congr (center ↥K) (center ↥K) (MulAut.conjNormal a : MulAut ↥K)
    (Subgroup.map_center_eq _)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H k => simp
  map_mul' a b := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H k => simp

theorem actOnQuot_mk (K : Subgroup A) [K.Normal] (a : A) (k : ↥K) :
    actOnQuot K a (QuotientGroup.mk k) =
      QuotientGroup.mk ⟨a * k * a⁻¹, Subgroup.Normal.conj_mem inferInstance _ k.2 a⟩ := by
  rfl

omit [Group A] in
theorem commutator_mul_central {G : Type} [Group G] (x y z₁ z₂ : G) (h₁ : ∀ g : G, g * z₁ = z₁ * g)
    (h₂ : ∀ g : G, g * z₂ = z₂ * g) : ⁅x * z₁, y * z₂⁆ = ⁅x, y⁆ := by
  have e1 : z₁ * z₂ * z₁⁻¹ = z₂ := by
    calc z₁ * z₂ * z₁⁻¹ = (z₂ * z₁) * z₁⁻¹ := by rw [← h₂ z₁]
      _ = z₂ := by group
  simp only [commutatorElement_def]
  calc x * z₁ * (y * z₂) * (x * z₁)⁻¹ * (y * z₂)⁻¹
      = x * (z₁ * y) * z₂ * z₁⁻¹ * x⁻¹ * z₂⁻¹ * y⁻¹ := by group
    _ = x * (y * z₁) * z₂ * z₁⁻¹ * x⁻¹ * z₂⁻¹ * y⁻¹ := by rw [← h₁ y]
    _ = x * y * (z₁ * z₂ * z₁⁻¹) * x⁻¹ * z₂⁻¹ * y⁻¹ := by group
    _ = x * y * z₂ * x⁻¹ * z₂⁻¹ * y⁻¹ := by rw [e1]
    _ = x * y * (z₂ * x⁻¹) * z₂⁻¹ * y⁻¹ := by group
    _ = x * y * (x⁻¹ * z₂) * z₂⁻¹ * y⁻¹ := by rw [← h₂ x⁻¹]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem centralizes_of_actOnQuot_eq_one (K : Subgroup A) [K.Normal] (hperf : commutator ↥K = ⊤)
    {d : A} (hd : actOnQuot K d = 1) : d ∈ centralizer (K : Set A) := by
  let φ : MulAut ↥K := MulAut.conjNormal d
  have hφ : ∀ k : ↥K, ((φ k : ↥K) : A) = d * k * d⁻¹ := fun k => rfl
  have hz : ∀ k : ↥K, ∃ z ∈ center ↥K, φ k = k * z := by
    intro k
    have h1 := actOnQuot_mk K d k
    rw [hd, MulAut.one_apply] at h1
    have h2 := (QuotientGroup.eq (a := k)
      (b := ⟨d * k * d⁻¹, Subgroup.Normal.conj_mem inferInstance _ k.2 d⟩)).mp h1
    exact ⟨k⁻¹ * φ k, h2, by simp⟩
  have hfix : ∀ x y : ↥K, φ ⁅x, y⁆ = ⁅x, y⁆ := by
    intro x y
    obtain ⟨z₁, hz₁, h₁⟩ := hz x
    obtain ⟨z₂, hz₂, h₂⟩ := hz y
    rw [map_commutatorElement, h₁, h₂]
    exact commutator_mul_central x y z₁ z₂ (Subgroup.mem_center_iff.mp hz₁)
      (Subgroup.mem_center_iff.mp hz₂)
  have hall : ∀ k : ↥K, φ k = k := by
    have hle : commutator ↥K ≤ MonoidHom.eqLocus (φ : ↥K →* ↥K) (MonoidHom.id ↥K) := by
      rw [commutator_def, Subgroup.commutator_le]
      intro x _ y _
      exact hfix x y
    intro k
    have hk : k ∈ commutator ↥K := by rw [hperf]; exact Subgroup.mem_top k
    exact hle hk
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have := congrArg Subtype.val (hall ⟨k, hk⟩)
  rw [hφ] at this
  simp only at this
  calc k * d = (d * k * d⁻¹) * d := by rw [this]
    _ = d * k := by group

theorem comm_mem_of_out_abelian (K : Subgroup A) [K.Normal] (hperf : commutator ↥K = ⊤)
    (hout : ∀ a b : MulAut (↥K ⧸ center ↥K), ⁅a, b⁆ ∈ IVK.innAut (↥K ⧸ center ↥K)) (a b : A) :
    ⁅a, b⁆ ∈ K ⊔ centralizer (K : Set A) := by
  have h1 : actOnQuot K ⁅a, b⁆ ∈ IVK.innAut (↥K ⧸ center ↥K) := by
    rw [map_commutatorElement]; exact hout _ _
  obtain ⟨kb, hkb⟩ := h1
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective kb
  have hk : actOnQuot K (k : A) = MulAut.conj (QuotientGroup.mk k) := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H k' =>
      rw [actOnQuot_mk, MulAut.conj_apply]
      rfl
  have hd : actOnQuot K (⁅a, b⁆ * (k : A)⁻¹) = 1 := by
    rw [map_mul, map_inv, hk, hkb, mul_inv_cancel]
  have hc := centralizes_of_actOnQuot_eq_one K hperf hd
  have : ⁅a, b⁆ = (⁅a, b⁆ * (k : A)⁻¹) * k := by group
  rw [this, sup_comm]
  exact Subgroup.mul_mem_sup hc k.2

end Quot

section CardFixed

variable {A : Type} [Group A] [Finite A]

theorem card_eq_range_mul_ker {G H : Type} [Group G] [Group H] [Finite G] (f : G →* H) :
    Nat.card G = Nat.card f.range * Nat.card f.ker := by
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker] at h1
  rw [← h1, mul_comm]

theorem card_fixed_le (K : Subgroup A) [K.Normal] (z : A)
    (hzZ : ∀ c ∈ center ↥K, z * (c : A) * z⁻¹ = c) :
    Nat.card ↥(fixedSubgroup (↥K ⧸ center ↥K) (actOnQuot K z)) ≤
      Nat.card ↥(center ↥K) *
        Nat.card ↥(((K ⊓ centralizer ({z} : Set A)).subgroupOf K).map
          (QuotientGroup.mk' (center ↥K))) := by
  classical
  set Z : Subgroup ↥K := center ↥K with hZ
  let π : ↥K →* ↥K ⧸ Z := QuotientGroup.mk' Z
  let Fx : Subgroup (↥K ⧸ Z) := fixedSubgroup (↥K ⧸ Z) (actOnQuot K z)
  let Ft : Subgroup ↥K := Fx.comap π
  let D : Subgroup ↥K := (K ⊓ centralizer ({z} : Set A)).subgroupOf K
  let γ : MulAut ↥K := MulAut.conjNormal z
  have hγ : ∀ k : ↥K, ((γ k : ↥K) : A) = z * k * z⁻¹ := fun k => rfl
  have hFt : ∀ k : ↥K, k ∈ Ft ↔ k⁻¹ * γ k ∈ Z := by
    intro k
    show π k ∈ Fx ↔ _
    show actOnQuot K z (π k) = π k ↔ _
    have h1 : actOnQuot K z (π k) = π (γ k) := by
      rw [show π k = QuotientGroup.mk k from rfl, actOnQuot_mk]
      rfl
    rw [h1]
    show QuotientGroup.mk (γ k) = QuotientGroup.mk k ↔ _
    rw [QuotientGroup.eq, ← inv_mem_iff (x := (γ k)⁻¹ * k)]
    simp
  have hD : ∀ k : ↥K, k ∈ D ↔ γ k = k := by
    intro k
    show (k : A) ∈ K ⊓ centralizer ({z} : Set A) ↔ _
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨-, h⟩
      apply Subtype.ext
      rw [hγ]
      calc z * (k : A) * z⁻¹ = (z * k) * z⁻¹ := rfl
        _ = (k * z) * z⁻¹ := by rw [← h]
        _ = k := by group
    · intro h
      refine ⟨k.2, ?_⟩
      have := congrArg Subtype.val h
      rw [hγ] at this
      calc (k : A) * z = (z * k * z⁻¹) * z := by rw [this]
        _ = z * k := by group
  have hDF : D ≤ Ft := by
    intro k hk
    rw [hFt, (hD k).mp hk]
    simp
  have hZD : Z ≤ D := by
    intro c hc
    rw [hD]
    apply Subtype.ext
    rw [hγ]
    exact hzZ c hc
  have hZF : Z ≤ Ft := hZD.trans hDF
  have hcent : ∀ k : ↥Ft, ((k : ↥K)⁻¹ * γ k) ∈ Z := fun k => (hFt k).mp k.2
  let ζ : ↥Ft →* ↥Z :=
    { toFun := fun k => ⟨(k : ↥K)⁻¹ * γ k, hcent k⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun k k' => by
        apply Subtype.ext
        have hc := Subgroup.mem_center_iff.mp (hcent k)
        show ((k * k' : ↥Ft) : ↥K)⁻¹ * γ ((k * k' : ↥Ft) : ↥K) =
          ((k : ↥K)⁻¹ * γ k) * ((k' : ↥K)⁻¹ * γ k')
        calc ((k * k' : ↥Ft) : ↥K)⁻¹ * γ ((k * k' : ↥Ft) : ↥K)
            = (k' : ↥K)⁻¹ * ((k : ↥K)⁻¹ * γ k) * γ k' := by
              show ((k : ↥K) * k')⁻¹ * γ ((k : ↥K) * k') = _
              rw [map_mul]; group
          _ = ((k : ↥K)⁻¹ * γ k) * (k' : ↥K)⁻¹ * γ k' := by rw [← hc ((k' : ↥K)⁻¹)]
          _ = _ := by group }
  have hζker : ζ.ker = D.subgroupOf Ft := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hD]
    constructor
    · intro h
      have h1 : (k : ↥K)⁻¹ * γ k = 1 := congrArg Subtype.val h
      have := mul_left_cancel (a := (k : ↥K)⁻¹) (b := γ k) (c := (k : ↥K)) (by rw [h1, inv_mul_cancel])
      exact this
    · intro h
      apply Subtype.ext
      show (k : ↥K)⁻¹ * γ k = 1
      rw [h, inv_mul_cancel]
  have hcard1 : Nat.card Ft ≤ Nat.card Z * Nat.card D := by
    rw [card_eq_range_mul_ker ζ, hζker]
    have h1 : Nat.card ζ.range ≤ Nat.card Z := by
      refine Nat.card_le_card_of_injective (fun x => (x : ↥Z)) ?_
      intro a b hab
      exact Subtype.ext hab
    have h2 : Nat.card (D.subgroupOf Ft) = Nat.card D :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDF).toEquiv
    rw [h2]
    exact Nat.mul_le_mul_right _ h1
  let ρ : ↥Ft →* ↥K ⧸ Z := π.comp Ft.subtype
  have hρrange : ρ.range = Fx := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact k.2
    · intro hx
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
      exact ⟨⟨k, hx⟩, rfl⟩
  have hρker : ρ.ker = Z.subgroupOf Ft := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show π k = 1 ↔ _
    exact QuotientGroup.eq_one_iff _
  have hcard2 : Nat.card Ft = Nat.card Fx * Nat.card Z := by
    rw [card_eq_range_mul_ker ρ, hρrange, hρker]
    congr 1
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZF).toEquiv
  let σ : ↥D →* ↥K ⧸ Z := π.comp D.subtype
  have hσrange : σ.range = D.map π := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, k.2, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
  have hσker : σ.ker = Z.subgroupOf D := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show π k = 1 ↔ _
    exact QuotientGroup.eq_one_iff _
  have hcard3 : Nat.card D = Nat.card (D.map π) * Nat.card Z := by
    rw [card_eq_range_mul_ker σ, hσrange, hσker]
    congr 1
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZD).toEquiv
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  have : Nat.card Fx * Nat.card Z ≤ (Nat.card Z * Nat.card (D.map π)) * Nat.card Z := by
    calc Nat.card Fx * Nat.card Z = Nat.card Ft := hcard2.symm
      _ ≤ Nat.card Z * Nat.card D := hcard1
      _ = (Nat.card Z * Nat.card (D.map π)) * Nat.card Z := by rw [hcard3]; ring
  exact Nat.le_of_mul_le_mul_right this hZpos

end CardFixed

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
