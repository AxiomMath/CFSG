module

public import CFSG.LocalAnalysis.EvenBN.U4.TorusPrelim

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.EvenBN.Common (prodFactorOne prodFactorTwo mem_normalizer_inf
  card_sup_mul_card_inf_eq upperSL lowerSL diagSL mkSL exists_eq_mkSL mem_upperSL_iff
  mem_lowerSL_iff unipotent_mem_upperSL lowerUnipotent_mem_lowerSL lowerUnipotent
  coe_lowerUnipotent coe_mkSL coe_diagSL mkSL_inv coe_mkSL_conj_unipotent units_inv_ne_self
  diagSL_inv transvection_eq_unipotent_or_lowerUnipotent eq_upperSL_or_eq_lowerSL
  exists_mulEquiv_eq_diagSL mem_normalizer_of_conj_mem map_mem_normalizer_map)
open CFSG.SL2MinimalFaithful (unipotent coe_unipotent)
open scoped MatrixGroups

section SL2

variable {k : Type*} [Field k]

theorem mem_upperSL_sup_lowerSL (A : SL(2, k)) : A ∈ upperSL k ⊔ lowerSL k := by
  induction A using Matrix.SL2.transvection_induction with
  | htransvec i j h c =>
    rcases transvection_eq_unipotent_or_lowerUnipotent h c with e | e <;> rw [e]
    exacts [mem_sup_left (unipotent_mem_upperSL c), mem_sup_right (lowerUnipotent_mem_lowerSL c)]
  | hmul A B hA hB => exact mul_mem hA hB

variable [CharP k 2]

theorem not_mem_normalizer_upperSL_of_conj_diagSL {x : SL(2, k)} {μ : kˣ} (hμ : μ ≠ 1)
    (hx : x * diagSL μ * x⁻¹ = diagSL μ⁻¹) : x ∉ normalizer (upperSL k : Set SL(2, k)) := by
  intro hN
  obtain ⟨p, q, r, s, hdet, rfl⟩ := exists_eq_mkSL x
  obtain ⟨c, hc⟩ := mem_upperSL_iff.1
    ((mem_normalizer_iff.1 hN (unipotent 1)).1 (unipotent_mem_upperSL 1))
  have h10 := congrArg (fun m : SL(2, k) => (m : Matrix (Fin 2) (Fin 2) k) 1 0) hc
  simp only [coe_unipotent, coe_mkSL_conj_unipotent] at h10
  simp at h10
  subst h10
  have h00 := congrArg (fun m : SL(2, k) => (m : Matrix (Fin 2) (Fin 2) k) 0 0) hx
  simp only [mkSL_inv] at h00
  simp [coe_mkSL, coe_diagSL, Matrix.mul_apply, Fin.sum_univ_two] at h00
  have hps : p * s = 1 := by simpa using hdet
  apply units_inv_ne_self hμ
  rw [← h00]
  linear_combination (μ : k) * hps

theorem not_mem_normalizer_lowerSL_of_conj_diagSL {x : SL(2, k)} {μ : kˣ} (hμ : μ ≠ 1)
    (hx : x * diagSL μ * x⁻¹ = diagSL μ⁻¹) : x ∉ normalizer (lowerSL k : Set SL(2, k)) := by
  intro hN
  obtain ⟨p, q, r, s, hdet, rfl⟩ := exists_eq_mkSL x
  obtain ⟨c, hc⟩ := mem_lowerSL_iff.1
    ((mem_normalizer_iff.1 hN (lowerUnipotent 1)).1 (lowerUnipotent_mem_lowerSL 1))
  have h01 := congrArg (fun m : SL(2, k) => (m : Matrix (Fin 2) (Fin 2) k) 0 1) hc
  simp only [mkSL_inv] at h01
  simp [coe_mkSL, coe_lowerUnipotent, Matrix.mul_apply, Fin.sum_univ_two] at h01
  have hq : q = 0 := by
    have : q ^ 2 = 0 := by linear_combination h01
    exact pow_eq_zero_iff (n := 2) two_ne_zero |>.1 this
  subst hq
  have h00 := congrArg (fun m : SL(2, k) => (m : Matrix (Fin 2) (Fin 2) k) 0 0) hx
  simp only [mkSL_inv] at h00
  simp [coe_mkSL, coe_diagSL, Matrix.mul_apply, Fin.sum_univ_two] at h00
  have hps : p * s = 1 := by simpa using hdet
  apply units_inv_ne_self hμ
  rw [← h00]
  linear_combination (μ : k) * hps

theorem sup_map_conj_eq_top_of_conj_diagSL [Finite k] {S : Subgroup SL(2, k)}
    (hS : Nat.card S = Nat.card k) {μ : kˣ} (hμ : μ ≠ 1)
    (hSμ : diagSL μ ∈ normalizer (S : Set SL(2, k))) {x : SL(2, k)}
    (hx : x * diagSL μ * x⁻¹ = diagSL μ⁻¹) : S ⊔ S.map (MulAut.conj x).toMonoidHom = ⊤ := by
  have hinv : diagSL μ⁻¹ ∈ normalizer (S : Set SL(2, k)) := by
    rw [← diagSL_inv]; exact inv_mem hSμ
  have h1 : MulAut.conj x (diagSL μ⁻¹) = diagSL μ := by
    rw [MulAut.conj_apply, ← diagSL_inv]
    calc x * (diagSL μ)⁻¹ * x⁻¹ = (x * diagSL μ * x⁻¹)⁻¹ := by group
      _ = diagSL μ := by rw [hx, diagSL_inv, inv_inv]
  have hμS' : diagSL μ ∈ normalizer ((S.map (MulAut.conj x).toMonoidHom : Subgroup _) :
      Set SL(2, k)) := by
    rw [← h1]; exact map_mem_normalizer_map (MulAut.conj x) hinv
  have hS'card : Nat.card (S.map (MulAut.conj x).toMonoidHom) = Nat.card k := by
    rw [card_map_of_injective (MulAut.conj x).injective, hS]
  have hN : ∀ W : Subgroup SL(2, k), S = W → S.map (MulAut.conj x).toMonoidHom = W →
      x ∈ normalizer (W : Set SL(2, k)) := by
    rintro W rfl he
    refine mem_normalizer_of_conj_mem (fun y hy => ?_) (fun y hy => ?_)
    · rw [← he]; exact ⟨y, hy, rfl⟩
    · rw [← he] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      rwa [show x⁻¹ * (x * z * x⁻¹) * x = z by group]
  have hU := mem_upperSL_sup_lowerSL (k := k)
  rcases eq_upperSL_or_eq_lowerSL hS hμ hSμ with h | h <;>
    rcases eq_upperSL_or_eq_lowerSL hS'card hμ hμS' with h' | h'
  · exact absurd (hN _ h h') (not_mem_normalizer_upperSL_of_conj_diagSL hμ hx)
  · rw [h', h]; exact eq_top_iff.2 fun A _ => hU A
  · rw [h', h, sup_comm]; exact eq_top_iff.2 fun A _ => hU A
  · exact absurd (hN _ h h') (not_mem_normalizer_lowerSL_of_conj_diagSL hμ hx)

omit [CharP k 2] in
theorem le_sup_map_conj_of_conj_eq_inv {G : Type*} [Group G] [Finite k] [CharP k 2]
    {X S : Subgroup G} (e : X ≃* SL(2, k)) (hSX : S ≤ X) (hS : Nat.card S = Nat.card k)
    {d r : G} (hdX : d ∈ X) (hrX : r ∈ X) (hd1 : d ≠ 1) (hd : d ^ (Nat.card k - 1) = 1)
    (hdS : d ∈ normalizer (S : Set G)) (hrd : r * d * r⁻¹ = d⁻¹) :
    X ≤ S ⊔ S.map (MulAut.conj r).toMonoidHom := by
  set d' : X := ⟨d, hdX⟩ with hd'
  set r' : X := ⟨r, hrX⟩ with hr'
  have hd1' : d' ≠ 1 := fun h => hd1 (congrArg Subtype.val h)
  have hd' : d' ^ (Nat.card k - 1) = 1 := Subtype.ext (by simpa [hd'] using hd)
  obtain ⟨ψ, μ, hμ, hψd⟩ := exists_mulEquiv_eq_diagSL e hd1' hd'
  set S₀ : Subgroup SL(2, k) := (S.subgroupOf X).map ψ.toMonoidHom with hS₀
  have hS₀card : Nat.card S₀ = Nat.card k := by
    rw [hS₀, card_map_of_injective ψ.injective, ← hS]
    exact Nat.card_congr (subgroupOfEquivOfLe hSX).toEquiv
  have hμS₀ : diagSL μ ∈ normalizer (S₀ : Set SL(2, k)) := by
    have hN : d' ∈ normalizer ((S.subgroupOf X : Subgroup X) : Set X) := by
      rw [mem_normalizer_iff]
      intro y
      rw [mem_subgroupOf, mem_subgroupOf]
      exact mem_normalizer_iff.1 hdS y
    rw [← hψd, hS₀, ← map_equiv_normalizer_eq]
    exact ⟨d', hN, rfl⟩
  have hx : ψ r' * diagSL μ * (ψ r')⁻¹ = diagSL μ⁻¹ := by
    rw [← hψd, ← diagSL_inv, ← hψd, ← map_inv, ← map_mul, ← map_mul, ← map_inv]
    congr 1
    exact Subtype.ext (by simpa [hd', hr'] using hrd)
  have htop := sup_map_conj_eq_top_of_conj_diagSL hS₀card hμ hμS₀ hx
  set φ : SL(2, k) →* G := X.subtype.comp ψ.symm.toMonoidHom with hφ
  set H := (S ⊔ S.map (MulAut.conj r).toMonoidHom).comap φ with hH
  have h1 : S₀ ≤ H := by
    rintro _ ⟨s, hs, rfl⟩
    simp only [hH, mem_comap, hφ, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, coe_subtype]
    exact mem_sup_left hs
  have h2 : S₀.map (MulAut.conj (ψ r')).toMonoidHom ≤ H := by
    rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    simp only [hH, mem_comap, hφ, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← map_inv, ← map_mul,
      MulEquiv.symm_apply_apply, coe_subtype, coe_mul, coe_inv]
    exact mem_sup_right ⟨s, hs, rfl⟩
  intro y hy
  have : ψ ⟨y, hy⟩ ∈ H := sup_le h1 h2 (htop ▸ mem_top _)
  simpa [hH, hφ] using this

end SL2

section Conj

variable {G : Type*} [Group G]

theorem mem_normalizer_map_conj {H : Subgroup G} {r x : G}
    (hx : r⁻¹ * x * r ∈ normalizer (H : Set G)) :
    x ∈ normalizer ((H.map (MulAut.conj r).toMonoidHom : Subgroup G) : Set G) := by
  rw [← map_equiv_normalizer_eq]
  exact ⟨_, hx, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩

theorem mem_map_conj_iff {H : Subgroup G} {r y : G} :
    y ∈ H.map (MulAut.conj r).toMonoidHom ↔ r⁻¹ * y * r ∈ H := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show r⁻¹ * (r * z * r⁻¹) * r = z by group]
    exact hz
  · intro hy
    exact ⟨_, hy, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩

end Conj

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

local notation "𝓦" => miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G)

theorem R1G_mem_L (_hS : Setting h L η t Q T) : miyamotoR1G h L η ∈ L :=
  (η.symm _).2

theorem R1G_inv (hS : Setting h L η t Q T) : (miyamotoR1G h L η)⁻¹ = miyamotoR1G h L η :=
  inv_eq_of_mul_eq_one_right hS.R1G_mul_self

theorem E_inf_E_r1 (hS : Setting h L η t Q T) :
    miyamotoEG h L η Q ⊓ (miyamotoEG h L η Q).map (MulAut.conj (miyamotoR1G h L η)).toMonoidHom =
      ⊥ := by
  have h1 := hS.E_r1_inf_F
  rw [hS.R1G_inv] at h1
  exact eq_bot_iff.2 fun x hx => h1 ▸ mem_inf.2 ⟨(mem_inf.1 hx).2, hS.E_le_F (mem_inf.1 hx).1⟩

theorem eq_bot_of_le_E_of_conj (hS : Setting h L η t Q T) {V : Subgroup G}
    (hVE : V ≤ miyamotoEG h L η Q)
    (hV : ∀ v ∈ V, miyamotoR1G h L η * v * (miyamotoR1G h L η)⁻¹ ∈ V) : V = ⊥ := by
  refine eq_bot_iff.2 fun v hv => ?_
  rw [← hS.E_inf_E_r1]
  refine mem_inf.2 ⟨hVE hv, mem_map_conj_iff.2 (hVE ?_)⟩
  have := hV v hv
  rw [hS.R1G_inv] at this ⊢
  exact this


theorem le_normalizer_of_le_F1 (hS : Setting h L η t Q T) {A B : Subgroup G}
    (hA : A ≤ miyamotoF1G h L η t) (hB : B ≤ miyamotoF1G h L η t) :
    B ≤ normalizer (A : Set G) := by
  intro x hx
  have hxF := hB hx
  rw [mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    rw [hS.F1_comm hxF (hA hz), mul_inv_cancel_right]
    exact hz
  · intro hz
    have hzF : z ∈ miyamotoF1G h L η t := by
      have := mul_mem (mul_mem (inv_mem hxF) (hA hz)) hxF
      rwa [show x⁻¹ * (x * z * x⁻¹) * x = z by group] at this
    rwa [hS.F1_comm hxF hzF, mul_inv_cancel_right] at hz


variable {k : Type} [Field k] {ψ : miyamotoM1G h L η t ≃* SL(2, k) × SL(2, k)}

local notation "𝓤" => miyamotoF1G h L η t ⊔ (𝓦 ⊓ prodFactorOne ψ)

local notation "𝓨" => CFSG.centerIn 𝓤 ⊓
  Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (miyamotoR1G h L η))) (CFSG.centerIn 𝓤)

@[expose] noncomputable def compOne (ψ : miyamotoM1G h L η t ≃* SL(2, k) × SL(2, k)) :
    miyamotoM1G h L η t →* G :=
  (miyamotoM1G h L η t).subtype.comp (ψ.symm.toMonoidHom.comp
    ((MonoidHom.inl _ _).comp ((MonoidHom.fst _ _).comp ψ.toMonoidHom)))

omit [Finite G] in
theorem compOne_apply (m : miyamotoM1G h L η t) :
    compOne ψ m = ((ψ.symm ((ψ m).1, 1) : miyamotoM1G h L η t) : G) :=
  rfl

omit [Finite G] in
theorem compOne_mem (m : miyamotoM1G h L η t) : compOne ψ m ∈ prodFactorOne ψ :=
  Common.symm_inl_mem_prodFactorOne ψ _

omit [Finite G] in
theorem conj_eq_conj_compOne (m : miyamotoM1G h L η t) {x : G} (hx : x ∈ prodFactorOne ψ) :
    (m : G) * x * (m : G)⁻¹ = compOne ψ m * x * (compOne ψ m)⁻¹ := by
  set c₂ : G := ((ψ.symm (1, (ψ m).2) : miyamotoM1G h L η t) : G) with hc₂
  have hm : (m : G) = compOne ψ m * c₂ := by
    rw [compOne_apply, hc₂, ← coe_mul, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul,
      Prod.mk.eta, MulEquiv.symm_apply_apply]
  have hc : c₂ * x = x * c₂ := (mem_centralizer_iff.1
    (Common.prodFactorTwo_le_centralizer ψ (Common.symm_inr_mem_prodFactorTwo ψ _)) x hx).symm
  rw [hm]
  calc compOne ψ m * c₂ * x * (compOne ψ m * c₂)⁻¹
      = compOne ψ m * (c₂ * x) * c₂⁻¹ * (compOne ψ m)⁻¹ := by group
    _ = compOne ψ m * x * (compOne ψ m)⁻¹ := by rw [hc]; group

theorem conj_R1G_mem_Y (hS : Setting h L η t Q T) {y : G} (hy : y ∈ 𝓨) :
    miyamotoR1G h L η * y * (miyamotoR1G h L η)⁻¹ ∈ 𝓨 := by
  obtain ⟨hy₁, hy₂⟩ := mem_inf.1 hy
  refine mem_inf.2 ⟨?_, ⟨y, hy₁, rfl⟩⟩
  have := mem_map_conj_iff.1 hy₂
  rw [hS.R1G_inv] at this ⊢
  exact this


theorem X2_le_normalizer_Y (hS : Setting h L η t Q T) :
    prodFactorTwo ψ ≤ normalizer ((𝓨 : Subgroup G) : Set G) := by
  have hZ : prodFactorTwo ψ ≤ normalizer ((CFSG.centerIn 𝓤 : Subgroup G) : Set G) :=
    fun x hx => normalizer_le_normalizer_centerIn _ (hS.X2_le_normalizer_U hx)
  intro x hx
  refine mem_normalizer_inf (hZ hx) (mem_normalizer_map_conj (hZ ?_))
  have := (mem_normalizer_iff.1 (inv_mem (Common.le_normalizer_prodFactorTwo ψ hS.R1G_mem_M1))
    x).1 hx
  rwa [inv_inv] at this

theorem Y_inf_centralizer_X2 [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) :
    𝓨 ⊓ centralizer (prodFactorTwo ψ : Set G) = ⊥ := by
  set r := miyamotoR1G h L η with hr
  have hrX : r⁻¹ ∈ normalizer (prodFactorTwo ψ : Set G) :=
    inv_mem (Common.le_normalizer_prodFactorTwo ψ hS.R1G_mem_M1)
  have hE : ∀ y ∈ 𝓨, y ∈ centralizer (prodFactorTwo ψ : Set G) → y ∈ miyamotoEG h L η Q :=
    fun y hy hyC => hS.centerIn_U_inf_centralizer_W2_le_E hk (mem_inf.1 hy).1
      (centralizer_le (SetLike.coe_subset_coe.2 inf_le_right) hyC)
  refine hS.eq_bot_of_le_E_of_conj (fun y hy => hE y (mem_inf.1 hy).1 (mem_inf.1 hy).2)
    fun y hy => mem_inf.2 ⟨hS.conj_R1G_mem_Y (mem_inf.1 hy).1, ?_⟩
  rw [mem_centralizer_iff]
  intro x hx
  have hx' : r⁻¹ * x * r⁻¹⁻¹ ∈ prodFactorTwo ψ := (mem_normalizer_iff.1 hrX x).1 hx
  rw [inv_inv] at hx'
  have hc := mem_centralizer_iff.1 (mem_inf.1 hy).2 _ hx'
  calc x * (r * y * r⁻¹) = r * ((r⁻¹ * x * r) * y) * r⁻¹ := by group
    _ = r * (y * (r⁻¹ * x * r)) * r⁻¹ := by rw [hc]
    _ = r * y * r⁻¹ * x := by group


theorem Y_ne_bot (hS : Setting h L η t Q T)
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤)) : 𝓨 ≠ ⊥ := by
  set Z := CFSG.centerIn 𝓤 with hZdef
  set r := miyamotoR1G h L η with hrdef
  set Zr := Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj r)) Z with hZr
  have hZF1 : Z ≤ miyamotoF1G h L η t := hS.centerIn_U_le_F1
  have hrF1 : r ∈ normalizer (miyamotoF1G h L η t : Set G) :=
    hS.M1_le_normalizer_F1 hS.R1G_mem_M1
  have hZrF1 : Zr ≤ miyamotoF1G h L η t := by
    rintro _ ⟨z, hz, rfl⟩
    exact (mem_normalizer_iff.1 hrF1 z).1 (hZF1 hz)
  have hcardZr : Nat.card Zr = Nat.card Z := card_map_of_injective (MulAut.conj r).injective
  have h1 := card_sup_mul_card_inf_eq (hS.le_normalizer_of_le_F1 hZF1 hZrF1)
  intro hY
  rw [hY, card_bot, mul_one, hcardZr] at h1
  have hcardle := Subgroup.card_le_of_le (sup_le hZF1 hZrF1)
  rw [h1, hS.card_F1] at hcardle
  have : (2 ^ f) ^ 4 * (2 ^ f) ^ 4 < Nat.card Z * Nat.card Z :=
    Nat.mul_lt_mul_of_lt_of_le hZ hZ.le Nat.card_pos
  have h8 : (2 ^ f) ^ 8 = (2 ^ f) ^ 4 * (2 ^ f) ^ 4 := by ring
  omega

theorem card_Y_ge [Fintype k] (hS : Setting h L η t Q T) (hk : Fintype.card k = (2 ^ f) ^ 2)
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤)) : (2 ^ f) ^ 4 ≤ Nat.card (𝓨 : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP k 2 := charP_of_card_eq_prime_pow (f := 2 * f) (by rw [hk, ← pow_mul, mul_comm])
  have hY2 : IsPGroup 2 (𝓨 : Subgroup G) :=
    hS.isPGroup_RG.to_le (inf_le_left.trans (inf_le_left.trans (hS.U_le_RG (ψ := ψ))))
  obtain ⟨d, hd⟩ := hY2.exists_card_eq
  by_contra hlt
  push Not at hlt
  have hd' : d < 2 * (2 * f) := by
    rw [hd, show (2 ^ f) ^ 4 = 2 ^ (2 * (2 * f)) by rw [← pow_mul]; ring_nf] at hlt
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 hlt
  have hk' : Nat.card k = 2 ^ (2 * f) := by
    rw [Nat.card_eq_fintype_card, hk, ← pow_mul, mul_comm]
  have hX2C : prodFactorTwo ψ ≤ centralizer (𝓨 : Set G) :=
    Common.le_centralizer_of_card_lt (Common.prodFactorTwoEquiv ψ) hk'
      (by have := hS.two_le; omega) (by omega) hS.X2_le_normalizer_Y hd hd'
  apply hS.Y_ne_bot hZ
  rw [← hS.Y_inf_centralizer_X2 hk]
  exact (inf_eq_left.2 (le_centralizer_iff.1 hX2C)).symm

theorem Y_inf_Y_t [Fintype k] (hS : Setting h L η t Q T) (hk : Fintype.card k = (2 ^ f) ^ 2)
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁)) :
    𝓨 ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) 𝓨 = ⊥ := by
  set r := miyamotoR1G h L η with hrdef
  have hrt : r * t = t * r := hS.comm_t_of_mem_L hS.R1G_mem_L
  refine hS.eq_bot_of_le_E_of_conj (fun v hv => ?_) (fun v hv => ?_)
  · rw [← hS.centerIn_U_inf_t hk hψt]
    obtain ⟨hv₁, hv₂⟩ := mem_inf.1 hv
    exact mem_inf.2 ⟨(mem_inf.1 hv₁).1, map_mono inf_le_left hv₂⟩
  · obtain ⟨hv₁, y, hy, rfl⟩ := mem_inf.1 hv
    refine mem_inf.2 ⟨hS.conj_R1G_mem_Y hv₁, ⟨r * y * r⁻¹, hS.conj_R1G_mem_Y hy, ?_⟩⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc t * (r * y * r⁻¹) * t⁻¹ = (t * r) * y * (t * r)⁻¹ := by group
      _ = (r * t) * y * (r * t)⁻¹ := by rw [← hrt]
      _ = r * (t * y * t⁻¹) * r⁻¹ := by group

theorem sec5_1_one [Fintype k] (hS : Setting h L η t Q T) (hk : Fintype.card k = (2 ^ f) ^ 2)
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤)) :
    Nat.card (𝓨 : Subgroup G) = (2 ^ f) ^ 4 ∧
      miyamotoF1G h L η t = 𝓨 ⊔ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) 𝓨 ∧
      𝓨 ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) 𝓨 = ⊥ := by
  set Y := 𝓨 with hYdef
  set Yt := Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) Y with hYt
  have hYF1 : Y ≤ miyamotoF1G h L η t := inf_le_left.trans hS.centerIn_U_le_F1
  have hYtF1 : Yt ≤ miyamotoF1G h L η t := by
    rintro _ ⟨y, hy, rfl⟩
    exact (mem_normalizer_iff.1 hS.t_mem_normalizer_F1 y).1 (hYF1 hy)
  have hcardYt : Nat.card Yt = Nat.card Y := card_map_of_injective (MulAut.conj t).injective
  have hinf := hS.Y_inf_Y_t hk hψt
  have h1 := card_sup_mul_card_inf_eq (hS.le_normalizer_of_le_F1 hYF1 hYtF1)
  rw [hinf, card_bot, mul_one, hcardYt] at h1
  have hcardle := Subgroup.card_le_of_le (sup_le hYF1 hYtF1)
  rw [h1, hS.card_F1] at hcardle
  have hge := hS.card_Y_ge hk hZ
  have h8 : (2 ^ f) ^ 8 = (2 ^ f) ^ 4 * (2 ^ f) ^ 4 := by ring
  have hY4 : Nat.card Y = (2 ^ f) ^ 4 := by
    refine le_antisymm ?_ hge
    by_contra hlt
    push Not at hlt
    have : (2 ^ f) ^ 4 * (2 ^ f) ^ 4 < Nat.card Y * Nat.card Y :=
      Nat.mul_lt_mul_of_lt_of_le hlt hlt.le Nat.card_pos
    omega
  refine ⟨hY4, (Subgroup.eq_of_le_of_card_ge (sup_le hYF1 hYtF1) ?_).symm, hinf⟩
  rw [h1, hY4, hS.card_F1, h8]

theorem X1_le_W1_sup [Fintype k] (hS : Setting h L η t Q T) (hk : Fintype.card k = (2 ^ f) ^ 2)
    {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a)) :
    prodFactorOne ψ ≤ (𝓦 ⊓ prodFactorOne ψ) ⊔
      Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (miyamotoR1G h L η)))
        (𝓦 ⊓ prodFactorOne ψ) := by
  have : CharP k 2 := charP_of_card_eq_prime_pow (f := 2 * f) (by rw [hk, ← pow_mul, mul_comm])
  set r := miyamotoR1G h L η with hrdef
  set S := 𝓦 ⊓ prodFactorOne ψ with hSdef
  have hN1M : miyamotoN1G h L η ≤ miyamotoM1G h L η t := hS.sec3_12_one.2.2.1
  have hD1 : 1 < Nat.card (miyamotoDG h L η) := by
    rw [card_miyamotoDG]
    have := hS.four_le
    have : 16 ≤ (2 ^ f) ^ 2 := by nlinarith
    omega
  obtain ⟨⟨d, hd⟩, hd1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1
    ((Subgroup.one_lt_card_iff_ne_bot _).1 hD1)
  have hd1' : d ≠ 1 := fun e => hd1 (Subtype.ext e)
  have hdN : d ∈ miyamotoN1G h L η := hS.DG_le_N1G hd
  set dM : miyamotoM1G h L η t := ⟨d, hN1M hdN⟩ with hdM
  set rM : miyamotoM1G h L η t := ⟨r, hS.R1G_mem_M1⟩ with hrM
  have hrd : rM * dM * rM⁻¹ = dM⁻¹ := by
    obtain ⟨a, ha⟩ := (range_miyamotoDHom h L η).symm ▸ hd
    apply Subtype.ext
    simp only [hdM, hrM, coe_mul, coe_inv]
    have e := hS.R1G_conj_miyamotoDHom a
    rw [hS.R1G_inv, ← hrdef] at e
    rw [← ha, show r⁻¹ = r from hS.R1G_inv, e, map_inv]
  set c := compOne ψ dM with hc
  set c' := compOne ψ rM with hc'
  have hcc : c' * c * c'⁻¹ = c⁻¹ := by
    rw [hc, hc', ← map_inv, ← map_mul, ← map_mul, hrd, map_inv]
  have hc1 : c ≠ 1 := by
    intro e
    have e' : (ψ.symm ((ψ dM).1, 1) : miyamotoM1G h L η t) = 1 :=
      Subtype.ext (by simpa [hc, compOne_apply] using e)
    have h1 : (ψ dM).1 = 1 := by
      have := congrArg ψ e'
      simp only [MulEquiv.apply_symm_apply, map_one, Prod.mk_eq_one] at this
      exact this.1
    rw [hψA ⟨d, hdN⟩ dM rfl] at h1
    exact hd1' (congrArg Subtype.val (α.map_eq_one_iff.1 h1))
  have hcpow : c ^ (Nat.card k - 1) = 1 := by
    have h1 : (⟨d, hd⟩ : miyamotoDG h L η) ^ Nat.card (miyamotoDG h L η) = 1 := pow_card_eq_one'
    have h2 : d ^ ((2 ^ f) ^ 2 - 1) = 1 := by
      rw [card_miyamotoDG] at h1
      simpa using congrArg Subtype.val h1
    have h3 : dM ^ ((2 ^ f) ^ 2 - 1) = 1 := Subtype.ext (by simpa [hdM] using h2)
    rw [hc, ← map_pow, Nat.card_eq_fintype_card, hk, h3, map_one]
  have hnorm : ∀ m : miyamotoM1G h L η t, (m : G) ∈ normalizer (𝓦 : Set G) →
      ∀ w ∈ S, compOne ψ m * w * (compOne ψ m)⁻¹ ∈ S := by
    intro m hm w hw
    rw [← conj_eq_conj_compOne m (mem_inf.1 hw).2]
    exact mem_inf.2 ⟨(mem_normalizer_iff.1 hm w).1 (mem_inf.1 hw).1,
      (mem_normalizer_iff.1 (Common.le_normalizer_prodFactorOne ψ m.2) w).1 (mem_inf.1 hw).2⟩
  have hcS : c ∈ normalizer (S : Set G) := by
    refine mem_normalizer_of_conj_mem (hnorm dM (hS.DG_le_normalizer_W hd)) fun w hw => ?_
    have := hnorm dM⁻¹ (inv_mem (hS.DG_le_normalizer_W hd)) w hw
    rw [map_inv, inv_inv] at this
    rw [inv_inv]
    exact this
  have hScard : Nat.card S = Nat.card k := by
    rw [hSdef, (hS.W_eq_sup (ψ := ψ) hk).2.1, Nat.card_eq_fintype_card, hk]
  have key := le_sup_map_conj_of_conj_eq_inv (Common.prodFactorOneEquiv ψ) inf_le_right hScard
    (compOne_mem dM) (compOne_mem rM) hc1 hcpow hcS hcc
  refine key.trans (sup_le_sup_left ?_ _)
  rintro _ ⟨w, hw, rfl⟩
  refine ⟨w, hw, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact conj_eq_conj_compOne rM (mem_inf.1 hw).2

theorem X1_le_centralizer_Y [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a)) :
    prodFactorOne ψ ≤ centralizer ((𝓨 : Subgroup G) : Set G) := by
  set r := miyamotoR1G h L η with hrdef
  refine (hS.X1_le_W1_sup hk hψA).trans (sup_le (fun w hw => ?_) ?_)
  · rw [mem_centralizer_iff]
    intro y hy
    exact (mem_centralizer_iff.1 (mem_inf.1 (mem_inf.1 hy).1).2 w (mem_sup_right hw)).symm
  · rintro _ ⟨w, hw, rfl⟩
    rw [mem_centralizer_iff]
    intro y hy
    have hri : r⁻¹ = r := hS.R1G_inv
    have hy' : r⁻¹ * y * r ∈ 𝓨 := by
      have := hS.conj_R1G_mem_Y hy
      rw [hri] at this ⊢
      exact this
    have hc := mem_centralizer_iff.1 (mem_inf.1 (mem_inf.1 hy').1).2 w (mem_sup_right hw)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc y * (r * w * r⁻¹) = r * ((r⁻¹ * y * r) * w) * r⁻¹ := by group
      _ = r * (w * (r⁻¹ * y * r)) * r⁻¹ := by rw [hc]
      _ = r * w * r⁻¹ * y := by group

theorem sec5_1_two [Fintype k] (hS : Setting h L η t Q T) (hk : Fintype.card k = (2 ^ f) ^ 2)
    {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤)) :
    miyamotoF1G h L η t ⊔ prodFactorOne ψ ≤ centralizer ((𝓨 : Subgroup G) : Set G) ∧
      ∀ V : Subgroup G, V ≤ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) 𝓨 →
        miyamotoF1G h L η t ⊔ prodFactorOne ψ ≤ normalizer (V : Set G) →
          V = ⊥ ∨ V = Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) 𝓨 := by
  have : CharP k 2 := charP_of_card_eq_prime_pow (f := 2 * f) (by rw [hk, ← pow_mul, mul_comm])
  set Y := 𝓨 with hYdef
  have hYF1 : Y ≤ miyamotoF1G h L η t := inf_le_left.trans hS.centerIn_U_le_F1
  have hti : t⁻¹ = t := hS.t_inv
  refine ⟨sup_le (fun x hx => mem_centralizer_iff.2 fun y hy => hS.F1_comm (hYF1 hy) hx)
    (hS.X1_le_centralizer_Y hk hψA), fun V hV hKV => ?_⟩
  set V' := V.comap (MulEquiv.toMonoidHom (MulAut.conj t)) with hV'
  have hmemV' : ∀ x, x ∈ V' ↔ t * x * t⁻¹ ∈ V := fun x => by
    simp [hV', MulAut.conj_apply]
  have hV'Y : V' ≤ Y := fun x hx => by
    have := mem_map_conj_iff.1 (hV ((hmemV' x).1 hx))
    rwa [show t⁻¹ * (t * x * t⁻¹) * t = x by group] at this
  have hX2V' : prodFactorTwo ψ ≤ normalizer (V' : Set G) := by
    intro x hx
    have hx' : t * x * t⁻¹ ∈ prodFactorOne ψ := by
      have := hS.t_conj_mem_X1 hψt hx
      rw [hti] at this ⊢
      exact this
    have hN := mem_normalizer_iff.1 (hKV (mem_sup_right hx'))
    rw [mem_normalizer_iff]
    intro v
    rw [hmemV', hmemV', show t * (x * v * x⁻¹) * t⁻¹ =
      (t * x * t⁻¹) * (t * v * t⁻¹) * (t * x * t⁻¹)⁻¹ by group]
    exact hN _
  have hk' : Nat.card k = 2 ^ (2 * f) := by
    rw [Nat.card_eq_fintype_card, hk, ← pow_mul, mul_comm]
  have hYcard : Nat.card Y = 2 ^ (2 * (2 * f)) := by
    rw [(hS.sec5_1_one hk hψt hZ).1, ← pow_mul]
    ring_nf
  have hnc : ¬ prodFactorTwo ψ ≤ centralizer (Y : Set G) := fun hC => hS.Y_ne_bot hZ (by
    rw [← hS.Y_inf_centralizer_X2 hk]
    exact (inf_eq_left.2 (le_centralizer_iff.1 hC)).symm)
  have hf := hS.two_le
  rcases Common.eq_bot_or_eq_of_card_le (Common.prodFactorTwoEquiv ψ) hk' (by omega) (by omega)
    (fun x hx y hy => hS.F1_comm (hYF1 hx) (hYF1 hy)) hYcard le_rfl hS.X2_le_normalizer_Y hX2V'
    hV'Y hnc with h0 | h1
  · left
    rw [← map_comap_eq_self_of_surjective (f := MulEquiv.toMonoidHom (MulAut.conj t))
      (MulAut.conj t).surjective V, ← hV', h0, Subgroup.map_bot]
  · right
    rw [← map_comap_eq_self_of_surjective (f := MulEquiv.toMonoidHom (MulAut.conj t))
      (MulAut.conj t).surjective V, ← hV', h1]

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
