module

public import CFSG.GH74.GLS.SP.Local.SPLCoordT
public import CFSG.GH74.GLS.SP.Local.SPLCoordK
public import CFSG.GH74.GLS.SP.Local.SPLNatMod
public import CFSG.GH74.GLS.SP.Local.SPLCoordG
public import CFSG.GH74.GLS.SP.Local.SPLWt3
public import CFSG.GH74.GLS.Stage4.HexCScalar

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK.L2Torus CFSG.GH74.BNPair
open CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.LU.Local
open scoped commutatorElement Pointwise

section Quot

variable {G : Type} [Group G] (R N K : Subgroup G)

@[expose] def conjOn (hKR : ∀ k ∈ K, ∀ r ∈ R, k * r * k⁻¹ ∈ R) : ↥K →* MulAut ↥R where
  toFun k :=
    { toFun := fun r => ⟨(k : G) * r * (k : G)⁻¹, hKR k k.2 r r.2⟩
      invFun := fun r => ⟨(k : G)⁻¹ * r * (k : G), by
        have := hKR (k : G)⁻¹ (K.inv_mem k.2) r r.2
        simpa using this⟩
      left_inv := fun r => by ext; simp [mul_assoc]
      right_inv := fun r => by ext; simp [mul_assoc]
      map_mul' := fun r r' => by ext; simp [mul_assoc] }
  map_one' := by ext r; simp
  map_mul' := fun k k' => by ext r; simp [mul_assoc]

theorem conjOn_apply (hKR : ∀ k ∈ K, ∀ r ∈ R, k * r * k⁻¹ ∈ R) (k : ↥K) (r : ↥R) :
    ((conjOn R K hKR k r : ↥R) : G) = (k : G) * r * (k : G)⁻¹ := rfl

theorem subgroupOf_normal_of_central (hNc : ∀ y ∈ N, ∀ r ∈ R, y * r = r * y) :
    (N.subgroupOf R).Normal where
  conj_mem := by
    intro n hn g
    have hn' : (n : G) ∈ N := hn
    have : (g : G) * n * (g : G)⁻¹ = n := by
      rw [← hNc n hn' g g.2]; group
    show ((g * n * g⁻¹ : ↥R) : G) ∈ N
    simpa [this] using hn'

@[expose] noncomputable def quotAct (hKR : ∀ k ∈ K, ∀ r ∈ R, k * r * k⁻¹ ∈ R)
    (hKN : ∀ k ∈ K, ∀ y ∈ N, k * y = y * k) (hN : (N.subgroupOf R).Normal) :
    ↥K →* MulAut (↥R ⧸ N.subgroupOf R) where
  toFun k := QuotientGroup.congr (N.subgroupOf R) (N.subgroupOf R) (conjOn R K hKR k) (by
    ext r
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : (y : G) ∈ N := hy
      show ((conjOn R K hKR k y : ↥R) : G) ∈ N
      rw [conjOn_apply]
      have : (k : G) * y * (k : G)⁻¹ = y := by rw [hKN k k.2 y hy']; group
      rw [this]; exact hy'
    · intro hr
      refine ⟨(conjOn R K hKR k)⁻¹ r, ?_, by simp⟩
      have hr' : (r : G) ∈ N := hr
      show (((conjOn R K hKR k)⁻¹ r : ↥R) : G) ∈ N
      have e : ((conjOn R K hKR k)⁻¹ r : ↥R) = r := by
        apply (conjOn R K hKR k).injective
        simp only [MulAut.apply_inv_self]
        ext
        rw [conjOn_apply]
        have : (k : G) * r * (k : G)⁻¹ = r := by rw [hKN k k.2 r hr']; group
        rw [this]
      rw [e]; exact hr')
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H r => simp
  map_mul' := fun k k' => by
    ext x
    induction x using QuotientGroup.induction_on with
    | H r => simp

end Quot

@[expose] def NatModStmt : Prop :=
  ∀ {p n : ℕ}, p.Prime → p ≠ 2 → ∀ {Fq : Type} [Field Fq] [Finite Fq], Nat.card Fq = p ^ n →
    ∀ {K : Type} [Group K] (ε : K ≃* Matrix.SpecialLinearGroup (Fin 2) Fq)
      {V : Type} [CommGroup V] [Finite V], (∀ v : V, v ^ p = 1) → Nat.card V = p ^ (2 * n) →
      ∀ (ρ : K →* MulAut V), Function.Injective ρ →
        ∃ τ : V ≃* Multiplicative (Fin 2 → Fq), ∀ (k : K) (v : V),
          τ (ρ k v) = Multiplicative.ofAdd
            (((ε k : Matrix.SpecialLinearGroup (Fin 2) Fq) : Matrix (Fin 2) (Fin 2) Fq).mulVec
              (Multiplicative.toAdd (τ v)))

theorem natModStmt_of_11_1b (h11 : IVK.Proofs2.IVK_11_1b_nat) : NatModStmt := by
  intro p n hp hp2 Fq _ _ hq K _ ε V _ _ hexp hcard ρ hf
  exact natural_module_of_11_1b h11 hp hp2 hq ε hexp hcard ρ hf

section Stage

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_le_of_comm (D : SPLNot3 G) (h3 : SPL3M2 D) :
    commutator ↥D.R₂ ≤ D.X₂.subgroupOf D.R₂ := by
  rw [commutator_def, Subgroup.commutator_le]
  intro g₁ _ g₂ _
  show ((⁅g₁, g₂⁆ : ↥D.R₂) : G) ∈ D.X₂
  have : ((⁅g₁, g₂⁆ : ↥D.R₂) : G) = ⁅(g₁ : G), (g₂ : G)⁆ := rfl
  rw [this, ← h3.R₂_comm]
  exact Subgroup.commutator_mem_commutator g₁.2 g₂.2

omit [Finite G] in
theorem X₂_central_R₂ (D : SPLNot3 G) (h3 : SPL3M2 D) :
    ∀ y ∈ D.X₂, ∀ r ∈ D.R₂, y * r = r * y := by
  intro y hy r hr
  have hy' : y ∈ (center ↥D.R₂).map D.R₂.subtype := by rw [h3.R₂_center]; exact hy
  obtain ⟨c, hc, rfl⟩ := hy'
  have := Subgroup.mem_center_iff.mp hc ⟨r, hr⟩
  exact congrArg Subtype.val this.symm

theorem K₁_cen_X₂ (D : SPLNot3 G) (hs : SPLSetup D.toSPLNot0) (h3 : SPL3M2 D) :
    ∀ k ∈ D.K₁, ∀ y ∈ D.X₂, k * y = y * k := fun k hk y hy =>
  hs.comps.comm k hk y (X₂_le_K₂ D hs h3.toSPL3X hy)

theorem z_nontrivial_mod_X₂ (D : SPLNot3 G) (hs : SPLSetup D.toSPLNot0) (h3 : SPL3M2 D)
    (hR : SPLR₁ D) : ∃ r ∈ D.R₂, D.z * r * D.z⁻¹ * r⁻¹ ∉ D.X₂ := by
  obtain ⟨x, hx, hx1⟩ := exists_ne_one_of_two_le D.X₃ (by
    rw [X₃_card D h3]; have := hs.q_ge; omega)
  refine ⟨x, X₃_le_R₂ D hx, fun hmem => ?_⟩
  have h1' := h3.z_X₃ x hx
  have e : D.z * x * D.z⁻¹ * x⁻¹ = x⁻¹ * x⁻¹ := by rw [h1']
  rw [e] at hmem
  have hX₃ : x⁻¹ * x⁻¹ ∈ D.X₃ := D.X₃.mul_mem (D.X₃.inv_mem hx) (D.X₃.inv_mem hx)
  have h12 : x⁻¹ * x⁻¹ ∈ D.X₂ ⊓ D.X₃ := ⟨hmem, hX₃⟩
  rw [X₂_inf_X₃ D h3 hR] at h12
  have h0 : x⁻¹ * x⁻¹ = 1 := Subgroup.mem_bot.mp h12
  have hxx : x * x = 1 := by
    have := congrArg (fun y => y⁻¹) h0
    simpa [mul_inv_rev] using this
  exact hx1 (eq_one_of_inv_eq_self (hs.prime.odd_of_ne_two hs.p_ne_two) ((X₃_eab D h3).2 x hx)
    (inv_eq_of_mul_eq_one_right hxx))

theorem X₂_inf_X₄ (D : SPLNot3 G) (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1)
    (h3 : SPL3M2 D) (hR : SPLR₁ D) :
    D.X₂ ⊓ D.X₄ = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx2, hx4⟩
  have hx4' : D.w₁ * x * D.w₁⁻¹ ∈ D.X₃ := (mem_conjBy_iff).mp hx4
  have hc : D.w₁ * x * D.w₁⁻¹ = x := by
    rw [K₁_cen_X₂ D hs h3 D.w₁ h1.w₁_mem x hx2]; group
  rw [hc] at hx4'
  have h12 : x ∈ D.X₂ ⊓ D.X₃ := ⟨hx2, hx4'⟩
  rw [X₂_inf_X₃ D h3 hR] at h12
  exact h12

theorem coords_of_stage (hNM : NatModStmt) (D : SPLNot3 G) (hs : SPLSetup D.toSPLNot0)
    (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D) (hR : SPLR₁ D) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = D.q ∧
      ∃ x₁ x₂ x₃ x₄ : F → ↥D.P, SPLCoord x₁ x₂ x₃ x₄ ∧
        (∀ g : ↥D.P, (g : G) ∈ D.X₁ ↔ ∃ s, x₁ s = g) ∧ (∀ g : ↥D.P, (g : G) ∈ D.X₂ ↔ ∃ s, x₂ s = g) ∧
        (∀ g : ↥D.P, (g : G) ∈ D.X₃ ↔ ∃ s, x₃ s = g) ∧
        (∀ g : ↥D.P, (g : G) ∈ D.X₄ ↔ ∃ s, x₄ s = g) := by
  classical
  obtain ⟨F, hFfield, hFfin, ε, hFq, hE1, hE2, hE3⟩ :=
    sl2_iso_data D.K₁ D.q D.p hs.prime hs.comps.sl₁ hs.odd_q hs.q_ge hs.q_pow D.h₁ D.w₁ h1.h₁_mem
      h1.w₁_mem h1.h₁_ord h1.w₁_inv D.X₁ h3.X₁_le h3.X₁_card
      (fun g hg x hx => h3.H_X₁ g (H₁_le_H D hg) x hx)
  refine ⟨F, hFfield, hFfin, hFq, ?_⟩
  obtain ⟨k, -, hqk⟩ := hs.q_pow
  have hFq' : Nat.card F = D.p ^ k := hFq.trans hqk
  have hX₂R : D.X₂ ≤ D.R₂ := le_sup_left.trans le_sup_left
  have hX₃R : D.X₃ ≤ D.R₂ := X₃_le_R₂ D
  have hX₄R : D.X₄ ≤ D.R₂ := le_sup_right
  have hKR : ∀ k ∈ D.K₁, ∀ r ∈ D.R₂, k * r * k⁻¹ ∈ D.R₂ :=
    K₁_normalizes_R₂ D hs h3.toSPL3X h3.R₂_normal
  have hKX₂ := K₁_cen_X₂ D hs h3
  have hX₂c := X₂_central_R₂ D h3
  have hnorm : (D.X₂.subgroupOf D.R₂).Normal := subgroupOf_normal_of_central D.R₂ D.X₂ hX₂c
  have _hnorm := hnorm
  have hcomm : IsMulCommutative (↥D.R₂ ⧸ D.X₂.subgroupOf D.R₂) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr (commutator_le_of_comm D h3)
  let instCG : CommGroup (↥D.R₂ ⧸ D.X₂.subgroupOf D.R₂) :=
    { (inferInstance : Group (↥D.R₂ ⧸ D.X₂.subgroupOf D.R₂)) with
      mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
  let π : ↥D.R₂ →* (↥D.R₂ ⧸ D.X₂.subgroupOf D.R₂) := QuotientGroup.mk' _
  let ρ := quotAct D.R₂ D.X₂ D.K₁ hKR hKX₂ hnorm
  have hπker : ∀ r : ↥D.R₂, π r = 1 ↔ (r : G) ∈ D.X₂ := fun r => by
    show QuotientGroup.mk r = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    rfl
  have hπsurj : Function.Surjective π := QuotientGroup.mk_surjective
  have hexp : ∀ v : ↥D.R₂ ⧸ D.X₂.subgroupOf D.R₂, v ^ D.p = 1 := by
    intro v
    obtain ⟨⟨r, hr⟩, rfl⟩ := hπsurj v
    have hr' : r ∈ ((D.R₂ : Set G)) := hr
    rw [h3.R₂_prod] at hr'
    obtain ⟨_, ⟨y, hy, a, ha, rfl⟩, b, hb, rfl⟩ := hr'
    have hya : π ⟨y * a * b, hr⟩ = π ⟨a, hX₃R ha⟩ * π ⟨b, hX₄R hb⟩ := by
      have e : (⟨y * a * b, hr⟩ : ↥D.R₂) = ⟨y, hX₂R hy⟩ * ⟨a, hX₃R ha⟩ * ⟨b, hX₄R hb⟩ := rfl
      rw [e, map_mul, map_mul, (hπker ⟨y, hX₂R hy⟩).2 hy, one_mul]
    rw [hya, mul_pow, ← map_pow, ← map_pow]
    have ha' : (⟨a, hX₃R ha⟩ : ↥D.R₂) ^ D.p = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow]; exact (X₃_eab D h3).2 a ha)
    have hb' : (⟨b, hX₄R hb⟩ : ↥D.R₂) ^ D.p = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow]; exact (X₄_eab D h3).2 b hb)
    rw [ha', hb']
    simp
  have hVcard : Nat.card (↥D.R₂ ⧸ D.X₂.subgroupOf D.R₂) = D.p ^ (2 * k) := by
    have h1' := Subgroup.card_eq_card_quotient_mul_card_subgroup (D.X₂.subgroupOf D.R₂)
    have h2' : Nat.card (D.X₂.subgroupOf D.R₂) = D.q := by
      rw [← X₂_card D h3]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX₂R).toEquiv
    have h3' : Nat.card ↥D.R₂ = D.q ^ 3 := h3.R₂_card
    rw [h3', h2'] at h1'
    have hq0 : 0 < D.q := by have := hs.q_ge; omega
    have : Nat.card (↥D.R₂ ⧸ D.X₂.subgroupOf D.R₂) = D.q ^ 2 := by
      apply Nat.eq_of_mul_eq_mul_right hq0
      rw [← h1']; ring
    rw [this, hqk, ← pow_mul, mul_comm]
  have hz := z_nontrivial_mod_X₂ D hs h3 hR
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro k hk
    apply Subtype.ext
    rw [Subgroup.coe_one]
    refine kernel_eq_one_of_quasisimple D.K₁ D.R₂ D.X₂ D.z hs.comps.quasi₁ hs.comps.cen₁
      (z_mul_z D hs) hKR ?_ (z_mem_K₁ hs) hz k.2 ?_
    · intro k' hk' y hy
      have : k' * y * k'⁻¹ = y := by rw [hKX₂ k' hk' y hy]; group
      rw [this]; exact hy
    · intro r hr
      have e := congrArg (fun f => f (QuotientGroup.mk ⟨r, hr⟩)) hk
      simp only [MulAut.one_apply] at e
      rw [show ρ k (QuotientGroup.mk ⟨r, hr⟩) =
        QuotientGroup.mk (conjOn D.R₂ D.K₁ hKR k ⟨r, hr⟩) from rfl] at e
      have e2 := (QuotientGroup.eq).mp e
      have e3 : ((k : G) * r * (k : G)⁻¹)⁻¹ * r ∈ D.X₂ := e2
      have e4 : r⁻¹ * ((k : G) * r * (k : G)⁻¹) ∈ D.X₂ := by
        have := D.X₂.inv_mem e3
        simpa [mul_assoc] using this
      have e5 := hX₂c _ e4 r hr
      have h6 : r * (r⁻¹ * ((k : G) * r * (k : G)⁻¹)) = (r⁻¹ * ((k : G) * r * (k : G)⁻¹)) * r :=
        e5.symm
      have : (k : G) * r * (k : G)⁻¹ * r⁻¹ = r⁻¹ * ((k : G) * r * (k : G)⁻¹) := by
        calc (k : G) * r * (k : G)⁻¹ * r⁻¹
            = (r * (r⁻¹ * ((k : G) * r * (k : G)⁻¹))) * r⁻¹ := by group
          _ = ((r⁻¹ * ((k : G) * r * (k : G)⁻¹)) * r) * r⁻¹ := by rw [h6]
          _ = _ := by group
      rw [this]; exact e4
  obtain ⟨τ, hτ⟩ := hNM hs.prime hs.p_ne_two hFq' ε hexp hVcard ρ hρinj
  have hup : ∀ s : F, ((ε.symm (sl2U s) : ↥D.K₁) : G) ∈ D.X₁ := fun s => by
    refine (hE1 _).2 ?_
    rw [MulEquiv.apply_symm_apply]
    simp [SL2Root.mem_upperSub]
  have hND : SPLNatData D.K₁ D.X₁ D.X₂ D.X₃ D.X₄ D.R₂ ε π ρ τ D.w₁ :=
    { X₂_R := hX₂R
      X₃_R := hX₃R
      X₄_R := hX₄R
      π_ker := hπker
      K_R := hKR
      ρ_π := fun k r => rfl
      τ_ρ := hτ
      X₂₃ := X₂_inf_X₃ D h3 hR
      X₂₄ := X₂_inf_X₄ D hs h1 h3 hR
      card₃ := (X₃_card D h3).trans hFq.symm
      card₄ := (X₄_card D h3).trans hFq.symm
      X₁_X₃ := h3.X₁_X₃
      X₁_upper := hup
      w_mem := h1.w₁_mem
      X₄_eq := fun x => mem_conjBy_iff
      w_anti := hE3
      H₃ := fun u x hx => h3.H_X₃ _ (H₁_le_H D (hE2 u)) x hx
      H₄ := fun u x hx => H_X₄ D hs h1 h3 _ (H₁_le_H D (hE2 u)) x hx }
  obtain ⟨x₃, x₄, hadd₃, hadd₄, hrng₃, hrng₄, huX₄, hdg₃, hdg₄⟩ := hND.exists_x34
  let x₁ : F → G := fun s => ((ε.symm (sl2U s) : ↥D.K₁) : G)
  let dg : Fˣ → G := fun u => ((ε.symm (sl2D u) : ↥D.K₁) : G)
  have hx₁mem : ∀ s, x₁ s ∈ D.K₁ := fun s => (ε.symm (sl2U s)).2
  have hdgmem : ∀ u, dg u ∈ D.K₁ := fun u => (ε.symm (sl2D u)).2
  have hrng₁ : ∀ g, g ∈ D.X₁ ↔ ∃ s, x₁ s = g := fun g => by
    constructor
    · intro hg
      have hgK : g ∈ D.K₁ := h3.X₁_le hg
      have hk := (hE1 ⟨g, hgK⟩).1 hg
      refine ⟨(ε ⟨g, hgK⟩ : SL2m F).1 0 1, ?_⟩
      have hU : ε ⟨g, hgK⟩ = sl2U ((ε ⟨g, hgK⟩ : SL2m F).1 0 1) := by
        obtain ⟨h00, h11, h10⟩ := hk
        apply Matrix.SpecialLinearGroup.ext
        intro i j
        fin_cases i <;> fin_cases j <;> simp [h00, h11, h10]
      show ((ε.symm (sl2U _) : ↥D.K₁) : G) = g
      rw [← hU]; simp
    · rintro ⟨s, rfl⟩
      exact hup s
  have htwo : (2 : F) ≠ 0 := by
    intro h2
    have := Fintype.ofFinite F
    have : Fact D.p.Prime := ⟨hs.prime⟩
    have hchar : CharP F D.p :=
      charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hFq')
    have hdvd : D.p ∣ 2 := (CharP.cast_eq_zero_iff F D.p 2).mp (by simpa using h2)
    exact hs.p_ne_two ((Nat.prime_dvd_prime_iff_eq hs.prime Nat.prime_two).mp hdvd)
  have hPset : ((D.P : Subgroup G) : Set G) = (D.X₁ : Set G) * (D.R₂ : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right D.X₁ D.R₂ (fun x hx => by
      rw [mem_normalizer_iff]
      intro r
      constructor
      · intro hr; exact hKR x (h3.X₁_le hx) r hr
      · intro hr
        have := hKR x⁻¹ (D.K₁.inv_mem (h3.X₁_le hx)) _ hr
        simpa [mul_assoc] using this)
  have hsl : SPLGData D.X₁ D.X₂ D.X₃ D.X₄ D.R₂ D.P x₁ x₃ x₄ dg (Nat.card F) :=
    { card_F := rfl
      two_ne := htwo
      add₁ := fun s s' => by
        show ((ε.symm (sl2U (s + s')) : ↥D.K₁) : G) = _
        rw [sl2U_add, map_mul]; rfl
      add₃ := hadd₃
      add₄ := hadd₄
      rng₁ := hrng₁
      rng₃ := hrng₃
      rng₄ := hrng₄
      X₁_le := le_sup_left
      X₂_le := hX₂R
      X₃_le := hX₃R
      X₄_le := hX₄R
      R₂_le := le_sup_right
      card₂ := (X₂_card D h3).trans hFq.symm
      cardR := by rw [hFq]; exact h3.R₂_card
      cardP := by rw [hFq]; exact h3.P_card
      cen₂ := fun y hy r hr => by
        have hr' : r ∈ ((D.X₁ : Set G) * (D.R₂ : Set G)) := by rw [← hPset]; exact hr
        obtain ⟨a, ha, b, hb, rfl⟩ := hr'
        calc y * (a * b) = (y * a) * b := by group
          _ = (a * y) * b := by rw [(hKX₂ a (h3.X₁_le ha) y hy).symm]
          _ = a * (y * b) := by group
          _ = a * (b * y) := by rw [hX₂c y hy b hb]
          _ = a * b * y := by group
      comm_R := fun r hr r' hr' => by
        rw [← h3.R₂_comm]
        exact Subgroup.commutator_mem_commutator hr hr'
      X₂_comm := h3.R₂_comm.ge
      fac₂ := fun r hr => by
        have hr' : r ∈ ((D.R₂ : Set G)) := hr
        rw [h3.R₂_prod] at hr'
        obtain ⟨_, ⟨y, hy, a, ha, rfl⟩, b, hb, rfl⟩ := hr'
        obtain ⟨a', rfl⟩ := (hrng₃ a).1 ha
        obtain ⟨b', rfl⟩ := (hrng₄ b).1 hb
        exact ⟨y, hy, a', b', rfl⟩
      fac_P := fun g hg => by
        have hg' : g ∈ ((D.X₁ : Set G) * (D.R₂ : Set G)) := by rw [← hPset]; exact hg
        obtain ⟨a, ha, r, hr, rfl⟩ := hg'
        obtain ⟨s, rfl⟩ := (hrng₁ a).1 ha
        exact ⟨s, r, hr, rfl⟩
      c13 := fun s a => h3.X₁_X₃ _ (hup s) _ ((hrng₃ _).2 ⟨a, rfl⟩)
      dg_X₁ := fun u s => by
        have e : ε.symm (sl2D u) * ε.symm (sl2U s) =
            ε.symm (sl2U ((u : F) ^ 2 * s)) * ε.symm (sl2D u) := by
          rw [← map_mul, ← map_mul, sl2D_mul_sl2U_eq]
        have e' := congrArg (fun z : ↥D.K₁ => (z : G)) e
        simp only [Subgroup.coe_mul] at e'
        show ((ε.symm (sl2D u) : ↥D.K₁) : G) * ((ε.symm (sl2U s) : ↥D.K₁) : G) *
          ((ε.symm (sl2D u) : ↥D.K₁) : G)⁻¹ = ((ε.symm (sl2U ((u : F) ^ 2 * s)) : ↥D.K₁) : G)
        rw [e']; group
      dg_X₃ := hdg₃
      dg_X₄ := hdg₄
      dg_X₂ := fun u y hy => hKX₂ _ (hdgmem u) y hy
      u_X₄ := huX₄ }
  obtain ⟨x₂, hx₂mem, hrng₂, hcoord⟩ := hsl.exists_coord
  have hrange : ∀ (Y : Subgroup G) (y : F → G) (hy : ∀ s, y s ∈ D.P),
      (∀ g, g ∈ Y ↔ ∃ s, y s = g) →
        ∀ g : ↥D.P, (g : G) ∈ Y ↔ ∃ s, (⟨y s, hy s⟩ : ↥D.P) = g := by
    intro Y y hy hr g
    constructor
    · intro hg
      obtain ⟨s, hs'⟩ := (hr _).1 hg
      exact ⟨s, Subtype.ext hs'⟩
    · rintro ⟨s, rfl⟩
      exact (hr _).2 ⟨s, rfl⟩
  exact ⟨fun s => ⟨x₁ s, hsl.x₁_mem_P s⟩, fun c => ⟨x₂ c, hx₂mem c⟩,
    fun a => ⟨x₃ a, hsl.x₃_mem_P a⟩, fun b => ⟨x₄ b, hsl.x₄_mem_P b⟩, hcoord,
    hrange _ _ _ hrng₁, hrange _ _ _ hrng₂, hrange _ _ _ hrng₃, hrange _ _ _ hrng₄⟩

end Stage

end CFSG.GH74.GLS.SP.Local
