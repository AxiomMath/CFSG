module

public import CFSG.CGT.Stroth77.Extension218Cocycle
public import CFSG.CGT.Stroth77.Extension218Parity
public import CFSG.CGT.Stroth77.Extension22Four
public import CFSG.CGT.Stroth77.Extension218Assembly
public import CFSG.CGT.Stroth77.Extension218Square

public section

namespace CFSG.CGT.Stroth77

open Ext218

variable {S : Type*} [Group S] [Finite S] {B C : Subgroup S}

theorem exists_ne_ne_of_card_eq_four218 {Q : Type*} [Finite Q] (hQ : Nat.card Q = 4) (a b : Q) :
    ∃ q, q ≠ a ∧ q ≠ b := by
  classical
  by_contra h
  push Not at h
  haveI := Fintype.ofFinite Q
  have hle : (Finset.univ : Finset Q).card ≤ ({a, b} : Finset Q).card :=
    Finset.card_le_card fun q _ => by
      by_cases hq : q = a
      · simp [hq]
      · simp [h q hq]
  have h2 := Finset.card_le_two (a := a) (b := b)
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hQ] at hle
  omega

theorem eq_or_of_card_eq_four218 {Q : Type*} [Finite Q] (hQ : Nat.card Q = 4) {q₀ q₁ q₂ q₃ : Q}
    (h01 : q₀ ≠ q₁) (h02 : q₀ ≠ q₂) (h03 : q₀ ≠ q₃) (h12 : q₁ ≠ q₂) (h13 : q₁ ≠ q₃)
    (h23 : q₂ ≠ q₃) (q : Q) : q = q₀ ∨ q = q₁ ∨ q = q₂ ∨ q = q₃ := by
  classical
  by_contra hq
  push Not at hq
  obtain ⟨hq0, hq1, hq2, hq3⟩ := hq
  haveI := Fintype.ofFinite Q
  have h5 : ({q, q₀, q₁, q₂, q₃} : Finset Q).card = 5 := by
    rw [Finset.card_insert_of_notMem (by simp [hq0, hq1, hq2, hq3]),
      Finset.card_insert_of_notMem (by simp [h01, h02, h03]),
      Finset.card_insert_of_notMem (by simp [h12, h13]), Finset.card_pair h23]
  have hle := Finset.card_le_univ ({q, q₀, q₁, q₂, q₃} : Finset Q)
  rw [h5, ← Nat.card_eq_fintype_card, hQ] at hle
  omega

section Sigma

variable {s : ℕ} {hs : 1 ≤ s} (D : StrothTypeData B (StrothTypeIndex.t221 s hs))
  (hexp : ∀ x ∈ C, x * x ∈ B)

noncomputable def sigma221 (x : C) : ZMod 2 × ZMod 2 × ZMod 2 :=
  par221 s (D.ec ⟨(x : S) * x, hexp _ x.2⟩)

variable {D hexp}

theorem comm_of_mem218 (hC : C ≤ Subgroup.centralizer (B : Set S)) {b z : S} (hb : b ∈ B)
    (hz : z ∈ C) : b * z = z * b :=
  Subgroup.mem_centralizer_iff.mp (hC hz) b hb

theorem par221_ec_mul (b c : B) :
    par221 s (D.ec (b * c)) = par221 s (D.ec b) + par221 s (D.ec c) := by
  rw [D.ec_mul]
  exact map_add (par221 s) (D.ec b) (D.ec c)

theorem par221_ec_of_sq_eq_one {b : B} (hb : b * b = 1) : par221 s (D.ec b) = 0 := by
  have h2 : (2 : ℤ) • (D.ec b : Torus (Type221.k s)) = 0 := by
    rw [two_zsmul]
    have h := congrArg D.ec hb
    rwa [D.ec_mul, D.ec_one] at h
  obtain ⟨x, y, z, -, -, -, hω⟩ := exists_bits_of_two_smul_eq_zero
    (by change 1 ≤ s + 2; omega) (by change 1 ≤ s + 4; omega) (by change 1 ≤ s + 4; omega) h2
  rw [hω]
  exact par221_bv x y z

theorem sigma221_mul (hC : C ≤ Subgroup.centralizer (B : Set S)) (x y : C) :
    sigma221 D hexp (x * y) = sigma221 D hexp x + sigma221 D hexp y := by
  set X : S := (x : S) with hX
  set Y : S := (y : S) with hY
  have hXC : X ∈ C := x.2
  have hYC : Y ∈ C := y.2
  have hX2 : X * X ∈ B := hexp X hXC
  have hY2 : Y * Y ∈ B := hexp Y hYC
  have hXY2 : X * Y * (X * Y) ∈ B := hexp (X * Y) (C.mul_mem hXC hYC)
  have hYYX : (Y * Y)⁻¹ * X = X * (Y * Y)⁻¹ := comm_of_mem218 hC (B.inv_mem hY2) hXC
  have hK : X⁻¹ * Y⁻¹ * X * Y = (X * X)⁻¹ * ((Y * Y)⁻¹ * (X * Y * (X * Y))) := by
    calc X⁻¹ * Y⁻¹ * X * Y = (X * X)⁻¹ * ((X * (Y * Y)⁻¹) * Y * X * Y) := by group
      _ = (X * X)⁻¹ * (((Y * Y)⁻¹ * X) * Y * X * Y) := by rw [hYYX]
      _ = (X * X)⁻¹ * ((Y * Y)⁻¹ * (X * Y * (X * Y))) := by group
  have hKB : X⁻¹ * Y⁻¹ * X * Y ∈ B := by
    rw [hK]
    exact B.mul_mem (B.inv_mem hX2) (B.mul_mem (B.inv_mem hY2) hXY2)
  have hKK : (X⁻¹ * Y⁻¹ * X * Y) * (X⁻¹ * Y⁻¹ * X * Y) = 1 := by
    set K := X⁻¹ * Y⁻¹ * X * Y with hKdef
    have h1 : Y⁻¹ * X * Y = X * K := by rw [hKdef]; group
    have hKY : K * Y = Y * K := comm_of_mem218 hC hKB hYC
    have h2 : Y⁻¹ * K * Y = K := by
      rw [mul_assoc, hKY, ← mul_assoc, inv_mul_cancel, one_mul]
    have hYY : (Y * Y) * X = X * (Y * Y) := comm_of_mem218 hC hY2 hXC
    have h3 : (Y * Y)⁻¹ * X * (Y * Y) = X := by
      rw [mul_assoc, ← hYY, ← mul_assoc, inv_mul_cancel, one_mul]
    have h4 : (Y * Y)⁻¹ * X * (Y * Y) = X * K * K := by
      calc (Y * Y)⁻¹ * X * (Y * Y) = Y⁻¹ * (Y⁻¹ * X * Y) * Y := by group
        _ = Y⁻¹ * (X * K) * Y := by rw [h1]
        _ = (Y⁻¹ * X * Y) * (Y⁻¹ * K * Y) := by group
        _ = X * K * K := by rw [h1, h2]
    have h5 : X * (K * K) = X * 1 := by rw [mul_one, ← mul_assoc, ← h4, h3]
    exact mul_left_cancel h5
  have hsq : (⟨X * Y * (X * Y), hXY2⟩ : B) =
      ⟨Y * Y, hY2⟩ * (⟨X * X, hX2⟩ * ⟨X⁻¹ * Y⁻¹ * X * Y, hKB⟩) := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [hK]
    group
  have hsK : (⟨X⁻¹ * Y⁻¹ * X * Y, hKB⟩ : B) * ⟨X⁻¹ * Y⁻¹ * X * Y, hKB⟩ = 1 :=
    Subtype.ext hKK
  have hpK := par221_ec_of_sq_eq_one (D := D) hsK
  have hxy : sigma221 D hexp (x * y) = par221 s (D.ec ⟨X * Y * (X * Y), hXY2⟩) := rfl
  rw [hxy, hsq, par221_ec_mul, par221_ec_mul, hpK, add_zero, add_comm]
  rfl

theorem sigma221_inclusion (hBC : B ≤ C) (b : B) :
    sigma221 D hexp (Subgroup.inclusion hBC b) = 0 := by
  have h : sigma221 D hexp (Subgroup.inclusion hBC b) = par221 s (D.ec (b * b)) := rfl
  rw [h, D.ec_mul, ← two_zsmul]
  exact par221_two_smul _

theorem mem_of_sigma221_eq_zero {S' : Subgroup S} (hBC : B ≤ C)
    (hC : C ≤ Subgroup.centralizer (B : Set S)) (hH : NoInvolutionsCentralizing S' B)
    (hcS : C ≤ S') {x : C} (h : sigma221 D hexp x = 0) : (x : S) ∈ B := by
  set X : S := (x : S) with hX
  have hXC : X ∈ C := x.2
  obtain ⟨t, ht⟩ := exists_two_smul_of_par221_eq_zero h
  set b : B := Additive.toMul (D.e.symm t) with hbdef
  have hbt : D.ec b = t := by
    rw [hbdef]
    exact D.e.apply_symm_apply _
  have hbb : (b : S) * b = X * X := by
    have h1 : b * b = ⟨X * X, hexp _ hXC⟩ := by
      apply D.ec_injective
      rw [D.ec_mul, hbt, ht]
      exact (two_zsmul t).symm
    exact congrArg Subtype.val h1
  have hcb : (b : S)⁻¹ * X = X * (b : S)⁻¹ := comm_of_mem218 hC (B.inv_mem b.2) hXC
  have hy2 : (X * (b : S)⁻¹) * (X * (b : S)⁻¹) = 1 := by
    calc (X * (b : S)⁻¹) * (X * (b : S)⁻¹) = X * ((b : S)⁻¹ * X) * (b : S)⁻¹ := by group
      _ = X * (X * (b : S)⁻¹) * (b : S)⁻¹ := by rw [hcb]
      _ = (X * X) * ((b : S) * b)⁻¹ := by group
      _ = 1 := by rw [hbb, mul_inv_cancel]
  have hyC : X * (b : S)⁻¹ ∈ C := C.mul_mem hXC (hBC (B.inv_mem b.2))
  have hyB : X * (b : S)⁻¹ ∈ B := hH _ (hcS hyC) hy2 (hC hyC)
  have hXe : X = X * (b : S)⁻¹ * b := by group
  rw [hXe]
  exact B.mul_mem hyB b.2

theorem sigma221_conj {g : S} (hgC : g ∈ Subgroup.normalizer C)
    (hgB : g ∈ Subgroup.normalizer B) (x : C) :
    sigma221 D hexp (conjBy hgC x) = par221 s (D.ec (conjBy hgB ⟨(x : S) * x, hexp _ x.2⟩)) := by
  have h : (⟨((conjBy hgC x : C) : S) * (conjBy hgC x : C), hexp _ (conjBy hgC x).2⟩ : B) =
      conjBy hgB ⟨(x : S) * x, hexp _ x.2⟩ := by
    apply Subtype.ext
    simp only [conjBy_val]
    group
  exact congrArg (fun z => par221 s (D.ec z)) h

theorem sigma221_conj_ρ (hL : D.L ≤ Subgroup.normalizer C) (x : C) :
    sigma221 D hexp (conjBy (hL D.ρ_mem_L) x) = rhoBar221 (sigma221 D hexp x) := by
  rw [sigma221_conj (hL D.ρ_mem_L) D.ρ_mem, ec_conj_ρ_t221 D]
  exact par221_phiR (Type221.data s) _

theorem sigma221_conj_uv (hL : D.L ≤ Subgroup.normalizer C) (x : C) :
    sigma221 D hexp (conjBy (hL D.uv_mem_L) x) = uvBar221 (sigma221 D hexp x) := by
  rw [sigma221_conj (hL D.uv_mem_L) D.uv_mem, ec_conj_uv_t221 D]
  exact par221_phiUV (Type221.data s) _

end Sigma

theorem false_of_index_four_t221_of_data {B C S' : Subgroup S} {s : ℕ} {hs : 1 ≤ s}
    (D : StrothTypeData B (StrothTypeIndex.t221 s hs))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B) (hexp : ∀ x ∈ C, x * x ∈ B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') : False := by
  classical
  set H := B.subgroupOf C
  have hQ : Nat.card (C ⧸ H) = 4 := by
    rw [← Subgroup.index_eq_card]
    exact index_four_of_relIndex hBC hrel
  have hmem : ∀ z : C, z ∈ H ↔ (z : S) ∈ B := fun z => Subgroup.mem_subgroupOf
  obtain ⟨q₁, hq₁, -⟩ := exists_ne_ne_of_card_eq_four218 hQ (QuotientGroup.mk 1)
    (QuotientGroup.mk 1)
  obtain ⟨x₁, rfl⟩ := QuotientGroup.mk_surjective q₁
  obtain ⟨q₂, hq₂, hq₂'⟩ := exists_ne_ne_of_card_eq_four218 hQ (QuotientGroup.mk 1)
    (QuotientGroup.mk x₁⁻¹)
  obtain ⟨x₂, rfl⟩ := QuotientGroup.mk_surjective q₂
  have hx₁ : (x₁ : S) ∉ B := by
    intro h
    exact hq₁ ((QuotientGroup.eq (s := H)).mpr (by simpa [hmem] using B.inv_mem h))
  have hx₂ : (x₂ : S) ∉ B := by
    intro h
    exact hq₂ ((QuotientGroup.eq (s := H)).mpr (by simpa [hmem] using B.inv_mem h))
  have hx₁₂ : ((x₁ * x₂ : C) : S) ∉ B := by
    intro h
    apply hq₂'
    apply (QuotientGroup.eq (s := H)).mpr
    rw [hmem]
    have h' : ((x₂⁻¹ * x₁⁻¹ : C) : S) ∈ B := by
      have := B.inv_mem h
      simpa [_root_.mul_inv_rev] using this
    simpa using h'
  set σ := sigma221 D hexp
  have hσmul : ∀ x y : C, σ (x * y) = σ x + σ y := sigma221_mul hC
  have hσB : ∀ b : B, σ (Subgroup.inclusion hBC b) = 0 := sigma221_inclusion hBC
  have hσ0 : ∀ x : C, σ x = 0 → (x : S) ∈ B := fun x hx =>
    mem_of_sigma221_eq_zero hBC hC hH hcS hx
  have hw₁ : σ x₁ ≠ 0 := fun h => hx₁ (hσ0 _ h)
  have hw₂ : σ x₂ ≠ 0 := fun h => hx₂ (hσ0 _ h)
  have hw₁₂ : σ x₁ ≠ σ x₂ := by
    intro h
    apply hx₁₂
    apply hσ0
    rw [hσmul, h]
    exact add_self_eq_zero_t221 _
  have hcover : ∀ y : C, σ y = 0 ∨ σ y = σ x₁ ∨ σ y = σ x₂ ∨ σ y = σ x₁ + σ x₂ := by
    intro y
    have hne : ∀ {a b : C}, (a⁻¹ * b : C) ∉ H → (QuotientGroup.mk a : C ⧸ H) ≠ QuotientGroup.mk b :=
      fun h h' => h ((QuotientGroup.eq (s := H)).mp h')
    have h01 : (QuotientGroup.mk 1 : C ⧸ H) ≠ QuotientGroup.mk x₁ :=
      hne (by rw [hmem]; simpa using hx₁)
    have h02 : (QuotientGroup.mk 1 : C ⧸ H) ≠ QuotientGroup.mk x₂ :=
      hne (by rw [hmem]; simpa using hx₂)
    have h03 : (QuotientGroup.mk 1 : C ⧸ H) ≠ QuotientGroup.mk (x₁ * x₂) :=
      hne (by rw [hmem]; simpa using hx₁₂)
    have h12 : (QuotientGroup.mk x₁ : C ⧸ H) ≠ QuotientGroup.mk x₂ := by
      intro h
      apply hq₂'
      rw [← h]
      apply (QuotientGroup.eq (s := H)).mpr
      rw [hmem]
      have h1 := B.inv_mem (hexp (x₁ : S) x₁.2)
      simpa [_root_.mul_inv_rev] using h1
    have h13 : (QuotientGroup.mk x₁ : C ⧸ H) ≠ QuotientGroup.mk (x₁ * x₂) :=
      hne (by rw [hmem]; simpa using hx₂)
    have h23 : (QuotientGroup.mk x₂ : C ⧸ H) ≠ QuotientGroup.mk (x₁ * x₂) := by
      refine hne fun h => hx₁ ?_
      rw [hmem] at h
      have hK : (x₂ : S)⁻¹ * x₁ * x₂ ∈ B := by
        have h' : ((x₂⁻¹ * (x₁ * x₂) : C) : S) = (x₂ : S)⁻¹ * x₁ * x₂ := by
          rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc]
        rw [← h']
        exact h
      have hc : (x₂ : S)⁻¹ * x₁ * x₂ * x₂ = x₂ * ((x₂ : S)⁻¹ * x₁ * x₂) :=
        comm_of_mem218 hC hK x₂.2
      have hx : (x₁ : S) = (x₂ : S)⁻¹ * x₁ * x₂ := by
        calc (x₁ : S) = (x₂ : S) * ((x₂ : S)⁻¹ * x₁ * x₂) * (x₂ : S)⁻¹ := by group
          _ = ((x₂ : S)⁻¹ * x₁ * x₂) * x₂ * (x₂ : S)⁻¹ := by rw [← hc]
          _ = (x₂ : S)⁻¹ * x₁ * x₂ := by group
      rw [hx]
      exact hK
    have hval : ∀ a : C, (QuotientGroup.mk y : C ⧸ H) = QuotientGroup.mk a → σ y = σ a := by
      intro a h
      have h' : (a⁻¹ * y : C) ∈ H := (QuotientGroup.eq (s := H)).mp h.symm
      rw [hmem] at h'
      have hy : y = a * Subgroup.inclusion hBC ⟨_, h'⟩ := by
        apply Subtype.ext
        simp
      rw [hy, hσmul, hσB, add_zero]
    rcases eq_or_of_card_eq_four218 hQ h01 h02 h03 h12 h13 h23 (QuotientGroup.mk y) with
      h | h | h | h
    · left
      rw [hval 1 h]
      simpa using hσB 1
    · exact Or.inr (Or.inl (hval x₁ h))
    · exact Or.inr (Or.inr (Or.inl (hval x₂ h)))
    · exact Or.inr (Or.inr (Or.inr (by rw [hval _ h, hσmul])))
  have hρ : ∀ x : C, rhoBar221 (σ x) = σ (conjBy (hL D.ρ_mem_L) x) := fun x =>
    (sigma221_conj_ρ hL x).symm
  have huv : ∀ x : C, uvBar221 (σ x) = σ (conjBy (hL D.uv_mem_L) x) := fun x =>
    (sigma221_conj_uv hL x).symm
  refine no_invariant_plane_t221 (σ x₁) (σ x₂) hw₁ hw₂ hw₁₂ ?_ ?_ ?_ ?_
  · rw [hρ]; exact hcover _
  · rw [hρ]; exact hcover _
  · rw [huv]; exact hcover _
  · rw [huv]; exact hcover _

theorem false_of_index_four_t221 {B C S' : Subgroup S} {s : ℕ} {hs : 1 ≤ s}
    (hB : HasStrothType B (StrothTypeIndex.t221 s hs))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B) (hexp : ∀ x ∈ C, x * x ∈ B)
    (hL : hB.data.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') : False :=
  false_of_index_four_t221_of_data hB.data hBC hC hrel hexp hL hH hcS

end CFSG.CGT.Stroth77
