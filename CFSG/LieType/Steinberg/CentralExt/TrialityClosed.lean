module

public import CFSG.LieType.Steinberg.CentralExt.TrialityLift
public import CFSG.LieType.Steinberg.CentralExt.PosLiftGen
public import CFSG.LieType.Steinberg.CentralExt.SpinMinusPosLift
public import CFSG.LieType.Steinberg.CentralExt.CoprimeSplit

public noncomputable section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Universal
  CFSG.LieType.CurtisTits
open scoped commutatorElement

namespace CFSG.LieType.Steinberg.CentralExt.TrialityClosed

attribute [local instance] TorusLift.centerCommGroup

@[expose] def rep (γ : Fin (Tag.rank .G2) → ℤ) : Fin d4.rank → ℤ :=
  if γ = r10 then d10 else if γ = r01 then d01 else if γ = r11 then d11
  else if γ = r12 then d12 else if γ = r13 then d13 else if γ = r23 then d23 else 0

theorem rep_r10 : rep r10 = d10 := by rw [rep, ite_eq_left rfl]
theorem rep_r01 : rep r01 = d01 := by rw [rep, ite_eq_right (by decide), ite_eq_left rfl]
theorem rep_r11 : rep r11 = d11 := by rw [rep, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]
theorem rep_r12 : rep r12 = d12 := by
  rw [rep, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]
theorem rep_r13 : rep r13 = d13 := by
  rw [rep, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_left rfl]
theorem rep_r23 : rep r23 = d23 := by
  rw [rep, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_right (by decide), ite_eq_left rfl]

theorem eq_one_of_add {A G : Type*} [AddZeroClass A] [Group G] {Y : A → G}
    (h : ∀ c d, Y (c + d) = Y c * Y d) : Y 0 = 1 := by
  have h0 := h 0 0
  rw [add_zero] at h0
  have h' : Y 0 * Y 0 = Y 0 * 1 := by rw [mul_one, ← h0]
  exact mul_left_cancel h'

section Chars

variable {K : Type} [Field K] {σ : K →+* K}

local notation "σu" => Units.map (RingHom.toMonoidHom σ)

local macro "comm_group" : tactic =>
  `(tactic| (apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv, ofMul_pow,
    ofMul_zpow, ofMul_one, zero_zsmul, one_zsmul, neg_zsmul, zero_add, add_zero]
    <;> abel))

theorem chi_J1 {t : Kˣ} (ht : normU σ t = 1) :
    chi σ 1 t d10 = 1 ∧ chi σ 1 t d01 = t ^ 2 ∧ chi σ 1 t d11 = t ^ 2 ∧
      chi σ 1 t d12 = ((σu (σu t)) ^ 2)⁻¹ ∧ chi σ 1 t d13 = 1 ∧ chi σ 1 t d23 = 1 := by
  refine ⟨by rw [chi_d10, ht]; simp, by rw [chi_d01]; simp, ?_, ?_, by rw [chi_d13, ht]; simp,
    by rw [chi_d23]⟩
  · rw [chi_d11, show (1 : Kˣ) * t * (σu t)⁻¹ * (σu (σu t))⁻¹ = t ^ 2 * (normU σ t)⁻¹ by
      rw [normU]; comm_group, ht, inv_one, mul_one]
  · rw [chi_d12, show t * σu t * (σu (σu t))⁻¹ = normU σ t * ((σu (σu t)) ^ 2)⁻¹ by
      rw [normU]; comm_group, ht, one_mul]

theorem chi_J2a {w : Kˣ} (hw : σu w = w) :
    chi σ (w ^ 2) w d10 = w ∧ chi σ (w ^ 2) w d01 = 1 ∧ chi σ (w ^ 2) w d11 = w ∧
      chi σ (w ^ 2) w d12 = w ∧ chi σ (w ^ 2) w d13 = w := by
  have hN : normU σ w = w ^ 3 := by rw [normU, hw, hw]; comm_group
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [chi_d10, hN]; comm_group
  · rw [chi_d01]; comm_group
  · rw [chi_d11, hw, hw]; comm_group
  · rw [chi_d12, hw, hw]; comm_group
  · rw [chi_d13, hN]; comm_group

theorem chi_J2b {w : Kˣ} (hw : σu w = w) :
    chi σ w w d10 = w⁻¹ ∧ chi σ w w d01 = w ∧ chi σ w w d11 = 1 ∧ chi σ w w d12 = w ∧
      chi σ w w d23 = w := by
  have hN : normU σ w = w ^ 3 := by rw [normU, hw, hw]; comm_group
  refine ⟨?_, ?_, ?_, ?_, by rw [chi_d23]⟩
  · rw [chi_d10, hN]; comm_group
  · rw [chi_d01]; comm_group
  · rw [chi_d11, hw, hw]; comm_group
  · rw [chi_d12, hw, hw]; comm_group

theorem chi_J3 (w : Kˣ) :
    chi σ w 1 d01 = w⁻¹ ∧ chi σ w 1 d11 = w ∧ chi σ w 1 d12 = 1 ∧ chi σ w 1 d13 = w⁻¹ ∧
      chi σ w 1 d23 = w := by
  have hN : normU σ (1 : Kˣ) = 1 := by simp [normU]
  refine ⟨by rw [chi_d01]; simp, by rw [chi_d11]; simp, by rw [chi_d12]; simp,
    by rw [chi_d13, hN, mul_one], by rw [chi_d23]⟩

theorem chi_J4a (u : Kˣ) :
    chi σ (normU σ u) (u ^ 2) d10 = 1 ∧ chi σ (normU σ u) (u ^ 2) d13 = normU σ u ∧
      chi σ (normU σ u) (u ^ 2) d23 = normU σ u := by
  refine ⟨?_, ?_, by rw [chi_d23]⟩
  · rw [chi_d10, normU_pow_two, mul_inv_cancel]
  · rw [chi_d13, normU_pow_two]; comm_group

theorem chi_J4b (u : Kˣ) :
    chi σ (normU σ u) u d10 = normU σ u ∧ chi σ (normU σ u) u d13 = 1 ∧
      chi σ (normU σ u) u d23 = normU σ u := by
  refine ⟨?_, by rw [chi_d13, inv_mul_cancel], by rw [chi_d23]⟩
  rw [chi_d10]; comm_group

theorem chi_J5 (u : Kˣ) :
    chi σ 1 u d10 = (normU σ u)⁻¹ ∧ chi σ 1 u d13 = normU σ u ∧ chi σ 1 u d23 = 1 := by
  refine ⟨by rw [chi_d10]; simp, by rw [chi_d13]; simp, by rw [chi_d23]⟩

theorem sep_of {a b : Fin (Tag.rank .G2) → ℤ} (j : fixedUnits σ × Kˣ)
    (ha : chi σ j.1 j.2 (rep a) = 1) (hb : chi σ j.1 j.2 (rep b) ≠ 1) :
    ∃ j : fixedUnits σ × Kˣ, ((chi σ j.1 j.2 (rep a) : Kˣ) : K) = 1 ∧
      ((chi σ j.1 j.2 (rep b) : Kˣ) : K) ≠ 1 :=
  ⟨j, by rw [ha, Units.val_one], fun h => hb (Units.val_eq_one.1 h)⟩

end Chars

local notation "𝕩" => xPar (rootOperatorFamily d4)

variable {K : Type} [Field K]

theorem mem_posRoots {σ : K →+* K} {γ : Fin (Tag.rank .G2) → ℤ}
    (hγ : γ ∈ PosLift.posRoots (twistedDatum σ)) :
    γ = r10 ∨ γ = r01 ∨ γ = r11 ∨ γ = r12 ∨ γ = r13 ∨ γ = r23 := by
  have h : IsRoot .G2 γ := isRoot_of_mem_twistedDatum_roots σ hγ.1
  have hp : 0 < ht γ := hγ.2
  obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check .G2)).1 h
  clear h hγ
  revert hp
  revert k
  decide

variable {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

theorem commute_xOrbit_xPar {α β : Fin d4.rank → ℤ} (hα : IsRoot d4 α) (hβ : IsRoot d4 β)
    (h0 : α ≠ β ∧ α ≠ -β ∧ ¬IsRoot d4 (α + β))
    (h1 : rho α ≠ β ∧ rho α ≠ -β ∧ ¬IsRoot d4 (rho α + β))
    (h2 : rho (rho α) ≠ β ∧ rho (rho α) ≠ -β ∧ ¬IsRoot d4 (rho (rho α) + β)) (c d : K) :
    Commute (xOrbit σ α c) (𝕩 β d) := by
  rw [xOrbit]
  exact ((commute_xPar hα hβ h0.1 h0.2.1 h0.2.2 _ _).mul_left
    (commute_xPar (isRoot_rho hα) hβ h1.1 h1.2.1 h1.2.2 _ _)).mul_left
    (commute_xPar (isRoot_rho (isRoot_rho hα)) hβ h2.1 h2.2.1 h2.2.2 _ _)

@[expose] def xr (γ : Fin (Tag.rank .G2) → ℤ) (c : K) : twistedGroup σ :=
  if γ = r10 then xL hσ isRoot_d10 rho_d10 (phi σ c)
  else if γ = r01 then xS hσ isRoot_d01 rho_d01 c
  else if γ = r11 then xS hσ isRoot_d11 rho_d11 c
  else if γ = r12 then xS hσ isRoot_d12 rho_d12 c
  else if γ = r13 then xL hσ isRoot_d13 rho_d13 (phi σ c)
  else if γ = r23 then xL hσ isRoot_d23 rho_d23 (phi σ c)
  else 1

theorem xr_r10 : xr hσ r10 = fun c => xL hσ isRoot_d10 rho_d10 (phi σ c) := by
  funext c; rw [xr, ite_eq_left rfl]
theorem xr_r01 : xr hσ r01 = xS hσ isRoot_d01 rho_d01 := by
  funext c; rw [xr, ite_eq_right (by decide), ite_eq_left rfl]
theorem xr_r11 : xr hσ r11 = xS hσ isRoot_d11 rho_d11 := by
  funext c; rw [xr, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]
theorem xr_r12 : xr hσ r12 = xS hσ isRoot_d12 rho_d12 := by
  funext c; rw [xr, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]
theorem xr_r13 : xr hσ r13 = fun c => xL hσ isRoot_d13 rho_d13 (phi σ c) := by
  funext c
  rw [xr, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_left rfl]
theorem xr_r23 : xr hσ r23 = fun c => xL hσ isRoot_d23 rho_d23 (phi σ c) := by
  funext c
  rw [xr, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_right (by decide), ite_eq_left rfl]

variable {E : Type*} [Group E] (π : E →* twistedGroup σ)

open _root_.Classical in
@[expose] def XS {α : Fin d4.rank → ℤ} (hα : IsRoot d4 α) (hne : rho α ≠ α) : K → E :=
  if h : ∃ Y : K → E, IsShortLift hσ π hα hne Y then h.choose else fun _ => 1

open _root_.Classical in
@[expose] def XL {α : Fin d4.rank → ℤ} (hα : IsRoot d4 α) (hfix : rho α = α) :
    fixedField σ → E :=
  if h : ∃ Y : fixedField σ → E, IsLongLift hσ π hα hfix Y then h.choose else fun _ => 1

theorem XS_spec {α : Fin d4.rank → ℤ} {hα : IsRoot d4 α} {hne : rho α ≠ α}
    (h : ∃ Y : K → E, IsShortLift hσ π hα hne Y) : IsShortLift hσ π hα hne (XS hσ π hα hne) := by
  classical
  rw [XS, dite_eq_left h]
  exact h.choose_spec

theorem XL_spec {α : Fin d4.rank → ℤ} {hα : IsRoot d4 α} {hfix : rho α = α}
    (h : ∃ Y : fixedField σ → E, IsLongLift hσ π hα hfix Y) :
    IsLongLift hσ π hα hfix (XL hσ π hα hfix) := by
  classical
  rw [XL, dite_eq_left h]
  exact h.choose_spec

@[expose] def Xr (γ : Fin (Tag.rank .G2) → ℤ) (c : K) : E :=
  if γ = r10 then XL hσ π isRoot_d10 rho_d10 (phi σ c)
  else if γ = r01 then XS hσ π isRoot_d01 rho_d01 c
  else if γ = r11 then XS hσ π isRoot_d11 rho_d11 c
  else if γ = r12 then XS hσ π isRoot_d12 rho_d12 c
  else if γ = r13 then XL hσ π isRoot_d13 rho_d13 (phi σ c)
  else if γ = r23 then XL hσ π isRoot_d23 rho_d23 (phi σ c)
  else 1

theorem Xr_r10 : Xr hσ π r10 = fun c => XL hσ π isRoot_d10 rho_d10 (phi σ c) := by
  funext c; rw [Xr, ite_eq_left rfl]
theorem Xr_r01 : Xr hσ π r01 = XS hσ π isRoot_d01 rho_d01 := by
  funext c; rw [Xr, ite_eq_right (by decide), ite_eq_left rfl]
theorem Xr_r11 : Xr hσ π r11 = XS hσ π isRoot_d11 rho_d11 := by
  funext c; rw [Xr, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]
theorem Xr_r12 : Xr hσ π r12 = XS hσ π isRoot_d12 rho_d12 := by
  funext c; rw [Xr, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]
theorem Xr_r13 : Xr hσ π r13 = fun c => XL hσ π isRoot_d13 rho_d13 (phi σ c) := by
  funext c
  rw [Xr, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_left rfl]
theorem Xr_r23 : Xr hσ π r23 = fun c => XL hσ π isRoot_d23 rho_d23 (phi σ c) := by
  funext c
  rw [Xr, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_right (by decide), ite_eq_left rfl]

structure RootData (γ : Fin (Tag.rank .G2) → ℤ) (x : K → twistedGroup σ) (X : K → E)
    (χ : fixedUnits σ × Kˣ → K) : Prop where
  par : ∀ g, g ∈ twistedRootGroup σ γ ↔ ∃ c, x c = g
  xadd : ∀ c d, x (c + d) = x c * x d
  Xadd : ∀ c d, X (c + d) = X c * X d
  lift : ∀ c, π (X c) = x c
  ker : ∀ c, x c = 1 → X c = 1
  conj : ∀ (j : fixedUnits σ × Kˣ) (e : E), π e = tor hσ j.1 j.2 → ∀ c,
    e * X c * e⁻¹ = X (χ j * c)

theorem rootData_short {α : Fin d4.rank → ℤ} {hα : IsRoot d4 α} {hne : rho α ≠ α}
    {γ : Fin (Tag.rank .G2) → ℤ} (hp : proj α = γ) {Y : K → E}
    (hY : IsShortLift hσ π hα hne Y) :
    RootData hσ π γ (xS hσ hα hne) Y (fun j => (chi σ j.1 j.2 α : K)) where
  par := mem_iff_xS hσ hα hne hp
  xadd := xS_add hσ hα hne
  Xadd := hY.1
  lift := hY.2.1
  ker c hc := by
    rw [xS_eq_one hσ hα hne hc]
    exact eq_one_of_add hY.1
  conj j e he c := hY.2.2 j.1 j.2 e he c

theorem rootData_long {α : Fin d4.rank → ℤ} {hα : IsRoot d4 α} {hfix : rho α = α}
    {γ : Fin (Tag.rank .G2) → ℤ} (hp : proj α = γ) {Y : fixedField σ → E}
    (hY : IsLongLift hσ π hα hfix Y) :
    RootData hσ π γ (fun c => xL hσ hα hfix (phi σ c)) (fun c => Y (phi σ c))
      (fun j => (chi σ j.1 j.2 α : K)) where
  par g := by
    rw [mem_iff_xL hσ hα hfix hp]
    exact ⟨fun ⟨c, hc⟩ => ⟨c, by rw [phi_coe, hc]⟩, fun ⟨c, hc⟩ => ⟨phi σ c, hc⟩⟩
  xadd c d := by rw [map_add, xL_add]
  Xadd c d := by rw [map_add, hY.1]
  lift c := hY.2.1 _
  ker c hc := by
    have h0 : phi σ c = 0 := xL_eq_one hσ hα hfix hc
    simp only [h0, eq_one_of_add hY.1]
  conj j e he c := by
    rw [hY.2.2 j.1 j.2 e he, ← phi_mul, chiF_val]

theorem pow_eq_one_of_mem_hHat [Finite K] (i : Fin (Tag.rank .G2)) {g : twistedGroup σ}
    (hg : g ∈ hHat σ i) : g ^ Nat.card Kˣ = 1 := by
  have : Fintype Kˣ := Fintype.ofFinite _
  have hg' : (g : adjointGroup d4 K) ∈ hHatE σ i := Subgroup.mem_subgroupOf.1 hg
  refine Subtype.ext ?_
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  match i with
  | ⟨0, _⟩ =>
    obtain ⟨s, hs⟩ := hg'
    rw [← hs, ← map_pow, Nat.card_eq_fintype_card]
    have h1 : s ^ Fintype.card Kˣ = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow]
      exact pow_card_eq_one)
    rw [h1, map_one]
  | ⟨1, _⟩ =>
    obtain ⟨t, ht⟩ := hg'
    rw [← ht, ← map_pow, Nat.card_eq_fintype_card, pow_card_eq_one, map_one]

section Sep

variable {π}

theorem conj_mem_of_commute {X : (Fin (Tag.rank .G2) → ℤ) → K → E}
    {a b : Fin (Tag.rank .G2) → ℤ} (hb : b ∈ PosLift.posRoots (twistedDatum σ))
    (hcomm : ∀ t c, X a t * X b c = X b c * X a t) (t c : K) :
    X a t * X b c * (X a t)⁻¹ ∈ ⨆ (ε : Fin (twistedDatum σ).rank → ℤ)
      (_ : ε ∈ PosLift.posRoots (twistedDatum σ) ∧
        (ε = b ∨ ∃ p : ℕ × ℕ, 0 < p.1 ∧ 0 < p.2 ∧ ε = p.1 • a + p.2 • b)), chevRoot X ε := by
  rw [hcomm, mul_inv_cancel_right]
  exact Subgroup.mem_iSup_of_mem b (Subgroup.mem_iSup_of_mem ⟨hb, Or.inl rfl⟩
    (xh_mem_chevRoot b c))

end Sep

section Main


include hσ in
theorem coprime_card_torus [Finite K] {p : ℕ} [hp : Fact p.Prime] [CharP K p] :
    p.Coprime (Nat.card (⨆ i, hHat σ i : Subgroup (twistedGroup σ))) := by
  have : Fintype K := Fintype.ofFinite K
  rw [Nat.Prime.coprime_iff_not_dvd hp.out]
  intro hdvd
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hpow : (g : twistedGroup σ) ^ Nat.card Kˣ = 1 :=
    SpinMinusClosed.pow_eq_one_of_mem_iSup (fun i h hh => pow_eq_one_of_mem_hHat i hh)
      (fun i j h hh h' hh' => (twistedDatum_steinbergExtras σ hσ).torus_commute i j h hh h' hh')
      g.2
  have hdvd' : p ∣ Nat.card Kˣ := by
    rw [← hg]
    exact orderOf_dvd_of_pow_eq_one (Subtype.ext (by rw [Subgroup.coe_pow, hpow,
      Subgroup.coe_one]))
  obtain ⟨m, -, hm⟩ := FiniteField.card K p
  have hpK : p ∣ Nat.card K := by
    rw [Nat.card_eq_fintype_card, hm]
    exact dvd_pow_self p (PNat.ne_zero m)
  have hK1 : 1 ≤ Nat.card K := Nat.one_le_iff_ne_zero.2 Nat.card_pos.ne'
  rw [Nat.card_units] at hdvd'
  have h1 := Nat.dvd_sub hpK hdvd'
  rw [show Nat.card K - (Nat.card K - 1) = 1 by omega] at h1
  exact hp.out.one_lt.ne' (Nat.dvd_one.1 h1)


theorem triality_exists_section_of_pKernel [Finite K] {q : ℕ} (hq : 3 ≤ q)
    (hK : Nat.card K = q ^ 3) (hσq : ∀ c, σ c = c ^ q) {p : ℕ} [Fact p.Prime] [CharP K p]
    {E : Type*} [Group E] [Finite E] {π : E →* twistedGroup σ} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (hpk : IsPGroup p π.ker) :
    ∃ s : twistedGroup σ →* E, ∀ g, π (s g) = g := by
  have hσ : ∀ c, σ (σ (σ c)) = c := sigma_three_of_card hK hσq
  obtain ⟨u, hu⟩ := exists_normU_ne_one hK hσq hq
  obtain ⟨t₁, ht₁, ht₁2⟩ := exists_normU_eq_one hK hσq (by omega)
  have hK4 : Nat.card K ≠ 4 := by
    rw [hK]
    intro h
    have : q ≤ 1 := by
      by_contra h'
      have : 2 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left (by omega) 3
      omega
    omega
  have hK9 : Nat.card K ≠ 9 := by
    rw [hK]
    intro h
    have : 3 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
    omega
  have hσinj : ∀ x : Kˣ, Units.map σ.toMonoidHom (Units.map σ.toMonoidHom x) = 1 → x = 1 :=
    fun x h => Units.ext (σ.injective (σ.injective (by
      have := congrArg (fun y : Kˣ => (y : K)) h
      simpa using this)))
  set w : fixedUnits σ := nu hσ u with hw
  have hwσ : Units.map σ.toMonoidHom (w : Kˣ) = w :=
    Units.ext ((mem_fixedUnits σ).1 w.2)
  have hw1 : (w : Kˣ) ≠ 1 := hu
  have hJ1 := chi_J1 (σ := σ) ht₁
  have hJ2a := chi_J2a (σ := σ) hwσ
  have hJ2b := chi_J2b (σ := σ) hwσ
  have hJ3 := chi_J3 (σ := σ) (w : Kˣ)
  have hJ4a := chi_J4a (σ := σ) u
  have hJ4b := chi_J4b (σ := σ) u
  have hJ5 := chi_J5 (σ := σ) u
  have h12 : ((Units.map σ.toMonoidHom (Units.map σ.toMonoidHom t₁)) ^ 2)⁻¹ ≠ 1 := by
    rw [inv_ne_one, ← map_pow, ← map_pow]
    exact fun h => ht₁2 (hσinj _ h)
  have hS01 := XS_spec hσ π (exists_isShortLift hσ hcen hπ isRoot_d01 rho_d01
    (commPairing_xS_eq_zero hσ hcen hπ hK4 hK9 isRoot_d01 rho_d01 fun v =>
      ⟨1, v, chi_d01_sq v⟩) 1 t₁ (by
        show ((chi σ 1 t₁ d01 : Kˣ) : K) ≠ 1
        rw [hJ1.2.1]; exact fun h => ht₁2 (Units.val_eq_one.1 h)))
  have hS11 := XS_spec hσ π (exists_isShortLift hσ hcen hπ isRoot_d11 rho_d11
    (commPairing_xS_eq_zero hσ hcen hπ hK4 hK9 isRoot_d11 rho_d11 fun v =>
      ⟨nu hσ v, v, chi_d11_sq v⟩) 1 t₁ (by
        show ((chi σ 1 t₁ d11 : Kˣ) : K) ≠ 1
        rw [hJ1.2.2.1]; exact fun h => ht₁2 (Units.val_eq_one.1 h)))
  have hS12 := XS_spec hσ π (exists_isShortLift hσ hcen hπ isRoot_d12 rho_d12
    (commPairing_xS_eq_zero hσ hcen hπ hK4 hK9 isRoot_d12 rho_d12 fun v =>
      ⟨1, v * Units.map σ.toMonoidHom (Units.map σ.toMonoidHom v), chi_d12_sq hσ v⟩) 1 t₁ (by
        show ((chi σ 1 t₁ d12 : Kˣ) : K) ≠ 1
        rw [hJ1.2.2.2.1]; exact fun h => h12 (Units.val_eq_one.1 h)))
  have hL10 := XL_spec hσ π (exists_isLongLift hσ hcen hπ isRoot_d10 rho_d10
    (commPairing_xL_d10_eq_zero hσ hcen hπ hu) 1 u (by
      show chi σ 1 u d10 ≠ 1
      rw [hJ5.1]; exact inv_ne_one.2 hu))
  have hL13 := XL_spec hσ π (exists_isLongLift hσ hcen hπ isRoot_d13 rho_d13
    (commPairing_xL_d13_eq_zero hσ hcen hπ hu) 1 u (by
      show chi σ 1 u d13 ≠ 1
      rw [hJ5.2.1]; exact hu))
  have hL23 := XL_spec hσ π (exists_isLongLift hσ hcen hπ isRoot_d23 rho_d23
    (commPairing_xL_d23_eq_zero hσ hcen hπ hu) w 1 (by rw [chi_d23]; exact hw1))
  have hD : ∀ γ ∈ PosLift.posRoots (twistedDatum σ), RootData hσ π γ (xr hσ γ) (Xr hσ π γ)
      (fun j => (chi σ j.1 j.2 (rep γ) : K)) := by
    intro γ hγ
    rcases mem_posRoots hγ with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [xr_r10, Xr_r10, rep_r10]; exact rootData_long hσ π proj_d10 hL10
    · rw [xr_r01, Xr_r01, rep_r01]; exact rootData_short hσ π proj_d01 hS01
    · rw [xr_r11, Xr_r11, rep_r11]; exact rootData_short hσ π proj_d11 hS11
    · rw [xr_r12, Xr_r12, rep_r12]; exact rootData_short hσ π proj_d12 hS12
    · rw [xr_r13, Xr_r13, rep_r13]; exact rootData_long hσ π proj_d13 hL13
    · rw [xr_r23, Xr_r23, rep_r23]; exact rootData_long hσ π proj_d23 hL23
  have hrev : ∀ {a b : Fin (Tag.rank .G2) → ℤ} (ha : a ∈ PosLift.posRoots (twistedDatum σ))
      (hb : b ∈ PosLift.posRoots (twistedDatum σ))
      (hxy : ∀ s t, xr hσ a s * xr hσ b t = xr hσ b t * xr hσ a s)
      (j : fixedUnits σ × Kˣ) (hja : chi σ j.1 j.2 (rep a) ≠ 1)
      (hjb : chi σ j.1 j.2 (rep b) = 1),
      ∀ s t, Xr hσ π a s * Xr hσ π b t = Xr hσ π b t * Xr hσ π a s := by
    intro a b ha hb hxy j hja hjb s t
    refine PosLift.commute_of_rev_sep hcen (hD a ha).Xadd (hD a ha).lift (hD b hb).lift hxy
      (e := TorusLift.lift hπ (tor hσ j.1 j.2)) (fun h => hja (Units.val_eq_one.1 h))
      (fun c => (hD a ha).conj j _ (TorusLift.map_lift hπ _) c) (fun c => ?_) s t
    rw [(hD b hb).conj j _ (TorusLift.map_lift hπ _) c, hjb, Units.val_one, one_mul]
  refine PosLift.exists_section_of_posLift' (twistedDatum_isCTGroupDatum σ hσ)
    (twistedDatum_steinbergExtras σ hσ) (twistedDatum_bruhatExtras σ) rfl (p := p) (k := K)
    (D := twistedDatum σ)
    (fun β hβ => HighestRoot.isPGroup_twistedD4_rootGroup σ hσ
      (isRoot_of_mem_twistedDatum_roots σ hβ)) (coprime_card_torus hσ) hπ hcen hpk
    (x := xr hσ) (fun γ hγ => (hD γ hγ).par) (fun γ hγ => (hD γ hγ).xadd) (X := Xr hσ π)
    (fun γ hγ => (hD γ hγ).Xadd) (fun γ hγ => (hD γ hγ).lift) (fun γ hγ => (hD γ hγ).ker)
    (tor := fun j : fixedUnits σ × Kˣ => TorusLift.lift hπ (tor hσ j.1 j.2))
    (χ := fun j γ => (chi σ j.1 j.2 (rep γ) : K))
    (fun j γ hγ c => (hD γ hγ).conj j _ (TorusLift.map_lift hπ _) c) ?_
  intro a ha b hb hab
  rcases mem_posRoots ha with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases mem_posRoots hb with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact absurd rfl hab
    | skip
  · exact Or.inl (sep_of (1, t₁) (by rw [rep_r10]; exact hJ1.1)
      (by rw [rep_r01]; show chi σ 1 t₁ d01 ≠ 1; rw [hJ1.2.1]; exact ht₁2))
  · exact Or.inl (sep_of (1, t₁) (by rw [rep_r10]; exact hJ1.1)
      (by rw [rep_r11]; show chi σ 1 t₁ d11 ≠ 1; rw [hJ1.2.2.1]; exact ht₁2))
  · exact Or.inl (sep_of (1, t₁) (by rw [rep_r10]; exact hJ1.1)
      (by rw [rep_r12]; show chi σ 1 t₁ d12 ≠ 1; rw [hJ1.2.2.2.1]; exact h12))
  · exact Or.inl (sep_of (w, u ^ 2) (by rw [rep_r10]; exact hJ4a.1)
      (by rw [rep_r13]; show chi σ (normU σ u) (u ^ 2) d13 ≠ 1; rw [hJ4a.2.1]; exact hu))
  · exact Or.inl (sep_of (w, u ^ 2) (by rw [rep_r10]; exact hJ4a.1)
      (by rw [rep_r23]; show chi σ (normU σ u) (u ^ 2) d23 ≠ 1; rw [hJ4a.2.2]; exact hu))
  · exact Or.inl (sep_of (w ^ 2, (w : Kˣ)) (by rw [rep_r01]; exact hJ2a.2.1)
      (by rw [rep_r10]; show chi σ ((w : Kˣ) ^ 2) (w : Kˣ) d10 ≠ 1; rw [hJ2a.1]; exact hw1))
  · exact Or.inl (sep_of (w ^ 2, (w : Kˣ)) (by rw [rep_r01]; exact hJ2a.2.1)
      (by rw [rep_r11]; show chi σ ((w : Kˣ) ^ 2) (w : Kˣ) d11 ≠ 1; rw [hJ2a.2.2.1]; exact hw1))
  · exact Or.inl (sep_of (w ^ 2, (w : Kˣ)) (by rw [rep_r01]; exact hJ2a.2.1)
      (by rw [rep_r12]; show chi σ ((w : Kˣ) ^ 2) (w : Kˣ) d12 ≠ 1; rw [hJ2a.2.2.2.1]; exact hw1))
  · exact Or.inl (sep_of (w ^ 2, (w : Kˣ)) (by rw [rep_r01]; exact hJ2a.2.1)
      (by rw [rep_r13]; show chi σ ((w : Kˣ) ^ 2) (w : Kˣ) d13 ≠ 1; rw [hJ2a.2.2.2.2]; exact hw1))
  · refine Or.inr (conj_mem_of_commute hb (hrev ha hb (fun s t => ?_) (1, t₁)
      (by rw [rep_r01]; show chi σ 1 t₁ d01 ≠ 1; rw [hJ1.2.1]; exact ht₁2) (by rw [rep_r23]; exact hJ1.2.2.2.2.2)))
    rw [xr_r01, xr_r23]
    exact Subtype.ext (commute_xOrbit_xPar isRoot_d01 isRoot_d23
      ⟨by decide, by decide, not_isRoot_of_cert (by decide)⟩
      ⟨by decide, by decide, not_isRoot_of_cert (by decide)⟩
      ⟨by decide, by decide, not_isRoot_of_cert (by decide)⟩ s _).eq
  · exact Or.inl (sep_of (w, (w : Kˣ)) (by rw [rep_r11]; exact hJ2b.2.2.1)
      (by rw [rep_r10]; show chi σ (w : Kˣ) (w : Kˣ) d10 ≠ 1; rw [hJ2b.1]; exact inv_ne_one.2 hw1))
  · exact Or.inl (sep_of (w, (w : Kˣ)) (by rw [rep_r11]; exact hJ2b.2.2.1)
      (by rw [rep_r01]; show chi σ (w : Kˣ) (w : Kˣ) d01 ≠ 1; rw [hJ2b.2.1]; exact hw1))
  · exact Or.inl (sep_of (w, (w : Kˣ)) (by rw [rep_r11]; exact hJ2b.2.2.1)
      (by rw [rep_r12]; show chi σ (w : Kˣ) (w : Kˣ) d12 ≠ 1; rw [hJ2b.2.2.2.1]; exact hw1))
  · refine Or.inr (conj_mem_of_commute hb (hrev ha hb (fun s t => ?_) (1, t₁)
      (by rw [rep_r11]; show chi σ 1 t₁ d11 ≠ 1; rw [hJ1.2.2.1]; exact ht₁2) (by rw [rep_r13]; exact hJ1.2.2.2.2.1)))
    rw [xr_r11, xr_r13]
    exact Subtype.ext (commute_xOrbit_xPar isRoot_d11 isRoot_d13
      ⟨by decide, by decide, not_isRoot_of_cert (by decide)⟩
      ⟨by decide, by decide, not_isRoot_of_cert (by decide)⟩
      ⟨by decide, by decide, not_isRoot_of_cert (by decide)⟩ s _).eq
  · exact Or.inl (sep_of (w, (w : Kˣ)) (by rw [rep_r11]; exact hJ2b.2.2.1)
      (by rw [rep_r23]; show chi σ (w : Kˣ) (w : Kˣ) d23 ≠ 1; rw [hJ2b.2.2.2.2]; exact hw1))
  · refine Or.inr (conj_mem_of_commute hb (hrev ha hb (fun s t => ?_) (1, t₁)
      (by rw [rep_r12]; show chi σ 1 t₁ d12 ≠ 1; rw [hJ1.2.2.2.1]; exact h12) (by rw [rep_r10]; exact hJ1.1)))
    rw [xr_r12, xr_r10]
    exact Subtype.ext (commute_xOrbit_xPar isRoot_d12 isRoot_d10
      ⟨by decide, by decide, not_isRoot_of_cert (by decide)⟩
      ⟨by decide, by decide, not_isRoot_of_cert (by decide)⟩
      ⟨by decide, by decide, not_isRoot_of_cert (by decide)⟩ s _).eq
  · exact Or.inl (sep_of (w, 1) (by rw [rep_r12]; exact hJ3.2.2.1)
      (by rw [rep_r01]; show chi σ (w : Kˣ) 1 d01 ≠ 1; rw [hJ3.1]; exact inv_ne_one.2 hw1))
  · exact Or.inl (sep_of (w, 1) (by rw [rep_r12]; exact hJ3.2.2.1)
      (by rw [rep_r11]; show chi σ (w : Kˣ) 1 d11 ≠ 1; rw [hJ3.2.1]; exact hw1))
  · exact Or.inl (sep_of (w, 1) (by rw [rep_r12]; exact hJ3.2.2.1)
      (by rw [rep_r13]; show chi σ (w : Kˣ) 1 d13 ≠ 1; rw [hJ3.2.2.2.1]; exact inv_ne_one.2 hw1))
  · exact Or.inl (sep_of (w, 1) (by rw [rep_r12]; exact hJ3.2.2.1)
      (by rw [rep_r23]; show chi σ (w : Kˣ) 1 d23 ≠ 1; rw [hJ3.2.2.2.2]; exact hw1))
  · exact Or.inl (sep_of (w, u) (by rw [rep_r13]; exact hJ4b.2.1)
      (by rw [rep_r10]; show chi σ (normU σ u) u d10 ≠ 1; rw [hJ4b.1]; exact hu))
  · exact Or.inl (sep_of (1, t₁) (by rw [rep_r13]; exact hJ1.2.2.2.2.1)
      (by rw [rep_r01]; show chi σ 1 t₁ d01 ≠ 1; rw [hJ1.2.1]; exact ht₁2))
  · exact Or.inl (sep_of (1, t₁) (by rw [rep_r13]; exact hJ1.2.2.2.2.1)
      (by rw [rep_r11]; show chi σ 1 t₁ d11 ≠ 1; rw [hJ1.2.2.1]; exact ht₁2))
  · exact Or.inl (sep_of (1, t₁) (by rw [rep_r13]; exact hJ1.2.2.2.2.1)
      (by rw [rep_r12]; show chi σ 1 t₁ d12 ≠ 1; rw [hJ1.2.2.2.1]; exact h12))
  · exact Or.inl (sep_of (w, u) (by rw [rep_r13]; exact hJ4b.2.1)
      (by rw [rep_r23]; show chi σ (normU σ u) u d23 ≠ 1; rw [hJ4b.2.2]; exact hu))
  · exact Or.inl (sep_of (1, u) (by rw [rep_r23]; exact hJ5.2.2)
      (by rw [rep_r10]; show chi σ 1 u d10 ≠ 1; rw [hJ5.1]; exact inv_ne_one.2 hu))
  · exact Or.inl (sep_of (1, t₁) (by rw [rep_r23]; exact hJ1.2.2.2.2.2)
      (by rw [rep_r01]; show chi σ 1 t₁ d01 ≠ 1; rw [hJ1.2.1]; exact ht₁2))
  · exact Or.inl (sep_of (1, t₁) (by rw [rep_r23]; exact hJ1.2.2.2.2.2)
      (by rw [rep_r11]; show chi σ 1 t₁ d11 ≠ 1; rw [hJ1.2.2.1]; exact ht₁2))
  · exact Or.inl (sep_of (1, t₁) (by rw [rep_r23]; exact hJ1.2.2.2.2.2)
      (by rw [rep_r12]; show chi σ 1 t₁ d12 ≠ 1; rw [hJ1.2.2.2.1]; exact h12))
  · exact Or.inl (sep_of (1, u) (by rw [rep_r23]; exact hJ5.2.2)
      (by rw [rep_r13]; show chi σ 1 u d13 ≠ 1; rw [hJ5.2.1]; exact hu))

theorem triality_exists_section_of_central [Finite K] {q : ℕ} (hq : 3 ≤ q)
    (hK : Nat.card K = q ^ 3) (hσq : ∀ c, σ c = c ^ q) {E : Type} [Group E] [Finite E]
    {π : E →* twistedGroup σ} (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) :
    ∃ s : twistedGroup σ →* E, ∀ g, π (s g) = g := by
  have hσ : ∀ c, σ (σ (σ c)) = c := sigma_three_of_card hK hσq
  obtain ⟨p, _, _⟩ := TorusLift.exists_prime_charP (k := K)
  exact CoprimeSplit.exists_section_of_parts (p := p) hπ hcen
    (fun _ _ _ _ hπ' hcen' hp' => triality_exists_section_of_pKernel hq hK hσq hπ' hcen' hp')
    (fun _ _ _ _ hπ' hcen' hc' => triality_exists_section_of_coprime hσ hπ' hcen' hc')

end Main

end CFSG.LieType.Steinberg.CentralExt.TrialityClosed
