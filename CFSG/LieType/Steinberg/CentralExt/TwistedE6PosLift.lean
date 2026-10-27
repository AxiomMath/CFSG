module

public import CFSG.LieType.Steinberg.CentralExt.TwistedE6Torus
public import CFSG.LieType.Steinberg.CentralExt.FixedFieldFunctional
public import CFSG.LieType.Steinberg.CentralExt.PosLiftGen
public import CFSG.LieType.Steinberg.CentralExt.SpinMinusPosLift
public import CFSG.LieType.Steinberg.CentralExt.CoprimeSplit

public noncomputable section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.ExceptionalCover CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Universal
  CFSG.LieType.CurtisTits
open scoped commutatorElement

namespace CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed

attribute [local instance] TorusLift.centerCommGroup

variable {k : Type} [Field k] (θ : k →+* k)

abbrev xF {α : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α) (hfix : rho α = α)
    (c : fixedSubfield θ) : fixedGroup k θ :=
  xFixed θ hα hfix c (theta_coe θ c)

theorem xF_add {α : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α) (hfix : rho α = α)
    (c d : fixedSubfield θ) : xF θ hα hfix (c + d) = xF θ hα hfix c * xF θ hα hfix d :=
  Subtype.ext (e6Data_valid.xm_add k α c d)

theorem xPair_add (hθ : ∀ c, θ (θ c) = c) {α : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α)
    (hne : rho α ≠ α) (c d : k) :
    xPair θ hθ hα hne (c + d) = xPair θ hθ hα hne c * xPair θ hθ hα hne d := by
  refine Subtype.ext ?_
  rw [Subgroup.coe_mul, xPair_val, xPair_val, xPair_val, map_add, mul_add, e6Data_valid.xm_add,
    e6Data_valid.xm_add]
  simp only [mul_assoc]
  rw [← mul_assoc (e6Data_valid.xm k α d),
    (commute_xm_rho hα hne d ((twistSign α : k) * θ c)).eq, mul_assoc]

theorem exists_xF_eq {β : Fin (Tag.rank .F4) → ℤ} {α : Fin (Tag.rank .E6) → ℤ}
    (hα : IsRoot .E6 α) (hp : proj α = β) (hfix : rho α = α) {y : fixedGroup k θ}
    (hy : y ∈ twistedRootGroup k θ β) : ∃ c, xF θ hα hfix c = y := by
  obtain ⟨c, hc, hyc⟩ := (mem_twistedRootGroup_iff_of_fixed θ hα hp hfix y).1 hy
  exact ⟨⟨c, hc⟩, Subtype.ext hyc.symm⟩

theorem exists_xPair_eq (hθ : ∀ c, θ (θ c) = c) {β : Fin (Tag.rank .F4) → ℤ}
    {α : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α) (hp : proj α = β) (hne : rho α ≠ α)
    {y : fixedGroup k θ} (hy : y ∈ twistedRootGroup k θ β) : ∃ c, xPair θ hθ hα hne c = y := by
  obtain ⟨c, hc⟩ := (mem_twistedRootGroup_iff_of_pair θ hα hp hne y).1 hy
  exact ⟨c, Subtype.ext hc.symm⟩

theorem eq_zero_of_xF_eq_one {α : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α)
    (hfix : rho α = α) {c : fixedSubfield θ} (h : xF θ hα hfix c = 1) : c = 0 := by
  have h' : e6Data_valid.xm k α c = e6Data_valid.xm k α 0 := by
    rw [e6Data_valid.xm_zero]
    exact congrArg Subtype.val h
  exact Subtype.ext (e6Data_valid.xm_injective k hα h')

theorem eq_zero_of_xPair_eq_one (hθ : ∀ c, θ (θ c) = c) {α : Fin (Tag.rank .E6) → ℤ}
    (hα : IsRoot .E6 α) (hne : rho α ≠ α) {c : k} (h : xPair θ hθ hα hne c = 1) : c = 0 := by
  have h' : e6Data_valid.xm k α c * e6Data_valid.xm k (rho α) ((twistSign α : k) * θ c) =
      e6Data_valid.xm k α 0 * e6Data_valid.xm k (rho α) ((twistSign α : k) * θ 0) := by
    rw [map_zero, mul_zero, e6Data_valid.xm_zero, e6Data_valid.xm_zero, mul_one]
    exact congrArg Subtype.val h
  exact (xm_mul_xm_rho_inj hα hne h').1

theorem torU_conj_torU {u u' : Fin (Tag.rank .E6) → kˣ} (hu : IsSymU θ u) (hu' : IsSymU θ u') :
    torU θ u hu * torU θ u' hu' * (torU θ u hu)⁻¹ = torU θ u' hu' := by
  have h : torU θ u hu * torU θ u' hu' = torU θ u' hu' * torU θ u hu := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, torU_val, torU_val, ← map_mul, ← map_mul, mul_comm])
  rw [h, mul_inv_cancel_right]

abbrev chiF {u : Fin (Tag.rank .E6) → kˣ} (hu : IsSymU θ u) {α : Fin (Tag.rank .E6) → ℤ}
    (hfix : rho α = α) : fixedSubfield θ :=
  ⟨(rootChar k α u : k), theta_rootChar_of_fixed θ hu hfix⟩

theorem torU_conj_xF {u : Fin (Tag.rank .E6) → kˣ} (hu : IsSymU θ u)
    {α : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α) (hfix : rho α = α) (c : fixedSubfield θ) :
    torU θ u hu * xF θ hα hfix c * (torU θ u hu)⁻¹ = xF θ hα hfix (chiF θ hu hfix * c) :=
  torU_conj_xFixed θ hu hα hfix c (theta_coe θ c)

theorem torS_conj_xF (s : Fin (Tag.rank .F4) → (fixedSubfield θ)ˣ) {α : Fin (Tag.rank .E6) → ℤ}
    (hα : IsRoot .E6 α) (hfix : rho α = α) (c : fixedSubfield θ) :
    torS θ s * xF θ hα hfix c * (torS θ s)⁻¹ =
      xF θ hα hfix ((chiS θ s (proj α) : fixedSubfield θ) * c) :=
  torS_conj_xFixed θ s hα hfix c (theta_coe θ c)

section Lift

variable {θ} (hθ : ∀ c, θ (θ c) = c) {E : Type*} [Group E] (π : E →* fixedGroup k θ)

@[expose] def IsShortLift {α : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α) (hne : rho α ≠ α)
    (Y : k → E) : Prop :=
  (∀ s t, Y (s + t) = Y s * Y t) ∧ (∀ c, π (Y c) = xPair θ hθ hα hne c) ∧
    ∀ (u : Fin (Tag.rank .E6) → kˣ) (hu : IsSymU θ u) (e : E), π e = torU θ u hu →
      ∀ c, e * Y c * e⁻¹ = Y ((rootChar k α u : k) * c)

@[expose] def IsLongLift {α : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α) (hfix : rho α = α)
    (Y : fixedSubfield θ → E) : Prop :=
  (∀ s t, Y (s + t) = Y s * Y t) ∧ (∀ c, π (Y c) = xF θ hα hfix c) ∧
    ∀ (u : Fin (Tag.rank .E6) → kˣ) (hu : IsSymU θ u) (e : E), π e = torU θ u hu →
      ∀ c, e * Y c * e⁻¹ = Y (chiF θ hu hfix * c)

variable {π} (hcen : π.ker ≤ Subgroup.center E) (hπ : Function.Surjective π)

include hcen in
theorem exists_isShortLift {α : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α) (hne : rho α ≠ α)
    (h0 : TorusLift.commPairing hcen hπ (xPair_add θ hθ hα hne) = 0)
    {u₀ : Fin (Tag.rank .E6) → kˣ} (hu₀ : IsSymU θ u₀) (h₀ : (rootChar k α u₀ : k) ≠ 1) :
    ∃ Y : k → E, IsShortLift hθ π hα hne Y :=
  ⟨TorusLift.canonLift hπ (x := xPair θ hθ hα hne) (torU θ u₀ hu₀) _,
    TorusLift.canonLift_add hcen hπ (xPair_add θ hθ hα hne) h0 (torU_conj_xPair θ hθ hu₀ hα hne)
      h₀,
    TorusLift.map_canonLift hπ (xPair_add θ hθ hα hne) (torU_conj_xPair θ hθ hu₀ hα hne) h₀,
    fun _ hu _ he c => TorusLift.conj_canonLift hcen hπ (torU_conj_torU θ hu hu₀)
      (torU_conj_xPair θ hθ hu hα hne) he c⟩

include hcen in
theorem exists_isLongLift {α : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α) (hfix : rho α = α)
    (h0 : TorusLift.commPairing hcen hπ (xF_add θ hα hfix) = 0)
    {u₀ : Fin (Tag.rank .E6) → kˣ} (hu₀ : IsSymU θ u₀) (h₀ : chiF θ hu₀ hfix ≠ 1) :
    ∃ Y : fixedSubfield θ → E, IsLongLift π hα hfix Y :=
  ⟨TorusLift.canonLift hπ (x := xF θ hα hfix) (torU θ u₀ hu₀) _,
    TorusLift.canonLift_add hcen hπ (xF_add θ hα hfix) h0 (torU_conj_xF θ hu₀ hα hfix) h₀,
    TorusLift.map_canonLift hπ (xF_add θ hα hfix) (torU_conj_xF θ hu₀ hα hfix) h₀,
    fun _ hu _ he c => TorusLift.conj_canonLift hcen hπ (torU_conj_torU θ hu hu₀)
      (torU_conj_xF θ hu hα hfix) he c⟩

theorem cartanCoord_single {τ : Tag} (a j : Fin τ.rank) :
    cartanCoord (Pi.single a 1 : Fin τ.rank → ℤ) j = τ.cartan j a := by
  simp [cartanCoord, Pi.single_apply]

include hcen in
theorem commPairing_xF_eq_zero [Finite k] (hF4 : Nat.card (fixedSubfield θ) ≠ 4)
    {α : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α) (hfix : rho α = α) :
    TorusLift.commPairing hcen hπ (xF_add θ hα hfix) = 0 := by
  obtain ⟨p, _, _⟩ := TorusLift.exists_prime_charP (k := fixedSubfield θ)
  refine Pairing.pairing_eq_zero_of_units p hF4 (TorusLift.commPairing_self hcen hπ _)
    fun u hu s t => ?_
  obtain ⟨s₀, hs₀⟩ : ∃ s₀, chiS θ s₀ (proj α) = Units.mk0 u hu :=
    exists_rootChar_eq (isRoot_proj hα) _
  refine TorusLift.commPairing_smul hcen hπ (xF_add θ hα hfix) (g := torS θ s₀) (fun c => ?_) s t
  rw [torS_conj_xF, hs₀, Units.val_mk0]

include hcen in
theorem commPairing_xPair_node_eq_zero [Finite k] (hk4 : Nat.card k ≠ 4)
    {a b : Fin (Tag.rank .E6)} (hb : rhoPerm b ≠ b) (hA : Tag.cartan .E6 b a = -1)
    (hA' : Tag.cartan .E6 (rhoPerm b) a = 0) (hne : rho (Pi.single a 1) ≠ Pi.single a 1) :
    TorusLift.commPairing hcen hπ (xPair_add θ hθ (IsRoot.basis a) hne) = 0 := by
  obtain ⟨p, _, _⟩ := TorusLift.exists_prime_charP (k := k)
  refine Pairing.pairing_eq_zero_of_units p hk4 (TorusLift.commPairing_self hcen hπ _)
    fun u hu s t => ?_
  have hsym := isSymU_mulSingle_pair θ hθ hb (Units.mk0 u hu)⁻¹
  refine TorusLift.commPairing_smul hcen hπ (xPair_add θ hθ (IsRoot.basis a) hne)
    (g := torU θ _ hsym) (fun c => ?_) s t
  rw [torU_conj_xPair θ hθ hsym (IsRoot.basis a) hne c, map_mul, rootChar_mulSingle,
    rootChar_mulSingle, cartanCoord_single, cartanCoord_single, hA, hA', zpow_zero, mul_one,
    zpow_neg_one, inv_inv, Units.val_mk0]

include hcen hπ in
theorem liftsCommute_fixedNode [Finite k] (hF4 : Nat.card (fixedSubfield θ) ≠ 4)
    {a : Fin (Tag.rank .E6)} (ha : rhoPerm a = a) {j : Fin (Tag.rank .F4)}
    (hj : orbitMap a = j) : LiftsCommute π (Pi.single j 1) := by
  have hα : IsRoot .E6 (Pi.single a 1) := IsRoot.basis a
  have hfix : rho (Pi.single a 1) = Pi.single a 1 := by rw [rho_single, ha]
  have hp : proj (Pi.single a 1) = Pi.single j 1 := by rw [proj_single, hj]
  exact liftsCommute_of_commPairing_eq_zero hcen hπ (xF_add θ hα hfix)
    (fun y hy => exists_xF_eq θ hα hp hfix hy) (commPairing_xF_eq_zero hcen hπ hF4 hα hfix)

include hθ hcen hπ in
theorem liftsCommute_pairNode [Finite k] (hk4 : Nat.card k ≠ 4) {a b : Fin (Tag.rank .E6)}
    (ha : rhoPerm a ≠ a) (hb : rhoPerm b ≠ b) (hA : Tag.cartan .E6 b a = -1)
    (hA' : Tag.cartan .E6 (rhoPerm b) a = 0) {j : Fin (Tag.rank .F4)} (hj : orbitMap a = j) :
    LiftsCommute π (Pi.single j 1) := by
  have hne : rho (Pi.single a 1) ≠ Pi.single a 1 := by
    rw [rho_single]
    intro h
    have := congrFun h (rhoPerm a)
    simp [ha] at this
  have hp : proj (Pi.single a 1) = Pi.single j 1 := by rw [proj_single, hj]
  exact liftsCommute_of_commPairing_eq_zero hcen hπ (xPair_add θ hθ (IsRoot.basis a) hne)
    (fun y hy => exists_xPair_eq θ hθ (IsRoot.basis a) hp hne hy)
    (commPairing_xPair_node_eq_zero hθ hcen hπ hk4 hb hA hA' hne)

include hθ hcen hπ in
theorem liftsCommute_all [Finite k] (hk4 : Nat.card k ≠ 4)
    (hF4 : Nat.card (fixedSubfield θ) ≠ 4) {β : Fin (Tag.rank .F4) → ℤ} (hβ : IsRoot .F4 β) :
    LiftsCommute π β := by
  refine liftsCommute_of_isRoot hπ (fun j => ?_) hβ
  fin_cases j
  · exact liftsCommute_fixedNode hcen hπ hF4 (a := nd 1) (by decide) (by decide)
  · exact liftsCommute_fixedNode hcen hπ hF4 (a := nd 3) (by decide) (by decide)
  · exact liftsCommute_pairNode hθ hcen hπ hk4 (a := nd 2) (b := nd 0) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  · exact liftsCommute_pairNode hθ hcen hπ hk4 (a := nd 0) (b := nd 2) (by decide) (by decide)
      (by decide) (by decide) (by decide)

variable (π) in
open _root_.Classical in
@[expose] def XS {α : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α) (hne : rho α ≠ α) : k → E :=
  if h : ∃ Y : k → E, IsShortLift hθ π hα hne Y then h.choose else fun _ => 1

variable (π) in
open _root_.Classical in
@[expose] def XL {α : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α) (hfix : rho α = α) :
    fixedSubfield θ → E :=
  if h : ∃ Y : fixedSubfield θ → E, IsLongLift π hα hfix Y then h.choose else fun _ => 1

theorem XS_spec {α : Fin (Tag.rank .E6) → ℤ} {hα : IsRoot .E6 α} {hne : rho α ≠ α}
    (h : ∃ Y : k → E, IsShortLift hθ π hα hne Y) : IsShortLift hθ π hα hne (XS hθ π hα hne) := by
  classical
  rw [XS, dite_eq_left h]
  exact h.choose_spec

theorem XL_spec {α : Fin (Tag.rank .E6) → ℤ} {hα : IsRoot .E6 α} {hfix : rho α = α}
    (h : ∃ Y : fixedSubfield θ → E, IsLongLift π hα hfix Y) :
    IsLongLift π hα hfix (XL π hα hfix) := by
  classical
  rw [XL, dite_eq_left h]
  exact h.choose_spec

variable (θ) in
open _root_.Classical in
@[expose] def xr (β : Fin (Tag.rank .F4) → ℤ) (c : k) : fixedGroup k θ :=
  if hβ : IsRoot .F4 β then
    if hfix : rho (liftRoot β) = liftRoot β then
      xF θ (liftRoot_spec hβ).1 hfix (fixedPhi θ c)
    else xPair θ hθ (liftRoot_spec hβ).1 hfix c
  else 1

variable (π) in
open _root_.Classical in
@[expose] def Xr (β : Fin (Tag.rank .F4) → ℤ) (c : k) : E :=
  if hβ : IsRoot .F4 β then
    if hfix : rho (liftRoot β) = liftRoot β then
      XL π (liftRoot_spec hβ).1 hfix (fixedPhi θ c)
    else XS hθ π (liftRoot_spec hβ).1 hfix c
  else 1

variable (π) in
structure RootData (β : Fin (Tag.rank .F4) → ℤ) (x : k → fixedGroup k θ) (X : k → E)
    (χ : (Fin (Tag.rank .E6) → kˣ) → k) : Prop where
  par : ∀ g, g ∈ twistedRootGroup k θ β ↔ ∃ c, x c = g
  xadd : ∀ c d, x (c + d) = x c * x d
  Xadd : ∀ c d, X (c + d) = X c * X d
  lift : ∀ c, π (X c) = x c
  ker : ∀ c, x c = 1 → X c = 1
  conj : ∀ (u : Fin (Tag.rank .E6) → kˣ) (hu : IsSymU θ u) (e : E), π e = torU θ u hu → ∀ c,
    e * X c * e⁻¹ = X (χ u * c)

theorem rootData_short {α : Fin (Tag.rank .E6) → ℤ} {hα : IsRoot .E6 α} {hne : rho α ≠ α}
    {β : Fin (Tag.rank .F4) → ℤ} (hp : proj α = β) {Y : k → E}
    (hY : IsShortLift hθ π hα hne Y) :
    RootData π β (xPair θ hθ hα hne) Y (fun u => (rootChar k α u : k)) where
  par g := ⟨fun hg => exists_xPair_eq θ hθ hα hp hne hg, fun ⟨c, hc⟩ => by
    rw [← hc, ← hp]
    exact xPair_mem θ hθ hα hne c⟩
  xadd := xPair_add θ hθ hα hne
  Xadd := hY.1
  lift := hY.2.1
  ker c hc := by
    rw [eq_zero_of_xPair_eq_one θ hθ hα hne hc]
    exact TorusLift.x_zero hY.1
  conj u hu e he c := hY.2.2 u hu e he c

theorem rootData_long {α : Fin (Tag.rank .E6) → ℤ} {hα : IsRoot .E6 α} {hfix : rho α = α}
    {β : Fin (Tag.rank .F4) → ℤ} (hp : proj α = β) {Y : fixedSubfield θ → E}
    (hY : IsLongLift π hα hfix Y) :
    RootData π β (fun c => xF θ hα hfix (fixedPhi θ c)) (fun c => Y (fixedPhi θ c))
      (fun u => (rootChar k α u : k)) where
  par g := by
    constructor
    · intro hg
      obtain ⟨d, hd⟩ := exists_xF_eq θ hα hp hfix hg
      exact ⟨d, by rw [fixedPhi_coe]; exact hd⟩
    · rintro ⟨c, rfl⟩
      rw [← hp]
      exact xFixed_mem θ hα hfix _ _
  xadd c d := by rw [map_add, xF_add]
  Xadd c d := by rw [map_add, hY.1]
  lift c := hY.2.1 _
  ker c hc := by
    rw [eq_zero_of_xF_eq_one θ hα hfix hc]
    exact TorusLift.x_zero hY.1
  conj u hu e he c := by
    rw [hY.2.2 u hu e he]
    exact congrArg Y (fixedPhi_mul θ (chiF θ hu hfix) c).symm

include hcen hπ in
theorem rootData_long_of (hall : ∀ β, IsRoot .F4 β → LiftsCommute π β)
    {β : Fin (Tag.rank .F4) → ℤ} (hβ : IsRoot .F4 β) {α : Fin (Tag.rank .E6) → ℤ}
    (hα : IsRoot .E6 α) (hp : proj α = β) (hfix : rho α = α) {u₀ : Fin (Tag.rank .E6) → kˣ}
    (hu₀ : IsSymU θ u₀) (h₀ : (rootChar k α u₀ : k) ≠ 1) :
    RootData π β (fun c => xF θ hα hfix (fixedPhi θ c)) (fun c => XL π hα hfix (fixedPhi θ c))
      (fun u => (rootChar k α u : k)) := by
  subst hp
  have hY := XL_spec (exists_isLongLift hcen hπ hα hfix
    (commPairing_eq_zero_of_liftsCommute hcen hπ (xF_add θ hα hfix)
      (fun c => xFixed_mem θ hα hfix _ _) (hall _ hβ)) hu₀
    (fun h => h₀ (congrArg Subtype.val h)))
  exact rootData_long rfl hY

include hcen hπ in
theorem rootData_short_of (hall : ∀ β, IsRoot .F4 β → LiftsCommute π β)
    {β : Fin (Tag.rank .F4) → ℤ} (hβ : IsRoot .F4 β) {α : Fin (Tag.rank .E6) → ℤ}
    (hα : IsRoot .E6 α) (hp : proj α = β) (hne : rho α ≠ α) {u₀ : Fin (Tag.rank .E6) → kˣ}
    (hu₀ : IsSymU θ u₀) (h₀ : (rootChar k α u₀ : k) ≠ 1) :
    RootData π β (xPair θ hθ hα hne) (XS hθ π hα hne) (fun u => (rootChar k α u : k)) := by
  subst hp
  have hY := XS_spec hθ (exists_isShortLift hθ hcen hπ hα hne
    (commPairing_eq_zero_of_liftsCommute hcen hπ (xPair_add θ hθ hα hne)
      (fun c => xPair_mem θ hθ hα hne c) (hall _ hβ)) hu₀ h₀)
  exact rootData_short hθ rfl hY

include hcen hπ in
theorem rootData_of_isRoot (hall : ∀ β, IsRoot .F4 β → LiftsCommute π β)
    {β : Fin (Tag.rank .F4) → ℤ} (hβ : IsRoot .F4 β) {u₀ : Fin (Tag.rank .E6) → kˣ}
    (hu₀ : IsSymU θ u₀) (h₀ : (rootChar k (liftRoot β) u₀ : k) ≠ 1) :
    RootData π β (xr θ hθ β) (Xr hθ π β) (fun u => (rootChar k (liftRoot β) u : k)) := by
  by_cases hfix : rho (liftRoot β) = liftRoot β
  · have ex : xr θ hθ β = fun c => xF θ (liftRoot_spec hβ).1 hfix (fixedPhi θ c) := by
      funext c
      rw [xr, dite_eq_left hβ, dite_eq_left hfix]
    have eX : Xr hθ π β = fun c => XL π (liftRoot_spec hβ).1 hfix (fixedPhi θ c) := by
      funext c
      rw [Xr, dite_eq_left hβ, dite_eq_left hfix]
    rw [ex, eX]
    exact rootData_long_of hcen hπ hall hβ _ (liftRoot_spec hβ).2 hfix hu₀ h₀
  · have ex : xr θ hθ β = xPair θ hθ (liftRoot_spec hβ).1 hfix := by
      funext c
      rw [xr, dite_eq_left hβ, dite_eq_right hfix]
    have eX : Xr hθ π β = XS hθ π (liftRoot_spec hβ).1 hfix := by
      funext c
      rw [Xr, dite_eq_left hβ, dite_eq_right hfix]
    rw [ex, eX]
    exact rootData_short_of hθ hcen hπ hall hβ _ (liftRoot_spec hβ).2 hfix hu₀ h₀

end Lift

theorem pow_eq_one_of_mem_hHat [Finite k] (i : Fin (Tag.rank .F4)) {g : fixedGroup k θ}
    (hg : g ∈ hHat k θ i) : g ^ Nat.card kˣ = 1 := by
  have hg' : (g : e6Data_valid.minGroup k) ∈ hHatE k θ i := Subgroup.mem_subgroupOf.1 hg
  have hfix : ∀ t : fixedUnits θ, t ^ Nat.card kˣ = 1 := fun t =>
    Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact pow_card_eq_one')
  refine Subtype.ext ?_
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  fin_cases i
  · obtain ⟨t, ht⟩ := hg'
    rw [← ht, ← map_pow, hfix, map_one]
  · obtain ⟨t, ht⟩ := hg'
    rw [← ht, ← map_pow, hfix, map_one]
  · obtain ⟨t, ht⟩ := hg'
    rw [← ht, ← map_pow, pow_card_eq_one', map_one]
  · obtain ⟨t, ht⟩ := hg'
    rw [← ht, ← map_pow, pow_card_eq_one', map_one]

theorem coprime_card_torus (hθ : ∀ c, θ (θ c) = c) [Finite k] {p : ℕ} [hp : Fact p.Prime]
    [CharP k p] : p.Coprime (Nat.card (⨆ i, hHat k θ i : Subgroup (fixedGroup k θ))) := by
  have : Fintype k := Fintype.ofFinite k
  have : Finite (Module.End k (Fin e6Data.d →₀ k)) := Module.finite_of_finite k
  rw [Nat.Prime.coprime_iff_not_dvd hp.out]
  intro hdvd
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hpow : (g : fixedGroup k θ) ^ Nat.card kˣ = 1 :=
    SpinMinusClosed.pow_eq_one_of_mem_iSup (fun i h hh => pow_eq_one_of_mem_hHat θ i hh)
      (fun i j h hh h' hh' => hHat_commute θ hθ hh hh') g.2
  have hdvd' : p ∣ Nat.card kˣ := by
    rw [← hg]
    exact orderOf_dvd_of_pow_eq_one (Subtype.ext (by rw [Subgroup.coe_pow, hpow,
      Subgroup.coe_one]))
  obtain ⟨m, -, hm⟩ := FiniteField.card k p
  have hpK : p ∣ Nat.card k := by
    rw [Nat.card_eq_fintype_card, hm]
    exact dvd_pow_self p (PNat.ne_zero m)
  have hK1 : 1 ≤ Nat.card k := Nat.one_le_iff_ne_zero.2 Nat.card_pos.ne'
  rw [Nat.card_units] at hdvd'
  have h1 := Nat.dvd_sub hpK hdvd'
  rw [show Nat.card k - (Nat.card k - 1) = 1 by omega] at h1
  exact hp.out.one_lt.ne' (Nat.dvd_one.1 h1)

theorem exists_pos_ne (β : Fin (Tag.rank .F4) → ℤ) :
    ∃ b : Fin (Tag.rank .F4) → ℤ, IsRoot .F4 b ∧ 0 < ht b ∧ b ≠ β := by
  by_cases h : β = Pi.single (nf 0) 1
  · refine ⟨Pi.single (nf 1) 1, IsRoot.basis _, by decide, ?_⟩
    rw [h]
    decide
  · exact ⟨Pi.single (nf 0) 1, IsRoot.basis _, by decide, fun h' => h h'.symm⟩

theorem twistedE6_exists_section_of_torus [Finite k] (hθ : ∀ c, θ (θ c) = c) {p : ℕ}
    [Fact p.Prime] [CharP k p] (hk4 : Nat.card k ≠ 4) (hF4 : Nat.card (fixedSubfield θ) ≠ 4)
    {ι : Type*} (U : ι → Fin (Tag.rank .E6) → kˣ) (hU : ∀ j, IsSymU θ (U j))
    (hsep : ∀ a b : Fin (Tag.rank .F4) → ℤ, IsRoot .F4 a → 0 < ht a → IsRoot .F4 b → 0 < ht b →
      a ≠ b → ∃ j, rootChar k (liftRoot a) (U j) = 1 ∧ rootChar k (liftRoot b) (U j) ≠ 1)
    {E : Type*} [Group E] [Finite E] {π : E →* fixedGroup k θ} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (hpk : IsPGroup p π.ker) :
    ∃ s : fixedGroup k θ →* E, ∀ g, π (s g) = g := by
  have : Finite (Module.End k (Fin e6Data.d →₀ k)) := Module.finite_of_finite k
  have hall : ∀ β, IsRoot .F4 β → LiftsCommute π β := fun β hβ =>
    liftsCommute_all hθ hcen hπ hk4 hF4 hβ
  have hD : ∀ γ ∈ PosLift.posRoots (twistedDatum k θ),
      RootData π γ (xr θ hθ γ) (Xr hθ π γ) (fun u => (rootChar k (liftRoot γ) u : k)) := by
    intro γ hγ
    have hr : IsRoot .F4 γ := isRoot_of_mem_twistedDatum_roots θ hγ.1
    obtain ⟨b, hb, hb0, hbγ⟩ := exists_pos_ne γ
    obtain ⟨j, -, hj⟩ := hsep b γ hb hb0 hr hγ.2 hbγ
    exact rootData_of_isRoot hθ hcen hπ hall hr (hU j)
      (fun h => hj (Units.val_eq_one.1 h))
  refine PosLift.exists_section_of_posLift'
    (twistedDatum_isCTGroupDatum θ hθ (iSup_twistedDatum_rootGroup θ hθ))
    (twistedDatum_steinbergExtras θ hθ) (twistedDatum_bruhatExtras θ) rfl (p := p) (k := k)
    (D := twistedDatum k θ)
    (fun β hβ => HighestRoot.isPGroup_twistedE6_rootGroup θ
      (isRoot_of_mem_twistedDatum_roots θ hβ)) (coprime_card_torus θ hθ) hπ hcen hpk
    (x := xr θ hθ) (fun γ hγ => (hD γ hγ).par) (fun γ hγ => (hD γ hγ).xadd) (X := Xr hθ π)
    (fun γ hγ => (hD γ hγ).Xadd) (fun γ hγ => (hD γ hγ).lift) (fun γ hγ => (hD γ hγ).ker)
    (tor := fun j => TorusLift.lift hπ (torU θ (U j) (hU j)))
    (χ := fun j γ => (rootChar k (liftRoot γ) (U j) : k))
    (fun j γ hγ c => (hD γ hγ).conj (U j) (hU j) _ (TorusLift.map_lift hπ _) c) ?_
  intro a ha b hb hab
  obtain ⟨j, h1, h2⟩ := hsep a b (isRoot_of_mem_twistedDatum_roots θ ha.1) ha.2
    (isRoot_of_mem_twistedDatum_roots θ hb.1) hb.2 hab
  exact Or.inl ⟨j, by rw [h1, Units.val_one], fun h => h2 (Units.val_eq_one.1 h)⟩

theorem twistedE6_exists_section_of_pKernel [Finite k] {q : ℕ} (hq : 5 ≤ q)
    (hk : Nat.card k = q ^ 2) (hθq : ∀ c, θ c = c ^ q) {p : ℕ} [Fact p.Prime] [CharP k p]
    {E : Type*} [Group E] [Finite E] {π : E →* fixedGroup k θ} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (hpk : IsPGroup p π.ker) :
    ∃ s : fixedGroup k θ →* E, ∀ g, π (s g) = g := by
  have hθ : ∀ c, θ (θ c) = c := theta_theta_of_card hk hθq
  have hF := card_fixedSubfield_of_card θ hk hθq
  have hq25 : 25 ≤ q ^ 2 := by nlinarith
  obtain ⟨w, hw⟩ := IsCyclic.exists_generator (α := (fixedSubfield θ)ˣ)
  have hw4 : 4 ≤ orderOf w := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hw, Nat.card_units, hF]
    omega
  refine twistedE6_exists_section_of_torus θ hθ (by omega) (by omega)
    (fun s : Fin (Tag.rank .F4) → (fixedSubfield θ)ˣ => fun a => coeU θ (s (orbitMap a)))
    (fun s => isSymU_split θ s) ?_ hπ hcen hpk
  intro a b hra ha hrb hb hab
  have hli : LinIndepPair a b := by
    by_contra h
    rcases TagRoots.eq_or_eq_neg_of_not_linIndepPair hra hrb h with h | h
    · exact hab h
    · have hab' : ht a = -ht b := by
        rw [h]
        exact Finset.sum_neg_distrib (f := b) (s := Finset.univ)
      linarith
  obtain ⟨t, h1, h2⟩ := AdjointClosed.exists_sep hw4 hra hrb hli
  have hinj : Function.Injective (coeU θ) :=
    Units.map_injective (fixedSubfield θ).subtype_injective
  have hc1 : coeU θ 1 = 1 := map_one (Units.map (fixedSubfield θ).subtype.toMonoidHom)
  refine ⟨t, ?_, ?_⟩
  · rw [rootChar_split, (liftRoot_spec hra).2, show chiS θ t a = 1 from h1, hc1]
  · rw [rootChar_split, (liftRoot_spec hrb).2, ← hc1]
    exact fun h => h2 (hinj h)

theorem twistedE6_exists_section_of_central [Finite k] {q : ℕ}
    (hq : 5 ≤ q) (hk : Nat.card k = q ^ 2) (hθq : ∀ c, θ c = c ^ q) {E : Type} [Group E]
    [Finite E] {π : E →* fixedGroup k θ} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) : ∃ s : fixedGroup k θ →* E, ∀ g, π (s g) = g := by
  have hθ : ∀ c, θ (θ c) = c := theta_theta_of_card hk hθq
  obtain ⟨p, _, _⟩ := TorusLift.exists_prime_charP (k := k)
  exact CoprimeSplit.exists_section_of_parts (p := p) hπ hcen
    (fun _ _ _ _ hπ' hcen' hp' => twistedE6_exists_section_of_pKernel θ hq hk hθq hπ' hcen' hp')
    (fun _ _ _ _ hπ' hcen' hc' => twistedE6_exists_section_of_coprime hθ hπ' hcen' hc')

end CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed
