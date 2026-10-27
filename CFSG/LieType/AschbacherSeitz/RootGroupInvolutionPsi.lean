module

public import CFSG.LieType.AschbacherSeitz.RootGroupInvolution
public import CFSG.GroupTheory.CommutingConjugatePair
public import CFSG.LieType.Steinberg.CentralExt.MinusculeCenter
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6Center

public section

namespace CFSG.LieType.AschbacherSeitz

open CFSG CFSG.Open CFSG.StandardType CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Universal CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.Steinberg.TwistedE6
open CFSG.LieType.Steinberg.Exceptional

theorem inf_center_eq_bot_of_isPGroup_two_of_oddCenter {U : Type} [Group U] [Finite U]
    {X : Subgroup U} (hX : IsPGroup 2 X) (hodd : Odd (Nat.card (Subgroup.center U))) :
    X ⊓ Subgroup.center U = ⊥ :=
  CFSG.GroupTheory.inf_eq_bot_of_isPGroup_two_of_odd hX hodd

private theorem adjDatum_rootGroup_sq_one
    {τ : Tag} {F : RootOperatorFamily τ} {K : Type} [Field K] [CharP K 2]
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ∀ x ∈ (adjDatum F K).rootGroup γ, x * x = 1 := by
  intro x hx
  obtain ⟨c, rfl⟩ := (mem_rootGroup_iff (F := F) hγ x).1 hx
  rw [← xPar_add (F := F), CharTwo.add_self_eq_zero, xPar_zero]

private theorem minDatum_rootGroup_sq_one
    {τ : Tag} {D : MinData τ} {hV : D.Valid} {hA : TauCeti.IsFiniteType τ.cartan}
    {k : Type} [Field k] [CharP k 2]
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ∀ x ∈ (hV.minDatum hA k).rootGroup γ, x * x = 1 := by
  intro x hx
  obtain ⟨c, rfl⟩ := (hV.mem_rootGroup (k := k)).1 hx
  rw [← hV.xm_add k, CharTwo.add_self_eq_zero, hV.xm_zero k]

private theorem twistedE6_rootGroup_sq_one (f : ℕ) (hf : 1 ≤ f)
    {γ : Fin (twistedE6Datum 2 f).rank → ℤ}
    (hγ : γ ∈ (twistedE6Datum 2 f).roots) :
    ∀ x ∈ (twistedE6Datum 2 f).rootGroup γ, x * x = 1 := by
  let K := GaloisField 2 (2 * f)
  let θ : K →+* K := frobQ 2 f
  have hγ' : IsRoot Tag.F4 γ :=
    isRoot_of_mem_twistedDatum_roots (k := K) (θ := θ) hγ
  intro x hx
  change x ∈ twistedRootGroup K θ γ at hx
  obtain ⟨α, hα, hp⟩ := exists_proj_eq hγ'
  by_cases hfix : rho α = α
  · obtain ⟨c, _, hxc⟩ :=
      (mem_twistedRootGroup_iff_of_fixed θ hα hp hfix x).1 hx
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, hxc]
    rw [← e6Data_valid.xm_add, CharTwo.add_self_eq_zero, e6Data_valid.xm_zero]
    rfl
  · obtain ⟨c, hxc⟩ := (mem_twistedRootGroup_iff_of_pair θ hα hp hfix x).1 hx
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, hxc]
    set a : e6Data_valid.minGroup K := e6Data_valid.xm K α c
    set b : e6Data_valid.minGroup K :=
      e6Data_valid.xm K (rho α) ((twistSign α : K) * θ c)
    have ha : a * a = 1 := by
      dsimp only [a]
      rw [← e6Data_valid.xm_add, CharTwo.add_self_eq_zero, e6Data_valid.xm_zero]
    have hb : b * b = 1 := by
      dsimp only [b]
      rw [← e6Data_valid.xm_add, CharTwo.add_self_eq_zero, e6Data_valid.xm_zero]
    have hcomm : Commute a b := commute_xm_rho hα hfix c _
    calc (a * b) * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hcomm.eq]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha, hb, mul_one]

private theorem odd_center_adjoint (τ : Tag) (K : Type) [Field K] [Finite K] :
    Odd (Nat.card (Subgroup.center (adjointGroup τ K))) := by
  rw [CFSG.LieType.Chevalley.center_adjointGroup_eq_bot, Subgroup.card_bot]
  norm_num

private theorem odd_center_e6 (f : ℕ) :
    Odd (Nat.card (Subgroup.center (e6Data_valid.minGroup (GaloisField 2 f)))) := by
  rw [(CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e6
    (k := GaloisField 2 f)).1]
  have hdvd : Nat.gcd 3 (Nat.card (GaloisField 2 f) - 1) ∣ 3 :=
    Nat.gcd_dvd_left 3 _
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h | h
  · rw [h]; norm_num
  · rw [h]; norm_num

private theorem odd_center_e7 (f : ℕ) (hf : 1 ≤ f) :
    Odd (Nat.card (Subgroup.center (e7Data_valid.minGroup (GaloisField 2 f)))) := by
  rw [(CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e7
    (k := GaloisField 2 f)).1]
  have hcard : Nat.card (GaloisField 2 f) = 2 ^ f :=
    GaloisField.card 2 f (by omega)
  have hodd : Odd (Nat.card (GaloisField 2 f) - 1) := by
    rw [hcard]
    exact Nat.Even.sub_odd Nat.one_le_two_pow
      (Even.pow_of_ne_zero even_two (by omega)) odd_one
  have hgcd : Nat.gcd 2 (Nat.card (GaloisField 2 f) - 1) = 1 := by
    rw [← Nat.coprime_iff_gcd_eq_one]
    exact Nat.coprime_two_left.mpr hodd
  rw [hgcd]
  norm_num

private theorem odd_center_twistedE6 (f : ℕ) (hf : 1 ≤ f) :
    Odd (Nat.card (Subgroup.center (twistedE6Group 2 f))) := by
  let K := GaloisField 2 (2 * f)
  let q := 2 ^ f
  have hk : Nat.card K = q ^ 2 := by
    dsimp only [K, q]
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  have hθq : ∀ c : K, frobQ 2 f c = c ^ q := by
    intro c
    exact frobQ_apply (p := 2) (f := f) c
  rw [(CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.card_center_fixedGroup
    (k := K) (θ := frobQ 2 f) (q := q) hk hθq).1]
  have hdvd : Nat.gcd 3 (q + 1) ∣ 3 := Nat.gcd_dvd_left 3 _
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h | h
  · rw [h]; norm_num
  · rw [h]; norm_num

theorem rootGroupInvolutionPsi_F4 (n f : ℕ) (hf : 1 ≤ f) {G : Type} [Group G]
    (ψ : (ggU .F4 n f).K →* G) (hker : ψ.ker ≤ Subgroup.center (ggU .F4 n f).K)
    {γ : Fin (ggU .F4 n f).D.rank → ℤ} (hγ : γ ∈ (ggU .F4 n f).D.roots)
    (hclass : GGRootClass (ggU .F4 n f).D .F4 γ) (u : (ggU .F4 n f).K) :
    ∃ r ∈ ggRootSub (ggU .F4 n f).D ψ γ u, orderOf r = 2 := by
  change ∃ r ∈ ggRootSub (adjDatum (rootOperatorFamily Tag.F4) (GaloisField 2 f)) ψ γ u,
    orderOf r = 2
  change γ ∈ (adjDatum (rootOperatorFamily Tag.F4) (GaloisField 2 f)).roots at hγ
  change ψ.ker ≤ Subgroup.center (adjointGroup Tag.F4 (GaloisField 2 f)) at hker
  have hγ' : IsRoot Tag.F4 γ :=
    (mem_adjDatum_roots (F := rootOperatorFamily Tag.F4) (K := GaloisField 2 f)).1 hγ
  have hsq : ∀ x ∈ (adjDatum (rootOperatorFamily Tag.F4) (GaloisField 2 f)).rootGroup γ,
      x * x = 1 :=
    adjDatum_rootGroup_sq_one (F := rootOperatorFamily Tag.F4) (K := GaloisField 2 f) hγ'
  haveI : Finite (Module.End (GaloisField 2 f) (RootModule Tag.F4 (GaloisField 2 f))) :=
    Module.finite_of_finite (GaloisField 2 f)
  haveI : Finite (adjointGroup Tag.F4 (GaloisField 2 f)) := Subtype.finite
  refine exists_involution_mem_ggRootSub (Δ := adjDatum (rootOperatorFamily Tag.F4)
    (GaloisField 2 f)) hγ u hker hsq ?_ ?_
  · exact rootGroup_ne_bot (F := rootOperatorFamily Tag.F4) hγ'
  · exact inf_center_eq_bot_of_isPGroup_two_of_oddCenter
      (X := (adjDatum (rootOperatorFamily Tag.F4) (GaloisField 2 f)).rootGroup γ)
      (fun x => ⟨1, Subtype.ext (by simpa [pow_two] using hsq x x.2)⟩)
      (odd_center_adjoint Tag.F4 (GaloisField 2 f))

theorem rootGroupInvolutionPsi_E6 (n f : ℕ) (hf : 1 ≤ f) {G : Type} [Group G]
    (ψ : (ggU .E6 n f).K →* G) (hker : ψ.ker ≤ Subgroup.center (ggU .E6 n f).K)
    {γ : Fin (ggU .E6 n f).D.rank → ℤ} (hγ : γ ∈ (ggU .E6 n f).D.roots)
    (hclass : GGRootClass (ggU .E6 n f).D .E6 γ) (u : (ggU .E6 n f).K) :
    ∃ r ∈ ggRootSub (ggU .E6 n f).D ψ γ u, orderOf r = 2 := by
  change ∃ r ∈ ggRootSub (e6Datum (GaloisField 2 f)) ψ γ u, orderOf r = 2
  change γ ∈ (e6Datum (GaloisField 2 f)).roots at hγ
  change ψ.ker ≤ Subgroup.center (e6Data_valid.minGroup (GaloisField 2 f)) at hker
  have hγ' : IsRoot Tag.E6 γ :=
    (MinData.Valid.mem_minDatum_roots (hV := e6Data_valid) (hA := isFiniteType_cartan_E6)
      (k := GaloisField 2 f)).1 hγ
  have hsq : ∀ x ∈ (e6Datum (GaloisField 2 f)).rootGroup γ, x * x = 1 :=
    minDatum_rootGroup_sq_one (D := e6Data) (hV := e6Data_valid)
      (hA := isFiniteType_cartan_E6) (k := GaloisField 2 f) hγ'
  haveI : Finite (Module.End (GaloisField 2 f) (Fin e6Data.d →₀ GaloisField 2 f)) :=
    Module.finite_of_finite (GaloisField 2 f)
  haveI : Finite ↥(e6Data_valid.minGroup (GaloisField 2 f)) := Subtype.finite
  refine exists_involution_mem_ggRootSub (Δ := e6Datum (GaloisField 2 f)) hγ u hker hsq ?_ ?_
  · exact e6Data_valid.rootGroup_ne_bot (GaloisField 2 f) hγ'
  · exact inf_center_eq_bot_of_isPGroup_two_of_oddCenter
      (X := (e6Datum (GaloisField 2 f)).rootGroup γ)
      (fun x => ⟨1, Subtype.ext (by simpa [pow_two] using hsq x x.2)⟩)
      (odd_center_e6 f)

theorem rootGroupInvolutionPsi_E7 (n f : ℕ) (hf : 1 ≤ f) {G : Type} [Group G]
    (ψ : (ggU .E7 n f).K →* G) (hker : ψ.ker ≤ Subgroup.center (ggU .E7 n f).K)
    {γ : Fin (ggU .E7 n f).D.rank → ℤ} (hγ : γ ∈ (ggU .E7 n f).D.roots)
    (hclass : GGRootClass (ggU .E7 n f).D .E7 γ) (u : (ggU .E7 n f).K) :
    ∃ r ∈ ggRootSub (ggU .E7 n f).D ψ γ u, orderOf r = 2 := by
  change ∃ r ∈ ggRootSub (e7Datum (GaloisField 2 f)) ψ γ u, orderOf r = 2
  change γ ∈ (e7Datum (GaloisField 2 f)).roots at hγ
  change ψ.ker ≤ Subgroup.center (e7Data_valid.minGroup (GaloisField 2 f)) at hker
  have hγ' : IsRoot Tag.E7 γ :=
    (MinData.Valid.mem_minDatum_roots (hV := e7Data_valid) (hA := isFiniteType_cartan_E7)
      (k := GaloisField 2 f)).1 hγ
  have hsq : ∀ x ∈ (e7Datum (GaloisField 2 f)).rootGroup γ, x * x = 1 :=
    minDatum_rootGroup_sq_one (D := e7Data) (hV := e7Data_valid)
      (hA := isFiniteType_cartan_E7) (k := GaloisField 2 f) hγ'
  haveI : Finite (Module.End (GaloisField 2 f) (Fin e7Data.d →₀ GaloisField 2 f)) :=
    Module.finite_of_finite (GaloisField 2 f)
  haveI : Finite ↥(e7Data_valid.minGroup (GaloisField 2 f)) := Subtype.finite
  refine exists_involution_mem_ggRootSub (Δ := e7Datum (GaloisField 2 f)) hγ u hker hsq ?_ ?_
  · exact e7Data_valid.rootGroup_ne_bot (GaloisField 2 f) hγ'
  · exact inf_center_eq_bot_of_isPGroup_two_of_oddCenter
      (X := (e7Datum (GaloisField 2 f)).rootGroup γ)
      (fun x => ⟨1, Subtype.ext (by simpa [pow_two] using hsq x x.2)⟩)
      (odd_center_e7 f hf)

theorem rootGroupInvolutionPsi_E8 (n f : ℕ) (hf : 1 ≤ f) {G : Type} [Group G]
    (ψ : (ggU .E8 n f).K →* G) (hker : ψ.ker ≤ Subgroup.center (ggU .E8 n f).K)
    {γ : Fin (ggU .E8 n f).D.rank → ℤ} (hγ : γ ∈ (ggU .E8 n f).D.roots)
    (hclass : GGRootClass (ggU .E8 n f).D .E8 γ) (u : (ggU .E8 n f).K) :
    ∃ r ∈ ggRootSub (ggU .E8 n f).D ψ γ u, orderOf r = 2 := by
  change ∃ r ∈ ggRootSub (adjDatum (rootOperatorFamily Tag.E8) (GaloisField 2 f)) ψ γ u,
    orderOf r = 2
  change γ ∈ (adjDatum (rootOperatorFamily Tag.E8) (GaloisField 2 f)).roots at hγ
  change ψ.ker ≤ Subgroup.center (adjointGroup Tag.E8 (GaloisField 2 f)) at hker
  have hγ' : IsRoot Tag.E8 γ :=
    (mem_adjDatum_roots (F := rootOperatorFamily Tag.E8) (K := GaloisField 2 f)).1 hγ
  have hsq : ∀ x ∈ (adjDatum (rootOperatorFamily Tag.E8) (GaloisField 2 f)).rootGroup γ,
      x * x = 1 :=
    adjDatum_rootGroup_sq_one (F := rootOperatorFamily Tag.E8) (K := GaloisField 2 f) hγ'
  haveI : Finite (Module.End (GaloisField 2 f) (RootModule Tag.E8 (GaloisField 2 f))) :=
    Module.finite_of_finite (GaloisField 2 f)
  haveI : Finite (adjointGroup Tag.E8 (GaloisField 2 f)) := Subtype.finite
  refine exists_involution_mem_ggRootSub (Δ := adjDatum (rootOperatorFamily Tag.E8)
    (GaloisField 2 f)) hγ u hker hsq ?_ ?_
  · exact rootGroup_ne_bot (F := rootOperatorFamily Tag.E8) hγ'
  · exact inf_center_eq_bot_of_isPGroup_two_of_oddCenter
      (X := (adjDatum (rootOperatorFamily Tag.E8) (GaloisField 2 f)).rootGroup γ)
      (fun x => ⟨1, Subtype.ext (by simpa [pow_two] using hsq x x.2)⟩)
      (odd_center_adjoint Tag.E8 (GaloisField 2 f))

theorem rootGroupInvolutionPsi_twistedE6 (n f : ℕ) (hf : 1 ≤ f) {G : Type} [Group G]
    (ψ : (ggU .twistedE6 n f).K →* G)
    (hker : ψ.ker ≤ Subgroup.center (ggU .twistedE6 n f).K)
    {γ : Fin (ggU .twistedE6 n f).D.rank → ℤ} (hγ : γ ∈ (ggU .twistedE6 n f).D.roots)
    (hclass : GGRootClass (ggU .twistedE6 n f).D .twistedE6 γ)
    (u : (ggU .twistedE6 n f).K) :
    ∃ r ∈ ggRootSub (ggU .twistedE6 n f).D ψ γ u, orderOf r = 2 := by
  change ∃ r ∈ ggRootSub (twistedE6Datum 2 f) ψ γ u, orderOf r = 2
  change γ ∈ (twistedE6Datum 2 f).roots at hγ
  change ψ.ker ≤ Subgroup.center (twistedE6Group 2 f) at hker
  let K := GaloisField 2 (2 * f)
  let θ : K →+* K := frobQ 2 f
  have hθ : ∀ c, θ (θ c) = c := frobQ_frobQ 2 f hf
  have hγ' : IsRoot Tag.F4 γ :=
    isRoot_of_mem_twistedDatum_roots (k := K) (θ := θ) hγ
  have hsq : ∀ x ∈ (twistedE6Datum 2 f).rootGroup γ, x * x = 1 :=
    twistedE6_rootGroup_sq_one f hf hγ
  have hne : (twistedE6Datum 2 f).rootGroup γ ≠ ⊥ := by
    change twistedRootGroup K θ γ ≠ ⊥
    exact twistedRootGroup_ne_bot (k := K) (θ := θ) hθ hγ'
  haveI : Finite (Module.End K (Fin e6Data.d →₀ K)) :=
    Module.finite_of_finite K
  haveI : Finite ↥(e6Data_valid.minGroup K) := Subtype.finite
  haveI : Finite (twistedE6Group 2 f) := Subtype.finite
  refine exists_involution_mem_ggRootSub (Δ := twistedE6Datum 2 f) hγ u hker hsq hne ?_
  exact inf_center_eq_bot_of_isPGroup_two_of_oddCenter
    (X := (twistedE6Datum 2 f).rootGroup γ)
    (fun x => ⟨1, Subtype.ext (by
      simpa [pow_two] using hsq x x.2)⟩)
    (odd_center_twistedE6 f hf)

theorem rootGroupInvolutionPsiAt (t : StatedLieTag) (ht : GGExcFive t)
    (n f : ℕ) (hf : 1 ≤ f) {G : Type} [Group G]
    (ψ : (ggU t n f).K →* G) (hker : ψ.ker ≤ Subgroup.center (ggU t n f).K)
    {γ : Fin (ggU t n f).D.rank → ℤ} (hγ : γ ∈ (ggU t n f).D.roots)
    (hclass : GGRootClass (ggU t n f).D t γ) (u : (ggU t n f).K) :
    ∃ r ∈ ggRootSub (ggU t n f).D ψ γ u, orderOf r = 2 := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact rootGroupInvolutionPsi_F4 n f hf ψ hker hγ hclass u
  · exact rootGroupInvolutionPsi_E6 n f hf ψ hker hγ hclass u
  · exact rootGroupInvolutionPsi_E7 n f hf ψ hker hγ hclass u
  · exact rootGroupInvolutionPsi_E8 n f hf ψ hker hγ hclass u
  · exact rootGroupInvolutionPsi_twistedE6 n f hf ψ hker hγ hclass u

end CFSG.LieType.AschbacherSeitz

end
