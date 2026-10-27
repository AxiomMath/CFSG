module

public import CFSG.ClassicalInvolution.RouteD.LocalTwinPartner
public import CFSG.ClassicalInvolution.RouteD.GapsEnd4Aux
public import CFSG.ClassicalInvolution.RouteD.GapsR2

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.Open (classicalInvolutionOddCore)
open scoped commutatorElement MatrixGroups

section Perfect

variable {KY : Type} [Group KY]

theorem commutator_mul_central (a b c d : KY) (hc : c ∈ Subgroup.center KY)
    (hd : d ∈ Subgroup.center KY) : ⁅a * c, b * d⁆ = ⁅a, b⁆ := by
  have hc' := Subgroup.mem_center_iff.mp hc
  have hd' := Subgroup.mem_center_iff.mp hd
  simp only [commutatorElement_def, mul_inv_rev]
  calc a * c * (b * d) * (c⁻¹ * a⁻¹) * (d⁻¹ * b⁻¹)
      = a * (c * (b * d)) * (c⁻¹ * a⁻¹) * (d⁻¹ * b⁻¹) := by simp only [mul_assoc]
    _ = a * ((b * d) * c) * (c⁻¹ * a⁻¹) * (d⁻¹ * b⁻¹) := by rw [← hc' (b * d)]
    _ = a * b * d * (c * c⁻¹) * a⁻¹ * (d⁻¹ * b⁻¹) := by simp only [mul_assoc]
    _ = a * b * (d * a⁻¹ * d⁻¹) * b⁻¹ := by simp only [mul_inv_cancel, mul_one, mul_assoc]
    _ = a * b * (a⁻¹ * (d * d⁻¹)) * b⁻¹ := by rw [← hd' a⁻¹]; simp only [mul_assoc]
    _ = a * b * a⁻¹ * b⁻¹ := by simp [mul_assoc]

theorem conj_mem_of_perfect {R : Subgroup KY} (hR : R ≤ ⁅R, R⁆) (r : KY)
    (h : ∀ x ∈ R, ∃ y ∈ R, ∃ c ∈ Subgroup.center KY, r * x * r⁻¹ = y * c) :
    ∀ x ∈ R, r * x * r⁻¹ ∈ R := by
  intro x hx
  have hx' := hR hx
  clear hx
  rw [Subgroup.commutator_def] at hx'
  induction hx' using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hg
    obtain ⟨y₁, hy₁, c₁, hc₁, e₁⟩ := h a ha
    obtain ⟨y₂, hy₂, c₂, hc₂, e₂⟩ := h b hb
    have : r * ⁅a, b⁆ * r⁻¹ = ⁅r * a * r⁻¹, r * b * r⁻¹⁆ := by
      simp only [commutatorElement_def]; group
    rw [this, e₁, e₂, commutator_mul_central _ _ _ _ hc₁ hc₂]
    simp only [commutatorElement_def]
    exact R.mul_mem (R.mul_mem (R.mul_mem hy₁ hy₂) (R.inv_mem hy₁)) (R.inv_mem hy₂)
  | one => simp
  | mul a b _ _ ha hb =>
    have : r * (a * b) * r⁻¹ = (r * a * r⁻¹) * (r * b * r⁻¹) := by group
    rw [this]; exact R.mul_mem ha hb
  | inv a _ ha =>
    have : r * a⁻¹ * r⁻¹ = (r * a * r⁻¹)⁻¹ := by group
    rw [this]; exact R.inv_mem ha

end Perfect

section StdNormalize

variable {F : Type} [Field F]

theorem blockSL_neg_one_mul (x : SL(3, F)) :
    blockSL F 3 2 1 (by omega) (-1) * x =
      (diagConj3 (-1) 1 x) * blockSL F 3 2 1 (by omega) (-1) := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_diagConj3,
    coe_blockSL_three_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_three]

theorem conjSub_eq_of_standardPair (h2 : (2 : F) ≠ 0) {X : Type} [Group X] {W U V : Subgroup X}
    (h : LinearBlockStandardPair F W U V) {v : X} (hv : v ∈ V) (hv2 : orderOf v = 2) :
    conjSub v U = U := by
  obtain ⟨θ, -, hker, hU, hV⟩ := pair_normalize h
  rw [← hV] at hv
  have hvθ := eq_block_neg_one h2 hker (by omega : 1 + 2 ≤ 3) hv hv2
  set n : SL(3, F) := blockSL F 3 2 1 (by omega) (-1) with hn
  have hnn : n * n = 1 := by
    rw [hn, ← map_mul]
    have : (-1 : SL(2, F)) * (-1) = 1 := by simp
    rw [this, map_one]
  have hvv : v * v = 1 := by rw [hvθ, ← map_mul, hnn, map_one]
  have key : ∀ u ∈ U, v * u * v ∈ U := by
    intro u hu
    rw [← hU] at hu
    obtain ⟨b, hb, rfl⟩ := hu
    obtain ⟨A, rfl⟩ := hb
    have e1 : n * blockSL F 3 2 0 (by omega) A =
        blockSL F 3 2 0 (by omega) (diagConj2 (-1) 1 A) * n := by
      rw [hn, blockSL_neg_one_mul, diagConj3_blockSL_zero]
    have e2 : v * θ (blockSL F 3 2 0 (by omega) A) * v =
        θ (blockSL F 3 2 0 (by omega) (diagConj2 (-1) 1 A)) := by
      rw [hvθ, ← map_mul, ← map_mul, e1, mul_assoc, hnn, mul_one]
    rw [e2, ← hU]
    exact ⟨_, ⟨_, rfl⟩, rfl⟩
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
  ext x
  rw [mem_conjSub_iff, hvi]
  constructor
  · intro hx
    have := key _ hx
    rwa [show v * (v * x * v) * v = x by
      calc v * (v * x * v) * v = (v * v) * x * (v * v) := by group
        _ = x := by rw [hvv]; group] at this
  · intro hx
    exact key x hx

end StdNormalize

theorem commute_of_conjSub_eq' {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {L : Subgroup G}
    {w t : G} (h2 : (2 : GaloisField p f) ≠ 0) (hex : classicalInvolutionOddCore L = ⊥)
    (hL : IsClassicalMember p f L w) (ht : conjSub t L = L) : Commute t w := by
  have hcl : IsClassicalMember p f (conjSub t L) (t * w * t⁻¹) := hL.conj t
  rw [ht] at hcl
  have := unique_involution_of_isClassicalMember h2 hex hL hcl
  exact (mul_inv_eq_iff_eq_mul.mp this.symm : t * w = w * t)

section Model

variable {KY : Type} [Group KY]

@[expose] def InvOf (R : Subgroup KY) (r : KY) : Prop := r ∈ R ∧ orderOf r = 2

@[expose] def ModelInvComm (Z : Subgroup KY) (R₁ R₂ : Subgroup KY) : Prop :=
  ∃ r₁ r₂, InvOf R₁ r₁ ∧ InvOf R₂ r₂ ∧ ⁅r₁, r₂⁆ ∈ Z

@[expose] def ModelAdj (Z : Subgroup KY) (R₁ R₂ : Subgroup KY) : Prop :=
  R₁ ≠ R₂ ∧ ¬ Commutes R₁ R₂ ∧ ∃ r₁ r₂, InvOf R₁ r₁ ∧ InvOf R₂ r₂ ∧
    ⁅r₁, r₂⁆ ∈ Z ∧ ∀ x ∈ R₁, r₂ * x * r₂⁻¹ ∈ R₁

@[expose] def ModelIndist (Z : Subgroup KY) (𝓕 : Set (Subgroup KY)) (R R' : Subgroup KY) : Prop :=
  R ≠ R' ∧ ∀ S ∈ 𝓕, S ≠ R → S ≠ R' → ModelInvComm Z S R → ModelInvComm Z S R' →
    (Commutes S R ↔ Commutes S R')

structure OrthGeom (Z : Subgroup KY) (𝓕 : Set (Subgroup KY)) (F : Type) [Field F] [Finite F] :
    Prop where
  star : ∀ c ∈ 𝓕, ∀ l₁ ∈ 𝓕, ∀ l₂ ∈ 𝓕, ∀ l₃ ∈ 𝓕, ModelAdj Z c l₁ → ModelAdj Z c l₂ →
    ModelAdj Z c l₃ → l₁ ≠ l₂ → l₁ ≠ l₃ → l₂ ≠ l₃ → Commutes l₁ l₂ → Commutes l₁ l₃ →
    Commutes l₂ l₃ → ModelIndist Z 𝓕 l₁ l₂ ∨ ModelIndist Z 𝓕 l₁ l₃ ∨ ModelIndist Z 𝓕 l₂ l₃
  sign : ∀ R₁ ∈ 𝓕, ∀ R₂ ∈ 𝓕, ∀ R₃ ∈ 𝓕, ModelAdj Z R₁ R₂ → ModelAdj Z R₃ R₂ → Commutes R₁ R₃ →
    (∃ W, LinearBlockStandardPair F W R₁ R₂) → ∃ W, LinearBlockStandardPair F W R₂ R₃
  perp2 : ∀ R₁ ∈ 𝓕, ∀ R₂ ∈ 𝓕, ModelAdj Z R₁ R₂ → (∃ W, LinearBlockStandardPair F W R₁ R₂) →
    ∃ S₁ ∈ 𝓕, ∃ S₂ ∈ 𝓕, S₁ ≠ S₂ ∧ Commutes R₁ S₁ ∧ Commutes R₁ S₂ ∧ ¬ Commutes R₂ S₁ ∧
      ¬ Commutes R₂ S₂

structure OrthFacts (𝓕 : Set (Subgroup KY)) (F : Type) [Field F] [Finite F] : Prop
    extends OrthGeom (Subgroup.center KY) 𝓕 F where
  lift : ∀ {X : Type} [Group X] (ψ : KY →* X), ψ.ker ≤ Subgroup.center KY →
    ∀ R₁ ∈ 𝓕, ∀ R₂ ∈ 𝓕, (∃ W, LinearBlockStandardPair F W (R₁.map ψ) (R₂.map ψ)) →
      ∃ W, LinearBlockStandardPair F W R₁ R₂

end Model

section Witness

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {tY : StatedLieTag} {nY : ℕ} {N : Subgroup G} {x : G}

@[expose] def IsLayerMember (cx : TCtx p f tY nY Ω N x) (L : Subgroup G) : Prop :=
  L ∈ centralizingMembers Ω {x} ∧ L ≠ N ∧ ¬ locImg Ω x L ≤ cx.d.Q₁

theorem IsLayerMember.of_not_commutes (cx : TCtx p f tY nY Ω N x) {L L' : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {x}) (hL' : L' ∈ centralizingMembers Ω {x}) (hne : L ≠ L')
    (hc : ¬ Commutes L L') : IsLayerMember cx L := by
  refine ⟨hL, ?_, ?_⟩
  · rintro rfl
    exact hc (cx.commutes_K_of_ne hL' (fun h => hne h.symm))
  · intro hTQ
    exact hc (cx.commutes_T_of_ne hL hTQ hL' (fun h => hne h.symm))

theorem IsLayerMember.exists_fund {cx : TCtx p f tY nY Ω N x} {L : Subgroup G}
    (hL : IsLayerMember cx L) :
    ∃ R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D,
      locImg Ω x L = R.map cx.d.ψ :=
  cx.exists_fund_of_ne hL.1 hL.2.1 hL.2.2

theorem exists_involution_of_fund (cx : TCtx p f tY nY Ω N x) {L : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {x})
    {R : Subgroup (modelUniv tY nY p f Fact.out).K}
    (hR : R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D)
    (hLR : locImg Ω x L = R.map cx.d.ψ) {w : G} (hw : IsClassicalMember p f L w) :
    ∃ r, InvOf R r ∧ cx.d.ψ r = locElt Ω x w (le_centralizingLayer hL hw.mem) := by
  have hwx : w ∈ locLayer Ω x := le_centralizingLayer hL hw.mem
  have hmem : locElt Ω x w hwx ∈ R.map cx.d.ψ :=
    hLR ▸ locElt_mem_locImg (le_centralizingLayer hL) hw.mem
  obtain ⟨r, hrR, hr⟩ := hmem
  have h2 : orderOf (cx.d.ψ r) = 2 := by
    rw [hr]; exact orderOf_locElt hwx hw.orderOf_eq_two
  have hsq : r * r = 1 := by
    have h1 : cx.d.ψ (r * r) = 1 := by
      rw [map_mul]
      have := pow_orderOf_eq_one (cx.d.ψ r)
      rwa [h2, pow_two] at this
    exact cx.hY.central R hR (r * r) (R.mul_mem hrR hrR) (cx.d.ker_le h1)
  have hr1 : r ≠ 1 := by
    intro h
    rw [h, map_one] at h2
    simp at h2
  exact ⟨r, ⟨hrR, orderOf_eq_prime (by rw [pow_two]; exact hsq) hr1⟩, hr⟩

theorem modelInvComm_of_commute (cx : TCtx p f tY nY Ω N x) {L L' : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {x}) (hL' : L' ∈ centralizingMembers Ω {x})
    {R R' : Subgroup (modelUniv tY nY p f Fact.out).K}
    (hR : R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D)
    (hR' : R' ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D)
    (hLR : locImg Ω x L = R.map cx.d.ψ) (hLR' : locImg Ω x L' = R'.map cx.d.ψ) {w w' : G}
    (hw : IsClassicalMember p f L w) (hw' : IsClassicalMember p f L' w') (hc : Commute w w') :
    ∃ r r', InvOf R r ∧ InvOf R' r' ∧ ⁅r, r'⁆ ∈ Subgroup.center (modelUniv tY nY p f Fact.out).K ∧
      cx.d.ψ r = locElt Ω x w (le_centralizingLayer hL hw.mem) ∧
      cx.d.ψ r' = locElt Ω x w' (le_centralizingLayer hL' hw'.mem) := by
  obtain ⟨r, hr, hψr⟩ := exists_involution_of_fund cx hL hR hLR hw
  obtain ⟨r', hr', hψr'⟩ := exists_involution_of_fund cx hL' hR' hLR' hw'
  refine ⟨r, r', hr, hr', cx.d.ker_le ?_, hψr, hψr'⟩
  have hcomm : cx.d.ψ r * cx.d.ψ r' = cx.d.ψ r' * cx.d.ψ r := by
    rw [hψr, hψr', locElt_mul, locElt_mul]
    congr 1
  rw [MonoidHom.mem_ker, map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm

omit [Finite G] in
theorem normalizes_of_conjSub (cx : TCtx p f tY nY Ω N x) {L : Subgroup G}
    {R : Subgroup (modelUniv tY nY p f Fact.out).K}
    (hR : R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D)
    (hLR : locImg Ω x L = R.map cx.d.ψ) {w : G} (hwx : w ∈ locLayer Ω x)
    {r : (modelUniv tY nY p f Fact.out).K} (hr : cx.d.ψ r = locElt Ω x w hwx)
    (hN : conjSub w L = L) : ∀ y ∈ R, r * y * r⁻¹ ∈ R := by
  refine conj_mem_of_perfect (cx.hY.perfR R hR) r fun y hy => ?_
  have hmem : cx.d.ψ (r * y * r⁻¹) ∈ R.map cx.d.ψ := by
    have h1 : cx.d.ψ y ∈ locImg Ω x L := by
      rw [hLR]; exact ⟨y, hy, rfl⟩
    have h2 : cx.d.ψ (r * y * r⁻¹) ∈ locImg Ω x (conjSub w L) := by
      have := locImg_conjSub_layer (Ω := Ω) (x := x) L ⟨w, hwx⟩
      rw [this]
      refine ⟨cx.d.ψ y, h1, ?_⟩
      simp only [map_mul, map_inv, hr]
      rfl
    rwa [hN, hLR] at h2
  obtain ⟨y', hy', hy'e⟩ := hmem
  refine ⟨y', hy', y'⁻¹ * (r * y * r⁻¹), cx.d.ker_le ?_, by group⟩
  rw [MonoidHom.mem_ker, map_mul, map_inv, hy'e, inv_mul_cancel]

theorem modelAdj_of_adj (cx : TCtx p f tY nY Ω N x) {L L' : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {x}) (hL' : L' ∈ centralizingMembers Ω {x})
    {R R' : Subgroup (modelUniv tY nY p f Fact.out).K}
    (hR : R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D)
    (hR' : R' ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D)
    (hLR : locImg Ω x L = R.map cx.d.ψ) (hLR' : locImg Ω x L' = R'.map cx.d.ψ) {w w' : G}
    (hw : IsClassicalMember p f L w) (hw' : IsClassicalMember p f L' w') (hne : L ≠ L')
    (hnc : ¬ Commutes L L') (hc : Commute w w') (hN : conjSub w' L = L) :
    ModelAdj (Subgroup.center (modelUniv tY nY p f Fact.out).K) R R' := by
  obtain ⟨r, r', hr, hr', hcen, hψr, hψr'⟩ :=
    modelInvComm_of_commute cx hL hL' hR hR' hLR hLR' hw hw' hc
  refine ⟨fun h => hne (cx.eq_of_locImg_eq hL hL' (by rw [hLR, hLR', h])), ?_, r, r', hr, hr',
    hcen, ?_⟩
  · intro h
    exact hnc ((cx.commutes_iff_fund hL hL' hR hLR hLR').mpr h)
  · exact normalizes_of_conjSub cx hR hLR (le_centralizingLayer hL' hw'.mem) hψr' hN

theorem modelInvComm_of_members (cx : TCtx p f tY nY Ω N x) {L L' : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {x}) (hL' : L' ∈ centralizingMembers Ω {x})
    {R R' : Subgroup (modelUniv tY nY p f Fact.out).K}
    (hR : R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D)
    (hR' : R' ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D)
    (hLR : locImg Ω x L = R.map cx.d.ψ) (hLR' : locImg Ω x L' = R'.map cx.d.ψ) {w w' : G}
    (hw : IsClassicalMember p f L w) (hw' : IsClassicalMember p f L' w') (hc : Commute w w') :
    ModelInvComm (Subgroup.center (modelUniv tY nY p f Fact.out).K) R R' := by
  obtain ⟨r, r', hr, hr', hcen, -, -⟩ :=
    modelInvComm_of_commute cx hL hL' hR hR' hLR hLR' hw hw' hc
  exact ⟨r, r', hr, hr', hcen⟩

theorem commutes_iff_of_indist (cx : TCtx p f tY nY Ω N x) {l l' d : Subgroup G}
    (hl : l ∈ centralizingMembers Ω {x}) (hl' : l' ∈ centralizingMembers Ω {x})
    (hd : IsLayerMember cx d) {Rl Rl' Rd : Subgroup (modelUniv tY nY p f Fact.out).K}
    (hRl : Rl ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D)
    (hRl' : Rl' ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D)
    (hRd : Rd ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D)
    (hlR : locImg Ω x l = Rl.map cx.d.ψ) (hlR' : locImg Ω x l' = Rl'.map cx.d.ψ)
    (hdR : locImg Ω x d = Rd.map cx.d.ψ) {wl wl' wd : G} (hwl : IsClassicalMember p f l wl)
    (hwl' : IsClassicalMember p f l' wl') (hwd : IsClassicalMember p f d wd) (hdl : d ≠ l)
    (hdl' : d ≠ l') (hc : Commute wd wl) (hc' : Commute wd wl')
    (hind : ModelIndist (Subgroup.center (modelUniv tY nY p f Fact.out).K)
      (fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D) Rl Rl') :
    Commutes d l ↔ Commutes d l' := by
  have h1 : Rd ≠ Rl := fun h => hdl (cx.eq_of_locImg_eq hd.1 hl (by rw [hdR, hlR, h]))
  have h2 : Rd ≠ Rl' := fun h => hdl' (cx.eq_of_locImg_eq hd.1 hl' (by rw [hdR, hlR', h]))
  have := hind.2 Rd hRd h1 h2 (modelInvComm_of_members cx hd.1 hl hRd hRl hdR hlR hwd hwl hc)
    (modelInvComm_of_members cx hd.1 hl' hRd hRl' hdR hlR' hwd hwl' hc')
  rw [cx.commutes_iff_fund hd.1 hl hRd hdR hlR, cx.commutes_iff_fund hd.1 hl' hRd hdR hlR']
  exact this

theorem IsLayerMember.of_distinguish (cx : TCtx p f tY nY Ω N x) {d l l' : Subgroup G}
    (hd : d ∈ centralizingMembers Ω {x}) (hl : l ∈ centralizingMembers Ω {x})
    (hl' : l' ∈ centralizingMembers Ω {x}) (hdl : d ≠ l) (hdl' : d ≠ l')
    (h : ¬ (Commutes d l ↔ Commutes d l')) : IsLayerMember cx d := by
  by_cases hc : Commutes d l
  · exact IsLayerMember.of_not_commutes cx hd hl' hdl' (fun hc' => h ⟨fun _ => hc', fun _ => hc⟩)
  · exact IsLayerMember.of_not_commutes cx hd hl hdl hc

theorem star_config (cx : TCtx p f tY nY Ω N x)
    (hF : OrthGeom (Subgroup.center (modelUniv tY nY p f Fact.out).K)
      (fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D) (GaloisField p f))
    {c : Subgroup G} {wc : G} {l : Fin 3 → Subgroup G} {w : Fin 3 → G}
    (hc : c ∈ centralizingMembers Ω {x}) (hwc : IsClassicalMember p f c wc)
    (hl : ∀ i, l i ∈ centralizingMembers Ω {x}) (hw : ∀ i, IsClassicalMember p f (l i) (w i))
    (hadj : ∀ i, c ≠ l i ∧ ¬ Commutes c (l i) ∧ Commute wc (w i) ∧ conjSub (w i) c = c)
    (hcomm : ∀ i j, i ≠ j → l i ≠ l j ∧ Commutes (l i) (l j))
    (hdist : ∀ i j : Fin 3, i < j → ∃ d v, d ∈ centralizingMembers Ω {x} ∧
      IsClassicalMember p f d v ∧ d ≠ l i ∧ d ≠ l j ∧ Commute v (w i) ∧ Commute v (w j) ∧
      ¬ (Commutes d (l i) ↔ Commutes d (l j))) : False := by
  classical
  have hcL : IsLayerMember cx c :=
    IsLayerMember.of_not_commutes cx hc (hl 0) (hadj 0).1 (hadj 0).2.1
  have hlL : ∀ i, IsLayerMember cx (l i) := fun i =>
    IsLayerMember.of_not_commutes cx (hl i) hc (hadj i).1.symm
      (fun h => (hadj i).2.1 (commutes_symm h))
  obtain ⟨Rc, hRc, hcR⟩ := hcL.exists_fund
  have hex : ∀ i, ∃ R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D,
      locImg Ω x (l i) = R.map cx.d.ψ := fun i => (hlL i).exists_fund
  choose R hR hlR using hex
  have hadjR : ∀ i, ModelAdj (Subgroup.center (modelUniv tY nY p f Fact.out).K) Rc (R i) :=
    fun i =>
    modelAdj_of_adj cx hc (hl i) hRc (hR i) hcR (hlR i) hwc (hw i) (hadj i).1 (hadj i).2.1
      (hadj i).2.2.1 (hadj i).2.2.2
  have hne : ∀ i j, i ≠ j → R i ≠ R j := fun i j hij h =>
    (hcomm i j hij).1 (cx.eq_of_locImg_eq (hl i) (hl j) (by rw [hlR i, hlR j, h]))
  have hcR' : ∀ i j, i ≠ j → Commutes (R i) (R j) := fun i j hij =>
    (cx.commutes_iff_fund (hl i) (hl j) (hR i) (hlR i) (hlR j)).mp (hcomm i j hij).2
  have key : ∀ i j : Fin 3, i < j → ModelIndist (Subgroup.center (modelUniv tY nY p f Fact.out).K)
      (fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D) (R i) (R j) → False := by
    intro i j hij hind
    obtain ⟨d, v, hd, hvd, hdi, hdj, hvi, hvj, hdn⟩ := hdist i j hij
    have hdL : IsLayerMember cx d := IsLayerMember.of_distinguish cx hd (hl i) (hl j) hdi hdj hdn
    obtain ⟨Rd, hRd, hdR⟩ := hdL.exists_fund
    exact hdn (commutes_iff_of_indist cx (hl i) (hl j) hdL (hR i) (hR j) hRd (hlR i) (hlR j)
      hdR (hw i) (hw j) hvd hdi hdj hvi hvj hind)
  have hstar := hF.star Rc hRc (R 0) (hR 0) (R 1) (hR 1) (R 2) (hR 2) (hadjR 0) (hadjR 1)
    (hadjR 2) (hne 0 1 (by decide)) (hne 0 2 (by decide)) (hne 1 2 (by decide))
    (hcR' 0 1 (by decide)) (hcR' 0 2 (by decide)) (hcR' 1 2 (by decide))
  rcases hstar with h | h | h
  · exact key 0 1 (by decide) h
  · exact key 0 2 (by decide) h
  · exact key 1 2 (by decide) h

omit [Finite G] in
theorem linearBlockStandardPair_locImg_of_members (hP1 : LocalOddCentral Ω {x})
    {L L' : Subgroup G} (hL : L ∈ centralizingMembers Ω {x}) (hL' : L' ∈ centralizingMembers Ω {x})
    {W : Subgroup G} (h : LinearBlockStandardPair (GaloisField p f) W L L') :
    ∃ W' : Subgroup (locQuot Ω x),
      LinearBlockStandardPair (GaloisField p f) W' (locImg Ω x L) (locImg Ω x L') := by
  have hW : W ≤ locLayer Ω x := (linearBlockStandardPair_le_sup' h).trans
    (sup_le (le_centralizingLayer hL) (le_centralizingLayer hL'))
  have h1 := CFSG.ClassicalInvolution.Generic.linearBlockStandardPair_subgroupOf hW h
  have hker : (QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x))).ker ≤
      Subgroup.center ↥(locLayer Ω x) := by
    rw [QuotientGroup.ker_mk']; exact hP1
  exact ⟨_, linearBlockStandardPair_map_central h1 _ hker⟩

theorem sign_config (cx : TCtx p f tY nY Ω N x)
    (hF : OrthFacts (fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D) (GaloisField p f))
    {a b d : Subgroup G} {wa wb wd : G} (ha : a ∈ centralizingMembers Ω {x})
    (hb : b ∈ centralizingMembers Ω {x}) (hd : d ∈ centralizingMembers Ω {x})
    (hwa : IsClassicalMember p f a wa) (hwb : IsClassicalMember p f b wb)
    (hwd : IsClassicalMember p f d wd) (hab : a ≠ b) (hbd : b ≠ d)
    (hpair : ∃ W, LinearBlockStandardPair (GaloisField p f) W a b) (hnbd : ¬ Commutes b d)
    (had : Commutes a d) (hcab : Commute wa wb) (hcdb : Commute wd wb)
    (hna : conjSub wb a = a) (hnd : conjSub wb d = d) :
    ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W b d := by
  obtain ⟨W, hW⟩ := hpair
  have hnab : ¬ Commutes a b := not_commutes_of_linearBlockStandardPair hW
  have haL : IsLayerMember cx a := IsLayerMember.of_not_commutes cx ha hb hab hnab
  have hbL : IsLayerMember cx b :=
    IsLayerMember.of_not_commutes cx hb hd hbd hnbd
  have hdL : IsLayerMember cx d := IsLayerMember.of_not_commutes cx hd hb hbd.symm
    (fun h => hnbd (commutes_symm h))
  obtain ⟨Ra, hRa, haR⟩ := haL.exists_fund
  obtain ⟨Rb, hRb, hbR⟩ := hbL.exists_fund
  obtain ⟨Rd, hRd, hdR⟩ := hdL.exists_fund
  have hadjab : ModelAdj (Subgroup.center (modelUniv tY nY p f Fact.out).K) Ra Rb :=
    modelAdj_of_adj cx ha hb hRa hRb haR hbR hwa hwb hab hnab hcab hna
  have hadjdb : ModelAdj (Subgroup.center (modelUniv tY nY p f Fact.out).K) Rd Rb :=
    modelAdj_of_adj cx hd hb hRd hRb hdR hbR hwd hwb hbd.symm
      (fun h => hnbd (commutes_symm h)) hcdb hnd
  have hcom : Commutes Ra Rd := (cx.commutes_iff_fund ha hd hRa haR hdR).mp had
  obtain ⟨W', hW'⟩ := linearBlockStandardPair_locImg_of_members cx.hP1 ha hb hW
  rw [haR, hbR] at hW'
  have hlift := hF.lift cx.d.ψ cx.d.ker_le Ra hRa Rb hRb ⟨W', hW'⟩
  obtain ⟨W₂, hW₂⟩ := hF.sign Ra hRa Rb hRb Rd hRd hadjab hadjdb hcom hlift
  exact cx.stdPair_of_fund hb hd hW₂ hbR hdR

end Witness

end CFSG.ClassicalInvolution.RouteD.Gaps
