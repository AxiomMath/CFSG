module

public import CFSG.GF2Type.Smith1979W3.T1216SquareData
public import CFSG.GF2Type.Smith1979W3.T1216Lift

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.O62 CFSG.GF2Type.Smith1979W3.Cert690
  CFSG.RankThree.Literature.FSmith

variable {G : Type} [Group G] [Finite G] (S : Setting G) {L : S.Qt ≃ₗ[ZMod 2] V₀}

private theorem conjL_rho_inv_eq_inv (y : S.M) :
    conjL L ↑(S.ρ y⁻¹) = (conjL L ↑(S.ρ y))⁻¹ := by
  rw [show (S.ρ y⁻¹ : S.O) = (S.ρ y)⁻¹ from map_inv _ _]
  rw [Subgroup.coe_inv, map_inv]

private theorem conjL_rho_mem_KPGL (hK : mbarModel S L = KPGL) (y : S.M) :
    conjL L ↑(S.ρ y) ∈ KPGL := by
  rw [← hK]
  exact conjL_ρ_mem_mbarModel S L y

private theorem conjL_rho_outer_iff (y : S.M) :
    conjL L ↑(S.ρ y) ∉ KPGL0 ↔ conjL L ↑(S.ρ y⁻¹) ∉ KPGL0 := by
  rw [conjL_rho_inv_eq_inv]
  exact not_congr (Subgroup.inv_mem_iff (H := KPGL0) (x := conjL L ↑(S.ρ y))).symm

private noncomputable def qgEquiv :
    {x : G // x ∈ S.QG} ≃ S.Q where
  toFun x :=
    ⟨⟨x.1, (S.mem_QG_iff.mp x.2).choose⟩, (S.mem_QG_iff.mp x.2).choose_spec⟩
  invFun q := ⟨(q : G), Subgroup.mem_map.mpr ⟨q, q.2, rfl⟩⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv q := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

private noncomputable def qgSubtypeEquiv (P : G → Prop) :
    {x : G // x ∈ S.QG ∧ P x} ≃ {q : S.Q // P (q : G)} where
  toFun x :=
    ⟨qgEquiv S ⟨x.1, x.2.1⟩, by
      have h := x.2.2
      change P ((qgEquiv S ⟨x.1, x.2.1⟩ : S.Q) : G) at h
      exact h⟩
  invFun q :=
    ⟨(q.1 : G), ⟨Subgroup.mem_map.mpr ⟨q.1, q.1.2, rfl⟩, q.2⟩⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv q := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

theorem exists_outer_involution_KPGL (hF : PGLFactsProp) :
    ∃ u ∈ KPGL, u ∉ KPGL0 ∧ u * u = 1 := by
  classical
  let u : V₀ ≃ₗ[ZMod 2] V₀ := wordProd [3, 12, 48]
  have hcode : Code.HasCode (u : V₀ →ₗ[ZMod 2] V₀) (wordC [3, 12, 48]) :=
    hasCode_wordProd _
  have hmem : u ∈ KPGL :=
    Subgroup.subset_closure ⟨wordC [3, 12, 48], by decide, hcode⟩
  have hsq : u * u = 1 := by
    show wordProd [3, 12, 48] * wordProd [3, 12, 48] = 1
    rw [← wordProd_append, ← wordProd_nil]
    exact (wordProd_eq_iff _ _).mpr (by decide)
  have hact : u (Code.vec 2) = Code.vec 1 := by
    have h1 : (u : V₀ → V₀) (Code.vec 2) =
        Code.vec (Code.act (wordC [3, 12, 48]) 2) := by
      change (u : V₀ →ₗ[ZMod 2] V₀) (Code.vec 2) = _
      rw [← LinearMap.toMatrix'_mulVec (u : V₀ →ₗ[ZMod 2] V₀) (Code.vec 2)]
      rw [show LinearMap.toMatrix' (u : V₀ →ₗ[ZMod 2] V₀) = Code.mat (wordC [3, 12, 48])
        from hcode]
      rw [← Code.vec_act]
    rw [h1]
    decide
  refine ⟨u, hmem, ?_, hsq⟩
  intro hu0
  have hpres := hF.2.2.2.2.2.2.2.2.1 u hu0
  have h7 := hF.2.2.2.2.2.2.1
  have hmemVPlus : u (Code.vec 2) ∈ VPlus := by
    rw [← hpres.1]
    exact Submodule.mem_map_of_mem (f := (u : V₀ →ₗ[ZMod 2] V₀))
      (Submodule.subset_span (by simp [VPlus]))
  have hmemVStar : u (Code.vec 2) ∈ VStar := by
    rw [hact]
    exact Submodule.subset_span (by simp [VStar])
  have hmemVPlus' : Code.vec 1 ∈ VPlus := by
    rw [← hact]
    exact hmemVPlus
  have hmemVStar' : Code.vec 1 ∈ VStar := by
    rw [← hact]
    exact hmemVStar
  have hbot : Code.vec 1 ∈ (⊥ : Submodule (ZMod 2) V₀) := by
    rw [← h7]
    exact ⟨hmemVPlus', hmemVStar'⟩
  rw [Submodule.mem_bot] at hbot
  exact (by decide : Code.vec 1 ≠ (0 : V₀)) hbot

private theorem pgl_card_mul_sq
    (hPS : PGLSquareProp) (hK : mbarModel S L = KPGL)
    (φ : S.Q ≃* Q0) (hφ : ∀ x : S.Q, (φ x).v = L (S.toQt x))
    (hIS : IsSquareData KPGL (sqData S φ))
    {τ : S.M} (hτout : conjL L ↑(S.ρ τ) ∉ KPGL0) (hτ2 : τ * τ = 1) :
    Nat.card {x : G // x ∈ S.QG ∧ ((τ : G) * x) * ((τ : G) * x) = 1} = 16 := by
  classical
  let u : V₀ ≃ₗ[ZMod 2] V₀ := conjL L ↑(S.ρ τ⁻¹)
  have huKPGL : u ∈ KPGL := conjL_rho_mem_KPGL S hK τ⁻¹
  have huout : u ∉ KPGL0 := by
    change conjL L ↑(S.ρ τ⁻¹) ∉ KPGL0
    rw [show conjL L ↑(S.ρ τ⁻¹) = (conjL L ↑(S.ρ τ))⁻¹ from
      conjL_rho_inv_eq_inv (S := S) (L := L) τ]
    exact fun h => hτout ((Subgroup.inv_mem_iff (H := KPGL0)).mp h)
  have husq : u * u = 1 := by
    change conjL L ↑(S.ρ τ⁻¹) * conjL L ↑(S.ρ τ⁻¹) = 1
    rw [show conjL L ↑(S.ρ τ⁻¹) = (conjL L ↑(S.ρ τ))⁻¹ from
      conjL_rho_inv_eq_inv (S := S) (L := L) τ]
    have hτ2' : (S.ρ τ) * (S.ρ τ) = 1 := by rw [← map_mul, hτ2, map_one]
    calc (conjL L ↑(S.ρ τ))⁻¹ * (conjL L ↑(S.ρ τ))⁻¹
        = (conjL L ↑(S.ρ τ) * conjL L ↑(S.ρ τ))⁻¹ := by group
      _ = (conjL L (↑(S.ρ τ) * ↑(S.ρ τ)))⁻¹ := by rw [map_mul]
      _ = (conjL L ↑((S.ρ τ) * (S.ρ τ)))⁻¹ := by rw [Subgroup.coe_mul]
      _ = 1 := by simp [hτ2']
  have hτQ : τ * τ ∈ S.Q := by rw [hτ2]; exact one_mem _
  obtain ⟨hcase, hfix⟩ := hPS (sqData S φ) hIS u huKPGL huout husq
  let θ : Q0 ≃* Q0 := rhoQ0 S φ τ
  have hθlift : ∀ x, (θ x).v = u x.v := fun x => v_rhoQ0 S φ hφ τ x
  have hθσ : sqData S φ θ = 1 := by
    have hsub : (⟨τ * τ, hτQ⟩ : S.Q) = 1 := Subtype.ext hτ2
    rw [show θ = rhoQ0 S φ τ from rfl, sqData_rhoQ0 S φ hτQ, hsub, map_one]
  have hθmem : θ ∈ {θ : Q0 ≃* Q0 | (∀ x, (θ x).v = u x.v) ∧ sqData S φ θ = 1} :=
    ⟨hθlift, hθσ⟩
  have hcase' : Set.ncard {θ : Q0 ≃* Q0 |
      (∀ x, (θ x).v = u x.v) ∧ sqData S φ θ = 1} = 8 := by
    rcases hcase with h | h
    · exact h.1
    · exfalso
      rw [h.1] at hθmem
      exact hθmem
  have hcount := card_mul_sq_eq S φ hφ hτQ (1 : S.Q)
  have hset : {θ : Q0 ≃* Q0 |
      (∀ e, (θ e).v = conjL L ↑(S.ρ τ⁻¹) e.v) ∧ sqData S φ θ = φ 1} =
      {θ : Q0 ≃* Q0 | (∀ x, (θ x).v = u x.v) ∧ sqData S φ θ = 1} := by
    rw [map_one]
  have hcardQ16SM : Nat.card {x : S.Q //
      (τ * (x : S.M)) * (τ * (x : S.M)) = ((1 : S.Q) : S.M)} = 16 := by
    rw [hcount, hset, hcase']
  have hcardQ16 : Nat.card {q : S.Q //
      ((τ : G) * (q : G)) * ((τ : G) * (q : G)) = 1} = 16 := by
    rw [← hcardQ16SM]
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun q => by
      constructor
      · intro h
        apply Subtype.ext
        simpa using h
      · intro h
        have h' := congrArg (fun x : S.M => (x : G)) h
        simpa using h'))
  calc Nat.card {x : G // x ∈ S.QG ∧ ((τ : G) * x) * ((τ : G) * x) = 1}
      = Nat.card {q : S.Q // ((τ : G) * (q : G)) * ((τ : G) * (q : G)) = 1} :=
        Nat.card_congr (qgSubtypeEquiv S
          (fun x => ((τ : G) * x) * ((τ : G) * x) = 1))
    _ = 16 := hcardQ16

private theorem pgl_card_centralizer
    (hPS : PGLSquareProp) (hK : mbarModel S L = KPGL)
    (φ : S.Q ≃* Q0) (hφ : ∀ x : S.Q, (φ x).v = L (S.toQt x))
    (hIS : IsSquareData KPGL (sqData S φ))
    {τ : S.M} (hτout : conjL L ↑(S.ρ τ) ∉ KPGL0) (hτ2 : τ * τ = 1) :
    Nat.card ↥(S.QG ⊓ Subgroup.centralizer ({(τ : G)} : Set G)) = 8 ∧
    ∀ x ∈ S.QG ⊓ Subgroup.centralizer ({(τ : G)} : Set G), x * x = 1 := by
  classical
  let u : V₀ ≃ₗ[ZMod 2] V₀ := conjL L ↑(S.ρ τ⁻¹)
  have huKPGL : u ∈ KPGL := conjL_rho_mem_KPGL S hK τ⁻¹
  have huout : u ∉ KPGL0 := by
    change conjL L ↑(S.ρ τ⁻¹) ∉ KPGL0
    rw [show conjL L ↑(S.ρ τ⁻¹) = (conjL L ↑(S.ρ τ))⁻¹ from
      conjL_rho_inv_eq_inv (S := S) (L := L) τ]
    exact fun h => hτout ((Subgroup.inv_mem_iff (H := KPGL0)).mp h)
  have husq : u * u = 1 := by
    change conjL L ↑(S.ρ τ⁻¹) * conjL L ↑(S.ρ τ⁻¹) = 1
    rw [show conjL L ↑(S.ρ τ⁻¹) = (conjL L ↑(S.ρ τ))⁻¹ from
      conjL_rho_inv_eq_inv (S := S) (L := L) τ]
    have hτ2' : (S.ρ τ) * (S.ρ τ) = 1 := by rw [← map_mul, hτ2, map_one]
    calc (conjL L ↑(S.ρ τ))⁻¹ * (conjL L ↑(S.ρ τ))⁻¹
        = (conjL L ↑(S.ρ τ) * conjL L ↑(S.ρ τ))⁻¹ := by group
      _ = (conjL L (↑(S.ρ τ) * ↑(S.ρ τ)))⁻¹ := by rw [map_mul]
      _ = (conjL L ↑((S.ρ τ) * (S.ρ τ)))⁻¹ := by rw [Subgroup.coe_mul]
      _ = 1 := by simp [hτ2']
  have hτQ : τ * τ ∈ S.Q := by rw [hτ2]; exact one_mem _
  obtain ⟨hcase, hfix⟩ := hPS (sqData S φ) hIS u huKPGL huout husq
  have hθlift : ∀ x, (rhoQ0 S φ τ x).v = u x.v := fun x => v_rhoQ0 S φ hφ τ x
  have hθσ : sqData S φ (rhoQ0 S φ τ) = 1 := by
    have hsub : (⟨τ * τ, hτQ⟩ : S.Q) = 1 := Subtype.ext hτ2
    rw [sqData_rhoQ0 S φ hτQ, hsub, map_one]
  have hfixτ := hfix (rhoQ0 S φ τ) hθlift (Or.inl hθσ)
  have hcardQ : Nat.card {x : S.Q // (x : S.M) * τ = τ * x} = 8 := by
    rw [card_centralizer_eq_ncard S φ τ]
    exact hfixτ.1
  have hcardG : Nat.card ↥(S.QG ⊓ Subgroup.centralizer ({(τ : G)} : Set G)) =
      Nat.card {q : S.Q // (q : S.M) * τ = τ * q} := by
    rw [show Nat.card ↥(S.QG ⊓ Subgroup.centralizer ({(τ : G)} : Set G)) =
        Nat.card {x : G // x ∈ S.QG ∧ x * (τ : G) = (τ : G) * x} from
      Nat.card_congr (Equiv.subtypeEquivRight (fun x => by
        rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]))]
    rw [Nat.card_congr (qgSubtypeEquiv S (fun x => x * (τ : G) = (τ : G) * x))]
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun q => by
      constructor
      · intro h
        apply Subtype.ext
        simpa using h
      · intro h
        have h' := congrArg (fun x : S.M => (x : G)) h
        simpa using h'))
  refine ⟨by rw [hcardG, hcardQ], ?_⟩
  intro x hx
  have hxQ : x ∈ S.QG := hx.1
  have hxc : x ∈ Subgroup.centralizer ({(τ : G)} : Set G) := hx.2
  have hxcomm : x * (τ : G) = (τ : G) * x :=
    (Subgroup.mem_centralizer_singleton_iff).mp hxc
  obtain ⟨hxM, hxq⟩ := S.mem_QG_iff.mp hxQ
  let q : S.Q := ⟨⟨x, hxM⟩, hxq⟩
  have hqcomm : (q : S.M) * τ = τ * q := by
    apply Subtype.ext
    simpa [q] using hxcomm
  have hfixq : rhoQ0 S φ τ (φ q) = φ q :=
    (rhoQ0_apply_eq_iff S φ τ q).mpr hqcomm
  have hsq : (φ q) * (φ q) = 1 := hfixτ.2.1 (φ q) hfixq
  have hqsq : q * q = 1 := φ.injective (by rw [map_mul, hsq, map_one])
  have hG : (x * x : G) = 1 := by
    have hcoe : ((q * q : S.Q) : G) = x * x := by
      simp [q]
    rw [← hcoe, hqsq]
    rfl
  exact hG

private theorem pgl_second_case
    (hK : mbarModel S L = KPGL)
    (hConj : ∀ u ∈ KPGL, u ∉ KPGL0 → u * u = 1 →
      ∀ u' ∈ KPGL, u' ∉ KPGL0 → u' * u' = 1 →
        ∃ k ∈ KPGL, k * u * k⁻¹ = u')
    (φ : S.Q ≃* Q0) (hφ : ∀ x : S.Q, (φ x).v = L (S.toQt x))
    (hIS : IsSquareData KPGL (sqData S φ))
    (u₀ : V₀ ≃ₗ[ZMod 2] V₀) (hu₀KPGL : u₀ ∈ KPGL) (hu₀not : u₀ ∉ KPGL0)
    (hu₀sq : u₀ * u₀ = 1)
    (hemptyOne : {θ : Q0 ≃* Q0 |
      (∀ x, (θ x).v = u₀ x.v) ∧ sqData S φ θ = 1} = ∅)
    (h8z : Set.ncard {θ : Q0 ≃* Q0 |
      (∀ x, (θ x).v = u₀ x.v) ∧ sqData S φ θ = z0} = 8) :
    (∀ y : S.M, conjL L ↑(S.ρ y) ∉ KPGL0 → y * y ≠ 1) ∧
    ∃ s : S.M, conjL L ↑(S.ρ s) ∉ KPGL0 ∧ (s : G) * s = S.z := by
  classical
  constructor
  · intro y hyout hy2
    let uy : V₀ ≃ₗ[ZMod 2] V₀ := conjL L ↑(S.ρ y⁻¹)
    have huyKPGL : uy ∈ KPGL := conjL_rho_mem_KPGL S hK y⁻¹
    have huyout : uy ∉ KPGL0 := by
      change conjL L ↑(S.ρ y⁻¹) ∉ KPGL0
      rw [show conjL L ↑(S.ρ y⁻¹) = (conjL L ↑(S.ρ y))⁻¹ from
        conjL_rho_inv_eq_inv (S := S) (L := L) y]
      exact fun h => hyout ((Subgroup.inv_mem_iff (H := KPGL0)).mp h)
    have huysq : uy * uy = 1 := by
      change conjL L ↑(S.ρ y⁻¹) * conjL L ↑(S.ρ y⁻¹) = 1
      rw [show conjL L ↑(S.ρ y⁻¹) = (conjL L ↑(S.ρ y))⁻¹ from
        conjL_rho_inv_eq_inv (S := S) (L := L) y]
      have hy2' : (S.ρ y) * (S.ρ y) = 1 := by rw [← map_mul, hy2, map_one]
      calc (conjL L ↑(S.ρ y))⁻¹ * (conjL L ↑(S.ρ y))⁻¹
          = (conjL L ↑(S.ρ y) * conjL L ↑(S.ρ y))⁻¹ := by group
        _ = (conjL L (↑(S.ρ y) * ↑(S.ρ y)))⁻¹ := by rw [map_mul]
        _ = (conjL L ↑((S.ρ y) * (S.ρ y)))⁻¹ := by rw [Subgroup.coe_mul]
        _ = 1 := by simp [hy2']
    obtain ⟨k, hkKPGL, hkconj⟩ := hConj uy huyKPGL huyout huysq u₀ hu₀KPGL hu₀not hu₀sq
    have hkmbar : k ∈ mbarModel S L := by rwa [hK]
    obtain ⟨m, hm⟩ := (mem_mbarModel_iff S L).mp hkmbar
    let y' : S.M := m * y * m⁻¹
    have hy'out : conjL L ↑(S.ρ y'⁻¹) = u₀ := by
      have hρ : (S.ρ y'⁻¹ : S.O) = S.ρ m * S.ρ y⁻¹ * S.ρ m⁻¹ := by
        change S.ρ ((m * y * m⁻¹)⁻¹) = S.ρ m * S.ρ y⁻¹ * S.ρ m⁻¹
        rw [show (m * y * m⁻¹)⁻¹ = m * y⁻¹ * m⁻¹ from by group]
        rw [map_mul, map_mul]
      have hconjm : conjL L ↑(S.ρ m⁻¹) = k⁻¹ := by
        rw [show conjL L ↑(S.ρ m⁻¹) = (conjL L ↑(S.ρ m))⁻¹ from
          conjL_rho_inv_eq_inv (S := S) (L := L) m, hm]
      rw [hρ]
      change conjL L (↑(S.ρ m) * ↑(S.ρ y⁻¹) * ↑(S.ρ m⁻¹)) = u₀
      rw [map_mul, map_mul, hconjm, hm]
      exact hkconj
    have hy'2 : y' * y' = 1 := by
      change (m * y * m⁻¹) * (m * y * m⁻¹) = 1
      rw [show (m * y * m⁻¹) * (m * y * m⁻¹) = m * (y * y) * m⁻¹ by group, hy2]
      group
    have hy'Q : y' * y' ∈ S.Q := by rw [hy'2]; exact one_mem _
    let θ' : Q0 ≃* Q0 := rhoQ0 S φ y'
    have hθ'lift : ∀ x, (θ' x).v = u₀ x.v := by
      intro x
      rw [show θ' = rhoQ0 S φ y' from rfl, v_rhoQ0 S φ hφ y' x, hy'out]
    have hθ'σ : sqData S φ θ' = 1 := by
      have hsub : (⟨y' * y', hy'Q⟩ : S.Q) = 1 := Subtype.ext hy'2
      rw [show θ' = rhoQ0 S φ y' from rfl, sqData_rhoQ0 S φ hy'Q, hsub, map_one]
    have hmem : θ' ∈ {θ : Q0 ≃* Q0 |
        (∀ x, (θ x).v = u₀ x.v) ∧ sqData S φ θ = 1} := ⟨hθ'lift, hθ'σ⟩
    rw [hemptyOne] at hmem
    exact hmem
  · have hne : ({θ : Q0 ≃* Q0 |
        (∀ x, (θ x).v = u₀ x.v) ∧ sqData S φ θ = z0} : Set (Q0 ≃* Q0)).Nonempty := by
      rw [← Set.ncard_pos]
      rw [h8z]
      norm_num
    obtain ⟨θ, hθlift, hθσ⟩ := hne
    have hθT : θ ∈ ThetaOver KPGL := ⟨u₀, hu₀KPGL, hu₀sq, hθlift⟩
    have hθX : θ ∈ XOver (mbarModel S L) := by
      rw [hK]
      exact ⟨u₀, hu₀KPGL, hθlift⟩
    obtain ⟨s, hsθ⟩ := exists_rhoQ0_eq S φ hφ hθX
    have hθTm : θ ∈ ThetaOver (mbarModel S L) := by rwa [hK]
    have hsQ : s * s ∈ S.Q := by
      rw [← rhoQ0_mem_ThetaOver_iff S φ hφ s, hsθ]
      exact hθTm
    have hsqz : (⟨s * s, hsQ⟩ : S.Q) = S.zQ := by
      apply φ.injective
      rw [← sqData_rhoQ0 S φ hsQ, hsθ, hθσ, phi_zQ S φ]
    have hs2 : (s : G) * s = S.z := by
      have h := congrArg (fun q : S.Q => (q : G)) hsqz
      simpa using h
    have hsu : conjL L ↑(S.ρ s⁻¹) = u₀ := by
      refine LinearEquiv.ext fun v => ?_
      obtain ⟨x, rfl⟩ : ∃ x : Q0, x.v = v := ⟨⟨0, v⟩, rfl⟩
      have h1 := hθlift x
      rw [← hsθ] at h1
      rw [← v_rhoQ0 S φ hφ s x]
      exact h1
    have hsout : conjL L ↑(S.ρ s) ∉ KPGL0 := by
      intro h
      apply hu₀not
      rw [← hsu]
      rw [conjL_rho_inv_eq_inv (S := S) (L := L) s]
      exact (Subgroup.inv_mem_iff (H := KPGL0)).mpr h
    exact ⟨s, hsout, hs2⟩

theorem pgl_exists_moved (hF : PGLFactsProp) (hPS : PGLSquareProp)
    (hL : ∀ v, qPlus (L v) = S.q v) (hK : mbarModel S L = KPGL) :
    ∀ y : S.M, conjL L ↑(S.ρ y) ∉ KPGL0 → ((y : G) * y = 1 ∨ (y : G) * y = S.z) →
      ∀ w : S.M, conjL L ↑(S.ρ w) ∈ KPGL0 → S.ρ w ≠ 1 → S.ρ w * S.ρ w = 1 →
        S.ρ w * S.ρ y = S.ρ y * S.ρ w →
        ∃ x ∈ S.QG ⊓ Subgroup.centralizer ({(y : G)} : Set G),
          (w : G) * x * (w : G)⁻¹ ≠ x ∧ (w : G) * x * (w : G)⁻¹ ≠ x * S.z := by
  classical
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_Q0 S hL
  have hIS : IsSquareData KPGL (sqData S φ) := by
    have h := isSquareData S φ hφ
    rwa [hK] at h
  intro y hyout hy2 w hwKPGL0 hwρne hwρsq hwcomm
  have hyQ : y * y ∈ S.Q := by
    rcases hy2 with h | h
    · have h' : y * y = 1 := Subtype.ext (by simpa using h)
      rw [h']; exact one_mem _
    · have h' : y * y = S.zM := Subtype.ext (by simpa using h)
      rw [h']; exact S.zM_mem_Q
  let u : V₀ ≃ₗ[ZMod 2] V₀ := conjL L ↑(S.ρ y⁻¹)
  have huKPGL : u ∈ KPGL := conjL_rho_mem_KPGL S hK y⁻¹
  have huout : u ∉ KPGL0 := by
    change conjL L ↑(S.ρ y⁻¹) ∉ KPGL0
    rw [show conjL L ↑(S.ρ y⁻¹) = (conjL L ↑(S.ρ y))⁻¹ from
      conjL_rho_inv_eq_inv (S := S) (L := L) y]
    exact fun h => hyout ((Subgroup.inv_mem_iff (H := KPGL0)).mp h)
  have hu_sq : u * u = 1 := by
    change conjL L ↑(S.ρ y⁻¹) * conjL L ↑(S.ρ y⁻¹) = 1
    have hyinvQ : y⁻¹ * y⁻¹ ∈ S.Q := by
      rw [show y⁻¹ * y⁻¹ = (y * y)⁻¹ from by group]
      exact S.Q.inv_mem hyQ
    have hρ1 : S.ρ (y⁻¹ * y⁻¹) = 1 := S.ρ_eq_one_of_mem_Q hyinvQ
    calc conjL L ↑(S.ρ y⁻¹) * conjL L ↑(S.ρ y⁻¹)
        = conjL L (↑(S.ρ y⁻¹) * ↑(S.ρ y⁻¹)) := by rw [map_mul]
      _ = conjL L ↑(S.ρ y⁻¹ * S.ρ y⁻¹) := by rw [Subgroup.coe_mul]
      _ = conjL L ↑(S.ρ (y⁻¹ * y⁻¹)) := by rw [map_mul]
      _ = 1 := by simp [hρ1]
  have hθlift : ∀ x, (rhoQ0 S φ y x).v = u x.v := fun x => v_rhoQ0 S φ hφ y x
  have hθσ : sqData S φ (rhoQ0 S φ y) = 1 ∨ sqData S φ (rhoQ0 S φ y) = z0 := by
    have h1 : sqData S φ (rhoQ0 S φ y) = φ (⟨y * y, hyQ⟩ : S.Q) :=
      sqData_rhoQ0 S φ hyQ
    rcases hy2 with h | h
    · left
      have h' : (⟨y * y, hyQ⟩ : S.Q) = 1 := by
        apply Subtype.ext
        apply Subtype.ext
        simpa using h
      rw [h1, h', map_one]
    · right
      have h' : (⟨y * y, hyQ⟩ : S.Q) = S.zQ := by
        apply Subtype.ext
        apply Subtype.ext
        simpa using h
      rw [h1, h', phi_zQ S φ]
  obtain ⟨-, hfix⟩ := hPS (sqData S φ) hIS u huKPGL huout hu_sq
  have hfixθ := hfix (rhoQ0 S φ y) hθlift hθσ
  let wbar : V₀ ≃ₗ[ZMod 2] V₀ := conjL L ↑(S.ρ w)
  have hwbar_ne : wbar ≠ 1 := by
    intro h
    change conjL L ↑(S.ρ w) = 1 at h
    exact hwρne (Subtype.ext ((conjL L).map_eq_one_iff.mp h))
  have hwbar_sq : wbar * wbar = 1 := by
    change conjL L ↑(S.ρ w) * conjL L ↑(S.ρ w) = 1
    calc conjL L ↑(S.ρ w) * conjL L ↑(S.ρ w)
        = conjL L (↑(S.ρ w) * ↑(S.ρ w)) := by rw [map_mul]
      _ = conjL L ↑(S.ρ w * S.ρ w) := by rw [Subgroup.coe_mul]
      _ = 1 := by simp [hwρsq]
  have hwbar_comm : wbar * u = u * wbar := by
    have hcomm_inv : (S.ρ w) * (S.ρ y⁻¹) = (S.ρ y⁻¹) * (S.ρ w) := by
      rw [show (S.ρ y⁻¹ : S.O) = (S.ρ y)⁻¹ from map_inv _ _]
      have h := congrArg (fun g : S.O => (S.ρ y)⁻¹ * g * (S.ρ y)⁻¹) hwcomm
      simpa [mul_assoc] using h.symm
    change conjL L ↑(S.ρ w) * conjL L ↑(S.ρ y⁻¹) =
      conjL L ↑(S.ρ y⁻¹) * conjL L ↑(S.ρ w)
    rw [← map_mul, ← map_mul]
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hcomm_inv]
  obtain ⟨x₀, hθx₀, hwx₀⟩ := hfixθ.2.2 wbar hwKPGL0 hwbar_ne hwbar_sq hwbar_comm
  let x : S.Q := φ.symm x₀
  have hφx : φ x = x₀ := MulEquiv.apply_symm_apply φ x₀
  have hxQG : (x : G) ∈ S.QG := Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩
  have hxcomm : (x : S.M) * y = y * x := by
    apply (rhoQ0_apply_eq_iff S φ y x).mp
    rw [hφx]
    exact hθx₀
  have hxC : (x : G) ∈ Subgroup.centralizer ({(y : G)} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg (fun g : S.M => (g : G)) hxcomm
  refine ⟨(x : G), ⟨hxQG, hxC⟩, ?_, ?_⟩
  · intro h
    apply hwx₀
    calc wbar x₀.v = (φ (conjAut S.normal w x)).v := by
          rw [v_φ_conjAut S φ hφ w x, hφx]
      _ = (φ x).v := by
          rw [show conjAut S.normal w x = x from by
            apply Subtype.ext
            apply Subtype.ext
            simpa [conjAut_apply, Subgroup.coe_mul] using h]
      _ = x₀.v := by rw [hφx]
  · intro h
    apply hwx₀
    calc wbar x₀.v = (φ (conjAut S.normal w x)).v := by
          rw [v_φ_conjAut S φ hφ w x, hφx]
      _ = (φ (x * S.zQ)).v := by
          rw [show conjAut S.normal w x = x * S.zQ from by
            apply Subtype.ext
            apply Subtype.ext
            simpa [conjAut_apply, Subgroup.coe_mul] using h]
      _ = (φ x * φ S.zQ).v := by rw [map_mul]
      _ = (φ x * z0).v := by rw [phi_zQ S φ]
      _ = (φ x).v := by simp [z0]
      _ = x₀.v := by rw [hφx]

theorem pgl_square_cases (hF : PGLFactsProp) (hPS : PGLSquareProp)
    (hL : ∀ v, qPlus (L v) = S.q v) (hK : mbarModel S L = KPGL) :
    ((∃ τ : S.M, conjL L ↑(S.ρ τ) ∉ KPGL0 ∧ τ * τ = 1) ∧
        ∀ τ : S.M, conjL L ↑(S.ρ τ) ∉ KPGL0 → τ * τ = 1 →
          Nat.card {x : G // x ∈ S.QG ∧ ((τ : G) * x) * ((τ : G) * x) = 1} = 16 ∧
          Nat.card ↥(S.QG ⊓ Subgroup.centralizer ({(τ : G)} : Set G)) = 8 ∧
          ∀ x ∈ S.QG ⊓ Subgroup.centralizer ({(τ : G)} : Set G), x * x = 1) ∨
      ((∀ y : S.M, conjL L ↑(S.ρ y) ∉ KPGL0 → y * y ≠ 1) ∧
        ∃ s : S.M, conjL L ↑(S.ρ s) ∉ KPGL0 ∧ (s : G) * s = S.z) := by
  classical
  obtain ⟨u₀, hu₀KPGL, hu₀not, hu₀sq⟩ := exists_outer_involution_KPGL hF
  obtain ⟨hKO, hcardK, hderiv, hcardK0, hVPlusSing, hVStarSing, hVInf, hVSup,
    hPres, hSwap, hIrr, hTrans, hNoCensus, hCentOut, hConjOut, hCentIn⟩ := hF
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_Q0 S hL
  have hIS : IsSquareData KPGL (sqData S φ) := by
    have h := isSquareData S φ hφ
    rwa [hK] at h
  have hu₀mbar : u₀ ∈ mbarModel S L := by rwa [hK]
  obtain ⟨m₀, hm₀⟩ := (mem_mbarModel_iff S L).mp hu₀mbar
  let y₀ : S.M := m₀⁻¹
  have hy₀ : conjL L ↑(S.ρ y₀⁻¹) = u₀ := by
    change conjL L ↑(S.ρ (m₀⁻¹)⁻¹) = u₀
    rw [inv_inv]
    exact hm₀
  have hy₀T : rhoQ0 S φ y₀ ∈ ThetaOver (mbarModel S L) :=
    ⟨conjL L ↑(S.ρ y₀⁻¹),
      conjL_ρ_mem_mbarModel S L y₀⁻¹, by rw [hy₀]; exact hu₀sq,
      fun x => v_rhoQ0 S φ hφ y₀ x⟩
  have hy₀Q : y₀ * y₀ ∈ S.Q :=
    (rhoQ0_mem_ThetaOver_iff S φ hφ y₀).mp hy₀T
  obtain ⟨hcase, hfix⟩ := hPS (sqData S φ) hIS u₀ hu₀KPGL hu₀not hu₀sq
  rcases hcase with ⟨h8one, hemptyZ⟩ | ⟨hemptyOne, h8z⟩
  · left
    have hcount := card_mul_sq_eq S φ hφ hy₀Q (1 : S.Q)
    have hset : {θ : Q0 ≃* Q0 |
        (∀ e, (θ e).v = conjL L ↑(S.ρ y₀⁻¹) e.v) ∧ sqData S φ θ = φ 1} =
        {θ : Q0 ≃* Q0 | (∀ x, (θ x).v = u₀ x.v) ∧ sqData S φ θ = 1} := by
      rw [hy₀, map_one]
    have hcardQ16 : Nat.card {x : S.Q //
        (y₀ * (x : S.M)) * (y₀ * (x : S.M)) = ((1 : S.Q) : S.M)} = 16 := by
      rw [hcount, hset, h8one]
    have hnonempty : Nonempty {x : S.Q //
        (y₀ * (x : S.M)) * (y₀ * (x : S.M)) = ((1 : S.Q) : S.M)} := by
      rw [← Finite.card_pos_iff, hcardQ16]
      norm_num
    obtain ⟨x, hx2⟩ := hnonempty
    let τ : S.M := y₀ * (x : S.M)
    have hτ2 : τ * τ = 1 := by
      change (y₀ * (x : S.M)) * (y₀ * (x : S.M)) = 1
      exact hx2
    have hτu : conjL L ↑(S.ρ τ⁻¹) = u₀ := by
      have hρx : S.ρ (x : S.M) = 1 := S.ρ_eq_one_of_mem_Q x.2
      have hρ : (S.ρ τ⁻¹ : S.O) = S.ρ y₀⁻¹ := by
        change S.ρ (y₀ * (x : S.M))⁻¹ = S.ρ y₀⁻¹
        rw [mul_inv_rev, map_mul, map_inv, hρx, inv_one, one_mul]
      rw [hρ, hy₀]
    have hτout : conjL L ↑(S.ρ τ) ∉ KPGL0 := by
      rw [conjL_rho_outer_iff (S := S) (L := L) τ]
      rw [hτu]
      exact hu₀not
    refine ⟨⟨τ, hτout, hτ2⟩, ?_⟩
    intro τ hτout hτ2
    exact ⟨pgl_card_mul_sq S hPS hK φ hφ hIS hτout hτ2,
      (pgl_card_centralizer S hPS hK φ hφ hIS hτout hτ2).1,
      (pgl_card_centralizer S hPS hK φ hφ hIS hτout hτ2).2⟩
  · right
    exact pgl_second_case S hK hConjOut φ hφ hIS u₀ hu₀KPGL hu₀not hu₀sq hemptyOne h8z

end CFSG.GF2Type.Smith1979W3

end
