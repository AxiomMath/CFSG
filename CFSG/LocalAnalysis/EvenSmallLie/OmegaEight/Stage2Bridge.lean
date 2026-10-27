module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Coord
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Model

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage2

open Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar

@[expose] def phiMat : Mat12 := Matrix.of fun i j =>
  if (i : ℕ) / 2 = (j : ℕ) / 2 then
    (if (i : ℕ) % 2 = 0 then 1 else (if (j : ℕ) % 2 = 1 then 1 else 0)) else 0

theorem toMatK_phiK : toMatK phiK = phiMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem invPair_phiK : invPair phiK phiK = true := by decide

theorem rep_tbarG : Rep phiK tbarG := rep_glOf invPair_phiK

@[expose] def kronMat (A : Matrix (Fin 6) (Fin 6) (ZMod 2)) : Mat12 := Matrix.of fun i j =>
  if (i : ℕ) % 2 = (j : ℕ) % 2 then A ⟨(i : ℕ) / 2, by omega⟩ ⟨(j : ℕ) / 2, by omega⟩ else 0

@[expose] def kronK (rows : Array ℕ) : ℕ :=
  keyOf (Array.ofFn (n := 12) fun r =>
    bitsOf 12 fun p => (p % 2 == (r : ℕ) % 2) && (rows.getD ((r : ℕ) / 2) 0).testBit (p / 2))

theorem toMatK_kronK (rows : Array ℕ) : toMatK (kronK rows) = kronMat (toMat 6 6 rows) := by
  ext i j
  rw [kronK, toMatK_keyOf, toMat_apply, getD_ofFn, testBit_bitsOf, kronMat, Matrix.of_apply,
    toMat_apply]
  simp only [j.isLt, decide_true, Bool.true_and]
  by_cases h : (i : ℕ) % 2 = (j : ℕ) % 2
  · rw [ite_eq_left h]
    simp [h]
  · rw [ite_eq_right h]
    have h' : ((j : ℕ) % 2 == (i : ℕ) % 2) = false := by simp [Ne.symm h]
    simp [h']

theorem aPart_single_even {j : Fin 12} (hj : (j : ℕ) % 2 = 0) :
    aPart (Pi.single j 1) = Pi.single ⟨(j : ℕ) / 2, by omega⟩ 1 := by
  ext i
  simp only [aPart, Pi.single_apply, Fin.ext_iff]
  congr 1
  apply propext
  omega

theorem bPart_single_even {j : Fin 12} (hj : (j : ℕ) % 2 = 0) : bPart (Pi.single j 1) = 0 := by
  ext i
  simp only [bPart, Pi.single_apply, Fin.ext_iff, Pi.zero_apply]
  rw [ite_eq_right (by omega)]

theorem aPart_single_odd {j : Fin 12} (hj : (j : ℕ) % 2 = 1) : aPart (Pi.single j 1) = 0 := by
  ext i
  simp only [aPart, Pi.single_apply, Fin.ext_iff, Pi.zero_apply]
  rw [ite_eq_right (by omega)]

theorem bPart_single_odd {j : Fin 12} (hj : (j : ℕ) % 2 = 1) :
    bPart (Pi.single j 1) = Pi.single ⟨(j : ℕ) / 2, by omega⟩ 1 := by
  ext i
  simp only [bPart, Pi.single_apply, Fin.ext_iff]
  congr 1
  apply propext
  omega

theorem eq_phiMat {M : Mat12} (h : ∀ v, M *ᵥ v = join (aPart v + bPart v) (bPart v)) :
    M = phiMat := by
  ext i j
  have e := congrFun (h (Pi.single j 1)) i
  rw [mulVec_single_one] at e
  change M i j = _ at e
  rw [e]
  rcases Nat.mod_two_eq_zero_or_one (j : ℕ) with hj | hj
  · rw [aPart_single_even hj, bPart_single_even hj, add_zero]
    simp only [join, phiMat, Matrix.of_apply, Pi.single_apply, Fin.ext_iff, Pi.zero_apply]
    split_ifs <;> first | rfl | omega
  · rw [aPart_single_odd hj, bPart_single_odd hj, zero_add]
    simp only [join, phiMat, Matrix.of_apply, Pi.single_apply, Fin.ext_iff]
    split_ifs <;> rfl

theorem eq_kronMat {M : Mat12} {A : Matrix (Fin 6) (Fin 6) (ZMod 2)}
    (h : ∀ v, M *ᵥ v = join (A *ᵥ aPart v) (A *ᵥ bPart v)) : M = kronMat A := by
  ext i j
  have e := congrFun (h (Pi.single j 1)) i
  rw [mulVec_single_one] at e
  change M i j = _ at e
  rw [e]
  rcases Nat.mod_two_eq_zero_or_one (j : ℕ) with hj | hj
  · rw [aPart_single_even hj, bPart_single_even hj, mulVec_single_one, mulVec_zero]
    simp only [join, kronMat, Matrix.of_apply, Pi.zero_apply, Matrix.col_apply]
    split_ifs <;> first | rfl | omega
  · rw [aPart_single_odd hj, bPart_single_odd hj, mulVec_single_one, mulVec_zero]
    simp only [join, kronMat, Matrix.of_apply, Pi.zero_apply, Matrix.col_apply]
    split_ifs <;> first | rfl | omega

namespace CoordHyp

variable {G : Type*} [Group G] [Finite G] {t : G} {Q R W : Subgroup G} {ψ : Vec6 → G}

theorem rhoG_mulVec_Phi (h : CoordHyp t Q R W ψ) {g : G} (hg : g ∈ NW W) {f : Vec12 → Vec12}
    (hf : ∀ v, g * Phi t R ψ v * g⁻¹ = Phi t R ψ (f v)) (v : Vec12) :
    (rhoG W h.coordEquiv g : Mat12) *ᵥ v = f v := by
  have e := rhoG_mulVec (φ := h.coordEquiv) hg (h.coordEquiv.symm (Multiplicative.ofAdd v))
  rw [MulEquiv.apply_symm_apply, toAdd_ofAdd] at e
  rw [e]
  have e2 : (⟨g * ((h.coordEquiv.symm (Multiplicative.ofAdd v) : W) : G) * g⁻¹,
      (Subgroup.mem_normalizer_iff.1 hg _).1 (h.coordEquiv.symm _).2⟩ : W) =
      ⟨Phi t R ψ (f v), h.Phi_mem _⟩ := Subtype.ext (show
        g * ((h.coordEquiv.symm (Multiplicative.ofAdd v) : W) : G) * g⁻¹ = Phi t R ψ (f v) by
        rw [h.coordEquiv_symm_apply, hf])
  rw [e2, h.coordEquiv_Phi, toAdd_ofAdd]

theorem rhoG_t_eq (h : CoordHyp t Q R W ψ) : rhoG W h.coordEquiv t = tbarG := by
  apply Units.ext
  rw [← rep_tbarG, toMatK_phiK]
  exact eq_phiMat (h.rhoG_mulVec_Phi h.t_mem (h.conj_t_Phi))

theorem rep_rhoG_of_act (h : CoordHyp t Q R W ψ) {p : G} (hpN : p ∈ NW W) (hpt : p * t = t * p)
    (hpR : ∀ r ∈ R, p * r * p⁻¹ ∈ R) {rows : Array ℕ}
    (hA : ∀ x, p * ψ x * p⁻¹ = ψ (toMat 6 6 rows *ᵥ x)) :
    Rep (kronK rows) (rhoG W h.coordEquiv p) := by
  rw [Rep, toMatK_kronK]
  exact (eq_kronMat (h.rhoG_mulVec_Phi hpN (h.conj_Phi_of_act hpt hpR hA))).symm

end CoordHyp

variable {G : Type*} [Group G]

structure BridgeModel (M : Model) {m n : ℕ} (pr : Fin m → Array ℕ) (ur : Fin n → Array ℕ) :
    Prop where
  tbar_eq : M.tbar = tbarG
  tbar_mem_TC : tbarG ∈ M.TC
  tbar_mem_CC : tbarG ∈ M.CC
  CC_p : ∀ i, ∀ x : GL12, Rep (kronK (pr i)) x → x ∈ M.CC
  CC_le : M.CC ≤ Subgroup.closure ({tbarG} ∪ {x | ∃ i, Rep (kronK (pr i)) x})
  TC_u : ∀ k, ∀ x : GL12, Rep (kronK (ur k)) x → x ∈ M.TC
  TC_le : M.TC ≤ Subgroup.closure ({tbarG} ∪ {x | ∃ k, Rep (kronK (ur k)) x})

open Subgroup in
structure BridgeCore (t : G) (Q R W P U : Subgroup G) (ψ : Vec6 → G) {m n : ℕ}
    (pr : Fin m → Array ℕ) (p : Fin m → G) (ur : Fin n → Array ℕ) (u : Fin n → G) : Prop where
  coord : CoordHyp t Q R W ψ
  orderOf_t : orderOf t = 2
  P_le_normalizer : P ≤ normalizer (W : Set G)
  P_le_normalizer_R : P ≤ normalizer (R : Set G)
  P_le_centralizer : P ≤ centralizer ({t} : Set G)
  p_mem : ∀ i, p i ∈ P
  p_act : ∀ i x, p i * ψ x * (p i)⁻¹ = ψ (toMat 6 6 (pr i) *ᵥ x)
  P_le : P ≤ Subgroup.closure ((Q : Set G) ∪ Set.range p)
  U_le_P : U ≤ P
  u_mem : ∀ k, u k ∈ U
  u_act : ∀ k x, u k * ψ x * (u k)⁻¹ = ψ (toMat 6 6 (ur k) *ᵥ x)
  U_le : U ≤ Subgroup.closure ((Q : Set G) ∪ Set.range u)
  TH_pgroup : IsPGroup 2 (U ⊔ zpowers t : Subgroup G)
  TH_max : ∀ V : Subgroup G, V ≤ centralizer ({t} : Set G) → IsPGroup 2 V → U ⊔ zpowers t ≤ V →
    V = U ⊔ zpowers t
  sylow_W : ∀ S : Subgroup G, S ≤ centralizer (W : Set G) → IsPGroup 2 S → S ≤ W
  centralizer_t : ∀ x ∈ normalizer (W : Set G), x * t * x⁻¹ * t⁻¹ ∈ centralizer (W : Set G) →
    x ∈ centralizer (W : Set G) ⊔ (P ⊔ zpowers t)

namespace BridgeCore

open Subgroup

variable {M : Model} {t : G} {Q R W P U : Subgroup G} {ψ : Vec6 → G} {m n : ℕ}
  {pr : Fin m → Array ℕ} {p : Fin m → G} {ur : Fin n → Array ℕ} {u : Fin n → G}

theorem mem_P (hB : BridgeCore t Q R W P U ψ pr p ur u) {x : G} (hx : x ∈ P) :
    x ∈ NW W ∧ x * t = t * x ∧ ∀ r ∈ R, x * r * x⁻¹ ∈ R :=
  ⟨hB.P_le_normalizer hx, mem_centralizer_singleton_iff.1 (hB.P_le_centralizer hx),
    fun r hr => (mem_normalizer_iff.1 (hB.P_le_normalizer_R hx) r).1 hr⟩

theorem rep_p [Finite G] (hB : BridgeCore t Q R W P U ψ pr p ur u) (i : Fin m) :
    Rep (kronK (pr i)) (rhoG W hB.coord.coordEquiv (p i)) := by
  obtain ⟨h1, h2, h3⟩ := hB.mem_P (hB.p_mem i)
  exact hB.coord.rep_rhoG_of_act h1 h2 h3 (hB.p_act i)

theorem rep_u [Finite G] (hB : BridgeCore t Q R W P U ψ pr p ur u) (k : Fin n) :
    Rep (kronK (ur k)) (rhoG W hB.coord.coordEquiv (u k)) := by
  obtain ⟨h1, h2, h3⟩ := hB.mem_P (hB.U_le_P (hB.u_mem k))
  exact hB.coord.rep_rhoG_of_act h1 h2 h3 (hB.u_act k)

theorem Q_le_rhoPre [Finite G] (hB : BridgeCore t Q R W P U ψ pr p ur u) (Y : Subgroup GL12) :
    Q ≤ rhoPre W hB.coord.coordEquiv Y := fun q hq => by
  have hqW := hB.coord.Q_le_W hq
  refine mem_rhoPre.2 ⟨W_le_NW hqW, ?_⟩
  rw [rhoG_W (φ := hB.coord.coordEquiv) hqW]
  exact one_mem Y

theorem P_le_rhoPre [Finite G] (hB : BridgeCore t Q R W P U ψ pr p ur u)
    (hM : BridgeModel M pr ur) :
    P ≤ rhoPre W hB.coord.coordEquiv M.CC := by
  refine hB.P_le.trans ((closure_le _).2 ?_)
  rintro x (hx | ⟨i, rfl⟩)
  · exact hB.Q_le_rhoPre M.CC hx
  · exact mem_rhoPre.2 ⟨(hB.mem_P (hB.p_mem i)).1, hM.CC_p i _ (hB.rep_p i)⟩

theorem U_le_rhoPre [Finite G] (hB : BridgeCore t Q R W P U ψ pr p ur u)
    (hM : BridgeModel M pr ur) :
    U ≤ rhoPre W hB.coord.coordEquiv M.TC := by
  refine hB.U_le.trans ((closure_le _).2 ?_)
  rintro x (hx | ⟨k, rfl⟩)
  · exact hB.Q_le_rhoPre M.TC hx
  · exact mem_rhoPre.2 ⟨(hB.mem_P (hB.U_le_P (hB.u_mem k))).1, hM.TC_u k _ (hB.rep_u k)⟩

theorem t_mem_rhoPre [Finite G] (hB : BridgeCore t Q R W P U ψ pr p ur u) {Y : Subgroup GL12}
    (hY : tbarG ∈ Y) : t ∈ rhoPre W hB.coord.coordEquiv Y :=
  mem_rhoPre.2 ⟨hB.coord.t_mem, by rw [hB.coord.rhoG_t_eq]; exact hY⟩

theorem TH_index [Finite G] (hB : BridgeCore t Q R W P U ψ pr p ur u) :
    ¬ 2 ∣ ((U ⊔ zpowers t).subgroupOf (centralizer ({t} : Set G))).index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := centralizer ({t} : Set G)
  have hTH : U ⊔ zpowers t ≤ H := sup_le (hB.U_le_P.trans hB.P_le_centralizer)
    ((zpowers_le).2 (mem_centralizer_singleton_iff.2 rfl))
  have hp : IsPGroup 2 ((U ⊔ zpowers t).subgroupOf H) :=
    hB.TH_pgroup.of_equiv (subgroupOfEquivOfLe hTH).symm
  let S : Sylow 2 H :=
    { toSubgroup := (U ⊔ zpowers t).subgroupOf H
      isPGroup' := hp
      is_maximal' := fun {Q'} hQ' hle => by
        have hV := hB.TH_max (Q'.map H.subtype) (map_subtype_le _) (hQ'.map _) (fun x hx =>
          ⟨⟨x, hTH hx⟩, hle (mem_subgroupOf.2 hx), rfl⟩)
        ext y
        constructor
        · intro hy
          have : (y : G) ∈ Q'.map H.subtype := ⟨y, hy, rfl⟩
          rw [hV] at this
          exact mem_subgroupOf.2 this
        · intro hy
          exact hle hy }
  exact S.not_dvd_index

theorem stage2Hyp [Finite G] (hB : BridgeCore t Q R W P U ψ pr p ur u)
    (hM : BridgeModel M pr ur) :
    Stage2Hyp M t (U ⊔ zpowers t) W hB.coord.coordEquiv where
  orderOf_t := hB.orderOf_t
  t_mem := mem_sup_right (mem_zpowers t)
  TH_le := sup_le (hB.U_le_P.trans hB.P_le_centralizer)
    ((zpowers_le).2 (mem_centralizer_singleton_iff.2 rfl))
  TH_pgroup := hB.TH_pgroup
  TH_index := hB.TH_index
  TH_le_normalizer := sup_le (hB.U_le_P.trans hB.P_le_normalizer) ((zpowers_le).2 hB.coord.t_mem)
  sylow_W := hB.sylow_W
  rho_t := by rw [hB.coord.rhoG_t_eq, hM.tbar_eq]
  rho_TH := fun x hx => (mem_rhoPre.1 ((sup_le (hB.U_le_rhoPre hM) ((zpowers_le).2
    (hB.t_mem_rhoPre hM.tbar_mem_TC))) hx)).2
  TC_le := by
    have hTN : U ⊔ zpowers t ≤ NW W :=
      sup_le (hB.U_le_P.trans hB.P_le_normalizer) ((zpowers_le).2 hB.coord.t_mem)
    have hle : M.TC ≤ rhoImg W hB.coord.coordEquiv (U ⊔ zpowers t) := by
      refine hM.TC_le.trans ((closure_le _).2 ?_)
      rintro x (hx | ⟨k, hk⟩)
      · rw [Set.mem_singleton_iff] at hx
        rw [hx, ← hB.coord.rhoG_t_eq]
        exact rhoG_mem_rhoImg hTN (mem_sup_right (mem_zpowers t))
      · rw [hk.unique (hB.rep_u k)]
        exact rhoG_mem_rhoImg hTN (mem_sup_left (hB.u_mem k))
    exact fun y hy => (mem_rhoImg hTN).1 (hle hy)
  CC_le := by
    have hle : M.CC ≤ Xof W hB.coord.coordEquiv := by
      refine hM.CC_le.trans ((closure_le _).2 ?_)
      rintro x (hx | ⟨i, hi⟩)
      · rw [Set.mem_singleton_iff] at hx
        rw [hx, ← hB.coord.rhoG_t_eq]
        exact rhoG_mem_Xof hB.coord.t_mem
      · rw [hi.unique (hB.rep_p i)]
        exact rhoG_mem_Xof (hB.mem_P (hB.p_mem i)).1
    exact fun y hy => mem_Xof.1 (hle hy)
  centralizer_le := by
    intro g hg hc
    have hc' : rhoG W hB.coord.coordEquiv (g * t * g⁻¹ * t⁻¹) = 1 := by
      have htN := hB.coord.t_mem
      rw [rhoG_mul (mul_mem (mul_mem hg htN) (inv_mem hg)) (inv_mem htN),
        rhoG_mul (mul_mem hg htN) (inv_mem hg), rhoG_mul hg htN, rhoG_inv hg, rhoG_inv htN,
        hB.coord.rhoG_t_eq]
      rw [hM.tbar_eq] at hc
      calc rhoG W hB.coord.coordEquiv g * tbarG * (rhoG W hB.coord.coordEquiv g)⁻¹ * tbarG⁻¹ =
          tbarG * rhoG W hB.coord.coordEquiv g * (rhoG W hB.coord.coordEquiv g)⁻¹ * tbarG⁻¹ := by
            rw [hc]
        _ = 1 := by group
    have hcW := mem_centralizer_of_rhoG_eq_one
      (mul_mem (mul_mem (mul_mem hg hB.coord.t_mem) (inv_mem hg)) (inv_mem hB.coord.t_mem)) hc'
    have hmem := hB.centralizer_t g hg hcW
    have hle : centralizer (W : Set G) ⊔ (P ⊔ zpowers t) ≤
        rhoPre W hB.coord.coordEquiv M.CC := by
      refine sup_le (fun c hc => mem_rhoPre.2 ⟨centralizer_le_NW hc, ?_⟩)
        (sup_le (hB.P_le_rhoPre hM) ((zpowers_le).2 (hB.t_mem_rhoPre hM.tbar_mem_CC)))
      rw [rhoG_eq_one_of_mem_centralizer hc]
      exact one_mem _
    exact (mem_rhoPre.1 (hle hmem)).2

end BridgeCore

end CFSG.EvenSmallLie.OmegaEight.Stage2
