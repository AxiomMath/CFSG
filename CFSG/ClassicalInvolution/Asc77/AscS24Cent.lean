module

public import CFSG.ClassicalInvolution.Asc77.AscS24Exact

public section

namespace CFSG.ClassicalInvolution.Asc77.S24

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Disconnected
open CFSG.Open (classicalInvolutionOddCore IsElemAbelian)
open scoped commutatorElement MatrixGroups

set_option linter.unusedSectionVars false

section Generic

variable {G : Type} [Group G]

theorem commutatorElement_mul_of_comm {X Y a b : G} (hXa : X * a = a * X) (hXb : X * b = b * X)
    (hXY : X * Y = Y * X) (hYa : Y * a = a * Y) (hYb : Y * b = b * Y) :
    ⁅X * a, Y * b⁆ = ⁅a, b⁆ := by
  have hX : Commute X (a * Y * b * a⁻¹) :=
    (((Commute.mul_right hXa hXY).mul_right hXb).mul_right (Commute.inv_right hXa))
  have hY : Commute Y (b * a⁻¹ * b⁻¹) :=
    ((Commute.mul_right hYb (Commute.inv_right hYa)).mul_right (Commute.inv_right hYb))
  rw [commutatorElement_def, commutatorElement_def]
  calc X * a * (Y * b) * (X * a)⁻¹ * (Y * b)⁻¹
      = X * (a * Y * b * a⁻¹) * X⁻¹ * (b⁻¹ * Y⁻¹) := by group
    _ = a * Y * b * a⁻¹ * (b⁻¹ * Y⁻¹) := by rw [hX.eq]; group
    _ = a * (Y * (b * a⁻¹ * b⁻¹) * Y⁻¹) := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [hY.eq]; group

theorem le_centralizer_of_normalizes {F : Type*} [Field F] [Finite F] (h4 : 4 ≤ Nat.card F)
    {H O L : Subgroup G} (hO : H ≤ Subgroup.normalizer (O : Set G)) (hLH : L ≤ H)
    (e : ↥L ≃* SL(2, F)) {w : G} (hwO : w ∈ Subgroup.centralizer (O : Set G))
    (hwL : w ∈ Subgroup.normalizer (L : Set G)) (hnc : ∃ x ∈ L, x * w ≠ w * x) :
    L ≤ Subgroup.centralizer (O : Set G) := by
  have hconj : ∀ h ∈ H, ∀ t ∈ Subgroup.centralizer (O : Set G),
      h * t * h⁻¹ ∈ Subgroup.centralizer (O : Set G) := by
    intro h hh t ht
    rw [Subgroup.mem_centralizer_iff]
    intro o ho
    have ho' : h⁻¹ * o * h ∈ O := by
      have := (Subgroup.mem_normalizer_iff.mp (hO (H.inv_mem hh)) o).mp ho
      simpa using this
    have hc := Subgroup.mem_centralizer_iff.mp ht _ ho'
    calc o * (h * t * h⁻¹) = h * ((h⁻¹ * o * h) * t) * h⁻¹ := by group
      _ = h * (t * (h⁻¹ * o * h)) * h⁻¹ := by rw [hc]
      _ = h * t * h⁻¹ * o := by group
  let T : Subgroup ↥L := (Subgroup.centralizer (O : Set G)).subgroupOf L
  have hT : T.Normal := by
    constructor
    intro t ht ℓ
    rw [Subgroup.mem_subgroupOf] at ht ⊢
    have := hconj ℓ (hLH ℓ.2) t ht
    simpa using this
  have hcomm : ∀ ℓ ∈ L, (ℓ * w * ℓ⁻¹ * w⁻¹ ∈ L ∧
      ℓ * w * ℓ⁻¹ * w⁻¹ ∈ Subgroup.centralizer (O : Set G)) := by
    intro ℓ hℓ
    refine ⟨?_, ?_⟩
    · have h1 : w * ℓ⁻¹ * w⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp hwL ℓ⁻¹).mp (L.inv_mem hℓ)
      have e1 : ℓ * w * ℓ⁻¹ * w⁻¹ = ℓ * (w * ℓ⁻¹ * w⁻¹) := by group
      rw [e1]
      exact L.mul_mem hℓ h1
    · exact Subgroup.mul_mem _ (hconj ℓ (hLH hℓ) w hwO) (Subgroup.inv_mem _ hwO)
  have hperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp (isPerfect_of_equiv_sl2 h4 e)
  rcases normal_cases_of_equiv_sl2 h4 e T hT with h | h | h
  rotate_right
  · intro x hx
    have : (⟨x, hx⟩ : ↥L) ∈ T := by rw [h]; trivial
    exact Subgroup.mem_subgroupOf.mp this
  all_goals
    exfalso
    have hTc : T ≤ Subgroup.center ↥L := by rw [h]; try exact bot_le
    have hcen : ∀ ℓ ∈ L, ∀ m ∈ L, (ℓ * w * ℓ⁻¹ * w⁻¹) * m = m * (ℓ * w * ℓ⁻¹ * w⁻¹) := by
      intro ℓ hℓ m hm
      obtain ⟨h1, h2⟩ := hcomm ℓ hℓ
      have h3 : (⟨_, h1⟩ : ↥L) ∈ Subgroup.center ↥L := hTc (Subgroup.mem_subgroupOf.mpr h2)
      have := Subgroup.mem_center_iff.mp h3 ⟨m, hm⟩
      exact (congrArg Subtype.val this).symm
    have hLw : L ≤ Subgroup.centralizer ({w} : Set G) := by
      rw [← hperf, Subgroup.commutator_le]
      intro a ha b hb
      rw [Subgroup.mem_centralizer_singleton_iff]
      set X := (a * w * a⁻¹ * w⁻¹)⁻¹ with hXd
      set Y := (b * w * b⁻¹ * w⁻¹)⁻¹ with hYd
      have hXL : X ∈ L := L.inv_mem (hcomm a ha).1
      have hYL : Y ∈ L := L.inv_mem (hcomm b hb).1
      have cX : ∀ m ∈ L, X * m = m * X := fun m hm => by
        have := hcen a ha m hm
        rw [hXd]
        calc (a * w * a⁻¹ * w⁻¹)⁻¹ * m
            = (a * w * a⁻¹ * w⁻¹)⁻¹ * (m * (a * w * a⁻¹ * w⁻¹)) * (a * w * a⁻¹ * w⁻¹)⁻¹ := by
              group
          _ = (a * w * a⁻¹ * w⁻¹)⁻¹ * ((a * w * a⁻¹ * w⁻¹) * m) * (a * w * a⁻¹ * w⁻¹)⁻¹ := by
              rw [this]
          _ = m * (a * w * a⁻¹ * w⁻¹)⁻¹ := by group
      have cY : ∀ m ∈ L, Y * m = m * Y := fun m hm => by
        have := hcen b hb m hm
        rw [hYd]
        calc (b * w * b⁻¹ * w⁻¹)⁻¹ * m
            = (b * w * b⁻¹ * w⁻¹)⁻¹ * (m * (b * w * b⁻¹ * w⁻¹)) * (b * w * b⁻¹ * w⁻¹)⁻¹ := by
              group
          _ = (b * w * b⁻¹ * w⁻¹)⁻¹ * ((b * w * b⁻¹ * w⁻¹) * m) * (b * w * b⁻¹ * w⁻¹)⁻¹ := by
              rw [this]
          _ = m * (b * w * b⁻¹ * w⁻¹)⁻¹ := by group
      have hwa : w * a * w⁻¹ = X * a := by rw [hXd]; group
      have hwb : w * b * w⁻¹ = Y * b := by rw [hYd]; group
      have key : w * ⁅a, b⁆ * w⁻¹ = ⁅a, b⁆ := by
        calc w * ⁅a, b⁆ * w⁻¹ = ⁅w * a * w⁻¹, w * b * w⁻¹⁆ := by
              simp only [commutatorElement_def]; group
          _ = ⁅X * a, Y * b⁆ := by rw [hwa, hwb]
          _ = ⁅a, b⁆ := commutatorElement_mul_of_comm (cX a ha) (cX b hb) (cX Y hYL)
              (cY a ha) (cY b hb)
      exact (calc w * ⁅a, b⁆ = w * ⁅a, b⁆ * w⁻¹ * w := by group
        _ = ⁅a, b⁆ * w := by rw [key]).symm
    obtain ⟨x, hx, hxw⟩ := hnc
    exact hxw (Subgroup.mem_centralizer_singleton_iff.mp (hLw hx))

theorem mem_centralizer_oddCoreOf_of_alphaOf {A : Subgroup G} (hα : alphaOf A = ⊥) {a : G}
    (ha : a ∈ A) (ha1 : a ≠ 1) {b : G} (hb : b ∈ A) :
    b ∈ Subgroup.centralizer
      ((oddCoreOf (Subgroup.centralizer ({a} : Set G)) : Subgroup G) : Set G) := by
  have h1 : ⁅oddCoreOf (Subgroup.centralizer ({a} : Set G)), A⁆ ≤ alphaOf A := by
    refine le_sup_of_le_left ?_
    exact le_iSup₂_of_le a ha (le_iSup_of_le ha1 le_rfl)
  rw [hα] at h1
  rw [Subgroup.mem_centralizer_iff]
  intro o ho
  have h2 := h1 (Subgroup.commutator_mem_commutator ho hb)
  exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp h2)

end Generic

namespace Ctx


variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u g : G}
  (C : Ctx p f Ω K K' W S R R' z u g)

include C

theorem J_mem : conjSub g⁻¹ K ∈ Ω :=
  C.hs.stand.hyp.conjInvariant g⁻¹ K C.hs.stand.mem

theorem oddCore_J_eq_bot [IsSimpleGroup G]
    (hZ : W ⊓ centerIn (Subgroup.normalizer (W : Set G)) = ⊥)
    (hL : if piSign p f then LayerLieType p f Ω C.e0 .PSL 3
      else LayerLieType p f Ω C.e0 .PSU 3) :
    classicalInvolutionOddCore ↥(conjSub g⁻¹ K) = ⊥ :=
  C.exactMembers hZ hL _ C.J_mem

theorem oddCore_K_eq_bot [IsSimpleGroup G]
    (hZ : W ⊓ centerIn (Subgroup.normalizer (W : Set G)) = ⊥)
    (hL : if piSign p f then LayerLieType p f Ω C.e0 .PSL 3
      else LayerLieType p f Ω C.e0 .PSU 3) :
    classicalInvolutionOddCore ↥K = ⊥ :=
  C.exactMembers hZ hL _ C.hs.stand.mem

theorem K_le_centralizer_e0 [IsSimpleGroup G]
    (hZ : W ⊓ centerIn (Subgroup.normalizer (W : Set G)) = ⊥)
    (hL : if piSign p f then LayerLieType p f Ω C.e0 .PSL 3
      else LayerLieType p f Ω C.e0 .PSU 3) :
    K ≤ Subgroup.centralizer ({C.e0} : Set G) := by
  have hO : oddCoreOf K = ⊥ := C.oddCoreOf_K_eq_bot hZ hL
  have h := le_exactCore_of_central C.K_classical (C.e0_isPGroup hZ) (C.K_mem_tq_e0 hZ).2
    (by rw [hO]; exact bot_le)
  exact h.trans (exactCore_le_centralizer _ _)

theorem J_le_centralizer_e0 [IsSimpleGroup G]
    (hZ : W ⊓ centerIn (Subgroup.normalizer (W : Set G)) = ⊥)
    (hL : if piSign p f then LayerLieType p f Ω C.e0 .PSL 3
      else LayerLieType p f Ω C.e0 .PSU 3) :
    conjSub g⁻¹ K ≤ Subgroup.centralizer ({C.e0} : Set G) := by
  have hO : oddCoreOf (conjSub g⁻¹ K) = ⊥ := by
    have h3 := C.oddCore_J_eq_bot hZ hL
    show (classicalInvolutionOddCore ↥(conjSub g⁻¹ K)).map (conjSub g⁻¹ K).subtype = ⊥
    rw [h3, Subgroup.map_bot]
  have h := le_exactCore_of_central C.J_classical (C.e0_isPGroup hZ) (C.J_mem_tq_e0 hZ).2
    (by rw [hO]; exact bot_le)
  exact h.trans (exactCore_le_centralizer _ _)

theorem mem_centralizer_oddCore_e0 [IsSimpleGroup G]
    (hZ : W ⊓ centerIn (Subgroup.normalizer (W : Set G)) = ⊥)
    (hL : if piSign p f then LayerLieType p f Ω C.e0 .PSL 3
      else LayerLieType p f Ω C.e0 .PSU 3) :
    u ∈ Subgroup.centralizer
        ((oddCoreOf (Subgroup.centralizer ({C.e0} : Set G)) : Subgroup G) : Set G) ∧
      z ∈ Subgroup.centralizer
        ((oddCoreOf (Subgroup.centralizer ({C.e0} : Set G)) : Subgroup G) : Set G) := by
  have hα := C.alphaOf_eq_bot hZ hL
  have hAu : IsElemAbelian2 (Subgroup.closure ({C.e0, u} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair (C.e0_sq hZ) C.u_sq C.e0_ne_one C.u_ne_one
      (fun h => C.e0_not_mem (by rw [h]; exact Subgroup.subset_closure (by simp)))
      C.comm_ue.symm
  have hAuB : Subgroup.closure ({C.e0, u} : Set G) ≤ C.B := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact C.e0_mem_B
    · exact C.u_mem_B
  have hAz : IsElemAbelian2 (Subgroup.closure ({C.e0, z} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair (C.e0_sq hZ) C.z_sq C.e0_ne_one C.hs.hz.ne_one C.e0_ne_z
      C.comm_ze.symm
  have hAzB : Subgroup.closure ({C.e0, z} : Set G) ≤ C.B := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact C.e0_mem_B
    · exact C.z_mem_B
  exact ⟨mem_centralizer_oddCoreOf_of_alphaOf (hα _ hAuB hAu)
      (Subgroup.subset_closure (by simp)) C.e0_ne_one (Subgroup.subset_closure (by simp)),
    mem_centralizer_oddCoreOf_of_alphaOf (hα _ hAzB hAz)
      (Subgroup.subset_closure (by simp)) C.e0_ne_one (Subgroup.subset_closure (by simp))⟩

theorem normalizes_pair :
    u ∈ Subgroup.normalizer (K : Set G) ∧
      z ∈ Subgroup.normalizer ((conjSub g⁻¹ K : Subgroup G) : Set G) := by
  have hst := C.hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hJK : conjSub g⁻¹ K ≠ K := by
    have h := C.D.F.hne₁
    rw [C.hK, C.hJ] at h
    exact fun e => h e.symm
  have hρ := C.D.F.ρ.hRK
  have hρ₃ := C.D.F.ρ₃.hRK
  rw [C.hK] at hρ
  rw [C.hJ] at hρ₃
  obtain ⟨h1, h2⟩ := Thompson.inf_W_le_normalizer_of_ne hp hq hΩ C.hd.hW hst.mem C.J_mem
    hJK.symm C.D.F.ρ.hR C.D.F.ρ₃.hR hρ hρ₃
  exact ⟨h2 ⟨C.J_classical.mem, C.u_mem_W⟩, h1 ⟨C.hs.hz.mem, C.z_mem_W⟩⟩

theorem sup_le_centralizer_oddCore [IsSimpleGroup G]
    (hZ : W ⊓ centerIn (Subgroup.normalizer (W : Set G)) = ⊥)
    (hL : if piSign p f then LayerLieType p f Ω C.e0 .PSL 3
      else LayerLieType p f Ω C.e0 .PSU 3) :
    K ⊔ conjSub g⁻¹ K ≤ Subgroup.centralizer
      ((oddCoreOf (Subgroup.centralizer ({C.e0} : Set G)) : Subgroup G) : Set G) := by
  have hst := C.hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have h5 := (ModelFacts.odd_and_five_le_card_galoisField (p := p) hp hq).2
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by omega
  obtain ⟨eK⟩ := C.K_classical.nonempty_equiv_sl2 (C.oddCore_K_eq_bot hZ hL)
  obtain ⟨eJ⟩ := C.J_classical.nonempty_equiv_sl2 (C.oddCore_J_eq_bot hZ hL)
  have hO : Subgroup.centralizer ({C.e0} : Set G) ≤
      Subgroup.normalizer ((oddCoreOf (Subgroup.centralizer ({C.e0} : Set G)) :
        Subgroup G) : Set G) :=
    CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn _
  obtain ⟨huO, hzO⟩ := C.mem_centralizer_oddCore_e0 hZ hL
  obtain ⟨huN, hzN⟩ := C.normalizes_pair
  refine sup_le ?_ ?_
  · refine le_centralizer_of_normalizes h4 hO (C.K_le_centralizer_e0 hZ hL) eK huO huN
      ⟨C.D.F.ρ.r, ?_, fun h => ?_⟩
    · have := C.D.F.ρ.hRK.1 C.D.F.ρ.hr
      rwa [C.hK] at this
    · have h1 : C.D.F.ρ.r * u * C.D.F.ρ.r⁻¹ = u := by rw [h]; group
      rw [C.conj_r_u] at h1
      exact C.hs.hz.ne_one (by simpa using h1)
  · refine le_centralizer_of_normalizes h4 hO (C.J_le_centralizer_e0 hZ hL) eJ hzO hzN
      ⟨C.D.F.ρ₃.r, ?_, fun h => ?_⟩
    · have := C.D.F.ρ₃.hRK.1 C.D.F.ρ₃.hr
      rwa [C.hJ] at this
    · have h1 : C.D.F.ρ₃.r * z * C.D.F.ρ₃.r⁻¹ = z := by rw [h]; group
      rw [C.conj_s_z] at h1
      exact C.u_ne_one (by simpa using h1)

end Ctx

end CFSG.ClassicalInvolution.Asc77.S24
