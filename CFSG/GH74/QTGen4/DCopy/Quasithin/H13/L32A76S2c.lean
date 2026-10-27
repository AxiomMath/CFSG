module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.L32A76S2c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A705a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A705b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A76S2b

public section

namespace CFSG.Quasithin.H13.L32A.S2

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.Q511 CFSG.Quasithin.H13.L32A.M76 CFSG.Quasithin.F7
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H Y : Subgroup G} {γ γ' : F8.Geom T L H}
  {g : ↥((L ⊔ T) ⊔ H)}

namespace Ctx_F4
open CFSG.Quasithin.H13.L32A.S2.Ctx_F4

variable (C : Ctx_F4 G T L V H Y)
include C

theorem UH_le_H_F4 : conjClosure V H ≤ H :=
  C.h91_F4.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)

theorem commHom_rho_F4 [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V H)))] (u : ↥H)
    {x : G} (hx : x ∈ conjClosure V H) :
    ((commHom (FixR.rho C.h91_F4 u)
        ⟨secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V)
          ⟨x, C.h91_F4.H_normalizes_V₁ (C.UH_le_H_F4 hx)⟩, secMk_mem_secImg hx⟩ :
        ↥(tildeOf (fsuV1 T V) (conjClosure V H))) :
        SecQuot (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V)) =
      secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V)
        ⟨(u : G) * x * (u : G)⁻¹ * x⁻¹, C.h91_F4.H_normalizes_V₁ (H.mul_mem (H.mul_mem
          (H.mul_mem u.2 (C.UH_le_H_F4 hx)) (H.inv_mem u.2)) (H.inv_mem (C.UH_le_H_F4 hx)))⟩ := by
  rw [commHom_apply, Subgroup.coe_mul, Subgroup.coe_inv, FixR.rho_coe, FixR.sig_apply,
    ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
  rfl

theorem rkIdx_fixV_autOn_F4 [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V H)))]
    {B : Subgroup G} (hBH : B ≤ H) :
    rkIdx (fixV (autOn (tildeOf (fsuV1 T V) B) (tildeOf (fsuV1 T V) (conjClosure V H)))) =
      mIdx (conjClosure V H) (centralizerMod (fsuV1 T V) (conjClosure V H) B) := by
  have hŨ := C.h91_F4.isElemAbelian_tilde
  have hn := HypF91.tilde_le_normalizer (V₁ := fsuV1 T V) (Vp := V) hBH
  have c2 := card_fixV_autOn_eq hŨ hn
  have c3 := C.h91_F4.relIndex_tilde_fixV hBH
  set K := tildeOf (fsuV1 T V) (conjClosure V H) ⊓ Subgroup.centralizer (tildeOf (fsuV1 T V) B :
    Set (SecQuot (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V))) with hK
  have hmul := Subgroup.relIndex_mul_card K (tildeOf (fsuV1 T V) (conjClosure V H))
  rw [inf_eq_left.mpr (inf_le_left : K ≤ tildeOf (fsuV1 T V) (conjClosure V H))] at hmul
  have hmul' := Subgroup.index_mul_card
    (fixV (autOn (tildeOf (fsuV1 T V) B) (tildeOf (fsuV1 T V) (conjClosure V H))))
  have hpos : 0 < Nat.card ↥K := Nat.card_pos
  have hidx : (fixV (autOn (tildeOf (fsuV1 T V) B)
      (tildeOf (fsuV1 T V) (conjClosure V H)))).index = K.relIndex
        (tildeOf (fsuV1 T V) (conjClosure V H)) := by
    have e : (fixV (autOn (tildeOf (fsuV1 T V) B) (tildeOf (fsuV1 T V) (conjClosure V H)))).index *
        Nat.card ↥K = K.relIndex (tildeOf (fsuV1 T V) (conjClosure V H)) * Nat.card ↥K := by
      calc (fixV (autOn (tildeOf (fsuV1 T V) B)
            (tildeOf (fsuV1 T V) (conjClosure V H)))).index * Nat.card ↥K
          = (fixV (autOn (tildeOf (fsuV1 T V) B)
            (tildeOf (fsuV1 T V) (conjClosure V H)))).index * Nat.card ↥(fixV (autOn
              (tildeOf (fsuV1 T V) B) (tildeOf (fsuV1 T V) (conjClosure V H)))) := by rw [c2]
        _ = _ := hmul'
        _ = K.relIndex (tildeOf (fsuV1 T V) (conjClosure V H)) * Nat.card ↥K := hmul.symm
    exact Nat.eq_of_mul_eq_mul_right hpos e
  unfold rkIdx mIdx
  rw [hidx, c3]

theorem unpack_F4 [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V H)))]
    (s : F8Setup T V L H γ γ' g)
    (hpos : 0 < mIdx (F8.Uγ V H (g : G)) (F8.Dγ V (fsuV1 T V) H (g : G)))
    (hle : mIdx (conjClosure V H) (F8.DH V (fsuV1 T V) H (g : G)) ≤
      mIdx (F8.Uγ V H (g : G)) (F8.Dγ V (fsuV1 T V) H (g : G))) :
    autOn (tildeOf (fsuV1 T V) (F8.Uγ V H (g : G))) (tildeOf (fsuV1 T V) (conjClosure V H)) ≤
        autOn (tildeOf (fsuV1 T V) H) (tildeOf (fsuV1 T V) (conjClosure V H)) ∧
      autOn (tildeOf (fsuV1 T V) (F8.Uγ V H (g : G))) (tildeOf (fsuV1 T V) (conjClosure V H)) ≠
        ⊥ ∧
      IsElemAbelian2
        (autOn (tildeOf (fsuV1 T V) (F8.Uγ V H (g : G))) (tildeOf (fsuV1 T V) (conjClosure V H))) ∧
      IsQuadratic
        (autOn (tildeOf (fsuV1 T V) (F8.Uγ V H (g : G))) (tildeOf (fsuV1 T V) (conjClosure V H))) ∧
      rkIdx (fixV (autOn (tildeOf (fsuV1 T V) (F8.Uγ V H (g : G)))
          (tildeOf (fsuV1 T V) (conjClosure V H)))) ≤
        2 * rk (autOn (tildeOf (fsuV1 T V) (F8.Uγ V H (g : G)))
          (tildeOf (fsuV1 T V) (conjClosure V H))) := by
  obtain ⟨⟨hA2, hr⟩, hk⟩ := (C.h98.F916_2 s hpos hle).1
  refine ⟨hA2.1, hA2.2.1, hA2.2.2, (isQuadratic_iff_commSeries_two _).mpr hk, ?_⟩
  have hmul := hA2.rAV_mul
  have hpos' : (0 : ℚ) < (rk (autOn (tildeOf (fsuV1 T V) (F8.Uγ V H (g : G)))
      (tildeOf (fsuV1 T V) (conjClosure V H))) : ℚ) := by exact_mod_cast hA2.rk_pos
  have h1 := mul_le_mul_of_nonneg_right hr hpos'.le
  rw [hmul] at h1
  exact_mod_cast (by linarith : (rkIdx (fixV (autOn (tildeOf (fsuV1 T V) (F8.Uγ V H (g : G)))
      (tildeOf (fsuV1 T V) (conjClosure V H)))) : ℚ) ≤
    2 * (rk (autOn (tildeOf (fsuV1 T V) (F8.Uγ V H (g : G)))
      (tildeOf (fsuV1 T V) (conjClosure V H))) : ℚ))

theorem isPGroup_T_F4 : IsPGroup 2 T := C.S.hyp.fsu.sylow.1

theorem isPGroup_autOn_T_F4 :
    IsPGroup 2 (autOn (tildeOf (fsuV1 T V) T) (tildeOf (fsuV1 T V) (conjClosure V H))) := by
  rintro ⟨a, ha⟩
  obtain ⟨t, htT, rfl⟩ := (FixR.mem_autOn_tilde_iff C.h91_F4 (Setting147.TH' C.S)).mp ha
  obtain ⟨k, hk⟩ := C.isPGroup_T_F4 ⟨t, htT⟩
  refine ⟨k, Subtype.ext ?_⟩
  have h1 : t ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
  simp [← map_pow, h1]

theorem eq_one_of_comm_E_F4 (s : F8Setup T V L H γ γ' g)
    {b : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))}
    (hb : b ∈ autOn (tildeOf (fsuV1 T V) (F8.Uγ V H (g : G)))
      (tildeOf (fsuV1 T V) (conjClosure V H)))
    (hbE : ∀ e ∈ autOn (tildeOf (fsuV1 T V) Y) (tildeOf (fsuV1 T V) (conjClosure V H)),
      b * e = e * b) : b = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h91 := C.h91_F4
  have hTH : T ≤ H := Setting147.TH' C.S
  have hLH : l1 T L V ≤ H := Setting147.l1H' C.S
  set ρ := FixR.rho h91 with hρ
  set X := autOn (tildeOf (fsuV1 T V) H) (tildeOf (fsuV1 T V) (conjClosure V H)) with hX
  set E := autOn (tildeOf (fsuV1 T V) Y) (tildeOf (fsuV1 T V) (conjClosure V H)) with hE
  set P := autOn (tildeOf (fsuV1 T V) T) (tildeOf (fsuV1 T V) (conjClosure V H)) with hP
  set Λ := autOn (tildeOf (fsuV1 T V) (l1 T L V)) (tildeOf (fsuV1 T V) (conjClosure V H)) with hΛ
  set D := P ⊓ (Subgroup.centralizer (E : Set _) ⊓ Subgroup.centralizer (Λ : Set _)) with hD

  have hD2 : IsPGroup 2 D := C.isPGroup_autOn_T_F4.to_le inf_le_left
  have hDX : D ≤ X := inf_le_left.trans (autOn_le_autOn _ (secImg_mono hTH))
  have hNE : ∀ x : ↥H, ∀ e ∈ E, ρ x * e * (ρ x)⁻¹ ∈ E := fun x e he =>
    C.conj_mem_E_F4 (C.rho_mem_X_F4 x) he
  have hNΛ : ∀ t : ↥H, (t : G) ∈ T → ∀ l ∈ Λ, ρ t * l * (ρ t)⁻¹ ∈ Λ := by
    intro t ht l hl
    obtain ⟨y, hyL, rfl⟩ := (FixR.mem_autOn_tilde_iff h91 hLH).mp hl
    refine (FixR.mem_autOn_tilde_iff h91 hLH).mpr ⟨t * y * t⁻¹, ?_, by
      rw [map_mul, map_mul, map_inv]⟩
    exact (Subgroup.mem_normalizer_iff.mp (Setting147.T_le_N_l1_F4 C.S C.h1332 ht) _).mp hyL
  have hnorm : ∀ x : ↥H, ρ x ∈ Subgroup.normalizer (D : Set _) := by

    set K : Subgroup G := ((Subgroup.normalizer (D : Set _)).comap ρ).map H.subtype with hKdef
    have hcomm : ∀ x : ↥H, (∀ d ∈ D, ρ x * d = d * ρ x) → (x : G) ∈ K := by
      intro x hx
      refine Subgroup.mem_map.mpr ⟨x, ?_, rfl⟩
      rw [Subgroup.mem_comap]
      refine Subgroup.mem_normalizer_fintype fun d hd => ?_
      rw [hx d hd, mul_inv_cancel_right]
      exact hd
    have hYK : Y ≤ K := fun y hy => hcomm ⟨y, C.hYH hy⟩ fun d hd =>
      ((Subgroup.mem_centralizer_iff.mp hd.2.1) _ (C.rho_mem_E_F4 ⟨y, C.hYH hy⟩ hy))
    have hLK : l1 T L V ≤ K := fun l hl => hcomm ⟨l, hLH hl⟩ fun d hd =>
      ((Subgroup.mem_centralizer_iff.mp hd.2.2) _
        ((FixR.mem_autOn_tilde_iff h91 hLH).mpr ⟨⟨l, hLH hl⟩, hl, rfl⟩))
    have hTK : T ≤ K := by
      intro t ht
      refine Subgroup.mem_map.mpr ⟨⟨t, hTH ht⟩, ?_, rfl⟩
      rw [Subgroup.mem_comap]
      have htP : ρ ⟨t, hTH ht⟩ ∈ P := (FixR.mem_autOn_tilde_iff h91 hTH).mpr ⟨_, ht, rfl⟩
      refine Subgroup.mem_normalizer_fintype fun d hd => ⟨P.mul_mem (P.mul_mem htP hd.1)
        (P.inv_mem htP), ?_, ?_⟩
      · refine Subgroup.mem_centralizer_iff.mpr fun e he => ?_
        have h1 := (Subgroup.mem_centralizer_iff.mp hd.2.1) _
          (by simpa using hNE (⟨t, hTH ht⟩)⁻¹ e he)
        calc e * (ρ ⟨t, hTH ht⟩ * d * (ρ ⟨t, hTH ht⟩)⁻¹)
            = ρ ⟨t, hTH ht⟩ * (((ρ ⟨t, hTH ht⟩)⁻¹ * e * ρ ⟨t, hTH ht⟩) * d) *
                (ρ ⟨t, hTH ht⟩)⁻¹ := by group
          _ = ρ ⟨t, hTH ht⟩ * (d * ((ρ ⟨t, hTH ht⟩)⁻¹ * e * ρ ⟨t, hTH ht⟩)) *
                (ρ ⟨t, hTH ht⟩)⁻¹ := by rw [h1]
          _ = ρ ⟨t, hTH ht⟩ * d * (ρ ⟨t, hTH ht⟩)⁻¹ * e := by group
      · refine Subgroup.mem_centralizer_iff.mpr fun l hl => ?_
        have h2 := hNΛ (⟨t, hTH ht⟩)⁻¹ (by simpa using T.inv_mem ht) l hl
        have h1 := (Subgroup.mem_centralizer_iff.mp hd.2.2) _ (by simpa using h2)
        calc l * (ρ ⟨t, hTH ht⟩ * d * (ρ ⟨t, hTH ht⟩)⁻¹)
            = ρ ⟨t, hTH ht⟩ * (((ρ ⟨t, hTH ht⟩)⁻¹ * l * ρ ⟨t, hTH ht⟩) * d) *
                (ρ ⟨t, hTH ht⟩)⁻¹ := by group
          _ = ρ ⟨t, hTH ht⟩ * (d * ((ρ ⟨t, hTH ht⟩)⁻¹ * l * ρ ⟨t, hTH ht⟩)) *
                (ρ ⟨t, hTH ht⟩)⁻¹ := by rw [h1]
          _ = ρ ⟨t, hTH ht⟩ * d * (ρ ⟨t, hTH ht⟩)⁻¹ * l := by group
    have hHK : H ≤ K := by
      rw [C.hHYL]
      exact sup_le hYK (sup_le hLK hTK)
    intro x
    obtain ⟨x', hx', hxx'⟩ := Subgroup.mem_map.mp (hHK x.2)
    have : x' = x := Subtype.ext hxx'
    rw [← this]
    exact hx'
  have hXD : X ≤ Subgroup.normalizer (D : Set _) := fun a ha => by
    obtain ⟨x, -, rfl⟩ := (FixR.mem_autOn_tilde_iff h91 le_rfl).mp ha
    exact hnorm x
  have hDO : D ≤ pCoreOf 2 X := le_pCoreOf_of_le_normalizer 2 hDX hXD hD2
  rw [hX, M76.pCoreOf_autOn_eq_bot' h91] at hDO

  obtain ⟨u, huγ, rfl⟩ := (FixR.mem_autOn_tilde_iff h91 (C.h98.Uγ_le_H s)).mp hb
  obtain ⟨c, hcH, hc⟩ := S1549C.exists_alpha C.h98 s
  have hl1eq : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  rw [hl1eq] at hc
  have hcu : (c : G) * u * c⁻¹ ∈ T :=
    Setting147.R1_le_T C.S (hc (Quasithin.mul_mem_conjSub huγ))
  set c' : ↥H := ⟨c, hcH⟩ with hc'
  have hb' : ρ c' * ρ u * (ρ c')⁻¹ ∈ D := by
    refine ⟨(FixR.mem_autOn_tilde_iff h91 hTH).mpr ⟨c' * u * c'⁻¹, hcu, by
      rw [map_mul, map_mul, map_inv]⟩, ?_, ?_⟩
    · refine Subgroup.mem_centralizer_iff.mpr fun e he => ?_
      have h1 := hbE _ (by simpa using hNE c'⁻¹ e he)
      calc e * (ρ c' * ρ u * (ρ c')⁻¹)
          = ρ c' * (((ρ c')⁻¹ * e * ρ c') * ρ u) * (ρ c')⁻¹ := by group
        _ = ρ c' * (ρ u * ((ρ c')⁻¹ * e * ρ c')) * (ρ c')⁻¹ := by rw [h1]
        _ = ρ c' * ρ u * (ρ c')⁻¹ * e := by group
    · refine Subgroup.mem_centralizer_iff.mpr fun l hl => ?_
      obtain ⟨y, hyL, rfl⟩ := (FixR.mem_autOn_tilde_iff h91 hLH).mp hl
      have hyL' : (c : G)⁻¹ * y * c ∈ l1 T L V := by
        have := (Subgroup.mem_normalizer_iff.mp (C.hHL (H.inv_mem hcH)) y).mp hyL
        simpa using this
      have hcomm := Setting147.comm_Uγ_l1_F4 C.S C.h98 C.h1332 C.hHL s
      have hq : (u : G) * ((c : G)⁻¹ * y * c) * (u : G)⁻¹ * ((c : G)⁻¹ * y * c)⁻¹ ∈
          pCoreOf 2 H := hcomm (Subgroup.commutator_mem_commutator huγ hyL')
      have h1 := FixR.rho_comm_of_mem h91 (x := u) (y := c'⁻¹ * y * c') (by simpa using hq)
      have e1 : ρ (c'⁻¹ * y * c') = (ρ c')⁻¹ * ρ y * ρ c' := by simp [map_mul, map_inv]
      rw [e1] at h1
      calc ρ y * (ρ c' * ρ u * (ρ c')⁻¹)
          = ρ c' * ((ρ c')⁻¹ * ρ y * ρ c' * ρ u) * (ρ c')⁻¹ := by group
        _ = ρ c' * (ρ u * ((ρ c')⁻¹ * ρ y * ρ c')) * (ρ c')⁻¹ := by rw [h1]
        _ = ρ c' * ρ u * (ρ c')⁻¹ * ρ y := by group
  have h1 := hDO hb'
  rw [Subgroup.mem_bot] at h1
  have h2 : ρ u = (ρ c')⁻¹ * (ρ c' * ρ u * (ρ c')⁻¹) * ρ c' := by group
  rw [h2, h1]
  group

theorem false_of_rank_two_F4 [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V H)))]
    (s : F8Setup T V L H γ γ' g)
    (hpos : 0 < mIdx (F8.Uγ V H (g : G)) (F8.Dγ V (fsuV1 T V) H (g : G)))
    (hle : mIdx (conjClosure V H) (F8.DH V (fsuV1 T V) H (g : G)) ≤
      mIdx (F8.Uγ V H (g : G)) (F8.Dγ V (fsuV1 T V) H (g : G)))
    {d₁ d₂ : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))} (hL : Lines d₁ d₂)
    {b₁ b₂ : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))}
    (hb₁ : b₁ ∈ autOn (tildeOf (fsuV1 T V) (F8.Uγ V H (g : G)))
      (tildeOf (fsuV1 T V) (conjClosure V H)))
    (hb₂ : b₂ ∈ autOn (tildeOf (fsuV1 T V) (F8.Uγ V H (g : G)))
      (tildeOf (fsuV1 T V) (conjClosure V H)))
    (hb₁1 : b₁ ≠ 1) (hb₂1 : b₂ ≠ 1) (hc₁ : cw b₁ ≤ cw d₁) (hc₂ : cw b₂ ≤ cw d₂)
    (hrkB : rk (autOn (tildeOf (fsuV1 T V) (F8.Uγ V H (g : G)))
      (tildeOf (fsuV1 T V) (conjClosure V H))) = 2)
    (hfix : rkIdx (fixV (autOn (tildeOf (fsuV1 T V) (F8.Uγ V H (g : G)))
      (tildeOf (fsuV1 T V) (conjClosure V H)))) = 4) : False := by
  have h91 := C.h91_F4
  have hUγH := C.h98.Uγ_le_H s

  have heq : 2 * mIdx (F8.Uγ V H (g : G)) (F8.Dγ V (fsuV1 T V) H (g : G)) =
      mIdx (conjClosure V H)
        (centralizerMod (fsuV1 T V) (conjClosure V H) (F8.Uγ V H (g : G))) := by
    rw [← C.h98.rk_autOn_tilde_Uγ s, hrkB, ← C.rkIdx_fixV_autOn_F4 hUγH, hfix]
  obtain ⟨-, hcent, hA₁, hcardA₁, hA₁V₁, -⟩ := (C.h98.F916_2 s hpos hle).2 heq
  have hDγ := C.h98.Dγ_eq_inf_pCoreOf s

  have key : ∀ b ∈ autOn (tildeOf (fsuV1 T V) (F8.Uγ V H (g : G)))
      (tildeOf (fsuV1 T V) (conjClosure V H)), b ≠ 1 →
      ∃ u : ↥H, (u : G) ∈ F8.Uγ V H (g : G) ∧ FixR.rho h91 u = b ∧
        ∃ x ∈ F8.DH V (fsuV1 T V) H (g : G), (u : G) * x * (u : G)⁻¹ * x⁻¹ ∈ F8.A₁ (fsuV1 T V) g ∧
          (u : G) * x * (u : G)⁻¹ * x⁻¹ ∉ fsuV1 T V := by
    intro b hb hb1
    obtain ⟨u, huγ, rfl⟩ := (FixR.mem_autOn_tilde_iff h91 hUγH).mp hb
    refine ⟨u, huγ, rfl, ?_⟩
    have hu : (u : G) ∉ centralizerMod (fsuV1 T V) (F8.Uγ V H (g : G))
        (F8.DH V (fsuV1 T V) H (g : G)) := by
      rw [hcent, hDγ]
      intro hu
      exact hb1 ((FixR.rho_eq_one_iff h91 u).mpr hu.2)
    by_contra hcon
    push Not at hcon
    apply hu
    refine ⟨huγ, h91.H_normalizes_V₁ u.2, fun x hx => ?_⟩
    by_contra hxV
    exact hxV (hcon x hx (hA₁ (Subgroup.commutator_mem_commutator huγ hx)))
  obtain ⟨u₁, -, hu₁, x₁, hx₁, ha₁A, ha₁V⟩ := key b₁ hb₁ hb₁1
  obtain ⟨u₂, -, hu₂, x₂, hx₂, ha₂A, ha₂V⟩ := key b₂ hb₂ hb₂1

  have hae : (u₁ : G) * x₁ * (u₁ : G)⁻¹ * x₁⁻¹ = (u₂ : G) * x₂ * (u₂ : G)⁻¹ * x₂⁻¹ := by
    obtain ⟨p, q, hpq, hpq'⟩ := Nat.card_eq_two_iff.mp hcardA₁
    have hall : ∀ z : ↥(F8.A₁ (fsuV1 T V) (g : G)), z = p ∨ z = q := fun z => by
      have : z ∈ ({p, q} : Set _) := hpq' ▸ Set.mem_univ z
      simpa using this
    have h1 : ∀ z : ↥(F8.A₁ (fsuV1 T V) (g : G)), (z : G) ≠ 1 → z ≠ 1 := fun z hz h =>
      hz (by rw [h]; rfl)
    have hne1 : ∀ z : ↥(F8.A₁ (fsuV1 T V) (g : G)), (z : G) ∉ fsuV1 T V → z ≠ 1 := fun z hz =>
      h1 z fun h => hz (by rw [h]; exact Subgroup.one_mem _)
    set z₁ : ↥(F8.A₁ (fsuV1 T V) (g : G)) := ⟨_, ha₁A⟩
    set z₂ : ↥(F8.A₁ (fsuV1 T V) (g : G)) := ⟨_, ha₂A⟩
    have hz₁ := hne1 z₁ ha₁V
    have hz₂ := hne1 z₂ ha₂V
    have h1o := hall 1
    have hz : z₁ = z₂ := by
      rcases hall z₁ with e1 | e1 <;> rcases hall z₂ with e2 | e2 <;> rcases h1o with e0 | e0 <;>
        first
          | exact e1.trans e2.symm
          | exact absurd (e1.trans e0.symm) hz₁
          | exact absurd (e2.trans e0.symm) hz₂
    exact congrArg Subtype.val hz

  have hx₁U : x₁ ∈ conjClosure V H := centralizerMod_le_left _ _ _ hx₁
  have hx₂U : x₂ ∈ conjClosure V H := centralizerMod_le_left _ _ _ hx₂
  set w₁ := commHom (FixR.rho h91 u₁)
    ⟨secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V)
      ⟨x₁, h91.H_normalizes_V₁ (C.UH_le_H_F4 hx₁U)⟩, secMk_mem_secImg hx₁U⟩ with hw₁
  set w₂ := commHom (FixR.rho h91 u₂)
    ⟨secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V)
      ⟨x₂, h91.H_normalizes_V₁ (C.UH_le_H_F4 hx₂U)⟩, secMk_mem_secImg hx₂U⟩ with hw₂
  have hw₁c : w₁ ∈ cw b₁ := ⟨_, Subgroup.mem_top _, by rw [hw₁, hu₁]⟩
  have hw₂c : w₂ ∈ cw b₂ := ⟨_, Subgroup.mem_top _, by rw [hw₂, hu₂]⟩
  have hw : w₁ = w₂ := by
    apply Subtype.ext
    rw [hw₁, hw₂, C.commHom_rho_F4 u₁ hx₁U, C.commHom_rho_F4 u₂ hx₂U]
    congr 1
    exact Subtype.ext hae
  have hw0 : w₁ ∈ cw d₁ ⊓ cw d₂ := ⟨hc₁ hw₁c, hc₂ (hw ▸ hw₂c)⟩
  rw [hL.inf_eq_bot, Subgroup.mem_bot] at hw0
  have h3 := congrArg Subtype.val hw0
  rw [hw₁, C.commHom_rho_F4 u₁ hx₁U] at h3
  exact ha₁V (secMk_eq_one_iff.mp h3)

theorem rank_one_F4 [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V H)))]
    (s : F8Setup T V L H γ γ' g)
    (hpos : 0 < mIdx (F8.Uγ V H (g : G)) (F8.Dγ V (fsuV1 T V) H (g : G)))
    (hle : mIdx (conjClosure V H) (F8.DH V (fsuV1 T V) H (g : G)) ≤
      mIdx (F8.Uγ V H (g : G)) (F8.Dγ V (fsuV1 T V) H (g : G)))
    {d₁ d₂ : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))} (hL : Lines d₁ d₂)
    (hEp : ∀ e ∈ autOn (tildeOf (fsuV1 T V) Y) (tildeOf (fsuV1 T V) (conjClosure V H)),
      Lines.InE d₁ d₂ e)
    (hd₁ : d₁ ∈ autOn (tildeOf (fsuV1 T V) Y) (tildeOf (fsuV1 T V) (conjClosure V H)))
    (hd₂ : d₂ ∈ autOn (tildeOf (fsuV1 T V) Y) (tildeOf (fsuV1 T V) (conjClosure V H))) :
    mIdx (F8.Uγ V H (g : G)) (F8.Dγ V (fsuV1 T V) H (g : G)) = 1 ∧
      mIdx (conjClosure V H) (F8.DH V (fsuV1 T V) H (g : G)) = 1 ∧
      ⁅F8.DH V (fsuV1 T V) H (g : G), F8.Uγ V H (g : G)⁆ ≠ ⊥ ∧
      ∃ b ∈ autOn (tildeOf (fsuV1 T V) (F8.Uγ V H (g : G)))
          (tildeOf (fsuV1 T V) (conjClosure V H)),
        autOn (tildeOf (fsuV1 T V) (F8.Uγ V H (g : G))) (tildeOf (fsuV1 T V) (conjClosure V H)) =
          Subgroup.zpowers b ∧
        ((b * d₁ * b⁻¹ = d₁⁻¹ ∧ b * d₂ * b⁻¹ = d₂ ∧ cw b ≤ cw d₁ ∧ rk (cw b) = 2) ∨
          (b * d₂ * b⁻¹ = d₂⁻¹ ∧ b * d₁ * b⁻¹ = d₁ ∧ cw b ≤ cw d₂ ∧ rk (cw b) = 2)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h91 := C.h91_F4
  have hUγH := C.h98.Uγ_le_H s
  obtain ⟨hBX, hne, hB, hquad, hr⟩ := C.unpack_F4 s hpos hle
  have hE : ∀ b ∈ autOn (tildeOf (fsuV1 T V) (F8.Uγ V H (g : G)))
      (tildeOf (fsuV1 T V) (conjClosure V H)),
      Lines.InE d₁ d₂ (b * d₁ * b⁻¹) ∧ Lines.InE d₁ d₂ (b * d₂ * b⁻¹) := fun b hb =>
    ⟨hEp _ (C.conj_mem_E_F4 (hBX hb) hd₁), hEp _ (C.conj_mem_E_F4 (hBX hb) hd₂)⟩
  have hfaith : ∀ b ∈ autOn (tildeOf (fsuV1 T V) (F8.Uγ V H (g : G)))
      (tildeOf (fsuV1 T V) (conjClosure V H)), b * d₁ * b⁻¹ = d₁ → b * d₂ * b⁻¹ = d₂ → b = 1 := by
    intro b hb h1 h2
    refine C.eq_one_of_comm_E_F4 s hb fun e he => ?_
    have hc₁ : b * d₁ = d₁ * b := by
      calc b * d₁ = (b * d₁ * b⁻¹) * b := by group
        _ = d₁ * b := by rw [h1]
    have hc₂ : b * d₂ = d₂ * b := by
      calc b * d₂ = (b * d₂ * b⁻¹) * b := by group
        _ = d₂ * b := by rw [h2]
    obtain ⟨a, -, c, -, rfl⟩ := hEp e he
    rw [← mul_assoc, (Commute.pow_right hc₁ a).eq, mul_assoc, (Commute.pow_right hc₂ c).eq,
      ← mul_assoc]
  have hpos' : 0 < mIdx (conjClosure V H) (F8.DH V (fsuV1 T V) H (g : G)) :=
    mIdx_pos_of_lt_of_isPGroup (isPGroup_of_isElemAbelian C.h98.F911_3)
      (C.h98.lemma_14_5_17 s)
  rcases hL.offender hB hne hquad hr hE hfaith with ⟨b, hb, hBz, hcase⟩ |
      ⟨b₁, hb₁, b₂, hb₂, hb₁1, hb₂1, hc₁, hc₂, hrkB, hfix⟩
  · have hb1 : b ≠ 1 := by
      rintro rfl
      rw [hBz, Subgroup.zpowers_one_eq_bot] at hne
      exact hne rfl
    have hb2 : b ^ 2 = 1 := hB.2 b hb
    have hrkB : rk (autOn (tildeOf (fsuV1 T V) (F8.Uγ V H (g : G)))
        (tildeOf (fsuV1 T V) (conjClosure V H))) = 1 := by
      rw [hBz, rk, Nat.card_zpowers, orderOf_eq_prime hb2 hb1]
      norm_num
    have hmγ : mIdx (F8.Uγ V H (g : G)) (F8.Dγ V (fsuV1 T V) H (g : G)) = 1 := by
      rw [← C.h98.rk_autOn_tilde_Uγ s, hrkB]
    have hmH : mIdx (conjClosure V H) (F8.DH V (fsuV1 T V) H (g : G)) = 1 := by omega
    have hrkb : rk (cw b) = 2 := by rcases hcase with h | h <;> exact h.2.2.2
    refine ⟨hmγ, hmH, ?_, b, hb, hBz, hcase⟩

    intro hbot
    have hDC : F8.DH V (fsuV1 T V) H (g : G) ≤
        centralizerMod (fsuV1 T V) (conjClosure V H) (F8.Uγ V H (g : G)) := by
      intro x hx
      have hxU : x ∈ conjClosure V H := centralizerMod_le_left _ _ _ hx
      refine ⟨hxU, h91.H_normalizes_V₁ (C.UH_le_H_F4 hxU), fun u hu => ?_⟩
      have h1 := Subgroup.commutator_mem_commutator hx hu
      rw [hbot, Subgroup.mem_bot, commutatorElement_def] at h1
      rw [h1]
      exact Subgroup.one_mem _
    have h1 := S1549C.mIdx_anti_right (X := conjClosure V H) hDC
    rw [← C.rkIdx_fixV_autOn_F4 hUγH, hBz, rkIdx_fixV_zpowers, commV_zpowers_eq_map] at h1
    have : rk (cw b) ≤ 1 := by
      show rk ((⊤ : Subgroup _).map (commHom b)) ≤ 1
      omega
    omega
  · exact (C.false_of_rank_two_F4 s hpos hle hL hb₁ hb₂ hb₁1 hb₂1 hc₁ hc₂ hrkB hfix).elim

end Ctx_F4

end CFSG.Quasithin.H13.L32A.S2

end
