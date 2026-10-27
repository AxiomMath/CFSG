module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.L32A76S2d
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A705b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A76S2b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A76S2c

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

theorem UN_le_F4 : conjClosure V H ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
  C.UH_le_H_F4.trans C.h91_F4.H_normalizes_V₁

omit C in

@[expose] noncomputable def piU_F4 (C : Ctx_F4 G T L V H Y) :
    ↥(conjClosure V H) →* ↥(tildeOf (fsuV1 T V) (conjClosure V H)) :=
  ((secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V)).comp
    (Subgroup.inclusion C.UN_le_F4)).codRestrict _ fun x => secMk_mem_secImg x.2

theorem piU_coe_F4 (x : ↥(conjClosure V H)) :
    ((C.piU_F4 x : ↥(tildeOf (fsuV1 T V) (conjClosure V H))) :
      SecQuot (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V)) =
      secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) ⟨x, C.UN_le_F4 x.2⟩ := rfl

theorem piU_surjective_F4 : Function.Surjective C.piU_F4 := by
  rintro ⟨w, hw⟩
  obtain ⟨x, hx, rfl⟩ := mem_secImg.mp hw
  exact ⟨⟨x, hx⟩, rfl⟩

theorem piU_eq_iff_F4 {x y : ↥(conjClosure V H)} :
    C.piU_F4 x = C.piU_F4 y ↔ (x : G)⁻¹ * y ∈ fsuV1 T V := by
  rw [← Subtype.coe_inj, piU_coe_F4, piU_coe_F4, secMk_eq_secMk_iff]

theorem piU_eq_one_iff_F4 {x : ↥(conjClosure V H)} : C.piU_F4 x = 1 ↔ (x : G) ∈ fsuV1 T V := by
  rw [← map_one C.piU_F4, piU_eq_iff_F4]
  simp

theorem piU_comm_F4 [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V H)))] (u : ↥H)
    (x : ↥(conjClosure V H)) :
    C.piU_F4 ⟨(u : G) * x * (u : G)⁻¹ * (x : G)⁻¹, comm_mem_UH u.2 x.2⟩ =
      commHom (FixR.rho C.h91_F4 u) (C.piU_F4 x) := by
  apply Subtype.ext
  rw [piU_coe_F4]
  exact (C.commHom_rho_F4 u x.2).symm

theorem piU_conj_F4 (u : ↥H) (x : ↥(conjClosure V H)) :
    C.piU_F4 ⟨(u : G) * x * (u : G)⁻¹, conj_mem_UH u.2 x.2⟩ = FixR.rho C.h91_F4 u (C.piU_F4 x) := by
  apply Subtype.ext
  rw [piU_coe_F4, FixR.rho_coe, FixR.sig_apply, piU_coe_F4, ← map_inv, ← map_mul, ← map_mul]
  rfl

theorem comm_le_preimage_F4 [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V H)))]
    (s : F8Setup T V L H γ γ' g) {b : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))}
    (hBz : autOn (tildeOf (fsuV1 T V) (F8.Uγ V H (g : G)))
      (tildeOf (fsuV1 T V) (conjClosure V H)) = Subgroup.zpowers b) (hb2 : b ^ 2 = 1) :
    ⁅conjClosure V H, F8.Uγ V H (g : G)⁆ ≤ ((cw b).comap C.piU_F4).map (conjClosure V H).subtype := by
  have hUγH := C.h98.Uγ_le_H s
  rw [Subgroup.commutator_le]
  intro x hx u hu
  have hu' : u ∈ H := hUγH hu
  have hxu : x * u * x⁻¹ * u⁻¹ ∈ conjClosure V H := by
    have e : x * u * x⁻¹ * u⁻¹ = (u * x * u⁻¹ * x⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ (comm_mem_UH hu' hx)
  refine ⟨⟨_, hxu⟩, Subgroup.mem_comap.mpr ?_, rfl⟩
  have hρu : FixR.rho C.h91_F4 ⟨u, hu'⟩ ∈ Subgroup.zpowers b := by
    rw [← hBz]
    exact (FixR.mem_autOn_tilde_iff C.h91_F4 hUγH).mpr ⟨⟨u, hu'⟩, hu, rfl⟩
  have e : (⟨x * u * x⁻¹ * u⁻¹, hxu⟩ : ↥(conjClosure V H)) =
      (⟨u * x * u⁻¹ * x⁻¹, comm_mem_UH hu' hx⟩ : ↥(conjClosure V H))⁻¹ :=
    Subtype.ext (by rw [Subgroup.coe_inv]; group)
  have h := C.piU_comm_F4 ⟨u, hu'⟩ ⟨x, hx⟩
  rw [e, map_inv, show C.piU_F4 ⟨u * x * u⁻¹ * x⁻¹, comm_mem_UH hu' hx⟩ =
    commHom (FixR.rho C.h91_F4 ⟨u, hu'⟩) (C.piU_F4 ⟨x, hx⟩) from h]
  refine Subgroup.inv_mem _ ?_
  rcases eq_one_or_eq_of_mem_zpowers hb2 hρu with h | h
  · rw [h, commHom_apply, MulAut.one_apply, mul_inv_cancel]
    exact Subgroup.one_mem _
  · rw [h]
    exact ⟨_, Subgroup.mem_top _, rfl⟩

theorem preimage_le_comm_F4 [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V H)))]
    (s : F8Setup T V L H γ γ' g) {b : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))}
    (hb : b ∈ autOn (tildeOf (fsuV1 T V) (F8.Uγ V H (g : G)))
      (tildeOf (fsuV1 T V) (conjClosure V H)))
    (hV₁A : fsuV1 T V ≤ ⁅conjClosure V H, F8.Uγ V H (g : G)⁆) :
    ((cw b).comap C.piU_F4).map (conjClosure V H).subtype ≤ ⁅conjClosure V H, F8.Uγ V H (g : G)⁆ := by
  have hUγH := C.h98.Uγ_le_H s
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨w, -, hw⟩ := hx
  obtain ⟨z, rfl⟩ := C.piU_surjective_F4 w
  obtain ⟨u, huγ, rfl⟩ := (FixR.mem_autOn_tilde_iff C.h91_F4 hUγH).mp hb
  rw [← C.piU_comm_F4, piU_eq_iff_F4] at hw
  have h3 : (u : G) * z * (u : G)⁻¹ * (z : G)⁻¹ ∈ ⁅conjClosure V H, F8.Uγ V H (g : G)⁆ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator huγ z.2
  have e : (x : G) = (u : G) * z * (u : G)⁻¹ * (z : G)⁻¹ *
      (((u : G) * z * (u : G)⁻¹ * (z : G)⁻¹)⁻¹ * x) := by group
  show (x : G) ∈ _
  rw [e]
  refine Subgroup.mul_mem _ h3 (hV₁A ?_)
  simpa using hw

theorem A₁_le_comm_F4
    (hne : ⁅F8.DH V (fsuV1 T V) H (g : G), F8.Uγ V H (g : G)⁆ ≠ ⊥) :
    F8.A₁ (fsuV1 T V) (g : G) ≤ ⁅conjClosure V H, F8.Uγ V H (g : G)⁆ := by
  have hle : ⁅F8.DH V (fsuV1 T V) H (g : G), F8.Uγ V H (g : G)⁆ ≤ F8.A₁ (fsuV1 T V) (g : G) := by
    rw [Subgroup.commutator_comm]
    exact commutator_centralizerMod_le _ _ _
  rw [← eq_of_le_of_ne_bot_of_card_two hle hne C.h98.card_A₁]
  exact Subgroup.commutator_mono (centralizerMod_le_left _ _ _) le_rfl

theorem V₁_le_comm_F4 [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V H)))]
    (s : F8Setup T V L H γ γ' g)
    (hpos : 0 < mIdx (F8.Uγ V H (g : G)) (F8.Dγ V (fsuV1 T V) H (g : G)))
    (hle : mIdx (conjClosure V H) (F8.DH V (fsuV1 T V) H (g : G)) ≤
      mIdx (F8.Uγ V H (g : G)) (F8.Dγ V (fsuV1 T V) H (g : G)))
    {d₁ d₂ : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))} (hL : Lines d₁ d₂)
    (hEp : ∀ e ∈ autOn (tildeOf (fsuV1 T V) Y) (tildeOf (fsuV1 T V) (conjClosure V H)),
      Lines.InE d₁ d₂ e)
    (hd₁ : d₁ ∈ autOn (tildeOf (fsuV1 T V) Y) (tildeOf (fsuV1 T V) (conjClosure V H)))
    (hd₂ : d₂ ∈ autOn (tildeOf (fsuV1 T V) Y) (tildeOf (fsuV1 T V) (conjClosure V H))) :
    fsuV1 T V ≤ ⁅conjClosure V H, F8.Uγ V H (g : G)⁆ := by
  obtain ⟨hmγ, hmH, -, -⟩ := C.rank_one_F4 s hpos hle hL hEp hd₁ hd₂
  have hlt : F8.Dγ V (fsuV1 T V) H (g : G) < F8.Uγ V H (g : G) := by
    refine lt_of_le_of_ne (centralizerMod_le_left _ _ _) fun he => ?_
    rw [he] at hpos
    simp [mIdx] at hpos
  obtain ⟨δ, δ', k, y, sk, -, -, hUδ, hUH, hDHk, hDδk⟩ :=
    C.h98.exists_symmetric_setup s (C.h98.not_Vγ_le_ballStab_of_lt s hlt)
  have hposk : 0 < mIdx (F8.Uγ V H (k : G)) (F8.Dγ V (fsuV1 T V) H (k : G)) := by
    rw [hUδ, hDδk, F9.mIdx_conjSub, hmH]
    norm_num
  have hlek : mIdx (conjClosure V H) (F8.DH V (fsuV1 T V) H (k : G)) ≤
      mIdx (F8.Uγ V H (k : G)) (F8.Dγ V (fsuV1 T V) H (k : G)) := by
    rw [hUδ, hDδk, F9.mIdx_conjSub, hmH, hDHk, ← hUH, F9.mIdx_conjSub, hmγ]
  obtain ⟨-, -, hnek, -⟩ := C.rank_one_F4 sk hposk hlek hL hEp hd₁ hd₂
  have e : ⁅F8.DH V (fsuV1 T V) H (k : G), F8.Uγ V H (k : G)⁆ =
      conjSub (y : G) ⁅F8.Dγ V (fsuV1 T V) H (g : G), conjClosure V H⁆ := by
    rw [hDHk, hUδ]
    exact (Subgroup.map_commutator _ _ _).symm
  have hne : ⁅F8.Dγ V (fsuV1 T V) H (g : G), conjClosure V H⁆ ≠ ⊥ := by
    intro hbot
    apply hnek
    rw [e, hbot]
    exact Subgroup.map_bot _
  have hleV : ⁅F8.Dγ V (fsuV1 T V) H (g : G), conjClosure V H⁆ ≤ fsuV1 T V := by
    rw [Subgroup.commutator_comm]
    exact commutator_centralizerMod_le _ _ _
  rw [← eq_of_le_of_ne_bot_of_card_two hleV hne C.h98.card_V₁, Subgroup.commutator_comm]
  exact Subgroup.commutator_mono le_rfl (centralizerMod_le_left _ _ _)

theorem comm_eq_preimage_F4 [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V H)))]
    (s : F8Setup T V L H γ γ' g) {b : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))}
    (hb : b ∈ autOn (tildeOf (fsuV1 T V) (F8.Uγ V H (g : G)))
      (tildeOf (fsuV1 T V) (conjClosure V H)))
    (hBz : autOn (tildeOf (fsuV1 T V) (F8.Uγ V H (g : G)))
      (tildeOf (fsuV1 T V) (conjClosure V H)) = Subgroup.zpowers b) (hb2 : b ^ 2 = 1)
    (hV₁A : fsuV1 T V ≤ ⁅conjClosure V H, F8.Uγ V H (g : G)⁆) :
    ⁅conjClosure V H, F8.Uγ V H (g : G)⁆ = ((cw b).comap C.piU_F4).map (conjClosure V H).subtype :=
  le_antisymm (C.comm_le_preimage_F4 s hBz hb2) (C.preimage_le_comm_F4 s hb hV₁A)

theorem card_comm_F4 [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V H)))]
    {A : Subgroup G} {b : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))}
    (hA : A = ((cw b).comap C.piU_F4).map (conjClosure V H).subtype) (hV₁A : fsuV1 T V ≤ A)
    (hrk : rk (cw b) = 2) : Nat.card A = 8 := by
  have hAN : A ≤ Subgroup.normalizer (fsuV1 T V : Set G) := by
    rw [hA]
    exact (Subgroup.map_subtype_le _).trans C.UN_le_F4

  have h1' := relIndex_secImg (A := Subgroup.normalizer (fsuV1 T V : Set G)) (B := fsuV1 T V)
    le_rfl hV₁A hAN
  have hbot : secImg (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) (fsuV1 T V) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_secImg.mp hy
    exact (secMk_eq_one_iff.mpr hx).symm ▸ Subgroup.one_mem _
  rw [hbot, Subgroup.relIndex_bot_left] at h1'
  have h1 : Nat.card (tildeOf (fsuV1 T V) A) = (fsuV1 T V).relIndex A := h1'

  have himg :
      tildeOf (fsuV1 T V) A = (cw b).map (tildeOf (fsuV1 T V) (conjClosure V H)).subtype := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := mem_secImg.mp hy
      rw [hA] at hx
      obtain ⟨z, hz, hzx⟩ := hx
      refine ⟨C.piU_F4 z, hz, ?_⟩
      rw [Subgroup.subtype_apply, piU_coe_F4]
      congr 1
      exact Subtype.ext hzx
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨z, rfl⟩ := C.piU_surjective_F4 w
      have hzA : (z : G) ∈ A := by rw [hA]; exact ⟨z, hw, rfl⟩
      rw [Subgroup.subtype_apply, piU_coe_F4]
      exact secMk_mem_secImg hzA
  have h2 : Nat.card (tildeOf (fsuV1 T V) A) = 4 := by
    rw [himg, Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
      card_eq_two_pow C.sq_eq_one_F4, hrk]
    norm_num
  have h3 := Subgroup.relIndex_mul_card (fsuV1 T V) A
  rw [inf_eq_left.mpr hV₁A, ← h1, h2, C.h98.card_V₁] at h3
  omega

theorem l1_le_normalizer_F4 [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V H)))]
    (s : F8Setup T V L H γ γ' g) {b : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))}
    (hb : b ∈ autOn (tildeOf (fsuV1 T V) (F8.Uγ V H (g : G)))
      (tildeOf (fsuV1 T V) (conjClosure V H)))
    {A : Subgroup G} (hA : A = ((cw b).comap C.piU_F4).map (conjClosure V H).subtype) :
    l1 T L V ≤ Subgroup.normalizer (A : Set G) := by
  have hUγH := C.h98.Uγ_le_H s
  have hLH : l1 T L V ≤ H := Setting147.l1H' C.S
  obtain ⟨u, huγ, rfl⟩ := (FixR.mem_autOn_tilde_iff C.h91_F4 hUγH).mp hb
  have hcomm := Setting147.comm_Uγ_l1_F4 C.S C.h98 C.h1332 C.hHL s
  have key : ∀ l : ↥H, (l : G) ∈ l1 T L V → ∀ a ∈ A, (l : G) * a * (l : G)⁻¹ ∈ A := by
    intro l hl a ha
    rw [hA] at ha ⊢
    obtain ⟨x, hx, rfl⟩ := ha
    refine ⟨⟨(l : G) * x * (l : G)⁻¹, conj_mem_UH l.2 x.2⟩, Subgroup.mem_comap.mpr ?_, rfl⟩
    rw [C.piU_conj_F4]
    have hc : FixR.rho C.h91_F4 l * FixR.rho C.h91_F4 u = FixR.rho C.h91_F4 u * FixR.rho C.h91_F4 l := by
      refine (FixR.rho_comm_of_mem C.h91_F4 ?_).symm
      exact hcomm (Subgroup.commutator_mem_commutator huγ hl)
    exact mem_map_commHom_of_comm hc hx
  intro l hl
  refine Subgroup.mem_normalizer_fintype fun a ha => ?_
  exact key ⟨l, hLH hl⟩ hl a ha

end Ctx_F4

structure Good_F4 (C : Ctx_F4 G T L V H Y)
    [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V H)))] (γ γ' : F8.Geom T L H)
    (g : ↥((L ⊔ T) ⊔ H)) (e₁ e₂ b : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))) : Prop where
  s : F8Setup T V L H γ γ' g
  mγ : mIdx (F8.Uγ V H (g : G)) (F8.Dγ V (fsuV1 T V) H (g : G)) = 1
  mH : mIdx (conjClosure V H) (F8.DH V (fsuV1 T V) H (g : G)) = 1
  lines : Lines e₁ e₂
  e₁E : e₁ ∈ autOn (tildeOf (fsuV1 T V) Y) (tildeOf (fsuV1 T V) (conjClosure V H))
  e₂E : e₂ ∈ autOn (tildeOf (fsuV1 T V) Y) (tildeOf (fsuV1 T V) (conjClosure V H))
  inE : ∀ e ∈ autOn (tildeOf (fsuV1 T V) Y) (tildeOf (fsuV1 T V) (conjClosure V H)),
    Lines.InE e₁ e₂ e
  bB : b ∈ autOn (tildeOf (fsuV1 T V) (F8.Uγ V H (g : G))) (tildeOf (fsuV1 T V) (conjClosure V H))
  Bz : autOn (tildeOf (fsuV1 T V) (F8.Uγ V H (g : G))) (tildeOf (fsuV1 T V) (conjClosure V H)) =
    Subgroup.zpowers b
  inv : b * e₁ * b⁻¹ = e₁⁻¹
  fix : b * e₂ * b⁻¹ = e₂
  cw_le : cw b ≤ cw e₁
  rk_cw : rk (cw b) = 2
  A_eq : ⁅conjClosure V H, F8.Uγ V H (g : G)⁆ = ((cw b).comap C.piU_F4).map (conjClosure V H).subtype
  V₁_le : fsuV1 T V ≤ ⁅conjClosure V H, F8.Uγ V H (g : G)⁆
  A₁_le : F8.A₁ (fsuV1 T V) (g : G) ≤ ⁅conjClosure V H, F8.Uγ V H (g : G)⁆
  card : Nat.card ↥(⁅conjClosure V H, F8.Uγ V H (g : G)⁆ : Subgroup G) = 8
  l1_le : l1 T L V ≤
    Subgroup.normalizer ((⁅conjClosure V H, F8.Uγ V H (g : G)⁆ : Subgroup G) : Set G)

namespace Ctx_F4
open CFSG.Quasithin.H13.L32A.S2.Ctx_F4

variable (C : Ctx_F4 G T L V H Y)
include C

theorem exists_good_F4 [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V H)))] :
    ∃ (γ γ' : F8.Geom T L H) (g : ↥((L ⊔ T) ⊔ H))
      (e₁ e₂ b : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))), Good_F4 C γ γ' g e₁ e₂ b := by
  obtain ⟨d₁, d₂, hd₁, hd₂, hL, hEp⟩ := C.exists_lines_F4

  obtain ⟨γ₀, γ₀', g₀, s₀⟩ := C.h98.exists_F8Setup
  obtain ⟨γ, γ', g, s, hpos, hle, -⟩ := C.h98.lemma_14_5_18_four s₀
    (Setting147.Dγ_lt_Uγ_F4 C.S C.h98 C.h1222 C.h1332 C.h1334 C.hHL s₀)
  obtain ⟨hmγ, hmH, hne, b, hb, hBz, hcase⟩ := C.rank_one_F4 s hpos hle hL hEp hd₁ hd₂
  have hb2 : b ^ 2 = 1 := (C.unpack_F4 s hpos hle).2.2.1.2 b hb
  have hV₁ := C.V₁_le_comm_F4 s hpos hle hL hEp hd₁ hd₂
  have hA := C.comm_eq_preimage_F4 s hb hBz hb2 hV₁
  have hrk : rk (cw b) = 2 := by rcases hcase with h | h <;> exact h.2.2.2
  have hcard := C.card_comm_F4 hA hV₁ hrk
  have hl1 := C.l1_le_normalizer_F4 s hb hA
  have hA₁ := C.A₁_le_comm_F4 hne
  rcases hcase with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · exact ⟨γ, γ', g, d₁, d₂, b, ⟨s, hmγ, hmH, hL, hd₁, hd₂, hEp, hb, hBz, h1, h2, h3, h4, hA, hV₁,
      hA₁, hcard, hl1⟩⟩
  · exact ⟨γ, γ', g, d₂, d₁, b, ⟨s, hmγ, hmH, hL.symm, hd₂, hd₁,
      fun e he => hL.inE_swap (hEp e he), hb, hBz, h1, h2, h3, h4, hA, hV₁, hA₁, hcard, hl1⟩⟩

end Ctx_F4

end CFSG.Quasithin.H13.L32A.S2

end
