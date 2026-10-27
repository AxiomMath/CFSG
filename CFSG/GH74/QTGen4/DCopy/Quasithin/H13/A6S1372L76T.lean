module

public import CFSG.Quasithin.H13.A6S1372L76T
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372L76Q

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge Matrix
open scoped IsMulCommutative

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} {S : Setting4 G T L V}

namespace Ctx76_F4
open CFSG.Quasithin.H13.A6.Setting4.Ctx76_F4

variable {H K : Subgroup G} [IsMulCommutative ↥(conjClosure S.V3 H)]
  {α : ↥(alternatingGroup (Fin 8)) ≃* GL (Fin 4) (ZMod 2)}

@[expose] noncomputable def cls7_F4 (C : S.Ctx76_F4 H K (FFModel.a7Four α))
    (u : ↥(conjClosure S.V3 H)) : Fin 4 → ZMod 2 :=
  A6L76T.vec7 α (C.βU_F4 u)

variable (C : S.Ctx76_F4 H K (FFModel.a7Four α))

theorem cls7_mul_F4 (u u' : ↥(conjClosure S.V3 H)) : C.cls7_F4 (u * u') = C.cls7_F4 u + C.cls7_F4 u' := by
  rw [cls7_F4, cls7_F4, cls7_F4, map_mul, A6L76T.vec7_mul]

theorem cls7_eq_zero_iff_F4 (u : ↥(conjClosure S.V3 H)) : C.cls7_F4 u = 0 ↔ C.βU_F4 u = 1 := by
  rw [cls7_F4, ← A6L76T.vec7_one α]
  exact (A6L76T.vec7_injective α).eq_iff

theorem cls7_inj_F4 {u u' : ↥(conjClosure S.V3 H)} (h : C.cls7_F4 u = C.cls7_F4 u') :
    C.βU_F4 u = C.βU_F4 u' :=
  A6L76T.vec7_injective α h

theorem cls7_equiv_F4 (k : ↥K) (u : ↥(conjClosure S.V3 H))
    (hku : (k : G) * u * (k : G)⁻¹ ∈ conjClosure S.V3 H) :
    C.cls7_F4 ⟨_, hku⟩ = A6L76T.mat7 α (C.α_F4 k) *ᵥ C.cls7_F4 u := by
  obtain ⟨m, hxm⟩ := QuotientGroup.mk_surjective (C.βU_F4 u)
  rw [cls7_F4, C.βU_equiv_F4 k u hku m.2 hxm.symm, A6L76T.vec7_mk, cls7_F4, ← hxm, A6L76T.vec7_mk]
  rfl

theorem βU_eq_one_iff_V1₇_F4 (hfix : fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
    ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) = ⊥) (u : ↥(conjClosure S.V3 H)) :
    C.βU_F4 u = 1 ↔ (u : G) ∈ fsuV1 T V := by
  obtain ⟨-, -, -, -, -, -, -, -, hβk, -⟩ := C.hR
  rw [βU_F4, MonoidHom.comp_apply, hβk, hfix, bot_inf_eq, Subgroup.mem_bot, C.ι_coe_F4,
    A6Mod.secMk_eq_one_iff]

@[expose] noncomputable def cv27_F4 : Fin 4 → ZMod 2 := C.cls7_F4 ⟨S.v2, S.v2_mem_UH H⟩

@[expose] noncomputable def cv2g7_F4 {g : ↥(Subgroup.normalizer (V : Set G))}
    (hgL : (g : G) ∈ S.L1) : Fin 4 → ZMod 2 :=
  C.cls7_F4 ⟨_, C.conj_mem_UH_F4 (C.hL1K hgL) (S.v2_mem_UH H)⟩

variable {g : ↥(Subgroup.normalizer (V : Set G))} (hgL : (g : G) ∈ S.L1)
  (hg : S.frame.ρ g = swap 0 1 * swap 1 2)

include hg in

theorem cls7_V3_F4 {u : G} (hu3 : u ∈ S.V3) (huU : u ∈ conjClosure S.V3 H) :
    C.cls7_F4 ⟨u, huU⟩ = 0 ∨ A6L76Q.In3v C.cv27_F4 (C.cv2g7_F4 hgL) (C.cls7_F4 ⟨u, huU⟩) := by
  rcases C.classes_V3_gen_F4 hgL hg hu3 huU with h | h | h | h
  · exact Or.inl ((C.cls7_eq_zero_iff_F4 _).2 h)
  · exact Or.inr (Or.inl (congrArg (A6L76T.vec7 α) h))
  · exact Or.inr (Or.inr (Or.inl (congrArg (A6L76T.vec7 α) h)))
  · refine Or.inr (Or.inr (Or.inr ?_))
    rw [cls7_F4, h, A6L76T.vec7_mul]
    rfl

include hg in

theorem reps7_V3_F4 {z : Fin 4 → ZMod 2} (hz : z = 0 ∨ A6L76Q.In3v C.cv27_F4 (C.cv2g7_F4 hgL) z) :
    ∃ v ∈ S.V3, ∃ hvU : v ∈ conjClosure S.V3 H, C.cls7_F4 ⟨v, hvU⟩ = z := by
  rcases hz with rfl | rfl | rfl | rfl
  · refine ⟨1, S.V3.one_mem, (conjClosure S.V3 H).one_mem, ?_⟩
    rw [C.cls7_eq_zero_iff_F4, show (⟨1, (conjClosure S.V3 H).one_mem⟩ : ↥(conjClosure S.V3 H)) =
      1 from rfl, map_one]
  · exact ⟨S.v2, S.v2_mem_V3, S.v2_mem_UH H, rfl⟩
  · exact ⟨_, S.conj_v2_mem_V3 hg, C.conj_mem_UH_F4 (C.hL1K hgL) (S.v2_mem_UH H), rfl⟩
  · refine ⟨_, S.V3.mul_mem S.v2_mem_V3 (S.conj_v2_mem_V3 hg),
      (conjClosure S.V3 H).mul_mem (S.v2_mem_UH H) (C.conj_mem_UH_F4 (C.hL1K hgL) (S.v2_mem_UH H)),
      ?_⟩
    rw [show (⟨S.v2 * ((g : G) * S.v2 * (g : G)⁻¹), (conjClosure S.V3 H).mul_mem (S.v2_mem_UH H)
      (C.conj_mem_UH_F4 (C.hL1K hgL) (S.v2_mem_UH H))⟩ : ↥(conjClosure S.V3 H)) =
      ⟨S.v2, S.v2_mem_UH H⟩ * ⟨_, C.conj_mem_UH_F4 (C.hL1K hgL) (S.v2_mem_UH H)⟩ from rfl,
      cls7_mul_F4]
    rfl

include hg in

theorem conj_mem_V3_of_pres7_F4 (hfix : fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
    ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) = ⊥) {d : G} (hdK : d ∈ K)
    (hd : ∀ z, (z = 0 ∨ A6L76Q.In3v C.cv27_F4 (C.cv2g7_F4 hgL) z) →
      (A6L76T.mat7 α (C.α_F4 ⟨d, hdK⟩) *ᵥ z = 0 ∨
        A6L76Q.In3v C.cv27_F4 (C.cv2g7_F4 hgL) (A6L76T.mat7 α (C.α_F4 ⟨d, hdK⟩) *ᵥ z)))
    {v : G} (hv : v ∈ S.V3) : d * v * d⁻¹ ∈ S.V3 := by
  have hvU : v ∈ conjClosure S.V3 H := le_conjClosure _ _ hv
  have hc := C.cls7_equiv_F4 ⟨d, hdK⟩ ⟨v, hvU⟩ (C.conj_mem_UH_F4 hdK hvU)
  obtain ⟨v', hv'3, hv'U, hv'⟩ := C.reps7_V3_F4 hgL hg (z := C.cls7_F4 ⟨_, C.conj_mem_UH_F4 hdK hvU⟩)
    (by rw [hc]; exact hd _ (C.cls7_V3_F4 hgL hg hv hvU))
  have h1 := C.cls7_inj_F4 hv'
  have hmem : d * v * d⁻¹ * v'⁻¹ ∈ conjClosure S.V3 H :=
    (conjClosure S.V3 H).mul_mem (C.conj_mem_UH_F4 hdK hvU) ((conjClosure S.V3 H).inv_mem hv'U)
  have h2 : C.βU_F4 ⟨_, hmem⟩ = 1 := by
    have e : (⟨_, hmem⟩ : ↥(conjClosure S.V3 H)) =
        ⟨_, C.conj_mem_UH_F4 hdK hvU⟩ * (⟨v', hv'U⟩)⁻¹ := rfl
    rw [e, map_mul, map_inv, ← h1, mul_inv_cancel]
  have h3 := (C.βU_eq_one_iff_V1₇_F4 hfix _).1 h2
  have e : d * v * d⁻¹ = (d * v * d⁻¹ * v'⁻¹) * v' := by group
  rw [e]
  exact S.V3.mul_mem (S.fsuV1_le_V3 h3) hv'3

theorem hat_of_a7_F4 (h1337 : Stmt13_3_7_F4)
    (C : S.Ctx76_F4 H K (FFModel.a7Four α))
    (hfix : fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) = ⊥) : IsHatA6 L := by
  by_contra hhat
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (FFModel.a7Four α).Gam := inferInstanceAs (Finite ↥(alternatingGroup (Fin 7)))
  have hle := S.pRank_three_NV3_le_one_F4 C.h13315 h1337 hhat C.hH
  obtain ⟨g, hgL, hg⟩ := S.exists_g012
  have hx0 : C.cv27_F4 ≠ 0 := fun h => C.βU_v2_ne_one_F4 ((C.cls7_eq_zero_iff_F4 _).1 h)
  have hy0 : C.cv2g7_F4 hgL ≠ 0 := fun h => C.βU_v2g_ne_one_F4 hgL ((C.cls7_eq_zero_iff_F4 _).1 h)
  have hxy : C.cv27_F4 ≠ C.cv2g7_F4 hgL := fun h => C.βU_v2_ne_v2g_F4 hgL hg (C.cls7_inj_F4 h)
  obtain ⟨x, y, hE, hxs, hys⟩ := A6L76S.exists_e9_lineStab α hx0 hy0 hxy
  set Y : Subgroup (FFModel.a7Four α).Gam :=
    (A6L76S.lineStab C.cv27_F4 (C.cv2g7_F4 hgL)).comap (α.toMonoidHom.comp altLift7) with hY
  have hpres : ∀ d : ↥K, C.α_F4 d ∈ Y → ∀ z, (z = 0 ∨ A6L76Q.In3v C.cv27_F4 (C.cv2g7_F4 hgL) z) →
      (A6L76T.mat7 α (C.α_F4 d) *ᵥ z = 0 ∨
        A6L76Q.In3v C.cv27_F4 (C.cv2g7_F4 hgL) (A6L76T.mat7 α (C.α_F4 d) *ᵥ z)) := by
    intro d hd z hz
    rcases hz with rfl | hz
    · left
      exact Matrix.mulVec_zero _
    · right
      exact hd z hz
  have h2 : 2 ≤ CFSG.Open.pRank 3 Y :=
    A6L76B.two_le_pRank_of_e9 (show x ∈ Y from hxs) (show y ∈ Y from hys) hE
  have h3 := A6L76B.pRank_map_le C.α_F4 C.not_three_dvd_ker_F4 (Y.comap C.α_F4)
  rw [Subgroup.map_comap_eq_self_of_surjective C.α_surj_F4] at h3
  have h4 := A6L76F.pRank_le_map_of_not_dvd (p := 3) K.subtype
    (by rw [Subgroup.ker_subtype, Subgroup.card_bot]; norm_num) (Y.comap C.α_F4)
  have hfwd : ∀ d : ↥K, d ∈ Y.comap C.α_F4 → ∀ v ∈ S.V3, (d : G) * v * (d : G)⁻¹ ∈ S.V3 :=
    fun d hd v hv => C.conj_mem_V3_of_pres7_F4 hgL hg hfix d.2 (hpres d hd) hv
  have hXN : (Y.comap C.α_F4).map K.subtype ≤ H ⊓ Subgroup.normalizer (S.V3 : Set G) := by
    rintro _ ⟨d, hd, rfl⟩
    refine ⟨C.hKH_F4 d.2, Subgroup.mem_normalizer_iff.2 fun v => ⟨hfwd d hd v, fun h' => ?_⟩⟩
    have h1 : ((d⁻¹ : ↥K) : G) * ((d : G) * v * (d : G)⁻¹) * ((d⁻¹ : ↥K) : G)⁻¹ ∈ S.V3 :=
      hfwd d⁻¹ ((Y.comap C.α_F4).inv_mem hd) _ h'
    have e : ((d⁻¹ : ↥K) : G) * ((d : G) * v * (d : G)⁻¹) * ((d⁻¹ : ↥K) : G)⁻¹ = v := by
      rw [Subgroup.coe_inv]
      group
    rwa [e] at h1
  have h5 := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hXN
  omega

include C in

theorem card_tildeU_a7_F4 (hfix : fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) = ⊥) :
    Nat.card (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) = 2 ^ 4 := by
  obtain ⟨-, -, -, -, -, -, -, hβs, hβk, -⟩ := C.hR
  have hβi : Function.Injective C.β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have h1 := (hβk u).1 hu
    rw [hfix, bot_inf_eq, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  have e1 : Nat.card ↥(commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) = Nat.card (Sec
        (⊤ : Subgroup ↥(conjClosure S.V3 H)) ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) := by
    rw [C.top_F4, Subgroup.card_top]
  rw [← e1, Nat.card_congr (Equiv.ofBijective _ ⟨hβi, hβs⟩), A6L76T.card_secKer7]

include C in

theorem tilde_eq_a7_F4 (hfix : fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) = ⊥) :
    autSec (autOn H (conjClosure S.V3 H)) ⊤ ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) =
      autSec (autOn K (conjClosure S.V3 H)) ⊤ ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) := by
  have hHU := le_normalizer_conjClosure S.V3 H
  have hHV := S.le_normalizer_UV1 C.hH
  have hK : Nat.card ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) = 2520 := by
    rw [← Nat.card_congr C.eπ_F4.toEquiv]
    show Nat.card ↥(alternatingGroup (Fin 7)) = 2520
    rw [nat_card_alternatingGroup, Nat.card_fin]
    rfl
  have hN := CFSG.QuasithinUnique.L246.C123.normalizer_eq_of_card_2520 C.sq_tildeU_F4
    (by rw [C.card_tildeU_a7_F4 hfix]; rfl) hK
  refine le_antisymm ?_ (autSec_mono (InternalSec.autOn_le_autOn_of_le C.hKH_F4) _ _)
  rw [← hN]
  intro x hx
  obtain ⟨h, -, rfl⟩ := (A6Mod.mem_autSec_iff hHU hHV le_rfl).1 hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨k, hkK, rfl⟩ := (A6Mod.mem_autSec_iff hHU hHV C.hKH_F4).1 hy
    refine (A6Mod.mem_autSec_iff hHU hHV C.hKH_F4).2 ⟨h * k * h⁻¹, ?_, by
      rw [map_mul, map_mul, map_inv]⟩
    exact (Subgroup.mem_normalizer_iff.mp (C.hHK h.2) k).mp hkK
  · intro hy
    obtain ⟨k, hkK, hk⟩ := (A6Mod.mem_autSec_iff hHU hHV C.hKH_F4).1 hy
    refine (A6Mod.mem_autSec_iff hHU hHV C.hKH_F4).2 ⟨h⁻¹ * k * h, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (C.hHK (H.inv_mem h.2)) k).mp hkK
      simpa using this
    · rw [map_mul, map_mul, map_inv, hk]
      group

end Ctx76_F4

end Setting4

end CFSG.Quasithin.H13.A6
