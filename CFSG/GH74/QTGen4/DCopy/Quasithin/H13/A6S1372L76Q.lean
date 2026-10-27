module

public import CFSG.Quasithin.H13.A6S1372L76Q
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372L76K
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372L76N
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372L76P2

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

@[expose] noncomputable def cls_F4
    (C : S.Ctx76_F4 H K (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2))))
    (u : ↥(conjClosure S.V3 H)) : Fin 4 → ZMod 2 :=
  A6L76Q.natVec (C.βU_F4 u)

variable (C : S.Ctx76_F4 H K (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2))))

theorem cls_mul_F4 (u u' : ↥(conjClosure S.V3 H)) : C.cls_F4 (u * u') = C.cls_F4 u + C.cls_F4 u' := by
  rw [cls_F4, cls_F4, cls_F4, map_mul, A6L76Q.natVec_mul]

theorem cls_eq_zero_iff_F4 (u : ↥(conjClosure S.V3 H)) : C.cls_F4 u = 0 ↔ C.βU_F4 u = 1 := by
  rw [cls_F4, ← A6L76Q.natVec_one]
  exact A6L76Q.natVec_injective.eq_iff

theorem cls_inj_F4 {u u' : ↥(conjClosure S.V3 H)} (h : C.cls_F4 u = C.cls_F4 u') : C.βU_F4 u = C.βU_F4 u' :=
  A6L76Q.natVec_injective h

theorem cls_equiv_F4 (k : ↥K) (u : ↥(conjClosure S.V3 H))
    (hku : (k : G) * u * (k : G)⁻¹ ∈ conjClosure S.V3 H) :
    C.cls_F4 ⟨_, hku⟩ = A6L76Q.mat (C.α_F4 k) *ᵥ C.cls_F4 u := by
  obtain ⟨m, hxm⟩ := QuotientGroup.mk_surjective (C.βU_F4 u)
  rw [cls_F4, C.βU_equiv_F4 k u hku m.2 hxm.symm, A6L76Q.natVec_mk, cls_F4, ← hxm, A6L76Q.natVec_mk]
  rfl

theorem βU_eq_one_iff_V1_F4 (hfix : fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
    ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) = ⊥) (u : ↥(conjClosure S.V3 H)) :
    C.βU_F4 u = 1 ↔ (u : G) ∈ fsuV1 T V := by
  obtain ⟨-, -, -, -, -, -, -, -, hβk, -⟩ := C.hR
  rw [βU_F4, MonoidHom.comp_apply, hβk, hfix, bot_inf_eq, Subgroup.mem_bot, C.ι_coe_F4,
    A6Mod.secMk_eq_one_iff]

@[expose] noncomputable def cv2_F4 : Fin 4 → ZMod 2 := C.cls_F4 ⟨S.v2, S.v2_mem_UH H⟩

@[expose] noncomputable def cv2g_F4 {g : ↥(Subgroup.normalizer (V : Set G))}
    (hgL : (g : G) ∈ S.L1) : Fin 4 → ZMod 2 :=
  C.cls_F4 ⟨_, C.conj_mem_UH_F4 (C.hL1K hgL) (S.v2_mem_UH H)⟩

variable {g : ↥(Subgroup.normalizer (V : Set G))} (hgL : (g : G) ∈ S.L1)
  (hg : S.frame.ρ g = swap 0 1 * swap 1 2)

include hg in

theorem cls_V3_F4 {u : G} (hu3 : u ∈ S.V3) (huU : u ∈ conjClosure S.V3 H) :
    C.cls_F4 ⟨u, huU⟩ = 0 ∨ A6L76Q.In3v C.cv2_F4 (C.cv2g_F4 hgL) (C.cls_F4 ⟨u, huU⟩) := by
  rcases C.classes_V3_gen_F4 hgL hg hu3 huU with h | h | h | h
  · exact Or.inl ((C.cls_eq_zero_iff_F4 _).2 h)
  · exact Or.inr (Or.inl (congrArg A6L76Q.natVec h))
  · exact Or.inr (Or.inr (Or.inl (congrArg A6L76Q.natVec h)))
  · refine Or.inr (Or.inr (Or.inr ?_))
    rw [cls_F4, h, A6L76Q.natVec_mul]
    rfl

include hg in

theorem reps_V3'_F4 {z : Fin 4 → ZMod 2} (hz : z = 0 ∨ A6L76Q.In3v C.cv2_F4 (C.cv2g_F4 hgL) z) :
    ∃ v ∈ S.V3, ∃ hvU : v ∈ conjClosure S.V3 H, C.cls_F4 ⟨v, hvU⟩ = z := by
  rcases hz with rfl | rfl | rfl | rfl
  · refine ⟨1, S.V3.one_mem, (conjClosure S.V3 H).one_mem, ?_⟩
    rw [C.cls_eq_zero_iff_F4, show (⟨1, (conjClosure S.V3 H).one_mem⟩ : ↥(conjClosure S.V3 H)) =
      1 from rfl, map_one]
  · exact ⟨S.v2, S.v2_mem_V3, S.v2_mem_UH H, rfl⟩
  · exact ⟨_, S.conj_v2_mem_V3 hg, C.conj_mem_UH_F4 (C.hL1K hgL) (S.v2_mem_UH H), rfl⟩
  · refine ⟨_, S.V3.mul_mem S.v2_mem_V3 (S.conj_v2_mem_V3 hg),
      (conjClosure S.V3 H).mul_mem (S.v2_mem_UH H) (C.conj_mem_UH_F4 (C.hL1K hgL) (S.v2_mem_UH H)),
      ?_⟩
    rw [show (⟨S.v2 * ((g : G) * S.v2 * (g : G)⁻¹), (conjClosure S.V3 H).mul_mem (S.v2_mem_UH H)
      (C.conj_mem_UH_F4 (C.hL1K hgL) (S.v2_mem_UH H))⟩ : ↥(conjClosure S.V3 H)) =
      ⟨S.v2, S.v2_mem_UH H⟩ * ⟨_, C.conj_mem_UH_F4 (C.hL1K hgL) (S.v2_mem_UH H)⟩ from rfl, cls_mul_F4]
    rfl

include hg in

theorem conj_mem_V3_of_pres_F4 (hfix : fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
    ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) = ⊥) {d : G} (hdK : d ∈ K)
    (hd : ∀ z, (z = 0 ∨ A6L76Q.In3v C.cv2_F4 (C.cv2g_F4 hgL) z) →
      (A6L76Q.mat (C.α_F4 ⟨d, hdK⟩) *ᵥ z = 0 ∨
        A6L76Q.In3v C.cv2_F4 (C.cv2g_F4 hgL) (A6L76Q.mat (C.α_F4 ⟨d, hdK⟩) *ᵥ z)))
    {v : G} (hv : v ∈ S.V3) : d * v * d⁻¹ ∈ S.V3 := by
  have hvU : v ∈ conjClosure S.V3 H := le_conjClosure _ _ hv
  have hc := C.cls_equiv_F4 ⟨d, hdK⟩ ⟨v, hvU⟩ (C.conj_mem_UH_F4 hdK hvU)
  obtain ⟨v', hv'3, hv'U, hv'⟩ := C.reps_V3'_F4 hgL hg (z := C.cls_F4 ⟨_, C.conj_mem_UH_F4 hdK hvU⟩)
    (by rw [hc]; exact hd _ (C.cls_V3_F4 hgL hg hv hvU))
  have h1 := C.cls_inj_F4 hv'
  have hmem : d * v * d⁻¹ * v'⁻¹ ∈ conjClosure S.V3 H :=
    (conjClosure S.V3 H).mul_mem (C.conj_mem_UH_F4 hdK hvU) ((conjClosure S.V3 H).inv_mem hv'U)
  have h2 : C.βU_F4 ⟨_, hmem⟩ = 1 := by
    have e : (⟨_, hmem⟩ : ↥(conjClosure S.V3 H)) =
        ⟨_, C.conj_mem_UH_F4 hdK hvU⟩ * (⟨v', hv'U⟩)⁻¹ := rfl
    rw [e, map_mul, map_inv, ← h1, mul_inv_cancel]
  have h3 := (C.βU_eq_one_iff_V1_F4 hfix _).1 h2
  have e : d * v * d⁻¹ = (d * v * d⁻¹ * v'⁻¹) * v' := by group
  rw [e]
  exact S.V3.mul_mem (S.fsuV1_le_V3 h3) hv'3

end Ctx76_F4

namespace Ctx76_F4
open CFSG.Quasithin.H13.A6.Setting4.Ctx76_F4

variable {H K : Subgroup G} [IsMulCommutative ↥(conjClosure S.V3 H)] {D : FFModel}

theorem exists_conj_mem_αT_F4 [Finite D.Gam] (C : S.Ctx76_F4 H K D) {X : Subgroup D.Gam}
    (hX : IsPGroup 2 X) : ∃ g : D.Gam, ∀ x ∈ X,
      g⁻¹ * x * g ∈ ((T ⊓ K).subgroupOf K).map C.α_F4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 D.Gam := (C.isPGroup_αT_F4).toSylow C.not_two_dvd_index_αT_F4
  obtain ⟨Q, hXQ⟩ := hX.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq D.Gam P Q
  refine ⟨g, fun x hx => ?_⟩
  have hxQ : x ∈ (Q : Subgroup D.Gam) := hXQ hx
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxQ
  have e : (MulAut.conj g)⁻¹ • x = g⁻¹ * x * g := by
    rw [← map_inv, MulAut.smul_def, MulAut.conj_apply, inv_inv]
  rw [← e]
  exact (IsPGroup.mem_toSylow _ _).1 hxQ

variable {H K : Subgroup G} [IsMulCommutative ↥(conjClosure S.V3 H)]

theorem hat_of_four_F4 (h1337 : Stmt13_3_7_F4)
    (C : S.Ctx76_F4 H K (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2))))
    (hfix : fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) = ⊥) : IsHatA6 L := by
  by_contra hhat
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle := S.pRank_three_NV3_le_one_F4 C.h13315 h1337 hhat C.hH
  have := A6L76Q.finite_gam
  obtain ⟨g, hgL, hg⟩ := S.exists_g012
  have hx0 : C.cv2_F4 ≠ 0 := fun h => C.βU_v2_ne_one_F4 ((C.cls_eq_zero_iff_F4 _).1 h)
  have hy0 : C.cv2g_F4 hgL ≠ 0 := fun h => C.βU_v2g_ne_one_F4 hgL ((C.cls_eq_zero_iff_F4 _).1 h)
  have hxy : C.cv2_F4 ≠ C.cv2g_F4 hgL := fun h => C.βU_v2_ne_v2g_F4 hgL hg (C.cls_inj_F4 h)

  have hT : ∀ t : ↥K, (t : G) ∈ T → ∀ z, (z = 0 ∨ A6L76Q.In3v C.cv2_F4 (C.cv2g_F4 hgL) z) →
      (A6L76Q.mat (C.α_F4 t) *ᵥ z = 0 ∨
        A6L76Q.In3v C.cv2_F4 (C.cv2g_F4 hgL) (A6L76Q.mat (C.α_F4 t) *ᵥ z)) := by
    intro t ht z hz
    obtain ⟨v, hv3, hvU, rfl⟩ := C.reps_V3'_F4 hgL hg hz
    rw [← C.cls_equiv_F4 t ⟨v, hvU⟩ (C.conj_mem_UH_F4 t.2 hvU)]
    exact C.cls_V3_F4 hgL hg ((Subgroup.mem_normalizer_iff.mp (S.T_le_normalizer_V3 ht) v).mp hv3) _

  have hinj : ∀ (σ : (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2))).Gam) z z',
      A6L76Q.mat σ *ᵥ z = A6L76Q.mat σ *ᵥ z' → z = z' := by
    intro σ z z' h
    have := congrArg (A6L76Q.mat σ⁻¹ *ᵥ ·) h
    simp only [Matrix.mulVec_mulVec, A6L76Q.mat_inv_mul, Matrix.one_mulVec] at this
    exact this
  have hne0 : ∀ (σ : (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2))).Gam) z,
      z ≠ 0 → A6L76Q.mat σ *ᵥ z ≠ 0 := fun σ z hz h =>
    hz (hinj σ z 0 (h.trans (Matrix.mulVec_zero _).symm))

  obtain ⟨h, hh⟩ := C.exists_conj_mem_αT_F4 (A6L76N.isPGroup_U 4)
  set a := A6L76Q.mat h *ᵥ C.cv2_F4 with ha
  set b := A6L76Q.mat h *ᵥ C.cv2g_F4 hgL with hb
  have hgen : ∀ (i j : Fin 4) (hij : i < j), A6L76Q.In3v a b
      (Matrix.transvection i j (1 : ZMod 2) *ᵥ a) ∧ A6L76Q.In3v a b
        (Matrix.transvection i j (1 : ZMod 2) *ᵥ b) := by
    intro i j hij
    obtain ⟨t, ht, hte⟩ := hh _ (Subgroup.mem_map_of_mem _ (A6L76N.tv_mem hij))
    have hT' := hT t (Subgroup.mem_subgroupOf.1 ht).1
    have key : ∀ z, Matrix.transvection i j (1 : ZMod 2) *ᵥ (A6L76Q.mat h *ᵥ z) =
        A6L76Q.mat h *ᵥ (A6L76Q.mat (C.α_F4 t) *ᵥ z) := by
      intro z
      have e : A6L76Q.mat h * A6L76Q.mat (C.α_F4 t) =
          Matrix.transvection i j (1 : ZMod 2) * A6L76Q.mat h := by
        rw [hte, A6L76Q.mat_mul, A6L76Q.mat_mul, ← mul_assoc, ← mul_assoc, A6L76Q.mat_mul_inv,
          one_mul]
        rfl
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e]
    have hcase : ∀ z, A6L76Q.In3v C.cv2_F4 (C.cv2g_F4 hgL) z → A6L76Q.In3v a b
        (Matrix.transvection i j (1 : ZMod 2) *ᵥ (A6L76Q.mat h *ᵥ z)) := by
      intro z hz
      rw [key]
      rcases hT' z (Or.inr hz) with h0 | h0
      · exfalso
        have hz0 : z ≠ 0 := by
          rcases hz with rfl | rfl | rfl
          · exact hx0
          · exact hy0
          · intro h1
            apply hxy
            have h2 := congrArg (· + C.cv2g_F4 hgL) h1
            simp only [zero_add, add_assoc, A6L76Q.add_self_vec, add_zero] at h2
            exact h2
        exact hne0 _ z hz0 h0
      · exact A6L76Q.in3v_mulVec _ h0
    exact ⟨hcase _ (Or.inl rfl), hcase _ (Or.inr (Or.inl rfl))⟩
  have ha0 : a ≠ 0 := hne0 h _ hx0
  have hb0 : b ≠ 0 := hne0 h _ hy0
  have hab : a ≠ b := fun e => hxy (hinj h _ _ e)
  obtain ⟨hLa, hLb⟩ := A6L76Q.lineU4 a b ha0 hb0 hab (hgen 0 1 (by decide)).1
    (hgen 0 1 (by decide)).2 (hgen 1 2 (by decide)).1 (hgen 1 2 (by decide)).2
    (hgen 2 3 (by decide)).1 (hgen 2 3 (by decide)).2

  set Y := A6L76Q.P0.map (MulAut.conj h⁻¹).toMonoidHom with hY
  have hpres : ∀ d : ↥K, C.α_F4 d ∈ Y → ∀ z, (z = 0 ∨ A6L76Q.In3v C.cv2_F4 (C.cv2g_F4 hgL) z) →
      (A6L76Q.mat (C.α_F4 d) *ᵥ z = 0 ∨
        A6L76Q.In3v C.cv2_F4 (C.cv2g_F4 hgL) (A6L76Q.mat (C.α_F4 d) *ᵥ z)) := by
    intro d hd z hz
    obtain ⟨σ, hσ, hσd⟩ := hd
    have hσ' : C.α_F4 d = h⁻¹ * σ * h := by
      rw [← hσd]
      show h⁻¹ * σ * h⁻¹⁻¹ = h⁻¹ * σ * h
      rw [inv_inv]
    have hmz : A6L76Q.InL (A6L76Q.mat h *ᵥ z) := by
      rcases hz with rfl | hz
      · rw [Matrix.mulVec_zero]
        exact ⟨rfl, rfl⟩
      · exact A6L76Q.inL_of_in3v hLa hLb (A6L76Q.in3v_mulVec _ hz)
    have hsz := A6L76Q.BUT_mulVec hσ hmz
    have e : A6L76Q.mat (C.α_F4 d) *ᵥ z =
        A6L76Q.mat h⁻¹ *ᵥ (A6L76Q.mat σ *ᵥ (A6L76Q.mat h *ᵥ z)) := by
      rw [hσ', A6L76Q.mat_mul, A6L76Q.mat_mul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    rw [e]
    rcases A6L76Q.spanL a b _ hLa hLb ha0 hb0 hab hsz with h0 | h0
    · left
      rw [h0, Matrix.mulVec_zero]
    · right
      have hback : ∀ x, A6L76Q.mat h⁻¹ *ᵥ (A6L76Q.mat h *ᵥ x) = x := fun x => by
        rw [Matrix.mulVec_mulVec, A6L76Q.mat_inv_mul, Matrix.one_mulVec]
      have := A6L76Q.in3v_mulVec (A6L76Q.mat h⁻¹) h0
      rwa [ha, hb, hback, hback] at this

  obtain ⟨hr1, hr2⟩ := A6L76Q.BUT_rot
  have hE0 := A6L76M.e9_rot (F := ZMod 2) (n := 4) rfl (p := 0) (q := 1) (r := 2) (s := 3)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hE0' : A6L76B.E9Pair
      (A6L76M.slOf (A6L76M.rot (0 : Fin 4) 1) (A6L76M.det_rot (by decide)) :
        (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2))).Gam)
      (A6L76M.slOf (A6L76M.rot (2 : Fin 4) 3) (A6L76M.det_rot (by decide))) := hE0
  have hE := hE0'.map (MulAut.conj h⁻¹).toMonoidHom (MulAut.conj h⁻¹).injective
  have h2 : 2 ≤ CFSG.Open.pRank 3 Y := A6L76B.two_le_pRank_of_e9
    (Subgroup.mem_map_of_mem _ (show _ ∈ A6L76Q.P0 from hr1))
    (Subgroup.mem_map_of_mem _ (show _ ∈ A6L76Q.P0 from hr2)) hE
  have h3 := A6L76B.pRank_map_le C.α_F4 C.not_three_dvd_ker_F4 (Y.comap C.α_F4)
  rw [Subgroup.map_comap_eq_self_of_surjective C.α_surj_F4] at h3
  have h4 := A6L76F.pRank_le_map_of_not_dvd (p := 3) K.subtype
    (by rw [Subgroup.ker_subtype, Subgroup.card_bot]; norm_num) (Y.comap C.α_F4)
  have hfwd : ∀ d : ↥K, d ∈ Y.comap C.α_F4 → ∀ v ∈ S.V3, (d : G) * v * (d : G)⁻¹ ∈ S.V3 :=
    fun d hd v hv => C.conj_mem_V3_of_pres_F4 hgL hg hfix d.2 (hpres d hd) hv
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

theorem sq_tildeU_F4 (C : S.Ctx76_F4 H K D)
    (a : Sec (⊤ : Subgroup ↥(conjClosure S.V3 H)) ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) :
    a ^ 2 = 1 := by
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective a
  have hw : w ^ 2 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    exact C.hab.2 _ w.1.2
  rw [← QuotientGroup.mk_pow, hw, QuotientGroup.mk_one]

theorem card_tildeU_four_F4
    (C : S.Ctx76_F4 H K (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2))))
    (hfix : fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
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
  rw [← e1, Nat.card_congr (Equiv.ofBijective _ ⟨hβi, hβs⟩), A6L76Q.card_secKer]

theorem tilde_eq_of_four_F4
    (C : S.Ctx76_F4 H K (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2))))
    (hfix : fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) = ⊥) :
    autSec (autOn H (conjClosure S.V3 H)) ⊤ ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) =
      autSec (autOn K (conjClosure S.V3 H)) ⊤ ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2)
    (fun a b : Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) => mul_comm a b) C.sq_tildeU_F4
    (C.card_tildeU_four_F4 hfix)
  have h1 := CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e
  have h2 : Nat.card ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) = Nat.card (MulAut (Sec
        (⊤ : Subgroup ↥(conjClosure S.V3 H)) ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) := by
    rw [h1, ← A6L76Q.card_gam]
    exact (Nat.card_congr C.eπ_F4.toEquiv).symm
  have : Finite (MulAut (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) :=
    Nat.finite_of_card_ne_zero (by rw [h1]; exact Nat.card_pos.ne')
  have htop := Subgroup.eq_top_of_card_eq _ h2
  refine le_antisymm ?_ (autSec_mono (InternalSec.autOn_le_autOn_of_le C.hKH_F4) _ _)
  rw [htop]
  exact le_top

theorem binaryNatural_of_four_F4
    (C : S.Ctx76_F4 H K (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2))))
    (hfix : fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) = ⊥) :
    BinaryNaturalSL (autSec (autOn H (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊤ ⊥ 4 1 := by
  refine ⟨ZMod 2, inferInstance, inferInstance, by rw [Nat.card_zmod, pow_one], ?_⟩
  have hR := (CFSG.Quasithin.H.Mathieu.realizes_iff _ _ _ _).2 ⟨C.π, C.β, C.hR⟩
  rw [C.top_F4, hfix, bot_inf_eq] at hR
  rw [C.tilde_eq_of_four_F4 hfix]
  exact hR

end Ctx76_F4

variable (S)
include S

theorem lem1376_one_F4 (hB : Lem1376L1K_F4) (h3 : Lem1376NThree_F4)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h13314 : Stmt13_3_14_F4) (h13315 : Stmt13_3_15_F4)
    (h1356two : Input1356Two_F4) (h1337 : Stmt13_3_7_F4) (hNS : ¬ LieModel G .PSp 3 2 1)
    (hNU : ¬ LieModel G .PSU 4 3 1) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hab : IsElemAbelian 2 (conjClosure S.V3 H)) [IsMulCommutative ↥(conjClosure S.V3 H)]
    {K : Subgroup G} (hK : K ∈ cComp H) (n : ℕ) (hn : 3 ≤ n)
    (hBN : BinaryNaturalSL (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
      (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
      (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
        commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) n 1) :
    n = 4 ∧ IsHatA6 L ∧ BinaryNaturalSL (autSec (autOn H (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊤ ⊥ 4 1 := by
  have hle := S.lem1376_one_le_four_F4 hB h37 h38 h13314 h13315 h1356two hNS hNU hH hab hK n hn hBN
  have hL1K := hB G T L V S hNS hNU H hH hab K hK (Or.inl ⟨n, hn, hBN⟩)
  have hn3 : n ≠ 3 := by
    rintro rfl
    exact h3 G T L V S hNS hNU H hH hab K hK hL1K hBN
  obtain rfl : n = 4 := by omega
  obtain ⟨F, _, _, hF, π, hπ⟩ := id hBN
  have hF2 : Nat.card F = 2 := by rw [hF, pow_one]
  obtain ⟨π', hπ'⟩ := A6L76O.realizesVia_zmod hF2 hπ
  have : IsSimpleGroup (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2))).Gam :=
    A6L76A.isSimpleGroup_statedSL (by norm_num) (Nat.card_zmod 2)
  obtain ⟨C⟩ := S.exists_ctx_F4 h37 h38 h13315 h1356two hNS hH hab hK hL1K
    (A6L76A.not_isSolvable_statedSL (by norm_num)) ⟨π', hπ'⟩
  have hfix := kgSL4Split_holds _ _ (fun v => (sq v).symm.trans (C.sq_tildeU_F4 v)) C.top_F4 hBN
  exact ⟨rfl, C.hat_of_four_F4 h1337 hfix, C.binaryNatural_of_four_F4 hfix⟩

end Setting4

end CFSG.Quasithin.H13.A6
