module

public import CFSG.Quasithin.H13.L32NLem14333b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14333a

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint L14332 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace L14333

variable {G : Type} [Group G]

variable [CFSG.GH74.QTGen4.Finite4 G]

namespace Ctx_F4
open CFSG.Quasithin.H13.L14333.Ctx_F4

variable {T L V V₂ K : Subgroup G} {g a z b d x : G} {D : HatModelU (fsuU T V)}
  (c : Ctx_F4 G T L V V₂ K g a z b d x D)
include c

theorem L_le_normV_F4 : L ≤ Subgroup.normalizer (V : Set G) := by
  obtain ⟨_, S⟩ := c.setting
  exact S.LV_F4

theorem T_le_normL_F4 : T ≤ Subgroup.normalizer (L : Set G) := by
  obtain ⟨_, S⟩ := c.setting
  exact S.TL_F4

theorem U_le_T_F4 : fsuU T V ≤ T := (fsuU_le_pCoreOf c.ctx).trans c.q_le

theorem cent_le_pCoreOf_F4 : (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (L ⊔ T) := by
  obtain ⟨_, S⟩ := c.setting
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le S.LV_F4 S.TV_F4
  exact le_pCoreOf_of_le_normalizer 2 inf_le_left
    (fun y hy => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hy, normalizer_le_normalizer_centralizer'' V (hLTV hy)⟩)
    S.isPGroup_cent_sup_F4

theorem zU_le_pCoreOf_F4 : centerOf (fsuU T V) ≤ pCoreOf 2 (L ⊔ T) := by
  refine le_trans ?_ c.cent_le_pCoreOf_F4
  intro y hy
  refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_right (c.U_le_T_F4 (Subgroup.mem_inf.mp hy).1),
    Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
  exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hy).2 v (c.ctx.V_U hv)

theorem X_le_pCoreOf_F4 : conjClosure (centerOf (fsuU T V)) L ≤ pCoreOf 2 (L ⊔ T) :=
  conjClosure_le fun _ hl _ hy => conj_mem_pCoreOf hl (c.zU_le_pCoreOf_F4 hy)

theorem isPGroup_X_F4 : IsPGroup 2 ↥(conjClosure (centerOf (fsuU T V)) L) :=
  (pCoreOf_isPGroup 2 (L ⊔ T)).to_le c.X_le_pCoreOf_F4

theorem isPGroup_zU_F4 : IsPGroup 2 ↥(centerOf (fsuU T V)) :=
  c.ctx.U2.to_le inf_le_left

theorem tight_zU_F4 :
    CFSG.ComponentClassification.AschbacherTightEmbedding.TightlyEmbedded
      (centerOf (fsuU T V)) := by
  rw [← c.zpowers_d_F4]
  refine S143.tightlyEmbedded_zpowers_of_sq c.d_sq c.z_ne c.z_sq_F4 fun h hh => ?_
  obtain ⟨_, S⟩ := c.setting
  rw [c.zpowers_d_F4]
  exact l32nH_le_normalizer_zU (S.mem_g1_F4 c.z_mem c.z_ne hh)

theorem X_comm_F4 : ∀ u ∈ conjClosure (centerOf (fsuU T V)) L,
    ∀ w ∈ conjClosure (centerOf (fsuU T V)) L, u * w = w * u := by
  set Z := centerOf (fsuU T V) with hZ
  set S' := pCoreOf 2 (L ⊔ T)
  have hS : CFSG.QuasithinUnique.Tight.Setup Z ⊤ Z S' := by
    refine ⟨c.tight_zU_F4, ⟨le_inf le_top le_rfl, c.isPGroup_zU_F4, ?_⟩, ?_, pCoreOf_isPGroup 2 _,
      le_top, c.zU_le_pCoreOf_F4⟩
    · rw [Subgroup.subgroupOf_eq_top.mpr inf_le_right, Subgroup.index_top]
      norm_num
    · intro h
      have : d ∈ Z := c.d_mem
      rw [h, Subgroup.mem_bot] at this
      apply c.z_ne
      rw [← c.d_sq, this, mul_one]
  have hΦ : ∃ y ∈ Z, y ^ 2 ≠ 1 := ⟨d, c.d_mem, by rw [pow_two, c.d_sq]; exact c.z_ne⟩
  have hcomm := S143.Wgen_comm (hS.delta_commute hΦ) (by
    rintro R ⟨⟨h, -, rfl⟩, -⟩ u hu w hw
    rw [CFSG.QuasithinUnique.BenderBranch.mem_conjugate_iff] at hu hw
    have hc := zU_comm (fsuU T V) _ hu _ hw
    calc u * w = h⁻¹ * ((h * u * h⁻¹) * (h * w * h⁻¹)) * h := by group
      _ = h⁻¹ * ((h * w * h⁻¹) * (h * u * h⁻¹)) * h := by rw [hc]
      _ = w * u := by group)
  have hle : conjClosure Z L ≤ CFSG.QuasithinUnique.Tight.Wgen
      (CFSG.QuasithinUnique.Tight.Delta ⊤ Z S') := by
    refine conjClosure_le fun l hl y hy => Subgroup.subset_closure ?_
    refine ⟨CFSG.conjugate Z l⁻¹, ⟨⟨l⁻¹, Subgroup.mem_top _, rfl⟩, fun w hw => ?_⟩, ?_⟩
    · rw [CFSG.QuasithinUnique.BenderBranch.mem_conjugate_iff] at hw
      have := conj_mem_pCoreOf hl (c.zU_le_pCoreOf_F4 hw)
      simpa [mul_assoc] using this
    · rw [CFSG.QuasithinUnique.BenderBranch.mem_conjugate_iff]
      simpa [mul_assoc] using hy
  exact fun u hu w hw => hcomm u (hle hu) w (hle hw)

theorem V_le_X_F4 (hV : V = conjClosure (fsuV1 T V) L) :
    V ≤ conjClosure (centerOf (fsuU T V)) L := by
  have hV1 : fsuV1 T V ≤ centerOf (fsuU T V) := c.vZ ▸ inf_le_right
  conv_lhs => rw [hV]
  exact conjClosure_mono hV1 le_rfl

theorem exists_sq_F4 (hV : V = conjClosure (fsuV1 T V) L) :
    ∀ v ∈ V, ∃ y ∈ conjClosure (centerOf (fsuU T V)) L, y * y = v := by
  intro v hv
  rw [hV] at hv
  induction hv using Subgroup.closure_induction with
  | mem v hv =>
    obtain ⟨l, hl, w, hw, rfl⟩ := hv
    rcases c.eq_of_mem_V1_F4 hw with rfl | rfl
    · exact ⟨1, Subgroup.one_mem _, by group⟩
    · refine ⟨l * d * l⁻¹, mem_conjClosure hl c.d_mem, ?_⟩
      rw [← c.d_sq]
      group
  | one => exact ⟨1, Subgroup.one_mem _, by group⟩
  | mul v w _ _ ihv ihw =>
    obtain ⟨y, hy, rfl⟩ := ihv
    obtain ⟨y', hy', rfl⟩ := ihw
    refine ⟨y * y', Subgroup.mul_mem _ hy hy', ?_⟩
    rw [mul_assoc, ← mul_assoc y', c.X_comm_F4 y' hy' y hy]
    group
  | inv v _ ihv =>
    obtain ⟨y, hy, rfl⟩ := ihv
    exact ⟨y⁻¹, Subgroup.inv_mem _ hy, by group⟩

theorem card_V_F4 : Nat.card V = 8 := by
  obtain ⟨_, S⟩ := c.setting
  exact S.card_V_F4

theorem mul_self_V_F4 {v : G} (hv : v ∈ V) : v * v = 1 := by
  obtain ⟨_, S⟩ := c.setting
  exact S.mul_self_V_F4 hv

theorem card_X_ge_F4 (hV : V = conjClosure (fsuV1 T V) L) :
    64 ≤ Nat.card ↥(conjClosure (centerOf (fsuU T V)) L) := by
  have h := card_mul_le_of_sq c.X_comm_F4 (c.V_le_X_F4 hV) (fun v hv => c.mul_self_V_F4 hv)
    (c.exists_sq_F4 hV)
  rw [c.card_V_F4] at h
  omega

theorem V_le_rconj_F4 {W : Subgroup G} (hVW : V ≤ W) {g : G} (hg : g ∈ L) : V ≤ rconj W g := by
  intro v hv
  rw [mem_rconj]
  exact hVW ((Subgroup.mem_normalizer_iff.mp (c.L_le_normV_F4 hg) v).mp hv)

theorem exists_rep_F4 {Y : Subgroup G} (hVY : V ≤ Y) (hY : Nat.card Y ≤ 16) :
    ∃ y ∈ Y, ∀ w ∈ Y, w ∈ V ∨ y⁻¹ * w ∈ V := by
  by_cases hle : Y ≤ V
  · exact ⟨1, Y.one_mem, fun w hw => Or.inl (hle hw)⟩
  obtain ⟨y, hyY, hyV⟩ := Set.not_subset.mp hle
  refine ⟨y, hyY, fun w hw => ?_⟩
  by_cases hwV : w ∈ V
  · exact Or.inl hwV
  right
  have hidx : V.relIndex Y = 2 := by
    have h1 := Subgroup.relIndex_mul_card (H := V) (K := Y)
    rw [inf_eq_left.mpr hVY, c.card_V_F4] at h1
    have h2 : V.relIndex Y ≠ 1 := fun h => hle (by
      rw [Subgroup.relIndex_eq_one] at h
      exact h)
    have h3 : 0 < Nat.card Y := Nat.card_pos
    omega
  have hm := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨y⁻¹, Y.inv_mem hyY⟩)
    (b := ⟨w, hw⟩)).mpr (iff_of_false (fun hm => hyV (by
      have := V.inv_mem (Subgroup.mem_subgroupOf.mp hm)
      rwa [inv_inv] at this)) (fun hm => hwV (Subgroup.mem_subgroupOf.mp hm)))
  exact Subgroup.mem_subgroupOf.mp hm

theorem card_S_le_F4 (hyp : AlmostSpecialL3Hyp 1 V (fsuV1 T V) L T (l32nH T V)) {g' h' : G}
    (hg : g' ∈ L) (hh : h' ∈ L)
    (hV : V = fsuV1 T V ⊔ rconj (fsuV1 T V) g' ⊔ rconj (fsuV1 T V) h') :
    Nat.card ↥(pCoreOf 2 (fsuU T V ⊔ rconj (fsuU T V) g' ⊔ rconj (fsuU T V) h')) ≤ 64 := by
  set I := fsuU T V ⊔ rconj (fsuU T V) g' ⊔ rconj (fsuU T V) h' with hI
  set S := pCoreOf 2 I with hSdef
  set W := fsuU T V ⊓ S with hW
  obtain ⟨hSj, hSset⟩ := hyp.G25_three rfl hg hh hV hI hSdef hW
  obtain ⟨-, -, -, hVZ, -, -, -⟩ := hyp.G25_four rfl hg hh hV hI hSdef hW
  have hVS : V ≤ S := hVZ.trans inf_le_left
  have hcent : ∀ v ∈ V, ∀ s ∈ S, s * v = v * s := fun v hv s hs =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hVZ hv)).2 s hs

  have hWle : W ≤ V ⊔ centerOf (fsuU T V) := fun w hw =>
    c.mem_sup_of_comm_F4 hw.1 fun v hv => (hcent v hv w hw.2)
  have hW16 : Nat.card W ≤ 16 := (Subgroup.card_le_of_le hWle).trans c.card_sup_zU_F4.le
  have hVW : V ≤ W := le_inf c.ctx.V_U hVS
  have hcard_r : ∀ k : G, Nat.card ↥(rconj W k) = Nat.card W := fun k =>
    Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective
  obtain ⟨y₁, hy₁, hy₁W⟩ := c.exists_rep_F4 (c.V_le_rconj_F4 hVW hg) ((hcard_r g').trans_le hW16)
  obtain ⟨y₂, hy₂, hy₂W⟩ := c.exists_rep_F4 (c.V_le_rconj_F4 hVW hh) ((hcard_r h').trans_le hW16)
  have hWgS : rconj W g' ≤ S :=
    (le_sup_right.trans le_sup_left : rconj W g' ≤ W ⊔ rconj W g' ⊔ rconj W h').trans hSj.ge
  have hWhS : rconj W h' ≤ S :=
    (le_sup_right : rconj W h' ≤ W ⊔ rconj W g' ⊔ rconj W h').trans hSj.ge
  have hWS : W ≤ S := inf_le_right
  let f : ↥W × Bool × Bool → ↥S := fun p =>
    ⟨(p.1 : G) * (if p.2.1 then y₁ else 1) * (if p.2.2 then y₂ else 1),
      S.mul_mem (S.mul_mem (hWS p.1.2) (by split_ifs; exacts [hWgS hy₁, S.one_mem]))
        (by split_ifs; exacts [hWhS hy₂, S.one_mem])⟩
  have hf : Function.Surjective f := by
    rintro ⟨s, hs⟩
    have hs' : s ∈ ((W : Set G) * (rconj W g' : Set G)) * (rconj W h' : Set G) := by
      rw [← hSset]; exact hs
    obtain ⟨p, hp, q, hq, rfl⟩ := Set.mem_mul.mp hs'
    obtain ⟨w, hw, r, hr, rfl⟩ := Set.mem_mul.mp hp
    have hrep : ∀ (y : G) (Y : Subgroup G) (hY : Y ≤ S), y ∈ Y →
        (∀ t ∈ Y, t ∈ V ∨ y⁻¹ * t ∈ V) → ∀ t ∈ Y, ∃ (ε : Bool) (v : G), v ∈ V ∧
          t = (if ε then y else 1) * v := by
      intro y Y _ _ hyY t ht
      rcases hyY t ht with h | h
      · exact ⟨false, t, h, by simp⟩
      · exact ⟨true, y⁻¹ * t, h, by simp⟩
    obtain ⟨ε₁, v₁, hv₁, rfl⟩ := hrep y₁ _ hWgS hy₁ hy₁W r hr
    obtain ⟨ε₂, v₂, hv₂, rfl⟩ := hrep y₂ _ hWhS hy₂ hy₂W q hq
    have hy₂S : (if ε₂ then y₂ else 1) ∈ S := by split_ifs; exacts [hWhS hy₂, S.one_mem]
    refine ⟨(⟨w * v₁ * v₂, W.mul_mem (W.mul_mem hw (hVW hv₁)) (hVW hv₂)⟩, ε₁, ε₂), ?_⟩
    apply Subtype.ext
    show w * v₁ * v₂ * (if ε₁ then y₁ else 1) * (if ε₂ then y₂ else 1) =
      w * ((if ε₁ then y₁ else 1) * v₁) * ((if ε₂ then y₂ else 1) * v₂)
    have hy₁S : (if ε₁ then y₁ else 1) ∈ S := by split_ifs; exacts [hWgS hy₁, S.one_mem]
    have e1 := hcent v₁ hv₁ _ hy₁S
    have e2 := hcent v₂ hv₂ _ hy₂S
    have e3 := hcent v₁ hv₁ _ hy₂S
    calc w * v₁ * v₂ * (if ε₁ then y₁ else 1) * (if ε₂ then y₂ else 1)
        = w * v₁ * (v₂ * (if ε₁ then y₁ else 1)) * (if ε₂ then y₂ else 1) := by group
      _ = w * v₁ * ((if ε₁ then y₁ else 1) * v₂) * (if ε₂ then y₂ else 1) := by
          rw [hcent v₂ hv₂ _ hy₁S]
      _ = w * (v₁ * (if ε₁ then y₁ else 1)) * (v₂ * (if ε₂ then y₂ else 1)) := by group
      _ = w * ((if ε₁ then y₁ else 1) * v₁) * ((if ε₂ then y₂ else 1) * v₂) := by
          rw [← e1, ← e2]
  have h := Nat.card_le_card_of_surjective f hf
  rw [Nat.card_prod, Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]
    at h
  omega

theorem exists_gh_F4 : ∃ g' ∈ L, ∃ h' ∈ L,
    V = fsuV1 T V ⊔ rconj (fsuV1 T V) g' ⊔ rconj (fsuV1 T V) h' := by
  obtain ⟨_, S⟩ := c.setting
  have hzV₂ : z ∈ V₂ := c.ctx.plane.2 c.z_mem
  have hz := c.z_mem_V_F4
  have ha := c.a_mem_V_F4
  have hb := c.b_mem
  have hbV₂ := c.b_nmem
  have haV₁ := c.ctx.a1
  have haV₂ := c.ctx.aV₂
  have ha1 : a ≠ 1 := fun h => haV₁ (h ▸ one_mem _)
  have hb1 : b ≠ 1 := fun h => hbV₂ (h ▸ one_mem _)
  have hzb : z ≠ b := fun h => hbV₂ (h ▸ hzV₂)
  have hab : a ≠ b := fun h => hbV₂ (h ▸ haV₂)
  have hza : z ≠ a := fun h => haV₁ (h ▸ c.z_mem)
  have habz : a ≠ b * z := fun h => hbV₂ (by
    have : b = a * z⁻¹ := by rw [h]; group
    rw [this]
    exact mul_mem haV₂ (inv_mem hzV₂))
  have hbaz : b ≠ a * z := fun h => hbV₂ (h ▸ mul_mem haV₂ hzV₂)
  obtain ⟨l₁, hl₁, -, -, hl₁z, -⟩ := S.exists_rot_F4 hb hz ha c.z_ne ha1 hzb hab hza habz
  obtain ⟨l₂, hl₂, -, -, hl₂z, -⟩ := S.exists_rot_F4 ha hz hb c.z_ne hb1 hza hab.symm hzb hbaz
  have hrV : ∀ l ∈ L, rconj (fsuV1 T V) l ≤ V := fun l hl y hy => by
    rw [mem_rconj] at hy
    have h1 := (Subgroup.mem_normalizer_iff.mp (c.L_le_normV_F4 (L.inv_mem hl)) _).mp
      (Subgroup.mem_inf.mp hy).1
    simpa [mul_assoc] using h1
  have haJ : a ∈ rconj (fsuV1 T V) l₁⁻¹ := by
    rw [mem_rconj, inv_inv, ← hl₁z]
    simpa [mul_assoc] using c.z_mem
  have hbJ : b ∈ rconj (fsuV1 T V) l₂⁻¹ := by
    rw [mem_rconj, inv_inv, ← hl₂z]
    simpa [mul_assoc] using c.z_mem
  refine ⟨l₁⁻¹, L.inv_mem hl₁, l₂⁻¹, L.inv_mem hl₂, le_antisymm ?_ ?_⟩
  · set J := fsuV1 T V ⊔ rconj (fsuV1 T V) l₁⁻¹ ⊔ rconj (fsuV1 T V) l₂⁻¹
    have hV1J : fsuV1 T V ≤ J := le_sup_left.trans le_sup_left
    have haJ' : a ∈ J := (le_sup_right.trans le_sup_left : rconj (fsuV1 T V) l₁⁻¹ ≤ J) haJ
    have hbJ' : b ∈ J := (le_sup_right : rconj (fsuV1 T V) l₂⁻¹ ≤ J) hbJ
    have hV₂J : ∀ w ∈ V₂, w ∈ J := by
      intro w hw
      rcases c.ctx.V₂_cases w hw with hw1 | ⟨e, he, rfl⟩
      · exact hV1J hw1
      · exact J.mul_mem haJ' (hV1J he)
    intro v hv
    rcases S.mem_V_F4 hb hbV₂ hv with hv2 | hv2
    · exact hV₂J v hv2
    · have := J.mul_mem (J.inv_mem hbJ') (hV₂J _ hv2)
      simpa using this
  · exact sup_le (sup_le inf_le_left (hrV _ (L.inv_mem hl₁))) (hrV _ (L.inv_mem hl₂))

theorem commutator_V_L_F4 : ⁅V, L⁆ = V := by
  have hcc : conjClosure L T = L := le_antisymm
    (conjClosure_le fun _ ht l hl => (Subgroup.mem_normalizer_iff.1 (c.T_le_normL_F4 ht) l).1 hl)
    (le_conjClosure L T)
  have h := c.ctx.hyp.fsu.irrPlus.2.2.2.1
  rwa [hcc] at h

theorem U_le_normalizer_X_F4 :
    fsuU T V ≤ Subgroup.normalizer (conjClosure (centerOf (fsuU T V)) L : Set G) := by
  refine le_normalizer_of_conj_mem fun u hu w hw => ?_
  have hle : conjClosure (centerOf (fsuU T V)) L ≤
      (conjClosure (centerOf (fsuU T V)) L).comap (MulAut.conj u).toMonoidHom := by
    refine conjClosure_le fun l hl y hy => ?_
    show u * (l * y * l⁻¹) * u⁻¹ ∈ conjClosure (centerOf (fsuU T V)) L
    have hul : u * l * u⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (c.T_le_normL_F4 (c.U_le_T_F4 hu)) l).mp hl
    have huy : u * y * u⁻¹ ∈ centerOf (fsuU T V) :=
      (Subgroup.mem_normalizer_iff.mp (l32nH_le_normalizer_zU (c.ctx.U_le hu)) y).mp hy
    have e : u * (l * y * l⁻¹) * u⁻¹ = (u * l * u⁻¹) * (u * y * u⁻¹) * (u * l * u⁻¹)⁻¹ := by
      group
    rw [e]
    exact mem_conjClosure hul huy
  exact hle hw

theorem pCoreOf_eq_F4 (hyp : AlmostSpecialL3Hyp 1 V (fsuV1 T V) L T (l32nH T V)) :
    pCoreOf 2 L = conjClosure (centerOf (fsuU T V)) L ∧ Nat.card ↥(pCoreOf 2 L) = 64 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g', hg, h', hh, hV⟩ := c.exists_gh_F4
  obtain ⟨D'⟩ := hyp.natural.nonempty_data
  let St : L3Setting 1 V (fsuV1 T V) L T (l32nH T V) := ⟨hyp, D'⟩
  set X := conjClosure (centerOf (fsuU T V)) L with hX
  set I := fsuU T V ⊔ rconj (fsuU T V) g' ⊔ rconj (fsuU T V) h' with hI
  have hI' : I = L ⊔ fsuU T V := St.G25_two_aux hg hh hV
  have hLI : L ≤ I := hI' ▸ le_sup_left
  have hUI : fsuU T V ≤ I := hI' ▸ le_sup_right
  have hUL : fsuU T V ≤ Subgroup.normalizer (L : Set G) := c.U_le_T_F4.trans c.T_le_normL_F4
  have hIX : I ≤ Subgroup.normalizer (X : Set G) := by
    rw [hI']
    exact sup_le (le_normalizer_conjClosure _ L) c.U_le_normalizer_X_F4
  have hXI : X ≤ I := conjClosure_le fun l hl y hy =>
    I.mul_mem (I.mul_mem (hLI hl) (hUI (Subgroup.mem_inf.mp hy).1)) (I.inv_mem (hLI hl))
  have hXS : X ≤ pCoreOf 2 I := le_pCoreOf_of_le_normalizer 2 hXI hIX c.isPGroup_X_F4
  have hVe : V = conjClosure (fsuV1 T V) L := hyp.V_eq
  have hXS' : X = pCoreOf 2 I :=
    Subgroup.eq_of_le_of_card_ge hXS ((c.card_S_le_F4 hyp hg hh hV).trans (c.card_X_ge_F4 hVe))
  have hcardS : Nat.card ↥(pCoreOf 2 I) = 64 :=
    le_antisymm (c.card_S_le_F4 hyp hg hh hV) (hXS' ▸ c.card_X_ge_F4 hVe)
  set S := pCoreOf 2 I with hSdef
  have hSab : ∀ u ∈ S, ∀ w ∈ S, u * w = w * u := by
    rw [← hXS']
    exact c.X_comm_F4
  have hLS : L ≤ Subgroup.normalizer (S : Set G) := hLI.trans (le_normalizer_pCoreOf 2 I)
  have hSL : S ≤ Subgroup.normalizer (L : Set G) := by
    refine (pCoreOf_le 2 I).trans ?_
    rw [hI']
    exact sup_le Subgroup.le_normalizer hUL

  set C := ⁅S, L⁆ with hC
  have hCS : C ≤ S := Subgroup.le_normalizer_iff_commutator_le_left.mp hLS
  have hCL : C ≤ L := Subgroup.le_normalizer_iff_commutator_le_right.mp hSL
  have hVS : V ≤ S := hXS' ▸ c.V_le_X_F4 hVe
  have hVC : V ≤ C := by
    conv_lhs => rw [← c.commutator_V_L_F4]
    exact Subgroup.commutator_mono hVS le_rfl
  have hCab : ∀ u ∈ C, ∀ w ∈ C, u * w = w * u := fun u hu w hw => hSab u (hCS hu) w (hCS hw)
  have hsqC : ∀ v ∈ V, ∃ y ∈ C, y * y = v := by
    intro v hv
    rw [← c.commutator_V_L_F4] at hv
    induction hv using Subgroup.closure_induction with
    | mem v hv =>
      obtain ⟨v', hv', l, hl, rfl⟩ := hv
      obtain ⟨s, hs, rfl⟩ := c.exists_sq_F4 hVe v' hv'
      have hsS : s ∈ S := hXS' ▸ hs
      exact ⟨⁅s, l⁆, Subgroup.commutator_mem_commutator hsS hl, sq_commutator hSab hsS (hLS hl)⟩
    | one => exact ⟨1, C.one_mem, by group⟩
    | mul v w _ _ ihv ihw =>
      obtain ⟨y, hy, rfl⟩ := ihv
      obtain ⟨y', hy', rfl⟩ := ihw
      refine ⟨y * y', C.mul_mem hy hy', ?_⟩
      rw [mul_assoc, ← mul_assoc y', hCab y' hy' y hy]
      group
    | inv v _ ihv =>
      obtain ⟨y, hy, rfl⟩ := ihv
      exact ⟨y⁻¹, C.inv_mem hy, by group⟩
  have hCcard : 64 ≤ Nat.card C := by
    have h := card_mul_le_of_sq hCab hVC (fun v hv => c.mul_self_V_F4 hv) hsqC
    rw [c.card_V_F4] at h
    omega
  have hCeq : C = S := Subgroup.eq_of_le_of_card_ge hCS (hcardS ▸ hCcard)
  have hSL' : S ≤ L := hCeq ▸ hCL

  have hO : pCoreOf 2 L = S := by
    refine le_antisymm (le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans hLI) ?_
      (pCoreOf_isPGroup 2 L)) (le_pCoreOf_of_le_normalizer 2 hSL' hLS (pCoreOf_isPGroup 2 I))
    rw [hI']
    exact sup_le (le_normalizer_pCoreOf 2 L)
      (hUL.trans (normalizer_le_normalizer_pCoreOf 2 L))
  exact ⟨hO.trans hXS'.symm, hO ▸ hcardS⟩

end Ctx_F4

end L14333

end CFSG.Quasithin.H13
