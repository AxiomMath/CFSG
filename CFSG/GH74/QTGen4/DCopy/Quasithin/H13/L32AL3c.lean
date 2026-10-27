module

public import CFSG.Quasithin.H13.L32AL3c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AL2f

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Quasithin.H.Om4 Matrix CFSG.Quasithin.H13.L32A.C
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V K : Subgroup G} {t₀ : G}

theorem card_vHat_F4 [IsMulCommutative ↥(conjClosure V (A6.g1 T V))]
    (S : Setting147 G T L V (A6.g1 T V)) (hF : HypF98 T V L (fsuV1 T V) V (A6.g1 T V))
    (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) :
    Nat.card (vHat V (A6.g1 T V) (fsuV1 T V)) = 4 := by
  obtain ⟨-, hV8, -, hV12, -⟩ :=
    stmtL32NModule_of_inputs_F4 h1332 h1334 G T L V S.hyp.hyp S.hyp.fsu
  have hV₁V : fsuV1 T V ≤ V := hF.toHypF91.V₁_le_V
  have hker : (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure V (A6.g1 T V)))).ker =
      (fsuV1 T V).subgroupOf (conjClosure V (A6.g1 T V)) := by
    ext u
    rw [MonoidHom.mem_ker, A6.A6Mod.secMk_eq_one_iff, Subgroup.mem_subgroupOf]
  rw [vHat, ← Subgroup.relIndex_ker, hker, Subgroup.relIndex_subgroupOf (le_conjClosure V _)]
  have h1 := Subgroup.card_mul_index ((fsuV1 T V).subgroupOf V)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV₁V).toEquiv, hV12, hV8] at h1
  change ((fsuV1 T V).subgroupOf V).index = 4
  omega

theorem comm_mem_of_mem_R1_F4 (S : Setting147 G T L V (A6.g1 T V))
    (hF : HypF98 T V L (fsuV1 T V) V (A6.g1 T V)) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) (h13314 : A6.Stmt13_3_14_F4) {r : G}
    (hr : r ∈ pCoreOf 2 (l1 T L V ⊔ T)) {v : G} (hv : v ∈ V) :
    r * v * r⁻¹ * v⁻¹ ∈ fsuV1 T V := by
  have h4 := lemma14_7_4_four_F4 S hF h1222 h1332 h1334 h13314
  have hl1 : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  rw [hl1, sup_comm] at h4
  rw [← h4] at hr
  have hQT : pCoreOf 2 (L ⊔ T) ≤ T := pCoreOf_le_of_le S.hyp le_sup_right
  have hQN : pCoreOf 2 (L ⊔ T) ≤ Subgroup.normalizer (pCoreOf 2 (A6.g1 T V) : Set G) :=
    (hQT.trans (Setting147.TH' S)).trans (le_normalizer_pCoreOf 2 _)
  obtain ⟨n, hn, s, hs, rfl⟩ := exists_mul_of_mem_sup hQN hr
  have hsC : s ∈ Subgroup.centralizer (V : Set G) := by
    rw [CosetGeom.pCoreOf_eq_inf_centralizer hF.toHypF91.amalgamHypV] at hs
    exact hs.2
  have hsv : s * v * s⁻¹ = v := by
    rw [← Subgroup.mem_centralizer_iff.mp hsC v hv, mul_inv_cancel_right]
  rw [hF.toHypF91.pCoreOf_eq_centralizerMod] at hn
  have hnv := (mem_centralizerMod.mp hn).2.2 v (le_conjClosure V _ hv)
  have e : n * s * v * (n * s)⁻¹ * v⁻¹ = n * v * n⁻¹ * v⁻¹ := by
    calc n * s * v * (n * s)⁻¹ * v⁻¹ = n * (s * v * s⁻¹) * n⁻¹ * v⁻¹ := by group
      _ = n * v * n⁻¹ * v⁻¹ := by rw [hsv]
  rw [e]
  exact hnv

namespace TopCtx

variable {X : TopCtx T L V K (fsuV1 T V) t₀} [IsMulCommutative ↥(conjClosure V (A6.g1 T V))]

variable {F : Type} [Field F] (e : Hat V (A6.g1 T V) (fsuV1 T V) ≃* VM F)

theorem le_map_img_pCore_F4 (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (h76 : Lemma14_7_6_F4)
    (h33 : Lemma14_7_33_F4) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (h1222 : Stmt12_2_2_F4)
    (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) {N : Subgroup (MulAut (VM F))}
    (hNL : N ≤ (X.img (l1 T L V)).map (MulAut.congr e).toMonoidHom)
    (hLN : (X.img (l1 T L V)).map (MulAut.congr e).toMonoidHom ≤
      Subgroup.normalizer (N : Set (MulAut (VM F))))
    (hN2 : ∀ x ∈ N, ∃ k : ℕ, x ^ (2 ^ k) = 1) :
    N ≤ (X.img (pCoreOf 2 (l1 T L V))).map (MulAut.congr e).toMonoidHom := by
  have hL1H : l1 T L V ≤ A6.g1 T V := Setting147.l1H' X.R.S
  set ψ : ↥(A6.g1 T V) →* MulAut (VM F) := (MulAut.congr e).toMonoidHom.comp X.top.act with hψ
  let P : Subgroup G := (N.comap ψ).map (A6.g1 T V).subtype ⊓ l1 T L V
  have hmemP : ∀ g : ↥(A6.g1 T V), (g : G) ∈ P ↔ ψ g ∈ N ∧ (g : G) ∈ l1 T L V := by
    intro g
    constructor
    · rintro ⟨⟨g', hg', hgg'⟩, hgL⟩
      have : g' = g := Subtype.ext hgg'
      subst this
      exact ⟨hg', hgL⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨g, h1, rfl⟩, h2⟩
  have hPL : P ≤ l1 T L V := inf_le_right
  have hPn : (P.subgroupOf (l1 T L V)).Normal := by
    refine ⟨fun p hp l => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hp ⊢
    set p' : ↥(A6.g1 T V) := ⟨(p : G), hL1H p.2⟩
    set l' : ↥(A6.g1 T V) := ⟨(l : G), hL1H l.2⟩
    have hp' := (hmemP p').mp hp
    have hlN : ψ l' ∈ Subgroup.normalizer (N : Set (MulAut (VM F))) :=
      hLN ((mem_map_img_iff e).mpr ⟨l', l.2, rfl⟩)
    have hc : ψ (l' * p' * l'⁻¹) ∈ N := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hlN _).mp hp'.1
    have hcL : ((l' * p' * l'⁻¹ : ↥(A6.g1 T V)) : G) ∈ l1 T L V := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact (l1 T L V).mul_mem ((l1 T L V).mul_mem l.2 hp'.2) ((l1 T L V).inv_mem l.2)
    have := (hmemP (l' * p' * l'⁻¹)).mpr ⟨hc, hcL⟩
    simpa [p', l'] using this
  have hP2 : IsPGroup 2 P := by
    rintro ⟨p, hp⟩
    set p' : ↥(A6.g1 T V) := ⟨p, hL1H (hPL hp)⟩
    have hp' := (hmemP p').mp hp
    obtain ⟨k, hk⟩ := hN2 _ hp'.1
    rw [← map_pow] at hk
    have h1 : X.top.act (p' ^ (2 ^ k)) = 1 := (MulAut.congr e).injective (by
      rw [map_one]
      exact hk)
    rw [X.act_eq_one_iff_F4 hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334] at h1
    obtain ⟨m, hm⟩ := pCoreOf_isPGroup 2 (A6.g1 T V) ⟨_, h1⟩
    refine ⟨k + m, Subtype.ext ?_⟩
    have := congrArg Subtype.val hm
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at this ⊢
    rw [pow_add, pow_mul]
    simpa [p'] using this
  have hPO : P ≤ pCoreOf 2 (l1 T L V) := le_pCoreOf 2 hPL hPn hP2
  intro x hx
  obtain ⟨a, haL, rfl⟩ := (mem_map_img_iff e).mp (hNL hx)
  exact (mem_map_img_iff e).mpr ⟨a, hPO ((hmemP a).mpr ⟨hx, haL⟩), rfl⟩

end TopCtx

end CFSG.Quasithin.H13.L32A.L2
