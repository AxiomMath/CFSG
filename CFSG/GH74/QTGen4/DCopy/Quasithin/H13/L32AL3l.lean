module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AL3k
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem143

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Quasithin.H.Om4 Matrix CFSG.Quasithin.H13.L32A.C
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V K : Subgroup G} {t₀ : G}

namespace TopCtx

variable (X : TopCtx T L V K (fsuV1 T V) t₀) [IsMulCommutative ↥(conjClosure V (A6.g1 T V))]
  {F : Type} [Field F] [Finite F] [CharP F 2] (e : Hat V (A6.g1 T V) (fsuV1 T V) ≃* VM F)
  {t : ↥(A6.g1 T V)} {z z' : G} {hz'U : z' ∈ conjClosure V (A6.g1 T V)}

theorem exists_three_centralizer_F4 (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (h76 : Lemma14_7_6_F4)
    (h33 : Lemma14_7_33_F4) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (h1222 : Stmt12_2_2_F4)
    (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (hF : HypF98 T V L (fsuV1 T V) V (A6.g1 T V))
    (hz : Subgroup.zpowers z = fsuV1 T V) (h : A114Hyp (fsuV1 T V ⊔ Subgroup.zpowers z') z z')
    (C : X.CfgAt e t hz'U) :
    ∃ x ∈ l1 T L V, orderOf x = 3 ∧
      x ∈ Subgroup.centralizer ((fsuV1 T V ⊔ Subgroup.zpowers z' : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hyL, hy3, hy1, hya⟩ := C.exists_three
  obtain ⟨l, hlL, rfl⟩ := (mem_map_img_iff e).mp hyL
  have hlN := (mem_normalizer_iff_fix (X := X) (e := e) hF hz h hz'U l).mpr hya
  have hact3 : X.top.act l ^ 3 = 1 :=
    (MulAut.congr e).injective (by rw [map_pow, hy3, map_one])
  have hact1 : X.top.act l ≠ 1 := fun h1 => hy1 (by rw [h1, map_one])
  have hord : orderOf (X.top.act l) = 3 := orderOf_eq_prime hact3 hact1
  have hl3 : ((l ^ 3 : ↥(A6.g1 T V)) : G) ∈ pCoreOf 2 (A6.g1 T V) :=
    (X.act_eq_one_iff_F4 hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334 _).mp
      (by rw [map_pow, hact3])
  obtain ⟨m, hm⟩ := pCoreOf_isPGroup 2 (A6.g1 T V) ⟨_, hl3⟩
  have hm' : ((l : G) ^ 3) ^ (2 ^ m) = 1 := by
    have := congrArg Subtype.val hm
    simpa using this
  set x := (l : G) ^ (2 ^ m) with hx
  have hx3 : x ^ 3 = 1 := by rw [hx, ← pow_mul, mul_comm, pow_mul, hm']
  have hx1 : x ≠ 1 := by
    intro hx1
    have h1 : X.top.act (l ^ (2 ^ m)) = 1 := by
      rw [X.act_eq_one_iff_F4 hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334]
      have : ((l ^ (2 ^ m) : ↥(A6.g1 T V)) : G) = 1 := by
        rw [SubgroupClass.coe_pow]
        exact hx1
      rw [this]
      exact Subgroup.one_mem _
    rw [map_pow] at h1
    have hdvd := orderOf_dvd_of_pow_eq_one h1
    rw [hord] at hdvd
    have h3 : (3 : ℕ) ∣ 2 := (Nat.prime_three.dvd_of_dvd_pow hdvd)
    omega
  have hxord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hxL : x ∈ l1 T L V := Subgroup.pow_mem _ hlL _
  have hxG : x ∈ A6.g1 T V := Subgroup.pow_mem _ l.2 _
  have hxN : x ∈ Subgroup.normalizer ((fsuV1 T V ⊔ Subgroup.zpowers z' : Subgroup G) :
      Set G) := Subgroup.pow_mem _ hlN _
  have hxz : x * z * x⁻¹ = z := by
    have hxC : x ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [centralizer_singleton_eq hF hz]
      exact hxG
    rw [Subgroup.mem_centralizer_singleton_iff.mp hxC, mul_inv_cancel_right]
  have hxz' : x * z' * x⁻¹ = z' := by
    have hz'V : x * z' * x⁻¹ ∈ fsuV1 T V ⊔ Subgroup.zpowers z' :=
      (Subgroup.mem_normalizer_iff.mp hxN z').mp h.mem₂
    rcases h.mem_V_cases hz'V with h0 | h0 | h0 | h0
    · exfalso
      apply h.ne_one₂
      calc z' = x⁻¹ * (x * z' * x⁻¹) * x := by group
        _ = 1 := by rw [h0]; group
    · exfalso
      apply h.ne
      calc z = x⁻¹ * (x * z * x⁻¹) * x := by group
        _ = x⁻¹ * (x * z' * x⁻¹) * x := by rw [hxz, h0]
        _ = z' := by group
    · exact h0
    · exfalso
      have e2 : x ^ 2 * z' * (x ^ 2)⁻¹ = z' := by
        calc x ^ 2 * z' * (x ^ 2)⁻¹ = x * (x * z' * x⁻¹) * x⁻¹ := by rw [pow_two]; group
          _ = x * (z * z') * x⁻¹ := by rw [h0]
          _ = (x * z * x⁻¹) * (x * z' * x⁻¹) := by group
          _ = z * (z * z') := by rw [hxz, h0]
          _ = z' := by rw [← mul_assoc, h.v₁_mul_self, one_mul]
      have e3 : x ^ 3 * z' * (x ^ 3)⁻¹ = z * z' := by
        calc x ^ 3 * z' * (x ^ 3)⁻¹ = x * (x ^ 2 * z' * (x ^ 2)⁻¹) * x⁻¹ := by
              rw [pow_three, pow_two]; group
          _ = z * z' := by rw [e2, h0]
      rw [hx3, one_mul, inv_one, mul_one] at e3
      apply h.ne_one₁
      calc z = z * z' * z'⁻¹ := by group
        _ = 1 := by rw [← e3, mul_inv_cancel]
  exact ⟨x, hxL, hxord, h.mem_centralizer_of_fixes hxz hxz'⟩

theorem V_le_closure_F4 (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (h76 : Lemma14_7_6_F4)
    (h33 : Lemma14_7_33_F4) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (h1222 : Stmt12_2_2_F4)
    (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (C : X.CfgAt e t hz'U) :
    V ≤ Subgroup.closure {w | ∃ l ∈ pCoreOf 2 (l1 T L V), w = l * z' * l⁻¹} ⊔ fsuV1 T V := by
  have hS0O := X.sZero_le_img_F4 e hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334 C
  have hL1H : l1 T L V ≤ A6.g1 T V := Setting147.l1H' X.R.S
  set W := Subgroup.closure {w | ∃ l ∈ pCoreOf 2 (l1 T L V), w = l * z' * l⁻¹} ⊔ fsuV1 T V
    with hW
  have hconjU : ∀ l ∈ pCoreOf 2 (l1 T L V), l * z' * l⁻¹ ∈ conjClosure V (A6.g1 T V) :=
    fun l hl => (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V (A6.g1 T V)
      (hL1H (pCoreOf_le 2 _ hl))) z').mp hz'U
  have hWU : W ≤ conjClosure V (A6.g1 T V) := by
    refine sup_le ?_ (X.top.hF.toHypF91.V₁_le_V.trans (le_conjClosure V _))
    rw [Subgroup.closure_le]
    rintro _ ⟨l, hl, rfl⟩
    exact hconjU l hl
  have h3 : Subgroup.closure {w | ∃ s ∈ sZero, w = s (e (InternalSec.secMk
      ((fsuV1 T V).subgroupOf (conjClosure V (A6.g1 T V))) ⟨z', hz'U⟩))} ≤
      ((W.subgroupOf (conjClosure V (A6.g1 T V))).map (InternalSec.secMk
        ((fsuV1 T V).subgroupOf (conjClosure V (A6.g1 T V))))).map e.toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨l, hlO, rfl⟩ := (mem_map_img_iff e).mp (hS0O hs)
    refine ⟨_, ⟨⟨(l : G) * z' * (l : G)⁻¹, hconjU l hlO⟩, Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_sup_left (Subgroup.subset_closure ⟨l, hlO, rfl⟩)), rfl⟩, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, congr_apply_e, X.top.act_mk]
  intro v hv
  have hvU : v ∈ conjClosure V (A6.g1 T V) := le_conjClosure V _ hv
  have h1 : e (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure V (A6.g1 T V)))
      ⟨v, hvU⟩) ∈ (vHat V (A6.g1 T V) (fsuV1 T V)).map e.toMonoidHom :=
    ⟨_, ⟨⟨v, hvU⟩, Subgroup.mem_subgroupOf.mpr hv, rfl⟩, rfl⟩
  obtain ⟨_, ⟨w, hw, rfl⟩, hwe⟩ := h3 (C.vs_le h1)
  rw [MulEquiv.coe_toMonoidHom] at hwe
  have hqw := e.injective hwe
  have h4 : InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure V (A6.g1 T V)))
      (w⁻¹ * ⟨v, hvU⟩) = 1 := by
    rw [map_mul, map_inv, hqw, inv_mul_cancel]
  rw [A6.A6Mod.secMk_eq_one_iff] at h4
  have e5 : v = (w : G) * ((w⁻¹ * ⟨v, hvU⟩ : ↥(conjClosure V (A6.g1 T V))) : G) := by
    simp
  rw [e5]
  exact W.mul_mem (Subgroup.mem_subgroupOf.mp hw) (Subgroup.mem_sup_right h4)

theorem inf_le_TY_F4 (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (h76 : Lemma14_7_6_F4)
    (h33 : Lemma14_7_33_F4) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (h1222 : Stmt12_2_2_F4)
    (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (C : X.CfgAt e t hz'U) :
    T ⊓ Subgroup.centralizer (V : Set G) ⊓
        Subgroup.centralizer ((fsuV1 T V ⊔ Subgroup.zpowers z' : Subgroup G) : Set G) ≤
      pCoreOf 2 (l1 T L V ⊔ T) ⊓
        Subgroup.normalizer ((fsuV1 T V ⊔ Subgroup.zpowers z' : Subgroup G) : Set G) := by
  intro x hx
  obtain ⟨hx1, hxY⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨hxT, hxV⟩ := Subgroup.mem_inf.mp hx1
  have hTH : T ≤ A6.g1 T V := Setting147.TH' X.R.S
  set x' : ↥(A6.g1 T V) := ⟨x, hTH hxT⟩
  have hfix : ∀ v ∈ (vHat V (A6.g1 T V) (fsuV1 T V)).map e.toMonoidHom,
      MulAut.congr e (X.top.act x') v = v := by
    rintro _ ⟨w, hw, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, congr_apply_e, X.act_fix_vHat (fun v hv => ?_) hw]
    have hc : x * v = v * x := (Subgroup.mem_centralizer_iff.mp hxV v hv).symm
    have e1 : (x' : G) * v * (x' : G)⁻¹ * v⁻¹ = 1 := by
      show x * v * x⁻¹ * v⁻¹ = 1
      rw [hc]
      group
    rw [e1]
    exact Subgroup.one_mem _
  have hR := C.mem_rs_of_fix ((mem_map_img_iff e).mpr ⟨x', hxT, rfl⟩) hfix
  exact ⟨X.mem_R1_of_img_F4 e hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334 (x := x') hR,
    Subgroup.centralizer_le_normalizer _ hxY⟩

theorem centralizer_V2_le_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (C : X.CfgAt e t hz'U)
    {V₂ : Subgroup G} (hV2 : A6.IsV2 T V V₂) :
    Subgroup.centralizer (V₂ : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have S := X.R.S
  obtain ⟨-, -, -, hV12, -⟩ :=
    stmtL32NModule_of_inputs_F4 h1332 h1334 G T L V S.hyp.hyp S.hyp.fsu
  obtain ⟨v₂, hv₂, hv₂V₁⟩ : ∃ v ∈ V₂, v ∉ fsuV1 T V := by
    by_contra hall
    push Not at hall
    have := Subgroup.card_le_of_le (show V₂ ≤ fsuV1 T V from hall)
    rw [hV2.2.2.2, hV12] at this
    omega
  have hv₂V : v₂ ∈ V := hV2.2.1 hv₂
  have hv₂U : v₂ ∈ conjClosure V (A6.g1 T V) := le_conjClosure V _ hv₂V
  have key : ∀ y : ↥(A6.g1 T V), (y : G) ∈ Subgroup.centralizer (V₂ : Set G) →
      ∀ w ∈ vHat V (A6.g1 T V) (fsuV1 T V), X.top.act y w ∈ vHat V (A6.g1 T V) (fsuV1 T V) := by
    intro y hy w hw
    have hyv : (y : G) * v₂ * (y : G)⁻¹ = v₂ := by
      rw [← Subgroup.mem_centralizer_iff.mp hy v₂ hv₂, mul_inv_cancel_right]
    have hyfix : MulAut.congr e (X.top.act y) (e (InternalSec.secMk
        ((fsuV1 T V).subgroupOf (conjClosure V (A6.g1 T V))) ⟨v₂, hv₂U⟩)) =
        e (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure V (A6.g1 T V)))
          ⟨v₂, hv₂U⟩) := by
      rw [congr_apply_e, X.top.act_mk]
      congr 2
      exact Subtype.ext hyv
    have hv₀ : e (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure V (A6.g1 T V)))
        ⟨v₂, hv₂U⟩) ∈ (vHat V (A6.g1 T V) (fsuV1 T V)).map e.toMonoidHom :=
      ⟨_, ⟨⟨v₂, hv₂U⟩, Subgroup.mem_subgroupOf.mpr hv₂V, rfl⟩, rfl⟩
    have hv₀1 : e (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure V (A6.g1 T V)))
        ⟨v₂, hv₂U⟩) ≠ 1 := by
      intro h1
      rw [MulEquiv.map_eq_one_iff, A6.A6Mod.secMk_eq_one_iff] at h1
      exact hv₂V₁ h1
    have hyH : MulAut.congr e (X.top.act y) ∈
        (X.img (A6.g1 T V)).map (MulAut.congr e).toMonoidHom :=
      (mem_map_img_iff e).mpr ⟨y, y.2, rfl⟩
    have h2 := C.stab_of_fix hyH hv₀ hv₀1 hyfix (v := e w) ⟨w, hw, rfl⟩
    rw [congr_apply_e] at h2
    obtain ⟨w', hw', hw'e⟩ := h2
    rw [MulEquiv.coe_toMonoidHom] at hw'e
    rw [← e.injective hw'e]
    exact hw'
  intro x hx
  have hxG : x ∈ A6.g1 T V := Subgroup.centralizer_le_normalizer _
    (Subgroup.centralizer_le hV2.1 hx)
  have hxN := (X.top.mem_normalizer_iff ⟨x, hxG⟩).mpr fun w hw =>
    ⟨key _ hx w hw, key _ (Subgroup.inv_mem _ hx) w hw⟩
  rw [sup_eq_left.mpr X.top.hF.toHypF91.V₁_le_V,
    lemma1433Five_of_inputs_F4 h1332 h1334 G T L V S.hyp.hyp S.hyp.fsu] at hxN
  exact hxN.1

end TopCtx

end CFSG.Quasithin.H13.L32A.L2
