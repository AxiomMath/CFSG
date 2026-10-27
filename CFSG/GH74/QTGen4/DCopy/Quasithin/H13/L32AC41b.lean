module

public import CFSG.Quasithin.H13.L32AC41b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC32g
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC41a

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H : Subgroup G}

theorem isSolvable_szB1_l1T_F4 (hN1 : LieSylowOver3) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) (S : Setting147 G T L V H) {K : Subgroup G} (hK : K ∈ cComp H)
    (hq : CFSG.IsQuasisimple (cStar K)) (hKn : H ≤ Subgroup.normalizer (K : Set G)) {n : ℕ}
    (hn : 1 < n) (hLie : A315.IsLieChar2 n (cStar K ⧸ Subgroup.center (cStar K)))
    (hl1K : l1 T L V ≤ K) :
    Group.IsSolvable ↥(szB1 T H K ⊔ modO2Image H (l1 T L V ⊔ T)) := by
  have hN := l1T_le_normalizer_szS1_F4 hN1 h1222 h1332 h1334 S hK hq hKn hn hLie hl1K
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hBN : modO2Image H (l1 T L V ⊔ T) ≤
      Subgroup.normalizer (szB1 T H K : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    intro z hz
    have hzS := hN hz
    obtain ⟨w, -, rfl⟩ := mem_modO2Image'.mp hz
    exact mem_normalizer_szB1 hzS (mk_mem_normalizer hKH (hKn w.2))
  exact isSolvable_sup_of_le_normalizer' hBN (isSolvable_szB1_of S hK)
    (isSolvable_l1T_star_F4 h1222 h1332 h1334 S)

theorem mem_normalizer_L_of_solvable_F4 (h29 : Thm14_7_29_F4) (S : Setting147 G T L V H)
    {X : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)} (hX : Group.IsSolvable ↥X)
    (hLT : modO2Image H (l1 T L V ⊔ T) ≤ X) {β : ↥H}
    (hβ : QuotientGroup.mk' (CFSG.pCore 2 ↥H) β ∈ X) :
    (β : G) ∈ Subgroup.normalizer (L : Set G) := by
  have hLTH : l1 T L V ⊔ T ≤ H := sup_le (Setting147.l1H' S) (Setting147.TH' S)
  have hLTY : l1 T L V ⊔ T ≤ (X.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥H))).map H.subtype :=
    fun z hz => Subgroup.mem_map.mpr ⟨⟨z, hLTH hz⟩, hLT (mem_modO2Image'.mpr ⟨_, hz, rfl⟩), rfl⟩
  exact h29 G T L V S.hyp _ hLTY ((Subgroup.map_subtype_le _).trans S.hz.2.1)
    (isSolvable_preimage hX) (Subgroup.mem_map.mpr ⟨β, hβ, rfl⟩)

theorem mem_nX_of_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (S : Setting147 G T L V H)
    {β : G} (hβH : β ∈ H) (hβL : β ∈ Subgroup.normalizer (L : Set G)) :
    β ∈ L32NSet14.nX T V := by
  have hVc : conjClosure (fsuV1 T V) L = V :=
    (h1334 G T L V S.hyp.hyp.h13 (S.hyp.hyp1223_F4 (stmt13_3_2_two_of_F4 h1332)).irrPlus).2.1
  have hβ1 : β ∈ Subgroup.normalizer (fsuV1 T V : Set G) := S.hz.2.1 hβH
  refine ⟨?_, hβ1⟩
  rw [← hVc]
  exact SzN16.mem_normalizer_conjClosure hβL hβ1

section Comm

variable {V₂ : Subgroup G} [IsMulCommutative ↥V]

theorem pCoreOf_L_nX_le_T_F4 (h : Hyp147 G T L V) (S14 : L32NSet14.Setting_F4 G T L V V₂) :
    pCoreOf 2 (L ⊓ L32NSet14.nX T V) ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTN : T ≤ Subgroup.normalizer ((L ⊓ L32NSet14.nX T V : Subgroup G) : Set G) :=
    fun r hr => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨S14.TL_F4 hr, Subgroup.le_normalizer (S14.T_le_X_F4 hr)⟩
  have hN : (L ⊓ L32NSet14.nX T V) ⊔ T ≤
      Subgroup.normalizer (pCoreOf 2 (L ⊓ L32NSet14.nX T V) : Set G) :=
    sup_le (Subgroup.le_normalizer.trans (normalizer_le_normalizer_pCoreOf 2 _))
      (hTN.trans (normalizer_le_normalizer_pCoreOf 2 _))
  exact (le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans le_sup_left) hN
    (pCoreOf_isPGroup 2 _)).trans (L32A.pCoreOf_le_of_le h le_sup_right)

theorem comm_mem_T_F4 (h : Hyp147 G T L V) (S14 : L32NSet14.Setting_F4 G T L V V₂)
    {ψ : ↥(L32NSet14.nX T V) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)}
    (hψ : ∀ x, ψ x = 1 ↔ (x : G) ∈ L32NSet14.trivSub V (fsuV1 T V))
    {t : G} (htT : t ∈ T) (htL : t ∈ L) {β : G} (hβX : β ∈ L32NSet14.nX T V)
    (hβL : β ∈ Subgroup.normalizer (L : Set G)) {τ : G} (hτT : τ ∈ T)
    (hτ : ψ ⟨τ, S14.T_le_X_F4 hτT⟩ = ψ ⟨β, hβX⟩) :
    t * β * t⁻¹ * β⁻¹ ∈ T := by
  have hτX := S14.T_le_X_F4 hτT
  have htX := S14.T_le_X_F4 htT
  have hwX : τ⁻¹ * β ∈ L32NSet14.nX T V := mul_mem (inv_mem hτX) hβX
  have hwt : τ⁻¹ * β ∈ L32NSet14.trivSub V (fsuV1 T V) := by
    have e : (⟨τ⁻¹ * β, hwX⟩ : ↥(L32NSet14.nX T V)) = ⟨τ, hτX⟩⁻¹ * ⟨β, hβX⟩ := rfl
    refine (hψ ⟨τ⁻¹ * β, hwX⟩).mp ?_
    rw [e, map_mul, map_inv, hτ, inv_mul_cancel]
  have hwL : τ⁻¹ * β ∈ Subgroup.normalizer (L : Set G) := mul_mem (inv_mem (S14.TL_F4 hτT)) hβL
  set w := τ⁻¹ * β with hw
  have hcL : t * w * t⁻¹ * w⁻¹ ∈ L := by
    have h1 : w * t⁻¹ * w⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hwL _).mp (inv_mem htL)
    have e : t * w * t⁻¹ * w⁻¹ = t * (w * t⁻¹ * w⁻¹) := by group
    rw [e]
    exact mul_mem htL h1
  have hcX : t * w * t⁻¹ * w⁻¹ ∈ L32NSet14.nX T V :=
    mul_mem (mul_mem (mul_mem htX hwX) (inv_mem htX)) (inv_mem hwX)
  have hct : t * w * t⁻¹ * w⁻¹ ∈ L32NSet14.trivSub V (fsuV1 T V) :=
    mul_mem (L32NSet14.conj_mem_trivSub htX.1 htX.2 hwt) (inv_mem hwt)
  have hcT : t * w * t⁻¹ * w⁻¹ ∈ T :=
    pCoreOf_L_nX_le_T_F4 h S14 (S14.le_pCoreOf_F4 inf_le_right (inf_le_left.trans le_sup_left)
      ⟨⟨hcL, hcX⟩, hct⟩)
  have e : t * β * t⁻¹ * β⁻¹ = (t * τ * t⁻¹ * τ⁻¹) * (τ * (t * w * t⁻¹ * w⁻¹) * τ⁻¹) := by
    rw [hw]
    group
  rw [e]
  exact mul_mem (mul_mem (mul_mem (mul_mem htT hτT) (inv_mem htT)) (inv_mem hτT))
    (mul_mem (mul_mem hτT hcT) (inv_mem hτT))

end Comm

end CFSG.Quasithin.H13.L32A.C
