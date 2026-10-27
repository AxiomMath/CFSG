module

public import CFSG.Quasithin.H13.L32AL2g
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AL2f

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Quasithin.H13.L32A.C
open scoped IsMulCommutative Pointwise

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V K W : Subgroup G} {t₀ : G}

namespace TopCtx

variable (X : TopCtx T L V K W t₀) [IsMulCommutative ↥(conjClosure V (A6.g1 T V))]

theorem fixV_img_K₀_F4 (hA37 : A37ForSQTK) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) : fixV (X.img (conjClosure K T)) = ⊥ := by
  set F := fixV (X.img (conjClosure K T)) with hF
  have hinv : ∀ h : ↥(A6.g1 T V), ∀ w ∈ F, X.top.act h w ∈ F := by
    intro h w hw y hy
    have hn := X.img_g1_le_normalizer ⟨h, Subgroup.mem_subgroupOf.mpr h.2, rfl⟩
    have hy' : (X.top.act h)⁻¹ * y * X.top.act h ∈ X.img (conjClosure K T) := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hn) y).mp hy
      simpa using this
    have := hw _ hy'
    simp only [MulAut.mul_apply] at this
    have h2 := congrArg (X.top.act h) this
    simpa using h2
  rcases X.top.irr F hinv with h | h
  · exact h
  · exfalso
    refine X.not_kb_le_ker_F4 hA37 h1222 h1332 h1334 fun a ha => ?_
    obtain ⟨κ, hκ, rfl⟩ := mem_modO2Image'.mp ha
    rw [MonoidHom.mem_ker, actDot_mk]
    apply MulEquiv.ext
    intro w
    have hw : w ∈ F := by rw [h]; exact Subgroup.mem_top w
    exact hw _ ⟨κ, Subgroup.mem_subgroupOf.mpr (le_conjClosure K T hκ), rfl⟩

theorem img_K_ne_bot_F4 (hA37 : A37ForSQTK) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) : X.img K ≠ ⊥ := by
  intro h
  refine X.not_kb_le_ker_F4 hA37 h1222 h1332 h1334 fun a ha => ?_
  obtain ⟨κ, hκ, rfl⟩ := mem_modO2Image'.mp ha
  rw [MonoidHom.mem_ker, actDot_mk]
  have : X.top.act κ ∈ X.img K := ⟨κ, Subgroup.mem_subgroupOf.mpr hκ, rfl⟩
  rw [h, Subgroup.mem_bot] at this
  exact this

theorem nonempty_equiv_img_K_F4 (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (h76 : Lemma14_7_6_F4)
    (h33 : Lemma14_7_33_F4) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (h1222 : Stmt12_2_2_F4)
    (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) :
    Nonempty (↥(X.img K) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨e₁⟩ := X.R.hA5
  obtain ⟨e₂⟩ := X.C.nonempty_equiv
  have hinj := X.actDot_injective_F4 hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334
  exact ⟨(MulEquiv.subgroupCongr (X.img_eq_map K)).trans
    ((Subgroup.equivMapOfInjective _ _ hinj).symm.trans (e₂.symm.trans e₁))⟩

theorem isQuasisimple_img_K_F4 (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (h76 : Lemma14_7_6_F4)
    (h33 : Lemma14_7_33_F4) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (h1222 : Stmt12_2_2_F4)
    (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) : CFSG.IsQuasisimple ↥(X.img K) := by
  obtain ⟨φ⟩ := X.nonempty_equiv_img_K_F4 hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334
  have hs : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have : IsSimpleGroup ↥(X.img K) := (MulEquiv.isSimpleGroup_congr φ).mpr hs
  obtain ⟨a, b, hab⟩ := alt5_noncomm
  refine (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup ⟨φ.symm a, φ.symm b, fun h => hab ?_⟩).1
  have := congrArg φ h
  simpa using this

theorem d31_F4 (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (h76 : Lemma14_7_6_F4)
    (h33 : Lemma14_7_33_F4) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (h1222 : Stmt12_2_2_F4)
    (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) {V' : Subgroup (Hat V (A6.g1 T V) W)}
    (hV' : V' ∈ IrrPlus (X.img (conjClosure K T)) ⊤) :
    D31 (X.img (A6.g1 T V)) (X.img (conjClosure K T)) (X.img T) (X.img K) V' := by
  have hTH : T ≤ A6.g1 T V := by rw [X.R.hG1]; exact le_sup_right
  have hKH : K ≤ A6.g1 T V := le_of_mem_cComp X.R.hK
  have hK₀H : conjClosure K T ≤ A6.g1 T V := by rw [X.R.hG1]; exact le_sup_left
  have hV'ne : V' ≠ ⊥ := (bot_le.trans_lt hV'.2.2.2.1).ne'
  refine ⟨fun w => by rw [pow_two]; exact X.top.sec_sq w, ?_, X.isSylowTwoOf_img_T,
    map_subgroupOf_mem_cComp X.top.act X.R.hK (X.img_K_ne_bot_F4 hA37 h1222 h1332 h1334),
    X.isQuasisimple_img_K_F4 hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334,
    map_subgroupOf_conjClosure X.top.act hKH hTH,
    map_le_normalizer_map_of_le_normalizer X.top.act hK₀H X.le_normalizer_K₀,
    ⟨le_top, hV'.2⟩, ?_, ?_⟩
  · rw [X.img_g1]
    exact isQuotientOfSQTK_range _ (sqtkGroup_of_setting X.top.S)
  · intro g hg v hv
    rw [X.img_K₀_sup_T, X.img_g1,
      X.pCoreOf_range_eq_bot_F4 hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334,
      Subgroup.mem_bot] at hg
    rw [hg]
    exact hv
  · set J := ⨆ m ∈ X.img (A6.g1 T V), V'.map (m : MulAut (Hat V (A6.g1 T V) W)).toMonoidHom
      with hJ
    have hinv : ∀ n ∈ X.img (A6.g1 T V), ∀ w ∈ J, n w ∈ J := by
      intro n hn w hw
      have hle : J.map n.toMonoidHom ≤ J := by
        rw [hJ, Subgroup.map_iSup]
        refine iSup_le fun m => ?_
        rw [Subgroup.map_iSup]
        refine iSup_le fun hm => ?_
        rw [Subgroup.map_map]
        exact le_iSup₂_of_le (n * m) (mul_mem hn hm) (le_of_eq rfl)
      exact hle ⟨w, hw, rfl⟩
    have hV'J : V' ≤ J := by
      have := le_iSup₂_of_le (f := fun (m : MulAut (Hat V (A6.g1 T V) W)) (_ : m ∈ X.img
        (A6.g1 T V)) => V'.map m.toMonoidHom) 1 (one_mem _) le_rfl
      intro v hv
      exact this ⟨v, hv, rfl⟩
    exact X.eq_top_of_inv (fun h => hV'ne (le_bot_iff.mp (h ▸ hV'J)))
      (fun m hm => hinv m (X.img_K₀_le hm)) (fun m hm => hinv m (X.img_T_le hm))

theorem exists_irrPlusOn_F4 (hA37 : A37ForSQTK) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) : ∃ V' : Subgroup (Hat V (A6.g1 T V) W),
      V' ∈ IrrPlusOn (X.img (conjClosure K T)) ⊤ (X.img T) := by
  have hV : ∀ w : Hat V (A6.g1 T V) W, w ^ 2 = 1 := fun w => by
    rw [pow_two]; exact X.top.sec_sq w
  obtain ⟨I₀, hI₀⟩ := exists_mem_irrPlus (X.fixV_img_K₀_F4 hA37 h1222 h1332 h1334) X.top.top_ne_bot
  have hTX : X.img T ≤ Subgroup.normalizer (X.img (conjClosure K T) :
      Set (MulAut (Hat V (A6.g1 T V) W))) := X.img_T_le.trans X.img_g1_le_normalizer
  obtain ⟨V', hV'⟩ := irrPlusOn_nonempty hV hTX X.isSylowTwoOf_img_T.2.1 hI₀
  have hsup : (⨆ y ∈ X.img T, y • I₀) = ⊤ := by
    have hne : I₀ ≠ ⊥ := (bot_le.trans_lt hI₀.2.2.2.1).ne'
    have h1 : (⨆ y ∈ X.img T, y • I₀) = orbSup (X.img T) I₀ := rfl
    rw [h1]
    exact X.orbSup_eq_top hne hI₀.2.1
  rw [hsup] at hV'
  exact ⟨V', hV'⟩

end TopCtx

end CFSG.Quasithin.H13.L32A.L2
