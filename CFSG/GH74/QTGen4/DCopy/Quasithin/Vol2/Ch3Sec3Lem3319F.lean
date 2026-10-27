module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3319A
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3319D
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3319F

public section
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.L3319

open CFSG.Open (pCoreOf quasithinOmegaOneCenter)
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open CFSG.Quasithin.JonesParshall (wedgeRep wedgeMat)
open CFSG.Quasithin.H13.L3316 (liftPre liftCore liftCore_le)
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.QuasithinUnique.Vol2Native.L239.L52 (blkSLTwo blkSLTwo_coe)
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem false_of_extSq_F4
    {T M L D : Subgroup G} (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (h12 : Step3_3_12R_F4) (h14 : Stmt3_3_14_F4) (hGA : CFSG.Open.GriessAllModelsStatement)
    (h51 : AsB51) [IsMulCommutative ↥(vPlus L T)]
    (e : ↥(autOn L (vPlus L T)) ≃* SpecialLinearGroup (Fin 5) (ZMod 2))
    (hB : B51Hyp (ffJ (autOn (L ⊔ T) (vPlus L T))) (autOn L (vPlus L T)))
    (hext : SLExteriorTwo (autOn L (vPlus L T)) (commV (autOn L (vPlus L T))) ⊥ 5) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V := vPlus L T with hVdef
  obtain ⟨α, Φ, hD⟩ := exists_data_F4 h14 hGA h e hext
  have hTL := hD.TL
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hHV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := hred.2.2.2.1
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hHV
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := le_sup_right.trans hHV
  have hV2 : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hred.2.1.2 v v.2)
  have hcard : Nat.card ↥(autOn L V) = 9999360 := by
    rw [Nat.card_congr e.toEquiv, Ln2.card_specialLinear 5 (Or.inr rfl)]
    rfl
  have hG := ffJ_eq_of_b51 hV2 h51 hB hcard
  set P := flagStabilizer 5 (ZMod 2) {2} with hP
  set Z₀ := V ⊓ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) with hZ₀
  have hPre : L ⊓ Subgroup.centralizer (Z₀ : Set G) = liftPre α P := hD.inf_centralizer_eq
  set Y := liftCore α P with hYdef
  have hαk2 : IsPGroup 2 ↥α.ker := by
    rw [hD.ker]
    exact CFSG.pCore_isPGroup
  have hno : ∀ c ∈ ({2} : Set ℕ), ¬ (2 < c ∧ c < 2 + 3) := by
    intro c hc
    rw [Set.mem_singleton_iff] at hc
    omega
  obtain ⟨ψ, hψs, hψk, -⟩ := L3318.exists_levi (Nat.card_zmod 2) le_rfl hD.surj hαk2
    (I := {2}) (a := 2) (m := 3) (by norm_num) le_rfl (Or.inr rfl) (Or.inl rfl) hno
  have hψk' := Ln2.ker_eq_pCore_of_hom (Nat.card_zmod 2) le_rfl hψs hψk
  have hYL : Y ≤ L := liftCore_le α P
  have hY : ⁅Y, Y⁆ = Y := L3316.liftCore_perfect α P
  have hTH : T ≤ Subgroup.normalizer ((L ⊓ Subgroup.centralizer (Z₀ : Set G) : Subgroup G) :
      Set G) := by
    intro t ht
    have hTTL : t ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
      ChiefCount.mem_normalizer_inf (Subgroup.le_normalizer ht) (hTL ht)
    exact ChiefCount.mem_normalizer_inf (hTL ht)
      (normalizer_le_normalizer_centralizer _ (ChiefCount.mem_normalizer_inf (hTV ht)
        (normalizer_le_normalizer_centralizer _ hTTL)))
  have hTY : T ≤ Subgroup.normalizer (Y : Set G) := by
    rw [hYdef, L3316.liftCore, ← hPre]
    exact hTH.trans (normalizer_le_normalizer_perfectCore _)
  have hZZ₀ : quasithinOmegaOneCenter T ≤ Z₀ := by
    refine le_inf (le_conjClosure _ _) ?_
    exact (B2F.omegaOneCenter_le_inf_centralizer T).trans
      (inf_le_right.trans (Subgroup.centralizer_le inf_le_left))
  have hYZ : Y ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
    rw [hYdef, L3316.liftCore, ← hPre]
    exact (perfectCore_le _).trans (inf_le_right.trans (Subgroup.centralizer_le hZZ₀))
  refine false_of_offender_F4 h h38 h39 h12 hYL hY hTY hYZ hψs hψk' fun B hB hBK => ?_
  have hBJ : B ≤ ffJ (autOn (L ⊔ T) V) := B19.le_ffJ hB
  have hBL : B ≤ autOn L V := hG ▸ hBJ
  set W := commV (autOn L V) with hWdef
  have hW : W = commVPlus L T L := Ln2.commV_autOn_eq h
  have hcardW : Nat.card ↥W = 2 ^ 10 := by
    rw [hW, ← hD.range, ← Nat.card_congr (MonoidHom.ofInjective hD.inj).toEquiv]
    show Nat.card (Fin 10 → ZMod 2) = 2 ^ 10
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  have hoffW : 2 ^ 10 ≤ Nat.card ↥B * Nat.card ↥(fixV B ⊓ W) := by
    have h1 := Subgroup.relIndex_mul_card (fixV B) W
    have h2 := (relIndex_fixV_le_index B W).trans (index_fixV_le_card hB)
    rw [← hcardW, ← h1]
    exact Nat.mul_le_mul_right _ h2
  have hker : ∀ l : ↥L, α l = 1 ↔ conjOf V L hLV l = 1 := fun l => by
    rw [hD.ker_iff, conjOf_eq_one_iff]
  have hsame : ∀ l l' : ↥L, α l = α l' ↔ conjOf V L hLV l = conjOf V L hLV l' := fun l l' => by
    rw [← mul_inv_eq_one, ← map_inv, ← map_mul, hker, map_mul, map_inv, mul_inv_eq_one]
  have hpre : ∀ b ∈ B, ∃ l : ↥L, conjOf V L hLV l = b := fun b hb => by
    have : b ∈ (conjOf V L hLV).range := by
      rw [range_conjOf hLV]
      exact hBL hb
    exact this
  choose lof hlof using hpre
  set YB := (B.comap (conjOf V L hLV)).map α with hYB
  have hlofB : ∀ b (hb : b ∈ B), conjOf V L hLV (lof b hb) ∈ B := fun b hb => by
    rw [hlof]
    exact hb
  have hcardB : Nat.card ↥B ≤ Nat.card ↥YB := by
    refine Nat.card_le_card_of_injective
      (fun b : ↥B => (⟨α (lof b b.2), ⟨lof b b.2, hlofB b b.2, rfl⟩⟩ : ↥YB)) fun b b' hbb => ?_
    have h1 : α (lof b b.2) = α (lof b' b'.2) := congrArg Subtype.val hbb
    apply Subtype.ext
    rw [← hlof b b.2, ← hlof b' b'.2]
    exact (hsame _ _).mp h1
  have hΦW : ∀ w : ↥V, w ∈ W → ∃ x, Φ x = w := fun w hw => by
    rw [hW, ← hD.range] at hw
    exact hw
  choose xof hxof using hΦW
  have hcardF : Nat.card ↥(fixV B ⊓ W) ≤ Nat.card (B42Ln.FixW YB) := by
    refine Nat.card_le_card_of_injective (fun w => ⟨Multiplicative.toAdd (xof w w.2.2),
      fun u hu => ?_⟩) fun w w' hww => ?_
    · obtain ⟨l, hl, rfl⟩ := hu
      have hfix : conjOf V L hLV l (w : ↥V) = w := w.2.1 _ hl
      rw [← JonesParshall.Curtis.wedgeRep_apply']
      apply (hD.comm_iff l _).mp
      rw [hxof]
      have := congrArg Subtype.val hfix
      rw [conjOf_coe] at this
      exact this
    · have h1 : xof w w.2.2 = xof w' w'.2.2 :=
        Multiplicative.toAdd.injective (congrArg Subtype.val hww)
      apply Subtype.ext
      rw [← hxof w w.2.2, ← hxof w' w'.2.2, h1]
  have hYc : ∀ a ∈ YB, ∀ b ∈ YB, a * b = b * a := by
    rintro _ ⟨l, hl, rfl⟩ _ ⟨l', hl', rfl⟩
    rw [← map_mul, ← map_mul, hsame, map_mul, map_mul]
    exact hB.2.2.1.1 _ hl _ hl'
  have hY2 : ∀ a ∈ YB, a * a = 1 := by
    rintro _ ⟨l, hl, rfl⟩
    rw [← map_mul, hker, map_mul, ← pow_two]
    exact hB.2.2.1.2 _ hl
  have hYne : YB ≠ ⊥ := by
    intro hbot
    apply hB.2.1
    rw [eq_bot_iff]
    intro b hb
    rw [Subgroup.mem_bot]
    have : α (lof b hb) ∈ YB := ⟨lof b hb, hlofB b hb, rfl⟩
    rw [hbot, Subgroup.mem_bot, hker, hlof] at this
    exact this
  obtain ⟨-, heq⟩ := B42Ln.card_mul_fixW_le' hYc hY2
  obtain ⟨g, hg⟩ := heq ((hoffW.trans (Nat.mul_le_mul hcardB hcardF))) hYne
  set K := autOn (pCoreOf 2 (Y ⊔ T)) V with hKdef
  set Q := (K.comap (conjOf V L hLV)).map α with hQdef
  have hYBQ : YB ≤ Q := Subgroup.map_mono (Subgroup.comap_mono hBK)
  have hsylYT : IsSylowTwoOf T (Y ⊔ T) := ⟨le_sup_right, h.sylow.1, fun h2 =>
    h.sylow.2 (h2.trans (Subgroup.relIndex_dvd_index_of_le le_sup_right))⟩
  have hPT : pCoreOf 2 (Y ⊔ T) ≤ T := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hsylYT
  have hK2 : IsPGroup 2 ↥K :=
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (Y ⊔ T)).comap_of_injective _
      (Subgroup.normalizer (V : Set G)).subtype_injective).map _
  have hT2 : IsPGroup 2 ↥(autOn T V) :=
    (h.sylow.1.comap_of_injective _ (Subgroup.normalizer (V : Set G)).subtype_injective).map _
  have hS₀ : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal h.toSetup331.isSylowTwoOf le_sup_left
      (sup_le Subgroup.le_normalizer hTL)
  have hT₀ : IsSylowTwoOf (autOn (T ⊓ L) V) (autOn L V) := isSylowTwoOf_autOn hLV hS₀
  have heqT : autOn T V ⊓ autOn L V = autOn (T ⊓ L) V :=
    hT₀.eq_of_le (le_inf (autOn_le_autOn V inf_le_left) (autOn_le_autOn V inf_le_right))
      inf_le_right (hT2.to_le inf_le_left)
  have hQU : Q ≤ unitriangular 5 (ZMod 2) := by
    rintro _ ⟨l, hl, rfl⟩
    have hlK : conjOf V L hLV l ∈ K := hl
    have hlL : conjOf V L hLV l ∈ autOn L V := by
      rw [← range_conjOf hLV]
      exact ⟨l, rfl⟩
    have hlT₀ : conjOf V L hLV l ∈ autOn (T ⊓ L) V :=
      heqT ▸ ⟨autOn_le_autOn V hPT hlK, hlL⟩
    rw [← map_conjOf hLV inf_le_right] at hlT₀
    obtain ⟨t, ht, hte⟩ := hlT₀
    rw [← hD.mapU, (hsame l t).mpr hte.symm]
    exact ⟨t, ht, rfl⟩
  have hQ2 : IsPGroup 2 ↥Q := by
    rintro ⟨_, ⟨l, hl, rfl⟩⟩
    obtain ⟨a, ha⟩ := hK2 ⟨_, hl⟩
    refine ⟨a, Subtype.ext ?_⟩
    have h1 : conjOf V L hLV (l ^ 2 ^ a) = 1 := by
      rw [map_pow]
      simpa using congrArg Subtype.val ha
    have h2 := (hker _).mpr h1
    rw [map_pow] at h2
    simpa using h2
  have hYK : ∀ (y : G) (hy : y ∈ Y) (l : ↥L), conjOf V L hLV l ∈ K →
      conjOf V L hLV (⟨y, hYL hy⟩ * l * ⟨y, hYL hy⟩⁻¹) ∈ K := by
    intro y hy l hl
    have hyN : conjOf V L hLV ⟨y, hYL hy⟩ ∈ autOn (Y ⊔ T) V :=
      ⟨Subgroup.inclusion hLV ⟨y, hYL hy⟩, Subgroup.mem_subgroupOf.mpr (le_sup_left (a := Y) hy),
        rfl⟩
    have hKN := autOn_le_normalizer (V := V)
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y ⊔ T)) hyN
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hKN _).mp hl
  have hfwd : ∀ p ∈ perfectCore P, ∀ q ∈ Q, p * q * p⁻¹ ∈ Q := by
    intro p hp q hq
    obtain ⟨y, hy, rfl⟩ := L3318.exists_mem_liftCore hD.surj hp
    obtain ⟨l, hl, rfl⟩ := hq
    refine ⟨_, hYK y hy l hl, ?_⟩
    rw [map_mul, map_mul, map_inv]
  have hQN : perfectCore P ≤ Subgroup.normalizer
      (Q : Set (SpecialLinearGroup (Fin 5) (ZMod 2))) := by
    intro p hp
    rw [Subgroup.mem_normalizer_iff]
    intro q
    refine ⟨hfwd p hp q, fun hq => ?_⟩
    have := hfwd p⁻¹ ((perfectCore P).inv_mem hp) _ hq
    simpa [mul_assoc] using this
  have hblk : ∀ q ∈ Q, blkAt 2 3 (by norm_num) (q : Matrix (Fin 5) (Fin 5) (ZMod 2)) = 1 :=
    fun q hq => blkAt_eq_one (hQU.trans unitriangular_le_flagStabilizer) hQ2 hQN hq
  set gM : Matrix (Fin 5) (Fin 5) (ZMod 2) := (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) with hgM
  set gI : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
    ((g⁻¹ : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) with hgI
  obtain ⟨b₀, hb₀⟩ : ∃ b, gI 4 b ≠ 0 := by
    by_contra hall
    push Not at hall
    have h1 : (((g⁻¹ * g : SpecialLinearGroup (Fin 5) (ZMod 2))) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)) 4 4 = 1 := by
      rw [inv_mul_cancel]
      simp
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply] at h1
    simp [← hgI, hall] at h1
  have hcol : ∀ (i : Fin 4) (a : Fin 5), 2 ≤ (a : ℕ) → gM a i.castSucc = 0 := by
    intro i a ha
    have hi4 : i.castSucc ≠ (4 : Fin 5) := (Fin.castSucc_lt_last i).ne
    have hrY : g * B42Ln.eT i.castSucc 4 hi4 * g⁻¹ ∈ YB := by
      rw [hg]
      exact ⟨_, B42Ln.eT_mem_R4 i hi4, rfl⟩
    have hrQ := hYBQ hrY
    have hrU := hQU hrQ
    have hrb := hblk _ hrQ
    have hmat : ((g * B42Ln.eT i.castSucc 4 hi4 * g⁻¹ : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)) =
          1 + vecMulVec (gM *ᵥ Pi.single i.castSucc 1) (Pi.single 4 1 ᵥ* gI) := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, B42Ln.coe_eT,
        B42Ln.eTM_eq _ _ hi4, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, ← hgM, ← hgI]
      rw [show gM * gI = 1 by
        rw [hgM, hgI, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
          Matrix.SpecialLinearGroup.coe_one], Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
    have hentry : ((g * B42Ln.eT i.castSucc 4 hi4 * g⁻¹ : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)) a b₀ =
          (1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) a b₀ + gM a i.castSucc * gI 4 b₀ := by
      rw [hmat, Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.mulVec_single_one,
        Matrix.single_one_vecMul]
      rfl
    have hδ : ((g * B42Ln.eT i.castSucc 4 hi4 * g⁻¹ : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)) a b₀ = (1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) a b₀ := by
      by_cases hba : (b₀ : ℕ) < a
      · rw [hrU.1 a b₀ (Fin.lt_def.mpr hba), Matrix.one_apply_ne (fun h => by
          rw [h] at hba
          omega)]
      · have := congrFun (congrFun hrb ⟨(a : ℕ) - 2, by omega⟩) ⟨(b₀ : ℕ) - 2, by omega⟩
        rw [blkAt_apply] at this
        have e1 : (⟨2 + ((a : ℕ) - 2), by omega⟩ : Fin 5) = a := Fin.ext (by simp; omega)
        have e2 : (⟨2 + ((b₀ : ℕ) - 2), by omega⟩ : Fin 5) = b₀ := Fin.ext (by simp; omega)
        rw [e1, e2] at this
        rw [this, Matrix.one_apply, Matrix.one_apply]
        congr 1
        apply propext
        simp only [Fin.ext_iff]
        omega
    rw [hentry] at hδ
    have h0 : gM a i.castSucc * gI 4 b₀ = 0 :=
      add_left_cancel (hδ.trans (add_zero _).symm)
    rcases mul_eq_zero.mp h0 with h | h
    · exact h
    · exact absurd h hb₀
  have hdet : gM.det = 1 := g.2
  have hrow : ∀ a : Fin 5, 2 ≤ (a : ℕ) → ∀ j : Fin 5, j ≠ 4 → gM a j = 0 := by
    intro a ha j hj
    have hj4 : (j : ℕ) < 4 := by
      have := j.isLt
      have : (j : ℕ) ≠ 4 := fun h => hj (Fin.ext h)
      omega
    have := hcol ⟨j, hj4⟩ a ha
    rwa [show (⟨(j : ℕ), hj4⟩ : Fin 4).castSucc = j from Fin.ext rfl] at this
  rcases zmod2_cases (gM 2 4) (gM 3 4) with h2 | h3 | h23
  · rw [Matrix.det_eq_zero_of_row_eq_zero 2 fun j => by
      by_cases hj : j = 4
      · rw [hj]
        exact h2
      · exact hrow 2 (by decide) j hj] at hdet
    exact zero_ne_one hdet
  · rw [Matrix.det_eq_zero_of_row_eq_zero 3 fun j => by
      by_cases hj : j = 4
      · rw [hj]
        exact h3
      · exact hrow 3 (by decide) j hj] at hdet
    exact zero_ne_one hdet
  · rw [Matrix.det_zero_of_row_eq (i := 2) (j := 3) (by decide) (funext fun j => by
      by_cases hj : j = 4
      · rw [hj]
        exact h23
      · rw [hrow 2 (by decide) j hj, hrow 3 (by decide) j hj])] at hdet
    exact zero_ne_one hdet

end CFSG.Quasithin.H13.L3319
