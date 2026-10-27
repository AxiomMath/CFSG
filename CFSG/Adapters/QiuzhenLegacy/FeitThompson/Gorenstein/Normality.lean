module

public import CFSG.Adapters.QiuzhenLegacy.FeitThompson.Gorenstein.Replacement
public import CFSG.GroupTheory.ABGLocalTools.Constraint
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Residual
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem4_1

public section

namespace CFSG.ABGTheoremB.RelativeZJ

open CFSG CFSG.ABGLocalTools
open scoped Pointwise commutatorElement

section

variable {G : Type*} [Group G]

section ConstraintAndStability

variable {p : ℕ} [Fact p.Prime]

variable [Finite G]

theorem inf_thompsonCenter_normal
    (hpodd : p ≠ 2) (U : Subgroup G) (hU : IsPGroup p U) (hBU : pCore p G ≤ U)
    (hstable : ∀ B' A : Subgroup G, B'.Normal → IsPGroup p B' → B' ≠ ⊥ → A ≤ U →
      ⁅⁅B', A⁆, A⁆ = ⊥ → A ≤ normalizerPCoreModCentralizer p B')
    (Ostar : Subgroup G) (hOn : Ostar.Normal)
    (hOZ : Ostar ≤ Subgroup.normalizer (thompsonCenter (G := G) U : Set G))
    (h3 : ∀ (L : Subgroup G) [L.Normal], Ostar ≤ L →
      (IsSylowOf p (U ⊓ L) L ∧ pCore p (G ⧸ L) ≤ U.map (QuotientGroup.mk' L)) ∨
        L ⊔ Subgroup.normalizer (thompsonCenter (G := G) U : Set G) = ⊤)
    (B : Subgroup G) [B.Normal] (hBp : IsPGroup p B) (hBne : B ≠ ⊥) :
    (B ⊓ thompsonCenter (G := G) U).Normal := by
  classical
  let Z : Subgroup G := thompsonCenter (G := G) U
  have hmain :
      ∀ n : ℕ, ∀ (B : Subgroup G), B.Normal → IsPGroup p B → B ≠ ⊥ →
        Nat.card B = n → (B ⊓ Z).Normal := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro B hBnormal hBp hBne hcardB
        let B0 : Subgroup G := B ⊓ Z
        let B1 : Subgroup G := Subgroup.normalClosure (B0 : Set G)
        by_cases hB0_bot : B0 = ⊥
        · simp [B0, hB0_bot]
        have hB0ne : B0 ≠ ⊥ := hB0_bot
        by_cases hB0_normal : B0.Normal
        · simpa [B0] using hB0_normal
        have hB0_not_normal : ¬ B0.Normal := hB0_normal
        have hB1_eq_B : B1 = B := by
          have hB1_le_B : B1 ≤ B := by
            let : B.Normal := hBnormal
            simpa [B0, B1] using
              (Subgroup.normalClosure_le_normal (N := B) (by
                intro x hx
                exact hx.1))
          have hB0_le_B1 : B0 ≤ B1 := by
            simpa [B1] using (Subgroup.le_normalClosure (H := B0))
          by_contra hB1_ne
          have hB1_lt_B : B1 < B := lt_of_le_of_ne hB1_le_B hB1_ne
          have hB1ne : B1 ≠ ⊥ := by
            intro hB1_bot
            apply hB0ne
            exact le_antisymm (hB1_bot ▸ hB0_le_B1) bot_le
          have hB1p : IsPGroup p B1 := by
            let B1sub : Subgroup B := B1.subgroupOf B
            have hB1sub_p : IsPGroup p B1sub := hBp.to_subgroup B1sub
            exact hB1sub_p.of_equiv (Subgroup.subgroupOfEquivOfLe hB1_le_B)
          have hB1_card_lt : Nat.card B1 < Nat.card B := natCard_lt_of_subgroup_lt hB1_lt_B
          have hB1_card_lt_n : Nat.card B1 < n := by
            simpa [hcardB] using hB1_card_lt
          have hB1_inf_normal : (B1 ⊓ Z).Normal := by
            exact ih (Nat.card B1) hB1_card_lt_n B1 (by
              dsimp [B1]
              infer_instance) hB1p hB1ne rfl
          have hB0_le_B1_inf : B0 ≤ B1 ⊓ Z := by
            intro x hx
            exact ⟨hB0_le_B1 hx, hx.2⟩
          have hB1_le_Z : B1 ≤ Z := by
            have hB1_le_inf : B1 ≤ B1 ⊓ Z := by
              let : (B1 ⊓ Z).Normal := hB1_inf_normal
              simpa [B1] using
                (Subgroup.normalClosure_le_normal (N := B1 ⊓ Z) hB0_le_B1_inf)
            exact fun x hx => (hB1_le_inf hx).2
          have hB0_eq_B1 : B0 = B1 := by
            apply le_antisymm hB0_le_B1
            intro x hx
            exact ⟨hB1_le_B hx, hB1_le_Z hx⟩
          have hB1_normal : B1.Normal := by
            dsimp [B1]
            infer_instance
          exact hB0_not_normal <| by
            simpa [hB0_eq_B1] using hB1_normal
        have hB_le_P : B ≤ U :=
          (le_sSup (show B ∈ {K : Subgroup G | K.Normal ∧ IsPGroup p K} from
            ⟨hBnormal, hBp⟩) : B ≤ pCore p G).trans hBU
        have hP_le_norm_Z : U ≤ Subgroup.normalizer (Z : Set G) := by
          exact
            Subgroup.le_normalizer.trans
              (rzj_normalizer_le_normalizer_thompsonCenter (G := G) U)
        let Bcomm : Subgroup G := ⁅B, B⁆
        have hBcomm_le_B : Bcomm ≤ B := by
          dsimp [Bcomm]
          exact Subgroup.commutator_le_left B B
        have hBcomm_p : IsPGroup p Bcomm := by
          let Bcomm_sub : Subgroup B := Bcomm.subgroupOf B
          have hBcomm_sub_p : IsPGroup p Bcomm_sub := hBp.to_subgroup Bcomm_sub
          exact hBcomm_sub_p.of_equiv (Subgroup.subgroupOfEquivOfLe hBcomm_le_B)
        have hBcomm_inf_normal : (Bcomm ⊓ Z).Normal := by
          by_cases hBcomm_bot : Bcomm = ⊥
          · simp [hBcomm_bot]
          · have : Nontrivial Bcomm :=
              (Subgroup.nontrivial_iff_ne_bot (H := Bcomm)).2 hBcomm_bot
            have : Nontrivial B :=
              (Subgroup.nontrivial_iff_ne_bot (H := B)).2 hBne
            have : Group.IsNilpotent B := hBp.isNilpotent
            have : Group.IsSolvable B := IsNilpotent.to_isSolvable
            have hBcomm_lt_B : Bcomm < B := by
              dsimp [Bcomm]
              simpa using (commutator_lt_self_of_isSolvable (G := G) B)
            have hBcomm_card_lt_n : Nat.card Bcomm < n := by
              have hBcomm_card_lt : Nat.card Bcomm < Nat.card B :=
                natCard_lt_of_subgroup_lt hBcomm_lt_B
              simpa [hcardB] using hBcomm_card_lt
            exact
              ih (Nat.card Bcomm) hBcomm_card_lt_n Bcomm
                (by
                  dsimp [Bcomm]
                  infer_instance)
                hBcomm_p hBcomm_bot rfl
        let N : Subgroup G := Bcomm ⊓ Z
        have hN_normal : N.Normal := by
          simpa [N] using hBcomm_inf_normal
        let qN : G →* G ⧸ N := QuotientGroup.mk' N
        let BbarN : Subgroup (G ⧸ N) := B.map qN
        have hBbarN_normal : BbarN.Normal := by
          dsimp [BbarN, qN]
          exact
            Subgroup.Normal.map (H := B) hBnormal
              (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
        let CbarN : Subgroup (G ⧸ N) := Subgroup.centralizer (BbarN : Set (G ⧸ N))
        have hCbarN_normal : CbarN.Normal := by
          apply (Subgroup.normalizer_eq_top_iff).mp
          apply top_le_iff.mp
          calc
            (⊤ : Subgroup (G ⧸ N)) = Subgroup.normalizer (BbarN : Set (G ⧸ N)) := by
              symm
              exact Subgroup.normalizer_eq_top (H := BbarN)
            _ ≤ Subgroup.normalizer (CbarN : Set (G ⧸ N)) := by
              dsimp [CbarN]
              exact CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer (X := G ⧸ N) BbarN
        let CN : Subgroup G := Subgroup.comap qN CbarN
        have hCN_normal : CN.Normal := by
          dsimp [CN]
          infer_instance
        have hB0_le_CN : B0 ≤ CN := by
          intro z hz
          show qN z ∈ CbarN
          rw [Subgroup.mem_centralizer_iff_commutator_eq_one]
          intro y hy
          rcases Subgroup.mem_map.mp hy with ⟨b, hb, rfl⟩
          apply (QuotientGroup.eq_one_iff (N := N) (x := ⁅b, z⁆)).2
          refine ⟨?_, ?_⟩
          · dsimp [Bcomm]
            exact Subgroup.commutator_mem_commutator hb hz.1
          · have hb_normZ : b ∈ Subgroup.normalizer (Z : Set G) := hP_le_norm_Z (hB_le_P hb)
            have hb_conj_z : b * z * b⁻¹ ∈ Z := by
              exact
                ((Subgroup.mem_normalizer_iff.mp hb_normZ) z).1 hz.2
            rw [commutatorElement_def]
            simpa [mul_assoc] using Z.mul_mem hb_conj_z (Z.inv_mem hz.2)
        have hB_le_CN : B ≤ CN := by
          rw [← hB1_eq_B]
          dsimp [B1]
          let : CN.Normal := hCN_normal
          exact Subgroup.normalClosure_le_normal (N := CN) hB0_le_CN
        have hBbarN_cent : BbarN ≤ Subgroup.centralizer (BbarN : Set (G ⧸ N)) := by
          intro x hx
          rcases Subgroup.mem_map.mp hx with ⟨b, hb, rfl⟩
          exact hB_le_CN hb
        have hBcomm_map_qN_bot : Bcomm.map qN = ⊥ := by
          calc
            Bcomm.map qN = ⁅BbarN, BbarN⁆ := by
              dsimp [Bcomm, BbarN, qN]
              rw [Subgroup.map_commutator]
            _ = ⊥ := by
              exact (Subgroup.commutator_eq_bot_iff_le_centralizer).2 hBbarN_cent
        have hBcomm_le_N : Bcomm ≤ N := by
          simpa [N, qN, QuotientGroup.ker_mk'] using
            (Subgroup.map_eq_bot_iff (f := qN) (H := Bcomm)).1 hBcomm_map_qN_bot
        have hBcomm_le_Z : Bcomm ≤ Z := by
          intro x hx
          exact (hBcomm_le_N hx).2
        have hB_le_cent_Bcomm : B ≤ Subgroup.centralizer (Bcomm : Set G) := by
          let : IsMulCommutative Z := rzj_thompsonCenter_isMulCommutative (G := G) U
          let C : Subgroup G := Subgroup.centralizer (Bcomm : Set G)
          have hC_normal : C.Normal := by
            apply (Subgroup.normalizer_eq_top_iff).mp
            apply top_le_iff.mp
            calc
              (⊤ : Subgroup G) = Subgroup.normalizer (Bcomm : Set G) := by
                symm
                exact Subgroup.normalizer_eq_top (H := Bcomm)
              _ ≤ Subgroup.normalizer (C : Set G) := by
                dsimp [C]
                exact CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer (X := G) Bcomm
          have hB0_le_C : B0 ≤ C := by
            intro z hz
            rw [Subgroup.mem_centralizer_iff]
            intro c hc
            exact
              setLike_mul_comm
                (s := Z) (hBcomm_le_Z hc) hz.2
          rw [← hB1_eq_B]
          dsimp [B1]
          let : C.Normal := hC_normal
          exact Subgroup.normalClosure_le_normal (N := C) hB0_le_C
        have hBcomm_le_cent_B : Bcomm ≤ Subgroup.centralizer (B : Set G) := by
          exact
            (Subgroup.commutator_eq_bot_iff_le_centralizer).1 <| by
              rw [Subgroup.commutator_comm]
              exact (Subgroup.commutator_eq_bot_iff_le_centralizer).2 hB_le_cent_Bcomm
        let L : Subgroup G := (Subgroup.normalizer (B0 : Set G)).normalCore
        let qL : G →* G ⧸ L := QuotientGroup.mk' L
        have hL_normal' : L.Normal := by
          dsimp [L]
          infer_instance
        have hO_le_L : Ostar ≤ L := by
          have hO_le_norm_B0 : Ostar ≤ Subgroup.normalizer (B0 : Set G) := by
            intro x hx
            have hxB : x ∈ Subgroup.normalizer (B : Set G) := by
              rw [Subgroup.normalizer_eq_top (H := B)]
              exact Subgroup.mem_top x
            simpa [B0] using
              (Subgroup.inf_normalizer_le_normalizer_inf (H := B) (K := Z) ⟨hxB, hOZ hx⟩)
          have : Ostar.Normal := hOn
          simpa [L] using
            (Subgroup.normal_le_normalCore
              (H := Subgroup.normalizer (B0 : Set G)) (N := Ostar)).2 hO_le_norm_B0
        obtain ⟨hsyl, hcov⟩ :
            IsSylowOf p (U ⊓ L) L ∧ pCore p (G ⧸ L) ≤ U.map qL := by
          rcases h3 L hO_le_L with h | h
          · exact h
          · exfalso
            apply hB0_not_normal
            apply (Subgroup.normalizer_eq_top_iff).mp
            apply top_le_iff.mp
            rw [← h]
            refine sup_le ?_ ?_
            · simpa [L] using (Subgroup.normalizer (B0 : Set G)).normalCore_le
            · intro x hx
              have hxB : x ∈ Subgroup.normalizer (B : Set G) := by
                rw [Subgroup.normalizer_eq_top (H := B)]
                exact Subgroup.mem_top x
              simpa [B0] using
                (Subgroup.inf_normalizer_le_normalizer_inf (H := B) (K := Z) ⟨hxB, hx⟩)
        let Bbar : Subgroup (G ⧸ L) := B.map qL
        let B0bar : Subgroup (G ⧸ L) := B0.map qL
        have hBbar_normal : Bbar.Normal := by
          dsimp [Bbar, qL]
          exact Subgroup.Normal.map (H := B) hBnormal (QuotientGroup.mk' L)
            (QuotientGroup.mk'_surjective L)
        have hBbar_p : IsPGroup p Bbar := by
          dsimp [Bbar, qL]
          exact IsPGroup.map (p := p) (H := B) hBp (QuotientGroup.mk' L)
        have hB0bar_le_Bbar : B0bar ≤ Bbar := by
          dsimp [B0bar, Bbar, qL]
          exact Subgroup.map_mono inf_le_left
        have hcentBbar_le_normB0bar :
            Subgroup.centralizer (Bbar : Set (G ⧸ L)) ≤
              Subgroup.normalizer (B0bar : Set (G ⧸ L)) := by
          intro x hx
          rw [Subgroup.mem_normalizer_iff]
          intro y
          constructor
          · intro hy
            have hxy : x * y = y * x :=
              (Subgroup.mem_centralizer_iff.mp hx _ (hB0bar_le_Bbar hy)).symm
            have hconj : x * y * x⁻¹ = y := by
              calc
                x * y * x⁻¹ = y * x * x⁻¹ := by rw [hxy, mul_assoc]
                _ = y := by simp
            simpa [hconj] using hy
          · intro hy
            have hxinv : x⁻¹ ∈ Subgroup.centralizer (Bbar : Set (G ⧸ L)) :=
              (Subgroup.centralizer (Bbar : Set (G ⧸ L))).inv_mem hx
            have hxy : x⁻¹ * (x * y * x⁻¹) = (x * y * x⁻¹) * x⁻¹ :=
              (Subgroup.mem_centralizer_iff.mp hxinv _ (hB0bar_le_Bbar hy)).symm
            have hy' : x⁻¹ * (x * y * x⁻¹) * x ∈ B0bar := by
              have hconj : x⁻¹ * (x * y * x⁻¹) * x = x * y * x⁻¹ := by
                calc
                  x⁻¹ * (x * y * x⁻¹) * x = ((x * y * x⁻¹) * x⁻¹) * x := by
                    rw [hxy]
                  _ = x * y * x⁻¹ := by simp [mul_assoc]
              simpa [hconj] using hy
            simpa [mul_assoc] using hy'
        have hJ_not_le_L :
            ¬ thompsonSubgroup (G := G) U ≤ L := by
          let : L.Normal := by
            dsimp [L]
            infer_instance
          intro hJ_le_L
          let R : Subgroup G := U ⊓ L
          have hJ_le_R : thompsonSubgroup (G := G) U ≤ R := by
            intro x hx
            exact ⟨rzj_thompsonSubgroup_le (G := G) U hx, hJ_le_L hx⟩
          have hZ_eq_R : thompsonCenter (G := G) R = Z := by
            simpa [Z, R] using
              (rzj_thompsonCenter_eq_of_le (G := G) (P := U) (R := R)
                inf_le_left hJ_le_R)
          have hFr : Subgroup.normalizer (R : Set G) ⊔ L = ⊤ := by
            obtain ⟨S, hS_map⟩ := hsyl
            simpa [R, hS_map] using (Sylow.normalizer_sup_eq_top (p := p) (N := L) S)
          have hL_le_norm_B0 : L ≤ Subgroup.normalizer (B0 : Set G) := by
            simpa [L] using (Subgroup.normalizer (B0 : Set G)).normalCore_le
          have hB0_normal' : B0.Normal := by
            apply (Subgroup.normalizer_eq_top_iff).mp
            apply top_le_iff.mp
            rw [← hFr]
            intro g hg
            rcases
                (Subgroup.mem_sup_of_normal_right
                  (s := Subgroup.normalizer (R : Set G)) (t := L) (x := g)).1 hg with
              ⟨n, hnR, l, hlL, rfl⟩
            have hnZ :
                n ∈ Subgroup.normalizer (Z : Set G) := by
              have hnTc :
                  n ∈ Subgroup.normalizer (thompsonCenter (G := G) R : Set G) :=
                (rzj_normalizer_le_normalizer_thompsonCenter (G := G) R) hnR
              simpa [hZ_eq_R] using hnTc
            have hnB :
                n ∈ Subgroup.normalizer (B : Set G) := by
              rw [Subgroup.normalizer_eq_top (H := B)]
              simp
            have hnB0 :
                n ∈ Subgroup.normalizer (B0 : Set G) := by
              simpa [B0] using
                (Subgroup.inf_normalizer_le_normalizer_inf (H := B) (K := Z) ⟨hnB, hnZ⟩)
            exact (Subgroup.normalizer (B0 : Set G)).mul_mem hnB0 (hL_le_norm_B0 hlL)
          exact hB0_not_normal hB0_normal'
        have hA_exists :
            ∃ A : Subgroup G,
              A ∈ thompsonAbelianSubgroups (G := G) U ∧
                ⁅⁅B, A⁆, A⁆ = ⊥ ∧ A ≤ L := by
          obtain ⟨A, hA, hB_norm_A⟩ :=
            rzj_theorem_8_2_9 (G := G) (P := U) (B := B) (by
              intro A hA hB_not_norm_A
              have hx_exists : ∃ x ∈ B, x ∉ Subgroup.normalizer (A : Set G) := by
                by_contra hx_not_exists
                apply hB_not_norm_A
                intro x hx
                by_contra hx_not_norm
                exact hx_not_exists ⟨x, hx, hx_not_norm⟩
              obtain ⟨x, hxB, hx_not_norm_A⟩ := hx_exists
              let H : Subgroup G := B ⊔ A
              have hH_le_P : H ≤ U := by
                dsimp [H]
                exact sup_le hB_le_P hA.1
              have hH_p : IsPGroup p ↥H := hU.to_le hH_le_P
              have habelian_step :
                  ∃ n, 0 < n ∧ IsMulCommutative (rzj_replacementCommChain B A n) := by
                exact
                  rzj_replacementCommChain_exists_positive_abelian
                    (p := p) B A hBne (by simpa [H] using hH_p)
              let nA : ℕ := Nat.find habelian_step
              have hnA_pos : 0 < nA := (Nat.find_spec habelian_step).1
              have hnA_comm : IsMulCommutative (rzj_replacementCommChain B A nA) :=
                (Nat.find_spec habelian_step).2
              have hbot_step : ∃ n, rzj_replacementCommChain B A n = ⊥ := by
                exact
                  rzj_replacementCommChain_eventually_bot
                    (p := p) B A (by simpa [H] using hH_p)
              let rA : ℕ := Nat.find hbot_step
              have hrA_bot : rzj_replacementCommChain B A rA = ⊥ := Nat.find_spec hbot_step
              have hrA_pos : 0 < rA := by
                have hrA_ne_zero : rA ≠ 0 := by
                  intro hrA_zero
                  apply hBne
                  have hr0 : rzj_replacementCommChain B A 0 = ⊥ := by
                    simpa [rA, hrA_zero] using hrA_bot
                  simpa [rzj_replacementCommChain_zero] using hr0
                exact Nat.pos_of_ne_zero hrA_ne_zero
              have hnA_min :
                  ∀ m, 0 < m → IsMulCommutative (rzj_replacementCommChain B A m) → nA ≤ m := by
                intro m hmpos hmcomm
                exact Nat.find_min' habelian_step ⟨hmpos, hmcomm⟩
              have hrA_min :
                  ∀ m, rzj_replacementCommChain B A m = ⊥ → rA ≤ m := by
                intro m hm
                exact Nat.find_min' hbot_step hm
              have hD2_ne_bot : rzj_replacementCommChain B A 2 ≠ ⊥ := by
                exact
                  rzj_replacementCommChain_two_ne_bot_of_not_normalizer
                    (G := G) (P := U) hA hB_le_P hB_not_norm_A
              have hnA_le_rA : nA ≤ rA := by
                exact hnA_min rA hrA_pos <| by
                  rw [hrA_bot]
                  infer_instance
              have hnA_succ_lt_rA :
                  rzj_replacementCommChain B A (nA + 1) ≠ ⊥ → nA + 1 < rA := by
                intro hDnA_succ_ne_bot
                by_contra hnot_lt
                have hrA_le : rA ≤ nA + 1 := Nat.le_of_not_gt hnot_lt
                have hDnA_succ_bot : rzj_replacementCommChain B A (nA + 1) = ⊥ := by
                  exact
                    rzj_replacementCommChain_eq_bot_of_eq_bot_of_le
                      B A hrA_le hrA_bot
                exact hDnA_succ_ne_bot hDnA_succ_bot
              have hZ_le_A : Z ≤ A := rzj_thompsonCenter_le_of_mem hA
              have hBcomm_le_A : Bcomm ≤ A := hBcomm_le_Z.trans hZ_le_A
              have hAinfB_cent_D1 :
                  A ⊓ B ≤
                    Subgroup.centralizer
                      (((rzj_replacementCommChain B A 1 : Subgroup G) : Set G)) := by
                simpa [Bcomm, rzj_replacementCommChain_succ, rzj_replacementCommChain_zero] using
                  (rzj_inf_le_centralizer_commutator_of_commutator_le
                    (G := G) (P := U) (B := B) (A := A) hA hBcomm_le_A)
              have hAinfB_cent_Di :
                  ∀ i, 1 ≤ i →
                    A ⊓ B ≤
                      Subgroup.centralizer
                        (((rzj_replacementCommChain B A i : Subgroup G) : Set G)) := by
                intro i hi x hx
                rw [Subgroup.mem_centralizer_iff]
                intro y hy
                exact
                  (Subgroup.mem_centralizer_iff.mp (hAinfB_cent_D1 hx) y)
                    ((rzj_replacementCommChain_antitone B A hi) hy)
              by_cases hDnA_succ_bot : rzj_replacementCommChain B A (nA + 1) = ⊥
              · let H : Subgroup G := B ⊔ A
                let Bsub : Subgroup H := B.subgroupOf H
                let Asub : Subgroup H := A.subgroupOf H
                let Nsub : Subgroup H := Bcomm.subgroupOf H
                let qH : H →* H ⧸ Nsub := QuotientGroup.mk' Nsub
                let Dbar : ℕ → Subgroup (H ⧸ Nsub) :=
                  fun i => (rzj_replacementCommChainSub B A i).map qH
                let : Bsub.Normal := hBnormal.subgroupOf H
                let : Nsub.Normal := by
                  change ((⁅B, B⁆).subgroupOf H).Normal
                  exact (Subgroup.commutator_normal B B).subgroupOf H
                have hBcomm_le_cent_A : Bcomm ≤ Subgroup.centralizer (A : Set G) := by
                  exact
                    hBcomm_le_A.trans
                      ((Subgroup.le_centralizer_iff_isMulCommutative (K := A)).2 hA.2.1)
                have hBcomm_le_cent_H : Bcomm ≤ Subgroup.centralizer (H : Set G) := by
                  dsimp [H]
                  rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure]
                  intro z hz
                  rw [Subgroup.mem_centralizer_iff]
                  intro y hy
                  rcases hy with hyB | hyA
                  · exact (Subgroup.mem_centralizer_iff.mp (hBcomm_le_cent_B hz) y hyB)
                  · exact (Subgroup.mem_centralizer_iff.mp (hBcomm_le_cent_A hz) y hyA)
                have hNsub_cent_top :
                    Nsub ≤ Subgroup.centralizer ((⊤ : Subgroup H) : Set H) := by
                  intro z hz
                  rw [Subgroup.mem_centralizer_iff]
                  intro y hy
                  apply Subtype.ext
                  exact
                    Subgroup.mem_centralizer_iff.mp
                      (hBcomm_le_cent_H (show (z : G) ∈ Bcomm from hz)) y.1 y.2
                have hBsub_sup_Asub_top : Bsub ⊔ Asub = ⊤ := by
                  apply (Subgroup.map_subtype_inj (H := H)).mp
                  calc
                    (Bsub ⊔ Asub).map H.subtype = B ⊔ A := by
                      rw [Subgroup.map_sup,
                        Subgroup.map_subgroupOf_eq_of_le le_sup_left,
                        Subgroup.map_subgroupOf_eq_of_le le_sup_right]
                    _ = H := by rfl
                    _ = (⊤ : Subgroup H).map H.subtype := by
                      simpa [MonoidHom.range_eq_map] using
                        (H.range_subtype : H.subtype.range = H).symm
                have hBsub_comm_le_Nsub : ⁅Bsub, Bsub⁆ ≤ Nsub := by
                  intro x hx
                  have hxmap : (x : G) ∈ Bcomm := by
                    have hxmap' :
                        (x : G) ∈ (⁅Bsub, Bsub⁆).map H.subtype := by
                      exact Subgroup.mem_map_of_mem H.subtype hx
                    rw [commutator_subgroupOf_map_eq
                      (S := H) (H := B) (R := B) le_sup_left le_sup_left] at hxmap'
                    simpa [Bcomm] using hxmap'
                  change x ∈ Bcomm.subgroupOf H
                  exact hxmap
                have hBbar_comm : IsMulCommutative (Bsub.map qH) := by
                  have hBbar_comm_eq :
                      ⁅Bsub.map qH, Bsub.map qH⁆ = ⊥ := by
                    apply le_antisymm
                    · calc
                        ⁅Bsub.map qH, Bsub.map qH⁆ = (⁅Bsub, Bsub⁆).map qH := by
                          rw [Subgroup.map_commutator]
                        _ ≤ Nsub.map qH := Subgroup.map_mono hBsub_comm_le_Nsub
                        _ = ⊥ := QuotientGroup.map_mk'_self (N := Nsub)
                    · exact bot_le
                  exact
                    (Subgroup.le_centralizer_iff_isMulCommutative (K := Bsub.map qH)).1 <|
                      (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hBbar_comm_eq
                have hAsub_comm : IsMulCommutative Asub := by
                  let : IsMulCommutative A := hA.2.1
                  simpa [Asub] using
                    (Subgroup.subgroupOf_isMulCommutative (H := A) (K := H))
                have hAbar_comm : IsMulCommutative (Asub.map qH) := by
                  let : IsMulCommutative Asub := hAsub_comm
                  exact Subgroup.map_isMulCommutative (H := Asub) qH
                have hBbar_sup_Abar_top :
                    Bsub.map qH ⊔ Asub.map qH = ⊤ := by
                  calc
                    Bsub.map qH ⊔ Asub.map qH = (Bsub ⊔ Asub).map qH := by
                      rw [← Subgroup.map_sup]
                    _ = (⊤ : Subgroup H).map qH := by rw [hBsub_sup_Asub_top]
                    _ = ⊤ := Subgroup.map_top_of_surjective qH (QuotientGroup.mk'_surjective Nsub)
                have hDbar_le_Bbar : ∀ i, Dbar i ≤ Bsub.map qH := by
                  intro i
                  dsimp [Dbar]
                  refine Subgroup.map_mono ?_
                  rw [rzj_replacementCommChainSub_eq_subgroupOf]
                  intro x hx
                  exact rzj_replacementCommChain_le_left B A i hx
                have hDbar_comm_A :
                    ∀ i, ⁅Dbar i, Asub.map qH⁆ = Dbar (i + 1) := by
                  intro i
                  change
                    ⁅(rzj_replacementCommChainSub B A i).map qH, (A.subgroupOf H).map qH⁆ =
                      (rzj_replacementCommChainSub B A (i + 1)).map qH
                  rw [rzj_replacementCommChainSub_succ, Subgroup.map_commutator]
                have hDbar_comm_A_rev :
                    ∀ i, ⁅Asub.map qH, Dbar i⁆ = Dbar (i + 1) := by
                  intro i
                  simpa [Subgroup.commutator_comm] using hDbar_comm_A i
                have hcommAbar_Bbar : ⁅Asub.map qH, Bsub.map qH⁆ = Dbar 1 := by
                  change ⁅Asub.map qH, Dbar 0⁆ = Dbar 1
                  simpa [Dbar, rzj_replacementCommChainSub_zero] using hDbar_comm_A_rev 0
                have hcommBbar_Abar : ⁅Bsub.map qH, Asub.map qH⁆ = Dbar 1 := by
                  change ⁅Dbar 0, Asub.map qH⁆ = Dbar 1
                  simpa [Dbar, rzj_replacementCommChainSub_zero] using hDbar_comm_A 0
                have hL1q_le :
                    (⊤ : Subgroup (H ⧸ Nsub)).lowerCentralSeries 1 ≤ Dbar 1 := by
                  rw [Subgroup.top_lowerCentralSeries_one]
                  refine (Subgroup.commutator_le).2 ?_
                  intro y hy z hz
                  have hy' : y ∈ Bsub.map qH ⊔ Asub.map qH := by
                    simp [hBbar_sup_Abar_top]
                  have hz' : z ∈ Bsub.map qH ⊔ Asub.map qH := by
                    simp [hBbar_sup_Abar_top]
                  let : (Bsub.map qH).Normal := by
                    exact
                      Subgroup.Normal.map
                        (H := Bsub) (inferInstance : Bsub.Normal) qH
                        (QuotientGroup.mk'_surjective Nsub)
                  rcases
                      (Subgroup.mem_sup_of_normal_left
                        (s := Bsub.map qH) (t := Asub.map qH) (x := y)).1 hy' with
                    ⟨b1, hb1, a1, ha1, rfl⟩
                  rcases
                      (Subgroup.mem_sup_of_normal_left
                        (s := Bsub.map qH) (t := Asub.map qH) (x := z)).1 hz' with
                    ⟨b2, hb2, a2, ha2, rfl⟩
                  have hb12 : b1 * b2 = b2 * b1 := by
                    exact
                      setLike_mul_comm
                        (s := Bsub.map qH) hb1 hb2
                  have ha12 : a1 * a2 = a2 * a1 := by
                    exact
                      setLike_mul_comm
                        (s := Asub.map qH) ha1 ha2
                  have ha1b2_mem : ⁅a1, b2⁆ ∈ Dbar 1 := by
                    have : ⁅a1, b2⁆ ∈ ⁅Asub.map qH, Bsub.map qH⁆ := by
                      exact Subgroup.commutator_mem_commutator ha1 hb2
                    rwa [hcommAbar_Bbar] at this
                  have hb1a2_mem : ⁅b1, a2⁆ ∈ Dbar 1 := by
                    have : ⁅b1, a2⁆ ∈ ⁅Bsub.map qH, Asub.map qH⁆ := by
                      exact Subgroup.commutator_mem_commutator hb1 ha2
                    rwa [hcommBbar_Abar] at this
                  have ha1b2_B : ⁅a1, b2⁆ ∈ Bsub.map qH := hDbar_le_Bbar 1 ha1b2_mem
                  have hb1a2_B : ⁅b1, a2⁆ ∈ Bsub.map qH := hDbar_le_Bbar 1 hb1a2_mem
                  have hb1_conj_ha1b2 :
                      b1 * ⁅a1, b2⁆ * b1⁻¹ = ⁅a1, b2⁆ := by
                    have hcomm : b1 * ⁅a1, b2⁆ = ⁅a1, b2⁆ * b1 := by
                      exact
                        setLike_mul_comm
                          (s := Bsub.map qH) hb1 ha1b2_B
                    calc
                      b1 * ⁅a1, b2⁆ * b1⁻¹ = (⁅a1, b2⁆ * b1) * b1⁻¹ := by
                        rw [hcomm]
                      _ = ⁅a1, b2⁆ := by simp [mul_assoc]
                  have hb2_conj_hb1a2 :
                      b2 * ⁅b1, a2⁆ * b2⁻¹ = ⁅b1, a2⁆ := by
                    have hcomm : b2 * ⁅b1, a2⁆ = ⁅b1, a2⁆ * b2 := by
                      exact
                        setLike_mul_comm
                          (s := Bsub.map qH) hb2 hb1a2_B
                    calc
                      b2 * ⁅b1, a2⁆ * b2⁻¹ = (⁅b1, a2⁆ * b2) * b2⁻¹ := by
                        rw [hcomm]
                      _ = ⁅b1, a2⁆ := by simp [mul_assoc]
                  have hbb2 : ⁅b1, b2⁆ = 1 := by
                    exact
                      commutatorElement_eq_one_iff_commute.mpr
                        (setLike_mul_comm
                          (s := Bsub.map qH) hb1 hb2)
                  have haa2 : ⁅a1, a2⁆ = 1 := by
                    exact
                      commutatorElement_eq_one_iff_commute.mpr
                        (setLike_mul_comm
                          (s := Asub.map qH) ha1 ha2)
                  have hleft_mem : ⁅b1 * a1, b2⁆ ∈ Dbar 1 := by
                    rw [commutator_mul_left, hbb2]
                    simpa [hb1_conj_ha1b2, mul_assoc] using ha1b2_mem
                  have hright_mem : ⁅b1 * a1, a2⁆ ∈ Dbar 1 := by
                    rw [commutator_mul_left, haa2]
                    simpa [mul_assoc] using hb1a2_mem
                  have hright_B : ⁅b1 * a1, a2⁆ ∈ Bsub.map qH := hDbar_le_Bbar 1 hright_mem
                  have hright_conj :
                      b2 * ⁅b1 * a1, a2⁆ * b2⁻¹ = ⁅b1 * a1, a2⁆ := by
                    have hcomm : b2 * ⁅b1 * a1, a2⁆ = ⁅b1 * a1, a2⁆ * b2 := by
                      exact
                        setLike_mul_comm
                          (s := Bsub.map qH) hb2 hright_B
                    calc
                      b2 * ⁅b1 * a1, a2⁆ * b2⁻¹ = (⁅b1 * a1, a2⁆ * b2) * b2⁻¹ := by
                        rw [hcomm]
                      _ = ⁅b1 * a1, a2⁆ := by simp [mul_assoc]
                  rw [commutator_mul_right]
                  simpa [hright_conj, mul_assoc] using (Dbar 1).mul_mem hleft_mem hright_mem
                have hLq_le_Dbar :
                    ∀ i, (⊤ : Subgroup (H ⧸ Nsub)).lowerCentralSeries (i + 1) ≤
                      Dbar (i + 1) := by
                  intro i
                  induction i with
                  | zero =>
                      exact hL1q_le
                  | succ i ih =>
                      rw [Subgroup.lowerCentralSeries_succ]
                      refine (Subgroup.commutator_le).2 ?_
                      intro x hx y hy
                      have hxD : x ∈ Dbar (i + 1) := ih hx
                      have hy' : y ∈ Bsub.map qH ⊔ Asub.map qH := by
                        simp [hBbar_sup_Abar_top]
                      let : (Bsub.map qH).Normal := by
                        exact
                          Subgroup.Normal.map
                            (H := Bsub) (inferInstance : Bsub.Normal) qH
                            (QuotientGroup.mk'_surjective Nsub)
                      rcases
                          (Subgroup.mem_sup_of_normal_left
                            (s := Bsub.map qH) (t := Asub.map qH) (x := y)).1 hy' with
                        ⟨b, hb, a, ha, rfl⟩
                      have hxb : ⁅x, b⁆ = 1 := by
                        have hxB : x ∈ Bsub.map qH := hDbar_le_Bbar (i + 1) hxD
                        exact
                          commutatorElement_eq_one_iff_commute.mpr
                            (setLike_mul_comm
                              (s := Bsub.map qH) hxB hb)
                      have hxa_mem : ⁅x, a⁆ ∈ Dbar (i + 2) := by
                        have : ⁅x, a⁆ ∈ ⁅Dbar (i + 1), Asub.map qH⁆ := by
                          exact Subgroup.commutator_mem_commutator hxD ha
                        simpa [hDbar_comm_A (i + 1)] using this
                      have hxa_B : ⁅x, a⁆ ∈ Bsub.map qH := hDbar_le_Bbar (i + 2) hxa_mem
                      have hconj :
                          b * ⁅x, a⁆ * b⁻¹ = ⁅x, a⁆ := by
                        have hcomm : b * ⁅x, a⁆ = ⁅x, a⁆ * b := by
                          exact
                            setLike_mul_comm
                              (s := Bsub.map qH) hb hxa_B
                        calc
                          b * ⁅x, a⁆ * b⁻¹ = (⁅x, a⁆ * b) * b⁻¹ := by
                            rw [hcomm]
                          _ = ⁅x, a⁆ := by simp [mul_assoc]
                      rw [commutator_mul_right, hxb]
                      simpa [hconj, mul_assoc] using hxa_mem
                have hLmap_le :
                    ∀ i, ((⊤ : Subgroup H).lowerCentralSeries i).map qH ≤
                      (⊤ : Subgroup (H ⧸ Nsub)).lowerCentralSeries i := by
                  intro i
                  induction i with
                  | zero =>
                      simp
                  | succ i ih =>
                      change
                        Subgroup.map qH ⁅(⊤ : Subgroup H).lowerCentralSeries i,
                          (⊤ : Subgroup H)⁆ ≤
                            (⊤ : Subgroup (H ⧸ Nsub)).lowerCentralSeries (i + 1)
                      rw [Subgroup.map_commutator, Subgroup.lowerCentralSeries_succ,
                        Subgroup.map_top_of_surjective qH (QuotientGroup.mk'_surjective Nsub)]
                      exact Subgroup.commutator_mono ih le_rfl
                have hDbar_bot : Dbar (nA + 1) = ⊥ := by
                  have hbot_sub : ((⊥ : Subgroup G).subgroupOf H) = (⊥ : Subgroup H) := by
                    ext x
                    simp
                  calc
                    Dbar (nA + 1) = Subgroup.map qH (rzj_replacementCommChainSub B A (nA + 1)) := by
                      rfl
                    _ = ((rzj_replacementCommChain B A (nA + 1)).subgroupOf H).map qH := by
                      rw [rzj_replacementCommChainSub_eq_subgroupOf]
                    _ = (⊥ : Subgroup H).map qH := by rw [hDnA_succ_bot, hbot_sub]
                    _ = ⊥ := by simp
                have hLq_bot :
                    (⊤ : Subgroup (H ⧸ Nsub)).lowerCentralSeries (nA + 1) = ⊥ := by
                  apply le_antisymm
                  · exact (hLq_le_Dbar nA).trans_eq hDbar_bot
                  · exact bot_le
                have hLH_le_Nsub :
                    (⊤ : Subgroup H).lowerCentralSeries (nA + 1) ≤ Nsub := by
                  have hmap_bot :
                      ((⊤ : Subgroup H).lowerCentralSeries (nA + 1)).map qH = ⊥ := by
                    apply le_antisymm
                    · exact (hLmap_le (nA + 1)).trans_eq hLq_bot
                    · exact bot_le
                  exact
                    (by
                      have hker :
                          (⊤ : Subgroup H).lowerCentralSeries (nA + 1) ≤ qH.ker :=
                        (Subgroup.map_eq_bot_iff
                          (f := qH)
                          (H := (⊤ : Subgroup H).lowerCentralSeries (nA + 1))).1 hmap_bot
                      simpa [qH, QuotientGroup.ker_mk'] using hker)
                have hLH_bot : (⊤ : Subgroup H).lowerCentralSeries (nA + 2) = ⊥ := by
                  have hcomm_bot :
                      ⁅(⊤ : Subgroup H).lowerCentralSeries (nA + 1),
                        (⊤ : Subgroup H)⁆ = ⊥ := by
                    exact
                      (Subgroup.commutator_eq_bot_iff_le_centralizer).2
                        (hLH_le_Nsub.trans hNsub_cent_top)
                  have hidx : nA + 2 = (nA + 1) + 1 := by omega
                  simpa [Subgroup.lowerCentralSeries, hidx] using hcomm_bot
                have hnA_le_two : nA ≤ 2 := by
                  by_contra hnA_gt_two
                  have hnA_ge_three : 3 ≤ nA := by omega
                  have hLpred_comm :
                      IsMulCommutative ((⊤ : Subgroup H).lowerCentralSeries (nA - 1)) := by
                    have hcomm_bot :
                        ⁅(⊤ : Subgroup H).lowerCentralSeries (nA - 1),
                          (⊤ : Subgroup H).lowerCentralSeries (nA - 1)⁆ = ⊥ := by
                      apply le_antisymm
                      · calc
                          ⁅(⊤ : Subgroup H).lowerCentralSeries (nA - 1),
                            (⊤ : Subgroup H).lowerCentralSeries (nA - 1)⁆ ≤
                              (⊤ : Subgroup H).lowerCentralSeries
                                ((nA - 1) + (nA - 1) + 1) := by
                                simpa using
                                  (CFSG.Glauberman.lowerCentralSeries_commutator_le
                                    (G := H) (nA - 1) (nA - 1))
                          _ ≤ (⊤ : Subgroup H).lowerCentralSeries (nA + 2) := by
                                apply Subgroup.lowerCentralSeries_antitone
                                omega
                          _ = ⊥ := hLH_bot
                      · exact bot_le
                    exact
                      (Subgroup.le_centralizer_iff_isMulCommutative
                        (K := (⊤ : Subgroup H).lowerCentralSeries (nA - 1))).1 <|
                        (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hcomm_bot
                  have hDpred_sub_comm :
                      IsMulCommutative ((rzj_replacementCommChain B A (nA - 1)).subgroupOf H) := by
                    have hsub :
                        (rzj_replacementCommChain B A (nA - 1)).subgroupOf H ≤
                          (⊤ : Subgroup H).lowerCentralSeries (nA - 1) := by
                      rw [← rzj_replacementCommChainSub_eq_subgroupOf]
                      exact rzj_replacementCommChainSub_le_lowerCentralSeries B A (nA - 1)
                    refine ⟨?_⟩
                    exact ⟨fun y z => by
                      apply Subtype.ext
                      simpa using
                        (setLike_mul_comm
                          (s := (⊤ : Subgroup H).lowerCentralSeries (nA - 1))
                          (hsub y.2) (hsub z.2))⟩
                  have hDpred_comm :
                      IsMulCommutative (rzj_replacementCommChain B A (nA - 1)) := by
                    refine ⟨?_⟩
                    exact ⟨fun y z => by
                      let yH : ((rzj_replacementCommChain B A (nA - 1)).subgroupOf H) :=
                        ⟨⟨y, rzj_replacementCommChain_le_sup B A (nA - 1) y.2⟩, y.2⟩
                      let zH : ((rzj_replacementCommChain B A (nA - 1)).subgroupOf H) :=
                        ⟨⟨z, rzj_replacementCommChain_le_sup B A (nA - 1) z.2⟩, z.2⟩
                      apply Subtype.ext
                      simpa [yH, zH] using
                        congrArg Subtype.val
                          ((IsMulCommutative.is_comm
                            (M := ((rzj_replacementCommChain B A (nA - 1)).subgroupOf H))).comm
                              yH zH)⟩
                  have hnA_pred_pos : 0 < nA - 1 := by
                    omega
                  have hle : nA ≤ nA - 1 :=
                    hnA_min (nA - 1) hnA_pred_pos hDpred_comm
                  omega
                have hnA_ne_one : nA ≠ 1 := by
                  intro hnA_eq_one
                  have hD2_bot : rzj_replacementCommChain B A 2 = ⊥ := by
                    simpa [hnA_eq_one] using hDnA_succ_bot
                  exact hD2_ne_bot hD2_bot
                have hnA_ge_two : 2 ≤ nA := by
                  by_contra hlt
                  have hnA_le_one : nA ≤ 1 := by omega
                  have hnA_eq_one : nA = 1 := by omega
                  exact hnA_ne_one hnA_eq_one
                have hnA_eq_two : nA = 2 := by omega
                have hD3_bot : rzj_replacementCommChain B A 3 = ⊥ := by
                  simpa [hnA_eq_two] using hDnA_succ_bot
                have hxP : x ∈ U := hB_le_P hxB
                have hD2_le_A : rzj_replacementCommChain B A 2 ≤ A := by
                  exact
                    rzj_replacementCommChain_le_of_succ_eq_bot
                      (G := G) (P := U) (B := B) (A := A)
                      hA hB_le_P hD3_bot
                have hD2_le_B : rzj_replacementCommChain B A 2 ≤ B :=
                  rzj_replacementCommChain_le_left B A 2
                have hDbar3_bot : Dbar 3 = ⊥ := by
                  simpa [hnA_eq_two] using hDbar_bot
                have hDbar2_cent_Abar :
                    Dbar 2 ≤
                      Subgroup.centralizer
                        (((Asub.map qH : Subgroup (H ⧸ Nsub)) : Set (H ⧸ Nsub))) := by
                  exact
                    (Subgroup.commutator_eq_bot_iff_le_centralizer).1 <| by
                      simpa [hDbar_comm_A 2] using hDbar3_bot
                have hxu_exists :
                    ∃ u ∈ A, ⁅x, u⁆ ∉ Subgroup.centralizer (A : Set G) := by
                  by_contra hno
                  let f : G ≃* G := MulAut.conj x
                  have hmap_le : A.map f.toMonoidHom ≤ A := by
                    intro y hy
                    rcases Subgroup.mem_map.mp hy with ⟨u, huA, rfl⟩
                    have hxu_centA : ⁅x, u⁆ ∈ Subgroup.centralizer (A : Set G) := by
                      by_contra hnot
                      exact hno ⟨u, huA, hnot⟩
                    have hxu_subcent : ⁅x, u⁆ ∈ rzj_subgroupCentralizerIn' U A := by
                      refine ⟨hxu_centA, ?_⟩
                      exact
                        (Subgroup.commutator_le_self (H := U))
                          (Subgroup.commutator_mem_commutator hxP (hA.1 huA))
                    have hxuA : ⁅x, u⁆ ∈ A := by
                      simpa [rzj_thompsonAbelianSubgroups_centralizer_eq (G := G) hA] using
                        hxu_subcent
                    simpa [f, show x * u * x⁻¹ = ⁅x, u⁆ * u by
                      simp [commutatorElement_def, mul_assoc]] using A.mul_mem hxuA huA
                  have hmap_eq : A.map f.toMonoidHom = A := by
                    apply Subgroup.eq_of_le_of_card_ge hmap_le
                    have hcard :
                        Nat.card (A.map f.toMonoidHom) = Nat.card A := by
                      simpa [f] using
                        (Subgroup.card_map_of_injective (K := A) (f := f.toMonoidHom) f.injective)
                    exact le_of_eq hcard.symm
                  apply hx_not_norm_A
                  rw [← Subgroup.conjAct_pointwise_smul_iff]
                  change A.map (MulAut.conj x).toMonoidHom = A
                  simpa [f] using hmap_eq
                obtain ⟨u, huA, hxu_not_centA⟩ := hxu_exists
                have hgen_comm :
                    ∀ u ∈ A, ∀ v ∈ A, ⁅⁅x, u⁆, ⁅x, v⁆⁆ = 1 := by
                  intro u huA v hvA
                  let a : G := ⁅x, u⁆
                  let b : G := ⁅x, v⁆
                  let d1 : G := ⁅a, v⁆
                  let d2 : G := ⁅b, u⁆
                  have haD1 : a ∈ rzj_replacementCommChain B A 1 := by
                    dsimp [a]
                    have : ⁅B, A⁆ = rzj_replacementCommChain B A (0 + 1) := by rfl
                    rw [this, rzj_replacementCommChain_succ, rzj_replacementCommChain_zero]
                    exact Subgroup.commutator_mem_commutator hxB huA
                  have hbD1 : b ∈ rzj_replacementCommChain B A 1 := by
                    dsimp [b]
                    have : ⁅B, A⁆ = rzj_replacementCommChain B A (0 + 1) := by rfl
                    rw [this, rzj_replacementCommChain_succ, rzj_replacementCommChain_zero]
                    exact Subgroup.commutator_mem_commutator hxB hvA
                  have haB : a ∈ B := (rzj_replacementCommChain_le_left B A 1) haD1
                  have hbB : b ∈ B := (rzj_replacementCommChain_le_left B A 1) hbD1
                  have hd1D2 : d1 ∈ rzj_replacementCommChain B A 2 := by
                    dsimp [d1]
                    have : ⁅⁅B, A⁆, A⁆ = rzj_replacementCommChain B A (1 + 1) := rfl
                    rw [this, rzj_replacementCommChain_succ]
                    exact Subgroup.commutator_mem_commutator haD1 hvA
                  have hd2D2 : d2 ∈ rzj_replacementCommChain B A 2 := by
                    dsimp [d2]
                    have : ⁅⁅B, A⁆, A⁆ = rzj_replacementCommChain B A (1 + 1) := rfl
                    rw [this, rzj_replacementCommChain_succ]
                    exact Subgroup.commutator_mem_commutator hbD1 huA
                  have hd1A : d1 ∈ A := hD2_le_A hd1D2
                  have hd2A : d2 ∈ A := hD2_le_A hd2D2
                  have hd1B : d1 ∈ B := hD2_le_B hd1D2
                  have hd2B : d2 ∈ B := hD2_le_B hd2D2
                  have hd1AB : d1 ∈ A ⊓ B := ⟨hd1A, hd1B⟩
                  have hd2AB : d2 ∈ A ⊓ B := ⟨hd2A, hd2B⟩
                  have hd1_cent_D1 :
                      d1 ∈ Subgroup.centralizer
                        (((rzj_replacementCommChain B A 1 : Subgroup G) : Set G)) :=
                    hAinfB_cent_D1 hd1AB
                  have hd2_cent_D1 :
                      d2 ∈ Subgroup.centralizer
                        (((rzj_replacementCommChain B A 1 : Subgroup G) : Set G)) :=
                    hAinfB_cent_D1 hd2AB
                  have hd1_cent_A : d1 ∈ Subgroup.centralizer (A : Set G) := by
                    exact
                      ((Subgroup.le_centralizer_iff_isMulCommutative (K := A)).2 hA.2.1) hd1A
                  have hd2_cent_A : d2 ∈ Subgroup.centralizer (A : Set G) := by
                    exact
                      ((Subgroup.le_centralizer_iff_isMulCommutative (K := A)).2 hA.2.1) hd2A
                  let xH : H := ⟨x, by
                    dsimp [H]
                    exact (show x ∈ B ⊔ A from Subgroup.mem_sup_left hxB)⟩
                  let uH : H := ⟨u, by
                    dsimp [H]
                    exact (show u ∈ B ⊔ A from Subgroup.mem_sup_right huA)⟩
                  let vH : H := ⟨v, by
                    dsimp [H]
                    exact (show v ∈ B ⊔ A from Subgroup.mem_sup_right hvA)⟩
                  let aH : H := ⟨a, rzj_replacementCommChain_le_sup B A 1 haD1⟩
                  let bH : H := ⟨b, rzj_replacementCommChain_le_sup B A 1 hbD1⟩
                  let d1H : H := ⟨d1, rzj_replacementCommChain_le_sup B A 2 hd1D2⟩
                  let d2H : H := ⟨d2, rzj_replacementCommChain_le_sup B A 2 hd2D2⟩
                  have huH_Abar : qH uH ∈ Asub.map qH := by
                    exact Subgroup.mem_map_of_mem qH <| by
                      simpa [Asub, uH, Subgroup.mem_subgroupOf] using huA
                  have hvH_Abar : qH vH ∈ Asub.map qH := by
                    exact Subgroup.mem_map_of_mem qH <| by
                      simpa [Asub, vH, Subgroup.mem_subgroupOf] using hvA
                  have haH_Dbar1 : qH aH ∈ Dbar 1 := by
                    dsimp [Dbar]
                    exact Subgroup.mem_map_of_mem qH <| by
                      have : ⁅B.subgroupOf (B ⊔ A), A.subgroupOf (B ⊔ A)⁆ =
                          rzj_replacementCommChainSub B A 1 := rfl
                      rw [this, rzj_replacementCommChainSub_eq_subgroupOf]
                      simpa [aH, Subgroup.mem_subgroupOf] using haD1
                  have hbH_Dbar1 : qH bH ∈ Dbar 1 := by
                    dsimp [Dbar]
                    exact Subgroup.mem_map_of_mem qH <| by
                      have : ⁅B.subgroupOf (B ⊔ A), A.subgroupOf (B ⊔ A)⁆ =
                          rzj_replacementCommChainSub B A 1 := rfl
                      rw [this, rzj_replacementCommChainSub_eq_subgroupOf]
                      simpa [bH, Subgroup.mem_subgroupOf] using hbD1
                  have hd1H_Dbar2 : qH d1H ∈ Dbar 2 := by
                    dsimp [Dbar]
                    exact Subgroup.mem_map_of_mem qH <| by
                      have : ⁅⁅B.subgroupOf (B ⊔ A), A.subgroupOf (B ⊔ A)⁆, A.subgroupOf (B ⊔ A)⁆ =
                          rzj_replacementCommChainSub B A 2 := rfl
                      rw [this, rzj_replacementCommChainSub_eq_subgroupOf]
                      simpa [d1H, Subgroup.mem_subgroupOf] using hd1D2
                  have hd2H_Dbar2 : qH d2H ∈ Dbar 2 := by
                    dsimp [Dbar]
                    exact Subgroup.mem_map_of_mem qH <| by
                      have : ⁅⁅B.subgroupOf (B ⊔ A), A.subgroupOf (B ⊔ A)⁆, A.subgroupOf (B ⊔ A)⁆ =
                          rzj_replacementCommChainSub B A 2 := rfl
                      rw [this,rzj_replacementCommChainSub_eq_subgroupOf]
                      simpa [d2H, Subgroup.mem_subgroupOf] using hd2D2
                  have haH_Bbar : qH aH ∈ Bsub.map qH := hDbar_le_Bbar 1 haH_Dbar1
                  have hbH_Bbar : qH bH ∈ Bsub.map qH := hDbar_le_Bbar 1 hbH_Dbar1
                  have hd1H_Bbar : qH d1H ∈ Bsub.map qH := hDbar_le_Bbar 2 hd1H_Dbar2
                  have hd2H_Bbar : qH d2H ∈ Bsub.map qH := hDbar_le_Bbar 2 hd2H_Dbar2
                  have haH_comm_bH : qH aH * qH bH = qH bH * qH aH := by
                    exact
                      setLike_mul_comm
                        (s := Bsub.map qH) haH_Bbar hbH_Bbar
                  have hd1bar_cent_Abar :
                      qH d1H ∈
                        Subgroup.centralizer
                          (((Asub.map qH : Subgroup (H ⧸ Nsub)) : Set (H ⧸ Nsub))) :=
                    hDbar2_cent_Abar hd1H_Dbar2
                  have hd2bar_cent_Abar :
                      qH d2H ∈
                        Subgroup.centralizer
                          (((Asub.map qH : Subgroup (H ⧸ Nsub)) : Set (H ⧸ Nsub))) :=
                    hDbar2_cent_Abar hd2H_Dbar2
                  have hq_d1_eq_d2 : qH d1H = qH d2H := by
                    have huvH : qH uH * qH vH = qH vH * qH uH := by
                      exact
                        setLike_mul_comm
                          (s := Asub.map qH) huH_Abar hvH_Abar
                    have hqa : ⁅qH xH, qH uH⁆ = qH aH := by
                      have hxuH : ⁅xH, uH⁆ = aH := by
                        apply Subtype.ext
                        rfl
                      rw [← hxuH]
                      exact (map_commutatorElement (f := qH) (g₁ := xH) (g₂ := uH)).symm
                    have hqb : ⁅qH xH, qH vH⁆ = qH bH := by
                      have hxvH : ⁅xH, vH⁆ = bH := by
                        apply Subtype.ext
                        rfl
                      rw [← hxvH]
                      exact (map_commutatorElement (f := qH) (g₁ := xH) (g₂ := vH)).symm
                    have hq_d1_inv :
                        ⁅qH uH, qH bH⁆ = (qH d2H)⁻¹ := by
                      calc
                        ⁅qH uH, qH bH⁆ = qH ⁅uH, bH⁆ := by
                          exact
                            (map_commutatorElement (f := qH) (g₁ := uH) (g₂ := bH)).symm
                        _ = (qH d2H)⁻¹ := by
                          have hbhu_eq : ⁅bH, uH⁆ = d2H := by
                            rfl
                          have hub_inv : ⁅uH, bH⁆ = (⁅bH, uH⁆)⁻¹ := by
                            simp
                          calc
                            qH ⁅uH, bH⁆ = qH ((⁅bH, uH⁆)⁻¹) := by rw [hub_inv]
                            _ = (qH ⁅bH, uH⁆)⁻¹ := by rw [qH.map_inv]
                            _ = (qH d2H)⁻¹ := by rw [hbhu_eq]
                    have hq_d2_inv :
                        ⁅qH vH, qH aH⁆ = (qH d1H)⁻¹ := by
                      calc
                        ⁅qH vH, qH aH⁆ = qH ⁅vH, aH⁆ := by
                          exact
                            (map_commutatorElement (f := qH) (g₁ := vH) (g₂ := aH)).symm
                        _ = (qH d1H)⁻¹ := by
                          have hav_eq : ⁅aH, vH⁆ = d1H := by
                            rfl
                          have hva_inv : ⁅vH, aH⁆ = (⁅aH, vH⁆)⁻¹ := by
                            simp
                          calc
                            qH ⁅vH, aH⁆ = qH ((⁅aH, vH⁆)⁻¹) := by rw [hva_inv]
                            _ = (qH ⁅aH, vH⁆)⁻¹ := by rw [qH.map_inv]
                            _ = (qH d1H)⁻¹ := by rw [hav_eq]
                    have hconj_u_b :
                        qH uH * qH bH * (qH uH)⁻¹ = (qH d2H)⁻¹ * qH bH := by
                      calc
                        qH uH * qH bH * (qH uH)⁻¹ = ⁅qH uH, qH bH⁆ * qH bH := by
                          simp [commutatorElement_def, mul_assoc]
                        _ = (qH d2H)⁻¹ * qH bH := by rw [hq_d1_inv]
                    have hconj_v_a :
                        qH vH * qH aH * (qH vH)⁻¹ = (qH d1H)⁻¹ * qH aH := by
                      calc
                        qH vH * qH aH * (qH vH)⁻¹ = ⁅qH vH, qH aH⁆ * qH aH := by
                          simp [commutatorElement_def, mul_assoc]
                        _ = (qH d1H)⁻¹ * qH aH := by rw [hq_d2_inv]
                    have hleft :
                        ⁅qH xH, qH uH * qH vH⁆ = qH aH * (qH d2H)⁻¹ * qH bH := by
                      rw [commutator_mul_right, hqa, hqb]
                      simpa [mul_assoc] using hconj_u_b
                    have hright :
                        ⁅qH xH, qH vH * qH uH⁆ = qH bH * (qH d1H)⁻¹ * qH aH := by
                      rw [commutator_mul_right, hqb, hqa]
                      simpa [mul_assoc] using hconj_v_a
                    have hEq :
                        qH aH * (qH d2H)⁻¹ * qH bH = qH bH * (qH d1H)⁻¹ * qH aH := by
                      calc
                        qH aH * (qH d2H)⁻¹ * qH bH = ⁅qH xH, qH uH * qH vH⁆ := hleft.symm
                        _ = ⁅qH xH, qH vH * qH uH⁆ := by rw [huvH]
                        _ = qH bH * (qH d1H)⁻¹ * qH aH := hright
                    have hEq' :
                        qH aH * qH bH * (qH d2H)⁻¹ =
                          qH aH * qH bH * (qH d1H)⁻¹ := by
                      calc
                        qH aH * qH bH * (qH d2H)⁻¹ = qH aH * (qH d2H)⁻¹ * qH bH := by
                          have hcomm :
                              qH bH * qH d2H = qH d2H * qH bH := by
                            exact
                              setLike_mul_comm
                                (s := Bsub.map qH) hbH_Bbar hd2H_Bbar
                          have hcomm' :
                              qH bH * (qH d2H)⁻¹ = (qH d2H)⁻¹ * qH bH := by
                            have hcomm' : Commute (qH bH) (qH d2H) := hcomm
                            exact hcomm'.inv_right.eq
                          simp [mul_assoc, ← hcomm']
                        _ = qH bH * (qH d1H)⁻¹ * qH aH := hEq
                        _ = qH bH * qH aH * (qH d1H)⁻¹ := by
                          have hcomm :
                              qH aH * qH d1H = qH d1H * qH aH := by
                            exact
                              setLike_mul_comm
                                (s := Bsub.map qH) haH_Bbar hd1H_Bbar
                          have hcomm' :
                              qH aH * (qH d1H)⁻¹ = (qH d1H)⁻¹ * qH aH := by
                            have hcomm' : Commute (qH aH) (qH d1H) := hcomm
                            exact hcomm'.inv_right.eq
                          simp [mul_assoc, ← hcomm']
                        _ = qH aH * qH bH * (qH d1H)⁻¹ := by
                          rw [haH_comm_bH]
                    have hinv_eq : (qH d2H)⁻¹ = (qH d1H)⁻¹ := by
                      exact mul_left_cancel hEq'
                    exact inv_injective hinv_eq.symm
                  have hdiff_mem : d1H / d2H ∈ Nsub := by
                    exact (QuotientGroup.eq_iff_div_mem).1 hq_d1_eq_d2
                  have hdiffBcomm : d1 / d2 ∈ Bcomm := by
                    simpa [d1H, d2H, d1, d2, Nsub, Subgroup.mem_subgroupOf] using hdiff_mem
                  have hdiff_cent_x : Commute (d1 / d2) x := by
                    exact
                      ((Subgroup.mem_centralizer_iff.mp (hBcomm_le_cent_B hdiffBcomm) x) hxB).symm
                  have hdiff_cent_xd2 : Commute (d1 / d2) ⁅x, d2⁆ := by
                    have hxd2B : ⁅x, d2⁆ ∈ B := by
                      exact
                        hBcomm_le_B <|
                          Subgroup.commutator_mem_commutator hxB hd2B
                    exact
                      ((Subgroup.mem_centralizer_iff.mp
                        (hBcomm_le_cent_B hdiffBcomm) ⁅x, d2⁆) hxd2B).symm
                  have hxdiff_one : ⁅x, d1 / d2⁆ = 1 := by
                    exact commutatorElement_eq_one_iff_commute.mpr hdiff_cent_x.symm
                  have hconj_diff_xd2 :
                      (d1 / d2) * ⁅x, d2⁆ * (d1 / d2)⁻¹ = ⁅x, d2⁆ := by
                    calc
                      (d1 / d2) * ⁅x, d2⁆ * (d1 / d2)⁻¹ =
                          (⁅x, d2⁆ * (d1 / d2)) * (d1 / d2)⁻¹ := by
                            rw [hdiff_cent_xd2.symm.eq]
                      _ = ⁅x, d2⁆ := by simp [mul_assoc]
                  have hd1v : Commute d1 v := by
                    exact ((Subgroup.mem_centralizer_iff.mp hd1_cent_A v) hvA).symm
                  have hd2u : Commute d2 u := by
                    exact ((Subgroup.mem_centralizer_iff.mp hd2_cent_A u) huA).symm
                  have hd1b : Commute d1 b := by
                    exact ((Subgroup.mem_centralizer_iff.mp hd1_cent_D1 b) hbD1).symm
                  have hd2a : Commute d2 a := by
                    exact ((Subgroup.mem_centralizer_iff.mp hd2_cent_D1 a) haD1).symm
                  have hd1_inv_v : ⁅a, v⁻¹⁆ = d1⁻¹ := by
                    rw [commutator_inv_right]
                    calc
                      v⁻¹ * d1⁻¹ * v = v⁻¹ * (d1⁻¹ * v) := by
                        simp [mul_assoc]
                      _ = v⁻¹ * (v * d1⁻¹) := by
                        rw [(hd1v.inv_left).eq]
                      _ = d1⁻¹ := by simp
                  have hd2_inv_u : ⁅b, u⁻¹⁆ = d2⁻¹ := by
                    rw [commutator_inv_right]
                    calc
                      u⁻¹ * d2⁻¹ * u = u⁻¹ * (d2⁻¹ * u) := by
                        simp [mul_assoc]
                      _ = u⁻¹ * (u * d2⁻¹) := by
                        rw [(hd2u.inv_left).eq]
                      _ = d2⁻¹ := by simp
                  have hxv_eq : x * v * x⁻¹ = b * v := by
                    dsimp [b]
                    simp [commutatorElement_def, mul_assoc]
                  have hxu_eq : x * u * x⁻¹ = a * u := by
                    dsimp [a]
                    simp [commutatorElement_def, mul_assoc]
                  have hd1_conj_xv :
                      (x * v * x⁻¹) * d1⁻¹ * (x * v * x⁻¹)⁻¹ = d1⁻¹ := by
                    have hv_fix : v * d1⁻¹ * v⁻¹ = d1⁻¹ := by
                      calc
                        v * d1⁻¹ * v⁻¹ = (d1⁻¹ * v) * v⁻¹ := by
                          rw [(hd1v.inv_left).symm.eq]
                        _ = d1⁻¹ := by simp [mul_assoc]
                    calc
                      (x * v * x⁻¹) * d1⁻¹ * (x * v * x⁻¹)⁻¹ =
                          (b * v) * d1⁻¹ * (b * v)⁻¹ := by rw [hxv_eq]
                      _ = b * (v * d1⁻¹ * v⁻¹) * b⁻¹ := by simp [mul_assoc]
                      _ = b * d1⁻¹ * b⁻¹ := by rw [hv_fix]
                      _ = d1⁻¹ := by
                        calc
                          b * d1⁻¹ * b⁻¹ = (d1⁻¹ * b) * b⁻¹ := by
                            rw [(hd1b.inv_left).symm.eq]
                          _ = d1⁻¹ := by simp [mul_assoc]
                  have hd2_conj_xu :
                      (x * u * x⁻¹) * d2⁻¹ * (x * u * x⁻¹)⁻¹ = d2⁻¹ := by
                    have hu_fix : u * d2⁻¹ * u⁻¹ = d2⁻¹ := by
                      calc
                        u * d2⁻¹ * u⁻¹ = (d2⁻¹ * u) * u⁻¹ := by
                          rw [(hd2u.inv_left).symm.eq]
                        _ = d2⁻¹ := by simp [mul_assoc]
                    calc
                      (x * u * x⁻¹) * d2⁻¹ * (x * u * x⁻¹)⁻¹ =
                          (a * u) * d2⁻¹ * (a * u)⁻¹ := by rw [hxu_eq]
                      _ = a * (u * d2⁻¹ * u⁻¹) * a⁻¹ := by simp [mul_assoc]
                      _ = a * d2⁻¹ * a⁻¹ := by rw [hu_fix]
                      _ = d2⁻¹ := by
                        calc
                          a * d2⁻¹ * a⁻¹ = (d2⁻¹ * a) * a⁻¹ := by
                            rw [(hd2a.inv_left).symm.eq]
                          _ = d2⁻¹ := by simp [mul_assoc]
                  have hc_eq_xd1 : ⁅a, b⁆ = ⁅x, d1⁆ := by
                    have haxBcomm : ⁅a, x⁆ ∈ Bcomm := by
                      exact Subgroup.commutator_mem_commutator haB hxB
                    have hax_x : Commute ⁅a, x⁆ x := by
                      exact
                        ((Subgroup.mem_centralizer_iff.mp (hBcomm_le_cent_B haxBcomm) x) hxB).symm
                    have hax_d1 : Commute ⁅a, x⁆ d1 := by
                      exact
                        ((Subgroup.mem_centralizer_iff.mp (hBcomm_le_cent_A haxBcomm) d1)
                          hd1A).symm
                    have hax_inv : ⁅a, x⁻¹⁆ = ⁅a, x⁆⁻¹ := by
                      rw [commutator_inv_right]
                      calc
                        x⁻¹ * ⁅a, x⁆⁻¹ * x = x⁻¹ * (x * ⁅a, x⁆⁻¹) := by
                          rw [(hax_x.inv_left).symm.eq, mul_assoc]
                        _ = ⁅a, x⁆⁻¹ := by simp
                    have hax_inv_v :
                        v * ⁅a, x⁆⁻¹ * v⁻¹ = ⁅a, x⁆⁻¹ := by
                      have haxv : Commute ⁅a, x⁆ v := by
                        exact
                          ((Subgroup.mem_centralizer_iff.mp (hBcomm_le_cent_A haxBcomm) v)
                            hvA).symm
                      calc
                        v * ⁅a, x⁆⁻¹ * v⁻¹ = (⁅a, x⁆⁻¹ * v) * v⁻¹ := by
                          rw [(haxv.inv_left).symm.eq]
                        _ = ⁅a, x⁆⁻¹ := by simp [mul_assoc]
                    calc
                      ⁅a, b⁆ = ⁅a, x * v * x⁻¹ * v⁻¹⁆ := by
                        dsimp [b]
                        simp [commutatorElement_def, mul_assoc]
                      _ = ⁅a, x * v * x⁻¹⁆ * d1⁻¹ := by
                        rw [commutator_mul_right]
                        calc
                          ⁅a, x * v * x⁻¹⁆ * (x * v * x⁻¹) * ⁅a, v⁻¹⁆ * (x * v * x⁻¹)⁻¹ =
                              ⁅a, x * v * x⁻¹⁆ *
                                ((x * v * x⁻¹) * ⁅a, v⁻¹⁆ * (x * v * x⁻¹)⁻¹) := by
                                  simp [mul_assoc]
                          _ = ⁅a, x * v * x⁻¹⁆ * d1⁻¹ := by
                                rw [hd1_inv_v, hd1_conj_xv]
                      _ = (⁅a, x⁆ * x * ⁅a, v * x⁻¹⁆ * x⁻¹) * d1⁻¹ := by
                        rw [show x * v * x⁻¹ = x * (v * x⁻¹) by simp [mul_assoc]]
                        rw [commutator_mul_right]
                      _ = (⁅a, x⁆ * x * (d1 * ⁅a, x⁆⁻¹) * x⁻¹) * d1⁻¹ := by
                        have hinner : ⁅a, v * x⁻¹⁆ = d1 * ⁅a, x⁆⁻¹ := by
                          rw [commutator_mul_right]
                          calc
                            ⁅a, v⁆ * v * ⁅a, x⁻¹⁆ * v⁻¹ = ⁅a, v⁆ * (v * ⁅a, x⁻¹⁆ * v⁻¹) := by
                              simp [mul_assoc]
                            _ = ⁅a, v⁆ * ⁅a, x⁆⁻¹ := by rw [hax_inv, hax_inv_v]
                            _ = d1 * ⁅a, x⁆⁻¹ := by rfl
                        rw [hinner]
                      _ = (x * d1 * x⁻¹) * d1⁻¹ := by
                        have hfix : ⁅a, x⁆ * d1 * ⁅a, x⁆⁻¹ = d1 := by
                          calc
                            ⁅a, x⁆ * d1 * ⁅a, x⁆⁻¹ = (d1 * ⁅a, x⁆) * ⁅a, x⁆⁻¹ := by
                              simp [hax_d1.eq, mul_assoc]
                            _ = d1 := by simp [commutatorElement_def,mul_assoc]
                        calc
                          (⁅a, x⁆ * x * (d1 * ⁅a, x⁆⁻¹) * x⁻¹) * d1⁻¹ =
                              (x * (⁅a, x⁆ * d1 * ⁅a, x⁆⁻¹) * x⁻¹) * d1⁻¹ := by
                                rw [hax_x.eq]
                                simp [mul_assoc]
                          _ = (x * d1 * x⁻¹) * d1⁻¹ := by rw [hfix]
                      _ = ⁅x, d1⁆ := by
                        simp [commutatorElement_def, mul_assoc]
                  have hc_eq_xd2 : ⁅b, a⁆ = ⁅x, d2⁆ := by
                    have hbxBcomm : ⁅b, x⁆ ∈ Bcomm := by
                      exact Subgroup.commutator_mem_commutator hbB hxB
                    have hbx_x : Commute ⁅b, x⁆ x := by
                      exact
                        ((Subgroup.mem_centralizer_iff.mp (hBcomm_le_cent_B hbxBcomm) x) hxB).symm
                    have hbx_d2 : Commute ⁅b, x⁆ d2 := by
                      exact
                        ((Subgroup.mem_centralizer_iff.mp (hBcomm_le_cent_A hbxBcomm) d2)
                          hd2A).symm
                    have hbx_inv : ⁅b, x⁻¹⁆ = ⁅b, x⁆⁻¹ := by
                      rw [commutator_inv_right]
                      calc
                        x⁻¹ * ⁅b, x⁆⁻¹ * x = x⁻¹ * (x * ⁅b, x⁆⁻¹) := by
                          rw [(hbx_x.inv_left).symm.eq, mul_assoc]
                        _ = ⁅b, x⁆⁻¹ := by simp
                    have hbx_inv_u :
                        u * ⁅b, x⁆⁻¹ * u⁻¹ = ⁅b, x⁆⁻¹ := by
                      have hbxu : Commute ⁅b, x⁆ u := by
                        exact
                          ((Subgroup.mem_centralizer_iff.mp (hBcomm_le_cent_A hbxBcomm) u)
                            huA).symm
                      calc
                        u * ⁅b, x⁆⁻¹ * u⁻¹ = (⁅b, x⁆⁻¹ * u) * u⁻¹ := by
                          rw [(hbxu.inv_left).symm.eq]
                        _ = ⁅b, x⁆⁻¹ := by simp [mul_assoc]
                    calc
                      ⁅b, a⁆ = ⁅b, x * u * x⁻¹ * u⁻¹⁆ := by
                        dsimp [a]
                        simp [commutatorElement_def, mul_assoc]
                      _ = ⁅b, x * u * x⁻¹⁆ * d2⁻¹ := by
                        rw [commutator_mul_right]
                        calc
                          ⁅b, x * u * x⁻¹⁆ * (x * u * x⁻¹) * ⁅b, u⁻¹⁆ * (x * u * x⁻¹)⁻¹ =
                              ⁅b, x * u * x⁻¹⁆ *
                                ((x * u * x⁻¹) * ⁅b, u⁻¹⁆ * (x * u * x⁻¹)⁻¹) := by
                                  simp [mul_assoc]
                          _ = ⁅b, x * u * x⁻¹⁆ * d2⁻¹ := by
                                rw [hd2_inv_u, hd2_conj_xu]
                      _ = (⁅b, x⁆ * x * ⁅b, u * x⁻¹⁆ * x⁻¹) * d2⁻¹ := by
                        rw [show x * u * x⁻¹ = x * (u * x⁻¹) by simp [mul_assoc]]
                        rw [commutator_mul_right]
                      _ = (⁅b, x⁆ * x * (d2 * ⁅b, x⁆⁻¹) * x⁻¹) * d2⁻¹ := by
                        have hinner : ⁅b, u * x⁻¹⁆ = d2 * ⁅b, x⁆⁻¹ := by
                          rw [commutator_mul_right]
                          calc
                            ⁅b, u⁆ * u * ⁅b, x⁻¹⁆ * u⁻¹ = ⁅b, u⁆ * (u * ⁅b, x⁻¹⁆ * u⁻¹) := by
                              simp [mul_assoc]
                            _ = ⁅b, u⁆ * ⁅b, x⁆⁻¹ := by rw [hbx_inv, hbx_inv_u]
                            _ = d2 * ⁅b, x⁆⁻¹ := by rfl
                        rw [hinner]
                      _ = (x * d2 * x⁻¹) * d2⁻¹ := by
                        have hfix : ⁅b, x⁆ * d2 * ⁅b, x⁆⁻¹ = d2 := by
                          calc
                            ⁅b, x⁆ * d2 * ⁅b, x⁆⁻¹ = (d2 * ⁅b, x⁆) * ⁅b, x⁆⁻¹ := by
                              simp [hbx_d2.eq, mul_assoc]
                            _ = d2 := by rw [mul_assoc, mul_inv_cancel, mul_one]
                        calc
                          (⁅b, x⁆ * x * (d2 * ⁅b, x⁆⁻¹) * x⁻¹) * d2⁻¹ =
                              (x * (⁅b, x⁆ * d2 * ⁅b, x⁆⁻¹) * x⁻¹) * d2⁻¹ := by
                                rw [hbx_x.eq]
                                simp [mul_assoc]
                          _ = (x * d2 * x⁻¹) * d2⁻¹ := by rw [hfix]
                      _ = ⁅x, d2⁆ := by
                        simp [commutatorElement_def, mul_assoc]
                  have hxd1_eq_hxd2 : ⁅x, d1⁆ = ⁅x, d2⁆ := by
                    calc
                      ⁅x, d1⁆ = ⁅x, (d1 / d2) * d2⁆ := by
                        simp [div_eq_mul_inv, mul_assoc]
                      _ = ⁅x, d1 / d2⁆ * (d1 / d2) * ⁅x, d2⁆ * (d1 / d2)⁻¹ := by
                        rw [commutator_mul_right]
                      _ = (d1 / d2) * ⁅x, d2⁆ * (d1 / d2)⁻¹ := by
                        rw [hxdiff_one]
                        simp
                      _ = ⁅x, d2⁆ := hconj_diff_xd2
                  have hcomm_eq_inv : ⁅a, b⁆ = ⁅a, b⁆⁻¹ := by
                    calc
                      ⁅a, b⁆ = ⁅x, d1⁆ := hc_eq_xd1
                      _ = ⁅x, d2⁆ := hxd1_eq_hxd2
                      _ = ⁅b, a⁆ := hc_eq_xd2.symm
                      _ = ⁅a, b⁆⁻¹ := by simp [commutatorElement_inv]
                  have hcomm_sq : ⁅a, b⁆ ^ 2 = 1 := by
                    calc
                      ⁅a, b⁆ ^ 2 = ⁅a, b⁆ * ⁅a, b⁆ := by simp [pow_two]
                      _ = ⁅a, b⁆ * ⁅a, b⁆⁻¹ := by nth_rw 2 [hcomm_eq_inv]
                      _ = 1 := by rw [mul_inv_cancel]
                  have habBcomm : ⁅a, b⁆ ∈ Bcomm := by
                    exact Subgroup.commutator_mem_commutator haB hbB
                  exact
                    rzj_eq_one_of_mem_pGroup_sq_eq_one
                      (G := G) (p := p) hpodd Bcomm hBcomm_p habBcomm hcomm_sq
                let M : Subgroup G := Subgroup.closure {g : G | ∃ v ∈ A, ⁅x, v⁆ = g}
                let C : Subgroup G := rzj_subgroupCentralizerIn' A M
                let Astar : Subgroup G := M ⊔ C
                have hM_le_D1 : M ≤ rzj_replacementCommChain B A 1 := by
                  dsimp [M]
                  rw [Subgroup.closure_le]
                  intro y hy
                  rcases hy with ⟨v, hvA, rfl⟩
                  have : ⁅B, A⁆ = rzj_replacementCommChain B A (0 + 1) := rfl
                  rw [this, rzj_replacementCommChain_succ, rzj_replacementCommChain_zero]
                  exact Subgroup.commutator_mem_commutator hxB hvA
                have hM_le_B : M ≤ B := hM_le_D1.trans (rzj_replacementCommChain_le_left B A 1)
                have hM_comm : IsMulCommutative M := by
                  dsimp [M]
                  exact Subgroup.isMulCommutative_closure
                    (k := {g : G | ∃ v ∈ A, ⁅x, v⁆ = g}) <| by
                      intro y hy z hz _
                      rcases hy with ⟨u, huA, rfl⟩
                      rcases hz with ⟨v, hvA, rfl⟩
                      exact commutatorElement_eq_one_iff_commute.mp (hgen_comm u huA v hvA)
                have hAstar :
                    Astar ∈ thompsonAbelianSubgroups (G := G) U := by
                  dsimp [Astar, C, M]
                  simpa using
                    (rzj_thompsonReplacement_base (G := G) (P := U)
                      (A := A) hA hxP hM_comm)
                have hAinfB_le_C : A ⊓ B ≤ C := by
                  intro y hy
                  dsimp [C, rzj_subgroupCentralizerIn']
                  refine ⟨?_, hy.1⟩
                  show y ∈ Subgroup.centralizer (M : Set G)
                  rw [Subgroup.mem_centralizer_iff]
                  intro m hmM
                  have hycent := hAinfB_cent_D1 hy
                  exact (Subgroup.mem_centralizer_iff.mp hycent m) (hM_le_D1 hmM)
                have hAinfB_le_AstarinfB : A ⊓ B ≤ Astar ⊓ B := by
                  intro y hy
                  exact ⟨(show C ≤ Astar from le_sup_right) (hAinfB_le_C hy), hy.2⟩
                have hxu_mem_M : ⁅x, u⁆ ∈ M := by
                  dsimp [M]
                  exact Subgroup.subset_closure ⟨u, huA, rfl⟩
                have hxu_mem_B : ⁅x, u⁆ ∈ B := hM_le_B hxu_mem_M
                have hxu_not_mem_A : ⁅x, u⁆ ∉ A := by
                  intro hxuA
                  have hxu_centA : ⁅x, u⁆ ∈ Subgroup.centralizer (A : Set G) := by
                    exact
                      ((Subgroup.le_centralizer_iff_isMulCommutative (K := A)).2 hA.2.1)
                        hxuA
                  exact hxu_not_centA hxu_centA
                have hAstar_lt : A ⊓ B < Astar ⊓ B := by
                  have hne : A ⊓ B ≠ Astar ⊓ B := by
                    intro hEq
                    have hxu_mem_AstarB : ⁅x, u⁆ ∈ Astar ⊓ B := by
                      exact ⟨(show M ≤ Astar from le_sup_left) hxu_mem_M, hxu_mem_B⟩
                    have hxu_mem_AB : ⁅x, u⁆ ∈ A ⊓ B := by
                      simpa [hEq] using hxu_mem_AstarB
                    exact hxu_not_mem_A hxu_mem_AB.1
                  exact lt_of_le_of_ne hAinfB_le_AstarinfB hne
                have hM_le_P : M ≤ U := hM_le_B.trans hB_le_P
                have hM_comm2 : ⁅⁅M, A⁆, A⁆ = ⊥ := by
                  have hMA_le_D2 : ⁅M, A⁆ ≤ rzj_replacementCommChain B A 2 := by
                    rw [rzj_replacementCommChain_succ]
                    exact Subgroup.commutator_mono hM_le_D1 le_rfl
                  have hMA_le_A : ⁅M, A⁆ ≤ A := hMA_le_D2.trans hD2_le_A
                  exact
                    (Subgroup.commutator_eq_bot_iff_le_centralizer).2
                      (hMA_le_A.trans
                        ((Subgroup.le_centralizer_iff_isMulCommutative (K := A)).2 hA.2.1))
                have hM_le_norm_A : M ≤ Subgroup.normalizer (A : Set G) := by
                  exact
                    (rzj_thompsonAbelianSubgroups_normalizer_iff_commutator_eq_bot
                      (G := G) (P := U) (A := A) (B := M) hA hM_le_P).2
                      hM_comm2
                have hAstar_le_norm_A : Astar ≤ Subgroup.normalizer (A : Set G) := by
                  rw [sup_le_iff]
                  constructor
                  · exact hM_le_norm_A
                  · trans A
                    · dsimp [C, rzj_subgroupCentralizerIn']
                      simp
                    · exact Subgroup.le_normalizer
                exact ⟨Astar, hAstar, hAstar_lt, hAstar_le_norm_A⟩
              · have hnA_succ_lt : nA + 1 < rA := hnA_succ_lt_rA hDnA_succ_bot
                have hrA_gt_two : 2 < rA := by
                  omega
                have hDrA1_ne_bot : rzj_replacementCommChain B A (rA - 1) ≠ ⊥ := by
                  intro hbot
                  have hle : rA ≤ rA - 1 := hrA_min (rA - 1) hbot
                  omega
                have hDrA2_not_cent :
                    ¬ rzj_replacementCommChain B A (rA - 2) ≤ Subgroup.centralizer (A : Set G) := by
                  intro hcent
                  have hsub : rA - 1 = (rA - 2) + 1 := by
                    omega
                  have hbot : rzj_replacementCommChain B A (rA - 1) = ⊥ := by
                    rw [hsub, rzj_replacementCommChain_succ]
                    exact (Subgroup.commutator_eq_bot_iff_le_centralizer).2 hcent
                  exact hDrA1_ne_bot hbot
                have hxu_exists :
                    ∃ x ∈ rzj_replacementCommChain B A (rA - 3),
                      ∃ u ∈ A, ⁅x, u⁆ ∉ Subgroup.centralizer (A : Set G) := by
                  by_contra hno
                  apply hDrA2_not_cent
                  have hsub : rA - 2 = (rA - 3) + 1 := by
                    omega
                  rw [hsub, rzj_replacementCommChain_succ]
                  refine (Subgroup.commutator_le).2 ?_
                  intro x hx u hu
                  by_contra hnot
                  exact hno ⟨x, hx, u, hu, hnot⟩
                obtain ⟨x, hxDrA3, u, huA, hxu_not_centA⟩ := hxu_exists
                let M : Subgroup G := Subgroup.closure {g : G | ∃ v ∈ A, ⁅x, v⁆ = g}
                let C : Subgroup G := rzj_subgroupCentralizerIn' A M
                let Astar : Subgroup G := M ⊔ C
                have hxB' : x ∈ B := (rzj_replacementCommChain_le_left B A (rA - 3)) hxDrA3
                have hxP : x ∈ U := hB_le_P hxB'
                have hM_le_DrA2 : M ≤ rzj_replacementCommChain B A (rA - 2) := by
                  dsimp [M]
                  rw [Subgroup.closure_le]
                  intro y hy
                  rcases hy with ⟨v, hvA, rfl⟩
                  have hsub : rA - 2 = (rA - 3) + 1 := by
                    omega
                  rw [hsub, rzj_replacementCommChain_succ]
                  exact Subgroup.commutator_mem_commutator hxDrA3 hvA
                have hM_le_B : M ≤ B :=
                  hM_le_DrA2.trans (rzj_replacementCommChain_le_left B A (rA - 2))
                have hnA_le_rA_sub2 : nA ≤ rA - 2 := by
                  omega
                have hM_le_DnA : M ≤ rzj_replacementCommChain B A nA :=
                  hM_le_DrA2.trans (rzj_replacementCommChain_antitone B A hnA_le_rA_sub2)
                have hM_comm : IsMulCommutative M := by
                  refine ⟨?_⟩
                  exact ⟨fun y z => by
                    apply Subtype.ext
                    simpa using
                      (setLike_mul_comm
                        (s := rzj_replacementCommChain B A nA)
                        (hM_le_DnA y.2) (hM_le_DnA z.2))⟩
                have hAstar :
                    Astar ∈ thompsonAbelianSubgroups (G := G) U := by
                  dsimp [Astar, C, M]
                  simpa using
                    (rzj_thompsonReplacement_base (G := G) (P := U)
                      (A := A) hA hxP hM_comm)
                have hAinfB_le_C : A ⊓ B ≤ C := by
                  intro y hy
                  dsimp [C, rzj_subgroupCentralizerIn']
                  refine ⟨?_, hy.1⟩
                  show y ∈ Subgroup.centralizer (M : Set G)
                  rw [Subgroup.mem_centralizer_iff]
                  intro m hmM
                  have hycent :=
                    hAinfB_cent_Di (rA - 2) (by omega : 1 ≤ rA - 2) hy
                  exact (Subgroup.mem_centralizer_iff.mp hycent m) (hM_le_DrA2 hmM)
                have hAinfB_le_AstarinfB : A ⊓ B ≤ Astar ⊓ B := by
                  intro y hy
                  exact ⟨(show C ≤ Astar from le_sup_right) (hAinfB_le_C hy), hy.2⟩
                have hxu_mem_M : ⁅x, u⁆ ∈ M := by
                  dsimp [M]
                  exact Subgroup.subset_closure ⟨u, huA, rfl⟩
                have hxu_mem_B : ⁅x, u⁆ ∈ B := hM_le_B hxu_mem_M
                have hxu_not_mem_A : ⁅x, u⁆ ∉ A := by
                  intro hxuA
                  have hxu_centA : ⁅x, u⁆ ∈ Subgroup.centralizer (A : Set G) := by
                    exact
                      ((Subgroup.le_centralizer_iff_isMulCommutative (K := A)).2 hA.2.1)
                        hxuA
                  exact hxu_not_centA hxu_centA
                have hAstar_lt : A ⊓ B < Astar ⊓ B := by
                  have hne : A ⊓ B ≠ Astar ⊓ B := by
                    intro hEq
                    have hxu_mem_AstarB : ⁅x, u⁆ ∈ Astar ⊓ B := by
                      exact ⟨(show M ≤ Astar from le_sup_left) hxu_mem_M, hxu_mem_B⟩
                    have hxu_mem_AB : ⁅x, u⁆ ∈ A ⊓ B := by
                      simpa [hEq] using hxu_mem_AstarB
                    exact hxu_not_mem_A hxu_mem_AB.1
                  exact lt_of_le_of_ne hAinfB_le_AstarinfB hne
                have hDrA1_le_A : rzj_replacementCommChain B A (rA - 1) ≤ A := by
                  have hsucc : rzj_replacementCommChain B A ((rA - 1) + 1) = ⊥ := by
                    have hsub : (rA - 1) + 1 = rA := by
                      omega
                    simpa [hsub] using hrA_bot
                  exact
                    rzj_replacementCommChain_le_of_succ_eq_bot
                      (G := G) (P := U) (B := B) (A := A)
                      hA hB_le_P hsucc
                have hM_le_P : M ≤ U := hM_le_B.trans hB_le_P
                have hM_comm2 : ⁅⁅M, A⁆, A⁆ = ⊥ := by
                  have hMA_le_DrA1 : ⁅M, A⁆ ≤ rzj_replacementCommChain B A (rA - 1) := by
                    have hsub : rA - 1 = (rA - 2) + 1 := by
                      omega
                    rw [hsub, rzj_replacementCommChain_succ]
                    exact Subgroup.commutator_mono hM_le_DrA2 le_rfl
                  have hMA_le_A : ⁅M, A⁆ ≤ A := hMA_le_DrA1.trans hDrA1_le_A
                  exact
                    (Subgroup.commutator_eq_bot_iff_le_centralizer).2
                      (hMA_le_A.trans
                        ((Subgroup.le_centralizer_iff_isMulCommutative (K := A)).2 hA.2.1))
                have hM_le_norm_A : M ≤ Subgroup.normalizer (A : Set G) := by
                  exact
                    (rzj_thompsonAbelianSubgroups_normalizer_iff_commutator_eq_bot
                      (G := G) (P := U) (A := A) (B := M) hA hM_le_P).2
                      hM_comm2
                have hAstar_le_norm_A : Astar ≤ Subgroup.normalizer (A : Set G) := by
                  rw [sup_le_iff]
                  constructor
                  · exact hM_le_norm_A
                  · trans A
                    · dsimp [C, rzj_subgroupCentralizerIn']
                      simp
                    · exact Subgroup.le_normalizer
                exact ⟨Astar, hAstar, hAstar_lt, hAstar_le_norm_A⟩)
          refine ⟨A, hA, ?_, ?_⟩
          · exact
              (rzj_thompsonAbelianSubgroups_normalizer_iff_commutator_eq_bot
                (G := G) (P := U) (A := A) (B := B) hA hB_le_P).1 hB_norm_A
          · have hP_le_norm_Z : U ≤ Subgroup.normalizer (Z : Set G) := by
              exact
                Subgroup.le_normalizer.trans
                  (rzj_normalizer_le_normalizer_thompsonCenter (G := G) U)
            have hA_le_norm_Z : A ≤ Subgroup.normalizer (Z : Set G) := hA.1.trans hP_le_norm_Z
            have hA_le_norm_B : A ≤ Subgroup.normalizer (B : Set G) := by
              rw [Subgroup.normalizer_eq_top (H := B)]
              exact le_top
            have hA_le_norm_B0 : A ≤ Subgroup.normalizer (B0 : Set G) := by
              intro a ha
              simpa [B0] using
                (Subgroup.inf_normalizer_le_normalizer_inf (H := B) (K := Z)
                  ⟨hA_le_norm_B ha, hA_le_norm_Z ha⟩)
            have hpCore_quot_bot' : pCore p (G ⧸ L) = ⊥ := by
              let : L.Normal := by
                dsimp [L]
                infer_instance
              let K : Subgroup G := Subgroup.comap qL (pCore p (G ⧸ L))
              have hK_normal : K.Normal := by
                dsimp [K, qL]
                infer_instance
              have hPK_map : (U ⊓ K).map qL = pCore p (G ⧸ L) := by
                apply le_antisymm
                · have hK_map : K.map qL = pCore p (G ⧸ L) := by
                    dsimp [K]
                    simpa using
                      (Subgroup.map_comap_eq_self_of_surjective
                        (f := qL) (h := QuotientGroup.mk'_surjective L) (H := pCore p (G ⧸ L)))
                  have hmap_le : (U ⊓ K).map qL ≤ K.map qL :=
                    Subgroup.map_mono (f := qL) inf_le_right
                  simpa [hK_map] using hmap_le
                · intro x hx
                  have hxPmap : x ∈ (U.map qL) := hcov hx
                  rcases Subgroup.mem_map.mp hxPmap with ⟨y, hyP, rfl⟩
                  have hyK : y ∈ K := by
                    simpa [K] using hx
                  exact Subgroup.mem_map.mpr ⟨y, ⟨hyP, hyK⟩, rfl⟩
              have hL_le_K : L ≤ K := by
                dsimp [K, qL]
                simpa [QuotientGroup.ker_mk'] using
                  (Subgroup.ker_le_comap (f := QuotientGroup.mk' L) (H := pCore p (G ⧸ L)))
              have hK_eq : K = L ⊔ (U ⊓ K) := by
                apply le_antisymm
                · intro x hxK
                  have hxmap : qL x ∈ pCore p (G ⧸ L) := hxK
                  rw [← hPK_map] at hxmap
                  rcases Subgroup.mem_map.mp hxmap with ⟨y, hyPK, hxy⟩
                  have hxy1 : qL (x * y⁻¹) = 1 := by
                    rw [map_mul, map_inv, hxy]
                    simp
                  have hker : x * y⁻¹ ∈ L := by
                    have hker' : x * y⁻¹ ∈ qL.ker := by
                      simpa [MonoidHom.mem_ker] using hxy1
                    simpa [qL, QuotientGroup.ker_mk'] using hker'
                  have hxsup : x * y⁻¹ ∈ L ⊔ (U ⊓ K) := by
                    exact Subgroup.mem_sup_left hker
                  have hysup : y ∈ L ⊔ (U ⊓ K) := by
                    exact Subgroup.mem_sup_right hyPK
                  simpa [mul_assoc] using
                    (Subgroup.mul_mem (L ⊔ (U ⊓ K)) hxsup hysup)
                · exact sup_le hL_le_K inf_le_right
              have hL_le_norm_B0 : L ≤ Subgroup.normalizer (B0 : Set G) := by
                simpa [L] using (Subgroup.normalizer (B0 : Set G)).normalCore_le
              have hPcapK_le_norm_B0 : U ⊓ K ≤ Subgroup.normalizer (B0 : Set G) := by
                intro x hx
                have hxB : x ∈ Subgroup.normalizer (B : Set G) := by
                  rw [Subgroup.normalizer_eq_top (H := B)]
                  simp
                have hxZ : x ∈ Subgroup.normalizer (Z : Set G) := hP_le_norm_Z hx.1
                simpa [B0] using
                  (Subgroup.inf_normalizer_le_normalizer_inf (H := B) (K := Z) ⟨hxB, hxZ⟩)
              have hK_le_norm_B0 : K ≤ Subgroup.normalizer (B0 : Set G) := by
                rw [hK_eq]
                exact sup_le hL_le_norm_B0 hPcapK_le_norm_B0
              have hK_le_L : K ≤ L := by
                let : K.Normal := hK_normal
                simpa [L] using
                  (Subgroup.normal_le_normalCore
                    (H := Subgroup.normalizer (B0 : Set G)) (N := K)).2 hK_le_norm_B0
              have hK_eq_L : K = L := le_antisymm hK_le_L hL_le_K
              have hK_map : K.map qL = pCore p (G ⧸ L) := by
                dsimp [K]
                simpa using
                  (Subgroup.map_comap_eq_self_of_surjective
                    (f := qL) (h := QuotientGroup.mk'_surjective L) (H := pCore p (G ⧸ L)))
              have hKmap_bot : K.map qL = ⊥ := by
                apply (Subgroup.map_eq_bot_iff (H := K) (f := qL)).2
                simp [qL, QuotientGroup.ker_mk', hK_eq_L]
              exact hK_map.symm.trans hKmap_bot
            let N : Subgroup G := Subgroup.normalizer (B : Set G)
            let C : Subgroup G := Subgroup.centralizer (B : Set G)
            have hN_eq_top : N = ⊤ := by
              dsimp [N]
              exact Subgroup.normalizer_eq_top (H := B)
            have hA_p : IsPGroup p A := hU.to_le hA.1
            have hA_le_N : A ≤ N := by
              rw [hN_eq_top]
              exact le_top
            have hC_le_L : C ≤ L := by
              have hC_le_cent_B0 : C ≤ Subgroup.centralizer (B0 : Set G) := by
                exact Subgroup.centralizer_le
                  (show (B0 : Set G) ⊆ (B : Set G) from fun _ hx => hx.1)
              have hC_le_norm_B0 : C ≤ Subgroup.normalizer (B0 : Set G) := by
                exact hC_le_cent_B0.trans (centralizer_le_normalizer (R := B0))
              let : C.Normal := by
                dsimp [C]
                exact Subgroup.normal_centralizer (H := B)
              simpa [L] using
                (Subgroup.normal_le_normalCore
                  (H := Subgroup.normalizer (B0 : Set G)) (N := C)).2 hC_le_norm_B0
            have hstableA :
                ((A.subgroupOf N).map (QuotientGroup.mk' (C.subgroupOf N))) ≤
                  pCore p (N ⧸ C.subgroupOf N) := by
              have hA' := hstable B A hBnormal hBp hBne hA.1
                ((rzj_thompsonAbelianSubgroups_normalizer_iff_commutator_eq_bot
                  (G := G) (P := U) (A := A) (B := B) hA hB_le_P).1 hB_norm_A)
              rintro _ ⟨a, ha, rfl⟩
              obtain ⟨n, hn', hna⟩ := hA' ha
              have hna' : n = a := Subtype.ext hna
              rw [← hna']
              exact hn'
            have hNmap_top : N.map qL = ⊤ := by
              rw [hN_eq_top]
              simpa [qL] using
                (Subgroup.map_top_of_surjective qL (QuotientGroup.mk'_surjective L))
            have hqN_surj : Function.Surjective (qL.comp N.subtype) := by
              intro y
              have hy : y ∈ N.map qL := by
                rw [hNmap_top]
                exact Subgroup.mem_top y
              rcases Subgroup.mem_map.mp hy with ⟨n, hn, hqy⟩
              exact ⟨Subtype.mk n hn, hqy⟩
            have hCN : C ≤ N := by
              simpa [N, C] using (centralizer_le_normalizer (G := G) B)
            let : (C.subgroupOf N).Normal := by
              exact
                (Subgroup.normal_subgroupOf_iff_le_normalizer
                  (H := C) (K := N) hCN).2
                  (by simpa [N, C] using CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer (X := G) B)
            let phi : N ⧸ C.subgroupOf N →* G ⧸ L :=
              QuotientGroup.lift (C.subgroupOf N) (qL.comp N.subtype) (by
                intro c hc
                exact (QuotientGroup.eq_one_iff (N := L) (x := (c : G))).2 (hC_le_L hc))
            have hphi_surj : Function.Surjective phi := by
              intro y
              rcases hqN_surj y with ⟨n, hnq⟩
              refine ⟨QuotientGroup.mk' (C.subgroupOf N) n, ?_⟩
              change qL (n : G) = y
              exact hnq
            have hAimage_bot :
                (((A.subgroupOf N).map (QuotientGroup.mk' (C.subgroupOf N))).map phi) = ⊥ := by
              apply bot_unique
              calc
                (((A.subgroupOf N).map (QuotientGroup.mk' (C.subgroupOf N))).map phi) ≤
                    (pCore p (N ⧸ C.subgroupOf N)).map phi := by
                      exact Subgroup.map_mono hstableA
                _ ≤ pCore p (G ⧸ L) := by
                      exact rzj_pCore_map_le_pCore_of_surjective (G := N ⧸ C.subgroupOf N)
                        (p := p) phi hphi_surj
                _ = ⊥ := hpCore_quot_bot'
            intro a ha
            have haN : a ∈ N := hA_le_N ha
            have haSub : (Subtype.mk a haN : N) ∈ A.subgroupOf N := ha
            have haMap :
                QuotientGroup.mk' (C.subgroupOf N) (Subtype.mk a haN) ∈
                  (A.subgroupOf N).map (QuotientGroup.mk' (C.subgroupOf N)) :=
              Subgroup.mem_map_of_mem (QuotientGroup.mk' (C.subgroupOf N)) haSub
            have hphi_mem :
                phi (QuotientGroup.mk' (C.subgroupOf N) (Subtype.mk a haN)) ∈
                  (((A.subgroupOf N).map (QuotientGroup.mk' (C.subgroupOf N))).map phi) :=
              Subgroup.mem_map_of_mem phi haMap
            have hphi_eq : phi (QuotientGroup.mk' (C.subgroupOf N) (Subtype.mk a haN)) = 1 := by
              have :
                  phi (QuotientGroup.mk' (C.subgroupOf N) (Subtype.mk a haN)) ∈
                    (⊥ : Subgroup (G ⧸ L)) := by
                simpa [hAimage_bot] using hphi_mem
              simpa using this
            have haq : qL a = 1 := by
              change qL a = 1 at hphi_eq
              exact hphi_eq
            exact (QuotientGroup.eq_one_iff (N := L) (x := a)).1 haq
        have hB_comm : IsMulCommutative B := by
          obtain ⟨A, hA, hcomm2, hA_le_L⟩ := hA_exists
          have hB_norm_A : B ≤ Subgroup.normalizer (A : Set G) := by
            exact
              (rzj_thompsonAbelianSubgroups_normalizer_iff_commutator_eq_bot
                (G := G) hA hB_le_P).2 hcomm2
          let R : Subgroup G := U ⊓ L
          let X : Subgroup G := thompsonCenter (G := G) R
          have hA_le_R : A ≤ R := by
            intro x hx
            exact ⟨hA.1 hx, hA_le_L hx⟩
          have hZ_le_A : Z ≤ A := rzj_thompsonCenter_le_of_mem hA
          have hZ_le_X : Z ≤ X := by
            exact
              rzj_thompsonCenter_le_of_mem_thompsonAbelianSubgroups
                (G := G) (P := U) (R := R) inf_le_left hA hZ_le_A hA_le_R
          have hB0_le_X : B0 ≤ X := by
            intro x hx
            exact hZ_le_X hx.2
          let : L.Normal := by
            dsimp [L]
            infer_instance
          have hFr : Subgroup.normalizer (R : Set G) ⊔ L = ⊤ := by
            obtain ⟨S, hS_map⟩ := hsyl
            simpa [R, hS_map] using (Sylow.normalizer_sup_eq_top (p := p) (N := L) S)
          have hL_le_norm_B0 : L ≤ Subgroup.normalizer (B0 : Set G) := by
            simpa [L] using (Subgroup.normalizer (B0 : Set G)).normalCore_le
          have hconj_B0_le_X : Group.conjugatesOfSet (B0 : Set G) ⊆ X := by
            intro y hy
            rcases Group.mem_conjugatesOfSet_iff.mp hy with ⟨x, hx, hxy⟩
            rcases isConj_iff.mp hxy with ⟨g, rfl⟩
            have hg : g ∈ Subgroup.normalizer (R : Set G) ⊔ L := by
              rw [hFr]
              exact Subgroup.mem_top g
            rcases
                (Subgroup.mem_sup_of_normal_right
                  (s := Subgroup.normalizer (R : Set G)) (t := L) (x := g)).1 hg with
              ⟨n, hnR, l, hlL, rfl⟩
            have hlB0 : l ∈ Subgroup.normalizer (B0 : Set G) := hL_le_norm_B0 hlL
            have hlx : l * x * l⁻¹ ∈ X := by
              exact hB0_le_X ((Subgroup.mem_normalizer_iff.mp hlB0 _).1 hx)
            have hnX : n ∈ Subgroup.normalizer (X : Set G) := by
              simpa [X] using (rzj_normalizer_le_normalizer_thompsonCenter (G := G) R) hnR
            have hnx : n * (l * x * l⁻¹) * n⁻¹ ∈ X :=
              (Subgroup.mem_normalizer_iff.mp hnX _).1 hlx
            simpa [mul_assoc] using hnx
          have hB_le_X : B ≤ X := by
            rw [← hB1_eq_B]
            dsimp [B1]
            rw [Subgroup.normalClosure, Subgroup.closure_le]
            exact hconj_B0_le_X
          let : IsMulCommutative X := rzj_thompsonCenter_isMulCommutative (G := G) R
          refine (Subgroup.le_centralizer_iff_isMulCommutative (K := B)).1 ?_
          intro x hx
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          simpa using
            (setLike_mul_comm (s := X) (hB_le_X hy) (hB_le_X hx))
        have hpCore_quot_bot : pCore p (G ⧸ L) = ⊥ := by
          let : L.Normal := by
            dsimp [L]
            infer_instance
          let K : Subgroup G := Subgroup.comap qL (pCore p (G ⧸ L))
          have hK_normal : K.Normal := by
            dsimp [K, qL]
            infer_instance
          have hPK_map : (U ⊓ K).map qL = pCore p (G ⧸ L) := by
            apply le_antisymm
            · have hK_map : K.map qL = pCore p (G ⧸ L) := by
                dsimp [K]
                simpa using
                  (Subgroup.map_comap_eq_self_of_surjective
                    (f := qL) (h := QuotientGroup.mk'_surjective L) (H := pCore p (G ⧸ L)))
              have hmap_le : (U ⊓ K).map qL ≤ K.map qL :=
                Subgroup.map_mono (f := qL) inf_le_right
              simpa [hK_map] using hmap_le
            · intro x hx
              have hxPmap : x ∈ (U.map qL) := hcov hx
              rcases Subgroup.mem_map.mp hxPmap with ⟨y, hyP, rfl⟩
              have hyK : y ∈ K := by
                simpa [K] using hx
              exact Subgroup.mem_map.mpr ⟨y, ⟨hyP, hyK⟩, rfl⟩
          have hL_le_K : L ≤ K := by
            dsimp [K, qL]
            simpa [QuotientGroup.ker_mk'] using
              (Subgroup.ker_le_comap (f := QuotientGroup.mk' L) (H := pCore p (G ⧸ L)))
          have hK_eq : K = L ⊔ (U ⊓ K) := by
            apply le_antisymm
            · intro x hxK
              have hxmap : qL x ∈ pCore p (G ⧸ L) := hxK
              rw [← hPK_map] at hxmap
              rcases Subgroup.mem_map.mp hxmap with ⟨y, hyPK, hxy⟩
              have hxy1 : qL (x * y⁻¹) = 1 := by
                rw [map_mul, map_inv, hxy]
                simp
              have hker : x * y⁻¹ ∈ L := by
                have hker' : x * y⁻¹ ∈ qL.ker := by
                  simpa [MonoidHom.mem_ker] using hxy1
                simpa [qL, QuotientGroup.ker_mk'] using hker'
              have hxsup : x * y⁻¹ ∈ L ⊔ (U ⊓ K) := by
                exact Subgroup.mem_sup_left hker
              have hysup : y ∈ L ⊔ (U ⊓ K) := by
                exact Subgroup.mem_sup_right hyPK
              simpa [mul_assoc] using (Subgroup.mul_mem (L ⊔ (U ⊓ K)) hxsup hysup)
            · exact sup_le hL_le_K inf_le_right
          have hL_le_norm_B0 : L ≤ Subgroup.normalizer (B0 : Set G) := by
            simpa [L] using (Subgroup.normalizer (B0 : Set G)).normalCore_le
          have hPcapK_le_norm_B0 : U ⊓ K ≤ Subgroup.normalizer (B0 : Set G) := by
            intro x hx
            have hxB : x ∈ Subgroup.normalizer (B : Set G) := by
              rw [Subgroup.normalizer_eq_top (H := B)]
              simp
            have hP_le_norm_Z : U ≤ Subgroup.normalizer (Z : Set G) := by
              exact (Subgroup.le_normalizer (H := U)).trans
                (by simpa [Z] using (rzj_normalizer_le_normalizer_thompsonCenter (G := G) U))
            have hxZ : x ∈ Subgroup.normalizer (Z : Set G) := hP_le_norm_Z hx.1
            simpa [B0] using
              (Subgroup.inf_normalizer_le_normalizer_inf (H := B) (K := Z) ⟨hxB, hxZ⟩)
          have hK_le_norm_B0 : K ≤ Subgroup.normalizer (B0 : Set G) := by
            rw [hK_eq]
            exact sup_le hL_le_norm_B0 hPcapK_le_norm_B0
          have hK_le_L : K ≤ L := by
            let : K.Normal := hK_normal
            simpa [L] using
              (Subgroup.normal_le_normalCore
                (H := Subgroup.normalizer (B0 : Set G)) (N := K)).2 hK_le_norm_B0
          have hK_eq_L : K = L := le_antisymm hK_le_L hL_le_K
          have hK_map : K.map qL = pCore p (G ⧸ L) := by
            dsimp [K]
            simpa using
              (Subgroup.map_comap_eq_self_of_surjective
                (f := qL) (h := QuotientGroup.mk'_surjective L) (H := pCore p (G ⧸ L)))
          have hKmap_bot : K.map qL = ⊥ := by
            apply (Subgroup.map_eq_bot_iff (H := K) (f := qL)).2
            simp [qL, QuotientGroup.ker_mk', hK_eq_L]
          exact hK_map.symm.trans hKmap_bot
        have hJ_not_le_L :
            ¬ thompsonSubgroup (G := G) U ≤ L := by
          let : L.Normal := by
            dsimp [L]
            infer_instance
          intro hJ_le_L
          let R : Subgroup G := U ⊓ L
          have hJ_le_R : thompsonSubgroup (G := G) U ≤ R := by
            intro x hx
            exact ⟨rzj_thompsonSubgroup_le (G := G) U hx, hJ_le_L hx⟩
          have hZ_eq_R : thompsonCenter (G := G) R = Z := by
            simpa [Z, R] using
              (rzj_thompsonCenter_eq_of_le (G := G) (P := U) (R := R)
                inf_le_left hJ_le_R)
          have hFr : Subgroup.normalizer (R : Set G) ⊔ L = ⊤ := by
            obtain ⟨S, hS_map⟩ := hsyl
            simpa [R, hS_map] using (Sylow.normalizer_sup_eq_top (p := p) (N := L) S)
          have hL_le_norm_B0 : L ≤ Subgroup.normalizer (B0 : Set G) := by
            simpa [L] using (Subgroup.normalizer (B0 : Set G)).normalCore_le
          have hB0_normal' : B0.Normal := by
            apply (Subgroup.normalizer_eq_top_iff).mp
            apply top_le_iff.mp
            rw [← hFr]
            intro g hg
            rcases
                (Subgroup.mem_sup_of_normal_right
                  (s := Subgroup.normalizer (R : Set G)) (t := L) (x := g)).1 hg with
              ⟨n, hnR, l, hlL, rfl⟩
            have hnZ :
                n ∈ Subgroup.normalizer (Z : Set G) := by
              have hnTc :
                  n ∈ Subgroup.normalizer (thompsonCenter (G := G) R : Set G) :=
                (rzj_normalizer_le_normalizer_thompsonCenter (G := G) R) hnR
              simpa [hZ_eq_R] using hnTc
            have hnB :
                n ∈ Subgroup.normalizer (B : Set G) := by
              rw [Subgroup.normalizer_eq_top (H := B)]
              simp
            have hnB0 :
                n ∈ Subgroup.normalizer (B0 : Set G) := by
              simpa [B0] using
                (Subgroup.inf_normalizer_le_normalizer_inf (H := B) (K := Z) ⟨hnB, hnZ⟩)
            exact (Subgroup.normalizer (B0 : Set G)).mul_mem hnB0 (hL_le_norm_B0 hlL)
          exact hB0_not_normal hB0_normal'
        have hA1_exists :
            ∃ A1 : Subgroup G,
              A1 ∈ thompsonAbelianSubgroups (G := G) U ∧
                ¬ A1 ≤ L := by
          by_contra hA1_not_exists
          apply hJ_not_le_L
          refine sSup_le ?_
          intro A hA
          by_contra hA_not_le_L
          exact hA1_not_exists ⟨A, hA, hA_not_le_L⟩
        let Sbad : Set (Subgroup G) :=
          {A : Subgroup G |
            A ∈ thompsonAbelianSubgroups (G := G) U ∧ ¬ A ≤ L}
        have hSbad_nonempty : Sbad.Nonempty := by
          rcases hA1_exists with ⟨A1, hA1, hA1_not_le_L⟩
          exact ⟨A1, hA1, hA1_not_le_L⟩
        have hSbad_finite : Sbad.Finite := Set.toFinite Sbad
        obtain ⟨A1, hA1max⟩ :=
          hSbad_finite.exists_maximalFor (f := fun A : Subgroup G => Nat.card ↥(A ⊓ B))
            Sbad hSbad_nonempty
        have hA1Sbad : A1 ∈ Sbad := hA1max.prop
        have hA1 : A1 ∈ thompsonAbelianSubgroups (G := G) U := hA1Sbad.1
        have hA1_not_le_L : ¬ A1 ≤ L := hA1Sbad.2
        have htriple_ne_bot : ⁅⁅B, A1⁆, A1⁆ ≠ ⊥ := by
          intro htriple_bot
          let N : Subgroup G := Subgroup.normalizer (B : Set G)
          let C : Subgroup G := Subgroup.centralizer (B : Set G)
          have hN_eq_top : N = ⊤ := by
            dsimp [N]
            exact Subgroup.normalizer_eq_top (H := B)
          have hA1_p : IsPGroup p A1 := hU.to_le hA1.1
          have hA1_le_N : A1 ≤ N := by
            rw [hN_eq_top]
            exact le_top
          have hC_le_L : C ≤ L := by
            have hC_le_cent_B0 : C ≤ Subgroup.centralizer (B0 : Set G) := by
              exact Subgroup.centralizer_le (show (B0 : Set G) ⊆ (B : Set G) from fun _ hx => hx.1)
            have hC_le_norm_B0 : C ≤ Subgroup.normalizer (B0 : Set G) := by
              exact hC_le_cent_B0.trans (centralizer_le_normalizer (R := B0))
            let : C.Normal := by
              dsimp [C]
              exact Subgroup.normal_centralizer (H := B)
            simpa [L] using
              (Subgroup.normal_le_normalCore
                (H := Subgroup.normalizer (B0 : Set G)) (N := C)).2 hC_le_norm_B0
          have hstableA1 :
              ((A1.subgroupOf N).map (QuotientGroup.mk' (C.subgroupOf N))) ≤
                pCore p (N ⧸ C.subgroupOf N) := by
            have hA' := hstable B A1 hBnormal hBp hBne hA1.1 htriple_bot
            rintro _ ⟨a, ha, rfl⟩
            obtain ⟨n, hn', hna⟩ := hA' ha
            have hna' : n = a := Subtype.ext hna
            rw [← hna']
            exact hn'
          have hNmap_top : N.map qL = ⊤ := by
            rw [hN_eq_top]
            simpa [qL] using
              (Subgroup.map_top_of_surjective qL (QuotientGroup.mk'_surjective L))
          have hqN_surj : Function.Surjective (qL.comp N.subtype) := by
            intro y
            have hy : y ∈ N.map qL := by
              rw [hNmap_top]
              exact Subgroup.mem_top y
            rcases Subgroup.mem_map.mp hy with ⟨n, hn, hqy⟩
            exact ⟨Subtype.mk n hn, hqy⟩
          have hCN : C ≤ N := by
            simpa [N, C] using (centralizer_le_normalizer (G := G) B)
          let : (C.subgroupOf N).Normal := by
            exact
              (Subgroup.normal_subgroupOf_iff_le_normalizer
                (H := C) (K := N) hCN).2
                (by simpa [N, C] using CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer (X := G) B)
          let phi : N ⧸ C.subgroupOf N →* G ⧸ L :=
            QuotientGroup.lift (C.subgroupOf N) (qL.comp N.subtype) (by
              intro c hc
              exact (QuotientGroup.eq_one_iff (N := L) (x := (c : G))).2 (hC_le_L hc))
          have hphi_surj : Function.Surjective phi := by
            intro y
            rcases hqN_surj y with ⟨n, hnq⟩
            refine ⟨QuotientGroup.mk' (C.subgroupOf N) n, ?_⟩
            change qL (n : G) = y
            exact hnq
          have hAimage_bot :
              (((A1.subgroupOf N).map (QuotientGroup.mk' (C.subgroupOf N))).map phi) = ⊥ := by
            apply bot_unique
            calc
              (((A1.subgroupOf N).map (QuotientGroup.mk' (C.subgroupOf N))).map phi) ≤
                  (pCore p (N ⧸ C.subgroupOf N)).map phi := by
                    exact Subgroup.map_mono hstableA1
              _ ≤ pCore p (G ⧸ L) := by
                    exact rzj_pCore_map_le_pCore_of_surjective (G := N ⧸ C.subgroupOf N)
                      (p := p) phi hphi_surj
              _ = ⊥ := hpCore_quot_bot
          have hA1_le_L : A1 ≤ L := by
            intro a ha
            have haN : a ∈ N := hA1_le_N ha
            have haSub : (Subtype.mk a haN : N) ∈ A1.subgroupOf N := ha
            have haMap :
                QuotientGroup.mk' (C.subgroupOf N) (Subtype.mk a haN) ∈
                  (A1.subgroupOf N).map (QuotientGroup.mk' (C.subgroupOf N)) :=
              Subgroup.mem_map_of_mem (QuotientGroup.mk' (C.subgroupOf N)) haSub
            have hphi_mem :
                phi (QuotientGroup.mk' (C.subgroupOf N) (Subtype.mk a haN)) ∈
                  (((A1.subgroupOf N).map (QuotientGroup.mk' (C.subgroupOf N))).map phi) :=
              Subgroup.mem_map_of_mem phi haMap
            have hphi_eq : phi (QuotientGroup.mk' (C.subgroupOf N) (Subtype.mk a haN)) = 1 := by
              have :
                  phi (QuotientGroup.mk' (C.subgroupOf N) (Subtype.mk a haN)) ∈
                    (⊥ : Subgroup (G ⧸ L)) := by
                simpa [hAimage_bot] using hphi_mem
              simpa using this
            have haq : qL a = 1 := by
              change qL a = 1 at hphi_eq
              exact hphi_eq
            exact (QuotientGroup.eq_one_iff (N := L) (x := a)).1 haq
          exact hA1_not_le_L hA1_le_L
        have hreplacement :
            ∃ Astar : Subgroup G,
              Astar ∈ thompsonAbelianSubgroups (G := G) U ∧
                A1 ⊓ B < Astar ⊓ B ∧
                Astar ≤ Subgroup.normalizer (A1 : Set G) := by
          have hB_not_norm_A1 : ¬ B ≤ Subgroup.normalizer (A1 : Set G) := by
            intro hB_norm_A1
            exact htriple_ne_bot <|
              (rzj_thompsonAbelianSubgroups_normalizer_iff_commutator_eq_bot
                (G := G) (P := U) (A := A1) (B := B) hA1 hB_le_P).1 hB_norm_A1
          let N : Subgroup G := B ⊓ Subgroup.normalizer (A1 : Set G)
          let H : Subgroup G := A1 ⊔ B
          have hH_le_P : H ≤ U := by
            dsimp [H]
            exact sup_le hA1.1 hB_le_P
          have hA1_le_norm_N : A1 ≤ Subgroup.normalizer (N : Set G) := by
            have hA1_le_norm_B : A1 ≤ Subgroup.normalizer (B : Set G) := by
              rw [Subgroup.normalizer_eq_top (H := B)]
              exact le_top
            have hA1_le_norm_normA1 :
                A1 ≤ Subgroup.normalizer (Subgroup.normalizer (A1 : Set G) : Set G) := by
              exact
                (Subgroup.le_normalizer : A1 ≤ Subgroup.normalizer (A1 : Set G)).trans
                  (Subgroup.le_normalizer :
                    Subgroup.normalizer (A1 : Set G) ≤
                      Subgroup.normalizer (Subgroup.normalizer (A1 : Set G) : Set G))
            intro a ha
            exact
              (Subgroup.inf_normalizer_le_normalizer_inf
                (H := B) (K := Subgroup.normalizer (A1 : Set G))
                ⟨hA1_le_norm_B ha, hA1_le_norm_normA1 ha⟩)
          have hB_le_norm_N : B ≤ Subgroup.normalizer (N : Set G) := by
            refine subgroup_le_normalizer_of_conj_mem N B ?_
            intro b n hn
            have hbn : (b : G) * n = n * b := by
              exact
                setLike_mul_comm
                  (s := B) b.2 hn.1
            have hconj : (b : G) * n * (b : G)⁻¹ = n := by
              calc
                (b : G) * n * (b : G)⁻¹ = n * (b : G) * (b : G)⁻¹ := by
                  rw [hbn, mul_assoc]
                _ = n := by simp
            simpa [N, hconj] using hn
          have hH_le_norm_N : H ≤ Subgroup.normalizer (N : Set G) := by
            dsimp [H]
            exact sup_le hA1_le_norm_N hB_le_norm_N
          let Nsub : Subgroup H := N.subgroupOf H
          have hNsub_normal : Nsub.Normal := by
            simpa [Nsub] using
              (Subgroup.normal_subgroupOf_of_le_normalizer
                (H := H) (N := N) hH_le_norm_N)
          let qH : H →* H ⧸ Nsub := QuotientGroup.mk' Nsub
          let Bsub : Subgroup H := B.subgroupOf H
          have hBsub_normal : Bsub.Normal := by
            have hH_le_norm_B : H ≤ Subgroup.normalizer (B : Set G) := by
              rw [Subgroup.normalizer_eq_top (H := B)]
              exact le_top
            simpa [Bsub] using
              (Subgroup.normal_subgroupOf_of_le_normalizer
                (H := H) (N := B) hH_le_norm_B)
          let Bbar : Subgroup (H ⧸ Nsub) := Bsub.map qH
          have hBbar_normal : Bbar.Normal := by
            dsimp [Bbar, qH]
            exact
              Subgroup.Normal.map (H := Bsub) hBsub_normal
                (QuotientGroup.mk' Nsub) (QuotientGroup.mk'_surjective Nsub)
          have hBbar_ne_bot : Bbar ≠ ⊥ := by
            intro hBbar_bot
            apply hB_not_norm_A1
            intro b hb
            have hbH : b ∈ H := by
              dsimp [H]
              exact (show B ≤ A1 ⊔ B from le_sup_right) hb
            have hbsub : (⟨b, hbH⟩ : H) ∈ Bsub := by
              simpa [Bsub, Subgroup.mem_subgroupOf]
            have hBsub_le_Nsub : Bsub ≤ Nsub := by
              have hmap_bot : Bsub.map qH = ⊥ := by
                simpa [Bbar] using hBbar_bot
              simpa [qH, QuotientGroup.ker_mk'] using
                (Subgroup.map_eq_bot_iff (f := qH) (H := Bsub)).1 hmap_bot
            have hbNsub : (⟨b, hbH⟩ : H) ∈ Nsub := hBsub_le_Nsub hbsub
            have hbN : b ∈ N := by
              simpa [Nsub, Subgroup.mem_subgroupOf] using hbNsub
            exact hbN.2
          have hHp : IsPGroup p H := hU.to_le hH_le_P
          let : Fact (IsPGroup p (H ⧸ Nsub)) := ⟨hHp.to_quotient Nsub⟩
          have hx_exists :
              ∃ x ∈ B, x ∉ Subgroup.normalizer (A1 : Set G) ∧
                ∀ u ∈ A1, ⁅x, u⁆ ∈ N := by
            let : Bbar.Normal := hBbar_normal
            have : Nontrivial Bbar := (Subgroup.nontrivial_iff_ne_bot (H := Bbar)).2 hBbar_ne_bot
            obtain ⟨xbar, hxbar_ne_one, hxbar_center⟩ :=
              exists_nontrivial_center_mem_normal (N := Bbar) (p := p)
            obtain ⟨x0, hx0Bsub, hx0eq⟩ := Subgroup.mem_map.mp xbar.2
            have hx0B : (x0 : G) ∈ B := by
              simpa [Bsub, Subgroup.mem_subgroupOf] using hx0Bsub
            have hx0_center : qH x0 ∈ Subgroup.center (H ⧸ Nsub) := by
              simpa [hx0eq] using hxbar_center
            have hx0_ne_one : qH x0 ≠ 1 := by
              intro hx0q_one
              apply hxbar_ne_one
              apply Subtype.ext
              simpa [hx0eq] using hx0q_one
            have hx0_not_norm : (x0 : G) ∉ Subgroup.normalizer (A1 : Set G) := by
              intro hx0_norm
              have hx0Nsub : x0 ∈ Nsub := by
                have hx0N : (x0 : G) ∈ N := ⟨hx0B, hx0_norm⟩
                simpa [Nsub, Subgroup.mem_subgroupOf] using hx0N
              have hx0q_one : qH x0 = 1 := by
                exact (QuotientGroup.eq_one_iff (N := Nsub) x0).2 hx0Nsub
              exact hx0_ne_one hx0q_one
            have hcomm_gen_le_N : ∀ u ∈ A1, ⁅(x0 : G), u⁆ ∈ N := by
              intro u hu
              let uH : H := ⟨u, by
                dsimp [H]
                exact (show A1 ≤ A1 ⊔ B from le_sup_left) hu⟩
              have hcommq :
                  qH x0 * qH uH = qH uH * qH x0 := by
                exact ((Subgroup.mem_center_iff.mp hx0_center) (qH uH)).symm
              have hcomm_q : ⁅qH x0, qH uH⁆ = 1 := by
                exact commutatorElement_eq_one_iff_commute.mpr hcommq
              have hmap_comm : qH ⁅x0, uH⁆ = 1 := by
                calc
                  qH ⁅x0, uH⁆ = ⁅qH x0, qH uH⁆ := by
                    exact map_commutatorElement (f := qH) (g₁ := x0) (g₂ := uH)
                  _ = 1 := hcomm_q
              have hcomm_mem : ⁅x0, uH⁆ ∈ Nsub := by
                exact (QuotientGroup.eq_one_iff (N := Nsub) ⁅x0, uH⁆).1 hmap_comm
              change ⁅(x0 : G), u⁆ ∈ N at hcomm_mem
              exact hcomm_mem
            exact ⟨(x0 : G), hx0B, hx0_not_norm, hcomm_gen_le_N⟩
          obtain ⟨x, hxB, hx_not_norm, hcomm_gen_le_N⟩ := hx_exists
          let M : Subgroup G := Subgroup.closure {g : G | ∃ u ∈ A1, ⁅x, u⁆ = g}
          let C : Subgroup G := rzj_subgroupCentralizerIn' A1 M
          let Astar : Subgroup G := M ⊔ C
          have hxP : x ∈ U := hB_le_P hxB
          have hM_le_B : M ≤ B := by
            dsimp [M]
            rw [Subgroup.closure_le]
            intro y hy
            rcases hy with ⟨u, hu, rfl⟩
            exact
              (Subgroup.commutator_le_left (H₁ := B) (H₂ := A1))
                (Subgroup.commutator_mem_commutator hxB hu)
          have hM_comm : IsMulCommutative M := by
            refine ⟨?_⟩
            exact ⟨fun y z => by
              apply Subtype.ext
              simpa using
                (setLike_mul_comm
                  (s := B) (hM_le_B y.2) (hM_le_B z.2))⟩
          have hAstar :
              Astar ∈ thompsonAbelianSubgroups (G := G) U := by
            dsimp [Astar, C, M]
            simpa using
              (rzj_thompsonReplacement_base (G := G) (P := U)
                (A := A1) hA1 hxP hM_comm)
          have hAstar_lt : A1 ⊓ B < Astar ⊓ B := by
            have hA1infB_le_C : A1 ⊓ B ≤ C := by
              intro y hy
              dsimp [C, rzj_subgroupCentralizerIn']
              refine ⟨?_, hy.1⟩
              show y ∈ Subgroup.centralizer (M : Set G)
              rw [Subgroup.mem_centralizer_iff]
              intro m hmM
              have hyB : y ∈ B := hy.2
              have hmB : m ∈ B := hM_le_B hmM
              exact
                setLike_mul_comm
                  (s := B) hmB hyB
            have hA1infB_le_AstarinfB : A1 ⊓ B ≤ Astar ⊓ B := by
              have hC_le_Astar : C ≤ Astar := by
                dsimp [Astar]
                exact le_sup_right
              intro y hy
              exact ⟨hC_le_Astar (hA1infB_le_C hy), hy.2⟩
            have hM_not_le_A1 : ¬ M ≤ A1 := by
              intro hM_le_A1
              have hconj_le : ConjAct.toConjAct x • A1 ≤ A1 := by
                rw [Subgroup.pointwise_smul_def]
                intro y hy
                rcases Subgroup.mem_map.mp hy with ⟨u, hu, rfl⟩
                change x * u * x⁻¹ ∈ A1
                have hxy : ⁅x, u⁆ ∈ A1 := by
                  exact hM_le_A1 <| by
                    dsimp [M]
                    exact Subgroup.subset_closure ⟨u, hu, rfl⟩
                rw [show x * u * x⁻¹ = ⁅x, u⁆ * u by
                  simp [commutatorElement_def, mul_assoc]]
                exact A1.mul_mem hxy hu
              have hconj_eq : ConjAct.toConjAct x • A1 = A1 := by
                apply Subgroup.eq_of_le_of_card_ge hconj_le
                have hinj :
                    Function.Injective
                      ((MulDistribMulAction.toMonoidEnd (ConjAct G) G
                        (ConjAct.toConjAct x)) : G →* G) := by
                  intro a b hab
                  change x * a * x⁻¹ = x * b * x⁻¹ at hab
                  have h' := congrArg (fun t : G => x⁻¹ * t * x) hab
                  simpa [mul_assoc] using h'
                have hcard_conj :
                    Nat.card ↥(ConjAct.toConjAct x • A1) = Nat.card A1 := by
                  rw [Subgroup.pointwise_smul_def]
                  simpa using
                    (Subgroup.card_map_of_injective (K := A1) hinj)
                exact le_of_eq hcard_conj.symm
              have hx_norm : x ∈ Subgroup.normalizer (A1 : Set G) := by
                exact (Subgroup.conjAct_pointwise_smul_iff (H := A1) (g := x)).1 hconj_eq
              exact hx_not_norm hx_norm
            have hne : A1 ⊓ B ≠ Astar ⊓ B := by
              intro hEq
              apply hM_not_le_A1
              intro m hmM
              have hmAstar : m ∈ Astar := by
                dsimp [Astar]
                exact (show M ≤ M ⊔ C from le_sup_left) hmM
              have hmAstarB : m ∈ Astar ⊓ B := ⟨hmAstar, hM_le_B hmM⟩
              have hmA1B : m ∈ A1 ⊓ B := by simpa [hEq] using hmAstarB
              exact hmA1B.1
            exact lt_of_le_of_ne hA1infB_le_AstarinfB hne
          have hAstar_le_norm : Astar ≤ Subgroup.normalizer (A1 : Set G) := by
            rw [sup_le_iff]
            constructor
            · trans B ⊓ (Subgroup.normalizer (A1 : Set G))
              · refine le_inf hM_le_B ?_
                dsimp [M]
                rw [Subgroup.closure_le]
                intro y hy
                rcases hy with ⟨u, hu, rfl⟩
                exact (hcomm_gen_le_N u hu).2
              · exact inf_le_right
            · trans A1
              · subst C
                simp [rzj_subgroupCentralizerIn']
              · exact Subgroup.le_normalizer
          exact ⟨Astar, hAstar, hAstar_lt, hAstar_le_norm⟩
        have hcontr : False := by
          obtain ⟨Astar, hAstar, hlt, hAstar_norm⟩ := hreplacement
          have hAstar_le_L : Astar ≤ L := by
            by_contra hAstar_not_le_L
            have hAstarSbad : Astar ∈ Sbad := ⟨hAstar, hAstar_not_le_L⟩
            have hcard_le : Nat.card ↥(A1 ⊓ B) ≤ Nat.card ↥(Astar ⊓ B) :=
              Subgroup.card_le_of_le hlt.le
            have hcard_ne : Nat.card ↥(A1 ⊓ B) ≠ Nat.card ↥(Astar ⊓ B) := by
              intro hEq
              apply hlt.ne
              exact Subgroup.eq_of_le_of_card_ge hlt.le (le_of_eq hEq.symm)
            have hcard_lt : Nat.card ↥(A1 ⊓ B) < Nat.card ↥(Astar ⊓ B) :=
              lt_of_le_of_ne hcard_le hcard_ne
            exact (not_lt_of_ge (hA1max.le hAstarSbad)) hcard_lt
          let R : Subgroup G := U ⊓ L
          let X : Subgroup G := thompsonCenter (G := G) R
          have hB_le_X : B ≤ X := by
            obtain ⟨A, hA, hcomm2, hA_le_L⟩ := hA_exists
            have hB_norm_A : B ≤ Subgroup.normalizer (A : Set G) := by
              exact
                (rzj_thompsonAbelianSubgroups_normalizer_iff_commutator_eq_bot
                  (G := G) hA hB_le_P).2 hcomm2
            have hA_le_R : A ≤ R := by
              intro x hx
              exact ⟨hA.1 hx, hA_le_L hx⟩
            have hZ_le_A : thompsonCenter (G := G) U ≤ A :=
              rzj_thompsonCenter_le_of_mem hA
            have hZ_le_X :
                thompsonCenter (G := G) U ≤ X := by
              exact
                rzj_thompsonCenter_le_of_mem_thompsonAbelianSubgroups
                  (G := G) (P := U) (R := R) inf_le_left hA hZ_le_A hA_le_R
            have hB0_le_X : B0 ≤ X := by
              intro x hx
              exact hZ_le_X hx.2
            let : L.Normal := by
              dsimp [L]
              infer_instance
            have hFr : Subgroup.normalizer (R : Set G) ⊔ L = ⊤ := by
              obtain ⟨S, hS_map⟩ := hsyl
              simpa [R, hS_map] using (Sylow.normalizer_sup_eq_top (p := p) (N := L) S)
            have hL_le_norm_B0 : L ≤ Subgroup.normalizer (B0 : Set G) := by
              simpa [L] using (Subgroup.normalizer (B0 : Set G)).normalCore_le
            have hconj_B0_le_X : Group.conjugatesOfSet (B0 : Set G) ⊆ X := by
              intro y hy
              rcases Group.mem_conjugatesOfSet_iff.mp hy with ⟨x, hx, hxy⟩
              rcases isConj_iff.mp hxy with ⟨g, rfl⟩
              have hg : g ∈ Subgroup.normalizer (R : Set G) ⊔ L := by
                rw [hFr]
                exact Subgroup.mem_top g
              rcases
                  (Subgroup.mem_sup_of_normal_right
                    (s := Subgroup.normalizer (R : Set G)) (t := L) (x := g)).1 hg with
                ⟨n, hnR, l, hlL, rfl⟩
              have hlB0 : l ∈ Subgroup.normalizer (B0 : Set G) := hL_le_norm_B0 hlL
              have hlx : l * x * l⁻¹ ∈ X := by
                exact hB0_le_X ((Subgroup.mem_normalizer_iff.mp hlB0 _).1 hx)
              have hnX : n ∈ Subgroup.normalizer (X : Set G) := by
                simpa [X] using (rzj_normalizer_le_normalizer_thompsonCenter (G := G) R) hnR
              have hnx : n * (l * x * l⁻¹) * n⁻¹ ∈ X :=
                (Subgroup.mem_normalizer_iff.mp hnX _).1 hlx
              simpa [mul_assoc] using hnx
            rw [← hB1_eq_B]
            dsimp [B1]
            rw [Subgroup.normalClosure, Subgroup.closure_le]
            exact hconj_B0_le_X
          have hAstar_le_R : Astar ≤ R := by
            intro x hx
            exact ⟨hAstar.1 hx, hAstar_le_L hx⟩
          have hAstar_in_R :
              Astar ∈ thompsonAbelianSubgroups (G := G) R := by
            refine ⟨hAstar_le_R, hAstar.2.1, ?_⟩
            intro C hC hCcomm
            exact hAstar.2.2 C (hC.trans inf_le_left) hCcomm
          have hAstar_le_JR : Astar ≤ thompsonSubgroup (G := G) R := le_sSup hAstar_in_R
          have hJcent_le_centAstar :
              Subgroup.centralizer (thompsonSubgroup (G := G) R : Set G) ≤
                Subgroup.centralizer (Astar : Set G) := by
            exact Subgroup.centralizer_le
              (show (Astar : Set G) ⊆ (thompsonSubgroup (G := G) R : Set G) from hAstar_le_JR)
          have hX_le_subcent : X ≤ rzj_subgroupCentralizerIn' R Astar := by
            intro z hz
            refine ⟨?_, ?_⟩
            · have hzcent :
                z ∈ Subgroup.centralizer (thompsonSubgroup (G := G) R : Set G) := by
                simpa [X, thompsonCenter, centerIn] using hz.2
              exact hJcent_le_centAstar hzcent
            · exact rzj_thompsonCenter_le (G := G) R hz
          have hX_le_Astar : X ≤ Astar := by
            simpa [rzj_thompsonAbelianSubgroups_centralizer_eq
              (G := G) (P := R) (A := Astar) hAstar_in_R] using hX_le_subcent
          have hcomm2_Astar : ⁅⁅Astar, A1⁆, A1⁆ = ⊥ := by
            exact
              (rzj_thompsonAbelianSubgroups_normalizer_iff_commutator_eq_bot
                (G := G) (P := U) (A := A1) (B := Astar) hA1 hAstar.1).1
                hAstar_norm
          have htriple_bot : ⁅⁅B, A1⁆, A1⁆ = ⊥ := by
            apply bot_unique
            calc
              ⁅⁅B, A1⁆, A1⁆ ≤ ⁅⁅X, A1⁆, A1⁆ := by
                exact Subgroup.commutator_mono (Subgroup.commutator_mono hB_le_X le_rfl) le_rfl
              _ ≤ ⁅⁅Astar, A1⁆, A1⁆ := by
                exact Subgroup.commutator_mono (Subgroup.commutator_mono hX_le_Astar le_rfl) le_rfl
              _ ≤ ⊥ := by simp [hcomm2_Astar]
          exact htriple_ne_bot htriple_bot
        exact False.elim hcontr
  exact hmain (Nat.card B) B (show B.Normal from inferInstance) hBp hBne rfl

end ConstraintAndStability

end

end CFSG.ABGTheoremB.RelativeZJ
