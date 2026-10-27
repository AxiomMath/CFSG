module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A727e
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A727h
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A727m
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A729
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace R727

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H : Subgroup G}

theorem false_of_isElemAbelianOfRank_F4
    (S : Setting147 G T L V H) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) (h76 : Lemma14_7_6_F4) (hs : Group.IsSolvable (↥H ⧸ CFSG.pCore 2 ↥H))
    {X : Subgroup ↥(CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H))} (hXs : IsSupercritical 3 X)
    (hXf : ∀ α : MulAut ↥(CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)), (orderOf α).Coprime 3 →
      (∀ x ∈ X, x⁻¹ * α x ∈ frattiniIn X) → α = 1)
    (hX : IsElemAbelianOfRank 3 2 ↥X)
    (hKn : (X.map (CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)).subtype).Normal)
    (hL3 : ¬ IsPGroup 3 ↥(modO2Image H (l1 T L V))) : False := by
  classical
  set K := X.map (CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)).subtype with hKdef
  have := hKn
  have eX := Nonempty.some hX

  have hKc : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have h : (⟨x, hx⟩ : ↥X) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ :=
      eX.injective (by rw [map_mul, map_mul, mul_comm])
    exact congrArg (fun z : ↥X => ((z : ↥(CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H))) :
      ↥H ⧸ CFSG.pCore 2 ↥H)) h
  have hK9 : Nat.card ↥K = 9 := by
    rw [hKdef, Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
      Nat.card_congr eX.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
      Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin]
    norm_num
  have hK3 : ∀ k ∈ K, k ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    simpa using congrArg Subtype.val (hXs.pow_eq_one x hx)

  have h98 := S.hypF98_F4 (stmt13_3_2_two_of_F4 h1332) (stmtL32NModule_of_inputs_F4 h1332 h1334) h1222
  have h91 := h98.toHypF91
  have hE := h91.isElemAbelian_tilde
  let _ : CommGroup ↥(tildeOf (fsuV1 T V) (conjClosure V H)) := commGroupOfElemAbelian hE
  have hV : ∀ w : ↥(tildeOf (fsuV1 T V) (conjClosure V H)), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using hE.2 w w.2)
  set XV := autOn (tildeOf (fsuV1 T V) H) (tildeOf (fsuV1 T V) (conjClosure V H)) with hXV
  have hker : CFSG.pCore 2 ↥H ≤ (FixR.rho h91).ker := fun x hx =>
    MonoidHom.mem_ker.mpr ((FixR.rho_eq_one_iff h91 x).mpr ((mem_pCoreOf_iff x).mpr hx))
  set ρ := QuotientGroup.lift (CFSG.pCore 2 ↥H) (FixR.rho h91) hker with hρdef
  have hρ : ∀ x : ↥H, ρ (QuotientGroup.mk' (CFSG.pCore 2 ↥H) x) = FixR.rho h91 x := fun _ => rfl
  have hinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro z hz
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥H) z
    rw [MonoidHom.mem_ker, hρ] at hz
    rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact (mem_pCoreOf_iff x).mp ((FixR.rho_eq_one_iff h91 x).mp hz)
  have hmemX : ∀ z, ρ z ∈ XV := by
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥H) z
    rw [hρ]
    exact (FixR.mem_autOn_tilde_iff h91 le_rfl).mpr ⟨x, x.2, rfl⟩
  have hXVρ : ∀ a ∈ XV, ∃ z, ρ z = a := by
    intro a ha
    obtain ⟨y, -, rfl⟩ := (FixR.mem_autOn_tilde_iff h91 le_rfl).mp ha
    exact ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥H) y, hρ y⟩

  refine E9.false_of_qhat (X := XV) (P := K.map ρ) hV ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rintro _ ⟨k, -, rfl⟩
    exact hmemX k
  · intro g hg κ hκ
    obtain ⟨z, rfl⟩ := hXVρ g hg
    obtain ⟨k, hk, rfl⟩ := hκ
    exact ⟨z * k * z⁻¹, hKn.conj_mem k hk z, by rw [map_mul, map_mul, map_inv]⟩
  · rintro _ ⟨k, hk, rfl⟩ _ ⟨k', hk', rfl⟩
    rw [← map_mul, ← map_mul, hKc k hk k' hk']
  · rw [Subgroup.card_map_of_injective hinj, hK9]
  · rintro _ ⟨k, hk, rfl⟩
    rw [← map_pow, hK3 k hk, map_one]
  · intro a ha ha2 hac
    obtain ⟨z, rfl⟩ := hXVρ a ha
    have hz2 : z ^ 2 = 1 := hinj (by rw [map_pow, ha2, map_one])
    have hzK : ∀ k ∈ K, z * k = k * z := fun k hk =>
      hinj (by rw [map_mul, map_mul]; exact hac _ ⟨k, hk, rfl⟩)
    rw [eq_one_of_comm_of_sq_F4 S h76 hs hXf hz2 hzK, map_one]
  · rintro _ ⟨k, hk, rfl⟩ hk1
    have hk1' : k ≠ 1 := by
      rintro rfl
      exact hk1 (map_one ρ)
    obtain ⟨b, -, hb3, hbk⟩ := exists_move_F4 S h1222 h1332 h1334 h76 hs hXs hXf hX hKn hL3 hk hk1'
    refine ⟨ρ b, hmemX b, by rw [← map_pow, hb3, map_one], fun hm => hbk ?_⟩
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hm
    rw [← map_mul, ← map_inv, ← map_mul, ← map_zpow] at hm
    exact Subgroup.mem_zpowers_iff.mpr ⟨m, hinj hm⟩
  · exact (qhatOf_le_qOf XV).trans h98.lemma_14_5_18_three.1

end R727

theorem input14727B2_of_F4
    (h76 : Lemma14_7_6_F4) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) :
    Input14727B2_F4 := by
  intro G _ _ T L V H S X hX hXf hKM hHe
  by_contra hLP
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP3 : IsPGroup 3 ↥(CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)) := CFSG.pCore_isPGroup
  have : (CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)).Normal := CFSG.pCore_normal
  have : X.Characteristic := hX.characteristic
  have hKn : (X.map (CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)).subtype).Normal :=
    normal_map_of_characteristic X
  have hK3 : IsPGroup 3 ↥(X.map (CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)).subtype) :=
    (hP3.to_subgroup X).map _
  have hL3 := R727.not_isPGroup_l1_star_F4 S h1332 hKn hK3 hHe hLP
  have hs := R727.isSolvable_star_F4 S h1332 h1334 hKn hK3 hHe

  have hPne : Nontrivial ↥(CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    intro hbot
    apply hKM
    refine R727.pre_le_M_of_le_l1_F4 S h1332 fun k hk => ?_
    obtain ⟨x, -, rfl⟩ := hk
    have hx : (x : ↥H ⧸ CFSG.pCore 2 ↥H) = 1 :=
      (Subgroup.eq_bot_iff_forall _).mp hbot _ x.2
    show (x : ↥H ⧸ CFSG.pCore 2 ↥H) ∈ _
    rw [hx]
    exact Subgroup.one_mem _
  rcases IsSupercritical.iso_cases (by norm_num) hX hP3 (R727.pRank_pCore_three_le S) with
    h | h | h
  · obtain ⟨e⟩ := h
    have hX3 : Nat.card ↥X = 3 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    have hKc : Nat.card ↥(X.map (CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)).subtype) = 3 := by
      rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hX3]
    exact R727.false_of_card_three_F4 S h1222 h1332 h1334 h76 hs hXf hKc hKn hL3
  · exact R727.false_of_isElemAbelianOfRank_F4 S h1222 h1332 h1334 h76 hs hX hXf h hKn hL3
  · exact R727.false_of_isPOnePlusTwo_F4 S h1222 h1332 h1334 h76 hs hXf h hKn hL3

theorem lemma14_7_27_of_inputs_F4
    (h714 : Thm14_7_14_F4) (h79 : Lemma14_7_9_F4) (h78 : Lemma14_7_8_F4) (h76 : Lemma14_7_6_F4)
    (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) : Lemma14_7_27_F4 :=
  lemma14_7_27_of_F4 h714 h79 h78 h1222 h1332 h1334 (input14727B2_of_F4 h76 h1222 h1332 h1334)

theorem lemma14_7_28_of_inputs_F4
    (h714 : Thm14_7_14_F4) (h79 : Lemma14_7_9_F4) (h78 : Lemma14_7_8_F4) (h76 : Lemma14_7_6_F4)
    (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) : Lemma14_7_28_F4 :=
  lemma14_7_28_of_F4 (lemma14_7_27_of_inputs_F4 h714 h79 h78 h76 h1222 h1332 h1334) h76 h1222 h1332
    h1334

theorem thm14_7_29_of_inputs_F4
    (h714 : Thm14_7_14_F4) (h79 : Lemma14_7_9_F4) (h78 : Lemma14_7_8_F4) (h76 : Lemma14_7_6_F4)
    (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) : Thm14_7_29_F4 :=
  thm14_7_29_of_F4 (lemma14_7_28_of_inputs_F4 h714 h79 h78 h76 h1222 h1332 h1334) h1222 h1332 h1334

end CFSG.Quasithin.H13.L32A
