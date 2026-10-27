module

public import CFSG.Quasithin.H13.L32AC37b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A770n
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC37a

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H V₂ : Subgroup G}

theorem le_inf_g1_sup_L2_F4 [IsMulCommutative ↥V] (S : L32NSet14.Setting_F4 G T L V V₂) :
    L ≤ (L ⊓ A6.g1 T V) ⊔ L₁Of L V₂ := by
  obtain ⟨z, a, b, hz, hz1, ha, haV, hb, hbV⟩ := S.exists_basis_F4
  have hzV₂ := S.hV2.1 hz
  have hzV : z ∈ V := (Subgroup.mem_inf.mp hz).1
  have haV' : a ∈ V := S.hV2.2.1 ha
  have hL2 : L₁Of L V₂ ≤ L := (oTwoRes_le _).trans inf_le_left
  have hJL : (L ⊓ A6.g1 T V) ⊔ L₁Of L V₂ ≤ L := sup_le inf_le_left hL2
  have key : ∀ w ∈ V, w ≠ 1 → ∃ h ∈ (L ⊓ A6.g1 T V) ⊔ L₁Of L V₂, h * z * h⁻¹ = w := by
    intro w hw hw1
    by_cases hw2 : w ∈ V₂
    · by_cases hw1' : w ∈ fsuV1 T V
      · rcases S.eq_of_mem_V1_F4 hz hz1 hw1' with rfl | rfl
        · exact absurd rfl hw1
        · exact ⟨1, one_mem _, by group⟩
      · obtain ⟨l, hl, hlz⟩ := S.exists_L2_F4 hz hz1 hw2 hw1' hb hbV
        exact ⟨l, Subgroup.mem_sup_right hl, hlz⟩
    · obtain ⟨l₂, hl₂, hl₂z⟩ := S.exists_L2_F4 hz hz1 ha haV hb hbV
      obtain ⟨n, hn, -, hnz, hna, -⟩ := S.exists_rot_F4 hzV haV' hw
        (fun h => haV (h ▸ one_mem _)) hw1 (fun h => haV (h ▸ hz)) (fun h => hw2 (h ▸ hzV₂))
        (fun h => hw2 (h ▸ ha)) (fun h => hw2 (h ▸ mul_mem hzV₂ ha))
      refine ⟨n * l₂, mul_mem (Subgroup.mem_sup_left (Subgroup.mem_inf.mpr
        ⟨hn, S.mem_g1_F4 hz hz1 hnz⟩)) (Subgroup.mem_sup_right hl₂), ?_⟩
      calc n * l₂ * z * (n * l₂)⁻¹ = n * (l₂ * z * l₂⁻¹) * n⁻¹ := by group
        _ = w := by rw [hl₂z, hna]
  intro l hl
  have hw : l * z * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (S.LV_F4 hl) z).mp hzV
  have hw1 : l * z * l⁻¹ ≠ 1 := fun h => hz1 (by
    calc z = l⁻¹ * (l * z * l⁻¹) * l := by group
      _ = 1 := by rw [h]; group)
  obtain ⟨h, hh, hhz⟩ := key _ hw hw1
  have hfix : (h⁻¹ * l) * z * (h⁻¹ * l)⁻¹ = z := by
    calc (h⁻¹ * l) * z * (h⁻¹ * l)⁻¹ = h⁻¹ * (l * z * l⁻¹) * h := by group
      _ = h⁻¹ * (h * z * h⁻¹) * h := by rw [hhz]
      _ = z := by group
  have hmem : h⁻¹ * l ∈ (L ⊓ A6.g1 T V) ⊔ L₁Of L V₂ :=
    Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem (hJL hh)) hl,
      S.mem_g1_F4 hz hz1 hfix⟩)
  have := mul_mem hh hmem
  rwa [mul_inv_cancel_left] at this

theorem inf_g1_le_l1_sup_T_F4 [IsMulCommutative ↥V] (S : Setting147 G T L V H)
    (S14 : L32NSet14.Setting_F4 G T L V V₂) : L ⊓ A6.g1 T V ≤ l1 T L V ⊔ T := by
  have hTX : T ≤ Subgroup.normalizer ((L ⊓ A6.g1 T V : Subgroup G) : Set G) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨S14.TL_F4 ht, Subgroup.le_normalizer (S14.T_V1_F4 ht)⟩
  have hsyl : IsSylowTwoOf (T ⊓ (L ⊓ A6.g1 T V)) (L ⊓ A6.g1 T V) :=
    A4.isSylowTwoOf_inf_normal
      (isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.fsu.sylow
        (le_sup_right : T ≤ (L ⊓ A6.g1 T V) ⊔ T))
      le_sup_left (sup_le Subgroup.le_normalizer hTX)
  exact (oTwoUpper_sup_of_sylow hsyl).ge.trans (sup_le_sup le_rfl inf_le_left)

theorem oTwoUpper_le_centralizer_F4 (S : Setting147 G T L V H) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) (hV2 : A6.IsV2 T V V₂) :
    oTwoUpper (centralizerMod (fsuV1 T V) H V₂) ≤ Subgroup.centralizer (V₂ : Set G) := by
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  have h2 := sq_mem_centralizer_F4 S h1332 h1334 hV2 hx.1
  exact (Subgroup.zpowers_le.mpr h2)
    (A4.mem_zpowers_pow_of_coprime (Nat.coprime_two_left.mpr hx.2))

theorem conj_mem_of_L2_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (h4 : Lemma14_7_4_two_three_F4) (S : Setting147 G T L V H) (hV2 : A6.IsV2 T V V₂)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) {l x v : G} (hl : l ∈ L₁Of L V₂)
    (hx : x ∈ oTwoUpper (centralizerMod (fsuV1 T V) H V₂)) (hv : v ∈ V) :
    l * (x * v * x⁻¹) * l⁻¹ ∈ conjClosure V H := by
  have h4' := h4 G T L V V₂ S.hyp hV2
  have hxC := oTwoUpper_le_centralizer_F4 S h1332 h1334 hV2 hx
  have hxH : x ∈ H := (oTwoUpper_le _ hx).1
  have hlN : l ∈ Subgroup.normalizer (V₂ : Set G) := ((oTwoRes_le _).trans inf_le_right) hl
  have hlL : l ∈ L := ((oTwoRes_le _).trans inf_le_left) hl
  have hxN : x ∈ Subgroup.normalizer (L₁Of L V₂ : Set G) := by
    rw [h4'.2.2.2.1, oTwoRes_eq_oTwoUpper]
    exact normalizer_le_normalizer_oTwoUpper _
      (h4'.1.2 ((Subgroup.centralizer_le_normalizer _) hxC))
  have hc : l * x * l⁻¹ * x⁻¹ ∈ T := by
    refine inf_centralizer_le_T_F4 h1222 h1332 h1334 h4 S hV2
      (Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_left ?_, ?_⟩)
    · have : x * l⁻¹ * x⁻¹ ∈ L₁Of L V₂ := (Subgroup.mem_normalizer_iff.mp hxN _).mp (inv_mem hl)
      have e : l * x * l⁻¹ * x⁻¹ = l * (x * l⁻¹ * x⁻¹) := by group
      rw [e]
      exact mul_mem hl this
    · have h1 : l * x * l⁻¹ ∈ Subgroup.centralizer (V₂ : Set G) :=
        (Subgroup.mem_normalizer_iff.mp (mem_normalizer_centralizer' hlN) x).mp hxC
      exact mul_mem h1 (inv_mem hxC)
  have hTH : T ≤ H := le_sup_right.trans S.hz.1.1
  have hcx : l * x * l⁻¹ * x⁻¹ * x ∈ H := mul_mem (hTH hc) hxH
  have hlv : l * v * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hLV hlL) v).mp hv
  have e : l * (x * v * x⁻¹) * l⁻¹ =
      (l * x * l⁻¹ * x⁻¹ * x) * (l * v * l⁻¹) * (l * x * l⁻¹ * x⁻¹ * x)⁻¹ := by group
  rw [e]
  exact mem_conjClosure hcx hlv

theorem L2_le_normalizer_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (h4 : Lemma14_7_4_two_three_F4) (S : Setting147 G T L V H) (hV2 : A6.IsV2 T V V₂)
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (heq : conjClosure V (centralizerMod (fsuV1 T V) H V₂) = conjClosure V H) :
    L₁Of L V₂ ≤ Subgroup.normalizer (conjClosure V H : Set G) := by
  intro l hl
  have hle : conjClosure V H ≤ conjClosure V (oTwoUpper (centralizerMod (fsuV1 T V) H V₂)) :=
    heq ▸ conjClosure_le_oTwoUpper S hTV hV2
  have hcomap : conjClosure V (oTwoUpper (centralizerMod (fsuV1 T V) H V₂)) ≤
      (conjClosure V H).comap (MulAut.conj l).toMonoidHom :=
    conjClosure_le fun x hx v hv => conj_mem_of_L2_F4 h1222 h1332 h1334 h4 S hV2 hLV hl hx hv
  exact Subgroup.mem_normalizer_fintype fun n hn => hcomap (hle hn)

theorem lemma14_7_37_one_of_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (h4 : Lemma14_7_4_two_three_F4) (S : Setting147 G T L V H) (hV2 : A6.IsV2 T V V₂) :
    conjClosure V (centralizerMod (fsuV1 T V) H V₂) < conjClosure V H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V S.hyp.hyp S.hyp.fsu).1.1
  have S14 := Hyp147.set14_F4 S.hyp h1222 h1332 h1334 hV2
  refine lt_of_le_of_ne (conjClosure_mono le_rfl (centralizerMod_le_left _ _ _)) fun heq => ?_
  have hTH : T ≤ H := le_sup_right.trans S.hz.1.1
  have hL2 := L2_le_normalizer_F4 h1222 h1332 h1334 h4 S hV2 S14.TV_F4 S14.LV_F4 heq
  have hHN := le_normalizer_conjClosure V H
  have hLN : L ⊔ T ≤ Subgroup.normalizer (conjClosure V H : Set G) :=
    sup_le ((le_inf_g1_sup_L2_F4 S14).trans
      (sup_le ((inf_g1_le_l1_sup_T_F4 S S14).trans (S.hz.1.1.trans hHN)) hL2)) (hTH.trans hHN)
  have hP2 : IsPGroup 2 ↥(conjClosure V H) := fun u => ⟨1, by
    have := L32A.Setting147.sq_fsuU S (fun v hv => S14.mul_self_V_F4 hv) u.1
      (conjClosure_mono le_rfl S.hz.2.1 u.2)
    apply Subtype.ext
    simpa [pow_two] using this⟩
  have hP1 : conjClosure V H ≠ ⊥ := fun hbot => by
    have h1 := Subgroup.card_le_of_le ((le_conjClosure V H).trans hbot.le)
    rw [Subgroup.card_bot, S14.card_V_F4] at h1
    omega
  exact S.hz.2.2 (hHN.trans
    (normalizer_le_normalizer_L_F4 S.hyp (stmt13_3_2_two_of_F4 h1332) hP1 hP2 hLN))

end CFSG.Quasithin.H13.L32A.C
