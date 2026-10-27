module

public import CFSG.Quasithin.H13.L32A74
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L1332
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASetting
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NModule
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NSet14Idx

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative commutatorElement

namespace Hyp147

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

theorem inf_centralizer_eq_bot_F4 (h : Hyp147 G T L V) (h13322 : Stmt13_3_2_two_F4)
    (hMod : StmtL32NModule_F4) : V ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  have h1281 := h.hyp1281One_F4 h13322 hMod
  obtain ⟨hcard, -, -⟩ := h1281.card_sq
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨hvV, hvC⟩ := Subgroup.mem_inf.mp hv
  rw [Subgroup.mem_bot]
  by_contra hv1
  obtain ⟨w, hw1, hwv⟩ : ∃ w : ↥V, w ≠ 1 ∧ w ≠ ⟨v, hvV⟩ := by
    by_contra hne
    have hsub : (Set.univ : Set ↥V) ⊆ {1, ⟨v, hvV⟩} := fun w _ => by
      by_cases hw : w = 1
      · exact Or.inl hw
      · exact Or.inr (by_contra fun h' => hne ⟨w, hw, h'⟩)
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_univ, hcard] at h1
    have h2 := Set.ncard_insert_le (1 : ↥V) {⟨v, hvV⟩}
    rw [Set.ncard_singleton] at h2
    omega
  obtain ⟨l, hl, hlv⟩ := L32A.exists_conj_eq_of_mem h1281 hvV w.2 hv1
    (fun h' => hw1 (Subtype.ext h'))
  apply hwv
  apply Subtype.ext
  show (w : G) = v
  rw [← hlv, Subgroup.mem_centralizer_iff.mp hvC l hl, mul_inv_cancel_right]

theorem isEmpty_autOn_equiv_F4 (h : Hyp147 G T L V) (hMod : StmtL32NModule_F4) :
    IsEmpty (↥(autOn L V) ≃* ↥(alternatingGroup (Fin 5))) := by
  refine ⟨fun e => ?_⟩
  obtain ⟨_, hnat⟩ := (hMod G T L V h.hyp h.fsu).2.2.2.2
  have h1 : Nat.card ↥(autOn L V) = 168 := by
    rw [card_eq_of_binaryNaturalSL hnat (by norm_num)]
    decide
  have h2 := Nat.card_congr e.toEquiv
  rw [h1, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin] at h2
  revert h2
  decide

theorem exists_V2_F4 (h : Hyp147 G T L V) (h13322 : Stmt13_3_2_two_F4) (hMod : StmtL32NModule_F4)
    (h1222 : Stmt12_2_2_F4) : ∃ V₂ : Subgroup G, A6.IsV2 T V V₂ := by
  obtain ⟨V₂, hV₂, h12⟩ :=
    exists_v2_of_hyp1281One_F4 h1222 (h.hyp1281One_F4 h13322 hMod) (h.isTSub_V1_F4 hMod)
  exact ⟨V₂, h12, hV₂.1, hV₂.2.2, by rw [hV₂.2.1]; norm_num⟩

theorem set14_F4 (h : Hyp147 G T L V) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) {V₂ : Subgroup G} (hV2 : A6.IsV2 T V V₂) [IsMulCommutative ↥V] :
    L32NSet14.Setting_F4 G T L V V₂ := by
  have h13322 := stmt13_3_2_two_of_F4 h1332
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  obtain ⟨_, hnat⟩ := (hMod G T L V h.hyp h.fsu).2.2.2.2
  exact ⟨h1222, h1332, h1334, h.hyp.h13, (h.hyp1223_F4 h13322).irrPlus,
    h.inf_centralizer_eq_bot_F4 h13322 hMod, hV2, h.hyp.linear, hnat⟩

end Hyp147

namespace L32A

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

theorem lemma14_7_4_one_F4 (h : Hyp147 G T L V) (h13322 : Stmt13_3_2_two_F4) (hMod : StmtL32NModule_F4)
    (h13314 : A6.Stmt13_3_14_F4) {V₂ : Subgroup G} (hV2 : A6.IsV2 T V V₂) :
    ⁅V₂, pCoreOf 2 (A6.g1 T V)⁆ = fsuV1 T V := by
  have hV1 := h.isTSub_V1_F4 hMod
  have hcard1 : Nat.card ↥(fsuV1 T V) = 2 := by simpa using hV1.2.1
  have hQT : pCoreOf 2 (A6.g1 T V) ≤ T := pCoreOf_le_of_le h hV1.2.2
  have hle : ⁅V₂, pCoreOf 2 (A6.g1 T V)⁆ ≤ fsuV1 T V := by
    rw [Subgroup.commutator_le]
    intro v hv q hq
    have hqT := hQT hq
    by_cases hv1 : v ∈ fsuV1 T V
    · have e : ⁅v, q⁆ = (q * v * q⁻¹ * v⁻¹)⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e, conj_fsuV1 hv1 hqT, mul_inv_cancel, inv_one]
      exact one_mem _
    · have h1 : q * v⁻¹ * q⁻¹ ∈ V₂ :=
        (Subgroup.mem_normalizer_iff.mp (hV2.2.2.1 hqT) _).mp (inv_mem hv)
      have h2 : q * v⁻¹ * q⁻¹ ∉ fsuV1 T V := fun h' => by
        apply hv1
        have := (Subgroup.mem_normalizer_iff.mp (hV1.2.2 (inv_mem hqT)) _).mp h'
        rw [show q⁻¹ * (q * v⁻¹ * q⁻¹) * q⁻¹⁻¹ = v⁻¹ by group] at this
        simpa using this
      have := L32NSet14.mul_mem_of_card_eq_two_mul hV2.1 (by rw [hV2.2.2.2, hcard1])
        (by rw [hcard1]; norm_num) hv h1 hv1 h2
      rwa [commutatorElement_def, mul_assoc v q, mul_assoc v (q * v⁻¹)]
  apply le_antisymm hle
  by_contra hnot
  have hbot : ⁅V₂, pCoreOf 2 (A6.g1 T V)⁆ = ⊥ := by
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [hcard1] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exact absurd (Subgroup.eq_of_le_of_card_ge hle (by rw [h2, hcard1])) fun e =>
        hnot (le_of_eq e.symm)
  apply h13314 G T L V V₂ h.hyp.h13 (h.hyp1223_F4 h13322).irrPlus
    (h.inf_centralizer_eq_bot_F4 h13322 hMod) hV2 (h.isEmpty_autOn_equiv_F4 hMod)
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hbot
  exact Subgroup.le_centralizer_iff.mp hbot

theorem conj_eq_of_basis_F4 {V₂ : Subgroup G} [IsMulCommutative ↥V]
    (S14 : L32NSet14.Setting_F4 G T L V V₂) {z a b g : G} (hz : z ∈ fsuV1 T V) (hz1 : z ≠ 1)
    (ha : a ∈ V₂) (haV : a ∉ fsuV1 T V) (hb : b ∈ V) (hbV : b ∉ V₂) (hgz : g * z * g⁻¹ = z)
    (hga : g * a * g⁻¹ = a) (hgb : g * b * g⁻¹ = b) {v : G} (hv : v ∈ V) :
    g * v * g⁻¹ = v := by
  have key1 : ∀ u ∈ fsuV1 T V, g * u * g⁻¹ = u := fun u hu => by
    rcases S14.eq_of_mem_V1_F4 hz hz1 hu with rfl | rfl
    · group
    · exact hgz
  have key2 : ∀ w ∈ V₂, g * w * g⁻¹ = w := fun w hw => by
    rcases S14.mem_V2_F4 ha haV hw with h | h
    · exact key1 w h
    · calc g * w * g⁻¹ = (g * a * g⁻¹)⁻¹ * (g * (a * w) * g⁻¹) := by group
        _ = w := by rw [hga, key1 _ h]; group
  rcases S14.mem_V_F4 hb hbV hv with h | h
  · exact key2 v h
  · calc g * v * g⁻¹ = (g * b * g⁻¹)⁻¹ * (g * (b * v) * g⁻¹) := by group
      _ = v := by rw [hgb, key2 _ h]; group

theorem lemma14_7_4_four_F4 {H : Subgroup G} (S : Setting147 G T L V H)
    (hF : HypF98 T V L (fsuV1 T V) V H) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) (h13314 : A6.Stmt13_3_14_F4) :
    pCoreOf 2 (L ⊔ T) ⊔ pCoreOf 2 H = pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) := by
  have h13322 := stmt13_3_2_two_of_F4 h1332
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨V₂, hV2⟩ := S.hyp.exists_V2_F4 h13322 hMod h1222
  have : IsMulCommutative ↥V := (hMod G T L V S.hyp.hyp S.hyp.fsu).1.1
  have S14 := S.hyp.set14_F4 h1222 h1332 h1334 hV2
  have hTH : T ≤ H := le_sup_right.trans hF.L₁T_le_H
  have hL1H : L₁Of L (fsuV1 T V) ≤ H := le_sup_left.trans hF.L₁T_le_H
  have hHG1 : H ≤ A6.g1 T V := S.hz.2.1
  have hQHT : pCoreOf 2 H ≤ T := pCoreOf_le_of_le S.hyp hTH
  have hR1T : pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ≤ T := pCoreOf_le_of_le S.hyp le_sup_right
  have hL1L : L₁Of L (fsuV1 T V) ≤ L := (L32NSet14.Setting.L1_le).trans inf_le_left
  have hQR : pCoreOf 2 (L ⊔ T) ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_sup_le S.hyp).trans le_sup_right)
      ((sup_le_sup_right hL1L T).trans (le_normalizer_pCoreOf 2 (L ⊔ T)))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T))
  have hQHR : pCoreOf 2 H ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 (hQHT.trans le_sup_right)
      ((sup_le hL1H hTH).trans (le_normalizer_pCoreOf 2 H))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)
  refine le_antisymm (sup_le hQR hQHR) ?_
  obtain ⟨z, a, b, hz, hz1, ha, haV, hb, hbV⟩ := S14.exists_basis_F4
  obtain ⟨x, hxL, hxz, hxa, hxb⟩ := S14.exists_x_F4 hz hz1 ha haV hb hbV
  have haV' : a ∈ V := hV2.2.1 ha
  have hzV : z ∈ V := (Subgroup.mem_inf.mp hz).1

  have hcases : ∀ r ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T), ∀ v ∈ V,
      ∃ e ∈ fsuV1 T V, r * v * r⁻¹ = e * v := fun r hr v hv =>
    ⟨_, (S14.pCoreOf_L1T_le_F4 hr).2.2 v hv, by group⟩

  have hQ1QH : pCoreOf 2 (A6.g1 T V) ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le_of_le S.hyp (S.hyp.isTSub_V1_F4 hMod).2.2).trans hTH)
      (hHG1.trans (le_normalizer_pCoreOf 2 _)) (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  obtain ⟨y, hyQH, hya⟩ : ∃ y ∈ pCoreOf 2 H, y * a * y⁻¹ = z * a := by
    by_contra hne
    have hfix : ∀ q ∈ pCoreOf 2 (A6.g1 T V), q * a * q⁻¹ = a := fun q hq => by
      obtain ⟨e, he, hqa⟩ := hcases q (hQHR (hQ1QH hq)) a haV'
      rcases S14.eq_of_mem_V1_F4 hz hz1 he with rfl | rfl
      · rw [hqa, one_mul]
      · exact absurd ⟨q, hQ1QH hq, hqa⟩ hne
    have hbot : ⁅V₂, pCoreOf 2 (A6.g1 T V)⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro w hw q hq
      have hqT := hR1T (hQHR (hQ1QH hq))
      have hqw : q * w * q⁻¹ = w := by
        have key1 : ∀ u ∈ fsuV1 T V, q * u * q⁻¹ = u := fun u hu => conj_fsuV1 hu hqT
        rcases S14.mem_V2_F4 ha haV hw with h' | h'
        · exact key1 w h'
        · calc q * w * q⁻¹ = (q * a * q⁻¹)⁻¹ * (q * (a * w) * q⁻¹) := by group
            _ = w := by rw [hfix q hq, key1 _ h']; group
      rw [Subgroup.mem_bot, commutatorElement_def, show w * q * w⁻¹ * q⁻¹ =
        w * (q * w * q⁻¹)⁻¹ by group, hqw, mul_inv_cancel]
    rw [lemma14_7_4_one_F4 S.hyp h13322 hMod h13314 hV2] at hbot
    exact hz1 (by rw [hbot] at hz; exact Subgroup.mem_bot.mp hz)

  have hxQH : x * y * x⁻¹ ∈ pCoreOf 2 H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (hL1H hxL)) y).mp hyQH
  have hcomm : ∀ {u v : G}, u ∈ V → v ∈ V → u * v = v * u := fun hu hv => S14.comm_V_F4 hu hv
  have hsq : ∀ {u : G}, u ∈ V → u * u = 1 := fun hu => S14.mul_self_V_F4 hu
  have hxia : x⁻¹ * a * x = a * b := by
    have e1 : x * (a * b) * x⁻¹ = a := by
      calc x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
        _ = b * (a * b) := by rw [hxa, hxb]
        _ = a * (b * b) := by rw [← mul_assoc, hcomm hb haV', mul_assoc]
        _ = a := by rw [hsq hb, mul_one]
    calc x⁻¹ * a * x = x⁻¹ * (x * (a * b) * x⁻¹) * x := by rw [e1]
      _ = a * b := by group
  have hxib : x⁻¹ * b * x = a := by
    calc x⁻¹ * b * x = x⁻¹ * (x * a * x⁻¹) * x := by rw [hxa]
      _ = a := by group
  obtain ⟨e, he, hyb⟩ := hcases y (hQHR hyQH) b hb
  have heV : e ∈ V := (Subgroup.mem_inf.mp he).1
  have hxe : x * e * x⁻¹ = e := by
    rcases S14.eq_of_mem_V1_F4 hz hz1 he with rfl | rfl
    · group
    · exact hxz
  have hyT : y ∈ T := hQHT hyQH
  have hye : y * e * y⁻¹ = e := conj_fsuV1 he hyT
  have hyz : y * z * y⁻¹ = z := conj_fsuV1 hz hyT

  have hy'a : (x * y * x⁻¹) * a * (x * y * x⁻¹)⁻¹ = z * e * a := by
    calc (x * y * x⁻¹) * a * (x * y * x⁻¹)⁻¹ = x * (y * (x⁻¹ * a * x) * y⁻¹) * x⁻¹ := by group
      _ = x * ((y * a * y⁻¹) * (y * b * y⁻¹)) * x⁻¹ := by rw [hxia]; group
      _ = (x * z * x⁻¹) * (x * a * x⁻¹) * (x * e * x⁻¹) * (x * b * x⁻¹) := by
          rw [hya, hyb]
          group
      _ = z * b * e * (a * b) := by rw [hxz, hxa, hxe, hxb]
      _ = z * e * a * (b * b) := by
          rw [mul_assoc z b e, hcomm hb heV, ← mul_assoc z e b, mul_assoc (z * e) b (a * b),
            ← mul_assoc b a b, hcomm hb haV', mul_assoc a b b, ← mul_assoc (z * e) a]
      _ = z * e * a := by rw [hsq hb, mul_one]
  have hy'b : (x * y * x⁻¹) * b * (x * y * x⁻¹)⁻¹ = z * b := by
    calc (x * y * x⁻¹) * b * (x * y * x⁻¹)⁻¹ = x * (y * (x⁻¹ * b * x) * y⁻¹) * x⁻¹ := by group
      _ = (x * z * x⁻¹) * (x * a * x⁻¹) := by rw [hxib, hya]; group
      _ = z * b := by rw [hxz, hxa]
  have hyy'a : (y * (x * y * x⁻¹)) * a * (y * (x * y * x⁻¹))⁻¹ = e * a := by
    calc (y * (x * y * x⁻¹)) * a * (y * (x * y * x⁻¹))⁻¹ =
          y * ((x * y * x⁻¹) * a * (x * y * x⁻¹)⁻¹) * y⁻¹ := by group
      _ = (y * z * y⁻¹) * (y * e * y⁻¹) * (y * a * y⁻¹) := by rw [hy'a]; group
      _ = z * e * (z * a) := by rw [hyz, hye, hya]
      _ = e * a := by
          rw [hcomm hzV heV, mul_assoc e z (z * a), ← mul_assoc z z a, hsq hzV, one_mul]
  have hyy'b : (y * (x * y * x⁻¹)) * b * (y * (x * y * x⁻¹))⁻¹ = z * e * b := by
    calc (y * (x * y * x⁻¹)) * b * (y * (x * y * x⁻¹))⁻¹ =
          y * ((x * y * x⁻¹) * b * (x * y * x⁻¹)⁻¹) * y⁻¹ := by group
      _ = (y * z * y⁻¹) * (y * b * y⁻¹) := by rw [hy'b]; group
      _ = z * e * b := by rw [hyz, hyb, mul_assoc]

  intro r hr
  obtain ⟨ε₁, hε₁, hra⟩ := hcases r hr a haV'
  obtain ⟨ε₂, hε₂, hrb⟩ := hcases r hr b hb
  obtain ⟨w, hwQH, hwa, hwb⟩ : ∃ w ∈ pCoreOf 2 H, w * a * w⁻¹ = ε₁ * a ∧
      w * b * w⁻¹ = ε₂ * b := by
    have hyy' : y * (x * y * x⁻¹) ∈ pCoreOf 2 H := mul_mem hyQH hxQH
    have hzz : z * z = 1 := hsq hzV
    rcases S14.eq_of_mem_V1_F4 hz hz1 hε₁ with rfl | rfl <;>
      rcases S14.eq_of_mem_V1_F4 hz hz1 hε₂ with rfl | rfl <;>
      rcases S14.eq_of_mem_V1_F4 hz hz1 he with rfl | rfl
    · exact ⟨1, one_mem _, by group, by group⟩
    · exact ⟨1, one_mem _, by group, by group⟩
    · exact ⟨_, hyy', by rw [hyy'a], by rw [hyy'b, mul_one]⟩
    · exact ⟨_, hxQH, by rw [hy'a, hzz], by rw [hy'b]⟩
    · exact ⟨y, hyQH, hya, by rw [hyb]⟩
    · exact ⟨_, hyy', by rw [hyy'a], by rw [hyy'b, hzz]⟩
    · exact ⟨_, hxQH, by rw [hy'a, mul_one], by rw [hy'b]⟩
    · exact ⟨y, hyQH, hya, by rw [hyb]⟩
  have hc : w⁻¹ * r ∈ T ⊓ Subgroup.centralizer (V : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem (hQHT hwQH)) (hR1T hr),
      Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    have hconj : (w⁻¹ * r) * v * (w⁻¹ * r)⁻¹ = v := by
      refine conj_eq_of_basis_F4 S14 hz hz1 ha haV hb hbV ?_ ?_ ?_ hv
      · rw [show w⁻¹ * r * z * (w⁻¹ * r)⁻¹ = w⁻¹ * (r * z * r⁻¹) * w by group,
          conj_fsuV1 hz (hR1T hr), show w⁻¹ * z * w = w⁻¹ * z * w⁻¹⁻¹ by group,
          conj_fsuV1 hz (inv_mem (hQHT hwQH))]
      · rw [show w⁻¹ * r * a * (w⁻¹ * r)⁻¹ = w⁻¹ * (r * a * r⁻¹) * w by group, hra, ← hwa]
        group
      · rw [show w⁻¹ * r * b * (w⁻¹ * r)⁻¹ = w⁻¹ * (r * b * r⁻¹) * w by group, hrb, ← hwb]
        group
    calc v * (w⁻¹ * r) = ((w⁻¹ * r) * v * (w⁻¹ * r)⁻¹) * (w⁻¹ * r) := by rw [hconj]
      _ = (w⁻¹ * r) * v := by group
  rw [hF.cT] at hc
  rw [show r = w * (w⁻¹ * r) by group]
  exact mul_mem (Subgroup.mem_sup_right hwQH) (Subgroup.mem_sup_left hc)

end L32A

end CFSG.Quasithin.H13
