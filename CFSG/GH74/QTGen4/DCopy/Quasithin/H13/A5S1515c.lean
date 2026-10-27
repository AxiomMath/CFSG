module

public import CFSG.Quasithin.H13.A5S1515c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1515b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5Top

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.A5.Orth

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

namespace Pf1515_F4
open CFSG.Quasithin.H13.A5.Setting.Pf1515_F4

variable {S : Setting G T L V} {H : Subgroup G} (P : Pf1515_F4 S H)
include P

theorem t21_props_F4 : P.t2_F4 * P.t1_F4 ≠ 1 ∧ (P.t2_F4 * P.t1_F4) ^ 3 = 1 := by
  have e : P.t2_F4 * P.t1_F4 = (P.t1_F4 * P.t2_F4)⁻¹ := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_left P.t1_props_F4.2.2.1,
      inv_eq_of_mul_eq_one_left P.t2_props_F4.2.2.1]
  rw [e, inv_pow, P.t12_props_F4.2, inv_one]
  exact ⟨fun h => P.t12_props_F4.1 (inv_eq_one.1 h), rfl⟩

theorem inSA_mem_F4 {x : MulAut (Multiplicative V4)} (hx : InSA P.t1_F4 P.t2_F4 x) :
    ∃ y : ↥H, (y : G) ∈ V ⊔ conjSub P.g⁻¹ V ∧ P.Φ_F4 y = x := by
  have ha : P.v ∈ V ⊔ conjSub P.g⁻¹ V := le_sup_left (a := V) P.v_mem
  have hb : P.g⁻¹ * P.v * P.g ∈ V ⊔ conjSub P.g⁻¹ V :=
    le_sup_right (b := conjSub P.g⁻¹ V) P.v'_mem_F4
  set a : ↥H := ⟨P.v, P.v_mem_H_F4⟩ with hadef
  set b : ↥H := ⟨P.g⁻¹ * P.v * P.g, P.v'_mem_H_F4⟩ with hbdef
  have hta : P.t1_F4 = P.Φ_F4 a := rfl
  have htb : P.t2_F4 = P.Φ_F4 b := rfl
  unfold InSA at hx
  rw [hta, htb] at hx
  rcases hx with h | h | h | h | h | h
  · exact ⟨1, Subgroup.one_mem _, by rw [h, map_one]⟩
  · exact ⟨a, ha, h.symm⟩
  · exact ⟨b, hb, h.symm⟩
  · exact ⟨a * b, Subgroup.mul_mem _ ha hb, by rw [h, map_mul]⟩
  · exact ⟨b * a, Subgroup.mul_mem _ hb ha, by rw [h, map_mul]⟩
  · exact ⟨a * (b * a), Subgroup.mul_mem _ ha (Subgroup.mul_mem _ hb ha),
      by rw [h, map_mul, map_mul]⟩

theorem Q_le_I_F4 : pCoreOf 2 H ≤ V ⊔ conjSub P.g⁻¹ V := P.Q_eq_U_F4 ▸ P.U_le_I_F4

theorem mem_I_of_Φ_eq_F4 {x y : ↥H} (hy : (y : G) ∈ V ⊔ conjSub P.g⁻¹ V) (h : P.Φ_F4 x = P.Φ_F4 y) :
    (x : G) ∈ V ⊔ conjSub P.g⁻¹ V := by
  have hq := P.Q_le_I_F4 ((P.Φ_eq_iff_F4 x y).1 h)
  have := (V ⊔ conjSub P.g⁻¹ V).mul_mem hq hy
  simpa using this

theorem conj_mem_I_F4 (x : ↥H) {s : ↥H} (hs : P.Φ_F4 s = P.t1_F4 ∨ P.Φ_F4 s = P.t2_F4) :
    (x : G) * s * (x : G)⁻¹ ∈ V ⊔ conjSub P.g⁻¹ V := by
  have hc : P.ch_F4 ∈ Oq ∧ P.ch_F4 ≠ 1 ∧ P.ch_F4 ^ 3 = 1 := P.ch_props_F4
  have hcases : InSA P.t1_F4 P.t2_F4 (P.Φ_F4 x * P.Φ_F4 s * (P.Φ_F4 x)⁻¹) := by
    rcases hs with hs | hs
    · rw [hs]
      exact normalizes_S3_aut hc.1 P.t1_props_F4.1 P.t2_props_F4.1 (P.Φ_mem_F4 x) hc.2
        P.t1_props_F4.2 P.t2_props_F4.2 P.t12_props_F4 (P.Φ_normalizes_F4 x)
    · rw [hs]
      exact inSA_swap P.t1_props_F4.2.2.1 P.t2_props_F4.2.2.1 P.t12_props_F4.2
        (normalizes_S3_aut hc.1 P.t2_props_F4.1 P.t1_props_F4.1 (P.Φ_mem_F4 x) hc.2
          P.t2_props_F4.2 P.t1_props_F4.2 P.t21_props_F4 (P.Φ_normalizes_F4 x))
  obtain ⟨y, hyI, hy⟩ := P.inSA_mem_F4 hcases
  exact P.mem_I_of_Φ_eq_F4 (x := x * s * x⁻¹) hyI (by rw [map_mul, map_mul, map_inv, hy])

theorem I_normal_F4 : H ≤ Subgroup.normalizer ((V ⊔ conjSub P.g⁻¹ V : Subgroup G) : Set G) := by
  have hQI := P.Q_le_I_F4
  have hNQ : ∀ x ∈ H, ∀ q ∈ pCoreOf 2 H, x * q * x⁻¹ ∈ pCoreOf 2 H := fun x hx q hq =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hx) q).mp hq

  have hV : ∀ x : ↥H, ∀ w ∈ V, (x : G) * w * (x : G)⁻¹ ∈ V ⊔ conjSub P.g⁻¹ V := by
    intro x w hw
    rcases P.V_cases_F4 hw with h | h
    · exact hQI (hNQ x x.2 w h)
    · have h1 := hQI (hNQ x x.2 _ h)
      have h2 : (x : G) * P.v * (x : G)⁻¹ ∈ V ⊔ conjSub P.g⁻¹ V :=
        P.conj_mem_I_F4 x (s := ⟨P.v, P.v_mem_H_F4⟩) (Or.inl rfl)
      have := (V ⊔ conjSub P.g⁻¹ V).mul_mem h1 h2
      have e : (x : G) * (w * P.v⁻¹) * (x : G)⁻¹ * ((x : G) * P.v * (x : G)⁻¹) =
          (x : G) * w * (x : G)⁻¹ := by group
      rwa [e] at this
  have hV' : ∀ x : ↥H, ∀ w ∈ conjSub P.g⁻¹ V,
      (x : G) * w * (x : G)⁻¹ ∈ V ⊔ conjSub P.g⁻¹ V := by
    intro x w hw
    have hw2 := hw
    rw [mem_conjSub, inv_inv] at hw2
    have hgi := H.inv_mem P.g_mem
    rcases P.V_cases_F4 hw2 with h | h
    · have hwQ : w ∈ pCoreOf 2 H := by
        have := hNQ _ hgi _ h
        simpa [mul_assoc] using this
      exact hQI (hNQ x x.2 w hwQ)
    · have hwQ : w * (P.g⁻¹ * P.v * P.g)⁻¹ ∈ pCoreOf 2 H := by
        have := hNQ _ hgi _ h
        have e : P.g⁻¹ * (P.g * w * P.g⁻¹ * P.v⁻¹) * P.g⁻¹⁻¹ = w * (P.g⁻¹ * P.v * P.g)⁻¹ := by
          group
        rwa [e] at this
      have h1 := hQI (hNQ x x.2 _ hwQ)
      have h2 : (x : G) * (P.g⁻¹ * P.v * P.g) * (x : G)⁻¹ ∈ V ⊔ conjSub P.g⁻¹ V :=
        P.conj_mem_I_F4 x (s := ⟨_, P.v'_mem_H_F4⟩) (Or.inr rfl)
      have := (V ⊔ conjSub P.g⁻¹ V).mul_mem h1 h2
      have e : (x : G) * (w * (P.g⁻¹ * P.v * P.g)⁻¹) * (x : G)⁻¹ *
          ((x : G) * (P.g⁻¹ * P.v * P.g) * (x : G)⁻¹) = (x : G) * w * (x : G)⁻¹ := by group
      rwa [e] at this
  refine le_normalizer_of_conj_mem fun x hx y hy => ?_
  have hmap : (V ⊔ conjSub P.g⁻¹ V).map (MulAut.conj x).toMonoidHom ≤ V ⊔ conjSub P.g⁻¹ V := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨w, hw, rfl⟩
      exact hV ⟨x, hx⟩ w hw
    · rintro _ ⟨w, hw, rfl⟩
      exact hV' ⟨x, hx⟩ w hw
  exact hmap ⟨y, hy, rfl⟩

theorem centralizer_le_Φ_F4 {b : MulAut (Multiplicative V4)} (hb : b ∈ Oq)
    (hbc : b * P.ch_F4 = P.ch_F4 * b) :
    ∃ x : ↥H, (x : G) ∈ S.L1 ⊔ (V ⊔ conjSub P.g⁻¹ V) ∧ P.Φ_F4 x = b := by
  have hc := P.ch_props_F4
  have hcube : P.ch_F4 * P.ch_F4 * P.ch_F4 = 1 := by rw [← pow_three']; exact hc.2.2
  have hcL : (P.c : G) ∈ S.L1 ⊔ (V ⊔ conjSub P.g⁻¹ V) := le_sup_left (a := S.L1) P.c_mem
  have hIY : V ⊔ conjSub P.g⁻¹ V ≤ S.L1 ⊔ (V ⊔ conjSub P.g⁻¹ V) := le_sup_right
  rcases centralizer_S3_aut hc.1 P.t1_props_F4.1 P.t2_props_F4.1 hb hc.2 P.t1_props_F4.2
    P.t2_props_F4.2 P.t12_props_F4 hbc with h | h | h
  · obtain ⟨y, hyI, hy⟩ := P.inSA_mem_F4 h
    exact ⟨y, hIY hyI, hy⟩
  ·
    obtain ⟨y, hyI, hy⟩ := P.inSA_mem_F4 h
    refine ⟨⟨P.c, P.c_mem_H_F4⟩ * y, Subgroup.mul_mem _ hcL (hIY hyI), ?_⟩
    rw [map_mul, hy]
    show P.ch_F4 * (P.ch_F4 * P.ch_F4 * b) = b
    calc P.ch_F4 * (P.ch_F4 * P.ch_F4 * b) = P.ch_F4 * P.ch_F4 * P.ch_F4 * b := by group
      _ = b := by rw [hcube, one_mul]
  ·
    obtain ⟨y, hyI, hy⟩ := P.inSA_mem_F4 h
    refine ⟨⟨P.c, P.c_mem_H_F4⟩ * ⟨P.c, P.c_mem_H_F4⟩ * y,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hcL hcL) (hIY hyI), ?_⟩
    rw [map_mul, map_mul, hy]
    show P.ch_F4 * P.ch_F4 * (P.ch_F4 * b) = b
    calc P.ch_F4 * P.ch_F4 * (P.ch_F4 * b) = P.ch_F4 * P.ch_F4 * P.ch_F4 * b := by group
      _ = b := by rw [hcube, one_mul]

theorem H_eq_gen_F4 : H = S.L1 ⊔ (V ⊔ conjSub P.g⁻¹ V) ⊔ T := by
  apply le_antisymm
  · refine le_sup_of_sq_mem (B2F.le_normalizer_sup P.hn P.I_normal_F4)
      (fun x hx => ?_) P.hF_F4.sylow_H
    have hsq := sq_comm_of_normalizes P.ch_props_F4.2.2 (P.Φ_normalizes_F4 ⟨x, hx⟩)
    rw [← map_mul] at hsq
    obtain ⟨y, hyY, hy⟩ := P.centralizer_le_Φ_F4 (P.Φ_mem_F4 _) hsq

    have hq := (P.Φ_eq_iff_F4 _ _).1 hy.symm
    have h1 := (le_sup_right : V ⊔ conjSub P.g⁻¹ V ≤ S.L1 ⊔ (V ⊔ conjSub P.g⁻¹ V))
      (P.Q_le_I_F4 hq)
    have := Subgroup.mul_mem _ h1 hyY
    rw [pow_two]
    simpa using this
  · exact sup_le (sup_le P.L1_le_H_F4 P.I_le_H_F4) P.T_le_H_F4

theorem dvd_card_range_F4 : 18 ∣ Nat.card P.Φ_F4.range := by
  rw [← card_centralizer_aut P.ch_props_F4.1 P.ch_props_F4.2]
  refine Subgroup.card_dvd_of_le fun b hb => ?_
  obtain ⟨x, -, hx⟩ := P.centralizer_le_Φ_F4 hb.1 (Subgroup.mem_centralizer_singleton_iff.mp hb.2)
  exact ⟨x, hx⟩

theorem z_central_F4 (u : G) (hu : u ∈ conjClosure S.V3 H) : S.z * u = u * S.z :=
  (P.comm_z_F4 (P.U_le_Q_F4.trans (pCoreOf_le 2 H) hu)).symm

theorem center_Q_F4 : centerOf (pCoreOf 2 H) = S.V1 := by
  rw [P.Q_eq_U_F4]
  apply le_antisymm
  · rintro x ⟨hx, hxc⟩
    refine P.mem_V1_of_central_F4 hx fun u hu => ?_
    exact (Subgroup.mem_centralizer_iff.mp hxc u hu).symm
  · intro x hx
    have hxU : x ∈ conjClosure S.V3 H := le_conjClosure S.V3 H (S.V1_le_V3 hx)
    refine ⟨hxU, ?_⟩
    show x ∈ Subgroup.centralizer (conjClosure S.V3 H : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    rcases S.mem_V1.1 hx with rfl | rfl
    · simp
    · exact (P.z_central_F4 u hu).symm

theorem G1_mem_Hz_F4 : S.G1 ∈ S.Hz := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨⟨P.hH.1.1.trans P.hH.2.1, fun h => ?_⟩, le_rfl, fun h => P.hH.2.2 (P.hH.2.1.trans h)⟩
  have hV1 : S.V1 ≤ pCoreOf 2 S.G1 := by
    refine le_pCoreOf_of_le_normalizer 2 ?_ ?_ (S.isPGroup_V.to_le S.V1_le_V)
    · rw [← S.centralizer_V1]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rcases S.mem_V1.1 hx with rfl | rfl <;> rcases S.mem_V1.1 hy with rfl | rfl <;> simp
    · rw [S.G1_eq_normalizer]
  rw [h, le_bot_iff] at hV1
  have := S.card_V1
  rw [hV1] at this
  simp at this

theorem H_eq_G1_F4 : H = S.G1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hG1 := P.G1_mem_Hz_F4
  have hF1 := S.hypF91_F4 P.h1323 hG1
  have hHG1 : H ≤ S.G1 := P.hH.2.1
  have hTG1 : T ≤ S.G1 := P.T_le_H_F4.trans hHG1

  have hQ1T : pCoreOf 2 S.G1 ≤ T := by
    obtain ⟨P', hP'⟩ := exists_sylow_of_quasithinIsSylowTwo S.h13.sylow
    have := pCoreOf_two_le_sylow S.G1 P' (hP' ▸ hTG1)
    rwa [hP'] at this
  have hQ1Q : pCoreOf 2 S.G1 ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 (hQ1T.trans P.T_le_H_F4)
      (hHG1.trans (le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
  have hUU1 : conjClosure S.V3 H ≤ conjClosure S.V3 S.G1 := conjClosure_mono le_rfl hHG1
  have hU1Q1 : conjClosure S.V3 S.G1 ≤ pCoreOf 2 S.G1 := hF1.conjClosure_Vp_le_pCoreOf
  have hQ1 : pCoreOf 2 S.G1 = conjClosure S.V3 H :=
    le_antisymm (hQ1Q.trans P.Q_eq_U_F4.le) (hUU1.trans hU1Q1)
  have hU1 : conjClosure S.V3 S.G1 = conjClosure S.V3 H :=
    le_antisymm (hU1Q1.trans hQ1.le) hUU1

  have hG1N : S.G1 ≤ Subgroup.normalizer (conjClosure S.V3 H : Set G) :=
    hQ1 ▸ le_normalizer_pCoreOf 2 S.G1
  have hG1z : S.G1 ≤ Subgroup.centralizer ({P.C.z} : Set G) := by rw [P.Cz]; exact le_rfl
  have hker1 : (P.C.act S.G1 hG1N hG1z).ker = (pCoreOf 2 S.G1).subgroupOf S.G1 := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Q8Coords.act_eq_one_iff, hF1.F92_3.1, hU1,
      mem_centralizerMod]
    constructor
    · intro h
      refine ⟨x.2, hF1.H_normalizes_V₁ x.2, fun u hu => ?_⟩
      rw [S.mem_V1, ← P.Cz]
      exact h u hu
    · intro h u hu
      have := h.2.2 u hu
      rwa [S.mem_V1, ← P.Cz] at this
  have hcard1 : Nat.card S.G1 =
      Nat.card (pCoreOf 2 S.G1) * Nat.card (P.C.act S.G1 hG1N hG1z).range := by
    rw [← Subgroup.card_mul_index ((pCoreOf 2 S.G1).subgroupOf S.G1), ← hker1,
      Subgroup.index_ker, hker1]
    congr 1
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (pCoreOf_le 2 S.G1)).toEquiv
  have hrange1 : Nat.card (P.C.act S.G1 hG1N hG1z).range ∣ 72 := by
    rw [← card_Oq]
    exact Subgroup.card_dvd_of_le fun b ⟨x, hx⟩ => hx ▸ P.C.act_mem_Oq _ _ _ x

  have hkerH : P.Φ_F4.ker = (pCoreOf 2 H).subgroupOf H := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, P.Φ_eq_one_iff_F4]
  have hcardH : Nat.card H = Nat.card (pCoreOf 2 H) * Nat.card P.Φ_F4.range := by
    rw [← Subgroup.card_mul_index ((pCoreOf 2 H).subgroupOf H), ← hkerH,
      Subgroup.index_ker, hkerH]
    congr 1
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (pCoreOf_le 2 H)).toEquiv

  have hQeq : Nat.card (pCoreOf 2 S.G1) = Nat.card (pCoreOf 2 H) := by
    rw [hQ1, P.Q_eq_U_F4]
  have hpos : 0 < Nat.card (pCoreOf 2 H) := Nat.card_pos
  obtain ⟨k, hk⟩ := P.dvd_card_range_F4
  obtain ⟨m, hm⟩ := hrange1
  have hidx := Subgroup.card_mul_index (H.subgroupOf S.G1)
  have hHcard : Nat.card ↥(H.subgroupOf S.G1) = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHG1).toEquiv
  rw [hHcard] at hidx
  have hodd : ¬ 2 ∣ (H.subgroupOf S.G1).index := by
    intro h2
    have hT := isSylowTwoOf_of_le S.h13.sylow hTG1
    apply hT.2.2
    exact h2.trans (Subgroup.index_dvd_of_le fun x hx => P.T_le_H_F4 hx)

  generalize hn : (H.subgroupOf S.G1).index = n at hidx hodd
  have h4 : n ∣ 4 := by
    have e1 : Nat.card (pCoreOf 2 H) * (18 * k * n * m) = Nat.card (pCoreOf 2 H) * 72 := by
      have := hcard1
      rw [hQeq, ← hidx, hcardH, hk] at this
      calc Nat.card (pCoreOf 2 H) * (18 * k * n * m)
          = Nat.card (pCoreOf 2 H) * (18 * k) * n * m := by ring
        _ = Nat.card (pCoreOf 2 H) * Nat.card ↥(P.C.act S.G1 hG1N hG1z).range * m := by
          rw [this]
        _ = Nat.card (pCoreOf 2 H) * 72 := by rw [hm]; ring
    have e2 : 18 * k * n * m = 72 := Nat.eq_of_mul_eq_mul_left hpos e1
    exact ⟨k * m, by nlinarith [e2]⟩
  have hn1 : n = 1 := by
    have hle := Nat.le_of_dvd (by norm_num) h4
    interval_cases n <;> omega
  have := Subgroup.index_eq_one.1 (hn.trans hn1)
  apply le_antisymm hHG1
  intro x hx
  have : (⟨x, hx⟩ : ↥S.G1) ∈ H.subgroupOf S.G1 := this ▸ Subgroup.mem_top _
  exact this

end Pf1515_F4

theorem nonempty_pf1515_F4 (h1323 : Input1323Two_F4) (h1326 : Input1326Two_F4) (h1336 : Input1336_F4)
    (hF956 : StmtF956i) (hG248 : StmtG248) (hC113 : StmtC113c) (S : Setting G T L V)
    {H : Subgroup G} (hH : H ∈ S.Hz) (hn : H ≤ Subgroup.normalizer (S.L1 : Set G))
    (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H)) : Nonempty (Pf1515_F4 S H) := by
  obtain ⟨g, hg, hQ8, hS3, hUI⟩ := S.F956_data_F4 h1323 h1326 h1336 hF956 hH hna
  obtain ⟨l, hl, hlN⟩ := S.exists_L_not_normalizer_V1
  obtain ⟨-, -, -, -, -, hUQ8⟩ := S.G248_data_F4 h1323 hG248 hH hn hna hl hlN
  obtain ⟨C⟩ := nonempty_q8Coords hUQ8
  obtain ⟨c, hcL, hc⟩ := S.exists_L1_of_three c3p_props.1 c3p_props.2.1 c3p_props.2.2
  obtain ⟨v, hv, hvQ⟩ := IsConcreteLE.not_le_iff_exists.1 (S.not_V_le_QH_F4 h1323 hH hna)

  have hzU : S.z ∈ conjClosure S.V3 H := le_conjClosure _ _ S.z_mem_V3
  have hUH : conjClosure S.V3 H ≤ H :=
    (S.hypF91_F4 h1323 hH).conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)
  have hCz : C.z = S.z := by
    have := C.center ⟨S.z, hzU⟩ fun u => Subtype.ext
      (Subgroup.mem_centralizer_singleton_iff.mp (hH.2.1 (hUH u.2))).symm
    rcases this with h | h
    · exact absurd h S.z_ne_one
    · exact h.symm
  exact ⟨⟨h1323, hG248, hC113, hH, hn, hna, g, hg, hQ8, hS3, hUI, C, hCz, c, hcL, hc, v, hv,
    hvQ⟩⟩

theorem data13515_F4 (h1323 : Input1323Two_F4) (h1326 : Input1326Two_F4) (h1336 : Input1336_F4)
    (hF956 : StmtF956i) (hG248 : StmtG248) (hC113 : StmtC113c) (S : Setting G T L V)
    {H : Subgroup G} (hH : H ∈ S.Hz) (hn : H ≤ Subgroup.normalizer (S.L1 : Set G))
    (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H)) : ∃ I : Subgroup G, Data13515 S H I := by
  obtain ⟨P⟩ := nonempty_pf1515_F4 h1323 h1326 h1336 hF956 hG248 hC113 S hH hn hna
  refine ⟨V ⊔ conjSub P.g⁻¹ V, ?_⟩
  obtain ⟨-, -, hcard, hS3⟩ := P.Idata_F4
  exact
    { H_eq := P.H_eq_G1_F4
      M_eq := P.normalizer_L_F4
      V_eq := P.pCoreOf_LT_F4
      center_QH := P.center_Q_F4
      I_le := P.I_le_H_F4
      I_normal := P.I_normal_F4
      I_S3 := hS3
      card_O2_I := hcard
      H_eq_gen := P.H_eq_gen_F4 }

end Setting

theorem input13515_of_F4 (h1323 : Input1323Two_F4) (h1326 : Input1326Two_F4) (h1336 : Input1336_F4)
    (hF956 : StmtF956i) (hG248 : StmtG248) (hC113 : StmtC113c) : Input13515_F4 :=
  fun _ _ _ _ _ _ S _ hH hn hna => S.data13515_F4 h1323 h1326 h1336 hF956 hG248 hC113 hH hn hna

end CFSG.Quasithin.H13.A5
