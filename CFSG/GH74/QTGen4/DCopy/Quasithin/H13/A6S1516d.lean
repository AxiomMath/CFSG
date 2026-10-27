module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1515d
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1516
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1516c

public section

namespace CFSG.Quasithin.H13

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.A5.Orth

namespace A6

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

section Data

variable
  (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hhat : ¬ IsHatA6 L)
  (hn : H ≤ Subgroup.normalizer (S.L1 : Set G)) (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H))
  {l : ↥(Subgroup.normalizer (V : Set G))} (hlL : (l : G) ∈ L) (hl : S.frame.ρ l = lK)
  (hobl : Obl13_5_14Six_F4) (hctk : Input13515CTK_F4) (hTL : ¬ T ≤ L)
  {SY : A5SitY (S.toA5Sit_F4 hNS h13315 h1356two hH hna) S.L1}
  (P : A5SitPf15 (S.toA5Sit_F4 hNS h13315 h1356two hH hna) SY)
include hNS h13315 h1356two hH hhat hn hna hlL hl hobl hctk hTL P

omit hTL in

theorem sign_ne_of_Z1_F4 {j : G} (hjZ : j ∈ P.Z1) (hjV : j ∉ fsuV1 T V)
    (hjN : j ∈ Subgroup.normalizer (V : Set G)) : Perm.sign (S.frame.ρ ⟨j, hjN⟩) ≠ 1 := by
  set A := S.toA5Sit_F4 hNS h13315 h1356two hH hna
  have hjQ : j ∈ pCoreOf 2 H := hjZ.1
  rcases S.rho_Q_F4 hNS h13315 h1356two hH hhat hjQ hjN with hK | hK
  · exfalso
    have hUL1 := S.UH_le_L1_six_F4 hNS h13315 h1356two hH hn hna
    obtain ⟨-, hsurj⟩ := S.lemma13_5_14_two_F4 hNS h1356two h13315 hH hUL1 hna
    obtain ⟨u, hu, hρu⟩ := hsurj _ hK
    have huN : u ∈ Subgroup.normalizer (V : Set G) :=
      S.frame.L_le (S.L1_le.trans inf_le_left (hUL1 hu))
    have hc : S.frame.ρ ((⟨u, huN⟩ : ↥(Subgroup.normalizer (V : Set G)))⁻¹ * ⟨j, hjN⟩) = 1 := by
      rw [map_mul, map_inv, hρu, inv_mul_cancel]
    have hcC := (S.rho_eq_one_iff _).1 hc
    have hF := S.hypF91_F4 hNS h13315 h1356two hH
    have hQT : pCoreOf 2 H ≤ T := pCoreOf_two_le_of_isSylowTwoOf hF.sylow_H
    have huT : u ∈ T := S.UH_le_T_F4 hNS h1356two h13315 hH hu
    have hTV : T ⊓ Subgroup.centralizer (V : Set G) = V :=
      S.cT_eq_V_F4 hNS h13315 h1356two hH hhat hn hna hlL hl hobl hctk
    have hcV : u⁻¹ * j ∈ V := by
      rw [← hTV]
      exact ⟨T.mul_mem (T.inv_mem huT) (hQT hjQ), hcC⟩
    have hcQ : u⁻¹ * j ∈ pCoreOf 2 H :=
      (pCoreOf 2 H).mul_mem ((pCoreOf 2 H).inv_mem (A.U_le_Q hu)) hjQ
    have hc3 : u⁻¹ * j ∈ S.V3 := by
      rw [← A.inf_Q_eq]
      exact ⟨hcV, hcQ⟩
    have hjU : j ∈ conjClosure S.V3 H := by
      have := (conjClosure S.V3 H).mul_mem hu (le_conjClosure _ _ hc3)
      simpa using this
    apply hjV
    have h : j ∈ conjClosure S.V3 H ⊓ P.Z1 := ⟨hjU, hjZ⟩
    rwa [P.U_inf_Z1] at h
  · exact sign_ne_of_mul_swap_mem hK

theorem not_conj_of_Z1_F4
    {j : G} (hjZ : j ∈ P.Z1) (hjV : j ∉ fsuV1 T V) (g : G) :
    g * S.z * g⁻¹ ≠ j := by
  intro hg
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ := S.card_Q_six_F4 hNS h13315 h1356two hH hhat hn hna hlL hl hobl hctk hTL
  have hHG := S.H_eq_G1_six_S6_F4 hNS h13315 h1356two hH hhat hn hna hlL hl hobl hctk hTL
  have hz := S.C_z_eq_F4 hNS h13315 h1356two hH hna P
  have hHz : H = Subgroup.centralizer ({S.z} : Set G) := hHG
  have hF := S.hypF91_F4 hNS h13315 h1356two hH
  have hNQ : Subgroup.normalizer (pCoreOf 2 H : Set G) ≤ H := by
    have h := P.normalizer_Q_le hQ
    rw [hz, ← hHz] at h
    exact h
  have hHZ : H ≤ Subgroup.normalizer (P.Z1 : Set G) :=
    (le_normalizer_pCoreOf 2 H).trans (P.normalizer_le_Z1 hQ)
  have hV1c : ∀ h ∈ H, ∀ v ∈ fsuV1 T V, v * h = h * v := fun h hh v hv =>
    Subgroup.mem_centralizer_iff.mp (hF.H_le_centralizer hh) v hv

  have hconjV : ∀ h ∈ H, h * j * h⁻¹ * j⁻¹ ∈ fsuV1 T V := by
    intro h hh
    have hjh : h * j * h⁻¹ ∈ P.Z1 := (Subgroup.mem_normalizer_iff.mp (hHZ hh) j).mp hjZ
    have hjh' : h * j * h⁻¹ ∉ fsuV1 T V := by
      intro hv
      apply hjV
      have hc := hV1c h hh _ hv
      have e : j = h * j * h⁻¹ := by
        calc j = h⁻¹ * ((h * j * h⁻¹) * h) := by group
          _ = h⁻¹ * (h * (h * j * h⁻¹)) := by rw [hc]
          _ = h * j * h⁻¹ := by group
      rw [e]
      exact hv
    exact P.mul_inv_mem_V1 hQ hjh hjZ hjh' hjV
  have hjH : j ∈ H := pCoreOf_le 2 H hjZ.1
  let ψ : ↥H →* ↥(fsuV1 T V) :=
    { toFun := fun h => ⟨h * j * h⁻¹ * j⁻¹, hconjV h h.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun h h' => by
        apply Subtype.ext
        show (h * h' : G) * j * (h * h' : G)⁻¹ * j⁻¹ =
          ((h : G) * j * (h : G)⁻¹ * j⁻¹) * ((h' : G) * j * (h' : G)⁻¹ * j⁻¹)
        have haV : (h' : G) * j * (h' : G)⁻¹ * j⁻¹ ∈ fsuV1 T V := hconjV h' h'.2
        have hb : (h : G) * j * (h : G)⁻¹ * j⁻¹ ∈ H :=
          H.mul_mem (H.mul_mem (H.mul_mem h.2 hjH) (H.inv_mem h.2)) (H.inv_mem hjH)
        have hha := hV1c h h.2 _ haV
        have hab := hV1c _ hb _ haV
        calc (h * h' : G) * j * (h * h' : G)⁻¹ * j⁻¹
            = (h : G) * ((h' : G) * j * (h' : G)⁻¹ * j⁻¹) * (h : G)⁻¹ *
                ((h : G) * j * (h : G)⁻¹ * j⁻¹) := by group
          _ = ((h' : G) * j * (h' : G)⁻¹ * j⁻¹) * ((h : G) * j * (h : G)⁻¹ * j⁻¹) := by
              rw [← hha]
              group
          _ = ((h : G) * j * (h : G)⁻¹ * j⁻¹) * ((h' : G) * j * (h' : G)⁻¹ * j⁻¹) := hab }

  set K := H ⊓ Subgroup.centralizer ({j} : Set G) with hK
  have hkerK : ψ.ker = K.subgroupOf H := by
    ext h
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h1
      have h2 : (h : G) * j * (h : G)⁻¹ * j⁻¹ = 1 := congrArg Subtype.val h1
      refine ⟨h.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      calc (h : G) * j = (h : G) * j * (h : G)⁻¹ * j⁻¹ * (j * h) := by group
        _ = j * h := by rw [h2, one_mul]
    · rintro ⟨-, hc⟩
      apply Subtype.ext
      show (h : G) * j * (h : G)⁻¹ * j⁻¹ = 1
      rw [Subgroup.mem_centralizer_singleton_iff.1 hc]
      group
  have hidxH : (K.subgroupOf H).index ≤ 2 := by
    rw [← hkerK, Subgroup.index_ker]
    calc Nat.card ψ.range ≤ Nat.card ↥(fsuV1 T V) := Subgroup.card_le_card_group _
      _ = 2 := S.card_V1

  have hQK : pCoreOf 2 H ≤ K := fun q hq => ⟨pCoreOf_le 2 H hq,
    Subgroup.mem_centralizer_singleton_iff.2 (P.Z1_comm_Q hQ hjZ hq).symm⟩
  have hKH : K ≤ H := inf_le_left
  have hHNK : H ≤ Subgroup.normalizer (K : Set G) := by
    refine A5.le_normalizer_of_forall_conj_mem fun h hh k hk => ?_
    have hk' : (⟨k, hKH hk⟩ : ↥H) ∈ ψ.ker := by rw [hkerK]; exact hk
    have := (MonoidHom.normal_ker ψ).conj_mem _ hk' ⟨h, hh⟩
    rw [hkerK, Subgroup.mem_subgroupOf] at this
    exact this
  have hO2K : pCoreOf 2 K = pCoreOf 2 H := by
    apply le_antisymm
    · exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K).trans hKH)
        (hHNK.trans (normalizer_le_normalizer_pCoreOf 2 K)) (pCoreOf_isPGroup 2 K)
    · exact le_pCoreOf_of_le_normalizer 2 hQK (hKH.trans (le_normalizer_pCoreOf 2 H))
        (pCoreOf_isPGroup 2 H)

  have hjconj : ∀ x : G, x * S.z = S.z * x → (g * x * g⁻¹) * j = j * (g * x * g⁻¹) := by
    intro x hx
    rw [← hg]
    calc g * x * g⁻¹ * (g * S.z * g⁻¹) = g * (x * S.z) * g⁻¹ := by group
      _ = g * (S.z * x) * g⁻¹ := by rw [hx]
      _ = g * S.z * g⁻¹ * (g * x * g⁻¹) := by group
  have hzconj : ∀ y : G, y * j = j * y → (g⁻¹ * y * g) * S.z = S.z * (g⁻¹ * y * g) := by
    intro y hy
    have hz' : S.z = g⁻¹ * j * g := by rw [← hg]; group
    rw [hz']
    calc g⁻¹ * y * g * (g⁻¹ * j * g) = g⁻¹ * (y * j) * g := by group
      _ = g⁻¹ * (j * y) * g := by rw [hy]
      _ = g⁻¹ * j * g * (g⁻¹ * y * g) := by group
  have hcardC : Nat.card (Subgroup.centralizer ({j} : Set G)) = Nat.card H := by
    rw [hHz]
    symm
    exact Nat.card_congr
      { toFun := fun x => ⟨g * x * g⁻¹, Subgroup.mem_centralizer_singleton_iff.2
          (hjconj x (Subgroup.mem_centralizer_singleton_iff.1 x.2))⟩
        invFun := fun y => ⟨g⁻¹ * y * g, Subgroup.mem_centralizer_singleton_iff.2
          (hzconj y (Subgroup.mem_centralizer_singleton_iff.1 y.2))⟩
        left_inv := fun x => Subtype.ext (by
          show g⁻¹ * (g * (x : G) * g⁻¹) * g = x
          group)
        right_inv := fun y => Subtype.ext (by
          show g * (g⁻¹ * (y : G) * g) * g⁻¹ = y
          group) }

  have hKC : K ≤ Subgroup.centralizer ({j} : Set G) := inf_le_right
  have hidxC : (K.subgroupOf (Subgroup.centralizer ({j} : Set G))).index ≤ 2 := by
    have h1 := Subgroup.card_mul_index (K.subgroupOf (Subgroup.centralizer ({j} : Set G)))
    have h2 := Subgroup.card_mul_index (K.subgroupOf H)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKC).toEquiv, hcardC] at h1
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv] at h2
    have hpos : 0 < Nat.card K := Nat.card_pos
    have : (K.subgroupOf (Subgroup.centralizer ({j} : Set G))).index =
        (K.subgroupOf H).index := Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)
    rw [this]
    exact hidxH
  have hCN : Subgroup.centralizer ({j} : Set G) ≤ Subgroup.normalizer (K : Set G) := by
    have hnorm : (K.subgroupOf (Subgroup.centralizer ({j} : Set G))).Normal := by
      rcases Nat.lt_or_ge (K.subgroupOf (Subgroup.centralizer ({j} : Set G))).index 2 with h | h
      · have h1 : (K.subgroupOf (Subgroup.centralizer ({j} : Set G))).index = 1 := by
          have := Subgroup.index_ne_zero_of_finite
            (H := K.subgroupOf (Subgroup.centralizer ({j} : Set G)))
          omega
        rw [Subgroup.index_eq_one.1 h1]
        infer_instance
      · exact Subgroup.normal_of_index_eq_two (by omega)
    refine A5.le_normalizer_of_forall_conj_mem fun c hc k hk => ?_
    have := hnorm.conj_mem ⟨k, hKC hk⟩ (Subgroup.mem_subgroupOf.2 hk) ⟨c, hc⟩
    rw [Subgroup.mem_subgroupOf] at this
    exact this

  have hCH : Subgroup.centralizer ({j} : Set G) ≤ H := by
    refine hCN.trans ((normalizer_le_normalizer_pCoreOf 2 K).trans ?_)
    rw [hO2K]
    exact hNQ
  have hCeq : Subgroup.centralizer ({j} : Set G) = H :=
    Subgroup.eq_of_le_of_card_ge hCH (le_of_eq hcardC.symm)

  have hgN : g ∈ Subgroup.normalizer (H : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [← hCeq]
      rw [hHz] at hh
      exact Subgroup.mem_centralizer_singleton_iff.2
        (hjconj h (Subgroup.mem_centralizer_singleton_iff.1 hh))
    · intro hh
      rw [← hCeq] at hh
      have h1 := hzconj _ (Subgroup.mem_centralizer_singleton_iff.1 hh)
      have e : g⁻¹ * (g * h * g⁻¹) * g = h := by group
      rw [e] at h1
      rw [hHz]
      exact Subgroup.mem_centralizer_singleton_iff.2 h1
  have hgH : g ∈ H := hNQ ((normalizer_le_normalizer_pCoreOf 2 H) hgN)
  have hgz : g * S.z = S.z * g := by
    rw [hHz] at hgH
    exact Subgroup.mem_centralizer_singleton_iff.1 hgH
  apply hjV
  rw [← hg, hgz, mul_inv_cancel_right]
  exact S.mem_V1_iff.2 (Or.inr rfl)

theorem comm_conj_of_sq_z_F4
    {j : G} (hjZ : j ∈ P.Z1) (hjV : j ∉ fsuV1 T V) (hj2 : j * j = S.z)
    {y : G} (hy1 : y⁻¹ * S.z * y ∈ pCoreOf 2 H) (hy2 : y * S.z * y⁻¹ ∈ pCoreOf 2 H)
    (hy3 : y⁻¹ * S.z * y ≠ S.z) : j * (y⁻¹ * j * y) = (y⁻¹ * j * y) * j := by
  have hQ := S.card_Q_six_F4 hNS h13315 h1356two hH hhat hn hna hlL hl hobl hctk hTL
  have hHG := S.H_eq_G1_six_S6_F4 hNS h13315 h1356two hH hhat hn hna hlL hl hobl hctk hTL
  have hHz : H = Subgroup.centralizer ({S.z} : Set G) := hHG
  have hF := S.hypF91_F4 hNS h13315 h1356two hH
  have hHZ : H ≤ Subgroup.normalizer (P.Z1 : Set G) :=
    (le_normalizer_pCoreOf 2 H).trans (P.normalizer_le_Z1 hQ)
  have hjH : j ∈ H := pCoreOf_le 2 H hjZ.1
  have hzz : S.z * S.z = 1 := by rw [← pow_two]; exact S.z_sq
  have hjc : ∀ q ∈ pCoreOf 2 H, j * q = q * j := fun q hq => P.Z1_comm_Q hQ hjZ hq
  set j' := y⁻¹ * j * y with hj'

  have hj'H : j' ∈ H := by
    rw [hHz, Subgroup.mem_centralizer_singleton_iff]
    have h := hjc _ hy2
    calc j' * S.z = y⁻¹ * (j * (y * S.z * y⁻¹)) * y := by rw [hj']; group
      _ = y⁻¹ * ((y * S.z * y⁻¹) * j) * y := by rw [h]
      _ = S.z * j' := by rw [hj']; group
  have hhH : y * j * y⁻¹ ∈ H := by
    rw [hHz, Subgroup.mem_centralizer_singleton_iff]
    have h := hjc _ hy1
    calc y * j * y⁻¹ * S.z = y * (j * (y⁻¹ * S.z * y)) * y⁻¹ := by group
      _ = y * ((y⁻¹ * S.z * y) * j) * y⁻¹ := by rw [h]
      _ = S.z * (y * j * y⁻¹) := by group

  set c := j⁻¹ * j'⁻¹ * j * j' with hc
  have hcZ : c ∈ P.Z1 := by
    have h1 : j'⁻¹ * j * j'⁻¹⁻¹ ∈ P.Z1 :=
      (Subgroup.mem_normalizer_iff.mp (hHZ (H.inv_mem hj'H)) j).mp hjZ
    rw [inv_inv] at h1
    have e : c = j⁻¹ * (j'⁻¹ * j * j') := by rw [hc]; group
    rw [e]
    exact P.Z1.mul_mem (P.Z1.inv_mem hjZ) h1
  have hcZy : y * c * y⁻¹ ∈ P.Z1 := by
    have h1 : (y * j * y⁻¹)⁻¹ * j⁻¹ * (y * j * y⁻¹)⁻¹⁻¹ ∈ P.Z1 :=
      (Subgroup.mem_normalizer_iff.mp (hHZ (H.inv_mem hhH)) j⁻¹).mp (P.Z1.inv_mem hjZ)
    rw [inv_inv] at h1
    have e : y * c * y⁻¹ = (y * j * y⁻¹)⁻¹ * j⁻¹ * (y * j * y⁻¹) * j := by
      rw [hc, hj']
      group
    rw [e]
    exact P.Z1.mul_mem h1 hjZ

  have hsqZ : ∀ x ∈ P.Z1, x ∉ fsuV1 T V → x * x = S.z := by
    intro x hx hxV
    have h := P.mul_inv_mem_V1 hQ hx hjZ hxV hjV
    set v := x * j⁻¹ with hv
    have hvc : v * j = j * v :=
      (Subgroup.mem_centralizer_iff.mp (hF.H_le_centralizer hjH) _ h)
    have hv2 : v * v = 1 := by
      rcases S.mem_V1_iff.1 h with h' | h'
      · rw [h', one_mul]
      · rw [h', hzz]
    have hxv : x = v * j := by rw [hv]; group
    calc x * x = v * j * (v * j) := by rw [← hxv]
      _ = v * (j * v) * j := by group
      _ = v * (v * j) * j := by rw [← hvc]
      _ = v * v * (j * j) := by group
      _ = S.z := by rw [hv2, one_mul, hj2]
  have hz1 : S.z ≠ 1 := S.z_ne_one

  have hyz : y * S.z * y⁻¹ ≠ S.z := by
    intro h
    apply hy3
    have e : y⁻¹ * (y * S.z * y⁻¹) * y = S.z := by group
    rw [h] at e
    exact e
  have hyz1 : y * S.z * y⁻¹ ≠ 1 := by
    intro h
    apply hz1
    calc S.z = y⁻¹ * (y * S.z * y⁻¹) * y := by group
      _ = 1 := by rw [h]; group
  have hc1 : c = 1 := by
    by_contra hc1
    by_cases hcV : c ∈ fsuV1 T V
    · have hcz : c = S.z := (S.mem_V1_iff.1 hcV).resolve_left hc1
      have hyzZ : y * S.z * y⁻¹ ∈ P.Z1 := by rw [← hcz]; exact hcZy
      have hyzV : y * S.z * y⁻¹ ∈ fsuV1 T V := by
        by_contra hn
        have h := hsqZ _ hyzZ hn
        apply hz1
        rw [← h]
        calc y * S.z * y⁻¹ * (y * S.z * y⁻¹) = y * (S.z * S.z) * y⁻¹ := by group
          _ = 1 := by rw [hzz]; group
      rcases S.mem_V1_iff.1 hyzV with h | h
      · exact hyz1 h
      · exact hyz h
    · have hc2 := hsqZ c hcZ hcV
      have hsq := P.sq_mem_V1 hQ (P.Z1_le_Q hcZy)
      have e : y * c * y⁻¹ * (y * c * y⁻¹) = y * S.z * y⁻¹ := by
        rw [← hc2]
        group
      rw [e] at hsq
      rcases S.mem_V1_iff.1 hsq with h | h
      · exact hyz1 h
      · exact hyz h
  calc j * j' = j' * j * (j⁻¹ * j'⁻¹ * j * j') := by group
    _ = j' * j := by rw [← hc, hc1, mul_one]

theorem exists_inv_not_conj_of_sq_z_F4
    {j : G} (hjZ : j ∈ P.Z1) (hjV : j ∉ fsuV1 T V)
    (hj2 : j * j = S.z) : ∃ a : G, a * a = 1 ∧ a ≠ 1 ∧ ∀ g : G, g * S.z * g⁻¹ ≠ a := by
  have hQ := S.card_Q_six_F4 hNS h13315 h1356two hH hhat hn hna hlL hl hobl hctk hTL
  have hHG := S.H_eq_G1_six_S6_F4 hNS h13315 h1356two hH hhat hn hna hlL hl hobl hctk hTL
  have hHz : H = Subgroup.centralizer ({S.z} : Set G) := hHG
  have hz := S.C_z_eq_F4 hNS h13315 h1356two hH hna P
  have hF := S.hypF91_F4 hNS h13315 h1356two hH
  set A := S.toA5Sit_F4 hNS h13315 h1356two hH hna
  have hQT : pCoreOf 2 H ≤ T := pCoreOf_two_le_of_isSylowTwoOf hF.sylow_H
  have hjN : j ∈ Subgroup.normalizer (V : Set G) := S.frame.T_le (hQT hjZ.1)
  have hzz : S.z * S.z = 1 := by rw [← pow_two]; exact S.z_sq

  obtain ⟨w₀, hw₀L, hw₀⟩ := (S.frame.image_L wK).2 (Perm.mem_alternatingGroup.2 wK_facts.1)
  have h3 : wK ^ 3 = 1 := by
    rw [pow_three, ← mul_assoc]
    exact wK_facts.2.1
  have hw₀3 : ((w₀ ^ 3 : ↥(Subgroup.normalizer (V : Set G))) : G) ∈ V :=
    S.mem_V_of_rho_F4 hNS h13315 h1356two hH hna hhat hn hlL hl hobl hctk
      (by rw [SubmonoidClass.coe_pow]; exact L.pow_mem hw₀L 3) (by rw [map_pow, hw₀, h3])
  have hw₀6 : w₀ ^ 6 = 1 := by
    apply Subtype.ext
    have h := S.elemAbelian_V.2 _ hw₀3
    rw [SubmonoidClass.coe_pow, ← pow_mul] at h
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    simpa using h
  set wN : ↥(Subgroup.normalizer (V : Set G)) := w₀ ^ 4 with hwN
  have hwN3 : wN ^ 3 = 1 := by
    rw [hwN, ← pow_mul, show 4 * 3 = 6 * 2 from rfl, pow_mul, hw₀6, one_pow]
  have hρw : S.frame.ρ wN = wK := by
    rw [hwN, map_pow, hw₀, show 4 = 3 + 1 from rfl, pow_succ, h3, one_mul]
  set w : G := (wN : G) with hw
  have hwL : w ∈ L := by rw [hw, hwN, SubmonoidClass.coe_pow]; exact L.pow_mem hw₀L 4
  have hw3 : w * w * w = 1 := by
    have : ((wN ^ 3 : ↥(Subgroup.normalizer (V : Set G))) : G) = 1 := by rw [hwN3]; rfl
    rw [SubmonoidClass.coe_pow, pow_three, ← mul_assoc] at this
    exact this
  have hwi : w⁻¹ = w * w := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact hw3)

  set z₁ := w⁻¹ * S.z * w with hz₁
  have hz₁V : z₁ ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ wN.2) S.z).mp S.z_mem_V
    simpa [hz₁, hw] using this
  have hψz₁ : ((S.frame.ψ ⟨z₁, hz₁V⟩ : ↥W4) : P6) = act4f wK⁻¹ e0123 := by
    have h := S.psi_conj_inv_coe wN S.z_mem_V hz₁V
    rw [hρw, S.psi_z] at h
    exact h
  set z₂ := w⁻¹ * z₁ * w with hz₂
  have hz₂V : z₂ ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ wN.2) z₁).mp hz₁V
    simpa [hz₂, hw] using this
  have hψz₂ : ((S.frame.ψ ⟨z₂, hz₂V⟩ : ↥W4) : P6) = act4f wK⁻¹ (act4f wK⁻¹ e0123) := by
    have h := S.psi_conj_inv_coe wN hz₁V hz₂V
    rw [hρw, hψz₁] at h
    exact h
  obtain ⟨-, -, hW1, hW2, hne1, hne2, hprod⟩ := wK_facts
  have hV2Q : ∀ x (hx : x ∈ V), InW2 (S.frame.ψ ⟨x, hx⟩ : P6) → x ∈ pCoreOf 2 H := fun x hx h =>
    A.U_le_Q (le_conjClosure _ _ (S.V2_le_V3 (S.mem_V2_of_psi hx h)))
  have hz₁Q : z₁ ∈ pCoreOf 2 H := hV2Q z₁ hz₁V (by rw [hψz₁]; exact hW1)
  have hz₂Q : z₂ ∈ pCoreOf 2 H := hV2Q z₂ hz₂V (by rw [hψz₂]; exact hW2)
  have hψinj : ∀ x y (hx : x ∈ V) (hy : y ∈ V),
      ((S.frame.ψ ⟨x, hx⟩ : ↥W4) : P6) = (S.frame.ψ ⟨y, hy⟩ : P6) → x = y :=
    fun x y hx hy h => congrArg Subtype.val (S.frame.ψ.injective (Subtype.ext h))
  have hpsiz : ((S.frame.ψ ⟨S.z, S.z_mem_V⟩ : ↥W4) : P6) = e0123 := by rw [S.psi_z]
  have hz₁z : z₁ ≠ S.z := fun h => hne1 (by
    rw [← hψz₁, ← hpsiz]
    exact congrArg (fun x : ↥V => ((S.frame.ψ x : ↥W4) : P6)) (Subtype.ext h))
  have hz₂z : z₂ ≠ S.z := fun h => hne2 (by
    rw [← hψz₂, ← hpsiz]
    exact congrArg (fun x : ↥V => ((S.frame.ψ x : ↥W4) : P6)) (Subtype.ext h))
  have hzzz : S.z * z₁ * z₂ = 1 := by
    have hm : S.z * z₁ * z₂ ∈ V := V.mul_mem (V.mul_mem S.z_mem_V hz₁V) hz₂V
    have h : ((S.frame.ψ ⟨S.z * z₁ * z₂, hm⟩ : ↥W4) : P6) = 1 := by
      have e : (⟨S.z * z₁ * z₂, hm⟩ : ↥V) = ⟨S.z, S.z_mem_V⟩ * ⟨z₁, hz₁V⟩ * ⟨z₂, hz₂V⟩ := rfl
      rw [e, map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, hpsiz, hψz₁, hψz₂]
      exact hprod
    have h1 : ((S.frame.ψ ⟨1, V.one_mem⟩ : ↥W4) : P6) = 1 := by
      rw [show (⟨1, V.one_mem⟩ : ↥V) = 1 from rfl, map_one]
      rfl
    exact hψinj _ 1 hm V.one_mem (by rw [h, h1])

  have hwz : w * S.z * w⁻¹ = z₂ := by
    rw [hz₂, hz₁, hwi]
    calc w * S.z * (w * w) = (w * w * w) * (w * S.z * (w * w)) := by rw [hw3, one_mul]
      _ = w * w * (w * w * S.z * w) * w := by group
  have hw2z : w * w * S.z * (w * w)⁻¹ = z₁ := by
    rw [hz₁, ← hwi]
    group

  have c01 := S.comm_conj_of_sq_z_F4 hNS h13315 h1356two hH hhat hn hna hlL hl hobl hctk hTL P
    hjZ hjV hj2 (y := w) hz₁Q (by rw [hwz]; exact hz₂Q) hz₁z
  have hw2z' : (w * w)⁻¹ * S.z * (w * w) = z₂ := by
    rw [hz₂, hz₁]
    group
  have c02 := S.comm_conj_of_sq_z_F4 hNS h13315 h1356two hH hhat hn hna hlL hl hobl hctk hTL P
    hjZ hjV hj2 (y := w * w) (by rw [hw2z']; exact hz₂Q) (by rw [hw2z]; exact hz₁Q)
    (by rw [hw2z']; exact hz₂z)
  set j₁ := w⁻¹ * j * w with hj₁
  set j₂ := (w * w)⁻¹ * j * (w * w) with hj₂
  have hj₂' : j₂ = w⁻¹ * j₁ * w := by rw [hj₂, hj₁]; group
  have c12 : j₁ * j₂ = j₂ * j₁ := by
    rw [hj₂']
    calc j₁ * (w⁻¹ * j₁ * w) = w⁻¹ * (j * j₁) * w := by rw [hj₁]; group
      _ = w⁻¹ * (j₁ * j) * w := by rw [c01]
      _ = w⁻¹ * j₁ * w * j₁ := by rw [hj₁]; group

  set a := j * j₁ * j₂ with ha
  have hj₁2 : j₁ * j₁ = z₁ := by rw [hj₁, hz₁, ← hj2]; group
  have hj₂2 : j₂ * j₂ = z₂ := by rw [hj₂', hz₂, ← hj₁2]; group
  have ha2 : a * a = 1 := by
    have h1 : Commute (j * j₁) j₂ := (Commute.mul_left c02 c12)
    have h2 : a * a = (j * j) * (j₁ * j₁) * (j₂ * j₂) := by
      rw [ha, ← pow_two, h1.mul_pow, (show Commute j j₁ from c01).mul_pow, pow_two, pow_two,
        pow_two]
    rw [h2, hj2, hj₁2, hj₂2, hzzz]

  have hsj : Perm.sign (S.frame.ρ ⟨j, hjN⟩) = -1 := by
    rcases Int.units_eq_one_or (Perm.sign (S.frame.ρ ⟨j, hjN⟩)) with h | h
    · exact absurd h (S.sign_ne_of_Z1_F4 hNS h13315 h1356two hH hhat hn hna hlL hl hobl hctk P
        hjZ hjV hjN)
    · exact h
  set jN : ↥(Subgroup.normalizer (V : Set G)) := ⟨j, hjN⟩ with hjN'
  set aN : ↥(Subgroup.normalizer (V : Set G)) :=
    jN * (wN⁻¹ * jN * wN) * ((wN * wN)⁻¹ * jN * (wN * wN)) with haN
  have haN' : (aN : G) = a := rfl
  have hsmul : ∀ x y : ↥(Subgroup.normalizer (V : Set G)),
      Perm.sign (S.frame.ρ (x * y)) = Perm.sign (S.frame.ρ x) * Perm.sign (S.frame.ρ y) :=
    fun x y => by rw [map_mul, Perm.sign_mul]
  have hsconj : ∀ x y : ↥(Subgroup.normalizer (V : Set G)),
      Perm.sign (S.frame.ρ (y⁻¹ * x * y)) = Perm.sign (S.frame.ρ x) := by
    intro x y
    rw [hsmul, hsmul, map_inv, Perm.sign_inv]
    rcases Int.units_eq_one_or (Perm.sign (S.frame.ρ y)) with h | h <;>
      rcases Int.units_eq_one_or (Perm.sign (S.frame.ρ x)) with h' | h' <;> rw [h, h'] <;> decide
  have hsa : Perm.sign (S.frame.ρ aN) ≠ 1 := by
    rw [haN, hsmul, hsmul, hsconj, hsconj, hsj]
    decide
  have haV : a ∉ V := by
    intro h
    apply hsa
    have hC : (aN : G) ∈ Subgroup.centralizer (V : Set G) := by
      rw [haN']
      exact S.V_le_centralizer_V h
    have : S.frame.ρ aN = 1 := (S.rho_eq_one_iff aN).2 hC
    rw [this, map_one]
  have ha1 : a ≠ 1 := fun h => haV (h ▸ V.one_mem)

  have cj1 : Commute j j₁ := c01
  have cj2 : Commute j j₂ := c02
  have c12' : Commute j₁ j₂ := c12
  have hj3 : w⁻¹ * j₂ * w = j := by
    rw [hj₂', hj₁]
    calc w⁻¹ * (w⁻¹ * (w⁻¹ * j * w) * w) * w = (w * w * w)⁻¹ * j * (w * w * w) := by group
      _ = j := by rw [hw3]; group
  have hwa : w * a = a * w := by
    have h : w⁻¹ * a * w = a := by
      calc w⁻¹ * a * w = (w⁻¹ * j * w) * (w⁻¹ * j₁ * w) * (w⁻¹ * j₂ * w) := by rw [ha]; group
        _ = j₁ * j₂ * j := by rw [← hj₁, ← hj₂', hj3]
        _ = j * (j₁ * j₂) := ((cj1.mul_right cj2).eq).symm
        _ = a := (mul_assoc j j₁ j₂).symm
    calc w * a = w * (w⁻¹ * a * w) := by rw [h]
      _ = a * w := by group
  have hja : j * a = a * j := by
    have hc : Commute j (j * (j₁ * j₂)) := (Commute.refl j).mul_right (cj1.mul_right cj2)
    rw [ha, mul_assoc]
    exact hc.eq

  have hww : (w * w)⁻¹ = w := by rw [← hwi, inv_inv]
  have hwj : w * j * w⁻¹ = j₂ := by
    rw [hj₂, hww, ← hwi]
  set d := j * w * j⁻¹ * w⁻¹ with hd
  have hd' : d = j * j₂⁻¹ := by
    rw [hd, ← hwj]
    group
  have hz₂2 : z₂ * z₂ = 1 := by rw [← pow_two]; exact S.elemAbelian_V.2 _ hz₂V
  have hz₂i : z₂⁻¹ = z₂ := inv_eq_of_mul_eq_one_right hz₂2
  have hdd : d * d = S.z * z₂ := by
    have cj2' : Commute j j₂⁻¹ := cj2.inv_right
    rw [hd', ← pow_two, cj2'.mul_pow, pow_two, pow_two, hj2, ← mul_inv_rev, hj₂2, hz₂i]
  have hddV : d * d ∈ V := by rw [hdd]; exact V.mul_mem S.z_mem_V hz₂V
  have hdd1 : d * d ≠ 1 := by
    rw [hdd]
    intro h
    apply hz₂z
    have : z₂ = S.z⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this, inv_eq_of_mul_eq_one_right hzz]
  have hdd4 : d * d * (d * d) = 1 := by
    rw [← pow_two]
    exact S.elemAbelian_V.2 _ hddV
  refine ⟨a, ha2, ha1, fun r hr => ?_⟩

  have hzr : S.z = r⁻¹ * a * r := by rw [← hr]; group
  have hcomm_z : ∀ x : G, x * a = a * x → r⁻¹ * x * r ∈ H := by
    intro x hx
    rw [hHz, Subgroup.mem_centralizer_singleton_iff, hzr]
    calc r⁻¹ * x * r * (r⁻¹ * a * r) = r⁻¹ * (x * a) * r := by group
      _ = r⁻¹ * (a * x) * r := by rw [hx]
      _ = r⁻¹ * a * r * (r⁻¹ * x * r) := by group
  have hx1 : j * w * j⁻¹ * a = a * (j * w * j⁻¹) := by
    have h1 : Commute j a := hja
    have h2 : Commute w a := hwa
    exact ((h1.mul_left h2).mul_left h1.inv_left).eq
  have hx2 : w⁻¹ * a = a * w⁻¹ := (show Commute w a from hwa).inv_left.eq
  have hs₁ := hcomm_z _ hx1
  have hs₂ := hcomm_z _ hx2
  have hcube : ∀ (x : G) (hx : x ∈ H), x * x * x = 1 → P.Φ ⟨x, hx⟩ ∈ P3 := by
    intro x hx h
    refine ⟨P.Φ_mem _, ?_⟩
    rw [← map_pow]
    have : (⟨x, hx⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by
      rw [SubmonoidClass.coe_pow, pow_three, ← mul_assoc]
      exact h)
    rw [this, map_one]
  have hP1 := hcube _ hs₁ (by
    calc r⁻¹ * (j * w * j⁻¹) * r * (r⁻¹ * (j * w * j⁻¹) * r) * (r⁻¹ * (j * w * j⁻¹) * r) =
        r⁻¹ * j * (w * w * w) * j⁻¹ * r := by group
      _ = 1 := by rw [hw3]; group)
  have hP2 := hcube _ hs₂ (by
    calc r⁻¹ * w⁻¹ * r * (r⁻¹ * w⁻¹ * r) * (r⁻¹ * w⁻¹ * r) = r⁻¹ * (w * w * w)⁻¹ * r := by
          group
      _ = 1 := by rw [hw3]; group)
  have hP12 : P.Φ (⟨_, hs₁⟩ * ⟨_, hs₂⟩) ∈ P3 := by
    rw [map_mul]
    exact P3.mul_mem hP1 hP2
  have he : ((⟨_, hs₁⟩ * ⟨_, hs₂⟩ : ↥H) : G) = r⁻¹ * d * r := by
    show r⁻¹ * (j * w * j⁻¹) * r * (r⁻¹ * w⁻¹ * r) = r⁻¹ * d * r
    rw [hd]
    group
  have hΦ1 : P.Φ (⟨_, hs₁⟩ * ⟨_, hs₂⟩) = 1 := by
    have h3 := hP12.2
    have h4 : P.Φ (⟨_, hs₁⟩ * ⟨_, hs₂⟩) ^ 4 = 1 := by
      rw [← map_pow]
      have : (⟨_, hs₁⟩ * ⟨_, hs₂⟩ : ↥H) ^ 4 = 1 := by
        apply Subtype.ext
        rw [SubmonoidClass.coe_pow, he]
        calc (r⁻¹ * d * r) ^ 4 = r⁻¹ * (d * d * (d * d)) * r := by
              simp only [pow_succ, pow_zero, one_mul]
              group
          _ = 1 := by rw [hdd4]; group
      rw [this, map_one]
    rw [pow_succ, h3, one_mul] at h4
    exact h4
  have hQmem := (P.Φ_eq_one_iff _).1 hΦ1
  rw [he] at hQmem
  have hsq := P.sq_mem_V1 hQ hQmem
  have e2 : r⁻¹ * d * r * (r⁻¹ * d * r) = r⁻¹ * (d * d) * r := by group
  rw [e2] at hsq
  rcases S.mem_V1_iff.1 hsq with h | h
  · apply hdd1
    calc d * d = r * (r⁻¹ * (d * d) * r) * r⁻¹ := by group
      _ = 1 := by rw [h]; group
  · apply haV
    have : d * d = a := by
      calc d * d = r * (r⁻¹ * (d * d) * r) * r⁻¹ := by group
        _ = a := by rw [h, hr]
    rw [← this]
    exact hddV

end Data

section Final

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hhat : ¬ IsHatA6 L)
  (hn : H ≤ Subgroup.normalizer (S.L1 : Set G)) (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H))
  (hobl : Obl13_5_14Six_F4) (hctk : Input13515CTK_F4)
include hNS h13315 h1356two hH hhat hn hna hobl hctk

theorem T_le_L_F4 : T ≤ L := by
  by_contra hTL
  obtain ⟨l, hlL, hl⟩ := S.exists_lK
  obtain ⟨P⟩ := S.nonempty_pf15_six_F4 hNS h13315 h1356two hH hn hna hhat hlL hl hobl
  have hQ := S.card_Q_six_F4 hNS h13315 h1356two hH hhat hn hna hlL hl hobl hctk hTL
  obtain ⟨j, hjZ, hjV⟩ : ∃ j ∈ P.Z1, j ∉ fsuV1 T V := by
    by_contra h
    push Not at h
    have := Subgroup.card_le_of_le (show P.Z1 ≤ fsuV1 T V from h)
    rw [P.card_Z1 hQ, S.card_V1] at this
    omega
  have hj2 := P.sq_mem_V1 hQ hjZ.1
  have hj1 : j ≠ 1 := fun h => hjV (h ▸ (fsuV1 T V).one_mem)
  rcases S.mem_V1_iff.1 hj2 with h | h
  · exact S.false_of_not_conj_F4 hNS h13315 h1356two hH hhat hn hna hlL hl hobl hctk hTL h hj1
      (S.not_conj_of_Z1_F4 hNS h13315 h1356two hH hhat hn hna hlL hl hobl hctk hTL P hjZ hjV)
  · obtain ⟨a, ha2, ha1, haz⟩ := S.exists_inv_not_conj_of_sq_z_F4 hNS h13315 h1356two hH hhat hn
      hna hlL hl hobl hctk hTL P hjZ hjV h
    exact S.false_of_not_conj_F4 hNS h13315 h1356two hH hhat hn hna hlL hl hobl hctk hTL ha2 ha1 haz

theorem psu43_F4 (hU43 : StmtU43Type) : LieModel G .PSU 4 3 1 :=
  S.psu43_of_le_F4 hNS h13315 h1356two hH hhat hn hna hU43 hobl hctk
    (S.T_le_L_F4 hNS h13315 h1356two hH hhat hn hna hobl hctk)

end Final

end Setting4

end A6

end CFSG.Quasithin.H13
