module

public import CFSG.Quasithin.H13.A6S1515
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5SitBridge6
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1514
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1514Obl
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1515Inputs

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

section Data

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hn : H ≤ Subgroup.normalizer (S.L1 : Set G))
  (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H)) (hhat : ¬ IsHatA6 L)
  {l : ↥(Subgroup.normalizer (V : Set G))} (hlL : (l : G) ∈ L) (hl : S.frame.ρ l = lK)
include hNS h13315 h1356two hH hn hna hhat hlL hl

omit h13315 h1356two in

theorem obl_data_F4 (hobl : Obl13_5_14Six_F4) :
    oTwoRes (pCoreOf 2 (L ⊔ T) ⊔ S.KH H l) = S.KH H l ∧ IsShort2 (S.KH H l) ∧
      IsAltType (S.KH H l) 5 ∧ pCoreOf 2 (S.KH H l) = V ∧
      conjClosure S.V3 H = pCoreOf 2 S.L1 ∧ IsQ8Sq ↥(conjClosure S.V3 H) :=
  hobl G T L V S H l hNS hH hn hna hhat l.2 hlL (S.not_mem_L1T hl)
    (Or.inl (by rw [Subtype.coe_eta, hl]; exact lK_facts.2.1))

omit hhat hlL hl in

theorem UH_le_L1_six_F4 : conjClosure S.V3 H ≤ S.L1 :=
  (S.toA5Sit_F4 hNS h13315 h1356two hH hna).UH_le_L1 hn

theorem nonempty_pf15_six_F4 (hobl : Obl13_5_14Six_F4) :
    Nonempty (A5SitPf15 (S.toA5Sit_F4 hNS h13315 h1356two hH hna)
      (S.toA5SitY_F4 hNS h13315 h1356two hH hna hhat)) := by
  obtain ⟨-, -, -, -, hU, hUQ8⟩ := S.obl_data_F4 hNS hH hn hna hhat hlL hl hobl
  exact (S.toA5Sit_F4 hNS h13315 h1356two hH hna).nonempty_pf15 VolI.stmtF956i _ hn hU hUQ8

omit hhat hl in

theorem KH_le_L_F4 : S.KH H l ≤ L := by
  have hUL : conjClosure S.V3 H ≤ L :=
    (S.UH_le_L1_six_F4 hNS h13315 h1356two hH hn hna).trans (S.L1_le.trans inf_le_left)
  refine sup_le hUL ?_
  rintro _ ⟨u, hu, rfl⟩
  have huL := hUL hu
  show (MulAut.conj (l : G)⁻¹) u ∈ L
  rw [MulAut.conj_apply, inv_inv]
  exact L.mul_mem (L.mul_mem (L.inv_mem hlL) huL) hlL

omit hhat hlL in

theorem KH_le_stab4V_F4 : S.KH H l ≤ S.stab4V := by
  obtain ⟨hK4, -⟩ := S.lemma13_5_14_two_F4 hNS h1356two h13315 hH
    (S.UH_le_L1_six_F4 hNS h13315 h1356two hH hn hna) hna
  refine sup_le (fun u hu => S.mem_stab4V.2 ⟨_, (K4L_stab _ (hK4 u hu)).1⟩) ?_
  rintro _ ⟨u, hu, rfl⟩
  have hu' := hK4 u hu
  have huN : u ∈ Subgroup.normalizer (V : Set G) :=
    S.frame.L_le (S.L1_le.trans inf_le_left (S.UH_le_L1_six_F4 hNS h13315 h1356two hH hn hna hu))
  have hmem : (l : G)⁻¹ * u * l ∈ Subgroup.normalizer (V : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ l.2) huN) l.2
  show (MulAut.conj (l : G)⁻¹) u ∈ S.stab4V
  rw [MulAut.conj_apply, inv_inv]
  refine S.mem_stab4V.2 ⟨hmem, ?_⟩
  have e : (⟨(l : G)⁻¹ * u * l, hmem⟩ : ↥(Subgroup.normalizer (V : Set G))) =
      l⁻¹ * ⟨u, huN⟩ * l := rfl
  rw [e, map_mul, map_mul, map_inv, hl]
  exact (K4L_stab _ hu').2

theorem isSylowTwoOf_T_inf_K_F4
    : IsSylowTwoOf (T ⊓ S.KH H l) (S.KH H l) := by
  have hUL1 := S.UH_le_L1_six_F4 hNS h13315 h1356two hH hn hna
  obtain ⟨-, hsurj⟩ := S.lemma13_5_14_two_F4 hNS h1356two h13315 hH hUL1 hna
  have hUT : conjClosure S.V3 H ≤ T := S.UH_le_T_F4 hNS h1356two h13315 hH
  have hUK : conjClosure S.V3 H ≤ S.KH H l := le_sup_left
  have hKL := S.KH_le_L_F4 hNS h13315 h1356two hH hn hna hlL
  rw [A4.isSylowTwoOf_iff_maximal]
  refine ⟨inf_le_right, S.h13.sylow.1.to_le inf_le_left, fun R hRK hR hTR => ?_⟩
  intro r hr
  have hrK := hRK hr
  obtain ⟨hrN, hr4, hrs⟩ := S.mem_stab4V.1 (S.KH_le_stab4V_F4 hNS h13315 h1356two hH hn hna hl hrK)

  have hpow : ∀ x ∈ R, ∀ hx : x ∈ Subgroup.normalizer (V : Set G),
      S.frame.ρ ⟨x, hx⟩ ^ 4 = 1 := by
    intro x hxR hx
    obtain ⟨k, hk⟩ := hR ⟨x, hxR⟩
    refine pow_four_of_pow_two_pow (k := k) ?_
    rw [← map_pow]
    have : (⟨x, hx⟩ : ↥(Subgroup.normalizer (V : Set G))) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [this, map_one]
  have hρr : S.frame.ρ ⟨r, hrN⟩ ∈ K4L := by
    refine k4MaxAt_all _ hr4 hrs (hpow r hr hrN) fun k hk => ?_
    obtain ⟨u, hu, hρu⟩ := hsurj k hk
    have huN : u ∈ Subgroup.normalizer (V : Set G) :=
      S.frame.L_le (S.L1_le.trans inf_le_left (hUL1 hu))
    have huR : u ∈ R := hTR ⟨hUT hu, hUK hu⟩
    have := hpow (r * u) (R.mul_mem hr huR) (Subgroup.mul_mem _ hrN huN)
    have e : (⟨r * u, Subgroup.mul_mem _ hrN huN⟩ : ↥(Subgroup.normalizer (V : Set G))) =
        ⟨r, hrN⟩ * ⟨u, huN⟩ := rfl
    rwa [e, map_mul, hρu] at this

  obtain ⟨u, hu, hρu⟩ := hsurj _ hρr
  have huN : u ∈ Subgroup.normalizer (V : Set G) :=
    S.frame.L_le (S.L1_le.trans inf_le_left (hUL1 hu))
  have hc : S.frame.ρ (⟨u, huN⟩⁻¹ * ⟨r, hrN⟩) = 1 := by
    rw [map_mul, map_inv, hρu, inv_mul_cancel]
  have hcC := (S.rho_eq_one_iff _).1 hc
  have hcL : u⁻¹ * r ∈ L := L.mul_mem (L.inv_mem (hKL (hUK hu))) (hKL hrK)
  have hcT : u⁻¹ * r ∈ T :=
    S.pCoreOf_L_le_T (S.inf_centralizer_le_pCoreOf hhat ⟨hcL, hcC⟩)
  have hrT : r ∈ T := by
    have := T.mul_mem (hUT hu) hcT
    simpa using this
  exact ⟨hrT, hrK⟩

theorem pCoreOf_LT_six_F4
    (hobl : Obl13_5_14Six_F4) (hctk : Input13515CTK_F4) :
    pCoreOf 2 (L ⊔ T) = V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hKeq, hshort, halt, hO2K, -, -⟩ :=
    S.obl_data_F4 hNS hH hn hna hhat hlL hl hobl
  have hKL := S.KH_le_L_F4 hNS h13315 h1356two hH hn hna hlL
  set K := S.KH H l with hKdef
  set Q := pCoreOf 2 (L ⊔ T) with hQ
  set Tm := T ⊓ Subgroup.normalizer (K : Set G) with hTm
  have hTm2 : IsPGroup 2 Tm := S.h13.sylow.1.to_le inf_le_left
  have hTmN : Tm ≤ Subgroup.normalizer (K : Set G) := inf_le_right
  have hsyl : IsSylowTwoOf Tm (K ⊔ Tm) := by
    refine isSylowTwoOf_sup_of_inf hTm2 hTmN ?_
    have e : Tm ⊓ K = T ⊓ K := by
      rw [hTm, inf_assoc, inf_eq_right.2 (Subgroup.le_normalizer (H := K))]
    rw [e]
    exact S.isSylowTwoOf_T_inf_K_F4 hNS h13315 h1356two hH hn hna hhat hlL hl
  obtain ⟨hC, -⟩ := VolI.stmtC113c G K Tm hsyl hTmN hshort halt

  have hQT : Q ≤ T := (S.cT ▸ inf_le_left : pCoreOf 2 (L ⊔ T) ≤ T)
  have hQN := S.pCoreOf_LT_le_normalizer_KH hKeq hKL
  have hQTm : Q ≤ Tm := le_inf hQT hQN
  have hQO : Q ≤ pCoreOf 2 (K ⊔ Tm) := le_pCoreOf_of_le_normalizer 2 (hQTm.trans le_sup_right)
    (sup_le (hKL.trans (le_sup_left.trans (le_normalizer_pCoreOf 2 _)))
      ((inf_le_left.trans le_sup_right).trans (le_normalizer_pCoreOf 2 _)))
    (pCoreOf_isPGroup 2 _)

  have hCTK : T ⊓ Subgroup.centralizer (K : Set G) = ⊥ :=
    hctk G T L V S H l hNS hH hn hna hhat l.2 hlL (S.not_mem_L1T hl)
      (Or.inl (by rw [Subtype.coe_eta, hl]; exact lK_facts.2.1))
  have hCTm : Tm ⊓ Subgroup.centralizer (K : Set G) = ⊥ :=
    le_bot_iff.1 (hCTK ▸ inf_le_inf_right _ inf_le_left)
  rw [hCTm, sup_bot_eq] at hC
  have hUQ : blockU K ≤ V := hshort.2.2.1.1.trans (inf_le_left.trans hO2K.le)
  refine le_antisymm ((hQO.trans hC.le).trans hUQ) ?_
  rw [hQ, ← S.cT]
  refine le_inf S.V_le_T fun v hv => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact congrArg Subtype.val (S.elemAbelian_V.1.is_comm.comm ⟨w, hw⟩ ⟨v, hv⟩)

theorem normalizer_L_six_F4
    (hobl : Obl13_5_14Six_F4) (hctk : Input13515CTK_F4) :
    Subgroup.normalizer (L : Set G) = L ⊔ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, hO2K, -, -⟩ := S.obl_data_F4 hNS hH hn hna hhat hlL hl hobl
  have hKL := S.KH_le_L_F4 hNS h13315 h1356two hH hn hna hlL
  have hLT := S.pCoreOf_LT_six_F4 hNS h13315 h1356two hH hn hna hhat hlL hl hobl hctk
  set M := Subgroup.normalizer (L : Set G) with hM
  have hVL : V ≤ L := hO2K ▸ (pCoreOf_le 2 _).trans hKL

  have hOM : pCoreOf 2 M = V := by
    refine le_antisymm ?_ S.V_le_pCoreOf_M
    rw [← hLT]
    exact le_pCoreOf_of_le_normalizer 2 (S.pCoreOf_M_le_T.trans le_sup_right)
      ((sup_le Subgroup.le_normalizer S.T_le_NL).trans (le_normalizer_pCoreOf 2 M))
      (pCoreOf_isPGroup 2 M)
  have hMV : M ≤ Subgroup.normalizer (V : Set G) := hOM ▸ le_normalizer_pCoreOf 2 M
  have hLTM : L ⊔ T ≤ M := sup_le Subgroup.le_normalizer S.T_le_NL
  refine le_antisymm ?_ hLTM

  set f : ↥M →* ℤˣ := Perm.sign.comp (S.frame.ρ.comp (Subgroup.inclusion hMV))
  have hker : f.ker ≤ (L ⊔ T).subgroupOf M := by
    intro m hm
    have hm' : Perm.sign (S.frame.ρ (Subgroup.inclusion hMV m)) = 1 := hm
    obtain ⟨l', hlL', hl'⟩ := (S.frame.image_L _).2 (Perm.mem_alternatingGroup.2 hm')
    rw [Subgroup.mem_subgroupOf]
    have hk : S.frame.ρ (l'⁻¹ * Subgroup.inclusion hMV m) = 1 := by
      rw [map_mul, map_inv, hl', inv_mul_cancel]
    have hkC := (S.rho_eq_one_iff _).1 hk
    have hkM : ((l'⁻¹ * Subgroup.inclusion hMV m : ↥(Subgroup.normalizer (V : Set G))) : G) ∈ M :=
      M.mul_mem (M.inv_mem (Subgroup.le_normalizer hlL')) m.2
    have hkC' : ((l'⁻¹ * Subgroup.inclusion hMV m : ↥(Subgroup.normalizer (V : Set G))) : G) ∈
        Subgroup.centralizer (pCoreOf 2 M : Set G) := by
      rw [hOM]
      exact hkC
    have hkV :
        ((l'⁻¹ * Subgroup.inclusion hMV m : ↥(Subgroup.normalizer (V : Set G))) : G) ∈ V := by
      have h := S.charTwo_M ⟨hkM, hkC'⟩
      rwa [hOM] at h
    have : (m : G) = l' * ((l'⁻¹ * Subgroup.inclusion hMV m :
        ↥(Subgroup.normalizer (V : Set G))) : G) := by
      simp [Subgroup.coe_inclusion]
    rw [this]
    exact le_sup_left (a := L) (L.mul_mem hlL' (hVL hkV))
  have h2 : ((L ⊔ T).subgroupOf M).index ∣ 2 := by
    have h1 := Subgroup.index_dvd_of_le hker
    rw [Subgroup.index_ker] at h1
    have h3 : Nat.card f.range ∣ 2 := by
      have := Subgroup.card_subgroup_dvd_card f.range
      rw [Nat.card_eq_fintype_card (α := ℤˣ), Fintype.card_units_int] at this
      exact this
    exact h1.trans h3
  have hodd : ¬ 2 ∣ ((L ⊔ T).subgroupOf M).index := by
    have hT := A5.isSylowTwoOf_of_le S.h13.sylow S.T_le_NL
    intro h
    apply hT.2.2
    exact h.trans (Subgroup.index_dvd_of_le fun x hx => (le_sup_right : T ≤ L ⊔ T) hx)
  have h1 : ((L ⊔ T).subgroupOf M).index = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
    · exact h
    · exact absurd (h ▸ dvd_rfl) hodd
  intro m hm
  have := Subgroup.index_eq_one.1 h1
  have hm' : (⟨m, hm⟩ : ↥M) ∈ (L ⊔ T).subgroupOf M := this ▸ Subgroup.mem_top _
  exact hm'

end Data

end Setting4

end CFSG.Quasithin.H13.A6
