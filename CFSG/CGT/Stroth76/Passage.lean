module

public import CFSG.CGT.Stroth76.PassageGroup
public import CFSG.CGT.Stroth76.NoInvFrame
public import CFSG.CGT.Stroth76.Lemma1

public section

namespace CFSG.CGT.Stroth76

open CFSG.CGT.Stroth77 CFSG.CGT.Stroth77.Arch76
open scoped commutatorElement

theorem fuv_fρ_fixed_eq_zero : ∀ v : Co, fuv v = v → fρ v = v → v = 0 := by
  decide +kernel

variable {G : Type} [Group G] [Finite G] (F : StrothFrame G)

theorem frame_card_S_dvd (h11 : ¬ 2 ^ 11 ∣ Nat.card G) :
    Nat.card (F.S : Subgroup G) ∣ 2 ^ 10 := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp F.S.isPGroup'
  have hdvd : Nat.card (F.S : Subgroup G) ∣ Nat.card G := Subgroup.card_subgroup_dvd_card _
  rw [hn] at hdvd ⊢
  refine pow_dvd_pow 2 ?_
  by_contra h
  exact h11 ((pow_dvd_pow 2 (by omega)).trans hdvd)

theorem frame_A_le_centralizer_inf :
    F.A ≤ Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) :=
  le_inf F.dA.toConfig.A_le_centralizer F.A_le_S

theorem frame_centralizer_inf_inf_T :
    (Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G)) ⊓
      (F.A ⊔ Subgroup.closure {F.dA.uv, F.dA.t, F.dA.u}) = F.A := by
  apply le_antisymm
  · rintro g ⟨⟨hgC, -⟩, hgT⟩
    exact mem_A_of_mem_Tsub_of_mem_centralizer F.dA.toConfig hgT hgC
  · exact le_inf (frame_A_le_centralizer_inf F) le_sup_left

theorem frame_card_centralizer_inf_sup_T :
    8 * Nat.card (Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) : Subgroup G) ≤
      Nat.card ((Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G)) ⊔
        (F.A ⊔ Subgroup.closure {F.dA.uv, F.dA.t, F.dA.u}) : Subgroup G) := by
  set Q := Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) with hQ
  set T := F.A ⊔ Subgroup.closure {F.dA.uv, F.dA.t, F.dA.u} with hT
  have hTc : Nat.card T = 2 ^ 8 := card_Tsub F.dA.toConfig
  have hAc : Nat.card F.A = 32 := F.dA.card_eq_32
  have h1 : Q.relIndex T * Nat.card (Q ⊓ T : Subgroup G) = Nat.card T :=
    Subgroup.relIndex_mul_card Q T
  rw [frame_centralizer_inf_inf_T F, hAc, hTc] at h1
  have h8 : Q.relIndex T = 8 := by omega
  have h2 : Q.relIndex (Q ⊔ T) * Nat.card (Q ⊓ (Q ⊔ T) : Subgroup G) =
      Nat.card (Q ⊔ T : Subgroup G) := Subgroup.relIndex_mul_card Q (Q ⊔ T)
  rw [inf_eq_left.mpr le_sup_left] at h2
  have hpos : 0 < Nat.card (Q ⊔ T : Subgroup G) := Nat.card_pos
  have hne : Q.relIndex (Q ⊔ T) ≠ 0 := by
    intro h
    rw [h, zero_mul] at h2
    omega
  have h3 : Q.relIndex T ≤ Q.relIndex (Q ⊔ T) := Subgroup.relIndex_le_of_le_right le_sup_right hne
  rw [← h2]
  rw [h8] at h3
  exact Nat.mul_le_mul_right _ h3

theorem frame_card_centralizer_inf_dvd (h11 : ¬ 2 ^ 11 ∣ Nat.card G) :
    Nat.card (Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) : Subgroup G) ∣ 2 ^ 7 := by
  have h8 := frame_card_centralizer_inf_sup_T F
  set Q := Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) with hQ
  set T := F.A ⊔ Subgroup.closure {F.dA.uv, F.dA.t, F.dA.u} with hT
  have hQT : Q ⊔ T ≤ (F.S : Subgroup G) := sup_le inf_le_right F.T_le_S
  have h4 : Nat.card (Q ⊔ T : Subgroup G) ≤ 2 ^ 10 :=
    (Subgroup.card_le_of_le hQT).trans (Nat.le_of_dvd (by norm_num) (frame_card_S_dvd F h11))
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp
    ((F.S.isPGroup').to_le (inf_le_right : Q ≤ (F.S : Subgroup G)))
  rw [hk] at h8 ⊢
  refine pow_dvd_pow 2 ?_
  by_contra h
  have h5 : 2 ^ 8 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem frame_card_centralizer_inf_le (h11 : ¬ 2 ^ 11 ∣ Nat.card G) :
    Nat.card (Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) : Subgroup G) ≤
      4 * Nat.card F.A := by
  have := Nat.le_of_dvd (by norm_num) (frame_card_centralizer_inf_dvd F h11)
  rw [F.dA.card_eq_32]
  omega

theorem frame_mem_normalizer_centralizer_inf {g : G}
    (hgA : g ∈ Subgroup.normalizer (F.A : Set G)) (hgS : g ∈ (F.S : Subgroup G)) :
    g ∈ Subgroup.normalizer
      ((Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) : Subgroup G) : Set G) :=
  Subgroup.inf_normalizer_le_normalizer_inf
    ⟨mem_normalizer_centralizer_of_mem hgA, Subgroup.le_normalizer hgS⟩

@[expose] def frameSylowN : Sylow 2 (Subgroup.normalizer (F.A : Set G)) :=
  ((F.nsylowA.2.1.comap_of_injective (Subgroup.normalizer (F.A : Set G)).subtype
    Subtype.val_injective : IsPGroup 2 (((F.S : Subgroup G) ⊓
      Subgroup.normalizer (F.A : Set G)).subgroupOf (Subgroup.normalizer (F.A : Set G))))).toSylow
    F.nsylowA.2.2

theorem coe_frameSylowN : (frameSylowN F : Subgroup (Subgroup.normalizer (F.A : Set G))) =
    ((F.S : Subgroup G) ⊓ Subgroup.normalizer (F.A : Set G)).subgroupOf
      (Subgroup.normalizer (F.A : Set G)) :=
  IsPGroup.toSylow_coe _ _

theorem frame_map_sylowN : (frameSylowN F : Subgroup (Subgroup.normalizer (F.A : Set G))).map
    (Subgroup.normalizer (F.A : Set G)).subtype =
      (F.S : Subgroup G) ⊓ Subgroup.normalizer (F.A : Set G) := by
  rw [coe_frameSylowN, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_right]

theorem frame_mem_centralizer_configN_iff (y : Subgroup.normalizer (F.A : Set G)) :
    y ∈ Subgroup.centralizer (F.configN.A : Set (Subgroup.normalizer (F.A : Set G))) ↔
      (y : G) ∈ Subgroup.centralizer (F.A : Set G) := by
  simp only [Subgroup.mem_centralizer_iff]
  constructor
  · intro h a ha
    have := congrArg Subtype.val (h ⟨a, Subgroup.le_normalizer ha⟩
      (Subgroup.mem_subgroupOf.mpr ha))
    simpa using this
  · intro h a ha
    exact Subtype.ext (by simpa using h a (Subgroup.mem_subgroupOf.mp ha))

theorem frame_centralizer_inf_sylowN_eq :
    Subgroup.centralizer (F.configN.A : Set (Subgroup.normalizer (F.A : Set G))) ⊓
        (frameSylowN F : Subgroup (Subgroup.normalizer (F.A : Set G))) =
      (Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G)).subgroupOf
        (Subgroup.normalizer (F.A : Set G)) := by
  ext y
  rw [Subgroup.mem_inf, frame_mem_centralizer_configN_iff, coe_frameSylowN,
    Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_inf]
  exact ⟨fun ⟨h1, h2, _⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, h2, y.2⟩⟩

theorem frame_map_centralizer_inf_sylowN :
    (Subgroup.centralizer (F.configN.A : Set (Subgroup.normalizer (F.A : Set G))) ⊓
        (frameSylowN F : Subgroup (Subgroup.normalizer (F.A : Set G)))).map
      (Subgroup.normalizer (F.A : Set G)).subtype =
      Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) := by
  rw [frame_centralizer_inf_sylowN_eq, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr (inf_le_left.trans (Subgroup.centralizer_le_normalizer _))]

theorem frame_not_dvd_relIndex_centralizerN :
    ¬ 2 ∣ (Subgroup.centralizer (F.configN.A : Set (Subgroup.normalizer (F.A : Set G))) ⊓
        (frameSylowN F : Subgroup (Subgroup.normalizer (F.A : Set G)))).relIndex
      (Subgroup.centralizer (F.configN.A : Set (Subgroup.normalizer (F.A : Set G)))) := by
  set N := Subgroup.normalizer (F.A : Set G)
  set Z := Subgroup.centralizer (F.configN.A : Set N)
  set P := (frameSylowN F : Subgroup N)
  haveI : Z.Normal := Subgroup.normal_centralizer
  have h1 := Subgroup.relIndex_mul_relIndex (P ⊓ Z) P (P ⊔ Z) inf_le_left le_sup_left
  have h2 := Subgroup.relIndex_mul_relIndex (P ⊓ Z) Z (P ⊔ Z) inf_le_right le_sup_right
  rw [Subgroup.inf_relIndex_left] at h1
  rw [Subgroup.relIndex_sup_right] at h2
  have hne : Z.relIndex P ≠ 0 :=
    (Subgroup.isFiniteRelIndex_iff_finiteIndex.mpr inferInstance).relIndex_ne_zero
  have key : (P ⊓ Z).relIndex Z = P.relIndex (P ⊔ Z) :=
    (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) (by rw [h1, ← h2, mul_comm])).symm
  rw [inf_comm, key]
  exact fun h => (frameSylowN F).not_dvd_index
    (h.trans (Subgroup.relIndex_dvd_index_of_le le_sup_left))

theorem frame_exists_frattini_ρ :
    ∃ r ∈ Subgroup.normalizer
        ((Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) : Subgroup G) : Set G),
      ∀ a ∈ F.A, r⁻¹ * a * r = F.dA.ρ⁻¹ * a * F.dA.ρ := by
  set N := Subgroup.normalizer (F.A : Set G)
  set Z := Subgroup.centralizer (F.configN.A : Set N)
  haveI : Z.Normal := Subgroup.normal_centralizer
  set QN := Z ⊓ (frameSylowN F : Subgroup N) with hQN
  have hQ2 : IsPGroup 2 QN := (frameSylowN F).isPGroup'.to_le inf_le_right
  have hP2 : IsPGroup 2 (QN.subgroupOf Z) :=
    hQ2.comap_of_injective Z.subtype Subtype.val_injective
  let Psyl : Sylow 2 Z := hP2.toSylow (frame_not_dvd_relIndex_centralizerN F)
  have hPmap : (Psyl : Subgroup Z).map Z.subtype = QN := by
    rw [show (Psyl : Subgroup Z) = QN.subgroupOf Z from IsPGroup.toSylow_coe _ _,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_left]
  have htop := Sylow.normalizer_sup_eq_top Psyl
  rw [hPmap] at htop
  have hρ : (⟨F.dA.ρ, F.dA.ρ_mem⟩ : N) ∈ ((Subgroup.normalizer (QN : Set N) ⊔ Z : Subgroup N) :
      Set N) := by rw [htop]; trivial
  rw [Subgroup.mul_normal, Set.mem_mul] at hρ
  obtain ⟨n, hn, c, hc, hnc⟩ := hρ
  refine ⟨(n : G), ?_, fun a ha => ?_⟩
  · have := coe_mem_normalizer_map hn
    rwa [hQN, frame_map_centralizer_inf_sylowN] at this
  · have hnc' : (n : G) = F.dA.ρ * (c : G)⁻¹ := by
      have h : (n : G) * (c : G) = F.dA.ρ := congrArg Subtype.val hnc
      rw [← h, mul_inv_cancel_right]
    have hρa : F.dA.ρ⁻¹ * a * F.dA.ρ ∈ F.A := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem F.dA.ρ_mem) a).mp ha
      rwa [inv_inv] at this
    have hca : F.dA.ρ⁻¹ * a * F.dA.ρ * (c : G) = (c : G) * (F.dA.ρ⁻¹ * a * F.dA.ρ) :=
      Subgroup.mem_centralizer_iff.mp ((frame_mem_centralizer_configN_iff F c).mp hc) _ hρa
    rw [hnc']
    calc (F.dA.ρ * (c : G)⁻¹)⁻¹ * a * (F.dA.ρ * (c : G)⁻¹) =
        (c : G) * (F.dA.ρ⁻¹ * a * F.dA.ρ) * (c : G)⁻¹ := by group
      _ = F.dA.ρ⁻¹ * a * F.dA.ρ := by rw [← hca]; group

theorem frame_isMulCommutative_centralizer_inf (h11 : ¬ 2 ^ 11 ∣ Nat.card G) :
    IsMulCommutative (Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) : Subgroup G) := by
  set K := F.dA.toConfig
  refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
  by_contra hxy
  have hz : ⁅(x : G), (y : G)⁆ ≠ 1 := commutatorElement_ne_one_iff.mpr hxy
  obtain ⟨r, hrN, hr⟩ := frame_exists_frattini_ρ F
  have huvN := frame_mem_normalizer_centralizer_inf F F.dA.uv_mem F.uv_mem_S
  have hcard := frame_card_centralizer_inf_le F h11
  obtain ⟨hzA, hzuv⟩ := conj_commutatorElement_eq_of_central_index_le_four
    (frame_A_le_centralizer_inf F) inf_le_left hcard x.2 y.2 hz huvN
  obtain ⟨-, hzr⟩ := conj_commutatorElement_eq_of_central_index_le_four
    (frame_A_le_centralizer_inf F) inf_le_left hcard x.2 y.2 hz hrN
  set z := ⁅(x : G), (y : G)⁆
  obtain ⟨v, hv⟩ := K.exists_ev hzA
  have h1 : fuv v = v := K.ev_injective (by
    rw [← K.conj_uv_ev, hv]
    show F.dA.uv⁻¹ * z * F.dA.uv = z
    calc F.dA.uv⁻¹ * z * F.dA.uv = F.dA.uv⁻¹ * (F.dA.uv * z * F.dA.uv⁻¹) * F.dA.uv := by
          rw [hzuv]
      _ = z := by group)
  have h2 : fρ v = v := K.ev_injective (by
    rw [← K.conj_ρ_ev, hv]
    show F.dA.ρ⁻¹ * z * F.dA.ρ = z
    rw [← hr z hzA]
    calc r⁻¹ * z * r = r⁻¹ * (r * z * r⁻¹) * r := by rw [hzr]
      _ = z := by group)
  apply hz
  rw [← hv, fuv_fρ_fixed_eq_zero v h1 h2, K.ev_zero]

theorem frame_noInvolutionsCentralizing (h11 : ¬ 2 ^ 11 ∣ Nat.card G) :
    NoInvolutionsCentralizing (F.S : Subgroup G) F.A := by
  intro z hzS hz2 hzC
  by_contra hzA
  set Q := Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) with hQ
  have hQc := frame_isMulCommutative_centralizer_inf F h11
  have hAQ := frame_A_le_centralizer_inf F
  have huvQ := frame_mem_normalizer_centralizer_inf F F.dA.uv_mem F.uv_mem_S
  have htQ := frame_mem_normalizer_centralizer_inf F F.dA.t_mem F.t_mem_S
  obtain ⟨z₁, hz₁Q, hz₁2, hz₁A, hz₁uv, -⟩ := exists_involution_conj_mem hAQ hQc huvQ
    F.dA.uv_mem F.dA.uv_sq htQ F.dA.uv_comm_t (show z ∈ Q from ⟨hzC, hzS⟩) hz2 hzA
  obtain ⟨z₂, hz₂Q, hz₂2, hz₂A, hz₂t, hz₂uv⟩ := exists_involution_conj_mem hAQ hQc htQ
    F.dA.t_mem F.dA.t_sq huvQ F.dA.uv_comm_t.symm hz₁Q hz₁2 hz₁A
  have hE := mem_normalizer_E_of_conj_mem F.dA.toConfig le_rfl (fun b hb _ => hb) hz₂2 hz₂Q.1
    (hz₂uv hz₁uv) hz₂t
  rw [frame_closureE_eq F] at hE
  exact hz₂A (frame_mem_A_of_mem_normalizer_E F hz₂Q.2 hE hz₂Q.1)

theorem frame_pow_four_mem_A (h11 : ¬ 2 ^ 11 ∣ Nat.card G) {q : G}
    (hq : q ∈ Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G)) : q ^ 4 ∈ F.A := by
  set Q := Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) with hQ
  have hAQ : F.A ≤ Q := frame_A_le_centralizer_inf F
  haveI : (F.A.subgroupOf Q).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hc : (n : G) * g = g * n := Subgroup.mem_centralizer_iff.mp g.2.1 n hn
    have : ((g * n * g⁻¹ : Q) : G) = n := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hc, mul_inv_cancel_right]
    rw [this]
    exact hn⟩
  have hidx : (F.A.subgroupOf Q).index ∣ 4 := by
    have h1 := (F.A.subgroupOf Q).card_mul_index
    have h2 : Nat.card (F.A.subgroupOf Q) = 32 := by
      rw [← F.dA.card_eq_32]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAQ).toEquiv
    have h3 := frame_card_centralizer_inf_dvd F h11
    rw [← h1, h2, show (2 : ℕ) ^ 7 = 32 * 4 by norm_num] at h3
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h3
  obtain ⟨k, hk⟩ := hidx
  have h := pow_mem (Subgroup.pow_index_mem (F.A.subgroupOf Q) (⟨q, hq⟩ : Q)) k
  rw [← pow_mul, ← hk, Subgroup.mem_subgroupOf] at h
  exact h

theorem frame_pow_four_eq_one {a : G} (ha : a ∈ F.A) : a ^ 4 = 1 := by
  obtain ⟨v, rfl⟩ := F.dA.toConfig.exists_ev ha
  rw [← Config.ev_nsmul, four_nsmul_eq, Config.ev_zero]

theorem frame_mem_centralizer_of_odd_pow_mem (h11 : ¬ 2 ^ 11 ∣ Nat.card G) {g : G}
    (hgA : g ∈ Subgroup.centralizer (F.A : Set G))
    (hgQ : g ∈ Subgroup.normalizer
      ((Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) : Subgroup G) : Set G))
    {m : ℕ} (hm : Odd m) (hgm : g ^ m ∈ Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G)) :
    g ∈ Subgroup.centralizer
      ((Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) : Subgroup G) : Set G) :=
  mem_centralizer_of_odd_pow_mem (frame_A_le_centralizer_inf F)
    (frame_isMulCommutative_centralizer_inf F h11)
    (fun r hr hr2 => frame_noInvolutionsCentralizing F h11 r hr.2 hr2 hr.1)
    (fun q hq => frame_pow_four_mem_A F h11 hq) (fun a ha => frame_pow_four_eq_one F ha)
    hgA hgQ hm hgm

theorem frame_exists_oddComplement (h11 : ¬ 2 ^ 11 ∣ Nat.card G) :
    ∃ O : Subgroup (Subgroup.normalizer (F.A : Set G)), O.Normal ∧
      O ≤ Subgroup.centralizer (F.configN.A : Set (Subgroup.normalizer (F.A : Set G))) ∧
      ¬ 2 ∣ Nat.card O ∧
      Subgroup.centralizer (F.configN.A : Set (Subgroup.normalizer (F.A : Set G))) ≤
        (Subgroup.centralizer (F.configN.A : Set (Subgroup.normalizer (F.A : Set G))) ⊓
          (frameSylowN F : Subgroup (Subgroup.normalizer (F.A : Set G)))) ⊔ O := by
  set N := Subgroup.normalizer (F.A : Set G)
  set Z := Subgroup.centralizer (F.configN.A : Set N)
  set QN := Z ⊓ (frameSylowN F : Subgroup N) with hQN
  have hQ2 : IsPGroup 2 QN := (frameSylowN F).isPGroup'.to_le inf_le_right
  refine exists_oddComplement_of_normalizer_le_centralizer F.configN.A QN inf_le_left hQ2
    (frame_not_dvd_relIndex_centralizerN F) (fun g hgZ hgN => ?_)
  set H := Z ⊓ Subgroup.normalizer (QN : Set N) with hH
  have hQH : QN ≤ H := le_inf inf_le_left Subgroup.le_normalizer
  haveI : (QN.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQH).mpr inf_le_right
  set m := QN.relIndex H with hm
  have hmZ : m ∣ QN.relIndex Z := by
    rw [hm, ← Subgroup.relIndex_mul_relIndex QN H Z hQH inf_le_left]
    exact dvd_mul_right _ _
  have hmodd : Odd m := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp
    (fun h => frame_not_dvd_relIndex_centralizerN F (h.trans hmZ)))
  have hgm : g ^ m ∈ QN := by
    have := Subgroup.pow_index_mem (QN.subgroupOf H) (⟨g, hgZ, hgN⟩ : H)
    rw [Subgroup.mem_subgroupOf] at this
    exact this
  have hmapQ := frame_map_centralizer_inf_sylowN F
  have hgA : (g : G) ∈ Subgroup.centralizer (F.A : Set G) :=
    (frame_mem_centralizer_configN_iff F g).mp hgZ
  have hgQ : (g : G) ∈ Subgroup.normalizer
      ((Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) : Subgroup G) : Set G) := by
    have := coe_mem_normalizer_map hgN
    rwa [hQN, hmapQ] at this
  have hgmG : (g : G) ^ m ∈ Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) := by
    rw [← hmapQ, ← Subgroup.coe_pow]
    exact Subgroup.mem_map_of_mem _ hgm
  have hC := frame_mem_centralizer_of_odd_pow_mem F h11 hgA hgQ hmodd hgmG
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  apply Subtype.ext
  have hqG : (q : G) ∈ Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) := by
    rw [← hmapQ]
    exact Subgroup.mem_map_of_mem _ hq
  exact (Subgroup.mem_centralizer_iff.mp hC) q hqG

end CFSG.CGT.Stroth76
