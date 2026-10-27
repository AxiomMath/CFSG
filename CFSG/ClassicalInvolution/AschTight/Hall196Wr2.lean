module

public import CFSG.ClassicalInvolution.AschTight.Hall196Act
public import CFSG.ClassicalInvolution.AschTight.S1911EtaStmt

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Hall196

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_sup_mul_card_inf' {A C : Subgroup G} (hC : C ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card ↥(A ⊔ C) * Nat.card ↥(A ⊓ C) = Nat.card A * Nat.card C := by
  have hA : A ≤ A ⊔ C := le_sup_left
  have hCL : C ≤ A ⊔ C := le_sup_right
  have : (A.subgroupOf (A ⊔ C)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hA).mpr (sup_le Subgroup.le_normalizer hC)
  have h1 := Subgroup.relIndex_sup_left (C.subgroupOf (A ⊔ C)) (A.subgroupOf (A ⊔ C))
  rw [← Subgroup.subgroupOf_sup hA hCL, Subgroup.subgroupOf_self, Subgroup.relIndex_top_right,
    Subgroup.relIndex_subgroupOf hCL] at h1
  have h2 := Subgroup.relIndex_mul_card (H := A) (K := A ⊔ C)
  have h3 := Subgroup.relIndex_mul_card (H := A) (K := C)
  rw [inf_eq_left.mpr hA] at h2
  have h4 : A.relIndex (A ⊔ C) = A.relIndex C := by
    rw [Subgroup.relIndex, ← h1]
  rw [← h2, ← h3, h4]
  ring

variable {p f : ℕ} [Fact p.Prime]

omit [Finite G] in
theorem inf_eq_map_of_sec19Data {K : Subgroup G} {S : Sylow 2 G} {Q₀ : Sylow 2 K}
    (hQ : (Q₀ : Subgroup K).map K.subtype ≤ (S : Subgroup G)) :
    (S : Subgroup G) ⊓ K = (Q₀ : Subgroup K).map K.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 (((S : Subgroup G) ⊓ K).subgroupOf K) :=
    (S.isPGroup'.to_le inf_le_left).comap_subtype
  have hle : (Q₀ : Subgroup K) ≤ ((S : Subgroup G) ⊓ K).subgroupOf K := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr ⟨hQ ⟨x, hx, rfl⟩, x.2⟩
  have heq := Q₀.3 h2 hle
  refine le_antisymm (fun x hx => ?_) (le_inf hQ (Subgroup.map_subtype_le _))
  have : (⟨x, hx.2⟩ : K) ∈ ((S : Subgroup G) ⊓ K).subgroupOf K :=
    Subgroup.mem_subgroupOf.mpr hx
  rw [heq] at this
  exact ⟨⟨x, hx.2⟩, this, rfl⟩

theorem inf_mem_rSet {K : Subgroup G} {z : G} {S : Sylow 2 G} {W : Subgroup G}
    (hd : Sec19Data p f K z S W) :
    (S : Subgroup G) ⊓ K ∈ RSet (CoreAssembly.conjClass K) := by
  obtain ⟨Q₀, hQ⟩ := hd.sylow
  rw [inf_eq_map_of_sec19Data hQ]
  exact ⟨K, CoreAssembly.mem_conjClass_self K, Q₀, rfl⟩

theorem le_of_sec19DataT {K : Subgroup G} {z : G} {S : Sylow 2 G}
    {W L : Subgroup G} {t : G} {V : Subgroup G} (hDT : Sec19DataT p f K z S W L t V) :
    V ≤ L := by
  have htb := hDT.tight.toTightBranch
  have hI := isUniqueInvolution_of_tight htb
  obtain ⟨R', hR', hVR', -, -⟩ := hDT.memV
  obtain ⟨J, hJ, Q, rfl⟩ := hR'
  have hVJ : V ≤ J := hVR'.trans (Subgroup.map_subtype_le _)
  have htJ : t ∈ J := hVJ hDT.memT
  obtain ⟨g, rfl⟩ := CoreAssembly.single_class K J hJ
  obtain ⟨g', rfl⟩ := CoreAssembly.single_class K L hDT.memL
  have h1 : t = g * z * g⁻¹ :=
    ((hI.conj g).unique t htJ hDT.invL.sq).resolve_left hDT.invL.ne_one
  have h2 : g' * z * g'⁻¹ = t := (hI.conj g').eq hDT.invL
  rw [conjSub_eq_conjSub_of_tight htb (h1.symm.trans h2.symm)] at hVJ
  exact hVJ

omit [Finite G] in
theorem mem_zpowers_of_isUniqueInvolution {L : Subgroup G} {t c : G}
    (hL : IsUniqueInvolution L t) (hcL : c ∈ L) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hc1 : c ≠ 1) : t ∈ Subgroup.zpowers c :=
  mem_zpowers_of_isPGroup hc2 (fun y hy hy2 => hL.unique y
    ((Subgroup.zpowers_le.mpr hcL) hy) hy2) (Subgroup.mem_zpowers c) hc1

theorem inf_le_of_etaFacts {K : Subgroup G} {z : G} {S : Sylow 2 G}
    {W L : Subgroup G} {t : G} {V : Subgroup G} (hDT : Sec19DataT p f K z S W L t V)
    (ef : S1911.EtaFacts K z S W V) : L ⊓ W ≤ V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVL := le_of_sec19DataT hDT
  have hCV : W ⊓ sec19Y K z ≤ Subgroup.normalizer (V : Set G) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro v
    constructor
    · intro hv
      have e : c * v * c⁻¹ = v := by
        rw [ef.comm c hc.1 v (hDT.leW hv)]
        group
      rw [e]
      exact hv
    · intro hv
      have hv' : v ∈ W := by
        have h1 : c⁻¹ * (c * v * c⁻¹) * c = v := by group
        rw [← h1]
        exact W.mul_mem (W.mul_mem (W.inv_mem hc.1) (hDT.leW hv)) hc.1
      have e : c * v * c⁻¹ = v := by
        rw [ef.comm c hc.1 v hv']
        group
      rwa [e] at hv
  rintro w ⟨hwL, hwW⟩
  have hw : w ∈ ((V ⊔ (W ⊓ sec19Y K z) : Subgroup G) : Set G) := ef.sup_eq ▸ hwW
  rw [Subgroup.coe_mul_of_right_le_normalizer_left V _ hCV] at hw
  obtain ⟨v, hv, c, hc, rfl⟩ := Set.mem_mul.mp hw
  have hcL : c ∈ L := by
    have e : c = v⁻¹ * (v * c) := by group
    rw [e]
    exact L.mul_mem (L.inv_mem (hVL hv)) hwL
  by_cases hc1 : c = 1
  · rw [hc1, mul_one]
    exact hv
  exfalso
  have hc2 : IsPGroup 2 (Subgroup.zpowers c) :=
    S.isPGroup'.to_le (Subgroup.zpowers_le.mpr (hDT.toSec19Data.hWS hc.1))
  have htc := mem_zpowers_of_isUniqueInvolution hDT.invL hcL hc2 hc1
  have htY : t ∈ sec19Y K z := (Subgroup.zpowers_le.mpr hc.2) htc
  have ht : t ∈ V ⊓ sec19Y K z := ⟨hDT.memT, htY⟩
  rw [ef.disj, Subgroup.mem_bot] at ht
  exact hDT.invL.ne_one ht

theorem eq_of_mem_of_sec19DataT {K : Subgroup G} {z : G} {S : Sylow 2 G}
    {W L : Subgroup G} {t : G} {V : Subgroup G} (hDT : Sec19DataT p f K z S W L t V)
    {J : Subgroup G} (hJ : J ∈ CoreAssembly.conjClass K) (htJ : t ∈ J) : J = L := by
  have htb := hDT.tight.toTightBranch
  have hI := isUniqueInvolution_of_tight htb
  obtain ⟨g, rfl⟩ := CoreAssembly.single_class K J hJ
  obtain ⟨g', hg'⟩ := CoreAssembly.single_class K L hDT.memL
  rw [hg'] at hDT ⊢
  have h1 : t = g * z * g⁻¹ :=
    ((hI.conj g).unique t htJ hDT.invL.sq).resolve_left hDT.invL.ne_one
  have h2 : g' * z * g'⁻¹ = t := (hI.conj g').eq hDT.invL
  exact conjSub_eq_conjSub_of_tight htb (h1.symm.trans h2.symm)

theorem exists_isSylow2In_of_sec19DataT {K : Subgroup G} {z : G} {S : Sylow 2 G}
    {W L : Subgroup G} {t : G} {V : Subgroup G} (hDT : Sec19DataT p f K z S W L t V) :
    ∃ R' : Subgroup G, IsSylow2In R' L ∧ V ≤ R' ∧ Nat.card R' = 2 * Nat.card V := by
  obtain ⟨R', hR', hVR', -, hidx⟩ := hDT.memV
  obtain ⟨J, hJ, hR'J, hR'2, hmax⟩ := mem_RSet_iff.mp hR'
  have hJL : J = L := eq_of_mem_of_sec19DataT hDT hJ (hR'J (hVR' hDT.memT))
  subst hJL
  refine ⟨R', ⟨hR'J, hR'2, hmax⟩, hVR', ?_⟩
  have h1 := Subgroup.relIndex_mul_card (H := V) (K := R')
  rw [inf_eq_left.mpr hVR', hidx] at h1
  exact h1.symm

theorem isSylow2In_inf_centralizer {K : Subgroup G} {z : G} {S : Sylow 2 G}
    {W L : Subgroup G} {t : G} {V : Subgroup G} (hDT : Sec19DataT p f K z S W L t V) :
    IsSylow2In V (L ⊓ Subgroup.centralizer ({z} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd := hDT.toSec19Data
  have htb := hd.tight.toTightBranch
  have hI := isUniqueInvolution_of_tight htb
  have hVL := le_of_sec19DataT hDT
  have hVS : V ≤ (S : Subgroup G) := hDT.leW.trans hd.hWS
  refine ⟨le_inf hVL (hVS.trans hd.hSz), S.isPGroup'.to_le hVS, fun T hT hT2 hVT => ?_⟩
  obtain ⟨R', hR', hVR', hcard⟩ := exists_isSylow2In_of_sec19DataT hDT
  by_contra hne
  have hle : Nat.card R' ≤ Nat.card T := by
    rw [hcard]
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hVT
    have hpos : 0 < Nat.card V := Nat.card_pos
    rcases k with _ | _ | k
    · rw [mul_zero] at hk
      exact absurd hk Nat.card_pos.ne'
    · exact absurd (Subgroup.eq_of_le_of_card_ge hVT (by omega)).symm hne
    · nlinarith
  have hTsyl : IsSylow2In T L := IsSylow2In.of_natCard_le hR' hT2 (hT.trans inf_le_left) hle
  have hTR : T ∈ RSet (CoreAssembly.conjClass K) := mem_RSet_of_isSylow2In hDT.memL hTsyl
  have hLK : L ≠ K := by
    rintro rfl
    exact hDT.ne (hI.eq hDT.invL).symm
  apply hd.tight.edgeless K (CoreAssembly.mem_conjClass_self K) L hDT.memL
  left
  refine ⟨hDT.memL, hLK, T, hTR, hT.trans inf_le_left, ?_⟩
  rw [normalizer_eq_centralizer_of_tight htb]
  exact hT.trans inf_le_right

end CFSG.ClassicalInvolution.Disconnected.AschTight.Hall196
