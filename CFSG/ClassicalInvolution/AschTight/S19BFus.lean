module

public import CFSG.ClassicalInvolution.AschTight.S19BAE
public import CFSG.ClassicalInvolution.AschTight.Hall196QD
public import CFSG.ClassicalInvolution.AschTight.S19BWC
public import CFSG.ClassicalInvolution.AschTight.Sec71D12
public import CFSG.ClassicalInvolution.AschTight.Sec71Good2

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19B

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] [Finite G]

theorem closure_pair_eq_of_card {R : Subgroup G} {u r : G} (huR : u ∈ R)
    (hcard : Nat.card R = 2 * Nat.card (Subgroup.zpowers u)) (hrR : r ∈ R)
    (hrU : r ∉ Subgroup.zpowers u) : R = Subgroup.closure {u, r} := by
  set H := Subgroup.closure ({u, r} : Set G) with hH
  have hHR : H ≤ R := (Subgroup.closure_le R).mpr (by
    rintro x (rfl | rfl)
    · exact huR
    · exact hrR)
  have hUH : Subgroup.zpowers u ≤ H :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert u _))
  have hrH : r ∈ H := Subgroup.subset_closure (Set.mem_insert_of_mem u rfl)
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hUH
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hHR
  have hpos : 0 < Nat.card (Subgroup.zpowers u) := Nat.card_pos
  have hk1 : k ≠ 1 := by
    rintro rfl
    rw [mul_one] at hk
    have e := Subgroup.eq_of_le_of_card_ge hUH hk.le
    rw [← e] at hrH
    exact hrU hrH
  have hkm : k * m = 2 := by
    have := hcard
    rw [hm, hk, mul_assoc] at this
    have h2 : Nat.card (Subgroup.zpowers u) * (k * m) = Nat.card (Subgroup.zpowers u) * 2 := by
      rw [this]
      ring
    exact Nat.eq_of_mul_eq_mul_left hpos h2
  have hm1 : m = 1 := by
    rcases Nat.dvd_prime Nat.prime_two |>.mp ⟨k, by rw [← hkm, mul_comm]⟩ with h | h
    · exact h
    · exfalso
      rw [h] at hkm
      have : k = 1 := by omega
      exact hk1 this
  rw [hm1, mul_one] at hm
  exact (Subgroup.eq_of_le_of_card_ge hHR hm.le).symm

variable {p f : ℕ} [Fact p.Prime] [IsSimpleGroup G] {K : Subgroup G} {z : G} {S : Sylow 2 G}
  {W L : Subgroup G} {t : G} {V : Subgroup G}

theorem inf_mem_USet (hd : Sec19DataT p f K z S W L t V) :
    K ⊓ W ∈ USet (CoreAssembly.conjClass K) := by
  have hd0 := hd.toSec19Data
  obtain ⟨η, S', hη, hinv, hWη, hηS⟩ := S1911.exists_eta hd0
  exact (hη.1 (S1911.inf_mem_eta hd0 hη hinv hWη hηS)).1

omit [Finite G] [IsSimpleGroup G] in
theorem exists_zpowers_eq_of_isCyclic {C : Subgroup G} (hC : IsCyclic C) :
    ∃ c : G, Subgroup.zpowers c = C := by
  obtain ⟨c, hc⟩ := hC.exists_generator
  exact ⟨c, (Hall196.eq_zpowers_of_generator hc).symm⟩

theorem exists_dData_K (hd : Sec19DataT p f K z S W L t V) :
    ∃ u r : G, ∃ K' : Subgroup G, ∃ z' : G, r ∈ (S : Subgroup G) ⊓ K ∧
      Sec71.DData (CoreAssembly.conjClass K) W ((S : Subgroup G) ⊓ K) K' u r z' ∧ z' = z := by
  have hd0 := hd.toSec19Data
  have ht := hd.tight
  have hI := isUniqueInvolution_of_tight ht.toTightBranch
  obtain ⟨-, -, -, hcyc, -⟩ := inf_mem_USet hd
  obtain ⟨u, hu⟩ := exists_zpowers_eq_of_isCyclic hcyc
  have hRW : (S : Subgroup G) ⊓ K ⊓ W = K ⊓ W := by
    ext x
    exact ⟨fun hx => ⟨hx.1.2, hx.2⟩, fun hx => ⟨⟨hd.hWS hx.2, hx.1⟩, hx.2⟩⟩
  have hcard : Nat.card ↥((S : Subgroup G) ⊓ K) = 2 * Nat.card (Subgroup.zpowers u) := by
    rw [hu]
    exact S1911.card_inf_eq hd0
  obtain ⟨r, hrR, hrU⟩ := S1911.exists_mem_not_mem hcard
  have huKW : u ∈ K ⊓ W := hu ▸ Subgroup.mem_zpowers u
  have huR : u ∈ (S : Subgroup G) ⊓ K := ⟨hd.hWS huKW.2, huKW.1⟩
  have hRD : (S : Subgroup G) ⊓ K ∈ DSet (CoreAssembly.conjClass K) W :=
    ⟨S1911.inf_mem_rSet hd0, fun x hx => le_normalizer_W hd hx.1⟩
  obtain ⟨K', z', hdd⟩ := Sec71.exists_dData ht.branch.odd ht.branch.five
    (hypOmegaMod_of_tightD ht) hd.hW hRD (hu.trans hRW.symm)
    (closure_pair_eq_of_card huR hcard hrR hrU)
  have hzR : z ∈ (S : Subgroup G) ⊓ K := ⟨hd.hWS (Hall196.mem_W_of_sec19DataT hd), hI.mem⟩
  have hz := hdd.uinv.unique z (hdd.le hzR) hI.sq
  exact ⟨u, r, K', z', hrR, hdd, (hz.resolve_left hI.ne_one).symm⟩

theorem exists_dData_L (hd : Sec19DataT p f K z S W L t V) {b : G}
    (hbS : b ∈ (S : Subgroup G)) (hbt : b ∈ Subgroup.centralizer ({t} : Set G)) :
    ∃ RL : Subgroup G, ∃ v rL : G, ∃ L' : Subgroup G, ∃ t' : G, IsSylow2In RL L ∧
      conjSub b RL = RL ∧ rL ∈ RL ∧
      Sec71.DData (CoreAssembly.conjClass K) W RL L' v rL t' ∧ t' = t := by
  have ht := hd.tight
  have hp := ht.branch.odd
  have hq := ht.branch.five
  have hΩ := hypOmegaMod_of_tightD ht
  obtain ⟨RL, hRL, hbRL, hWRL, hVRL, hcardRL⟩ := S1911.exists_sylow_member_of_mem_A hd hbS hbt
  have hRLR : RL ∈ RSet (CoreAssembly.conjClass K) := mem_RSet_of_isSylow2In hd.memL hRL
  have hWN : W ≤ Subgroup.normalizer (RL : Set G) := fun w hw =>
    mem_normalizer_iff_conjSub_eq.mpr (hWRL w hw)
  have hP : IsPGroup 2 ↥(W ⊔ RL) :=
    IsPGroup.to_sup_of_normal_right' (S.isPGroup'.to_le hd.hWS) hRL.2.1 hWN
  obtain ⟨S₁, hS₁⟩ := hP.exists_le_sylow
  obtain ⟨η, hη, hWη⟩ := hd.hW
  have hηS₁ : ∀ U ∈ η, U ≤ (S₁ : Subgroup G) := fun U hU =>
    ((hWη ▸ le_iSup₂_of_le (f := fun U' (_ : U' ∈ η) => U') U hU le_rfl : U ≤ W).trans
      le_sup_left).trans hS₁
  have h610 := (l6_10_proved p f hp hq G _ hΩ S₁ η hη hηS₁).1
  have hRLN : RL ≤ Subgroup.normalizer (W : Set G) := fun x hx => by
    rw [mem_normalizer_iff_conjSub_eq, hWη]
    exact Sec7.conjSub_iSup_eq_of_forall_mem (h610 RL hRLR (le_sup_right.trans hS₁) x hx)
  have hRLW : RL ⊓ W = V := by
    refine le_antisymm (fun x hx => ?_) (le_inf hVRL hd.leW)
    have hx : x ∈ (S : Subgroup G) ⊓ L := ⟨hd.hWS hx.2, hRL.1 hx.1⟩
    rwa [S1911.inf_member_eq hd] at hx
  obtain ⟨-, -, -, hVcyc, -⟩ := hd.memV
  obtain ⟨v, hv⟩ := exists_zpowers_eq_of_isCyclic hVcyc
  have hcard : Nat.card RL = 2 * Nat.card (Subgroup.zpowers v) := by
    rw [hv]
    exact hcardRL
  obtain ⟨rL, hrRL, hrV⟩ := S1911.exists_mem_not_mem hcard
  have hvRL : v ∈ RL := hVRL (hv ▸ Subgroup.mem_zpowers v)
  obtain ⟨L', t', hdd⟩ := Sec71.exists_dData hp hq hΩ hd.hW ⟨hRLR, hRLN⟩ (hv.trans hRLW.symm)
    (closure_pair_eq_of_card hvRL hcard hrRL hrV)
  have htt := hdd.uinv.unique t (hdd.le (hVRL hd.memT)) hd.invL.sq
  exact ⟨RL, v, rL, L', t', hRL, hbRL, hrRL, hdd, (htt.resolve_left hd.invL.ne_one).symm⟩

theorem exists_conj_eq_t_of_centralizes (hd : Sec19DataT p f K z S W L t V) {b : G}
    (hbS : b ∈ (S : Subgroup G))
    (hbR : b ∈ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G))
    (hbW : b ∈ Subgroup.centralizer (W : Set G)) (hbL : b ∈ centralizerModOdd ⊤ L) :
    ∃ g : G, g * b = b * g ∧ g * z * g⁻¹ = t := by
  have ht := hd.tight
  have hp := ht.branch.odd
  have hq := ht.branch.five
  have hΩ := hypOmegaMod_of_tightD ht
  have hWc := S1911.comm_of_mem hd.toSec19Data
  have hW2 : IsPGroup 2 W := S.isPGroup'.to_le hd.hWS
  have hbt : b ∈ Subgroup.centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hbW t (S1911.mem_W hd)).symm
  obtain ⟨u, r, K', z', hrR, hdK, hz'⟩ := exists_dData_K hd
  subst hz'
  obtain ⟨RL, v, rL, L', t', hRL, hbRL, hrRL, hdL, ht'⟩ := exists_dData_L hd hbS hbt
  subst ht'
  have hzt : z' ≠ t' := fun h => hd.ne h.symm
  have hKL : K' ≠ L' := fun h => hzt (hdK.uinv.eq (h ▸ hdL.uinv))
  obtain ⟨i, hi⟩ := hdK.exists_rel hdL.u_memW (hdK.le_normalizer hdL.u_memW)
  obtain ⟨k, hk⟩ := hdL.exists_rel hdK.u_memW (hdL.le_normalizer hdK.u_memW)
  have hedge : ∀ J₁ ∈ CoreAssembly.conjClass K, ∀ J₂ ∈ CoreAssembly.conjClass K,
      J₂ ∉ omegaNbr (CoreAssembly.conjClass K) J₁ := fun J₁ h₁ J₂ h₂ h =>
    ht.edgeless J₁ h₁ J₂ h₂ (Or.inl h)
  have hio : Odd i := by
    by_contra hie
    have hie' : Even i := Int.not_odd_iff_even.mp hie
    have hke := Sec71.even_of_even hp hq hΩ hdK hdL hWc hzt hi hk hie'
    exact hedge K' hdK.memK L' hdL.memK
      (Sec71.case_two_of_even hp hq hΩ hdK hdL hWc hKL hzt hi hk hie' hke).1
  have hko : Odd k := by
    by_contra hke
    exact (Int.not_even_iff_odd.mpr hio)
      (Sec71.even_of_even hp hq hΩ hdL hdK hWc hzt.symm hk hi (Int.not_odd_iff_even.mp hke))
  have h4 : (4 : ℤ) ∣ i * k - 1 := by
    by_contra hbad
    exact Sec71.false_of_not_four_dvd hp hq hΩ hdK hdL hWc hKL hzt hi hk hio hko hbad
      (aEmpty_of_tightD ht hdK.memK)
  have hconj := Sec71.conj_eq_of_four_dvd hΩ hdK hdL hW2 hWc hzt hi hk hio h4
  have hrb : r * b = b * r := Subgroup.mem_centralizer_iff.mp hbR r hrR
  have hrLb : b * rL = rL * b :=
    S1916.commute_of_mem_centralizerModOdd hbL hRL.1 hRL.2.1
      (mem_normalizer_iff_conjSub_eq.mpr hbRL) hrRL
  refine ⟨r⁻¹ * rL, ?_, ?_⟩
  · have hrb' : r⁻¹ * b = b * r⁻¹ := by
      calc r⁻¹ * b = r⁻¹ * (b * r) * r⁻¹ := by group
        _ = r⁻¹ * (r * b) * r⁻¹ := by rw [hrb]
        _ = b * r⁻¹ := by group
    calc r⁻¹ * rL * b = r⁻¹ * (b * rL) := by rw [hrLb]; group
      _ = r⁻¹ * b * rL := by group
      _ = b * r⁻¹ * rL := by rw [hrb']
      _ = b * (r⁻¹ * rL) := by group
  · have h1 : conjSub (r⁻¹ * rL) K' = L' := by
      rw [conjSub_mul, hconj, conjSub_inv_conjSub]
    have h2 := hdK.uinv.conj (r⁻¹ * rL)
    rw [h1] at h2
    exact (hdL.uinv.eq h2).symm

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19B
