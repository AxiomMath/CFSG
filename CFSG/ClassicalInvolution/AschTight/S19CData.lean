module

public import CFSG.ClassicalInvolution.AschTight.S19BFus

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19C

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

theorem exists_dData_K_of (hd : Sec19DataT p f K z S W L t V) {r : G}
    (hrR : r ∈ (S : Subgroup G) ⊓ K) (hrU : r ∉ K ⊓ W) :
    ∃ u : G, ∃ K' : Subgroup G, Subgroup.zpowers u = K ⊓ W ∧
      Sec71.DData (CoreAssembly.conjClass K) W ((S : Subgroup G) ⊓ K) K' u r z := by
  have hd0 := hd.toSec19Data
  have ht := hd.tight
  have hI := isUniqueInvolution_of_tight ht.toTightBranch
  obtain ⟨-, -, -, hcyc, -⟩ := S19B.inf_mem_USet hd
  obtain ⟨u, hu⟩ := S19B.exists_zpowers_eq_of_isCyclic hcyc
  have hRW : (S : Subgroup G) ⊓ K ⊓ W = K ⊓ W := by
    ext x
    exact ⟨fun hx => ⟨hx.1.2, hx.2⟩, fun hx => ⟨⟨hd.hWS hx.2, hx.1⟩, hx.2⟩⟩
  have hcard : Nat.card ↥((S : Subgroup G) ⊓ K) = 2 * Nat.card (Subgroup.zpowers u) := by
    rw [hu]
    exact S1911.card_inf_eq hd0
  have huKW : u ∈ K ⊓ W := hu ▸ Subgroup.mem_zpowers u
  have huR : u ∈ (S : Subgroup G) ⊓ K := ⟨hd.hWS huKW.2, huKW.1⟩
  have hRD : (S : Subgroup G) ⊓ K ∈ DSet (CoreAssembly.conjClass K) W :=
    ⟨S1911.inf_mem_rSet hd0, fun x hx => S19B.le_normalizer_W hd hx.1⟩
  obtain ⟨K', z', hdd⟩ := Sec71.exists_dData ht.branch.odd ht.branch.five
    (hypOmegaMod_of_tightD ht) hd.hW hRD (hu.trans hRW.symm)
    (S19B.closure_pair_eq_of_card huR hcard hrR (hu ▸ hrU))
  have hzR : z ∈ (S : Subgroup G) ⊓ K := ⟨hd.hWS (Hall196.mem_W_of_sec19DataT hd), hI.mem⟩
  have hz := hdd.uinv.unique z (hdd.le hzR) hI.sq
  have hzz : z' = z := (hz.resolve_left hI.ne_one).symm
  exact ⟨u, K', hu, hzz ▸ hdd⟩

theorem exists_RL (hd : Sec19DataT p f K z S W L t V) {a : G} (haS : a ∈ (S : Subgroup G))
    (hat : a ∈ Subgroup.centralizer ({t} : Set G)) :
    ∃ RL : Subgroup G, ∃ v : G, IsSylow2In RL L ∧ conjSub a RL = RL ∧
      RL ∈ DSet (CoreAssembly.conjClass K) W ∧ Subgroup.zpowers v = RL ⊓ W ∧
      Subgroup.zpowers v = V ∧ Nat.card RL = 2 * Nat.card (Subgroup.zpowers v) := by
  have ht := hd.tight
  have hp := ht.branch.odd
  have hq := ht.branch.five
  have hΩ := hypOmegaMod_of_tightD ht
  obtain ⟨RL, hRL, haRL, hWRL, hVRL, hcardRL⟩ := S1911.exists_sylow_member_of_mem_A hd haS hat
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
  obtain ⟨v, hv⟩ := S19B.exists_zpowers_eq_of_isCyclic hVcyc
  exact ⟨RL, v, hRL, haRL, ⟨hRLR, hRLN⟩, hv.trans hRLW.symm, hv, by rw [hv]; exact hcardRL⟩

theorem exists_dData_L_of (hd : Sec19DataT p f K z S W L t V) {RL : Subgroup G} {v rL : G}
    (hRLD : RL ∈ DSet (CoreAssembly.conjClass K) W)
    (hv : Subgroup.zpowers v = RL ⊓ W) (hvV : Subgroup.zpowers v = V)
    (hcard : Nat.card RL = 2 * Nat.card (Subgroup.zpowers v)) (hrL : rL ∈ RL)
    (hrLV : rL ∉ Subgroup.zpowers v) :
    ∃ L' : Subgroup G, Sec71.DData (CoreAssembly.conjClass K) W RL L' v rL t := by
  have ht := hd.tight
  have hvRL : v ∈ RL := (hv ▸ Subgroup.mem_zpowers v : v ∈ RL ⊓ W).1
  obtain ⟨L', t', hdd⟩ := Sec71.exists_dData ht.branch.odd ht.branch.five
    (hypOmegaMod_of_tightD ht) hd.hW hRLD hv (S19B.closure_pair_eq_of_card hvRL hcard hrL hrLV)
  have htRL : t ∈ RL := (hv ▸ (hvV ▸ hd.memT : t ∈ Subgroup.zpowers v) : t ∈ RL ⊓ W).1
  have htt := hdd.uinv.unique t (hdd.le htRL) hd.invL.sq
  have htt' : t' = t := (htt.resolve_left hd.invL.ne_one).symm
  exact ⟨L', htt' ▸ hdd⟩

theorem conj_eq_of_dData (hd : Sec19DataT p f K z S W L t V) {R RL K' L' : Subgroup G}
    {u r v rL : G} (hdK : Sec71.DData (CoreAssembly.conjClass K) W R K' u r z)
    (hdL : Sec71.DData (CoreAssembly.conjClass K) W RL L' v rL t) :
    conjSub (r⁻¹ * rL) K' = L' ∧ (r⁻¹ * rL) * z * (r⁻¹ * rL)⁻¹ = t := by
  have ht := hd.tight
  have hp := ht.branch.odd
  have hq := ht.branch.five
  have hΩ := hypOmegaMod_of_tightD ht
  have hWc := S1911.comm_of_mem hd.toSec19Data
  have hW2 : IsPGroup 2 W := S.isPGroup'.to_le hd.hWS
  have hzt : z ≠ t := fun h => hd.ne h.symm
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
      (S19B.aEmpty_of_tightD ht hdK.memK)
  have hconj := Sec71.conj_eq_of_four_dvd hΩ hdK hdL hW2 hWc hzt hi hk hio h4
  have h1 : conjSub (r⁻¹ * rL) K' = L' := by
    rw [conjSub_mul, hconj, conjSub_inv_conjSub]
  refine ⟨h1, ?_⟩
  have h2 := hdK.uinv.conj (r⁻¹ * rL)
  rw [h1] at h2
  exact (hdL.uinv.eq h2).symm

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19C
