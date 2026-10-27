module

public import CFSG.Sporadic.J4.QT2LocMain
public import CFSG.Sporadic.J4.QT2LocCntProof
public import CFSG.Sporadic.J4.QTRankProof
public import CFSG.Sporadic.J4.QTCheck
public meta import CFSG.Sporadic.J4.QT2LocNative
public import Certificates.Certificate4002
public import Certificates.Certificate4008
public import Certificates.Certificate4017
public import Certificates.Certificate4117
public import Certificates.Certificate3084
public import CFSG.Sporadic.J4.QT2LocMainBase
public import CFSG.Sporadic.J4.QTOutChar
public import CFSG.Sporadic.J4Base

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2

theorem table_comm_of_commute (hM : MatFacts) {c : ℕ} {τ T : List ℕ} {h v : J}
    (hh : Acts h τ) (hv : Acts v T) (hcomm : eta uJ 11 c * h * v = v * (eta uJ 11 c * h)) :
    compT τ T = compT T τ := by
  have h1 : Acts (eta uJ 11 c * h) τ := hh.eta_mul hM (eta_mem_Eg 11 le_rfl c)
  have h2 := h1.mul hv
  have h3 := hv.mul h1
  rw [hcomm] at h2
  exact Acts.unique hM h2 h3

theorem K_eq_union (hM : MatFacts) (P : List (List ℕ × J))
    (hP : ∀ p ∈ P, Acts p.2 p.1 ∧ actT p.1 1 = 1) (hnd : (P.map Prod.fst).Nodup)
    (hcard : P.length * 2048 = Nat.card ↥(Subgroup.centralizer ({eta uJ 11 1} : Set J))) :
    ∀ x : J, x * eta uJ 11 1 = eta uJ 11 1 * x →
      ∃ p ∈ P, ∃ c < 2048, x = eta uJ 11 c * p.2 := by
  classical
  set K := Subgroup.centralizer ({eta uJ 11 1} : Set J) with hK
  have hmemK : ∀ p ∈ P, ∀ c : ℕ, eta uJ 11 c * p.2 ∈ K := by
    intro p hp c
    rw [hK, Subgroup.mem_centralizer_singleton_iff]
    have h1 : p.2 * eta uJ 11 1 * p.2⁻¹ = eta uJ 11 1 := by
      rw [(hP p hp).1.2 1 (by norm_num), (hP p hp).2]
    have h2 : p.2 * eta uJ 11 1 = eta uJ 11 1 * p.2 := by
      calc p.2 * eta uJ 11 1 = (p.2 * eta uJ 11 1 * p.2⁻¹) * p.2 := by group
        _ = eta uJ 11 1 * p.2 := by rw [h1]
    have h3 : eta uJ 11 c * eta uJ 11 1 = eta uJ 11 1 * eta uJ 11 c :=
      Eg_comm (elem_uJ hM) (eta_mem_Eg 11 le_rfl c) (eta_mem_Eg 11 le_rfl 1)
    calc eta uJ 11 c * p.2 * eta uJ 11 1 = eta uJ 11 c * (p.2 * eta uJ 11 1) := by group
      _ = eta uJ 11 c * (eta uJ 11 1 * p.2) := by rw [h2]
      _ = (eta uJ 11 c * eta uJ 11 1) * p.2 := by group
      _ = (eta uJ 11 1 * eta uJ 11 c) * p.2 := by rw [h3]
      _ = eta uJ 11 1 * (eta uJ 11 c * p.2) := by group
  let g : {p // p ∈ P} × Fin 2048 → J := fun d => eta uJ 11 (d.2 : ℕ) * d.1.1.2
  have hfst : ∀ p ∈ P, ∀ q ∈ P, p.1 = q.1 → p = q :=
    fun p hp q hq e => List.inj_on_of_nodup_map hnd hp hq e
  have hginj : Function.Injective g := by
    rintro ⟨⟨p, hp⟩, c⟩ ⟨⟨q, hq⟩, c'⟩ e'
    have hp' : Acts (eta uJ 11 (c : ℕ) * p.2) p.1 :=
      (hP p hp).1.eta_mul hM (eta_mem_Eg 11 le_rfl c)
    have hq' : Acts (eta uJ 11 (c' : ℕ) * q.2) q.1 :=
      (hP q hq).1.eta_mul hM (eta_mem_Eg 11 le_rfl c')
    have e'' : eta uJ 11 (c : ℕ) * p.2 = eta uJ 11 (c' : ℕ) * q.2 := e'
    rw [e''] at hp'
    have hpq : p = q := hfst p hp q hq (Acts.unique hM hp' hq')
    subst hpq
    have e2 : eta uJ 11 (c : ℕ) = eta uJ 11 (c' : ℕ) := mul_right_cancel e''
    have hcc : (c : ℕ) = c' := eta_inj hM c (by omega) c' (by omega) e2
    rw [Fin.ext hcc]
  have hsub : Set.range g ⊆ (K : Set J) := by
    rintro _ ⟨⟨⟨p, hp⟩, c⟩, rfl⟩
    exact hmemK p hp c
  have hcardD : Nat.card ({p // p ∈ P} × Fin 2048) = P.length * 2048 := by
    rw [Nat.card_prod]
    have hnodup : P.Nodup := List.Nodup.of_map _ hnd
    have e2 : Nat.card {p // p ∈ P} = Nat.card {p // p ∈ P.toFinset} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun x => List.mem_toFinset.symm)
    rw [e2, Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hnodup]
    simp
  have hrange : (Set.range g).ncard = P.length * 2048 := by
    rw [← Nat.card_coe_set_eq, Nat.card_range_of_injective hginj, hcardD]
  have hKn : (K : Set J).ncard = P.length * 2048 := by
    rw [← Nat.card_coe_set_eq]
    exact hcard.symm
  have heq : Set.range g = (K : Set J) :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hKn, hrange]) (Set.toFinite _)
  intro x hx
  have hxK : x ∈ (K : Set J) := by
    rw [hK]
    exact Subgroup.mem_centralizer_singleton_iff.2 hx
  rw [← heq] at hxK
  obtain ⟨⟨⟨p, hp⟩, c⟩, hfc⟩ := hxK
  exact ⟨p, hp, c, c.2, hfc.symm⟩

noncomputable def tFin : Finset J := (tMasks.map (eta uJ 11)).toFinset

theorem mem_tFin {x : J} : x ∈ tFin ↔ ∃ c ∈ tMasks, eta uJ 11 c = x := by
  simp [tFin]

theorem tMasks_facts :
    tMasks.length = 276 ∧ tMasks.Nodup ∧ ∀ c ∈ tMasks, c < 2048 :=
  Certificates.certificate4117.1

theorem card_tFin (hM : MatFacts) : tFin.card = 276 := by
  obtain ⟨h1, h2, h3⟩ := tMasks_facts
  rw [tFin, List.toFinset_card_of_nodup, List.length_map, h1]
  rw [List.nodup_map_iff_inj_on h2]
  intro c hc d hd e
  exact eta_inj hM c (h3 c hc) d (h3 d hd) e

theorem tFin_conj (hM : MatFacts) :
    ∀ h ∈ Hj, ∀ x ∈ tFin, h * x * h⁻¹ ∈ tFin := by
  intro h hh x hx
  obtain ⟨c, hc, rfl⟩ := mem_tFin.1 hx
  obtain ⟨c', hc', e⟩ := (tSet_conj hM h hh).1 (eta uJ 11 c) ⟨c, hc, rfl⟩
  exact mem_tFin.2 ⟨c', hc', e.symm⟩

theorem exists_conj_eta_one_of_mem_tMasks_hroot :
    (orbits.getD 0 (1, [], [])).1 = 1 :=
  Certificates.certificate4117.2

theorem exists_conj_eta_one_of_mem_tMasks (hM : MatFacts) {c : ℕ} (hc : c ∈ tMasks) :
    ∃ g ∈ Hj, g * eta uJ 11 1 * g⁻¹ = eta uJ 11 c := by
  have hroot : (orbits.getD 0 (1, [], [])).1 = 1 := exists_conj_eta_one_of_mem_tMasks_hroot
  have hoo : orbits.getD 0 (1, [], []) ∈ orbits := by
    by_contra hnot
    have hdef : orbits.getD 0 (1, [], []) = (1, [], []) := by
      rw [List.getD_eq_getElem?_getD]
      cases h : orbits[0]? with
      | none => rfl
      | some y =>
        exact absurd (List.mem_of_getElem? h) (by simpa [List.getD_eq_getElem?_getD, h] using hnot)
    have hz : tMasks = [] := by
      simp only [tMasks, hdef]
      rfl
    rw [hz] at hc
    simp at hc
  obtain ⟨p, hp, rfl⟩ : ∃ p ∈ (orbits.getD 0 (1, [], [])).2.1, p.1 = c := by
    simpa [tMasks] using hc
  obtain ⟨hlet, hfold⟩ := orbit_words _ hoo p hp
  rw [hroot] at hfold
  refine ⟨(p.2.map XJ).prod, ?_, ?_⟩
  · refine Subgroup.list_prod_mem Hj ?_
    intro x hx
    obtain ⟨ℓ, hℓ, rfl⟩ := List.mem_map.1 hx
    exact XJ_mem (hlet ℓ hℓ)
  · rw [word_conj XJ act p.2 (fun ℓ hℓ => hX_all hM (hlet ℓ hℓ)), hfold]

theorem tFin_trans (hM : MatFacts) : ∀ x ∈ tFin, ∃ h ∈ Hj, h * eta uJ 11 1 * h⁻¹ = x := by
  intro x hx
  obtain ⟨c, hc, rfl⟩ := mem_tFin.1 hx
  exact exists_conj_eta_one_of_mem_tMasks hM hc

theorem card_centralizer_eta_one :
    Nat.card ↥(Subgroup.centralizer ({eta uJ 11 1} : Set J)) = 1816657920 := by
  have hM := j4Facts.mat
  have hz : eta uJ 11 1 ∈ tFin := mem_tFin.2 ⟨1, one_mem_tMasks, rfl⟩
  have hHM := card_eq_card_mul_centralizer Hj (eta uJ 11 1) tFin hz (tFin_conj hM)
    (fun x hx => tFin_trans hM x hx)
  have hle : Subgroup.centralizer ({eta uJ 11 1} : Set J) ≤ Hj := by
    intro x hx
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 hx
    have h2 : x * eta uJ 11 1 = eta uJ 11 1 * x := h1
    exact centralizer_eta_one_le_Hj h2
  have hinf : Subgroup.centralizer ({eta uJ 11 1} : Set J) ⊓ Hj =
      Subgroup.centralizer ({eta uJ 11 1} : Set J) := le_antisymm inf_le_left (le_inf le_rfl hle)
  rw [hinf, card_Hj j4Facts, card_tFin hM] at hHM
  omega

end CFSG.QuasithinUnique.A5
