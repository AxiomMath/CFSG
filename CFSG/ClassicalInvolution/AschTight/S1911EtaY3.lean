module

public import CFSG.ClassicalInvolution.AschTight.S1911EtaY2
public import CFSG.ClassicalInvolution.AschTight.S1911EtaStmt

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

theorem conjSub_le_of_mem_sylow (hd : Sec19DataT p f K z S W L t V) {y : G}
    (hy : y ∈ (S : Subgroup G)) : conjSub y V ≤ W := by
  have hd0 := hd.toSec19Data
  have htb := hd.tight.toTightBranch
  have hΩ := hypOmegaMod_of_tightD hd.tight
  have hI := isUniqueInvolution_of_tight htb
  obtain ⟨η, S', hη, hinv, hWη, hηS⟩ := exists_eta hd0
  have hU' : conjSub y V ∈ USet (CoreAssembly.conjClass K) :=
    USet.conj hΩ.conjInvariant hd.memV y
  have hU'S : conjSub y V ≤ (S : Subgroup G) := conjSub_le_of_le_of_mem (hd.leW.trans hd.hWS) hy
  obtain ⟨B, ⟨hBη, hB⟩, -⟩ := l6_8 p f hd.tight.branch.odd hd.tight.branch.five G _ hΩ S _
    hU' hU'S η (mem_etaG hη hinv) hηS
  rcases hB with hBeq | hBR
  · rw [hBeq, hWη]
    exact le_iSup₂ (f := fun (C : Subgroup G) (_ : C ∈ η) => C) B hBη
  · exfalso
    obtain ⟨J, hJ, hJsyl⟩ := exists_isSylow2In_of_mem_RSet hBR
    by_cases hJK : J = K
    · have h1 : conjSub y V ≤ K := hJK ▸ (le_sup_left.trans hJsyl.1)
      have hne : K ≠ conjSub y L := by
        intro h
        apply hd.ne
        have h2 : z = y * t * y⁻¹ := hI.eq (h ▸ hd.invL.conj y)
        have hyz : y * z = z * y := Subgroup.mem_centralizer_singleton_iff.mp (hd.hSz hy)
        calc t = y⁻¹ * (y * t * y⁻¹) * y := by group
          _ = y⁻¹ * z * y := by rw [← h2]
          _ = z := by rw [mul_assoc, ← hyz]; group
      have hodd := odd_card_inf_of_tight htb (CoreAssembly.mem_conjClass_self K)
        (hΩ.conjInvariant y L hd.memL) hne
      have hyt : y * t * y⁻¹ ∈ K ⊓ conjSub y L :=
        ⟨h1 (conj_mem_conjSub hd.memT), conj_mem_conjSub hd.invL.mem⟩
      have hu := hd.invL.conj y
      exact hu.ne_one (eq_one_of_isPGroup_of_mem_odd hodd hyt
        (isPGroup_zpowers_of_mul_self_eq_one hu.sq hu.ne_one))
    · refine not_le_normalizer_of_mem_rSet hd.tight.edgeless hJ
        (CoreAssembly.mem_conjClass_self K) hJK hBR hJsyl.1 ?_
      rw [normalizer_eq_centralizer_of_tight htb]
      exact (sup_le hU'S (hηS B hBη)).trans hd.hSz

theorem le_normalizer_of_inf_sec19Y (hd : Sec19DataT p f K z S W L t V) :
    (S : Subgroup G) ⊓ sec19Y K z ≤ Subgroup.normalizer (W : Set G) := by
  have hd0 := hd.toSec19Data
  intro y hy
  have hyC := mem_centralizer_of_mem_inf_sec19Y hd0 hy.1 hy.2
  have hUR : K ⊓ W ≤ (S : Subgroup G) ⊓ K := fun x hx => ⟨hd.hWS hx.2, hx.1⟩
  have hU : conjSub y (K ⊓ W) = K ⊓ W :=
    conjSub_eq_of_mem_normalizer (Subgroup.centralizer_le_normalizer _
      (Subgroup.centralizer_le hUR hyC))
  have hle : conjSub y W ≤ W := by
    calc conjSub y W = conjSub y ((K ⊓ W) ⊔ V) := by rw [← sup_eq_inf_sup hd]
      _ = conjSub y (K ⊓ W) ⊔ conjSub y V := Subgroup.map_sup _ _ _
      _ ≤ W := sup_le (by rw [hU]; exact inf_le_right) (conjSub_le_of_mem_sylow hd hy.1)
  exact mem_normalizer_iff_conjSub_eq.mpr
    (Subgroup.eq_of_le_of_card_ge hle (natCard_conjSub W y).ge)

theorem four_le_card (hd : Sec19DataT p f K z S W L t V) : 4 ≤ Nat.card V := by
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ :=
    (hypOmegaMod_of_tightD hd.tight).exists_data_of_mem_USet hd.tight.branch.odd hd.memV
  exact h4

variable (p f) in
theorem etaYForm : EtaYForm p f := by
  intro G _ _ _ K z S W L t V hd
  exact
    { comm := comm_of_mem hd.toSec19Data
      sup_eq := sup_inf_sec19Y_eq hd
      supU := by rw [inf_comm]; exact sup_eq_inf_sup hd
      disj := inf_sec19Y_eq_bot hd
      cyclic := isCyclic_inf_sec19Y hd
      card := card_inf_sec19Y hd
      four := four_le_card hd
      normalizes := le_normalizer_of_inf_sec19Y hd
      cent := inf_sec19Y_eq hd.toSec19Data }

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
