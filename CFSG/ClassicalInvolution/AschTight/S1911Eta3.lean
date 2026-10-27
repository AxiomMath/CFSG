module

public import CFSG.ClassicalInvolution.AschTight.S1911Eta2

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

theorem conjSub_eq_of_mem_inf (hd : Sec19Data p f K z S W) {r : G}
    (hr : r ∈ (S : Subgroup G) ⊓ K) : conjSub r W = W := by
  obtain ⟨η, S', hη, hinv, hWη, hηS⟩ := exists_eta hd
  rw [hWη]
  exact conjSub_iSup_eq (conjSub_mem_eta hd hη hinv hηS (inf_mem_rSet hd) inf_le_left hr)

omit [IsSimpleGroup G] in
theorem mem_normalizer_of_mem_W (hd : Sec19Data p f K z S W) {u : G} (hu : u ∈ W) :
    u ∈ Subgroup.normalizer (K : Set G) := by
  rw [normalizer_eq_centralizer_of_tight hd.tight.toTightBranch]
  exact hd.hSz (hd.hWS hu)

theorem exists_conj_eq_mul (hd : Sec19DataT p f K z S W L t V) :
    ∃ r ∈ (S : Subgroup G) ⊓ K, r * t * r⁻¹ = t * z := by
  have hd0 := hd.toSec19Data
  have hI := isUniqueInvolution_of_tight hd.tight.toTightBranch
  have htW := mem_W hd
  have hdich : ∀ r ∈ (S : Subgroup G) ⊓ K, r * t * r⁻¹ * t⁻¹ = 1 ∨ r * t * r⁻¹ * t⁻¹ = z := by
    intro r hr
    have hrt : r * t * r⁻¹ ∈ W := (conjSub_eq_of_mem_inf hd0 hr) ▸ conj_mem_conjSub htW
    exact conj_mul_inv_eq_or hI hr.2 (mem_normalizer_of_mem_W hd0 htW) hd.invL.sq
      (comm_of_mem hd0 _ hrt t htW)
  by_cases hall : ∀ r ∈ (S : Subgroup G) ⊓ K, r * t * r⁻¹ * t⁻¹ = 1
  · exfalso
    refine not_le_centralizer_of_mem_rSet hd.tight (CoreAssembly.mem_conjClass_self K) hd.memL
      (member_ne hd).symm hd.invL (inf_mem_rSet hd0) inf_le_right ?_
    intro r hr
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hall r hr
    calc r * t = r * t * r⁻¹ * t⁻¹ * (t * r) := by group
      _ = t * r := by rw [h1, one_mul]
  push Not at hall
  obtain ⟨r, hr, hr1⟩ := hall
  refine ⟨r, hr, ?_⟩
  have h1 := (hdich r hr).resolve_left hr1
  have hzt : t * z = z * t :=
    Subgroup.mem_centralizer_singleton_iff.mp (hd.hSz (hd.hWS htW))
  calc r * t * r⁻¹ = r * t * r⁻¹ * t⁻¹ * t := by group
    _ = t * z := by rw [h1, hzt]

theorem conjSub_le_inf_sup (hd : Sec19DataT p f K z S W L t V) {r : G}
    (hr : r ∈ (S : Subgroup G) ⊓ K) : conjSub r V ≤ (K ⊓ W) ⊔ V := by
  have hd0 := hd.toSec19Data
  intro y hy
  have hv : r⁻¹ * y * r ∈ V := mem_conjSub_iff.mp hy
  obtain ⟨v, hvV, hvy⟩ : ∃ v ∈ V, r⁻¹ * y * r = v := ⟨_, hv, rfl⟩
  have hvW : v ∈ W := hd.leW hvV
  have hy' : y = (r * v * r⁻¹ * v⁻¹) * v := by rw [← hvy]; group
  have hc : r * v * r⁻¹ * v⁻¹ ∈ K ⊓ W := by
    refine ⟨?_, ?_⟩
    · have h1 : v * r⁻¹ * v⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (mem_normalizer_of_mem_W hd0 hvW) _).mp (K.inv_mem hr.2)
      have e : r * v * r⁻¹ * v⁻¹ = r * (v * r⁻¹ * v⁻¹) := by group
      rw [e]
      exact K.mul_mem hr.2 h1
    · have h1 : r * v * r⁻¹ ∈ W := (conjSub_eq_of_mem_inf hd0 hr) ▸ conj_mem_conjSub hvW
      exact W.mul_mem h1 (W.inv_mem hvW)
  rw [hy']
  exact Subgroup.mul_mem_sup hc hvV

theorem sup_eq_inf_sup (hd : Sec19DataT p f K z S W L t V) : W = (K ⊓ W) ⊔ V := by
  have hd0 := hd.toSec19Data
  have htb := hd.tight.toTightBranch
  have hΩ := hypOmegaMod_of_tightD hd.tight
  have hI := isUniqueInvolution_of_tight htb
  obtain ⟨η, S', hη, hinv, hWη, hηS⟩ := exists_eta hd0
  have hVη : V ∈ η := mem_eta_of_le hd0 hη hinv hWη hd.memV hd.leW
  refine le_antisymm ?_ (sup_le inf_le_right hd.leW)
  have hW' : W ≤ (K ⊓ W) ⊔ V := by
    conv_lhs => rw [hWη]
    refine iSup₂_le fun A hA => ?_
    have hAW : A ≤ W := hWη ▸ le_iSup₂ (f := fun (B : Subgroup G) (_ : B ∈ η) => B) A hA
    obtain ⟨J, hJ, hAJ⟩ := hΩ.exists_member_of_mem_USet hd.tight.branch.odd (hη.1 hA).1
    obtain ⟨u, hu⟩ := exists_isUniqueInvolution_member htb hJ
    rcases invol_eq_or hd hη hinv hWη hA hJ hAJ hu with rfl | rfl | rfl
    · have hJK : J = K :=
        eq_of_isUniqueInvolution_member htb hJ (CoreAssembly.mem_conjClass_self K) hu hI
      exact le_sup_of_le_left (le_inf (hJK ▸ hAJ) hAW)
    · have hJL : J = L := eq_of_isUniqueInvolution_member htb hJ hd.memL hu hd.invL
      by_cases hAV : A = V
      · exact hAV ▸ le_sup_right
      · exact absurd ⟨hJL ▸ hAJ, le_member hd⟩ (hη.2.1 A hA V hVη hAV L hd.memL)
    · obtain ⟨r, hr, hrt⟩ := exists_conj_eq_mul hd
      have hrV : conjSub r V ∈ η :=
        conjSub_mem_eta hd0 hη hinv hηS (inf_mem_rSet hd0) inf_le_left hr V hVη
      have hrL : IsUniqueInvolution (conjSub r L) (t * z) := hrt ▸ hd.invL.conj r
      have hJr : J = conjSub r L :=
        eq_of_isUniqueInvolution_member htb hJ (hΩ.conjInvariant r L hd.memL) hu hrL
      by_cases hAr : A = conjSub r V
      · rw [hAr]
        exact conjSub_le_inf_sup hd hr
      · exact absurd ⟨hAJ, hJr ▸ conjSub_mono (le_member hd)⟩ (hη.2.1 A hA _ hrV hAr J hJ)
  exact hW'

theorem inf_inf_eq_bot (hd : Sec19DataT p f K z S W L t V) : K ⊓ W ⊓ V = ⊥ := by
  have hodd := odd_card_inf_of_tight hd.tight.toTightBranch (CoreAssembly.mem_conjClass_self K)
    hd.memL (member_ne hd).symm
  rw [eq_bot_iff]
  intro x hx
  have hxKL : x ∈ K ⊓ L := ⟨hx.1.1, le_member hd hx.2⟩
  have hx2 : IsPGroup 2 (Subgroup.zpowers x) :=
    (S.isPGroup'.to_le hd.hWS).to_le (Subgroup.zpowers_le.mpr hx.1.2)
  exact Subgroup.mem_bot.mpr (eq_one_of_isPGroup_of_mem_odd hodd hxKL hx2)

theorem inf_member_eq_bot (hd : Sec19DataT p f K z S W L t V) : V ⊓ K = ⊥ := by
  rw [eq_bot_iff, ← inf_inf_eq_bot hd]
  intro x hx
  exact ⟨⟨hx.2, hd.leW hx.1⟩, hx.1⟩

theorem card_inf_eq_card (hd : Sec19DataT p f K z S W L t V) :
    Nat.card ↥(K ⊓ W) = Nat.card V := by
  have hd0 := hd.toSec19Data
  have hΩ := hypOmegaMod_of_tightD hd.tight
  have hp := hd.tight.branch.odd
  obtain ⟨R', -, J, hJ, hR'J, hVR', -, hcard, -⟩ := hΩ.exists_data_of_mem_USet hp hd.memV
  have h1 := hΩ.natCard_isSylow2In hJ hR'J
  have h2 := hΩ.natCard_isSylow2In (CoreAssembly.mem_conjClass_self K) (isSylow2In_inf hd0)
  have h3 := card_inf_eq hd0
  omega

theorem card_eq_mul (hd : Sec19DataT p f K z S W L t V) :
    Nat.card W = Nat.card ↥(K ⊓ W) * Nat.card V := by
  conv_lhs => rw [sup_eq_inf_sup hd]
  refine card_sup_of_comm (fun a ha b hb => comm_of_mem hd.toSec19Data a ha.2 b (hd.leW hb)) ?_
  exact inf_inf_eq_bot hd

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
