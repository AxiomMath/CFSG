module

public import CFSG.LocalAnalysis.AGLEmbedding.G28Small
public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorLayer

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

section CaseOne

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R : Subgroup G} {z : G}

theorem commutator_le_of_ne_component {M W W' : Subgroup G}
    {Lb Lb' : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hLb : IsComponentOf Lb ⊤)
    (hLb' : IsComponentOf Lb' ⊤) (hne : Lb ≠ Lb') (hW : W ≤ preM M Lb) (hW' : W' ≤ preM M Lb') :
    ⁅W, W'⁆ ≤ pCoreOf 2 M := by
  have hc := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hLb hLb' hne
  rw [Subgroup.commutator_le]
  intro w hw w' hw'
  obtain ⟨m, hm, rfl⟩ := hW hw
  obtain ⟨m', hm', rfl⟩ := hW' hw'
  have hcomm := Subgroup.mem_centralizer_iff.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc hm) _ hm'
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⁅m, m'⁆ = 1 := by
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, ← hcomm]
    group
  have := coe_mem_pCoreOf_two_of_mk_eq_one _ h1
  simpa [commutatorElement_def] using this

theorem D1PhaseThree.commutator_le_of_piece_and_conj {P : Sylow 3 G} {M H R : Subgroup G}
    (h3 : D1PhaseThree 3 P M H R) {L : Subgroup G} (hL : IsTwoPrimeComponent M L)
    {V : Subgroup G} (hVV : ⁅V, V⁆ = V) (hVK : V ≤ H ⊓ M) (hVN : ¬ V ≤ GLBPrimeCore 3 H)
    (hKVN : H ⊓ M ≤ Subgroup.normalizer ((V ⊔ GLBPrimeCore 3 H : Subgroup G) : Set G))
    (hdich : ∀ W : Subgroup G, W ≤ H ⊓ M → V ≤ Subgroup.normalizer (W : Set G) →
      V ≤ W ⊔ GLBPrimeCore 3 H ∨ ⁅W, V⁆ ≤ GLBPrimeCore 3 H)
    (hVE : V ≤ blockClosure M (H ⊓ M) L) {k : G} (hk : k ∈ H ⊓ M)
    (hne : barM M (L.map (MulAut.conj k).toMonoidHom) ≠ barM M L) :
    ⁅(H ⊓ M) ⊓ preM M (barM M L), V⁆ ≤ GLBPrimeCore 3 H ∧
      ⁅(H ⊓ M) ⊓ preM M (barM M (L.map (MulAut.conj k).toMonoidHom)), V⁆ ≤ GLBPrimeCore 3 H := by
  set N := GLBPrimeCore 3 H with hNdef
  set K := H ⊓ M with hKdef
  set Lb := barM M L with hLb
  set Lb' := barM M (L.map (MulAut.conj k).toMonoidHom) with hLb'
  have hLc : IsComponentOf Lb ⊤ := hL.component
  have hLk := hL.map_conj hk.2
  have hLc' : IsComponentOf Lb' ⊤ := hLk.component
  have hLay := barM_blockClosure_le_layer (inf_le_right : K ≤ M) hL
  have hVbar : ∀ v ∈ V, ∀ C : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf C ⊤ →
      v ∈ Subgroup.normalizer (preM M C : Set G) := by
    intro v hv C hC
    have hvM : v ∈ M := (hVK hv).2
    refine mem_normalizer_preM hvM (layer_le_normalizer_component hC (hLay ?_))
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (hVE hv))
  set W := K ⊓ preM M Lb with hW
  set W' := K ⊓ preM M Lb' with hW'
  have hKK : K ≤ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer
  have hVW : V ≤ Subgroup.normalizer (W : Set G) := fun v hv =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hKK (hVK hv), hVbar v hv Lb hLc⟩
  have hVW' : V ≤ Subgroup.normalizer (W' : Set G) := fun v hv =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hKK (hVK hv), hVbar v hv Lb' hLc'⟩
  have hWK : W ≤ K := inf_le_left
  have hW'K : W' ≤ K := inf_le_left
  have hWH : W ≤ H := hWK.trans inf_le_left
  have hW'H : W' ≤ H := hW'K.trans inf_le_left
  have hcWW' : ⁅W, W'⁆ ≤ N :=
    (commutator_le_of_ne_component hLc hLc' (Ne.symm hne) inf_le_right inf_le_right).trans
      ((h3.twoCore_M_le h3.twoCore_inf).trans (pCoreOf_le_glbPrimeCore Nat.prime_two
        (by norm_num) H))
  have hconj : ∀ x ∈ W, k * x * k⁻¹ ∈ W' := by
    rintro x ⟨hxK, hxL⟩
    refine ⟨K.mul_mem (K.mul_mem hk hxK) (K.inv_mem hk), ?_⟩
    have hxM : x ∈ M := hxK.2
    show k * x * k⁻¹ ∈ preM M Lb'
    rw [mem_preM (M.mul_mem (M.mul_mem hk.2 hxM) (M.inv_mem hk.2)), hLb', barM_map_conj hk.2]
    have hxL' : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hxM⟩ ∈ Lb := (mem_preM hxM).mp hxL
    refine ⟨_, hxL', ?_⟩
    change QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨k, hk.2⟩ * _ *
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨k, hk.2⟩)⁻¹ = _
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hconj' : ∀ x ∈ W', k⁻¹ * x * k ∈ W := by
    rintro x ⟨hxK, hxL⟩
    refine ⟨K.mul_mem (K.mul_mem (K.inv_mem hk) hxK) hk, ?_⟩
    have hxM : x ∈ M := hxK.2
    show k⁻¹ * x * k ∈ preM M Lb
    rw [mem_preM (M.mul_mem (M.mul_mem (M.inv_mem hk.2) hxM) hk.2)]
    have hxL' : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hxM⟩ ∈ Lb' := (mem_preM hxM).mp hxL
    rw [hLb', barM_map_conj hk.2] at hxL'
    obtain ⟨w, hw, hwx⟩ := hxL'
    have e : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨k⁻¹ * x * k, M.mul_mem (M.mul_mem
        (M.inv_mem hk.2) hxM) hk.2⟩ = (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨k, hk.2⟩)⁻¹ *
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hxM⟩ * QuotientGroup.mk' (CFSG.pCore 2 ↥M)
          ⟨k, hk.2⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e, ← hwx]
    simpa [MulAut.conj_apply, mul_assoc] using hw
  have hNnorm : ∀ g ∈ H, ∀ n ∈ N, g * n * g⁻¹ ∈ N := fun g hg n hn =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_glbPrimeCore 3 H hg) n).mp hn
  have hWNn : W ≤ Subgroup.normalizer (N : Set G) := hWH.trans (le_normalizer_glbPrimeCore 3 H)
  have hW'Nn : W' ≤ Subgroup.normalizer (N : Set G) :=
    hW'H.trans (le_normalizer_glbPrimeCore 3 H)
  have hVN' : V ⊔ N ≤ W ⊔ N → V ⊔ N ≤ W' ⊔ N := by
    intro hle x hx
    have hkx : k⁻¹ * x * k ∈ V ⊔ N := by
      have := (Subgroup.mem_normalizer_iff.mp (hKVN (K.inv_mem hk)) x).mp hx
      simpa using this
    have hkx' := hle hkx
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right W N hWNn] at hkx'
    obtain ⟨w, hw, n, hn, he⟩ := hkx'
    have hx' : x = (k * w * k⁻¹) * (k * n * k⁻¹) := by
      have : x = k * (k⁻¹ * x * k) * k⁻¹ := by group
      rw [this, ← he]
      group
    rw [hx']
    exact Subgroup.mul_mem_sup (hconj w hw) (hNnorm k hk.1 n hn)
  have hVN'' : V ⊔ N ≤ W' ⊔ N → V ⊔ N ≤ W ⊔ N := by
    intro hle x hx
    have hkx : k * x * k⁻¹ ∈ V ⊔ N := (Subgroup.mem_normalizer_iff.mp (hKVN hk) x).mp hx
    have hkx' := hle hkx
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right W' N hW'Nn] at hkx'
    obtain ⟨w, hw, n, hn, he⟩ := hkx'
    have hx' : x = (k⁻¹ * w * k) * (k⁻¹ * n * k) := by
      have : x = k⁻¹ * (k * x * k⁻¹) * k := by group
      rw [this, ← he]
      group
    rw [hx']
    have hn' : k⁻¹ * n * k ∈ N := by
      have := hNnorm k⁻¹ (H.inv_mem hk.1) n hn
      simpa using this
    exact Subgroup.mul_mem_sup (hconj' w hw) hn'
  have hnot : ¬ (V ⊔ N ≤ W ⊔ N ∧ V ⊔ N ≤ W' ⊔ N) := by
    rintro ⟨h1, h2⟩
    apply hVN
    have hcomm := commutator_sup_glbPrimeCore_le (p := 3) hWH hW'H hcWW'
    rw [← hVV]
    exact (Subgroup.commutator_mono (le_sup_left.trans h1) (le_sup_left.trans h2)).trans hcomm
  refine ⟨?_, ?_⟩
  · rcases hdich W hWK hVW with h1 | h1
    · exact absurd ⟨sup_le h1 le_sup_right, hVN' (sup_le h1 le_sup_right)⟩ hnot
    · exact h1
  · rcases hdich W' hW'K hVW' with h1 | h1
    · exact absurd ⟨hVN'' (sup_le h1 le_sup_right), sup_le h1 le_sup_right⟩ hnot
    · exact h1

theorem D1G28Data.barM_conj_eq_of_piece (h : D1G28Data P M H R z) (hB3 : StmtBlockThree)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) {V : Subgroup G}
    (hVPi : V ≤ (H ⊓ M) ⊓ blockClosure M (H ⊓ M) L)
    (hV : SU38Piece (H ⊓ M) (GLBPrimeCore 3 H) z V) {k : G} (hk : k ∈ H ⊓ M) :
    barM M (L.map (MulAut.conj k).toMonoidHom) = barM M L := by
  have h3 := h.ph3
  obtain ⟨hVV, hVK, hVN, hKVN, -, hdich, hcent⟩ := hV
  obtain ⟨hTM, hTH, hQT, hT3⟩ := h.small_T
  obtain ⟨hNPi, y, hyL, hy3, hyl, hyPi⟩ := h.mem_Pi hB3 hL
  set N := GLBPrimeCore 3 H with hNdef
  set K := H ⊓ M with hKdef
  by_contra hne
  obtain ⟨hWV, hW'V⟩ := h3.commutator_le_of_piece_and_conj hL.toIsTwoPrimeComponent hVV hVK hVN
    hKVN hdich (fun v hv => (hVPi hv).2) hk hne
  set Lb := barM M L with hLb
  set Lb' := barM M (L.map (MulAut.conj k).toMonoidHom) with hLb'
  set W := K ⊓ preM M Lb with hW
  set W' := K ⊓ preM M Lb' with hW'
  have hconj : ∀ x ∈ W, k * x * k⁻¹ ∈ W' := by
    rintro x ⟨hxK, hxL⟩
    refine ⟨K.mul_mem (K.mul_mem hk hxK) (K.inv_mem hk), ?_⟩
    have hxM : x ∈ M := hxK.2
    show k * x * k⁻¹ ∈ preM M Lb'
    rw [mem_preM (M.mul_mem (M.mul_mem hk.2 hxM) (M.inv_mem hk.2)), hLb', barM_map_conj hk.2]
    have hxL' : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hxM⟩ ∈ Lb := (mem_preM hxM).mp hxL
    refine ⟨_, hxL', ?_⟩
    change QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨k, hk.2⟩ * _ *
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨k, hk.2⟩)⁻¹ = _
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hyK : y ∈ K := hyPi.1
  have hyW : y ∈ W := ⟨hyK, le_preM hL.le le_rfl hyL⟩
  have hkyW' : k * y * k⁻¹ ∈ W' := hconj y hyW
  have hyT : y ∈ Subgroup.zpowers z ⊔ N := hcent y hyK fun v hv => by
    have := Subgroup.commutator_mem_commutator hyW hv
    simpa [commutatorElement_def] using hWV this
  have hkyT : k * y * k⁻¹ ∈ Subgroup.zpowers z ⊔ N := hcent _ hkyW'.1 fun v hv => by
    have := Subgroup.commutator_mem_commutator hkyW' hv
    simpa [commutatorElement_def] using hW'V this
  exact hne (barM_conj_eq_of_small hL.toIsTwoPrimeComponent hyL hy3 hyl hk.2 hTM hQT hyT hkyT
    hT3)

end CaseOne

end CFSG.AGLEmbedding
