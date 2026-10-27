module

public import CFSG.ClassicalInvolution.AschTight.T6ASD
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenSDMuC
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenSDType2
public import CFSG.ClassicalInvolution.Q3.TL3S8Four
public import CFSG.ClassicalInvolution.Q3.TL3S8Mu
public import CFSG.ClassicalInvolution.Q3.TL3S8Setup
public import CFSG.ClassicalInvolution.Q3.TL3S8Zstar

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.Q3T6
open scoped commutatorElement

variable {G : Type} [Group G]

structure TightFStarOK (G : Type) [Group G] (t : G) : Prop where
  oddCore : classicalInvolutionOddCore G = ⊥
  noncentral : t ∉ Subgroup.center G
  contains : ∀ N : Subgroup G, N.Normal → t ∈ N → genFittingFStar G ≤ N

theorem TightFStarOK.of_simple [Finite G] [IsSimpleGroup (genFittingFStar G)]
    (hnab : ∃ a b : genFittingFStar G, a * b ≠ b * a) {t : G} (ht : t ≠ 1) :
    TightFStarOK G t where
  oddCore := classicalInvolutionOddCore_eq_bot_of_fstar hnab
  noncentral := not_mem_center_of_fstar hnab ht
  contains := fun _ hN htN => genFittingFStar_le_of_normal hnab hN htN ht

theorem genFittingFStar_le_of_normal_of_quasisimple [Finite G] {t : G}
    (hq : CFSG.Open.IsQuasisimple ↥(genFittingFStar G)) (hord : orderOf t = 2)
    (ht : ¬ ∃ P : Subgroup G, P.Normal ∧ IsPGroup 2 P ∧ t ∈ P) {N : Subgroup G} (hN : N.Normal)
    (htN : t ∈ N) : genFittingFStar G ≤ N := by
  classical
  set F : Subgroup G := genFittingFStar G with hFdef
  have hFn : F.Normal := genFittingFStar_normal G
  set Z : Subgroup ↥F := Subgroup.center ↥F with hZdef
  have hMn : ((N ⊓ F).subgroupOf F).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact ⟨hN.conj_mem _ hn.1 g, hFn.conj_mem _ hn.2 g⟩
  set M : Subgroup ↥F := (N ⊓ F).subgroupOf F with hMdef
  have hMq : (M.map (QuotientGroup.mk' Z)).Normal :=
    hMn.map (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z)
  have hsimp : IsSimpleGroup (↥F ⧸ Z) := hq.2
  rcases hsimp.eq_bot_or_eq_top_of_normal (M.map (QuotientGroup.mk' Z)) with h0 | h0
  ·
    exfalso
    have hMZ : ∀ x ∈ N, x ∈ F → ∀ f ∈ F, x * f = f * x := by
      intro x hxN hxF f hf
      have hxM : (⟨x, hxF⟩ : ↥F) ∈ M := Subgroup.mem_subgroupOf.mpr ⟨hxN, hxF⟩
      have h1 : QuotientGroup.mk' Z ⟨x, hxF⟩ ∈ M.map (QuotientGroup.mk' Z) :=
        Subgroup.mem_map_of_mem _ hxM
      rw [h0, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      have := Subgroup.mem_center_iff.mp h1 ⟨f, hf⟩
      exact congrArg Subtype.val this.symm
    set ZF : Subgroup G := Z.map F.subtype with hZF
    have hZFc : ⁅ZF, F⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      rintro _ ⟨z, hz, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨f, hf⟩)
    have hNF : ⁅N, F⁆ ≤ ZF := by
      rw [Subgroup.commutator_le]
      intro n hn f hf
      have h1 : ⁅n, f⁆ ∈ N := by
        have := hN.conj_mem n⁻¹ (N.inv_mem hn) f
        have e : ⁅n, f⁆ = n * (f * n⁻¹ * f⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact N.mul_mem hn this
      have h2 : ⁅n, f⁆ ∈ F := by
        have e : ⁅n, f⁆ = (n * f * n⁻¹) * f⁻¹ := by simp only [commutatorElement_def]
        rw [e]
        exact F.mul_mem (hFn.conj_mem f hf n) (F.inv_mem hf)
      have hMg : (⟨⁅n, f⁆, h2⟩ : ↥F) ∈ M := Subgroup.mem_subgroupOf.mpr ⟨h1, h2⟩
      have h3 : QuotientGroup.mk' Z ⟨⁅n, f⁆, h2⟩ ∈ M.map (QuotientGroup.mk' Z) :=
        Subgroup.mem_map_of_mem _ hMg
      rw [h0, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
      exact ⟨⟨⁅n, f⁆, h2⟩, h3, rfl⟩
    have hcomm1 : ⁅⁅N, F⁆, F⁆ = ⊥ :=
      le_bot_iff.mp (hZFc ▸ Subgroup.commutator_mono_left hNF)
    have hcomm2 : ⁅⁅F, N⁆, F⁆ = ⊥ := by rw [Subgroup.commutator_comm F N]; exact hcomm1
    have hmapTop : (⊤ : Subgroup ↥F).map F.subtype = F := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hFF : ⁅F, F⁆ = F := by
      calc ⁅F, F⁆ = ⁅(⊤ : Subgroup ↥F).map F.subtype, (⊤ : Subgroup ↥F).map F.subtype⁆ := by
            rw [hmapTop]
        _ = (⁅(⊤ : Subgroup ↥F), (⊤ : Subgroup ↥F)⁆ : Subgroup ↥F).map F.subtype :=
            (Subgroup.map_commutator _ _ _).symm
        _ = (commutator ↥F).map F.subtype := by rw [_root_.commutator_def]
        _ = F := by rw [hq.1, hmapTop]
    have h3 : ⁅⁅F, F⁆, N⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate hcomm2 hcomm1
    rw [hFF] at h3
    have hNc : N ≤ Subgroup.centralizer (F : Set G) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
      exact h3
    have hNF' : ∀ x ∈ N, x ∈ F := fun x hx =>
      CFSG.Adapters.generalized_fitting_self_centralizing G (hNc hx)
    have hNcomm : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x := fun x hx y hy =>
      (Subgroup.mem_centralizer_iff.mp (hNc hx)) y (hNF' y hy) |>.symm
    let P : Subgroup G :=
      { carrier := {x | x ∈ N ∧ x * x = 1}
        mul_mem' := fun {a b} ha hb => ⟨N.mul_mem ha.1 hb.1, by
          have hab : a * b = b * a := hNcomm a ha.1 b hb.1
          calc a * b * (a * b) = a * (b * a) * b := by group
            _ = a * (a * b) * b := by rw [← hab]
            _ = (a * a) * (b * b) := by group
            _ = 1 := by rw [ha.2, hb.2, one_mul]⟩
        one_mem' := ⟨N.one_mem, by simp⟩
        inv_mem' := fun {a} ha => ⟨N.inv_mem ha.1, by
          have : a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
          rw [this, ha.2, inv_one]⟩ }
    have htt : t * t = 1 := by rw [← sq, ← hord, pow_orderOf_eq_one]
    refine ht ⟨P, ⟨fun x hx g => ⟨hN.conj_mem x hx.1 g, ?_⟩⟩, ?_, ⟨htN, htt⟩⟩
    · calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
        _ = 1 := by rw [hx.2]; group
    · intro x
      refine ⟨1, ?_⟩
      apply Subtype.ext
      simpa [pow_two] using x.2.2
  ·
    have hMZ : M ⊔ Z = ⊤ := by
      rw [eq_top_iff]
      intro f _
      have hf : QuotientGroup.mk' Z f ∈ M.map (QuotientGroup.mk' Z) := by rw [h0]; trivial
      obtain ⟨m, hm, hmf⟩ := Subgroup.mem_map.mp hf
      have hz : m⁻¹ * f ∈ Z := QuotientGroup.eq.mp hmf
      have e : f = m * (m⁻¹ * f) := by group
      rw [e]
      exact Subgroup.mul_mem_sup hm hz
    have hcomm : commutator ↥F ≤ M := by
      rw [_root_.commutator_def]
      calc ⁅(⊤ : Subgroup ↥F), ⊤⁆ = ⁅M ⊔ Z, ⊤⁆ := by rw [hMZ]
        _ = ⁅M, ⊤⁆ ⊔ ⁅Z, ⊤⁆ := Subgroup.commutator_sup_right M Z ⊤
        _ = ⁅M, ⊤⁆ := by rw [hZdef, Subgroup.commutator_center_left, sup_bot_eq]
        _ ≤ M := Subgroup.commutator_le_left M ⊤
    have hMtop : M = ⊤ := by
      rw [eq_top_iff, ← hq.1]
      exact hcomm
    intro f hf
    have : (⟨f, hf⟩ : ↥F) ∈ M := by rw [hMtop]; trivial
    exact (Subgroup.mem_subgroupOf.mp this).1

theorem TightFStarOK.of_quasisimple [Finite G] {t : G} (hord : orderOf t = 2)
    (hq : CFSG.Open.IsQuasisimple ↥(genFittingFStar G)) (hO : classicalInvolutionOddCore G = ⊥)
    (ht : ¬ ∃ P : Subgroup G, P.Normal ∧ IsPGroup 2 P ∧ t ∈ P) : TightFStarOK G t where
  oddCore := hO
  noncentral := fun hc => ht ⟨Subgroup.zpowers t, ⟨fun x hx g => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      have hgt : Commute g t := Subgroup.mem_center_iff.mp hc g
      have e : g * t ^ k * g⁻¹ = t ^ k := by
        rw [(hgt.zpow_right k).eq, mul_assoc, mul_inv_cancel, mul_one]
      rw [e]
      exact Subgroup.zpow_mem_zpowers t k⟩,
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; norm_num),
    Subgroup.mem_zpowers t⟩
  contains := fun _ hN htN => genFittingFStar_le_of_normal_of_quasisimple hq hord ht hN htN

namespace TightSylowStd

variable [Finite G] {R : Subgroup G} {S : Sylow 2 R} {t : G} {T : Sylow 2 G}

theorem exists_conj_mem_sylow_ne' (hF : TightFStarOK G t) (h : TightSylowStd R S t T) :
    ∃ g : G, g * t * g⁻¹ ∈ (T : Subgroup G) ∧ g * t * g⁻¹ ≠ t := by
  have hord : orderOf t = 2 := h.datum.order
  have hzS : t ∈ (T : Subgroup G) := h.mem_T
  have hzZ : (⟨t, hzS⟩ : (T : Subgroup G)) ∈ Subgroup.center (T : Subgroup G) := by
    rw [Subgroup.mem_center_iff]
    intro s
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp (h.hTt s.2)
  exact CFSG.ClassicalInvolution.exists_conj_mem_sylow_ne hF.oddCore T ⟨t, hzS⟩ hzZ
    (by rw [Subgroup.orderOf_mk]; exact hord) hF.noncentral

theorem twoSubgroupsFourGenerated_of_allTypeTwo' (hF : TightFStarOK G t)
    (hB3 : GoldschmidtB3Tmp)
    (h : TightSylowStd R S t T) (hA : AllTypeTwo (tightCore R) t) :
    TwoSubgroupsFourGenerated (genFittingFStar G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht := h.setup194
  have hI := h.isUniqueInvolution
  have hS2 : IsSylow2Of ((S : Subgroup R).map R.subtype) (tightCore R) := h.sylow_core
  obtain ⟨Q₀, hQ₀⟩ := hS2.exists_sylow
  set R0 : Subgroup G := (Q₀ : Subgroup (tightCore R)).map (tightCore R).subtype with hR0
  have hR : R0 ∈ RSet (CoreAssembly.conjClass (tightCore R)) :=
    ⟨tightCore R, CoreAssembly.mem_conjClass_self _, Q₀, rfl⟩
  have hRK : R0 ≤ tightCore R := Subgroup.map_subtype_le _
  have hzR : IsUniqueInvolution R0 t := ht.isUniqueInvolution_of_mem_rSet_of_le hR hRK
  have hRT : R0 ≤ (T : Subgroup G) := by
    rw [hQ₀]
    exact h.hST
  have hSN : (T : Subgroup G) ≤ Subgroup.normalizer (R0 : Set G) := by
    intro s hs
    have hle : conjSubgroup s R0 ≤ (T : Subgroup G) := by
      intro x hx
      have hx' := mem_conjSubgroup_iff.mp hx
      have e : x = s * (s⁻¹ * x * s) * s⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hs (hRT hx')) (Subgroup.inv_mem _ hs)
    exact conjSubgroup_eq_self_iff.mp (ht.sylow_eq Q₀ T.isPGroup' hRT hle)
  have hSz : (T : Subgroup G) ≤ Subgroup.centralizer ({t} : Set G) := h.hTt
  have hSKR : (T : Subgroup G) ⊓ tightCore R ≤ R0 := by
    have h2 : IsPGroup 2 (((T : Subgroup G) ⊓ tightCore R).subgroupOf (tightCore R)) :=
      (T.isPGroup'.to_le inf_le_left).comap_subtype
    have hle : (Q₀ : Subgroup (tightCore R)) ≤
        ((T : Subgroup G) ⊓ tightCore R).subgroupOf (tightCore R) := by
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr ⟨hRT ⟨x, hx, rfl⟩, x.2⟩
    have heq := Q₀.3 h2 hle
    intro x hx
    have hxK : x ∈ tightCore R := hx.2
    have : (⟨x, hxK⟩ : tightCore R) ∈ ((T : Subgroup G) ⊓ tightCore R).subgroupOf (tightCore R) :=
      Subgroup.mem_subgroupOf.mpr hx
    rw [heq] at this
    exact ⟨⟨x, hxK⟩, this, rfl⟩
  obtain ⟨g, htS, htz⟩ := h.exists_conj_mem_sylow_ne' hF
  set t' := g * t * g⁻¹ with ht'def
  set P := R0 ⊔ Subgroup.zpowers t' with hPdef
  have hPS : P ≤ (T : Subgroup G) := sup_le hRT (Subgroup.zpowers_le.mpr htS)
  have htzc : t' * t = t * t' := Subgroup.mem_centralizer_singleton_iff.mp (hSz htS)
  have hsd := SD.isSemidihedral_sup_of_allTypeTwo ht hA hR hRK (hSN htS) htzc htz
  obtain ⟨a, b, M, hsdd⟩ := exists_sdData (T.isPGroup'.to_le hPS) hsd
  have hcl : fusionStronglyClosed (P : Set G) T := by
    intro x hx y hy
    have := SD.mem_sup_of_conj_mem ht hA hR hRK hRT hSKR hSN hSz htS htz hx (y := y⁻¹)
      (by rwa [inv_inv])
    rwa [inv_inv] at this
  have hNC : ∀ n ∈ Subgroup.normalizer (P : Set G), ∃ k : ℕ,
      n ^ (2 ^ k) ∈ Subgroup.centralizer (P : Set G) := by
    intro n hn
    obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos n).ne'
    refine ⟨k, hsdd.mem_centralizer_of_odd (Subgroup.pow_mem _ hn _) ?_⟩
    rw [orderOf_pow' n (pow_ne_zero _ two_ne_zero), hkm,
      Nat.gcd_mul_right_left, Nat.mul_div_cancel_left _ (by positivity)]
    exact hm
  have hB := hB3 G T P hPS hcl hNC
  set N : Subgroup G := Subgroup.normalClosure (P : Set G) with hNdef
  have hNn : N.Normal := Subgroup.normalClosure_normal
  have htN : t ∈ N := Subgroup.le_normalClosure (Subgroup.mem_sup_left hzR.mem)
  have hFN : genFittingFStar G ≤ N := hF.contains N hNn htN
  have hTN : (T : Subgroup G) ⊓ N = P :=
    hB.2.2 _ inf_le_right (T.isPGroup'.to_le inf_le_left)
      (le_inf hPS (Subgroup.le_normalClosure))
  have hAP : ∀ X : Subgroup G, IsPGroup 2 X → X ≤ genFittingFStar G →
      ∃ g' : G, X ≤ conjSub g' P := by
    intro X hX2 hXF
    obtain ⟨T', hXT'⟩ := hX2.exists_le_sylow
    obtain ⟨g', hg'⟩ := MulAction.exists_smul_eq G T T'
    have hT' : (T' : Subgroup G) = conjSub g' (T : Subgroup G) := by
      rw [← hg', Sylow.coe_subgroup_smul]
      rfl
    refine ⟨g', fun x hx => ?_⟩
    have hxT : x ∈ conjSub g' (T : Subgroup G) := hT' ▸ hXT' hx
    rw [mem_conjSub_iff] at hxT ⊢
    have hxN : g'⁻¹ * x * g' ∈ N := by
      have := hNn.conj_mem x (hFN (hXF hx)) g'⁻¹
      simpa using this
    rw [← hTN]
    exact ⟨hxT, hxN⟩
  refine twoSubgroupsFourGenerated_of_conj_le (fun Q hQP => ?_) hAP
  obtain ⟨c, d, hcd⟩ := T6A.exists_closure_pair_eq hQP fun x hx y hy hxa hya =>
    T6A.sdData_inv_mul_mem_zpowers hsdd hx hy hxa hya
  refine ⟨{c, d}, (Finset.card_insert_le _ _).trans (by simp), ?_⟩
  rw [Finset.coe_insert, Finset.coe_singleton, hcd]


theorem not_muIsoZ2' (hF : TightFStarOK G t) (hB3 : GoldschmidtB3Tmp)
    (h : TightSylowStd R S t T) {W : Subgroup G}
    (hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R))) :
    ¬ MuIsoZ2 (CoreAssembly.conjClass (tightCore R)) W := by
  intro hZ
  have hst := SD.omegaStarNbr_eq_empty_of_muIsoZ2 muS3OfShape3 h.partIHypG hW h.edgeless hZ
  have hA := SD.allTypeTwo_of_omegaStarNbr_eq_empty h.hypOmegaGen h.edgeless hst
    h.isUniqueInvolution
  exact h.notFour (h.twoSubgroupsFourGenerated_of_allTypeTwo' hF hB3 hA)

theorem muIsoS3' (hF : TightFStarOK G t) (hB3 : GoldschmidtB3Tmp)
    (h : TightSylowStd R S t T) {W : Subgroup G}
    (hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R))) :
    MuIsoS3 (CoreAssembly.conjClass (tightCore R)) W :=
  (h.muZ2OrS3 hW).resolve_left (h.not_muIsoZ2' hF hB3 hW)

end TightSylowStd

end CFSG.ClassicalInvolution.Q3
