module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsSeitz6b
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.LinearAutCubeProof
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Star2313UnitaryProof
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Gen2318LocalExc

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz7

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
open CFSG.HardMathSupport.Dickson.I271 (autImage actPre actHom actHom_mk coe_normalizerMonoidHom mem_actPre
  pRank_actPre eq_top_of_sup_center_eq_top mem_autImage actPre_le_left)
open CFSG.HardMathSupport.Solomon.LocalBalance (InducesInnerIn autOrderIn)
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54Ns (gammaPrimeIn)
open CFSG.HardMathSupport.Solomon.Coordinator (i271_exists_card_eq i271_pRank_eq i271_isElemAbelian_of_le
  exists_pow_autOrderIn)
open CFSG.LieType.Seitz (fixedPoints mem_fixedPoints)
open CFSG.AGLEmbeddingD2 (IsD2SeitzException)
open GL83.CompFam

set_option linter.unusedSectionVars false

section Conj

variable {X : Type} [Group X] [Finite X]

theorem three_mul_le_of_not_mem {p : ℕ} (hp : p.Prime) {K : Subgroup X} (hK : IsComponentOf K ⊤)
    {E : Subgroup X} (hEK : E ≤ K) (hE : IsElemAbelian p E)
    (hEZ : ∀ x ∈ E, (∀ y ∈ K, x * y = y * x) → x = 1) {ρ : ℕ} (hEc : Nat.card E = p ^ ρ)
    {b : X} (hb : b ∉ Subgroup.normalizer (K : Set X))
    (hbb : b * b ∉ Subgroup.normalizer (K : Set X)) :
    3 * ρ ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set K₁ := cj b K with hK₁def
  set K₂ := cj (b * b) K with hK₂def
  have hK₁ : IsComponentOf K₁ ⊤ := isComponentOf_cj hK b
  have hK₂ : IsComponentOf K₂ ⊤ := isComponentOf_cj hK (b * b)
  have h01 : K ≠ K₁ := fun h => hb (cj_eq_iff_mem_normalizer.1 h.symm)
  have h02 : K ≠ K₂ := fun h => hbb (cj_eq_iff_mem_normalizer.1 h.symm)
  have h12 : K₁ ≠ K₂ := by
    intro h
    apply h01
    have h' := congrArg (cj b⁻¹) h
    rw [hK₁def, hK₂def, cj_inv_cj, cj_mul, cj_inv_cj] at h'
    exact h'
  have hc01 := InputsSeitz6.comm_of_ne_comp hK hK₁ h01
  have hc02 := InputsSeitz6.comm_of_ne_comp hK hK₂ h02
  have hc12 := InputsSeitz6.comm_of_ne_comp hK₁ hK₂ h12
  set E₁ := cj b E with hE₁def
  set E₂ := cj (b * b) E with hE₂def
  have hE₁K : E₁ ≤ K₁ := cj_mono b hEK
  have hE₂K : E₂ ≤ K₂ := cj_mono (b * b) hEK
  have hE₁ : IsElemAbelian p E₁ := CFSG.SectionRank.isElemAbelian_map hE _
  have hE₂ : IsElemAbelian p E₂ := CFSG.SectionRank.isElemAbelian_map hE _
  have hE₁c : Nat.card E₁ = p ^ ρ := by
    show Nat.card (E.map (MulAut.conj b).toMonoidHom) = _
    rw [Subgroup.card_map_of_injective (MulAut.conj b).injective, hEc]
  have hE₂c : Nat.card E₂ = p ^ ρ := by
    show Nat.card (E.map (MulAut.conj (b * b)).toMonoidHom) = _
    rw [Subgroup.card_map_of_injective (MulAut.conj (b * b)).injective, hEc]
  have hc : ∀ x ∈ E, ∀ y ∈ E₁, x * y = y * x := fun x hx y hy => hc01 x (hEK hx) y (hE₁K hy)
  have hd01 : E ⊓ E₁ = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    rw [Subgroup.mem_bot]
    exact hEZ x hx.1 fun y hy => (hc01 y hy x (hE₁K hx.2)).symm
  have hE01 : IsElemAbelian p (E ⊔ E₁) := CFSG.Open.IsElemAbelian.sup_of_commute hE hE₁ hc
  have hE01c : Nat.card (E ⊔ E₁ : Subgroup X) = p ^ (ρ + ρ) := by
    rw [card_sup_of_commute_of_inf_eq_bot hc hd01, hEc, hE₁c, pow_add]
  have hE01C : E ⊔ E₁ ≤ Subgroup.centralizer (K₂ : Set X) := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · exact Subgroup.mem_centralizer_iff.2 fun y hy => (hc02 x (hEK hx) y hy).symm
    · exact Subgroup.mem_centralizer_iff.2 fun y hy => (hc12 x (hE₁K hx) y hy).symm
  have hc' : ∀ x ∈ E ⊔ E₁, ∀ y ∈ E₂, x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.1 (hE01C hx) y (hE₂K hy)).symm
  have hd : (E ⊔ E₁) ⊓ E₂ = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    rw [Subgroup.mem_bot]
    obtain ⟨hx01, hx2⟩ := hx
    set g := b * b with hg
    have hy : g⁻¹ * x * g ∈ E := mem_cj.1 hx2
    have hyc : ∀ k ∈ K, (g⁻¹ * x * g) * k = k * (g⁻¹ * x * g) := by
      intro k hk
      have hk2 : g * k * g⁻¹ ∈ K₂ := mul_mem_cj hk
      have h1 : g * k * g⁻¹ * x = x * (g * k * g⁻¹) :=
        Subgroup.mem_centralizer_iff.1 (hE01C hx01) _ hk2
      calc (g⁻¹ * x * g) * k = g⁻¹ * (x * (g * k * g⁻¹)) * g := by group
        _ = g⁻¹ * (g * k * g⁻¹ * x) * g := by rw [h1]
        _ = k * (g⁻¹ * x * g) := by group
    have h1 : g⁻¹ * x * g = 1 := hEZ _ hy hyc
    calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have := InputsSeitz.add_le_pRank_of_commute hp hE01 hE₂ hc' hd hE01c hE₂c
  omega

end Conj

section Lift


variable {X : Type} [Group X] [Finite X]

theorem le_gammaPrime_of_fixed2_rank {k : ℕ} {B K : Subgroup X} (hperf : commutator ↥K = ⊤)
    (hodd : Odd (Nat.card (Subgroup.center ↥K)))
    (Fam : Set (Subgroup (MulAut (↥K ⧸ Subgroup.center ↥K))))
    (hFam : ∀ P ∈ Fam, k ≤ CFSG.Open.pRank 3 (actPre B K P))
    (hgen : Subgroup.closure {s : ↥K ⧸ Subgroup.center ↥K |
      (∃ P ∈ Fam, ∀ e ∈ P, e s = s) ∧ ∃ j : ℕ, s ^ (2 ^ j) = 1} = ⊤) :
    K ≤ gammaPrimeIn 3 k B K := by
  set Γ : Subgroup X := gammaPrimeIn 3 k B K with hΓ
  set Γ₀ : Subgroup ↥K := Γ.subgroupOf K with hΓ₀
  set S : Set (↥K ⧸ Subgroup.center ↥K) :=
    {s | (∃ P ∈ Fam, ∀ e ∈ P, e s = s) ∧ ∃ j : ℕ, s ^ (2 ^ j) = 1} with hS
  have hlift : ∀ s ∈ S, ∃ k' ∈ Γ₀, (QuotientGroup.mk k' : ↥K ⧸ Subgroup.center ↥K) = s := by
    rintro s ⟨⟨P, hP, hs⟩, hs2⟩
    obtain ⟨k', rfl, j', hk⟩ := Gen2318Lift.exists_twoElem_lift (Subgroup.center ↥K) s hs2
    refine ⟨k', ?_, rfl⟩
    show (k' : X) ∈ Γ
    have hcent : (k' : X) ∈ Subgroup.centralizer (actPre B K P : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      obtain ⟨hqN, hqB, hqP⟩ := mem_actPre.1 hq
      set k'' : ↥K := K.normalizerMonoidHom ⟨q, hqN⟩ k' with hk''
      have h1 : (QuotientGroup.mk k'' : ↥K ⧸ Subgroup.center ↥K) = QuotientGroup.mk k' := by
        have := hs _ hqP
        rwa [actHom_mk] at this
      have h2 : ∃ j : ℕ, k'' ^ (2 ^ j) = 1 := ⟨j', by rw [hk'', ← map_pow, hk, map_one]⟩
      have h3 : k'' = k' := Gen2318Lift.twoElem_unique hodd h2 ⟨j', hk⟩ h1
      have h4 : (k'' : X) = q * (k' : X) * q⁻¹ := coe_normalizerMonoidHom K ⟨q, hqN⟩ k'
      have h5 : q * (k' : X) * q⁻¹ = (k' : X) := by rw [← h4, h3]
      calc q * (k' : X) = q * (k' : X) * q⁻¹ * q := by group
        _ = (k' : X) * q := by rw [h5]
    have hle : K ⊓ Subgroup.centralizer (actPre B K P : Set X) ≤ Γ :=
      le_iSup₂_of_le (f := fun (E : Subgroup X) (_ : E ≤ B ∧ k ≤ CFSG.Open.pRank 3 E) =>
        K ⊓ Subgroup.centralizer (E : Set X)) (actPre B K P) ⟨actPre_le_left, hFam P hP⟩ le_rfl
    exact hle ⟨k'.2, hcent⟩
  have hle : Subgroup.closure S ≤ Γ₀.map (QuotientGroup.mk' (Subgroup.center ↥K)) := by
    rw [Subgroup.closure_le]
    intro s hs
    obtain ⟨k', hk', rfl⟩ := hlift s hs
    exact ⟨k', hk', rfl⟩
  have hsup : Γ₀ ⊔ Subgroup.center ↥K = ⊤ := by
    rw [eq_top_iff]
    intro g _
    have hg : (QuotientGroup.mk g : ↥K ⧸ Subgroup.center ↥K) ∈ Subgroup.closure S := by
      rw [hgen]; exact Subgroup.mem_top _
    obtain ⟨γ, hγ, hγg⟩ := hle hg
    have hz : γ⁻¹ * g ∈ Subgroup.center ↥K := QuotientGroup.eq.1 hγg
    have : g = γ * (γ⁻¹ * g) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hγ hz
  have htop : Γ₀ = ⊤ := eq_top_of_sup_center_eq_top hperf hsup
  intro x hx
  have : (⟨x, hx⟩ : ↥K) ∈ Γ₀ := by rw [htop]; exact Subgroup.mem_top _
  exact this

theorem le_gammaPrime_of_seitz_rank (hSeitz : Seitz2313Even) {k : ℕ} {B K : Subgroup X}
    (hperf : commutator ↥K = ⊤) (hBel : IsElemAbelian 3 B)
    (hodd : Odd (Nat.card (Subgroup.center ↥K))) {d : TauCeti.ValidLieTypeIndex}
    (hs : Seitz2313Cover.EvenScope d.1)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* (TauCeti.CFSGIndex.lie d).Group)
    {E₀ : Subgroup (MulAut (↥K ⧸ Subgroup.center ↥K))} (hE₀ : E₀ ≤ autImage B K)
    (hEel : IsElemAbelian 3 E₀) {m : ℕ} (hm : Nat.card E₀ = 3 ^ m) (hm1 : 1 ≤ m)
    (hc : k ≤ CFSG.Open.pRank 3 (B ⊓ Subgroup.centralizer (K : Set X)) + (m - 1))
    (hU : ∃ U : Subgroup (↥K ⧸ Subgroup.center ↥K), U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧
      ∀ φ ∈ E₀, ∀ u ∈ U, φ u ∈ U) :
    K ≤ gammaPrimeIn 3 k B K := by
  have hE0 : E₀ ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hm
    have := Nat.one_lt_pow (by omega : m ≠ 0) (by norm_num : 1 < 3)
    omega
  have hgenS := hSeitz 3 Nat.prime_three (by norm_num) _ d ⟨e⟩ hs E₀ hEel hE0 hU
  refine le_gammaPrime_of_fixed2_rank hperf hodd {F | F ≤ E₀ ∧ F.relIndex E₀ = 3} ?_ ?_
  · rintro F ⟨hFE, hFi⟩
    have h1 := Subgroup.relIndex_mul_card F E₀
    rw [inf_of_le_left hFE, hFi, hm] at h1
    have hFcard : Nat.card F = 3 ^ (m - 1) := by
      have h3 : 3 * Nat.card F = 3 * 3 ^ (m - 1) := by
        rw [h1, ← pow_succ']
        congr 1
        omega
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) h3
    rw [pRank_actPre Nat.prime_three hBel hperf (hFE.trans hE₀) hFcard]
    exact hc
  · exact Gen2318Lift.closure_fixed2_eq_top_of_seitz _ (fun F hF => hF) hgenS

theorem gammaPrimeIn_le_glbCore {k : ℕ} (hk : 2 ≤ k) (B K : Subgroup X) :
    gammaPrimeIn 3 k B K ≤ GLBCore 3 2 B :=
  iSup₂_le fun _ hE => inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans
    (normalizer_le_glbCore hE.1 (hk.trans hE.2)))

theorem star2313Even_holds : Star2313Even :=
  star2313Even_of_inputs LinearAutCubeProof.linearAutCube_holds
    Star2313UnitaryProof.star2313UnitaryInput_holds

theorem gen2318_holds (hGA : CFSG.Open.GriessAllModelsStatement) : Gen2318 :=
  gen2318_of_inputs hGA star2313Even_holds gen2318TwoLocal_holds gen2318OutThreePrime_holds
    (gen2318RankFour_of_sylow' gen2318RankFourSylowUniq_holds) gen2318E64Core_holds
    (gen2318E68Outer_of_inputs hGA e68FieldFix_holds gen2318TwoLocal_holds
      (gen2318RankFour_of_sylow' gen2318RankFourSylowUniq_holds))

theorem twoLocalRank_le_pRank_top : GLATwoLocalRank 3 X ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  show sSup {k | ∃ H : Subgroup X, CFSG.Open.IsTwoLocal H ∧ CFSG.Open.pRank 3 H = k} ≤ _
  refine csSup_le' ?_
  rintro k ⟨H, -, rfl⟩
  exact CFSG.SectionRank.pRank_mono (by norm_num) le_top

theorem card_stab_eq {B K : Subgroup X} (hperf : commutator ↥K = ⊤) :
    Nat.card ↥(B ⊓ Subgroup.normalizer (K : Set X)) =
      Nat.card (autImage B K) * Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set X)) := by
  rw [card_autImage hperf]
  unfold autOrderIn
  have h := Subgroup.relIndex_mul_card (Subgroup.centralizer (K : Set X))
    (B ⊓ Subgroup.normalizer (K : Set X))
  have hci : Subgroup.centralizer (K : Set X) ⊓ (B ⊓ Subgroup.normalizer (K : Set X)) =
      B ⊓ Subgroup.centralizer (K : Set X) := by
    apply le_antisymm
    · exact fun x hx => ⟨hx.2.1, hx.1⟩
    · exact fun x hx => ⟨hx.2, hx.1, Subgroup.centralizer_le_normalizer _ hx.2⟩
  rw [hci] at h
  exact h.symm

theorem exists_toral {K : Subgroup X} (hq : CFSG.Open.IsQuasisimple ↥K) (d : TauCeti.ValidLieTypeIndex)
    (hd : Gen2318Index d.1) (e : (↥K ⧸ Subgroup.center ↥K) ≃* (TauCeti.CFSGIndex.lie d).Group) :
    ∃ (E : Subgroup X) (ρ : ℕ), E ≤ K ∧ IsElemAbelian 3 E ∧
      (∀ x ∈ E, (∀ y ∈ K, x * y = y * x) → x = 1) ∧ Nat.card E = 3 ^ ρ ∧ rho2318 d.1 ≤ ρ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨EK, -, hEKel, hdisj, hρ, -, -, -⟩ := gen2318TwoLocal_holds ↥K hq d hd ⟨e⟩
  refine ⟨EK.map K.subtype, CFSG.Open.pRank 3 EK, Subgroup.map_subtype_le EK,
    CFSG.SectionRank.isElemAbelian_map hEKel K.subtype, ?_, ?_, hρ⟩
  · rintro _ ⟨y, hy, rfl⟩ hyc
    have hyz : y ∈ Subgroup.center ↥K :=
      Subgroup.mem_center_iff.2 fun g => Subtype.ext (hyc g g.2).symm
    have h1 : y ∈ EK ⊓ Subgroup.center ↥K := ⟨hy, hyz⟩
    rw [hdisj, Subgroup.mem_bot] at h1
    rw [h1, map_one]
  · rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact GL83.PiGen.card_eq_pow_pRank hEKel

theorem le_glbCore_of_star {B K : Subgroup X} (hB : IsElemAbelian 3 B) (hK : IsComponentOf K ⊤)
    (hodd : Odd (Nat.card (Subgroup.center ↥K))) {d : TauCeti.ValidLieTypeIndex}
    (hd : Gen2318Index d.1) (e : (↥K ⧸ Subgroup.center ↥K) ≃* (TauCeti.CFSGIndex.lie d).Group) {r : ℕ}
    (hr : Nat.card (autImage B K) = 3 ^ r) (hr3 : 3 ≤ r)
    (h5 : 5 ≤ CFSG.Open.pRank 3 (B ⊓ Subgroup.centralizer (K : Set X)) + r) :
    K ≤ GLBCore 3 2 B := by
  have hperf : commutator ↥K = ⊤ := hK.2.2.1
  have hAel : IsElemAbelian 3 (autImage B K) := isElemAbelian_autImage hB
  obtain ⟨E₀, hE₀A, hrel, U, hU0, hU2, hUinv⟩ := star2313Even_holds _ d hd ⟨e⟩ (autImage B K) hAel
  have hE₀el : IsElemAbelian 3 E₀ := i271_isElemAbelian_of_le hAel hE₀A
  obtain ⟨m₀, hm₀⟩ := i271_exists_card_eq Nat.prime_three hE₀el
  have h1 := Subgroup.relIndex_mul_card E₀ (autImage B K)
  rw [inf_of_le_left hE₀A, hm₀, hr] at h1
  have h3 : 3 ^ r ≤ 3 ^ (m₀ + 2) := by
    calc 3 ^ r = E₀.relIndex (autImage B K) * 3 ^ m₀ := h1.symm
      _ ≤ 9 * 3 ^ m₀ := Nat.mul_le_mul_right _ hrel
      _ = 3 ^ (m₀ + 2) := by ring
  have h4 : r ≤ m₀ + 2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 h3
  exact (le_gammaPrime_of_seitz_rank seitz2313Even_holds (k := 2) hperf hB hodd
    (gen2318Index_evenScope hd) e hE₀A hE₀el hm₀ (by omega) (by omega) ⟨U, hU0, hU2, hUinv⟩).trans
    (gammaPrimeIn_le_glbCore le_rfl B K)

theorem five_le_of_e68_outer (hGA : CFSG.Open.GriessAllModelsStatement) {B K : Subgroup X}
    (hBel : IsElemAbelian 3 B) (hKc : IsComponentOf K ⊤) (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hrk : GLATwoLocalRank 3 X ≤ CFSG.Open.pRank 3 B) (d : TauCeti.ValidLieTypeIndex)
    (hd : IsE6EightIndex d.1) (e : (↥K ⧸ Subgroup.center ↥K) ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hout : ¬ InducesInnerIn B K) {r : ℕ} (hr : autOrderIn B K = 3 ^ r) : 5 ≤ r := by
  classical
  have hq : CFSG.Open.IsQuasisimple ↥K := hKc.2.2
  have hZ : Subgroup.center ↥K = ⊥ := Gen2318E68Aux.center_eq_bot_of_E68 hGA hq ⟨d, hd, ⟨e⟩⟩
  have hπinj : ∀ a c : ↥K, (QuotientGroup.mk a : ↥K ⧸ Subgroup.center ↥K) = QuotientGroup.mk c →
      a = c := by
    intro a c h
    have h' := QuotientGroup.eq.1 h
    rw [hZ, Subgroup.mem_bot] at h'
    exact inv_mul_eq_one.1 h'
  have hπsurj : Function.Surjective (QuotientGroup.mk : ↥K → ↥K ⧸ Subgroup.center ↥K) :=
    QuotientGroup.mk_surjective
  obtain ⟨eKS, hεK⟩ : ∃ eKS : ↥K ≃* (↥K ⧸ Subgroup.center ↥K),
      ∀ k : ↥K, eKS k = QuotientGroup.mk k :=
    ⟨MulEquiv.ofBijective (QuotientGroup.mk' (Subgroup.center ↥K))
      ⟨fun a c h => hπinj a c h, hπsurj⟩, fun k => rfl⟩
  have hbex : ∃ b ∈ B ⊓ Subgroup.normalizer (K : Set X),
      ∀ k ∈ K, k⁻¹ * b ∉ Subgroup.centralizer (K : Set X) := by
    unfold InducesInnerIn at hout
    push Not at hout
    exact hout
  obtain ⟨b, hbBN, hbnot⟩ := hbex
  have hbB : b ∈ B := (Subgroup.mem_inf.1 hbBN).1
  have hbN : b ∈ Subgroup.normalizer (K : Set X) := (Subgroup.mem_inf.1 hbBN).2
  have hb3 : b ^ 3 = 1 := hBel.2 b hbB
  have hβ3 : (actHom K ⟨b, hbN⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have h1 : (⟨b, hbN⟩ : ↥(Subgroup.normalizer (K : Set X))) ^ 3 = 1 :=
      Subtype.ext (by simpa using hb3)
    rw [h1, map_one]
  have hβrange : actHom K ⟨b, hbN⟩ ∉ (MulAut.conj : (↥K ⧸ Subgroup.center ↥K) →*
      MulAut (↥K ⧸ Subgroup.center ↥K)).range := by
    rintro ⟨s, hs⟩
    obtain ⟨k, rfl⟩ := hπsurj s
    apply hbnot (k : X) k.2
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have key : (k : X) * x * (k : X)⁻¹ = b * x * b⁻¹ := by
      have h1 : MulAut.conj (QuotientGroup.mk k : ↥K ⧸ Subgroup.center ↥K)
          (QuotientGroup.mk (⟨x, hx⟩ : ↥K)) =
          actHom K ⟨b, hbN⟩ (QuotientGroup.mk (⟨x, hx⟩ : ↥K)) := by
        rw [hs]
      rw [actHom_mk] at h1
      have h2 : (QuotientGroup.mk (k * ⟨x, hx⟩ * k⁻¹ : ↥K) : ↥K ⧸ Subgroup.center ↥K) =
          QuotientGroup.mk (K.normalizerMonoidHom ⟨b, hbN⟩ ⟨x, hx⟩) := h1
      have h3 := congrArg Subtype.val (hπinj _ _ h2)
      rw [coe_normalizerMonoidHom] at h3
      exact h3
    calc x * ((k : X)⁻¹ * b) = (k : X)⁻¹ * ((k : X) * x * (k : X)⁻¹) * b := by group
      _ = (k : X)⁻¹ * (b * x * b⁻¹) * b := by rw [key]
      _ = ((k : X)⁻¹ * b) * x := by group
  obtain ⟨H, hHfix, hHcen, hHq, d₂, hd₂, ⟨eH⟩⟩ :=
    e68FieldFix_holds (↥K ⧸ Subgroup.center ↥K) d hd ⟨e⟩ (actHom K ⟨b, hbN⟩) hβ3 hβrange
  have hHquot : Nonempty ((↥H ⧸ Subgroup.center ↥H) ≃* (TauCeti.CFSGIndex.lie d₂).Group) :=
    ⟨(QuotientGroup.quotientMulEquivOfEq hHcen).trans (QuotientGroup.quotientBot.trans eH)⟩
  obtain ⟨E, P, hEel, -, hρ, hPne, hP2, hEN⟩ :=
    gen2318TwoLocal_holds ↥H hHq d₂ (Gen2318E68Aux.gen2318Index_of_E62 hd₂) hHquot
  have hcart : ∃ E P : Subgroup ↥H, IsElemAbelian 3 E ∧ 4 ≤ CFSG.Open.pRank 3 E ∧ P ≠ ⊥ ∧
      IsPGroup 2 ↥P ∧ E ≤ Subgroup.normalizer (P : Set ↥H) := by
    refine ⟨E, P, hEel, ?_, hPne, hP2, hEN⟩
    rw [Gen2318E68Aux.rho2318_E62 hd₂] at hρ
    exact hρ
  exact Gen2318E68Aux.rank_bound_of_fixed hεK hZ hBel hBN hbB hbN hb3 hbnot hrk hHfix hcart hr

theorem le_glbCore_of_rankFour (hGA : CFSG.Open.GriessAllModelsStatement) {B K : Subgroup X}
    (hB : IsElemAbelian 3 B) (hK : IsComponentOf K ⊤) (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hC : B ⊓ Subgroup.centralizer (K : Set X) = ⊥) (hm4 : CFSG.Open.pRank 3 B = 4)
    (hrk : CFSG.Open.pRank 3 B = CFSG.Open.pRank 3 (⊤ : Subgroup X))
    (d : TauCeti.ValidLieTypeIndex) (e : (↥K ⧸ Subgroup.center ↥K) ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hd : Gen2318Index d.1) : K ≤ GLBCore 3 2 B := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq : CFSG.Open.IsQuasisimple ↥K := hK.2.2
  have hperf : commutator ↥K = ⊤ := hq.1
  have hodd : Odd (Nat.card (Subgroup.center ↥K)) :=
    Gen2318Lift.odd_center_gen2318 hGA hq ⟨d, hd, ⟨e⟩⟩
  obtain ⟨r, hr⟩ := exists_pow_autOrderIn Nat.prime_three hB hBN
  have hm := pRank_eq_add_autOrderIn Nat.prime_three hB hBN hr
  have hc0 : CFSG.Open.pRank 3 (B ⊓ Subgroup.centralizer (K : Set X)) = 0 := by
    rw [hC]
    exact pRank_bot_eq_zero' Nat.prime_three
  rw [hc0, zero_add, hm4] at hm
  have hAel : IsElemAbelian 3 (autImage B K) := isElemAbelian_autImage hB
  have hAcard : Nat.card (autImage B K) = 3 ^ 4 := by rw [card_autImage hperf, hr, ← hm]
  obtain ⟨E, ρ, -, hEel, -, hEc, hρ⟩ := exists_toral hq d hd e
  have hρm : ρ ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
    CFSG.SectionRank.le_pRank (by norm_num) le_top hEel hEc
  have h4 := four_le_rho2318 hd
  have hrk4 : IsRankFourIndex d.1 := by
    rcases gen2318_trichotomy hd with h6 | h | h64
    · omega
    · exact h
    · have := rho2318_E6Four h64
      omega
  have hinner : autImage B K ≤ (MulAut.conj : (↥K ⧸ Subgroup.center ↥K) →*
      MulAut (↥K ⧸ Subgroup.center ↥K)).range := by
    rcases isRankFour_split hrk4 with hout3 | he68
    · exact gen2318OutThreePrime_holds _ d hout3 ⟨e⟩ _ hAel
    · refine autImage_le_range_conj ?_
      by_contra hninn
      have hrk2 : GLATwoLocalRank 3 X ≤ CFSG.Open.pRank 3 B := hrk ▸ twoLocalRank_le_pRank_top
      have := five_le_of_e68_outer hGA hB hK hBN hrk2 d he68 e hninn hr
      omega
  obtain ⟨U, hU0, hU2, hUinv⟩ :=
    gen2318RankFour_of_sylow' gen2318RankFourSylowUniq_holds _ d hrk4 ⟨e⟩ _ hAel hAcard hinner
  exact (le_gammaPrime_of_seitz_rank seitz2313Even_holds (k := 2) hperf hB hodd
    (gen2318Index_evenScope hd) e le_rfl hAel hAcard (by norm_num) (by rw [hc0]; norm_num)
    ⟨U, hU0, hU2, hUinv⟩).trans (gammaPrimeIn_le_glbCore le_rfl B K)

theorem le_glbCore_of_gen2318 (hGA : CFSG.Open.GriessAllModelsStatement) (hKX : CFSG.Open.IsKGroup X)
    {B : Subgroup X} (hB : IsElemAbelian 3 B) (hB4 : 4 ≤ CFSG.Open.pRank 3 B)
    (hrk : CFSG.Open.pRank 3 B = CFSG.Open.pRank 3 (⊤ : Subgroup X)) {K : Subgroup X}
    (hK : IsComponentOf K ⊤)
    (hsmall : 3 ^ (CFSG.Open.pRank 3 B - 2) * Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set X)) <
      Nat.card ↥(B ⊓ Subgroup.normalizer (K : Set X)))
    (d : TauCeti.ValidLieTypeIndex) (e : (↥K ⧸ Subgroup.center ↥K) ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hd : Gen2318Index d.1) : K ≤ GLBCore 3 2 B := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq : CFSG.Open.IsQuasisimple ↥K := hK.2.2
  have hperf : commutator ↥K = ⊤ := hq.1
  have hodd : Odd (Nat.card (Subgroup.center ↥K)) :=
    Gen2318Lift.odd_center_gen2318 hGA hq ⟨d, hd, ⟨e⟩⟩
  have hAel : IsElemAbelian 3 (autImage B K) := isElemAbelian_autImage hB
  obtain ⟨r, hr⟩ := i271_exists_card_eq Nat.prime_three hAel
  have hCel : IsElemAbelian 3 (B ⊓ Subgroup.centralizer (K : Set X)) :=
    i271_isElemAbelian_of_le hB inf_le_left
  have hCc : Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set X)) =
      3 ^ CFSG.Open.pRank 3 (B ⊓ Subgroup.centralizer (K : Set X)) :=
    GL83.PiGen.card_eq_pow_pRank hCel
  have hBc : Nat.card B = 3 ^ CFSG.Open.pRank 3 B := GL83.PiGen.card_eq_pow_pRank hB
  have hstab := card_stab_eq (B := B) hperf
  rw [hr, hCc] at hstab
  have hrm : CFSG.Open.pRank 3 B - 1 ≤ r := by
    rw [hCc, hstab] at hsmall
    have h1 : 3 ^ (CFSG.Open.pRank 3 B - 2) < 3 ^ r := lt_of_mul_lt_mul_right hsmall (Nat.zero_le _)
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).1 h1
    omega
  by_cases h5 : 5 ≤ CFSG.Open.pRank 3 (B ⊓ Subgroup.centralizer (K : Set X)) + r
  · exact le_glbCore_of_star hB hK hodd hd e hr (by omega) h5
  push Not at h5
  have hBN : B ≤ Subgroup.normalizer (K : Set X) := by
    intro b hbB
    by_contra hbN
    have hb3 : b ^ 3 = 1 := hB.2 b hbB
    have hbb : b * b ∉ Subgroup.normalizer (K : Set X) := by
      intro h
      apply hbN
      have h2 : b * b * (b * b) = b := by
        have h4 : b * b * (b * b) = b ^ 3 * b := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        rw [h4, hb3, one_mul]
      rw [← h2]
      exact Subgroup.mul_mem _ h h
    obtain ⟨E, ρ, hEK, hEel, hEZ, hEc, hρ⟩ := exists_toral hq d hd e
    have h3 := three_mul_le_of_not_mem Nat.prime_three hK hEK hEel hEZ hEc hbN hbb
    have h4 := four_le_rho2318 hd
    omega
  have hstabB : B ⊓ Subgroup.normalizer (K : Set X) = B := inf_eq_left.2 hBN
  have hmcr : CFSG.Open.pRank 3 B = r + CFSG.Open.pRank 3 (B ⊓ Subgroup.centralizer (K : Set X)) := by
    rw [hstabB, hBc, ← pow_add] at hstab
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) hstab
  by_cases hC : B ⊓ Subgroup.centralizer (K : Set X) = ⊥
  · have hc0 : CFSG.Open.pRank 3 (B ⊓ Subgroup.centralizer (K : Set X)) = 0 := by
      rw [hC]
      exact pRank_bot_eq_zero' Nat.prime_three
    exact le_glbCore_of_rankFour hGA hB hK hBN hC (by omega) hrk d e hd
  · have hrk2 : GLATwoLocalRank 3 X ≤ CFSG.Open.pRank 3 B := hrk ▸ twoLocalRank_le_pRank_top
    exact ((gen2318_holds hGA) X hKX K B hK hB hBN hrk2 hC ⟨d, hd, ⟨e⟩⟩).2.trans
      (gammaPrimeIn_le_glbCore (by norm_num) B K)

end Lift

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz7

end
