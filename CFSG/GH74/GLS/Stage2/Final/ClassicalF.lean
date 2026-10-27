module

public import CFSG.GH74.GLS.Stage2.Final.ClassicalN
public import CFSG.GH74.GLS.Stage1.Main.Bridge
public import CFSG.GH74.GLS.Stage2.Final.LayerFDerive

public section

namespace CFSG.GH74.GLS.Stage2.Final

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Main
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec7

theorem isCentralInvolution_of_isConj {G : Type} [Group G] {z x : G} (hz : IsCentralInvolution z)
    (h : IsConj z x) : IsCentralInvolution x := by
  obtain ⟨hord, S₀, hzS, hzc⟩ := hz
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  refine ⟨?_, c • S₀, ?_, ?_⟩
  · have h1 := MulEquiv.orderOf_eq (MulAut.conj c) z
    rw [MulAut.conj_apply] at h1
    rw [← hc, h1]
    exact hord
  · rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact ⟨z, hzS, by rw [← hc]; rfl⟩
  · intro s hs
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hs
    obtain ⟨s', hs', rfl⟩ := hs
    have := hzc s' hs'
    rw [← hc]
    show (c * s' * c⁻¹) * (c * z * c⁻¹) = (c * z * c⁻¹) * (c * s' * c⁻¹)
    calc (c * s' * c⁻¹) * (c * z * c⁻¹) = c * (s' * z) * c⁻¹ := by group
      _ = c * (z * s') * c⁻¹ := by rw [this]
      _ = (c * z * c⁻¹) * (c * s' * c⁻¹) := by group


theorem stageFiveClassical_of_l4F (hMC : ModelCenter) (hEC : ECInter) (hMD : ModelsDisjoint)
    (hMO : ModelOddCore) (hMOne : ModelOneClass) (hMLB : ModelLayerBar) {G : Type} [Group G] [Finite G]
    {z : G} {S : Subgroup G} {ε : Bool} {q : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)}
    (hctx : Stage2Ctx G z (Kind.l4 ε) S) (hout : Stage2Out G z (Kind.l4 ε) S)
    (hq : Stage1L4 G z S ε q L₁ L₂) (ht : L4U4TermTypeQ ε G z S q)
    (hmax : ∀ p f : ℕ, p.Prime → p ^ f = q → Max6A G p f) : StageFiveClassical G := by
  obtain ⟨hE, Gs, iGs, fGs, p, f, hp, hp2, hpf, htag, ⟨S₁, hSS₁⟩, hC⟩ := ht
  have hgt3 : 3 < q := hq.pair.gt3
  have hqodd : Odd q := hq.pair.odd
  have h5 : 5 ≤ p ^ f := by
    obtain ⟨m, hm⟩ := hqodd
    omega
  have h3 : 3 < p ^ f := by omega
  have hmod8 := hq.mod8
  have hq4 : q % 4 = (if ε then 1 else 3) := by
    rcases hq.fusion with ⟨h4, -⟩ | ⟨-, x, hx, -⟩
    · exact h4
    · exfalso
      have hxz : IsConj z x := hE.1 x hx.x_inv
      exact hx.x_nonCentral (isCentralInvolution_of_isConj hctx.central hxz)
  have hone : ∀ u v : G, u ∈ S → v ∈ S → orderOf u = 2 → orderOf v = 2 → IsConj u v := by
    intro u v _ _ hu hv
    exact (hE.1 u hu).symm.trans (hE.1 v hv)
  have hGs : IsClassicalModel Gs p f ∧ (LieModel Gs .PSL 4 p f ∨ LieModel Gs .PSU 4 p f) ∧
      ((p ^ f % 8 ≠ 1 ∧ LieModel Gs .PSL 4 p f) ∨ (p ^ f % 8 ≠ 7 ∧ LieModel Gs .PSU 4 p f)) ∧
      ((p ^ f % 8 = 5 ∧ LieModel Gs .PSL 4 p f) ∨ (p ^ f % 8 = 3 ∧ LieModel Gs .PSU 4 p f)) ∧
      ((ε = true ∧ p ^ f % 8 ≠ 1 ∧ LieModel Gs .PSL 4 p f) ∨
        (ε = false ∧ p ^ f % 8 ≠ 7 ∧ LieModel Gs .PSU 4 p f)) := by
    rcases htag with ⟨hε, hL⟩ | ⟨hε, hL⟩
    · subst hε
      have h8 : p ^ f % 8 ≠ 1 := by simpa [hpf] using hmod8
      have h4 : p ^ f % 4 = 1 := by simpa [hpf] using hq4
      have h5' : p ^ f % 8 = 5 := by omega
      exact ⟨⟨hp, hp2, h3, Or.inr (Or.inl ⟨h8, hL⟩)⟩, Or.inl hL, Or.inl ⟨h8, hL⟩, Or.inl ⟨h5', hL⟩,
        Or.inl ⟨rfl, h8, hL⟩⟩
    · subst hε
      have h8 : p ^ f % 8 ≠ 7 := by simpa [hpf] using hmod8
      have h4 : p ^ f % 4 = 3 := by simpa [hpf] using hq4
      have h3' : p ^ f % 8 = 3 := by omega
      exact ⟨⟨hp, hp2, h3, Or.inr (Or.inr ⟨h8, hL⟩)⟩, Or.inr hL, Or.inr ⟨h8, hL⟩, Or.inr ⟨h3', hL⟩,
        Or.inr ⟨rfl, h8, hL⟩⟩
  obtain ⟨hGsm, hLU0, hLU, hcls, hεtag⟩ := hGs
  have hone' : ∀ u v : Gs, orderOf u = 2 → orderOf v = 2 → IsConj u v :=
    hMOne Gs p f hp hp2 hcls
  obtain ⟨z₁, hz₁o, hcen₁⟩ := hMC Gs p f hGsm S₁
  have hz₁S : z₁ ∈ (S₁ : Subgroup Gs) := by
    have : z₁ ∈ (center ↥(S₁ : Subgroup Gs)).map (S₁ : Subgroup Gs).subtype := by
      rw [hcen₁]; exact Subgroup.mem_zpowers z₁
    obtain ⟨c, -, hc⟩ := this
    rw [← hc]; exact c.2
  have hz₁c : ∀ s ∈ (S₁ : Subgroup Gs), s * z₁ = z₁ * s := by
    intro s hs
    have hmem : z₁ ∈ (center ↥(S₁ : Subgroup Gs)).map (S₁ : Subgroup Gs).subtype := by
      rw [hcen₁]; exact Subgroup.mem_zpowers z₁
    obtain ⟨c, hc, hcz⟩ := hmem
    have := Subgroup.mem_center_iff.1 hc ⟨s, hs⟩
    have h2 := congrArg Subtype.val this
    rw [← hcz]
    exact h2
  have hz₁cent : IsCentralInvolution z₁ := ⟨hz₁o, S₁, hz₁S, hz₁c⟩
  have hS₁C : (S₁ : Subgroup Gs) ≤ Cen z₁ := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hz₁c s hs)
  have hS₁G : CFSG.ABGLocalTools.IsSylowOf 2 (S₁ : Subgroup Gs) ⊤ := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_top, S₁.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact S₁.not_dvd_index
  have hS₁C' : CFSG.ABGLocalTools.IsSylowOf 2 (S₁ : Subgroup Gs) (Cen z₁) := hS₁G.of_le hS₁C le_top
  obtain ⟨S'c, hS'c⟩ := hS₁C'
  obtain ⟨φ₀⟩ := hC z₁ S'c hz₁cent S₁ hSS₁ hS'c.symm
  have hSylX : CFSG.ABGLocalTools.IsSylowOf 2 (barOf z S) (Stage1.Thm3.Sec8.layerSBar z S) :=
    (isSylowOf_barOf hctx.sylow).of_le (by rw [layerSBar_eq_sup]; exact le_sup_right) le_top
  have hSylY : CFSG.ABGLocalTools.IsSylowOf 2 (barOf z₁ (S₁ : Subgroup Gs))
      (Stage1.Thm3.Sec8.layerSBar z₁ (S₁ : Subgroup Gs)) :=
    (isSylowOf_barOf ⟨S'c, hS'c⟩).of_le (by rw [layerSBar_eq_sup]; exact le_sup_right) le_top
  obtain ⟨PX, hPX⟩ := hSylX.exists_sylow_eq_subgroupOf
  obtain ⟨PY, hPY⟩ := hSylY.exists_sylow_eq_subgroupOf
  obtain ⟨φ, hφ'⟩ := exists_equiv_sylow φ₀ PX PY
  have hφ : ∀ y : ↥(Stage1.Thm3.Sec8.layerSBar z S),
      (y : CentralizerBar z) ∈ barOf z S ↔
        (φ y : CentralizerBar z₁) ∈ barOf z₁ (S₁ : Subgroup Gs) := by
    intro y
    have h1 := hφ' y
    rw [hPX, hPY] at h1
    exact h1
  have hcen2 : Cen2 G z S := ⟨hctx.std.toStd0, hctx.central, hctx.sylow⟩
  obtain ⟨hcyc, hdvd⟩ := hout.oddCoreL4 ε q L₁ L₂ rfl hq
  have hEC' := hEC G z (Kind.l4 ε) S hctx (Or.inr ⟨ε, rfl⟩)
  have hN : layerTimesSylow z S ⊓ OddCore z = ⊥ :=
    LayerLift.layerTimesSylow_inf_oddCore_eq_bot hctx.sylow.isPGroup hctx.S_le_Cen hEC'
  have hlift := LayerLift.barOf_layer_eq_of_cyclic z hcyc
  obtain ⟨hN', hB'⟩ := hMLB Gs p f S₁ z₁ hGsm hLU0 hz₁o hcen₁
  have hB : barOf z (layerTimesSylow z S) = Stage1.Thm3.Sec8.layerSBar z S := by
    rw [layerSBar_eq_sup, LayerFD.barOf_layerTimesSylow hctx.S_le_Cen, hlift]
  have hB'' : barOf z₁ (layerTimesSylow z₁ (S₁ : Subgroup Gs)) =
      Stage1.Thm3.Sec8.layerSBar z₁ (S₁ : Subgroup Gs) := by
    rw [layerSBar_eq_sup, layer_sup_barOf_eq_of_barOf_eq S₁.isPGroup' hS₁C hB', hB']
  obtain ⟨ψ, hψS, hψf⟩ := compatIso_of_bar hctx.S_le_Cen hS₁C hN hB hN' hB'' φ hφ hone
    (fun u v _ _ hu hv => hone' u v hu hv)
  have hcenS := center_eq_zpowers_of_equiv (le_sup_right : S ≤ layerTimesSylow z S)
    (le_sup_right : (S₁ : Subgroup Gs) ≤ layerTimesSylow z₁ (S₁ : Subgroup Gs)) ψ hψS hctx.z_mem
    (fun s hs => hctx.S_comm_z hs) hctx.orderOf_z hz₁o hcen₁
  have hodd2 : Nat.Coprime 2 (Nat.card ↥(pPrimeCore 2 ↥(Cen z))) :=
    CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥(Cen z))
  have hdiv : Nat.card ↥(pPrimeCore 2 ↥(Cen z)) ∣
      Nat.card ↥(pPrimeCore 2 ↥(centralizer ({z₁} : Set Gs))) := by
    have hOo := hMO Gs p f S₁ z₁ hGsm hz₁o hcen₁
    rcases hεtag with ⟨hε, h8, hL⟩ | ⟨hε, h8, hL⟩
    · rw [(hOo.1 h8 hL)]
      rw [hε] at hdvd
      simp only [ite_true] at hdvd
      rw [← hpf] at hdvd
      exact dvd_ordCompl_of_odd hodd2 hdvd
    · rw [(hOo.2 h8 hL)]
      rw [hε] at hdvd
      simp only [Bool.false_eq_true, ite_false] at hdvd
      rw [← hpf] at hdvd
      exact dvd_ordCompl_of_odd hodd2 hdvd
  have hmx := hmax p f hp hpf
  refine ⟨Gs, iGs, Or.inr ⟨p, f, hp, hp2, h5, hLU, hmx⟩, ?_⟩
  refine ⟨⟨p, f, hp, hp2, h3, ?_⟩, ?_⟩
  · rcases hLU0 with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  obtain ⟨S₀, hS₀⟩ := sylow_of_sylowTop hctx.sylow_top
  subst hS₀
  refine ⟨S₀, z, S₁, z₁, hcenS, hcen₁, ⟨ψ, hψS, hψf⟩, ?_, fun _ => ⟨hcyc, hdiv⟩⟩
  rintro ⟨p', f', hp', hp2', hLp⟩
  exfalso
  rcases hLU0 with h | h
  · exact (hMD Gs p' f' p f hp' hp2' hp hp2 hLp).1 h
  · exact (hMD Gs p' f' p f hp' hp2' hp hp2 hLp).2 h

end CFSG.GH74.GLS.Stage2.Final
