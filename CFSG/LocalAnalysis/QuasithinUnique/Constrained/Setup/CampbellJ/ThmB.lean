module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.ThmB52
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.JLocalAimg
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.ThmB51

public section

namespace CFSG.QuasithinUnique.Setup.CampbellJ

open CFSG.QuasithinUnique.Setup.Campbell

open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G] {k : Type*} [Field k] [Finite k] {S : Sylow 2 G}
  {ρ : G →* Matrix.SpecialLinearGroup (Fin 2) k} {ψ : Ecore G →* Multiplicative (Fin 2 → k)}
  {Fp Zp : Subgroup G}

namespace PartnerCoreJ

private theorem exists_core_max_not_commute_partnerJ (h : IsSeed S ρ (Ecore G) ψ)
    (hp : PartnerCoreJ (S : Subgroup G) Fp Zp) (hFQ : Fp ≤ CFSG.pCore 2 G)
    (hF : ¬ Fp ≤ Fcore G) :
    ∃ A₀ : Subgroup G, CFSG.Quasithin.IsMaxElemAbelian (CFSG.pCore 2 G) A₀ ∧
      ⁅A₀, Fp⁆ ≠ ⊥ := by
  by_contra hall
  push Not at hall
  apply hF
  intro f hf
  have hfJ : f ∈ CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G) :=
    fp_le_thompsonJ_core h hp hFQ hf
  refine CFSG.Quasithin.BlueprintB2.mem_centerTorsion_iff.mpr
    ⟨hfJ, fun k hk => ?_, (isElemAbelian_iff.mp hp.isElemAbelian_fp).2 f hf⟩
  have hcent : CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G) ≤
      Subgroup.centralizer (({f} : Set G)) := by
    refine thompsonJ_le_of_forall fun A₀ hA₀ a ha => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact (mul_comm_of_commutator_eq_bot (hall A₀ hA₀) ha hf).symm
  exact (Subgroup.mem_centralizer_iff.mp (hcent hk) f (Set.mem_singleton f)).symm

theorem Hone_le_normalizer_Fcore_sup (h : IsSeed S ρ (Ecore G) ψ)
    (hp : PartnerCoreJ (S : Subgroup G) Fp Zp) (hFQ : Fp ≤ CFSG.pCore 2 G)
    (hnc : ¬ Hone S ≤ Subgroup.centralizer (Zp : Set G)) :
    Hone S ≤ Subgroup.normalizer ((Fcore G ⊔ Fp : Subgroup G) : Set G) := by
  classical
  have hN : ∀ y ∈ Subgroup.normalizer ((Zp : Subgroup G) : Set G), y ∈ Mnorm S ρ :=
    fun y hy => normalizer_le_Mnorm_J h hp.zcentral hnc hy
  obtain ⟨g, -, hgM⟩ := h.exists_Hone_not_mem_Mnorm
  obtain ⟨A, hA, hAQ⟩ := h.exists_max_outside
  have hXB := cj_fp_le_BoneP h hp hFQ hA hAQ hgM hN
  have hAX : ⁅A, cj Fp g⁆ ≤ Fcore G :=
    calc ⁅A, cj Fp g⁆ ≤ ⁅A, CFSG.Quasithin.BoneP Fp A⁆ :=
          Subgroup.commutator_mono le_rfl hXB
      _ ≤ Zfix S ⊔ Zp := commutator_A_BoneP_le h hp hA hAQ
      _ ≤ Fcore G := sup_le h.Zfix_le_Fcore (zp_le_Fcore h hp)
  have hcjA : ⁅cj A g⁻¹, Fp⁆ ≤ Fcore G := by
    have h1 : ⁅cj A g⁻¹, Fp⁆ = cj ⁅A, cj Fp g⁆ g⁻¹ := by
      rw [cj_commutator, cj_inv_cj]
    rw [h1]
    calc cj ⁅A, cj Fp g⁆ g⁻¹ ≤ cj (Fcore G) g⁻¹ := cj_mono hAX
      _ = Fcore G := cj_eq_self_of_normal
  have hTFa : ⁅CFSG.Quasithin.thompsonJ (S : Subgroup G), Fp⁆ = Zp := hp.commJ
  have hTnorm : ∀ t ∈ CFSG.Quasithin.thompsonJ (S : Subgroup G),
      t ∈ Subgroup.normalizer ((Fcore G ⊔ Fp : Subgroup G) : Set G) := by
    intro t ht
    refine mem_normalizer_sup_of_commutator (mem_normalizer_of_normal _ t) fun w hw => ?_
    have h1 : ⁅t, w⁆ ∈ (⁅CFSG.Quasithin.thompsonJ (S : Subgroup G), Fp⁆ : Subgroup G) :=
      Subgroup.commutator_mem_commutator ht hw
    rw [hTFa] at h1
    exact zp_le_Fcore h hp h1
  have hAnorm : ∀ y ∈ cj A g⁻¹,
      y ∈ Subgroup.normalizer ((Fcore G ⊔ Fp : Subgroup G) : Set G) := by
    intro y hy
    refine mem_normalizer_sup_of_commutator (mem_normalizer_of_normal _ y) fun w hw => ?_
    exact hcjA (Subgroup.commutator_mem_commutator hy hw)
  have hJsup : Subgroup.normalizer ((Fcore G ⊔ Fp : Subgroup G) : Set G) ⊔
      CFSG.pCore 2 G = ⊤ := by
    obtain ⟨ℓ, hℓ⟩ := h.exists_rootGrp_eq
    obtain ⟨hmapA, -⟩ := h.max_outside hA hAQ
    have hne : ℓ ≠ ρ g • ℓ := fun e => hgM ((mem_Mnorm_iff hℓ).mpr e.symm)
    refine h.sup_core_eq_top hne ?_ ?_
    · rw [← hℓ, ← hmapA]
      exact Subgroup.map_mono fun a ha => hTnorm a (maxElem_le_thompsonJ hA ha)
    · rw [rootGrp_smul_eq_map, ← hℓ, ← hmapA]
      rintro _ ⟨u, ⟨a, ha, rfl⟩, rfl⟩
      refine ⟨g * a * g⁻¹, hAnorm _ ?_, by simp [MulAut.conj_apply, map_mul, map_inv]⟩
      rw [mem_cj]
      simpa [mul_assoc] using ha
  exact Hone_le_of_sup_core_eq_top hTnorm hJsup

private theorem commutator_core_sup_eq (h : IsSeed S ρ (Ecore G) ψ)
    (hp : PartnerCoreJ (S : Subgroup G) Fp Zp) (hFQ : Fp ≤ CFSG.pCore 2 G)
    (hF : ¬ Fp ≤ Fcore G) :
    ⁅CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G), Fcore G ⊔ Fp⁆ = Zp := by
  have hZaCent : Zp ≤ Subgroup.centralizer
      ((CFSG.Quasithin.thompsonJ (S : Subgroup G)) : Set G) :=
    fun z hz => Subgroup.mem_centralizer_iff.mpr fun s hs => hp.zcentral s hs z hz
  have hTFa : ⁅CFSG.Quasithin.thompsonJ (S : Subgroup G), Fp⁆ = Zp := hp.commJ
  have hRle : CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G) ≤
      CFSG.Quasithin.thompsonJ (S : Subgroup G) := h.thompsonJ_core_le_thompsonJ_sylow
  have hupper : ⁅CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G), Fcore G ⊔ Fp⁆ ≤ Zp := by
    refine commutator_sup_le (N := CFSG.Quasithin.thompsonJ (S : Subgroup G))
      (fun n hn v hv => mem_of_central_conj hZaCent hn hv) (Fcore_le_JS h)
      hp.fp_le_thompsonJ ?_ ?_
    · rw [commutator_eq_bot_of_commute fun r hr f hf =>
        (Fcore_commute_thompsonJ_core hf hr)]
      exact bot_le
    · rw [← hTFa]
      exact Subgroup.commutator_mono hRle le_rfl
  have hlower : Zp ≤ ⁅CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G), Fcore G ⊔ Fp⁆ := by
    obtain ⟨A₀, hA₀Q, hA₀ne⟩ := exists_core_max_not_commute_partnerJ h hp hFQ hF
    have hA₀S := h.max_core_facts.1 A₀ hA₀Q
    have e : ⁅A₀, Fp⁆ = Zp := (hp.commA A₀ hA₀S).resolve_left hA₀ne
    rw [← e]
    exact Subgroup.commutator_mono (maxElem_le_thompsonJ hA₀Q) le_sup_right
  exact le_antisymm hupper hlower

private theorem Hone_le_normalizer_zp (hH1 : Hone S ≤
    Subgroup.normalizer ((Fcore G ⊔ Fp : Subgroup G) : Set G))
    (hRW : ⁅CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G), Fcore G ⊔ Fp⁆ = Zp) :
    ∀ y ∈ Hone S, y ∈ Subgroup.normalizer ((Zp : Subgroup G) : Set G) := by
  intro y hy
  have hyW : cj (Fcore G ⊔ Fp) y = Fcore G ⊔ Fp := by
    apply cj_eq_of_forall_mem
    intro x hx
    exact (Subgroup.mem_normalizer_iff.mp (hH1 hy) x).mp hx
  have h1 : cj ⁅CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G), Fcore G ⊔ Fp⁆ y =
      ⁅CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G), Fcore G ⊔ Fp⁆ := by
    rw [cj_commutator,
      cj_eq_self_of_normal (Y := CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G)), hyW]
  rw [hRW] at h1
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : x ∈ cj Zp y := by rw [h1]; exact hx
    exact mem_cj.mp this
  · intro hx
    have : x ∈ cj Zp y := mem_cj.mpr hx
    rwa [h1] at this

theorem partner_centrality (h : IsSeed S ρ (Ecore G) ψ)
    (hp : PartnerCoreJ (S : Subgroup G) Fp Zp) (hFQ : Fp ≤ CFSG.pCore 2 G) (hF : ¬ Fp ≤ Fcore G) :
    Zp ≤ Hone S ⊓ Subgroup.centralizer (Hone S : Set G) := by
  classical
  by_contra hcon
  have hZaT : Zp ≤ CFSG.Quasithin.thompsonJ (S : Subgroup G) := hp.zp_le_thompsonJ
  have hZaH : Zp ≤ Hone S := hZaT.trans Subgroup.le_normalClosure
  have hnc : ¬ Hone S ≤ Subgroup.centralizer ((Zp : Subgroup G) : Set G) := by
    intro hle
    apply hcon
    exact le_inf hZaH (Subgroup.le_centralizer_iff.mp hle)
  have hN : ∀ y ∈ Subgroup.normalizer ((Zp : Subgroup G) : Set G), y ∈ Mnorm S ρ :=
    fun y hy => normalizer_le_Mnorm_J h hp.zcentral hnc hy
  obtain ⟨g, hgH, hgM⟩ := h.exists_Hone_not_mem_Mnorm
  have hH1 : Hone S ≤ Subgroup.normalizer ((Fcore G ⊔ Fp : Subgroup G) : Set G) :=
    Hone_le_normalizer_Fcore_sup h hp hFQ hnc
  have hHZ := Hone_le_normalizer_zp (Fp := Fp) (Zp := Zp) hH1 (commutator_core_sup_eq h hp hFQ hF)
  exact hgM (hN g (hHZ g hgH))

end PartnerCoreJ

theorem aimgJ_Zfix_le_center_Hone (h : IsSeed S ρ (Ecore G) ψ)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))
    (hV : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G) ≤ CFSG.pCore 2 G)
    (hF : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) ≠ Fcore G) :
    aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S) ≤
      Hone S ⊓ Subgroup.centralizer (Hone S : Set G) := by
  refine PartnerCoreJ.partner_centrality h (partnerCoreJ_aimg h α) (aimgJ_Fcore_le_core h α hV) ?_
  intro hle
  exact hF (Subgroup.eq_of_le_of_card_ge hle
    (card_aimg (S := CFSG.Quasithin.thompsonJ (S : Subgroup G)) (α := α)
      (Fcore_le_JS h)).ge)

end CFSG.QuasithinUnique.Setup.CampbellJ

end
