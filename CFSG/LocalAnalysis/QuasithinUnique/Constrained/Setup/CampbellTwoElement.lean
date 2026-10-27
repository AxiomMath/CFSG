module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellTwoTools
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellDihedral

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Subgroup CFSG CFSG.Quasithin CFSG.Quasithin.BlueprintB2
open scoped LinearAlgebra.Projectivization

section TwoElement

variable {G : Type*} [Group G] {k : Type*} [Field k] {S : Sylow 2 G}
  {ρ : G →* Matrix.SpecialLinearGroup (Fin 2) k} {ψ : Ecore G →* Multiplicative (Fin 2 → k)}

omit [Field k] in
theorem cj_le_core [Finite G] {Y : Subgroup G} (hY : Y ≤ CFSG.pCore 2 G) (w : G) :
    cj Y w ≤ CFSG.pCore 2 G := by
  have := cj_mono (g := w) hY
  rwa [cj_eq_self_of_normal (Y := CFSG.pCore 2 G)] at this

omit [Field k] in
theorem adm_core_cj [Finite G] {Y : Subgroup G} (hY : Adm (CFSG.pCore 2 G) Y) (w : G) :
    Adm (CFSG.pCore 2 G) (cj Y w) := by
  obtain ⟨A, hA, hYA⟩ := hY
  refine ⟨cj A w, ?_, cj_mono hYA⟩
  have := isMaxElemAbelian_cj w hA
  rwa [cj_eq_self_of_normal (Y := CFSG.pCore 2 G)] at this

namespace IsSeed

variable [Finite G] [Finite k] (h : IsSeed S ρ (Ecore G) ψ)
include h

theorem conj_commute_of_mem_sylow (α : (S : Subgroup G) ≃* (S : Subgroup G))
    (hV : aimg (S : Subgroup G) α (Vmod G) ≤ CFSG.pCore 2 G)
    (hF : aimg (S : Subgroup G) α (Fcore G) ≠ Fcore G) {g t : G} (ht : t ∈ (S : Subgroup G)) :
    ⁅cj (aimg (S : Subgroup G) α (Fcore G)) g, cj (aimg (S : Subgroup G) α (Fcore G)) (g * t)⁆ =
      ⊥ := by
  classical
  by_contra hne
  have hZc := h.aimg_Zfix_le_center α hV hF
  have hCSV := h.sylow_inf_centralizer_Vmod
  have hQS : CFSG.pCore 2 G ≤ (S : Subgroup G) := core_le_sylow S
  set Fa := aimg (S : Subgroup G) α (Fcore G) with hFa
  set Va := aimg (S : Subgroup G) α (Vmod G) with hVa
  set Za := aimg (S : Subgroup G) α (Zfix S) with hZa
  set u : G := g * t * g⁻¹ with hu
  have hFaQ : Fa ≤ CFSG.pCore 2 G := h.aimg_Fcore_le_core α hV
  have hVaFa : Va ≤ Fa := aimg_mono (Vmod_le_Ecore.trans h.Ecore_le_Fcore)
  have hZaVa : Za ≤ Va := aimg_mono (inf_le_left : Zfix S ≤ Vmod G)
  have hFaS : Fa ≤ (S : Subgroup G) := aimg_le
  have hFaAdmQ : Adm (CFSG.pCore 2 G) Fa := h.adm_core_aimg_Fcore α hV
  have hsa : aimg (S : Subgroup G) α.symm Fa = Fcore G := aimg_symm_aimg Fcore_le_sylow
  have hZaS : Za ≤ (S : Subgroup G) := aimg_le
  have hFg : cj Fa (g * t) = cj (cj Fa u) g := by
    rw [cj_cj]
    congr 1
    rw [hu]; group
  have hne1 : ⁅Fa, cj Fa u⁆ ≠ ⊥ := by
    intro hb
    apply hne
    rw [hFg, ← cj_commutator, hb, cj_bot]
  have hcjFaS : cj Fa u ≤ (S : Subgroup G) := (cj_le_core hFaQ u).trans hQS
  have hVaQ : Va ≤ CFSG.pCore 2 G := hVaFa.trans hFaQ
  have hcjVaS : cj Va u ≤ (S : Subgroup G) := (cj_le_core hVaQ u).trans hQS
  have hb1 : ⁅Fcore G, aimg (S : Subgroup G) α.symm (cj Fa u)⁆ ≠ ⊥ := by
    intro hb
    apply hne1
    have h1 := aimg_commutator (S := (S : Subgroup G)) (α := α.symm) hFaS hcjFaS
    rw [hsa, hb] at h1
    exact (aimg_eq_bot_iff α.symm (commutator_le_of_le hFaS hcjFaS)).mp h1
  have hrep : cj Fa u = cj Va u ⊔ (cj Fa u ⊓ Subgroup.centralizer (Fa : Set G)) :=
    h.tr_Fcore_rep α u (Y := Fa) (h.adm_cj_of_adm_core hFaAdmQ u)
  have hint : cj Fa u ⊓ Subgroup.centralizer (Fa : Set G) ≤ (S : Subgroup G) :=
    inf_le_left.trans hcjFaS
  have hY : aimg (S : Subgroup G) α.symm (cj Fa u) =
      aimg (S : Subgroup G) α.symm (cj Va u) ⊔
        (aimg (S : Subgroup G) α.symm (cj Fa u) ⊓
          Subgroup.centralizer ((Fcore G : Subgroup G) : Set G)) := by
    conv_lhs => rw [hrep]
    rw [aimg_sup hcjVaS hint, aimg_centralizer hFaS, hsa]
  have hYel : CFSG.Open.IsElemAbelian 2 (aimg (S : Subgroup G) α.symm (cj Fa u)) :=
    isElemAbelian_aimg α.symm (isElemAbelian_cj (isElemAbelian_aimg α isElemAbelian_Fcore) u)
  have hb2 : ⁅Fcore G, aimg (S : Subgroup G) α.symm (cj Va u)⁆ ≠ ⊥ := by
    intro hb
    apply hb1
    rw [Subgroup.commutator_comm]
    have hle : ⁅aimg (S : Subgroup G) α.symm (cj Fa u), Fcore G⁆ ≤
        ⁅aimg (S : Subgroup G) α.symm (cj Va u) ⊔
          (aimg (S : Subgroup G) α.symm (cj Fa u) ⊓
            Subgroup.centralizer ((Fcore G : Subgroup G) : Set G)), Fcore G⁆ :=
      Subgroup.commutator_mono hY.le le_rfl
    have hle2 : ⁅aimg (S : Subgroup G) α.symm (cj Va u) ⊔
          (aimg (S : Subgroup G) α.symm (cj Fa u) ⊓
            Subgroup.centralizer ((Fcore G : Subgroup G) : Set G)), Fcore G⁆ ≤
        ⁅aimg (S : Subgroup G) α.symm (cj Va u), Fcore G⁆ := by
      refine commutator_sup_of_commute (fun x hx c hc => ?_) (fun c hc w hw =>
        (Subgroup.mem_centralizer_iff.mp hc.2 w hw).symm)
      have hxY : x ∈ aimg (S : Subgroup G) α.symm (cj Fa u) := by
        rw [hY]; exact Subgroup.mem_sup_left hx
      exact (isElemAbelian_iff.mp hYel).1 x hxY c hc.1
    rw [Subgroup.commutator_comm] at hb
    have := hle.trans hle2
    rw [hb] at this
    exact le_bot_iff.mp this
  have hUS : aimg (S : Subgroup G) α.symm (cj Va u) ≤ (S : Subgroup G) := aimg_le
  have hUAdm : Adm (S : Subgroup G) (aimg (S : Subgroup G) α.symm (cj Va u)) :=
    adm_aimg α.symm (h.adm_sylow_of_adm_core (adm_core_cj (hFaAdmQ.mono hVaFa) u))
  have hUQ : ¬ aimg (S : Subgroup G) α.symm (cj Va u) ≤ CFSG.pCore 2 G := by
    intro hUQ
    obtain ⟨A', hA', hUA'⟩ := h.adm_core_of_adm hUAdm hUQ
    have hUR : aimg (S : Subgroup G) α.symm (cj Va u) ≤ thompsonJ (CFSG.pCore 2 G) :=
      hUA'.trans (maxElem_le_thompsonJ hA')
    apply hb2
    exact commutator_eq_bot_of_commute fun f hf w hw =>
      (Fcore_commute_thompsonJ_core hf (hUR hw)).symm
  have hex : ∃ v ∈ Vmod G, ∃ w ∈ aimg (S : Subgroup G) α.symm (cj Va u), v * w ≠ w * v := by
    by_contra hall
    push Not at hall
    apply hUQ
    intro w hw
    rw [← hCSV]
    exact ⟨hUS hw, Subgroup.mem_centralizer_iff.mpr fun v hv => hall v hv w hw⟩
  obtain ⟨v, hvV, w, hwU, hvw⟩ := hex
  have hvS : v ∈ (S : Subgroup G) := Vmod_le_sylow hvV
  obtain ⟨y₁, hy₁, hwy₁⟩ := mem_aimg.mp hwU
  have haVa : ((α ⟨v, hvS⟩ : (S : Subgroup G)) : G) ∈ Va := mem_aimg_of_mem (y := ⟨v, hvS⟩) hvV
  have hnc : ((α ⟨v, hvS⟩ : (S : Subgroup G)) : G) * (y₁ : G) ≠
      (y₁ : G) * ((α ⟨v, hvS⟩ : (S : Subgroup G)) : G) := by
    intro hc
    apply hvw
    have h1 : α ⟨v, hvS⟩ * y₁ = y₁ * α ⟨v, hvS⟩ := Subtype.ext hc
    have h2 : (⟨v, hvS⟩ : (S : Subgroup G)) * α.symm y₁ = α.symm y₁ * ⟨v, hvS⟩ := by
      apply α.injective
      rw [map_mul, map_mul, α.apply_symm_apply]; exact h1
    have h3 := congrArg Subtype.val h2
    simp only [Subgroup.coe_mul] at h3
    rw [hwy₁] at h3
    exact h3
  have haQ' : ((α ⟨v, hvS⟩ : (S : Subgroup G)) : G) ∈ CFSG.pCore 2 G := hVaQ haVa
  have haS_u : ((α ⟨v, hvS⟩ : (S : Subgroup G)) : G) ∈ cj (S : Subgroup G) u := by
    have h1 := cj_mono (g := u) hQS
    rw [cj_eq_self_of_normal (Y := CFSG.pCore 2 G)] at h1
    exact h1 haQ'
  have ha_ntQ : ((α ⟨v, hvS⟩ : (S : Subgroup G)) : G) ∉
      tr (S : Subgroup G) α u (CFSG.pCore 2 G) := by
    intro haQ
    exact hnc (tr_core_commute_tr_Vmod α u haQ hy₁)
  have hUC : ∀ x' ∈ aimg (S : Subgroup G) α.symm (cj Va u),
      (∀ v' ∈ Vmod G, v' * x' = x' * v') → x' ∈ Zfix S := by
    intro x' hx' hcomm
    obtain ⟨y₂, hy₂, hy₂e⟩ := mem_aimg.mp hx'
    have hcomm2 : ((α ⟨v, hvS⟩ : (S : Subgroup G)) : G) * (y₂ : G) =
        (y₂ : G) * ((α ⟨v, hvS⟩ : (S : Subgroup G)) : G) := by
      have h1 : (⟨v, hvS⟩ : (S : Subgroup G)) * α.symm y₂ = α.symm y₂ * ⟨v, hvS⟩ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        rw [hy₂e]; exact hcomm v hvV
      have h2 := congrArg α h1
      rw [map_mul, map_mul, α.apply_symm_apply] at h2
      exact congrArg Subtype.val h2
    have hZ1 := h.tr_sylow_not_core_comm_Vmod α u haS_u ha_ntQ hy₂ hcomm2
    have hZ2 : (y₂ : G) ∈ Za := by
      have : cj Za u = Za := cj_eq_of_le_center hZc u
      rw [← this]; exact hZ1
    have h3 := (mem_aimg_symm_iff y₂.2).mp hZ2
    simpa [hy₂e] using h3
  have hUQeq : aimg (S : Subgroup G) α.symm (cj Va u) ⊓ CFSG.pCore 2 G = Zfix S := by
    apply le_antisymm
    · rintro x ⟨hxU, hxQ⟩
      exact hUC x hxU fun v' hv' => (Ecore_commute_core hxQ (Vmod_le_Ecore hv')).symm
    · intro z hz
      refine ⟨?_, Ecore_le_core (Vmod_le_Ecore ((inf_le_left : Zfix S ≤ Vmod G) hz))⟩
      have hzS : z ∈ (S : Subgroup G) := Zfix_le_sylow hz
      have h1 : ((α ⟨z, hzS⟩ : (S : Subgroup G)) : G) ∈ Za := mem_aimg_of_mem hz
      have h2 : ((α ⟨z, hzS⟩ : (S : Subgroup G)) : G) ∈ cj Va u := by
        have : cj Za u = Za := cj_eq_of_le_center hZc u
        have h3 : ((α ⟨z, hzS⟩ : (S : Subgroup G)) : G) ∈ cj Za u := by rw [this]; exact h1
        exact cj_mono hZaVa h3
      exact mem_aimg.mpr ⟨α ⟨z, hzS⟩, h2, by simp⟩
  have hcardU : Nat.card (aimg (S : Subgroup G) α.symm (cj Va u)) = Nat.card (Vmod G) := by
    rw [card_aimg hcjVaS, card_cj, card_aimg Vmod_le_sylow]
  have hSUQ := h.sylow_eq_sup_of_card hUS hcardU (by rw [hUQeq])
  have ht' : t ∈ CFSG.pCore 2 G ⊔ aimg (S : Subgroup G) α.symm (cj Va u) := by
    rw [sup_comm, ← hSUQ]; exact ht
  obtain ⟨q₀, hq₀, x, hxU, hqx⟩ := Subgroup.mem_sup_of_normal_left.mp ht'
  have hFt : cj Fa (g * t) = cj Fa (g * x) := by
    have e1 : g * t = (g * q₀ * g⁻¹) * (g * x) := by rw [← hqx]; group
    rw [e1, ← cj_cj]
    have : cj Fa (g * q₀ * g⁻¹) = Fa :=
      cj_eq_of_forall_mem fun z hz => aimg_Fcore_normal_mem α
        (hQS ((CFSG.pCore_normal (G := G) (p := 2)).conj_mem q₀ hq₀ g)) hz
    rw [this]
  rw [hFt] at hne
  have hUel : CFSG.Open.IsElemAbelian 2 (aimg (S : Subgroup G) α.symm (cj Va u)) :=
    isElemAbelian_aimg α.symm (isElemAbelian_cj (isElemAbelian_aimg α isElemAbelian_Vmod) u)
  have hx2 : x * x = 1 := by rw [← pow_two]; exact (isElemAbelian_iff.mp hUel).2 x hxU
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hex_y : ∃ y ∈ cj Va g, y ∉ Za := by
    by_contra hall
    push Not at hall
    have h1 := Subgroup.card_le_of_le (show cj Va g ≤ Za from hall)
    rw [card_cj, card_aimg Vmod_le_sylow, ← h.card_k_mul_card_Zfix, card_aimg Zfix_le_sylow] at h1
    obtain ⟨n, hn, hk⟩ := h.card_k
    have hpos : 0 < Nat.card (Zfix S) := Nat.card_pos
    have h2 : 2 ≤ Nat.card k := by
      rw [hk]
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h3 := Nat.mul_le_mul_right (Nat.card (Zfix S)) h2
    linarith
  obtain ⟨y, hyVa, hyZa⟩ := hex_y
  have hyFa : y ∈ cj Fa g := cj_mono hVaFa hyVa
  have hyW : y ∈ Wnc S α := by
    have : y ∈ ⨆ g : G, cj Fa g := Subgroup.mem_iSup_of_mem g hyFa
    rwa [← Wnc_eq_iSup] at this
  have hyR : y ∈ thompsonJ (CFSG.pCore 2 G) := h.Wnc_le_thompsonJ_core α hV hyW
  have hy2 : y ^ 2 = 1 :=
    (isElemAbelian_iff.mp (isElemAbelian_cj (isElemAbelian_aimg α isElemAbelian_Vmod) g)).2 y hyVa
  have hdih := h.dihedral_commute α hV hF u⁻¹ (v := x) (by rw [inv_inv]; exact hxU) hyW hy2
  have hCR : ∀ r ∈ thompsonJ (CFSG.pCore 2 G), r * y = y * r →
      ∀ w' ∈ cj Va g, r * w' = w' * r := by
    intro r hr hry w' hw'
    have hrS : r ∈ cj (S : Subgroup G) g := by
      have h1 := cj_mono (g := g) hQS
      rw [cj_eq_self_of_normal (Y := CFSG.pCore 2 G)] at h1
      exact h1 (thompsonJ_le_self' _ hr)
    have hrQ : r ∈ tr (S : Subgroup G) α g (CFSG.pCore 2 G) := by
      by_contra hrQ
      have hZy := h.tr_sylow_not_core_comm_Vmod α g hrS hrQ hyVa hry
      have : cj Za g = Za := cj_eq_of_le_center hZc g
      apply hyZa
      rw [← this]; exact hZy
    exact tr_core_commute_tr_Vmod α g hrQ hw'
  have hrR : x⁻¹ * y * x ∈ thompsonJ (CFSG.pCore 2 G) := by
    have := thompsonJ_conj_mem hyR x⁻¹
    simpa using this
  have hrW := hCR _ hrR hdih.symm
  have hVagx : ∀ w ∈ cj Va (g * x), y * w = w * y := by
    intro w hw
    have hw' : x * w * x⁻¹ ∈ cj Va g := by
      have : cj Va (g * x) = cj (cj Va g) x := by rw [cj_cj]
      rw [this] at hw; exact mem_cj.mp hw
    have h1 := hrW _ hw'
    have hxxz : ∀ z : G, x * (x * z) = z := fun z => by rw [← mul_assoc, hx2, one_mul]
    rw [hxinv] at h1
    simp only [mul_assoc, hxxz] at h1
    have h2 := mul_left_cancel h1
    have h3 : y * w * x = w * y * x := by simpa only [mul_assoc] using h2
    exact mul_right_cancel h3
  have hVagxR : cj Va (g * x) ≤ thompsonJ (CFSG.pCore 2 G) := by
    have h1 := cj_mono (g := g * x) (hVaFa.trans (h.aimg_Fcore_le_thompsonJ_core α hV))
    rwa [cj_eq_self_of_normal (Y := thompsonJ (CFSG.pCore 2 G))] at h1
  have hVV : ∀ w ∈ cj Va (g * x), ∀ w' ∈ cj Va g, w * w' = w' * w := fun w hw w' hw' =>
    hCR w (hVagxR hw) (hVagx w hw).symm w' hw'
  have hrep2 : cj Fa (g * x) = cj Va (g * x) ⊔
      (cj Fa (g * x) ⊓ Subgroup.centralizer ((cj Va g : Subgroup G) : Set G)) :=
    h.tr_Fcore_rep α (g * x) (Y := cj Va g)
      (h.adm_cj_of_adm_core (adm_core_cj (hFaAdmQ.mono hVaFa) g) (g * x))
  have hFaVa : cj Fa (g * x) ≤ Subgroup.centralizer ((cj Va g : Subgroup G) : Set G) := by
    rw [hrep2]
    exact sup_le (fun w hw => Subgroup.mem_centralizer_iff.mpr fun w' hw' => (hVV w hw w' hw').symm)
      inf_le_right
  have hrep3 : cj Fa g = cj Va g ⊔
      (cj Fa g ⊓ Subgroup.centralizer ((cj Fa (g * x) : Subgroup G) : Set G)) :=
    h.tr_Fcore_rep α g (Y := cj Fa (g * x))
      (h.adm_cj_of_adm_core (adm_core_cj hFaAdmQ (g * x)) g)
  have hfinal : cj Fa g ≤ Subgroup.centralizer ((cj Fa (g * x) : Subgroup G) : Set G) := by
    rw [hrep3]
    exact sup_le (Subgroup.le_centralizer_iff.mp hFaVa) inf_le_right
  apply hne
  exact commutator_eq_bot_of_commute fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (hfinal ha) b hb).symm

theorem two_element_conjugate_commutation (α : (S : Subgroup G) ≃* (S : Subgroup G))
    (hV : aimg (S : Subgroup G) α (Vmod G) ≤ CFSG.pCore 2 G) (g x : G)
    (hx : ∃ n : ℕ, x ^ (2 ^ n) = 1) :
    ⁅cj (aimg (S : Subgroup G) α (Fcore G)) g,
      cj (aimg (S : Subgroup G) α (Fcore G)) (g * x)⁆ = ⊥ := by
  by_cases hF : aimg (S : Subgroup G) α (Fcore G) = Fcore G
  · rw [hF, cj_eq_self_of_normal, cj_eq_self_of_normal]
    exact commutator_eq_bot_of_commute fun a ha b hb =>
      (isElemAbelian_iff.mp (isElemAbelian_Fcore (G := G))).1 a ha b hb
  · obtain ⟨c, hc⟩ := exists_conj_mem_sylow hx S
    have h1 := h.conj_commute_of_mem_sylow α hV hF (g := g * c) (t := c⁻¹ * x * c) hc
    have e : g * c * (c⁻¹ * x * c) = g * x * c := by group
    rw [e, ← cj_cj, ← cj_cj, ← cj_commutator] at h1
    calc ⁅cj (aimg (S : Subgroup G) α (Fcore G)) g,
          cj (aimg (S : Subgroup G) α (Fcore G)) (g * x)⁆
        = cj (cj ⁅cj (aimg (S : Subgroup G) α (Fcore G)) g,
            cj (aimg (S : Subgroup G) α (Fcore G)) (g * x)⁆ c) c⁻¹ := cj_inv_cj.symm
      _ = cj ⊥ c⁻¹ := by rw [h1]
      _ = ⊥ := cj_bot

end IsSeed

end TwoElement

end CFSG.QuasithinUnique.Setup.Campbell
