module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23HeT
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23Suz
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23HeModelC

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.CF23L34

open CFSG Subgroup CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.CatFactsL4U4
open CFSG.ComponentClassification.CatFactsL4U4.OutInv

variable {H : Type} [Group H] [Finite H] {h : Hyp52 H} (hKa : conjugate h.K h.a = h.K)

@[expose] def nlEquivP
    (e : OddBar h.K ≃* Blueprint.NativeSporadic.He) :
    ↥(NL hKa) ≃* ↥heP :=
  (nlEquiv hKa).trans (lkEquivP e)

theorem exists_ident
    (e : OddBar h.K ≃* Blueprint.NativeSporadic.He)
    (hL : Blueprint.LieModel (ZStarBar h.J) .PSL 3 2 2) (hαN : phi hKa (abar h) ∈ NL hKa) :
    ∃ ι : ↥(NL hKa) →* Equiv.Perm (Fin 8330), Function.Injective ι ∧ (∀ γ, ι γ ∈ heP) ∧
      (∀ p ∈ heP, ∃ γ, ι γ = p) ∧ ι ⟨phi hKa (abar h), hαN⟩ = heGenPerm 0 ∧
      ∀ γ : ↥(NL hKa), (γ : ↥(GAut hKa)) ∈ Jhat hKa ↔ ι γ ∈ hjJ := by
  set Θ := nlEquivP hKa e with hΘ
  set αN : ↥(NL hKa) := ⟨phi hKa (abar h), hαN⟩ with hαNdef
  set t' : Equiv.Perm (Fin 8330) := ((Θ αN : ↥heP) : Equiv.Perm (Fin 8330)) with ht'
  have ht'P : t' ∈ heP := (Θ αN).2
  have hordN : orderOf αN = 2 := by
    rw [hαNdef, Subgroup.orderOf_mk]
    exact orderOf_phi_abar' hKa
  have hord : orderOf t' = 2 := by
    rw [ht', Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hordN]
  set Jh : Subgroup ↥(NL hKa) := (Jhat hKa).subgroupOf (NL hKa) with hJh
  have hJhC : ∀ γ ∈ Jh, γ * αN = αN * γ := by
    intro γ hγ
    rw [hJh, mem_subgroupOf] at hγ
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp ((Jhat_component hKa).1 hγ)
  have hcardJ : 5 ∣ Nat.card Jh := by
    have hq : Nat.card (↥(Jhat hKa) ⧸ center ↥(Jhat hKa)) = 20160 :=
      CatLeaf.card_of_isL34Type (lieModel_Jhat hKa hL)
    have h1 := Subgroup.card_quotient_dvd_card (center ↥(Jhat hKa))
    rw [hq] at h1
    rw [hJh, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Jhat_le_NL hKa)).toEquiv]
    exact dvd_trans (by norm_num) h1
  have himg : (Jh.map (heP.subtype.comp Θ.toMonoidHom)) ≤ centralizerIn heP t' := by
    rintro _ ⟨γ, hγ, rfl⟩
    rw [mem_centralizerIn]
    refine ⟨(Θ γ).2, ?_⟩
    have := congrArg (fun z => ((Θ z : ↥heP) : Equiv.Perm (Fin 8330))) (hJhC γ hγ)
    simp only [map_mul, Subgroup.coe_mul] at this
    show ((Θ γ : ↥heP) : Equiv.Perm (Fin 8330)) * t' = t' * ((Θ γ : ↥heP) : Equiv.Perm (Fin 8330))
    rw [ht']
    exact this
  have hcardimg : Nat.card (Jh.map (heP.subtype.comp Θ.toMonoidHom)) = Nat.card Jh :=
    Subgroup.card_map_of_injective (heP.subtype_injective.comp Θ.injective)
  rcases involution_conj_cases ht'P hord with ⟨c, hc, hct⟩ | ⟨c, hc, hct⟩
  swap
  · exfalso
    have hC1 : Nat.card (centralizerIn heP t') = 21504 := by
      rw [hct, centralizerIn, Nat.card_congr (infCentralizerConjEquiv hc heT1P).toEquiv]
      exact card_heP_cent1
    have hdvd := Subgroup.card_dvd_of_le himg
    rw [hcardimg, hC1] at hdvd
    have := dvd_trans hcardJ hdvd
    omega
  set ι : ↥(NL hKa) →* Equiv.Perm (Fin 8330) :=
    (MulAut.conj c⁻¹).toMonoidHom.comp (heP.subtype.comp Θ.toMonoidHom) with hιdef
  have hι : ∀ γ, ι γ = c⁻¹ * ((Θ γ : ↥heP) : Equiv.Perm (Fin 8330)) * c := fun γ => by
    simp [hιdef]
  have hιinj : Function.Injective ι := by
    intro γ γ' hγγ'
    rw [hι, hι, mul_left_inj, mul_right_inj] at hγγ'
    exact Θ.injective (Subtype.ext hγγ')
  have hιP : ∀ γ, ι γ ∈ heP := fun γ => by
    rw [hι]
    exact heP.mul_mem (heP.mul_mem (heP.inv_mem hc) (Θ γ).2) hc
  have hιsurj : ∀ p ∈ heP, ∃ γ, ι γ = p := by
    intro p hp
    refine ⟨Θ.symm ⟨c * p * c⁻¹, heP.mul_mem (heP.mul_mem hc hp) (heP.inv_mem hc)⟩, ?_⟩
    rw [hι, MulEquiv.apply_symm_apply]
    group
  have hια : ι αN = heGenPerm 0 := by
    rw [hι, ← ht', hct]
    group
  have hcomm_iff : ∀ γ : ↥(NL hKa), γ * αN = αN * γ ↔ ι γ * heGenPerm 0 = heGenPerm 0 * ι γ := by
    intro γ
    rw [← hια, ← map_mul, ← map_mul]
    exact ⟨fun h1 => by rw [h1], fun h1 => hιinj h1⟩
  have hmap : (centralizer ({αN} : Set ↥(NL hKa))).map ι = centralizerIn heP (heGenPerm 0) := by
    ext g
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      exact mem_centralizerIn.2 ⟨hιP γ, (hcomm_iff γ).1 (mem_centralizer_singleton_iff.mp hγ)⟩
    · intro hg
      obtain ⟨hgP, hgt⟩ := mem_centralizerIn.1 hg
      obtain ⟨γ, rfl⟩ := hιsurj g hgP
      exact ⟨γ, mem_centralizer_singleton_iff.mpr ((hcomm_iff γ).2 hgt), rfl⟩
  set Φc : ↥(centralizer ({αN} : Set ↥(NL hKa))) ≃* ↥(centralizerIn heP (heGenPerm 0)) :=
    ((centralizer ({αN} : Set ↥(NL hKa))).equivMapOfInjective ι hιinj).trans
      (MulEquiv.subgroupCongr hmap) with hΦc
  have hΦc : ∀ x, (Φc x : Equiv.Perm (Fin 8330)) = ι x := fun _ => rfl
  have hX := isComponent_centralizer_subgroupOf hαN (Jhat_le_NL hKa) (Jhat_component hKa).2
  have hY := LocalCores.isComponent_map_mulEquiv Φc hX
  have heq := component_eq_hjJ hY
  refine ⟨ι, hιinj, hιP, hιsurj, hια, fun γ => ⟨fun hγ => ?_, fun hγ => ?_⟩⟩
  · have hγC : γ ∈ centralizer ({αN} : Set ↥(NL hKa)) :=
      mem_centralizer_singleton_iff.mpr (hJhC γ (by rw [hJh, mem_subgroupOf]; exact hγ))
    have h1 : Φc ⟨γ, hγC⟩ ∈ ((Jh.subgroupOf (centralizer ({αN} : Set ↥(NL hKa))))).map
        Φc.toMonoidHom :=
      ⟨⟨γ, hγC⟩, by rw [SetLike.mem_coe, mem_subgroupOf, mem_subgroupOf]; exact hγ, rfl⟩
    rw [heq, mem_subgroupOf, hΦc] at h1
    exact h1
  · have hγC : γ ∈ centralizer ({αN} : Set ↥(NL hKa)) :=
      mem_centralizer_singleton_iff.mpr ((hcomm_iff γ).2 (mem_centralizerIn.1 (hjJ_le hγ)).2)
    have h1 : Φc ⟨γ, hγC⟩ ∈ hjJ.subgroupOf (centralizerIn heP (heGenPerm 0)) := by
      rw [mem_subgroupOf, hΦc]
      exact hγ
    rw [← heq] at h1
    obtain ⟨x, hx, hxe⟩ := h1
    have hx' : x = ⟨γ, hγC⟩ := Φc.injective hxe
    subst hx'
    rw [SetLike.mem_coe, mem_subgroupOf, mem_subgroupOf] at hx
    exact hx

end CFSG.ComponentClassification.GSThmB.CF23L34
