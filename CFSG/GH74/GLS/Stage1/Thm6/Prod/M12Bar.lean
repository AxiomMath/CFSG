module

public import CFSG.GH74.GLS.Stage1.Thm6.Prod.AbstractBar
public import CFSG.GH74.GLS.Stage1.Thm6.Prod.Transport
public import CFSG.GH74.GLS.AssemblyComponents
public import CFSG.GH74.GLS.Stage1.Thm6.Sec14.Struct
public import CFSG.GH74.GLS.Stage1.Thm6.M12Facts.RFacts

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Prod

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm6.M12Facts
  CFSG.GH74.GLS.Stage1.Thm6.Sec13 CFSG.GH74.GLS.Stage1.Thm6.Sec14
open scoped commutatorElement

section Bar

variable {Γ : Type*} [Group Γ] {S' : Subgroup Γ} {a b y x : Γ}

theorem centralizer_z_eq_top (hcen : ∀ g : Γ, g * (a ^ 2 * b ^ 2) = (a ^ 2 * b ^ 2) * g) :
    Subgroup.centralizer ({a ^ 2 * b ^ 2} : Set Γ) = ⊤ := by
  apply eq_top_iff.2
  intro g _
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  rw [Set.mem_singleton_iff] at ht
  rw [ht]
  exact (hcen g).symm

theorem normal_of_conc {R : Subgroup Γ} {z : Γ}
    (hcen : ∀ g : Γ, g * z = z * g)
    (hn : (R.subgroupOf (Subgroup.centralizer ({z} : Set Γ))).Normal) : R.Normal := by
  constructor
  intro r hr g
  have hg : g ∈ Subgroup.centralizer ({z} : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    rw [ht]; exact (hcen g).symm
  have hr' : r ∈ Subgroup.centralizer ({z} : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    rw [ht]; exact (hcen r).symm
  have := hn.conj_mem ⟨r, hr'⟩ hr ⟨g, hg⟩
  exact this

theorem rsub_pGroup (h : M12Data S' a b y x) (hS : Sylow2In S' ⊤) :
    IsPGroup 2 ↥(Rsub S' a b) := by
  have hR : Rsub S' a b = nfSub h pR closed_pR := R_eq h
  have hle : Rsub S' a b ≤ S' := by rw [hR]; exact nfSub_le_S h closed_pR
  exact hS.2.1.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)

theorem exists_comm_z : ∃ p q : NF, pR p ∧ pR q ∧ nfComm p q = zNF := by decide +kernel

theorem commutator_nu (h : M12Data S' a b y x) (p q : NF) :
    ⁅nu a b y x p, nu a b y x q⁆ = nu a b y x (nfComm p q) := by
  simp only [commutatorElement_def, nu_inv h, nu_mul h, nfComm]

theorem barCfg_of_conc [Finite Γ] (h : M12Data S' a b y x) (hS : Sylow2In S' ⊤)
    (hcen : ∀ g : Γ, g * (a ^ 2 * b ^ 2) = (a ^ 2 * b ^ 2) * g)
    (hc : Lemma14_3Conc Γ (a ^ 2 * b ^ 2) (Rsub S' a b) (R1sub a b y))
    [hRn : (Rsub S' a b).Normal] : BarCfg (Rsub S' a b) (a ^ 2 * b ^ 2) := by
  have hC : Subgroup.centralizer ({a ^ 2 * b ^ 2} : Set Γ) = ⊤ := centralizer_z_eq_top hcen
  have hgC : ∀ g : Γ, g ∈ Subgroup.centralizer ({a ^ 2 * b ^ 2} : Set Γ) := fun g => by
    rw [hC]; trivial
  have hR : Rsub S' a b = nfSub h pR closed_pR := R_eq h
  refine
    { pgroup := rsub_pGroup h hS
      card := by rw [hR]; exact card_R h
      quot := ?_
      z_mem := by
        rw [hR, zG_eq (y := y) (x := x)]; exact (nu_mem_nfSub h closed_pR zNF).2 pR_zNF
      z_sq := z_sq h
      z_central := hcen
      z_comm := ?_
      cent_X := ?_ }
  · obtain ⟨e⟩ := hc.quot_S3
    have hn : ((Rsub S' a b).subgroupOf (Subgroup.centralizer ({a ^ 2 * b ^ 2} : Set Γ))).Normal := by
      constructor
      intro n hn g
      exact hRn.conj_mem n hn g
    let e1 : ↥(Subgroup.centralizer ({a ^ 2 * b ^ 2} : Set Γ)) ≃* Γ :=
      (MulEquiv.subgroupCongr hC).trans Subgroup.topEquiv
    have he1 : ((Rsub S' a b).subgroupOf (Subgroup.centralizer ({a ^ 2 * b ^ 2} : Set Γ))).map
        e1.toMonoidHom = Rsub S' a b := by
      ext g
      constructor
      · rintro ⟨c, hc', rfl⟩; exact hc'
      · intro hg; exact ⟨⟨g, hgC g⟩, hg, rfl⟩
    exact ⟨(QuotientGroup.congr _ (Rsub S' a b) e1 he1).symm.trans e⟩
  · obtain ⟨p, q, hp, hq, hpq⟩ := exists_comm_z
    refine ⟨nu a b y x p, ?_, nu a b y x q, ?_, ?_⟩
    · rw [hR]; exact (nu_mem_nfSub h closed_pR p).2 hp
    · rw [hR]; exact (nu_mem_nfSub h closed_pR q).2 hq
    · rw [commutator_nu h, hpq, zG_eq (y := y) (x := x)]
  · intro X r hr hcomm
    have hrange : (X : Subgroup Γ) ≤
        (Subgroup.centralizer ({a ^ 2 * b ^ 2} : Set Γ)).subtype.range := by
      rw [Subgroup.range_subtype, hC]; exact le_top
    have hr' : (⟨r, hgC r⟩ : ↥(Subgroup.centralizer ({a ^ 2 * b ^ 2} : Set Γ))) ∈
        (Rsub S' a b).subgroupOf (Subgroup.centralizer ({a ^ 2 * b ^ 2} : Set Γ)) := hr
    refine hc.cent_X
      (X.comapOfInjective (Subgroup.centralizer ({a ^ 2 * b ^ 2} : Set Γ)).subtype
        (Subgroup.centralizer ({a ^ 2 * b ^ 2} : Set Γ)).subtype_injective hrange)
      ⟨r, hgC r⟩ hr' (fun w hw => ?_)
    have hwX : (w : Γ) ∈ X := by
      have h1 : w ∈ ((X.comapOfInjective (Subgroup.centralizer ({a ^ 2 * b ^ 2} : Set Γ)).subtype
          (Subgroup.centralizer ({a ^ 2 * b ^ 2} : Set Γ)).subtype_injective hrange : Sylow 3 _) :
          Subgroup _) := hw
      rw [Sylow.coe_comapOfInjective] at h1
      exact h1
    apply Subtype.ext
    exact hcomm (w : Γ) hwX

end Bar

section CBar

open CFSG.GH74.GLS.Stage2.Local

variable {G : Type} [Group G] (z : G)

theorem z_mem_Cen : z ∈ Cen z := by
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  rw [Set.mem_singleton_iff] at ht
  rw [ht]

theorem zBar_central (g : CentralizerBar z) :
    g * toBar z ⟨z, z_mem_Cen z⟩ = toBar z ⟨z, z_mem_Cen z⟩ * g := by
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective g
  show QuotientGroup.mk (c * ⟨z, z_mem_Cen z⟩) = QuotientGroup.mk (⟨z, z_mem_Cen z⟩ * c)
  congr 1
  apply Subtype.ext
  exact (Subgroup.mem_centralizer_iff.1 c.2 z (Set.mem_singleton _)).symm

theorem barOf_zpowers :
    barOf z (zpowers z) = zpowers (toBar z ⟨z, z_mem_Cen z⟩) := by
  unfold barOf
  have : (zpowers z).subgroupOf (Cen z) = zpowers (⟨z, z_mem_Cen z⟩ : ↥(Cen z)) := by
    apply le_antisymm
    · rintro ⟨g, hg⟩ hmem
      obtain ⟨n, rfl⟩ := (show g ∈ zpowers z from hmem)
      exact ⟨n, Subtype.ext (by simp)⟩
    · rintro g ⟨n, rfl⟩
      exact ⟨n, by simp⟩
  rw [this, MonoidHom.map_zpowers]

variable {z} [Finite G]

theorem stage1M12_Cfields {S' : Subgroup (CentralizerBar z)} {a b y x : CentralizerBar z}
    (h : M12Data S' a b y x) (hS : Sylow2In S' ⊤)
    (hz : a ^ 2 * b ^ 2 = toBar z ⟨z, z_mem_Cen z⟩)
    (hc : Lemma14_3Conc (CentralizerBar z) (a ^ 2 * b ^ 2) (Rsub S' a b) (R1sub a b y)) :
    (∃ A B : Subgroup (CentralizerBar z), IsCentralProd A B (WBar z) ∧
      Nonempty (↥A ≃* QuaternionGroup 2) ∧ Nonempty (↥B ≃* QuaternionGroup 2) ∧ A.Normal) ∧
    (∃ A : Subgroup (CentralizerBar z), Nonempty (↥A ≃* Multiplicative (ZMod 3)) ∧
      LBar z = oResidual 2 (CentralizerBar z) ∧ oResidual 2 (CentralizerBar z) = WBar z ⊔ A ∧
      generalizedFitting (CentralizerBar z) = WBar z ∧ ⁅WBar z, A⁆ = WBar z ∧
      (∀ w ∈ WBar z, (∀ a ∈ A, a * w = w * a) → w ∈ barOf z (zpowers z))) ∧
    (∃ _ : (WBar z).Normal, Nonempty ((CentralizerBar z ⧸ WBar z) ≃* Equiv.Perm (Fin 3))) := by
  have hcen : ∀ g : CentralizerBar z, g * (a ^ 2 * b ^ 2) = (a ^ 2 * b ^ 2) * g := by
    intro g; rw [hz]; exact zBar_central z g
  have hRn : (Rsub S' a b).Normal := normal_of_conc hcen (by
    have := hc.R_normal
    exact this)
  have hR1n : (R1sub a b y).Normal := normal_of_conc hcen (by
    have := hc.R₁_normal
    exact this)
  have cfg := barCfg_of_conc h hS hcen hc
  have hO : pPrimeCore 2 (CentralizerBar z) = ⊥ := pPrimeCore_quotient_eq_bot _
  obtain ⟨A, hAcyc, hOres, hFst, hcomm, hfix, hpcore, htop, -⟩ := cfg.summary hO
  have hI : oPrimePResidual 2 (CentralizerBar z) ≤ InnerE z := by
    rw [innerE_eq_top_of_fstar_solvable _ (fstar_solvable_of_pcore hFst hpcore)]
    exact le_top
  have hW : WBar z = Rsub S' a b := by rw [WBar_eq z, hpcore]
  have hR : Rsub S' a b = nfSub h pR closed_pR := R_eq h
  have hR1 : R1sub a b y = nfSub h pR1 closed_pR1 := R1_eq h
  refine ⟨⟨nfSub h pR1 closed_pR1, nfSub h pR2 closed_pR2, ?_, R1_q8 h, Sec14.R2_q8 h, ?_⟩,
    ⟨A, hAcyc, LBar_eq_oResidual z htop hI, by rw [hW]; exact hOres, by rw [hW]; exact hFst,
      by rw [hW]; exact hcomm, ?_⟩, ?_⟩
  ·
    have hz1 : orderOf (a ^ 2 * b ^ 2) = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact z_sq h) (z_ne_one h)
    refine ⟨?_, ?_, ?_⟩
    · rw [hW, hR]
      apply le_antisymm
      · exact sup_le (nfSub_le_nfSub h _ _ pR_of_pR1) (nfSub_le_nfSub h _ _ pR_of_pR2)
      · rintro _ ⟨p, hp, rfl⟩
        obtain ⟨q, hq, q', hq', e⟩ := R_decomp p hp
        rw [← e, ← nu_mul h]
        exact Subgroup.mul_mem_sup ((nu_mem_nfSub h closed_pR1 q).2 hq)
          ((nu_mem_nfSub h closed_pR2 q').2 hq')
    · rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
      rw [nu_mul h, nu_mul h, R1R2_comm p q hp hq]
    · have : nfSub h pR1 closed_pR1 ⊓ nfSub h pR2 closed_pR2 = zpowers (a ^ 2 * b ^ 2) := by
        apply le_antisymm
        · rintro _ ⟨⟨p, hp1, rfl⟩, ⟨q, hq2, hqp⟩⟩
          have hpq : q = p := nu_injective h hqp.symm
          subst hpq
          rcases R1R2_inter q hp1 hq2 with rfl | rfl
          · rw [nu_zero]; exact Subgroup.one_mem _
          · rw [← zG_eq (y := y) (x := x)]; exact Subgroup.mem_zpowers _
        · rw [zpowers_le]
          refine ⟨?_, ?_⟩
          · rw [zG_eq (y := y) (x := x)]; exact (nu_mem_nfSub h closed_pR1 zNF).2 pR1_zNF
          · rw [zG_eq (y := y) (x := x)]; exact (nu_mem_nfSub h closed_pR2 zNF).2 pR2_zNF
      rw [this, Nat.card_zpowers, hz1]
  ·
    rw [← hR1]; exact hR1n
  ·
    intro w hw hAw
    have := hfix w (hW ▸ hw) hAw
    rw [barOf_zpowers z, ← hz]
    exact this
  · obtain ⟨e⟩ := cfg.quot
    have hWn : (WBar z).Normal := hW ▸ hRn
    exact ⟨hWn, ⟨(QuotientGroup.quotientMulEquivOfEq hW).trans e⟩⟩

end CBar

end CFSG.GH74.GLS.Stage1.Thm6.Prod
