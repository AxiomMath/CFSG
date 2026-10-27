module

public import CFSG.ClassicalInvolution.Q3.Q3T6OpenMuSym
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenMuCtx

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T6.Mu

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {W : Subgroup G}

theorem dComp_subset_dstarComp (hΩ : HypOmegaGen Ω) (K : Subgroup G) :
    dComp Ω K ⊆ dstarComp Ω K := by
  intro J hJ
  have hJ' : Relation.ReflTransGen (fun M N : Subgroup G => N ∈ Ω ∧ Disconnected.dAdj Ω M N) K J :=
    hJ
  refine Relation.ReflTransGen.mono (p := dstarAdj Ω) ?_ K J hJ'
  intro M N hMN
  refine ⟨hMN.1, ?_⟩
  rcases hMN.2 with h | h
  · exact Or.inl (omegaNbr_subset_omegaStarNbr hΩ M h)
  · exact Or.inr (omegaNbr_subset_omegaStarNbr hΩ N h)

theorem exists_boundary_of_dComp_ne (hΩ : HypOmegaGen Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hne : dComp Ω K ≠ dstarComp Ω K) :
    ∃ K₁ ∈ dComp Ω K, ∃ J₁ ∈ omegaStarNbr Ω K₁, J₁ ∉ dComp Ω K := by
  obtain ⟨J, hJ, hJn⟩ : ∃ J ∈ dstarComp Ω K, J ∉ dComp Ω K := by
    by_contra hcon
    push Not at hcon
    exact hne (Set.Subset.antisymm (dComp_subset_dstarComp hΩ K) hcon)
  have key : ∀ J, Relation.ReflTransGen (dstarAdj Ω) K J → J ∉ dComp Ω K →
      ∃ K₁ ∈ dComp Ω K, ∃ J₁ ∈ omegaStarNbr Ω K₁, J₁ ∉ dComp Ω K := by
    intro J hJ
    induction hJ with
    | refl => exact fun h => absurd (self_mem_dComp' K) h
    | @tail b c _ hbc ih =>
      intro hc
      by_cases hbd : b ∈ dComp Ω K
      · refine ⟨b, hbd, c, ?_, hc⟩
        obtain ⟨hcΩ, h | h⟩ := hbc
        · exact h
        · exact omegaStarNbr_symm hΩ hcΩ (mem_of_mem_dComp' hK hbd) h
      · exact ih hbd
  exact key J hJ hJn

section Ctx

variable (c : Q3CL.Thompson.Ctx Ω W)

include c

theorem ctx_mem_dComp_of_connected (hconn : DbarConnected Ω W) {K₁ J₁ R T : Subgroup G}
    (hK₁ : K₁ ∈ Ω) (hJ₁ : J₁ ∈ Ω) (hR : R ∈ DSet Ω W) (hT : T ∈ DSet Ω W)
    (hRK : IsSylow2In R K₁) (hTJ : IsSylow2In T J₁) : J₁ ∈ dComp Ω K₁ := by
  have key : ∀ R', Relation.ReflTransGen (DbarAdj Ω W) R R' →
      R' ∈ DSet Ω W ∧ ∃ K' ∈ dComp Ω K₁, IsSylow2In R' K' := by
    intro R' h
    induction h with
    | refl => exact ⟨hR, K₁, self_mem_dComp' K₁, hRK⟩
    | @tail b d _ hbd ih =>
      obtain ⟨hbD, K', hK'd, hbK'⟩ := ih
      have hK'Ω : K' ∈ Ω := mem_of_mem_dComp' hK₁ hK'd
      obtain ⟨hdD, hadj⟩ := hbd
      obtain ⟨K'', hK''Ω, hdK''⟩ := exists_isSylow2In_of_mem_RSet hdD.1
      refine ⟨hdD, ?_⟩
      by_cases hKeq : K'' = K'
      · exact ⟨K', hK'd, hKeq ▸ hdK''⟩
      · obtain ⟨rb, hrb, hrbW⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D c.hΩ c.hW hbD
        obtain ⟨rd, hrd, hrdW⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D c.hΩ c.hW hdD
        let ρ : Rep Ω W := ⟨K', b, rb, hK'Ω, hbD, hbK', hrb, hrbW⟩
        let σ : Rep Ω W := ⟨K'', d, rd, hK''Ω, hdD, hdK'', hrd, hrdW⟩
        rcases hadj with ⟨-, hcomm⟩ | ⟨hle, -⟩
        · have hcm : ρ.img * σ.img = σ.img * ρ.img :=
            (piG_comm_iff (hbD.2 hrb) (hdD.2 hrd)).mpr (hcomm rb hrb rd hrd)
          exact ⟨K'', mem_dComp_of_dAdj hK'd hK''Ω
            (Or.inl (ctx_omega_of_comm c ρ σ (Ne.symm hKeq) hcm)), hdK''⟩
        · exact absurd (c.K_eq_of_img_eq σ ρ
            (Q3CL.Thompson.piG_eq_of_le_sup c.hΩ c.hW hbD hdD hle hrb hrd hrbW hrdW)) hKeq
  obtain ⟨-, K'', hK''d, hTK''⟩ := key T (hconn R hR T hT)
  have hK''Ω : K'' ∈ Ω := mem_of_mem_dComp' hK₁ hK''d
  have hT8 : 8 ≤ Nat.card T := Sec6Gen.eight_le_of_mem_RSet c.hΩ hT.1
  have hKJ : K'' = J₁ :=
    Sec6Gen.eq_of_le_of_le c.hΩ hK''Ω hJ₁ hTK''.2.1 (by omega) hTK''.1 hTJ.1
  exact hKJ ▸ hK''d

theorem not_connected_of_dComp_ne {K : Subgroup G} (hK : K ∈ Ω)
    (hne : dComp Ω K ≠ dstarComp Ω K) : ¬ DbarConnected Ω W := by
  intro hconn
  have hΩ := c.hΩ
  have hW := c.hW
  obtain ⟨K₁, hK₁d, J₁, hJ₁, hJ₁n⟩ := exists_boundary_of_dComp_ne hΩ hK hne
  have hK₁ : K₁ ∈ Ω := mem_of_mem_dComp' hK hK₁d
  obtain ⟨hJ₁Ω, -, U, hU, hUJ₁, hUN⟩ := hJ₁
  have hU2 : IsPGroup 2 U := Sec6Gen.isPGroup_of_mem_USet hΩ hU
  obtain ⟨R, hRK, hRU⟩ := Asc77.T3.exists_sylow_normalized hU2 hUN
  have hUR : U ≤ Subgroup.normalizer (R : Set G) := fun u hu =>
    mem_normalizer_iff_conjSub_eq.mpr (hRU u hu)
  obtain ⟨S₁, hS₁⟩ := (hU2.to_sup_of_normal_right' hRK.2.1 hUR).exists_le_sylow
  obtain ⟨S, hWS⟩ := exists_sylow_ge_of_mem_WSet hW
  obtain ⟨g, hg⟩ := exists_conjSub_eq_of_sylow S₁ S
  have hUS : conjSub g U ≤ (S : Subgroup G) := by
    have := conjSub_mono (n := g) (le_sup_left.trans hS₁)
    rwa [hg] at this
  have hRS : conjSub g R ≤ (S : Subgroup G) := by
    have := conjSub_mono (n := g) (le_sup_right.trans hS₁)
    rwa [hg] at this
  have hK' : conjSub g K₁ ∈ Ω := hΩ.conjInvariant g K₁ hK₁
  have hJ' : conjSub g J₁ ∈ Ω := hΩ.conjInvariant g J₁ hJ₁Ω
  have hR'K' : IsSylow2In (conjSub g R) (conjSub g K₁) := hRK.conj g
  have hR'D : conjSub g R ∈ DSet Ω W :=
    Q3CL.Thompson.mem_DSet_of_le_sylow hΩ hW hWS (mem_RSet_of_isSylow2In hK' hR'K') hRS
  obtain ⟨T, hTD, hTJ⟩ := Q3CL.Thompson.exists_sylow_mem_DSet hΩ hW hWS hJ'
    (USet.conj hΩ.conjInvariant hU g) (conjSub_mono hUJ₁) hUS
  have hmem := ctx_mem_dComp_of_connected c hconn hK' hJ' hR'D hTD hR'K' hTJ
  have h1 : conjSub g K₁ ∈ dComp Ω (conjSub g K) :=
    mem_dComp_conjSub hΩ.conjInvariant hK₁d g
  have h2 : conjSub g J₁ ∈ dComp Ω (conjSub g K) := dComp_trans' h1 hmem
  have h3 := mem_dComp_conjSub hΩ.conjInvariant h2 g⁻¹
  rw [conjSub_inv_conjSub, conjSub_inv_conjSub] at h3
  exact hJ₁n h3

end Ctx

theorem thompsonGraphAll (hP : Q3CL.PartIHypG Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hne : dComp Ω K ≠ dstarComp Ω K) (hW : W ∈ WSet Ω) : ¬ DbarConnected Ω W :=
  not_connected_of_dComp_ne (Q3CL.T8.ctxOf hP hW) hK hne

theorem exists_not_conn_of_not_connected (hΩ : HypOmegaGen Ω) (hW : W ∈ WSet Ω)
    (hnc : ¬ DbarConnected Ω W) :
    ∃ d ∈ muDelta Ω W, ∃ a ∈ muDelta Ω W, ¬ Star3T.Conn (muDelta Ω W) d a := by
  by_contra hcon
  push Not at hcon
  apply hnc
  intro R hR T hT
  obtain ⟨r, hr, hrW⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩ hW hR
  obtain ⟨t, ht, htW⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩ hW hT
  have hd : (⟨piG W r, piG_mem_muGroup (Subgroup.mem_sup_left (le_MGrp_of_mem_D hR hr))⟩ :
      ↥(muGroup Ω W)) ∈ muDelta Ω W := ⟨R, hR, r, hr, hrW, rfl⟩
  have ha : (⟨piG W t, piG_mem_muGroup (Subgroup.mem_sup_left (le_MGrp_of_mem_D hT ht))⟩ :
      ↥(muGroup Ω W)) ∈ muDelta Ω W := ⟨T, hT, t, ht, htW, rfl⟩
  have hconn := hcon _ hd _ ha
  have key : ∀ x : ↥(muGroup Ω W), Star3T.Conn (muDelta Ω W)
      ⟨piG W r, piG_mem_muGroup (Subgroup.mem_sup_left (le_MGrp_of_mem_D hR hr))⟩ x →
      ∃ R' ∈ DSet Ω W, ∃ r' ∈ R', r' ∉ W ∧ (x : NQuot (W ⊔ OCW W)) = piG W r' ∧
        Relation.ReflTransGen (DbarAdj Ω W) R R' := by
    intro x hx
    induction hx with
    | refl => exact ⟨R, hR, r, hr, hrW, rfl, Relation.ReflTransGen.refl⟩
    | @tail y z _ hyz ih =>
      obtain ⟨Ry, hRy, ry, hry, hryW, hyr, hpath⟩ := ih
      obtain ⟨Rz, hRz, rz, hrz, hrzW, hzr⟩ := hyz.2.1
      refine ⟨Rz, hRz, rz, hrz, hrzW, hzr, hpath.tail ⟨hRz, ?_⟩⟩
      have hryN := hRy.2 hry
      have hrzN := hRz.2 hrz
      by_cases hyz' : y = z
      · right
        have e : piG W rz = piG W ry := by rw [← hzr, ← hyr, hyz']
        exact ⟨le_sup_of_piG_eq hry hRy.2 hRz.2 (fun x hx hxW =>
            (Q3CL.Thompson.D_piG_eq hΩ hW hRz hx hrz hxW hrzW).trans e),
          le_sup_of_piG_eq hrz hRz.2 hRy.2 (fun x hx hxW =>
            (Q3CL.Thompson.D_piG_eq hΩ hW hRy hx hry hxW hryW).trans e.symm)⟩
      · left
        refine ⟨fun hle => hyz' ?_, fun x hx x' hx' => ?_⟩
        · apply Subtype.ext
          rw [hyr, hzr]
          exact (Q3CL.Thompson.piG_eq_of_le_sup hΩ hW hRy hRz hle hry hrz hryW hrzW).symm
        · by_cases hxW : x ∈ W
          · exact Subgroup.mem_sup_left (comm_mem_of_mem hxW (hRz.2 hx'))
          · by_cases hx'W : x' ∈ W
            · have h2 : x * x' * x⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hRy.2 hx) x').mp hx'W
              exact Subgroup.mem_sup_left (W.mul_mem h2 (W.inv_mem hx'W))
            · have hc : y * z = z * y := hyz.2.2
              have hc' : piG W x * piG W x' = piG W x' * piG W x := by
                rw [Q3CL.Thompson.D_piG_eq hΩ hW hRy hx hry hxW hryW,
                  Q3CL.Thompson.D_piG_eq hΩ hW hRz hx' hrz hx'W hrzW, ← hyr, ← hzr]
                exact congrArg Subtype.val hc
              exact (piG_comm_iff (hRy.2 hx) (hRz.2 hx')).mp hc'
  obtain ⟨R', hR', r', hr', hr'W, hr'eq, hpath⟩ := key _ hconn
  have hr'eq' : piG W t = piG W r' := hr'eq
  refine hpath.tail ⟨hT, Or.inr ⟨?_, ?_⟩⟩
  · exact le_sup_of_piG_eq hr' hR'.2 hT.2 (fun x hx hxW =>
      (Q3CL.Thompson.D_piG_eq hΩ hW hT hx ht hxW htW).trans hr'eq')
  · exact le_sup_of_piG_eq ht hT.2 hR'.2 (fun x hx hxW =>
      (Q3CL.Thompson.D_piG_eq hΩ hW hR' hx hr' hxW hr'W).trans hr'eq'.symm)

end CFSG.ClassicalInvolution.Q3.Q3T6.Mu
