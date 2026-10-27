module

public import CFSG.LargeExtraspecial.S14C13B1b
public import CFSG.LargeExtraspecial.S14C13A
public import CFSG.LargeExtraspecial.S14C10Main

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial.S4

section Generic

variable {Y : Type} [Group Y] {M : Subgroup Y} {M0 : Subgroup M} {t0 : M0}

theorem quotientIso_of_sym3 {N : Subgroup Y}
    (hF : (timmesfeldFStar ↥(M ⊓ centralizer ({((t0 : M) : Y)} : Set Y))).map
      (M ⊓ centralizer ({((t0 : M) : Y)} : Set Y)).subtype = N)
    (hCt : M ⊓ centralizer ({((t0 : M) : Y)} : Set Y) = Ct0 M0 ((t0 : M) : Y))
    (hmap : (timmesfeldFStar (centralizer ({t0} : Set M0))).map (inclC M0 t0) = N)
    {P : Type*} [Group P] (Φ : centralizer ({t0} : Set M0) →* Equiv.Perm (Fin 3) × P)
    (hΦs : Function.Surjective Φ)
    (hΦk : Φ.ker = timmesfeldFStar (centralizer ({t0} : Set M0)))
    {X : Type*} [Group X] (eX : P ≃* X) :
    timmesfeldQuotientIso (timmesfeldFStar (centralizer ({(t0 : M)} : Set M)))
      (Equiv.Perm (Fin 3) × X) := by
  have hΦ1 := map_eq_one_iff_of_ker hmap hΦk
  let e0 : centralizer ({t0} : Set M0) ≃* ↥(M ⊓ centralizer ({((t0 : M) : Y)} : Set Y)) :=
    (MonoidHom.ofInjective (inclC_injective (t0 := t0))).trans
      (MulEquiv.subgroupCongr ((range_inclC (t0 := t0)).trans hCt.symm))
  have he0 : ∀ c, (e0 c).1 = inclC M0 t0 c := fun c =>
    MonoidHom.ofInjective_apply (inclC_injective (t0 := t0)) (x := c)
  let ψ : ↥(M ⊓ centralizer ({((t0 : M) : Y)} : Set Y)) →* Equiv.Perm (Fin 3) × X :=
    ((MonoidHom.id _).prodMap eX.toMonoidHom).comp (Φ.comp e0.symm.toMonoidHom)
  have hψs : Function.Surjective ψ := by
    intro y
    obtain ⟨c, hc⟩ := hΦs (y.1, eX.symm y.2)
    refine ⟨e0 c, ?_⟩
    show Prod.map (MonoidHom.id _) eX.toMonoidHom (Φ (e0.symm (e0 c))) = y
    rw [MulEquiv.symm_apply_apply, hc]
    exact Prod.ext rfl (eX.apply_symm_apply y.2)
  refine quotientIso_centralizer (t0 : M) hψs ?_
  ext x
  rw [MonoidHom.mem_ker]
  have h1 : ψ x = 1 ↔ Φ (e0.symm x) = 1 := by
    show Prod.map (MonoidHom.id _) eX.toMonoidHom (Φ (e0.symm x)) = 1 ↔ _
    simp only [Prod.ext_iff, Prod.map_fst, Prod.map_snd, Prod.fst_one, Prod.snd_one,
      MonoidHom.id_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
  rw [h1, hΦ1, ← he0, MulEquiv.apply_symm_apply, ← hF]
  exact mem_map_iff_mem Subtype.val_injective

theorem eq_one_of_central_of_equiv {P A : Type*} [Group P] [Group A] [IsSimpleGroup A]
    (hnc : ∃ a b : A, a * b ≠ b * a) (e : P ≃* A) {p : P} (hp : ∀ q, p * q = q * p) :
    p = 1 := by
  have h1 := eq_one_of_central_of_simple hnc (z := e p) fun a => by
    obtain ⟨q, rfl⟩ := e.surjective a
    rw [← map_mul, hp q, map_mul]
  exact e.injective (h1.trans (map_one e).symm)

end Generic

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem quotientIso_of_Phi {t0 : Mbar0 S} (htM : ((t0 : S.Mbar) : S.O) ∈ S.Mbar)
    (hF : FCt S ((t0 : S.Mbar) : S.O) = Nbar S g ((t0 : S.Mbar) : S.O))
    (hCt : Ct S ((t0 : S.Mbar) : S.O) = Ct0 (Mbar0 S) ((t0 : S.Mbar) : S.O))
    (hmap : (timmesfeldFStar (centralizer ({t0} : Set (Mbar0 S)))).map (inclC (Mbar0 S) t0) =
      Nbar S g ((t0 : S.Mbar) : S.O))
    {P : Type} [Group P] (Φ : centralizer ({t0} : Set (Mbar0 S)) →* Equiv.Perm (Fin 3) × P)
    (hΦs : Function.Surjective Φ)
    (hΦk : Φ.ker = timmesfeldFStar (centralizer ({t0} : Set (Mbar0 S))))
    {X : Type} [Group X] (eX : P ≃* X) :
    timmesfeldQuotientIso (timmesfeldFStar (centralizer
      ({(⟨((t0 : S.Mbar) : S.O), htM⟩ : S.Mbar)} : Set S.Mbar))) (Equiv.Perm (Fin 3) × X) :=
  quotientIso_of_sym3 hF hCt hmap Φ hΦs hΦk eX

theorem b1_final (hYb : Ybar13Stmt) [IsSimpleGroup G]
    {t0 : Mbar0 S} (hSt : Stage S g ((t0 : S.Mbar) : S.O))
    (hocc : Config.omegaPlus8b.Occurs S g ((t0 : S.Mbar) : S.O))
    (hext : IsExtraspecialPGroup 2 (Nbar S g ((t0 : S.Mbar) : S.O)))
    (h6 : IsSimpleGroup (Mbar0 S)) (h7 : Concl14_7 S g ((t0 : S.Mbar) : S.O))
    (hF : FCt S ((t0 : S.Mbar) : S.O) = Nbar S g ((t0 : S.Mbar) : S.O))
    (hperf : ⁅Rbar S g ((t0 : S.Mbar) : S.O), Rbar S g ((t0 : S.Mbar) : S.O)⁆ =
      Rbar S g ((t0 : S.Mbar) : S.O))
    (hR0 : Rbar S g ((t0 : S.Mbar) : S.O) ≤ Ct0 (Mbar0 S) ((t0 : S.Mbar) : S.O))
    (hmap : (timmesfeldFStar (centralizer ({t0} : Set (Mbar0 S)))).map (inclC (Mbar0 S) t0) =
      Nbar S g ((t0 : S.Mbar) : S.O))
    {P : Type} [Group P] (Φ : centralizer ({t0} : Set (Mbar0 S)) →* Equiv.Perm (Fin 3) × P)
    (hΦs : Function.Surjective Φ)
    (hΦk : Φ.ker = timmesfeldFStar (centralizer ({t0} : Set (Mbar0 S)))) :
    Bridge.TimmesfeldAlt8 S.width S.Mbar := by
  have haQ := hSt.hyp4.conj_mem
  have hK1 := fst_eq_one_of_perfect Φ (comap_inclC_perfect hR0 hperf)
  have hpre := b1_structure hYb hSt hocc hext h7 hF hR0 hmap Φ hΦs hΦk hK1
  obtain ⟨ePR⟩ := b1_equiv haQ hR0 hmap Φ hΦs hΦk hpre hK1
  obtain ⟨⟨H, C, ht, ht1, hVQ, hΩ, hdim⟩, hplus⟩ := hocc.1
  have hsR : IsSimpleGroup (RmodN S g ((t0 : S.Mbar) : S.O)) :=
    ((S45Q.hyp45Q H C).omega ht ht1 hVQ hΩ (by omega)).1
  have hZ : ∀ p : P, (∀ q, p * q = q * p) → p = 1 := fun _ hp =>
    eq_one_of_central_of_equiv (exists_noncomm_RmodN haQ hperf) ePR hp
  have hCt0 := b1_Ct_le hYb hSt hocc hext h7 hF hR0 hmap Φ hΦs hΦk hpre hK1 hZ
  have hCt := le_antisymm hCt0 (Ct0_le _)
  have htN := S6.self_mem_Nbar hSt.hyp4 hSt.mem
  have : (Mbar0 S).Normal := timmesfeldFStar_normal S.Mbar
  have htop : Mbar0 S = ⊤ := eq_top_of_centralizer_le (Rbar_le_Mbar (Nbar_le_Rbar htN)) hF
    hext.1 htN hSt.ne_one (fun y hy hyc => eq_one_or_eq_of_centralizes_Nbar hSt hext hy hyc)
    fun x hx => Subgroup.mem_map.mpr (mem_Ct0.mp (hCt0 hx)).1
  have hsimple : IsSimpleGroup S.Mbar := (MulEquiv.isSimpleGroup_congr
    ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv)).mp h6
  obtain ⟨htM, ht2, -, ⟨eF⟩⟩ := partA_data hSt hext hF
  obtain ⟨Q, hQ, -, hX, -, horb⟩ := hΩ.exists_form
  obtain ⟨eΩ⟩ := nonempty_omegaGroup_equiv_omegaPlus hQ (m := 4) (by rw [hdim]) (by norm_num)
    (isPlusType_of_rnPlus horb hplus)
  refine ⟨hsimple, ⟨_, htM⟩, ht2, (Bridge.timmesfeldIsExtraspecial_congr eF).mpr
    ((Bridge.timmesfeldIsExtraspecial_iff _).mpr hext), Or.inl ⟨hocc.2.1,
      (Nat.card_congr eF.toEquiv).trans hocc.2.2, ?_⟩⟩
  exact quotientIso_of_Phi htM hF hCt hmap Φ hΦs hΦk
    (ePR.trans ((MulEquiv.subgroupCongr hX).trans eΩ))

theorem claim14_13B1_of (hCE : CentralExtInput.{0}) (h2 : PSLPSU10Input) (hYb : Ybar13Stmt) :
    Claim14_13B1 := by
  intro G _ _ _ S g t hSt hocc hext h6 h7 h8 hF ih
  obtain ⟨H, C, ht, ht1, hVQ, hcase, -⟩ := case_of_occurs hocc
  have haQ := H.conj_mem
  have htN := S6.self_mem_Nbar H ht
  have htc : ∀ y ∈ Nbar S g t, t * y = y * t := fun y hy =>
    (commute_of_mem_Rbar haQ (Nbar_le_Rbar hy)).symm
  have hperf := rbarPerfectStmt_of hCE G S g t _ hSt hocc hext
  have hcardN : Nat.card (Nbar S g t) = 2 ^ 17 := hocc.2.2
  have hd : finrank (ZMod 2) (Vt S g t) = 8 := hocc.1.1.2.2.2.2.2.2
  have hnonab := exists_noncomm_Mbar0 hext htN ht1 htc h8
  have hle : FCt S t ≤ (Mbar0 S).map S.Mbar.subtype := fun x hx => by
    rw [hF] at hx
    exact h8 (Nbar_le_Rbar hx)
  obtain ⟨t0, rfl⟩ : ∃ t0 : Mbar0 S, ((t0 : S.Mbar) : S.O) = t := by
    obtain ⟨m, hm, hmt⟩ := h8 (Nbar_le_Rbar htN)
    exact ⟨⟨m, hm⟩, hmt⟩
  have ht2 : orderOf t0 = 2 := by
    refine orderOf_eq_prime ?_ fun h => ht1 (congrArg (fun y : Mbar0 S => ((y : S.Mbar) : S.O)) h)
    have := mul_self_of_mem_Lbar S haQ ht
    exact Subtype.ext (Subtype.ext (by simpa [pow_two] using this))
  have hR0 : Rbar S g ((t0 : S.Mbar) : S.O) ≤ Ct0 (Mbar0 S) ((t0 : S.Mbar) : S.O) := fun r hr =>
    mem_Ct0.mpr ⟨Subgroup.mem_map.mp (h8 hr),
      mem_centralizer_singleton_iff.mp (Rbar_le_centralizer haQ hr)⟩
  have hmap : (timmesfeldFStar (centralizer ({t0} : Set (Mbar0 S)))).map (inclC (Mbar0 S) t0) =
      Nbar S g ((t0 : S.Mbar) : S.O) :=
    (map_fstar_inclC (timmesfeldFStar_normal S.Mbar) h7.2 hle).trans hF
  obtain ⟨X, _, φ, hφs, hφk, hconc⟩ := exists_conclusion_of_mainFor (w := 8) ih hnonab ht2 hmap
    hext (hcardN.trans (by norm_num))
  rcases hconc.width_eight with hX | ⟨-, -, q, -, h3⟩
  · exfalso
    have e := (Subgroup.equivMapOfInjective _ _ (inclC_injective (t0 := t0))).trans
      (MulEquiv.subgroupCongr hmap)
    exact false_of_alt2 h2 hcase (Or.inl hd) hcardN hperf hR0 hmap
      ((Bridge.timmesfeldIsExtraspecial_congr e).mpr
        ((Bridge.timmesfeldIsExtraspecial_iff _).mpr hext))
      ((Nat.card_congr e.toEquiv).trans hcardN) ht2 hX
  · rcases h3 with h3 | h3
    · obtain ⟨e⟩ := h3
      exact b1_final hYb hSt hocc hext h6 h7 hF hperf hR0 hmap (e.toMonoidHom.comp φ)
        (e.surjective.comp hφs) ((ker_mulEquiv_comp φ e).trans hφk)
    · obtain ⟨e⟩ := h3
      exact b1_final hYb hSt hocc hext h6 h7 hF hperf hR0 hmap (e.toMonoidHom.comp φ)
        (e.surjective.comp hφs) ((ker_mulEquiv_comp φ e).trans hφk)

end CFSG.LargeExtraspecial.S14
