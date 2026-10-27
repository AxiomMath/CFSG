module

public import CFSG.CGT.PushingUpLit.CGT6X.End4S
public import CFSG.CGT.PushingUpLit.CGT6.EmbAltRec
public import CFSG.CGT.PushingUpLit.CGT6.EmbNatLiftArrow
public import CFSG.CGT.PushingUpLit.CGT6.EmbAltY

public section

open scoped commutatorElement

namespace CFSG.CGT.PushingUpLit.CGT6X.End4

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit.CGT6
  CFSG.CGT.PushingUpLit.CGT6X.End3 CFSG.CGT.PushingUpLit.BHS6 CFSG.CGT.PushingUp

variable {V : Type} [CommGroup V]

theorem swap_conj_three {n : ℕ} {g : Equiv.Perm (Fin n)} (hg : g.IsThreeCycle) {a b c : Fin n}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (h1 : g a = b) (h2 : g b = c) (h3 : g c = a) :
    Equiv.swap a b * g * (Equiv.swap a b)⁻¹ = g⁻¹ := by
  have hsub : ({a, b, c} : Finset (Fin n)) ⊆ g.support := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rw [Equiv.Perm.mem_support]
    rcases hz with rfl | rfl | rfl
    · rw [h1]; exact hab.symm
    · rw [h2]; exact hbc.symm
    · rw [h3]; exact hac
  have hcard : ({a, b, c} : Finset (Fin n)).card = 3 := by
    rw [Finset.card_eq_three]
    exact ⟨a, b, c, hab, hac, hbc, rfl⟩
  have hsupp : ({a, b, c} : Finset (Fin n)) = g.support :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hg.card_support])
  refine Equiv.ext fun z => ?_
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_inv]
  by_cases hza : z = a
  · subst hza
    rw [Equiv.swap_apply_left, h2, Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm]
    exact ((Equiv.Perm.inv_eq_iff_eq).mpr h3.symm).symm
  by_cases hzb : z = b
  · subst hzb
    rw [Equiv.swap_apply_right, h1, Equiv.swap_apply_right]
    exact ((Equiv.Perm.inv_eq_iff_eq).mpr h1.symm).symm
  by_cases hzc : z = c
  · subst hzc
    rw [Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm, h3, Equiv.swap_apply_left]
    exact ((Equiv.Perm.inv_eq_iff_eq).mpr h2.symm).symm
  · have hz : z ∉ g.support := by
      rw [← hsupp]
      simp [hza, hzb, hzc]
    have hgz : g z = z := Equiv.Perm.notMem_support.mp hz
    rw [Equiv.swap_apply_of_ne_of_ne hza hzb, hgz, Equiv.swap_apply_of_ne_of_ne hza hzb]
    exact ((Equiv.Perm.inv_eq_iff_eq).mpr hgz.symm).symm

section TypeA

variable [Finite V] {G T Y : Subgroup (MulAut V)}

theorem a7_typeA_false (hV : ∀ v : V, v ^ 2 = 1) (cfg : EndCfg4 G T Y)
    (e : LayerQ G Y ≃* alternatingGroup (Fin 7)) {t : MulAut V} (htT : t ∈ T) (ht2 : t * t = 1)
    (hH : (Y.subgroupOf (CGT6.conjClosure Y G)).map (piHom e) = altStabilizer 7 {5, 6})
    (hσ : ∀ (l : MulAut V) (hl : l ∈ CGT6.conjClosure Y G),
      ((piHom e ⟨t * l * t⁻¹, conj_mem_conjClosure (cfg.adm.hTG htT) hl⟩ :
        alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) =
        Equiv.swap 5 6 * ((piHom e ⟨l, hl⟩ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) *
          (Equiv.swap 5 6)⁻¹)
    (hA : IsNatSectionBy (altAct 5) Y (commV Y) (commV Y ⊓ fixV Y)) : False := by
  have hYL : Y ≤ CGT6.conjClosure Y G := CGT6.le_conjClosure
  have hLG : CGT6.conjClosure Y G ≤ G := CGT6.conjClosure_le (cfg.adm.hYC.trans inf_le_left)
  have hperfY : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr cfg.adm.hperf
  obtain ⟨hinv, θY, β, hβs, hβk, hβe⟩ := id hA
  have hbot : commV Y ⊓ fixV Y = ⊥ :=
    commV_inf_fixV_eq_bot_of_quot hV (by decide) (by norm_num) θY β hβs hβk hβe
  have hnat : IsNatSectionWith (altAct 5) θY (commV Y) ⊥ :=
    ⟨hinv, β, hβs, by rw [hβk, hbot], hβe⟩
  have hcenter : Subgroup.center ↥(CGT6.conjClosure Y G) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    exact center_trivial_of_typeA hV cfg hA (fun l hl =>
      (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨l, hl⟩)).symm)
  have hinj : Function.Injective (piHom e) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_piHom e, hcenter]
  let θ : ↥(CGT6.conjClosure Y G) ≃* alternatingGroup (Fin 7) :=
    MulEquiv.ofBijective (piHom e) ⟨hinj, piHom_surjective e⟩
  have hθ : ∀ l : ↥(CGT6.conjClosure Y G), θ l = piHom e l := fun l => rfl
  have hθmap : θ.toMonoidHom = piHom e := MonoidHom.ext fun l => rfl
  have hVL := commV_conjClosure_eq_top hV cfg
  have hC := fix_conjClosure_trivial hV cfg
  have hK : (Y.subgroupOf (CGT6.conjClosure Y G)).map θ.toMonoidHom =
      altStabilizer (5 + 2) {5, 6} := by
    rw [hθmap]
    exact hH
  have hE : commV (Subgroup.zpowers t) ≤ fixV Y := commV_zpowers_le_fixV hV cfg htT ht2
  have hNtriv : ∀ (x : MulAut V) (hx : x ∈ CGT6.conjClosure Y G) (c : Fin (5 + 2)), c ≠ 5 → c ≠ 6 →
      ((θ ⟨x, hx⟩ : alternatingGroup (Fin (5 + 2))) : Equiv.Perm (Fin (5 + 2))).IsThreeCycle →
      ((θ ⟨x, hx⟩ : alternatingGroup (Fin (5 + 2))) : Equiv.Perm (Fin (5 + 2))) 5 = 6 →
      ((θ ⟨x, hx⟩ : alternatingGroup (Fin (5 + 2))) : Equiv.Perm (Fin (5 + 2))) 6 = c →
      ((θ ⟨x, hx⟩ : alternatingGroup (Fin (5 + 2))) : Equiv.Perm (Fin (5 + 2))) c = 5 →
      ∀ n ∈ Y, x * n = n * x → ∀ u ∈ commV (Subgroup.zpowers x), n u = u := by
    intro x hx c hc5 hc6 h3 h56 h6c hc5' n hn hnx u hu
    have hl1 := conj_mem_conjClosure (Y := Y) (cfg.adm.hTG htT) hx
    have hconj : t * x * t⁻¹ = x⁻¹ := by
      have h1 : θ ⟨t * x * t⁻¹, hl1⟩ = (θ ⟨x, hx⟩)⁻¹ := by
        apply Subtype.ext
        rw [Subgroup.coe_inv]
        exact (hσ x hx).trans (swap_conj_three h3 (by decide) (Ne.symm hc5) (Ne.symm hc6)
          h56 h6c hc5')
      have h2 : θ ⟨t * x * t⁻¹, hl1⟩ = θ ⟨x⁻¹, inv_mem hx⟩ := by
        rw [h1, ← map_inv]
        rfl
      exact congrArg Subtype.val (θ.injective h2)
    have hord : orderOf x = 3 := by
      have h1 : orderOf ((θ ⟨x, hx⟩ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) = 3 :=
        h3.orderOf
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq] at h1
      rw [← h1]
      exact Subgroup.orderOf_coe (⟨x, hx⟩ : ↥(CGT6.conjClosure Y G))
    exact commV_zpowers_fix_of_inv ht2 hconj (by rw [hord]; decide) hnx.symm
      (fun w hw => hE hw n hn) u hu
  have hnatL : IsNatSectionWith (altAct (5 + 2)) θ (commV (CGT6.conjClosure Y G)) ⊥ :=
    rec418_gen (k := 5) hV (by decide) le_rfl θ (a := 5) (b := 6) (by decide) hYL hK θY hnat hC
      hVL hNtriv
  have hF : ({5, 6} : Finset (Fin (2 * 3 + 1))).card = (2 * 3 + 1) - (2 * 2 + 1) := by decide
  have hlift := natLift_holds V hV (CGT6.conjClosure Y G) Y 3 2 (by norm_num) (by norm_num)
    (by norm_num) θ hnatL {5, 6} hF hYL hK
  have hsub : ((CGT6.conjClosure Y G).subgroupOf G).IsSubnormal :=
    Subgroup.Normal.isSubnormal ((Subgroup.normal_subgroupOf_iff hLG).mpr
      fun h k hh hk => conj_mem_conjClosure hk hh)
  exact cfg.nolift ⟨CGT6.conjClosure Y G, hYL, hLG, hsub, Or.inl hlift⟩

end TypeA


section Conj

theorem map_conj_altStabilizer {m : ℕ} (ρ : Equiv.Perm (Fin m)) (F : Finset (Fin m)) :
    (altStabilizer m F).map (MulAut.conjNormal (H := alternatingGroup (Fin m))
      ρ).toMonoidHom = altStabilizer m (F.image ρ) := by
  ext a
  rw [mem_altStabilizer_iff, Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩ i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    rw [mem_altStabilizer_iff] at hh
    show (ρ * (h : Equiv.Perm (Fin m)) * ρ⁻¹) (ρ j) = ρ j
    simp [Equiv.Perm.mul_apply, hh j hj]
  · intro ha
    refine ⟨(MulAut.conjNormal (H := alternatingGroup (Fin m)) ρ⁻¹) a, ?_, ?_⟩
    · rw [mem_altStabilizer_iff]
      intro j hj
      show (ρ⁻¹ * (a : Equiv.Perm (Fin m)) * ρ⁻¹⁻¹) j = j
      have := ha (ρ j) (Finset.mem_image_of_mem ρ hj)
      simp [Equiv.Perm.mul_apply, this]
    · apply Subtype.ext
      show ρ * (ρ⁻¹ * (a : Equiv.Perm (Fin m)) * ρ⁻¹⁻¹) * ρ⁻¹ = a
      group

end Conj

section Normalize

variable [Finite V] {G T Y : Subgroup (MulAut V)}

theorem exists_normalized_pair (cfg : EndCfg4 G T Y) {m : ℕ}
    (e : LayerQ G Y ≃* alternatingGroup (Fin m)) {t : MulAut V} (htT : t ∈ T)
    {σ : Equiv.Perm (Fin m)}
    (hσ : ∀ (l : MulAut V) (hl : l ∈ CGT6.conjClosure Y G),
      ((piHom e ⟨t * l * t⁻¹, conj_mem_conjClosure (cfg.adm.hTG htT) hl⟩ :
        alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) = σ * ((piHom e ⟨l, hl⟩ :
          alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) * σ⁻¹)
    {p q p' q' : Fin m}
    (hH : (Y.subgroupOf (CGT6.conjClosure Y G)).map (piHom e) = altStabilizer m {p, q})
    (hσpq : σ = Equiv.swap p q) (ρ : Equiv.Perm (Fin m)) (hρp : ρ p = p') (hρq : ρ q = q') :
    ∃ e' : LayerQ G Y ≃* alternatingGroup (Fin m),
      (Y.subgroupOf (CGT6.conjClosure Y G)).map (piHom e') = altStabilizer m {p', q'} ∧
      ∀ (l : MulAut V) (hl : l ∈ CGT6.conjClosure Y G),
        ((piHom e' ⟨t * l * t⁻¹, conj_mem_conjClosure (cfg.adm.hTG htT) hl⟩ :
          alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) = Equiv.swap p' q' *
            ((piHom e' ⟨l, hl⟩ : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) *
              (Equiv.swap p' q')⁻¹ := by
  let c : alternatingGroup (Fin m) ≃* alternatingGroup (Fin m) :=
    MulAut.conjNormal (H := alternatingGroup (Fin m)) ρ
  refine ⟨e.trans c, ?_, ?_⟩
  · have h1 : piHom (e.trans c) = c.toMonoidHom.comp (piHom e) := MonoidHom.ext fun l => rfl
    rw [h1, ← Subgroup.map_map, hH]
    have h2 := map_conj_altStabilizer ρ {p, q}
    rw [Finset.image_insert, Finset.image_singleton, hρp, hρq] at h2
    exact h2
  · intro l hl
    have h1 : ∀ l' : ↥(CGT6.conjClosure Y G), piHom (e.trans c) l' = c (piHom e l') :=
      fun l' => rfl
    rw [h1, h1]
    show ρ * ((piHom e ⟨t * l * t⁻¹, _⟩ : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) * ρ⁻¹ = _
    rw [hσ l hl, hσpq]
    have h3 : Equiv.swap p' q' = ρ * Equiv.swap p q * ρ⁻¹ := by
      rw [← hρp, ← hρq]
      exact Equiv.swap_apply_apply ρ p q
    rw [h3]
    show _ = ρ * Equiv.swap p q * ρ⁻¹ * (ρ * ((piHom e ⟨l, hl⟩ : alternatingGroup (Fin m)) :
      Equiv.Perm (Fin m)) * ρ⁻¹) * (ρ * Equiv.swap p q * ρ⁻¹)⁻¹
    group

end Normalize

section Main

theorem end4Small_a7 : End4Small fun Q _ => Nonempty (Q ≃* alternatingGroup (Fin 7)) := by
  intro V _ _ hV G T Y cfg hY2 ⟨e⟩
  obtain ⟨t, htT, ht2, ht1⟩ := exists_involution_of_T cfg
  have htG : t ∈ G := cfg.adm.hTG htT
  obtain ⟨σ, hσ⟩ := exists_sigma (m := 7) (by norm_num) (by norm_num) e htG
  have hσ1 := sigma_ne_one cfg e htG ht2 ht1 hσ
  have := isSimpleGroup_piY hY2 e
  obtain ⟨p, q, hpq, hHpq, hσpq⟩ :=
    a7_config _ (card_piY hY2 e) σ hσ1 (sigma_comm cfg e htT hσ)
  obtain ⟨ρ, hρp, hρq⟩ := exists_perm_pair p q hpq
  obtain ⟨e', hH', hσ'⟩ := exists_normalized_pair cfg e htT hσ hHpq hσpq ρ hρp hρq
  have hX : InClassX ↥(yuHol Y) := by
    rcases cfg.hcls2 with h | ⟨n, hn, hΩ⟩
    · exact h
    · exfalso
      have := not_natOmegaMinus_of_ysl (f := 2) (n := n) (by norm_num) (by omega) hY2 hΩ
      omega
  rcases natSection_of_classX hV cfg.adm.hperf hX le_rfl hY2 with hS | ⟨-, hA⟩
  · exact a7_typeS_false hV cfg hY2 e' htT ht2 ht1 hH' hσ' hS
  · exact a7_typeA_false hV cfg e' htT ht2 hH' hσ' hA

end Main

end CFSG.CGT.PushingUpLit.CGT6X.End4
