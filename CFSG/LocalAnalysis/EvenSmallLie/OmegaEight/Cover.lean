module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.CoverBound
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.CoverCore
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeBridge

public noncomputable section

namespace CFSG.EvenSmallLie.OmegaEight.Cover

open Subgroup CFSG.RankThree.PerfectCover CFSG.LieType.Multipliers

theorem rhoT_eq : rhoT = gen 8 :=
  Equiv.ext fun q => Fin.ext (by rw [gen8_val]; rfl)

theorem gen8_cube (g : Equiv.Perm (Fin 360)) :
    gen 8 * (gen 8 * (gen 8 * g * (gen 8)⁻¹) * (gen 8)⁻¹) * (gen 8)⁻¹ = g := by
  have h3 : gen 8 * gen 8 * gen 8 = 1 := Equiv.ext fun q => Fin.ext (by
    simp only [Equiv.Perm.mul_apply, gen8_val, Equiv.Perm.one_apply]
    omega)
  calc _ = (gen 8 * gen 8 * gen 8) * g * (gen 8 * gen 8 * gen 8)⁻¹ := by group
    _ = g := by rw [h3, one_mul, inv_one, mul_one]

@[expose] def triality : omegaT →* omegaT :=
  ((MulAut.conj (gen 8)).toMonoidHom.comp omegaT.subtype).codRestrict omegaT fun g =>
    conj_mem_omegaT_of_gen (Or.inl rfl) g.2

theorem coe_triality (g : omegaT) :
    (triality g : Equiv.Perm (Fin 360)) = gen 8 * g * (gen 8)⁻¹ := by
  show (MulAut.conj (gen 8)) (g : Equiv.Perm (Fin 360)) = _
  exact MulAut.conj_apply _ _

theorem triality_cube
    (g : omegaT) : triality (triality (triality g)) = g :=
  Subtype.ext (by simp only [coe_triality]; exact gen8_cube _)

theorem triality_surjective
    : Function.Surjective triality := fun g =>
  ⟨triality (triality g), triality_cube g⟩

theorem triality_injective
    : Function.Injective triality := fun g h hgh => by
  rw [← triality_cube g, ← triality_cube h, hgh]

abbrev U : Type := HopfCover omegaT

abbrev piU : U →* omegaT := hopfCoverMap omegaT

@[expose] def piTwo
    : U →* omegaT := (triality.comp triality).comp piU

instance :
    Group.IsPerfect omegaT := isPerfect_omegaT

theorem piTwo_surjective :
    Function.Surjective piTwo :=
  (triality_surjective.comp triality_surjective).comp hopfCoverMap_surjective

theorem piTwo_ker : piTwo.ker = piU.ker := by
  ext u
  simp only [MonoidHom.mem_ker, piTwo, MonoidHom.comp_apply]
  exact ⟨fun h => triality_injective (triality_injective (by rw [h, map_one, map_one])),
    fun h => by rw [h, map_one, map_one]⟩

@[expose] def tauHat :
    U →* U :=
  hopfLift piTwo piTwo_surjective (piTwo_ker ▸ hopfMultiplier_le_center)

theorem piTwo_ker_le : piTwo.ker ≤ center U := by
  rw [piTwo_ker]
  exact hopfMultiplier_le_center

theorem tauHat_eq
    : tauHat = hopfLift piTwo piTwo_surjective piTwo_ker_le := rfl

theorem piU_tauHat
    (u : U) : piU (tauHat u) = triality (piU u) := by
  have h := DFunLike.congr_fun (comp_hopfLift piTwo piTwo_surjective piTwo_ker_le) u
  rw [MonoidHom.comp_apply, ← tauHat_eq, piTwo, MonoidHom.comp_apply,
    MonoidHom.comp_apply] at h
  rw [← h, triality_cube]

theorem tauHat_cube
    (u : U) : tauHat (tauHat (tauHat u)) = u := by
  have h := hopfCover_hom_ext piU hopfMultiplier_le_center (tauHat.comp (tauHat.comp tauHat))
    (MonoidHom.id U) (MonoidHom.ext fun u => by
      simp only [MonoidHom.comp_apply, piU_tauHat, triality_cube])
    (MonoidHom.comp_id _)
  exact DFunLike.congr_fun h u

@[expose] def tauEquiv :
    U ≃* U :=
  { tauHat with
    invFun := fun u => tauHat (tauHat u)
    left_inv := tauHat_cube
    right_inv := tauHat_cube }

theorem tauEquiv_apply
    (u : U) : tauEquiv u = tauHat u := rfl

@[expose] def rhoU
    : U →* Equiv.Perm (Fin 240) := rhoHom.comp coverEquiv.symm.toMonoidHom

@[expose] def wordU
    (w : List (Fin 4 × Bool)) : U :=
  coverEquiv (PresentedGroup.mk _ (FreeGroup.mk w))

theorem rhoU_wordU
    (w : List (Fin 4 × Bool)) : rhoU (wordU w) = rhoWord w := by
  rw [rhoU, wordU, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  exact rhoHom_mk w

theorem coe_piU_wordU
    (w : List (Fin 4 × Bool)) :
    (piU (wordU w) : Equiv.Perm (Fin 360)) = word w := by
  rw [wordU, hopfCoverMap_coverEquiv, coverMap_mk]
  exact coe_lift_gensX_mk w

theorem rho_facts
    : rhoWord uWord * rhoWord uWord = 1 ∧ rhoWord tuWord * rhoWord tuWord ≠ 1 := by
  have h := rho_check
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not] at h
  exact ⟨h.1.2, h.2⟩

theorem sq_wordU_mem :
    wordU uWord ^ 2 ∈ piU.ker := by
  rw [MonoidHom.mem_ker, map_pow]
  refine Subtype.ext ?_
  rw [SubgroupClass.coe_pow, coe_piU_wordU, sq, model_facts.2.2.2.1]
  rfl

theorem inv_mul_tauEquiv_mem :
    (wordU tuWord)⁻¹ * tauEquiv (wordU uWord) ∈ piU.ker := by
  rw [MonoidHom.mem_ker, map_mul, map_inv, tauEquiv_apply, piU_tauHat, inv_mul_eq_one]
  refine Subtype.ext ?_
  rw [coe_triality, coe_piU_wordU, coe_piU_wordU, model_facts.2.2.2.2, rhoT_eq]

theorem tauEquiv_mem
    {m : U} (hm : m ∈ piU.ker) : tauEquiv m ∈ piU.ker := by
  rw [MonoidHom.mem_ker] at hm ⊢
  rw [tauEquiv_apply, piU_tauHat, hm, map_one]

theorem nonempty_quotient_mulEquiv_U
    {K K' : Subgroup U} [K.Normal] [K'.Normal]
    (hK : K ≤ piU.ker) (hK' : K' ≤ piU.ker) (hKc : Nat.card piU.ker = 2 * Nat.card K)
    (hK'c : Nat.card piU.ker = 2 * Nat.card K') : Nonempty (U ⧸ K ≃* U ⧸ K') := by
  obtain ⟨hfin, h4⟩ := card_hopfMultiplier_le
  exact nonempty_quotient_mulEquiv hopfMultiplier_le_center h4 tauEquiv tauHat_cube
    (fun _ => tauEquiv_mem) rhoU sq_wordU_mem inv_mul_tauEquiv_mem
    (by rw [rhoU_wordU, sq]; exact rho_facts.1) (by rw [rhoU_wordU, sq]; exact rho_facts.2)
    hK hK' hKc hK'c

section Extension

variable
    {E : Type*} [Group E] [Group.IsPerfect E] (q : E →* omegaT)
  (hq : Function.Surjective q) (hker : q.ker ≤ center E)

omit [Group.IsPerfect E] in
theorem ker_hopfLift_le : (hopfLift q hq hker).ker ≤ piU.ker := fun u hu => by
  rw [MonoidHom.mem_ker] at hu ⊢
  rw [show piU u = q (hopfLift q hq hker u) from
    (DFunLike.congr_fun (comp_hopfLift q hq hker) u).symm, hu, map_one]

theorem card_ker_piU_eq (h2 : Nat.card q.ker = 2) :
    Nat.card piU.ker = 2 * Nat.card (hopfLift q hq hker).ker := by
  set f := (hopfLift q hq hker).domRestrict piU.ker
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, MonoidHom.domRestrict_range,
    map_hopfMultiplier_hopfLift, h2, MonoidHom.ker_domRestrict,
    Nat.card_congr (subgroupOfEquivOfLe (ker_hopfLift_le q hq hker)).toEquiv] at h1
  exact h1

def mulEquivQuotient : U ⧸ (hopfLift q hq hker).ker ≃* E :=
  QuotientGroup.quotientKerEquivOfSurjective _ (hopfLift_surjective q hq hker)

end Extension

theorem nonempty_mulEquiv_of_double_covers_omegaT
    {E E' : Type*} [Group E] [Group E']
    [Group.IsPerfect E] [Group.IsPerfect E'] (q : E →* omegaT) (hq : Function.Surjective q)
    (hker : q.ker ≤ center E) (h2 : Nat.card q.ker = 2) (q' : E' →* omegaT)
    (hq' : Function.Surjective q') (hker' : q'.ker ≤ center E') (h2' : Nat.card q'.ker = 2) :
    Nonempty (E ≃* E') := by
  obtain ⟨φ⟩ := nonempty_quotient_mulEquiv_U (ker_hopfLift_le q hq hker)
    (ker_hopfLift_le q' hq' hker') (card_ker_piU_eq q hq hker h2)
    (card_ker_piU_eq q' hq' hker' h2')
  exact ⟨((mulEquivQuotient q hq hker).symm.trans φ).trans (mulEquivQuotient q' hq' hker')⟩

theorem ker_comp_mulEquiv {E X Y : Type*} [Group E] [Group X] [Group Y] (q : E →* X)
    (e : X ≃* Y) : (e.toMonoidHom.comp q).ker = q.ker := by
  ext x
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff]

theorem nonempty_mulEquiv_of_double_covers
    {X X' : Type} [Group X] [Group X']
    (hX : CFSG.Blueprint.LieModel X .POmegaPlus 4 2 1)
    (hX' : CFSG.Blueprint.LieModel X' .POmegaPlus 4 2 1) {E E' : Type*} [Group E] [Group E']
    [Group.IsPerfect E] [Group.IsPerfect E'] (q : E →* X) (hq : Function.Surjective q)
    (hker : q.ker ≤ center E) (h2 : Nat.card q.ker = 2) (q' : E' →* X')
    (hq' : Function.Surjective q') (hker' : q'.ker ≤ center E') (h2' : Nat.card q'.ker = 2) :
    Nonempty (E ≃* E') := by
  obtain ⟨e⟩ := nonempty_mulEquiv_omegaT hX
  obtain ⟨e'⟩ := nonempty_mulEquiv_omegaT hX'
  rw [← ker_comp_mulEquiv q e] at hker h2
  rw [← ker_comp_mulEquiv q' e'] at hker' h2'
  exact nonempty_mulEquiv_of_double_covers_omegaT _ (e.surjective.comp hq) hker h2 _
    (e'.surjective.comp hq') hker' h2'

theorem omega8plus_double_cover_unique
    (L₁ L₂ : Type) [Group L₁] [Group L₂]
    (hL₁ : commutator L₁ = ⊤) (hL₂ : commutator L₂ = ⊤) (hZ₁ : Nat.card (center L₁) = 2)
    (hZ₂ : Nat.card (center L₂) = 2)
    (hX₁ : CFSG.Blueprint.LieModel (L₁ ⧸ center L₁) .POmegaPlus 4 2 1)
    (hX₂ : CFSG.Blueprint.LieModel (L₂ ⧸ center L₂) .POmegaPlus 4 2 1) :
    ∃ θ : L₁ ≃* L₂, (center L₁).map θ.toMonoidHom = center L₂ := by
  have : Group.IsPerfect L₁ := ⟨hL₁⟩
  have : Group.IsPerfect L₂ := ⟨hL₂⟩
  obtain ⟨θ⟩ := nonempty_mulEquiv_of_double_covers hX₁ hX₂ (QuotientGroup.mk' (center L₁))
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _).le
    (by rw [QuotientGroup.ker_mk', hZ₁]) (QuotientGroup.mk' (center L₂))
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _).le
    (by rw [QuotientGroup.ker_mk', hZ₂])
  exact ⟨θ, map_center_eq θ⟩

theorem eq_of_card_eq_two {G : Type*} [Group G] {S : Subgroup G} (hS : Nat.card S = 2)
    {a b : G} (ha : a ∈ S) (ha1 : a ≠ 1) (hb : b ∈ S) (hb1 : b ≠ 1) : a = b := by
  have : Finite S := Nat.finite_of_card_ne_zero (by omega)
  by_contra hab
  have h := length_le_card (M := S) (l := [1, a, b]) (by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
        not_or, and_true, not_false_eq_true]
      exact ⟨⟨ha1.symm, hb1.symm⟩, hab⟩) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro g (rfl | rfl | rfl)
      exacts [S.one_mem, ha, hb])
  simp only [List.length_cons, List.length_nil] at h
  omega

theorem omega8plus_double_cover_unique_of_mem_center
    (L₁ L₂ : Type) [Group L₁] [Group L₂]
    (hL₁ : commutator L₁ = ⊤) (hL₂ : commutator L₂ = ⊤) (hZ₁ : Nat.card (center L₁) = 2)
    (hZ₂ : Nat.card (center L₂) = 2)
    (hX₁ : CFSG.Blueprint.LieModel (L₁ ⧸ center L₁) .POmegaPlus 4 2 1)
    (hX₂ : CFSG.Blueprint.LieModel (L₂ ⧸ center L₂) .POmegaPlus 4 2 1) {t₁ : L₁} {t₂ : L₂}
    (ht₁ : t₁ ∈ center L₁) (ht₁' : t₁ ≠ 1) (ht₂ : t₂ ∈ center L₂) (ht₂' : t₂ ≠ 1) :
    ∃ θ : L₁ ≃* L₂, θ t₁ = t₂ := by
  obtain ⟨θ, hθ⟩ := omega8plus_double_cover_unique L₁ L₂ hL₁ hL₂ hZ₁ hZ₂ hX₁ hX₂
  refine ⟨θ, eq_of_card_eq_two hZ₂ ?_ ?_ ht₂ ht₂'⟩
  · rw [← hθ]
    exact mem_map_of_mem _ ht₁
  · rwa [ne_eq, MulEquiv.map_eq_one_iff]

theorem center_omegaT :
    center omegaT = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  have hc : (g : Equiv.Perm (Fin 360)) ∈
      Subgroup.centralizer (omegaT : Set (Equiv.Perm (Fin 360))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact congrArg Subtype.val (mem_center_iff.1 hg ⟨h, hh⟩)
  rw [centralizer_omegaT, mem_bot] at hc
  exact mem_bot.2 (Subtype.ext hc)

theorem center_eq_ker_of_lieModel
    {W : Type*} [Group W] {Y : Type} [Group Y]
    (hY : CFSG.Blueprint.LieModel Y .POmegaPlus 4 2 1) (p : W →* Y) (hp : Function.Surjective p)
    (hpker : p.ker ≤ center W) : center W = p.ker := by
  obtain ⟨e⟩ := nonempty_mulEquiv_omegaT hY
  refine le_antisymm (fun c hc => ?_) hpker
  rw [MonoidHom.mem_ker]
  have h1 : e (p c) ∈ center omegaT := by
    rw [mem_center_iff]
    intro g
    obtain ⟨w, hw⟩ := hp (e.symm g)
    rw [show g = e (p w) by rw [hw, MulEquiv.apply_symm_apply], ← map_mul, ← map_mul, ← map_mul,
      ← map_mul, mem_center_iff.1 hc w]
  rwa [center_omegaT, mem_bot, MulEquiv.map_eq_one_iff] at h1

theorem omega8plus_double_cover_mulEquiv
    (L : Type) [Group L] (hL : commutator L = ⊤)
    (hZ : Nat.card (center L) = 2)
    (hX : CFSG.Blueprint.LieModel (L ⧸ center L) .POmegaPlus 4 2 1) {W : Type*} [Group W]
    [Group.IsPerfect W] {Y : Type} [Group Y] (hY : CFSG.Blueprint.LieModel Y .POmegaPlus 4 2 1)
    (p : W →* Y) (hp : Function.Surjective p) (hpker : p.ker ≤ center W)
    (hp2 : Nat.card p.ker = 2) : ∃ θ : L ≃* W, (center L).map θ.toMonoidHom = p.ker := by
  have : Group.IsPerfect L := ⟨hL⟩
  obtain ⟨θ⟩ := nonempty_mulEquiv_of_double_covers hX hY (QuotientGroup.mk' (center L))
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _).le
    (by rw [QuotientGroup.ker_mk', hZ]) p hp hpker hp2
  exact ⟨θ, (map_center_eq θ).trans (center_eq_ker_of_lieModel hY p hp hpker)⟩

end CFSG.EvenSmallLie.OmegaEight.Cover
