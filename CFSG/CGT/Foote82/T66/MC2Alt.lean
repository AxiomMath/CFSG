module

public import CFSG.CGT.Foote82.T66.CitedMC2
public import CFSG.CGT.Foote82.T66.MC2Lin
import CFSG.CGT.Foote82.T66.MC2Perm
import CFSG.CGT.Foote82.T66.MC2Quot
import CFSG.CGT.Foote82.T66.MC2Arith
import CFSG.LocalAnalysis.ComponentInitial.DerivedFixedLayer
import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI
import CFSG.RankThree.PartTwo.Sec19.SimsItem316SmallModels
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerBasic

public section

namespace CFSG.CGT.Foote82

namespace MC2

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem injective_of_isSimpleGroup {A T : Type*} [Group A] [IsSimpleGroup A] [Group T]
    [Nontrivial T]
    (α : A →* T) (hα : Function.Surjective α) : Function.Injective α := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal α.ker with h | h
  · exact (MonoidHom.ker_eq_bot_iff α).1 h
  · exfalso
    obtain ⟨t, ht⟩ := exists_ne (1 : T)
    obtain ⟨a, rfl⟩ := hα t
    exact ht ((MonoidHom.mem_ker).1 (h ▸ Subgroup.mem_top a))

theorem nontrivial_alt {n : ℕ} (hn : 3 ≤ n) : Nontrivial (alternatingGroup (Fin n)) :=
  alternatingGroup.nontrivial_of_three_le_card (by simpa using hn)

theorem factorial_div_two_inj {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (h : a.factorial / 2 = b.factorial / 2) : a = b := by
  have h2a : 2 ∣ a.factorial := Nat.dvd_factorial (by norm_num) ha
  have h2b : 2 ∣ b.factorial := Nat.dvd_factorial (by norm_num) hb
  have : a.factorial = b.factorial := by
    obtain ⟨x, hx⟩ := h2a
    obtain ⟨y, hy⟩ := h2b
    rw [hx, hy] at h ⊢
    simp at h
    rw [h]
  exact (Nat.factorial_inj (by omega)).1 this

section Transport

variable {G : Subgroup (GLV V)} {m : ℕ} (ψ : ↥G ≃* alternatingGroup (Fin m))

abbrev iota : ↥G →* Equiv.Perm (Fin m) := (alternatingGroup (Fin m)).subtype.comp ψ.toMonoidHom

theorem iota_injective : Function.Injective (iota ψ) :=
  (alternatingGroup (Fin m)).subtype_injective.comp ψ.injective

theorem iota_mem (g : ↥G) : iota ψ g ∈ alternatingGroup (Fin m) := (ψ g).2

theorem iota_symm {σ : Equiv.Perm (Fin m)} (hσ : σ ∈ alternatingGroup (Fin m)) :
    iota ψ (ψ.symm ⟨σ, hσ⟩) = σ := by
  simp

abbrev img (H : Subgroup (GLV V)) : Subgroup (Equiv.Perm (Fin m)) := (H.subgroupOf G).map (iota ψ)

theorem mem_img {H : Subgroup (GLV V)} {σ : Equiv.Perm (Fin m)} :
    σ ∈ img ψ H ↔ ∃ g : ↥G, (g : GLV V) ∈ H ∧ iota ψ g = σ := by
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem img_inf_centralizer (t : ↥G) :
    img ψ (G ⊓ Subgroup.centralizer ({(t : GLV V)} : Set (GLV V))) =
      alternatingGroup (Fin m) ⊓ Subgroup.centralizer ({iota ψ t} : Set (Equiv.Perm (Fin m))) := by
  ext σ
  rw [mem_img]
  constructor
  · rintro ⟨g, ⟨-, hg⟩, rfl⟩
    refine ⟨iota_mem ψ g, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have hc : (g : GLV V) * t = t * g := Subgroup.mem_centralizer_singleton_iff.1 hg
    have hc' : g * t = t * g := Subtype.ext hc
    rw [← map_mul, ← map_mul, hc']
  · rintro ⟨hA, hc⟩
    refine ⟨ψ.symm ⟨σ, hA⟩, ⟨(ψ.symm ⟨σ, hA⟩).2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩,
      iota_symm ψ hA⟩
    have hc' : iota ψ (ψ.symm ⟨σ, hA⟩ * t) = iota ψ (t * ψ.symm ⟨σ, hA⟩) := by
      rw [map_mul, map_mul, iota_symm]
      exact Subgroup.mem_centralizer_singleton_iff.1 hc
    exact congrArg Subtype.val (iota_injective ψ hc')

theorem isComponentOf_img {L K : Subgroup (GLV V)} (hL : L ≤ G) (hK : K ≤ G)
    (h : IsComponentOf L K) : IsComponentOf (img ψ L) (img ψ K) := by
  rw [← CFSG.Assembly.isComponentOf_iff_open] at h ⊢
  have h' : CFSG.Assembly.IsComponentOf (L.subgroupOf G) (K.subgroupOf G) := by
    rw [← CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff G.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hL, Subgroup.map_subgroupOf_eq_of_le hK]
    exact h
  exact (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff (iota_injective ψ)).2 h'

end Transport

theorem tight_false {G L : Subgroup (GLV V)} {s : GLV V} (h : StdForm G L s) (hLG : L ≤ G)
    {m : ℕ} (ψ : ↥G ≃* alternatingGroup (Fin m)) {F : Set (Fin m)} (himg : img ψ L = altOn F)
    {g' u' : Equiv.Perm (Fin m)} (hg' : g' ∈ alternatingGroup (Fin m))
    (hu' : u' ∈ alternatingGroup (Fin m)) (hu2 : orderOf u' = 2) (hufix : ∀ z ∈ F, u' z = z)
    (hgu : g' * u' = u' * g') {σ : Equiv.Perm (Fin m)} (hσ : σ ∈ altOn F)
    (hσg : g' * σ * g'⁻¹ ∉ altOn F) : False := by
  set g : ↥G := ψ.symm ⟨g', hg'⟩ with hg
  set u : ↥G := ψ.symm ⟨u', hu'⟩ with hu
  have hιg : iota ψ g = g' := iota_symm ψ hg'
  have hιu : iota ψ u = u' := iota_symm ψ hu'
  have hgN : (g : GLV V) ∉ Subgroup.normalizer (L : Set (GLV V)) := by
    intro hN
    rw [← himg] at hσ hσg
    obtain ⟨ℓ, hℓL, rfl⟩ := (mem_img ψ).1 hσ
    apply hσg
    refine (mem_img ψ).2 ⟨g * ℓ * g⁻¹, ?_, by rw [map_mul, map_mul, map_inv, hιg]⟩
    exact (Subgroup.mem_normalizer_iff.1 hN ℓ).1 hℓL
  have huL : (u : GLV V) ∈ Subgroup.centralizer (L : Set (GLV V)) := by
    refine Subgroup.mem_centralizer_iff.2 fun ℓ hℓ => ?_
    have hℓ' : iota ψ ⟨ℓ, hLG hℓ⟩ ∈ altOn F := himg ▸ (mem_img ψ).2 ⟨⟨ℓ, hLG hℓ⟩, hℓ, rfl⟩
    have hc := commute_of_fix hufix hℓ'
    have : (⟨ℓ, hLG hℓ⟩ : ↥G) * u = u * ⟨ℓ, hLG hℓ⟩ := by
      apply iota_injective ψ
      rw [map_mul, map_mul, hιu, hc]
    exact congrArg Subtype.val this
  have hgu' : g * u = u * g := by
    apply iota_injective ψ
    rw [map_mul, map_mul, hιg, hιu, hgu]
  have huK : (u : GLV V) ∈ G ⊓ Subgroup.centralizer (L : Set (GLV V)) := ⟨u.2, huL⟩
  have hug : (u : GLV V) ∈ (G ⊓ Subgroup.centralizer (L : Set (GLV V))).map
      (MulAut.conj (g : GLV V)).toMonoidHom := by
    refine ⟨u, huK, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have : (g : GLV V) * u = u * g := congrArg Subtype.val hgu'
    rw [this, mul_inv_cancel_right]
  have ho : orderOf (u : GLV V) = 2 := by
    rw [Subgroup.orderOf_coe, ← orderOf_injective (iota ψ) (iota_injective ψ) u, hιu, hu2]
  have hev := CFSG.StandardSubgroupAPI.even_card_of_mem_of_orderOf_eq_two
    (Q := (G ⊓ Subgroup.centralizer (L : Set (GLV V))) ⊓
      (G ⊓ Subgroup.centralizer (L : Set (GLV V))).map (MulAut.conj (g : GLV V)).toMonoidHom)
    ⟨huK, hug⟩ ho
  exact (Nat.not_even_iff_odd.2 (h.tight g g.2 hgN)) hev

structure AltData (G L : Subgroup (GLV V)) {m : ℕ} (ψ : ↥G ≃* alternatingGroup (Fin m))
    (F : Set (Fin m)) : Prop where
  le : L ≤ G
  img_eq : img ψ L = altOn F
  card_add : F.ncard + 4 = m
  five_le : 5 ≤ F.ncard

theorem altSetup {G L : Subgroup (GLV V)} {s : GLV V} (h : StdForm G L s)
    (h4 : 4 ∣ Nat.card ↥(G ⊓ Subgroup.centralizer (L : Set (GLV V)))) {m : ℕ}
    (ψ : ↥G ≃* alternatingGroup (Fin m)) : ∃ F : Set (Fin m), AltData G L ψ F := by
  have hLG : L ≤ G := stdForm_L_le h
  have hev : Even (Nat.card ↥(G ⊓ Subgroup.centralizer (L : Set (GLV V)))) :=
    even_iff_two_dvd.2 ((by norm_num : 2 ∣ 4).trans h4)
  obtain ⟨t, htK, ht2⟩ := CFSG.StandardSubgroupAPI.exists_mem_orderOf_eq_two_of_even hev
  have hcompt := h.component_of_inv t htK.1 ht2 htK.2
  set t' : ↥G := ⟨t, htK.1⟩ with ht'
  set σt := iota ψ t' with hσt
  have hcomp : IsComponentOf (img ψ L)
      (alternatingGroup (Fin m) ⊓ Subgroup.centralizer ({σt} : Set (Equiv.Perm (Fin m)))) := by
    rw [hσt, ← img_inf_centralizer ψ t']
    exact isComponentOf_img ψ hLG inf_le_left hcompt
  have hσt2 : orderOf σt = 2 := by
    rw [hσt, orderOf_injective (iota ψ) (iota_injective ψ) t', Subgroup.orderOf_mk, ht2]
  have hR : IsPGroup 2 (Subgroup.zpowers σt) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hσt2, pow_one])
  have hCR : Subgroup.centralizer ((Subgroup.zpowers σt : Subgroup (Equiv.Perm (Fin m))) :
      Set (Equiv.Perm (Fin m))) = Subgroup.centralizer ({σt} : Set (Equiv.Perm (Fin m))) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  obtain ⟨h5, hLeq⟩ := eq_altOn_of_isComponentOf hR (by rw [hCR]) (by rw [hCR]; exact inf_le_right)
    hcomp
  set F : Set (Fin m) := {i | ∀ r ∈ Subgroup.zpowers σt, r i = i} with hF
  have hFc : Fᶜ = (σt.support : Set (Fin m)) := by
    ext i
    simp only [hF, Set.mem_compl_iff, Set.mem_setOf_eq, Finset.mem_coe, Equiv.Perm.mem_support]
    constructor
    · intro hi hσi
      apply hi
      intro r hr
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hr
      exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hσi k
    · intro hσi hi
      exact hσi (hi σt (Subgroup.mem_zpowers σt))
  have h5F : 5 ≤ F.ncard := by
    rw [← Nat.card_coe_set_eq]
    exact h5
  have hc4 : 4 ≤ Fᶜ.ncard := by
    rw [hFc, Set.ncard_coe_finset]
    exact four_le_card_support hσt2 (iota_mem ψ t')
  have hc4' : Fᶜ.ncard ≤ 4 := by
    by_contra hlt
    obtain ⟨g', hg', u', hu', hu2, hufix, hgu, σ, hσ, hσg⟩ :=
      exists_tight_witness h5F (by omega)
    exact tight_false h hLG ψ hLeq hg' hu' hu2 hufix hgu hσ hσg
  have hsum := Set.ncard_add_ncard_compl F
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hsum
  exact ⟨F, ⟨hLG, hLeq, by omega, h5F⟩⟩

namespace AltData

variable {G L : Subgroup (GLV V)} {m : ℕ} {ψ : ↥G ≃* alternatingGroup (Fin m)}
  {F : Set (Fin m)}

abbrev jL (hd : AltData G L ψ F) : ↥L →* Equiv.Perm (Fin m) :=
  (iota ψ).comp (Subgroup.inclusion hd.le)

theorem jL_injective (hd : AltData G L ψ F) : Function.Injective hd.jL :=
  (iota_injective ψ).comp (Subgroup.inclusion_injective hd.le)

theorem jL_mem (hd : AltData G L ψ F) (ℓ : ↥L) : hd.jL ℓ ∈ altOn F := by
  rw [← hd.img_eq]
  exact (mem_img ψ).2 ⟨Subgroup.inclusion hd.le ℓ, ℓ.2, rfl⟩

theorem exists_jL_eq (hd : AltData G L ψ F) {σ : Equiv.Perm (Fin m)} (hσ : σ ∈ altOn F) :
    ∃ ℓ : ↥L, hd.jL ℓ = σ := by
  rw [← hd.img_eq] at hσ
  obtain ⟨g, hgL, rfl⟩ := (mem_img ψ).1 hσ
  exact ⟨⟨g, hgL⟩, rfl⟩

@[expose] noncomputable def mulEquiv (hd : AltData G L ψ F) : ↥L ≃* ↥(altOn F) :=
  MulEquiv.ofBijective (hd.jL.codRestrict _ hd.jL_mem)
    ⟨fun a b hab => by
      have h' := congrArg Subtype.val hab
      simp only [MonoidHom.codRestrict_apply] at h'
      exact hd.jL_injective h', fun σ => by
      obtain ⟨ℓ, hℓ⟩ := hd.exists_jL_eq σ.2
      exact ⟨ℓ, Subtype.ext hℓ⟩⟩

theorem coe_mulEquiv (hd : AltData G L ψ F) (ℓ : ↥L) :
    ((hd.mulEquiv ℓ : ↥(altOn F)) : Equiv.Perm (Fin m)) = hd.jL ℓ :=
  rfl

theorem card_L (hd : AltData G L ψ F) : Nat.card ↥L = F.ncard.factorial / 2 := by
  rw [Nat.card_congr hd.mulEquiv.toEquiv, card_altOn (by have := hd.five_le; omega)]

theorem isSimpleGroup (hd : AltData G L ψ F) : IsSimpleGroup ↥L := by
  have := isSimpleGroup_altOn hd.five_le
  exact hd.mulEquiv.isSimpleGroup

theorem card_eq_of_surjective (hd : AltData G L ψ F) {T : Type*} [Group T] [Nontrivial T]
    (α : ↥L →* T) (hα : Function.Surjective α) : F.ncard.factorial / 2 = Nat.card T := by
  have := hd.isSimpleGroup
  rw [← hd.card_L]
  exact Nat.card_congr (Equiv.ofBijective α ⟨injective_of_isSimpleGroup α hα, hα⟩)

end AltData

theorem isAltNaturalModule_of_omegaPlus_three {L : Subgroup (GLV V)}
    (h : IsOmegaPlusModule L 3) : IsAltNaturalModule L 8 := by
  obtain ⟨φ, ψ, hψ⟩ := CFSG.RankThree.PartTwo.Sec19.SimsItem316Small.omegaPlusTwo_three_model
  obtain ⟨α, hα, β, hβ, hker, hR⟩ := h
  refine ⟨φ.toMonoidHom.comp α, φ.surjective.comp hα, ψ.toAddMonoidHom.comp β,
    ψ.surjective.comp hβ, ?_, ?_⟩
  · rw [← hker]
    ext w
    simp
  · intro ℓ w w' hw x hx
    have := hR ℓ w w' hw
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
      MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom] at hx ⊢
    rw [this]
    exact hψ (α ℓ) (β w) x hx

theorem case_omegaMinus {G L : Subgroup (GLV V)} {m : ℕ} {ψ : ↥G ≃* alternatingGroup (Fin m)}
    {F : Set (Fin m)} (hd : AltData G L ψ F) {k : ℕ} (hk : k = 2 ∨ k = 3)
    (hO : IsOmegaMinusModule L k) : False := by
  obtain ⟨α, hα, -⟩ := hO
  have : Nontrivial ↥(omegaMinusTwo k) := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    rcases hk with rfl | rfl
    · rw [card_omegaMinusTwo_two]; norm_num
    · rw [card_omegaMinusTwo_three]; norm_num
  exact factorial_div_two_ne_card_omegaMinusTwo hk (hd.card_eq_of_surjective α hα)

theorem case_a6z3 (h6 : A6NoSixDimIrr) {G L : Subgroup (GLV V)} {s : GLV V} (h : StdForm G L s)
    {m : ℕ} {ψ : ↥G ≃* alternatingGroup (Fin m)} {F : Set (Fin m)} (hd : AltData G L ψ F)
    (hA : IsA6Z3Module L) : False := by
  obtain ⟨⟨α, hα⟩, hdim⟩ := hA
  have := hd.isSimpleGroup
  have : Nontrivial (alternatingGroup (Fin 6)) := nontrivial_alt (by norm_num)
  have hinj := rhoT_injective h.extremal.faithful
  let e₁ : ↥L ≃* ↥(rhoT L).range := MonoidHom.ofInjective hinj
  let e₂ : ↥L ≃* alternatingGroup (Fin 6) :=
    MulEquiv.ofBijective α ⟨injective_of_isSimpleGroup α hα, hα⟩
  exact h6 (TildeV L) (rhoT L).range ⟨e₁.symm.trans e₂⟩
    (isIrr_range_rhoT h.extremal.setup.irrTilde) hdim

end MC2

end CFSG.CGT.Foote82
