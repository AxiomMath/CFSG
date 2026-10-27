module

public import CFSG.CGT.PushingUpLit.CGT6.OmegaPlusKb
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.CGT.PushingUpLit.CGT6.OmegaPlus

open CFSG CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {V : Type} [CommGroup V]

theorem card_sup_eq_mul_of_inf_eq_bot (A B : Subgroup V) (h : A ⊓ B = ⊥) :
    Nat.card ↥(A ⊔ B) = Nat.card ↥A * Nat.card ↥B :=
  CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer A B
    (by rw [CommGroup.normalizer_eq_top]; exact le_top) (disjoint_iff.mpr h)

theorem card_fixV_conj (x t : MulAut V) :
    Nat.card ↥(fixV (Subgroup.zpowers (x * t * x⁻¹))) = Nat.card ↥(fixV (Subgroup.zpowers t)) :=
  CFSG.Quasithin.card_fixV_zpowers_conj x t

theorem card_fixV_lt [Finite V] {U W : Subgroup V} (hsup : W ⊔ U = ⊤) (hinf : W ⊓ U = ⊥)
    {t k : MulAut V} (htU : ∀ u ∈ U, t u = u) (htW : ∀ w ∈ W, t w ∈ W)
    (hkW : ∀ w ∈ W, k w = w) (hkU : ∀ u ∈ U, k u ∈ U) (hk : ∃ u ∈ U, k u ≠ u) :
    Nat.card ↥(fixV (Subgroup.zpowers (t * k))) < Nat.card ↥(fixV (Subgroup.zpowers t)) := by
  have hdec : ∀ v : V, ∃ w ∈ W, ∃ u ∈ U, w * u = v := by
    intro v
    have : v ∈ W ⊔ U := by rw [hsup]; exact Subgroup.mem_top v
    exact Subgroup.mem_sup.mp this
  have huniq : ∀ {w w' u u' : V}, w ∈ W → w' ∈ W → u ∈ U → u' ∈ U → w * u = w' * u' →
      w = w' ∧ u = u' := by
    intro w w' u u' hw hw' hu hu' h
    have h1 : w'⁻¹ * w = u' * u⁻¹ := by
      calc w'⁻¹ * w = w'⁻¹ * (w * u) * u⁻¹ := by group
        _ = w'⁻¹ * (w' * u') * u⁻¹ := by rw [h]
        _ = u' * u⁻¹ := by group
    have h2 : w'⁻¹ * w ∈ W ⊓ U :=
      ⟨W.mul_mem (W.inv_mem hw') hw, h1 ▸ U.mul_mem hu' (U.inv_mem hu)⟩
    rw [hinf, Subgroup.mem_bot] at h2
    have hww : w = w' := by
      have := congrArg (fun z => w' * z) h2
      simpa using this
    refine ⟨hww, ?_⟩
    rw [hww] at h
    exact mul_left_cancel h
  let F : Subgroup V := fixV (Subgroup.zpowers t) ⊓ W
  let Uk : Subgroup V := fixV (Subgroup.zpowers k) ⊓ U
  have h2 : fixV (Subgroup.zpowers t) = F ⊔ U := by
    ext v
    constructor
    · intro hv
      obtain ⟨w, hw, u, hu, rfl⟩ := hdec v
      have ht : t (w * u) = w * u := Quasithin.mem_fixV_zpowers_iff.mp hv
      rw [map_mul, htU u hu] at ht
      have : t w = w := mul_right_cancel ht
      exact Subgroup.mem_sup.mpr ⟨w, ⟨Quasithin.mem_fixV_zpowers_iff.mpr this, hw⟩, u, hu, rfl⟩
    · intro hv
      obtain ⟨f, hf, u, hu, rfl⟩ := Subgroup.mem_sup.mp hv
      apply Quasithin.mem_fixV_zpowers_iff.mpr
      rw [map_mul, htU u hu, Quasithin.mem_fixV_zpowers_iff.mp hf.1]
  have h1 : fixV (Subgroup.zpowers (t * k)) = F ⊔ Uk := by
    ext v
    constructor
    · intro hv
      obtain ⟨w, hw, u, hu, rfl⟩ := hdec v
      have ht : (t * k) (w * u) = w * u := Quasithin.mem_fixV_zpowers_iff.mp hv
      have e : (t * k) (w * u) = t w * k u := by
        simp only [MulAut.mul_apply, map_mul, hkW w hw, htU _ (hkU u hu)]
      rw [e] at ht
      obtain ⟨hwt, hku⟩ := huniq (htW w hw) hw (hkU u hu) hu ht
      exact Subgroup.mem_sup.mpr ⟨w, ⟨Quasithin.mem_fixV_zpowers_iff.mpr hwt, hw⟩, u,
        ⟨Quasithin.mem_fixV_zpowers_iff.mpr hku, hu⟩, rfl⟩
    · intro hv
      obtain ⟨f, hf, u, hu, rfl⟩ := Subgroup.mem_sup.mp hv
      apply Quasithin.mem_fixV_zpowers_iff.mpr
      have e : (t * k) (f * u) = t f * k u := by
        simp only [MulAut.mul_apply, map_mul, hkW f hf.2, htU _ (hkU u hu.2)]
      rw [e, Quasithin.mem_fixV_zpowers_iff.mp hf.1, Quasithin.mem_fixV_zpowers_iff.mp hu.1]
  have hFU : F ⊓ U = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ W ⊓ U := ⟨hx.1.2, hx.2⟩
    rwa [hinf] at this
  have hFUk : F ⊓ Uk = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ W ⊓ U := ⟨hx.1.2, hx.2.2⟩
    rwa [hinf] at this
  rw [h1, h2, card_sup_eq_mul_of_inf_eq_bot _ _ hFUk, card_sup_eq_mul_of_inf_eq_bot _ _ hFU]
  have hUk : Nat.card ↥Uk < Nat.card ↥U := by
    refine Subgroup.card_lt_of_lt (lt_of_le_of_ne inf_le_right fun h => ?_)
    obtain ⟨u, hu, hku⟩ := hk
    have : u ∈ Uk := by rw [h]; exact hu
    exact hku (Quasithin.mem_fixV_zpowers_iff.mp this.1)
  exact Nat.mul_lt_mul_of_pos_left hUk Nat.card_pos

theorem commutator_kStab_eq_one [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {G T Y D B : Subgroup (MulAut V)} {n : ℕ} (cfg : Emb4Cfg G T Y) (hP : PlusSide G Y D B n)
    {b t : MulAut V} (hb : b ∈ B) (hb2 : b ^ 2 = 1) (hb1 : b ≠ 1) (htT : t ∈ T)
    {x : MulAut V} (_hx : x ∈ G ⊓ Subgroup.centralizer ({b} : Set (MulAut V)))
    (hxt : x * t * x⁻¹ * t⁻¹ ∈ kStab G b) : x * t = t * x := by
  have hkB : x * t * x⁻¹ * t⁻¹ ∈ B := kStab_le_B hV cfg hP hb hb2 hb1 hxt
  have hkY : x * t * x⁻¹ * t⁻¹ ∈ Y := hP.by_ hkB
  have htG : t ∈ G := cfg.adm.hTG htT
  have htcY : t ∈ Subgroup.centralizer (Y : Set (MulAut V)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_iff.mp (cfg.adm.hYC hy).2 t htT |>.symm
  have hcomm : ∀ y ∈ Y, t * y = y * t := fun y hy =>
    (Subgroup.mem_centralizer_iff.mp htcY y hy).symm
  by_contra hne
  have hk1 : x * t * x⁻¹ * t⁻¹ ≠ 1 := by
    intro h
    apply hne
    calc x * t = (x * t * x⁻¹ * t⁻¹) * t * x := by group
      _ = t * x := by rw [h, one_mul]
  have hxtx : x * t * x⁻¹ = t * (x * t * x⁻¹ * t⁻¹) := by
    rw [hcomm _ hkY]
    group
  have h2pow : ∃ m : ℕ, t ^ 2 ^ m = 1 := by
    obtain ⟨m, hm⟩ := cfg.adm.hT2 ⟨t, htT⟩
    exact ⟨m, congrArg Subtype.val hm⟩
  have hlt := card_fixV_lt (U := commV Y) (W := fixV Y) hP.vsup hP.vinf
    (t := t) (k := x * t * x⁻¹ * t⁻¹)
    (fun u hu => hP.ctriv t ⟨htG, htcY⟩ h2pow u hu)
    (fun w hw => by
      rw [mem_fixV] at hw ⊢
      intro y hy
      have := congrArg (fun z : MulAut V => z w) (hcomm y hy)
      simp only [MulAut.mul_apply] at this
      rw [← this, hw y hy])
    (fun w hw => (mem_fixV.mp hw) _ hkY) (fun u hu => commV_invariant hkY hu)
    (by
      by_contra hcon
      push Not at hcon
      exact hk1 (hP.faith _ hkY fun u hu => hcon u hu))
  rw [← hxtx, card_fixV_conj] at hlt
  exact lt_irrefl _ hlt

end CFSG.CGT.PushingUpLit.CGT6.OmegaPlus
