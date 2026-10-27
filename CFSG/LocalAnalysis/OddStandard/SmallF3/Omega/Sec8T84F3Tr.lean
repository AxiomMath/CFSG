module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F1Defs
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LocalAnalysis.ComponentClassification.HSFLitSevenPerm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {A B : Type} [Group A] [Group B]

private lemma injOn_of_inf_ker_eq_bot (f : A →* B) {P : Subgroup A}
    (hinj : P ⊓ f.ker = ⊥) {x y : A} (hx : x ∈ P) (hy : y ∈ P) (h : f x = f y) : x = y := by
  have hmem : x * y⁻¹ ∈ P ⊓ f.ker := by
    refine ⟨P.mul_mem hx (P.inv_mem hy), ?_⟩
    show f (x * y⁻¹) = 1
    rw [map_mul, map_inv, h, mul_inv_cancel]
  rw [hinj, Subgroup.mem_bot] at hmem
  exact mul_inv_eq_one.mp hmem

private lemma map_comap_eq_self (f : A →* B) {P : Subgroup A}
    (hinj : P ⊓ f.ker = ⊥) {U : Subgroup A} (hU : U ≤ P) :
    (U.map f).comap f ⊓ P = U := by
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · rw [Subgroup.mem_inf] at hx
    obtain ⟨hxmap, hxP⟩ := hx
    rw [Subgroup.mem_comap] at hxmap
    obtain ⟨u, huU, hfu⟩ := Subgroup.mem_map.mp hxmap
    have : u = x := injOn_of_inf_ker_eq_bot f hinj (hU huU) hxP hfu
    rwa [this] at huU
  · exact ⟨Subgroup.mem_comap.mpr (Subgroup.mem_map_of_mem f hx), hU hx⟩

private lemma map_injective_of_le (f : A →* B) {P : Subgroup A}
    (hinj : P ⊓ f.ker = ⊥) {U₁ U₂ : Subgroup A} (h₁ : U₁ ≤ P) (h₂ : U₂ ≤ P)
    (h : U₁.map f = U₂.map f) : U₁ = U₂ := by
  rw [← map_comap_eq_self f hinj h₁, h, map_comap_eq_self f hinj h₂]

private lemma card_map_of_le (f : A →* B) {P : Subgroup A}
    (hinj : P ⊓ f.ker = ⊥) {U : Subgroup A} (hU : U ≤ P) :
    Nat.card (U.map f) = Nat.card U := by
  have hinj' : Function.Injective (f.comp P.subtype) := fun x y hxy =>
    Subtype.ext (injOn_of_inf_ker_eq_bot f hinj x.2 y.2 hxy)
  have h1 : U.map f = (U.subgroupOf P).map (f.comp P.subtype) := by
    conv_lhs => rw [← Subgroup.map_subgroupOf_eq_of_le hU]
    rw [Subgroup.map_map]
  rw [h1]
  rw [Subgroup.card_map_of_injective (f := f.comp P.subtype)
    (K := U.subgroupOf P) hinj']
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU).toEquiv

private lemma isElemAbelian_of_map (f : A →* B) {P : Subgroup A}
    (hinj : P ⊓ f.ker = ⊥) {U : Subgroup A} (hU : U ≤ P)
    (h : CFSG.Open.IsElemAbelian 2 (U.map f)) : CFSG.Open.IsElemAbelian 2 U := by
  refine ⟨isMulCommutative_iff.mpr fun x y => Subtype.ext ?_, fun x hx => ?_⟩
  · apply injOn_of_inf_ker_eq_bot f hinj (P.mul_mem (hU x.2) (hU y.2))
      (P.mul_mem (hU y.2) (hU x.2))
    rw [map_mul, map_mul]
    exact h.comm (Subgroup.mem_map_of_mem f x.2) (Subgroup.mem_map_of_mem f y.2)
  · apply injOn_of_inf_ker_eq_bot f hinj (P.pow_mem (hU hx) 2) P.one_mem
    rw [map_pow, map_one]
    exact h.2 (f x) (Subgroup.mem_map_of_mem f hx)

private lemma isElemAb2_of_map (f : A →* B) {P : Subgroup A}
    (hinj : P ⊓ f.ker = ⊥) {U : Subgroup A} (hU : U ≤ P) {k : ℕ}
    (h : IsElemAb2 (U.map f) k) : IsElemAb2 U k :=
  ⟨isElemAbelian_of_map f hinj hU h.1,
    by rw [← card_map_of_le f hinj hU]; exact h.2⟩

private lemma isElemAb2_map (f : A →* B) {P : Subgroup A}
    (hinj : P ⊓ f.ker = ⊥) {U : Subgroup A} (hU : U ≤ P) {k : ℕ}
    (h : IsElemAb2 U k) : IsElemAb2 (U.map f) k :=
  ⟨h.1.map f, by rw [card_map_of_le f hinj hU]; exact h.2⟩

private lemma map_inf_eq_of_le (f : A →* B) {P : Subgroup A} (hinj : P ⊓ f.ker = ⊥)
    {U₁ U₂ : Subgroup A} (h₁ : U₁ ≤ P) (h₂ : U₂ ≤ P) :
    (U₁ ⊓ U₂).map f = U₁.map f ⊓ U₂.map f := by
  refine le_antisymm (le_inf (Subgroup.map_mono inf_le_left) (Subgroup.map_mono inf_le_right)) ?_
  intro y hy
  obtain ⟨hy₁, hy₂⟩ := Subgroup.mem_inf.mp hy
  obtain ⟨u, hu, hfu⟩ := Subgroup.mem_map.mp hy₁
  have huU₂ : u ∈ U₂ := by
    obtain ⟨w, hw, hfw⟩ := Subgroup.mem_map.mp (hfu.symm ▸ hy₂)
    have hw_eq : w = u := injOn_of_inf_ker_eq_bot f hinj (h₂ hw) (h₁ hu) hfw
    rwa [hw_eq] at hw
  exact hfu ▸ Subgroup.mem_map_of_mem f (Subgroup.mem_inf.mpr ⟨hu, huU₂⟩)

private lemma comap_inf_map_eq (f : A →* B) {P : Subgroup A} {E : Subgroup B}
    (hE : E ≤ P.map f) : (E.comap f ⊓ P).map f = E := by
  refine le_antisymm ?_ ?_
  · calc (E.comap f ⊓ P).map f ≤ (E.comap f).map f := Subgroup.map_mono inf_le_left
      _ ≤ E := Subgroup.map_comap_le f E
  · intro y hy
    obtain ⟨x, hxP, hfx⟩ := Subgroup.mem_map.mp (hE hy)
    exact hfx ▸ Subgroup.mem_map_of_mem f
      (Subgroup.mem_inf.mpr ⟨Subgroup.mem_comap.mpr (hfx.symm ▸ hy), hxP⟩)

private lemma inf_zpowers_eq_bot_of_not_mem [Finite B] {J : Subgroup B} {v : B}
    (hv2 : v ^ 2 = 1) (hvJ : v ∉ J) : J ⊓ Subgroup.zpowers v = ⊥ := by
  have hv1 : v ≠ 1 := fun h => hvJ (h ▸ J.one_mem)
  have horder : orderOf v = 2 := orderOf_eq_prime hv2 hv1
  rw [Subgroup.eq_bot_iff_card]
  have hdvd : Nat.card ↥(J ⊓ Subgroup.zpowers v) ∣ 2 := by
    have h := Subgroup.card_dvd_of_le (H := J ⊓ Subgroup.zpowers v)
      (K := Subgroup.zpowers v) inf_le_right
    rwa [Nat.card_zpowers, horder] at h
  have hne : Nat.card ↥(J ⊓ Subgroup.zpowers v) ≠ 2 := by
    intro h2
    have heq : J ⊓ Subgroup.zpowers v = Subgroup.zpowers v := by
      refine Subgroup.eq_of_le_of_card_ge inf_le_right ?_
      rw [h2, Nat.card_zpowers, horder]
    have : v ∈ J ⊓ Subgroup.zpowers v := by
      rw [heq]; exact Subgroup.mem_zpowers v
    exact hvJ this.1
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exact h1
  · exact absurd h2 hne

theorem sec8t84_pmod_of_hom {A B : Type} [Group A] [Finite A] [Group B] [Finite B] (f : A →* B)
    {V P : Subgroup A} (hVP : V ≤ P) (hinj : P ⊓ f.ker = ⊥) (hV : IsElemAb2 V 4)
    (hVn : (V.subgroupOf P).Normal) {Fb : Subgroup B}
    (hF : Sec8T84PFacts B (V.map f) (P.map f) Fb) :
    Sec8T84PMod A V P (Fb.comap f ⊓ P) := by
  set F : Subgroup A := Fb.comap f ⊓ P with hFdef
  have hFle : F ≤ P := by rw [hFdef]; exact inf_le_right
  have hFmap : F.map f = Fb := by rw [hFdef]; exact comap_inf_map_eq f hF.F_le
  obtain ⟨y, hy3, hyN, hyC, sbar, hsbarP, hsbarNot, hsbarOrder, hsbarInv, hsbarGen⟩ :=
    hF.y_exists
  obtain ⟨s, hsP, hfs⟩ := Subgroup.mem_map.mp hsbarP
  have hs2 : s ^ 2 = 1 := by
    have hsker : f (s ^ 2) = 1 := by
      rw [map_pow, hfs, ← hsbarOrder]
      exact pow_orderOf_eq_one sbar
    have hmem : s ^ 2 ∈ P ⊓ f.ker := ⟨P.pow_mem hsP 2, MonoidHom.mem_ker.mpr hsker⟩
    rw [hinj, Subgroup.mem_bot] at hmem
    exact hmem
  have hs1 : s ≠ 1 := by
    intro h
    have hsbar1 : sbar = 1 := by rw [← hfs, h, map_one]
    rw [hsbar1, orderOf_one] at hsbarOrder
    exact absurd hsbarOrder (by decide)
  have hsOrder : orderOf s = 2 := orderOf_eq_prime hs2 hs1
  have hsNot : s ∉ V ⊔ F := by
    intro hs
    apply hsbarNot
    have hmem : f s ∈ (V ⊔ F).map f := Subgroup.mem_map_of_mem f hs
    rwa [Subgroup.map_sup, hFmap, hfs] at hmem
  have hPgen : P = zpowers s ⊔ (V ⊔ F) := by
    apply map_injective_of_le f hinj le_rfl
      (sup_le (Subgroup.zpowers_le.mpr hsP) (sup_le hVP hFle))
    rw [Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers, hfs, hFmap]
    exact hsbarGen
  have hFe16 : IsElemAb2 F 4 :=
    isElemAb2_of_map f hinj hFle (by rw [hFmap]; exact hF.F_e16)
  have hFne : F ≠ V := by
    intro h
    exact hF.F_ne (hFmap.symm.trans (by rw [h]))
  have hFnorm : (F.subgroupOf P).Normal := by
    rw [hFdef, Subgroup.normal_subgroupOf_iff inf_le_right]
    intro a b ha hb
    refine ⟨?_, P.mul_mem (P.mul_mem hb ha.2) (P.inv_mem hb)⟩
    show f (b * a * b⁻¹) ∈ Fb
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.normal_subgroupOf_iff hF.F_le).mp hF.F_norm (f a) (f b)
      (Subgroup.mem_comap.mp ha.1) (Subgroup.mem_map_of_mem f hb)
  have onlyF : ∀ F' : Subgroup A, F' ≤ P → IsElemAb2 F' 4 → F' = V ∨ F' = F := by
    intro F' hF'le hF'e
    rcases hF.only (F'.map f) (Subgroup.map_mono hF'le) (isElemAb2_map f hinj hF'le hF'e) with
      h | h
    · exact Or.inl (map_injective_of_le f hinj hF'le hVP h)
    · exact Or.inr (map_injective_of_le f hinj hF'le hFle (h.trans hFmap.symm))
  have no32F : ∀ F' : Subgroup A, F' ≤ P → ¬ IsElemAb2 F' 5 := fun F' hF'le hF'e =>
    hF.no32 (F'.map f) (Subgroup.map_mono hF'le) (isElemAb2_map f hinj hF'le hF'e)
  have hJcard : Nat.card ↥(V ⊔ F) = 64 := by
    rw [← card_map_of_le f hinj (sup_le hVP hFle), Subgroup.map_sup, hFmap]
    exact hF.J_card
  have hEFcard : Nat.card ↥(V ⊓ F) = 4 := by
    rw [← card_map_of_le f hinj ((inf_le_right : V ⊓ F ≤ F).trans hFle),
      map_inf_eq_of_le f hinj hVP hFle, hFmap]
    exact hF.EF_card
  have centV : P ⊓ centralizer (V : Set A) = V := by
    refine le_antisymm (fun x hx => ?_)
      (le_inf hVP (Subgroup.le_centralizer_iff_isMulCommutative.mpr hV.1.1))
    obtain ⟨hxP, hxcent⟩ := Subgroup.mem_inf.mp hx
    have hxmap : f x ∈ V.map f := by
      have hmem : f x ∈ P.map f ⊓ centralizer (V.map f : Set B) := by
        refine ⟨Subgroup.mem_map_of_mem f hxP, ?_⟩
        refine Subgroup.mem_centralizer_iff.mpr ?_
        intro w hw
        obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hw
        rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hxcent v hv]
      rwa [hF.cent_E] at hmem
    rw [← map_comap_eq_self f hinj hVP]
    exact ⟨Subgroup.mem_comap.mpr hxmap, hxP⟩
  have centF : P ⊓ centralizer (F : Set A) = F := by
    refine le_antisymm (fun x hx => ?_)
      (le_inf hFle (Subgroup.le_centralizer_iff_isMulCommutative.mpr hFe16.1.1))
    obtain ⟨hxP, hxcent⟩ := Subgroup.mem_inf.mp hx
    have hxmap : f x ∈ Fb := by
      have hmem : f x ∈ P.map f ⊓ centralizer (Fb : Set B) := by
        refine ⟨Subgroup.mem_map_of_mem f hxP, ?_⟩
        refine Subgroup.mem_centralizer_iff.mpr ?_
        intro w hw
        rw [← hFmap] at hw
        obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hw
        rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hxcent v hv]
      rwa [hF.cent_F] at hmem
    have : f x ∈ F.map f := by rw [hFmap]; exact hxmap
    rw [← map_comap_eq_self f hinj hFle]
    exact ⟨Subgroup.mem_comap.mpr this, hxP⟩
  have genF : ∃ s ∈ P, s ∉ V ⊔ F ∧ orderOf s = 2 ∧ P = zpowers s ⊔ (V ⊔ F) :=
    ⟨s, hsP, hsNot, hsOrder, hPgen⟩
  have cardP : Nat.card P = 2 ^ 7 := by
    rw [← card_map_of_le f hinj (le_refl P)]
    have hJb_le : V.map f ⊔ Fb ≤ P.map f := sup_le (Subgroup.map_mono hVP) hF.F_le
    have hVmap_normal : ((V.map f).subgroupOf (P.map f)).Normal := by
      rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono hVP)]
      intro a b ha hb
      obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp ha
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hb
      have hvV : x * v * x⁻¹ ∈ V := (Subgroup.normal_subgroupOf_iff hVP).mp hVn v x hv hx
      simpa using Subgroup.mem_map_of_mem f hvV
    have hJb_normal : ((V.map f ⊔ Fb).subgroupOf (P.map f)).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hJb_le]
      refine le_trans (le_inf ?_ ?_)
        (Subgroup.inf_normalizer_le_normalizer_sup (V.map f) Fb)
      · exact (Subgroup.normal_subgroupOf_iff_le_normalizer
          (Subgroup.map_mono hVP)).mp hVmap_normal
      · exact (Subgroup.normal_subgroupOf_iff_le_normalizer hF.F_le).mp hF.F_norm
    have hdisj : (V.map f ⊔ Fb) ⊓ Subgroup.zpowers sbar = ⊥ :=
      inf_zpowers_eq_bot_of_not_mem
        (by rw [← hsbarOrder]; exact pow_orderOf_eq_one sbar) hsbarNot
    have hle : Subgroup.zpowers sbar ≤
        Subgroup.normalizer ((V.map f ⊔ Fb : Subgroup B) : Set B) :=
      le_trans (Subgroup.zpowers_le.mpr hsbarP)
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hJb_le).mp hJb_normal)
    have hcard := CFSG.ComponentClassification.HSFLit.card_sup_eq_mul_of_le_normalizer hle hdisj
    have hcard' : Nat.card ↥(Subgroup.zpowers sbar ⊔ (V.map f ⊔ Fb)) =
        Nat.card ↥(V.map f ⊔ Fb) * Nat.card (Subgroup.zpowers sbar) := by
      rw [show Subgroup.zpowers sbar ⊔ (V.map f ⊔ Fb) =
        (V.map f ⊔ Fb) ⊔ Subgroup.zpowers sbar from
          sup_comm (Subgroup.zpowers sbar) (V.map f ⊔ Fb)]
      exact hcard
    have hsbar_card : Nat.card (Subgroup.zpowers sbar) = 2 := by
      rw [Nat.card_zpowers, hsbarOrder]
    rw [hsbarGen, hcard', hF.J_card, hsbar_card]
    norm_num
  exact ⟨cardP, hVP, hFle, hV, hFe16, hFne, hVn, hFnorm, onlyF, no32F, hJcard, hEFcard,
    centV, centF, genF⟩

end CFSG.OddStandard.SmallF3.Omega
