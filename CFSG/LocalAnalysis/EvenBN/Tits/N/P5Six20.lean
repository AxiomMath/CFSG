module

public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.EvenBN.Tits.N.StarBasic
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5Lin
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5KSet

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5

open Subgroup CFSG.Open CFSG.LocalAnalysis.EvenBN.Tits.N

variable {Γ : Type} [Group Γ] [Finite Γ]

omit [Finite Γ] in
theorem exists_le_fusionIsSylowIn_two {D X : Subgroup Γ} (hD : IsPGroup 2 D) (hDX : D ≤ X) :
    ∃ T : Subgroup Γ, D ≤ T ∧ fusionIsSylowIn 2 T X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := (hD.comap_subtype (K := X)).exists_le_sylow
  refine ⟨(P : Subgroup X).map X.subtype,
    fun u hu => ⟨⟨u, hDX hu⟩, hP (show (⟨u, hDX hu⟩ : X) ∈ D.comap X.subtype from hu), rfl⟩,
    Subgroup.map_subtype_le _, P.isPGroup'.map _, fun Q hQX hQ hPQ => ?_⟩
  have h1 := P.is_maximal' (Q := Q.subgroupOf X) hQ.comap_subtype
    (fun x hx => hPQ ⟨x, hx, rfl⟩)
  refine le_antisymm (fun q hq => ⟨⟨q, hQX hq⟩, ?_, rfl⟩) hPQ
  rw [← h1]
  exact hq

omit [Finite Γ] in
theorem mem_map_mulAutConj_iff {A : Subgroup Γ} {g a : Γ} :
    a ∈ A.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * a * g ∈ A := by
  rw [mem_map_equiv, MulAut.conj_symm_apply]

omit [Finite Γ] in
theorem card_map_mulAutConj (A : Subgroup Γ) (g : Γ) :
    Nat.card (A.map (MulAut.conj g).toMonoidHom) = Nat.card A :=
  card_map_of_injective (MulAut.conj g).injective

namespace KSet

variable {Hs C U K W0 W : Subgroup Γ} {x y t : Γ} (h : KSet Hs C U K W0 W x y t)

include h

theorem card_le_of_elemAbelian_le_C {D : Subgroup Γ} (hDC : D ≤ C) (hD : IsElemAbelian 2 D) :
    Nat.card D ≤ 32 ∧ (Nat.card D = 32 → D = U ⊔ zpowers t) := by
  obtain ⟨T, hDT, hT⟩ := exists_le_fusionIsSylowIn_two hD.isPGroup hDC
  have hA := h.A1 T hT
  have hU0 : U ⊔ zpowers t ∈ maxElemAbelian2 T := hA ▸ Set.mem_singleton _
  have hle : ∀ D' : Subgroup Γ, D' ≤ T → IsElemAbelian 2 D' → Nat.card D' ≤ 32 := fun D' hD'T hD' =>
    h.card_U0 ▸ hU0.2.2 D' hD'T hD'
  refine ⟨hle D hDT hD, fun h32 => ?_⟩
  have hDmem : D ∈ maxElemAbelian2 T := ⟨hDT, hD, fun D' hD'T hD' => h32 ▸ hle D' hD'T hD'⟩
  rw [hA] at hDmem
  exact hDmem

theorem card_le_of_elemAbelian_le_centralizer_conj {g : Γ} (hg : g ∈ Hs) {X : Subgroup Γ}
    (hX : X ≤ centralizer ({g * t * g⁻¹} : Set Γ) ⊓ Hs) (hXab : IsElemAbelian 2 X) :
    Nat.card X ≤ 32 ∧ (Nat.card X = 32 → X = (U ⊔ zpowers t).map (MulAut.conj g).toMonoidHom) := by
  have hDC : X.map (MulAut.conj g⁻¹).toMonoidHom ≤ C := by
    intro b hb
    rw [mem_map_mulAutConj_iff, inv_inv] at hb
    obtain ⟨hbc, hbH⟩ := Subgroup.mem_inf.1 (hX hb)
    rw [mem_centralizer_singleton_iff] at hbc
    rw [h.C_cent]
    refine ⟨mem_centralizer_singleton_iff.2 ?_, ?_⟩
    · calc b * t = g⁻¹ * ((g * b * g⁻¹) * (g * t * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * t * g⁻¹) * (g * b * g⁻¹)) * g := by rw [hbc]
        _ = t * b := by group
    · have e : b = g⁻¹ * (g * b * g⁻¹) * g := by group
      rw [e]
      exact mul_mem (mul_mem (Subgroup.inv_mem _ hg) hbH) hg
  obtain ⟨h1, h2⟩ := h.card_le_of_elemAbelian_le_C hDC (hXab.map _)
  rw [card_map_mulAutConj] at h1 h2
  refine ⟨h1, fun h32 => ?_⟩
  have hDU := h2 h32
  ext a
  rw [mem_map_mulAutConj_iff, ← hDU, mem_map_mulAutConj_iff, inv_inv,
    show g * (g⁻¹ * a * g) * g⁻¹ = a by group]

theorem six20 (hmax : maxElemAbelian2 K = {W}) {g : Γ} (hg : g ∈ Hs)
    (hs : g * t * g⁻¹ ∈ normalizer (W : Set Γ)) :
    zpowers (g * t * g⁻¹) ⊔ (W ⊓ centralizer ({g * t * g⁻¹} : Set Γ)) =
        (U ⊔ zpowers t).map (MulAut.conj g).toMonoidHom ∧
      g ∈ normalizer (W : Set Γ) := by
  have hconj : ∀ {X : Subgroup Γ}, X ≤ centralizer ({g * t * g⁻¹} : Set Γ) ⊓ Hs → IsElemAbelian 2 X →
      Nat.card X ≤ 32 ∧ (Nat.card X = 32 → X = (U ⊔ zpowers t).map (MulAut.conj g).toMonoidHom) :=
    fun hX hXab => h.card_le_of_elemAbelian_le_centralizer_conj hg hX hXab
  generalize hsdef : g * t * g⁻¹ = s at hs hconj ⊢
  have hss : s * s = 1 := by
    rw [← hsdef]
    calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [h.t_sq]; group
  have hs1 : s ≠ 1 := by
    intro e
    apply h.t_ne_one
    calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
      _ = 1 := by rw [hsdef, e]; group
  have hs2 : s ^ 2 = 1 := by rw [pow_two]; exact hss
  have hsH : s ∈ Hs := hsdef ▸ mul_mem (mul_mem hg (h.C_le_Hs h.t_mem_C)) (Subgroup.inv_mem _ hg)
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have hWc : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb => h.W_ab.comm ha hb
  have hsW : s ∉ W := by
    intro hsW
    have hWle : W ≤ centralizer ({s} : Set Γ) ⊓ Hs := fun w hw =>
      ⟨mem_centralizer_singleton_iff.2 (hWc w hw s hsW), h.W_le_Hs hw⟩
    have h1 := (hconj hWle h.W_ab).1
    rw [h.W_card] at h1
    norm_num at h1
  set Z := W ⊓ centralizer ({s} : Set Γ)
  have hZ16 : 16 ≤ Nat.card Z := by
    have hj : actFun W s * actFun W s = 1 := by
      rw [← actFun_mul W hs hs, hss, actFun_one]
    have hc : ∀ a b : ↥W, a * b = b * a := fun a b => Subtype.ext (hWc a a.2 b b.2)
    have h2 : ∀ w : ↥W, w * w = 1 := fun w => Subtype.ext (h.W_ab.mul_self_eq_one w.2)
    have hle := card_le_sq_fixSub hc h2 hj
    have hfix : (fixSub (actFun W s)).map W.subtype = Z := by
      ext a
      rw [mem_map]
      constructor
      · rintro ⟨w, hw, rfl⟩
        rw [mem_fixSub, actFun_fixes_iff W hs] at hw
        exact Subgroup.mem_inf.2 ⟨w.2, mem_centralizer_singleton_iff.2 hw.symm⟩
      · intro ha
        obtain ⟨haW, hac⟩ := Subgroup.mem_inf.1 ha
        refine ⟨⟨a, haW⟩, ?_, rfl⟩
        rw [mem_fixSub, actFun_fixes_iff W hs]
        exact (mem_centralizer_singleton_iff.1 hac).symm
    rw [← card_map_of_injective (f := W.subtype) W.subtype_injective, hfix, h.W_card] at hle
    by_contra hlt
    push Not at hlt
    have : Nat.card Z ^ 2 ≤ 15 ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have hZab : IsElemAbelian 2 Z := h.W_ab.mono inf_le_left
  have hsZ : ∀ a ∈ Z, ∀ b ∈ zpowers s, a * b = b * a := by
    intro a ha b hb
    rcases mem_zpowers_sq_one hss hb with rfl | rfl
    · rw [mul_one, one_mul]
    · exact mem_centralizer_singleton_iff.1 ha.2
  have hnZ : zpowers s ≤ normalizer (Z : Set Γ) :=
    zpowers_le.2 (Subgroup.centralizer_le_normalizer _
      (mem_centralizer_iff.2 fun z hz => hsZ z hz s (mem_zpowers s)))
  have hdisj : Disjoint Z (zpowers s) := by
    rw [disjoint_iff, eq_bot_iff]
    rintro a ⟨haZ, has⟩
    rcases mem_zpowers_sq_one hss has with rfl | rfl
    · exact one_mem _
    · exact absurd haZ.1 hsW
  have hsord : orderOf s = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime hs2 hs1
  set E := Z ⊔ zpowers s with hEdef
  have hEcard : Nat.card E = Nat.card Z * 2 := by
    rw [hEdef, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer Z (zpowers s) hnZ hdisj,
      Nat.card_zpowers, hsord]
  have hEab : IsElemAbelian 2 E := hZab.sup_of_commute (isElemAbelian_zpowers hs2) hsZ
  have hEle : E ≤ centralizer ({s} : Set Γ) ⊓ Hs := by
    refine sup_le (le_inf inf_le_right (inf_le_left.trans h.W_le_Hs)) ?_
    rw [zpowers_le]
    exact ⟨mem_centralizer_singleton_iff.2 rfl, hsH⟩
  obtain ⟨hE32, hEU⟩ := hconj hEle hEab
  have hEeq : E = (U ⊔ zpowers t).map (MulAut.conj g).toMonoidHom := hEU (by omega)
  refine ⟨by rw [sup_comm]; exact hEeq, ?_⟩
  have hmap : ∀ w ∈ W, ∀ e ∈ E, w * e * w⁻¹ ∈ E := by
    intro w hw e he
    have he' : e ∈ ((Z ⊔ zpowers s : Subgroup Γ) : Set Γ) := he
    rw [coe_mul_of_right_le_normalizer_left Z (zpowers s) hnZ] at he'
    obtain ⟨z, hz, b, hb, rfl⟩ := Set.mem_mul.1 he'
    have hz' : z ∈ Z := hz
    have hwz : w * z * w⁻¹ = z := by rw [hWc w hw z (Subgroup.mem_inf.1 hz').1]; group
    obtain hb1 | hb1 := mem_zpowers_sq_one hss hb
    · rw [hb1, mul_one, hwz]
      exact mem_sup_left hz'
    · rw [hb1]
      have hv : s * w * s ∈ W := by
        have h1 := (mem_normalizer_iff.1 hs w).1 hw
        rwa [hsinv] at h1
      have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right (h.W_ab.mul_self_eq_one hw)
      have hwv : w * (s * w * s) = (s * w * s) * w := hWc w hw _ hv
      have hcs : w * (s * w * s) ∈ centralizer ({s} : Set Γ) := by
        rw [mem_centralizer_singleton_iff]
        calc w * (s * w * s) * s = (s * w * s) * w * s := by rw [hwv]
          _ = s * (w * (s * w * s)) := by group
      have e' : w * (z * s) * w⁻¹ = z * (w * (s * w * s)) * s := by
        calc w * (z * s) * w⁻¹ = (w * z * w⁻¹) * (w * s * w⁻¹) := by group
          _ = z * (w * s * w) := by rw [hwz, hwinv]
          _ = z * (w * s * w) * (s * s) := by rw [hss, mul_one]
          _ = z * (w * (s * w * s)) * s := by group
      rw [e']
      exact mul_mem (mem_sup_left (mul_mem hz' (Subgroup.mem_inf.2 ⟨mul_mem hw hv, hcs⟩)))
        (mem_sup_right (mem_zpowers s))
  have hWE : ∀ w ∈ W, w ∈ normalizer (E : Set Γ) := fun w hw => mem_normalizer_iff.2 fun e =>
    ⟨hmap w hw e, fun he => by
      have := hmap w⁻¹ (Subgroup.inv_mem _ hw) _ he
      rwa [show w⁻¹ * (w * e * w⁻¹) * w⁻¹⁻¹ = e by group] at this⟩
  have hU0 : ∀ a, a ∈ U ⊔ zpowers t ↔ g * a * g⁻¹ ∈ E := fun a => by
    rw [hEeq, mem_map_mulAutConj_iff, show g⁻¹ * (g * a * g⁻¹) * g = a by group]
  have hWK : W.map (MulAut.conj g⁻¹).toMonoidHom ≤ K := by
    intro b hb
    rw [mem_map_mulAutConj_iff, inv_inv] at hb
    have hb' : b = g⁻¹ * (g * b * g⁻¹) * g := by group
    rw [h.K_def]
    refine ⟨mem_normalizer_iff.2 fun a => ?_, ?_⟩
    · rw [hU0 a, hU0, show g * (b * a * b⁻¹) * g⁻¹ = (g * b * g⁻¹) * (g * a * g⁻¹) * (g * b * g⁻¹)⁻¹ by group]
      exact mem_normalizer_iff.1 (hWE _ hb) _
    · rw [hb']
      exact mul_mem (mul_mem (Subgroup.inv_mem _ hg) (h.W_le_Hs hb)) hg
  have hWmax : W ∈ maxElemAbelian2 K := hmax ▸ Set.mem_singleton _
  have hWg : W.map (MulAut.conj g⁻¹).toMonoidHom ∈ maxElemAbelian2 K :=
    ⟨hWK, h.W_ab.map _, fun D hDK hD => (card_map_mulAutConj W g⁻¹).symm ▸ hWmax.2.2 D hDK hD⟩
  rw [hmax] at hWg
  have hginv : g⁻¹ ∈ normalizer (W : Set Γ) := mem_normalizer_iff_map_conj_eq.2 hWg
  exact inv_inv g ▸ Subgroup.inv_mem _ hginv

end KSet

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5
