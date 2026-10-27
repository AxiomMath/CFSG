module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.NA
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.EvenSporadicStandard.Co2Std.Exclusion

open Subgroup
open scoped IsMulCommutative Pointwise

variable {G : Type} [Group G] [Finite G] {L A T : Subgroup G} {z t : G}
  {W W₁ W₂ : Subgroup G}

private theorem card_inf_centralizer (h : WHyp G L A T z t W W₁ W₂) {u : G}
    (hu : u ∈ normalizer (W : Set G)) (huz : IsConj z u) (hu2 : u * u = 1) (huW : u ∉ W) :
    Nat.card ↥(W ⊓ centralizer ({u} : Set G)) = 2 ^ 10 ∧
      Nat.card ↥((W ⊓ centralizer ({u} : Set G)) ⊔ zpowers u) = 2 ^ 11 ∧
      IsElementaryAbelian 2 ↥((W ⊓ centralizer ({u} : Set G)) ⊔ zpowers u) ∧
      ((W ⊓ centralizer ({u} : Set G)) ⊔ zpowers u) ≤ centralizer ({u} : Set G) := by
  classical
  haveI hWelem : IsElementaryAbelian 2 ↥W := h.elemAb
  haveI hWcomm : IsMulCommutative ↥W := hWelem.toIsMulCommutative
  have hu_inv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hWcard : Nat.card ↥W = 2 ^ 20 := h.e3.card
  let ψ : ↥W →* ↥W :=
    ((MulAut.conj u).toMonoidHom.comp W.subtype).codRestrict W
      (fun w => (mem_normalizer_iff.1 hu (w : G)).1 w.2)
  let φ : ↥W →* ↥W := MonoidHom.id ↥W * ψ
  have hψ : ∀ w : ↥W, ((ψ w : ↥W) : G) = u * (w : G) * u⁻¹ := fun w => rfl
  have hφ : ∀ w : ↥W, ((φ w : ↥W) : G) = (w : G) * (u * (w : G) * u⁻¹) := by
    intro w
    show ((w : ↥W) : G) * ((ψ w : ↥W) : G) = (w : G) * (u * (w : G) * u⁻¹)
    rw [hψ]
  have hsq : ∀ w : ↥W, (w : G) * (w : G) = 1 := by
    intro w
    have h1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := W) (w : G) w.2
    rwa [pow_two] at h1
  have hker : φ.ker = (W ⊓ centralizer ({u} : Set G)).subgroupOf W := by
    ext w
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      mem_centralizer_singleton_iff, w.2, true_and]
    constructor
    · intro hw
      have h1 : (w : G) * (u * (w : G) * u⁻¹) = 1 := by
        have h2 : ((φ w : ↥W) : G) = 1 := by rw [hw]; rfl
        rwa [hφ w] at h2
      have h3 : u * (w : G) * u⁻¹ = (w : G) :=
        (eq_inv_of_mul_eq_one_right h1).trans (inv_eq_of_mul_eq_one_right (hsq w))
      calc (w : G) * u = (u * (w : G) * u⁻¹) * u := by rw [h3]
        _ = u * (w : G) := by group
    · intro hw
      apply Subtype.ext
      show (w : G) * (u * (w : G) * u⁻¹) = 1
      have h3 : u * (w : G) * u⁻¹ = (w : G) := by
        calc u * (w : G) * u⁻¹ = ((w : G) * u) * u⁻¹ := by rw [hw]
          _ = (w : G) := by rw [mul_inv_cancel_right]
      rw [h3, hsq w]
  have hrange_le : φ.range ≤ (W ⊓ centralizer ({u} : Set G)).subgroupOf W := by
    rintro _ ⟨w, rfl⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    refine ⟨(φ w).2, ?_⟩
    rw [mem_centralizer_singleton_iff]
    have huw : u * (w : G) * u⁻¹ ∈ W := (mem_normalizer_iff.1 hu (w : G)).1 w.2
    have hcw : (w : G) * (u * (w : G) * u⁻¹) = (u * (w : G) * u⁻¹) * (w : G) :=
      congrArg Subtype.val (mul_comm' w ⟨u * (w : G) * u⁻¹, huw⟩)
    have hucu : u * (u * (w : G) * u⁻¹) * u⁻¹ = (w : G) := by
      calc u * (u * (w : G) * u⁻¹) * u⁻¹ = u * u * (w : G) * (u⁻¹ * u⁻¹) := by group
        _ = (w : G) := by rw [hu2, hu_inv, hu2]; group
    have h1 : u * ((φ w : ↥W) : G) * u⁻¹ = ((φ w : ↥W) : G) := by
      rw [hφ w]
      calc u * ((w : G) * (u * (w : G) * u⁻¹)) * u⁻¹
          = (u * (w : G) * u⁻¹) * (u * (u * (w : G) * u⁻¹) * u⁻¹) := by group
        _ = (u * (w : G) * u⁻¹) * (w : G) := by rw [hucu]
        _ = (w : G) * (u * (w : G) * u⁻¹) := hcw.symm
    calc ((φ w : ↥W) : G) * u = (u * ((φ w : ↥W) : G) * u⁻¹) * u := by rw [h1]
      _ = u * ((φ w : ↥W) : G) := by group
  have hck : Nat.card ↥φ.ker = Nat.card ↥(W ⊓ centralizer ({u} : Set G)) := by
    rw [hker]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : W ⊓ centralizer ({u} : Set G) ≤ W)).toEquiv
  have hcr : Nat.card ↥φ.range ≤ Nat.card ↥(W ⊓ centralizer ({u} : Set G)) := by
    have h1 : Nat.card ↥φ.range ≤
        Nat.card ↥((W ⊓ centralizer ({u} : Set G)).subgroupOf W) :=
      Nat.card_le_card_of_injective (Subgroup.inclusion hrange_le)
        (Subgroup.inclusion_injective hrange_le)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : W ⊓ centralizer ({u} : Set G) ≤ W)).toEquiv] at h1
  have hdecomp : Nat.card ↥W =
      Nat.card ↥(W ⊓ centralizer ({u} : Set G)) * Nat.card ↥φ.range := by
    rw [← Subgroup.card_ker_mul_card_range φ, hck]
  have hsquare : 2 ^ 20 ≤
      Nat.card ↥(W ⊓ centralizer ({u} : Set G)) * Nat.card ↥(W ⊓ centralizer ({u} : Set G)) := by
    calc 2 ^ 20 = Nat.card ↥W := hWcard.symm
      _ = Nat.card ↥(W ⊓ centralizer ({u} : Set G)) * Nat.card ↥φ.range := hdecomp
      _ ≤ Nat.card ↥(W ⊓ centralizer ({u} : Set G)) *
            Nat.card ↥(W ⊓ centralizer ({u} : Set G)) := Nat.mul_le_mul_left _ hcr
  have hCge : 2 ^ 10 ≤ Nat.card ↥(W ⊓ centralizer ({u} : Set G)) := by
    nlinarith [hsquare]
  have hzu_cent : zpowers u ≤ centralizer ((W ⊓ centralizer ({u} : Set G)) : Set G) := by
    rw [zpowers_le, Subgroup.mem_centralizer_iff]
    intro c hc
    exact mem_centralizer_singleton_iff.mp
      ((inf_le_right : W ⊓ centralizer ({u} : Set G) ≤ centralizer ({u} : Set G)) hc)
  have hCcent : W ⊓ centralizer ({u} : Set G) ≤
      centralizer (zpowers u : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact inf_le_right
  haveI hCelem : IsElementaryAbelian 2 ↥(W ⊓ centralizer ({u} : Set G)) :=
    hWelem.of_le inf_le_left
  haveI hzu_elem : IsElementaryAbelian 2 ↥(zpowers u) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (p := 2) (by rw [pow_two]; exact hu2)
  haveI hYelem : IsElementaryAbelian 2 ↥(zpowers u ⊔ (W ⊓ centralizer ({u} : Set G))) :=
    IsElementaryAbelian.sup_of_le_centralizer hCcent
  have hYsup : (W ⊓ centralizer ({u} : Set G)) ⊔ zpowers u =
      zpowers u ⊔ (W ⊓ centralizer ({u} : Set G)) := sup_comm _ _
  have hdisj : Disjoint (W ⊓ centralizer ({u} : Set G)) (zpowers u) := by
    rw [disjoint_iff]
    refine le_bot_iff.1 ?_
    intro x hx
    rcases eq_one_or_eq_of_mem_zpowers hu2 hx.2 with rfl | rfl
    · exact one_mem _
    · exact absurd hx.1.1 huW
  have hzcard : Nat.card ↥(zpowers u) = 2 := by
    have hz2 : u ^ 2 = 1 := by rw [pow_two]; exact hu2
    rw [Nat.card_zpowers, orderOf_eq_prime hz2 (fun h1 => huW (h1 ▸ one_mem W))]
  have hYcard : Nat.card ↥((W ⊓ centralizer ({u} : Set G)) ⊔ zpowers u) =
      2 * Nat.card ↥(W ⊓ centralizer ({u} : Set G)) := by
    rw [← Nat.card_congr (mulEquivProdSup
      (A := W ⊓ centralizer ({u} : Set G)) (B := zpowers u) hzu_cent hdisj).toEquiv,
      Nat.card_prod, hzcard, mul_comm]
  have hYC' : zpowers u ⊔ (W ⊓ centralizer ({u} : Set G)) ≤ centralizer ({u} : Set G) := by
    refine sup_le ?_ inf_le_right
    rw [zpowers_le]
    exact mem_centralizer_singleton_iff.mpr rfl
  have hYC : (W ⊓ centralizer ({u} : Set G)) ⊔ zpowers u ≤ centralizer ({u} : Set G) := by
    rwa [hYsup]
  have hYle : Nat.card ↥((W ⊓ centralizer ({u} : Set G)) ⊔ zpowers u) ≤ 2 ^ 11 := by
    rw [hYsup]
    exact h.hyp.card_le_of_isConj huz hYelem hYC'
  have hCle : Nat.card ↥(W ⊓ centralizer ({u} : Set G)) ≤ 2 ^ 10 := by
    have h1 := hYcard
    omega
  refine ⟨le_antisymm hCle hCge, ?_, ?_, ?_⟩
  · rw [hYcard, le_antisymm hCle hCge]
    norm_num
  · rw [hYsup]
    exact hYelem
  · rw [hYsup]
    exact hYC'


private theorem card_inf_L (h : WHyp G L A T z t W W₁ W₂) {Y' : Subgroup G}
    (hY'P : Y' ≤ L ⊔ zpowers z) (hY'elem : IsElementaryAbelian 2 ↥Y')
    (hcard : Nat.card ↥Y' = 2 ^ 11) :
    Nat.card ↥(Y' ⊓ L) = 2 ^ 10 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzcent : zpowers z ≤ centralizer (L : Set G) :=
    le_centralizer_zpowers_of_centralizer_eq h.hyp.set.centralizer_z
  have hznorm : zpowers z ≤ normalizer (L : Set G) :=
    hzcent.trans (Subgroup.centralizer_le_normalizer (L : Set G))
  let P : Subgroup G := L ⊔ zpowers z
  have hLP : L ≤ P := le_sup_left
  have hPn : P ≤ normalizer (L : Set G) := sup_le Subgroup.le_normalizer hznorm
  haveI : (L.subgroupOf P).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hPn
  let q : ↥Y' →* P ⧸ (L.subgroupOf P) :=
    (QuotientGroup.mk' (L.subgroupOf P)).comp (Subgroup.inclusion hY'P)
  have hker : q.ker = (Y' ⊓ L).subgroupOf Y' := by
    rw [show q = (QuotientGroup.mk' (L.subgroupOf P)).comp (Subgroup.inclusion hY'P) from rfl,
      ← MonoidHom.comap_ker, QuotientGroup.ker_mk', Subgroup.comap_inclusion_subgroupOf]
    ext y
    simp [Subgroup.mem_subgroupOf]
  have hPcard : Nat.card ↥P = 2 * Nat.card ↥L := by
    have h1 := GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer L (zpowers z)
      hznorm h.hyp.set.disjoint
    rw [h1, Nat.card_zpowers,
      orderOf_eq_prime (by rw [pow_two]; exact h.hyp.set.z_sq) h.hyp.set.z_ne]
    ring
  have hquotcard : Nat.card (P ⧸ (L.subgroupOf P)) = 2 := by
    have h1 : Nat.card ↥P = Nat.card (P ⧸ (L.subgroupOf P)) * Nat.card ↥(L.subgroupOf P) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup (L.subgroupOf P)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLP).toEquiv] at h1
    have h2 : Nat.card (P ⧸ (L.subgroupOf P)) * Nat.card ↥L = 2 * Nat.card ↥L := by
      rw [← h1, hPcard]
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥L)) h2
  have hrange : Nat.card ↥q.range ≤ 2 := by
    have h1 : Nat.card ↥q.range ≤ Nat.card (P ⧸ (L.subgroupOf P)) :=
      Nat.card_le_card_of_injective (fun x : ↥q.range => (x.1 : P ⧸ (L.subgroupOf P)))
        (fun x y hxy => Subtype.ext hxy)
    omega
  have hUelem : IsElementaryAbelian 2 ↥(Y' ⊓ L) := hY'elem.of_le inf_le_left
  have hUle : Nat.card ↥(Y' ⊓ L) ≤ 2 ^ 10 := h.hyp.card_le_of_le_L hUelem inf_le_right
  have hcardY' : Nat.card ↥Y' = Nat.card ↥(Y' ⊓ L) * Nat.card ↥q.range := by
    have h1 : Nat.card ↥Y' = Nat.card ↥q.ker * Nat.card ↥q.range :=
      (Subgroup.card_ker_mul_card_range q).symm
    rw [h1, hker]
    congr 1
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : Y' ⊓ L ≤ Y')).toEquiv
  have hge : 2 ^ 10 ≤ Nat.card ↥(Y' ⊓ L) := by
    have h2 : 2 ^ 11 ≤ Nat.card ↥(Y' ⊓ L) * 2 := by
      rw [← hcard, hcardY']
      exact Nat.mul_le_mul_left _ hrange
    omega
  omega

theorem WHyp.exists_conj_of_isConj (h : WHyp G L A T z t W W₁ W₂) {u : G}
    (hu : u ∈ normalizer (W : Set G)) (huz : IsConj z u) :
    ∃ g ∈ normalizer (W : Set G), g * z * g⁻¹ = u := by
  classical
  have hz2 : z * z = 1 := h.hyp.set.z_sq
  obtain ⟨h₀, hh₀⟩ := isConj_iff.1 huz
  have hu2 : u * u = 1 := by
    rw [← hh₀]
    calc (h₀ * z * h₀⁻¹) * (h₀ * z * h₀⁻¹) = h₀ * (z * z) * h₀⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  have huW : u ∉ W := fun hW => h.not_isConj hW huz
  haveI hWelem : IsElementaryAbelian 2 ↥W := h.elemAb
  haveI hWcomm : IsMulCommutative ↥W := hWelem.toIsMulCommutative
  haveI hzu_elem : IsElementaryAbelian 2 ↥(zpowers u) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (p := 2) (by rw [pow_two]; exact hu2)
  let C : Subgroup G := W ⊓ centralizer ({u} : Set G)
  let Y : Subgroup G := C ⊔ zpowers u
  obtain ⟨hCcard, hYcard, hYelem, hYC⟩ := card_inf_centralizer h hu huz hu2 huW
  have hzcard : Nat.card ↥(zpowers u) = 2 := by
    have h1 : u ^ 2 = 1 := by rw [pow_two]; exact hu2
    rw [Nat.card_zpowers, orderOf_eq_prime h1 (fun h1 => huW (h1 ▸ one_mem W))]
  let Y' : Subgroup G := Y.map (MulAut.conj h₀⁻¹).toMonoidHom
  have hY'card : Nat.card ↥Y' = 2 ^ 11 := by
    rw [show Y' = Y.map (MulAut.conj h₀⁻¹).toMonoidHom from rfl,
      Subgroup.card_map_of_injective (MulAut.conj h₀⁻¹).injective, hYcard]
  have hY'elem : IsElementaryAbelian 2 ↥Y' := by
    rw [show Y' = Y.map (MulAut.conj h₀⁻¹).toMonoidHom from rfl]
    exact IsElementaryAbelian.map (MulAut.conj h₀⁻¹).toMonoidHom
  have hmemY' : ∀ x : G, x ∈ Y' ↔ h₀ * x * h₀⁻¹ ∈ Y := by
    intro x
    rw [show Y' = Y.map (MulAut.conj h₀⁻¹).toMonoidHom from rfl, Subgroup.mem_map_equiv,
      MulAut.conj_symm_apply, inv_inv]
  have hY'P : Y' ≤ L ⊔ zpowers z := by
    intro x hx
    have hxY : h₀ * x * h₀⁻¹ ∈ Y := (hmemY' x).1 hx
    have hxcent : h₀ * x * h₀⁻¹ ∈ centralizer ({u} : Set G) := hYC hxY
    have hzc : x * z = z * x := by
      have hucomm : (h₀ * x * h₀⁻¹) * u = u * (h₀ * x * h₀⁻¹) :=
        mem_centralizer_singleton_iff.mp hxcent
      have hzeq : z = h₀⁻¹ * u * h₀ := by rw [← hh₀]; group
      calc x * z = x * (h₀⁻¹ * u * h₀) := by rw [hzeq]
        _ = h₀⁻¹ * ((h₀ * x * h₀⁻¹) * u) * h₀ := by group
        _ = h₀⁻¹ * (u * (h₀ * x * h₀⁻¹)) * h₀ := by rw [hucomm]
        _ = (h₀⁻¹ * u * h₀) * x := by group
        _ = z * x := by rw [hzeq]
    rw [← h.hyp.set.centralizer_z]
    exact mem_centralizer_singleton_iff.mpr hzc
  have hUcard : Nat.card ↥(Y' ⊓ L) = 2 ^ 10 := card_inf_L h hY'P hY'elem hY'card
  have hUelem : IsElementaryAbelian 2 ↥(Y' ⊓ L) := hY'elem.of_le inf_le_left
  obtain ⟨l, hlL, hlcong⟩ :=
    h.hyp.exists_conj_eq_A hUelem inf_le_right hUcard
  let g : G := h₀ * l⁻¹
  have hgz : g * z * g⁻¹ = u := by
    have hcomm : Commute l z := h.hyp.commute_of_mem hlL
    have hlinv : l⁻¹ * z * l = z := by
      rw [hcomm.inv_left.eq]
      group
    calc g * z * g⁻¹ = h₀ * (l⁻¹ * z * l) * h₀⁻¹ := by
          show (h₀ * l⁻¹) * z * (h₀ * l⁻¹)⁻¹ = h₀ * (l⁻¹ * z * l) * h₀⁻¹
          group
      _ = h₀ * z * h₀⁻¹ := by rw [hlinv]
      _ = u := hh₀
  have hgA : ∀ a ∈ A, g * a * g⁻¹ ∈ Y := by
    intro a ha
    have hmem : l⁻¹ * a * l ∈ Y' ⊓ L := by
      refine (hlcong (l⁻¹ * a * l)).2 ?_
      have h1 : l * (l⁻¹ * a * l) * l⁻¹ = a := by group
      rw [h1]
      exact ha
    have hmem2 : h₀ * (l⁻¹ * a * l) * h₀⁻¹ ∈ Y := (hmemY' _).1 hmem.1
    have hgAeq : g * a * g⁻¹ = h₀ * (l⁻¹ * a * l) * h₀⁻¹ := by
      show (h₀ * l⁻¹) * a * (h₀ * l⁻¹)⁻¹ = h₀ * (l⁻¹ * a * l) * h₀⁻¹
      group
    rw [hgAeq]
    exact hmem2
  let Cg : Subgroup G := A.map (MulAut.conj g).toMonoidHom
  have hCgcard : Nat.card ↥Cg = 2 ^ 10 := by
    rw [show Cg = A.map (MulAut.conj g).toMonoidHom from rfl,
      Subgroup.card_map_of_injective (MulAut.conj g).injective, h.hyp.jc.module.card]
  have hCgY : Cg ≤ Y := by
    rintro _ ⟨a, ha, rfl⟩
    exact hgA a ha
  have huCg : u ∉ Cg := by
    rintro ⟨a, ha, hga⟩
    have h1 : g⁻¹ * u * g = a := by
      rw [← hga, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have h2 : g⁻¹ * u * g = z := by rw [← hgz]; group
    exact h.hyp.z_not_mem_L (show z ∈ L from (h2.symm.trans h1) ▸ h.hyp.jc.le ha)
  have hu_cent_Cg : u ∈ centralizer (Cg : Set G) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    have hza : z * a * z⁻¹ = a := by
      rw [show z * a = a * z from (h.hyp.commute_of_mem (h.hyp.jc.le ha)).symm]
      group
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    show (g * a * g⁻¹) * u = u * (g * a * g⁻¹)
    calc (g * a * g⁻¹) * u = (g * a * g⁻¹) * (g * z * g⁻¹) := by rw [hgz]
      _ = g * (a * z) * g⁻¹ := by group
      _ = g * (z * a) * g⁻¹ := by
          rw [show a * z = z * a from h.hyp.commute_of_mem (h.hyp.jc.le ha)]
      _ = (g * z * g⁻¹) * (g * a * g⁻¹) := by group
      _ = u * (g * a * g⁻¹) := by rw [hgz]
  have hzu_norm : zpowers u ≤ normalizer (Cg : Set G) :=
    zpowers_le.2 (Subgroup.centralizer_le_normalizer (Cg : Set G) hu_cent_Cg)
  have hdisjCg : Disjoint Cg (zpowers u) := by
    rw [disjoint_iff]
    refine le_bot_iff.1 ?_
    intro x hx
    rcases eq_one_or_eq_of_mem_zpowers hu2 hx.2 with rfl | rfl
    · exact one_mem _
    · exact absurd hx.1 huCg
  have hcardsup : Nat.card ↥(Cg ⊔ zpowers u) = 2 ^ 11 := by
    rw [GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer Cg (zpowers u)
      hzu_norm hdisjCg, hCgcard, hzcard]
    norm_num
  have hYeq : Y = Cg ⊔ zpowers u := by
    refine (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
    · exact sup_le hCgY le_sup_right
    · rw [hcardsup, hYcard]
  have hC_le_Cg : C ≤ Cg := by
    intro x hx
    by_contra hxCg
    have hxY : x ∈ Y := by
      rw [show Y = C ⊔ zpowers u from rfl]
      exact mem_sup_left hx
    have hxmul : x ∈ (Cg : Set G) * (zpowers u : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left Cg (zpowers u) hzu_norm, ← hYeq]
      exact hxY
    obtain ⟨c, hc, t, ht, hct⟩ := hxmul
    rcases eq_one_or_eq_of_mem_zpowers hu2 ht with ht1 | htu
    · exact hxCg (by simpa [← hct, ht1] using hc)
    · rw [htu] at hct
      obtain ⟨a, ha, rfl⟩ := hc
      have hxconj : IsConj z x := by
        obtain ⟨r, -, hrz⟩ := h.e2.conj_surj a ha
        have haz : a * z = z * a := h.hyp.commute_of_mem (h.hyp.jc.le ha)
        refine isConj_iff.2 ⟨g * r, ?_⟩
        calc (g * r) * z * (g * r)⁻¹ = g * (r * z * r⁻¹) * g⁻¹ := by group
          _ = g * (z * a) * g⁻¹ := by rw [hrz]
          _ = g * (a * z) * g⁻¹ := by rw [haz]
          _ = x := by
              rw [← hct]
              show g * (a * z) * g⁻¹ = g * a * g⁻¹ * u
              rw [← hgz]
              group
      exact h.not_isConj hx.1 hxconj
  have hCeq : C = Cg := Subgroup.eq_of_le_of_card_ge hC_le_Cg (by rw [hCgcard, hCcard])
  have hWsup_cent : W ⊔ zpowers u ≤ centralizer (C : Set G) := by
    refine sup_le ?_ ?_
    · intro w hw
      rw [mem_centralizer_iff]
      intro c hc
      exact congrArg Subtype.val (mul_comm' ⟨c, hc.1⟩ ⟨w, hw⟩)
    · rw [zpowers_le, mem_centralizer_iff]
      intro c hc
      exact mem_centralizer_singleton_iff.mp hc.2
  have hdisjWu : Disjoint W (zpowers u) := by
    rw [disjoint_iff]
    refine le_bot_iff.1 ?_
    intro x hx
    rcases eq_one_or_eq_of_mem_zpowers hu2 hx.2 with rfl | rfl
    · exact one_mem _
    · exact absurd hx.1 huW
  have hWsupcard : Nat.card ↥(W ⊔ zpowers u) = 2 ^ 21 := by
    rw [GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer W (zpowers u)
      (zpowers_le.2 hu) hdisjWu, h.e3.card, hzcard]
    norm_num
  have hWsup2 : IsPGroup 2 ↥(W ⊔ zpowers u) :=
    (IsElementaryAbelian.isPGroup 2 ↥W).to_sup_of_normal_left'
      (IsElementaryAbelian.isPGroup 2 ↥(zpowers u)) (zpowers_le.2 hu)
  let P : Subgroup G := (W ⊔ zpowers u).map (MulAut.conj g⁻¹).toMonoidHom
  have hPcard : Nat.card ↥P = 2 ^ 21 := by
    rw [show P = (W ⊔ zpowers u).map (MulAut.conj g⁻¹).toMonoidHom from rfl,
      Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hWsupcard]
  have hP2 : IsPGroup 2 ↥P := by
    rw [show P = (W ⊔ zpowers u).map (MulAut.conj g⁻¹).toMonoidHom from rfl]
    exact hWsup2.map (MulAut.conj g⁻¹).toMonoidHom
  have hPC : P ≤ centralizer (A : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_iff]
    intro a ha
    have hxcent : x ∈ centralizer (C : Set G) := hWsup_cent hx
    have hga : g * a * g⁻¹ ∈ C := by
      rw [hCeq]
      exact ⟨a, ha, MulAut.conj_apply g a⟩
    have hcomm : (g * a * g⁻¹) * x = x * (g * a * g⁻¹) :=
      mem_centralizer_iff.mp hxcent (g * a * g⁻¹) hga
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc a * (g⁻¹ * x * g⁻¹⁻¹) = g⁻¹ * ((g * a * g⁻¹) * x) * g := by group
      _ = g⁻¹ * (x * (g * a * g⁻¹)) * g := by rw [hcomm]
      _ = (g⁻¹ * x * g⁻¹⁻¹) * a := by group
  obtain ⟨c, hcCent, hcP⟩ := h.exists_conj_le_R₀ hP2 hPC
  have hcPeq : P.map (MulAut.conj c).toMonoidHom = R₀ A z := by
    have hle : P.map (MulAut.conj c).toMonoidHom ≤ R₀ A z := by
      rintro _ ⟨p, hp, rfl⟩
      exact hcP p hp
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj c).injective, hPcard, h.e2.card_R₀]
  have hk_sup : (W ⊔ zpowers u).map (MulAut.conj (c * g⁻¹)).toMonoidHom = R₀ A z := by
    have h1 : (W ⊔ zpowers u).map (MulAut.conj (c * g⁻¹)).toMonoidHom =
        ((W ⊔ zpowers u).map (MulAut.conj g⁻¹).toMonoidHom).map
          (MulAut.conj c).toMonoidHom := by
      rw [Subgroup.map_map]
      congr 1
      ext x
      rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom,
        MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply]
      group
    rw [h1, hcPeq]
  have hkW : W.map (MulAut.conj (c * g⁻¹)).toMonoidHom ≤ R₀ A z := by
    have h1 : W.map (MulAut.conj (c * g⁻¹)).toMonoidHom ≤
        (W ⊔ zpowers u).map (MulAut.conj (c * g⁻¹)).toMonoidHom :=
      Subgroup.map_mono le_sup_left
    rwa [hk_sup] at h1
  have hkWcard : Nat.card ↥(W.map (MulAut.conj (c * g⁻¹)).toMonoidHom) = 2 ^ 20 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj (c * g⁻¹)).injective, h.e3.card]
  have hkWcomm : ∀ a ∈ W.map (MulAut.conj (c * g⁻¹)).toMonoidHom,
      ∀ b ∈ W.map (MulAut.conj (c * g⁻¹)).toMonoidHom, a * b = b * a := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    calc (c * g⁻¹) * x * (c * g⁻¹)⁻¹ * ((c * g⁻¹) * y * (c * g⁻¹)⁻¹)
        = (c * g⁻¹) * (x * y) * (c * g⁻¹)⁻¹ := by group
      _ = (c * g⁻¹) * (y * x) * (c * g⁻¹)⁻¹ := by
          have hxy : x * y = y * x :=
            congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥W) ⟨y, hy⟩)
          rw [hxy]
      _ = (c * g⁻¹) * y * (c * g⁻¹)⁻¹ * ((c * g⁻¹) * x * (c * g⁻¹)⁻¹) := by group
  have hWeq : W.map (MulAut.conj (c * g⁻¹)).toMonoidHom = W :=
    h.eq_of_le_R₀ hkW hkWcomm hkWcard
  have hk_norm : c * g⁻¹ ∈ normalizer (W : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq]
    exact hWeq
  have hku_R₀ : (c * g⁻¹) * u * (c * g⁻¹)⁻¹ ∈ R₀ A z := by
    have h1 : (c * g⁻¹) * u * (c * g⁻¹)⁻¹ ∈
        (W ⊔ zpowers u).map (MulAut.conj (c * g⁻¹)).toMonoidHom :=
      Subgroup.mem_map_of_mem _ (mem_sup_right (mem_zpowers u))
    rwa [hk_sup] at h1
  have hku_W : (c * g⁻¹) * u * (c * g⁻¹)⁻¹ ∉ W := by
    intro hmem
    apply huW
    have hkinv : (c * g⁻¹)⁻¹ ∈ normalizer (W : Set G) := inv_mem hk_norm
    have hmem' : (c * g⁻¹)⁻¹ * ((c * g⁻¹) * u * (c * g⁻¹)⁻¹) * (c * g⁻¹) ∈ W := by
      have h := (mem_normalizer_iff.1 hkinv ((c * g⁻¹) * u * (c * g⁻¹)⁻¹)).1 hmem
      rwa [inv_inv] at h
    have h1 : u = (c * g⁻¹)⁻¹ * ((c * g⁻¹) * u * (c * g⁻¹)⁻¹) * (c * g⁻¹) := by group
    rw [h1]
    exact hmem'
  have hku2 : ((c * g⁻¹) * u * (c * g⁻¹)⁻¹) * ((c * g⁻¹) * u * (c * g⁻¹)⁻¹) = 1 := by
    calc ((c * g⁻¹) * u * (c * g⁻¹)⁻¹) * ((c * g⁻¹) * u * (c * g⁻¹)⁻¹)
        = (c * g⁻¹) * (u * u) * (c * g⁻¹)⁻¹ := by group
      _ = 1 := by rw [hu2]; group
  have hza : z * ((c * g⁻¹) * u * (c * g⁻¹)⁻¹) ∈ A :=
    h.mul_mem_A_of_mul_self hku_R₀ hku_W hku2
  have hkua : (c * g⁻¹) * u * (c * g⁻¹)⁻¹ = z * (z * ((c * g⁻¹) * u * (c * g⁻¹)⁻¹)) := by
    rw [← mul_assoc, hz2, one_mul]
  obtain ⟨r, hrR, hrz⟩ := h.e2.conj_surj (z * ((c * g⁻¹) * u * (c * g⁻¹)⁻¹)) hza
  have hrN : r ∈ normalizer (W : Set G) :=
    h.e3.M_le ((inf_le_left : R₀ A z ≤ M A z) hrR)
  have hrz' : r * z * r⁻¹ = (c * g⁻¹) * u * (c * g⁻¹)⁻¹ := hrz.trans hkua.symm
  have hkinv : (c * g⁻¹)⁻¹ ∈ normalizer (W : Set G) := inv_mem hk_norm
  refine ⟨(c * g⁻¹)⁻¹ * r, mul_mem hkinv hrN, ?_⟩
  calc ((c * g⁻¹)⁻¹ * r) * z * ((c * g⁻¹)⁻¹ * r)⁻¹
      = (c * g⁻¹)⁻¹ * (r * z * r⁻¹) * (c * g⁻¹) := by group
    _ = (c * g⁻¹)⁻¹ * ((c * g⁻¹) * u * (c * g⁻¹)⁻¹) * (c * g⁻¹) := by rw [hrz']
    _ = u := by group

end CFSG.EvenSporadicStandard.Co2Std.Exclusion
