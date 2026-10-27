module

public import CFSG.LocalAnalysis.GH72.Sec2Step
public import CFSG.LocalAnalysis.GH72.Signalizer
public import CFSG.LocalAnalysis.GH72.StrongEmbed
public import CFSG.LocalAnalysis.GH72.Sec4Basic
public import CFSG.LocalAnalysis.ABGTheoremB.IV1
public import CFSG.LocalAnalysis.GH72.GWTwoExtension
public import CFSG.LocalAnalysis.GH72.Alignment
public import CFSG.LocalAnalysis.GH72.G3a
import CFSG.GroupTheory.OddInversion
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorNontrivial

public section

namespace CFSG.GH72

open Subgroup

open CFSG.ABGLocalTools (IsSylowOf isSylowOf_iff)
open CFSG.CGT.Foote81L6 (mem_sup_iff_of_le_normalizer le_normalizer_of_comm)
open CFSG.CGT.Foote81L6.TStruct (mem_map_conj mem_normalizer_of_map_conj_eq
  map_conj_eq_self_of_mem_normalizer)

section Helpers

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_O_of_le_of_le_normalizer {N H : Subgroup G} (hNH : N ≤ H)
    (hHN : H ≤ normalizer (N : Set G)) (hodd : Odd (Nat.card N)) : N ≤ O H := by
  have hn : (N.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hNH).mpr hHN
  have ho : Odd (Nat.card (N.subgroupOf H)) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hNH).toEquiv]
  have hle : N.subgroupOf H ≤ CFSG.oddCore H := le_sSup ⟨hn, ho⟩
  intro n hn'
  exact ⟨⟨n, hNH hn'⟩, hle (show (⟨n, hNH hn'⟩ : H) ∈ N.subgroupOf H from hn'), rfl⟩

theorem O_inf_le_O_of_le {K L : Subgroup G} (hLK : L ≤ K) : O K ⊓ L ≤ O L :=
  le_O_of_le_of_le_normalizer inf_le_right
    (fun _ hg => inf_normalizer_le_normalizer_inf ⟨le_normalizer_O K (hLK hg), le_normalizer hg⟩)
    ((card_O_odd K).of_dvd_nat (card_dvd_of_le inf_le_left))

theorem mem_normalizer_of_forall_conj_mem {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ normalizer (H : Set G) := by
  have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  refine mem_normalizer_of_map_conj_eq (eq_of_le_of_card_ge hle ?_)
  rw [card_map_of_injective (MulAut.conj g).injective]

theorem conj_mem_O_C {g x u : G} (hu : u ∈ O (C x)) : g * u * g⁻¹ ∈ O (C (g * x * g⁻¹)) := by
  have hN : (O (C x)).map (MulAut.conj g).toMonoidHom ≤ O (C (g * x * g⁻¹)) := by
    refine le_O_of_le_of_le_normalizer ?_ ?_ ?_
    · rintro _ ⟨v, hv, rfl⟩
      have hvx : v * x = x * v := mem_centralizer_singleton_iff.mp (map_subtype_le _ hv)
      rw [mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc g * v * g⁻¹ * (g * x * g⁻¹) = g * (v * x) * g⁻¹ := by group
        _ = g * (x * v) * g⁻¹ := by rw [hvx]
        _ = g * x * g⁻¹ * (g * v * g⁻¹) := by group
    · intro h hh
      have hk : g⁻¹ * h * g ∈ C x := by
        rw [mem_centralizer_singleton_iff] at hh ⊢
        calc g⁻¹ * h * g * x = g⁻¹ * (h * (g * x * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * x * g⁻¹) * h) * g := by rw [hh]
          _ = x * (g⁻¹ * h * g) := by group
      have hkN := le_normalizer_O (C x) hk
      rw [mem_normalizer_iff] at hkN ⊢
      intro n
      rw [mem_map_conj, mem_map_conj, hkN]
      constructor <;> intro hn
      · convert hn using 1
        group
      · convert hn using 1
        group
    · rw [card_map_of_injective (MulAut.conj g).injective]
      exact card_O_odd _
  exact hN ⟨u, hu, rfl⟩

omit [Finite G] in
theorem mem_normalizer_iSup_of_forall {ι : Sort*} {H : ι → Subgroup G} {g : G}
    (h : ∀ i, g ∈ normalizer (H i : Set G)) : g ∈ normalizer ((⨆ i, H i : Subgroup G) : Set G) := by
  apply mem_normalizer_of_map_conj_eq
  rw [Subgroup.map_iSup]
  exact iSup_congr fun i => map_conj_eq_self_of_mem_normalizer (h i)

omit [Finite G] in
theorem normalizer_le_normalizer_O (D : Subgroup G) :
    normalizer (D : Set G) ≤ normalizer (O D : Set G) :=
  CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.normalizer_normalizes_oddCore_image D

theorem normalizer_le_normalizer_O2 (D : Subgroup G) :
    normalizer (D : Set G) ≤ normalizer (O2 D : Set G) := by
  intro s hs
  obtain ⟨phi, hphi⟩ : ∃ phi : MulAut D, phi = D.normalizerMonoidHom ⟨s, hs⟩ := ⟨_, rfl⟩
  have hhom : (MulAut.conj s).toMonoidHom.comp D.subtype = D.subtype.comp phi.toMonoidHom := by
    ext d
    rw [hphi]
    rfl
  set S : Set (Subgroup D) := {N : Subgroup D | N.Normal ∧ ∃ n : ℕ, N.index = 2 ^ n} with hS
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  change ((sInf S).map D.subtype).map (MulAut.conj s).toMonoidHom = (sInf S).map D.subtype
  rw [Subgroup.map_map, hhom, ← Subgroup.map_map]
  congr 1
  have hle : (sInf S).map phi.toMonoidHom ≤ sInf S := by
    refine le_sInf fun N hN => map_le_iff_le_comap.mpr (sInf_le ?_)
    obtain ⟨hNn, n, hn⟩ := hN
    exact ⟨hNn.comap _, n, by rw [index_comap_of_surjective _ phi.surjective, hn]⟩
  exact eq_of_le_of_card_ge hle (by rw [card_map_of_injective phi.injective])

omit [Finite G] in
theorem mem_normalizer_sup_of {H K : Subgroup G} {g : G} (hH : g ∈ normalizer (H : Set G))
    (hK : g ∈ normalizer (K : Set G)) : g ∈ normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq] at hH hK ⊢
  rw [Subgroup.map_sup, hH, hK]

theorem mem_normalizer_centralizer_of {Z : Subgroup G} {g : G} (hg : g ∈ normalizer (Z : Set G)) :
    g ∈ normalizer (centralizer (Z : Set G) : Set G) := by
  apply mem_normalizer_of_forall_conj_mem
  intro h hh
  rw [mem_centralizer_iff] at hh ⊢
  intro x hx
  have hx' : g⁻¹ * x * g ∈ Z := by
    have := (mem_normalizer_iff.mp (inv_mem hg) x).1 hx
    rwa [inv_inv] at this
  have h1 := hh _ hx'
  calc x * (g * h * g⁻¹) = g * ((g⁻¹ * x * g) * h) * g⁻¹ := by group
    _ = g * (h * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
    _ = g * h * g⁻¹ * x := by group

theorem le_O_sup_inf_normalizer {L R : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hR : IsSylowOf p R (O L)) : L ≤ O L ⊔ (L ⊓ normalizer (R : Set G)) := by
  intro g hg
  have hRg : R.map (MulAut.conj g).toMonoidHom ≤ O L := by
    rintro _ ⟨r, hr, rfl⟩
    exact (mem_normalizer_iff.mp (le_normalizer_O L hg) r).1 (hR.le hr)
  obtain ⟨c, hc, hcR⟩ := exists_mem_map_conj_le_of_isSylowOf hR hRg (hR.isPGroup.map _)
  have heq : (R.map (MulAut.conj g).toMonoidHom).map (MulAut.conj c).toMonoidHom = R :=
    eq_of_le_of_card_ge hcR (by rw [card_map_of_injective (MulAut.conj c).injective,
      card_map_of_injective (MulAut.conj g).injective])
  have hcg : c * g ∈ normalizer (R : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq]
    calc R.map (MulAut.conj (c * g)).toMonoidHom
        = (R.map (MulAut.conj g).toMonoidHom).map (MulAut.conj c).toMonoidHom := by
          rw [Subgroup.map_map]
          congr 1
          ext x
          simp [mul_assoc]
      _ = R := heq
  have e : g = c⁻¹ * (c * g) := by group
  rw [e]
  exact mul_mem (mem_sup_left (inv_mem hc))
    (mem_sup_right (mem_inf.mpr ⟨mul_mem ((map_subtype_le _) hc) hg, hcg⟩))

end Helpers

section XYGen

variable {G : Type} [Group G] [Finite G] {X Y : Subgroup G}

omit [Finite G] in
private theorem xySup_le_of {f : G → G → Subgroup G} {N : Subgroup G}
    (h : ∀ x ∈ X, x ≠ 1 → ∀ y ∈ Y, y ≠ 1 → f x y ≤ N) : xySup X Y f ≤ N :=
  xySupOf_le (X₀ := X) (Y₀ := Y) (f := f) h

omit [Finite G] in
private theorem commutator_self_le' (H : Subgroup G) : ⁅H, H⁆ ≤ H :=
  commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

omit [Finite G] in
private theorem mem_normalizer_O_C' {g z : G} (h : g * z = z * g) :
    g ∈ normalizer ((O (C z) : Subgroup G) : Set G) :=
  le_normalizer_O (C z) (mem_centralizer_singleton_iff.mpr h)

theorem xyGenerated_of_le_of_isXYBalanced (hX : IsKleinFour X) (hY : IsKleinFour Y)
    (hXY : X ⊓ Y = ⊥) (hYX : Y ≤ centralizer (X : Set G)) (hbal : IsXYBalanced X Y)
    {K : Subgroup G} (hKodd : Odd (Nat.card K)) (hKA : X ⊔ Y ≤ normalizer (K : Set G))
    (hKgen : XYGenerated X Y K) {F : Subgroup G} (hFK : F ≤ K)
    (hFA : X ⊔ Y ≤ normalizer (F : Set G)) : XYGenerated X Y F := by
  have hXab : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := by
    have := hX
    intro a ha b hb
    exact congrArg Subtype.val
      ((IsKleinFour.isMulCommutative (G := X)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hYab : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a := by
    have := hY
    intro a ha b hb
    exact congrArg Subtype.val
      ((IsKleinFour.isMulCommutative (G := Y)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hcX : X ⊔ Y ≤ centralizer (X : Set G) := sup_le
    (fun a ha => mem_centralizer_iff.mpr fun b hb => hXab b hb a ha) hYX
  have hcY : X ⊔ Y ≤ centralizer (Y : Set G) := sup_le (le_centralizer_iff.mp hYX)
    (fun a ha => mem_centralizer_iff.mpr fun b hb => hYab b hb a ha)
  have hcA : X ⊔ Y ≤ centralizer ((X ⊔ Y : Subgroup G) : Set G) :=
    sup_le (le_centralizer_iff.mp hcX) (le_centralizer_iff.mp hcY)
  have hcomm : ∀ a ∈ X ⊔ Y, ∀ b ∈ X ⊔ Y, a * b = b * a := fun a ha b hb =>
    ((mem_centralizer_iff.mp (hcA hb)) a ha)
  have hnotY : ∀ x ∈ X, x ≠ 1 → x ∉ Y := fun x hx hx1 hxY => hx1 (by
    have h : x ∈ X ⊓ Y := mem_inf.mpr ⟨hx, hxY⟩
    rwa [hXY, mem_bot] at h)
  have hnotX : ∀ y ∈ Y, y ≠ 1 → y ∉ X := fun y hy hy1 hyX => hy1 (by
    have h : y ∈ X ⊓ Y := mem_inf.mpr ⟨hyX, hy⟩
    rwa [hXY, mem_bot] at h)
  have hOC : ∀ z : G, O (C z) ≤ C z := fun z => map_subtype_le _
  have hDodd : ∀ D : Subgroup G, D ≤ K → Odd (Nat.card D) := fun D hD =>
    hKodd.of_dvd_nat (card_dvd_of_le hD)
  have hAC : ∀ z ∈ X ⊔ Y, X ⊔ Y ≤ normalizer ((C z : Subgroup G) : Set G) := fun z hz g hg =>
    mem_normalizer_C_of_commute (hcomm g hg z hz)
  have hAO : ∀ z ∈ X ⊔ Y, X ⊔ Y ≤ normalizer ((O (C z) : Subgroup G) : Set G) := fun z hz g hg =>
    mem_normalizer_O_C' (hcomm g hg z hz)
  have hAKC : ∀ z ∈ X ⊔ Y, X ⊔ Y ≤ normalizer ((K ⊓ C z : Subgroup G) : Set G) := fun z hz g hg =>
    inf_normalizer_le_normalizer_inf ⟨hKA hg, hAC z hz hg⟩
  have hinvcomm : ∀ (D : Subgroup G), D ≤ K → ∀ {t u : G}, u ∈ D → t * u * t⁻¹ = u⁻¹ →
      u ∈ ⁅D, zpowers t⁆ := fun D hD _ _ hu h =>
    mem_commutator_zpowers_of_conj_eq_inv (hDodd D hD) hu h
  have h22 := prop_2_2 (K := K) (X := X) (Y := Y) hKodd hX hY hXY hYX hKA
    (fun x y => K ⊓ O (C x) ⊓ O (C y))
    (fun x _ _ y _ _ => inf_le_inf (inf_le_inf_left _ (hOC x)) (hOC y))
    (fun x hx _ y hy _ => by
      refine (normal_subgroupOf_iff_le_normalizer
        (inf_le_inf (inf_le_inf_left _ (hOC x)) (hOC y))).mpr ?_
      intro g hg
      obtain ⟨⟨hgK, hgx⟩, hgy⟩ := hg
      exact inf_normalizer_le_normalizer_inf ⟨inf_normalizer_le_normalizer_inf
        ⟨le_normalizer hgK, mem_normalizer_O_C' (mem_centralizer_singleton_iff.mp hgx)⟩,
        mem_normalizer_O_C' (mem_centralizer_singleton_iff.mp hgy)⟩)
    (fun x hx _ y hy _ g hg => inf_normalizer_le_normalizer_inf
      ⟨inf_normalizer_le_normalizer_inf ⟨hKA hg, hAO x (mem_sup_left hx) hg⟩,
        hAO y (mem_sup_right hy) hg⟩)
    hKgen
    (fun x hx hx1 x' hx' hx'1 y hy hy1 y' hy' hy'1 => by
      constructor
      · rintro g ⟨⟨⟨hgK, hgx⟩, hgy⟩, hgx'⟩
        exact ⟨⟨hgK, hbal.a₁ x hx hx1 x' (mem_sup_left hx') (hnotY x' hx' hx'1)
          (mem_inf.mpr ⟨hgx, hgx'⟩)⟩, hgy⟩
      · rintro g ⟨⟨⟨hgK, hgx⟩, hgy⟩, hgy'⟩
        exact ⟨⟨hgK, hgx⟩, hbal.a₂ y hy hy1 y' (mem_sup_right hy') (hnotX y' hy' hy'1)
          (mem_inf.mpr ⟨hgy, hgy'⟩)⟩)
    (fun x hx hx1 y hy hy1 u hu hXinv hYinv => by
      obtain ⟨x', hx', hx'z⟩ := exists_mem_not_mem_zpowers_of_isKleinFour hX hx hx1
      obtain ⟨y', hy', hy'z⟩ := exists_mem_not_mem_zpowers_of_isKleinFour hY hy hy1
      set D : Subgroup G := K ⊓ C x ⊓ C y with hD
      have hDK : D ≤ K := inf_le_left.trans inf_le_left
      have hDA : X ⊔ Y ≤ normalizer (D : Set G) := fun g hg =>
        inf_normalizer_le_normalizer_inf ⟨hAKC x (mem_sup_left hx) hg,
          hAC y (mem_sup_right hy) hg⟩
      have h1 := hbal.b₁ x hx hx1 D (inf_le_left.trans inf_le_right) (hDodd D hDK) hDA
      have h2 := hbal.b₂ y hy hy1 D inf_le_right (hDodd D hDK) hDA
      have hux : u ∈ O (C x) := h1 (mem_sup_left (commutator_mono le_rfl
        ((zpowers_le).mpr hx') (hinvcomm D hDK hu (hXinv x' hx' hx'z))))
      have huy : u ∈ O (C y) := h2 (mem_sup_left (commutator_mono le_rfl
        ((zpowers_le).mpr hy') (hinvcomm D hDK hu (hYinv y' hy' hy'z))))
      exact ⟨⟨hDK hu, hux⟩, huy⟩)
    (fun x hx hx1 y hy hy1 => by
      constructor
      · intro u hu hYinv
        obtain ⟨y', hy', hy'z⟩ := exists_mem_not_mem_zpowers_of_isKleinFour hY hy hy1
        obtain ⟨huL, huy⟩ := mem_inf.mp hu
        have hKx := hAKC x (mem_sup_left hx)
        have hL1 : ⁅K ⊓ C x, Y⁆ ≤ K ⊓ C x :=
          le_normalizer_iff_commutator_le_left.mp (le_sup_right.trans hKx)
        have huKx : u ∈ K ⊓ C x := hL1 (commutator_self_le' _ huL)
        have hux : u ∈ O (C x) := hbal.b₁ x hx hx1 (K ⊓ C x) inf_le_right
          (hDodd _ inf_le_left) hKx (mem_sup_right huL)
        have hKy := hAKC y (mem_sup_right hy)
        have huKy : u ∈ K ⊓ C y := mem_inf.mpr ⟨(mem_inf.mp huKx).1, huy⟩
        have huy' : u ∈ O (C y) := hbal.b₂ y hy hy1 (K ⊓ C y) inf_le_right
          (hDodd _ inf_le_left) hKy (mem_sup_left (commutator_mono le_rfl
            ((zpowers_le).mpr hy') (hinvcomm _ inf_le_left huKy (hYinv y' hy' hy'z))))
        exact ⟨⟨(mem_inf.mp huKx).1, hux⟩, huy'⟩
      · intro u hu hXinv
        obtain ⟨x', hx', hx'z⟩ := exists_mem_not_mem_zpowers_of_isKleinFour hX hx hx1
        obtain ⟨huL, hux⟩ := mem_inf.mp hu
        have hKy := hAKC y (mem_sup_right hy)
        have hL1 : ⁅K ⊓ C y, X⁆ ≤ K ⊓ C y :=
          le_normalizer_iff_commutator_le_left.mp (le_sup_left.trans hKy)
        have huKy : u ∈ K ⊓ C y := hL1 (commutator_self_le' _ huL)
        have huy : u ∈ O (C y) := hbal.b₂ y hy hy1 (K ⊓ C y) inf_le_right
          (hDodd _ inf_le_left) hKy (mem_sup_right huL)
        have hKx := hAKC x (mem_sup_left hx)
        have huKx : u ∈ K ⊓ C x := mem_inf.mpr ⟨(mem_inf.mp huKy).1, hux⟩
        have hux' : u ∈ O (C x) := hbal.b₁ x hx hx1 (K ⊓ C x) inf_le_right
          (hDodd _ inf_le_left) hKx (mem_sup_left (commutator_mono le_rfl
            ((zpowers_le).mpr hx') (hinvcomm _ inf_le_left huKx (hXinv x' hx' hx'z))))
        exact ⟨⟨(mem_inf.mp huKy).1, hux'⟩, huy⟩)
    (fun p P hp hPp hPK hPA hPgen Q hQP hQA => by
      have hQK : Q ≤ K := hQP.trans hPK
      have hKxy : ∀ {E : Subgroup G}, E ≤ K →
          (fun x y => E ⊓ (K ⊓ O (C x) ⊓ O (C y))) = fun x y => E ⊓ O (C x) ⊓ O (C y) := by
        intro E hE
        funext x y
        rw [← inf_assoc, ← inf_assoc, inf_eq_left.mpr hE]
      by_cases hp2 : p = 2
      · subst hp2
        have hPbot : P = ⊥ := by
          rcases hPp.card_eq_or_dvd with h1 | h2
          · exact card_eq_one.mp h1
          · exact absurd (h2.trans (card_dvd_of_le hPK)) (Nat.two_dvd_ne_zero.mpr
              (Nat.odd_iff.mp hKodd))
        have hQbot : Q = ⊥ := le_bot_iff.mp (hPbot ▸ hQP)
        subst hQbot
        exact le_antisymm bot_le (xySup_le_of fun _ _ _ _ _ _ => inf_le_left)
      · rw [hKxy hPK] at hPgen
        rw [hKxy hQK]
        exact hbal.c p P hp hp2 hPp hPA hPgen Q hQP hQA)
  have hF := h22 F hFK hFA
  have e : (fun x y => F ⊓ (K ⊓ O (C x) ⊓ O (C y))) = fun x y => F ⊓ O (C x) ⊓ O (C y) := by
    funext x y
    rw [← inf_assoc, ← inf_assoc, inf_eq_left.mpr hFK]
  rw [e] at hF
  exact hF

end XYGen

section OddGroups

variable {G : Type} [Group G] [Finite G]

theorem le_of_forall_isSylowOf_normalized {W J A : Subgroup G} (hA2 : IsPGroup 2 A)
    (hAW : A ≤ normalizer (W : Set G)) (hW : Odd (Nat.card W))
    (h : ∀ p : ℕ, p.Prime → ∀ P : Subgroup G, IsSylowOf p P W → A ≤ normalizer (P : Set G) →
      P ≤ J) : W ≤ J := by
  have hrel : (J ⊓ W).relIndex W = 1 := by
    rw [Nat.eq_one_iff_not_exists_prime_dvd]
    intro p hp hdvd
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨P, hP, hAP⟩ := CFSG.ABGTheoremB.exists_isSylowOf_normalized_of_odd hp hA2 hAW hW
    have hPJ : P ≤ J ⊓ W := le_inf (h p hp P hP hAP) hP.le
    exact (isSylowOf_iff.mp hP).2.2 (hdvd.trans (relIndex_dvd_of_le_left W hPJ))
  exact (relIndex_eq_one.mp hrel).trans inf_le_left

omit [Finite G] in
theorem le_inf_centralizer_sup_commutator {D : Subgroup G} (hD : Odd (Nat.card D)) {t : G}
    (ht : orderOf t = 2) (htD : t ∈ normalizer (D : Set G)) :
    D ≤ (D ⊓ C t) ⊔ ⁅D, zpowers t⁆ := by
  intro d hd
  obtain ⟨⟨c, j⟩, ⟨hc, hj⟩, hcj⟩ :=
    (OddInversion.odd_involution_product_decomposition hD ht htD).1.surjOn hd
  simp only at hcj
  rw [← hcj]
  exact mul_mem (mem_sup_left hc)
    (mem_sup_right (mem_commutator_zpowers_of_conj_eq_inv hD hj.1 hj.2))

theorem le_iSup_inf_centralizer {D Z : Subgroup G} (hD : Odd (Nat.card D)) (hZ : IsKleinFour Z)
    (hZD : Z ≤ normalizer (D : Set G)) :
    D ≤ ⨆ (z : G) (_ : z ∈ Z) (_ : z ≠ 1), D ⊓ C z := by
  have h := le_iSup_centralizers hD hZ (ι := MonoidHom.id G) Function.injective_id
    (by rw [Subgroup.map_id]; exact hZD)
  refine h.trans (iSup_le fun z => ?_)
  exact le_iSup_of_le (z : G) (le_iSup_of_le z.2.1 (le_iSup_of_le z.2.2 le_rfl))

end OddGroups

section Side

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_centralizer_of_isKleinFour {Z' : Subgroup G} (hZ' : IsKleinFour Z') {z' z'' g : G}
    (hz' : z' ∈ Z') (hz'' : z'' ∈ Z') (hz'1 : z' ≠ 1) (hz''z : z'' ∉ zpowers z')
    (h1 : g * z' = z' * g) (h2 : g * z'' = z'' * g) : g ∈ centralizer (Z' : Set G) := by
  rw [mem_centralizer_iff]
  intro w hw
  have hz''1 : z'' ≠ 1 := fun h => hz''z (h ▸ one_mem _)
  have hne : z' ≠ z'' := fun h => hz''z (h ▸ mem_zpowers z')
  by_cases hw1 : w = 1
  · rw [hw1, one_mul, mul_one]
  by_cases hwz' : w = z'
  · rw [hwz']
    exact h1.symm
  by_cases hwz'' : w = z''
  · rw [hwz'']
    exact h2.symm
  have := hZ'
  have h := IsKleinFour.eq_mul_of_ne_all (G := Z') (x := ⟨z', hz'⟩) (y := ⟨z'', hz''⟩)
    (z := ⟨w, hw⟩) (fun h => hz'1 (congrArg Subtype.val h))
    (fun h => hz''1 (congrArg Subtype.val h)) (fun h => hne (congrArg Subtype.val h))
    (fun h => hw1 (congrArg Subtype.val h)) (fun h => hwz' (congrArg Subtype.val h))
    (fun h => hwz'' (congrArg Subtype.val h))
  have hw' : w = z' * z'' := congrArg Subtype.val h
  rw [hw']
  calc z' * z'' * g = z' * (g * z'') := by rw [mul_assoc, h2]
    _ = g * (z' * z'') := by rw [← mul_assoc, ← h1, mul_assoc]

omit [Finite G] in
theorem mem_centralizer_sup_of {Z Z' : Subgroup G} {g : G} (h : g ∈ centralizer (Z : Set G))
    (h' : g ∈ centralizer (Z' : Set G)) : g ∈ centralizer ((Z ⊔ Z' : Subgroup G) : Set G) := by
  have : zpowers g ≤ centralizer ((Z ⊔ Z' : Subgroup G) : Set G) :=
    le_centralizer_iff.mpr (sup_le (le_centralizer_iff.mp ((zpowers_le).mpr h))
      (le_centralizer_iff.mp ((zpowers_le).mpr h')))
  exact this (mem_zpowers g)

theorem commutator_O_inf_centralizer_le_of {A W Z Z' : Subgroup G}
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hZZ' : Z ⊔ Z' = A)
    (hb : ∀ z' ∈ Z', z' ≠ 1 → ∀ D : Subgroup G, D ≤ C z' → Odd (Nat.card D) →
      A ≤ normalizer (D : Set G) → ⁅D, Z'⁆ ≤ O (C z'))
    {z : G} (hz : z ∈ Z) (h413 : O (centralizer (Z : Set G)) ⊓ C z ≤ O (C z))
    (hgen : ∀ z' ∈ Z', z' ≠ 1 → C z' ⊓ O (C z) ⊓ O (C z') ≤ W)
    {z' z'' : G} (hz' : z' ∈ Z') (hz'1 : z' ≠ 1) (hz'' : z'' ∈ Z') :
    ⁅O (centralizer (Z : Set G)) ⊓ C z', zpowers z''⁆ ≤ W := by
  set L := centralizer (Z : Set G) with hLdef
  have hZA : Z ≤ A := hZZ' ▸ le_sup_left
  have hZ'A : Z' ≤ A := hZZ' ▸ le_sup_right
  have hDodd := card_O_odd L
  have hAL : A ≤ L := fun g hg => mem_centralizer_iff.mpr fun h hh => hAab h (hZA hh) g hg
  have hAD : A ≤ normalizer (O L : Set G) := hAL.trans (le_normalizer_O L)
  have hDL : O L ≤ L := map_subtype_le _
  have hLz : L ≤ C z := centralizer_le (Set.singleton_subset_iff.mpr hz)
  have hcz : z'' * z' = z' * z'' := hAab _ (hZ'A hz'') _ (hZ'A hz')
  have hD'odd : Odd (Nat.card (O L ⊓ C z' : Subgroup G)) :=
    hDodd.of_dvd_nat (card_dvd_of_le inf_le_left)
  have hAD' : A ≤ normalizer ((O L ⊓ C z' : Subgroup G) : Set G) := fun g hg =>
    inf_normalizer_le_normalizer_inf ⟨hAD hg, mem_normalizer_C_of_commute
      (hAab g hg z' (hZ'A hz'))⟩
  have hz''D' := hAD' (hZ'A hz'')
  refine le_trans (le_inf (le_inf ?_ ?_) ?_) (hgen z' hz' hz'1)
  · exact (commutator_mono inf_le_right ((zpowers_le).mpr
      (mem_centralizer_singleton_iff.mpr hcz))).trans (commutator_self_le' _)
  · refine le_trans (le_inf ?_ ?_) h413
    · exact (le_normalizer_iff_commutator_le_left.mp ((zpowers_le).mpr hz''D')).trans
        inf_le_left
    · exact (commutator_mono (inf_le_left.trans (hDL.trans hLz))
        ((zpowers_le).mpr (hLz (hAL (hZ'A hz''))))).trans (commutator_self_le' _)
  · exact (commutator_mono le_rfl ((zpowers_le).mpr hz'')).trans
      (hb z' hz' hz'1 _ inf_le_right hD'odd hAD')

theorem O_centralizer_le_normalizer_of {A W Z Z' : Subgroup G} (hZ' : IsKleinFour Z')
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hZZ' : Z ⊔ Z' = A)
    (hb : ∀ z' ∈ Z', z' ≠ 1 → ∀ D : Subgroup G, D ≤ C z' → Odd (Nat.card D) →
      A ≤ normalizer (D : Set G) → ⁅D, Z'⁆ ≤ O (C z'))
    {z : G} (hz : z ∈ Z) (h413 : O (centralizer (Z : Set G)) ⊓ C z ≤ O (C z))
    (hgen : ∀ z' ∈ Z', z' ≠ 1 → C z' ⊓ O (C z) ⊓ O (C z') ≤ W)
    (hCA : centralizer (A : Set G) ≤ normalizer (W : Set G)) :
    O (centralizer (Z : Set G)) ≤ normalizer (W : Set G) := by
  set L := centralizer (Z : Set G) with hLdef
  have hZA : Z ≤ A := hZZ' ▸ le_sup_left
  have hZ'A : Z' ≤ A := hZZ' ▸ le_sup_right
  have hDodd := card_O_odd L
  have hAL : A ≤ L := fun g hg => mem_centralizer_iff.mpr fun h hh => hAab h (hZA hh) g hg
  have hAD : A ≤ normalizer (O L : Set G) := hAL.trans (le_normalizer_O L)
  have hDL : O L ≤ L := map_subtype_le _
  refine (le_iSup_inf_centralizer hDodd hZ' (hZ'A.trans hAD)).trans
    (iSup_le fun z' => iSup_le fun hz' => iSup_le fun hz'1 => ?_)
  obtain ⟨z'', hz'', hz''z⟩ := exists_mem_not_mem_zpowers_of_isKleinFour hZ' hz' hz'1
  have hz''1 : z'' ≠ 1 := fun h => hz''z (h ▸ one_mem _)
  have hz''2 : orderOf z'' = 2 := orderOf_eq_two_of_isKleinFour hZ' hz'' hz''1
  have hD'odd : Odd (Nat.card (O L ⊓ C z' : Subgroup G)) :=
    hDodd.of_dvd_nat (card_dvd_of_le inf_le_left)
  have hz''D' : z'' ∈ normalizer ((O L ⊓ C z' : Subgroup G) : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨hAD (hZ'A hz''), mem_normalizer_C_of_commute
      (hAab _ (hZ'A hz'') _ (hZ'A hz'))⟩
  refine (le_inf_centralizer_sup_commutator hD'odd hz''2 hz''D').trans (sup_le ?_ ?_)
  · refine le_trans ?_ hCA
    intro g hg
    have hg' := mem_inf.mp hg
    have hgL : g ∈ L := hDL (mem_inf.mp hg'.1).1
    have hgz' : g * z' = z' * g := mem_centralizer_singleton_iff.mp (mem_inf.mp hg'.1).2
    have hgz'' : g * z'' = z'' * g := mem_centralizer_singleton_iff.mp hg'.2
    rw [← hZZ']
    exact mem_centralizer_sup_of hgL
      (mem_centralizer_of_isKleinFour hZ' hz' hz'' hz'1 hz''z hgz' hgz'')
  · exact (commutator_O_inf_centralizer_le_of hAab hZZ' hb hz h413 hgen hz' hz'1 hz'').trans
      le_normalizer

theorem map_le_of_le_centralizer_of {A W Z Z' L₀ P : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hZ' : IsKleinFour Z') (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hZZ' : Z ⊔ Z' = A)
    (hA2 : IsPGroup 2 A)
    (hb : ∀ z' ∈ Z', z' ≠ 1 → ∀ D : Subgroup G, D ≤ C z' → Odd (Nat.card D) →
      A ≤ normalizer (D : Set G) → ⁅D, Z'⁆ ≤ O (C z'))
    {z : G} (hz : z ∈ Z) (h413 : O (centralizer (Z : Set G)) ⊓ C z ≤ O (C z))
    (hgen : ∀ z' ∈ Z', z' ≠ 1 → C z' ⊓ O (C z) ⊓ O (C z') ≤ W)
    (hOW : O (centralizer (Z : Set G)) ≤ normalizer (W : Set G))
    (hL₀ : L₀ ≤ centralizer (Z : Set G)) (hZ'L₀ : Z' ≤ L₀)
    (hsimple : QuotIs L₀ (O (centralizer (Z : Set G))) (fun L _ => IsSimpleGroup L))
    (hPW : IsSylowOf p P W) (hAP : A ≤ centralizer (P : Set G))
    (hPO : P ≤ O (centralizer (Z : Set G))) :
    ∀ m ∈ L₀, P.map (MulAut.conj m).toMonoidHom ≤ W := by
  set L := centralizer (Z : Set G) with hLdef
  have : Fact p.Prime := ⟨hp⟩
  have hZA : Z ≤ A := hZZ' ▸ le_sup_left
  have hZ'A : Z' ≤ A := hZZ' ▸ le_sup_right
  have hAL : A ≤ L := fun g hg => mem_centralizer_iff.mpr fun h hh => hAab h (hZA hh) g hg
  have hAO : A ≤ normalizer (O L : Set G) := hAL.trans (le_normalizer_O L)
  have hOodd := card_O_odd L
  have hAPn : A ≤ normalizer (P : Set G) := hAP.trans (centralizer_le_normalizer _)
  obtain ⟨R, hR, hPR, hAR⟩ := CFSG.ABGTheoremB.exists_isSylowOf_normalized_ge_of_odd hp hA2 hAO
    hOodd hPO hPW.isPGroup hAPn
  have hRodd : Odd (Nat.card R) := hOodd.of_dvd_nat (card_dvd_of_le hR.le)
  have hRZ' : R ≤ centralizer (Z' : Set G) := by
    have key : ∀ z' ∈ Z', z' ≠ 1 → R ⊓ C z' ≤ centralizer (Z' : Set G) := by
      intro z' hz' hz'1
      obtain ⟨z'', hz'', hz''z⟩ := exists_mem_not_mem_zpowers_of_isKleinFour hZ' hz' hz'1
      have hz''1 : z'' ≠ 1 := fun h => hz''z (h ▸ one_mem _)
      have hz''2 : orderOf z'' = 2 := orderOf_eq_two_of_isKleinFour hZ' hz'' hz''1
      have hR'odd : Odd (Nat.card (R ⊓ C z' : Subgroup G)) :=
        hRodd.of_dvd_nat (card_dvd_of_le inf_le_left)
      have hz''R' : z'' ∈ normalizer ((R ⊓ C z' : Subgroup G) : Set G) :=
        inf_normalizer_le_normalizer_inf ⟨hAR (hZ'A hz''), mem_normalizer_C_of_commute
          (hAab _ (hZ'A hz'') _ (hZ'A hz'))⟩
      have hEW : ⁅R ⊓ C z', zpowers z''⁆ ≤ W :=
        (commutator_mono (inf_le_inf_right _ hR.le) le_rfl).trans
          (commutator_O_inf_centralizer_le_of hAab hZZ' hb hz h413 hgen hz' hz'1 hz'')
      have hER : ⁅R ⊓ C z', zpowers z''⁆ ≤ R :=
        (le_normalizer_iff_commutator_le_left.mp ((zpowers_le).mpr hz''R')).trans inf_le_left
      have hEP : ⁅R ⊓ C z', zpowers z''⁆ ≤ P := by
        have h := hPW.eq_of_le (le_sup_left (b := ⁅R ⊓ C z', zpowers z''⁆))
          (sup_le hPW.le hEW) (hR.isPGroup.to_le (sup_le hPR hER))
        exact le_sup_right.trans h.le
      intro u hu
      obtain ⟨⟨c, j⟩, ⟨hc, hj⟩, hcj⟩ :=
        (OddInversion.odd_involution_product_decomposition hR'odd hz''2 hz''R').1.surjOn hu
      simp only at hcj
      have hjE : j ∈ ⁅R ⊓ C z', zpowers z''⁆ :=
        mem_commutator_zpowers_of_conj_eq_inv hR'odd hj.1 hj.2
      have hjfix : z'' * j * z''⁻¹ = j := by
        have h1 := mem_centralizer_iff.mp (hAP (hZ'A hz'')) j (hEP hjE)
        rw [← h1, mul_inv_cancel_right]
      have hj1 : j = 1 := eq_one_of_conj_eq_self_of_conj_eq_inv hR'odd hj.1 hjfix hj.2
      rw [hj1, mul_one] at hcj
      rw [← hcj]
      have hc' := mem_inf.mp hc
      exact mem_centralizer_of_isKleinFour hZ' hz' hz'' hz'1 hz''z
        (mem_centralizer_singleton_iff.mp (mem_inf.mp hc'.1).2)
        (mem_centralizer_singleton_iff.mp hc'.2)
    exact (le_iSup_inf_centralizer hRodd hZ' (hZ'A.trans hAR)).trans
      (iSup_le fun z' => iSup_le fun hz' => iSup_le fun hz'1 => key z' hz' hz'1)
  set N : Subgroup G := O L ⊔ (L ⊓ centralizer (R : Set G)) with hNdef
  have hLN : L ≤ normalizer (N : Set G) := by
    refine (le_O_sup_inf_normalizer hR).trans (sup_le (le_sup_left.trans le_normalizer) ?_)
    intro g hg
    exact mem_normalizer_sup_of (le_normalizer_O L (mem_inf.mp hg).1)
      (inf_normalizer_le_normalizer_inf ⟨le_normalizer (mem_inf.mp hg).1,
        mem_normalizer_centralizer_of (mem_inf.mp hg).2⟩)
  have hL₀N : L₀ ≤ N := by
    obtain ⟨Lq, _, f, hf, hker, hsimp⟩ := hsimple
    have hNn : (N.subgroupOf L₀).Normal := normal_subgroupOf_of_le_normalizer (hL₀.trans hLN)
    have hNq : ((N.subgroupOf L₀).map f).Normal := hNn.map f hf
    rcases hNq.eq_bot_or_eq_top with h | h
    · exfalso
      have hZ'O : Z' ≤ O L := by
        intro w hw
        have hwN : w ∈ N := mem_sup_right (mem_inf.mpr ⟨hAL (hZ'A hw),
          le_centralizer_iff.mp hRZ' hw⟩)
        have hmem : f ⟨w, hZ'L₀ hw⟩ ∈ (N.subgroupOf L₀).map f := ⟨⟨w, hZ'L₀ hw⟩, hwN, rfl⟩
        rw [h, mem_bot, ← MonoidHom.mem_ker, hker, mem_subgroupOf] at hmem
        exact hmem
      have hdvd := card_dvd_of_le hZ'O
      rw [hZ'.card_four] at hdvd
      exact (Nat.not_even_iff_odd.mpr hOodd) (even_iff_two_dvd.mpr
        ((by norm_num : 2 ∣ 4).trans hdvd))
    · intro m hm
      obtain ⟨n, hn, hfn⟩ : f ⟨m, hm⟩ ∈ (N.subgroupOf L₀).map f := h ▸ mem_top _
      have hk : n⁻¹ * ⟨m, hm⟩ ∈ f.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hfn, inv_mul_cancel]
      rw [hker, mem_subgroupOf] at hk
      have e : m = (n : G) * ((n⁻¹ * ⟨m, hm⟩ : L₀) : G) := by simp
      rw [e]
      exact mul_mem hn (mem_sup_left hk)
  intro m hm
  obtain ⟨o, ho, c, hc, rfl⟩ :=
    (mem_sup_iff_of_le_normalizer (inf_le_left.trans (le_normalizer_O L))).1 (hL₀N hm)
  rintro _ ⟨u, hu, rfl⟩
  have hcu : c * u * c⁻¹ = u := by
    have h1 := mem_centralizer_iff.mp (mem_inf.mp hc).2 u (hPR hu)
    rw [← h1, mul_inv_cancel_right]
  have e : (MulAut.conj (o * c)).toMonoidHom u = o * u * o⁻¹ := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc o * c * u * (o * c)⁻¹ = o * (c * u * c⁻¹) * o⁻¹ := by group
      _ = o * u * o⁻¹ := by rw [hcu]
  rw [e]
  exact (mem_normalizer_iff.mp (hOW ho) u).1 (hPW.le hu)

theorem le_normalizer_of_forall_sylow {W A L₀ : Subgroup G} (hA2 : IsPGroup 2 A)
    (hAW : A ≤ normalizer (W : Set G)) (hWodd : Odd (Nat.card W))
    (h : ∀ m ∈ L₀, ∀ p : ℕ, p.Prime → ∀ P : Subgroup G, IsSylowOf p P W →
      A ≤ normalizer (P : Set G) → P.map (MulAut.conj m).toMonoidHom ≤ W) :
    L₀ ≤ normalizer (W : Set G) := by
  intro m hm
  apply mem_normalizer_of_forall_conj_mem
  have hle : W ≤ W.comap (MulAut.conj m).toMonoidHom :=
    le_of_forall_isSylowOf_normalized hA2 hAW hWodd fun p hp P hP hAP =>
      map_le_iff_le_comap.mp (h m hm p hp P hP hAP)
  intro w hw
  exact hle hw

theorem exists_isMaxInvIn_ge {p : ℕ} {A P : Subgroup G} (hP : IsPGroup p P)
    (hAP : A ≤ normalizer (P : Set G)) : ∃ R : Subgroup G, IsMaxInvIn p A ⊤ R ∧ P ≤ R := by
  set S : Set (Subgroup G) := {Q | IsPGroup p Q ∧ A ≤ normalizer (Q : Set G) ∧ P ≤ Q} with hS
  obtain ⟨R, hRS, hRmax⟩ := Set.exists_max_image S (fun Q : Subgroup G => Nat.card Q)
    (Set.toFinite S) ⟨P, hP, hAP, le_rfl⟩
  obtain ⟨hRp, hAR, hPR⟩ := hRS
  refine ⟨R, ⟨le_top, hRp, hAR, fun Q _ hQ hAQ hRQ => ?_⟩, hPR⟩
  exact (eq_of_le_of_card_ge hRQ (hRmax Q ⟨hQ, hAQ, hPR.trans hRQ⟩)).symm

omit [Finite G] in
theorem covers_map_conj {H L₀ OL : Subgroup G} {g : G} (hc : Covers H L₀ OL)
    (h₀ : g ∈ normalizer (L₀ : Set G)) (h₁ : g ∈ normalizer (OL : Set G)) :
    Covers (H.map (MulAut.conj g).toMonoidHom) L₀ OL := by
  have hm := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hc
  rwa [Subgroup.map_sup, Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
    map_conj_eq_self_of_mem_normalizer h₀, map_conj_eq_self_of_mem_normalizer h₁] at hm

private theorem odd_card_of_isPGroup' {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Q : Subgroup G}
    (hQ : IsPGroup p Q) : Odd (Nat.card Q) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card.mp hQ)
  rw [hk]
  exact (hp.odd_of_ne_two hp2).pow

omit [Finite G] in
theorem exists_ne_one_of_isKleinFour' {Z : Subgroup G} (hZ : IsKleinFour Z) : ∃ z ∈ Z, z ≠ 1 := by
  by_contra h
  push Not at h
  have hle : Z ≤ ⊥ := fun z hz => (mem_bot).mpr (h z hz)
  have h4 := hZ.card_four
  rw [le_bot_iff.mp hle, card_bot] at h4
  omega

omit [Finite G] in
theorem IsE16.mul_self {A : Subgroup G} (hA : IsE16 A) {a : G} (ha : a ∈ A) : a * a = 1 := by
  rw [← pow_two]
  exact hA.1.2 a ha

omit [Finite G] in
theorem IsE16.orderOf_eq_two {A : Subgroup G} (hA : IsE16 A) {a : G} (ha : a ∈ A)
    (ha1 : a ≠ 1) : orderOf a = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact hA.mul_self ha) ha1

omit [Finite G] in
theorem IsE16.comm {A : Subgroup G} (hA : IsE16 A) {a b : G} (ha : a ∈ A) (hb : b ∈ A) :
    a * b = b * a :=
  CFSG.CGT.Foote81L6.TStruct.comm_of_mul_self (fun _ hx => hA.mul_self hx) ha hb

end Side

namespace Sec4Setting

variable {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) {A : Subgroup G}
  (hAS : A ≤ 𝔖.S) (hA : IsE16 A)
include hAS hA

theorem X_sup_Y : 𝔖.X A ⊔ 𝔖.Y A = A :=
  (dd_e16_split _ _ _ 𝔖.decomp A hAS hA).1

theorem isKleinFour_X : IsKleinFour (𝔖.X A) :=
  (dd_e16_split _ _ _ 𝔖.decomp A hAS hA).2.1

theorem isKleinFour_Y : IsKleinFour (𝔖.Y A) :=
  (dd_e16_split _ _ _ 𝔖.decomp A hAS hA).2.2.1

omit hAS hA in
theorem X_inf_Y : 𝔖.X A ⊓ 𝔖.Y A = ⊥ :=
  le_bot_iff.mp (𝔖.decomp.inf_eq ▸ inf_le_inf inf_le_right inf_le_right)

omit hAS hA in
theorem Y_le_centralizer_X : 𝔖.Y A ≤ centralizer (𝔖.X A : Set G) := fun _ hy =>
  mem_centralizer_iff.mpr fun _ hx => 𝔖.decomp.comm hx.2 hy.2

theorem isXYBalanced_of
    (h410 : (∀ x ∈ 𝔖.X A, x ≠ 1 → ∀ a ∈ A, a ∉ 𝔖.Y A → O (C x) ⊓ C a ≤ O (C a)) ∧
      (∀ y ∈ 𝔖.Y A, y ≠ 1 → ∀ a ∈ A, a ∉ 𝔖.X A → O (C y) ⊓ C a ≤ O (C a)))
    (h411 : (∀ x ∈ 𝔖.X A, x ≠ 1 → ∀ D : Subgroup G, D ≤ C x → Odd (Nat.card D) →
        A ≤ normalizer (D : Set G) → ⁅D, 𝔖.X A⁆ ⊔ ⁅⁅D, 𝔖.Y A⁆, ⁅D, 𝔖.Y A⁆⁆ ≤ O (C x)) ∧
      (∀ y ∈ 𝔖.Y A, y ≠ 1 → ∀ D : Subgroup G, D ≤ C y → Odd (Nat.card D) →
        A ≤ normalizer (D : Set G) → ⁅D, 𝔖.Y A⁆ ⊔ ⁅⁅D, 𝔖.X A⁆, ⁅D, 𝔖.X A⁆⁆ ≤ O (C y)))
    (h520 : ∀ {p : ℕ}, p.Prime → p ≠ 2 → ∀ P : Subgroup G, IsPGroup p P →
      A ≤ normalizer (P : Set G) → XYGenerated (𝔖.X A) (𝔖.Y A) P → ∀ Q : Subgroup G, Q ≤ P →
        A ≤ normalizer (Q : Set G) → XYGenerated (𝔖.X A) (𝔖.Y A) Q) :
    IsXYBalanced (𝔖.X A) (𝔖.Y A) := by
  have hsup := 𝔖.X_sup_Y hAS hA
  exact {
    a₁ := fun x hx hx1 a ha haY => h410.1 x hx hx1 a (hsup ▸ ha) haY
    a₂ := fun y hy hy1 b hb hbX => h410.2 y hy hy1 b (hsup ▸ hb) hbX
    b₁ := fun x hx hx1 D hD hDo hDA => h411.1 x hx hx1 D hD hDo (hsup ▸ hDA)
    b₂ := fun y hy hy1 D hD hDo hDA => h411.2 y hy hy1 D hD hDo (hsup ▸ hDA)
    c := fun _ P hp hp2 hPp hPA hPgen Q hQP hQA =>
      h520 hp hp2 P hPp (hsup ▸ hPA) hPgen Q hQP (hsup ▸ hQA) }

theorem prop_6_1_of
    (h410 : (∀ x ∈ 𝔖.X A, x ≠ 1 → ∀ a ∈ A, a ∉ 𝔖.Y A → O (C x) ⊓ C a ≤ O (C a)) ∧
      (∀ y ∈ 𝔖.Y A, y ≠ 1 → ∀ a ∈ A, a ∉ 𝔖.X A → O (C y) ⊓ C a ≤ O (C a)))
    (h411 : (∀ x ∈ 𝔖.X A, x ≠ 1 → ∀ D : Subgroup G, D ≤ C x → Odd (Nat.card D) →
        A ≤ normalizer (D : Set G) → ⁅D, 𝔖.X A⁆ ⊔ ⁅⁅D, 𝔖.Y A⁆, ⁅D, 𝔖.Y A⁆⁆ ≤ O (C x)) ∧
      (∀ y ∈ 𝔖.Y A, y ≠ 1 → ∀ D : Subgroup G, D ≤ C y → Odd (Nat.card D) →
        A ≤ normalizer (D : Set G) → ⁅D, 𝔖.Y A⁆ ⊔ ⁅⁅D, 𝔖.X A⁆, ⁅D, 𝔖.X A⁆⁆ ≤ O (C y)))
    (h520 : ∀ {p : ℕ}, p.Prime → p ≠ 2 → ∀ P : Subgroup G, IsPGroup p P →
      A ≤ normalizer (P : Set G) → XYGenerated (𝔖.X A) (𝔖.Y A) P → ∀ Q : Subgroup G, Q ≤ P →
        A ≤ normalizer (Q : Set G) → XYGenerated (𝔖.X A) (𝔖.Y A) Q) :
    (∀ a ∈ A, a ≠ 1 → theta (𝔖.X A) (𝔖.Y A) a ≤ centralizer {a}) ∧
    (∀ a ∈ A, a ≠ 1 → Odd (Nat.card (theta (𝔖.X A) (𝔖.Y A) a))) ∧
    (∀ a ∈ A, a ≠ 1 → A ≤ normalizer (theta (𝔖.X A) (𝔖.Y A) a : Set G)) ∧
    (∀ a ∈ A, a ≠ 1 → ∀ b ∈ A, b ≠ 1 →
      theta (𝔖.X A) (𝔖.Y A) a ⊓ centralizer {b} ≤ theta (𝔖.X A) (𝔖.Y A) b) := by
  have h23 := prop_2_3 (𝔖.isKleinFour_X hAS hA) (𝔖.isKleinFour_Y hAS hA) 𝔖.X_inf_Y
    𝔖.Y_le_centralizer_X (𝔖.isXYBalanced_of hAS hA h410 h411 h520)
  rwa [𝔖.X_sup_Y hAS hA] at h23

theorem prop_6_2_of
    (h410 : (∀ x ∈ 𝔖.X A, x ≠ 1 → ∀ a ∈ A, a ∉ 𝔖.Y A → O (C x) ⊓ C a ≤ O (C a)) ∧
      (∀ y ∈ 𝔖.Y A, y ≠ 1 → ∀ a ∈ A, a ∉ 𝔖.X A → O (C y) ⊓ C a ≤ O (C a)))
    (h411 : (∀ x ∈ 𝔖.X A, x ≠ 1 → ∀ D : Subgroup G, D ≤ C x → Odd (Nat.card D) →
        A ≤ normalizer (D : Set G) → ⁅D, 𝔖.X A⁆ ⊔ ⁅⁅D, 𝔖.Y A⁆, ⁅D, 𝔖.Y A⁆⁆ ≤ O (C x)) ∧
      (∀ y ∈ 𝔖.Y A, y ≠ 1 → ∀ D : Subgroup G, D ≤ C y → Odd (Nat.card D) →
        A ≤ normalizer (D : Set G) → ⁅D, 𝔖.Y A⁆ ⊔ ⁅⁅D, 𝔖.X A⁆, ⁅D, 𝔖.X A⁆⁆ ≤ O (C y)))
    (h520 : ∀ {p : ℕ}, p.Prime → p ≠ 2 → ∀ P : Subgroup G, IsPGroup p P →
      A ≤ normalizer (P : Set G) → XYGenerated (𝔖.X A) (𝔖.Y A) P → ∀ Q : Subgroup G, Q ≤ P →
        A ≤ normalizer (Q : Set G) → XYGenerated (𝔖.X A) (𝔖.Y A) Q) :
    Odd (Nat.card (𝔖.WA A)) := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := 𝔖.prop_6_1_of hAS hA h410 h411 h520
  exact theorem_2_1 A hA.1 hA.2.ge _ h₁ h₂ h₃ h₄

omit hAS hA in
theorem prop_6_5_of_prop_6_4
    (h64 : 𝔖.WA A ≠ ⊥ → CFSG.IsStronglyEmbedded (normalizer (𝔖.WA A : Set G))) :
    ∀ a ∈ A, a ≠ 1 → theta (𝔖.X A) (𝔖.Y A) a = ⊥ := by
  intro a ha ha1
  by_contra hne
  have hW : 𝔖.WA A ≠ ⊥ := by
    intro hW
    apply hne
    rw [eq_bot_iff, ← hW]
    exact le_iSup_of_le a (le_iSup_of_le ha (le_iSup_of_le ha1 le_rfl))
  exact not_stronglyEmbedded_of_productFusion 𝔖.decomp 𝔖.fusion _ (h64 hW)

omit hAS hA in
theorem prop_6_6_of
    (h65 : ∀ A : Subgroup G, A ≤ 𝔖.S → IsE16 A → ∀ a ∈ A, a ≠ 1 →
      theta (𝔖.X A) (𝔖.Y A) a = ⊥)
    (s₁ s₂ : G) (hs₁ : s₁ ∈ 𝔖.S₁) (hs₂ : s₂ ∈ 𝔖.S₂) (h₁ : orderOf s₁ = 2)
    (h₂ : orderOf s₂ = 2) : O (C s₁) ⊓ O (C s₂) = ⊥ := by
  have hd := 𝔖.decomp
  have hsq : ∀ s : G, orderOf s = 2 → s * s = 1 := fun s hs => by
    rw [← pow_two, ← hs, pow_orderOf_eq_one]
  have hne : ∀ s : G, orderOf s = 2 → s ≠ 1 := fun s hs h => by
    rw [h, orderOf_one] at hs
    omega
  obtain ⟨V₁, hV₁, hs₁V⟩ := hd.dih₁.exists_four_mem hs₁ (hsq s₁ h₁)
  obtain ⟨V₂, hV₂, hs₂V⟩ := hd.isDih₂.exists_four_mem hs₂ (hsq s₂ h₂)
  have hAS : V₁ ⊔ V₂ ≤ 𝔖.S := sup_le (hV₁.1.trans hd.le_left) (hV₂.1.trans hd.le_right)
  have hA := hd.isE16_sup hV₁ hV₂
  have hX : 𝔖.X (V₁ ⊔ V₂) = V₁ := hd.sup_inf_left hV₁.1 hV₂.1
  have hY : 𝔖.Y (V₁ ⊔ V₂) = V₂ := hd.sup_inf_right hV₁.1 hV₂.1
  have h := h65 (V₁ ⊔ V₂) hAS hA s₁ (mem_sup_left hs₁V) (hne s₁ h₁)
  rw [eq_bot_iff, ← h]
  have hle : C s₁ ⊓ O (C s₁) ⊓ O (C s₂) ≤ theta (𝔖.X (V₁ ⊔ V₂)) (𝔖.Y (V₁ ⊔ V₂)) s₁ :=
    le_xySupOf (X₀ := 𝔖.X (V₁ ⊔ V₂)) (Y₀ := 𝔖.Y (V₁ ⊔ V₂))
      (f := fun x y => C s₁ ⊓ O (C x) ⊓ O (C y)) (by rw [hX]; exact hs₁V) (hne s₁ h₁)
      (by rw [hY]; exact hs₂V) (hne s₂ h₂)
  refine le_trans ?_ hle
  exact le_inf (le_inf (inf_le_left.trans (map_subtype_le _)) inf_le_left) inf_le_right

omit hAS hA in
theorem gen_le_WA {a x y : G} (ha : a ∈ A) (ha1 : a ≠ 1) (hx : x ∈ 𝔖.X A) (hx1 : x ≠ 1)
    (hy : y ∈ 𝔖.Y A) (hy1 : y ≠ 1) : C a ⊓ O (C x) ⊓ O (C y) ≤ 𝔖.WA A :=
  (le_xySupOf (X₀ := 𝔖.X A) (Y₀ := 𝔖.Y A) (f := fun x y => C a ⊓ O (C x) ⊓ O (C y)) hx hx1 hy
    hy1).trans (le_iSup_of_le a (le_iSup_of_le ha (le_iSup_of_le ha1 le_rfl)))

omit hAS hA in
theorem xyGenerated_WA : XYGenerated (𝔖.X A) (𝔖.Y A) (𝔖.WA A) := by
  refine le_antisymm ?_ (xySupOf_le (X₀ := 𝔖.X A) (Y₀ := 𝔖.Y A)
    fun _ _ _ _ _ _ => inf_le_left.trans inf_le_left)
  refine iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => ?_
  exact xySupOf_mono (X₀ := 𝔖.X A) (Y₀ := 𝔖.Y A) fun x hx hx1 y hy hy1 =>
    le_inf (le_inf (𝔖.gen_le_WA ha ha1 hx hx1 hy hy1) (inf_le_left.trans inf_le_right))
      inf_le_right

omit hAS hA in
theorem le_normalizer_WA
    (h : ∀ a ∈ A, a ≠ 1 → A ≤ normalizer (theta (𝔖.X A) (𝔖.Y A) a : Set G)) :
    A ≤ normalizer (𝔖.WA A : Set G) := fun _ hg =>
  mem_normalizer_iSup_of_forall fun a => mem_normalizer_iSup_of_forall fun ha =>
    mem_normalizer_iSup_of_forall fun ha1 => h a ha ha1 hg

theorem normalizer_le_normalizer_X : normalizer (A : Set G) ≤ normalizer (𝔖.X A : Set G) := by
  intro g hg
  apply mem_normalizer_of_forall_conj_mem
  intro x hx
  have hgx : g * x * g⁻¹ ∈ A := (mem_normalizer_iff.mp hg x).1 hx.1
  refine ⟨hgx, ?_⟩
  by_cases hx1 : x = 1
  · rw [hx1, mul_one, mul_inv_cancel]
    exact one_mem _
  have hS : ∀ {b : G}, b ∈ A → b ∈ 𝔖.S₁ ⊔ 𝔖.S₂ := fun hb => 𝔖.decomp.sup_eq ▸ hAS hb
  exact ((𝔖.fusion.separate x (hS hx.1) _ (hS hgx) (hA.orderOf_eq_two hx.1 hx1)
    (isConj_iff.mpr ⟨g, rfl⟩)).1).mp hx.2

theorem normalizer_le_normalizer_Y : normalizer (A : Set G) ≤ normalizer (𝔖.Y A : Set G) := by
  intro g hg
  apply mem_normalizer_of_forall_conj_mem
  intro y hy
  have hgy : g * y * g⁻¹ ∈ A := (mem_normalizer_iff.mp hg y).1 hy.1
  refine ⟨hgy, ?_⟩
  by_cases hy1 : y = 1
  · rw [hy1, mul_one, mul_inv_cancel]
    exact one_mem _
  have hS : ∀ {b : G}, b ∈ A → b ∈ 𝔖.S₁ ⊔ 𝔖.S₂ := fun hb => 𝔖.decomp.sup_eq ▸ hAS hb
  exact ((𝔖.fusion.separate y (hS hy.1) _ (hS hgy) (hA.orderOf_eq_two hy.1 hy1)
    (isConj_iff.mpr ⟨g, rfl⟩)).2).mp hy.2

theorem normalizer_le_normalizer_WA : normalizer (A : Set G) ≤ normalizer (𝔖.WA A : Set G) := by
  intro g hg
  have hgX := 𝔖.normalizer_le_normalizer_X hAS hA hg
  have hgY := 𝔖.normalizer_le_normalizer_Y hAS hA hg
  apply mem_normalizer_of_forall_conj_mem
  suffices h : (𝔖.WA A).map (MulAut.conj g).toMonoidHom ≤ 𝔖.WA A from fun w hw => h ⟨w, hw, rfl⟩
  change (⨆ (a : G) (_ : a ∈ A) (_ : a ≠ 1), theta (𝔖.X A) (𝔖.Y A) a).map _ ≤ _
  simp only [Subgroup.map_iSup]
  refine iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => ?_
  change (xySupOf (𝔖.X A) (𝔖.Y A) fun x y => C a ⊓ O (C x) ⊓ O (C y)).map _ ≤ _
  rw [map_xySupOf]
  refine xySupOf_le fun x hx hx1 y hy hy1 => ?_
  rintro _ ⟨u, hu, rfl⟩
  rw [SetLike.mem_coe, mem_inf, mem_inf] at hu
  obtain ⟨⟨hua, hux⟩, huy⟩ := hu
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hne : ∀ {b : G}, b ≠ 1 → g * b * g⁻¹ ≠ 1 := fun {b} hb h => hb (by
    have e : g⁻¹ * (g * b * g⁻¹) * g = b := by group
    rw [← e, h, mul_one, inv_mul_cancel])
  have hC : g * u * g⁻¹ ∈ C (g * a * g⁻¹) := by
    rw [mem_centralizer_singleton_iff] at hua ⊢
    calc g * u * g⁻¹ * (g * a * g⁻¹) = g * (u * a) * g⁻¹ := by group
      _ = g * (a * u) * g⁻¹ := by rw [hua]
      _ = g * a * g⁻¹ * (g * u * g⁻¹) := by group
  exact 𝔖.gen_le_WA ((mem_normalizer_iff.mp hg a).1 ha) (hne ha1)
    ((mem_normalizer_iff.mp hgX x).1 hx) (hne hx1) ((mem_normalizer_iff.mp hgY y).1 hy) (hne hy1)
    (mem_inf.mpr ⟨mem_inf.mpr ⟨hC, conj_mem_O_C hux⟩, conj_mem_O_C huy⟩)

theorem normalizer_le_normalizer_M₀ {g : G} (hg : g ∈ normalizer (A : Set G)) :
    g ∈ normalizer (𝔖.M A : Set G) ∧ g ∈ normalizer (O (𝔖.M A) : Set G) ∧
      g ∈ normalizer (𝔖.M₀ A : Set G) := by
  have hM : g ∈ normalizer (𝔖.M A : Set G) :=
    mem_normalizer_centralizer_of (𝔖.normalizer_le_normalizer_X hAS hA hg)
  have hO := normalizer_le_normalizer_O _ hM
  have hO2 := normalizer_le_normalizer_O2 _ hM
  exact ⟨hM, hO, mem_normalizer_sup_of (mem_normalizer_commutator' hO2 hO2) hO⟩

theorem normalizer_le_normalizer_N₀ {g : G} (hg : g ∈ normalizer (A : Set G)) :
    g ∈ normalizer (𝔖.N A : Set G) ∧ g ∈ normalizer (O (𝔖.N A) : Set G) ∧
      g ∈ normalizer (𝔖.N₀ A : Set G) := by
  have hN : g ∈ normalizer (𝔖.N A : Set G) :=
    mem_normalizer_centralizer_of (𝔖.normalizer_le_normalizer_Y hAS hA hg)
  have hO := normalizer_le_normalizer_O _ hN
  have hO2 := normalizer_le_normalizer_O2 _ hN
  exact ⟨hN, hO, mem_normalizer_sup_of (mem_normalizer_commutator' hO2 hO2) hO⟩

omit hAS hA in
include 𝔖 in
theorem oddCore_eq_bot : CFSG.oddCore G = ⊥ := 𝔖.mc.hyp.1

omit hAS hA in
include 𝔖 in
theorem ne_top_of_isPLocal {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {H : Subgroup G}
    (hH : CFSG.IsPLocal p H) : H ≠ ⊤ := by
  obtain ⟨Q, hQ1, hQp, rfl⟩ := hH
  intro htop
  have hQn : Q.Normal := normalizer_eq_top_iff.mp htop
  have hle : Q ≤ CFSG.oddCore G := le_sSup ⟨hQn, odd_card_of_isPGroup' hp hp2 hQp⟩
  rw [𝔖.oddCore_eq_bot] at hle
  exact hQ1 (le_bot_iff.mp hle)

theorem map_le_WA_of_not_le_centralizer
    (h46 : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ P₁ P₂ : Subgroup G, IsMaxInvIn p A ⊤ P₁ →
      IsMaxInvIn p A ⊤ P₂ → ∃ g ∈ normalizer (A : Set G), P₁.map (MulAut.conj g).toMonoidHom = P₂)
    (h54 : ∀ {p : ℕ}, p.Prime → p ≠ 2 → (∃ D : Subgroup G, IsPGroup p D ∧
      A ≤ normalizer (D : Set G) ∧ ¬ A ≤ centralizer (D : Set G) ∧
      XYGenerated (𝔖.X A) (𝔖.Y A) D) → ∃ H, 𝔖.IsCovering p A H)
    (h414 : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H → Covers H (𝔖.M₀ A) (O (𝔖.M A)) →
      Covers H (𝔖.N₀ A) (O (𝔖.N A)) → ∀ D : Subgroup G, D ≤ H → Odd (Nat.card D) →
        A ≤ normalizer (D : Set G) → (XYGenerated (𝔖.X A) (𝔖.Y A) D ↔ D ≤ O H))
    (hOM : O (𝔖.M A) ≤ normalizer (𝔖.WA A : Set G))
    (hON : O (𝔖.N A) ≤ normalizer (𝔖.WA A : Set G))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup G} (hPp : IsPGroup p P)
    (hAP : A ≤ normalizer (P : Set G)) (hnc : ¬ A ≤ centralizer (P : Set G))
    (hPgen : XYGenerated (𝔖.X A) (𝔖.Y A) P) :
    (∀ m ∈ 𝔖.M₀ A, P.map (MulAut.conj m).toMonoidHom ≤ 𝔖.WA A) ∧
      ∀ m ∈ 𝔖.N₀ A, P.map (MulAut.conj m).toMonoidHom ≤ 𝔖.WA A := by
  obtain ⟨H, ⟨hHloc, hAH, R, hR, hRH⟩, hHM, hHN⟩ := h54 hp hp2 ⟨P, hPp, hAP, hnc, hPgen⟩
  obtain ⟨R', hR', hPR'⟩ := exists_isMaxInvIn_ge hPp hAP
  obtain ⟨g, hg, hgR⟩ := h46 p hp hp2 R R' hR hR'
  set H' := H.map (MulAut.conj g).toMonoidHom with hH'def
  have hPH' : P ≤ H' := hPR'.trans (hgR ▸ map_mono hRH)
  have hAH' : A ≤ H' := by
    rw [← map_conj_eq_self_of_mem_normalizer hg]
    exact map_mono hAH
  have hH'ne : H' ≠ ⊤ := by
    intro htop
    apply 𝔖.ne_top_of_isPLocal hp hp2 hHloc
    rw [eq_top_iff]
    intro x _
    have hx : g * x * g⁻¹ ∈ H' := htop ▸ mem_top _
    rw [hH'def, mem_map_conj] at hx
    have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rwa [e] at hx
  obtain ⟨-, hgOM, hgM₀⟩ := 𝔖.normalizer_le_normalizer_M₀ hAS hA hg
  obtain ⟨-, hgON, hgN₀⟩ := 𝔖.normalizer_le_normalizer_N₀ hAS hA hg
  have hH'M := covers_map_conj hHM hgM₀ hgOM
  have hH'N := covers_map_conj hHN hgN₀ hgON
  have hPO : P ≤ O H' :=
    (h414 H' hH'ne hAH' hH'M hH'N P hPH' (odd_card_of_isPGroup' hp hp2 hPp) hAP).mp hPgen
  have hOH'W : O H' ≤ 𝔖.WA A := by
    have hgen := (h414 H' hH'ne hAH' hH'M hH'N (O H') (map_subtype_le _) (card_O_odd H')
      (hAH'.trans (le_normalizer_O H'))).mpr le_rfl
    refine hgen.le.trans (xySupOf_le (X₀ := 𝔖.X A) (Y₀ := 𝔖.Y A)
      fun x hx hx1 y hy hy1 => ?_)
    exact (le_inf (le_inf ((inf_le_left.trans inf_le_right).trans (map_subtype_le _))
      (inf_le_left.trans inf_le_right)) inf_le_right).trans
      (𝔖.gen_le_WA hx.1 hx1 hx hx1 hy hy1)
  have key : ∀ {L L₀ : Subgroup G}, L₀ ≤ L → Covers H' L₀ (O L) →
      O L ≤ normalizer (𝔖.WA A : Set G) →
      ∀ m ∈ L₀, P.map (MulAut.conj m).toMonoidHom ≤ 𝔖.WA A := by
    intro L L₀ hL₀L hcov hOW m hm
    have hm' : m ∈ O L ⊔ (H' ⊓ L₀) := by
      rw [sup_comm]
      exact hcov hm
    obtain ⟨o, ho, h, hh, rfl⟩ := (mem_sup_iff_of_le_normalizer
      (inf_le_right.trans (hL₀L.trans (le_normalizer_O L)))).1 hm'
    rintro _ ⟨u, hu, rfl⟩
    have hhu : h * u * h⁻¹ ∈ 𝔖.WA A :=
      hOH'W ((mem_normalizer_iff.mp (le_normalizer_O H' (mem_inf.mp hh).1) u).1 (hPO hu))
    have e : (MulAut.conj (o * h)).toMonoidHom u = o * (h * u * h⁻¹) * o⁻¹ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e]
    exact (mem_normalizer_iff.mp (hOW ho) _).1 hhu
  have hM₀M : 𝔖.M₀ A ≤ 𝔖.M A :=
    sup_le (commutator_self_le' _ |>.trans (map_subtype_le _)) (map_subtype_le _)
  have hN₀N : 𝔖.N₀ A ≤ 𝔖.N A :=
    sup_le (commutator_self_le' _ |>.trans (map_subtype_le _)) (map_subtype_le _)
  exact ⟨key hM₀M hH'M hOM, key hN₀N hH'N hON⟩

theorem M_ne_top : 𝔖.M A ≠ ⊤ := by
  intro htop
  obtain ⟨x, hx, hx1⟩ := exists_ne_one_of_isKleinFour' (𝔖.isKleinFour_X hAS hA)
  obtain ⟨u, hu, hu2, hu1, hux⟩ := 𝔖.decomp.dih₁.exists_involution_ne x
  obtain ⟨g, hg⟩ := isConj_iff.mp (𝔖.fusion.conj₁ x hx.2 u hu (hA.orderOf_eq_two hx.1 hx1)
    (orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1))
  have hgx : g ∈ 𝔖.M A := htop ▸ mem_top g
  have hfix : g * x * g⁻¹ = x := by
    rw [← mem_centralizer_iff.mp hgx x hx, mul_inv_cancel_right]
  exact hux (hg.symm.trans hfix)

theorem N_ne_top : 𝔖.N A ≠ ⊤ := by
  intro htop
  obtain ⟨y, hy, hy1⟩ := exists_ne_one_of_isKleinFour' (𝔖.isKleinFour_Y hAS hA)
  obtain ⟨u, hu, hu2, hu1, huy⟩ := 𝔖.decomp.isDih₂.exists_involution_ne y
  obtain ⟨g, hg⟩ := isConj_iff.mp (𝔖.fusion.conj₂ y hy.2 u hu (hA.orderOf_eq_two hy.1 hy1)
    (orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1))
  have hgy : g ∈ 𝔖.N A := htop ▸ mem_top g
  have hfix : g * y * g⁻¹ = y := by
    rw [← mem_centralizer_iff.mp hgy y hy, mul_inv_cancel_right]
  exact huy (hg.symm.trans hfix)

theorem prop_6_3_of
    (h47 : QuotIs (𝔖.M₀ A) (O (𝔖.M A)) (fun L _ => IsL2OrA7 L 7) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₂ (𝔖.M₀ A) ∧
      𝔖.M A = 𝔖.M₀ A ⊔ (𝔖.M A ⊓ normalizer (A : Set G)) ∧
      𝔖.M A = 𝔖.M₀ A ⊔ (𝔖.M A ⊓ normalizer (𝔖.S₂ : Set G)) ∧
      (∀ x ∈ 𝔖.X A, x ≠ 1 → O2 (C x) = (O2 (𝔖.M A) ⊓ O2 (C x)) ⊔ O (C x)) ∧
      (∀ x ∈ 𝔖.X A, x ≠ 1 → ⁅O2 (C x), O2 (C x)⁆ ⊔ O (C x) =
        (𝔖.M₀ A ⊓ ⁅O2 (C x), O2 (C x)⁆) ⊔ O (C x)))
    (h48 : QuotIs (𝔖.N₀ A) (O (𝔖.N A)) (fun L _ => IsL2OrA7 L 5 ∨ IsKleinFour L) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₁ (𝔖.N₀ A) ∧
      𝔖.N A = 𝔖.N₀ A ⊔ (𝔖.N A ⊓ normalizer (A : Set G)) ∧
      𝔖.N A = 𝔖.N₀ A ⊔ (𝔖.N A ⊓ normalizer (𝔖.S₁ : Set G)) ∧
      (∀ y ∈ 𝔖.Y A, y ≠ 1 → O2 (C y) = (O2 (𝔖.N A) ⊓ O2 (C y)) ⊔ O (C y)) ∧
      (∀ y ∈ 𝔖.Y A, y ≠ 1 → ⁅O2 (C y), O2 (C y)⁆ ⊔ O (C y) =
        (𝔖.N₀ A ⊓ ⁅O2 (C y), O2 (C y)⁆) ⊔ O (C y)))
    (h410 : (∀ x ∈ 𝔖.X A, x ≠ 1 → ∀ a ∈ A, a ∉ 𝔖.Y A → O (C x) ⊓ C a ≤ O (C a)) ∧
      (∀ y ∈ 𝔖.Y A, y ≠ 1 → ∀ a ∈ A, a ∉ 𝔖.X A → O (C y) ⊓ C a ≤ O (C a)))
    (h411 : (∀ x ∈ 𝔖.X A, x ≠ 1 → ∀ D : Subgroup G, D ≤ C x → Odd (Nat.card D) →
        A ≤ normalizer (D : Set G) → ⁅D, 𝔖.X A⁆ ⊔ ⁅⁅D, 𝔖.Y A⁆, ⁅D, 𝔖.Y A⁆⁆ ≤ O (C x)) ∧
      (∀ y ∈ 𝔖.Y A, y ≠ 1 → ∀ D : Subgroup G, D ≤ C y → Odd (Nat.card D) →
        A ≤ normalizer (D : Set G) → ⁅D, 𝔖.Y A⁆ ⊔ ⁅⁅D, 𝔖.X A⁆, ⁅D, 𝔖.X A⁆⁆ ≤ O (C y)))
    (h413 : ∀ H : Subgroup G, H ≠ ⊤ →
      (Covers H (𝔖.M₀ A) (O (𝔖.M A)) → ∀ x ∈ 𝔖.X A, x ≠ 1 → x ∈ H → O H ⊓ C x ≤ O (C x)) ∧
      (Covers H (𝔖.N₀ A) (O (𝔖.N A)) → ∀ y ∈ 𝔖.Y A, y ≠ 1 → y ∈ H → O H ⊓ C y ≤ O (C y)))
    (h414 : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H → Covers H (𝔖.M₀ A) (O (𝔖.M A)) →
      Covers H (𝔖.N₀ A) (O (𝔖.N A)) → ∀ D : Subgroup G, D ≤ H → Odd (Nat.card D) →
        A ≤ normalizer (D : Set G) → (XYGenerated (𝔖.X A) (𝔖.Y A) D ↔ D ≤ O H))
    (h46 : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ P₁ P₂ : Subgroup G, IsMaxInvIn p A ⊤ P₁ →
      IsMaxInvIn p A ⊤ P₂ → ∃ g ∈ normalizer (A : Set G), P₁.map (MulAut.conj g).toMonoidHom = P₂)
    (h54 : ∀ {p : ℕ}, p.Prime → p ≠ 2 → (∃ D : Subgroup G, IsPGroup p D ∧
      A ≤ normalizer (D : Set G) ∧ ¬ A ≤ centralizer (D : Set G) ∧
      XYGenerated (𝔖.X A) (𝔖.Y A) D) → ∃ H, 𝔖.IsCovering p A H)
    (h520 : ∀ {p : ℕ}, p.Prime → p ≠ 2 → ∀ P : Subgroup G, IsPGroup p P →
      A ≤ normalizer (P : Set G) → XYGenerated (𝔖.X A) (𝔖.Y A) P → ∀ Q : Subgroup G, Q ≤ P →
        A ≤ normalizer (Q : Set G) → XYGenerated (𝔖.X A) (𝔖.Y A) Q)
    (hW : 𝔖.WA A ≠ ⊥) :
    𝔖.M A ≤ normalizer (𝔖.WA A : Set G) ∧ 𝔖.N A ≤ normalizer (𝔖.WA A : Set G) ∧
      normalizer (A : Set G) ≤ normalizer (𝔖.WA A : Set G) := by
  have _ := hW
  have hsup := 𝔖.X_sup_Y hAS hA
  have hX := 𝔖.isKleinFour_X hAS hA
  have hY := 𝔖.isKleinFour_Y hAS hA
  have hbal := 𝔖.isXYBalanced_of hAS hA h410 h411 h520
  obtain ⟨-, -, h61₃, -⟩ := 𝔖.prop_6_1_of hAS hA h410 h411 h520
  have hWodd := 𝔖.prop_6_2_of hAS hA h410 h411 h520
  have hAW := 𝔖.le_normalizer_WA h61₃
  have hNA := 𝔖.normalizer_le_normalizer_WA hAS hA
  have hCA : centralizer (A : Set G) ≤ normalizer (𝔖.WA A : Set G) :=
    (centralizer_le_normalizer _).trans hNA
  have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => hA.comm ha hb
  have hA2 : IsPGroup 2 A := IsPGroup.of_card (n := 4) (by rw [hA.2]; norm_num)
  have hWgen : ∀ F : Subgroup G, F ≤ 𝔖.WA A → A ≤ normalizer (F : Set G) →
      XYGenerated (𝔖.X A) (𝔖.Y A) F := fun F hFW hFA =>
    xyGenerated_of_le_of_isXYBalanced hX hY 𝔖.X_inf_Y 𝔖.Y_le_centralizer_X hbal hWodd
      (hsup.symm ▸ hAW) 𝔖.xyGenerated_WA hFW (hsup.symm ▸ hFA)
  have hXA : 𝔖.X A ≤ A := inf_le_left
  have hYA : 𝔖.Y A ≤ A := inf_le_left
  have hAM : A ≤ 𝔖.M A := fun g hg => mem_centralizer_iff.mpr fun h hh => hAab h (hXA hh) g hg
  have hAN : A ≤ 𝔖.N A := fun g hg => mem_centralizer_iff.mpr fun h hh => hAab h (hYA hh) g hg
  have hM₀M : 𝔖.M₀ A ≤ 𝔖.M A :=
    sup_le (commutator_self_le' _ |>.trans (map_subtype_le _)) (map_subtype_le _)
  have hN₀N : 𝔖.N₀ A ≤ 𝔖.N A :=
    sup_le (commutator_self_le' _ |>.trans (map_subtype_le _)) (map_subtype_le _)
  have hOM₀ : O (𝔖.M A) ≤ 𝔖.M₀ A := le_sup_right
  have hON₀ : O (𝔖.N A) ≤ 𝔖.N₀ A := le_sup_right
  have hcovM : Covers (𝔖.M A) (𝔖.M₀ A) (O (𝔖.M A)) := fun m hm =>
    mem_sup_left (mem_inf.mpr ⟨hM₀M hm, hm⟩)
  have hcovN : Covers (𝔖.N A) (𝔖.N₀ A) (O (𝔖.N A)) := fun m hm =>
    mem_sup_left (mem_inf.mpr ⟨hN₀N hm, hm⟩)
  have h413M : ∀ x ∈ 𝔖.X A, x ≠ 1 → O (𝔖.M A) ⊓ C x ≤ O (C x) := fun x hx hx1 =>
    (h413 _ (𝔖.M_ne_top hAS hA)).1 hcovM x hx hx1 (hAM (hXA hx))
  have h413N : ∀ y ∈ 𝔖.Y A, y ≠ 1 → O (𝔖.N A) ⊓ C y ≤ O (C y) := fun y hy hy1 =>
    (h413 _ (𝔖.N_ne_top hAS hA)).2 hcovN y hy hy1 (hAN (hYA hy))
  obtain ⟨x₀, hx₀, hx₀1⟩ := exists_ne_one_of_isKleinFour' hX
  obtain ⟨y₀, hy₀, hy₀1⟩ := exists_ne_one_of_isKleinFour' hY
  have hbY : ∀ y ∈ 𝔖.Y A, y ≠ 1 → ∀ D : Subgroup G, D ≤ C y → Odd (Nat.card D) →
      A ≤ normalizer (D : Set G) → ⁅D, 𝔖.Y A⁆ ≤ O (C y) := fun y hy hy1 D hD hDo hDA =>
    le_sup_left.trans (h411.2 y hy hy1 D hD hDo hDA)
  have hbX : ∀ x ∈ 𝔖.X A, x ≠ 1 → ∀ D : Subgroup G, D ≤ C x → Odd (Nat.card D) →
      A ≤ normalizer (D : Set G) → ⁅D, 𝔖.X A⁆ ≤ O (C x) := fun x hx hx1 D hD hDo hDA =>
    le_sup_left.trans (h411.1 x hx hx1 D hD hDo hDA)
  have hgenY : ∀ y ∈ 𝔖.Y A, y ≠ 1 → C y ⊓ O (C x₀) ⊓ O (C y) ≤ 𝔖.WA A := fun y hy hy1 =>
    𝔖.gen_le_WA (hYA hy) hy1 hx₀ hx₀1 hy hy1
  have hgenX : ∀ x ∈ 𝔖.X A, x ≠ 1 → C x ⊓ O (C y₀) ⊓ O (C x) ≤ 𝔖.WA A := fun x hx hx1 =>
    (le_inf (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
      (inf_le_left.trans inf_le_right)).trans (𝔖.gen_le_WA (hXA hx) hx1 hx hx1 hy₀ hy₀1)
  have hsup' : 𝔖.Y A ⊔ 𝔖.X A = A := by rw [sup_comm]; exact hsup
  have hOM : O (𝔖.M A) ≤ normalizer (𝔖.WA A : Set G) :=
    O_centralizer_le_normalizer_of hY hAab hsup hbY hx₀ (h413M x₀ hx₀ hx₀1) hgenY hCA
  have hON : O (𝔖.N A) ≤ normalizer (𝔖.WA A : Set G) :=
    O_centralizer_le_normalizer_of hX hAab hsup' hbX hy₀ (h413N y₀ hy₀ hy₀1) hgenX hCA
  have hsyl : ∀ {Z Z' L₀ : Subgroup G}, (Z = 𝔖.X A ∧ Z' = 𝔖.Y A) ∨ (Z = 𝔖.Y A ∧ Z' = 𝔖.X A) →
      L₀ ≤ centralizer (Z : Set G) → Z' ≤ L₀ →
      QuotIs L₀ (O (centralizer (Z : Set G))) (fun L _ => IsSimpleGroup L) →
      (∀ m ∈ L₀, ∀ {p : ℕ}, p.Prime → p ≠ 2 → ∀ {P : Subgroup G}, IsPGroup p P →
        A ≤ normalizer (P : Set G) → ¬ A ≤ centralizer (P : Set G) →
        XYGenerated (𝔖.X A) (𝔖.Y A) P → P.map (MulAut.conj m).toMonoidHom ≤ 𝔖.WA A) →
      L₀ ≤ normalizer (𝔖.WA A : Set G) := by
    intro Z Z' L₀ hZZ hL₀ hZ'L₀ hsimple hD2
    refine le_normalizer_of_forall_sylow hA2 hAW hWodd fun m hm p hp P hP hAP => ?_
    by_cases hp2 : p = 2
    · subst hp2
      have hPbot : P = ⊥ := by
        rcases hP.isPGroup.card_eq_or_dvd with h1 | h2
        · exact card_eq_one.mp h1
        · exact absurd (h2.trans (card_dvd_of_le hP.le)) (Nat.two_dvd_ne_zero.mpr
            (Nat.odd_iff.mp hWodd))
      rw [hPbot, Subgroup.map_bot]
      exact bot_le
    have hPgen := hWgen P hP.le hAP
    by_cases hc : A ≤ centralizer (P : Set G)
    · have hPC : P ≤ centralizer (A : Set G) := le_centralizer_iff.mp hc
      rcases hZZ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have hPO : P ≤ O (𝔖.M A) := by
          rw [hPgen]
          refine xySupOf_le (X₀ := 𝔖.X A) (Y₀ := 𝔖.Y A) fun x hx hx1 y hy hy1 => ?_
          refine le_trans ?_ (O_inf_le_O_of_le (K := C x) (L := 𝔖.M A)
            (centralizer_le (Set.singleton_subset_iff.mpr hx)))
          exact le_inf (inf_le_left.trans inf_le_right)
            ((inf_le_left.trans inf_le_left).trans (hPC.trans (centralizer_le hXA)))
        exact map_le_of_le_centralizer_of hp hY hAab hsup hA2 hbY hx₀ (h413M x₀ hx₀ hx₀1)
          hgenY hOM hL₀ hZ'L₀ hsimple hP hc hPO m hm
      · have hPO : P ≤ O (𝔖.N A) := by
          rw [hPgen]
          refine xySupOf_le (X₀ := 𝔖.X A) (Y₀ := 𝔖.Y A) fun x hx hx1 y hy hy1 => ?_
          refine le_trans ?_ (O_inf_le_O_of_le (K := C y) (L := 𝔖.N A)
            (centralizer_le (Set.singleton_subset_iff.mpr hy)))
          exact le_inf inf_le_right
            ((inf_le_left.trans inf_le_left).trans (hPC.trans (centralizer_le hYA)))
        exact map_le_of_le_centralizer_of hp hX hAab hsup' hA2 hbX hy₀ (h413N y₀ hy₀ hy₀1)
          hgenX hON hL₀ hZ'L₀ hsimple hP hc hPO m hm
    · exact hD2 m hm hp hp2 hP.isPGroup hAP hc hPgen
  have hD2 := fun {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup G} (hPp : IsPGroup p P)
      (hAP : A ≤ normalizer (P : Set G)) (hc : ¬ A ≤ centralizer (P : Set G))
      (hPgen : XYGenerated (𝔖.X A) (𝔖.Y A) P) =>
    𝔖.map_le_WA_of_not_le_centralizer hAS hA h46 h54 h414 hOM hON hp hp2 hPp hAP hc hPgen
  have hM₀ : 𝔖.M₀ A ≤ normalizer (𝔖.WA A : Set G) := by
    obtain ⟨L, _, f, hf, hker, h7⟩ := h47.1
    exact hsyl (Or.inl ⟨rfl, rfl⟩) hM₀M (inf_le_right.trans h47.2.1.le)
      ⟨L, _, f, hf, hker, isSimpleGroup_of_isL2OrA7 (by norm_num) h7⟩
      fun m hm _ hp hp2 _ hPp hAP hc hPgen => (hD2 hp hp2 hPp hAP hc hPgen).1 m hm
  have hN₀ : 𝔖.N₀ A ≤ normalizer (𝔖.WA A : Set G) := by
    obtain ⟨L, _, f, hf, hker, h5 | hK⟩ := h48.1
    · exact hsyl (Or.inr ⟨rfl, rfl⟩) hN₀N (inf_le_right.trans h48.2.1.le)
        ⟨L, _, f, hf, hker, isSimpleGroup_of_isL2OrA7 le_rfl h5⟩
        fun m hm _ hp hp2 _ hPp hAP hc hPgen => (hD2 hp hp2 hPp hAP hc hPgen).2 m hm
    ·
      have hcard : Nat.card (𝔖.N₀ A) = 4 * Nat.card (O (𝔖.N A)) := by
        rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
          Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv,
          hK.card_four, hker, Nat.card_congr (subgroupOfEquivOfLe hON₀).toEquiv]
      have hS₁N₀ : 𝔖.S₁ ≤ 𝔖.N₀ A := h48.2.1.le
      have hS₁N : 𝔖.S₁ ≤ normalizer (O (𝔖.N A) : Set G) :=
        (hS₁N₀.trans hN₀N).trans (le_normalizer_O _)
      have hS₁O : O (𝔖.N A) ⊓ 𝔖.S₁ = ⊥ := by
        rw [eq_bot_iff]
        intro g hg
        have h2 : IsPGroup 2 (O (𝔖.N A) ⊓ 𝔖.S₁ : Subgroup G) :=
          h48.2.1.isPGroup.to_le inf_le_right
        rcases h2.card_eq_or_dvd with h1 | h1
        · rw [card_eq_one] at h1
          rw [h1] at hg
          exact hg
        · exact absurd (h1.trans (card_dvd_of_le inf_le_left)) (Nat.two_dvd_ne_zero.mpr
            (Nat.odd_iff.mp (card_O_odd _)))
      have hsupcard := CFSG.CGT.Foote81L6.card_sup_of_le_normalizer hS₁N hS₁O
      have h4 := 𝔖.decomp.dih₁.four_le_card
      have hOpos : 0 < Nat.card (O (𝔖.N A)) := Nat.card_pos
      have hle : O (𝔖.N A) ⊔ 𝔖.S₁ ≤ 𝔖.N₀ A := sup_le hON₀ hS₁N₀
      have hcle := card_le_of_le hle
      rw [hsupcard, hcard] at hcle
      have hS₁4 : Nat.card 𝔖.S₁ = 4 := by
        have : Nat.card 𝔖.S₁ ≤ 4 := by
          by_contra! h
          have : 4 * Nat.card (O (𝔖.N A)) < Nat.card 𝔖.S₁ * Nat.card (O (𝔖.N A)) :=
            Nat.mul_lt_mul_of_pos_right h hOpos
          nlinarith
        omega
      have hN₀eq : O (𝔖.N A) ⊔ 𝔖.S₁ = 𝔖.N₀ A := eq_of_le_of_card_ge hle (by
        rw [hsupcard, hcard, hS₁4, mul_comm])
      have hXS₁ : 𝔖.X A = 𝔖.S₁ := eq_of_le_of_card_ge inf_le_right (by
        rw [hS₁4, hX.card_four])
      rw [← hN₀eq, ← hXS₁]
      refine sup_le hON (le_trans ?_ hCA)
      intro g hg
      exact mem_centralizer_iff.mpr fun h hh => hAab h hh g (hXA hg)
  refine ⟨?_, ?_, hNA⟩
  · rw [h47.2.2.1]
    exact sup_le hM₀ (inf_le_right.trans hNA)
  · rw [h48.2.2.1]
    exact sup_le hN₀ (inf_le_right.trans hNA)

theorem prop_6_4_of
    (h47 : QuotIs (𝔖.M₀ A) (O (𝔖.M A)) (fun L _ => IsL2OrA7 L 7) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₂ (𝔖.M₀ A) ∧
      𝔖.M A = 𝔖.M₀ A ⊔ (𝔖.M A ⊓ normalizer (A : Set G)) ∧
      𝔖.M A = 𝔖.M₀ A ⊔ (𝔖.M A ⊓ normalizer (𝔖.S₂ : Set G)) ∧
      (∀ x ∈ 𝔖.X A, x ≠ 1 → O2 (C x) = (O2 (𝔖.M A) ⊓ O2 (C x)) ⊔ O (C x)) ∧
      (∀ x ∈ 𝔖.X A, x ≠ 1 → ⁅O2 (C x), O2 (C x)⁆ ⊔ O (C x) =
        (𝔖.M₀ A ⊓ ⁅O2 (C x), O2 (C x)⁆) ⊔ O (C x)))
    (h48 : QuotIs (𝔖.N₀ A) (O (𝔖.N A)) (fun L _ => IsL2OrA7 L 5 ∨ IsKleinFour L) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₁ (𝔖.N₀ A) ∧
      𝔖.N A = 𝔖.N₀ A ⊔ (𝔖.N A ⊓ normalizer (A : Set G)) ∧
      𝔖.N A = 𝔖.N₀ A ⊔ (𝔖.N A ⊓ normalizer (𝔖.S₁ : Set G)) ∧
      (∀ y ∈ 𝔖.Y A, y ≠ 1 → O2 (C y) = (O2 (𝔖.N A) ⊓ O2 (C y)) ⊔ O (C y)) ∧
      (∀ y ∈ 𝔖.Y A, y ≠ 1 → ⁅O2 (C y), O2 (C y)⁆ ⊔ O (C y) =
        (𝔖.N₀ A ⊓ ⁅O2 (C y), O2 (C y)⁆) ⊔ O (C y)))
    (h410 : (∀ x ∈ 𝔖.X A, x ≠ 1 → ∀ a ∈ A, a ∉ 𝔖.Y A → O (C x) ⊓ C a ≤ O (C a)) ∧
      (∀ y ∈ 𝔖.Y A, y ≠ 1 → ∀ a ∈ A, a ∉ 𝔖.X A → O (C y) ⊓ C a ≤ O (C a)))
    (h411 : (∀ x ∈ 𝔖.X A, x ≠ 1 → ∀ D : Subgroup G, D ≤ C x → Odd (Nat.card D) →
        A ≤ normalizer (D : Set G) → ⁅D, 𝔖.X A⁆ ⊔ ⁅⁅D, 𝔖.Y A⁆, ⁅D, 𝔖.Y A⁆⁆ ≤ O (C x)) ∧
      (∀ y ∈ 𝔖.Y A, y ≠ 1 → ∀ D : Subgroup G, D ≤ C y → Odd (Nat.card D) →
        A ≤ normalizer (D : Set G) → ⁅D, 𝔖.Y A⁆ ⊔ ⁅⁅D, 𝔖.X A⁆, ⁅D, 𝔖.X A⁆⁆ ≤ O (C y)))
    (h412 : ∀ H : Subgroup G, H ≠ ⊤ → 𝔖.M A ≤ H → 𝔖.N A ≤ H →
      ∀ t ∈ H, orderOf t = 2 → ∃ h ∈ H, h * t * h⁻¹ ∈ A)
    (h413 : ∀ H : Subgroup G, H ≠ ⊤ →
      (Covers H (𝔖.M₀ A) (O (𝔖.M A)) → ∀ x ∈ 𝔖.X A, x ≠ 1 → x ∈ H → O H ⊓ C x ≤ O (C x)) ∧
      (Covers H (𝔖.N₀ A) (O (𝔖.N A)) → ∀ y ∈ 𝔖.Y A, y ≠ 1 → y ∈ H → O H ⊓ C y ≤ O (C y)))
    (h414 : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H → Covers H (𝔖.M₀ A) (O (𝔖.M A)) →
      Covers H (𝔖.N₀ A) (O (𝔖.N A)) → ∀ D : Subgroup G, D ≤ H → Odd (Nat.card D) →
        A ≤ normalizer (D : Set G) → (XYGenerated (𝔖.X A) (𝔖.Y A) D ↔ D ≤ O H))
    (h415 : ∀ a : G, a ∈ A → a ≠ 1 →
      C a ≤ xySup (𝔖.X A) (𝔖.Y A) (fun x y => O (C a) ⊓ O (C x) ⊓ O (C y)) ⊔
        (C a ⊓ 𝔖.M₀ A) ⊔ (C a ⊓ 𝔖.N₀ A) ⊔ (C a ⊓ normalizer (A : Set G)))
    (h46 : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ P₁ P₂ : Subgroup G, IsMaxInvIn p A ⊤ P₁ →
      IsMaxInvIn p A ⊤ P₂ → ∃ g ∈ normalizer (A : Set G), P₁.map (MulAut.conj g).toMonoidHom = P₂)
    (h54 : ∀ {p : ℕ}, p.Prime → p ≠ 2 → (∃ D : Subgroup G, IsPGroup p D ∧
      A ≤ normalizer (D : Set G) ∧ ¬ A ≤ centralizer (D : Set G) ∧
      XYGenerated (𝔖.X A) (𝔖.Y A) D) → ∃ H, 𝔖.IsCovering p A H)
    (h520 : ∀ {p : ℕ}, p.Prime → p ≠ 2 → ∀ P : Subgroup G, IsPGroup p P →
      A ≤ normalizer (P : Set G) → XYGenerated (𝔖.X A) (𝔖.Y A) P → ∀ Q : Subgroup G, Q ≤ P →
        A ≤ normalizer (Q : Set G) → XYGenerated (𝔖.X A) (𝔖.Y A) Q)
    (hW : 𝔖.WA A ≠ ⊥) : CFSG.IsStronglyEmbedded (normalizer (𝔖.WA A : Set G)) := by
  obtain ⟨hMK, hNK, hNA⟩ := 𝔖.prop_6_3_of hAS hA h47 h48 h410 h411 h413 h414 h46 h54 h520 hW
  have hWodd := 𝔖.prop_6_2_of hAS hA h410 h411 h520
  have hM₀M : 𝔖.M₀ A ≤ 𝔖.M A :=
    sup_le (commutator_self_le' _ |>.trans (map_subtype_le _)) (map_subtype_le _)
  have hN₀N : 𝔖.N₀ A ≤ 𝔖.N A :=
    sup_le (commutator_self_le' _ |>.trans (map_subtype_le _)) (map_subtype_le _)
  have hKne : normalizer (𝔖.WA A : Set G) ≠ ⊤ := by
    intro htop
    have hle : 𝔖.WA A ≤ CFSG.oddCore G := le_sSup ⟨normalizer_eq_top_iff.mp htop, hWodd⟩
    rw [𝔖.oddCore_eq_bot] at hle
    exact hW (le_bot_iff.mp hle)
  have hSK : (𝔖.S : Subgroup G) ≤ normalizer (𝔖.WA A : Set G) := by
    rw [← 𝔖.decomp.sup_eq]
    refine sup_le (le_trans ?_ hNK) (le_trans ?_ hMK)
    · intro g hg
      exact mem_centralizer_iff.mpr fun y hy => (𝔖.decomp.comm hg hy.2).symm
    · intro g hg
      exact mem_centralizer_iff.mpr fun x hx => 𝔖.decomp.comm hx.2 hg
  have hNS : normalizer ((𝔖.S : Subgroup G) : Set G) ≤ normalizer (𝔖.WA A : Set G) := by
    intro g hg
    have hBS : A.map (MulAut.conj g).toMonoidHom ≤ 𝔖.S := by
      rw [← map_conj_eq_self_of_mem_normalizer hg]
      exact map_mono hAS
    obtain ⟨s, hs, hsB⟩ := Sec3Setting.lemma_3_1 𝔖.toSec3Setting A _ hAS hBS hA
      (hA.map _ (MulAut.conj g).injective) g rfl
    have hsg : s⁻¹ * g ∈ normalizer (A : Set G) := by
      rw [mem_normalizer_iff_map_conj_eq]
      calc A.map (MulAut.conj (s⁻¹ * g)).toMonoidHom
          = (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj s⁻¹).toMonoidHom := by
            rw [Subgroup.map_map]
            congr 1
            ext x
            simp [mul_assoc]
        _ = (A.map (MulAut.conj s).toMonoidHom).map (MulAut.conj s⁻¹).toMonoidHom := by rw [hsB]
        _ = A := by
            rw [Subgroup.map_map]
            convert Subgroup.map_id A
            ext x
            simp [mul_assoc]
    have e : g = s * (s⁻¹ * g) := by group
    rw [e]
    exact mul_mem (hSK hs) (hNA hsg)
  have hCK : ∀ t ∈ normalizer (𝔖.WA A : Set G), orderOf t = 2 →
      C t ≤ normalizer (𝔖.WA A : Set G) := by
    intro t ht ht2
    obtain ⟨h, hh, hta⟩ := h412 _ hKne hMK hNK t ht ht2
    have ha1 : h * t * h⁻¹ ≠ 1 := by
      intro h1
      have : t = 1 := by
        have e : t = h⁻¹ * (h * t * h⁻¹) * h := by group
        rw [e, h1, mul_one, inv_mul_cancel]
      rw [this, orderOf_one] at ht2
      omega
    have hCa : C (h * t * h⁻¹) ≤ normalizer (𝔖.WA A : Set G) := by
      refine (h415 _ hta ha1).trans (sup_le (sup_le (sup_le ?_ ?_) ?_) ?_)
      · refine (xySupOf_le (X₀ := 𝔖.X A) (Y₀ := 𝔖.Y A) fun x hx hx1 y hy hy1 => ?_).trans
          le_normalizer
        exact (inf_le_inf_right _ (inf_le_inf_right _ (map_subtype_le _))).trans
          (𝔖.gen_le_WA hta ha1 hx hx1 hy hy1)
      · exact inf_le_right.trans (hM₀M.trans hMK)
      · exact inf_le_right.trans (hN₀N.trans hNK)
      · exact inf_le_right.trans hNA
    intro u hu
    have hu' : h * u * h⁻¹ ∈ C (h * t * h⁻¹) := by
      rw [mem_centralizer_singleton_iff] at hu ⊢
      calc h * u * h⁻¹ * (h * t * h⁻¹) = h * (u * t) * h⁻¹ := by group
        _ = h * (t * u) * h⁻¹ := by rw [hu]
        _ = h * t * h⁻¹ * (h * u * h⁻¹) := by group
    have e : u = h⁻¹ * (h * u * h⁻¹) * h := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hh) (hCa hu')) hh
  exact stronglyEmbedded_of_centralizers _ hKne 𝔖.S hSK hNS hCK

theorem prop_6_5_of
    (h47 : QuotIs (𝔖.M₀ A) (O (𝔖.M A)) (fun L _ => IsL2OrA7 L 7) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₂ (𝔖.M₀ A) ∧
      𝔖.M A = 𝔖.M₀ A ⊔ (𝔖.M A ⊓ normalizer (A : Set G)) ∧
      𝔖.M A = 𝔖.M₀ A ⊔ (𝔖.M A ⊓ normalizer (𝔖.S₂ : Set G)) ∧
      (∀ x ∈ 𝔖.X A, x ≠ 1 → O2 (C x) = (O2 (𝔖.M A) ⊓ O2 (C x)) ⊔ O (C x)) ∧
      (∀ x ∈ 𝔖.X A, x ≠ 1 → ⁅O2 (C x), O2 (C x)⁆ ⊔ O (C x) =
        (𝔖.M₀ A ⊓ ⁅O2 (C x), O2 (C x)⁆) ⊔ O (C x)))
    (h48 : QuotIs (𝔖.N₀ A) (O (𝔖.N A)) (fun L _ => IsL2OrA7 L 5 ∨ IsKleinFour L) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₁ (𝔖.N₀ A) ∧
      𝔖.N A = 𝔖.N₀ A ⊔ (𝔖.N A ⊓ normalizer (A : Set G)) ∧
      𝔖.N A = 𝔖.N₀ A ⊔ (𝔖.N A ⊓ normalizer (𝔖.S₁ : Set G)) ∧
      (∀ y ∈ 𝔖.Y A, y ≠ 1 → O2 (C y) = (O2 (𝔖.N A) ⊓ O2 (C y)) ⊔ O (C y)) ∧
      (∀ y ∈ 𝔖.Y A, y ≠ 1 → ⁅O2 (C y), O2 (C y)⁆ ⊔ O (C y) =
        (𝔖.N₀ A ⊓ ⁅O2 (C y), O2 (C y)⁆) ⊔ O (C y)))
    (h410 : (∀ x ∈ 𝔖.X A, x ≠ 1 → ∀ a ∈ A, a ∉ 𝔖.Y A → O (C x) ⊓ C a ≤ O (C a)) ∧
      (∀ y ∈ 𝔖.Y A, y ≠ 1 → ∀ a ∈ A, a ∉ 𝔖.X A → O (C y) ⊓ C a ≤ O (C a)))
    (h411 : (∀ x ∈ 𝔖.X A, x ≠ 1 → ∀ D : Subgroup G, D ≤ C x → Odd (Nat.card D) →
        A ≤ normalizer (D : Set G) → ⁅D, 𝔖.X A⁆ ⊔ ⁅⁅D, 𝔖.Y A⁆, ⁅D, 𝔖.Y A⁆⁆ ≤ O (C x)) ∧
      (∀ y ∈ 𝔖.Y A, y ≠ 1 → ∀ D : Subgroup G, D ≤ C y → Odd (Nat.card D) →
        A ≤ normalizer (D : Set G) → ⁅D, 𝔖.Y A⁆ ⊔ ⁅⁅D, 𝔖.X A⁆, ⁅D, 𝔖.X A⁆⁆ ≤ O (C y)))
    (h412 : ∀ H : Subgroup G, H ≠ ⊤ → 𝔖.M A ≤ H → 𝔖.N A ≤ H →
      ∀ t ∈ H, orderOf t = 2 → ∃ h ∈ H, h * t * h⁻¹ ∈ A)
    (h413 : ∀ H : Subgroup G, H ≠ ⊤ →
      (Covers H (𝔖.M₀ A) (O (𝔖.M A)) → ∀ x ∈ 𝔖.X A, x ≠ 1 → x ∈ H → O H ⊓ C x ≤ O (C x)) ∧
      (Covers H (𝔖.N₀ A) (O (𝔖.N A)) → ∀ y ∈ 𝔖.Y A, y ≠ 1 → y ∈ H → O H ⊓ C y ≤ O (C y)))
    (h414 : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H → Covers H (𝔖.M₀ A) (O (𝔖.M A)) →
      Covers H (𝔖.N₀ A) (O (𝔖.N A)) → ∀ D : Subgroup G, D ≤ H → Odd (Nat.card D) →
        A ≤ normalizer (D : Set G) → (XYGenerated (𝔖.X A) (𝔖.Y A) D ↔ D ≤ O H))
    (h415 : ∀ a : G, a ∈ A → a ≠ 1 →
      C a ≤ xySup (𝔖.X A) (𝔖.Y A) (fun x y => O (C a) ⊓ O (C x) ⊓ O (C y)) ⊔
        (C a ⊓ 𝔖.M₀ A) ⊔ (C a ⊓ 𝔖.N₀ A) ⊔ (C a ⊓ normalizer (A : Set G)))
    (h46 : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ P₁ P₂ : Subgroup G, IsMaxInvIn p A ⊤ P₁ →
      IsMaxInvIn p A ⊤ P₂ → ∃ g ∈ normalizer (A : Set G), P₁.map (MulAut.conj g).toMonoidHom = P₂)
    (h54 : ∀ {p : ℕ}, p.Prime → p ≠ 2 → (∃ D : Subgroup G, IsPGroup p D ∧
      A ≤ normalizer (D : Set G) ∧ ¬ A ≤ centralizer (D : Set G) ∧
      XYGenerated (𝔖.X A) (𝔖.Y A) D) → ∃ H, 𝔖.IsCovering p A H)
    (h520 : ∀ {p : ℕ}, p.Prime → p ≠ 2 → ∀ P : Subgroup G, IsPGroup p P →
      A ≤ normalizer (P : Set G) → XYGenerated (𝔖.X A) (𝔖.Y A) P → ∀ Q : Subgroup G, Q ≤ P →
        A ≤ normalizer (Q : Set G) → XYGenerated (𝔖.X A) (𝔖.Y A) Q) :
    ∀ a ∈ A, a ≠ 1 → theta (𝔖.X A) (𝔖.Y A) a = ⊥ :=
  𝔖.prop_6_5_of_prop_6_4 fun hW =>
    𝔖.prop_6_4_of hAS hA h47 h48 h410 h411 h412 h413 h414 h415 h46 h54 h520 hW

end Sec4Setting

end CFSG.GH72
