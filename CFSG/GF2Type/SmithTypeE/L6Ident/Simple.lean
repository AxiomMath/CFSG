module

public import CFSG.GF2Type.SmithTypeE.L6Ident.Fusion
public import CFSG.GF2Type.SmithTypeE.FourSevenGen
public import CFSG.LargeExtraspecial.S14SMJSub

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.L6Ident

open Subgroup CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14 CFSG.GF2Type.SmithTypeE.L6
open scoped MatrixGroups

variable {G : Type} [Group G]

variable [Finite G] [IsSimpleGroup G] (hE : SmithL6E23a) (S : Setting G) (hw : S.width = 10)
  (hU : Nonempty (Mbar0 S ≃* PSL(6, ZMod 2))) {t u : G} (ht : IsConj S.z t) (hu : IsConj S.z u)
  (htM : t ∈ S.M) (huM : u ∈ S.M) (htQ : t ∉ S.QG) (huQ : u ∉ S.QG) (htu : orderOf (t * u) = 3)

include hE hw hU ht hu htM huM htQ huQ htu in
theorem exists_simple_le_cent2 :
    ∃ K : Subgroup G, K ≤ cent2 t u ∧ S.z ∈ K ∧ IsSimpleGroup K ∧ S.QG ⊓ cent2 t u ≤ K ∧
      (∀ h ∈ cent2 t u, h * S.z * h⁻¹ ∈ K) ∧ ∀ h ∈ cent2 t u, ∀ k ∈ K, h * k * h⁻¹ ∈ K := by
  classical
  have hzH : S.z ∈ cent2 t u := z_mem_cent2 S htM huM
  have hmem : ∀ {x : G}, x ∈ S.QG ⊓ cent2 t u ↔ x ∈ S.QG ∧ Commute x t ∧ Commute x u :=
    fun {x} => by rw [mem_inf, mem_cent2]
  obtain ⟨hext, hcard, hgenE, hcent, hO2⟩ := hE G S hw hU t u ht hu htM huM htQ huQ htu
  set T := SMJ.subSetting S (cent2 t u) hzH hext hcent hO2 with hT
  have hTz : ((T.z : cent2 t u) : G) = S.z := rfl
  have hTQ : ∀ {x : cent2 t u}, x ∈ T.QG ↔ (x : G) ∈ S.QG := fun {x} =>
    SMJ.mem_subSetting_QG_iff S _ hzH hext hcent hO2
  have hTM : ∀ {x : cent2 t u}, x ∈ T.M ↔ (x : G) ∈ S.M := fun {x} =>
    SMJ.mem_subSetting_M_iff S _ hzH hext hcent hO2
  have hfus : ∀ a : G, IsConj S.z a → a ∈ S.QG → a ≠ S.z → a ∈ cent2 t u →
      ∃ h ∈ cent2 t u, h * S.z * h⁻¹ = S.z * a := by
    intro a ha haQ haz haH
    obtain ⟨hat, hau⟩ := mem_cent2.mp haH
    obtain ⟨q, hqt, hqu, hq⟩ := exists_conj_eq_z_mul hE S hw hU ht hu htM huM htu ha haQ haz hat hau
    exact ⟨q, mem_cent2.mpr ⟨hqt, hqu⟩, hq⟩
  let X : Set (cent2 t u) := {x | IsConj S.z (x : G) ∧ (x : G) ∈ S.QG ∧ (x : G) ≠ S.z}
  have hXQ : X ⊆ T.QG := fun x hx => hTQ.mpr hx.2.1
  have hX2 : ∀ x ∈ X, x * x = 1 := fun x hx =>
    Subtype.ext (SmithQ.mul_self_eq_one_of_isConj S hx.1)
  have hXzmul : ∀ x ∈ X, x * T.z ∈ X := by
    intro x hx
    obtain ⟨hxD, hxQ, hxz⟩ := hx
    have hx1 : (x : G) ≠ 1 := SME.ne_one_of_isConj S hxD
    have hxzz : (x : G) * S.z ≠ S.z := fun h => hx1 (by
      calc (x : G) = (x : G) * S.z * S.z⁻¹ := by group
        _ = 1 := by rw [h, mul_inv_cancel])
    exact ⟨isConj_mul_z S hxD hxQ hxz, S.QG.mul_mem hxQ S.z_mem_QG, hxzz⟩
  have hgenD : ∀ (L : Subgroup G), S.z ∈ L →
      (∀ a : G, IsConj S.z a → a ∈ S.QG → a ≠ S.z → a ∈ cent2 t u → a ∈ L) →
      S.QG ⊓ cent2 t u ≤ L := by
    intro L hzL hL q hq
    refine (closure_le L).mpr ?_ (hgenE hq)
    rintro c ⟨hc, hcQ, hcH⟩
    by_cases hcz : c = S.z
    · rw [hcz]; exact hzL
    · exact hL c hc hcQ hcz hcH
  have hXne : X.Nonempty := by
    by_contra hX
    have hle := hgenD (zpowers S.z) (mem_zpowers _) fun a ha haQ haz haH =>
      absurd ⟨⟨a, haH⟩, ha, haQ, haz⟩ hX
    have := Subgroup.card_le_of_le hle
    rw [hcard, Nat.card_zpowers, S.orderOf_z] at this
    norm_num at this
  have hgen : T.QG ≤ closure (X ∪ {T.z}) := by
    have hle : S.QG ⊓ cent2 t u ≤ (closure (X ∪ {T.z})).map (cent2 t u).subtype :=
      hgenD _ ⟨T.z, subset_closure (Or.inr rfl), rfl⟩ fun a ha haQ haz haH =>
        ⟨⟨a, haH⟩, subset_closure (Or.inl ⟨ha, haQ, haz⟩), rfl⟩
    intro q hq
    obtain ⟨q', hq', hq'e⟩ := hle (mem_inf.mpr ⟨hTQ.mp hq, q.2⟩)
    rwa [show q' = q from Subtype.ext hq'e] at hq'
  have hO : ∀ x ∈ X, T.ZInOTwo x := by
    intro x hx
    obtain ⟨hxD, hxQ, hxz⟩ := hx
    obtain ⟨g, hg⟩ := isConj_iff.mp hxD
    let P : Subgroup (cent2 t u) :=
      (S.QG.map (MulAut.conj g).toMonoidHom).comap (cent2 t u).subtype
    have hmemP : ∀ {p : cent2 t u}, p ∈ P ↔ g⁻¹ * (p : G) * g ∈ S.QG := fun {p} => by
      simp only [P, mem_comap, mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        coe_subtype]
      constructor
      · rintro ⟨q, hq, hqe⟩
        rw [← hqe]
        simpa [mul_assoc] using hq
      · intro h
        exact ⟨_, h, by group⟩
    have hcx : ∀ {c : cent2 t u}, c ∈ centralizer ({x} : Set (cent2 t u)) →
        g⁻¹ * (c : G) * g ∈ S.M := fun {c} hc => by
      have hc' : (c : G) * (x : G) = (x : G) * c := by
        have := mem_centralizer_singleton_iff.mp hc
        exact congrArg Subtype.val this
      rw [mem_centralizer_singleton_iff]
      rw [← hg] at hc'
      calc g⁻¹ * (c : G) * g * S.z = g⁻¹ * ((c : G) * (g * S.z * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * S.z * g⁻¹) * c) * g := by rw [hc']
        _ = S.z * (g⁻¹ * (c : G) * g) := by group
    refine T.zInOTwo_of_le (P := P) ?_ ?_ ?_ ?_
    · intro p hp
      rw [mem_centralizer_singleton_iff]
      apply Subtype.ext
      have h1 := mem_centralizer_singleton_iff.mp (S.QG_le_M (hmemP.mp hp))
      simp only [Subgroup.coe_mul]
      rw [← hg]
      calc (p : G) * (g * S.z * g⁻¹) = g * ((g⁻¹ * (p : G) * g) * S.z) * g⁻¹ := by group
        _ = g * (S.z * (g⁻¹ * (p : G) * g)) * g⁻¹ := by rw [h1]
        _ = g * S.z * g⁻¹ * p := by group
    · intro c hc p hp
      rw [hmemP]
      have := S.conj_mem_QG (hcx hc) (hmemP.mp hp)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [show g⁻¹ * ((c : G) * p * (c : G)⁻¹) * g =
            g⁻¹ * c * g * (g⁻¹ * p * g) * (g⁻¹ * c * g)⁻¹ by group]
      exact this
    · exact (S.isPGroup_QG.map _).comap_of_injective _ (cent2 t u).subtype_injective
    · rw [hmemP, hTz]
      have hxQa := S.z_mem_Qa (g := g) (by rw [hg]; exact hxQ) (by rw [hg]; exact hxz)
      exact (SME.mem_Qa_iff S g S.z).mp hxQa
  have hzK : S.z ∈ T.zGen.map (cent2 t u).subtype := ⟨T.z, T.z_mem_zGen, rfl⟩
  have hzaK : ∀ a : G, IsConj S.z a → a ∈ S.QG → a ≠ S.z → a ∈ cent2 t u →
      S.z * a ∈ T.zGen.map (cent2 t u).subtype := by
    intro a ha haQ haz haH
    obtain ⟨h, hH, hh⟩ := hfus a ha haQ haz haH
    exact ⟨⟨h, hH⟩ * T.z * ⟨h, hH⟩⁻¹, T.conj_mem_zGen _, by rw [← hh]; rfl⟩
  have hmemK : ∀ a : G, IsConj S.z a → a ∈ S.QG → a ≠ S.z → a ∈ cent2 t u →
      a ∈ T.zGen.map (cent2 t u).subtype := by
    intro a ha haQ haz haH
    have := (T.zGen.map (cent2 t u).subtype).mul_mem
      ((T.zGen.map (cent2 t u).subtype).inv_mem hzK) (hzaK a ha haQ haz haH)
    rwa [inv_mul_cancel_left] at this
  have hQK : S.QG ⊓ cent2 t u ≤ T.zGen.map (cent2 t u).subtype := hgenD _ hzK hmemK
  obtain ⟨⟨a₁, ha₁H⟩, ha₁D, ha₁Q, ha₁z⟩ := hXne
  rcases T.fourSeven_gen hXQ hX2 hXzmul ⟨_, ha₁D, ha₁Q, ha₁z⟩ hgen hO with hMtop | habel |
    ⟨hsimp, -⟩
  ·
    exfalso
    obtain ⟨h, hH, hh⟩ := hfus a₁ ha₁D ha₁Q ha₁z ha₁H
    have hhM : h ∈ S.M := hTM.mp (hMtop ▸ Subgroup.mem_top (⟨h, hH⟩ : cent2 t u))
    have : S.z * a₁ = S.z := by
      rw [← hh, S.z_comm hhM]; group
    exact SME.ne_one_of_isConj S ha₁D (by simpa using this)
  ·
    exfalso
    set Z' := T.zGen.map (cent2 t u).subtype with hZ'
    have hinv : ∀ x ∈ T.zGen, x * x = 1 := fun x hx => by
      by_cases hx1 : x = 1
      · rw [hx1, one_mul]
      · obtain ⟨c, rfl⟩ := isConj_iff.mp (habel x hx hx1)
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one]
        rw [show (c : G) * (T.z : G) * (c : G)⁻¹ * ((c : G) * (T.z : G) * (c : G)⁻¹) =
          (c : G) * ((T.z : G) * (T.z : G)) * (c : G)⁻¹ by group, hTz,
          SmithQ.mul_self_eq_one_of_isConj S (IsConj.refl _)]
        group
    have hinv' : ∀ x ∈ Z', x * x = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      have := congrArg Subtype.val (hinv x hx)
      simpa using this
    have hcommZ : ∀ x ∈ Z', ∀ y ∈ Z', x * y = y * x := fun x hx y hy => by
      have h1 := hinv' x hx
      have h2 := hinv' y hy
      have hyx : (y * x)⁻¹ = y * x := (eq_inv_of_mul_eq_one_left (hinv' _ (Z'.mul_mem hy hx))).symm
      calc x * y = x * y * (y * x) * (y * x)⁻¹ := by group
        _ = y * x := by
            rw [show x * y * (y * x) = x * (y * y) * x by group, h2, mul_one, h1, one_mul, hyx]
    have hab : ∀ x : ↥(S.QG ⊓ cent2 t u), ∀ y : ↥(S.QG ⊓ cent2 t u), x * y = y * x :=
      fun x y => Subtype.ext (hcommZ x (hQK x.2) y (hQK y.2))
    have hctop : center ↥(S.QG ⊓ cent2 t u) = ⊤ :=
      Subgroup.eq_top_iff' _ |>.mpr fun x => Subgroup.mem_center_iff.mpr fun y => (hab y x)
    have h2 := hext.2.2.2
    rw [hctop, Subgroup.card_top, hcard] at h2
    norm_num at h2
  ·
    refine ⟨T.zGen.map (cent2 t u).subtype, Subgroup.map_subtype_le _, hzK,
      (Subgroup.equivMapOfInjective T.zGen _ (cent2 t u).subtype_injective).symm.isSimpleGroup,
      hQK, fun h hH => ⟨⟨h, hH⟩ * T.z * ⟨h, hH⟩⁻¹, T.conj_mem_zGen _, rfl⟩, ?_⟩
    rintro h hH _ ⟨k, hk, rfl⟩
    exact ⟨⟨h, hH⟩ * k * ⟨h, hH⟩⁻¹, T.zGen_normal.conj_mem k hk _, rfl⟩

end CFSG.GF2Type.SmithTypeE.L6Ident
