module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX2E6LAmbient
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX2E6Red

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator

theorem kd264X2E6Row_of_localP (hL : X2E6LocalP (fun G => Nat.card G = 9))
    (hW : X2E6WeylCore) : KD264X2E6Row := by
  obtain ⟨hW1, hW2⟩ := hW
  intro d _ q _ _ _ hd hq A hA hm
  have hp3 : Nat.Prime 3 := by norm_num
  obtain ⟨Q, hAQ⟩ := IsPGroup.exists_le_sylow (isPGroup_of_isElemAbelian hA)
  obtain ⟨V, φ, ρ, _, _, hequi, hker, hrange, hcrit⟩ := hL d q hd hq Q
  obtain ⟨m, hmA⟩ := exists_card_eq_pow_of_isElemAbelian hp3 hA
  have hpm : CFSG.Open.pRank 3 A = m := pRank_eq_of_card_eq hp3 hA hmA
  have hm5 : 5 ≤ m := by rw [hpm] at hm; exact hm
  have hAqc : Nat.card (A.subgroupOf (Q : Subgroup _)) = 3 ^ m := by
    rw [← hmA]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAQ).toEquiv
  have hcomm : ∀ y z : A.subgroupOf (Q : Subgroup _), y * z = z * y := by
    intro y z
    apply Subtype.ext
    apply Subtype.ext
    exact isElemAbelian_commute hA (Subgroup.mem_subgroupOf.1 y.2)
      (Subgroup.mem_subgroupOf.1 z.2)
  have hcube : ∀ y : A.subgroupOf (Q : Subgroup _), y ^ 3 = 1 := by
    intro y
    apply Subtype.ext
    apply Subtype.ext
    exact hA.2 _ (Subgroup.mem_subgroupOf.1 y.2)
  let fA : A.subgroupOf (Q : Subgroup _) →* Matrix.GeneralLinearGroup (Fin 6) (ZMod 3) :=
    ρ.comp (A.subgroupOf (Q : Subgroup _)).subtype
  have hRab : IsElemAbelian 3 fA.range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 a.2
      obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 b.2
      apply Subtype.ext
      show (a : Matrix.GeneralLinearGroup (Fin 6) (ZMod 3)) * (b : Matrix.GeneralLinearGroup (Fin 6) (ZMod 3)) =
        (b : Matrix.GeneralLinearGroup (Fin 6) (ZMod 3)) * (a : Matrix.GeneralLinearGroup (Fin 6) (ZMod 3))
      rw [← hy, ← hz, ← map_mul, ← map_mul, hcomm y z]
    · obtain ⟨y, rfl⟩ := MonoidHom.mem_range.1 hx
      show fA y ^ 3 = 1
      rw [← map_pow, hcube y, map_one]
  obtain ⟨r, hrR⟩ := exists_card_eq_pow_of_isElemAbelian hp3 hRab
  have hdiv := Subgroup.card_ker_mul_card_range fA
  rw [hAqc, hrR] at hdiv
  have hrm : r ≤ m := by
    have : 3 ^ r ∣ 3 ^ m := Dvd.intro_left _ hdiv
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 this
  have hkerc : Nat.card fA.ker = 3 ^ (m - r) := by
    apply Nat.eq_of_mul_eq_mul_right (pow_pos (by norm_num : (0 : ℕ) < 3) r)
    rw [hdiv, ← pow_add, Nat.sub_add_cancel hrm]
  let g1 : fA.ker →* MulAut (TauCeti.CFSGIndex.lie d).Group :=
    (Q : Subgroup _).subtype.comp ((A.subgroupOf (Q : Subgroup _)).subtype.comp fA.ker.subtype)
  have hgV : ∀ x : fA.ker, g1 x ∈ V := by
    intro x
    have h1 : ρ (x.1).1 = 1 := MonoidHom.mem_ker.1 x.2
    exact (hker (x.1).1).1 h1
  let g2 : fA.ker →* V := g1.codRestrict V hgV
  have hgxA : ∀ x : fA.ker, ((g2 x : V) : MulAut (TauCeti.CFSGIndex.lie d).Group) ∈ A :=
    fun x => Subgroup.mem_subgroupOf.1 x.1.2
  let ψ : fA.ker →* Multiplicative (Fin 6 → ZMod 3) := φ.toMonoidHom.comp g2
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    have h1 : g2 x = g2 y := φ.injective hxy
    have h2 : ((g2 x : V) : MulAut (TauCeti.CFSGIndex.lie d).Group) =
        ((g2 y : V) : MulAut (TauCeti.CFSGIndex.lie d).Group) := congrArg Subtype.val h1
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact h2
  let Ucoord : AddSubgroup (Fin 6 → ZMod 3) := Subgroup.toAddSubgroup' ψ.range
  have hmemU : ∀ a : Fin 6 → ZMod 3, a ∈ Ucoord ↔ Multiplicative.ofAdd a ∈ ψ.range :=
    fun a => Subgroup.mem_toAddSubgroup' _ a
  have hUcard : Nat.card Ucoord = 3 ^ (m - r) := by
    rw [show Ucoord = Subgroup.toAddSubgroup' ψ.range from rfl, card_toAddSubgroup_eq,
      MonoidHom.range_eq_map, Subgroup.card_map_of_injective hψinj, Subgroup.card_top, hkerc]
  have hUfix : (Ucoord : Set (Fin 6 → ZMod 3)) ⊆ fixVec fA.range := by
    intro a ha
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 ((hmemU a).1 ha)
    have hφx : Multiplicative.toAdd (φ (g2 x)) = a := by
      have h1 : φ (g2 x) = Multiplicative.ofAdd a := hx
      rw [h1, toAdd_ofAdd]
    unfold fixVec
    intro g hg
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.1 hg
    have hy : (y.1 : MulAut (TauCeti.CFSGIndex.lie d).Group) ∈ A :=
      Subgroup.mem_subgroupOf.1 y.2
    have hcommut : (y.1 : MulAut (TauCeti.CFSGIndex.lie d).Group) * ((g2 x : V) : MulAut (TauCeti.CFSGIndex.lie d).Group) *
        ((y.1 : MulAut (TauCeti.CFSGIndex.lie d).Group))⁻¹ = ((g2 x : V) : MulAut (TauCeti.CFSGIndex.lie d).Group) := by
      rw [mul_inv_eq_iff_eq_mul]
      exact isElemAbelian_commute hA hy (hgxA x)
    have key := hequi y.1 (g2 x) (g2 x) hcommut
    show Matrix.mulVec (ρ y.1 : Matrix (Fin 6) (Fin 6) (ZMod 3)) a = a
    calc Matrix.mulVec (ρ y.1 : Matrix (Fin 6) (Fin 6) (ZMod 3)) a
        = Matrix.mulVec (ρ y.1 : Matrix (Fin 6) (Fin 6) (ZMod 3))
            (Multiplicative.toAdd (φ (g2 x))) := by rw [hφx]
      _ = Multiplicative.toAdd (φ (g2 x)) := key.symm
      _ = a := hφx
  have hR_le : fA.range ≤ W3 := by
    rintro _ ⟨y, rfl⟩
    exact hrange y.1
  rcases Nat.lt_or_ge r 2 with hr2 | hr2
  ·
    have key : ∃ F : AddSubgroup (Fin 6 → ZMod 3), (F : Set (Fin 6 → ZMod 3)) ⊆ Ucoord ∧
        Nat.card F = 9 ∧ RootGood (F : Set (Fin 6 → ZMod 3)) := by
      rcases Nat.lt_or_ge r 1 with hr0 | hr1
      · exact weyl_rank0 Ucoord (by rw [hUcard]; exact Nat.pow_le_pow_right (by norm_num) (by omega))
      · exact hW2 fA.range hR_le hRab r hrR (by omega) Ucoord hUfix
          (by rw [hUcard]; exact Nat.pow_le_pow_right (by norm_num) (by omega))
    obtain ⟨F, hFU, hFcard, hgood⟩ := key
    let G : Subgroup (Multiplicative (Fin 6 → ZMod 3)) := (Subgroup.toAddSubgroup').symm F
    have hGF : Subgroup.toAddSubgroup' G = F := OrderIso.apply_symm_apply _ F
    have hmemG : ∀ a : Fin 6 → ZMod 3, Multiplicative.ofAdd a ∈ G ↔ a ∈ F := by
      intro a
      rw [← Subgroup.mem_toAddSubgroup', hGF]
    have himg : (fun g : Multiplicative (Fin 6 → ZMod 3) => Multiplicative.toAdd g) ''
        (G : Set (Multiplicative (Fin 6 → ZMod 3))) = (F : Set (Fin 6 → ZMod 3)) := by
      ext a
      constructor
      · rintro ⟨g, hg, rfl⟩
        exact (hmemG (Multiplicative.toAdd g)).1 (by simpa using hg)
      · intro ha
        exact ⟨Multiplicative.ofAdd a, (hmemG a).2 ha, rfl⟩
    have hGood : RootGood ((fun g : Multiplicative (Fin 6 → ZMod 3) => Multiplicative.toAdd g) ''
        (G : Set (Multiplicative (Fin 6 → ZMod 3)))) := by
      rw [himg]; exact hgood
    have hGcard : Nat.card G = 9 := by rw [← card_toAddSubgroup_eq G, hGF, hFcard]
    have hFg : ∀ g ∈ G, Multiplicative.toAdd g ∈ Ucoord := fun g hg =>
      hFU ((hmemG (Multiplicative.toAdd g)).1 (by simpa using hg))
    have hFA : (G.map φ.symm.toMonoidHom).map V.subtype ≤ A := by
      rintro z hz
      obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hz
      obtain ⟨g, hg, hgv⟩ := Subgroup.mem_map.1 hv
      obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 ((hmemU _).1 (hFg g hg))
      have h1 : φ (g2 x) = g := by
        have h2 : φ (g2 x) = Multiplicative.ofAdd (Multiplicative.toAdd g) := hx
        rw [h2, ofAdd_toAdd]
      have h3 : φ v = g := by
        rw [← hgv]
        exact φ.apply_symm_apply g
      have hgx : g2 x = v := by
        apply φ.injective
        rw [h1, h3]
      show V.subtype v ∈ A
      rw [← hgx]
      exact hgxA x
    have hF'V : (G.map φ.symm.toMonoidHom).map V.subtype ≤ V := by
      rintro z hz
      obtain ⟨v, _, rfl⟩ := Subgroup.mem_map.1 hz
      exact v.2
    have hF'ab := isElemAbelian_mono (isElemAbelian_of_mulEquiv V φ) hF'V
    have hinj1 : Function.Injective V.subtype := Subtype.val_injective
    have hcardF' : Nat.card ↥((G.map φ.symm.toMonoidHom).map V.subtype) = 9 := by
      rw [Subgroup.card_map_of_injective hinj1, Subgroup.card_map_of_injective φ.symm.injective,
        hGcard]
    exact ⟨(G.map φ.symm.toMonoidHom).map V.subtype, hFA, hF'ab,
      pRank_eq_of_card_eq hp3 hF'ab (n := 2) (hcardF'.trans (by norm_num)),
      hcrit G hGcard (by rw [himg]; exact hgood)⟩
  · exfalso
    obtain ⟨hr3, hfix⟩ := hW1 fA.range hR_le hRab r hrR
    have h1 := hfix hr2
    have h2 : Nat.card Ucoord ≤ Nat.card (fixVec fA.range) :=
      Nat.card_mono (Set.toFinite _) hUfix
    rw [hUcard] at h2
    have h3 : 3 ^ (4 - r) < 3 ^ (m - r) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    exact absurd (h2.trans h1) (not_le.2 h3)

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6

end
