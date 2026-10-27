module

public import CFSG.GH74.QTGen4.GL4.Embed
public import CFSG.GH74.QTGen4.U42.VertexGen4B

public section

namespace CFSG.GH74.QTGen4.U42.VertexGen4

open CFSG.Quasithin CFSG.Open

theorem isCharP_of_charTwo {G : Type} [Group G] {H : Subgroup G}
    (h : CFSG.QuasithinUnique.CharTwo H) : CFSG.IsCharacteristicP 2 ↥H := by
  intro x hx
  have hx' : (x : G) ∈ H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) := by
    refine ⟨x.2, Subgroup.mem_centralizer_iff.2 fun z hz => ?_⟩
    obtain ⟨y, hy, rfl⟩ := hz
    have := Subgroup.mem_centralizer_iff.1 hx y (by rwa [CFSG.pCore_eq_open])
    exact congrArg Subtype.val this
  obtain ⟨y, hy, hyx⟩ := h hx'
  have : y = x := Subtype.ext hyx
  rw [CFSG.pCore_eq_open]
  exact this ▸ hy

@[expose] def cj {G : Type} [Group G] {L X : Subgroup G} (hN : X ≤ Subgroup.normalizer (L : Set G))
    (g : ↥X) : ↥L →* ↥L where
  toFun l := ⟨(g : G) * l * (g : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hN g.2) l).mp l.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

theorem cj_coe {G : Type} [Group G] {L X : Subgroup G} (hN : X ≤ Subgroup.normalizer (L : Set G))
    (g : ↥X) (l : ↥L) : ((cj hN g l : ↥L) : G) = (g : G) * (l : G) * (g : G)⁻¹ := rfl

theorem cj_inv {G : Type} [Group G] {L X : Subgroup G} (hN : X ≤ Subgroup.normalizer (L : Set G))
    (g : ↥X) (a : ↥L) : cj hN g⁻¹ (cj hN g a) = a :=
  Subtype.ext (by simp [cj_coe, mul_assoc])

theorem cj_injective {G : Type} [Group G] {L X : Subgroup G}
    (hN : X ≤ Subgroup.normalizer (L : Set G)) (g : ↥X) : Function.Injective (cj hN g) := by
  intro a b hab
  have h := congrArg (cj hN g⁻¹) hab
  rwa [cj_inv, cj_inv] at h

theorem pCore_conj_mem {G : Type} [Group G] {L X : Subgroup G}
    (hN : X ≤ Subgroup.normalizer (L : Set G)) (g : ↥X) {n : ↥L}
    (hn : n ∈ CFSG.pCore 2 ↥L) : cj hN g n ∈ CFSG.pCore 2 ↥L := by
  let M : Subgroup ↥L := (CFSG.pCore 2 ↥L).comap (cj hN g⁻¹)
  have hMn : M.Normal := inferInstance
  have hMp : IsPGroup 2 M :=
    IsPGroup.comap_of_injective (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) (cj hN g⁻¹)
      (cj_injective hN g⁻¹)
  have hMle : M ≤ CFSG.pCore 2 ↥L := le_sSup ⟨hMn, hMp⟩
  refine hMle ?_
  show cj hN g n ∈ (CFSG.pCore 2 ↥L).comap (cj hN g⁻¹)
  rw [Subgroup.mem_comap, cj_inv]
  exact hn

theorem pCore_map_le {G : Type} [Group G] {L X : Subgroup G} (hLX : L ≤ X)
    (hN : X ≤ Subgroup.normalizer (L : Set G)) :
    (CFSG.pCore 2 ↥L).map (Subgroup.inclusion hLX) ≤ CFSG.pCore 2 ↥X := by
  let N' : Subgroup ↥X := (CFSG.pCore 2 ↥L).map (Subgroup.inclusion hLX)
  have hN'n : N'.Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨cj hN g m, pCore_conj_mem hN g hm, ?_⟩
    exact Subtype.ext rfl
  have hN'p : IsPGroup 2 N' :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).map (Subgroup.inclusion hLX)
  exact le_sSup ⟨hN'n, hN'p⟩

theorem comap_pCore_le {G : Type} [Group G] {L X : Subgroup G} (hLX : L ≤ X) :
    (CFSG.pCore 2 ↥X).comap (Subgroup.inclusion hLX) ≤ CFSG.pCore 2 ↥L := by
  have hn : ((CFSG.pCore 2 ↥X).comap (Subgroup.inclusion hLX)).Normal := inferInstance
  have hp : IsPGroup 2 ((CFSG.pCore 2 ↥X).comap (Subgroup.inclusion hLX)) :=
    IsPGroup.comap_of_injective (CFSG.pCore_isPGroup (p := 2) (G := ↥X)) _
      (Subgroup.inclusion_injective hLX)
  exact le_sSup ⟨hn, hp⟩

theorem isL2Quot_two_of_gen4 {G : Type} [Group G] [Finite G] (hG : CFSG.GH74.Gen4 G)
    {Li Lj S : Subgroup G} (h : CFSG.Quasithin.Hyp111At Li Lj S) (hns : ¬ Group.IsSolvable ↥Li) :
    CFSG.Quasithin.IsL2Quot 2 (CFSG.Quasithin.oTwoQuot ↥Li) := by
  let X : Subgroup G := Li ⊔ S ⊔ CFSG.Quasithin.borelOf Lj S
  have hLX : Li ≤ X := le_trans le_sup_left le_sup_left
  have hNX : X ≤ Subgroup.normalizer (Li : Set G) :=
    sup_le (sup_le Subgroup.le_normalizer h.normalizes) h.borel_le
  have hXp : CFSG.IsCharacteristicP 2 ↥X := isCharP_of_charTwo h.charTwo
  have hXg : CFSG.GH74.Gen4 ↥X := CFSG.GH74.Gen4.subgroup X hG
  obtain ⟨ψX, hψX⟩ := CFSG.GH74.QTGen4.exists_injective_quotient_pCore_to_GL4 hXp hXg
  let f : ↥Li →* ↥X ⧸ CFSG.pCore 2 ↥X :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥X)).comp (Subgroup.inclusion hLX)
  let φ : ↥Li →* GL (Fin 4) (ZMod 2) := ψX.comp f
  have hker : φ.ker ≤ CFSG.pCore 2 ↥Li := by
    intro g hg
    have h1 : f g = 1 := (injective_iff_map_eq_one ψX).mp hψX (f g) hg
    have h2 : Subgroup.inclusion hLX g ∈ CFSG.pCore 2 ↥X := (QuotientGroup.eq_one_iff _).mp h1
    exact comap_pCore_le hLX h2
  have hN : CFSG.pCore 2 ↥Li ≤ φ.ker := by
    intro n hn
    show ψX (f n) = 1
    have h1 : f n = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (pCore_map_le hLX hNX ⟨n, hn, rfl⟩)
    rw [h1, map_one]
  have hpc : CFSG.pCore 2 ↥Li = CFSG.Open.pCore 2 ↥Li := CFSG.pCore_eq_open ↥Li 2
  have hker' : φ.ker ≤ CFSG.Open.pCore 2 ↥Li := by rw [← hpc]; exact hker
  have hN' : CFSG.Open.pCore 2 ↥Li ≤ φ.ker := by rw [← hpc]; exact hN
  let ψ1 : CFSG.Quasithin.oTwoQuot ↥Li →* GL (Fin 4) (ZMod 2) := QuotientGroup.lift _ φ hN'
  have hinj : Function.Injective ψ1 := by
    refine (injective_iff_map_eq_one ψ1).mpr fun a ha => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
    exact (QuotientGroup.eq_one_iff g).mpr (hker' ha)
  have hns' : ¬ Group.IsSolvable (CFSG.Quasithin.oTwoQuot ↥Li) := by
    intro hQ
    apply hns
    have hPp : IsPGroup 2 (CFSG.Open.pCore 2 ↥Li) := by
      rw [← hpc]
      exact CFSG.pCore_isPGroup (p := 2) (G := ↥Li)
    haveI : Group.IsNilpotent ↥(CFSG.Open.pCore 2 ↥Li) := hPp.isNilpotent
    exact Group.isSolvable_of_ker_le_range (CFSG.Open.pCore 2 ↥Li).subtype
      (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥Li))
      (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
  exact CFSG.GH74.QTGen4.U42.VertexGen4B.listed_case_two h.listed hns' ψ1 hinj

end CFSG.GH74.QTGen4.U42.VertexGen4

end
