module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I269SBlk
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
public import CFSG.Sporadic.Co2Smith.SmithCo2
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieSp6
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.LevelLieSp6
open CFSG.RankThree.Classical
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

theorem i269s_conj_eq_one_iff {G : Type} [Group G] (hZ : Subgroup.center G = ⊥) {g : G} :
    MulAut.conj g = 1 ↔ g = 1 := by
  constructor
  · intro h
    have hc := LevelLieSp6.mem_center_of_conj_eq_one h
    rw [hZ, Subgroup.mem_bot] at hc
    exact hc
  · rintro rfl
    ext z
    simp

theorem i269s_conj_injective {G : Type} [Group G] (hZ : Subgroup.center G = ⊥) {x y : G}
    (h : MulAut.conj x = MulAut.conj y) : x = y := by
  have h1 : MulAut.conj (x⁻¹ * y) = 1 := by
    rw [map_mul, map_inv, h, inv_mul_cancel]
  exact inv_mul_eq_one.1 ((i269s_conj_eq_one_iff hZ).1 h1)

theorem i269s_E9_of_pairs {T : Type} [Group T] [Finite T]
    (hinner : ∀ α : MulAut T, ∃ t : T, α = MulAut.conj t) (hZ : Subgroup.center T = ⊥)
    (hpair : ∀ x y : T, x ^ 3 = 1 → x ≠ 1 → y ^ 3 = 1 → Commute x y → y ∉ Subgroup.zpowers x →
      Group.IsSolvable ↥(Subgroup.centralizer ({x} : Set T) ⊓ Subgroup.centralizer ({y} : Set T))) :
    E9Solv T := by
  intro E hE hcard
  classical
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : Nontrivial E := Finite.one_lt_card_iff_nontrivial.1 (by rw [hcard]; norm_num)
  obtain ⟨α₁, hα₁1⟩ := exists_ne (1 : E)
  have hα3 : (α₁.1 : MulAut T) ^ 3 = 1 := hE.2 α₁.1 α₁.2
  have hα1 : (α₁.1 : MulAut T) ≠ 1 := fun h => hα₁1 (Subtype.ext h)
  obtain ⟨α₂, hα₂E, hα₂⟩ : ∃ α₂ ∈ E, α₂ ∉ Subgroup.zpowers (α₁.1 : MulAut T) := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have hle : E ≤ Subgroup.zpowers (α₁.1 : MulAut T) := fun α hα => hcon α hα
    have h1 : Nat.card E ≤ Nat.card (Subgroup.zpowers (α₁.1 : MulAut T)) :=
      Subgroup.card_le_of_le hle
    have h2 : orderOf (α₁.1 : MulAut T) ∣ 3 := orderOf_dvd_of_pow_eq_one hα3
    have h3 : Nat.card (Subgroup.zpowers (α₁.1 : MulAut T)) ≤ 3 := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) h2
    omega
  obtain ⟨t₁, ht₁⟩ := hinner α₁.1
  obtain ⟨t₂, ht₂⟩ := hinner α₂
  have ht₁1 : t₁ ≠ 1 := by
    rintro rfl
    apply hα1
    rw [ht₁, map_one]
  have ht₁3 : t₁ ^ 3 = 1 := (i269s_conj_eq_one_iff hZ).1 (by
    rw [map_pow, ← ht₁, hα3])
  have ht₂3 : t₂ ^ 3 = 1 := (i269s_conj_eq_one_iff hZ).1 (by
    rw [map_pow, ← ht₂]
    exact hE.2 α₂ hα₂E)
  have hcomm : Commute t₁ t₂ := by
    have hc : α₁.1 * α₂ = α₂ * α₁.1 := congrArg Subtype.val
      (hE.1.is_comm.comm ⟨α₁.1, α₁.2⟩ ⟨α₂, hα₂E⟩)
    apply i269s_conj_injective hZ
    rw [map_mul, map_mul, ← ht₁, ← ht₂, hc]
  have hzp : t₂ ∉ Subgroup.zpowers t₁ := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    apply hα₂
    rw [ht₂, ← hk, map_zpow, ← ht₁]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k
  haveI := hpair t₁ t₂ ht₁3 ht₁1 ht₂3 hcomm hzp
  have hsub : i269Fix E ≤ Subgroup.centralizer ({t₁} : Set T) ⊓
      Subgroup.centralizer ({t₂} : Set T) := by
    intro g hg
    rw [mem_i269Fix] at hg
    have h1 : t₁ * g * t₁⁻¹ = g := by
      have := hg α₁.1 α₁.2
      rw [ht₁, MulAut.conj_apply] at this
      exact this
    have h2 : t₂ * g * t₂⁻¹ = g := by
      have := hg α₂ hα₂E
      rw [ht₂, MulAut.conj_apply] at this
      exact this
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 fun h hh => ?_,
      Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
    · rw [Set.mem_singleton_iff.1 hh]
      exact mul_inv_eq_iff_eq_mul.1 h1
    · rw [Set.mem_singleton_iff.1 hh]
      exact mul_inv_eq_iff_eq_mul.1 h2
  exact isSolvable_of_le_isSolvable hsub

theorem i269s_isSolvable_map {G T : Type} [Group G] [Group T] (e : G ≃* T) (C : Subgroup G)
    (h : Group.IsSolvable ↥C) : Group.IsSolvable ↥(C.map e.toMonoidHom) := by
  haveI := h
  exact isSolvable_of_mulEquiv' (Subgroup.equivMapOfInjective C e.toMonoidHom e.injective).symm

theorem i269s_centralizer_map {G T : Type} [Group G] [Group T] (e : G ≃* T) (x y : G) :
    Subgroup.centralizer ({e x} : Set T) ⊓ Subgroup.centralizer ({e y} : Set T) =
      (Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G)).map
        e.toMonoidHom := by
  ext z
  constructor
  · intro hz
    obtain ⟨hzx, hzy⟩ := Subgroup.mem_inf.1 hz
    have h1 := Subgroup.mem_centralizer_iff.1 hzx (e x) (Set.mem_singleton _)
    have h2 := Subgroup.mem_centralizer_iff.1 hzy (e y) (Set.mem_singleton _)
    refine ⟨e.symm z, Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 fun h hh => ?_,
      Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩, e.apply_symm_apply z⟩
    · rw [Set.mem_singleton_iff.1 hh]
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply]
      exact h1
    · rw [Set.mem_singleton_iff.1 hh]
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply]
      exact h2
  · intro hz
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hz
    obtain ⟨hgx, hgy⟩ := Subgroup.mem_inf.1 hg
    have h1 := Subgroup.mem_centralizer_iff.1 hgx x (Set.mem_singleton _)
    have h2 := Subgroup.mem_centralizer_iff.1 hgy y (Set.mem_singleton _)
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 fun h hh => ?_,
      Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
    · rw [Set.mem_singleton_iff.1 hh]
      show e x * e g = e g * e x
      rw [← map_mul, ← map_mul, h1]
    · rw [Set.mem_singleton_iff.1 hh]
      show e y * e g = e g * e y
      rw [← map_mul, ← map_mul, h2]

theorem i269s_proj_bij (hK2 : Nat.card (ZMod 2) = 2) :
    Function.Bijective (proj 3 (ZMod 2)) :=
  ⟨proj_injective_of_card_two hK2, QuotientGroup.mk'_surjective _⟩

noncomputable def i269sSpProj : StatedSp 3 (ZMod 2) ≃* StatedProj (StatedSp 3 (ZMod 2)) :=
  MulEquiv.ofBijective (proj 3 (ZMod 2)) (i269s_proj_bij (by rw [Nat.card_eq_fintype_card, ZMod.card]))

theorem i269s_E9_proj_sp62 : E9Solv (StatedProj (StatedSp 3 (ZMod 2))) := by
  have hK2 : Nat.card (ZMod 2) = 2 := by rw [Nat.card_eq_fintype_card, ZMod.card]
  haveI := CFSG.Sporadic.Co2Smith.isSimpleGroup_sp62
  haveI : IsSimpleGroup (StatedProj (StatedSp 3 (ZMod 2))) := i269sSpProj.symm.isSimpleGroup
  haveI : Finite (StatedProj (StatedSp 3 (ZMod 2))) := Finite.of_equiv _ i269sSpProj.toEquiv
  have hcard : Nat.card (StatedProj (StatedSp 3 (ZMod 2))) = 1451520 := by
    rw [← Nat.card_congr i269sSpProj.toEquiv, CFSG.Sporadic.Co2Smith.natCard_sp62]
  have hnc : ∃ a b : StatedProj (StatedSp 3 (ZMod 2)), a * b ≠ b * a :=
    exists_noncomm_of_simple_not_prime (by rw [hcard]; norm_num)
  refine i269s_E9_of_pairs (inner_of_card_two hK2) (center_eq_bot_of_simple hnc) ?_
  intro xb yb hxb3 hxb1 hyb3 hxyb hyxb
  have hsurj : Function.Surjective (proj 3 (ZMod 2)) := QuotientGroup.mk'_surjective _
  obtain ⟨x, rfl⟩ := hsurj xb
  obtain ⟨y, rfl⟩ := hsurj yb
  have hinj := proj_injective_of_card_two hK2
  have hx3 : x ^ 3 = 1 := hinj (by rw [map_pow, hxb3, map_one])
  have hx1 : x ≠ 1 := fun h => hxb1 (by rw [h, map_one])
  have hy3 : y ^ 3 = 1 := hinj (by rw [map_pow, hyb3, map_one])
  have hxy : Commute x y := hinj (by rw [map_mul, map_mul]; exact hxyb)
  have hyx : y ∉ Subgroup.zpowers x := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    apply hyxb
    rw [← hk, map_zpow]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k
  have hsol := i269s_isSolvable_map i269sSpProj _ (i269s_pair_solvable hK2 hx3 hx1 hy3 hxy hyx)
  have heq : Subgroup.centralizer ({proj 3 (ZMod 2) x} : Set (StatedProj (StatedSp 3 (ZMod 2)))) ⊓
      Subgroup.centralizer ({proj 3 (ZMod 2) y} : Set (StatedProj (StatedSp 3 (ZMod 2)))) =
      (Subgroup.centralizer ({x} : Set (StatedSp 3 (ZMod 2))) ⊓
        Subgroup.centralizer ({y} : Set (StatedSp 3 (ZMod 2)))).map i269sSpProj.toMonoidHom :=
    i269s_centralizer_map i269sSpProj x y
  rw [heq]
  exact hsol

theorem e9Solv_sp6two (S : Type) [Group S] (h : catalogIs S S9.isSp6two) : E9Solv S := by
  obtain ⟨e₀⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.bridge_sp6two h
  exact E9Solv.of_mulEquiv (E9Solv.of_mulEquiv i269s_E9_proj_sp62 i269sSpProj) e₀

end CFSG.LocalAnalysis.GLTheoremA

end
