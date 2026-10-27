module

public import CFSG.Open.LocalVocabulary
import CFSG.RankThree.PartOne.K133.KillL2
import CFSG.Dihedral.GorensteinWalter.PGL2SquareRange
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LinearAlgebra

open CFSG CFSG.Open CFSG.GorensteinWalter Matrix

private theorem psl2_elemAb_card_le_univ {K : Type*} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) [NeZero (p : K)]
    (A : Subgroup (PSL2 K)) (hA : IsElementaryAbelian p A) : Nat.card A ≤ p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let π : SpecialLinearGroup (Fin 2) K →* PSL2 K :=
    QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) K))
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : ¬ p ∣ Nat.card π.ker := by
    intro hdvd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have hxc : (x : SpecialLinearGroup (Fin 2) K) ∈
        Subgroup.center (SpecialLinearGroup (Fin 2) K) := by
      have : (x : SpecialLinearGroup (Fin 2) K) ∈ π.ker := x.2
      simpa [π] using this
    obtain ⟨r, hr, hrx⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hxc
    have hx2 : (x : SpecialLinearGroup (Fin 2) K) ^ 2 = 1 := by
      ext1
      rw [Matrix.SpecialLinearGroup.coe_pow, ← hrx, ← map_pow, Matrix.SpecialLinearGroup.coe_one]
      rw [Fintype.card_fin] at hr
      rw [hr, map_one]
    have hxo : orderOf (x : SpecialLinearGroup (Fin 2) K) = p := by
      rw [Subgroup.orderOf_coe, hx]
    have : p ∣ 2 := hxo ▸ orderOf_dvd_of_pow_eq_one hx2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
  obtain ⟨E', hE'map, hE'dis⟩ := CFSG.RankThree.PartOne.CTP.SeitzToral.exists_lift_of_coprime_ker
    π hπ hker A (IsElementaryAbelian.isPGroup p A)
  have hE'mem : ∀ x ∈ E', π x ∈ A := fun x hx => hE'map ▸ ⟨x, hx, rfl⟩
  have hE'comm : ∀ a ∈ E', ∀ b ∈ E', a * b = b * a := by
    intro a ha b hb
    have hc : a * b * a⁻¹ * b⁻¹ ∈ E' :=
      E'.mul_mem (E'.mul_mem (E'.mul_mem ha hb) (E'.inv_mem ha)) (E'.inv_mem hb)
    have hk : a * b * a⁻¹ * b⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      have hcm : π a * π b = π b * π a :=
        congrArg Subtype.val (hA.is_comm.comm ⟨π a, hE'mem a ha⟩ ⟨π b, hE'mem b hb⟩)
      rw [hcm]
      group
    have := Subgroup.disjoint_def.mp hE'dis hc hk
    exact commutatorElement_eq_one_iff_mul_comm.mp this
  have hE'exp : ∀ a ∈ E', a ^ p = 1 := by
    intro a ha
    have hk : a ^ p ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact elemPow_eq_one_of_isElementaryAbelian (π a) (hE'mem a ha)
    exact Subgroup.disjoint_def.mp hE'dis (E'.pow_mem ha p) hk
  have hcyc : IsCyclic E' :=
    CFSG.RankThree.PartOne.K133.isCyclic_of_commuting_pow_eq_one_sl2 hp E' hE'comm hE'exp
  have hE'le : Nat.card E' ≤ p := by
    have hexp : Monoid.exponent ↥E' ∣ p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x =>
      Subtype.ext (by simpa using hE'exp x x.2)
    rw [IsCyclic.exponent_eq_card] at hexp
    exact Nat.le_of_dvd hp.pos hexp
  have hsurj : Function.Surjective (fun x : E' => (⟨π x, hE'mem x x.2⟩ : A)) := by
    intro a
    have : (a : PSL2 K) ∈ E'.map π := hE'map ▸ a.2
    obtain ⟨x, hx, hxa⟩ := this
    exact ⟨⟨x, hx⟩, Subtype.ext hxa⟩
  exact (Nat.card_le_card_of_surjective _ hsurj).trans hE'le

private theorem card_le_of_isElemAbelian_pgl_two {F : Type*} [Field F] [Finite F] {p : ℕ}
    [Fact p.Prime] (hp : p ≠ 2) (hpF : (p : F) ≠ 0)
    (Q : Subgroup (Matrix.ProjGenLinGroup (Fin 2) F)) (hQ : IsElemAbelian p Q) :
    Nat.card Q ≤ p := by
  classical
  haveI : NeZero (p : F) := ⟨hpF⟩
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  have hQH : Q ≤ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
    intro x hx
    exact CFSG.GorensteinWalter.pgl2_mem_psl2Range_of_pow_odd hpodd (hQ.2 x hx)
  set Q' : Subgroup (PSL2 F) :=
    Q.comap (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)) with hQ'def
  have hQ'elem : IsElemAbelian p Q' :=
    IsElemAbelian.comap hQ
      (Matrix.ProjectiveSpecialLinearGroup.toPGL_injective (n := Fin 2) (R := F))
  have hbound : Nat.card Q' ≤ p :=
    psl2_elemAb_card_le_univ (Fact.out : p.Prime) hp Q' hQ'elem.isElementaryAbelian
  have hcard : Nat.card Q' = Nat.card Q := by
    have hmap : Q'.map (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)) = Q :=
      Subgroup.map_comap_eq_self hQH
    have h1 : Nat.card (Q'.map (Matrix.ProjectiveSpecialLinearGroup.toPGL
        (n := Fin 2) (R := F))) = Nat.card Q' :=
      Subgroup.card_map_of_injective
        (Matrix.ProjectiveSpecialLinearGroup.toPGL_injective (n := Fin 2) (R := F))
    rw [hmap] at h1
    exact h1.symm
  calc Nat.card Q = Nat.card Q' := hcard.symm
    _ ≤ p := hbound

theorem not_pSq_pgl_two {F : Type*} [Field F] [Fintype F] {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hpF : (p : F) ≠ 0) (B : Subgroup (GL (Fin 2) F))
    (hZ : Subgroup.center (GL (Fin 2) F) ≤ B)
    (hB : IsElemAbelian p (⊤ : Subgroup (B ⧸ (Subgroup.center (GL (Fin 2) F)).subgroupOf B))) :
    Nat.card (B ⧸ (Subgroup.center (GL (Fin 2) F)).subgroupOf B) ≤ p := by
  classical
  haveI : NeZero (p : F) := ⟨hpF⟩
  let f : B →* (GL (Fin 2) F ⧸ Subgroup.center (GL (Fin 2) F)) :=
    (QuotientGroup.mk' (Subgroup.center (GL (Fin 2) F))).comp B.subtype
  have hker : f.ker = (Subgroup.center (GL (Fin 2) F)).subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show QuotientGroup.mk' (Subgroup.center (GL (Fin 2) F)) (b : GL (Fin 2) F) = 1 ↔
      (b : GL (Fin 2) F) ∈ Subgroup.center (GL (Fin 2) F)
    exact QuotientGroup.eq_one_iff _
  let Φ : B ⧸ (Subgroup.center (GL (Fin 2) F)).subgroupOf B →*
      (GL (Fin 2) F ⧸ Subgroup.center (GL (Fin 2) F)) :=
    QuotientGroup.lift ((Subgroup.center (GL (Fin 2) F)).subgroupOf B) f hker.ge
  have hΦinj : Function.Injective Φ :=
    (QuotientGroup.injective_lift_iff ((Subgroup.center (GL (Fin 2) F)).subgroupOf B) f
      hker.ge).mpr hker.symm
  let Q : Subgroup (Matrix.ProjGenLinGroup (Fin 2) F) := Φ.range
  have hQ : IsElemAbelian p Q := by
    have h := IsElemAbelian.map hB Φ
    rwa [← MonoidHom.range_eq_map Φ] at h
  have hcardQ :
      Nat.card (B ⧸ (Subgroup.center (GL (Fin 2) F)).subgroupOf B) = Nat.card Q := by
    let e : (B ⧸ (Subgroup.center (GL (Fin 2) F)).subgroupOf B) ≃* Q :=
      MulEquiv.ofBijective Φ.rangeRestrict
        ⟨fun a b hab => hΦinj (congrArg Subtype.val hab), Φ.rangeRestrict_surjective⟩
    exact Nat.card_congr e.toEquiv
  rw [hcardQ]
  exact card_le_of_isElemAbelian_pgl_two hp hpF Q hQ

end CFSG.LinearAlgebra
