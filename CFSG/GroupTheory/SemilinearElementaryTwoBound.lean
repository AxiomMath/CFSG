module

public import CFSG.LieType.ChevTwo.OppCl.Defs
import CFSG.RankThree.GF2n.Smith81.TiSylow
import CFSG.RankThree.GF2n.Stroth80.HeringSec9Lin
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LnAut

public section

namespace CFSG.GroupTheory

open CFSG.RankThree.GF2n.Smith81 CFSG.RankThree.GF2n.Stroth80.HS9
  CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln

theorem card_le_two_mul_card_of_isElemAbelian_semilinear_two
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (D : Subgroup (Equiv.Perm (Fin 2 → F)))
    (hD : CFSG.Open.IsElemAbelian 2 D)
    (hsem : D ≤ CFSG.LieType.ChevTwo.OppCl.semilinGroup F (Fin 2 → F)) :
    Nat.card D ≤ 2 * Nat.card F := by
  classical
  let V := Fin 2 → F
  have hsem' : D ≤ semilinearPerm F V := by
    intro d hd
    simpa [V, CFSG.LieType.ChevTwo.OppCl.semilinGroup, semilinearPerm] using hsem hd
  let incl : D →* semilinearPerm F V := Subgroup.inclusion hsem'
  let π : D →* (F ≃+* F) := semilinearHom.comp incl
  have hD2 : ∀ d : D, d * d = 1 := by
    intro d
    apply Subtype.ext
    have h : (d : Equiv.Perm V) ^ 2 = 1 := hD.2 d.1 d.2
    simpa [pow_two] using h
  have hπ2 : ∀ d : D, π d * π d = 1 := by
    intro d
    rw [← map_mul, hD2 d, map_one]
  have hcyclicAut : IsCyclic (F ≃+* F) := isCyclic_ringAut F
  have hcyclicRange : IsCyclic ↥π.range := Subgroup.isCyclic _
  have hfinAut : Finite (F ≃+* F) :=
    Finite.of_injective (fun e : F ≃+* F => (e : F → F))
      (by intro a b h; ext x; exact congrFun h x)
  have hfinRange : Finite ↥π.range :=
    Finite.of_injective (Subgroup.subtype π.range) Subtype.val_injective
  have hfintypeRange : Fintype ↥π.range := Fintype.ofFinite _
  have hrangeCard : Nat.card ↥π.range ≤ 2 := by
    have h := IsCyclic.card_pow_eq_one_le (α := ↥π.range) (n := 2) (by norm_num)
    have htop : Finset.univ.filter (fun x : ↥π.range => x ^ 2 = 1) = Finset.univ := by
      apply Finset.filter_true_of_mem
      intro x _
      obtain ⟨d, hd⟩ := MonoidHom.mem_range.mp x.2
      apply Subtype.ext
      show (x : F ≃+* F) ^ 2 = 1
      rw [← hd]
      exact hπ2 d
    have h' : (Finset.univ : Finset ↥π.range).card ≤ 2 := by simpa [htop] using h
    have h'' : Fintype.card ↥π.range ≤ 2 := by simpa using h'
    have hnat : Nat.card ↥π.range = Fintype.card ↥π.range := Nat.card_eq_fintype_card
    rw [hnat]
    exact h''
  let B : Subgroup (semilinearPerm F V) := π.ker.map incl
  have hB : B ≤ linearToSemilinear.range := by
    rintro b ⟨d, hd, rfl⟩
    have hd' : semilinearHom (incl d) = 1 := by
      simpa [π, MonoidHom.comp_apply] using (MonoidHom.mem_ker.mp hd)
    rw [← ker_semilinearHom]
    simpa [MonoidHom.mem_ker] using hd'
  let S : Subgroup (V ≃ₗ[F] V) := B.comap linearToSemilinear
  have hSmap : S.map linearToSemilinear = B := by
    rw [Subgroup.map_comap_eq, inf_eq_right.mpr hB]
  have hcardS : Nat.card S = Nat.card π.ker := by
    calc Nat.card S = Nat.card (S.map linearToSemilinear) :=
          (Subgroup.card_map_of_injective (K := S) (f := linearToSemilinear)
            linearToSemilinear_injective).symm
      _ = Nat.card B := by rw [hSmap]
      _ = Nat.card π.ker := Subgroup.card_map_of_injective (K := π.ker) (f := incl)
          (Subgroup.inclusion_injective hsem')
  have hS2 : ∀ s ∈ S, s * s = 1 := by
    intro s hs
    have hfs : linearToSemilinear s ∈ B := by
      rw [← hSmap]
      exact Subgroup.mem_map_of_mem _ hs
    obtain ⟨d, -, hde⟩ := Subgroup.mem_map.mp hfs
    apply linearToSemilinear_injective
    calc linearToSemilinear (s * s) = linearToSemilinear s * linearToSemilinear s :=
          map_mul _ _ _
      _ = incl d * incl d := by rw [hde]
      _ = incl (d * d) := (map_mul incl d d).symm
      _ = 1 := by rw [hD2 d, map_one]
  have hS : IsPGroup 2 S := by
    intro s
    refine ⟨1, ?_⟩
    apply Subtype.ext
    show (s : V ≃ₗ[F] V) ^ (2 ^ 1) = 1
    simpa [pow_two] using hS2 s s.2
  have hV : Nat.card V = Nat.card F ^ 2 := by
    dsimp only [V]
    rw [Nat.card_fun, Nat.card_fin]
  have hSle : Nat.card S ≤ Nat.card F := two_subgroup_gl_two_le hV S hS
  calc Nat.card D = Nat.card π.ker * Nat.card π.range :=
        (Subgroup.card_ker_mul_card_range π).symm
    _ = Nat.card S * Nat.card π.range := by rw [hcardS]
    _ ≤ Nat.card F * 2 := Nat.mul_le_mul hSle hrangeCard
    _ = 2 * Nat.card F := Nat.mul_comm _ _

end CFSG.GroupTheory
