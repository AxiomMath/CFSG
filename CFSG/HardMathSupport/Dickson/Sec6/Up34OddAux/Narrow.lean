module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Layer
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Odd
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Defs
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1412Levels

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.HardMathSupport.Solomon.LocalBalance

@[expose] def NoL34Inn (r : ℕ) : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = r →
    ∀ [Finite (TauCeti.CFSGIndex.lie d).Group],
    ∀ u : (TauCeti.CFSGIndex.lie d).Group, orderOf u = 3 → NoL34Layer (MulAut.conj u)

@[expose] def NoL34Out (r : ℕ) : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = r →
    ∀ [Finite (TauCeti.CFSGIndex.lie d).Group],
    ∀ α : MulAut (TauCeti.CFSGIndex.lie d).Group, orderOf α = 3 →
      α ∉ (MulAut.conj : (TauCeti.CFSGIndex.lie d).Group →* _).range → NoL34Layer α

theorem noL34Inn_three_of_kdCharP (h : KDCharP 3) : NoL34Inn 3 := by
  intro d hd _ u hu A hA _
  exfalso
  rw [fixSubgroup_conj_eq_centralizer] at hA
  have hle : A ≤ GLAPLayer 3
      (Subgroup.centralizer ({u} : Set (TauCeti.CFSGIndex.lie d).Group)) := le_sSup hA
  rw [h d hd u hu, le_bot_iff] at hle
  exact glaPComponent_ne_bot' hA hle

theorem up34OddLeaf_of_noL34 (hInn : ∀ r : ℕ, r.Prime → r ≠ 2 → NoL34Inn r)
    (hOut : ∀ r : ℕ, r.Prime → r ≠ 2 → NoL34Out r) : Up34OddLeaf := by
  intro S _ _ hS hnab d hd ⟨e⟩ α hpump
  obtain ⟨hα3, hα1, I, hI, hI34⟩ := hpump
  haveI := hS
  have hfin : Finite (TauCeti.CFSGIndex.lie d).Group := Finite.of_equiv S e.toEquiv
  haveI : IsSimpleGroup (TauCeti.CFSGIndex.lie d).Group := e.symm.isSimpleGroup
  have hnabG : ∃ a b : (TauCeti.CFSGIndex.lie d).Group, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨e a, e b, fun h' => hab (e.injective (by rw [map_mul, map_mul]; exact h'))⟩
  have hZ : Subgroup.center (TauCeti.CFSGIndex.lie d).Group = ⊥ :=
    up34_center_eq_bot_of_simple hnabG
  let ψ : MulAut (TauCeti.CFSGIndex.lie d).Group := MulAut.congr e α
  have hψ3 : ψ ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
  have hψ1 : ψ ≠ 1 := by
    intro h1
    exact hα1 ((MulAut.congr e).injective (h1.trans (map_one _).symm))
  have hker : (e : S →* (TauCeti.CFSGIndex.lie d).Group).ker ≤ Subgroup.center S := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 e.injective]
    exact bot_le
  obtain ⟨A, hA, hAT⟩ := isLThreeFour_barOf_of_central
    (e : S →* (TauCeti.CFSGIndex.lie d).Group) e.surjective hker α ψ
    (fun y => by simp [ψ, MulAut.congr_apply]) hI hI34
  have hchar : d.1.characteristic ≠ 2 := characteristic_ne_two_of_not_isCharTwoLieIndex hd
  have hprime : d.1.characteristic.Prime := d.characteristic_prime
  have hord : orderOf ψ = 3 := orderOf_eq_prime hψ3 hψ1
  have hno : NoL34Layer ψ := by
    by_cases hin : ψ ∈ (MulAut.conj : (TauCeti.CFSGIndex.lie d).Group →* _).range
    · obtain ⟨u, hu⟩ := hin
      have hu1 : u ≠ 1 := by
        rintro rfl
        exact hψ1 (hu.symm.trans (map_one _))
      have hu3 : u ^ 3 = 1 := by
        have h1 : MulAut.conj (u ^ 3) = 1 := by rw [map_pow, hu]; exact hψ3
        have hcen : u ^ 3 ∈ Subgroup.center (TauCeti.CFSGIndex.lie d).Group := by
          rw [Subgroup.mem_center_iff]
          intro g
          have hg := DFunLike.congr_fun h1 g
          rw [MulAut.conj_apply, MulAut.one_apply] at hg
          exact (mul_inv_eq_iff_eq_mul.1 hg).symm
        rw [hZ, Subgroup.mem_bot] at hcen
        exact hcen
      have hord' : orderOf u = 3 := orderOf_eq_prime hu3 hu1
      have := hInn _ hprime hchar d rfl u hord'
      rwa [hu] at this
    · exact hOut _ hprime hchar d rfl ψ hord hin
  exact hno A hA hAT

end CFSG.HardMathSupport.Dickson.Sec6
