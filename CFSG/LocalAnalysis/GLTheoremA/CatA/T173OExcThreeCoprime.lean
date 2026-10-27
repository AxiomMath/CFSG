module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OConj
import CFSG.RankThree.PartOne.KE8F.HyperGen
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentLinUnitParabGroup

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.T173 CFSG.LocalAnalysis.GLTheoremA.T173X
open CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent

variable {G₀ : Type} [Group G₀]

theorem map_conj_stdLayer_eq_of_mem_centralizer {d h : G₀}
    (hh : h ∈ Subgroup.centralizer ({d} : Set G₀)) :
    (stdLayer d).map (MulAut.conj h).toMonoidHom = stdLayer d := by
  have hd : (MulAut.conj h) d = d := by
    rw [MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff.mp hh]
    group
  rw [← stdLayer_map_mulEquiv (MulAut.conj h) d, hd]

theorem map_conj_stdLayer_le_innerClosure {A : Subgroup G₀} {d n : G₀}
    (hn : n ∈ Subgroup.normalizer (A : Set G₀)) :
    (stdLayer d).map (MulAut.conj n).toMonoidHom ≤ innerClosure A d :=
  le_iSup₂ (f := fun (a : G₀) (_ : a ∈ Subgroup.normalizer (A : Set G₀)) =>
    (stdLayer d).map (MulAut.conj a).toMonoidHom) n hn

variable [Finite G₀]

theorem inf_centralizer_le_centralizer_of_isStdElt {p : ℕ} {A T : Subgroup G₀} {e : G₀}
    (he : IsStdElt p A e) (hT2 : IsPGroup 2 T)
    (hAL : A ≤ Subgroup.zpowers e ⊔ stdLayer e)
    (hLT : stdLayer e ≤ Subgroup.normalizer (T : Set G₀)) :
    T ⊓ Subgroup.centralizer ({e} : Set G₀) ≤ Subgroup.centralizer (A : Set G₀) := by
  have hS : CFSG.Open.IsQuasisimple ↥(stdLayer e) := he.2.2.2.1.2.2
  have hN : T ⊓ Subgroup.centralizer ({e} : Set G₀) ≤ T := inf_le_left
  have hNsolv : Group.IsSolvable ↥(T ⊓ Subgroup.centralizer ({e} : Set G₀)) := by
    haveI : Group.IsNilpotent ↥(T ⊓ Subgroup.centralizer ({e} : Set G₀)) :=
      IsPGroup.isNilpotent (hT2.to_le hN)
    exact IsNilpotent.to_isSolvable
  have hSN : ∀ s ∈ stdLayer e, ∀ n ∈ T ⊓ Subgroup.centralizer ({e} : Set G₀),
      s * n * s⁻¹ ∈ T ⊓ Subgroup.centralizer ({e} : Set G₀) := by
    intro s hs n hn
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hLT hs) n).mp hn.1, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hse : s * e = e * s :=
      Subgroup.mem_centralizer_singleton_iff.mp (he.2.2.2.1.1 hs)
    have hsie : s⁻¹ * e = e * s⁻¹ :=
      Subgroup.mem_centralizer_singleton_iff.mp
        ((Subgroup.centralizer ({e} : Set G₀)).inv_mem (he.2.2.2.1.1 hs))
    have hne : n * e = e * n := Subgroup.mem_centralizer_singleton_iff.mp hn.2
    calc s * n * s⁻¹ * e = s * n * (s⁻¹ * e) := by group
      _ = s * n * (e * s⁻¹) := by rw [hsie]
      _ = s * (n * e) * s⁻¹ := by group
      _ = s * (e * n) * s⁻¹ := by rw [hne]
      _ = s * e * n * s⁻¹ := by group
      _ = e * s * n * s⁻¹ := by rw [hse]
      _ = e * (s * n * s⁻¹) := by group
  have hNS : ∀ n ∈ T ⊓ Subgroup.centralizer ({e} : Set G₀), ∀ s ∈ stdLayer e,
      n * s * n⁻¹ ∈ stdLayer e := by
    intro n hn s hs
    have hmap := map_conj_stdLayer_eq_of_mem_centralizer (d := e) hn.2
    have hmem : (MulAut.conj n) s ∈ (stdLayer e).map (MulAut.conj n).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj n).toMonoidHom hs
    rw [hmap] at hmem
    simpa [MulAut.conj_apply] using hmem
  have hcomm :=
    LinUnitParab.commute_of_solvable_of_isQuasisimple
      (N := T ⊓ Subgroup.centralizer ({e} : Set G₀)) (S := stdLayer e) hS hNsolv hSN hNS
  intro r hr
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have hAle : A ≤ Subgroup.centralizer ({r} : Set G₀) := by
    refine hAL.trans (sup_le ?_ ?_)
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp hr.2).symm
    · intro s hs
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hcomm r hr s hs).symm
  exact Subgroup.mem_centralizer_singleton_iff.mp (hAle ha)

theorem inf_centralizer_conj_stdElt_eq_bot {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A T : Subgroup G₀} {d n : G₀} (hAp : IsPGroup p A) (hd : IsStdElt p A d)
    (hCA : Subgroup.centralizer (A : Set G₀) ≤ A)
    (hAL : A ≤ Subgroup.zpowers d ⊔ stdLayer d) (hT2 : IsPGroup 2 T)
    (hTN : innerClosure A d ⊔ A ≤ Subgroup.normalizer (T : Set G₀))
    (hn : n ∈ Subgroup.normalizer (A : Set G₀)) :
    T ⊓ Subgroup.centralizer ({n * d * n⁻¹} : Set G₀) = ⊥ := by
  set e : G₀ := n * d * n⁻¹ with he
  have hAn : A.map (MulAut.conj n).toMonoidHom = A :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hn
  have hee : (MulAut.conj n) d = e := by
    rw [MulAut.conj_apply, he]
  have hed : IsStdElt p A e := by
    have h := isStdElt_map (MulAut.conj n) hd
    rwa [hAn, hee] at h
  have hLe : stdLayer e = (stdLayer d).map (MulAut.conj n).toMonoidHom := by
    rw [← hee, stdLayer_map_mulEquiv]
  have hAL' : A ≤ Subgroup.zpowers e ⊔ stdLayer e := by
    have h := Subgroup.map_mono (f := (MulAut.conj n).toMonoidHom) hAL
    rw [hAn, Subgroup.map_sup, MonoidHom.map_zpowers] at h
    simpa only [MulEquiv.coe_toMonoidHom, hee, ← hLe] using h
  have hLT : stdLayer e ≤ Subgroup.normalizer (T : Set G₀) := by
    rw [hLe]
    exact (map_conj_stdLayer_le_innerClosure (A := A) (d := d) hn).trans
      (le_sup_left.trans hTN)
  have hker := inf_centralizer_le_centralizer_of_isStdElt hed hT2 hAL' hLT
  have hdisj : Disjoint T A := IsPGroup.disjoint_of_coprime hT2 hAp
    ((Nat.coprime_primes Nat.prime_two hp).mpr hp2.symm)
  refine eq_bot_iff.mpr ((le_inf inf_le_left (hker.trans hCA)).trans hdisj.le_bot)

theorem stdVanishes_of_hyperplanes {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A : Subgroup G₀} {d : G₀} (hAel : IsElemAbelian p A) (hd : IsStdElt p A d)
    (hCA : Subgroup.centralizer (A : Set G₀) ≤ A)
    (hAL : A ≤ Subgroup.zpowers d ⊔ stdLayer d)
    (hhyp : ∀ D : Subgroup ↥A, D.index = p →
      ∃ n ∈ Subgroup.normalizer (A : Set G₀), n * d * n⁻¹ ∈ D.map A.subtype) :
    StdVanishes A d := by
  rintro ⟨T, hT, hT2, hTN⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CFSG.IsElementaryAbelian p ↥A := hAel.isElementaryAbelian
  haveI : Nontrivial ↥A :=
    ⟨⟨⟨d, hd.1⟩, 1, fun h => hd.2.1 (congrArg Subtype.val h)⟩⟩
  have hAp : IsPGroup p A := hAel.isPGroup
  have hTp : ¬ p ∣ Nat.card T := by
    intro hdvd
    obtain ⟨k, hk⟩ := IsPGroup.exists_card_eq (p := 2) (G := T) hT2
    rw [hk] at hdvd
    exact hp2 (Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_two hdvd)
  have hAN : A ≤ Subgroup.normalizer (T : Set G₀) := le_sup_right.trans hTN
  have hgen := CFSG.RankThree.PartOne.KE8F.le_iSup_hyperplane_centralizers (p := p)
    (A := A) (V := T) hAN hTp
  refine hT (eq_bot_iff.2 (hgen.trans (iSup₂_le fun D hD => ?_)))
  obtain ⟨n, hn, hnD⟩ := hhyp D hD
  exact (inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hnD))).trans
    (le_of_eq (inf_centralizer_conj_stdElt_eq_bot hp hp2 hAp hd hCA hAL hT2 hTN hn))

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
