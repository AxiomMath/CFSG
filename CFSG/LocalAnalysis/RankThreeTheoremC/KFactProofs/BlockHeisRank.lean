module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisCoreDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisHomC

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

theorem exists_lift_elemAbelian {L : Type*} [Group L] [Finite L] {q : ℕ} (hq : q.Prime)
    (hZ : ¬ q ∣ Nat.card (Subgroup.center L)) (A : Subgroup (L ⧸ Subgroup.center L))
    (hA : IsMulCommutative A) (hAq : ∀ x ∈ A, x ^ q = 1) :
    ∃ T : Subgroup L, IsMulCommutative T ∧ (∀ x ∈ T, x ^ q = 1) ∧ Nat.card T = Nat.card A := by
  haveI : Fact q.Prime := ⟨hq⟩
  let π : L →* L ⧸ Subgroup.center L := QuotientGroup.mk' (Subgroup.center L)
  let Ã : Subgroup L := A.comap π
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  let ψ : Ã →* A := (π.comp Ã.subtype).codRestrict A (fun x => x.2)
  have hψs : Function.Surjective ψ := by
    rintro ⟨a, ha⟩
    obtain ⟨l, rfl⟩ := hπs a
    exact ⟨⟨l, ha⟩, rfl⟩
  have hker : ¬ q ∣ Nat.card ψ.ker := by
    intro hdvd
    apply hZ
    refine hdvd.trans ?_
    let ι : ψ.ker →* Subgroup.center L :=
      { toFun := fun x => ⟨((x : Ã) : L), by
          have h1 : π ((x : Ã) : L) = 1 :=
            congrArg (fun a : A => (a : L ⧸ Subgroup.center L)) (MonoidHom.mem_ker.1 x.2)
          exact (QuotientGroup.eq_one_iff _).1 h1⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hι : Function.Injective ι := by
      intro x y hxy
      have h : ((x : Ã) : L) = ((y : Ã) : L) :=
        congrArg (fun z : Subgroup.center L => (z : L)) hxy
      exact Subtype.ext (Subtype.ext h)
    exact Subgroup.card_dvd_of_injective ι hι
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨T'⟩ := (inferInstance : Nonempty (Sylow q Ã))
  have hcardÃ : Nat.card Ã = Nat.card ψ.ker * Nat.card A := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψs).toEquiv] at h1
    rw [h1, mul_comm]
  have hfact : (Nat.card Ã).factorization q = (Nat.card A).factorization q := by
    rw [hcardÃ, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hker, zero_add]
  have hApg : IsPGroup q A := fun x => ⟨1, Subtype.ext (by simpa using hAq x x.2)⟩
  obtain ⟨n, hn⟩ := hApg.exists_card_eq
  have hAfact : (Nat.card A).factorization q = n := by
    rw [hn, Nat.Prime.factorization_pow hq]
    simp
  have hinj : Function.Injective (ψ.comp (T' : Subgroup Ã).subtype) :=
    injective_comp_subtype_of_isPGroup ψ hker T'.isPGroup'
  have hT'card : Nat.card (T' : Subgroup Ã) = Nat.card A := by
    rw [T'.card_eq_multiplicity, hfact, hAfact, hn]
  haveI := hA
  have hcomm : ∀ x y : (T' : Subgroup Ã), x * y = y * x := fun x y => by
    apply hinj
    rw [map_mul, map_mul]
    exact mul_comm' _ _
  have hexp : ∀ x : (T' : Subgroup Ã), x ^ q = 1 := fun x => by
    apply hinj
    rw [map_pow, map_one]
    apply Subtype.ext
    exact hAq _ (ψ.comp (T' : Subgroup Ã).subtype x).2
  refine ⟨(T' : Subgroup Ã).map Ã.subtype, ⟨⟨fun x y => ?_⟩⟩, ?_, ?_⟩
  · obtain ⟨x', hx', hxx'⟩ := Subgroup.mem_map.1 x.2
    obtain ⟨y', hy', hyy'⟩ := Subgroup.mem_map.1 y.2
    apply Subtype.ext
    change (x : L) * (y : L) = (y : L) * (x : L)
    rw [← hxx', ← hyy']
    exact congrArg (fun z : (T' : Subgroup Ã) => ((z : Ã) : L)) (hcomm ⟨x', hx'⟩ ⟨y', hy'⟩)
  · intro x hx
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.1 hx
    have := congrArg (fun z : (T' : Subgroup Ã) => ((z : Ã) : L)) (hexp ⟨x', hx'⟩)
    exact this
  · rw [Subgroup.card_map_of_injective Ã.subtype_injective, hT'card]

theorem heis_rank_quotient {L : Type*} [Group L] [Finite L] (hrk : OddRankLeThree L) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hZ : ¬ q ∣ Nat.card (Subgroup.center L))
    (A : Subgroup (L ⧸ Subgroup.center L)) (hA : IsMulCommutative A)
    (hAq : ∀ x ∈ A, x ^ q = 1) : Nat.card A ≤ q ^ 3 := by
  obtain ⟨T, hT, hTq, hTc⟩ := exists_lift_elemAbelian hq hZ A hA hAq
  rw [← hTc]
  exact hrk q hq hq2 T hT hTq

theorem heis_conj_injective (L : Type*) [Group L] [hL : Group.IsPerfect L]
    [IsSimpleGroup (L ⧸ Subgroup.center L)] :
    Function.Injective
      (MulAut.conj : (L ⧸ Subgroup.center L) →* MulAut (L ⧸ Subgroup.center L)) := by
  obtain ⟨a, b, hab⟩ := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian
    L ⟨hL.commutator_eq_top, inferInstance⟩
  rw [injective_iff_map_eq_one]
  intro x hx
  have hc : x ∈ Subgroup.center (L ⧸ Subgroup.center L) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h := congrArg (fun f : MulAut (L ⧸ Subgroup.center L) => f g) hx
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  have hbot : Subgroup.center (L ⧸ Subgroup.center L) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center (L ⧸ Subgroup.center L)) with h | h
    · exact h
    · exfalso
      apply hab
      have hb : b ∈ Subgroup.center (L ⧸ Subgroup.center L) := by rw [h]; trivial
      exact Subgroup.mem_center_iff.1 hb a
  rw [hbot] at hc
  exact Subgroup.mem_bot.1 hc

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
