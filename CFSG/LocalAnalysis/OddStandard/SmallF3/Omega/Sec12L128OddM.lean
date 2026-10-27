module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

private abbrev Alt5 := ↥(alternatingGroup (Fin 5))

private abbrev Model := Multiplicative (ZMod 2) × Alt5

private def iota2 : Alt5 →* Model := MonoidHom.inr _ _

private def pi2 : Model →* Alt5 := MonoidHom.snd _ _

private def Sodd : Set Model := {m : Model | Odd (orderOf m)}

private lemma mul_self_zmod2 (x : Multiplicative (ZMod 2)) : x * x = 1 :=
  CharTwo.add_self_eq_zero x.toAdd

private lemma iota2_injective : Function.Injective iota2 := by
  intro a b h
  have := congrArg Prod.snd h
  simpa [iota2] using this

private lemma pi2_surjective : Function.Surjective pi2 := fun a => ⟨(1, a), rfl⟩

private lemma fst_eq_one_of_odd {m : Model} (hm : Odd (orderOf m)) : m.1 = 1 := by
  have h1 : orderOf m.1 ∣ orderOf m := orderOf_map_dvd (MonoidHom.fst _ _) m
  have hodd : Odd (orderOf m.1) := Odd.of_dvd_nat hm h1
  have h2 : orderOf m.1 ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one, pow_two]
    exact mul_self_zmod2 m.1
  have hone : orderOf m.1 = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  exact orderOf_eq_one_iff.mp hone

private lemma card_alt5 : Nat.card Alt5 = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

private lemma exists_orderOf_two : ∃ a : Alt5, orderOf a = 2 :=
  exists_prime_orderOf_dvd_card' 2 (by rw [card_alt5]; norm_num)

private lemma exists_orderOf_three : ∃ a : Alt5, orderOf a = 3 :=
  exists_prime_orderOf_dvd_card' 3 (by rw [card_alt5]; norm_num)

private lemma conj_mem_Sodd (g : Model) {x : Model} (hx : x ∈ Sodd) :
    g * x * g⁻¹ ∈ Sodd := by
  have hx' : Odd (orderOf x) := hx
  change Odd (orderOf (g * x * g⁻¹))
  have h : orderOf (g * x * g⁻¹) = orderOf x := by
    simpa [MulAut.conj_apply] using MulEquiv.orderOf_eq (MulAut.conj g) x
  rw [h]
  exact hx'

private lemma closure_Sodd_normal : (Subgroup.closure Sodd).Normal := by
  refine ⟨fun n hn g => ?_⟩
  induction hn using Subgroup.closure_induction with
  | mem x hx => exact Subgroup.subset_closure (conj_mem_Sodd g hx)
  | one => simpa using Subgroup.one_mem (Subgroup.closure Sodd)
  | mul x y hx hy ihx ihy =>
      have hxy : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by
        simpa [MulAut.conj_apply] using map_mul (MulAut.conj g) x y
      rw [hxy]
      exact Subgroup.mul_mem _ ihx ihy
  | inv x hx ih =>
      have hx' : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by
        simpa [MulAut.conj_apply] using map_inv (MulAut.conj g) x
      rw [hx']
      exact Subgroup.inv_mem _ ih

theorem sec128_model_oddNormal_bot
    (N : Subgroup (Multiplicative (ZMod 2) × ↥(alternatingGroup (Fin 5)))) [N.Normal]
    (hN : Odd (Nat.card N)) : N = ⊥ := by
  haveI hNmap : (N.map pi2).Normal := (inferInstance : N.Normal).map pi2 pi2_surjective
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map pi2) with hbot | htop
  · rw [Subgroup.eq_bot_iff_forall]
    intro n hn
    have hn2 : n.2 = 1 := by
      have hker : n ∈ pi2.ker := (Subgroup.map_eq_bot_iff N).mp hbot hn
      have : pi2 n = 1 := MonoidHom.mem_ker.mp hker
      simpa [pi2] using this
    have hnn : n * n = 1 := by
      refine Prod.ext ?_ ?_
      · simpa using mul_self_zmod2 n.1
      · simp [hn2]
    have hdvd2 : orderOf n ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one, pow_two]
      exact hnn
    have hdvdN : orderOf n ∣ Nat.card N := by
      have h := orderOf_dvd_natCard (⟨n, hn⟩ : N)
      rwa [← Subgroup.orderOf_coe] at h
    have hodd : Odd (orderOf n) := Odd.of_dvd_nat hN hdvdN
    have hn1 : n.1 = 1 := fst_eq_one_of_odd hodd
    exact Prod.ext hn1 hn2
  · exfalso
    have hdvd : Nat.card Alt5 ∣ Nat.card N := by
      have h := Subgroup.card_map_dvd (H := N) (f := pi2)
      rwa [htop, Subgroup.card_top] at h
    have h60 : 60 ∣ Nat.card N := by rwa [card_alt5] at hdvd
    rcases hN.of_dvd_nat h60 with ⟨k, hk⟩
    omega

theorem sec128_model_oTwo_le
    (P : Subgroup (Multiplicative (ZMod 2) × ↥(alternatingGroup (Fin 5)))) [P.Normal]
    (hP : ∀ m ∈ Subgroup.closure
        {m : Multiplicative (ZMod 2) × ↥(alternatingGroup (Fin 5)) | Odd (orderOf m)},
      m * m = 1 → m ∈ P) :
    ∀ m ∈ Subgroup.closure
        {m : Multiplicative (ZMod 2) × ↥(alternatingGroup (Fin 5)) | Odd (orderOf m)}, m ∈ P := by
  change ∀ m ∈ Subgroup.closure Sodd, m ∈ P
  have hP' : ∀ m ∈ Subgroup.closure Sodd, m * m = 1 → m ∈ P := hP
  obtain ⟨a3, ha3⟩ := exists_orderOf_three
  have ha3mem : a3 ∈ (Subgroup.closure Sodd).comap iota2 := by
    show iota2 a3 ∈ Subgroup.closure Sodd
    apply Subgroup.subset_closure
    show Odd (orderOf (iota2 a3))
    rw [orderOf_injective iota2 iota2_injective a3, ha3]
    exact ⟨1, by norm_num⟩
  have ha3ne : a3 ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha3
    exact absurd ha3 (by norm_num)
  have hcomap_top : (Subgroup.closure Sodd).comap iota2 = ⊤ := by
    haveI : ((Subgroup.closure Sodd).comap iota2).Normal := closure_Sodd_normal.comap iota2
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Subgroup.closure Sodd).comap iota2) with
      h | h
    · rw [h] at ha3mem
      exact absurd (Subgroup.mem_bot.mp ha3mem) ha3ne
    · exact h
  have hAall : ∀ a : Alt5, iota2 a ∈ Subgroup.closure Sodd := by
    intro a
    have h : a ∈ (Subgroup.closure Sodd).comap iota2 := by
      rw [hcomap_top]
      exact Subgroup.mem_top a
    exact h
  obtain ⟨a2, ha2⟩ := exists_orderOf_two
  have ha2ne : a2 ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha2
    exact absurd ha2 (by norm_num)
  have ha2sq : a2 * a2 = 1 := by
    rw [← pow_two, ← ha2, pow_orderOf_eq_one]
  have hPall : ∀ a : Alt5, iota2 a ∈ P := by
    have hcomapP : P.comap iota2 = ⊤ := by
      haveI : (P.comap iota2).Normal := (inferInstance : P.Normal).comap iota2
      have ha2mem : a2 ∈ P.comap iota2 := by
        show iota2 a2 ∈ P
        refine hP' (iota2 a2) (hAall a2) ?_
        rw [← map_mul, ha2sq, map_one]
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P.comap iota2) with h | h
      · rw [h] at ha2mem
        exact absurd (Subgroup.mem_bot.mp ha2mem) ha2ne
      · exact h
    intro a
    have h : a ∈ P.comap iota2 := by
      rw [hcomapP]
      exact Subgroup.mem_top a
    exact h
  refine (Subgroup.closure_le P).mpr ?_
  intro m hm
  have hm1 : m.1 = 1 := fst_eq_one_of_odd hm
  have hm_eq : m = iota2 m.2 := Prod.ext hm1 rfl
  rw [hm_eq]
  exact hPall m.2

end CFSG.OddStandard.SmallF3.Omega
