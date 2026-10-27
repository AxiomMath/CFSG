module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Ext
public import CFSG.Adapters.Involutions
public import CFSG.Quasithin.Background.A1cTransfer
public import CFSG.GH74.GLS.Bg.Local.Transfer1515

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec12

open Subgroup CFSG.Quasithin

theorem not_two_dvd_index_of_isSylow2In {X : Type*} [Group X] {P : Subgroup X}
    (hP : IsSylow2In P ⊤) : ¬ 2 ∣ P.index := by
  simpa [Subgroup.relIndex_top_right] using hP.2.2

theorem ig_15_3 : IG_15_3 := by
  intro X _ _ hsimple hnonab P hP z hzP hz hz1 hzc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Sylow 2 X := hP.2.1.toSylow (not_two_dvd_index_of_isSylow2In hP)
  have hSP : (S : Subgroup X) = P := rfl
  by_contra hcon
  have hwc : ∀ g : X, g⁻¹ * z * g ∈ (S : Subgroup X) → g⁻¹ * z * g = z := by
    intro g hg
    by_contra hne
    exact hcon ⟨g, hg, hne⟩
  let zs : (S : Subgroup X) := ⟨z, hzP⟩
  have hzZ : zs ∈ Subgroup.center (S : Subgroup X) :=
    Subgroup.mem_center_iff.mpr fun t => Subtype.ext (hzc t t.2).symm
  have hzs2 : zs ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using hz)
  have hzs1 : zs ≠ 1 := fun e => hz1 (congrArg Subtype.val e)
  have hzord : orderOf zs = 2 := orderOf_eq_prime hzs2 hzs1
  obtain ⟨_, hcen⟩ := CFSG.Adapters.glauberman_zStar S zs hzZ hzord hwc
  have hzord' : orderOf z = 2 := by
    rw [← hzord]
    exact Subgroup.orderOf_coe zs
  have hodd : CFSG.oddCore X = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (CFSG.oddCore X) with h | h
    · exact h
    · exact absurd (h ▸ Subgroup.mem_top z) (CFSG.Adapters.not_mem_oddCore_of_orderOf_eq_two hzord')
  have hzcen : z ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := Subgroup.mem_center_iff.mp hcen (QuotientGroup.mk g)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hodd,
      Subgroup.mem_bot] at h1
    exact (inv_mul_eq_one.mp h1)
  rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact hz1 (by simpa [h] using hzcen)
  · obtain ⟨a, b, hab⟩ := hnonab
    exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)

theorem isWeaklyClosedIn_self {X : Type*} [Group X] [Finite X] (P : Subgroup X) :
    IsWeaklyClosedIn P P := by
  intro g hg
  have hcard : Nat.card ↥(conjSubgroup P g) = Nat.card ↥P :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  exact Subgroup.eq_of_le_of_card_ge hg (by rw [hcard])

theorem ig_16_2 : IG_16_2 := by
  intro X _ _ P hP a b ha hb hac hbc hconj
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Sylow 2 X := hP.2.1.toSylow (not_two_dvd_index_of_isSylow2In hP)
  have hSP : (S : Subgroup X) = P := rfl
  obtain ⟨g, hg⟩ := hconj
  have hx : a ∈ Subgroup.centralizer (P : Set X) :=
    Subgroup.mem_centralizer_iff.mpr fun t ht => (hac t ht).symm
  have hy : b ∈ Subgroup.centralizer (P : Set X) :=
    Subgroup.mem_centralizer_iff.mpr fun t ht => (hbc t ht).symm
  exact burnside_fusion_lemma_centralizer S (W := P) (le_of_eq hSP.symm) (isWeaklyClosedIn_self P)
    hx hy hg

theorem ig_15_15 : IG_15_15 := by
  intro X _ _ P Q u hP _hQP hQn _hQne hcyc huP huQ hleast hc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPidx : ¬ 2 ∣ P.index := not_two_dvd_index_of_isSylow2In hP
  obtain ⟨n, hn⟩ : ∃ n, orderOf u = 2 ^ n := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp hP.2.1 ⟨u, huP⟩
    exact ⟨n, by simpa using hn⟩
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply huQ
    have : u = 1 := orderOf_eq_one_iff.mp (by simpa using hn)
    rw [this]
    exact Q.one_mem
  refine CFSG.GH74.GLS.Bg.Thompson.thompson_transfer_1515 (p := 2) hP.2.1 hPidx hQn hcyc huP huQ
    ?_ (fun g hg hext => hc _ hg ⟨g, rfl⟩ hext)
  intro g k hmem
  by_contra hnot
  have hle := hleast _ hmem hnot
  have hk : k ≠ 0 := by
    rintro rfl
    apply hnot
    simp
  have hord : orderOf (g⁻¹ * u ^ (2 * k) * g) = orderOf (u ^ (2 * k)) := by
    have := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective
      (u ^ (2 * k))
    simpa [MulAut.conj_apply] using this
  have hdvd : orderOf (u ^ (2 * k)) ∣ 2 ^ (n - 1) := by
    rw [orderOf_dvd_iff_pow_eq_one, ← pow_mul]
    have h2 : 2 * k * 2 ^ (n - 1) = k * orderOf u := by
      rw [hn]
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
      simp [pow_succ]
      ring
    rw [h2, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
  have hlt : 2 ^ (n - 1) < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have := Nat.le_of_dvd (pow_pos (by norm_num) _) hdvd
  rw [hord] at hle
  omega

end CFSG.GH74.GLS.Stage1.Thm6.Sec12
