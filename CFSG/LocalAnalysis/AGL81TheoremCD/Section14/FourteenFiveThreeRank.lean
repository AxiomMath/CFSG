module

public import CFSG.Open.LocalVocabulary
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
import CFSG.LocalAnalysis.SectionRank.DerivedQuotient
import CFSG.Permutation.OrderThreeCentralizer
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115QuotientMembership

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FourteenFiveThree

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem two_le_pRank_centralizer_of_mulEquiv {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) {M : Subgroup G} {K : Subgroup ↥M} [K.Normal] {E : Subgroup G}
    (hEM : E ≤ M)
    (hE : IsElemAbelian p E) (hEcard : Nat.card ↥E = p ^ 2)
    (hdisj : E.subgroupOf M ⊓ K = ⊥) {d : G} (hdM : d ∈ M)
    (hEC : E ≤ Subgroup.centralizer ({d} : Set G))
    (e : (↥M ⧸ K) ≃* X)
    (hy : orderOf (e (QuotientGroup.mk' K ⟨d, hdM⟩)) = 3) :
    2 ≤ pRank p (Subgroup.centralizer
      ({e (QuotientGroup.mk' K ⟨d, hdM⟩)} : Set X)) := by
  let q : ↥M →* (↥M ⧸ K) := QuotientGroup.mk' K
  let ι : ↥E →* ↥M := Subgroup.inclusion hEM
  let f : ↥E →* X := e.toMonoidHom.comp (q.comp ι)
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hxq : q (ι x) = 1 := e.injective (by simpa [f] using hx)
    have hxK : ι x ∈ K := (QuotientGroup.eq_one_iff (ι x)).mp (by simpa [q] using hxq)
    have hxE : ι x ∈ E.subgroupOf M := by
      rw [Subgroup.mem_subgroupOf]
      exact x.2
    have hxinf : ι x ∈ E.subgroupOf M ⊓ K := ⟨hxE, hxK⟩
    rw [hdisj, Subgroup.mem_bot] at hxinf
    exact Subgroup.mem_bot.mpr (Subgroup.inclusion_injective hEM hxinf)
  have hrange : f.range ≤ Subgroup.centralizer
      ({e (QuotientGroup.mk' K ⟨d, hdM⟩)} : Set X) := by
    rintro z ⟨x, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxcomm : (x : G) * d = d * (x : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hEC x.2)
    have hcommM : ι x * (⟨d, hdM⟩ : ↥M) = (⟨d, hdM⟩ : ↥M) * ι x := by
      apply Subtype.ext
      simpa [ι] using hxcomm
    have hcommq : q (ι x) * q ⟨d, hdM⟩ = q ⟨d, hdM⟩ * q (ι x) := by
      rw [← map_mul, ← map_mul, hcommM]
    have hcomm := congrArg e hcommq
    simpa [f, q, MulEquiv.map_mul] using hcomm
  refine CFSG.SectionRank.le_pRank_of_injective (G := X) (A := ↥E) hp.one_lt ?_ ?_
    (k := 2) hEcard f hf hrange
  · haveI := hE.1
    exact fun a b => mul_comm' a b
  · intro a
    exact Subtype.ext (by simpa using hE.2 (a : G) a.2)

private theorem exists_elemAbelian_disjoint {M : Subgroup G} {p : ℕ} (hp : p.Prime)
    {d : G}
    (hrank : 2 ≤ pRank p (M ⊓ Subgroup.centralizer ({d} : Set G)))
    (hcon : ¬ p ∣ Nat.card ↥((CFSG.pPrimeCore 3 ↥M).map M.subtype ⊓
      Subgroup.centralizer ({d} : Set G))) :
    ∃ E : Subgroup G, E ≤ M ∧ E ≤ Subgroup.centralizer ({d} : Set G) ∧
      IsElemAbelian p E ∧ Nat.card ↥E = p ^ 2 ∧
      E.subgroupOf M ⊓ CFSG.pPrimeCore 3 ↥M = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  let K : Subgroup ↥M := CFSG.pPrimeCore 3 ↥M
  obtain ⟨E, hE_le, hE, hEcard⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (k := 2) hrank
  have hEM : E ≤ M := hE_le.trans inf_le_left
  have hEC : E ≤ Subgroup.centralizer ({d} : Set G) := hE_le.trans inf_le_right
  have hinf : E ⊓ K.map M.subtype = ⊥ := by
    have hle : E ⊓ K.map M.subtype ≤
        K.map M.subtype ⊓ Subgroup.centralizer ({d} : Set G) :=
      le_inf inf_le_right (inf_le_left.trans hEC)
    have hpn : ¬ p ∣ Nat.card ↥(E ⊓ K.map M.subtype) := fun h =>
      hcon (h.trans (Subgroup.card_dvd_of_le hle))
    have hcop : Nat.Coprime (Nat.card ↥(E ⊓ K.map M.subtype)) (p ^ 2) :=
      ((hp.coprime_iff_not_dvd).mpr hpn).symm.pow_right 2
    have hdvd : Nat.card ↥(E ⊓ K.map M.subtype) ∣ p ^ 2 := by
      simpa [hEcard] using
        Subgroup.card_dvd_of_le (inf_le_left : E ⊓ K.map M.subtype ≤ E)
    exact Subgroup.eq_bot_of_card_eq _ (Nat.Coprime.eq_one_of_dvd hcop hdvd)
  have hdisj : E.subgroupOf M ⊓ K = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    rw [Subgroup.mem_bot]
    have hxE : (x : G) ∈ E := Subgroup.mem_subgroupOf.mp hx.1
    have hxK : (x : G) ∈ K.map M.subtype := ⟨x, hx.2, rfl⟩
    have hxinf : (x : G) ∈ E ⊓ K.map M.subtype := ⟨hxE, hxK⟩
    rw [hinf, Subgroup.mem_bot] at hxinf
    exact Subtype.ext hxinf
  exact ⟨E, hEM, hEC, hE, hEcard, hdisj⟩

theorem dvd_card_pPrimeCore_inf_centralizer {M : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p)
    (hMbar : Nonempty (↥M ⧸ CFSG.pPrimeCore 3 ↥M ≃* Equiv.Perm (Fin 9)) ∨
      Nonempty (↥M ⧸ CFSG.pPrimeCore 3 ↥M ≃* alternatingGroup (Fin 11)) ∨
      Nonempty (↥M ⧸ CFSG.pPrimeCore 3 ↥M ≃* Equiv.Perm (Fin 11)))
    {d : G} (hdM : d ∈ M) (hd : orderOf d = 3)
    (hrank : 2 ≤ CFSG.Open.pRank p (M ⊓ Subgroup.centralizer ({d} : Set G))) :
    p ∣ Nat.card ↥((CFSG.pPrimeCore 3 ↥M).map M.subtype ⊓
      Subgroup.centralizer ({d} : Set G)) := by
  let K : Subgroup ↥M := CFSG.pPrimeCore 3 ↥M
  change p ∣ Nat.card ↥(K.map M.subtype ⊓ Subgroup.centralizer ({d} : Set G))
  by_contra hcon
  obtain ⟨E, hEM, hEC, hE, hEcard, hdisj⟩ := exists_elemAbelian_disjoint hp hrank hcon
  have hdK : d ∉ K.map M.subtype := by
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    intro hmem
    have h3 : 3 ∣ Nat.card ↥(K.map M.subtype) := by
      simpa [hd] using Subgroup.orderOf_dvd_natCard (K.map M.subtype) hmem
    rw [Subgroup.card_map_of_injective M.subtype_injective] at h3
    exact (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mp
      (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥M)) h3
  have hdK' : (⟨d, hdM⟩ : ↥M) ∉ K := fun h => hdK ⟨⟨d, hdM⟩, h, rfl⟩
  let dstar : ↥M ⧸ K := QuotientGroup.mk' K ⟨d, hdM⟩
  have hdstar : orderOf dstar = 3 := by
    have hx : orderOf (⟨d, hdM⟩ : ↥M) = 3 := by rw [Subgroup.orderOf_mk, hd]
    exact CFSG.BenderSuzuki.lemma115_orderOf_quotient_eq_prime_of_not_mem K
      (by norm_num : Nat.Prime 3) hx hdK'
  rcases hMbar with hbar | hbar | hbar
  · obtain ⟨e⟩ := hbar
    have hy : orderOf (e dstar) = 3 := by rw [MulEquiv.orderOf_eq, hdstar]
    have h2 := two_le_pRank_centralizer_of_mulEquiv hp hEM hE hEcard hdisj hdM hEC e hy
    have h2' : 2 ≤ CFSG.Open.pRank p (Subgroup.centralizer ({e dstar} : Set _)) := by
      simpa [dstar] using h2
    have h1 := CFSG.Permutation.pRank_centralizer_le_one_of_orderOf_eq_three
      (n := 9) (by norm_num) hp hp5 hy
    omega
  · obtain ⟨e⟩ := hbar
    have hy : orderOf (e dstar) = 3 := by rw [MulEquiv.orderOf_eq, hdstar]
    have h2 := two_le_pRank_centralizer_of_mulEquiv hp hEM hE hEcard hdisj hdM hEC e hy
    have h2' : 2 ≤ CFSG.Open.pRank p (Subgroup.centralizer ({e dstar} : Set _)) := by
      simpa [dstar] using h2
    have h1 := CFSG.Permutation.pRank_centralizer_alternatingGroup_le_one_of_orderOf_eq_three
      (n := 11) (by norm_num) hp hp5 hy
    omega
  · obtain ⟨e⟩ := hbar
    have hy : orderOf (e dstar) = 3 := by rw [MulEquiv.orderOf_eq, hdstar]
    have h2 := two_le_pRank_centralizer_of_mulEquiv hp hEM hE hEcard hdisj hdM hEC e hy
    have h2' : 2 ≤ CFSG.Open.pRank p (Subgroup.centralizer ({e dstar} : Set _)) := by
      simpa [dstar] using h2
    have h1 := CFSG.Permutation.pRank_centralizer_le_one_of_orderOf_eq_three
      (n := 11) (by norm_num) hp hp5 hy
    omega

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FourteenFiveThree
