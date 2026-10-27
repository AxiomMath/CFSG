module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.Basic

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup
open CFSG.EvenSporadicStandard.Finkelstein77 (innAut)

variable {G : Type} [Group G] {L : Subgroup G}

@[expose] noncomputable def thetaH {z : G}
    (hMN : centralizer ({z} : Set G) ≤ normalizer (L : Set G)) :
    centralizer ({z} : Set G) →* MulAut (L ⧸ center L) :=
  (normalizerAction L).comp (Subgroup.inclusion hMN)

theorem thetaH_apply {z : G} (hMN : centralizer ({z} : Set G) ≤ normalizer (L : Set G))
    (g : centralizer ({z} : Set G)) (x l : L) (hl : (l : G) = (g : G) * x * (g : G)⁻¹) :
    thetaH hMN g (x : L ⧸ center L) = (l : L ⧸ center L) :=
  normalizerAction_apply (Subgroup.inclusion hMN g) x l hl

theorem le_centralizer_singleton {z : G} (hz : z ∈ centralizer (L : Set G)) :
    L ≤ centralizer ({z} : Set G) := fun l hl =>
  mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hz l hl)

theorem thetaH_conj {z : G} (hMN : centralizer ({z} : Set G) ≤ normalizer (L : Set G))
    (hz : z ∈ centralizer (L : Set G)) (l : L) :
    thetaH hMN ⟨(l : G), le_centralizer_singleton hz l.2⟩ = MulAut.conj (l : L ⧸ center L) := by
  ext x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  rw [MulAut.conj_apply]
  refine (thetaH_apply hMN _ y (l * y * l⁻¹) (by simp)).trans ?_
  simp

theorem thetaH_eq_one_iff [Finite G] (h : StdHyp G L)
    (hS : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {z : G}
    (hz : z ∈ centralizer (L : Set G)) (hz2 : orderOf z = 2)
    (hMN : centralizer ({z} : Set G) ≤ normalizer (L : Set G))
    (g : centralizer ({z} : Set G)) : thetaH hMN g = 1 ↔ (g : G) ∈ zpowers z := by
  have h1 : thetaH hMN g = 1 ↔ (g : G) ∈ centralizer (L : Set G) :=
    normalizerAction_eq_one_iff h.standard.1.1 (Subgroup.inclusion hMN g)
  rw [h1, ← h.centralizer_inf_centralizer_eq_zpowers hS hz hz2]
  constructor
  · intro hg
    exact ⟨hg, g.2⟩
  · intro hg
    exact hg.1

theorem thetaH_ker [Finite G] (h : StdHyp G L)
    (hS : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {z : G}
    (hz : z ∈ centralizer (L : Set G)) (hz2 : orderOf z = 2)
    (hMN : centralizer ({z} : Set G) ≤ normalizer (L : Set G)) :
    (thetaH hMN).ker =
      zpowers (⟨z, mem_centralizer_singleton_iff.2 rfl⟩ : centralizer ({z} : Set G)) := by
  ext g
  rw [MonoidHom.mem_ker, thetaH_eq_one_iff h hS hz hz2 hMN, mem_zpowers_iff, mem_zpowers_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩

theorem relIndex_sup_zpowers_eq_two [Finite G] (h : StdHyp G L)
    (hS : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {z : G}
    (hz : z ∈ centralizer (L : Set G)) (hz2 : orderOf z = 2)
    (hout : (innAut (L ⧸ center L)).index ∣ 2)
    (hidx : (L ⊔ centralizer (L : Set G)).relIndex (normalizer (L : Set G)) = 2) :
    (L ⊔ zpowers z).relIndex (centralizer ({z} : Set G)) = 2 := by
  have hdvd := (h.relIndex_sup_zpowers_dvd hS hz hz2).trans hout
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
  · exfalso
    have hle : centralizer ({z} : Set G) ≤ L ⊔ zpowers z := Subgroup.relIndex_eq_one.1 h1
    have hinn : centralizer ({z} : Set G) ≤ L ⊔ centralizer (L : Set G) :=
      hle.trans (sup_le_sup_left (zpowers_le.2 hz) L)
    have hN := M22Std.normalizer_le_sup_centralizer_of_centralizer_le hS hz hz2 hinn
    rw [Subgroup.relIndex_eq_one.2 hN] at hidx
    exact absurd hidx (by norm_num)
  · exact h2

theorem thetaH_surjective [Finite G] (h : StdHyp G L)
    (hS : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {z : G}
    (hz : z ∈ centralizer (L : Set G)) (hz2 : orderOf z = 2)
    (hMN : centralizer ({z} : Set G) ≤ normalizer (L : Set G))
    (hout : (innAut (L ⧸ center L)).index ∣ 2)
    (hidx : (L ⊔ centralizer (L : Set G)).relIndex (normalizer (L : Set G)) = 2) :
    Function.Surjective (thetaH hMN) := by
  have hrel := relIndex_sup_zpowers_eq_two h hS hz hz2 hout hidx
  set R := (thetaH hMN).range with hR
  have hinnR : innAut (L ⧸ center L) ≤ R := by
    rintro _ ⟨q, rfl⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨⟨(l : G), le_centralizer_singleton hz l.2⟩, thetaH_conj hMN hz l⟩
  have hnle : ¬ R ≤ innAut (L ⧸ center L) := by
    intro hle
    have hne : ¬ centralizer ({z} : Set G) ≤ L ⊔ zpowers z := fun h1 =>
      absurd (Subgroup.relIndex_eq_one.2 h1) (by rw [hrel]; norm_num)
    apply hne
    intro g hg
    have hmem : thetaH hMN ⟨g, hg⟩ ∈ innAut (L ⧸ center L) := hle ⟨⟨g, hg⟩, rfl⟩
    have h2 := (normalizerAction_mem_range_conj_iff h.standard.1.1
      (Subgroup.inclusion hMN ⟨g, hg⟩)).1 hmem
    rw [← h.centralizer_inf_sup_centralizer_eq hS hz hz2]
    exact ⟨hg, h2⟩
  have h1 := Subgroup.relIndex_mul_index hinnR
  rcases (Nat.dvd_prime Nat.prime_two).1 hout with h3 | h3
  · have htop : innAut (L ⧸ center L) = ⊤ := Subgroup.index_eq_one.1 h3
    have : R = ⊤ := eq_top_iff.2 (htop ▸ hinnR)
    exact MonoidHom.range_eq_top.1 this
  · rw [h3] at h1
    have hne1 : (innAut (L ⧸ center L)).relIndex R ≠ 1 := fun h4 =>
      hnle (Subgroup.relIndex_eq_one.1 h4)
    have hd : (innAut (L ⧸ center L)).relIndex R ∣ 2 := ⟨R.index, h1.symm⟩
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h4 | h4
    · exact absurd h4 hne1
    · rw [h4] at h1
      have h5 : R.index = 1 := by omega
      exact MonoidHom.range_eq_top.1 (Subgroup.index_eq_one.1 h5)

end CFSG.EvenSporadicStandard.Fin76b
