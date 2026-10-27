module

public import CFSG.GH74.Uniqueness.SU.SU1Graph

public section

namespace CFSG.GH74.Uniqueness.SU.SU1

open Subgroup

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

theorem isolated_absorbs (hp : p.Prime) {P : Subgroup G} {A : Ep2Vertex p P}
    (hA : IsIsolated p A) {F : Subgroup G} (hFP : F ≤ P) (hF : Open.IsElemAbelian p F)
    (hcomm : ∀ f ∈ F, ∀ x ∈ A.1, f * x = x * f) (hcard : p ^ 2 ≤ Nat.card F) : F = A.1 := by
  obtain ⟨W, hWF, hW, hWcard⟩ := exists_vertex_le hp hF hcard
  have hWA : (⟨W, hWF.trans hFP, hW, hWcard⟩ : Ep2Vertex p P) = A := by
    by_contra hne
    exact hA ⟨W, hWF.trans hFP, hW, hWcard⟩
      ⟨fun h => hne h.symm, fun a ha b hb => (hcomm b (hWF hb) a ha).symm⟩
  have hAF : A.1 ≤ F := by
    have : W = A.1 := congrArg Subtype.val hWA
    rw [← this]
    exact hWF
  by_contra hFA
  have hlt : A.1 < F := lt_of_le_of_ne hAF (Ne.symm hFA)
  have hc := card_lt_of_lt hlt
  rw [A.2.2.2] at hc
  obtain ⟨k, hk⟩ := IsElemAbelian.exists_card hp hF
  rw [hk] at hc
  have hk3 : 3 ≤ k := by
    by_contra hcon
    have : k ≤ 2 := by omega
    have : p ^ k ≤ p ^ 2 := Nat.pow_le_pow_right hp.pos this
    omega
  obtain ⟨W', hW'F, hW', hW'card, hW'ne⟩ := exists_other_vertex hp A.2.2.2 hF
    (by rw [hk]; exact Nat.pow_le_pow_right hp.pos hk3)
  exact hA ⟨W', hW'F.trans hFP, hW', hW'card⟩
    ⟨fun h => hW'ne (congrArg Subtype.val h).symm, fun a ha b hb => (hcomm b (hW'F hb) a ha).symm⟩

theorem not_le_of_isIsolated (hp : p.Prime) {P : Subgroup G} (hP : IsPGroup p P)
    (hrk : 3 ≤ Open.pRank p P) (A : Ep2Vertex p P) (hA : IsIsolated p A) {E : Subgroup G}
    (hEP : E ≤ P) (hEn : P ≤ normalizer (E : Set G)) (hE : Open.IsElemAbelian p E) :
    ¬ A.1 ≤ E := by
  intro hAE
  by_cases hEA : E = A.1
  · exact not_isIsolated_of_isNormalEp2 hp hP hrk (U := A.1) ⟨A.2.1, hEA ▸ hEn, A.2.2.1, A.2.2.2⟩
      A rfl hA
  · have hlt : A.1 < E := lt_of_le_of_ne hAE (Ne.symm hEA)
    have hc := card_lt_of_lt hlt
    rw [A.2.2.2] at hc
    obtain ⟨k, hk⟩ := IsElemAbelian.exists_card hp hE
    rw [hk] at hc
    have hk3 : 3 ≤ k := by
      by_contra hcon
      have : k ≤ 2 := by omega
      have : p ^ k ≤ p ^ 2 := Nat.pow_le_pow_right hp.pos this
      omega
    obtain ⟨W, hWE, hW, hWcard, hWne⟩ := exists_other_vertex hp A.2.2.2 hE
      (by rw [hk]; exact Nat.pow_le_pow_right hp.pos hk3)
    refine hA ⟨W, ?_, hW, hWcard⟩ ⟨fun h => hWne (congrArg Subtype.val h).symm, ?_⟩
    · exact hWE.trans hEP
    · intro a ha b hb
      exact (isElemAbelian_iff.mp hE).1 a (hAE ha) b (hWE hb)

theorem ig10_21_iii (hp : p.Prime) {P : Subgroup G} (hP : IsPGroup p P) (hrk : 3 ≤ Open.pRank p P)
    (hU : ∃ U, IsNormalEp2 p P U) (A : Ep2Vertex p P) (hA : IsIsolated p A) {E : Subgroup G}
    (hEP : E ≤ P) (hEn : P ≤ normalizer (E : Set G)) (hE : Open.IsElemAbelian p E)
    (hE1 : E ≠ ⊥) :
    ¬ A.1 ≤ E ∧ ∀ a ∈ A.1, a ∉ E →
      (A.1 ⊓ E = E ⊓ centralizer (A.1 : Set G) ∧
        E ⊓ centralizer ({a} : Set G) = E ⊓ centralizer (A.1 : Set G) ∧
        Nat.card ↥(E ⊓ centralizer (A.1 : Set G)) = p) ∧
      (centralizer (A.1 : Set G) ⊓ P = centralizer ({a} : Set G) ⊓ P ∧
        ∃ K : Subgroup G, K ≤ P ∧ K ≤ centralizer ({a} : Set G) ∧ zpowers a ⊓ K = ⊥ ∧
          zpowers a ⊔ K = centralizer ({a} : Set G) ⊓ P ∧ A.1 ⊓ E ≤ K ∧ Open.pRank p K = 1) := by
  refine ⟨not_le_of_isIsolated hp hP hrk A hA hEP hEn hE, ?_⟩
  intro a haA haE
  obtain ⟨U, hU⟩ := hU
  have := Fact.mk hp
  have hAel := isElemAbelian_iff.mp A.2.2.1
  have hEel := isElemAbelian_iff.mp hE
  have haP : a ∈ P := A.2.1 haA
  have ha1 : a ≠ 1 := fun h => haE (h ▸ E.one_mem)
  have hap : a ^ p = 1 := hAel.2 a haA
  have hconjE := conj_mem_of_le_normalizer hEn
  obtain ⟨e, heE, he1, hec⟩ := exists_central_of_normal hp hP hEP hconjE hE1
  have hep : e ^ p = 1 := hEel.2 e heE
  have heP : e ∈ P := hEP heE
  have hoa : orderOf a = p := orderOf_eq_prime hap ha1
  have hoe : orderOf e = p := orderOf_eq_prime hep he1
  have hea : e ∉ zpowers a := by
    intro h
    have hle : zpowers e ≤ zpowers a := Subgroup.zpowers_le.mpr h
    have heq : zpowers e = zpowers a := Subgroup.eq_of_le_of_card_ge hle
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hoa, hoe])
    exact haE ((Subgroup.zpowers_le.mpr heE) (heq.symm.le (Subgroup.mem_zpowers a)))
  obtain ⟨hel2, hcard2⟩ := isElemAbelian_card_sup_zpowers hp hap hep ha1 hea (hec a haP)
  have hFA : ∀ f ∈ zpowers a ⊔ zpowers e, ∀ x ∈ A.1, f * x = x * f := by
    intro f hf x hx
    have h1 : a ∈ centralizer ({x} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hAel.1 a haA x hx)
    have h2 : e ∈ centralizer ({x} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hec x (A.2.1 hx)).symm
    have hle : zpowers a ⊔ zpowers e ≤ centralizer ({x} : Set G) :=
      sup_le (Subgroup.zpowers_le.mpr h1) (Subgroup.zpowers_le.mpr h2)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hf)
  have hAeq : zpowers a ⊔ zpowers e = A.1 :=
    isolated_absorbs hp hA (sup_le (Subgroup.zpowers_le.mpr haP) (Subgroup.zpowers_le.mpr heP))
      hel2 hFA (by rw [hcard2])
  have heA : e ∈ A.1 := hAeq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers e)
  have hcentA : ∀ x : G, x * a = a * x → x * e = e * x → x ∈ centralizer (A.1 : Set G) := by
    intro x hxa hxe
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [← hAeq] at hh
    have ha' : a ∈ centralizer ({x} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hxa.symm
    have he' : e ∈ centralizer ({x} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hxe.symm
    have hle : zpowers a ⊔ zpowers e ≤ centralizer ({x} : Set G) :=
      sup_le (Subgroup.zpowers_le.mpr ha') (Subgroup.zpowers_le.mpr he')
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hh)
  have hze : zpowers e ≤ A.1 ⊓ E :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨heA, heE⟩)
  have hAE_lt : A.1 ⊓ E < A.1 := by
    refine lt_of_le_of_ne inf_le_left (fun h => haE ?_)
    have : a ∈ A.1 ⊓ E := by rw [h]; exact haA
    exact this.2
  have hAEcard : Nat.card ↥(A.1 ⊓ E) = p := by
    have hc := card_lt_of_lt hAE_lt
    rw [A.2.2.2] at hc
    obtain ⟨s, hs⟩ := IsElemAbelian.exists_card hp (IsElemAbelian.mono (inf_le_left.trans le_rfl)
      A.2.2.1 : Open.IsElemAbelian p (A.1 ⊓ E))
    have hle := Subgroup.card_le_of_le hze
    rw [Nat.card_zpowers, hoe, hs] at hle
    rw [hs] at hc ⊢
    have hs1 : 1 ≤ s := by
      by_contra hcon
      have : s = 0 := by omega
      rw [this, pow_zero] at hle
      have := hp.one_lt
      omega
    have hs2 : s < 2 := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hc
    have : s = 1 := by omega
    rw [this, pow_one]
  have hAEeq : zpowers e = A.1 ⊓ E :=
    Subgroup.eq_of_le_of_card_ge hze (by rw [hAEcard, Nat.card_zpowers, hoe])
  have hCEA : A.1 ⊓ E = E ⊓ centralizer (A.1 : Set G) := by
    ext x
    constructor
    · rintro ⟨hxA, hxE⟩
      exact ⟨hxE, Subgroup.mem_centralizer_iff.mpr (fun h hh => hAel.1 h hh x hxA)⟩
    · rintro ⟨hxE, hxC⟩
      refine ⟨?_, hxE⟩
      have hxp : x ^ p = 1 := hEel.2 x hxE
      have hxcomm : ∀ h ∈ A.1, h * x = x * h := fun h hh =>
        Subgroup.mem_centralizer_iff.mp hxC h hh
      have hel3 : Open.IsElemAbelian p (A.1 ⊔ zpowers x) :=
        IsElemAbelian.sup A.2.2.1 (isElemAbelian_zpowers hxp)
          (by
            rintro h hh s ⟨m, rfl⟩
            exact (Commute.zpow_right (show Commute h x from hxcomm h hh) m).eq)
      have hF3 : A.1 ⊔ zpowers x = A.1 :=
        isolated_absorbs hp hA (sup_le A.2.1 (Subgroup.zpowers_le.mpr (hEP hxE))) hel3
          (fun f hf y hy => (isElemAbelian_iff.mp hel3).1 f hf y (Subgroup.mem_sup_left hy))
          (by
            have h := Subgroup.card_le_of_le (le_sup_left : A.1 ≤ A.1 ⊔ zpowers x)
            rwa [A.2.2.2] at h)
      rw [← hF3]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hCEa : E ⊓ centralizer ({a} : Set G) = E ⊓ centralizer (A.1 : Set G) := by
    ext x
    constructor
    · rintro ⟨hxE, hxa⟩
      exact ⟨hxE, hcentA x (Subgroup.mem_centralizer_singleton_iff.mp hxa)
        (hEel.1 x hxE e heE)⟩
    · rintro ⟨hxE, hxC⟩
      exact ⟨hxE, Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hxC a haA).symm⟩
  refine ⟨⟨hCEA, hCEa, by rw [← hCEA]; exact hAEcard⟩, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨hxC, hxP⟩
      exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hxC a haA).symm, hxP⟩
    · rintro ⟨hxa, hxP⟩
      exact ⟨hcentA x (Subgroup.mem_centralizer_singleton_iff.mp hxa) (hec x hxP), hxP⟩
  · set C : Subgroup G := centralizer ({a} : Set G) ⊓ P with hC
    set K : Subgroup G := centralizer (U : Set G) ⊓ C with hK
    obtain ⟨-, hrel, -⟩ := ig10_20_ii hp hP hU
    have hUP : U ≤ P := hU.1
    have heU : e ∈ centralizer (U : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      exact hec u (hUP hu)
    have haR : a ∉ centralizer (U : Set G) := by
      intro haU
      have hAU : A.1 ≤ centralizer (U : Set G) := by
        rw [← hAeq]
        exact sup_le (Subgroup.zpowers_le.mpr haU) (Subgroup.zpowers_le.mpr heU)
      have hUA : (⟨U, hU.1, hU.2.2⟩ : Ep2Vertex p P) = A := by
        by_contra hne
        exact hA ⟨U, hU.1, hU.2.2⟩ ⟨fun h => hne h.symm, fun x hx u hu =>
          (Subgroup.mem_centralizer_iff.mp (hAU hx) u hu).symm⟩
      exact not_isIsolated_of_isNormalEp2 hp hP hrk hU A (congrArg Subtype.val hUA).symm hA
    have haC : a ∈ C := ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, haP⟩
    have heC : e ∈ C := ⟨Subgroup.mem_centralizer_singleton_iff.mpr (hec a haP).symm, heP⟩
    have heK : e ∈ K := ⟨heU, heC⟩
    have haK : a ∉ K := fun h => haR h.1
    have hCP : C ≤ P := inf_le_right
    have hKC : K ≤ C := inf_le_right
    have hCpg : IsPGroup p C := hP.to_le hCP
    have hrelC : (centralizer (U : Set G)).relIndex C ≤ p :=
      (Subgroup.relIndex_le_of_le_right hCP (relIndex_ne_zero_of_finite _ _)).trans hrel
    have hrelC1 : (centralizer (U : Set G)).relIndex C ≠ 1 := by
      rw [Ne, Subgroup.relIndex_eq_one]
      intro h
      exact haR (h haC)
    obtain ⟨n, hn⟩ := relIndex_pow hp hCpg (centralizer (U : Set G))
    have hrelCp : (centralizer (U : Set G)).relIndex C = p :=
      hn ▸ pow_eq_self_of_le hp (hn ▸ hrelC) (hn ▸ hrelC1)
    have hCK : Nat.card C = p * Nat.card K := by
      have := Subgroup.relIndex_mul_card (H := centralizer (U : Set G)) (K := C)
      rw [hrelCp] at this
      exact this.symm
    have hKle : K ≤ zpowers a ⊔ K := le_sup_right
    have haS : a ∈ zpowers a ⊔ K := Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
    have hSC : zpowers a ⊔ K ≤ C := sup_le (Subgroup.zpowers_le.mpr haC) hKC
    have hKlt : K < zpowers a ⊔ K :=
      lt_of_le_of_ne hKle (fun h => haK (by rw [h]; exact haS))
    have hdvd1 : Nat.card K ∣ Nat.card (zpowers a ⊔ K : Subgroup G) :=
      Subgroup.card_dvd_of_le hKle
    have hdvd2 : Nat.card (zpowers a ⊔ K : Subgroup G) ∣ Nat.card C :=
      Subgroup.card_dvd_of_le hSC
    obtain ⟨m, hm⟩ := hdvd1
    have hKpos : 0 < Nat.card K := Nat.card_pos
    rw [hCK, hm] at hdvd2
    have hmp : m ∣ p := by
      have : Nat.card K * m ∣ Nat.card K * p := by rwa [mul_comm p] at hdvd2
      exact (Nat.mul_dvd_mul_iff_left hKpos).mp this
    have hm1 : m ≠ 1 := by
      intro h
      have := card_lt_of_lt hKlt
      rw [hm, h, mul_one] at this
      exact lt_irrefl _ this
    have hmp' : m = p := ((Nat.dvd_prime hp).mp hmp).resolve_left hm1
    have hSeq : zpowers a ⊔ K = C := Subgroup.eq_of_le_of_card_ge hSC
      (by rw [hCK, hm, hmp']; exact (Nat.mul_comm _ _).le)
    refine ⟨K, hKC.trans hCP, hKC.trans inf_le_left, ?_, hSeq, ?_, ?_⟩
    · by_contra hJne
      have hJle : zpowers a ⊓ K ≤ zpowers a := inf_le_left
      have hdvd : Nat.card ↥(zpowers a ⊓ K) ∣ p := by
        have := Subgroup.card_dvd_of_le hJle
        rwa [Nat.card_zpowers, hoa] at this
      rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
      · exact hJne (Subgroup.eq_bot_of_card_eq _ h1)
      · have hJeq : zpowers a ⊓ K = zpowers a :=
          Subgroup.eq_of_le_of_card_ge hJle (by rw [Nat.card_zpowers, hoa, h1])
        have : a ∈ zpowers a ⊓ K := by rw [hJeq]; exact Subgroup.mem_zpowers a
        exact haK this.2
    · rw [← hAEeq]
      exact Subgroup.zpowers_le.mpr heK
    · refine le_antisymm ?_ ?_
      · refine pRank_le_of ?_
        intro F hFK hF k hk
        by_contra hk2
        have hk2' : 2 ≤ k := by omega
        obtain ⟨W, hWF, hW, hWcard⟩ := exists_vertex_le hp hF
          (hk ▸ Nat.pow_le_pow_right hp.pos hk2')
        have hWK : W ≤ K := hWF.trans hFK
        have hWP : W ≤ P := hWK.trans (hKC.trans hCP)
        refine hA ⟨W, hWP, hW, hWcard⟩ ⟨?_, ?_⟩
        · intro h
          have hAW : A.1 = W := congrArg Subtype.val h
          apply haR
          have : a ∈ W := hAW ▸ haA
          exact (hWK this).1
        · intro x hx w hw
          have hwC : w ∈ centralizer (A.1 : Set G) := by
            apply hcentA w
            · exact Subgroup.mem_centralizer_singleton_iff.mp (hWK hw).2.1
            · exact hec w (hWP hw)
          exact Subgroup.mem_centralizer_iff.mp hwC x hx
      · exact le_pRank hp.one_lt (Subgroup.zpowers_le.mpr heK) (isElemAbelian_zpowers hep)
          (by rw [Nat.card_zpowers, hoe, pow_one])

end CFSG.GH74.Uniqueness.SU.SU1
