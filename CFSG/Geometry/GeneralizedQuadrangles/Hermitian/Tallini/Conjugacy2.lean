module

public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Tallini.Conjugacy

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons

universe u

variable {V : Type u}

section ConjugacyD2

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

theorem color_zero_of_mem_isStarLine {c : Γ.Coloring (Fin 2)} {L : Set V}
    (hL : IsStarLine Γ c L) {z : V} (hz : z ∈ L) : c z = 0 := by
  obtain ⟨x, y, hx, hy, hxy, rfl⟩ := hL
  exact color_eq_zero_of_mem_starLine hz

theorem exists_mem_ne_of_isStarLine {c : Γ.Coloring (Fin 2)} {L : Set V}
    (hL : IsStarLine Γ c L) (p : V) : ∃ q ∈ L, q ≠ p := by
  obtain ⟨x, y, hx, hy, hxy, rfl⟩ := hL
  by_cases hxp : x = p
  · refine ⟨y, mem_starLine_right hy, ?_⟩
    intro hyp
    exact hxy (hxp.trans hyp.symm)
  · exact ⟨x, mem_starLine_left hx, hxp⟩

theorem conjLine_eq_of_mem (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) {X : Set V} (hX : IsNonabsPlane Γ c X)
    {p q : V} (hp : c p = 0) (hpX : p ∉ X) (hq : q ∈ conjLine Γ c X p) :
    conjLine Γ c X q = conjLine Γ c X p := by
  classical
  have hNhyp : IsHypLine Γ c (conjLine Γ c X p) :=
    (isHypLine_conjLine hP hT c hdeg hreg hX.1 hp hpX).1
  have hNstar : IsStarLine Γ c (conjLine Γ c X p) := IsHypLine.isStarLine hP hNhyp
  have hNperp : ptPerp Γ c (conjLine Γ c X p) ⊆ X :=
    (isHypLine_conjLine hP hT c hdeg hreg hX.1 hp hpX).2.2
  have hdisj : Disjoint (conjLine Γ c X p) X :=
    disjoint_of_ptPerp_subset hP hT c hdeg hreg hX hNstar hNperp
  have hqX : q ∉ X := fun hqX => Set.disjoint_left.mp hdisj hq hqX
  exact (eq_conjLine hP hT c hdeg hreg hX.1 hqX hNstar hq hNperp).symm

theorem card_conjLine_partition (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) {X : Set V} (hX : IsNonabsPlane Γ c X)
    {S : Finset V} (hpoints : ∀ p ∈ S, c p = 0) (hoff : ∀ p ∈ S, p ∉ X)
    (hclosed : ∀ p ∈ S, conjLine Γ c X p ⊆ (S : Set V)) :
    S.card = (S.image (fun p => conjLine Γ c X p)).card * (t + 1) := by
  classical
  let f : V → Set V := fun p => conjLine Γ c X p
  have hfiber : ∀ N ∈ S.image f, (S.filter fun p => f p = N).card = t + 1 := by
    intro N hN
    obtain ⟨p0, hp0S, rfl⟩ := Finset.mem_image.mp hN
    have hp0 : c p0 = 0 := hpoints p0 hp0S
    have hp0X : p0 ∉ X := hoff p0 hp0S
    have hNhyp : IsHypLine Γ c (f p0) :=
      (isHypLine_conjLine hP hT c hdeg hreg hX.1 hp0 hp0X).1
    have hNcard : (f p0).ncard = t + 1 :=
      IsHypLine.ncard hP hT c hdeg hreg hNhyp
    have hp0N : p0 ∈ f p0 :=
      (isHypLine_conjLine hP hT c hdeg hreg hX.1 hp0 hp0X).2.1
    have hNsub : f p0 ⊆ (S : Set V) := hclosed p0 hp0S
    have hfiber_eq : (S.filter fun p => f p = f p0) = (f p0).toFinset := by
      ext q
      constructor
      · intro hq
        rw [Finset.mem_filter] at hq
        have hqS : q ∈ S := hq.1
        have hq0 : c q = 0 := hpoints q hqS
        have hqX : q ∉ X := hoff q hqS
        have hqN : q ∈ f p0 := by
          rw [← hq.2]
          exact (isHypLine_conjLine hP hT c hdeg hreg hX.1 hq0 hqX).2.1
        simpa using hqN
      · intro hq
        rw [Finset.mem_filter]
        have hqN : q ∈ f p0 := by simpa using hq
        have hqS : q ∈ S := hNsub hqN
        refine ⟨hqS, ?_⟩
        exact conjLine_eq_of_mem hP hT c hdeg hreg hX hp0 hp0X hqN
    rw [hfiber_eq, ← Set.ncard_eq_toFinset_card' (f p0)]
    exact hNcard
  have h := Finset.card_eq_sum_card_image f S
  rw [h]
  calc
    ∑ N ∈ S.image f, (S.filter fun p => f p = N).card =
        ∑ N ∈ S.image f, (t + 1) := Finset.sum_congr rfl hfiber
    _ = (S.image f).card * (t + 1) := by
      rw [Finset.sum_const, smul_eq_mul]

theorem conjLine_subset_sdiff (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) {X : Set V} (hX : IsNonabsPlane Γ c X)
    {p : V} (hp : c p = 0) (hpX : p ∉ X) :
    conjLine Γ c X p ⊆ Xᶜ := by
  intro z hz
  have hNhyp : IsHypLine Γ c (conjLine Γ c X p) :=
    (isHypLine_conjLine hP hT c hdeg hreg hX.1 hp hpX).1
  have hNperp : ptPerp Γ c (conjLine Γ c X p) ⊆ X :=
    (isHypLine_conjLine hP hT c hdeg hreg hX.1 hp hpX).2.2
  have hdisj : Disjoint (conjLine Γ c X p) X :=
    disjoint_of_ptPerp_subset hP hT c hdeg hreg hX
      (IsHypLine.isStarLine hP hNhyp) hNperp
  exact fun hzX => Set.disjoint_left.mp hdisj hz hzX

theorem isHypLine_inter_of_isConjPlane (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) (hst : s ≠ t) (hii : TalliniCond Γ c)
    {X Y : Set V} (hX : IsNonabsPlane Γ c X) (hY : IsNonabsPlane Γ c Y)
    (hc : IsConjPlane Γ c X Y) : IsHypLine Γ c (X ∩ Y) := by
  classical
  have hii' : TalliniCondPrime Γ c := talliniCondPrime_of_talliniCond hP hT c hdeg hreg hii
  have hXneY : X ≠ Y := by
    intro hXY
    subst hXY
    have habs : IsAbsPlane Γ c X :=
      (isConjPlane_self_iff hP hT c hdeg hreg hX.1).mp hc
    exact not_isNonabsPlane_of_isAbsPlane hP hT c hdeg habs hX
  have hnonempty : (X ∩ Y).Nonempty :=
    inter_nonempty hP hT c hdeg hreg hst hii' hX.1 hY.1
  rcases inter_cases hP hT c hdeg hreg hX.1 hY.1 hXneY with hzero | hsingle | hline
  · exact absurd hzero hnonempty.ne_empty
  · obtain ⟨x, hx⟩ := hsingle
    exfalso
    have hseq : s = t ^ 2 := s_eq_t_sq hP hT c hdeg hreg hst hii'
    have hYcard : Y.ncard = t ^ 3 + 1 := by
      rw [ncard_of_isOvoid hP hT c hdeg hY.2, hseq]
      ring
    have hInter : (Y ∩ X).ncard = 1 := by
      rw [Set.inter_comm, hx]
      simp
    have hDiff : (Y \ X).ncard = t ^ 3 := by
      have h := Set.ncard_inter_add_ncard_sdiff_eq_ncard Y X
      rw [hInter, hYcard] at h
      omega
    let S : Finset V := (Y \ X).toFinset
    have hScard : S.card = t ^ 3 := by
      change (Y \ X).toFinset.card = t ^ 3
      rw [← Set.ncard_eq_toFinset_card' (Y \ X)]
      exact hDiff
    have hpoints : ∀ p ∈ S, c p = 0 := by
      intro p hpS
      have hpYX : p ∈ Y \ X := by simpa [S] using hpS
      exact hY.1.1.1.1 p hpYX.1
    have hoff : ∀ p ∈ S, p ∉ X := by
      intro p hpS
      have hpYX : p ∈ Y \ X := by simpa [S] using hpS
      exact hpYX.2
    have hclosed : ∀ p ∈ S, conjLine Γ c X p ⊆ (S : Set V) := by
      intro p hpS
      have hpYX : p ∈ Y \ X := by simpa [S] using hpS
      have hp0 : c p = 0 := hY.1.1.1.1 p hpYX.1
      have hpX : p ∉ X := hpYX.2
      have hNY : conjLine Γ c X p ⊆ Y :=
        subset_of_isConjPlane hP hT c hdeg hreg hii hX.1 hY.1 hc hpYX.1 hpX
      have hNX : conjLine Γ c X p ⊆ Xᶜ :=
        conjLine_subset_sdiff hP hT c hdeg hreg hX hp0 hpX
      intro z hz
      have hzY : z ∈ Y := hNY hz
      have hzX : z ∉ X := hNX hz
      exact Set.mem_toFinset.mpr ⟨hzY, hzX⟩
    have hpart := card_conjLine_partition hP hT c hdeg hreg hX hpoints hoff hclosed
    have hdvd : t + 1 ∣ t ^ 3 := by
      rw [hScard] at hpart
      exact ⟨(S.image (fun p => conjLine Γ c X p)).card, by rw [hpart, Nat.mul_comm]⟩
    have ht : Nat.Coprime (t + 1) t := by
      simpa using (Nat.coprime_self_add_left (m := t) (n := 1)).mpr (by simp)
    have hcop : Nat.Coprime (t + 1) (t ^ 3) :=
      (Nat.coprime_pow_right_iff (by norm_num) (t + 1) t).mpr ht
    have hone : t + 1 = 1 := Nat.eq_one_of_dvd_coprimes hcop (dvd_refl (t + 1)) hdvd
    have ht2 : 2 ≤ t := two_le_t hP hT c hdeg
    omega
  · obtain ⟨a, b, ha0, hb0, hab, hIab⟩ := hline
    have haI : a ∈ X ∩ Y := by
      rw [hIab]
      exact mem_starLine_left ha0
    have hbI : b ∈ X ∩ Y := by
      rw [hIab]
      exact mem_starLine_right hb0
    exact ⟨a, b, ha0, dist_eq_four_of_mem_of_isOvoid hP hT hX.2 haI.1 hbI.1 hab,
      hIab⟩

theorem existsUnique_conjPlane_superset (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) (hii : TalliniCond Γ c)
    {X R : Set V} (hX : IsStarPlane Γ c X) (hR : IsStarLine Γ c R) (hRX : ¬ R ⊆ X)
    (hRc : ¬ ptPerp Γ c R ⊆ X) :
    ∃! Y, IsStarPlane Γ c Y ∧ R ⊆ Y ∧ IsConjPlane Γ c X Y := by
  classical
  have hRne : ∃ p, p ∈ R ∧ p ∉ X := by
    by_contra h
    apply hRX
    intro p hpR
    by_contra hpX
    exact h ⟨p, hpR, hpX⟩
  obtain ⟨p, hpR, hpX⟩ := hRne
  have hp : c p = 0 := color_zero_of_mem_isStarLine hR hpR
  have hNhyp : IsHypLine Γ c (conjLine Γ c X p) :=
    (isHypLine_conjLine hP hT c hdeg hreg hX hp hpX).1
  have hNstar : IsStarLine Γ c (conjLine Γ c X p) := IsHypLine.isStarLine hP hNhyp
  have hpN : p ∈ conjLine Γ c X p :=
    (isHypLine_conjLine hP hT c hdeg hreg hX hp hpX).2.1
  have hNperpX : ptPerp Γ c (conjLine Γ c X p) ⊆ X :=
    (isHypLine_conjLine hP hT c hdeg hreg hX hp hpX).2.2
  have hNR : conjLine Γ c X p ≠ R := by
    intro hEq
    apply hRc
    rw [← hEq]
    exact hNperpX
  have hinter : R ∩ conjLine Γ c X p = {p} := by
    ext q
    constructor
    · rintro ⟨hqR, hqN⟩
      rw [Set.mem_singleton_iff]
      by_contra hqp
      have hRq : R = starLine Γ c p q :=
        starLine_eq_of_isStarLine_of_mem hP hT hR hpR hqR (Ne.symm hqp)
      have hNq : conjLine Γ c X p = starLine Γ c p q :=
        starLine_eq_of_isStarLine_of_mem hP hT hNstar hpN hqN (Ne.symm hqp)
      exact hNR.symm (hRq.trans hNq.symm)
    · intro hq
      rw [Set.mem_singleton_iff] at hq
      subst hq
      exact ⟨hpR, hpN⟩
  obtain ⟨r, hrR, hrp⟩ := exists_mem_ne_of_isStarLine hR p
  obtain ⟨n, hnN, hnp⟩ := exists_mem_ne_of_isStarLine hNstar p
  have hnc : ¬ IsStarCollinear Γ c p r n := by
    rintro ⟨S, hS, hpS, hrS, hnS⟩
    have hSR : S = R := by
      have hSp : S = starLine Γ c p r :=
        starLine_eq_of_isStarLine_of_mem hP hT hS hpS hrS hrp.symm
      have hRp : R = starLine Γ c p r :=
        starLine_eq_of_isStarLine_of_mem hP hT hR hpR hrR hrp.symm
      exact hSp.trans hRp.symm
    have hnR : n ∈ R := by
      rw [← hSR]
      exact hnS
    have hnInt : n ∈ R ∩ conjLine Γ c X p := ⟨hnR, hnN⟩
    rw [hinter] at hnInt
    exact hnp (Set.mem_singleton_iff.mp hnInt)
  have hr : c r = 0 := color_zero_of_mem_isStarLine hR hrR
  have hn : c n = 0 := color_zero_of_mem_isStarLine hNstar hnN
  have hii' : TalliniCondPrime Γ c := talliniCondPrime_of_talliniCond hP hT c hdeg hreg hii
  obtain ⟨Y, hYstar, hpY, hrY, hnY⟩ := hii' p r n hp hr hn hnc
  have hRY : R ⊆ Y := by
    have hRpr : R = starLine Γ c p r :=
      starLine_eq_of_isStarLine_of_mem hP hT hR hpR hrR hrp.symm
    rw [hRpr]
    exact hYstar.1.1.2 p hpY r hrY hrp.symm
  have hNY : conjLine Γ c X p ⊆ Y := by
    have hNpn : conjLine Γ c X p = starLine Γ c p n :=
      starLine_eq_of_isStarLine_of_mem hP hT hNstar hpN hnN hnp.symm
    rw [hNpn]
    exact hYstar.1.1.2 p hpY n hnY hnp.symm
  have hconj : IsConjPlane Γ c X Y := by
    refine ⟨ptPerp Γ c (conjLine Γ c X p),
      (ptPerp_ptPerp_starLine hP hT c hdeg hreg hNstar).1, hNperpX, ?_⟩
    rw [(ptPerp_ptPerp_starLine hP hT c hdeg hreg hNstar).2]
    exact hNY
  refine ⟨Y, ⟨hYstar, hRY, hconj⟩, ?_⟩
  intro Z hZ
  obtain ⟨hZstar, hRZ, hZconj⟩ := hZ
  have hpZ : p ∈ Z := hRZ hpR
  have hNZ : conjLine Γ c X p ⊆ Z :=
    subset_of_isConjPlane hP hT c hdeg hreg hii hX hZstar hZconj hpZ hpX
  have hYZ : Y = Z :=
    eq_of_isStarPlane hP hT c hdeg hreg hYstar hZstar
      ⟨hpY, hpZ⟩ ⟨hrY, hRZ hrR⟩ ⟨hnY, hNZ hnN⟩ hnc
  exact hYZ.symm

theorem mem_conjNet_of_conjLine_subset (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) {X : Set V} (hX : IsStarPlane Γ c X)
    {p : V} (hp : c p = 0) (hpX : p ∉ X) {Y : Set V} (hY : IsStarPlane Γ c Y)
    (hNY : conjLine Γ c X p ⊆ Y) : Y ∈ conjNet Γ c X := by
  refine ⟨hY, ?_⟩
  have hNhyp : IsHypLine Γ c (conjLine Γ c X p) :=
    (isHypLine_conjLine hP hT c hdeg hreg hX hp hpX).1
  have hNstar : IsStarLine Γ c (conjLine Γ c X p) := IsHypLine.isStarLine hP hNhyp
  have hNperp : ptPerp Γ c (conjLine Γ c X p) ⊆ X :=
    (isHypLine_conjLine hP hT c hdeg hreg hX hp hpX).2.2
  refine ⟨ptPerp Γ c (conjLine Γ c X p),
    (ptPerp_ptPerp_starLine hP hT c hdeg hreg hNstar).1, hNperp, ?_⟩
  rw [(ptPerp_ptPerp_starLine hP hT c hdeg hreg hNstar).2]
  exact hNY

end ConjugacyD2

end CFSG.Geometry.GeneralizedQuadrangles
