module

public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusSmallWeyl
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted

local macro "fr_idx" : tactic =>
  `(tactic| first
    | (simp [DNodes.adj_def]; done)
    | (simp [DNodes.adj_def]; omega)
    | (simp; done)
    | (simp; omega)
    | omega)

section ShortConj

variable {G : Type} [Group G]



private theorem map_conj_mul (x w : G) (A : Subgroup G) :
    A.map (MulAut.conj (x * w)).toMonoidHom =
      (A.map (MulAut.conj w).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext y
  show x * w * y * (x * w)⁻¹ = x * (w * y * w⁻¹) * x⁻¹
  group

end ShortConj

section Short

variable {K : Type} [Field K] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {n : ℕ}


end Short

section LeafBridge

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem leafBridge_fixed {s : ℕ} (hs : 3 ≤ s) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (c : TCtx p f .POmegaMinus (s + 5) Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 .POmegaMinus (s + 5) Ω z) {β : Subgroup G} {t : G}
    (ht : IsClassicalMember p f β t) (htz : t * z * t⁻¹ = z) {M : Subgroup G} (hMΩ : M ∈ Ω)
    (hMz : M ∈ centralizingMembers Ω {z}) (nd : DNodes p f (s + 5 - 1) Ω M)
    (h0 : nd.J ⟨0, by omega⟩ = K) (h1 : nd.J ⟨1, by omega⟩ = β)
    (x : spinGroup (quadMinus (s + 5) (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2))
    (tM : Bool)
    (hnode : ∀ a (ha : a ≤ s), locImg Ω z (nd.J ⟨a + 2, by omega⟩) =
      ((rootSL2 (minusHyp (s + 5) (minusCoeffs p f).1 (minusCoeffs p f).2) a (a + 1) (by omega)
        (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom).map c.d.ψ)
    (hMimg : locImg Ω z M =
      ((rootSL2 (minusHyp (s + 5) (minusCoeffs p f).1 (minusCoeffs p f).2) (s + 2) (s + 3)
        (by omega) (by omega) (by omega) true tM).map (MulAut.conj x).toMonoidHom).map c.d.ψ) :
    ∀ y ∈ (rootSL2 (minusHyp (s + 5) (minusCoeffs p f).1 (minusCoeffs p f).2) 2 (s + 2)
      (by omega) (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom,
      locAut c.hΩ.conjInvariant htz (c.d.ψ y) = c.d.ψ y := by
  classical
  have hΩ := c.hΩ
  have hirr := minusCoeffs_irr p f
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · subst h
      simp at hq
    · exact h
  have hadm : StatedLieAdmissible .POmegaMinus (s + 5) p f := ⟨Fact.out, hf1, by omega⟩
  have hq4 : 4 ≤ p ^ f := by omega
  have cq := Exotic.centralQuot_minus hp2 hq hadm
  have hF := orthCross_minusDatum (f := f) hp2 (by omega : 5 ≤ s + 5) hq
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  set Fr := minusHyp (s + 5) (minusCoeffs p f).1 (minusCoeffs p f).2 with hFr
  have hFn := rootSL2_conj_mem_gen hq4 cq Fr (a := 2) (b := s + 2) (by omega) (by omega)
    (by omega) true false x
  obtain ⟨N, hNz, hNK, hNQ, hNimg⟩ := c.exists_member_of_fund hFn
  have hNK' : Commutes N K := commutes_symm (c.commutes_K_of_ne hNz hNK)
  have hKJ : ∀ a (h : a < s + 5 - 1), 2 ≤ a → Commutes K (nd.J ⟨a, h⟩) := by
    intro a h ha
    rw [← h0]
    exact nd.commutes_of_not_adj (fin_ne_of_val_ne (by simp; omega)) (by fr_idx)
  have hmemz : ∀ a (h : a < s + 5 - 1), 2 ≤ a → nd.J ⟨a, h⟩ ∈ centralizingMembers Ω {z} :=
    fun a h ha => mem_centralizingMembers_of_commutes (nd.mem _) c.hz.mem
      (commutes_symm (hKJ a h ha))
  have hFcomm : ∀ a (h : a + 2 < s + 5 - 1), (a = 0 ∨ a = 3) → Commutes N (nd.J ⟨a + 2, h⟩) := by
    intro a h ha
    refine (c.commutes_iff_fund hNz (hmemz _ _ (by omega)) hFn hNimg
      (hnode a (by omega))).mpr ?_
    rcases ha with rfl | rfl
    · exact (commutes_rootSL2_disjoint Fr (a := 2) (b := s + 2) (c := 0) (d := 1)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) true false true false).conjSub x
    · exact (commutes_rootSL2_disjoint Fr (a := 2) (b := s + 2) (c := 3) (d := 4)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) true false true false).conjSub x
  have hstd : ∃ W, LinearBlockStandardPair (GaloisField p f) W M N := by
    obtain ⟨W, hW⟩ := stdPair_bridge_minus (p := p) (f := f) hs hp2 x tM
    exact c.stdPair_of_fund hMz hNz (linearBlockStandardPair_symm hW) hMimg hNimg
  have h5 : ∀ a (h : a < s + 5 - 1), a ≤ 3 → Commutes (nd.J ⟨a, h⟩) (nd.J ⟨5, by omega⟩) := by
    intro a h ha
    refine nd.commutes_of_not_adj (a := ⟨a, h⟩) (b := ⟨5, by omega⟩)
      (fin_ne_of_val_ne (by show a ≠ 5; omega)) ?_
    simp only [DNodes.adj_def]
    omega
  have hβN : Commutes N β :=
    leaf_commutes_beta (by omega) c hsingle hshape hF nd h0 h1 (nd.mem _) (nd.cl _) h5 hMΩ hNz.1
      (nd.commK ⟨5, by omega⟩) (hFcomm 3 (by omega) (Or.inr rfl)) (h0 ▸ nd.commK ⟨0, by omega⟩)
      (nd.commK ⟨2, by omega⟩) hNK' (hFcomm 0 (by omega) (Or.inl rfl)) hstd
  intro y hy
  have hNt : N ≤ Subgroup.centralizer ({t} : Set G) := fun n hn =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hβN n hn t ht.mem)
  exact (locAut_fixed_iff hΩ c.hP1 htz hNz).mp hNt (c.d.ψ y) (by rw [hNimg]; exact ⟨y, hy, rfl⟩)

end LeafBridge

section LeafW

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem leafW_fixed_ge3 {s : ℕ} (hs : 3 ≤ s) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (c : TCtx p f .POmegaMinus (s + 5) Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 .POmegaMinus (s + 5) Ω z) {β : Subgroup G} {t : G}
    (ht : IsClassicalMember p f β t) (htz : t * z * t⁻¹ = z) {M : Subgroup G} (hMΩ : M ∈ Ω)
    (hMz : M ∈ centralizingMembers Ω {z}) (nd : DNodes p f (s + 5 - 1) Ω M)
    (h0 : nd.J ⟨0, by omega⟩ = K) (h1 : nd.J ⟨1, by omega⟩ = β)
    (x : spinGroup (quadMinus (s + 5) (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2))
    (tM : Bool)
    (hnode : ∀ a (ha : a ≤ s), locImg Ω z (nd.J ⟨a + 2, by omega⟩) =
      ((rootSL2 (minusHyp (s + 5) (minusCoeffs p f).1 (minusCoeffs p f).2) a (a + 1) (by omega)
        (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom).map c.d.ψ)
    (hMimg : locImg Ω z M =
      ((rootSL2 (minusHyp (s + 5) (minusCoeffs p f).1 (minusCoeffs p f).2) (s + 2) (s + 3)
        (by omega) (by omega) (by omega) true tM).map (MulAut.conj x).toMonoidHom).map c.d.ψ)
    (w : Fin 2 → GaloisField p f) :
    ∀ y ∈ (rootSL2 (minusHyp (s + 5) (minusCoeffs p f).1 (minusCoeffs p f).2) 3 4 (by omega)
      (by omega) (by omega) true false).map (MulAut.conj (x * twShortRoot (s + 5)
        (minusCoeffs_irr p f) ⟨4, by omega⟩ true (.ofAdd w))).toMonoidHom,
      locAut c.hΩ.conjInvariant htz (c.d.ψ y) = c.d.ψ y := by
  classical
  have hΩ := c.hΩ
  have hirr := minusCoeffs_irr p f
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · subst h
      simp at hq
    · exact h
  have hadm : StatedLieAdmissible .POmegaMinus (s + 5) p f := ⟨Fact.out, hf1, by omega⟩
  have hq4 : 4 ≤ p ^ f := by omega
  have cq := Exotic.centralQuot_minus hp2 hq hadm
  have hF := orthCross_minusDatum (f := f) hp2 (by omega : 5 ≤ s + 5) hq
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  set Fr := minusHyp (s + 5) (minusCoeffs p f).1 (minusCoeffs p f).2 with hFr
  set Xw := twShortRoot (s + 5) hirr (⟨4, by omega⟩ : Fin (s + 5 - 1)) true (.ofAdd w) with hXw
  have hFw := rootSL2_conj_mem_gen hq4 cq Fr (a := 3) (b := 4) (by omega) (by omega)
    (by omega) true false (x * Xw)
  obtain ⟨N, hNz, hNK, hNQ, hNimg⟩ := c.exists_member_of_fund hFw
  have hNK' : Commutes N K := commutes_symm (c.commutes_K_of_ne hNz hNK)
  have hKJ : ∀ a (h : a < s + 5 - 1), 2 ≤ a → Commutes K (nd.J ⟨a, h⟩) := by
    intro a h ha
    rw [← h0]
    exact nd.commutes_of_not_adj (fin_ne_of_val_ne (by simp; omega)) (by fr_idx)
  have hmemz : ∀ a (h : a < s + 5 - 1), 2 ≤ a → nd.J ⟨a, h⟩ ∈ centralizingMembers Ω {z} :=
    fun a h ha => mem_centralizingMembers_of_commutes (nd.mem _) c.hz.mem
      (commutes_symm (hKJ a h ha))
  have hXc : ∀ {a b' : ℕ} (ha : a < s + 5 - 1) (hb : b' < s + 5 - 1) (hab : a ≠ b'), a ≠ 4 →
      b' ≠ 4 → ∀ (sg tg : Bool), ∀ y ∈ rootSL2 Fr a b' ha hb hab sg tg, Commute Xw y :=
    fun ha hb hab ha4 hb4 sg tg =>
      commute_twShortRoot_rootSL2 hirr ha hb hab ⟨4, by omega⟩ (fun e => ha4 e.symm)
        (fun e => hb4 e.symm) sg tg true w
  have hNJ2 : Commutes N (nd.J ⟨2, by omega⟩) := by
    refine (c.commutes_iff_fund hNz (hmemz _ _ (by omega)) hFw hNimg (hnode 0 (by omega))).mpr ?_
    rw [map_conj_mul]
    exact (commutes_map_conj_of_commute Xw _ _ (hXc (a := 0) (b' := 1) (by omega) (by omega)
      (by omega) (by omega) (by omega) true false) (commutes_rootSL2_disjoint Fr (a := 3) (b := 4)
      (c := 0) (d := 1)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) true false true false)).conjSub x
  have hNM : Commutes N M := by
    refine (c.commutes_iff_fund hNz hMz hFw hNimg hMimg).mpr ?_
    rw [map_conj_mul]
    exact (commutes_map_conj_of_commute Xw _ _ (hXc (a := s + 2) (b' := s + 3) (by omega)
      (by omega) (by omega) (by omega) (by omega) true tM) (commutes_rootSL2_disjoint Fr (a := 3)
      (b := 4) (c := s + 2)
      (d := s + 3) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) true false true tM)).conjSub x
  have hstd : ∃ W, LinearBlockStandardPair (GaloisField p f) W (nd.J ⟨4, by omega⟩) N := by
    obtain ⟨W₁, hW₁⟩ := linearBlockStandardPair_minusDatum hirr h2 (by omega : 4 ≤ s + 5)
      (i := (⟨2, by omega⟩ : Fin (s + 5 - 1))) (j := (⟨3, by omega⟩ : Fin (s + 5 - 1)))
      (by show 2 + 1 = 3; omega) (by show 3 + 1 < s + 5 - 1; omega)
    rw [rankOne_minusDatum_of_lt hirr (by show 2 + 1 < s + 5 - 1; omega),
      rankOne_minusDatum_of_lt hirr (by show 3 + 1 < s + 5 - 1; omega)] at hW₁
    have hW₂ := CFSG.ClassicalInvolution.ModelFacts.linearBlockStandardPair_map_conj hW₁ Xw
    rw [map_conj_eq_of_commute Xw (rootSL2 Fr 2 3 (by omega) (by omega) (by omega) true false)
      (hXc (a := 2) (b' := 3) (by omega) (by omega) (by omega) (by omega) (by omega) true
        false)] at hW₂
    have hW₃ := CFSG.ClassicalInvolution.ModelFacts.linearBlockStandardPair_map_conj hW₂ x
    rw [map_conj_mul] at hNimg
    exact c.stdPair_of_fund (hmemz 4 (by omega) (by omega)) hNz hW₃ (hnode 2 (by omega)) hNimg
  have hβN : Commutes N β := by
    obtain ⟨xM, hxM⟩ := hΩ.classical M hMΩ
    refine leaf_commutes_beta (by omega) c hsingle hshape
      (orthCross_minusDatum (f := f) hp2 (by omega : 5 ≤ s + 5) hq) nd h0 h1 hMΩ hxM
      (fun a h ha => commutes_symm (nd.commK ⟨a, h⟩)) (nd.mem _) hNz.1
      (commutes_symm (nd.commK ⟨4, by omega⟩)) hNM ?_ ?_ hNK' hNJ2 hstd
    · rw [← h0]
      exact nd.commutes_of_not_adj (fin_ne_of_val_ne (by simp)) (by fr_idx)
    · exact nd.commutes_of_not_adj (fin_ne_of_val_ne (by simp)) (by fr_idx)
  intro y hy
  have hNt : N ≤ Subgroup.centralizer ({t} : Set G) := fun n hn =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hβN n hn t ht.mem)
  exact (locAut_fixed_iff hΩ c.hP1 htz hNz).mp hNt (c.d.ψ y) (by rw [hNimg]; exact ⟨y, hy, rfl⟩)

end LeafW

end CFSG.ClassicalInvolution.RouteD.Gaps
