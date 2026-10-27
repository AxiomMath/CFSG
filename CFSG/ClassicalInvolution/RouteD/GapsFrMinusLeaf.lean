module

public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusCross
public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusFix
public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusNodes
public import CFSG.ClassicalInvolution.RouteD.GapsPatternD
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
public import CFSG.ClassicalInvolution.Models.TwistedPairs
public import CFSG.ClassicalInvolution.RouteD.GapsChainConfig
public import CFSG.ClassicalInvolution.RouteD.GapsFrNodes
public import CFSG.ClassicalInvolution.RouteD.GapsOrthPairs
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedDNodes

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

section Leaf

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem leaf_commutes_beta {m : ℕ} (hm : 7 ≤ m) (c : TCtx p f .POmegaMinus m Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hshape : LocalShapeT p f 2 .POmegaMinus m Ω z)
    (hF : OrthCross (Subgroup.center (modelUniv .POmegaMinus m p f Fact.out).K)
      (fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus m p f Fact.out).D))
    {β : Subgroup G} {M : Subgroup G} (nd : DNodes p f (m - 1) Ω M)
    (h0 : nd.J ⟨0, by omega⟩ = K) (h1 : nd.J ⟨1, by omega⟩ = β)
    {W₀ : Subgroup G} {x₀ : G} (hW₀ : W₀ ∈ Ω) (hx₀ : IsClassicalMember p f W₀ x₀)
    (hW0 : ∀ a (h : a < m - 1), a ≤ 3 → Commutes (nd.J ⟨a, h⟩) W₀)
    {D N : Subgroup G} (hDΩ : D ∈ Ω) (hNΩ : N ∈ Ω) (hDW : Commutes D W₀) (hNW : Commutes N W₀)
    (hDK : Commutes D K) (hD2 : Commutes D (nd.J ⟨2, by omega⟩)) (hNK : Commutes N K)
    (hN2 : Commutes N (nd.J ⟨2, by omega⟩))
    (hDN : ∃ W, LinearBlockStandardPair (GaloisField p f) W D N) :
    Commutes N β := by
  classical
  have hΩ := c.hΩ
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f c.hp2
  obtain ⟨cx⟩ := exists_ctx_member c hsingle hshape hW₀ hx₀
  obtain ⟨W, hW⟩ := hDN
  have hDne : D ≠ N := ne_of_linearBlockStandardPair hW
  have hDNn : ¬ Commutes D N := not_commutes_of_linearBlockStandardPair hW
  obtain ⟨wN, hwN⟩ := hΩ.classical N hNΩ
  obtain ⟨wD, hwD⟩ := hΩ.classical D hDΩ
  have hmem : ∀ a (h : a < m - 1), a ≤ 3 → nd.J ⟨a, h⟩ ∈ centralizingMembers Ω {x₀} :=
    fun a h ha => mem_centralizingMembers_of_commutes (nd.mem _) hx₀.mem (hW0 a h ha)
  have a01 : DNodes.Adj (⟨0, by omega⟩ : Fin (m - 1)) ⟨1, by omega⟩ := by fr_idx
  have a12 : DNodes.Adj (⟨1, by omega⟩ : Fin (m - 1)) ⟨2, by omega⟩ := by fr_idx
  have a32 : DNodes.Adj (⟨3, by omega⟩ : Fin (m - 1)) ⟨2, by omega⟩ := by fr_idx
  have hK : K ∈ centralizingMembers Ω {x₀} := h0 ▸ hmem 0 (by omega) (by omega)
  have hβ : β ∈ centralizingMembers Ω {x₀} := h1 ▸ hmem 1 (by omega) (by omega)
  have hJ : nd.J ⟨2, by omega⟩ ∈ centralizingMembers Ω {x₀} := hmem 2 (by omega) (by omega)
  have hJ3 : nd.J ⟨3, by omega⟩ ∈ centralizingMembers Ω {x₀} := hmem 3 (by omega) (by omega)
  have hDx : D ∈ centralizingMembers Ω {x₀} := mem_centralizingMembers_of_commutes hDΩ hx₀.mem hDW
  have hNx : N ∈ centralizingMembers Ω {x₀} := mem_centralizingMembers_of_commutes hNΩ hx₀.mem hNW
  have hwK : IsClassicalMember p f K (nd.w ⟨0, by omega⟩) := h0 ▸ nd.cl _
  have hwβ : IsClassicalMember p f β (nd.w ⟨1, by omega⟩) := h1 ▸ nd.cl _
  have hKN : K ≠ N := fun e => by
    rw [← e] at hNK
    exact not_commutes_self_of_mem hΩ c.hK hNK
  have hJN : nd.J ⟨2, by omega⟩ ≠ N := fun e => by
    rw [← e] at hN2
    exact not_commutes_self_of_mem hΩ (nd.mem _) hN2
  have hKD : K ≠ D := fun e => by
    rw [← e] at hDK
    exact not_commutes_self_of_mem hΩ c.hK hDK
  have hJD : nd.J ⟨2, by omega⟩ ≠ D := fun e => by
    rw [← e] at hD2
    exact not_commutes_self_of_mem hΩ (nd.mem _) hD2
  refine cross_config cx hF (K := K) (β := β) (J := nd.J ⟨2, by omega⟩) (N := N) hK hβ hJ hNx
    hwK hwβ (nd.cl _) hwN ⟨?_, ?_, ?_, ?_⟩ ⟨?_, ?_, ?_, ?_⟩ ?_ ?_ hKN hNK hJN hN2 ?_ ?_ ?_
  · rw [← h0, ← h1]
    exact nd.ne_J hΩ (by simp)
  · rw [← h0, ← h1]
    exact nd.not_commutes_of_adj a01
  · exact nd.commute_w h2 _ _
  · rw [← h0]
    exact nd.conjSub_w h2 a01
  · rw [← h1]
    exact nd.ne_J hΩ (by simp)
  · rw [← h1]
    exact nd.not_commutes_of_adj a12
  · exact nd.commute_w h2 _ _
  · rw [← h1]
    exact nd.conjSub_w h2 a12
  · rw [← h0]
    exact nd.ne_J hΩ (by simp)
  · rw [← h0]
    exact nd.commutes_of_not_adj (by simp) (by fr_idx)
  ·
    refine ⟨nd.J ⟨3, by omega⟩, nd.w ⟨3, by omega⟩, hJ3, nd.cl _, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← h0]
      exact nd.ne_J hΩ (by simp)
    · exact nd.ne_J hΩ (by simp)
    · exact nd.commute_w h2 _ _
    · exact nd.commute_w h2 _ _
    · rw [← h0]
      exact nd.commutes_of_not_adj (by simp) (by fr_idx)
    · exact nd.not_commutes_of_adj a32
  ·
    refine ⟨D, wD, hDx, hwD, hKD.symm, hDne, ?_, ?_, hDK, hDNn⟩
    · exact hDK wD hwD.mem _ (h0 ▸ (nd.cl ⟨0, by omega⟩).mem)
    · exact standardPair_involutions_commute h2 hW hwD.mem hwN.mem hwD.orderOf_eq_two
        hwN.orderOf_eq_two
  ·
    refine ⟨D, wD, hDx, hwD, hJD.symm, hDne, ?_, ?_, hD2, hDNn⟩
    · exact hD2 wD hwD.mem _ (nd.cl ⟨2, by omega⟩).mem
    · exact standardPair_involutions_commute h2 hW hwD.mem hwN.mem hwD.orderOf_eq_two
        hwN.orderOf_eq_two

end Leaf

section ShortConj

variable {G : Type} [Group G]

theorem map_conj_eq_of_commute (w : G) (R : Subgroup G) (h : ∀ r ∈ R, Commute w r) :
    R.map (MulAut.conj w).toMonoidHom = R := by
  ext y
  constructor
  · rintro ⟨r, hr, rfl⟩
    have : (MulAut.conj w).toMonoidHom r = r := by
      show w * r * w⁻¹ = r
      rw [(h r hr).eq]
      group
    rw [this]
    exact hr
  · intro hy
    refine ⟨y, hy, ?_⟩
    show w * y * w⁻¹ = y
    rw [(h y hy).eq]
    group

theorem commutes_map_conj_of_commute (w : G) (A B : Subgroup G) (hB : ∀ b ∈ B, Commute w b)
    (hAB : Commutes A B) : Commutes (A.map (MulAut.conj w).toMonoidHom) B := by
  rintro _ ⟨a, ha, rfl⟩ b hb
  show w * a * w⁻¹ * b = b * (w * a * w⁻¹)
  have h1 : w⁻¹ * b = b * w⁻¹ := ((hB b hb).inv_left).eq
  calc w * a * w⁻¹ * b = w * a * (w⁻¹ * b) := by group
    _ = w * a * (b * w⁻¹) := by rw [h1]
    _ = w * (a * b) * w⁻¹ := by group
    _ = w * (b * a) * w⁻¹ := by rw [hAB a ha b hb]
    _ = (w * b) * a * w⁻¹ := by group
    _ = (b * w) * a * w⁻¹ := by rw [(hB b hb).eq]
    _ = b * (w * a * w⁻¹) := by group

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

theorem commute_twShortRoot_rootSL2 {a b' : ℕ} (ha : a < n - 1) (hb : b' < n - 1)
    (hab : a ≠ b') (k : Fin (n - 1)) (hka : k.val ≠ a) (hkb : k.val ≠ b') (s t u : Bool)
    (p : Fin 2 → K) :
    ∀ y ∈ rootSL2 (minusFrame n b c).toHypFrame a b' ha hb hab s t,
      Commute (twShortRoot n hirr k u (.ofAdd p)) y := by
  have hij : (⟨a, ha⟩ : Fin (n - 1)) ≠ ⟨b', hb⟩ := fun h => hab (congrArg Fin.val h)
  have hka' : k ≠ ⟨a, ha⟩ := fun h => hka (congrArg Fin.val h)
  have hkb' : k ≠ ⟨b', hb⟩ := fun h => hkb (congrArg Fin.val h)
  have hle : rootSL2 (minusFrame n b c).toHypFrame a b' ha hb hab s t ≤
      Subgroup.centralizer ({twShortRoot n hirr k u (.ofAdd p)} : Set _) := by
    unfold rootSL2
    rw [longSL2_range_eq_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨x, rfl⟩
      obtain ⟨a', rfl⟩ := Multiplicative.ofAdd.surjective x
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (commute_longRoot_twShortRoot_of_ne n hirr hij hka' hkb' s t u a' p).eq
    · rintro _ ⟨x, rfl⟩
      obtain ⟨a', rfl⟩ := Multiplicative.ofAdd.surjective x
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (commute_longRoot_twShortRoot_of_ne n hirr hij.symm hkb' hka' (!t) (!s) u a' p).eq
  intro y hy
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hy)).symm

end Short

section LeafN

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem leafN_fixed {s : ℕ} (hs : 4 ≤ s) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
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
    ∀ y ∈ (rootSL2 (minusHyp (s + 5) (minusCoeffs p f).1 (minusCoeffs p f).2) (s + 1) (s + 2)
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
  have hFn := rootSL2_conj_mem_gen hq4 cq Fr (a := s + 1) (b := s + 2) (by omega) (by omega)
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
  have hFcomm : ∀ a (ha : a + 2 ≤ s + 1) , Commutes N (nd.J ⟨a + 2, by omega⟩) := by
    intro a ha
    refine (c.commutes_iff_fund hNz (hmemz _ _ (by omega)) hFn hNimg (hnode a (by omega))).mpr ?_
    exact (commutes_rootSL2_disjoint Fr (a := s + 1) (b := s + 2) (c := a) (d := a + 1)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) true false true false).conjSub x
  have hstd : ∃ W, LinearBlockStandardPair (GaloisField p f) W M N := by
    have hm3 : 3 ≤ s + 5 - 1 := by omega
    have hA : dNode hm3 Fr x ⟨s + 1, by omega⟩ = (rootSL2 Fr (s + 1) (s + 2) (by omega) (by omega)
        (by omega) true false).map (MulAut.conj x).toMonoidHom := by
      rw [dNode_lt hm3 Fr x ⟨s + 1, by omega⟩ (by show s + 1 + 1 < s + 5 - 1; omega)]
    cases tM with
    | false =>
      obtain ⟨W, hW⟩ := stdPair_dNode_minus (p := p) (f := f) (m := s + 5) (by omega) hp2 x
        (a := ⟨s + 1, by omega⟩) (b := ⟨s + 2, by omega⟩)
        (Or.inl ⟨rfl, by show s + 2 + 1 < s + 5 - 1; omega⟩)
      have hB : dNode hm3 Fr x ⟨s + 2, by omega⟩ = (rootSL2 Fr (s + 2) (s + 3) (by omega)
          (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom := by
        rw [dNode_lt hm3 Fr x ⟨s + 2, by omega⟩ (by show s + 2 + 1 < s + 5 - 1; omega)]
      rw [hA, hB] at hW
      exact c.stdPair_of_fund hMz hNz (linearBlockStandardPair_symm hW) hMimg hNimg
    | true =>
      obtain ⟨W, hW⟩ := stdPair_dNode_minus (p := p) (f := f) (m := s + 5) (by omega) hp2 x
        (a := ⟨s + 1, by omega⟩) (b := ⟨s + 3, by omega⟩)
        (Or.inr ⟨by show s + 1 + 3 = s + 5 - 1; omega, by show s + 3 + 1 = s + 5 - 1; omega⟩)
      have hB : dNode hm3 Fr x ⟨s + 3, by omega⟩ = (rootSL2 Fr (s + 2) (s + 3) (by omega)
          (by omega) (by omega) true true).map (MulAut.conj x).toMonoidHom := by
        rw [dNode_last hm3 Fr x ⟨s + 3, by omega⟩ (by show ¬ s + 3 + 1 < s + 5 - 1; omega)]
        congr 1
      rw [hA, hB] at hW
      exact c.stdPair_of_fund hMz hNz (linearBlockStandardPair_symm hW) hMimg hNimg
  have h5 : ∀ a (h : a < s + 5 - 1), a ≤ 3 → Commutes (nd.J ⟨a, h⟩) (nd.J ⟨5, by omega⟩) := by
    intro a h ha
    refine nd.commutes_of_not_adj (a := ⟨a, h⟩) (b := ⟨5, by omega⟩)
      (fin_ne_of_val_ne (by show a ≠ 5; omega)) ?_
    simp only [DNodes.adj_def]
    omega
  have hβN : Commutes N β :=
    leaf_commutes_beta (by omega) c hsingle hshape hF nd h0 h1 (nd.mem _) (nd.cl _) h5 hMΩ hNz.1
      (nd.commK ⟨5, by omega⟩) (hFcomm 3 (by omega)) (h0 ▸ nd.commK ⟨0, by omega⟩)
      (nd.commK ⟨2, by omega⟩) hNK' (hFcomm 0 (by omega)) hstd
  intro y hy
  have hNt : N ≤ Subgroup.centralizer ({t} : Set G) := fun n hn =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hβN n hn t ht.mem)
  exact (locAut_fixed_iff hΩ c.hP1 htz hNz).mp hNt (c.d.ψ y) (by rw [hNimg]; exact ⟨y, hy, rfl⟩)

end LeafN

section LeafW

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem leafW_fixed {s : ℕ} (hs : 4 ≤ s) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
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
