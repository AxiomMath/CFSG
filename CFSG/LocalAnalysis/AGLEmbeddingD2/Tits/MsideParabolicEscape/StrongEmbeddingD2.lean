module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.StrongCriterion

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbeddingD2

section OmegaCenter

variable {G : Type*} [Group G]

def omegaCenter (p : ℕ) (Y : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ Y ∧ (∀ y ∈ Y, x * y = y * x) ∧ x ^ p = 1}
  one_mem' := ⟨Y.one_mem, fun y _ => by simp, one_pow p⟩
  mul_mem' := by
    rintro a b ⟨haY, hac, hap⟩ ⟨hbY, hbc, hbp⟩
    refine ⟨Y.mul_mem haY hbY, fun y hy => ?_, ?_⟩
    · rw [mul_assoc, hbc y hy, ← mul_assoc, hac y hy, mul_assoc]
    · have hcomm : Commute a b := (hbc a haY).symm
      rw [hcomm.mul_pow, hap, hbp, one_mul]
  inv_mem' := by
    rintro a ⟨haY, hac, hap⟩
    refine ⟨Y.inv_mem haY, fun y hy => ?_, ?_⟩
    · have : Commute a y := hac y hy
      exact this.inv_left
    · rw [inv_pow, hap, inv_one]

theorem omegaCenter_le (p : ℕ) (Y : Subgroup G) : omegaCenter p Y ≤ Y := fun _ hx => hx.1

theorem isElemAbelian_omegaCenter (p : ℕ) (Y : Subgroup G) : IsElemAbelian p (omegaCenter p Y) := by
  refine ⟨isMulCommutative_iff.mpr fun a b => ?_, fun x hx => hx.2.2⟩
  apply Subtype.ext
  exact (b.2.2.1 a a.2.1).symm

theorem conj_mem_omegaCenter {p : ℕ} {Y : Subgroup G} {n h : G}
    (hn : n ∈ Subgroup.normalizer (Y : Set G)) (hh : h ∈ omegaCenter p Y) :
    n * h * n⁻¹ ∈ omegaCenter p Y := by
  obtain ⟨hY, hc, hp⟩ := hh
  refine ⟨(Subgroup.mem_normalizer_iff.mp hn h).mp hY, fun y hy => ?_, ?_⟩
  · have hn' : n⁻¹ ∈ Subgroup.normalizer (Y : Set G) := (Subgroup.normalizer (Y : Set G)).inv_mem hn
    have hy' : n⁻¹ * y * n ∈ Y := by
      have := (Subgroup.mem_normalizer_iff.mp hn' y).mp hy
      simpa using this
    have h1 := hc _ hy'
    calc n * h * n⁻¹ * y = n * (h * (n⁻¹ * y * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * y * n) * h) * n⁻¹ := by rw [h1]
      _ = y * (n * h * n⁻¹) := by group
  · rw [conj_pow, hp]
    simp

theorem normalizer_le_normalizer_omegaCenter (p : ℕ) (Y : Subgroup G) :
    Subgroup.normalizer (Y : Set G) ≤ Subgroup.normalizer (omegaCenter p Y : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact conj_mem_omegaCenter hn
  · intro hh
    have hn' : n⁻¹ ∈ Subgroup.normalizer (Y : Set G) := (Subgroup.normalizer (Y : Set G)).inv_mem hn
    have := conj_mem_omegaCenter (p := p) hn' hh
    simpa [mul_assoc] using this

variable [Finite G]

theorem omegaCenter_ne_bot {p : ℕ} (hp : p.Prime) {Y : Subgroup G} (hY : IsPGroup p Y)
    (hY1 : Y ≠ ⊥) : omegaCenter p Y ≠ ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have : Nontrivial Y := (Subgroup.nontrivial_iff_ne_bot Y).mpr hY1
  have hcen : Nontrivial (Subgroup.center ↥Y) := hY.center_nontrivial
  have hZp : IsPGroup p (Subgroup.center ↥Y) := hY.to_subgroup _
  have hdvd : p ∣ Nat.card (Subgroup.center ↥Y) := by
    rcases hZp.card_eq_or_dvd with h | h
    · exfalso
      have := Nat.card_eq_one_iff_unique.mp h
      obtain ⟨a, b, hab⟩ := hcen.exists_pair_ne
      exact hab (this.1.elim a b)
    · exact h
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥Y)) p hdvd
  have hzp : ((z : ↥Y) : G) ^ p = 1 := by
    have h1 : z ^ p = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
    have h2 : (z : ↥Y) ^ p = 1 := by
      have := congrArg (fun w : ↥(Subgroup.center ↥Y) => (w : ↥Y)) h1
      simpa using this
    have := congrArg (fun w : ↥Y => (w : G)) h2
    simpa using this
  have hz1 : ((z : ↥Y) : G) ≠ 1 := by
    intro h1
    have : z = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      simpa using h1
    rw [this, orderOf_one] at hz
    exact hp.one_lt.ne hz
  intro hbot
  have hmem : ((z : ↥Y) : G) ∈ omegaCenter p Y := by
    refine ⟨(z : ↥Y).2, fun y hy => ?_, hzp⟩
    have := Subgroup.mem_center_iff.mp z.2 ⟨y, hy⟩
    have := congrArg Subtype.val this
    simpa using this.symm
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hz1 hmem

end OmegaCenter

variable {G : Type} [Group G] [Finite G]

theorem D2Escape.normalizer_le_of_le_M_of_order_p {p : ℕ} {P : Sylow p G}
    {M A H R : Subgroup G} (h : D2Escape p P M A H R)
    (h1 : ∀ x ∈ M, orderOf x = p →
      Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) ≤ M)
    {Y : Subgroup G} (hYM : Y ≤ M) (hY : IsPGroup p Y) (hY1 : Y ≠ ⊥) :
    Subgroup.normalizer (Y : Set G) ≤ M := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  refine (normalizer_le_normalizer_omegaCenter p Y).trans ?_
  set X := omegaCenter p Y with hXdef
  have hXY : X ≤ Y := omegaCenter_le p Y
  have hXe : IsElemAbelian p X := isElemAbelian_omegaCenter p Y
  have hX1 : X ≠ ⊥ := omegaCenter_ne_bot hp hY hY1
  have hXp : IsPGroup p X := hY.to_le hXY
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p)).mp hXp
  by_cases hk2 : 2 ≤ k
  · exact h.normalizer_le_of_le_M (hXY.trans hYM) hXp
      (hk2.trans (le_pRank_of_isElemAbelian hp hXe hk))
  · have hk1 : k = 1 := by
      by_contra hne
      have : k = 0 := by omega
      apply hX1
      refine Subgroup.eq_bot_of_card_eq _ ?_
      rw [hk, this, pow_zero]
    subst hk1
    obtain ⟨x, hxX⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hX1
    have hxo : orderOf (x : G) = p := by
      refine orderOf_eq_prime (hXe.2 x x.2) ?_
      intro h1'
      apply hxX
      exact Subtype.ext h1'
    have hzp : Subgroup.zpowers (x : G) = X := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr x.2) ?_
      rw [Nat.card_zpowers, hxo, hk, pow_one]
    rw [← hzp]
    exact h1 x (hYM (hXY x.2)) hxo

omit [Finite G] in
theorem conj_mem_centralizer_of_mem_normalizer_zpowers {x n c : G}
    (hn : n ∈ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G))
    (hc : c ∈ Subgroup.centralizer ({x} : Set G)) :
    n * c * n⁻¹ ∈ Subgroup.centralizer ({x} : Set G) := by
  have hn' : n⁻¹ ∈ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) :=
    (Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G)).inv_mem hn
  have hy : n⁻¹ * x * n ∈ Subgroup.zpowers x := by
    have := (Subgroup.mem_normalizer_iff.mp hn' x).mp (Subgroup.mem_zpowers x)
    simpa using this
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hcx : Commute c x := (Subgroup.mem_centralizer_iff.mp hc x (Set.mem_singleton x)).symm
  have hcy : c * (n⁻¹ * x * n) = (n⁻¹ * x * n) * c := by
    rw [← hk]
    exact hcx.zpow_right k
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  subst hz
  calc z * (n * c * n⁻¹) = n * ((n⁻¹ * z * n) * c) * n⁻¹ := by group
    _ = n * (c * (n⁻¹ * z * n)) * n⁻¹ := by rw [hcy]
    _ = n * c * n⁻¹ * z := by group

omit [Finite G] in
theorem mem_normalizer_map_subtype {N : Subgroup G} {F : Subgroup N} {a : N}
    (ha : a ∈ Subgroup.normalizer (F : Set N)) :
    (a : G) ∈ Subgroup.normalizer ((F.map N.subtype : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at ha ⊢
  intro g
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨a * f * a⁻¹, (ha f).mp hf, by simp⟩
  · rintro ⟨f, hf, hfg⟩
    have hgN : g ∈ N := by
      have : g = (a : G)⁻¹ * (f : G) * a := by
        have h1 : (f : G) = (a : G) * g * (a : G)⁻¹ := hfg
        rw [h1]; group
      rw [this]
      exact N.mul_mem (N.mul_mem (N.inv_mem a.2) f.2) a.2
    have hg' : a * (⟨g, hgN⟩ : N) * a⁻¹ ∈ F := by
      have : a * (⟨g, hgN⟩ : N) * a⁻¹ = f := by
        apply Subtype.ext
        simpa using hfg.symm
      rw [this]; exact hf
    exact ⟨⟨g, hgN⟩, (ha _).mpr hg', rfl⟩

theorem D2Escape.normalizer_zpowers_le_of_centralizer_le {p : ℕ} {P : Sylow p G}
    {M A H R : Subgroup G} (h : D2Escape p P M A H R) {x : G}
    (hC : Subgroup.centralizer ({x} : Set G) ≤ M)
    (hrank : 2 ≤ pRank p (Subgroup.centralizer ({x} : Set G))) :
    Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) ≤ M := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  set C := Subgroup.centralizer ({x} : Set G) with hCdef
  set N := Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) with hNdef
  have hCN : C ≤ N := centralizer_singleton_le_normalizer_zpowers x
  have hnormal : (C.subgroupOf N).Normal :=
    ⟨fun c hc n => by
      rw [Subgroup.mem_subgroupOf] at hc ⊢
      exact conj_mem_centralizer_of_mem_normalizer_zpowers n.2 hc⟩
  obtain ⟨E, hEC, hEe, hEcard⟩ := pRank_attained p hp C
  have hE2 : 2 ≤ pRank p E := hrank.trans (le_pRank_of_isElemAbelian hp hEe hEcard)
  have hEp : IsPGroup p E := fun y => ⟨1, Subtype.ext (by simpa using hEe.2 y y.2)⟩
  have hE'' : IsPGroup p ((E.subgroupOf N).subgroupOf (C.subgroupOf N)) :=
    (hEp.comap_subtype (K := N)).comap_subtype (K := C.subgroupOf N)
  obtain ⟨F, hEF⟩ := hE''.exists_le_sylow
  have hfr := Sylow.normalizer_sup_eq_top F
  intro n hn
  have hmem : (⟨n, hn⟩ : N) ∈ Subgroup.normalizer
      ((F.map (C.subgroupOf N).subtype : Subgroup N) : Set N) ⊔ C.subgroupOf N := by
    rw [hfr]; exact Subgroup.mem_top _
  obtain ⟨a, ha, c, hc, hac⟩ := Subgroup.mem_sup_of_normal_right.mp hmem
  have hcG : (c : G) ∈ C := Subgroup.mem_subgroupOf.mp hc
  set F'' : Subgroup G := (F.map (C.subgroupOf N).subtype).map N.subtype with hF''
  have hF''C : F'' ≤ C := by
    rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    exact Subgroup.mem_subgroupOf.mp f.2
  have hF''p : IsPGroup p F'' := (F.isPGroup'.map _).map _
  have hEF'' : E ≤ F'' := by
    intro e he
    have heC : e ∈ C := hEC he
    have heN : e ∈ N := hCN heC
    refine ⟨⟨e, heN⟩, ⟨⟨⟨e, heN⟩, Subgroup.mem_subgroupOf.mpr heC⟩, hEF ?_, rfl⟩, rfl⟩
    exact he
  have hrank'' : 2 ≤ pRank p F'' := hE2.trans (pRank_mono p hp hEF'')
  have hnorm : Subgroup.normalizer (F'' : Set G) ≤ M :=
    h.normalizer_le_of_le_M (hF''C.trans hC) hF''p hrank''
  have haM : (a : G) ∈ M := hnorm (mem_normalizer_map_subtype ha)
  have : n = (a : G) * (c : G) := by
    have := congrArg (fun w : N => (w : G)) hac
    simpa using this.symm
  rw [this]
  exact M.mul_mem haM (hC hcG)

theorem D2Escape.stronglyEmbedded_of_order_p {p : ℕ} {P : Sylow p G} {M A H R : Subgroup G}
    (h : D2Escape p P M A H R) (hM : M ≠ ⊤)
    (h1 : ∀ x ∈ M, orderOf x = p →
      Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) ≤ M) :
    GLBStronglyEmbedded p M := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  refine stronglyEmbedded_of_normalizer_le hp hM P h.sylow_le ?_ fun Y hYM hY hY1 =>
    D2Escape.normalizer_le_of_le_M_of_order_p h h1 hYM hY hY1
  intro hPbot
  have hAp : IsPGroup p A := h.isPGroup.to_le h.A_le
  obtain ⟨m, hm⟩ := exists_conjugate_le_sylow_of_le p P h.sylow_le h.A_le_M hAp
  have hcard : Nat.card (A.map (MulAut.conj (m : G)).toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj (m : G)).injective, h.card_A]
  rw [hPbot, le_bot_iff] at hm
  rw [hm, Subgroup.card_bot] at hcard
  have := Nat.one_lt_pow (by norm_num : (2 : ℕ) ≠ 0) hp.one_lt
  omega

theorem D2Escape.stronglyEmbedded_of_centralizers {p : ℕ} {P : Sylow p G}
    {M A H R : Subgroup G} (h : D2Escape p P M A H R) (hM : M ≠ ⊤)
    (hC : ∀ x ∈ M, orderOf x = p → Subgroup.centralizer ({x} : Set G) ≤ M)
    (hrank : ∀ x ∈ M, orderOf x = p →
      2 ≤ pRank p (Subgroup.centralizer ({x} : Set G))) :
    GLBStronglyEmbedded p M :=
  D2Escape.stronglyEmbedded_of_order_p h hM fun x hxM hxo =>
    D2Escape.normalizer_zpowers_le_of_centralizer_le h (hC x hxM hxo) (hrank x hxM hxo)

theorem D2Escape.stronglyEmbedded_of_pure {P : Sylow 3 G} {M A H R : Subgroup G}
    (h : D2Escape 3 P M A H R) (hglob : D2Global G) (h3 : 3 ∈ GLBBetaFour G)
    (hpure : ∀ x ∈ M, orderOf x = 3 →
      3 ≤ pRank 3 (M ⊓ Subgroup.centralizer ({x} : Set G))) :
    GLBStronglyEmbedded 3 M := by
  have := hglob.simple
  have hM : M ≠ ⊤ := twoLocal_ne_top hglob.nonab h.maxTwoLocal_M.1
  rcases hglob.deltaTwo h3 P M h.maxTwoLocal_M h.sylow_le with hs | ⟨-, hC⟩
  · exact hs
  · have hCM : ∀ x ∈ M, orderOf x = 3 → Subgroup.centralizer ({x} : Set G) ≤ M :=
      fun x hxM hxo => hC x hxM hxo (hpure x hxM hxo)
    refine D2Escape.stronglyEmbedded_of_centralizers h hM hCM fun x hxM hxo => ?_
    have := hpure x hxM hxo
    rw [inf_eq_right.mpr (hCM x hxM hxo)] at this
    omega

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
