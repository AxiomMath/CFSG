module

public import CFSG.Open.GLBDefs
public import CFSG.Open.RankThreeDefs
import CFSG.RankThree.PartOne.K1327.Trick
import CFSG.LocalAnalysis.AGLEmbedding.Signalizer
import CFSG.GH74.Uniqueness.SU.SU1Basic
import CFSG.LocalAnalysis.AGLEmbedding.ReducedOrbitsAux

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.InnerQ

open CFSG.Open CFSG.AGLEmbedding CFSG.PreuniquenessRankFour.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem normalizer_le_of_not_isCyclic (hp : p.Prime) (hp2 : p ≠ 2) {P : Sylow p G}
    {M : Subgroup G} (hPM : (P : Subgroup G) ≤ M)
    (hΓ : rankThreeGamma 2 p (P : Subgroup G) ≤ M)
    {D : Subgroup G} (hDM : D ≤ M) (hD : IsPGroup p D) (hnc : ¬ IsCyclic D) :
    Subgroup.normalizer (D : Set G) ≤ M := by
  have : Fact p.Prime := ⟨hp⟩
  set PM : Sylow p M := P.subtype hPM
  have hD' : IsPGroup p (D.subgroupOf M) := hD.comap_subtype
  obtain ⟨S, hS⟩ := hD'.exists_le_sylow
  obtain ⟨m, rfl⟩ := MulAction.exists_smul_eq M PM S
  set g : G := (m : G)
  have hgD : D.map (MulAut.conj g⁻¹).toMonoidHom ≤ P := by
    rintro _ ⟨d, hd, rfl⟩
    have hdS : (⟨d, hDM hd⟩ : M) ∈ ((m • PM : Sylow p M) : Subgroup M) := hS hd
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
      MulAut.conj_inv_apply, Sylow.coe_subtype, Subgroup.mem_subgroupOf] at hdS
    simpa using hdS
  have hrank : 2 ≤ Open.pRank p (D.map (MulAut.conj g⁻¹).toMonoidHom) := by
    rw [pRank_map_of_injective p hp _ (MulAut.conj g⁻¹).injective]
    exact two_le_pRank_of_isPGroup_not_isCyclic hp hp2 hD hnc
  have hN : Subgroup.normalizer
      ((D.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup G) : Set G) ≤ M := by
    refine le_trans ?_ hΓ
    exact le_sSup ⟨_, hgD, hrank, rfl⟩
  intro x hx
  have hx' : g⁻¹ * x * g ∈ Subgroup.normalizer
      ((D.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨d, hd, rfl⟩
      refine ⟨x * d * x⁻¹, (Subgroup.mem_normalizer_iff.mp hx d).mp hd, ?_⟩
      simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
      group
    · rintro ⟨d, hd, hdy⟩
      refine ⟨x⁻¹ * d * x, ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) d).mp hd
        simpa using this
      · simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom] at hdy ⊢
        have hy : y = (g⁻¹ * x * g)⁻¹ * (g⁻¹ * d * g⁻¹⁻¹) * (g⁻¹ * x * g) := by
          rw [hdy]; group
        rw [hy]
        group
  have hgM : g ∈ M := m.2
  have := hN hx'
  have e : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
  rw [e]
  exact M.mul_mem (M.mul_mem hgM this) (M.inv_mem hgM)

theorem normalizer_zpowers_le (hp : p.Prime) (hp2 : p ≠ 2) {P : Sylow p G}
    {M : Subgroup G} (hPM : (P : Subgroup G) ≤ M)
    (hΓ : rankThreeGamma 2 p (P : Subgroup G) ≤ M)
    {E : Subgroup G} (_hEM : E ≤ M) (hE : IsElemAbelian p E) (hEnc : ¬ IsCyclic E)
    {x : G} (hx : x ∈ E) (hC : Subgroup.centralizer ({x} : Set G) ≤ M) :
    Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) ≤ M := by
  have : Fact p.Prime := ⟨hp⟩
  set Nx := Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G)
  set C := Subgroup.centralizer ({x} : Set G)
  have hCN : C ≤ Nx := fun c hc => by
    have hxc : x * c = c * x := (Subgroup.mem_centralizer_singleton_iff.mp hc).symm
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact (Commute.zpow_left (show Commute x c from hxc) k).eq
  set C₁ := C.subgroupOf Nx
  have hC₁ : C₁.Normal := by
    refine ⟨fun c hc n => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hc ⊢
    have hn' := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ n.2) x).mp
      (Subgroup.mem_zpowers x)
    obtain ⟨k, hk⟩ := hn'
    have hcx : (c : G) * x = x * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [Subgroup.coe_mul]
    have hk' : (n : G)⁻¹ * x * (n : G)⁻¹⁻¹ = x ^ k := hk.symm
    rw [inv_inv] at hk'
    have e : x = (n : G) * x ^ k * (n : G)⁻¹ := by rw [← hk']; group
    rw [e]
    have hck : (c : G) * x ^ k = x ^ k * c :=
      (Commute.zpow_right (show Commute (c : G) x from hcx) k).eq
    calc (n : G) * c * (n : G)⁻¹ * ((n : G) * x ^ k * (n : G)⁻¹)
        = (n : G) * (c * x ^ k) * (n : G)⁻¹ := by group
      _ = (n : G) * (x ^ k * c) * (n : G)⁻¹ := by rw [hck]
      _ = (n : G) * x ^ k * (n : G)⁻¹ * ((n : G) * c * (n : G)⁻¹) := by group
  have hEC : E ≤ C := fun e he => Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val ((isMulCommutative_iff.mp hE.1) ⟨e, he⟩ ⟨x, hx⟩))
  have hEpG : IsPGroup p E := fun e => ⟨1, Subtype.ext (by simpa using hE.2 e e.2)⟩
  set E₁ : Subgroup C₁ := (E.subgroupOf Nx).subgroupOf C₁
  have hE₁ : IsPGroup p E₁ := hEpG.comap_subtype.comap_subtype
  obtain ⟨S, hS⟩ := hE₁.exists_le_sylow
  set B : Subgroup G := ((S : Subgroup C₁).map C₁.subtype).map Nx.subtype
  have hBC : B ≤ C := by
    rintro _ ⟨_, ⟨c, -, rfl⟩, rfl⟩
    exact Subgroup.mem_subgroupOf.mp c.2
  have hEB : E ≤ B := by
    intro e he
    have heN : e ∈ Nx := hCN (hEC he)
    have heC : (⟨e, heN⟩ : Nx) ∈ C₁ := Subgroup.mem_subgroupOf.mpr (hEC he)
    have heE₁ : (⟨⟨e, heN⟩, heC⟩ : C₁) ∈ E₁ :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr he)
    exact ⟨_, ⟨_, hS heE₁, rfl⟩, rfl⟩
  have hBp : IsPGroup p B := (S.isPGroup'.map _).map _
  have hBnc : ¬ IsCyclic B := fun hc => hEnc (Subgroup.isCyclic_of_le hEB)
  have hNB : Subgroup.normalizer (B : Set G) ≤ M :=
    normalizer_le_of_not_isCyclic hp hp2 hPM hΓ (hBC.trans hC) hBp hBnc
  have htop := Sylow.normalizer_sup_eq_top (p := p) (N := C₁) S
  intro n hn
  have hn' : (⟨n, hn⟩ : Nx) ∈
      Subgroup.normalizer (((S : Subgroup C₁).map C₁.subtype : Subgroup Nx) : Set Nx) ⊔ C₁ :=
    htop ▸ Subgroup.mem_top _
  have hle : Subgroup.normalizer
      (((S : Subgroup C₁).map C₁.subtype : Subgroup Nx) : Set Nx) ⊔ C₁ ≤
      M.comap Nx.subtype := by
    refine sup_le ?_ ?_
    · intro y hy
      have hy' : (y : G) ∈ Subgroup.normalizer (B : Set G) :=
        Subgroup.le_normalizer_map Nx.subtype ⟨y, hy, rfl⟩
      exact hNB hy'
    · intro c hc
      exact hC (Subgroup.mem_subgroupOf.mp hc)
  exact hle hn'

theorem gamma_one_le (hp : p.Prime) (hp2 : p ≠ 2) {P : Sylow p G}
    {M : Subgroup G} (hPM : (P : Subgroup G) ≤ M)
    (hΓ : rankThreeGamma 2 p (P : Subgroup G) ≤ M)
    {E : Subgroup G} (hEM : E ≤ M) (hE : IsElemAbelian p E) (hEnc : ¬ IsCyclic E)
    (hC : ∀ x ∈ E, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ≤ M) :
    rankThreeGamma 1 p E ≤ M := by
  have : Fact p.Prime := ⟨hp⟩
  have hEpG : IsPGroup p E := fun e => ⟨1, Subtype.ext (by simpa using hE.2 e e.2)⟩
  refine sSup_le ?_
  rintro _ ⟨Q, hQE, hQr, rfl⟩
  by_cases hQc : IsCyclic Q
  · obtain ⟨g, hg⟩ := hQc.exists_generator
    have hQ : Q = Subgroup.zpowers (g : G) := by
      ext y
      constructor
      · intro hy
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
        exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
      · intro hy
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        exact Q.zpow_mem g.2 k
    have hg1 : (g : G) ≠ 1 := by
      intro h1
      have hbot : Q = ⊥ := by rw [hQ, h1, Subgroup.zpowers_one_eq_bot]
      obtain ⟨A, hAQ, -, hAcard⟩ := pRank_attained p hp Q
      have hA : A = ⊥ := le_bot_iff.mp (hbot ▸ hAQ)
      rw [hA, Subgroup.card_bot] at hAcard
      have : p ^ 1 ≤ p ^ Open.pRank p Q := Nat.pow_le_pow_right hp.pos hQr
      rw [← hAcard, pow_one] at this
      exact absurd this (by linarith [hp.two_le])
    rw [hQ]
    exact normalizer_zpowers_le hp hp2 hPM hΓ hEM hE hEnc (hQE g.2) (hC _ (hQE g.2) hg1)
  · exact normalizer_le_of_not_isCyclic hp hp2 hPM hΓ (hQE.trans hEM) (hEpG.to_le hQE) hQc

theorem primeCore_centralizer_le (hp : p.Prime) (hp2 : p ≠ 2) {P : Sylow p G}
    {M : Subgroup G} (hPM : (P : Subgroup G) ≤ M)
    (hΓ : rankThreeGamma 2 p (P : Subgroup G) ≤ M)
    {x : G} (hxM : x ∈ M) (hxp : x ^ p = 1) (hx1 : x ≠ 1) {F : Subgroup G} (hFM : F ≤ M)
    (hFx : F ≤ Subgroup.centralizer ({x} : Set G)) (hF : IsElemAbelian p F)
    (hFcard : Nat.card F = p ^ 2) (hFout : ∀ f ∈ F, f ≠ 1 → f ∉ Subgroup.zpowers x) :
    GLBPrimeCore p (Subgroup.centralizer ({x} : Set G)) ≤ M := by
  have : Fact p.Prime := ⟨hp⟩
  set C := Subgroup.centralizer ({x} : Set G)
  set O := GLBPrimeCore p C
  have hFN : F ≤ Subgroup.normalizer (O : Set G) := hFx.trans (le_normalizer_glbPrimeCore p C)
  have hcop : ¬ p ∣ Nat.card O := fun h =>
    hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (glbPrimeCore_coprime p C) h)
  refine (CFSG.RankThree.PartOne.K1327.le_iSup_centralizers hp hF hFcard hFN hcop).trans ?_
  refine iSup_le fun ⟨f, hf1⟩ => ?_
  have hfF : (f : G) ∈ F := f.2
  have hf1' : (f : G) ≠ 1 := fun h => hf1 (Subtype.ext h)
  have hxf : (f : G) * x = x * f := Subgroup.mem_centralizer_singleton_iff.mp (hFx hfF)
  set D := Subgroup.zpowers x ⊔ Subgroup.zpowers (f : G)
  have hDM : D ≤ M := sup_le (Subgroup.zpowers_le.mpr hxM) (Subgroup.zpowers_le.mpr (hFM hfF))
  have hfp : (f : G) ^ p = 1 := hF.2 _ hfF
  obtain ⟨hDel, hDcard⟩ := CFSG.GH74.Uniqueness.SU.SU1.isElemAbelian_card_sup_zpowers hp hxp hfp
    hx1 (hFout _ hfF hf1') hxf.symm
  have hDp : IsPGroup p D := fun e => ⟨1, Subtype.ext (by simpa using hDel.2 e e.2)⟩
  have hDnc : ¬ IsCyclic D := by
    intro hc
    have hexp : Monoid.exponent D ∣ p :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun e => Subtype.ext (by simpa using hDel.2 e e.2)
    rw [IsCyclic.exponent_eq_card, hDcard] at hexp
    have := Nat.le_of_dvd hp.pos hexp
    nlinarith [hp.two_le]
  have hND := normalizer_le_of_not_isCyclic hp hp2 hPM hΓ hDM hDp hDnc
  intro o ho
  obtain ⟨hoO, hof⟩ := Subgroup.mem_inf.mp ho
  refine hND ?_
  have hoC : o ∈ C := glbPrimeCore_le p C hoO
  have hox : o * x = x * o := Subgroup.mem_centralizer_singleton_iff.mp hoC
  have hof' : o * f = f * o := Subgroup.mem_centralizer_singleton_iff.mp hof
  have hDo : D ≤ Subgroup.centralizer ((Subgroup.zpowers o : Subgroup G) : Set G) := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro w hw
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      exact (Commute.zpow_left (show Commute o x from hox) k).eq
    · rw [Subgroup.mem_centralizer_iff]
      intro w hw
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      exact (Commute.zpow_left (show Commute o (f : G) from hof') k).eq
  have hoD : o ∈ Subgroup.centralizer (D : Set G) :=
    (Subgroup.le_centralizer_iff.mp hDo) (Subgroup.mem_zpowers o)
  exact Subgroup.centralizer_le_normalizer _ hoD

end CFSG.LocalAnalysis.RankThreeTheoremC.InnerQ
