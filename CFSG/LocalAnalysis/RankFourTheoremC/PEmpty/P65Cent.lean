module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65Basic
import CFSG.ClassicalInvolution.LBalance.Glauberman.SylowTools
import CFSG.Goldschmidt.Steps.G310Basic
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore
import CFSG.RankThree.PartTwo.Sec21.Item23Tools
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62xDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC (SmallRankPlane SmallRankSylowTwo smallRankR
  smallRankIsQ8D8)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G}

private theorem exists_central_of_isPGroup {q : ℕ} [Fact q.Prime] {Q : Subgroup G}
    (hQ : IsPGroup q Q) (hQ1 : Q ≠ ⊥) :
    ∃ c ∈ Q, (∀ t ∈ Q, t * c = c * t) ∧ orderOf c = q := by
  have hnt : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot _).mpr hQ1
  have hZ : Nontrivial (center Q) := hQ.center_nontrivial
  have hdvd : q ∣ Nat.card (center Q) :=
    (hQ.to_subgroup _).card_eq_or_dvd.resolve_left fun h =>
      (Finite.one_lt_card_iff_nontrivial.mpr hZ).ne' h
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' q hdvd
  refine ⟨((c : Q) : G), (c : Q).2, fun t ht => ?_, ?_⟩
  · exact congrArg Subtype.val (Subgroup.mem_center_iff.mp c.2 ⟨t, ht⟩)
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hc]

private theorem isSylowOf_of_normalizer_le {f : ℕ} [Fact f.Prime] {M C S : Subgroup G}
    (hS : CFSG.ABGLocalTools.IsSylowOf f S (M ⊓ C)) (hN : normalizer (S : Set G) ≤ M) :
    CFSG.ABGLocalTools.IsSylowOf f S C := by
  obtain ⟨T, hST, hT⟩ := CFSG.ClassicalInvolution.GlaubermanAut.exists_isSylowOf_ge hS.isPGroup
    (hS.le.trans inf_le_right)
  rcases hST.eq_or_lt with rfl | hlt
  · exact hT
  · exfalso
    have hgrow := CFSG.RankThree.PartTwo.Sec21.lt_inf_normalizer_of_lt hT.isPGroup hlt
    have hle : T ⊓ normalizer (S : Set G) ≤ M ⊓ C :=
      le_inf (inf_le_right.trans hN) (inf_le_left.trans hT.le)
    have := hS.eq_of_le hgrow.le hle hT.isPGroup.to_inf_left
    exact hgrow.ne this.symm

private theorem exists_conj_of_isSylowOf {f : ℕ} [Fact f.Prime] {C S S' : Subgroup G}
    (hS : CFSG.ABGLocalTools.IsSylowOf f S C) (hS' : CFSG.ABGLocalTools.IsSylowOf f S' C) :
    ∃ c ∈ C, S' = S.map (MulAut.conj c).toMonoidHom := by
  obtain ⟨Q, rfl⟩ := hS
  obtain ⟨Q', rfl⟩ := hS'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C Q Q'
  exact ⟨g, g.2, by rw [← hg, CFSG.Goldschmidt.G310.map_subtype_smul_sylow]⟩

private theorem centralizer_zpowers_eq (y : G) :
    centralizer ((zpowers y : Subgroup G) : Set G) = centralizer ({y} : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

private theorem centralizer_le_normalizer_zpowers (y : G) :
    centralizer ({y} : Set G) ≤ normalizer ((zpowers y : Subgroup G) : Set G) := by
  rw [← centralizer_zpowers_eq]
  exact Subgroup.centralizer_le_normalizer _

private theorem normalizer_zpowers_le_normalizer_centralizer (y : G) :
    normalizer ((zpowers y : Subgroup G) : Set G) ≤
      normalizer ((centralizer ({y} : Set G) : Subgroup G) : Set G) := by
  have hn := Subgroup.normal_subgroupOf_centralizer_normalizer ((zpowers y : Subgroup G) : Set G)
  rw [centralizer_zpowers_eq] at hn
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer_zpowers y)).mp hn

private theorem normalizer_le_normalizer_zpowers {F : Subgroup G} (hcyc : IsCyclic F) {y : G}
    (hy : y ∈ F) :
    normalizer (F : Set G) ≤ normalizer ((zpowers y : Subgroup G) : Set G) := by
  haveI := hcyc
  intro g hg
  have hgy : g * y * g⁻¹ ∈ F := (mem_normalizer_iff.mp hg y).mp hy
  set a : F := ⟨y, hy⟩ with ha
  set a' : F := ⟨g * y * g⁻¹, hgy⟩ with ha'
  have hord : orderOf a' = orderOf a := by
    have h1 : orderOf a = orderOf y := (Subgroup.orderOf_coe a).symm
    have h2 : orderOf a' = orderOf (g * y * g⁻¹) := (Subgroup.orderOf_coe a').symm
    have h3 : orderOf (g * y * g⁻¹) = orderOf y := by
      simpa [MulAut.conj_apply] using MulEquiv.orderOf_eq (MulAut.conj g) y
    rw [h1, h2, h3]
  have hzp : zpowers a' = zpowers a :=
    IsCyclic.subgroup_eq_iff_card_eq.mpr (by rw [Nat.card_zpowers, Nat.card_zpowers, hord])
  rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
  have := congrArg (Subgroup.map F.subtype) hzp
  rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at this
  exact this

private theorem normalizer_zpowers_le_of_centralizer_le {f : ℕ} [Fact f.Prime] {M S : Subgroup G}
    {y : G} (hS : CFSG.ABGLocalTools.IsSylowOf f S (centralizer ({y} : Set G)))
    (hSM : normalizer (S : Set G) ≤ M) (hCM : centralizer ({y} : Set G) ≤ M) :
    normalizer ((zpowers y : Subgroup G) : Set G) ≤ M := by
  intro h hh
  have hhC := normalizer_zpowers_le_normalizer_centralizer y hh
  have hCh : (centralizer ({y} : Set G)).map (MulAut.conj h).toMonoidHom =
      centralizer ({y} : Set G) := mem_normalizer_iff_map_conj_eq.mp hhC
  have hT : CFSG.ABGLocalTools.IsSylowOf f (S.map (MulAut.conj h).toMonoidHom)
      (centralizer ({y} : Set G)) := by
    have := isSylowOf_map_conj hS h
    rwa [hCh] at this
  obtain ⟨c, hcC, hc⟩ := exists_conj_of_isSylowOf hS hT
  have hn := p65_mem_normalizer_of_map_eq hc
  have := M.mul_mem (hCM hcC) (hSM hn)
  simpa using this

private theorem exists_sylow_centralizer (hS : Situation G p P M) {f : ℕ} (hf : f.Prime)
    (hf2 : f ≠ 2) (h4 : 4 ≤ Open.pRank f M) {y : G} (hyM : y ∈ M) (hyo : orderOf y = f) :
    ∃ (S : Subgroup G) (F₀ : Sylow f G),
      CFSG.ABGLocalTools.IsSylowOf f S (M ⊓ centralizer ({y} : Set G)) ∧
      CFSG.ABGLocalTools.IsSylowOf f S (centralizer ({y} : Set G)) ∧
      normalizer (S : Set G) ≤ M ∧ D1Local f F₀ M := by
  haveI : Fact f.Prime := ⟨hf⟩
  have hyC : y ∈ centralizer ({y} : Set G) := mem_centralizer_singleton_iff.mpr rfl
  have hycard : Nat.card (zpowers y) = f := by rw [Nat.card_zpowers, hyo]
  have hyp : IsPGroup f (zpowers y) := IsPGroup.of_card (n := 1) (by rw [hycard, pow_one])
  have hyf : y ^ f = 1 := by rw [← hyo]; exact pow_orderOf_eq_one y
  obtain ⟨S₁, hS₁⟩ := CFSG.ABGLocalTools.exists_isSylowOf f (M ⊓ centralizer ({y} : Set G))
  have hyS₁ : y ∈ S₁ :=
    CFSG.ClassicalInvolution.GlaubermanAut.isSylowOf_le_of_le_normalizer hS₁ hyp
      (zpowers_le.mpr ⟨hyM, hyC⟩) (inf_le_right.trans (centralizer_le_normalizer_zpowers y))
      (mem_zpowers y)
  have hS₁M : S₁ ≤ M := hS₁.le.trans inf_le_left
  have hS₁C : S₁ ≤ centralizer ({y} : Set G) := hS₁.le.trans inf_le_right
  obtain ⟨Fh, hS₁Fh, hFh⟩ :=
    CFSG.ClassicalInvolution.GlaubermanAut.exists_isSylowOf_ge hS₁.isPGroup hS₁M
  have hFhM : Fh ≤ M := hFh.le
  have hFhp : IsPGroup f Fh := hFh.isPGroup
  have hFhrk : 4 ≤ Open.pRank f Fh := by rw [pRank_eq_of_isSylowOf hf hFh]; exact h4
  have hFhC : Fh ⊓ centralizer ({y} : Set G) = S₁ :=
    hS₁.eq_of_le (le_inf hS₁Fh hS₁C) (inf_le_inf_right _ hFhM) hFhp.to_inf_left
  obtain ⟨F₀, hFhF₀⟩ := hFhp.exists_le_sylow
  obtain ⟨hD, -⟩ := p65_d1Local_of_le hS hf hf2 h4 hFhM hFhp (by omega) F₀ hFhF₀
  have hrk : 2 ≤ Open.pRank f S₁ := by
    have hFh1 : Fh ≠ ⊥ := by
      rintro rfl
      have := dvd_card_of_one_le_pRank hf (by omega : 1 ≤ Open.pRank f (⊥ : Subgroup G))
      rw [Subgroup.card_bot] at this
      exact hf.one_lt.ne' (Nat.dvd_one.mp this)
    obtain ⟨c, hcFh, hcz, hco⟩ := exists_central_of_isPGroup hFhp hFh1
    have hyFh : y ∈ Fh := hS₁Fh hyS₁
    have hcC : c ∈ centralizer ({y} : Set G) := mem_centralizer_singleton_iff.mpr (hcz y hyFh).symm
    have hcS₁ : c ∈ S₁ := hFhC ▸ mem_inf.mpr ⟨hcFh, hcC⟩
    have hcf : c ^ f = 1 := by rw [← hco]; exact pow_orderOf_eq_one c
    by_cases hcy : c ∈ zpowers y
    ·
      have hccard : Nat.card (zpowers c) = f := by rw [Nat.card_zpowers, hco]
      have heq : zpowers c = zpowers y :=
        Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hcy) (by omega)
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (heq ▸ mem_zpowers y : y ∈ zpowers c)
      have hFhC' : Fh ≤ centralizer ({y} : Set G) := fun t ht => by
        rw [mem_centralizer_singleton_iff, ← hk]
        exact (Commute.zpow_right (hcz t ht) k).eq
      have hFhS₁ : Fh = S₁ := by rw [← hFhC]; exact (inf_eq_left.mpr hFhC').symm
      rw [← hFhS₁]
      omega
    ·
      have hcomm : ∀ e ∈ zpowers y, e * c = c * e := fun e he =>
        hcz e (zpowers_le.mpr hyFh he)
      have hcard := CFSG.RankThree.PartOne.Planes.card_sup_zpowers hf (zpowers y) hcf hcy hcomm
      have hye : CFSG.IsElementaryAbelian f (zpowers y) :=
        CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hyf
      have hce : CFSG.IsElementaryAbelian f (zpowers c) :=
        CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hcf
      have hE : CFSG.IsElementaryAbelian f ↥(zpowers y ⊔ zpowers c) :=
        CFSG.IsElementaryAbelian.sup_of_le_centralizer
          (zpowers_le.mpr (mem_centralizer_iff.mpr fun e he => hcomm e he))
      have hE' : IsElemAbelian f (zpowers y ⊔ zpowers c) :=
        (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian f _).1 hE
      exact CFSG.SectionRank.le_pRank hf.one_lt
        (sup_le (zpowers_le.mpr hyS₁) (zpowers_le.mpr hcS₁)) hE'
        (k := 2) (by rw [hcard, hycard, pow_two])
  have hS₁N : normalizer (S₁ : Set G) ≤ M :=
    normalizer_le_of_two_le_pRank hS.toGlobal.fullCore hD hS₁.isPGroup hS₁M hrk
  exact ⟨S₁, F₀, hS₁, isSylowOf_of_normalizer_le hS₁ hS₁N, hS₁N, hD⟩

private theorem inf_normalizer_le_normalizer_of_almostStrong {f : ℕ} (hf : f.Prime)
    {M Fs Y : Subgroup G} (hYcard : Nat.card Y = f) (hYM : Y ≤ M) (hFs : IsPGroup f Fs)
    (hFsM : Fs ≤ M) (hYFs : Y ≤ Fs) (hNM : ¬ normalizer (Y : Set G) ≤ M)
    (hAS : GLBAlmostStrong M f) :
    M ⊓ normalizer (Fs : Set G) ≤ normalizer (Y : Set G) := by
  obtain ⟨-, -, -, P', hP'M, -, hcase⟩ := hAS
  rcases hcase with ⟨-, hstrong⟩ | ⟨-, -, -, P₀, -, -, -, -, -, -, -, hlast⟩
  · exfalso
    apply hNM
    intro g hg
    by_contra hgM
    refine hstrong g hgM ?_
    rw [← hYcard]
    refine Subgroup.card_dvd_of_le (le_inf hYM ?_)
    intro t ht
    exact ⟨g * t * g⁻¹, hYM ((mem_normalizer_iff.mp hg t).mp ht), by simp [mul_assoc]⟩
  ·
    have hYN : ∀ g ∈ M, Y.map (MulAut.conj g).toMonoidHom ≤ (P' : Subgroup G) →
        Y.map (MulAut.conj g).toMonoidHom = P₀ := by
      intro g hgM hgP
      by_contra hne
      have hcard' : Nat.card (Y.map (MulAut.conj g).toMonoidHom) = f := by
        rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hYcard]
      have hnorm := hlast _ hgP hcard' hne
      rw [← Subgroup.map_equiv_normalizer_eq Y (MulAut.conj g)] at hnorm
      apply hNM
      intro n hn
      have h1 : g * n * g⁻¹ ∈ M := hnorm ⟨n, hn, rfl⟩
      have h2 : g⁻¹ * (g * n * g⁻¹) * g ∈ M := M.mul_mem (M.mul_mem (M.inv_mem hgM) h1) hgM
      simpa [mul_assoc] using h2
    obtain ⟨m, hm⟩ := pGroup_conjugate_into_sylow_within_overgroup f hf P' M hP'M Fs hFs hFsM
    intro s hs
    obtain ⟨hsM, hsN⟩ := mem_inf.mp hs
    have hsFs : Y.map (MulAut.conj s).toMonoidHom ≤ Fs := by
      have h1 : Fs.map (MulAut.conj s).toMonoidHom = Fs := mem_normalizer_iff_map_conj_eq.mp hsN
      rw [← h1]
      exact Subgroup.map_mono hYFs
    have h1 : Y.map (MulAut.conj (m : G)).toMonoidHom ≤ (P' : Subgroup G) :=
      (Subgroup.map_mono hYFs).trans hm
    have h2 : Y.map (MulAut.conj ((m : G) * s)).toMonoidHom ≤ (P' : Subgroup G) := by
      rintro _ ⟨t, ht, rfl⟩
      have hts : s * t * s⁻¹ ∈ Fs := hsFs ⟨t, ht, rfl⟩
      have := hm ⟨s * t * s⁻¹, hts, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using this
    have heq : Y.map (MulAut.conj ((m : G) * s)).toMonoidHom =
        Y.map (MulAut.conj (m : G)).toMonoidHom :=
      (hYN _ (M.mul_mem m.2 hsM) h2).trans (hYN _ m.2 h1).symm
    simpa using p65_mem_normalizer_of_map_eq heq

theorem p65_pRank_centralizer_le_two (hS : Situation G p P M) (hx : Point P M x)
    (hz : Central P z)
    (hApply : ∀ {W : Subgroup G}, W ≠ ⊥ → W ≤ M →
      zpowers x ⊔ zpowers z ≤ normalizer (W : Set G) → ¬ normalizer (W : Set G) ≤ M →
      ∀ {Q : Subgroup G}, Q ≤ normalizer (W : Set G) → IsPGroup p Q →
        ¬ p ∣ (Q.subgroupOf (normalizer (W : Set G))).index → zpowers x ⊔ zpowers z ≤ Q →
        3 ≤ Open.pRank p (normalizer (W : Set G)) →
        ∀ W' : Subgroup G, W' ≤ normalizer (W : Set G) →
          zpowers x ⊔ zpowers z ≤ normalizer (W' : Set G) → Nat.Coprime (Nat.card W') (2 * p) →
          W' ≤ rankThreePrimeCore p (normalizer (W : Set G)))
    {f : ℕ} (hf : f.Prime) (hf2 : f ≠ 2) (hfp : f ≠ p) (h4 : 4 ≤ Open.pRank f M)
    {F Fs R : Subgroup G} {y : G} (hF : IsPGroup f F) (hF1 : F ≠ ⊥) (hFM : F ≤ M)
    (hBF : zpowers x ⊔ zpowers z ≤ normalizer (F : Set G))
    (hHM : ¬ normalizer (F : Set G) ≤ M) (hcyc : IsCyclic F) (hy : y ∈ F) (hyo : orderOf y = f)
    (hFs : IsPGroup f Fs) (hFsM : Fs ≤ M) (hBFs : zpowers x ⊔ zpowers z ≤ normalizer (Fs : Set G))
    (hFFs : F < Fs)
    (hmax : ∀ F' : Subgroup G, F' ≤ M → IsPGroup f F' → F' ≠ ⊥ →
      zpowers x ⊔ zpowers z ≤ normalizer (F' : Set G) → Nat.card F < Nat.card F' →
      normalizer (F' : Set G) ≤ M)
    (hR : IsPGroup p R) (hRM : R ≤ M) (hBR : zpowers x ⊔ zpowers z ≤ R)
    (hRFs : R ≤ normalizer (Fs : Set G)) (hR3 : 3 ≤ Open.pRank p R) :
    Open.pRank f (centralizer ({y} : Set G)) ≤ 2 := by
  by_contra hcon
  push Not at hcon
  have hprime := hS.prime
  haveI : Fact p.Prime := ⟨hprime⟩
  haveI : Fact f.Prime := ⟨hf⟩
  have hpl := plane_of_central hS hx hz
  have hB3 : IsPGroup p ↥(zpowers x ⊔ zpowers z) := IsPGroup.of_card (n := 2) hpl.card_eq
  have hyM : y ∈ M := hFM hy
  have hYcard : Nat.card (zpowers y) = f := by rw [Nat.card_zpowers, hyo]
  have hY1 : zpowers y ≠ ⊥ := fun h => by
    have h1 := hYcard
    rw [h, Subgroup.card_bot] at h1
    exact hf.one_lt.ne h1
  have hYM : zpowers y ≤ M := zpowers_le.mpr hyM
  have hNF : normalizer (F : Set G) ≤ normalizer ((zpowers y : Subgroup G) : Set G) :=
    normalizer_le_normalizer_zpowers hcyc hy
  have hNM : ¬ normalizer ((zpowers y : Subgroup G) : Set G) ≤ M := fun h => hHM (hNF.trans h)
  have hBN : zpowers x ⊔ zpowers z ≤ normalizer ((zpowers y : Subgroup G) : Set G) :=
    hBF.trans hNF
  obtain ⟨S, F₀, hSM, hSC, hSN, hD⟩ := exists_sylow_centralizer hS hf hf2 h4 hyM hyo
  have hCM : ¬ centralizer ({y} : Set G) ≤ M := fun hCM =>
    hNM (normalizer_zpowers_le_of_centralizer_le hSC hSN hCM)
  have hrank3 : 3 ≤ Open.pRank f (M ⊓ centralizer ({y} : Set G)) := by
    rw [← pRank_eq_of_isSylowOf hf hSM, pRank_eq_of_isSylowOf hf hSC]
    omega
  have hAS : GLBAlmostStrong M f :=
    (hS.toGlobal.thmC f F₀ M hD ⟨y, hyM, hyo, hrank3, hCM⟩).1
  have hYFs : zpowers y ≤ Fs := zpowers_le.mpr (hFFs.le hy)
  have hMN := inf_normalizer_le_normalizer_of_almostStrong hf hYcard hYM hFs hFsM hYFs hNM hAS
  have hFsN : Fs ≤ normalizer ((zpowers y : Subgroup G) : Set G) := fun t ht =>
    hMN (mem_inf.mpr ⟨hFsM ht, le_normalizer ht⟩)
  have hRN : R ≤ normalizer ((zpowers y : Subgroup G) : Set G) := fun t ht =>
    hMN (mem_inf.mpr ⟨hRM ht, hRFs ht⟩)
  obtain ⟨Q, hRQ, hQ⟩ := CFSG.ClassicalInvolution.GlaubermanAut.exists_isSylowOf_ge hR hRN
  have hQN := hQ.le
  have hQp : IsPGroup p Q := hQ.isPGroup
  have hQidx : ¬ p ∣ (Q.subgroupOf (normalizer ((zpowers y : Subgroup G) : Set G))).index :=
    (CFSG.ABGLocalTools.isSylowOf_iff.mp hQ).2.2
  have hBQ : zpowers x ⊔ zpowers z ≤ Q := hBR.trans hRQ
  have hrankN : 3 ≤ Open.pRank p (normalizer ((zpowers y : Subgroup G) : Set G)) :=
    hR3.trans (CFSG.SectionRank.pRank_mono hprime.one_lt hRN)
  have hcop : Nat.Coprime (Nat.card Fs) (2 * p) := by
    obtain ⟨k, hk⟩ := hFs.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_left k (Nat.Coprime.mul_right
      ((Nat.coprime_primes hf Nat.prime_two).mpr hf2) ((Nat.coprime_primes hf hprime).mpr hfp))
  have hFsO := hApply hY1 hYM hBN hNM hQN hQp hQidx hBQ hrankN Fs hFsN hBFs hcop
  have hOM : rankThreePrimeCore p (normalizer ((zpowers y : Subgroup G) : Set G)) ≤ M :=
    p65_primeCore_le_of_rank_three hS hx hz hQN hQp hQidx hrankN hBQ
  obtain ⟨-, hNO, hOp⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p
    (normalizer ((zpowers y : Subgroup G) : Set G))
  have hOp' :
      ¬ p ∣ Nat.card (rankThreePrimeCore p (normalizer ((zpowers y : Subgroup G) : Set G))) :=
    (Nat.Prime.coprime_iff_not_dvd hprime).mp hOp
  obtain ⟨S', hS'syl, hFsS', hBS'⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    hprime hf hB3 hOp' (hBN.trans hNO) hFsO hFs hBFs
  have hS'1 : S' ≠ ⊥ := bot_lt_iff_ne_bot.mp ((bot_le.trans_lt hFFs).trans_le hFsS')
  have hcard : Nat.card F < Nat.card S' :=
    (Subgroup.card_lt_of_lt hFFs).trans_le (Subgroup.card_le_of_le hFsS')
  have hS'N : normalizer (S' : Set G) ≤ M :=
    hmax S' (hS'syl.1.trans hOM) hS'syl.2.1 hS'1 hBS' hcard
  exact hNM (p65_le_of_normalizer_le hprime hf hOp' hNO hOM hS'syl hS'N)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
