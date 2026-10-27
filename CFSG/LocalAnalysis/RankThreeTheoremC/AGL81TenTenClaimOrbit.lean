module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenTenClaimOf
public import CFSG.LocalAnalysis.AGLEmbedding.CZeroOrbitLines
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81CZeroOrbitRank
import CFSG.LocalAnalysis.AGLEmbedding.SUPairModel
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenSevenFourL34NoRem
import CFSG.Quasithin.Background.C41PfE

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers
open Subgroup
open CFSG.ComponentClassification.AS76b (oUpperTwo)

namespace TenTenClaimOrbit

variable {G : Type} [Group G] [Finite G]

theorem oUpperTwo_mono {A B : Subgroup G} (h : A ≤ B) : oUpperTwo A ≤ oUpperTwo B :=
  closure_mono fun _ hx => ⟨h hx.1, hx.2⟩

theorem subgroupOf_map_restrictAut {X J : Subgroup G} {q : G}
    (hX : X.map (MulAut.conj q).toMonoidHom = X) (hJ : J ≤ X) :
    (J.subgroupOf X).map (CZeroOrbit.restrictAut (MulAut.conj q) X hX).toMonoidHom =
      (J.map (MulAut.conj q).toMonoidHom).subgroupOf X := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : (y : G) ∈ J := mem_subgroupOf.mp hy
    exact mem_subgroupOf.mpr ⟨y, hy', rfl⟩
  · intro hx
    obtain ⟨y, hy, hyx⟩ := mem_subgroupOf.mp hx
    refine ⟨⟨y, hJ hy⟩, mem_subgroupOf.mpr hy, Subtype.ext ?_⟩
    exact hyx

theorem nonempty_quotEquiv_barM {X I : Subgroup G} (hIX : I ≤ X)
    (hker : ∀ g ∈ I, g ∈ pCoreOf 2 X ↔ g ∈ pCoreOf 2 I) :
    Nonempty (↥I ⧸ CFSG.pCore 2 ↥I ≃* ↥(barM X I)) := by
  set N : Subgroup ↥X := CFSG.pCore 2 ↥X with hNdef
  set π := QuotientGroup.mk' N with hπ
  set φ : ↥I →* ↥X ⧸ N := π.comp (inclusion hIX) with hφ
  have hrange : φ.range = barM X I := by
    rw [hφ, MonoidHom.range_comp, inclusion_range]
    rfl
  have hker' : φ.ker = CFSG.pCore 2 ↥I := by
    ext i
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    have h1 : inclusion hIX i ∈ N ↔ (i : G) ∈ pCoreOf 2 X := by
      constructor
      · intro h
        exact ⟨_, h, rfl⟩
      · rintro ⟨y, hy, hyi⟩
        have : y = inclusion hIX i := Subtype.ext hyi
        rwa [← this]
    rw [h1, hker i i.2]
    constructor
    · rintro ⟨y, hy, hyi⟩
      have : y = i := Subtype.ext hyi
      rwa [← this]
    · intro h
      exact ⟨_, h, rfl⟩
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hker').symm.trans
    (QuotientGroup.quotientKerEquivRange φ)).trans (MulEquiv.subgroupCongr hrange)⟩

theorem rank_of_cZero_orbit {X I₀ : Subgroup G} (hI₀ : I₀ ∈ cZero X)
    (h3 : 3 ∣ Nat.card (oUpperTwo I₀)) {q : G} (hq : q ∈ normalizer (X : Set G)) {p k : ℕ}
    (hp : p.Prime) (hqk : q ^ p ^ k = 1)
    (hmove : (oUpperTwo I₀).map (MulAut.conj q).toMonoidHom ≠ oUpperTwo I₀) :
    2 ≤ CFSG.Open.pRank 3 X ∧ (5 ≤ p → 4 ≤ CFSG.Open.pRank 3 X) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N : Subgroup ↥X := CFSG.pCore 2 ↥X with hNdef
  set π := QuotientGroup.mk' N with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hO : CFSG.pCore 2 (↥X ⧸ N) = ⊥ := CZeroProduct.pCore_quotient_pCore_eq_bot 2
  have hX : X.map (MulAut.conj q).toMonoidHom = X := mem_normalizer_iff_map_conj_eq.mp hq
  set φ : MulAut ↥X := CZeroOrbit.restrictAut (MulAut.conj q) X hX with hφdef
  have hφN : N.map φ.toMonoidHom = N := CFSG.pCore_map_iso 2 φ
  set σ : MulAut (↥X ⧸ N) := QuotientGroup.congr N N φ hφN with hσdef
  have hσπ : ∀ x : ↥X, σ (π x) = π (φ x) := fun x => rfl
  have hφpow : ∀ (n : ℕ) (x : ↥X), (((φ ^ n) x : ↥X) : G) = q ^ n * x * (q ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, MulAut.mul_apply, ih]
      change q ^ n * (q * x * q⁻¹) * (q ^ n)⁻¹ = q ^ (n + 1) * x * (q ^ (n + 1))⁻¹
      rw [pow_succ]
      group
  have hσpow : ∀ (n : ℕ) (x : ↥X), (σ ^ n) (π x) = π ((φ ^ n) x) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih => intro x; rw [pow_succ, MulAut.mul_apply, hσπ, ih, pow_succ, MulAut.mul_apply]
  have hσ : σ ^ p ^ k = 1 := by
    ext y
    obtain ⟨x, rfl⟩ := hπs y
    rw [hσpow]
    change π _ = π x
    congr 1
    apply Subtype.ext
    rw [hφpow, hqk, inv_one, one_mul, mul_one]
  set T := barM X I₀ with hTdef
  have hT : IsSubnormal T ⊤ := by
    have := (IsSubnormal.of_mathlib hI₀.subnormal.subgroupOf).map π
    rwa [map_top_of_surjective π hπs] at this
  have hrank : CFSG.Open.pRank 3 (⊤ : Subgroup (↥X ⧸ N)) ≤ CFSG.Open.pRank 3 X := by
    obtain ⟨E, -, hE, hcard⟩ :=
      CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (⊤ : Subgroup (↥X ⧸ N))
    obtain ⟨E', hE'X, hE', hcard'⟩ :=
      TenTenClaim.exists_elemAbelian_lift le_rfl hE ((TenTenClaim.barM_self X).symm ▸ le_top)
    exact CFSG.SectionRank.le_pRank (p := 3) (by norm_num) hE'X hE' (hcard'.trans hcard)
  have hI₀X : I₀ ≤ X := hI₀.le
  set S := oUpperTwo I₀ with hSdef
  have hSX : S ≤ X := (oUpperTwo_le_self I₀).trans hI₀X
  have h1 : (oUpperTwo (I₀.subgroupOf X)).map X.subtype = oUpperTwo I₀ := by
    rw [SUPair.map_oUpperTwo, subgroupOf_map_subtype, inf_of_le_left hI₀X]
  have hO2T : oUpperTwo T = barM X S := by
    rw [hTdef, barM, barM, ← SUPair.map_oUpperTwo]
    congr 1
    rw [hSdef, ← h1]
    exact (Subgroup.comap_map_eq_self_of_injective X.subtype_injective _).symm
  have hσS : (barM X S).map σ.toMonoidHom = barM X (S.map (MulAut.conj q).toMonoidHom) := by
    rw [barM, barM, Subgroup.map_map, ← subgroupOf_map_restrictAut hX hSX, Subgroup.map_map]
    rfl
  have hleS : ∀ {J : Subgroup G}, J ≤ X → barM X J = barM X S → J ≤ S ⊔ pCoreOf 2 X := by
    intro J hJX hJS x hx
    have hxX : x ∈ X := hJX hx
    have hmem : π ⟨x, hxX⟩ ∈ barM X S := hJS ▸ ⟨⟨x, hxX⟩, mem_subgroupOf.mpr hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hmem
    have hv : y⁻¹ * ⟨x, hxX⟩ ∈ N := by
      rw [← QuotientGroup.eq_one_iff]
      change π _ = 1
      rw [map_mul, map_inv, hyx, inv_mul_cancel]
    have e : x = (y : G) * ((y⁻¹ * ⟨x, hxX⟩ : ↥X) : G) := by simp
    rw [e]
    exact mul_mem (mem_sup_left (mem_subgroupOf.mp hy)) (mem_sup_right ⟨_, hv, rfl⟩)
  have hmoveT : (oUpperTwo T).map σ.toMonoidHom ≠ oUpperTwo T := by
    rw [hO2T, hσS]
    intro hJS
    have hSqX : S.map (MulAut.conj q).toMonoidHom ≤ X := by
      rw [← hX]
      exact Subgroup.map_mono hSX
    have hle := hleS hSqX hJS
    apply hmove
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rcases (IsCZeroMember.shape hI₀) with ha | ⟨hO2, _⟩
      ·
        have hperf : ⁅I₀, I₀⁆ = I₀ := ha.perfect
        have hSI : S = I₀ := SevenFourL34.oUpperTwo_eq_of_perfect hperf
        rw [hSI] at hle ⊢
        refine CFSG.Quasithin.C41Pf.le_of_perfect_of_le_sup
          (TenTenNormI.pCoreOf_le_normalizer hI₀X hI₀.subnormal hperf)
          (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X) ?_ hle
        rw [← Subgroup.map_commutator, hperf]
      ·
        have hle' : S.map (MulAut.conj q).toMonoidHom ≤ I₀ := hle.trans (sup_le
          (oUpperTwo_le_self I₀) (hO2 ▸ CFSG.LieType.BorelTits.pCoreOf_le 2 I₀))
        calc S.map (MulAut.conj q).toMonoidHom
            = oUpperTwo (S.map (MulAut.conj q).toMonoidHom) := by
              rw [← SUPair.map_oUpperTwo, hSdef, NoRem.oUpperTwo_idem]
          _ ≤ oUpperTwo I₀ := oUpperTwo_mono hle'
    · rw [Subgroup.card_map_of_injective (MulAut.conj q).injective]
  have hshape : IsSymThreeOrSUThreeTwo ↥T ∨ (IsComponentOf T ⊤ ∧ 3 ∣ Nat.card T) := by
    rcases (IsCZeroMember.shape hI₀) with ha | ⟨hO2, hb⟩
    ·
      right
      have hker : ∀ g ∈ I₀, g ∈ pCoreOf 2 X ↔ g ∈ pCoreOf 2 I₀ := by
        intro g hg
        constructor
        · intro hgX
          have hnorm : I₀ ≤ normalizer ((I₀ ⊓ pCoreOf 2 X : Subgroup G) : Set G) := by
            intro h hh
            have hjA : h ∈ normalizer (I₀ : Set G) := le_normalizer hh
            have hjB : h ∈ normalizer (pCoreOf 2 X : Set G) :=
              localGroup_le_normalizer_pCoreOf 2 X (hI₀X hh)
            rw [mem_normalizer_iff] at hjA hjB ⊢
            intro x
            rw [mem_inf, mem_inf, hjA x, hjB x]
          exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hnorm
            ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).to_le inf_le_right) ⟨hg, hgX⟩
        · intro hgI
          have hsn : IsSubnormal (pCoreOf 2 I₀) X :=
            IsSubnormal.step (CFSG.LieType.BorelTits.pCoreOf_le 2 I₀)
              ((normal_subgroupOf_iff_le_normalizer (CFSG.LieType.BorelTits.pCoreOf_le 2 I₀)).2
                (localGroup_le_normalizer_pCoreOf 2 I₀)) hI₀.subnormal
          exact SubnormalCommute.le_pCoreOf_of_isSubnormal hsn
            (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 I₀) hgI
      obtain ⟨e⟩ := nonempty_quotEquiv_barM hI₀X hker
      have hq := ha.component.2.2
      rw [TenTenClaim.barM_self] at hq
      have hQ : CFSG.Open.IsQuasisimple (↥I₀ ⧸ CFSG.pCore 2 ↥I₀) :=
        Open.IsQuasisimple.of_mulEquiv Subgroup.topEquiv.symm hq
      refine ⟨⟨le_top, hT, Open.IsQuasisimple.of_mulEquiv e.symm hQ⟩, ?_⟩
      have hSI : S = I₀ := SevenFourL34.oUpperTwo_eq_of_perfect ha.perfect
      rw [hSI] at h3
      rw [← Nat.card_congr e.toEquiv]
      have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥I₀)
      obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥I₀)).exists_card_eq
      rw [hcard, hm] at h3
      exact (Nat.Coprime.pow_right m (by norm_num : Nat.Coprime 3 2)).dvd_of_dvd_mul_right h3
    ·
      left
      have hker : ∀ g ∈ I₀, g ∈ pCoreOf 2 X ↔ g ∈ pCoreOf 2 I₀ := fun g _ => by rw [hO2]
      obtain ⟨e⟩ := nonempty_quotEquiv_barM hI₀X hker
      exact IsSymThreeOrSUThreeTwo.of_mulEquiv e hb
  obtain ⟨h2, h4⟩ := CZeroOrbitRank.rank_of_orbit hO hT hshape hp σ hσ hmoveT
  exact ⟨h2.trans hrank, fun hp5 => (h4 hp5).trans hrank⟩

end TenTenClaimOrbit

variable {G : Type} [Group G] [Finite G]

open CFSG.ComponentClassification.AS76b (oUpperTwo) in
open TenTenClaim in
theorem agl81TenTenClaimCfg_of_orbit (h1031 : AGL81TenThreeOneAt G) (h98 : AGL81NineEightFour G) :
    AGL81TenTenClaimCfg G := by
  intro hS p P M H Q K hd L hL hNL I₀ hI₀
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set I := oUpperTwo I₀ with hIdef
  obtain ⟨H₁, R₁, he⟩ := hd.escape
  have hp : p.Prime := he.prime
  have hp2 : p ≠ 2 := he.ne_two
  obtain ⟨hVM, hconjN⟩ := normalizer_facts h98 hS hd hL hI₀
  have hLc : IsTwoPrimeComponent M L := hL.toIsTwoPrimeComponent
  have hLM : L ≤ M := hLc.le
  have hI₀L : I₀ ≤ L := hI₀.le.trans inf_le_right
  have hIL : I ≤ L := (oUpperTwo_le_self I₀).trans hI₀L
  have hIM : I ≤ M := hIL.trans hLM
  have h3 : 3 ∣ Nat.card I := h1031 hS p P M H Q K hd L hL I₀ hI₀
  obtain ⟨e, heI, he3, hnc⟩ := exists_noncentral hLM hI₀ hI₀L h3
  have heL : e ∈ barM M L := barM_mono hIL heI
  have hrkM : CFSG.Open.pRank 3 M ≤ 3 := by
    have h := local_pRank_le_evenRank 3 Nat.prime_three (by norm_num) M he.maxTwoLocal_M.1
    rw [hS.rank] at h
    exact h
  have hrkL : CFSG.Open.pRank 3 L ≤ 3 :=
    (CFSG.SectionRank.pRank_mono (by norm_num) hLM).trans hrkM
  have hconjM : ∀ g ∈ M, L.map (MulAut.conj g).toMonoidHom ≤ M := fun g hg => (hLc.map_conj hg).le
  have hQH : Q ≤ H := hd.le_H
  have hQM : Q ≤ M := hd.base.1
  have hQp : IsPGroup p Q := hd.base.2.1
  have horbitI : ∀ q ∈ Q, L.map (MulAut.conj q).toMonoidHom = L →
      I.map (MulAut.conj q).toMonoidHom ≠ I →
      2 ≤ CFSG.Open.pRank 3 L ∧ (5 ≤ p → 4 ≤ CFSG.Open.pRank 3 L) := by
    intro q hq hLq hIq
    obtain ⟨k, hk⟩ := hQp ⟨q, hq⟩
    have hk' : q ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hqHL : q ∈ normalizer ((H ⊓ L : Subgroup G) : Set G) := by
      have hjA : q ∈ normalizer (H : Set G) := le_normalizer (hQH hq)
      have hjB : q ∈ normalizer (L : Set G) := Subgroup.mem_normalizer_iff_map_conj_eq.mpr hLq
      rw [mem_normalizer_iff] at hjA hjB ⊢
      intro h
      rw [mem_inf, mem_inf, hjA h, hjB h]
    obtain ⟨h2, h4⟩ := TenTenClaimOrbit.rank_of_cZero_orbit hI₀ h3 hqHL hp hk' hIq
    have hmono : CFSG.Open.pRank 3 (H ⊓ L) ≤ CFSG.Open.pRank 3 L :=
      CFSG.SectionRank.pRank_mono (by norm_num) inf_le_right
    exact ⟨h2.trans hmono, fun hp5 => (h4 hp5).trans hmono⟩
  have hlift : ∀ W : Subgroup G, W ≤ M → W ≤ normalizer (I : Set G) →
      ∀ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), E ≤ barM M W → IsElemAbelian 3 E →
        Nat.card E = 3 ^ 3 →
        ∃ Q₀ : Subgroup G, IsAGLQ 3 M Q₀ ∧ Q₀ ≤ normalizer (I : Set G) := by
    intro W hWM hWN E hEW hE hEcard
    obtain ⟨Q₀, hQ₀W, hQ₀, hQ₀card⟩ := exists_elemAbelian_lift hWM hE hEW
    refine ⟨Q₀, ⟨hQ₀W.trans hWM, fun x => ⟨1, Subtype.ext (by simpa using hQ₀.2 _ x.2)⟩, Or.inl ?_⟩,
      hQ₀W.trans hWN⟩
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top, ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_rfl hQ₀ (hQ₀card.trans hEcard)
  rcases eq_or_ne p 3 with rfl | hp3
  ·
    by_cases h3c : ∃ a ∈ M, ∃ b ∈ M, L.map (MulAut.conj a).toMonoidHom ≠ L ∧
        L.map (MulAut.conj b).toMonoidHom ≠ L ∧
        L.map (MulAut.conj a).toMonoidHom ≠ L.map (MulAut.conj b).toMonoidHom
    · obtain ⟨a, ha, b, hb, hLa, hLb, hab⟩ := h3c
      have hg : ∀ i, (![a, b] : Fin 2 → G) i ∈ M := by
        intro i
        fin_cases i
        · exact ha
        · exact hb
      have hab' := Ne.symm hab
      obtain ⟨E₂, hE₂cl, hE₂, hE₂card⟩ := exists_E_conj hLc heL he3 hnc 2 ![a, b] hg (by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all)
      have hmemL : ∀ i, MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨(![a, b] : Fin 2 → G) i, hg i⟩) e ∈
          barM M (L.map (MulAut.conj ((![a, b] : Fin 2 → G) i)).toMonoidHom) :=
        fun i => (conj_noncentral heL he3 hnc (hg i)).1
      have hneL : ∀ i, L ≠ L.map (MulAut.conj ((![a, b] : Fin 2 → G) i)).toMonoidHom := by
        intro i
        fin_cases i
        · exact Ne.symm hLa
        · exact Ne.symm hLb
      have hE₂cent : E₂ ≤ centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
        refine hE₂cl.trans ?_
        rw [closure_le]
        rintro _ ⟨i, rfl⟩
        exact barM_le_centralizer hLc (hLc.map_conj (hg i)) (hneL i) (hmemL i)
      have hce : ∀ c ∈ E₂, e * c = c * e := fun c hc =>
        Subgroup.mem_centralizer_iff.mp (hE₂cent hc) e heL
      obtain ⟨hEab, hEcard⟩ := elemAbelian_zpowers_sup he3 hnc hE₂ hE₂cent hce
      set W := I ⊔ L.map (MulAut.conj a).toMonoidHom ⊔ L.map (MulAut.conj b).toMonoidHom ⊔
        pCoreOf 2 M with hW
      have hWM : W ≤ M := sup_le (sup_le (sup_le hIM (hconjM a ha)) (hconjM b hb))
        (CFSG.LieType.BorelTits.pCoreOf_le 2 M)
      have hWN : W ≤ normalizer (I : Set G) := sup_le (sup_le (sup_le le_normalizer
        (hconjN a ha hLa)) (hconjN b hb hLb)) hVM
      have hLW : ∀ i, L.map (MulAut.conj ((![a, b] : Fin 2 → G) i)).toMonoidHom ≤ W := by
        intro i
        fin_cases i
        · exact le_sup_right.trans (le_sup_left.trans le_sup_left)
        · exact le_sup_right.trans le_sup_left
      refine hlift W hWM hWN (zpowers e ⊔ E₂) (sup_le ?_ ?_) hEab (by rw [hEcard, hE₂card]; norm_num)
      · rw [zpowers_le]
        exact barM_mono (le_sup_left.trans (le_sup_left.trans le_sup_left)) heI
      · refine hE₂cl.trans ?_
        rw [closure_le]
        rintro _ ⟨i, rfl⟩
        exact barM_mono (hLW i) (hmemL i)
    · push Not at h3c
      obtain ⟨m, hm, hne⟩ : ∃ m ∈ M, L.map (MulAut.conj m).toMonoidHom ≠ L := by
        by_contra hcon
        push Not at hcon
        apply hNL
        refine ⟨fun n hn g => ?_⟩
        rw [Subgroup.mem_subgroupOf] at hn ⊢
        have h := hcon g g.2
        rw [← h]
        exact ⟨n, hn, by simp [MulAut.conj_apply]⟩
      by_cases hr : 2 ≤ CFSG.Open.pRank 3 (barM M L)
      ·
        obtain ⟨E0, hE0L, hE0, hE0card⟩ :=
          CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (barM M L)
        have hE0p : IsPGroup 3 ↥E0 := fun x => ⟨1, Subtype.ext (by simpa using hE0.2 _ x.2)⟩
        obtain ⟨K9, hK9⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card Nat.prime_three hE0p
          (n := 2) (by rw [hE0card]; exact Nat.pow_le_pow_right (by norm_num) hr)
        set E9 := K9.map E0.subtype with hE9
        have hE9le : E9 ≤ E0 := Subgroup.map_subtype_le K9
        have hE9ab : IsElemAbelian 3 E9 := by
          have := hE0.1
          exact ⟨isMulCommutative_anti hE9le, fun x hx => hE0.2 x (hE9le hx)⟩
        have hE9card : Nat.card E9 = 3 ^ 2 := by
          rw [hE9, Subgroup.card_map_of_injective E0.subtype_injective, hK9]
        set c := MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨m, hm⟩) with hc
        set E9' := E9.map c.toMonoidHom with hE9'
        have hE9'L : E9' ≤ barM M (L.map (MulAut.conj m).toMonoidHom) := by
          rw [barM_map_conj hm]
          exact Subgroup.map_mono (hE9le.trans hE0L)
        have hE9'ab : IsElemAbelian 3 E9' :=
          CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hE9ab _
        have hE9'card : Nat.card E9' = 3 ^ 2 := by
          rw [hE9', Subgroup.card_map_of_injective c.injective, hE9card]
        have hE9'cent : E9' ≤ centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
          hE9'L.trans (barM_le_centralizer hLc (hLc.map_conj hm) (Ne.symm hne))
        have hce : ∀ c ∈ E9', e * c = c * e := fun c hc =>
          Subgroup.mem_centralizer_iff.mp (hE9'cent hc) e heL
        obtain ⟨hEab, hEcard⟩ := elemAbelian_zpowers_sup he3 hnc hE9'ab hE9'cent hce
        set W := I ⊔ L.map (MulAut.conj m).toMonoidHom ⊔ pCoreOf 2 M with hW
        have hWM : W ≤ M := sup_le (sup_le hIM (hconjM m hm)) (CFSG.LieType.BorelTits.pCoreOf_le 2 M)
        have hWN : W ≤ normalizer (I : Set G) :=
          sup_le (sup_le le_normalizer (hconjN m hm hne)) hVM
        refine hlift W hWM hWN (zpowers e ⊔ E9') (sup_le ?_ ?_) hEab
          (by rw [hEcard, hE9'card]; norm_num)
        · rw [zpowers_le]
          exact barM_mono (le_sup_left.trans le_sup_left) heI
        · exact hE9'L.trans (barM_mono (le_sup_right.trans le_sup_left))
      ·
        push Not at hr
        refine ⟨Q, hd.base, fun q hq => ?_⟩
        obtain ⟨k, hk⟩ := hQp ⟨q, hq⟩
        have hk' : q ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
        have hLq : L.map (MulAut.conj q).toMonoidHom = L := by
          by_contra hLq
          have h2 : L.map (MulAut.conj (q ^ 2)).toMonoidHom ≠ L :=
            map_conj_pow_ne Nat.prime_three hk' hLq (d := 2) (by norm_num) (by norm_num)
          have h12 := map_conj_pow_inj Nat.prime_three hk' hLq (i := 1) (j := 2) (by norm_num)
            (by norm_num)
          rw [pow_one] at h12
          exact h12 (h3c q (hQM hq) (q ^ 2) (M.pow_mem (hQM hq) 2) hLq h2)
        by_contra hIq'
        have hIq : I.map (MulAut.conj q).toMonoidHom ≠ I := fun h =>
          hIq' (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
        have h1 := (horbitI q hq hLq hIq).1
        have h2 := pRank_le_pRank_barM hLM (M := M) (L := L)
        omega
  ·
    have hp5 : 5 ≤ p := by
      have h2 := hp.two_le
      by_contra h
      interval_cases p
      · exact hp2 rfl
      · exact hp3 rfl
      · exact absurd hp (by decide)
    refine ⟨Q, hd.base, fun q hq => ?_⟩
    obtain ⟨k, hk⟩ := hQp ⟨q, hq⟩
    have hk' : q ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hLq : L.map (MulAut.conj q).toMonoidHom = L := by
      by_contra hLq
      have h4 := le_pRank_of_conj hLc heL he3 hnc 4 (fun i => q ^ (i : ℕ))
        (fun i => M.pow_mem (hQM hq) _) (by
          intro i j hij
          have hne' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
          rcases lt_or_gt_of_ne hne' with h | h
          · exact map_conj_pow_inj hp hk' hLq h (by omega)
          · exact (map_conj_pow_inj hp hk' hLq h (by omega)).symm)
      omega
    by_contra hIq'
    have hIq : I.map (MulAut.conj q).toMonoidHom ≠ I := fun h =>
      hIq' (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
    have := (horbitI q hq hLq hIq).2 hp5
    omega

end CFSG.LocalAnalysis.RankThreeTheoremC
