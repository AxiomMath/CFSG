module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallDefs
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoverStar
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbCover
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbPerf
import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

theorem false_of_mem_center_of_perfect {X : Type*} [Group X] [Finite X] {p : ℕ} [hp : Fact p.Prime]
    (hX : commutator X = ⊤) {x : X} (hx : x ∈ Subgroup.center X) (hxp : orderOf x = p)
    (hS : ∀ Q : Subgroup X, IsPGroup p Q → Nat.card Q ≤ p) : False := by
  have hxP : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxp, pow_one])
  obtain ⟨P, hP⟩ := hxP.exists_le_sylow
  have heq : Subgroup.zpowers x = (P : Subgroup X) :=
    Subgroup.eq_of_le_of_card_ge hP (by rw [Nat.card_zpowers, hxp]; exact hS _ P.isPGroup')
  have hPc : (P : Subgroup X) ≤ Subgroup.center X := by
    rw [← heq]
    exact Subgroup.zpowers_le.mpr hx
  have hN : Subgroup.normalizer ((P : Subgroup X) : Set X) ≤
      Subgroup.centralizer ((P : Subgroup X) : Set X) := fun g _ y hy =>
    (Subgroup.mem_center_iff.mp (hPc hy) g).symm
  set f := MonoidHom.transferSylow P hN
  have hcomm : IsMulCommutative (P : Subgroup X) :=
    ⟨⟨fun a b => Subtype.ext (hN (Subgroup.le_normalizer b.2) a a.2)⟩⟩
  have hker : f.ker = ⊤ := by
    rw [eq_top_iff, ← hX, commutator_def]
    refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm.is_comm.comm _ _
  have h1 := MonoidHom.not_dvd_card_ker_transferSylow P hN
  rw [hker, Subgroup.card_top] at h1
  apply h1
  rw [← hxp]
  exact orderOf_dvd_natCard x

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

def blockNormalizerAt (M S : Subgroup G) : Subgroup G :=
  ⨅ L : {L : Subgroup G // IsWeakSBlock M S L}, Subgroup.normalizer (L.1 : Set G)

omit [Finite G] in
theorem mem_blockNormalizerAt {M S : Subgroup G} {x : G} :
    x ∈ blockNormalizerAt M S ↔
      ∀ L : Subgroup G, IsWeakSBlock M S L → x ∈ Subgroup.normalizer (L : Set G) := by
  unfold blockNormalizerAt
  rw [Subgroup.mem_iInf]
  exact ⟨fun h L hL => h ⟨L, hL⟩, fun h L => h L.1 L.2⟩

theorem conj_mem_blockNormalizerAt {M S : Subgroup G} {y x : G}
    (hyS : y ∈ Subgroup.normalizer (S : Set G)) (hyM : y ∈ M)
    (hx : x ∈ blockNormalizerAt M S) : y * x * y⁻¹ ∈ blockNormalizerAt M S := by
  rw [mem_blockNormalizerAt] at hx ⊢
  intro L hL
  have hL' := hL.map_conj (M.inv_mem hyM) ((Subgroup.normalizer (S : Set G)).inv_mem hyS)
  have hxL' := hx _ hL'
  refine Subgroup.mem_normalizer_fintype fun l hl => ?_
  have h1 : y⁻¹ * l * y⁻¹⁻¹ ∈ L.map (MulAut.conj y⁻¹).toMonoidHom :=
    ⟨l, hl, by simp⟩
  have h2 := (Subgroup.mem_normalizer_iff.mp hxL' _).mp h1
  obtain ⟨l', hl', hl'eq⟩ := h2
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hl'eq
  have h3 : y * x * y⁻¹ * l * (y * x * y⁻¹)⁻¹ = l' := by
    have : l' = y * (y⁻¹ * l' * y) * y⁻¹ := by group
    rw [this, hl'eq]
    group
  rw [h3]
  exact hl'

theorem D1OneSmallData.exists_cover_blocks_at (hd : D1OneSmallData p P M H R Rbar K)
    {S : Subgroup G} (hHS : H ⊓ M ≤ Subgroup.normalizer (S : Set G)) {z : G}
    (hz : D1SmallCZElt p H R K z) (hzM : z ∈ M) (hnIa : ¬ D1SmallIa p H K)
    (hR : Nat.card R ≤ p * Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup (H ⧸ primeComplementCore (G := H) p)))
    (hzN : z ∈ blockNormalizerAt M S) :
    ∃ V : Subgroup G, V ≤ H ⊓ M ∧ ⁅V, V⁆ = V ∧ z ∈ V ∧
      ∀ L : Subgroup G, IsWeakSBlock M S L →
        V ≤ Subgroup.normalizer (L : Set G) := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨L', hL', hL'X, hzL'⟩ := D1OneSmallData.exists_second_component hd hz hnIa hR
  have hzH : z ∈ H := hz.2.2.1
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p)
  set C := Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p))
  have hzne : π ⟨z, hzH⟩ ≠ 1 := by
    intro h1
    have h2 := (mk'_primeComplementCore_eq_one_iff p _).mp h1
    have h3 := Subgroup.orderOf_dvd_natCard _ h2
    rw [hz.2.1] at h3
    exact (Nat.Prime.coprime_iff_not_dvd hp).mp (glbPrimeCore_coprime p H) h3
  have hL'ne : L' ≠ K := by
    rintro rfl
    have hmem : π ⟨z, hzH⟩ ∈ L' ⊓ C := ⟨hzL' hzH, hz.2.2.2⟩
    rw [inf_centralizer_eq_bot_of_center hd.center, Subgroup.mem_bot] at hmem
    exact hzne hmem
  have hL'C : L' ≤ C := le_centralizer_of_component_ne hL' hd.comp hL'ne
  set Y : Subgroup G := (L'.comap π).map H.subtype ⊓ M
  set Y₀ : Subgroup G := Y ⊓ blockNormalizerAt M S
  have hYH : Y ≤ H := inf_le_left.trans (Subgroup.map_subtype_le _)
  have hY₀H : Y₀ ≤ H := inf_le_left.trans hYH
  have hzY : z ∈ Y := ⟨⟨⟨z, hzH⟩, hzL' hzH, rfl⟩, hzM⟩
  have hzY₀ : z ∈ Y₀ := ⟨hzY, hzN⟩
  set V := perfectCore Y₀
  have hVY₀ : V ≤ Y₀ := perfectCore_le Y₀
  set ψ := π.comp (Subgroup.inclusion hY₀H)
  have hψz : ψ ⟨z, hzY₀⟩ = π ⟨z, hzH⟩ := rfl
  have hrangeL : ψ.range ≤ L' := by
    rintro _ ⟨⟨y, ⟨⟨h, hh, rfl⟩, -⟩, -⟩, rfl⟩
    have : Subgroup.inclusion hY₀H ⟨(h : G), ⟨⟨h, hh, rfl⟩, ‹_›⟩, ‹_›⟩ = h := Subtype.ext rfl
    simpa [ψ, this] using hh
  have hnorm : ((ψ.range).subgroupOf L').Normal := by
    refine ⟨fun a ha l => ?_⟩
    obtain ⟨x, hx⟩ := Subgroup.mem_subgroupOf.mp ha
    obtain ⟨h, hh, hhl⟩ := hL'X l.2
    have hhM : (h : G) ∈ M := (Subgroup.mem_subgroupOf.mp hh).2
    have hhY : (h : G) ∈ Y := ⟨⟨h, show π h ∈ L' from hhl ▸ l.2, rfl⟩, hhM⟩
    have hxY₀ := x.2
    have hc : (h : G) * x * (h : G)⁻¹ ∈ Y₀ :=
      ⟨Y.mul_mem (Y.mul_mem hhY hxY₀.1) (Y.inv_mem hhY),
        conj_mem_blockNormalizerAt (hHS ⟨h.2, hhM⟩) hhM hxY₀.2⟩
    refine Subgroup.mem_subgroupOf.mpr ⟨⟨_, hc⟩, ?_⟩
    have he : Subgroup.inclusion hY₀H ⟨_, hc⟩ = h * Subgroup.inclusion hY₀H x * h⁻¹ :=
      Subtype.ext rfl
    change π (Subgroup.inclusion hY₀H ⟨_, hc⟩) = _
    rw [he, map_mul, map_mul, map_inv, hhl]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hx]
    rfl
  have hQ : Open.IsQuasisimple ↥L' := hL'.2.2
  have hrange : ψ.range = L' := by
    rcases ComponentClassification.Quasisimple.normal_le_center_or_eq_top hQ
      ((ψ.range).subgroupOf L') with hcen | htop
    · exfalso
      have hzc : (⟨π ⟨z, hzH⟩, hzL' hzH⟩ : ↥L') ∈ Subgroup.center ↥L' :=
        hcen (Subgroup.mem_subgroupOf.mpr ⟨⟨z, hzY₀⟩, hψz⟩)
      refine false_of_mem_center_of_perfect (p := p) hQ.1 hzc ?_ ?_
      · rw [Subgroup.orderOf_mk]
        refine orderOf_eq_prime ?_ hzne
        have : (⟨z, hzH⟩ : H) ^ p = 1 := Subtype.ext (by simp [← hz.2.1, pow_orderOf_eq_one])
        rw [← map_pow, this, map_one]
      · intro Q hQp
        have h1 := D1OneSmallData.card_le_of_le_centralizer hd hR
          ((Subgroup.map_subtype_le Q).trans hL'C) (hQp.map L'.subtype)
        rwa [Subgroup.card_map_of_injective L'.subtype_injective] at h1
    · refine le_antisymm hrangeL fun l hl => ?_
      have : (⟨l, hl⟩ : ↥L') ∈ (ψ.range).subgroupOf L' := htop ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp this
  have hW : (perfectCore (⊤ : Subgroup ↥Y₀)).map ψ = L' := by
    rw [map_perfectCore, ← MonoidHom.range_eq_map, hrange]
    exact perfectCore_eq_self_of_perfect (commutator_eq_self_of_component hL')
  have hWU : (perfectCore (⊤ : Subgroup ↥Y₀)).map Y₀.subtype = V := by
    rw [map_perfectCore, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hzW : π ⟨z, hzH⟩ ∈ (perfectCore (⊤ : Subgroup ↥Y₀)).map ψ := by
    rw [hW]
    exact hzL' hzH
  obtain ⟨w', hw'W, hw'z⟩ := hzW
  have hwV : (w' : G) ∈ V := hWU ▸ ⟨w', hw'W, rfl⟩
  set n : ↥Y₀ := w'⁻¹ * ⟨z, hzY₀⟩
  have hn : p.Coprime (orderOf n) := by
    have h1 : ψ n = 1 := by
      rw [map_mul, map_inv, hw'z, hψz]
      exact inv_mul_cancel _
    have h2 := (mk'_primeComplementCore_eq_one_iff p _).mp h1
    have h3 : orderOf (Subgroup.inclusion hY₀H n) ∣ Nat.card (GLBPrimeCore p H) := by
      have := Subgroup.orderOf_dvd_natCard (GLBPrimeCore p H)
        (x := (Subgroup.inclusion hY₀H n : G)) h2
      rwa [Subgroup.orderOf_coe] at this
    rw [orderOf_injective _ (Subgroup.inclusion_injective hY₀H)] at h3
    exact (glbPrimeCore_coprime p H).coprime_dvd_right h3
  have hUn : (V.subgroupOf Y₀).Normal := perfectCore_normal Y₀
  set q := QuotientGroup.mk' (V.subgroupOf Y₀)
  have hqw : q w' = 1 := (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hwV)
  have hqz : q ⟨z, hzY₀⟩ = q n := by
    rw [show n = w'⁻¹ * ⟨z, hzY₀⟩ from rfl, map_mul, map_inv, hqw, inv_one, one_mul]
  have hzp : orderOf (⟨z, hzY₀⟩ : ↥Y₀) = p := by rw [Subgroup.orderOf_mk]; exact hz.2.1
  have h1 : orderOf (q ⟨z, hzY₀⟩) ∣ p := hzp ▸ orderOf_map_dvd q _
  have h2 : orderOf (q ⟨z, hzY₀⟩) ∣ orderOf n := hqz ▸ orderOf_map_dvd q n
  have h3 : orderOf (q ⟨z, hzY₀⟩) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hn) h2
  have h4 : ⟨z, hzY₀⟩ ∈ V.subgroupOf Y₀ :=
    (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp h3)
  refine ⟨V, hVY₀.trans (le_inf hY₀H (inf_le_left.trans inf_le_right)), perfectCore_perfect Y₀,
    Subgroup.mem_subgroupOf.mp h4, fun L hL => ?_⟩
  exact fun v hv => (mem_blockNormalizerAt.mp (hVY₀ hv).2) L hL

def blockNormalizer (M H : Subgroup G) : Subgroup G := blockNormalizerAt M (pCoreOf 2 H)

omit [Finite G] in
theorem mem_blockNormalizer {M H : Subgroup G} {x : G} :
    x ∈ blockNormalizer M H ↔
      ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → x ∈ Subgroup.normalizer (L : Set G) :=
  mem_blockNormalizerAt

theorem D1OneSmallData.exists_cover_blocks (hd : D1OneSmallData p P M H R Rbar K) {z : G}
    (hz : D1SmallCZElt p H R K z) (hzM : z ∈ M) (hnIa : ¬ D1SmallIa p H K)
    (hR : Nat.card R ≤ p * Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup (H ⧸ primeComplementCore (G := H) p)))
    (hzN : z ∈ blockNormalizer M H) :
    ∃ V : Subgroup G, V ≤ H ⊓ M ∧ ⁅V, V⁆ = V ∧ z ∈ V ∧
      ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
        V ≤ Subgroup.normalizer (L : Set G) :=
  hd.exists_cover_blocks_at (fun _ hx => localGroup_le_normalizer_pCoreOf 2 H hx.1) hz hzM hnIa hR
    hzN

end CFSG.AGLEmbedding
