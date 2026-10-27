module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95IvDefs
import CFSG.LocalAnalysis.GLTheoremB.Prop95Ii
import CFSG.LocalAnalysis.GLTheoremB.CentralizerLift

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Parts
open CFSG.LocalAnalysis.GLTheoremB.Prop95Assembly
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531 (FFChevConclusion)
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevTwo)
open scoped commutatorElement

section Setting

variable {G : Type} [Group G] [Finite G]
variable {m p : ℕ} {M D L : Subgroup G}

private theorem fam_img_mono {M : Subgroup G} (N : Subgroup ↥M) [N.Normal] {Y Z : Subgroup G}
    (h : Y ≤ Z) :
    (Y.subgroupOf M).map (QuotientGroup.mk' N) ≤ (Z.subgroupOf M).map (QuotientGroup.mk' N) :=
  Subgroup.map_mono (Subgroup.comap_mono h)

private theorem fam_mem_img {M : Subgroup G} (N : Subgroup ↥M) [N.Normal] {Y : Subgroup G}
    {y : ↥M ⧸ N} :
    y ∈ (Y.subgroupOf M).map (QuotientGroup.mk' N) ↔
      ∃ x : ↥M, (x : G) ∈ Y ∧ QuotientGroup.mk' N x = y := by
  constructor
  · intro hy
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 hy
    exact ⟨x, Subgroup.mem_subgroupOf.1 hx, hxy⟩
  · rintro ⟨x, hx, rfl⟩
    exact Subgroup.mem_map.2 ⟨x, Subgroup.mem_subgroupOf.2 hx, rfl⟩

private theorem fam_img_normalizes {M : Subgroup G} (N : Subgroup ↥M) [N.Normal] {x : ↥M}
    {Y : Subgroup G} (hx : (x : G) ∈ Subgroup.normalizer (Y : Set G)) :
    QuotientGroup.mk' N x ∈ Subgroup.normalizer
      (((Y.subgroupOf M).map (QuotientGroup.mk' N) : Subgroup (↥M ⧸ N)) : Set (↥M ⧸ N)) := by
  have fwd : ∀ y : ↥M, (y : G) ∈ Subgroup.normalizer (Y : Set G) →
      ∀ u ∈ (Y.subgroupOf M).map (QuotientGroup.mk' N),
        QuotientGroup.mk' N y * u * (QuotientGroup.mk' N y)⁻¹ ∈
          (Y.subgroupOf M).map (QuotientGroup.mk' N) := by
    intro y hy u hu
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hu
    refine Subgroup.mem_map.2 ⟨y * z * y⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      have hz' : (z : G) ∈ Y := Subgroup.mem_subgroupOf.1 hz
      have := (Subgroup.mem_normalizer_iff.1 hy (z : G)).1 hz'
      simpa using this
    · simp only [map_mul, map_inv]
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    exact fwd x hx u hu
  · intro hu
    have h' := fwd x⁻¹ ((Subgroup.normalizer (Y : Set G)).inv_mem hx) _ hu
    simpa [map_inv, mul_assoc] using h'

private theorem fam_img_isElemAbelian {M : Subgroup G} {p : ℕ} (N : Subgroup ↥M) [N.Normal]
    {D : Subgroup G} (hD : IsElemAbelian p D) :
    IsElemAbelian p ((D.subgroupOf M).map (QuotientGroup.mk' N)) := by
  refine ⟨isMulCommutative_iff.2 fun a b => ?_, fun a ha => ?_⟩
  · obtain ⟨x, hxD, hx⟩ := (fam_mem_img N).1 a.2
    obtain ⟨y, hyD, hy⟩ := (fam_mem_img N).1 b.2
    have hcG : (x : G) * (y : G) = (y : G) * (x : G) :=
      congrArg Subtype.val (isMulCommutative_iff.1 hD.1 ⟨(x : G), hxD⟩ ⟨(y : G), hyD⟩)
    have hc : x * y = y * x := Subtype.ext hcG
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hx, ← hy, ← map_mul, ← map_mul, hc]
  · obtain ⟨x, hxD, rfl⟩ := (fam_mem_img N).1 ha
    have hx : x ^ p = 1 := Subtype.ext (by simpa using hD.2 (x : G) hxD)
    rw [← map_pow, hx, map_one]

private theorem fam_img_pCoreOf_le {M : Subgroup G} (N : Subgroup ↥M) [N.Normal] (S : Subgroup G) :
    ((pCoreOf 2 S).subgroupOf M).map (QuotientGroup.mk' N) ≤
      pCoreOf 2 ((S.subgroupOf M).map (QuotientGroup.mk' N) : Subgroup (↥M ⧸ N)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (fam_img_mono N (CFSG.LieType.BorelTits.pCoreOf_le 2 S)) ?_ ?_
  · intro z hz
    obtain ⟨x, hxS, rfl⟩ := (fam_mem_img N).1 hz
    exact fam_img_normalizes N (le_normalizer_pCoreOf 2 S hxS)
  · exact IsPGroup.map
      (IsPGroup.comap_subtype (K := M) (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 S))
      (QuotientGroup.mk' N)

private theorem fam_pCoreOf_tl_le {M S : Subgroup G} (hS : S ≤ M) :
    pCoreOf 2 (tl M S) ≤ tl M (pCoreOf 2 S) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨π, hπ⟩ : ∃ π : ↥S →* Mt M,
      ∀ g : ↥S, π g = QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨(g : G), hS g.2⟩ :=
    ⟨(QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hS), fun g => rfl⟩
  have hker : IsPGroup 2 π.ker := by
    have heq : π.ker = (CFSG.pCore 2 ↥M).comap (Subgroup.inclusion hS) := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_comap, hπ]
      exact QuotientGroup.eq_one_iff _
    rw [heq]
    exact IsPGroup.comap_of_injective (CFSG.LieType.BorelTits.pCore_isPGroup 2)
      (Subgroup.inclusion hS) (Subgroup.inclusion_injective hS)
  have hP : IsPGroup 2 ((pCoreOf 2 (tl M S)).comap π) :=
    IsPGroup.comap_of_ker_isPGroup (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) π hker
  have hN : ((pCoreOf 2 (tl M S)).comap π).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_comap] at hn ⊢
    have hg : π g ∈ tl M S := by
      rw [hπ]
      exact Subgroup.mem_map.2 ⟨⟨g, hS g.2⟩, Subgroup.mem_subgroupOf.2 g.2, rfl⟩
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 (tl M S) hg) (π n)).1 hn
  have hle := CFSG.LieType.BorelTits.le_pCore 2 hN hP
  intro x hx
  obtain ⟨y, hyS, rfl⟩ :=
    (fam_mem_img (CFSG.pCore 2 ↥M)).1 (CFSG.LieType.BorelTits.pCoreOf_le 2 (tl M S) hx)
  have hz : (⟨(y : G), hyS⟩ : ↥S) ∈ (pCoreOf 2 (tl M S)).comap π := by
    rw [Subgroup.mem_comap, hπ]
    exact hx
  have hyc : (y : G) ∈ pCoreOf 2 S := Subgroup.mem_map.2 ⟨_, hle hz, rfl⟩
  exact (fam_mem_img (CFSG.pCore 2 ↥M)).2 ⟨y, hyc, rfl⟩

private theorem fam_tl_pCoreOf_eq {M S : Subgroup G} (hS : S ≤ M) :
    tl M (pCoreOf 2 S) = pCoreOf 2 (tl M S) :=
  le_antisymm (fam_img_pCoreOf_le (CFSG.pCore 2 ↥M) S) (fam_pCoreOf_tl_le hS)

private theorem fam_not_dvd_pCoreOf {M : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ Nat.card (pCoreOf 2 M) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).exists_card_eq
  rw [hk]
  intro h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))

private theorem fam_eq_one_of_mem {N : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hN : ¬ p ∣ Nat.card N) {d : G} (hdN : d ∈ N) (hd : d ^ p = 1) : d = 1 := by
  have h1 : orderOf d ∣ p := orderOf_dvd_of_pow_eq_one hd
  have h2 : orderOf d ∣ Nat.card N := by
    have := orderOf_dvd_natCard (⟨d, hdN⟩ : ↥N)
    rwa [Subgroup.orderOf_mk] at this
  rcases (Nat.dvd_prime hp).1 h1 with h | h
  · exact orderOf_eq_one_iff.1 h
  · exact absurd (h ▸ h2) hN

private theorem fam_mk_ne_one_pCore {M D : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hDp : ∀ x ∈ D, x ^ p = 1) {d : G} (hdD : d ∈ D) (hd1 : d ≠ 1) (hdM : d ∈ M) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨d, hdM⟩ ≠ 1 := by
  intro h
  have hmem : (⟨d, hdM⟩ : ↥M) ∈ CFSG.pCore 2 ↥M := (QuotientGroup.eq_one_iff _).1 h
  have hdN : d ∈ pCoreOf 2 M := Subgroup.mem_map.2 ⟨⟨d, hdM⟩, hmem, rfl⟩
  exact hd1 (fam_eq_one_of_mem hp (fam_not_dvd_pCoreOf hp hp2) hdN (hDp d hdD))

private theorem fam_barX_mk_ne_one {M D : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hDp : ∀ x ∈ D, x ^ p = 1) {d : G} (hdD : d ∈ D) (hd1 : d ≠ 1) (hdM : d ∈ M) :
    QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨d, hdM⟩ ≠ 1 := by
  intro h
  have hmem : (⟨d, hdM⟩ : ↥M) ∈ GLAPPrimeCore p ↥M := (QuotientGroup.eq_one_iff _).1 h
  have hdN : d ∈ GLAPPrimeCoreOf p M := Subgroup.mem_map.2 ⟨⟨d, hdM⟩, hmem, rfl⟩
  exact hd1 (fam_eq_one_of_mem hp (not_dvd_card_glaPPrimeCoreOf hp M) hdN (hDp d hdD))

private theorem fam_normalizer_iSup {X : Type*} [Group X] {ι : Sort*} (H : ι → Subgroup X) {g : X}
    (hg : ∀ i, g ∈ Subgroup.normalizer (H i : Set X)) :
    g ∈ Subgroup.normalizer ((⨆ i, H i : Subgroup X) : Set X) := by
  have fwd : ∀ g' : X, (∀ i, g' ∈ Subgroup.normalizer (H i : Set X)) →
      ∀ y ∈ (⨆ i, H i : Subgroup X), g' * y * g'⁻¹ ∈ (⨆ i, H i : Subgroup X) := by
    intro g' hg' y hy
    refine Subgroup.iSup_induction H (C := fun y => g' * y * g'⁻¹ ∈ (⨆ i, H i : Subgroup X))
      hy (fun i y hy => ?_) (by simp) (fun x y hx hy => ?_)
    · exact Subgroup.mem_iSup_of_mem i ((Subgroup.mem_normalizer_iff.1 (hg' i) y).1 hy)
    · show g' * (x * y) * g'⁻¹ ∈ (⨆ i, H i : Subgroup X)
      have e : g' * (x * y) * g'⁻¹ = (g' * x * g'⁻¹) * (g' * y * g'⁻¹) := by group
      rw [e]
      exact (⨆ i, H i).mul_mem hx hy
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact fwd g hg y
  · intro hy
    have h' := fwd g⁻¹ (fun i => (Subgroup.normalizer (H i : Set X)).inv_mem (hg i)) _ hy
    have e : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
    rw [e] at h'
    exact h'

private theorem fam_tl_term {M D : Subgroup G} {d : G} (hdM : d ∈ M) (hdD : d ∈ D) :
    tl M (pCoreOf 2 (Subgroup.centralizer ({d} : Set G))) ≤
      Hfam M D (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨d, hdM⟩) :=
  le_iSup_of_le d (le_iSup_of_le hdM (le_iSup_of_le hdD (le_iSup_of_le rfl le_rfl)))

private theorem fam_barX_term {p : ℕ} {M D : Subgroup G} {d : G} (hdM : d ∈ M) (hdD : d ∈ D) :
    barX p M (pCoreOf 2 (Subgroup.centralizer ({d} : Set G))) ≤
      Hbar p M D (QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨d, hdM⟩) :=
  le_iSup_of_le d (le_iSup_of_le hdM (le_iSup_of_le hdD (le_iSup_of_le rfl le_rfl)))

private theorem fam_barX_centralizer {M : Subgroup G} {p : ℕ} (hp : p.Prime) {d : G} (hdM : d ∈ M)
    (hdP : IsPGroup p (Subgroup.zpowers d)) :
    barX p M (M ⊓ Subgroup.centralizer ({d} : Set G)) =
      Subgroup.centralizer ({QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨d, hdM⟩} :
        Set (↥M ⧸ GLAPPrimeCore p ↥M)) := by
  rw [barX_inf_centralizer hp hdM le_rfl (Subgroup.le_normalizer hdM) hdP, barX_self, top_inf_eq]

theorem tl_centralizer_eq (h : IvSetting m p M D L) {d : G} (hdD : d ∈ D) (hdM : d ∈ M) :
    tl M (Subgroup.centralizer ({d} : Set G)) =
      Subgroup.centralizer ({QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨d, hdM⟩} : Set (Mt M)) := by
  have hp : p.Prime := prime_of_standing h.standing
  haveI : Fact p.Prime := ⟨hp⟩
  have hdP : IsPGroup p (Subgroup.zpowers d) :=
    isPGroup_zpowers_of_pow_eq_one' (h.hyp.plane.1.2 d hdD)
  have hdN : d ∈ Subgroup.normalizer ((pCoreOf 2 M : Subgroup G) : Set G) :=
    le_normalizer_pCoreOf 2 M hdM
  have hV : ¬ p ∣ Nat.card (pCoreOf 2 M) := fam_not_dvd_pCoreOf hp (ne_two_of_standing h.standing)
  apply le_antisymm
  · rintro _ ⟨x, hxC, rfl⟩
    have hxd : (x : G) * d = d * (x : G) :=
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_subgroupOf.1 hxC)
    have h2 : x * (⟨d, hdM⟩ : ↥M) = (⟨d, hdM⟩ : ↥M) * x := Subtype.ext hxd
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, h2]
  · intro z hz
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ z
    have hc := Subgroup.mem_centralizer_singleton_iff.1 hz
    have h3 : QuotientGroup.mk' (CFSG.pCore 2 ↥M)
        ((⟨d, hdM⟩ : ↥M) * x * (⟨d, hdM⟩ : ↥M)⁻¹ * x⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [← hc]
      simp
    have hdiv : ((⟨d, hdM⟩ : ↥M) * x * (⟨d, hdM⟩ : ↥M)⁻¹ * x⁻¹) ∈ CFSG.pCore 2 ↥M :=
      (QuotientGroup.eq_one_iff ((⟨d, hdM⟩ : ↥M) * x * (⟨d, hdM⟩ : ↥M)⁻¹ * x⁻¹)).1 h3
    have hx' : d * (x : G) * d⁻¹ * (x : G)⁻¹ ∈ pCoreOf 2 M :=
      Subgroup.mem_map.2 ⟨_, hdiv, by simp⟩
    obtain ⟨v, hv, hvc⟩ :=
      exists_mul_mem_centralizer hdP hV hdN (le_normalizer_pCoreOf 2 M x.2) hx'
    have hvM : v ∈ M := CFSG.LieType.BorelTits.pCoreOf_le 2 M hv
    have hvpc : (⟨v, hvM⟩ : ↥M) ∈ CFSG.pCore 2 ↥M := by
      obtain ⟨y, hy, hyv⟩ := Subgroup.mem_map.1 hv
      have : y = ⟨v, hvM⟩ := Subtype.ext hyv
      exact this ▸ hy
    have hwM : (x : G) * v ∈ M := M.mul_mem x.2 hvM
    have hv1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (⟨v, hvM⟩ : ↥M) = 1 :=
      (QuotientGroup.eq_one_iff _).2 hvpc
    have hmk : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (⟨(x : G) * v, hwM⟩ : ↥M) =
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) x := by
      rw [show (⟨(x : G) * v, hwM⟩ : ↥M) = x * ⟨v, hvM⟩ from rfl, map_mul, hv1, mul_one]
    rw [← hmk]
    exact Subgroup.mem_map.2 ⟨⟨(x : G) * v, hwM⟩, Subgroup.mem_subgroupOf.2 hvc, rfl⟩

theorem hfam_family (h : IvSetting m p M D L) : SignalizerFamily p (tl M D) (Hfam M D) := by
  have hp : p.Prime := prime_of_standing h.standing
  haveI : Fact p.Prime := ⟨hp⟩
  have hE : IsElemAbelian p D := h.hyp.plane.1
  have hDc : ∀ u ∈ D, ∀ v ∈ D, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (isMulCommutative_iff.1 hE.1 ⟨u, hu⟩ ⟨v, hv⟩)
  refine ⟨fam_img_isElemAbelian (CFSG.pCore 2 ↥M) hE, ?_, ?_⟩
  · intro a ha _
    obtain ⟨x, hxD, rfl⟩ := (fam_mem_img (CFSG.pCore 2 ↥M)).1 ha
    unfold Hfam
    refine iSup_le fun d' => iSup_le fun hd'M => iSup_le fun hd'D => iSup_le fun hmk => ?_
    rw [← hmk, ← tl_centralizer_eq h hd'D hd'M]
    exact fam_img_pCoreOf_le (CFSG.pCore 2 ↥M) _
  · intro a ha _ e he
    obtain ⟨x, hxD, rfl⟩ := (fam_mem_img (CFSG.pCore 2 ↥M)).1 ha
    obtain ⟨y, hyD, rfl⟩ := (fam_mem_img (CFSG.pCore 2 ↥M)).1 he
    unfold Hfam
    refine fam_normalizer_iSup _ fun d' => fam_normalizer_iSup _ fun hd'M =>
      fam_normalizer_iSup _ fun hd'D => fam_normalizer_iSup _ fun hmk => ?_
    have hyC : (y : G) ∈ Subgroup.centralizer ({d'} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.2 (hDc _ hyD _ hd'D)
    exact fam_img_normalizes (CFSG.pCore 2 ↥M) (le_normalizer_pCoreOf 2 _ hyC)

theorem sigmaFam_hfam (h : IvSetting m p M D L) :
    sigmaFam (tl M D) (Hfam M D) = tl M (sigmaStar D) := by
  have hp : p.Prime := prime_of_standing h.standing
  have hp2 : p ≠ 2 := ne_two_of_standing h.standing
  have hE : IsElemAbelian p D := h.hyp.plane.1
  have hDp : ∀ x ∈ D, x ^ p = 1 := hE.2
  apply le_antisymm
  · unfold sigmaFam
    refine iSup_le fun x => iSup_le fun hx => iSup_le fun hx1 => ?_
    obtain ⟨y, hyD, rfl⟩ := (fam_mem_img (CFSG.pCore 2 ↥M)).1 hx
    unfold Hfam
    refine iSup_le fun d => iSup_le fun hdM => iSup_le fun hdD => iSup_le fun hmk => ?_
    have hd1 : d ≠ 1 := by
      rintro rfl
      apply hx1
      rw [← hmk]
      exact map_one (QuotientGroup.mk' (CFSG.pCore 2 ↥M))
    unfold sigmaStar
    exact fam_img_mono (CFSG.pCore 2 ↥M)
      (le_iSup_of_le d (le_iSup_of_le hdD (le_iSup_of_le hd1 le_rfl)))
  · have key : sigmaStar D ≤ ((sigmaFam (tl M D) (Hfam M D)).comap
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype := by
      unfold sigmaStar
      refine iSup_le fun d => iSup_le fun hdD => iSup_le fun hd1 => ?_
      have hdM : d ∈ M := h.hyp.le hdD
      have hA := h.hyp.clause_a d hdD hd1
      intro g hg
      refine Subgroup.mem_map.2 ⟨⟨g, hA hg⟩, Subgroup.mem_comap.2 ?_, rfl⟩
      have hmemT : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨d, hdM⟩ ∈ tl M D :=
        Subgroup.mem_map.2 ⟨⟨d, hdM⟩, Subgroup.mem_subgroupOf.2 hdD, rfl⟩
      have hne := fam_mk_ne_one_pCore hp hp2 hDp hdD hd1 hdM
      have hsub : Hfam M D (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨d, hdM⟩) ≤
          sigmaFam (tl M D) (Hfam M D) := by
        unfold sigmaFam
        exact le_iSup_of_le (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨d, hdM⟩)
          (le_iSup_of_le hmemT (le_iSup_of_le hne le_rfl))
      exact hsub (fam_tl_term hdM hdD
        (Subgroup.mem_map.2 ⟨⟨g, hA hg⟩, Subgroup.mem_subgroupOf.2 hg, rfl⟩))
    intro z hz
    obtain ⟨w, hw, rfl⟩ := (fam_mem_img (CFSG.pCore 2 ↥M)).1 hz
    obtain ⟨w', hw', hww'⟩ := Subgroup.mem_map.1 (key hw)
    have hw'w : w' = w := Subtype.ext hww'
    rw [Subgroup.mem_comap, hw'w] at hw'
    exact hw'

theorem tl_gammaD_le_pCore (h : IvSetting m p M D L) :
    tl M (gammaD D) ≤ pCoreOf 2 (sigmaFam (tl M D) (Hfam M D)) := by
  rw [sigmaFam_hfam h]
  calc tl M (gammaD D) ≤ tl M (sigmaOf D) := fam_img_mono _ (gammaD_le_sigmaOf D)
    _ = tl M (pCoreOf 2 (sigmaStar D)) := rfl
    _ = pCoreOf 2 (tl M (sigmaStar D)) := fam_tl_pCoreOf_eq (sigmaStar_le h.hyp)

theorem hbar_family (h : IvSetting m p M D L) :
    SignalizerFamily p (barX p M D) (Hbar p M D) ∧ SignalizerFamily.CInvariant (barX p M D) (Hbar p M D) := by
  have hp : p.Prime := prime_of_standing h.standing
  haveI : Fact p.Prime := ⟨hp⟩
  have hE : IsElemAbelian p D := h.hyp.plane.1
  have hDc : ∀ u ∈ D, ∀ v ∈ D, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (isMulCommutative_iff.1 hE.1 ⟨u, hu⟩ ⟨v, hv⟩)
  have hDp : ∀ x ∈ D, x ^ p = 1 := hE.2
  have hcent : ∀ {d : G} (hdM : d ∈ M) (hdD : d ∈ D), d ≠ 1 →
      barX p M (pCoreOf 2 (Subgroup.centralizer ({d} : Set G))) ≤
        pCoreOf 2 (Subgroup.centralizer
          ({QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨d, hdM⟩} : Set (↥M ⧸ GLAPPrimeCore p ↥M))) := by
    intro d hdM hdD hd1
    have hdP : IsPGroup p (Subgroup.zpowers d) := isPGroup_zpowers_of_pow_eq_one' (hDp d hdD)
    have hHM : pCoreOf 2 (Subgroup.centralizer ({d} : Set G)) ≤ M := h.hyp.clause_a d hdD hd1
    rw [← fam_barX_centralizer hp hdM hdP]
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_
      (isPGroup_barX (p := p) (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) hHM)
    · exact fam_img_mono _ (le_inf hHM (CFSG.LieType.BorelTits.pCoreOf_le 2 _))
    · intro c hc
      obtain ⟨z, hz, rfl⟩ := (fam_mem_img _).1 hc
      exact fam_img_normalizes _ (le_normalizer_pCoreOf 2 _ (Subgroup.mem_inf.1 hz).2)
  refine ⟨⟨fam_img_isElemAbelian (GLAPPrimeCore p ↥M) hE, ?_, ?_⟩, ?_⟩
  · intro a ha ha1
    obtain ⟨x, hxD, rfl⟩ := (fam_mem_img (GLAPPrimeCore p ↥M)).1 ha
    unfold Hbar
    refine iSup_le fun d' => iSup_le fun hd'M => iSup_le fun hd'D => iSup_le fun hmk => ?_
    have hd'1 : d' ≠ 1 := by
      rintro rfl
      apply ha1
      rw [← hmk]
      exact map_one (QuotientGroup.mk' (GLAPPrimeCore p ↥M))
    rw [← hmk]
    exact hcent hd'M hd'D hd'1
  · intro a ha _ e he
    obtain ⟨x, hxD, rfl⟩ := (fam_mem_img (GLAPPrimeCore p ↥M)).1 ha
    obtain ⟨y, hyD, rfl⟩ := (fam_mem_img (GLAPPrimeCore p ↥M)).1 he
    unfold Hbar
    refine fam_normalizer_iSup _ fun d' => fam_normalizer_iSup _ fun hd'M =>
      fam_normalizer_iSup _ fun hd'D => fam_normalizer_iSup _ fun hmk => ?_
    have hyC : (y : G) ∈ Subgroup.centralizer ({d'} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.2 (hDc _ hyD _ hd'D)
    exact fam_img_normalizes (GLAPPrimeCore p ↥M) (le_normalizer_pCoreOf 2 _ hyC)
  · intro a ha _ c hc
    obtain ⟨x, hxD, rfl⟩ := (fam_mem_img (GLAPPrimeCore p ↥M)).1 ha
    unfold Hbar
    refine fam_normalizer_iSup _ fun d' => fam_normalizer_iSup _ fun hd'M =>
      fam_normalizer_iSup _ fun hd'D => fam_normalizer_iSup _ fun hmk => ?_
    rw [← hmk] at hc
    have hd'P : IsPGroup p (Subgroup.zpowers d') := isPGroup_zpowers_of_pow_eq_one' (hDp d' hd'D)
    rw [← fam_barX_centralizer hp hd'M hd'P] at hc
    obtain ⟨z, hz, rfl⟩ := (fam_mem_img (GLAPPrimeCore p ↥M)).1 hc
    exact fam_img_normalizes _ (le_normalizer_pCoreOf 2 _ (Subgroup.mem_inf.1 hz).2)

theorem sigmaFam_hbar (h : IvSetting m p M D L) :
    sigmaFam (barX p M D) (Hbar p M D) = barX p M (sigmaStar D) ∧
      barX p M (gammaD D) ≤ pCoreOf 2 (sigmaFam (barX p M D) (Hbar p M D)) ∧
      ∀ e ∈ barX p M D, e ∈ Subgroup.normalizer
        ((barX p M (gammaD D) : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M)) := by
  have hp : p.Prime := prime_of_standing h.standing
  haveI : Fact p.Prime := ⟨hp⟩
  have hE : IsElemAbelian p D := h.hyp.plane.1
  have hDp : ∀ x ∈ D, x ^ p = 1 := hE.2
  have hsig : sigmaFam (barX p M D) (Hbar p M D) = barX p M (sigmaStar D) := by
    apply le_antisymm
    · unfold sigmaFam
      refine iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => ?_
      obtain ⟨x, hxD, rfl⟩ := (fam_mem_img (GLAPPrimeCore p ↥M)).1 ha
      unfold Hbar
      refine iSup_le fun d' => iSup_le fun hd'M => iSup_le fun hd'D => iSup_le fun hmk => ?_
      have hd'1 : d' ≠ 1 := by
        rintro rfl
        apply ha1
        rw [← hmk]
        exact map_one (QuotientGroup.mk' (GLAPPrimeCore p ↥M))
      unfold sigmaStar
      exact fam_img_mono (GLAPPrimeCore p ↥M)
        (le_iSup_of_le d' (le_iSup_of_le hd'D (le_iSup_of_le hd'1 le_rfl)))
    · have key : sigmaStar D ≤ ((sigmaFam (barX p M D) (Hbar p M D)).comap
          (QuotientGroup.mk' (GLAPPrimeCore p ↥M))).map M.subtype := by
        unfold sigmaStar
        refine iSup_le fun d => iSup_le fun hdD => iSup_le fun hd1 => ?_
        have hdM : d ∈ M := h.hyp.le hdD
        have hA := h.hyp.clause_a d hdD hd1
        intro g hg
        refine Subgroup.mem_map.2 ⟨⟨g, hA hg⟩, Subgroup.mem_comap.2 ?_, rfl⟩
        have hmemT : QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨d, hdM⟩ ∈ barX p M D :=
          Subgroup.mem_map.2 ⟨⟨d, hdM⟩, Subgroup.mem_subgroupOf.2 hdD, rfl⟩
        have hne := fam_barX_mk_ne_one hp hDp hdD hd1 hdM
        have hsub : Hbar p M D (QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨d, hdM⟩) ≤
            sigmaFam (barX p M D) (Hbar p M D) := by
          unfold sigmaFam
          exact le_iSup_of_le (QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨d, hdM⟩)
            (le_iSup_of_le hmemT (le_iSup_of_le hne le_rfl))
        exact hsub (fam_barX_term (p := p) hdM hdD
          (Subgroup.mem_map.2 ⟨⟨g, hA hg⟩, Subgroup.mem_subgroupOf.2 hg, rfl⟩))
      intro z hz
      obtain ⟨w, hw, rfl⟩ := (fam_mem_img (GLAPPrimeCore p ↥M)).1 hz
      obtain ⟨w', hw', hww'⟩ := Subgroup.mem_map.1 (key hw)
      have hw'w : w' = w := Subtype.ext hww'
      rw [Subgroup.mem_comap, hw'w] at hw'
      exact hw'
  refine ⟨hsig, ?_, ?_⟩
  · rw [hsig]
    exact le_trans (fam_img_mono (GLAPPrimeCore p ↥M) (gammaD_le_sigmaOf D))
      (fam_img_pCoreOf_le (GLAPPrimeCore p ↥M) (sigmaStar D))
  · intro e he
    obtain ⟨x, hxD, rfl⟩ := (fam_mem_img (GLAPPrimeCore p ↥M)).1 he
    exact fam_img_normalizes (GLAPPrimeCore p ↥M)
      (normalizer_le_normalizer_gammaD D (Subgroup.le_normalizer hxD))

theorem tl_sigmaOf_eq (h : IvSetting m p M D L) :
    tl M (sigmaOf D) = pCoreOf 2 (sigmaFam (tl M D) (Hfam M D)) := by
  rw [sigmaFam_hfam h]
  exact fam_tl_pCoreOf_eq (sigmaStar_le h.hyp)

end Setting

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
