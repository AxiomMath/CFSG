module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieLift
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCore
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieIdx
public import CFSG.GroupTheory.ElemAbelianRank
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_10FiCover
public import CFSG.LieType.Simplicity.Classical
public import CFSG.Adapters.LinearCatalogStated
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TableGeneric
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.RankThree.GroupTheory.ComponentCubeObstruction
public import CFSG.GroupTheory.CommutingProductFixedSubgroup

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.PerfectAutomorphisms

variable {Y : Type} [Group Y] [Finite Y]

private theorem card_B_eq_pow_mul_card_centralizer {K B : Subgroup Y}
    (hBN : B ≤ Subgroup.normalizer (K : Set Y)) {p m : ℕ} {S : Type} [Group S]
    (eK : ↥K ⧸ Subgroup.center ↥K ≃* S) (hperf : Group.IsPerfect ↥K)
    (hcardrange : Nat.card (kd264Rho hBN eK).range = p ^ m) :
    Nat.card B = p ^ m * Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) := by
  have h := card_range_kd264Rho_mul hperf hBN eK
  rw [hcardrange] at h
  exact h.symm

private theorem card_le_pow_pRank_center_of_le_center {K : Subgroup Y} {p : ℕ} (hp : p.Prime)
    {F : Subgroup Y} (hF : IsElemAbelian p F)
    (hFZ : F ≤ (Subgroup.center ↥K).map K.subtype) :
    Nat.card F ≤ p ^ CFSG.Open.pRank p (Subgroup.center ↥K) := by
  have hp1 : 1 < p := hp.one_lt
  let F' : Subgroup ↥K := F.comap K.subtype
  have hFrange : F ≤ K.subtype.range := by
    rw [Subgroup.range_subtype]
    exact hFZ.trans (Subgroup.map_subtype_le _)
  have hF'map : F'.map K.subtype = F := Subgroup.map_comap_eq_self hFrange
  have hF'el : IsElemAbelian p F' := hF.subgroupOf K
  have hF'le : F' ≤ Subgroup.center ↥K := by
    have h := Subgroup.comap_mono (f := K.subtype) hFZ
    rwa [Subgroup.comap_map_eq_self_of_injective K.subtype_injective] at h
  have hcard : Nat.card F' = Nat.card F := by
    rw [← hF'map, Subgroup.card_map_of_injective K.subtype_injective]
  calc Nat.card F = Nat.card F' := hcard.symm
    _ = p ^ CFSG.Open.pRank p F' := CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian hp hF'el
    _ ≤ p ^ CFSG.Open.pRank p (Subgroup.center ↥K) :=
      Nat.pow_le_pow_right hp.pos (CFSG.SectionRank.pRank_mono hp1 hF'le)

private theorem not_mem_sup_of_rho_not_inner {K B : Subgroup Y}
    (hBN : B ≤ Subgroup.normalizer (K : Set Y)) {S : Type} [Group S]
    (eK : ↥K ⧸ Subgroup.center ↥K ≃* S) {b : ↥B}
    (h : kd264Rho hBN eK b ∉ (MulAut.conj : S →* MulAut S).range) :
    (b : Y) ∉ K ⊔ (B ⊓ Subgroup.centralizer (K : Set Y)) := by
  intro hbmem
  have hcommKC : ∀ k ∈ K, ∀ c ∈ B ⊓ Subgroup.centralizer (K : Set Y), k * c = c * k := by
    intro k hk c hc
    exact Subgroup.mem_centralizer_iff.1 hc.2 k hk
  obtain ⟨k, hkK, c, hcC, hkc⟩ :=
    CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcommKC hbmem
  have hcK : c ∈ Subgroup.centralizer (K : Set Y) := hcC.2
  have hcB : c ∈ B := hcC.1
  have hkB : k ∈ B := by
    have hk_eq : k = (b : Y) * c⁻¹ := by rw [← hkc]; group
    rw [hk_eq]
    exact B.mul_mem b.2 (B.inv_mem hcB)
  have hconj : ∀ y ∈ K, (b : Y)⁻¹ * y * (b : Y) = k⁻¹ * y * k := by
    intro y hy
    have hcy : c * y = y * c := (Subgroup.mem_centralizer_iff.1 hcK y hy).symm
    have hckyk : c * (k⁻¹ * y * k) = (k⁻¹ * y * k) * c :=
      (Subgroup.mem_centralizer_iff.1 hcK (k⁻¹ * y * k)
        (K.mul_mem (K.mul_mem (K.inv_mem hkK) hy) hkK)).symm
    calc (b : Y)⁻¹ * y * (b : Y) = c⁻¹ * (k⁻¹ * y * k) * c := by rw [← hkc]; group
      _ = c⁻¹ * ((k⁻¹ * y * k) * c) := by group
      _ = c⁻¹ * (c * (k⁻¹ * y * k)) := by rw [hckyk]
      _ = k⁻¹ * y * k := by group
  exact h (kd264Rho_mem_range_conj hBN eK b ⟨k, hkK⟩ hconj)

private theorem onCenterQuotient_normalizerConjAutOfMem {K B : Subgroup Y}
    (hBN : B ≤ Subgroup.normalizer (K : Set Y)) (b : ↥B) :
    onCenterQuotient (normalizerConjAutOfMem K B hBN b) =
      normalizerToCenterQuotientAut K B hBN b := by
  rfl

private theorem pRank_top_eq_of_center_eq_bot {K : Subgroup Y} {p : ℕ}
    {S : Type} [Group S] [Finite S]
    {eK : ↥K ⧸ Subgroup.center ↥K ≃* S}
    (hZ : Subgroup.center ↥K = ⊥) (hp : p.Prime) :
    CFSG.Open.pRank p (⊤ : Subgroup S) = CFSG.Open.pRank p (⊤ : Subgroup ↥K) := by
  let eK' : ↥K ≃* S :=
    (QuotientGroup.quotientBot (G := ↥K)).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hZ).symm.trans eK)
  exact (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt eK').symm

private theorem isSimpleGroup_lie_of_lpEpsIdx {p : ℕ} (e : TauCeti.ValidLieTypeIndex)
    (h : lpEpsIdx p e.1) : IsSimpleGroup (TauCeti.CFSGIndex.lie e).Group := by
  obtain ⟨d, hv⟩ := e
  obtain ⟨q, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩ := h
  · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity _ _ _ _
      (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv (MulEquiv.refl _))).2
  · exact (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ _ _ _
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA _ _ hv (MulEquiv.refl _))).2

theorem kd264LiftLow_holds (hI5 : KD264I5Low) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    KD264LiftLow p := by
  intro Y instY finY K B hBN d instD eK m hq hB hmax hcardrange k hk
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  have hperf : Group.IsPerfect ↥K := ⟨hq.1⟩
  set C : Subgroup Y := B ⊓ Subgroup.centralizer (K : Set Y) with hCdef
  have hBcard : Nat.card B = p ^ m * Nat.card ↥C :=
    card_B_eq_pow_mul_card_centralizer hBN eK hperf hcardrange
  set z : ℕ := CFSG.Open.pRank p (Subgroup.center ↥K) with hzdef
  set M : ℕ := CFSG.Open.pRank p (⊤ : Subgroup ↥K) with hMdef
  obtain ⟨E₀, -, hE₀el, hE₀card⟩ := CFSG.SectionRank.exists_pRank hp1 (⊤ : Subgroup ↥K)
  set E : Subgroup Y := E₀.map K.subtype with hEdef
  have hEK : E ≤ K := Subgroup.map_subtype_le _
  have hEel : IsElemAbelian p E := hE₀el.map K.subtype
  have hEcard : Nat.card E = p ^ M := by
    rw [hEdef, Subgroup.card_map_of_injective K.subtype_injective, hE₀card, hMdef]
  have hEC : E ⊓ C ≤ (Subgroup.center ↥K).map K.subtype := by
    rw [CFSG.center_map_subtype_eq_inf_centralizer]
    intro x hx
    exact ⟨hEK hx.1, (inf_le_right : B ⊓ Subgroup.centralizer (K : Set Y) ≤ Subgroup.centralizer (K : Set Y)) hx.2⟩
  have hECcard : Nat.card ↥(E ⊓ C) ≤ p ^ z :=
    card_le_pow_pRank_center_of_le_center hp (hEel.mono inf_le_left) hEC
  have hMR := kd264_rank_ineq hp hB hmax (b := (1 : Y)) (A := E) B.one_mem hEel hEK
    (by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      simp) (Or.inl rfl)
  have hMR' : Nat.card E * Nat.card ↥C ≤ Nat.card B * Nat.card ↥(E ⊓ C) := by
    simpa [hCdef] using hMR
  have h1 : p ^ M * Nat.card ↥C ≤ p ^ m * Nat.card ↥C * p ^ z := by
    calc p ^ M * Nat.card ↥C = Nat.card E * Nat.card ↥C := by rw [hEcard]
      _ ≤ Nat.card B * Nat.card ↥(E ⊓ C) := hMR'
      _ = (p ^ m * Nat.card ↥C) * Nat.card ↥(E ⊓ C) := by rw [hBcard]
      _ ≤ (p ^ m * Nat.card ↥C) * p ^ z := Nat.mul_le_mul_left _ hECcard
  have hCpos : 0 < Nat.card ↥C := Nat.card_pos
  have h1' : p ^ M * Nat.card ↥C ≤ (p ^ m * p ^ z) * Nat.card ↥C := by
    calc p ^ M * Nat.card ↥C ≤ (p ^ m * Nat.card ↥C) * p ^ z := h1
      _ = p ^ m * (Nat.card ↥C * p ^ z) := by rw [mul_assoc]
      _ = (p ^ m * p ^ z) * Nat.card ↥C := by rw [mul_comm (Nat.card ↥C) (p ^ z), mul_assoc]
  have h2 : p ^ M ≤ p ^ m * p ^ z :=
    Nat.le_of_mul_le_mul_right h1' hCpos
  have h3 : p ^ M ≤ p ^ (m + z) := by simpa [pow_add] using h2
  have h4 : M ≤ m + z := (Nat.pow_le_pow_iff_right hp1).1 h3
  have hi5 : k + z ≤ M := by
    have h := hI5 p hp hp2 ↥K hq d k hk ⟨eK⟩
    simpa [hzdef, hMdef] using h
  omega

private theorem noMult_pRank_top_le {K B : Subgroup Y}
    (hBN : B ≤ Subgroup.normalizer (K : Set Y)) {p m : ℕ} (hp : p.Prime)
    {S : Type} [Group S] [Finite S] (eK : ↥K ⧸ Subgroup.center ↥K ≃* S)
    (hperf : Group.IsPerfect ↥K) (hB : IsElemAbelian p B) (hmax : IsMaxRankIn p B ⊤)
    (hcardrange : Nat.card (kd264Rho hBN eK).range = p ^ m)
    (hZ : Subgroup.center ↥K = ⊥) :
    CFSG.Open.pRank p (⊤ : Subgroup S) ≤ m := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  set C : Subgroup Y := B ⊓ Subgroup.centralizer (K : Set Y) with hCdef
  have hBcard : Nat.card B = p ^ m * Nat.card ↥C :=
    card_B_eq_pow_mul_card_centralizer hBN eK hperf hcardrange
  have hEq : CFSG.Open.pRank p (⊤ : Subgroup S) =
      CFSG.Open.pRank p (⊤ : Subgroup ↥K) := pRank_top_eq_of_center_eq_bot (eK := eK) hZ hp
  set M : ℕ := CFSG.Open.pRank p (⊤ : Subgroup ↥K) with hMdef
  obtain ⟨E₀, -, hE₀el, hE₀card⟩ := CFSG.SectionRank.exists_pRank hp1 (⊤ : Subgroup ↥K)
  set E : Subgroup Y := E₀.map K.subtype with hEdef
  have hEK : E ≤ K := Subgroup.map_subtype_le _
  have hEel : IsElemAbelian p E := hE₀el.map K.subtype
  have hEcard : Nat.card E = p ^ M := by
    rw [hEdef, Subgroup.card_map_of_injective K.subtype_injective, hE₀card, hMdef]
  have hEC : E ⊓ C ≤ (Subgroup.center ↥K).map K.subtype := by
    rw [CFSG.center_map_subtype_eq_inf_centralizer]
    intro x hx
    exact ⟨hEK hx.1, (inf_le_right : B ⊓ Subgroup.centralizer (K : Set Y) ≤
      Subgroup.centralizer (K : Set Y)) hx.2⟩
  have hECbot : E ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    exact hEC.trans (by rw [hZ, Subgroup.map_bot])
  have hMR := kd264_rank_ineq hp hB hmax (b := (1 : Y)) (A := E) B.one_mem hEel hEK
    (by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      simp) (Or.inl rfl)
  have hMR' : p ^ M * Nat.card ↥C ≤ p ^ m * Nat.card ↥C := by
    have h := hMR
    rw [hEcard, hBcard, hECbot] at h
    simpa [hCdef] using h
  have hCpos : 0 < Nat.card ↥C := Nat.card_pos
  have h2 : p ^ M ≤ p ^ m := Nat.le_of_mul_le_mul_right hMR' hCpos
  have h3 : M ≤ m := (Nat.pow_le_pow_iff_right hp1).1 h2
  rw [hEq, hMdef]
  exact h3

private theorem noMult_outer_rank {K B : Subgroup Y}
    (hBN : B ≤ Subgroup.normalizer (K : Set Y)) {S : Type} [Group S] [Finite S]
    {p m : ℕ} (hp : p.Prime) (eK : ↥K ⧸ Subgroup.center ↥K ≃* S)
    (hperf : Group.IsPerfect ↥K) (hB : IsElemAbelian p B)
    (hmax : IsMaxRankIn p B ⊤) (hcardrange : Nat.card (kd264Rho hBN eK).range = p ^ m)
    (hZ : Subgroup.center ↥K = ⊥) :
    ∀ a ∈ (kd264Rho hBN eK).range, a ∉ (MulAut.conj : S →* MulAut S).range →
      ∀ E : Subgroup S, E ≤ fixSubgroup a → IsElemAbelian p E →
        CFSG.Open.pRank p E + 1 ≤ m := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  set C : Subgroup Y := B ⊓ Subgroup.centralizer (K : Set Y) with hCdef
  have hBcard : Nat.card B = p ^ m * Nat.card ↥C :=
    card_B_eq_pow_mul_card_centralizer hBN eK hperf hcardrange
  intro a ha hainner E hEfix hEel
  rw [hCdef] at *
  obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp ha
  have hcommKC : ∀ k ∈ K, ∀ c ∈ B ⊓ Subgroup.centralizer (K : Set Y), k * c = c * k := by
    intro k hk c hc
    exact Subgroup.mem_centralizer_iff.1 hc.2 k hk
  have hbnot := not_mem_sup_of_rho_not_inner hBN eK (b := b) (by simpa [hb] using hainner)
  have hb1 : (b : Y) ≠ 1 := by
    intro hb1
    exact hbnot (hb1 ▸ Subgroup.mem_sup_left K.one_mem)
  have hbpow : (b : Y) ^ p = 1 := hB.2 b b.2
  have hcardb : Nat.card (Subgroup.zpowers (b : Y)) = p := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hbpow hb1
  let π : ↥K →* S :=
    eK.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))
  have hπker : π.ker ≤ Subgroup.center ↥K := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx' : (QuotientGroup.mk' (Subgroup.center ↥K)) x = 1 := by
      apply eK.injective
      simpa [π] using hx
    exact (QuotientGroup.eq_one_iff x).1 (by simpa using hx')
  have hπsurj : Function.Surjective π :=
    eK.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center ↥K))
  have hπinj : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hxZ : x ∈ Subgroup.center ↥K := hπker hx
    rw [hZ] at hxZ
    exact hxZ
  set E' : Subgroup ↥K := E.comap π with hE'def
  have hE'map : E'.map π = E := Subgroup.map_comap_eq_self_of_surjective hπsurj E
  have hE'el : IsElemAbelian p E' := by simpa [hE'def] using hEel.comap hπinj
  have hE'card : Nat.card E' = Nat.card E := by
    rw [← hE'map, Subgroup.card_map_of_injective hπinj]
  have hE'Yel : IsElemAbelian p (E'.map K.subtype) := hE'el.map K.subtype
  have hE'Ycard : Nat.card (E'.map K.subtype) = Nat.card E := by
    rw [Subgroup.card_map_of_injective K.subtype_injective, hE'card]
  have hE'fix : E' ≤ fixSubgroup (normalizerConjAutOfMem K B hBN b) := by
    intro x hx
    rw [mem_fixSubgroup]
    apply hπinj
    change eK ((QuotientGroup.mk' (Subgroup.center ↥K))
      ((normalizerConjAutOfMem K B hBN b) x)) = π x
    rw [normalizerConjAutOfMem_comp_mk]
    have hxE : π x ∈ E := by rw [← hE'map]; exact Subgroup.mem_map_of_mem π hx
    have hax : a (π x) = π x := hEfix hxE
    rw [show eK ((normalizerToCenterQuotientAut K B hBN b)
        ((QuotientGroup.mk' (Subgroup.center ↥K)) x)) =
        (kd264Rho hBN eK b) (eK ((QuotientGroup.mk' (Subgroup.center ↥K)) x)) by
      simp [kd264Rho, MulAut.congr_apply]]
    rw [hb]
    exact hax
  have hE'cent : E'.map K.subtype ≤ Subgroup.centralizer ({(b : Y)} : Set Y) := by
    have hsub : E'.map K.subtype ≤ (fixSubgroup (normalizerConjAutOfMem K B hBN b)).map K.subtype :=
      Subgroup.map_mono hE'fix
    have hsub' : E'.map K.subtype ≤
        (fixSubgroup ((Subgroup.normalizerMonoidHom (H := K)) ⟨(b : Y), hBN b.2⟩)).map K.subtype :=
      hsub
    change E'.map K.subtype ≤ Subgroup.map K.subtype
      (MonoidHom.eqLocus ((Subgroup.normalizerMonoidHom (H := K)) ⟨(b : Y), hBN b.2⟩).toMonoidHom
        (MonoidHom.id ↥K)) at hsub'
    rw [CFSG.map_eqLocus_normalizerMonoidHom K (hBN b.2)] at hsub'
    exact hsub'.trans inf_le_right
  have hEC' : (E'.map K.subtype) ⊓ (B ⊓ Subgroup.centralizer (K : Set Y)) ≤
      (Subgroup.center ↥K).map K.subtype := by
    rw [CFSG.center_map_subtype_eq_inf_centralizer]
    intro x hx
    exact ⟨Subgroup.map_subtype_le _ hx.1,
      (inf_le_right : B ⊓ Subgroup.centralizer (K : Set Y) ≤
        Subgroup.centralizer (K : Set Y)) hx.2⟩
  have hEC'bot : (E'.map K.subtype) ⊓ (B ⊓ Subgroup.centralizer (K : Set Y)) = ⊥ := by
    rw [eq_bot_iff]
    exact hEC'.trans (by rw [hZ, Subgroup.map_bot])
  have hMR := kd264_rank_ineq hp hB hmax (b := (b : Y)) b.2
    (A := E'.map K.subtype) hE'Yel (Subgroup.map_subtype_le _) hE'cent (Or.inr hbnot)
  have hMR' : Nat.card E * Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) * p ≤
      p ^ m * Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) := by
    have h := hMR
    rw [hE'Ycard, hcardb, hBcard, hEC'bot, Subgroup.card_bot, mul_one] at h
    simpa using h
  have hMR'' : (Nat.card E * p) * Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) ≤
      p ^ m * Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) := by
    calc (Nat.card E * p) * Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) =
        Nat.card E * Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) * p := by ring
      _ ≤ p ^ m * Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) := hMR'
  have h2 : p ^ CFSG.Open.pRank p E * p ≤ p ^ m := by
    rw [← CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian hp hEel]
    exact Nat.le_of_mul_le_mul_right hMR'' Nat.card_pos
  have h3 : p ^ (CFSG.Open.pRank p E + 1) ≤ p ^ m := by
    simpa [pow_succ] using h2
  have h4 : CFSG.Open.pRank p E + 1 ≤ m := (Nat.pow_le_pow_iff_right hp1).1 h3
  exact h4

theorem kd264LiftNoMult_holds {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hMult : KD264MultLie p) : KD264LiftNoMult p := by
  intro Y instY finY K B hBN d instD eK m hq hcore hB hmax hcardrange hpchar hnotmult
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hperf : Group.IsPerfect ↥K := ⟨hq.1⟩
  have hZp : IsPGroup p (Subgroup.center ↥K) :=
    isPGroup_center_of_pPrimeCore_eq_bot hp hcore
  have hZ : Subgroup.center ↥K = ⊥ := by
    by_contra hne
    exact hnotmult (hMult ↥K hq d ⟨eK⟩ hpchar hZp hne)
  have hSrank : CFSG.Open.pRank p (⊤ : Subgroup (TauCeti.CFSGIndex.lie d).Group) ≤ m :=
    noMult_pRank_top_le (p := p) (S := (TauCeti.CFSGIndex.lie d).Group)
      hBN hp eK hperf hB hmax hcardrange hZ
  exact ⟨hSrank, noMult_outer_rank hBN hp eK hperf hB hmax hcardrange hZ⟩

private theorem field_beta_data {K B : Subgroup Y}
    (hBN : B ≤ Subgroup.normalizer (K : Set Y)) {S : Type} [Group S]
    {p : ℕ} (hp3 : p = 3) (hB : IsElemAbelian p B)
    (eK : ↥K ⧸ Subgroup.center ↥K ≃* S) {a : MulAut S}
    (ha : a ∈ (kd264Rho hBN eK).range) (haout : a ∉ innAutDerived S) :
    ∃ b : ↥B, kd264Rho hBN eK b = a ∧ (b : Y) ^ 3 = 1 ∧
      (normalizerConjAutOfMem K B hBN b) ^ 3 = 1 ∧
      onCenterQuotient (normalizerConjAutOfMem K B hBN b) ∉
        innAutDerived (↥K ⧸ Subgroup.center ↥K) := by
  obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp ha
  have hb3Y : (b : Y) ^ 3 = 1 := by simpa [hp3] using hB.2 b b.2
  have hb3 : (b : ↥B) ^ 3 = 1 := Subtype.ext (by simpa using hb3Y)
  have hβ3 : (normalizerConjAutOfMem K B hBN b) ^ 3 = 1 := by
    have hhom : normalizerConjAutOfMem K B hBN b =
        ((Subgroup.normalizerMonoidHom (H := K)).comp (Subgroup.inclusion hBN)) b := rfl
    rw [hhom, ← map_pow, hb3, map_one]
  have hβout : onCenterQuotient (normalizerConjAutOfMem K B hBN b) ∉
      innAutDerived (↥K ⧸ Subgroup.center ↥K) := by
    intro hmem
    apply haout
    have hconj : MulAut.congr eK (onCenterQuotient (normalizerConjAutOfMem K B hBN b)) = a := by
      rw [onCenterQuotient_normalizerConjAutOfMem]
      rw [← hb]
      rfl
    rw [← hconj]
    have hmapmem : MulAut.congr eK (onCenterQuotient (normalizerConjAutOfMem K B hBN b)) ∈
        (innAutDerived (↥K ⧸ Subgroup.center ↥K)).map (MulAut.congr eK).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hmem
    rwa [map_innAutDerived_congr eK] at hmapmem
  exact ⟨b, hb, hb3Y, hβ3, hβout⟩

theorem kd264LiftField_holds (hI5F : KD264I5Field) {p : ℕ} (hp : p.Prime) :
    KD264LiftField p := by
  intro Y instY finY K B hBN d instD eK m hq hB hmax hcardrange hp3 a ha haout k hk
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  have hperf : Group.IsPerfect ↥K := ⟨hq.1⟩
  subst hp3
  set C : Subgroup Y := B ⊓ Subgroup.centralizer (K : Set Y) with hCdef
  have hBcard : Nat.card B = 3 ^ m * Nat.card ↥C :=
    card_B_eq_pow_mul_card_centralizer hBN eK hperf hcardrange
  obtain ⟨b, hb, hb3Y, hβ3, hβout⟩ := field_beta_data hBN rfl hB eK ha haout
  have hb1 : (b : Y) ≠ 1 := by
    intro hb1
    exact (not_mem_sup_of_rho_not_inner hBN eK (b := b) (by
      intro hinner
      exact haout (by
        have hinner' : kd264Rho hBN eK b ∈ innAutDerived (TauCeti.CFSGIndex.lie d).Group :=
          inner_le_innAutDerived _ hinner
        rwa [hb] at hinner'))) (hb1 ▸ Subgroup.mem_sup_left K.one_mem)
  have hcardb : Nat.card (Subgroup.zpowers (b : Y)) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hb3Y hb1
  obtain ⟨E, hEfix, hEel, hErank⟩ :=
    hI5F ↥K hq d k hk ⟨eK⟩ (normalizerConjAutOfMem K B hBN b) hβ3 hβout
  set z : ℕ := CFSG.Open.pRank 3 (Subgroup.center ↥K) with hzdef
  set A : Subgroup Y := E.map K.subtype with hAdef
  have hAK : A ≤ K := Subgroup.map_subtype_le _
  have hAel : IsElemAbelian 3 A := hEel.map K.subtype
  have hAcard : Nat.card A = 3 ^ CFSG.Open.pRank 3 E := by
    rw [hAdef, Subgroup.card_map_of_injective K.subtype_injective,
      CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian (by norm_num) hEel]
  have hnotinner : kd264Rho hBN eK b ∉ (MulAut.conj :
      (TauCeti.CFSGIndex.lie d).Group →* MulAut (TauCeti.CFSGIndex.lie d).Group).range := by
    intro hinner
    have hinner' : kd264Rho hBN eK b ∈ innAutDerived (TauCeti.CFSGIndex.lie d).Group :=
      inner_le_innAutDerived _ hinner
    exact haout (by rwa [hb] at hinner')
  have hbnot := not_mem_sup_of_rho_not_inner hBN eK (b := b) hnotinner
  have hb1 : (b : Y) ≠ 1 := by
    intro hb1
    exact hbnot (hb1 ▸ Subgroup.mem_sup_left K.one_mem)
  have hcardb : Nat.card (Subgroup.zpowers (b : Y)) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hb3Y hb1
  have hAcent : A ≤ Subgroup.centralizer ({(b : Y)} : Set Y) := by
    have hsub : A ≤ (fixSubgroup (normalizerConjAutOfMem K B hBN b)).map K.subtype := by
      rw [hAdef]
      exact Subgroup.map_mono hEfix
    change A ≤ Subgroup.map K.subtype
      (MonoidHom.eqLocus ((Subgroup.normalizerMonoidHom (H := K)) ⟨(b : Y), hBN b.2⟩).toMonoidHom
        (MonoidHom.id ↥K)) at hsub
    rw [CFSG.map_eqLocus_normalizerMonoidHom K (hBN b.2)] at hsub
    exact hsub.trans inf_le_right
  have hEC : A ⊓ C ≤ (Subgroup.center ↥K).map K.subtype := by
    rw [CFSG.center_map_subtype_eq_inf_centralizer]
    intro x hx
    exact ⟨hAK hx.1, (inf_le_right : B ⊓ Subgroup.centralizer (K : Set Y) ≤
      Subgroup.centralizer (K : Set Y)) hx.2⟩
  have hECcard : Nat.card ↥(A ⊓ C) ≤ 3 ^ z :=
    card_le_pow_pRank_center_of_le_center (p := 3) (by norm_num) (hAel.mono inf_le_left) hEC
  have hMR := kd264_rank_ineq (p := 3) (by norm_num) hB hmax (b := (b : Y)) b.2
    (A := A) hAel hAK hAcent (Or.inr hbnot)
  have hMR' : Nat.card A * Nat.card ↥C * 3 ≤ 3 ^ m * Nat.card ↥C * 3 ^ z := by
    calc Nat.card A * Nat.card ↥C * 3 =
        Nat.card A * Nat.card ↥C * Nat.card (Subgroup.zpowers (b : Y)) := by rw [hcardb]
      _ ≤ Nat.card B * Nat.card ↥(A ⊓ C) := hMR
      _ ≤ (3 ^ m * Nat.card ↥C) * 3 ^ z := by
        rw [hBcard]
        exact Nat.mul_le_mul_left _ hECcard
  have hpow : 3 ^ (k + z) ≤ Nat.card A := by
    calc 3 ^ (k + z) ≤ 3 ^ CFSG.Open.pRank 3 E :=
          Nat.pow_le_pow_right (by norm_num) hErank
      _ = Nat.card A := hAcard.symm
  have h1 : 3 ^ (k + z) * Nat.card ↥C * 3 ≤ 3 ^ m * Nat.card ↥C * 3 ^ z := by
    calc 3 ^ (k + z) * Nat.card ↥C * 3 ≤ Nat.card A * Nat.card ↥C * 3 :=
          Nat.mul_le_mul_right 3 (Nat.mul_le_mul_right (Nat.card ↥C) hpow)
      _ ≤ 3 ^ m * Nat.card ↥C * 3 ^ z := hMR'
  have hCpos : 0 < Nat.card ↥C := Nat.card_pos
  have h1' : 3 ^ (k + z) * 3 * Nat.card ↥C ≤ 3 ^ m * 3 ^ z * Nat.card ↥C := by
    calc 3 ^ (k + z) * 3 * Nat.card ↥C = 3 ^ (k + z) * Nat.card ↥C * 3 := by ring
      _ ≤ 3 ^ m * Nat.card ↥C * 3 ^ z := h1
      _ = 3 ^ m * 3 ^ z * Nat.card ↥C := by ring
  have h2 : 3 ^ (k + z) * 3 ≤ 3 ^ m * 3 ^ z :=
    Nat.le_of_mul_le_mul_right h1' hCpos
  have h3 : 3 ^ (k + z + 1) ≤ 3 ^ (m + z) := by
    calc 3 ^ (k + z + 1) = 3 ^ (k + z) * 3 := by ring_nf
      _ ≤ 3 ^ m * 3 ^ z := h2
      _ = 3 ^ (m + z) := by rw [pow_add]
  have h4 : k + z + 1 ≤ m + z := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 h3
  omega

private theorem mrj_component_lift {K : Subgroup Y} {S : Type} [Group S] [Finite S]
    {p : ℕ} (hp : p.Prime) {α : MulAut ↥K} {β : MulAut S} {π : ↥K →* S}
    (hπker : π.ker ≤ Subgroup.center ↥K) (hπsurj : Function.Surjective π)
    (hαβ : ∀ k : ↥K, π (α k) = β (π k))
    {J : Subgroup S} (hJ : GLAPComponent p (fixSubgroup β) J)
    {e : TauCeti.ValidLieTypeIndex}
    (e0 : ↥J ⧸ Subgroup.center ↥J ≃* (TauCeti.CFSGIndex.lie e).Group)
    (hliesimple : IsSimpleGroup (TauCeti.CFSGIndex.lie e).Group) :
    ∃ Jt : Subgroup ↥K, GLAPComponent p (fixSubgroup α) Jt ∧ Jt.map π = J ∧
      CFSG.Open.IsQuasisimple ↥Jt ∧
      Nonempty (↥Jt ⧸ Subgroup.center ↥Jt ≃* (TauCeti.CFSGIndex.lie e).Group) := by
  obtain ⟨Jt, hJt, hJtmap⟩ :=
    exists_glaPComponent_map_fixSubgroup π hπker α β hαβ hπsurj hp hJ
  have hJtperf : Group.IsPerfect ↥Jt :=
    Subgroup.isPerfect_iff.mpr (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJt)
  let f : ↥Jt →* ↥J :=
    (MulEquiv.subgroupCongr hJtmap).toMonoidHom.comp (π.subgroupMap Jt)
  have hf : Function.Surjective f :=
    (MulEquiv.subgroupCongr hJtmap).surjective.comp (MonoidHom.subgroupMap_surjective π Jt)
  have hker : f.ker ≤ Subgroup.center ↥Jt := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hx1 : π x = 1 := by
      have hx' : (π.subgroupMap Jt) x = 1 := by
        apply (MulEquiv.subgroupCongr hJtmap).injective
        simpa [f] using hx
      simpa using congrArg Subtype.val hx'
    have hxK : (x : ↥K) ∈ Subgroup.center ↥K := hπker (MonoidHom.mem_ker.mpr hx1)
    exact Subtype.ext (Subgroup.mem_center_iff.mp hxK (y : ↥K))
  have hcenter : (Subgroup.center ↥J).comap f = Subgroup.center ↥Jt :=
    CFSG.LocalCores.comap_center_eq_of_perfect hJtperf f hf hker
  have hc : Subgroup.center ↥Jt =
      ((QuotientGroup.mk' (Subgroup.center ↥J)).comp f).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', hcenter]
  let eZ : (↥Jt ⧸ Subgroup.center ↥Jt) ≃* (↥J ⧸ Subgroup.center ↥J) :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans
      (QuotientGroup.quotientKerEquivOfSurjective _
        ((QuotientGroup.mk'_surjective _).comp hf))
  have hJsimple : IsSimpleGroup (↥J ⧸ Subgroup.center ↥J) :=
    (MulEquiv.isSimpleGroup_congr e0).2 hliesimple
  have hJtq : CFSG.Open.IsQuasisimple ↥Jt :=
    ⟨hJtperf.commutator_eq_top, (MulEquiv.isSimpleGroup_congr eZ).2 hJsimple⟩
  exact ⟨Jt, hJt, hJtmap, hJtq, ⟨eZ.trans e0⟩⟩

private theorem mrj_C'_card {K B C : Subgroup Y} {p : ℕ} (hp : p.Prime)
    (hB : IsElemAbelian p B) (hCB : C ≤ B)
    (hCK : C ≤ Subgroup.centralizer (K : Set Y))
    {b : ↥B} (hbC : (b : Y) ∉ C) (hbpow : (b : Y) ^ p = 1)
    {Jt : Subgroup ↥K}
    (hJYcent : Jt.map K.subtype ≤ Subgroup.centralizer ({(b : Y)} : Set Y)) :
    Nat.card ↥C * p ≤
      Nat.card ↥(B ⊓ Subgroup.centralizer (Jt.map K.subtype : Set Y)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hb1 : (b : Y) ≠ 1 := by
    intro hb1'
    exact hbC (hb1' ▸ C.one_mem)
  have hcardb : Nat.card (Subgroup.zpowers (b : Y)) = p := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hbpow hb1
  set JY : Subgroup Y := Jt.map K.subtype with hJYdef
  set C' : Subgroup Y := B ⊓ Subgroup.centralizer (JY : Set Y) with hC'def
  have hC'le : C ⊔ Subgroup.zpowers (b : Y) ≤ C' := by
    refine sup_le ?_ ?_
    · intro c hc
      refine ⟨hCB hc, ?_⟩
      change c ∈ Subgroup.centralizer (JY : Set Y)
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      exact Subgroup.mem_centralizer_iff.1 (hCK hc) j (Subgroup.map_subtype_le _ hj)
    · intro x hx
      rw [Subgroup.mem_zpowers_iff] at hx
      obtain ⟨n, rfl⟩ := hx
      have hbJY : (b : Y) ∈ Subgroup.centralizer (JY : Set Y) := by
        rw [Subgroup.mem_centralizer_iff]
        intro j hj
        exact (Subgroup.mem_centralizer_iff.1 (hJYcent hj) b (Set.mem_singleton (b : Y))).symm
      exact ⟨B.zpow_mem (show (b : Y) ∈ B from b.2) n,
        (Subgroup.centralizer (JY : Set Y)).zpow_mem hbJY n⟩
  have hdisj : Disjoint C (Subgroup.zpowers (b : Y)) := by
    rw [disjoint_iff]
    have h := CFSG.RankThree.zpowers_inf_eq_bot_of_not_mem hp
      (orderOf_eq_prime hbpow hb1) (S := C) hbC
    rwa [inf_comm] at h
  have hnorm : Subgroup.zpowers (b : Y) ≤ Subgroup.normalizer (C : Set Y) := by
    have hcomm : Subgroup.zpowers (b : Y) ≤ Subgroup.centralizer (C : Set Y) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      have hbc : b * c = c * b := hB.comm b.2 (hCB hc)
      rw [Subgroup.mem_zpowers_iff] at hx
      obtain ⟨n, rfl⟩ := hx
      exact (Commute.zpow_left hbc n).eq.symm
    exact hcomm.trans (Subgroup.centralizer_le_normalizer (C : Set Y))
  have hsupcard : Nat.card ↥(C ⊔ Subgroup.zpowers (b : Y)) = Nat.card ↥C * p := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer C
      (Subgroup.zpowers (b : Y)) hnorm hdisj, hcardb]
  calc Nat.card ↥C * p = Nat.card ↥(C ⊔ Subgroup.zpowers (b : Y)) := hsupcard.symm
    _ ≤ Nat.card ↥C' := Subgroup.card_le_of_le hC'le
    _ = Nat.card ↥(B ⊓ Subgroup.centralizer (Jt.map K.subtype : Set Y)) := by rw [hC'def, hJYdef]

private theorem mrj_rank_step {K B C : Subgroup Y} {p m : ℕ} (hp : p.Prime)
    (hB : IsElemAbelian p B) (hmax : IsMaxRankIn p B ⊤) (hCB : C ≤ B)
    (hCK : C ≤ Subgroup.centralizer (K : Set Y))
    (hBcard : Nat.card B = p ^ m * Nat.card ↥C)
    {b : ↥B} (hbC : (b : Y) ∉ C) (hbpow : (b : Y) ^ p = 1)
    {Jt : Subgroup ↥K}
    (hJYcent : Jt.map K.subtype ≤ Subgroup.centralizer ({(b : Y)} : Set Y))
    (hi5 : p - 2 + CFSG.Open.pRank p (Subgroup.center ↥Jt) ≤
      CFSG.Open.pRank p (⊤ : Subgroup ↥Jt)) :
    p - 1 ≤ m := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  set M : ℕ := CFSG.Open.pRank p (⊤ : Subgroup ↥Jt) with hMdef
  set z : ℕ := CFSG.Open.pRank p (Subgroup.center ↥Jt) with hzdef
  have hi5' : p - 2 + z ≤ M := by simpa [hzdef, hMdef] using hi5
  obtain ⟨E, -, hEel, hEcard⟩ := CFSG.SectionRank.exists_pRank hp1 (⊤ : Subgroup ↥Jt)
  set A : Subgroup Y := (E.map Jt.subtype).map K.subtype with hAdef
  have hAel : IsElemAbelian p A := (hEel.map Jt.subtype).map K.subtype
  have hAcard : Nat.card A = p ^ M := by
    rw [hAdef, Subgroup.card_map_of_injective K.subtype_injective,
      Subgroup.card_map_of_injective Jt.subtype_injective, hEcard, hMdef]
  set JY : Subgroup Y := Jt.map K.subtype with hJYdef
  have hAJY : A ≤ JY := by
    rw [hAdef, hJYdef]
    exact Subgroup.map_mono (Subgroup.map_subtype_le E)
  have hAcent : A ≤ Subgroup.centralizer ({(b : Y)} : Set Y) :=
    hAJY.trans hJYcent
  set C' : Subgroup Y := B ⊓ Subgroup.centralizer (JY : Set Y) with hC'def
  have hC'card : Nat.card ↥C * p ≤ Nat.card ↥C' := by
    simpa [hJYdef, hC'def] using mrj_C'_card hp hB hCB hCK hbC hbpow hJYcent
  have hAC' : A ⊓ C' ≤ (Subgroup.center ↥JY).map JY.subtype := by
    rw [CFSG.center_map_subtype_eq_inf_centralizer]
    intro x hx
    exact ⟨hAJY hx.1, hx.2.2⟩
  have hAC'card : Nat.card ↥(A ⊓ C') ≤ p ^ CFSG.Open.pRank p (Subgroup.center ↥JY) :=
    card_le_pow_pRank_center_of_le_center hp (hAel.mono inf_le_left) hAC'
  have hzJY : CFSG.Open.pRank p (Subgroup.center ↥JY) = z := by
    let eJ : ↥Jt ≃* ↥JY := Subgroup.equivMapOfInjective Jt K.subtype K.subtype_injective
    have hmap : (Subgroup.center ↥Jt).map eJ.toMonoidHom = Subgroup.center ↥JY :=
      Subgroup.map_center_eq eJ
    rw [← hmap, CFSG.HardMathSupport.Timmesfeld.ComponentBalance.pRank_map_mulEquiv hp1 eJ, hzdef]
  have hMR := kd264_rank_ineq hp hB hmax (b := (1 : Y)) B.one_mem (A := A) hAel hAJY
    (by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      simp) (Or.inl rfl)
  have hMR' : Nat.card A * Nat.card ↥C' ≤ Nat.card B * Nat.card ↥(A ⊓ C') := by
    change Nat.card A * Nat.card ↥(B ⊓ Subgroup.centralizer (JY : Set Y)) ≤
      Nat.card B * Nat.card ↥(A ⊓ (B ⊓ Subgroup.centralizer (JY : Set Y)))
    simpa using hMR
  have h1 : p ^ M * (Nat.card ↥C * p) ≤ p ^ m * Nat.card ↥C * p ^ z := by
    calc p ^ M * (Nat.card ↥C * p) = Nat.card A * (Nat.card ↥C * p) := by rw [hAcard]
      _ ≤ Nat.card A * Nat.card ↥C' := Nat.mul_le_mul_left _ hC'card
      _ ≤ Nat.card B * Nat.card ↥(A ⊓ C') := hMR'
      _ ≤ (p ^ m * Nat.card ↥C) * p ^ z := by
        rw [hBcard]
        exact Nat.mul_le_mul_left _ (by rwa [hzJY] at hAC'card)
  have hCpos : 0 < Nat.card ↥C := Nat.card_pos
  have h1' : (p ^ M * p) * Nat.card ↥C ≤ (p ^ m * p ^ z) * Nat.card ↥C := by
    calc (p ^ M * p) * Nat.card ↥C = p ^ M * (Nat.card ↥C * p) := by ring
      _ ≤ p ^ m * Nat.card ↥C * p ^ z := h1
      _ = (p ^ m * p ^ z) * Nat.card ↥C := by ring
  have h2 : p ^ M * p ≤ p ^ m * p ^ z := Nat.le_of_mul_le_mul_right h1' hCpos
  have h3 : p ^ (M + 1) ≤ p ^ (m + z) := by
    calc p ^ (M + 1) = p ^ M * p := by rw [pow_succ]
      _ ≤ p ^ m * p ^ z := h2
      _ = p ^ (m + z) := by rw [pow_add]
  have h4 : M + 1 ≤ m + z := (Nat.pow_le_pow_iff_right hp1).1 h3
  omega

theorem kd264LiftMRJ_holds (hI5 : KD264I5Low) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    KD264LiftMRJ p := by
  intro Y instY finY K B hBN d instD eK m hq hB hmax hcardrange β hβ hβ1 J hJ e he hlp
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  have hperf : Group.IsPerfect ↥K := ⟨hq.1⟩
  set C : Subgroup Y := B ⊓ Subgroup.centralizer (K : Set Y) with hCdef
  have hBcard : Nat.card B = p ^ m * Nat.card ↥C :=
    card_B_eq_pow_mul_card_centralizer hBN eK hperf hcardrange
  obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hβ
  have hbC : (b : Y) ∉ C := by
    intro hbCin
    have hbker : b ∈ (kd264Rho hBN eK).ker := by
      rw [ker_kd264Rho hperf hBN eK]
      exact hbCin
    exact hβ1 (by rw [← hb]; exact MonoidHom.mem_ker.mp hbker)
  have hb1 : (b : Y) ≠ 1 := by
    intro hb1'
    exact hbC (hb1' ▸ C.one_mem)
  have hbpow : (b : Y) ^ p = 1 := hB.2 b b.2
  have hcardb : Nat.card (Subgroup.zpowers (b : Y)) = p := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hbpow hb1
  let α : MulAut ↥K := normalizerConjAutOfMem K B hBN b
  let π : ↥K →* (TauCeti.CFSGIndex.lie d).Group :=
    eK.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))
  have hπker : π.ker ≤ Subgroup.center ↥K := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx' : (QuotientGroup.mk' (Subgroup.center ↥K)) x = 1 := by
      apply eK.injective
      simpa [π] using hx
    exact (QuotientGroup.eq_one_iff x).1 (by simpa using hx')
  have hπsurj : Function.Surjective π :=
    eK.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center ↥K))
  have hαβ : ∀ k : ↥K, π (α k) = β (π k) := by
    intro k
    change eK ((QuotientGroup.mk' (Subgroup.center ↥K)) ((normalizerConjAutOfMem K B hBN b) k)) =
      β (eK ((QuotientGroup.mk' (Subgroup.center ↥K)) k))
    rw [normalizerConjAutOfMem_comp_mk]
    rw [show eK ((normalizerToCenterQuotientAut K B hBN b)
        ((QuotientGroup.mk' (Subgroup.center ↥K)) k)) =
        (kd264Rho hBN eK b) (eK ((QuotientGroup.mk' (Subgroup.center ↥K)) k)) by
      simp [kd264Rho, MulAut.congr_apply]]
    rw [hb]
  obtain ⟨e0⟩ := he
  have hliesimple : IsSimpleGroup (TauCeti.CFSGIndex.lie e).Group :=
    isSimpleGroup_lie_of_lpEpsIdx e hlp
  obtain ⟨Jt, hJt, hJtmap, hJtq, hJiso⟩ :=
    mrj_component_lift hp hπker hπsurj hαβ hJ e0 hliesimple
  obtain ⟨eZ⟩ := hJiso
  have hi5 : p - 2 + CFSG.Open.pRank p (Subgroup.center ↥Jt) ≤
      CFSG.Open.pRank p (⊤ : Subgroup ↥Jt) := by
    have h := hI5 p hp hp2 ↥Jt hJtq e (p - 2) (i5LowBound_of_lpEpsIdx hlp) ⟨eZ⟩
    simpa using h
  have hJYcent : Jt.map K.subtype ≤ Subgroup.centralizer ({(b : Y)} : Set Y) := by
    have hsub : Jt.map K.subtype ≤ (fixSubgroup α).map K.subtype :=
      Subgroup.map_mono hJt.1
    change Jt.map K.subtype ≤ Subgroup.map K.subtype
      (MonoidHom.eqLocus ((Subgroup.normalizerMonoidHom (H := K)) ⟨(b : Y), hBN b.2⟩).toMonoidHom
        (MonoidHom.id ↥K)) at hsub
    rw [CFSG.map_eqLocus_normalizerMonoidHom K (hBN b.2)] at hsub
    exact hsub.trans inf_le_right
  exact mrj_rank_step hp hB hmax (hCdef.le.trans inf_le_left) (hCdef.le.trans inf_le_right)
    hBcard hbC hbpow hJYcent hi5

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
