module

public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2Diagonal
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSwapUnique

public section

namespace CFSG.SeitzReduction.SeitzQ2

open Subgroup
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.EvenSmallLie (StandardSetting)
open scoped commutatorElement

section Generation

variable {G : Type*} [Group G]

theorem iSup_subgroupOf_eq_top {κ : Type*} {L : Subgroup G} {D : κ → Subgroup G}
    (hgen : ⨆ k, D k = L) : ⨆ k, (D k).subgroupOf L = ⊤ := by
  apply Subgroup.map_injective L.subtype_injective
  rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hDL : ∀ k, D k ≤ L := fun k => hgen ▸ le_iSup D k
  simp_rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 (hDL _)]
  exact hgen

theorem iSup_map_conj_eq_of_isSimpleGroup {L D : Subgroup G} (hL : IsSimpleGroup L)
    (hDL : D ≤ L) (hD : D ≠ ⊥) : ⨆ g : L, D.map (MulAut.conj (g : G)).toMonoidHom = L := by
  set N : Subgroup G := ⨆ g : L, D.map (MulAut.conj (g : G)).toMonoidHom with hN
  have hNL : N ≤ L := iSup_le fun g => by
    rintro _ ⟨x, hx, rfl⟩
    exact L.mul_mem (L.mul_mem g.2 (hDL hx)) (L.inv_mem g.2)
  have hDN : D ≤ N := by
    have h1 := le_iSup (fun g : L => D.map (MulAut.conj (g : G)).toMonoidHom) 1
    simp only [OneMemClass.coe_one, map_one] at h1
    intro x hx
    exact h1 ⟨x, hx, by simp⟩
  have hconj : ∀ l : L, N.map (MulAut.conj (l : G)).toMonoidHom ≤ N := by
    intro l
    rw [hN, Subgroup.map_iSup]
    refine iSup_le fun g => ?_
    rw [F4Pilot.map_conj_map_conj_toMonoidHom]
    exact le_iSup (fun g : L => D.map (MulAut.conj (g : G)).toMonoidHom) (l * g)
  have hnorm : (N.subgroupOf L).Normal := by
    refine ⟨fun n hn l => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    exact hconj l ⟨n, hn, by simp [MulAut.conj_apply]⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf L) with h | h
  · exfalso
    apply hD
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hDL hx⟩ : L) ∈ N.subgroupOf L := mem_subgroupOf.2 (hDN hx)
    rw [h, mem_bot] at hx'
    exact (mem_bot).2 (congrArg Subtype.val hx')
  · exact le_antisymm hNL fun x hx => mem_subgroupOf.1 (h ▸ mem_top (⟨x, hx⟩ : L))

end Generation

section Swap

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem le_iSup_centralizerPerfectCore_of_swap (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) {A : Subgroup G} (hq : CFSG.Open.IsQuasisimple A)
    (hA : A.map (MulAut.conj t).toMonoidHom ≤ centralizer (A : Set G))
    (hcard : Nat.card L ≤ Nat.card (A ⧸ center A)) {κ : Type*} (X D : κ → Subgroup G)
    (hXL : ∀ k, X k ≤ L) (hDX : ∀ k, D k ≤ centralizer (X k : Set G))
    (hDperf : ∀ k, ⁅D k, D k⁆ = D k) (hgen : ⨆ k, D k = L) :
    A ≤ ⨆ k, centralizerPerfectCore (X k) := by
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have : Group.IsPerfect A := ⟨hq.1⟩
  have hDL : ∀ k, D k ≤ L := fun k => hgen ▸ le_iSup D k
  set δ := LinearPilot.linearSwapDiag hA with hδdef
  have hperf : ⁅δ.range, δ.range⁆ = δ.range := by
    rw [MonoidHom.range_eq_map]
    exact LinearPilot.commutator_map_eq_of_commutator_eq δ (by
      rw [← _root_.commutator_def]
      exact Group.IsPerfect.commutator_eq_top)
  have hle : δ.range ≤ L :=
    CFSG.SeitzReduction.std_perfect_le hset hOut htC ht hperf
      (LinearPilot.range_linearSwapDiag_le_centralizer htt hA)
  have hrange : δ.range = L := Subgroup.eq_of_le_of_card_ge hle
    (hcard.trans (LinearPilot.card_quotient_center_le_card_range_linearSwapDiag hA))
  have hmemL : ∀ x : A, δ x ∈ L := fun x => hle ⟨x, rfl⟩
  set π : A →* L := δ.codRestrict L hmemL with hπ
  have hπapp : ∀ x : A, (π x : G) = δ x := fun x => rfl
  have hπs : Function.Surjective π := by
    intro z
    obtain ⟨x, hx⟩ : (z : G) ∈ δ.range := hrange ▸ z.2
    exact ⟨x, Subtype.ext hx⟩
  have hπker : π.ker ≤ center A := by
    intro x hx
    apply LinearPilot.ker_linearSwapDiag_le_center hA
    rw [MonoidHom.mem_ker] at hx ⊢
    exact congrArg Subtype.val hx
  set C : κ → Subgroup A := fun k => perfectCore (((D k).subgroupOf L).comap π) with hC
  have hCnb : ∀ k, (C k).map A.subtype ≤ centralizerPerfectCore (X k) := by
    intro k
    have hperfC : ⁅(C k).map A.subtype, (C k).map A.subtype⁆ = (C k).map A.subtype := by
      rw [← map_commutator, CFSG.Quasithin.perfectCore_perfect]
    refine F4Pilot.le_centralizerPerfectCore hperfC ?_
    set T : Subgroup A := ((X k).subgroupOf L).comap π with hT
    have hCT : (C k).map A.subtype ≤ centralizer ((T.map A.subtype : Subgroup G) : Set G) := by
      refine LinearPilot.le_centralizer_of_commutator_le_center (M := A) (map_subtype_le _)
        hperfC ?_
      rw [Subgroup.commutator_le]
      rintro _ ⟨c, hc, rfl⟩ _ ⟨x, hx, rfl⟩
      have hcD : ((π c : L) : G) ∈ D k := mem_subgroupOf.1
        (mem_comap.1 (CFSG.Quasithin.perfectCore_le (((D k).subgroupOf L).comap π) hc))
      have hxX : ((π x : L) : G) ∈ X k := mem_subgroupOf.1 hx
      have hcomm : π ⁅c, x⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact Subtype.ext ((mem_centralizer_iff.1 (hDX k hcD) _ hxX).symm)
      exact ⟨⁅c, x⁆, hπker hcomm, rfl⟩
    intro w hw
    rw [mem_centralizer_iff]
    intro y hy
    obtain ⟨c, hc, rfl⟩ := hw
    obtain ⟨x, hx⟩ : y ∈ δ.range := hrange ▸ hXL k hy
    have hxT : x ∈ T := by
      change ((π x : L) : G) ∈ X k
      rw [hπapp, hx]
      exact hy
    have h1 : (x : G) * c = c * x := mem_centralizer_iff.1 (hCT ⟨c, hc, rfl⟩) _ ⟨x, hxT, rfl⟩
    have h2 : (c : G) * (t * x * t⁻¹) = (t * x * t⁻¹) * c :=
      mem_centralizer_iff.1 (hA ⟨x, x.2, rfl⟩) c c.2
    rw [← hx, hδdef, LinearPilot.linearSwapDiag_apply]
    change (x : G) * (t * x * t⁻¹) * c = c * (x * (t * x * t⁻¹))
    calc (x : G) * (t * x * t⁻¹) * c = x * ((t * x * t⁻¹) * c) := by group
      _ = x * (c * (t * x * t⁻¹)) := by rw [h2]
      _ = (x * c) * (t * x * t⁻¹) := by group
      _ = (c * x) * (t * x * t⁻¹) := by rw [h1]
      _ = c * (x * (t * x * t⁻¹)) := by group
  have hgenA : (⨆ k, C k) = ⊤ := by
    refine LinearPilot.eq_top_of_sup_center_eq_top_of_perfect ?_
    have hi : ∀ k, (C k).map π = (D k).subgroupOf L := by
      intro k
      rw [hC, CFSG.Quasithin.map_perfectCore, Subgroup.map_comap_eq_self_of_surjective hπs,
        CFSG.Quasithin.perfectCore_eq_self_of_perfect
          (CFSG.SeitzReduction.commutator_subgroupOf_eq_self (hDL k) (hDperf k))]
    have hmap : (⨆ k, C k).map π = ⊤ := by
      rw [Subgroup.map_iSup]
      simp_rw [hi]
      exact iSup_subgroupOf_eq_top hgen
    refine eq_top_iff.2 ?_
    calc (⊤ : Subgroup A) = (⨆ k, C k) ⊔ π.ker := by
          rw [← Subgroup.comap_map_eq, hmap, Subgroup.comap_top]
      _ ≤ (⨆ k, C k) ⊔ center A := sup_le_sup_left hπker _
  intro g hg
  have hmem : (⟨g, hg⟩ : A) ∈ ⨆ k, C k := hgenA ▸ mem_top _
  have h2 : g ∈ (⨆ k, C k).map A.subtype := ⟨⟨g, hg⟩, hmem, rfl⟩
  rw [Subgroup.map_iSup] at h2
  exact (iSup_mono hCnb) h2

theorem conjugate_eq_of_swap_of_neighbours (hset : SeitzSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) {G₁ : Subgroup G} (hq : CFSG.Open.IsQuasisimple G₁)
    (h₁₂ : G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G))
    (hδ : ∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L) (hsurj : ∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y)
    {κ : Type*} (X D : κ → Subgroup G) (hXL : ∀ k, X k ≤ L)
    (hDX : ∀ k, D k ≤ centralizer (X k : Set G)) (hDperf : ∀ k, ⁅D k, D k⁆ = D k)
    (hgen : ⨆ k, D k = L)
    (hE : ∀ k, centralizerPerfectCore (X k) ≤ G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom) (h : G)
    (hswap : (CFSG.conjugate G₁ h).map (MulAut.conj t).toMonoidHom =
      CFSG.conjugate (G₁.map (MulAut.conj t).toMonoidHom) h) :
    CFSG.conjugate (G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom) h =
      G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom := by
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hcard₁ := LinearPilot.card_quotient_center_eq_of_swapFactors hset.center_eq_bot h₁₂ hδ
    hsurj
  have hA : (CFSG.conjugate G₁ h).map (MulAut.conj t).toMonoidHom ≤
      centralizer (CFSG.conjugate G₁ h : Set G) := by
    rw [hswap]
    exact LinearPilot.conjugate_le_centralizer_of_le_centralizer h₁₂ h
  have hcardA : Nat.card L ≤ Nat.card (CFSG.conjugate G₁ h ⧸ center (CFSG.conjugate G₁ h)) := by
    rw [← Nat.card_congr (LinearPilot.conjugateQuotientCenterEquiv G₁ h).toEquiv, hcard₁]
  have hAle := (le_iSup_centralizerPerfectCore_of_swap hset.standardSetting hOut htC ht
    (LinearPilot.isQuasisimple_conjugate hq h) hA hcardA X D hXL hDX hDperf hgen).trans
    (iSup_le hE)
  have htG₀ : t ∈ normalizer ((G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) :=
    F4Pilot.mem_normalizer_sup_of_map_conj_eq htt rfl
  have hBle : CFSG.conjugate (G₁.map (MulAut.conj t).toMonoidHom) h ≤
      G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom := by
    rw [← hswap]
    calc (CFSG.conjugate G₁ h).map (MulAut.conj t).toMonoidHom
        ≤ (G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom :=
          map_mono hAle
      _ = G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom :=
          F4Pilot.mem_normalizer_iff_map_conj_toMonoidHom.1 htG₀
  have hle : CFSG.conjugate (G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom) h ≤
      G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom := by
    rw [CFSG.conjugate, Subgroup.map_sup]
    exact sup_le hAle hBle
  exact Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective).ge

end Swap

section Unique

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem unique_of_swapFactors_of_neighbours (hset : SeitzSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) {G₁ : Subgroup G} (hq : CFSG.Open.IsQuasisimple G₁)
    (h₁₂ : G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G))
    (hδ : ∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L) (hsurj : ∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y)
    {κ : Type*} (X D : κ → Subgroup G) (hXL : ∀ k, X k ≤ L)
    (hDX : ∀ k, D k ≤ centralizer (X k : Set G)) (hDperf : ∀ k, ⁅D k, D k⁆ = D k)
    (hgen : ⨆ k, D k = L)
    (hE : ∀ k, centralizerPerfectCore (X k) ≤ G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom)
    (hnorm : ∀ h : G, t ∈ normalizer (CFSG.conjugate G₁ h : Set G) →
      t ∈ normalizer (CFSG.conjugate (G₁.map (MulAut.conj t).toMonoidHom) h : Set G) →
      t ∉ centralizer (CFSG.conjugate G₁ h : Set G) →
      t ∉ centralizer (CFSG.conjugate (G₁.map (MulAut.conj t).toMonoidHom) h : Set G) →
      False) :
    ∀ g : G, g⁻¹ * t * g ∈
        normalizer ((G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) →
      g ∈ normalizer ((G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
  have hcard₁ := LinearPilot.card_quotient_center_eq_of_swapFactors hset.center_eq_bot h₁₂ hδ
    hsurj
  refine F4Pilot.unique_of_forall_conjugate_eq fun h htM => ?_
  have hM : CFSG.conjugate (G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom) h =
      CFSG.conjugate G₁ h ⊔ CFSG.conjugate (G₁.map (MulAut.conj t).toMonoidHom) h :=
    Subgroup.map_sup _ _ _
  rw [hM] at htM
  have hqA := LinearPilot.isQuasisimple_conjugate hq h
  have hqB := LinearPilot.isQuasisimple_conjugate (LinearPilot.isQuasisimple_map_conj hq t) h
  have hAB := LinearPilot.conjugate_le_centralizer_of_le_centralizer h₁₂ h
  have hBA := le_centralizer_iff.1 hAB
  obtain ⟨hpA, hbA, hnA⟩ := F4Pilot.perfect_ne_bot_dichotomy_of_isQuasisimple hqA
  obtain ⟨hpB, hbB, hnB⟩ := F4Pilot.perfect_ne_bot_dichotomy_of_isQuasisimple hqB
  rcases F4Pilot.map_conj_eq_or_eq_of_perfect hAB hpA hbA hnA hnB htM with hAA | hswap
  ·
    rcases F4Pilot.map_conj_eq_or_eq_of_perfect hBA hpB hbB hnB hnA
        (by rw [sup_comm]; exact htM) with hBB | hBA'
    · exfalso
      have hBconj := LinearPilot.map_conj_conjugate_eq (A := G₁) h t
      have hAconj : (CFSG.conjugate (G₁.map (MulAut.conj t).toMonoidHom) h).map
          (MulAut.conj (h⁻¹ * t * h)⁻¹).toMonoidHom = CFSG.conjugate G₁ h :=
        F4Pilot.map_conj_eq_of_map_conj_inv_eq (by rw [inv_inv]; exact hBconj)
      have hcardA : Nat.card L ≤ Nat.card (CFSG.conjugate G₁ h) := by
        rw [← hcard₁, Nat.card_congr (LinearPilot.conjugateQuotientCenterEquiv G₁ h).toEquiv,
          Subgroup.card_eq_card_quotient_mul_card_subgroup (center (CFSG.conjugate G₁ h))]
        exact Nat.le_mul_of_pos_right _ Nat.card_pos
      have hcardB : Nat.card L ≤
          Nat.card (CFSG.conjugate (G₁.map (MulAut.conj t).toMonoidHom) h) := by
        rw [← hBconj, Subgroup.card_map_of_injective (MulAut.conj _).injective]
        exact hcardA
      refine hnorm h (F4Pilot.mem_normalizer_iff_map_conj_toMonoidHom.2 hAA)
        (F4Pilot.mem_normalizer_iff_map_conj_toMonoidHom.2 hBB) ?_ ?_
      · exact LinearPilot.not_mem_centralizer_of_conj_le_centralizer hset hOut htC ht hpA hcardA
          _ (hBconj ▸ hAB)
      · exact LinearPilot.not_mem_centralizer_of_conj_le_centralizer hset hOut htC ht hpB hcardB
          _ (hAconj ▸ hBA)
    ·
      exfalso
      have hAB' : CFSG.conjugate (G₁.map (MulAut.conj t).toMonoidHom) h = CFSG.conjugate G₁ h :=
        F4Pilot.map_conj_toMonoidHom_inj.1 (hBA'.trans hAA.symm)
      rw [hAB'] at hAB
      exact hbA (by rw [← hpA, commutator_eq_bot_iff_le_centralizer.2 hAB])
  · exact conjugate_eq_of_swap_of_neighbours hset hOut htC ht hq h₁₂ hδ hsurj X D hXL hDX hDperf
      hgen hE h hswap

theorem nonSwap_of_factorNormal (hset : SeitzSetting G L) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hloc : ∀ A : Subgroup G, CFSG.Open.IsQuasisimple A → Odd (Nat.card (center A)) →
      (∃ φ : A →* L, Function.Surjective φ ∧ φ.ker ≤ center A) →
      ∀ g : G, A.map (MulAut.conj g).toMonoidHom ≤ centralizer (A : Set G) →
        t ∈ normalizer (A : Set G) →
        t ∈ normalizer ((A.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) →
        t ∉ centralizer (A : Set G) →
        t ∉ centralizer ((A.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) → False)
    {G₁ : Subgroup G} (hq : CFSG.Open.IsQuasisimple G₁)
    (h₁₂ : G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G))
    (hδ : ∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L) (hsurj : ∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y) :
    ∀ h : G, t ∈ normalizer (CFSG.conjugate G₁ h : Set G) →
      t ∈ normalizer (CFSG.conjugate (G₁.map (MulAut.conj t).toMonoidHom) h : Set G) →
      t ∉ centralizer (CFSG.conjugate G₁ h : Set G) →
      t ∉ centralizer (CFSG.conjugate (G₁.map (MulAut.conj t).toMonoidHom) h : Set G) →
      False := by
  have hodd := UnitaryPilot.odd_card_center_of_swapFactors hset.center_eq_bot ht hKt hq h₁₂ hδ
    hsurj
  intro h htA htB hnA hnB
  have hBconj := LinearPilot.map_conj_conjugate_eq (A := G₁) h t
  have hoddA : Odd (Nat.card (center (CFSG.conjugate G₁ h))) := by
    rw [← Nat.card_congr (Subgroup.centerCongr (LinearPilot.conjugateEquiv G₁ h)).toEquiv]
    exact hodd
  refine hloc (CFSG.conjugate G₁ h) (LinearPilot.isQuasisimple_conjugate hq h) hoddA
    (LinearPilot.exists_surjective_conjugate_of_linearSwapDiag h₁₂ hδ hsurj h) (h⁻¹ * t * h) ?_
    htA ?_ hnA ?_
  · rw [hBconj]
    exact LinearPilot.conjugate_le_centralizer_of_le_centralizer h₁₂ h
  · rw [hBconj]
    exact htB
  · rw [hBconj]
    exact hnB

theorem unique_of_swapFactors_of_neighbours_of_factorNormal (hset : SeitzSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hloc : ∀ A : Subgroup G, CFSG.Open.IsQuasisimple A → Odd (Nat.card (center A)) →
      (∃ φ : A →* L, Function.Surjective φ ∧ φ.ker ≤ center A) →
      ∀ g : G, A.map (MulAut.conj g).toMonoidHom ≤ centralizer (A : Set G) →
        t ∈ normalizer (A : Set G) →
        t ∈ normalizer ((A.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) →
        t ∉ centralizer (A : Set G) →
        t ∉ centralizer ((A.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) → False)
    {G₁ : Subgroup G} (hq : CFSG.Open.IsQuasisimple G₁)
    (h₁₂ : G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G))
    (hδ : ∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L) (hsurj : ∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y)
    {κ : Type*} (X D : κ → Subgroup G) (hXL : ∀ k, X k ≤ L)
    (hDX : ∀ k, D k ≤ centralizer (X k : Set G)) (hDperf : ∀ k, ⁅D k, D k⁆ = D k)
    (hgen : ⨆ k, D k = L)
    (hE : ∀ k, centralizerPerfectCore (X k) ≤ G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom) :
    ∀ g : G, g⁻¹ * t * g ∈
        normalizer ((G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) →
      g ∈ normalizer ((G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) :=
  unique_of_swapFactors_of_neighbours hset hOut (LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt)
    ht hq h₁₂ hδ hsurj X D hXL hDX hDperf hgen hE
    (nonSwap_of_factorNormal hset ht hKt hloc hq h₁₂ hδ hsurj)

end Unique

section Endgame

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem isSimpleGroup_of_seitzSetting (hset : SeitzSetting G L) : IsSimpleGroup L := by
  have : IsSimpleGroup (L ⧸ center L) := hset.standardSetting.standard.1.2
  exact ((QuotientGroup.quotientBot (G := L)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hset.center_eq_bot.symm)).isSimpleGroup

omit [Finite G] in
theorem le_sup_map_conj_of_surj {t : G} {G₁ : Subgroup G}
    (hsurj : ∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y) :
    L ≤ G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hsurj y hy
  exact mul_mem (mem_sup_left hx) (mem_sup_right ⟨x, hx, rfl⟩)

theorem unique_of_swapFactors_of_neighbour (hset : SeitzSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) {G₁ : Subgroup G} (hq : CFSG.Open.IsQuasisimple G₁)
    (h₁₂ : G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G))
    (hδ : ∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L) (hsurj : ∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y)
    {X D : Subgroup G} (hXL : X ≤ L) (hDL : D ≤ L) (hDX : D ≤ centralizer (X : Set G))
    (hDperf : ⁅D, D⁆ = D) (hD : D ≠ ⊥)
    (hE : centralizerPerfectCore X ≤ G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom)
    (hnorm : ∀ h : G, t ∈ normalizer (CFSG.conjugate G₁ h : Set G) →
      t ∈ normalizer (CFSG.conjugate (G₁.map (MulAut.conj t).toMonoidHom) h : Set G) →
      t ∉ centralizer (CFSG.conjugate G₁ h : Set G) →
      t ∉ centralizer (CFSG.conjugate (G₁.map (MulAut.conj t).toMonoidHom) h : Set G) →
      False) :
    ∀ g : G, g⁻¹ * t * g ∈
        normalizer ((G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) →
      g ∈ normalizer ((G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
  have hL := isSimpleGroup_of_seitzSetting hset
  have hLG₀ := le_sup_map_conj_of_surj (L := L) hsurj
  refine unique_of_swapFactors_of_neighbours hset hOut htC ht hq h₁₂ hδ hsurj
    (fun g : L => X.map (MulAut.conj (g : G)).toMonoidHom)
    (fun g : L => D.map (MulAut.conj (g : G)).toMonoidHom) (fun g => ?_) (fun g => ?_)
    (fun g => ?_) (iSup_map_conj_eq_of_isSimpleGroup hL hDL hD) (fun g => ?_) hnorm
  · rintro _ ⟨x, hx, rfl⟩
    exact L.mul_mem (L.mul_mem g.2 (hXL hx)) (L.inv_mem g.2)
  · rintro _ ⟨d, hd, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    have hxd : x * d = d * x := mem_centralizer_iff.1 (hDX hd) x hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc (g : G) * x * (g : G)⁻¹ * ((g : G) * d * (g : G)⁻¹) = g * (x * d) * (g : G)⁻¹ := by
          group
      _ = g * (d * x) * (g : G)⁻¹ := by rw [hxd]
      _ = (g : G) * d * (g : G)⁻¹ * ((g : G) * x * (g : G)⁻¹) := by group
  · rw [← map_commutator, hDperf]
  · rw [← F4Pilot.map_centralizerPerfectCore (MulAut.conj (g : G)) X]
    calc (centralizerPerfectCore X).map (MulAut.conj (g : G)).toMonoidHom
        ≤ (G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom).map (MulAut.conj (g : G)).toMonoidHom :=
          map_mono hE
      _ = G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom :=
          F4Pilot.mem_normalizer_iff_map_conj_toMonoidHom.1 (le_normalizer (hLG₀ g.2))

theorem false_of_swapFactors_of_neighbours (hset : SeitzSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) {G₁ : Subgroup G} (hq : CFSG.Open.IsQuasisimple G₁)
    (h₁₂ : G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G))
    (hδ : ∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L) (hsurj : ∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y)
    {κ : Type*} (X D : κ → Subgroup G) (hXL : ∀ k, X k ≤ L)
    (hDX : ∀ k, D k ≤ centralizer (X k : Set G)) (hDperf : ∀ k, ⁅D k, D k⁆ = D k)
    (hgen : ⨆ k, D k = L)
    (hE : ∀ k, centralizerPerfectCore (X k) ≤ G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom)
    (hnorm : ∀ h : G, t ∈ normalizer (CFSG.conjugate G₁ h : Set G) →
      t ∈ normalizer (CFSG.conjugate (G₁.map (MulAut.conj t).toMonoidHom) h : Set G) →
      t ∉ centralizer (CFSG.conjugate G₁ h : Set G) →
      t ∉ centralizer (CFSG.conjugate (G₁.map (MulAut.conj t).toMonoidHom) h : Set G) →
      False) : False := by
  have : IsSimpleGroup G := hset.1
  exact F4Pilot.false_of_simple_of_swap_of_isQuasisimple ht hq h₁₂ rfl
    (unique_of_swapFactors_of_neighbours hset hOut htC ht hq h₁₂ hδ hsurj X D hXL hDX hDperf hgen
      hE hnorm)

end Endgame

section Assembly

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem false_of_coherent_swapParam_of_overlaps (hset : SeitzSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hloc : ∀ A : Subgroup G, CFSG.Open.IsQuasisimple A → Odd (Nat.card (center A)) →
      (∃ φ : A →* L, Function.Surjective φ ∧ φ.ker ≤ center A) →
      ∀ g : G, A.map (MulAut.conj g).toMonoidHom ≤ centralizer (A : Set G) →
        t ∈ normalizer (A : Set G) →
        t ∈ normalizer ((A.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) →
        t ∉ centralizer (A : Set G) →
        t ∉ centralizer ((A.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) → False)
    {ι κ : Type*} {D : ι → Subgroup G} (P : ∀ a, SwapParam t (D a)) (O : κ → Subgroup G)
    (ν : κ → ι) (hOν : ∀ k, O k ≤ D (ν k)) (hOperf : ∀ k, ⁅O k, O k⁆ = O k)
    (hpair : ∀ k l, ∃ a, O k ≤ D a ∧ O l ≤ D a ∧ AgreeOn (P (ν k)) (P a) (O k) ∧
      AgreeOn (P (ν l)) (P a) (O l))
    (hgen : ⨆ k, O k = L) (X : κ → Subgroup G) (hXL : ∀ k, X k ≤ L)
    (hOX : ∀ k, O k ≤ centralizer (X k : Set G))
    (hM : ∀ k, centralizerPerfectCore (X k) =
      (((O k).subgroupOf (D (ν k))).prod ((O k).subgroupOf (D (ν k)))).map (P (ν k)).Ψ) :
    False := by
  have hL := isSimpleGroup_of_seitzSetting hset
  obtain ⟨hq, h₁₂, hδ, hsurj, hpiece⟩ := isQuasisimple_iSup_fst P hL O ν hOν hOperf hpair hgen
  have htC := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  exact false_of_swapFactors_of_neighbours hset hOut htC ht hq h₁₂ hδ hsurj X O hXL hOX hOperf hgen
    (fun k => (hM k).trans_le (hpiece k)) (nonSwap_of_factorNormal hset ht hKt hloc hq h₁₂ hδ hsurj)

end Assembly

end CFSG.SeitzReduction.SeitzQ2
