module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieCaseBIso
public import CFSG.LocalAnalysis.AGLEmbedding.UPrimeComponents
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNTwoAClassAux
import CFSG.LocalAnalysis.AGLEmbedding.OneLieConfig

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

theorem simple_of_center_eq_bot {Y : Type} [Group Y] {L : Subgroup Y}
    (hL : IsComponentOf L ⊤) (hZ : Subgroup.center L = ⊥)
    (hcat : IsCatalogGroup (L ⧸ Subgroup.center L)) :
    IsSimpleGroup L ∧ (∃ a b : L, a * b ≠ b * a) ∧ IsCatalogGroup L := by
  let e : L ≃* L ⧸ Subgroup.center L :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  refine ⟨isSimpleGroup_of_center_eq_bot hL hZ, ?_, IsCatalogGroup.of_mulEquiv e hcat⟩
  obtain ⟨a, b, hab⟩ :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian L hL.2.2
  refine ⟨e.symm a, e.symm b, fun hba => hab ?_⟩
  simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg e hba

theorem isSimpleGroup_of_centralizer_eq_bot {Y : Type} [Group Y] {L : Subgroup Y}
    (hL : IsComponentOf L ⊤) (hCL : Subgroup.centralizer (L : Set Y) = ⊥)
    (hcat : IsCatalogGroup (L ⧸ Subgroup.center L)) :
    IsSimpleGroup L ∧ (∃ a b : L, a * b ≠ b * a) ∧ IsCatalogGroup L := by
  have hZ : Subgroup.center L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxC : (x : Y) ∈ Subgroup.centralizer (L : Set Y) :=
      Subgroup.mem_centralizer_iff.mpr fun l hl =>
        congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨l, hl⟩)
    rw [hCL, Subgroup.mem_bot] at hxC
    exact Subgroup.mem_bot.mpr (Subtype.ext hxC)
  exact simple_of_center_eq_bot hL hZ hcat

structure D1OneLieEscData {G : Type} [Group G] [Finite G] (p : ℕ) (P : Sylow p G)
    (M H R : Subgroup G) (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) (P' : Sylow p G)
    (H₁ S : Subgroup G) : Prop where
  data : D1OneLieData p P M H R Rbar K
  escape : D1Escape p P' M H₁ S
  nclIn_le : nclIn H (d1LiftX p H R K) ≤ H₁

namespace D1OneLieEscData

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {P' : Sylow p G}
  {H₁ S : Subgroup G}

theorem symm_apply_of_mulEquiv (hc : D1OneLieEscData p P M H R Rbar K P' H₁ S)
    {L : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)} (ψ : L ≃* K)
    (hψ : ∀ (j : G) (hj : j ∈ nclIn H (d1LiftX p H R K))
      (hjL : QuotientGroup.mk' (primeComplementCore (G := H₁) p) ⟨j, hc.nclIn_le hj⟩ ∈ L),
      ((ψ ⟨_, hjL⟩ : K) : H ⧸ primeComplementCore (G := H) p) =
        QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨j, nclIn_le_self H _ hj⟩)
    {j : G} (hj : j ∈ nclIn H (d1LiftX p H R K))
    (hjL : QuotientGroup.mk' (primeComplementCore (G := H₁) p) ⟨j, hc.nclIn_le hj⟩ ∈ L)
    (hjK : QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨j, nclIn_le_self H _ hj⟩ ∈ K) :
    ψ.symm ⟨_, hjK⟩ = ⟨_, hjL⟩ := by
  apply ψ.injective
  rw [MulEquiv.apply_symm_apply]
  exact Subtype.ext (hψ j hj hjL).symm

theorem mem_of_mulEquiv (hc : D1OneLieEscData p P M H R Rbar K P' H₁ S)
    {L : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)}
    (hJL : ((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) = L) (ψ : L ≃* K)
    (hψ : ∀ (j : G) (hj : j ∈ nclIn H (d1LiftX p H R K))
      (hjL : QuotientGroup.mk' (primeComplementCore (G := H₁) p) ⟨j, hc.nclIn_le hj⟩ ∈ L),
      ((ψ ⟨_, hjL⟩ : K) : H ⧸ primeComplementCore (G := H) p) =
        QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨j, nclIn_le_self H _ hj⟩)
    (ℓ : L) (hℓ : ((ψ ℓ : K) : H ⧸ primeComplementCore (G := H) p) ∈
      ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p))) :
    (ℓ : H₁ ⧸ primeComplementCore (G := H₁) p) ∈
      ((H₁ ⊓ M).subgroupOf H₁).map (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) := by
  have hd := hc.data
  have hℓJ : (ℓ : H₁ ⧸ primeComplementCore (G := H₁) p) ∈
      ((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
        (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) := hJL ▸ ℓ.2
  obtain ⟨j', hj', hjℓ⟩ := hℓJ
  have hjJ : (j' : G) ∈ nclIn H (d1LiftX p H R K) := hj'
  have hℓeq : ℓ = ⟨QuotientGroup.mk' (primeComplementCore (G := H₁) p) ⟨j', hc.nclIn_le hjJ⟩,
      hjℓ ▸ ℓ.2⟩ := Subtype.ext hjℓ.symm
  rw [hℓeq, hψ j' hjJ] at hℓ
  obtain ⟨m, hm, hmj⟩ := hℓ
  have hn : (m : G)⁻¹ * j' ∈ GLBPrimeCore p H :=
    (mk'_primeComplementCore_eq_one_iff p (m⁻¹ * ⟨j', nclIn_le_self H _ hjJ⟩)).mp
      (by rw [map_mul, map_inv, hmj, inv_mul_cancel])
  have hmM : (m : G) ∈ M := (Subgroup.mem_subgroupOf.mp hm).2
  have hjM : (j' : G) ∈ M := by
    have e : (j' : G) = m * ((m : G)⁻¹ * j') := by group
    rw [e]
    exact M.mul_mem hmM (hd.cfg.ext.primeCore_le hn)
  exact ⟨j', Subgroup.mem_subgroupOf.mpr ⟨j'.2, hjM⟩, hjℓ⟩

theorem not_le_of_mulEquiv (hc : D1OneLieEscData p P M H R Rbar K P' H₁ S)
    {L : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)}
    (hJL : ((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) = L) (ψ : L ≃* K)
    (hψ : ∀ (j : G) (hj : j ∈ nclIn H (d1LiftX p H R K))
      (hjL : QuotientGroup.mk' (primeComplementCore (G := H₁) p) ⟨j, hc.nclIn_le hj⟩ ∈ L),
      ((ψ ⟨_, hjL⟩ : K) : H ⧸ primeComplementCore (G := H) p) =
        QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨j, nclIn_le_self H _ hj⟩) :
    ¬ L ≤ ((H₁ ⊓ M).subgroupOf H₁).map (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) := by
  have hd := hc.data
  intro hLX
  obtain ⟨z, hzR, hzK, hzp, hzc⟩ := hd.z
  apply (hd.cfg.red.rankOne_principle hd.comp hd.noncyclic hzR hzK hzp hzc).2
  intro k hk
  set ℓ := ψ.symm ⟨k, hk⟩ with hℓ
  obtain ⟨h', hh', hh'ℓ⟩ := hLX ℓ.2
  have hℓJ : (ℓ : H₁ ⧸ primeComplementCore (G := H₁) p) ∈
      ((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
        (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) := hJL ▸ ℓ.2
  obtain ⟨j', hj', hjℓ⟩ := hℓJ
  have hjJ : (j' : G) ∈ nclIn H (d1LiftX p H R K) := hj'
  have hn : (h' : G)⁻¹ * j' ∈ GLBPrimeCore p H₁ :=
    (mk'_primeComplementCore_eq_one_iff p (h'⁻¹ * j')).mp
      (by rw [map_mul, map_inv, hh'ℓ, hjℓ, inv_mul_cancel])
  have hh'M : (h' : G) ∈ M := (Subgroup.mem_subgroupOf.mp hh').2
  have hjM : (j' : G) ∈ M := by
    have e : (j' : G) = h' * ((h' : G)⁻¹ * j') := by group
    rw [e]
    exact M.mul_mem hh'M (hc.escape.primeCore_le hn)
  have hkeq : k = QuotientGroup.mk' (primeComplementCore (G := H) p)
      ⟨j', nclIn_le_self H _ hjJ⟩ := by
    have h1 := hψ j' hjJ (hjℓ ▸ ℓ.2)
    have h2 : (⟨QuotientGroup.mk' (primeComplementCore (G := H₁) p) ⟨j', hc.nclIn_le hjJ⟩,
        hjℓ ▸ ℓ.2⟩ : L) = ℓ := Subtype.ext hjℓ
    rw [h2, hℓ, MulEquiv.apply_symm_apply] at h1
    exact h1
  rw [hkeq]
  exact ⟨⟨j', nclIn_le_self H _ hjJ⟩,
    Subgroup.mem_subgroupOf.mpr ⟨nclIn_le_self H _ hjJ, hjM⟩, rfl⟩

theorem exists_sylow_of_mulEquiv (hc : D1OneLieEscData p P M H R Rbar K P' H₁ S)
    {L : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)}
    (hJL : ((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) = L) (ψ : L ≃* K)
    (hψ : ∀ (j : G) (hj : j ∈ nclIn H (d1LiftX p H R K))
      (hjL : QuotientGroup.mk' (primeComplementCore (G := H₁) p) ⟨j, hc.nclIn_le hj⟩ ∈ L),
      ((ψ ⟨_, hjL⟩ : K) : H ⧸ primeComplementCore (G := H) p) =
        QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨j, nclIn_le_self H _ hj⟩) :
    ∃ T₁ : Sylow p L, (T₁ : Subgroup L).map L.subtype =
      ((d1LiftX p H R K).subgroupOf H₁).map
        (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) := by
  have hd := hc.data
  have : Fact p.Prime := ⟨hc.escape.prime⟩
  obtain ⟨T, hT⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Rbar
    (ComponentClassification.Components.mathlib_subnormal_of_chain hd.comp.2.1
      Subgroup.IsSubnormal.top)
  have hXJ : ∀ x : G, x ∈ d1LiftX p H R K → x ∈ nclIn H (d1LiftX p H R K) :=
    fun x hx => le_nclIn (d1LiftX_le_H p H R K) hx
  have hXL : ∀ (x : G) (hx : x ∈ d1LiftX p H R K),
      QuotientGroup.mk' (primeComplementCore (G := H₁) p) ⟨x, hc.nclIn_le (hXJ x hx)⟩ ∈ L :=
    fun x hx => hJL ▸ Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (hXJ x hx))
  have hsurj : Function.Surjective ψ.symm.toMonoidHom := ψ.symm.surjective
  refine ⟨T.mapSurjective hsurj, ?_⟩
  rw [Sylow.coe_mapSurjective hsurj T]
  ext y
  constructor
  · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    have htR : (t : H ⧸ primeComplementCore (G := H) p) ∈
        (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K := hT ▸ ⟨t, ht, rfl⟩
    rw [← hd.cfg.map_d1LiftX_eq_inf] at htR
    obtain ⟨x, hx, hxt⟩ := htR
    have hxX : (x : G) ∈ d1LiftX p H R K := hx
    have hxK : QuotientGroup.mk' (primeComplementCore (G := H) p)
        ⟨(x : G), nclIn_le_self H _ (hXJ x hxX)⟩ ∈ K := hxt ▸ t.2
    have htx : t = ⟨_, hxK⟩ := Subtype.ext hxt.symm
    simp only [MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
    rw [htx, hc.symm_apply_of_mulEquiv ψ hψ (hXJ x hxX) (hXL x hxX) hxK]
    exact ⟨⟨x, hc.nclIn_le (hXJ x hxX)⟩, Subgroup.mem_subgroupOf.mpr hxX, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    have hxX : (x : G) ∈ d1LiftX p H R K := hx
    have hxR : QuotientGroup.mk' (primeComplementCore (G := H) p)
        ⟨(x : G), nclIn_le_self H _ (hXJ x hxX)⟩ ∈
          (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K := by
      rw [← hd.cfg.map_d1LiftX_eq_inf]
      exact ⟨⟨x, nclIn_le_self H _ (hXJ x hxX)⟩, hxX, rfl⟩
    have hxK := hxR.2
    rw [← hT] at hxR
    obtain ⟨t, ht, htx⟩ := hxR
    have htx' : t = ⟨_, hxK⟩ := Subtype.ext htx
    refine ⟨ψ.symm t, ⟨t, ht, rfl⟩, ?_⟩
    rw [htx', hc.symm_apply_of_mulEquiv ψ hψ (hXJ x hxX) (hXL x hxX)]
    rfl

theorem oneLieFacts_of_mulEquiv (hc : D1OneLieEscData p P M H R Rbar K P' H₁ S)
    (hK : KFactOneLie) {L : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)}
    (hLs : IsSimpleGroup L) (hLnab : ∃ a b : L, a * b ≠ b * a) (hLcat : IsCatalogGroup L)
    (hJL : ((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) = L) (ψ : L ≃* K)
    (hψ : ∀ (j : G) (hj : j ∈ nclIn H (d1LiftX p H R K))
      (hjL : QuotientGroup.mk' (primeComplementCore (G := H₁) p) ⟨j, hc.nclIn_le hj⟩ ∈ L),
      ((ψ ⟨_, hjL⟩ : K) : H ⧸ primeComplementCore (G := H) p) =
        QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨j, nclIn_le_self H _ hj⟩)
    (T₁ : Sylow p L) (hT₁ : (T₁ : Subgroup L).map L.subtype =
      ((d1LiftX p H R K).subgroupOf H₁).map (QuotientGroup.mk' (primeComplementCore (G := H₁) p))) :
    OneLieFacts p L T₁ ∧ (GLBCore p 1 (T₁ : Subgroup L)).map L.subtype ≤
      ((H₁ ⊓ M).subgroupOf H₁).map (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) := by
  have hd := hc.data
  have hp := hc.escape.prime
  have : Fact p.Prime := ⟨hp⟩
  set Xt := ((d1LiftX p H R K).subgroupOf H₁).map
    (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) with hXt
  have hXL : Xt ≤ L := hT₁ ▸ Subgroup.map_subtype_le _
  have hXH₁ : d1LiftX p H R K ≤ H₁ := (le_nclIn (d1LiftX_le_H p H R K)).trans hc.nclIn_le
  obtain ⟨z, hzR, hzK, hzp, hzc⟩ := hd.z
  obtain ⟨hN, -⟩ := hd.cfg.red.rankOne_principle hd.comp hd.noncyclic hzR hzK hzp hzc
  have hψX : ∀ u : L, (u : H₁ ⧸ primeComplementCore (G := H₁) p) ∈ Xt →
      ((ψ u : K) : H ⧸ primeComplementCore (G := H) p) ∈
        (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K := by
    intro u hu
    obtain ⟨x, hx, hxu⟩ := hu
    have hxX : (x : G) ∈ d1LiftX p H R K := hx
    have hxJ : (x : G) ∈ nclIn H (d1LiftX p H R K) := le_nclIn (d1LiftX_le_H p H R K) hxX
    have hueq : u = ⟨QuotientGroup.mk' (primeComplementCore (G := H₁) p)
        ⟨(x : G), hc.nclIn_le hxJ⟩, hxu ▸ u.2⟩ := Subtype.ext hxu.symm
    rw [hueq, hψ (x : G) hxJ, ← hd.cfg.map_d1LiftX_eq_inf]
    exact ⟨⟨x, nclIn_le_self H _ hxJ⟩, hxX, rfl⟩
  have hN' : ∀ U : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p), U ≤ Xt ⊓ L → U ≠ ⊥ →
      L ⊓ Subgroup.normalizer (U : Set (H₁ ⧸ primeComplementCore (G := H₁) p)) ≤
        ((H₁ ⊓ M).subgroupOf H₁).map (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) := by
    rintro U hU hU1 ℓ ⟨hℓL, hℓN⟩
    have hUX : U ≤ Xt := hU.trans inf_le_left
    have hUL : U ≤ L := hU.trans inf_le_right
    refine hc.mem_of_mulEquiv hJL ψ hψ ⟨ℓ, hℓL⟩ ?_
    set U' : Subgroup (H ⧸ primeComplementCore (G := H) p) :=
      ((U.subgroupOf L).map ψ.toMonoidHom).map K.subtype with hU'
    have hU'R : U' ≤ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K := by
      rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      exact hψX u (hUX (Subgroup.mem_subgroupOf.mp hu))
    have hU'1 : U' ≠ ⊥ := by
      intro hbot
      apply hU1
      rw [eq_bot_iff]
      intro u hu
      have hmem : ((ψ ⟨u, hUL hu⟩ : K) : H ⧸ primeComplementCore (G := H) p) ∈ U' :=
        ⟨_, ⟨⟨u, hUL hu⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      have h1 : ψ ⟨u, hUL hu⟩ = 1 := Subtype.ext hmem
      have h2 : (⟨u, hUL hu⟩ : L) = 1 := ψ.injective (by rw [h1, map_one])
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val h2)
    have hℓU' : ((ψ ⟨ℓ, hℓL⟩ : K) : H ⧸ primeComplementCore (G := H) p) ∈
        K ⊓ Subgroup.normalizer (U' : Set (H ⧸ primeComplementCore (G := H) p)) := by
      refine ⟨(ψ ⟨ℓ, hℓL⟩).2, mem_normalizer_of_conj_map_le ?_⟩
      rintro _ ⟨_, ⟨_, ⟨u, hu, rfl⟩, rfl⟩, rfl⟩
      have huU : (u : H₁ ⧸ primeComplementCore (G := H₁) p) ∈ U := Subgroup.mem_subgroupOf.mp hu
      have hcU : ℓ * u * ℓ⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hℓN u).mp huU
      refine ⟨_, ⟨⟨ℓ, hℓL⟩ * u * (⟨ℓ, hℓL⟩ : L)⁻¹, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩, ?_⟩
      · simpa using hcU
      · simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv, Subgroup.coe_subtype,
          MulAut.conj_apply]
    exact hN U' hU'R hU'1 hℓU'
  have hT₁' : (T₁ : Subgroup L).map L.subtype = Xt ⊓ L := by rw [hT₁, inf_eq_left.mpr hXL]
  have hΓX := glbCore_map_le_of_normalizer_le hp hT₁' hN'
  have hΓne : GLBCore p 1 (T₁ : Subgroup L) ≠ ⊤ := fun htop =>
    hc.not_le_of_mulEquiv hJL ψ hψ fun y hy => hΓX ⟨⟨y, hy⟩, by rw [htop]; exact Subgroup.mem_top _,
      rfl⟩
  have hT₁nc : ¬ IsCyclic (T₁ : Subgroup L) := fun hcyc => hd.not_isCyclic_map hXH₁ (by
    rw [← hXt, ← hT₁]
    exact isCyclic_of_surjective _ (L.subtype.subgroupMap_surjective (T₁ : Subgroup L)))
  have hbig : ¬ Open.pRank p (⊤ : Subgroup (MulAut L)) ≤ 2 := by
    have h1 := pRank_map_of_injective p hp (MulAut.congr ψ).toMonoidHom (MulAut.congr ψ).injective
      (⊤ : Subgroup (MulAut L))
    rw [Subgroup.map_top_of_surjective _ (MulAut.congr ψ).surjective] at h1
    rw [← h1]
    exact hd.big
  exact ⟨hK L hLs hLnab hLcat p hp hc.escape.ne_two T₁ hT₁nc hΓne hbig, hΓX⟩

end D1OneLieEscData

namespace D1OneLieCompetitorData

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {R₁ : Subgroup G} {P' : Sylow p G}
  {H₁ S : Subgroup G}

theorem toEsc (hc : D1OneLieCompetitorData p P M H R Rbar K R₁ P' H₁ S) :
    D1OneLieEscData p P M H R Rbar K P' H₁ S :=
  ⟨hc.data, hc.escape, hc.nclIn_le⟩

theorem exists_sylow_of_mulEquiv (hc : D1OneLieCompetitorData p P M H R Rbar K R₁ P' H₁ S)
    {L : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)}
    (hJL : ((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) = L) (ψ : L ≃* K)
    (hψ : ∀ (j : G) (hj : j ∈ nclIn H (d1LiftX p H R K))
      (hjL : QuotientGroup.mk' (primeComplementCore (G := H₁) p) ⟨j, hc.nclIn_le hj⟩ ∈ L),
      ((ψ ⟨_, hjL⟩ : K) : H ⧸ primeComplementCore (G := H) p) =
        QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨j, nclIn_le_self H _ hj⟩) :
    ∃ T₁ : Sylow p L, (T₁ : Subgroup L).map L.subtype =
      ((d1LiftX p H R K).subgroupOf H₁).map
        (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) :=
  hc.toEsc.exists_sylow_of_mulEquiv hJL ψ hψ

theorem oneLieFacts_of_mulEquiv (hc : D1OneLieCompetitorData p P M H R Rbar K R₁ P' H₁ S)
    (hK : KFactOneLie) {L : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)}
    (hLs : IsSimpleGroup L) (hLnab : ∃ a b : L, a * b ≠ b * a) (hLcat : IsCatalogGroup L)
    (hJL : ((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) = L) (ψ : L ≃* K)
    (hψ : ∀ (j : G) (hj : j ∈ nclIn H (d1LiftX p H R K))
      (hjL : QuotientGroup.mk' (primeComplementCore (G := H₁) p) ⟨j, hc.nclIn_le hj⟩ ∈ L),
      ((ψ ⟨_, hjL⟩ : K) : H ⧸ primeComplementCore (G := H) p) =
        QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨j, nclIn_le_self H _ hj⟩)
    (T₁ : Sylow p L) (hT₁ : (T₁ : Subgroup L).map L.subtype =
      ((d1LiftX p H R K).subgroupOf H₁).map (QuotientGroup.mk' (primeComplementCore (G := H₁) p))) :
    OneLieFacts p L T₁ ∧ (GLBCore p 1 (T₁ : Subgroup L)).map L.subtype ≤
      ((H₁ ⊓ M).subgroupOf H₁).map (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) :=
  hc.toEsc.oneLieFacts_of_mulEquiv hK hLs hLnab hLcat hJL ψ hψ T₁ hT₁

theorem toPhaseThree (hc : D1OneLieCompetitorData p P M H R Rbar K R₁ P' H₁ S)
    (hSch : KFactCatalogSchreier)
    (hJc : IsComponentOf (((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p))) ⊤) (hK : KFactOneLie) :
    D1PhaseThree p P' M H₁ S := by
  have hd := hc.data
  have hp := hc.escape.prime
  obtain ⟨L, hL, -, hJL, hCL, huniq, ψ, hψ⟩ := hc.exists_mulEquiv hSch hJc
  obtain ⟨Rb₁, -, hred₁, -, hcomp₁, -, -, -, -⟩ :=
    hc.escape.exists_reducedNongeneration_of_not_hasPrimeConstraint hd.cfg.glob.kProper
      hc.not_hasPrimeConstraint
  obtain ⟨hLs, hLnab, hLcat⟩ := isSimpleGroup_of_centralizer_eq_bot hL hCL (hcomp₁ L hL).2.1
  obtain ⟨T₁, hT₁⟩ := hc.exists_sylow_of_mulEquiv hJL ψ hψ
  obtain ⟨hF, hΓX⟩ := hc.oneLieFacts_of_mulEquiv hK hLs hLnab hLcat hJL ψ hψ T₁ hT₁
  have hU : UPrimeHyp p (((H₁ ⊓ M).subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p))) :=
    uPrimeHyp_of_forall_kFact hp fun L' hL' _ => by
      obtain rfl := huniq L' hL'
      exact ⟨hF.uPrime, T₁, hΓX⟩
  exact hc.escape.toPhaseThreeU hd.glob
    (hc.escape.primeCore_inf_eq_iff.mpr (hred₁.primeComplementCore_eq_bot_of_uPrimeHyp hU))

end D1OneLieCompetitorData

end CFSG.AGLEmbedding
