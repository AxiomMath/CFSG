module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieCaseBPhase
public import CFSG.LocalAnalysis.AGLEmbedding.TheoremZGen
import CFSG.LocalAnalysis.AGLEmbedding.CoprimeSup
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux2
import CFSG.LocalAnalysis.AGLEmbedding.OneLieOpMbar
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

namespace D1OneLieEscData

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {R₁ : Subgroup G} {P' : Sylow p G}
  {H₁ S : Subgroup G}

theorem nclIn_le_and_nclIn_eq_of_simple (hc : D1OneLieEscData p P M H R Rbar K P' H₁ S)
    {L : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)} (hLn : L.Normal) (hLs : IsSimpleGroup L)
    (hJL : ((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) = L) :
    nclIn H (d1LiftX p H R K) ≤ nclIn H₁ (d1LiftX p H R K) ∧
      nclIn (nclIn H₁ (d1LiftX p H R K)) (d1LiftX p H R K) = nclIn H₁ (d1LiftX p H R K) := by
  have hd := hc.data
  have hp := hc.escape.prime
  have : Fact p.Prime := ⟨hp⟩
  have : IsSimpleGroup L := hLs
  set X := d1LiftX p H R K with hXdef
  set J := nclIn H X with hJdef
  set J₁ := nclIn H₁ X with hJ₁def
  have hXH : X ≤ H := d1LiftX_le_H p H R K
  have hXH₁ : X ≤ H₁ := (le_nclIn hXH).trans hc.nclIn_le
  have hXp : IsPGroup p X := hd.cfg.ext.isPGroup.to_le (d1LiftX_le p H R K)
  have hJ₁H₁ : J₁ ≤ H₁ := nclIn_le_self H₁ X
  have hXJ₁ : X ≤ J₁ := le_nclIn hXH₁
  have hcop : (Nat.card (GLBPrimeCore p H₁)).Coprime p := (glbPrimeCore_coprime p H₁).symm
  have hsup : ∀ A B : Subgroup G, A ≤ H₁ →
      (A.subgroupOf H₁).map (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) ≤
        (B.subgroupOf H₁).map (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) →
      A ≤ B ⊔ GLBPrimeCore p H₁ := by
    intro A B hAH hAB a ha
    obtain ⟨b, hb, hba⟩ := hAB (Subgroup.mem_map_of_mem _
      (show (⟨a, hAH ha⟩ : H₁) ∈ A.subgroupOf H₁ from ha))
    have hn : (b : G)⁻¹ * a ∈ GLBPrimeCore p H₁ :=
      (mk'_primeComplementCore_eq_one_iff p (b⁻¹ * ⟨a, hAH ha⟩)).mp
        (by rw [map_mul, map_inv, hba, inv_mul_cancel])
    have e : a = b * ((b : G)⁻¹ * a) := by group
    rw [e]
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hb) hn
  set Lh : Subgroup G :=
    (L.comap (QuotientGroup.mk' (primeComplementCore (G := H₁) p))).map H₁.subtype with hLh
  have hLhH₁ : Lh ≤ H₁ := Subgroup.map_subtype_le _
  have hLhsub : Lh.subgroupOf H₁ = L.comap (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) :=
    Subgroup.comap_map_eq_self_of_injective H₁.subtype_injective _
  have hH₁Lh : H₁ ≤ Subgroup.normalizer (Lh : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLhH₁).mp (by rw [hLhsub]; exact hLn.comap _)
  have hXLh : X ≤ Lh := fun x hx => ⟨⟨x, hXH₁ hx⟩, show _ ∈ L from hJL ▸
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (le_nclIn hXH hx)), rfl⟩
  have hJ₁Lh : J₁ ≤ Lh := CFSG.AGLEmbedding.nclIn_le hXLh hLhH₁ hH₁Lh
  have hJ₁L : (J₁.subgroupOf H₁).map (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) ≤ L := by
    rintro _ ⟨j, hj, rfl⟩
    have := hJ₁Lh (Subgroup.mem_subgroupOf.mp hj)
    rw [← Subgroup.mem_subgroupOf, hLhsub] at this
    exact this
  have hXt1 : (X.subgroupOf H₁).map (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) ≠ ⊥ :=
    map_mk_ne_bot_of_isPGroup hp hXH₁ hXp hd.d1LiftX_ne_bot
  have hJ₁n : ((J₁.subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p))).Normal :=
    (nclIn_normal H₁ X).map _ (QuotientGroup.mk'_surjective _)
  have hJ₁eq : (J₁.subgroupOf H₁).map (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) = L :=
    eq_of_le_normalizer_of_isSimpleGroup hJ₁L
      (by rw [Subgroup.normalizer_eq_top_iff.mpr hJ₁n]; exact le_top)
      (ne_bot_of_le_ne_bot hXt1 (Subgroup.map_mono (Subgroup.comap_mono hXJ₁)))
  have hJsup : J ≤ J₁ ⊔ GLBPrimeCore p H₁ := hsup J J₁ hc.nclIn_le (by rw [hJL, hJ₁eq])
  have hJJ₁ : J ≤ J₁ := by
    refine nclIn_le_of_forall_conj_mem fun c hc' x hx => ?_
    have hXc : X.map (MulAut.conj c).toMonoidHom ≤ J := by
      rintro _ ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_nclIn H X hc') y).mp (le_nclIn hXH hy)
    exact le_of_le_sup_of_coprime_card_of_le (hXc.trans hc.nclIn_le) hJ₁H₁ (glbPrimeCore_le p H₁)
      (nclIn_normal H₁ X) (hXp.map _) hcop (hXc.trans hJsup) ⟨x, hx, rfl⟩
  have hLJ₁ : nclIn J₁ X ≤ J₁ := nclIn_le_self J₁ X
  have hJ₂eq : ((nclIn J₁ X).subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) = L :=
    eq_of_le_normalizer_of_isSimpleGroup
      ((Subgroup.map_mono (Subgroup.comap_mono hLJ₁)).trans hJ₁eq.le)
      (hJ₁eq.ge.trans (CFSG.AGLEmbedding.map_le_normalizer_map _ (hLJ₁.trans hJ₁H₁)
        (le_normalizer_nclIn J₁ X)))
      (ne_bot_of_le_ne_bot hXt1 (Subgroup.map_mono (Subgroup.comap_mono (le_nclIn hXJ₁))))
  have hJLN : J₁ ≤ nclIn J₁ X ⊔ (J₁ ⊓ GLBPrimeCore p H₁) := by
    intro j hj
    obtain ⟨l, hl, hlj⟩ : QuotientGroup.mk' (primeComplementCore (G := H₁) p)
        ⟨j, hJ₁H₁ hj⟩ ∈ ((nclIn J₁ X).subgroupOf H₁).map
          (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) := by
      rw [hJ₂eq, ← hJ₁eq]
      exact Subgroup.mem_map_of_mem _ (show (⟨j, hJ₁H₁ hj⟩ : H₁) ∈ J₁.subgroupOf H₁ from hj)
    have hn : (l : G)⁻¹ * j ∈ GLBPrimeCore p H₁ :=
      (mk'_primeComplementCore_eq_one_iff p (l⁻¹ * ⟨j, hJ₁H₁ hj⟩)).mp
        (by rw [map_mul, map_inv, hlj, inv_mul_cancel])
    have e : j = l * ((l : G)⁻¹ * j) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hl ⟨J₁.mul_mem (J₁.inv_mem (hLJ₁ hl)) hj, hn⟩
  have hcop' : (Nat.card (J₁ ⊓ GLBPrimeCore p H₁ : Subgroup G)).Coprime p :=
    ((glbPrimeCore_coprime p H₁).coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)).symm
  have hconj : ∀ c ∈ H₁, ∀ x ∈ X, c * x * c⁻¹ ∈ nclIn J₁ X := by
    intro c hc' x hx
    have hXc : X.map (MulAut.conj c).toMonoidHom ≤ J₁ := by
      rintro _ ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_nclIn H₁ X hc') y).mp (hXJ₁ hy)
    exact le_of_le_sup_of_coprime_card_of_le hXc hLJ₁ inf_le_left (nclIn_normal J₁ X)
      (hXp.map _) hcop' (hXc.trans hJLN) ⟨x, hx, rfl⟩
  exact ⟨hJJ₁, le_antisymm hLJ₁ (nclIn_le_of_forall_conj_mem hconj)⟩

theorem nclIn_eq_of_le_of_simple (hc : D1OneLieEscData p P M H R Rbar K P' H₁ S)
    {L : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)} (hLn : L.Normal) (hLs : IsSimpleGroup L)
    (hJL : ((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) = L) {Y : Subgroup G}
    (hYX : Y ≤ d1LiftX p H R K) (hY : Y ≠ ⊥) :
    nclIn H₁ Y = nclIn H₁ (d1LiftX p H R K) := by
  have hd := hc.data
  have hp := hc.escape.prime
  have : Fact p.Prime := ⟨hp⟩
  have : IsSimpleGroup L := hLs
  set X := d1LiftX p H R K with hXdef
  have hXH : X ≤ H := d1LiftX_le_H p H R K
  have hXH₁ : X ≤ H₁ := (le_nclIn hXH).trans hc.nclIn_le
  have hXp : IsPGroup p X := hd.cfg.ext.isPGroup.to_le (d1LiftX_le p H R K)
  have hYH₁ : Y ≤ H₁ := hYX.trans hXH₁
  set Lh : Subgroup G :=
    (L.comap (QuotientGroup.mk' (primeComplementCore (G := H₁) p))).map H₁.subtype with hLh
  have hLhH₁ : Lh ≤ H₁ := Subgroup.map_subtype_le _
  have hLhsub : Lh.subgroupOf H₁ = L.comap (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) :=
    Subgroup.comap_map_eq_self_of_injective H₁.subtype_injective _
  have hH₁Lh : H₁ ≤ Subgroup.normalizer (Lh : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLhH₁).mp (by rw [hLhsub]; exact hLn.comap _)
  have hXLh : X ≤ Lh := fun x hx => ⟨⟨x, hXH₁ hx⟩, show _ ∈ L from hJL ▸
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (le_nclIn hXH hx)), rfl⟩
  have hYL : ((nclIn H₁ Y).subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) ≤ L := by
    rintro _ ⟨j, hj, rfl⟩
    have := CFSG.AGLEmbedding.nclIn_le (hYX.trans hXLh) hLhH₁ hH₁Lh (Subgroup.mem_subgroupOf.mp hj)
    rw [← Subgroup.mem_subgroupOf, hLhsub] at this
    exact this
  have hYn : (((nclIn H₁ Y).subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p))).Normal :=
    (nclIn_normal H₁ Y).map _ (QuotientGroup.mk'_surjective _)
  have hYeq : ((nclIn H₁ Y).subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) = L :=
    eq_of_le_normalizer_of_isSimpleGroup hYL
      (by rw [Subgroup.normalizer_eq_top_iff.mpr hYn]; exact le_top)
      (ne_bot_of_le_ne_bot (map_mk_ne_bot_of_isPGroup hp hYH₁ (hXp.to_le hYX) hY)
        (Subgroup.map_mono (Subgroup.comap_mono (le_nclIn hYH₁))))
  have hXsup : X ≤ nclIn H₁ Y ⊔ GLBPrimeCore p H₁ := by
    intro x hx
    obtain ⟨b, hb, hbx⟩ : QuotientGroup.mk' (primeComplementCore (G := H₁) p) ⟨x, hXH₁ hx⟩ ∈
        ((nclIn H₁ Y).subgroupOf H₁).map (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) := by
      rw [hYeq]
      have := hXLh hx
      obtain ⟨x', hx', hxx'⟩ := this
      rw [show x' = ⟨x, hXH₁ hx⟩ from Subtype.ext hxx'] at hx'
      exact hx'
    have hn : (b : G)⁻¹ * x ∈ GLBPrimeCore p H₁ :=
      (mk'_primeComplementCore_eq_one_iff p (b⁻¹ * ⟨x, hXH₁ hx⟩)).mp
        (by rw [map_mul, map_inv, hbx, inv_mul_cancel])
    have e : x = b * ((b : G)⁻¹ * x) := by group
    rw [e]
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hb) hn
  have hXY : X ≤ nclIn H₁ Y :=
    le_of_le_sup_of_coprime_card_of_le hXH₁ (nclIn_le_self H₁ Y) (glbPrimeCore_le p H₁)
      (nclIn_normal H₁ Y) hXp (glbPrimeCore_coprime p H₁).symm hXsup
  exact le_antisymm
    (CFSG.AGLEmbedding.nclIn_le (hYX.trans (le_nclIn hXH₁)) (nclIn_le_self H₁ X)
      (le_normalizer_nclIn H₁ X))
    (CFSG.AGLEmbedding.nclIn_le hXY (nclIn_le_self H₁ Y) (le_normalizer_nclIn H₁ Y))

theorem pCoreCentralizer_inf_le (hc : D1OneLieEscData p P M H R Rbar K P' H₁ S)
    (hK : KFactOneLie) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hY : pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥) (hWK : d1MapPCore p M H ≤ K)
    (hU3 : ¬ (IsUnitaryGroup p K ∧
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) =
        centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)))
    (h3₁ : D1PhaseThree p P' M H₁ S) {L : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)}
    (hLn : L.Normal)
    (hJL : ((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) = L) (ψ : L ≃* K)
    (hψ : ∀ (j : G) (hj : j ∈ nclIn H (d1LiftX p H R K))
      (hjL : QuotientGroup.mk' (primeComplementCore (G := H₁) p) ⟨j, hc.nclIn_le hj⟩ ∈ L),
      ((ψ ⟨_, hjL⟩ : K) : H ⧸ primeComplementCore (G := H) p) =
        QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨j, nclIn_le_self H _ hj⟩) :
    pCoreCentralizerPreimage p M ⊓ H₁ ≤ d1LiftX p H R K ⊔ d1PlusCore p H₁ L := by
  have hd := hc.data
  have hp := hc.escape.prime
  have : Fact p.Prime := ⟨hp⟩
  have h3 := hd.toPhaseThree hK
  have : L.Normal := hLn
  obtain ⟨T₁, hT₁, hF⟩ := hd.oneLieFacts hK
  have hfacts := hd.d1MapPCore_facts hK h84 hD2
  set W := d1MapPCore p M H with hW
  have hWT : W ≤ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :=
    le_inf hfacts.2.1 hWK
  have hW1 : W ≠ ⊥ := ne_bot_of_le_ne_bot (hfacts.2.2.2.2.mp hY) inf_le_left
  have hWK' : W ≤ K := hWK
  have hXJ : ∀ x : G, x ∈ d1LiftX p H R K → x ∈ nclIn H (d1LiftX p H R K) :=
    fun x hx => le_nclIn (d1LiftX_le_H p H R K) hx
  have hXL : ∀ (x : G) (hx : x ∈ d1LiftX p H R K),
      QuotientGroup.mk' (primeComplementCore (G := H₁) p) ⟨x, hc.nclIn_le (hXJ x hx)⟩ ∈ L :=
    fun x hx => hJL ▸ Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (hXJ x hx))
  have hWX : ∀ w ∈ W, ∃ r : G, r ∈ d1LiftX p H R K ∧ r ∈ pCorePreimage p M ∧
      ∃ hr : r ∈ H, QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨r, hr⟩ = w := by
    intro w hw
    have hwK : w ∈ K := hWK hw
    rw [hW, h3.d1MapPCore_eq h84 hD2] at hw
    obtain ⟨r, ⟨hrR, hrY⟩, rfl⟩ := hw
    exact ⟨r, ⟨r, ⟨hrR, hwK⟩, rfl⟩, hrY, r.2, rfl⟩
  set V : Subgroup K := W.subgroupOf K with hV
  have hVmap : V.map K.subtype = W := Subgroup.map_subgroupOf_eq_of_le hWK'
  have hVT : V ≤ T₁ := by
    intro v hv
    have hvT : (v : H ⧸ primeComplementCore (G := H) p) ∈ (T₁ : Subgroup K).map K.subtype :=
      hT₁ ▸ hWT (Subgroup.mem_subgroupOf.mp hv)
    obtain ⟨t, ht, htv⟩ := hvT
    rwa [← Subtype.ext htv]
  have hV1 : V ≠ ⊥ := by
    intro hbot
    apply hW1
    rw [← hVmap, hbot, Subgroup.map_bot]
  have hNV : Subgroup.normalizer ((T₁ : Subgroup K) : Set K) ≤
      Subgroup.normalizer ((V : Subgroup K) : Set K) := fun n hn =>
    Subgroup.le_normalizer_comap K.subtype (hfacts.2.2.1 (hT₁ ▸ coe_mem_normalizer_map hn))
  intro d ⟨hdD, hdH⟩
  set y := QuotientGroup.mk' (primeComplementCore (G := H₁) p) ⟨d, hdH⟩ with hy
  have hyC := mk_mem_centralizer_d1MapPCore h3₁.twoCore_M_le_glbPrimeCore hdD hdH
  set f : MulAut K := MulAut.congr ψ (MulAut.conjNormal y) with hf
  have hfV : ∀ v ∈ V, f v = v := by
    intro v hv
    obtain ⟨r, hrX, hrY, hrH, hrv⟩ := hWX v (Subgroup.mem_subgroupOf.mp hv)
    have hrK : QuotientGroup.mk' (primeComplementCore (G := H) p)
        ⟨r, nclIn_le_self H _ (hXJ r hrX)⟩ ∈ K := hrv ▸ v.2
    have hveq : v = ⟨_, hrK⟩ := Subtype.ext hrv.symm
    have hrH₁ : r ∈ H₁ := hc.nclIn_le (hXJ r hrX)
    have hcomm := Subgroup.mem_centralizer_iff.mp hyC
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p) ⟨r, hrH₁⟩)
      ⟨⟨r, hrH₁⟩, Subgroup.mem_subgroupOf.mpr hrY, rfl⟩
    rw [hveq, hf, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      hc.symm_apply_of_mulEquiv ψ hψ (hXJ r hrX) (hXL r hrX) hrK]
    have hfix : MulAut.conjNormal y
        (⟨QuotientGroup.mk' (primeComplementCore (G := H₁) p) ⟨r, hrH₁⟩, hXL r hrX⟩ : L) =
        ⟨_, hXL r hrX⟩ := by
      apply Subtype.ext
      have h1 : y * QuotientGroup.mk' (primeComplementCore (G := H₁) p) ⟨r, hrH₁⟩ =
          QuotientGroup.mk' (primeComplementCore (G := H₁) p) ⟨r, hrH₁⟩ * y := hcomm.symm
      rw [MulAut.conjNormal_apply]
      simp only
      rw [h1]
      group
    rw [hfix, ← hc.symm_apply_of_mulEquiv ψ hψ (hXJ r hrX) (hXL r hrX) hrK,
      MulEquiv.apply_symm_apply]
  rcases hF.centralizer V hVT hV1 hNV with hall | ⟨hcen, hU⟩
  · obtain ⟨t, ht, hft⟩ := hall f hfV
    have hyt : MulAut.conjNormal y = MulAut.conj (ψ.symm t) := by
      apply (MulAut.congr ψ).injective
      rw [← hf, hft]
      ext k
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulAut.conj_apply, map_mul, map_inv,
        MulEquiv.apply_symm_apply]
    have hyL := inv_mul_mem_centralizer_of_conjNormal_eq hyt
    have htR : (t : H ⧸ primeComplementCore (G := H) p) ∈
        (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K := hT₁ ▸ ⟨t, ht, rfl⟩
    rw [← hd.cfg.map_d1LiftX_eq_inf] at htR
    obtain ⟨x, hx, hxt⟩ := htR
    have hxX : (x : G) ∈ d1LiftX p H R K := hx
    have hxK : QuotientGroup.mk' (primeComplementCore (G := H) p)
        ⟨(x : G), nclIn_le_self H _ (hXJ x hxX)⟩ ∈ K := hxt ▸ t.2
    have htx : t = ⟨_, hxK⟩ := Subtype.ext hxt.symm
    rw [htx, hc.symm_apply_of_mulEquiv ψ hψ (hXJ x hxX) (hXL x hxX) hxK] at hyL
    have hn : (x : G)⁻¹ * d ∈ d1PlusCore p H₁ L := by
      refine ⟨(⟨x, hc.nclIn_le (hXJ x hxX)⟩ : H₁)⁻¹ * ⟨d, hdH⟩, ?_, rfl⟩
      show QuotientGroup.mk' (primeComplementCore (G := H₁) p)
        ((⟨x, hc.nclIn_le (hXJ x hxX)⟩ : H₁)⁻¹ * ⟨d, hdH⟩) ∈
          Subgroup.centralizer (L : Set (H₁ ⧸ primeComplementCore (G := H₁) p))
      rw [map_mul, map_inv]
      exact hyL
    have e : d = x * ((x : G)⁻¹ * d) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hxX hn
  · exfalso
    apply hU3
    refine ⟨hU, ?_⟩
    rw [inf_eq_left.mpr hWT]
    have h1 := congrArg (Subgroup.map K.subtype) hcen
    rwa [hVmap, map_subtype_centerOf, hT₁] at h1

end D1OneLieEscData

namespace D1OneLieCompetitorData

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {R₁ : Subgroup G} {P' : Sylow p G}
  {H₁ S : Subgroup G}

theorem pCoreCentralizer_inf_le (hc : D1OneLieCompetitorData p P M H R Rbar K R₁ P' H₁ S)
    (hSch : KFactCatalogSchreier)
    (hJc : IsComponentOf (((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p))) ⊤) (hK : KFactOneLie)
    (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hY : pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥) (hWK : d1MapPCore p M H ≤ K)
    (hU3 : ¬ (IsUnitaryGroup p K ∧
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) =
        centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K))) :
    pCoreCentralizerPreimage p M ⊓ H₁ ≤ d1LiftX p H R K ⊔ GLBPrimeCore p H₁ := by
  have h3₁ := hc.toPhaseThree hSch hJc hK
  obtain ⟨L, -, hLn, hJL, hCL, -, ψ, hψ⟩ := hc.exists_mulEquiv hSch hJc
  refine (hc.toEsc.pCoreCentralizer_inf_le hK h84 hD2 hY hWK hU3 h3₁ hLn hJL ψ hψ).trans
    (sup_le_sup_left ?_ _)
  rintro _ ⟨h, hh, rfl⟩
  have hh' : QuotientGroup.mk' (primeComplementCore (G := H₁) p) h ∈
      Subgroup.centralizer (L : Set (H₁ ⧸ primeComplementCore (G := H₁) p)) := hh
  rw [hCL, Subgroup.mem_bot] at hh'
  exact (mk'_primeComplementCore_eq_one_iff p h).mp hh'

theorem nclIn_le_and_nclIn_eq (hc : D1OneLieCompetitorData p P M H R Rbar K R₁ P' H₁ S)
    (hSch : KFactCatalogSchreier)
    (hJc : IsComponentOf (((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p))) ⊤) :
    nclIn H (d1LiftX p H R K) ≤ nclIn H₁ (d1LiftX p H R K) ∧
      nclIn (nclIn H₁ (d1LiftX p H R K)) (d1LiftX p H R K) = nclIn H₁ (d1LiftX p H R K) := by
  obtain ⟨L, hL, hLn, hJL, hCL, -, -, -⟩ := hc.exists_mulEquiv hSch hJc
  obtain ⟨Rb₁, -, -, -, hcomp₁, -, -, -, -⟩ :=
    hc.escape.exists_reducedNongeneration_of_not_hasPrimeConstraint hc.data.cfg.glob.kProper
      hc.not_hasPrimeConstraint
  exact hc.toEsc.nclIn_le_and_nclIn_eq_of_simple hLn
    (isSimpleGroup_of_centralizer_eq_bot hL hCL (hcomp₁ L hL).2.1).1
    hJL

theorem nclIn_eq_of_le (hc : D1OneLieCompetitorData p P M H R Rbar K R₁ P' H₁ S)
    (hSch : KFactCatalogSchreier)
    (hJc : IsComponentOf (((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p))) ⊤) {Y : Subgroup G}
    (hYX : Y ≤ d1LiftX p H R K) (hY : Y ≠ ⊥) :
    nclIn H₁ Y = nclIn H₁ (d1LiftX p H R K) := by
  obtain ⟨L, hL, hLn, hJL, hCL, -, -, -⟩ := hc.exists_mulEquiv hSch hJc
  obtain ⟨Rb₁, -, -, -, hcomp₁, -, -, -, -⟩ :=
    hc.escape.exists_reducedNongeneration_of_not_hasPrimeConstraint hc.data.cfg.glob.kProper
      hc.not_hasPrimeConstraint
  exact hc.toEsc.nclIn_eq_of_le_of_simple hLn
    (isSimpleGroup_of_centralizer_eq_bot hL hCL (hcomp₁ L hL).2.1).1
    hJL hYX hY

theorem commutator_nclIn_le_twoCore (hc : D1OneLieCompetitorData p P M H R Rbar K R₁ P' H₁ S)
    (hSch : KFactCatalogSchreier)
    (hJc : IsComponentOf (((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p))) ⊤) (hK : KFactOneLie)
    (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hY : pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥) :
    ⁅GLBPrimeCore p H₁, nclIn H₁ (d1LiftX p H R K)⁆ ≤ pCoreOf 2 H₁ := by
  have h3₁ := hc.toPhaseThree hSch hJc hK
  have hXH₁ : d1LiftX p H R K ≤ H₁ := (le_nclIn (d1LiftX_le_H p H R K)).trans hc.nclIn_le
  rw [← hc.nclIn_eq_of_le hSch hJc inf_le_right hY]
  exact CFSG.AGLEmbedding.commutator_nclIn_le (inf_le_right.trans hXH₁)
    (le_normalizer_glbPrimeCore p H₁) (localGroup_le_normalizer_pCoreOf 2 H₁)
    (((Subgroup.commutator_mono le_rfl inf_le_left).trans
      (h3₁.commutator_pCorePreimage_le h84 hD2)).trans (h3₁.twoCore_M_le h3₁.twoCore_inf))

end D1OneLieCompetitorData

end CFSG.AGLEmbedding
