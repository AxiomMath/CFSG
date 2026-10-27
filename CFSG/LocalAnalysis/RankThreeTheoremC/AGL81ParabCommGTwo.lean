module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommGTwoCover
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommGeneric
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommLinTransferCover
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommLinTransferS3
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusNodeEscape
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrG2
import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.GTwo

open CFSG.Open CFSG.AGLEmbedding CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
open scoped commutatorElement

theorem isQuasisimple_of_simple_nonab {L : Type*} [Group L] [IsSimpleGroup L]
    (hL : ∃ a b : L, a * b ≠ b * a) : Open.IsQuasisimple L := by
  have hZ : Subgroup.center L = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center L) with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hL
      exact absurd ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a) hab
  refine ⟨?_,
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).isSimpleGroup⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator L) with h | h
  · obtain ⟨a, b, hab⟩ := hL
    have : ⁅a, b⁆ = 1 := by
      rw [← Subgroup.mem_bot, ← h]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    exact absurd (commutatorElement_eq_one_iff_mul_comm.mp this) hab
  · exact h


variable {K : Type} [Field K] [Finite K] [CharP K 2]

section Levi

variable {A : Subgroup (adjointGroup .G2 K)} (hBA : borel (g2Datum K) (torus (τ := .G2) K) ≤ A)
  {i : Fin (Tag.rank .G2)} (hI : negIndices (g2Datum K) A = {i})

include hBA hI in
theorem posUnipotentExcept_le_pCoreOf :
    posUnipotentExcept (g2Datum K) i ≤ CFSG.Open.pCoreOf 2 A := by
  have hB := borelQuotient_g2 (CFSG.AGLEmbedding.ParabAutIrr.adjointQuotientEquiv K).symm
  have hAU := CFSG.AGLEmbedding.LeviBlock.le_normalizer_posUnipotentExcept_of_negIndices_eq hB
    hBA hI
  exact le_pCoreOf (CFSG.AGLEmbedding.LeviBlock.posUnipotentExcept_le_of_borel_le hBA i)
    (fun a ha n hn => (Subgroup.mem_normalizer_iff.1 (hAU ha) n).1 hn)
    (CFSG.AGLEmbedding.LeviBlock.isPGroup_posUnipotentExcept hB i)

include hBA hI in
theorem le_normalizer_rankOne_sup :
    A ≤ Subgroup.normalizer ((rankOne (g2Datum K).rootGroup i ⊔
      posUnipotentExcept (g2Datum K) i : Subgroup (adjointGroup .G2 K)) :
        Set (adjointGroup .G2 K)) := by
  have hB := borelQuotient_g2 (CFSG.AGLEmbedding.ParabAutIrr.adjointQuotientEquiv K).symm
  refine (CFSG.AGLEmbedding.LeviBlock.le_torus_sup_of_negIndices_eq hB hBA hI).trans
    (sup_le (fun t ht => ?_) Subgroup.le_normalizer)
  exact CFSG.AGLEmbedding.ParabAutIrr.mem_normalizer_sup
    (iSup_torus_le_normalizer_rankOne hB.ct i ht)
    (CFSG.AGLEmbedding.ToralCensus.iSup_torus_le_normalizer_posUnipotentExcept hB.ct i ht)

end Levi

section Transfer

variable {G : Type} [Group G] [Finite G] {Y P : Subgroup G}
  {π : adjointGroup .G2 K →* ↥Y} (hπ : Function.Bijective π)

@[expose] noncomputable def toPHom (hPY : P ≤ Y) : ↥((P.subgroupOf Y).comap π) →* ↥P where
  toFun a := ⟨((π a : ↥Y) : G), a.2⟩
  map_one' := by simp
  map_mul' a b := by ext; simp

omit [Finite G] in
theorem toPHom_bijective (hπ : Function.Bijective π) (hPY : P ≤ Y) :
    Function.Bijective (toPHom (π := π) hPY) := by
  refine ⟨fun a b h => Subtype.ext (hπ.1 (Subtype.ext ?_)), fun x => ?_⟩
  · have := congrArg Subtype.val h
    simpa [toPHom] using this
  · obtain ⟨c, hc⟩ := hπ.2 ⟨x, hPY x.2⟩
    have hcA : c ∈ (P.subgroupOf Y).comap π := by
      rw [Subgroup.mem_comap, hc, Subgroup.mem_subgroupOf]
      exact x.2
    exact ⟨⟨c, hcA⟩, Subtype.ext (by simp [toPHom, hc])⟩

@[expose] noncomputable def toP (hπ : Function.Bijective π) (hPY : P ≤ Y) :
    ↥((P.subgroupOf Y).comap π) ≃* ↥P :=
  MulEquiv.ofBijective (toPHom hPY) (toPHom_bijective hπ hPY)

omit [Finite G] in
theorem coe_toP (hPY : P ≤ Y) (a : ↥((P.subgroupOf Y).comap π)) :
    ((toP hπ hPY a : ↥P) : G) = ((π a : ↥Y) : G) :=
  rfl

theorem mem_pCoreOf_of_toP (hPY : P ≤ Y) {a : ↥((P.subgroupOf Y).comap π)}
    (h : toP hπ hPY a ∈ CFSG.pCore 2 ↥P) :
    (a : adjointGroup .G2 K) ∈ CFSG.Open.pCoreOf 2 ((P.subgroupOf Y).comap π) := by
  rw [← CFSG.pCore_map_iso 2 (toP hπ hPY)] at h
  obtain ⟨a', ha', he⟩ := h
  have : a' = a := (toP hπ hPY).injective he
  exact ⟨a, this ▸ ha', rfl⟩

theorem toP_mem_pCore (hPY : P ≤ Y) {a : ↥((P.subgroupOf Y).comap π)}
    (h : (a : adjointGroup .G2 K) ∈ CFSG.Open.pCoreOf 2 ((P.subgroupOf Y).comap π)) :
    toP hπ hPY a ∈ CFSG.pCore 2 ↥P := by
  obtain ⟨a', ha', he⟩ := h
  have : a' = a := Subtype.ext he
  rw [← CFSG.pCore_map_iso 2 (toP hπ hPY)]
  exact ⟨a', ha', by rw [this]; rfl⟩

include hπ in
theorem toHat_rankOne_mem_wSup (hPY : P ≤ Y)
    (hBA : borel (g2Datum K) (torus (τ := .G2) K) ≤ (P.subgroupOf Y).comap π)
    {i : Fin (Tag.rank .G2)} (hI : negIndices (g2Datum K) ((P.subgroupOf Y).comap π) = {i})
    (h4 : 4 ≤ Nat.card K) {s : adjointGroup .G2 K} (hs : s ∈ rankOne (g2Datum K).rootGroup i)
    (hsA : s ∈ (P.subgroupOf Y).comap π) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥P) (toP hπ hPY ⟨s, hsA⟩) ∈
      wSup (↥P ⧸ CFSG.pCore 2 ↥P) := by
  set A := (P.subgroupOf Y).comap π with hAdef
  set M := rankOne (g2Datum K).rootGroup i with hMdef
  set U := posUnipotentExcept (g2Datum K) i with hUdef
  have hMA : M ≤ A := rankOne_le_of_mem_negIndices hBA (by rw [hI]; rfl)
  obtain ⟨hMs, hnc⟩ := rankOne_simple h4 i
  set ρ : ↥M →* ↥P ⧸ CFSG.pCore 2 ↥P :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥P)).comp ((toP hπ hPY).toMonoidHom.comp
      (Subgroup.inclusion hMA)) with hρ
  have hUO := posUnipotentExcept_le_pCoreOf hBA hI
  have hN := le_normalizer_rankOne_sup hBA hI
  haveI : Finite ↥(adjointGroup .G2 K) := generated_group_finite .G2 _
  have hB := borelQuotient_g2 (CFSG.AGLEmbedding.ParabAutIrr.adjointQuotientEquiv K).symm
  have hMU : M ≤ Subgroup.normalizer (U : Set (adjointGroup .G2 K)) :=
    rankOne_le_normalizer_posUnipotentExcept hB.ct hB.extras i
  have hnormal : ρ.range.Normal := by
    refine ⟨?_⟩
    rintro _ ⟨m, rfl⟩ x
    obtain ⟨a, rfl⟩ := (QuotientGroup.mk'_surjective _).comp (toP hπ hPY).surjective x
    have hc : (a : adjointGroup .G2 K) * m * (a : adjointGroup .G2 K)⁻¹ ∈
        ((M ⊔ U : Subgroup (adjointGroup .G2 K)) : Set (adjointGroup .G2 K)) :=
      (Subgroup.mem_normalizer_iff.1 (hN a.2) m).1 (le_sup_left (b := U) m.2)
    rw [Subgroup.coe_mul_of_left_le_normalizer_right M U hMU] at hc
    obtain ⟨m', hm', u, hu, hmu⟩ := hc
    refine ⟨⟨m', hm'⟩, ?_⟩
    have huA : u ∈ A := pCoreOf_le A (hUO hu)
    have hk : toP hπ hPY ⟨u, huA⟩ ∈ CFSG.pCore 2 ↥P := toP_mem_pCore hπ hPY (hUO hu)
    have he : a * Subgroup.inclusion hMA m * a⁻¹ = Subgroup.inclusion hMA ⟨m', hm'⟩ * ⟨u, huA⟩ :=
      Subtype.ext (by simpa using hmu.symm)
    simp only [hρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Function.comp_apply]
    have hk' : QuotientGroup.mk' (CFSG.pCore 2 ↥P) (toP hπ hPY ⟨u, huA⟩) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hk
    rw [← map_mul, ← map_mul, ← map_inv, ← map_mul, ← map_inv, ← map_mul, he, map_mul, map_mul,
      hk', mul_one]
  have hle := Lin.range_le_wSup_of_isQuasisimple ρ hnormal (isQuasisimple_of_simple_nonab hnc)
  exact hle ⟨⟨s, hs⟩, rfl⟩

end Transfer

theorem parabCommOn_idxG2_of (hGA : CFSG.Open.GriessAllModelsStatement) :
    ParabCommOn (IsLieOf IdxG2) := by
  intro G _ _ Y P p hp hp2 hY h2 hF hpar hne hna
  left
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd := Lin.odd_card_center_of_pCore_eq_bot (pCore_eq_bot_of_pCoreOf h2)
  obtain ⟨f, hf, ⟨e⟩⟩ := exists_mulEquiv_g2_of_isLieOf hGA hY hodd hF
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have h4 : 4 ≤ Nat.card (GaloisField 2 f) := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨π, hQ, hBA, i, hI⟩ := exists_node_of_parabolic e hpar hne hna
  have hPY : P ≤ Y := hpar.1
  have hinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro z hz
    have hc := hQ.ker_central z hz
    rw [CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := Tag.G2) (K := GaloisField 2 f),
      Subgroup.mem_bot] at hc
    exact hc
  have hπ : Function.Bijective π := ⟨hinj, hQ.surj⟩
  set ψ : adjointGroup .G2 (GaloisField 2 f) ≃* ↥Y := MulEquiv.ofBijective π hπ with hψ
  set A := (P.subgroupOf Y).comap π with hAdef
  set aut : ↥(Subgroup.normalizer (Y : Set G)) →* MulAut (adjointGroup .G2 (GaloisField 2 f)) :=
    (MulAut.congr ψ.symm).toMonoidHom.comp Y.normalizerMonoidHom with haut
  have haut_apply : ∀ (β : ↥(Subgroup.normalizer (Y : Set G)))
      (c : adjointGroup .G2 (GaloisField 2 f)),
      π (aut β c) = Y.normalizerMonoidHom β (π c) := fun β c => by
    change ψ (ψ.symm (Y.normalizerMonoidHom β (ψ c))) = _
    rw [MulEquiv.apply_symm_apply]
    rfl
  have hA : ∀ β : ↥(Subgroup.normalizer (Y : Set G)), (β : G) ∈ Subgroup.normalizer (P : Set G) →
      ∀ a ∈ A, aut β a ∈ A := fun β hβ a ha => by
    rw [hAdef, Subgroup.mem_comap, haut_apply, Subgroup.mem_subgroupOf,
      Subgroup.normalizerMonoidHom_apply_apply_coe]
    exact (Subgroup.mem_normalizer_iff.mp hβ _).mp ha
  have hW : ∀ β : ↥(Subgroup.normalizer (Y : Set G)), (β : G) ∈ Subgroup.normalizer (P : Set G) →
      WCent P β → ∀ s ∈ rankOne (g2Datum (GaloisField 2 f)).rootGroup i,
        aut β s * s⁻¹ ∈ CFSG.Open.pCoreOf 2 A := fun β hβ hWβ s hs => by
    have hsA : s ∈ A := rankOne_le_of_mem_negIndices hBA (by rw [hI]; rfl) hs
    have hmem := toHat_rankOne_mem_wSup hπ hPY hBA hI h4 hs hsA
    have hw := hWβ _ (toP hπ hPY ⟨s, hsA⟩).2 hmem
    have hsA' : aut β s * s⁻¹ ∈ A := A.mul_mem (hA β hβ s hsA) (A.inv_mem hsA)
    refine mem_pCoreOf_of_toP hπ hPY (a := ⟨_, hsA'⟩) ?_
    have hval : ((toP hπ hPY ⟨_, hsA'⟩ : ↥P) : G) =
        (β : G) * ((toP hπ hPY ⟨s, hsA⟩ : ↥P) : G) * (β : G)⁻¹ *
          ((toP hπ hPY ⟨s, hsA⟩ : ↥P) : G)⁻¹ := by
      rw [coe_toP, coe_toP, map_mul, map_inv, haut_apply, Subgroup.coe_mul, Subgroup.coe_inv,
        Subgroup.normalizerMonoidHom_apply_apply_coe]
    obtain ⟨o, ho, hoe⟩ := hw
    have : toP hπ hPY ⟨_, hsA'⟩ = o := Subtype.ext (by rw [hval]; exact hoe.symm)
    rw [this]
    exact ho
  intro b₁ b₂ ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩ ⟨k₃, hk₃⟩ hb₁Y hb₂Y hb₁P hb₂P hW₁ hW₂ y hy
  set β₁ : ↥(Subgroup.normalizer (Y : Set G)) := ⟨b₁, hb₁Y⟩
  set β₂ : ↥(Subgroup.normalizer (Y : Set G)) := ⟨b₂, hb₂Y⟩
  have hodd₃ : Odd (orderOf ⁅aut β₁, aut β₂⁆) := by
    rw [← map_commutatorElement]
    have hpow : (aut ⁅β₁, β₂⁆) ^ p ^ k₃ = 1 := by
      rw [← map_pow]
      have : ⁅β₁, β₂⁆ ^ p ^ k₃ = 1 := Subtype.ext (by simpa [commutatorElement_def] using hk₃)
      rw [this, map_one]
    exact ((hp.odd_of_ne_two hp2).pow (n := k₃)).of_dvd_nat (orderOf_dvd_of_pow_eq_one hpow)
  have hcomm := g2_model_comm hf hK hBA hI (hA β₁ hb₁P) (hA β₂ hb₂P) (hW β₁ hb₁P hW₁)
    (hW β₂ hb₂P hW₂) hodd₃
  rw [← map_commutatorElement] at hcomm
  have hγ : Y.normalizerMonoidHom ⁅β₁, β₂⁆ = 1 := by
    apply (MulAut.congr ψ.symm).injective
    rw [map_one]
    exact hcomm
  have h3 := congrArg (fun γ : MulAut ↥Y => ((γ ⟨y, hy⟩ : ↥Y) : G)) hγ
  simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply] at h3
  have h4' : ((⁅β₁, β₂⁆ : ↥(Subgroup.normalizer (Y : Set G))) : G) = ⁅b₁, b₂⁆ := by
    simp [β₁, β₂, commutatorElement_def]
  rw [h4'] at h3
  calc ⁅b₁, b₂⁆ * y = ⁅b₁, b₂⁆ * y * ⁅b₁, b₂⁆⁻¹ * ⁅b₁, b₂⁆ := by group
    _ = y * ⁅b₁, b₂⁆ := by rw [h3]

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.GTwo
