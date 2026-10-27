module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.FiveSetting
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.FFAlt
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Setting
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.U33Proved
import CFSG.Quasithin.Recognition.M12AmalAutIso
public import CFSG.Monster.B.TwoA.Census.PermClasses


public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.Open
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open scoped commutatorElement

section Preimage

variable {X : Type} [Group X] {T : Subgroup X} (L' : Subgroup X)

theorem exists_mul_of_mem_comap_gnImg {x : X}
    (hx : x ∈ (gnImg T L').comap (QuotientGroup.mk' (gnC T))) :
    ∃ l ∈ L', ∃ c ∈ gnC T, x = l * c := by
  obtain ⟨l, hl, hlx⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp hx)
  refine ⟨l, hl, l⁻¹ * x, ?_, by group⟩
  rw [← QuotientGroup.eq]
  exact hlx

theorem le_comap_gnImg : L' ≤ (gnImg T L').comap (QuotientGroup.mk' (gnC T)) :=
  Subgroup.le_comap_map _ _

theorem commutator_gnV_comap_gnImg :
    ⁅gnV T, (gnImg T L').comap (QuotientGroup.mk' (gnC T))⁆ = ⁅gnV T, L'⁆ := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro v hv x hx
    obtain ⟨l, hl, c, hc, rfl⟩ := exists_mul_of_mem_comap_gnImg L' hx
    have hcv : v * c = c * v := Subgroup.mem_centralizer_iff.mp hc v hv
    have e : ⁅v, l * c⁆ = ⁅v, l⁆ := by
      simp only [commutatorElement_def, mul_inv_rev]
      calc v * (l * c) * v⁻¹ * (c⁻¹ * l⁻¹) = v * l * (c * v⁻¹ * c⁻¹) * l⁻¹ := by group
        _ = v * l * v⁻¹ * l⁻¹ := by
          have : c * v⁻¹ * c⁻¹ = v⁻¹ := by
            have h1 : c * v = v * c := hcv.symm
            calc c * v⁻¹ * c⁻¹ = v⁻¹ * (v * c) * v⁻¹ * c⁻¹ := by group
              _ = v⁻¹ * (c * v) * v⁻¹ * c⁻¹ := by rw [hcv]
              _ = v⁻¹ := by group
          rw [this]
    rw [e]
    exact Subgroup.commutator_mem_commutator hv hl
  · exact Subgroup.commutator_mono le_rfl (le_comap_gnImg L')

theorem mem_centralizer_comap_gnImg_iff {y : X} (hy : y ∈ gnV T) :
    y ∈ Subgroup.centralizer ((gnImg T L').comap (QuotientGroup.mk' (gnC T)) : Set X) ↔
      y ∈ Subgroup.centralizer (L' : Set X) := by
  constructor
  · intro h
    exact Subgroup.centralizer_le (le_comap_gnImg L') h
  · intro h
    rw [Subgroup.mem_centralizer_iff] at h ⊢
    intro x hx
    obtain ⟨l, hl, c, hc, rfl⟩ := exists_mul_of_mem_comap_gnImg L' hx
    have hcy : y * c = c * y := Subgroup.mem_centralizer_iff.mp hc y hy
    calc l * c * y = l * (c * y) := by group
      _ = l * (y * c) := by rw [hcy]
      _ = l * y * c := by group
      _ = y * l * c := by rw [h l hl]
      _ = y * (l * c) := by group

theorem le_normalizer_comap_gnImg {W : Subgroup X} (hWV : W ≤ gnV T)
    (hW : L' ≤ Subgroup.normalizer (W : Set X)) :
    (gnImg T L').comap (QuotientGroup.mk' (gnC T)) ≤ Subgroup.normalizer (W : Set X) := by
  intro x hx
  obtain ⟨l, hl, c, hc, rfl⟩ := exists_mul_of_mem_comap_gnImg L' hx
  have hfix : ∀ u ∈ gnV T, c * u * c⁻¹ = u := fun u hu => by
    have h := Subgroup.mem_centralizer_iff.mp hc u hu
    calc c * u * c⁻¹ = u * c * c⁻¹ := by rw [h]
      _ = u := by group
  have hcW : c ∈ Subgroup.normalizer (W : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      rw [hfix w (hWV hw)]
      exact hw
    · intro hw
      have h1 := hfix _ (hWV hw)
      have h2 : c * w * c⁻¹ = w := by
        calc c * w * c⁻¹ = c⁻¹ * (c * (c * w * c⁻¹) * c⁻¹) * c := by group
          _ = c⁻¹ * (c * w * c⁻¹) * c := by rw [h1]
          _ = w := by group
      rw [← h2]
      exact hw
  exact Subgroup.mul_mem _ (hW hl) hcW

theorem commutator_gnV_le : ⁅gnV T, L'⁆ ≤ gnV T := by
  have : (gnV T).Normal := Subgroup.normalClosure_normal
  exact Subgroup.commutator_le_left _ _

theorem commutator_inf_centralizer_comap_gnImg :
    ⁅gnV T, (gnImg T L').comap (QuotientGroup.mk' (gnC T))⁆ ⊓
        Subgroup.centralizer ((gnImg T L').comap (QuotientGroup.mk' (gnC T)) : Set X) =
      ⁅gnV T, L'⁆ ⊓ Subgroup.centralizer (L' : Set X) := by
  rw [commutator_gnV_comap_gnImg]
  ext y
  simp only [Subgroup.mem_inf]
  exact ⟨fun h => ⟨h.1, (mem_centralizer_comap_gnImg_iff L' (commutator_gnV_le L' h.1)).mp h.2⟩,
    fun h => ⟨h.1, (mem_centralizer_comap_gnImg_iff L' (commutator_gnV_le L' h.1)).mpr h.2⟩⟩

theorem hasIrr_of_comap_gnImg
    (h : HasIrreducibleCommutatorQuotient ((gnImg T L').comap (QuotientGroup.mk' (gnC T)))
      (gnV T)) :
    HasIrreducibleCommutatorQuotient L' (gnV T) := by
  obtain ⟨hlt, hmin⟩ := h
  rw [commutator_inf_centralizer_comap_gnImg, commutator_gnV_comap_gnImg] at hlt hmin
  exact ⟨hlt, fun W hW1 hW2 hW3 =>
    hmin W hW1 hW2 (le_normalizer_comap_gnImg L' (hW2.trans (commutator_gnV_le L')) hW3)⟩

theorem relIndex_comap_gnImg :
    (⁅gnV T, (gnImg T L').comap (QuotientGroup.mk' (gnC T))⁆ ⊓
        Subgroup.centralizer ((gnImg T L').comap (QuotientGroup.mk' (gnC T)) : Set X)).relIndex
      ⁅gnV T, (gnImg T L').comap (QuotientGroup.mk' (gnC T))⁆ =
      (⁅gnV T, L'⁆ ⊓ Subgroup.centralizer (L' : Set X)).relIndex ⁅gnV T, L'⁆ := by
  rw [commutator_inf_centralizer_comap_gnImg, commutator_gnV_comap_gnImg]

end Preimage

section Transport

variable {X Y : Type} [Group X] [Group Y] (f : X →* Y) (hf : Function.Injective f)
  (L' V' : Subgroup X)
include hf

theorem map_commutator_inf_centralizer :
    (⁅V', L'⁆ ⊓ Subgroup.centralizer (L' : Set X)).map f =
      ⁅V'.map f, L'.map f⁆ ⊓ Subgroup.centralizer ((L'.map f : Subgroup Y) : Set Y) := by
  rw [← Subgroup.map_commutator]
  ext y
  simp only [Subgroup.mem_inf, Subgroup.mem_map]
  constructor
  · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
    refine ⟨⟨x, hx1, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨l, hl, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hx2 l hl]
  · rintro ⟨⟨x, hx1, rfl⟩, hx2⟩
    refine ⟨x, ⟨hx1, ?_⟩, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    apply hf
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_iff.mp hx2 (f l) ⟨l, hl, rfl⟩

theorem hasIrr_map (h : HasIrreducibleCommutatorQuotient L' V') :
    HasIrreducibleCommutatorQuotient (L'.map f) (V'.map f) := by
  obtain ⟨hlt, hmin⟩ := h
  unfold HasIrreducibleCommutatorQuotient
  rw [← map_commutator_inf_centralizer f hf L' V', ← Subgroup.map_commutator]
  refine ⟨(Subgroup.map_lt_map_iff_of_injective hf).mpr hlt, fun W hW1 hW2 hW3 => ?_⟩
  have hWr : W ≤ f.range := hW2.trans (Subgroup.map_le_range f _)
  have hWe : (W.comap f).map f = W := Subgroup.map_comap_eq_self hWr
  have h1 : ⁅V', L'⁆ ⊓ Subgroup.centralizer (L' : Set X) ≤ W.comap f :=
    Subgroup.map_le_iff_le_comap.mp hW1
  have h2 : W.comap f ≤ ⁅V', L'⁆ := by
    rw [← Subgroup.map_le_map_iff_of_injective hf, hWe]
    exact hW2
  have h3 : L' ≤ Subgroup.normalizer ((W.comap f : Subgroup X) : Set X) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro w
    have := Subgroup.mem_normalizer_iff.mp (hW3 ⟨l, hl, rfl⟩) (f w)
    simp only [Subgroup.mem_comap, map_mul, map_inv]
    exact this
  rcases hmin _ h1 h2 h3 with h | h
  · left
    rw [← hWe, h]
  · right
    rw [← hWe, h]

theorem relIndex_map_commutator {n : ℕ}
    (h : (⁅V', L'⁆ ⊓ Subgroup.centralizer (L' : Set X)).relIndex ⁅V', L'⁆ = n) :
    (⁅V'.map f, L'.map f⁆ ⊓ Subgroup.centralizer ((L'.map f : Subgroup Y) : Set Y)).relIndex
      ⁅V'.map f, L'.map f⁆ = n := by
  rw [← map_commutator_inf_centralizer f hf L' V', ← Subgroup.map_commutator,
    Subgroup.relIndex_map_map_of_injective _ _ hf, h]

end Transport

section Socle

variable {G : Type} [Group G] [Finite G]

theorem relIndex_sup_le_of_le_normalizer {H K : Subgroup G}
    (hK : K ≤ Subgroup.normalizer (H : Set G)) :
    K.relIndex (H ⊔ K) ≤ (H ⊓ K).relIndex H := by
  let f : ↥H ⧸ ((H ⊓ K).subgroupOf H) → ↥(H ⊔ K) ⧸ (K.subgroupOf (H ⊔ K)) :=
    Quotient.map' (fun u : ↥H => (⟨(u : G), Subgroup.mem_sup_left u.2⟩ : ↥(H ⊔ K)))
      (fun u v huv => by
        rw [QuotientGroup.leftRel_apply] at huv ⊢
        have := Subgroup.mem_subgroupOf.mp huv
        exact Subgroup.mem_subgroupOf.mpr (by simpa using this.2))
  have hf : Function.Surjective f := by
    intro q
    induction q using Quotient.inductionOn' with
    | h x =>
      have hx : (x : G) ∈ ((H ⊔ K : Subgroup G) : Set G) := x.2
      rw [Subgroup.coe_mul_of_right_le_normalizer_left H K hK] at hx
      obtain ⟨a, ha, b, hb, hab⟩ := hx
      refine ⟨Quotient.mk'' ⟨a, ha⟩, ?_⟩
      show Quotient.mk'' _ = Quotient.mk'' _
      apply Quotient.sound'
      rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf]
      change a⁻¹ * (x : G) ∈ K
      rw [← hab]
      have : a⁻¹ * (a * b) = b := by group
      rw [this]
      exact hb
  have := Nat.card_le_card_of_surjective f hf
  simpa [Subgroup.relIndex, Subgroup.index] using this

theorem socleLE_of_relIndex_eq {L V : Subgroup G} (hLV : L ≤ Subgroup.normalizer (V : Set G))
    {n : ℕ} (h : (⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G)).relIndex ⁅V, L⁆ = n) :
    SocleLE L V n := by
  have hUV : ⁅V, L⁆ ≤ V := by
    rw [Subgroup.commutator_le]
    intro v hv l hl
    have : l * v⁻¹ * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hLV hl) _).mp (V.inv_mem hv)
    have e : ⁅v, l⁆ = v * (l * v⁻¹ * l⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact V.mul_mem hv this
  have hK : V ⊓ Subgroup.centralizer (L : Set G) ≤
      Subgroup.normalizer ((⁅V, L⁆ : Subgroup G) : Set G) := by
    intro v hv
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => conj_mem_commutator_left hv.1 hx, fun hx => ?_⟩
    have := conj_mem_commutator_left (V.inv_mem hv.1) hx
    have e : v⁻¹ * (v * x * v⁻¹) * v⁻¹⁻¹ = x := by group
    rwa [e] at this
  unfold SocleLE
  refine (relIndex_sup_le_of_le_normalizer hK).trans (le_of_eq ?_)
  rw [← h]
  congr 1
  ext x
  simp only [Subgroup.mem_inf]
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hUV h.1, h.2⟩⟩

end Socle

section Bridge

variable {G : Type} [Group G] [Finite G] {M S L : Subgroup G}

omit [Finite G] in
theorem thompsonJ_subgroupOf (hSM : S ≤ M) :
    thompsonJ (S.subgroupOf M) = (thompsonJ S).subgroupOf M := by
  have hJS : thompsonJ S ≤ S := CFSG.Quasithin.C1GN.thompsonJ_le S
  apply Subgroup.map_injective M.subtype_injective
  rw [← CFSG.Quasithin.AmalTransport.thompsonJ_map_of_injective M.subtype M.subtype_injective,
    Subgroup.map_subgroupOf_eq_of_le hSM, Subgroup.map_subgroupOf_eq_of_le (hJS.trans hSM)]

theorem fiveStar_commutator_thompsonJ (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) (hJ : ¬ ⁅L, thompsonJ S⁆ ≤ pCoreOf 2 M) :
    ⁅gnImg (S.subgroupOf M) (L.subgroupOf M),
        gnImg (S.subgroupOf M) (thompsonJ (S.subgroupOf M))⁆ =
      gnImg (S.subgroupOf M) (L.subgroupOf M) := by
  have hSM := hA.twoRadical.1
  have hQS : pCoreOf 2 M ≤ S := CFSG.Quasithin.c2_1_pCore_le hA.twoRadical
  have hJS : thompsonJ S ≤ S := CFSG.Quasithin.C1GN.thompsonJ_le S
  have hbar := commutator_barM_thompsonJ_eq hL hSM hSL hJ
  rw [← map_subgroupOf_rhoX le_rfl hL.le, ← map_subgroupOf_rhoX le_rfl (hJS.trans hSM),
    ← Subgroup.map_commutator] at hbar
  have hle : L.subgroupOf M ≤
      ⁅L.subgroupOf M, (thompsonJ S).subgroupOf M⁆ ⊔ (rhoX M M le_rfl).ker :=
    Subgroup.map_le_map_iff.mp hbar.ge
  have hker : (rhoX M M le_rfl).ker ≤ gnC (S.subgroupOf M) := rhoX_ker_le le_rfl hSM hQS
  rw [thompsonJ_subgroupOf hSM]
  unfold gnImg
  rw [← Subgroup.map_commutator]
  apply le_antisymm
  · apply Subgroup.map_mono
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_subgroupOf] at ha hb ⊢
    have hb' : (b : G) * (a : G)⁻¹ * (b : G)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hSL (hJS hb)) _).mp (L.inv_mem ha)
    have e : ((⁅a, b⁆ : ↥M) : G) = (a : G) * ((b : G) * (a : G)⁻¹ * (b : G)⁻¹) := by
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact L.mul_mem ha hb'
  · calc (L.subgroupOf M).map (QuotientGroup.mk' (gnC (S.subgroupOf M)))
        ≤ (⁅L.subgroupOf M, (thompsonJ S).subgroupOf M⁆ ⊔ (rhoX M M le_rfl).ker).map
            (QuotientGroup.mk' (gnC (S.subgroupOf M))) := Subgroup.map_mono hle
      _ = (⁅L.subgroupOf M, (thompsonJ S).subgroupOf M⁆).map
            (QuotientGroup.mk' (gnC (S.subgroupOf M))) := by
        have hk : (rhoX M M le_rfl).ker.map (QuotientGroup.mk' (gnC (S.subgroupOf M))) = ⊥ := by
          rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
          exact hker
        rw [Subgroup.map_sup, hk, sup_bot_eq]

theorem fiveStar_mulEquiv (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L)
    (hZ : Subgroup.center ↥(barM M L) = ⊥) :
    Nonempty (↥(gnImg (S.subgroupOf M) (L.subgroupOf M)) ≃* ↥(barM M L)) := by
  obtain ⟨-, hdvd, ⟨e⟩, -⟩ := blockStar_facts le_rfl hA.twoRadical.1
    (CFSG.Quasithin.c2_1_pCore_le hA.twoRadical) hL hL.le (not_le_gnC_of_weakSBlock hA hL)
  rw [hZ, Subgroup.card_bot, Nat.dvd_one] at hdvd
  have hZ' := Subgroup.eq_bot_of_card_eq _ hdvd
  exact ⟨(QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ'.symm)).trans
    (e.symm.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot))⟩

omit [Finite G] in
theorem center_barM_eq_bot_of_alt {n : ℕ} (hn : 4 ≤ n)
    (e : ↥(barM M L) ≃* alternatingGroup (Fin n)) : Subgroup.center ↥(barM M L) = ⊥ := by
  have h := Subgroup.map_center_eq e
  rw [alternatingGroup.center_eq_bot (by simpa using hn)] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h

theorem citedFive_of_fiveThreeAlt (hF : GN.AGL81FiveThreeAlt) :
    CitedFive := by
  intro G _ _ M S L hK hA hL hJ hrow
  have hSM := hA.twoRadical.1
  have hQS : pCoreOf 2 M ≤ S := CFSG.Quasithin.c2_1_pCore_le hA.twoRadical
  have hSL : S ≤ Subgroup.normalizer (L : Set G) :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.le_normalizer_of_isWeakSBlock hK hA hL
  have hS2 : IsPGroup 2 S := by
    rw [hA.twoRadical.2.2]
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) _
  have hT2 : IsPGroup 2 (S.subgroupOf M) := hS2.comap_subtype
  have hchar : CharTwo (⊤ : Subgroup ↥M) := charTwo_top_of_le hA.charTwo
    (CFSG.LieType.BorelTits.pCoreOf_le (r := 2) M) le_rfl
  have hcore : pCoreOf 2 (⊤ : Subgroup ↥M) = (pCoreOf 2 M).subgroupOf M := by
    rw [← Subgroup.subgroupOf_self (H := M)]
    exact (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_subgroupOf 2 M M le_rfl).symm
  have hQT : pCoreOf 2 (⊤ : Subgroup ↥M) ≤ S.subgroupOf M := by
    rw [hcore]
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hQS (Subgroup.mem_subgroupOf.mp hx))
  obtain ⟨h7, h6, hU⟩ := hF ↥M (S.subgroupOf M) (cfsgIsKGroup_of_open hK) hchar hT2 hQT
    (gnImg (S.subgroupOf M) (L.subgroupOf M)) (fiveStar_isComponent hA hL)
    (fiveStar_commutator_thompsonJ hA hL hSL hJ)
  have hmapV : (gnV (S.subgroupOf M)).map M.subtype = mModule M S := map_gnV_eq_mModule hSM
  have hmapL : (L.subgroupOf M).map M.subtype = L := Subgroup.map_subgroupOf_eq_of_le hL.le
  have hirr : HasIrreducibleCommutatorQuotient
      ((gnImg (S.subgroupOf M) (L.subgroupOf M)).comap
        (QuotientGroup.mk' (gnC (S.subgroupOf M)))) (gnV (S.subgroupOf M)) →
      HasIrreducibleCommutatorQuotient L (mModule M S) := fun hI => by
    have := hasIrr_map M.subtype M.subtype_injective (L.subgroupOf M) (gnV (S.subgroupOf M))
      (hasIrr_of_comap_gnImg (L.subgroupOf M) hI)
    rwa [hmapV, hmapL] at this
  have hsoc : ∀ n : ℕ, (⁅gnV (S.subgroupOf M), (gnImg (S.subgroupOf M) (L.subgroupOf M)).comap
        (QuotientGroup.mk' (gnC (S.subgroupOf M)))⁆ ⊓
        Subgroup.centralizer ((gnImg (S.subgroupOf M) (L.subgroupOf M)).comap
          (QuotientGroup.mk' (gnC (S.subgroupOf M))) : Set ↥M)).relIndex
        ⁅gnV (S.subgroupOf M), (gnImg (S.subgroupOf M) (L.subgroupOf M)).comap
          (QuotientGroup.mk' (gnC (S.subgroupOf M)))⁆ = n → SocleLE L (mModule M S) n :=
    fun n hn => by
      rw [relIndex_comap_gnImg] at hn
      have := relIndex_map_commutator M.subtype M.subtype_injective (L.subgroupOf M)
        (gnV (S.subgroupOf M)) hn
      rw [hmapV, hmapL] at this
      exact socleLE_of_relIndex_eq (hL.le.trans (normalizer_mModule M S)) this
  have hiso : Subgroup.center ↥(barM M L) = ⊥ → ∀ {Z : Type} [Group Z], (↥(barM M L) ≃* Z) →
      Nonempty (↥(gnImg (S.subgroupOf M) (L.subgroupOf M)) ≃* Z) := fun hZ _ _ e => by
    obtain ⟨φ⟩ := fiveStar_mulEquiv hA hL hZ
    exact ⟨φ.trans e⟩
  have h6' : Nonempty (↥(barM M L) ≃* alternatingGroup (Fin 6)) →
      Nonempty (↥(gnImg (S.subgroupOf M) (L.subgroupOf M)) ≃* alternatingGroup (Fin 6)) :=
    fun ⟨e⟩ => hiso (center_barM_eq_bot_of_alt (by norm_num) e) e
  have hU' : IsUThreeThree ↥(barM M L) →
      ∃ d : TauCeti.ValidLieTypeIndex, (∃ q : TauCeti.PrimePower, q.card = 3 ∧
        d.1 = .twistedA 2 q) ∧
        Nonempty (↥(gnImg (S.subgroupOf M) (L.subgroupOf M)) ≃* (TauCeti.CFSGIndex.lie d).Group) :=
    fun hU3 => by
      have hZ := (u33_simple_card_center hU3).2.2
      obtain ⟨d, hd, ⟨e⟩⟩ := hU3
      exact ⟨d, hd, hiso hZ e⟩
  refine ⟨?_, fun h => ?_, fun h => ?_⟩
  · rcases hrow with h | h | hU3
    · exact hirr (h6 (h6' h)).1
    · obtain ⟨e⟩ := h
      exact hirr (h7 (hiso (center_barM_eq_bot_of_alt (by norm_num) e) e))
    · exact hirr (hU (hU' hU3)).1
  · simpa using hsoc _ (h6 (h6' h)).2
  · simpa using hsoc _ (hU (hU' h)).2

end Bridge

end CFSG.AGLEmbeddingD2.McLaughlin
