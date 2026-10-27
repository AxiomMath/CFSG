module

public import CFSG.GH74.GLS.C3.Layer1.Th2P85Defs
public import CFSG.GH74.GLS.C3.Layer1.Th2HYStruct

public section

namespace CFSG.GH74.GLS.Th2.P85

open Subgroup CFSG Blueprint CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2
  CFSG.GH74.GLS.TwoThin
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem imgM_mono {M X Y : Subgroup G} (h : X ≤ Y) : imgM M X ≤ imgM M Y :=
  Subgroup.map_mono (Subgroup.comap_mono h)

omit [Finite G] in
theorem mem_imgM_iff {M X : Subgroup G} {w : Mb M} :
    w ∈ imgM M X ↔ ∃ m : ↥M, (m : G) ∈ X ∧ barMk ↥M m = w := by
  unfold imgM
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]

omit [Finite G] in
theorem barMk_eq_one_iff_mem_pPrimeCoreOf {M : Subgroup G} (m : ↥M) :
    barMk ↥M m = 1 ↔ (m : G) ∈ pPrimeCoreOf 2 M := by
  rw [C3.Layer1.Back.Setup91.mem_pPrimeCoreOf_iff]
  exact ⟨fun h => ⟨m.2, (QuotientGroup.eq_one_iff m).1 h⟩,
    fun ⟨_, h⟩ => (QuotientGroup.eq_one_iff m).2 h⟩

omit [Finite G] in
@[expose] def toImgM {K M : Subgroup G} (hKM : K ≤ M) : ↥K →* ↥(imgM M K) :=
  ((barMk ↥M).comp (Subgroup.inclusion hKM)).codRestrict (imgM M K) fun k =>
    mem_imgM_iff.2 ⟨Subgroup.inclusion hKM k, k.2, rfl⟩

omit [Finite G] in
theorem toImgM_surjective {K M : Subgroup G} (hKM : K ≤ M) :
    Function.Surjective (toImgM hKM) := by
  intro w
  obtain ⟨m, hm, hw⟩ := mem_imgM_iff.1 w.2
  exact ⟨⟨m, hm⟩, Subtype.ext hw⟩

omit [Finite G] in
theorem mem_ker_toImgM {K M : Subgroup G} (hKM : K ≤ M) (k : ↥K) :
    k ∈ (toImgM hKM).ker ↔ (k : G) ∈ pPrimeCoreOf 2 M := by
  rw [MonoidHom.mem_ker]
  refine Iff.trans ?_ (barMk_eq_one_iff_mem_pPrimeCoreOf (M := M) ⟨k, hKM k.2⟩)
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem odd_card_ker_toImgM {K M : Subgroup G} (hKM : K ≤ M) :
    Odd (Nat.card (toImgM hKM).ker) := by
  have h1 : (toImgM hKM).ker.map (Subgroup.inclusion hKM) ≤ (barMk ↥M).ker := by
    rintro _ ⟨k, hk, rfl⟩
    exact MonoidHom.mem_ker.2
      ((barMk_eq_one_iff_mem_pPrimeCoreOf _).2 ((mem_ker_toImgM hKM k).1 hk))
  have h2 := Subgroup.card_dvd_of_le h1
  rw [Subgroup.card_map_of_injective (Subgroup.inclusion_injective hKM)] at h2
  exact Odd.of_dvd_nat odd_card_ker_barMk h2

theorem eq_sup_of_imgM_eq {K L M : Subgroup G} (hLM : L ≤ M) (hKL : K ≤ L)
    (h : imgM M K = imgM M L) : L = pPrimeCoreOf 2 L ⊔ K := by
  refine le_antisymm (fun l hl => ?_) (sup_le (TwoThin.pPrimeCoreOf_le L) hKL)
  have hlM : l ∈ M := hLM hl
  have hmem : barMk ↥M ⟨l, hlM⟩ ∈ imgM M L := mem_imgM_iff.2 ⟨⟨l, hlM⟩, hl, rfl⟩
  rw [← h] at hmem
  obtain ⟨k, hk, hkl⟩ := mem_imgM_iff.1 hmem
  have h1 : barMk ↥M (k⁻¹ * ⟨l, hlM⟩) = 1 := by
    rw [map_mul, map_inv, hkl, inv_mul_cancel]
  have h2 : (k : G)⁻¹ * l ∈ pPrimeCoreOf 2 M := (barMk_eq_one_iff_mem_pPrimeCoreOf _).1 h1
  have h3 : (k : G)⁻¹ * l ∈ L := L.mul_mem (L.inv_mem (hKL hk)) hl
  have h4 : (k : G)⁻¹ * l ∈ pPrimeCoreOf 2 L := Th2.inf_le_pPrimeCoreOf hLM ⟨h2, h3⟩
  have h5 : (k : G) * ((k : G)⁻¹ * l) ∈ K ⊔ pPrimeCoreOf 2 L := Subgroup.mul_mem_sup hk h4
  rw [sup_comm]
  simpa using h5

theorem pPrimeCoreOf_le_of_eq_sup {K L : Subgroup G} (hKL : K ≤ L)
    (hLeq : L = pPrimeCoreOf 2 L ⊔ K) : pPrimeCoreOf 2 K ≤ pPrimeCoreOf 2 L := by
  have hOL : pPrimeCoreOf 2 L ≤ L := TwoThin.pPrimeCoreOf_le L
  have hPK : pPrimeCoreOf 2 K ≤ K := TwoThin.pPrimeCoreOf_le K
  have hKO : ∀ k ∈ K, k ∈ normalizer (pPrimeCoreOf 2 L : Set G) := fun k hk =>
    TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer (hKL hk))
  have hKP : ∀ k ∈ K, k ∈ normalizer (pPrimeCoreOf 2 K : Set G) := fun k hk =>
    TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer hk)
  have hW : L ≤ normalizer ((pPrimeCoreOf 2 L ⊔ pPrimeCoreOf 2 K : Subgroup G) : Set G) :=
    hLeq.le.trans (sup_le (fun o ho => Subgroup.le_normalizer (Subgroup.mem_sup_left ho))
      fun k hk => Th2.mem_normalizer_sup (hKO k hk) (hKP k hk))
  have hodd : Odd (Nat.card ↥(pPrimeCoreOf 2 L ⊔ pPrimeCoreOf 2 K)) := by
    have hcard := Th2.HY.card_sup_mul_card_inf_of_le_normalizer
      (A := pPrimeCoreOf 2 K) (B := pPrimeCoreOf 2 L) fun p hp => hKO p (hPK hp)
    rw [sup_comm]
    have : Odd (Nat.card ↥(pPrimeCoreOf 2 K ⊔ pPrimeCoreOf 2 L) *
        Nat.card ↥(pPrimeCoreOf 2 K ⊓ pPrimeCoreOf 2 L)) := by
      rw [hcard]
      exact (TwoThin.card_pPrimeCoreOf_odd K).mul (TwoThin.card_pPrimeCoreOf_odd L)
    exact (Nat.odd_mul.1 this).1
  have hle := Th2.HY.le_pPrimeCoreOf_of_norm (N := pPrimeCoreOf 2 L ⊔ pPrimeCoreOf 2 K) (X := L)
    (sup_le hOL (hPK.trans hKL))
    (fun x hx w hw => (Subgroup.mem_normalizer_iff.1 (hW hx) w).1 hw) hodd
  exact le_sup_right.trans hle

theorem kBar_equiv_imgM {K M : Subgroup G} (hKM : K ≤ M) :
    Nonempty ((↥(imgM M K) ⧸ pPrimeCore 2 ↥(imgM M K)) ≃* kBar K) := by
  let g : ↥K →* ↥(imgM M K) ⧸ pPrimeCore 2 ↥(imgM M K) :=
    (QuotientGroup.mk' (pPrimeCore 2 ↥(imgM M K))).comp (toImgM hKM)
  have hg : Function.Surjective g := (QuotientGroup.mk'_surjective _).comp (toImgM_surjective hKM)
  have hker : g.ker = pPrimeCore 2 ↥K := by
    apply le_antisymm
    · have hcomap : g.ker = (pPrimeCore 2 ↥(imgM M K)).comap (toImgM hKM) := by
        ext k
        simp [g, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
      have hodd : Odd (Nat.card g.ker) := by
        rw [hcomap]
        exact CFSG.OrderReductions.OddCore.odd_preimage (toImgM hKM) (toImgM_surjective hKM)
          (odd_card_ker_toImgM hKM) _ (odd_card_pPrimeCore _)
      exact CFSG.GroupTheory.le_pPrimeCore_of_normal inferInstance (Nat.coprime_two_left.2 hodd)
    · intro k hk
      have hN : ((pPrimeCore 2 ↥K).map (toImgM hKM)).Normal :=
        Subgroup.Normal.map inferInstance _ (toImgM_surjective hKM)
      have hcop : Nat.Coprime 2 (Nat.card ↥((pPrimeCore 2 ↥K).map (toImgM hKM))) :=
        Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ _) CFSG.pPrimeCore_coprime_card
      have hle := CFSG.GroupTheory.le_pPrimeCore_of_normal hN hcop
      exact (QuotientGroup.eq_one_iff _).2 (hle (Subgroup.mem_map_of_mem _ hk))
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective g hg).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker)⟩

theorem ker_toImgM_eq {K M : Subgroup G} (hKM : K ≤ M)
    (h : pPrimeCoreOf 2 K ≤ pPrimeCoreOf 2 M) : (toImgM hKM).ker = pPrimeCore 2 ↥K := by
  ext k
  rw [mem_ker_toImgM]
  constructor
  · intro hk
    obtain ⟨_, hk'⟩ := C3.Layer1.Back.Setup91.mem_pPrimeCoreOf_iff.1
      (Th2.inf_le_pPrimeCoreOf hKM ⟨hk, k.2⟩)
    exact hk'
  · intro hk
    exact h ⟨k, hk, rfl⟩

theorem imgM_equiv_kBar {K L M : Subgroup G} (hKL : K ≤ L) (hsub : IsSubnormalIn L M)
    (hLeq : L = pPrimeCoreOf 2 L ⊔ K) : Nonempty (↥(imgM M L) ≃* kBar K) := by
  have hLM : L ≤ M := hsub.1
  have hKM : K ≤ M := hKL.trans hLM
  have hOLM : pPrimeCoreOf 2 L ≤ pPrimeCoreOf 2 M := Th2.pPrimeCoreOf_le_of_subnormal hsub
  have hKO : pPrimeCoreOf 2 K ≤ pPrimeCoreOf 2 M :=
    (pPrimeCoreOf_le_of_eq_sup hKL hLeq).trans hOLM
  have hKN : K ≤ normalizer (pPrimeCoreOf 2 L : Set G) := fun k hk =>
    TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer (hKL hk))
  have himg : imgM M L ≤ imgM M K := by
    intro w hw
    obtain ⟨m, hm, rfl⟩ := mem_imgM_iff.1 hw
    have hm' : (m : G) ∈ K ⊔ pPrimeCoreOf 2 L := by rw [sup_comm, ← hLeq]; exact hm
    obtain ⟨k, hk, o, ho, hmko⟩ := (Th2.HY.mem_sup_iff_mul_of_le_normalizer hKN).1 hm'
    refine mem_imgM_iff.2 ⟨⟨k, hKM hk⟩, hk, ?_⟩
    have ho1 : barMk ↥M ⟨o, hLM (TwoThin.pPrimeCoreOf_le L ho)⟩ = 1 :=
      (barMk_eq_one_iff_mem_pPrimeCoreOf _).2 (hOLM ho)
    have hm2 : m = ⟨k, hKM hk⟩ * ⟨o, hLM (TwoThin.pPrimeCoreOf_le L ho)⟩ := Subtype.ext hmko
    rw [hm2, map_mul, ho1, mul_one]
  have hEq : imgM M L = imgM M K := le_antisymm himg (imgM_mono hKL)
  have hker : (toImgM hKM).ker = pPrimeCore 2 ↥K := ker_toImgM_eq hKM hKO
  exact ⟨(MulEquiv.subgroupCongr hEq).trans
    ((QuotientGroup.quotientKerEquivOfSurjective (toImgM hKM) (toImgM_surjective hKM)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hker))⟩

theorem equiv_imgM {M Q : Subgroup G} (hQM : Q ≤ M) (hQ : IsPGroup 2 ↥Q) :
    Nonempty (↥Q ≃* ↥(imgM M Q)) := by
  have hinj : Function.Injective (toImgM hQM) := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have h1 : (k : G) ∈ pPrimeCoreOf 2 M := (mem_ker_toImgM hQM k).1 hk
    have h2 : (k : G) ∈ Q ⊓ pPrimeCoreOf 2 M := ⟨k.2, h1⟩
    rw [C3.Layer1.Back.Setup91.inf_pPrimeCoreOf_eq_bot M hQ, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  exact ⟨MulEquiv.ofBijective (toImgM hQM) ⟨hinj, toImgM_surjective hQM⟩⟩

theorem factorization_card_imgM {A M : Subgroup G} (hAM : A ≤ M) :
    (Nat.card ↥(imgM M A)).factorization 2 = (Nat.card ↥A).factorization 2 := by
  have h : Nat.card ↥(imgM M A) *
      Nat.card ↥((barMk ↥M).ker.subgroupOf (A.subgroupOf M)) = Nat.card ↥(A.subgroupOf M) :=
    CFSG.OrderReductions.StrongEmbeddingInheritance.map_card_mul_kernel_card (barMk ↥M)
      (A.subgroupOf M)
  have hodd : Odd (Nat.card ↥((barMk ↥M).ker.subgroupOf (A.subgroupOf M))) :=
    CFSG.ComponentClassification.OddKernel.odd_card_restriction_kernel (barMk ↥M)
      odd_card_ker_barMk (A.subgroupOf M)
  have hA : Nat.card ↥(A.subgroupOf M) = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv
  rw [hA] at h
  have h2 := congrArg (fun n => n.factorization 2) h
  simp only [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply] at h2
  have h3 := C3.Layer1.Back.Setup91.factorization_two_of_odd hodd
  omega

theorem isSylowOf_imgM_of_le {A M Q : Subgroup G} (hAM : A ≤ M) (hQ : IsSylowOf 2 Q A) :
    IsSylowOf 2 (imgM M Q) (imgM M A) := by
  obtain ⟨e⟩ := equiv_imgM (hQ.le.trans hAM) hQ.isPGroup
  refine isSylowOf_of_card (imgM_mono hQ.le) ?_
  rw [← Nat.card_congr e.toEquiv, hQ.card_eq, factorization_card_imgM hAM]

theorem imgM_cmbar_eq {K M : Subgroup G} (hKM : K ≤ M) :
    imgM M (CMbar M K) = centralizer (imgM M K : Set (Mb M)) := by
  ext w
  constructor
  · intro hw
    obtain ⟨c, hc, rfl⟩ := mem_imgM_iff.1 hw
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, hk, rfl⟩ := mem_imgM_iff.1 hh
    have h1 : ⁅(k : G), (c : G)⁆ ∈ pPrimeCoreOf 2 M := hc.2.2.2 k (Subgroup.mem_sup_left hk)
    have h2 : barMk ↥M ⁅k, c⁆ = 1 := (barMk_eq_one_iff_mem_pPrimeCoreOf _).2 (by
      have : ((⁅k, c⁆ : ↥M) : G) = ⁅(k : G), (c : G)⁆ := by simp [commutatorElement_def]
      rw [this]
      exact h1)
    rw [map_commutatorElement] at h2
    exact commutatorElement_eq_one_iff_mul_comm.1 h2
  · intro hw
    obtain ⟨c, rfl⟩ := barMk_surjective (Y := ↥M) w
    refine mem_imgM_iff.2 ⟨c, ?_, rfl⟩
    refine Th2.HY.mem_CMbar_of_comm hKM c.2 fun k hk => ?_
    have hcomm : barMk ↥M ⟨k, hKM hk⟩ * barMk ↥M c = barMk ↥M c * barMk ↥M ⟨k, hKM hk⟩ :=
      (Subgroup.mem_centralizer_iff.1 hw) _ (mem_imgM_iff.2 ⟨⟨k, hKM hk⟩, hk, rfl⟩)
    have h2 : barMk ↥M ⁅(⟨k, hKM hk⟩ : ↥M), c⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2 hcomm
    have h3 := (barMk_eq_one_iff_mem_pPrimeCoreOf _).1 h2
    simpa [commutatorElement_def] using h3

theorem isSylowOf_imgM_cmbar {K M Q : Subgroup G} (hKM : K ≤ M)
    (hQ : IsSylowOf 2 Q (CMbar M K)) :
    IsSylowOf 2 (imgM M Q) (centralizer (imgM M K : Set (Mb M))) := by
  rw [← imgM_cmbar_eq hKM]
  exact isSylowOf_imgM_of_le (A := CMbar M K) inf_le_left hQ

theorem isKGroupNative_Mb_of_kProper (hK : Assembly.KProper Blueprint.Catalog G)
    {M : Subgroup G} (hM : M ≠ ⊤) : IsKGroupNative (Mb M) :=
  isKGroupNative_of_surjective (X := ↥M) (isKGroupNative_of_kProper hK hM) ⊤
    ((barMk ↥M).comp (⊤ : Subgroup ↥M).subtype)
    (barMk_surjective.comp fun m => ⟨⟨m, trivial⟩, rfl⟩)

theorem isKGroupNative_Mb (hG : IsKProperSimple G) {M : Subgroup G} (hM : M ≠ ⊤) :
    IsKGroupNative (Mb M) :=
  isKGroupNative_Mb_of_kProper hG.2.2 hM

end CFSG.GH74.GLS.Th2.P85
