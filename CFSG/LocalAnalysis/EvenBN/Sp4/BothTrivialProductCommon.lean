module

public import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialProductUnique
public import CFSG.LocalAnalysis.EvenBN.Sp4.ProductModel
import CFSG.LocalAnalysis.EvenBN.Common.CoprimeQuotient
import CFSG.LocalAnalysis.EvenBN.U4.CaseTwoNine
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions

public section

namespace CFSG.LocalAnalysis.EvenBN.Sp4

namespace BothTrivialProduct

open Subgroup CFSG.Blueprint CFSG.Open
open CFSG.LocalAnalysis.SymplecticFourStandard
open GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
  FullCenterTorus FullCenterWeyl FullCenterMutual BothTrivial BothTrivialHeisenberg
  BothTrivialClosure BothTrivialLayer BothTrivialRankOne BothTrivialSlice BothTrivialField
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open CFSG.LocalAnalysis.EvenBN.Common (prodFst prodFstHom)
open scoped MatrixGroups

section CommonSylowAbstract

open scoped commutatorElement

namespace CommonSylow

section Step1

variable {G : Type*} [Group G] {H : Type*} [Group H] {N X P : Subgroup G} {t : G}
  {ρ : N →* H × H}

@[expose] def kerSub (d : ProductDiagData N X P t ρ) : Subgroup G := d.delta.ker.map P.subtype

theorem mem_kerSub_iff (d : ProductDiagData N X P t ρ) {x : G} :
    x ∈ kerSub d ↔ x ∈ P ∧ x * (t * x * t⁻¹) = 1 := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, d.delta_apply] at ha
    exact ⟨a.2, ha⟩
  · rintro ⟨hx, h1⟩
    exact ⟨⟨x, hx⟩, by rw [SetLike.mem_coe, MonoidHom.mem_ker, d.delta_apply]; exact h1, rfl⟩

theorem comm_P_Pt (d : ProductDiagData N X P t ρ) {a b : G} (ha : a ∈ P)
    (hb : b ∈ P.map (MulAut.conj t).toMonoidHom) : a * b = b * a :=
  (mem_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 d.comm_conj ha) b hb).symm

theorem kerSub_le_inf (d : ProductDiagData N X P t ρ) :
    kerSub d ≤ P ⊓ P.map (MulAut.conj t).toMonoidHom := by
  intro x hx
  obtain ⟨hxP, h1⟩ := (mem_kerSub_iff d).1 hx
  refine mem_inf.2 ⟨hxP, ?_⟩
  rw [diag_mem_map_conj_iff d.t_sq]
  have : t * x * t⁻¹ = x⁻¹ := eq_inv_of_mul_eq_one_right h1
  rw [this]
  exact inv_mem hxP

variable [Finite G]

theorem card_inf_le (d : ProductDiagData N X P t ρ) :
    Nat.card (P ⊓ P.map (MulAut.conj t).toMonoidHom : Subgroup G) ≤ Nat.card (kerSub d) ^ 2 := by
  set Y : Subgroup G := P ⊓ P.map (MulAut.conj t).toMonoidHom with hY
  have hYP : Y ≤ P := inf_le_left
  let f : Y →* G := d.delta.comp (Subgroup.inclusion hYP)
  have hfx : ∀ y : Y, f y = (y : G) * (t * y * t⁻¹) := fun y => rfl
  have hcard := Subgroup.card_ker_mul_card_range f
  have hker : Nat.card f.ker ≤ Nat.card (kerSub d) := by
    rw [← Subgroup.card_map_of_injective (f := Y.subtype) Y.subtype_injective (K := f.ker)]
    refine Subgroup.card_le_of_le ?_
    rintro _ ⟨y, hy, rfl⟩
    refine (mem_kerSub_iff d).2 ⟨hYP y.2, ?_⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, hfx] at hy
    exact hy
  have hrange : Nat.card f.range ≤ Nat.card (kerSub d) := by
    refine Subgroup.card_le_of_le ?_
    rintro _ ⟨y, rfl⟩
    rw [hfx]
    obtain ⟨hyP, hyt⟩ := mem_inf.1 y.2
    obtain ⟨b, hb⟩ : ∃ b, b = t * (y : G) * t⁻¹ := ⟨_, rfl⟩
    rw [← hb]
    have hbP : b ∈ P := by
      rw [hb]
      exact (diag_mem_map_conj_iff d.t_sq).1 hyt
    have hyX : (y : G) ∈ X := d.mem_X_of_mem_inf hyP hyt
    have hbX : b ∈ X := by
      rw [hb]
      exact d.conj_t_mem_X hyX
    refine (mem_kerSub_iff d).2 ⟨mul_mem hyP hbP, ?_⟩
    have htb : t * b * t⁻¹ = (y : G) := by
      rw [hb]
      exact diag_conj_conj d.t_sq _
    have htz : t * ((y : G) * b) * t⁻¹ = b * (y : G) := by
      have e : t * ((y : G) * b) * t⁻¹ = (t * (y : G) * t⁻¹) * (t * b * t⁻¹) := by group
      rw [e, htb, ← hb]
    rw [htz]
    calc (y : G) * b * (b * (y : G)) = (y : G) * (b * b) * (y : G) := by group
      _ = 1 := by rw [d.X_sq b hbX, mul_one, d.X_sq _ hyX]
  calc Nat.card Y = Nat.card f.ker * Nat.card f.range := hcard.symm
    _ ≤ Nat.card (kerSub d) * Nat.card (kerSub d) := Nat.mul_le_mul hker hrange
    _ = Nat.card (kerSub d) ^ 2 := (sq _).symm

theorem R_facts (d : ProductDiagData N X P t ρ) {S Pm CU U : Subgroup G}
    (hS2 : IsPGroup 2 S) (hPmS : Pm ≤ S)
    (htS : ∀ s ∈ S, t * s * t⁻¹ ∈ S) (hSC : ∀ x ∈ S, t * x = x * t → x ∈ Pm)
    (hPmCU : Pm ≤ CU) (hUPm : U ≤ Pm)
    (hCU₁ : ∀ x ∈ P, x * (t * x * t⁻¹) ∈ CU) (hCU₂ : ∀ y ∈ CU, ∃ x ∈ P, x * (t * x * t⁻¹) = y)
    (hU : ∀ x ∈ P, x * (t * x * t⁻¹) = 1 → x ∈ U) (hodd : ¬ 2 ∣ S.relIndex P) :
    kerSub d ≤ S ⊓ P ∧ (∀ x ∈ S ⊓ P, x * (t * x * t⁻¹) ∈ Pm) ∧
      (∀ y ∈ Pm, ∃ x ∈ S ⊓ P, x * (t * x * t⁻¹) = y) ∧
      Nat.card (S ⊓ P : Subgroup G) = Nat.card Pm * Nat.card (kerSub d) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : kerSub d ≤ S ⊓ P := fun x hx => by
    obtain ⟨hxP, h1⟩ := (mem_kerSub_iff d).1 hx
    exact mem_inf.2 ⟨hPmS (hUPm (hU x hxP h1)), hxP⟩
  have himg : ∀ x ∈ S ⊓ P, x * (t * x * t⁻¹) ∈ Pm := by
    intro x hx
    obtain ⟨hxS, hxP⟩ := mem_inf.1 hx
    exact hSC _ (mul_mem hxS (htS x hxS)) (d.delta_comm hxP)
  set R' : Subgroup P := (S ⊓ P).subgroupOf P with hR'
  set δ := d.delta with hδ
  have hDm : R'.map δ ≤ Pm := by
    rintro _ ⟨a, ha, rfl⟩
    exact himg a (mem_subgroupOf.1 ha)
  have hkerR : δ.ker ≤ R' := by
    intro x hx
    rw [MonoidHom.mem_ker, hδ, d.delta_apply] at hx
    exact mem_subgroupOf.2 (hK ((mem_kerSub_iff d).2 ⟨x.2, hx⟩))
  have h1 := Common.card_map_mul_card_inf_ker δ R'
  rw [inf_of_le_right hkerR] at h1
  have h2 := Subgroup.card_ker_mul_card_range δ
  have hrange : δ.range = CU := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact hCU₁ x x.2
    · intro hy
      obtain ⟨x, hx, rfl⟩ := hCU₂ y hy
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [hrange] at h2
  have h3 := Subgroup.relIndex_mul_card (H := S) (K := P)
  have hRcard : Nat.card R' = Nat.card (S ⊓ P : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : S ⊓ P ≤ P)).toEquiv
  have hkcard : Nat.card (kerSub d) = Nat.card δ.ker :=
    Subgroup.card_map_of_injective P.subtype_injective
  have hker_pos : 0 < Nat.card δ.ker := Nat.card_pos
  have hCUidx : Nat.card CU = S.relIndex P * Nat.card (R'.map δ) := by
    refine Nat.eq_of_mul_eq_mul_left hker_pos ?_
    calc Nat.card δ.ker * Nat.card CU = Nat.card P := h2
      _ = S.relIndex P * Nat.card (S ⊓ P : Subgroup G) := h3.symm
      _ = S.relIndex P * Nat.card R' := by rw [hRcard]
      _ = S.relIndex P * (Nat.card (R'.map δ) * Nat.card δ.ker) := by rw [h1]
      _ = Nat.card δ.ker * (S.relIndex P * Nat.card (R'.map δ)) := by ring
  have hPm2 : IsPGroup 2 Pm := hS2.to_le hPmS
  obtain ⟨k, hk⟩ := hPm2.exists_card_eq
  have hcop : Nat.Coprime (Nat.card Pm) (S.relIndex P) := by
    rw [hk]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd)
  have hdvd1 : Nat.card Pm ∣ Nat.card CU := Subgroup.card_dvd_of_le hPmCU
  rw [hCUidx] at hdvd1
  have hdvd2 : Nat.card Pm ∣ Nat.card (R'.map δ) := hcop.dvd_of_dvd_mul_left hdvd1
  have hle : Nat.card Pm ≤ Nat.card (R'.map δ) := Nat.le_of_dvd Nat.card_pos hdvd2
  have hDmeq : R'.map δ = Pm := Subgroup.eq_of_le_of_card_ge hDm hle
  refine ⟨hK, himg, fun y hy => ?_, ?_⟩
  · rw [← hDmeq] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    exact ⟨a, mem_subgroupOf.1 ha, rfl⟩
  · rw [hkcard, ← hDmeq, ← hRcard, ← h1, mul_comm]

theorem sup_conj_eq (d : ProductDiagData N X P t ρ) {S Pm : Subgroup G}
    (htS : ∀ s ∈ S, t * s * t⁻¹ ∈ S) (hcardS : Nat.card S = Nat.card Pm ^ 2)
    (hRcard : Nat.card (S ⊓ P : Subgroup G) = Nat.card Pm * Nat.card (kerSub d)) :
    (S ⊓ P) ⊔ (S ⊓ P).map (MulAut.conj t).toMonoidHom = S := by
  set R : Subgroup G := S ⊓ P with hR
  set Rt : Subgroup G := R.map (MulAut.conj t).toMonoidHom with hRt
  have hmemRt : ∀ y, y ∈ Rt ↔ t * y * t⁻¹ ∈ R := fun y => diag_mem_map_conj_iff d.t_sq
  have hRtS : Rt ≤ S := fun y hy => by
    have := htS _ (mem_inf.1 ((hmemRt y).1 hy)).1
    rwa [diag_conj_conj d.t_sq] at this
  have hRS : R ≤ S := inf_le_left
  have hcomm : ∀ a ∈ R, ∀ b ∈ Rt, a * b = b * a := fun a ha b hb =>
    comm_P_Pt d (mem_inf.1 ha).2 (Subgroup.map_mono (inf_le_right : R ≤ P) hb)
  have hnorm : Rt ≤ normalizer (R : Set G) := fun b hb =>
    Subgroup.centralizer_le_normalizer (R : Set G)
      (mem_centralizer_iff.2 fun a ha => hcomm a ha b hb)
  have h1 := Common.card_sup_mul_card_inf_eq hnorm
  have hRtcard : Nat.card Rt = Nat.card R :=
    Subgroup.card_map_of_injective (MulAut.conj t).injective
  have hinf : Nat.card (R ⊓ Rt : Subgroup G) ≤ Nat.card (kerSub d) ^ 2 := by
    refine le_trans (Subgroup.card_le_of_le ?_) (card_inf_le d)
    exact inf_le_inf inf_le_right (Subgroup.map_mono inf_le_right)
  have hge : Nat.card S ≤ Nat.card (R ⊔ Rt : Subgroup G) := by
    have h2 : Nat.card Pm ^ 2 * Nat.card (kerSub d) ^ 2 ≤
        Nat.card (R ⊔ Rt : Subgroup G) * Nat.card (kerSub d) ^ 2 := by
      calc Nat.card Pm ^ 2 * Nat.card (kerSub d) ^ 2 = Nat.card R * Nat.card Rt := by
            rw [hRtcard, hRcard]; ring
        _ = Nat.card (R ⊔ Rt : Subgroup G) * Nat.card (R ⊓ Rt : Subgroup G) := h1.symm
        _ ≤ Nat.card (R ⊔ Rt : Subgroup G) * Nat.card (kerSub d) ^ 2 :=
            Nat.mul_le_mul_left _ hinf
    rw [hcardS]
    exact Nat.le_of_mul_le_mul_right h2 (by have := Nat.card_pos (α := kerSub d); positivity)
  exact Subgroup.eq_of_le_of_card_ge (sup_le hRS hRtS) hge

theorem card_le_inf_mul (d : ProductDiagData N X P t ρ) {q : ℕ}
    (hH : ∀ B : Subgroup H, IsPGroup 2 B → Nat.card B ≤ q) {R : Subgroup G} (hRP : R ≤ P)
    (hR2 : IsPGroup 2 R) : Nat.card R ≤ Nat.card (R ⊓ X : Subgroup G) * q := by
  have hRΛ : R ≤ Common.prodFst ρ := hRP.trans d.le_prodFst
  let θ : R →* H := (Common.prodFstHom ρ).comp (Subgroup.inclusion hRΛ)
  have hcard := Subgroup.card_ker_mul_card_range θ
  have hker : Nat.card θ.ker ≤ Nat.card (R ⊓ X : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective (f := R.subtype) R.subtype_injective (K := θ.ker)]
    refine Subgroup.card_le_of_le ?_
    rintro _ ⟨x, hx, rfl⟩
    refine mem_inf.2 ⟨x.2, ?_⟩
    have hx' : Subgroup.inclusion hRΛ x ∈ (Common.prodFstHom ρ).ker := hx
    rw [Common.ker_prodFstHom d.ker, mem_subgroupOf] at hx'
    exact hx'
  have hrange : Nat.card θ.range ≤ q :=
    hH _ (hR2.of_surjective θ.rangeRestrict θ.rangeRestrict_surjective)
  calc Nat.card R = Nat.card θ.ker * Nat.card θ.range := hcard.symm
    _ ≤ Nat.card (R ⊓ X : Subgroup G) * q := Nat.mul_le_mul hker hrange

theorem X_le_sup (d : ProductDiagData N X P t ρ) {q : ℕ} (hXcard : Nat.card X = q ^ 6)
    (hPX : q ^ 3 * Nat.card (kerSub d) ≤ Nat.card (P ⊓ X : Subgroup G)) :
    X ≤ (P ⊓ X) ⊔ (P.map (MulAut.conj t).toMonoidHom ⊓ X) := by
  set A : Subgroup G := P ⊓ X with hA
  set B : Subgroup G := P.map (MulAut.conj t).toMonoidHom ⊓ X with hB
  have hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    d.X_comm a (mem_inf.1 ha).2 b (mem_inf.1 hb).2
  have hnorm : B ≤ normalizer (A : Set G) := fun b hb =>
    Subgroup.centralizer_le_normalizer (A : Set G)
      (mem_centralizer_iff.2 fun a ha => hcomm a ha b hb)
  have h1 := Common.card_sup_mul_card_inf_eq hnorm
  have hXt : ∀ y, t * y * t⁻¹ ∈ X ↔ y ∈ X := fun y =>
    ⟨fun h => by simpa [diag_conj_conj d.t_sq] using d.conj_t_mem_X h, fun h => d.conj_t_mem_X h⟩
  have hBA : B = A.map (MulAut.conj t).toMonoidHom := by
    ext y
    rw [diag_mem_map_conj_iff d.t_sq, hA, hB, mem_inf, mem_inf, diag_mem_map_conj_iff d.t_sq,
      hXt]
  have hBcard : Nat.card B = Nat.card A := by
    rw [hBA]
    exact Subgroup.card_map_of_injective (MulAut.conj t).injective
  have hinf : Nat.card (A ⊓ B : Subgroup G) ≤ Nat.card (kerSub d) ^ 2 := by
    refine le_trans (Subgroup.card_le_of_le ?_) (card_inf_le d)
    exact inf_le_inf inf_le_left (inf_le_left)
  have hkpos : 0 < Nat.card (kerSub d) := Nat.card_pos
  have hge : Nat.card X ≤ Nat.card (A ⊔ B : Subgroup G) := by
    have h2 : q ^ 6 * Nat.card (kerSub d) ^ 2 ≤
        Nat.card (A ⊔ B : Subgroup G) * Nat.card (kerSub d) ^ 2 := by
      calc q ^ 6 * Nat.card (kerSub d) ^ 2 = (q ^ 3 * Nat.card (kerSub d)) ^ 2 := by ring
        _ ≤ Nat.card A ^ 2 := Nat.pow_le_pow_left hPX 2
        _ = Nat.card A * Nat.card B := by rw [hBcard]; ring
        _ = Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) := h1.symm
        _ ≤ Nat.card (A ⊔ B : Subgroup G) * Nat.card (kerSub d) ^ 2 :=
            Nat.mul_le_mul_left _ hinf
    rw [hXcard]
    exact Nat.le_of_mul_le_mul_right h2 (by positivity)
  exact (Subgroup.eq_of_le_of_card_ge (sup_le inf_le_right inf_le_right) hge).ge

theorem sup_conj_eq_N_of_X_le (d : ProductDiagData N X P t ρ)
    (hXsup : X ≤ P ⊔ P.map (MulAut.conj t).toMonoidHom) :
    P ⊔ P.map (MulAut.conj t).toMonoidHom = N := by
  have hΛt := Common.prodFst_sup_map_conj d.t_mem d.t_sq d.swap d.surj
  refine le_antisymm (sup_le d.P_le fun y hy => ?_) ?_
  · have h1 := d.conj_t_mem_N (d.P_le ((diag_mem_map_conj_iff d.t_sq).1 hy))
    rwa [diag_conj_conj d.t_sq] at h1
  · rw [← hΛt, ← d.sup_X, Subgroup.map_sup, Common.map_conj_eq_of_mem_normalizer d.t_mem_X]
    exact sup_le (sup_le le_sup_left hXsup) (sup_le le_sup_right hXsup)

theorem not_two_dvd_relIndex_P (d : ProductDiagData N X P t ρ) [Finite G] {S : Subgroup G}
    (hSN : S ≤ N) (hodd : ¬ 2 ∣ S.relIndex N) : ¬ 2 ∣ S.relIndex P := by
  have hSnorm : S ≤ normalizer (P : Set G) := fun s hs =>
    Subgroup.mem_normalizer_fintype fun p hp => d.conj_mem_P (hSN hs) hp
  have h1 := Common.card_sup_mul_card_inf_eq hSnorm
  have h2 : Nat.card (P ⊔ S : Subgroup G) ∣ Nat.card N :=
    Subgroup.card_dvd_of_le (sup_le d.P_le hSN)
  have h3 := Subgroup.relIndex_mul_card (H := S) (K := P)
  have h4 := Subgroup.relIndex_mul_card (H := S) (K := N)
  rw [inf_of_le_left hSN] at h4
  rw [inf_comm] at h1
  have hc : 0 < Nat.card (S ⊓ P : Subgroup G) := Nat.card_pos
  have h5 : Nat.card (P ⊔ S : Subgroup G) = S.relIndex P * Nat.card S := by
    refine Nat.eq_of_mul_eq_mul_right hc ?_
    calc Nat.card (P ⊔ S : Subgroup G) * Nat.card (S ⊓ P : Subgroup G)
        = Nat.card P * Nat.card S := h1
      _ = (S.relIndex P * Nat.card (S ⊓ P : Subgroup G)) * Nat.card S := by rw [h3]
      _ = S.relIndex P * Nat.card S * Nat.card (S ⊓ P : Subgroup G) := by ring
  rw [h5, ← h4] at h2
  have h6 : S.relIndex P ∣ S.relIndex N := Nat.dvd_of_mul_dvd_mul_right Nat.card_pos h2
  exact fun h => hodd (dvd_trans h h6)

end Step1

section Lift

variable {G : Type*} [Group G] {H : Type*} [Group H] {N X P : Subgroup G} {t : G}
  {ρ : N →* H × H}

theorem delta_conj (d : ProductDiagData N X P t ρ) {y r : G} (hy : y ∈ P) (hr : r ∈ P) :
    (y * r * y⁻¹) * (t * (y * r * y⁻¹) * t⁻¹) =
      (y * (t * y * t⁻¹)) * (r * (t * r * t⁻¹)) * (y * (t * y * t⁻¹))⁻¹ := by
  have hδ : d.delta (⟨y, hy⟩ * ⟨r, hr⟩ * ⟨y, hy⟩⁻¹) =
      d.delta ⟨y, hy⟩ * d.delta ⟨r, hr⟩ * (d.delta ⟨y, hy⟩)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
  simpa only [d.delta_apply, Subgroup.coe_mul, Subgroup.coe_inv] using hδ

theorem delta_commutator (d : ProductDiagData N X P t ρ) {a b : G} (ha : a ∈ P) (hb : b ∈ P) :
    ⁅a, b⁆ * (t * ⁅a, b⁆ * t⁻¹) = ⁅a * (t * a * t⁻¹), b * (t * b * t⁻¹)⁆ := by
  have hδ : d.delta ⁅(⟨a, ha⟩ : P), ⟨b, hb⟩⁆ = ⁅d.delta ⟨a, ha⟩, d.delta ⟨b, hb⟩⁆ :=
    map_commutatorElement _ _ _
  simpa only [d.delta_apply, commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] using hδ

theorem inv_mul_mem_kerSub (d : ProductDiagData N X P t ρ) {a b : G} (ha : a ∈ P) (hb : b ∈ P)
    (h : a * (t * a * t⁻¹) = b * (t * b * t⁻¹)) : a⁻¹ * b ∈ kerSub d := by
  refine (mem_kerSub_iff d).2 ⟨mul_mem (inv_mem ha) hb, ?_⟩
  have h1 : d.delta (⟨a, ha⟩⁻¹ * ⟨b, hb⟩) = (d.delta ⟨a, ha⟩)⁻¹ * d.delta ⟨b, hb⟩ := by
    rw [map_mul, map_inv]
  have h2 : d.delta (⟨a, ha⟩⁻¹ * ⟨b, hb⟩) = 1 := by
    rw [h1, d.delta_apply, d.delta_apply]
    simp only
    rw [h]
    exact inv_mul_cancel _
  rw [d.delta_apply] at h2
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h2

@[expose] def dm (d : ProductDiagData N X P t ρ) (A : Subgroup G) : Subgroup G :=
  (A.subgroupOf P).map d.delta

theorem mem_dm_iff (d : ProductDiagData N X P t ρ) {A : Subgroup G} (hAP : A ≤ P) {y : G} :
    y ∈ dm d A ↔ ∃ a ∈ A, a * (t * a * t⁻¹) = y := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, mem_subgroupOf.1 ha, by rw [d.delta_apply]⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, hAP ha⟩, mem_subgroupOf.2 ha, by rw [d.delta_apply]⟩

theorem dm_sup (d : ProductDiagData N X P t ρ) {A B : Subgroup G} (hA : A ≤ P) (hB : B ≤ P) :
    dm d (A ⊔ B) = dm d A ⊔ dm d B := by
  unfold dm
  rw [Subgroup.subgroupOf_sup hA hB, Subgroup.map_sup]

variable [Finite G]

theorem exists_odd_lift (d : ProductDiagData N X P t ρ) {R Pm J : Subgroup G}
    (hKR : kerSub d ≤ R)
    (hJ : ∀ j ∈ J, ∃ x ∈ P, x * (t * x * t⁻¹) = j)
    (hδR : ∀ x ∈ R, x * (t * x * t⁻¹) ∈ Pm) (hδR' : ∀ y ∈ Pm, ∃ x ∈ R, x * (t * x * t⁻¹) = y)
    (hJPm : ∀ j ∈ J, ∀ y ∈ Pm, j * y * j⁻¹ ∈ Pm) (hRP : R ≤ P)
    (hK2 : IsPGroup 2 (kerSub d)) (hJodd : Odd (Nat.card J)) :
    ∃ Jh : Subgroup G, Jh ≤ P ∧ Odd (Nat.card Jh) ∧ (∀ y ∈ Jh, y * (t * y * t⁻¹) ∈ J) ∧
      (∀ j ∈ J, ∃ y ∈ Jh, y * (t * y * t⁻¹) = j) ∧ (∀ y ∈ Jh, ∀ r ∈ R, y * r * y⁻¹ ∈ R) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Hs : Subgroup P := J.comap d.delta with hHs
  let f : Hs →* G := d.delta.comp Hs.subtype
  have hfx : ∀ y : Hs, f y = ((y : P) : G) * (t * ((y : P) : G) * t⁻¹) := fun y => by
    show d.delta (y : P) = _
    rw [d.delta_apply]
  have hfrange : f.range = J := by
    ext j
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hj
      obtain ⟨x, hx, hxj⟩ := hJ j hj
      refine ⟨⟨⟨x, hx⟩, ?_⟩, ?_⟩
      · show d.delta ⟨x, hx⟩ ∈ J
        rw [d.delta_apply]
        exact hxj ▸ hj
      · rw [hfx]
        exact hxj
  set g : Hs →* G := P.subtype.comp Hs.subtype with hg
  have hginj : Function.Injective g := P.subtype_injective.comp Hs.subtype_injective
  have hfker : Nat.card f.ker = Nat.card (kerSub d) := by
    have h1 : f.ker.map g = kerSub d := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine (mem_kerSub_iff d).2 ⟨(y : P).2, ?_⟩
        have := hy
        rw [SetLike.mem_coe, MonoidHom.mem_ker, hfx] at this
        exact this
      · intro hx
        obtain ⟨hxP, h1⟩ := (mem_kerSub_iff d).1 hx
        refine ⟨⟨⟨x, hxP⟩, ?_⟩, ?_, rfl⟩
        · show d.delta ⟨x, hxP⟩ ∈ J
          rw [d.delta_apply]
          exact h1 ▸ one_mem J
        · rw [SetLike.mem_coe, MonoidHom.mem_ker, hfx]
          exact h1
    rw [← h1, Subgroup.card_map_of_injective hginj]
  have hcard := Subgroup.card_ker_mul_card_range f
  have hcop : Nat.Coprime (Nat.card f.ker) f.ker.index := by
    obtain ⟨k, hk⟩ := hK2.exists_card_eq
    rw [hfker, hk, Subgroup.index_ker, hfrange]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hJodd)
  obtain ⟨C, hC⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hCcard : Nat.card C = Nat.card J := by
    have h1 := hC.card_mul_card
    rw [← hfrange]
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans hcard.symm)
  have hmapC : C.map f = f.range := by
    have h1 := hC.sup_eq_top
    rw [MonoidHom.range_eq_map, ← h1, Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).2 le_rfl,
      bot_sup_eq]
  refine ⟨C.map g, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨c, hc, rfl⟩
    exact (c : P).2
  · rw [Subgroup.card_map_of_injective hginj, hCcard]
    exact hJodd
  · rintro _ ⟨c, hc, rfl⟩
    have h1 : d.delta (c : P) ∈ J := c.2
    rw [d.delta_apply] at h1
    exact h1
  · intro j hj
    rw [← hfrange, ← hmapC] at hj
    obtain ⟨c, hc, rfl⟩ := hj
    exact ⟨g c, ⟨c, hc, rfl⟩, (hfx c).symm⟩
  · rintro _ ⟨c, hc, rfl⟩ r hr
    have hyP : ((c : P) : G) ∈ P := (c : P).2
    have hyJ : ((c : P) : G) * (t * ((c : P) : G) * t⁻¹) ∈ J := by
      have h1 : d.delta (c : P) ∈ J := c.2
      rw [d.delta_apply] at h1
      exact h1
    have hz : ((c : P) : G) * r * ((c : P) : G)⁻¹ ∈ P := mul_mem (mul_mem hyP (hRP hr)) (inv_mem hyP)
    have hδz := delta_conj d hyP (hRP hr)
    have hδzmem : (((c : P) : G) * r * ((c : P) : G)⁻¹) *
        (t * (((c : P) : G) * r * ((c : P) : G)⁻¹) * t⁻¹) ∈ Pm := by
      rw [hδz]
      exact hJPm _ hyJ _ (hδR r hr)
    obtain ⟨r', hr', hr'z⟩ := hδR' _ hδzmem
    have hk : r'⁻¹ * (((c : P) : G) * r * ((c : P) : G)⁻¹) ∈ kerSub d :=
      inv_mul_mem_kerSub d (hRP hr') hz hr'z
    have := mul_mem hr' (hKR hk)
    rwa [mul_inv_cancel_left] at this

end Lift

section Dichotomy

variable {G : Type*} [Group G]

theorem exists_mul_of_odd_action [Finite G] {Pm J : Subgroup G} (hPm : IsPGroup 2 Pm)
    (hJ : ∀ j ∈ J, ∀ y ∈ Pm, j * y * j⁻¹ ∈ Pm) (hodd : Odd (Nat.card J)) {m : G} (hm : m ∈ Pm) :
    ∃ c ∈ Pm ⊓ centralizer (J : Set G), ∃ n ∈ ⁅Pm, J⁆, m = c * n := by
  have hNM : ⁅Pm, J⁆ ≤ Pm := by
    rw [commutator_le]
    intro a ha j hj
    rw [commutatorElement_def]
    have h1 := hJ j hj a⁻¹ (inv_mem ha)
    have e : a * j * a⁻¹ * j⁻¹ = a * (j * a⁻¹ * j⁻¹) := by group
    rw [e]
    exact mul_mem ha h1
  have hJn : J ≤ normalizer (Pm : Set G) := fun j hj =>
    Subgroup.mem_normalizer_fintype fun y hy => hJ j hj y hy
  have hnil : Group.IsNilpotent Pm := hPm.isNilpotent
  have hcop : (Nat.card J).Coprime (Nat.card Pm) := by
    obtain ⟨k, hk⟩ := hPm.exists_card_eq
    rw [hk]
    exact (Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hodd))
  refine Common.exists_mem_inf_centralizer_mul_of_coprime hNM
    (Subgroup.normalizer_commutator_ge_left Pm J) hJn
    (Subgroup.normalizer_commutator_ge_right Pm J) inferInstance hcop hm fun s hs => ?_
  have h1 : ⁅m⁻¹, s⁆ ∈ ⁅Pm, J⁆ := commutator_mem_commutator (inv_mem hm) hs
  have e : ⁅m⁻¹, s⁆ = m⁻¹ * (s * m * s⁻¹) := by
    simp only [commutatorElement_def]
    group
  rwa [e] at h1

theorem commutator_le_of_sup {S R Rt Jh : Subgroup G} (hS : S ≤ R ⊔ Rt)
    (hRRt : ∀ a ∈ R, ∀ b ∈ Rt, a * b = b * a) (hJRt : ∀ y ∈ Jh, ∀ b ∈ Rt, y * b = b * y)
    (hJR : ∀ y ∈ Jh, ∀ r ∈ R, y * r * y⁻¹ ∈ R) : ⁅S, Jh⁆ ≤ R := by
  rw [commutator_le]
  intro s hs j hj
  obtain ⟨a, ha, b, hb, rfl⟩ := diag_exists_mul_of_mem_sup hRRt (hS hs)
  have hbjb : b * j * b⁻¹ = j := by
    calc b * j * b⁻¹ = j * b * b⁻¹ := by rw [hJRt j hj b hb]
      _ = j := by group
  have e : ⁅a * b, j⁆ = a * (j * a⁻¹ * j⁻¹) := by
    simp only [commutatorElement_def]
    calc a * b * j * (a * b)⁻¹ * j⁻¹ = a * (b * j * b⁻¹) * a⁻¹ * j⁻¹ := by group
      _ = a * j * a⁻¹ * j⁻¹ := by rw [hbjb]
      _ = a * (j * a⁻¹ * j⁻¹) := by group
  rw [e]
  exact mul_mem ha (hJR j hj a⁻¹ (inv_mem ha))

theorem commutator_le_sup_of_sup {S R' R't Jh : Subgroup G} (hS : S ≤ R' ⊔ R't)
    (hc : ∀ a ∈ R', ∀ b ∈ R't, a * b = b * a)
    (hJR't : ∀ y ∈ Jh, ∀ r ∈ R't, y * r * y⁻¹ ∈ R't) :
    ⁅S, Jh⁆ ≤ ⁅R', Jh⁆ ⊔ ⁅R't, Jh⁆ := by
  rw [commutator_le]
  intro s hs j hj
  obtain ⟨a, ha, b, hb, rfl⟩ := diag_exists_mul_of_mem_sup hc (hS hs)
  have e : ⁅a * b, j⁆ = a * ⁅b, j⁆ * a⁻¹ * ⁅a, j⁆ := by
    simp only [commutatorElement_def]
    group
  have hu : ⁅b, j⁆ ∈ R't := by
    rw [commutatorElement_def]
    have e2 : b * j * b⁻¹ * j⁻¹ = b * (j * b⁻¹ * j⁻¹) := by group
    rw [e2]
    exact mul_mem hb (hJR't j hj b⁻¹ (inv_mem hb))
  have hau : a * ⁅b, j⁆ * a⁻¹ = ⁅b, j⁆ := by
    rw [hc a ha _ hu]
    group
  rw [e, hau]
  exact mul_mem (mem_sup_right (commutator_mem_commutator hb hj))
    (mem_sup_left (commutator_mem_commutator ha hj))

theorem commutator_le_self {R' Jh : Subgroup G} (hJR' : ∀ y ∈ Jh, ∀ r ∈ R', y * r * y⁻¹ ∈ R') :
    ⁅R', Jh⁆ ≤ R' := by
  rw [commutator_le]
  intro a ha j hj
  rw [commutatorElement_def]
  have e : a * j * a⁻¹ * j⁻¹ = a * (j * a⁻¹ * j⁻¹) := by group
  rw [e]
  exact mul_mem ha (hJR' j hj a⁻¹ (inv_mem ha))

theorem normalized_by_S {S R' R't Jh : Subgroup G} (hS : S ≤ R' ⊔ R't)
    (hc : ∀ a ∈ R', ∀ b ∈ R't, a * b = b * a)
    (hJR' : ∀ y ∈ Jh, ∀ r ∈ R', y * r * y⁻¹ ∈ R')
    (hJR't : ∀ y ∈ Jh, ∀ r ∈ R't, y * r * y⁻¹ ∈ R't) :
    (∀ s ∈ S, ∀ a ∈ ⁅R', Jh⁆, s * a * s⁻¹ ∈ ⁅R', Jh⁆) ∧
      (∀ s ∈ S, ∀ a ∈ ⁅R't, Jh⁆, s * a * s⁻¹ ∈ ⁅R't, Jh⁆) := by
  constructor
  · intro s hs a ha
    obtain ⟨a', ha', b, hb, rfl⟩ := diag_exists_mul_of_mem_sup hc (hS hs)
    have hba : b * a * b⁻¹ = a := by
      have := hc a (commutator_le_self hJR' ha) b hb
      calc b * a * b⁻¹ = a * b * b⁻¹ := by rw [this]
        _ = a := by group
    have e : a' * b * a * (a' * b)⁻¹ = a' * (b * a * b⁻¹) * a'⁻¹ := by group
    rw [e, hba]
    exact (mem_normalizer_iff.1 (Subgroup.normalizer_commutator_ge_left R' Jh ha') a).1 ha
  · intro s hs a ha
    obtain ⟨a', ha', b, hb, rfl⟩ := diag_exists_mul_of_mem_sup hc (hS hs)
    have e : a' * b * a * (a' * b)⁻¹ = a' * (b * a * b⁻¹) * a'⁻¹ := by group
    have hbab : b * a * b⁻¹ ∈ ⁅R't, Jh⁆ :=
      (mem_normalizer_iff.1 (Subgroup.normalizer_commutator_ge_left R't Jh hb) a).1 ha
    have hR : b * a * b⁻¹ ∈ R't := commutator_le_self hJR't hbab
    have h1 : a' * (b * a * b⁻¹) * a'⁻¹ = b * a * b⁻¹ := by
      rw [hc a' ha' _ hR]
      group
    rw [e, h1]
    exact hbab

end Dichotomy

section Main

variable {G : Type*} [Group G] [Finite G] {H : Type*} [Group H] {N X P : Subgroup G} {t : G}
  {ρ : N →* H × H}

theorem dichotomy (d : ProductDiagData N X P t ρ) {S Pm Zm R' R't J Jh : Subgroup G}
    (hPm2 : IsPGroup 2 Pm) (hJPm : ∀ j ∈ J, ∀ y ∈ Pm, j * y * j⁻¹ ∈ Pm)
    (hJodd : Odd (Nat.card J)) (hZ : Pm ⊓ centralizer (J : Set G) ≤ Zm)
    (hdich : ∀ A₁ A₂ : Subgroup G, A₁ ≤ Pm → A₂ ≤ Pm → (∀ u ∈ Pm, ∀ x ∈ A₁, u * x * u⁻¹ ∈ A₁) →
      (∀ u ∈ Pm, ∀ x ∈ A₂, u * x * u⁻¹ ∈ A₂) → (∀ x ∈ A₁, ∀ y ∈ A₂, x * y = y * x) →
      Pm ≤ A₁ ⊔ A₂ ⊔ Zm → A₁ = Pm ∨ A₂ = Pm)
    (hSRRt : S ≤ (S ⊓ P) ⊔ (S ⊓ P).map (MulAut.conj t).toMonoidHom)
    (hδR : ∀ x ∈ S ⊓ P, x * (t * x * t⁻¹) ∈ Pm)
    (hδR' : ∀ y ∈ Pm, ∃ x ∈ S ⊓ P, x * (t * x * t⁻¹) = y)
    (hJhP : Jh ≤ P) (hJhJ : ∀ j ∈ J, ∃ y ∈ Jh, y * (t * y * t⁻¹) = j)
    (hJhR : ∀ y ∈ Jh, ∀ r ∈ S ⊓ P, y * r * y⁻¹ ∈ S ⊓ P)
    (hR'S : R' ≤ S) (hR'tS : R't ≤ S) (hS' : S ≤ R' ⊔ R't)
    (hc' : ∀ a ∈ R', ∀ b ∈ R't, a * b = b * a)
    (hJhR' : ∀ y ∈ Jh, ∀ r ∈ R', y * r * y⁻¹ ∈ R')
    (hJhR't : ∀ y ∈ Jh, ∀ r ∈ R't, y * r * y⁻¹ ∈ R't) :
    ∃ D : Subgroup G, D ≤ S ⊓ P ∧ (∀ y ∈ Pm, ∃ x ∈ D, x * (t * x * t⁻¹) = y) ∧
      (D ≤ R' ∨ D ≤ R't) := by
  set R : Subgroup G := S ⊓ P with hR
  set Rt : Subgroup G := R.map (MulAut.conj t).toMonoidHom with hRt
  have hRP : R ≤ P := inf_le_right
  have hRtP : Rt ≤ P.map (MulAut.conj t).toMonoidHom := Subgroup.map_mono hRP
  have hRRt : ∀ a ∈ R, ∀ b ∈ Rt, a * b = b * a := fun a ha b hb =>
    comm_P_Pt d (hRP ha) (hRtP hb)
  have hJRt : ∀ y ∈ Jh, ∀ b ∈ Rt, y * b = b * y := fun y hy b hb =>
    comm_P_Pt d (hJhP hy) (hRtP hb)
  have hSR : ⁅S, Jh⁆ ≤ R := commutator_le_of_sup hSRRt hRRt hJRt hJhR
  have hSDpq : ⁅S, Jh⁆ ≤ ⁅R', Jh⁆ ⊔ ⁅R't, Jh⁆ := commutator_le_sup_of_sup hS' hc' hJhR't
  have hDpR : ⁅R', Jh⁆ ≤ R := (Subgroup.commutator_mono_left hR'S).trans hSR
  have hDqR : ⁅R't, Jh⁆ ≤ R := (Subgroup.commutator_mono_left hR'tS).trans hSR
  obtain ⟨hNp, hNq⟩ := normalized_by_S hS' hc' hJhR' hJhR't
  have hDpP : ⁅R', Jh⁆ ≤ P := hDpR.trans hRP
  have hDqP : ⁅R't, Jh⁆ ≤ P := hDqR.trans hRP
  have hsupP : ⁅R', Jh⁆ ⊔ ⁅R't, Jh⁆ ≤ P := sup_le hDpP hDqP
  have hdmP : ∀ A : Subgroup G, A ≤ R → dm d A ≤ Pm := by
    intro A hA y hy
    obtain ⟨a, ha, rfl⟩ := (mem_dm_iff d (hA.trans hRP)).1 hy
    exact hδR a (hA ha)
  have hdmN : ∀ A : Subgroup G, A ≤ R → (∀ s ∈ S, ∀ a ∈ A, s * a * s⁻¹ ∈ A) →
      ∀ u ∈ Pm, ∀ x ∈ dm d A, u * x * u⁻¹ ∈ dm d A := by
    intro A hA hAn u hu x hx
    obtain ⟨r, hr, rfl⟩ := hδR' u hu
    obtain ⟨a, ha, rfl⟩ := (mem_dm_iff d (hA.trans hRP)).1 hx
    rw [← delta_conj d (hRP hr) (hRP (hA ha))]
    exact (mem_dm_iff d (hA.trans hRP)).2 ⟨r * a * r⁻¹, hAn r (mem_inf.1 hr).1 a ha, rfl⟩
  have hdmC : ∀ x ∈ dm d ⁅R', Jh⁆, ∀ y ∈ dm d ⁅R't, Jh⁆, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := (mem_dm_iff d hDpP).1 hx
    obtain ⟨b, hb, rfl⟩ := (mem_dm_iff d hDqP).1 hy
    have hab : a * b = b * a :=
      hc' a (commutator_le_self hJhR' ha) b (commutator_le_self hJhR't hb)
    rw [← d.delta_mul (hDpP ha) (hDqP hb), ← d.delta_mul (hDqP hb) (hDpP ha), hab]
  have hle : Pm ≤ dm d ⁅R', Jh⁆ ⊔ dm d ⁅R't, Jh⁆ ⊔ Zm := by
    intro m hm
    obtain ⟨c, hc, n, hn, rfl⟩ := exists_mul_of_odd_action hPm2 hJPm hJodd hm
    have hn' : n ∈ dm d ⁅R', Jh⁆ ⊔ dm d ⁅R't, Jh⁆ := by
      have : ⁅Pm, J⁆ ≤ dm d ⁅R', Jh⁆ ⊔ dm d ⁅R't, Jh⁆ := by
        rw [commutator_le]
        intro x hx j hj
        obtain ⟨r, hr, rfl⟩ := hδR' x hx
        obtain ⟨y, hy, rfl⟩ := hJhJ j hj
        rw [← delta_commutator d (hRP hr) (hJhP hy), ← dm_sup d hDpP hDqP]
        exact (mem_dm_iff d hsupP).2
          ⟨⁅r, y⁆, hSDpq (commutator_mem_commutator (mem_inf.1 hr).1 hy), rfl⟩
      exact this hn
    exact mul_mem (mem_sup_right (hZ hc)) (mem_sup_left hn')
  rcases hdich (dm d ⁅R', Jh⁆) (dm d ⁅R't, Jh⁆) (hdmP _ hDpR) (hdmP _ hDqR) (hdmN _ hDpR hNp)
    (hdmN _ hDqR hNq) hdmC hle with h | h
  · refine ⟨⁅R', Jh⁆, hDpR, fun y hy => ?_, Or.inl (commutator_le_self hJhR')⟩
    rw [← h] at hy
    exact (mem_dm_iff d hDpP).1 hy
  · refine ⟨⁅R't, Jh⁆, hDqR, fun y hy => ?_, Or.inr (commutator_le_self hJhR't)⟩
    rw [← h] at hy
    exact (mem_dm_iff d hDqP).1 hy

theorem conj_mem_normalizer {A : Subgroup G} (ht : t * t = 1) (htA : ∀ a ∈ A, t * a * t⁻¹ ∈ A)
    {y : G} (hy : y ∈ normalizer (A : Set G)) : t * y * t⁻¹ ∈ normalizer (A : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun a ha => ?_
  have h1 : t⁻¹ * a * t ∈ A := by
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    rw [hti]
    simpa [hti] using htA a ha
  have h2 : y * (t⁻¹ * a * t) * y⁻¹ ∈ A := (mem_normalizer_iff.1 hy _).1 h1
  have h3 := htA _ h2
  have e : t * y * t⁻¹ * a * (t * y * t⁻¹)⁻¹ = t * (y * (t⁻¹ * a * t) * y⁻¹) * t⁻¹ := by group
  rw [e]
  exact h3

theorem lift_normalizes_partner (d : ProductDiagData N X P t ρ) {S P' Jh : Subgroup G}
    (htS : ∀ s ∈ S, t * s * t⁻¹ ∈ S) (hJS : ∀ y ∈ Jh, ∀ s ∈ S, y * s * y⁻¹ ∈ S)
    (hJhP : Jh ≤ P) (hJodd : Odd (Nat.card Jh))
    (hcross : ∀ y : G, y ∈ normalizer (S : Set G) → y ∈ normalizer (X : Set G) →
      Odd (orderOf y) → y ∈ normalizer (P' : Set G)) :
    (∀ y ∈ Jh, ∀ r ∈ S ⊓ P', y * r * y⁻¹ ∈ S ⊓ P') ∧
      (∀ y ∈ Jh, ∀ r ∈ (S ⊓ P').map (MulAut.conj t).toMonoidHom,
        y * r * y⁻¹ ∈ (S ⊓ P').map (MulAut.conj t).toMonoidHom) := by
  have hodd : ∀ y ∈ Jh, Odd (orderOf y) := fun y hy =>
    Odd.of_dvd_nat hJodd (Subgroup.orderOf_dvd_natCard Jh hy)
  have hyS : ∀ y ∈ Jh, y ∈ normalizer (S : Set G) := fun y hy =>
    Subgroup.mem_normalizer_fintype fun s hs => hJS y hy s hs
  have hyX : ∀ y ∈ Jh, y ∈ normalizer (X : Set G) := fun y hy =>
    d.N_le_normalizer (d.P_le (hJhP hy))
  have hnormP : ∀ y ∈ Jh, y ∈ normalizer (P' : Set G) := fun y hy =>
    hcross y (hyS y hy) (hyX y hy) (hodd y hy)
  have hnormP' : ∀ y ∈ Jh, t * y * t⁻¹ ∈ normalizer (P' : Set G) := fun y hy => by
    refine hcross _ (conj_mem_normalizer d.t_sq htS (hyS y hy))
      (conj_mem_normalizer d.t_sq (fun a ha => d.conj_t_mem_X ha) (hyX y hy)) ?_
    refine Odd.of_dvd_nat (hodd y hy) (orderOf_dvd_of_pow_eq_one ?_)
    rw [conj_pow, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
  have hnormS' : ∀ y ∈ Jh, t * y * t⁻¹ ∈ normalizer (S : Set G) := fun y hy =>
    conj_mem_normalizer d.t_sq htS (hyS y hy)
  constructor
  · intro y hy r hr
    exact mem_inf.2 ⟨hJS y hy r (mem_inf.1 hr).1,
      (mem_normalizer_iff.1 (hnormP y hy) r).1 (mem_inf.1 hr).2⟩
  · intro y hy r hr
    rw [diag_mem_map_conj_iff d.t_sq] at hr ⊢
    have e : t * (y * r * y⁻¹) * t⁻¹ = (t * y * t⁻¹) * (t * r * t⁻¹) * (t * y * t⁻¹)⁻¹ := by group
    rw [e]
    exact mem_inf.2 ⟨(mem_normalizer_iff.1 (hnormS' y hy) _).1 (mem_inf.1 hr).1,
      (mem_normalizer_iff.1 (hnormP' y hy) _).1 (mem_inf.1 hr).2⟩

end Main

section Frattini

variable {G : Type*} [Group G] [Finite G]

theorem exists_complement_of_inf_sq {R K : Subgroup G} (hKR : K ≤ R)
    (hK : ∀ k ∈ K, k ∈ Subgroup.closure {x : G | ∃ r ∈ R, x = r * r} → k = 1) :
    ∃ W : Subgroup G, W ≤ R ∧ K ⊓ W = ⊥ ∧ K ⊔ W = R := by
  set Φ : Subgroup G := Subgroup.closure {x : G | ∃ r ∈ R, x = r * r} with hΦ
  have hgen : ∀ r ∈ R, r * r ∈ Φ := fun r hr => Subgroup.subset_closure ⟨r, hr, rfl⟩
  have hΦR : Φ ≤ R := (Subgroup.closure_le R).2 (by rintro _ ⟨r, hr, rfl⟩; exact mul_mem hr hr)
  have hcomm : ∀ x ∈ R, ∀ y ∈ R, x * y * x⁻¹ * y⁻¹ ∈ Φ := by
    intro x hx y hy
    have e : x * y * x⁻¹ * y⁻¹ = (x * x) * ((x⁻¹ * y) * (x⁻¹ * y)) * (y⁻¹ * y⁻¹) := by group
    rw [e]
    exact mul_mem (mul_mem (hgen x hx) (hgen _ (mul_mem (inv_mem hx) hy))) (hgen _ (inv_mem hy))
  let 𝒲 : Set (Subgroup G) := {W | W ≤ R ∧ Φ ≤ W ∧ K ⊓ W = ⊥}
  have hΦ𝒲 : Φ ∈ 𝒲 := ⟨hΦR, le_rfl, eq_bot_iff.2 fun k hk =>
    mem_bot.2 (hK k (mem_inf.1 hk).1 (mem_inf.1 hk).2)⟩
  haveI : Finite (Subgroup G) :=
    Finite.of_injective (SetLike.coe : Subgroup G → Set G) SetLike.coe_injective
  obtain ⟨W, hW, hmax⟩ := Set.exists_max_image 𝒲 (fun W : Subgroup G => Nat.card W)
    (Set.toFinite 𝒲) ⟨Φ, hΦ𝒲⟩
  obtain ⟨hWR, hΦW, hKW⟩ := hW
  refine ⟨W, hWR, hKW, le_antisymm (sup_le hKR hWR) ?_⟩
  intro x hx
  by_contra hxn
  have hxW : ∀ w ∈ W, x * w * x⁻¹ ∈ W := by
    intro w hw
    have h1 : x * w * x⁻¹ * w⁻¹ ∈ W := hΦW (hcomm x hx w (hWR hw))
    have := mul_mem h1 hw
    rwa [inv_mul_cancel_right] at this
  have hle : zpowers x ≤ normalizer (W : Set G) :=
    Subgroup.zpowers_le.2 (Subgroup.mem_normalizer_fintype hxW)
  have hx2 : x * x ∈ W := hΦW (hgen x hx)
  have hKW' : K ⊓ (zpowers x ⊔ W) = ⊥ := by
    refine eq_bot_iff.2 fun k hk => ?_
    obtain ⟨hkK, hkW'⟩ := mem_inf.1 hk
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right (zpowers x) W hle]
      at hkW'
    obtain ⟨a, ha, w, hw, rfl⟩ := Set.mem_mul.1 hkW'
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 ha
    have hsq : x ^ (2 : ℤ) ∈ W := by rw [zpow_two]; exact hx2
    obtain ⟨m, hm | hm⟩ := Int.even_or_odd' n
    · have h1 : x ^ n ∈ W := by
        rw [hm, zpow_mul]
        exact Subgroup.zpow_mem _ hsq m
      have : x ^ n * w ∈ K ⊓ W := mem_inf.2 ⟨hkK, mul_mem h1 hw⟩
      rw [hKW] at this
      exact this
    · exfalso
      have h1 : (x ^ (2 : ℤ)) ^ m ∈ W := Subgroup.zpow_mem _ hsq m
      have h2 : x ^ n = (x ^ (2 : ℤ)) ^ m * x := by
        rw [hm, zpow_add, zpow_mul, zpow_one]
      apply hxn
      have ex : x = ((x ^ (2 : ℤ)) ^ m)⁻¹ * (x ^ n * w) * w⁻¹ := by
        rw [h2]
        generalize (x ^ (2 : ℤ)) ^ m = a
        group
      rw [ex]
      exact mul_mem (mul_mem (mem_sup_right (inv_mem h1)) (mem_sup_left hkK))
        (mem_sup_right (inv_mem hw))
  have hmem : zpowers x ⊔ W ∈ 𝒲 :=
    ⟨sup_le (Subgroup.zpowers_le.2 hx) hWR, hΦW.trans le_sup_right, hKW'⟩
  have hxnW : x ∉ W := fun h => hxn (mem_sup_right h)
  have hlt : W < zpowers x ⊔ W :=
    lt_of_le_of_ne le_sup_right fun h => hxnW (h ▸ mem_sup_left (mem_zpowers x))
  exact absurd (hmax _ hmem) (not_le.2 (Subgroup.card_lt_of_lt hlt))

end Frattini

section KBot

variable {G : Type*} [Group G] [Finite G] {H : Type*} [Group H] {N X P : Subgroup G} {t : G}
  {ρ : N →* H × H}

theorem kerSub_eq_bot (d : ProductDiagData N X P t ρ) {S Pm U W₁ W₂ P' D : Subgroup G}
    (hKR : kerSub d ≤ S ⊓ P) (hKcent : ∀ k ∈ kerSub d, ∀ s ∈ S, k * s = s * k)
    (hKsq : ∀ k ∈ kerSub d, k * k = 1) (hKU : kerSub d ≤ U) (hUW : U ≤ W₁)
    (hUt : ∀ u ∈ U, t * u = u * t)
    (hδR : ∀ x ∈ S ⊓ P, x * (t * x * t⁻¹) ∈ Pm)
    (hD : D ≤ S ⊓ P) (hDδ : ∀ y ∈ Pm, ∃ x ∈ D, x * (t * x * t⁻¹) = y)
    (hDP' : D ≤ P' ∨ D ≤ P'.map (MulAut.conj t).toMonoidHom)
    (hY' : ∀ z ∈ P', z ∈ P'.map (MulAut.conj t).toMonoidHom → z ∈ W₂)
    (hWW : ∀ x ∈ W₁, x ∈ W₂ → x = 1)
    (hcentP : ∀ k ∈ kerSub d, ∀ p ∈ P, k * p = p * k)
    (hodd : ¬ 2 ∣ (S ⊓ P).relIndex P) (hR2 : IsPGroup 2 (S ⊓ P : Subgroup G))
    (hK2 : IsPGroup 2 (kerSub d)) : kerSub d = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRP : S ⊓ P ≤ P := inf_le_right
  have hsq : ∀ r ∈ S ⊓ P, ∃ x ∈ D, r * r = x * x := by
    intro r hr
    obtain ⟨x, hx, hxr⟩ := hDδ _ (hδR r hr)
    have hk : x⁻¹ * r ∈ kerSub d := inv_mul_mem_kerSub d (hRP (hD hx)) (hRP hr) hxr
    refine ⟨x, hx, ?_⟩
    have h1 := hKcent _ hk x (mem_inf.1 (hD hx)).1
    have h2 := hKsq _ hk
    calc r * r = x * (x⁻¹ * r) * (x * (x⁻¹ * r)) := by group
      _ = x * ((x⁻¹ * r) * x) * (x⁻¹ * r) := by group
      _ = x * (x * (x⁻¹ * r)) * (x⁻¹ * r) := by rw [h1]
      _ = x * x * ((x⁻¹ * r) * (x⁻¹ * r)) := by group
      _ = x * x := by rw [h2, mul_one]
  have hΦ : ∀ k ∈ kerSub d, k ∈ Subgroup.closure {x : G | ∃ r ∈ S ⊓ P, x = r * r} → k = 1 := by
    intro k hk hkΦ
    have hkU := hKU hk
    have htk : t * k * t⁻¹ = k := by
      rw [hUt k hkU]
      group
    have hkW₁ := hUW hkU
    have hkP' : k ∈ P' ∨ k ∈ P'.map (MulAut.conj t).toMonoidHom := by
      rcases hDP' with hDP | hDP
      · left
        refine (Subgroup.closure_le P').2 ?_ hkΦ
        rintro _ ⟨r, hr, rfl⟩
        obtain ⟨x, hx, e⟩ := hsq r hr
        rw [e]
        exact mul_mem (hDP hx) (hDP hx)
      · right
        refine (Subgroup.closure_le (P'.map (MulAut.conj t).toMonoidHom)).2 ?_ hkΦ
        rintro _ ⟨r, hr, rfl⟩
        obtain ⟨x, hx, e⟩ := hsq r hr
        rw [e]
        exact mul_mem (hDP hx) (hDP hx)
    have hboth : k ∈ P' ∧ k ∈ P'.map (MulAut.conj t).toMonoidHom := by
      rcases hkP' with h | h
      · exact ⟨h, (diag_mem_map_conj_iff d.t_sq).2 (by rw [htk]; exact h)⟩
      · refine ⟨?_, h⟩
        have := (diag_mem_map_conj_iff d.t_sq).1 h
        rwa [htk] at this
    exact hWW k hkW₁ (hY' k hboth.1 hboth.2)
  obtain ⟨W, hWR, hKW, hKWR⟩ := exists_complement_of_inf_sq hKR hΦ
  have hKP : kerSub d ≤ P := fun k hk => (mem_kerSub_iff d).1 hk |>.1
  have hG := CFSG.LocalAnalysis.EvenBN.U4.commutator_inf_eq_bot_of_central (p := 2) hKP
    (fun p hp => mem_centralizer_iff.2 fun k hk => hcentP k hk p hp) hK2 hRP hR2 hodd hWR hKW hKWR
  rw [d.perfect, inf_of_le_right hKP] at hG
  exact hG

end KBot

section Transport

variable {G : Type*} [Group G] {L : Subgroup G} {M : Type*} [Group M]

theorem eq_or_eq_of_pull (φ : L ≃* M) {U Z : Subgroup M}
    (hdich : ∀ H₁ H₂ : Subgroup M, H₁ ≤ U → H₂ ≤ U → (∀ u ∈ U, ∀ x ∈ H₁, u * x * u⁻¹ ∈ H₁) →
      (∀ u ∈ U, ∀ x ∈ H₂, u * x * u⁻¹ ∈ H₂) → (∀ x ∈ H₁, ∀ y ∈ H₂, x * y = y * x) →
      U ≤ H₁ ⊔ H₂ ⊔ Z → H₁ = U ∨ H₂ = U)
    {A₁ A₂ : Subgroup G} (hA₁ : A₁ ≤ pull φ U) (hA₂ : A₂ ≤ pull φ U)
    (hn₁ : ∀ u ∈ pull φ U, ∀ x ∈ A₁, u * x * u⁻¹ ∈ A₁)
    (hn₂ : ∀ u ∈ pull φ U, ∀ x ∈ A₂, u * x * u⁻¹ ∈ A₂)
    (hc : ∀ x ∈ A₁, ∀ y ∈ A₂, x * y = y * x) (hle : pull φ U ≤ A₁ ⊔ A₂ ⊔ pull φ Z) :
    A₁ = pull φ U ∨ A₂ = pull φ U := by
  have hpull : ∀ A : Subgroup G, A ≤ L → pull φ ((A.subgroupOf L).map φ.toMonoidHom) = A := by
    intro A hAL
    rw [pull, Subgroup.comap_map_eq_self_of_injective (f := φ.toMonoidHom) φ.injective,
      Subgroup.subgroupOf_map_subtype, inf_of_le_left hAL]
  have hAL₁ : A₁ ≤ L := hA₁.trans (pull_le φ U)
  have hAL₂ : A₂ ≤ L := hA₂.trans (pull_le φ U)
  have hmem : ∀ {A : Subgroup G} (hAL : A ≤ L) {y : M},
      y ∈ (A.subgroupOf L).map φ.toMonoidHom ↔ ((φ.symm y : L) : G) ∈ A := by
    intro A hAL y
    constructor
    · rintro ⟨a, ha, rfl⟩
      simpa using mem_subgroupOf.1 ha
    · intro hy
      exact ⟨φ.symm y, mem_subgroupOf.2 hy, by simp⟩
  have hnorm : ∀ {A : Subgroup G} (hAL : A ≤ L), (∀ u ∈ pull φ U, ∀ x ∈ A, u * x * u⁻¹ ∈ A) →
      ∀ u ∈ U, ∀ x ∈ (A.subgroupOf L).map φ.toMonoidHom,
        u * x * u⁻¹ ∈ (A.subgroupOf L).map φ.toMonoidHom := by
    intro A hAL hn u hu x hx
    rw [hmem hAL] at hx ⊢
    have e : ((φ.symm (u * x * u⁻¹) : L) : G) =
        ((φ.symm u : L) : G) * ((φ.symm x : L) : G) * ((φ.symm u : L) : G)⁻¹ := by
      simp [map_mul, map_inv]
    rw [e]
    exact hn _ (symm_mem_pull.2 hu) _ hx
  have hcomm : ∀ x ∈ (A₁.subgroupOf L).map φ.toMonoidHom, ∀ y ∈ (A₂.subgroupOf L).map φ.toMonoidHom,
      x * y = y * x := by
    intro x hx y hy
    rw [hmem hAL₁] at hx
    rw [hmem hAL₂] at hy
    have h1 := hc _ hx _ hy
    have h2 : φ.symm x * φ.symm y = φ.symm y * φ.symm x := Subtype.ext h1
    have h3 := congrArg φ h2
    simpa [map_mul] using h3
  have hU₁ : (A₁.subgroupOf L).map φ.toMonoidHom ≤ U := fun y hy => by
    rw [hmem hAL₁] at hy
    exact symm_mem_pull.1 (hA₁ hy)
  have hU₂ : (A₂.subgroupOf L).map φ.toMonoidHom ≤ U := fun y hy => by
    rw [hmem hAL₂] at hy
    exact symm_mem_pull.1 (hA₂ hy)
  have hUle : U ≤ (A₁.subgroupOf L).map φ.toMonoidHom ⊔ (A₂.subgroupOf L).map φ.toMonoidHom ⊔ Z := by
    intro y hy
    have h1 : ((φ.symm y : L) : G) ∈ pull φ ((A₁.subgroupOf L).map φ.toMonoidHom ⊔
        (A₂.subgroupOf L).map φ.toMonoidHom ⊔ Z) := by
      rw [pull_sup, pull_sup, hpull A₁ hAL₁, hpull A₂ hAL₂]
      exact hle (symm_mem_pull.2 hy)
    exact symm_mem_pull.1 h1
  rcases hdich _ _ hU₁ hU₂ (hnorm hAL₁ hn₁) (hnorm hAL₂ hn₂) hcomm hUle with h | h
  · left
    rw [← hpull A₁ hAL₁, h]
  · right
    rw [← hpull A₂ hAL₂, h]

theorem pull_inf_centralizer_le (φ : L ≃* M) {U T Z : Subgroup M}
    (h : U ⊓ centralizer (T : Set M) ≤ Z) :
    pull φ U ⊓ centralizer (pull φ T : Set G) ≤ pull φ Z := by
  intro x hx
  obtain ⟨hxU, hxC⟩ := mem_inf.1 hx
  obtain ⟨hxL, hxU'⟩ := mem_pull.1 hxU
  refine mem_pull.2 ⟨hxL, h (mem_inf.2 ⟨hxU', mem_centralizer_iff.2 fun a ha => ?_⟩)⟩
  have h1 := mem_centralizer_iff.1 hxC ((φ.symm a : L) : G) (symm_mem_pull.2 ha)
  have h2 : φ.symm a * ⟨x, hxL⟩ = ⟨x, hxL⟩ * φ.symm a := Subtype.ext h1
  have h3 := congrArg φ h2
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h3
  exact h3

end Transport

section Assembly

variable {G : Type*} [Group G] {H : Type*} [Group H] {N X P : Subgroup G} {t : G}
  {ρ : N →* H × H}

structure SharedHyp (t : G) (S Pm Zm : Subgroup G) : Prop where
  S2 : IsPGroup 2 S
  tS : ∀ s ∈ S, t * s * t⁻¹ ∈ S
  Pm_le : Pm ≤ S
  SC : ∀ x ∈ S, t * x = x * t → x ∈ Pm
  Pm_t : ∀ x ∈ Pm, t * x = x * t
  card_S : Nat.card S = Nat.card Pm ^ 2
  dich : ∀ A₁ A₂ : Subgroup G, A₁ ≤ Pm → A₂ ≤ Pm → (∀ u ∈ Pm, ∀ x ∈ A₁, u * x * u⁻¹ ∈ A₁) →
    (∀ u ∈ Pm, ∀ x ∈ A₂, u * x * u⁻¹ ∈ A₂) → (∀ x ∈ A₁, ∀ y ∈ A₂, x * y = y * x) →
    Pm ≤ A₁ ⊔ A₂ ⊔ Zm → A₁ = Pm ∨ A₂ = Pm

structure AxisHyp (d : ProductDiagData N X P t ρ) (S Pm Zm CU U W J : Subgroup G) : Prop where
  X_le_S : X ≤ S
  S_le_N : S ≤ N
  S_odd : ¬ 2 ∣ S.relIndex N
  Pm_le_CU : Pm ≤ CU
  U_le_Pm : U ≤ Pm
  diag₁ : ∀ x ∈ P, x * (t * x * t⁻¹) ∈ CU
  diag₂ : ∀ y ∈ CU, ∃ x ∈ P, x * (t * x * t⁻¹) = y
  diag₃ : ∀ x ∈ P, x * (t * x * t⁻¹) = 1 → x ∈ U
  U_le_W : U ≤ W
  X_inf_W : ∀ x ∈ X, x ∈ centralizer (N : Set G) → x ∈ W
  J_le_CU : J ≤ CU
  J_norm : ∀ j ∈ J, ∀ y ∈ Pm, j * y * j⁻¹ ∈ Pm
  J_odd : Odd (Nat.card J)
  J_cent : Pm ⊓ centralizer (J : Set G) ≤ Zm

variable [Finite G] {S Pm Zm CU U W J : Subgroup G}

theorem AxisHyp.step1 {d : ProductDiagData N X P t ρ} (A : AxisHyp d S Pm Zm CU U W J)
    (sh : SharedHyp t S Pm Zm) :
    kerSub d ≤ S ⊓ P ∧ (∀ x ∈ S ⊓ P, x * (t * x * t⁻¹) ∈ Pm) ∧
      (∀ y ∈ Pm, ∃ x ∈ S ⊓ P, x * (t * x * t⁻¹) = y) ∧
      Nat.card (S ⊓ P : Subgroup G) = Nat.card Pm * Nat.card (kerSub d) ∧
      (S ⊓ P) ⊔ (S ⊓ P).map (MulAut.conj t).toMonoidHom = S ∧ ¬ 2 ∣ (S ⊓ P).relIndex P := by
  have hodd : ¬ 2 ∣ S.relIndex P := not_two_dvd_relIndex_P d A.S_le_N A.S_odd
  obtain ⟨h1, h2, h3, h4⟩ := R_facts d sh.S2 sh.Pm_le sh.tS sh.SC A.Pm_le_CU A.U_le_Pm A.diag₁
    A.diag₂ A.diag₃ hodd
  exact ⟨h1, h2, h3, h4, sup_conj_eq d sh.tS sh.card_S h4, by rwa [Subgroup.inf_relIndex_right]⟩

theorem pair_step {H' : Type*} [Group H'] {N' X' P' : Subgroup G} {ρ' : N' →* H' × H'}
    (d : ProductDiagData N X P t ρ) (d' : ProductDiagData N' X' P' t ρ')
    {CU' U' W' J' : Subgroup G} (sh : SharedHyp t S Pm Zm) (A : AxisHyp d S Pm Zm CU U W J)
    (A' : AxisHyp d' S Pm Zm CU' U' W' J')
    (cross : ∀ y : G, y ∈ normalizer (S : Set G) → y ∈ normalizer (X : Set G) → Odd (orderOf y) →
      y ∈ normalizer (P' : Set G))
    (hWW : ∀ x ∈ W, x ∈ W' → x = 1) :
    kerSub d = ⊥ ∧ ∃ D : Subgroup G, D ≤ S ⊓ P ∧
      (∀ y ∈ Pm, ∃ x ∈ D, x * (t * x * t⁻¹) = y) ∧
      (D ≤ S ⊓ P' ∨ D ≤ (S ⊓ P').map (MulAut.conj t).toMonoidHom) := by
  obtain ⟨hKR, hδ, hδ', -, hSeq, hodd⟩ := A.step1 sh
  obtain ⟨-, -, -, -, hSeq', -⟩ := A'.step1 sh
  have hRP : S ⊓ P ≤ P := inf_le_right
  have hK2 : IsPGroup 2 (kerSub d) := sh.S2.to_le (hKR.trans inf_le_left)
  have hR2 : IsPGroup 2 (S ⊓ P : Subgroup G) := sh.S2.to_le inf_le_left
  obtain ⟨Jh, hJhP, hJhodd, -, hJhJ, hJhR⟩ := exists_odd_lift d hKR
    (fun j hj => A.diag₂ j (A.J_le_CU hj)) hδ hδ' A.J_norm hRP hK2 A.J_odd
  have hRtP : (S ⊓ P).map (MulAut.conj t).toMonoidHom ≤ P.map (MulAut.conj t).toMonoidHom :=
    Subgroup.map_mono hRP
  have hRtS : (S ⊓ P).map (MulAut.conj t).toMonoidHom ≤ S := fun y hy => by
    have := sh.tS _ (mem_inf.1 ((diag_mem_map_conj_iff d.t_sq).1 hy)).1
    rwa [diag_conj_conj d.t_sq] at this
  have hJS : ∀ y ∈ Jh, ∀ s ∈ S, y * s * y⁻¹ ∈ S := by
    intro y hy s hs
    obtain ⟨a, ha, b, hb, rfl⟩ := diag_exists_mul_of_mem_sup
      (fun a ha b hb => comm_P_Pt d (hRP ha) (hRtP hb)) (hSeq.ge hs)
    have hyb : y * b * y⁻¹ = b := by
      rw [comm_P_Pt d (hJhP hy) (hRtP hb)]
      group
    have e : y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
    rw [e, hyb]
    exact mul_mem (mem_inf.1 (hJhR y hy a ha)).1 (hRtS hb)
  obtain ⟨hJhR', hJhR't⟩ := lift_normalizes_partner d sh.tS hJS hJhP hJhodd cross
  have hR'tS : (S ⊓ P').map (MulAut.conj t).toMonoidHom ≤ S := fun y hy => by
    have := sh.tS _ (mem_inf.1 ((diag_mem_map_conj_iff d.t_sq).1 hy)).1
    rwa [diag_conj_conj d.t_sq] at this
  obtain ⟨D, hD, hDδ, hDR'⟩ := dichotomy d (sh.S2.to_le sh.Pm_le) A.J_norm A.J_odd A.J_cent sh.dich
    hSeq.ge hδ hδ' hJhP hJhJ hJhR (inf_le_left : S ⊓ P' ≤ S) hR'tS hSeq'.ge
    (fun a ha b hb => comm_P_Pt d' (mem_inf.1 ha).2 (Subgroup.map_mono inf_le_right hb)) hJhR'
    hJhR't
  refine ⟨?_, D, hD, hDδ, hDR'⟩
  have hKcentN : ∀ k ∈ kerSub d, k ∈ centralizer (N : Set G) := fun k hk =>
    d.mem_centralizer_of_mem_inf (kerSub_le_inf d hk).1 (kerSub_le_inf d hk).2
  refine kerSub_eq_bot d (U := U) (W₁ := W) (W₂ := W') (P' := P') hKR
    (fun k hk s hs => (mem_centralizer_iff.1 (hKcentN k hk) s (A.S_le_N hs)).symm)
    (fun k hk => d.X_sq k (d.mem_X_of_mem_inf (kerSub_le_inf d hk).1 (kerSub_le_inf d hk).2))
    (fun k hk => A.diag₃ k ((mem_kerSub_iff d).1 hk).1 ((mem_kerSub_iff d).1 hk).2) A.U_le_W
    (fun u hu => sh.Pm_t u (A.U_le_Pm hu)) hδ hD hDδ ?_ ?_ hWW
    (fun k hk p hp => (mem_centralizer_iff.1 (hKcentN k hk) p (d.P_le hp)).symm) hodd hR2 hK2
  · rcases hDR' with h | h
    · exact Or.inl (h.trans inf_le_right)
    · exact Or.inr (h.trans (Subgroup.map_mono inf_le_right))
  · intro z hz hzt
    exact A'.X_inf_W z (d'.mem_X_of_mem_inf hz hzt) (d'.mem_centralizer_of_mem_inf hz hzt)

theorem map_inf_conj_eq {S P' : Subgroup G} (ht : t * t = 1) (htS : ∀ s ∈ S, t * s * t⁻¹ ∈ S) :
    (S ⊓ P').map (MulAut.conj t).toMonoidHom = S ⊓ P'.map (MulAut.conj t).toMonoidHom := by
  ext y
  rw [diag_mem_map_conj_iff ht, mem_inf, mem_inf, diag_mem_map_conj_iff ht]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have := htS _ h1
    rwa [diag_conj_conj ht] at this
  · rintro ⟨h1, h2⟩
    exact ⟨htS y h1, h2⟩

theorem main_abstract {H₁ H₂ : Type*} [Group H₁] [Group H₂] {N₁ X₁ P₁ N₂ X₂ P₂ : Subgroup G}
    {ρ₁ : N₁ →* H₁ × H₁} {ρ₂ : N₂ →* H₂ × H₂}
    (d₁ : ProductDiagData N₁ X₁ P₁ t ρ₁) (d₂ : ProductDiagData N₂ X₂ P₂ t ρ₂)
    {CU₁ U₁ W₁ J₁ CU₂ U₂ W₂ J₂ : Subgroup G} (sh : SharedHyp t S Pm Zm)
    (A₁ : AxisHyp d₁ S Pm Zm CU₁ U₁ W₁ J₁) (A₂ : AxisHyp d₂ S Pm Zm CU₂ U₂ W₂ J₂)
    (cross₁ : ∀ y : G, y ∈ normalizer (S : Set G) → y ∈ normalizer (X₁ : Set G) →
      Odd (orderOf y) → y ∈ normalizer (P₂ : Set G))
    (cross₂ : ∀ y : G, y ∈ normalizer (S : Set G) → y ∈ normalizer (X₂ : Set G) →
      Odd (orderOf y) → y ∈ normalizer (P₁ : Set G))
    (hWW : ∀ x ∈ W₁, x ∈ W₂ → x = 1) :
    P₁ ⊓ P₁.map (MulAut.conj t).toMonoidHom = ⊥ ∧ P₂ ⊓ P₂.map (MulAut.conj t).toMonoidHom = ⊥ ∧
      (S ⊓ P₁ = S ⊓ P₂ ∨ S ⊓ P₁ = S ⊓ P₂.map (MulAut.conj t).toMonoidHom) := by
  obtain ⟨hK₁, D₁, hD₁R, hD₁δ, hD₁⟩ := pair_step d₁ d₂ sh A₁ A₂ cross₁ hWW
  obtain ⟨hK₂, -⟩ := pair_step d₂ d₁ sh A₂ A₁ cross₂ (fun x h2 h1 => hWW x h1 h2)
  obtain ⟨-, hδ₁, -, hRcard₁, -, -⟩ := A₁.step1 sh
  obtain ⟨-, -, -, hRcard₂, -, -⟩ := A₂.step1 sh
  have hY₁ : P₁ ⊓ P₁.map (MulAut.conj t).toMonoidHom = ⊥ := by
    have h := card_inf_le d₁
    rw [hK₁, Subgroup.card_bot, one_pow] at h
    exact (Subgroup.card_le_one_iff_eq_bot _).1 h
  have hY₂ : P₂ ⊓ P₂.map (MulAut.conj t).toMonoidHom = ⊥ := by
    have h := card_inf_le d₂
    rw [hK₂, Subgroup.card_bot, one_pow] at h
    exact (Subgroup.card_le_one_iff_eq_bot _).1 h
  refine ⟨hY₁, hY₂, ?_⟩
  rw [hK₁, Subgroup.card_bot, mul_one] at hRcard₁
  rw [hK₂, Subgroup.card_bot, mul_one] at hRcard₂
  have hR₁ : ∀ r ∈ S ⊓ P₁, r ∈ D₁ := by
    intro r hr
    obtain ⟨x, hx, hxr⟩ := hD₁δ _ (hδ₁ r hr)
    have hk := inv_mul_mem_kerSub d₁ (mem_inf.1 (hD₁R hx)).2 (mem_inf.1 hr).2 hxr
    rw [hK₁, mem_bot, inv_mul_eq_one] at hk
    rw [← hk]
    exact hx
  rcases hD₁ with h | h
  · left
    exact Subgroup.eq_of_le_of_card_ge (fun r hr => h (hR₁ r hr)) (by rw [hRcard₁, hRcard₂])
  · right
    rw [← map_inf_conj_eq d₂.t_sq sh.tS]
    refine Subgroup.eq_of_le_of_card_ge (fun r hr => h (hR₁ r hr)) ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj t).injective, hRcard₁, hRcard₂]

theorem AxisHyp.sup_conj_eq_N {d : ProductDiagData N X P t ρ} (A : AxisHyp d S Pm Zm CU U W J)
    (sh : SharedHyp t S Pm Zm) {q : ℕ} (hq : 0 < q)
    (hH : ∀ B : Subgroup H, IsPGroup 2 B → Nat.card B ≤ q)
    (hPm : Nat.card Pm = q ^ 4) (hX : Nat.card X = q ^ 6) :
    P ⊔ P.map (MulAut.conj t).toMonoidHom = N := by
  obtain ⟨hKR, -, -, hRcard, -, -⟩ := A.step1 sh
  have hR2 : IsPGroup 2 (S ⊓ P : Subgroup G) := sh.S2.to_le inf_le_left
  have h1 := card_le_inf_mul d hH (inf_le_right : S ⊓ P ≤ P) hR2
  have hRX : (S ⊓ P) ⊓ X = P ⊓ X := by
    ext x
    simp only [mem_inf]
    constructor
    · rintro ⟨⟨_, hP⟩, hX'⟩
      exact ⟨hP, hX'⟩
    · rintro ⟨hP, hX'⟩
      exact ⟨⟨A.X_le_S hX', hP⟩, hX'⟩
  rw [hRX, hRcard, hPm] at h1
  have h2 : q ^ 3 * Nat.card (kerSub d) ≤ Nat.card (P ⊓ X : Subgroup G) := by
    refine Nat.le_of_mul_le_mul_right ?_ hq
    calc q ^ 3 * Nat.card (kerSub d) * q = q ^ 4 * Nat.card (kerSub d) := by ring
      _ ≤ _ := h1
  exact sup_conj_eq_N_of_X_le d ((X_le_sup d hX h2).trans (sup_le_sup inf_le_left inf_le_left))

end Assembly

section Maximal

variable {G : Type*} [Group G] [Finite G]

theorem mem_normalizer_of_max {Lam P : Subgroup G} (hP : ⁅P, P⁆ = P) (hPΛ : P ≤ Lam)
    (hmax : ∀ Q : Subgroup G, Q ≤ Lam → ⁅Q, Q⁆ = Q → Q ≤ P) {y : G}
    (hy : y ∈ normalizer (Lam : Set G)) : y ∈ normalizer (P : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun p hp => ?_
  have hQ : P.map (MulAut.conj y).toMonoidHom ≤ P := by
    refine hmax _ ?_ ?_
    · rintro _ ⟨q, hq, rfl⟩
      exact (mem_normalizer_iff.1 hy q).1 (hPΛ hq)
    · rw [← Subgroup.map_commutator, hP]
  exact hQ ⟨p, hp, rfl⟩

end Maximal

end CommonSylow

end CommonSylowAbstract

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G}

local notation "𝐀[" i "]" => pull φ (rootA K i)
local notation "𝐔[" i "]" => pull φ (rootU K i)
set_option quotPrecheck false in
local notation "𝐃[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄₀" => (𝐄[Axis.one] ⊓ 𝐄[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐅" => closure {x : G | ∃ e ∈ 𝐄₀, ∃ j ∈ pull φ (diagTorus K),
  x = e⁻¹ * (j⁻¹ * e * j)}
local notation "𝐰[" i "]" => ((φ.symm (weylElt K i) : L) : G)
set_option quotPrecheck false in
local notation "𝐗[" i "]" => (𝐅 ⊔ 𝐅.map (MulAut.conj 𝐰[i]⁻¹).toMonoidHom : Subgroup G)
set_option quotPrecheck false in
local notation "𝐒" => (𝐗[Axis.one] ⊔ 𝐗[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐍𝐂[" i "]" => closure {x : G | ∃ g ∈ normalizer (𝐗[i] : Set G),
  ∃ y ∈ (L ⊓ centralizer (𝐔[i] : Set G) : Subgroup G) ⊔ 𝐗[i], x = g⁻¹ * y * g}

structure AxisData (h : FCHyp L K n φ t) (i : Axis) where
  ρ : 𝐍𝐂[i] →* SL(2, K) × SL(2, K)
  surj : Function.Surjective ρ
  ker : ρ.ker = 𝐗[i].subgroupOf 𝐍𝐂[i]
  swap : ∀ x y : 𝐍𝐂[i], (y : G) = t * x * t⁻¹ → ρ y = (ρ x).swap
  β : SL(2, K) ≃* SL(2, K)
  rho_s : ∀ (M : SL(2, K)) (hM : ((φ.symm (sHom K i M) : L) : G) ∈ 𝐍𝐂[i]),
    ρ ⟨_, hM⟩ = (β M, β M)
  P : Subgroup G
  le : P ≤ prodFst ρ
  perfect : ⁅P, P⁆ = P
  sup_X : P ⊔ 𝐗[i] = prodFst ρ
  comm : ⁅P, P.map (MulAut.conj t).toMonoidHom⁆ = ⊥
  max : ∀ Q : Subgroup G, Q ≤ prodFst ρ → ⁅Q, Q⁆ = Q → Q ≤ P

theorem AxisData.diagData (h : FCHyp L K n φ t)
    (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) {i : Axis} (d : AxisData h i) :
    ProductDiagData 𝐍𝐂[i] 𝐗[i] d.P t d.ρ :=
  ProductDiagData.mk d.surj d.ker (le_sup_right.trans (sup_le_NC (φ := φ) (t := t) i))
    (fun x hx => X_mul_self h hbt i hx)
    (fun x hx y hy => comm_of_mul_self (fun _ hz => X_mul_self h hbt i hz) hx hy)
    (mem_normalizer_of_conj_le fun z hz => conj_mem_NC i (t_mem_normalizer_X h i) hz)
    h.setup.t_mul_t d.swap d.le d.perfect d.sup_X d.comm d.max

theorem card_S_eq (h : FCHyp L K n φ t)
    (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) : Nat.card 𝐒 = (2 ^ n) ^ 8 := by
  have hf := closureSetupFacts h hbt Axis.one
  have h1 := card_barSub hf.X_le_S hf.S_le
  rw [hf.card_S, hf.card_X] at h1
  rw [← h1]
  ring

theorem sharedHyp (h : FCHyp L K n φ t)
    (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) :
    CommonSylow.SharedHyp t 𝐒 (pull φ (antiUnipotent K)) (pull φ (antiUnipotentCenter K)) := by
  have hSC := BothTrivialSlice.S_inf_C h hbt
  have hcard := card_S_eq h hbt
  have hPcard : Nat.card (pull φ (antiUnipotent K)) = (2 ^ n) ^ 4 := by
    rw [card_pull, card_antiUnipotent h.setup.card_K]
  refine ⟨IsPGroup.of_card (n := 8 * n) (by rw [hcard]; ring), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    exact (mem_normalizer_iff.1 (T_le_normalizer_S h hbt (t_mem_T h)) s).1 hs
  · exact fun x hx => (mem_inf.1 (hSC.ge hx)).1
  · exact fun x hx hxt => hSC.le (mem_inf.2 ⟨hx, mem_centralizer_singleton_iff.2 hxt.symm⟩)
  · exact fun x hx => (mem_centralizer_singleton_iff.1 (mem_inf.1 (hSC.ge hx)).2).symm
  · rw [hcard, hPcard]
    ring
  · exact fun A₁ A₂ h1 h2 n1 n2 c hle => CommonSylow.eq_or_eq_of_pull φ
      (fun H₁ H₂ h1' h2' n1' n2' c' hU => ProductModel.antiUnipotent_eq_of_commute h.four_le_card
        h1' h2' n1' n2' c' hU) h1 h2 n1 n2 c hle

theorem P_le_CU (i : Axis) :
    pull φ (antiUnipotent K) ≤ L ⊓ centralizer (𝐔[i] : Set G) := by
  intro p hp
  refine mem_inf.2 ⟨pull_le φ _ hp, mem_centralizer_iff.2 fun u hu => ?_⟩
  obtain ⟨hpL, hp'⟩ := mem_pull.1 hp
  obtain ⟨huL, hu'⟩ := mem_pull.1 hu
  have h1 := antiUnipotentCenter_comm ((rootU_le_center i) hu') hp'
  have h2 : (⟨u, huL⟩ : L) * ⟨p, hpL⟩ = ⟨p, hpL⟩ * ⟨u, huL⟩ :=
    φ.injective (by rw [map_mul, map_mul]; exact h1)
  exact congrArg Subtype.val h2

theorem S_odd (h : FCHyp L K n φ t)
    (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) {i : Axis} (d : AxisData h i) :
    ¬ 2 ∣ (𝐒 : Subgroup G).relIndex 𝐍𝐂[i] := by
  have hf := closureSetupFacts h hbt i
  have hS := card_S_eq h hbt
  have h1 := Subgroup.relIndex_mul_card (H := (𝐒 : Subgroup G)) (K := 𝐍𝐂[i])
  rw [inf_of_le_left (S_le_NC h hbt i), hS] at h1
  have h2 := Subgroup.card_ker_mul_card_of_surjective d.surj
  have hker : Nat.card d.ρ.ker = Nat.card 𝐗[i] := by
    rw [d.ker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hf.NC_normal.1).toEquiv
  rw [hker, hf.card_X, Nat.card_prod, card_SL₂, h.setup.card_K] at h2
  have hodd : Odd ((2 ^ n) ^ 2 - 1) :=
    Common.odd_sq_pow_sub_one (f := n) (by have := h.setup.two_le; omega)
  have hm : (𝐒 : Subgroup G).relIndex 𝐍𝐂[i] = ((2 ^ n) ^ 2 - 1) ^ 2 := by
    refine Nat.eq_of_mul_eq_mul_right (by positivity : 0 < (2 ^ n) ^ 8) ?_
    rw [h1, ← h2]
    generalize (2 ^ n) ^ 2 - 1 = m
    ring
  rw [hm]
  exact (hodd.pow).not_two_dvd_nat

theorem X_inf_W (h : FCHyp L K n φ t)
    (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) (i : Axis) {x : G} (hx : x ∈ 𝐗[i])
    (hxc : x ∈ centralizer (𝐍𝐂[i] : Set G)) :
    x ∈ 𝐅 ⊓ centralizer (pull φ (axisTorus K i) : Set G) := by
  have hxS : x ∈ centralizer (𝐒 : Set G) :=
    centralizer_le (SetLike.coe_subset_coe.2 (S_le_NC h hbt i)) hxc
  have hxF : x ∈ 𝐅 := (BothTrivialHeisenberg.center_S h hbt).le (mem_center_map_iff.mpr
    ⟨X_le_S i hx, fun y hy => mem_centralizer_iff.mp hxS y hy⟩)
  have hw : 𝐰[i] ∈ 𝐍𝐂[i] := by
    have := sup_le_NC (φ := φ) (t := t) i (mem_sup_left (s_mem_CU h i (BothTrivialProductAxis.weylSL2 K)))
    rwa [BothTrivialProductAxis.sHom_weylSL2] at this
  have hxFw : x ∈ 𝐅.map (MulAut.conj 𝐰[i]⁻¹).toMonoidHom := by
    refine ⟨x, hxF, ?_⟩
    have hc := mem_centralizer_iff.1 hxc _ (inv_mem hw)
    show 𝐰[i]⁻¹ * x * 𝐰[i]⁻¹⁻¹ = x
    rw [hc]
    group
  exact F_inf_Fw h i ▸ mem_inf.2 ⟨hxF, hxFw⟩

theorem odd_card_axisTorus (h : FCHyp L K n φ t) (i : Axis) :
    Odd (Nat.card (pull φ (axisTorus K i))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hodd
  have h2 : 2 ∣ Nat.card (pull φ (axisTorus K i)) :=
    even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hodd)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hxJ : ((x : pull φ (axisTorus K i)) : G) ^ (Nat.card K - 1) = 1 :=
    torus_pow_card_sub_one (axisTorus_le_J0 i x.2)
  have h3 : orderOf ((x : pull φ (axisTorus K i)) : G) ∣ Nat.card K - 1 :=
    orderOf_dvd_of_pow_eq_one hxJ
  rw [Subgroup.orderOf_coe, hx] at h3
  exact (Nat.not_even_iff_odd.2 (odd_card_sub_one h)) (even_iff_two_dvd.2 h3)

theorem axisHyp (h : FCHyp L K n φ t)
    (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) {i : Axis} (d : AxisData h i) :
    CommonSylow.AxisHyp (d.diagData h hbt) 𝐒 (pull φ (antiUnipotent K))
      (pull φ (antiUnipotentCenter K)) (L ⊓ centralizer (𝐔[i] : Set G)) 𝐔[i]
      (𝐅 ⊓ centralizer (pull φ (axisTorus K i) : Set G)) (pull φ (axisTorus K i)) := by
  obtain ⟨hd₁, hd₂, hd₃⟩ := diagonal_eq_CU h hbt i d.ρ d.surj d.ker d.swap d.β d.rho_s d.le
    d.perfect d.sup_X d.comm d.max
  have hJ : pull φ (axisTorus K i) ≤ normalizer (pull φ (antiUnipotent K) : Set G) :=
    (axisTorus_le_J0 i).trans (OneAxisSecondAxis.J₀_le_normalizer_pull fun _ hδ _ ha =>
      OneAxisSecondAxis.diagTorus_conj_antiUnipotent hδ ha)
  exact
    { X_le_S := X_le_S i
      S_le_N := S_le_NC h hbt i
      S_odd := S_odd h hbt d
      Pm_le_CU := P_le_CU i
      U_le_Pm := pull_mono φ ((rootU_le_center i).trans antiUnipotentCenter_le)
      diag₁ := hd₁
      diag₂ := hd₂
      diag₃ := hd₃
      U_le_W := FullCenterTorus.U_le_W h i
      X_inf_W := fun x hx hxc => X_inf_W h hbt i hx hxc
      J_le_CU := J_le_CU i
      J_norm := fun j hj y hy => (mem_normalizer_iff.1 (hJ hj) y).1 hy
      J_odd := odd_card_axisTorus h i
      J_cent := CommonSylow.pull_inf_centralizer_le φ
        (ProductModel.antiUnipotent_inf_centralizer_axisTorus_le h.four_le_card i) }

theorem partner_normalizes (h : FCHyp L K n φ t)
    (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) {i : Axis} (d : AxisData h i) {y : G}
    (hyS : y ∈ normalizer (𝐒 : Set G)) (hyX : y ∈ normalizer (𝐗[i.swap] : Set G))
    (hy : Odd (orderOf y)) : y ∈ normalizer (d.P : Set G) :=
  CommonSylow.mem_normalizer_of_max d.perfect d.le d.max
    (mem_normalizer_prodFst_of_odd h hbt i d.ρ d.surj d.ker d.swap
      (mem_normalizer_X_of_mem_normalizer_S h hbt i d.ρ d.surj d.ker d.swap d.β d.rho_s d.le
        d.perfect d.sup_X d.comm d.max hyS hyX) hy)

theorem AxisData.sup_map_conj_eq (h : FCHyp L K n φ t)
    (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) {i : Axis} (d : AxisData h i) :
    d.P ⊔ d.P.map (MulAut.conj t).toMonoidHom = 𝐍𝐂[i] := by
  have hf := closureSetupFacts h hbt i
  have : Fintype K := Fintype.ofFinite K
  refine (axisHyp h hbt d).sup_conj_eq_N (sharedHyp h hbt) (q := 2 ^ n) (by positivity) ?_ ?_
    hf.card_X
  · intro B hB
    exact Common.card_le_of_isPGroup_SL2 (K := K) (by have := h.setup.two_le; omega)
      (by rw [← Nat.card_eq_fintype_card]; exact h.setup.card_K) hB
  · rw [card_pull, card_antiUnipotent h.setup.card_K]

theorem common_sylow (h : FCHyp L K n φ t)
    (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (d₁ : AxisData h Axis.one) (d₂ : AxisData h Axis.two) :
    d₁.P ⊓ d₁.P.map (MulAut.conj t).toMonoidHom = ⊥ ∧
      d₂.P ⊓ d₂.P.map (MulAut.conj t).toMonoidHom = ⊥ ∧
      (𝐒 ⊓ d₁.P = 𝐒 ⊓ d₂.P ∨ 𝐒 ⊓ d₁.P = 𝐒 ⊓ d₂.P.map (MulAut.conj t).toMonoidHom) := by
  refine CommonSylow.main_abstract (d₁.diagData h hbt) (d₂.diagData h hbt) (sharedHyp h hbt)
    (axisHyp h hbt d₁) (axisHyp h hbt d₂)
    (fun y hyS hyX hy => partner_normalizes h hbt d₂ hyS hyX hy)
    (fun y hyS hyX hy => partner_normalizes h hbt d₁ hyS hyX hy) (fun x h1 h2 => ?_)
  exact Subgroup.mem_bot.1 ((FullCenterTorus.W_inf_W h).le (mem_inf.2 ⟨h1, h2⟩))

end Setting

end BothTrivialProduct

end CFSG.LocalAnalysis.EvenBN.Sp4
