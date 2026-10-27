module

public import CFSG.LocalAnalysis.EvenSporadicStandard.ReeStd.ConjN
public import CFSG.LocalAnalysis.EvenSporadicStandard.ReeStd.SylowLe
import CFSG.LocalAnalysis.EvenSporadicStandard.J1.Count

public section

namespace CFSG.EvenSporadicStandard.ReeStd

open Subgroup CFSG.EvenSporadicStandard

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem relIndex_sup_right_of_le_normalizer {H K : Subgroup G}
    (hH : H ≤ normalizer (K : Set G)) : K.relIndex (H ⊔ K) = K.relIndex H := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hH
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hH
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient H K hH).toEquiv.symm

namespace LocalSetting

@[expose] def CZ (H : LocalSetting G) (S : Subgroup G) : Subgroup G :=
  centralizer ({H.z} : Set G) ⊓ normalizer (S : Set G)

@[expose] def DC (H : LocalSetting G) (S : Subgroup G) : Subgroup G :=
  centralizer (H.V : Set G) ⊓ normalizer (S : Set G)

@[expose] def RC (H : LocalSetting G) (S : Subgroup G) : Subgroup G :=
  centralizer (H.E : Set G) ⊓ normalizer (S : Set G)

variable {H : LocalSetting G} {S : Subgroup G}

theorem V_le_centralizer_V : H.V ≤ centralizer (H.V : Set G) := fun v hv =>
  Subgroup.mem_centralizer_iff.2 fun w hw => H.V_comm hw hv

theorem centralizer_V_le_centralizer_z : centralizer (H.V : Set G) ≤ centralizer ({H.z} : Set G) :=
  fun x hx => by
    rw [mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 hx H.z H.z_mem_V).symm

theorem centralizer_V_le_centralizer_E : centralizer (H.V : Set G) ≤ centralizer (H.E : Set G) :=
  Subgroup.centralizer_le H.E_le_V

theorem DC_le_CZ : H.DC S ≤ H.CZ S :=
  inf_le_inf_right _ centralizer_V_le_centralizer_z

theorem DC_le_RC : H.DC S ≤ H.RC S :=
  inf_le_inf_right _ centralizer_V_le_centralizer_E

theorem mem_DC_of_mem_CZ_of_mem_RC {x : G} (hC : x ∈ H.CZ S) (hR : x ∈ H.RC S) : x ∈ H.DC S := by
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 fun v hv => ?_, hC.2⟩
  have hxz : x * H.z = H.z * x := mem_centralizer_singleton_iff.1 hC.1
  have hxE := Subgroup.mem_centralizer_iff.1 hR.1
  rcases H.mem_V_iff'.1 hv with he | ⟨e, he, rfl⟩
  · exact hxE v he
  · have h1 := hxE e he
    calc e * H.z * x = e * (H.z * x) := by group
      _ = e * (x * H.z) := by rw [hxz]
      _ = (e * x) * H.z := by group
      _ = (x * e) * H.z := by rw [h1]
      _ = x * (e * H.z) := by group

end LocalSetting

namespace Stage

variable {H : LocalSetting G} {S Λ : Subgroup G} (h : Stage H S Λ)

include h in
theorem V_le_DC : H.V ≤ H.DC S :=
  le_inf LocalSetting.V_le_centralizer_V fun v hv => le_normalizer (h.V_le hv)

include h in
theorem DC_inf_S : H.DC S ⊓ S = H.V := by
  refine le_antisymm ?_ (le_inf h.V_le_DC h.V_le)
  exact H.le_V_of_isPGroup_of_le_centralizer_V (h.pgroup.to_le inf_le_right)
    (inf_le_left.trans inf_le_left)

include h in
theorem CZ_le_B : H.CZ S ≤ H.B := by
  rintro n ⟨hnC, hnN⟩
  refine H.mem_B_def.2 ⟨mem_normalizer_iff.2 fun v => ?_, hnC⟩
  rw [← h.centralizer_S]
  have hC := mem_normalizer_iff.1 (le_normalizer hnC : n ∈ normalizer
    ((centralizer ({H.z} : Set G) : Subgroup G) : Set G)) v
  have hN := mem_normalizer_iff.1 hnN v
  exact and_congr hC hN

include h in
theorem S_le_RC : S ≤ H.RC S := by
  intro s hs
  refine ⟨Subgroup.mem_centralizer_iff.2 fun e he => ?_, le_normalizer hs⟩
  rcases h.cover s hs with hsΛ | hsz
  · exact h.comm (h.E_le he) hsΛ
  · obtain ⟨t, htΛ, rfl⟩ : ∃ t ∈ Λ, s = t * H.z :=
      ⟨s * H.z, hsz, by rw [mul_assoc, H.z_mul_self, mul_one]⟩
    calc e * (t * H.z) = (e * t) * H.z := by group
      _ = (t * e) * H.z := by rw [h.comm (h.E_le he) htΛ]
      _ = t * (e * H.z) := by group
      _ = t * (H.z * e) := by rw [H.z_comm_E he]
      _ = t * H.z * e := by group

include h in
theorem card_CZ : Nat.card (H.CZ S) = 21 * Nat.card (H.DC S) := by
  let ρ : H.CZ S →* MulAut H.E := H.actB.comp (Subgroup.inclusion h.CZ_le_B)
  have hρ : ∀ (x : H.CZ S) (e : H.E), ((ρ x e : H.E) : G) = (x : G) * e * (x : G)⁻¹ :=
    fun x e => rfl
  have hker : ∀ x : H.CZ S, ρ x = 1 ↔ (x : G) ∈ H.DC S := by
    intro x
    constructor
    · intro h1
      refine LocalSetting.mem_DC_of_mem_CZ_of_mem_RC x.2 ⟨Subgroup.mem_centralizer_iff.2 fun e he => ?_,
        x.2.2⟩
      have h2 : (x : G) * e * (x : G)⁻¹ = e := by
        have := congrArg (fun α : MulAut H.E => ((α ⟨e, he⟩ : H.E) : G)) h1
        simpa [hρ] using this
      calc e * (x : G) = ((x : G) * e * (x : G)⁻¹) * (x : G) := by rw [h2]
        _ = (x : G) * e := by group
    · intro h1
      refine MulEquiv.ext fun e => Subtype.ext ?_
      rw [hρ]
      have := Subgroup.mem_centralizer_iff.1 h1.1 e (H.E_le_V e.2)
      calc (x : G) * e * (x : G)⁻¹ = (e * (x : G)) * (x : G)⁻¹ := by rw [this]
        _ = e := by group
  have hrange : ρ.range = H.actB.range := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, rfl⟩
      exact ⟨Subgroup.inclusion h.CZ_le_B x, rfl⟩
    · rintro _ ⟨b, rfl⟩
      obtain ⟨c, hc, hcb⟩ := h.cov b b.2
      refine ⟨⟨c, hc⟩, ?_⟩
      refine MulEquiv.ext fun e => Subtype.ext ?_
      rw [hρ]
      exact hcb e e.2
  have hkercard : Nat.card ρ.ker = Nat.card (H.DC S) :=
    Nat.card_congr ⟨fun x => ⟨(x.1 : G), (hker x.1).1 x.2⟩,
      fun d => ⟨⟨d.1, LocalSetting.DC_le_CZ d.2⟩, (hker ⟨d.1, LocalSetting.DC_le_CZ d.2⟩).2 d.2⟩,
      fun x => rfl, fun d => rfl⟩
  have h1 := Subgroup.card_ker_mul_card_range ρ
  rw [hkercard, hrange, H.card_range_B] at h1
  omega

include h in
theorem odd_relIndex_V_DC : Odd (H.V.relIndex (H.DC S)) := by
  obtain ⟨T, hTp, hVT, hTD, hTodd⟩ :=
    exists_isPGroup_le_odd_relIndex (A := H.DC S) (h.pgroup.to_le h.V_le) h.V_le_DC
  have hTV : T ≤ H.V := H.le_V_of_isPGroup_of_le_centralizer_V hTp (hTD.trans inf_le_left)
  rwa [le_antisymm hTV hVT] at hTodd

include h in
theorem card_DC : Nat.card (H.DC S) = H.V.relIndex (H.DC S) * 16 := by
  have h1 := Subgroup.relIndex_mul_card (H := H.V) (K := H.DC S)
  rw [inf_eq_left.2 h.V_le_DC, H.card_V] at h1
  rw [← h1]

include h in
theorem odd_relIndex_S_sup_DC : Odd (S.relIndex (H.DC S ⊔ S)) := by
  have hDN : H.DC S ≤ normalizer (S : Set G) := inf_le_right
  rw [relIndex_sup_right_of_le_normalizer hDN, ← inf_relIndex_right, inf_comm, h.DC_inf_S]
  exact h.odd_relIndex_V_DC

include h in
theorem card_sup_DC : Nat.card (H.DC S ⊔ S : Subgroup G) =
    Nat.card S * H.V.relIndex (H.DC S) := by
  have hDN : H.DC S ≤ normalizer (S : Set G) := inf_le_right
  have h1 := Subgroup.relIndex_mul_card (H := S) (K := H.DC S ⊔ S)
  rw [inf_eq_left.2 le_sup_right, relIndex_sup_right_of_le_normalizer hDN, ← inf_relIndex_right,
    inf_comm, h.DC_inf_S] at h1
  rw [← h1, mul_comm]

include h in
theorem le_S_of_isPGroup_of_le_sup_DC {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPY : P ≤ H.DC S ⊔ S) : P ≤ S := by
  have hDN : H.DC S ≤ normalizer (S : Set G) := inf_le_right
  have hN : (S.subgroupOf (H.DC S ⊔ S)).Normal :=
    Subgroup.normal_subgroupOf_sup_of_le_normalizer hDN
  exact CFSG.OddStandard.L2Ree.le_of_isPGroup_of_odd_relIndex hN h.odd_relIndex_S_sup_DC hPY hP

include h in
theorem card_N (hS : 2 ∣ S.index) :
    Nat.card (normalizer (S : Set G) : Subgroup G) = 21 * Nat.card Λ * Nat.card (H.DC S) := by
  have h1 := J1Std.card_eq_card_conjClass_mul (normalizer (S : Set G) : Subgroup G) H.z
  have h3 : centralizer ({H.z} : Set G) ⊓ (normalizer (S : Set G) : Subgroup G) = H.CZ S := rfl
  rw [h3, h.card_CZ] at h1
  have h2 : Nat.card {x : G // ∃ m ∈ (normalizer (S : Set G) : Subgroup G),
      x = m * H.z * m⁻¹} = Nat.card Λ := by
    refine Nat.card_congr ⟨fun x => ⟨H.z * x.1, ?_⟩, fun l => ⟨H.z * l.1, ?_⟩, ?_, ?_⟩
    · obtain ⟨m, hm, hx⟩ := x.2
      obtain ⟨hS', hΛ'⟩ := h.N_conj_z_mem hm
      rw [hx]
      exact h.z_mul_mem_Λ hS' hΛ'
    · obtain ⟨hzS, hzΛ⟩ := h.z_mul_mem l.2
      exact h.conj_N_eq hS hzS hzΛ
    · intro x
      apply Subtype.ext
      show H.z * (H.z * x.1) = x.1
      rw [← mul_assoc, H.z_mul_self, one_mul]
    · intro l
      apply Subtype.ext
      show H.z * (H.z * l.1) = l.1
      rw [← mul_assoc, H.z_mul_self, one_mul]
  rw [h2] at h1
  rw [h1]
  ring

end Stage

end CFSG.EvenSporadicStandard.ReeStd
