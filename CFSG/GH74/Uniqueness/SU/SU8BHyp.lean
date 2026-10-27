module

public import CFSG.GH74.Uniqueness.SU.SU8BFin
public import CFSG.GH74.Uniqueness.SU.SU8Syl

public section

namespace CFSG.GH74.Uniqueness.SU.SU8

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU8.Setup
  CFSG.GH74.Uniqueness.SU.SU8.Burn

section Hyp

variable {G : Type} [Group G] [Finite G] {z : G} {S L A : Subgroup G}

theorem Hyp20A.z_mem_S (hyp : Hyp20A z S L A) : z ∈ S := by
  obtain ⟨h, hhH, hhS⟩ := hyp.exists_conj_le
  have h1 := hhS z hyp.z_mem.1
  have h2 : z * h = h * z := Subgroup.mem_centralizer_iff.mp hhH z (Set.mem_singleton z)
  have h3 : h⁻¹ * z * h = z := by
    calc h⁻¹ * z * h = h⁻¹ * (z * h) := by group
      _ = h⁻¹ * (h * z) := by rw [h2]
      _ = z := by group
  rwa [h3] at h1

theorem Hyp20A.exists_sylow_le_H (hyp : Hyp20A z S L A) :
    ∃ P : Sylow 2 ↥(normalizer (A : Set G)),
      ∀ x ∈ (P : Subgroup ↥(normalizer (A : Set G))), (x : G) ∈ Hz z := by
  obtain ⟨T, hAT, hcl⟩ := hyp.A_strongly_closed
  have hSp : IsPGroup 2 ↥S := hyp.S_sylow.2.1
  have hSidx : ¬ 2 ∣ S.index := by
    have h1 : Odd (S.relIndex ⊤) := hyp.S_sylow.2.2
    rw [Subgroup.relIndex_top_right] at h1
    exact fun h2 => (Nat.not_even_iff_odd.mpr h1) (even_iff_two_dvd.mpr h2)
  let Ssyl : Sylow 2 G := hSp.toSylow hSidx
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq G Ssyl T
  have hTmem : ∀ x : G, x ∈ (T : Subgroup G) ↔ y⁻¹ * x * y ∈ S := fun x => by
    rw [← hy, mem_sylow_smul_iff]
    rfl
  have hSH : S ≤ Hz z := hyp.S_sylow_H.1
  have hzS : z ∈ S := hyp.z_mem_S
  have hz'T : y * z * y⁻¹ ∈ (T : Subgroup G) := by
    rw [hTmem]
    have : y⁻¹ * (y * z * y⁻¹) * y = z := by group
    rwa [this]
  have hz'c : ∀ t ∈ (T : Subgroup G), t * (y * z * y⁻¹) = (y * z * y⁻¹) * t := by
    intro t ht
    have h1 : y⁻¹ * t * y ∈ S := (hTmem t).mp ht
    have h2 : z * (y⁻¹ * t * y) = (y⁻¹ * t * y) * z :=
      Subgroup.mem_centralizer_iff.mp (hSH h1) z (Set.mem_singleton z)
    calc t * (y * z * y⁻¹) = y * (y⁻¹ * t * y) * z * y⁻¹ := by group
      _ = y * (z * (y⁻¹ * t * y)) * y⁻¹ := by rw [h2]; group
      _ = (y * z * y⁻¹) * t := by group
  have hAcomm : IsMulCommutative A := hyp.A_elem.1
  have hzT : Subgroup.zpowers z ≤ (T : Subgroup G) := by
    rw [Subgroup.zpowers_le]; exact hAT hyp.z_mem.1
  have hmapT : (Subgroup.zpowers z).map (MulAut.conj (y⁻¹)⁻¹).toMonoidHom ≤ (T : Subgroup G) := by
    rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
    simpa [MulAut.conj_apply] using hz'T
  obtain ⟨n, hnN, hn⟩ := CFSG.Goldschmidt.N4b G T A (Subgroup.zpowers z) y⁻¹ hAT hAcomm hcl hzT hmapT
  have hnz : n⁻¹ * z * n = y * z * y⁻¹ := by
    have := hn z (Subgroup.mem_zpowers z)
    simpa using this
  have hTN : (T : Subgroup G) ≤ normalizer (A : Set G) := fun s hs =>
    normalizer_le_of_strongly_closed hAT hcl (Subgroup.le_normalizer hs)
  have hTp : IsPGroup 2 ↥((T : Subgroup G).subgroupOf (normalizer (A : Set G))) :=
    T.isPGroup'.of_equiv (Subgroup.subgroupOfEquivOfLe hTN).symm
  have hTidx : ¬ 2 ∣ ((T : Subgroup G).subgroupOf (normalizer (A : Set G))).index := by
    intro h2
    have h3 : ((T : Subgroup G).relIndex (normalizer (A : Set G))) ∣ (T : Subgroup G).index :=
      Subgroup.relIndex_dvd_index_of_le hTN
    exact T.not_dvd_index (h2.trans h3)
  let Tn : Sylow 2 ↥(normalizer (A : Set G)) := hTp.toSylow hTidx
  refine ⟨(⟨n, hnN⟩ : ↥(normalizer (A : Set G))) • Tn, fun x hx => ?_⟩
  rw [mem_sylow_smul_iff] at hx
  have hxT : (n⁻¹ * (x : G) * n) ∈ (T : Subgroup G) := by
    have := Subgroup.mem_subgroupOf.mp hx
    simpa using this
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  rw [Set.mem_singleton_iff.mp hw]
  have hc := hz'c _ hxT
  rw [← hnz] at hc
  have hx' : (x : G) = n * (n⁻¹ * (x : G) * n) * n⁻¹ := by group
  have hz2 : z = n * (n⁻¹ * z * n) * n⁻¹ := by group
  calc z * (x : G) = n * ((n⁻¹ * z * n) * (n⁻¹ * (x : G) * n)) * n⁻¹ := by group
    _ = n * ((n⁻¹ * (x : G) * n) * (n⁻¹ * z * n)) * n⁻¹ := by rw [hc]
    _ = (x : G) * z := by group

theorem Hyp20A.odd_relIndex (hyp : Hyp20A z S L A) :
    Odd ((normalizer ((A ⊓ centralizerBar (Hz z) L : Subgroup G) : Set G)).relIndex
      (normalizer (A : Set G))) := by
  set N : Subgroup G := normalizer (A : Set G) with hN
  obtain ⟨P, hP⟩ := hyp.exists_sylow_le_H
  have hle : (P : Subgroup ↥N) ≤
      (normalizer ((A ⊓ centralizerBar (Hz z) L : Subgroup G) : Set G)).subgroupOf N := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    have hxH : (x : G) ∈ Hz z := hP x hx
    have hxA : (x : G) ∈ normalizer (A : Set G) := x.2
    rw [Subgroup.mem_normalizer_iff]
    intro v
    have hC : ∀ {w : G}, w ∈ centralizerBar (Hz z) L → (x : G) * w * (x : G)⁻¹ ∈ centralizerBar (Hz z) L :=
      fun hw => Lem203.conj_mem_centralizerBar hyp.L_normal hxH hw
    have hCinv : ∀ {w : G}, w ∈ centralizerBar (Hz z) L →
        (x : G)⁻¹ * w * (x : G) ∈ centralizerBar (Hz z) L := by
      intro w hw
      have := Lem203.conj_mem_centralizerBar hyp.L_normal ((Hz z).inv_mem hxH) hw
      simpa using this
    constructor
    · rintro ⟨hvA, hvC⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp hxA v).mp hvA, hC hvC⟩
    · rintro ⟨hvA, hvC⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp hxA v).mpr hvA, ?_⟩
      have h2 := hCinv hvC
      have e : (x : G)⁻¹ * ((x : G) * v * (x : G)⁻¹) * (x : G) = v := by group
      rwa [e] at h2
  have hdvd := Subgroup.index_dvd_of_le hle
  have hnd : ¬ 2 ∣ (P : Subgroup ↥N).index := P.not_dvd_index
  have hrel : ¬ 2 ∣ ((normalizer ((A ⊓ centralizerBar (Hz z) L : Subgroup G) : Set G)).relIndex N) :=
    fun h2 => hnd (h2.trans hdvd)
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hrel)

omit [Finite G] in
theorem Hyp20A.not_normal (hyp : Hyp20A z S L A)
    (hne : A ⊓ centralizerBar (Hz z) L ≠ A) :
    ¬ normalizer (A : Set G) ≤ normalizer ((A ⊓ centralizerBar (Hz z) L : Subgroup G) : Set G) := by
  intro h
  apply hne
  refine hyp.irreducible _ inf_le_left ?_ h
  intro hbot
  have hz := hyp.z_mem
  rw [hbot] at hz
  exact hyp.z_ne_one ((Subgroup.mem_bot).mp hz)

theorem Hyp20A.false_of_caseB (hyp : Hyp20A z S L A)
    (cb : CaseB L A (A ⊓ centralizerBar (Hz z) L) z) : False := by
  have hne : A ⊓ centralizerBar (Hz z) L ≠ A := by
    intro h
    have h1 := cb.card_A
    rw [h] at h1
    have : 0 < Nat.card A := Nat.card_pos
    omega
  exact CaseBCnt.final_false cb (fun g v hv hv1 hgv => hyp.TI hv hv1 hgv) (hyp.not_normal hne)
    hyp.odd_relIndex

end Hyp

end CFSG.GH74.Uniqueness.SU.SU8
