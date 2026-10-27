module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Model.Hmod
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeCongr

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Simple2S5

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

@[expose] noncomputable def pPrime : Subgroup (Equiv.Perm (Fin 1408)) := P1408 ⊓ blocks1408

theorem pPrime_le : pPrime ≤ P1408 := inf_le_left

section Cert


theorem relIndex_pPrime (hΛ : HSCtx) : pPrime.relIndex P1408 = 2 := by
  have hcomap : (pPrime.subgroupOf P1408).comap (hmod1408Equiv hΛ).toMonoidHom = hΛ.Emod := by
    ext x
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, pPrime, Subgroup.mem_inf,
      hmod1408Equiv_mem_Emod_iff]
    constructor
    · rintro ⟨-, hx⟩
      exact hx
    · intro hx
      exact ⟨(hmod1408Equiv hΛ x).2, hx⟩
  show (pPrime.subgroupOf P1408).index = 2
  rw [← Subgroup.index_comap_of_surjective (H := pPrime.subgroupOf P1408)
    (f := (hmod1408Equiv hΛ).toMonoidHom) (hmod1408Equiv hΛ).surjective,
    hcomap, hΛ.Emod_index]

theorem card_pPrime (hΛ : HSCtx) : Nat.card ↥pPrime = 88704000 := by
  have hcard : Nat.card ↥(pPrime.subgroupOf P1408) = Nat.card ↥pPrime :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe pPrime_le).toEquiv
  have hmul : Nat.card ↥(pPrime.subgroupOf P1408) * pPrime.relIndex P1408 = 177408000 := by
    rw [Subgroup.relIndex, Subgroup.card_mul_index, card_P1408 hΛ]
  rw [hcard, relIndex_pPrime hΛ] at hmul
  omega

end Cert

set_option maxRecDepth 10000

private theorem h1408BlockOK_parts' :
    (∀ i : Fin 6, (∀ k : ℕ, k < 704 → ap (h1408X i) k < 704) ∧
        (∀ k : ℕ, k < 704 → 704 ≤ ap (h1408X i) (704 + k))) ∧
      (∀ k : ℕ, k < 704 → ap h1408V k = 704 + k ∧ ap h1408V (704 + k) = k) := by
  have h := Certificates.certificate26760.2.2.2.2
  simp only [h1408BlockOK, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    List.mem_range, decide_eq_true_eq, beq_iff_eq, forall_const] at h
  exact h

private theorem rep_perm_apply_val {n : ℕ} {T : Table} {g : Equiv.Perm (Fin n)} (h : Rep n T g)
    (p : Fin n) : ap T p.val = (g p).val := by
  have hr := h p.val p.isLt
  rw [idx_of_lt g p.isLt, Equiv.Perm.smul_def] at hr
  exact hr

private theorem h1408VPerm_val_of_lt {p : Fin 1408}
    (hp : p.val < 704) : (h1408VPerm p).val = 704 + p.val := by
  have hb := h1408BlockOK_parts'.2 p.val hp
  rw [← rep_perm_apply_val rep_h1408V p, hb.1]

private theorem h1408VPerm_val_of_ge {p : Fin 1408}
    (hp : 704 ≤ p.val) : (h1408VPerm p).val = p.val - 704 := by
  have hk : p.val - 704 < 704 := by omega
  have hb := h1408BlockOK_parts'.2 (p.val - 704) hk
  rw [← rep_perm_apply_val rep_h1408V p, show p.val = 704 + (p.val - 704) by omega, hb.2]
  omega

private theorem h1408XPerm_mem_blocks (i : Fin 6) :
    h1408XPerm i ∈ blocks1408 := by
  intro v
  have hp : ap (h1408X i) v.val = (h1408XPerm i v).val := rep_perm_apply_val (rep_h1408X i).1 v
  have hblock := h1408BlockOK_parts'.1 i
  constructor
  · intro h
    by_contra hlt
    have hk : v.val - 704 < 704 := by omega
    have hc := hblock.2 (v.val - 704) hk
    rw [show 704 + (v.val - 704) = v.val by omega, hp] at hc
    omega
  · intro h
    have hc := hblock.1 v.val h
    rwa [hp] at hc

private theorem h1408VPerm_conj_mem_blocks
    {x : Equiv.Perm (Fin 1408)} (hx : x ∈ blocks1408) :
    h1408VPerm * x * h1408VPerm⁻¹ ∈ blocks1408 := by
  have hVinv : h1408VPerm⁻¹ = h1408VPerm := by
    rw [inv_eq_iff_mul_eq_one]
    exact h1408VPerm_mul_self
  have hbx : ∀ i : Fin 1408, (x i).val < 704 ↔ i.val < 704 := hx
  intro p
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hVinv]
  by_cases hp : p.val < 704
  · have hxq : ¬ (x (h1408VPerm p)).val < 704 := by
      intro h
      have hq := (hbx (h1408VPerm p)).mp h
      rw [h1408VPerm_val_of_lt hp] at hq
      omega
    have hge : 704 ≤ (x (h1408VPerm p)).val := by omega
    rw [h1408VPerm_val_of_ge hge]
    constructor <;> intro _ <;> omega
  · have hpge : 704 ≤ p.val := by omega
    have hq : (h1408VPerm p).val < 704 := by
      rw [h1408VPerm_val_of_ge hpge]
      omega
    have hxq : (x (h1408VPerm p)).val < 704 := (hbx _).mpr hq
    rw [h1408VPerm_val_of_lt hxq]
    constructor <;> intro h <;> omega

private theorem h1408VPerm_mem_normalizer_blocks :
    h1408VPerm ∈ Subgroup.normalizer (blocks1408 : Set (Equiv.Perm (Fin 1408))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact h1408VPerm_conj_mem_blocks
  · intro h
    have h' := h1408VPerm_conj_mem_blocks (x := h1408VPerm * x * h1408VPerm⁻¹) h
    have hVinv : h1408VPerm⁻¹ = h1408VPerm := by
      rw [inv_eq_iff_mul_eq_one]
      exact h1408VPerm_mul_self
    convert h' using 1
    rw [hVinv]
    symm
    calc h1408VPerm * (h1408VPerm * x * h1408VPerm) * h1408VPerm
        = (h1408VPerm * h1408VPerm) * x * (h1408VPerm * h1408VPerm) := by group
      _ = x := by rw [h1408VPerm_mul_self]; simp

private theorem P1408_le_normalizer_blocks :
    P1408 ≤ Subgroup.normalizer (blocks1408 : Set (Equiv.Perm (Fin 1408))) := by
  rw [P1408, Subgroup.closure_le]
  rintro _ ⟨j, rfl⟩
  rcases lt_or_eq_of_le (show j.val ≤ 6 by omega) with hlt | heq
  · have hj : j = Fin.castSucc (⟨j.val, hlt⟩ : Fin 6) := Fin.ext rfl
    rw [hj, h1408GenPerm_castSucc]
    exact Subgroup.le_normalizer (h1408XPerm_mem_blocks _)
  · have hj : j = 6 := Fin.ext (by simpa using heq)
    rw [hj, h1408GenPerm_last]
    exact h1408VPerm_mem_normalizer_blocks

section Cert26760


theorem conj_mem_pPrime (hΛ : HSCtx)
    {c x : Equiv.Perm (Fin 1408)} (hc : c ∈ P1408)
    (hx : x ∈ pPrime) : c * x * c⁻¹ ∈ pPrime := by
  have hx' := Subgroup.mem_inf.mp hx
  have hnorm : c ∈ Subgroup.normalizer (blocks1408 : Set (Equiv.Perm (Fin 1408))) :=
    P1408_le_normalizer_blocks hc
  have hb : c * x * c⁻¹ ∈ blocks1408 :=
    (Subgroup.mem_normalizer_iff.mp hnorm x).mp hx'.2
  exact Subgroup.mem_inf.mpr
    ⟨P1408.mul_mem (P1408.mul_mem hc hx'.1) (P1408.inv_mem hc), hb⟩

end Cert26760

structure Good (S : Subgroup (Equiv.Perm (Fin 1408))) (t : Equiv.Perm (Fin 1408)) : Prop where
  le : S ≤ P1408
  simple : IsSimpleGroup ↥S
  mem : t ∈ S
  sq : t * t = 1
  ne : t ≠ 1
  cover : IsNonsplitDoubleCoverOfS5 ↥(S ⊓ Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 1408))))

theorem Good.conj {S : Subgroup (Equiv.Perm (Fin 1408))} {t : Equiv.Perm (Fin 1408)}
    (h : Good S t) {c : Equiv.Perm (Fin 1408)} (hc : c ∈ P1408) :
    Good (S.map (MulAut.conj c).toMonoidHom) (c * t * c⁻¹) := by
  let φ : Equiv.Perm (Fin 1408) ≃* Equiv.Perm (Fin 1408) := MulAut.conj c
  have hφ : ∀ x : Equiv.Perm (Fin 1408), φ x = c * x * c⁻¹ := fun x => MulAut.conj_apply c x
  haveI : IsSimpleGroup ↥S := h.simple
  refine { le := ?_, simple := ?_, mem := ?_, sq := ?_, ne := ?_, cover := ?_ }
  · intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨s, hs, rfl⟩
    change φ s ∈ P1408
    rw [hφ]
    exact P1408.mul_mem (P1408.mul_mem hc (h.le hs)) (P1408.inv_mem hc)
  · exact (Subgroup.equivMapOfInjective S φ.toMonoidHom φ.injective).symm.isSimpleGroup
  · simpa [hφ] using Subgroup.mem_map_of_mem φ.toMonoidHom h.mem
  · calc c * t * c⁻¹ * (c * t * c⁻¹) = c * (t * t) * c⁻¹ := by group
      _ = 1 := by rw [h.sq]; simp
  · intro h1
    apply h.ne
    calc t = c⁻¹ * (c * t * c⁻¹) * c := by group
      _ = 1 := by rw [h1]; simp
  · have hmap : S.map φ.toMonoidHom ⊓
        Subgroup.centralizer ({c * t * c⁻¹} : Set (Equiv.Perm (Fin 1408))) =
        (S ⊓ Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 1408)))).map φ.toMonoidHom := by
      ext x
      constructor
      · rintro ⟨hxS, hxC⟩
        rcases Subgroup.mem_map.mp hxS with ⟨s, hs, rfl⟩
        have hcomm : φ s * (c * t * c⁻¹) = (c * t * c⁻¹) * φ s :=
          Subgroup.mem_centralizer_singleton_iff.mp hxC
        have hst : s * t = t * s := by
          apply φ.injective
          rw [map_mul, map_mul]
          rw [← hφ t] at hcomm
          exact hcomm
        exact Subgroup.mem_map.mpr
          ⟨s, ⟨hs, Subgroup.mem_centralizer_singleton_iff.mpr hst⟩, rfl⟩
      · rintro hx
        rcases Subgroup.mem_map.mp hx with ⟨s, ⟨hs, hsc⟩, rfl⟩
        refine ⟨Subgroup.mem_map_of_mem φ.toMonoidHom hs, ?_⟩
        change φ s ∈ Subgroup.centralizer ({c * t * c⁻¹} : Set (Equiv.Perm (Fin 1408)))
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hst : s * t = t * s := Subgroup.mem_centralizer_singleton_iff.mp hsc
        calc φ s * (c * t * c⁻¹) = φ s * φ t := by rw [← hφ t]
          _ = φ (s * t) := by rw [map_mul]
          _ = φ (t * s) := by rw [hst]
          _ = φ t * φ s := by rw [map_mul]
          _ = (c * t * c⁻¹) * φ s := by rw [← hφ t]
    have hequiv : ↥(S ⊓ Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 1408)))) ≃*
        ↥(S.map φ.toMonoidHom ⊓
          Subgroup.centralizer ({c * t * c⁻¹} : Set (Equiv.Perm (Fin 1408)))) :=
      (Subgroup.equivMapOfInjective
        (S ⊓ Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 1408))))
        φ.toMonoidHom φ.injective).trans (MulEquiv.subgroupCongr hmap.symm)
    exact IsNonsplitDoubleCoverOfS5.of_mulEquiv hequiv h.cover

end CFSG.EvenSporadicStandard.HNRecog.Simple2S5
