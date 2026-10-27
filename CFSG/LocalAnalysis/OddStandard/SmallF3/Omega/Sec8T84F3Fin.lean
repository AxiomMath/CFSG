module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F3Sy
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec8t84_factP_quot (hP : Sec8T84FactP) {A : Type} [Group A] [Finite A]
    {N V H P : Subgroup A} [N.Normal] [V.Normal] (hN : Odd (Nat.card N)) (hV : IsElemAb2 V 4)
    (hVN : ∀ v ∈ V, ∀ n ∈ N, v * n = n * v)
    (hA6 : ∃ φ : A →* alternatingGroup (Fin 6), Function.Surjective φ ∧ φ.ker = V ⊔ N)
    (hHN : H ⊓ (V ⊔ N) ≤ N) (hHsup : H ⊔ (V ⊔ N) = ⊤)
    (htrans : ∀ v ∈ V, v ≠ 1 → ∀ w ∈ V, w ≠ 1 → ∃ y : A, y * v * y⁻¹ = w)
    (hPs : IsSylow2Of P ⊤) :
    ∃ Fb : Subgroup (A ⧸ N), Sec8T84PFacts (A ⧸ N) (V.map (QuotientGroup.mk' N))
      (P.map (QuotientGroup.mk' N)) Fb := by
  obtain ⟨φ, hφsurj, hφker⟩ := hA6
  have hsurj : Function.Surjective (QuotientGroup.mk' N : A →* A ⧸ N) :=
    QuotientGroup.mk'_surjective N
  have hker : (QuotientGroup.mk' N : A →* A ⧸ N).ker = N := QuotientGroup.ker_mk' N
  have hVNbot : V ⊓ N = ⊥ := by
    refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
    rw [hV.2]
    exact (Nat.coprime_two_left.mpr hN).pow_left 4
  have hcardmap : Nat.card (V.map (QuotientGroup.mk' N)) = Nat.card V := by
    rw [← Subgroup.relIndex_ker (f := (QuotientGroup.mk' N : A →* A ⧸ N)) (K := V), hker]
    have hdisj : Disjoint N V := disjoint_iff.mpr (by rw [inf_comm]; exact hVNbot)
    show (N.subgroupOf V).index = Nat.card V
    rw [Subgroup.subgroupOf_eq_bot.mpr hdisj, Subgroup.index_bot]
  have hEab : IsElemAb2 (V.map (QuotientGroup.mk' N)) 4 :=
    ⟨CFSG.Open.IsElemAbelian.map hV.1 (QuotientGroup.mk' N), by rw [hcardmap, hV.2]⟩
  have hEnorm : (V.map (QuotientGroup.mk' N)).Normal :=
    Subgroup.Normal.map (inferInstance : V.Normal) (QuotientGroup.mk' N) hsurj
  have hEH : (V.map (QuotientGroup.mk' N)) ⊓ (H.map (QuotientGroup.mk' N)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    obtain ⟨hxV, hxH⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨v, hv, hvx⟩ := Subgroup.mem_map.mp hxV
    obtain ⟨h, hh, hhx⟩ := Subgroup.mem_map.mp hxH
    have hvn : v⁻¹ * h ∈ N := by
      have h1 : (QuotientGroup.mk' N : A →* A ⧸ N) (v⁻¹ * h) = 1 := by
        rw [map_mul, map_inv, hvx, hhx, inv_mul_cancel]
      rwa [← MonoidHom.mem_ker, hker] at h1
    have hhN : h ∈ N := by
      refine hHN (Subgroup.mem_inf.mpr ⟨hh, ?_⟩)
      have h2 : v * (v⁻¹ * h) = h := by group
      rw [← h2]
      exact Subgroup.mul_mem_sup hv hvn
    have hπh : (QuotientGroup.mk' N : A →* A ⧸ N) h = 1 := by
      rw [← MonoidHom.mem_ker, hker]; exact hhN
    rw [← hhx]; exact hπh
  have hNmap : N.map (QuotientGroup.mk' N) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, hker]
  have hEHsup : (V.map (QuotientGroup.mk' N)) ⊔ (H.map (QuotientGroup.mk' N)) = ⊤ := by
    have h1 : ((H ⊔ (V ⊔ N)).map (QuotientGroup.mk' N)) = ⊤ := by
      rw [hHsup, Subgroup.map_top_of_surjective _ hsurj]
    rw [Subgroup.map_sup, Subgroup.map_sup, hNmap] at h1
    rw [sup_comm]; simpa using h1
  have hNφ : N ≤ φ.ker := by rw [hφker]; exact le_sup_right
  let φb : A ⧸ N →* alternatingGroup (Fin 6) := QuotientGroup.lift N φ hNφ
  let ψ : ↥(H.map (QuotientGroup.mk' N)) →* alternatingGroup (Fin 6) :=
    φb.comp (H.map (QuotientGroup.mk' N)).subtype
  have hφb_apply (a : A) : φb ((QuotientGroup.mk' N) a) = φ a := rfl
  have hkerψ : ψ.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hx1 : ψ x = 1 := MonoidHom.mem_ker.mp hx
    obtain ⟨h, hh, hhx⟩ := Subgroup.mem_map.mp x.2
    have hxeq : (⟨(QuotientGroup.mk' N) h, Subgroup.mem_map_of_mem _ hh⟩ :
        ↥(H.map (QuotientGroup.mk' N))) = x := Subtype.ext hhx
    have hφh : φ h = 1 := by
      have h1 : ψ ⟨(QuotientGroup.mk' N) h, Subgroup.mem_map_of_mem _ hh⟩ = φ h :=
        hφb_apply h
      rw [hxeq] at h1
      rw [h1] at hx1
      exact hx1
    have hhN : h ∈ N := by
      refine hHN (Subgroup.mem_inf.mpr ⟨hh, ?_⟩)
      rw [← hφker]
      exact MonoidHom.mem_ker.mpr hφh
    have hπh : (QuotientGroup.mk' N) h = 1 := by
      rw [← MonoidHom.mem_ker, hker]; exact hhN
    exact Subtype.ext (by rw [← hhx]; exact hπh)
  have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp hkerψ
  have hsurjψ : Function.Surjective ψ := by
    intro y
    obtain ⟨a, ha⟩ := hφsurj y
    have ha_mem : a ∈ H ⊔ (V ⊔ N) := by rw [hHsup]; trivial
    obtain ⟨h, hh, c, hc, hca⟩ :=
      (Subgroup.mem_sup_of_normal_right (s := H) (t := V ⊔ N) (x := a)).mp ha_mem
    have hc_ker : φ c = 1 := MonoidHom.mem_ker.mp (by rw [hφker]; exact hc)
    refine ⟨⟨(QuotientGroup.mk' N) h, Subgroup.mem_map_of_mem _ hh⟩, ?_⟩
    have h1 : ψ ⟨(QuotientGroup.mk' N) h, Subgroup.mem_map_of_mem _ hh⟩ = φ h :=
      hφb_apply h
    rw [h1, ← ha, ← hca, map_mul, hc_ker, mul_one]
  have hHae6 : Nonempty (↥(H.map (QuotientGroup.mk' N)) ≃* alternatingGroup (Fin 6)) :=
    ⟨MulEquiv.ofBijective ψ ⟨hinj, hsurjψ⟩⟩
  have htrans' : ∀ a ∈ V.map (QuotientGroup.mk' N), a ≠ 1 →
      ∀ b ∈ V.map (QuotientGroup.mk' N), b ≠ 1 →
        ∃ h ∈ H.map (QuotientGroup.mk' N), h * a * h⁻¹ = b := by
    intro a ha ha1 b hb hb1
    obtain ⟨v, hv, hvx⟩ := Subgroup.mem_map.mp ha
    obtain ⟨w, hw, hwx⟩ := Subgroup.mem_map.mp hb
    have hv1 : v ≠ 1 := fun h1 => ha1 (by rw [← hvx, h1, map_one])
    have hw1 : w ≠ 1 := fun h1 => hb1 (by rw [← hwx, h1, map_one])
    obtain ⟨g, hg⟩ := htrans v hv hv1 w hw hw1
    have hg_mem : g ∈ H ⊔ (V ⊔ N) := by rw [hHsup]; trivial
    obtain ⟨h, hh, c, hc, hgc⟩ :=
      (Subgroup.mem_sup_of_normal_right (s := H) (t := V ⊔ N) (x := g)).mp hg_mem
    have hcent : V ⊔ N ≤ Subgroup.centralizer (V : Set A) :=
      sup_le (fun v hv => Subgroup.mem_centralizer_iff.mpr fun u hu =>
                CFSG.Open.IsElemAbelian.comm hV.1 hu hv)
             (fun n hn => Subgroup.mem_centralizer_iff.mpr fun v hv => hVN v hv n hn)
    have hcomm : c * v = v * c := (Subgroup.mem_centralizer_iff.mp (hcent hc) v hv).symm
    have hconj : h * v * h⁻¹ = w := by
      rw [← hg, ← hgc, mul_inv_rev]
      calc h * v * h⁻¹
          = h * (v * c) * (c⁻¹ * h⁻¹) := by group
        _ = h * (c * v) * (c⁻¹ * h⁻¹) := by rw [hcomm]
        _ = h * c * v * (c⁻¹ * h⁻¹) := by group
    refine ⟨(QuotientGroup.mk' N) h, Subgroup.mem_map_of_mem _ hh, ?_⟩
    have hq : (QuotientGroup.mk' N) h * a * ((QuotientGroup.mk' N) h)⁻¹
        = (QuotientGroup.mk' N) (h * v * h⁻¹) := by
      rw [← hvx, map_mul, map_mul, map_inv]
    rw [hq, hconj, hwx]
  have hPsyl : IsSylow2Of (P.map (QuotientGroup.mk' N)) ⊤ :=
    (sec8t84_sylow_map_quot N P hN hPs).2
  exact hP (A ⧸ N) (V.map (QuotientGroup.mk' N)) (H.map (QuotientGroup.mk' N))
    (P.map (QuotientGroup.mk' N)) hEab hEnorm hHae6 hEH hEHsup htrans' hPsyl

end CFSG.OddStandard.SmallF3.Omega
