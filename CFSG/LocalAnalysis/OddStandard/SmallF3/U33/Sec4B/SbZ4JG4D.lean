module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JG2A

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {NQ : Subgroup G} {N : Subgroup ↥NQ} [N.Normal] {t : G}

private lemma z4j_mem_cent_iff {Vc Vsub : Subgroup ↥NQ} {Vh K : Subgroup (↥NQ ⧸ N)}
    (hVc : Z4JLift N Vc Vh) (hVsub : Vsub ≤ Vc)
    (hK : Vh ⊓ centralizer ((Vsub.map (z4iπ N) : Subgroup (↥NQ ⧸ N)) : Set (↥NQ ⧸ N)) = K)
    {x₀ : ↥NQ} (hx₀ : x₀ ∈ Vc) :
    (x₀ : G) ∈ centralizer ((Vsub.map NQ.subtype : Subgroup G) : Set G) ↔
      z4iπ N x₀ ∈ K := by
  have hxVh : z4iπ N x₀ ∈ Vh := by
    rw [← hVc.map_eq]
    exact Subgroup.mem_map_of_mem (z4iπ N) hx₀
  rw [← hK, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx
    refine ⟨hxVh, ?_⟩
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hw
    have hv' : (v : G) ∈ Vsub.map NQ.subtype := Subgroup.mem_map_of_mem NQ.subtype hv
    have h := hx (v : G) hv'
    have hvx : v * x₀ = x₀ * v := Subtype.ext (by simpa using h)
    rw [← map_mul, ← map_mul, hvx]
  · intro hx
    intro g hg
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hg
    have h := hx.2 (z4iπ N v) (Subgroup.mem_map_of_mem (z4iπ N) hv)
    have hvx : v * x₀ = x₀ * v :=
      hVc.inj (Vc.mul_mem (hVsub hv) hx₀) (Vc.mul_mem hx₀ (hVsub hv))
        (by rw [map_mul, map_mul, h])
    simpa using congrArg (Subtype.val) hvx

theorem z4j_fusion_lift {Vc Vsub : Subgroup ↥NQ} {Vh Mc K : Subgroup (↥NQ ⧸ N)}
    (hVc : Z4JLift N Vc Vh) (hVsub : Vsub ≤ Vc) (hMc : Mc ≤ Vh)
    (hK : Vh ⊓ centralizer ((Vsub.map (z4iπ N) : Subgroup (↥NQ ⧸ N)) : Set (↥NQ ⧸ N)) = K)
    {σ : ↥NQ ⧸ N} (hσ : σ ∈ Vh) (hσ2 : σ * σ = 1) (hσK : σ ∉ K)
    {T : ↥NQ ⧸ N → Prop}
    (hT : ∀ a : ↥NQ, a * a = 1 → a ≠ 1 → (T (z4iπ N a) ↔ ∃ g : G, (a : G) = g * t * g⁻¹))
    (hTσ : T σ)
    (hfus : ∀ u ∈ Vh, u * u = 1 → T u → u ∉ K → ∃ w ∈ Mc, u = w * σ * w⁻¹)
    (hcard : Nat.card ↥(Vh ⊓ centralizer ({σ} : Set (↥NQ ⧸ N))) = 128) :
    ∃ s ∈ Vc.map NQ.subtype, s * s = 1 ∧
      s ∉ centralizer ((Vsub.map NQ.subtype : Subgroup G) : Set G) ∧
      (∃ g : G, s = g * t * g⁻¹) ∧
      (∀ x ∈ Vc.map NQ.subtype, x * x = 1 →
        x ∉ centralizer ((Vsub.map NQ.subtype : Subgroup G) : Set G) →
        (∃ g : G, x = g * t * g⁻¹) → ∃ w ∈ Vc.map NQ.subtype, x = w * s * w⁻¹) ∧
      Nat.card ↥(Vc.map NQ.subtype ⊓ centralizer ({s} : Set G)) = 128 := by
  obtain ⟨s₀, hs₀Vc, hs₀map⟩ := hVc.exists_lift hσ
  have hs₀2 : s₀ * s₀ = 1 :=
    hVc.mul_self_eq_one hs₀Vc (by rw [hs₀map]; exact hσ2)
  have hs₀1 : s₀ ≠ 1 := by
    intro h1
    apply hσK
    rw [← hs₀map, h1, map_one]
    exact K.one_mem
  have hs2 : (s₀ : G) * (s₀ : G) = 1 := by
    simpa using congrArg (Subtype.val) hs₀2
  have hscent : (s₀ : G) ∉ centralizer ((Vsub.map NQ.subtype : Subgroup G) : Set G) := by
    intro hc
    apply hσK
    rw [← hs₀map]
    exact (z4j_mem_cent_iff hVc hVsub hK hs₀Vc).mp hc
  have hsconj : ∃ g : G, (s₀ : G) = g * t * g⁻¹ :=
    (hT s₀ hs₀2 hs₀1).mp (by rw [hs₀map]; exact hTσ)
  have hfus' : ∀ x ∈ Vc.map NQ.subtype, x * x = 1 →
      x ∉ centralizer ((Vsub.map NQ.subtype : Subgroup G) : Set G) →
      (∃ g : G, x = g * t * g⁻¹) →
      ∃ w ∈ Vc.map NQ.subtype, x = w * (s₀ : G) * w⁻¹ := by
    intro x hxVg hx2 hxcent hxconj
    obtain ⟨x₀, hx₀Vc, rfl⟩ := Subgroup.mem_map.1 hxVg
    have hx02 : x₀ * x₀ = 1 := Subtype.ext (by simpa using hx2)
    have hx01 : x₀ ≠ 1 := by
      intro h1
      refine hxcent ?_
      rw [h1]
      exact (centralizer ((Vsub.map NQ.subtype : Subgroup G) : Set G)).one_mem
    have hTx : T (z4iπ N x₀) := (hT x₀ hx02 hx01).mpr hxconj
    have hxVh : z4iπ N x₀ ∈ Vh := by
      rw [← hVc.map_eq]
      exact Subgroup.mem_map_of_mem (z4iπ N) hx₀Vc
    have hxpi2 : z4iπ N x₀ * z4iπ N x₀ = 1 := by
      rw [← map_mul, hx02, map_one]
    have hxK : z4iπ N x₀ ∉ K := by
      intro hKmem
      exact hxcent ((z4j_mem_cent_iff hVc hVsub hK hx₀Vc).mpr hKmem)
    obtain ⟨w', hw'Mc, hw'conj⟩ := hfus (z4iπ N x₀) hxVh hxpi2 hTx hxK
    obtain ⟨w₀, hw₀Vc, hw₀map⟩ := hVc.exists_lift (hMc hw'Mc)
    have hconj0 : x₀ = w₀ * s₀ * w₀⁻¹ := by
      apply hVc.inj hx₀Vc (Vc.mul_mem (Vc.mul_mem hw₀Vc hs₀Vc) (Vc.inv_mem hw₀Vc))
      rw [map_mul, map_mul, map_inv, hw₀map, hs₀map, hw'conj]
    exact ⟨(w₀ : G), Subgroup.mem_map_of_mem NQ.subtype hw₀Vc,
      by simpa using congrArg (Subtype.val) hconj0⟩
  refine ⟨(s₀ : G), Subgroup.mem_map_of_mem NQ.subtype hs₀Vc, hs2, hscent, hsconj, hfus', ?_⟩
  have hmap : (Vc ⊓ centralizer ({s₀} : Set ↥NQ)).map NQ.subtype =
      Vc.map NQ.subtype ⊓ centralizer ({(s₀ : G)} : Set G) := by
    apply le_antisymm
    · intro y hy
      obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hy
      refine ⟨Subgroup.mem_map_of_mem NQ.subtype hc.1, ?_⟩
      have hcs : c * s₀ = s₀ * c := Subgroup.mem_centralizer_singleton_iff.1 hc.2
      exact Subgroup.mem_centralizer_singleton_iff.mpr (by simpa using congrArg (Subtype.val) hcs)
    · intro y hy
      obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hy.1
      refine Subgroup.mem_map_of_mem NQ.subtype ⟨hc, ?_⟩
      have hcomm : NQ.subtype c * (s₀ : G) = (s₀ : G) * NQ.subtype c :=
        Subgroup.mem_centralizer_singleton_iff.mp hy.2
      exact Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext (by simpa using hcomm))
  have hcardVc : Nat.card ↥(Vc ⊓ centralizer ({s₀} : Set ↥NQ)) = 128 := by
    rw [hVc.card_cent hs₀Vc, hs₀map, hcard]
  rw [← hmap, Subgroup.card_map_of_injective (K := Vc ⊓ centralizer ({s₀} : Set ↥NQ))
    NQ.subtype_injective]
  exact hcardVc

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
