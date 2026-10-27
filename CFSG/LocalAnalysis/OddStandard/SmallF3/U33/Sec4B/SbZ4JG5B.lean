module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutH74
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JG2A

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {NQ : Subgroup G} {N : Subgroup ↥NQ} [N.Normal] {t : G}

theorem z4j_gold_lift [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    {Vc : Subgroup ↥NQ} {Vh Qp : Subgroup (↥NQ ⧸ N)} (hVc : Z4JLift N Vc Vh) (hQp : Qp ≤ Vh)
    (hQp2 : Nat.card Vh = 2 * Nat.card Qp) (hVgi : ¬ 2 ∣ (Vc.map NQ.subtype).index)
    {T : ↥NQ ⧸ N → Prop}
    (hT : ∀ a : ↥NQ, a * a = 1 → a ≠ 1 → (T (z4iπ N a) ↔ ∃ g : G, (a : G) = g * t * g⁻¹))
    {σ : ↥NQ ⧸ N} (hσ : σ ∈ Vh) (hσQ : σ ∉ Qp) (hσ2 : σ * σ = 1) (hTσ : T σ)
    (hsyl : ∀ (g : G) (P : Subgroup G), IsPGroup 2 P →
      P ≤ centralizer ({g * t * g⁻¹} : Set G) →
      ¬ 2 ∣ P.relIndex (centralizer ({g * t * g⁻¹} : Set G)) → Nat.card P = 128) :
    ∃ β ∈ Qp, T β ∧ Nat.card ↥(Vh ⊓ centralizer ({β} : Set (↥NQ ⧸ N))) = 128 := by
  set Q' : Subgroup ↥NQ := Vc ⊓ Qp.comap (z4iπ N) with hQ'def
  have hQ'Vc : Q' ≤ Vc := inf_le_left
  have hQ'map : Q'.map (z4iπ N) = Qp := by
    rw [hQ'def]; exact hVc.map_sub hQp
  have hQ'card : Nat.card Q' = Nat.card Qp := by
    rw [hQ'def]; exact hVc.card_sub hQp
  set Vg : Subgroup G := Vc.map NQ.subtype with hVgdef
  set Q'g : Subgroup G := Q'.map NQ.subtype with hQ'gdef
  have hQ'gVg : Q'g ≤ Vg := by
    rw [hQ'gdef, hVgdef]; exact Subgroup.map_mono hQ'Vc
  have hVg2 : IsPGroup 2 Vg := by rw [hVgdef]; exact hVc.isPGroup.map _
  have hVgi' : ¬ 2 ∣ Vg.index := by rw [hVgdef]; exact hVgi
  have hcardQ'g : Nat.card Q'g = Nat.card Qp := by
    rw [hQ'gdef, Subgroup.card_map_of_injective NQ.subtype_injective, hQ'card]
  have hQ2 : Q'g.relIndex Vg = 2 := by
    have hcardVg : Nat.card Vg = 2 * Nat.card Q'g := by
      rw [hVgdef, Subgroup.card_map_of_injective NQ.subtype_injective, hVc.card_eq, hQp2,
        ← hcardQ'g]
    have hrel := Subgroup.relIndex_mul_card (H := Q'g) (K := Vg)
    rw [inf_of_le_left hQ'gVg, hcardVg] at hrel
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hrel
  obtain ⟨t₀, ht₀Vc, ht₀π⟩ := hVc.exists_lift hσ
  have ht₀2 : t₀ * t₀ = 1 := hVc.mul_self_eq_one ht₀Vc (by rw [ht₀π, hσ2])
  have ht₀1 : t₀ ≠ 1 := by
    intro h
    refine hσQ ?_
    rw [← ht₀π, h, map_one]
    exact Qp.one_mem
  have ht₀Q' : t₀ ∉ Q' := by
    intro h
    apply hσQ
    rw [← ht₀π, ← hQ'map]
    exact Subgroup.mem_map_of_mem (z4iπ N) h
  have ht₀gVg : (t₀ : G) ∈ Vg := by
    rw [hVgdef]; exact Subgroup.mem_map_of_mem NQ.subtype ht₀Vc
  have ht₀gQ'g : (t₀ : G) ∉ Q'g := by
    rw [hQ'gdef]
    rintro ⟨q, hq, hqeq⟩
    exact ht₀Q' (NQ.subtype_injective hqeq ▸ hq)
  have ht₀g2 : (t₀ : G) * (t₀ : G) = 1 := by
    have h := congrArg (fun z : ↥NQ => (z : G)) ht₀2
    simpa using h
  have ht₀conj : ∃ g₀ : G, (t₀ : G) = g₀ * t * g₀⁻¹ := by
    have hTt₀ : T (z4iπ N t₀) := by rw [ht₀π]; exact hTσ
    exact (hT t₀ ht₀2 ht₀1).mp hTt₀
  obtain ⟨w, hwQ'g, hwodd, -⟩ :=
    Outside.H74_of_simple hnab hVg2 hVgi' hQ'gVg hQ2 ht₀gVg ht₀gQ'g ht₀g2
  obtain ⟨b, hbQ', hbG₀⟩ := Subgroup.mem_map.mp hwQ'g
  have hbG : (b : G) = w * (t₀ : G) * w⁻¹ := hbG₀
  have hbQ : b ∈ Vc ⊓ Qp.comap (z4iπ N) := hQ'def ▸ hbQ'
  have hbVc : b ∈ Vc := hbQ.1
  have hbQp : z4iπ N b ∈ Qp := Subgroup.mem_comap.mp hbQ.2
  set β : ↥NQ ⧸ N := z4iπ N b with hβdef
  have hb2 : b * b = 1 := by
    apply NQ.subtype_injective
    change (b : G) * (b : G) = (1 : G)
    rw [hbG]
    rw [show (w * (t₀ : G) * w⁻¹) * (w * (t₀ : G) * w⁻¹)
        = w * ((t₀ : G) * (t₀ : G)) * w⁻¹ by group, ht₀g2]
    group
  have hb1 : b ≠ 1 := by
    intro h
    apply ht₀1
    apply NQ.subtype_injective
    have h1 : (t₀ : G) = w⁻¹ * (b : G) * w := by rw [hbG]; group
    rw [h] at h1
    simpa using h1
  have hbconj : ∃ g : G, (b : G) = g * t * g⁻¹ := by
    obtain ⟨g₀, hg₀⟩ := ht₀conj
    exact ⟨w * g₀, by rw [hbG, hg₀]; group⟩
  have hTβ : T β := by
    have h := (hT b hb2 hb1).mpr hbconj
    rwa [← hβdef] at h
  have hβQp : β ∈ Qp := by rw [hβdef]; exact hbQp
  have hcent : Nat.card ↥(Vc ⊓ centralizer ({b} : Set ↥NQ)) =
      Nat.card ↥(Vg ⊓ centralizer ({(b : G)} : Set G)) := by
    rw [hVgdef]
    have hmap : (Vc ⊓ centralizer ({b} : Set ↥NQ)).map NQ.subtype =
        Vc.map NQ.subtype ⊓ centralizer ({(b : G)} : Set G) := by
      apply le_antisymm
      · rintro x ⟨c, ⟨hcVc, hcc⟩, rfl⟩
        refine ⟨⟨c, hcVc, rfl⟩, ?_⟩
        have hcb : c * b = b * c := by
          have h := (Subgroup.mem_centralizer_iff).mp hcc
          exact (h b (by rfl)).symm
        exact Subgroup.mem_centralizer_singleton_iff.mpr (by
          simpa using congrArg (fun z : ↥NQ => (z : G)) hcb)
      · rintro x ⟨⟨c, hcVc, rfl⟩, hxc⟩
        refine ⟨c, ⟨hcVc, ?_⟩, rfl⟩
        refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
        exact NQ.subtype_injective (by
          have h := ((Subgroup.mem_centralizer_iff).mp hxc) ↑b (by rfl)
          simpa using h.symm)
    rw [← hmap, Subgroup.card_map_of_injective NQ.subtype_injective]
  have hπbcard : Nat.card ↥(Vh ⊓ centralizer ({β} : Set (↥NQ ⧸ N))) =
      Nat.card ↥(Vc ⊓ centralizer ({b} : Set ↥NQ)) := by
    have h := hVc.card_cent hbVc
    rw [← hβdef] at h
    exact h.symm
  have hodd : ¬ 2 ∣ (Vg ⊓ centralizer ({(b : G)} : Set G)).relIndex
      (centralizer ({(b : G)} : Set G)) := by
    rwa [← hbG] at hwodd
  have hP : IsPGroup 2 (Vg ⊓ centralizer ({(b : G)} : Set G) : Subgroup G) :=
    hVg2.to_inf_left
  obtain ⟨g₀, hg₀⟩ := ht₀conj
  have hbg : (b : G) = (w * g₀) * t * (w * g₀)⁻¹ := by
    rw [hbG, hg₀]; group
  have hPc : (Vg ⊓ centralizer ({(b : G)} : Set G)) ≤
      centralizer ({(w * g₀) * t * (w * g₀)⁻¹} : Set G) := by
    rw [← hbg]; exact inf_le_right
  have hPi : ¬ 2 ∣ (Vg ⊓ centralizer ({(b : G)} : Set G)).relIndex
      (centralizer ({(w * g₀) * t * (w * g₀)⁻¹} : Set G)) := by
    rw [← hbg]; exact hodd
  have h128 : Nat.card ↥(Vg ⊓ centralizer ({(b : G)} : Set G)) = 128 :=
    hsyl (w * g₀) _ hP hPc hPi
  exact ⟨β, hβQp, hTβ, by rw [hπbcard, hcent]; exact h128⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
