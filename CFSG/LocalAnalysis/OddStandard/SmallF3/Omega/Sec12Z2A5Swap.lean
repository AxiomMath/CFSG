module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z2A5Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.Swap
public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.Out
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.Quasithin.EmptyFaithful.S14110AuxWreath

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.EvenSporadicStandard.SolomonRed

variable {Y : Type} [Group Y] {τ : Y}

private theorem commute_subtype {G : Type*} [Group G] {H K : Subgroup G}
    (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) (m : ↥H) (n : ↥K) :
    Commute (H.subtype m) (K.subtype n) :=
  hc m m.2 n n.2

private theorem mem_sup_of_commute {G : Type*} [Group G] {H K : Subgroup G}
    (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {x : G} (hx : x ∈ H ⊔ K) :
    ∃ h ∈ H, ∃ k ∈ K, x = h * k := by
  have hsup : H ⊔ K = (MonoidHom.noncommCoprod H.subtype K.subtype
      (commute_subtype hc)).range := by
    apply le_antisymm
    · refine sup_le (fun h hh => ⟨(⟨h, hh⟩, 1), ?_⟩) (fun k hk => ⟨(1, ⟨k, hk⟩), ?_⟩)
      · simp [MonoidHom.noncommCoprod_apply]
      · simp [MonoidHom.noncommCoprod_apply]
    · rintro _ ⟨⟨h, k⟩, rfl⟩
      rw [MonoidHom.noncommCoprod_apply]
      exact mul_mem (mem_sup_left h.2) (mem_sup_right k.2)
  rw [hsup] at hx
  obtain ⟨⟨h, k⟩, rfl⟩ := hx
  exact ⟨h, h.2, k, k.2, by simp [MonoidHom.noncommCoprod_apply]⟩

theorem outSq_alternatingGroup_five : OutSq (alternatingGroup (Fin 5)) := by
  intro α
  obtain ⟨σ, hσ⟩ :=
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by norm_num)
      (by norm_num)).2 α
  have hsq : σ * σ ∈ alternatingGroup (Fin 5) := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul]
    exact Int.units_mul_self _
  refine ⟨⟨σ * σ, hsq⟩, fun x => ?_⟩
  subst hσ
  apply Subtype.ext
  show (σ * ((σ * (x : Equiv.Perm (Fin 5)) * σ⁻¹)) * σ⁻¹) =
    (σ * σ) * x * (σ * σ)⁻¹
  group

theorem z2a5_swap_index [Finite Y] (h : Z2A5Hyp Y τ) (hZ : CFSG.Open.fusionZStar Y = ⊥)
    (e : ↥(centralizer ({τ} : Set Y)) ≃* Multiplicative (ZMod 2) × ↥(alternatingGroup (Fin 5)))
    {S₁ S₂ : Subgroup Y} (hs : SwapData Y τ (embA e).range S₁ S₂) :
    (CFSG.layer Y).index = 2 := by
  have hB := setting_of_equiv sec128_A5_noncomm h.1 hZ e
  have hne : τ ≠ 1 := hB.z_ne
  have hinj := embA_injective e
  have hBle : (embA e).range ≤ CFSG.layer Y := by
    rw [← hs.inf_eq]
    exact inf_le_left
  have hC : ∀ d ∈ centralizer ({τ} : Set Y), d ∈ normalizer (S₁ : Set Y) →
      d ∈ CFSG.layer Y := by
    intro d hd hdN
    rcases mem_range_or_mul sec128_A5_noncomm hne e hd with h1 | h1
    · exact hBle h1
    · exfalso
      have h2 : d * τ ∈ normalizer (S₁ : Set Y) :=
        CFSG.LocalCores.layer_le_normalizer hs.comp (hBle h1)
      have h3 : τ ∈ normalizer (S₁ : Set Y) := by
        have := mul_mem (inv_mem hdN) h2
        simpa using this
      exact hs.z_not_mem_normalizer h3
  let φ : ↥S₁ ≃* ↥(alternatingGroup (Fin 5)) :=
    hs.iso.some.trans (MonoidHom.ofInjective hinj).symm
  have hsq' : OutSq ↥S₁ := OutSq.of_mulEquiv φ.symm outSq_alternatingGroup_five
  have habel : OutAbel ↥S₁ := hsq'.abel
  have hall : ∀ y ∈ normalizer (S₁ : Set Y), y ∈ CFSG.layer Y :=
    hs.normalizer_le_layer hB hC (fun y₁ hy₁ y₂ hy₂ => outCond_one habel hy₁ hy₂)
      (fun y hy => outCond_two hsq' hy)
  exact hs.index_layer hB hall

theorem z2a5_swap [Finite Y] (h : Z2A5Hyp Y τ) (hZ : CFSG.Open.fusionZStar Y = ⊥)
    (e : ↥(centralizer ({τ} : Set Y)) ≃* Multiplicative (ZMod 2) × ↥(alternatingGroup (Fin 5)))
    {S₁ S₂ : Subgroup Y} (hs : SwapData Y τ (embA e).range S₁ S₂) : IsO4Plus4 Y := by
  have hB := setting_of_equiv sec128_A5_noncomm h.1 hZ e
  have hidx : (CFSG.layer Y).index = 2 := z2a5_swap_index h hZ e hs
  have hτ2 : τ * τ = 1 := z2a5_mul_self h
  have hτN : τ⁻¹ ∉ CFSG.layer Y := fun hh => hs.z_not_mem (inv_mem_iff.mp hh)
  have hS₂le : S₂ ≤ CFSG.layer Y := by
    rw [hs.layer_eq]
    exact le_sup_right
  have hdisj : ∀ x ∈ S₁, x ∈ S₂ → x = 1 := by
    intro x hx1 hx2
    have hx : x ∈ S₁ ⊓ S₂ := ⟨hx1, hx2⟩
    rwa [hs.disjoint hB, mem_bot] at hx
  have hcosets : ∀ m ∈ (⊤ : Subgroup Y),
      m ∈ CFSG.layer Y ∨ m * τ⁻¹ ∈ CFSG.layer Y := by
    intro m _
    by_cases hm : m ∈ CFSG.layer Y
    · exact Or.inl hm
    · exact Or.inr ((Subgroup.mul_mem_iff_of_index_two hidx (a := m) (b := τ⁻¹)).2
        (iff_of_false hm hτN))
  have hfact : ∀ n ∈ CFSG.layer Y, ∃ a ∈ S₁, ∃ b ∈ S₂, n = a * b := by
    intro n hn
    rw [hs.layer_eq] at hn
    exact mem_sup_of_commute hs.commute hn
  obtain ⟨w⟩ := CFSG.Quasithin.S14110.nonempty_mulEquiv_wreath (M := ⊤) (N := CFSG.layer Y)
    (M₁ := S₁) (M₂ := S₂) (s := τ) (D := ↥(alternatingGroup (Fin 5)))
    le_top (mem_top τ) hs.le_layer hS₂le hs.commute hdisj hτ2 hs.z_not_mem hcosets hfact
    (fun a ha => hs.conj_mem_S₂ ha) (fun b hb => hs.conj_mem_S₁ hB hb)
    (hs.iso.some.trans (MonoidHom.ofInjective (embA_injective e)).symm)
  exact ⟨Subgroup.topEquiv.symm.trans w⟩

end CFSG.OddStandard.SmallF3.Omega
