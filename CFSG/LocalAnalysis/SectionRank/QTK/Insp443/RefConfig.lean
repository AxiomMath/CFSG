module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.KConfig
public import CFSG.Quasithin.Vol2.KGFactC31Ident

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.Quasithin.KGC31

variable {K : Type} [Group K] {L V MK : Subgroup K}

theorem KConfig.map_mulEquiv {K' : Type} [Group K'] (h : KConfig K L V MK) (e : K ≃* K') :
    KConfig K' (L.map e.toMonoidHom) (V.map e.toMonoidHom) (MK.map e.toMonoidHom) where
  ne_bot := by
    intro hbot
    exact h.ne_bot ((Subgroup.map_eq_bot_iff_of_injective V e.injective).mp hbot)
  elemAbelian := h.elemAbelian.map e.toMonoidHom
  perfect := by
    have h1 := congrArg (Subgroup.map e.toMonoidHom) h.perfect
    rwa [Subgroup.map_commutator] at h1
  le_normalizer := by
    rw [← Subgroup.map_normalizer_eq_of_bijective V e.bijective]
    exact Subgroup.map_mono h.le_normalizer
  le_pCoreOf := by
    rw [CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 e L]
    exact Subgroup.map_mono h.le_pCoreOf
  pCoreOf_le := by
    rw [CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 e L]
    refine (Subgroup.map_mono h.pCoreOf_le).trans ?_
    simpa [Subgroup.coe_map] using
      Subgroup.map_centralizer_le_centralizer_image (V : Set K) e.toMonoidHom
  eq_commutator := by
    have h1 := congrArg (Subgroup.map e.toMonoidHom) h.eq_commutator
    rwa [Subgroup.map_commutator] at h1
  le_MK := Subgroup.map_mono h.le_MK
  MK_le_normalizer := by
    rw [← Subgroup.map_normalizer_eq_of_bijective L e.bijective]
    exact Subgroup.map_mono h.MK_le_normalizer
  MK_ne_top := by
    intro htop
    apply h.MK_ne_top
    ext x
    constructor
    · intro _; exact Subgroup.mem_top _
    · intro _
      have hx : e.toMonoidHom x ∈ MK.map e.toMonoidHom := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨m, hm, hme⟩ := hx
      exact (e.injective hme) ▸ hm
  normalizer_le := by
    intro Q' hQ'ne hQ'2 hInv
    set Q : Subgroup K := Q'.comap e.toMonoidHom with hQdef
    have hQne : Q ≠ ⊥ := by
      intro hbot
      apply hQ'ne
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨a, rfl⟩ := e.surjective x
      have ha : a ∈ Q := by
        simpa [hQdef] using hx
      rw [hbot] at ha
      rw [Subgroup.mem_bot] at ha ⊢
      exact (congrArg e.toMonoidHom ha).trans (map_one e.toMonoidHom)
    have hQ2 : IsPGroup 2 Q := hQ'2.comap_of_injective e.toMonoidHom e.injective
    have hInvQ : ∀ σ : K ≃* K, V.map σ.toMonoidHom = V → L.map σ.toMonoidHom = L →
        MK.map σ.toMonoidHom = MK → Q.map σ.toMonoidHom = Q := by
      intro σ hσV hσL hσMK
      let τ : K' ≃* K' := (e.symm.trans σ).trans e
      have hcomp : τ.toMonoidHom.comp e.toMonoidHom =
          e.toMonoidHom.comp σ.toMonoidHom := by
        ext x
        simp [τ]
      have hτV : (V.map e.toMonoidHom).map τ.toMonoidHom = V.map e.toMonoidHom := by
        rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hσV]
      have hτL : (L.map e.toMonoidHom).map τ.toMonoidHom = L.map e.toMonoidHom := by
        rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hσL]
      have hτMK : (MK.map e.toMonoidHom).map τ.toMonoidHom = MK.map e.toMonoidHom := by
        rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hσMK]
      have hQinv : Q.map σ.toMonoidHom = Q := by
        ext x
        constructor
        · rintro ⟨q, hq, rfl⟩
          have hq' : e.toMonoidHom q ∈ Q' := by
            simpa [hQdef] using hq
          have h1 : τ (e.toMonoidHom q) ∈ Q' := by
            have h2 : τ (e.toMonoidHom q) ∈ Q'.map τ.toMonoidHom :=
              Subgroup.mem_map_of_mem τ.toMonoidHom hq'
            rwa [hInv τ hτV hτL hτMK] at h2
          have h3 : e.toMonoidHom (σ q) = τ (e.toMonoidHom q) := by
            have h4 := congrArg (fun f : K →* K' => f q) hcomp
            simpa using h4.symm
          change e.toMonoidHom (σ q) ∈ Q'
          rw [h3]
          exact h1
        · intro hx
          have hx' : e.toMonoidHom x ∈ Q' := by
            simpa [hQdef] using hx
          refine ⟨σ.symm x, ?_, by simp⟩
          have h3 : e.toMonoidHom (σ.symm x) = τ.symm (e.toMonoidHom x) := by
            apply τ.injective
            have h4 := congrArg (fun f : K →* K' => f (σ.symm x)) hcomp
            simpa using h4
          have h2 : e.toMonoidHom x ∈ Q'.map τ.toMonoidHom := by
            rwa [hInv τ hτV hτL hτMK]
          obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp h2
          have hz' : τ.symm (e.toMonoidHom x) = z := by
            rw [← hzx]
            simp
          change e.toMonoidHom (σ.symm x) ∈ Q'
          rw [h3]
          exact hz' ▸ hz
      exact hQinv
    intro x hx
    obtain ⟨a, rfl⟩ := e.surjective x
    have ha : a ∈ Subgroup.normalizer (Q : Set K) := by
      rw [Subgroup.mem_normalizer_iff]
      intro q
      have hq := Subgroup.mem_normalizer_iff.mp hx (e.toMonoidHom q)
      simpa [hQdef] using hq
    exact Subgroup.mem_map_of_mem e.toMonoidHom (h.normalizer_le Q hQne hQ2 hInvQ ha)

end CFSG.SectionRank.QTK.Insp443

namespace CFSG.Quasithin.KGC31

theorem _root_.CFSG.Quasithin.KGC31.RefData.map_mulEquiv {G₀ G₁ : Type} [Group G₀] [Group G₁]
    {U M' : Subgroup G₀} (h : CFSG.Quasithin.KGC31.RefData U M') (e : G₀ ≃* G₁) :
    CFSG.Quasithin.KGC31.RefData (U.map e.toMonoidHom) (M'.map e.toMonoidHom) where
  cent := by
    intro x hx
    obtain ⟨a, rfl⟩ := e.surjective x
    have ha : a ∈ Subgroup.centralizer (U : Set G₀) := by
      rw [Subgroup.mem_centralizer_iff] at hx ⊢
      intro u hu
      apply e.injective
      rw [map_mul, map_mul]
      exact hx (e.toMonoidHom u) (Subgroup.mem_map_of_mem e.toMonoidHom hu)
    exact Subgroup.mem_map_of_mem e.toMonoidHom (h.cent ha)
  comm := by
    rintro a ⟨a', ha', rfl⟩ b ⟨b', hb', rfl⟩
    rw [← map_mul, ← map_mul, h.comm a' ha' b' hb']
  le := Subgroup.map_mono h.le
  norm := by
    intro m hm
    obtain ⟨m', hm', rfl⟩ := hm
    rw [Subgroup.mem_normalizer_iff]
    intro u
    have hmem : ∀ z : G₁, z ∈ U.map e.toMonoidHom ↔ e.symm z ∈ U := by
      intro z
      constructor
      · rintro ⟨u', hu', rfl⟩
        simpa using hu'
      · intro hz
        simpa using Subgroup.mem_map_of_mem e.toMonoidHom hz
    rw [hmem u, hmem (e.toMonoidHom m' * u * (e.toMonoidHom m')⁻¹)]
    simpa [map_mul, map_inv] using (Subgroup.mem_normalizer_iff.mp (h.norm hm') (e.symm u))
  perf := by
    intro K hKN hK
    set K' : Subgroup G₀ := K.comap e.toMonoidHom with hK'def
    have hmem : ∀ z : G₀, e.toMonoidHom z ∈ U.map e.toMonoidHom ↔ z ∈ U := by
      intro z
      constructor
      · rintro ⟨u', hu', h⟩
        exact (e.injective h) ▸ hu'
      · intro hz
        exact Subgroup.mem_map_of_mem e.toMonoidHom hz
    have hK'N : K' ≤ Subgroup.normalizer (U : Set G₀) := by
      intro k hk
      have hkK : e.toMonoidHom k ∈ K := by
        simpa only [hK'def, Subgroup.mem_comap] using hk
      rw [Subgroup.mem_normalizer_iff]
      intro u
      have hiff := Subgroup.mem_normalizer_iff.mp (hKN hkK) (e.toMonoidHom u)
      rw [← hmem u, ← hmem (k * u * k⁻¹)]
      simpa [map_mul, map_inv] using hiff
    have hK'perf : ⁅K', K'⁆ = K' := by
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      rw [Subgroup.map_commutator, hK'def, Subgroup.map_comap_eq,
        MonoidHom.range_eq_top.mpr e.surjective, top_inf_eq, hK]
    have hKmap : K'.map e.toMonoidHom = K := by
      rw [hK'def, Subgroup.map_comap_eq,
        MonoidHom.range_eq_top.mpr e.surjective, top_inf_eq]
    rw [← hKmap]
    exact Subgroup.map_mono (h.perf K' hK'N hK'perf)
  simple := by
    intro K hUK hKM hMK
    set K' : Subgroup G₀ := K.comap e.toMonoidHom with hK'def
    have hUK' : U ≤ K' := by
      intro u hu
      have h1 : e.toMonoidHom u ∈ K := hUK (Subgroup.mem_map_of_mem e.toMonoidHom hu)
      simpa only [hK'def, Subgroup.mem_comap] using h1
    have hK'M' : K' ≤ M' := by
      intro k hk
      have hkK : e.toMonoidHom k ∈ K := by
        simpa only [hK'def, Subgroup.mem_comap] using hk
      obtain ⟨m, hm, hme⟩ := hKM hkK
      exact (e.injective hme) ▸ hm
    have hM'K' : M' ≤ Subgroup.normalizer (K' : Set G₀) := by
      intro m hm
      rw [Subgroup.mem_normalizer_iff]
      intro k
      have hmK : e.toMonoidHom m ∈ M'.map e.toMonoidHom :=
        Subgroup.mem_map_of_mem e.toMonoidHom hm
      have hiff := Subgroup.mem_normalizer_iff.mp (hMK hmK) (e.toMonoidHom k)
      rw [hK'def, Subgroup.mem_comap]
      simpa [map_mul, map_inv] using hiff
    have hKmap : K'.map e.toMonoidHom = K := by
      rw [hK'def, Subgroup.map_comap_eq,
        MonoidHom.range_eq_top.mpr e.surjective, top_inf_eq]
    rcases h.simple K' hUK' hK'M' hM'K' with hcase | hcase
    · left
      rw [← hKmap, hcase]
    · right
      rw [← hKmap, hcase]

end CFSG.Quasithin.KGC31

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.Quasithin.KGC31

variable {K : Type} [Group K] {L V MK : Subgroup K}

theorem KConfig.eq_of_refData_of_le [Finite K] (h : KConfig K L V MK) {U M' : Subgroup K}
    (hd : CFSG.Quasithin.KGC31.RefData U M') (hUV : U ≤ V) : V = U ∧ L = M' := by
  have hC : Subgroup.centralizer (V : Set K) ≤ U :=
    (Subgroup.centralizer_le hUV).trans hd.cent
  have hOU : pCoreOf 2 L ≤ U := h.pCoreOf_le.trans hC
  have hVU : V ≤ U := h.le_pCoreOf.trans hOU
  have hVeq : V = U := le_antisymm hVU hUV
  have hUO : U ≤ pCoreOf 2 L := hVeq ▸ h.le_pCoreOf
  have hOeq : pCoreOf 2 L = U := le_antisymm hOU hUO
  have hUL : U ≤ L := hOeq ▸ CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hLN : L ≤ Subgroup.normalizer (U : Set K) := by
    rw [← hVeq]
    exact h.le_normalizer
  have hLM' : L ≤ M' := hd.perf L hLN h.perfect
  have hM'N : M' ≤ Subgroup.normalizer (V : Set K) := by
    rw [hVeq]
    exact hd.norm
  have hM'NL : M' ≤ Subgroup.normalizer (L : Set K) :=
    hM'N.trans (h.normalizer_le_MK.trans h.MK_le_normalizer)
  rcases hd.simple L hUL hLM' hM'NL with hLU | hLM'
  · have hLbot : L = ⊥ := by
      rw [← h.perfect, hLU, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact (hd.comm x hx z hz).symm
    have hVbot : V = ⊥ := by
      rw [h.eq_commutator, hLbot, Subgroup.commutator_bot_right]
    exact absurd hVbot h.ne_bot
  · exact ⟨hVeq, hLM'⟩

theorem KConfig.eq_of_refData [Finite K] (h : KConfig K L V MK) {U M' : Subgroup K}
    (hd : CFSG.Quasithin.KGC31.RefData U M') {y t : K} (hy : y ∈ L) (ht : t ∈ V)
    (hU : CFSG.Quasithin.KGC31.orbSub y t = U) : V = U ∧ L = M' :=
  h.eq_of_refData_of_le hd (hU ▸ orbSub_le (h.le_normalizer hy) ht)

end CFSG.SectionRank.QTK.Insp443

end
