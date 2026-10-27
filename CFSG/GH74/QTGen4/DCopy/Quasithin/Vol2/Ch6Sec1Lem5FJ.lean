module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Lem5FG
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Lem5FJS432

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H : Subgroup G} {n : ℕ}

namespace Cx615C

theorem false_of_b56Case3_ch615_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4)
    (c : Cx615C G T M L V H n) (hU : IsElemAbelian 2 (UX615 T L H))
    (hN : ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G))
    (hF : ∀ F : Subgroup (MulAut (IntMod (UX615 T L H) hU)), B56FactorList ↥F →
      FactorFacts_ch615 F)
    (h3 : B56Case3 (ffJ (autI hU (borelL T L ⊔ H)))) : False := by
  classical
  obtain ⟨G₁, G₂, hsup, hinf, hcomm, hl₁, hl₂, W₁, W₂, -, -, -, -, -, hW, hp₁, hp₂⟩ := h3
  have hf₁ := hF G₁ hl₁
  have hf₂ := hF G₂ hl₂
  obtain ⟨D, hD⟩ := c.exists_hall_ch615
  have hc' : ∀ a ∈ G₂, ∀ b ∈ G₁, a * b = b * a := fun a ha b hb => (hcomm b hb a ha).symm
  have hinf' : G₂ ⊓ G₁ = ⊥ := by rw [inf_comm]; exact hinf
  have hXN : borelL T L ⊔ H ≤ Subgroup.normalizer (UX615 T L H : Set G) :=
    le_normalizer_conjClosure _ _
  have hTsX : autI hU T ≤ autI hU (borelL T L ⊔ H) := autI_mono hU (c.hH.1.1.trans le_sup_right)
  have hDsY : autI hU D ≤ autI hU (borelL T L ⊔ T) := autI_mono hU (hD.1.trans le_sup_left)
  have hYsX : autI hU (borelL T L ⊔ T) ≤ autI hU (borelL T L ⊔ H) :=
    autI_mono hU (sup_le le_sup_left (c.hH.1.1.trans le_sup_right))
  have hGsX : G₁ ⊔ G₂ ≤ autI hU (borelL T L ⊔ H) := hsup ▸ B6.ffJ_le _
  have hnorm : ∀ x ∈ autI hU (borelL T L ⊔ H),
      x ∈ Subgroup.normalizer ((G₁ ⊔ G₂ : Subgroup _) : Set (MulAut _)) := fun x hx =>
    hsup ▸ B6.le_normalizer_ffJ _ hx
  have hKG : autI hU (oTwoUpper H) ≤ G₁ ⊔ G₂ := hsup ▸ (c.le_ffJ_ch615 hU).2
  have hJG : autI hU (thompsonJ T) ≤ G₁ ⊔ G₂ := hsup ▸ (c.le_ffJ_ch615 hU).1
  have hDsodd : ∀ d ∈ autI hU D, Odd (orderOf d) := by
    have hodd : Odd (Nat.card (autI hU D)) := by
      rw [(c.autI_hall_ch615 hU hD).2, ← (c.hall_ch615 hD).2]
      exact hD.2.1
    exact fun d hd => Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard _ hd)
  have hGsn : ((G₁ ⊔ G₂).subgroupOf (autI hU (borelL T L ⊔ H))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hGsX).mpr fun x hx => hnorm x hx
  have hP : IsSylowTwoOf (autI hU T ⊓ (G₁ ⊔ G₂)) (G₁ ⊔ G₂) :=
    RankOneRecog.isSylowTwoOf_inf_of_subnormal (c.isSylowTwoOf_autI_ch615 hU) hGsX
      hGsn.isSubnormal
  have hn₁ : (G₁.subgroupOf (G₁ ⊔ G₂)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le_normalizer_ch615 hcomm)
  have hn₂ : (G₂.subgroupOf (G₁ ⊔ G₂)).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr ?_
    rw [sup_comm]
    exact sup_le_normalizer_ch615 hc'
  have hS : ∀ Gi : Subgroup (MulAut (IntMod (UX615 T L H) hU)), Gi ≤ G₁ ⊔ G₂ →
      (Gi.subgroupOf (G₁ ⊔ G₂)).Normal → IsSylowTwoOf (autI hU T ⊓ Gi) Gi := by
    intro Gi hGi hn
    have := RankOneRecog.isSylowTwoOf_inf_of_subnormal hP hGi hn.isSubnormal
    rwa [inf_assoc, inf_eq_right.mpr hGi] at this
  have hS₁ := hS G₁ le_sup_left hn₁
  have hS₂ := hS G₂ le_sup_right hn₂
  have hJsplit : autI hU (thompsonJ T) ≤ (autI hU T ⊓ G₁) ⊔ (autI hU T ⊓ G₂) := by
    exact ((le_inf (autI_mono hU (thompsonJ_le_self T)) hJG).trans
      (le_sup_inf_of_isSylowTwoOf_ch615 hcomm hinf hP)).trans
      (sup_le_sup (inf_le_inf_right _ inf_le_left) (inf_le_inf_right _ inf_le_left))
  have hTK : autI hU T ≤ Subgroup.normalizer (autI hU (oTwoUpper H) : Set (MulAut _)) := by
    have hTK' : T ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
      c.hH.1.1.trans (le_normalizer_oTwoUpper H)
    intro y hy
    refine Subgroup.mem_normalizer_iff.mpr fun a =>
      ⟨fun ha => C124.autI_conj_mem hU hTK' y hy a ha, fun ha => ?_⟩
    have := C124.autI_conj_mem hU hTK' y⁻¹ ((autI hU T).inv_mem hy) _ ha
    simpa [mul_assoc] using this
  have hsplit : autI hU (oTwoUpper H) ≤
      (autI hU (oTwoUpper H) ⊓ G₁) ⊔ (autI hU (oTwoUpper H) ⊓ G₂) :=
    (c.le_commutator_ch615 hU).trans (commutator_le_sup_inf_ch615 hcomm
      (P := autI hU T ⊓ (G₁ ⊔ G₂)) hKG ((le_inf (autI_mono hU (thompsonJ_le_self T)) hJG).trans
        (le_sup_inf_of_isSylowTwoOf_ch615 hcomm hinf hP)) (inf_le_left.trans hTK))
  have hcW : ∀ (Gi : Subgroup (MulAut (IntMod (UX615 T L H) hU))) (Wi C : Subgroup _),
      B56Piece Gi Wi C → commV Gi ≤ Wi := by
    intro Gi Wi C h
    rcases h with ⟨hWi, -⟩ | ⟨hWi, -⟩ | ⟨-, hle, -⟩
    · rw [hWi]; exact le_sup_left
    · rw [hWi]; exact le_sup_left
    · exact hle
  have hfix : ∀ (Gi Gj : Subgroup (MulAut (IntMod (UX615 T L H) hU))) (Wi Wj : Subgroup _),
      Gi ≤ G₁ ⊔ G₂ → Gj ≠ ⊥ → (∀ a ∈ Gi, ∀ b ∈ Gj, a * b = b * a) →
      commV Gi ≤ Wi → commV Gj ≤ Wj → Wi ⊓ Wj = fixV (G₁ ⊔ G₂) → fixV Gi ≠ ⊥ := by
    intro Gi Gj Wi Wj hGi hGj hcij hWi hWj hWij hb
    by_cases h0 : fixV (G₁ ⊔ G₂) = ⊥
    · apply commV_ne_bot_ch615 hGj
      rw [eq_bot_iff, ← hb]
      intro w hw g hg
      have h1 : g w * w⁻¹ ∈ commV Gi := Subgroup.subset_closure ⟨g, hg, w, rfl⟩
      have h2 : g w * w⁻¹ ∈ commV Gj :=
        (commV Gj).mul_mem (mem_commV_of_conj_ch615 (fun x hx => by
          rw [hcij g hg x hx, mul_inv_cancel_right]; exact hx) hw) ((commV Gj).inv_mem hw)
      have h3 : g w * w⁻¹ ∈ Wi ⊓ Wj := ⟨hWi h1, hWj h2⟩
      rw [hWij, h0, Subgroup.mem_bot, mul_inv_eq_one] at h3
      exact h3
    · apply h0
      rw [eq_bot_iff, ← hb]
      exact fun v hv x hx => hv x (hGi hx)
  rw [← hsup] at hW
  have hfix₁ := hfix G₁ G₂ W₁ W₂ le_sup_left hf₂.ne_bot hcomm (hcW _ _ _ hp₁) (hcW _ _ _ hp₂)
    (hsup ▸ hW)
  have hfix₂ := hfix G₂ G₁ W₂ W₁ le_sup_right hf₁.ne_bot hc' (hcW _ _ _ hp₂) (hcW _ _ _ hp₁)
    (by rw [inf_comm]; exact hsup ▸ hW)
  have hperm := fun x (hx : x ∈ autI hU (borelL T L ⊔ H)) => map_conj_eq_or_swap_ch615 hcomm hinf
    hf₁.center hf₂.center hf₁.indec hf₂.indec hf₁.ne_bot hf₂.ne_bot (hnorm x hx)
  have hodd : ∀ x ∈ autI hU (borelL T L ⊔ H), Odd (orderOf x) →
      x ∈ Subgroup.normalizer (G₁ : Set (MulAut _)) ∧
        x ∈ Subgroup.normalizer (G₂ : Set (MulAut _)) := by
    intro x hx hxo
    rcases hperm x hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨mem_normalizer_of_map_eq_ch615 h1, mem_normalizer_of_map_eq_ch615 h2⟩
    · have hx2 : ∀ (Gi Gj : Subgroup (MulAut (IntMod (UX615 T L H) hU))),
          Gi.map (MulAut.conj x).toMonoidHom = Gj → Gj.map (MulAut.conj x).toMonoidHom = Gi →
          x ^ 2 ∈ Subgroup.normalizer (Gi : Set (MulAut _)) := by
        intro Gi Gj hij hji
        refine mem_normalizer_of_conj_mem_l32_ch615 fun g hg => ?_
        have h1' : x * g * x⁻¹ ∈ Gj := by rw [← hij]; exact ⟨g, hg, rfl⟩
        have h2' : x * (x * g * x⁻¹) * x⁻¹ ∈ Gi := by rw [← hji]; exact ⟨_, h1', rfl⟩
        have e2 : x ^ 2 * g * (x ^ 2)⁻¹ = x * (x * g * x⁻¹) * x⁻¹ := by
          rw [pow_two, mul_inv_rev]
          group
        rw [e2]
        exact h2'
      obtain ⟨k, hk⟩ := hxo
      have ex : x = (x ^ 2) ^ (k + 1) := by
        rw [← pow_mul]
        calc x = x ^ orderOf x * x := by rw [pow_orderOf_eq_one, one_mul]
          _ = x ^ (2 * (k + 1)) := by rw [← pow_succ, hk]; ring_nf
      rw [ex]
      exact ⟨Subgroup.pow_mem _ (hx2 G₁ G₂ h1 h2) _, Subgroup.pow_mem _ (hx2 G₂ G₁ h2 h1) _⟩
  have hDs₁ : autI hU D ≤ Subgroup.normalizer (G₁ : Set (MulAut _)) := fun d hd =>
    (hodd d (hYsX (hDsY hd)) (hDsodd d hd)).1
  have hDs₂ : autI hU D ≤ Subgroup.normalizer (G₂ : Set (MulAut _)) := fun d hd =>
    (hodd d (hYsX (hDsY hd)) (hDsodd d hd)).2
  by_cases hsw : ∀ t ∈ autI hU T, G₁.map (MulAut.conj t).toMonoidHom = G₁
  ·
    have hTs₁ : autI hU T ≤ Subgroup.normalizer (G₁ : Set (MulAut _)) := fun t ht =>
      mem_normalizer_of_map_eq_ch615 (hsw t ht)
    have hTs₂ : autI hU T ≤ Subgroup.normalizer (G₂ : Set (MulAut _)) := fun t ht =>
      mem_normalizer_right_ch615 hcomm hf₁.center (hnorm t (hTsX ht)) (hTs₁ ht)
    have hor := c.le_or_le_ch615_F4 h331 hU (A := autI hU (oTwoUpper H) ⊓ G₁)
      (B := autI hU (oTwoUpper H) ⊓ G₂) inf_le_left inf_le_left
      (fun t ht => Subgroup.inf_normalizer_le_normalizer_inf ⟨hTK ht, hTs₁ ht⟩)
      (fun t ht => Subgroup.inf_normalizer_le_normalizer_inf ⟨hTK ht, hTs₂ ht⟩)
      (fun k hk => (mem_sup_iff_of_commute_ch615 (fun a ha b hb =>
        hcomm a (Subgroup.mem_inf.mp ha).2 b (Subgroup.mem_inf.mp hb).2)).mp (hsplit hk))
    have hKJ : ∀ (Gi Gj : Subgroup (MulAut (IntMod (UX615 T L H) hU))),
        (∀ a ∈ Gi, ∀ b ∈ Gj, a * b = b * a) →
        autI hU (thompsonJ T) ≤ (autI hU T ⊓ Gi) ⊔ (autI hU T ⊓ Gj) →
        autI hU (oTwoUpper H) ≤ Gi →
        autI hU (oTwoUpper H) ≤ ⁅autI hU (oTwoUpper H), autI hU T ⊓ Gi⁆ := by
      intro Gi Gj hcij hJij hKi
      refine (c.le_commutator_ch615 hU).trans (Subgroup.commutator_le.mpr fun k hk j hj => ?_)
      obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := (mem_sup_iff_of_commute_ch615 (fun a ha b hb =>
        hcij a (Subgroup.mem_inf.mp ha).2 b (Subgroup.mem_inf.mp hb).2)).mp (hJij hj)
      have hks : ⁅k, s₂⁆ = 1 := by
        rw [commutatorElement_def, hcij k (hKi hk) s₂ (Subgroup.mem_inf.mp hs₂).2]
        group
      have e : ⁅k, s₁ * s₂⁆ = ⁅k, s₁⁆ * (s₁ * ⁅k, s₂⁆ * s₁⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e, hks, mul_one, mul_inv_cancel, mul_one]
      exact Subgroup.commutator_mem_commutator hk hs₁
    rcases hor with h | h
    · have hK₁ : autI hU (oTwoUpper H) ≤ G₁ := h.trans inf_le_right
      exact c.false_of_le_factor_ch615_F4 h432 hU hN hD hf₁ hTs₁ hDs₁ hK₁ hS₁
        (hKJ G₁ G₂ hcomm hJsplit hK₁) hfix₁
    · have hK₂ : autI hU (oTwoUpper H) ≤ G₂ := h.trans inf_le_right
      exact c.false_of_le_factor_ch615_F4 h432 hU hN hD hf₂ hTs₂ hDs₂ hK₂ hS₂
        (hKJ G₂ G₁ hc' (by rw [sup_comm]; exact hJsplit) hK₂) hfix₂
  ·
    push Not at hsw
    obtain ⟨t, htT, htn⟩ := hsw
    rcases hperm t (hTsX htT) with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact htn h1
    · exact c.false_of_swap_ch615 hU hN hD hcomm hinf hf₁ htT h1 h2 hDs₁ hDs₂ hKG hsplit hS₁
        hJsplit

end Cx615C

end CFSG.Quasithin.H13
