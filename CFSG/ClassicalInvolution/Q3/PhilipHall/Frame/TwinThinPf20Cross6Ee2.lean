module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf20Cross6Ee

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

set_option linter.unusedSectionVars false

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

namespace TwinThin

local notation "gCentMembers" => CFSG.ClassicalInvolution.Generic.centMembers
local notation "gCentLayer" => CFSG.ClassicalInvolution.Generic.centLayer

variable {G : Type} [Group G] [Finite G] {K₀ K K' : Subgroup G} {z : G} {π : Set (Subgroup G)}
  {g : G}

namespace Setting

variable (S : Setting K₀ K K' z π g)
include S

theorem exists_vector_six (htw : S.TwinLab 6)
    (J : AEIdent (fam K (conjSub g (piGen π))) 6) (hsec : SecYu K₀ K K' z π g) :
    ∀ J' ∈ π, ∀ t : G, IsUniqueInvolution J' t →
      ∃ w : Wr 6, Cross.InducedBy J t w ∧ w.perm = 1 := by
  classical
  have hm5 : 5 ≤ 6 := by norm_num
  have hm8 : (6 : ℕ) ≠ 8 := by norm_num
  have hAut := Cross.aeAut_of_five_le hm5
  have hcov := S.aeCoverHyp hm5 hm8 J
  obtain ⟨α, h, b, hlab⟩ := J.label K S.mem_fam_self
  obtain ⟨u, a, c, ha, hc, hac, hpair, huX, hu', hφu⟩ := S.exists_pairInv hm5 htw J hlab
  obtain ⟨-, hS2, kY, hk5, ⟨Ju⟩⟩ := hsec u hpair
  intro J' hJ' t ht
  obtain ⟨w, hw, hfix⟩ := S.exists_induced_fix hm5 hAut htw J hJ' ht hlab
  refine ⟨w, hw, ?_⟩
  by_contra hσ
  obtain ⟨U, hUdef⟩ : ∃ U : Finset (Fin 6), U = ({a, c} : Finset (Fin 6))ᶜ := ⟨_, rfl⟩
  have hU4 : U.card = 4 := by
    rw [hUdef, Finset.card_compl, Fintype.card_fin, Finset.card_pair hac]
  have hmemU : ∀ x, x ∈ U ↔ x ≠ a ∧ x ≠ c := by
    intro x
    simp [hUdef]
  have haU : a ∉ U := fun hh => ((hmemU a).mp hh).1 rfl
  have hcU : c ∉ U := fun hh => ((hmemU c).mp hh).2 rfl
  have hrange : ∀ x, x ∈ Set.range (AE.emb U hU4) ↔ x ∈ U := fun x => by
    rw [AE.range_emb]; exact Finset.mem_coe
  have hp : ∀ x, x ∈ U ↔ w.perm x ∈ U := by
    intro x
    rw [hmemU, hmemU]
    have h1 : w.perm x = a ↔ x = a := by
      constructor
      · intro hh
        exact w.perm.injective (hh.trans (hfix a ha).symm)
      · rintro rfl
        exact hfix _ ha
    have h2 : w.perm x = c ↔ x = c := by
      constructor
      · intro hh
        exact w.perm.injective (hh.trans (hfix c hc).symm)
      · rintro rfl
        exact hfix _ hc
    simp only [ne_eq, h1, h2]
  obtain ⟨b₀, c₁, hwdec, hc₁⟩ := TwinThinPf10.exists_decomp (AE.emb U hU4) w
    (fun x => by rw [hrange, hrange]; exact hp x)
  have hbperm : ∀ i, (AE.emb U hU4) (b₀.perm i) = w.perm ((AE.emb U hU4) i) := by
    intro i
    have h1 : w.perm = c₁.perm * (embed (AE.emb U hU4) b₀).perm := by
      rw [hwdec]; rfl
    rw [h1]
    show (AE.emb U hU4) (b₀.perm i) =
      c₁.perm (embedPerm (AE.emb U hU4) b₀.perm ((AE.emb U hU4) i))
    rw [embedPerm_apply]
    exact ((hc₁ ((AE.emb U hU4) (b₀.perm i)) (not_not.mpr ⟨_, rfl⟩)).2).symm
  have hconjw := TwinThinPf10.conj_embed (AE.emb U hU4) hwdec hc₁
  obtain ⟨d, hdα, hda, hdc⟩ : ∃ d ∈ α, d ≠ a ∧ d ≠ c := by
    have hlt : ({a, c} : Finset (Fin 6)).card < α.card :=
      lt_of_le_of_lt Finset.card_le_two (by omega)
    obtain ⟨d, hdα, hd⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd
    exact ⟨d, hdα, hd.1, hd.2⟩
  obtain ⟨i₀, hi₀⟩ : ∃ i, (AE.emb U hU4) i = d := (hrange d).mpr ((hmemU d).mpr ⟨hda, hdc⟩)
  have hfixi : b₀.perm i₀ = i₀ := by
    apply (AE.emb U hU4).injective
    rw [hbperm, hi₀, hfix d hdα]
  have hb₀1 : b₀.perm ≠ 1 := by
    intro hb1
    apply hσ
    refine Equiv.ext fun x => ?_
    by_cases hxU : x ∈ U
    · obtain ⟨i, rfl⟩ := (hrange x).mpr hxU
      rw [← hbperm, hb1]
      rfl
    · have : x = a ∨ x = c := by
        by_contra hcon
        push Not at hcon
        exact hxU ((hmemU x).mpr hcon)
      rcases this with rfl | rfl
      · exact hfix _ ha
      · exact hfix _ hc
  have hb₀d : b₀.perm ≠ d₁ ∧ b₀.perm ≠ d₂ ∧ b₀.perm ≠ d₃ := by
    refine ⟨fun hh => ?_, fun hh => ?_, fun hh => ?_⟩
    · exact TwinThinPf20.d_no_fixed _ (Or.inl hh) i₀ hfixi
    · exact TwinThinPf20.d_no_fixed _ (Or.inr (Or.inl hh)) i₀ hfixi
    · exact TwinThinPf20.d_no_fixed _ (Or.inr (Or.inr hh)) i₀ hfixi
  obtain ⟨k, hk, hnc⟩ := TwinThinPf20.exists_noncomm_perm b₀.perm hb₀1 hb₀d.1 hb₀d.2.1 hb₀d.2.2
  obtain ⟨Lp, hLp, hlabp⟩ := J.label_surj U hU4 true
  obtain ⟨Lm, hLm, hlabm⟩ := J.label_surj U hU4 false
  have hPp := S.mem_centMembers_of_label hm5 J hu' hac hφu hLp hlabp haU hcU
  have hPm := S.mem_centMembers_of_label hm5 J hu' hac hφu hLm hlabm haU hcU
  have hxmem : AE.mkQ 6 (embed (AE.emb U hU4) k) ∈
      (Lp.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ := by
    rw [hlabp]
    exact TwinThinPf10.mkQ_embed_mem_true U hU4 hk
  obtain ⟨x, hx, hφx⟩ := J.exists_of_mem_map hLp hxmem
  obtain ⟨zL, hzp, -⟩ := TL4.AECov.exists_isUniqueInvolution J hm5 hLp
    (S.card8 _ (S.fam_mem hLp)) hlabp
  obtain ⟨zm, hzm, -⟩ := TL4.AECov.exists_isUniqueInvolution J hm5 hLm
    (S.card8 _ (S.fam_mem hLm)) hlabm
  have hzmz : zL = zm := hcov.twin_z U hU4 Lp hLp Lm hLm hlabp hlabm zL zm hzp hzm
  rw [← hzmz] at hzm
  have hcommLL : Commutes Lp Lm := hcov.twin_comm U hU4 Lp hLp Lm hLm hlabp hlabm
  obtain ⟨ep⟩ := S.iso_q8 (S.fam_mem hLp)
  obtain ⟨em⟩ := S.iso_q8 (S.fam_mem hLm)
  have hΩ := S.hs.hyp
  have hmemπ : J' ∈ gCentMembers (CoreAssembly.conjClass K₀) u :=
    CFSG.ClassicalInvolution.Generic.mem_centMembers_iff_commute.mpr
      ⟨S.mem_of_mem_pi hJ', fun y hy => huX y (le_piGen hJ' hy)⟩
  have htO : t ∈ pCoreOf 2 (pSpan (gCentMembers (CoreAssembly.conjClass K₀) u)) :=
    hS2 J' hmemπ t ht
  obtain ⟨βY, hβY, cY, hlabY⟩ := Ju.label Lp hPp
  have hzLne : Ju.φ ⟨zL, le_pSpan hPp hzp.mem⟩ ≠ 1 := by
    rw [Ju.map_eq_zBar hk5 hPp (S.card8 _ (S.fam_mem hLp)) hlabY hzp]
    exact AE.zBar_ne_one hk5 βY hβY
  obtain ⟨c', hc', hc'u, hφc'⟩ := S.exists_cprime hm5 hm8 J hpair.2.1 hu' hφu U hU4 haU hcU
  have hc'N : c' ∈ Subgroup.normalizer
      (pSpan (gCentMembers (CoreAssembly.conjClass K₀) u) : Set G) := by
    apply mem_normalizer_of_conjSub_eq
    have h1 := CFSG.ClassicalInvolution.Generic.conjSub_centLayer hΩ.conjInvariant c' u
    have h2 : c' * u * c'⁻¹ = u := by rw [hc'u]; group
    rw [h2] at h1
    exact h1
  have htC := S.cent_of_involution_pi hm5 htw J hJ' ht
  have htN : t ∈ Subgroup.normalizer (pSpan (fam K (conjSub g (piGen π))) : Set G) :=
    S.mem_normalizer_pSpan_fam htC
  have htfam : ∀ L ∈ fam K (conjSub g (piGen π)), conjSub t L ∈ fam K (conjSub g (piGen π)) :=
    fun L hL => S.fam_conj_of_cent' htC hL
  have hc'X : c' ∈ conjSub g (piGen π) := (SetLike.ext_iff.mp S.fam_gen c').mp hc'
  have hc'fam : ∀ L ∈ fam K (conjSub g (piGen π)), conjSub c' L ∈ fam K (conjSub g (piGen π)) :=
    fun L hL => fam_inv L hL c' hc'X
  have hc'N' : c' ∈ Subgroup.normalizer (pSpan (fam K (conjSub g (piGen π))) : Set G) :=
    Subgroup.le_normalizer hc'
  have hindc' : Cross.InducedBy J c'
      (twinVec (AE.emb U hU4) a * embed (AE.emb U hU4) yQ) := inducedBy_of_mem J hc' hφc'
  have hpc' : ∀ y, y ∈ U ↔
      (twinVec (AE.emb U hU4) a * embed (AE.emb U hU4) yQ).perm y ∈ U := by
    intro y
    have e : (twinVec (AE.emb U hU4) a * embed (AE.emb U hU4) yQ).perm =
        embedPerm (AE.emb U hU4) yQ.perm := by
      show (1 : Equiv.Perm (Fin 6)) * (embed (AE.emb U hU4) yQ).perm = _
      rw [one_mul]; rfl
    rw [e]
    by_cases hy : y ∈ Set.range (AE.emb U hU4)
    · obtain ⟨i, rfl⟩ := hy
      rw [embedPerm_apply]
      exact ⟨fun _ => (hrange _).mp ⟨_, rfl⟩, fun _ => (hrange _).mp ⟨_, rfl⟩⟩
    · rw [embedPerm_of_not_mem _ _ hy]
  have htx : t * x * t⁻¹ ∈ Lp ⊔ Lm := by
    have hmem : t * x * t⁻¹ ∈ conjSub t Lp := conj_mem_conjSub hx
    rcases S.conjSub_mem_pair hm5 J htN htfam hw U hU4 hp hLp hLm hlabp hlabm
        (Or.inl rfl) with h | h
    · rw [h] at hmem; exact Subgroup.mem_sup_left hmem
    · rw [h] at hmem; exact Subgroup.mem_sup_right hmem
  have hξQ : t * x * t⁻¹ * x⁻¹ ∈ Lp ⊔ Lm :=
    mul_mem htx (inv_mem (Subgroup.mem_sup_left hx))
  have hc'Q : ∀ y ∈ Lp ⊔ Lm, c' * y * c'⁻¹ ∈ Lp ⊔ Lm := by
    intro y hy
    obtain ⟨l, hl, l', hl', rfl⟩ := Q8Pair.mem_sup hcommLL hy
    have e : c' * (l * l') * c'⁻¹ = (c' * l * c'⁻¹) * (c' * l' * c'⁻¹) := by group
    rw [e]
    refine mul_mem ?_ ?_
    · have hmem : c' * l * c'⁻¹ ∈ conjSub c' Lp := conj_mem_conjSub hl
      rcases S.conjSub_mem_pair hm5 J hc'N' hc'fam hindc' U hU4 hpc' hLp hLm hlabp hlabm
          (Or.inl rfl) with h | h
      · rw [h] at hmem; exact Subgroup.mem_sup_left hmem
      · rw [h] at hmem; exact Subgroup.mem_sup_right hmem
    · have hmem : c' * l' * c'⁻¹ ∈ conjSub c' Lm := conj_mem_conjSub hl'
      rcases S.conjSub_mem_pair hm5 J hc'N' hc'fam hindc' U hU4 hpc' hLp hLm hlabp hlabm
          (Or.inr rfl) with h | h
      · rw [h] at hmem; exact Subgroup.mem_sup_left hmem
      · rw [h] at hmem; exact Subgroup.mem_sup_right hmem
  have hξO : t * x * t⁻¹ * x⁻¹ ∈ pCoreOf 2 (pSpan (gCentMembers (CoreAssembly.conjClass K₀) u)) := by
    have h1 : x * t⁻¹ * x⁻¹ ∈ pCoreOf 2 (pSpan (gCentMembers (CoreAssembly.conjClass K₀) u)) :=
      pCoreOf_conj_mem_self (le_pSpan hPp hx) ((pCoreOf 2 _).inv_mem htO)
    have := (pCoreOf 2 (pSpan (gCentMembers (CoreAssembly.conjClass K₀) u))).mul_mem htO h1
    simpa [mul_assoc] using this
  have hξ''O := pCoreOf_conj_mem hc'N hξO
  have hξ''Q := hc'Q _ hξQ
  have hcomm : (t * x * t⁻¹ * x⁻¹) * (c' * (t * x * t⁻¹ * x⁻¹) * c'⁻¹) =
      (c' * (t * x * t⁻¹ * x⁻¹) * c'⁻¹) * (t * x * t⁻¹ * x⁻¹) := by
    rcases Q8Pair.comm_mem hzp hzm hcommLL ep em hξQ hξ''Q with h1 | h1
    · calc (t * x * t⁻¹ * x⁻¹) * (c' * (t * x * t⁻¹ * x⁻¹) * c'⁻¹)
          = ((t * x * t⁻¹ * x⁻¹) * (c' * (t * x * t⁻¹ * x⁻¹) * c'⁻¹) * (t * x * t⁻¹ * x⁻¹)⁻¹ *
              (c' * (t * x * t⁻¹ * x⁻¹) * c'⁻¹)⁻¹) *
            ((c' * (t * x * t⁻¹ * x⁻¹) * c'⁻¹) * (t * x * t⁻¹ * x⁻¹)) := by group
        _ = (c' * (t * x * t⁻¹ * x⁻¹) * c'⁻¹) * (t * x * t⁻¹ * x⁻¹) := by rw [h1, one_mul]
    · exfalso
      obtain ⟨hc, hφ⟩ := comm_ker_of_pCore hk5 Ju hξO hξ''O
      apply hzLne
      have : (⟨zL, le_pSpan hPp hzp.mem⟩ : ↥(pSpan (gCentMembers (CoreAssembly.conjClass K₀) u))) =
          ⟨(t * x * t⁻¹ * x⁻¹) * (c' * (t * x * t⁻¹ * x⁻¹) * c'⁻¹) * (t * x * t⁻¹ * x⁻¹)⁻¹ *
            (c' * (t * x * t⁻¹ * x⁻¹) * c'⁻¹)⁻¹, hc⟩ := Subtype.ext h1.symm
      rw [this]
      exact hφ
  have hsq : (t * x * t⁻¹ * x⁻¹) * (t * x * t⁻¹ * x⁻¹) = 1 := by
    rcases Q8Pair.sq_mem hzp hzm hcommLL ep em hξQ with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨hc, hφ⟩ := sq_ker_of_pCore hk5 Ju hξO
      apply hzLne
      have : (⟨zL, le_pSpan hPp hzp.mem⟩ : ↥(pSpan (gCentMembers (CoreAssembly.conjClass K₀) u))) =
          ⟨(t * x * t⁻¹ * x⁻¹) * (t * x * t⁻¹ * x⁻¹), hc⟩ := Subtype.ext h1.symm
      rw [this]
      exact hφ
  have hxP : x ∈ pSpan (fam K (conjSub g (piGen π))) := le_pSpan hLp hx
  have hx₁ : t * x * t⁻¹ ∈ pSpan (fam K (conjSub g (piGen π))) :=
    TwinThinPf.conj_mem_of_normalizer htN hxP
  have hξX : t * x * t⁻¹ * x⁻¹ ∈ pSpan (fam K (conjSub g (piGen π))) :=
    mul_mem hx₁ (inv_mem hxP)
  have hξ2X : c' * (t * x * t⁻¹ * x⁻¹) * c'⁻¹ ∈ pSpan (fam K (conjSub g (piGen π))) :=
    TwinThinPf.conj_mem_of_normalizer hc'N' hξX
  have hja : a ∉ Set.range (AE.emb U hU4) := fun hh => haU ((hrange a).mp hh)
  obtain ⟨ξ₀, hξ₀⟩ : ∃ ξ₀ : Wr 4, ξ₀ = (b₀ * k * b₀⁻¹) * k⁻¹ := ⟨_, rfl⟩
  have hφξ : J.φ ⟨t * x * t⁻¹ * x⁻¹, hξX⟩ = AE.mkQ 6 (embed (AE.emb U hU4) ξ₀) := by
    have e1 : (⟨t * x * t⁻¹ * x⁻¹, hξX⟩ : ↥(pSpan (fam K (conjSub g (piGen π))))) =
        ⟨t * x * t⁻¹, hx₁⟩ * ⟨x, hxP⟩⁻¹ := rfl
    have e2 := hw ⟨x, hxP⟩ ⟨t * x * t⁻¹, hx₁⟩ rfl
    rw [e1, map_mul, map_inv, e2, hφx]
    have h1 : AE.mkQ 6 w * AE.mkQ 6 (embed (AE.emb U hU4) k) * (AE.mkQ 6 w)⁻¹ =
        AE.mkQ 6 (embed (AE.emb U hU4) (b₀ * k * b₀⁻¹)) := by
      rw [← map_inv, ← map_mul, ← map_mul, hconjw k]
    rw [h1, hξ₀]
    simp only [map_mul, map_inv]
  obtain ⟨ξ₁, hξ₁⟩ : ∃ ξ₁ : Wr 4,
      ξ₁ = (ofVec (vec4 [0]) * yQ) * ξ₀ * (ofVec (vec4 [0]) * yQ)⁻¹ := ⟨_, rfl⟩
  have hφξ2 : J.φ ⟨c' * (t * x * t⁻¹ * x⁻¹) * c'⁻¹, hξ2X⟩ =
      AE.mkQ 6 (embed (AE.emb U hU4) ξ₁) := by
    have e2 := hindc' ⟨t * x * t⁻¹ * x⁻¹, hξX⟩ ⟨c' * (t * x * t⁻¹ * x⁻¹) * c'⁻¹, hξ2X⟩ rfl
    rw [e2, hφξ, ← map_inv, ← map_mul, ← map_mul,
      conj_wc_embed (AE.emb U hU4) hja ξ₀, hξ₁]
  have hφcomm : AE.mkQ 6 (embed (AE.emb U hU4) ξ₀) * AE.mkQ 6 (embed (AE.emb U hU4) ξ₁) =
      AE.mkQ 6 (embed (AE.emb U hU4) ξ₁) * AE.mkQ 6 (embed (AE.emb U hU4) ξ₀) := by
    rw [← hφξ, ← hφξ2, ← map_mul, ← map_mul]
    exact congrArg J.φ (Subtype.ext hcomm)
  have hcomm₀ : ξ₀ * ξ₁ = ξ₁ * ξ₀ := by
    have h1 := comm_of_mkQ_comm_of_supportedOn hm5 (embed_supportedOn (AE.emb U hU4) ξ₀)
      (embed_supportedOn (AE.emb U hU4) ξ₁) hφcomm
    apply embed_injective (AE.emb U hU4)
    rw [map_mul, map_mul]
    exact h1
  have hξ₀sq : ξ₀ * ξ₀ = 1 := by
    have h1 : J.φ ⟨(t * x * t⁻¹ * x⁻¹) * (t * x * t⁻¹ * x⁻¹), mul_mem hξX hξX⟩ = 1 := by
      have : (⟨(t * x * t⁻¹ * x⁻¹) * (t * x * t⁻¹ * x⁻¹), mul_mem hξX hξX⟩ :
          ↥(pSpan (fam K (conjSub g (piGen π))))) = 1 := Subtype.ext hsq
      rw [this, map_one]
    have h2 : J.φ ⟨(t * x * t⁻¹ * x⁻¹) * (t * x * t⁻¹ * x⁻¹), mul_mem hξX hξX⟩ =
        AE.mkQ 6 (embed (AE.emb U hU4) (ξ₀ * ξ₀)) := by
      have e : (⟨(t * x * t⁻¹ * x⁻¹) * (t * x * t⁻¹ * x⁻¹), mul_mem hξX hξX⟩ :
          ↥(pSpan (fam K (conjSub g (piGen π))))) = ⟨_, hξX⟩ * ⟨_, hξX⟩ := rfl
      rw [e, map_mul, hφξ, ← map_mul, ← map_mul]
    rw [h2] at h1
    have h3 : AE.mkQ 6 (embed (AE.emb U hU4) (ξ₀ * ξ₀)) =
        AE.mkQ 6 (embed (AE.emb U hU4) 1) := by
      rw [h1, map_one, map_one]
    have h4 := mkQ_inj_of_supportedOn hm5 (embed_supportedOn (AE.emb U hU4) _)
      (embed_supportedOn (AE.emb U hU4) _) h3
    exact embed_injective (AE.emb U hU4) h4
  have hξ₀perm : ξ₀.perm ≠ 1 := by
    intro hh
    apply hnc
    have h1 : b₀.perm * k.perm * b₀.perm⁻¹ * k.perm⁻¹ = 1 := by
      have := hh
      rw [hξ₀] at this
      simpa [Wr.mul_perm, Wr.inv_perm] using this
    calc b₀.perm * k.perm
        = (b₀.perm * k.perm * b₀.perm⁻¹ * k.perm⁻¹) * (k.perm * b₀.perm) := by group
      _ = k.perm * b₀.perm := by rw [h1, one_mul]
  have hξ₀q : ξ₀ ∈ TwinThinPf20.q0List := by
    rw [hξ₀]
    exact TwinThinPf20.conj_comm_mem_q0 b₀ hk
  refine TwinThinPf20.fc_key ξ₀ hξ₀q hξ₀sq hξ₀perm ?_
  rw [← hξ₁]
  exact hcomm₀

end Setting

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
