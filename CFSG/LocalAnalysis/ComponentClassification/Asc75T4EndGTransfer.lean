module

public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4EndGSylow
public import CFSG.GH74.GLS.Bg.Local.Transfer1515

public section

namespace CFSG.ComponentClassification.Asc75T4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem5
open CFSG.ComponentClassification.AschbacherTheorem5.SectionSix
open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G]

namespace PSLModel

variable {Q : Subgroup G} (M : PSLModel Q)

omit [Finite G] in
theorem mul_mem_psl {x y : PGammaL2 M.F} (hx : x ∈ pGammaL2PGLRange M.F)
    (hy : y ∈ pGammaL2PGLRange M.F) (hx' : x ∉ pGammaL2PSLRange M.F)
    (hy' : y ∉ pGammaL2PSLRange M.F) : x * y ∈ pGammaL2PSLRange M.F := by
  have hidx := pGammaL2_psl_range_relIndex_pgl_eq_two M.F M.hF
  have h := (Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨x, hx⟩ : pGammaL2PGLRange M.F))
    (b := ⟨y, hy⟩)).mpr ⟨fun h => absurd h hx', fun h => absurd h hy'⟩
  exact h

theorem pglRange_le_range {t : G} (ht : IsOverlapInv Q t)
    (hpgl : M.psi (toBar Q ⟨t, ht.mem_normalizer⟩) ∈ pGammaL2PGLRange M.F)
    (hpsl : M.psi (toBar Q ⟨t, ht.mem_normalizer⟩) ∉ pGammaL2PSLRange M.F) :
    pGammaL2PGLRange M.F ≤ M.psi.range := by
  have hpslr : pGammaL2PSLRange M.F ≤ M.psi.range := by
    rintro _ ⟨y, rfl⟩
    refine ⟨(M.e.symm y : Bar Q), ?_⟩
    rw [M.psi_apply_of_mem, MulEquiv.apply_symm_apply]
    rfl
  intro x hx
  by_cases hxs : x ∈ pGammaL2PSLRange M.F
  · exact hpslr hxs
  · have h1 := M.mul_mem_psl hx hpgl hxs hpsl
    obtain ⟨w, hw⟩ := hpslr h1
    refine ⟨w * (toBar Q ⟨t, ht.mem_normalizer⟩)⁻¹, ?_⟩
    rw [map_mul, hw, map_inv, mul_inv_cancel_right]

end PSLModel

namespace EndSylow

variable {Q : Subgroup G} (X : EndSylow Q) (hE : EndSetting Q) (M : PSLModel Q)

theorem mem_R_of_mem_layer {s : G} (hs : s ∈ X.S)
    (h : toBar Q ⟨s, X.S_le hs⟩ ∈ bar Q (twoPrimeLayerIn Q)) : s ∈ X.R := by
  have h4 : toBar Q ⟨s, X.S_le hs⟩ ∈ bar Q (X.S ⊓ Q) := by
    rw [bar_inf_of_core_le (oddCoreIn_le Q)]
    exact mem_inf.mpr ⟨toBar_mem_bar Q hs, bar_mono Q (twoPrimeLayerIn_le Q) h⟩
  obtain ⟨r, hrR, hr⟩ := (mem_bar_iff Q _ _).mp h4
  have := toBar_injOn_of_isPGroup X.hS.isPGroup (mem_inf.mp hrR).1 hs hr
  rw [this] at hrR
  exact hrR

omit [Finite G] in
theorem isPGroup_zpowers_bar {s : G} (hs : s ∈ X.S) :
    IsPGroup 2 (zpowers (toBar Q ⟨s, X.S_le hs⟩)) :=
  (isPGroup_bar (D := Q) X.hS.isPGroup).to_le ((zpowers_le).mpr (toBar_mem_bar Q hs))

include hE in
theorem mem_P_iff_psi_mem
    (hodd : Odd (Nat.card (centralizer (bar Q (twoPrimeLayerIn Q) : Set (Bar Q)))))
    {s : G} (hs : s ∈ X.S) :
    s ∈ X.P ↔ M.psi (toBar Q ⟨s, X.S_le hs⟩) ∈ pGammaL2PGLRange M.F := by
  have htN := X.ht.mem_normalizer
  obtain ⟨hpgl, hpsl⟩ := M.outerDiagonal hE X.ht
  have hst : s * X.t ∈ X.S := mul_mem hs X.htS
  have hmul : toBar Q ⟨s * X.t, X.S_le hst⟩ = toBar Q ⟨s, X.S_le hs⟩ * toBar Q ⟨X.t, htN⟩ := by
    rw [← map_mul]
    rfl
  constructor
  · intro hP
    rcases X.mem_P_iff.mp hP with h | h
    · have hL : toBar Q ⟨s, X.S_le hs⟩ ∈ bar Q (twoPrimeLayerIn Q) :=
        hE.mem_layer_of_isPGroup (toBar_mem_bar Q (X.R_le_Q h)) (X.isPGroup_zpowers_bar hs)
      exact M.pslRange_le_pglRange ((M.mem_sup_centralizer_iff _).mp (mem_sup_left hL))
    · have hL : toBar Q ⟨s * X.t, X.S_le hst⟩ ∈ bar Q (twoPrimeLayerIn Q) :=
        hE.mem_layer_of_isPGroup (toBar_mem_bar Q (X.R_le_Q h)) (X.isPGroup_zpowers_bar hst)
      have h1 := M.pslRange_le_pglRange ((M.mem_sup_centralizer_iff _).mp (mem_sup_left hL))
      rw [hmul, map_mul] at h1
      have h2 := mul_mem h1 (inv_mem hpgl)
      rwa [mul_inv_cancel_right] at h2
  · intro h
    by_cases hs' : M.psi (toBar Q ⟨s, X.S_le hs⟩) ∈ pGammaL2PSLRange M.F
    · have hL := hE.mem_layer_of_mem_sup hodd ((M.mem_sup_centralizer_iff _).mpr hs')
        (X.isPGroup_zpowers_bar hs)
      exact X.R_le_P (X.mem_R_of_mem_layer hs hL)
    · have h1 := M.mul_mem_psl h hpgl hs' hpsl
      rw [← map_mul, ← hmul] at h1
      have hL := hE.mem_layer_of_mem_sup hodd ((M.mem_sup_centralizer_iff _).mpr h1)
        (X.isPGroup_zpowers_bar hst)
      exact X.mem_P_iff.mpr (Or.inr (X.mem_R_of_mem_layer hst hL))

@[expose] noncomputable def toOut : X.S →* PGammaL2 M.F ⧸ pGammaL2PGLRange M.F :=
  (QuotientGroup.mk' (pGammaL2PGLRange M.F)).comp
    (M.psi.comp ((toBar Q).comp (inclusion X.S_le)))

theorem toOut_apply (s : X.S) :
    X.toOut M s = QuotientGroup.mk (M.psi (toBar Q ⟨s, X.S_le s.2⟩)) := rfl

include hE in
theorem toOut_eq_one_iff
    (hodd : Odd (Nat.card (centralizer (bar Q (twoPrimeLayerIn Q) : Set (Bar Q)))))
    (s : X.S) : X.toOut M s = 1 ↔ (s : G) ∈ X.P := by
  rw [toOut_apply, QuotientGroup.eq_one_iff, X.mem_P_iff_psi_mem hE M hodd s.2]

include hE M in
theorem exists_generator
    (hodd : Odd (Nat.card (centralizer (bar Q (twoPrimeLayerIn Q) : Set (Bar Q))))) :
    ∃ b ∈ X.S, ∀ x ∈ X.S, ∃ k : ℤ, (b ^ k)⁻¹ * x ∈ X.P := by
  have : IsCyclic (PGammaL2 M.F ⧸ pGammaL2PGLRange M.F) := pGammaL2_quotient_pgl_isCyclic M.F M.hF
  obtain ⟨⟨y, b, rfl⟩, hy⟩ := IsCyclic.exists_generator (α := (X.toOut M).range)
  refine ⟨b, b.2, fun x hx => ?_⟩
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hy ⟨X.toOut M ⟨x, hx⟩, ⟨x, hx⟩, rfl⟩)
  refine ⟨k, ?_⟩
  have hk' : X.toOut M b ^ k = X.toOut M ⟨x, hx⟩ := congrArg Subtype.val hk
  have h1 : X.toOut M ((b ^ k)⁻¹ * ⟨x, hx⟩) = 1 := by
    rw [map_mul, map_inv, map_zpow, hk', inv_mul_cancel]
  exact (X.toOut_eq_one_iff hE M hodd _).mp h1

include hE M in
theorem inv_mul_mem_P
    (hodd : Odd (Nat.card (centralizer (bar Q (twoPrimeLayerIn Q) : Set (Bar Q)))))
    {u v : G} (hu : u ∈ X.S) (hv : v ∈ X.S) (hu2 : u ^ 2 = 1) (hv2 : v ^ 2 = 1)
    (huP : u ∉ X.P) (hvP : v ∉ X.P) : u⁻¹ * v ∈ X.P := by
  have : IsCyclic (PGammaL2 M.F ⧸ pGammaL2PGLRange M.F) := pGammaL2_quotient_pgl_isCyclic M.F M.hF
  have : Finite (X.toOut M).range :=
    Finite.of_surjective (X.toOut M).rangeRestrict (MonoidHom.rangeRestrict_surjective _)
  have hsq : ∀ w : X.S, (w : G) ^ 2 = 1 → (X.toOut M).rangeRestrict w ^ 2 = 1 := fun w hw => by
    rw [← map_pow, show w ^ 2 = 1 from Subtype.ext (by simpa using hw), map_one]
  have hne : ∀ w : X.S, (w : G) ∉ X.P → (X.toOut M).rangeRestrict w ≠ 1 := fun w hw h =>
    hw ((X.toOut_eq_one_iff hE M hodd w).mp (congrArg Subtype.val h))
  have heq := AschbacherKnownGroup.FactsL2.eq_of_sq_eq_one_of_isCyclic
    (hsq ⟨u, hu⟩ hu2) (hsq ⟨v, hv⟩ hv2) (hne ⟨u, hu⟩ huP) (hne ⟨v, hv⟩ hvP)
  have h1 : X.toOut M ((⟨u, hu⟩ : X.S)⁻¹ * ⟨v, hv⟩) = 1 := by
    rw [map_mul, map_inv]
    have := congrArg Subtype.val heq
    simp only [MonoidHom.coe_rangeRestrict] at this
    rw [this, inv_mul_cancel]
  exact (X.toOut_eq_one_iff hE M hodd _).mp h1

include hE M in
theorem exists_involution
    (hodd : Odd (Nat.card (centralizer (bar Q (twoPrimeLayerIn Q) : Set (Bar Q)))))
    (hSP : ¬ X.S ≤ X.P) : ∃ y ∈ X.S, y ^ 2 = 1 ∧ y ∉ X.P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set PG := pGammaL2PGLRange M.F with hPG
  obtain ⟨hpgl, hpsl⟩ := M.outerDiagonal hE X.ht
  obtain ⟨s₀, hs₀S, hs₀P⟩ := Set.not_subset.mp hSP
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp X.hS.isPGroup ⟨s₀, hs₀S⟩
  have hk' : orderOf s₀ = 2 ^ k := (Subgroup.orderOf_coe (⟨s₀, hs₀S⟩ : X.S)).trans hk
  obtain ⟨s, hsS, hsP, hs2P⟩ : ∃ s ∈ X.S, s ∉ X.P ∧ s ^ 2 ∈ X.P := by
    have hex : ∃ j : ℕ, s₀ ^ 2 ^ j ∈ X.P := ⟨k, by rw [← hk', pow_orderOf_eq_one]; exact one_mem _⟩
    let j := Nat.find hex
    have hj : s₀ ^ 2 ^ j ∈ X.P := Nat.find_spec hex
    have hj0 : j ≠ 0 := fun h => hs₀P (by simpa [h] using hj)
    refine ⟨s₀ ^ 2 ^ (j - 1), pow_mem hs₀S _, Nat.find_min hex (by omega), ?_⟩
    rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hj0)]
    exact hj
  have hsN := X.S_le hsS
  set γ := M.psi (toBar Q ⟨s, hsN⟩) with hγ
  have hγPG : γ ∉ PG := fun h => hsP ((X.mem_P_iff_psi_mem hE M hodd hsS).mpr h)
  have hγ2 : γ ^ 2 ∈ PG := by
    have h := (X.mem_P_iff_psi_mem hE M hodd (pow_mem hsS 2)).mp hs2P
    have : toBar Q ⟨s ^ 2, X.S_le (pow_mem hsS 2)⟩ = toBar Q ⟨s, hsN⟩ ^ 2 := by
      rw [← map_pow]
      rfl
    rwa [this, map_pow] at h
  have hker : ∀ x : PGammaL2 M.F, x ∈ PG ↔ x.right = 1 := fun x => by
    rw [hPG, pGammaL2PGLRange, SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.mem_ker,
      SemidirectProduct.rightHom_eq_right]
  set σ := γ.right with hσ
  have hσ1 : σ ≠ 1 := fun h => hγPG ((hker γ).mpr h)
  have hσ2 : σ * σ = 1 := by
    have := (hker _).mp hγ2
    rwa [pow_two, SemidirectProduct.mul_right] at this
  set j : PGammaL2 M.F := SemidirectProduct.inr σ with hj
  have hj2 : j ^ 2 = 1 := by
    rw [hj, pow_two, ← (SemidirectProduct.inr : (M.F ≃+* M.F) →* PGammaL2 M.F).map_mul, hσ2,
      map_one]
  have hjPG : j ∉ PG := fun h => hσ1 (by
    have := (hker _).mp h
    rwa [hj, SemidirectProduct.right_inr] at this)
  have hjr : j ∈ M.psi.range := by
    have hrange := M.pglRange_le_range X.ht hpgl hpsl
    have h1 : SemidirectProduct.inl γ.left ∈ M.psi.range := hrange ⟨_, rfl⟩
    have h2 : γ ∈ M.psi.range := ⟨_, rfl⟩
    have : j = (SemidirectProduct.inl γ.left)⁻¹ * γ := by
      rw [eq_inv_mul_iff_mul_eq, SemidirectProduct.inl_left_mul_inr_right]
    rw [this]
    exact mul_mem (inv_mem h1) h2
  obtain ⟨v₁, hv₁⟩ := hjr
  have hv₁sq : M.psi (v₁ ^ 2) = 1 := by rw [map_pow, hv₁, hj2]
  have hC := (M.psi_eq_one_iff _).mp hv₁sq
  obtain ⟨m, hm⟩ : Odd (orderOf (v₁ ^ 2)) := by
    have h := orderOf_dvd_natCard (⟨v₁ ^ 2, hC⟩ :
      centralizer (bar Q (twoPrimeLayerIn Q) : Set (Bar Q)))
    rw [Subgroup.orderOf_mk] at h
    exact hodd.of_dvd_nat h
  set v₂ := v₁ ^ (2 * m + 1) with hv₂
  have hv₂2 : v₂ ^ 2 = 1 := by
    rw [hv₂, ← pow_mul, show (2 * m + 1) * 2 = 2 * (2 * m + 1) by ring, pow_mul, ← hm,
      pow_orderOf_eq_one]
  have hψv₂ : M.psi v₂ = j := by
    rw [hv₂, map_pow, hv₁, pow_succ, pow_mul, hj2, one_pow, one_mul]
  obtain ⟨h₀, hh₀⟩ := toBar_surjective Q v₂
  have hh₀sq : toBar Q (h₀ ^ 2) = 1 := by rw [map_pow, hh₀, hv₂2]
  rw [toBar_eq_one_iff] at hh₀sq
  obtain ⟨m', hm'⟩ : Odd (orderOf ((h₀ : G) ^ 2)) := by
    have h0 : ((h₀ : G) ^ 2) ∈ oddCoreIn Q := by
      have := hh₀sq
      simp only [SubgroupClass.coe_pow] at this
      exact this
    have h := orderOf_dvd_natCard (⟨(h₀ : G) ^ 2, h0⟩ : oddCoreIn Q)
    rw [Subgroup.orderOf_mk] at h
    exact (odd_card_oddCoreIn Q).of_dvd_nat h
  set h₁ := h₀ ^ (2 * m' + 1) with hh₁
  have hh₁2 : (h₁ : G) ^ 2 = 1 := by
    rw [hh₁, SubgroupClass.coe_pow, ← pow_mul,
      show (2 * m' + 1) * 2 = 2 * (2 * m' + 1) by ring, pow_mul, ← hm', pow_orderOf_eq_one]
  have hψh₁ : M.psi (toBar Q h₁) = j := by
    rw [hh₁, map_pow, hh₀, map_pow, hψv₂, pow_succ, pow_mul, hj2, one_pow, one_mul]
  obtain ⟨c, hcH, hc⟩ := AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf X.hS
    (isPGroup_zpowers_of_pow_eq_one (k := 1) (by simpa using hh₁2))
    ((zpowers_le).mpr h₁.2)
  have hyS : c⁻¹ * (h₁ : G) * c ∈ X.S := hc ((mem_rightConjugate_iff _ c _).mpr (by
    rw [show c * (c⁻¹ * (h₁ : G) * c) * c⁻¹ = h₁ by group]
    exact mem_zpowers _))
  refine ⟨c⁻¹ * h₁ * c, hyS, by
    rw [show (c⁻¹ * (h₁ : G) * c) ^ 2 = c⁻¹ * (h₁ : G) ^ 2 * c by rw [pow_two, pow_two]; group,
      hh₁2]
    group, fun hyP => ?_⟩
  have h1 := (X.mem_P_iff_psi_mem hE M hodd hyS).mp hyP
  have h2 : toBar Q ⟨c⁻¹ * h₁ * c, X.S_le hyS⟩ =
      (toBar Q ⟨c, hcH⟩)⁻¹ * toBar Q h₁ * toBar Q ⟨c, hcH⟩ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [h2, map_mul, map_mul, map_inv, hψh₁] at h1
  apply hjPG
  have h3 := (pGammaL2PGLRange_normal M.F).conj_mem _ h1 (M.psi (toBar Q ⟨c, hcH⟩))
  rwa [show M.psi (toBar Q ⟨c, hcH⟩) * ((M.psi (toBar Q ⟨c, hcH⟩))⁻¹ * j *
    M.psi (toBar Q ⟨c, hcH⟩)) * (M.psi (toBar Q ⟨c, hcH⟩))⁻¹ = j by group] at h3

end EndSylow

namespace MainCounterexample

variable {Q : Subgroup G} (hM : MainCounterexample G Q) (hE : EndSetting Q)
include hM hE

theorem S_le_P
    (X : EndSylow Q) (M : PSLModel Q) : X.S ≤ X.P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd := hM.odd_card_centralizer hE
  by_contra hSP
  obtain ⟨y, hyS, hy2, hyP⟩ := X.exists_involution hE M hodd hSP
  have hy1 : y ≠ 1 := fun h => hyP (h ▸ one_mem _)
  have hSyl := hE.isSylowOf_top X.hS
  have hSidx : ¬ 2 ∣ X.S.index := by
    have := (isSylowOf_iff.mp hSyl).2.2
    rwa [relIndex_top_right] at this
  have hconj : ∀ g : G, g⁻¹ * y * g ∉ X.P := by
    intro g hg
    have hω := X.isOmegaInv_of_mem hE M hg (by rw [show (g⁻¹ * y * g) ^ 2 = g⁻¹ * y ^ 2 * g by rw [pow_two, pow_two]; group, hy2]; group)
      (fun h => hy1 (by rw [show y = g * (g⁻¹ * y * g) * g⁻¹ by group, h]; group))
    have hω' := hω.conj g
    rw [show g * (g⁻¹ * y * g) * g⁻¹ = y by group] at hω'
    exact hyP (X.mem_of_isOmegaInv hE hodd hyS hω')
  have hQn : ∀ s ∈ X.S, ∀ p ∈ X.P, s * p * s⁻¹ ∈ X.P := by
    intro s hs p hp
    have hsp : s * p * s⁻¹ ∈ X.S := mul_mem (mul_mem hs (X.P_le_S hp)) (inv_mem hs)
    rw [X.mem_P_iff_psi_mem hE M hodd hsp]
    have h1 := (X.mem_P_iff_psi_mem hE M hodd (X.P_le_S hp)).mp hp
    have : toBar Q ⟨s * p * s⁻¹, X.S_le hsp⟩ = toBar Q ⟨s, X.S_le hs⟩ *
        toBar Q ⟨p, X.S_le (X.P_le_S hp)⟩ * (toBar Q ⟨s, X.S_le hs⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [this, map_mul, map_mul, map_inv]
    exact (pGammaL2PGLRange_normal M.F).conj_mem _ h1 _
  rcases CFSG.GH74.GLS.Bg.Thompson.thompson_transfer_1515 (p := 2) hSyl.isPGroup hSidx hQn
      (X.exists_generator hE M hodd) hyS hyP
      (fun g k _ => by
        rw [pow_mul, hy2, one_pow, mul_one, inv_mul_cancel]
        exact one_mem _)
      (fun g hgS _ => Or.inr (X.inv_mul_mem_P hE M hodd hyS hgS hy2
        (by rw [show (g⁻¹ * y * g) ^ 2 = g⁻¹ * y ^ 2 * g by rw [pow_two, pow_two]; group, hy2]; group) hyP (hconj g))) with
    ⟨N, hN, -, hNp, hyN⟩ | ⟨g, hg, -, -⟩
  · have := hN
    have : Group.IsNilpotent (G ⧸ N) := hNp.isNilpotent
    have hbt : (⊥ : Subgroup (G ⧸ N)) ≠ ⊤ := by
      intro h
      apply hyN
      have h1 : (QuotientGroup.mk y : G ⧸ N) ∈ (⊥ : Subgroup (G ⧸ N)) := by
        rw [h]
        exact Subgroup.mem_top _
      exact (QuotientGroup.eq_one_iff y).1 (Subgroup.mem_bot.1 h1)
    obtain ⟨M', hM', -⟩ := (eq_top_or_exists_le_coatom (⊥ : Subgroup (G ⧸ N))).resolve_left hbt
    have hMidx : M'.index = 2 := (IsPGroup.isCoatom_iff_index_eq_prime hNp).1 hM'
    exact hM.false_of_index_eq_two hE ((Subgroup.normal_of_index_eq_two hMidx).comap _)
      ((Subgroup.index_comap_of_surjective M' (f := QuotientGroup.mk' N)
        QuotientGroup.mk_surjective).trans hMidx)
  · exact hconj g hg

end MainCounterexample

end CFSG.ComponentClassification.Asc75T4
