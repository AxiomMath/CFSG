module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step211Str

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard Hexa

theorem mem_zpowers_of_commute_of_isThreeCycle {σ τ : Equiv.Perm (Fin 6)} (hτ : τ.IsThreeCycle)
    (hστ : σ * τ = τ * σ) {i₀ i₁ : Fin 6} (h01 : i₀ ≠ i₁) (hτ0 : τ i₀ = i₀) (hτ1 : τ i₁ = i₁)
    (hσ0 : σ i₀ = i₀) (hσ1 : σ i₁ = i₁) : ∃ i : ℕ, σ = τ ^ i := by
  have hcyc := hτ.isCycle
  obtain ⟨a, ha⟩ := hcyc.nonempty_support
  have ha' : τ a ≠ a := Equiv.Perm.mem_support.mp ha
  have hσa : τ (σ a) ≠ σ a := fun h => ha' (σ.injective (by
    calc σ (τ a) = (σ * τ) a := rfl
      _ = (τ * σ) a := by rw [hστ]
      _ = σ a := h))
  obtain ⟨i, hi⟩ := hcyc.exists_pow_eq ha' hσa
  set σ' := (τ ^ i)⁻¹ * σ with hσ'
  have hσ'τ : Commute σ' τ := by
    rw [hσ']
    exact ((Commute.pow_left (Commute.refl τ) i).inv_left).mul_left hστ
  have hσ'a : σ' a = a := by
    rw [hσ', Equiv.Perm.mul_apply, ← hi]
    simp
  have hfix : ∀ x, τ x ≠ x → σ' x = x := fun x hx => by
    obtain ⟨j, hj⟩ := hcyc.exists_pow_eq ha' hx
    rw [← hj]
    calc σ' ((τ ^ j) a) = (σ' * τ ^ j) a := rfl
      _ = (τ ^ j * σ') a := by rw [(hσ'τ.pow_right j).eq]
      _ = (τ ^ j) a := by rw [Equiv.Perm.mul_apply, hσ'a]
  have hfix0 : σ' i₀ = i₀ := by
    rw [hσ', Equiv.Perm.mul_apply, hσ0, Equiv.Perm.inv_eq_iff_eq,
      Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hτ0]
  have hfix1 : σ' i₁ = i₁ := by
    rw [hσ', Equiv.Perm.mul_apply, hσ1, Equiv.Perm.inv_eq_iff_eq,
      Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hτ1]
  have hsupp : σ'.support ⊆ ((τ.supportᶜ).erase i₀).erase i₁ := fun z hz => by
    rw [Equiv.Perm.mem_support] at hz
    simp only [Finset.mem_erase, Finset.mem_compl, Equiv.Perm.mem_support, not_not]
    exact ⟨fun h => hz (h ▸ hfix1), fun h => hz (h ▸ hfix0), by_contra fun h => hz (hfix z h)⟩
  have hcard : (((τ.supportᶜ).erase i₀).erase i₁).card = 1 := by
    have h0 : i₀ ∈ τ.supportᶜ := by
      rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not]
      exact hτ0
    have h1 : i₁ ∈ (τ.supportᶜ).erase i₀ := by
      rw [Finset.mem_erase, Finset.mem_compl, Equiv.Perm.mem_support, not_not]
      exact ⟨h01.symm, hτ1⟩
    rw [Finset.card_erase_of_mem h1, Finset.card_erase_of_mem h0, Finset.card_compl,
      hτ.card_support, Fintype.card_fin]
  have h1 : σ' = 1 :=
    Equiv.Perm.card_support_le_one.mp ((Finset.card_le_card hsupp).trans hcard.le)
  exact ⟨i, (inv_mul_eq_one.mp h1).symm⟩

variable {G : Type} [Group G] [Finite G]

section Frame

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

variable (h11 : Step11)
  {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
  (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A)))
  {x : G} (hx : x ∈ sec2P F) (hxS : x ∉ sec2S A R E F)

include h11 hE16 hF hL hodd hx hxS

theorem sec2UY_mem_normalizer_E
    (hEH : conjSet E (sec2H E F) = insert E (conjSet (rightConjugate E x) (sec2P E)))
    {u y : G} (huy : Sec2UY A R E F u y) : y ∈ normalizer (E : Set G) := by
  have hEx := (rightConjugate_inf_eq_and_sec2S_eq h11 hE16 hF hL hodd hx hxS).1
  have hPZ := sec2P_le_normalizer_sec2Z h11 hE16 hF hL hodd
  have hyH : y ∈ sec2H E F := huy.2.2.2.1.1.1
  have hyR : y ∈ normalizer (R : Set G) := huy.2.2.2.1.1.2
  have hmem : rightConjugate E y ∈ conjSet E (sec2H E F) := ⟨y, hyH, rfl⟩
  rw [hEH] at hmem
  rcases hmem with h | ⟨p, hp, hpe⟩
  · exact (rightConjugate_eq_self_iff E y).mp h
  · exfalso
    have hRA : R ≤ centralizer (A : Set G) := hF.sylowR.le
    have hRA1 : R ⊓ A = ⊥ := inf_eq_bot_of_odd_center hRA hF.sylowR.isPGroup hodd
    have hPE : sec2P E ≤ normalizer (E : Set G) := Sec2.sec2P_le E
    have hRZ : R ≤ sec2Z A E F := by
      intro r hr
      have h1 : r ∈ rightConjugate E y := by
        rw [mem_rightConjugate_iff]
        exact hF.R_le_E ((mem_normalizer_iff.mp hyR r).mp hr)
      rw [hpe, rightConjugate_mul, mem_rightConjugate_iff] at h1
      have h2 : p * r * p⁻¹ ∈ rightConjugate E x ⊓ E := by
        refine ⟨(mem_rightConjugate_iff _ _ _).mpr ?_,
          (mem_normalizer_iff.mp (hPE hp) r).mp (hF.R_le_E hr)⟩
        simpa [mul_assoc] using h1
      rw [hEx] at h2
      have h3 := (mem_normalizer_iff.mp (hPZ (inv_mem hp)) _).mp h2
      simpa [mul_assoc] using h3
    have hR1 : R = ⊥ := by
      rw [eq_bot_iff, ← hRA1]
      exact fun r hr => ⟨hr, (inf_le_left : sec2Z A E F ≤ A) (hRZ hr)⟩
    have := hF.cardR
    rw [hR1, card_bot] at this
    norm_num at this

variable (h4 : 4 ^ 4 ≤ Nat.card (conjClosure (E ⊓ A) (sec2P F)))

include h4

theorem sec2UY_mem_normalizer_sec2F0
    (hEH : conjSet E (sec2H E F) = insert E (conjSet (rightConjugate E x) (sec2P E)))
    {u y : G} (huy : Sec2UY A R E F u y) : y ∈ normalizer (sec2F0 A E x : Set G) := by
  have hyE := sec2UY_mem_normalizer_E h11 hE16 hF hL hodd hx hxS hEH huy
  have hyP := Sec2.normalizer_le_normalizer_sec2P E hyE
  have hyS := sec2H_le_normalizer_sec2S h11 hE16 hF hL hodd huy.2.2.2.1.1.1
  obtain ⟨hF0e, hF064⟩ := isElemAbelian_and_card_of_mem_planes hF
    (sec2F0_mem_planes h11 hE16 hF hL hodd hx hxS h4)
  set V := rightConjugate (sec2F0 A E x) y with hV
  have hVe : IsElemAbelian 2 V := AS76b.isElemAbelian_rightConjugate hF0e y
  have hV64 : Nat.card V = 64 := by rw [hV, rightConjugate_card, hF064]
  have hF0PS : sec2F0 A E x ≤ sec2P E ⊓ sec2S A R E F := by
    rw [sec2P_inf_sec2S_eq h11 hE16 hF hL hodd hx hxS]
    exact le_sup_right
  have hVPS : V ≤ sec2P E ⊓ sec2S A R E F := by
    intro v hv
    rw [hV, mem_rightConjugate_iff] at hv
    have h1 := hF0PS hv
    have e1 : v = y⁻¹ * (y * v * y⁻¹) * y⁻¹⁻¹ := by group
    rw [e1]
    exact Subgroup.mem_inf.mpr ⟨(mem_normalizer_iff.mp (inv_mem hyP) _).mp h1.1,
      (mem_normalizer_iff.mp (inv_mem hyS) _).mp h1.2⟩
  rcases le_or_le_of_isElemAbelian h11 hE16 hF hL hodd hx hxS hVPS hVe with h | h
  · exfalso
    have hVE : V = E := Subgroup.eq_of_le_of_card_ge h (by rw [hV64, hF.cardE])
    have h1 := rightConjugate_sec2F0_ne h11 hE16 hF hL hodd hx hxS hyE
    exact h1 hVE
  · have hVF : V = sec2F0 A E x := Subgroup.eq_of_le_of_card_ge h (by rw [hV64, hF064])
    exact (rightConjugate_eq_self_iff _ y).mp hVF

theorem sec2UY_sec2PlanesActionFin_eq_one (e : ↥(sec2PlanesP E F) ≃ Fin 6)
    {rep : Fin 64 → G} {ψ : ↥(normalizer (sec2P E : Set G)) →* Equiv.Perm (Fin 64)}
    (hc : Sec2HexaCoord E A F rep e ψ)
    (hEH : conjSet E (sec2H E F) = insert E (conjSet (rightConjugate E x) (sec2P E)))
    {u y : G} (huy : Sec2UY A R E F u y) :
    ∃ hy : y ∈ normalizer (sec2P E : Set G), y ∈ sec2K E ∧
      sec2PlanesActionFin E F e ⟨y, hy⟩ = 1 := by
  obtain ⟨huA, hu3, huE, ⟨⟨hyH, -⟩, hyu⟩, hy3⟩ := id huy
  have hyE := sec2UY_mem_normalizer_E h11 hE16 hF hL hodd hx hxS hEH huy
  have hyF0 := sec2UY_mem_normalizer_sec2F0 h11 hE16 hF hL hodd hx hxS h4 hEH huy
  have hyP := Sec2.normalizer_le_normalizer_sec2P E hyE
  have hyK : y ∈ sec2K E := mem_sec2K_of_odd hyP (by rw [hy3]; decide)
  obtain ⟨huEn, huF, -, hufix⟩ := sec2U_facts h11 hE16 hF hL hodd huA hu3 huE
  obtain ⟨huP, hτ⟩ :=
    isThreeCycle_sec2PlanesActionFin_sec2U h11 hE16 hF hL hodd hx hxS h4 e huA hu3 huE
  have huK : u ∈ sec2K E := mem_sec2K_of_odd huP (by rw [hu3]; decide)
  have huF0 := mem_normalizer_sec2F0_of_mem h11 hE16 hF hL hodd huA.1 huEn huF hx hxS
  have hEpl : E ∈ sec2PlanesP E F :=
    ⟨⟨1, Or.inl (rightConjugate_one E).symm⟩, le_sec2P_of_frame hF⟩
  have hF0pl : sec2F0 A E x ∈ sec2PlanesP E F :=
    ⟨sec2F0_mem_planes h11 hE16 hF hL hodd hx hxS h4, sec2F0_le_sec2P hF x⟩
  have h01 : e ⟨E, hEpl⟩ ≠ e ⟨_, hF0pl⟩ := fun h => by
    have h1 := rightConjugate_sec2F0_ne h11 hE16 hF hL hodd hx hxS (Subgroup.one_mem _)
    rw [rightConjugate_one] at h1
    exact h1 (congrArg Subtype.val (e.injective h)).symm
  have hfix : ∀ {n : G} (hn : n ∈ normalizer (sec2P E : Set G)) (V : ↥(sec2PlanesP E F)),
      n ∈ normalizer ((V : Subgroup G) : Set G) → sec2PlanesActionFin E F e ⟨n, hn⟩ (e V) = e V :=
    fun hn V hnV => by
      rw [sec2PlanesActionFin_apply_eq_iff, Equiv.symm_apply_apply]
      exact hnV
  have hcomm : sec2PlanesActionFin E F e ⟨y, hyP⟩ * sec2PlanesActionFin E F e ⟨u, huP⟩ =
      sec2PlanesActionFin E F e ⟨u, huP⟩ * sec2PlanesActionFin E F e ⟨y, hyP⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.mp hyu)
  obtain ⟨i, hi⟩ := mem_zpowers_of_commute_of_isThreeCycle hτ hcomm h01
    (hfix huP _ huEn) (hfix huP _ huF0) (hfix hyP _ hyE) (hfix hyP _ hyF0)
  refine ⟨hyP, hyK, ?_⟩
  have huy' : (u ^ i * y⁻¹ : G) ∈ sec2K E := mul_mem (pow_mem huK i) (inv_mem hyK)
  have hρ : sec2KAction E F e ⟨u ^ i * y⁻¹, huy'⟩ = 1 := by
    apply Subtype.ext
    rw [coe_sec2KAction_apply, OneMemClass.coe_one]
    have e1 : (⟨u ^ i * y⁻¹, sec2K_le_normalizer_sec2P E huy'⟩ :
        ↥(normalizer (sec2P E : Set G))) = ⟨u, huP⟩ ^ i * (⟨y, hyP⟩)⁻¹ := Subtype.ext rfl
    rw [e1, map_mul, map_pow, map_inv, ← hi, mul_inv_cancel]
  have hC := mem_centralizer_of_sec2KAction_eq_one h11 hE16 hF hL hodd hx hxS h4 e hc hρ
  have hZE : sec2Z A E F ≤ E ⊓ A := by
    rw [hF.sec2Z_eq]
    exact fun z hz => ⟨hz.1.1, hz.2⟩
  have hyZ := sec2H_le_centralizer_sec2Z h11 hE16 hF hL hodd hyH
  have huZ : ∀ w ∈ sec2Z A E F, u ^ i * w * (u ^ i)⁻¹ = w := fun w hw => by
    have h1 : w * (u ^ i * y⁻¹) = u ^ i * y⁻¹ * w := mem_centralizer_iff.mp hC w (hZE hw)
    have h2 : w * y = y * w := mem_centralizer_iff.mp hyZ w hw
    calc u ^ i * w * (u ^ i)⁻¹ = u ^ i * y⁻¹ * (y * w) * (u ^ i)⁻¹ := by group
      _ = u ^ i * y⁻¹ * (w * y) * (u ^ i)⁻¹ := by rw [← h2]
      _ = u ^ i * y⁻¹ * w * (u ^ i * y⁻¹)⁻¹ := by group
      _ = w * (u ^ i * y⁻¹) * (u ^ i * y⁻¹)⁻¹ := by rw [← h1]
      _ = w := by group
  have hu3' : u ^ 3 = 1 := by rw [← hu3]; exact pow_orderOf_eq_one u
  have h3 : 3 ∣ i := by
    by_contra h3
    have hi' : i % 3 = 1 ∨ i % 3 = 2 := by omega
    have hu' : u = (u ^ i) ^ (if i % 3 = 1 then 1 else 2) := by
      rw [← pow_mul, ← pow_mod_orderOf, hu3]
      rcases hi' with h | h
      · rw [ite_eq_left_iff.mpr (fun h' => absurd h h'), mul_one, h, pow_one]
      · rw [ite_eq_right_iff.mpr (fun h' => by omega), show i * 2 % 3 = 1 by omega, pow_one]
    obtain ⟨w, hw, hw1⟩ : ∃ w ∈ sec2Z A E F, w ≠ 1 := by
      by_contra hall
      push Not at hall
      have hbot : sec2Z A E F = ⊥ := eq_bot_iff.mpr fun w hw => hall w hw
      have h4' := hF.card_sec2Z hodd
      rw [hbot, card_bot] at h4'
      norm_num at h4'
    apply hw1
    refine hufix w hw ?_
    have hpow : ∀ j : ℕ, (u ^ i) ^ j * w * ((u ^ i) ^ j)⁻¹ = w := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        calc (u ^ i) ^ (j + 1) * w * ((u ^ i) ^ (j + 1))⁻¹
            = (u ^ i) ^ j * (u ^ i * w * (u ^ i)⁻¹) * ((u ^ i) ^ j)⁻¹ := by
              rw [pow_succ]; group
          _ = w := by rw [huZ w hw, ih]
    rw [hu']
    exact hpow _
  obtain ⟨k, rfl⟩ := h3
  rw [hi, pow_mul]
  have hτ3 : (sec2PlanesActionFin E F e ⟨u, huP⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨u, huP⟩ : ↥(normalizer (sec2P E : Set G))) ^ 3 = 1 := Subtype.ext (by simpa using hu3')
    rw [this, map_one]
  rw [hτ3, one_pow]

theorem commutator_mem_centralizerMod_of_sec2UY (e : ↥(sec2PlanesP E F) ≃ Fin 6)
    {rep : Fin 64 → G} {ψ : ↥(normalizer (sec2P E : Set G)) →* Equiv.Perm (Fin 64)}
    (hc : Sec2HexaCoord E A F rep e ψ)
    (hEH : conjSet E (sec2H E F) = insert E (conjSet (rightConjugate E x) (sec2P E)))
    {u y : G} (huy : Sec2UY A R E F u y) {k : G} (hk : k ∈ sec2K E) :
    y⁻¹ * k⁻¹ * y * k ∈ centralizerMod (sec2K E) (sec2P E) (E ⊓ A) := by
  obtain ⟨hyP, hyK, hρ⟩ := sec2UY_sec2PlanesActionFin_eq_one h11 hE16 hF hL hodd hx hxS h4 e hc
    hEH huy
  have hkP := sec2K_le_normalizer_sec2P E hk
  have hψ := psi_commute_of_mem_sec2K h11 hE16 hF hL hodd hc ⟨y, hyP⟩ hρ hk
  have hmem := (mem_centralizerMod_iff_psi h11 hE16 hF hL hodd hx hxS h4 e hc
    (n := (⟨y, hyP⟩ : ↥(normalizer (sec2P E : Set G)))⁻¹ * (⟨k, hkP⟩)⁻¹ * ⟨y, hyP⟩ * ⟨k, hkP⟩)
    (mul_mem (mul_mem (mul_mem (inv_mem hyK) (inv_mem hk)) hyK) hk)).mpr (by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      have e1 : (ψ ⟨y, hyP⟩)⁻¹ * (ψ ⟨k, hkP⟩)⁻¹ * ψ ⟨y, hyP⟩ * ψ ⟨k, hkP⟩ =
          (ψ ⟨y, hyP⟩)⁻¹ * (ψ ⟨k, hkP⟩)⁻¹ * (ψ ⟨y, hyP⟩ * ψ ⟨k, hkP⟩) := by group
      rw [e1, ← hψ]
      group)
  exact hmem

omit h11 hE16 hL hx hxS h4 in
theorem conj_ne_of_sec2UY {u y ξ : G} (huy : Sec2UY A R E F u y)
    (hξ : u = ξ * y ∨ u = ξ * y⁻¹) (hξS : ActsAsF4Scalar ξ (sec2S A R E F) (sec2Z A E F))
    {r : G} (hr : r ∈ R) (hr1 : r ≠ 1) : y⁻¹ * r * y ≠ r := by
  intro hyr
  have hRA : R ≤ centralizer (A : Set G) := hF.sylowR.le
  have hur : u * r = r * u := mem_centralizer_iff.mp (hRA hr) u huy.1.1
  have hyr' : y * r * y⁻¹ = r := by
    calc y * r * y⁻¹ = y * (y⁻¹ * r * y) * y⁻¹ := by rw [hyr]
      _ = r := by group
  have hξr : ξ⁻¹ * r * ξ = r := by
    rcases hξ with h | h
    · have e1 : ξ = u * y⁻¹ := by rw [h]; group
      rw [e1]
      calc (u * y⁻¹)⁻¹ * r * (u * y⁻¹) = y * (u⁻¹ * (r * u)) * y⁻¹ := by group
        _ = y * (u⁻¹ * (u * r)) * y⁻¹ := by rw [hur]
        _ = y * r * y⁻¹ := by group
        _ = r := hyr'
    · have e1 : ξ = u * y := by rw [h]; group
      rw [e1]
      calc (u * y)⁻¹ * r * (u * y) = y⁻¹ * (u⁻¹ * (r * u)) * y := by group
        _ = y⁻¹ * (u⁻¹ * (u * r)) * y := by rw [hur]
        _ = y⁻¹ * r * y := by group
        _ = r := hyr
  have hrS : r ∈ sec2S A R E F :=
    (le_sec2S_and_le_sec2S hF).1 (hF.R_le_E hr)
  have h1 := hξS.2.2 r hrS
  have h2 : ξ⁻¹ * ξ⁻¹ * r * ξ * ξ = r := by
    calc ξ⁻¹ * ξ⁻¹ * r * ξ * ξ = ξ⁻¹ * (ξ⁻¹ * r * ξ) * ξ := by group
      _ = r := by rw [hξr, hξr]
  rw [hξr, h2] at h1
  have hr2 : r * r = 1 := by rw [← sq]; exact hF.elemR.2 r hr
  rw [hr2, one_mul] at h1
  have hRA1 : R ⊓ A = ⊥ := inf_eq_bot_of_odd_center hRA hF.sylowR.isPGroup hodd
  have h3 : r ∈ R ⊓ A := ⟨hr, h1.1⟩
  rw [hRA1, mem_bot] at h3
  exact hr1 h3

end Frame

theorem step211_of
    (h11 : Step11) {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h22iv : Step22iv) : Step211 := by
  intro G _ _ A R g E F hS
  have hF := hS.frame
  have hL := hS.type
  have hodd := hS.odd
  have hSc := sec2S_comm h11 hE16 hF hL hodd
  have h4 : 4 ^ 4 ≤ Nat.card (conjClosure (E ⊓ A) (sec2P F)) :=
    h22iv G A R g F E ⟨hF.symm, hL, hodd, hS.below⟩
  have h4' : 4 ^ 4 ≤ Nat.card (conjClosure (F ⊓ A) (sec2P E)) := h22iv G A R g E F hS
  obtain ⟨h, hh, hhC⟩ := exists_mem_sec2P_not_mem_centralizerMod h11 hE16 hF hL hodd
  have hhS : h ∉ sec2S A R E F := fun hS' => hhC (by
    rw [← sec2S_inf_sec2P h11 hE16 hF hL hodd]
    exact ⟨hS', hh⟩)
  obtain ⟨x, hx, hxC⟩ := exists_mem_sec2P_not_mem_centralizerMod h11 hE16 hF.symm hL hodd
  have hxS : x ∉ sec2S A R E F := fun hS' => hxC (by
    rw [← sec2S_inf_sec2P h11 hE16 hF.symm hL hodd, hSc]
    exact ⟨hS', hx⟩)
  have hEH := conjSet_E_sec2H_eq_insert h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
  obtain ⟨rep, e, ψ, hc⟩ := exists_sec2HexaCoord h11 hE16 hF hL hodd hx hxS h4
  have hCeq := centralizerMod_eq_sup h11 hE16 hF hL hodd hx hxS h4 e hc
  have h27 := (step27_of h11 hE16 h22iv G A R g E F hS).2
  refine ⟨sup_le (sec2P_le_sec2K h11 hE16 hF hL hodd hx hxS h4 e hc)
    (AS76b.oddCoreIn_le _), ?_, ?_, ?_, ?_, hCeq, ?_, ⟨sec2KAction E F e,
    sec2KAction_surjective h11 hE16 hF hL hodd hx hxS h4 e,
    ker_sec2KAction h11 hE16 hF hL hodd hx hxS h4 e hc⟩, ?_⟩
  · rw [← hCeq]
    exact relIndex_centralizerMod h11 hE16 hF hL hodd hx hxS h4 e hc
  · rw [← hCeq]
    exact commutator_sup_centralizerMod_eq h11 hE16 hF hL hodd hx hxS h4 e hc
  · intro u y huy k hk
    rw [← hCeq]
    exact commutator_mem_centralizerMod_of_sec2UY h11 hE16 hF hL hodd hx hxS h4 e hc hEH huy hk
  · intro u y huy r hr hr1
    obtain ⟨ξ, -, hξ, hξS, -⟩ := h27 u y huy
    exact conj_ne_of_sec2UY hF hodd huy hξ hξS hr hr1
  · intro B hEB hBP hKB
    exact eq_or_eq_of_le_sec2P h11 hE16 hF hL hodd hx hxS h4 e hc hEB hBP hKB
  · intro B hB hKB
    exact eq_bot_or_eq_of_le_inf h11 hE16 hF hL hodd hx hxS h4 hB hKB

end CFSG.ComponentClassification.AS81
