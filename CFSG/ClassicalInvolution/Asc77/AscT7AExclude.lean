module

public import CFSG.ClassicalInvolution.Asc77.AscT7AStep12
public import CFSG.ClassicalInvolution.Asc77.AscT7ASetup
public import CFSG.ClassicalInvolution.Asc77.AscT7AEStand
public import CFSG.ClassicalInvolution.Asc77.AscP1ThompsonTwelve

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson

namespace T7A

section Finite

open Equiv

def swaps4 : Finset (Perm (Fin 4)) :=
  {swap 0 1, swap 0 2, swap 0 3, swap 1 2, swap 1 3, swap 2 3}

def swaps3 : Finset (Perm (Fin 3)) := {swap 0 1, swap 0 2, swap 1 2}

theorem odd_inv_mem4 : ∀ d : Perm (Fin 4), d * d = 1 → d ≠ 1 → Perm.sign d = -1 → d ∈ swaps4 := by
  decide

theorem even_inv_not_comm4 : ∀ d : Perm (Fin 4), d * d = 1 → d ≠ 1 → Perm.sign d = 1 →
    ∃ s ∈ swaps4, s * d ≠ d * s ∧ (s * d) ^ 3 ≠ 1 := by
  decide

theorem swaps_conj4 : ∀ s ∈ swaps4, ∀ s' ∈ swaps4, ∃ g : Perm (Fin 4), g * s * g⁻¹ = s' := by
  decide

theorem no_three_swaps4 : ∀ a ∈ swaps4, ∀ b ∈ swaps4, ∀ c ∈ swaps4, a ≠ b → a ≠ c → b ≠ c →
    a * b = b * a → a * c = c * a → b * c = c * b → False := by
  decide

theorem inv_mem3 : ∀ d : Perm (Fin 3), d * d = 1 → d ≠ 1 → d ∈ swaps3 := by decide

theorem no_two_comm3 : ∀ a ∈ swaps3, ∀ b ∈ swaps3, a ≠ b → a * b ≠ b * a := by decide

theorem no_three_commuting_perm4 {Δ : Set (Perm (Fin 4))} (h : Star3T.IsTT Δ) :
    ∀ a ∈ Δ, ∀ b ∈ Δ, ∀ c ∈ Δ, a ≠ b → a ≠ c → b ≠ c → a * b = b * a → a * c = c * a →
      b * c = c * b → False := by
  have hsw : ∀ d ∈ Δ, Perm.sign d = -1 → d ∈ swaps4 := fun d hd hs =>
    odd_inv_mem4 d (h.mul_self d hd) (h.ne_one d hd) hs
  have hodd : ∃ d ∈ Δ, Perm.sign d = -1 := by
    by_contra hno
    push Not at hno
    have hle : Subgroup.closure Δ ≤ (Perm.sign : Perm (Fin 4) →* ℤˣ).ker := by
      rw [Subgroup.closure_le]
      intro d hd
      rw [SetLike.mem_coe, MonoidHom.mem_ker]
      rcases Int.units_eq_one_or (Perm.sign d) with h1 | h1
      · exact h1
      · exact absurd h1 (hno d hd)
    rw [h.closure_eq_top] at hle
    have := hle (Subgroup.mem_top (swap (0 : Fin 4) 1))
    rw [MonoidHom.mem_ker, Perm.sign_swap (by decide)] at this
    exact absurd this (by decide)
  obtain ⟨d₀, hd₀, hd₀s⟩ := hodd
  have hall : ∀ s ∈ swaps4, s ∈ Δ := fun s hs => by
    obtain ⟨g, hg⟩ := swaps_conj4 d₀ (hsw d₀ hd₀ hd₀s) s hs
    rw [← hg]
    exact h.conj_mem d₀ hd₀ g
  have hΔ : ∀ x ∈ Δ, x ∈ swaps4 := fun x hx => by
    rcases Int.units_eq_one_or (Perm.sign x) with h1 | h1
    · exfalso
      obtain ⟨s, hs, hsne, hs3⟩ := even_inv_not_comm4 x (h.mul_self x hx) (h.ne_one x hx) h1
      rcases h.comm_or_cube s (hall s hs) x hx with h2 | h2
      · exact hsne h2
      · exact hs3 h2
    · exact hsw x hx h1
  intro a ha b hb c hc hab hac hbc h1 h2 h3
  exact no_three_swaps4 a (hΔ a ha) b (hΔ b hb) c (hΔ c hc) hab hac hbc h1 h2 h3

theorem no_two_commuting_perm3 {Δ : Set (Perm (Fin 3))} (h : Star3T.IsTT Δ) :
    ∀ a ∈ Δ, ∀ b ∈ Δ, a ≠ b → a * b ≠ b * a := fun a ha b hb hab =>
  no_two_comm3 a (inv_mem3 a (h.mul_self a ha) (h.ne_one a ha)) b
    (inv_mem3 b (h.mul_self b hb) (h.ne_one b hb)) hab

end Finite

theorem isTT_map_equiv {Q Q' : Type*} [Group Q] [Group Q'] {Δ : Set Q} (h : Star3T.IsTT Δ)
    (e : Q ≃* Q') : Star3T.IsTT (e '' Δ) where
  mul_self := by
    rintro _ ⟨d, hd, rfl⟩
    rw [← map_mul, h.mul_self d hd, map_one]
  ne_one := by
    rintro _ ⟨d, hd, rfl⟩ h1
    exact h.ne_one d hd (e.injective (by rw [h1, map_one]))
  conj_mem := by
    rintro _ ⟨d, hd, rfl⟩ g
    refine ⟨e.symm g * d * (e.symm g)⁻¹, h.conj_mem d hd _, ?_⟩
    simp
  closure_eq_top := by
    have h1 : Subgroup.closure (e '' Δ) = (Subgroup.closure Δ).map e.toMonoidHom :=
      (MonoidHom.map_closure e.toMonoidHom Δ).symm
    rw [h1, h.closure_eq_top]
    exact Subgroup.map_top_of_surjective _ e.surjective
  comm_or_cube := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rcases h.comm_or_cube a ha b hb with h1 | h1
    · left
      rw [← map_mul, ← map_mul, h1]
    · right
      rw [← map_mul, ← map_pow, h1, map_one]

end T7A

section Members

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem exists_muDelta_eq_piG {W R : Subgroup G} (hR : R ∈ DSet Ω W) {r : G} (hr : r ∈ R)
    (hrW : r ∉ W) : ∃ a ∈ muDelta Ω W, (a : NQuot (W ⊔ OCW W)) = piG W r :=
  ⟨⟨piG W r, piG_mem_muGroup (Subgroup.mem_sup_left (le_MGrp_of_mem_D hR hr))⟩,
    ⟨R, hR, r, hr, hrW, rfl⟩, rfl⟩

omit [Finite G] in
theorem muGroup_comm_of_comm {W R T : Subgroup G} (hR : R ∈ DSet Ω W) (hT : T ∈ DSet Ω W)
    {r t : G} (hr : r ∈ R) (ht : t ∈ T) (hrt : r * t = t * r) {a b : ↥(muGroup Ω W)}
    (ha : (a : NQuot (W ⊔ OCW W)) = piG W r) (hb : (b : NQuot (W ⊔ OCW W)) = piG W t) :
    a * b = b * a := by
  apply Subtype.ext
  show (a : NQuot (W ⊔ OCW W)) * b = b * a
  rw [ha, hb]
  refine (piG_comm_iff (hR.2 hr) (hT.2 ht)).mpr ?_
  have : r * t * r⁻¹ * t⁻¹ = 1 := by rw [hrt]; group
  rw [this]
  exact one_mem _

theorem piG_ne_of_ne_members (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {W : Subgroup G} (hW : W ∈ WSet Ω) {R T K J : Subgroup G} (hR : R ∈ DSet Ω W)
    (hT : T ∈ DSet Ω W) (hK : K ∈ Ω) (hJ : J ∈ Ω) (hRK : IsSylow2In R K) (hTJ : IsSylow2In T J)
    (hKJ : K ≠ J) {r t : G} (hr : r ∈ R) (ht : t ∈ T) (htW : t ∉ W) :
    piG W r ≠ piG W t := by
  intro heq
  have hTR : T ≤ R ⊔ W ⊔ OCW W :=
    le_sup_of_piG_eq hr hR.2 hT.2 fun x hx hxW =>
      (D_piG_eq hp hq hΩ hW hT hx ht hxW htW).trans heq.symm
  obtain ⟨M, hM, hRM, hTM⟩ := exists_member_of_D_same hp hq hΩ hW hR hT hTR
  have h8R := hΩ.eight_le_of_mem_RSet hp hR.1
  have h8T := hΩ.eight_le_of_mem_RSet hp hT.1
  have h1 : K = M := hΩ.eq_of_le_of_le hK hM hRK.2.1 (by omega) hRK.1 hRM
  have h2 : J = M := hΩ.eq_of_le_of_le hJ hM hTJ.2.1 (by omega) hTJ.1 hTM
  exact hKJ (h1.trans h2.symm)

end Members

section Exclude

variable {p f : ℕ} [Fact p.Prime]

variable (p f) in
theorem c21_12_exclude_of (h1 : ThompsonCube p f) (h752 : L7_5_2 p f) : C21_12_exclude p f := by
  intro G _ _ _ Ω K K' z u J t W h _
  have hp : p ≠ 2 := h.std.stand.odd
  have hq : 5 ≤ p ^ f := h.std.stand.five
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hK : K ∈ Ω := h.std.stand.mem
  have hK'Ω : K' ∈ Ω := h.std.hK'.1
  have hJΩ : J ∈ Ω := h.hJ.1
  have hP : PartIHyp p f Ω := ⟨hp, hq, hΩ, h.std.stand.aEmpty⟩
  obtain ⟨S, R, R', T, hRsyl, hR'syl, hTsyl, hRS, hR'S, hTS, hRR', hRT, hR'T⟩ :=
    exists_twinSylow hp hq hΩ hK h.std.hz h.std.hK' h.std.hne h.hJ
  obtain ⟨η, hη, hηinv⟩ := exists_invariant_mem_etaSet hp hq hΩ S
  obtain ⟨W₁, hW₁, hSN⟩ : ∃ W₁ : Subgroup G, W₁ ∈ WSet Ω ∧
      ∀ s ∈ (S : Subgroup G), s ∈ Subgroup.normalizer (W₁ : Set G) :=
    ⟨⨆ U ∈ η, U, ⟨η, ⟨S, hη, hηinv⟩, rfl⟩, fun s hs =>
      mem_normalizer_iff_conjSub_eq.mpr (T7A.conjSub_eta_eq hηinv hs)⟩
  have hRD : R ∈ DSet Ω W₁ := ⟨mem_RSet_of_isSylow2In hK hRsyl, fun x hx => hSN x (hRS hx)⟩
  have hR'D : R' ∈ DSet Ω W₁ := ⟨mem_RSet_of_isSylow2In hK'Ω hR'syl, fun x hx => hSN x (hR'S hx)⟩
  have hTD : T ∈ DSet Ω W₁ := ⟨mem_RSet_of_isSylow2In hJΩ hTsyl, fun x hx => hSN x (hTS hx)⟩
  have hTT := Thompson.isTT_muDelta hp hq hΩ hW₁ (h1 G Ω hP W₁ hW₁)
  obtain ⟨r, hr, hrW⟩ := exists_not_mem_of_mem_D hp hq hΩ hW₁ hRD
  obtain ⟨r', hr', hr'W⟩ := exists_not_mem_of_mem_D hp hq hΩ hW₁ hR'D
  obtain ⟨t', ht', ht'W⟩ := exists_not_mem_of_mem_D hp hq hΩ hW₁ hTD
  obtain ⟨a, ha, haeq⟩ := exists_muDelta_eq_piG hRD hr hrW
  obtain ⟨b, hb, hbeq⟩ := exists_muDelta_eq_piG hR'D hr' hr'W
  obtain ⟨c, hc, hceq⟩ := exists_muDelta_eq_piG hTD ht' ht'W
  have hKK' : K ≠ K' := h.std.hne.symm
  have hKJ : K ≠ J := fun e => by
    have := h.hJ.2 K (mem_twinSet_self hK h.std.hz)
    exact this.2.1 e.symm
  have hK'J : K' ≠ J := fun e => by
    have := h.hJ.2 K' h.std.hK'
    exact this.2.1 e.symm
  have hab : a ≠ b := fun e =>
    piG_ne_of_ne_members hp hq hΩ hW₁ hRD hR'D hK hK'Ω hRsyl hR'syl hKK' hr hr' hr'W
      (haeq.symm.trans ((congrArg Subtype.val e).trans hbeq))
  have hac : a ≠ c := fun e =>
    piG_ne_of_ne_members hp hq hΩ hW₁ hRD hTD hK hJΩ hRsyl hTsyl hKJ hr ht' ht'W
      (haeq.symm.trans ((congrArg Subtype.val e).trans hceq))
  have hbc : b ≠ c := fun e =>
    piG_ne_of_ne_members hp hq hΩ hW₁ hR'D hTD hK'Ω hJΩ hR'syl hTsyl hK'J hr' ht' ht'W
      (hbeq.symm.trans ((congrArg Subtype.val e).trans hceq))
  have hab' : a * b = b * a := muGroup_comm_of_comm hRD hR'D hr hr' (hRR' r hr r' hr') haeq hbeq
  have hac' : a * c = c * a := muGroup_comm_of_comm hRD hTD hr ht' (hRT r hr t' ht') haeq hceq
  have hbc' : b * c = c * b := muGroup_comm_of_comm hR'D hTD hr' ht' (hR'T r' hr' t' ht') hbeq hceq
  constructor
  · rintro ⟨e⟩
    obtain ⟨e'⟩ := h752 hp hq G Ω hΩ W₁ hW₁ W h.hW
    have hTT3 := T7A.isTT_map_equiv hTT (e'.trans e)
    exact T7A.no_two_commuting_perm3 hTT3 _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      (fun e2 => hab ((e'.trans e).injective e2))
      (by rw [← map_mul, ← map_mul, hab'])
  · rintro ⟨e⟩
    obtain ⟨e'⟩ := h752 hp hq G Ω hΩ W₁ hW₁ W h.hW
    have hTT4 := T7A.isTT_map_equiv hTT (e'.trans e)
    exact T7A.no_three_commuting_perm4 hTT4 _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
      (fun e2 => hab ((e'.trans e).injective e2)) (fun e2 => hac ((e'.trans e).injective e2))
      (fun e2 => hbc ((e'.trans e).injective e2))
      (by rw [← map_mul, ← map_mul, hab']) (by rw [← map_mul, ← map_mul, hac'])
      (by rw [← map_mul, ← map_mul, hbc'])

variable (p f) in
theorem c21_12_of_thompson (h717 : L7_17 p f) (h1 : ThompsonCube p f) (h752 : L7_5_2 p f) :
    C21_12 p f :=
  c21_12_of p f h717 (c21_12_exclude_of p f h1 h752)

variable (p f) in
theorem c21_12_of_inputs (h1 : ThompsonCube p f) (h2 : ThompsonStar p f)
    (h3 : ThompsonClique p f) (h752 : L7_5_2 p f) (h5 : ThompsonGraph p f) : C21_12 p f :=
  c21_12_of_thompson p f (l7_17_of_inputs (l7_10_of_inputs h1 h2 h3) h752 h5) h1 h752

end Exclude

end CFSG.ClassicalInvolution.Asc77
