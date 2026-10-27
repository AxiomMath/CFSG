module

public import CFSG.ClassicalInvolution.Asc77.AscP1Lem79
public import CFSG.ClassicalInvolution.Asc77.AscP1LemMod
public import CFSG.ClassicalInvolution.Asc77.AscT7DMu
public import CFSG.ClassicalInvolution.Asc77.AscT7DPerm

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T7E

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

structure Frame4 (Ω : Set (Subgroup G)) (W : Subgroup G) where
  ρ : Thompson.Rep Ω W
  ρ' : Thompson.Rep Ω W
  ρ₃ : Thompson.Rep Ω W
  z : G
  j : G
  hz : IsUniqueInvolution ρ.K z
  hz' : IsUniqueInvolution ρ'.K z
  hj : IsUniqueInvolution ρ₃.K j
  hnbr : ρ'.K ∈ omegaNbr Ω ρ.K
  hnbr' : ρ.K ∈ omegaNbr Ω ρ'.K
  hne₁ : ρ.K ≠ ρ₃.K
  hne₂ : ρ'.K ≠ ρ₃.K
  hn₁ : ρ₃.K ∉ omegaNbr Ω ρ.K
  hn₂ : ρ₃.K ∉ omegaNbr Ω ρ'.K
  hn₁' : ρ.K ∉ omegaNbr Ω ρ₃.K
  hn₂' : ρ'.K ∉ omegaNbr Ω ρ₃.K

theorem exists_frame4 [IsSimpleGroup G] {K K' : Subgroup G} {z : G}
    (hs : Hyp23Setting p f Ω K K' z) (hW : W ∈ WSet Ω) (hzW : z ∈ W) (hS4 : MuIsoS4 Ω W) :
    ∃ (e : ↥(muGroup Ω W) ≃* Equiv.Perm (Fin 4)) (F : Frame4 Ω W),
      (∀ x, x ∈ Thompson.muDelta Ω W ↔ (e x).IsSwap) ∧ F.ρ.K = K ∧ F.ρ'.K = K' ∧ F.z = z ∧
      T7D.imgQ F.ρ ≠ T7D.imgQ F.ρ' ∧
      T7D.imgQ F.ρ * T7D.imgQ F.ρ' = T7D.imgQ F.ρ' * T7D.imgQ F.ρ ∧
      T7D.imgQ F.ρ * T7D.imgQ F.ρ₃ ≠ T7D.imgQ F.ρ₃ * T7D.imgQ F.ρ ∧
      T7D.imgQ F.ρ' * T7D.imgQ F.ρ₃ ≠ T7D.imgQ F.ρ₃ * T7D.imgQ F.ρ' := by
  have hst : AscStand p f Ω K := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hs.hK'
  have c : Thompson.Ctx p f Ω W := T7D.ctx_of_stand hst hW
  obtain ⟨e, he⟩ := T7D.exists_swap_equiv hs hW hS4
  obtain ⟨S, R, R', hWS, hRsyl, hR'syl, hRS, hR'S⟩ := T7D.exists_sylow_frame hs hW hzW
  have hRD : R ∈ DSet Ω W :=
    Thompson.mem_DSet_of_le_sylow hp hq hΩ hW hWS (mem_RSet_of_isSylow2In hK hRsyl) hRS
  have hR'D : R' ∈ DSet Ω W :=
    Thompson.mem_DSet_of_le_sylow hp hq hΩ hW hWS (mem_RSet_of_isSylow2In hK' hR'syl) hR'S
  obtain ⟨ρ, hρK, -⟩ := T7D.exists_rep hp hq hΩ hW hK hRsyl hRD
  obtain ⟨ρ', hρ'K, -⟩ := T7D.exists_rep hp hq hΩ hW hK' hR'syl hR'D
  have hzρ : IsUniqueInvolution ρ.K z := by rw [hρK]; exact hz
  have hzρ' : IsUniqueInvolution ρ'.K z := by rw [hρ'K]; exact hz'
  have hne : ρ.K ≠ ρ'.K := by
    rw [hρK, hρ'K]
    exact hs.hne.symm
  have hρnbr : ρ'.K ∈ omegaNbr Ω ρ.K := by
    have hperp : K' ∈ KPerp Ω K := by rw [hs.perp]; exact Or.inr rfl
    rw [hρK, hρ'K]
    rcases hperp with e | e
    · exact absurd e hs.hne
    · exact e
  have hcomm : ρ.img * ρ'.img = ρ'.img * ρ.img := c.comm_of_omega ρ ρ' hρnbr
  have hρnbr' : ρ.K ∈ omegaNbr Ω ρ'.K := c.omega_of_comm ρ' ρ hne.symm hcomm.symm
  have hab : T7D.imgQ ρ ≠ T7D.imgQ ρ' := fun h =>
    hne (c.K_eq_of_img_eq ρ ρ' (congrArg Subtype.val h))
  have hcommQ : T7D.imgQ ρ * T7D.imgQ ρ' = T7D.imgQ ρ' * T7D.imgQ ρ := Subtype.ext hcomm
  obtain ⟨c₃, hc₃Δ, hac, hbc⟩ :=
    S4.exists_third he (T7D.imgQ_mem ρ) (T7D.imgQ_mem ρ') hab hcommQ
  obtain ⟨ρ₃, hρ₃⟩ := Thompson.exists_rep_of_mem_muDelta hc₃Δ
  have hc₃ : T7D.imgQ ρ₃ = c₃ := Subtype.ext hρ₃
  have hac' : T7D.imgQ ρ * T7D.imgQ ρ₃ ≠ T7D.imgQ ρ₃ * T7D.imgQ ρ := by rw [hc₃]; exact hac
  have hbc' : T7D.imgQ ρ' * T7D.imgQ ρ₃ ≠ T7D.imgQ ρ₃ * T7D.imgQ ρ' := by rw [hc₃]; exact hbc
  have hne₁ : ρ.K ≠ ρ₃.K := fun h => hac' (by
    have h1 : T7D.imgQ ρ = T7D.imgQ ρ₃ := Subtype.ext (c.img_eq_of_K_eq ρ ρ₃ h)
    rw [← h1])
  have hne₂ : ρ'.K ≠ ρ₃.K := fun h => hbc' (by
    have h1 : T7D.imgQ ρ' = T7D.imgQ ρ₃ := Subtype.ext (c.img_eq_of_K_eq ρ' ρ₃ h)
    rw [← h1])
  obtain ⟨j, hj⟩ := hΩ.exists_uniqueInvolution hp hq ρ₃.hK
  refine ⟨e, ⟨ρ, ρ', ρ₃, z, j, hzρ, hzρ', hj, hρnbr, hρnbr', hne₁, hne₂, ?_, ?_, ?_, ?_⟩, he,
    hρK, hρ'K, rfl, hab, hcommQ, hac', hbc'⟩
  · exact fun h => hac' (Subtype.ext (c.comm_of_omega ρ ρ₃ h))
  · exact fun h => hbc' (Subtype.ext (c.comm_of_omega ρ' ρ₃ h))
  · exact fun h => hac' (Subtype.ext (c.comm_of_omega ρ₃ ρ h).symm)
  · exact fun h => hbc' (Subtype.ext (c.comm_of_omega ρ₃ ρ' h).symm)

theorem swap_word_cases {Q : Type*} [Group Q] {Δ : Set Q} {e : Q ≃* Equiv.Perm (Fin 4)}
    (he : ∀ x, x ∈ Δ ↔ (e x).IsSwap) {a b c : Q} (ha : a ∈ Δ) (hb : b ∈ Δ) (hc : c ∈ Δ)
    (hab : a ≠ b) (hcomm : a * b = b * a) (hac : a * c ≠ c * a) {x : Q} (hx : x ∈ Δ) :
    x = a ∨ x = b ∨ x = c ∨ x = a * c * a ∨ x = b * c * b ∨ x = a * b * c * b * a := by
  have h := S4.swap_word (e a) (S4.mem_swaps4_of_mem he ha) (e b) (S4.mem_swaps4_of_mem he hb)
    (e c) (S4.mem_swaps4_of_mem he hc) (fun h => hab (e.injective h))
    (by rw [← map_mul, ← map_mul, hcomm])
    (fun h => hac (e.injective (by rw [map_mul, map_mul, h]))) (e x)
    (S4.mem_swaps4_of_mem he hx)
  rcases h with h | h | h | h | h | h
  · exact Or.inl (e.injective h)
  · exact Or.inr (Or.inl (e.injective h))
  · exact Or.inr (Or.inr (Or.inl (e.injective h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (e.injective (by rw [h, map_mul, map_mul])))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (e.injective (by rw [h, map_mul, map_mul]))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (e.injective (by rw [h, map_mul, map_mul, map_mul, map_mul]))))))

omit [Finite G] in
theorem conjSub_inf_W {m : G} (hm : m ∈ Subgroup.normalizer (W : Set G)) (A : Subgroup G) :
    conjSub m A ⊓ W = conjSub m (A ⊓ W) := by
  have hW : conjSub m W = W := mem_normalizer_iff_conjSub_eq.mp hm
  have hx : ∀ x, x ∈ W ↔ m⁻¹ * x * m ∈ W := fun x => by rw [← mem_conjSub_iff, hW]
  ext x
  simp only [Subgroup.mem_inf, mem_conjSub_iff]
  rw [← hx x]

theorem inf_W_conj_of_img (c : Thompson.Ctx p f Ω W) {m : G}
    (hm : m ∈ Subgroup.normalizer (W : Set G)) (σ ρ₀ : Thompson.Rep Ω W)
    (h : σ.img = Thompson.piG W m * ρ₀.img * (Thompson.piG W m)⁻¹) :
    σ.K ⊓ W = conjSub m (ρ₀.K ⊓ W) := by
  have hK : σ.K = conjSub m ρ₀.K :=
    c.K_eq_of_img_eq σ (T7D.conjRep c.hΩ hm ρ₀) (by rw [T7D.conjRep_img]; exact h)
  rw [hK, conjSub_inf_W hm]

namespace Frame4

omit [Finite G] in
theorem mem_inf_of_mem_inf {ρ : Thompson.Rep Ω W} {x : G} (hx : x ∈ ρ.R ⊓ W) : x ∈ ρ.K ⊓ W :=
  ⟨ρ.hRK.1 hx.1, hx.2⟩

theorem exists_gens (c : Thompson.Ctx p f Ω W) (F : Frame4 Ω W) :
    ∃ x₁ x₂ x₃ : G, Subgroup.zpowers x₁ = F.ρ.R ⊓ W ∧ Subgroup.zpowers x₂ = F.ρ'.R ⊓ W ∧
    Subgroup.zpowers x₃ = F.ρ₃.R ⊓ W ∧
    F.ρ.r * x₁ * F.ρ.r⁻¹ = x₁⁻¹ ∧ F.ρ.r * x₂ * F.ρ.r⁻¹ = x₂ ∧ F.ρ.r * x₃ * F.ρ.r⁻¹ = x₃ * x₁ ∧
    F.ρ'.r * x₁ * F.ρ'.r⁻¹ = x₁ ∧ F.ρ'.r * x₂ * F.ρ'.r⁻¹ = x₂⁻¹ ∧
    F.ρ'.r * x₃ * F.ρ'.r⁻¹ = x₃ * x₂ ∧
    F.ρ₃.r * x₁ * F.ρ₃.r⁻¹ = x₁ * x₃ ∧ F.ρ₃.r * x₂ * F.ρ₃.r⁻¹ = x₂ * x₃ ∧
    F.ρ₃.r * x₃ * F.ρ₃.r⁻¹ = x₃⁻¹ := by
  obtain ⟨x₁, h₁⟩ := Thompson.exists_zpowers_eq_inf_W c.hp c.hq c.hΩ c.hW F.ρ.hR
  obtain ⟨v₂, hv₂⟩ := Thompson.exists_zpowers_eq_inf_W c.hp c.hq c.hΩ c.hW F.ρ'.hR
  obtain ⟨v₃, hv₃⟩ := Thompson.exists_zpowers_eq_inf_W c.hp c.hq c.hΩ c.hW F.ρ₃.hR
  obtain ⟨x₃, hx₃, hs₁, hr₃⟩ := c.rel_exact F.hne₁ F.hn₁ h₁ hv₃
  have h₃ : Subgroup.zpowers x₃ = F.ρ₃.R ⊓ W := hx₃.trans hv₃
  obtain ⟨x₂, hx₂, ht₃, hs₂⟩ := c.rel_exact (F.hne₂.symm) F.hn₂' h₃ hv₂
  have h₂ : Subgroup.zpowers x₂ = F.ρ'.R ⊓ W := hx₂.trans hv₂
  have m₁ : x₁ ∈ F.ρ.K ⊓ W := mem_inf_of_mem_inf (h₁ ▸ Subgroup.mem_zpowers x₁)
  have m₂ : x₂ ∈ F.ρ'.K ⊓ W := mem_inf_of_mem_inf (h₂ ▸ Subgroup.mem_zpowers x₂)
  have m₃ : x₃ ∈ F.ρ₃.K ⊓ W := mem_inf_of_mem_inf (h₃ ▸ Subgroup.mem_zpowers x₃)
  have cen : ∀ (ρ σ : Thompson.Rep Ω W), σ.K ∈ omegaNbr Ω ρ.K → ∀ {x : G}, x ∈ σ.K ⊓ W →
      ρ.r * x * ρ.r⁻¹ = x := fun ρ σ hnbr x hx => by
    rw [c.centralizes ρ σ hnbr hx]
    group
  refine ⟨x₁, x₂, x₃, h₁, h₂, h₃, c.conj_inv F.ρ m₁, cen _ _ F.hnbr m₂, hr₃,
    cen _ _ F.hnbr' m₁, c.conj_inv F.ρ' m₂, ht₃, hs₁, hs₂, c.conj_inv F.ρ₃ m₃⟩

omit [Finite G] in
theorem pow_half_eq {K : Subgroup G} {z x : G} (hz : IsUniqueInvolution K z) (hx : x ∈ K) {m : ℕ}
    (hm : 0 < m) (hord : orderOf x = 4 * m) : x ^ (2 * m) = z := by
  have h4 : x ^ (4 * m) = 1 := by rw [← hord]; exact pow_orderOf_eq_one x
  have hg : x ^ (2 * m) * x ^ (2 * m) = 1 := by
    rw [← pow_add, show 2 * m + 2 * m = 4 * m by ring]; exact h4
  rcases hz.unique (x ^ (2 * m)) (K.pow_mem hx _) hg with h | h
  · exfalso
    have hd := orderOf_dvd_of_pow_eq_one h
    rw [hord] at hd
    have := Nat.le_of_dvd (by omega) hd
    omega
  · exact h

theorem orders (c : Thompson.Ctx p f Ω W) (F : Frame4 Ω W) {x₁ x₂ x₃ : G}
    (h₁ : Subgroup.zpowers x₁ = F.ρ.R ⊓ W) (h₂ : Subgroup.zpowers x₂ = F.ρ'.R ⊓ W)
    (h₃ : Subgroup.zpowers x₃ = F.ρ₃.R ⊓ W) :
    ∃ m : ℕ, 0 < m ∧ orderOf x₁ = 4 * m ∧ orderOf x₂ = 4 * m ∧ orderOf x₃ = 4 * m ∧
      x₁ ^ (2 * m) = F.z ∧ x₂ ^ (2 * m) = F.z ∧ x₃ ^ (2 * m) = F.j := by
  have hord : ∀ (ρ : Thompson.Rep Ω W) (x : G), Subgroup.zpowers x = ρ.R ⊓ W →
      2 * orderOf x = Nat.card ρ.R := by
    intro ρ x hx
    have h1 : orderOf x = Nat.card ↥(ρ.R ⊓ W) := by rw [← Nat.card_zpowers, hx]
    rw [h1]
    exact (Thompson.D_card c.hp c.hq c.hΩ c.hW ρ.hR).symm
  obtain ⟨N, hcard⟩ : ∃ N : ℕ, ∀ ρ : Thompson.Rep Ω W, Nat.card ρ.R = 2 ^ N :=
    ⟨_, fun ρ => c.hΩ.natCard_isSylow2In ρ.hK ρ.hRK⟩
  have h4 : 4 ≤ orderOf x₁ := by
    have := (Thompson.inf_W_of_mem_D c.hp c.hq c.hΩ c.hW F.ρ.hR F.ρ.hK F.ρ.hRK).2.2.2.1
    rwa [← h₁, Nat.card_zpowers] at this
  have e₁ := hord F.ρ x₁ h₁
  have e₂ := hord F.ρ' x₂ h₂
  have e₃ := hord F.ρ₃ x₃ h₃
  rw [hcard] at e₁ e₂ e₃
  have hN3 : 3 ≤ N := by
    by_contra hlt
    have : 2 ^ N ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨k, hk⟩ : ∃ k, N = k + 3 := ⟨N - 3, by omega⟩
  have hpow : (2 : ℕ) ^ N = 8 * 2 ^ k := by rw [hk, pow_add]; ring
  have hm : 0 < 2 ^ k := pow_pos (by norm_num) k
  have o₁ : orderOf x₁ = 4 * 2 ^ k := by omega
  have o₂ : orderOf x₂ = 4 * 2 ^ k := by omega
  have o₃ : orderOf x₃ = 4 * 2 ^ k := by omega
  have m₁ : x₁ ∈ F.ρ.K := F.ρ.hRK.1 (h₁ ▸ Subgroup.mem_zpowers x₁ : x₁ ∈ F.ρ.R ⊓ W).1
  have m₂ : x₂ ∈ F.ρ'.K := F.ρ'.hRK.1 (h₂ ▸ Subgroup.mem_zpowers x₂ : x₂ ∈ F.ρ'.R ⊓ W).1
  have m₃ : x₃ ∈ F.ρ₃.K := F.ρ₃.hRK.1 (h₃ ▸ Subgroup.mem_zpowers x₃ : x₃ ∈ F.ρ₃.R ⊓ W).1
  exact ⟨2 ^ k, hm, o₁, o₂, o₃, pow_half_eq F.hz m₁ hm o₁, pow_half_eq F.hz' m₂ hm o₂,
    pow_half_eq F.hj m₃ hm o₃⟩

omit [Finite G] in
theorem conjSub_zpowers' (x g : G) :
    conjSub x (Subgroup.zpowers g) = Subgroup.zpowers (x * g * x⁻¹) := by
  unfold conjSub
  rw [MonoidHom.map_zpowers]
  rfl

theorem W_le_closure (c : Thompson.Ctx p f Ω W) (F : Frame4 Ω W)
    {e : ↥(muGroup Ω W) ≃* Equiv.Perm (Fin 4)}
    (he : ∀ x, x ∈ Thompson.muDelta Ω W ↔ (e x).IsSwap)
    (hab : T7D.imgQ F.ρ ≠ T7D.imgQ F.ρ')
    (hcomm : T7D.imgQ F.ρ * T7D.imgQ F.ρ' = T7D.imgQ F.ρ' * T7D.imgQ F.ρ)
    (hac : T7D.imgQ F.ρ * T7D.imgQ F.ρ₃ ≠ T7D.imgQ F.ρ₃ * T7D.imgQ F.ρ) {x₁ x₂ x₃ : G}
    (h₁ : Subgroup.zpowers x₁ = F.ρ.R ⊓ W) (h₂ : Subgroup.zpowers x₂ = F.ρ'.R ⊓ W)
    (h₃ : Subgroup.zpowers x₃ = F.ρ₃.R ⊓ W) (r₂ : F.ρ.r * x₂ * F.ρ.r⁻¹ = x₂)
    (r₃ : F.ρ.r * x₃ * F.ρ.r⁻¹ = x₃ * x₁)
    (t₃ : F.ρ'.r * x₃ * F.ρ'.r⁻¹ = x₃ * x₂) :
    W ≤ Subgroup.closure ({x₁, x₂, x₃} : Set G) := by
  set Wc := Subgroup.closure ({x₁, x₂, x₃} : Set G) with hWc
  have hx₁ : x₁ ∈ Wc := Subgroup.subset_closure (by simp)
  have hx₂ : x₂ ∈ Wc := Subgroup.subset_closure (by simp)
  have hx₃ : x₃ ∈ Wc := Subgroup.subset_closure (by simp)
  have hKW : ∀ ρ : Thompson.Rep Ω W, ρ.K ⊓ W = ρ.R ⊓ W := fun ρ =>
    (Thompson.inf_W_of_mem_D c.hp c.hq c.hΩ c.hW ρ.hR ρ.hK ρ.hRK).1.symm
  have hsq : ∀ ρ : Thompson.Rep Ω W, ρ.img * ρ.img = 1 := fun ρ =>
    congrArg Subtype.val
      (Thompson.muDelta_mul_self c.hp c.hq c.hΩ c.hW (T7D.imgQ_mem ρ))
  have hinv : ∀ ρ : Thompson.Rep Ω W, ρ.img⁻¹ = ρ.img := fun ρ =>
    inv_eq_of_mul_eq_one_right (hsq ρ)
  have key : ∀ σ : Thompson.Rep Ω W, σ.K ⊓ W ≤ Wc := by
    intro σ
    rcases swap_word_cases he (T7D.imgQ_mem F.ρ) (T7D.imgQ_mem F.ρ') (T7D.imgQ_mem F.ρ₃) hab
      hcomm hac (T7D.imgQ_mem σ) with h | h | h | h | h | h
    · rw [c.K_eq_of_img_eq σ F.ρ (congrArg Subtype.val h), hKW, ← h₁]
      exact Subgroup.zpowers_le.mpr hx₁
    · rw [c.K_eq_of_img_eq σ F.ρ' (congrArg Subtype.val h), hKW, ← h₂]
      exact Subgroup.zpowers_le.mpr hx₂
    · rw [c.K_eq_of_img_eq σ F.ρ₃ (congrArg Subtype.val h), hKW, ← h₃]
      exact Subgroup.zpowers_le.mpr hx₃
    · have e1 : σ.img = F.ρ.img * F.ρ₃.img * F.ρ.img := congrArg Subtype.val h
      have hval : σ.img = Thompson.piG W F.ρ.r * F.ρ₃.img * (Thompson.piG W F.ρ.r)⁻¹ := by
        show σ.img = F.ρ.img * F.ρ₃.img * F.ρ.img⁻¹
        rw [hinv]
        exact e1
      rw [inf_W_conj_of_img c F.ρ.r_mem_normalizer σ F.ρ₃ hval, hKW, ← h₃, conjSub_zpowers', r₃]
      exact Subgroup.zpowers_le.mpr (Wc.mul_mem hx₃ hx₁)
    · have e1 : σ.img = F.ρ'.img * F.ρ₃.img * F.ρ'.img := congrArg Subtype.val h
      have hval : σ.img = Thompson.piG W F.ρ'.r * F.ρ₃.img * (Thompson.piG W F.ρ'.r)⁻¹ := by
        show σ.img = F.ρ'.img * F.ρ₃.img * F.ρ'.img⁻¹
        rw [hinv]
        exact e1
      rw [inf_W_conj_of_img c F.ρ'.r_mem_normalizer σ F.ρ₃ hval, hKW, ← h₃, conjSub_zpowers', t₃]
      exact Subgroup.zpowers_le.mpr (Wc.mul_mem hx₃ hx₂)
    · have e1 : σ.img = F.ρ.img * F.ρ'.img * F.ρ₃.img * F.ρ'.img * F.ρ.img :=
        congrArg Subtype.val h
      have hm : F.ρ.r * F.ρ'.r ∈ Subgroup.normalizer (W : Set G) :=
        Subgroup.mul_mem _ F.ρ.r_mem_normalizer F.ρ'.r_mem_normalizer
      have hpm : Thompson.piG W (F.ρ.r * F.ρ'.r) = F.ρ.img * F.ρ'.img :=
        Thompson.piG_mul F.ρ.r_mem_normalizer F.ρ'.r_mem_normalizer
      have hval : σ.img = Thompson.piG W (F.ρ.r * F.ρ'.r) * F.ρ₃.img *
          (Thompson.piG W (F.ρ.r * F.ρ'.r))⁻¹ := by
        rw [hpm, mul_inv_rev, hinv, hinv, e1]
        simp only [mul_assoc]
      rw [inf_W_conj_of_img c hm σ F.ρ₃ hval, hKW, ← h₃, conjSub_zpowers']
      have : (F.ρ.r * F.ρ'.r) * x₃ * (F.ρ.r * F.ρ'.r)⁻¹ = x₃ * x₁ * x₂ := by
        calc (F.ρ.r * F.ρ'.r) * x₃ * (F.ρ.r * F.ρ'.r)⁻¹
            = F.ρ.r * (F.ρ'.r * x₃ * F.ρ'.r⁻¹) * F.ρ.r⁻¹ := by group
          _ = F.ρ.r * (x₃ * x₂) * F.ρ.r⁻¹ := by rw [t₃]
          _ = (F.ρ.r * x₃ * F.ρ.r⁻¹) * (F.ρ.r * x₂ * F.ρ.r⁻¹) := by group
          _ = x₃ * x₁ * x₂ := by rw [r₃, r₂]
      rw [this]
      exact Subgroup.zpowers_le.mpr (Wc.mul_mem (Wc.mul_mem hx₃ hx₁) hx₂)
  obtain ⟨η, ⟨S₀, hη, -⟩, hWη⟩ := c.hW
  obtain ⟨S, hWS⟩ := Thompson.exists_sylow_ge_of_mem_WSet c.hW
  have hηW : ∀ V ∈ η, V ≤ W := fun V hV => hWη ▸ le_iSup₂ (f := fun U (_ : U ∈ η) => U) V hV
  intro w hw
  rw [hWη] at hw
  refine (iSup₂_le (fun V hV => ?_) : (⨆ V ∈ η, V : Subgroup G) ≤ Wc) hw
  have hVU : V ∈ USet Ω := (hη.1 hV).1
  obtain ⟨J, hJ, hVJ⟩ := c.hΩ.exists_member_of_mem_USet c.hp hVU
  obtain ⟨T, hTD, hTJ⟩ := Thompson.exists_sylow_mem_DSet c.hp c.hq c.hΩ c.hW hWS hJ hVU hVJ
    ((hηW V hV).trans hWS)
  obtain ⟨σ, hσK, -⟩ := T7D.exists_rep c.hp c.hq c.hΩ c.hW hJ hTJ hTD
  have := key σ
  rw [hσK] at this
  exact (le_inf hVJ (hηW V hV)).trans this

omit [Finite G] in
theorem commutes_of_mem_centerIn {R : Subgroup G} {a : G} (ha : a ∈ centerIn R) {g : G}
    (hg : g ∈ R) : g * a = a * g := by
  obtain ⟨y, hy, rfl⟩ := ha
  have := Subgroup.mem_center_iff.mp hy ⟨g, hg⟩
  exact congrArg Subtype.val this

theorem exists_structure (c : Thompson.Ctx p f Ω W) (F : Frame4 Ω W)
    {e : ↥(muGroup Ω W) ≃* Equiv.Perm (Fin 4)}
    (he : ∀ x, x ∈ Thompson.muDelta Ω W ↔ (e x).IsSwap)
    (hab : T7D.imgQ F.ρ ≠ T7D.imgQ F.ρ')
    (hcomm : T7D.imgQ F.ρ * T7D.imgQ F.ρ' = T7D.imgQ F.ρ' * T7D.imgQ F.ρ)
    (hac : T7D.imgQ F.ρ * T7D.imgQ F.ρ₃ ≠ T7D.imgQ F.ρ₃ * T7D.imgQ F.ρ) :
    ∃ (x₁ x₂ x₃ : G) (m : ℕ), 0 < m ∧ Subgroup.zpowers x₁ = F.ρ.R ⊓ W ∧
      Subgroup.zpowers x₂ = F.ρ'.R ⊓ W ∧ Subgroup.zpowers x₃ = F.ρ₃.R ⊓ W ∧
      orderOf x₁ = 4 * m ∧ orderOf x₂ = 4 * m ∧ orderOf x₃ = 4 * m ∧ x₁ ^ (2 * m) = F.z ∧
      x₂ ^ (2 * m) = F.z ∧ x₃ ^ (2 * m) = F.j ∧
      x₁ ∈ F.ρ.K ∧ x₂ ∈ F.ρ'.K ∧ x₃ ∈ F.ρ₃.K ∧
      (∀ a ∈ W ⊓ centerIn (Subgroup.normalizer (W : Set G)),
        a = 1 ∨ a = (x₁ * x₂⁻¹ * x₃ ^ 2) ^ m) := by
  obtain ⟨x₁, x₂, x₃, h₁, h₂, h₃, r₁, r₂, r₃, t₁, t₂, t₃, s₁, s₂, s₃⟩ := F.exists_gens c
  obtain ⟨m, hm, o₁, o₂, o₃, z₁, z₂, z₃⟩ := F.orders c h₁ h₂ h₃
  have hgen : W ≤ Subgroup.closure ({x₁, x₂, x₃} : Set G) :=
    F.W_le_closure c he hab hcomm hac h₁ h₂ h₃ r₂ r₃ t₃
  have m₁ : x₁ ∈ W := (h₁ ▸ Subgroup.mem_zpowers x₁ : x₁ ∈ F.ρ.R ⊓ W).2
  have m₂ : x₂ ∈ W := (h₂ ▸ Subgroup.mem_zpowers x₂ : x₂ ∈ F.ρ'.R ⊓ W).2
  have m₃ : x₃ ∈ W := (h₃ ▸ Subgroup.mem_zpowers x₃ : x₃ ∈ F.ρ₃.R ⊓ W).2
  have k₁ : x₁ ∈ F.ρ.K := F.ρ.hRK.1 (h₁ ▸ Subgroup.mem_zpowers x₁ : x₁ ∈ F.ρ.R ⊓ W).1
  have k₂ : x₂ ∈ F.ρ'.K := F.ρ'.hRK.1 (h₂ ▸ Subgroup.mem_zpowers x₂ : x₂ ∈ F.ρ'.R ⊓ W).1
  have k₃ : x₃ ∈ F.ρ₃.K := F.ρ₃.hRK.1 (h₃ ▸ Subgroup.mem_zpowers x₃ : x₃ ∈ F.ρ₃.R ⊓ W).1
  refine ⟨x₁, x₂, x₃, m, hm, h₁, h₂, h₃, o₁, o₂, o₃, z₁, z₂, z₃, k₁, k₂, k₃, ?_⟩
  intro a ha
  refine A3Mod.fixed_eq_one_or (show Commute x₁ x₂ from c.comm_W _ m₁ _ m₂)
    (show Commute x₁ x₃ from c.comm_W _ m₁ _ m₃) (show Commute x₂ x₃ from c.comm_W _ m₂ _ m₃)
    o₁ o₂ o₃ (z₁.trans z₂.symm) r₁ r₂ r₃ t₁ t₂ t₃ s₁ s₂ s₃ (hgen ha.1) ?_ ?_ ?_
  · rw [commutes_of_mem_centerIn ha.2 F.ρ.r_mem_normalizer]; group
  · rw [commutes_of_mem_centerIn ha.2 F.ρ'.r_mem_normalizer]; group
  · rw [commutes_of_mem_centerIn ha.2 F.ρ₃.r_mem_normalizer]; group

end Frame4

end T7E

end CFSG.ClassicalInvolution.Asc77
