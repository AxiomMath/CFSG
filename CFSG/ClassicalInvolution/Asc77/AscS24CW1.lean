module

public import CFSG.ClassicalInvolution.Asc77.AscS24CQuat
public import CFSG.ClassicalInvolution.Asc77.AscS24BCyc1
public import CFSG.ClassicalInvolution.Asc77.AscT7K2

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace S24

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}


variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : S24B.Ctx8 p f Ω K K' W S R R' z u)

include C in
theorem exists_conj_W {W₁ : Subgroup G} (hW₁ : W₁ ∈ WSet Ω) : ∃ h : G, conjSub h W = W₁ := by
  have hst := C.hs.stand
  obtain ⟨η, hηG, hWη⟩ := id C.hd.hW
  obtain ⟨S₀, hηS₀, hinv⟩ := id hηG
  have hUS₀ : ∀ U ∈ η, U ≤ (S₀ : Subgroup G) := fun U hU => (hηS₀.1 hU).2
  have hWS₀ : W ≤ (S₀ : Subgroup G) := by
    rw [hWη]; exact iSup₂_le fun U hU => hUS₀ U hU
  have hP : PartIHyp p f Ω := ⟨hst.odd, hst.five, hst.hyp, hst.aEmpty⟩
  have htr : ∀ K₁ ∈ Ω, ∀ J ∈ Ω, ∃ g : G, conjSub g K₁ = J := by
    intro K₁ hK₁ J hJ
    obtain ⟨g₁, rfl⟩ := hst.trans K₁ hK₁
    obtain ⟨g₂, rfl⟩ := hst.trans J hJ
    exact ⟨g₂ * g₁⁻¹, by rw [conjSub_mul, conjSub_inv_conjSub]⟩
  have h612 := AschTight.Sec7.l6_12_mod p f G Ω hP htr S₀
  dsimp only at h612
  rcases h612 with ⟨η₀, -, -, huniq, -⟩ | h2
  · have hMS₀ : (⨆ U ∈ {U : Subgroup G | (∃ η ∈ etaG Ω, U ∈ η) ∧ U ≤ (S₀ : Subgroup G)}, U) ≤
        (S₀ : Subgroup G) := iSup₂_le fun U hU => hU.2
    have hηeq : η = η₀ := huniq η hηG fun m hm U hU => hinv m (hMS₀ hm) U hU
    obtain ⟨η₁, ⟨S₁, hS₁, hinv₁⟩, rfl⟩ := hW₁
    obtain ⟨x, hx⟩ := exists_conjSub_eq_of_sylow S₁ S₀
    have hinv₁' : ∀ s ∈ (S₀ : Subgroup G), ∀ U ∈ conjSub x '' η₁,
        conjSub s U ∈ conjSub x '' η₁ := by
      intro s hs U hU
      obtain ⟨U₀, hU₀, rfl⟩ := hU
      have hs' : x⁻¹ * s * x ∈ (S₁ : Subgroup G) := by
        rw [← hx, mem_conjSub_iff] at hs
        exact hs
      refine ⟨conjSub (x⁻¹ * s * x) U₀, hinv₁ _ hs' U₀ hU₀, ?_⟩
      rw [← conjSub_mul, ← conjSub_mul]
      congr 1
      group
    have hη₁' : conjSub x '' η₁ ∈ etaG Ω := by
      refine ⟨S₀, ?_, hinv₁'⟩
      have := conjSub_image_mem_etaSet hst.hyp.conjInvariant hS₁ x
      rwa [hx] at this
    have hη₁eq : conjSub x '' η₁ = η₀ :=
      huniq _ hη₁' fun m hm U hU => hinv₁' m (hMS₀ hm) U hU
    refine ⟨x⁻¹, ?_⟩
    have e : conjSub x (⨆ U ∈ η₁, U) = W := by
      have e1 : conjSub x (⨆ U ∈ η₁, U) = ⨆ U ∈ conjSub x '' η₁, U := by
        rw [conjSub_iSup₂, iSup_image]
      rw [e1, hη₁eq, ← hηeq, hWη]
    rw [← e, conjSub_inv_conjSub]
  · exact (C.not_alt_two hWS₀ h2).elim

theorem inv_W {w : G} (hw : w ∈ W) (h2 : w * w = 1) :
    w = 1 ∨ w = z ∨ w = C.D.F.j ∨ w = z * C.D.F.j := by
  obtain ⟨a, b, rfl⟩ := C.exists_nf hw
  rw [C.mul_nf] at h2
  obtain ⟨h1, h3⟩ := C.eq_one_of_nf _ _ h2
  have ha := C.four_dvd_of_x₁ h1
  have hb := C.four_dvd_of_x₃ h3
  have hx₁ : ∀ c : ℤ, C.D.x₁ ^ c = C.D.x₁ ^ (c % 4) := fun c => by
    have e := zpow_mod_orderOf C.D.x₁ c
    rw [C.orderOf_x₁] at e
    exact_mod_cast e.symm
  have hx₃ : ∀ c : ℤ, C.D.x₃ ^ c = C.D.x₃ ^ (c % 4) := fun c => by
    have e := zpow_mod_orderOf C.D.x₃ c
    rw [C.orderOf_x₃] at e
    exact_mod_cast e.symm
  have hz2 : C.D.x₁ ^ (2 : ℤ) = z := by rw [zpow_two, ← pow_two, C.x₁_sq]
  have hj2 : C.D.x₃ ^ (2 : ℤ) = C.D.F.j := by rw [zpow_two, ← pow_two, C.x₃_sq]
  have ha' : a % 4 = 0 ∨ a % 4 = 2 := by omega
  have hb' : b % 4 = 0 ∨ b % 4 = 2 := by omega
  rw [hx₁ a, hx₃ b]
  rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb' <;> rw [ha', hb']
  · left; simp
  · right; right; left; rw [zpow_zero, one_mul, hj2]
  · right; left; rw [zpow_zero, mul_one, hz2]
  · right; right; right; rw [hz2, hj2]

include C in
theorem exists_normalizer_conj_z {w : G} (hw : w ∈ W) (h2 : w * w = 1) (h1 : w ≠ 1) :
    ∃ g ∈ Subgroup.normalizer (W : Set G), g * z * g⁻¹ = w := by
  have hrN := C.D.F.ρ.r_mem_normalizer
  have hsN := C.D.F.ρ₃.r_mem_normalizer
  have hzj : z * C.D.F.j = C.D.F.j * z := by
    have := Thompson.commutes_of_mem_WSet C.D.c.hp C.D.c.hq C.D.c.hΩ C.D.c.hW z C.hd.hzW
      C.D.F.j (by rw [← C.x₃_sq]; exact W.pow_mem C.D.x₃_mem 2)
    exact this
  have hrz : C.D.F.ρ.r * z * C.D.F.ρ.r⁻¹ = z :=
    C.hzK.conj_eq (conjSub_eq_self_of_mem C.r_mem_K)
  have hrj : C.D.F.ρ.r * C.D.F.j * C.D.F.ρ.r⁻¹ = C.D.F.j * z := by
    rw [← C.x₃_sq, ← conj_pow, C.D.r₃, C.D.comm13.symm.mul_pow, C.x₁_sq]
  rcases inv_W C hw h2 with h | h | h | h
  · exact absurd h h1
  · exact ⟨1, Subgroup.one_mem _, by rw [h]; group⟩
  · refine ⟨C.D.F.ρ.r * C.D.F.ρ₃.r, Subgroup.mul_mem _ hrN hsN, ?_⟩
    calc C.D.F.ρ.r * C.D.F.ρ₃.r * z * (C.D.F.ρ.r * C.D.F.ρ₃.r)⁻¹
        = C.D.F.ρ.r * (C.D.F.ρ₃.r * z * C.D.F.ρ₃.r⁻¹) * C.D.F.ρ.r⁻¹ := by group
      _ = (C.D.F.ρ.r * z * C.D.F.ρ.r⁻¹) * (C.D.F.ρ.r * C.D.F.j * C.D.F.ρ.r⁻¹) := by
          rw [C.s_conj_z]; group
      _ = z * (C.D.F.j * z) := by rw [hrz, hrj]
      _ = w := by rw [h, ← hzj, ← mul_assoc, C.hzK.sq, one_mul]
  · exact ⟨C.D.F.ρ₃.r, hsN, by rw [h, C.s_conj_z]⟩

include C in
theorem twin_cases {h : G} (hh : h ∈ Subgroup.centralizer ({z} : Set G)) :
    (conjSub h K = K ∧ conjSub h K' = K') ∨ (conjSub h K = K' ∧ conjSub h K' = K) := by
  have hΩ := C.hs.stand.hyp
  have hzh : h * z * h⁻¹ = z := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hh
    rw [hh]
    group
  have hK₁ : conjSub h K ∈ twinSet Ω K :=
    ⟨hΩ.conjInvariant h K C.hs.stand.mem, z, C.hzK, by have := C.hzK.conj h; rwa [hzh] at this⟩
  have hK'₁ : conjSub h K' ∈ twinSet Ω K :=
    ⟨hΩ.conjInvariant h K' C.hs.hK'.1, z, C.hzK, by have := C.hzK'.conj h; rwa [hzh] at this⟩
  rw [C.hs.twinSet_eq] at hK₁ hK'₁
  have hne : conjSub h K ≠ conjSub h K' := fun e => C.hs.hne ((conjSub_inj h).mp e).symm
  rcases hK₁ with h1 | h1 <;> rcases hK'₁ with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (h1.trans h2.symm) hne

include C in
theorem exists_centralizer_conj_W {W₁ : Subgroup G} (hW₁ : W₁ ∈ WSet Ω) (hzW₁ : z ∈ W₁) :
    ∃ h ∈ Subgroup.centralizer ({z} : Set G), conjSub h W = W₁ := by
  obtain ⟨h, rfl⟩ := exists_conj_W C hW₁
  rw [mem_conjSub_iff] at hzW₁
  have h2 : (h⁻¹ * z * h) * (h⁻¹ * z * h) = 1 := by
    calc (h⁻¹ * z * h) * (h⁻¹ * z * h) = h⁻¹ * (z * z) * h := by group
      _ = 1 := by rw [C.hzK.sq]; group
  have h1 : h⁻¹ * z * h ≠ 1 := by
    intro e
    apply C.hzK.ne_one
    calc z = h * (h⁻¹ * z * h) * h⁻¹ := by group
      _ = 1 := by rw [e]; group
  obtain ⟨g, hgN, hg⟩ := exists_normalizer_conj_z C hzW₁ h2 h1
  refine ⟨h * g, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    calc h * g * z = h * (g * z * g⁻¹) * g := by group
      _ = h * (h⁻¹ * z * h) * g := by rw [hg]
      _ = z * (h * g) := by group
  · rw [conjSub_mul, mem_normalizer_iff_conjSub_eq.mp hgN]

include C in
theorem mem_sup_of_W1 {W₁ : Subgroup G} (hW₁ : W₁ ∈ WSet Ω) (hzW₁ : z ∈ W₁) {v : G}
    (hv : v ∈ W₁) (hv2 : v * v = 1) : v ∈ K ⊔ K' := by
  obtain ⟨h, hh, rfl⟩ := exists_centralizer_conj_W C hW₁ hzW₁
  rw [mem_conjSub_iff] at hv
  have hw2 : (h⁻¹ * v * h) * (h⁻¹ * v * h) = 1 := by
    calc (h⁻¹ * v * h) * (h⁻¹ * v * h) = h⁻¹ * (v * v) * h := by group
      _ = 1 := by rw [hv2]; group
  have hmem := T7K.conj_mem_sup C.hs hh (C.mem_sup_of_mul_self hv hw2)
  have e : h * (h⁻¹ * v * h) * h⁻¹ = v := by group
  rwa [e] at hmem

include C in
theorem mem_sup_of_conj_z {g : G} (hne : g * z * g⁻¹ ≠ z)
    (hcomm : (g * z * g⁻¹) * C.D.F.ρ.r = C.D.F.ρ.r * (g * z * g⁻¹)) :
    g * z * g⁻¹ ∈ K ⊔ K' := by
  have hst := C.hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hL : conjSub g K ∈ Ω := hΩ.conjInvariant g K hK
  have hzL : IsUniqueInvolution (conjSub g K) (g * z * g⁻¹) := C.hzK.conj g
  have hLK : conjSub g K ≠ K := by
    intro e
    rw [e] at hzL
    exact hne (hzL.eq C.hzK)
  have hrK : C.D.F.ρ.r ∈ K := C.r_mem_K
  have hor : orderOf C.D.F.ρ.r = 4 :=
    orderOf_of_member hp hΩ hK C.hzK C.hRsyl C.x₁_mem_R C.card_R C.D.F.ρ.r C.r_mem_R
      C.r_not_mem_zpowers
  have hnc : ¬ ∀ w ∈ K, C.D.F.ρ.r * w = w * C.D.F.ρ.r := by
    intro h
    have e := h _ C.x₁_mem_K
    have e2 : C.D.x₁⁻¹ = C.D.x₁ := by
      rw [← C.D.r₁, e]; group
    have e3 : C.D.x₁ ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 1 [← e2]
      exact inv_mul_cancel _
    have := orderOf_dvd_of_pow_eq_one e3
    rw [C.orderOf_x₁] at this
    omega
  have hr2 : IsPGroup 2 ↥(Subgroup.zpowers C.D.F.ρ.r) := T7A.isPGroup_zpowers_of_orderOf_four hor
  have hrN : C.D.F.ρ.r ∈ Subgroup.normalizer (conjSub g K : Set G) :=
    hΩ.omega5 _ hL K hK hLK _ hzL _ hrK hnc hr2 hcomm.symm
  have hU : Subgroup.zpowers C.D.F.ρ.r ∈ USet Ω := by
    refine mem_USet_of_natCard hK C.hRsyl (Subgroup.zpowers_le.mpr C.r_mem_R) inferInstance ?_
    simp [C.h8, Nat.card_zpowers, hor]
  have hKstar : K ∈ omegaStarNbr Ω (conjSub g K) :=
    ⟨hK, hLK.symm, _, hU, Subgroup.zpowers_le.mpr hrK, Subgroup.zpowers_le.mpr hrN⟩
  obtain ⟨W₁, hW₁, R₁, hR₁, T₁, hT₁, hR₁L, hT₁K⟩ :=
    Thompson.exists_W_of_mem_omegaStarNbr hp hq hΩ hL hKstar
  have hzhW : g * z * g⁻¹ ∈ W₁ :=
    (Thompson.uniqueInvolution_mem_W hp hq hΩ hW₁ hL hR₁ hR₁L hzL).2
  have hzW : z ∈ W₁ := (Thompson.uniqueInvolution_mem_W hp hq hΩ hW₁ hK hT₁ hT₁K C.hzK).2
  exact mem_sup_of_W1 C hW₁ hzW hzhW hzL.sq

include C in
theorem exists_sylow_pair_of_le {Y : Subgroup G} (hY : IsPGroup 2 Y) (hYK : Y ≤ K ⊔ K') :
    ∃ R₂ R₂' : Subgroup G, IsSylow2In R₂ K ∧ IsSylow2In R₂' K' ∧ Commutes R₂ R₂' ∧
      Y ≤ R₂ ⊔ R₂' := by
  have hst := C.hs.stand
  have hp : p ≠ 2 := hst.odd
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK'Ω : K' ∈ Ω := C.hs.hK'.1
  obtain ⟨R₀, R₀', hR₀, hR₀', hc₀⟩ :=
    T7A.exists_commuting_sylow_twin hΩ hK hK'Ω C.hs.hne C.hzK C.hzK'
  have hQ₀ := T7A.isSylow2In_sup_of_twin hp hΩ hK hK'Ω C.hs.hne C.hzK C.hzK' hR₀ hR₀' hc₀
  obtain ⟨P, hP, hYP⟩ := IsSylow2In.exists_ge hY hYK
  obtain ⟨g, hgQ, hg⟩ := exists_conjSub_eq_of_isSylow2In hQ₀ hP
  have hKN : K' ≤ Subgroup.normalizer (K : Set G) :=
    hΩ.le_normalizer_of_twin hK'Ω hK C.hs.hne C.hzK' C.hzK
  have hK'N : K ≤ Subgroup.normalizer (K' : Set G) :=
    hΩ.le_normalizer_of_twin hK hK'Ω C.hs.hne.symm C.hzK C.hzK'
  have hgK : conjSub g K = K :=
    mem_normalizer_iff_conjSub_eq.mp ((sup_le Subgroup.le_normalizer hKN) hgQ)
  have hgK' : conjSub g K' = K' :=
    mem_normalizer_iff_conjSub_eq.mp ((sup_le hK'N Subgroup.le_normalizer) hgQ)
  refine ⟨conjSub g R₀, conjSub g R₀', ?_, ?_, hc₀.conjSub g, ?_⟩
  · have := hR₀.conj g
    rwa [hgK] at this
  · have := hR₀'.conj g
    rwa [hgK'] at this
  · rw [← T7A.conjSub_sup_eq, hg]
    exact hYP

end S24

end CFSG.ClassicalInvolution.Asc77
