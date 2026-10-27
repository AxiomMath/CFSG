module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6Frat24
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6E27
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsMaxModel
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6Endgame
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_4Aux

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin A6Facts

@[expose] def Lemma2526Claim : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (hs : UnconstrainedSetting G T M)
    (N : Notation25 hs) (t zK : G), Lv2525 N t zK → 1 < CFSG.Open.pRank 2 N.SC →
      ∀ i ∈ N.SC, i ≠ 1 → i ^ 2 = 1 → IsComponentIn N.K (Subgroup.centralizer ({i} : Set G))

section Generic

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def conjugateEquiv (K : Subgroup G) (g : G) :
    ↥(CFSG.conjugate K g) ≃* ↥K :=
  (K.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective).symm

omit [Finite G] in
theorem center_conjugate_trivial {K : Subgroup G} (g : G)
    (hZ : ∀ x ∈ K, (∀ y ∈ K, x * y = y * x) → x = 1) :
    ∀ x ∈ CFSG.conjugate K g, (∀ y ∈ CFSG.conjugate K g, x * y = y * x) → x = 1 := by
  intro x hx hc
  have hk : g * x * g⁻¹ ∈ K := BenderBranch.mem_conjugate_iff.mp hx
  have hkc : ∀ w ∈ K, (g * x * g⁻¹) * w = w * (g * x * g⁻¹) := by
    intro w hw
    have hw' : g⁻¹ * w * g ∈ CFSG.conjugate K g := by
      rw [BenderBranch.mem_conjugate_iff]
      simpa [mul_assoc] using hw
    have := hc _ hw'
    calc (g * x * g⁻¹) * w = g * (x * (g⁻¹ * w * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * w * g) * x) * g⁻¹ := by rw [this]
      _ = w * (g * x * g⁻¹) := by group
  have h1 : g * x * g⁻¹ = 1 := hZ _ hk hkc
  calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
    _ = 1 := by rw [h1]; group

theorem exists_order_three {A : Subgroup G} (e : ↥A ≃* Equiv.Perm (Fin 4)) :
    ∃ c ∈ A, c ^ 3 = 1 ∧ c ≠ 1 := by
  have h3 : 3 ∣ Nat.card A := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
    decide
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
  refine ⟨(x : G), x.2, ?_, ?_⟩
  · have := pow_orderOf_eq_one x
    rw [hx] at this
    exact congrArg Subtype.val this
  · intro h1
    have : x = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hx
    omega

theorem false_of_commuting_A6 (he : CFSG.Assembly.evenRank G ≤ 2) {F K K' : Subgroup G}
    (hF2 : IsPGroup 2 F) (hF1 : F ≠ ⊥) (hFK : F ≤ K)
    (eK' : ↥K' ≃* alternatingGroup (Fin 6))
    (hZ' : ∀ x ∈ K', (∀ y ∈ K', x * y = y * x) → x = 1)
    (hcomm : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a) {c : G} (hcK : c ∈ K) (hc3 : c ^ 3 = 1)
    (hc1 : c ≠ 1) (hcF : c ∈ Subgroup.normalizer (F : Set G)) : False := by
  obtain ⟨E, hEle, hE, hEcard⟩ := exists_elemAbelian_27 eK' hZ' hc3 hc1
    (fun k hk => hcomm c hcK k hk)
  have hK'N : K' ≤ Subgroup.normalizer (F : Set G) := by
    intro k hk
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact hcomm f (hFK hf) k hk
  have hle : K' ⊔ Subgroup.zpowers c ≤ Subgroup.normalizer (F : Set G) :=
    sup_le hK'N (Subgroup.zpowers_le.mpr hcF)
  have hcore : pCoreOf 2 (Subgroup.normalizer (F : Set G)) ≠ ⊥ := by
    intro hbot
    apply hF1
    have := le_pCoreOf_of_normalizes (p := 2) (N := F) (K := Subgroup.normalizer (F : Set G))
      Subgroup.le_normalizer le_rfl hF2
    rw [hbot] at this
    exact le_bot_iff.mp this
  exact Unc25G2.false_of_isElemAbelian_card_cube he hcore (hEle.trans hle) Nat.prime_three
    (by norm_num) hE hEcard

theorem le_normalizer_of_component (he : CFSG.Assembly.evenRank G ≤ 2) {K X F : Subgroup G}
    (hKc : IsComponentIn K X) (eK : ↥K ≃* alternatingGroup (Fin 6))
    (hZ : ∀ x ∈ K, (∀ y ∈ K, x * y = y * x) → x = 1) (hF2 : IsPGroup 2 F) (hF1 : F ≠ ⊥)
    (hFK : F ≤ K) {c : G} (hcK : c ∈ K) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    (hcF : c ∈ Subgroup.normalizer (F : Set G)) : X ≤ Subgroup.normalizer (K : Set G) := by
  intro g hg
  rw [← BenderBranch.conjugate_eq_iff_mem_normalizer]
  by_contra hne
  have hKg : IsComponentIn (CFSG.conjugate K g) X := Unc25G2.isComponentIn_conjugate hKc hg
  have hcomm : ⁅K, CFSG.conjugate K g⁆ = ⊥ :=
    (BenderBranch.eq_or_commute_of_isComponentIn hKc hKg).resolve_left fun h' => hne h'.symm
  exact false_of_commuting_A6 he hF2 hF1 hFK ((conjugateEquiv K g).trans eK)
    (center_conjugate_trivial g hZ)
    (fun a ha b hb => BenderBranch.commute_of_commutator_eq_bot hcomm ha hb) hcK hc3 hc1 hcF

omit [Finite G] in
theorem centralizer_conj_le_normalizer {j x : G} {K : Subgroup G}
    (h : Subgroup.centralizer ({j} : Set G) ≤ Subgroup.normalizer (K : Set G)) :
    Subgroup.centralizer ({x⁻¹ * j * x} : Set G) ≤
      Subgroup.normalizer (CFSG.conjugate K x : Set G) := by
  intro g hg
  have hgc : g * (x⁻¹ * j * x) = (x⁻¹ * j * x) * g := Subgroup.mem_centralizer_singleton_iff.mp hg
  have h1 : x * g * x⁻¹ ∈ Subgroup.centralizer ({j} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * g * x⁻¹ * j = x * (g * (x⁻¹ * j * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * j * x) * g) * x⁻¹ := by rw [hgc]
      _ = j * (x * g * x⁻¹) := by group
  have h2 := h h1
  rw [Subgroup.mem_normalizer_iff] at h2 ⊢
  intro y
  rw [BenderBranch.mem_conjugate_iff, BenderBranch.mem_conjugate_iff]
  have e : x * (g * y * g⁻¹) * x⁻¹ = (x * g * x⁻¹) * (x * y * x⁻¹) * (x * g * x⁻¹)⁻¹ := by group
  rw [e]
  exact h2 (x * y * x⁻¹)

theorem exists_mem_ne_two_of_four_le {E : Subgroup G} (hE : 4 ≤ Nat.card E) (a b : G) :
    ∃ x ∈ E, x ≠ a ∧ x ≠ b := by
  by_contra hcon
  push Not at hcon
  have hsub : (E : Set G) ⊆ {a, b} := by
    intro x hx
    by_cases hxa : x = a
    · exact Or.inl hxa
    · exact Or.inr (hcon x hx hxa)
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({a, b} : Set G).ncard ≤ 2 := by
    calc ({a, b} : Set G).ncard ≤ ({b} : Set G).ncard + 1 := Set.ncard_insert_le a {b}
      _ = 2 := by rw [Set.ncard_singleton]
  have h3 : (E : Set G).ncard = Nat.card E := by
    rw [← Nat.card_coe_set_eq]
    rfl
  omega

theorem rankSet_bddAbove (H : Subgroup G) :
    BddAbove {k : ℕ | ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ k} :=
  ⟨Nat.card G, by
    rintro k ⟨E, -, -, hk⟩
    calc k ≤ 2 ^ k := (Nat.lt_pow_self (by norm_num)).le
      _ = Nat.card E := hk.symm
      _ ≤ Nat.card G := Subgroup.card_le_card_group E⟩

theorem one_le_pRank_of_involution {H : Subgroup G} {t : G} (htH : t ∈ H) (ht1 : t ≠ 1)
    (ht2 : t ^ 2 = 1) : 1 ≤ CFSG.Open.pRank 2 H := by
  unfold CFSG.Open.pRank
  apply le_csSup (rankSet_bddAbove H)
  refine ⟨Subgroup.zpowers t, Subgroup.zpowers_le.mpr htH, ⟨inferInstance, ?_⟩, ?_⟩
  · intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    simp [ht2]
  · rw [Nat.card_zpowers, orderOf_eq_prime ht2 ht1, pow_one]

theorem exists_involution_ne {H : Subgroup G} (t : G) (h : 1 < CFSG.Open.pRank 2 H) :
    ∃ i ∈ H, i ≠ 1 ∧ i ≠ t ∧ i ^ 2 = 1 := by
  have hne : {k : ℕ | ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ k}.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have : CFSG.Open.pRank 2 H = 0 := by
      unfold CFSG.Open.pRank
      rw [hne]
      simp
    omega
  have hmem := Nat.sSup_mem hne (rankSet_bddAbove H)
  obtain ⟨E, hEH, hEel, hEcard⟩ := hmem
  have h4 : 4 ≤ Nat.card E := by
    rw [hEcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ CFSG.Open.pRank 2 H := Nat.pow_le_pow_right (by norm_num) h
  obtain ⟨i, hiE, hi1, hit⟩ := exists_mem_ne_two_of_four_le h4 1 t
  exact ⟨i, hEH hiE, hi1, hit, hEel.2 i hiE⟩

end Generic

theorem lemma2526 (hclaim : Lemma2526Claim) : Lemma2526 := by
  intro G _ _ T M hs N t zK h
  have he : CFSG.Assembly.evenRank G ≤ 2 := hs.setting.qtke.2.2
  have hK0 : N.K0 = N.K := h.concl2520
  have hKH : N.H ≤ Subgroup.normalizer (N.K : Set G) := by
    rw [← hK0]; exact N.H_le_normalizer_K0
  have hf := h.facts2511
  have h254 := h.facts254
  have h258 := h.facts258
  have hsimple := h258.simple
  have hZK : ∀ x ∈ N.K, (∀ y ∈ N.K, x * y = y * x) → x = 1 := fun x hx hc =>
    N.center_K_trivial hsimple hx hc
  obtain ⟨eK⟩ := h.concl2521.nonempty_K
  obtain ⟨D⟩ := exists_a6Datum N hKH h258 h.concl2521
  have hxt : N.x⁻¹ * t * N.x = zK := h.concl2525.1
  have htSC : t ∈ N.SC := hf.t_mem
  show CFSG.Open.pRank 2 N.SC = 1
  by_contra hne
  have hpR : 1 < CFSG.Open.pRank 2 N.SC :=
    lt_of_le_of_ne (one_le_pRank_of_involution htSC hf.t_ne_one hf.t_sq) fun h1 => hne h1.symm
  obtain ⟨i, hiSC, hi1, hit, hi2⟩ := exists_involution_ne t hpR
  have hiS : i ∈ N.S := N.SC_le_S hiSC
  have hcl : IsComponentIn N.K (Subgroup.centralizer ({i} : Set G)) :=
    hclaim G T M hs N t zK h hpR i hiSC hi1 hi2
  obtain ⟨E₁, E₂, hE₁K, hE₂K, hE₁4, hE₂4, -, -, -, -⟩ := h.concl2523
  have hFK : E₁ ≤ N.K := fun x hx => (hE₁K hx).2
  have hF2 : IsPGroup 2 ↥E₁ := fun g => ⟨1, Subtype.ext (by simpa using hE₁4.1.2 (g : G) g.2)⟩
  have hF1 : E₁ ≠ ⊥ := by
    intro hbot
    have := hE₁4.2
    rw [hbot] at this
    simp at this
  obtain ⟨e4⟩ := h258.four_normalizer E₁ hFK hE₁4
  obtain ⟨c, hcmem, hc3, hc1⟩ := exists_order_three e4
  have hCi : Subgroup.centralizer ({i} : Set G) ≤ Subgroup.normalizer (N.K : Set G) :=
    le_normalizer_of_component he hcl eK hZK hF2 hF1 hFK hcmem.1 hc3 hc1 hcmem.2
  have hCt : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (N.K : Set G) := by
    rw [← h.concl2522.2.1]; exact hKH
  have hCix := centralizer_conj_le_normalizer (x := N.x) hCi
  have hCtx := centralizer_conj_le_normalizer (x := N.x) hCt
  rw [hxt] at hCtx
  have hzKS : zK ∈ N.S := N.SK_le_S (hf.zK_mem_SK hK0)
  have hSN : ∀ s ∈ N.S, s ∈ Subgroup.normalizer (CFSG.conjugate N.K N.x : Set G) := by
    intro s hs'
    apply hCtx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hf.zK_mem_center.2 s hs'
  have hzT : N.z ∈ centerOf T := N.tuple.z_mem
  have hzS : N.z ∈ centerOf N.S :=
    ⟨N.tuple.center_le hzT,
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr N.S_le_T) hzT.2⟩
  have hΦz : D.Φ N.z = zb := D.Φ_z hK0 h254 hzS
  have hΦzK : D.Φ zK = zb := (D.Φ_zK hK0 hf).trans hΦz
  set ι : G := N.x⁻¹ * i * N.x with hι
  have hιS : ι ∈ N.S := N.x_conj_S' hiS
  have hιH : ι ∈ N.H := N.S_le_H hιS
  have hι2 : ι * ι = 1 := by
    have h1 : ι * ι = N.x⁻¹ * (i * i) * N.x := by rw [hι]; group
    have h2 : i * i = 1 := by rw [← sq]; exact hi2
    rw [h1, h2]; group
  have hιSCx : ι ∈ CFSG.conjugate N.SC N.x := by
    rw [BenderBranch.mem_conjugate_iff]
    have : N.x * ι * N.x⁻¹ = i := by rw [hι]; group
    rw [this]; exact hiSC
  have hι1 : ι ≠ 1 := by
    intro h1
    apply hi1
    have : i = N.x * ι * N.x⁻¹ := by rw [hι]; group
    rw [this, h1]; group
  have hιnSC : ι ∉ N.SC := by
    intro hι'
    apply hι1
    have h3 : ι ∈ N.SC ⊓ CFSG.conjugate N.SC N.x := ⟨hι', hιSCx⟩
    rw [h.concl255.1, Subgroup.mem_bot] at h3
    exact h3
  have hΦι1 : D.Φ ι ≠ 1 := fun h1 => hιnSC (D.mem_SC_of_Φ_eq_one hK0 hιS h1)
  have hΦιzb : D.Φ ι ≠ zb := by
    intro hz
    have h1 : zK⁻¹ * ι ∈ N.SC := D.inv_mul_mem_SC hK0 hzKS hιS (by rw [hΦzK, hz])
    have hzKx : zK ∈ CFSG.conjugate N.SC N.x := by
      rw [BenderBranch.mem_conjugate_iff]
      have : N.x * zK * N.x⁻¹ = t := by rw [← hxt]; group
      rw [this]; exact htSC
    have h2 : zK⁻¹ * ι ∈ CFSG.conjugate N.SC N.x :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hzKx) hιSCx
    have h3 : zK⁻¹ * ι ∈ N.SC ⊓ CFSG.conjugate N.SC N.x := ⟨h1, h2⟩
    rw [h.concl255.1, Subgroup.mem_bot] at h3
    have h4 : zK = ι := inv_mul_eq_one.mp h3
    apply hit
    calc i = N.x * ι * N.x⁻¹ := by rw [hι]; group
      _ = N.x * zK * N.x⁻¹ := by rw [← h4]
      _ = t := by rw [← hxt]; group
  have hΦι2 : D.Φ ι * D.Φ ι = 1 := by rw [← D.mul ι hιH ι hιH, hι2, D.Φ_one]
  obtain ⟨k', hk'psl, hk'comm, hk'P⟩ := invol_cent_not_P0 (D.S_mem ι hιS) hΦι1 hΦιzb hΦι2
  obtain ⟨k, hkK, hkΦ⟩ := D.K_surj k' hk'psl
  have hkH : k ∈ N.H := N.K_le_H hkK
  have hkι : k * ι = ι * k := by
    have hιk : ι * k * ι⁻¹ ∈ N.K := (Subgroup.mem_normalizer_iff.mp (hKH hιH) k).mp hkK
    have h1 : ι * k * ι⁻¹ = k := by
      apply D.inj_K hsimple hιk hkK
      rw [D.Φ_conj hιH hkH, hkΦ, ← hk'comm]
      group
    calc k * ι = (ι * k * ι⁻¹) * ι := by rw [h1]
      _ = ι * k := by group
  have hkN : k ∈ Subgroup.normalizer (CFSG.conjugate N.K N.x : Set G) :=
    hCix (Subgroup.mem_centralizer_singleton_iff.mpr hkι)
  let X : Subgroup P10 :=
    { carrier := {p | ∃ w ∈ Subgroup.normalizer (CFSG.conjugate N.K N.x : Set G) ⊓ N.H, D.Φ w = p}
      mul_mem' := by
        rintro _ _ ⟨w₁, hw₁, rfl⟩ ⟨w₂, hw₂, rfl⟩
        exact ⟨w₁ * w₂, Subgroup.mul_mem _ hw₁ hw₂, D.mul w₁ hw₁.2 w₂ hw₂.2⟩
      one_mem' := ⟨1, Subgroup.one_mem _, D.Φ_one⟩
      inv_mem' := by
        rintro _ ⟨w, hw, rfl⟩
        exact ⟨w⁻¹, Subgroup.inv_mem _ hw, D.Φ_inv hw.2⟩ }
  have hP : ∀ p ∈ P0, p ∈ X := by
    intro p hp
    obtain ⟨s, hs', hsp⟩ := D.S_surj p hp
    exact ⟨s, ⟨hSN s hs', N.S_le_H hs'⟩, hsp⟩
  have hk'X : k' ∈ X := ⟨k, ⟨hkN, hkH⟩, hkΦ⟩
  have hpsl : A6Models.psl29 ≤ X := P0_overgroup hP hk'psl hk'P hk'X
  have hKW : ∀ a ∈ N.K, a ∈ Subgroup.normalizer (CFSG.conjugate N.K N.x : Set G) := by
    intro a ha
    obtain ⟨w, ⟨hwN, hwH⟩, hwa⟩ := hpsl (D.K_mem a ha)
    have haH := N.K_le_H ha
    have h1 : D.Φ (w⁻¹ * a) = 1 := by
      rw [D.mul _ (N.H.inv_mem hwH) _ haH, D.Φ_inv hwH, hwa, inv_mul_cancel]
    have h2 := (D.ker _ (N.H.mul_mem (N.H.inv_mem hwH) haH)).mp h1
    have h3 : w⁻¹ * a ∈ N.S :=
      N.mem_S_of_centralizes hKH h254 hZK (N.H.mul_mem (N.H.inv_mem hwH) haH) h2
    have h4 : a = w * (w⁻¹ * a) := by group
    rw [h4]
    exact Subgroup.mul_mem _ hwN (hSN _ h3)
  have hx2K : N.x ^ 2 ∈ Subgroup.normalizer (N.K : Set G) := hKH (N.S_le_H N.x_sq)
  have hKx2 : CFSG.conjugate N.K (N.x * N.x) = N.K := by
    rw [← sq]; exact BenderBranch.conjugate_eq_iff_mem_normalizer.mpr hx2K
  have hKxinv : CFSG.conjugate N.K N.x⁻¹ = CFSG.conjugate N.K N.x := by
    have h1 : CFSG.conjugate (CFSG.conjugate N.K N.x) N.x = N.K := by
      rw [BenderBranch.conjugate_conjugate]; exact hKx2
    calc CFSG.conjugate N.K N.x⁻¹
        = CFSG.conjugate (CFSG.conjugate (CFSG.conjugate N.K N.x) N.x) N.x⁻¹ := by rw [h1]
      _ = CFSG.conjugate (CFSG.conjugate N.K N.x) (N.x * N.x⁻¹) := by
          rw [BenderBranch.conjugate_conjugate]
      _ = CFSG.conjugate N.K N.x := by rw [mul_inv_cancel, BenderBranch.conjugate_one]
  have hKxN : ∀ g ∈ CFSG.conjugate N.K N.x, g ∈ Subgroup.normalizer (N.K : Set G) := by
    intro g hg
    have ha : N.x * g * N.x⁻¹ ∈ N.K := BenderBranch.mem_conjugate_iff.mp hg
    have hgeq : g = N.x⁻¹ * (N.x * g * N.x⁻¹) * N.x := by group
    have hKa : CFSG.conjugate (CFSG.conjugate N.K N.x) (N.x * g * N.x⁻¹) =
        CFSG.conjugate N.K N.x :=
      BenderBranch.conjugate_eq_iff_mem_normalizer.mpr (hKW _ ha)
    rw [← BenderBranch.conjugate_eq_iff_mem_normalizer]
    calc CFSG.conjugate N.K g
        = CFSG.conjugate N.K (N.x⁻¹ * (N.x * g * N.x⁻¹) * N.x) := by rw [← hgeq]
      _ = CFSG.conjugate (CFSG.conjugate (CFSG.conjugate N.K N.x⁻¹) (N.x * g * N.x⁻¹)) N.x := by
          rw [BenderBranch.conjugate_conjugate, BenderBranch.conjugate_conjugate]
          congr 1
          group
      _ = CFSG.conjugate (CFSG.conjugate (CFSG.conjugate N.K N.x) (N.x * g * N.x⁻¹)) N.x := by
          rw [hKxinv]
      _ = CFSG.conjugate (CFSG.conjugate N.K N.x) N.x := by rw [hKa]
      _ = N.K := by rw [BenderBranch.conjugate_conjugate]; exact hKx2
  have hKxNorm : ∀ a ∈ N.K, ∀ b ∈ CFSG.conjugate N.K N.x,
      a * b * a⁻¹ ∈ CFSG.conjugate N.K N.x := fun a ha b hb =>
    (Subgroup.mem_normalizer_iff.mp (hKW a ha) b).mp hb
  have hKNorm : ∀ b ∈ CFSG.conjugate N.K N.x, ∀ a ∈ N.K, b * a * b⁻¹ ∈ N.K := fun b hb a ha =>
    (Subgroup.mem_normalizer_iff.mp (hKxN b hb) a).mp ha
  have hKne : ¬ N.K ≤ CFSG.conjugate N.K N.x := by
    intro hle
    have heq : N.K = CFSG.conjugate N.K N.x :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjugate])
    have hzKK : zK ∈ N.K := (hf.zK_mem_SK hK0).2
    have hzKc : ∀ y ∈ N.K, zK * y = y * zK := by
      intro y hy
      have hy' : y ∈ CFSG.conjugate N.K N.x := heq ▸ hy
      have hk := BenderBranch.mem_conjugate_iff.mp hy'
      have htk : (N.x * y * N.x⁻¹) * t = t * (N.x * y * N.x⁻¹) := by
        have := Subgroup.mem_centralizer_iff.mp (N.SC_le_centralizer htSC) _ (hK0 ▸ hk)
        exact this
      calc zK * y = N.x⁻¹ * (t * (N.x * y * N.x⁻¹)) * N.x := by rw [← hxt]; group
        _ = N.x⁻¹ * ((N.x * y * N.x⁻¹) * t) * N.x := by rw [htk]
        _ = y * zK := by rw [← hxt]; group
    have h1 : zK = 1 := hZK zK hzKK fun y hy => (hzKc y hy)
    apply hf.t_ne_one
    calc t = N.x * zK * N.x⁻¹ := by rw [← hxt]; group
      _ = 1 := by rw [h1]; group
  have hJ : N.K ⊓ CFSG.conjugate N.K N.x = ⊥ := by
    have hnorm : ((N.K ⊓ CFSG.conjugate N.K N.x).subgroupOf N.K).Normal := by
      refine ⟨fun a ha g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at ha ⊢
      refine ⟨N.K.mul_mem (N.K.mul_mem g.2 ha.1) (N.K.inv_mem g.2), ?_⟩
      exact hKxNorm _ g.2 _ ha.2
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((N.K ⊓ CFSG.conjugate N.K N.x).subgroupOf N.K) with hbot | htop
    · rw [Subgroup.eq_bot_iff_forall]
      intro y hy
      have : (⟨y, hy.1⟩ : ↥N.K) ∈ (N.K ⊓ CFSG.conjugate N.K N.x).subgroupOf N.K :=
        Subgroup.mem_subgroupOf.mpr hy
      rw [hbot, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    · exfalso
      apply hKne
      intro y hy
      have : (⟨y, hy⟩ : ↥N.K) ∈ (N.K ⊓ CFSG.conjugate N.K N.x).subgroupOf N.K := by
        rw [htop]; exact Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.mp this).2
  have hcomm : ∀ a ∈ N.K, ∀ b ∈ CFSG.conjugate N.K N.x, a * b = b * a := by
    intro a ha b hb
    have h1 : a * b * a⁻¹ * b⁻¹ ∈ CFSG.conjugate N.K N.x :=
      Subgroup.mul_mem _ (hKxNorm a ha b hb) (Subgroup.inv_mem _ hb)
    have h2 : a * b * a⁻¹ * b⁻¹ ∈ N.K := by
      have := N.K.mul_mem ha (hKNorm b hb a⁻¹ (N.K.inv_mem ha))
      simpa [mul_assoc] using this
    have h3 : a * b * a⁻¹ * b⁻¹ ∈ N.K ⊓ CFSG.conjugate N.K N.x := ⟨h2, h1⟩
    rw [hJ, Subgroup.mem_bot] at h3
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [h3, one_mul]
  exact false_of_commuting_A6 he hF2 hF1 hFK ((conjugateEquiv N.K N.x).trans eK)
    (center_conjugate_trivial N.x hZK) hcomm hcmem.1 hc3 hc1 hcmem.2

end CFSG.QuasithinUnique
