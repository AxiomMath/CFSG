module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Coprime
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aSecStd
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuot
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalKProper

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

open CFSG Subgroup CFSG.ComponentClassification.GSThmB CFSG.ComponentClassification.UnbalancedLayer

variable {H : Type} [Group H] [Finite H] (h : Hyp52 H)

theorem K_le_W : h.K ≤ h.W := h.isPComponent_K.1

theorem W_le_normalizer_K (hKa : conjugate h.K h.a = h.K) : h.W ≤ normalizer (h.K : Set H) := by
  have h1 := OddQuot.le_normalizer_layerIn h.W
  rw [← h.V_eq_K hKa]
  exact h1

@[expose] noncomputable def actW (hKa : conjugate h.K h.a = h.K) :
    h.W →* MulAut (OddBar h.K) :=
  (oddBarConj h.K).comp (inclusion (W_le_normalizer_K h hKa))

theorem actW_apply_mk (hKa : conjugate h.K h.a = h.K) (w : h.W) (k : h.K) :
    actW h hKa w (k : OddBar h.K) =
      ((⟨(w : H) * k * (w : H)⁻¹, (mem_normalizer_iff.mp (W_le_normalizer_K h hKa w.2) k).mp
        k.2⟩ : h.K) : OddBar h.K) := rfl

theorem actW_of_mem_K (hKa : conjugate h.K h.a = h.K) (k : h.K) :
    actW h hKa ⟨k, K_le_W h k.2⟩ = MulAut.conj (k : OddBar h.K) := by
  ext x
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
  rfl

variable {h}

theorem mem_pPrimeCore_of_mem_pPrimeCore_W {k : h.K}
    (hk : (⟨k, K_le_W h k.2⟩ : h.W) ∈ pPrimeCore 2 h.W) : k ∈ pPrimeCore 2 h.K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M : Subgroup h.K := (pPrimeCore 2 h.W).comap (inclusion (K_le_W h)) with hM
  have hMn : M.Normal := (pPrimeCore_normal (p := 2) (G := h.W)).comap _
  have hMc : Nat.Coprime 2 (Nat.card M) := by
    have hle : M.map (inclusion (K_le_W h)) ≤ pPrimeCore 2 h.W := map_comap_le _ _
    have h1 := card_dvd_of_le hle
    rw [card_map_of_injective (inclusion_injective _)] at h1
    exact (pPrimeCore_coprime_card (p := 2) (G := h.W)).coprime_dvd_right h1
  exact (le_sSup ⟨hMn, hMc⟩ : M ≤ pPrimeCore 2 h.K) hk

theorem mem_pPrimeCore_of_mem_oddTwoCore (hsimp : IsSimpleGroup (OddBar h.K)) {s : ℕ}
    (hs : s.Prime) (hs2 : s ≠ 2) (hsK : s ∣ Nat.card (OddBar h.K)) {k : h.K}
    (hk : (⟨k, K_le_W h k.2⟩ : h.W) ∈ oddTwoCore h.W) : k ∈ pPrimeCore 2 h.K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup h.K := (oddTwoCore h.W).comap (inclusion (K_le_W h)) with hN
  have hNn : N.Normal := (oddTwoCore_normal h.W).comap _
  have hNb : (N.map (QuotientGroup.mk' (pPrimeCore 2 h.K))).Normal :=
    hNn.map _ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' (pPrimeCore 2 h.K)))
    with hb | ht
  · have : QuotientGroup.mk' (pPrimeCore 2 h.K) k ∈
        N.map (QuotientGroup.mk' (pPrimeCore 2 h.K)) := ⟨k, hk, rfl⟩
    rw [hb, mem_bot] at this
    exact (QuotientGroup.eq_one_iff k).1 this
  exfalso
  have h2 : ∀ y : OddBar h.K, ∃ e : ℕ, y ^ 2 ^ e = 1 := by
    intro y
    have hy : y ∈ N.map (QuotientGroup.mk' (pPrimeCore 2 h.K)) := by
      rw [ht]
      exact mem_top y
    obtain ⟨n, hn, rfl⟩ := hy
    obtain ⟨e, he⟩ := B5a.exists_pow_mem_of_mem_oddTwoCore hn
    refine ⟨e, ?_⟩
    rw [← map_pow]
    apply (QuotientGroup.eq_one_iff _).2
    have : inclusion (K_le_W h) (n ^ 2 ^ e) ∈ pPrimeCore 2 h.W := by
      rw [map_pow]
      exact he
    exact mem_pPrimeCore_of_mem_pPrimeCore_W this
  have := Fact.mk hs
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' s hsK
  obtain ⟨e, he⟩ := h2 y
  have h3 := orderOf_dvd_of_pow_eq_one he
  rw [hy] at h3
  exact hs2 ((Nat.prime_dvd_prime_iff_eq hs Nat.prime_two).1 (hs.dvd_of_dvd_pow h3))

theorem mem_oddTwoCore_of_mem_pPrimeCore (hKN : h.W ≤ normalizer (h.K : Set H)) {k : h.K}
    (hk : k ∈ pPrimeCore 2 h.K) : (⟨k, K_le_W h k.2⟩ : h.W) ∈ oddTwoCore h.W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply Hyp52.pPrimeCore_le_oddTwoCore
  set M : Subgroup h.W := (pPrimeCore 2 h.K).map (inclusion (K_le_W h)) with hM
  have hMn : M.Normal := ⟨fun m hm w => by
    obtain ⟨o, ho, rfl⟩ := hm
    have hw := UnbalancedGS.normalizer_le_normalizer_map_of_characteristic h.K
      (pPrimeCore 2 h.K) (hKN w.2)
    obtain ⟨o', ho', hoe⟩ := mem_map.1 ((mem_normalizer_iff.1 hw (o : H)).1 ⟨o, ho, rfl⟩)
    refine ⟨o', ho', Subtype.ext ?_⟩
    rw [subtype_apply] at hoe
    simp only [coe_inclusion, coe_mul, coe_inv, hoe]⟩
  have hMc : Nat.Coprime 2 (Nat.card M) := by
    rw [hM, card_map_of_injective (inclusion_injective _)]
    exact pPrimeCore_coprime_card
  exact (le_sSup ⟨hMn, hMc⟩ : M ≤ pPrimeCore 2 h.W) ⟨k, hk, rfl⟩

theorem mem_normalizer_of_conj_mem {G : Type*} [Group G] [Finite G] {J' : Subgroup G} {z : G}
    (hz : ∀ y ∈ J', z * y * z⁻¹ ∈ J') : z ∈ normalizer (J' : Set G) := by
  have hle : J'.map (MulAut.conj z).toMonoidHom ≤ J' := by
    rintro _ ⟨y, hy, rfl⟩
    exact hz y hy
  have heq : J'.map (MulAut.conj z).toMonoidHom = J' :=
    eq_of_le_of_card_ge hle (by
      rw [card_map_of_injective (MulAut.conj z).injective])
  rw [mem_normalizer_iff]
  intro y
  constructor
  · exact hz y
  · intro hy
    rw [← heq] at hy
    obtain ⟨y', hy', hyy⟩ := hy
    have : y' = y := by
      have := congrArg (fun t => z⁻¹ * t * z) hyy
      simpa [MulAut.conj_apply, mul_assoc] using this
    rwa [← this]

section Bar

variable (hKa : conjugate h.K h.a = h.K) (hsimp : IsSimpleGroup (OddBar h.K)) {s : ℕ}
  (hs : s.Prime) (hs2 : s ≠ 2) (hsK : s ∣ Nat.card (OddBar h.K))

include hsimp hs hs2 hsK in
theorem oddTwoCore_le_ker_actW : oddTwoCore h.W ≤ (actW h hKa).ker := by
  intro o ho
  rw [MonoidHom.mem_ker]
  ext x
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
  rw [actW_apply_mk, MulAut.one_apply, QuotientGroup.eq]
  set k₁ : h.K := ⟨(o : H) * k * (o : H)⁻¹, (mem_normalizer_iff.mp
    (W_le_normalizer_K h hKa o.2) k).mp k.2⟩ with hk₁
  apply mem_pPrimeCore_of_mem_oddTwoCore hsimp hs hs2 hsK
  have hkW : (k : H) ∈ h.W := K_le_W h k.2
  have h1 : (⟨(k₁⁻¹ * k : h.K), K_le_W h (k₁⁻¹ * k).2⟩ : h.W) =
      o * ((⟨k, hkW⟩ : h.W)⁻¹ * o * (⟨k, hkW⟩ : h.W)⁻¹⁻¹)⁻¹ := by
    apply Subtype.ext
    simp only [hk₁, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv]
    group
  rw [h1]
  exact mul_mem ho (inv_mem ((oddTwoCore_normal h.W).conj_mem o ho _))

@[expose] noncomputable def actBar : Wbar h.B →* MulAut (OddBar h.K) :=
  QuotientGroup.lift (oddTwoCore h.W) (actW h hKa) (oddTwoCore_le_ker_actW hKa hsimp hs hs2 hsK)

theorem actBar_mk (w : h.W) :
    actBar hKa hsimp hs hs2 hsK (wbarMk h.B w) = actW h hKa w := QuotientGroup.lift_mk _ _ _

include hKa in
theorem pPrimeCore_le_ker_kbar :
    pPrimeCore 2 h.K ≤ ((wbarMk h.B).comp (inclusion (K_le_W h))).ker := by
  intro k hk
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, wbarMk, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]
  exact mem_oddTwoCore_of_mem_pPrimeCore (W_le_normalizer_K h hKa) hk

@[expose] noncomputable def kbar : OddBar h.K →* Wbar h.B :=
  QuotientGroup.lift (pPrimeCore 2 h.K) ((wbarMk h.B).comp (inclusion (K_le_W h)))
    (pPrimeCore_le_ker_kbar hKa)

theorem kbar_mk (k : h.K) :
    kbar hKa (k : OddBar h.K) = wbarMk h.B ⟨k, K_le_W h k.2⟩ := QuotientGroup.lift_mk _ _ _

include hsimp hs hs2 hsK in
theorem kbar_injective : Function.Injective (kbar hKa) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
  rw [kbar_mk, wbarMk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
  exact (QuotientGroup.eq_one_iff k).2 (mem_pPrimeCore_of_mem_oddTwoCore hsimp hs hs2 hsK hx)

theorem kbar_actBar (u : Wbar h.B) (x : OddBar h.K) :
    kbar hKa (actBar hKa hsimp hs hs2 hsK u x) = u * kbar hKa x * u⁻¹ := by
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (oddTwoCore h.W) u
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
  change kbar hKa (actBar hKa hsimp hs hs2 hsK (wbarMk h.B w) (k : OddBar h.K)) = _
  rw [actBar_mk, actW_apply_mk, kbar_mk, kbar_mk]
  change wbarMk h.B _ = wbarMk h.B w * wbarMk h.B _ * (wbarMk h.B w)⁻¹
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

theorem actBar_kbar (x : OddBar h.K) :
    actBar hKa hsimp hs hs2 hsK (kbar hKa x) = MulAut.conj x := by
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
  rw [kbar_mk, actBar_mk, actW_of_mem_K]

theorem map_kbar_imJB :
    (imJB h).map (kbar hKa) = wbarImage h.B (GSLit.fixedLayer h.J h.B) := by
  ext y
  constructor
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    refine ⟨⟨k, K_le_W h k.2⟩, ?_, ?_⟩
    · exact hk
    · exact (kbar_mk hKa k).symm
  · rintro ⟨w, hw, rfl⟩
    have hwK : (w : H) ∈ h.K := fixedLayer_le_K h hKa hw
    refine ⟨QuotientGroup.mk ⟨w, hwK⟩, ⟨⟨w, hwK⟩, hw, rfl⟩, ?_⟩
    rw [kbar_mk]

include hsimp hs hs2 hsK in
theorem conj_mem_centralizer {w : h.W} {g' : OddBar h.K}
    (hfix : ∀ y ∈ imJB h, actW h hKa w (g' * y * g'⁻¹) = g' * y * g'⁻¹) :
    (kbar hKa g')⁻¹ * wbarMk h.B w * kbar hKa g' ∈
      centralizer (wbarImage h.B (GSLit.fixedLayer h.J h.B) : Set (Wbar h.B)) := by
  rw [mem_centralizer_iff]
  intro l hl
  rw [← map_kbar_imJB hKa] at hl
  obtain ⟨y, hy, rfl⟩ := hl
  have h1 : wbarMk h.B w * kbar hKa (g' * y * g'⁻¹) * (wbarMk h.B w)⁻¹ =
      kbar hKa (g' * y * g'⁻¹) := by
    rw [← kbar_actBar hKa hsimp hs hs2 hsK, actBar_mk, hfix y hy]
  rw [map_mul, map_mul, map_inv] at h1
  calc kbar hKa y * ((kbar hKa g')⁻¹ * wbarMk h.B w * kbar hKa g')
      = (kbar hKa g')⁻¹ * (kbar hKa g' * kbar hKa y * (kbar hKa g')⁻¹) * wbarMk h.B w *
          kbar hKa g' := by group
    _ = (kbar hKa g')⁻¹ * (wbarMk h.B w * (kbar hKa g' * kbar hKa y * (kbar hKa g')⁻¹) *
          (wbarMk h.B w)⁻¹) * wbarMk h.B w * kbar hKa g' := by rw [h1]
    _ = (kbar hKa g')⁻¹ * wbarMk h.B w * kbar hKa g' * kbar hKa y := by group

include hsimp hs hs2 hsK in
theorem false_of_fixed_conj {w : h.W} (hw2 : ∃ n : ℕ, w ^ 2 ^ n = 1)
    (hτ : actW h hKa w ≠ 1) {g x : OddBar h.K}
    (hfixJ : ∀ y ∈ imJB h, actW h hKa w (g * y * g⁻¹) = g * y * g⁻¹)
    (hfixx : actW h hKa w x = x)
    (hxN : g⁻¹ * x * g ∉ normalizer (imJB h : Set (OddBar h.K))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstd := h.isStandard_bar
  set L := wbarImage h.B (GSLit.fixedLayer h.J h.B) with hL
  set C := centralizer (L : Set (Wbar h.B)) with hC
  set wb := wbarMk h.B w with hwb
  set v := (kbar hKa g)⁻¹ * wb * kbar hKa g with hv
  set u := kbar hKa (g⁻¹ * x * g) with hu
  have hvC : v ∈ C := conj_mem_centralizer hKa hsimp hs hs2 hsK hfixJ
  have hfix' : ∀ y ∈ imJB h, actW h hKa w (x * g * y * (x * g)⁻¹) = x * g * y * (x * g)⁻¹ := by
    intro y hy
    have : x * g * y * (x * g)⁻¹ = x * (g * y * g⁻¹) * x⁻¹ := by group
    rw [this, map_mul, map_mul, map_inv, hfixJ y hy, hfixx]
  have huvC : u⁻¹ * v * u ∈ C := by
    have := conj_mem_centralizer hKa hsimp hs hs2 hsK hfix'
    convert this using 1
    rw [hu, hv, hwb]
    simp only [map_mul, map_inv]
    group
  have hmem : v ∈ C ⊓ conjugate C u⁻¹ := by
    refine ⟨hvC, ?_⟩
    show v ∈ C.map (MulAut.conj u⁻¹⁻¹).toMonoidHom
    refine ⟨u⁻¹ * v * u, huvC, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hv1 : v ≠ 1 := by
    intro h1
    apply hτ
    have h2 : actBar hKa hsimp hs hs2 hsK v = 1 := by rw [h1, map_one]
    rw [hv, map_mul, map_mul, map_inv, actBar_kbar, hwb, actBar_mk] at h2
    calc actW h hKa w = MulAut.conj g * ((MulAut.conj g)⁻¹ * actW h hKa w * MulAut.conj g) *
          (MulAut.conj g)⁻¹ := by group
      _ = 1 := by rw [h2, mul_one, mul_inv_cancel]
  obtain ⟨n, hn⟩ := hw2
  have hvn : v ^ 2 ^ n = 1 := by
    have hvc : v = MulAut.conj (kbar hKa g)⁻¹ wb := by rw [MulAut.conj_apply, inv_inv]
    rw [hvc, ← map_pow, hwb, ← map_pow, hn, map_one, map_one]
  have h2v : 2 ∣ orderOf v := by
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hvn)
    rcases k with _ | k
    · exact absurd (orderOf_eq_one_iff.1 (by rw [hk', pow_zero])) hv1
    · rw [hk', pow_succ]
      exact dvd_mul_left 2 _
  have huN : u ∈ normalizer (L : Set (Wbar h.B)) := by
    rw [← hstd.2.2.2.1]
    by_contra hun
    have hodd := hstd.2.2.1 u⁻¹ (fun h' => hun (by simpa using inv_mem h'))
    have h3 := orderOf_dvd_natCard (⟨v, hmem⟩ : ↥(C ⊓ conjugate C u⁻¹))
    rw [Subgroup.orderOf_mk] at h3
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 (h2v.trans h3))
  apply hxN
  apply mem_normalizer_of_conj_mem
  intro y hy
  have h4 : kbar hKa ((g⁻¹ * x * g) * y * (g⁻¹ * x * g)⁻¹) ∈ L := by
    rw [map_mul, map_mul, map_inv, ← hu]
    have hy' : kbar hKa y ∈ L := by
      rw [hL, ← map_kbar_imJB hKa]
      exact ⟨y, hy, rfl⟩
    exact (mem_normalizer_iff.mp huN _).mp hy'
  rw [hL, ← map_kbar_imJB hKa] at h4
  obtain ⟨y', hy', hyy⟩ := h4
  rw [← kbar_injective hKa hsimp hs hs2 hsK hyy]
  exact hy'

end Bar

end CFSG.ComponentClassification.CatFactsL4U4
