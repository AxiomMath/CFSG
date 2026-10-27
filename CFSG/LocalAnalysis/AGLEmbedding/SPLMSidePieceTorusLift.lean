module

public import CFSG.LocalAnalysis.AGLEmbedding.SPLMSidePieces
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux

public section

namespace CFSG.AGLEmbedding.SPLMSide

section Group

variable {A : Type*} [Group A] [Finite A]

theorem mem_normalizer_of_conj_into {T : Subgroup A} {g : A} (hg : ∀ t ∈ T, g * t * g⁻¹ ∈ T) :
    g ∈ Subgroup.normalizer (T : Set A) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨t, ht, rfl⟩
    exact hg t ht
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

omit [Finite A] in
theorem mem_of_mem_sup_coprime {N O : Subgroup A} [N.Normal] {q : ℕ}
    (hO : q.Coprime (Nat.card O)) {t : A} (ht : t ∈ N ⊔ O) {k : ℕ} (htk : t ^ q ^ k = 1) :
    t ∈ N := by
  obtain ⟨n, hn, o, ho, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp ht
  have h1 : orderOf (QuotientGroup.mk' N (n * o)) ∣ q ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, htk, map_one])
  have h2 : orderOf (QuotientGroup.mk' N (n * o)) ∣ Nat.card O := by
    have hn1 : QuotientGroup.mk' N n = 1 :=
      MonoidHom.mem_ker.mp (by rwa [QuotientGroup.ker_mk'])
    rw [map_mul, hn1, one_mul]
    exact (orderOf_map_dvd _ o).trans (Subgroup.orderOf_dvd_natCard O ho)
  have h3 := Nat.eq_one_of_dvd_coprimes (hO.pow_left k) h1 h2
  rwa [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3

theorem exists_rPart_map_eq {B : Type*} [Group B] (f : A →* B) (g : A) {r : ℕ}
    (hr : r.Prime) (hg : f g ^ r = 1) : ∃ m k : ℕ, (g ^ m) ^ r ^ k = 1 ∧ f (g ^ m) = f g := by
  obtain ⟨a, n, hrn, hn⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' r hr.one_lt.ne'
  have hcop : n.Coprime (orderOf (f g)) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hg)
      (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hr).mpr hrn))
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  refine ⟨n * m, a, ?_, ?_⟩
  · rw [← pow_mul, show n * m * r ^ a = r ^ a * n * m by ring, pow_mul, ← hn,
      pow_orderOf_eq_one, one_pow]
  · rw [map_pow, pow_mul, hm]

end Group

open CFSG.Open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {M : Subgroup G} {z : G}
  {Pbar : Sylow p (D1CzQuot p z)} {KC : Subgroup (D1CzQuot p z)}

theorem map_torusLift {P' : Sylow p G} (hRC : D1ReducedCentralizer p P' M z Pbar KC) :
    ((d1LiftX p (Subgroup.centralizer ({z} : Set G)) (P' : Subgroup G) KC).subgroupOf
        (Subgroup.centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p)) =
      (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC := by
  rw [map_d1LiftX, ← hRC.sylow_eq]

theorem eq_of_mk_eq_torusLift (hp : p.Prime) {T : Subgroup G} (hTp : IsPGroup p T) {a b : G}
    (haT : a ∈ T) (hbT : b ∈ T) (ha : a ∈ Subgroup.centralizer ({z} : Set G))
    (hb : b ∈ Subgroup.centralizer ({z} : Set G))
    (hab : QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p)
      ⟨a, ha⟩ = QuotientGroup.mk' (primeComplementCore p) ⟨b, hb⟩) : a = b :=
  congrArg Subtype.val (eq_of_mk_eq_of_isPGroup hp _ (primeComplementCore_coprime p)
    (hTp.comap_subtype (K := Subgroup.centralizer ({z} : Set G)))
    (a := ⟨a, ha⟩) (b := ⟨b, hb⟩) haT hbT hab)

omit [Finite G] in
theorem le_torusLift {X P' : Subgroup G} (hXP : X ≤ P')
    (hXC : X ≤ Subgroup.centralizer ({z} : Set G))
    (hpair : (X.subgroupOf (Subgroup.centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p)) =
      centerOf ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC)) :
    X ≤ d1LiftX p (Subgroup.centralizer ({z} : Set G)) P' KC := by
  intro x hx
  have hZ : QuotientGroup.mk' (primeComplementCore p) ⟨x, hXC hx⟩ ∈
      centerOf ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC) :=
    hpair ▸ Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)
  exact ⟨⟨x, hXC hx⟩, ⟨hXP hx, hZ.1.2⟩, rfl⟩

theorem mem_of_mk_mem_centerOf (hp : p.Prime) {T X : Subgroup G} (hTp : IsPGroup p T)
    (hXT : X ≤ T)
    (hpair : (X.subgroupOf (Subgroup.centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p)) =
      centerOf ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC))
    {t : G} (ht : t ∈ T) (htC : t ∈ Subgroup.centralizer ({z} : Set G))
    (hZ : QuotientGroup.mk' (primeComplementCore p) ⟨t, htC⟩ ∈
      centerOf ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC)) : t ∈ X := by
  rw [← hpair] at hZ
  obtain ⟨x, hx, hxt⟩ := hZ
  have hxX : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hx
  rwa [← eq_of_mk_eq_torusLift hp hTp (hXT hxX) ht x.2 htC hxt]

theorem commute_torusLift_of_mem {T X : Subgroup G} (hp : p.Prime) (hTp : IsPGroup p T)
    (hTC : T ≤ Subgroup.centralizer ({z} : Set G)) (hXT : X ≤ T)
    (hTmap : (T.subgroupOf (Subgroup.centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p)) =
      (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC)
    (hpair : (X.subgroupOf (Subgroup.centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p)) =
      centerOf ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC)) :
    ∀ t ∈ T, ∀ x ∈ X, t * x = x * t := by
  intro t ht x hx
  set π := QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p)
  have htC := hTC ht
  have hxC := hTC (hXT hx)
  have hπt : π ⟨t, htC⟩ ∈ (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC :=
    hTmap ▸ Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ht)
  have hπx : π ⟨x, hxC⟩ ∈ centerOf ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC) :=
    hpair ▸ Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)
  have hcomm := Subgroup.mem_centralizer_iff.mp hπx.2 _ hπt
  refine eq_of_mk_eq_torusLift hp hTp (T.mul_mem ht (hXT hx)) (T.mul_mem (hXT hx) ht)
    (Subgroup.mul_mem _ htC hxC) (Subgroup.mul_mem _ hxC htC) ?_
  change π (⟨t, htC⟩ * ⟨x, hxC⟩) = π (⟨x, hxC⟩ * ⟨t, htC⟩)
  rw [map_mul, map_mul, hcomm]

theorem commutator_mem_of_torusLift {T X : Subgroup G} (hp : p.Prime) (hTp : IsPGroup p T)
    (hTC : T ≤ Subgroup.centralizer ({z} : Set G)) (hXT : X ≤ T)
    (hTmap : (T.subgroupOf (Subgroup.centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p)) =
      (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC)
    (hpair : (X.subgroupOf (Subgroup.centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p)) =
      centerOf ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC))
    (htil : SPLCtildeFacts p M z Pbar KC) : ∀ a ∈ T, ∀ b ∈ T, a * b * a⁻¹ * b⁻¹ ∈ X := by
  intro a ha b hb
  set π := QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p)
  have haC := hTC ha
  have hbC := hTC hb
  have hπa : π ⟨a, haC⟩ ∈ (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC :=
    hTmap ▸ Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ha)
  have hπb : π ⟨b, hbC⟩ ∈ (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC :=
    hTmap ▸ Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hb)
  have hmemC : a * b * a⁻¹ * b⁻¹ ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ haC hbC)
      (Subgroup.inv_mem _ haC)) (Subgroup.inv_mem _ hbC)
  refine mem_of_mk_mem_centerOf hp hTp hXT hpair
    (T.mul_mem (T.mul_mem (T.mul_mem ha hb) (T.inv_mem ha)) (T.inv_mem hb)) hmemC ?_
  have h := htil.comm _ hπa _ hπb
  convert h using 1
  change π (⟨a, haC⟩ * ⟨b, hbC⟩ * ⟨a, haC⟩⁻¹ * ⟨b, hbC⟩⁻¹) = _
  simp only [map_mul, map_inv]

theorem pow_eq_one_of_torusLift {T : Subgroup G} (hp : p.Prime) (hTp : IsPGroup p T)
    (hTC : T ≤ Subgroup.centralizer ({z} : Set G))
    (hTmap : (T.subgroupOf (Subgroup.centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p)) =
      (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC)
    (htil : SPLCtildeFacts p M z Pbar KC) : ∀ a ∈ T, a ^ p = 1 := by
  intro a ha
  set π := QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p)
  have haC := hTC ha
  have hπa : π ⟨a, haC⟩ ∈ (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC :=
    hTmap ▸ Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ha)
  refine eq_of_mk_eq_torusLift hp hTp (T.pow_mem ha p) T.one_mem
    (Subgroup.pow_mem _ haC p) (Subgroup.one_mem _) ?_
  change π (⟨a, haC⟩ ^ p) = π 1
  rw [map_pow, htil.exp _ hπa, map_one]

omit [Finite G] in
theorem exists_ne_of_torusLift {T : Subgroup G}
    (hTmap : (T.subgroupOf (Subgroup.centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p)) =
      (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC)
    (htil : SPLCtildeFacts p M z Pbar KC) : ∃ a ∈ T, ∃ b ∈ T, a * b ≠ b * a := by
  obtain ⟨a', ha', b', hb', hne⟩ := htil.nonab
  rw [← hTmap] at ha' hb'
  obtain ⟨a, ha, rfl⟩ := ha'
  obtain ⟨b, hb, rfl⟩ := hb'
  refine ⟨a, Subgroup.mem_subgroupOf.mp ha, b, Subgroup.mem_subgroupOf.mp hb, fun h => hne ?_⟩
  rw [← map_mul, ← map_mul]
  exact congrArg _ (Subtype.ext h)

theorem card_torusLift {T : Subgroup G} (hp : p.Prime) (hTp : IsPGroup p T)
    (hTC : T ≤ Subgroup.centralizer ({z} : Set G))
    (hTmap : (T.subgroupOf (Subgroup.centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p)) =
      (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC) :
    Nat.card T = Nat.card ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC : Subgroup _) := by
  have hTp' : IsPGroup p (T.subgroupOf (Subgroup.centralizer ({z} : Set G))) :=
    hTp.comap_subtype
  rw [← hTmap, card_map_mk_of_isPGroup hp _ (primeComplementCore_coprime p) hTp',
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTC).toEquiv]

theorem conj_mem_torusLift_mul {T : Subgroup G} (hTC : T ≤ Subgroup.centralizer ({z} : Set G))
    (hTmap : (T.subgroupOf (Subgroup.centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p)) =
      (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC)
    (htil : SPLCtildeFacts p M z Pbar KC) :
    ∀ g ∈ Subgroup.centralizer ({z} : Set G) ⊓ M, ∀ t ∈ T, ∃ t' ∈ T,
      ∃ o ∈ GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)), g * t * g⁻¹ = t' * o := by
  intro g hg t ht
  set π := QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p)
  set g' : Subgroup.centralizer ({z} : Set G) := ⟨g, hg.1⟩
  set t' : Subgroup.centralizer ({z} : Set G) := ⟨t, hTC ht⟩
  have hπg : π g' ∈ splXt0 p M z := ⟨g', Subgroup.mem_subgroupOf.mpr hg, rfl⟩
  have hπt : π t' ∈ (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC :=
    hTmap ▸ Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ht)
  have h := htil.norm _ hπg _ hπt
  rw [← hTmap] at h
  obtain ⟨s, hs, hseq⟩ := h
  have hker : π (s⁻¹ * (g' * t' * g'⁻¹)) = 1 := by
    rw [map_mul, map_inv, hseq, map_mul, map_mul, map_inv]
    group
  refine ⟨s, Subgroup.mem_subgroupOf.mp hs, _,
    (mk'_primeComplementCore_eq_one_iff p _).mp hker, ?_⟩
  change ((g' * t' * g'⁻¹ : Subgroup.centralizer ({z} : Set G)) : G) = _
  rw [← Subgroup.coe_mul, mul_inv_cancel_left]

end CFSG.AGLEmbedding.SPLMSide
