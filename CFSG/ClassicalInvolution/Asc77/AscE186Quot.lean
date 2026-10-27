module

public import CFSG.ClassicalInvolution.Asc77.AscE184Quot

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {N : Subgroup G} [N.Normal]

theorem exists_lift_sylow (hN : Odd (Nat.card N)) {J : Subgroup G} {Rb : Subgroup (G ⧸ N)}
    (hRb : IsSylow2In Rb (J.map (QuotientGroup.mk' N))) :
    ∃ R : Subgroup G, IsSylow2In R J ∧ R.map (QuotientGroup.mk' N) = Rb := by
  set mk := QuotientGroup.mk' N with hmk
  obtain ⟨R₀, hR₀, -⟩ := IsSylow2In.exists_ge (T := ⊥) (P := J) IsPGroup.of_bot bot_le
  obtain ⟨x, hxJ, hx⟩ := exists_conjSub_eq_of_isSylow2In (isSylow2In_map_mk hN hR₀) hRb
  obtain ⟨j, hjJ, rfl⟩ := hxJ
  refine ⟨conjSub j R₀, ?_, ?_⟩
  · have := IsSylow2In.conj hR₀ j
    rwa [conjSub_eq_self_of_mem hjJ] at this
  · rw [AscQuot.map_conjSub]
    exact hx

theorem exists_lift_RSet (hp : p ≠ 2) (hΩ' : HypOmegaMod p f (quotFamily Ω N))
    (hN : Odd (Nat.card N)) {J : Subgroup G} (hJ : J ∈ Ω)
    {Rb : Subgroup (G ⧸ N)} (hRb : Rb ∈ RSet (quotFamily Ω N))
    (hRbJ : Rb ≤ J.map (QuotientGroup.mk' N)) :
    ∃ R ∈ RSet Ω, R ≤ J ∧ R.map (QuotientGroup.mk' N) = Rb := by
  have hRbsyl : IsSylow2In Rb (J.map (QuotientGroup.mk' N)) :=
    hΩ'.isSylow2In_of_mem_RSet_of_le hp (map_mem_quotFamily hJ) hRb hRbJ
  obtain ⟨R, hR, hmap⟩ := exists_lift_sylow hN hRbsyl
  exact ⟨R, mem_RSet_of_isSylow2In hJ hR, hR.1, hmap⟩

theorem exists_lift_twin (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hN : Odd (Nat.card N)) {K : Subgroup G} (hK : K ∈ Ω) {Lb : Subgroup (G ⧸ N)}
    (hLb : Lb ∈ twinSet (quotFamily Ω N) (K.map (QuotientGroup.mk' N))) :
    ∃ L ∈ twinSet Ω K, L.map (QuotientGroup.mk' N) = Lb := by
  set mk := QuotientGroup.mk' N with hmk
  obtain ⟨hLbΩ, zb, hzbK, hzbL⟩ := hLb
  obtain ⟨L₀, hL₀, rfl⟩ := hLbΩ
  obtain ⟨z, hz⟩ := hΩ.exists_uniqueInvolution hp hq hK
  obtain ⟨z₀, hz₀⟩ := hΩ.exists_uniqueInvolution hp hq hL₀
  have e1 : mk z = zb :=
    (isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN K) hz).eq hzbK
  have e2 : mk z₀ = zb :=
    (isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN L₀) hz₀).eq hzbL
  obtain ⟨n, hn, hnz⟩ := exists_conj_eq_of_map_eq hN hz.sq hz₀.sq (e1.trans e2.symm)
  refine ⟨conjSub n L₀, ⟨hΩ.conjInvariant n L₀ hL₀, z, hz, ?_⟩, ?_⟩
  · have := hz₀.conj n
    rwa [hnz] at this
  · rw [AscQuot.map_conjSub, show mk n = 1 from (QuotientGroup.eq_one_iff _).mpr hn,
      conjSub_one]

theorem exists_lift_kperp (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hΩ' : HypOmegaMod p f (quotFamily Ω N)) (hN : Odd (Nat.card N)) {L : Subgroup G} (hL : L ∈ Ω)
    {Jb : Subgroup (G ⧸ N)}
    (hJb : Jb ∈ KPerp (quotFamily Ω N) (L.map (QuotientGroup.mk' N))) :
    ∃ J ∈ KPerp Ω L, J.map (QuotientGroup.mk' N) = Jb := by
  set mk := QuotientGroup.mk' N with hmk
  rcases hJb with rfl | ⟨hJbΩ, hne, Rb, hRb, hRbJ, hRbN⟩
  · exact ⟨L, Set.mem_insert _ _, rfl⟩
  · obtain ⟨J₀, hJ₀, rfl⟩ := hJbΩ
    obtain ⟨R'', hR'', hR''J, hR''map⟩ := exists_lift_RSet hp hΩ' hN hJ₀ hRb hRbJ
    have hR''2 : IsPGroup 2 R'' := (hΩ.isSylow2In_of_mem_RSet_of_le hp hJ₀ hR'' hR''J).2.1
    obtain ⟨m, hm, hmN⟩ := exists_conj_normalizer hp hq hΩ hN hL hR''2 (fun u hu =>
      hRbN (hR''map ▸ Subgroup.mem_map_of_mem _ hu))
    have hmk : mk m = 1 := (QuotientGroup.eq_one_iff _).mpr hm
    have hJm : J₀ ∈ omegaNbr Ω (conjSub m L) := by
      refine ⟨hJ₀, fun h => hne ?_, R'', hR'', hR''J, hmN⟩
      show J₀.map mk = L.map mk
      rw [h, AscQuot.map_conjSub, hmk, conjSub_one]
    have h1 := omegaNbr_conj hΩ.conjInvariant hJm m⁻¹
    rw [conjSub_inv_conjSub] at h1
    refine ⟨conjSub m⁻¹ J₀, Set.mem_insert_of_mem _ h1, ?_⟩
    rw [AscQuot.map_conjSub, map_inv, hmk, inv_one, conjSub_one]

omit [Finite G] in
theorem exists_involution_lift (hN : Odd (Nat.card N)) {L J : Subgroup G} {a : G ⧸ N}
    (ha : a ∈ L.map (QuotientGroup.mk' N) ⊔ J.map (QuotientGroup.mk' N)) (ha1 : a ≠ 1)
    (ha2 : a * a = 1) :
    ∃ b ∈ L ⊔ J, b ≠ 1 ∧ b * b = 1 ∧ QuotientGroup.mk' N b = a := by
  set mk := QuotientGroup.mk' N with hmk
  rw [← Subgroup.map_sup] at ha
  obtain ⟨b₁, hb₁, rfl⟩ := ha
  have hsq : b₁ * b₁ ∈ N := by
    have : mk (b₁ * b₁) = 1 := by rw [map_mul]; exact ha2
    exact (QuotientGroup.eq_one_iff _).mp this
  have hodd : Odd (orderOf (b₁ * b₁)) := hN.of_dvd_nat (Subgroup.orderOf_dvd_natCard N hsq)
  obtain ⟨j, hj⟩ := hodd
  refine ⟨b₁ ^ (2 * j + 1), (L ⊔ J).pow_mem hb₁ _, ?_, ?_, ?_⟩
  · intro h
    apply ha1
    have : mk (b₁ ^ (2 * j + 1)) = mk b₁ := by
      rw [map_pow, pow_succ, pow_mul, pow_two, ha2, one_pow, one_mul]
    rw [← this, h, map_one]
  · have h1 : (b₁ * b₁) ^ (2 * j + 1) = 1 := by
      rw [← hj]
      exact pow_orderOf_eq_one _
    calc b₁ ^ (2 * j + 1) * b₁ ^ (2 * j + 1) = b₁ ^ (2 * (2 * j + 1)) := by
          rw [← pow_add]
          congr 1
          ring
      _ = (b₁ * b₁) ^ (2 * j + 1) := by rw [pow_mul, pow_two]
      _ = 1 := h1
  · rw [map_pow, pow_succ, pow_mul, pow_two, ha2, one_pow, one_mul]

omit [Finite G] in
theorem centralizer_map_le (hN : Odd (Nat.card N)) {a : G} (ha : a * a = 1) :
    Subgroup.centralizer ({QuotientGroup.mk' N a} : Set (G ⧸ N)) ≤
      (Subgroup.centralizer ({a} : Set G)).map (QuotientGroup.mk' N) := by
  intro x hx
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
  rw [Subgroup.mem_centralizer_singleton_iff] at hx
  have hcomm : QuotientGroup.mk' N (g * a * g⁻¹) = QuotientGroup.mk' N a := by
    rw [map_mul, map_mul, map_inv, hx]
    group
  have hsq : (g * a * g⁻¹) * (g * a * g⁻¹) = 1 := by
    calc (g * a * g⁻¹) * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
      _ = 1 := by rw [ha]; group
  obtain ⟨n, hn, hna⟩ := exists_conj_eq_of_map_eq hN hsq ha hcomm
  refine ⟨n⁻¹ * g, ?_, ?_⟩
  · show n⁻¹ * g ∈ Subgroup.centralizer ({a} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc n⁻¹ * g * a = (n⁻¹ * (g * a * g⁻¹) * n) * (n⁻¹ * g) := by group
      _ = a * (n⁻¹ * g) := by rw [← hna]; group
  · have hn1 : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff _).mpr hn
    have hnmk : QuotientGroup.mk' N n⁻¹ = 1 := by rw [map_inv, hn1, inv_one]
    rw [map_mul, hnmk, one_mul]

open scoped commutatorElement in
theorem E187C.map_ne_of_twin_of
    (h8R : ∀ {Q : Subgroup G}, Q ∈ RSet Ω → 8 ≤ Nat.card Q)
    (hcomm : ∀ {K J : Subgroup G} {z : G}, K ∈ Ω → J ∈ Ω → K ≠ J →
      IsUniqueInvolution K z → IsUniqueInvolution J z → ⁅K, J⁆ ≤ oddCoreOf K ⊓ oddCoreOf J)
    (hc2 : ∀ {K : Subgroup G} {z : G}, K ∈ Ω → IsUniqueInvolution K z → ∀ w ∈ K,
      IsPGroup 2 (Subgroup.zpowers w) → (∀ y ∈ K, ⁅w, y⁆ ∈ oddCoreOf K) → w = 1 ∨ w = z)
    (hN : Odd (Nat.card N)) {K K' : Subgroup G} (hK : K ∈ Ω) (hK' : K' ∈ twinSet Ω K)
    (hne : K' ≠ K) :
    K'.map (QuotientGroup.mk' N) ≠ K.map (QuotientGroup.mk' N) := by
  intro heq
  set mk := QuotientGroup.mk' N with hmk
  obtain ⟨hK'Ω, z, hz, hz'⟩ := hK'
  obtain ⟨V, hV, hVsyl, -⟩ :=
    exists_mem_RSet_ge hK (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup G)) bot_le
  have hV8 := h8R hV
  have hVN : V ⊓ N = ⊥ :=
    AscQuot.inf_eq_bot_of_isPGroup_of_odd N hVsyl.2.1 hVsyl.1 (odd_natCard_inf hN K)
  have hsub : ∀ y ∈ V.map mk, y = 1 ∨ y = mk z := by
    rintro _ ⟨x, hxV, rfl⟩
    have hxbar : mk x ∈ K'.map mk := by
      rw [heq]
      exact Subgroup.mem_map_of_mem _ (hVsyl.1 hxV)
    obtain ⟨y, hy, hyx⟩ := hxbar
    have hx2 : IsPGroup 2 (Subgroup.zpowers x) :=
      hVsyl.2.1.to_le (Subgroup.zpowers_le.mpr hxV)
    rcases E187C.eq_one_or_eq_of_map_eq_of_twin_of hcomm hc2 hN hK hK'Ω (Ne.symm hne) hz hz' hy
      (hVsyl.1 hxV) hx2 hyx with h1 | h1
    · left
      rw [h1, map_one]
    · right
      rw [h1]
  have hcard2 : Nat.card ↥(V.map mk) ≤ 2 := natCard_subgroup_le_two_of_subset hsub
  have hcardV : Nat.card ↥(V.map mk) = Nat.card V :=
    (Nat.card_congr (AscQuot.quotRestrictEquiv hVN).toEquiv).symm
  omega

theorem map_ne_of_twin (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hN : Odd (Nat.card N)) {K K' : Subgroup G} (hK : K ∈ Ω) (hK' : K' ∈ twinSet Ω K)
    (hne : K' ≠ K) :
    K'.map (QuotientGroup.mk' N) ≠ K.map (QuotientGroup.mk' N) :=
  E187C.map_ne_of_twin_of (fun hQ => hΩ.eight_le_of_mem_RSet hp hQ)
    (fun hK hJ hKJ hzK hzJ => hΩ.comm_le_oddCore_of_twin hK hJ hKJ hzK hzJ)
    (fun hK hz => hΩ.center_two hp hq hK hz)
    hN hK hK' hne

end CFSG.ClassicalInvolution.Asc77
