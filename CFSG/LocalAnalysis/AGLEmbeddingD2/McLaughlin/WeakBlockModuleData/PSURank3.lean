module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.PSUTorus3
public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviBorel
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTwoSU
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThree
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.PSULift
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.PSUTorus
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.AGLEmbedding CFSG.QuasithinUnique
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.Assembly.LowTwoRank
  CFSG.LieType.Steinberg CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits

theorem three_le_pRank_of_lifted {K E : Type} [Group K] [Group E] [Finite E] (α : K →* E)
    (hcube : ∀ w ∈ α.ker, w ^ 3 = 1 → w = 1) (PE : Subgroup E) (g₀ g₁ g₂ : K)
    (h₀ : α g₀ ∈ PE) (h₁ : α g₁ ∈ PE) (h₂ : α g₂ ∈ PE)
    (c₀ : g₀ ^ 3 = 1) (c₁ : g₁ ^ 3 = 1) (c₂ : g₂ ^ 3 = 1)
    (m₀₁ : Commute g₀ g₁) (m₀₂ : Commute g₀ g₂) (m₁₂ : Commute g₁ g₂)
    (n₀ : g₀ ≠ 1) (n₁ : ∀ m : ℕ, g₀ ^ m ≠ g₁) (n₂ : ∀ a b : ℕ, g₀ ^ a * g₁ ^ b ≠ g₂) :
    3 ≤ CFSG.Open.pRank 3 PE := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set x : ↥PE := ⟨α g₀, h₀⟩ with hx
  set y : ↥PE := ⟨α g₁, h₁⟩ with hy
  set z : ↥PE := ⟨α g₂, h₂⟩ with hz
  have hx3 : x ^ 3 = 1 := Subtype.ext (by simp [hx, ← map_pow, c₀])
  have hy3 : y ^ 3 = 1 := Subtype.ext (by simp [hy, ← map_pow, c₁])
  have hz3 : z ^ 3 = 1 := Subtype.ext (by simp [hz, ← map_pow, c₂])
  have hxy : Commute x y := Subtype.ext (by simp [hx, hy, ← map_mul, m₀₁.eq])
  have hxz : Commute x z := Subtype.ext (by simp [hx, hz, ← map_mul, m₀₂.eq])
  have hyz : Commute y z := Subtype.ext (by simp [hy, hz, ← map_mul, m₁₂.eq])
  have hx1 : x ≠ 1 := fun h => n₀ (hcube g₀ (by
    rw [MonoidHom.mem_ker]; exact congrArg Subtype.val h) c₀)
  have hxn : ∀ m : ℕ, x ^ m ≠ y := by
    intro m h
    have hα' : α (g₀ ^ m) = α g₁ := by
      have := congrArg Subtype.val h
      simpa [hx, hy, map_pow] using this
    have hw : g₀ ^ m * g₁⁻¹ ∈ α.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hα', mul_inv_cancel]
    have hw3 : (g₀ ^ m * g₁⁻¹) ^ 3 = 1 := by
      rw [((m₀₁.pow_left m).inv_right).mul_pow, inv_pow, c₁, inv_one, mul_one, ← pow_mul,
        mul_comm, pow_mul, c₀, one_pow]
    exact n₁ m (mul_inv_eq_one.mp (hcube _ hw hw3))
  have hxyn : ∀ a b : ℕ, x ^ a * y ^ b ≠ z := by
    intro a b h
    have hα' : α (g₀ ^ a * g₁ ^ b) = α g₂ := by
      have := congrArg Subtype.val h
      simpa [hx, hy, hz, map_pow, map_mul] using this
    have hw : g₀ ^ a * g₁ ^ b * g₂⁻¹ ∈ α.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hα', mul_inv_cancel]
    have hu3 : (g₀ ^ a * g₁ ^ b) ^ 3 = 1 := by
      rw [((m₀₁.pow_left a).pow_right b).mul_pow, ← pow_mul, mul_comm, pow_mul, c₀, one_pow,
        ← pow_mul, mul_comm, pow_mul, c₁, one_pow, mul_one]
    have hcu : Commute (g₀ ^ a * g₁ ^ b) g₂ :=
      ((m₀₂.pow_left a).mul_left (m₁₂.pow_left b))
    have hw3 : (g₀ ^ a * g₁ ^ b * g₂⁻¹) ^ 3 = 1 := by
      rw [(hcu.inv_right).mul_pow, inv_pow, c₂, hu3, inv_one, mul_one]
    exact n₂ a b (mul_inv_eq_one.mp (hcube _ hw hw3))
  have := CFSG.SectionRank.ClassicalEven.three_le_pRank_of_gens hx3 hy3 hz3 hxy hxz hyz hx1 hxn
    hxyn
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup PE]
  exact this

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem exists_last_node_pair (hF : Nat.card F = (2 ^ 1) ^ 2) {n : ℕ} (he : Even n)
    {Y : Type} [Group Y] [Finite Y] {ζ : traceZero (unitaryInvolution F 2 1)}
    {π' : SU (unitaryInvolution F 2 1) n →* Y}
    (hQ : BorelQuotient (rootDatum hF n)
      (levelWeyl (unitaryInvolution_involutive hF) ζ) (levelTorus (unitaryInvolution F 2 1))
      π' (Nat.card F - 1)) (J : Subgroup Y)
    (hBJ : ∀ b ∈ borel (rootDatum hF n) (levelTorus (unitaryInvolution F 2 1)), π' b ∈ J)
    (hne : J.comap π' ≠ borel (rootDatum hF n) (levelTorus (unitaryInvolution F 2 1)))
    (hperf : ∀ V : Subgroup Y, V ≤ J → ⁅V, V⁆ = V → Nat.Coprime 3 (Nat.card V)) :
    ∃ x y : SU (unitaryInvolution F 2 1) n, π' x ∈ J ∧ π' y ∈ J ∧ x ^ 2 = 1 ∧ y ^ 2 = 1 ∧
      (x * y) ^ 3 = 1 ∧ x * y ≠ 1 ∧
      ∀ t ∈ ⨆ k, levelTorus (unitaryInvolution F 2 1) k, Commute t x ∧ Commute t y := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBA : borel (rootDatum hF n) (levelTorus (unitaryInvolution F 2 1)) ≤ J.comap π' := fun b hb => hBJ b hb
  obtain ⟨i, hi⟩ := exists_negRoot_le_of_borel_lt hQ.ct hQ.extras hBA hne
  have hroot : ∀ i : Fin (rootDatum hF n).rank, (Pi.single i 1 : Fin (rootDatum hF n).rank → ℤ) ∈ (rootDatum hF n).roots := fun i =>
    (RootSystem.ofCartan (rootDatum hF n).isFiniteType (rootDatum hF n).divisible).single_mem i
  have hroot' : ∀ i : Fin (rootDatum hF n).rank, (-Pi.single i 1 : Fin (rootDatum hF n).rank → ℤ) ∈ (rootDatum hF n).roots := fun i =>
    (RootSystem.ofCartan (rootDatum hF n).isFiniteType (rootDatum hF n).divisible).neg_mem _ (hroot i)
  have hLJ : rankOne (rootDatum hF n).rootGroup i ≤ J.comap π' := sup_le ((rootGroup_le_borel (hroot i) (ht_single_pos i)).trans hBA) hi
  obtain ⟨x, hx, y, hy, h3, c, hc⟩ := hasOrderThree_su hF i
  have hxyL : x * y ∈ rankOne (rootDatum hF n).rootGroup i :=
    mul_mem (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hy)
  have hxyc : x * y ∉ Subgroup.center (SU (unitaryInvolution F 2 1) n) := fun hcen =>
    hc (Subgroup.mem_center_iff.1 hcen c).symm
  have hxB : x ∈ borel (rootDatum hF n) (levelTorus (unitaryInvolution F 2 1)) := posUnipotent_le_borel (rootGroup_le_posUnipotent
    (hroot i) (ht_single_pos i) hx)
  have hπx : π' x ∈ J := hBJ x hxB
  have hπy : π' y ∈ J := hi hy
  have hk : ¬ i.val + 1 < n / 2 := by
    intro hk
    have hp := commutator_eq_self_of_isPerfect (su_short_isPerfect hF hk)
    have hord : orderOf (π' (x * y)) = 3 :=
      orderOf_eq_prime (by rw [← map_pow, h3, map_one]) fun h1 => hxyc (hQ.ker_central _ h1)
    have hdvd : 3 ∣ Nat.card ((rankOne (rootDatum hF n).rootGroup i).map π') := by
      have := Subgroup.orderOf_dvd_natCard ((rankOne (rootDatum hF n).rootGroup i).map π') ⟨x * y, hxyL, rfl⟩
      rwa [hord] at this
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
      (hperf _ (Subgroup.map_le_iff_le_comap.2 hLJ) (by rw [← Subgroup.map_commutator, hp])) hdvd
  have hcard6 : Nat.card ↥(rankOne (rootDatum hF n).rootGroup i) = 6 := su_last_even_card hF he hk
  have hcard2 : ∀ γ : Fin (rootDatum hF n).rank → ℤ, (γ = Pi.single i 1 ∨ γ = -Pi.single i 1) →
      Nat.card ((rootDatum hF n).rootGroup γ) = 2 := by
    intro γ hγ
    have hγr : γ ∈ (rootDatum hF n).roots := by rcases hγ with rfl | rfl <;> simp [hroot, hroot']
    have hle : (rootDatum hF n).rootGroup γ ≤ rankOne (rootDatum hF n).rootGroup i := by
      rcases hγ with rfl | rfl
      · exact le_sup_left
      · exact le_sup_right
    obtain ⟨k, hk⟩ := (hQ.pGroup γ hγr).exists_card_eq
    have hd : 2 ^ k ∣ 6 := hk ▸ hcard6 ▸ Subgroup.card_dvd_of_le hle
    have hk0 : k ≠ 0 := fun h0 => hQ.extras.ne_bot γ hγr
      (Subgroup.eq_bot_of_card_eq _ (by rw [hk, h0, pow_zero]))
    have hk1 : k ≤ 1 := by
      by_contra hk1
      have := (pow_dvd_pow 2 (show 2 ≤ k by omega)).trans hd
      norm_num at this
    rw [hk, show k = 1 by omega, pow_one]
  have hsq : ∀ γ : Fin (rootDatum hF n).rank → ℤ, (γ = Pi.single i 1 ∨ γ = -Pi.single i 1) →
      ∀ z ∈ (rootDatum hF n).rootGroup γ, z ^ 2 = 1 := fun γ hγ z hz => by
    have := Subgroup.orderOf_dvd_natCard _ hz
    rw [hcard2 γ hγ] at this
    exact orderOf_dvd_iff_pow_eq_one.1 this
  have hconj : ∀ γ : Fin (rootDatum hF n).rank → ℤ, (γ = Pi.single i 1 ∨ γ = -Pi.single i 1) →
      ∀ t ∈ ⨆ k, levelTorus (unitaryInvolution F 2 1) k, ∀ z ∈ (rootDatum hF n).rootGroup γ, t * z * t⁻¹ = z := by
    intro γ hγ t ht z hz
    have hγr : γ ∈ (rootDatum hF n).roots := by rcases hγ with rfl | rfl <;> simp [hroot, hroot']
    exact conj_eq_self_of_card_two (hcard2 γ hγ)
      (fun w hw => (Subgroup.mem_normalizer_iff.1
        (torus_le_normalizer_rootGroup hQ.ct hγr ht) w).1 hw) hz
  refine ⟨x, y, hπx, hπy, hsq _ (Or.inl rfl) x hx, hsq _ (Or.inr rfl) y hy, h3, ?_, fun t ht => ?_⟩
  · intro h1
    exact hxyc (h1 ▸ one_mem _)
  · exact ⟨mul_inv_eq_iff_eq_mul.1 (hconj _ (Or.inl rfl) t ht x hx),
      mul_inv_eq_iff_eq_mul.1 (hconj _ (Or.inr rfl) t ht y hy)⟩

theorem three_le_pRank_of_psu_cover (hGA : CFSG.Open.GriessAllModelsStatement)
    (hF : Nat.card F = (2 ^ 1) ^ 2) {n : ℕ} (hn : 6 ≤ n) (h3n : 3 ∣ n)
    {Y : Type} [Group Y] [Finite Y] (e : Y ≃* StatedProj (StatedSU n (2 ^ 1) F))
    (hYc : Subgroup.center Y = ⊥) {E : Type} [Group E] [Finite E] (hE : Group.IsPerfect E)
    (p : E →* Y) (hp : Function.Surjective p) (hk : p.ker ≤ Subgroup.center E)
    (hkc : Nat.card p.ker = 3) (T : Sylow 2 Y) (J : Subgroup Y)
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJne : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y))
    (hperf : ∀ V : Subgroup Y, V ≤ J → ⁅V, V⁆ = V → Nat.Coprime 3 (Nat.card V))
    (PE : Subgroup E) (hPE : ∀ x : E, p x ∈ J → x ∈ PE) : 3 ≤ CFSG.Open.pRank 3 PE := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have hB := borelQuotient_su hF (by omega) ζ hζ e
  obtain ⟨π', hπ's, hπ'k, hT⟩ := hB.exists_conj_eq T
  have hQ : BorelQuotient (rootDatum hF n)
      (levelWeyl (unitaryInvolution_involutive hF) ζ) (levelTorus (unitaryInvolution F 2 1))
      π' (Nat.card F - 1) :=
    { ct := hB.ct, extras := hB.extras, pGroup := hB.pGroup, surj := hπ's, odd := hB.odd,
      torus_pow := hB.torus_pow, ker_central := fun z hz => hB.ker_central z (hπ'k ▸ hz),
      ker_pow := fun z hz => hB.ker_pow z (hπ'k ▸ hz) }
  have hNπ := hQ.normalizer_map_posUnipotent
  rw [← hT] at hNπ
  have hBJ : ∀ b ∈ borel (rootDatum hF n) (levelTorus (unitaryInvolution F 2 1)), π' b ∈ J :=
    fun b hb => hNJ (by rw [hNπ]; exact ⟨b, hb, rfl⟩)
  have hker' : π'.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 1) n) :=
    fun z hz => hB.ker_central z (hπ'k ▸ hz)
  have hc : StatedClassicalModel Y .PSU n 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, by omega, fun h => by simp at h; omega⟩, F, inferInstance,
      inferInstance, hF, ⟨e⟩⟩
  obtain ⟨α, hα, hcomp, hcop⟩ := exists_lift_su_compat_three hGA hF (by omega) h3n hc hYc π'
    hπ's hker' hE p hp hk (IsPGroup.of_card (n := 1) (by rw [hkc]; norm_num)) hkc
  have hcube : ∀ w : SU (unitaryInvolution F 2 1) n, w ∈ α.ker → w ^ 3 = 1 → w = 1 := by
    intro w hw hw3
    have h1 : orderOf w ∣ 3 := orderOf_dvd_of_pow_eq_one hw3
    have h2 : orderOf w ∣ Nat.card α.ker := Subgroup.orderOf_dvd_natCard α.ker hw
    have hself : Nat.Coprime (orderOf w) (orderOf w) :=
      (hcop.coprime_dvd_left h1).coprime_dvd_right h2
    exact orderOf_eq_one_iff.mp (Nat.coprime_self _ |>.mp hself)
  have hF3 : Nat.card F - 1 = 3 := by rw [hF]; norm_num
  have hmemJ : ∀ g : SU (unitaryInvolution F 2 1) n, π' g ∈ J → α g ∈ PE := by
    intro g hg
    apply hPE
    have : p (α g) = π' g := by rw [← MonoidHom.comp_apply, hcomp]
    rw [this]
    exact hg
  have hmem : ∀ g : SU (unitaryInvolution F 2 1) n,
      g ∈ borel (rootDatum hF n) (levelTorus (unitaryInvolution F 2 1)) → α g ∈ PE :=
    fun g hg => hmemJ g (hBJ g hg)
  have hcub : ∀ (k : Fin (n / 2)) (g : SU (unitaryInvolution F 2 1) n),
      g ∈ levelTorus (unitaryInvolution F 2 1) k → g ^ 3 = 1 := fun k g hg => by
    have := hQ.torus_pow _ g hg
    rwa [hF3] at this
  have hbor : ∀ (k : Fin (n / 2)) (g : SU (unitaryInvolution F 2 1) n),
      g ∈ levelTorus (unitaryInvolution F 2 1) k →
      g ∈ borel (rootDatum hF n) (levelTorus (unitaryInvolution F 2 1)) := fun k g hg =>
    iSup_le_borel (Subgroup.mem_iSup_of_mem _ hg)
  by_cases hn8 : 8 ≤ n
  · obtain ⟨g₀, g₁, g₂, h₀, h₁, h₂, c₀₁, c₀₂, c₁₂, n₀, n₁, n₂⟩ := exists_torus_triple hF hn8
    exact three_le_pRank_of_lifted α hcube PE g₀ g₁ g₂ (hmem _ (hbor _ _ h₀))
      (hmem _ (hbor _ _ h₁)) (hmem _ (hbor _ _ h₂)) (hcub _ _ h₀) (hcub _ _ h₁) (hcub _ _ h₂)
      c₀₁ c₀₂ c₁₂ n₀ n₁ n₂
  · have hn6 : n = 6 := by obtain ⟨m, hm⟩ := h3n; omega
    have hne : J.comap π' ≠ borel (rootDatum hF n) (levelTorus (unitaryInvolution F 2 1)) := by
      intro he
      apply hJne
      rw [hNπ, ← he, Subgroup.map_comap_eq_self_of_surjective hπ's]
    obtain ⟨x, y, hπx, hπy, hx2, hy2, hxy3, hxy1, htor⟩ :=
      exists_last_node_pair hF (by rw [hn6]; decide) hQ J hBJ hne hperf
    obtain ⟨g₀, g₁, h₀, h₁, hcomm, hg₀, hind⟩ := exists_torus_pair hF hn
    have hT₀ : ∀ t ∈ levelTorus (unitaryInvolution F 2 1) (⟨0, by omega⟩ : Fin (n / 2)) ⊔
        levelTorus (unitaryInvolution F 2 1) (⟨1, by omega⟩ : Fin (n / 2)),
        t ∈ ⨆ k, levelTorus (unitaryInvolution F 2 1) k := by
      intro t ht
      exact (sup_le (le_iSup (fun k => levelTorus (unitaryInvolution F 2 1) k) _)
        (le_iSup (fun k => levelTorus (unitaryInvolution F 2 1) k) _)) ht
    have hg₀T := htor g₀ (hT₀ _ (Subgroup.mem_sup_left h₀))
    have hg₁T := htor g₁ (hT₀ _ (Subgroup.mem_sup_right h₁))
    have hcxy₀ : Commute g₀ (x * y) := hg₀T.1.mul_right hg₀T.2
    have hcxy₁ : Commute g₁ (x * y) := hg₁T.1.mul_right hg₁T.2
    refine three_le_pRank_of_lifted α hcube PE g₀ g₁ (x * y) (hmem _ (hbor _ _ h₀))
      (hmem _ (hbor _ _ h₁)) (hmemJ _ (by rw [map_mul]; exact mul_mem hπx hπy))
      (hcub _ _ h₀) (hcub _ _ h₁) hxy3 hcomm hcxy₀ hcxy₁ hg₀ hind ?_
    intro a b h
    have hu : g₀ ^ a * g₁ ^ b ∈ ⨆ k, levelTorus (unitaryInvolution F 2 1) k := by
      refine mul_mem (pow_mem (hT₀ _ (Subgroup.mem_sup_left h₀)) a)
        (pow_mem (hT₀ _ (Subgroup.mem_sup_right h₁)) b)
    have hcx := (htor _ hu).1
    rw [h] at hcx
    have hxy : x * y = y * x := by
      have h1 : x * (y * x) = x * (x * y) := by
        have := hcx.eq
        rw [mul_assoc] at this
        rw [← this]
      exact (mul_left_cancel h1).symm
    have hsq : (x * y) ^ 2 = 1 := by
      rw [pow_two, mul_assoc, ← mul_assoc y, ← hxy, mul_assoc, ← mul_assoc x, ← pow_two, hx2,
        one_mul, ← pow_two, hy2]
    exact hxy1 (CFSG.AGLEmbedding.eq_one_of_sq_eq_one_of_cube_eq_one hsq hxy3)

theorem three_le_pRank_of_psu_extension (hGA : CFSG.Open.GriessAllModelsStatement)
    (hF : Nat.card F = (2 ^ 1) ^ 2) {n : ℕ} (hn : 6 ≤ n) (h3n : 3 ∣ n)
    {X : Type} [Group X] [Finite X] (hperf : Group.IsPerfect X) (P : Subgroup X)
    (hZP : Subgroup.center X ≤ P) (h3 : 3 ∣ Nat.card (Subgroup.center X))
    (e : X ⧸ Subgroup.center X ≃* StatedProj (StatedSU n (2 ^ 1) F))
    (hYc : Subgroup.center (X ⧸ Subgroup.center X) = ⊥)
    {T : Subgroup (X ⧸ Subgroup.center X)} (hT : IsSylowTwoOf T ⊤)
    (hNJ : Subgroup.normalizer (T : Set (X ⧸ Subgroup.center X)) ≤
      P.map (QuotientGroup.mk' (Subgroup.center X)))
    (hJne : P.map (QuotientGroup.mk' (Subgroup.center X)) ≠ Subgroup.normalizer (T : Set (X ⧸ Subgroup.center X)))
    (hJperf : ∀ V : Subgroup (X ⧸ Subgroup.center X),
      V ≤ P.map (QuotientGroup.mk' (Subgroup.center X)) → ⁅V, V⁆ = V → Nat.Coprime 3 (Nat.card V)) :
    3 ≤ CFSG.Open.pRank 3 P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Y := X ⧸ Subgroup.center X with hY
  have hc : StatedClassicalModel Y .PSU n 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, by omega, fun h => by simp at h; omega⟩, F, inferInstance,
      inferInstance, hF, ⟨e⟩⟩
  obtain ⟨e0, he16, hM⟩ := card_hopfMultiplier_of_model_psu_two hGA hc
  have hdvd : Nat.card (Subgroup.center X) ∣ Nat.card (CFSG.Open.griessHopfMultiplier Y) :=
    card_center_dvd_card_griessHopfMultiplier hperf (MulEquiv.refl Y)
  have hMg : Nat.card (CFSG.Open.griessHopfMultiplier Y) = 3 * e0 := by
    rw [Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess Y).toEquiv, hM,
      Nat.gcd_eq_right h3n]
  obtain ⟨k, hk⟩ := h3
  have hk16 : k ∣ 16 := by
    have h1 : 3 * k ∣ 3 * e0 := by rw [← hk, ← hMg]; exact hdvd
    exact (Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1).trans he16
  obtain ⟨a, -, hka⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (by simpa using hk16 : k ∣ 2 ^ 4)
  obtain ⟨Z2', hZ2'⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥(Subgroup.center X)) 2
    (n := a) (by rw [hk, hka]; exact ⟨3, by ring⟩)
  set Z2 : Subgroup X := Z2'.map (Subgroup.center X).subtype with hZ2
  have hZ2c : Z2 ≤ Subgroup.center X := Subgroup.map_subtype_le Z2'
  haveI hZ2n : Z2.Normal := ⟨fun n hn g => by
    have h := Subgroup.mem_center_iff.mp (hZ2c hn) g
    have : g * n * g⁻¹ = n := by rw [h]; group
    rw [this]; exact hn⟩
  have hZ2card : Nat.card Z2 = 2 ^ a := by
    rw [hZ2, Subgroup.card_map_of_injective (Subgroup.center X).subtype_injective, hZ2']
  haveI : Group.IsPerfect X := hperf
  set E := X ⧸ Z2 with hE
  let p : E →* Y := QuotientGroup.map Z2 (Subgroup.center X) (MonoidHom.id X)
    (by simpa using hZ2c)
  have hpmk : ∀ x : X, p (QuotientGroup.mk x) = QuotientGroup.mk x := fun x => rfl
  have hp : Function.Surjective p := fun y => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨QuotientGroup.mk x, hpmk x⟩
  have hEperf : Group.IsPerfect E :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' Z2) (QuotientGroup.mk'_surjective _)
  have hkcen : p.ker ≤ Subgroup.center E := by
    intro x hx
    obtain ⟨x0, rfl⟩ := QuotientGroup.mk_surjective x
    rw [MonoidHom.mem_ker, hpmk, QuotientGroup.eq_one_iff] at hx
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g0, rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp hx g0]
  have hkc : Nat.card p.ker = 3 := by
    have h1 : Nat.card X = Nat.card E * Nat.card Z2 := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Z2]
    have h2 : Nat.card X = Nat.card Y * Nat.card (Subgroup.center X) := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X)]
    have h3' : Nat.card E = Nat.card Y * Nat.card p.ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup p.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective p hp).toEquiv]
    have hYpos : 0 < Nat.card Y := Nat.card_pos
    have hZ2pos : 0 < Nat.card Z2 := Nat.card_pos
    have : Nat.card Y * (Nat.card p.ker * Nat.card Z2) = Nat.card Y * (3 * 2 ^ a) := by
      rw [← mul_assoc, ← h3', ← h1, h2, hk, hka]
    have := Nat.eq_of_mul_eq_mul_left hYpos this
    rw [hZ2card] at this
    exact Nat.eq_of_mul_eq_mul_right (by positivity) this
  set PE : Subgroup E := P.map (QuotientGroup.mk' Z2) with hPE
  have hPEmem : ∀ x : E, p x ∈ P.map (QuotientGroup.mk' (Subgroup.center X)) → x ∈ PE := by
    intro x hx
    obtain ⟨x0, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hpmk] at hx
    obtain ⟨u, hu, hux⟩ := hx
    have : u⁻¹ * x0 ∈ Subgroup.center X := by
      exact QuotientGroup.eq.mp hux
    have hx0 : x0 ∈ P := by
      have := P.mul_mem hu (hZP this)
      simpa using this
    exact ⟨x0, hx0, rfl⟩
  obtain ⟨T', hT'⟩ := exists_sylow_of_isSylowTwoOf_top hT
  have hrank := three_le_pRank_of_psu_cover hGA hF hn h3n e hYc hEperf p hp hkcen hkc T'
    (P.map (QuotientGroup.mk' (Subgroup.center X))) (by rw [hT']; exact hNJ)
    (by rw [hT']; exact hJne) hJperf PE hPEmem
  set f : ↥P →* ↥PE := (QuotientGroup.mk' Z2).subgroupMap P with hf
  have hfs : Function.Surjective f := (QuotientGroup.mk' Z2).subgroupMap_surjective P
  have hfker : f.ker = Z2.subgroupOf P := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← QuotientGroup.eq_one_iff]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have hcop : Nat.Coprime 3 (Nat.card f.ker) := by
    rw [hfker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hZ2c.trans hZP)).toEquiv, hZ2card]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have hrk := CFSG.RankThreeCoreUniqueness.Helpers.pRank_top_eq_of_coprime_kernel 3
    Nat.prime_three f hfs hcop
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup P, hrk]
  exact hrank.trans_eq (CFSG.SectionRank.pRank_eq_pRank_top_subgroup PE)

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
