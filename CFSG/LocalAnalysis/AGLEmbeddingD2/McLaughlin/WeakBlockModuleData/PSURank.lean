module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.PSUTorus
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.CensusRank
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.PSULift

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.AGLEmbedding CFSG.QuasithinUnique
  CFSG.AGLEmbedding.ParabHub CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem two_le_pRank_of_psu_cover (hGA : CFSG.Open.GriessAllModelsStatement)
    (hF : Nat.card F = (2 ^ 1) ^ 2) {n : ℕ} (hn : 6 ≤ n) (h3n : 3 ∣ n)
    {Y : Type} [Group Y] [Finite Y] (e : Y ≃* StatedProj (StatedSU n (2 ^ 1) F))
    (hYc : Subgroup.center Y = ⊥) {E : Type} [Group E] [Finite E] (hE : Group.IsPerfect E)
    (p : E →* Y) (hp : Function.Surjective p) (hk : p.ker ≤ Subgroup.center E)
    (hkc : Nat.card p.ker = 3) (T : Sylow 2 Y) (J : Subgroup Y)
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J) (PE : Subgroup E)
    (hPE : ∀ x : E, p x ∈ J → x ∈ PE) : 2 ≤ CFSG.Open.pRank 3 PE := by
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
  obtain ⟨g₀, g₁, h₀, h₁, hcomm, hg₀, hind⟩ := exists_torus_pair hF hn
  have hcube : ∀ w : SU (unitaryInvolution F 2 1) n, w ∈ α.ker → w ^ 3 = 1 → w = 1 := by
    intro w hw hw3
    have h1 : orderOf w ∣ 3 := orderOf_dvd_of_pow_eq_one hw3
    have h2 : orderOf w ∣ Nat.card α.ker := by
      have := Subgroup.orderOf_dvd_natCard α.ker hw
      exact this
    have hself : Nat.Coprime (orderOf w) (orderOf w) :=
      (hcop.coprime_dvd_left h1).coprime_dvd_right h2
    exact orderOf_eq_one_iff.mp (Nat.coprime_self _ |>.mp hself)
  have hF3 : Nat.card F - 1 = 3 := by rw [hF]; norm_num
  have hg₀3 : g₀ ^ 3 = 1 := by
    have := hQ.torus_pow _ g₀ h₀
    rwa [hF3] at this
  have hg₁3 : g₁ ^ 3 = 1 := by
    have := hQ.torus_pow _ g₁ h₁
    rwa [hF3] at this
  have hmem : ∀ g : SU (unitaryInvolution F 2 1) n,
      g ∈ borel (rootDatum hF n) (levelTorus (unitaryInvolution F 2 1)) → α g ∈ PE := by
    intro g hg
    apply hPE
    have : p (α g) = π' g := by rw [← MonoidHom.comp_apply, hcomp]
    rw [this]
    exact hBJ g hg
  have hb₀ : g₀ ∈ borel (rootDatum hF n) (levelTorus (unitaryInvolution F 2 1)) :=
    iSup_le_borel (Subgroup.mem_iSup_of_mem _ h₀)
  have hb₁ : g₁ ∈ borel (rootDatum hF n) (levelTorus (unitaryInvolution F 2 1)) :=
    iSup_le_borel (Subgroup.mem_iSup_of_mem _ h₁)
  set x : ↥PE := ⟨α g₀, hmem g₀ hb₀⟩ with hx
  set y : ↥PE := ⟨α g₁, hmem g₁ hb₁⟩ with hy
  have hx3 : x ^ 3 = 1 := Subtype.ext (by simp [hx, ← map_pow, hg₀3])
  have hy3 : y ^ 3 = 1 := Subtype.ext (by simp [hy, ← map_pow, hg₁3])
  have hxy : Commute x y := Subtype.ext (by simp [hx, hy, ← map_mul, hcomm])
  have hx1 : x ≠ 1 := fun h => hg₀ (hcube g₀ (by
    rw [MonoidHom.mem_ker]; exact congrArg Subtype.val h) hg₀3)
  have hxn : ∀ m : ℕ, x ^ m ≠ y := by
    intro m h
    have hα' : α (g₀ ^ m) = α g₁ := by
      have := congrArg Subtype.val h
      simpa [hx, hy, map_pow] using this
    have hw : g₀ ^ m * g₁⁻¹ ∈ α.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hα', mul_inv_cancel]
    have hcg : Commute g₀ g₁ := hcomm
    have hw3 : (g₀ ^ m * g₁⁻¹) ^ 3 = 1 := by
      rw [((hcg.pow_left m).inv_right).mul_pow, inv_pow, hg₁3, inv_one, mul_one, ← pow_mul,
        mul_comm, pow_mul, hg₀3, one_pow]
    have := hcube _ hw hw3
    exact hind m (mul_inv_eq_one.mp this)
  have := two_le_pRank_of_gens hx3 hy3 hxy hx1 hxn
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup PE]
  exact this

theorem two_le_pRank_of_psu_extension (hGA : CFSG.Open.GriessAllModelsStatement)
    (hF : Nat.card F = (2 ^ 1) ^ 2) {n : ℕ} (hn : 6 ≤ n) (h3n : 3 ∣ n)
    {X : Type} [Group X] [Finite X] (hperf : Group.IsPerfect X) (P : Subgroup X)
    (hZP : Subgroup.center X ≤ P) (h3 : 3 ∣ Nat.card (Subgroup.center X))
    (e : X ⧸ Subgroup.center X ≃* StatedProj (StatedSU n (2 ^ 1) F))
    (hYc : Subgroup.center (X ⧸ Subgroup.center X) = ⊥)
    {T : Subgroup (X ⧸ Subgroup.center X)} (hT : IsSylowTwoOf T ⊤)
    (hNJ : Subgroup.normalizer (T : Set (X ⧸ Subgroup.center X)) ≤
      P.map (QuotientGroup.mk' (Subgroup.center X))) :
    2 ≤ CFSG.Open.pRank 3 P := by
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
  have hrank := two_le_pRank_of_psu_cover hGA hF hn h3n e hYc hEperf p hp hkcen hkc T'
    (P.map (QuotientGroup.mk' (Subgroup.center X))) (by rw [hT']; exact hNJ) PE hPEmem
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
