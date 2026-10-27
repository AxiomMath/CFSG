module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviSUOddK
import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviSUThree
import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviBorel
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTwoSU
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockSylowThreeAutExcArith

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg
  CFSG.LieType.BorelTits CFSG.LieType.CurtisTits

theorem card_biSup_dvd_pow_of_commutes {G : Type*} [Group G] [Finite G] {ι : Type*}
    [DecidableEq ι] {H : ι → Subgroup G} (hcomm : ∀ i j, ∀ a ∈ H i, ∀ b ∈ H j, Commute a b)
    {p : ℕ} (hp : ∀ i, Nat.card (H i) ∣ p) (s : Finset ι) :
    Nat.card (⨆ i ∈ s, H i : Subgroup G) ∣ p ^ s.card := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.iSup_insert, Finset.card_insert_of_notMem ha, pow_succ']
    exact (card_sup_dvd_mul_of_commutes (Commutes.biSup_left fun i _ => hcomm i a).symm).trans
      (mul_dvd_mul (hp a) ih)

variable {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = (2 ^ 1) ^ 2) {n : ℕ}

include hF in
theorem card_levelTorus_su_dvd_three (i : Fin (n / 2))
    (hpow : ∀ g ∈ levelTorus (unitaryInvolution F 2 1) (n := n) i, g ^ 3 = 1) :
    Nat.card (levelTorus (unitaryInvolution F 2 1) (n := n) i) ∣ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (SU (unitaryInvolution F 2 1) n) := Finite.of_injective _ Subtype.val_injective
  set H := levelTorus (unitaryInvolution F 2 1) (n := n) i
  choose c hc using fun x : H => SUExtras.exists_tFun_of_mem_levelTorus x.2
  have hinj : Function.Injective c := fun x y hxy =>
    Subtype.ext (SUExtras.mat_injective (by rw [hc x, hc y, hxy]))
  have hle : Nat.card H ≤ 3 := by
    have := Nat.card_le_card_of_injective c hinj
    rwa [Nat.card_units, hF] at this
  have h3 : IsPGroup 3 H := fun x => ⟨1, Subtype.ext (by simpa using hpow x x.2)⟩
  obtain ⟨m, hm⟩ := h3.exists_card_eq
  rw [hm] at hle ⊢
  have hm1 : m ≤ 1 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 (by simpa using hle)
  simpa using Nat.pow_dvd_pow 3 hm1

include hF in
theorem exists_card_dvd_parab_su_odd (hn5 : 5 ≤ n) (hn : ¬Even n) {W : Type} [Group W]
    [Finite W] (α : SU (unitaryInvolution F 2 1) n →* W) (hα : Function.Surjective α)
    (hker : α.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 1) n))
    (T : Sylow 2 W) (J : Subgroup W)
    (hNJ : Subgroup.normalizer ((T : Subgroup W) : Set W) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup W) : Set W))
    (hperf : ∀ U : Subgroup W, U ≤ J → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U)) :
    ∃ a : ℕ, Nat.card J ∣ 2 ^ a * 3 ^ (n / 2 + 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (SU (unitaryInvolution F 2 1) n) := Finite.of_injective _ Subtype.val_injective
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have hB := borelQuotient_su_level hF (by omega) (fun h => by simp at h; omega) hζ α hα hker
  obtain ⟨π', hπ', hker', hT⟩ := hB.exists_conj_eq T
  have hQ : BorelQuotient (rootDatum hF n) (levelWeyl (unitaryInvolution_involutive hF) ζ)
      (levelTorus (unitaryInvolution F 2 1)) π' (Nat.card F - 1) :=
    { ct := hB.ct, extras := hB.extras, pGroup := hB.pGroup, surj := hπ', odd := hB.odd
      torus_pow := hB.torus_pow
      ker_central := fun z hz => hB.ker_central z (hker' ▸ hz)
      ker_pow := fun z hz => hB.ker_pow z (hker' ▸ hz) }
  have hNπ := hQ.normalizer_map_posUnipotent
  rw [← hT] at hNπ
  have hBJ : (borel (rootDatum hF n) (levelTorus (unitaryInvolution F 2 1))).map π' ≤ J :=
    hNπ ▸ hNJ
  have hBA : borel (rootDatum hF n) (levelTorus (unitaryInvolution F 2 1)) ≤ J.comap π' :=
    fun b hb => hBJ ⟨b, hb, rfl⟩
  set k : Fin (n / 2) := ⟨n / 2 - 1, by omega⟩ with hkdef
  have hk : ¬k.val + 1 < n / 2 := by simp only [hkdef]; omega
  have hnodes : ∀ i ∈ negIndices (rootDatum hF n) (J.comap π'), i = k := by
    intro i hi
    by_contra hik
    have hshort : i.val + 1 < n / 2 := by
      have h1 : i.val < n / 2 := i.isLt
      have h2 : i.val ≠ n / 2 - 1 := fun h => hik (Fin.ext h)
      omega
    have hLi := rankOne_le_of_mem_negIndices hBA hi
    obtain ⟨a, ha, b, hb, hab3, c, hc⟩ := hasOrderThree_su hF i
    have habL : a * b ∈ rankOne (rootDatum hF n).rootGroup i :=
      mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)
    have hord : orderOf (π' (a * b)) = 3 :=
      orderOf_eq_prime (by rw [← map_pow, hab3, map_one]) fun h1 =>
        hc (Subgroup.mem_center_iff.1 (hQ.ker_central _ h1) c).symm
    have hdvd : 3 ∣ Nat.card ((rankOne (rootDatum hF n).rootGroup i).map π') := by
      have := Subgroup.orderOf_dvd_natCard ((rankOne (rootDatum hF n).rootGroup i).map π')
        ⟨a * b, habL, rfl⟩
      rwa [hord] at this
    have hp := commutator_eq_self_of_isPerfect (su_short_isPerfect hF hshort)
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
      (hperf _ (Subgroup.map_le_iff_le_comap.2 hLi) (by rw [← Subgroup.map_commutator, hp])) hdvd
  have hAne : J.comap π' ≠ borel (rootDatum hF n) (levelTorus (unitaryInvolution F 2 1)) := by
    intro he
    apply hJ
    rw [hNπ, ← he, Subgroup.map_comap_eq_self_of_surjective hπ']
  obtain ⟨i₀, hi₀⟩ := negIndices_nonempty_of_ne hQ.ct hQ.extras hBA hAne
  have hk₀ : k ∈ negIndices (rootDatum hF n) (J.comap π') := hnodes i₀ hi₀ ▸ hi₀
  have hLJ : (rankOne (rootDatum hF n).rootGroup k).map π' ≤ J :=
    Subgroup.map_le_iff_le_comap.2 (rankOne_le_of_mem_negIndices hBA hk₀)
  have hTJ : (⨆ i, levelTorus (unitaryInvolution F 2 1) (n := n) i).map π' ≤ J :=
    (Subgroup.map_mono (iSup_le_borel (D := rootDatum hF n)
      (H := levelTorus (unitaryInvolution F 2 1)))).trans hBJ
  have hUJ : (posUnipotentExcept (rootDatum hF n) k).map π' ≤ J :=
    (Subgroup.map_mono ((posUnipotentExcept_le_posUnipotent (D := rootDatum hF n) k).trans
      (posUnipotent_le_borel (D := rootDatum hF n)
        (H := levelTorus (unitaryInvolution F 2 1))))).trans hBJ
  have hTL := iSup_torus_le_normalizer_rankOne hQ.ct k
  have hLU := rankOne_le_normalizer_posUnipotentExcept hQ.ct hQ.extras k
  have hdec : ∀ z ∈ J, ∃ l ∈ rankOne (rootDatum hF n).rootGroup k,
      ∃ t ∈ ⨆ i, levelTorus (unitaryInvolution F 2 1) (n := n) i,
        ∃ u ∈ posUnipotentExcept (rootDatum hF n) k, z = π' (l * t * u) := by
    intro z hz
    obtain ⟨g, hg, _, ⟨b, hb, rfl⟩, rfl⟩ := exists_mul_of_mem_of_borel_le hQ.ct hQ.extras hπ'
      hBJ hz
    have hle : (⨆ i ∈ negIndices (rootDatum hF n) (J.comap π'),
        (rankOne (rootDatum hF n).rootGroup i).map π') ≤
          (rankOne (rootDatum hF n).rootGroup k).map π' := iSup₂_le fun i hi => by
      obtain rfl := hnodes i hi
      exact le_rfl
    obtain ⟨l, hl, rfl⟩ := hle hg
    obtain ⟨t, ht, u, hu, w, hw, rfl⟩ := exists_eq_mul_mul_of_mem_borel hQ.ct hQ.extras k hb
    have hwL : w ∈ rankOne (rootDatum hF n).rootGroup k := Subgroup.mem_sup_left hw
    refine ⟨l * (t * w * t⁻¹), mul_mem hl ((Subgroup.mem_normalizer_iff.1 (hTL ht) w).1 hwL), t,
      ht, w⁻¹ * u * w, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.1 (hLU (inv_mem hwL)) u).1 hu
      rwa [inv_inv] at this
    · rw [← map_mul]
      congr 1
      group
  set H := levelTorus (unitaryInvolution F 2 1) (n := n) with hH
  set L := rankOne (rootDatum hF n).rootGroup k with hL
  set T₀ : Subgroup (SU (unitaryInvolution F 2 1) n) := ⨆ i ∈ Finset.univ.erase k, H i with hT₀
  have hsplit : (⨆ i, H i) = H k ⊔ T₀ := by
    rw [hT₀, ← Finset.iSup_insert, Finset.insert_erase (Finset.mem_univ k)]
    simp only [Finset.mem_univ, iSup_true]
  have hLT : L ⊔ (⨆ i, H i) = L ⊔ T₀ := by
    rw [hsplit, ← sup_assoc, sup_eq_left.2 (hQ.ct.H_le k)]
  have hT₀T : T₀ ≤ ⨆ i, H i := hsplit ▸ le_sup_right
  have hT₀card : Nat.card T₀ ∣ 3 ^ (n / 2 - 1) := by
    have h := card_biSup_dvd_pow_of_commutes (H := H)
      (fun i j a ha b hb => hQ.extras.torus_commute i j a ha b hb)
      (fun i => card_levelTorus_su_dvd_three hF i fun g hg => by
        have h3 := hQ.torus_pow i g hg
        rwa [hF] at h3) (Finset.univ.erase k)
    rwa [Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin] at h
  have hLcard : Nat.card L = 216 :=
    (exists_su_three_two_heis hF (rankOneLastOddEquiv hF hn hk)).1
  have hAJ : (L ⊔ T₀).map π' ≤ J := by
    rw [Subgroup.map_sup]
    exact sup_le hLJ ((Subgroup.map_mono hT₀T).trans hTJ)
  have hprod : ∀ z ∈ J, ∃ a ∈ (L ⊔ T₀).map π',
      ∃ b ∈ (posUnipotentExcept (rootDatum hF n) k).map π', z = a * b := by
    intro z hz
    obtain ⟨l, hl, t, ht, u, hu, rfl⟩ := hdec z hz
    refine ⟨π' (l * t), ⟨l * t, ?_, rfl⟩, π' u, ⟨u, hu, rfl⟩, map_mul π' _ _⟩
    rw [← hLT]
    exact mul_mem (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right ht)
  have hU2 : IsPGroup 2 (posUnipotentExcept (rootDatum hF n) k) :=
    (isPGroup_iSup_pos hQ.extras hQ.pGroup).to_le
      (posUnipotentExcept_le_posUnipotent (D := rootDatum hF n) k)
  obtain ⟨b, hb⟩ := (hU2.map π').exists_card_eq
  refine ⟨3 + b, ?_⟩
  have h1 := card_dvd_mul_of_forall_mem_mul hAJ hUJ hprod
  have h2 := Subgroup.card_map_dvd (L ⊔ T₀) π'
  have h3 := card_sup_dvd_mul T₀ L (hT₀T.trans hTL)
  rw [sup_comm] at h3
  rw [hb] at h1
  refine h1.trans ((mul_dvd_mul_right (h2.trans (h3.trans
    (mul_dvd_mul_right hT₀card _))) _).trans (dvd_of_eq ?_))
  rw [hLcard, show n / 2 + 2 = (n / 2 - 1) + 3 by omega, pow_add, pow_add]
  ring

theorem three_dvd_index_of_su_odd (hGA : CFSG.Open.GriessAllModelsStatement)
    {Y₁ X : Type} [Group Y₁] [Finite Y₁] [Group X]
    (hY₁ : Group.IsPerfect Y₁) (ρ₁ : Y₁ →* X) (hρ₁ : Function.Surjective ρ₁)
    (hk : ρ₁.ker ≤ Subgroup.center Y₁) (h3 : IsPGroup 3 ρ₁.ker)
    (hX : Subgroup.center X = ⊥) {n : ℕ}
    (hc : CFSG.Open.StatedClassicalModel X .PSU n 2 1) (hn : ¬ Even n)
    (hcard : Nat.card X = CFSG.Open.ordTwistedA (n - 1) (2 ^ 1))
    (T₁ : Sylow 2 Y₁) (J₁ : Subgroup Y₁)
    (hNJ : Subgroup.normalizer ((T₁ : Subgroup Y₁) : Set Y₁) ≤ J₁)
    (hJ : J₁ ≠ Subgroup.normalizer ((T₁ : Subgroup Y₁) : Set Y₁))
    (hperf : ∀ U : Subgroup Y₁, U ≤ J₁ → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U)) :
    3 ∣ J₁.index := by
  obtain ⟨⟨-, -, hn3, hne⟩, F, hF, hFfin, hFcard, ⟨e⟩⟩ := id hc
  have := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := 1 * 2)
    (by rw [← Nat.card_eq_fintype_card, hFcard, pow_mul])
  have hn4 : 4 ≤ n := by
    by_contra h4
    exact hne (by rw [show n = 3 by omega]; rfl)
  have hn5 : 5 ≤ n := by
    rcases Nat.even_or_odd n with h | ⟨j, rfl⟩
    · exact absurd h hn
    · omega
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hFcard
  have hB := borelQuotient_su hFcard (by omega) ζ hζ e
  obtain ⟨α, hα, hαker⟩ := exists_lift_su hGA hFcard hn4 hc hX _ hB.surj
    (fun z hz => hB.ker_central z hz) hY₁ ρ₁ hρ₁ hk h3
  obtain ⟨a, ha⟩ := exists_card_dvd_parab_su_odd hFcard hn5 hn α hα hαker T₁ J₁ hNJ hJ hperf
  have hY3 : 3 ^ (n / 2 + 3) ∣ Nat.card J₁ * J₁.index := by
    rw [J₁.card_mul_index]
    exact (hcard ▸ three_pow_dvd_ordTwistedA_odd hn5 hn).trans
      (Subgroup.card_dvd_of_surjective hρ₁)
  by_contra h3i
  have hcop : Nat.Coprime (3 ^ (n / 2 + 3)) J₁.index :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3i)
  have h2 : Nat.Coprime (3 ^ (n / 2 + 3)) (2 ^ a) := Nat.Coprime.pow _ _ (by norm_num)
  have h33 := h2.dvd_of_dvd_mul_left ((hcop.dvd_of_dvd_mul_right hY3).trans ha)
  have := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 3)).1 h33
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
