module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDispatchGlue
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinearCover
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinearFlag
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinearCyc

public section

namespace CFSG.AGLEmbedding

namespace ToralCensus

open CFSG.Open CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.AGLEmbedding.ParabPrime (perfectJoin le_perfectJoin perfectJoin_le perfectJoin_perfect)

theorem exists_mulEquiv_projectiveSL_of_isLieOf {X : Type} [Group X] (h : IsLieOf IdxA X) :
    ∃ n f : ℕ, 2 ≤ n ∧ 1 ≤ f ∧ Nonempty (X ≃* projectiveSL n (GaloisField 2 f)) := by
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := h
  cases d with
  | A r q =>
    change q.p = 2 at hd
    have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    obtain ⟨p, k, hp, hk⟩ := q
    change p = 2 at hd
    subst hd
    have : Fact (Nat.Prime 2) := ⟨hp⟩
    exact ⟨r + 1, k, by omega, hk, ⟨(e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL
      r ⟨2, k, hp, hk⟩ hv)).trans (LinearCover.projectiveSpecialLinearEquivProjectiveSL _ _)⟩⟩
  | _ => exact hd.elim

theorem exists_compat_of_center_eq_bot {L : Type} [Group L] (hZ : Subgroup.center L = ⊥)
    {n : ℕ} {K : Type} [Field K] (e : L ⧸ Subgroup.center L ≃* projectiveSL n K) :
    ∃ ρ : Matrix.SpecialLinearGroup (Fin n) K →* L,
      ∀ g, e (QuotientGroup.mk (ρ g)) = proj n K g := by
  have hinj : Function.Injective (CFSG.GH74.Generic.centralQuotientMap e) := by
    rw [← MonoidHom.ker_eq_bot_iff, CFSG.GH74.Generic.centralQuotientMap_ker, hZ]
  let φ := MulEquiv.ofBijective (CFSG.GH74.Generic.centralQuotientMap e)
    ⟨hinj, CFSG.GH74.Generic.centralQuotientMap_surjective e⟩
  refine ⟨φ.symm.toMonoidHom.comp (proj n K), fun g => ?_⟩
  rw [← CFSG.GH74.Generic.centralQuotientMap_apply]
  exact φ.apply_symm_apply (proj n K g)

theorem gcd_two_two_pow_pred_eq_one {f : ℕ} (hf : 1 ≤ f) : Nat.gcd 2 (2 ^ f - 1) = 1 := by
  have hodd : Odd (2 ^ f - 1) :=
    Nat.Even.sub_odd (Nat.one_le_two_pow) ((Nat.even_pow' (by omega)).mpr even_two) odd_one
  exact Nat.coprime_two_left.mpr hodd

theorem exists_cover_comap_eq_flagStabilizer
    (hGA : GriessAllModelsStatement) {Y : Type} [Group Y]
    [Finite Y] {L J : Subgroup Y} (hCP : CompParab L J)
    (hA : IsLieOf IdxA (↥L ⧸ Subgroup.center ↥L)) :
    ∃ (n f : ℕ) (ρ : Matrix.SpecialLinearGroup (Fin n) (GaloisField 2 f) →* ↥L)
      (e : ↥L ⧸ Subgroup.center ↥L ≃* projectiveSL n (GaloisField 2 f)) (I : Set ℕ),
      3 ≤ n ∧ 1 ≤ f ∧ Function.Surjective ρ ∧
      ρ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) (GaloisField 2 f)) ∧
      (∀ g, e (QuotientGroup.mk (ρ g)) = proj n (GaloisField 2 f) g) ∧
      (∀ i ∈ I, 1 ≤ i ∧ i < n) ∧ I.Nonempty ∧ (∃ i, 1 ≤ i ∧ i < n ∧ i ∉ I) ∧
      (J.subgroupOf L).comap ρ = flagStabilizer n (GaloisField 2 f) I := by
  obtain ⟨n, f, hn, hf, ⟨e⟩⟩ := exists_mulEquiv_projectiveSL_of_isLieOf hA
  have hq := hCP.comp.2.2
  have hcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨ρ, hρs, -, hρ⟩ : ∃ ρ : Matrix.SpecialLinearGroup (Fin n) (GaloisField 2 f) →* ↥L,
      Function.Surjective ρ ∧
      ρ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) (GaloisField 2 f)) ∧
      ∀ g, e (QuotientGroup.mk (ρ g)) = proj n (GaloisField 2 f) g := by
    by_cases h3 : 3 ≤ n
    · exact kFactCoverLinear_of_griess hGA Y L hCP.comp hCP.odd n _ h3 e
    · have : Fintype (GaloisField 2 f) := Fintype.ofFinite _
      have hdvd := oddCenterLinear_of_griess hGA Y L hCP.comp hCP.odd n (GaloisField 2 f) ⟨e⟩
      rw [show n = 2 by omega, ← Nat.card_eq_fintype_card, hcard,
        gcd_two_two_pow_pred_eq_one hf, Nat.dvd_one] at hdvd
      obtain ⟨ρ, hρ⟩ := exists_compat_of_center_eq_bot (Subgroup.eq_bot_of_card_eq _ hdvd) e
      obtain ⟨hs, hk⟩ := surjective_and_ker_le_of_compat hq.1 e ρ hρ
      exact ⟨ρ, hs, hk, hρ⟩
  obtain ⟨σ, e', I, hσs, hσ, hI, hcomap, hne, hnb⟩ :=
    exists_comap_eq_flagStabilizer hCP.odd (by omega) e hρs hρ hCP.parab
  obtain ⟨-, hσk⟩ := surjective_and_ker_le_of_compat hq.1 e' σ hσ
  obtain ⟨i, hiI⟩ := hne hCP.ne_top
  obtain ⟨i₀, hi₀, hi₀n, hi₀I⟩ := hnb hCP.ne_borel
  have hi := hI i hiI
  have hn3 : 3 ≤ n := by
    by_contra h
    exact hi₀I (show i₀ = i by omega ▸ hiI)
  exact ⟨n, f, σ, e', I, hn3, hf, hσs, hσk, hσ, hI, ⟨i, hiI⟩, ⟨i₀, hi₀, hi₀n, hi₀I⟩, hcomap⟩

section Element

variable {Y : Type} [Group Y] {L : Subgroup Y} {G : Type*} [Group G] {ρ : G →* ↥L}

theorem exists_eq_cover_mul_of_mem_sup (hρs : Function.Surjective ρ) {u : Y}
    (hu : u ∈ L ⊔ Subgroup.centralizer (L : Set Y)) :
    ∃ t : G, ∃ c ∈ Subgroup.centralizer (L : Set Y), u = (ρ t : Y) * c := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (le_normalizer_centralizer L)] at hu
  obtain ⟨l, hl, c, hc, rfl⟩ := hu
  obtain ⟨t, ht⟩ := hρs ⟨l, hl⟩
  exact ⟨t, c, hc, by rw [ht]⟩

theorem not_mem_center_of_eq_mul (hρs : Function.Surjective ρ) {u : Y} {t : G} {c : Y}
    (hc : c ∈ Subgroup.centralizer (L : Set Y)) (hu : u = (ρ t : Y) * c)
    (huC : u ∉ Subgroup.centralizer (L : Set Y)) : t ∉ Subgroup.center G := by
  intro ht
  refine huC (hu ▸ Subgroup.mul_mem _ (Subgroup.mem_centralizer_iff.mpr fun l hl => ?_) hc)
  obtain ⟨g, hg⟩ := hρs ⟨l, hl⟩
  have h := congrArg (fun x => ((ρ x : ↥L) : Y)) (Subgroup.mem_center_iff.mp ht g)
  simp only [map_mul, Subgroup.coe_mul, hg] at h
  exact h

theorem centralizer_le_comap_of_eq_mul {J : Subgroup Y} {u : Y} {t : G} {c : Y}
    (hc : c ∈ Subgroup.centralizer (L : Set Y)) (hu : u = (ρ t : Y) * c)
    (hfix : ∀ l ∈ L, u * l * u⁻¹ = l → l ∈ J) :
    Subgroup.centralizer ({t} : Set G) ≤ (J.subgroupOf L).comap ρ := by
  intro g hg
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
  refine hfix _ (ρ g).2 (mul_inv_eq_iff_eq_mul.mpr ?_)
  have h1 : (ρ t : Y) * ρ g = ρ g * ρ t := by
    have h := congrArg (fun x => ((ρ x : ↥L) : Y)) (Subgroup.mem_centralizer_iff.mp hg t rfl)
    simp only [map_mul, Subgroup.coe_mul] at h
    exact h
  have h2 : c * ρ g = ρ g * c := (Subgroup.mem_centralizer_iff.mp hc _ (ρ g).2).symm
  rw [hu, mul_assoc, h2, ← mul_assoc, h1, mul_assoc]

variable {n : ℕ} {K : Type} [Field K]

theorem pow_mem_center_of_eq_mul {ρ : Matrix.SpecialLinearGroup (Fin n) K →* ↥L}
    {e : ↥L ⧸ Subgroup.center ↥L ≃* projectiveSL n K}
    (hρ : ∀ g, e (QuotientGroup.mk (ρ g)) = proj n K g) {u : Y}
    {t : Matrix.SpecialLinearGroup (Fin n) K} {c : Y}
    (hc : c ∈ Subgroup.centralizer (L : Set Y)) (hu : u = (ρ t : Y) * c) {m : ℕ}
    (hum : u ^ m = 1) : t ^ m ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) := by
  have hcomm : Commute (ρ t : Y) c := Subgroup.mem_centralizer_iff.mp hc _ (ρ t).2
  have h1 : ((ρ (t ^ m) : ↥L) : Y) = (c ^ m)⁻¹ := by
    rw [hu, hcomm.mul_pow] at hum
    rw [map_pow, Subgroup.coe_pow]
    exact eq_inv_of_mul_eq_one_left hum
  have hZ : ρ (t ^ m) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro l
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, h1]
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.inv_mem _ (Subgroup.pow_mem _ hc m)) l l.2
  rw [← scalars_eq_center, ← proj_eq_one_iff, ← hρ, (QuotientGroup.eq_one_iff _).mpr hZ,
    map_one]

end Element

section Perfect

variable {Y : Type} [Group Y] {L J : Subgroup Y} {G : Type*} [Group G] {ρ : G →* ↥L}

theorem ker_subtype_comp_le (hker : ρ.ker ≤ Subgroup.center G) :
    (L.subtype.comp ρ).ker ≤ Subgroup.center G := fun _ hg =>
  hker (MonoidHom.mem_ker.mpr (Subtype.ext (MonoidHom.mem_ker.mp hg)))

theorem map_perfectJoin_comap_subgroupOf (hρs : Function.Surjective ρ)
    (hker : ρ.ker ≤ Subgroup.center G) (hJL : J ≤ L) :
    (perfectJoin ((J.subgroupOf L).comap ρ)).map (L.subtype.comp ρ) = perfectJoin J := by
  have hσr : J ≤ (L.subtype.comp ρ).range := fun j hj => by
    obtain ⟨g, hg⟩ := hρs ⟨j, hJL hj⟩
    exact ⟨g, by rw [MonoidHom.comp_apply, hg]; rfl⟩
  exact map_perfectJoin_comap_eq _ (ker_subtype_comp_le hker) hσr

theorem exists_eq_mul_of_mem_perfectJoin_sup (hρs : Function.Surjective ρ)
    (hker : ρ.ker ≤ Subgroup.center G) (hJL : J ≤ L) {u : Y}
    (hu : u ∈ perfectJoin J ⊔ Subgroup.centralizer (L : Set Y)) :
    ∃ t ∈ perfectJoin ((J.subgroupOf L).comap ρ),
      ∃ c ∈ Subgroup.centralizer (L : Set Y), u = (ρ t : Y) * c := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (((perfectJoin_le J).trans hJL).trans (le_normalizer_centralizer L))] at hu
  obtain ⟨j, hj, c, hc, rfl⟩ := hu
  rw [SetLike.mem_coe, ← map_perfectJoin_comap_subgroupOf hρs hker hJL] at hj
  obtain ⟨t, ht, rfl⟩ := hj
  exact ⟨t, ht, c, hc, rfl⟩

theorem isCyclic_of_cycPerfect_comap (hρs : Function.Surjective ρ)
    (hker : ρ.ker ≤ Subgroup.center G) (hJL : J ≤ L) {p : ℕ} (hcyc : CycPerfect p J)
    {Q : Subgroup G} (hQ : Q ≤ perfectJoin ((J.subgroupOf L).comap ρ)) (hQp : IsPGroup p Q)
    (hQZ : Q ⊓ Subgroup.center G = ⊥) : IsCyclic Q := by
  by_contra hnc
  have hQσ : Q.map (L.subtype.comp ρ) ≤ perfectJoin J := by
    rw [← map_perfectJoin_comap_subgroupOf hρs hker hJL]
    exact Subgroup.map_mono hQ
  exact not_isCyclic_map_of_inf_center_eq_bot _ (ker_subtype_comp_le hker) hQZ hnc
    (hcyc _ (perfectJoin_le J) (perfectJoin_perfect J) _ hQσ (hQp.map _))

end Perfect

structure NaturalSetup {Y : Type} [Group Y] (L J : Subgroup Y) (p : ℕ) (u : Y) (n f : ℕ)
    (ρ : Matrix.SpecialLinearGroup (Fin n) (GaloisField 2 f) →* ↥L)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* projectiveSL n (GaloisField 2 f)) (I : Set ℕ)
    (t : Matrix.SpecialLinearGroup (Fin n) (GaloisField 2 f)) : Prop where
  three_le : 3 ≤ n
  one_le : 1 ≤ f
  surj : Function.Surjective ρ
  ker_le : ρ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) (GaloisField 2 f))
  compat : ∀ g, e (QuotientGroup.mk (ρ g)) = proj n (GaloisField 2 f) g
  cuts : ∀ i ∈ I, 1 ≤ i ∧ i < n
  nonempty : I.Nonempty
  ne_borel : ∃ i, 1 ≤ i ∧ i < n ∧ i ∉ I
  comap : (J.subgroupOf L).comap ρ = flagStabilizer n (GaloisField 2 f) I
  eq_mul : ∃ c ∈ Subgroup.centralizer (L : Set Y), u = (ρ t : Y) * c
  pow_mem : t ^ p ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) (GaloisField 2 f))
  not_mem : t ∉ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) (GaloisField 2 f))
  centralizer_le : Subgroup.centralizer ({t} : Set (Matrix.SpecialLinearGroup (Fin n)
    (GaloisField 2 f))) ≤ flagStabilizer n (GaloisField 2 f) I
  cyc : ∀ Q : Subgroup (Matrix.SpecialLinearGroup (Fin n) (GaloisField 2 f)),
    Q ≤ perfectJoin (flagStabilizer n (GaloisField 2 f) I) → IsPGroup p Q →
    Q ⊓ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) (GaloisField 2 f)) = ⊥ → IsCyclic Q

theorem exists_naturalSetup
    (hGA : GriessAllModelsStatement) {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y}
    (hCP : CompParab L J) (hA : IsLieOf IdxA (↥L ⧸ Subgroup.center ↥L)) {p : ℕ}
    (hcyc : CycPerfect p J) {u : Y} (hu : u ∈ L ⊔ Subgroup.centralizer (L : Set Y))
    (hup : u ^ p = 1) (huC : u ∉ Subgroup.centralizer (L : Set Y))
    (hfix : ∀ l ∈ L, u * l * u⁻¹ = l → l ∈ J) :
    ∃ (n f : ℕ) (ρ : Matrix.SpecialLinearGroup (Fin n) (GaloisField 2 f) →* ↥L)
      (e : ↥L ⧸ Subgroup.center ↥L ≃* projectiveSL n (GaloisField 2 f)) (I : Set ℕ)
      (t : Matrix.SpecialLinearGroup (Fin n) (GaloisField 2 f)),
      NaturalSetup L J p u n f ρ e I t ∧
        (u ∈ perfectJoin J ⊔ Subgroup.centralizer (L : Set Y) →
          t ∈ perfectJoin (flagStabilizer n (GaloisField 2 f) I)) := by
  obtain ⟨n, f, ρ, e, I, hn, hf, hρs, hker, hρ, hI, hne, hnb, hcomap⟩ :=
    exists_cover_comap_eq_flagStabilizer hGA hCP hA
  have hJL : J ≤ L := hCP.parab.1
  obtain ⟨t, ht, c, hc, hut⟩ : ∃ t, (u ∈ perfectJoin J ⊔ Subgroup.centralizer (L : Set Y) →
      t ∈ perfectJoin (flagStabilizer n (GaloisField 2 f) I)) ∧
      ∃ c ∈ Subgroup.centralizer (L : Set Y), u = (ρ t : Y) * c := by
    by_cases hj : u ∈ perfectJoin J ⊔ Subgroup.centralizer (L : Set Y)
    · obtain ⟨t, ht, hc⟩ := exists_eq_mul_of_mem_perfectJoin_sup hρs hker hJL hj
      exact ⟨t, fun _ => hcomap ▸ ht, hc⟩
    · obtain ⟨t, hc⟩ := exists_eq_cover_mul_of_mem_sup hρs hu
      exact ⟨t, fun h => absurd h hj, hc⟩
  refine ⟨n, f, ρ, e, I, t, ⟨hn, hf, hρs, hker, hρ, hI, hne, hnb, hcomap, ⟨c, hc, hut⟩,
    pow_mem_center_of_eq_mul hρ hc hut hup, not_mem_center_of_eq_mul hρs hc hut huC,
    hcomap ▸ centralizer_le_comap_of_eq_mul hc hut hfix, fun Q hQ hQp hQZ =>
      isCyclic_of_cycPerfect_comap hρs hker hJL hcyc (hcomap ▸ hQ) hQp hQZ⟩, ht⟩

end ToralCensus

end CFSG.AGLEmbedding
