module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc.Glue
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinThreeSetup
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinPrimeBlocks
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusHubPrime

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding
open CFSG.AGLEmbedding.ParabPrime (perfectJoin perfectJoin_le perfectJoin_perfect le_perfectJoin)
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus
open scoped commutatorElement
open CFSG.AGLEmbedding.ToralCensus CFSG.LocalAnalysis.ComponentInitial LinearFlag

theorem exists_centCycBar' {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y}
    (h : CompParabE L J) {p : ℕ} (hp : p.Prime) {D : Subgroup Y} (hDp : ⁅D, D⁆ = D)
    (hDJ : D ≤ J ⊔ Subgroup.centralizer (L : Set Y))
    (hDcyc : ∀ A : Subgroup Y, A ≤ D → IsPGroup p A → IsCyclic A)
    (hDpart : ∀ V : Subgroup Y, V ≤ J → ⁅V, V⁆ = V → ∀ k : ℕ, p ^ k ∣ Nat.card V →
      p ^ k ∣ Nat.card D)
    {x : Y} (hxD : x ∈ D) (hxp : x ^ p = 1) (hxC : x ∉ Subgroup.centralizer (L : Set Y))
    (hxW : ∀ W : Subgroup Y, W ≤ L → ⁅W, W⁆ = W → W ≤ Subgroup.centralizer ({x} : Set Y) →
      W = ⊥) :
    ∃ ρ : ↥(J ⊔ Subgroup.centralizer (L : Set Y)) →* ↥L ⧸ Subgroup.center ↥L,
      (∀ g, ρ g = 1 ↔ (g : Y) ∈ Subgroup.centralizer (L : Set Y)) ∧
      (∀ g, ρ g ∈ jBar L J) ∧
      CentCycBar (jBar L J) p (ρ ⟨x, hDJ hxD⟩) ∧
      ⁅(D.subgroupOf (J ⊔ Subgroup.centralizer (L : Set Y))).map ρ,
        (D.subgroupOf (J ⊔ Subgroup.centralizer (L : Set Y))).map ρ⁆ =
        (D.subgroupOf (J ⊔ Subgroup.centralizer (L : Set Y))).map ρ ∧
      (D.subgroupOf (J ⊔ Subgroup.centralizer (L : Set Y))).map ρ ≤ jBar L J ∧
      ρ ⟨x, hDJ hxD⟩ ∈ (D.subgroupOf (J ⊔ Subgroup.centralizer (L : Set Y))).map ρ := by
  classical
  have hJL : J ≤ L := h.parab.1
  obtain ⟨ρ, hρmk, hρker⟩ := exists_leviHom (L := L) (J := J) hJL
  have hcomm : ∀ a ∈ J, ∀ b ∈ Subgroup.centralizer (L : Set Y), a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.1 hb a (hJL ha)
  have hρJ : ∀ g : ↥(J ⊔ Subgroup.centralizer (L : Set Y)), ρ g ∈ jBar L J := by
    intro g
    obtain ⟨a, ha, c, hc, hg⟩ := exists_mul_of_mem_sup_commute hcomm g.2
    have hg' : g = ⟨a * c, Subgroup.mul_mem_sup ha hc⟩ := Subtype.ext hg
    rw [hg', hρmk a ha c hc]
    exact ⟨⟨a, hJL ha⟩, Subgroup.mem_subgroupOf.2 ha, rfl⟩
  set D' : Subgroup ↥(J ⊔ Subgroup.centralizer (L : Set Y)) := D.subgroupOf (J ⊔ Subgroup.centralizer (L : Set Y)) with hD'
  set Dh : Subgroup (↥L ⧸ Subgroup.center ↥L) := D'.map ρ with hDh
  have hD'map : D'.map (J ⊔ Subgroup.centralizer (L : Set Y)).subtype = D := Subgroup.map_subgroupOf_eq_of_le hDJ
  have hD'perf : ⁅D', D'⁆ = D' := by
    apply Subgroup.map_injective (J ⊔ Subgroup.centralizer (L : Set Y)).subtype_injective
    rw [Subgroup.map_commutator, hD'map, hDp]
  have hDhperf : ⁅Dh, Dh⁆ = Dh := by
    rw [hDh, ← Subgroup.map_commutator, hD'perf]
  have hDhJ : Dh ≤ jBar L J := by
    rintro _ ⟨g, -, rfl⟩
    exact hρJ g
  have hcardD' : Nat.card D' = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDJ).toEquiv
  have hD'mem : ∀ g : ↥(J ⊔ Subgroup.centralizer (L : Set Y)), g ∈ D' ↔ (g : Y) ∈ D := fun g => Subgroup.mem_subgroupOf
  have hD'cyc : ∀ A : Subgroup ↥(J ⊔ Subgroup.centralizer (L : Set Y)), A ≤ D' → IsPGroup p A → IsCyclic A := by
    intro A hA hAp
    have hAm : A.map (J ⊔ Subgroup.centralizer (L : Set Y)).subtype ≤ D := by
      rintro _ ⟨a, ha, rfl⟩
      exact (hD'mem a).1 (hA ha)
    have : IsCyclic ↥(A.map (J ⊔ Subgroup.centralizer (L : Set Y)).subtype) := hDcyc _ hAm (hAp.map (J ⊔ Subgroup.centralizer (L : Set Y)).subtype)
    exact isCyclic_of_surjective
      (Subgroup.equivMapOfInjective A (J ⊔ Subgroup.centralizer (L : Set Y)).subtype (J ⊔ Subgroup.centralizer (L : Set Y)).subtype_injective).symm.toMonoidHom
      (MulEquiv.surjective _)
  have hD'cycG : ∀ A : Subgroup ↥D', IsPGroup p A → IsCyclic A := by
    intro A hAp
    have h1 : IsCyclic ↥(A.map D'.subtype) := hD'cyc _ (by
      rintro _ ⟨a, -, rfl⟩
      exact a.2) (hAp.map D'.subtype)
    exact isCyclic_of_surjective
      (Subgroup.equivMapOfInjective A D'.subtype D'.subtype_injective).symm.toMonoidHom
      (MulEquiv.surjective _)
  have hxM : x ∈ (J ⊔ Subgroup.centralizer (L : Set Y)) := hDJ hxD
  set xM : ↥(J ⊔ Subgroup.centralizer (L : Set Y)) := ⟨x, hxM⟩ with hxMdef
  have hxD' : xM ∈ D' := (hD'mem xM).2 hxD
  set x' : ↥D' := ⟨xM, hxD'⟩ with hx'def
  have hx'p : x' ^ p = 1 := Subtype.ext (Subtype.ext hxp)
  have hρx : ρ xM ≠ 1 := fun h1 => hxC ((hρker xM).1 h1)
  have hx'1 : x' ≠ 1 := fun h1 => hρx (by
    have : xM = 1 := congrArg (fun z : ↥D' => (z : ↥(J ⊔ Subgroup.centralizer (L : Set Y)))) h1
    rw [this, map_one])
  have hx'N : x' ∉ (ρ.subgroupMap D').ker := fun hk => hρx (by
    have := congrArg Subtype.val (MonoidHom.mem_ker.1 hk)
    exact this)
  have hNp : ¬ p ∣ Nat.card (ρ.subgroupMap D').ker :=
    normal_pPrime_of_cycSylow hp hD'cycG hx'p hx'1 hx'N
  have hDhdvd : ∀ k, p ^ k ∣ Nat.card D → p ^ k ∣ Nat.card Dh := by
    intro k hk
    have hsurj : Function.Surjective (ρ.subgroupMap D') := ρ.subgroupMap_surjective D'
    have hmul := Subgroup.card_ker_mul_card_of_surjective hsurj
    have hcop : Nat.Coprime (p ^ k) (Nat.card (ρ.subgroupMap D').ker) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hNp)
    rw [← hcardD', ← hmul] at hk
    exact hcop.dvd_of_dvd_mul_left hk
  have hDhcyc : ∀ A ≤ Dh, IsPGroup p A → IsCyclic A := by
    intro A hADh hAp
    have hPmap : (D' ⊓ A.comap ρ).map ρ = A := by
      refine le_antisymm ?_ ?_
      · rintro _ ⟨g, hg, rfl⟩
        exact hg.2
      · intro y hy
        obtain ⟨g, hg, rfl⟩ := hADh hy
        exact ⟨g, ⟨hg, hy⟩, rfl⟩
    obtain ⟨R, hRP, hRp, hRmap⟩ := exists_pSubgroup_map_eq hp hPmap hAp
    have hRcyc : IsCyclic R := hD'cyc R (fun r hr => (hRP hr).1) hRp
    subst hRmap
    have := hRcyc
    exact isCyclic_of_surjective (ρ.subgroupMap R) (ρ.subgroupMap_surjective R)
  set K : Subgroup (↥L ⧸ Subgroup.center ↥L) := perfectJoin (jBar L J) with hK
  have hDhK : Dh ≤ K := le_perfectJoin hDhJ hDhperf
  have hKdvd : ∀ k, p ^ k ∣ Nat.card K → p ^ k ∣ Nat.card Dh := by
    intro k hk
    obtain ⟨W, hWJ, hWp, hWmap⟩ := exists_perfect_lift_le h.parab (perfectJoin_perfect (jBar L J))
      (perfectJoin_le (jBar L J))
    have h1 : Nat.card K ∣ Nat.card (W.subgroupOf L) := by
      rw [hK, ← hWmap]
      exact Subgroup.card_dvd_of_surjective (MonoidHom.subgroupMap_surjective _ _)
    have h2 : Nat.card (W.subgroupOf L) = Nat.card W :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hWJ.trans hJL)).toEquiv
    exact hDhdvd k (hDpart W hWJ hWp k (by rw [← h2]; exact hk.trans h1))
  have hKcyc := cyc_of_sylow_dvd_le hp hDhK hDhcyc hKdvd
  obtain ⟨l, hl, c, hc, hxlc⟩ := exists_mul_of_mem_sup_commute hcomm hxM
  have hxM' : xM = ⟨l * c, Subgroup.mul_mem_sup hl hc⟩ := Subtype.ext hxlc
  have hvdef : ρ xM = (QuotientGroup.mk ⟨l, hJL hl⟩ : ↥L ⧸ Subgroup.center ↥L) := by
    rw [hxM', hρmk l hl c hc]
  have hvDh : ρ xM ∈ Dh := ⟨xM, hxD', rfl⟩
  obtain ⟨S₀, hS₀, hne, htop⟩ := exists_sylow_parab_central h
  refine ⟨ρ, hρker, hρJ, ⟨⟨S₀, hS₀, hne⟩, htop, ?_, ?_, hρx, hDhK hvDh, ?_⟩, hDhperf, hDhJ, hvDh⟩
  · intro V hVJ hV Q hQV hQp
    exact hKcyc Q (hQV.trans (le_perfectJoin hVJ hV)) hQp
  · rw [← map_pow]
    have : xM ^ p = 1 := Subtype.ext hxp
    rw [this, map_one]
  · intro V hVC hV
    rw [hvdef] at hVC
    exact perfect_cent_trivial_one (l := ⟨l, hJL hl⟩) (c := c) hc hxlc hxW hVC hV

section Top
variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem center_top_eq_bot (hZ : Subgroup.center X = ⊥) :
    Subgroup.center ↥(⊤ : Subgroup X) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have h1 : (z : X) ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := Subgroup.mem_center_iff.1 hz ⟨g, Subgroup.mem_top g⟩
    exact congrArg Subtype.val this
  rw [hZ, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  exact Subtype.ext h1

@[expose] noncomputable def topQuotEquiv (hZ : Subgroup.center X = ⊥) :
    ↥(⊤ : Subgroup X) ⧸ Subgroup.center ↥(⊤ : Subgroup X) ≃* X :=
  (QuotientGroup.quotientMulEquivOfEq (center_top_eq_bot hZ)).trans
    (QuotientGroup.quotientBot.trans Subgroup.topEquiv)

omit [Finite X] in
theorem isQuasisimple_top (hperf : commutator X = ⊤) (hsimple : IsSimpleGroup X)
    (hZ : Subgroup.center X = ⊥) : CFSG.Open.IsQuasisimple ↥(⊤ : Subgroup X) := by
  have : IsSimpleGroup (↥(⊤ : Subgroup X) ⧸ Subgroup.center ↥(⊤ : Subgroup X)) :=
    MulEquiv.isSimpleGroup (topQuotEquiv hZ)
  refine ⟨?_, this⟩
  have : Group.IsPerfect X := Group.isPerfect_def.mpr hperf
  have : Group.IsPerfect ↥(⊤ : Subgroup X) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.topEquiv (G := X)).symm.toMonoidHom)
      (MulEquiv.surjective _)
  exact Group.isPerfect_def.mp this

theorem centCycBar_compParab_top {J : Subgroup X} {p : ℕ} {v : X} (hA : IsLieOf IdxA X)
    (hperf : commutator X = ⊤) (hsimple : IsSimpleGroup X) (hZ : Subgroup.center X = ⊥)
    (h : CentCycBar J p v) : CompParab (⊤ : Subgroup X) J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀, hS₀, hne⟩ := h.parab
  refine ⟨⟨le_rfl, IsSubnormal.refl _, isQuasisimple_top hperf hsimple hZ⟩, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨d, hd, ⟨e⟩⟩ := hA
    refine Or.inl ⟨d, ?_, ⟨(topQuotEquiv hZ).trans e⟩⟩
    obtain ⟨d, hv⟩ := d
    cases d <;> simp_all [IdxA, IsClassicalOrG2Index]
  · rw [center_top_eq_bot hZ]
    simp
  · exact ⟨le_top, S₀, isSylowTwoOf_top_of_sylow' S₀, by simpa using hS₀⟩
  · exact fun hJ => h.ne_top (by simpa using hJ)
  · intro T hT hJT
    apply hne
    have hidx : ¬ 2 ∣ T.index := by
      have h2 := hT.2.2
      rwa [show (T.subgroupOf ⊤).index = T.index from Subgroup.relIndex_top_right T] at h2
    let T' : Sylow 2 X := hT.2.1.toSylow hidx
    have hNT : Subgroup.normalizer (T : Set X) = J := by
      rw [hJT]; ext y; simp
    have hle : Subgroup.normalizer ((S₀ : Subgroup X) : Set X) ≤
        Subgroup.normalizer ((T' : Subgroup X) : Set X) := by
      show _ ≤ Subgroup.normalizer (T : Set X)
      rw [hNT]; exact hS₀
    have hidx2 : (Subgroup.normalizer ((S₀ : Subgroup X) : Set X)).index =
        (Subgroup.normalizer ((T' : Subgroup X) : Set X)).index := by
      have e1 := Sylow.card_eq_index_normalizer S₀
      have e2 := Sylow.card_eq_index_normalizer T'
      exact e1.symm.trans e2
    have hc1 := Subgroup.card_mul_index (Subgroup.normalizer ((S₀ : Subgroup X) : Set X))
    have hc2 := Subgroup.card_mul_index (Subgroup.normalizer ((T' : Subgroup X) : Set X))
    have hpos : 0 < (Subgroup.normalizer ((S₀ : Subgroup X) : Set X)).index := by
      rw [Nat.pos_iff_ne_zero]; exact Subgroup.FiniteIndex.index_ne_zero
    have hcard : Nat.card (Subgroup.normalizer ((T' : Subgroup X) : Set X)) ≤
        Nat.card (Subgroup.normalizer ((S₀ : Subgroup X) : Set X)) := by
      rw [hidx2] at hc1
      exact Nat.le_of_mul_le_mul_right (by rw [hc1, hc2]) (hidx2 ▸ hpos)
    have heq := Subgroup.eq_of_le_of_card_ge hle hcard
    rw [← hNT]
    exact heq.symm

end Top


section Flag
variable {X : Type} [Group X] [Finite X]

theorem centCycBar_flag {n f : ℕ} (hn : 1 ≤ n) (hZ : Subgroup.center X = ⊥)
    (e : X ≃* projectiveSL n (GaloisField 2 f)) {J : Subgroup X} {p : ℕ} {v : X}
    (hCP : CompParab (⊤ : Subgroup X) J) (h : CentCycBar J p v) :
    ∃ (σ : Matrix.SpecialLinearGroup (Fin n) (GaloisField 2 f) →* X) (I : Set ℕ),
      3 ≤ n ∧ Function.Surjective σ ∧
      σ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) (GaloisField 2 f)) ∧
      (∀ i ∈ I, 1 ≤ i ∧ i < n) ∧ I.Nonempty ∧ (∃ i, 1 ≤ i ∧ i < n ∧ i ∉ I) ∧
      J.comap σ = flagStabilizer n (GaloisField 2 f) I ∧
      CycFlagPerfect n (GaloisField 2 f) I p ∧
      ∃ t ∈ perfectJoin (flagStabilizer n (GaloisField 2 f) I), σ t = v ∧
        t ^ p ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) (GaloisField 2 f)) ∧
        t ∉ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) (GaloisField 2 f)) := by
  let eT : ↥(⊤ : Subgroup X) ⧸ Subgroup.center ↥(⊤ : Subgroup X) ≃*
      projectiveSL n (GaloisField 2 f) := (topQuotEquiv hZ).trans e
  obtain ⟨ρ, hρ⟩ := exists_compat_of_center_eq_bot (center_top_eq_bot hZ) eT
  obtain ⟨hρs, -⟩ := surjective_and_ker_le_of_compat hCP.comp.2.2.1 eT ρ hρ
  obtain ⟨σ, e', I, hσs, hσ, hI, hcomap, hne, hnb⟩ :=
    exists_comap_eq_flagStabilizer hCP.odd hn eT hρs hρ hCP.parab
  obtain ⟨-, hσk⟩ := surjective_and_ker_le_of_compat hCP.comp.2.2.1 e' σ hσ
  obtain ⟨i, hiI⟩ := hne hCP.ne_top
  obtain ⟨i₀, hi₀, hi₀n, hi₀I⟩ := hnb hCP.ne_borel
  have hi := hI i hiI
  have hn3 : 3 ≤ n := by
    by_contra hh
    exact hi₀I (show i₀ = i by omega ▸ hiI)
  have hJL : J ≤ (⊤ : Subgroup X) := le_top
  have hker' : (((⊤ : Subgroup X).subtype.comp σ).ker) ≤
      Subgroup.center (Matrix.SpecialLinearGroup (Fin n) (GaloisField 2 f)) := fun g hg =>
    hσk (MonoidHom.mem_ker.mpr (Subtype.ext (MonoidHom.mem_ker.mp hg)))
  have hcomap' : J.comap ((⊤ : Subgroup X).subtype.comp σ) =
      flagStabilizer n (GaloisField 2 f) I := by
    rw [← hcomap]
    ext g
    simp [Subgroup.mem_subgroupOf]
  refine ⟨(⊤ : Subgroup X).subtype.comp σ, I, hn3, ?_, hker', hI, ⟨i, hiI⟩,
    ⟨i₀, hi₀, hi₀n, hi₀I⟩, hcomap', ?_, ?_⟩
  · intro x
    obtain ⟨s, hs⟩ := hσs ⟨x, Subgroup.mem_top x⟩
    exact ⟨s, by simp [hs]⟩
  · intro Q hQ hQp hQZ
    exact isCyclic_of_cycPerfect_comap hσs hσk hJL h.cyc (hcomap ▸ hQ) hQp hQZ
  · have hm := map_perfectJoin_comap_subgroupOf hσs hσk hJL
    have hv : v ∈ (perfectJoin ((J.subgroupOf (⊤ : Subgroup X)).comap σ)).map
        ((⊤ : Subgroup X).subtype.comp σ) := hm ▸ h.join
    obtain ⟨t, ht, hv'⟩ := hv
    refine ⟨t, hcomap ▸ ht, hv', hker' ?_, fun htc => h.ne_one ?_⟩
    · rw [MonoidHom.mem_ker, map_pow, hv', h.pow]
    · rw [← hv']
      have hc : ((⊤ : Subgroup X).subtype.comp σ) t ∈ Subgroup.center X := by
        rw [Subgroup.mem_center_iff]
        intro x
        obtain ⟨s, hs⟩ := (show Function.Surjective ((⊤ : Subgroup X).subtype.comp σ) from
          fun x => by
            obtain ⟨s, hs⟩ := hσs ⟨x, Subgroup.mem_top x⟩
            exact ⟨s, by simp [hs]⟩) x
        rw [← hs, ← map_mul, ← map_mul, Subgroup.mem_center_iff.1 htc s]
      rw [hZ] at hc
      exact hc
end Flag

section Torus
open TauCeti
theorem exists_equiv_of_isLieOfTorus {X : Type} [Group X] {p : ℕ} (hX : IsLieOfTorus IdxA p X) :
    ∃ n f : ℕ, 2 ≤ n ∧ 1 ≤ f ∧ Nonempty (X ≃* projectiveSL n (GaloisField 2 f)) ∧
      4 ≤ Nat.card (GaloisField 2 f) ∧ p ∣ Nat.card (GaloisField 2 f) - 1 := by
  obtain ⟨⟨d, hv⟩, hd, hnt, ⟨e⟩⟩ := hX
  cases d with
  | A r q =>
    change q.p = 2 at hd
    have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    obtain ⟨p', k, hp', hk⟩ := q
    change p' = 2 at hd
    subst hd
    have : Fact (Nat.Prime 2) := ⟨hp'⟩
    have hcard : Nat.card (GaloisField 2 k) = 2 ^ k := GaloisField.card 2 k (by omega)
    have hnt' : ¬ (2 ^ k = 2 ∨ ¬ p ∣ 2 ^ k - 1) := by
      simpa [IndexTorusFree, PrimePower.card_def] using hnt
    refine ⟨r + 1, k, by omega, hk, ⟨(e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL
      r ⟨2, k, hp', hk⟩ hv)).trans (LinearCover.projectiveSpecialLinearEquivProjectiveSL _ _)⟩,
      ?_, ?_⟩
    · rw [hcard]
      have h2 : 2 ^ k ≠ 2 := fun h => hnt' (Or.inl h)
      have hk2 : 2 ≤ k := by
        by_contra hlt
        exact h2 (by interval_cases k; rfl)
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
    · rw [hcard]
      by_contra hnd
      exact hnt' (Or.inr hnd)
  | _ => exact hd.elim
end Torus

section Props
open scoped commutatorElement

@[expose] def TorusFourCell : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ) (I : Set ℕ) (p : ℕ), 4 ≤ n →
    p.Prime → 5 ≤ p → 4 ≤ Nat.card K → p ∣ Nat.card K - 1 → (∀ i ∈ I, 1 ≤ i ∧ i < n) →
    I.Nonempty → (∃ i, 1 ≤ i ∧ i < n ∧ i ∉ I) → CycFlagPerfect n K I p →
    ∀ t : Matrix.SpecialLinearGroup (Fin n) K, t ∈ perfectJoin (flagStabilizer n K I) →
      t ^ p ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) →
      t ∉ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) →
      ∃ W : Subgroup (Matrix.SpecialLinearGroup (Fin n) K),
        W ≤ Subgroup.centralizer ({t} : Set (Matrix.SpecialLinearGroup (Fin n) K)) ∧
        ⁅W, W⁆ = W ∧ W ≠ ⊥ ∧ W ⊓ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) = ⊥

@[expose] def TorusThreeCell : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (I : Set ℕ) (p : ℕ),
    p.Prime → 5 ≤ p → 4 ≤ Nat.card K → p ∣ Nat.card K - 1 → (∀ i ∈ I, 1 ≤ i ∧ i < 3) →
    I.Nonempty → (∃ i, 1 ≤ i ∧ i < 3 ∧ i ∉ I) →
    ∀ E D : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K),
      E ≤ flagStabilizer 3 K I → D ≤ flagStabilizer 3 K I → IsPGroup p E → ⁅D, D⁆ = D →
      p ∣ Nat.card D → (∀ e ∈ E, ∀ d ∈ D, e * d = d * e) → IsCyclic E

end Props

section Three
open scoped commutatorElement
variable {X : Type} [Group X] [Finite X]

theorem false_of_sl_centralizer {G : Type*} [Group G] {J : Subgroup X} {p : ℕ} {v : X}
    (h : CentCycBar J p v) (σ : G →* X) (hker : σ.ker ≤ Subgroup.center G) {t : G}
    (htv : σ t = v) {W : Subgroup G}
    (hW : W ≤ Subgroup.centralizer ({t} : Set G)) (hWp : ⁅W, W⁆ = W) (hW0 : W ≠ ⊥)
    (hWZ : W ⊓ Subgroup.center G = ⊥) : False := by
  have hV := h.triv (W.map σ) ?_ (by rw [← Subgroup.map_commutator, hWp])
  · apply hW0
    rw [eq_bot_iff]
    intro w hw
    have h1 : σ w ∈ (⊥ : Subgroup X) := hV ▸ Subgroup.mem_map_of_mem σ hw
    rw [Subgroup.mem_bot] at h1
    have h2 : w ∈ W ⊓ Subgroup.center G := ⟨hw, hker (MonoidHom.mem_ker.mpr h1)⟩
    rw [hWZ] at h2
    exact h2
  · rintro _ ⟨w, hw, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    rw [Set.mem_singleton_iff] at hk
    subst hk
    have := Subgroup.mem_centralizer_iff.1 (hW hw) t (Set.mem_singleton t)
    rw [← htv, ← map_mul, ← map_mul, this]

end Three

section Three2
open scoped commutatorElement
variable {X : Type} [Group X] [Finite X]

theorem centCycBar_torus_three (hFour : TorusFourCell) (hperf : commutator X = ⊤)
    (hsimple : IsSimpleGroup X) (hZ : Subgroup.center X = ⊥) {J : Subgroup X} {p : ℕ} {v : X}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hT : IsLieOfTorus IdxA p X) (h : CentCycBar J p v) :
    ∃ f : ℕ, Nonempty (X ≃* projectiveSL 3 (GaloisField 2 f)) ∧
      ∃ (σ : Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 f) →* X) (I : Set ℕ),
        4 ≤ Nat.card (GaloisField 2 f) ∧ p ∣ Nat.card (GaloisField 2 f) - 1 ∧
        Function.Surjective σ ∧
        σ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 f)) ∧
        (∀ i ∈ I, 1 ≤ i ∧ i < 3) ∧ I.Nonempty ∧ (∃ i, 1 ≤ i ∧ i < 3 ∧ i ∉ I) ∧
        J.comap σ = flagStabilizer 3 (GaloisField 2 f) I := by
  obtain ⟨n, f, hn2, hf, ⟨e⟩, hK4, hpK⟩ := exists_equiv_of_isLieOfTorus hT
  have hA : IsLieOf IdxA X := by
    obtain ⟨d, hd, -, he⟩ := hT
    exact ⟨d, hd, he⟩
  have hCP := centCycBar_compParab_top hA hperf hsimple hZ h
  obtain ⟨σ, I, hn3, hσs, hσk, hI, hne, hnb, hcomap, hcyc, t, ht, htv, htp, htc⟩ :=
    centCycBar_flag (by omega) hZ e hCP h
  by_cases hn4 : 4 ≤ n
  · obtain ⟨W, hWc, hWp, hW0, hWZ⟩ := hFour (GaloisField 2 f) n I p hn4 hp hp5 hK4 hpK hI hne hnb
      hcyc t ht htp htc
    exact (false_of_sl_centralizer h σ hσk htv hWc hWp hW0 hWZ).elim
  · obtain rfl : n = 3 := by omega
    exact ⟨f, ⟨e⟩, σ, I, hK4, hpK, hσs, hσk, hI, hne, hnb, hcomap⟩

end Three2

section Three3
open scoped commutatorElement
variable {X : Type} [Group X] [Finite X]

theorem isCyclic_of_centCycBar_torus_three (hFour : TorusFourCell) (hThree : TorusThreeCell)
    (hperf : commutator X = ⊤) (hsimple : IsSimpleGroup X) (hZ : Subgroup.center X = ⊥)
    {J : Subgroup X} {p : ℕ} {v : X} (hp : p.Prime) (hp5 : 5 ≤ p) (hT : IsLieOfTorus IdxA p X)
    (h : CentCycBar J p v) {Dh : Subgroup X} (hDp : ⁅Dh, Dh⁆ = Dh) (hDJ : Dh ≤ J) (hvD : v ∈ Dh)
    {A : Subgroup X} (hAJ : A ≤ J) (hAp : IsPGroup p A)
    (hAD : A ≤ Subgroup.centralizer (Dh : Set X)) : IsCyclic A := by
  obtain ⟨f, -, σ, I, hK4, hpK, hσs, hσk, hI, hne, hnb, hcomap⟩ :=
    centCycBar_torus_three hFour hperf hsimple hZ hp hp5 hT h
  obtain ⟨D', hD'p, hD'le, hD'map⟩ := CFSG.AGLEmbedding.ParabPrime.exists_perfect_map_eq σ hσk hDp
    (by rw [MonoidHom.range_eq_top.2 hσs]; exact le_top)
  obtain ⟨E', hE'le, hE'p, hE'map⟩ := exists_pSubgroup_map_eq (ψ := σ) hp
    (P := A.comap σ) (Subgroup.map_comap_eq_self_of_surjective hσs A) hAp
  have hD'Q : D' ≤ flagStabilizer 3 (GaloisField 2 f) I := by
    rw [← hcomap]
    exact fun x hx => hDJ (hD'le hx)
  have hE'Q : E' ≤ flagStabilizer 3 (GaloisField 2 f) I := by
    rw [← hcomap]
    exact fun x hx => hAJ (hE'le hx)
  have hcomm : ∀ e ∈ E', ∀ d ∈ D', e * d = d * e := by
    intro e he
    have hcen : ∀ d ∈ D', ⁅d, e⁆ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 f)) := by
      intro d hd
      apply hσk
      rw [MonoidHom.mem_ker, map_commutatorElement]
      have h1 : σ e ∈ A := hE'map ▸ Subgroup.mem_map_of_mem σ he
      have h2 : σ d ∈ Dh := hD'map ▸ Subgroup.mem_map_of_mem σ hd
      have := Subgroup.mem_centralizer_iff.1 (hAD h1) (σ d) h2
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact this
    have hle : ⁅D', D'⁆ ≤ Subgroup.centralizer ({e} : Set (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 f))) := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      rw [Set.mem_singleton_iff] at hk
      subst hk
      have := commutator_commutator_eq_one_of_central (hcen a ha) (hcen b hb)
      rw [commutatorElement_eq_one_iff_mul_comm] at this
      exact this.symm
    intro d hd
    have hd' : d ∈ ⁅D', D'⁆ := by rw [hD'p]; exact hd
    have := Subgroup.mem_centralizer_iff.1 (hle hd') e (Set.mem_singleton e)
    exact this
  have hdvd : p ∣ Nat.card D' := by
    obtain ⟨d, hd, hdv⟩ : v ∈ D'.map σ := hD'map ▸ hvD
    have : Fact p.Prime := ⟨hp⟩
    have h1 : orderOf v = p := orderOf_eq_prime h.pow h.ne_one
    have h2 : orderOf v ∣ orderOf d := hdv ▸ orderOf_map_dvd σ d
    have h3 : orderOf d ∣ Nat.card D' := by
      have := orderOf_dvd_natCard (⟨d, hd⟩ : D')
      rwa [Subgroup.orderOf_mk] at this
    exact h1 ▸ h2.trans h3
  have hEc := hThree (GaloisField 2 f) I p hp hp5 hK4 hpK hI hne hnb E' D' hE'Q hD'Q hE'p hD'p hdvd hcomm
  rw [← hE'map]
  exact isCyclic_of_surjective (σ.subgroupMap E') (σ.subgroupMap_surjective E')
end Three3

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc
