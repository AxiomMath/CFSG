module

public import CFSG.HardMathSupport.Solomon.LocalBalance.InnDiagThree
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma24
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.GroupTheory.HyperplaneGeneration
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

namespace Lemma54Ns

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

variable {G : Type*} [Group G]

@[expose] def gammaPrimeIn [Finite G] (p k : ℕ) (B X : Subgroup G) : Subgroup G :=
  ⨆ (E : Subgroup G) (_ : E ≤ B ∧ k ≤ CFSG.Open.pRank p E), X ⊓ Subgroup.centralizer (E : Set G)

@[expose] def IsInGMinusOne [Finite G] (p : ℕ) (B L : Subgroup G) : Prop :=
  bClosure B L = gammaPrimeIn p (CFSG.Open.pRank p B - 1) B (bClosure B L)

export CFSG.HardMathSupport.Solomon.LocalBalance (IsConjByGL IsInnDiagPSL3 IsInnDiagPSU3
  IsInnDiagThree IsThreeType)

theorem IsThreeType.of_isFieldAutThree {Y : Type*} [Group Y] {α : MulAut Y}
    (h : IsFieldAutThree α) (h1 : α ≠ 1) : IsThreeType Y := by
  rcases h with h | ⟨K, hK, hf, θ, σ, φ, γ, -, -⟩ | ⟨K, hK, hf, q, θ, σ, φ, γ, hq, -, -, -⟩
  · exact absurd h h1
  · exact Or.inl ⟨K, hK, hf, ⟨θ⟩⟩
  · exact Or.inr ⟨K, hK, hf, q, hq, ⟨θ⟩⟩

@[expose] def fixedSubgroup {K B : Type*} [Group K] [Group B] (ρ : B →* MulAut K)
    (E : Subgroup B) : Subgroup K where
  carrier := {k | ∀ e ∈ E, ρ e k = k}
  one_mem' := fun e _ => map_one (ρ e)
  mul_mem' := fun {a b} ha hb e he => by rw [map_mul, ha e he, hb e he]
  inv_mem' := fun {a} ha e he => by rw [map_inv, ha e he]

@[expose] def Input23_16 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → IsThreeType K →
    ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (B : Type) [Group B] [Finite B] (ρ : B →* MulAut K),
      IsElemAbelian p (⊤ : Subgroup B) →
      (∃ H : Subgroup B, Nat.card B = p * Nat.card H ∧ ∀ h ∈ H, IsFieldAutThree (ρ h)) →
      (⊤ : Subgroup K) ≤ ⨆ (E : Subgroup B)
        (_ : CFSG.Open.pRank p (⊤ : Subgroup B) - 1 ≤ CFSG.Open.pRank p E), fixedSubgroup ρ E

@[expose] def Input23_16At3 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → IsThreeType K →
    ∀ (B : Type) [Group B] [Finite B] (ρ : B →* MulAut K),
      IsElemAbelian 3 (⊤ : Subgroup B) →
      (∃ H : Subgroup B, Nat.card B = 3 * Nat.card H ∧ ∀ h ∈ H, IsFieldAutThree (ρ h)) →
      (⊤ : Subgroup K) ≤ ⨆ (E : Subgroup B)
        (_ : CFSG.Open.pRank 3 (⊤ : Subgroup B) - 1 ≤ CFSG.Open.pRank 3 E), fixedSubgroup ρ E

@[expose] def Input22_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X B L : Subgroup G),
    B ≤ X → IsElemAbelian 3 B → GLAPComponent 3 X L →
    1 ≤ CFSG.Open.pRank 3 (B ⊓ Subgroup.normalizer (L : Set G)) →
    L ≤ gammaPrimeIn 3 (CFSG.Open.pRank 3 (B ⊓ Subgroup.normalizer (L : Set G)) - 1)
      (B ⊓ Subgroup.normalizer (L : Set G)) L →
    IsInGMinusOne 3 B L

@[expose] def Input19_1_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Open.IsKProper G → ∀ p : ℕ, p.Prime → ∀ D : Subgroup G, IsElemAbelian p D → D ≠ ⊥ →
      ∀ b ∈ Subgroup.centralizer (D : Set G), b ≠ 1 → b ^ p = 1 →
        (∀ L : Subgroup G, GLAPComponent p (Subgroup.centralizer ({b} : Set G)) L →
          GLADelta p D ⊓ Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (L : Set G)) ∧
        ∀ L : Subgroup G, GLAPComponent p (Subgroup.centralizer ({b} : Set G)) L →
          ¬ ⁅L, GLADelta p D ⊓ Subgroup.centralizer ({b} : Set G)⁆ ≤
              GLAPPrimeCoreOf p (Subgroup.centralizer ({b} : Set G)) →
            kerB p D L = ⊥ ∧ D ≤ Subgroup.normalizer (L : Set G) ∧
              ((((GLADelta p D ⊓ Subgroup.centralizer ({b} : Set G)).subgroupOf
                    (Subgroup.normalizer (L : Set G))).map (barAut p L)) ≤
                localDeltaIn p
                  ((((GLADelta p D ⊓ Subgroup.centralizer ({b} : Set G)) ⊔ L).subgroupOf
                    (Subgroup.normalizer (L : Set G))).map (barAut p L))
                  ((D.subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut p L)))

@[expose] def Input19_7_3d : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → IsThreeType K →
    ∀ D H : Subgroup (MulAut K), IsEkIn 3 2 ⊤ D → innerAut K ≤ H →
      D ≤ Subgroup.normalizer (H : Set (MulAut K)) → localDeltaIn 3 H D ≠ ⊥ →
        ∀ α ∈ D, IsInnDiagThree α

@[expose] def Input7_FieldInnDiag : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → ∀ α : MulAut K,
    IsFieldAutThree α → IsInnDiagThree α → α = 1

theorem isElemAbelian_of_le' {p : ℕ} {A B : Subgroup G} (hB : IsElemAbelian p B) (h : A ≤ B) :
    IsElemAbelian p A := CFSG.Open.IsElemAbelian.mono hB h

theorem exists_card_eq_pow [Finite G] {p : ℕ} (hp : p.Prime) {A : Subgroup G}
    (hA : IsElemAbelian p A) : ∃ k, Nat.card A = p ^ k := by
  have : Fact p.Prime := ⟨hp⟩
  have hpg : IsPGroup p A := fun x => ⟨1, by
    apply Subtype.ext
    simpa using hA.2 x x.2⟩
  exact IsPGroup.iff_card.1 hpg

theorem exists_mem_inf_ne_one [Finite G] {A D B : Subgroup G} (hAB : A ≤ B) (hDB : D ≤ B)
    (hcard : Nat.card B < Nat.card A * Nat.card D) : ∃ a ∈ A ⊓ D, a ≠ 1 := by
  by_contra hno
  simp only [not_exists, not_and, not_not] at hno
  let f : A × D → B := fun x => ⟨(x.1 : G) * x.2, B.mul_mem (hAB x.1.2) (hDB x.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ ⟨⟨x', hx'⟩, ⟨y', hy'⟩⟩ h
    have h1 : x * y = x' * y' := congrArg Subtype.val h
    have h2 : x'⁻¹ * x = y' * y⁻¹ := by
      calc x'⁻¹ * x = x'⁻¹ * (x * y) * y⁻¹ := by group
        _ = x'⁻¹ * (x' * y') * y⁻¹ := by rw [h1]
        _ = y' * y⁻¹ := by group
    have h3 : x'⁻¹ * x ∈ A ⊓ D :=
      ⟨A.mul_mem (A.inv_mem hx') hx, h2 ▸ D.mul_mem hy' (D.inv_mem hy)⟩
    have h4 : x'⁻¹ * x = 1 := hno _ h3
    have h5 : x = x' := (inv_mul_eq_one.1 h4).symm
    subst h5
    have h6 : y = y' := mul_left_cancel h1
    subst h6
    rfl
  have := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod] at this
  omega

theorem exists_hyperplane [Finite G] {A N B : Subgroup G} (hBel : IsElemAbelian 3 B)
    (hBcard : Nat.card B = 3 ^ 4) (hNB : N ≤ B) (hAN : A ≤ N) {k : ℕ} (hk : Nat.card A = 3 ^ k)
    (hk3 : 3 ≤ k) : ∃ H : Subgroup G, H ≤ A ∧ Nat.card N = 3 * Nat.card H := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨j, hj⟩ := exists_card_eq_pow Nat.prime_three (isElemAbelian_of_le' hBel hNB)
  have hkj : k ≤ j := by
    have hd : 3 ^ k ∣ 3 ^ j := hk ▸ hj ▸ Subgroup.card_dvd_of_le hAN
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hd
  have hj4 : j ≤ 4 := by
    have hd : 3 ^ j ∣ 3 ^ 4 := hBcard ▸ hj ▸ Subgroup.card_dvd_of_le hNB
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hd
  have hdvd : 3 ^ (j - 1) ∣ Nat.card A := by
    rw [hk]; exact pow_dvd_pow 3 (by omega)
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3 hdvd
  refine ⟨K.map A.subtype, Subgroup.map_subtype_le K, ?_⟩
  rw [Subgroup.card_map_of_injective A.subtype_injective, hK, hj]
  have : j = (j - 1) + 1 := by omega
  conv_lhs => rw [this]
  rw [pow_succ]; ring

theorem isInGOne_of_isInGMinusOne [Finite G] {B L : Subgroup G}
    (hB : CFSG.Open.pRank 3 B = 4) (h : IsInGMinusOne 3 B L) : IsInGOne 3 B L := by
  unfold IsInGOne coreIn
  apply le_antisymm
  · rw [IsInGMinusOne, hB] at h
    refine h.le.trans ?_
    unfold gammaPrimeIn
    refine iSup_le fun E => iSup_le fun hE => ?_
    exact le_iSup₂_of_le E ⟨hE.1, by simpa using hE.2⟩
      (inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _))
  · exact iSup₂_le fun Q _ => inf_le_left

theorem barX_ne_bot_of_comp [Finite G] {p : ℕ} {X L : Subgroup G} (hL : GLAPComponent p X L) :
    barX p X L ≠ ⊥ := by
  intro hbot
  have h3 := hL.2.2.1
  change IsComponentOf (barX p X L) ⊤ at h3
  rw [hbot] at h3
  obtain ⟨-, hsimple⟩ := h3.2.2
  have := hsimple.toNontrivial
  have hss : Subsingleton (↥(⊥ : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)) ⧸
      Subgroup.center ↥(⊥ : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X))) := inferInstance
  exact (not_subsingleton_iff_nontrivial.2 inferInstance) hss

theorem not_slob_of_le_lambdaOf [Finite G] {B : Subgroup G} {b : G} {L : Subgroup G}
    (hL : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L) (hle : L ≤ lambdaOf 3 B b) :
    ¬ IsStronglyLocallyOneBalanced 3 B b L := by
  intro hslob
  set X := Subgroup.centralizer ({b} : Set G) with hX
  have hcen : ∀ L' : Subgroup G, GLAPComponent 3 X L' → ¬ IsStronglyLocallyOneBalanced 3 B b L' →
      barX 3 X L' ≤ Subgroup.centralizer (barX 3 X L : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := by
    intro L' hL' hnslob
    have hne : L ≠ L' := fun h => hnslob (h ▸ hslob)
    have hbar : barX 3 X L ≠ barX 3 X L' := fun h => hne (glaPComponent_uniqueAux hL hL' h)
    have hcomm : ⁅barX 3 X L, barX 3 X L'⁆ = ⊥ :=
      CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hL.2.2.1 hL'.2.2.1 hbar
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 (by rw [Subgroup.commutator_comm]; exact hcomm)
  set P : Subgroup G := ((Subgroup.centralizer
    (barX 3 X L : Set (↥X ⧸ GLAPPrimeCore 3 ↥X))).comap
      (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X))).map X.subtype with hP
  have hSP : lambdaOf 3 B b ≤ P := by
    refine sSup_le fun L' hL' => ?_
    intro y hy
    have hyX : y ∈ X := hL'.1.1 hy
    refine ⟨⟨y, hyX⟩, ?_, rfl⟩
    exact hcen L' hL'.1 hL'.2 ⟨⟨y, hyX⟩, (Subgroup.mem_subgroupOf).2 hy, rfl⟩
  have hbarle : barX 3 X L ≤ Subgroup.centralizer (barX 3 X L : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := by
    rintro _ ⟨c, hc, rfl⟩
    obtain ⟨y, hy, hyc⟩ := hSP (hle ((Subgroup.mem_subgroupOf).1 hc))
    have hyc' : y = c := Subtype.ext hyc
    subst hyc'
    exact hy
  have hperf : ⁅barX 3 X L, barX 3 X L⁆ = barX 3 X L :=
    Subgroup.isPerfect_iff.1 ⟨hL.2.2.1.2.2.1⟩
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer.2 hbarle] at hperf
  exact barX_ne_bot_of_comp hL hperf.symm

theorem conj_mem_gLAPPrimeCoreOf' {p : ℕ} {J : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (J : Set G)) {y : G} (hy : y ∈ GLAPPrimeCoreOf p J) :
    g * y * g⁻¹ ∈ GLAPPrimeCoreOf p J := by
  obtain ⟨y', hy', rfl⟩ := hy
  refine ⟨J.normalizerMonoidHom ⟨g, hg⟩ y',
    map_gLAPPrimeCore_le p (J.normalizerMonoidHom ⟨g, hg⟩) ⟨y', hy', rfl⟩, ?_⟩
  rfl

theorem mem_centralizerQuot_iff_barAut' (p : ℕ) {J : Subgroup G}
    (g : ↥(Subgroup.normalizer (J : Set G))) :
    (g : G) ∈ centralizerQuot J (GLAPPrimeCoreOf p J) ↔ barAut p J g = 1 := by
  have hs : ∀ y : ↥J, ((J.normalizerMonoidHom g y : ↥J) : G) = g * y * (g : G)⁻¹ := fun _ => rfl
  constructor
  · rintro ⟨-, -, hc⟩
    ext z
    induction z using QuotientGroup.induction_on with | H y => ?_
    rw [barAut_mk, MulAut.one_apply, eq_comm, QuotientGroup.eq]
    have := hc (y : G)⁻¹ (J.inv_mem y.2)
    refine (Subgroup.mem_map_iff_mem J.subtype_injective).1
      (?_ : J.subtype _ ∈ GLAPPrimeCoreOf p J)
    simpa [mul_assoc, hs] using this
  · intro h
    refine ⟨g.2, ?_, fun x hx => ?_⟩
    · rw [Subgroup.mem_normalizer_iff]
      intro y
      refine ⟨fun hy => conj_mem_gLAPPrimeCoreOf' g.2 hy, fun hy => ?_⟩
      have := conj_mem_gLAPPrimeCoreOf' (inv_mem g.2) hy
      simpa [mul_assoc] using this
    · have h1 := congrArg (fun φ => φ (QuotientGroup.mk (⟨x, hx⟩⁻¹ : ↥J))) h
      simp only [barAut_mk, MulAut.one_apply] at h1
      rw [eq_comm, QuotientGroup.eq] at h1
      have h2 : J.subtype _ ∈ GLAPPrimeCoreOf p J := Subgroup.mem_map_of_mem J.subtype h1
      simpa [mul_assoc, hs] using h2

theorem card_map_barAut_of_kerB_eq_bot [Finite G] {p : ℕ} {D L : Subgroup G}
    (hDN : D ≤ Subgroup.normalizer (L : Set G)) (hker : kerB p D L = ⊥) :
    Nat.card ((D.subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut p L)) = Nat.card D := by
  have hinj : Function.Injective
      ((barAut p L).domRestrict (D.subgroupOf (Subgroup.normalizer (L : Set G)))) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, hx⟩ h
    have h1 : barAut p L x = 1 := h
    have hxD : (x : G) ∈ D := Subgroup.mem_subgroupOf.1 hx
    have hmem : (x : G) ∈ kerB p D L := ⟨hxD, (mem_centralizerQuot_iff_barAut' p x).2 h1⟩
    rw [hker] at hmem
    exact Subtype.ext (Subtype.ext (Subgroup.mem_bot.1 hmem))
  rw [← MonoidHom.domRestrict_range]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm.trans
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDN).toEquiv)

theorem map_barAut_ne_bot {p : ℕ} {L X : Subgroup G} (hXN : X ≤ Subgroup.normalizer (L : Set G))
    (hnot : ¬ ⁅L, X⁆ ≤ GLAPPrimeCoreOf p L) :
    (X.subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut p L) ≠ ⊥ := by
  intro hbot
  apply hnot
  refine Subgroup.commutator_le.2 fun ℓ hℓ x hx => ?_
  have h1 : barAut p L ⟨x, hXN hx⟩ = 1 := by
    have : barAut p L ⟨x, hXN hx⟩ ∈ (X.subgroupOf (Subgroup.normalizer (L : Set G))).map
        (barAut p L) := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hx)
    rw [hbot] at this
    exact Subgroup.mem_bot.1 this
  have h2 := ((mem_centralizerQuot_iff_barAut' p ⟨x, hXN hx⟩).2 h1).2.2 ℓ hℓ
  rw [commutatorElement_def]
  exact h2

theorem innerAut_le_map {p : ℕ} {L T : Subgroup G} (hLT : L ≤ T) :
    innerAut (barOf p L) ≤
      (T.subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut p L) := by
  rintro _ ⟨k, rfl⟩
  induction k using QuotientGroup.induction_on with | H ℓ => ?_
  refine ⟨⟨ℓ, Subgroup.le_normalizer ℓ.2⟩, Subgroup.mem_subgroupOf.2 (hLT ℓ.2), ?_⟩
  ext z
  induction z using QuotientGroup.induction_on with | H x => ?_
  rw [barAut_mk]
  simp [MulAut.conj_apply]
  rfl

theorem gLADelta_le_centralizer {p : ℕ} {D : Subgroup G} {d : G} (hd : d ∈ D) :
    GLADelta p D ≤ Subgroup.centralizer ({d} : Set G) := by
  intro x hx
  by_cases hd1 : d = 1
  · subst hd1; simp [Subgroup.mem_centralizer_singleton_iff]
  · simp only [GLADelta, Subgroup.mem_iInf] at hx
    exact Subgroup.map_subtype_le _ (hx d hd hd1)

theorem isElemAbelian_top_subgroup {p : ℕ} {N : Subgroup G} (hN : IsElemAbelian p N) :
    IsElemAbelian p (⊤ : Subgroup ↥N) :=
  ⟨⟨⟨fun u v => Subtype.ext (Subtype.ext (elemAbelian_comm hN u.1.2 v.1.2))⟩⟩,
    fun x _ => Subtype.ext (hN.2 x.1 x.2)⟩

theorem pRank_top_eq [Finite G] {N : Subgroup G} (hN : IsElemAbelian 3 N) :
    CFSG.Open.pRank 3 (⊤ : Subgroup ↥N) = CFSG.Open.pRank 3 N := by
  obtain ⟨j, hj⟩ := exists_card_eq_pow Nat.prime_three hN
  rw [pRank_eq_of_card Nat.prime_three hN hj, pRank_eq_of_card Nat.prime_three
    (isElemAbelian_top_subgroup hN) (by rw [Subgroup.card_top]; exact hj)]

theorem pRank_map_subtype [Finite G] {N : Subgroup G} {E : Subgroup ↥N} (hE : IsElemAbelian 3 E) :
    CFSG.Open.pRank 3 (E.map N.subtype) = CFSG.Open.pRank 3 E := by
  obtain ⟨j, hj⟩ := exists_card_eq_pow Nat.prime_three hE
  rw [pRank_eq_of_card Nat.prime_three hE hj, pRank_eq_of_card Nat.prime_three
    (isElemAbelian_map hE N.subtype)
    (by rw [Subgroup.card_map_of_injective N.subtype_injective]; exact hj)]

theorem exists_fixed_rep [Finite G] {L E : Subgroup G} (hE : IsElemAbelian 3 E) (ℓ0 : ↥L)
    (hfix : ∀ e ∈ E, ∀ he : e ∈ Subgroup.normalizer (L : Set G),
      (QuotientGroup.mk (L.normalizerMonoidHom ⟨e, he⟩ ℓ0) : barOf 3 L) = QuotientGroup.mk ℓ0)
    (hEL : E ≤ Subgroup.normalizer (L : Set G)) :
    ∃ ℓ : ↥L, (QuotientGroup.mk ℓ : barOf 3 L) = QuotientGroup.mk ℓ0 ∧
      ∀ e ∈ E, ∀ he : e ∈ Subgroup.normalizer (L : Set G), L.normalizerMonoidHom ⟨e, he⟩ ℓ = ℓ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEp : IsPGroup 3 ↥E := fun x => ⟨1, by
    apply Subtype.ext
    simpa using hE.2 x x.2⟩
  let σ : ↥E →* Equiv.Perm ↥L :=
    (MulAut.toPerm ↥L).comp ((L.normalizerMonoidHom).comp (Subgroup.inclusion hEL))
  let _ : MulAction ↥E ↥L := MulAction.compHom ↥L σ
  let S : SubMulAction ↥E ↥L :=
    { carrier := {ℓ | (QuotientGroup.mk ℓ : barOf 3 L) = QuotientGroup.mk ℓ0}
      smul_mem' := fun c x hx => by
        have h1 : (QuotientGroup.mk (c • x) : barOf 3 L) =
            barAut 3 L ⟨c, hEL c.2⟩ (QuotientGroup.mk x) := by
          rw [barAut_mk]; rfl
        have h2 := hfix c c.2 (hEL c.2)
        have hx' : (QuotientGroup.mk x : barOf 3 L) = QuotientGroup.mk ℓ0 := hx
        show (QuotientGroup.mk (c • x) : barOf 3 L) = QuotientGroup.mk ℓ0
        rw [h1, hx', barAut_mk]
        exact h2 }
  have hcard : Nat.card S = Nat.card (GLAPPrimeCore 3 ↥L) := by
    refine Nat.card_congr
      { toFun := fun s => ⟨ℓ0⁻¹ * s.1, ?_⟩
        invFun := fun o => ⟨ℓ0 * o.1, ?_⟩
        left_inv := fun s => by ext; simp
        right_inv := fun o => by ext; simp }
    · exact QuotientGroup.eq.1 s.2.symm
    · show (QuotientGroup.mk (ℓ0 * o.1) : barOf 3 L) = QuotientGroup.mk ℓ0
      rw [QuotientGroup.eq]
      simp
  have hmod := hEp.card_modEq_card_fixedPoints S
  have hcop : Nat.Coprime 3 (Nat.card S) := by
    rw [hcard]; exact coprime_card_gLAPPrimeCore_aux 3 ↥L
  have hne : Nonempty (MulAction.fixedPoints ↥E S) := by
    by_contra hemp
    rw [not_nonempty_iff] at hemp
    have h0 : Nat.card ↥(MulAction.fixedPoints ↥E S) = 0 := Nat.card_of_isEmpty
    rw [h0] at hmod
    have h3 : 3 ∣ Nat.card S := (Nat.modEq_zero_iff_dvd).1 hmod
    have := Nat.Coprime.eq_one_of_dvd hcop h3
    omega
  obtain ⟨⟨s, hs⟩⟩ := hne
  refine ⟨s.1, s.2, fun e he hnorm => ?_⟩
  have := hs ⟨e, he⟩
  have h3 : σ ⟨e, he⟩ s.1 = s.1 := congrArg Subtype.val this
  exact h3

theorem gLAPPrimeCoreOf_le_gammaPrimeIn [Finite G] {L N : Subgroup G}
    (hNL : N ≤ Subgroup.normalizer (L : Set G)) (hN : IsElemAbelian 3 N)
    (hN1 : 1 ≤ CFSG.Open.pRank 3 N) :
    GLAPPrimeCoreOf 3 L ≤ gammaPrimeIn 3 (CFSG.Open.pRank 3 N - 1) N L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O : Subgroup G := GLAPPrimeCoreOf 3 L with hOdef
  have hNO : N ≤ Subgroup.normalizer (O : Set G) := fun n hn => by
    have hnL := hNL hn
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => conj_mem_gLAPPrimeCoreOf' hnL hy, fun hy => ?_⟩
    have := conj_mem_gLAPPrimeCoreOf' (inv_mem hnL) hy
    simpa [mul_assoc] using this
  let φ : ↥N →* MulAut ↥O := O.normalizerMonoidHom.comp (Subgroup.inclusion hNO)
  let _ : MulDistribMulAction ↥N ↥O := MulDistribMulAction.compHom ↥O φ
  have _ : CFSG.IsElementaryAbelian 3 ↥N :=
    { is_comm := ⟨fun a b => Subtype.ext (elemAbelian_comm hN a.2 b.2)⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (hN.2 x x.2) }
  obtain ⟨j, hj⟩ := exists_card_eq_pow Nat.prime_three hN
  have hj1 : 1 ≤ j := by rw [pRank_eq_of_card Nat.prime_three hN hj] at hN1; exact hN1
  have : Nontrivial ↥N := by
    refine Finite.one_lt_card_iff_nontrivial.1 ?_
    rw [hj]
    exact Nat.one_lt_pow (by omega) (by norm_num)
  have hp3 : ¬ 3 ∣ Nat.card ↥O := by
    have hc : Nat.card ↥O = Nat.card (GLAPPrimeCore 3 ↥L) :=
      Subgroup.card_map_of_injective L.subtype_injective
    rw [hc]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 (coprime_card_gLAPPrimeCore_aux 3 ↥L)
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := 3) (A := ↥N) (H := ↥O) hp3
  intro y hy
  have h1 : (⟨y, hy⟩ : ↥O) ∈ ⨆ (B : Subgroup ↥N) (_ : B.index = 3),
      CFSG.fixedPointSubgroup ↥B ↥O := hgen ▸ Subgroup.mem_top _
  have h2 := Subgroup.mem_map_of_mem O.subtype h1
  simp only [Subgroup.map_iSup] at h2
  refine (iSup_le fun B => iSup_le fun hB => ?_ :
    (⨆ (B : Subgroup ↥N) (_ : B.index = 3),
      (CFSG.fixedPointSubgroup ↥B ↥O).map O.subtype) ≤
        gammaPrimeIn 3 (CFSG.Open.pRank 3 N - 1) N L) h2
  rintro _ ⟨x, hx, rfl⟩
  have hxL : (x : G) ∈ L := Subgroup.map_subtype_le _ x.2
  have hcard : Nat.card ↥B * 3 = Nat.card ↥N := by rw [← hB]; exact B.card_mul_index
  have hBel : IsElemAbelian 3 B := isElemAbelian_of_le' (isElemAbelian_top_subgroup hN) le_top
  obtain ⟨k, hk⟩ := exists_card_eq_pow Nat.prime_three hBel
  have hkj : k + 1 = j := by
    have h3 : 3 ^ (k + 1) = 3 ^ j := by rw [pow_succ, ← hk, hcard, hj]
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h3
  have hrk : CFSG.Open.pRank 3 N - 1 ≤ CFSG.Open.pRank 3 (B.map N.subtype) := by
    rw [pRank_map_subtype hBel, pRank_eq_of_card Nat.prime_three hBel hk,
      pRank_eq_of_card Nat.prime_three hN hj]
    omega
  refine Subgroup.mem_iSup_of_mem (B.map N.subtype) (Subgroup.mem_iSup_of_mem
    ⟨Subgroup.map_subtype_le B, hrk⟩ ⟨hxL, ?_⟩)
  show (x : G) ∈ Subgroup.centralizer (↑(B.map N.subtype) : Set G)
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨b, hb, rfl⟩
  have e : ((b : ↥N) : G) * (x : G) * ((b : ↥N) : G)⁻¹ = x :=
    congrArg Subtype.val (hx ⟨b, hb⟩)
  calc ((b : ↥N) : G) * (x : G)
      = (((b : ↥N) : G) * (x : G) * ((b : ↥N) : G)⁻¹) * ((b : ↥N) : G) := by group
    _ = (x : G) * ((b : ↥N) : G) := by rw [e]

theorem le_gammaPrimeIn_of_quotient [Finite G] {L N : Subgroup G}
    (hNL : N ≤ Subgroup.normalizer (L : Set G)) (hN : IsElemAbelian 3 N)
    (hN1 : 1 ≤ CFSG.Open.pRank 3 N)
    (hK : (⊤ : Subgroup (barOf 3 L)) ≤ ⨆ (E : Subgroup ↥N)
      (_ : CFSG.Open.pRank 3 (⊤ : Subgroup ↥N) - 1 ≤ CFSG.Open.pRank 3 E),
        fixedSubgroup ((barAut 3 L).comp (Subgroup.inclusion hNL)) E) :
    L ≤ gammaPrimeIn 3 (CFSG.Open.pRank 3 N - 1) N L := by
  set Γ := gammaPrimeIn 3 (CFSG.Open.pRank 3 N - 1) N L with hΓ
  have hO : GLAPPrimeCoreOf 3 L ≤ Γ := gLAPPrimeCoreOf_le_gammaPrimeIn hNL hN hN1
  set M : Subgroup (barOf 3 L) :=
    (Γ.subgroupOf L).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)) with hM
  have hMtop : (⊤ : Subgroup (barOf 3 L)) ≤ M := by
    refine hK.trans (iSup_le fun E => iSup_le fun hE => ?_)
    intro k hk
    obtain ⟨ℓ0, rfl⟩ := QuotientGroup.mk_surjective k
    have hEel : IsElemAbelian 3 E :=
      isElemAbelian_of_le' (isElemAbelian_top_subgroup hN) le_top
    have hE'el : IsElemAbelian 3 (E.map N.subtype) := isElemAbelian_map hEel N.subtype
    have hE'L : E.map N.subtype ≤ Subgroup.normalizer (L : Set G) :=
      (Subgroup.map_subtype_le E).trans hNL
    obtain ⟨ℓ, hℓ, hfixℓ⟩ := exists_fixed_rep hE'el ℓ0 (fun e he hnorm => by
      obtain ⟨n, hn, rfl⟩ := he
      have h1 := hk n hn
      rw [MonoidHom.comp_apply] at h1
      have h2 : (QuotientGroup.mk (L.normalizerMonoidHom ⟨n.1, hnorm⟩ ℓ0) : barOf 3 L) =
          QuotientGroup.mk ℓ0 := by
        rw [← barAut_mk]; exact h1
      exact h2) hE'L
    have hrk : CFSG.Open.pRank 3 N - 1 ≤ CFSG.Open.pRank 3 (E.map N.subtype) := by
      rw [pRank_map_subtype hEel, ← pRank_top_eq hN]; exact hE
    have hℓΓ : (ℓ : G) ∈ Γ := by
      refine Subgroup.mem_iSup_of_mem (E.map N.subtype) (Subgroup.mem_iSup_of_mem
        ⟨(Subgroup.map_subtype_le E), hrk⟩ ⟨ℓ.2, ?_⟩)
      show (ℓ : G) ∈ Subgroup.centralizer (↑(E.map N.subtype) : Set G)
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨n, hn, rfl⟩
      have e := congrArg Subtype.val (hfixℓ (n : G) ⟨n, hn, rfl⟩ (hNL n.2))
      have e' : (n : G) * (ℓ : G) * (n : G)⁻¹ = ℓ := e
      calc (n : G) * ℓ = ((n : G) * ℓ * (n : G)⁻¹) * n := by group
        _ = ℓ * n := by rw [e']
    refine ⟨ℓ, Subgroup.mem_subgroupOf.2 hℓΓ, ?_⟩
    rw [QuotientGroup.mk'_apply, hℓ]
  intro ℓ hℓ
  obtain ⟨γ, hγ, hγℓ⟩ := hMtop (Subgroup.mem_top (QuotientGroup.mk (⟨ℓ, hℓ⟩ : ↥L) : barOf 3 L))
  have hγΓ : (γ : G) ∈ Γ := Subgroup.mem_subgroupOf.1 hγ
  have h1 : γ⁻¹ * ⟨ℓ, hℓ⟩ ∈ GLAPPrimeCore 3 ↥L := by
    rw [QuotientGroup.mk'_apply] at hγℓ
    exact QuotientGroup.eq.1 hγℓ
  have h2 : ((γ⁻¹ * ⟨ℓ, hℓ⟩ : ↥L) : G) ∈ GLAPPrimeCoreOf 3 L := Subgroup.mem_map_of_mem L.subtype h1
  have h3 := Γ.mul_mem hγΓ (hO h2)
  simpa using h3

omit [Group G] in
theorem isInGMinusOne_of_hyperplane (h2316 : Input23_16At3) (h224 : Input22_4)
    {G' : Type} [Group G'] [Finite G'] {X B L : Subgroup G'} (hBX : B ≤ X)
    (hBel : IsElemAbelian 3 B) (hcomp : GLAPComponent 3 X L) {H : Subgroup G'}
    (hH : H ≤ B ⊓ Subgroup.normalizer (L : Set G'))
    (hHcard : Nat.card ↥(B ⊓ Subgroup.normalizer (L : Set G')) = 3 * Nat.card ↥H)
    (hHfield : ∀ h ∈ H, InducesFieldAut 3 L h) : IsInGMinusOne 3 B L := by
  set N : Subgroup G' := B ⊓ Subgroup.normalizer (L : Set G') with hNdef
  have hNL : N ≤ Subgroup.normalizer (L : Set G') := inf_le_right
  have hN : IsElemAbelian 3 N := isElemAbelian_of_le' hBel inf_le_left
  obtain ⟨j, hj⟩ := exists_card_eq_pow Nat.prime_three hN
  have hHel : IsElemAbelian 3 H := isElemAbelian_of_le' hN hH
  obtain ⟨k, hk⟩ := exists_card_eq_pow Nat.prime_three hHel
  have hkj : k + 1 = j := by
    have h3 : 3 ^ (k + 1) = 3 ^ j := by rw [pow_succ, mul_comm, ← hk, ← hHcard, hj]
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h3
  have hN1 : 1 ≤ CFSG.Open.pRank 3 N := by
    rw [pRank_eq_of_card Nat.prime_three hN hj]; omega
  let ρ : ↥N →* MulAut (barOf 3 L) := (barAut 3 L).comp (Subgroup.inclusion hNL)
  set H' : Subgroup ↥N := H.subgroupOf N with hH'
  have hH'card : Nat.card ↥H' = Nat.card ↥H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv
  have hH'el : IsElemAbelian 3 H' :=
    isElemAbelian_of_le' (isElemAbelian_top_subgroup hN) le_top
  have hrkH' : CFSG.Open.pRank 3 (⊤ : Subgroup ↥N) - 1 ≤ CFSG.Open.pRank 3 H' := by
    rw [pRank_top_eq hN, pRank_eq_of_card Nat.prime_three hN hj,
      pRank_eq_of_card Nat.prime_three hH'el (hH'card.trans hk)]
    omega
  have hK : (⊤ : Subgroup (barOf 3 L)) ≤ ⨆ (E : Subgroup ↥N)
      (_ : CFSG.Open.pRank 3 (⊤ : Subgroup ↥N) - 1 ≤ CFSG.Open.pRank 3 E), fixedSubgroup ρ E := by
    by_cases htriv : ∀ h ∈ H', ρ h = 1
    · refine le_trans ?_ (le_iSup₂_of_le H' hrkH' le_rfl)
      intro x _ h hh
      rw [htriv h hh]; rfl
    · push Not at htriv
      obtain ⟨h0, hh0, hρ0⟩ := htriv
      have hfa : IsFieldAutThree (ρ h0) := by
        obtain ⟨_, hf⟩ := hHfield h0.1 (Subgroup.mem_subgroupOf.1 hh0)
        exact hf
      have hT : IsThreeType (barOf 3 L) := IsThreeType.of_isFieldAutThree hfa hρ0
      have hq : CFSG.Open.IsQuasisimple (barOf 3 L) := isQuasisimple_quotient_of_glaPComponent hcomp
      exact h2316 (barOf 3 L) hq hT ↥N ρ
        (isElemAbelian_top_subgroup hN)
        ⟨H', by rw [hH'card, ← hHcard], fun h hh => by
          obtain ⟨_, hf⟩ := hHfield h.1 (Subgroup.mem_subgroupOf.1 hh)
          exact hf⟩
  have hL := le_gammaPrimeIn_of_quotient hNL hN hN1 hK
  exact h224 G' X B L hBX hBel hcomp hN1 hL

theorem false_of_branch_b (h191 : Input19_1_2) (h197 : Input19_7_3d)
    (h7 : Input7_FieldInnDiag) {G : Type} [Group G] [Finite G] {m : ℕ} (hS : GLStanding G m 3)
    {B : Subgroup G} (hBel : IsElemAbelian 3 B) {b : G} (hb : b ∈ B) (hb1 : b ≠ 1)
    {L : Subgroup G} (hcomp : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L)
    {D : Subgroup G} (hDel : IsElemAbelian 3 D) (hDcard : Nat.card D = 3 ^ 2) (hDB : D ≤ B)
    (hnot : ¬ ⁅L, GLADelta 3 D ⊓ Subgroup.centralizer ({b} : Set G)⁆ ≤ GLAPPrimeCoreOf 3 L)
    {a : G} (haD : a ∈ D) (ha1 : a ≠ 1) (haN : a ∈ Subgroup.normalizer (L : Set G))
    (hfa : IsFieldAutThree (barAut 3 L ⟨a, haN⟩)) : False := by
  have := hS.simple
  set C : Subgroup G := Subgroup.centralizer ({b} : Set G) with hC
  set X : Subgroup G := GLADelta 3 D ⊓ C with hXdef
  have hDne : D ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hDcard
    norm_num at hDcard
  have hbD : b ∈ Subgroup.centralizer (D : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact elemAbelian_comm hBel (hDB hd) hb
  obtain ⟨hnorm, hmain⟩ :=
    h191 G hS.nonabelian hS.kProper 3 Nat.prime_three D hDel hDne b hbD hb1 (hBel.2 b hb)
  have hXN : X ≤ Subgroup.normalizer (L : Set G) := hnorm L hcomp
  have hnot' : ¬ ⁅L, X⁆ ≤ GLAPPrimeCoreOf 3 C := by
    intro hle
    apply hnot
    have hLX : ⁅L, X⁆ ≤ L := Subgroup.commutator_le.2 fun ℓ hℓ x hx => by
      rw [commutatorElement_def]
      have h1 := (Subgroup.mem_normalizer_iff.1 (hXN hx) ℓ⁻¹).1 (L.inv_mem hℓ)
      have h2 := L.mul_mem hℓ h1
      simpa [mul_assoc] using h2
    intro y hy
    have h3 := gLAPPrimeCoreOf_inf_le Nat.prime_three C L ⟨hle hy, hLX hy⟩
    rwa [inf_eq_right.2 hcomp.1] at h3
  obtain ⟨hker, hDN, himg⟩ := hmain L hcomp hnot'
  by_cases h1 : barAut 3 L ⟨a, haN⟩ = 1
  · have hmem : a ∈ kerB 3 D L := ⟨haD, (mem_centralizerQuot_iff_barAut' 3 ⟨a, haN⟩).2 h1⟩
    rw [hker] at hmem
    exact ha1 (Subgroup.mem_bot.1 hmem)
  · have hT : IsThreeType (barOf 3 L) := IsThreeType.of_isFieldAutThree hfa h1
    have hq : CFSG.Open.IsQuasisimple (barOf 3 L) := isQuasisimple_quotient_of_glaPComponent hcomp
    set Dt : Subgroup (MulAut (barOf 3 L)) :=
      (D.subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut 3 L) with hDt
    set Ht : Subgroup (MulAut (barOf 3 L)) :=
      ((X ⊔ L).subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut 3 L) with hHt
    have hDtE : IsEkIn 3 2 ⊤ Dt :=
      ⟨le_top, isElemAbelian_map (isElemAbelian_subgroupOf hDel) _, by
        rw [hDt, card_map_barAut_of_kerB_eq_bot hDN hker, hDcard]⟩
    have hinn : innerAut (barOf 3 L) ≤ Ht := innerAut_le_map (p := 3) (le_sup_right : L ≤ X ⊔ L)
    have hconjT : ∀ d ∈ D, ∀ t ∈ X ⊔ L, d * t * d⁻¹ ∈ X ⊔ L := by
      intro d hd t ht
      have hle : X ⊔ L ≤ (X ⊔ L).comap (MulAut.conj d).toMonoidHom := by
        refine sup_le (fun x hx => ?_) (fun ℓ hℓ => ?_)
        · have hdx : d * x = x * d :=
            Subgroup.mem_centralizer_iff.1 (gLADelta_le_centralizer hd hx.1) d rfl
          have e : d * x * d⁻¹ = x := by rw [hdx]; group
          rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, e]
          exact Subgroup.mem_sup_left hx
        · have hdl : d * ℓ * d⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hDN hd) ℓ).1 hℓ
          rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          exact Subgroup.mem_sup_right hdl
      have := hle ht
      rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
    have hconjH : ∀ d ∈ Dt, ∀ h ∈ Ht, d * h * d⁻¹ ∈ Ht := by
      rintro _ ⟨⟨d, hdN⟩, hdD, rfl⟩ _ ⟨⟨t, htN⟩, htT, rfl⟩
      refine ⟨⟨d, hdN⟩ * ⟨t, htN⟩ * ⟨d, hdN⟩⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
      exact Subgroup.mem_subgroupOf.2
        (hconjT d (Subgroup.mem_subgroupOf.1 hdD) t (Subgroup.mem_subgroupOf.1 htT))
    have hnormH : Dt ≤ Subgroup.normalizer (Ht : Set (MulAut (barOf 3 L))) := by
      intro d hd
      refine Subgroup.mem_normalizer_iff.2 fun h => ⟨fun hh => hconjH d hd h hh, fun hh => ?_⟩
      have h2 := hconjH d⁻¹ (Dt.inv_mem hd) _ hh
      have e : d⁻¹ * (d * h * d⁻¹) * d⁻¹⁻¹ = h := by group
      rwa [e] at h2
    have hdelta : localDeltaIn 3 Ht Dt ≠ ⊥ := by
      intro hbot
      rw [hbot] at himg
      exact map_barAut_ne_bot hXN hnot (le_bot_iff.1 himg)
    have hI := h197 (barOf 3 L) hq hT Dt Ht hDtE hinn hnormH hdelta (barAut 3 L ⟨a, haN⟩)
      (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 haD))
    exact h1 (h7 (barOf 3 L) hq _ hfa hI)

end Lemma54Ns

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

theorem lemma54_of_inputs (h2316 : Lemma54Ns.Input23_16At3) (h224 : Lemma54Ns.Input22_4)
    (h191 : Lemma54Ns.Input19_1_2) (h197 : Lemma54Ns.Input19_7_3d)
    (h7 : Lemma54Ns.Input7_FieldInnDiag) : Lemma54 := by
  intro G _ _ m hS hC B hB b hb hb1 L hL A hAB hA
  by_contra hrk
  have hrk3 : 3 ≤ CFSG.Open.pRank 3 A := by omega
  have hBel : IsElemAbelian 3 B := hB.1.1
  have hBcard : Nat.card B = 3 ^ 4 := by
    have := hB.1.2.1
    rwa [hC.2.1] at this
  have hBrank : CFSG.Open.pRank 3 B = 4 := pRank_eq_of_card Nat.prime_three hBel hBcard
  have hAel : IsElemAbelian 3 A := Lemma54Ns.isElemAbelian_of_le' hBel hAB
  obtain ⟨k, hk⟩ := Lemma54Ns.exists_card_eq_pow Nat.prime_three hAel
  have hk3 : 3 ≤ k := (pRank_eq_of_card Nat.prime_three hAel hk) ▸ hrk3
  have hcomp := hL.1
  have hAN : ∀ a ∈ A, a ∈ Subgroup.normalizer (L : Set G) := fun a ha => (hA a ha).1
  have hbC : B ≤ Subgroup.centralizer ({b} : Set G) := le_centralizer_of_mem hBel hb
  rcases hL.2 with ⟨hlam, hpsi⟩ | ⟨D, hD, hnot⟩
  ·
    have hnotslob := Lemma54Ns.not_slob_of_le_lambdaOf hcomp hlam
    have hANle : A ≤ B ⊓ Subgroup.normalizer (L : Set G) := fun a ha => ⟨hAB ha, hAN a ha⟩
    obtain ⟨H, hHA, hHcard⟩ := Lemma54Ns.exists_hyperplane hBel hBcard inf_le_left hANle hk hk3
    have hG := Lemma54Ns.isInGMinusOne_of_hyperplane h2316 h224 hbC hBel hcomp
      (fun h hh => hANle (hHA hh)) hHcard (fun h hh => hA h (hHA hh))
    have hG1 : IsInGOne 3 B L := Lemma54Ns.isInGOne_of_isInGMinusOne hBrank hG
    apply hpsi
    refine (le_sSup ⟨hcomp, hnotslob, hG1⟩ : L ≤ psiOf 3 B b).trans ?_
    exact (le_sup_left.trans le_sup_left : psiOf 3 B b ≤ psiStar 3 B b).trans
      (le_iSup₂_of_le b hb (le_iSup (fun _ : b ≠ 1 => psiStar 3 B b) hb1))
  ·
    obtain ⟨hDB, hDel, hDcard⟩ := hD
    obtain ⟨a, ⟨haA, haD⟩, ha1⟩ := Lemma54Ns.exists_mem_inf_ne_one hAB hDB (by
      rw [hBcard, hk, hDcard]
      have : 3 ^ 3 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
      norm_num at this ⊢
      omega)
    obtain ⟨haN, hfa⟩ := hA a haA
    exact Lemma54Ns.false_of_branch_b h191 h197 h7 hS hBel hb hb1 hcomp hDel hDcard hDB hnot haD ha1
      haN hfa

end CFSG.HardMathSupport.Solomon.LocalBalance
