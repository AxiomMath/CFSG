module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.PrimeBlocksD2
public import CFSG.LocalAnalysis.AGLEmbeddingD2.U3Data
import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisInverting
import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveOddCore

public section

open scoped commutatorElement

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2

namespace CFSG.AGLEmbeddingD2

section Generation

variable {Y : Type*} [Group Y]

theorem le_closure_two_elements_of_inverted_mod {N R₀ Z₀ : Subgroup Y} {p : ℕ} (hp : Odd p)
    (hRN : R₀ ≤ N) (hZR : Z₀ ≤ R₀) (hZc : ∀ z ∈ Z₀, ∀ r ∈ R₀, z * r = r * z)
    (hcomm : Z₀ ≤ ⁅R₀, R₀⁆) (hexp : ∀ x ∈ R₀, x ^ p = 1) {y : Y} (hy : y ∈ N)
    (hy2 : ∃ k : ℕ, y ^ 2 ^ k = 1) (hinv : ∀ x ∈ R₀, ∃ z ∈ Z₀, y * x * y⁻¹ = x⁻¹ * z) :
    R₀ ≤ Subgroup.closure {a : Y | a ∈ N ∧ ∃ k : ℕ, a ^ 2 ^ k = 1} := by
  set T := Subgroup.closure {a : Y | a ∈ N ∧ ∃ k : ℕ, a ^ 2 ^ k = 1} with hT
  obtain ⟨k, hk⟩ := hy2
  obtain ⟨m, hm⟩ := hp
  have h2 : y⁻¹ ∈ {a : Y | a ∈ N ∧ ∃ k : ℕ, a ^ 2 ^ k = 1} := by
    refine ⟨N.inv_mem hy, k, ?_⟩
    rw [inv_pow, hk, inv_one]
  have hsplit : ∀ x ∈ R₀, ∃ s ∈ T, s ∈ R₀ ∧ ∃ z ∈ Z₀, x = s * z := by
    intro x hx
    obtain ⟨z, hz, hyx⟩ := hinv x hx
    have hxN : x ∈ N := hRN hx
    have h1 : x * y * x⁻¹ ∈ {a : Y | a ∈ N ∧ ∃ k : ℕ, a ^ 2 ^ k = 1} := by
      refine ⟨N.mul_mem (N.mul_mem hxN hy) (N.inv_mem hxN), k, ?_⟩
      rw [conj_pow, hk]
      simp
    have hcT : x * y * x⁻¹ * y⁻¹ ∈ T :=
      T.mul_mem (Subgroup.subset_closure h1) (Subgroup.subset_closure h2)
    have hzx : z⁻¹ * x = x * z⁻¹ := hZc z⁻¹ (Z₀.inv_mem hz) x hx
    have hc : x * y * x⁻¹ * y⁻¹ = x * x * z⁻¹ := by
      have h3 : y * x⁻¹ * y⁻¹ = z⁻¹ * x := by
        have h4 : y * x⁻¹ * y⁻¹ = (y * x * y⁻¹)⁻¹ := by group
        rw [h4, hyx]
        group
      calc x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
        _ = x * (z⁻¹ * x) := by rw [h3]
        _ = x * (x * z⁻¹) := by rw [hzx]
        _ = x * x * z⁻¹ := by group
    set c := x * y * x⁻¹ * y⁻¹ with hcdef
    have hcR : c ∈ R₀ := by
      rw [hc]
      exact R₀.mul_mem (R₀.mul_mem hx hx) (R₀.inv_mem (hZR hz))
    have hxx : x * x = c * z := by rw [hc]; group
    have hcz : Commute c z := (hZc z hz c hcR).symm
    have hx2 : x = (x * x) ^ (m + 1) := by
      have h5 : (x * x) ^ (m + 1) = x ^ (2 * m + 1) * x := by
        rw [← pow_two, ← pow_mul, show 2 * (m + 1) = (2 * m + 1) + 1 by ring, pow_succ]
      rw [h5, ← hm, hexp x hx, one_mul]
    refine ⟨c ^ (m + 1), T.pow_mem hcT _, R₀.pow_mem hcR _, z ^ (m + 1), Z₀.pow_mem hz _, ?_⟩
    rw [← hcz.mul_pow, ← hxx]
    exact hx2
  have hcommT : ⁅R₀, R₀⁆ ≤ T := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨s, hsT, hsR, z, hz, rfl⟩ := hsplit a ha
    obtain ⟨s', hs'T, hs'R, z', hz', rfl⟩ := hsplit b hb
    have e1 : ⁅s * z, s' * z'⁆ = ⁅s, s'⁆ := by
      simp only [commutatorElement_def]
      have a1 : z * s' = s' * z := hZc z hz s' hs'R
      have a2 : z * z' = z' * z := hZc z hz z' (hZR hz')
      have a3 : z' * s⁻¹ = s⁻¹ * z' := hZc z' hz' s⁻¹ (R₀.inv_mem hsR)
      calc s * z * (s' * z') * (s * z)⁻¹ * (s' * z')⁻¹
          = s * (z * s') * (z' * z⁻¹) * s⁻¹ * z'⁻¹ * s'⁻¹ := by group
        _ = s * (s' * z) * (z' * z⁻¹) * s⁻¹ * z'⁻¹ * s'⁻¹ := by rw [a1]
        _ = s * s' * (z * z') * z⁻¹ * s⁻¹ * z'⁻¹ * s'⁻¹ := by group
        _ = s * s' * (z' * z) * z⁻¹ * s⁻¹ * z'⁻¹ * s'⁻¹ := by rw [a2]
        _ = s * s' * z' * s⁻¹ * z'⁻¹ * s'⁻¹ := by group
        _ = s * s' * (z' * s⁻¹) * z'⁻¹ * s'⁻¹ := by group
        _ = s * s' * (s⁻¹ * z') * z'⁻¹ * s'⁻¹ := by rw [a3]
        _ = s * s' * s⁻¹ * s'⁻¹ := by group
    rw [e1]
    exact T.mul_mem (T.mul_mem (T.mul_mem hsT hs'T) (T.inv_mem hsT)) (T.inv_mem hs'T)
  intro x hx
  obtain ⟨s, hsT, -, z, hz, rfl⟩ := hsplit x hx
  exact T.mul_mem hsT (hcommT (hcomm hz))

end Generation

section HeisData

variable {G : Type} [Group G] [Finite G] {p : ℕ} {M H R Z : Subgroup G}

private theorem D2HeisData.le_R (h : D2HeisData p M H R Z) : Z ≤ R :=
  h.heis.2.1 ▸ Subgroup.commutator_le_self R

private theorem D2HeisData.conj_mem (h : D2HeisData p M H R Z) {g : G}
    (hg : ∀ x ∈ R, g * x * g⁻¹ ∈ R) : ∀ z ∈ Z, g * z * g⁻¹ ∈ Z := by
  intro z hz
  rw [← h.heis.2.1] at hz ⊢
  have hmap : (⁅R, R⁆ : Subgroup G).map (MulAut.conj g).toMonoidHom ≤ ⁅R, R⁆ := by
    rw [Subgroup.map_commutator]
    have hR : R.map (MulAut.conj g).toMonoidHom ≤ R := by
      rintro _ ⟨x, hx, rfl⟩
      exact hg x hx
    exact Subgroup.commutator_mono hR hR
  exact hmap ⟨z, hz, by simp [MulAut.conj_apply]⟩

private theorem D2HeisData.mul_comm_of_mem (h : D2HeisData p M H R Z) :
    ∀ z ∈ Z, ∀ r ∈ R, z * r = r * z := by
  have hp : p.Prime := h.pair.prime
  have : Fact p.Prime := ⟨hp⟩
  have : Group.IsNilpotent R := h.pair.isPGroup_R.isNilpotent
  have hZR := h.le_R
  set Z' : Subgroup R := Z.subgroupOf R with hZ'
  have hZ'n : Z'.Normal := ⟨fun n hn g => by
    show ((g * n * g⁻¹ : R) : G) ∈ Z
    have : ((g * n * g⁻¹ : R) : G) = (g : G) * (n : G) * (g : G)⁻¹ := rfl
    rw [this]
    exact h.conj_mem (fun x hx => R.mul_mem (R.mul_mem g.2 hx) (R.inv_mem g.2)) _ hn⟩
  have hcard : Nat.card Z' = p :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZR).toEquiv).trans h.heis.1
  have hZ'ne : Z' ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    exact hp.one_lt.ne hcard
  have hint := Group.IsNilpotent.inf_center_ne_bot_of_normal hZ'ne
  have hdvd : Nat.card (Z' ⊓ Subgroup.center R : Subgroup R) ∣ p :=
    hcard ▸ Subgroup.card_dvd_of_le inf_le_left
  have hle : Z' ⊓ Subgroup.center R = Z' := by
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exact absurd (Subgroup.eq_bot_of_card_eq _ h1) hint
    · exact Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h1, hcard])
  intro z hz r hr
  have hzc : (⟨z, hZR hz⟩ : R) ∈ Z' ⊓ Subgroup.center R := by
    rw [hle]
    exact Subgroup.mem_subgroupOf.mpr hz
  exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hzc.2 ⟨r, hr⟩)).symm

private theorem D2HeisData.coprime_of_perfect (h : D2HeisData p M H R Z) :
    ∀ Y : Subgroup G, Y ≤ M ⊓ Subgroup.normalizer (pCoreOf 2 H : Set G) → ⁅Y, Y⁆ = Y →
      p.Coprime (Nat.card Y) := by
  intro Y hY hperf
  have hYN := h.perfect_le Y (h.pair.inf_eq_inf_normalizer_twoCore ▸ hY) hperf
  exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hYN)
    (glbPrimeCore_coprime p H)

theorem D2HeisData.exists_inverting (h : D2HeisData p M H R Z) :
    ∃ t ∈ H ⊓ M, ∃ e : ℕ, 6 ∣ e ∧ ∀ x ∈ R, ∃ z ∈ Z, t ^ e * x * (t ^ e)⁻¹ = x⁻¹ * z := by
  obtain ⟨t, htK, -, -, -, e, -, -, h6, -, hinv, -⟩ := h.lines
  exact ⟨t, htK, e, h6, hinv⟩

end HeisData

theorem AGLPair.pow_six_mem_normalizer_weakSBlock {G : Type} [Group G] [Finite G] {p : ℕ}
    {M H R : Subgroup G} (hD1 : D1For G)
    (hB3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → BlockHasThree M (pCoreOf 2 H) L)
    (h : AGLPair p M H R) {t : G} (ht : t ∈ H ⊓ M) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) : t ^ 6 ∈ Subgroup.normalizer (L : Set G) := by
  have htM : t ∈ M := ht.2
  have htS : t ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    (h.inf_eq_inf_normalizer_twoCore ▸ ht).2
  refine pow_six_mem_normalizer_of_bound fun m hmove => ?_
  have hinj := injective_map_conj_pow_aux' (L := L) (t := t) (m := m) hmove
  have h1 := h.card_le_pRank_three_of_blocks hB3
    (fun i : Fin m => L.map (MulAut.conj (t ^ (i : ℕ))).toMonoidHom)
    (fun i => hL.map_conj (M.pow_mem htM _) (Subgroup.pow_mem _ htS _)) hinj
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h1
  exact h1.trans (h.pRank_inf_le_three hD1 Nat.prime_three (by decide))

theorem D2HeisData.barM_le_centralizer_of_weakSBlock {G : Type} [Group G] [Finite G] {p : ℕ}
    {M H R Z : Subgroup G} (hD1 : D1For G) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : NoXBlockFor G) (hK2 : KFactParabolicThree)
    (hC3 : CitedBlockThreeTransvection) (hK5 : KFactBlockThreeAltSeven)
    (hKin : KFactTwoGenInner) (hKP : KFactParabolicPrime)
    (hC3p : CitedBlockTransvectionPrime) (hK5p : KFactBlockAltSevenPrime)
    (h : D2HeisData p M H R Z) (hp5 : 5 ≤ p) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    barM M R ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  have hp : p.Prime := h.pair.prime
  set S := pCoreOf 2 H with hSdef
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  have hB3 : ∀ L : Subgroup G, IsWeakSBlock M S L → BlockHasThree M S L := fun L hL =>
    h.pair.blockHasThree h85 h86 h93 hD2 hK2 hC3 hK5 hL
  have hexp : ∀ r ∈ R, r ^ p = 1 := h.heis.2.2
  have hZR : Z ≤ R := h.le_R
  have hRL : R ≤ Subgroup.normalizer (L : Set G) := fun x hxR =>
    h.pair.mem_normalizer_weakSBlock hD1 hB3 hp hp5 (h.pair.R_le_inf hxR)
      (isPGroup_zpowers_of_pow_eq_one (k := 1) (by simpa using hexp x hxR)) hL
  obtain ⟨t, htK, e, h6, hιinv⟩ := h.exists_inverting
  set ι := t ^ e with hι
  have hιM : ι ∈ M := M.pow_mem htK.2 _
  have hιL : ι ∈ Subgroup.normalizer (L : Set G) := by
    obtain ⟨c', hc'⟩ := h6
    rw [hι, hc', pow_mul]
    exact Subgroup.pow_mem _ (h.pair.pow_six_mem_normalizer_weakSBlock hD1 hB3 htK hL) c'
  have hιR : ∀ x ∈ R, ι * x * ι⁻¹ ∈ R := by
    intro x hx
    obtain ⟨z, hz, hxz⟩ := hιinv x hx
    rw [hxz]
    exact R.mul_mem (R.inv_mem hx) (hZR hz)
  have hιZ := h.conj_mem hιR
  obtain ⟨k, j, hj, hn⟩ := Nat.exists_eq_two_pow_mul_odd (n := orderOf ι) (orderOf_pos ι).ne'
  have hjk : (ι ^ j) ^ 2 ^ k = 1 := by
    rw [← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one]
  have hyinv : ∀ x ∈ R, ∃ z ∈ Z, ι ^ j * x * (ι ^ j)⁻¹ = x⁻¹ * z := fun x hx =>
    exists_mul_of_pow_inverts_mod h.mul_comm_of_mem hιZ hιinv hj hx
  have hy2M : ι ^ j ∈ M := M.pow_mem hιM j
  have hy2L : ι ^ j ∈ Subgroup.normalizer (L : Set G) := Subgroup.pow_mem _ hιL j
  have hPq : ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      V ≤ barM M (Subgroup.normalizer (S : Set G) ⊓ L) → ⁅V, V⁆ = V →
        p.Coprime (Nat.card V) :=
    fun V hV hVp => coprime_card_of_le_barM_of_perfect (inf_le_right.trans hL.le)
      (fun W hW hWp => h.coprime_of_perfect W
        (le_inf (hW.trans (inf_le_right.trans hL.le)) (hW.trans inf_le_left)) hWp) hV hVp
  have hP := h.pair.coprime_card_barM_normalizer_inf h85 h93 hD2 hKP hC3p hK5p hL hp hp5 hPq
  have hMtop : M ≠ ⊤ := fun hM => h.pair.not_le (hM ▸ le_top)
  have hcat : IsCatalogGroup (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) :=
    ((catalogSimpleSections_of_isKProper h.pair.glob.kProper M hMtop).quotient
      _).isCatalogGroup_center_quotient hL.component
  set yb := mk ⟨ι ^ j, hy2M⟩ with hyb
  have hybN : yb ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    mem_normalizer_barM hy2M hy2L
  have hyb2 : ∃ k : ℕ, yb ^ 2 ^ k = 1 := by
    refine ⟨k, ?_⟩
    have : (⟨ι ^ j, hy2M⟩ : M) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hjk)
    rw [hyb, ← map_pow, this, map_one]
  have hclosR : barM M R ≤ Subgroup.closure
      {a : ↥M ⧸ CFSG.pCore 2 ↥M | a ∈ Subgroup.normalizer
        (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧ ∃ k : ℕ, a ^ 2 ^ k = 1} := by
    refine le_closure_two_elements_of_inverted_mod (hp.odd_of_ne_two (by omega)) ?_
      (barM_mono hZR) ?_ ?_ ?_ hybN hyb2 ?_
    · rintro _ ⟨⟨x, hxM⟩, hx, rfl⟩
      exact mem_normalizer_barM hxM (hRL (Subgroup.mem_subgroupOf.mp hx))
    · rintro _ ⟨⟨z, hzM⟩, hz, rfl⟩ _ ⟨⟨r, hrM⟩, hr, rfl⟩
      have := h.mul_comm_of_mem z (Subgroup.mem_subgroupOf.mp hz) r (Subgroup.mem_subgroupOf.mp hr)
      rw [← map_mul, ← map_mul]
      exact congrArg mk (Subtype.ext this)
    · have hRM : R ≤ M := h.pair.le_M
      have h1 : ⁅barM M R, barM M R⁆ = ((⁅R.subgroupOf M, R.subgroupOf M⁆ : Subgroup M)).map mk :=
        (Subgroup.map_commutator _ _ _).symm
      rw [h1]
      rintro _ ⟨⟨z, hzM⟩, hz, rfl⟩
      refine Subgroup.mem_map_of_mem _ ?_
      have hz' : z ∈ (⁅R.subgroupOf M, R.subgroupOf M⁆ : Subgroup M).map M.subtype := by
        rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hRM, h.heis.2.1]
        exact Subgroup.mem_subgroupOf.mp hz
      obtain ⟨w, hw, hwz⟩ := hz'
      exact (Subtype.ext hwz : w = ⟨z, hzM⟩) ▸ hw
    · rintro _ ⟨⟨x, hxM⟩, hx, rfl⟩
      have := hexp x (Subgroup.mem_subgroupOf.mp hx)
      rw [← map_pow]
      exact (congrArg mk (Subtype.ext (by simpa using this))).trans (map_one mk)
    · rintro _ ⟨⟨x, hxM⟩, hx, rfl⟩
      obtain ⟨z, hz, hxz⟩ := hyinv x (Subgroup.mem_subgroupOf.mp hx)
      have hzM : z ∈ M := h.pair.le_M (hZR hz)
      refine ⟨mk ⟨z, hzM⟩, Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hz), ?_⟩
      have h1 : (⟨ι ^ j, hy2M⟩ : M) * ⟨x, hxM⟩ * (⟨ι ^ j, hy2M⟩ : M)⁻¹ =
          (⟨x, hxM⟩ : M)⁻¹ * ⟨z, hzM⟩ := Subtype.ext (by simpa using hxz)
      have h2 := congrArg mk h1
      simpa only [hyb, map_mul, map_inv] using h2
  rintro _ ⟨⟨x, hxM⟩, hx, rfl⟩
  have hxR : x ∈ R := Subgroup.mem_subgroupOf.mp hx
  have hxS : x ∈ Subgroup.normalizer (S : Set G) :=
    (h.pair.inf_eq_inf_normalizer_twoCore ▸ h.pair.R_le_inf hxR).2
  set xb := mk ⟨x, hxM⟩ with hxb
  have hxbp : xb ^ p = 1 := by
    have : (⟨x, hxM⟩ : M) ^ p = 1 := Subtype.ext (by simpa using hexp x hxR)
    rw [hxb, ← map_pow, this, map_one]
  have hsup := hKin (↥M ⧸ CFSG.pCore 2 ↥M) (barM M L) hL.component hcat p hp hp5
    (h.pair.twoGenInner_hyp h85 h93 hD2 hL hP) xb
    (hclosR (Subgroup.mem_map_of_mem _ hx)) ⟨1, by simpa using hxbp⟩
  exact h.pair.mem_centralizer_of_mem_sup h84 h86 hD2 hL hP hsup
    (mem_normalizer_barM hxM hxS) (k := 1) (by simpa using hxbp)

end CFSG.AGLEmbeddingD2
