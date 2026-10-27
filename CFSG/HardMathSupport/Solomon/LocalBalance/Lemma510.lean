module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements2
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma24
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L75X4
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Layer
public import CFSG.LocalAnalysis.GLTheoremB.PCompLift
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

namespace Lemma510Ns

@[expose] def IsL3Type (Y : Type*) [Group Y] : Prop :=
  (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K % 3 = 1 ∧
      (Nonempty (Y ≃* StatedProj (StatedSL 3 K)) ∨ Nonempty (Y ≃* ↥(StatedSL 3 K)))) ∨
    (∃ (K : Type) (_ : Field K) (_ : Finite K) (q : ℕ), Nat.card K = q ^ 2 ∧ q % 3 = 2 ∧
      (Nonempty (Y ≃* StatedProj (StatedSU 3 q K)) ∨ Nonempty (Y ≃* ↥(StatedSU 3 q K))))

@[expose] def Input6_1 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y → IsPGroup 3 (Subgroup.center Y) →
    IsExtremalType (Y ⧸ Subgroup.center Y) → IsExtremalType Y ∨ IsSLThreeEps Y

@[expose] def Input19_1_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Open.IsKProper G → ∀ p : ℕ, p.Prime → ∀ k : ℕ, 1 ≤ k → ∀ D : Subgroup G,
      IsElemAbelian p D → Nat.card D = p ^ k →
      ∀ b ∈ Subgroup.centralizer (D : Set G), b ≠ 1 → b ^ p = 1 →
        (∀ L : Subgroup G, GLAPComponent p (Subgroup.centralizer ({b} : Set G)) L →
          GLADelta p D ⊓ Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (L : Set G)) ∧
        ∀ L : Subgroup G, GLAPComponent p (Subgroup.centralizer ({b} : Set G)) L →
          ¬ ⁅L, GLADelta p D ⊓ Subgroup.centralizer ({b} : Set G)⁆ ≤
              GLAPPrimeCoreOf p (Subgroup.centralizer ({b} : Set G)) →
            D ≤ Subgroup.normalizer (L : Set G) ∧ ¬ IsCompLocallyBalanced p k D L

@[expose] def Input7_L3Aut : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y →
    (IsExtremalType Y ∨ IsSLThreeEps Y) →
    ∀ E : Subgroup (MulAut Y), IsElemAbelian 3 E →
      ∃ F : Subgroup (MulAut Y), F ≤ E ∧ (F.subgroupOf E).index ≤ 9 ∧
        ∀ α ∈ F, IsFieldAutThree α

@[expose] def Input14_5L3 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], ∀ K : Subgroup Y,
    CFSG.Open.IsQuasisimple ↥K → CFSG.Open.IsKGroup ↥K →
    (IsExtremalType ↥K ∨ IsSLThreeEps ↥K) → ∀ x : Y, x ∈ Subgroup.normalizer (K : Set Y) →
      ¬ K ≤ Subgroup.centralizer ({x} : Set Y) → K ≤ Subgroup.centralizer ({x ^ 3} : Set Y) →
        GLAPLayer 3 (K ⊓ Subgroup.centralizer ({x} : Set Y)) = ⊥ ∨
          CFSG.Open.IsQuasisimple ↥(GLAPLayer 3 (K ⊓ Subgroup.centralizer ({x} : Set Y)))

@[expose] def fixSub {Y : Type*} [Group Y] (α : MulAut Y) : Subgroup Y :=
  (α : Y →* Y).eqLocus (MonoidHom.id Y)

theorem mem_fixSub {Y : Type*} [Group Y] {α : MulAut Y} {y : Y} : y ∈ fixSub α ↔ α y = y :=
  Iff.rfl


@[expose] def Gap510_Nontrivial : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y →
    (IsExtremalType Y ∨ IsSLThreeEps Y) → ∀ α : MulAut Y, α ^ 3 = 1 → IsFieldAutThree α →
      GLAPLayer 3 (fixSub α) ≠ ⊥

@[expose] def Gap510_Type : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y →
    (IsExtremalType Y ∨ IsSLThreeEps Y) → ∀ α : MulAut Y, α ^ 3 = 1 → IsFieldAutThree α →
      ∀ J : Subgroup Y, GLAPComponent 3 (fixSub α) J → IsL3Type (barOf 3 J)

@[expose] def Gap510_Centre : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y →
    (IsExtremalType Y ∨ IsSLThreeEps Y) → ∀ α : MulAut Y, α ^ 3 = 1 → IsFieldAutThree α →
      ∀ J : Subgroup Y, GLAPComponent 3 (fixSub α) J →
        Subgroup.center Y ≤ J ∧ J ⊓ oPrimePOf 3 J ≤ Subgroup.center Y

@[expose] def Gap510_Inner : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y →
    (IsExtremalType Y ∨ IsSLThreeEps Y) → ∀ β : MulAut Y, β ^ 3 = 1 →
      ∀ J : Subgroup Y, GLAPComponent 3 (fixSub β) J → IsL3Type (barOf 3 J) → IsFieldAutThree β

section General

variable {G : Type*} [Group G]

theorem mem_oPrimePOf_conj [Finite G] {L : Subgroup G} {l y : G} (hl : l ∈ L)
    (hy : y ∈ oPrimePOf 3 L) : l * y * l⁻¹ ∈ oPrimePOf 3 L := by
  obtain ⟨y', hy', rfl⟩ := hy
  refine ⟨⟨l, hl⟩ * y' * ⟨l, hl⟩⁻¹, (oPrimeP.normal 3 ↥L).conj_mem y' hy' ⟨l, hl⟩, ?_⟩
  simp

theorem exists_isEkIn_of_index_le [Finite G] {B L : Subgroup G} (hB : IsElemAbelian 3 B)
    (hcard : Nat.card B = 3 ^ 4) (hN : B ≤ Subgroup.normalizer (L : Set G))
    {F : Subgroup (MulAut (barOf 3 L))}
    (hidx : (F.subgroupOf (autBar 3 B L)).index ≤ 9) :
    ∃ A : Subgroup G, IsEkIn 3 2 B A ∧ ∀ a ∈ A, ∃ h : a ∈ Subgroup.normalizer (L : Set G),
      barAut 3 L ⟨a, h⟩ ∈ F := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let φ : ↥B →* MulAut (barOf 3 L) := (barAut 3 L).comp (Subgroup.inclusion hN)
  have hrange : φ.range = autBar 3 B L := by
    ext α
    constructor
    · rintro ⟨b, rfl⟩
      refine ⟨⟨(b : G), hN b.2⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      exact ⟨b.2, hN b.2⟩
    · rintro ⟨g, hg, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hg
      exact ⟨⟨(g : G), hg.1⟩, rfl⟩
  set F' : Subgroup ↥B := F.comap φ with hF'
  have hidx' : F'.index ≤ 9 := by
    rw [hF', Subgroup.index_comap, hrange]
    exact hidx
  have hmul := F'.card_mul_index
  rw [hcard] at hmul
  have hdvd : Nat.card F' ∣ 3 ^ 4 := ⟨F'.index, hmul.symm⟩
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have hk2 : 2 ≤ k := by
    by_contra hlt
    push Not at hlt
    have : Nat.card F' ≤ 3 := by
      rw [hk']
      calc 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 3 := by norm_num
    have h81 : 3 ^ 4 = Nat.card F' * F'.index := hmul.symm
    have : 3 ^ 4 ≤ 3 * 9 := by
      rw [h81]
      exact Nat.mul_le_mul this hidx'
    norm_num at this
  have hd9 : 3 ^ 2 ∣ Nat.card F' := by
    rw [hk']
    exact Nat.pow_dvd_pow 3 hk2
  obtain ⟨A'', hA''⟩ := Sylow.exists_subgroup_card_pow_prime 3 hd9
  set A : Subgroup G := (A''.map F'.subtype).map B.subtype with hA
  have hAB : A ≤ B := Subgroup.map_subtype_le _
  refine ⟨A, ⟨hAB, ?_, ?_⟩, ?_⟩
  · exact isElemAbelian_mono hB hAB
  · rw [hA, Subgroup.card_map_of_injective B.subtype_injective,
      Subgroup.card_map_of_injective F'.subtype_injective, hA'']
  · intro a ha
    obtain ⟨b, ⟨f, hf, rfl⟩, rfl⟩ := ha
    exact ⟨hN (f : ↥B).2, f.2⟩

theorem zpowers_cases {r : G} (hr : r ^ 3 = 1) {t : G} (ht : t ∈ Subgroup.zpowers r) :
    t = 1 ∨ t = r ∨ t = r * r := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
  have h1 : r ^ n = r ^ (n % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv n 3, zpow_add, zpow_mul]
    have : r ^ (3 : ℤ) = 1 := by exact_mod_cast hr
    rw [this, one_zpow, mul_one]
  have h2 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h2 with h | h | h
  · left; rw [h1, h]; simp
  · right; left; rw [h1, h]; simp
  · right; right; rw [h1, h]; simp [pow_two]

theorem exists_conj_mem_of_mul [Finite G] {J D : Subgroup G} (hJD : J ≤ Subgroup.normalizer (D : Set G))
    (hD : Nat.Coprime 3 (Nat.card D)) {r j n : G} (hj : j ∈ J) (hn : n ∈ D) (hr : r ^ 3 = 1)
    (hrjn : r = j * n) : ∃ d ∈ D, d * r * d⁻¹ ∈ J := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set T : Subgroup G := Subgroup.zpowers r with hT
  have hTp : IsPGroup 3 T := by
    intro t
    refine ⟨1, ?_⟩
    obtain ⟨t, ht⟩ := t
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
    apply Subtype.ext
    show (r ^ k) ^ (3 ^ 1) = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    have : r ^ (3 : ℤ) = 1 := by exact_mod_cast hr
    simp [this]
  have hnormD : ∀ d ∈ D, j * d * j⁻¹ ∈ D := fun d hd =>
    (Subgroup.mem_normalizer_iff.1 (hJD hj) d).1 hd
  have key : ∀ d ∈ D, ∃ d' ∈ D, ((r * d : G) : G ⧸ J) = ((d' : G) : G ⧸ J) := by
    intro d hd
    refine ⟨j * (n * d) * j⁻¹, hnormD _ (D.mul_mem hn hd), ?_⟩
    rw [QuotientGroup.eq]
    have : (r * d)⁻¹ * (j * (n * d) * j⁻¹) = j⁻¹ := by rw [hrjn]; group
    rw [this]
    exact J.inv_mem hj
  let S : SubMulAction T (G ⧸ J) :=
    { carrier := {c | ∃ d ∈ D, c = ((d : G) : G ⧸ J)}
      smul_mem' := by
        rintro ⟨t, ht⟩ c ⟨d, hd, rfl⟩
        have h1 : ∀ d ∈ D, ∃ d' ∈ D, r • ((d : G) : G ⧸ J) = ((d' : G) : G ⧸ J) := by
          intro d hd
          obtain ⟨d', hd', h⟩ := key d hd
          exact ⟨d', hd', h⟩
        rcases zpowers_cases hr ht with rfl | rfl | rfl
        · exact ⟨d, hd, by simp⟩
        · obtain ⟨d', hd', h⟩ := h1 d hd
          exact ⟨d', hd', h⟩
        · obtain ⟨d', hd', h⟩ := h1 d hd
          obtain ⟨d'', hd'', h'⟩ := h1 d' hd'
          refine ⟨d'', hd'', ?_⟩
          show (r * r) • ((d : G) : G ⧸ J) = _
          rw [mul_smul]
          show r • (r • ((d : G) : G ⧸ J)) = _
          rw [h]; exact h' }
  have hSo : (S : Set (G ⧸ J)) = MulAction.orbit D ((1 : G) : G ⧸ J) := by
    ext c
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact ⟨⟨d, hd⟩, by show ((d * 1 : G) : G ⧸ J) = _; simp⟩
    · rintro ⟨⟨d, hd⟩, rfl⟩
      exact ⟨d, hd, by show ((d * 1 : G) : G ⧸ J) = _; simp⟩
  have hcardS : Nat.card S ∣ Nat.card D := by
    have := Fintype.ofFinite ↥D
    have := Fintype.ofFinite ↥(MulAction.orbit D ((1 : G) : G ⧸ J))
    have h1 := MulAction.card_orbit_mul_card_stabilizer_eq_card_group D ((1 : G) : G ⧸ J)
    have h2 : Nat.card S = Nat.card (MulAction.orbit D ((1 : G) : G ⧸ J)) := by
      have h3 : Nat.card S = Nat.card (S : Set (G ⧸ J)) := Nat.card_congr (Equiv.refl _)
      rw [h3, hSo]
    rw [h2]
    simp only [← Nat.card_eq_fintype_card] at h1
    exact Dvd.intro _ h1
  have hn3 : ¬ 3 ∣ Nat.card S := fun h =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hD (h.trans hcardS)
  have hmod := hTp.card_modEq_card_fixedPoints S
  have hfp : Nonempty (MulAction.fixedPoints T S) := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have h0 : Nat.card (MulAction.fixedPoints T S) = 0 := Nat.card_of_isEmpty
    rw [h0] at hmod
    exact hn3 ((Nat.modEq_zero_iff_dvd).1 hmod)
  obtain ⟨⟨c, hcfix⟩⟩ := hfp
  obtain ⟨d, hd, hcd⟩ := c.2
  have hfixr := hcfix ⟨r, Subgroup.mem_zpowers r⟩
  have h3 : r • ((d : G) : G ⧸ J) = ((d : G) : G ⧸ J) := by
    have := congrArg Subtype.val hfixr
    simpa [hcd] using this
  have h4 : ((r * d : G) : G ⧸ J) = ((d : G) : G ⧸ J) := h3
  rw [QuotientGroup.eq] at h4
  refine ⟨d⁻¹, D.inv_mem hd, ?_⟩
  have h5 : d⁻¹ * r * d⁻¹⁻¹ = ((r * d)⁻¹ * d)⁻¹ := by group
  rw [h5]
  exact J.inv_mem h4

theorem mem_of_le_sSup [Finite G] {p : ℕ} {X L : Subgroup G}
    (hL : GLAPComponent p X L) {𝒮 : Set (Subgroup G)} (h𝒮 : ∀ A ∈ 𝒮, GLAPComponent p X A)
    (hle : L ≤ sSup 𝒮) : L ∈ 𝒮 := by
  by_contra hL𝒮
  have hcomm : ∀ A ∈ 𝒮, ⁅barX p X A, barX p X L⁆ = ⊥ := by
    intro A hA
    have hne : A ≠ L := fun h => hL𝒮 (h ▸ hA)
    have hbar : barX p X A ≠ barX p X L := fun h => hne (glaPComponent_uniqueAux (h𝒮 A hA) hL h)
    exact CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ (h𝒮 A hA).2.2.1 hL.2.2.1 hbar
  have hAX : ∀ A ∈ 𝒮, A ≤ X := fun A hA => (h𝒮 A hA).1
  set T : Subgroup ↥X := ⨆ A ∈ 𝒮, A.subgroupOf X with hT
  have hmapT : T.map X.subtype = sSup 𝒮 := by
    rw [hT, Subgroup.map_iSup, sSup_eq_iSup]
    refine iSup_congr fun A => ?_
    rw [Subgroup.map_iSup]
    refine iSup_congr fun hA => ?_
    exact Subgroup.map_subgroupOf_eq_of_le (hAX A hA)
  have hLT : L.subgroupOf X ≤ T := by
    intro l hl
    have h1 : (l : G) ∈ sSup 𝒮 := hle ((Subgroup.mem_subgroupOf).1 hl)
    rw [← hmapT] at h1
    obtain ⟨t, ht, htl⟩ := h1
    have : t = l := Subtype.ext htl
    exact this ▸ ht
  have hbarle : barX p X L ≤ ⨆ A ∈ 𝒮, barX p X A := by
    have h1 : barX p X L ≤ T.map (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) :=
      Subgroup.map_mono hLT
    refine h1.trans ?_
    rw [hT, Subgroup.map_iSup]
    refine iSup_mono fun A => ?_
    rw [Subgroup.map_iSup]
    exact iSup_mono fun hA => le_rfl
  have hcen : barX p X L ≤ Subgroup.centralizer (barX p X L : Set _) := by
    refine hbarle.trans (iSup₂_le fun A hA => ?_)
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 (hcomm A hA)
  have h0 : ⁅barX p X L, barX p X L⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hcen
  rw [barX_perfect_of_glaPComponent hL] at h0
  have hq : CFSG.Open.IsQuasisimple ↥(barX p X L) := hL.2.2.1.2.2
  have := CFSG.ComponentClassification.Quasisimple.nontrivial hq
  exact (Subgroup.nontrivial_iff_ne_bot _).1 this h0

theorem map_pCore_le_pCore_of_isSubnormal' {H : Type*} [Group H] (p : ℕ) {X Y : Subgroup H}
    (hX : IsSubnormal X Y) : (CFSG.pCore p ↥X).map X.subtype ≤ (CFSG.pCore p ↥Y).map Y.subtype := by
  have key : ∀ {X Y : Subgroup H}, X ≤ Y → Y ≤ Subgroup.normalizer (X : Set H) →
      (CFSG.pCore p X).map X.subtype ≤ (CFSG.pCore p Y).map Y.subtype := by
    intro X Y hXY hYN
    have hLY : (CFSG.pCore p X).map X.subtype ≤ Y := (Subgroup.map_subtype_le _).trans hXY
    have hle : ((CFSG.pCore p X).map X.subtype).subgroupOf Y ≤ CFSG.pCore p Y := by
      apply le_sSup
      refine ⟨⟨fun l hl y => ?_⟩, ?_⟩
      · rw [Subgroup.mem_subgroupOf] at hl ⊢
        have hN := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
          (CFSG.pCore p X) (hYN y.2)
        simpa using (Subgroup.mem_normalizer_iff.mp hN _).mp hl
      · exact (CFSG.pCore_isPGroup.map X.subtype).of_equiv (Subgroup.subgroupOfEquivOfLe hLY).symm
    calc (CFSG.pCore p X).map X.subtype
        = (((CFSG.pCore p X).map X.subtype).subgroupOf Y).map Y.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hLY).symm
      _ ≤ (CFSG.pCore p Y).map Y.subtype := Subgroup.map_mono hle
  induction hX with
  | refl => exact le_rfl
  | step hHM hn _ ih =>
    exact (key hHM ((Subgroup.normal_subgroupOf_iff_le_normalizer hHM).mp hn)).trans ih


theorem oPrimePOf_le_of_glaPComponent [Finite G] {X K : Subgroup G} (hK : GLAPComponent 3 X K) :
    oPrimePOf 3 K ≤ oPrimePOf 3 X := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  rintro y ⟨y', hy', rfl⟩
  have hKX : K ≤ X := hK.1
  have hsn : IsSubnormal K X := hK.2.1
  let e := quotEquivBarX hp hKX hsn
  have hsnb : IsSubnormal (barX 3 X K) ⊤ := hK.2.2.1.2.1
  have h1 : e (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) y') ∈ CFSG.pCore 3 ↥(barX 3 X K) := by
    rw [← CFSG.pCore_map_iso 3 e]
    exact Subgroup.mem_map_of_mem _ hy'
  have h2 := map_pCore_le_pCore_of_isSubnormal' 3 hsnb
  have h3 : ((e (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) y') : ↥(barX 3 X K)) :
      ↥X ⧸ GLAPPrimeCore 3 ↥X) ∈ CFSG.pCore 3 (↥X ⧸ GLAPPrimeCore 3 ↥X) := by
    have h4 := h2 (Subgroup.mem_map_of_mem _ h1)
    have h5 : (CFSG.pCore 3 ↥(⊤ : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X))).map
        (⊤ : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X)).subtype = CFSG.pCore 3 (↥X ⧸ GLAPPrimeCore 3 ↥X) := by
      have := CFSG.pCore_map_iso 3 (Subgroup.topEquiv : (⊤ : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X)) ≃* _)
      rw [← this]
      rfl
    rw [← h5]
    exact h4
  have h6 : ((e (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) y') : ↥(barX 3 X K)) :
      ↥X ⧸ GLAPPrimeCore 3 ↥X) = QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) (Subgroup.inclusion hKX y') :=
    rfl
  rw [h6] at h3
  exact ⟨Subgroup.inclusion hKX y', h3, rfl⟩

theorem pCore_le_center {Y : Type*} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime)
    (hq : CFSG.Open.IsQuasisimple Y) : CFSG.pCore p Y ≤ Subgroup.center Y := by
  have : Fact p.Prime := ⟨hp⟩
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq
      (CFSG.pCore p Y) with h | h
  · exact h
  · exfalso
    have hpg : IsPGroup p (⊤ : Subgroup Y) := h ▸ CFSG.pCore_isPGroup (p := p) (G := Y)
    have := (hpg.of_equiv Subgroup.topEquiv).isNilpotent
    have : Group.IsPerfect Y := ⟨hq.1⟩
    have : Nontrivial Y := CFSG.ComponentClassification.Quasisimple.nontrivial hq
    exact Group.IsPerfect.not_isSolvable Y inferInstance

theorem mem_GLAPPrimeCore_iff {K : Subgroup G} {p : ℕ} (z : ↥K) :
    z ∈ GLAPPrimeCore p ↥K ↔ (z : G) ∈ GLAPPrimeCoreOf p K := by
  constructor
  · intro h; exact ⟨z, h, rfl⟩
  · rintro ⟨z', hz', hzz⟩
    have : z' = z := Subtype.ext hzz
    exact this ▸ hz'

theorem mem_oPrimePOf_of_mem_inf [Finite G] {X L J : Subgroup G} (hL : GLAPComponent 3 X L)
    (hJL : J ≤ L) {y : G} (hyJ : y ∈ J) (hyL : y ∈ oPrimePOf 3 L) : y ∈ oPrimePOf 3 J := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hq : CFSG.Open.IsQuasisimple (barOf 3 L) := isQuasisimple_quotient_of_glaPComponent hL
  obtain ⟨y', hy', hy'y⟩ := hyL
  have hcen : QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) y' ∈ Subgroup.center (barOf 3 L) :=
    pCore_le_center hp hq hy'
  refine ⟨⟨y, hyJ⟩, ?_, rfl⟩
  show QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) ⟨y, hyJ⟩ ∈ CFSG.pCore 3 (↥J ⧸ GLAPPrimeCore 3 ↥J)
  refine mem_pCore_of_forall_comm_aux hp fun w => ?_
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥J) w
  rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  have hwL : (w : G) ∈ L := hJL w.2
  have h1 := Subgroup.mem_center_iff.1 hcen (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) ⟨w, hwL⟩)
  rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq] at h1
  rw [mem_GLAPPrimeCore_iff]
  have h2 := (mem_GLAPPrimeCore_iff _).1 h1
  have h3 : GLAPPrimeCoreOf 3 L ⊓ J ≤ GLAPPrimeCoreOf 3 J := by
    have := gLAPPrimeCoreOf_inf_le hp L J
    rwa [inf_eq_right.2 hJL] at this
  have hc : (((⟨w, hwL⟩ : ↥L) * y')⁻¹ * (y' * ⟨w, hwL⟩) : ↥L) = ⟨(w * y)⁻¹ * (y * w), by
      exact J.mul_mem (J.inv_mem (J.mul_mem w.2 hyJ)) (J.mul_mem hyJ w.2)
        |> fun h => hJL h⟩ := by
    apply Subtype.ext
    simp [← hy'y]
  rw [hc] at h2
  refine h3 ⟨h2, ?_⟩
  exact J.mul_mem (J.inv_mem (J.mul_mem w.2 hyJ)) (J.mul_mem hyJ w.2)


theorem isSLThreeEps_of_mulEquiv {Y Y' : Type*} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : IsSLThreeEps Y) : IsSLThreeEps Y' := by
  rcases h with ⟨K, hK, hf, hc, ⟨f⟩⟩ | ⟨K, hK, hf, q, hc, hq, hq8, ⟨f⟩⟩
  · exact Or.inl ⟨K, hK, hf, hc, ⟨e.symm.trans f⟩⟩
  · exact Or.inr ⟨K, hK, hf, q, hc, hq, hq8, ⟨e.symm.trans f⟩⟩

theorem isExtremalType_of_mulEquiv {Y Y' : Type*} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : IsExtremalType Y) : IsExtremalType Y' := by
  rcases h with ⟨K, hK, hf, hc, ⟨f⟩⟩ | ⟨K, hK, hf, q, hc, hq, hq8, ⟨f⟩⟩
  · exact Or.inl ⟨K, hK, hf, hc, ⟨e.symm.trans f⟩⟩
  · exact Or.inr ⟨K, hK, hf, q, hc, hq, hq8, ⟨e.symm.trans f⟩⟩

theorem glaPComponent_of_normal_sub [Finite G] {p : ℕ} (hp : p.Prime) {Y M J : Subgroup G}
    (hYM : Y ≤ M) (hn : (Y.subgroupOf M).Normal) (hJ : GLAPComponent p Y J) :
    GLAPComponent p M J := by
  obtain ⟨hJY, hsn, hcomp, hmin⟩ := hJ
  have hJM : J ≤ M := hJY.trans hYM
  have hsnM : IsSubnormal J M :=
    isSubnormal_trans' hsn (IsSubnormal.step hYM hn (IsSubnormal.refl M))
  refine ⟨hJM, hsnM, ⟨le_top, ?_, ?_⟩, ?_⟩
  · have := isSubnormal_barX (C := M) p hsnM
    rwa [barX_self] at this
  · have e : ↥(barX p Y J) ≃* ↥(barX p M J) :=
      (quotEquivBarX hp hJY hsn).symm.trans (quotEquivBarX hp hJM hsnM)
    exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e hcomp.2.2
  · intro J' hJ' hJ'sn heq
    have hJ'J : J' ≤ J := hJ'.le
    have hsnY : IsSubnormal J' Y := isSubnormal_of_le_of_le hJ'sn (hJ'J.trans hJY) hYM
    have hcore : J ⊓ GLAPPrimeCoreOf p M ≤ GLAPPrimeCoreOf p Y := by
      rw [glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hsnM]
      exact glaPPrimeCoreOf_le_of_isSubnormal p hsn
    refine hmin J' hJ' hsnY ?_
    show barX p Y J' = barX p Y J
    refine le_antisymm (barX_mono p hJ'J) ?_
    refine barX_le_of_forall (hJ'J.trans hJY) (fun k hk => ?_)
    obtain ⟨j, hj, hjk⟩ := exists_of_barX_le (X := M) (le_of_eq heq.symm) hk (hJM hk)
    exact ⟨j, hj, hcore ⟨J.mul_mem (J.inv_mem (hJ'J hj)) hk, hjk⟩⟩


theorem commutator_mem_core {p : ℕ} {C : Subgroup G} {x y : G} (hx : x ∈ C) (hy : y ∈ C)
    (h : QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨x, hx⟩ * QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨y, hy⟩ =
      QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨y, hy⟩ * QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨x, hx⟩) :
    x⁻¹ * y⁻¹ * x * y ∈ GLAPPrimeCoreOf p C := by
  have hxX : x⁻¹ * y⁻¹ * x * y ∈ C :=
    C.mul_mem (C.mul_mem (C.mul_mem (C.inv_mem hx) (C.inv_mem hy)) hx) hy
  refine ⟨⟨_, hxX⟩, (QuotientGroup.eq_one_iff _).1 ?_, rfl⟩
  have h2 : (⟨x⁻¹ * y⁻¹ * x * y, hxX⟩ : ↥C) = ⟨x, hx⟩⁻¹ * ⟨y, hy⟩⁻¹ * ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
  show QuotientGroup.mk' (GLAPPrimeCore p ↥C) _ = 1
  rw [h2, map_mul, map_mul, map_mul, map_inv, map_inv]
  set a := QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨x, hx⟩
  set b := QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨y, hy⟩
  calc a⁻¹ * b⁻¹ * a * b = (b * a)⁻¹ * (a * b) := by group
    _ = 1 := by rw [← h]; simp

theorem layer_le_normalizer [Finite G] {C L : Subgroup G} (hL : GLAPComponent 3 C L) :
    GLAPLayer 3 C ≤ Subgroup.normalizer (L : Set G) := by
  refine sSup_le fun A hA => ?_
  by_cases hAL : A = L
  · subst hAL; exact Subgroup.le_normalizer
  · have hbar : barX 3 C A ≠ barX 3 C L := fun h => hAL (glaPComponent_uniqueAux hA hL h)
    have hcomm : ⁅barX 3 C A, barX 3 C L⁆ = ⊥ :=
      CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hA.2.2.1 hL.2.2.1 hbar
    have hcen := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
    intro a ha
    have haC : a ∈ C := hA.1 ha
    have key : ∀ l ∈ L, l⁻¹ * a⁻¹ * l * a ∈ GLAPPrimeCoreOf 3 C := by
      intro l hl
      have hlC : l ∈ C := hL.1 hl
      have hlb : QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨l, hlC⟩ ∈ barX 3 C L :=
        ⟨⟨l, hlC⟩, (Subgroup.mem_subgroupOf).2 hl, rfl⟩
      have hab : QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨a, haC⟩ ∈ barX 3 C A :=
        ⟨⟨a, haC⟩, (Subgroup.mem_subgroupOf).2 ha, rfl⟩
      have := Subgroup.mem_centralizer_iff.1 (hcen hab) _ hlb
      exact commutator_mem_core hlC haC this
    rw [mem_normalizer_iff_gLBConj_eq]
    have hcomp' : GLAPComponent 3 C (GLBConj a L) := by
      have := glaPComponent_gLBConj a hL
      rwa [gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer haC)] at this
    refine glaPComponent_uniqueAux hcomp' hL (le_antisymm ?_ ?_)
    · refine barX_le_of_forall hL.1 (fun k hk => ⟨a * k * a⁻¹, mem_gLBConj.1 hk, ?_⟩)
      have := key (a * k * a⁻¹) (mem_gLBConj.1 hk)
      simpa [mul_assoc] using this
    · refine barX_le_of_forall hcomp'.1 (fun l hl => ⟨a⁻¹ * l * a, ?_, ?_⟩)
      · rw [mem_gLBConj]; simpa [mul_assoc] using hl
      · have := (GLAPPrimeCoreOf 3 C).inv_mem (key l hl)
        simpa [mul_assoc] using this

theorem exists_fixed_coset [Finite G] {x : G} (hx : x ^ 3 = 1) {T : Subgroup G}
    (hT : Nat.Coprime 3 (Nat.card T)) (hxT : ∀ t ∈ T, x * t * x⁻¹ ∈ T) {g : G}
    (hg : g⁻¹ * (x * g * x⁻¹) ∈ T) : ∃ t ∈ T, x * (g * t) * x⁻¹ = g * t := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set c : G := g⁻¹ * (x * g * x⁻¹) with hc
  let f : T → T := fun t => ⟨c * (x * t * x⁻¹), T.mul_mem hg (hxT _ t.2)⟩
  have hf : Function.Injective f := by
    intro t t' h
    have h1 : c * (x * (t : G) * x⁻¹) = c * (x * (t' : G) * x⁻¹) := congrArg Subtype.val h
    have h2 := mul_left_cancel h1
    have h3 : (t : G) = t' := mul_left_cancel (mul_right_cancel h2)
    exact Subtype.ext h3
  let τ : Equiv.Perm T := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf)
  have hτ : ∀ t, (τ t : G) = c * (x * t * x⁻¹) := fun t => rfl
  have hτ3 : τ ^ 3 = 1 := by
    ext t
    simp only [pow_succ, pow_zero, one_mul, Equiv.Perm.coe_mul, Function.comp_apply,
      Equiv.Perm.coe_one, id_eq]
    rw [hτ, hτ, hτ]
    have e : c * (x * (c * (x * (c * (x * (t : G) * x⁻¹)) * x⁻¹)) * x⁻¹) =
        (c * (x * c * x⁻¹) * (x ^ 2 * c * (x ^ 2)⁻¹)) * ((x ^ 3) * (t : G) * (x ^ 3)⁻¹) := by
      group
    rw [e, hx]
    have hx' : x * x * x = 1 := by simpa [pow_succ] using hx
    have e2 : c * (x * c * x⁻¹) * (x ^ 2 * c * (x ^ 2)⁻¹) =
        g⁻¹ * (x * x * x) * g * (x * x * x)⁻¹ := by
      simp only [hc]; group
    rw [e2, hx']; simp
  have hP : IsPGroup 3 (Subgroup.zpowers τ) := by
    intro u
    refine ⟨1, ?_⟩
    obtain ⟨u, hu⟩ := u
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    apply Subtype.ext
    show (τ ^ k) ^ (3 ^ 1) = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    have : τ ^ (3 : ℤ) = 1 := by exact_mod_cast hτ3
    simp [this]
  have hmod := hP.card_modEq_card_fixedPoints T
  have hfp : Nonempty (MulAction.fixedPoints (Subgroup.zpowers τ) T) := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have h0 : Nat.card (MulAction.fixedPoints (Subgroup.zpowers τ) T) = 0 := Nat.card_of_isEmpty
    rw [h0] at hmod
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hT ((Nat.modEq_zero_iff_dvd).1 hmod)
  obtain ⟨⟨t, ht⟩⟩ := hfp
  have h1 : τ t = t := ht ⟨τ, Subgroup.mem_zpowers τ⟩
  have h2 : c * (x * (t : G) * x⁻¹) = t := by
    have := congrArg Subtype.val h1
    rw [hτ] at this
    exact this
  refine ⟨t, t.2, ?_⟩
  have h3 : x * g * x⁻¹ = g * c := by simp only [hc]; group
  calc x * (g * (t : G)) * x⁻¹ = (x * g * x⁻¹) * (x * (t : G) * x⁻¹) := by group
    _ = g * (c * (x * (t : G) * x⁻¹)) := by rw [h3]; group
    _ = g * t := by rw [h2]


theorem mem_normalizer_primeCore_of_mem_normalizer [Finite G] {L : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G)) (p : ℕ) :
    x ∈ Subgroup.normalizer (GLAPPrimeCoreOf p L : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq] at hx ⊢
  rw [← glaPPrimeCoreOf_gLBConj, hx]

theorem map_inf_centralizer_eq [Finite G] {X L : Subgroup G} (hLX : L ≤ X) (hsn : IsSubnormal L X)
    {x : G} (hxX : x ∈ X) (hxL : x ∈ Subgroup.normalizer (L : Set G)) (hx3 : x ^ 3 = 1) :
    barX 3 X (L ⊓ Subgroup.centralizer ({x} : Set G)) =
      barX 3 X L ⊓ Subgroup.centralizer
        ({QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨x, hxX⟩} : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  ext z
  rw [Subgroup.mem_inf]
  constructor
  · rintro ⟨a, ha, rfl⟩
    have ha' : (a : G) ∈ L ⊓ Subgroup.centralizer ({x} : Set G) := (Subgroup.mem_subgroupOf).1 ha
    refine ⟨⟨a, (Subgroup.mem_subgroupOf).2 ha'.1, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have := Subgroup.mem_centralizer_singleton_iff.1 ha'.2
    simpa using this
  · rintro ⟨⟨l, hl, rfl⟩, hcen⟩
    have hlL : (l : G) ∈ L := (Subgroup.mem_subgroupOf).1 hl
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, QuotientGroup.mk'_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq] at hcen
    have hc1 : ((l * ⟨x, hxX⟩)⁻¹ * (⟨x, hxX⟩ * l) : ↥X) ∈ GLAPPrimeCore 3 ↥X := hcen
    have hc2 : ((l : G)⁻¹ * (x * l * x⁻¹)) ∈ GLAPPrimeCoreOf 3 X := by
      have h1 : (x⁻¹ * (l : G)⁻¹ * x * l) ∈ GLAPPrimeCoreOf 3 X := ⟨_, hc1, by simp [mul_assoc]⟩
      have h2 := mem_gLAPPrimeCoreOf_conj h1 hxX
      have : x * (x⁻¹ * (l : G)⁻¹ * x * l) * x⁻¹ = (l : G)⁻¹ * (x * l * x⁻¹) := by group
      rwa [this] at h2
    have hc3 : ((l : G)⁻¹ * (x * l * x⁻¹)) ∈ GLAPPrimeCoreOf 3 L := by
      rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hsn]
      refine ⟨?_, hc2⟩
      have h1 := (Subgroup.mem_normalizer_iff.1 hxL (l : G)).1 hlL
      exact L.mul_mem (L.inv_mem hlL) h1
    have hxT : ∀ t ∈ GLAPPrimeCoreOf 3 L, x * t * x⁻¹ ∈ GLAPPrimeCoreOf 3 L := fun t ht =>
      (Subgroup.mem_normalizer_iff.1 (mem_normalizer_primeCore_of_mem_normalizer hxL 3) t).1 ht
    have hTcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCoreOf 3 L)) := by
      have h2 : Nat.card (GLAPPrimeCoreOf 3 L) = Nat.card (GLAPPrimeCore 3 ↥L) :=
        Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
      rw [h2]; exact coprime_card_gLAPPrimeCore_aux 3 ↥L
    obtain ⟨t, ht, hfix⟩ := exists_fixed_coset hx3 hTcop hxT hc3
    have htL : t ∈ L := (CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.GLAPPrimeCoreOf_le 3 L) ht
    have htX : t ∈ GLAPPrimeCoreOf 3 X := glaPPrimeCoreOf_le_of_isSubnormal 3 hsn ht
    have hltX : (l : G) * t ∈ X := X.mul_mem l.2 (hLX htL)
    refine ⟨⟨(l : G) * t, hltX⟩, (Subgroup.mem_subgroupOf).2 ⟨L.mul_mem hlL htL, ?_⟩, ?_⟩
    · show (l : G) * t ∈ Subgroup.centralizer ({x} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have : x * ((l : G) * t) = ((l : G) * t) * x := by
        have := congrArg (· * x) hfix
        simpa [mul_assoc] using this
      exact this.symm
    · rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      have htX' : t ∈ X := (CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.GLAPPrimeCoreOf_le 3 X) htX
      have : (⟨(l : G) * t, hltX⟩⁻¹ * l : ↥X) = ⟨t⁻¹, X.inv_mem htX'⟩ := by
        apply Subtype.ext; simp
      rw [this, mem_GLAPPrimeCore_iff]
      exact (GLAPPrimeCoreOf 3 X).inv_mem htX


theorem eq_of_isSubnormal_of_quasisimple {Y : Type*} [Group Y] {Q J : Subgroup Y}
    (hQ : CFSG.Open.IsQuasisimple ↥Q) (hsn : IsSubnormal J Q) (hperf : ⁅J, J⁆ = J)
    (hJ : J ≠ ⊥) : J = Q := by
  set Z : Subgroup Y := (Subgroup.center ↥Q).map Q.subtype with hZ
  have key : ∀ {A B : Subgroup Y}, IsSubnormal A B → B = Q → A ≤ Z ∨ A = Q := by
    intro A B h
    induction h with
    | refl => intro hB; right; exact hB
    | step hHM hn hMK ih =>
      rename_i H M K
      intro hK
      rcases ih hK with hMZ | hMQ
      · left; exact hHM.trans hMZ
      · subst hMQ
        have hHQ : H ≤ M := hHM
        have hnorm : (H.subgroupOf M).Normal := hn
        rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hQ
          (H.subgroupOf M) with hc | hc
        · left
          intro h hh
          have := hc (show (⟨h, hHQ hh⟩ : ↥M) ∈ H.subgroupOf M from hh)
          exact ⟨⟨h, hHQ hh⟩, this, rfl⟩
        · right
          refine le_antisymm hHQ fun m hm => ?_
          have : (⟨m, hm⟩ : ↥M) ∈ H.subgroupOf M := by rw [hc]; trivial
          exact (Subgroup.mem_subgroupOf).1 this
  rcases key hsn rfl with hJZ | hJQ
  · exfalso
    apply hJ
    rw [eq_bot_iff, ← hperf]
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    obtain ⟨a', ha', rfl⟩ := hJZ ha
    obtain ⟨b', hb', rfl⟩ := hJZ hb
    have : a' * b' = b' * a' := (Subgroup.mem_center_iff.1 ha' b').symm
    rw [Subgroup.mem_bot]
    show (a' : Y) * b' * (a' : Y)⁻¹ * (b' : Y)⁻¹ = 1
    have h2 : (a' : Y) * b' = b' * a' := congrArg Subtype.val this
    rw [h2]; group
  · exact hJQ



theorem glaPComponent_ne_bot {G : Type*} [Group G] {p : ℕ} {X J : Subgroup G} (hJ : GLAPComponent p X J) :
    J ≠ ⊥ := by
  intro h
  have hq := hJ.2.2.1.2.2
  change CFSG.Open.IsQuasisimple ↥((J.subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p X)))
    at hq
  rw [h, Subgroup.bot_subgroupOf, Subgroup.map_bot] at hq
  exact (Subgroup.nontrivial_iff_ne_bot _).1
    (CFSG.ComponentClassification.Quasisimple.nontrivial hq) rfl

theorem normalizerMonoidHom_coe (L : Subgroup G) (γ : ↥(Subgroup.normalizer (L : Set G))) (l : ↥L) :
    (L.normalizerMonoidHom γ l : G) = (γ : G) * l * (γ : G)⁻¹ := rfl

theorem map_inf_centralizer_eq_fixSub [Finite G] {L : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G)) (hx3 : x ^ 3 = 1) :
    ((L ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf L).map
        (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)) = fixSub (barAut 3 L ⟨x, hx⟩) := by
  ext y
  constructor
  · rintro ⟨a, ha, rfl⟩
    have ha' : (a : G) ∈ L ⊓ Subgroup.centralizer ({x} : Set G) := (Subgroup.mem_subgroupOf).1 ha
    show barAut 3 L ⟨x, hx⟩ (QuotientGroup.mk a) = QuotientGroup.mk a
    rw [barAut_mk]
    congr 1
    apply Subtype.ext
    have := Subgroup.mem_centralizer_singleton_iff.1 ha'.2
    show x * (a : G) * x⁻¹ = a
    rw [this.symm]; group
  · intro hy
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
    have hy' : barAut 3 L ⟨x, hx⟩ (QuotientGroup.mk l) = QuotientGroup.mk l := hy
    rw [barAut_mk, QuotientGroup.eq] at hy'
    have hc : (l : G)⁻¹ * (x * l * x⁻¹) ∈ GLAPPrimeCoreOf 3 L := by
      have h1 := (mem_GLAPPrimeCore_iff _).1 hy'
      have h2 : (l : G)⁻¹ * (x * l * x⁻¹) =
          ((((L.normalizerMonoidHom ⟨x, hx⟩ l)⁻¹ * l : ↥L) : G))⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, normalizerMonoidHom_coe]
        group
      rw [h2]
      exact (GLAPPrimeCoreOf 3 L).inv_mem h1
    have hxT : ∀ t ∈ GLAPPrimeCoreOf 3 L, x * t * x⁻¹ ∈ GLAPPrimeCoreOf 3 L := fun t ht =>
      (Subgroup.mem_normalizer_iff.1 (mem_normalizer_primeCore_of_mem_normalizer hx 3) t).1 ht
    have hTcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCoreOf 3 L)) := by
      have h2 : Nat.card (GLAPPrimeCoreOf 3 L) = Nat.card (GLAPPrimeCore 3 ↥L) :=
        Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
      rw [h2]; exact coprime_card_gLAPPrimeCore_aux 3 ↥L
    obtain ⟨t, ht, hfix⟩ := exists_fixed_coset hx3 hTcop hxT hc
    have htL : t ∈ L := (CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.GLAPPrimeCoreOf_le 3 L) ht
    refine ⟨⟨(l : G) * t, L.mul_mem l.2 htL⟩, (Subgroup.mem_subgroupOf).2
      ⟨L.mul_mem l.2 htL, ?_⟩, ?_⟩
    · show (l : G) * t ∈ Subgroup.centralizer ({x} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have : x * ((l : G) * t) = ((l : G) * t) * x := by
        have := congrArg (· * x) hfix
        simpa [mul_assoc] using this
      exact this.symm
    · show QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) _ = QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) l
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      have : (⟨(l : G) * t, L.mul_mem l.2 htL⟩⁻¹ * l : ↥L) = ⟨t⁻¹, L.inv_mem htL⟩ := by
        apply Subtype.ext; simp
      rw [this, mem_GLAPPrimeCore_iff]
      exact (GLAPPrimeCoreOf 3 L).inv_mem ht


end General

section Lift

variable {G : Type} [Group G] [Finite G]

theorem isL3Type_of_mulEquiv {Y Y' : Type*} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : IsL3Type Y) : IsL3Type Y' := by
  rcases h with ⟨K, hK, hf, hc, h⟩ | ⟨K, hK, hf, q, hc, hq, h⟩
  · refine Or.inl ⟨K, hK, hf, hc, ?_⟩
    rcases h with h | h
    · obtain ⟨f⟩ := h; exact Or.inl ⟨e.symm.trans f⟩
    · obtain ⟨f⟩ := h; exact Or.inr ⟨e.symm.trans f⟩
  · refine Or.inr ⟨K, hK, hf, q, hc, hq, ?_⟩
    rcases h with h | h
    · obtain ⟨f⟩ := h; exact Or.inl ⟨e.symm.trans f⟩
    · obtain ⟨f⟩ := h; exact Or.inr ⟨e.symm.trans f⟩


omit [Finite G] in
theorem coprime_ker_subtype (L : Subgroup G) (A : Subgroup ↥L) :
    Nat.Coprime 3 (Nat.card ↥(A ⊓ (L.subtype).ker)) := by
  rw [Subgroup.ker_subtype, inf_bot_eq, Subgroup.card_bot]; exact Nat.coprime_one_right _

theorem coprime_ker_mk (L : Subgroup G) (A : Subgroup ↥L) :
    Nat.Coprime 3 (Nat.card ↥(A ⊓ (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)).ker)) := by
  have h1 : Nat.card ↥(A ⊓ (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)).ker) ∣
      Nat.card (GLAPPrimeCore 3 ↥L) := by
    have hker : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)).ker = GLAPPrimeCore 3 ↥L :=
      QuotientGroup.ker_mk' _
    have h2 : Nat.card ↥(QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)).ker =
        Nat.card (GLAPPrimeCore 3 ↥L) := by rw [hker]
    rw [← h2]
    exact Subgroup.card_dvd_of_le inf_le_right
  exact (coprime_card_gLAPPrimeCore_aux 3 ↥L).coprime_dvd_right h1

theorem exists_comp_subgroupOf {L S J : Subgroup G} (hSL : S ≤ L) (hJ : GLAPComponent 3 S J) :
    ∃ J₁ : Subgroup ↥L, GLAPComponent 3 (S.subgroupOf L) J₁ ∧ J₁.map L.subtype = J := by
  have hAmap : (S.subgroupOf L).map L.subtype = S := Subgroup.map_subgroupOf_eq_of_le hSL
  exact exists_glaPComponent_map_eq Nat.prime_three L.subtype (coprime_ker_subtype L _)
    (show GLAPComponent 3 ((S.subgroupOf L).map L.subtype) J by rw [hAmap]; exact hJ)

theorem comp_map_subgroupOf {L S : Subgroup G} (hSL : S ≤ L) {J₁ : Subgroup ↥L}
    (hJ₁ : GLAPComponent 3 (S.subgroupOf L) J₁) : GLAPComponent 3 S (J₁.map L.subtype) := by
  have hAmap : (S.subgroupOf L).map L.subtype = S := Subgroup.map_subgroupOf_eq_of_le hSL
  have := glaPComponent_map Nat.prime_three L.subtype (coprime_ker_subtype L _) hJ₁
  rwa [hAmap] at this

theorem comp_map_fixSub {L : Subgroup G} {x : G} (hx : x ∈ Subgroup.normalizer (L : Set G))
    (hx3 : x ^ 3 = 1) {J₁ : Subgroup ↥L}
    (hJ₁ : GLAPComponent 3 ((L ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf L) J₁) :
    GLAPComponent 3 (fixSub (barAut 3 L ⟨x, hx⟩)) (J₁.map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L))) := by
  have := glaPComponent_map Nat.prime_three (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L))
    (coprime_ker_mk L _) hJ₁
  rwa [map_inf_centralizer_eq_fixSub hx hx3] at this

theorem exists_comp_of_fixSub {L : Subgroup G} {x : G} (hx : x ∈ Subgroup.normalizer (L : Set G))
    (hx3 : x ^ 3 = 1) {J : Subgroup (barOf 3 L)}
    (hJ : GLAPComponent 3 (fixSub (barAut 3 L ⟨x, hx⟩)) J) :
    ∃ J₁ : Subgroup ↥L,
      GLAPComponent 3 ((L ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf L) J₁ ∧
        J₁.map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)) = J := by
  rw [← map_inf_centralizer_eq_fixSub hx hx3] at hJ
  exact exists_glaPComponent_map_eq Nat.prime_three _ (coprime_ker_mk L _) hJ

noncomputable def liftEquiv {L : Subgroup G} (J₁ : Subgroup ↥L) :
    barOf 3 (J₁.map L.subtype) ≃* barOf 3 (J₁.map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L))) :=
  (lcEquiv Nat.prime_three L.subtype J₁ (coprime_ker_subtype L J₁)).symm.trans
    (lcEquiv Nat.prime_three (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)) J₁ (coprime_ker_mk L J₁))

theorem liftEquiv_apply {L : Subgroup G} (J₁ : Subgroup ↥L) (j : ↥L) (hj : j ∈ J₁) :
    liftEquiv J₁ (QuotientGroup.mk ⟨(j : G), ⟨j, hj, rfl⟩⟩) =
      QuotientGroup.mk ⟨QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) j, ⟨j, hj, rfl⟩⟩ := by
  unfold liftEquiv
  rw [MulEquiv.trans_apply]
  have h1 : (lcEquiv Nat.prime_three L.subtype J₁ (coprime_ker_subtype L J₁)).symm
      (QuotientGroup.mk ⟨(j : G), ⟨j, hj, rfl⟩⟩) = QuotientGroup.mk ⟨j, hj⟩ := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [h1]
  rfl


omit [Finite G] in
theorem barAut_pow_three {L : Subgroup G} {x : G} (hx : x ∈ Subgroup.normalizer (L : Set G))
    (hx3 : x ^ 3 = 1) : (barAut 3 L ⟨x, hx⟩) ^ 3 = 1 := by
  rw [← map_pow]
  have : (⟨x, hx⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
  rw [this, map_one]

theorem amb_nontrivial (g : Gap510_Nontrivial) {X L : Subgroup G} (hL : GLAPComponent 3 X L)
    (hty : IsExtremalType (barOf 3 L) ∨ IsSLThreeEps (barOf 3 L)) {x : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G)) (hx3 : x ^ 3 = 1)
    (hfld : IsFieldAutThree (barAut 3 L ⟨x, hx⟩)) :
    GLAPLayer 3 (L ⊓ Subgroup.centralizer ({x} : Set G)) ≠ ⊥ := by
  have hq : CFSG.Open.IsQuasisimple (barOf 3 L) := isQuasisimple_quotient_of_glaPComponent hL
  have hne := g (barOf 3 L) hq hty _ (barAut_pow_three hx hx3) hfld
  obtain ⟨J, hJ⟩ : ∃ J : Subgroup (barOf 3 L), GLAPComponent 3 (fixSub (barAut 3 L ⟨x, hx⟩)) J := by
    by_contra hno
    push Not at hno
    apply hne
    have : {J : Subgroup (barOf 3 L) | GLAPComponent 3 (fixSub (barAut 3 L ⟨x, hx⟩)) J} = ∅ :=
      Set.eq_empty_of_forall_notMem hno
    show sSup {J : Subgroup (barOf 3 L) | GLAPComponent 3 (fixSub (barAut 3 L ⟨x, hx⟩)) J} = ⊥
    rw [this, sSup_empty]
  obtain ⟨J₁, hJ₁, -⟩ := exists_comp_of_fixSub hx hx3 hJ
  have hJc := comp_map_subgroupOf (inf_le_left : L ⊓ Subgroup.centralizer ({x} : Set G) ≤ L) hJ₁
  intro hbot
  have : J₁.map L.subtype ≤ GLAPLayer 3 (L ⊓ Subgroup.centralizer ({x} : Set G)) := le_sSup hJc
  rw [hbot, le_bot_iff] at this
  exact glaPComponent_ne_bot hJc this

theorem amb_type (g : Gap510_Type) {X L : Subgroup G} (hL : GLAPComponent 3 X L)
    (hty : IsExtremalType (barOf 3 L) ∨ IsSLThreeEps (barOf 3 L)) {x : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G)) (hx3 : x ^ 3 = 1)
    (hfld : IsFieldAutThree (barAut 3 L ⟨x, hx⟩)) {J : Subgroup G}
    (hJ : GLAPComponent 3 (L ⊓ Subgroup.centralizer ({x} : Set G)) J) : IsL3Type (barOf 3 J) := by
  have hq : CFSG.Open.IsQuasisimple (barOf 3 L) := isQuasisimple_quotient_of_glaPComponent hL
  obtain ⟨J₁, hJ₁, rfl⟩ := exists_comp_subgroupOf (inf_le_left : L ⊓ Subgroup.centralizer ({x} : Set G) ≤ L) hJ
  have hc := comp_map_fixSub hx hx3 hJ₁
  have := g (barOf 3 L) hq hty _ (barAut_pow_three hx hx3) hfld _ hc
  exact isL3Type_of_mulEquiv (liftEquiv J₁).symm this


theorem amb_centre (g : Gap510_Centre) {X L : Subgroup G} (hL : GLAPComponent 3 X L)
    (hty : IsExtremalType (barOf 3 L) ∨ IsSLThreeEps (barOf 3 L)) {x : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G)) (hx3 : x ^ 3 = 1)
    (hfld : IsFieldAutThree (barAut 3 L ⟨x, hx⟩)) {J : Subgroup G}
    (hJ : GLAPComponent 3 (L ⊓ Subgroup.centralizer ({x} : Set G)) J) :
    (∀ r ∈ L ⊓ Subgroup.centralizer ({x} : Set G), r ∈ oPrimePOf 3 L →
        ∃ j ∈ J, ∃ n ∈ GLAPPrimeCoreOf 3 L ⊓ Subgroup.centralizer ({x} : Set G), r = j * n) ∧
      J ⊓ oPrimePOf 3 J ≤ oPrimePOf 3 L := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hq : CFSG.Open.IsQuasisimple (barOf 3 L) := isQuasisimple_quotient_of_glaPComponent hL
  have hJle : J ≤ L ⊓ Subgroup.centralizer ({x} : Set G) := hJ.1
  obtain ⟨J₁, hJ₁, rfl⟩ := exists_comp_subgroupOf
    (inf_le_left : L ⊓ Subgroup.centralizer ({x} : Set G) ≤ L) hJ
  have hc := comp_map_fixSub hx hx3 hJ₁
  obtain ⟨hZ1, hZ2⟩ := g (barOf 3 L) hq hty _ (barAut_pow_three hx hx3) hfld _ hc
  refine ⟨?_, ?_⟩
  · rintro r hr ⟨y, hy, rfl⟩
    have hmem : QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) y ∈ Subgroup.center (barOf 3 L) :=
      pCore_le_center hp hq hy
    obtain ⟨j₁, hj₁, hjy⟩ := hZ1 hmem
    have hn : j₁⁻¹ * y ∈ GLAPPrimeCore 3 ↥L := by
      have := QuotientGroup.eq.1 (show QuotientGroup.mk j₁ = QuotientGroup.mk y from hjy)
      exact this
    have hjC : (j₁ : G) ∈ Subgroup.centralizer ({x} : Set G) :=
      (hJle ⟨j₁, hj₁, rfl⟩).2
    refine ⟨(j₁ : G), ⟨j₁, hj₁, rfl⟩, ((j₁⁻¹ * y : ↥L) : G), ⟨?_, ?_⟩, ?_⟩
    · exact (mem_GLAPPrimeCore_iff _).1 hn
    · have h2 : ((j₁⁻¹ * y : ↥L) : G) = (j₁ : G)⁻¹ * y := rfl
      rw [h2]
      exact (Subgroup.centralizer ({x} : Set G)).mul_mem
        ((Subgroup.centralizer ({x} : Set G)).inv_mem hjC) hr.2
    · simp
  · rintro j ⟨hjJ, hjO⟩
    obtain ⟨j₁, hj₁, rfl⟩ := hjJ
    obtain ⟨z, hz, hzj⟩ := hjO
    have hzeq : z = ⟨(j₁ : G), ⟨j₁, hj₁, rfl⟩⟩ := Subtype.ext hzj
    subst hzeq
    have h1 : liftEquiv J₁ (QuotientGroup.mk' (GLAPPrimeCore 3 ↥(J₁.map L.subtype))
        ⟨(j₁ : G), ⟨j₁, hj₁, rfl⟩⟩) ∈
        CFSG.pCore 3 (barOf 3 (J₁.map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)))) := by
      rw [← CFSG.pCore_map_iso 3 (liftEquiv J₁)]
      exact Subgroup.mem_map_of_mem _ hz
    rw [QuotientGroup.mk'_apply, liftEquiv_apply J₁ j₁ hj₁] at h1
    have h2 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) j₁ ∈ Subgroup.center (barOf 3 L) :=
      (hZ2 ⟨⟨j₁, hj₁, rfl⟩, ⟨_, h1, rfl⟩⟩)
    have h3 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) j₁ ∈ CFSG.pCore 3 (barOf 3 L) := by
      refine mem_pCore_of_forall_comm_aux hp fun w => ?_
      exact Subgroup.mem_center_iff.1 h2 w
    exact ⟨j₁, h3, rfl⟩

theorem amb_inner (g : Gap510_Inner) {X K : Subgroup G} (hK : GLAPComponent 3 X K)
    (hty : IsExtremalType (barOf 3 K) ∨ IsSLThreeEps (barOf 3 K)) {b : G}
    (hb : b ∈ Subgroup.normalizer (K : Set G)) (hb3 : b ^ 3 = 1) {J : Subgroup G}
    (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({b} : Set G)) J)
    (hJt : IsL3Type (barOf 3 J)) : InducesFieldAut 3 K b := by
  have hq : CFSG.Open.IsQuasisimple (barOf 3 K) := isQuasisimple_quotient_of_glaPComponent hK
  obtain ⟨J₁, hJ₁, rfl⟩ := exists_comp_subgroupOf
    (inf_le_left : K ⊓ Subgroup.centralizer ({b} : Set G) ≤ K) hJ
  have hc := comp_map_fixSub hb hb3 hJ₁
  exact ⟨hb, g (barOf 3 K) hq hty _ (barAut_pow_three hb hb3) _ hc
    (isL3Type_of_mulEquiv (liftEquiv J₁) hJt)⟩

end Lift

section Typed

variable {G : Type} [Group G] [Finite G]

theorem eq_of_glaPComponent_inf_centralizer
    (i145 : Input14_5L3) {X L : Subgroup G}
    (hty : IsExtremalType (barOf 3 L) ∨ IsSLThreeEps (barOf 3 L))
    (hNK : CFSG.Open.IsKGroup ↥(Subgroup.normalizer (L : Set G)))
    (hL : GLAPComponent 3 X L) {x : G} (hxN : x ∈ Subgroup.normalizer (L : Set G)) (hx3 : x ^ 3 = 1)
    {J J' : Subgroup G} (hJ : GLAPComponent 3 (L ⊓ Subgroup.centralizer ({x} : Set G)) J)
    (hJ' : GLAPComponent 3 (L ⊓ Subgroup.centralizer ({x} : Set G)) J') : J = J' := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  set N : Subgroup G := Subgroup.normalizer (L : Set G) with hN
  have hLN : L ≤ N := Subgroup.le_normalizer
  have hLnorm : (L.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLN).2 le_rfl
  have hLcomp : GLAPComponent 3 N L :=
    glaPComponent_of_normal_sub hp hLN hLnorm (glaPComponent_of_le hp hL le_rfl hL.1)
  have hsnLN : IsSubnormal L N := hLcomp.2.1
  have hxN' : x ∈ N := hxN
  set ψ : ↥N →* (↥N ⧸ GLAPPrimeCore 3 ↥N) := QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) with hψ
  set K'' : Subgroup (↥N ⧸ GLAPPrimeCore 3 ↥N) := barX 3 N L with hK''
  set x' : ↥N ⧸ GLAPPrimeCore 3 ↥N := ψ ⟨x, hxN'⟩ with hx'
  have hq : CFSG.Open.IsQuasisimple ↥K'' := hLcomp.2.2.1.2.2
  have hKg : CFSG.Open.IsKGroup ↥K'' := isKGroup_subgroup' (isKGroup_quotient' hNK _) K''
  have hKty : IsExtremalType ↥K'' ∨ IsSLThreeEps ↥K'' := by
    have e := quotEquivBarX hp hLN hsnLN
    rcases hty with h | h
    · exact Or.inl (isExtremalType_of_mulEquiv e h)
    · exact Or.inr (isSLThreeEps_of_mulEquiv e h)
  have hx'N : x' ∈ Subgroup.normalizer (K'' : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)) := by
    refine Subgroup.mem_normalizer_fintype fun k hk => ?_
    obtain ⟨l, hl, rfl⟩ := hk
    refine ⟨⟨x, hxN'⟩ * l * ⟨x, hxN'⟩⁻¹, ?_, by simp [hx', hψ]⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hl ⊢
    have := (Subgroup.mem_normalizer_iff.1 hxN (l : G)).1 hl
    simpa using this
  have hx'3 : x' ^ 3 = 1 := by
    rw [hx', ← map_pow]
    have : (⟨x, hxN'⟩ : ↥N) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [this, map_one]
  have hmap : barX 3 N (L ⊓ Subgroup.centralizer ({x} : Set G)) =
      K'' ⊓ Subgroup.centralizer ({x'} : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)) :=
    map_inf_centralizer_eq hLN hsnLN hxN' hxN hx3
  have huniq : ∀ J₁ J₂ : Subgroup (↥N ⧸ GLAPPrimeCore 3 ↥N),
      GLAPComponent 3 (K'' ⊓ Subgroup.centralizer ({x'} : Set (↥N ⧸ GLAPPrimeCore 3 ↥N))) J₁ →
      GLAPComponent 3 (K'' ⊓ Subgroup.centralizer ({x'} : Set (↥N ⧸ GLAPPrimeCore 3 ↥N))) J₂ →
      J₁ = J₂ := by
    intro J₁ J₂ h₁ h₂
    by_cases hK : K'' ≤ Subgroup.centralizer ({x'} : Set (↥N ⧸ GLAPPrimeCore 3 ↥N))
    · have hĈ : K'' ⊓ Subgroup.centralizer ({x'} : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)) = K'' :=
        inf_eq_left.2 hK
      rw [hĈ] at h₁ h₂
      rw [eq_of_isSubnormal_of_quasisimple hq h₁.2.1 (glaPComponent_perfect h₁)
        (glaPComponent_ne_bot h₁),
        eq_of_isSubnormal_of_quasisimple hq h₂.2.1 (glaPComponent_perfect h₂)
        (glaPComponent_ne_bot h₂)]
    · have hx'p : K'' ≤ Subgroup.centralizer ({x' ^ 3} : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)) := by
        rw [hx'3]
        intro k _
        rw [Subgroup.mem_centralizer_singleton_iff]; simp
      rcases i145 _ K'' hq hKg hKty x' hx'N hK hx'p with hbot | hQ
      · exfalso
        have : J₁ ≤ GLAPLayer 3 (K'' ⊓ Subgroup.centralizer ({x'} : Set (↥N ⧸ GLAPPrimeCore 3 ↥N))) :=
          le_sSup h₁
        rw [hbot, le_bot_iff] at this
        exact glaPComponent_ne_bot h₁ this
      · set Ĉ := K'' ⊓ Subgroup.centralizer ({x'} : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)) with hĈ
        have hJQ : ∀ J₁ : Subgroup (↥N ⧸ GLAPPrimeCore 3 ↥N), GLAPComponent 3 Ĉ J₁ →
            J₁ = GLAPLayer 3 Ĉ := by
          intro J₁ h₁
          have hle : J₁ ≤ GLAPLayer 3 Ĉ := le_sSup h₁
          have hQC : GLAPLayer 3 Ĉ ≤ Ĉ := sSup_le fun A hA => hA.1
          exact eq_of_isSubnormal_of_quasisimple hQ (isSubnormal_of_le_of_le h₁.2.1 hle hQC)
            (glaPComponent_perfect h₁) (glaPComponent_ne_bot h₁)
        rw [hJQ J₁ h₁, hJQ J₂ h₂]
  set A : Subgroup ↥N := (L ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf N with hA
  have hLxN : L ⊓ Subgroup.centralizer ({x} : Set G) ≤ N := inf_le_left.trans hLN
  have hAmap : A.map N.subtype = L ⊓ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.map_subgroupOf_eq_of_le hLxN
  have hkerN : Nat.Coprime 3 (Nat.card ↥(A ⊓ (N.subtype).ker)) := by
    rw [Subgroup.ker_subtype, inf_bot_eq, Subgroup.card_bot]; exact Nat.coprime_one_right _
  have hkerψ : Nat.Coprime 3 (Nat.card ↥(A ⊓ ψ.ker)) := by
    have h1 : Nat.card ↥(A ⊓ ψ.ker) ∣ Nat.card (GLAPPrimeCore 3 ↥N) := by
      have hker : ψ.ker = GLAPPrimeCore 3 ↥N := QuotientGroup.ker_mk' _
      have h2 : Nat.card ↥ψ.ker = Nat.card (GLAPPrimeCore 3 ↥N) := by rw [hker]
      rw [← h2]
      exact Subgroup.card_dvd_of_le inf_le_right
    exact (coprime_card_gLAPPrimeCore_aux 3 ↥N).coprime_dvd_right h1
  have hApsi : A.map ψ = K'' ⊓ Subgroup.centralizer ({x'} : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)) :=
    hmap
  obtain ⟨J₁, hJ₁, hJ₁m⟩ := exists_glaPComponent_map_eq hp N.subtype hkerN (K' := J) (hAmap ▸ hJ)
  obtain ⟨J₂, hJ₂, hJ₂m⟩ := exists_glaPComponent_map_eq hp N.subtype hkerN (K' := J') (hAmap ▸ hJ')
  have hc₁ : GLAPComponent 3 (K'' ⊓ Subgroup.centralizer ({x'} : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)))
      (J₁.map ψ) := hApsi ▸ glaPComponent_map hp ψ hkerψ hJ₁
  have hc₂ : GLAPComponent 3 (K'' ⊓ Subgroup.centralizer ({x'} : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)))
      (J₂.map ψ) := hApsi ▸ glaPComponent_map hp ψ hkerψ hJ₂
  have himg : J₁.map ψ = J₂.map ψ := huniq _ _ hc₁ hc₂
  have hb₁ := lcEquiv_barX hp ψ A hkerψ hJ₁.1
  have hb₂ := lcEquiv_barX hp ψ A hkerψ hJ₂.1
  have hbar : barX 3 A J₁ = barX 3 A J₂ := by
    apply Subgroup.map_injective (lcEquiv hp ψ A hkerψ).injective
    show (barX 3 A J₁).map (lcMonoidHom hp ψ A hkerψ) = (barX 3 A J₂).map (lcMonoidHom hp ψ A hkerψ)
    rw [hb₁, hb₂, himg]
  have hJ₁₂ : J₁ = J₂ := glaPComponent_uniqueAux hJ₁ hJ₂ hbar
  rw [← hJ₁m, ← hJ₂m, hJ₁₂]

theorem type_of_ext_quot (h61 : Input6_1) {X L : Subgroup G}
    (hL : GLAPComponent 3 X L) (h : IsExtremalType (↥L ⧸ oPrimeP 3 ↥L)) :
    IsExtremalType (barOf 3 L) ∨ IsSLThreeEps (barOf 3 L) := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hq : CFSG.Open.IsQuasisimple (barOf 3 L) := isQuasisimple_quotient_of_glaPComponent hL
  have hZeq : Subgroup.center (barOf 3 L) = CFSG.pCore 3 (barOf 3 L) := by
    refine le_antisymm ?_ (pCore_le_center hp hq)
    intro z hz
    refine mem_pCore_of_forall_comm_aux hp fun w => ?_
    exact (Subgroup.mem_center_iff.1 hz w)
  have hZp : IsPGroup 3 (Subgroup.center (barOf 3 L)) := by
    rw [hZeq]; exact CFSG.pCore_isPGroup
  have hle : GLAPPrimeCore 3 ↥L ≤ oPrimeP 3 ↥L := by
    intro l hl
    show QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) l ∈ CFSG.pCore 3 (barOf 3 L)
    rw [(QuotientGroup.eq_one_iff l).2 hl |> fun h => show QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) l = 1 from h]
    exact Subgroup.one_mem _
  have e1 := QuotientGroup.quotientQuotientEquivQuotient (GLAPPrimeCore 3 ↥L) (oPrimeP 3 ↥L) hle
  have hmap : (oPrimeP 3 ↥L).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)) =
      Subgroup.center (barOf 3 L) := by
    rw [hZeq]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  have e2 : (barOf 3 L ⧸ Subgroup.center (barOf 3 L)) ≃* (↥L ⧸ oPrimeP 3 ↥L) :=
    (QuotientGroup.quotientMulEquivOfEq hmap.symm).trans e1
  have hext : IsExtremalType (barOf 3 L ⧸ Subgroup.center (barOf 3 L)) :=
    isExtremalType_of_mulEquiv e2.symm h
  exact h61 (barOf 3 L) hq hZp hext

theorem glaPComponent_inf_centralizer {C L : Subgroup G} (hL : GLAPComponent 3 C L)
    (x : G) {J : Subgroup G} (hJ : GLAPComponent 3 (L ⊓ Subgroup.centralizer ({x} : Set G)) J) :
    GLAPComponent 3 (C ⊓ Subgroup.centralizer ({x} : Set G)) J := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  set Cx : Subgroup G := Subgroup.centralizer ({x} : Set G) with hCx
  set Λ : Subgroup G := GLAPLayer 3 C with hΛ
  have hLΛ : L ≤ Λ := le_sSup hL
  have hΛC : Λ ≤ C := sSup_le fun A hA => hA.1
  have hLN : Λ ≤ Subgroup.normalizer (L : Set G) := layer_le_normalizer hL
  have hCN : C ≤ Subgroup.normalizer (Λ : Set G) := UniquenessMaximal.Sec7.le_normalizer_glaPLayer 3 C
  have h1 : ((L ⊓ Cx).subgroupOf (Λ ⊓ Cx)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_inf_right _ hLΛ)]
    intro g hg
    refine Subgroup.mem_normalizer_fintype fun n hn => ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.1 (hLN hg.1) n).1 hn.1
    · exact Cx.mul_mem (Cx.mul_mem hg.2 hn.2) (Cx.inv_mem hg.2)
  have h2 : ((Λ ⊓ Cx).subgroupOf (C ⊓ Cx)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_inf_right _ hΛC)]
    intro g hg
    refine Subgroup.mem_normalizer_fintype fun n hn => ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.1 (hCN hg.1) n).1 hn.1
    · exact Cx.mul_mem (Cx.mul_mem hg.2 hn.2) (Cx.inv_mem hg.2)
  exact glaPComponent_of_normal_sub hp (inf_le_inf_right _ hΛC) h2
    (glaPComponent_of_normal_sub hp (inf_le_inf_right _ hLΛ) h1 hJ)

omit [Finite G] in
theorem isCompLocallyBalanced_mono {p k : ℕ} {B D L : Subgroup G} (hDB : D ≤ B)
    (h : IsCompLocallyBalanced p k B L) : IsCompLocallyBalanced p k D L := by
  have hle : autBar p D L ≤ autBar p B L := by
    unfold autBar
    refine Subgroup.map_mono ?_
    intro g hg
    rw [Subgroup.mem_subgroupOf] at hg ⊢
    exact ⟨hDB hg.1, hg.2⟩
  intro D' hD' H hH hN
  exact h D' ⟨hD'.1.trans hle, hD'.2⟩ H hH hN

theorem rank_eq_four {m : ℕ} (hS : GLStanding G m 3) (hC : GLCaseFour G 3) : m = 4 := by
  have h1 := hS.rank_eq
  have h2 := hC.2.1
  omega

theorem part_i (h31 : Lemma31) (h59 : Lemma59) (h1910 : Input19_10) (h191 : Input19_1_2)
    (h61 : Input6_1) {m : ℕ} (hS : GLStanding G m 3) (hC : GLCaseFour G 3) {B : Subgroup G}
    (hB : IsBZeroMax 3 B) {b : G} (hb : b ∈ B) (hb1 : b ≠ 1) {L : Subgroup G}
    (hL : IsUpsilonComponent B b L) :
    IsExtremalType (barOf 3 L) ∨ IsSLThreeEps (barOf 3 L) := by
  have := hS.simple
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hB1 : IsBOneMax 3 B :=
    CFSG.HardMathSupport.Solomon.Proving.isBOneMax_of_isBZeroMax (by norm_num) hB
  obtain ⟨hLC, hdisj⟩ := hL
  rcases hdisj with ⟨hΛ, hψ⟩ | ⟨D, hD, hDnc⟩
  ·
    have hsc : IsSCp 3 ⊤ B := lemma23_proved G m 3 hS B hB1
    have hlam := lambdaOf_eq_of_lemma31 h31 hS hB.1 hsc hb hb1
    rw [lambdaMOf_eq_bot_of_ne_five (by norm_num), sup_bot_eq] at hlam
    set C : Subgroup G := Subgroup.centralizer ({b} : Set G) with hCdef
    set S1 : Set (Subgroup G) := {L | GLAPComponent 3 C L ∧ ¬ IsStronglyLocallyOneBalanced 3 B b L ∧
      IsInGOne 3 B L} with hS1
    set S2 : Set (Subgroup G) := {L | GLAPComponent 3 C L ∧ ¬ IsStronglyLocallyOneBalanced 3 B b L ∧
      Lemma31iii 3 B L} with hS2
    set S3 : Set (Subgroup G) := {L | GLAPComponent 3 C L ∧ ¬ IsStronglyLocallyOneBalanced 3 B b L ∧
      Lemma31iv 3 B L} with hS3
    have hle : L ≤ sSup (S1 ∪ S2 ∪ S3) := by
      rw [sSup_union, sSup_union]
      have : lambdaOf 3 B b = sSup S1 ⊔ sSup S2 ⊔ sSup S3 := hlam
      rw [← this]
      exact hΛ
    have hmem := mem_of_le_sSup hLC (fun A hA => by
      rcases hA with (hA | hA) | hA
      · exact hA.1
      · exact hA.1
      · exact hA.1) hle
    rcases hmem with (hm | hm) | hm
    · exfalso
      apply hψ
      have h1 : L ≤ psiOf 3 B b := le_sSup hm
      have h2 : psiOf 3 B b ≤ psiStarGroup 3 B :=
        le_iSup₂_of_le b hb (le_iSup_of_le hb1 (le_sup_left.trans le_sup_left))
      exact h1.trans h2
    · obtain ⟨-, -, -, -, ⟨K, hK, hKf, hKc, ⟨e⟩⟩, -⟩ := hm
      refine type_of_ext_quot h61 hLC (Or.inl ⟨K, hK, hKf, ?_, ⟨e⟩⟩)
      rw [hKc]
    · exact absurd hm.2.2.2.2.1 (h59 G m hS hC B hB b hb hb1 L ⟨hLC, Or.inl ⟨hΛ, hψ⟩⟩)
  ·
    have hBel : IsElemAbelian 3 B := hB.1.1
    set C : Subgroup G := Subgroup.centralizer ({b} : Set G) with hCdef
    have hBC : B ≤ C := le_centralizer_of_mem hBel hb
    have hCne : C ≠ ⊤ := centralizer_ne_top_of_simple hS.nonabelian hb1
    have hrk : GLATwoLocalRank 3 ↥C ≤ CFSG.Open.pRank 3 B :=
      (glaTwoLocalRank_subgroup_le hp C).trans (hS.rank_eq.le.trans (hS.le_pRank' hB1))
    have h2rk : 2 ≤ CFSG.Open.pRank 3 B :=
      le_trans (by have := hS.four_le; omega) (hS.le_pRank' hB1)
    obtain ⟨hDB, hDel, hDcard⟩ := hD
    have hDb : b ∈ Subgroup.centralizer (D : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      exact elemAbelian_comm hBel (hDB hd) hb
    obtain ⟨hnorm, hmain⟩ := h191 G hS.nonabelian hS.kProper 3 hp 2 (by norm_num) D hDel hDcard b
      hDb hb1 (hBel.2 b hb)
    have hX := hnorm L hLC
    have hnc : ¬ ⁅L, GLADelta 3 D ⊓ C⁆ ≤ GLAPPrimeCoreOf 3 C := by
      intro h
      apply hDnc
      have h1 : ⁅L, GLADelta 3 D ⊓ C⁆ ≤ L := by
        refine Subgroup.commutator_le.2 fun l hl y hy => ?_
        have hyN : y ∈ Subgroup.normalizer (L : Set G) := hX hy
        have h2 : y * l⁻¹ * y⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hyN l⁻¹).1 (L.inv_mem hl)
        rw [commutatorElement_def]
        have h3 : l * y * l⁻¹ * y⁻¹ = l * (y * l⁻¹ * y⁻¹) := by group
        rw [h3]
        exact L.mul_mem hl h2
      have h4 : GLAPPrimeCoreOf 3 C ⊓ L ≤ GLAPPrimeCoreOf 3 L := by
        have := gLAPPrimeCoreOf_inf_le hp C L
        rwa [inf_eq_right.2 hLC.1] at this
      exact fun z hz => h4 ⟨h hz, h1 hz⟩
    obtain ⟨hDN, hnbal⟩ := hmain L hLC hnc
    have hbal : ¬ IsCompLocallyBalanced 3 2 B L := fun hbalB =>
      hnbal (isCompLocallyBalanced_mono hDB hbalB)
    have h3 := (h1910 G hS.nonabelian hS.kProper 3 hp (by norm_num) C hCne B hBC hBel hrk L hLC).2.2
      h2rk
    rcases h3 with h3 | ⟨h5, -⟩ | ⟨-, h3⟩ | ⟨h5, -⟩
    · exact absurd h3 hbal
    · exact absurd h5 (by norm_num)
    · exact type_of_ext_quot h61 hLC h3
    · exact absurd h5 (by norm_num)


theorem part_iii (h56 : Lemma56) (h7 : Input7_L3Aut) {m : ℕ} (hS : GLStanding G m 3)
    (hC : GLCaseFour G 3) {B : Subgroup G} (hB : IsBZeroMax 3 B) {b : G} (hb : b ∈ B)
    (hb1 : b ≠ 1) {L : Subgroup G} (hL : IsUpsilonComponent B b L)
    (hty : IsExtremalType (barOf 3 L) ∨ IsSLThreeEps (barOf 3 L)) :
    ∃ A : Subgroup G, IsEkIn 3 2 B A ∧ ∀ a ∈ A, InducesFieldAut 3 L a := by
  have hB1 : IsBOneMax 3 B :=
    CFSG.HardMathSupport.Solomon.Proving.isBOneMax_of_isBZeroMax (by norm_num) hB
  have hBel : IsElemAbelian 3 B := hB.1.1
  have hBN : B ≤ Subgroup.normalizer (L : Set G) := (h56 G m hS hC B hB b hb hb1).2 L hL
  have hq : CFSG.Open.IsQuasisimple (barOf 3 L) := isQuasisimple_quotient_of_glaPComponent hL.1
  have hBel' : IsElemAbelian 3 (B ⊓ Subgroup.normalizer (L : Set G)) := by
    rw [inf_eq_left.2 hBN]; exact hBel
  have hE : IsElemAbelian 3 (autBar 3 B L) := isElemAbelian_map (isElemAbelian_subgroupOf hBel') _
  obtain ⟨F, hFE, hidx, hF⟩ := h7 (barOf 3 L) hq hty (autBar 3 B L) hE
  have hcard : Nat.card B = 3 ^ 4 := by
    have := hS.card_eq hB1
    rwa [rank_eq_four hS hC] at this
  obtain ⟨A, hA, hAF⟩ := exists_isEkIn_of_index_le hBel hcard hBN hidx
  refine ⟨A, hA, fun a ha => ?_⟩
  obtain ⟨h, hmem⟩ := hAF a ha
  exact ⟨h, hF _ hmem⟩

theorem part_iv (h53 : Lemma53) (h56 : Lemma56) (i183 : UniquenessMaximal.Input18_3_4)
    (i145 : Input14_5L3) (g1 : Gap510_Nontrivial) (g2 : Gap510_Type) (g3 : Gap510_Centre) (g4 : Gap510_Inner)
    {m : ℕ} (hS : GLStanding G m 3) (hC : GLCaseFour G 3) {B : Subgroup G}
    (hB : IsBZeroMax 3 B)
    (hi : ∀ x ∈ B, x ≠ 1 → ∀ A : Subgroup G, IsUpsilonComponent B x A →
      IsExtremalType (barOf 3 A) ∨ IsSLThreeEps (barOf 3 A))
    {b : G} (hb : b ∈ B) (hb1 : b ≠ 1) {L : Subgroup G} (hL : IsUpsilonComponent B b L)
    {x : G} (hx : x ∈ B) (hx1 : x ≠ 1) (hfld : InducesFieldAut 3 L x) :
    GLAPComponent 3 (Subgroup.centralizer ({x} : Set G)) (pumpUp L x) ∧
      InducesFieldAut 3 (pumpUp L x) b ∧
      B ⊓ oPrimePOf 3 L ≤ oPrimePOf 3 (Subgroup.centralizer ({x} : Set G)) := by
  have := hS.simple
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hB1 : IsBOneMax 3 B :=
    CFSG.HardMathSupport.Solomon.Proving.isBOneMax_of_isBZeroMax (by norm_num) hB
  have hBel : IsElemAbelian 3 B := hB.1.1
  set Cb : Subgroup G := Subgroup.centralizer ({b} : Set G) with hCb
  set Cx : Subgroup G := Subgroup.centralizer ({x} : Set G) with hCx
  have hLC : GLAPComponent 3 Cb L := hL.1
  have hCbne : Cb ≠ ⊤ := centralizer_ne_top_of_simple hS.nonabelian hb1
  have hCxne : Cx ≠ ⊤ := centralizer_ne_top_of_simple hS.nonabelian hx1
  have hKx : CFSG.Open.IsKGroup ↥Cx := isKGroup_of_isKProper hS.kProper hCxne
  have hty : IsExtremalType (barOf 3 L) ∨ IsSLThreeEps (barOf 3 L) := hi b hb hb1 L hL
  have hx3 : x ^ 3 = 1 := hBel.2 x hx
  have hb3 : b ^ 3 = 1 := hBel.2 b hb
  have hxCb : x ∈ Cb := le_centralizer_of_mem hBel hb hx
  have hbCx : b ∈ Cx := le_centralizer_of_mem hBel hx hb
  obtain ⟨hxNL, hfa⟩ := hfld
  have hne := amb_nontrivial g1 hLC hty hxNL hx3 hfa
  obtain ⟨J, hJ⟩ : ∃ J : Subgroup G, GLAPComponent 3 (L ⊓ Cx) J := by
    by_contra hno
    push Not at hno
    apply hne
    have : {J : Subgroup G | GLAPComponent 3 (L ⊓ Cx) J} = ∅ := Set.eq_empty_of_forall_notMem hno
    show sSup {J : Subgroup G | GLAPComponent 3 (L ⊓ Cx) J} = ⊥
    rw [this, sSup_empty]
  have hNKL : CFSG.Open.IsKGroup ↥(Subgroup.normalizer (L : Set G)) := by
    refine isKGroup_of_isKProper hS.kProper ?_
    intro htop
    have hnorm : L.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal L with h | h
    · exact glaPComponent_ne_bot hLC h
    · apply hCbne
      rw [← top_le_iff, ← h]
      exact hLC.1
  have hJu : ∀ J' : Subgroup G, GLAPComponent 3 (L ⊓ Cx) J' → J' = J := fun J' hJ' =>
    eq_of_glaPComponent_inf_centralizer i145 hty hNKL hLC hxNL hx3 hJ' hJ
  have hlayer : GLAPLayer 3 (L ⊓ Subgroup.centralizer ({x} : Set G)) = J :=
    le_antisymm (sSup_le fun A hA => (hJu A hA).le) (le_sSup hJ)
  have hJC : GLAPComponent 3 (Cb ⊓ Cx) J := glaPComponent_inf_centralizer hLC x hJ
  have hJC' : GLAPComponent 3 (Cx ⊓ Subgroup.centralizer ({b} : Set G)) J := by
    rwa [← hCb, inf_comm]
  have hpump : pumpUp L x ≤ upsilonOf B x := h53 G m hS hC B hB1 b hb hb1 L hL x hx hx1 ⟨hxNL, hfa⟩
  have hpump' : pumpUp L x = ⨆ g ∈ GLAPLayer 3 Cx, GLBConj g J := by
    unfold pumpUp; rw [hlayer]
  rcases UniquenessMaximal.dichotomy_of_input18_3_4 i183 hKx hbCx hb3 hJC' with
    ⟨K, hK, hJK, hKeq, hbK⟩ | ⟨L₁, L₂, L₃, h₁, h₂, h₃, h12, h23, h31, hc1, hc2, hc3, hKeq, hJle⟩
  ·
    have hpK : pumpUp L x = K := by rw [hpump']; exact hKeq
    have hKU : IsUpsilonComponent B x K := by
      have hle : K ≤ sSup {A | IsUpsilonComponent B x A} := hpK ▸ hpump
      exact mem_of_le_sSup hK (fun A hA => hA.1) hle
    have htyK : IsExtremalType (barOf 3 K) ∨ IsSLThreeEps (barOf 3 K) := hi x hx hx1 K hKU
    have hbN : b ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_iff_gLBConj_eq.2 hbK
    have hJK' : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({b} : Set G)) J :=
      glaPComponent_of_le hp hJC' (le_inf hJK (hJC'.1.trans inf_le_right)) (inf_le_inf_right _ hK.1)
    have hfieldK : InducesFieldAut 3 K b :=
      amb_inner g4 hK htyK hbN hb3 hJK' (amb_type g2 hLC hty hxNL hx3 hfa hJ)
    refine ⟨hpK ▸ hK, hpK ▸ hfieldK, ?_⟩
    obtain ⟨hZ1, -⟩ := amb_centre g3 hLC hty hxNL hx3 hfa hJ
    obtain ⟨-, hZ2⟩ := amb_centre g3 hK htyK hbN hb3 hfieldK.2 hJK'
    rintro r ⟨hrB, hrO⟩
    have hrL : r ∈ L := by obtain ⟨y, -, rfl⟩ := hrO; exact y.2
    have hrCx : r ∈ Cx := le_centralizer_of_mem hBel hx hrB
    have hr3 : r ^ 3 = 1 := hBel.2 r hrB
    obtain ⟨j, hjJ, n, hnD, hrjn⟩ := hZ1 r ⟨hrL, hrCx⟩ hrO
    set D : Subgroup G := GLAPPrimeCoreOf 3 L ⊓ Cx with hD
    have hJL : J ≤ L := hJ.1.trans inf_le_left
    have hJCx : J ≤ Cx := hJ.1.trans inf_le_right
    have hJN : J ≤ Subgroup.normalizer (D : Set G) := by
      intro j hj
      refine Subgroup.mem_normalizer_fintype fun d hd => ⟨?_, ?_⟩
      · exact mem_gLAPPrimeCoreOf_conj hd.1 (hJL hj)
      · exact Cx.mul_mem (Cx.mul_mem (hJCx hj) hd.2) (Cx.inv_mem (hJCx hj))
    have hDcop : Nat.Coprime 3 (Nat.card D) := by
      have h1 : Nat.card D ∣ Nat.card (GLAPPrimeCoreOf 3 L) :=
        Subgroup.card_dvd_of_le inf_le_left
      have h2 : Nat.card (GLAPPrimeCoreOf 3 L) = Nat.card (GLAPPrimeCore 3 ↥L) :=
        Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
      exact (coprime_card_gLAPPrimeCore_aux 3 ↥L).coprime_dvd_right (h2 ▸ h1)
    obtain ⟨d, hdD, hdr⟩ := exists_conj_mem_of_mul hJN hDcop hjJ hnD hr3 hrjn
    have hdL : d ∈ L :=
      CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.GLAPPrimeCoreOf_le 3 L hdD.1
    have hr'O : d * r * d⁻¹ ∈ oPrimePOf 3 L := mem_oPrimePOf_conj hdL hrO
    have hr'J : d * r * d⁻¹ ∈ oPrimePOf 3 J := mem_oPrimePOf_of_mem_inf hLC hJL hdr hr'O
    have hr'K : d * r * d⁻¹ ∈ oPrimePOf 3 K := hZ2 ⟨hdr, hr'J⟩
    have hr'X : d * r * d⁻¹ ∈ oPrimePOf 3 Cx := oPrimePOf_le_of_glaPComponent hK hr'K
    have := mem_oPrimePOf_conj (Cx.inv_mem hdD.2) hr'X
    simpa [mul_assoc] using this
  ·
    exfalso
    have hle : L₁ ≤ upsilonOf B x := by
      have h1 : L₁ ≤ pumpUp L x := by
        rw [hpump', hKeq]; exact le_sup_left.trans le_sup_left
      exact h1.trans hpump
    have hL₁ : IsUpsilonComponent B x L₁ := mem_of_le_sSup h₁ (fun A hA => hA.1) hle
    have hBN := (h56 G m hS hC B hB x hx hx1).2 L₁ hL₁
    have hbN : b ∈ Subgroup.normalizer (L₁ : Set G) := hBN hb
    have := mem_normalizer_iff_gLBConj_eq.1 hbN
    rw [hc1] at this
    exact h12 this.symm

end Typed

end Lemma510Ns

theorem lemma510_of_inputs (h53 : Lemma53) (h56 : Lemma56) (h59 : Lemma59) (h31 : Lemma31)
    (h1910 : Input19_10) (h191 : Lemma510Ns.Input19_1_2) (h61 : Lemma510Ns.Input6_1)
    (h7 : Lemma510Ns.Input7_L3Aut) (i183 : UniquenessMaximal.Input18_3_4)
    (i145 : Lemma510Ns.Input14_5L3) (g1 : Lemma510Ns.Gap510_Nontrivial) (g2 : Lemma510Ns.Gap510_Type)
    (g3 : Lemma510Ns.Gap510_Centre) (g4 : Lemma510Ns.Gap510_Inner) : Lemma510 := by
  intro G _ _ m hS hC B hB b hb hb1 L hL
  have hi : ∀ x ∈ B, x ≠ 1 → ∀ A : Subgroup G, IsUpsilonComponent B x A →
      IsExtremalType (barOf 3 A) ∨ IsSLThreeEps (barOf 3 A) := fun x hx hx1 A hA =>
    Lemma510Ns.part_i h31 h59 h1910 h191 h61 hS hC hB hx hx1 hA
  refine ⟨hi b hb hb1 L hL, Lemma510Ns.part_iii h56 h7 hS hC hB hb hb1 hL (hi b hb hb1 L hL), ?_⟩
  intro x hx hx1 hfld
  exact Lemma510Ns.part_iv h53 h56 i183 i145 g1 g2 g3 g4 hS hC hB hi hb hb1 hL hx hx1 hfld

end CFSG.HardMathSupport.Solomon.LocalBalance
