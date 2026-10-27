module

public import CFSG.LocalAnalysis.AGLEmbedding.RankLemmas
public import CFSG.LocalAnalysis.LargeEvenClassification.ElementaryHomRank
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.GroupTheory.ElemAbelianRank
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraBasic

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.Open

variable {T B : Type*} [Group T] [Finite T] [Group B] [Finite B]

private theorem exists_fullRank_elemAbelian {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) :
    ∃ A : Subgroup G, A ≤ H ∧ IsElemAbelian 2 A ∧
      CFSG.Open.pRank 2 A = CFSG.Open.pRank 2 H := by
  obtain ⟨A, hAH, hAe, hAcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := 2) (by norm_num) H
  have hcardA : Nat.card A = 2 ^ CFSG.Open.pRank 2 A :=
    CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_two hAe
  have hpow : 2 ^ CFSG.Open.pRank 2 A = 2 ^ CFSG.Open.pRank 2 H := by
    rw [← hcardA, hAcard]
  exact ⟨A, hAH, hAe, Nat.pow_right_injective (by norm_num) hpow⟩

private theorem isMaxElemAbelian_of_elem_pRank_eq {G : Type*} [Group G] [Finite G]
    {A H : Subgroup G} (hAH : A ≤ H) (hA : IsElemAbelian 2 A)
    (hrank : CFSG.Open.pRank 2 A = CFSG.Open.pRank 2 H) :
    CFSG.Quasithin.IsMaxElemAbelian H A := by
  refine (CFSG.Quasithin.isMaxElemAbelian_iff_corank_zero).mpr ⟨hAH, hA, ?_⟩
  have hcard : Nat.card A = 2 ^ CFSG.Open.pRank 2 A :=
    CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_two hA
  rw [pow_zero, mul_one, ← hrank]
  exact hcard

private theorem pRank_eq_of_isMaxElemAbelian {G : Type*} [Group G] [Finite G]
    {A H : Subgroup G} (hA : CFSG.Quasithin.IsMaxElemAbelian H A) :
    CFSG.Open.pRank 2 A = CFSG.Open.pRank 2 H := by
  have hc := (CFSG.Quasithin.isMaxElemAbelian_iff_corank_zero.mp hA).2.2
  rw [pow_zero, mul_one] at hc
  have hcard : Nat.card A = 2 ^ CFSG.Open.pRank 2 A :=
    CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_two hA.2.1
  rw [hcard] at hc
  exact Nat.pow_right_injective (by norm_num) hc

private theorem relative_rank_inequalities
    (f : T →* B) (L : Subgroup B)
    (hadd : CFSG.Open.pRank 2 (L.comap f) =
      CFSG.Open.pRank 2 f.ker + CFSG.Open.pRank 2 L)
    (hrel : ∀ E : Subgroup B, CFSG.Quasithin.IsMaxElemAbelian (⊤ : Subgroup B) E →
      CFSG.Open.pRank 2 E ≤ CFSG.Open.pRank 2 (E ⊓ L) + 1) :
    (∀ A : Subgroup T, A ≤ L.comap f → IsElemAbelian 2 A →
      CFSG.Open.pRank 2 A ≤ CFSG.Open.pRank 2 (A ⊓ f.ker) + CFSG.Open.pRank 2 L) ∧
    (CFSG.Open.pRank 2 (L.comap f) < CFSG.Open.pRank 2 (⊤ : Subgroup T) →
      ∀ A : Subgroup T, CFSG.Quasithin.IsMaxElemAbelian (⊤ : Subgroup T) A →
        CFSG.Open.pRank 2 A ≤ CFSG.Open.pRank 2 (A ⊓ L.comap f) + 1) := by
  constructor
  · intro A hAN _hA
    have hmap : CFSG.Open.pRank 2 (A.map f) ≤ CFSG.Open.pRank 2 L := by
      refine CFSG.SectionRank.pRank_mono (p := 2) (by norm_num) ?_
      intro x hx
      obtain ⟨a, haA, rfl⟩ := Subgroup.mem_map.mp hx
      exact hAN haA
    exact (CFSG.AGLEmbedding.pRank_le_pRank_inf_ker_add_pRank_map
      (p := 2) Nat.prime_two f A).trans (Nat.add_le_add_left hmap _)
  · intro hlt A hA
    have hArank : CFSG.Open.pRank 2 A = CFSG.Open.pRank 2 (⊤ : Subgroup T) :=
      pRank_eq_of_isMaxElemAbelian hA
    have hBbound : CFSG.Open.pRank 2 (⊤ : Subgroup B) ≤ CFSG.Open.pRank 2 L + 1 := by
      obtain ⟨E, hE⟩ := CFSG.Quasithin.exists_isMaxElemAbelian (⊤ : Subgroup B)
      have hErank : CFSG.Open.pRank 2 E = CFSG.Open.pRank 2 (⊤ : Subgroup B) :=
        pRank_eq_of_isMaxElemAbelian hE
      have hEL : CFSG.Open.pRank 2 (E ⊓ L) ≤ CFSG.Open.pRank 2 L :=
        CFSG.SectionRank.pRank_mono (p := 2) (by norm_num) inf_le_right
      calc CFSG.Open.pRank 2 (⊤ : Subgroup B) = CFSG.Open.pRank 2 E := hErank.symm
        _ ≤ CFSG.Open.pRank 2 (E ⊓ L) + 1 := hrel E hE
        _ ≤ CFSG.Open.pRank 2 L + 1 := Nat.add_le_add_right hEL 1
    have hkerle : CFSG.Open.pRank 2 (A ⊓ f.ker) ≤ CFSG.Open.pRank 2 f.ker :=
      CFSG.SectionRank.pRank_mono (p := 2) (by norm_num) inf_le_right
    have hTle : CFSG.Open.pRank 2 (⊤ : Subgroup T) ≤
        CFSG.Open.pRank 2 f.ker + CFSG.Open.pRank 2 (A.map f) := by
      calc CFSG.Open.pRank 2 (⊤ : Subgroup T) = CFSG.Open.pRank 2 A := hArank.symm
        _ ≤ CFSG.Open.pRank 2 (A ⊓ f.ker) + CFSG.Open.pRank 2 (A.map f) :=
          CFSG.AGLEmbedding.pRank_le_pRank_inf_ker_add_pRank_map
            (p := 2) Nat.prime_two f A
        _ ≤ CFSG.Open.pRank 2 f.ker + CFSG.Open.pRank 2 (A.map f) :=
          Nat.add_le_add_right hkerle _
    have hmapgt : CFSG.Open.pRank 2 L < CFSG.Open.pRank 2 (A.map f) := by
      rw [hadd] at hlt
      omega
    have hmaple : CFSG.Open.pRank 2 (A.map f) ≤ CFSG.Open.pRank 2 (⊤ : Subgroup B) :=
      CFSG.SectionRank.pRank_mono (p := 2) (by norm_num) le_top
    have hmapeq : CFSG.Open.pRank 2 (A.map f) = CFSG.Open.pRank 2 (⊤ : Subgroup B) := by
      omega
    have hmapelem : IsElemAbelian 2 (A.map f) := CFSG.Open.IsElemAbelian.map hA.2.1 f
    have hmapmax : CFSG.Quasithin.IsMaxElemAbelian (⊤ : Subgroup B) (A.map f) := by
      refine ⟨le_top, hmapelem, ?_⟩
      intro C hC hCe
      have hCrank : CFSG.Open.pRank 2 C ≤ CFSG.Open.pRank 2 (⊤ : Subgroup B) :=
        CFSG.SectionRank.pRank_mono (p := 2) (by norm_num) hC
      rw [CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_two hCe,
        CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_two hmapelem,
        hmapeq]
      exact Nat.pow_le_pow_right (by norm_num) hCrank
    let K : Subgroup T := A ⊓ L.comap f
    have hKelem : IsElemAbelian 2 K := hA.2.1.mono inf_le_left
    have hKcard : Nat.card K = 2 ^ CFSG.Open.pRank 2 K :=
      CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_two hKelem
    have hKformula := CFSG.LargeEvenClassification.Helpers.elementary_hom_rank_add
      (Ambient := T) (Target := B) (prime := 2) Nat.prime_two K hKelem hKcard
      (f.comp K.subtype)
    have hKker : (f.comp K.subtype).ker.map K.subtype = K ⊓ f.ker := by
      ext x
      simp [K, MonoidHom.mem_ker]
      tauto
    have hKmap : (f.comp K.subtype).range = K.map f := by
      ext y
      simp [K]
    have hKrank : CFSG.Open.pRank 2 (A ⊓ f.ker) + CFSG.Open.pRank 2 ((A.map f) ⊓ L) =
        CFSG.Open.pRank 2 (A ⊓ L.comap f) := by
      have hKkerA : K ⊓ f.ker = A ⊓ f.ker := by
        ext x
        constructor
        · rintro ⟨⟨hxA, _hxN⟩, hxker⟩
          exact ⟨hxA, hxker⟩
        · rintro ⟨hxA, hxker⟩
          refine ⟨⟨hxA, ?_⟩, hxker⟩
          change f x ∈ L
          rw [MonoidHom.mem_ker.mp hxker]
          exact L.one_mem
      have hKmapA : K.map f = (A.map f) ⊓ L := by
        ext y
        constructor
        · rintro ⟨x, hxK, rfl⟩
          exact ⟨⟨x, hxK.1, rfl⟩, hxK.2⟩
        · rintro ⟨hyA, hyL⟩
          obtain ⟨x, hxA, rfl⟩ := Subgroup.mem_map.mp hyA
          exact ⟨x, ⟨hxA, hyL⟩, rfl⟩
      simpa [hKker, hKmap, hKkerA, hKmapA, K] using hKformula
    have hrelmap := hrel (A.map f) hmapmax
    calc CFSG.Open.pRank 2 A
        ≤ CFSG.Open.pRank 2 (A ⊓ f.ker) + CFSG.Open.pRank 2 (A.map f) :=
          CFSG.AGLEmbedding.pRank_le_pRank_inf_ker_add_pRank_map
            (p := 2) Nat.prime_two f A
      _ ≤ CFSG.Open.pRank 2 (A ⊓ f.ker) +
          (CFSG.Open.pRank 2 ((A.map f) ⊓ L) + 1) := Nat.add_le_add_left hrelmap _
      _ = (CFSG.Open.pRank 2 (A ⊓ f.ker) + CFSG.Open.pRank 2 ((A.map f) ⊓ L)) + 1 := by
          rw [Nat.add_assoc]
      _ = CFSG.Open.pRank 2 (A ⊓ L.comap f) + 1 := by rw [hKrank]

private theorem exists_saturating_maxElemAbelian {G : Type*} [Group G] [Finite G]
    {Q N T : Subgroup G} {r : ℕ}
    (hQN : Q ≤ N) (hNT : N ≤ T)
    (hrankN : CFSG.Open.pRank 2 N = CFSG.Open.pRank 2 Q + r)
    (hrelN : ∀ A : Subgroup G, A ≤ N → IsElemAbelian 2 A →
      CFSG.Open.pRank 2 A ≤ CFSG.Open.pRank 2 (A ⊓ Q) + r)
    (hrelT : CFSG.Open.pRank 2 N < CFSG.Open.pRank 2 T →
      ∀ A : Subgroup G, A ≤ T → IsElemAbelian 2 A →
        CFSG.Open.pRank 2 A = CFSG.Open.pRank 2 T →
        CFSG.Open.pRank 2 A ≤ CFSG.Open.pRank 2 (A ⊓ N) + 1) :
    ∃ A : Subgroup G, A ≤ T ∧ IsElemAbelian 2 A ∧
      CFSG.Open.pRank 2 A = CFSG.Open.pRank 2 T ∧
      CFSG.Open.pRank 2 (A ⊓ Q) = CFSG.Open.pRank 2 Q ∧
      (∀ u : G, u ∈ Q → orderOf u = 2 → (∀ q ∈ Q, q * u = u * q) →
        u ∈ A ∧ CFSG.Open.pRank 2 (T ⊓ centralizer ({u} : Set G)) =
          CFSG.Open.pRank 2 T) := by
  classical
  have hNleT : CFSG.Open.pRank 2 N ≤ CFSG.Open.pRank 2 T :=
    CFSG.SectionRank.pRank_mono (p := 2) (by norm_num) hNT
  have central_part : ∀ A : Subgroup G, A ≤ T → IsElemAbelian 2 A →
      CFSG.Open.pRank 2 A = CFSG.Open.pRank 2 T →
      CFSG.Open.pRank 2 (A ⊓ Q) = CFSG.Open.pRank 2 Q →
      (∀ u : G, u ∈ Q → orderOf u = 2 → (∀ q ∈ Q, q * u = u * q) →
        u ∈ A ∧ CFSG.Open.pRank 2 (T ⊓ centralizer ({u} : Set G)) =
          CFSG.Open.pRank 2 T) := by
    intro A hAT hAel hArankT hAqrank
    have hAqel : IsElemAbelian 2 (A ⊓ Q) := CFSG.Open.IsElemAbelian.mono hAel inf_le_left
    have hAqmax : CFSG.Quasithin.IsMaxElemAbelian Q (A ⊓ Q) :=
      isMaxElemAbelian_of_elem_pRank_eq inf_le_right hAqel hAqrank
    intro u huQ hu2 huc
    have hu2' : u ^ 2 = 1 := by
      rw [← hu2]
      exact pow_orderOf_eq_one u
    have huAq : u ∈ A ⊓ Q :=
      CFSG.QuasithinUnique.GammaExtra.mem_of_isMaxElemAbelian_of_central_involution
        hAqmax huQ huc hu2'
    have huA : u ∈ A := huAq.1
    have hAcomm : A ≤ centralizer ({u} : Set G) := by
      intro a ha
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val
        (hAel.1.is_comm.comm ⟨a, ha⟩ ⟨u, huA⟩)
    have hAleCT : A ≤ T ⊓ centralizer ({u} : Set G) := le_inf hAT hAcomm
    have hCTge : CFSG.Open.pRank 2 T ≤
        CFSG.Open.pRank 2 (T ⊓ centralizer ({u} : Set G)) := by
      rw [← hArankT]
      exact CFSG.SectionRank.pRank_mono (p := 2) (by norm_num) hAleCT
    have hCTle : CFSG.Open.pRank 2 (T ⊓ centralizer ({u} : Set G)) ≤
        CFSG.Open.pRank 2 T :=
      CFSG.SectionRank.pRank_mono (p := 2) (by norm_num) inf_le_left
    exact ⟨huA, le_antisymm hCTle hCTge⟩
  by_cases hEq : CFSG.Open.pRank 2 N = CFSG.Open.pRank 2 T
  · obtain ⟨A, hAN, hAel, hArankN⟩ := exists_fullRank_elemAbelian N
    have hAT : A ≤ T := hAN.trans hNT
    have hArankT : CFSG.Open.pRank 2 A = CFSG.Open.pRank 2 T := by
      rw [hArankN, hEq]
    have hAqge : CFSG.Open.pRank 2 Q ≤ CFSG.Open.pRank 2 (A ⊓ Q) := by
      have h := hrelN A hAN hAel
      rw [hArankN, hrankN] at h
      omega
    have hAqle : CFSG.Open.pRank 2 (A ⊓ Q) ≤ CFSG.Open.pRank 2 Q :=
      CFSG.SectionRank.pRank_mono (p := 2) (by norm_num) inf_le_right
    have hAqrank : CFSG.Open.pRank 2 (A ⊓ Q) = CFSG.Open.pRank 2 Q :=
      le_antisymm hAqle hAqge
    exact ⟨A, hAT, hAel, hArankT, hAqrank,
      central_part A hAT hAel hArankT hAqrank⟩
  · have hlt : CFSG.Open.pRank 2 N < CFSG.Open.pRank 2 T :=
      lt_of_le_of_ne hNleT hEq
    obtain ⟨A, hAmax⟩ := CFSG.Quasithin.exists_isMaxElemAbelian T
    have hAT : A ≤ T := hAmax.1
    have hAel : IsElemAbelian 2 A := hAmax.2.1
    have hArankT : CFSG.Open.pRank 2 A = CFSG.Open.pRank 2 T :=
      pRank_eq_of_isMaxElemAbelian hAmax
    have hArelT := hrelT hlt A hAT hAel hArankT
    have hANge : CFSG.Open.pRank 2 N ≤ CFSG.Open.pRank 2 (A ⊓ N) := by
      have hTge : CFSG.Open.pRank 2 N + 1 ≤ CFSG.Open.pRank 2 T :=
        Nat.succ_le_of_lt hlt
      omega
    have hANle : CFSG.Open.pRank 2 (A ⊓ N) ≤ CFSG.Open.pRank 2 N :=
      CFSG.SectionRank.pRank_mono (p := 2) (by norm_num) inf_le_right
    have hANrank : CFSG.Open.pRank 2 (A ⊓ N) = CFSG.Open.pRank 2 N :=
      le_antisymm hANle hANge
    have hANel : IsElemAbelian 2 (A ⊓ N) := CFSG.Open.IsElemAbelian.mono hAel inf_le_left
    have hrel := hrelN (A ⊓ N) inf_le_right hANel
    have hdouble : (A ⊓ N) ⊓ Q = A ⊓ Q := by
      rw [inf_assoc, inf_eq_right.mpr hQN]
    have hAqge : CFSG.Open.pRank 2 Q ≤ CFSG.Open.pRank 2 (A ⊓ Q) := by
      rw [hdouble] at hrel
      rw [hANrank, hrankN] at hrel
      omega
    have hAqle : CFSG.Open.pRank 2 (A ⊓ Q) ≤ CFSG.Open.pRank 2 Q :=
      CFSG.SectionRank.pRank_mono (p := 2) (by norm_num) inf_le_right
    have hAqrank : CFSG.Open.pRank 2 (A ⊓ Q) = CFSG.Open.pRank 2 Q :=
      le_antisymm hAqle hAqge
    exact ⟨A, hAT, hAel, hArankT, hAqrank,
      central_part A hAT hAel hArankT hAqrank⟩

theorem exists_maxElemAbelian_inf_ker_of_relative_rank
    (f : T →* B) (L : Subgroup B)
    (hadd : CFSG.Open.pRank 2 (L.comap f) =
      CFSG.Open.pRank 2 f.ker + CFSG.Open.pRank 2 L)
    (hrel : ∀ E : Subgroup B, CFSG.Quasithin.IsMaxElemAbelian (⊤ : Subgroup B) E →
      CFSG.Open.pRank 2 E ≤ CFSG.Open.pRank 2 (E ⊓ L) + 1) :
    ∃ A : Subgroup T, CFSG.Quasithin.IsMaxElemAbelian (⊤ : Subgroup T) A ∧
      CFSG.Open.pRank 2 (A ⊓ f.ker) = CFSG.Open.pRank 2 f.ker ∧
      (∀ u : T, u ∈ f.ker → orderOf u = 2 →
        (∀ q ∈ f.ker, q * u = u * q) →
        u ∈ A ∧ CFSG.Open.pRank 2 (centralizer ({u} : Set T)) =
          CFSG.Open.pRank 2 (⊤ : Subgroup T)) := by
  have hQN : f.ker ≤ L.comap f := by
    intro q hq
    change f q ∈ L
    rw [MonoidHom.mem_ker.mp hq]
    exact L.one_mem
  have hrelAll := relative_rank_inequalities f L hadd hrel
  have hrelN : ∀ A : Subgroup T, A ≤ L.comap f → IsElemAbelian 2 A →
      CFSG.Open.pRank 2 A ≤ CFSG.Open.pRank 2 (A ⊓ f.ker) + CFSG.Open.pRank 2 L :=
    hrelAll.1
  obtain ⟨A, _hAT, hAel, hArankT, hAqrank, hAcentral⟩ :=
    exists_saturating_maxElemAbelian
      (Q := f.ker) (N := L.comap f) (T := ⊤) (r := CFSG.Open.pRank 2 L)
      hQN le_top hadd hrelN
      (fun hlt A hAT hAel hArank =>
        hrelAll.2 hlt A
          (isMaxElemAbelian_of_elem_pRank_eq hAT hAel hArank))
  have hAmax : CFSG.Quasithin.IsMaxElemAbelian (⊤ : Subgroup T) A :=
    isMaxElemAbelian_of_elem_pRank_eq le_top hAel hArankT
  have hAcentral' : ∀ u : T, u ∈ f.ker → orderOf u = 2 →
      (∀ q ∈ f.ker, q * u = u * q) →
      u ∈ A ∧ CFSG.Open.pRank 2 (centralizer ({u} : Set T)) =
        CFSG.Open.pRank 2 (⊤ : Subgroup T) := by
    intro u hu huo huc
    have hunb := hAcentral u hu huo huc
    refine ⟨hunb.1, ?_⟩
    simpa using hunb.2
  exact ⟨A, hAmax, hAqrank, hAcentral'⟩

end CFSG.GroupTheory
