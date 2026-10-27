module

public import CFSG.LocalAnalysis.AGLEmbedding.ZZPrimeDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbAltDefs
import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsAux
import CFSG.LocalAnalysis.AGLEmbedding.PrimeBlockTypes
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CanonicalCoprimePreimages

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def CitedBlockTransvectionPL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), Open.IsKGroup ↥M →
    Asc81bHyp M S → IsWeakSBlock M S L → ¬ InClassXBlock L → ¬ IsSylowTwoOf (S ⊓ L) L →
    NineThreeThree M S L →
    (∃ (k : ℕ) (d : TauCeti.ValidLieTypeIndex), 3 ≤ k ∧
        (∃ q : TauCeti.PrimePower, q.card = 2 ∧ d.1 = .B k q) ∧
        Nonempty (↥(barM M (Subgroup.normalizer (S : Set G) ⊓ L)) ⧸
          CFSG.pCore 2 ↥(barM M (Subgroup.normalizer (S : Set G) ⊓ L)) ≃*
            (TauCeti.CFSGIndex.lie d).Group)) ∨
      ∃ n : ℕ, (n = 3 ∨ n = 4 ∨ n = 6) ∧
        Nonempty (↥(barM M (Subgroup.normalizer (S : Set G) ⊓ L)) ⧸
          CFSG.pCore 2 ↥(barM M (Subgroup.normalizer (S : Set G) ⊓ L)) ≃* Equiv.Perm (Fin n))

@[expose] def CitedBlockAltSevenPL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), Open.IsKGroup ↥M →
    Asc81bHyp M S → IsWeakSBlock M S L → ¬ InClassXBlock L → ¬ IsSylowTwoOf (S ⊓ L) L →
    NineThreeFive M L → Nat.card (barM M (Subgroup.normalizer (S : Set G) ⊓ L)) ∣ 72

@[expose] def KFactSpTwoSimple : Prop :=
  ∀ (k : ℕ) (d : TauCeti.ValidLieTypeIndex), 3 ≤ k →
    (∃ q : TauCeti.PrimePower, q.card = 2 ∧ d.1 = .B k q) →
      IsSimpleGroup (TauCeti.CFSGIndex.lie d).Group ∧
        2 ^ 9 ∣ Nat.card (TauCeti.CFSGIndex.lie d).Group

@[expose] def KFactSpTwoPerfect : Prop :=
  ∀ (k : ℕ) (d : TauCeti.ValidLieTypeIndex), 3 ≤ k →
    (∃ q : TauCeti.PrimePower, q.card = 2 ∧ d.1 = .B k q) →
      commutator (TauCeti.CFSGIndex.lie d).Group = ⊤

theorem kFactSpTwoPerfect_of_simple (hSp : KFactSpTwoSimple) : KFactSpTwoPerfect := by
  intro k d hk hd
  obtain ⟨hsimp, h29⟩ := hSp k d hk hd
  set Q := (TauCeti.CFSGIndex.lie d).Group
  have := hsimp
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Q) with h | h
  · exfalso
    have h' : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ = ⊥ := by rw [← commutator_def]; exact h
    have hc := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h'
    have hcomm : ∀ a b : Q, a * b = b * a := fun a b =>
      (Subgroup.mem_centralizer_iff.mp (hc (Subgroup.mem_top a)) b (Subgroup.mem_top b)).symm
    let _ : CommGroup Q := { (inferInstance : Group Q) with mul_comm := hcomm }
    have hpr := IsSimpleGroup.prime_card (α := Q)
    have h2 : 2 ∣ Nat.card Q := dvd_trans (dvd_pow_self 2 (by norm_num)) h29
    have h4 : 4 ∣ Nat.card Q := dvd_trans (pow_dvd_pow 2 (by norm_num : 2 ≤ 9)) h29
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hpr).mp h2
    rw [← this] at h4
    norm_num at h4
  · exact h

theorem citedBlockTransvectionPrime_of_PL (hPL : CitedBlockTransvectionPL)
    (hSp : KFactSpTwoPerfect) : CitedBlockTransvectionPrime := by
  intro G _ _ M S L p hK hA hL hX hS h3 hp hp5 hperf
  rcases hPL G M S L hK hA hL hX hS h3 with ⟨k, d, hk, hd, ⟨e⟩⟩ | ⟨n, -, ⟨e⟩⟩
  · refine coprime_card_of_coprime_card_quotient_pCore_two hp (by omega) ?_
    rw [Nat.card_congr e.toEquiv]
    have hQ := hSp k d hk hd
    have h := coprime_card_of_surjective_of_perfect hperf
      (e.toMonoidHom.comp (QuotientGroup.mk' _))
      (e.surjective.comp (QuotientGroup.mk'_surjective _)) ⊤
      (by rw [← commutator_def, hQ])
    rwa [Subgroup.card_top] at h
  · exact coprime_card_of_quotient_perm hp hp5 hperf e

theorem kFactBlockAltSevenPrime_of_PL (hPL : CitedBlockAltSevenPL) :
    KFactBlockAltSevenPrime := by
  intro G _ _ M S L p hK hA hL hX hS h5 hp hp5 _
  have h72 : p.Coprime 72 := by
    rw [show (72 : ℕ) = 2 ^ 3 * 3 ^ 2 by norm_num]
    exact Nat.Coprime.mul_right
      (Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr (by omega)))
      (Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_three).mpr (by omega)))
  exact Nat.Coprime.coprime_dvd_right (hPL G M S L hK hA hL hX hS h5) h72

theorem citedBlockThreeToralAltIb_of_PL (hPL : CitedBlockTransvectionPL)
    (hSp : KFactSpTwoSimple) : CitedBlockThreeToralAltIb := by
  intro G _ _ M S L p hK hA hL hX hS h3 hp hJ E hEP hEel hEcard
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  have hp2 : p ≠ 2 := by rcases hp with rfl | rfl <;> norm_num
  have : Fact p.Prime := ⟨hpp⟩
  set P := barM M (Subgroup.normalizer (S : Set G) ⊓ L)
  have h3Q := pow_three_dvd_card_quotient_pCore hpp hp2 hEP hEcard
  rcases hPL G M S L hK hA hL hX hS h3 with ⟨k, d, hk, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · obtain ⟨hsimp, h29⟩ := hSp k d hk hd
    set Q := (TauCeti.CFSGIndex.lie d).Group
    rw [Nat.card_congr e.toEquiv] at h3Q
    have hQperf : commutator Q = ⊤ := kFactSpTwoPerfect_of_simple hSp k d hk hd
    set ψ : ↥P →* Q := e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥P))
    have hψ : Function.Surjective ψ := e.surjective.comp (QuotientGroup.mk'_surjective _)
    have hTop : Group.IsPerfect (⊤ : Subgroup Q) := by
      rw [Subgroup.isPerfect_iff, ← commutator_def, hQperf]
    set R₀ := perfectResidualOf (Subgroup.comap ψ ⊤)
    have hR₀ : R₀.map ψ = ⊤ := finite_canonical_perfect_preimage_image_eq ψ hψ ⊤ hTop
    have hR₀p : ⁅R₀, R₀⁆ = R₀ :=
      Subgroup.isPerfect_iff.mp (finite_perfectResidualOf_isPerfect (Subgroup.comap ψ ⊤))
    set V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) := R₀.map P.subtype
    have hVP : V ≤ P := Subgroup.map_subtype_le R₀
    have hVperf : ⁅V, V⁆ = V := by rw [← Subgroup.map_commutator, hR₀p]
    set φ : ↥V →* Q := ψ.comp (Subgroup.inclusion hVP)
    have hφ : Function.Surjective φ := by
      intro q
      have : q ∈ R₀.map ψ := hR₀ ▸ Subgroup.mem_top q
      obtain ⟨r, hr, rfl⟩ := this
      exact ⟨⟨(r : ↥M ⧸ CFSG.pCore 2 ↥M), r, hr, rfl⟩, by
        simp [φ, Subgroup.inclusion]⟩
    have hker2 : IsPGroup 2 φ.ker := by
      intro x
      have hx : ψ (Subgroup.inclusion hVP x) = 1 := x.2
      have hmem : Subgroup.inclusion hVP x ∈ CFSG.pCore 2 ↥P := by
        have : QuotientGroup.mk' (CFSG.pCore 2 ↥P) (Subgroup.inclusion hVP x) = 1 :=
          e.injective (by simpa [ψ] using hx)
        exact (QuotientGroup.eq_one_iff _).mp this
      obtain ⟨j, hj⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥P) ⟨_, hmem⟩
      refine ⟨j, Subtype.ext (Subtype.ext ?_)⟩
      have := congrArg (fun y => ((y : ↥P) : ↥M ⧸ CFSG.pCore 2 ↥M)) (congrArg Subtype.val hj)
      simpa using this
    obtain ⟨N, hN, hNi, f, hf⟩ := hJ V hVP hVperf
    have hQV : Nat.card Q ∣ Nat.card V := by
      rw [← Subgroup.index_mul_card φ.ker, Subgroup.index_ker,
        MonoidHom.range_eq_top_of_surjective φ hφ, Subgroup.card_top]
      exact dvd_mul_right _ _
    set W := f.ker ⊔ φ.ker
    have hWn : W.Normal := by
      have := f.normal_ker; have := φ.normal_ker; infer_instance
    have := hsimp
    have := hWn.map φ hφ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (W.map φ) with hWb | hWt
    · have hle : f.ker ≤ φ.ker := le_sup_left.trans ((Subgroup.map_eq_bot_iff _).mp hWb)
      have hdvd : φ.ker.index ∣ f.ker.index := Subgroup.index_dvd_of_le hle
      rw [Subgroup.index_ker, Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective φ hφ,
        Subgroup.card_top] at hdvd
      have hA := hdvd.trans (Subgroup.card_subgroup_dvd_card f.range)
      rw [Nat.card_prod] at hA
      have : Nontrivial (Fin p) := Fin.nontrivial_iff_two_le.mpr hpp.two_le
      rw [nat_card_alternatingGroup, Nat.card_fin] at hA
      have h29' := h29.trans hA
      rcases hp with rfl | rfl <;> revert h29' <;> decide
    · have hW : W = ⊤ := by
        rw [eq_top_iff]
        intro v _
        have : φ v ∈ W.map φ := hWt ▸ Subgroup.mem_top _
        obtain ⟨w, hw, hwv⟩ := this
        have : w⁻¹ * v ∈ φ.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hwv, inv_mul_cancel]
        have hv : v = w * (w⁻¹ * v) := by group
        rw [hv]
        exact W.mul_mem hw (le_sup_right (b := φ.ker) this)
      have hf2 : ∀ v : ↥V, ∃ j : ℕ, f v ^ 2 ^ j = 1 := by
        intro v
        have hv : v ∈ W := hW ▸ Subgroup.mem_top v
        have : f v ∈ W.map f := Subgroup.mem_map_of_mem f hv
        rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).mpr le_rfl, bot_sup_eq] at this
        obtain ⟨j, hj⟩ := (hker2.map f) ⟨f v, this⟩
        exact ⟨j, by simpa using congrArg Subtype.val hj⟩
      have hNp : ¬ p ∣ Nat.card N := by
        intro hd
        obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := N) p hd
        have hxo : orderOf (x : ↥V) = p := by rw [Subgroup.orderOf_coe, hx]
        obtain ⟨j, hj⟩ := hf2 x
        have hfx : f x = 1 := by
          have h1 : orderOf (f x) ∣ p := hxo ▸ orderOf_map_dvd f (x : ↥V)
          have h2 : orderOf (f x) ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hj
          have hcop : Nat.Coprime p (2 ^ j) :=
            Nat.Coprime.pow_right j ((Nat.coprime_primes hpp Nat.prime_two).mpr hp2)
          exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
        have hmem : (x : ↥V) ∈ f.ker ⊓ N := ⟨hfx, x.2⟩
        have h1 := orderOf_dvd_natCard (⟨x, hmem⟩ : ↥(f.ker ⊓ N))
        rw [Subgroup.orderOf_mk, hxo] at h1
        exact hpp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hf h1)
      have hV2 : ¬ p ^ 2 ∣ Nat.card V := by
        rw [← Subgroup.index_mul_card N]
        intro h
        exact hNi (Nat.Coprime.dvd_of_dvd_mul_right
          (Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hpp).mpr hNp)) h)
      exact hV2 (dvd_trans (pow_dvd_pow p (by norm_num : 2 ≤ 3)) (h3Q.trans hQV))
  · rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      at h3Q
    rcases hp with rfl | rfl <;> rcases hn with rfl | rfl | rfl <;> revert h3Q <;> decide

end CFSG.AGLEmbedding
